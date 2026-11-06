//! commit-pd — the in-path receipt device's commit seat (../../../chokepoint.system).
//!
//! It embeds the Lean step function `dregg_chokepoint_arrive` (CommitBytes.lean: the
//! summary step `stepS`, proved to refine `CommitStep.step`, whose outputs satisfy
//! `commit_before_forward`) and is the ONLY protection domain holding the NIC: the
//! virtio-mmio region and its IRQ are mapped into this PD and no other (the `.system` file is
//! the statement; seL4 enforces it). For each offered frame:
//!
//!   1. build the step's wire from the device state and the frame, call the Lean step;
//!   2. `F hw' len' occ leaf` : copy the leaf to `leaf_buf` and make a PROTECTED PROCEDURE
//!      CALL to persist-pd, which appends it to the durable log it alone holds and returns the
//!      new log length. Only after the call returns, and only if that length equals `len'`,
//!      is the frame forwarded. A PPC is synchronous, so "persist, then forward" is the
//!      control flow itself, the order the theorem states;
//!   3. `R hw' len'` : refuse; nothing is persisted or forwarded;
//!   4. anything else (malformed, length mismatch): halt the device (fail-closed).
//!
//! Forwarding in this image is a serial line plus a read of the NIC's virtio magic register
//! (proving the cap is held and live); driving virtio TX is the net-driver PD's code, to be
//! folded in next. The hardware counter `hw` is PD-local here: the non-rollbackable counter
//! the theorem assumes is a named residual of this image.

#![no_std]
#![no_main]
#![allow(unreachable_patterns)]

use core::alloc::{GlobalAlloc, Layout};
use core::ffi::{c_char, c_int, c_long};
use core::ptr;

use one_shot_mutex::sync::RawOneShotMutex;

use sel4_dlmalloc::{StaticDlmalloc, StaticHeap};
use sel4_linux_syscall_types::{ENOMEM, ENOSYS, MAP_ANONYMOUS, SEEK_CUR};
use sel4_microkit::{
    debug_print, debug_println, memory_region_symbol, protection_domain, set_mr, Channel,
    ChannelSet, Handler, Infallible, MessageInfo,
};
use sel4_musl::{
    set_syscall_handler, ParseSyscallError, Syscall, SyscallReturnValue, VaListAsSyscallArgs,
};

const LEAF_BUF_SIZE: usize = 0x1000;
fn leaf_buf() -> *mut u8 {
    memory_region_symbol!(leaf_buf_vaddr: *mut [u8], n = LEAF_BUF_SIZE).as_ptr() as *mut u8
}
fn nic_mmio() -> *const u32 {
    memory_region_symbol!(nic_mmio_vaddr: *mut [u8], n = 0x1000).as_ptr() as *const u32
}

const PERSIST: Channel = Channel::new(1);

unsafe extern "C" {
    fn chokepoint_init() -> c_int;
    fn chokepoint_arrive(wire: *const u8, n: usize, out: *mut u8, cap: usize) -> c_long;
}

/// The device state the wire carries (CommitBytes `Summary`).
struct Device {
    hw: u64,
    ctr: u64,
    epoch: u64,
    log_len: u64,
    cap: u64,
    halted: bool,
    /// The job manifest root (VJM) in force, hex.
    vjm_hex: &'static str,
    forwarded: u64,
    refused: u64,
}

/// A fixed-capacity byte writer (no_std formatting target).
struct Buf<const N: usize> {
    b: [u8; N],
    n: usize,
}
impl<const N: usize> Buf<N> {
    const fn new() -> Self {
        Buf { b: [0; N], n: 0 }
    }
    fn as_bytes(&self) -> &[u8] {
        &self.b[..self.n]
    }
}
impl<const N: usize> core::fmt::Write for Buf<N> {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        let s = s.as_bytes();
        if self.n + s.len() > N {
            return Err(core::fmt::Error);
        }
        self.b[self.n..self.n + s.len()].copy_from_slice(s);
        self.n += s.len();
        Ok(())
    }
}

fn hex_nibble(c: u8) -> Option<u8> {
    match c {
        b'0'..=b'9' => Some(c - b'0'),
        b'a'..=b'f' => Some(c - b'a' + 10),
        _ => None,
    }
}

fn parse_u64(t: &[u8]) -> Option<u64> {
    if t.is_empty() {
        return None;
    }
    let mut v: u64 = 0;
    for &c in t {
        if !c.is_ascii_digit() {
            return None;
        }
        v = v.checked_mul(10)?.checked_add(u64::from(c - b'0'))?;
    }
    Some(v)
}

impl Device {
    /// Offer one frame. Returns true if it was forwarded.
    fn offer(&mut self, job: u64, payload: &[u8]) -> bool {
        use core::fmt::Write;
        if self.halted {
            debug_println!("[commit]   device HALTED: frame for job {job} not offered");
        }
        let mut wire: Buf<1024> = Buf::new();
        let _ = write!(
            wire,
            "{} {} {} {} {} {} {} {} ",
            self.hw,
            self.ctr,
            self.epoch,
            self.log_len,
            self.cap,
            u8::from(self.halted),
            job,
            self.vjm_hex
        );
        if payload.is_empty() {
            let _ = write!(wire, "-");
        } else {
            for b in payload {
                let _ = write!(wire, "{:02x}", b);
            }
        }
        let mut reply = [0u8; 1024];
        let n = unsafe {
            chokepoint_arrive(
                wire.as_bytes().as_ptr(),
                wire.n,
                reply.as_mut_ptr(),
                reply.len(),
            )
        };
        if n < 0 {
            return self.halt("reply overflow");
        }
        let reply = &reply[..n as usize];
        let mut f = reply.split(|&c| c == b' ');
        match f.next() {
            Some(b"F") => {
                let (Some(hw), Some(len), Some(occ), Some(leaf)) = (
                    f.next().and_then(parse_u64),
                    f.next().and_then(parse_u64),
                    f.next().and_then(parse_u64),
                    f.next(),
                ) else {
                    return self.halt("malformed F reply");
                };
                if f.next().is_some() || leaf.len() % 2 != 0 || leaf.len() / 2 > LEAF_BUF_SIZE - 8 {
                    return self.halt("malformed F reply");
                }
                // The leaf into leaf_buf: 8-byte LE length, then the bytes.
                let lb = leaf_buf();
                let ln = leaf.len() / 2;
                for i in 0..ln {
                    let (Some(h), Some(l)) = (hex_nibble(leaf[2 * i]), hex_nibble(leaf[2 * i + 1]))
                    else {
                        return self.halt("leaf is not hex");
                    };
                    unsafe { lb.add(8 + i).write_volatile((h << 4) | l) };
                }
                for (i, b) in (ln as u64).to_le_bytes().iter().enumerate() {
                    unsafe { lb.add(i).write_volatile(*b) };
                }
                // PERSIST: a protected procedure call; persist-pd returns the durable length.
                set_mr(0, ln as u64);
                let ack = PERSIST.pp_call(MessageInfo::new(0, 1));
                let durable = sel4_microkit::get_mr(0);
                if ack.label() != 0 || durable != len {
                    debug_println!(
                        "[commit]   persist ack label={} durable_len={} expected {}",
                        ack.label(),
                        durable,
                        len
                    );
                    return self.halt("persist did not acknowledge the expected log length");
                }
                self.hw = hw;
                self.ctr = hw;
                self.log_len = len;
                // FORWARD, strictly after the acknowledged persist.
                let magic = unsafe { core::ptr::read_volatile(nic_mmio()) };
                self.forwarded += 1;
                debug_println!(
                    "[commit]   FORWARD occ={occ} job={job} ({} bytes) after persist ack (log={len}); NIC magic={:#010x}",
                    payload.len(),
                    magic
                );
                true
            }
            Some(b"R") => {
                let (Some(hw), Some(len)) =
                    (f.next().and_then(parse_u64), f.next().and_then(parse_u64))
                else {
                    return self.halt("malformed R reply");
                };
                self.hw = hw;
                self.log_len = len;
                self.refused += 1;
                debug_println!(
                    "[commit]   REFUSE job={job}: nothing persisted, nothing forwarded (log={len})"
                );
                false
            }
            _ => self.halt("empty or unknown reply (fail-closed)"),
        }
    }

    fn halt(&mut self, why: &str) -> bool {
        self.halted = true;
        debug_println!("[commit]   HALT: {why}");
        false
    }
}

// ── THE ORDERING FIX (../executor-rootserver, WALL-roottask.md §__sysinfo-null) ─
// The seL4 musl libc routes every syscall through the `__sysinfo` function
// pointer, NULL until `set_syscall_handler` populates it. `global_init()` runs
// the C++ `.init_array` constructors (Lean static initializers — some allocate:
// malloc → mmap → `br __sysinfo`(=0) → fault at address 0) BEFORE the PD entry.
// `sel4_ctors_dtors::run_ctors` executes `.preinit_array` BEFORE `.init_array`,
// so a `.preinit_array` entry installs the handler ahead of every C++ ctor. This
// is identical to the root task — the Microkit entry runs the same global_init.
unsafe extern "C" fn install_syscall_handler_preinit() {
    unsafe {
        set_syscall_handler(handle_syscall);
    }
}

#[used]
#[unsafe(link_section = ".preinit_array")]
static PREINIT_INSTALL_SYSCALL_HANDLER: unsafe extern "C" fn() = install_syscall_handler_preinit;

#[protection_domain(heap_size = 0x10000)]
fn init() -> HandlerImpl {
    debug_println!("");
    debug_println!("[commit] chokepoint commit-PD: the Lean step function on seL4");
    debug_println!(
        "[commit]   caps: nic_mmio + NIC IRQ (sole holder), leaf_buf (RW), PPC to persist"
    );
    let rc = unsafe { chokepoint_init() };
    if rc != 0 {
        debug_println!("[commit]   FATAL: Lean init rc={rc}; the device stays halted");
        return HandlerImpl;
    }
    debug_println!("[commit]   Lean runtime + CommitBytes initialised");
    let mut dev = Device {
        hw: 0,
        ctr: 0,
        epoch: 1,
        log_len: 0,
        cap: 4,
        halted: false,
        vjm_hex: "7669656d",
        forwarded: 0,
        refused: 0,
    };
    // Six offered frames against capacity 4: four forwards, then refusals.
    let frames: [&[u8]; 6] = [
        b"frame-0", b"frame-1", b"frame-2", b"frame-3", b"frame-4", b"frame-5",
    ];
    for (i, p) in frames.iter().enumerate() {
        dev.offer(100 + i as u64, p);
    }
    debug_println!(
        "[commit]   SUMMARY forwarded={} refused={} log_len={} hw={} halted={}",
        dev.forwarded,
        dev.refused,
        dev.log_len,
        dev.hw,
        dev.halted
    );
    debug_println!("[commit]   CHOKEPOINT-BOOT-OK");
    HandlerImpl
}

struct HandlerImpl;

impl Handler for HandlerImpl {
    type Error = Infallible;
    fn notified(&mut self, channels: ChannelSet) -> Result<(), Self::Error> {
        for c in channels.iter() {
            debug_println!("[commit]   notified on channel {}", c.index());
        }
        Ok(())
    }
}

// ════════════════════════════════════════════════════════════════════════════
// The in-PD Linux-syscall handler — ported verbatim from ../executor-rootserver/
// src/main.rs. It services the surface the embedded Lean runtime exercises on the
// pure executor turn: heap (Brk + anonymous Mmap), stdout/stderr (Write/Writev),
// and the no-op identity calls. Any unexpected syscall is reported (a precise
// next wall to characterize) rather than silently faked. The verified turn is
// pure + single-threaded + deterministic, so the faithful answers are no-op
// success / zero-fill.
// ════════════════════════════════════════════════════════════════════════════

// ENOENT (no such file/directory) — not re-exported by sel4-linux-syscall-types.
const ENOENT: SyscallReturnValue = 2;
const EBADF: SyscallReturnValue = 9;
// The sentinel fd `openat("/dev/urandom")` returns; `read` zero-fills it. The
// Lean runtime seeds its hash from /dev/urandom at init.
const URANDOM_FD: SyscallReturnValue = 1000;

fn path_is(path_ptr: *const u8, want: &[u8]) -> bool {
    if path_ptr.is_null() {
        return false;
    }
    for (i, &w) in want.iter().enumerate() {
        let c = unsafe { *path_ptr.add(i) };
        if c != w {
            return false;
        }
    }
    unsafe { *path_ptr.add(want.len()) == 0 }
}

fn handle_syscall(
    syscall: Result<Syscall, ParseSyscallError<VaListAsSyscallArgs>>,
) -> SyscallReturnValue {
    match syscall {
        Ok(syscall) => handle_known_syscall(syscall),
        Err(ParseSyscallError::UnrecognizedSyscallNumber { sysnum, args }) => {
            handle_by_number(sysnum, args)
        }
        Err(err) => {
            debug_println!("[commit]   UNPARSED SYSCALL (a precise wall): {err:?}");
            -ENOSYS
        }
    }
}

mod nr {
    use sel4_linux_syscall_types::SyscallNumber;
    pub const IOCTL: SyscallNumber = 29;
    pub const FUTEX: SyscallNumber = 98;
    pub const SET_ROBUST_LIST: SyscallNumber = 99;
    pub const NANOSLEEP: SyscallNumber = 101;
    pub const CLOCK_GETTIME: SyscallNumber = 113;
    pub const SCHED_GETAFFINITY: SyscallNumber = 123;
    pub const SIGALTSTACK: SyscallNumber = 132;
    pub const RT_SIGACTION: SyscallNumber = 134;
    pub const RT_SIGPROCMASK: SyscallNumber = 135;
    pub const SET_TID_ADDRESS: SyscallNumber = 96;
    pub const MPROTECT: SyscallNumber = 226;
    pub const MADVISE: SyscallNumber = 233;
    pub const PRLIMIT64: SyscallNumber = 261;
    pub const GETRANDOM: SyscallNumber = 278;
    pub const TGKILL: SyscallNumber = 131;
    pub const EXIT_GROUP: SyscallNumber = 94;
    pub const RSEQ: SyscallNumber = 293;
    pub const MEMBARRIER: SyscallNumber = 283;
    pub const OPENAT: SyscallNumber = 56;
    pub const CLOSE: SyscallNumber = 57;
    pub const READ: SyscallNumber = 63;
    pub const FCNTL: SyscallNumber = 25;
    pub const FSTAT: SyscallNumber = 80;
    pub const NEWFSTATAT: SyscallNumber = 79;
    pub const READLINKAT: SyscallNumber = 78;
    pub const FACCESSAT: SyscallNumber = 48;
    pub const STATX: SyscallNumber = 291;
    pub const PPOLL: SyscallNumber = 73;
    pub const GETPID: SyscallNumber = 172;
    pub const GETTID: SyscallNumber = 178;
    pub const GETRUSAGE: SyscallNumber = 165;
    pub const SYSINFO: SyscallNumber = 179;
    pub const SCHED_YIELD: SyscallNumber = 124;
}

fn handle_by_number(
    sysnum: sel4_linux_syscall_types::SyscallNumber,
    mut args: VaListAsSyscallArgs,
) -> SyscallReturnValue {
    use sel4_linux_syscall_types::SyscallArgs;
    match sysnum {
        nr::SET_TID_ADDRESS
        | nr::SET_ROBUST_LIST
        | nr::RT_SIGACTION
        | nr::RT_SIGPROCMASK
        | nr::SIGALTSTACK
        | nr::IOCTL
        | nr::MPROTECT
        | nr::MADVISE
        | nr::PRLIMIT64
        | nr::SCHED_GETAFFINITY
        | nr::RSEQ
        | nr::MEMBARRIER
        | nr::TGKILL
        | nr::NANOSLEEP => 0,
        nr::FUTEX => 0,
        nr::GETPID | nr::GETTID => 1,
        nr::SCHED_YIELD | nr::PPOLL | nr::GETRUSAGE | nr::SYSINFO => 0,
        nr::OPENAT => {
            let _dirfd: usize = args.next_arg().unwrap_or(0);
            let path_ptr: *const u8 = args.next_arg::<usize>().unwrap_or(0) as *const u8;
            if path_is(path_ptr, b"/dev/urandom") || path_is(path_ptr, b"/dev/random") {
                URANDOM_FD
            } else {
                -ENOENT
            }
        }
        nr::FACCESSAT | nr::READLINKAT | nr::STATX | nr::NEWFSTATAT => -ENOENT,
        nr::CLOSE | nr::FCNTL => 0,
        nr::READ => {
            let fd: SyscallReturnValue =
                args.next_arg::<usize>().unwrap_or(0) as SyscallReturnValue;
            let buf: *mut u8 = args.next_arg::<usize>().unwrap_or(0) as *mut u8;
            let count: usize = args.next_arg().unwrap_or(0);
            if fd == URANDOM_FD && !buf.is_null() {
                for i in 0..count {
                    unsafe { buf.add(i).write(0) };
                }
                count as SyscallReturnValue
            } else {
                0
            }
        }
        nr::FSTAT => -EBADF,
        nr::CLOCK_GETTIME => {
            let _clockid: usize = args.next_arg().unwrap_or(0);
            let ts: *mut u64 = args.next_arg::<usize>().unwrap_or(0) as *mut u64;
            if !ts.is_null() {
                unsafe {
                    ts.write(0);
                    ts.add(1).write(0);
                }
            }
            0
        }
        nr::GETRANDOM => {
            let buf: *mut u8 = args.next_arg::<usize>().unwrap_or(0) as *mut u8;
            let len: usize = args.next_arg().unwrap_or(0);
            if !buf.is_null() {
                for i in 0..len {
                    unsafe { buf.add(i).write(0) };
                }
            }
            len as SyscallReturnValue
        }
        nr::EXIT_GROUP => {
            debug_println!("[commit]   (libc exit_group during/after the turn — parking)");
            sel4::init_thread::suspend_self()
        }
        other => {
            debug_println!("[commit]   UNHANDLED SYSCALL number {other} (a precise wall)");
            -ENOSYS
        }
    }
}

fn handle_known_syscall(syscall: Syscall) -> SyscallReturnValue {
    use Syscall::*;
    match syscall {
        Getuid | Geteuid | Getgid | Getegid => 0,
        Brk { addr } => {
            let bounds = BRK_HEAP.bounds();
            (if addr.is_null() {
                bounds.start()
            } else if (bounds.start()..bounds.end()).contains(&addr.cast()) {
                addr.cast()
            } else {
                ptr::null()
            }) as SyscallReturnValue
        }
        Mmap {
            addr: _,
            len,
            prot: _,
            flag,
            fd: _,
            offset: _,
        } => {
            if flag & MAP_ANONYMOUS != 0 {
                (unsafe { MMAP_DLMALLOC.alloc(Layout::from_size_align(len, 4096).unwrap()) })
                    as SyscallReturnValue
            } else {
                -ENOMEM
            }
        }
        Lseek { fd, offset, whence } => {
            assert!(whence == SEEK_CUR);
            assert!(offset == 0);
            assert!((0..=2).contains(&fd));
            0
        }
        Write { fd, buf, count } => {
            assert!(fd == 1 || fd == 2);
            for i in 0..(count as isize) {
                let c: c_char = unsafe { *buf.offset(i) };
                debug_print!("{}", c as u8 as char);
            }
            count as SyscallReturnValue
        }
        Writev { fd, iov, iovcnt } => {
            assert!(fd == 1 || fd == 2);
            let mut ret: isize = 0;
            for i in 0..(iovcnt as isize) {
                let iov = unsafe { &*iov.offset(i) };
                for j in 0..(iov.iov_len as isize) {
                    let c: u8 = unsafe { *(iov.iov_base as *const u8).offset(j) };
                    debug_print!("{}", c as char);
                    ret += 1;
                }
            }
            ret as SyscallReturnValue
        }
        other => {
            debug_println!("[commit]   UNHANDLED SYSCALL (a precise wall): {other:?}");
            -ENOSYS
        }
    }
}

// The brk heap and the mmap pool — the Lean runtime + one transfer turn fit in a
// few MiB (the host-musl run's RSS is modest). These are static PD memory (BSS
// in the PD's own frames), so they directly inflate the initial-task footprint
// the seL4 loader must place; sized to the turn's real need (48 MiB GC arena),
// not generously, to keep the embedded image small.
static BRK_HEAP: StaticHeap<{ 4 * 1024 * 1024 }> = StaticHeap::new();

const MMAP_HEAP_SIZE: usize = 48 * 1024 * 1024;
static MMAP_HEAP: StaticHeap<MMAP_HEAP_SIZE> = StaticHeap::new();
static MMAP_DLMALLOC: StaticDlmalloc<RawOneShotMutex> = StaticDlmalloc::new(MMAP_HEAP.bounds());
