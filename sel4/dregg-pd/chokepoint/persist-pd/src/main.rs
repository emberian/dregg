//! persist-pd — the chokepoint's durable-log seat (../../../chokepoint.system).
//!
//! The ONLY PD holding `durable_log`. It serves one protected procedure: read the leaf commit-pd
//! staged in `leaf_buf` (mapped read-only here), append it to the log, return the new log length
//! in MR0. commit-pd forwards only after this call returns that length. The log is RAM in this
//! image; a block-device cap would land here and only here.

#![no_std]
#![no_main]

use sel4_microkit::{
    debug_println, get_mr, memory_region_symbol, protection_domain, set_mr, Channel, Handler,
    Infallible, MessageInfo,
};

const LEAF_BUF_SIZE: usize = 0x1000;
const LOG_SIZE: usize = 0x10000;

fn leaf_buf() -> *const u8 {
    memory_region_symbol!(leaf_buf_vaddr: *mut [u8], n = LEAF_BUF_SIZE).as_ptr() as *const u8
}
fn durable_log() -> *mut u8 {
    memory_region_symbol!(durable_log_vaddr: *mut [u8], n = LOG_SIZE).as_ptr() as *mut u8
}

#[protection_domain(heap_size = 0x10000)]
fn init() -> HandlerImpl {
    debug_println!("[persist] chokepoint persist-PD: sole holder of durable_log; leaf_buf (R)");
    HandlerImpl {
        entries: 0,
        used: 0,
    }
}

struct HandlerImpl {
    entries: u64,
    used: usize,
}

impl Handler for HandlerImpl {
    type Error = Infallible;

    fn protected(
        &mut self,
        _channel: Channel,
        msg_info: MessageInfo,
    ) -> Result<MessageInfo, Self::Error> {
        let n = get_mr(0) as usize;
        let lb = leaf_buf();
        let mut len_bytes = [0u8; 8];
        for (i, b) in len_bytes.iter_mut().enumerate() {
            *b = unsafe { lb.add(i).read_volatile() };
        }
        let staged = u64::from_le_bytes(len_bytes) as usize;
        if msg_info.count() != 1
            || n != staged
            || n > LEAF_BUF_SIZE - 8
            || self.used + 8 + n > LOG_SIZE
        {
            debug_println!(
                "[persist]   REFUSE append (n={n}, staged={staged}, used={})",
                self.used
            );
            set_mr(0, self.entries);
            return Ok(MessageInfo::new(1, 1));
        }
        let log = durable_log();
        for (i, b) in (n as u64).to_le_bytes().iter().enumerate() {
            unsafe { log.add(self.used + i).write_volatile(*b) };
        }
        for i in 0..n {
            unsafe {
                log.add(self.used + 8 + i)
                    .write_volatile(lb.add(8 + i).read_volatile())
            };
        }
        self.used += 8 + n;
        self.entries += 1;
        let tail = unsafe { lb.add(8 + n - 4).read_volatile() };
        debug_println!(
            "[persist]   PERSIST entry {} ({n}-byte leaf, digest tail ..{:02x}) durable",
            self.entries,
            tail
        );
        set_mr(0, self.entries);
        Ok(MessageInfo::new(0, 1))
    }
}
