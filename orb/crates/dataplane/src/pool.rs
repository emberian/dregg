//! A fixed-capacity pool of reusable byte buffers.
//!
//! The hot path — receive request bytes, hand them to the proven core, write
//! the response bytes back — needs three transient buffers per request: the
//! connection's accumulation buffer, the request buffer handed across the serve
//! seam, and the response buffer handed back. Allocating and freeing these per
//! request is the steady-state allocation the high-performance IO path is meant
//! to remove.
//!
//! [`BufferPool`] holds a free list of `Vec<u8>` that are checked out as
//! [`PooledBuf`] and returned to the list when the `PooledBuf` is dropped —
//! from whichever thread drops it, so a buffer can travel from a connection
//! worker to the serve thread and back and still recycle to the same pool. In
//! steady state (free list warm) a checkout is a `Vec::pop` and a return is a
//! `clear` + `push`: no allocation, no `free`. The list grows only when demand
//! exceeds the warm set, and is capped so a burst cannot retain buffers without
//! bound.
//!
//! ## Allocation profile
//!
//! Once the free list has served its first `N` concurrent buffers, the Rust
//! host performs **zero heap allocation per request** for these buffers. The
//! remaining per-request allocations live *inside the Lean runtime*: the seam
//! `drorb_serve : ByteArray -> ByteArray` consumes an owned input `ByteArray`
//! and returns an owned output `ByteArray`, so the runtime allocates one of each
//! per call on its GC heap. That copy-once discipline is intrinsic to the proven
//! ABI (the core is a pure `ByteArray -> ByteArray` function); the host cannot
//! remove it without changing that ABI. The host-side buffers this pool governs
//! are the ones the host *can* keep allocation-free, and does.

use std::ops::{Deref, DerefMut};
use std::sync::{Arc, Mutex};

/// A pool of reusable byte buffers shared across the host's threads.
pub struct BufferPool {
    free: Mutex<Vec<Vec<u8>>>,
    /// Capacity a freshly minted buffer reserves, so early requests do not pay
    /// repeated `realloc` as they fill.
    buf_cap: usize,
    /// Ceiling on retained free buffers. A returned buffer beyond this is
    /// dropped rather than retained, bounding idle memory after a burst.
    max_retained: usize,
}

impl BufferPool {
    /// A pool that mints buffers with `buf_cap` reserved capacity and retains at
    /// most `max_retained` idle buffers on the free list.
    pub fn new(buf_cap: usize, max_retained: usize) -> Arc<Self> {
        Arc::new(BufferPool {
            free: Mutex::new(Vec::new()),
            buf_cap,
            max_retained,
        })
    }

    /// Check out a cleared buffer. Reuses a free-list entry when one is warm,
    /// else mints a fresh buffer with the pool's reserve capacity.
    pub fn take(self: &Arc<Self>) -> PooledBuf {
        let buf = {
            let mut free = self.free.lock().unwrap();
            free.pop()
        }
        .unwrap_or_else(|| Vec::with_capacity(self.buf_cap));
        PooledBuf {
            buf,
            pool: Arc::clone(self),
        }
    }

    /// Return a buffer to the free list, or drop it if the list is at its cap.
    fn give_back(&self, mut buf: Vec<u8>) {
        buf.clear();
        let mut free = self.free.lock().unwrap();
        if free.len() < self.max_retained {
            free.push(buf);
        }
        // else: drop `buf`, releasing its allocation — the burst is over.
    }
}

/// A byte buffer on loan from a [`BufferPool`]. Derefs to its `Vec<u8>`; returns
/// itself to the pool (cleared) on drop, regardless of which thread drops it.
pub struct PooledBuf {
    buf: Vec<u8>,
    pool: Arc<BufferPool>,
}

impl Deref for PooledBuf {
    type Target = Vec<u8>;
    fn deref(&self) -> &Vec<u8> {
        &self.buf
    }
}

impl DerefMut for PooledBuf {
    fn deref_mut(&mut self) -> &mut Vec<u8> {
        &mut self.buf
    }
}

impl Drop for PooledBuf {
    fn drop(&mut self) {
        // Move the inner buffer out (leaving an empty, allocation-free Vec) and
        // hand it back to the pool for reuse.
        let buf = std::mem::take(&mut self.buf);
        self.pool.give_back(buf);
    }
}
