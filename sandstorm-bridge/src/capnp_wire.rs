//! A minimal, **safe**, allocation-bounded Cap'n Proto wire codec — reader + writer —
//! for exactly the message shapes a Sandstorm `.spk` carries: `Signature`, `Archive`
//! (with its nested `File` tree), and `Manifest`.
//!
//! This is the real capnp wire (<https://capnproto.org/encoding.html>), not a
//! projection: it reads the genuine multi-segment, far-pointer-bearing messages a real
//! catalog `.spk` is made of (the `sample.spk` archive is a 60-segment message), and it
//! writes single-segment messages a stock `capnp` tool reads back. No `unsafe`, no C
//! toolchain, no codegen — pure byte slicing, so the crate keeps its `unsafe_code =
//! "forbid"` discipline and stays pure-Rust/vendorable/offline.
//!
//! Only the slice of capnp the `.spk` format uses is implemented: struct pointers,
//! list pointers (byte/`Data`, `Text`, pointer-list, and composite-struct lists),
//! far pointers (single- and double-word landing pads), and the single-segment writer.
//! Every traversal is bounded — a list count is validated against the words actually
//! present before anything is allocated, and pointer-following is depth-limited — so a
//! malformed or hostile message is refused with bounded memory rather than looping or
//! over-allocating (defense in depth: the archive is decoded only *after* its Ed25519
//! signature verifies, but the reader does not rely on that).

/// Why decoding a capnp message failed.
#[derive(Debug, PartialEq, Eq)]
pub enum CapnpError {
    /// The stream framing (segment table) was truncated or self-inconsistent.
    Framing(&'static str),
    /// A pointer pointed outside the message (or into a too-small region).
    OutOfBounds(&'static str),
    /// A list declared more elements than the remaining message could hold — refused
    /// before allocation (an over-count / decompression-style bomb).
    ListTooLarge,
    /// Pointer-following exceeded the depth budget (a cycle or pathological nesting).
    TooDeep,
    /// A field had a type the `.spk` schema does not use here.
    WrongKind(&'static str),
}

impl std::fmt::Display for CapnpError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CapnpError::Framing(s) => write!(f, "capnp framing: {s}"),
            CapnpError::OutOfBounds(s) => write!(f, "capnp pointer out of bounds: {s}"),
            CapnpError::ListTooLarge => write!(f, "capnp list count exceeds message bytes"),
            CapnpError::TooDeep => write!(f, "capnp pointer nesting too deep"),
            CapnpError::WrongKind(s) => write!(f, "capnp field has unexpected kind: {s}"),
        }
    }
}
impl std::error::Error for CapnpError {}

/// The cap on how deep `get_*` will follow pointers — guards against cycles and
/// pathological nesting in a hostile message.
const MAX_DEPTH: u32 = 256;

/// A parsed, framed capnp message: its segments, borrowed from the input buffer.
pub struct Message<'a> {
    segments: Vec<&'a [u8]>,
}

impl<'a> Message<'a> {
    /// Parse exactly one framed capnp message from the front of `bytes`, returning the
    /// message and the number of bytes it consumed (so a caller can split a stream of
    /// concatenated messages — a `.spk` is `Signature ++ Archive`).
    pub fn parse_prefix(bytes: &'a [u8]) -> Result<(Message<'a>, usize), CapnpError> {
        let seg_count_minus_one =
            read_u32(bytes, 0).ok_or(CapnpError::Framing("missing segment count"))?;
        let seg_count = (seg_count_minus_one as usize)
            .checked_add(1)
            .ok_or(CapnpError::Framing("segment count overflow"))?;
        // The segment table: (count) u32 sizes after the count word.
        let table_bytes = 4usize
            .checked_add(
                seg_count
                    .checked_mul(4)
                    .ok_or(CapnpError::Framing("table overflow"))?,
            )
            .ok_or(CapnpError::Framing("table overflow"))?;
        // Bound the table against the input before reading each size.
        if table_bytes > bytes.len() {
            return Err(CapnpError::Framing("segment table truncated"));
        }
        let mut sizes = Vec::with_capacity(seg_count);
        let mut total_words: usize = 0;
        for i in 0..seg_count {
            let sz = read_u32(bytes, 4 + i * 4)
                .ok_or(CapnpError::Framing("segment size truncated"))?
                as usize;
            total_words = total_words
                .checked_add(sz)
                .ok_or(CapnpError::Framing("segment words overflow"))?;
            sizes.push(sz);
        }
        // The table is padded to a word (8-byte) boundary.
        let header = (table_bytes + 7) & !7;
        let data_bytes = total_words
            .checked_mul(8)
            .ok_or(CapnpError::Framing("segment bytes overflow"))?;
        let consumed = header
            .checked_add(data_bytes)
            .ok_or(CapnpError::Framing("message size overflow"))?;
        if consumed > bytes.len() {
            return Err(CapnpError::Framing("message body truncated"));
        }
        let mut segments = Vec::with_capacity(seg_count);
        let mut off = header;
        for sz in sizes {
            let n = sz * 8;
            segments.push(&bytes[off..off + n]);
            off += n;
        }
        Ok((Message { segments }, consumed))
    }

    /// The root struct of the message (the pointer at word 0 of segment 0).
    pub fn root(&self) -> Result<Struct<'a, '_>, CapnpError> {
        let seg0 = self
            .segments
            .first()
            .ok_or(CapnpError::Framing("no segments"))?;
        let ptr = read_u64(seg0, 0).ok_or(CapnpError::Framing("missing root pointer"))?;
        match self.follow(0, 0, ptr, 0)? {
            Resolved::Struct(s) => Ok(s),
            _ => Err(CapnpError::WrongKind("root is not a struct")),
        }
    }

    fn seg(&self, idx: usize) -> Result<&'a [u8], CapnpError> {
        self.segments
            .get(idx)
            .copied()
            .ok_or(CapnpError::OutOfBounds("segment index"))
    }

    /// Resolve a pointer word located at `seg`/`word_idx` (used for in-segment pointers
    /// and for far-pointer landing pads), returning the thing it designates.
    fn follow(
        &self,
        seg: usize,
        ptr_word_idx: usize,
        ptr: u64,
        depth: u32,
    ) -> Result<Resolved<'a, '_>, CapnpError> {
        if depth > MAX_DEPTH {
            return Err(CapnpError::TooDeep);
        }
        if ptr == 0 {
            return Ok(Resolved::Null);
        }
        match ptr & 3 {
            2 => {
                // Far pointer. offset (29 bits) = landing-pad word in target segment;
                // bit 2 = double-far flag; high 32 bits = target segment id.
                let landing_word = ((ptr >> 3) & 0x1fff_ffff) as usize;
                let double = (ptr >> 2) & 1 == 1;
                let target_seg = (ptr >> 32) as usize;
                let lseg = self.seg(target_seg)?;
                if !double {
                    let landing = read_u64(lseg, landing_word * 8)
                        .ok_or(CapnpError::OutOfBounds("far landing pad"))?;
                    self.follow(target_seg, landing_word, landing, depth + 1)
                } else {
                    // Two-word pad: [far pointer to content][tag describing content].
                    let far = read_u64(lseg, landing_word * 8)
                        .ok_or(CapnpError::OutOfBounds("double-far pad"))?;
                    let tag = read_u64(lseg, (landing_word + 1) * 8)
                        .ok_or(CapnpError::OutOfBounds("double-far tag"))?;
                    if far & 3 != 2 {
                        return Err(CapnpError::Framing("double-far first word not a far ptr"));
                    }
                    let content_word = ((far >> 3) & 0x1fff_ffff) as usize;
                    let content_seg = (far >> 32) as usize;
                    self.resolve_with_tag(content_seg, content_word, tag)
                }
            }
            _ => {
                // Struct or list pointer: offset is relative to the word AFTER the
                // pointer word.
                let off = sign_extend_30((ptr >> 2) & 0x3fff_ffff);
                let target = (ptr_word_idx as i64) + 1 + off;
                if target < 0 {
                    return Err(CapnpError::OutOfBounds("negative target"));
                }
                self.resolve_with_tag(seg, target as usize, ptr)
            }
        }
    }

    /// Interpret `tag` as a struct/list descriptor whose content starts at
    /// `seg`/`content_word`.
    fn resolve_with_tag(
        &self,
        seg: usize,
        content_word: usize,
        tag: u64,
    ) -> Result<Resolved<'a, '_>, CapnpError> {
        match tag & 3 {
            0 => {
                let data_words = ((tag >> 32) & 0xffff) as usize;
                let ptr_words = ((tag >> 48) & 0xffff) as usize;
                self.bound_struct(seg, content_word, data_words, ptr_words)?;
                Ok(Resolved::Struct(Struct {
                    msg: self,
                    seg,
                    data_word: content_word,
                    data_words,
                    ptr_words,
                }))
            }
            1 => {
                let elem_type = ((tag >> 32) & 7) as u8;
                let count = ((tag >> 35) & 0x1fff_ffff) as usize;
                Ok(Resolved::List(List {
                    msg: self,
                    seg,
                    start_word: content_word,
                    elem_type,
                    count,
                }))
            }
            _ => Err(CapnpError::Framing("tag is itself a far/other pointer")),
        }
    }

    fn bound_struct(
        &self,
        seg: usize,
        data_word: usize,
        data_words: usize,
        ptr_words: usize,
    ) -> Result<(), CapnpError> {
        let s = self.seg(seg)?;
        let total = data_word
            .checked_add(data_words)
            .and_then(|w| w.checked_add(ptr_words))
            .ok_or(CapnpError::OutOfBounds("struct extent overflow"))?;
        if total * 8 > s.len() {
            return Err(CapnpError::OutOfBounds("struct extends past segment"));
        }
        Ok(())
    }
}

enum Resolved<'a, 'm> {
    Null,
    Struct(Struct<'a, 'm>),
    List(List<'a, 'm>),
}

/// A reader over one struct in a message.
pub struct Struct<'a, 'm> {
    msg: &'m Message<'a>,
    seg: usize,
    data_word: usize,
    data_words: usize,
    ptr_words: usize,
}

impl<'a, 'm> Struct<'a, 'm> {
    fn seg_bytes(&self) -> &'a [u8] {
        // Safe: bounded at construction by `bound_struct`.
        self.msg.segments[self.seg]
    }

    /// Read a little-endian `u16` at `byte_off` within the data section (0 if past it).
    pub fn get_u16(&self, byte_off: usize) -> u16 {
        let abs = self.data_word * 8 + byte_off;
        if byte_off + 2 > self.data_words * 8 {
            return 0;
        }
        read_u16(self.seg_bytes(), abs).unwrap_or(0)
    }

    /// Read a little-endian `u32` at `byte_off` within the data section (0 if past it).
    pub fn get_u32(&self, byte_off: usize) -> u32 {
        if byte_off + 4 > self.data_words * 8 {
            return 0;
        }
        read_u32(self.seg_bytes(), self.data_word * 8 + byte_off).unwrap_or(0)
    }

    /// Read a little-endian `i64` at `byte_off` within the data section (0 if past it).
    pub fn get_i64(&self, byte_off: usize) -> i64 {
        if byte_off + 8 > self.data_words * 8 {
            return 0;
        }
        read_u64(self.seg_bytes(), self.data_word * 8 + byte_off).unwrap_or(0) as i64
    }

    fn raw_ptr(&self, i: usize) -> Result<Option<(usize, u64)>, CapnpError> {
        if i >= self.ptr_words {
            return Ok(None);
        }
        let ptr_word = self.data_word + self.data_words + i;
        let p = read_u64(self.seg_bytes(), ptr_word * 8)
            .ok_or(CapnpError::OutOfBounds("pointer slot"))?;
        Ok(Some((ptr_word, p)))
    }

    /// The struct at pointer slot `i`, if present and a struct.
    pub fn get_struct(&self, i: usize) -> Result<Option<Struct<'a, 'm>>, CapnpError> {
        match self.raw_ptr(i)? {
            None => Ok(None),
            Some((pw, p)) => match self.msg.follow(self.seg, pw, p, 0)? {
                Resolved::Null => Ok(None),
                Resolved::Struct(s) => Ok(Some(s)),
                Resolved::List(_) => Err(CapnpError::WrongKind("expected struct, got list")),
            },
        }
    }

    /// The list at pointer slot `i`, if present and a list.
    pub fn get_list(&self, i: usize) -> Result<Option<List<'a, 'm>>, CapnpError> {
        match self.raw_ptr(i)? {
            None => Ok(None),
            Some((pw, p)) => match self.msg.follow(self.seg, pw, p, 0)? {
                Resolved::Null => Ok(None),
                Resolved::List(l) => Ok(Some(l)),
                Resolved::Struct(_) => Err(CapnpError::WrongKind("expected list, got struct")),
            },
        }
    }

    /// The raw bytes of a `Data` field at pointer slot `i` (empty if absent).
    pub fn get_data(&self, i: usize) -> Result<Vec<u8>, CapnpError> {
        match self.get_list(i)? {
            None => Ok(Vec::new()),
            Some(l) => l.bytes(),
        }
    }

    /// A `Text` field at pointer slot `i` as a `String` (the trailing NUL is dropped;
    /// empty if absent).
    pub fn get_text(&self, i: usize) -> Result<String, CapnpError> {
        let mut b = self.get_data(i)?;
        if b.last() == Some(&0) {
            b.pop();
        }
        Ok(String::from_utf8_lossy(&b).into_owned())
    }
}

/// A reader over one list in a message.
pub struct List<'a, 'm> {
    msg: &'m Message<'a>,
    seg: usize,
    start_word: usize,
    elem_type: u8,
    count: usize,
}

impl<'a, 'm> List<'a, 'm> {
    /// Number of elements (for a composite list, the struct-element count).
    pub fn len(&self) -> usize {
        if self.elem_type == 7 {
            // composite: `count` is the word count; the tag word holds element count.
            self.composite_count().unwrap_or(0)
        } else {
            self.count
        }
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    fn seg_bytes(&self) -> Result<&'a [u8], CapnpError> {
        self.msg.seg(self.seg)
    }

    /// The bytes of a byte-list (`Data` / `Text` body): element type 2 (1-byte) — the
    /// only list-of-bytes shape the `.spk` schema uses.
    pub fn bytes(&self) -> Result<Vec<u8>, CapnpError> {
        if self.count == 0 {
            return Ok(Vec::new());
        }
        if self.elem_type != 2 {
            return Err(CapnpError::WrongKind("expected a byte list"));
        }
        let s = self.seg_bytes()?;
        let start = self
            .start_word
            .checked_mul(8)
            .ok_or(CapnpError::OutOfBounds("list start overflow"))?;
        let end = start
            .checked_add(self.count)
            .ok_or(CapnpError::OutOfBounds("list end overflow"))?;
        if end > s.len() {
            return Err(CapnpError::ListTooLarge);
        }
        Ok(s[start..end].to_vec())
    }

    fn composite_count(&self) -> Result<usize, CapnpError> {
        let s = self.seg_bytes()?;
        let tag =
            read_u64(s, self.start_word * 8).ok_or(CapnpError::OutOfBounds("composite tag"))?;
        Ok(((tag >> 2) & 0x3fff_ffff) as usize)
    }

    /// Iterate a composite list (list of structs), yielding a [`Struct`] per element.
    /// The element count is validated against the words actually present, so a bogus
    /// over-count is refused before anything is allocated.
    pub fn structs(&self) -> Result<Vec<Struct<'a, 'm>>, CapnpError> {
        if self.elem_type != 7 {
            return Err(CapnpError::WrongKind("expected a composite list"));
        }
        let s = self.seg_bytes()?;
        let tag =
            read_u64(s, self.start_word * 8).ok_or(CapnpError::OutOfBounds("composite tag"))?;
        if tag & 3 != 0 {
            return Err(CapnpError::Framing("composite tag is not a struct tag"));
        }
        let elem_count = ((tag >> 2) & 0x3fff_ffff) as usize;
        let data_words = ((tag >> 32) & 0xffff) as usize;
        let ptr_words = ((tag >> 48) & 0xffff) as usize;
        let stride = data_words
            .checked_add(ptr_words)
            .ok_or(CapnpError::OutOfBounds("stride overflow"))?;
        // `count` (the list-pointer word count) must equal elem_count*stride; and the
        // whole region (tag + bodies) must fit the segment — refuse an over-count bomb.
        let body_words = elem_count
            .checked_mul(stride)
            .ok_or(CapnpError::ListTooLarge)?;
        if body_words != self.count {
            return Err(CapnpError::Framing("composite word count mismatch"));
        }
        let total_words = self
            .start_word
            .checked_add(1)
            .and_then(|w| w.checked_add(body_words))
            .ok_or(CapnpError::ListTooLarge)?;
        if total_words * 8 > s.len() {
            return Err(CapnpError::ListTooLarge);
        }
        let mut out = Vec::with_capacity(elem_count);
        for i in 0..elem_count {
            let data_word = self.start_word + 1 + i * stride;
            out.push(Struct {
                msg: self.msg,
                seg: self.seg,
                data_word,
                data_words,
                ptr_words,
            });
        }
        Ok(out)
    }

    /// Iterate a pointer-list (`List(Text)`, `List(...)`): element type 6, yielding the
    /// pointer at each slot for the caller to interpret.
    pub fn text_list(&self) -> Result<Vec<String>, CapnpError> {
        if self.count == 0 {
            return Ok(Vec::new());
        }
        if self.elem_type != 6 {
            return Err(CapnpError::WrongKind("expected a pointer list"));
        }
        let s = self.seg_bytes()?;
        let total = self
            .start_word
            .checked_add(self.count)
            .ok_or(CapnpError::ListTooLarge)?;
        if total * 8 > s.len() {
            return Err(CapnpError::ListTooLarge);
        }
        let mut out = Vec::with_capacity(self.count);
        for i in 0..self.count {
            let pw = self.start_word + i;
            let p = read_u64(s, pw * 8).ok_or(CapnpError::OutOfBounds("text list slot"))?;
            match self.msg.follow(self.seg, pw, p, 0)? {
                Resolved::Null => out.push(String::new()),
                Resolved::List(l) => {
                    let mut b = l.bytes()?;
                    if b.last() == Some(&0) {
                        b.pop();
                    }
                    out.push(String::from_utf8_lossy(&b).into_owned());
                }
                Resolved::Struct(_) => {
                    return Err(CapnpError::WrongKind("text list slot is a struct"))
                }
            }
        }
        Ok(out)
    }
}

// ---------------------------------------------------------------------------
// Single-segment writer.
// ---------------------------------------------------------------------------

/// A single-segment capnp message under construction (a word-aligned byte arena).
pub struct Builder {
    buf: Vec<u8>,
}

impl Builder {
    pub fn new() -> Self {
        Builder { buf: Vec::new() }
    }

    /// Allocate `n` zeroed words, returning the index of the first.
    fn alloc(&mut self, n: usize) -> usize {
        let wi = self.buf.len() / 8;
        self.buf.resize(self.buf.len() + n * 8, 0);
        wi
    }

    fn put_word(&mut self, word_idx: usize, v: u64) {
        self.buf[word_idx * 8..word_idx * 8 + 8].copy_from_slice(&v.to_le_bytes());
    }

    fn put_bytes(&mut self, byte_off: usize, data: &[u8]) {
        self.buf[byte_off..byte_off + data.len()].copy_from_slice(data);
    }

    /// Write a struct pointer (into a pre-allocated slot) designating `target_word`.
    fn struct_ptr_at(&mut self, slot: usize, target_word: usize, dwords: u16, pwords: u16) {
        let off = target_word as i64 - (slot as i64 + 1);
        let off30 = (off as u64) & 0x3fff_ffff;
        let p = (off30 << 2) | ((dwords as u64) << 32) | ((pwords as u64) << 48);
        self.put_word(slot, p);
    }

    /// Write a `Data` (or `Text`) byte-list pointer into `slot`, appending the bytes.
    /// `text` adds a trailing NUL (capnp `Text` is NUL-terminated).
    fn bytes_ptr_at(&mut self, slot: usize, data: &[u8], text: bool) {
        let count = data.len() + if text { 1 } else { 0 };
        if count == 0 {
            // Empty list: a list pointer with zero count (offset is irrelevant).
            self.put_word(slot, 1);
            return;
        }
        let words = count.div_ceil(8);
        let content = self.alloc(words);
        self.put_bytes(content * 8, data);
        let off = content as i64 - (slot as i64 + 1);
        let off30 = (off as u64) & 0x3fff_ffff;
        // element type 2 = 1 byte; bit0 set = list pointer.
        let p = 1 | (off30 << 2) | (2u64 << 32) | ((count as u64) << 35);
        self.put_word(slot, p);
    }

    /// Write a composite (list-of-struct) pointer for `files` into `slot`.
    fn file_list_ptr_at(&mut self, slot: usize, files: &[WireFile]) {
        if files.is_empty() {
            self.put_word(slot, 0); // null = empty list
            return;
        }
        const DW: usize = 2; // discriminant+padding word, mtime word
        const PW: usize = 2; // name, union value
        const STRIDE: usize = DW + PW;
        let total = 1 + files.len() * STRIDE; // tag + element slots
        let tag_word = self.alloc(total);
        // tag word: struct "pointer" whose offset field holds the element count.
        let count30 = (files.len() as u64) & 0x3fff_ffff;
        let tag = (count30 << 2) | ((DW as u64) << 32) | ((PW as u64) << 48);
        self.put_word(tag_word, tag);
        // the list pointer's count is the word count of the bodies (excluding the tag).
        let off = tag_word as i64 - (slot as i64 + 1);
        let off30 = (off as u64) & 0x3fff_ffff;
        let body_words = (files.len() * STRIDE) as u64;
        let p = 1 | (off30 << 2) | (7u64 << 32) | (body_words << 35);
        self.put_word(slot, p);
        for (i, f) in files.iter().enumerate() {
            let base = tag_word + 1 + i * STRIDE;
            // data word 0: discriminant in the low 16 bits.
            self.put_word(base, f.discriminant() as u64);
            // data word 1: lastModificationTimeNs.
            self.put_word(base + 1, f.mtime_ns as u64);
            let name_slot = base + DW;
            let union_slot = base + DW + 1;
            self.bytes_ptr_at(name_slot, f.name.as_bytes(), true);
            match &f.content {
                WireContent::Regular(b) | WireContent::Executable(b) => {
                    self.bytes_ptr_at(union_slot, b, false)
                }
                WireContent::Symlink(t) => self.bytes_ptr_at(union_slot, t.as_bytes(), true),
                WireContent::Directory(sub) => self.file_list_ptr_at(union_slot, sub),
            }
        }
    }

    /// Frame the single segment into the stream format (segment table + words).
    fn into_framed(self) -> Vec<u8> {
        let words = self.buf.len() / 8;
        let mut out = Vec::with_capacity(8 + self.buf.len());
        out.extend_from_slice(&0u32.to_le_bytes()); // segment count - 1 = 0
        out.extend_from_slice(&(words as u32).to_le_bytes());
        out.extend_from_slice(&self.buf);
        out
    }
}

impl Default for Builder {
    fn default() -> Self {
        Self::new()
    }
}

/// A file entry for the writer (mirrors the crate's `spk::FileContent` without coupling).
pub enum WireContent<'a> {
    Regular(&'a [u8]),
    Executable(&'a [u8]),
    Symlink(&'a str),
    Directory(Vec<WireFile<'a>>),
}

/// A file node for the writer.
pub struct WireFile<'a> {
    pub name: &'a str,
    pub content: WireContent<'a>,
    pub mtime_ns: i64,
}

impl WireFile<'_> {
    fn discriminant(&self) -> u16 {
        match self.content {
            WireContent::Regular(_) => 0,
            WireContent::Executable(_) => 1,
            WireContent::Symlink(_) => 2,
            WireContent::Directory(_) => 3,
        }
    }
}

/// Serialize an `Archive` (a `List(File)` root) to a framed capnp message.
pub fn write_archive(files: &[WireFile]) -> Vec<u8> {
    let mut b = Builder::new();
    let root_slot = b.alloc(1);
    // Archive struct: 0 data words, 1 pointer (the files list).
    let archive_struct = b.alloc(1);
    b.struct_ptr_at(root_slot, archive_struct, 0, 1);
    b.file_list_ptr_at(archive_struct, files);
    b.into_framed()
}

/// Serialize a `Signature { publicKey :Data, signature :Data }` to a framed message.
pub fn write_signature(public_key: &[u8], signature: &[u8]) -> Vec<u8> {
    let mut b = Builder::new();
    let root_slot = b.alloc(1);
    // Signature struct: 0 data words, 2 pointers.
    let sig_struct = b.alloc(2);
    b.struct_ptr_at(root_slot, sig_struct, 0, 2);
    b.bytes_ptr_at(sig_struct, public_key, false);
    b.bytes_ptr_at(sig_struct + 1, signature, false);
    b.into_framed()
}

// ---------------------------------------------------------------------------
// Little-endian readers with bounds checks (no panics on bad input).
// ---------------------------------------------------------------------------

fn read_u16(b: &[u8], off: usize) -> Option<u16> {
    b.get(off..off + 2)
        .map(|s| u16::from_le_bytes([s[0], s[1]]))
}
fn read_u32(b: &[u8], off: usize) -> Option<u32> {
    b.get(off..off + 4)
        .map(|s| u32::from_le_bytes([s[0], s[1], s[2], s[3]]))
}
fn read_u64(b: &[u8], off: usize) -> Option<u64> {
    b.get(off..off + 8)
        .map(|s| u64::from_le_bytes([s[0], s[1], s[2], s[3], s[4], s[5], s[6], s[7]]))
}

/// Sign-extend a 30-bit two's-complement pointer offset to `i64`.
fn sign_extend_30(v: u64) -> i64 {
    let v = v & 0x3fff_ffff;
    if v & 0x2000_0000 != 0 {
        (v as i64) - (1 << 30)
    } else {
        v as i64
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn round_trips_an_archive_through_the_real_wire() {
        let files = vec![
            WireFile {
                name: "README",
                content: WireContent::Regular(b"hello"),
                mtime_ns: 42,
            },
            WireFile {
                name: "app",
                content: WireContent::Directory(vec![
                    WireFile {
                        name: "server",
                        content: WireContent::Executable(b"\x7fELF"),
                        mtime_ns: 7,
                    },
                    WireFile {
                        name: "link",
                        content: WireContent::Symlink("server"),
                        mtime_ns: 0,
                    },
                ]),
                mtime_ns: 0,
            },
        ];
        let bytes = write_archive(&files);
        let (msg, consumed) = Message::parse_prefix(&bytes).unwrap();
        assert_eq!(consumed, bytes.len());
        let root = msg.root().unwrap();
        let list = root.get_list(0).unwrap().unwrap();
        let structs = list.structs().unwrap();
        assert_eq!(structs.len(), 2);
        assert_eq!(structs[0].get_text(0).unwrap(), "README");
        assert_eq!(structs[0].get_u16(0), 0); // regular
        assert_eq!(structs[0].get_i64(8), 42);
        assert_eq!(structs[0].get_data(1).unwrap(), b"hello");
        // The directory nests.
        assert_eq!(structs[1].get_text(0).unwrap(), "app");
        assert_eq!(structs[1].get_u16(0), 3); // directory
        let sub = structs[1].get_list(1).unwrap().unwrap().structs().unwrap();
        assert_eq!(sub.len(), 2);
        assert_eq!(sub[0].get_text(0).unwrap(), "server");
        assert_eq!(sub[0].get_u16(0), 1); // executable
        assert_eq!(sub[0].get_data(1).unwrap(), b"\x7fELF");
        assert_eq!(sub[1].get_u16(0), 2); // symlink
        assert_eq!(sub[1].get_text(1).unwrap(), "server");
    }

    #[test]
    fn round_trips_a_signature() {
        let pk = [0xabu8; 32];
        let sig = [0xcdu8; 128];
        let bytes = write_signature(&pk, &sig);
        let (msg, _) = Message::parse_prefix(&bytes).unwrap();
        let root = msg.root().unwrap();
        assert_eq!(root.get_data(0).unwrap(), pk);
        assert_eq!(root.get_data(1).unwrap(), sig);
    }

    #[test]
    fn a_truncated_frame_is_refused() {
        let bytes = write_signature(&[1u8; 32], &[2u8; 128]);
        assert!(Message::parse_prefix(&bytes[..4]).is_err());
    }

    #[test]
    fn an_overlarge_composite_count_is_refused_before_allocation() {
        // A list pointer claiming a huge composite body with no backing words.
        // Frame: 1 segment, 2 words. word0 = list pointer (composite, offset 0),
        // word1 = composite tag claiming a giant element count.
        let mut buf = Vec::new();
        buf.extend_from_slice(&0u32.to_le_bytes()); // segcount-1
        buf.extend_from_slice(&2u32.to_le_bytes()); // 2 words
                                                    // list pointer: type=1, offset=0 (tag is the next word), elem=7, count=huge.
        let p: u64 = 1 | (0u64 << 2) | (7u64 << 32) | (0x1fff_ffffu64 << 35);
        buf.extend_from_slice(&p.to_le_bytes());
        // composite tag: element count = huge, stride 1.
        let tag: u64 = ((0x1fff_ffffu64) << 2) | (1u64 << 32);
        buf.extend_from_slice(&tag.to_le_bytes());
        let (msg, _) = Message::parse_prefix(&buf).unwrap();
        let root_list = msg.root();
        // root() expects a struct; here the root is a list, so it errors — fetch the
        // list directly to exercise the count guard.
        assert!(root_list.is_err());
        let (msg2, _) = Message::parse_prefix(&buf).unwrap();
        // Re-resolve word0 as a list and assert structs() refuses the over-count.
        let seg0 = &buf[8..];
        let p0 = u64::from_le_bytes(seg0[0..8].try_into().unwrap());
        let resolved = msg2.follow(0, 0, p0, 0).unwrap();
        match resolved {
            Resolved::List(l) => assert!(matches!(
                l.structs(),
                Err(CapnpError::ListTooLarge) | Err(CapnpError::Framing(_))
            )),
            _ => panic!("expected a list"),
        }
    }
}
