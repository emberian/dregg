# sel4/Makefile — build + boot the dregg Robigalia v0 seL4 image.
#
# This BOOTS on a native-macOS toolchain (Microkit SDK 2.2.0 + rust-sel4 +
# qemu-system-aarch64/riscv64). Run `./setup.sh` once to install deps + the SDK,
# then `make run` (aarch64) or `make run-riscv` (riscv64).
#
# Boot ladder (.docs-history-noclaude/SEL4-EMBEDDING.md §5), each an actual QEMU boot:
#   make run-m0   — M0: a Rust PD prints "dregg robigalia v0" on seL4.
#   make run-m1   — M1: the verifier PD (proof-in -> verdict-out contract).
#   make run-m2   — M2: the rbg DirectoryCell PD (the Robigalia heart).
#   make run-riscv— M5: M0 retargeted to qemu_virt_riscv64.
#   make run      — alias for run-m2 (the richest single-PD demo).

# ── Configuration ───────────────────────────────────────────────────────────
MICROKIT_SDK ?= $(HOME)/sel4-sdk/microkit-sdk-2.2.0
BOARD        ?= qemu_virt_aarch64
CONFIG       ?= debug
PD_DIR       := dregg-pd
BUILD        ?= build
MICROKIT     := $(MICROKIT_SDK)/bin/microkit

# The libsel4 headers rust-sel4's build.rs locates via $SEL4_INCLUDE_DIRS.
export SEL4_INCLUDE_DIRS := $(MICROKIT_SDK)/board/$(BOARD)/$(CONFIG)/include

# The aarch64 / riscv64 seL4 Microkit target specs (vendored in dregg-pd/targets).
AARCH64_TARGET := targets/aarch64-sel4-microkit.json
RISCV_TARGET   := targets/riscv64imac-sel4-microkit.json

CARGO_FLAGS := --release -Z json-target-spec

# QEMU: the qemu_virt_aarch64 Microkit kernel is built as a hypervisor, so the
# vCPU must have EL2 — `virtualization=on`.
QEMU_AARCH64 := qemu-system-aarch64 -machine virt,virtualization=on -cpu cortex-a53 \
                -m 2G -nographic
# The 5-PD assembly's executor seat embeds the verified Lean image (~280 MiB of
# ELF segments); the loader copies it into RAM, so the assembly needs more guest
# memory than the single-PD demos. (.docs-history-noclaude/EMBEDDABLE-LEAN-RUNTIME.md §4.)
QEMU_AARCH64_ASSEMBLY := qemu-system-aarch64 -machine virt,virtualization=on \
                -cpu cortex-a53 -m 4G -nographic
QEMU_RISCV   := qemu-system-riscv64 -machine virt -m 2G -nographic

# The GRAPHICAL boot reuses the same EL2 `virt` machine but DROPS -nographic and
# adds a display device. We keep the kernel/vCPU flags but build the QEMU line
# explicitly (so the serial stays on stdio for boot diagnostics alongside the
# window). `-device ramfb` is the simplest display on `virt`: a RAM framebuffer
# the compositor-fb PD configures over fw_cfg + scans out.
QEMU_AARCH64_GRAPHICAL := qemu-system-aarch64 -machine virt,virtualization=on \
                -cpu cortex-a53 -m 2G -device ramfb
# macOS display backend. On Linux swap `cocoa,show-cursor=on` for `gtk` (or
# `sdl`); everything else is identical.
QEMU_DISPLAY ?= cocoa,show-cursor=on

PHONY_CHOKEPOINT := build-chokepoint run-chokepoint
.PHONY: $(PHONY_CHOKEPOINT)
.PHONY: all run run-m0 run-m1 run-m2 run-stark run-net run-assembly run-riscv \
        build-executor-microkit verify-executor-microkit \
        build-assembly-real run-assembly-real \
        build-aarch64 build-assembly build-riscv build-graphical run-graphical \
        run-graphical-headless build-tutorial run-tutorial run-tutorial-headless \
        build-image run-image run-image-headless capture-image-modes \
        build-deos-live run-deos-live run-deos-live-headless \
        verify-isolation clean help

help:
	@echo "dregg Robigalia v0 seL4 image:"
	@echo "  ./setup.sh        — install deps + Microkit SDK (run once)"
	@echo "  make run          — boot the rbg DirectoryCell PD (M2) in QEMU"
	@echo "  make run-m0       — boot the 'dregg robigalia v0' banner PD (M0)"
	@echo "  make run-m1       — boot the verifier PD (M1)"
	@echo "  make run-m2       — boot the rbg DirectoryCell PD (M2)"
	@echo "  make run-stark    — boot the verifier-stark PD: real STARK on-device"
	@echo "  make run-net      — boot the net-driver PD: probe a REAL virtio-net (M3 edge)"
	@echo "  make run-assembly — boot the 5-PD FIRMAMENT (verifier+executor+persist+net+app)"
	@echo "  make run-graphical— boot the compositor-fb PD: REAL ramfb pixels in a QEMU window"
	@echo "  make run-graphical-headless — same image, -display none, serial-proves ramfb config"
	@echo "  make run-tutorial — boot the deos ONBOARDING: interactive multi-screen tutorial + keyboard"
	@echo "  make run-tutorial-headless  — same image, -display none, for screendump capture"
	@echo "  make run-image    — boot the deos LIVE IMAGE VIEWER: a live object browser of REAL cells"
	@echo "  make run-image-headless     — same image, -display none, for screendump capture"
	@echo "  make capture-image-modes    — boot headless, screendump BOTH modes (image + TAB->gpui cockpit)"
	@echo "  make run-riscv    — boot M0 on qemu_virt_riscv64 (M5)"

all: build-aarch64

# ── Cross-build the PD ELFs (aarch64) ───────────────────────────────────────
build-aarch64:
	cd $(PD_DIR) && cargo build $(CARGO_FLAGS)

build-riscv:
	cd $(PD_DIR) && SEL4_INCLUDE_DIRS=$(MICROKIT_SDK)/board/qemu_virt_riscv64/$(CONFIG)/include \
		cargo build $(CARGO_FLAGS) --target $(RISCV_TARGET) -p dregg-m0-hello

# M5 full: build the verifier-stark heart organ + the rbg DirectoryCell heart
# for riscv64 (the same no_std PDs that boot M-STARK/M2 on aarch64; they are
# arch-agnostic — sel4-microkit + blake3/serde only). Its own target dir
# (target-riscv) so it never collides with the aarch64 `target/`.
build-riscv-full:
	cd $(PD_DIR) && SEL4_INCLUDE_DIRS=$(MICROKIT_SDK)/board/qemu_virt_riscv64/$(CONFIG)/include \
		CARGO_TARGET_DIR=target-riscv \
		cargo build $(CARGO_FLAGS) --target $(RISCV_TARGET) \
			-p dregg-verifier-stark-pd -p dregg-rbg-dir

# ── Link an image for one PD and boot it (aarch64) ──────────────────────────
# $1 = PD elf basename (no ext), $2 = system file, $3 = pd-xml-name
define LINK_AND_RUN_AARCH64
	mkdir -p $(BUILD)
	cp $(PD_DIR)/target/aarch64-sel4-microkit/release/$(1).elf $(BUILD)/
	printf '<?xml version="1.0" encoding="UTF-8"?>\n<system>\n  <protection_domain name="$(3)" priority="100" stack_size="0x10000">\n    <program_image path="$(1).elf" />\n  </protection_domain>\n</system>\n' > $(BUILD)/$(1).system
	$(MICROKIT) $(BUILD)/$(1).system --search-path $(BUILD) --board $(BOARD) --config $(CONFIG) -o $(BUILD)/$(1).img -r $(BUILD)/$(1).report.txt
	$(QEMU_AARCH64) -device loader,file=$(BUILD)/$(1).img,addr=0x70000000,cpu-num=0 -serial mon:stdio
endef

run: run-m2

run-m0: build-aarch64
	$(call LINK_AND_RUN_AARCH64,dregg-m0-hello,m0,dregg_m0)

run-m1: build-aarch64
	$(call LINK_AND_RUN_AARCH64,dregg-verifier-pd,m1,dregg_verifier)

run-m2: build-aarch64
	$(call LINK_AND_RUN_AARCH64,dregg-rbg-dir,m2,dregg_rbg_dir)

# M1+ : the verified-compute heart organ — a REAL plonky3-style STARK
# (BabyBear+BLAKE3+FRI) proved + verified on-device, with the anti-ghost tooth.
run-stark: build-aarch64
	$(call LINK_AND_RUN_AARCH64,dregg-verifier-stark-pd,mstark,dregg_verifier_stark)

# M3: the firmament's network EDGE — the virtio-net driver PD probing a REAL
# QEMU virtio-net-device on the mmio bus. The driver maps mmio slot 31 (base
# 0xa000000 + 31*0x200 = 0xa003e00; region phys_addr 0xa003000 + OFFSET 0xe00),
# reads the VirtIOHeader, confirms DeviceType::Network, and brings the device UP
# (prints its MAC). The QEMU flags below are what make the slot non-empty — the
# wall this clears was InvalidDeviceType(0) (an empty mmio slot).
run-net: build-aarch64
	mkdir -p $(BUILD)
	cp $(PD_DIR)/target/aarch64-sel4-microkit/release/dregg-net-driver-pd.elf $(BUILD)/
	$(MICROKIT) net-driver-only.system --search-path $(BUILD) --board $(BOARD) --config $(CONFIG) -o $(BUILD)/net-driver.img -r $(BUILD)/net-driver.report.txt
	$(QEMU_AARCH64) \
		-global virtio-mmio.force-legacy=false \
		-netdev user,id=net0 \
		-device virtio-net-device,netdev=net0,bus=virtio-mmio-bus.31 \
		-device loader,file=$(BUILD)/net-driver.img,addr=0x70000000,cpu-num=0 \
		-serial mon:stdio

# ── THE 5-PD FIRMAMENT ASSEMBLY (dregg.system) ──────────────────────────────
# Wire the real PDs into ONE booting multi-PD seL4 image (.docs-history-noclaude/FIRMAMENT.md §2):
#   verifier — dregg-verifier-stark-pd : a REAL BabyBear+BLAKE3+FRI STARK
#              proved+verified on-device (the bankable verified-compute HEART
#              ORGAN; anti-ghost teeth fire). Self-contains its proof — no Lean.
#   executor — dregg-executor-microkit-pd : the HEART, REAL. EMBEDS the VERIFIED
#              Lean executor (dregg_exec_full_forest_auth = execFullForestG +
#              admission, proved in metatheory/). Reads turn_in (R) → runs the
#              verified turn → writes the receipt to commit_out (RW) → signals
#              persist+verifier. The §2 Lean-ELF blocker is CLEARED (musl +
#              libuv-excised runtime folded from executor-rootserver). A real
#              verified turn flows through this PD (status:2 ok:1).
#   persist  — dregg-persist-stub-pd   : the durable-store seat. Maps commit_out
#              (R) ONLY and reads the executor's sentinel back — the cross-PD
#              channel proven live. The storage-device cap lands HERE (§3).
#   net      — dregg-net-driver-pd     : the EDGE. SOLE holder of the NIC cap +
#              virtio-mmio + DMA paddr + IRQ 79; probes a REAL virtio-net device
#              and brings the NIC UP (the n>1 end of the cap gradation, §3).
#   app      — dregg-rbg-dir           : a houyhnhnm app-PD (rbg DirectoryCell:
#              CAS + ACL + factory slot-caveat). Holds ONLY its own caps.
# The cap partition IS the trust boundary ("capabilities all the way down").
# QEMU carries the same -device virtio-net-device the net edge probes (slot 31).
# The REAL executor PD lives in its OWN workspace (it links the heavy verified
# Lean closure + the seL4-musl-rebuilt runtime; keeping it out of the dregg-pd
# workspace keeps the other PDs' build light). It needs LIBCLANG_PATH (the sel4
# crate's bindgen) + the same SEL4_INCLUDE_DIRS. The seL4-musl archive set it
# links is provisioned by executor-rootserver/scripts/{provision-sel4,
# relink-roottask}.sh (already run; see ../docs/EMBEDDABLE-LEAN-RUNTIME.md §4).
EXEC_MK_DIR  := $(PD_DIR)/executor-microkit-pd
EXEC_MK_ELF  := $(EXEC_MK_DIR)/target/aarch64-sel4-microkit/release/dregg-executor-microkit-pd.elf
LIBCLANG_PATH ?= /opt/homebrew/opt/llvm/lib

# Build the REAL executor PD: a Microkit PD that LINKS the verified Lean executor
# (dregg_exec_full_forest_auth) + the ELF Lean runtime + the real crypto floor +
# the seL4 musl into one ELF (0 undefined symbols). This is the firmament
# keystone artifact (executor-microkit-pd/WALL.md). Run `make verify-executor-
# microkit` to confirm the verified entry is embedded.
build-executor-microkit:
	cd $(EXEC_MK_DIR) && LIBCLANG_PATH=$(LIBCLANG_PATH) \
		SEL4_INCLUDE_DIRS=$(SEL4_INCLUDE_DIRS) \
		cargo build --release -Z json-target-spec

# Prove the verified executor entry is embedded in the assembled PD ELF (T =
# defined text), with zero undefined symbols.
verify-executor-microkit: build-executor-microkit
	@echo "== verified entry embedded in the assembled Microkit PD: =="
	@nm $(EXEC_MK_ELF) | grep ' T dregg_exec_full_forest_auth' || \
		(echo "MISSING verified entry!" && exit 1)
	@echo "== undefined symbols in the static PD (must be 0): =="
	@nm $(EXEC_MK_ELF) | grep -c ' U ' | xargs -I{} echo "   undefined: {}"

# ── build-assembly-real: the REAL executor seat — BOOTS ─────────────────────
# Builds the 5-PD image with the REAL executor PD (dregg-executor-microkit-pd,
# embedding the VERIFIED executor) wired into dregg.system, and packages it into
# ONE bootable Microkit image. The verified turn runs status:2 ok:1 INSIDE the
# assembled PD (executor-microkit-pd/microkit-patch/assembly-boot-evidence.log).
#
# TWO things make the ~300-MiB-text executor PD fit a Microkit image:
#   1. The PD ELF is linked with `-z max-page-size=0x200000` (its .cargo/config
#      .toml) so its PT_LOAD segments are 2 MiB-aligned.
#   2. A one-function microkit-tool patch maps PD image segments with 2 MiB Large
#      pages where alignment permits (stock microkit hard-codes 4 KiB for every
#      image frame). Without it the executor needs ~83,000 frame caps and the
#      on-device CapDL initialiser exhausts ROOT_CNODE_SIZE_BITS (OutOfSlots);
#      with it the image is ~170 Large frames + small tails (2,322 objects total).
#      The patch + the prebuilt patched tool are in
#      executor-microkit-pd/microkit-patch/ (0001-2mib-elf-image-pages.patch,
#      built against the microkit 2.2.0 tag to match the SDK's initialiser.elf).
#      Install it once:  cp executor-microkit-pd/microkit-patch/microkit-2.2.0-patched \
#                           $(MICROKIT)
# The SDK loader.elf is relinked to 0x90000000 (loader.elf.orig-0x70000000 is the
# backup); QEMU loads the image blob at addr=0x90000000 to match.
build-assembly-real: build-aarch64 build-executor-microkit
	cd $(PD_DIR) && cargo build $(CARGO_FLAGS) \
		-p dregg-verifier-stark-pd \
		-p dregg-persist-stub-pd -p dregg-net-driver-pd -p dregg-rbg-dir
	# net_client (the ingress edge): built WITH `executor-ingress` so it stages a
	# verified turn into turn_in + signals the executor (own invocation because
	# --features is package-scoped). This is the 6th PD that closes the wire→heart
	# path in dregg.system.
	cd $(PD_DIR) && cargo build $(CARGO_FLAGS) \
		-p dregg-net-client-pd --features dregg-net-client-pd/executor-ingress
	mkdir -p $(BUILD)
	cp $(PD_DIR)/target/aarch64-sel4-microkit/release/dregg-verifier-stark-pd.elf $(BUILD)/
	cp $(EXEC_MK_ELF)                                                              $(BUILD)/
	cp $(PD_DIR)/target/aarch64-sel4-microkit/release/dregg-persist-stub-pd.elf   $(BUILD)/
	cp $(PD_DIR)/target/aarch64-sel4-microkit/release/dregg-net-driver-pd.elf     $(BUILD)/
	cp $(PD_DIR)/target/aarch64-sel4-microkit/release/dregg-net-client-pd.elf     $(BUILD)/
	cp $(PD_DIR)/target/aarch64-sel4-microkit/release/dregg-rbg-dir.elf           $(BUILD)/
	$(MICROKIT) dregg.system --search-path $(BUILD) --board $(BOARD) --config $(CONFIG) -o $(BUILD)/dregg-real.img -r $(BUILD)/dregg-real.report.txt

# Boot the REAL 6-PD firmament: a SignedTurn on TCP :5555 is Ed25519-checked by
# the net_client (ingress) PD, staged into turn_in, and run by the VERIFIED Lean
# executor (status:2 ok:1) through the assembled PD's channels (turn_in/
# commit_out); the verifier-stark PD verifies a real STARK, persist reads the
# commit, the net driver brings the NIC up. The hostfwd maps host :5555 -> guest.
run-assembly-real: build-assembly-real
	$(QEMU_AARCH64_ASSEMBLY) \
		-global virtio-mmio.force-legacy=false \
		-netdev user,id=net0,hostfwd=tcp::5555-:5555 \
		-device virtio-net-device,netdev=net0,bus=virtio-mmio-bus.31 \
		-device loader,file=$(BUILD)/dregg-real.img,addr=0x90000000,cpu-num=0 \
		-serial mon:stdio

# ── build-chokepoint / run-chokepoint: the in-path receipt device ──────────────
# Two PDs (chokepoint.system): commit (the Lean step `dregg_chokepoint_arrive`, Lean 4.30.0,
# compiled to C and linked against the seL4-built runtime; SOLE holder of the NIC region and
# IRQ) and persist (SOLE holder of the log; reached by a synchronous PPC). Boots in QEMU:
# four frames persisted-then-forwarded, two refused at capacity
# (chokepoint-boot-evidence.log). Needs the exec-sel4 runtime archives provisioned by
# dregg-pd/executor-rootserver (as build-executor-microkit does).
CP_DIR := $(PD_DIR)/chokepoint
CP_REL := $(CP_DIR)/target/aarch64-sel4-microkit/release
build-chokepoint:
	$(CP_DIR)/scripts/build-lean.sh
	cd $(CP_DIR) && cargo build $(CARGO_FLAGS)
	mkdir -p build-chokepoint
	cp $(CP_REL)/dregg-chokepoint-commit-pd.elf $(CP_REL)/dregg-chokepoint-persist-pd.elf build-chokepoint/
	$(MICROKIT) chokepoint.system --search-path build-chokepoint --board $(BOARD) --config $(CONFIG) -o build-chokepoint/chokepoint.img -r build-chokepoint/chokepoint.report.txt

run-chokepoint: build-chokepoint
	$(QEMU_AARCH64) -global virtio-mmio.force-legacy=false \
		-netdev user,id=net0 -device virtio-net-device,netdev=net0,bus=virtio-mmio-bus.31 \
		-device loader,file=build-chokepoint/chokepoint.img,addr=0x70000000,cpu-num=0 -serial mon:stdio

# ── build-assembly / run-assembly: the BOOTABLE 5-PD firmament demo ──────────
# The same 5-PD firmament, with the executor seat held by the small stub PD
# (dregg-stub.system) so the WHOLE assembly BOOTS in QEMU today (the real
# executor PD links the verified turn — see build-assembly-real + WALL.md — but
# its 285-MiB-text image overflows the microkit tool's fixed loader). This keeps
# the firmament boot demonstrable while the verified-executor seat is the linked
# keystone artifact + the verified turn boots under seL4 via the rootserver.
build-assembly: build-aarch64
	cd $(PD_DIR) && cargo build $(CARGO_FLAGS) \
		-p dregg-verifier-stark-pd -p dregg-executor-stub-pd \
		-p dregg-persist-stub-pd -p dregg-net-driver-pd -p dregg-rbg-dir
	mkdir -p $(BUILD)
	cp $(PD_DIR)/target/aarch64-sel4-microkit/release/dregg-verifier-stark-pd.elf $(BUILD)/
	cp $(PD_DIR)/target/aarch64-sel4-microkit/release/dregg-executor-stub-pd.elf  $(BUILD)/
	cp $(PD_DIR)/target/aarch64-sel4-microkit/release/dregg-persist-stub-pd.elf   $(BUILD)/
	cp $(PD_DIR)/target/aarch64-sel4-microkit/release/dregg-net-driver-pd.elf     $(BUILD)/
	cp $(PD_DIR)/target/aarch64-sel4-microkit/release/dregg-rbg-dir.elf           $(BUILD)/
	$(MICROKIT) dregg-stub.system --search-path $(BUILD) --board $(BOARD) --config $(CONFIG) -o $(BUILD)/dregg.img -r $(BUILD)/dregg.report.txt

run-assembly: build-assembly
	$(QEMU_AARCH64) \
		-global virtio-mmio.force-legacy=false \
		-netdev user,id=net0 \
		-device virtio-net-device,netdev=net0,bus=virtio-mmio-bus.31 \
		-device loader,file=$(BUILD)/dregg.img,addr=0x70000000,cpu-num=0 \
		-serial mon:stdio

# ── THE GRAPHICAL BOOT (dregg-graphical.system) ─────────────────────────────
# The compositor-fb PD drives a REAL framebuffer visible in a QEMU window: it is
# the SOLE holder of the fw_cfg engine MMIO cap (phys 0x9020000) + a 2 MiB DMA
# framebuffer region (its guest-PHYSICAL base handed to ramfb via region_paddr),
# configures QEMU's `ramfb` display over fw_cfg, and writes a deos splash (test
# pattern + banner) into the framebuffer (docs/desktop-os-research/
# GRAPHICAL-SEL4-BOOT.md). The bytes->glass path on seL4, end to end.
build-graphical:
	cd $(PD_DIR) && cargo build $(CARGO_FLAGS) -p dregg-compositor-fb-pd
	mkdir -p $(BUILD)
	cp $(PD_DIR)/target/aarch64-sel4-microkit/release/dregg-compositor-fb-pd.elf $(BUILD)/
	$(MICROKIT) dregg-graphical.system --search-path $(BUILD) --board $(BOARD) --config $(CONFIG) -o $(BUILD)/dregg-graphical.img -r $(BUILD)/dregg-graphical.report.txt

# THE VISIBLE WINDOW — run this for ember: a real QEMU window scanning out the
# PD's pixels. Serial stays on stdio so the boot diagnostics print alongside.
run-graphical: build-graphical
	$(QEMU_AARCH64_GRAPHICAL) \
		-display $(QEMU_DISPLAY) \
		-device loader,file=$(BUILD)/dregg-graphical.img,addr=0x70000000,cpu-num=0 \
		-serial mon:stdio

# Window-less proof (CI / background): the SAME image with -display none. The PD
# still configures ramfb + draws; its serial output proves resolution, fb phys
# addr, the etc/ramfb selector, and bytes written — verifiable with no window.
run-graphical-headless: build-graphical
	$(QEMU_AARCH64_GRAPHICAL) \
		-display none \
		-device loader,file=$(BUILD)/dregg-graphical.img,addr=0x70000000,cpu-num=0 \
		-serial mon:stdio

# ── THE deos ONBOARDING (deos-tutorial.system) ──────────────────────────────
# The deos-tutorial PD boots a polished, multi-screen, INTERACTIVE tutorial: it
# drives ramfb (like compositor-fb) AND a virtio-keyboard-device (virtio-mmio
# slot 30, the same device-cap discipline the net PD uses), so the newcomer
# presses SPACE / UP / DOWN to walk a six-screen arc teaching deos from first
# principles, rendering REAL deos data shapes (a cell's four substances, an
# affordance's cap-gate, a dregg:// reference). docs/desktop-os-research/
# GRAPHICAL-SEL4-BOOT.md.
build-tutorial:
	cd $(PD_DIR) && cargo build $(CARGO_FLAGS) -p dregg-deos-tutorial-pd
	mkdir -p $(BUILD)
	cp $(PD_DIR)/target/aarch64-sel4-microkit/release/dregg-deos-tutorial-pd.elf $(BUILD)/
	$(MICROKIT) deos-tutorial.system --search-path $(BUILD) --board $(BOARD) --config $(CONFIG) -o $(BUILD)/deos-tutorial.img -r $(BUILD)/deos-tutorial.report.txt

# THE INTERACTIVE WINDOW — run this for ember: a real QEMU window scanning out
# the tutorial, with a real virtio-keyboard. Press SPACE / UP / DOWN to navigate.
# Serial stays on stdio so the boot diagnostics + screen transitions print.
run-tutorial: build-tutorial
	$(QEMU_AARCH64_GRAPHICAL) \
		-display $(QEMU_DISPLAY) \
		-global virtio-mmio.force-legacy=false \
		-device virtio-keyboard-device,bus=virtio-mmio-bus.30 \
		-device loader,file=$(BUILD)/deos-tutorial.img,addr=0x70000000,cpu-num=0 \
		-serial mon:stdio

# Window-less (CI / screendump capture over QMP): the SAME image, -display none.
# The PD configures ramfb + draws screen 1; drive keys over QMP send-key to step.
run-tutorial-headless: build-tutorial
	$(QEMU_AARCH64_GRAPHICAL) \
		-display none \
		-global virtio-mmio.force-legacy=false \
		-device virtio-keyboard-device,bus=virtio-mmio-bus.30 \
		-device loader,file=$(BUILD)/deos-tutorial.img,addr=0x70000000,cpu-num=0 \
		-serial mon:stdio

# ── THE deos LIVE IMAGE VIEWER (deos-image.system) ──────────────────────────
# The deos-image PD boots a Smalltalk/Pharo-style object browser of REAL deos
# cells: the left rail lists the ACTUAL cells in the image (a frozen snapshot of
# real `dregg_cell::CellState`s — real ids, balances, c-lists, fields, proofs;
# `deos-image/src/image_data.rs` is @generated by `cargo run -p dregg-cell
# --example gen_image_snapshot`), and the main pane inspects the FOCUSED cell.
# UP/DOWN walk between cells; ENTER drills into a cell's four substances
# (VALUE / STATE / AUTHORITY / EVIDENCE); ESC backs out. It drives ramfb (like
# the tutorial) AND a virtio-keyboard-device (virtio-mmio slot 30, the same
# device-cap discipline the net PD uses). docs/desktop-os-research/
# GRAPHICAL-SEL4-BOOT.md.
build-image:
	cd $(PD_DIR) && cargo build $(CARGO_FLAGS) -p dregg-deos-image-pd
	mkdir -p $(BUILD)
	cp $(PD_DIR)/target/aarch64-sel4-microkit/release/dregg-deos-image-pd.elf $(BUILD)/
	$(MICROKIT) deos-image.system --search-path $(BUILD) --board $(BOARD) --config $(CONFIG) -o $(BUILD)/deos-image.img -r $(BUILD)/deos-image.report.txt

# THE LIVE IMAGE WINDOW — run this for ember: a real QEMU window scanning out
# the cell browser, with a real virtio-keyboard. UP/DOWN walk cells, ENTER drills
# in, ESC backs out. Serial stays on stdio so the boot diagnostics + navigation
# transitions print.
run-image: build-image
	$(QEMU_AARCH64_GRAPHICAL) \
		-display $(QEMU_DISPLAY) \
		-global virtio-mmio.force-legacy=false \
		-device virtio-keyboard-device,bus=virtio-mmio-bus.30 \
		-device loader,file=$(BUILD)/deos-image.img,addr=0x70000000,cpu-num=0 \
		-serial mon:stdio

# Window-less (CI / screendump capture over QMP): the SAME image, -display none.
# The PD configures ramfb + paints the cell rail; drive keys over QMP send-key to
# walk cells and drill in, and `screendump` to capture the live browser.
run-image-headless: build-image
	$(QEMU_AARCH64_GRAPHICAL) \
		-display none \
		-global virtio-mmio.force-legacy=false \
		-device virtio-keyboard-device,bus=virtio-mmio-bus.30 \
		-device loader,file=$(BUILD)/deos-image.img,addr=0x70000000,cpu-num=0 \
		-serial mon:stdio

# EVIDENCE CAPTURE — boot the image headless, drive the virtio-keyboard over QMP,
# and screendump BOTH modes to PNG: the LIVE IMAGE (the cell browser) and — after
# a QMP `send-key TAB` — the starbridge-v2 COCKPIT (the REAL gpui render, lavapipe
# / no GPU, baked into the PD and blitted onto the ramfb framebuffer QEMU scans
# out — docs/desktop-os-research/GPUI-OFFSCREEN-FORK.md). Writes
# /tmp/sel4-cockpit-{image,cockpit}-mode.png. This is the gpui->seL4-framebuffer
# weld's reproducible proof.
capture-image-modes: build-image
	python3 scripts/capture-cockpit-mode.py

# ── LIVE-REPAINT-ON-TURN on real seL4 (deos-live.system) ────────────────────
# A two-PD image: the VERIFIED executor PD (dregg-executor-microkit-pd, embedding
# `dregg_exec_full_forest_auth`) ⊕ the LIVE IMAGE VIEWER PD (deos-image, ramfb +
# virtio-keyboard). The executor runs a REAL verified turn, writes the receipt to
# the shared commit_out region, and signals the viewer (channel id 2 ⇄ id 1); the
# viewer reads the genuine receipt and paints the "VERIFIED TURN on seL4" banner
# on glass. A genuine verified turn drives live-repaint, on real seL4.
#
# REUSES the banked executor PD ELF (the firmament keystone, executor-microkit-pd
# /WALL.md) — no relink. Like build-assembly-real, the ~285-MiB executor needs
# (1) the 2 MiB-page microkit patch and (2) the relinked 0x90000000 loader, both
# already installed (executor-microkit-pd/microkit-patch/). QEMU loads the image
# at addr=0x90000000 and adds -device ramfb + the virtio-keyboard.
build-deos-live: build-image
	@test -f $(EXEC_MK_ELF) || (echo "executor PD ELF missing: $(EXEC_MK_ELF) — run 'make build-executor-microkit' first" && exit 1)
	mkdir -p $(BUILD)
	cp $(EXEC_MK_ELF) $(BUILD)/
	$(MICROKIT) deos-live.system --search-path $(BUILD) --board $(BOARD) --config $(CONFIG) -o $(BUILD)/deos-live.img -r $(BUILD)/deos-live.report.txt

# Boot WITH a window: the cell browser on ramfb; the executor's verified turn
# repaints the live-turn banner the instant the assembly comes up. UP/DOWN still
# walk the cells (the banner rides every paint).
run-deos-live: build-deos-live
	qemu-system-aarch64 -machine virt,virtualization=on -cpu cortex-a53 -m 4G \
		-device ramfb -display $(QEMU_DISPLAY) \
		-global virtio-mmio.force-legacy=false \
		-device virtio-keyboard-device,bus=virtio-mmio-bus.30 \
		-device loader,file=$(BUILD)/deos-live.img,addr=0x90000000,cpu-num=0 \
		-serial mon:stdio

# Window-less (CI / screendump capture over QMP): the SAME image, -display none.
run-deos-live-headless: build-deos-live
	qemu-system-aarch64 -machine virt,virtualization=on -cpu cortex-a53 -m 4G \
		-device ramfb -display none \
		-global virtio-mmio.force-legacy=false \
		-device virtio-keyboard-device,bus=virtio-mmio-bus.30 \
		-device loader,file=$(BUILD)/deos-live.img,addr=0x90000000,cpu-num=0 \
		-serial mon:stdio

# ── M5: M0 on riscv64 ───────────────────────────────────────────────────────
run-riscv: build-riscv
	mkdir -p $(BUILD)
	cp $(PD_DIR)/target/riscv64imac-sel4-microkit/release/dregg-m0-hello.elf $(BUILD)/
	printf '<?xml version="1.0" encoding="UTF-8"?>\n<system>\n  <protection_domain name="dregg_m0" priority="100" stack_size="0x10000">\n    <program_image path="dregg-m0-hello.elf" />\n  </protection_domain>\n</system>\n' > $(BUILD)/m0-riscv.system
	$(MICROKIT) $(BUILD)/m0-riscv.system --search-path $(BUILD) --board qemu_virt_riscv64 --config $(CONFIG) -o $(BUILD)/m0-riscv.img -r $(BUILD)/m0-riscv.report.txt
	$(QEMU_RISCV) -kernel $(BUILD)/m0-riscv.img -serial mon:stdio

# ── The HOST proof: the verify core links Lean-free (runs anywhere) ──────────
verify-isolation:
	cargo build -p dregg-verifier --features no-lean-link
	@echo "--- linked dynamic libs (expect system libs only) ---"
	@otool -L ../target/debug/dregg-verifier 2>/dev/null || true
	@! nm ../target/debug/dregg-verifier 2>/dev/null | grep -iE "uv_run|lean_initialize|leanrt|__gmp" \
		&& echo "PASS: no Lean runtime symbols" || (echo "FAIL: Lean symbols present" && exit 1)

clean:
	rm -rf $(BUILD) $(PD_DIR)/target
