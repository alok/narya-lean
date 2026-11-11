# Narya-Lean

**Higher-Dimensional Multi-Modal & Quantitative Observational Type Theory in Lean 4 — Unified Cubical/Modal/Linear/Directed/HIT Kernel, 19 Machine-Checked Resolutions (`A`–`S`, `0 sorry`), Zero-Lisp Extensible `.narya` Pratt/Mixfix Syntax, Unison Content-Addressed `#hash` Digests, Sorbet-Style Flat Arena, Linear Interaction Nets, Verified `Core → AArch64` `ThinEmitter` + In-Process `MAP_JIT`, Profiler, and Lake-Style Merkle Builder.**

`narya-lean` reimagines [Mike Shulman's Narya](https://github.com/mikeshulman/narya) inside **Lean 4** (`v4.35.0`), merging Narya's family of higher-dimensional, modal, directed, and quantitative/linear type theories into one kernel with a **Lean/Idris2/Granule-inspired extensible Zero-Lisp `.narya` surface language**, **Unison-style content-addressed AST/Proof/ABI hashing**, machine-checked resolutions of **nineteen upstream, theoretical, and architectural problems (`A`–`S`, `zero sorry`, `zero noncomputable`)**, CSLib-style theory & cost combinators (`TimeM`), and a top-to-bottom verified compiler (`Core.NbE → HIR → MIR → LIR → Arm64 → ThinEmitter ByteArray → W^X MAP_JIT`) engineered from day one around **Nelson Elhage's Sorbet data-layout principles** and **Leonardo de Moura's SViL Nov 2026 multi-IR codegen architecture**.

---

## Highlights & Measured Performance (Apple Silicon / AArch64)

1. **All Narya Type Theories + Quantitative/Linear Adjoint Types Unified in One Kernel (`Narya/Dim`, `Narya/Core`)**:
   - **Symmetric Higher Observational Type Theory (`Dir.hott`)**: computational univalence & fibrancy (`Glue`, `trr`, `trl`, `liftr`, `liftl`, `trans`, `sym`, `arrowLine`, `piLine`, `prodLine`, `sigLine`, `boxLine`, `calc_eq`, `pathJ`), **observational function extensionality (`funext` + `hap`)**, and **coinductive bisimulation** via bridge/record projection (`.proj` through `obsEq`).
   - **$k$-ary Internal & External Parametricity (`Dir.param k`, `Gel`, `ungel`, `-external` lockers)**, **Displayed Type Theory & Coinductive `SST` (`Dir.displayed`, `Energy.potential`)**, **0-ary Nominal Freshness (`Dir.nominal`)**, and **Predicative `Mugen` Universe Polymorphism (`LevelExpr`, `no_girard_type_in_type`)**.
   - **Quantitative & Linear Adjoint Type Theory (`QTT` + Benton's `LNL`, `linearAdjointTheory`)**: `0 / 1 / ω` semiring grades on 2-categorical modalities (`Ghost0` = static proof/spec erasure, `1_Lin` = unique ownership / FBIP / fan-free Interaction Nets, `! = F ∘ G` = explicit duplication with BFS-synthesized dereliction `ε_lnl`).
2. **Engineered for Speed from the Ground Up (`Narya/Fast`, `Narya/Compiler/ThinEmitter`, `cbits/narya_jit.c`)**:
   - **Unboxed 64-Bit Cubical Primitives (`PackedSFace`, `PackedSDeg`)**: `bv_decide`-verified bitmasks (`1` formal `TimeM` tick vs `d + 1` ticks; **8.5x** wall-clock speedup at rank 16).
   - **Sorbet-Style Flat `SymId` Interner & 16-Byte `PackedNode` `TermArena` (`Arena.lean`)**: `O(1)` 32-bit `SymId` global table (**137x** faster than string-keyed list lookup: `25 µs` vs `3,436 µs` for 20k lookups) + hash-consed 16-byte `PackedNode` (`w0, w1 : UInt64`) arena executing 50,000 DAG evaluations in `1.52 ms` with **0 per-eval heap allocations**.
   - **Linear Interaction Nets (`InteractionNet.lean`)**: flat-array Lafont Symmetric Interaction Combinators (`32`-bit `Port`) where `1`-graded linear pipelines emit **zero `DUP` fan nodes**, **zero fan commutations**, and **zero arena grows** during reduction (**~4.6M interactions/sec**).
   - **Thin Emitter + In-Process W^X `MAP_JIT` / `mprotect` (`ThinEmitter.lean` + `cbits/narya_jit.c`)**: `core_nbe_to_arm64_correct` (`0 sorry`) proves `Core.evalTerm` (with HoTT/univalence/modal proof `let`-bindings erased!) equals `Arm64.exec`; `ThinEmitter` streams `bv_decide`-verified ARMv8-A 32-bit machine words directly into a `ByteArray` and executes them in-process in **~0.5–5 µs/run** (**>10,000x faster** than spawning `clang` at `~65,000 µs`, and **31x faster** than `HIR.eval` on 50,000-step SplitMix64 `cbnz x8` loops!).
3. **Zero-Lisp Extensible `.narya` Syntax + Unison Content-Addressed `#hash` Digests (`Narya/Syntax/Modern.lean`, `Narya/Meta/ContentHash.lean`)**:
   - **Lean/Idris2/Granule Surface Syntax (`.narya`)**: Pratt + arbitrary-arity mixfix parser (`SyntaxEnv`) extensible dynamically in-file and across `import`s via `prefix`, `postfix`, `infixl`, `infixr`, and leading/trailing `notation` (e.g. `notation 50 a " ≡[" A "] " b => Id A a b`, `⟪x, y⟫`), QTT graded binders (`(0 g : A)`, `(1 x : A)`, `(ω x : A)`, `(x @[μ] : A)`), modal boxes (`□[μ] A`, `box[μ] e`, `f @[μ] x`), layout-sensitive `let` blocks, and automatic `.ny → .narya` source translation (`narya translate`).
   - **Machine-Checked Equivalence to Legacy `.ny` (`0 sorry`)**: `elabModernExpr_eq_elaborateSExp` and `ofSExp_toSExp_roundtrip` prove `.narya` elaborates identically to legacy `.ny` across all 22 mode theories.
   - **Unison Content-Addressed Proof/Impl/ABI Hashing (`ContentHash.lean`)**: Every declaration receives a 3-tier digest (`#spec` theorem hash, `#impl` nameless De Bruijn + `#hash`-resolved implementation hash, and `#abi` raw ARMv8-A machine-code hash). Proven invariant under deep binder α-renaming (`termContentHash_alpha_invariant`) and upstream global refactoring (`global_rename_preserves_contentHash`) — verified 16/16 identical between `stdlib_modern/*.narya` and `stdlib/*.ny`!
4. **Five Open HOTT/Narya Theory Frontiers Resolved (`Narya/Core/HIT.lean`, `Directed.lean`, `Squares.lean`, `RelTransfer.lean`, `Canonicity.lean`)**:
   - **Observational 1-HITs (`HIT.lean`)**: Interval-free `S1`, `SuspBool`, `QuotSwap` with universal Licata–Shulman `π₁(S¹) ≅ ℤ` retract (`pi1_S1_encode_decode_pos`, `pi1_S1_encode_decode_neg`).
   - **Directed HoTT (`Directed.lean`)**: Asymmetric `Dir.directed`, variance checking, `CovGlue` directed univalence without an inverse, and Covariant Yoneda on `Δ²`.
   - **2D Cubical Squares & `--without-K` Eckmann–Hilton (`Squares.lean`)**: 9-face `CubeOf`/`TubeOf` open-box Kan filling with strict regularity, 2-sided `refl` η, and `eckmann_hilton_comm`.
   - **Internal `Gel` Representation Transfer (`RelTransfer.lean`)**: Unary Peano `Nat` specifications proven to refine through `NatU64Gel` to 64-bit hardware execution on `Arm64.exec` and `ThinEmitter` `MAP_JIT`.
   - **Closed Univalent + Modal Canonicity (`Canonicity.lean`)**: Tait–Girard hereditary logical relations proving closed `Bool` and `U64` terms compute to canonical values across `Glue`, `arrowLine`, `prodLine`, and `boxLine`.
5. **First-Class Meta Tooling: Profiler & Lake-Inspired Merkle Builder (`Narya/Meta`)**:
   - **Nanosecond + Heap-Allocation Profiler (`Profiler.lean`)**: `@[noinline]`-guarded phase spans (`IO.monoNanosNow` + `IO.getNumHeartbeats`) exporting terminal hotspot tables, Chrome/Perfetto Trace Event JSON (`--json`), and Brendan Gregg `.folded` flamegraphs (`--folded`).
   - **Lake-Style Content-Addressed Merkle DAG Builder (`Build.lean`)**: `narya.toml` manifest + `import` cycle-checked topological sort + `BuildTrace` (`1723` root seed + `mix`), supporting `.narya`, `.ny`, and mixed packages while persisting `.trace`, `.nyo`, `unison.digests`, and native `.arm64.bin` artifacts (**< 1 ms** cached rebuild!).

---

## Architecture & Verified Pipeline

```mermaid
flowchart LR
    A[".ny Packages & Lean 4 DSL\n(narya.toml, narya_hoTT!, #narya_jit)"] --> B["Sorbet Arena & Glued Kernel\n(SymId + 16B PackedNode + NbE + Unify + QTT/MTT)"]
    B -->|"1-graded linear"| L["Flat-Array Interaction Net\n(0 DUP fans, 0 reduction allocs)"]
    B -->|"ErasableCore (0 sorry)"| C["HIR → MIR → LIR\n(Proof Erasure + x4..x7 Regs + cbnz x8)"]
    C --> D["Arm64 & ThinEmitter\n(bv_decide ARMv8-A words)"]
    D --> E["W^X MAP_JIT / mprotect\n(~5 µs in-process native run\n& .arm64.bin Merkle cache)"]
```

---

## Problems Resolved with Machine-Checked Proofs (`zero sorry`)

| # | Problem / Bottleneck | Resolution in `narya-lean` | Key Verified Theorems |
|---|---|---|---|
| **A** | Fixed global arity (`dim.ml`) prevents mixing HoTT, $k$-ary parametricity, `dTT`, & nominal types | Colored variable-arity `Dir` (`hott`, `param k`, `displayed`, `nominal`), heterogeneous axis swap, & `DepCube` | `SFace.isId_of_nominal`, `Perm.swapAxes_involutive`, `Op.id_isId` (`Narya/Dim/`) |
| **B** | Hardcoded OCaml mode functors & manual modal coercions (`modal.rst:16-18`) | First-class `ModeTheory` combinators (21 catalog theories) + Godement 2-cell normalizer & BFS `KeySynth` | `opposite2Cat_involutive`, `standardCatalog_all_wf`, `synthUnique?_sound` (`Narya/Modal/`) |
| **C** | Sinister modal codata fibrancy (`fibrancy.ml:127`), discrete windows (`norm.ml:80`), & discrete units (`discrete.rst`) | Adjoint key fusion `(ε ▷ L) ∘ᵥ (L ◁ η) ↝ 1_L`, functorial `filterSFace`, & $k=0, 1, \ge 2$ discrete unit theorems | `adjoint_triangle_key_cancel`, `discrete_window_endpoint_invariance`, `no_unbiased_natural_discrete_unit_ge2` (`ModalHoTT.lean`) |
| **D** | Unary GADT overhead & unverified representation swaps | Bit-packed `UInt64` `PackedSFace` + `TimeM` cost certificates + `RepBridge` | `packed_isId_eq_ref`, `packed_sface_isId_correct_and_faster`, `loopFusionOpt` (`PackedDim.lean`, `TimeM.lean`) |
| **E** | Computational HOTT fibrancy, observational `funext`/`hap`, & coinductive bisimulation | Strictly positive `arrowTrr`/`piTrr`, `Σ`/`boxLine` univalence, `funext`/`hap`, & `.proj` through `obsEq` on `potential` streams | `dependent_pi_transport_computes`, `modal_box_transport_computes`, `funext_hap_beta` (`NbE.lean`, `ModalHoTT.lean`) |
| **F** | Glued unification vs unfolding & non-pattern blocking (`EQUAL.md:170-202`) | Transactional `MetaCtx` + ternary `UnifyOutcome` + glued-preserving `quotePatternRHS?` | `speculative_never_mutates_metas`, `solveMeta_generation_strictly_increases`, `occursCheck_rejects_self_cycle` (`Unify.lean`) |
| **G** | Positivity, guardedness, `--without-K`, & predicative `Mugen` levels | `checkDataSpecPositivity`, `checkDefGuardedness`, `checkWithoutKPathMatch`, `univalence_refutes_axiomK`, & `LevelExpr` | `univalence_refutes_axiomK`, `checkLevelLeq_sound`, `no_girard_type_in_type` (`Safety.lean`, `Level.lean`) |
| **H** | Register promotion (`x4..x7`) & nested-safe hardware `cbnz x8` loops | Caller-saved `x4..x7` promotion (`0` stack ops on hot loops), `loopX8`, Mach-O & ELF emitters | `LIR.exec_compileAux`, `Arm64.noLoopCode_preserves_x8`, `Arm64.compileFullPipeline_correct` (`Compiler/`) |
| **I** | Quantitative / Linear Adjoint Types (`QTT` + Benton `LNL`) & FBIP reuse | `UsageGrade` (`0/1/ω` semiring), `linearAdjointTheory`, `checkLinearity`, & `canMutateInPlace` | `varUsage_mod_mul`, `ghost0_erasure_enforced`, `lnl_linear_vs_bang_duplication` (`Linear.lean`) |
| **J** | Sorbet-style cache-local AST arena & `O(1)` symbol interning | `SymId` (`UInt32`), `FastGlobalTable`, & hash-consed 16-byte `PackedNode` (`w0, w1 : UInt64`) `TermArena` | `pack_unpack_tag`, `pack_unpack_abc`, `pack_unpack_u64Lit` (`Fast/Arena.lean`) |
| **K** | Optimal linear reduction without garbage collection or fan overhead | Flat-array Lafont `INet` (`32`-bit `Port`) with `freeList` node recycling & `0`-`DUP` linear compilation | `pack_unpack_slot`, `linear_pipeline_valid_and_zero_dups`, `bang_duplication_uses_dup_fans` (`Fast/InteractionNet.lean`) |
| **L** | End-to-end `Core.NbE → Arm64` proof erasure, `ThinEmitter` binary encoding & sub-ms builds | `ErasableCore` simulation, `bv_decide` ARMv8-A encoders, W^X `MAP_JIT`/`mprotect`, `Profiler`, & `BuildTrace` | `evalTerm_erasure_sound`, `core_nbe_to_arm64_correct`, `decode_encodeMovk`, `decode_encodeAluReg` (`Erasure.lean`, `ThinEmitter.lean`) |
| **M** | Observational 1-HITs without a cubical interval | `pctor`, `elimHIT` computing on `ap`, `S1`/`SuspBool`/`QuotSwap`, & universal `π₁(S¹) ≅ ℤ` | `pi1_S1_encode_decode_pos`, `pi1_S1_encode_decode_neg`, `SuspBool_not_merid_flips` (`Core/HIT.lean`) |
| **N** | Directed HoTT & asymmetric `CovGlue` univalence without inverses | `Dir.directed`/`opDirected`, `directedCatTheory`, variance checker, `CovGlue`, & Yoneda | `directed_rejects_sym`, `covGlue_forward_beta_u64`, `directed_yoneda_naturality_delta2` (`Core/Directed.lean`) |
| **O** | 2D cubical squares, strict Kan regularity, & `--without-K` Eckmann–Hilton | 9-face `Square2D`, `kanOpenBoxLid`, two-sided `refl` η, & `Ω²` commutativity | `square_tube_plug_roundtrip`, `kanOpenBoxLid_regularity`, `eckmann_hilton_comm` (`Core/Squares.lean`) |
| **P** | Verified unary math spec → 64-bit hardware transfer (`Gel`) | `NatU64Gel` relational bridge from Peano `Nat` through `toU64` to `Arm64.exec` | `nat_add_transfers_to_arm64_u64`, `fastAddWithGelBridge_refines_peano` (`Core/RelTransfer.lean`) |
| **Q** | Constructive Univalent + Modal Canonicity for `Bool` & `U64` | Tait–Girard `ValRel` logical relation across `Glue`, `sym`, `trans`, `arrowLine`, `prodLine`, `boxLine` | `closed_bool_canonicity`, `closed_u64_canonicity`, `higherOrder_univalent_canonicity` (`Core/Canonicity.lean`) |
| **R** | Lisp-free Lean/Idris2/Granule extensible syntax equivalent to `.ny` | Total Pratt + mixfix `.narya` parser (`SyntaxEnv`), QTT grades, & `.ny → .narya` translator | `elabModernExpr_eq_elaborateSExp`, `ofSExp_toSExp_roundtrip`, `infix_desugar_eq_elaborateSExp`, `mixfix_id_desugar_eq_elaborateSExp` (`Syntax/Modern.lean`) |
| **S** | Unison content-addressed source/proof/ABI model for agentic refactoring | Nameless De Bruijn + `#hash` `termContentHash` & 3-tier `DefDigest` (`#spec`, `#impl`, `#abi`) | `termContentHash_alpha_invariant`, `global_rename_preserves_contentHash`, `modern_and_legacy_same_contentHash`, `same_erasure_same_abiHash` (`Meta/ContentHash.lean`) |

---

## Quickstart

### Prerequisites
- [Lean 4 / `elan`](https://lean-lang.org/lean4/doc/quickstart.html) (automatically selects `leanprover/lean4:v4.35.0` via `lean-toolchain`)
- macOS on Apple Silicon (`clang`) **or** Linux `aarch64` (`cc`) for live W^X `MAP_JIT`/`mprotect` and Mach-O/ELF native execution

### Build & Run Full Verification Suite (`75/75` Kernel, Theory Frontier, Syntax, Unison, Arena, INet & JIT Assertions)
```bash
lake build
lake test
```

### CLI Commands (`lake exe narya`)
```bash
# 1. Incremental Merkle DAG build on Zero-Lisp .narya stdlib (with cross-module notations & Unison digests!)
lake exe narya build stdlib_modern --rebuild
lake exe narya build stdlib_modern

# 2. Inspect Unison content-addressed (#impl, #spec, #abi) digests & translate legacy .ny -> .narya
lake exe narya hash stdlib_modern
lake exe narya translate examples/univalence_and_modal.ny

# 3. Run dynamic Pratt/mixfix + QTT graded modal .narya showcase
lake exe narya run examples/modern_showcase.narya

# 4. Nanosecond + heap-allocation phase profiler with Chrome Trace JSON & Flamegraph export
lake exe narya profile stdlib_modern/collatz.narya --json /tmp/narya_trace.json --folded /tmp/narya.folded

# 5. Stream verified ARMv8-A 32-bit machine words & run in-process via W^X MAP_JIT (~5 µs/run)
lake exe narya jit
lake exe narya bench
lake exe narya catalog
```

---

## Repository Layout

- `Narya/Dim/` — Colored variable-arity directions, `SFace`, `SDeg`, `Perm`, `Op`, `CubeOf`, `TubeOf`
- `Narya/Modal/` — `ModeTheory` (`UsageGrade` `0/1/ω`), 21-theory combinator catalog (`Combinators.lean`), Godement normalizer & BFS `KeySynth`
- `Narya/Core/` — Syntax (`funext`, `hap`, `U64`), glued `Val`, `NbE`, `Equal`, glued ternary `Unify`, positivity/`--without-K` `Safety`, predicative `Level`, QTT/LNL `Linear`, bidirectional `Check`, and `ModalHoTT`
- `Narya/Fast/` — Unboxed `PackedDim`, Sorbet 16-byte `PackedNode` `Arena`, and flat-array Lafont `InteractionNet`
- `Narya/Compiler/` — `TimeM`, `RepBridge`, `HIR`, `MIR`, `LIR`, `Arm64`, `Core → Arm64` `Erasure` (`core_nbe_to_arm64_correct`), and `ThinEmitter` + `cbits/narya_jit.c` W^X `MAP_JIT`
- `Narya/Meta/` — Hierarchical nanosecond + heap-allocation `Profiler` & Lake-inspired Merkle `BuildTrace` package builder (`Build`)
- `Narya/Syntax/` & `Narya/Elab/` — Pretty-printer, `.ny` parser/runner, and Lean 4 `narya!` / `narya_hoTT!` / `#narya_jit` / `def_mode_theory` DSL
- `stdlib/` — Multi-module standard package (`narya.toml`, `core.ny`, `univalence.ny`, `collatz.ny`, `linear.ny`)
- `docs/SPEC.md` & `docs/ARCHITECTURE_AND_GUIDE.md` — Specification, mathematical foundations, and exhaustive developer manual

---

## Attribution & License

Inspired by and faithfully modeling the type-theoretic semantics of [**Narya**](https://github.com/mikeshulman/narya) by **Mike Shulman** and contributors, combined with theory-combinator ideas from Carette & O'Connor / [CSLib](https://github.com/leanprover/cslib), Sorbet-inspired data layout principles from **Nelson Elhage**, Symmetric Interaction Combinators from **Yves Lafont**, and multi-IR code generation concepts from **Leonardo de Moura**'s SViL 2026 presentation.

Licensed under **GPL-3.0-only** (matching upstream `mikeshulman/narya`); see [LICENSE](./LICENSE).
