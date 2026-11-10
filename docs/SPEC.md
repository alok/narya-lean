# `narya-lean` — Technical Specification & Research Blueprint

## 1. Mission & Thesis ("A Perfectible Higher-Dimensional Language")

Plain intensional dependent type theory (such as MLTT) makes a programming language *perfectible* in the sense of [alok.blog ("A perfectable programming language")](https://alok.blog): programs, specifications, metaprograms, and equivalence proofs inhabit one language. Yet plain MLTT treats **isomorphic representations as unequal**: replacing a linked unary representation with a packed 64-bit word, an AoS buffer with SoA, or a naive specification with a register-allocated loop requires manual transport across APIs instead of computational observational equality.

**Narya** (Mike Shulman) attacks this at the type-theoretic root by combining:
1. **Observational Higher Dimensions** (`Id` / `Br`, `refl` / `rel`, `ap`, `sym`, `Gel`, `glue`) where equality and parametricity compute structurally on types (`Π`, `Σ`/records, `data`, `codata` bisimulations).
2. **Multi-Modal & Adjoint Type Theory (MTT / MATT)** parameterized by a 2-category of modes, modalities (`1-cells`), and natural transformation keys (`2-cells`, `t #α`), unifying cohesive (`♭ ⊣ ♯`, `ʃ ⊣ ♭`), guarded (`▹`), crisp (`△ ⊣ □`), and displayed (`-dtt`) type theories.

**`narya-lean`** re-implements and extends Narya **in Lean 4**, uniting four pillars:
1. **Clean Reference Semantics (`Narya.Dim`, `Narya.Modal`, `Narya.Core`)**: Faithful Lean 4 port and generalization of Narya's OCaml architecture (`lib/dim`, `lib/modal`, `lib/core`, `lib/hott`) serving as the readable mathematical oracle.
2. **Machine-Checked Resolution of 4 Open Problems in Narya**:
   - **Problem A — Multi-Directional Variable-Arity Dimension Category (`Narya.Dim.*`)**: OCaml Narya supports only a single active dimension direction (`observational.rst:4`, `lib/dim/README.md:5`). We construct the colored symmetric semicartesian cube category $\square_\Sigma$ supporting **simultaneous** HoTT paths (`e`, arity 2, fibrant), variable-arity parametricity (`p`, arity $k$), unary simplicial display (`d`, arity 1), and nominal weakening (`w`, arity 0), proving categorical laws, residual factorization (`deg ∘ sface = sface' ∘ deg'`), and cross-direction interchange (`sym_{d₁,d₂}`).
   - **Problem B — First-Class Mode Theory Combinators & Verified 2-Cell Key Synthesis (`Narya.Modal.*`)**: OCaml Narya hardcodes each mode theory in OCaml (`modal.rst:16–18`). Drawing on Carette–O'Connor theory presentation combinators and CSLib, we build algebraic 2-categorical combinators (`trivial`, `arrow`, `twoCell`, `adjunction`, `coproduct`, `composeHoriz`, `amalgamate`, `opposite2Cat`, `retractSubmode`, `discretize`) with a verified 2-cell normalizer and unique key synthesizer, deriving Narya's standard mode theories compositionally and exposing user-definable `mode_theory` declarations via Lean 4 metaprogramming.
   - **Problem C — Modal Higher Observational Type Theory ("Modal HoTT", `Narya.Core.ModalHoTT`)**: Resolves two explicit `Unimplemented`/`MODALTODO` gaps in upstream Narya (`fibrancy.ml:127` and `norm.ml:80`) plus the higher-arity discrete-unit question (`discrete.rst:70–101`):
     1. *Adjoint Modal Fibrancy Theorem*: Derives transport (`trr`, `trl`) and path-lifting (`liftr`, `liftl`) on negative modal records/codatatypes `(x : L | _) .fld : A` along any sinister adjunction $L \dashv R$ via unit-keyed projection and counit-keyed conversion, proving coherence from the triangle identities $(\varepsilon L) \circ (L \eta) = 1_L$ and $(R \varepsilon) \circ (\eta R) = 1_R$.
     2. *Discrete Window Higher-Match Factorization*: Proves soundness of higher-dimensional pattern matching behind a discrete window modality via dimension-filter diagonalization.
     3. *Multi-Arity Biased Discrete Units*: Proves the impossibility of unbiased natural transformations $1 \Rightarrow \mu$ into discrete $\mu$ for arity $k \ge 2$, proves uniqueness at $k = 1$, and introduces endpoint-biased 2-cells $\eta_i$ ($0 \le i < k$) that consistently generalize `-discrete-tconn` to arbitrary arity.
   - **Problem D — Retention & Unary Dimension Bottlenecks (`Narya.Fast.*`)**: Replaces heap-allocated unary GADT faces/degeneracies with unboxed `UInt64` bit-packed cubical operators (`PackedSFace`, `PackedSDeg`) and proves a zero-`sorry` refinement isomorphism (`decode (compPacked f g) = comp (decode f) (decode g)`), alongside glued evaluation (`GluedNeu`), spine-first η-conversion (`EQUAL.md`), and identity-action short-circuiting (`PROFILING.md`).
3. **Lean 4 Metaprogramming & Familiar Syntax (`Narya.Elab.*`, `Narya.Syntax.*`)**:
   - Familiar Lean-style DSL (`mode_theory`, `narya_def`, `#narya_check`, `#narya_eval`, `#narya_asm`) with custom syntax categories, hover-friendly elaboration, and `.ny` parser support.
4. **Verified Optimization via Theory/Cost Combinators & Multi-IR Native ARM64 Codegen (`Narya.Compiler.*`)**:
   - Inspired by **CSLib's `TimeM`** and **Leonardo de Moura's Nov 2026 SViL "New Code Generator" architecture** (`Lean/Narya → HIR → MIR → LIR → Native Assembly`):
     - Uses **Modal Guarded Parametricity** to separate the *extensional/univalent specification mode* (where `Gel`/`glue` bridges equate high-level specs with packed machine representations) from the *discrete/intensional machine mode* (where `TimeM` proves strict step/cycle reductions `fast.time < spec.time`).
     - Defines formal operational semantics for **HIR** (functional core after modal/dimension erasure), **MIR** (join points + Perceus/Lean uniqueness `reset`/`reuse` stack/in-place annotations), **LIR** (register/stack machine), and **ARM64 (`AArch64`)** instructions.
     - Proves end-to-end semantic preservation (`zero sorry`) across optimization and lowering passes, emits real macOS Apple Silicon (`arm64-apple-darwin`) assembly, assembles via `clang`, and verifies native binary execution in `lake test`.

---

## 2. Module Map & Contracts

| Layer | Module | Responsibility | Key Theorems / Checks |
|---|---|---|---|
| **1. Dim** | `Narya.Dim.Direction` | Multi-directional signatures (`hott`, `param k`, `displayed`, `nominal`, custom) | Decidable equality, endpoint arity bounds |
| | `Narya.Dim.Word` | Colored dimension contexts `DimCtx`, insertions, shuffles | Associativity, length & membership invariants |
| | `Narya.Dim.SFace` | Colored strict faces (`zero`, `endpt`, `mid`), residuals | `id_comp`, `comp_id`, `comp_assoc` |
| | `Narya.Dim.SDeg` | Colored strict degeneracies (`zero`, `deg`, `keep`) | `id_comp`, `comp_id`, `comp_assoc`, section existence |
| | `Narya.Dim.Perm` | Color-preserving permutations & cross-direction interchange | Identity, composition, inverse, interchange involution |
| | `Narya.Dim.Op` | Cubical operators (`SDeg × Perm × SFace`) & distributive law | Residual factorization (`degSFace`) soundness |
| | `Narya.Dim.Cube` | `CubeOf` and boundary `TubeOf` indexed by strict faces | Functoriality (`map_id`, `map_comp`), `actCube` identity law |
| **2. Modal** | `Narya.Modal.ModeTheory` | 2-categories of modes, quiver modalities, 2-cell keys, dimension filters | Well-formedness, filter functoriality |
| | `Narya.Modal.Combinators` | Theory combinators (`arrow`, `adjunction`, `amalgamate`, `opposite`, `discretize`, ...) + 19 Narya mode theories | Arity-discreteness compatibility theorem |
| | `Narya.Modal.KeySynth` | 2-cell key synthesis & adjunction triangle normalizer | Soundness of synthesized 2-cells & triangle reduction |
| **3. Core** | `Narya.Core.Syntax` | Scoped Narya AST (`Kinetic`/`Potential`, modal `Π`/`Σ`/`Data`/`Codata`, `Gel`, `glue`, higher fields) | Scoping & mode-locking invariants |
| | `Narya.Core.Value` | Glued NbE semantic values, neutral spines, cube environments | `act_id` short-circuit law |
| | `Narya.Core.NbE` | Glued evaluation, case-tree/comatch execution, observational `Id`/`Br`/`Gel`/`glue`/`trr`, readback | Normalization & β/ι/observational computation tests |
| | `Narya.Core.Equal` | 3-tier conversion checker (pointer/structural fast-path → spine-first → η + local glued unfold) | Reflexivity & spine-first soundness |
| | `Narya.Core.Check` | Bidirectional modal + higher-dimensional typechecker | Typechecks parametricity, HoTT, dTT (`SST`), cohesive examples |
| | `Narya.Core.ModalHoTT` | Formal resolution of Modal HoTT transport, discrete windows, & biased discrete units | `adjoint_modal_trr_coh`, `discrete_window_factor`, `no_unbiased_discrete_unit_ge2`, `biased_unit_coherent` |
| **4. Syntax** | `Narya.Elab.DSL` | Lean 4 metaprogramming DSL (`mode_theory`, `narya!`, `#narya_check`, `#narya_eval`, `#narya_asm`) | Compile-time elaboration tests |
| | `Narya.Syntax.Parser` | Standalone surface parser & pretty-printer for CLI `.ny` / `.narya` snippets | Roundtrip & CLI execution tests |
| **5. Fast & Compiler** | `Narya.Fast.PackedDim` | Unboxed `UInt64` bit-packed strict faces & degeneracies | Isomorphism & homomorphism proofs vs `Narya.Dim.SFace`/`SDeg` |
| | `Narya.Compiler.TimeM` | CSLib-style `TimeM` cost monad + modal representation-bridge optimization framework | Verified representation swap (`Unary ↔ Packed`, `Slow ↔ Fast`) with strict cost bound |
| | `Narya.Compiler.HIR` | High-level IR (modal/bridge/proof erasure) + verified optimizer (const-fold, algebraic, DCE) | `evalHIR_opt_eq` (`zero sorry`) |
| | `Narya.Compiler.MIR` | Mid-level IR (join points + Perceus `reset`/`reuse` uniqueness analysis) | `evalMIR_lower_eq` (`zero sorry`) |
| | `Narya.Compiler.LIR` | Low-level register/slot machine IR with `TimeM` instruction costs | `evalLIR_lower_eq` (`zero sorry`) |
| | `Narya.Compiler.Arm64` | Native Apple Silicon `AArch64` assembly emitter + formal register machine | `runArm64_emit_eq` (`zero sorry`) + live `clang` Mach-O execution test |

---

## 3. Done Criteria
1. `lake build` succeeds with **0 errors, 0 warnings, and 0 `sorry`s** across the entire codebase.
2. `lake test` passes 100% of unit, property, typechecking, open-problem theorem, and live `clang` ARM64 native binary execution tests.
3. `lake exe narya` runs standalone checks, evaluations, mode theory inspections, and native ARM64 compilation.
4. Public GitHub repository `alok/narya-lean` pushed with atomic commit history, GitHub Actions CI, `README.md`, and `docs/ARCHITECTURE_AND_GUIDE.md`.
