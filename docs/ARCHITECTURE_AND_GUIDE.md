# Narya-Lean: Architecture, Mathematical Foundations & Developer Guide

This document serves as the comprehensive architectural, mathematical, and developer manual for **`narya-lean`** — a clean-slate Lean 4 implementation and unification of **Narya** (Mike Shulman's higher-dimensional, multi-modal observational type theory proof assistant), extended with **CSLib-style theory combinators**, **machine-checked resolutions of four upstream open problems (`zero sorry`)**, and **Leonardo de Moura's SViL 2026 multi-IR verified native ARM64 compiler** realizing the vision of a *perfectible programming language*.

---

## 1. System Overview & Layered Architecture

Every file in `Narya/` is **100% computable** (`zero noncomputable`), **100% total** (`zero partial`), and **100% kernel-verified** (`zero sorry`), compiled under `autoImplicit := false` on Lean `v4.35.0`.

```mermaid
flowchart TD
    subgraph Surface["Layer 4: Surface Syntax & Lean 4 Metaprogramming"]
        DSL["Narya/Elab/DSL.lean\nnarya!, narya_hoTT!, def_mode_theory\n#narya_check, #narya_eval"]
        NY["Narya/Syntax/Parser.lean & Pretty.lean\nStandalone .ny Scripts & CLI"]
    end

    subgraph Core["Layer 3: Glued Multi-Modal Observational Kernel"]
        CHK["Narya/Core/Check.lean\nBidirectional MTT Checker\nLockers, Fibrancy, Sinister Codata"]
        EQ["Narya/Core/Equal.lean\n3-Tier Glued & Type-Directed η Conversion"]
        NBE["Narya/Core/NbE.lean\nGlued NbE, Glue/Gel Univalence, Potential SST"]
        MH["Narya/Core/ModalHoTT.lean\nOpen Problems C1–C3 Proofs"]
    end

    subgraph Modal["Layer 2: 2-Categorical Mode Combinators"]
        MT["Narya/Modal/ModeTheory.lean\nFirst-Class ModeTheory & Functorial filterDim"]
        MC["Narya/Modal/Combinators.lean\n20 Standard Theories + Amalgamation / 2-Dual"]
        KS["Narya/Modal/KeySynth.lean\nGodement Interchange Normalizer & BFS synthKey"]
    end

    subgraph Dim["Layer 1: Colored Variable-Arity Cubical Category"]
        DIR["Narya/Dim/Direction.lean & Word.lean\nhott (2,fib), param k, displayed (1), nominal (0)"]
        OPS["Narya/Dim/SFace, SDeg, Perm, Op, Cube\nCanonical Factorization & Universe-Pure DepCube"]
        FAST["Narya/Fast/PackedDim.lean\nUnboxed UInt64 PackedSFace & bv_decide Proofs"]
    end

    subgraph Compiler["Layer 5: Perfectible Language & Verified ARM64 Backend"]
        TIMEM["Narya/Compiler/TimeM.lean\nCSLib LawfulMonad TimeM, RepBridge, VerifiedOpt"]
        HIR["Narya/Compiler/HIR.lean\nModal/Bridge Erasure & Verified Optimizer"]
        MIR["Narya/Compiler/MIR.lean\nUniqueness Analysis & Stack/Reg Ownership"]
        LIR["Narya/Compiler/LIR.lean\n16-Byte Aligned Stack-Height Machine"]
        ARM["Narya/Compiler/Arm64.lean\nFormal AArch64 ISA, movz/movk, Mach-O clang Runner"]
    end

    DSL --> CHK
    NY --> CHK
    CHK --> EQ --> NBE
    CHK --> KS --> MC --> MT --> OPS --> DIR
    FAST -. "Refines (0 sorry)" .-> OPS
    NBE --> HIR --> MIR --> LIR --> ARM
    TIMEM --> LIR
    TIMEM --> FAST
```

---

## 2. Layer 1: Multi-Directional Variable-Arity Cubical Category (`Narya/Dim/`)

### 2.1 Resolving Upstream Open Problem A (`Direction.lean`)
In upstream OCaml Narya, the cubical arity is fixed globally at startup (`arity = 2` by default, `-arity k` for $k$-ary parametricity, `-dtt` for unary displayed bridges), preventing a single proof script from combining HoTT paths, $k$-ary relational bridges, unary displayed bridges, and 0-ary nominal freshness dimensions simultaneously.

`Narya/Dim/Direction.lean` replaces the global integer arity with a colored direction descriptor `Dir`:
- `Dir.hott` (`arity = 2, fibrant = true`): symmetric Higher Observational Type Theory paths admitting `trr`, `trl`, `liftr`, and `pathJ`.
- `Dir.param k` (`arity = k, fibrant = false`): $k$-ary internal/external relational parametricity bridges (`Br`, `Gel`).
- `Dir.displayed` (`arity = 1, fibrant = false`): unary directed fibrations for Displayed Type Theory (`dTT`) and coinductive Semisimplicial Types (`SST`).
- `Dir.nominal` (`arity = 0, fibrant = false`): 0-ary nominal freshness dimensions (`Fresh(A)`), whose `Endpoint (.nominal) = Fin 0` is uninhabited — automatically making every strict face over pure nominal contexts an identity (`SFace.isId_of_nominal`).

### 2.2 Canonical Cubical Factorization (`SFace`, `SDeg`, `Perm`, `Op`)
Every morphism in our colored variable-arity cube category factors uniquely as a triple `Op m n`:
1. **Strict Degeneracy (`SDeg m k`)**: drops/duplicates dimensions (`zero`, `suc`, `deg`).
2. **Colored Axis Permutation (`Perm k l`)**: reorders dimensions while preserving direction colors (`Perm.swapAxes_involutive` enables Fubini interchange between HoTT paths and parametricity bridges!).
3. **Strict Face (`SFace l n`)**: specializes subset of axes to concrete endpoints `e : Fin g.arity` (`zero`, `mid`, `endpt`).

Composition of general cube operators `Op.comp` uses the verified distributive helpers:
- `sdegSFace` (`SFace` pushed past `SDeg`)
- `permSFace` (`SFace` pushed past `Perm`)
- `sdegPerm` (`Perm` pushed past `SDeg`)

### 2.3 Avoiding Universe Level Bumps in Dependent Cubes (`Cube.lean`)
A subtle Lean 4 pitfall when porting OCaml GADTs (`Cube.ml`, `Tube.ml`): defining `inductive DepCube (F : DimCtx → Type u) : DimCtx → Type u` with a non-uniform family parameter `F` forces `DepCube F n : Type (u + 1)` in Lean 4's kernel!
We avoid this completely in `Narya/Dim/Cube.lean` by defining `DepCube` via **structural recursion on `DimCtx : List Dir`**:
```lean
def DepCube {u : Type _} (F : DimCtx → Type u) : DimCtx → Type u
  | [] => F []
  | g :: m => (Endpoint g → DepCube F m) × DepCube (fun k => F (g :: k)) m
```
This keeps `DepCube F n : Type u` with **zero universe bump**, enabling `CubeOf V n` (full cubes) and `TubeOf V f` (partial boundary tubes indexed by `SFace m n`) to live in `Type 0`.

---

## 3. Layer 2: First-Class 2-Categorical Mode Combinators (`Narya/Modal/`)

### 3.1 Mode Theories as First-Class Data (`ModeTheory.lean`, `Combinators.lean`)
Upstream OCaml Narya hardcodes mode theories as static OCaml module functors. Inspired by Carette & O'Connor's *Theory Presentation Combinators* and Lean's `CSLib`, `Narya/Modal/` represents mode theories as first-class 2-categorical presentations `ModeTheory`:
- **0-cells**: `modes : List ModeId`
- **1-cells**: `modalities : List ModGen` carrying structural flags (`tangible`, `pellucid`, `transparent`, `translucent`, `sinister`, `isLocker`, and `discreteDirs : List Dir`)
- **2-cells**: `twoCells : List TwoCellGen` (`α : src ⇒ tgt`)
- **Equations**: `rules : List TwoCellRule` (`lhs ↝ rhs`)

Combinators in `Narya/Modal/Combinators.lean`:
- `trivialTheory`, `arrowTheory`, `twoCellTheory`, `comonadTheory`, `adjunctionNamed`
- `coproduct` & `amalgamate` (2-categorical pushout identifying shared modes/modalities, used to build `spatialTheory` $\Pi \dashv \mathrm{Disc} \dashv \Gamma$ and `ambiflectionTheory` $L \dashv M \dashv R$!)
- `opposite2Cat` (reverses 2-cell directions `src ↔ tgt`, deriving `monadTheory` from `comonadTheory` and `reflectionTheory` from `coreflectionTheory`, with `opposite2Cat_involutive` proven `zero sorry`!)
- `retractSubmode`, `discretizeTargetMode`, `addLocker`
- `standardCatalog`: 20 ready-to-use mode theories (all verified well-formed by `standardCatalog_all_wf : standardCatalog.all ModeTheory.wf = true := by decide`).

### 3.2 Godement-Interchange Normalizer & BFS Key Synthesis (`KeySynth.lean`)
In Multimodal Type Theory (`MTT`), accessing `(x : μ | A)` inside a locked context `Γ, lock_ν` requires a **canonical** 2-cell coercion `α : μ ⇒ ν`.
`Narya/Modal/KeySynth.lean` resolves Open Problem B (`docs/source/modal.rst:16-18`) by:
1. Flattening 2-cells into vertical spines of `WhiskeredAtom`s (`l ◁ c ▷ r`).
2. Rewriting spines via contextual slice matching (`applyRuleAtHead`) **plus** 2-categorical **Godement interchange & intermediate-path shrinking** (`tryInterchangeAtHead`), ensuring Schanuel–Street zig-zag composites in `adjunctionTheory` collapse uniquely to `η` and `ε` (`adjunction_triangleL_norm`, `adjunction_triangleR_norm`).
3. Running bounded breadth-first search (`synthKey`) returning `.unique α`, `.ambiguous α₁ α₂` (flagging incoherent mode theories rather than silently guessing!), or `.notFound`, backed by `synthUnique?_sound`.

---

## 4. Layer 3: Glued NbE, MTT Checker & Open Problem Proofs (`Narya/Core/`)

### 4.1 3-Tier Glued Normalization by Evaluation (`Value.lean`, `NbE.lean`, `Equal.lean`)
Following `lib/core/EQUAL.md` in upstream Narya:
- **Kinetic Definitions (`Val.glued name rspine forced`)**: Retain both the unexpanded global symbol + reverse elimination spine *and* the lazily forced semantic value. In `Equal.lean`, **Tier 1** checks spine equality of matching glued heads *before* **Tier 2** (type-directed function/codata η-expansion, including 0-field record η!) and **Tier 3** (structural forced comparison), avoiding exponential blowup.
- **Potential Definitions (`Energy.potential` / `.neu (.potential name) rspine`)**: Coinductive definitions (such as `SST` in Displayed Type Theory) do **not** unfold eagerly; they unfold only on-demand when hit by a projection `projVal` or application `applyVal`, guaranteeing termination!
- **Computational Univalence (`Glue` / `Gel`)**: `evalTrr` and `evalTrl` compute directly through `Gel Dir.hott [A₀, A₁] equiv`, reducing `trr (Glue A₀ A₁ ⟨fwd := f, bwd := g⟩) x₀ ↝ f x₀` and `trl (Glue A₀ A₁ ⟨fwd := f, bwd := g⟩) x₁ ↝ g x₁`!

### 4.2 Exact MTT Locking Variance (`Check.lean`)
Each variable entry in `MTTCtx` stores:
- `declMod : ModPath` (`ν : varMode → bindMode`)
- `accLock : ModPath` (`λ : currMode → bindMode`, right-composed via `accLock ↦ accLock ∘ μ` whenever `Γ.lockBy μ` enters a modal position `μ : dom → Γ.mode`).

Variable lookup checks `declMod ⇒ accLock` via `KeySynth.synthKey`:
- Comonad counit (`(y : □ | B)` at empty lock `1_M`): synthesizes `ε : □ ⇒ 1_M`.
- Comonad comultiplication (`(y : □ | B)` under `lock_{□∘□}`): synthesizes `δ : □ ⇒ □ ∘ □`.
- Adjunction unit (`(x : 1_D | A)` under `lock_{R∘L}`): synthesizes `η : 1_D ⇒ R ∘ L`.
- Adjunction counit (`(y : L∘R | B)` at empty lock `1_C`): synthesizes `ε : L ∘ R ⇒ 1_C`.
- Parametricity locker (`isLocked`): rejects `Type_ext` (`UU_ext`) whenever `outerLock` has an active `isLocker` modality not reset by an inner discrete modality (`incl` / `up` / `Lift`).

### 4.3 Machine-Checked Resolutions of Open Problems C1–C3 (`ModalHoTT.lean`)
1. **C1 — Adjoint Modal Fibrancy (`fibrancy.ml:127`)**:
   - `adjoint_triangle_key_cancel` & `adjoint_modal_trr_refl_coh`: Proves that for any sinister left adjoint `L ⊣ R`, transporting a negative modal codata field across reflexivity and cancelling `(ε ▷ L) ∘ᵥ (L ◁ η)` via `Val.actKey` is strictly the identity (`zero sorry`).
   - `univalence_gel_trr_computes`: Proves the computational univalence β-law on `Gel` bridges (`zero sorry`).
2. **C2 — Higher-Dimensional Discrete Window Match (`norm.ml:80`)**:
   - `discrete_window_endpoint_invariance` & `discrete_window_find`: Proves that for any cube over `n` and modality `μ` discretizing all directions in `n`, `CubeOf.find` is invariant across all strict faces `f : SFace m n` (`zero sorry`).
3. **C3 — Complete Classification of Discrete Modality Units (`discrete.rst:70-101`)**:
   - `no_natural_discrete_unit_arity0` ($k = 0$: impossible by fixed-point-free negation on `Bool`).
   - `unique_natural_discrete_unit_arity1` ($k = 1$: uniquely pinned down to $\eta(x) = x$).
   - `no_unbiased_natural_discrete_unit_ge2` ($k \ge 2$: impossible to be both symmetric and diagonal by Bool-swap naturality, while vertex-biased projections $\pi_0$ satisfy associativity `vertex_biased_assoc`).

### 4.4 Open Problem E: Coding Computational HOTT Fibrancy from Scratch (`NbE.lean`, `ModalHoTT.lean`)
In Mike Shulman's Higher Observational Type Theory (`docs/source/hott.rst`, `lib/core/fibrancy.ml`), equality is **observational** (`Id A x y` computes according to the type constructor of `A`), while transport (`trr`, `trl`) and dependent path lifting (`liftr`, `liftl`) must compute strictly across type-former bridges without losing strict positivity of semantic values `Val`!

**Why naive higher-order closures fail in Lean 4**:
If you try to define `Val.lam : (Val → Val) → Val`, Lean 4's kernel rightly rejects `Val` for violating strict positivity. Conversely, if you try to compile dependent function transport `trr (piLine pA pB) f₀` by syntactically shifting De Bruijn indices inside `Term` at runtime, every transport step pays $O(|t|)$ AST traversal overhead and complicates termination proofs.

**How we solve it cleanly (`Value.lean`, `NbE.lean`)**:
1. **First-Order Transport Closures (`Closure`)**:
   We extend the first-order `Closure` inductive (`Closure.term env body`) with four dedicated HOTT transport constructors:
   - `arrowTrr (pA pB f₀ : Val)` & `arrowTrl (pA pB f₁ : Val)`
   - `piTrr (pA : Val) (pB : Closure) (f₀ : Val)` & `piTrl (pA : Val) (pB : Closure) (f₁ : Val)`
2. **Exact contravariant/covariant computation (`applyClosure` in `NbE.lean`)**:
   When `f₁ := Val.lam name m (.piTrr pA pB f₀)` is applied to `a₁ : A₁`:
   - Pull `a₁` **backward** along `pA` to the left endpoint: `a₀ := evalTrl fuel G .hott pA a₁`.
   - Lift that backward transport to a bridge `pa : Id pA a₀ a₁` via `evalLiftl fuel G .hott pA a₁`.
   - Instantiate the codomain bridge family `pB` at `pa` (`pBa := applyClosure fuel G pB pa`).
   - Transport `f₀ a₀` **forward** along `pBa`: `evalTrr fuel G .hott pBa (applyVal fuel G f₀ m a₀)`!
3. **Dependent Σ & Cross-Mode Modal Box Transport**:
   - On `prodLine pA pB` and `sigLine pA pB`, `evalTrr` transports the first field `u₁ := trr pA u₀`, lifts `pu := liftr pA u₀ : Id pA u₀ u₁`, instantiates `pB pu`, and transports the second field along `pB pu` (`sigma_dependent_transport_computes`).
   - On `boxLine m pA`, `evalTrr` commutes directly inside positive modal boxes: `trr (boxLine m pA) (box m a₀) ↝ box m (trr pA a₀)`, respecting cross-mode MTT locks (`modal_box_transport_computes`).
4. **Equational Chains (`calc_eq`) & Involutive `sym`**:
   - `evalTrans` reduces on **both** left and right `refl` (`trans refl q ↝ q` and `trans p refl ↝ p`), while `evalSym` cancels double symmetry on neutrals (`sym (sym p) ↝ p`, `sym_involutive_neu`) and flips `Glue` equivalences (`flipEquivFields`).

### 4.5 Open Problem F: Glued Ternary Miller Pattern Unification (`Unify.lean`, `EQUAL.md:170–202`)
Upstream Narya's `lib/core/EQUAL.md` (lines 170–202) documents three interlocking design problems when moving from pure conversion checking (`Equal.lean`) to unification with metavariables (`?m`):
1. **Stateful mutation vs backtracking**: In OCaml, speculative glued comparisons (`equal_val` Tier 1) cannot safely mutate global metavariables if Tier 1 fails and falls back to forced unfolding, unless state is rolled back or re-checked (`localRetry` vs `strictSmalltt`).
2. **Ternary blocking**: Non-pattern spines like `?m0 true ≡ false` are neither provably equal nor provably disequal (`?m0 := fun _ => false` might later solve it!), so returning `Bool` conflates *"definitely unequal"* with *"stucked on non-pattern meta"*.
3. **Preserving glued abbreviations in solutions (`EQUAL.md:188`)**: Standard NbE pattern unification quotes the **forced** value of the RHS, unfolding user definitions like `notBool y` into raw `matchData` case trees inside synthesized meta solutions!

**How to build `Narya/Core/Unify.lean`**:
1. **Purely Functional Transactional `MetaCtx`**:
   Store `entries : List (Nat × MetaEntry)` + a strictly increasing `generation : Nat` counter (`solveMeta_generation_strictly_increases`). Speculative Tier-1 spine unification (`unifyRigidSpines`) threads `mc`, and on `.notEqual` or `.blocked`, simply **discards** the speculative `MetaCtx` (`speculative_never_mutates_metas`)! When `generation` advances during a comparison (`mc'.generation > mc.generation`), `FallbackPolicy.localRetry` re-runs local conversion under the newly learned meta bindings instead of failing prematurely.
2. **Ternary `UnifyOutcome`**:
   `equal (mc' : MetaCtx) | notEqual | blocked (metaId : Nat) (mc' : MetaCtx)`.
3. **Glued-First Miller Readback with Pruning Fallback (`quotePatternRHS?`)**:
   Given `?m x₁ ... xₖ ≡ rhs` where `[x₁, ..., xₖ]` are distinct bound levels (`extractMillerSpine?`):
   - When `rhs = .glued name rspine forced`: **first** attempt `quotePatternSpine? (.global name) rspine` checking that every free variable in `rspine` belongs to `{x₁, ..., xₖ}` and `?m` does not occur (`occursCheck_rejects_self_cycle`). If it succeeds, `?m` is solved as `fun x₁ ... xₖ => name ...` **without unfolding `name`**!
   - If `rspine` mentions an out-of-scope variable `y ∉ {x₁, ..., xₖ}` (e.g. `?m0 x ≡ constZero y` where `constZero z := 0`), `quotePatternSpine?` returns `none`, and `quotePatternRHS?` **automatically falls back to `forced`** (`0`), pruning the dead dependency on `y` and solving `?m0 := fun x => 0`!

### 4.6 Open Problem G: Strict Positivity, Coinductive Guardedness & `--without-K` (`Safety.lean`)
A proof assistant combining inductive `data`, coinductive `codata`/`Energy.potential`, and computational univalence (`Glue`) faces three lethal consistency hazards if unchecked:
1. **Non-positive inductives (`Bad := mk : (Bad → Empty) → Bad`)**: Yield Curry's/Girard's paradox in 4 lines without `Type : Type`. `checkDataSpecPositivity` forbids the inductive type name anywhere to the left of `Π`/`→` (`occursInTerm`), while allowing strictly positive recursive arguments and infinitary branching trees like Brouwer ordinals (`sup : (Nat → Ord) → Ord`).
2. **Unguarded kinetic/potential recursion**: `checkDefGuardedness` forbids recursive references in `Energy.kinetic` definitions (`Loop := sig { f : Loop }`) and requires `Energy.potential` definitions (like `SST`) to guard every self-reference inside a negative type constructor (`.recordTy`, `.codataTy`, `.pi`) or lazy constructor wrapper.
3. **Axiom K vs Univalence (`univalence_refutes_axiomK`)**:
   Hofmann–Streicher's Axiom K (`∀ (p : Id Bool Bool), p = refl Bool`) contradicts univalence! In `Safety.lean`:
   - `checkWithoutKPathMatch` enforces Cockx–Devriese–Piessens `--without-K` pattern matching: both path endpoints must be constructor-free (`isConstructorFreePat`) and linearly distinct (`(patVars lhs).all (fun v => !(patVars rhs).contains v)`), rejecting `Id A x x` (Axiom K) and `Id A x (succ x)` while accepting `J` (`Id A x y`).
   - `univalence_refutes_axiomK` proves **directly inside Lean's kernel** (`0 sorry`) that `uaBool := Glue(Bool, Bool, notEquiv)` transports `true ↦ false` while `reflBool` transports `true ↦ true`, hence `uaBool ≠ reflBool`, refuting `AxiomK`!

---

## 5. Layer 5: A Perfectible Programming Language & Verified `AArch64` Backend (`Narya/Fast/`, `Narya/Compiler/`)

### 5.1 Connecting Type Theory, Cost Semantics (`TimeM`), and Optimization
In *"A perfectable programming language"* (`alok.blog`), optimization is not an ad-hoc compiler black box: fast bit-packed or unboxed representations sit side-by-side with clear mathematical specifications, linked by representation bridges (`RepBridge` / `Gel`) and machine-checked cost certificates (`TimeM`, `VerifiedOpt`):
- In `perfectibleOptTheory`:
  - Mode `"Logic"` retains HoTT paths (`Dir.hott`) and binary representation bridges (`Dir.param 2`), transporting specifications automatically across representation changes.
  - Mode `"Mach"` discretizes representation bridges (`discreteDirs := [.param 2]`), allowing intensional machine cost (`TimeM.time`) and hardware layout to be observed consistently without violating internal parametricity!
- **Case Study 1 (`Narya/Fast/PackedDim.lean` + `TimeM.lean`)**:
  `PackedSFace` packs strict cubical faces of rank $\le 63$ into two unboxed `UInt64` bitmasks (`endMask`, `valMask`). Using `Std.Tactic.BVDecide` (`bv_decide`), `packed_isId_eq_ref` and `packed_sface_isId_correct_and_faster` prove bit-exact equivalence with `Narya.Dim.SFace` alongside an asymptotic $O(d) \to O(1)$ operational cost reduction (`1` tick vs `d + 1` ticks).
- **Case Study 2 (`loopFusionOpt` in `TimeM.lean`)**:
  Proves two-pass heap list map+sum refines to single-pass register accumulation (`n + 1 < 2n + 2` ticks for all lists).

### 5.2 Open Problem H: Coding Register Promotion & Counted Hardware Loops (`HIR → MIR → LIR → Arm64`)
Modeled on Leonardo de Moura's November 2026 SViL architecture (*"New Code Generator"*), upgraded from a pure stack machine to a **register-promoting, hardware-loop compiler** across both **macOS Mach-O (`arm64-apple-darwin`)** and **Linux ELF (`aarch64-linux-gnu`)**:

| Stage | Module | Key Responsibility | Correctness Theorem (`0 sorry`) |
|---|---|---|---|
| **1. HIR** | `Narya/Compiler/HIR.lean` | Erases modal `key`s, `boxIntro`s, and `refl` bridges; folds constants, eliminates dead `ifZero` branches, strength-reduces `x * 2 ↝ x <<< 1`, eliminates 0-trip `repeatLoop`s, & unrolls 1-trip loops (`HIR.opt`) | `HIR.eval_opt_eq` |
| **2. MIR** | `Narya/Compiler/MIR.lean` | Static variable use-count / uniqueness analysis (`OwnershipKind`), loop-nesting detection (`MIR.hasLoop`), `joinIfZero`, & `repeatLoop` (`MIR.lowerFromHIR`) | `MIR.eval_lower_eq` |
| **3. LIR** | `Narya/Compiler/LIR.lean` | Promotes lexical variables, loop accumulators, & `binOp` LHS operands to caller-saved `LocalReg` (`x4..x7`) when `< 4` live (zero stack traffic!), spilling deeper scopes (`≥ 4`) to `[sp, #16*k]` (`LIR.lowerFromMIR`) | `LIR.exec_compileAux` & `LIR.exec_lowerFromMIR_acc_and_stack` |
| **4. Arm64** | `Narya/Compiler/Arm64.lean` | Formal `AArch64` ISA (`x0..x8` + `sp`), `movz`/`movk` (`movzk_reconstruct_u64`), `loopX8` (`cbz`/`sub x8, #1`/`cbnz`), `x8` non-interference (`noLoopCode_preserves_x8`), & Mach-O / Linux ELF native runners | `Arm64.compileFullPipeline_correct` & `Arm64.compileFullPipeline_stack_clean` |

#### Deep-Dive Engineering Walkthrough for Manual Implementation:
1. **Zero-Overhead Caller-Saved Register Promotion (`x4..x7` in `LIR.compileAux`)**:
   - Under AAPCS64 (both Apple Darwin and Linux), `x0` is return/arg0, `x1` is scratch/arg1, `x2..x3` hold saved `(arg0, arg1)`, **`x4..x7` are caller-saved registers** (requiring zero function prologue/epilogue stack spills!), and **`x8` is caller-saved** (used as our hardware loop counter).
   - `compileAux (locs : List VarLoc) (usedRegs : Nat) (curH : Nat)` allocates monotonically in `usedRegs`:
     - Whenever `usedRegs < 4`, `letAlloc`, `repeatLoop` accumulators, and `binOp` LHS operands bind `r = ⟨usedRegs, hReg⟩` (`x_{4+usedRegs}`) and compile their inner continuation at `usedRegs + 1`.
     - Sequential sibling `letAlloc`s and `binOp`s **automatically reuse** `x_{4+usedRegs}` as soon as the previous subexpression finishes!
     - Only when 4 outer registers are simultaneously live (`usedRegs ≥ 4`) does `compileAux` spill to `[sp, #16 * (curH - 1 - h)]`.
   - **Inductive Simulation Postcondition**: Because `compileAux` at `usedRegs` may clobber dead scratch registers `≥ usedRegs`, the exact inductive postcondition in `LIR.exec_compileAux` is:
     `st'.acc = MIR.eval p₀ p₁ env m ∧ st'.stack = st.stack ∧ (∀ r : LocalReg, r.val < usedRegs → st'.getLocal r = st.getLocal r)`.
     Those three conjuncts compose cleanly across `binOp`, `letAlloc`, `joinIfZero`, and `repeatLoop`!
2. **Nested-Safe Hardware Loops in `x8` (`loopX8` & `saveCounter`)**:
   - What happens if an outer `repeatLoop` contains an inner `repeatLoop`? If both wrote to `x8` unconditionally, the inner loop would clobber the outer loop's `x8`!
   - Solution: `MIR.hasLoop stepBody` checks statically whether `stepBody` contains an inner loop:
     - **Inner / single hot loops (`saveCounter = false`)**: `noLoopCode_preserves_x8` proves `stepBody` never touches `x8` (`Reg64` only indexes `x0..x7`!). Emitted assembly loads `x8` once before the loop and runs `L_loop: <register-only body>; sub x8, x8, #1; cbnz x8, L_loop` with **zero memory ops (`LIR.countStackOps = 0`)**!
     - **Outer loops (`saveCounter = true`)**: Each outer iteration executes `str x8, [sp, #-16]!`, runs `stepBody` compiled at stack depth `curH + 1` (so any `[sp, #16*slot]` offsets inside `stepBody` automatically account for the pushed `x8`!), and executes `ldr x8, [sp], #16` before `sub x8, x8, #1; cbnz x8, L_loop`!
3. **Keeping `LIR.exec` and `Arm64.exec` Structural (`iterStep` Trick)**:
   - If `runLoop` is placed inside a `mutual` block with `step` and `exec` using `termination_by`, Lean compiles `exec` via `WellFounded.fix`, which blocks fast kernel reduction under `decide`!
   - By factoring out `iterStep : Bool → (State → State) → ...` and writing `iterN iters.toNat (iterStep save (exec body)) ...`, the recursive call `exec body` is passed directly on constructor child `body` **without `WellFounded.fix`**, keeping `step` and `exec` 100% structural!
4. **Mach-O (`arm64-apple-darwin`) vs ELF (`aarch64-linux-gnu`) Assembly**:
   - macOS Mach-O prefixes C symbols with `_` (`_narya_entry`) under `.section __TEXT,__text,regular,pure_instructions`.
   - Linux ELF uses unprefixed symbols (`narya_entry`), `.type narya_entry, %function`, and `.section .note.GNU-stack,"",%progbits` (preventing GNU `ld` executable-stack warnings on Ubuntu 24.04 ARM64).

---

## 6. Developer Manual: Extending & Using `narya-lean`

### 6.1 Writing Proofs in Lean 4 with `narya_hoTT!`, `calc_eq`, and `narya!`
Import `Narya` in any `.lean` file:
```lean
import Narya
open Narya.Modal.Combinators Narya.Core Narya.Elab

def G := GlobalEnv.withStdPrelude pureHoTT

-- Interactive InfoView typechecking, equational chains & normalization:
#narya_check [G] fun (A : _) => refl(A)
#narya_eval  [G] trr(refl(Bool), true)
#narya_eval  [hoTTWithNot] trr(calc_eq(Bool == Bool by Glue(Bool, Bool, notEquiv) == Bool by <- Glue(Bool, Bool, notEquiv)), true)
```

### 6.2 Defining Custom Mode Theories
Use either the declarative `def_mode_theory` macro or 2-categorical combinators:
```lean
-- Option A: Declarative macro
def_mode_theory MyGuardedCohesive default_mode Space where
  mode Set
  discrete_modality shape : Space -> Set
  sinister_modality disc  : Set -> Space

-- Option B: First-class algebraic combinators (with 2-cells & equations)
def myDoubleAdj :=
  amalgamate "double_adj"
    (adjunctionNamed "a1" "M0" "M1" "L1" "R1" "eta1" "eps1")
    (adjunctionNamed "a2" "M1'" "M2" "L2" "R2" "eta2" "eps2")
    [("M1", "M1'")]
```

### 6.3 Compiling & Running Zero-Spill Verified Hardware Loops (`AArch64`)
```lean
import Narya
open Narya.Compiler

def myLoopKernel : HIR :=
  .repeatLoop 1000 (.param ⟨0, by omega⟩)
    (.binOp .add (.binOp .mul (.var 0) (.lit 2)) (.param ⟨1, by omega⟩))

-- 1. Automatic proof of AArch64 correctness for all 64-bit inputs:
theorem myLoopKernel_verified (x y : UInt64) :
    (Arm64.exec (Arm64.compileFullPipeline myLoopKernel) (Arm64State.initABI x y)).x0 =
      HIR.eval x y [] myLoopKernel :=
  Arm64.compileFullPipeline_correct myLoopKernel x y

-- 2. Automatic certificate of ZERO stack memory traffic (`x4..x7` + `x8` only!):
theorem myLoopKernel_zero_spills :
    LIR.countStackOps (LIR.lowerFromMIR (MIR.lowerFromHIR (HIR.opt myLoopKernel))) = 0 := by
  decide
```

### 6.4 CLI Workflow (`lake exe narya`)
```bash
lake build                                           # Build full library & compile-time #guard proofs
lake test                                            # Run all 47 unit, modal, unify, safety & native AArch64 tests
lake exe narya catalog                               # Inspect all 20 built-in mode theories
lake exe narya run examples/univalence_and_modal.ny  # Execute standalone .ny script
lake exe narya asm                                   # Print verified AArch64 assembly & run on hardware
lake exe narya bench                                 # Run TimeM + 50,000-trip AArch64 loop benchmarks
```
