/-
  Narya.Examples.Tour — Machine-Checked Showcase of Unified Multi-Modal HoTT & Verified ARM64 Codegen

  Demonstrates:
  1. Familiar Lean 4 `narya_hoTT!` / `narya!` DSL & Computational Univalence (`Glue` + `trr` / `trl`)
  2. Binary Parametricity & `-external` Locker Gating (`Type_ext` blocked under `lock`, permitted outside)
  3. Displayed Type Theory (`displayedTheory`) & Guarded Coinductive Definitions (`Energy.potential` / `SST`)
  4. Declarative `def_mode_theory` Macro & 2-Categorical Combinators
  5. Perfectible Programming Language (`HIR.opt → MIR → LIR → Arm64`) with Zero-`sorry` Correctness
-/
import Narya.Dim
import Narya.Modal
import Narya.Core
import Narya.Syntax
import Narya.Elab
import Narya.Fast
import Narya.Compiler

namespace Narya.Examples

open Narya.Dim Narya.Modal Narya.Modal.Combinators Narya.Core Narya.Syntax Narya.Elab
open Narya.Fast Narya.Compiler

/-! ### 1. Computational Univalence (`Glue` + `trr` / `trl`) in `narya_hoTT!` -/

/-- Boolean negation `notBool : Bool → Bool` in Core Narya. -/
def notBoolTy : Term := narya_hoTT! Bool → Bool

def notBoolBody : Term :=
  .lam "b" (ModPath.id "M")
    (.matchData (.bvar 0) (ModPath.id "M")
      (.dataTy "Bool" [])
      [ ("false", 0, .ctor "Bool" "true" [])
      , ("true",  0, .ctor "Bool" "false" []) ])

/-- Equivalence record type `{ fwd : Bool → Bool, bwd : Bool → Bool }`. -/
def boolEquivTy : Term :=
  narya_hoTT! sig { fwd : Bool → Bool, bwd : Bool → Bool }

def notEquivBody : Term :=
  narya_hoTT! ⟨ fwd := notBool, bwd := notBool ⟩

/-- Standard HoTT environment extended with checked `notBool` and `notEquiv`. -/
def hoTTWithNot : GlobalEnv :=
  let G0 := GlobalEnv.withStdPrelude pureHoTT
  match addCheckedDef G0 "notBool" notBoolTy notBoolBody with
  | .error _ => G0
  | .ok G1 =>
    match addCheckedDef G1 "notEquiv" boolEquivTy notEquivBody with
    | .error _ => G1
    | .ok G2 => G2

/-- Univalence path `uaNot : Id(Type, Bool, Bool)` built via `Glue(Bool, Bool, notEquiv)`! -/
def uaNotTerm : Term :=
  narya_hoTT! Glue(Bool, Bool, notEquiv)

-- Compile-time verification (`#guard` checked during `lake build`):
--   1. `uaNotTerm : Id(Type, Bool, Bool)` typechecks in `pureHoTT`
--   2. Forward univalence transport `trr(Glue(Bool, Bool, notEquiv), true)` normalizes to `Bool.false`
--   3. Backward univalence transport `trl(Glue(Bool, Bool, notEquiv), false)` normalizes to `Bool.true`
--   4. Round-trip transport `trr(uaNot, trl(uaNot, true))` normalizes to `Bool.true`!
#guard (synthClosed hoTTWithNot uaNotTerm).isOk
#guard (normalize hoTTWithNot [] 0 (narya_hoTT! trr(Glue(Bool, Bool, notEquiv), true)) ==
  .ctor "Bool" "false" [])
#guard (normalize hoTTWithNot [] 0 (narya_hoTT! trl(Glue(Bool, Bool, notEquiv), false)) ==
  .ctor "Bool" "true" [])
#guard (normalize hoTTWithNot [] 0
  (narya_hoTT! trr(Glue(Bool, Bool, notEquiv), trl(Glue(Bool, Bool, notEquiv), true))) ==
  .ctor "Bool" "true" [])

-- 5. Full Computational HOTT Fibrancy (`arrowLine`, `prodLine`, `boxLine`, `calc_eq`):
--    - Transporting `(fun b => true) : Bool → Bool` across `arrowLine(uaNot, uaNot)` and applying
--      to `true` computes `not (true) = false`!
--    - Transporting `⟨fst := true, snd := false⟩` across `prodLine(uaNot, uaNot)` computes
--      `⟨fst := false, snd := true⟩`!
--    - Equational reasoning `calc_eq(Bool == Bool by uaNot == Bool by <- uaNot)` transports `true ~> true`!
#guard (normalize hoTTWithNot [] 0
  (narya_hoTT! (trr(arrowLine(Glue(Bool, Bool, notEquiv), Glue(Bool, Bool, notEquiv)), (fun b => true)) true)) ==
  .ctor "Bool" "false" [])
#guard (normalize hoTTWithNot [] 0
  (narya_hoTT! trr(prodLine(Glue(Bool, Bool, notEquiv), Glue(Bool, Bool, notEquiv)), ⟨fst := true, snd := false⟩)) ==
  .tuple [("fst", .ctor "Bool" "false" []), ("snd", .ctor "Bool" "true" [])])
#guard (normalize hoTTWithNot [] 0
  (narya_hoTT! trr(calc_eq(Bool == Bool by Glue(Bool, Bool, notEquiv) == Bool by <- Glue(Bool, Bool, notEquiv)), true)) ==
  .ctor "Bool" "true" [])

/-! ### 2. External Parametricity (`-external`) & Locker Universe Discipline -/

def extEnv : GlobalEnv := GlobalEnv.withStdPrelude externalParamTheory

/-- Outside `lock`, the external discrete universe `Type_ext` synthesizes cleanly! -/
theorem tour_ext_universe_allowed_unlocked :
    (synthClosed extEnv (narya! [externalParamTheory] Type_ext)).isOk = true := by
  decide

/-- Inside the parametricity locker `box(lock, Type_ext)`, `Type_ext` is **rejected** by the kernel
    with the exact locker diagnostic! -/
theorem tour_ext_universe_rejected_under_lock :
    synthClosed extEnv (narya! [externalParamTheory] box(lock, Type_ext)) =
      .error "External universe UU_ext is forbidden inside a parametricity locker!" :=
  rfl

/-! ### 3. Displayed Type Theory (`-dtt`) & Potential Coinductive `SST` -/

/-- Coinductive Semisimplicial Type (`SST`) skeleton checked under `Energy.potential`:
    `SST : Type 1 := sig { vtx : Type, step : SST }` (lazy `Val.glued` unfolding prevents divergence!). -/
def sstCheckedResult : Except String GlobalEnv :=
  let G0 := GlobalEnv.withStdPrelude displayedTheory
  let sstTy : Term := (narya! [displayedTheory] Type 1)
  let sstBody : Term := (narya! [displayedTheory] sig { vtx : Type, step : SST })
  addCheckedDef G0 "SST" sstTy sstBody .potential

#guard sstCheckedResult.isOk

/-! ### 4. Declarative `def_mode_theory` Macro in Lean 4 -/

def_mode_theory TourCohesive default_mode Space where
  mode Set
  discrete_modality pi0 : Space -> Set
  sinister_modality disc : Set -> Space
  discrete_modality codisc : Space -> Set

theorem tour_declarative_mode_theory_wf :
    TourCohesive.wf = true := by
  decide

/-! ### 5. Perfectible Programming Language: Verified `HIR → MIR → LIR → Arm64` Kernel -/

/-- Representative branch + strength-reduced arithmetic kernel (`collatzStepHIR`):
    Given `(n, _)` in `(x0, x1)`:
    `let parity := n & 1 in if parity == 0 then n >> 1 else ((n * 2) + n) + 1`
    Note: `HIR.opt` automatically strength-reduces `n * 2` to `n <<< 1` (`lsl`)! -/
def collatzStepHIR : HIR :=
  .letBind (.binOp .bitAnd (.param ⟨0, by omega⟩) (.lit 1))
    (.ifZero (.var 0)
      (.binOp .shr (.param ⟨0, by omega⟩) (.lit 1))
      (.binOp .add
        (.binOp .add
          (.binOp .mul (.param ⟨0, by omega⟩) (.lit 2))
          (.param ⟨0, by omega⟩))
        (.lit 1)))

/-- Machine-checked proof (`0 sorry`) that the emitted `AArch64` assembly for `collatzStepHIR`
    computes the exact 64-bit `HIR` specification for ALL `n, aux : UInt64`! -/
theorem tour_collatzStep_arm64_correct (n aux : UInt64) :
    (Arm64.exec (Arm64.compileFullPipeline collatzStepHIR) (Arm64State.initABI n aux)).x0 =
      HIR.eval n aux [] collatzStepHIR :=
  Arm64.compileFullPipeline_correct collatzStepHIR n aux

/-- Concrete sanity check on `n = 27` (`27` is odd, so `3 * 27 + 1 = 82`) and `n = 82` (`82 / 2 = 41`). -/
theorem tour_collatzStep_samples :
    (Arm64.exec (Arm64.compileFullPipeline collatzStepHIR) (Arm64State.initABI 27 0)).x0 = 82 ∧
    (Arm64.exec (Arm64.compileFullPipeline collatzStepHIR) (Arm64State.initABI 82 0)).x0 = 41 := by
  decide

/-- 64-bit SplitMix-style mixing kernel (`mix64HIR`) exercising 4-instruction `movz`/`movk`
    materialization (`0xBF58476D1CE4E5B9`), 64-bit `eor`, `lsr`, and `mul`. -/
def mix64HIR : HIR :=
  .letBind (.binOp .bitXor (.param ⟨0, by omega⟩) (.binOp .shr (.param ⟨0, by omega⟩) (.lit 30)))
    (.letBind (.binOp .mul (.var 0) (.lit 0xBF58476D1CE4E5B9))
      (.binOp .bitXor (.var 0) (.param ⟨1, by omega⟩)))

/-- Machine-checked proof (`0 sorry`) that `mix64HIR` compiles accurately to `AArch64` for all `(a0, a1)`. -/
theorem tour_mix64_arm64_correct (a0 a1 : UInt64) :
    (Arm64.exec (Arm64.compileFullPipeline mix64HIR) (Arm64State.initABI a0 a1)).x0 =
      HIR.eval a0 a1 [] mix64HIR :=
  Arm64.compileFullPipeline_correct mix64HIR a0 a1

/-- 111-iteration Collatz orbit kernel (`collatzOrbit111HIR`):
    Runs 111 steps of `if acc == 1 then 1 else collatzStep(acc)` inside a single register-promoted
    `AArch64` hardware `cbnz x8` loop! Starting from `n = 27` (which climbs to `9232`), it reaches `1`. -/
def collatzOrbit111HIR : HIR :=
  .repeatLoop 111 (.param ⟨0, by omega⟩)
    (.ifZero (.binOp .sub (.var 0) (.lit 1))
      (.lit 1)
      (.letBind (.binOp .bitAnd (.var 0) (.lit 1))
        (.ifZero (.var 0)
          (.binOp .shr (.var 1) (.lit 1))
          (.binOp .add
            (.binOp .add (.binOp .mul (.var 1) (.lit 2)) (.var 1))
            (.lit 1)))))

theorem tour_collatzOrbit111_arm64_correct (n aux : UInt64) :
    (Arm64.exec (Arm64.compileFullPipeline collatzOrbit111HIR) (Arm64State.initABI n aux)).x0 =
      HIR.eval n aux [] collatzOrbit111HIR :=
  Arm64.compileFullPipeline_correct collatzOrbit111HIR n aux

/-- **Zero-Spill Register Promotion Certificate (`0` `str`/`ldr` stack ops!)**:
    All variables and binary temporaries in `collatzOrbit111HIR` stay in `x4..x7` + `x8`! -/
theorem tour_collatzOrbit111_zero_stack_ops :
    LIR.countStackOps (LIR.lowerFromMIR (MIR.lowerFromHIR (HIR.opt collatzOrbit111HIR))) = 0 := by
  decide

set_option maxRecDepth 8192 in
/-- **Kernel Theorem (`0 sorry`)**: Running the emitted `AArch64` machine code for `collatzOrbit111HIR`
    on `n = 27` returns `1` in register `x0` (proved by rewriting along `Arm64.compileFullPipeline_correct`)! -/
theorem tour_collatzOrbit111_27_reaches_one :
    (Arm64.exec (Arm64.compileFullPipeline collatzOrbit111HIR) (Arm64State.initABI 27 0)).x0 = 1 := by
  rw [Arm64.compileFullPipeline_correct]
  decide

/-- 50,000-iteration SplitMix64 hardware loop (`iteratedMix64LoopHIR`):
    Scoped live-ranges reuse `x5..x6` while keeping the accumulator in `x4` and loop counter in `x8`,
    executing all 50,000 non-linear 64-bit mixing steps inside a single native `AArch64` `cbnz x8`
    loop with **zero stack memory traffic** and **zero C call overhead**! -/
def iteratedMix64LoopHIR : HIR :=
  .repeatLoop 50000 (.param ⟨0, by omega⟩)
    (.letBind
      (.letBind
        (.letBind (.binOp .add (.var 0) (.lit 0x9E3779B97F4A7C15))
          (.binOp .bitXor (.var 0) (.binOp .shr (.var 0) (.lit 30))))
        (.binOp .mul (.var 0) (.lit 0xBF58476D1CE4E5B9)))
      (.binOp .bitXor (.var 0) (.param ⟨1, by omega⟩)))

theorem tour_iteratedMix64_arm64_correct (seed salt : UInt64) :
    (Arm64.exec (Arm64.compileFullPipeline iteratedMix64LoopHIR) (Arm64State.initABI seed salt)).x0 =
      HIR.eval seed salt [] iteratedMix64LoopHIR :=
  Arm64.compileFullPipeline_correct iteratedMix64LoopHIR seed salt

theorem tour_iteratedMix64_zero_stack_ops :
    LIR.countStackOps (LIR.lowerFromMIR (MIR.lowerFromHIR (HIR.opt iteratedMix64LoopHIR))) = 0 := by
  decide

/-- Nested hardware `repeatLoop` kernel (`nestedLoopHIR`):
    Outer loop (`7` trips) wrapping an inner loop (`5` trips, total `35` additions of `arg1` to `arg0`),
    exercising automatic stack save/restore of outer hardware loop counter `x8`! -/
def nestedLoopHIR : HIR :=
  .repeatLoop 7 (.param ⟨0, by omega⟩)
    (.repeatLoop 5 (.var 0)
      (.binOp .add (.var 0) (.param ⟨1, by omega⟩)))

theorem tour_nestedLoop_arm64_correct (a0 a1 : UInt64) :
    (Arm64.exec (Arm64.compileFullPipeline nestedLoopHIR) (Arm64State.initABI a0 a1)).x0 =
      HIR.eval a0 a1 [] nestedLoopHIR :=
  Arm64.compileFullPipeline_correct nestedLoopHIR a0 a1

theorem tour_nestedLoop_sample :
    (Arm64.exec (Arm64.compileFullPipeline nestedLoopHIR) (Arm64State.initABI 100 3)).x0 = 205 := by
  rw [Arm64.compileFullPipeline_correct]
  decide

/-! ## 6. Proof-Carrying `narya_hoTT!` Term Erased & Verified Down to `Arm64.exec` -/

/-- Written directly in the Lean 4 `narya_hoTT!` macro DSL: binds a HoTT univalence `Glue`
    proof at `0`-graded unused position around a 111-step Collatz `u64_repeat` hardware loop! -/
def tourProofCarryingCollatz : Narya.Core.Term :=
  narya_hoTT!
    let ua : Id(Type, Bool, Bool) := Glue(Bool, Bool, notEquiv) ;
    u64_repeat(111, arg0, n =>
      u64_ifz(u64_and(n, u64(1)),
        u64_shr(n, u64(1)),
        u64_add(u64_mul(n, u64(3)), u64(1))))

theorem tour_proofCarryingCollatz_erasable :
    ErasableCore [] tourProofCarryingCollatz = true := by decide

theorem tour_proofCarryingCollatz_nbe_eq_arm64 (seed : UInt64) :
    (evalTerm 512 (abiGlobalEnv pureHoTT seed 0) [] tourProofCarryingCollatz).force =
      .u64Lit ((Arm64.exec (Arm64.compileFullPipeline (HIR.eraseFromCore tourProofCarryingCollatz))
                           (Arm64State.initABI seed 0)).x0) :=
  core_nbe_to_arm64_correct pureHoTT seed 0 tour_proofCarryingCollatz_erasable (by decide)

end Narya.Examples
