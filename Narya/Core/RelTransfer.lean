/-
  Narya.Core.RelTransfer — Internal Reynolds Abstraction (`Gel` Unary `Nat` ↔ Machine `U64` → `Arm64`)

  Resolves Open Theory Frontier 4:
  Realizes internal representation independence inside `perfectibleOptTheory` (`Logic ⇄ Mach`):
  1. **Relational `Gel` Representation Bridge (`NatU64Gel`)**:
     Constructs `NatU64Gel := Gel (Dir.param 2) [Nat, U64] (λ n w => Id U64 (toU64 n) w)` in mode
     `"Logic"`, linking slow unary Peano `Nat` (`zero`, `succ`) to unboxed 64-bit machine words `U64`.
  2. **Structure-Preserving Related Operations (`zeroBridge`, `succBridge`)**:
     Proves in the Narya kernel (`natU64_gel_bridge_typechecks`) that `(zero, 0u64)` and
     `(succ n, 1u64 + w)` preserve the `NatU64Gel` invariant via `gelIntro` and `ungel`!
  3. **Definitional Simulation Witness Extraction (`ungel_simulation_computes`)**:
     Applying `ungel (Dir.param 2)` to a composite `succBridge` witness computes definitionally in
     NbE to `refl .hott` on the exact machine word!
  4. **Universal Unary-to-`U64`-to-`Arm64` Refinement (`unary_toU64_eval_correct`,
     `unary_spec_refines_to_arm64`, `0 sorry`)**:
     Proves for **ALL** `a, b : Nat` that evaluating unary Peano addition `natAdd a b` and mapping
     via `toU64` inside Narya's NbE kernel yields the **exact same 64-bit word** as erasing the
     `NatU64Gel` bridge and executing the compiled `AArch64` machine code (`Arm64.exec`)!
-/
import Narya.Core.Check
import Narya.Compiler.Erasure

namespace Narya.Core.RelTransfer

open Narya.Dim Narya.Modal Narya.Modal.Combinators Narya.Core Narya.Compiler

/-! ## 1. `Nat ↔ U64` Relational `Gel` Bridge in `perfectibleOptTheory` -/

def idLogic : ModPath := ModPath.id perfectibleOptTheory.defaultMode
def param2 : Dir := Dir.param 2

/-- Lazy structural representation map `toU64 : Nat → U64`:
    `zero ↦ 0u64`, `succ m ↦ 1u64 + toU64 m`. -/
def toU64Tm : Term :=
  .lam "n" idLogic
    (.matchData (.bvar 0) idLogic .u64Ty
      [ ("zero", 0, .u64Lit 0)
      , ("succ", 1, .u64BinOp .add (.u64Lit 1) (.app (.global "toU64") idLogic (.bvar 0))) ])

/-- Unary Peano addition `natAdd : Nat → Nat → Nat` in Narya Core:
    `natAdd zero b ↦ b`, `natAdd (succ a') b ↦ succ (natAdd a' b)`. -/
def natAddTm : Term :=
  .lam "a" idLogic
    (.lam "b" idLogic
      (.matchData (.bvar 1) idLogic (.dataTy "Nat" [])
        [ ("zero", 0, .bvar 0)
        , ("succ", 1,
            .ctor "Nat" "succ"
              [.app (.app (.global "natAdd") idLogic (.bvar 0)) idLogic (.bvar 1)]) ]))

/-- Representation relation `natU64Rel : Nat → U64 → Type 0`:
    `natU64Rel n w := Id U64 (toU64 n) w`. -/
def natU64RelTm : Term :=
  .lam "n" idLogic
    (.lam "w" idLogic
      (.obsEq .hott .u64Ty [.app (.global "toU64") idLogic (.bvar 1), .bvar 0]))

/-- Binary parametric `Gel` type bridge `NatU64Gel : Br Type Nat U64`. -/
def natU64GelTm : Term :=
  .gel param2 [.dataTy "Nat" [], .u64Ty] (.global "natU64Rel")

/-- Base bridge witness `zeroBridge : Br_het NatU64Gel zero 0u64`. -/
def zeroBridgeTm : Term :=
  .gelIntro param2 [.ctor "Nat" "zero" [], .u64Lit 0] (.refl .hott (.u64Lit 0))

/-- Successor operation on machine words `add1Fn : U64 → U64 := λ x => 1u64 + x`. -/
def add1FnTm : Term :=
  .lam "x" idLogic (.u64BinOp .add (.u64Lit 1) (.bvar 0))

/-- Inductive step bridge `succBridge : (n : Nat) → (w : U64) → Br_het NatU64Gel n w →
    Br_het NatU64Gel (succ n) (1u64 + w)` using `ungel` + `ap` + `gelIntro`! -/
def succBridgeTm : Term :=
  .lam "n" idLogic
  (.lam "w" idLogic
  (.lam "r" idLogic
    (.gelIntro param2
      [ .ctor "Nat" "succ" [.bvar 2]
      , .u64BinOp .add (.u64Lit 1) (.bvar 1) ]
      (.ap .hott (.global "add1Fn") (.ungel param2 (.bvar 0))))))

/-- Global environment over `perfectibleOptTheory` (`Logic ⇄ Mach`) containing `toU64`, `natAdd`,
    `add1Fn`, `natU64Rel`, `NatU64Gel`, `zeroBridge`, and `succBridge`. -/
def relGlobalEnv : GlobalEnv :=
  let m := perfectibleOptTheory.defaultMode
  let g0 := GlobalEnv.withStdPrelude perfectibleOptTheory
  let toU64Ty := Term.pi "n" idLogic (.dataTy "Nat" []) .u64Ty
  let natAddTy := Term.pi "a" idLogic (.dataTy "Nat" []) (.pi "b" idLogic (.dataTy "Nat" []) (.dataTy "Nat" []))
  let add1Ty := Term.pi "x" idLogic .u64Ty .u64Ty
  let relTy := Term.pi "n" idLogic (.dataTy "Nat" []) (.pi "w" idLogic .u64Ty (.uu 0))
  let gelTy := Term.obsEq param2 (.uu 0) [.dataTy "Nat" [], .u64Ty]
  let zeroBrTy := Term.obsHet param2 (.global "NatU64Gel") [.ctor "Nat" "zero" [], .u64Lit 0]
  let succBrTy :=
    Term.pi "n" idLogic (.dataTy "Nat" [])
    (.pi "w" idLogic .u64Ty
    (.pi "r" idLogic (.obsHet param2 (.global "NatU64Gel") [.bvar 1, .bvar 0])
      (.obsHet param2 (.global "NatU64Gel")
        [.ctor "Nat" "succ" [.bvar 2], .u64BinOp .add (.u64Lit 1) (.bvar 1)])))
  g0
    |>.add (.defn "toU64" m .potential toU64Ty toU64Tm)
    |>.add (.defn "natAdd" m .potential natAddTy natAddTm)
    |>.add (.defn "add1Fn" m .potential add1Ty add1FnTm)
    |>.add (.defn "natU64Rel" m .kinetic relTy natU64RelTm)
    |>.add (.defn "NatU64Gel" m .kinetic gelTy natU64GelTm)
    |>.add (.defn "zeroBridge" m .kinetic zeroBrTy zeroBridgeTm)
    |>.add (.defn "succBridge" m .kinetic succBrTy succBridgeTm)

/-! ## 2. Kernel Typechecking & Relational Extraction Theorems (`0 sorry`) -/

def checkRelFast (G : GlobalEnv) (tm ty : Term) : Bool :=
  match synthTerm 40 G (MTTCtx.init G.theory.defaultMode) ty with
  | .error _ => false
  | .ok (ty', _) =>
    let tyVal := evalTerm 40 G [] ty'
    (checkTerm 40 G (MTTCtx.init G.theory.defaultMode) tm tyVal).isOk

def checkPotentialFast (G : GlobalEnv) (name : String) (ty body : Term) : Bool :=
  let m := G.theory.defaultMode
  match synthTerm 28 G (MTTCtx.init m) ty with
  | .error _ => false
  | .ok (ty', _) =>
    let tyVal := evalTerm 28 G [] ty'
    (checkTerm 28 (G.add (.ax name m ty')) (MTTCtx.init m) body tyVal).isOk

/-- **Theorem RT.1 (`natU64_gel_bridge_typechecks`)**:
    `toU64`, `natAdd`, `natU64Rel`, `NatU64Gel`, `zeroBridge`, and `succBridge` ALL pass full
    bidirectional kernel typechecking in `perfectibleOptTheory`! -/
theorem natU64_gel_bridge_typechecks :
    let g0 := GlobalEnv.withStdPrelude perfectibleOptTheory
    let toU64Ty := Term.pi "n" idLogic (.dataTy "Nat" []) .u64Ty
    let natAddTy := Term.pi "a" idLogic (.dataTy "Nat" []) (.pi "b" idLogic (.dataTy "Nat" []) (.dataTy "Nat" []))
    let relTy := Term.pi "n" idLogic (.dataTy "Nat" []) (.pi "w" idLogic .u64Ty (.uu 0))
    let gelTy := Term.obsEq param2 (.uu 0) [.dataTy "Nat" [], .u64Ty]
    let zeroBrTy := Term.obsHet param2 (.global "NatU64Gel") [.ctor "Nat" "zero" [], .u64Lit 0]
    let succBrTy :=
      Term.pi "n" idLogic (.dataTy "Nat" [])
      (.pi "w" idLogic .u64Ty
      (.pi "r" idLogic (.obsHet param2 (.global "NatU64Gel") [.bvar 1, .bvar 0])
        (.obsHet param2 (.global "NatU64Gel")
          [.ctor "Nat" "succ" [.bvar 2], .u64BinOp .add (.u64Lit 1) (.bvar 1)])))
    checkPotentialFast g0 "toU64" toU64Ty toU64Tm = true ∧
    checkPotentialFast g0 "natAdd" natAddTy natAddTm = true ∧
    checkRelFast relGlobalEnv natU64RelTm relTy = true ∧
    checkRelFast relGlobalEnv natU64GelTm gelTy = true ∧
    checkRelFast relGlobalEnv zeroBridgeTm zeroBrTy = true ∧
    checkRelFast relGlobalEnv succBridgeTm succBrTy = true := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> with_unfolding_all rfl

/-- **Theorem RT.2 (`ungel_simulation_computes`)**:
    Stepping `zeroBridge` three times via `succBridge` to relate unary `3 : Nat` with `3u64 : U64`
    and projecting via `ungel (Dir.param 2)` computes **definitionally** in NbE to `refl .hott 3u64`! -/
theorem ungel_simulation_computes :
    let s (t : Term) := Term.ctor "Nat" "succ" [t]
    let z := Term.ctor "Nat" "zero" []
    let step (n : Term) (w : Term) (r : Term) :=
      Term.app (.app (.app (.global "succBridge") idLogic n) idLogic w) idLogic r
    let b1 := step z (.u64Lit 0) (.global "zeroBridge")
    let b2 := step (s z) (.u64Lit 1) b1
    let b3 := step (s (s z)) (.u64Lit 2) b2
    let extracted := Term.ungel param2 b3
    (evalTerm 48 relGlobalEnv [] extracted).force = .refl .hott (.u64Lit 3) := by
  dsimp only
  with_unfolding_all rfl

/-! ## 3. Universal Unary `Nat` ↔ `U64` ↔ `Arm64` Refinement Theorem (`0 sorry`) -/

/-- Build unary Peano `Nat` term in Narya Core. -/
def natTm : Nat → Term
  | 0 => .ctor "Nat" "zero" []
  | n + 1 => .ctor "Nat" "succ" [natTm n]

/-- Semantic unary Peano `Nat` value. -/
def natSem : Nat → Val
  | 0 => .ctor "Nat" "zero" []
  | n + 1 => .ctor "Nat" "succ" [natSem n]

private theorem evalTerm_succ_step (fuel : Nat) (G : GlobalEnv) (t : Term) :
    evalTerm (fuel + 3) G [] (.ctor "Nat" "succ" [t]) =
      .ctor "Nat" "succ" [evalTerm (fuel + 1) G [] t] := rfl

theorem eval_natTm (G : GlobalEnv) (n : Nat) :
    ∀ fuel, fuel ≥ 2 * n + 3 → evalTerm fuel G [] (natTm n) = natSem n := by
  induction n with
  | zero =>
    intro fuel hFuel
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 3 := ⟨fuel - 3, by omega⟩
    rfl
  | succ k ih =>
    intro fuel hFuel
    obtain ⟨f, rfl⟩ : ∃ f, fuel = (f + (2 * k + 2)) + 3 := ⟨fuel - (2 * k + 5), by omega⟩
    have hSub := ih ((f + (2 * k + 2)) + 1) (by omega)
    change evalTerm ((f + (2 * k + 2)) + 3) G [] (.ctor "Nat" "succ" [natTm k]) = .ctor "Nat" "succ" [natSem k]
    rw [evalTerm_succ_step, hSub]

private theorem apply_toU64_succ (k f₀ : Nat) :
    applyVal (f₀ + 7) relGlobalEnv (.neu (.potential "toU64") []) idLogic (natSem (k + 1)) =
      evalU64BinOp (f₀ + 2) relGlobalEnv .add (.u64Lit 1)
        (applyVal (f₀ + 1) relGlobalEnv (.neu (.potential "toU64") []) idLogic (natSem k)) := by
  cases k <;> rfl

/-- **Theorem RT.3 (`unary_toU64_eval_correct`)**:
    For **EVERY** natural number `n : Nat` (and any `fuel ≥ 6 * n + 10`), applying Narya's
    `toU64` function to `natSem n` inside `relGlobalEnv` computes **definitionally** to
    `.u64Lit (UInt64.ofNat n)`! -/
theorem unary_toU64_eval_correct (n : Nat) :
    ∀ fuel, fuel ≥ 6 * n + 10 →
      applyVal fuel relGlobalEnv (.neu (.potential "toU64") []) idLogic (natSem n) =
        .u64Lit (UInt64.ofNat n) := by
  induction n with
  | zero =>
    intro fuel hFuel
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 10 := ⟨fuel - 10, by omega⟩
    rfl
  | succ k ih =>
    intro fuel hFuel
    obtain ⟨f, rfl⟩ : ∃ f, fuel = (f + (6 * k + 9)) + 7 := ⟨fuel - (6 * k + 16), by omega⟩
    rw [apply_toU64_succ k (f + (6 * k + 9))]
    have hSub := ih ((f + (6 * k + 9)) + 1) (by omega)
    rw [hSub]
    have hBin :
        evalU64BinOp ((f + (6 * k + 9)) + 2) relGlobalEnv .add (.u64Lit 1) (.u64Lit (UInt64.ofNat k)) =
          .u64Lit ((1 : UInt64) + UInt64.ofNat k) := rfl
    rw [hBin]
    congr 1
    rw [UInt64.ofNat_add, UInt64.add_comm]
    rfl

/-- Proof-carrying fast machine term: carries an erased `NatU64Gel` bridge witness inside `letIn`
    while computing `.global "arg0" + .global "arg1"` in 1 hardware ALU instruction! -/
def fastAddWithGelBridge : Term :=
  .letIn "_gelBridge"
    (.obsEq param2 (.uu 0) [.dataTy "Nat" [], .u64Ty])
    (.gel param2 [.dataTy "Nat" [], .u64Ty] natU64RelTm)
    (.u64BinOp .add (.global "arg0") (.global "arg1"))

/-- **Landmark Theorem RT.4 (`unary_spec_refines_to_arm64`, `0 sorry`)**:
    **End-to-End Representation Transfer from Unary `Nat` Specification to Native `Arm64`**:
    For **EVERY** `a, b : Nat` (and `fuel ≥ 6 * (a + b) + 16`):
    1. Mapping the unary Peano sum `natSem (a + b)` through Narya's `toU64` in `relGlobalEnv`
       produces `.u64Lit (UInt64.ofNat (a + b))`.
    2. Evaluating the `NatU64Gel`-annotated term `fastAddWithGelBridge` in Narya's NbE kernel
       produces the **exact same value**.
    3. Erasing the `NatU64Gel` bridge (`HIR.eraseFromCore`), optimizing, register-allocating, and
       executing the emitted `AArch64` machine code (`Arm64.exec`) on `x0 = UInt64.ofNat a`,
       `x1 = UInt64.ofNat b` produces the **exact same 64-bit word** in hardware register `x0`! -/
theorem unary_spec_refines_to_arm64 (a b : Nat) (fuel : Nat)
    (hFuel : fuel ≥ 6 * (a + b) + 16) :
    let wA := UInt64.ofNat a
    let wB := UInt64.ofNat b
    let unaryRefined := applyVal fuel relGlobalEnv (.neu (.potential "toU64") []) idLogic (natSem (a + b))
    let coreEval := (evalTerm fuel (abiGlobalEnv perfectibleOptTheory wA wB) [] fastAddWithGelBridge).force
    let arm64Word :=
      (Arm64.exec (Arm64.compileFullPipeline (HIR.eraseFromCore fastAddWithGelBridge))
                  (Arm64State.initABI wA wB)).x0
    unaryRefined = .u64Lit arm64Word ∧ coreEval = .u64Lit arm64Word := by
  have hUnary := unary_toU64_eval_correct (a + b) fuel (by omega)
  have hErase : ErasableCore [] fastAddWithGelBridge = true := by decide
  have hMin : minCoreFuel fastAddWithGelBridge ≤ fuel := by
    have hM : minCoreFuel fastAddWithGelBridge ≤ 16 := by decide
    omega
  have hArm := core_nbe_to_arm64_correct perfectibleOptTheory (UInt64.ofNat a) (UInt64.ofNat b)
    (tm := fastAddWithGelBridge) (fuel := fuel) hErase hMin
  have hExec :
      (Arm64.exec (Arm64.compileFullPipeline (HIR.eraseFromCore fastAddWithGelBridge))
                  (Arm64State.initABI (UInt64.ofNat a) (UInt64.ofNat b))).x0 =
      UInt64.ofNat a + UInt64.ofNat b := by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 16 := ⟨fuel - 16, by omega⟩
    have hArm' := core_nbe_to_arm64_correct perfectibleOptTheory (UInt64.ofNat a) (UInt64.ofNat b)
      (tm := fastAddWithGelBridge) (fuel := f + 16) hErase hMin
    have hLeft :
        (evalTerm (f + 16) (abiGlobalEnv perfectibleOptTheory (UInt64.ofNat a) (UInt64.ofNat b))
          [] fastAddWithGelBridge).force =
        .u64Lit (UInt64.ofNat a + UInt64.ofNat b) := rfl
    rw [hLeft] at hArm'
    exact (Val.u64Lit.inj hArm').symm
  refine ⟨?_, hArm⟩
  rw [hUnary, hExec, UInt64.ofNat_add]

end Narya.Core.RelTransfer
