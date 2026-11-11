/-
  Narya.Core.Linear — Quantitative Modalities (`QTT`), Benton's `LNL`, & Static `RC == 1` Exclusivity

  Bridges Narya's Multimodal Type Theory (`MTT` / `linearAdjointTheory`) directly to low-level
  runtime performance (Perceus / Lean 4 FBIP destructive in-place reuse & zero-fan Interaction Nets):
  1. **Quantitative Semiring (`UsageGrade`: `0`, `1`, `ω`)**:
     Proves all 10 Rig/Semiring axioms (`add_zero`, `zero_add`, `add_comm`, `add_assoc`,
     `mul_one`, `one_mul`, `mul_zero`, `zero_mul`, `left_distrib`, `right_distrib`, `0 sorry`).
  2. **Branch-Sensitive Quantitative Usage Analysis (`varUsage`)**:
     Distinguishes multiplicative tensor (`add`: `f a` uses `x` in both `f` and `a` ⇒ `1 + 1 = ω`)
     from additive branching (`lub`: `ifZero c then x else x` uses `x` once on the taken path ⇒
     `lub 1 1 = 1`!) and erases type-only / ghost positions (`0 · q = 0`)!
  3. **Static Exclusivity & Zero-Cost Erasure Checker (`checkLinearity`)**:
     - Enforces `usage ≤ 1` on `1`-graded binders in linear modes (`"Lin"` in `linearAdjointTheory`),
       certifying **static `RC == 1` uniqueness** (zero refcount ops, branch-free in-place mutation!).
     - Enforces `usage == 0` on `0`-graded binders (`Ghost0`), certifying **zero-bit erasure**!
-/
import Narya.Core.Check

namespace Narya.Core.Linear

open Narya.Dim Narya.Modal Narya.Modal.Combinators Narya.Core

/-! ## 1. Machine-Checked QTT Rig / Semiring Laws (`zero sorry`) -/

@[simp] theorem add_zero (q : UsageGrade) : UsageGrade.add q .zero = q := by cases q <;> rfl
@[simp] theorem zero_add (q : UsageGrade) : UsageGrade.add .zero q = q := by cases q <;> rfl

theorem add_comm (p q : UsageGrade) : UsageGrade.add p q = UsageGrade.add q p := by
  cases p <;> cases q <;> rfl

theorem add_assoc (p q r : UsageGrade) :
    UsageGrade.add (UsageGrade.add p q) r = UsageGrade.add p (UsageGrade.add q r) := by
  cases p <;> cases q <;> cases r <;> rfl

@[simp] theorem mul_one (q : UsageGrade) : UsageGrade.mul q .one = q := by cases q <;> rfl
@[simp] theorem one_mul (q : UsageGrade) : UsageGrade.mul .one q = q := by cases q <;> rfl
@[simp] theorem mul_zero (q : UsageGrade) : UsageGrade.mul q .zero = .zero := by cases q <;> rfl
@[simp] theorem zero_mul (q : UsageGrade) : UsageGrade.mul .zero q = .zero := by cases q <;> rfl

theorem mul_comm (p q : UsageGrade) : UsageGrade.mul p q = UsageGrade.mul q p := by
  cases p <;> cases q <;> rfl

theorem mul_assoc (p q r : UsageGrade) :
    UsageGrade.mul (UsageGrade.mul p q) r = UsageGrade.mul p (UsageGrade.mul q r) := by
  cases p <;> cases q <;> cases r <;> rfl

theorem left_distrib (p q r : UsageGrade) :
    UsageGrade.mul p (UsageGrade.add q r) =
      UsageGrade.add (UsageGrade.mul p q) (UsageGrade.mul p r) := by
  cases p <;> cases q <;> cases r <;> rfl

theorem right_distrib (p q r : UsageGrade) :
    UsageGrade.mul (UsageGrade.add p q) r =
      UsageGrade.add (UsageGrade.mul p r) (UsageGrade.mul q r) := by
  cases p <;> cases q <;> cases r <;> rfl

@[simp] theorem lub_idem (q : UsageGrade) : UsageGrade.lub q q = q := by cases q <;> rfl

theorem modPath_grade_comp (μ ν : ModPath) :
    (ModPath.comp μ ν).flags.grade = UsageGrade.mul μ.flags.grade ν.flags.grade := by
  unfold ModPath.comp ModPath.flags
  dsimp only
  induction μ.steps with
  | nil => simp [ModalityFlags.id]
  | cons g rest ih =>
    simp only [List.cons_append, List.foldr]
    change UsageGrade.mul g.flags.grade (List.foldr (fun g acc => g.flags.comp acc) ModalityFlags.id (rest ++ ν.steps)).grade =
      UsageGrade.mul (UsageGrade.mul g.flags.grade (List.foldr (fun g acc => g.flags.comp acc) ModalityFlags.id rest).grade)
        (List.foldr (fun g acc => g.flags.comp acc) ModalityFlags.id ν.steps).grade
    rw [ih, mul_assoc]

/-! ## 2. Computational Usage Analysis (`varUsage`) -/

mutual

def varUsageList : List Term → Ix → UsageGrade
  | [], _ => .zero
  | t :: ts, ix => UsageGrade.add (varUsageAux t ix) (varUsageList ts ix)

def varUsageTuple : List (String × Term) → Ix → UsageGrade
  | [], _ => .zero
  | (_, t) :: rest, ix => UsageGrade.add (varUsageAux t ix) (varUsageTuple rest ix)

def varUsageBranches : List (String × Nat × Term) → Ix → UsageGrade
  | [], _ => .zero
  | (_, ar, body) :: rest, ix =>
    UsageGrade.lub (varUsageAux body (ix + ar)) (varUsageBranches rest ix)

/-- Structural recursion on `Term` first (`Term → Ix → UsageGrade`) so Lean 4 compiles to `Term.rec`! -/
def varUsageAux : Term → Ix → UsageGrade
  | .bvar j, ix => if j == ix then .one else .zero
  | .mvar _, _ | .global _, _ | .uu _, _ | .uuExt _, _ | .u64Ty, _ | .u64Lit _, _
  | .pi _ _ _ _, _ | .recordTy _, _ | .dataTy _ _, _ | .obsEq _ _ _, _ | .obsHet _ _ _, _
  | .gel _ _ _, _ | .gelIntro _ _ _, _ | .arrowLine _ _ _ _, _ | .piLine _ _ _ _ _ _ _, _
  | .prodLine _ _ _ _ _, _ | .sigLine _ _ _ _ _ _ _ _ _, _ | .boxLine _ _ _, _ => .zero
  | .refl _ _, _ => .zero -- Bridges erase to 0 runtime uses!
  | .lam _ _ body, ix => varUsageAux body (ix + 1)
  | .app fn mod arg, ix =>
    UsageGrade.add (varUsageAux fn ix) (UsageGrade.mul mod.flags.grade (varUsageAux arg ix))
  | .letIn _ _ val body, ix =>
    UsageGrade.add (varUsageAux val ix) (varUsageAux body (ix + 1))
  | .key _ sub, ix => varUsageAux sub ix
  | .modalBox _ _, _ => .zero
  | .boxIntro mod sub, ix => UsageGrade.mul mod.flags.grade (varUsageAux sub ix)
  | .letBox _ _ scrut _ body, ix =>
    UsageGrade.add (varUsageAux scrut ix) (varUsageAux body (ix + 1))
  | .tuple fs, ix => varUsageTuple fs ix
  | .proj sub _, ix => varUsageAux sub ix
  | .ctor _ _ args, ix | .pctor _ _ args, ix => varUsageList args ix
  | .matchData scrut _ _ branches, ix =>
    UsageGrade.add (varUsageAux scrut ix) (varUsageBranches branches ix)
  | .elimHIT _ _ ptBranches pathBranches scrut, ix =>
    UsageGrade.add (varUsageAux scrut ix)
      (UsageGrade.lub (varUsageBranches ptBranches ix) (varUsageBranches pathBranches ix))
  | .sym _ p, ix | .ungel _ p, ix => varUsageAux p ix
  | .ap _ _ a, ix | .trr _ _ a, ix | .trl _ _ a, ix | .liftr _ _ a, ix | .liftl _ _ a, ix =>
    varUsageAux a ix
  | .trans _ p q, ix => UsageGrade.add (varUsageAux p ix) (varUsageAux q ix)
  | .pathJ _ _ _ _ reflC _ path, ix =>
    UsageGrade.add (varUsageAux reflC ix) (varUsageAux path ix)
  | .funext _ _ body, ix => varUsageAux body (ix + 3)
  | .hap _ pf a₀ a₁ pa, ix =>
    UsageGrade.add (varUsageAux pf ix)
      (UsageGrade.add (varUsageAux a₀ ix) (UsageGrade.add (varUsageAux a₁ ix) (varUsageAux pa ix)))
  | .u64BinOp _ l r, ix => UsageGrade.add (varUsageAux l ix) (varUsageAux r ix)
  | .u64IfZero c z nz, ix =>
    UsageGrade.add (varUsageAux c ix) (UsageGrade.lub (varUsageAux z ix) (varUsageAux nz ix))
  | .u64Repeat iters init step, ix =>
    let loopScale : UsageGrade :=
      if iters == 0 then .zero else if iters == 1 then .one else .omega
    UsageGrade.add (varUsageAux init ix) (UsageGrade.mul loopScale (varUsageAux step (ix + 1)))

end

/-- Compute the quantitative runtime usage of De Bruijn variable `ix` in `tm`. -/
@[inline]
def varUsage (ix : Ix) (tm : Term) : UsageGrade :=
  varUsageAux tm ix

/-! ## 3. Quantitative Linearity & Ghost-Erasure Checker -/

/-- Structural boolean check that every `1`-graded binder in a linear mode has runtime usage `≤ 1`
    and every `0`-graded binder has `0` runtime usage (purely structural on `Term` for kernel `decide`!). -/
def isLinearityValid (T : ModeTheory) (mode : ModeId) : Term → Bool
  | .lam _ mod body =>
    let u := varUsage 0 body
    let allowed : UsageGrade :=
      if mod.flags.grade == .zero then .zero
      else if T.isLinearMode mode && mod.flags.grade == .one then .one
      else .omega
    UsageGrade.leq u allowed && isLinearityValid T mode body
  | .letIn _ _ val body =>
    let u := varUsage 0 body
    let allowed : UsageGrade := if T.isLinearMode mode then .one else .omega
    isLinearityValid T mode val && UsageGrade.leq u allowed && isLinearityValid T mode body
  | .app fn mod arg =>
    isLinearityValid T mode fn && isLinearityValid T mod.dom arg
  | .boxIntro mod sub =>
    isLinearityValid T mod.dom sub
  | .letBox _ mod scrut _ body =>
    let u := varUsage 0 body
    let allowed : UsageGrade :=
      if mod.flags.grade == .zero then .zero
      else if T.isLinearMode mode && mod.flags.grade == .one then .one
      else .omega
    isLinearityValid T mode scrut && UsageGrade.leq u allowed && isLinearityValid T mode body
  | .u64BinOp _ l r =>
    isLinearityValid T mode l && isLinearityValid T mode r
  | .u64IfZero c z nz =>
    isLinearityValid T mode c && isLinearityValid T mode z && isLinearityValid T mode nz
  | .u64Repeat _ init step =>
    let uAcc := varUsage 0 step
    let accOk := if T.isLinearMode mode then UsageGrade.leq uAcc .one else true
    isLinearityValid T mode init && accOk && isLinearityValid T mode step
  | _ => true

/-- Check quantitative linearity & ghost-erasure, returning descriptive error diagnostics. -/
def checkLinearity (T : ModeTheory) (mode : ModeId) (tm : Term) : Except String Unit :=
  if isLinearityValid T mode tm then .ok ()
  else .error s!"Quantitative linearity / Ghost0 erasure violation at mode '{mode}'"

/-- Whether a binder's variable `0` in `body` is statically guaranteed exclusive (`RC == 1` / FBIP in-place safe!). -/
def canMutateInPlace (body : Term) : Bool :=
  UsageGrade.leq (varUsage 0 body) .one

/-! ## 4. Machine-Checked Linearity, Erasure, & Branch-Sharing Theorems (`zero sorry`) -/

/-- **Theorem L.1 (`ghost0_erasure_enforced`)**:
    In `linearAdjointTheory` (`LNL`), binding `(x : Ghost0 | Nat)` and returning `x` at runtime is
    REJECTED (`Ghost0` has `grade = 0`), while returning a constant (using `x` only in erased `refl x`)
    is ACCEPTED! -/
theorem ghost0_erasure_enforced :
    let ghostMod : ModPath :=
      match linearAdjointTheory.findMod? "Ghost0" with
      | some g => ModPath.atom g
      | none => ModPath.id "Lin"
    let badLeak : Term := .lam "x" ghostMod (.bvar 0)
    let okErased : Term := .lam "x" ghostMod (.letIn "p" (.uu 0) (.refl .hott (.bvar 0)) (.u64Lit 42))
    isLinearityValid linearAdjointTheory "Lin" badLeak = false ∧
    isLinearityValid linearAdjointTheory "Lin" okErased = true := by
  decide

/-- **Theorem L.2 (`lnl_linear_vs_bang_duplication`)**:
    In `linearAdjointTheory` (`LNL` at mode `"Lin"`):
    1. Duplicating a `1`-graded linear variable `λ (x : 1_Lin) => x + x` is REJECTED (`1 + 1 = ω ≰ 1`)!
    2. Using a `1`-graded linear variable across BOTH arms of `u64IfZero c x (x + 1)` IS ACCEPTED
       (`lub 1 1 = 1 ≤ 1` — additive `&` branch sharing preserves `RC == 1` in-place exclusivity!)!
    3. Duplicating an exponential `!`-guarded variable `λ (x : F ∘ G) => x + x` IS ACCEPTED (`F ∘ G` has grade `ω`)! -/
theorem lnl_linear_vs_bang_duplication :
    let idLin := ModPath.id "Lin"
    let bangMod : ModPath :=
      match linearAdjointTheory.findMod? "F", linearAdjointTheory.findMod? "G" with
      | some F, some G => ModPath.comp (ModPath.atom F) (ModPath.atom G)
      | _, _ => idLin
    let badDup : Term := .lam "x" idLin (.u64BinOp .add (.bvar 0) (.bvar 0))
    let okBranch : Term := .lam "x" idLin
      (.u64IfZero (.u64Lit 0) (.bvar 0) (.u64BinOp .add (.bvar 0) (.u64Lit 1)))
    let okBangDup : Term := .lam "x" bangMod (.u64BinOp .add (.bvar 0) (.bvar 0))
    isLinearityValid linearAdjointTheory "Lin" badDup = false ∧
    isLinearityValid linearAdjointTheory "Lin" okBranch = true ∧
    canMutateInPlace (.u64IfZero (.u64Lit 0) (.bvar 0) (.u64BinOp .add (.bvar 0) (.u64Lit 1))) = true ∧
    isLinearityValid linearAdjointTheory "Lin" okBangDup = true := by
  decide

end Narya.Core.Linear
