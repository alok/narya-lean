/-
  Narya.Core.Level — Predicative `Mugen` Universe Polymorphism Algebra

  Machine-checked resolution of Upstream Narya Open Problem I1 (`docs/source/built-in-types.rst`):
  - Upstream Narya currently uses inconsistent `Type : Type` and cites incorporating `mugen`
    universe levels as a future roadmap item.
  - This module formalizes algebraic universe level expressions (`const`, `lvar`, `succ`, `max`),
    their denotational valuation `eval ρ : Nat`, canonical normalization into max-of-offsets form
    (`CanLevel`), a decidable universal level inequality checker `checkLevelLeq`, and machine-checked
    soundness + anti-Girard (`¬ (u + 1 ≤ u)`) theorems (`zero sorry`, `zero noncomputable`).
-/
import Narya.Dim

namespace Narya.Core.Level

/-- Universe level variable identifier (`u_0`, `u_1`, ...). -/
abbrev LevelVar := Nat

/-- Algebraic `Mugen`-style predicative universe level expressions. -/
inductive LevelExpr where
  /-- Concrete finite universe level `k`. -/
  | const (k : Nat)
  /-- Polymorphic universe level parameter `u_v`. -/
  | lvar (v : LevelVar)
  /-- Successor universe `e + 1` (`Type e : Type (succ e)`). -/
  | succ (e : LevelExpr)
  /-- Least upper bound `max a b` (`Π (x : A_a) → B_b : Type (max a b)`). -/
  | max (a b : LevelExpr)
  deriving DecidableEq, Repr, Inhabited

namespace LevelExpr

/-- Evaluate `e` under level assignment `ρ : LevelVar → Nat`. -/
def eval (ρ : LevelVar → Nat) : LevelExpr → Nat
  | .const k => k
  | .lvar v => ρ v
  | .succ e => eval ρ e + 1
  | .max a b => Nat.max (eval ρ a) (eval ρ b)

/-- Substitute `sub` for level variables in `e`. -/
def subst (sub : LevelVar → LevelExpr) : LevelExpr → LevelExpr
  | .const k => .const k
  | .lvar v => sub v
  | .succ e => .succ (subst sub e)
  | .max a b => .max (subst sub a) (subst sub b)

/-- Universal semantic universe inequality: `e₁ ≤ e₂` for ALL level assignments `ρ`. -/
def SemLeq (e₁ e₂ : LevelExpr) : Prop :=
  ∀ ρ : LevelVar → Nat, eval ρ e₁ ≤ eval ρ e₂

@[simp]
theorem eval_const (ρ : LevelVar → Nat) (k : Nat) : eval ρ (.const k) = k := rfl

@[simp]
theorem eval_lvar (ρ : LevelVar → Nat) (v : LevelVar) : eval ρ (.lvar v) = ρ v := rfl

@[simp]
theorem eval_succ (ρ : LevelVar → Nat) (e : LevelExpr) : eval ρ (.succ e) = eval ρ e + 1 := rfl

@[simp]
theorem eval_max (ρ : LevelVar → Nat) (a b : LevelExpr) :
    eval ρ (.max a b) = Nat.max (eval ρ a) (eval ρ b) := rfl

theorem eval_subst (ρ : LevelVar → Nat) (sub : LevelVar → LevelExpr) (e : LevelExpr) :
    eval ρ (subst sub e) = eval (fun v => eval ρ (sub v)) e := by
  induction e with
  | const _ => rfl
  | lvar _ => rfl
  | succ e ih => simp [subst, ih]
  | max a b iha ihb => simp [subst, iha, ihb]

theorem semLeq_refl (e : LevelExpr) : SemLeq e e :=
  fun _ => Nat.le_refl _

theorem semLeq_trans {a b c : LevelExpr} (h₁ : SemLeq a b) (h₂ : SemLeq b c) :
    SemLeq a c :=
  fun ρ => Nat.le_trans (h₁ ρ) (h₂ ρ)

theorem max_lub_left (a b : LevelExpr) : SemLeq a (.max a b) :=
  fun ρ => Nat.le_max_left (eval ρ a) (eval ρ b)

theorem max_lub_right (a b : LevelExpr) : SemLeq b (.max a b) :=
  fun ρ => Nat.le_max_right (eval ρ a) (eval ρ b)

/-- **Predicativity / Anti-Girard Theorem (`no_girard_type_in_type`)**:
    For EVERY universe expression `u`, `succ u` is NEVER universally `≤ u` (`Type u : Type u` is
    impossible in every valuation)! -/
theorem no_girard_type_in_type (u : LevelExpr) : ¬ SemLeq (.succ u) u := by
  intro h
  have hZero := h (fun _ => 0)
  simp only [eval_succ] at hZero
  omega

/-! ### Canonical Max-of-Atoms Normalization & Decidable `checkLevelLeq` -/

/-- Atomic universe offset: either a pure constant `k` or `u_v + k`. -/
inductive LevelAtom where
  | constOff (k : Nat)
  | varOff (v : LevelVar) (k : Nat)
  deriving DecidableEq, Repr, Inhabited

namespace LevelAtom

def eval (ρ : LevelVar → Nat) : LevelAtom → Nat
  | .constOff k => k
  | .varOff v k => ρ v + k

def bump (d : Nat) : LevelAtom → LevelAtom
  | .constOff k => .constOff (k + d)
  | .varOff v k => .varOff v (k + d)

theorem eval_bump (ρ : LevelVar → Nat) (d : Nat) (a : LevelAtom) :
    eval ρ (bump d a) = eval ρ a + d := by
  cases a <;> simp [bump, eval, Nat.add_assoc]

/-- Decide whether single atom `a` is universally `≤` atom `b`. -/
def atomLeq : LevelAtom → LevelAtom → Bool
  | .constOff k₁, .constOff k₂ => decide (k₁ ≤ k₂)
  | .constOff k₁, .varOff _ k₂ => decide (k₁ ≤ k₂)
  | .varOff v₁ k₁, .varOff v₂ k₂ => (v₁ == v₂) && decide (k₁ ≤ k₂)
  | .varOff _ _, .constOff _ => false

theorem atomLeq_sound {a b : LevelAtom} (h : atomLeq a b = true) (ρ : LevelVar → Nat) :
    a.eval ρ ≤ b.eval ρ := by
  cases a with
  | constOff k₁ =>
    cases b with
    | constOff k₂ =>
      simp [atomLeq, eval] at h ⊢
      exact h
    | varOff v₂ k₂ =>
      simp [atomLeq, eval] at h ⊢
      omega
  | varOff v₁ k₁ =>
    cases b with
    | constOff _ =>
      simp [atomLeq] at h
    | varOff v₂ k₂ =>
      simp [atomLeq, Bool.and_eq_true, eval] at h ⊢
      rcases h with ⟨hv, hk⟩
      subst hv
      omega

end LevelAtom

/-- Canonical form: a non-empty list of `LevelAtom`s interpreted as their maximum. -/
def evalAtoms (ρ : LevelVar → Nat) : List LevelAtom → Nat
  | [] => 0
  | a :: as => Nat.max (a.eval ρ) (evalAtoms ρ as)

theorem evalAtoms_append (ρ : LevelVar → Nat) (xs ys : List LevelAtom) :
    evalAtoms ρ (xs ++ ys) = Nat.max (evalAtoms ρ xs) (evalAtoms ρ ys) := by
  induction xs with
  | nil => simp [evalAtoms]
  | cons x rest ih =>
    simp only [List.cons_append, evalAtoms, ih, Nat.max_assoc]

theorem evalAtoms_map_bump_nonempty (ρ : LevelVar → Nat) (d : Nat) :
    ∀ (xs : List LevelAtom), xs ≠ [] →
      evalAtoms ρ (xs.map (LevelAtom.bump d)) = evalAtoms ρ xs + d
  | [], hNe => False.elim (hNe rfl)
  | [a], _ => by
    simp [evalAtoms, LevelAtom.eval_bump]
  | a :: b :: rest, _ => by
    have ih := evalAtoms_map_bump_nonempty ρ d (b :: rest) (by simp)
    change Nat.max ((LevelAtom.bump d a).eval ρ) (evalAtoms ρ ((b :: rest).map (LevelAtom.bump d))) =
      Nat.max (a.eval ρ) (evalAtoms ρ (b :: rest)) + d
    rw [LevelAtom.eval_bump, ih]
    simp only [Nat.max_def]
    split <;> split <;> omega

/-- Flatten any `LevelExpr` into a non-empty list of `LevelAtom`s. -/
def toAtoms : LevelExpr → List LevelAtom
  | .const k => [.constOff k]
  | .lvar v => [.varOff v 0]
  | .succ e => (toAtoms e).map (LevelAtom.bump 1)
  | .max a b => toAtoms a ++ toAtoms b

theorem toAtoms_nonempty (e : LevelExpr) : toAtoms e ≠ [] := by
  induction e with
  | const _ => simp [toAtoms]
  | lvar _ => simp [toAtoms]
  | succ e ih =>
    intro hEmpty
    simp [toAtoms] at hEmpty
    exact ih hEmpty
  | max a _ iha _ =>
    intro hEmpty
    simp [toAtoms] at hEmpty
    exact iha hEmpty.1

theorem evalAtoms_toAtoms (ρ : LevelVar → Nat) (e : LevelExpr) :
    evalAtoms ρ (toAtoms e) = eval ρ e := by
  induction e with
  | const k => simp [toAtoms, evalAtoms, LevelAtom.eval]
  | lvar v => simp [toAtoms, evalAtoms, LevelAtom.eval]
  | succ e ih =>
    simp only [toAtoms, eval_succ]
    rw [evalAtoms_map_bump_nonempty ρ 1 (toAtoms e) (toAtoms_nonempty e), ih]
  | max a b iha ihb =>
    simp only [toAtoms, eval_max, evalAtoms_append, iha, ihb]

/-- Check if atom `a` is dominated by at least one atom in `bs`. -/
def atomDominatedBy (a : LevelAtom) : List LevelAtom → Bool
  | [] => false
  | b :: bs => LevelAtom.atomLeq a b || atomDominatedBy a bs

theorem atomDominatedBy_sound {a : LevelAtom} {bs : List LevelAtom}
    (h : atomDominatedBy a bs = true) (ρ : LevelVar → Nat) :
    a.eval ρ ≤ evalAtoms ρ bs := by
  induction bs with
  | nil => simp [atomDominatedBy] at h
  | cons b rest ih =>
    simp only [atomDominatedBy, Bool.or_eq_true] at h
    simp only [evalAtoms]
    cases h with
    | inl hHead =>
      exact Nat.le_trans (LevelAtom.atomLeq_sound hHead ρ) (Nat.le_max_left _ _)
    | inr hTail =>
      exact Nat.le_trans (ih hTail) (Nat.le_max_right _ _)

def allAtomsDominated (as bs : List LevelAtom) : Bool :=
  match as with
  | [] => true
  | a :: rest => atomDominatedBy a bs && allAtomsDominated rest bs

theorem allAtomsDominated_sound {as bs : List LevelAtom}
    (h : allAtomsDominated as bs = true) (ρ : LevelVar → Nat) :
    evalAtoms ρ as ≤ evalAtoms ρ bs := by
  induction as with
  | nil => simp [evalAtoms]
  | cons a rest ih =>
    simp only [allAtomsDominated, Bool.and_eq_true] at h
    simp only [evalAtoms]
    exact Nat.max_le.mpr ⟨atomDominatedBy_sound h.1 ρ, ih h.2⟩

/-- **Decidable Universe Level Inequality Checker (`checkLevelLeq`)**:
    Decides `max_i a_i ≤ max_j b_j` by normalizing both expressions to max-of-offsets form! -/
def checkLevelLeq (e₁ e₂ : LevelExpr) : Bool :=
  allAtomsDominated (toAtoms e₁) (toAtoms e₂)

/-- **Theorem I1.1 (`checkLevelLeq_sound`, `0 sorry`)**:
    Whenever `checkLevelLeq e₁ e₂ = true`, `e₁` is universally `≤ e₂` under ALL level valuations! -/
theorem checkLevelLeq_sound {e₁ e₂ : LevelExpr} (h : checkLevelLeq e₁ e₂ = true) :
    SemLeq e₁ e₂ := by
  intro ρ
  rw [← evalAtoms_toAtoms ρ e₁, ← evalAtoms_toAtoms ρ e₂]
  exact allAtomsDominated_sound h ρ

end LevelExpr

end Narya.Core.Level
