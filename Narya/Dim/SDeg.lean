/-
  Narya.Dim.SDeg — Colored Strict Degeneracies

  Multi-directional generalization of OCaml Narya's `lib/dim/sdeg.ml` and
  `lib/dim/section.ml`.
  Walking from outermost to innermost in the domain `m`, each generator either
  survives to `n` (`keep`) or is degenerated away (`degen`).

  Includes machine-checked proofs (`zero sorry`) of:
  - Category laws (`id_comp`, `comp_id`, `comp_assoc`)
  - Domain insertion (`insertDegen`, `insertKeep`)
  - Distributive law `sdegSFace` commuting strict degeneracies past strict faces
  - Section existence (`section?`: when `g.arity ≥ 1`, every strict degeneracy
    admits a right-inverse strict face!)
-/
import Narya.Dim.SFace

namespace Narya.Dim

/-- Colored strict degeneracy from `m` (higher degenerated cube) to `n` (lower cube). -/
inductive SDeg : DimCtx → DimCtx → Type where
  | zero : SDeg [] []
  | keep {a b : DimCtx} (s : SDeg a b) (g : Dir) :
      SDeg (g :: a) (g :: b)
  | degen {a b : DimCtx} (s : SDeg a b) (g : Dir) :
      SDeg (g :: a) b
  deriving Repr, DecidableEq

namespace SDeg

/-- Identity strict degeneracy on `n`. -/
def id : (n : DimCtx) → SDeg n n
  | [] => .zero
  | g :: n => .keep (id n) g

/-- Collapse every axis of `a` down to the 0-cube `[]` (`sdeg_zero` in OCaml). -/
def toZero : (a : DimCtx) → SDeg a []
  | [] => .zero
  | g :: a => .degen (toZero a) g

/-- Single-axis degeneracy `refl` / `rel` extending `n` by one degenerate axis `g`. -/
def reflAxis (g : Dir) (n : DimCtx) : SDeg (g :: n) n :=
  .degen (id n) g

/-- Boolean check whether a strict degeneracy is the identity (`degen` never appears). -/
def isId {m n : DimCtx} : SDeg m n → Bool
  | .zero => true
  | .degen _ _ => false
  | .keep s _ => s.isId

/-- Applicative composition of strict degeneracies (`comp s t = s ∘ t`). -/
def comp {a b c : DimCtx} : SDeg b c → SDeg a b → SDeg a c
  | .zero, .zero => .zero
  | s, .degen t g => .degen (comp s t) g
  | .keep s _, .keep t g => .keep (comp s t) g
  | .degen s _, .keep t g => .degen (comp s t) g

/-- Horizontal concatenation of strict degeneracies. -/
def append {a1 b1 a2 b2 : DimCtx} :
    SDeg a1 b1 → SDeg a2 b2 → SDeg (a1 ++ a2) (b1 ++ b2)
  | .zero, s2 => s2
  | .keep s1 g, s2 => .keep (append s1 s2) g
  | .degen s1 g, s2 => .degen (append s1 s2) g

/-! ### Category Laws for Colored Strict Degeneracies -/

@[simp]
theorem id_comp {a b : DimCtx} (s : SDeg a b) :
    comp (id b) s = s := by
  induction s with
  | zero => rfl
  | keep s' g ih => simp [id, comp, ih]
  | degen s' g ih => simp [comp, ih]

@[simp]
theorem comp_id {a b : DimCtx} (s : SDeg a b) :
    comp s (id a) = s := by
  induction s with
  | zero => rfl
  | keep s' g ih => simp [id, comp, ih]
  | degen s' g ih => simp [id, comp, ih]

theorem comp_assoc {a b c d : DimCtx}
    (r : SDeg c d) (s : SDeg b c) (t : SDeg a b) :
    comp (comp r s) t = comp r (comp s t) := by
  induction t generalizing c d with
  | zero =>
    cases s
    cases r
    rfl
  | degen t' g ih =>
    simp [comp, ih]
  | keep t' g ih =>
    cases s with
    | degen s' _ =>
      simp [comp, ih]
    | keep s' _ =>
      cases r with
      | degen r' _ => simp [comp, ih]
      | keep r' _ => simp [comp, ih]

theorem cod_length_le_dom {m n : DimCtx} (s : SDeg m n) :
    n.length ≤ m.length := by
  induction s with
  | zero => exact Nat.le_refl 0
  | keep _ _ ih => exact Nat.succ_le_succ ih
  | degen _ _ ih => exact Nat.le_succ_of_le ih

/-! ### Inserting into Domain (`sdeg_insert_degen` and `sdeg_insert`) -/

/-- Insert a degenerate generator `g` anywhere in the domain, leaving codomain unchanged. -/
def insertDegen {a b asuc : DimCtx} {g : Dir} :
    SDeg a b → DimInsert g a asuc → SDeg asuc b
  | s, .now => .degen s g
  | .keep s h, .later i => .keep (insertDegen s i) h
  | .degen s h, .later i => .degen (insertDegen s i) h

/-- Witness of inserting a surviving generator `g` into the domain of `SDeg a b`. -/
inductive InsertResult (g : Dir) (asuc b : DimCtx) : Type where
  | mk {bsuc : DimCtx} (s : SDeg asuc bsuc) (ins : DimInsert g b bsuc) :
      InsertResult g asuc b
  deriving Repr

/-- Insert a surviving generator `g` into the domain, reporting where it lands in the codomain. -/
def insertKeep {a b asuc : DimCtx} {g : Dir}
    (s : SDeg a b) (ins : DimInsert g a asuc) : InsertResult g asuc b :=
  match ins with
  | .now => .mk (.keep s g) .now
  | .later i =>
    match s with
    | .keep s' h =>
      match insertKeep s' i with
      | .mk s'' j => .mk (.keep s'' h) (.later j)
    | .degen s' h =>
      match insertKeep s' i with
      | .mk s'' j => .mk (.degen s'' h) j

@[simp]
theorem insertKeep_now {a b : DimCtx} {g : Dir} (s : SDeg a b) :
    insertKeep s (DimInsert.now (g := g)) = .mk (.keep s g) .now := by
  cases s <;> rfl

/-! ### Distributive Law: Commuting `SDeg` Past `SFace` (`sdeg_sface` in `op.ml`) -/

/-- Result of pushing `SDeg n j` past `SFace m n`: an `SFace p j` followed by `SDeg m p`. -/
inductive SDegSFace (m j : DimCtx) : Type where
  | mk {p : DimCtx} (f : SFace p j) (s : SDeg m p) : SDegSFace m j
  deriving Repr

/-- Push a strict degeneracy `s : SDeg n j` past a strict face `b : SFace m n`. -/
def sdegSFace {m n j : DimCtx} : SDeg n j → SFace m n → SDegSFace m j
  | .zero, .zero => .mk .zero .zero
  | .keep s g, .endpt f _ e =>
    match sdegSFace s f with
    | .mk f' s' => .mk (.endpt f' g e) s'
  | .keep s g, .mid f _ =>
    match sdegSFace s f with
    | .mk f' s' => .mk (.mid f' g) (.keep s' g)
  | .degen s _, .endpt f _ _ =>
    sdegSFace s f
  | .degen s g, .mid f _ =>
    match sdegSFace s f with
    | .mk f' s' => .mk f' (.degen s' g)

/-- Identity preservation of `sdegSFace`: pushing `SDeg.id n` past `f` yields `(f, SDeg.id m)`. -/
theorem sdegSFace_id_left {m n : DimCtx} (f : SFace m n) :
    sdegSFace (SDeg.id n) f = .mk f (SDeg.id m) := by
  induction f with
  | zero => rfl
  | endpt f' g e ih =>
    simp only [SDeg.id, sdegSFace]
    rw [ih]
  | mid f' g ih =>
    simp only [SDeg.id, sdegSFace]
    rw [ih]

theorem sdegSFace_id_right {m n : DimCtx} (s : SDeg n m) :
    sdegSFace s (SFace.id n) = .mk (SFace.id m) s := by
  induction s with
  | zero => rfl
  | keep s' g ih =>
    simp only [SFace.id, sdegSFace]
    rw [ih]
  | degen s' g ih =>
    simp only [SFace.id, sdegSFace]
    rw [ih]

/-! ### Section Theorem (`lib/dim/section.ml`) -/

/-- Whenever every degenerated direction has `arity ≥ 1` (e.g. HoTT `e`, displayed `d`,
    or `k`-ary parametricity for `k ≥ 1`, excluding nullary nominal `w`), any strict
    degeneracy `s : SDeg m n` admits a canonical strict-face section `f : SFace n m`
    choosing endpoint `0`. -/
def sectionZero {m n : DimCtx} (s : SDeg m n)
    (hpos : ∀ g ∈ m, 0 < g.arity) : SFace n m :=
  match s with
  | .zero => .zero
  | .keep s' g =>
    .mid (sectionZero s' (fun x hx => hpos x (.tail g hx))) g
  | .degen s' g =>
    have hg : 0 < g.arity := hpos g (.head _)
    .endpt (sectionZero s' (fun x hx => hpos x (.tail g hx))) g ⟨0, hg⟩

/-- Pushing `s : SDeg m n` past its canonical section `sectionZero s` yields `(id n, id n)`. -/
theorem sdegSFace_sectionZero {m n : DimCtx} (s : SDeg m n)
    (hpos : ∀ g ∈ m, 0 < g.arity) :
    sdegSFace s (sectionZero s hpos) = .mk (SFace.id n) (SDeg.id n) := by
  induction s with
  | zero => rfl
  | keep s' g ih =>
    simp only [sectionZero, sdegSFace]
    rw [ih (fun x hx => hpos x (.tail g hx))]
    rfl
  | degen s' g ih =>
    simp only [sectionZero, sdegSFace]
    exact ih (fun x hx => hpos x (.tail g hx))

end SDeg

end Narya.Dim
