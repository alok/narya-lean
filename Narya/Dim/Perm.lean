/-
  Narya.Dim.Perm — Colored Dimension Permutations & Cross-Direction Interchange

  Multi-directional generalization of OCaml Narya's `lib/dim/perm.ml` and
  `lib/util/word.ml` (`permute`).

  Key mathematical property (Open Problem 1 resolution):
  `Perm m n` is a bijection of axes preserving each axis's direction color `g : Dir`.
  Consequently:
  1. Within a single direction (e.g. `e, e`), `swapAxes Dir.hott Dir.hott m` is
     Narya's symmetry operator `sym` for Eckmann–Hilton and higher cubes.
  2. Across *distinct* directions (e.g. HoTT `e` and Parametricity `p` or
     Displayed `d`), `swapAxes Dir.hott (Dir.param 2) m` is the **interchange
     isomorphism** witnessing that bridges of paths are canonically paths of bridges!
-/
import Narya.Dim.SDeg

namespace Narya.Dim

/-- Result of commuting two insertions `DimInsert g₁ x y` and `DimInsert h₁ y z`
    into `DimInsert h₁ x w` followed by `DimInsert g₁ w z`. -/
structure PushInsertResult (g₁ h₁ : Dir) (x z : DimCtx) : Type where
  {w : DimCtx}
  insH : DimInsert h₁ x w
  insG : DimInsert g₁ w z
  deriving Repr

/-- Push an inner insertion `DimInsert g₁ x y` past an outer insertion `DimInsert h₁ y z`. -/
def pushInsert {g₁ h₁ : Dir} {x y z : DimCtx}
    (i₁ : DimInsert g₁ x y) (i₂ : DimInsert h₁ y z) : PushInsertResult g₁ h₁ x z :=
  match i₂ with
  | .now => .mk .now (.later i₁)
  | .later i₂' =>
    match i₁ with
    | .now => .mk i₂' .now
    | .later i₁' =>
      match pushInsert i₁' i₂' with
      | .mk j₁ j₂ => .mk (.later j₁) (.later j₂)

/-- Color-preserving permutation of dimension axes `m` onto `n`. -/
inductive Perm : DimCtx → DimCtx → Type where
  | zero : Perm [] []
  | suc {g : Dir} {a b c : DimCtx} (p : Perm a b) (ins : DimInsert g a c) :
      Perm c (g :: b)
  deriving Repr

namespace Perm

/-- Identity permutation on `n`. -/
def id : (n : DimCtx) → Perm n n
  | [] => .zero
  | _ :: n => .suc (id n) .now

/-- Boolean test whether a permutation is the syntactic identity (`now` at every step). -/
def isId {m n : DimCtx} : Perm m n → Bool
  | .zero => true
  | .suc p .now => p.isId
  | .suc _ (.later _) => false

/-- Swap the two outermost axes `g₁` and `g₂` (`sym` when `g₁ = g₂`, cross-direction
    interchange when `g₁ ≠ g₂`). -/
def swapAxes (g₁ g₂ : Dir) (m : DimCtx) : Perm (g₁ :: g₂ :: m) (g₂ :: g₁ :: m) :=
  .suc (.suc (id m) .now) (.later .now)

/-- Extract the action of `Perm m n` on a chosen codomain insertion `DimInsert g npred n`. -/
structure ExtractResult (g : Dir) (m npred : DimCtx) : Type where
  {mpred : DimCtx}
  p : Perm mpred npred
  ins : DimInsert g mpred m
  deriving Repr

def extract {g : Dir} {m npred n : DimCtx}
    (perm : Perm m n) (ins : DimInsert g npred n) : ExtractResult g m npred :=
  match ins with
  | .now =>
    match perm with
    | .suc p insA => .mk p insA
  | .later insInner =>
    match perm with
    | .suc p insOuter =>
      match extract p insInner with
      | .mk p' insMid =>
        match pushInsert insMid insOuter with
        | .mk insH insG => .mk (.suc p' insH) insG

/-- Applicative composition of colored permutations (`comp q p = q ∘ p`). -/
def comp {a b c : DimCtx} : Perm b c → Perm a b → Perm a c
  | .zero, .zero => .zero
  | .suc q insB, p =>
    match extract p insB with
    | .mk p' insA => .suc (comp q p') insA

/-- Co-insert a generator at an arbitrary codomain position (`perm_with_extra` in OCaml). -/
def coinsert {g : Dir} {a b bsuc : DimCtx} :
    Perm a b → DimInsert g b bsuc → Perm (g :: a) bsuc
  | p, .now => .suc p .now
  | .suc p insA, .later insB =>
    .suc (coinsert p insB) (.later insA)

/-- Inverse of a colored permutation (`perm_inv`). -/
def inv {a b : DimCtx} : Perm a b → Perm b a
  | .zero => .zero
  | .suc p insA => coinsert (inv p) insA

/-! ### Preservation & Category/Interchange Theorems (`zero sorry`) -/

theorem length_eq {m n : DimCtx} (p : Perm m n) : m.length = n.length := by
  induction p with
  | zero => rfl
  | suc _ ins ih =>
    rw [DimInsert.length_eq ins, ih]
    rfl

/-- Every permutation preserves the exact count of every direction generator `q : Dir`. -/
theorem countDir_eq {m n : DimCtx} (p : Perm m n) (q : Dir) :
    DimCtx.countDir m q = DimCtx.countDir n q := by
  induction p with
  | zero => rfl
  | suc _ ins ih =>
    rw [DimInsert.countDir_eq ins q, ih]
    simp only [DimCtx.countDir, List.countP_cons]

@[simp]
theorem extract_now {g : Dir} {a b c : DimCtx} (p : Perm a b) (ins : DimInsert g a c) :
    extract (.suc p ins) .now = .mk p ins := rfl

@[simp]
theorem extract_later {g h : Dir} {a b c npred : DimCtx}
    (p : Perm a b) (insOuter : DimInsert h a c) (insInner : DimInsert g npred b) :
    extract (.suc p insOuter) (.later insInner) =
      ⟨.suc (extract p insInner).p (pushInsert (extract p insInner).ins insOuter).insH,
       (pushInsert (extract p insInner).ins insOuter).insG⟩ := rfl

@[simp]
theorem id_comp {a b : DimCtx} (p : Perm a b) :
    comp (id b) p = p := by
  induction p with
  | zero => rfl
  | suc p' ins ih =>
    simp only [id, comp, extract_now]
    rw [ih]

@[simp]
theorem pushInsert_now {g₁ h₁ : Dir} {x y : DimCtx} (i₁ : DimInsert g₁ x y) :
    pushInsert i₁ (DimInsert.now (g := h₁)) = ⟨.now, .later i₁⟩ := by
  cases i₁ <;> rfl

@[simp]
theorem pushInsert_now_later {g₁ h₁ : Dir} {x z : DimCtx} (i₂ : DimInsert h₁ x z) :
    pushInsert (DimInsert.now (g := g₁)) (.later i₂) = ⟨i₂, .now⟩ := by
  cases i₂ <;> rfl

theorem extract_id {g : Dir} {n npred : DimCtx} (ins : DimInsert g npred n) :
    extract (id n) ins = .mk (id npred) ins := by
  induction ins with
  | now => rfl
  | @later h m msuc ins' ih =>
    simp only [id, extract]
    rw [ih, pushInsert_now]

@[simp]
theorem comp_id {a b : DimCtx} (p : Perm a b) :
    comp p (id a) = p := by
  induction p with
  | zero => rfl
  | suc p' ins ih =>
    simp only [comp]
    rw [extract_id]
    simp only [ih]

/-- **Multi-Directional Interchange Involution Theorem**:
    Swapping any two axes `g₁` and `g₂` (whether identical, giving HoTT `sym² = id`,
    or distinct, giving HoTT × Parametricity / Display interchange) twice is
    provably the identity permutation! -/
theorem swapAxes_involutive (g₁ g₂ : Dir) (m : DimCtx) :
    comp (swapAxes g₂ g₁ m) (swapAxes g₁ g₂ m) = id (g₁ :: g₂ :: m) := by
  simp only [swapAxes, comp, extract_later, extract_now, id_comp, id]
  rfl

theorem inv_swapAxes (g₁ g₂ : Dir) (m : DimCtx) :
    inv (swapAxes g₁ g₂ m) = swapAxes g₂ g₁ m := by
  have h : ∀ k : DimCtx, inv (id k) = id k := by
    intro k
    induction k with
    | nil => rfl
    | cons d ds ih => simp [id, inv, ih, coinsert]
  simp only [swapAxes, inv, coinsert, h m]

end Perm

end Narya.Dim
