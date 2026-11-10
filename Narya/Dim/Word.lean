/-
  Narya.Dim.Word — Colored Dimension Contexts, Insertions, and Shuffles

  Generalizes OCaml Narya's `lib/util/word.ml` and `lib/dim/d.ml` from unary
  single-generator naturals to multi-directional words `DimCtx := List Dir`.
  Head (`g :: n`) represents the outermost dimension generator `(n, g) D.suc`.
-/
import Narya.Dim.Direction

namespace Narya.Dim

/-- A colored dimension context: a finite sequence of direction generators,
    ordered from outermost (head) to innermost (tail). -/
abbrev DimCtx : Type := List Dir

namespace DimCtx

/-- Dimension 0 (0-cube). -/
def zero : DimCtx := []

/-- Extend a dimension context on the outside with generator `g`. -/
def suc (n : DimCtx) (g : Dir) : DimCtx := g :: n

/-- Total dimension rank (number of cube axes). -/
def rank (n : DimCtx) : Nat := n.length

/-- Count how many axes belong to a specific direction `g`. -/
def countDir (n : DimCtx) (g : Dir) : Nat :=
  n.countP (· == g)

/-- True if every generator in `n` has arity 0 (purely nominal dimension). -/
def isNominalOnly (n : DimCtx) : Bool :=
  n.all (fun g => g.arity == 0)

theorem rank_zero : rank zero = 0 := rfl
theorem rank_suc (n : DimCtx) (g : Dir) : rank (suc n g) = rank n + 1 := rfl

end DimCtx

/-- `DimInsert g m msuc` witnesses inserting generator `g` into `m` to obtain `msuc`,
    preserving the relative order of all other generators in `m`.
    Direct multi-directional port of OCaml Narya's `('m, 'g, 'msuc) D.insert`. -/
inductive DimInsert (g : Dir) : DimCtx → DimCtx → Type where
  | now {m : DimCtx} : DimInsert g m (g :: m)
  | later {h : Dir} {m msuc : DimCtx} (ins : DimInsert g m msuc) :
      DimInsert g (h :: m) (h :: msuc)
  deriving Repr

namespace DimInsert

/-- Numerical index (0 = outermost) where `g` was inserted. -/
def index {g : Dir} {m msuc : DimCtx} : DimInsert g m msuc → Nat
  | .now => 0
  | .later i => i.index + 1

theorem length_eq {g : Dir} {m msuc : DimCtx} (ins : DimInsert g m msuc) :
    msuc.length = m.length + 1 := by
  induction ins with
  | now => rfl
  | later _ ih => simp [ih]

theorem countDir_eq {g : Dir} {m msuc : DimCtx} (ins : DimInsert g m msuc) (q : Dir) :
    DimCtx.countDir msuc q = DimCtx.countDir m q + (if g == q then 1 else 0) := by
  induction ins with
  | now =>
    simp only [DimCtx.countDir, List.countP_cons]
  | later _ ih =>
    simp only [DimCtx.countDir, List.countP_cons] at ih ⊢
    omega

end DimInsert

/-- `Shuffle a b ab` witnesses interleaving two dimension contexts `a` and `b`
    into `ab` while preserving the internal order of both `a` and `b`.
    Generalizes `lib/dim/shuffle.ml` to colored directions. -/
inductive Shuffle : DimCtx → DimCtx → DimCtx → Type where
  | zero : Shuffle [] [] []
  | left {g : Dir} {a b ab : DimCtx} (s : Shuffle a b ab) :
      Shuffle (g :: a) b (g :: ab)
  | right {g : Dir} {a b ab : DimCtx} (s : Shuffle a b ab) :
      Shuffle a (g :: b) (g :: ab)
  deriving Repr

namespace Shuffle

/-- Trivial shuffle corresponding to list append `a ++ b`. -/
def trivial : (a b : DimCtx) → Shuffle a b (a ++ b)
  | [], [] => .zero
  | [], g :: b => .right (trivial [] b)
  | g :: a, b => .left (trivial a b)

/-- Swap the two inputs of a shuffle without changing the interleaved output. -/
def symm {a b ab : DimCtx} : Shuffle a b ab → Shuffle b a ab
  | .zero => .zero
  | .left s => .right s.symm
  | .right s => .left s.symm

theorem symm_involutive {a b ab : DimCtx} (s : Shuffle a b ab) :
    s.symm.symm = s := by
  induction s with
  | zero => rfl
  | left _ ih => simp [symm, ih]
  | right _ ih => simp [symm, ih]

theorem length_eq {a b ab : DimCtx} (s : Shuffle a b ab) :
    ab.length = a.length + b.length := by
  induction s with
  | zero => rfl
  | left _ ih => simp [ih]; omega
  | right _ ih => simp [ih]; omega

end Shuffle

end Narya.Dim
