/-
  Narya.Dim.Op — General Colored Degeneracies & Cubical Operators

  Multi-directional generalization of OCaml Narya's `lib/dim/deg.ml` and `lib/dim/op.ml`.
  - Every general degeneracy `Deg m n` factors canonically as `SDeg m k` followed by `Perm k n`.
  - Every general cubical operator `Op m n` factors canonically as `Deg m p` followed by `SFace p n`
    (stored in applicative order as `SFace p n × Deg m p`, matching `Op (f, s)` in `op.ml`).
  - Composition of cubical operators uses the distributive law `degSFace`, commuting
    `Deg n q` past `SFace r n` via `SDeg.sdegSFace` and `SFace.residual`!
-/
import Narya.Dim.Perm

namespace Narya.Dim

/-- General colored degeneracy `Deg m n`: a strict degeneracy `SDeg m k` followed by `Perm k n`. -/
inductive Deg : DimCtx → DimCtx → Type where
  | mk {m k n : DimCtx} (s : SDeg m k) (p : Perm k n) : Deg m n
  deriving Repr

namespace Deg

/-- Identity degeneracy on `n`. -/
def id (n : DimCtx) : Deg n n :=
  .mk (SDeg.id n) (Perm.id n)

/-- Collapse every axis of `m` to `[]`. -/
def toZero (m : DimCtx) : Deg m [] :=
  .mk (SDeg.toZero m) .zero

/-- Embed a strict degeneracy as a `Deg`. -/
def ofSDeg {m n : DimCtx} (s : SDeg m n) : Deg m n :=
  .mk s (Perm.id n)

/-- Embed a permutation as a `Deg`. -/
def ofPerm {m n : DimCtx} (p : Perm m n) : Deg m n :=
  .mk (SDeg.id m) p

/-- Boolean identity check (powers the 96.2% short-circuit fast path from `PROFILING.md`!). -/
def isId {m n : DimCtx} : Deg m n → Bool
  | .mk s p => s.isId && p.isId

/-- Extend `Deg m n` by one surviving axis `g` inserted into `m` at `ins` (`deg_suc` in OCaml). -/
def suc {g : Dir} {m msuc n : DimCtx} :
    Deg m n → DimInsert g m msuc → Deg msuc (g :: n)
  | .mk s p, ins =>
    match SDeg.insertKeep s ins with
    | .mk s' insK => .mk s' (.suc p insK)

/-- Commute `Perm b c` past `SDeg a b` (`perm_sdeg` distributive law). -/
inductive PermSDegResult (a c : DimCtx) : Type where
  | mk {b' : DimCtx} (s : SDeg b' c) (p : Perm a b') : PermSDegResult a c
  deriving Repr

/-- Uninsert a surviving codomain axis from `SDeg a bsuc` (`sdeg_uninsert` in `sdeg.ml`). -/
inductive UninsertResult (g : Dir) (a b : DimCtx) : Type where
  | mk {apred : DimCtx} (s : SDeg apred b) (ins : DimInsert g apred a) :
      UninsertResult g a b

def uninsertSDeg {g : Dir} {a b bsuc : DimCtx} :
    SDeg a bsuc → DimInsert g b bsuc → UninsertResult g a b
  | .keep s _, .now => .mk s .now
  | .keep s h, .later i =>
    match uninsertSDeg s i with
    | .mk s' j => .mk (.keep s' h) (.later j)
  | .degen s h, i =>
    match uninsertSDeg s i with
    | .mk s' j => .mk (.degen s' h) (.later j)

/-- Commute a strict degeneracy `SDeg b c` past a permutation `Perm a b`. -/
def sdegPerm {a b c : DimCtx} : SDeg b c → Perm a b → Deg a c
  | .zero, .zero => .mk .zero .zero
  | .degen s _, .suc p insA =>
    match sdegPerm s p with
    | .mk s' p' => .mk (SDeg.insertDegen s' insA) p'
  | .keep s _, .suc p insA =>
    match sdegPerm s p with
    | .mk s' p' =>
      match SDeg.insertKeep s' insA with
      | .mk s'' insK => .mk s'' (.suc p' insK)

/-- Applicative composition of general degeneracies (`comp d1 d2 = d1 ∘ d2`). -/
def comp {a b c : DimCtx} : Deg b c → Deg a b → Deg a c
  | .mk s1 p1, .mk s2 p2 =>
    match sdegPerm s1 p2 with
    | .mk s1' p2' => .mk (SDeg.comp s1' s2) (Perm.comp p1 p2')

theorem sdegPerm_id_left {a b : DimCtx} (p : Perm a b) :
    sdegPerm (SDeg.id b) p = .mk (SDeg.id a) p := by
  induction p with
  | zero => rfl
  | suc p' ins ih =>
    simp only [SDeg.id, sdegPerm]
    rw [ih]
    dsimp only
    have hKeep : ∀ {x xsuc : DimCtx} {g : Dir} (i : DimInsert g x xsuc),
        SDeg.insertKeep (SDeg.id x) i = .mk (SDeg.id xsuc) i := by
      intro x xsuc g i
      induction i with
      | now => simp [SDeg.insertKeep_now, SDeg.id]
      | @later h m msuc i' ihIns =>
        have hStep : SDeg.insertKeep (SDeg.id (h :: m)) (.later i') =
            match SDeg.insertKeep (SDeg.id m) i' with
            | .mk s'' j => .mk (.keep s'' h) (.later j) := by
          cases i' <;> rfl
        rw [hStep, ihIns]
        rfl
    rw [hKeep ins]

@[simp]
theorem id_comp {a b : DimCtx} (d : Deg a b) :
    comp (id b) d = d := by
  cases d with
  | mk s p =>
    simp only [id, comp]
    rw [sdegPerm_id_left]
    simp only [SDeg.id_comp, Perm.id_comp]

end Deg

/-- General colored cubical operator `Op m n`: `Deg m p` followed by `SFace p n`. -/
inductive Op : DimCtx → DimCtx → Type where
  | mk {m p n : DimCtx} (f : SFace p n) (d : Deg m p) : Op m n
  deriving Repr

namespace Op

/-- Identity cubical operator on `n`. -/
def id (n : DimCtx) : Op n n :=
  .mk (SFace.id n) (Deg.id n)

/-- Embed a strict face into `Op`. -/
def ofSFace {m n : DimCtx} (f : SFace m n) : Op m n :=
  .mk f (Deg.id m)

/-- Embed a degeneracy into `Op`. -/
def ofDeg {m n : DimCtx} (d : Deg m n) : Op m n :=
  .mk (SFace.id n) d

/-- Fast boolean check for the identity cubical operator. -/
def isId {m n : DimCtx} : Op m n → Bool
  | .mk f d => f.isId && d.isId

/-- Push `Perm n k` past `SFace m n` (`perm_sface_op` in `op.ml:34-43`). -/
def permSFace {m n k : DimCtx} : Perm n k → SFace m n → Op m k
  | .zero, b => .mk b (Deg.id m)
  | .suc p ins, b =>
    match SFace.residual b ins with
    | .endpt f e =>
      match permSFace p f with
      | .mk f' d' => .mk (.endpt f' _ e) d'
    | .mid f l =>
      match permSFace p f with
      | .mk f' d' => .mk (.mid f' _) (Deg.suc d' l)

/-- **Distributive Law (`degSFace`)**: Push a general degeneracy `Deg n k` past a
    strict face `SFace m n` to obtain `Op m k` (`deg_sface` in `op.ml:45-49`). -/
def degSFace {m n k : DimCtx} : Deg n k → SFace m n → Op m k
  | .mk s p, b =>
    match SDeg.sdegSFace s b with
    | .mk b' s' =>
      match permSFace p b' with
      | .mk f (.mk s'' p') => .mk f (.mk (SDeg.comp s'' s') p')

/-- Applicative composition of general cubical operators (`comp a b = a ∘ b`). -/
def comp {k m n : DimCtx} : Op m n → Op k m → Op k n
  | .mk a b, .mk c d =>
    match degSFace b c with
    | .mk c' b' => .mk (SFace.comp a c') (Deg.comp b' d)

/-! ### Identity & Distributive Soundness Theorems (`zero sorry`) -/

theorem permSFace_id {m n : DimCtx} (f : SFace m n) :
    permSFace (Perm.id n) f = .mk f (Deg.id m) := by
  induction f with
  | zero => rfl
  | endpt f' g e ih =>
    simp only [Perm.id, permSFace, SFace.residual]
    rw [ih]
  | mid f' g ih =>
    simp only [Perm.id, permSFace, SFace.residual]
    rw [ih]
    dsimp only [Deg.id, Deg.suc]
    rw [SDeg.insertKeep_now]
    rfl

theorem degSFace_id_left {m n : DimCtx} (f : SFace m n) :
    degSFace (Deg.id n) f = .mk f (Deg.id m) := by
  simp only [Deg.id, degSFace]
  rw [SDeg.sdegSFace_id_left, permSFace_id]
  dsimp only [Deg.id]
  rw [SDeg.id_comp]

@[simp]
theorem id_comp {m n : DimCtx} (o : Op m n) :
    comp (id n) o = o := by
  cases o with
  | mk f d =>
    simp only [id, comp]
    rw [degSFace_id_left]
    simp only [SFace.id_comp, Deg.id_comp]

end Op

end Narya.Dim
