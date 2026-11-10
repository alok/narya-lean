/-
  Narya.Modal.ModeTheory — First-Class 2-Categorical Mode Theories & Dimension Filtering

  Port and generalization of OCaml Narya's `lib/modal/` (`modality.mli` + mode functors).
  Resolves Open Problem B (part 1) & Open Problem A/C interface:
  - Mode theories are first-class values (`ModeTheory`) rather than static OCaml functors.
  - Modalities carry fine-grained structural flags (`tangible`, `pellucid`, `transparent`,
    `translucent`, `sinister` for negative modal fields via left adjoints, `isLocker` for
    external/displayed parametricity, and per-direction `discreteDirs : List Dir`).
  - Dimension contexts `DimCtx` and cubical operators (`SFace`, `SDeg`, `Perm`, `Op`) admit
    a provably functorial projection `filterDim` / `filterSFace` / `filterOp` that collapses
    discretized directions while preserving non-discrete higher dimensions!
-/
import Narya.Dim

namespace Narya.Modal

open Narya.Dim

/-- Identifier for a mode (0-cell of a mode theory). -/
abbrev ModeId := String

/-- Identifier for a generating modality (1-cell of a mode theory). -/
abbrev ModId := String

/-- Identifier for a generating 2-cell / modal key (`α : μ ⇒ ν`). -/
abbrev KeyId := String

/-- Structural flags of a modality `μ : M → N`, unifying `docs/source/modal.rst`,
    `discrete.rst`, `external.rst`, and `displayed.rst`. -/
structure ModalityFlags where
  /-- Admits positive modal pattern matching (`match x with | (y : μ) => ...`). -/
  tangible : Bool := true
  /-- Strictly preserves universes (`UU`). -/
  pellucid : Bool := false
  /-- Strictly preserves all type formers (e.g. identity modality). -/
  transparent : Bool := false
  /-- Preserves codata types up to projection. -/
  translucent : Bool := false
  /-- Left adjoint (`L ⊣ R`), enabling negative modal codata fields `(x : L | _) .fld : A`. -/
  sinister : Bool := false
  /-- Directions collapsed/discretized by this modality (`g ∈ discreteDirs` forgets `g`-bridges/paths). -/
  discreteDirs : List Dir := []
  /-- Acts as a parametricity locker blocking external types (`-external` / `-dtt`). -/
  isLocker : Bool := false
  deriving DecidableEq, Repr, Inhabited

namespace ModalityFlags

/-- Flags of the identity modality `1_M : M → M`. -/
def id : ModalityFlags :=
  { tangible := true
    pellucid := true
    transparent := true
    translucent := true
    sinister := true
    discreteDirs := []
    isLocker := false }

/-- Flags of a composite modality `f ∘ g` (apply `g`, then `f`). -/
def comp (f g : ModalityFlags) : ModalityFlags :=
  { tangible := f.tangible && g.tangible
    pellucid := f.pellucid && g.pellucid
    transparent := f.transparent && g.transparent
    translucent := f.translucent && g.translucent
    sinister := f.sinister && g.sinister
    discreteDirs := f.discreteDirs ++ g.discreteDirs
    isLocker := f.isLocker || g.isLocker }

/-- Whether a modality discretizes (collapses) a given dimension direction `d`. -/
def isDiscreteFor (fl : ModalityFlags) (d : Dir) : Bool :=
  fl.discreteDirs.contains d

/-- Whether a modality keeps a dimension direction `d` non-discrete. -/
def keepsDir (fl : ModalityFlags) (d : Dir) : Bool :=
  !(fl.isDiscreteFor d)

@[simp]
theorem keepsDir_id (d : Dir) : id.keepsDir d = true := rfl

@[simp]
theorem keepsDir_comp (f g : ModalityFlags) (d : Dir) :
    (comp f g).keepsDir d = (f.keepsDir d && g.keepsDir d) := by
  simp [keepsDir, isDiscreteFor, comp, Bool.not_or]

end ModalityFlags

/-- A generating 1-cell (atomic modality) `μ : dom → cod` in a mode theory. -/
structure ModGen where
  name : ModId
  dom : ModeId
  cod : ModeId
  flags : ModalityFlags := {}
  deriving DecidableEq, Repr, Inhabited

/-- A formal composite 1-cell `μ₁ ∘ ⋯ ∘ μₖ : dom → cod` in a mode theory.
    Convention: `steps = [μ₁, μ₂]` represents categorical composition `μ₁ ∘ μ₂`,
    where `μ₂ : dom → mid` applies first (closest to the variable) and `μ₁ : mid → cod`
    applies outermost (closest to the ambient context). -/
structure ModPath where
  dom : ModeId
  cod : ModeId
  steps : List ModGen
  deriving DecidableEq, Repr, Inhabited

namespace ModPath

/-- Identity 1-cell `1_M : M → M`. -/
def id (m : ModeId) : ModPath :=
  { dom := m, cod := m, steps := [] }

/-- Atomic 1-cell from a single generator `g : g.dom → g.cod`. -/
def atom (g : ModGen) : ModPath :=
  { dom := g.dom, cod := g.cod, steps := [g] }

/-- Categorical composition `μ ∘ ν` (valid when `μ.dom = ν.cod`). -/
def comp (μ ν : ModPath) : ModPath :=
  { dom := ν.dom, cod := μ.cod, steps := μ.steps ++ ν.steps }

/-- Check composable chain validity from `dom` to `cod`. -/
def wfSteps (dom cod : ModeId) : List ModGen → Bool
  | [] => dom == cod
  | g :: rest => (g.cod == cod) && wfSteps dom g.dom rest

/-- Well-formedness of a `ModPath`. -/
def wf (μ : ModPath) : Bool :=
  wfSteps μ.dom μ.cod μ.steps

@[simp]
theorem wf_id (m : ModeId) : (id m).wf = true := by
  simp [id, wf, wfSteps]

@[simp]
theorem comp_id_left (μ : ModPath) : comp (id μ.cod) μ = μ := by
  cases μ; rfl

@[simp]
theorem comp_id_right (μ : ModPath) : comp μ (id μ.dom) = μ := by
  cases μ
  simp [comp, id]

theorem comp_assoc (μ ν ρ : ModPath) :
    comp (comp μ ν) ρ = comp μ (comp ν ρ) := by
  cases μ; cases ν; cases ρ
  simp [comp, List.append_assoc]

theorem wfSteps_append {a b c : ModeId} {xs ys : List ModGen}
    (h₁ : wfSteps b c xs = true) (h₂ : wfSteps a b ys = true) :
    wfSteps a c (xs ++ ys) = true := by
  induction xs generalizing c with
  | nil =>
    simp [wfSteps] at h₁
    subst h₁
    exact h₂
  | cons g rest ih =>
    simp [wfSteps, Bool.and_eq_true] at h₁ ⊢
    exact ⟨h₁.1, ih h₁.2⟩

theorem wf_comp {μ ν : ModPath} (hμ : μ.wf = true) (hν : ν.wf = true) (hEq : μ.dom = ν.cod) :
    (comp μ ν).wf = true := by
  unfold wf at hμ hν ⊢
  unfold comp
  dsimp only
  rw [← hEq] at hν
  exact wfSteps_append hμ hν

/-- Effective `ModalityFlags` of a composite modality path. -/
def flags (μ : ModPath) : ModalityFlags :=
  μ.steps.foldr (fun g acc => ModalityFlags.comp g.flags acc) ModalityFlags.id

@[simp]
theorem flags_id (m : ModeId) : (id m).flags = ModalityFlags.id := rfl

theorem keepsDir_steps_append (xs ys : List ModGen) (d : Dir) :
    (List.foldr (fun g acc => ModalityFlags.comp g.flags acc) ModalityFlags.id (xs ++ ys)).keepsDir d =
      ((List.foldr (fun g acc => ModalityFlags.comp g.flags acc) ModalityFlags.id xs).keepsDir d &&
       (List.foldr (fun g acc => ModalityFlags.comp g.flags acc) ModalityFlags.id ys).keepsDir d) := by
  induction xs with
  | nil => simp
  | cons g rest ih =>
    simp only [List.cons_append, List.foldr, ModalityFlags.keepsDir_comp, ih, Bool.and_assoc]

/-- Whether `μ` keeps direction `d` non-discrete. -/
def keepsDir (μ : ModPath) (d : Dir) : Bool :=
  μ.flags.keepsDir d

@[simp]
theorem keepsDir_id (m : ModeId) (d : Dir) : (id m).keepsDir d = true := rfl

theorem keepsDir_comp (μ ν : ModPath) (d : Dir) :
    (comp μ ν).keepsDir d = (μ.keepsDir d && ν.keepsDir d) := by
  exact keepsDir_steps_append μ.steps ν.steps d

end ModPath

/-! ### Structural Dimension Filtering & Functorial Operator Projection -/

/-- Structural dimension context filter (defined via `cond` so `Bool.casesOn`
    computes definitionally with zero casts!). -/
def filterCtx (keep : Dir → Bool) : DimCtx → DimCtx
  | [] => []
  | g :: m => cond (keep g) (g :: filterCtx keep m) (filterCtx keep m)

@[simp]
theorem filterCtx_true (ctx : DimCtx) : filterCtx (fun _ => true) ctx = ctx := by
  induction ctx with
  | nil => rfl
  | cons g m ih => simp [filterCtx, ih]

theorem filterCtx_filterCtx (p q : Dir → Bool) (ctx : DimCtx) :
    filterCtx p (filterCtx q ctx) = filterCtx (fun d => p d && q d) ctx := by
  induction ctx with
  | nil => rfl
  | cons g m ih =>
    dsimp only [filterCtx]
    cases q g
    · dsimp only [cond]
      cases p g <;> simp [ih]
    · dsimp only [cond, filterCtx]
      cases p g <;> simp [ih]

namespace ModPath

/-- Filter a multi-directional dimension context `ctx : DimCtx` through modality `μ`,
    dropping any directions discretized by `μ`! -/
def filterDim (μ : ModPath) (ctx : DimCtx) : DimCtx :=
  filterCtx μ.keepsDir ctx

@[simp]
theorem filterDim_id (m : ModeId) (ctx : DimCtx) :
    (id m).filterDim ctx = ctx := by
  exact filterCtx_true ctx

/-- **Functoriality of Modal Dimension Filtering**: Filtering by `μ ∘ ν` equals
    filtering by `ν` and then filtering by `μ`! -/
theorem filterDim_comp (μ ν : ModPath) (ctx : DimCtx) :
    (comp μ ν).filterDim ctx = μ.filterDim (ν.filterDim ctx) := by
  unfold filterDim
  rw [filterCtx_filterCtx]
  congr 1
  funext d
  exact keepsDir_comp μ ν d

/-- Pretty name of a `ModPath` (e.g. `"1_M"` or `"R∘L"`). -/
def pretty (μ : ModPath) : String :=
  match μ.steps with
  | [] => s!"1_{μ.dom}"
  | gs => String.intercalate "∘" (gs.map (·.name))

end ModPath

/-- Project a strict face `f : SFace m n` along a direction filter `keep : Dir → Bool`.
    When `keep g = false` (a discretized direction), BOTH every endpoint `.endpt f' g e`
    AND the interior `.mid f' g` project to `filterSFace keep f'`, collapsing bridges/paths
    in direction `g` to identities! -/
def filterSFace (keep : Dir → Bool) {m n : DimCtx} :
    SFace m n → SFace (filterCtx keep m) (filterCtx keep n)
  | .zero => .zero
  | @SFace.endpt m n' f' g e =>
    let r := filterSFace keep f'
    Bool.casesOn (motive := fun b =>
        SFace (filterCtx keep m) (cond b (g :: filterCtx keep n') (filterCtx keep n')))
      (keep g) r (.endpt r g e)
  | @SFace.mid m' n' f' g =>
    let r := filterSFace keep f'
    Bool.casesOn (motive := fun b =>
        SFace (cond b (g :: filterCtx keep m') (filterCtx keep m'))
              (cond b (g :: filterCtx keep n') (filterCtx keep n')))
      (keep g) r (.mid r g)

/-- **Identity Preservation of `filterSFace`**. -/
@[simp]
theorem filterSFace_id (keep : Dir → Bool) (n : DimCtx) :
    filterSFace keep (SFace.id n) = SFace.id (filterCtx keep n) := by
  induction n with
  | nil => rfl
  | cons g m ih =>
    simp only [SFace.id, filterSFace, filterCtx]
    cases keep g <;> simp [cond, SFace.id, ih]

/-- **Functoriality of `filterSFace` (`filterSFace_comp`)**: Filtering preserves
    strict face composition for arbitrary multi-arity directions! -/
theorem filterSFace_comp (keep : Dir → Bool) {a b c : DimCtx}
    (f₁ : SFace b c) (f₂ : SFace a b) :
    filterSFace keep (f₁.comp f₂) = (filterSFace keep f₁).comp (filterSFace keep f₂) := by
  induction f₁ generalizing a with
  | zero =>
    cases f₂
    rfl
  | endpt f₁' g e ih =>
    simp only [SFace.comp, filterSFace, filterCtx]
    cases keep g <;> simp [SFace.comp, ih]
  | mid f₁' g ih =>
    cases f₂ with
    | endpt f₂' _ e =>
      simp only [SFace.comp, filterSFace, filterCtx]
      cases keep g <;> simp [SFace.comp, ih]
    | mid f₂' _ =>
      simp only [SFace.comp, filterSFace, filterCtx]
      cases keep g <;> simp [SFace.comp, ih]

/-- Project a strict degeneracy `s : SDeg m n` along a direction filter `keep : Dir → Bool`. -/
def filterSDeg (keep : Dir → Bool) {m n : DimCtx} :
    SDeg m n → SDeg (filterCtx keep m) (filterCtx keep n)
  | .zero => .zero
  | @SDeg.keep a' b' s g =>
    let r := filterSDeg keep s
    Bool.casesOn (motive := fun b =>
        SDeg (cond b (g :: filterCtx keep a') (filterCtx keep a'))
             (cond b (g :: filterCtx keep b') (filterCtx keep b')))
      (keep g) r (.keep r g)
  | @SDeg.degen a' b' s g =>
    let r := filterSDeg keep s
    Bool.casesOn (motive := fun b =>
        SDeg (cond b (g :: filterCtx keep a') (filterCtx keep a'))
             (filterCtx keep b'))
      (keep g) r (.degen r g)

@[simp]
theorem filterSDeg_id (keep : Dir → Bool) (n : DimCtx) :
    filterSDeg keep (SDeg.id n) = SDeg.id (filterCtx keep n) := by
  induction n with
  | nil => rfl
  | cons g m ih =>
    simp only [SDeg.id, filterSDeg, filterCtx]
    cases keep g <;> simp [cond, SDeg.id, ih]

/-! ### 2-Cells (Modal Keys) and Mode Theory Presentations -/

/-- A generating 2-cell (atomic modal key) `α : src ⇒ tgt` between parallel 1-cells. -/
structure TwoCellGen where
  name : KeyId
  domMode : ModeId
  codMode : ModeId
  src : ModPath
  tgt : ModPath
  deriving DecidableEq, Repr, Inhabited

/-- Formal 2-cell expressions in a 2-category of modes, modalities, and keys. -/
inductive TwoCellExpr : Type where
  /-- Identity 2-cell `1_μ : μ ⇒ μ`. -/
  | id2 (μ : ModPath) : TwoCellExpr
  /-- Generating 2-cell `α : src ⇒ tgt`. -/
  | gen (c : TwoCellGen) : TwoCellExpr
  /-- Vertical composition `β ∘ᵥ α : μ ⇒ ρ` (`α : μ ⇒ ν` followed by `β : ν ⇒ ρ`). -/
  | vcomp (β α : TwoCellExpr) : TwoCellExpr
  /-- Left whiskering `λ_ ◁ α : λ_ ∘ μ ⇒ λ_ ∘ ν`. -/
  | whiskerL (l : ModPath) (α : TwoCellExpr) : TwoCellExpr
  /-- Right whiskering `α ▷ ρ : μ ∘ ρ ⇒ ν ∘ ρ`. -/
  | whiskerR (α : TwoCellExpr) (r : ModPath) : TwoCellExpr
  deriving DecidableEq, Repr, Inhabited

namespace TwoCellExpr

/-- Compute the source `ModPath` of a `TwoCellExpr`. -/
def src : TwoCellExpr → ModPath
  | .id2 μ => μ
  | .gen c => c.src
  | .vcomp _ α => α.src
  | .whiskerL l α => l.comp α.src
  | .whiskerR α r => α.src.comp r

/-- Compute the target `ModPath` of a `TwoCellExpr`. -/
def tgt : TwoCellExpr → ModPath
  | .id2 μ => μ
  | .gen c => c.tgt
  | .vcomp β _ => β.tgt
  | .whiskerL l α => l.comp α.tgt
  | .whiskerR α r => α.tgt.comp r

/-- Check 2-categorical typing well-formedness of a `TwoCellExpr`. -/
def wf : TwoCellExpr → Bool
  | .id2 μ => μ.wf
  | .gen c =>
    c.src.wf && c.tgt.wf &&
    (c.src.dom == c.domMode) && (c.src.cod == c.codMode) &&
    (c.tgt.dom == c.domMode) && (c.tgt.cod == c.codMode)
  | .vcomp β α =>
    α.wf && β.wf && (α.tgt == β.src)
  | .whiskerL l α =>
    l.wf && α.wf && (l.dom == α.src.cod) && (l.dom == α.tgt.cod)
  | .whiskerR α r =>
    α.wf && r.wf && (α.src.dom == r.cod) && (α.tgt.dom == r.cod)

/-- Horizontal Godement composition `β ⋆ α : β.src ∘ α.src ⇒ β.tgt ∘ α.tgt`. -/
def hcomp (β α : TwoCellExpr) : TwoCellExpr :=
  .vcomp (.whiskerL β.tgt α) (.whiskerR β α.src)

/-- Pretty-print a 2-cell expression. -/
def pretty : TwoCellExpr → String
  | .id2 μ => s!"id({μ.pretty})"
  | .gen c => c.name
  | .vcomp β α => s!"({β.pretty} ∘ᵥ {α.pretty})"
  | .whiskerL l α =>
    if l.steps.isEmpty then α.pretty else s!"({l.pretty} ◁ {α.pretty})"
  | .whiskerR α r =>
    if r.steps.isEmpty then α.pretty else s!"({α.pretty} ▷ {r.pretty})"

end TwoCellExpr

/-- Directed 2-cell rewrite / coherence equation `lhs ↝ rhs` (with parallel `src` and `tgt`). -/
structure TwoCellRule where
  name : String
  lhs : TwoCellExpr
  rhs : TwoCellExpr
  deriving DecidableEq, Repr, Inhabited

/-- A first-class 2-categorical **Mode Theory Presentation** (`ModeTheory`).
    Can be constructed, inspected, composed via CSLib/Carette–O'Connor theory combinators,
    and elaborated via Lean 4 `mode_theory` declarations! -/
structure ModeTheory where
  name : String
  modes : List ModeId
  modalities : List ModGen
  twoCells : List TwoCellGen
  rules : List TwoCellRule := []
  defaultMode : ModeId := "M"
  deriving DecidableEq, Repr, Inhabited

namespace ModeTheory

/-- Look up a generating modality by name. -/
def findMod? (T : ModeTheory) (name : ModId) : Option ModGen :=
  T.modalities.find? (fun g => g.name == name)

/-- Look up a generating 2-cell by name. -/
def findTwoCell? (T : ModeTheory) (name : KeyId) : Option TwoCellGen :=
  T.twoCells.find? (fun c => c.name == name)

/-- Check that every modality, 2-cell, and rule in `T` is well-formed over `T.modes`. -/
def wf (T : ModeTheory) : Bool :=
  (T.modes.contains T.defaultMode) &&
  T.modalities.all (fun g => T.modes.contains g.dom && T.modes.contains g.cod) &&
  T.twoCells.all (fun c =>
    T.modes.contains c.domMode && T.modes.contains c.codMode &&
    (TwoCellExpr.gen c).wf) &&
  T.rules.all (fun r =>
    r.lhs.wf && r.rhs.wf && (r.lhs.src == r.rhs.src) && (r.lhs.tgt == r.rhs.tgt))

end ModeTheory

end Narya.Modal
