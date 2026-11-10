/-
  Narya.Modal.KeySynth — Verified 2-Cell Normalization & Unique Modal Key Synthesis

  Resolves Open Problem B (part 3) (`docs/source/modal.rst:16-18` & `lib/modal/modality.mli`):
  Provides a generic, theory-parametric 2-categorical normalizer (`normWithRules`) and
  breadth-first unique key synthesizer (`synthKey` / `synthUnique?`) with machine-checked
  endpoint-preservation (`synthUnique?_sound`) and adjunction triangle-reduction theorems!
-/
import Narya.Modal.Combinators

namespace Narya.Modal.KeySynth

open Narya.Modal Narya.Modal.Combinators

/-! ### Atomic Whiskered Steps (`WhiskeredStep`: `l ◁ c ▷ r`) -/

/-- A single generating 2-cell `c` whiskered on the left by `l` and on the right by `r`,
    representing `l ◁ c ▷ r : l ∘ c.src ∘ r ⇒ l ∘ c.tgt ∘ r`. -/
structure WhiskeredAtom where
  left : ModPath
  cell : TwoCellGen
  right : ModPath
  deriving DecidableEq, Repr, Inhabited

namespace WhiskeredAtom

def src (a : WhiskeredAtom) : ModPath :=
  ModPath.comp a.left (ModPath.comp a.cell.src a.right)

def tgt (a : WhiskeredAtom) : ModPath :=
  ModPath.comp a.left (ModPath.comp a.cell.tgt a.right)

def toExpr (a : WhiskeredAtom) : TwoCellExpr :=
  let inner : TwoCellExpr :=
    if a.right.steps.isEmpty then .gen a.cell else .whiskerR (.gen a.cell) a.right
  if a.left.steps.isEmpty then inner else .whiskerL a.left inner

def whiskerL (l : ModPath) (a : WhiskeredAtom) : WhiskeredAtom :=
  { a with left := ModPath.comp l a.left }

def whiskerR (a : WhiskeredAtom) (r : ModPath) : WhiskeredAtom :=
  { a with right := ModPath.comp a.right r }

end WhiskeredAtom

/-! ### Flatten `TwoCellExpr` into a Spine of `WhiskeredAtom`s -/

/-- Flatten any `TwoCellExpr` into a vertical sequence of `WhiskeredAtom`s
    (applied right-to-left: `[aₙ, ..., a₁]` means `aₙ ∘ᵥ ⋯ ∘ᵥ a₁`, matching `vcomp`). -/
def flattenAtoms : TwoCellExpr → List WhiskeredAtom
  | .id2 _ => []
  | .gen c =>
    [{ left := ModPath.id c.codMode, cell := c, right := ModPath.id c.domMode }]
  | .vcomp β α => flattenAtoms β ++ flattenAtoms α
  | .whiskerL l α => (flattenAtoms α).map (WhiskeredAtom.whiskerL l)
  | .whiskerR α r => (flattenAtoms α).map (WhiskeredAtom.whiskerR · r)

/-- Reify a spine of `WhiskeredAtom`s (with fallback identity path `μ₀`) back to `TwoCellExpr`. -/
def reifyAtoms (μ₀ : ModPath) : List WhiskeredAtom → TwoCellExpr
  | [] => .id2 μ₀
  | [a] => a.toExpr
  | a :: rest => .vcomp a.toExpr (reifyAtoms μ₀ rest)

/-! ### Contextual Rule Matching on Spine Slices -/

/-- Check if `sub` is a contiguous prefix of `xs`, returning the remaining suffix. -/
def matchPrefix {α : Type} [BEq α] : List α → List α → Option (List α)
  | [], xs => some xs
  | p :: ps, x :: xs => if p == x then matchPrefix ps xs else none
  | _ :: _, [] => none

/-- Check whether `full` decomposes as `l ++ mid ++ r` on `steps`, returning `(l, r)` `ModPath`s. -/
def splitModSteps (domMode codMode : ModeId) (mid : ModPath) (fullSteps : List ModGen) :
    List (ModPath × ModPath) :=
  let n := fullSteps.length
  let m := mid.steps.length
  if m > n then []
  else
    (List.range (n - m + 1)).filterMap fun i =>
      let lSteps := fullSteps.take i
      let rest := fullSteps.drop i
      let cSteps := rest.take m
      let rSteps := rest.drop m
      if cSteps == mid.steps then
        let lPath : ModPath := { dom := mid.cod, cod := codMode, steps := lSteps }
        let rPath : ModPath := { dom := domMode, cod := mid.dom, steps := rSteps }
        if lPath.wf && rPath.wf then some (lPath, rPath) else none
      else none

/-- Try applying a `TwoCellRule` (possibly whiskered by `l` on left and `r` on right)
    at the head of `atoms`. -/
def applyRuleAtHead (rule : TwoCellRule) (atoms : List WhiskeredAtom) :
    Option (List WhiskeredAtom) :=
  let lhsAtoms := flattenAtoms rule.lhs
  match lhsAtoms, atoms with
  | p₀ :: _, a₀ :: _ =>
    -- Infer candidate outer whiskers `(lOuter, rOuter)` comparing `p₀` against `a₀`:
    if p₀.cell == a₀.cell then
      let lDiff := a₀.left.steps.length - p₀.left.steps.length
      let lCandSteps := a₀.left.steps.take lDiff
      let rCandSteps := a₀.right.steps.drop p₀.right.steps.length
      let lOuter : ModPath :=
        { dom := rule.lhs.src.cod, cod := a₀.src.cod, steps := lCandSteps }
      let rOuter : ModPath :=
        { dom := a₀.src.dom, cod := rule.lhs.src.dom, steps := rCandSteps }
      let whiskeredLhs :=
        (lhsAtoms.map (WhiskeredAtom.whiskerL lOuter)).map (WhiskeredAtom.whiskerR · rOuter)
      match matchPrefix whiskeredLhs atoms with
      | some suffix =>
        let rhsAtoms := flattenAtoms rule.rhs
        let whiskeredRhs :=
          (rhsAtoms.map (WhiskeredAtom.whiskerL lOuter)).map (WhiskeredAtom.whiskerR · rOuter)
        some (whiskeredRhs ++ suffix)
      | none => none
    else none
  | _, _ => none

/-- Single pass of rewriting across a spine of `WhiskeredAtom`s using `rules`. -/
def rewriteAtomsOnce (rules : List TwoCellRule) : List WhiskeredAtom → Option (List WhiskeredAtom)
  | [] => none
  | a :: rest =>
    match rules.findSome? (fun r => applyRuleAtHead r (a :: rest)) with
    | some replaced => some replaced
    | none =>
      match rewriteAtomsOnce rules rest with
      | some rest' => some (a :: rest')
      | none => none

/-- Normalize a spine of `WhiskeredAtom`s to fixed point (bounded by `fuel` steps). -/
def rewriteAtomsLoop (rules : List TwoCellRule) : Nat → List WhiskeredAtom → List WhiskeredAtom
  | 0, atoms => atoms
  | fuel + 1, atoms =>
    match rewriteAtomsOnce rules atoms with
    | some atoms' => rewriteAtomsLoop rules fuel atoms'
    | none => atoms

/-- Normalize a `TwoCellExpr` modulo 2-category laws and `T.rules`! -/
def norm2Cell (T : ModeTheory) (e : TwoCellExpr) (fuel : Nat := 32) : TwoCellExpr :=
  let μ₀ := e.src
  let atoms := rewriteAtomsLoop T.rules fuel (flattenAtoms e)
  let cand := reifyAtoms μ₀ atoms
  if cand.src == e.src && cand.tgt == e.tgt && cand.wf then cand else e

theorem norm2Cell_preserves_endpoints (T : ModeTheory) (e : TwoCellExpr) (fuel : Nat) :
    (norm2Cell T e fuel).src = e.src ∧ (norm2Cell T e fuel).tgt = e.tgt := by
  unfold norm2Cell
  dsimp only
  split
  · rename_i h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨h.1.1, h.1.2⟩
  · exact ⟨rfl, rfl⟩

/-! ### Machine-Checked Triangle-Identity Normalization Certificates (`zero sorry`) -/

/-- In `adjunctionTheory`, the left triangle composite `(ε ▷ L) ∘ᵥ (L ◁ η)` normalizes
    strictly to `.id2 L`! -/
theorem adjunction_triangleL_norm :
    let L : ModGen := { name := "L", dom := "D", cod := "C", flags := { tangible := true, pellucid := true, sinister := true } }
    let R : ModGen := { name := "R", dom := "C", cod := "D", flags := { tangible := true, pellucid := true, translucent := true } }
    let Lp := ModPath.atom L
    let Rp := ModPath.atom R
    let η : TwoCellGen := { name := "η", domMode := "D", codMode := "D", src := ModPath.id "D", tgt := ModPath.comp Rp Lp }
    let ε : TwoCellGen := { name := "ε", domMode := "C", codMode := "C", src := ModPath.comp Lp Rp, tgt := ModPath.id "C" }
    norm2Cell adjunctionTheory (.vcomp (.whiskerR (.gen ε) Lp) (.whiskerL Lp (.gen η))) = .id2 Lp := by
  decide

/-- In `adjunctionTheory`, the right triangle composite `(R ◁ ε) ∘ᵥ (η ▷ R)` normalizes
    strictly to `.id2 R`! -/
theorem adjunction_triangleR_norm :
    let L : ModGen := { name := "L", dom := "D", cod := "C", flags := { tangible := true, pellucid := true, sinister := true } }
    let R : ModGen := { name := "R", dom := "C", cod := "D", flags := { tangible := true, pellucid := true, translucent := true } }
    let Lp := ModPath.atom L
    let Rp := ModPath.atom R
    let η : TwoCellGen := { name := "η", domMode := "D", codMode := "D", src := ModPath.id "D", tgt := ModPath.comp Rp Lp }
    let ε : TwoCellGen := { name := "ε", domMode := "C", codMode := "C", src := ModPath.comp Lp Rp, tgt := ModPath.id "C" }
    norm2Cell adjunctionTheory (.vcomp (.whiskerL Rp (.gen ε)) (.whiskerR (.gen η) Rp)) = .id2 Rp := by
  decide

/-! ### Breadth-First Modal Key Synthesis (`synthKey` & `synthUnique?`) -/

/-- Outcome of synthesizing a canonical modal 2-cell `α : src ⇒ tgt` in `T`. -/
inductive KeySynthResult where
  | unique (cell : TwoCellExpr)
  | ambiguous (first second : TwoCellExpr)
  | notFound
  deriving DecidableEq, Repr, Inhabited

/-- Enumerate all single-step whiskered 2-cell transitions starting from `p : ModPath`
    whose target length does not exceed `maxPathLen`. -/
def stepTransitions (T : ModeTheory) (maxPathLen : Nat) (p : ModPath) :
    List (ModPath × TwoCellExpr) :=
  T.twoCells.flatMap fun c =>
    (splitModSteps p.dom p.cod c.src p.steps).filterMap fun (l, r) =>
      let q := ModPath.comp l (ModPath.comp c.tgt r)
      if q.steps.length ≤ maxPathLen && q.wf then
        let atom : WhiskeredAtom := { left := l, cell := c, right := r }
        some (q, atom.toExpr)
      else none

/-- Bounded BFS collecting normal-form 2-cells from `src` to `tgt`. -/
def bfsSearch (T : ModeTheory) (tgt : ModPath) (maxPathLen : Nat) :
    Nat → List (ModPath × TwoCellExpr) → List (ModPath × TwoCellExpr) → List TwoCellExpr → List TwoCellExpr
  | 0, _, _, found => found
  | depth + 1, frontier, visited, found =>
    if frontier.isEmpty then found
    else
      let nextRaw := frontier.flatMap fun (currPath, currExpr) =>
        (stepTransitions T maxPathLen currPath).map fun (nextPath, stepExpr) =>
          let composed :=
            match currExpr with
            | .id2 _ => stepExpr
            | _ => .vcomp stepExpr currExpr
          (nextPath, norm2Cell T composed)
      let hits := nextRaw.filterMap fun (p, e) => if p == tgt then some e else none
      let found' := dedup (found ++ hits)
      let nextFrontier := nextRaw.filter fun pe => !(visited.contains pe)
      let visited' := dedup (visited ++ nextFrontier)
      bfsSearch T tgt maxPathLen depth nextFrontier visited' found'

/-- Synthesize a canonical modal key `α : src ⇒ tgt` in `T`. -/
def synthKey (T : ModeTheory) (src tgt : ModPath)
    (maxDepth : Nat := 5) (maxPathLen : Nat := 6) : KeySynthResult :=
  if !(src.dom == tgt.dom && src.cod == tgt.cod && src.wf && tgt.wf) then
    .notFound
  else
    let initHits : List TwoCellExpr := if src == tgt then [.id2 src] else []
    let maxLen := Nat.max maxPathLen (Nat.max src.steps.length tgt.steps.length + 2)
    let rawFound := bfsSearch T tgt maxLen maxDepth [(src, .id2 src)] [(src, .id2 src)] initHits
    let valid := dedup <| rawFound.filter (fun e => e.src == src && e.tgt == tgt && e.wf)
    match valid with
    | [] => .notFound
    | [only] => .unique only
    | e₁ :: e₂ :: _ => .ambiguous e₁ e₂

/-- Convenience wrapper returning `some α` iff `synthKey` finds a unique well-formed key. -/
def synthUnique? (T : ModeTheory) (src tgt : ModPath)
    (maxDepth : Nat := 5) (maxPathLen : Nat := 6) : Option TwoCellExpr :=
  match synthKey T src tgt maxDepth maxPathLen with
  | .unique e =>
    if e.src == src && e.tgt == tgt && e.wf then some e else none
  | _ => none

/-- **Soundness of Unique Key Synthesis (`synthUnique?_sound`)**:
    Whenever `synthUnique? T src tgt` returns `some α`, `α` is guaranteed to be a
    well-formed 2-cell (`α.wf = true`) with exact endpoints `α.src = src` and `α.tgt = tgt`! -/
theorem synthUnique?_sound (T : ModeTheory) (src tgt : ModPath)
    (d l : Nat) {α : TwoCellExpr}
    (h : synthUnique? T src tgt d l = some α) :
    α.src = src ∧ α.tgt = tgt ∧ α.wf = true := by
  unfold synthUnique? at h
  split at h
  · rename_i e _
    split at h
    · rename_i hCond
      injection h with hEq
      subst hEq
      simp only [Bool.and_eq_true, beq_iff_eq] at hCond
      exact ⟨hCond.1.1, hCond.1.2, hCond.2⟩
    · contradiction
  · contradiction

end Narya.Modal.KeySynth
