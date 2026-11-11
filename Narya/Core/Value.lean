/-
  Narya.Core.Value — Strictly Positive Glued NbE Semantic Domain & Modal Key Actions

  Port of OCaml Narya's `lib/core/value.ml` and `lib/core/act.ml`.
  Key engineering choices:
  1. Closures (`Closure`) are first-order data `{ env : List Val, body : Term }`, making
     `Val` strictly positive, inspectable (`Repr`, `BEq`), and 100% computable.
  2. `Val.glued` retains BOTH the unreduced global head+spine AND the forced semantic
     value, enabling Narya's 3-tier `EQUAL.md` conversion fast-path.
  3. Modal key action `actKey` short-circuits identity 2-cells in $O(1)$ (`actKey_id2`)
     and fuses adjacent spine keys via `KeySynth.norm2Cell` — so adjunction triangle
     identities `(ε ▷ L) ∘ᵥ (L ◁ η) ↝ 1_L` reduce definitionally in NbE!
-/
import Narya.Core.Syntax

namespace Narya.Core

open Narya.Dim Narya.Modal Narya.Modal.KeySynth

/-- Neutral head in the semantic domain. -/
inductive Head where
  /-- Bound variable at De Bruijn level `lvl` (0 = outermost context variable). -/
  | lvar (lvl : Lvl)
  /-- Unsolved unification metavariable `?m_id` (`EQUAL.md:174`). -/
  | mvar (id : Nat)
  /-- Postulated global axiom / opaque constant. -/
  | ax (name : String)
  /-- Potential (lazy coinductive) global constant awaiting projection/observation. -/
  | potential (name : String)
  deriving BEq, Repr, Inhabited

mutual

/-- First-order semantic closure (strictly positive, covering lexical lambdas and
    HOTT contravariant-covariant `Π`-transport functions). -/
inductive Closure where
  | mk (env : List Val) (body : Term)
  | arrowTrr (g : Dir) (mod : ModPath) (domLine : Val) (codLine : Val) (f₀ : Val)
  | arrowTrl (g : Dir) (mod : ModPath) (domLine : Val) (codLine : Val) (f₁ : Val)
  | piTrr (g : Dir) (mod : ModPath) (domLine : Val) (env : List Val) (codLine : Term) (f₀ : Val)
  | piTrl (g : Dir) (mod : ModPath) (domLine : Val) (env : List Val) (codLine : Term) (f₁ : Val)
  deriving BEq, Repr

/-- Semantic elimination frame (stored in reverse-application order on `rspine` for $O(1)$ push). -/
inductive Elim where
  | app (mod : ModPath) (arg : Val)
  | proj (field : String)
  | key (cell : TwoCellExpr)
  | sym (g : Dir)
  | ap (g : Dir) (fn : Val)
  | ungel (g : Dir)
  | trr (g : Dir) (tyLine : Val)
  | trl (g : Dir) (tyLine : Val)
  | matchData (winMod : ModPath) (motive : Val)
      (branches : List (String × Nat × Term)) (env : List Val)
  | pathJ (g : Dir) (ty : Val) (base : Val) (motive : Val) (reflCase : Val) (target : Val)
  | hap (g : Dir) (a₀ a₁ pa : Val)
  | u64BinOpL (op : BinOp64) (rhs : Val)
  | u64BinOpR (op : BinOp64) (lhs : UInt64)
  | u64IfZero (zBr nzBr : Val)
  deriving BEq, Repr

/-- Glued semantic values of `narya-lean`. -/
inductive Val where
  /-- Stuck neutral `hd` with reverse-order elimination spine `rspine`. -/
  | neu (hd : Head) (rspine : List Elim)
  /-- Glued global unfolding: keeps `name` + `rspine` for $O(1)$ spine comparison
      while caching the unfolded value `forced`! -/
  | glued (name : String) (rspine : List Elim) (forced : Val)
  /-- Observational universe `UU lvl`. -/
  | uu (lvl : Nat)
  /-- External discrete universe `UU_ext lvl`. -/
  | uuExt (lvl : Nat)
  /-- Modal dependent function type `(x : mod | dom) → cod`. -/
  | pi (name : String) (mod : ModPath) (dom : Val) (cod : Closure)
  /-- Modal lambda `λ (x : mod) => body`. -/
  | lam (name : String) (mod : ModPath) (body : Closure)
  /-- Positive modal box type `⟨mod | ty⟩`. -/
  | modalBox (mod : ModPath) (ty : Val)
  /-- Positive modal box value `box(mod, tm)`. -/
  | boxIntro (mod : ModPath) (tm : Val)
  /-- Dependent record / negative modal codata type telescope. -/
  | recordTy (env : List Val) (fields : List (String × ModPath × Term))
  /-- Evaluated record / comatch tuple `⟨f₁ := v₁, ...⟩`. -/
  | tuple (fields : List (String × Val))
  /-- Inductive datatype `Data name params`. -/
  | dataTy (name : String) (params : List Val)
  /-- Inductive constructor `Ctor dataName ctorName args`. -/
  | ctor (dataName : String) (ctorName : String) (args : List Val)
  /-- Homogeneous observational bridge/path type (when `ty` is neutral or atomic). -/
  | obsEq (g : Dir) (ty : Val) (ends : List Val)
  /-- Heterogeneous observational bridge/path type (when `tyBridge` is neutral). -/
  | obsHet (g : Dir) (tyBridge : Val) (ends : List Val)
  /-- Reflexivity / degeneracy bridge `refl_g v`. -/
  | refl (g : Dir) (tm : Val)
  /-- Composite fibrant path `trans g p q` (when neither `p` nor `q` is `refl`). -/
  | trans (g : Dir) (p : Val) (q : Val)
  /-- Relational Gel/Glue bridge-of-types `Gel_g types rel`. -/
  | gel (g : Dir) (types : List Val) (rel : Val)
  /-- Canonical bridge inside a `Gel` type: `gelIntro_g ends wit`. -/
  | gelIntro (g : Dir) (ends : List Val) (wit : Val)
  /-- Canonical non-dependent modal function-type bridge. -/
  | arrowLine (g : Dir) (mod : ModPath) (domLine : Val) (codLine : Val)
  /-- Canonical dependent modal Π-type bridge. -/
  | piLine (g : Dir) (name : String) (mod : ModPath) (domLine : Val)
      (env : List Val) (cod0 cod1 codLine : Term)
  /-- Canonical binary product record bridge. -/
  | prodLine (g : Dir) (fstName sndName : String) (fstLine : Val) (sndLine : Val)
  /-- Canonical dependent modal Σ/record bridge. -/
  | sigLine (g : Dir) (fstName sndName : String) (fstMod sndMod : ModPath)
      (fstLine : Val) (env : List Val) (snd0 snd1 sndLine : Term)
  /-- Canonical positive modal box type bridge. -/
  | boxLine (g : Dir) (mod : ModPath) (innerLine : Val)
  /-- Canonical fibrant forward path lift `liftr g tyLine x₀`. -/
  | liftr (g : Dir) (tyLine : Val) (x₀ : Val)
  /-- Canonical fibrant backward path lift `liftl g tyLine x₁`. -/
  | liftl (g : Dir) (tyLine : Val) (x₁ : Val)
  /-- Canonical pointwise function-bridge witness `funext g mod env body`. -/
  | funext (g : Dir) (mod : ModPath) (env : List Val) (body : Term)
  /-- Unboxed 64-bit machine word type `U64`. -/
  | u64Ty
  /-- Unboxed 64-bit machine word semantic value. -/
  | u64Lit (val : UInt64)
  deriving BEq, Repr

end

instance : Inhabited Val := ⟨.uu 0⟩
instance : Inhabited Closure := ⟨.mk [] (.uu 0)⟩
instance : Inhabited Elim := ⟨.proj ""⟩

namespace Val

/-- Construct a fresh neutral variable at De Bruijn level `lvl`. -/
def vvar (lvl : Lvl) : Val :=
  .neu (.lvar lvl) []

/-- Unwrap any outer `Val.glued` wrapper to reveal the underlying canonical/neutral `Val`. -/
def force : Val → Val
  | .glued _ _ forced => force forced
  | v => v

mutual
def actKeyGo (T : ModeTheory) (cNorm : TwoCellExpr) : Val → Val
  | .neu hd (.key prev :: rest) =>
    let fused := norm2Cell T (.vcomp cNorm prev)
    match fused with
    | .id2 _ => .neu hd rest
    | _ => .neu hd (.key fused :: rest)
  | .neu hd rspine => .neu hd (.key cNorm :: rspine)
  | .glued name rspine forced =>
    .glued name (.key cNorm :: rspine) (actKeyGo T cNorm forced)
  | .uu lvl => .uu lvl
  | .uuExt lvl => .uuExt lvl
  | .tuple fields => .tuple (actKeyFields T cNorm fields)
  | .refl g tm =>
    if cNorm.tgt.keepsDir g then .refl g (actKeyGo T cNorm tm)
    else actKeyGo T cNorm tm
  | other => other

def actKeyFields (T : ModeTheory) (cNorm : TwoCellExpr) :
    List (String × Val) → List (String × Val)
  | [] => []
  | (fn, fv) :: rest => (fn, actKeyGo T cNorm fv) :: actKeyFields T cNorm rest
end

/-- Apply a normalized 2-cell key `cell : TwoCellExpr` to a semantic value `v`.
    - Normalizes `cell` once at the root and short-circuits `.id2 _` in $O(1)$!
    - Fuses adjacent `.key prev` eliminations via `norm2Cell T (.vcomp cell prev)` and
      drops `.id2 _` completely (implementing triangle-identity cancellation!). -/
def actKey (T : ModeTheory) (cell : TwoCellExpr) (v : Val) : Val :=
  let cNorm := norm2Cell T cell
  match cNorm with
  | .id2 _ => v
  | _ => actKeyGo T cNorm v

/-- **Identity Key Short-Circuit Theorem (`actKey_id2`)**:
    Acting by an identity 2-cell `.id2 μ` (when `μ.wf = true`) leaves every semantic
    value `v` strictly unchanged! -/
theorem actKey_id2 (T : ModeTheory) (μ : ModPath) (hWf : μ.wf = true) (v : Val) :
    actKey T (.id2 μ) v = v := by
  unfold actKey norm2Cell
  simp [flattenAtoms, rewriteAtomsLoop, rewriteAtomsOnce, reifyAtoms,
        TwoCellExpr.src, TwoCellExpr.tgt, TwoCellExpr.wf, hWf]

end Val

end Narya.Core
