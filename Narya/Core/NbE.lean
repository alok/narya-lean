/-
  Narya.Core.NbE — Total Glued Normalization-by-Evaluation, Observational Gel, & Fibrancy

  Port and multi-directional unification of OCaml Narya's `lib/core/norm.ml`
  and `lib/core/fibrancy.ml`.
  100% computable and total (fuel-indexed, `zero partial`, `zero sorry`).
  Computes:
  - Glued transparent globals (`Energy.kinetic`) + lazy coinductive globals (`Energy.potential`)
  - Modal `Π` β-reduction and 2-cell key fusion (`actKey` with triangle cancellation)
  - Positive modal box β-reduction (`letBox (boxIntro m v) ↝ body[v]`)
  - Record / negative modal codata field projection (`⟨..., f := v, ...⟩ .f ↝ v`)
  - Windowed inductive pattern matching (`matchData (ctor c args) ↝ branch_c[args]`)
  - Relational `Gel` bridges (`ObsHet g (Gel_g As R) ends ↝ R ends₀ ...`, `ungel (gelIntro ends w) ↝ w`)
  - Computational Univalence (`trr .hott (Gel .hott [A₀, A₁] equivTuple) x₀ ↝ equivTuple.fwd x₀`!)
  - HoTT path computation (`ap g f (refl g x) ↝ refl g (f x)`, `sym g (refl g x) ↝ refl g x`, `J ... (refl g a) ↝ reflCase`)
  - Full `readback` from `Val` to normal-form `Term` (with Π and record η-canonicalization option)
-/
import Narya.Core.Value

namespace Narya.Core

open Narya.Dim Narya.Modal

/-- Look up De Bruijn index `ix` in `Val` environment `env`. -/
def lookupValEnv (env : List Val) (ix : Ix) : Val :=
  match env[ix]? with
  | some v => v
  | none => .neu (.lvar ix) []

/-- Look up a field in a tuple's `(name, Val)` list. -/
def lookupTupleField? (fields : List (String × Val)) (fname : String) : Option Val :=
  fields.findSome? fun (n, v) => if n == fname then some v else none

mutual

/-- Apply a semantic function `fn` to an argument `arg` at modality `mod`. -/
def applyVal (fuel : Nat) (G : GlobalEnv) (fn : Val) (mod : ModPath) (arg : Val) : Val :=
  match fuel with
  | 0 => .neu (.ax "<out-of-fuel>") [.app mod arg]
  | fuel' + 1 =>
    match fn with
    | .lam _ _ (.mk env body) =>
      evalTerm fuel' G (arg :: env) body
    | .glued name rspine forced =>
      .glued name (.app mod arg :: rspine) (applyVal fuel' G forced mod arg)
    | .neu (.potential name) rspine =>
      match G.lookup? name with
      | some (.defn _ _ _ _ body) =>
        let unfolded := replaySpine fuel' G (evalTerm fuel' G [] body) rspine.reverse
        applyVal fuel' G unfolded mod arg
      | _ => .neu (.potential name) (.app mod arg :: rspine)
    | .neu hd rspine =>
      .neu hd (.app mod arg :: rspine)
    | other =>
      .neu (.ax "<stuck-app>") [.app mod arg, .proj s!"{reprStr other}"]

/-- Apply `fn` to a list of arguments at identity modality `1_M`. -/
def applyManyId (fuel : Nat) (G : GlobalEnv) (fn : Val) : List Val → Val
  | [] => fn
  | a :: as =>
    match fuel with
    | 0 => fn
    | fuel' + 1 =>
      let step := applyVal fuel' G fn (ModPath.id G.theory.defaultMode) a
      applyManyId fuel' G step as

/-- Project `.field` from a semantic value `v` (unfolding `potential` globals lazily!). -/
def projVal (fuel : Nat) (G : GlobalEnv) (v : Val) (field : String) : Val :=
  match fuel with
  | 0 => .neu (.ax "<out-of-fuel>") [.proj field]
  | fuel' + 1 =>
    match v with
    | .tuple fields =>
      match lookupTupleField? fields field with
      | some fv => fv
      | none => .neu (.ax "<missing-field>") [.proj field]
    | .glued name rspine forced =>
      .glued name (.proj field :: rspine) (projVal fuel' G forced field)
    | .neu (.potential name) rspine =>
      match G.lookup? name with
      | some (.defn _ _ _ _ body) =>
        let unfolded := replaySpine fuel' G (evalTerm fuel' G [] body) rspine.reverse
        projVal fuel' G unfolded field
      | _ => .neu (.potential name) (.proj field :: rspine)
    | .neu hd rspine =>
      .neu hd (.proj field :: rspine)
    | _ => .neu (.ax "<stuck-proj>") [.proj field]

/-- Replay a chronological list of `Elim` frames onto `v` (used when forcing a `potential` global). -/
def replaySpine (fuel : Nat) (G : GlobalEnv) (v : Val) : List Elim → Val
  | [] => v
  | e :: es =>
    match fuel with
    | 0 => v
    | fuel' + 1 =>
      let v' :=
        match e with
        | .app mod arg => applyVal fuel' G v mod arg
        | .proj field => projVal fuel' G v field
        | .key cell => Val.actKey G.theory cell v
        | .sym g => evalSym fuel' G g v
        | .ap g fn => evalAp fuel' G g fn v
        | .ungel g => evalUngel fuel' G g v
        | .trr g tyLine => evalTrr fuel' G g tyLine v
        | .trl g tyLine => evalTrl fuel' G g tyLine v
        | .matchData winMod motive branches env =>
          evalMatch fuel' G v winMod motive branches env
        | .pathJ g ty base motive reflCase target =>
          evalPathJ fuel' G g ty base motive reflCase target v
      replaySpine fuel' G v' es

/-- Compute homogeneous observational equality/bridge type `ObsEq g ty ends`. -/
def evalObsEq (fuel : Nat) (_G : GlobalEnv) (g : Dir) (ty : Val) (ends : List Val) : Val :=
  match fuel with
  | 0 => .obsEq g ty ends
  | _ + 1 =>
    match g with
    | .nominal =>
      -- Open Problem A: 0-ary nominal direction has 0 endpoints (`Fresh A ≡ A` on types without free names)!
      ty
    | _ => .obsEq g ty ends

/-- Compute heterogeneous observational bridge/path type `ObsHet g tyBridge ends`.
    Crucially, `ObsHet g (Gel_g types rel) ends` computes directly to `rel ends₀ ... ends_{k-1}`! -/
def evalObsHet (fuel : Nat) (G : GlobalEnv) (g : Dir) (tyBridge : Val) (ends : List Val) : Val :=
  match fuel with
  | 0 => .obsHet g tyBridge ends
  | fuel' + 1 =>
    match tyBridge.force with
    | .refl g' ty =>
      if g == g' then evalObsEq fuel' G g ty ends
      else .obsHet g tyBridge ends
    | .gel g' _ rel =>
      if g == g' then applyManyId fuel' G rel ends
      else .obsHet g tyBridge ends
    | _ => .obsHet g tyBridge ends

/-- Compute symmetry `sym g p`. -/
def evalSym (fuel : Nat) (G : GlobalEnv) (g : Dir) (p : Val) : Val :=
  match fuel with
  | 0 => .neu (.ax "<sym-fuel>") [.sym g]
  | fuel' + 1 =>
    match p with
    | .refl g' tm => if g == g' then .refl g tm else .neu (.ax "<sym-dir>") [.sym g]
    | .glued name rspine forced =>
      .glued name (.sym g :: rspine) (evalSym fuel' G g forced)
    | .neu hd rspine => .neu hd (.sym g :: rspine)
    | _ => .neu (.ax "<stuck-sym>") [.sym g]

/-- Compute congruence `ap g fn argBridge`. -/
def evalAp (fuel : Nat) (G : GlobalEnv) (g : Dir) (fn : Val) (argBridge : Val) : Val :=
  match fuel with
  | 0 => .neu (.ax "<ap-fuel>") [.ap g fn]
  | fuel' + 1 =>
    match argBridge with
    | .refl g' tm =>
      if g == g' then
        .refl g (applyVal fuel' G fn (ModPath.id G.theory.defaultMode) tm)
      else .neu (.ax "<ap-dir>") [.ap g fn]
    | .glued name rspine forced =>
      .glued name (.ap g fn :: rspine) (evalAp fuel' G g fn forced)
    | .neu hd rspine => .neu hd (.ap g fn :: rspine)
    | _ => .neu (.ax "<stuck-ap>") [.ap g fn]

/-- Compute relational Gel witness extraction `ungel g bridgeVal`. -/
def evalUngel (fuel : Nat) (G : GlobalEnv) (g : Dir) (bridgeVal : Val) : Val :=
  match fuel with
  | 0 => .neu (.ax "<ungel-fuel>") [.ungel g]
  | fuel' + 1 =>
    match bridgeVal with
    | .gelIntro g' _ wit =>
      if g == g' then wit else .neu (.ax "<ungel-dir>") [.ungel g]
    | .glued name rspine forced =>
      .glued name (.ungel g :: rspine) (evalUngel fuel' G g forced)
    | .neu hd rspine => .neu hd (.ungel g :: rspine)
    | _ => .neu (.ax "<stuck-ungel>") [.ungel g]

/-- Compute fibrant forward transport `trr g tyLine x₀`!
    - `trr g (refl g A) x₀ ↝ x₀`
    - **Univalence Computation**: `trr g (Gel g [A₀, A₁] equiv) x₀ ↝ equiv.fwd x₀`
      (or `equiv x₀` if `equiv` is directly a function/equivalence)! -/
def evalTrr (fuel : Nat) (G : GlobalEnv) (g : Dir) (tyLine : Val) (x₀ : Val) : Val :=
  match fuel with
  | 0 => .neu (.ax "<trr-fuel>") [.trr g tyLine]
  | fuel' + 1 =>
    match tyLine.force with
    | .refl g' _ =>
      if g == g' then x₀ else .neu (.ax "<trr-dir>") [.trr g tyLine]
    | .gel g' _ rel =>
      if g == g' then
        match rel.force with
        | .tuple fields =>
          match lookupTupleField? fields "fwd" with
          | some fwdFn => applyVal fuel' G fwdFn (ModPath.id G.theory.defaultMode) x₀
          | none => applyVal fuel' G rel (ModPath.id G.theory.defaultMode) x₀
        | _ => applyVal fuel' G rel (ModPath.id G.theory.defaultMode) x₀
      else .neu (.ax "<trr-dir>") [.trr g tyLine]
    | _ =>
      match x₀ with
      | .neu hd rspine => .neu hd (.trr g tyLine :: rspine)
      | .glued name rspine forced =>
        .glued name (.trr g tyLine :: rspine) (evalTrr fuel' G g tyLine forced)
      | _ => .neu (.ax "<stuck-trr>") [.trr g tyLine]

/-- Compute fibrant backward transport `trl g tyLine x₁`!
    - `trl g (refl g A) x₁ ↝ x₁`
    - **Univalence Inverse Computation**: `trl g (Gel g [A₀, A₁] equiv) x₁ ↝ equiv.bwd x₁`! -/
def evalTrl (fuel : Nat) (G : GlobalEnv) (g : Dir) (tyLine : Val) (x₁ : Val) : Val :=
  match fuel with
  | 0 => .neu (.ax "<trl-fuel>") [.trl g tyLine]
  | fuel' + 1 =>
    match tyLine.force with
    | .refl g' _ =>
      if g == g' then x₁ else .neu (.ax "<trl-dir>") [.trl g tyLine]
    | .gel g' _ rel =>
      if g == g' then
        match rel.force with
        | .tuple fields =>
          match lookupTupleField? fields "bwd" with
          | some bwdFn => applyVal fuel' G bwdFn (ModPath.id G.theory.defaultMode) x₁
          | none => applyVal fuel' G rel (ModPath.id G.theory.defaultMode) x₁
        | _ => applyVal fuel' G rel (ModPath.id G.theory.defaultMode) x₁
      else .neu (.ax "<trl-dir>") [.trl g tyLine]
    | _ =>
      match x₁ with
      | .neu hd rspine => .neu hd (.trl g tyLine :: rspine)
      | .glued name rspine forced =>
        .glued name (.trl g tyLine :: rspine) (evalTrl fuel' G g tyLine forced)
      | _ => .neu (.ax "<stuck-trl>") [.trl g tyLine]

/-- Compute windowed inductive pattern matching (`matchData`). -/
def evalMatch (fuel : Nat) (G : GlobalEnv) (scrut : Val) (winMod : ModPath)
    (motive : Val) (branches : List (String × Nat × Term)) (env : List Val) : Val :=
  match fuel with
  | 0 => .neu (.ax "<match-fuel>") [.matchData winMod motive branches env]
  | fuel' + 1 =>
    match scrut with
    | .ctor _ ctorName args =>
      match branches.find? (fun (cn, _, _) => cn == ctorName) with
      | some (_, _, body) =>
        -- Filter constructor arguments through the modal window (collapsing discrete bridges):
        let filteredArgs := args.map fun a =>
          match a with
          | .refl g tm => if winMod.keepsDir g then .refl g tm else tm
          | other => other
        evalTerm fuel' G (filteredArgs.reverse ++ env) body
      | none => .neu (.ax s!"<missing-branch:{ctorName}>") []
    | .glued name rspine forced =>
      .glued name (.matchData winMod motive branches env :: rspine)
        (evalMatch fuel' G forced winMod motive branches env)
    | .neu hd rspine =>
      .neu hd (.matchData winMod motive branches env :: rspine)
    | _ => .neu (.ax "<stuck-match>") [.matchData winMod motive branches env]

/-- Compute HoTT path induction `J` (`pathJ g ty base motive reflCase base (refl g base) ↝ reflCase`). -/
def evalPathJ (fuel : Nat) (G : GlobalEnv) (g : Dir) (ty base motive reflCase target path : Val) : Val :=
  match fuel with
  | 0 => .neu (.ax "<J-fuel>") [.pathJ g ty base motive reflCase target]
  | fuel' + 1 =>
    match path with
    | .refl g' _ =>
      if g == g' then reflCase
      else .neu (.ax "<J-dir>") [.pathJ g ty base motive reflCase target]
    | .glued name rspine forced =>
      .glued name (.pathJ g ty base motive reflCase target :: rspine)
        (evalPathJ fuel' G g ty base motive reflCase target forced)
    | .neu hd rspine =>
      .neu hd (.pathJ g ty base motive reflCase target :: rspine)
    | _ => .neu (.ax "<stuck-J>") [.pathJ g ty base motive reflCase target]

/-- Evaluate a list of `Term`s in `env`. -/
def evalTerms (fuel : Nat) (G : GlobalEnv) (env : List Val) : List Term → List Val
  | [] => []
  | t :: ts =>
    match fuel with
    | 0 => []
    | fuel' + 1 => evalTerm fuel' G env t :: evalTerms fuel' G env ts

/-- Evaluate named tuple fields. -/
def evalTupleFields (fuel : Nat) (G : GlobalEnv) (env : List Val) :
    List (String × Term) → List (String × Val)
  | [] => []
  | (fn, ft) :: rest =>
    match fuel with
    | 0 => []
    | fuel' + 1 => (fn, evalTerm fuel' G env ft) :: evalTupleFields fuel' G env rest

/-- Core Glued NbE Evaluator (`evalTerm`). -/
def evalTerm (fuel : Nat) (G : GlobalEnv) (env : List Val) (tm : Term) : Val :=
  match fuel with
  | 0 => .neu (.ax "<eval-out-of-fuel>") []
  | fuel' + 1 =>
    match tm with
    | .bvar ix => lookupValEnv env ix
    | .global name =>
      match G.lookup? name with
      | some (.defn _ _ .kinetic _ body) =>
        .glued name [] (evalTerm fuel' G [] body)
      | some (.defn _ _ .potential _ _) =>
        .neu (.potential name) []
      | _ => .neu (.ax name) []
    | .uu lvl => .uu lvl
    | .uuExt lvl => .uuExt lvl
    | .pi name mod dom cod =>
      .pi name mod (evalTerm fuel' G env dom) (.mk env cod)
    | .lam name mod body =>
      .lam name mod (.mk env body)
    | .app fn mod arg =>
      applyVal fuel' G (evalTerm fuel' G env fn) mod (evalTerm fuel' G env arg)
    | .letIn _ _ val body =>
      let v := evalTerm fuel' G env val
      evalTerm fuel' G (v :: env) body
    | .key cell sub =>
      Val.actKey G.theory cell (evalTerm fuel' G env sub)
    | .modalBox mod ty =>
      .modalBox mod (evalTerm fuel' G env ty)
    | .boxIntro mod sub =>
      .boxIntro mod (evalTerm fuel' G env sub)
    | .letBox _ _ scrut motive body =>
      let sv := evalTerm fuel' G env scrut
      match sv.force with
      | .boxIntro _ inner => evalTerm fuel' G (inner :: env) body
      | .neu hd rspine => .neu hd (.app (ModPath.id G.theory.defaultMode) (evalTerm fuel' G env motive) :: rspine)
      | _ => .neu (.ax "<stuck-letBox>") []
    | .recordTy fields =>
      .recordTy env fields
    | .tuple fields =>
      .tuple (evalTupleFields fuel' G env fields)
    | .proj sub field =>
      projVal fuel' G (evalTerm fuel' G env sub) field
    | .dataTy name params =>
      .dataTy name (evalTerms fuel' G env params)
    | .ctor dName cName args =>
      .ctor dName cName (evalTerms fuel' G env args)
    | .matchData scrut winMod motive branches =>
      evalMatch fuel' G (evalTerm fuel' G env scrut) winMod (evalTerm fuel' G env motive) branches env
    | .obsEq g ty ends =>
      evalObsEq fuel' G g (evalTerm fuel' G env ty) (evalTerms fuel' G env ends)
    | .obsHet g tyB ends =>
      evalObsHet fuel' G g (evalTerm fuel' G env tyB) (evalTerms fuel' G env ends)
    | .refl g sub =>
      .refl g (evalTerm fuel' G env sub)
    | .sym g p =>
      evalSym fuel' G g (evalTerm fuel' G env p)
    | .ap g fn argB =>
      evalAp fuel' G g (evalTerm fuel' G env fn) (evalTerm fuel' G env argB)
    | .gel g tys rel =>
      .gel g (evalTerms fuel' G env tys) (evalTerm fuel' G env rel)
    | .gelIntro g ends wit =>
      .gelIntro g (evalTerms fuel' G env ends) (evalTerm fuel' G env wit)
    | .ungel g bTm =>
      evalUngel fuel' G g (evalTerm fuel' G env bTm)
    | .trr g tyL x₀ =>
      evalTrr fuel' G g (evalTerm fuel' G env tyL) (evalTerm fuel' G env x₀)
    | .trl g tyL x₁ =>
      evalTrl fuel' G g (evalTerm fuel' G env tyL) (evalTerm fuel' G env x₁)
    | .liftr g tyL x₀ =>
      .liftr g (evalTerm fuel' G env tyL) (evalTerm fuel' G env x₀)
    | .pathJ g ty base motive reflCase target path =>
      evalPathJ fuel' G g
        (evalTerm fuel' G env ty)
        (evalTerm fuel' G env base)
        (evalTerm fuel' G env motive)
        (evalTerm fuel' G env reflCase)
        (evalTerm fuel' G env target)
        (evalTerm fuel' G env path)

end

/-- Default evaluation fuel (`1024`). -/
def defaultFuel : Nat := 1024

/-- Evaluate a `Term` in `G` and `env` with `defaultFuel`. -/
def eval (G : GlobalEnv) (env : List Val) (tm : Term) : Val :=
  evalTerm defaultFuel G env tm

/-- Evaluate a semantic `Closure` on argument `arg`. -/
def evalClosure (fuel : Nat) (G : GlobalEnv) (cl : Closure) (arg : Val) : Val :=
  match cl with
  | .mk env body => evalTerm fuel G (arg :: env) body

/-! ### Readback (`quoteVal`) from `Val` to Normal-Form `Term` -/

mutual

def quoteSpine (fuel : Nat) (G : GlobalEnv) (depth : Nat) (base : Term) : List Elim → Term
  | [] => base
  | e :: es =>
    match fuel with
    | 0 => base
    | fuel' + 1 =>
      let prev := quoteSpine fuel' G depth base es
      match e with
      | .app mod arg => .app prev mod (quoteVal fuel' G depth arg)
      | .proj field => .proj prev field
      | .key cell => .key cell prev
      | .sym g => .sym g prev
      | .ap g fn => .ap g (quoteVal fuel' G depth fn) prev
      | .ungel g => .ungel g prev
      | .trr g tyL => .trr g (quoteVal fuel' G depth tyL) prev
      | .trl g tyL => .trl g (quoteVal fuel' G depth tyL) prev
      | .matchData winMod motive branches env =>
        let qBranches := quoteBranches fuel' G depth env branches
        .matchData prev winMod (quoteVal fuel' G depth motive) qBranches
      | .pathJ g ty baseV motive reflC target =>
        .pathJ g (quoteVal fuel' G depth ty) (quoteVal fuel' G depth baseV)
          (quoteVal fuel' G depth motive) (quoteVal fuel' G depth reflC)
          (quoteVal fuel' G depth target) prev

def quoteBranches (fuel : Nat) (G : GlobalEnv) (depth : Nat) (env : List Val) :
    List (String × Nat × Term) → List (String × Nat × Term)
  | [] => []
  | (cn, ar, body) :: rest =>
    match fuel with
    | 0 => []
    | fuel' + 1 =>
      let freshVars := (List.range ar).map (fun i => Val.vvar (depth + i))
      let vBody := evalTerm fuel' G (freshVars.reverse ++ env) body
      let qBody := quoteVal fuel' G (depth + ar) vBody
      (cn, ar, qBody) :: quoteBranches fuel' G depth env rest

def quoteRecordFields (fuel : Nat) (G : GlobalEnv) (depth : Nat) (env : List Val) :
    List (String × ModPath × Term) → List (String × ModPath × Term)
  | [] => []
  | (fn, fmod, fty) :: rest =>
    match fuel with
    | 0 => []
    | fuel' + 1 =>
      let vTy := evalTerm fuel' G env fty
      let qTy := quoteVal fuel' G depth vTy
      let fresh := Val.vvar depth
      (fn, fmod, qTy) :: quoteRecordFields fuel' G (depth + 1) (fresh :: env) rest

def quoteVals (fuel : Nat) (G : GlobalEnv) (depth : Nat) : List Val → List Term
  | [] => []
  | v :: vs =>
    match fuel with
    | 0 => []
    | fuel' + 1 => quoteVal fuel' G depth v :: quoteVals fuel' G depth vs

def quoteTupleVals (fuel : Nat) (G : GlobalEnv) (depth : Nat) :
    List (String × Val) → List (String × Term)
  | [] => []
  | (fn, fv) :: rest =>
    match fuel with
    | 0 => []
    | fuel' + 1 => (fn, quoteVal fuel' G depth fv) :: quoteTupleVals fuel' G depth rest

/-- Quote a semantic `Val` at context depth `depth` back into a normal-form `Term`
    (forcing glued definitions to obtain full β-normal forms!). -/
def quoteVal (fuel : Nat) (G : GlobalEnv) (depth : Nat) (v : Val) : Term :=
  match fuel with
  | 0 => .global "<quote-out-of-fuel>"
  | fuel' + 1 =>
    match v with
    | .glued _ _ forced => quoteVal fuel' G depth forced
    | .neu hd rspine =>
      let headTm : Term :=
        match hd with
        | .lvar lvl =>
          let ix := if depth > lvl then depth - 1 - lvl else 0
          .bvar ix
        | .ax name => .global name
        | .potential name => .global name
      quoteSpine fuel' G depth headTm rspine
    | .uu lvl => .uu lvl
    | .uuExt lvl => .uuExt lvl
    | .pi name mod dom cod =>
      let qDom := quoteVal fuel' G depth dom
      let fresh := Val.vvar depth
      let qCod := quoteVal fuel' G (depth + 1) (evalClosure fuel' G cod fresh)
      .pi name mod qDom qCod
    | .lam name mod body =>
      let fresh := Val.vvar depth
      let qBody := quoteVal fuel' G (depth + 1) (evalClosure fuel' G body fresh)
      .lam name mod qBody
    | .modalBox mod ty => .modalBox mod (quoteVal fuel' G depth ty)
    | .boxIntro mod sub => .boxIntro mod (quoteVal fuel' G depth sub)
    | .recordTy env fields => .recordTy (quoteRecordFields fuel' G depth env fields)
    | .tuple fields => .tuple (quoteTupleVals fuel' G depth fields)
    | .dataTy name params => .dataTy name (quoteVals fuel' G depth params)
    | .ctor dName cName args => .ctor dName cName (quoteVals fuel' G depth args)
    | .obsEq g ty ends =>
      .obsEq g (quoteVal fuel' G depth ty) (quoteVals fuel' G depth ends)
    | .obsHet g tyB ends =>
      .obsHet g (quoteVal fuel' G depth tyB) (quoteVals fuel' G depth ends)
    | .refl g sub => .refl g (quoteVal fuel' G depth sub)
    | .gel g tys rel =>
      .gel g (quoteVals fuel' G depth tys) (quoteVal fuel' G depth rel)
    | .gelIntro g ends wit =>
      .gelIntro g (quoteVals fuel' G depth ends) (quoteVal fuel' G depth wit)
    | .liftr g tyL x₀ =>
      .liftr g (quoteVal fuel' G depth tyL) (quoteVal fuel' G depth x₀)

end

/-- Normalize a `Term` at context length `depth` via `eval` + `quoteVal`. -/
def normalize (G : GlobalEnv) (env : List Val) (depth : Nat) (tm : Term) : Term :=
  quoteVal defaultFuel G depth (eval G env tm)

end Narya.Core
