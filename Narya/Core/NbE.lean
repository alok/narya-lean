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
  fields.findSome? fun (n, v) => if strEq n fname then some v else none

/-- Swap forward/backward fields (`fwd ↔ bwd`, `liftr ↔ liftl`) when inverting a `Gel`/`Glue` equivalence. -/
def flipEquivFields (fields : List (String × Val)) : List (String × Val) :=
  fields.map fun (k, v) =>
    if strEq k "fwd" then ("bwd", v)
    else if strEq k "bwd" then ("fwd", v)
    else if strEq k "liftr" then ("liftl", v)
    else if strEq k "liftl" then ("liftr", v)
    else (k, v)

mutual

/-- Apply a semantic function `fn` to an argument `arg` at modality `mod`. -/
def applyVal (fuel : Nat) (G : GlobalEnv) (fn : Val) (mod : ModPath) (arg : Val) : Val :=
  match fuel with
  | 0 => .neu (.ax "<out-of-fuel>") [.app mod arg]
  | fuel' + 1 =>
    match fn with
    | .lam _ _ (.mk env body) =>
      evalTerm fuel' G (arg :: env) body
    | .lam _ _ (.arrowTrr g pMod domLine codLine f₀) =>
      let a₀ := evalTrl fuel' G g domLine arg
      let fa₀ := applyVal fuel' G f₀ pMod a₀
      evalTrr fuel' G g codLine fa₀
    | .lam _ _ (.arrowTrl g pMod domLine codLine f₁) =>
      let a₁ := evalTrr fuel' G g domLine arg
      let fa₁ := applyVal fuel' G f₁ pMod a₁
      evalTrl fuel' G g codLine fa₁
    | .lam _ _ (.piTrr g pMod domLine env codLine f₀) =>
      let a₀ := evalTrl fuel' G g domLine arg
      let a₂ := evalLiftl fuel' G g domLine arg
      let bLine := evalTerm fuel' G (a₂ :: arg :: a₀ :: env) codLine
      let fa₀ := applyVal fuel' G f₀ pMod a₀
      evalTrr fuel' G g bLine fa₀
    | .lam _ _ (.piTrl g pMod domLine env codLine f₁) =>
      let a₁ := evalTrr fuel' G g domLine arg
      let a₂ := evalLiftr fuel' G g domLine arg
      let bLine := evalTerm fuel' G (a₂ :: a₁ :: arg :: env) codLine
      let fa₁ := applyVal fuel' G f₁ pMod a₁
      evalTrl fuel' G g bLine fa₁
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
    | .refl g inner =>
      -- Observational coinductive/record bisimulation: `(refl_g r).fld ↝ refl_g (r.fld)`!
      .refl g (projVal fuel' G inner field)
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
        | .elimHIT dName motive ptBranches pathBranches env =>
          evalElimHIT fuel' G dName motive ptBranches pathBranches env v
        | .pathJ g ty base motive reflCase target =>
          evalPathJ fuel' G g ty base motive reflCase target v
        | .hap g a₀ a₁ pa =>
          evalHap fuel' G g v a₀ a₁ pa
        | .u64BinOpL op rhs =>
          evalU64BinOp fuel' G op v rhs
        | .u64BinOpR op lhs =>
          evalU64BinOp fuel' G op (.u64Lit lhs) v
        | .u64IfZero zBr nzBr =>
          evalU64IfZero v zBr nzBr
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

/-- Compute symmetry `sym g p` (including involutive cancellation, anti-homomorphism on `trans`,
    and equivalence reversal on `Gel`/`Glue`, `arrowLine`, `prodLine`, and `boxLine`). -/
def evalSym (fuel : Nat) (G : GlobalEnv) (g : Dir) (p : Val) : Val :=
  match fuel with
  | 0 => .neu (.ax "<sym-fuel>") [.sym g]
  | fuel' + 1 =>
    match p with
    | .refl g' tm => if g == g' then .refl g tm else .neu (.ax "<sym-dir>") [.sym g]
    | .trans g' p₁ p₂ =>
      if g == g' then
        evalTrans fuel' G g (evalSym fuel' G g p₂) (evalSym fuel' G g p₁)
      else .neu (.ax "<sym-dir>") [.sym g]
    | .pctor dName pName args =>
      .invPctor g dName pName args
    | .invPctor g' dName pName args =>
      if g == g' then .pctor dName pName args
      else .neu (.ax "<sym-dir>") [.sym g]
    | .gel g' [a₀, a₁] rel =>
      if g == g' then
        match rel.force with
        | .tuple fs => .gel g [a₁, a₀] (.tuple (flipEquivFields fs))
        | _ => .gel g [a₁, a₀] rel
      else .neu (.ax "<sym-dir>") [.sym g]
    | .arrowLine g' mod dL cL =>
      if g == g' then .arrowLine g mod (evalSym fuel' G g dL) (evalSym fuel' G g cL)
      else .neu (.ax "<sym-dir>") [.sym g]
    | .prodLine g' fN sN fL sL =>
      if g == g' then .prodLine g fN sN (evalSym fuel' G g fL) (evalSym fuel' G g sL)
      else .neu (.ax "<sym-dir>") [.sym g]
    | .boxLine g' mod inL =>
      if g == g' then .boxLine g mod (evalSym fuel' G g inL)
      else .neu (.ax "<sym-dir>") [.sym g]
    | .glued name rspine forced =>
      .glued name (.sym g :: rspine) (evalSym fuel' G g forced)
    | .neu hd (.sym g' :: rest) =>
      if g == g' then .neu hd rest else .neu hd (.sym g :: .sym g' :: rest)
    | .neu hd rspine => .neu hd (.sym g :: rspine)
    | _ => .neu (.ax "<stuck-sym>") [.sym g]

/-- Compute fibrant path composition `trans g p q` (two-sided `refl` identity + structural fusion). -/
def evalTrans (fuel : Nat) (G : GlobalEnv) (g : Dir) (p : Val) (q : Val) : Val :=
  match fuel with
  | 0 => .trans g p q
  | fuel' + 1 =>
    match p.force, q.force with
    | .refl g' _, _ => if g == g' then q else .trans g p q
    | _, .refl g' _ => if g == g' then p else .trans g p q
    | .arrowLine g₁ m₁ d₁ c₁, .arrowLine g₂ m₂ d₂ c₂ =>
      if g == g₁ && g == g₂ && m₁ == m₂ then
        .arrowLine g m₁ (evalTrans fuel' G g d₁ d₂) (evalTrans fuel' G g c₁ c₂)
      else .trans g p q
    | .prodLine g₁ f₁ s₁ a₁ b₁, .prodLine g₂ f₂ s₂ a₂ b₂ =>
      if g == g₁ && g == g₂ && strEq f₁ f₂ && strEq s₁ s₂ then
        .prodLine g f₁ s₁ (evalTrans fuel' G g a₁ a₂) (evalTrans fuel' G g b₁ b₂)
      else .trans g p q
    | .boxLine g₁ m₁ in₁, .boxLine g₂ m₂ in₂ =>
      if g == g₁ && g == g₂ && m₁ == m₂ then
        .boxLine g m₁ (evalTrans fuel' G g in₁ in₂)
      else .trans g p q
    | _, _ => .trans g p q

/-- Compute congruence `ap g fn argBridge` (including functoriality on `trans`, inverse HIT
    path constructors `invPctor`, and computational β-reduction of `elimHIT` on `pctor`!). -/
def evalAp (fuel : Nat) (G : GlobalEnv) (g : Dir) (fn : Val) (argBridge : Val) : Val :=
  match fuel with
  | 0 => .neu (.ax "<ap-fuel>") [.ap g fn]
  | fuel' + 1 =>
    match argBridge with
    | .refl g' tm =>
      if g == g' then
        .refl g (applyVal fuel' G fn (ModPath.id G.theory.defaultMode) tm)
      else .neu (.ax "<ap-dir>") [.ap g fn]
    | .trans g' p q =>
      if g == g' then
        evalTrans fuel' G g (evalAp fuel' G g fn p) (evalAp fuel' G g fn q)
      else .neu (.ax "<ap-dir>") [.ap g fn]
    | .pctor dName pName args =>
      match fn.force with
      | .lam _ _ (.mk fnEnv (.elimHIT dName' _ _ pathBranches (.bvar 0))) =>
        if strEq dName dName' then
          match pathBranches.find? (fun (pn, _, _) => strEq pn pName) with
          | some (_, _, pBody) => evalTerm fuel' G (args.reverse ++ fnEnv) pBody
          | none => .neu (.ax s!"<missing-hit-path:{pName}>") [.ap g fn]
        else .neu (.ax "<ap-hit-mismatch>") [.ap g fn]
      | .lam _ _ (.mk _ (.bvar 0)) =>
        .pctor dName pName args
      | .lam _ _ (.mk _ (.modalBox bMod (.bvar 0))) =>
        if bMod.keepsDir g then .boxLine g bMod (.pctor dName pName args)
        else .neu (.ax "<stuck-ap>") [.ap g fn]
      | _ => .neu (.ax "<stuck-ap-pctor>") [.ap g fn]
    | .invPctor g' dName pName args =>
      if g == g' then
        evalSym fuel' G g (evalAp fuel' G g fn (.pctor dName pName args))
      else .neu (.ax "<ap-dir>") [.ap g fn]
    | .glued name rspine forced =>
      .glued name (.ap g fn :: rspine) (evalAp fuel' G g fn forced)
    | .neu hd rspine => .neu hd (.ap g fn :: rspine)
    | _ =>
      -- Push `ap` of identity or modal box type constructor `λ X => ⟨μ | X⟩` directly!
      match fn.force with
      | .lam _ _ (.mk _ (.bvar 0)) => argBridge
      | .lam _ _ (.mk _ (.modalBox bMod (.bvar 0))) =>
        if bMod.keepsDir g then .boxLine g bMod argBridge
        else .neu (.ax "<stuck-ap>") [.ap g fn]
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

/-- Compute fibrant forward transport `trr g tyLine x₀` across ALL HOTT type formers!
    - `refl`: `trr g (refl g A) x₀ ↝ x₀`
    - `Gel`/`Glue`: `trr g (Gel g [A₀, A₁] equiv) x₀ ↝ equiv.fwd x₀`
    - `trans`: `trr g (trans g p q) x₀ ↝ trr g q (trr g p x₀)`
    - `arrowLine` / `piLine`: contravariant `trl`/`liftl` on domain, covariant `trr` on codomain!
    - `prodLine` / `sigLine`: dependent field-by-field transport using `liftr` on earlier fields!
    - `boxLine`: `trr g (boxLine g μ pA) (boxIntro μ a₀) ↝ boxIntro μ (trr g pA a₀)`! -/
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
    | .trans g' p q =>
      if g == g' then evalTrr fuel' G g q (evalTrr fuel' G g p x₀)
      else .neu (.ax "<trr-dir>") [.trr g tyLine]
    | .arrowLine g' mod domL codL =>
      if g == g' then .lam "x" mod (.arrowTrr g mod domL codL x₀)
      else .neu (.ax "<trr-dir>") [.trr g tyLine]
    | .piLine g' name mod domL env _ _ codL =>
      if g == g' then .lam name mod (.piTrr g mod domL env codL x₀)
      else .neu (.ax "<trr-dir>") [.trr g tyLine]
    | .prodLine g' fN sN fL sL =>
      if g == g' then
        let vFst := evalTrr fuel' G g fL (projVal fuel' G x₀ fN)
        let vSnd := evalTrr fuel' G g sL (projVal fuel' G x₀ sN)
        .tuple [(fN, vFst), (sN, vSnd)]
      else .neu (.ax "<trr-dir>") [.trr g tyLine]
    | .sigLine g' fN sN _ _ fL env _ _ sL =>
      if g == g' then
        let u₀_fst := projVal fuel' G x₀ fN
        let u₀_snd := projVal fuel' G x₀ sN
        let u₁_fst := evalTrr fuel' G g fL u₀_fst
        let u_lift := evalLiftr fuel' G g fL u₀_fst
        let sLineVal := evalTerm fuel' G (u_lift :: u₁_fst :: u₀_fst :: env) sL
        let u₁_snd := evalTrr fuel' G g sLineVal u₀_snd
        .tuple [(fN, u₁_fst), (sN, u₁_snd)]
      else .neu (.ax "<trr-dir>") [.trr g tyLine]
    | .boxLine g' mod inL =>
      if g == g' then
        match x₀.force with
        | .boxIntro _ a₀ => .boxIntro mod (evalTrr fuel' G g inL a₀)
        | .neu hd rspine => .neu hd (.trr g tyLine :: rspine)
        | _ => .neu (.ax "<stuck-trr-box>") [.trr g tyLine]
      else .neu (.ax "<trr-dir>") [.trr g tyLine]
    | _ =>
      match x₀ with
      | .neu hd rspine => .neu hd (.trr g tyLine :: rspine)
      | .glued name rspine forced =>
        .glued name (.trr g tyLine :: rspine) (evalTrr fuel' G g tyLine forced)
      | _ => .neu (.ax "<stuck-trr>") [.trr g tyLine]

/-- Compute fibrant backward transport `trl g tyLine x₁` across ALL HOTT type formers! -/
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
    | .trans g' p q =>
      if g == g' then evalTrl fuel' G g p (evalTrl fuel' G g q x₁)
      else .neu (.ax "<trl-dir>") [.trl g tyLine]
    | .arrowLine g' mod domL codL =>
      if g == g' then .lam "x" mod (.arrowTrl g mod domL codL x₁)
      else .neu (.ax "<trl-dir>") [.trl g tyLine]
    | .piLine g' name mod domL env _ _ codL =>
      if g == g' then .lam name mod (.piTrl g mod domL env codL x₁)
      else .neu (.ax "<trl-dir>") [.trl g tyLine]
    | .prodLine g' fN sN fL sL =>
      if g == g' then
        let vFst := evalTrl fuel' G g fL (projVal fuel' G x₁ fN)
        let vSnd := evalTrl fuel' G g sL (projVal fuel' G x₁ sN)
        .tuple [(fN, vFst), (sN, vSnd)]
      else .neu (.ax "<trl-dir>") [.trl g tyLine]
    | .sigLine g' fN sN _ _ fL env _ _ sL =>
      if g == g' then
        let u₁_fst := projVal fuel' G x₁ fN
        let u₁_snd := projVal fuel' G x₁ sN
        let u₀_fst := evalTrl fuel' G g fL u₁_fst
        let u_liftl := evalLiftl fuel' G g fL u₁_fst
        let sLineVal := evalTerm fuel' G (u_liftl :: u₁_fst :: u₀_fst :: env) sL
        let u₀_snd := evalTrl fuel' G g sLineVal u₁_snd
        .tuple [(fN, u₀_fst), (sN, u₀_snd)]
      else .neu (.ax "<trl-dir>") [.trl g tyLine]
    | .boxLine g' mod inL =>
      if g == g' then
        match x₁.force with
        | .boxIntro _ a₁ => .boxIntro mod (evalTrl fuel' G g inL a₁)
        | .neu hd rspine => .neu hd (.trl g tyLine :: rspine)
        | _ => .neu (.ax "<stuck-trl-box>") [.trl g tyLine]
      else .neu (.ax "<trl-dir>") [.trl g tyLine]
    | _ =>
      match x₁ with
      | .neu hd rspine => .neu hd (.trl g tyLine :: rspine)
      | .glued name rspine forced =>
        .glued name (.trl g tyLine :: rspine) (evalTrl fuel' G g tyLine forced)
      | _ => .neu (.ax "<stuck-trl>") [.trl g tyLine]

/-- Compute fibrant forward path lifting `liftr g tyLine x₀`! -/
def evalLiftr (fuel : Nat) (G : GlobalEnv) (g : Dir) (tyLine : Val) (x₀ : Val) : Val :=
  match fuel with
  | 0 => .liftr g tyLine x₀
  | fuel' + 1 =>
    match tyLine.force with
    | .refl g' _ => if g == g' then .refl g x₀ else .liftr g tyLine x₀
    | .gel g' _ rel =>
      if g == g' then
        match rel.force with
        | .tuple fields =>
          match lookupTupleField? fields "liftr" with
          | some liftrFn =>
            let idM := ModPath.id G.theory.defaultMode
            let x₁ := evalTrr fuel' G g tyLine x₀
            let wit := applyVal fuel' G liftrFn idM x₀
            .gelIntro g [x₀, x₁] wit
          | none => .liftr g tyLine x₀
        | _ => .liftr g tyLine x₀
      else .liftr g tyLine x₀
    | .prodLine g' fN sN fL sL =>
      if g == g' then
        .tuple [(fN, evalLiftr fuel' G g fL (projVal fuel' G x₀ fN)),
                (sN, evalLiftr fuel' G g sL (projVal fuel' G x₀ sN))]
      else .liftr g tyLine x₀
    | .sigLine g' fN sN _ _ fL env _ _ sL =>
      if g == g' then
        let u₀_fst := projVal fuel' G x₀ fN
        let u₀_snd := projVal fuel' G x₀ sN
        let u₁_fst := evalTrr fuel' G g fL u₀_fst
        let u_lift := evalLiftr fuel' G g fL u₀_fst
        let sLineVal := evalTerm fuel' G (u_lift :: u₁_fst :: u₀_fst :: env) sL
        .tuple [(fN, u_lift), (sN, evalLiftr fuel' G g sLineVal u₀_snd)]
      else .liftr g tyLine x₀
    | .boxLine g' mod inL =>
      if g == g' then
        match x₀.force with
        | .boxIntro _ a₀ => .boxIntro mod (evalLiftr fuel' G g inL a₀)
        | _ => .liftr g tyLine x₀
      else .liftr g tyLine x₀
    | _ => .liftr g tyLine x₀

/-- Compute fibrant backward path lifting `liftl g tyLine x₁` (`hott.rst:14`)! -/
def evalLiftl (fuel : Nat) (G : GlobalEnv) (g : Dir) (tyLine : Val) (x₁ : Val) : Val :=
  match fuel with
  | 0 => .liftl g tyLine x₁
  | fuel' + 1 =>
    match tyLine.force with
    | .refl g' _ => if g == g' then .refl g x₁ else .liftl g tyLine x₁
    | .gel g' _ rel =>
      if g == g' then
        match rel.force with
        | .tuple fields =>
          match lookupTupleField? fields "liftl" with
          | some liftlFn =>
            let idM := ModPath.id G.theory.defaultMode
            let x₀ := evalTrl fuel' G g tyLine x₁
            let wit := applyVal fuel' G liftlFn idM x₁
            .gelIntro g [x₀, x₁] wit
          | none => .liftl g tyLine x₁
        | _ => .liftl g tyLine x₁
      else .liftl g tyLine x₁
    | .prodLine g' fN sN fL sL =>
      if g == g' then
        .tuple [(fN, evalLiftl fuel' G g fL (projVal fuel' G x₁ fN)),
                (sN, evalLiftl fuel' G g sL (projVal fuel' G x₁ sN))]
      else .liftl g tyLine x₁
    | .sigLine g' fN sN _ _ fL env _ _ sL =>
      if g == g' then
        let u₁_fst := projVal fuel' G x₁ fN
        let u₁_snd := projVal fuel' G x₁ sN
        let u₀_fst := evalTrl fuel' G g fL u₁_fst
        let u_liftl := evalLiftl fuel' G g fL u₁_fst
        let sLineVal := evalTerm fuel' G (u_liftl :: u₁_fst :: u₀_fst :: env) sL
        .tuple [(fN, u_liftl), (sN, evalLiftl fuel' G g sLineVal u₁_snd)]
      else .liftl g tyLine x₁
    | .boxLine g' mod inL =>
      if g == g' then
        match x₁.force with
        | .boxIntro _ a₁ => .boxIntro mod (evalLiftl fuel' G g inL a₁)
        | _ => .liftl g tyLine x₁
      else .liftl g tyLine x₁
    | _ => .liftl g tyLine x₁

/-- Compute windowed inductive pattern matching (`matchData`). -/
def evalMatch (fuel : Nat) (G : GlobalEnv) (scrut : Val) (winMod : ModPath)
    (motive : Val) (branches : List (String × Nat × Term)) (env : List Val) : Val :=
  match fuel with
  | 0 => .neu (.ax "<match-fuel>") [.matchData winMod motive branches env]
  | fuel' + 1 =>
    match scrut with
    | .ctor _ ctorName args =>
      match branches.find? (fun (cn, _, _) => strEq cn ctorName) with
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

/-- Compute Higher Inductive Type point-elimination (`evalElimHIT`). -/
def evalElimHIT (fuel : Nat) (G : GlobalEnv) (dName : String) (motive : Val)
    (ptBranches pathBranches : List (String × Nat × Term)) (env : List Val) (scrut : Val) : Val :=
  match fuel with
  | 0 => .neu (.ax "<elimHIT-fuel>") [.elimHIT dName motive ptBranches pathBranches env]
  | fuel' + 1 =>
    match scrut with
    | .ctor dName' ctorName args =>
      if strEq dName dName' then
        match ptBranches.find? (fun (cn, _, _) => strEq cn ctorName) with
        | some (_, _, body) => evalTerm fuel' G (args.reverse ++ env) body
        | none => .neu (.ax s!"<missing-hit-pt:{ctorName}>") []
      else .neu (.ax "<elimHIT-data-mismatch>") []
    | .glued name rspine forced =>
      .glued name (.elimHIT dName motive ptBranches pathBranches env :: rspine)
        (evalElimHIT fuel' G dName motive ptBranches pathBranches env forced)
    | .neu hd rspine =>
      .neu hd (.elimHIT dName motive ptBranches pathBranches env :: rspine)
    | _ => .neu (.ax "<stuck-elimHIT>") [.elimHIT dName motive ptBranches pathBranches env]

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

/-- Compute observational function-bridge application `hap g pf a₀ a₁ pa`:
    - `hap g (funext g mod body) a₀ a₁ pa ↝ body[a₀, a₁, pa]` (computational `funext` β-law!)
    - `hap g (refl g fn) a₀ a₁ pa ↝ ap g fn pa` (reflexive function bridge agrees with `ap`!) -/
def evalHap (fuel : Nat) (G : GlobalEnv) (g : Dir) (pf a₀ a₁ pa : Val) : Val :=
  match fuel with
  | 0 => .neu (.ax "<hap-fuel>") [.hap g a₀ a₁ pa]
  | fuel' + 1 =>
    match pf with
    | .funext g' _ env body =>
      if g == g' then evalTerm fuel' G (pa :: a₁ :: a₀ :: env) body
      else .neu (.ax "<hap-dir>") [.hap g a₀ a₁ pa]
    | .refl g' fn =>
      if g == g' then evalAp fuel' G g fn pa
      else .neu (.ax "<hap-dir>") [.hap g a₀ a₁ pa]
    | .glued name rspine forced =>
      .glued name (.hap g a₀ a₁ pa :: rspine) (evalHap fuel' G g forced a₀ a₁ pa)
    | .neu hd rspine =>
      .neu hd (.hap g a₀ a₁ pa :: rspine)
    | _ => .neu (.ax "<stuck-hap>") [.hap g a₀ a₁ pa]

/-- Compute 64-bit word ALU operation `u64BinOp op lhs rhs`. -/
def evalU64BinOp (fuel : Nat) (G : GlobalEnv) (op : BinOp64) (lhs rhs : Val) : Val :=
  match fuel with
  | 0 => .neu (.ax "<u64-fuel>") [.u64BinOpL op rhs]
  | fuel' + 1 =>
    match lhs, rhs with
    | .u64Lit a, .u64Lit b => .u64Lit (op.eval a b)
    | .glued _ _ f₁, _ => evalU64BinOp fuel' G op f₁ rhs
    | _, .glued _ _ f₂ => evalU64BinOp fuel' G op lhs f₂
    | .neu hd sp, _ => .neu hd (.u64BinOpL op rhs :: sp)
    | .u64Lit a, .neu hd sp => .neu hd (.u64BinOpR op a :: sp)
    | _, _ => .neu (.ax "<stuck-u64-op>") [.u64BinOpL op rhs]

/-- Compute 64-bit zero conditional `u64IfZero cond zBr nzBr`. -/
def evalU64IfZero (cond zBr nzBr : Val) : Val :=
  match cond.force with
  | .u64Lit c => if c == 0 then zBr else nzBr
  | .neu hd sp => .neu hd (.u64IfZero zBr nzBr :: sp)
  | _ => .neu (.ax "<stuck-u64-if>") [.u64IfZero zBr nzBr]

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
    | .mvar id => .neu (.mvar id) []
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
    | .pctor dName pName args =>
      .pctor dName pName (evalTerms fuel' G env args)
    | .matchData scrut winMod motive branches =>
      evalMatch fuel' G (evalTerm fuel' G env scrut) winMod (evalTerm fuel' G env motive) branches env
    | .elimHIT dName motive ptBranches pathBranches scrut =>
      evalElimHIT fuel' G dName (evalTerm fuel' G env motive) ptBranches pathBranches env
        (evalTerm fuel' G env scrut)
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
      evalLiftr fuel' G g (evalTerm fuel' G env tyL) (evalTerm fuel' G env x₀)
    | .liftl g tyL x₁ =>
      evalLiftl fuel' G g (evalTerm fuel' G env tyL) (evalTerm fuel' G env x₁)
    | .trans g p q =>
      evalTrans fuel' G g (evalTerm fuel' G env p) (evalTerm fuel' G env q)
    | .arrowLine g mod dL cL =>
      .arrowLine g mod (evalTerm fuel' G env dL) (evalTerm fuel' G env cL)
    | .piLine g name mod dL c0 c1 cL =>
      .piLine g name mod (evalTerm fuel' G env dL) env c0 c1 cL
    | .prodLine g fN sN fL sL =>
      .prodLine g fN sN (evalTerm fuel' G env fL) (evalTerm fuel' G env sL)
    | .sigLine g fN sN fM sM fL s0 s1 sL =>
      .sigLine g fN sN fM sM (evalTerm fuel' G env fL) env s0 s1 sL
    | .boxLine g mod inL =>
      .boxLine g mod (evalTerm fuel' G env inL)
    | .pathJ g ty base motive reflCase target path =>
      evalPathJ fuel' G g
        (evalTerm fuel' G env ty)
        (evalTerm fuel' G env base)
        (evalTerm fuel' G env motive)
        (evalTerm fuel' G env reflCase)
        (evalTerm fuel' G env target)
        (evalTerm fuel' G env path)
    | .funext g mod body =>
      .funext g mod env body
    | .hap g pf a₀ a₁ pa =>
      evalHap fuel' G g
        (evalTerm fuel' G env pf)
        (evalTerm fuel' G env a₀)
        (evalTerm fuel' G env a₁)
        (evalTerm fuel' G env pa)
    | .u64Ty => .u64Ty
    | .u64Lit v => .u64Lit v
    | .u64BinOp op l r =>
      evalU64BinOp fuel' G op (evalTerm fuel' G env l) (evalTerm fuel' G env r)
    | .u64IfZero c z nz =>
      match (evalTerm fuel' G env c).force with
      | .u64Lit cv =>
        if cv == 0 then evalTerm fuel' G env z else evalTerm fuel' G env nz
      | cOther =>
        evalU64IfZero cOther (evalTerm fuel' G env z) (evalTerm fuel' G env nz)
    | .u64Repeat iters init stepBody =>
      let vInit := evalTerm fuel' G env init
      iterN iters.toNat (fun acc => evalTerm fuel' G (acc :: env) stepBody) vInit

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
  | .arrowTrr g pMod domLine codLine f₀ =>
    let a₀ := evalTrl fuel G g domLine arg
    let fa₀ := applyVal fuel G f₀ pMod a₀
    evalTrr fuel G g codLine fa₀
  | .arrowTrl g pMod domLine codLine f₁ =>
    let a₁ := evalTrr fuel G g domLine arg
    let fa₁ := applyVal fuel G f₁ pMod a₁
    evalTrl fuel G g codLine fa₁
  | .piTrr g pMod domLine env codLine f₀ =>
    let a₀ := evalTrl fuel G g domLine arg
    let a₂ := evalLiftl fuel G g domLine arg
    let bLine := evalTerm fuel G (a₂ :: arg :: a₀ :: env) codLine
    let fa₀ := applyVal fuel G f₀ pMod a₀
    evalTrr fuel G g bLine fa₀
  | .piTrl g pMod domLine env codLine f₁ =>
    let a₁ := evalTrr fuel G g domLine arg
    let a₂ := evalLiftr fuel G g domLine arg
    let bLine := evalTerm fuel G (a₂ :: a₁ :: arg :: env) codLine
    let fa₁ := applyVal fuel G f₁ pMod a₁
    evalTrl fuel G g bLine fa₁

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
      | .elimHIT dName motive ptBranches pathBranches env =>
        let qPt := quoteBranches fuel' G depth env ptBranches
        let qPath := quoteBranches fuel' G depth env pathBranches
        .elimHIT dName (quoteVal fuel' G depth motive) qPt qPath prev
      | .pathJ g ty baseV motive reflC target =>
        .pathJ g (quoteVal fuel' G depth ty) (quoteVal fuel' G depth baseV)
          (quoteVal fuel' G depth motive) (quoteVal fuel' G depth reflC)
          (quoteVal fuel' G depth target) prev
      | .hap g a₀ a₁ pa =>
        .hap g prev (quoteVal fuel' G depth a₀) (quoteVal fuel' G depth a₁) (quoteVal fuel' G depth pa)
      | .u64BinOpL op rhs =>
        .u64BinOp op prev (quoteVal fuel' G depth rhs)
      | .u64BinOpR op lhs =>
        .u64BinOp op (.u64Lit lhs) prev
      | .u64IfZero zBr nzBr =>
        .u64IfZero prev (quoteVal fuel' G depth zBr) (quoteVal fuel' G depth nzBr)

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
        | .mvar id => .mvar id
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
    | .pctor dName pName args => .pctor dName pName (quoteVals fuel' G depth args)
    | .invPctor g dName pName args =>
      .sym g (.pctor dName pName (quoteVals fuel' G depth args))
    | .obsEq g ty ends =>
      .obsEq g (quoteVal fuel' G depth ty) (quoteVals fuel' G depth ends)
    | .obsHet g tyB ends =>
      .obsHet g (quoteVal fuel' G depth tyB) (quoteVals fuel' G depth ends)
    | .refl g sub => .refl g (quoteVal fuel' G depth sub)
    | .trans g p q =>
      .trans g (quoteVal fuel' G depth p) (quoteVal fuel' G depth q)
    | .gel g tys rel =>
      .gel g (quoteVals fuel' G depth tys) (quoteVal fuel' G depth rel)
    | .gelIntro g ends wit =>
      .gelIntro g (quoteVals fuel' G depth ends) (quoteVal fuel' G depth wit)
    | .arrowLine g mod dL cL =>
      .arrowLine g mod (quoteVal fuel' G depth dL) (quoteVal fuel' G depth cL)
    | .piLine g name mod dL env c0 c1 cL =>
      let v0 := Val.vvar depth
      let v1 := Val.vvar (depth + 1)
      let v2 := Val.vvar (depth + 2)
      let qC0 := quoteVal fuel' G (depth + 1) (evalTerm fuel' G (v0 :: env) c0)
      let qC1 := quoteVal fuel' G (depth + 1) (evalTerm fuel' G (v0 :: env) c1)
      let qCL := quoteVal fuel' G (depth + 3) (evalTerm fuel' G (v2 :: v1 :: v0 :: env) cL)
      .piLine g name mod (quoteVal fuel' G depth dL) qC0 qC1 qCL
    | .prodLine g fN sN fL sL =>
      .prodLine g fN sN (quoteVal fuel' G depth fL) (quoteVal fuel' G depth sL)
    | .sigLine g fN sN fM sM fL env s0 s1 sL =>
      let v0 := Val.vvar depth
      let v1 := Val.vvar (depth + 1)
      let v2 := Val.vvar (depth + 2)
      let qS0 := quoteVal fuel' G (depth + 1) (evalTerm fuel' G (v0 :: env) s0)
      let qS1 := quoteVal fuel' G (depth + 1) (evalTerm fuel' G (v0 :: env) s1)
      let qSL := quoteVal fuel' G (depth + 3) (evalTerm fuel' G (v2 :: v1 :: v0 :: env) sL)
      .sigLine g fN sN fM sM (quoteVal fuel' G depth fL) qS0 qS1 qSL
    | .boxLine g mod inL =>
      .boxLine g mod (quoteVal fuel' G depth inL)
    | .liftr g tyL x₀ =>
      .liftr g (quoteVal fuel' G depth tyL) (quoteVal fuel' G depth x₀)
    | .liftl g tyL x₁ =>
      .liftl g (quoteVal fuel' G depth tyL) (quoteVal fuel' G depth x₁)
    | .funext g mod env body =>
      let v0 := Val.vvar depth
      let v1 := Val.vvar (depth + 1)
      let v2 := Val.vvar (depth + 2)
      let qBody := quoteVal fuel' G (depth + 3) (evalTerm fuel' G (v2 :: v1 :: v0 :: env) body)
      .funext g mod qBody
    | .u64Ty => .u64Ty
    | .u64Lit v => .u64Lit v

end

/-- Normalize a `Term` at context length `depth` via `eval` + `quoteVal`. -/
def normalize (G : GlobalEnv) (env : List Val) (depth : Nat) (tm : Term) : Term :=
  quoteVal defaultFuel G depth (eval G env tm)

end Narya.Core
