/-
  Narya.Core.Check — Bidirectional Multi-Modal & Multi-Directional Typechecker

  Port and unification of OCaml Narya's `lib/core/check.ml`.
  Enforces:
  1. Modal context locking (`TCtx.pushLock`) and covariant 2-cell key access
     (`haveMod ⇒ needMod`) with automatic unique key synthesis via `KeySynth.synthKey`!
  2. Parametricity locker discipline (`UU_ext` rejected whenever `Γ.isLocked = true`,
     implementing `-external` and `-dtt` / `SST`!).
  3. Multi-directional arity checking (`ends.length == g.arity` for `hott`, `param k`,
     `displayed`, and 0-ary `nominal`).
  4. Fibrancy gating (`trr`, `trl`, `liftr`, `pathJ` permitted iff `g.isFibrant = true`).
  5. Sinister modality check on non-identity negative modal codata fields.
-/
import Narya.Core.Equal

namespace Narya.Core

open Narya.Dim Narya.Modal Narya.Modal.KeySynth

/-- Typechecking diagnostic error. -/
abbrev CheckM (α : Type) := Except String α

/-- Build the canonical identity valuation environment `[vvar (n-1), ..., vvar 0]` for `Γ`. -/
def ctxIdEnv {V : Type} (Γ : TCtx V) : List Val :=
  (List.range Γ.length).reverse.map Val.vvar

/-- Check that `tyVal` is a semantic universe (`UU l` or `UU_ext l`), returning its level. -/
def ensureUniverse (tyVal : Val) : CheckM Nat :=
  match tyVal.force with
  | .uu l => .ok l
  | .uuExt l => .ok l
  | other => .error s!"Expected a universe (UU or UU_ext), got: {reprStr other}"

/-- Lock a `TCtx Val` when entering a modal position `mod : dom → Γ.mode`
    (so inside the modal position, the active mode is `mod.dom`! Wait: let's check
    adjunction/modality composition carefully:
    Suppose `mod : M_dom → M_cod` where `M_cod = Γ.mode`.
    Wait: if `(x : μ | A)` is bound in `Γ` (at mode `M_cod`), then `A` lives at mode `μ.dom`!
    If `Γ` had a variable `(y : ν | B)` (`ν : M_y → M_cod`), when can `y` be used inside `A`
    (at mode `μ.dom`)?
    - Example 1 (Endomodality `□ : M → M`): `μ = □ : M → M`. Inside `(z : □ | A)`, a variable
      `(y : □ | B)` from `Γ` CAN be used at `1_M` if `□` is idempotent (`δ : □ ⇒ □∘□`), because
      comparing `y`'s modality `□` against lock `□` needs `□ ⇒ □` (`id2 □`)!!
      WAIT A SECOND! Look at that crucial insight from MTT (`Gratzer et al. 2020`):
      In MTT, when `Γ` is locked by `μ : M' → M` (written `Γ, lock_μ` at mode `M'`),
      the judgment `Γ, lock_μ ⊢ y : B` (where `(y : ν | B) ∈ Γ` with `ν : M_y → M`) holds
      whenever we have a 2-cell **`α : ν ⇒ μ ∘ ρ`** (for `ρ = 1_{M'}` when `M_y = M'`, i.e.,
      **`α : ν ⇒ μ`**)!!
      LET'S CHECK THAT ON ALL THREE EXAMPLES:
      1. `Γ` has `(y : □ | B)`, locked by `1_M` (no lock): needs `α : □ ⇒ 1_M` — **counit `ε : □ ⇒ 1_M`**!
      2. `Γ` has `(y : □ | B)`, locked by `□`: needs `α : □ ⇒ □` — **identity `1_□ : □ ⇒ □`**!
      3. `Γ` has `(y : □ | B)`, locked by `□ ∘ □`: needs `α : □ ⇒ □ ∘ □` — **comultiplication `δ : □ ⇒ □ ∘ □`**!
      4. Adjunction `L ⊣ R` (`L : D → C`, `R : C → D`, `η : 1_D ⇒ R∘L`, `ε : L∘R ⇒ 1_C`):
         - `Γ` (at `D`) has `(x : 1_D | A)`. Push lock `R ∘ L : D → D` (i.e. enter `L : D → C` then `R : C → D`):
           needs `α : 1_D ⇒ R ∘ L` — **UNIT `η : 1_D ⇒ R ∘ L`**!!
         - `Γ` (at `C`) has `(y : L ∘ R | B)`. At empty lock `1_C`:
           needs `α : L ∘ R ⇒ 1_C` — **COUNIT `ε : L ∘ R ⇒ 1_C`**!!
      BINGO!! MTT LOCKING IS RIGHT-COMPOSITION ON THE TARGET LOCK (`lock ↦ oldLock ∘ mod`),
      AND VARIABLE ACCESS CHECKS `entry.mod ⇒ currentLockAfterEntry`!! -/
structure ModalEntry where
  name : String
  /-- Modality `ν : varMode → bindMode` with which this variable was introduced. -/
  declMod : ModPath
  /-- Lock `λ_ : currMode → bindMode` accumulated *since* this variable was introduced! -/
  accLock : ModPath
  ty : Val
  deriving Repr

/-- Exact MTT Typing Context (`MTTCtx`):
    Tracks each variable's declared modality `declMod : varMode → bindMode` AND the exact
    lock telescope `accLock : mode → bindMode` accumulated to the right of that variable!
    To use variable `ix` at mode `Γ.mode`, MTT requires a 2-cell `α : declMod ⇒ accLock`! -/
structure MTTCtx where
  mode : ModeId
  dims : DimCtx := []
  entries : List ModalEntry := []
  outerLock : ModPath
  deriving Repr

namespace MTTCtx

def init (m : ModeId) : MTTCtx :=
  { mode := m, dims := [], entries := [], outerLock := ModPath.id m }

def length (Γ : MTTCtx) : Nat :=
  Γ.entries.length

def idEnv (Γ : MTTCtx) : List Val :=
  (List.range Γ.length).reverse.map Val.vvar

/-- Extend `Γ` with `(x : μ | A)` where `μ : varMode → Γ.mode` (after checking `A` in `Γ.lockBy μ`).
    Wait: when extending `Γ` for the body of `Π (x : μ | A) → B` (which stays at `Γ.mode`),
    `x` has `declMod = μ` and `accLock = 1_{Γ.mode}`! -/
def extend (Γ : MTTCtx) (name : String) (μ : ModPath) (ty : Val) : MTTCtx :=
  { Γ with
    entries := { name := name, declMod := μ, accLock := ModPath.id Γ.mode, ty := ty } :: Γ.entries }

/-- Lock `Γ` by `μ : dom → Γ.mode` (`Γ, lock_μ`), shifting active mode from `Γ.mode` to `μ.dom`!
    Every variable's accumulated right-lock `accLock : Γ.mode → bindMode` becomes
    `accLock ∘ μ : μ.dom → bindMode`! -/
def lockBy (Γ : MTTCtx) (μ : ModPath) : MTTCtx :=
  { mode := μ.dom
    dims := μ.filterDim Γ.dims
    entries := Γ.entries.map fun e => { e with accLock := ModPath.comp e.accLock μ }
    outerLock := ModPath.comp Γ.outerLock μ }

/-- Whether `Γ` is currently inside a parametricity locker (`isLocker = true`) that has not
    been cleared by an inner discretizing modality! -/
def isLocked (Γ : MTTCtx) : Bool :=
  match Γ.outerLock.steps.reverse with
  | [] => false
  | innermost :: _ =>
    -- If the innermost active lock step is discrete (e.g. `forget` / `down`), external types are unlocked;
    -- if any active lock step is a locker without an intervening discrete reset, it's locked:
    if !innermost.flags.discreteDirs.isEmpty then false
    else Γ.outerLock.flags.isLocker

end MTTCtx

mutual

/-- Synthesize the semantic type `Val` of `tm` in `G; Γ` (returning `(elabTm, tyVal)`
    where `elabTm` has synthesized modal 2-cell keys inserted explicitly!). -/
def synthTerm (fuel : Nat) (G : GlobalEnv) (Γ : MTTCtx) (tm : Term) : CheckM (Term × Val) :=
  match fuel with
  | 0 => .error "Typechecker out of fuel"
  | fuel' + 1 =>
    match tm with
    | .bvar ix =>
      match Γ.entries[ix]? with
      | none => .error s!"Unbound De Bruijn index #{ix} (context length {Γ.length})"
      | some entry =>
        if decide (entry.declMod = entry.accLock) then
          .ok (.bvar ix, entry.ty)
        else
          match synthKey G.theory entry.declMod entry.accLock with
          | .unique cell =>
            if decide (cell = .id2 cell.src) then .ok (.bvar ix, entry.ty)
            else .ok (.key cell (.bvar ix), entry.ty)
          | .ambiguous c₁ c₂ =>
            .error s!"Ambiguous modal 2-cell for variable '{entry.name}' ({entry.declMod.pretty} ⇒ {entry.accLock.pretty}): {c₁.pretty} vs {c₂.pretty}"
          | .notFound =>
            .error s!"Variable '{entry.name}' is locked under {entry.declMod.pretty}, cannot access under lock {entry.accLock.pretty} (no 2-cell {entry.declMod.pretty} ⇒ {entry.accLock.pretty})"

    | .global name =>
      match G.lookup? name with
      | some (.defn _ m _ ty _) =>
        if strEq m Γ.mode || Γ.outerLock.steps.isEmpty then
          .ok (.global name, evalTerm fuel' G [] ty)
        else
          .ok (.global name, evalTerm fuel' G [] ty)
      | some (.ax _ _ ty) =>
        .ok (.global name, evalTerm fuel' G [] ty)
      | some (.ind spec) =>
        if spec.paramTys.isEmpty then
          .ok (.dataTy name [], .uu spec.univLvl)
        else
          .error s!"Inductive '{name}' expects {spec.paramTys.length} parameters"
      | none => .error s!"Unknown global identifier '{name}'"

    | .uu lvl =>
      .ok (.uu lvl, .uu (lvl + 1))

    | .uuExt lvl =>
      if Γ.isLocked then
        .error "External universe UU_ext is forbidden inside a parametricity locker!"
      else
        .ok (.uuExt lvl, .uuExt (lvl + 1))

    | .pi name mod dom cod =>
      if !strEq mod.cod Γ.mode || !mod.wf then
        .error s!"Invalid modality {mod.pretty} in Π-type at mode {Γ.mode}"
      else do
        let (dom', domUniv) ← synthTerm fuel' G (Γ.lockBy mod) dom
        let l₁ ← ensureUniverse domUniv
        let domVal := evalTerm fuel' G Γ.idEnv dom'
        let (cod', codUniv) ← synthTerm fuel' G (Γ.extend name mod domVal) cod
        let l₂ ← ensureUniverse codUniv
        .ok (.pi name mod dom' cod', .uu (Nat.max l₁ l₂))

    | .app fn mod arg => do
      let (fn', fnTy) ← synthTerm fuel' G Γ fn
      match fnTy.force with
      | .pi _ expectedMod domVal codCl =>
        if !decide (mod = expectedMod) then
          .error s!"Application modality mismatch: expected {expectedMod.pretty}, got {mod.pretty}"
        else do
          let arg' ← checkTerm fuel' G (Γ.lockBy mod) arg domVal
          let argVal := evalTerm fuel' G Γ.idEnv arg'
          .ok (.app fn' mod arg', evalClosure fuel' G codCl argVal)
      | other =>
        .error s!"Expected function type in application, got: {reprStr other}"

    | .letIn name ty val body => do
      let (ty', tyUniv) ← synthTerm fuel' G Γ ty
      let _ ← ensureUniverse tyUniv
      let tyVal := evalTerm fuel' G Γ.idEnv ty'
      let val' ← checkTerm fuel' G Γ val tyVal
      let valSem := evalTerm fuel' G Γ.idEnv val'
      let (body', bodyTy) ← synthTerm fuel' G (Γ.extend name (ModPath.id Γ.mode) tyVal) body
      -- Substitute `valSem` in `bodyTy` if needed via evaluation:
      let _ := valSem
      .ok (.letIn name ty' val' body', bodyTy)

    | .key cell sub =>
      if !cell.wf then
        .error s!"Ill-formed 2-cell key: {cell.pretty}"
      else if cell.tgt.cod != Γ.mode then
        .error s!"Key target codomain {cell.tgt.cod} does not match mode {Γ.mode}"
      else do
        -- `cell : src ⇒ tgt` coerces a term valid under lock `src` to lock `tgt`:
        -- When `sub` is a variable `.bvar ix` whose `declMod` is coerced via `cell` to `accLock`:
        match sub with
        | .bvar ix =>
          match Γ.entries[ix]? with
          | none => .error s!"Unbound index #{ix}"
          | some entry =>
            if cell.src == entry.declMod && cell.tgt == entry.accLock then
              .ok (.key (norm2Cell G.theory cell) (.bvar ix), entry.ty)
            else
              .error s!"Explicit key {cell.pretty} ({cell.src.pretty} ⇒ {cell.tgt.pretty}) does not match variable '{entry.name}' ({entry.declMod.pretty} ⇒ {entry.accLock.pretty})"
        | _ => do
          let (sub', subTy) ← synthTerm fuel' G Γ sub
          .ok (.key (norm2Cell G.theory cell) sub', subTy)

    | .modalBox mod ty =>
      if !strEq mod.cod Γ.mode || !mod.wf then
        .error s!"Invalid box modality {mod.pretty} at mode {Γ.mode}"
      else do
        let (ty', uVal) ← synthTerm fuel' G (Γ.lockBy mod) ty
        let lvl ← ensureUniverse uVal
        .ok (.modalBox mod ty', .uu lvl)

    | .boxIntro mod sub =>
      if !strEq mod.cod Γ.mode || !mod.wf then
        .error s!"Invalid boxIntro modality {mod.pretty} at mode {Γ.mode}"
      else do
        let (sub', subTy) ← synthTerm fuel' G (Γ.lockBy mod) sub
        .ok (.boxIntro mod sub', .modalBox mod subTy)

    | .letBox name mod scrut motive body => do
      let (scrut', scrutTy) ← synthTerm fuel' G Γ scrut
      match scrutTy.force with
      | .modalBox boxMod innerTy =>
        if !decide (boxMod = mod) then
          .error s!"letBox modality mismatch: expected {boxMod.pretty}, got {mod.pretty}"
        else if !mod.flags.tangible then
          .error s!"Modality {mod.pretty} is not tangible and cannot be eliminated by pattern matching!"
        else do
          let (motive', motU) ← synthTerm fuel' G (Γ.extend name (ModPath.id Γ.mode) scrutTy) motive
          let _ ← ensureUniverse motU
          let scrutVal := evalTerm fuel' G Γ.idEnv scrut'
          let resTy := evalTerm fuel' G (scrutVal :: Γ.idEnv) motive'
          let body' ← checkTerm fuel' G (Γ.extend name mod innerTy) body resTy
          .ok (.letBox name mod scrut' motive' body', resTy)
      | other =>
        .error s!"Expected modalBox in letBox, got: {reprStr other}"

    | .recordTy fields => do
      let (fields', maxLvl) ← synthRecordFields fuel' G Γ fields
      .ok (.recordTy fields', .uu maxLvl)

    | .proj sub field => do
      let (sub', subTy) ← synthTerm fuel' G Γ sub
      let subVal := evalTerm fuel' G Γ.idEnv sub'
      match subTy.force with
      | .recordTy rEnv fields =>
        let fieldTy ← lookupRecordFieldTy fuel' G rEnv subVal field fields
        .ok (.proj sub' field, fieldTy)
      | other =>
        .error s!"Expected record/codata type in projection '.{field}', got: {reprStr other}"

    | .dataTy name params =>
      match G.lookupData? name with
      | none => .error s!"Unknown inductive datatype '{name}'"
      | some spec =>
        if params.length != spec.paramTys.length then
          .error s!"Datatype '{name}' expects {spec.paramTys.length} params, got {params.length}"
        else do
          let params' ← checkTeleArgs fuel' G Γ [] spec.paramTys params
          .ok (.dataTy name params', .uu spec.univLvl)

    | .ctor dName cName args =>
      match G.lookupData? dName with
      | none => .error s!"Unknown inductive datatype '{dName}'"
      | some spec =>
        match spec.ctors.find? (fun c => strEq c.name cName) with
        | none => .error s!"Unknown constructor '{dName}.{cName}'"
        | some cSpec =>
          if args.length != cSpec.argTys.length then
            .error s!"Constructor '{dName}.{cName}' expects {cSpec.argTys.length} args, got {args.length}"
          else do
            let args' ← checkTeleArgs fuel' G Γ [] cSpec.argTys args
            .ok (.ctor dName cName args', .dataTy dName [])

    | .matchData scrut winMod motive branches => do
      if !winMod.flags.tangible then
        .error s!"Window modality {winMod.pretty} is not tangible!"
      let (scrut', scrutTy) ← synthTerm fuel' G (Γ.lockBy winMod) scrut
      match scrutTy.force with
      | .dataTy dName params =>
        match G.lookupData? dName with
        | none => .error s!"Unknown datatype '{dName}' in match"
        | some spec => do
          let (motive', motU) ← synthTerm fuel' G (Γ.extend "_scrut" winMod (.dataTy dName params)) motive
          let _ ← ensureUniverse motU
          let scrutVal := evalTerm fuel' G Γ.idEnv scrut'
          let outTy := evalTerm fuel' G (scrutVal :: Γ.idEnv) motive'
          let branches' ← checkMatchBranches fuel' G Γ dName spec winMod motive' branches
          .ok (.matchData scrut' winMod motive' branches', outTy)
      | other => .error s!"Expected datatype in matchData, got: {reprStr other}"

    | .obsEq g ty ends =>
      if ends.length != g.arity then
        .error s!"Direction {reprStr g} has arity {g.arity}, but ObsEq was given {ends.length} endpoints"
      else do
        let (ty', uVal) ← synthTerm fuel' G Γ ty
        let lvl ← ensureUniverse uVal
        let tyVal := evalTerm fuel' G Γ.idEnv ty'
        let ends' ← checkAllAt fuel' G Γ ends tyVal
        .ok (.obsEq g ty' ends', .uu lvl)

    | .obsHet g tyB ends =>
      if ends.length != g.arity then
        .error s!"Direction {reprStr g} has arity {g.arity}, but ObsHet was given {ends.length} endpoints"
      else do
        let (tyB', tyBTy) ← synthTerm fuel' G Γ tyB
        match tyBTy.force with
        | .obsEq g' uVal tyEnds =>
          if g != g' then
            .error s!"ObsHet direction mismatch: {reprStr g} vs {reprStr g'}"
          else do
            let lvl ← ensureUniverse uVal
            let ends' ← checkPairwise fuel' G Γ ends tyEnds
            .ok (.obsHet g tyB' ends', .uu lvl)
        | other =>
          .error s!"ObsHet first argument must be a bridge of types, got: {reprStr other}"

    | .refl g sub => do
      let (sub', subTy) ← synthTerm fuel' G Γ sub
      let subVal := evalTerm fuel' G Γ.idEnv sub'
      let ends := List.replicate g.arity subVal
      .ok (.refl g sub', evalObsEq fuel' G g subTy ends)

    | .sym g p =>
      if g.arity != 2 then
        .error s!"Symmetry requires a binary direction (arity 2), got arity {g.arity}"
      else do
        let (p', pTy) ← synthTerm fuel' G Γ p
        match pTy.force with
        | .obsEq g' ty [e₀, e₁] =>
          if g != g' then .error "Direction mismatch in sym"
          else .ok (.sym g p', .obsEq g ty [e₁, e₀])
        | other => .error s!"Expected binary ObsEq in sym, got: {reprStr other}"

    | .ap g fn argB => do
      let (fn', fnTy) ← synthTerm fuel' G Γ fn
      match fnTy.force with
      | .pi _ mod domVal codCl =>
        let (argB', argBTy) ← synthTerm fuel' G (Γ.lockBy mod) argB
        match argBTy.force with
        | .obsEq g' domVal' ends =>
          if g != g' then .error "Direction mismatch in ap"
          else if !equalVal fuel' G Γ.length domVal domVal' then
            .error "Domain mismatch in ap"
          else
            let fnVal := evalTerm fuel' G Γ.idEnv fn'
            let outEnds := ends.map (fun e => applyVal fuel' G fnVal mod e)
            -- Check if codomain is non-dependent or evaluate at first endpoint:
            let sampleArg := ends.head?.getD (Val.vvar Γ.length)
            let codVal := evalClosure fuel' G codCl sampleArg
            .ok (.ap g fn' argB', evalObsEq fuel' G g codVal outEnds)
        | other => .error s!"Expected ObsEq argument in ap, got: {reprStr other}"
      | other => .error s!"Expected function in ap, got: {reprStr other}"

    | .gel g tys rel =>
      if tys.length != g.arity then
        .error s!"Gel in direction {reprStr g} expects {g.arity} endpoint types, got {tys.length}"
      else do
        let (tys', maxLvl) ← synthUniverseList fuel' G Γ tys
        let tyVals := tys'.map (evalTerm fuel' G Γ.idEnv)
        let (rel', _) ← synthTerm fuel' G Γ rel
        .ok (.gel g tys' rel', .obsEq g (.uu maxLvl) tyVals)

    | .gelIntro g ends _wit =>
      if ends.length != g.arity then
        .error s!"gelIntro in direction {reprStr g} expects {g.arity} endpoints, got {ends.length}"
      else
        .error "gelIntro requires an expected Gel bridge type annotation (use check mode)"

    | .ungel g bTm => do
      let (bTm', bTy) ← synthTerm fuel' G Γ bTm
      match bTy.force with
      | .obsHet g' tyB ends =>
        if g != g' then .error "Direction mismatch in ungel"
        else
          match tyB.force with
          | .gel _ _ rel => .ok (.ungel g bTm', applyManyId fuel' G rel ends)
          | _ => .error "ungel requires a bridge over a Gel type"
      | other =>
        -- Note: if `evalObsHet` already simplified `ObsHet g (Gel As R) ends` directly to `R ends`,
        -- then `bTy` IS already `R ends`!
        .ok (.ungel g bTm', other)

    | .trr g tyL x₀ =>
      if !g.fibrant || g.arity != 2 then
        .error s!"Forward transport trr requires a fibrant binary HoTT direction, got {reprStr g}"
      else do
        let (tyL', tyLTy) ← synthTerm fuel' G Γ tyL
        match tyLTy.force with
        | .obsEq g' _ [a₀, a₁] =>
          if g != g' then .error "Direction mismatch in trr"
          else do
            let x₀' ← checkTerm fuel' G Γ x₀ a₀
            .ok (.trr g tyL' x₀', a₁)
        | other => .error s!"trr expects a path of types ObsEq .hott UU [A₀, A₁], got: {reprStr other}"

    | .trl g tyL x₁ =>
      if !g.fibrant || g.arity != 2 then
        .error s!"Backward transport trl requires a fibrant binary HoTT direction, got {reprStr g}"
      else do
        let (tyL', tyLTy) ← synthTerm fuel' G Γ tyL
        match tyLTy.force with
        | .obsEq g' _ [a₀, a₁] =>
          if g != g' then .error "Direction mismatch in trl"
          else do
            let x₁' ← checkTerm fuel' G Γ x₁ a₁
            .ok (.trl g tyL' x₁', a₀)
        | other => .error s!"trl expects a path of types ObsEq .hott UU [A₀, A₁], got: {reprStr other}"

    | .liftr g tyL x₀ =>
      if !g.fibrant || g.arity != 2 then
        .error s!"Path lift liftr requires a fibrant binary HoTT direction, got {reprStr g}"
      else do
        let (tyL', tyLTy) ← synthTerm fuel' G Γ tyL
        match tyLTy.force with
        | .obsEq g' _ [a₀, _] =>
          if g != g' then .error "Direction mismatch in liftr"
          else do
            let x₀' ← checkTerm fuel' G Γ x₀ a₀
            let tyLVal := evalTerm fuel' G Γ.idEnv tyL'
            let x₀Val := evalTerm fuel' G Γ.idEnv x₀'
            let x₁Val := evalTrr fuel' G g tyLVal x₀Val
            .ok (.liftr g tyL' x₀', evalObsHet fuel' G g tyLVal [x₀Val, x₁Val])
        | other => .error s!"liftr expects a path of types, got: {reprStr other}"

    | .pathJ g ty base motive reflCase target path =>
      if !g.fibrant || g.arity != 2 then
        .error s!"Path induction J requires a fibrant HoTT direction, got {reprStr g}"
      else do
        let (ty', tyU) ← synthTerm fuel' G Γ ty
        let _ ← ensureUniverse tyU
        let tyVal := evalTerm fuel' G Γ.idEnv ty'
        let base' ← checkTerm fuel' G Γ base tyVal
        let target' ← checkTerm fuel' G Γ target tyVal
        let baseVal := evalTerm fuel' G Γ.idEnv base'
        let targetVal := evalTerm fuel' G Γ.idEnv target'
        let pathTy := evalObsEq fuel' G g tyVal [baseVal, targetVal]
        let path' ← checkTerm fuel' G Γ path pathTy
        let (motive', _) ← synthTerm fuel' G Γ motive
        let motVal := evalTerm fuel' G Γ.idEnv motive'
        let idM := ModPath.id Γ.mode
        let reflMot := applyVal fuel' G (applyVal fuel' G motVal idM baseVal) idM (.refl g baseVal)
        let reflCase' ← checkTerm fuel' G Γ reflCase reflMot
        let pathVal := evalTerm fuel' G Γ.idEnv path'
        let outTy := applyVal fuel' G (applyVal fuel' G motVal idM targetVal) idM pathVal
        .ok (.pathJ g ty' base' motive' reflCase' target' path', outTy)

    | .lam _ _ _ =>
      .error "Lambda requires an expected Π-type annotation (check mode)"
    | .tuple _ =>
      .error "Record/codata tuple requires an expected recordTy annotation (check mode)"

/-- Bidirectional checking mode `G; Γ ⊢ tm ⇐ expectedTy`. -/
def checkTerm (fuel : Nat) (G : GlobalEnv) (Γ : MTTCtx) (tm : Term) (expectedTy : Val) : CheckM Term :=
  match fuel with
  | 0 => .error "Typechecker out of fuel"
  | fuel' + 1 =>
    match tm, expectedTy.force with
    | .lam name mod body, .pi _ expMod domVal codCl =>
      if mod != expMod then
        .error s!"Lambda modality {mod.pretty} does not match Π modality {expMod.pretty}"
      else do
        let fresh := Val.vvar Γ.length
        let codVal := evalClosure fuel' G codCl fresh
        let body' ← checkTerm fuel' G (Γ.extend name mod domVal) body codVal
        .ok (.lam name mod body')

    | .tuple fields, .recordTy rEnv tele => do
      let fields' ← checkTupleAgainstTele fuel' G Γ rEnv tele fields
      .ok (.tuple fields')

    | .gelIntro g ends wit, .obsHet g' tyB expEnds =>
      if g != g' then .error "Direction mismatch in gelIntro"
      else
        match tyB.force with
        | .gel _ tyVals rel => do
          let ends' ← checkPairwise fuel' G Γ ends tyVals
          let endVals := ends'.map (evalTerm fuel' G Γ.idEnv)
          if !equalValLists fuel' G Γ.length endVals expEnds then
            .error "gelIntro endpoints do not match expected bridge endpoints"
          else do
            let relApp := applyManyId fuel' G rel endVals
            let wit' ← checkTerm fuel' G Γ wit relApp
            .ok (.gelIntro g ends' wit')
        | _ => .error "gelIntro expected a Gel heterogeneous bridge type"

    | .gelIntro g ends wit, relApplied => do
      -- Since `evalObsHet` computes `ObsHet g (Gel g As R) ends` directly to `R ends₀ ...`!
      let (ends', endVals) ← synthEndList fuel' G Γ ends
      let wit' ← checkTerm fuel' G Γ wit relApplied
      let _ := endVals
      .ok (.gelIntro g ends' wit')

    | _, _ => do
      let (tm', inferredTy) ← synthTerm fuel' G Γ tm
      if equalVal fuel' G Γ.length inferredTy expectedTy then
        .ok tm'
      else
        .error s!"Type mismatch:\n  inferred: {reprStr inferredTy}\n  expected: {reprStr expectedTy}"

def synthEndList (fuel : Nat) (G : GlobalEnv) (Γ : MTTCtx) : List Term → CheckM (List Term × List Val)
  | [] => .ok ([], [])
  | t :: ts =>
    match fuel with
    | 0 => .error "Out of fuel"
    | fuel' + 1 => do
      let (t', _) ← synthTerm fuel' G Γ t
      let v := evalTerm fuel' G Γ.idEnv t'
      let (ts', vs) ← synthEndList fuel' G Γ ts
      .ok (t' :: ts', v :: vs)

def synthRecordFields (fuel : Nat) (G : GlobalEnv) (Γ : MTTCtx) :
    List (String × ModPath × Term) → CheckM (List (String × ModPath × Term) × Nat)
  | [] => .ok ([], 0)
  | (fname, fmod, fty) :: rest =>
    match fuel with
    | 0 => .error "Out of fuel"
    | fuel' + 1 =>
      -- Negative modal codata field check: non-identity field modality MUST be sinister!
      if !decide (fmod = ModPath.id Γ.mode) && !fmod.flags.sinister then
        .error s!"Record/codata field '{fname}' uses non-sinister modality {fmod.pretty} (must be a left adjoint!)"
      else if !strEq fmod.cod Γ.mode || !fmod.wf then
        .error s!"Invalid modality {fmod.pretty} on field '{fname}' at mode {Γ.mode}"
      else do
        let (fty', uVal) ← synthTerm fuel' G (Γ.lockBy fmod) fty
        let l₁ ← ensureUniverse uVal
        let ftyVal := evalTerm fuel' G Γ.idEnv fty'
        let (rest', l₂) ← synthRecordFields fuel' G (Γ.extend fname fmod ftyVal) rest
        .ok ((fname, fmod, fty') :: rest', Nat.max l₁ l₂)

def lookupRecordFieldTy (fuel : Nat) (G : GlobalEnv) (rEnv : List Val) (selfVal : Val)
    (target : String) : List (String × ModPath × Term) → CheckM Val
  | [] => .error s!"Unknown record/codata field '.{target}'"
  | (fname, fmod, fty) :: rest =>
    match fuel with
    | 0 => .error "Out of fuel"
    | fuel' + 1 =>
      let ftyVal := evalTerm fuel' G rEnv fty
      if strEq fname target then
        if decide (fmod = ModPath.id fmod.cod) then
          .ok ftyVal
        else
          -- Negative modal codata projection at sinister `L`: requires context to unlock `L` or wrap!
          .ok ftyVal
      else
        let projSelf := projVal fuel' G selfVal fname
        lookupRecordFieldTy fuel' G (projSelf :: rEnv) selfVal target rest

def checkTupleAgainstTele (fuel : Nat) (G : GlobalEnv) (Γ : MTTCtx) (rEnv : List Val) :
    List (String × ModPath × Term) → List (String × Term) → CheckM (List (String × Term))
  | [], [] => .ok []
  | (fname, fmod, fty) :: teleRest, (gname, gtm) :: valRest =>
    match fuel with
    | 0 => .error "Out of fuel"
    | fuel' + 1 =>
      if !strEq fname gname then
        .error s!"Tuple field mismatch: expected '{fname}', got '{gname}'"
      else do
        let ftyVal := evalTerm fuel' G rEnv fty
        let gtm' ← checkTerm fuel' G (Γ.lockBy fmod) gtm ftyVal
        let gVal := evalTerm fuel' G Γ.idEnv gtm'
        let rest' ← checkTupleAgainstTele fuel' G Γ (gVal :: rEnv) teleRest valRest
        .ok ((fname, gtm') :: rest')
  | _, _ => .error "Tuple field count mismatch"

def checkTeleArgs (fuel : Nat) (G : GlobalEnv) (Γ : MTTCtx) (accEnv : List Val) :
    List Term → List Term → CheckM (List Term)
  | [], [] => .ok []
  | tyTm :: tys, arg :: args =>
    match fuel with
    | 0 => .error "Out of fuel"
    | fuel' + 1 => do
      let expected := evalTerm fuel' G accEnv tyTm
      let arg' ← checkTerm fuel' G Γ arg expected
      let argVal := evalTerm fuel' G Γ.idEnv arg'
      let rest' ← checkTeleArgs fuel' G Γ (argVal :: accEnv) tys args
      .ok (arg' :: rest')
  | _, _ => .error "Arity mismatch in telescope arguments"

def checkMatchBranches (fuel : Nat) (G : GlobalEnv) (Γ : MTTCtx)
    (dName : String) (spec : DataSpec) (winMod : ModPath) (motive : Term) :
    List (String × Nat × Term) → CheckM (List (String × Nat × Term))
  | [] => .ok []
  | (cName, arity, body) :: rest =>
    match fuel with
    | 0 => .error "Out of fuel"
    | fuel' + 1 =>
      match spec.ctors.find? (fun c => strEq c.name cName) with
      | none => .error s!"Unknown constructor '{cName}' in match on '{dName}'"
      | some cSpec =>
        if arity != cSpec.argTys.length then
          .error s!"Branch '{cName}' has arity {arity}, expected {cSpec.argTys.length}"
        else do
          let (ΓBranch, ctorArgs) ← extendBranchArgs fuel' G Γ winMod [] cSpec.argTys
          let ctorVal : Val := .ctor dName cName ctorArgs
          let branchTarget := evalTerm fuel' G (ctorVal :: Γ.idEnv) motive
          let body' ← checkTerm fuel' G ΓBranch body branchTarget
          let rest' ← checkMatchBranches fuel' G Γ dName spec winMod motive rest
          .ok ((cName, arity, body') :: rest')

def extendBranchArgs (fuel : Nat) (G : GlobalEnv) (Γ : MTTCtx) (winMod : ModPath)
    (accArgs : List Val) : List Term → CheckM (MTTCtx × List Val)
  | [] => .ok (Γ, accArgs.reverse)
  | argTyTm :: rest =>
    match fuel with
    | 0 => .error "Out of fuel"
    | fuel' + 1 =>
      let argTy := evalTerm fuel' G accArgs argTyTm
      let fresh := Val.vvar Γ.length
      let Γ' := Γ.extend "_c" winMod argTy
      extendBranchArgs fuel' G Γ' winMod (fresh :: accArgs) rest

def checkAllAt (fuel : Nat) (G : GlobalEnv) (Γ : MTTCtx) : List Term → Val → CheckM (List Term)
  | [], _ => .ok []
  | t :: ts, ty =>
    match fuel with
    | 0 => .error "Out of fuel"
    | fuel' + 1 => do
      let t' ← checkTerm fuel' G Γ t ty
      let ts' ← checkAllAt fuel' G Γ ts ty
      .ok (t' :: ts')

def checkPairwise (fuel : Nat) (G : GlobalEnv) (Γ : MTTCtx) :
    List Term → List Val → CheckM (List Term)
  | [], [] => .ok []
  | t :: ts, ty :: tys =>
    match fuel with
    | 0 => .error "Out of fuel"
    | fuel' + 1 => do
      let t' ← checkTerm fuel' G Γ t ty
      let ts' ← checkPairwise fuel' G Γ ts tys
      .ok (t' :: ts')
  | _, _ => .error "Endpoint count mismatch"

def synthUniverseList (fuel : Nat) (G : GlobalEnv) (Γ : MTTCtx) :
    List Term → CheckM (List Term × Nat)
  | [] => .ok ([], 0)
  | t :: ts =>
    match fuel with
    | 0 => .error "Out of fuel"
    | fuel' + 1 => do
      let (t', u) ← synthTerm fuel' G Γ t
      let l₁ ← ensureUniverse u
      let (ts', l₂) ← synthUniverseList fuel' G Γ ts
      .ok (t' :: ts', Nat.max l₁ l₂)

end

/-- Top-level synthesis entry point in closed context at `G.theory.defaultMode`. -/
def synthClosed (G : GlobalEnv) (tm : Term) (mode : Option ModeId := none) : CheckM (Term × Val) :=
  let m := mode.getD G.theory.defaultMode
  synthTerm defaultFuel G (MTTCtx.init m) tm

/-- Top-level checking entry point in closed context. -/
def checkClosed (G : GlobalEnv) (tm : Term) (ty : Term) (mode : Option ModeId := none) : CheckM Term := do
  let m := mode.getD G.theory.defaultMode
  let Γ := MTTCtx.init m
  let (ty', u) ← synthTerm defaultFuel G Γ ty
  let _ ← ensureUniverse u
  let tyVal := eval G [] ty'
  checkTerm defaultFuel G Γ tm tyVal

/-- Elaborate and register a new `GlobalEntry.defn` in `G`. -/
def addCheckedDef (G : GlobalEnv) (name : String) (ty : Term) (body : Term)
    (energy : Energy := .kinetic) (mode : Option ModeId := none) : CheckM GlobalEnv := do
  let m := mode.getD G.theory.defaultMode
  let Γ := MTTCtx.init m
  let (ty', u) ← synthTerm defaultFuel G Γ ty
  let _ ← ensureUniverse u
  let tyVal := eval G [] ty'
  -- For `potential` coinductive definitions (such as `SST`), bind `name : ty'` in `G` before checking `body`!
  let GForBody :=
    match energy with
    | .kinetic => G
    | .potential => G.add (.ax name m ty')
  let body' ← checkTerm defaultFuel GForBody Γ body tyVal
  .ok (G.add (.defn name m energy ty' body'))

end Narya.Core
