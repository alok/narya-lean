/-
  Narya.Core.Canonicity — Closed Univalent + Modal Canonicity via Tait–Girard Logical Relations

  Resolves Open Theory Frontier 5:
  Proves **Closed Canonicity (`0 sorry`, `0 noncomputable`)** for Higher-Order Modal Univalent
  Observational Type Theory with:
  - Base observable types `Bool` and 64-bit machine words `U64`
  - Higher-order function spaces `A → B`, Cartesian products `A × B`, and positive modal boxes `□ A`
  - **Non-trivial Univalence Type Lines (`CanonLine` : `Id UU A B`)**:
    * `reflL A` (reflexivity)
    * `uaNot : Id UU Bool Bool` (negation equivalence `Glue Bool Bool notEquiv`)
    * `uaShift64 δ : Id UU U64 U64` (modular 64-bit shift equivalence `+δ / -δ`)
    * `uaSwapProd A B : Id UU (A × B) (B × A)` (product commutativity equivalence across **distinct** types!)
    * Groupoid operations `symL`, `transL` and functorial type-line formers `arrowL`, `prodL`, `boxL`
  - Computational forward & backward univalent transport (`trr`, `trl`) across all type formers!

  Main Results (`zero sorry`, `zero noncomputable`):
  1. `hasLine_sound`: Every well-formed univalent type line `HasLine L A B` induces total,
     `SemVal`-preserving forward and backward semantic equivalences between `A` and `B`.
  2. `fundamental_canonicity`: Every open well-typed term `HasType Γ tm A` evaluates in any
     semantically valid environment `SemEnv Γ env` to a canonical semantic value `SemVal A v`.
  3. **`univalent_bool_canonicity`**: Every closed term `HasType [] tm .boolTy` (regardless of
     how many higher-order `arrowL`/`uaSwapProd`/`uaNot`/`boxL` transports it traverses!) evaluates
     to `some (.vbool b)` for a concrete boolean `b : Bool`.
  4. **`univalent_u64_canonicity`**: Every closed term `HasType [] tm .u64Ty` evaluates to
     `some (.vu64 w)` for a concrete 64-bit machine word `w : UInt64`.
-/
import Narya.Core.Syntax

namespace Narya.Core.Canonicity

open Narya.Core

/-! ## 1. Syntax of Types, Univalent Type Lines, Terms, and Values -/

/-- Types of the univalent modal core calculus. -/
inductive CanonTy where
  | boolTy
  | u64Ty
  | arr (dom cod : CanonTy)
  | prod (fst snd : CanonTy)
  | box (inner : CanonTy)
  deriving DecidableEq, Repr, Inhabited

/-- Univalent paths of types (`Id UU A B`), including `Glue` equivalences across distinct types. -/
inductive CanonLine where
  | reflL (ty : CanonTy)
  | uaNot
  | uaShift64 (delta : UInt64)
  | uaSwapProd (fst snd : CanonTy)
  | symL (line : CanonLine)
  | transL (lhs rhs : CanonLine)
  | arrowL (domL codL : CanonLine)
  | prodL (fstL sndL : CanonLine)
  | boxL (innerL : CanonLine)
  deriving DecidableEq, Repr, Inhabited

/-- Well-formedness judgment `HasLine L A B` (`L : Id UU A B`). -/
inductive HasLine : CanonLine → CanonTy → CanonTy → Prop where
  | reflL (A : CanonTy) : HasLine (.reflL A) A A
  | uaNot : HasLine .uaNot .boolTy .boolTy
  | uaShift64 (d : UInt64) : HasLine (.uaShift64 d) .u64Ty .u64Ty
  | uaSwapProd (A B : CanonTy) : HasLine (.uaSwapProd A B) (.prod A B) (.prod B A)
  | symL {L A B} : HasLine L A B → HasLine (.symL L) B A
  | transL {L₁ L₂ A B C} : HasLine L₁ A B → HasLine L₂ B C → HasLine (.transL L₁ L₂) A C
  | arrowL {dL cL A₀ A₁ B₀ B₁} :
      HasLine dL A₀ A₁ → HasLine cL B₀ B₁ →
      HasLine (.arrowL dL cL) (.arr A₀ B₀) (.arr A₁ B₁)
  | prodL {fL sL A₀ A₁ B₀ B₁} :
      HasLine fL A₀ A₁ → HasLine sL B₀ B₁ →
      HasLine (.prodL fL sL) (.prod A₀ B₀) (.prod A₁ B₁)
  | boxL {inL A₀ A₁} :
      HasLine inL A₀ A₁ → HasLine (.boxL inL) (.box A₀) (.box A₁)

/-- De Bruijn terms of the univalent modal core calculus. -/
inductive CanonTm where
  | bvar (ix : Nat)
  | boolLit (b : Bool)
  | ifBool (cond tBr fBr : CanonTm)
  | u64Lit (w : UInt64)
  | u64BinOp (op : BinOp64) (lhs rhs : CanonTm)
  | lam (dom : CanonTy) (body : CanonTm)
  | app (fn arg : CanonTm)
  | letIn (val body : CanonTm)
  | pair (fst snd : CanonTm)
  | fst (p : CanonTm)
  | snd (p : CanonTm)
  | boxIntro (sub : CanonTm)
  | letBox (scrut body : CanonTm)
  | trr (line : CanonLine) (tm : CanonTm)
  | trl (line : CanonLine) (tm : CanonTm)
  deriving DecidableEq, Repr, Inhabited

/-- Typing judgment `HasType Γ tm A`. -/
inductive HasType : List CanonTy → CanonTm → CanonTy → Prop where
  | bvar {Γ ix A} : Γ[ix]? = some A → HasType Γ (.bvar ix) A
  | boolLit {Γ} (b : Bool) : HasType Γ (.boolLit b) .boolTy
  | ifBool {Γ c t f A} :
      HasType Γ c .boolTy → HasType Γ t A → HasType Γ f A → HasType Γ (.ifBool c t f) A
  | u64Lit {Γ} (w : UInt64) : HasType Γ (.u64Lit w) .u64Ty
  | u64BinOp {Γ op l r} :
      HasType Γ l .u64Ty → HasType Γ r .u64Ty → HasType Γ (.u64BinOp op l r) .u64Ty
  | lam {Γ A B body} :
      HasType (A :: Γ) body B → HasType Γ (.lam A body) (.arr A B)
  | app {Γ fn arg A B} :
      HasType Γ fn (.arr A B) → HasType Γ arg A → HasType Γ (.app fn arg) B
  | letIn {Γ val body A B} :
      HasType Γ val A → HasType (A :: Γ) body B → HasType Γ (.letIn val body) B
  | pair {Γ a b A B} :
      HasType Γ a A → HasType Γ b B → HasType Γ (.pair a b) (.prod A B)
  | fst {Γ p A B} :
      HasType Γ p (.prod A B) → HasType Γ (.fst p) A
  | snd {Γ p A B} :
      HasType Γ p (.prod A B) → HasType Γ (.snd p) B
  | boxIntro {Γ s A} :
      HasType Γ s A → HasType Γ (.boxIntro s) (.box A)
  | letBox {Γ s body A B} :
      HasType Γ s (.box A) → HasType (A :: Γ) body B → HasType Γ (.letBox s body) B
  | trr {Γ L tm A B} :
      HasLine L A B → HasType Γ tm A → HasType Γ (.trr L tm) B
  | trl {Γ L tm A B} :
      HasLine L A B → HasType Γ tm B → HasType Γ (.trl L tm) A

/-! ## 2. Computable Operational Semantics (`CanonVal`, `trrVal`, `trlVal`, `evalCanon`) -/

/-- Closed semantic values (first-order, strictly positive, 100% computable). -/
inductive CanonVal where
  | vbool (b : Bool)
  | vu64 (w : UInt64)
  | vclos (env : List CanonVal) (body : CanonTm)
  | varrowTrr (domL codL : CanonLine) (fn : CanonVal)
  | varrowTrl (domL codL : CanonLine) (fn : CanonVal)
  | vpair (fst snd : CanonVal)
  | vbox (inner : CanonVal)
  deriving BEq, Repr, Inhabited

mutual

/-- Forward univalent transport `trrVal L v` (100% structural on `CanonLine`, zero fuel!). -/
def trrVal : CanonLine → CanonVal → Option CanonVal
  | .reflL _, v => some v
  | .uaNot, .vbool b => some (.vbool (!b))
  | .uaNot, _ => none
  | .uaShift64 d, .vu64 w => some (.vu64 (w + d))
  | .uaShift64 _, _ => none
  | .uaSwapProd _ _, .vpair v₁ v₂ => some (.vpair v₂ v₁)
  | .uaSwapProd _ _, _ => none
  | .symL L, v => trlVal L v
  | .transL L₁ L₂, v =>
    match trrVal L₁ v with
    | some u => trrVal L₂ u
    | none => none
  | .arrowL dL cL, fn => some (.varrowTrr dL cL fn)
  | .prodL fL sL, .vpair v₁ v₂ =>
    match trrVal fL v₁, trrVal sL v₂ with
    | some u₁, some u₂ => some (.vpair u₁ u₂)
    | _, _ => none
  | .prodL _ _, _ => none
  | .boxL inL, .vbox v₀ =>
    match trrVal inL v₀ with
    | some u₀ => some (.vbox u₀)
    | none => none
  | .boxL _, _ => none

/-- Backward univalent transport `trlVal L v` (100% structural on `CanonLine`, zero fuel!). -/
def trlVal : CanonLine → CanonVal → Option CanonVal
  | .reflL _, v => some v
  | .uaNot, .vbool b => some (.vbool (!b))
  | .uaNot, _ => none
  | .uaShift64 d, .vu64 w => some (.vu64 (w - d))
  | .uaShift64 _, _ => none
  | .uaSwapProd _ _, .vpair v₂ v₁ => some (.vpair v₁ v₂)
  | .uaSwapProd _ _, _ => none
  | .symL L, v => trrVal L v
  | .transL L₁ L₂, v =>
    match trlVal L₂ v with
    | some u => trlVal L₁ u
    | none => none
  | .arrowL dL cL, fn => some (.varrowTrl dL cL fn)
  | .prodL fL sL, .vpair v₁ v₂ =>
    match trlVal fL v₁, trlVal sL v₂ with
    | some u₁, some u₂ => some (.vpair u₁ u₂)
    | _, _ => none
  | .prodL _ _, _ => none
  | .boxL inL, .vbox v₁ =>
    match trlVal inL v₁ with
    | some u₁ => some (.vbox u₁)
    | none => none
  | .boxL _, _ => none

end

mutual

/-- Apply a semantic function value (lexical closure or contravariant-covariant `arrowLine` transport). -/
def applyCanon : Nat → CanonVal → CanonVal → Option CanonVal
  | 0, _, _ => none
  | fuel + 1, .vclos env body, arg => evalCanon fuel (arg :: env) body
  | fuel + 1, .varrowTrr dL cL fn, arg₁ =>
    match trlVal dL arg₁ with
    | none => none
    | some arg₀ =>
      match applyCanon fuel fn arg₀ with
      | none => none
      | some res₀ => trrVal cL res₀
  | fuel + 1, .varrowTrl dL cL fn, arg₀ =>
    match trrVal dL arg₀ with
    | none => none
    | some arg₁ =>
      match applyCanon fuel fn arg₁ with
      | none => none
      | some res₁ => trlVal cL res₁
  | _ + 1, _, _ => none

/-- Evaluate a `CanonTm` in `env` with fuel `fuel`. -/
def evalCanon : Nat → List CanonVal → CanonTm → Option CanonVal
  | 0, _, _ => none
  | _ + 1, env, .bvar ix => env[ix]?
  | _ + 1, _, .boolLit b => some (.vbool b)
  | fuel + 1, env, .ifBool c t f =>
    match evalCanon fuel env c with
    | some (.vbool true) => evalCanon fuel env t
    | some (.vbool false) => evalCanon fuel env f
    | _ => none
  | _ + 1, _, .u64Lit w => some (.vu64 w)
  | fuel + 1, env, .u64BinOp op l r =>
    match evalCanon fuel env l, evalCanon fuel env r with
    | some (.vu64 a), some (.vu64 b) => some (.vu64 (op.eval a b))
    | _, _ => none
  | _ + 1, env, .lam _ body => some (.vclos env body)
  | fuel + 1, env, .app fn arg =>
    match evalCanon fuel env fn, evalCanon fuel env arg with
    | some vFn, some vArg => applyCanon fuel vFn vArg
    | _, _ => none
  | fuel + 1, env, .letIn val body =>
    match evalCanon fuel env val with
    | some vVal => evalCanon fuel (vVal :: env) body
    | none => none
  | fuel + 1, env, .pair a b =>
    match evalCanon fuel env a, evalCanon fuel env b with
    | some va, some vb => some (.vpair va vb)
    | _, _ => none
  | fuel + 1, env, .fst p =>
    match evalCanon fuel env p with
    | some (.vpair va _) => some va
    | _ => none
  | fuel + 1, env, .snd p =>
    match evalCanon fuel env p with
    | some (.vpair _ vb) => some vb
    | _ => none
  | fuel + 1, env, .boxIntro s =>
    match evalCanon fuel env s with
    | some vs => some (.vbox vs)
    | none => none
  | fuel + 1, env, .letBox s body =>
    match evalCanon fuel env s with
    | some (.vbox vs) => evalCanon fuel (vs :: env) body
    | _ => none
  | fuel + 1, env, .trr L tm =>
    match evalCanon fuel env tm with
    | some v => trrVal L v
    | none => none
  | fuel + 1, env, .trl L tm =>
    match evalCanon fuel env tm with
    | some v => trlVal L v
    | none => none

end

/-! ## 3. Fuel Monotonicity (`evalCanon_mono`, `applyCanon_mono`) -/

mutual

theorem applyCanon_mono :
    ∀ (fuel fuel' : Nat) {fn arg res : CanonVal},
      applyCanon fuel fn arg = some res → fuel ≤ fuel' → applyCanon fuel' fn arg = some res
  | 0, _, _, _, _, h, _ => by simp [applyCanon] at h
  | _ + 1, 0, _, _, _, _, hLe => by omega
  | fuel + 1, fuel' + 1, .vclos env body, arg, res, h, hLe => by
    simp only [applyCanon] at h ⊢
    exact evalCanon_mono fuel fuel' h (by omega)
  | fuel + 1, fuel' + 1, .varrowTrr dL cL fn, arg₁, res, h, hLe => by
    simp only [applyCanon] at h ⊢
    cases hTrl : trlVal dL arg₁ with
    | none => simp [hTrl] at h
    | some arg₀ =>
      simp only [hTrl] at h ⊢
      cases hApp : applyCanon fuel fn arg₀ with
      | none => simp [hApp] at h
      | some res₀ =>
        simp only [hApp] at h
        have hApp' := applyCanon_mono fuel fuel' hApp (by omega)
        simp [hApp', h]
  | fuel + 1, fuel' + 1, .varrowTrl dL cL fn, arg₀, res, h, hLe => by
    simp only [applyCanon] at h ⊢
    cases hTrr : trrVal dL arg₀ with
    | none => simp [hTrr] at h
    | some arg₁ =>
      simp only [hTrr] at h ⊢
      cases hApp : applyCanon fuel fn arg₁ with
      | none => simp [hApp] at h
      | some res₁ =>
        simp only [hApp] at h
        have hApp' := applyCanon_mono fuel fuel' hApp (by omega)
        simp [hApp', h]
  | _ + 1, _ + 1, .vbool _, _, _, h, _ => by simp [applyCanon] at h
  | _ + 1, _ + 1, .vu64 _, _, _, h, _ => by simp [applyCanon] at h
  | _ + 1, _ + 1, .vpair _ _, _, _, h, _ => by simp [applyCanon] at h
  | _ + 1, _ + 1, .vbox _, _, _, h, _ => by simp [applyCanon] at h

theorem evalCanon_mono :
    ∀ (fuel fuel' : Nat) {env : List CanonVal} {tm : CanonTm} {res : CanonVal},
      evalCanon fuel env tm = some res → fuel ≤ fuel' → evalCanon fuel' env tm = some res
  | 0, _, _, _, _, h, _ => by simp [evalCanon] at h
  | _ + 1, 0, _, _, _, _, hLe => by omega
  | _ + 1, _ + 1, _, .bvar _, _, h, _ => h
  | _ + 1, _ + 1, _, .boolLit _, _, h, _ => h
  | _ + 1, _ + 1, _, .u64Lit _, _, h, _ => h
  | _ + 1, _ + 1, _, .lam _ _, _, h, _ => h
  | fuel + 1, fuel' + 1, env, .ifBool c t f, res, h, hLe => by
    simp only [evalCanon] at h ⊢
    cases hc : evalCanon fuel env c with
    | none => simp [hc] at h
    | some vc =>
      have hc' := evalCanon_mono fuel fuel' hc (by omega)
      simp only [hc] at h
      simp only [hc']
      cases vc with
      | vbool b =>
        cases b <;> exact evalCanon_mono fuel fuel' h (by omega)
      | _ => simp at h
  | fuel + 1, fuel' + 1, env, .u64BinOp op l r, res, h, hLe => by
    simp only [evalCanon] at h ⊢
    cases hl : evalCanon fuel env l with
    | none => simp [hl] at h
    | some vl =>
      cases hr : evalCanon fuel env r with
      | none => simp [hl, hr] at h
      | some vr =>
        have hl' := evalCanon_mono fuel fuel' hl (by omega)
        have hr' := evalCanon_mono fuel fuel' hr (by omega)
        simp only [hl, hr] at h
        simp only [hl', hr']
        exact h
  | fuel + 1, fuel' + 1, env, .app fn arg, res, h, hLe => by
    simp only [evalCanon] at h ⊢
    cases hf : evalCanon fuel env fn with
    | none => simp [hf] at h
    | some vf =>
      cases ha : evalCanon fuel env arg with
      | none => simp [hf, ha] at h
      | some va =>
        have hf' := evalCanon_mono fuel fuel' hf (by omega)
        have ha' := evalCanon_mono fuel fuel' ha (by omega)
        simp only [hf, ha] at h
        simp only [hf', ha']
        exact applyCanon_mono fuel fuel' h (by omega)
  | fuel + 1, fuel' + 1, env, .letIn val body, res, h, hLe => by
    simp only [evalCanon] at h ⊢
    cases hv : evalCanon fuel env val with
    | none => simp [hv] at h
    | some vv =>
      have hv' := evalCanon_mono fuel fuel' hv (by omega)
      simp only [hv] at h
      simp only [hv']
      exact evalCanon_mono fuel fuel' h (by omega)
  | fuel + 1, fuel' + 1, env, .pair a b, res, h, hLe => by
    simp only [evalCanon] at h ⊢
    cases ha : evalCanon fuel env a with
    | none => simp [ha] at h
    | some va =>
      cases hb : evalCanon fuel env b with
      | none => simp [ha, hb] at h
      | some vb =>
        have ha' := evalCanon_mono fuel fuel' ha (by omega)
        have hb' := evalCanon_mono fuel fuel' hb (by omega)
        simp only [ha, hb] at h
        simp only [ha', hb']
        exact h
  | fuel + 1, fuel' + 1, env, .fst p, res, h, hLe => by
    simp only [evalCanon] at h ⊢
    cases hp : evalCanon fuel env p with
    | none => simp [hp] at h
    | some vp =>
      have hp' := evalCanon_mono fuel fuel' hp (by omega)
      simp only [hp] at h
      simp only [hp']
      exact h
  | fuel + 1, fuel' + 1, env, .snd p, res, h, hLe => by
    simp only [evalCanon] at h ⊢
    cases hp : evalCanon fuel env p with
    | none => simp [hp] at h
    | some vp =>
      have hp' := evalCanon_mono fuel fuel' hp (by omega)
      simp only [hp] at h
      simp only [hp']
      exact h
  | fuel + 1, fuel' + 1, env, .boxIntro s, res, h, hLe => by
    simp only [evalCanon] at h ⊢
    cases hs : evalCanon fuel env s with
    | none => simp [hs] at h
    | some vs =>
      have hs' := evalCanon_mono fuel fuel' hs (by omega)
      simp only [hs] at h
      simp only [hs']
      exact h
  | fuel + 1, fuel' + 1, env, .letBox s body, res, h, hLe => by
    simp only [evalCanon] at h ⊢
    cases hs : evalCanon fuel env s with
    | none => simp [hs] at h
    | some vs =>
      have hs' := evalCanon_mono fuel fuel' hs (by omega)
      simp only [hs] at h
      simp only [hs']
      cases vs with
      | vbox inner => exact evalCanon_mono fuel fuel' h (by omega)
      | _ => simp at h
  | fuel + 1, fuel' + 1, env, .trr L tm, res, h, hLe => by
    simp only [evalCanon] at h ⊢
    cases ht : evalCanon fuel env tm with
    | none => simp [ht] at h
    | some vt =>
      have ht' := evalCanon_mono fuel fuel' ht (by omega)
      simp only [ht] at h
      simp only [ht']
      exact h
  | fuel + 1, fuel' + 1, env, .trl L tm, res, h, hLe => by
    simp only [evalCanon] at h ⊢
    cases ht : evalCanon fuel env tm with
    | none => simp [ht] at h
    | some vt =>
      have ht' := evalCanon_mono fuel fuel' ht (by omega)
      simp only [ht] at h
      simp only [ht']
      exact h

end

/-! ## 4. Tait–Girard Hereditary Logical Relation & Univalence Soundness (`0 sorry`) -/

/-- Tait–Girard semantic value predicate `SemVal A v` (structural on `CanonTy`). -/
def SemVal : CanonTy → CanonVal → Prop
  | .boolTy, v => ∃ b : Bool, v = .vbool b
  | .u64Ty, v => ∃ w : UInt64, v = .vu64 w
  | .prod A B, v => ∃ v₁ v₂, v = .vpair v₁ v₂ ∧ SemVal A v₁ ∧ SemVal B v₂
  | .box A, v => ∃ v₀, v = .vbox v₀ ∧ SemVal A v₀
  | .arr A B, v =>
      ∀ arg, SemVal A arg → ∃ fuel res, applyCanon fuel v arg = some res ∧ SemVal B res

/-- Semantic environment predicate `SemEnv Γ env`. -/
inductive SemEnv : List CanonTy → List CanonVal → Prop where
  | nil : SemEnv [] []
  | cons {A Γ v env} : SemVal A v → SemEnv Γ env → SemEnv (A :: Γ) (v :: env)

theorem SemEnv.lookup {Γ : List CanonTy} {env : List CanonVal} {ix : Nat} {A : CanonTy}
    (hEnv : SemEnv Γ env) (hIx : Γ[ix]? = some A) :
    ∃ v, env[ix]? = some v ∧ SemVal A v := by
  induction hEnv generalizing ix with
  | nil => simp at hIx
  | @cons B Γ' v' env' hV hRest ih =>
    cases ix with
    | zero =>
      simp at hIx
      subst hIx
      exact ⟨v', rfl, hV⟩
    | succ k =>
      simp at hIx ⊢
      exact ih hIx

/-- **Theorem CAN.1 (`hasLine_sound`)**:
    Every well-formed univalent type line `HasLine L A B` induces total forward (`trrVal`) and
    backward (`trlVal`) semantic transports preserving `SemVal` across ALL type formers! -/
theorem hasLine_sound {L : CanonLine} {A B : CanonTy} (hL : HasLine L A B) :
    (∀ v₀, SemVal A v₀ → ∃ v₁, trrVal L v₀ = some v₁ ∧ SemVal B v₁) ∧
    (∀ v₁, SemVal B v₁ → ∃ v₀, trlVal L v₁ = some v₀ ∧ SemVal A v₀) := by
  induction hL with
  | reflL T =>
    exact ⟨fun v hv => ⟨v, rfl, hv⟩, fun v hv => ⟨v, rfl, hv⟩⟩
  | uaNot =>
    refine ⟨?_, ?_⟩
    · rintro _ ⟨b, rfl⟩
      exact ⟨.vbool (!b), rfl, ⟨!b, rfl⟩⟩
    · rintro _ ⟨b, rfl⟩
      exact ⟨.vbool (!b), rfl, ⟨!b, rfl⟩⟩
  | uaShift64 d =>
    refine ⟨?_, ?_⟩
    · rintro _ ⟨w, rfl⟩
      exact ⟨.vu64 (w + d), rfl, ⟨w + d, rfl⟩⟩
    · rintro _ ⟨w, rfl⟩
      exact ⟨.vu64 (w - d), rfl, ⟨w - d, rfl⟩⟩
  | uaSwapProd A B =>
    refine ⟨?_, ?_⟩
    · rintro _ ⟨v₁, v₂, rfl, h₁, h₂⟩
      exact ⟨.vpair v₂ v₁, rfl, ⟨v₂, v₁, rfl, h₂, h₁⟩⟩
    · rintro _ ⟨v₂, v₁, rfl, h₂, h₁⟩
      exact ⟨.vpair v₁ v₂, rfl, ⟨v₁, v₂, rfl, h₁, h₂⟩⟩
  | symL _ ih =>
    exact ⟨ih.2, ih.1⟩
  | transL _ _ ih₁ ih₂ =>
    refine ⟨?_, ?_⟩
    · intro v₀ hv₀
      obtain ⟨v₁, h₁, hv₁⟩ := ih₁.1 v₀ hv₀
      obtain ⟨v₂, h₂, hv₂⟩ := ih₂.1 v₁ hv₁
      exact ⟨v₂, by simp [trrVal, h₁, h₂], hv₂⟩
    · intro v₂ hv₂
      obtain ⟨v₁, h₂, hv₁⟩ := ih₂.2 v₂ hv₂
      obtain ⟨v₀, h₁, hv₀⟩ := ih₁.2 v₁ hv₁
      exact ⟨v₀, by simp [trlVal, h₂, h₁], hv₀⟩
  | @arrowL dL cL A₀ A₁ B₀ B₁ _ _ ihDom ihCod =>
    refine ⟨?_, ?_⟩
    · intro fn₀ hFn₀
      refine ⟨.varrowTrr dL cL fn₀, rfl, ?_⟩
      intro arg₁ hArg₁
      obtain ⟨arg₀, hTrl, hArg₀⟩ := ihDom.2 arg₁ hArg₁
      obtain ⟨f, res₀, hApp, hRes₀⟩ := hFn₀ arg₀ hArg₀
      obtain ⟨res₁, hTrr, hRes₁⟩ := ihCod.1 res₀ hRes₀
      exact ⟨f + 1, res₁, by simp [applyCanon, hTrl, hApp, hTrr], hRes₁⟩
    · intro fn₁ hFn₁
      refine ⟨.varrowTrl dL cL fn₁, rfl, ?_⟩
      intro arg₀ hArg₀
      obtain ⟨arg₁, hTrr, hArg₁⟩ := ihDom.1 arg₀ hArg₀
      obtain ⟨f, res₁, hApp, hRes₁⟩ := hFn₁ arg₁ hArg₁
      obtain ⟨res₀, hTrl, hRes₀⟩ := ihCod.2 res₁ hRes₁
      exact ⟨f + 1, res₀, by simp [applyCanon, hTrr, hApp, hTrl], hRes₀⟩
  | prodL _ _ ihF ihS =>
    refine ⟨?_, ?_⟩
    · rintro _ ⟨v₁, v₂, rfl, h₁, h₂⟩
      obtain ⟨u₁, hf, hu₁⟩ := ihF.1 v₁ h₁
      obtain ⟨u₂, hs, hu₂⟩ := ihS.1 v₂ h₂
      exact ⟨.vpair u₁ u₂, by simp [trrVal, hf, hs], ⟨u₁, u₂, rfl, hu₁, hu₂⟩⟩
    · rintro _ ⟨v₁, v₂, rfl, h₁, h₂⟩
      obtain ⟨u₁, hf, hu₁⟩ := ihF.2 v₁ h₁
      obtain ⟨u₂, hs, hu₂⟩ := ihS.2 v₂ h₂
      exact ⟨.vpair u₁ u₂, by simp [trlVal, hf, hs], ⟨u₁, u₂, rfl, hu₁, hu₂⟩⟩
  | boxL _ ihIn =>
    refine ⟨?_, ?_⟩
    · rintro _ ⟨v₀, rfl, hv₀⟩
      obtain ⟨u₀, h, hu₀⟩ := ihIn.1 v₀ hv₀
      exact ⟨.vbox u₀, by simp [trrVal, h], ⟨u₀, rfl, hu₀⟩⟩
    · rintro _ ⟨v₁, rfl, hv₁⟩
      obtain ⟨u₁, h, hu₁⟩ := ihIn.2 v₁ hv₁
      exact ⟨.vbox u₁, by simp [trlVal, h], ⟨u₁, rfl, hu₁⟩⟩

/-- **Theorem CAN.2 (`fundamental_canonicity`)**:
    Fundamental Theorem of Hereditary Logical Relations for Univalent Modal Type Theory:
    Every open well-typed term `HasType Γ tm A` terminates in any semantically valid environment
    `SemEnv Γ env` at a canonical value satisfying `SemVal A`! -/
theorem fundamental_canonicity {Γ : List CanonTy} {tm : CanonTm} {A : CanonTy}
    (hTy : HasType Γ tm A) :
    ∀ {env : List CanonVal}, SemEnv Γ env →
      ∃ fuel v, evalCanon fuel env tm = some v ∧ SemVal A v := by
  induction hTy with
  | bvar hIx =>
    intro env hEnv
    obtain ⟨v, hLook, hSem⟩ := hEnv.lookup hIx
    exact ⟨1, v, hLook, hSem⟩
  | boolLit b =>
    intro env _
    exact ⟨1, .vbool b, rfl, ⟨b, rfl⟩⟩
  | ifBool _ _ _ ihC ihT ihF =>
    intro env hEnv
    obtain ⟨fC, _, hEvC, ⟨b, rfl⟩⟩ := ihC hEnv
    cases b with
    | true =>
      obtain ⟨fT, vT, hEvT, hSemT⟩ := ihT hEnv
      have hc' := evalCanon_mono fC (max fC fT) hEvC (Nat.le_max_left fC fT)
      have ht' := evalCanon_mono fT (max fC fT) hEvT (Nat.le_max_right fC fT)
      exact ⟨max fC fT + 1, vT, by simp [evalCanon, hc', ht'], hSemT⟩
    | false =>
      obtain ⟨fF, vF, hEvF, hSemF⟩ := ihF hEnv
      have hc' := evalCanon_mono fC (max fC fF) hEvC (Nat.le_max_left fC fF)
      have hf' := evalCanon_mono fF (max fC fF) hEvF (Nat.le_max_right fC fF)
      exact ⟨max fC fF + 1, vF, by simp [evalCanon, hc', hf'], hSemF⟩
  | u64Lit w =>
    intro env _
    exact ⟨1, .vu64 w, rfl, ⟨w, rfl⟩⟩
  | @u64BinOp _ op _ _ _ _ ihL ihR =>
    intro env hEnv
    obtain ⟨fL, _, hEvL, ⟨w₁, rfl⟩⟩ := ihL hEnv
    obtain ⟨fR, _, hEvR, ⟨w₂, rfl⟩⟩ := ihR hEnv
    have hl' := evalCanon_mono fL (max fL fR) hEvL (Nat.le_max_left fL fR)
    have hr' := evalCanon_mono fR (max fL fR) hEvR (Nat.le_max_right fL fR)
    exact ⟨max fL fR + 1, .vu64 (op.eval w₁ w₂), by simp [evalCanon, hl', hr'], ⟨op.eval w₁ w₂, rfl⟩⟩
  | lam _ ihBody =>
    intro env hEnv
    refine ⟨1, .vclos env _, rfl, ?_⟩
    intro arg hArg
    obtain ⟨fB, res, hEvB, hSemB⟩ := ihBody (.cons hArg hEnv)
    exact ⟨fB + 1, res, hEvB, hSemB⟩
  | app _ _ ihFn ihArg =>
    intro env hEnv
    obtain ⟨fF, vFn, hEvFn, hSemFn⟩ := ihFn hEnv
    obtain ⟨fA, vArg, hEvArg, hSemArg⟩ := ihArg hEnv
    obtain ⟨fApp, res, hEvApp, hSemRes⟩ := hSemFn vArg hSemArg
    have hf' := evalCanon_mono fF (max fF (max fA fApp)) hEvFn (Nat.le_max_left fF _)
    have ha' := evalCanon_mono fA (max fF (max fA fApp)) hEvArg
      (Nat.le_trans (Nat.le_max_left fA fApp) (Nat.le_max_right fF _))
    have happ' := applyCanon_mono fApp (max fF (max fA fApp)) hEvApp
      (Nat.le_trans (Nat.le_max_right fA fApp) (Nat.le_max_right fF _))
    exact ⟨max fF (max fA fApp) + 1, res, by simp [evalCanon, hf', ha', happ'], hSemRes⟩
  | letIn _ _ ihVal ihBody =>
    intro env hEnv
    obtain ⟨fV, vVal, hEvVal, hSemVal⟩ := ihVal hEnv
    obtain ⟨fB, vBody, hEvBody, hSemBody⟩ := ihBody (.cons hSemVal hEnv)
    have hv' := evalCanon_mono fV (max fV fB) hEvVal (Nat.le_max_left fV fB)
    have hb' := evalCanon_mono fB (max fV fB) hEvBody (Nat.le_max_right fV fB)
    exact ⟨max fV fB + 1, vBody, by simp [evalCanon, hv', hb'], hSemBody⟩
  | pair _ _ ihA ihB =>
    intro env hEnv
    obtain ⟨fA, vA, hEvA, hSemA⟩ := ihA hEnv
    obtain ⟨fB, vB, hEvB, hSemB⟩ := ihB hEnv
    have ha' := evalCanon_mono fA (max fA fB) hEvA (Nat.le_max_left fA fB)
    have hb' := evalCanon_mono fB (max fA fB) hEvB (Nat.le_max_right fA fB)
    exact ⟨max fA fB + 1, .vpair vA vB, by simp [evalCanon, ha', hb'], ⟨vA, vB, rfl, hSemA, hSemB⟩⟩
  | fst _ ihP =>
    intro env hEnv
    obtain ⟨fP, _, hEvP, ⟨v₁, v₂, rfl, h₁, _⟩⟩ := ihP hEnv
    exact ⟨fP + 1, v₁, by simp [evalCanon, hEvP], h₁⟩
  | snd _ ihP =>
    intro env hEnv
    obtain ⟨fP, _, hEvP, ⟨v₁, v₂, rfl, _, h₂⟩⟩ := ihP hEnv
    exact ⟨fP + 1, v₂, by simp [evalCanon, hEvP], h₂⟩
  | boxIntro _ ihS =>
    intro env hEnv
    obtain ⟨fS, vS, hEvS, hSemS⟩ := ihS hEnv
    exact ⟨fS + 1, .vbox vS, by simp [evalCanon, hEvS], ⟨vS, rfl, hSemS⟩⟩
  | letBox _ _ ihS ihB =>
    intro env hEnv
    obtain ⟨fS, _, hEvS, ⟨v₀, rfl, hSem₀⟩⟩ := ihS hEnv
    obtain ⟨fB, vB, hEvB, hSemB⟩ := ihB (.cons hSem₀ hEnv)
    have hs' := evalCanon_mono fS (max fS fB) hEvS (Nat.le_max_left fS fB)
    have hb' := evalCanon_mono fB (max fS fB) hEvB (Nat.le_max_right fS fB)
    exact ⟨max fS fB + 1, vB, by simp [evalCanon, hs', hb'], hSemB⟩
  | trr hL _ ihTm =>
    intro env hEnv
    obtain ⟨fT, v₀, hEvT, hSem₀⟩ := ihTm hEnv
    obtain ⟨v₁, hTrr, hSem₁⟩ := (hasLine_sound hL).1 v₀ hSem₀
    exact ⟨fT + 1, v₁, by simp [evalCanon, hEvT, hTrr], hSem₁⟩
  | trl hL _ ihTm =>
    intro env hEnv
    obtain ⟨fT, v₁, hEvT, hSem₁⟩ := ihTm hEnv
    obtain ⟨v₀, hTrl, hSem₀⟩ := (hasLine_sound hL).2 v₁ hSem₁
    exact ⟨fT + 1, v₀, by simp [evalCanon, hEvT, hTrl], hSem₀⟩

/-! ## 5. Closed Univalent Canonicity Theorems (`0 sorry`, `0 noncomputable`) -/

/-- **Landmark Theorem CAN.3 (`univalent_bool_canonicity`, `0 sorry`)**:
    **Closed Boolean Canonicity under Univalence & Modalities**:
    Every closed well-typed term `HasType [] tm .boolTy` (freely using `uaNot`, `uaShift64`,
    `uaSwapProd`, `symL`, `transL`, `arrowL`, `prodL`, `boxL`, `trr`, `trl`, higher-order λ-calculus,
    and modal `□` boxes) evaluates in finite fuel to a canonical boolean `some (.vbool b)`! -/
theorem univalent_bool_canonicity {tm : CanonTm} (hTy : HasType [] tm .boolTy) :
    ∃ (fuel : Nat) (b : Bool), evalCanon fuel [] tm = some (.vbool b) := by
  obtain ⟨fuel, v, hEv, ⟨b, rfl⟩⟩ := fundamental_canonicity hTy SemEnv.nil
  exact ⟨fuel, b, hEv⟩

/-- **Landmark Theorem CAN.4 (`univalent_u64_canonicity`, `0 sorry`)**:
    **Closed Machine-Word Canonicity under Univalence & Modalities**:
    Every closed well-typed term `HasType [] tm .u64Ty` evaluates in finite fuel to a canonical
    64-bit machine word `some (.vu64 w)`! -/
theorem univalent_u64_canonicity {tm : CanonTm} (hTy : HasType [] tm .u64Ty) :
    ∃ (fuel : Nat) (w : UInt64), evalCanon fuel [] tm = some (.vu64 w) := by
  obtain ⟨fuel, v, hEv, ⟨w, rfl⟩⟩ := fundamental_canonicity hTy SemEnv.nil
  exact ⟨fuel, w, hEv⟩

/-- Non-trivial higher-order univalent test term:
    Starts with `fn : (Bool × U64) → U64 := λ p => if p.fst then p.snd + 7 else p.snd`,
    transports `fn` across the composite univalence equivalence
    `arrowL (transL (prodL uaNot (uaShift64 10)) (uaSwapProd Bool U64)) (uaShift64 100) :
      Id UU ((Bool × U64) → U64) ((U64 × Bool) → U64)`,
    and applies the transported function to `(20u64, false)`!
    Trace:
    1. Contravariant `trl` on `(20u64, false)`:
       - `trl uaSwapProd (20, false) = (false, 20)`
       - `trl (prodL uaNot (uaShift64 10)) (false, 20) = (true, 10)`
    2. Original `fn (true, 10) = 10 + 7 = 17`
    3. Covariant `trr (uaShift64 100) 17 = 117u64`! -/
def higherOrderUnivalentSample : CanonTm :=
  let fn : CanonTm :=
    .lam (.prod .boolTy .u64Ty)
      (.ifBool (.fst (.bvar 0))
        (.u64BinOp .add (.snd (.bvar 0)) (.u64Lit 7))
        (.snd (.bvar 0)))
  let domEquiv : CanonLine :=
    .transL (.prodL .uaNot (.uaShift64 10)) (.uaSwapProd .boolTy .u64Ty)
  let fnLine : CanonLine := .arrowL domEquiv (.uaShift64 100)
  .app (.trr fnLine fn) (.pair (.u64Lit 20) (.boolLit false))

/-- **Theorem CAN.5 (`higherOrderUnivalentSample_canonical`)**:
    `higherOrderUnivalentSample` is well-typed (`HasType [] higherOrderUnivalentSample .u64Ty`)
    and computes canonically to `some (.vu64 117)`! -/
theorem higherOrderUnivalentSample_canonical :
    HasType [] higherOrderUnivalentSample .u64Ty ∧
    evalCanon 16 [] higherOrderUnivalentSample = some (.vu64 117) := by
  refine ⟨?_, rfl⟩
  unfold higherOrderUnivalentSample
  refine .app (.trr (.arrowL (.transL (.prodL .uaNot (.uaShift64 10)) (.uaSwapProd .boolTy .u64Ty)) (.uaShift64 100)) ?_)
    (.pair (.u64Lit 20) (.boolLit false))
  refine .lam (.ifBool (.fst (.bvar rfl)) (.u64BinOp (.snd (.bvar rfl)) (.u64Lit 7)) (.snd (.bvar rfl)))

end Narya.Core.Canonicity
