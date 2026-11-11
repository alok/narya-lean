/-
  Narya.Core.Equal — 3-Tier Glued & Type-Directed η Conversion Checker

  Faithful port of OCaml Narya's `lib/core/equal.ml` and `lib/core/EQUAL.md`:
  - **Tier 1 (Glued/Neutral Spine Fast-Path)**: Compares matching global glued heads
    or neutral heads by spine equality *before* unfolding definitions or η-expanding
    codata/records (preventing exponential η-blowup).
  - **Tier 2 (Type-Directed η-Laws)**: Expands functions at `Π`-types and projections
    across dependent record / negative modal codata telescopes (including 0-field η!).
  - **Tier 3 (Canonical Structural Conversion)**: Forces glued values and checks
    structural equality across universes, modalities, datatypes, and Gel/HoTT bridges.
-/
import Narya.Core.NbE

namespace Narya.Core

open Narya.Dim Narya.Modal Narya.Modal.KeySynth

/-- Build `[vvar (base + k - 1), ..., vvar base]` for opening an `arity`-binder branch body in NbE. -/
def freshBranchVars (base : Nat) : Nat → List Val
  | 0 => []
  | k + 1 => freshBranchVars (base + 1) k ++ [.vvar base]

/-- Kernel-reducible α-structural `Term` equality fast-path (fuel-bounded so Lean 4 compiles it
    via `Nat.rec` rather than opaque `partial` `instBEqTerm.beq`, preventing divergence when
    comparing neutral `matchData`/`elimHIT` branches that invoke recursive `.potential` globals). -/
def termFastEq : Nat → Term → Term → Bool
  | 0, _, _ => false
  | fuel + 1, t₁, t₂ =>
    match t₁, t₂ with
    | .bvar i₁, .bvar i₂ => i₁ == i₂
    | .mvar i₁, .mvar i₂ => i₁ == i₂
    | .global n₁, .global n₂ => strEq n₁ n₂
    | .uu l₁, .uu l₂ => l₁ == l₂
    | .uuExt l₁, .uuExt l₂ => l₁ == l₂
    | .pi _ m₁ d₁ c₁, .pi _ m₂ d₂ c₂ =>
      decide (m₁ = m₂) && termFastEq fuel d₁ d₂ && termFastEq fuel c₁ c₂
    | .lam _ m₁ b₁, .lam _ m₂ b₂ =>
      decide (m₁ = m₂) && termFastEq fuel b₁ b₂
    | .app f₁ m₁ a₁, .app f₂ m₂ a₂ =>
      decide (m₁ = m₂) && termFastEq fuel f₁ f₂ && termFastEq fuel a₁ a₂
    | .letIn _ ty₁ v₁ b₁, .letIn _ ty₂ v₂ b₂ =>
      termFastEq fuel ty₁ ty₂ && termFastEq fuel v₁ v₂ && termFastEq fuel b₁ b₂
    | .modalBox m₁ a₁, .modalBox m₂ a₂ => decide (m₁ = m₂) && termFastEq fuel a₁ a₂
    | .boxIntro m₁ a₁, .boxIntro m₂ a₂ => decide (m₁ = m₂) && termFastEq fuel a₁ a₂
    | .proj s₁ f₁, .proj s₂ f₂ => strEq f₁ f₂ && termFastEq fuel s₁ s₂
    | .dataTy n₁ [], .dataTy n₂ [] => strEq n₁ n₂
    | .ctor d₁ c₁ [], .ctor d₂ c₂ [] => strEq d₁ d₂ && strEq c₁ c₂
    | .ctor d₁ c₁ [x₁], .ctor d₂ c₂ [x₂] =>
      strEq d₁ d₂ && strEq c₁ c₂ && termFastEq fuel x₁ x₂
    | .pctor d₁ p₁ [], .pctor d₂ p₂ [] => strEq d₁ d₂ && strEq p₁ p₂
    | .refl g₁ a₁, .refl g₂ a₂ => decide (g₁ = g₂) && termFastEq fuel a₁ a₂
    | .sym g₁ a₁, .sym g₂ a₂ => decide (g₁ = g₂) && termFastEq fuel a₁ a₂
    | .ungel g₁ a₁, .ungel g₂ a₂ => decide (g₁ = g₂) && termFastEq fuel a₁ a₂
    | .ap g₁ f₁ a₁, .ap g₂ f₂ a₂ =>
      decide (g₁ = g₂) && termFastEq fuel f₁ f₂ && termFastEq fuel a₁ a₂
    | .trr g₁ f₁ a₁, .trr g₂ f₂ a₂ =>
      decide (g₁ = g₂) && termFastEq fuel f₁ f₂ && termFastEq fuel a₁ a₂
    | .trl g₁ f₁ a₁, .trl g₂ f₂ a₂ =>
      decide (g₁ = g₂) && termFastEq fuel f₁ f₂ && termFastEq fuel a₁ a₂
    | .trans g₁ f₁ a₁, .trans g₂ f₂ a₂ =>
      decide (g₁ = g₂) && termFastEq fuel f₁ f₂ && termFastEq fuel a₁ a₂
    | .u64Ty, .u64Ty => true
    | .u64Lit a₁, .u64Lit a₂ => a₁ == a₂
    | .u64BinOp op₁ l₁ r₁, .u64BinOp op₂ l₂ r₂ =>
      decide (op₁ = op₂) && termFastEq fuel l₁ l₂ && termFastEq fuel r₁ r₂
    | .u64IfZero c₁ z₁ nz₁, .u64IfZero c₂ z₂ nz₂ =>
      termFastEq fuel c₁ c₂ && termFastEq fuel z₁ z₂ && termFastEq fuel nz₁ nz₂
    | _, _ => false

mutual

/-- Compare two semantic values (untyped / universe-level structural equality with glued fast-path). -/
def equalVal (fuel : Nat) (G : GlobalEnv) (depth : Nat) (v₁ v₂ : Val) : Bool :=
  match fuel with
  | 0 => false
  | fuel' + 1 =>
    -- Tier 1a: Glued fast-path (same defined constant head without forcing!)
    match v₁, v₂ with
    | .glued n₁ sp₁ f₁, .glued n₂ sp₂ f₂ =>
      if strEq n₁ n₂ && equalSpines fuel' G depth sp₁ sp₂ then true
      else equalVal fuel' G depth f₁ f₂
    | .glued _ _ f₁, _ => equalVal fuel' G depth f₁ v₂
    | _, .glued _ _ f₂ => equalVal fuel' G depth v₁ f₂
    | .neu h₁ sp₁, .neu h₂ sp₂ =>
      (h₁ == h₂) && equalSpines fuel' G depth sp₁ sp₂
    | .uu l₁, .uu l₂ => l₁ == l₂
    | .uuExt l₁, .uuExt l₂ => l₁ == l₂
    | .pi _ m₁ d₁ c₁, .pi _ m₂ d₂ c₂ =>
      decide (m₁ = m₂) &&
      equalVal fuel' G depth d₁ d₂ &&
      let x := Val.vvar depth
      equalVal fuel' G (depth + 1) (evalClosure fuel' G c₁ x) (evalClosure fuel' G c₂ x)
    | .lam _ m₁ b₁, .lam _ m₂ b₂ =>
      decide (m₁ = m₂) &&
      let x := Val.vvar depth
      equalVal fuel' G (depth + 1) (evalClosure fuel' G b₁ x) (evalClosure fuel' G b₂ x)
    | .modalBox m₁ t₁, .modalBox m₂ t₂ =>
      decide (m₁ = m₂) && equalVal fuel' G depth t₁ t₂
    | .boxIntro m₁ a₁, .boxIntro m₂ a₂ =>
      decide (m₁ = m₂) && equalVal fuel' G depth a₁ a₂
    | .recordTy env₁ fs₁, .recordTy env₂ fs₂ =>
      equalRecordTele fuel' G depth env₁ env₂ fs₁ fs₂
    | .tuple fs₁, .tuple fs₂ =>
      equalTupleFields fuel' G depth fs₁ fs₂
    | .dataTy n₁ ps₁, .dataTy n₂ ps₂ =>
      strEq n₁ n₂ && equalValLists fuel' G depth ps₁ ps₂
    | .ctor d₁ c₁ as₁, .ctor d₂ c₂ as₂ =>
      strEq d₁ d₂ && strEq c₁ c₂ && equalValLists fuel' G depth as₁ as₂
    | .pctor d₁ p₁ as₁, .pctor d₂ p₂ as₂ =>
      strEq d₁ d₂ && strEq p₁ p₂ && equalValLists fuel' G depth as₁ as₂
    | .invPctor g₁ d₁ p₁ as₁, .invPctor g₂ d₂ p₂ as₂ =>
      (g₁ == g₂) && strEq d₁ d₂ && strEq p₁ p₂ && equalValLists fuel' G depth as₁ as₂
    | .obsEq g₁ ty₁ es₁, .obsEq g₂ ty₂ es₂ =>
      (g₁ == g₂) && equalVal fuel' G depth ty₁ ty₂ && equalValLists fuel' G depth es₁ es₂
    | .obsHet g₁ tb₁ es₁, .obsHet g₂ tb₂ es₂ =>
      (g₁ == g₂) && equalVal fuel' G depth tb₁ tb₂ && equalValLists fuel' G depth es₁ es₂
    | .refl g₁ a₁, .refl g₂ a₂ =>
      (g₁ == g₂) && equalVal fuel' G depth a₁ a₂
    | .trans g₁ p₁ q₁, .trans g₂ p₂ q₂ =>
      (g₁ == g₂) && equalVal fuel' G depth p₁ p₂ && equalVal fuel' G depth q₁ q₂
    | .gel g₁ ts₁ r₁, .gel g₂ ts₂ r₂ =>
      (g₁ == g₂) && equalValLists fuel' G depth ts₁ ts₂ && equalVal fuel' G depth r₁ r₂
    | .gelIntro g₁ es₁ w₁, .gelIntro g₂ es₂ w₂ =>
      (g₁ == g₂) && equalValLists fuel' G depth es₁ es₂ && equalVal fuel' G depth w₁ w₂
    | .arrowLine g₁ m₁ d₁ c₁, .arrowLine g₂ m₂ d₂ c₂ =>
      (g₁ == g₂) && decide (m₁ = m₂) && equalVal fuel' G depth d₁ d₂ && equalVal fuel' G depth c₁ c₂
    | .piLine g₁ _ m₁ d₁ e₁ c0₁ c1₁ cL₁, .piLine g₂ _ m₂ d₂ e₂ c0₂ c1₂ cL₂ =>
      let v0 := Val.vvar depth
      let v1 := Val.vvar (depth + 1)
      let v2 := Val.vvar (depth + 2)
      (g₁ == g₂) && decide (m₁ = m₂) &&
      equalVal fuel' G depth d₁ d₂ &&
      equalVal fuel' G (depth + 1) (evalTerm fuel' G (v0 :: e₁) c0₁) (evalTerm fuel' G (v0 :: e₂) c0₂) &&
      equalVal fuel' G (depth + 1) (evalTerm fuel' G (v0 :: e₁) c1₁) (evalTerm fuel' G (v0 :: e₂) c1₂) &&
      equalVal fuel' G (depth + 3) (evalTerm fuel' G (v2 :: v1 :: v0 :: e₁) cL₁)
        (evalTerm fuel' G (v2 :: v1 :: v0 :: e₂) cL₂)
    | .prodLine g₁ f₁ s₁ a₁ b₁, .prodLine g₂ f₂ s₂ a₂ b₂ =>
      (g₁ == g₂) && strEq f₁ f₂ && strEq s₁ s₂ &&
      equalVal fuel' G depth a₁ a₂ && equalVal fuel' G depth b₁ b₂
    | .sigLine g₁ f₁ s₁ fm₁ sm₁ fl₁ e₁ s0₁ s1₁ sL₁, .sigLine g₂ f₂ s₂ fm₂ sm₂ fl₂ e₂ s0₂ s1₂ sL₂ =>
      let v0 := Val.vvar depth
      let v1 := Val.vvar (depth + 1)
      let v2 := Val.vvar (depth + 2)
      (g₁ == g₂) && strEq f₁ f₂ && strEq s₁ s₂ &&
      decide (fm₁ = fm₂) && decide (sm₁ = sm₂) &&
      equalVal fuel' G depth fl₁ fl₂ &&
      equalVal fuel' G (depth + 1) (evalTerm fuel' G (v0 :: e₁) s0₁) (evalTerm fuel' G (v0 :: e₂) s0₂) &&
      equalVal fuel' G (depth + 1) (evalTerm fuel' G (v0 :: e₁) s1₁) (evalTerm fuel' G (v0 :: e₂) s1₂) &&
      equalVal fuel' G (depth + 3) (evalTerm fuel' G (v2 :: v1 :: v0 :: e₁) sL₁)
        (evalTerm fuel' G (v2 :: v1 :: v0 :: e₂) sL₂)
    | .boxLine g₁ m₁ in₁, .boxLine g₂ m₂ in₂ =>
      (g₁ == g₂) && decide (m₁ = m₂) && equalVal fuel' G depth in₁ in₂
    | .liftr g₁ l₁ x₁, .liftr g₂ l₂ x₂ =>
      (g₁ == g₂) && equalVal fuel' G depth l₁ l₂ && equalVal fuel' G depth x₁ x₂
    | .liftl g₁ l₁ x₁, .liftl g₂ l₂ x₂ =>
      (g₁ == g₂) && equalVal fuel' G depth l₁ l₂ && equalVal fuel' G depth x₁ x₂
    | .funext g₁ m₁ e₁ b₁, .funext g₂ m₂ e₂ b₂ =>
      let v0 := Val.vvar depth
      let v1 := Val.vvar (depth + 1)
      let v2 := Val.vvar (depth + 2)
      (g₁ == g₂) && decide (m₁ = m₂) &&
      equalVal fuel' G (depth + 3) (evalTerm fuel' G (v2 :: v1 :: v0 :: e₁) b₁)
        (evalTerm fuel' G (v2 :: v1 :: v0 :: e₂) b₂)
    | .u64Ty, .u64Ty => true
    | .u64Lit a, .u64Lit b => a == b
    | _, _ => false

/-- Type-directed conversion `G; depth ⊢ v₁ ≡ v₂ : ty` implementing Narya's `EQUAL.md` 3-tier order:
    1. Neutral/glued spine fast-path BEFORE η-expansion!
    2. Type-directed η-expansion on `Π` and `recordTy` (including negative modal codata!).
    3. Fallback to `equalVal`. -/
def equalAt (fuel : Nat) (G : GlobalEnv) (depth : Nat) (ty : Val) (v₁ v₂ : Val) : Bool :=
  match fuel with
  | 0 => false
  | fuel' + 1 =>
    -- Tier 1: Neutral / Glued Spine Fast-Path BEFORE η-expansion (`EQUAL.md`)!
    let fastPath : Bool :=
      match v₁, v₂ with
      | .neu h₁ sp₁, .neu h₂ sp₂ => (h₁ == h₂) && equalSpines fuel' G depth sp₁ sp₂
      | .glued n₁ sp₁ _, .glued n₂ sp₂ _ => (n₁ == n₂) && equalSpines fuel' G depth sp₁ sp₂
      | _, _ => false
    if fastPath then true
    else
      -- Tier 2: Type-Directed η-Expansion
      match ty.force with
      | .pi _ mod _ cod =>
        let x := Val.vvar depth
        let app₁ := applyVal fuel' G v₁ mod x
        let app₂ := applyVal fuel' G v₂ mod x
        let codTy := evalClosure fuel' G cod x
        equalAt fuel' G (depth + 1) codTy app₁ app₂
      | .recordTy env fields =>
        equalAtRecord fuel' G depth env fields v₁ v₂
      | _ =>
        -- Tier 3: Structural / Glued Unfolding
        equalVal fuel' G depth v₁ v₂

def equalAtRecord (fuel : Nat) (G : GlobalEnv) (depth : Nat) (env : List Val)
    (fields : List (String × ModPath × Term)) (v₁ v₂ : Val) : Bool :=
  match fields with
  | [] => true
  | (fname, _, ftyTm) :: rest =>
    match fuel with
    | 0 => false
    | fuel' + 1 =>
      let fty := evalTerm fuel' G env ftyTm
      let p₁ := projVal fuel' G v₁ fname
      let p₂ := projVal fuel' G v₂ fname
      equalAt fuel' G depth fty p₁ p₂ &&
      equalAtRecord fuel' G depth (p₁ :: env) rest v₁ v₂

def equalRecordTele (fuel : Nat) (G : GlobalEnv) (depth : Nat) (env₁ env₂ : List Val)
    (fs₁ fs₂ : List (String × ModPath × Term)) : Bool :=
  match fs₁, fs₂ with
  | [], [] => true
  | (n₁, m₁, t₁) :: r₁, (n₂, m₂, t₂) :: r₂ =>
    match fuel with
    | 0 => false
    | fuel' + 1 =>
      strEq n₁ n₂ && decide (m₁ = m₂) &&
      equalVal fuel' G depth (evalTerm fuel' G env₁ t₁) (evalTerm fuel' G env₂ t₂) &&
      let x := Val.vvar depth
      equalRecordTele fuel' G (depth + 1) (x :: env₁) (x :: env₂) r₁ r₂
  | _, _ => false

def equalTupleFields (fuel : Nat) (G : GlobalEnv) (depth : Nat)
    (fs₁ fs₂ : List (String × Val)) : Bool :=
  match fs₁, fs₂ with
  | [], [] => true
  | (n₁, v₁) :: r₁, (n₂, v₂) :: r₂ =>
    match fuel with
    | 0 => false
    | fuel' + 1 =>
      strEq n₁ n₂ && equalVal fuel' G depth v₁ v₂ && equalTupleFields fuel' G depth r₁ r₂
  | _, _ => false

def equalValLists (fuel : Nat) (G : GlobalEnv) (depth : Nat) (xs ys : List Val) : Bool :=
  match xs, ys with
  | [], [] => true
  | x :: xr, y :: yr =>
    match fuel with
    | 0 => false
    | fuel' + 1 => equalVal fuel' G depth x y && equalValLists fuel' G depth xr yr
  | _, _ => false

def equalBranches (fuel : Nat) (G : GlobalEnv) (depth : Nat)
    (env₁ env₂ : List Val)
    (bs₁ bs₂ : List (String × Nat × Term)) : Bool :=
  match bs₁, bs₂ with
  | [], [] => true
  | (c₁, ar₁, t₁) :: r₁, (c₂, ar₂, t₂) :: r₂ =>
    match fuel with
    | 0 => false
    | fuel' + 1 =>
      let sameHead := strEq c₁ c₂ && (ar₁ == ar₂)
      let bodyOk :=
        if termFastEq fuel' t₁ t₂ && equalValLists fuel' G depth env₁ env₂ then
          true
        else
          let fvs := freshBranchVars depth ar₁
          equalVal fuel' G (depth + ar₁)
            (evalTerm fuel' G (fvs ++ env₁) t₁)
            (evalTerm fuel' G (fvs ++ env₂) t₂)
      sameHead && bodyOk && equalBranches fuel' G depth env₁ env₂ r₁ r₂
  | _, _ => false

def equalSpines (fuel : Nat) (G : GlobalEnv) (depth : Nat) (s₁ s₂ : List Elim) : Bool :=
  match s₁, s₂ with
  | [], [] => true
  | e₁ :: r₁, e₂ :: r₂ =>
    match fuel with
    | 0 => false
    | fuel' + 1 => equalElim fuel' G depth e₁ e₂ && equalSpines fuel' G depth r₁ r₂
  | _, _ => false

def equalElim (fuel : Nat) (G : GlobalEnv) (depth : Nat) (e₁ e₂ : Elim) : Bool :=
  match fuel with
  | 0 => false
  | fuel' + 1 =>
    match e₁, e₂ with
    | .app m₁ a₁, .app m₂ a₂ => (m₁ == m₂) && equalVal fuel' G depth a₁ a₂
    | .proj f₁, .proj f₂ => f₁ == f₂
    | .key c₁, .key c₂ => norm2Cell G.theory c₁ == norm2Cell G.theory c₂
    | .sym g₁, .sym g₂ => g₁ == g₂
    | .ap g₁ fn₁, .ap g₂ fn₂ => (g₁ == g₂) && equalVal fuel' G depth fn₁ fn₂
    | .ungel g₁, .ungel g₂ => g₁ == g₂
    | .trr g₁ l₁, .trr g₂ l₂ => (g₁ == g₂) && equalVal fuel' G depth l₁ l₂
    | .trl g₁ l₁, .trl g₂ l₂ => (g₁ == g₂) && equalVal fuel' G depth l₁ l₂
    | .matchData w₁ m₁ b₁ e₁, .matchData w₂ m₂ b₂ e₂ =>
      decide (w₁ = w₂) && equalVal fuel' G depth m₁ m₂ && equalBranches fuel' G depth e₁ e₂ b₁ b₂
    | .elimHIT d₁ m₁ pt₁ pa₁ e₁, .elimHIT d₂ m₂ pt₂ pa₂ e₂ =>
      strEq d₁ d₂ && equalVal fuel' G depth m₁ m₂ &&
      equalBranches fuel' G depth e₁ e₂ pt₁ pt₂ &&
      equalBranches fuel' G depth e₁ e₂ pa₁ pa₂
    | .pathJ g₁ t₁ b₁ m₁ rc₁ tg₁, .pathJ g₂ t₂ b₂ m₂ rc₂ tg₂ =>
      (g₁ == g₂) &&
      equalVal fuel' G depth t₁ t₂ &&
      equalVal fuel' G depth b₁ b₂ &&
      equalVal fuel' G depth m₁ m₂ &&
      equalVal fuel' G depth rc₁ rc₂ &&
      equalVal fuel' G depth tg₁ tg₂
    | .hap g₁ a0₁ a1₁ pa₁, .hap g₂ a0₂ a1₂ pa₂ =>
      (g₁ == g₂) &&
      equalVal fuel' G depth a0₁ a0₂ &&
      equalVal fuel' G depth a1₁ a1₂ &&
      equalVal fuel' G depth pa₁ pa₂
    | .u64BinOpL op₁ r₁, .u64BinOpL op₂ r₂ =>
      (op₁ == op₂) && equalVal fuel' G depth r₁ r₂
    | .u64BinOpR op₁ l₁, .u64BinOpR op₂ l₂ =>
      (op₁ == op₂) && (l₁ == l₂)
    | .u64IfZero z₁ nz₁, .u64IfZero z₂ nz₂ =>
      equalVal fuel' G depth z₁ z₂ && equalVal fuel' G depth nz₁ nz₂
    | _, _ => false

end

/-- Convenience top-level conversion entry points using `defaultFuel`. -/
def convVal (G : GlobalEnv) (depth : Nat) (v₁ v₂ : Val) : Bool :=
  equalVal defaultFuel G depth v₁ v₂

def convAt (G : GlobalEnv) (depth : Nat) (ty : Val) (v₁ v₂ : Val) : Bool :=
  equalAt defaultFuel G depth ty v₁ v₂

end Narya.Core
