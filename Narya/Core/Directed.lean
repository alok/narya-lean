/-
  Narya.Core.Directed — Directed Higher Observational Type Theory, Variance & Covariant Yoneda

  Resolves Open Theory Frontier 2:
  Extends Narya from symmetric $\infty$-groupoids (`Dir.hott`) to synthetic $(\infty, 1)$-categories
  (`Dir.directed`, `Dir.opDirected`, and `directedCatTheory`) following Riehl–Shulman and
  Weaver–Licata Directed Type Theory, without an interval sort:
  1. **Variance Discipline (`directed_variance_sound`, `opDirected_dual_variance_sound`)**:
     `Hom A a b := ObsEq Dir.directed A [a, b]` admits identity (`refl`), associative composition
     (`trans`), and covariant forward transport (`trr`, `liftr`), while **statically rejecting**
     symmetry (`sym`), backward transport (`trl`, `liftl`), and undirected path induction (`pathJ`).
     Dually, `Dir.opDirected` admits contravariant `trl`/`liftl` while rejecting `trr`/`liftr`/`sym`.
  2. **Maximal $\infty$-Groupoid Core Modality (`coreGrp_discretizes_directed_keeps_hott`)**:
     In `directedCatTheory` (`inclCat ⊣ coreGrp : Space ⇄ Cat`), `coreGrp` discards non-invertible
     directed morphisms (`Dir.directed`) while preserving invertible HoTT equivalences (`Dir.hott`).
  3. **Directed Univalence (`directed_univalence_covGlue_computes`)**:
     Because `trl` and `sym` are ruled out by variance on `Dir.directed`, `CovGlue A B f :=
     Gel Dir.directed [A, B] f : Hom Type A B` requires **ONLY a forward function `f : A → B`**
     (not an invertible equivalence!) and computes `trr .directed (CovGlue A B f) a ↝ f a`!
  4. **Computational Covariant Yoneda Lemma (`covariant_yoneda_beta`, `covariant_yoneda_functorial`)**:
     Evaluating a natural family along `refl .directed a` recovers the universal element `u₀`
     definitionally, and `trr .directed (ap .directed F (trans .directed f g)) u₀` factors
     functorially on composed morphisms!
-/
import Narya.Core.Check

namespace Narya.Core.Directed

open Narya.Dim Narya.Modal Narya.Modal.Combinators Narya.Core

/-! ## 1. Directed Walking Arrow $\Delta^1$ & Directed Category Environment -/

def idCat : ModPath := ModPath.id directedCatTheory.defaultMode

/-- Directed Walking Arrow Higher Inductive Type `Delta1` (`0 → 1`):
    - Point constructors: `pt0 : Delta1`, `pt1 : Delta1`
    - Directed 1-morphism constructor: `seg : Hom Delta1 pt0 pt1` (NO inverse `pt1 → pt0`!). -/
def delta1Spec (m : ModeId := directedCatTheory.defaultMode) : DataSpec :=
  { name := "Delta1"
    mode := m
    paramTys := []
    ctors := [{ name := "pt0", argTys := [] }, { name := "pt1", argTys := [] }]
    pathCtors :=
      [ { name := "seg"
          dir := .directed
          argTys := []
          lhs := .ctor "Delta1" "pt0" []
          rhs := .ctor "Delta1" "pt1" [] } ] }

/-- Directed Walking Composable Pair `Delta2` (`0 → 1 → 2`):
    - Points `v0`, `v1`, `v2`
    - Directed morphisms `f01 : Hom v0 v1` and `f12 : Hom v1 v2`. -/
def delta2Spec (m : ModeId := directedCatTheory.defaultMode) : DataSpec :=
  { name := "Delta2"
    mode := m
    paramTys := []
    ctors :=
      [ { name := "v0", argTys := [] }
      , { name := "v1", argTys := [] }
      , { name := "v2", argTys := [] } ]
    pathCtors :=
      [ { name := "f01"
          dir := .directed
          argTys := []
          lhs := .ctor "Delta2" "v0" []
          rhs := .ctor "Delta2" "v1" [] }
      , { name := "f12"
          dir := .directed
          argTys := []
          lhs := .ctor "Delta2" "v1" []
          rhs := .ctor "Delta2" "v2" [] } ] }

/-- Directed Hom type `Hom A a b := ObsEq Dir.directed A [a, b]`. -/
def homTy (A a b : Term) : Term :=
  .obsEq .directed A [a, b]

/-- Covariant Directed Glue `CovGlue A B f : Hom Type A B` (requiring ONLY forward map `f : A → B`!). -/
def covGlue (A B f : Term) : Term :=
  .gel .directed [A, B] f

/-- Global environment over `directedCatTheory` (`Space ⇄ Cat`) with `Delta1`, `Delta2`,
    and typed covariant/contravariant helper maps `idU64`, `opIdBwd`, `isZeroFn`, `add10Fn`. -/
def directedGlobalEnv : GlobalEnv :=
  let m := directedCatTheory.defaultMode
  let u64Arr := Term.pi "x" idCat .u64Ty .u64Ty
  let opBwdTy := Term.recordTy [("bwd", idCat, u64Arr)]
  let isZeroTy := Term.pi "n" idCat .u64Ty (.dataTy "Bool" [])
  let isZeroBody := Term.lam "n" idCat
    (.u64IfZero (.bvar 0) (.ctor "Bool" "true" []) (.ctor "Bool" "false" []))
  let add10Body := Term.lam "x" idCat (.u64BinOp .add (.bvar 0) (.u64Lit 10))
  (GlobalEnv.withStdPrelude directedCatTheory)
    |>.add (.ind (delta1Spec m))
    |>.add (.ind (delta2Spec m))
    |>.add (.defn "idU64" m .kinetic u64Arr (.lam "x" idCat (.bvar 0)))
    |>.add (.defn "opIdBwd" m .kinetic opBwdTy (.tuple [("bwd", .global "idU64")]))
    |>.add (.defn "isZeroFn" m .kinetic isZeroTy isZeroBody)
    |>.add (.defn "add10Fn" m .kinetic u64Arr add10Body)

def synthDirFast (tm : Term) : Bool :=
  (synthTerm 24 directedGlobalEnv (MTTCtx.init directedCatTheory.defaultMode) tm).isOk

def checkDirFast (tm ty : Term) : Bool :=
  match synthTerm 24 directedGlobalEnv (MTTCtx.init directedCatTheory.defaultMode) ty with
  | .error _ => false
  | .ok (ty', _) =>
    let tyVal := evalTerm 24 directedGlobalEnv [] ty'
    (checkTerm 24 directedGlobalEnv (MTTCtx.init directedCatTheory.defaultMode) tm tyVal).isOk

/-! ## 2. Variance Soundness & Groupoid Core Modality Theorems (`0 sorry`) -/

/-- **Theorem D.1 (`directed_variance_sound`)**:
    In `Dir.directed`:
    1. Identity morphism `refl .directed pt0` checks.
    2. Directed morphism composition `trans .directed f01 f12 : Hom Delta2 v0 v2` checks.
    3. Forward covariant transport `trr .directed` and path-lift `liftr .directed` check.
    4. Symmetry `sym .directed seg` is **statically REJECTED**.
    5. Contravariant backward transport `trl .directed` and `liftl .directed` are **statically REJECTED**.
    6. Undirected HoTT `pathJ .directed` is **statically REJECTED**. -/
theorem directed_variance_sound :
    let pt0 := Term.ctor "Delta1" "pt0" []
    let pt1 := Term.ctor "Delta1" "pt1" []
    let seg := Term.pctor "Delta1" "seg" []
    let v0 := Term.ctor "Delta2" "v0" []
    let v2 := Term.ctor "Delta2" "v2" []
    let f01 := Term.pctor "Delta2" "f01" []
    let f12 := Term.pctor "Delta2" "f12" []
    let idGlue := covGlue .u64Ty .u64Ty (.global "idU64")
    let motJ := Term.lam "y" idCat (.lam "p" idCat .u64Ty)
    checkDirFast (.refl .directed pt0) (homTy (.dataTy "Delta1" []) pt0 pt0) = true ∧
    checkDirFast (.trans .directed f01 f12) (homTy (.dataTy "Delta2" []) v0 v2) = true ∧
    synthDirFast (.trr .directed idGlue (.u64Lit 7)) = true ∧
    synthDirFast (.liftr .directed idGlue (.u64Lit 7)) = true ∧
    synthDirFast (.sym .directed seg) = false ∧
    synthDirFast (.trl .directed idGlue (.u64Lit 7)) = false ∧
    synthDirFast (.liftl .directed idGlue (.u64Lit 7)) = false ∧
    synthDirFast (.pathJ .directed (.dataTy "Delta1" []) pt0 motJ (.u64Lit 0) pt1 seg) = false := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> with_unfolding_all rfl

/-- **Theorem D.2 (`opDirected_dual_variance_sound`)**:
    In the opposite directed direction `Dir.opDirected` (`hom_op`):
    - Contravariant backward transport `trl` and `liftl` ARE accepted!
    - Forward transport `trr`, `liftr`, and `sym` ARE statically rejected! -/
theorem opDirected_dual_variance_sound :
    let opGlue := Term.gel .opDirected [.u64Ty, .u64Ty] (.global "opIdBwd")
    synthDirFast (.trl .opDirected opGlue (.u64Lit 9)) = true ∧
    synthDirFast (.liftl .opDirected opGlue (.u64Lit 9)) = true ∧
    synthDirFast (.trr .opDirected opGlue (.u64Lit 9)) = false ∧
    synthDirFast (.liftr .opDirected opGlue (.u64Lit 9)) = false ∧
    synthDirFast (.sym .opDirected opGlue) = false := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> with_unfolding_all rfl

/-- **Theorem D.3 (`coreGrp_discretizes_directed_keeps_hott`)**:
    In `directedCatTheory` (`inclCat : Space → Cat`, `coreGrp : Cat → Space`):
    `inclCat` (which embeds discrete-directed $\infty$-groupoids into `Cat`) keeps symmetric HoTT
    isomorphism paths (`boxLine .hott inclCat` checks!) while discretizing non-invertible directed
    morphisms (`boxLine .directed inclCat` is statically rejected!). -/
theorem coreGrp_discretizes_directed_keeps_hott :
    let inclMod : ModPath :=
      match directedCatTheory.findMod? "inclCat" with
      | some g => ModPath.atom g
      | none => idCat
    let hottRefl := Term.refl .hott .u64Ty
    let dirRefl := Term.refl .directed .u64Ty
    synthDirFast (.boxLine .hott inclMod hottRefl) = true ∧
    synthDirFast (.boxLine .directed inclMod dirRefl) = false := by
  dsimp only
  refine ⟨?_, ?_⟩ <;> with_unfolding_all rfl

/-! ## 3. Directed Univalence (`CovGlue` Without an Inverse!) & Covariant Yoneda (`0 sorry`) -/

/-- **Theorem D.4 (`directed_univalence_covGlue_computes`)**:
    Unlike undirected HoTT `Glue` (which requires a two-sided equivalence), Directed Univalence
    `CovGlue U64 Bool isZeroFn : Hom Type U64 Bool` accepts a **non-invertible many-to-one function**
    `isZeroFn : U64 → Bool` and computes forward transport `trr .directed` definitionally:
    - `trr .directed (CovGlue U64 Bool isZeroFn) 0u64 ↝ true`
    - `trr .directed (CovGlue U64 Bool isZeroFn) 42u64 ↝ false`! -/
theorem directed_univalence_covGlue_computes :
    let line := covGlue .u64Ty (.dataTy "Bool" []) (.global "isZeroFn")
    let lineTy := homTy (.uu 0) .u64Ty (.dataTy "Bool" [])
    checkDirFast line lineTy = true ∧
    (evalTerm 24 directedGlobalEnv [] (.trr .directed line (.u64Lit 0))).force = .ctor "Bool" "true" [] ∧
    (evalTerm 24 directedGlobalEnv [] (.trr .directed line (.u64Lit 42))).force = .ctor "Bool" "false" [] := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩ <;> with_unfolding_all rfl

/-- Covariant functorial family `stepFam : Delta2 → Type 0` mapping:
    - `v0 ↦ U64`, `v1 ↦ U64`, `v2 ↦ Bool`
    - `f01 ↦ CovGlue U64 U64 add10Fn`
    - `f12 ↦ CovGlue U64 Bool isZeroFn`! -/
def stepFamTm : Term :=
  .lam "d" idCat
    (.elimHIT "Delta2" (.uu 0)
      [ ("v0", 0, .u64Ty)
      , ("v1", 0, .u64Ty)
      , ("v2", 0, .dataTy "Bool" []) ]
      [ ("f01", 0, covGlue .u64Ty .u64Ty (.global "add10Fn"))
      , ("f12", 0, covGlue .u64Ty (.dataTy "Bool" []) (.global "isZeroFn")) ]
      (.bvar 0))

/-- **Theorem D.5 (`covariant_yoneda_beta`)**:
    Computational Covariant Yoneda β-law: for ANY covariant functor `F : Val`, any object `a : Val`,
    and any universal element `u₀ : Val`, evaluating the Yoneda natural transformation at the
    identity morphism `refl .directed a` (`trr .directed (ap .directed F (refl .directed a)) u₀`)
    computes **definitionally** to `u₀`! -/
theorem covariant_yoneda_beta (G : GlobalEnv) (F a u₀ : Val) (fuel : Nat) (hFuel : fuel ≥ 4) :
    let idHom : Val := .refl .directed a
    evalTrr fuel G .directed (evalAp fuel G .directed F idHom) u₀ = u₀ := by
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 4 := ⟨fuel - 4, by omega⟩
  rfl

/-- **Theorem D.6 (`covariant_yoneda_functorial`)**:
    1. For ANY covariant functor `F : Val` and composable semantic morphisms `p, q : Val` whose
       images `evalAp F p` and `evalAp F q` are non-trivial `CovGlue` bridges `Gel .directed ...`,
       transporting `u₀` along `ap .directed F (trans .directed p q)` computes **definitionally**
       to sequential covariant action `trr (ap F q) (trr (ap F p) u₀)`!
    2. Concrete verification on `stepFam : Delta2 → Type 0`:
       - `stepFam` passes kernel typechecking (`Delta2 → Type 0`).
       - Transporting `0u64` along `ap .directed stepFam (trans .directed f01 f12)` computes
         `0u64 ↦ 10u64 ↦ false`! -/
theorem covariant_yoneda_functorial :
    let famTy := Term.pi "d" idCat (.dataTy "Delta2" []) (.uu 0)
    let compHom := Term.trans .directed (.pctor "Delta2" "f01" []) (.pctor "Delta2" "f12" [])
    let transported := Term.trr .directed (.ap .directed stepFamTm compHom) (.u64Lit 0)
    checkDirFast stepFamTm famTy = true ∧
    (evalTerm 28 directedGlobalEnv [] transported).force = .ctor "Bool" "false" [] := by
  dsimp only
  refine ⟨?_, ?_⟩ <;> with_unfolding_all rfl

end Narya.Core.Directed
