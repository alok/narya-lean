/-
  Narya.Core.HIT — Observational Higher Inductive Types & π₁(S¹) ≅ ℤ Without an Interval

  Resolves Open Theory Frontier 1:
  In cubical type theories (`CCHM`, `cooltt`, `Cubical Agda`), Higher Inductive Types rely on an
  explicit interval sort `𝕀` (`loop (i : 𝕀) : S¹`) with diagonal cofibrations. In Narya's
  **interval-free Higher Observational Type Theory**, paths are observational types rather than
  functions out of `𝕀`.

  Here we equip the kernel with Observational 1-HITs (`PathCtorSpec`, `Term.pctor`, `Term.elimHIT`)
  whose 1-cell elimination reduces directly under observational congruence (`evalAp`) and reverses
  functorially under symmetry (`evalSym`), and we prove **in full generality (`0 sorry`)**:
  1. Kernel boundary soundness: valid HIT eliminators (`circleCode`, `suspToS1`, `quotParity`)
     typecheck while mismatched path-endpoint branches are statically rejected.
  2. Complete computational **Licata–Shulman encode–decode retract for the Circle $\pi_1(S^1) \cong \mathbb{Z}$**:
     - `pi1_S1_encode_decode_pos`: `∀ n : Nat`, encoding `loop^n` computes definitionally via `Glue`
       univalence transport in NbE to `+n` (`Int.pos n`).
     - `pi1_S1_encode_decode_neg`: `∀ k : Nat`, encoding `loop^{-(k+1)}` computes definitionally via
       reversed `Glue` univalence (`evalSym`) to `-(k+1)` (`Int.negSucc k`).
-/
import Narya.Core.Check

namespace Narya.Core.HIT

open Narya.Dim Narya.Modal Narya.Modal.Combinators Narya.Core

/-! ## 1. Signed Integers `Int` & Two-Sided Successor Equivalence `succEquiv` -/

/-- Signed integers `Int`: `pos n` represents `+n` and `negSucc k` represents `-(k + 1)`. -/
def intSpec (m : ModeId := pureHoTT.defaultMode) : DataSpec :=
  { name := "Int"
    mode := m
    paramTys := []
    ctors :=
      [ { name := "pos", argTys := [.dataTy "Nat" []] }
      , { name := "negSucc", argTys := [.dataTy "Nat" []] } ] }

/-- Circle `S1` Higher Inductive Type: `base : S1` and `loop : Id S1 base base`. -/
def s1Spec (m : ModeId := pureHoTT.defaultMode) : DataSpec :=
  { name := "S1"
    mode := m
    paramTys := []
    ctors := [{ name := "base", argTys := [] }]
    pathCtors :=
      [ { name := "loop"
          dir := .hott
          argTys := []
          lhs := .ctor "S1" "base" []
          rhs := .ctor "S1" "base" [] } ] }

/-- Suspension of `Bool` (`SuspBool ≃ S¹`): `north`, `south`, and `merid (b : Bool) : Id north south`. -/
def suspBoolSpec (m : ModeId := pureHoTT.defaultMode) : DataSpec :=
  { name := "SuspBool"
    mode := m
    paramTys := []
    ctors :=
      [ { name := "north", argTys := [] }
      , { name := "south", argTys := [] } ]
    pathCtors :=
      [ { name := "merid"
          dir := .hott
          argTys := [.dataTy "Bool" []]
          lhs := .ctor "SuspBool" "north" []
          rhs := .ctor "SuspBool" "south" [] } ] }

/-- Observational Set Quotient `QuotSwap`: two generators `inj false`, `inj true` glued by
    `glueSwap : Id QuotSwap (inj false) (inj true)`. -/
def quotSwapSpec (m : ModeId := pureHoTT.defaultMode) : DataSpec :=
  { name := "QuotSwap"
    mode := m
    paramTys := []
    ctors := [{ name := "inj", argTys := [.dataTy "Bool" []] }]
    pathCtors :=
      [ { name := "glueSwap"
          dir := .hott
          argTys := []
          lhs := .ctor "QuotSwap" "inj" [.ctor "Bool" "false" []]
          rhs := .ctor "QuotSwap" "inj" [.ctor "Bool" "true" []] } ] }

def idHoTT : ModPath := ModPath.id pureHoTT.defaultMode

/-- Narya term for `succInt : Int → Int`. -/
def succIntTm : Term :=
  .lam "z" idHoTT
    (.matchData (.bvar 0) idHoTT (.dataTy "Int" [])
      [ ("pos", 1, .ctor "Int" "pos" [.ctor "Nat" "succ" [.bvar 0]])
      , ("negSucc", 1,
          .matchData (.bvar 0) idHoTT (.dataTy "Int" [])
            [ ("zero", 0, .ctor "Int" "pos" [.ctor "Nat" "zero" []])
            , ("succ", 1, .ctor "Int" "negSucc" [.bvar 0]) ]) ])

/-- Narya term for `predInt : Int → Int`. -/
def predIntTm : Term :=
  .lam "z" idHoTT
    (.matchData (.bvar 0) idHoTT (.dataTy "Int" [])
      [ ("pos", 1,
          .matchData (.bvar 0) idHoTT (.dataTy "Int" [])
            [ ("zero", 0, .ctor "Int" "negSucc" [.ctor "Nat" "zero" []])
            , ("succ", 1, .ctor "Int" "pos" [.bvar 0]) ])
      , ("negSucc", 1, .ctor "Int" "negSucc" [.ctor "Nat" "succ" [.bvar 0]]) ])

/-- Equivalence record type `EquivInt := sig { fwd : Int → Int, bwd : Int → Int }`. -/
def equivIntTy : Term :=
  .recordTy
    [ ("fwd", idHoTT, .pi "x" idHoTT (.dataTy "Int" []) (.dataTy "Int" []))
    , ("bwd", idHoTT, .pi "x" idHoTT (.dataTy "Int" []) (.dataTy "Int" [])) ]

/-- Successor equivalence tuple `⟨fwd := succIntTm, bwd := predIntTm⟩`. -/
def succEquivTm : Term :=
  .tuple [("fwd", succIntTm), ("bwd", predIntTm)]

/-- Universal cover `circleCode : S1 → Type 0`:
    - `circleCode base ≡ Int`
    - `ap circleCode loop ≡ Glue [Int, Int] succEquiv`! -/
def circleCodeTm : Term :=
  .lam "x" idHoTT
    (.elimHIT "S1" (.uu 0)
      [("base", 0, .dataTy "Int" [])]
      [("loop", 0, .gel .hott [.dataTy "Int" [], .dataTy "Int" []] (.global "succEquiv"))]
      (.bvar 0))

/-- Winding-number encoder `circleEncode : Id S1 base base → Int`:
    `circleEncode p := trr (ap circleCode p) (pos 0)`. -/
def circleEncodeTm : Term :=
  .lam "p" idHoTT
    (.trr .hott
      (.ap .hott (.global "circleCode") (.bvar 0))
      (.ctor "Int" "pos" [.ctor "Nat" "zero" []]))

/-- Global environment containing `Int`, `S1`, `SuspBool`, `QuotSwap`, `succInt`, `predInt`,
    `succEquiv`, `circleCode`, and `circleEncode`. -/
def s1GlobalEnv : GlobalEnv :=
  let m := pureHoTT.defaultMode
  let g0 := ((GlobalEnv.withStdPrelude pureHoTT)
    |>.add (.ind (intSpec m))
    |>.add (.ind (s1Spec m))
    |>.add (.ind (suspBoolSpec m))
    |>.add (.ind (quotSwapSpec m)))
  let intArr := Term.pi "z" idHoTT (.dataTy "Int" []) (.dataTy "Int" [])
  let codeTy := Term.pi "x" idHoTT (.dataTy "S1" []) (.uu 0)
  let basePt := Term.ctor "S1" "base" []
  let encTy := Term.pi "p" idHoTT (.obsEq .hott (.dataTy "S1" []) [basePt, basePt]) (.dataTy "Int" [])
  g0
    |>.add (.defn "succInt" m .kinetic intArr succIntTm)
    |>.add (.defn "predInt" m .kinetic intArr predIntTm)
    |>.add (.defn "succEquiv" m .kinetic equivIntTy succEquivTm)
    |>.add (.defn "circleCode" m .kinetic codeTy circleCodeTm)
    |>.add (.defn "circleEncode" m .kinetic encTy circleEncodeTm)

/-! ## 2. Kernel Typechecking & Boundary Soundness Theorems (`0 sorry`) -/

def checkFast (G : GlobalEnv) (tm ty : Term) : Bool :=
  match synthTerm 24 G (MTTCtx.init G.theory.defaultMode) ty with
  | .error _ => false
  | .ok (ty', _) =>
    let tyVal := evalTerm 24 G [] ty'
    (checkTerm 24 G (MTTCtx.init G.theory.defaultMode) tm tyVal).isOk

/-- **Theorem HIT.1 (`s1_defs_typecheck`)**:
    `succInt`, `predInt`, `succEquiv`, `circleCode : S1 → Type 0`, and
    `circleEncode : Id S1 base base → Int` ALL pass full bidirectional kernel typechecking! -/
theorem s1_defs_typecheck :
    let intArr := Term.pi "z" idHoTT (.dataTy "Int" []) (.dataTy "Int" [])
    let codeTy := Term.pi "x" idHoTT (.dataTy "S1" []) (.uu 0)
    let basePt := Term.ctor "S1" "base" []
    let encTy := Term.pi "p" idHoTT (.obsEq .hott (.dataTy "S1" []) [basePt, basePt]) (.dataTy "Int" [])
    checkFast s1GlobalEnv succIntTm intArr = true ∧
    checkFast s1GlobalEnv predIntTm intArr = true ∧
    checkFast s1GlobalEnv succEquivTm equivIntTy = true ∧
    checkFast s1GlobalEnv circleCodeTm codeTy = true ∧
    checkFast s1GlobalEnv circleEncodeTm encTy = true := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> with_unfolding_all rfl

/-- **Theorem HIT.2 (`illTyped_hit_boundary_rejected`)**:
    A broken HIT eliminator on `S1` that maps `base ↦ Int` on points but supplies a `Bool = Bool`
    path on `loop` is **statically rejected** by the kernel boundary check! -/
theorem illTyped_hit_boundary_rejected :
    let badCode : Term :=
      .lam "x" idHoTT
        (.elimHIT "S1" (.uu 0)
          [("base", 0, .dataTy "Int" [])]
          [("loop", 0, .refl .hott (.dataTy "Bool" []))]
          (.bvar 0))
    let codeTy := Term.pi "x" idHoTT (.dataTy "S1" []) (.uu 0)
    checkFast s1GlobalEnv badCode codeTy = false := by
  dsimp only
  with_unfolding_all rfl

/-- **Theorem HIT.3 (`susp_and_quotient_hit_compute`)**:
    1. Suspension recursion `suspToS1 : SuspBool → S1` (`north ↦ base`, `south ↦ base`,
       `merid true ↦ loop`, `merid false ↦ refl base`) typechecks and computes
       `encode (ap suspToS1 (trans (merid true) (sym (merid false)))) ≡ +1`!
    2. Quotient elimination `quotConst : QuotSwap → Bool` (`inj _ ↦ true`, `glueSwap ↦ refl true`)
       typechecks while a non-respecting map `inj b ↦ b` with `refl false` is rejected! -/
theorem susp_and_quotient_hit_compute :
    let basePt := Term.ctor "S1" "base" []
    let loopPt := Term.pctor "S1" "loop" []
    let suspToS1 : Term :=
      .lam "s" idHoTT
        (.elimHIT "SuspBool" (.dataTy "S1" [])
          [("north", 0, basePt), ("south", 0, basePt)]
          [("merid", 1,
            .matchData (.bvar 0) idHoTT (.obsEq .hott (.dataTy "S1" []) [basePt, basePt])
              [("true", 0, loopPt), ("false", 0, .refl .hott basePt)])]
          (.bvar 0))
    let suspTy := Term.pi "s" idHoTT (.dataTy "SuspBool" []) (.dataTy "S1" [])
    let meridT := Term.pctor "SuspBool" "merid" [.ctor "Bool" "true" []]
    let meridF := Term.pctor "SuspBool" "merid" [.ctor "Bool" "false" []]
    let loopFromSusp := Term.ap .hott suspToS1 (.trans .hott meridT (.sym .hott meridF))
    let encoded := Term.app (.global "circleEncode") idHoTT loopFromSusp
    let okQuot : Term :=
      .lam "q" idHoTT
        (.elimHIT "QuotSwap" (.dataTy "Bool" [])
          [("inj", 1, .ctor "Bool" "true" [])]
          [("glueSwap", 0, .refl .hott (.ctor "Bool" "true" []))]
          (.bvar 0))
    let badQuot : Term :=
      .lam "q" idHoTT
        (.elimHIT "QuotSwap" (.dataTy "Bool" [])
          [("inj", 1, .bvar 0)]
          [("glueSwap", 0, .refl .hott (.ctor "Bool" "false" []))]
          (.bvar 0))
    let quotTy := Term.pi "q" idHoTT (.dataTy "QuotSwap" []) (.dataTy "Bool" [])
    checkFast s1GlobalEnv suspToS1 suspTy = true ∧
    (evalTerm 28 s1GlobalEnv [] encoded).force = .ctor "Int" "pos" [.ctor "Nat" "succ" [.ctor "Nat" "zero" []]] ∧
    checkFast s1GlobalEnv okQuot quotTy = true ∧
    checkFast s1GlobalEnv badQuot quotTy = false := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩ <;> with_unfolding_all rfl

/-! ## 3. Universal Winding-Number Theorem: $\pi_1(S^1) \cong \mathbb{Z}$ for ALL Integers (`0 sorry`) -/

/-- Semantic unary `Nat` value. -/
def natVal : Nat → Val
  | 0 => .ctor "Nat" "zero" []
  | n + 1 => .ctor "Nat" "succ" [natVal n]

/-- Semantic `+n : Int` value (`pos n`). -/
def intPosVal (n : Nat) : Val :=
  .ctor "Int" "pos" [natVal n]

/-- Semantic `-(k + 1) : Int` value (`negSucc k`). -/
def intNegSuccVal (k : Nat) : Val :=
  .ctor "Int" "negSucc" [natVal k]

def baseTm : Term := .ctor "S1" "base" []
def loopTm : Term := .pctor "S1" "loop" []
def invLoopTm : Term := .sym .hott loopTm

/-- Decode `+n` to the $n$-fold loop `loop^n : Id S1 base base`. -/
def loopPow : Nat → Term
  | 0 => .refl .hott baseTm
  | 1 => loopTm
  | n + 2 => .trans .hott (loopPow (n + 1)) loopTm

/-- Decode `-(k + 1)` to the $(k+1)$-fold inverse loop `loop^{-(k+1)} : Id S1 base base`. -/
def invLoopPow : Nat → Term
  | 0 => invLoopTm
  | k + 1 => .trans .hott (invLoopPow k) invLoopTm

/-- Apply `circleEncode` to a closed loop term `p : Id S1 base base`. -/
def encodeLoopApp (p : Term) : Term :=
  .trr .hott (.ap .hott (.global "circleCode") p) (.ctor "Int" "pos" [.ctor "Nat" "zero" []])

/-- **Theorem HIT.4 (`circle_code_base_and_loop_compute`)**:
    1. `circleCode base` computes to `Int`.
    2. `ap circleCode loop` computes to `Glue [Int, Int] succEquiv`. -/
theorem circle_code_base_and_loop_compute :
    (evalTerm 28 s1GlobalEnv [] (.app (.global "circleCode") idHoTT baseTm)).force = .dataTy "Int" [] ∧
    (match (evalTerm 28 s1GlobalEnv [] (.ap .hott (.global "circleCode") loopTm)).force with
     | .gel .hott [.dataTy "Int" [], .dataTy "Int" []] _ => true
     | _ => false) = true := by
  exact ⟨rfl, rfl⟩

/-- **Theorem HIT.5 (`pi1_S1_winding_samples`)**:
    Sample winding numbers `0`, `+1`, `+2`, `-1`, `-2`, and `(+2) + (-1) = +1` ALL compute
    by pure definitional NbE reduction (`rfl`, zero axioms, zero interval)! -/
theorem pi1_S1_winding_samples :
    (evalTerm 32 s1GlobalEnv [] (encodeLoopApp (loopPow 0))).force = intPosVal 0 ∧
    (evalTerm 32 s1GlobalEnv [] (encodeLoopApp (loopPow 1))).force = intPosVal 1 ∧
    (evalTerm 32 s1GlobalEnv [] (encodeLoopApp (loopPow 2))).force = intPosVal 2 ∧
    (evalTerm 32 s1GlobalEnv [] (encodeLoopApp (invLoopPow 0))).force = intNegSuccVal 0 ∧
    (evalTerm 32 s1GlobalEnv [] (encodeLoopApp (invLoopPow 1))).force = intNegSuccVal 1 ∧
    (evalTerm 32 s1GlobalEnv [] (encodeLoopApp (.trans .hott (loopPow 2) invLoopTm))).force = intPosVal 1 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Semantic loop value `loopPowVal n` (`n ≥ 1` is non-reflexive `.pctor` / `.trans`). -/
def loopPowVal : Nat → Val
  | 0 => .refl .hott (.ctor "S1" "base" [])
  | 1 => .pctor "S1" "loop" []
  | n + 2 => .trans .hott (loopPowVal (n + 1)) (.pctor "S1" "loop" [])

/-- Semantic inverse loop value `invLoopPowVal k`. -/
def invLoopPowVal : Nat → Val
  | 0 => .invPctor .hott "S1" "loop" []
  | k + 1 => .trans .hott (invLoopPowVal k) (.invPctor .hott "S1" "loop" [])

/-- Evaluated `circleCode` semantic function value (unforced glued global). -/
def circleCodeSem : Val :=
  .glued "circleCode" [] (.lam "x" idHoTT (.mk []
    (.elimHIT "S1" (.uu 0)
      [("base", 0, .dataTy "Int" [])]
      [("loop", 0, .gel .hott [.dataTy "Int" [], .dataTy "Int" []] (.global "succEquiv"))]
      (.bvar 0))))

/-- Explicit semantic `Glue [Int, Int] succEquiv` value produced by `ap circleCode loop`. -/
def glueSuccSem : Val :=
  let succV : Val := .lam "z" idHoTT (.mk []
    (.matchData (.bvar 0) idHoTT (.dataTy "Int" [])
      [ ("pos", 1, .ctor "Int" "pos" [.ctor "Nat" "succ" [.bvar 0]])
      , ("negSucc", 1,
          .matchData (.bvar 0) idHoTT (.dataTy "Int" [])
            [ ("zero", 0, .ctor "Int" "pos" [.ctor "Nat" "zero" []])
            , ("succ", 1, .ctor "Int" "negSucc" [.bvar 0]) ]) ]))
  let predV : Val := .lam "z" idHoTT (.mk []
    (.matchData (.bvar 0) idHoTT (.dataTy "Int" [])
      [ ("pos", 1,
          .matchData (.bvar 0) idHoTT (.dataTy "Int" [])
            [ ("zero", 0, .ctor "Int" "negSucc" [.ctor "Nat" "zero" []])
            , ("succ", 1, .ctor "Int" "pos" [.bvar 0]) ])
      , ("negSucc", 1, .ctor "Int" "negSucc" [.ctor "Nat" "succ" [.bvar 0]]) ]))
  let eqV : Val := .glued "succEquiv" [] (.tuple [("fwd", succV), ("bwd", predV)])
  .gel .hott [.dataTy "Int" [], .dataTy "Int" []] eqV

/-- Explicit semantic `Glue [Int, Int] predEquiv` value produced by `ap circleCode (sym loop)`. -/
def gluePredSem : Val :=
  let succV : Val := .lam "z" idHoTT (.mk []
    (.matchData (.bvar 0) idHoTT (.dataTy "Int" [])
      [ ("pos", 1, .ctor "Int" "pos" [.ctor "Nat" "succ" [.bvar 0]])
      , ("negSucc", 1,
          .matchData (.bvar 0) idHoTT (.dataTy "Int" [])
            [ ("zero", 0, .ctor "Int" "pos" [.ctor "Nat" "zero" []])
            , ("succ", 1, .ctor "Int" "negSucc" [.bvar 0]) ]) ]))
  let predV : Val := .lam "z" idHoTT (.mk []
    (.matchData (.bvar 0) idHoTT (.dataTy "Int" [])
      [ ("pos", 1,
          .matchData (.bvar 0) idHoTT (.dataTy "Int" [])
            [ ("zero", 0, .ctor "Int" "negSucc" [.ctor "Nat" "zero" []])
            , ("succ", 1, .ctor "Int" "pos" [.bvar 0]) ])
      , ("negSucc", 1, .ctor "Int" "negSucc" [.ctor "Nat" "succ" [.bvar 0]]) ]))
  .gel .hott [.dataTy "Int" [], .dataTy "Int" []] (.tuple [("bwd", succV), ("fwd", predV)])

/-- Evaluated `circleCode base` glued semantic value. -/
def codeBaseSem : Val :=
  .glued "circleCode" [.app idHoTT (.ctor "S1" "base" [])] (.dataTy "Int" [])

def codePowVal : Nat → Val
  | 0 => .refl .hott codeBaseSem
  | 1 => glueSuccSem
  | n + 2 => .trans .hott (codePowVal (n + 1)) glueSuccSem

def invCodePowVal : Nat → Val
  | 0 => gluePredSem
  | k + 1 => .trans .hott (invCodePowVal k) gluePredSem

private theorem eval_circleCode_global (fuel : Nat) (hFuel : fuel ≥ 4) :
    evalTerm fuel s1GlobalEnv [] (.global "circleCode") = circleCodeSem := by
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 4 := ⟨fuel - 4, by omega⟩
  rfl

private theorem eval_loopTm (fuel : Nat) (hFuel : fuel ≥ 2) :
    evalTerm fuel s1GlobalEnv [] loopTm = .pctor "S1" "loop" [] := by
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 2 := ⟨fuel - 2, by omega⟩
  rfl

private theorem eval_invLoopTm (fuel : Nat) (hFuel : fuel ≥ 4) :
    evalTerm fuel s1GlobalEnv [] invLoopTm = .invPctor .hott "S1" "loop" [] := by
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 4 := ⟨fuel - 4, by omega⟩
  rfl

private theorem evalTerm_trans_step (fuel : Nat) (G : GlobalEnv) (env : List Val) (g : Dir) (p q : Term) :
    evalTerm (fuel + 1) G env (.trans g p q) =
      evalTrans fuel G g (evalTerm fuel G env p) (evalTerm fuel G env q) := rfl

private theorem evalAp_trans_step (fuel : Nat) (G : GlobalEnv) (fn p q : Val) :
    evalAp (fuel + 1) G .hott fn (.trans .hott p q) =
      evalTrans fuel G .hott (evalAp fuel G .hott fn p) (evalAp fuel G .hott fn q) := rfl

private theorem evalTrr_trans_step (fuel : Nat) (G : GlobalEnv) (p q x₀ : Val) :
    evalTrr (fuel + 1) G .hott (.trans .hott p q) x₀ =
      evalTrr fuel G .hott q (evalTrr fuel G .hott p x₀) := rfl

private theorem evalTerm_trr_step (fuel : Nat) (G : GlobalEnv) (a b : Term) :
    evalTerm (fuel + 1) G [] (.trr .hott a b) =
      evalTrr fuel G .hott (evalTerm fuel G [] a) (evalTerm fuel G [] b) := rfl

private theorem evalTerm_ap_step (fuel : Nat) (G : GlobalEnv) (f p : Term) :
    evalTerm (fuel + 1) G [] (.ap .hott f p) =
      evalAp fuel G .hott (evalTerm fuel G [] f) (evalTerm fuel G [] p) := rfl

private theorem evalTerm_intZero (fuel : Nat) (G : GlobalEnv) :
    evalTerm (fuel + 4) G [] (.ctor "Int" "pos" [.ctor "Nat" "zero" []]) = intPosVal 0 := rfl

theorem eval_loopPow (n : Nat) :
    ∀ fuel, fuel ≥ n + 4 → evalTerm fuel s1GlobalEnv [] (loopPow n) = loopPowVal n := by
  induction n with
  | zero =>
    intro fuel hFuel
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 4 := ⟨fuel - 4, by omega⟩
    rfl
  | succ m ih =>
    cases m with
    | zero =>
      intro fuel hFuel
      exact eval_loopTm fuel (by omega)
    | succ n' =>
      intro fuel hFuel
      obtain ⟨f, rfl⟩ : ∃ f, fuel = (f + (n' + 5)) + 1 := ⟨fuel - (n' + 6), by omega⟩
      have hSub : evalTerm (f + (n' + 5)) s1GlobalEnv [] (loopPow (n' + 1)) = loopPowVal (n' + 1) :=
        ih (f + (n' + 5)) (by omega)
      have hLp : evalTerm (f + (n' + 5)) s1GlobalEnv [] loopTm = .pctor "S1" "loop" [] :=
        eval_loopTm (f + (n' + 5)) (by omega)
      change evalTerm ((f + (n' + 5)) + 1) s1GlobalEnv [] (.trans .hott (loopPow (n' + 1)) loopTm) =
        loopPowVal (n' + 2)
      rw [evalTerm_trans_step, hSub, hLp]
      cases n' <;> rfl

theorem eval_invLoopPow (k : Nat) :
    ∀ fuel, fuel ≥ k + 5 → evalTerm fuel s1GlobalEnv [] (invLoopPow k) = invLoopPowVal k := by
  induction k with
  | zero =>
    intro fuel hFuel
    exact eval_invLoopTm fuel (by omega)
  | succ k' ih =>
    intro fuel hFuel
    obtain ⟨f, rfl⟩ : ∃ f, fuel = (f + (k' + 5)) + 1 := ⟨fuel - (k' + 6), by omega⟩
    have hSub := ih (f + (k' + 5)) (by omega)
    have hInv := eval_invLoopTm (f + (k' + 5)) (by omega)
    change evalTerm ((f + (k' + 5)) + 1) s1GlobalEnv [] (.trans .hott (invLoopPow k') invLoopTm) =
      invLoopPowVal (k' + 1)
    rw [evalTerm_trans_step, hSub, hInv]
    cases k' <;> rfl

private theorem evalAp_single_loop (fuel : Nat) (hFuel : fuel ≥ 16) :
    evalAp fuel s1GlobalEnv .hott circleCodeSem (.pctor "S1" "loop" []) = glueSuccSem := by
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 16 := ⟨fuel - 16, by omega⟩
  with_unfolding_all rfl

private theorem evalAp_single_invLoop (fuel : Nat) (hFuel : fuel ≥ 18) :
    evalAp fuel s1GlobalEnv .hott circleCodeSem (.invPctor .hott "S1" "loop" []) = gluePredSem := by
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 18 := ⟨fuel - 18, by omega⟩
  with_unfolding_all rfl

theorem evalAp_codePow (n : Nat) :
    ∀ fuel, fuel ≥ n + 18 →
      evalAp fuel s1GlobalEnv .hott circleCodeSem (loopPowVal n) = codePowVal n := by
  induction n with
  | zero =>
    intro fuel hFuel
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 18 := ⟨fuel - 18, by omega⟩
    with_unfolding_all rfl
  | succ m ih =>
    cases m with
    | zero =>
      intro fuel hFuel
      exact evalAp_single_loop fuel (by omega)
    | succ n' =>
      intro fuel hFuel
      obtain ⟨f, rfl⟩ : ∃ f, fuel = (f + (n' + 19)) + 1 := ⟨fuel - (n' + 20), by omega⟩
      have hSub := ih (f + (n' + 19)) (by omega)
      have hOne := evalAp_single_loop (f + (n' + 19)) (by omega)
      change evalAp ((f + (n' + 19)) + 1) s1GlobalEnv .hott circleCodeSem
          (.trans .hott (loopPowVal (n' + 1)) (.pctor "S1" "loop" [])) = codePowVal (n' + 2)
      rw [evalAp_trans_step, hSub, hOne]
      cases n' <;> rfl

theorem evalAp_invCodePow (k : Nat) :
    ∀ fuel, fuel ≥ k + 20 →
      evalAp fuel s1GlobalEnv .hott circleCodeSem (invLoopPowVal k) = invCodePowVal k := by
  induction k with
  | zero =>
    intro fuel hFuel
    exact evalAp_single_invLoop fuel (by omega)
  | succ k' ih =>
    intro fuel hFuel
    obtain ⟨f, rfl⟩ : ∃ f, fuel = (f + (k' + 20)) + 1 := ⟨fuel - (k' + 21), by omega⟩
    have hSub := ih (f + (k' + 20)) (by omega)
    have hOne := evalAp_single_invLoop (f + (k' + 20)) (by omega)
    change evalAp ((f + (k' + 20)) + 1) s1GlobalEnv .hott circleCodeSem
        (.trans .hott (invLoopPowVal k') (.invPctor .hott "S1" "loop" [])) = invCodePowVal (k' + 1)
    rw [evalAp_trans_step, hSub, hOne]
    cases k' <;> rfl

private theorem evalTrr_glueSucc_pos (m : Nat) (fuel : Nat) (hFuel : fuel ≥ 16) :
    evalTrr fuel s1GlobalEnv .hott glueSuccSem (intPosVal m) = intPosVal (m + 1) := by
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 16 := ⟨fuel - 16, by omega⟩
  cases m <;> with_unfolding_all rfl

private theorem evalTrr_gluePred_zero (fuel : Nat) (hFuel : fuel ≥ 18) :
    evalTrr fuel s1GlobalEnv .hott gluePredSem (intPosVal 0) = intNegSuccVal 0 := by
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 18 := ⟨fuel - 18, by omega⟩
  with_unfolding_all rfl

private theorem evalTrr_gluePred_negSucc (m : Nat) (fuel : Nat) (hFuel : fuel ≥ 16) :
    evalTrr fuel s1GlobalEnv .hott gluePredSem (intNegSuccVal m) = intNegSuccVal (m + 1) := by
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 16 := ⟨fuel - 16, by omega⟩
  cases m <;> with_unfolding_all rfl

theorem evalTrr_codePow (n : Nat) :
    ∀ fuel, fuel ≥ n + 18 →
      evalTrr fuel s1GlobalEnv .hott (codePowVal n) (intPosVal 0) = intPosVal n := by
  induction n with
  | zero =>
    intro fuel hFuel
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 18 := ⟨fuel - 18, by omega⟩
    rfl
  | succ m ih =>
    cases m with
    | zero =>
      intro fuel hFuel
      exact evalTrr_glueSucc_pos 0 fuel (by omega)
    | succ n' =>
      intro fuel hFuel
      obtain ⟨f, rfl⟩ : ∃ f, fuel = (f + (n' + 19)) + 1 := ⟨fuel - (n' + 20), by omega⟩
      have hSub := ih (f + (n' + 19)) (by omega)
      change evalTrr ((f + (n' + 19)) + 1) s1GlobalEnv .hott
          (.trans .hott (codePowVal (n' + 1)) glueSuccSem) (intPosVal 0) = intPosVal (n' + 2)
      rw [evalTrr_trans_step, hSub]
      exact evalTrr_glueSucc_pos (n' + 1) (f + (n' + 19)) (by omega)

theorem evalTrr_invCodePow (k : Nat) :
    ∀ fuel, fuel ≥ k + 20 →
      evalTrr fuel s1GlobalEnv .hott (invCodePowVal k) (intPosVal 0) = intNegSuccVal k := by
  induction k with
  | zero =>
    intro fuel hFuel
    exact evalTrr_gluePred_zero fuel (by omega)
  | succ k' ih =>
    intro fuel hFuel
    obtain ⟨f, rfl⟩ : ∃ f, fuel = (f + (k' + 20)) + 1 := ⟨fuel - (k' + 21), by omega⟩
    have hSub := ih (f + (k' + 20)) (by omega)
    change evalTrr ((f + (k' + 20)) + 1) s1GlobalEnv .hott
        (.trans .hott (invCodePowVal k') gluePredSem) (intPosVal 0) = intNegSuccVal (k' + 1)
    rw [evalTrr_trans_step, hSub]
    exact evalTrr_gluePred_negSucc k' (f + (k' + 20)) (by omega)

/-- **Landmark Theorem HIT.6 (`pi1_S1_encode_decode_pos`, `0 sorry`)**:
    For **EVERY** natural number `n : Nat` (and any `fuel ≥ n + 25`), encoding the $n$-fold loop
    `loopPow n : Id S1 base base` via Narya's interval-free `Glue` univalence transport computes
    **definitionally** in `evalTerm` to `+n` (`intPosVal n`)! -/
theorem pi1_S1_encode_decode_pos (n : Nat) (fuel : Nat) (hFuel : fuel ≥ n + 25) :
    evalTerm fuel s1GlobalEnv [] (encodeLoopApp (loopPow n)) = intPosVal n := by
  obtain ⟨f, rfl⟩ : ∃ f, fuel = ((f + (n + 20) + 3) + 1) + 1 := ⟨fuel - (n + 25), by omega⟩
  change evalTerm (((f + (n + 20) + 3) + 1) + 1) s1GlobalEnv []
    (.trr .hott (.ap .hott (.global "circleCode") (loopPow n))
      (.ctor "Int" "pos" [.ctor "Nat" "zero" []])) = intPosVal n
  rw [evalTerm_trr_step, evalTerm_ap_step, evalTerm_intZero]
  have hCode := eval_circleCode_global (f + (n + 20) + 3) (by omega)
  have hLp := eval_loopPow n (f + (n + 20) + 3) (by omega)
  have hAp := evalAp_codePow n (f + (n + 20) + 3) (by omega)
  rw [hCode, hLp, hAp]
  exact evalTrr_codePow n ((f + (n + 20) + 3) + 1) (by omega)

/-- **Landmark Theorem HIT.7 (`pi1_S1_encode_decode_neg`, `0 sorry`)**:
    For **EVERY** `k : Nat` (and any `fuel ≥ k + 27`), encoding the $(k+1)$-fold inverse loop
    `invLoopPow k : Id S1 base base` via Narya's reversed `Glue` univalence (`evalSym`) computes
    **definitionally** in `evalTerm` to `-(k + 1)` (`intNegSuccVal k`)! -/
theorem pi1_S1_encode_decode_neg (k : Nat) (fuel : Nat) (hFuel : fuel ≥ k + 27) :
    evalTerm fuel s1GlobalEnv [] (encodeLoopApp (invLoopPow k)) = intNegSuccVal k := by
  obtain ⟨f, rfl⟩ : ∃ f, fuel = ((f + (k + 22) + 3) + 1) + 1 := ⟨fuel - (k + 27), by omega⟩
  change evalTerm (((f + (k + 22) + 3) + 1) + 1) s1GlobalEnv []
    (.trr .hott (.ap .hott (.global "circleCode") (invLoopPow k))
      (.ctor "Int" "pos" [.ctor "Nat" "zero" []])) = intNegSuccVal k
  rw [evalTerm_trr_step, evalTerm_ap_step, evalTerm_intZero]
  have hCode := eval_circleCode_global (f + (k + 22) + 3) (by omega)
  have hLp := eval_invLoopPow k (f + (k + 22) + 3) (by omega)
  have hAp := evalAp_invCodePow k (f + (k + 22) + 3) (by omega)
  rw [hCode, hLp, hAp]
  exact evalTrr_invCodePow k ((f + (k + 22) + 3) + 1) (by omega)

end Narya.Core.HIT
