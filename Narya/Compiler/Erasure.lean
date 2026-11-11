/-
  Narya.Compiler.Erasure — Machine-Checked `Core.NbE` ↔ `HIR` ↔ `Arm64` Proof-Erasure Soundness

  Closes the end-to-end semantic verification loop from Narya's full higher-dimensional
  Glued Normalization-by-Evaluation kernel (`Narya.Core.evalTerm`) all the way down to
  the 64-bit `AArch64` register + aligned-stack machine (`Arm64.exec`):

    `Narya.Core.evalTerm` (with HoTT/univalence/modal proof `let`-bindings & 2-cell `.key`s)
      ══(`evalTerm_erasure_sound`, `0 sorry`)══▶ `HIR.eval` (`HIR.eraseFromCore`)
      ══(`compileFullPipeline_correct`, `0 sorry`)══▶ `Arm64.exec` (`x0` AAPCS64 return register!)

  Key Result (`core_nbe_to_arm64_correct`, `zero sorry`):
  For any closed `ErasableCore [] tm = true` (which permits arbitrary higher-dimensional
  observational/HoTT/modal proof `let`-bindings at `0`-graded unused positions alongside
  2-cell modal `.key` coercions, 64-bit ALU arithmetic, conditionals, and counted loops)
  and any `fuel ≥ minCoreFuel tm`:
    `(evalTerm fuel (abiGlobalEnv T arg0 arg1) [] tm).force =
       .u64Lit ((Arm64.exec (Arm64.compileFullPipeline (HIR.eraseFromCore tm))
                            (Arm64State.initABI arg0 arg1)).x0)`!
-/
import Narya.Core.NbE
import Narya.Compiler.Arm64

namespace Narya.Compiler

open Narya.Core Narya.Modal

/-- Standard 2-parameter AAPCS64 global environment binding `"arg0"` (`x0`) and `"arg1"` (`x1`). -/
def abiGlobalEnv (T : ModeTheory) (p₀ p₁ : UInt64) : GlobalEnv :=
  let m := T.defaultMode
  { theory := T
    entries := [
      .defn "arg0" m .kinetic .u64Ty (.u64Lit p₀),
      .defn "arg1" m .kinetic .u64Ty (.u64Lit p₁)
    ] }

/-- Semantic relation stating that a Narya `Val` denotes the unboxed 64-bit word `w : UInt64`
    (either directly as `.u64Lit w` or wrapped in a lazy transparent `.glued` node). -/
inductive ValDenotesU64 : Val → UInt64 → Prop where
  | raw (w : UInt64) : ValDenotesU64 (.u64Lit w) w
  | glued (name : String) (sp : List Elim) (w : UInt64) :
      ValDenotesU64 (.glued name sp (.u64Lit w)) w

theorem ValDenotesU64.force_eq {v : Val} {w : UInt64} (h : ValDenotesU64 v w) :
    v.force = .u64Lit w := by
  cases h <;> rfl

/-- Acting by ANY 2-cell modal key `cell : TwoCellExpr` preserves `ValDenotesU64`! -/
theorem ValDenotesU64.actKey_preserves (T : ModeTheory) (cell : TwoCellExpr)
    {v : Val} {w : UInt64} (h : ValDenotesU64 v w) :
    ValDenotesU64 (Val.actKey T cell v) w := by
  unfold Val.actKey
  dsimp only
  split
  · exact h
  · cases h with
    | raw w => exact ValDenotesU64.raw w
    | glued name sp w =>
      simp only [Val.actKeyGo]
      exact ValDenotesU64.glued name _ w

/-- Context simulation invariant indexed by `liveVars : List Bool`:
    - `true`: computational `U64` variable (`ValDenotesU64 v w`)
    - `false`: `0`-graded ghost / HoTT / modal proof binding (`v` can be ANY `Val`, never read at runtime!) -/
inductive EnvMatches : List Bool → List Val → List UInt64 → Prop where
  | nil : EnvMatches [] [] []
  | cons_live {bs : List Bool} {vs : List Val} {ws : List UInt64} {v : Val} {w : UInt64} :
      ValDenotesU64 v w → EnvMatches bs vs ws → EnvMatches (true :: bs) (v :: vs) (w :: ws)
  | cons_ghost {bs : List Bool} {vs : List Val} {ws : List UInt64} (v : Val) (w : UInt64) :
      EnvMatches bs vs ws → EnvMatches (false :: bs) (v :: vs) (w :: ws)

theorem envMatches_get {liveVars : List Bool} {vs : List Val} {ws : List UInt64}
    (hEnv : EnvMatches liveVars vs ws) (ix : Nat)
    (hLive : liveVars[ix]?.getD false = true) :
    ∃ v w, vs[ix]? = some v ∧ ws[ix]? = some w ∧ ValDenotesU64 v w := by
  induction hEnv generalizing ix with
  | nil => simp at hLive
  | cons_live hv _ ih =>
    cases ix with
    | zero => exact ⟨_, _, rfl, rfl, hv⟩
    | succ k =>
      simp only [List.getElem?_cons_succ] at hLive ⊢
      exact ih k hLive
  | cons_ghost _ _ _ ih =>
    cases ix with
    | zero => simp at hLive
    | succ k =>
      simp only [List.getElem?_cons_succ] at hLive ⊢
      exact ih k hLive

theorem envMatches_lookup {liveVars : List Bool} {vs : List Val} {ws : List UInt64}
    (hEnv : EnvMatches liveVars vs ws) (ix : Nat)
    (hLive : liveVars[ix]?.getD false = true) :
    ValDenotesU64 (lookupValEnv vs ix) (ws[ix]?.getD 0) := by
  obtain ⟨v, w, hv, hw, hDen⟩ := envMatches_get hEnv ix hLive
  simp only [lookupValEnv, hv, hw, Option.getD_some]
  exact hDen

/-- Syntactic predicate identifying `Core.Term` programs whose computational core erases cleanly
    to 64-bit `HIR` (allowing arbitrary HoTT/modal proof `letIn`s at unused `false` positions!). -/
def ErasableCore (liveVars : List Bool) : Term → Bool
  | .bvar ix => liveVars[ix]?.getD false
  | .u64Lit _ => true
  | .global name => strEq name "arg0" || strEq name "arg1"
  | .u64BinOp _ l r => ErasableCore liveVars l && ErasableCore liveVars r
  | .u64IfZero c z nz =>
    ErasableCore liveVars c && ErasableCore liveVars z && ErasableCore liveVars nz
  | .u64Repeat _ init step =>
    ErasableCore liveVars init && ErasableCore (true :: liveVars) step
  | .letIn _ _ val body =>
    (ErasableCore liveVars val && ErasableCore (true :: liveVars) body) ||
    ErasableCore (false :: liveVars) body
  | .key _ sub => ErasableCore liveVars sub
  | _ => false

/-- Sufficient NbE evaluation fuel for `evalTerm` to compute `tm` without fuel exhaustion. -/
def minCoreFuel : Term → Nat
  | .global _ => 2
  | .u64BinOp _ l r => Nat.max (Nat.max (minCoreFuel l) (minCoreFuel r)) 3 + 1
  | .u64IfZero c z nz => Nat.max (minCoreFuel c) (Nat.max (minCoreFuel z) (minCoreFuel nz)) + 1
  | .u64Repeat _ init step => Nat.max (minCoreFuel init) (minCoreFuel step) + 1
  | .letIn _ _ val body => Nat.max (minCoreFuel val) (minCoreFuel body) + 1
  | .key _ sub => minCoreFuel sub + 1
  | _ => 1

theorem minCoreFuel_pos (tm : Term) : 1 ≤ minCoreFuel tm := by
  cases tm <;> simp [minCoreFuel] <;> omega

/-- `evalU64BinOp` on any two `ValDenotesU64` operands with `fuel ≥ 3` produces `.u64Lit (op.eval a b)`. -/
theorem evalU64BinOp_denotes {fuel : Nat} (G : GlobalEnv) (op : BinOp64)
    {v₁ v₂ : Val} {a b : UInt64}
    (hv₁ : ValDenotesU64 v₁ a) (hv₂ : ValDenotesU64 v₂ b) (hFuel : 3 ≤ fuel) :
    ValDenotesU64 (evalU64BinOp fuel G op v₁ v₂) (op.eval a b) := by
  obtain ⟨f₃, rfl⟩ : ∃ k, fuel = k + 3 := ⟨fuel - 3, by omega⟩
  cases hv₁ with
  | raw a =>
    cases hv₂ with
    | raw b =>
      simp only [evalU64BinOp]
      exact ValDenotesU64.raw (op.eval a b)
    | glued n2 sp2 b =>
      simp only [evalU64BinOp]
      exact ValDenotesU64.raw (op.eval a b)
  | glued n1 sp1 a =>
    cases hv₂ with
    | raw b =>
      simp only [evalU64BinOp]
      exact ValDenotesU64.raw (op.eval a b)
    | glued n2 sp2 b =>
      simp only [evalU64BinOp]
      exact ValDenotesU64.raw (op.eval a b)

/-- Loop invariant lifting step-body soundness across `iterN n` iterations. -/
theorem iterN_erasure_sound (n : Nat) {fCore : Val → Val} {fHIR : UInt64 → UInt64}
    (hStep : ∀ {v : Val} {w : UInt64}, ValDenotesU64 v w → ValDenotesU64 (fCore v) (fHIR w))
    {v₀ : Val} {w₀ : UInt64} (hInit : ValDenotesU64 v₀ w₀) :
    ValDenotesU64 (iterN n fCore v₀) (iterN n fHIR w₀) := by
  induction n generalizing v₀ w₀ with
  | zero => exact hInit
  | succ k ih =>
    simp only [iterN]
    exact ih (hStep hInit)

/-- **Core NbE-to-HIR Erasure Soundness Theorem (`evalTerm_erasure_sound`, `0 sorry`)**:
    Evaluating any `ErasableCore` term in Narya's full Glued NbE engine (`evalTerm`)
    denotes the exact 64-bit `UInt64` value produced by `HIR.eval` on `HIR.eraseFromCore tm`! -/
theorem evalTerm_erasure_sound (T : ModeTheory) (p₀ p₁ : UInt64) :
    ∀ (tm : Term) {liveVars : List Bool} {vs : List Val} {ws : List UInt64} {fuel : Nat},
      ErasableCore liveVars tm = true →
      EnvMatches liveVars vs ws →
      minCoreFuel tm ≤ fuel →
      ValDenotesU64 (evalTerm fuel (abiGlobalEnv T p₀ p₁) vs tm)
                    (HIR.eval p₀ p₁ ws (HIR.eraseFromCore tm))
  | .bvar ix, _, _, _, fuel, hErase, hEnv, hFuel => by
    have hPos : 1 ≤ fuel := Nat.le_trans (minCoreFuel_pos _) hFuel
    obtain ⟨fuel', rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
    simp only [ErasableCore] at hErase
    simp only [evalTerm, HIR.eraseFromCore, HIR.eval]
    exact envMatches_lookup hEnv ix hErase

  | .u64Lit w, _, _, _, fuel, _, _, hFuel => by
    have hPos : 1 ≤ fuel := Nat.le_trans (minCoreFuel_pos _) hFuel
    obtain ⟨fuel', rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
    simp only [evalTerm, HIR.eraseFromCore, HIR.eval]
    exact ValDenotesU64.raw w

  | .global name, _, _, _, fuel, hErase, _, hFuel => by
    simp only [minCoreFuel] at hFuel
    obtain ⟨fuel', rfl⟩ : ∃ k, fuel = k + 2 := ⟨fuel - 2, by omega⟩
    simp only [ErasableCore, Bool.or_eq_true, strEq, decide_eq_true_eq] at hErase
    rcases hErase with rfl | rfl
    · simp only [evalTerm, abiGlobalEnv, GlobalEnv.lookup?, List.find?, strEq,
                 HIR.eraseFromCore, HIR.eval]
      exact ValDenotesU64.glued "arg0" [] p₀
    · have hNe : decide ("arg0" = "arg1") = false := by decide
      simp only [evalTerm, abiGlobalEnv, GlobalEnv.lookup?, List.find?, strEq, hNe,
                 HIR.eraseFromCore, HIR.eval]
      exact ValDenotesU64.glued "arg1" [] p₁

  | .u64BinOp op l r, _, _, _, fuel, hErase, hEnv, hFuel => by
    simp only [minCoreFuel] at hFuel
    obtain ⟨fuel', rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
    have hMax : Nat.max (Nat.max (minCoreFuel l) (minCoreFuel r)) 3 ≤ fuel' := by omega
    have h3 : 3 ≤ fuel' := Nat.le_trans (Nat.le_max_right _ _) hMax
    have hLR : Nat.max (minCoreFuel l) (minCoreFuel r) ≤ fuel' := Nat.le_trans (Nat.le_max_left _ _) hMax
    have hlF : minCoreFuel l ≤ fuel' := Nat.le_trans (Nat.le_max_left _ _) hLR
    have hrF : minCoreFuel r ≤ fuel' := Nat.le_trans (Nat.le_max_right _ _) hLR
    simp only [ErasableCore, Bool.and_eq_true] at hErase
    have ihl := evalTerm_erasure_sound T p₀ p₁ l hErase.1 hEnv hlF
    have ihr := evalTerm_erasure_sound T p₀ p₁ r hErase.2 hEnv hrF
    simp only [evalTerm, HIR.eraseFromCore, HIR.eval]
    exact evalU64BinOp_denotes (abiGlobalEnv T p₀ p₁) op ihl ihr h3

  | .u64IfZero c z nz, _, _, _, fuel, hErase, hEnv, hFuel => by
    simp only [minCoreFuel] at hFuel
    obtain ⟨fuel', rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
    have hMax : Nat.max (minCoreFuel c) (Nat.max (minCoreFuel z) (minCoreFuel nz)) ≤ fuel' := by omega
    have hcF : minCoreFuel c ≤ fuel' := Nat.le_trans (Nat.le_max_left _ _) hMax
    have hznz : Nat.max (minCoreFuel z) (minCoreFuel nz) ≤ fuel' := Nat.le_trans (Nat.le_max_right _ _) hMax
    have hzF : minCoreFuel z ≤ fuel' := Nat.le_trans (Nat.le_max_left _ _) hznz
    have hnzF : minCoreFuel nz ≤ fuel' := Nat.le_trans (Nat.le_max_right _ _) hznz
    simp only [ErasableCore, Bool.and_eq_true] at hErase
    rcases hErase with ⟨⟨hcE, hzE⟩, hnzE⟩
    have hcDen := evalTerm_erasure_sound T p₀ p₁ c hcE hEnv hcF
    have hzDen := evalTerm_erasure_sound T p₀ p₁ z hzE hEnv hzF
    have hnzDen := evalTerm_erasure_sound T p₀ p₁ nz hnzE hEnv hnzF
    simp only [evalTerm, HIR.eraseFromCore, HIR.eval, hcDen.force_eq]
    split
    · exact hzDen
    · exact hnzDen

  | .u64Repeat iters init step, _, _, _, fuel, hErase, hEnv, hFuel => by
    simp only [minCoreFuel] at hFuel
    obtain ⟨fuel', rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
    have hMax : Nat.max (minCoreFuel init) (minCoreFuel step) ≤ fuel' := by omega
    have hiF : minCoreFuel init ≤ fuel' := Nat.le_trans (Nat.le_max_left _ _) hMax
    have hsF : minCoreFuel step ≤ fuel' := Nat.le_trans (Nat.le_max_right _ _) hMax
    simp only [ErasableCore, Bool.and_eq_true] at hErase
    have hiDen := evalTerm_erasure_sound T p₀ p₁ init hErase.1 hEnv hiF
    simp only [evalTerm, HIR.eraseFromCore, HIR.eval]
    exact iterN_erasure_sound iters.toNat
      (fun hv => evalTerm_erasure_sound T p₀ p₁ step hErase.2 (.cons_live hv hEnv) hsF)
      hiDen

  | .letIn _ _ val body, _, _, _, fuel, hErase, hEnv, hFuel => by
    simp only [minCoreFuel] at hFuel
    obtain ⟨fuel', rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
    have hMax : Nat.max (minCoreFuel val) (minCoreFuel body) ≤ fuel' := by omega
    have hvF : minCoreFuel val ≤ fuel' := Nat.le_trans (Nat.le_max_left _ _) hMax
    have hbF : minCoreFuel body ≤ fuel' := Nat.le_trans (Nat.le_max_right _ _) hMax
    simp only [ErasableCore, Bool.or_eq_true, Bool.and_eq_true] at hErase
    simp only [evalTerm, HIR.eraseFromCore, HIR.eval]
    rcases hErase with ⟨hvE, hbLive⟩ | hbGhost
    · have hvDen := evalTerm_erasure_sound T p₀ p₁ val hvE hEnv hvF
      exact evalTerm_erasure_sound T p₀ p₁ body hbLive (.cons_live hvDen hEnv) hbF
    · exact evalTerm_erasure_sound T p₀ p₁ body hbGhost (.cons_ghost _ _ hEnv) hbF

  | .key cell sub, _, _, _, fuel, hErase, hEnv, hFuel => by
    simp only [minCoreFuel] at hFuel
    obtain ⟨fuel', rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
    have hsF : minCoreFuel sub ≤ fuel' := by omega
    simp only [ErasableCore] at hErase
    have hsDen := evalTerm_erasure_sound T p₀ p₁ sub hErase hEnv hsF
    simp only [evalTerm, HIR.eraseFromCore]
    exact ValDenotesU64.actKey_preserves T cell hsDen

  | .mvar _, _, _, _, _, hErase, _, _
  | .uu _, _, _, _, _, hErase, _, _
  | .uuExt _, _, _, _, _, hErase, _, _
  | .pi _ _ _ _, _, _, _, _, hErase, _, _
  | .lam _ _ _, _, _, _, _, hErase, _, _
  | .app _ _ _, _, _, _, _, hErase, _, _
  | .modalBox _ _, _, _, _, _, hErase, _, _
  | .boxIntro _ _, _, _, _, _, hErase, _, _
  | .letBox _ _ _ _ _, _, _, _, _, hErase, _, _
  | .recordTy _, _, _, _, _, hErase, _, _
  | .tuple _, _, _, _, _, hErase, _, _
  | .proj _ _, _, _, _, _, hErase, _, _
  | .dataTy _ _, _, _, _, _, hErase, _, _
  | .ctor _ _ _, _, _, _, _, hErase, _, _
  | .pctor _ _ _, _, _, _, _, hErase, _, _
  | .matchData _ _ _ _, _, _, _, _, hErase, _, _
  | .elimHIT _ _ _ _ _, _, _, _, _, hErase, _, _
  | .obsEq _ _ _, _, _, _, _, hErase, _, _
  | .obsHet _ _ _, _, _, _, _, hErase, _, _
  | .refl _ _, _, _, _, _, hErase, _, _
  | .sym _ _, _, _, _, _, hErase, _, _
  | .trans _ _ _, _, _, _, _, hErase, _, _
  | .ap _ _ _, _, _, _, _, hErase, _, _
  | .gel _ _ _, _, _, _, _, hErase, _, _
  | .gelIntro _ _ _, _, _, _, _, hErase, _, _
  | .ungel _ _, _, _, _, _, hErase, _, _
  | .arrowLine _ _ _ _, _, _, _, _, hErase, _, _
  | .piLine _ _ _ _ _ _ _, _, _, _, _, hErase, _, _
  | .prodLine _ _ _ _ _, _, _, _, _, hErase, _, _
  | .sigLine _ _ _ _ _ _ _ _ _, _, _, _, _, hErase, _, _
  | .boxLine _ _ _, _, _, _, _, hErase, _, _
  | .trr _ _ _, _, _, _, _, hErase, _, _
  | .trl _ _ _, _, _, _, _, hErase, _, _
  | .liftr _ _ _, _, _, _, _, hErase, _, _
  | .liftl _ _ _, _, _, _, _, hErase, _, _
  | .pathJ _ _ _ _ _ _ _, _, _, _, _, hErase, _, _
  | .funext _ _ _, _, _, _, _, hErase, _, _
  | .hap _ _ _ _ _, _, _, _, _, hErase, _, _
  | .u64Ty, _, _, _, _, hErase, _, _ => by
    simp [ErasableCore] at hErase

/-- **Top-to-Bottom Verified Compiler Theorem (`core_nbe_to_arm64_correct`, `0 sorry`)**:
    For EVERY higher-dimensional Narya `Core.Term` `tm` with `ErasableCore [] tm = true`
    (supporting HoTT/univalence/modal proof `let`-bindings, 2-cell `.key` coercions, 64-bit
    arithmetic, conditionals, and counted loops) and `minCoreFuel tm ≤ fuel`:
    Narya's Glued NbE evaluator (`evalTerm`) produces the **exact same 64-bit word** as
    erasing proofs (`HIR.eraseFromCore`), optimizing (`HIR.opt`), lowering (`MIR` → `LIR`),
    and executing the emitted `AArch64` machine code (`Arm64.compileFullPipeline`)! -/
theorem core_nbe_to_arm64_correct (T : ModeTheory) (arg0 arg1 : UInt64)
    {tm : Term} {fuel : Nat}
    (hErase : ErasableCore [] tm = true)
    (hFuel : minCoreFuel tm ≤ fuel) :
    (evalTerm fuel (abiGlobalEnv T arg0 arg1) [] tm).force =
      .u64Lit ((Arm64.exec (Arm64.compileFullPipeline (HIR.eraseFromCore tm))
                           (Arm64State.initABI arg0 arg1)).x0) := by
  have hDen := evalTerm_erasure_sound T arg0 arg1 tm hErase EnvMatches.nil hFuel
  rw [hDen.force_eq, Arm64.compileFullPipeline_correct]

end Narya.Compiler
