/-
  Narya.Compiler.MIR — Mid-Level IR with Uniqueness Analysis, Loop Nesting & Join Points

  Stage 2 of Leonardo de Moura's SViL Nov 2026 "New Code Generator" architecture:
    `HIR` ──(`MIR.lowerFromHIR` with static uniqueness / use-count analysis)──▶ `MIR`

  Annotates every binding with its exact static ownership/layout discipline (`dead`,
  `uniqueReg` for linear single-use values, or `sharedStack` for multi-use values),
  tracks nested loop structure (`MIR.hasLoop`) for hardware loop-counter register allocation,
  and lowers control flow to explicit join-point branches and counted loops, with a
  machine-checked semantics preservation theorem (`MIR.eval_lower_eq`, `zero sorry`).
-/
import Narya.Compiler.HIR

namespace Narya.Compiler

/-- Static ownership / allocation discipline inferred during `HIR → MIR` lowering
    (directly modeling the SViL 2026 priorities: stack-allocated objects & uniqueness!). -/
inductive OwnershipKind where
  /-- Zero dynamic uses (can be erased if pure, or dropped immediately). -/
  | dead
  /-- Linear single-use value (`useCount = 1`): kept unboxed in register / reused in-place! -/
  | uniqueReg
  /-- Shared multi-use value (`useCount ≥ 2`): promoted to caller-saved register if `< 4` live, else 16-byte stack slot! -/
  | sharedStack
  deriving DecidableEq, Repr, Inhabited

/-- Mid-Level IR (`MIR`) with ownership-annotated `letAlloc`, `joinIfZero`, and `repeatLoop`. -/
inductive MIR where
  | lit (val : UInt64)
  | param (idx : Fin 2)
  | var (ix : Nat)
  | binOp (op : BinOp64) (lhs rhs : MIR)
  /-- Ownership-annotated local binding (register-promoted when `< 4` live, else stack-allocated, zero GC heap). -/
  | letAlloc (own : OwnershipKind) (val : MIR) (body : MIR)
  /-- Structured conditional join point merging `zeroJoin` and `nonZeroJoin` into target slot. -/
  | joinIfZero (cond : MIR) (zeroJoin : MIR) (nonZeroJoin : MIR)
  /-- Counted loop iterating `stepBody` `count.toNat` times from `init` with accumulator at `.var 0`. -/
  | repeatLoop (count : UInt64) (init : MIR) (stepBody : MIR)
  deriving DecidableEq, Repr, Inhabited

namespace MIR

/-- Check whether an `MIR` expression contains any `repeatLoop` node.
    When `hasLoop stepBody == false`, `LIR`/`Arm64` keeps the hardware loop counter
    entirely in `x8` with zero stack spills inside the loop! -/
def hasLoop : MIR → Bool
  | .lit _ => false
  | .param _ => false
  | .var _ => false
  | .binOp _ l r => hasLoop l || hasLoop r
  | .letAlloc _ v b => hasLoop v || hasLoop b
  | .joinIfZero c z nz => hasLoop c || hasLoop z || hasLoop nz
  | .repeatLoop _ _ _ => true

/-- Count syntactic occurrences of De Bruijn variable `target` in an `HIR` expression
    (taking `Nat.max` across mutually exclusive `ifZero` branches and scaling by `count.toNat` across loops). -/
def countVarUses (target : Nat) : HIR → Nat
  | .lit _ => 0
  | .param _ => 0
  | .var ix => if ix == target then 1 else 0
  | .binOp _ l r => countVarUses target l + countVarUses target r
  | .letBind val body => countVarUses target val + countVarUses (target + 1) body
  | .ifZero c z nz => countVarUses target c + Nat.max (countVarUses target z) (countVarUses target nz)
  | .repeatLoop count init stepBody =>
    countVarUses target init + count.toNat * countVarUses (target + 1) stepBody

/-- Classify ownership discipline from static per-path variable occurrence upper bound. -/
def classifyOwnership (uses : Nat) : OwnershipKind :=
  match uses with
  | 0 => .dead
  | 1 => .uniqueReg
  | _ => .sharedStack

/-- Formal operational semantics of `MIR`. -/
def eval (p₀ p₁ : UInt64) (env : List UInt64) : MIR → UInt64
  | .lit v => v
  | .param i => if i.val == 0 then p₀ else p₁
  | .var ix => env[ix]?.getD 0
  | .binOp op l r => op.eval (eval p₀ p₁ env l) (eval p₀ p₁ env r)
  | .letAlloc _ val body =>
    let v := eval p₀ p₁ env val
    eval p₀ p₁ (v :: env) body
  | .joinIfZero cond zJ nzJ =>
    if eval p₀ p₁ env cond == 0 then eval p₀ p₁ env zJ
    else eval p₀ p₁ env nzJ
  | .repeatLoop count init stepBody =>
    iterN count.toNat (fun acc => eval p₀ p₁ (acc :: env) stepBody) (eval p₀ p₁ env init)

/-- Lower `HIR` to ownership-annotated & join-point `MIR`. -/
def lowerFromHIR : HIR → MIR
  | .lit v => .lit v
  | .param i => .param i
  | .var ix => .var ix
  | .binOp op l r => .binOp op (lowerFromHIR l) (lowerFromHIR r)
  | .letBind val body =>
    let own := classifyOwnership (countVarUses 0 body)
    .letAlloc own (lowerFromHIR val) (lowerFromHIR body)
  | .ifZero c z nz =>
    .joinIfZero (lowerFromHIR c) (lowerFromHIR z) (lowerFromHIR nz)
  | .repeatLoop count init stepBody =>
    .repeatLoop count (lowerFromHIR init) (lowerFromHIR stepBody)

/-- **Theorem D3.2 (`eval_lower_eq`)**: Lowering `HIR` to ownership-annotated `MIR`
    preserves exact 64-bit semantics across all inputs and lexical environments! -/
@[simp]
theorem eval_lower_eq (p₀ p₁ : UInt64) (env : List UInt64) (e : HIR) :
    eval p₀ p₁ env (lowerFromHIR e) = HIR.eval p₀ p₁ env e := by
  induction e generalizing env with
  | lit _ => rfl
  | param _ => rfl
  | var _ => rfl
  | binOp op l r ihl ihr =>
    simp [lowerFromHIR, eval, HIR.eval, ihl, ihr]
  | letBind val body ihv ihb =>
    simp [lowerFromHIR, eval, HIR.eval, ihv, ihb]
  | ifZero c z nz ihc ihz ihnz =>
    simp [lowerFromHIR, eval, HIR.eval, ihc, ihz, ihnz]
  | repeatLoop count init stepBody ihi ihs =>
    simp only [lowerFromHIR, eval, HIR.eval, ihi env]
    exact iterN_congr count.toNat _ _ _ (fun acc => ihs (acc :: env))

end MIR

end Narya.Compiler
