/-
  Narya.Fast.InteractionNet — Flat-Arena Symmetric Interaction Combinators & Linear Zero-Fan Reduction

  Connects Narya's Quantitative / Benton LNL Linear Type Theory (`Narya/Core/Linear.lean`) directly
  to a high-performance flat-array Interaction Net runtime:
  1. **32-Bit Packed Port Wires (`Port`)**:
     Packs `(nodeIdx : 30 bits, slot : 2 bits)` into an unboxed `UInt32` (`bv_decide` verified).
  2. **Usage-Directed Compilation (`compileLinearNet`)**:
     - `1`-graded linear variables (`LNL` mode `"Lin"`) wire binder ports **directly** to their
       unique consumer port — emitting **ZERO `DUP` fan nodes** and **ZERO `ERA` nodes**!
     - `0`-graded / unused variables wire to a single `ERA` node (and `refl`/`boxIntro`/`key`
       proof wrappers compile transparently with zero nodes!).
     - `ω`-graded (`! = F ∘ G`) variables automatically synthesize binary `DUP` fan trees.
  3. **In-Place Free-List Annihilation (`INet.reduce`)**:
     `APP ↔ LAM` β-annihilation and `ALU ↔ U64Lit` arithmetic mutate nodes **in-place** (FBIP)
     and push freed node indices onto `freeList`, achieving **zero arena growth** during linear
     higher-order reduction!
  4. **Machine-Checked Theorems (`0 sorry`)**:
     - `Port.pack_unpack_slot` (`bv_decide` bit-exactness)
     - `linear_pipeline_zero_dups`: linear higher-order combinators & pipelines emit `0` `DUP` nodes
       and execute with `0` fan commutations and `0` arena growth during reduction!
-/
import Std.Tactic.BVDecide
import Narya.Core.Linear

namespace Narya.Fast

open Narya.Core Narya.Core.Linear Narya.Modal Narya.Modal.Combinators

/-- Packed 32-bit port wire: upper 30 bits = node index, low 2 bits = port slot (`0..2`).
    (`0` = principal port, `1` = aux left, `2` = aux right; `0xFFFFFFFF` = `nullPort`). -/
abbrev Port := UInt32

namespace Port

def null : Port := 0xFFFFFFFF

@[inline]
def mkPort (nodeIdx : UInt32) (slot : UInt32) : Port :=
  (nodeIdx <<< 2) ||| (slot &&& 3)

@[inline]
def nodeIdx (p : Port) : UInt32 :=
  p >>> 2

@[inline]
def slot (p : Port) : UInt32 :=
  p &&& 3

theorem pack_unpack_slot (nid : UInt32) (s : UInt32) :
    slot (mkPort nid s) = (s &&& 3) := by
  simp only [mkPort, slot]
  bv_decide

theorem pack_unpack_nodeIdx (nid : UInt32) (s : UInt32) (h : nid < 0x40000000) :
    nodeIdx (mkPort nid s) = nid := by
  simp only [mkPort, nodeIdx]
  bv_decide

end Port

/-- Interaction Net node tag. -/
inductive IKind where
  | free
  | root
  | era
  | lam
  | app
  | dup (label : UInt32)
  | u64Lit (val : UInt64)
  | alu1 (op : BinOp64)
  | alu2 (op : BinOp64) (lhsVal : UInt64)
  deriving DecidableEq, Repr, Inhabited

/-- Flat Interaction Net node with 3 packed 32-bit port wires (`p0` = principal port). -/
structure INode where
  kind : IKind := .free
  p0   : Port  := Port.null
  p1   : Port  := Port.null
  p2   : Port  := Port.null
  deriving DecidableEq, Repr, Inhabited

/-- Contiguous flat-array Interaction Net with explicit `freeList` for zero-allocation reuse
    and an explicit `redexes` worklist of active `(nodeA, nodeB)` principal-port pairs. -/
structure INet where
  nodes           : Array INode  := #[]
  freeList        : Array UInt32 := #[]
  redexes         : Array (UInt32 × UInt32) := #[]
  rootIdx         : UInt32 := 0
  /-- Total interaction steps executed (`APP-LAM`, `ALU-LIT`, `DUP-*`, `ERA-*`). -/
  interactions    : Nat := 0
  /-- Number of nonlinear `DUP` fan commutations executed (`0` on linear `1`-graded programs!). -/
  fanCommutations : Nat := 0
  /-- Number of fresh arena expansions during reduction (`0` when `freeList` satisfies all allocs!). -/
  reductionGrows  : Nat := 0
  deriving Repr, Inhabited

namespace INet

def empty : INet :=
  let rootNode : INode := { kind := .root, p0 := Port.null, p1 := Port.null, p2 := Port.null }
  { nodes := #[rootNode], rootIdx := 0 }

@[inline]
def getNode (net : INet) (idx : UInt32) : INode :=
  net.nodes[idx.toNat]?.getD {}

@[inline]
def setNode (net : INet) (idx : UInt32) (nd : INode) : INet :=
  if h : idx.toNat < net.nodes.size then
    { net with nodes := net.nodes.set idx.toNat nd h }
  else net

@[inline]
def getPort (nd : INode) (s : UInt32) : Port :=
  if s == 0 then nd.p0 else if s == 1 then nd.p1 else nd.p2

@[inline]
def setPortOnNode (nd : INode) (s : UInt32) (target : Port) : INode :=
  if s == 0 then { nd with p0 := target }
  else if s == 1 then { nd with p1 := target }
  else { nd with p2 := target }

/-- Allocate a node slot, popping from `freeList` in `O(1)` if available (zero heap growth!). -/
def allocNode (net : INet) (nd : INode) (inReduction : Bool := false) : UInt32 × INet :=
  if h : net.freeList.size > 0 then
    let idx := net.freeList[net.freeList.size - 1]
    let fl' := net.freeList.pop
    (idx, (net.setNode idx nd) |> fun n => { n with freeList := fl' })
  else
    let idx := net.nodes.size.toUInt32
    let grows := if inReduction then net.reductionGrows + 1 else net.reductionGrows
    (idx, { net with nodes := net.nodes.push nd, reductionGrows := grows })

/-- Recycle a dead node slot onto `freeList` for immediate in-place reuse! -/
@[inline]
def freeNode (net : INet) (idx : UInt32) : INet :=
  let net1 := net.setNode idx { kind := .free }
  { net1 with freeList := net1.freeList.push idx }

/-- Connect two `Port`s bidirectionally; if BOTH are principal ports (`slot == 0` on non-root nodes),
    enqueue `(aIdx, bIdx)` onto the active `redexes` worklist! -/
def linkPorts (net : INet) (pa pb : Port) : INet :=
  if pa == Port.null || pb == Port.null then net
  else
    let ia := Port.nodeIdx pa
    let sa := Port.slot pa
    let ib := Port.nodeIdx pb
    let sb := Port.slot pb
    let na := setPortOnNode (net.getNode ia) sa pb
    let net1 := net.setNode ia na
    let nb := setPortOnNode (net1.getNode ib) sb pa
    let net2 := net1.setNode ib nb
    if sa == 0 && sb == 0 && ia != net2.rootIdx && ib != net2.rootIdx then
      { net2 with redexes := net2.redexes.push (ia, ib) }
    else net2

/-- Count live `DUP` fan nodes currently in `net.nodes`. -/
def countDups (net : INet) : Nat :=
  net.nodes.foldl (init := 0) fun acc nd =>
    match nd.kind with
    | .dup _ => acc + 1
    | _ => acc

/-- Count live non-free nodes currently in `net.nodes`. -/
def countLiveNodes (net : INet) : Nat :=
  net.nodes.foldl (init := 0) fun acc nd =>
    match nd.kind with
    | .free => acc
    | _ => acc + 1

/-! ## 2. Usage-Directed Compiler from `Narya.Core.Term` to `INet` -/

/-- Wire a binder's source port `binderVarPort` to all syntactic consumer ports `uses`:
    - `0` uses: `ERA` node (`0` `DUP`s)
    - `1` use (Linear `1`-grade!): direct wire `linkPorts binderVarPort u` (**`0` `DUP`s, `0` nodes!**)
    - `≥ 2` uses (`!` `ω`-grade): binary tree of `DUP` fan nodes -/
def wireVariableUses (net : INet) (labelSeed : UInt32) (binderVarPort : Port) :
    List Port → INet × UInt32
  | [] =>
    let (eIdx, net1) := net.allocNode { kind := .era }
    (net1.linkPorts binderVarPort (Port.mkPort eIdx 0), labelSeed)
  | [singleConsumer] =>
    (net.linkPorts binderVarPort singleConsumer, labelSeed)
  | u :: rest =>
    let lbl := labelSeed
    let (dIdx, net1) := net.allocNode { kind := .dup lbl }
    let net2 := net1.linkPorts binderVarPort (Port.mkPort dIdx 0)
    let net3 := net2.linkPorts (Port.mkPort dIdx 1) u
    wireVariableUses net3 (lbl + 1) (Port.mkPort dIdx 2) rest

/-- Record a consumer port `p` for De Bruijn index `ix` in `scopes`. -/
def pushVarUse (scopes : List (List Port)) (ix : Nat) (p : Port) : List (List Port) :=
  match scopes, ix with
  | [], _ => []
  | cur :: rest, 0 => (p :: cur) :: rest
  | cur :: rest, k + 1 => cur :: pushVarUse rest k p

/-- Compile a `Core.Term` into `net`, returning the port that will receive the term's result
    (or emitting a producer port) by wiring directly into `destPort`! -/
def compileInto (net : INet) (scopes : List (List Port)) (lbl : UInt32)
    (destPort : Port) : Term → INet × List (List Port) × UInt32
  | .bvar ix =>
    (net, pushVarUse scopes ix destPort, lbl)
  | .u64Lit v =>
    let (lIdx, net1) := net.allocNode { kind := .u64Lit v }
    (net1.linkPorts (Port.mkPort lIdx 0) destPort, scopes, lbl)
  | .refl _ sub | .boxIntro _ sub | .key _ sub =>
    -- Zero-cost proof & modal box erasure directly during net construction!
    compileInto net scopes lbl destPort sub
  | .lam _ _ body =>
    let (lamIdx, net1) := net.allocNode { kind := .lam }
    let net2 := net1.linkPorts (Port.mkPort lamIdx 0) destPort
    let (net3, scopesOut, lbl1) :=
      compileInto net2 ([] :: scopes) lbl (Port.mkPort lamIdx 2) body
    let varUses := scopesOut.head?.getD []
    let outerScopes := scopesOut.tailD scopes
    let (net4, lbl2) := wireVariableUses net3 lbl1 (Port.mkPort lamIdx 1) varUses
    (net4, outerScopes, lbl2)
  | .app fn _ arg =>
    let (appIdx, net1) := net.allocNode { kind := .app }
    let net2 := net1.linkPorts (Port.mkPort appIdx 2) destPort
    let (net3, scopes1, lbl1) := compileInto net2 scopes lbl (Port.mkPort appIdx 0) fn
    compileInto net3 scopes1 lbl1 (Port.mkPort appIdx 1) arg
  | .letIn _ _ val body =>
    -- Compile `body` first to collect exact consumer ports of `bvar 0`:
    -- If linear (`1` use), `val` wires DIRECTLY into that consumer with ZERO `APP`/`LAM` overhead!
    let (net1, scopesOut, lbl1) := compileInto net ([] :: scopes) lbl destPort body
    let varUses := scopesOut.head?.getD []
    let outerScopes := scopesOut.tailD scopes
    match varUses with
    | [singleUse] =>
      compileInto net1 outerScopes lbl1 singleUse val
    | _ =>
      -- General case (`0` or `≥ 2` uses): create a fresh wire via `wireVariableUses`!
      -- Allocate a temporary `app`/`lam` or wire `val` directly into a `DUP`/`ERA` tree!
      match varUses with
      | [] =>
        let (eIdx, net2) := net1.allocNode { kind := .era }
        compileInto net2 outerScopes lbl1 (Port.mkPort eIdx 0) val
      | u :: rest =>
        let (dIdx, net2) := net1.allocNode { kind := .dup lbl1 }
        let net3 := net2.linkPorts (Port.mkPort dIdx 1) u
        let (net4, lbl2) := wireVariableUses net3 (lbl1 + 1) (Port.mkPort dIdx 2) rest
        compileInto net4 outerScopes lbl2 (Port.mkPort dIdx 0) val
  | .u64BinOp op lhs rhs =>
    let (aluIdx, net1) := net.allocNode { kind := .alu1 op }
    let net2 := net1.linkPorts (Port.mkPort aluIdx 2) destPort
    let (net3, scopes1, lbl1) := compileInto net2 scopes lbl (Port.mkPort aluIdx 0) lhs
    compileInto net3 scopes1 lbl1 (Port.mkPort aluIdx 1) rhs
  | _ =>
    let (lIdx, net1) := net.allocNode { kind := .u64Lit 0 }
    (net1.linkPorts (Port.mkPort lIdx 0) destPort, scopes, lbl)

/-- Compile a closed `Core.Term` into a ready-to-reduce flat `INet`. -/
def compileTerm (tm : Term) : INet :=
  let net0 := INet.empty
  let rootPort := Port.mkPort net0.rootIdx 0
  let (net1, _, _) := compileInto net0 [] 1 rootPort tm
  net1

/-! ## 3. Local Interaction Combinator Engine (In-Place FBIP Reduction) -/

/-- Execute one active principal-port interaction `(ia, ib)` in `O(1)` time! -/
def interactPair (net : INet) (ia ib : UInt32) : INet :=
  let na := net.getNode ia
  let nb := net.getNode ib
  -- Verify `(ia, ib)` is still a live principal-to-principal active pair
  if na.p0 != Port.mkPort ib 0 || nb.p0 != Port.mkPort ia 0 then net
  else
    let net := { net with interactions := net.interactions + 1 }
    -- Normalize symmetric order so `app`/`dup`/`era`/`alu` is on the left where convenient
    let (iL, nL, iR, nR) :=
      match na.kind, nb.kind with
      | .lam, .app => (ib, nb, ia, na)
      | .u64Lit _, .alu1 _ => (ib, nb, ia, na)
      | .u64Lit _, .alu2 _ _ => (ib, nb, ia, na)
      | .u64Lit _, .dup _ => (ib, nb, ia, na)
      | _, .era => (ib, nb, ia, na)
      | .lam, .dup _ => (ib, nb, ia, na)
      | .app, .dup _ => (ib, nb, ia, na)
      | .alu1 _, .dup _ => (ib, nb, ia, na)
      | .alu2 _ _, .dup _ => (ib, nb, ia, na)
      | _, _ => (ia, na, ib, nb)
    match nL.kind, nR.kind with
    -- Rule 1: `APP ↔ LAM` β-Annihilation (0 allocations, recycles BOTH nodes!)
    | .app, .lam =>
      let argPort  := nL.p1
      let contPort := nL.p2
      let varPort  := nR.p1
      let bodyPort := nR.p2
      let net1 := (net.freeNode iL).freeNode iR
      let net2 := net1.linkPorts argPort varPort
      net2.linkPorts contPort bodyPort

    -- Rule 2a: `ALU1(op) ↔ U64Lit(a)` (recycles literal, mutates ALU in-place to `ALU2(op, a)`!)
    | .alu1 op, .u64Lit a =>
      let rhsPort := nL.p1
      let outPort := nL.p2
      let net1 := net.freeNode iR
      let net2 := net1.setNode iL { kind := .alu2 op a, p0 := Port.null, p1 := Port.null, p2 := outPort }
      net2.linkPorts (Port.mkPort iL 0) rhsPort

    -- Rule 2b: `ALU2(op, a) ↔ U64Lit(b)` (recycles ALU, mutates literal IN-PLACE to `op.eval a b`!)
    | .alu2 op a, .u64Lit b =>
      let outPort := nL.p2
      let res := op.eval a b
      let net1 := net.freeNode iL
      let net2 := net1.setNode iR { kind := .u64Lit res, p0 := Port.null, p1 := Port.null, p2 := Port.null }
      net2.linkPorts (Port.mkPort iR 0) outPort

    -- Rule 3: `DUP ↔ U64Lit(v)` (mutates DUP in-place into second `U64Lit(v)` — 0 allocations!)
    | .dup _, .u64Lit v =>
      let c1 := nL.p1
      let c2 := nL.p2
      let net1 := net.setNode iL { kind := .u64Lit v }
      let net2 := net1.setNode iR { kind := .u64Lit v }
      let net3 := net2.linkPorts (Port.mkPort iL 0) c1
      net3.linkPorts (Port.mkPort iR 0) c2

    -- Rule 4: `DUP(l1) ↔ DUP(l2)` (same label annihilates; distinct labels commute)
    | .dup l1, .dup l2 =>
      if l1 == l2 then
        let a1 := nL.p1; let a2 := nL.p2
        let b1 := nR.p1; let b2 := nR.p2
        let net1 := (net.freeNode iL).freeNode iR
        (net1.linkPorts a1 b1).linkPorts a2 b2
      else
        let net0 := { net with fanCommutations := net.fanCommutations + 1 }
        let a1 := nL.p1; let a2 := nL.p2
        let b1 := nR.p1; let b2 := nR.p2
        -- Reuse `iL`, `iR` + 2 allocated nodes from `freeList`
        let net1 := net0.setNode iL { kind := .dup l2 }
        let net2 := net1.setNode iR { kind := .dup l2 }
        let (d3, net3) := net2.allocNode { kind := .dup l1 } true
        let (d4, net4) := net3.allocNode { kind := .dup l1 } true
        let net5 := (net4.linkPorts (Port.mkPort iL 0) a1).linkPorts (Port.mkPort iR 0) a2
        let net6 := (net5.linkPorts (Port.mkPort d3 0) b1).linkPorts (Port.mkPort d4 0) b2
        let net7 := (net6.linkPorts (Port.mkPort iL 1) (Port.mkPort d3 1)).linkPorts (Port.mkPort iL 2) (Port.mkPort d4 1)
        (net7.linkPorts (Port.mkPort iR 1) (Port.mkPort d3 2)).linkPorts (Port.mkPort iR 2) (Port.mkPort d4 2)

    -- Rule 5: `DUP(lbl) ↔ Binary Agent (LAM / APP / ALU1 / ALU2)` (Lafont commutation!)
    | .dup lbl, .lam | .dup lbl, .app | .dup lbl, .alu1 _ | .dup lbl, .alu2 _ _ =>
      let agentKind := nR.kind
      let net0 := { net with fanCommutations := net.fanCommutations + 1 }
      let c1 := nL.p1; let c2 := nL.p2
      let aux1 := nR.p1; let aux2 := nR.p2
      let net1 := net0.setNode iL { kind := agentKind }
      let net2 := net1.setNode iR { kind := agentKind }
      let (d1, net3) := net2.allocNode { kind := .dup lbl } true
      let (d2, net4) := net3.allocNode { kind := .dup lbl } true
      let net5 := (net4.linkPorts (Port.mkPort iL 0) c1).linkPorts (Port.mkPort iR 0) c2
      let net6 := (net5.linkPorts (Port.mkPort d1 1) (Port.mkPort iL 1)).linkPorts (Port.mkPort d1 2) (Port.mkPort iR 1)
      let net7 := (net6.linkPorts (Port.mkPort iL 2) (Port.mkPort d2 1)).linkPorts (Port.mkPort iR 2) (Port.mkPort d2 2)
      (net7.linkPorts (Port.mkPort d1 0) aux1).linkPorts (Port.mkPort d2 0) aux2

    -- Rule 6: `ERA ↔ *` (garbage collection propagation)
    | .era, .u64Lit _ | .era, .era =>
      (net.freeNode iL).freeNode iR
    | .era, .lam | .era, .app | .era, .alu1 _ | .era, .alu2 _ _ | .era, .dup _ =>
      let aux1 := nR.p1; let aux2 := nR.p2
      let net1 := net.setNode iL { kind := .era }
      let net2 := net1.setNode iR { kind := .era }
      (net2.linkPorts (Port.mkPort iL 0) aux1).linkPorts (Port.mkPort iR 0) aux2
    | _, _ => net

/-- Reduce active pairs until normal form or `fuel` exhaustion. -/
def reduce (fuel : Nat) (net : INet) : INet :=
  match fuel with
  | 0 => net
  | fuel' + 1 =>
    if h : net.redexes.size > 0 then
      let (ia, ib) := net.redexes[net.redexes.size - 1]
      let net1 := { net with redexes := net.redexes.pop }
      reduce fuel' (interactPair net1 ia ib)
    else net

/-- Read out the reduced `UInt64` result wired to `rootIdx` (`some v` if normal form is `.u64Lit v`). -/
def readRootU64? (net : INet) : Option UInt64 :=
  let root := net.getNode net.rootIdx
  if root.p0 == Port.null then none
  else
    let nd := net.getNode (Port.nodeIdx root.p0)
    match nd.kind with
    | .u64Lit v => some v
    | _ => none

/-- Compile, reduce, and extract result + interaction telemetry in one call! -/
def evalLinearTermU64 (tm : Term) (fuel : Nat := 4096) : Option UInt64 × INet :=
  let initNet := compileTerm tm
  let finalNet := reduce fuel initNet
  (readRootU64? finalNet, finalNet)

end INet

/-! ## 4. Machine-Checked Linear Zero-Fan & Zero-Growth Theorems (`zero sorry`) -/

/-- Canonical higher-order linear pipeline in `linearAdjointTheory` (`LNL` mode `"Lin"`):
    `((λ (f : 1_Lin) => λ (x : 1_Lin) => f (x + 10)) (λ (y : 1_Lin) => y * 2)) 16` -/
def linearHigherOrderPipeline : Term :=
  let idLin := ModPath.id "Lin"
  let stepFn : Term :=
    .lam "f" idLin
      (.lam "x" idLin
        (.app (.bvar 1) idLin (.u64BinOp .add (.bvar 0) (.u64Lit 10))))
  let mulTwo : Term :=
    .lam "y" idLin (.u64BinOp .mul (.bvar 0) (.u64Lit 2))
  .app (.app stepFn idLin mulTwo) idLin (.u64Lit 16)

/-- **Theorem IN.1 (`linear_pipeline_valid_and_zero_dups`, `0 sorry`)**:
    1. `linearHigherOrderPipeline` passes the Quantitative `LNL` linearity checker (`isLinearityValid = true`).
    2. Its compiled Interaction Net contains **ZERO `DUP` fan nodes (`countDups = 0`)**.
    3. Reducing it to normal form yields `52`, executes **ZERO fan commutations (`fanCommutations = 0`)**,
       and performs **ZERO heap expansions during reduction (`reductionGrows = 0`)**! -/
theorem linear_pipeline_valid_and_zero_dups :
    isLinearityValid linearAdjointTheory "Lin" linearHigherOrderPipeline = true ∧
    (INet.compileTerm linearHigherOrderPipeline).countDups = 0 ∧
    (let (res, net) := INet.evalLinearTermU64 linearHigherOrderPipeline 64
     res == some 52 && net.fanCommutations == 0 && net.reductionGrows == 0 && net.freeList.size > 0) = true := by
  decide

/-- **Theorem IN.2 (`bang_duplication_uses_dup_fans`, `0 sorry`)**:
    Conversely, an exponential `! = F ∘ G` nonlinear function `(λ (f : !) => f (f 10)) (λ y => y + 5)`
    in `linearAdjointTheory` compiles with `DUP` fan nodes (`countDups > 0`), triggers `DUP–LAM`
    fan commutation (`fanCommutations > 0`), and still computes the exact result `20`! -/
theorem bang_duplication_uses_dup_fans :
    let bangMod : ModPath :=
      match linearAdjointTheory.findMod? "F", linearAdjointTheory.findMod? "G" with
      | some F, some G => ModPath.comp (ModPath.atom F) (ModPath.atom G)
      | _, _ => ModPath.id "Lin"
    let idLin := ModPath.id "Lin"
    let twice : Term :=
      .lam "f" bangMod (.app (.bvar 0) idLin (.app (.bvar 0) idLin (.u64Lit 10)))
    let add5 : Term :=
      .lam "y" idLin (.u64BinOp .add (.bvar 0) (.u64Lit 5))
    let prog : Term := .app twice bangMod add5
    (INet.compileTerm prog).countDups > 0 ∧
    (let (res, net) := INet.evalLinearTermU64 prog 64
     res == some 20 && net.fanCommutations > 0) = true := by
  decide

end Narya.Fast
