/-
  Narya.Syntax.Modern — Zero-Lisp Extensible Surface Syntax (`.narya`), Pratt/Mixfix Parser,
  Bidirectional `.ny ↔ .narya` Translator, and Machine-Checked Equivalence Proofs (`0 sorry`)

  Inspired by:
  - **Lean 4**: Dynamic parser environment (`SyntaxEnv`) extensible in-file and across `import`s
    via `prefix`, `postfix`, `infixl`, `infixr`, and arbitrary-arity leading/trailing `notation`
    rules with numeric binding powers, plus column-aware layout-sensitive `let` bindings (`0` `;`s).
  - **Idris 2 QTT**: Quantitative rig-graded binders `(0 g : A)` (erased ghost), `(1 x : A)` (linear),
    and `(ω x : A)` / `(omega x : A)` (unrestricted bang promotion `! = F ∘ G`).
  - **Granule & Narya**: Explicit coeffect/modality annotations `(x @[μ] : A)`, modal applications
    `f @[μ] x`, graded modal boxes `□[μ] A` / `Box[μ] A` and `box[μ] e`, and custom observational
    path notations (e.g. `notation 50 a " ≡[" A "] " b => Id A a b`).

  Machine-Checked Guarantees (`0 sorry`, `0 noncomputable`):
  1. `elabModernExpr_eq_elaborateSExp`: Direct elaboration of any well-formed `ModernExpr` produces
     the **exact same `Except String Term`** as legacy `.ny` `elaborateSExp` across all fuel bounds,
     all 2-categorical `ModeTheory`s, all modes, and all binder scopes.
  2. `ofSExp_toSExp_roundtrip`: `ModernExpr.ofSExp fuel e.toSExp = .ok e` for all `fuel ≥ e.depth`.
  3. `infix_desugar_eq_elaborateSExp` & `mixfix_id_desugar_eq_elaborateSExp`: User-defined dynamic
     `infixl`/`infixr` and multi-token `notation` expansions preserve `elaborateSExp` semantics.
-/
import Narya.Syntax.Parser

namespace Narya.Syntax

open Narya.Dim Narya.Modal Narya.Modal.Combinators Narya.Core
open Narya.Core.Safety Narya.Core.Unify Narya.Core.Linear

/-! ## 1. Reserved Keyword Predicates & Well-Formed `ModernExpr` AST -/

/-- Atom-position keywords matched specially by `elaborateSExp` (`elabBuiltinAtom?`). -/
def isAtomKeyword (s : String) : Bool :=
  (elabBuiltinAtom? s).isSome

/-- List-head keywords matched specially by `elaborateSExp` (`isReservedListHead`). -/
abbrev isListKeyword (s : String) : Bool :=
  isReservedListHead s

mutual

/-- Record field declaration in Modern `.narya` syntax (`sig { f : A, g @[L] : B }`). -/
inductive ModernField where
  | plain (name : String) (ty : ModernExpr)
  | modal (name : String) (mod : String) (ty : ModernExpr)
  deriving BEq, Repr

/-- Record tuple assignment in Modern `.narya` syntax (`{ f := u, g := v }`). -/
inductive ModernTupleField where
  | assign (name : String) (val : ModernExpr)
  deriving BEq, Repr

/-- Structured Zero-Lisp `.narya` surface expression AST. -/
inductive ModernExpr where
  | typeU0
  | typeU1
  | typeU (lvlStr : String)
  | typeExt
  | u64Ty
  | zeroNat
  | trueBool
  | falseBool
  | ttUnit
  | natTy
  | boolTy
  | unitTy
  | emptyTy
  | hole0
  | hole (idStr : String)
  | var (ident : String)
  | u64Lit (numStr : String)
  | succNat (n : ModernExpr)
  | pi (x : String) (mod : String) (dom cod : ModernExpr)
  | arrow (dom cod : ModernExpr)
  | lamMod (x : String) (mod : String) (body : ModernExpr)
  | lam (x : String) (body : ModernExpr)
  | letIn (x : String) (ty val body : ModernExpr)
  | appMod (fn : ModernExpr) (mod : String) (arg : ModernExpr)
  | boxTy (mod : String) (ty : ModernExpr)
  | boxIntro (mod : String) (sub : ModernExpr)
  | record (fields : List ModernField)
  | tuple (fields : List ModernTupleField)
  | proj (sub : ModernExpr) (fld : String)
  | funext (x : String) (body : ModernExpr)
  | hap (pf a0 a1 pa : ModernExpr)
  | ifz (cond zBranch nzBranch : ModernExpr)
  | repeatU64 (cntStr : String) (init : ModernExpr) (accVar : String) (step : ModernExpr)
  | obsId (ty : ModernExpr) (ends : List ModernExpr)
  | obsBr (ty : ModernExpr) (ends : List ModernExpr)
  | obsDisp (ty e0 : ModernExpr)
  | obsFresh (ty : ModernExpr)
  | refl (sub : ModernExpr)
  | reflDir (dir : String) (sub : ModernExpr)
  | glue (a b rel : ModernExpr)
  | gel (a b rel : ModernExpr)
  | trr (line x : ModernExpr)
  | trl (line x : ModernExpr)
  | liftr (line x : ModernExpr)
  | liftl (line x : ModernExpr)
  | sym (p : ModernExpr)
  | trans (p q : ModernExpr)
  | arrowLine (d c : ModernExpr)
  | prodLine (fN sN : String) (fL sL : ModernExpr)
  | boxLine (mod : String) (inner : ModernExpr)
  | binOp64 (op : BinOp64) (lhs rhs : ModernExpr)
  | call (fn : ModernExpr) (args : List ModernExpr)
  deriving BEq, Repr

end

instance : Inhabited ModernExpr := ⟨.typeU0⟩

/-- Built-in atom decoder matching `elabBuiltinAtom?`. -/
def ofBuiltinAtom? : String → Option ModernExpr
  | "Type" | "UU" => some .typeU0
  | "Type1" => some .typeU1
  | "Type_ext" | "UU_ext" => some .typeExt
  | "U64" => some .u64Ty
  | "zero" => some .zeroNat
  | "true" => some .trueBool
  | "false" => some .falseBool
  | "tt" => some .ttUnit
  | "Nat" => some .natTy
  | "Bool" => some .boolTy
  | "Unit" => some .unitTy
  | "Empty" => some .emptyTy
  | "?" => some .hole0
  | _ => none

/-- Returns `true` if `e` serializes to `.atom _` in call-head position with a reserved keyword. -/
def ModernExpr.isReservedCallHead : ModernExpr → Bool
  | .typeU0 | .typeU1 | .typeExt | .u64Ty
  | .zeroNat | .trueBool | .falseBool | .ttUnit
  | .natTy | .boolTy | .unitTy | .emptyTy | .hole0 => true
  | .var s => isAtomKeyword s || isListKeyword s
  | _ => false

/-- Flatten curried applications `mkCall (call f xs) y = call f (xs ++ [y])`. -/
def ModernExpr.mkCall (fn arg : ModernExpr) : ModernExpr :=
  match fn with
  | .call head prev => .call head (prev ++ [arg])
  | _ => .call fn [arg]

mutual

def ModernField.toSExp : ModernField → SExp
  | .plain fname fty => .list [.atom fname, fty.toSExp]
  | .modal fname modStr fty => .list [.atom fname, .atom modStr, fty.toSExp]

def ModernTupleField.toSExp : ModernTupleField → SExp
  | .assign fname val => .list [.atom fname, val.toSExp]

def ModernExpr.listToSExp : List ModernExpr → List SExp
  | [] => []
  | e :: es => e.toSExp :: ModernExpr.listToSExp es

def ModernField.listToSExp : List ModernField → List SExp
  | [] => []
  | f :: fs => f.toSExp :: ModernField.listToSExp fs

def ModernTupleField.listToSExp : List ModernTupleField → List SExp
  | [] => []
  | f :: fs => f.toSExp :: ModernTupleField.listToSExp fs

/-- Canonical serialization of `ModernExpr` to legacy `.ny` `SExp`. -/
def ModernExpr.toSExp : ModernExpr → SExp
  | .typeU0 => .atom "Type"
  | .typeU1 => .atom "Type1"
  | .typeU lvlStr => .list [.atom "Type", .atom lvlStr]
  | .typeExt => .atom "Type_ext"
  | .u64Ty => .atom "U64"
  | .zeroNat => .atom "zero"
  | .trueBool => .atom "true"
  | .falseBool => .atom "false"
  | .ttUnit => .atom "tt"
  | .natTy => .atom "Nat"
  | .boolTy => .atom "Bool"
  | .unitTy => .atom "Unit"
  | .emptyTy => .atom "Empty"
  | .hole0 => .atom "?"
  | .hole idStr => .list [.atom "?", .atom idStr]
  | .var ident => .atom ident
  | .u64Lit numStr => .list [.atom "u64", .atom numStr]
  | .succNat n => .list [.atom "succ", n.toSExp]
  | .pi x mod dom cod => .list [.atom "pi", .atom x, .atom mod, dom.toSExp, cod.toSExp]
  | .arrow dom cod => .list [.atom "arrow", dom.toSExp, cod.toSExp]
  | .lamMod x mod body => .list [.atom "lam", .atom x, .atom mod, body.toSExp]
  | .lam x body => .list [.atom "fun", .atom x, body.toSExp]
  | .letIn x ty val body => .list [.atom "let", .atom x, ty.toSExp, val.toSExp, body.toSExp]
  | .appMod fn mod arg => .list [.atom "app_mod", fn.toSExp, .atom mod, arg.toSExp]
  | .boxTy mod ty => .list [.atom "box", .atom mod, ty.toSExp]
  | .boxIntro mod sub => .list [.atom "box_intro", .atom mod, sub.toSExp]
  | .record fields => .list (.atom "record" :: ModernField.listToSExp fields)
  | .tuple fields => .list (.atom "tuple" :: ModernTupleField.listToSExp fields)
  | .proj sub fld => .list [.atom "proj", sub.toSExp, .atom fld]
  | .funext x body => .list [.atom "funext", .atom x, body.toSExp]
  | .hap pf a0 a1 pa => .list [.atom "hap", pf.toSExp, a0.toSExp, a1.toSExp, pa.toSExp]
  | .ifz c z nz => .list [.atom "u64_ifz", c.toSExp, z.toSExp, nz.toSExp]
  | .repeatU64 cntStr init accVar step =>
    .list [.atom "u64_repeat", .atom cntStr, init.toSExp, .atom accVar, step.toSExp]
  | .obsId ty ends => .list (.atom "Id" :: ty.toSExp :: ModernExpr.listToSExp ends)
  | .obsBr ty ends => .list (.atom "Br" :: ty.toSExp :: ModernExpr.listToSExp ends)
  | .obsDisp ty e0 => .list [.atom "Disp", ty.toSExp, e0.toSExp]
  | .obsFresh ty => .list [.atom "Fresh", ty.toSExp]
  | .refl sub => .list [.atom "refl", sub.toSExp]
  | .reflDir dir sub => .list [.atom "refl_dir", .atom dir, sub.toSExp]
  | .glue a b rel => .list [.atom "Glue", a.toSExp, b.toSExp, rel.toSExp]
  | .gel a b rel => .list [.atom "Gel", a.toSExp, b.toSExp, rel.toSExp]
  | .trr l x => .list [.atom "trr", l.toSExp, x.toSExp]
  | .trl l x => .list [.atom "trl", l.toSExp, x.toSExp]
  | .liftr l x => .list [.atom "liftr", l.toSExp, x.toSExp]
  | .liftl l x => .list [.atom "liftl", l.toSExp, x.toSExp]
  | .sym p => .list [.atom "sym", p.toSExp]
  | .trans p q => .list [.atom "trans", p.toSExp, q.toSExp]
  | .arrowLine d c => .list [.atom "arrow_line", d.toSExp, c.toSExp]
  | .prodLine fN sN fL sL => .list [.atom "prod_line", .atom fN, .atom sN, fL.toSExp, sL.toSExp]
  | .boxLine mod inner => .list [.atom "box_line", .atom mod, inner.toSExp]
  | .binOp64 op l r => .list [.atom op.name, l.toSExp, r.toSExp]
  | .call fn args => .list (fn.toSExp :: ModernExpr.listToSExp args)

end

mutual

def ModernField.wf : ModernField → Bool
  | .plain _ fty => fty.wf
  | .modal _ _ fty => fty.wf

def ModernTupleField.wf : ModernTupleField → Bool
  | .assign _ val => val.wf

def ModernExpr.listWf : List ModernExpr → Bool
  | [] => true
  | e :: es => e.wf && ModernExpr.listWf es

def ModernField.listWf : List ModernField → Bool
  | [] => true
  | f :: fs => f.wf && ModernField.listWf fs

def ModernTupleField.listWf : List ModernTupleField → Bool
  | [] => true
  | f :: fs => f.wf && ModernTupleField.listWf fs

/-- Well-formedness predicate ensuring `.var` and `.call` heads do not collide with reserved keywords. -/
def ModernExpr.wf : ModernExpr → Bool
  | .typeU0 | .typeU1 | .typeU _ | .typeExt | .u64Ty
  | .zeroNat | .trueBool | .falseBool | .ttUnit
  | .natTy | .boolTy | .unitTy | .emptyTy | .hole0 | .hole _ | .u64Lit _ => true
  | .var ident => !isAtomKeyword ident
  | .succNat n => n.wf
  | .pi _ _ dom cod => dom.wf && cod.wf
  | .arrow dom cod => dom.wf && cod.wf
  | .lamMod _ _ body => body.wf
  | .lam _ body => body.wf
  | .letIn _ ty val body => ty.wf && val.wf && body.wf
  | .appMod fn _ arg => fn.wf && arg.wf
  | .boxTy _ ty => ty.wf
  | .boxIntro _ sub => sub.wf
  | .record fields => ModernField.listWf fields
  | .tuple fields => ModernTupleField.listWf fields
  | .proj sub _ => sub.wf
  | .funext _ body => body.wf
  | .hap pf a0 a1 pa => pf.wf && a0.wf && a1.wf && pa.wf
  | .ifz c z nz => c.wf && z.wf && nz.wf
  | .repeatU64 _ init _ step => init.wf && step.wf
  | .obsId ty ends => ty.wf && ModernExpr.listWf ends
  | .obsBr ty ends => ty.wf && ModernExpr.listWf ends
  | .obsDisp ty e0 => ty.wf && e0.wf
  | .obsFresh ty => ty.wf
  | .refl sub => sub.wf
  | .reflDir _ sub => sub.wf
  | .glue a b rel => a.wf && b.wf && rel.wf
  | .gel a b rel => a.wf && b.wf && rel.wf
  | .trr l x => l.wf && x.wf
  | .trl l x => l.wf && x.wf
  | .liftr l x => l.wf && x.wf
  | .liftl l x => l.wf && x.wf
  | .sym p => p.wf
  | .trans p q => p.wf && q.wf
  | .arrowLine d c => d.wf && c.wf
  | .prodLine _ _ fL sL => fL.wf && sL.wf
  | .boxLine _ inner => inner.wf
  | .binOp64 _ l r => l.wf && r.wf
  | .call fn args => (!args.isEmpty) && (!fn.isReservedCallHead) && fn.wf && ModernExpr.listWf args

end

/-! ## 2. Direct `ModernExpr → Term` Elaborator & Reverse `SExp → ModernExpr` Decoder -/

mutual

def elabModernRecordTele (fuel : Nat) (T : ModeTheory) (mode : ModeId) (locals : List String)
    (fields : List ModernField) : Except String (List FieldDecl) :=
  match fuel with
  | 0 => .error "Elaborator out of fuel"
  | fuel' + 1 =>
    match fields with
    | [] => .ok []
    | .modal fname modStr ftyExp :: rest => do
      let mp ← resolveModPath T mode modStr
      let fty ← elabModernExpr fuel' T mp.dom locals ftyExp
      let rest' ← elabModernRecordTele fuel' T mode (fname :: locals) rest
      .ok ((fname, mp, fty) :: rest')
    | .plain fname ftyExp :: rest => do
      let mp := ModPath.id mode
      let fty ← elabModernExpr fuel' T mode locals ftyExp
      let rest' ← elabModernRecordTele fuel' T mode (fname :: locals) rest
      .ok ((fname, mp, fty) :: rest')

def elabModernTupleFields (fuel : Nat) (T : ModeTheory) (mode : ModeId) (locals : List String)
    (fields : List ModernTupleField) : Except String (List (String × Term)) :=
  match fuel with
  | 0 => .error "Elaborator out of fuel"
  | fuel' + 1 =>
    match fields with
    | [] => .ok []
    | .assign fname valExp :: rest => do
      let v ← elabModernExpr fuel' T mode locals valExp
      let rest' ← elabModernTupleFields fuel' T mode locals rest
      .ok ((fname, v) :: rest')

/-- Direct elaborator from `ModernExpr` to Narya Core `Term` (zero S-expressions at runtime!). -/
def elabModernExpr (fuel : Nat) (T : ModeTheory) (mode : ModeId) (locals : List String)
    (expr : ModernExpr) : Except String Term :=
  match fuel with
  | 0 => .error "Elaborator out of fuel"
  | fuel' + 1 =>
    match expr with
    | .typeU0 => .ok (.uu 0)
    | .typeU1 => .ok (.uu 1)
    | .typeExt => .ok (.uuExt 0)
    | .u64Ty => .ok .u64Ty
    | .zeroNat => .ok (.ctor "Nat" "zero" [])
    | .trueBool => .ok (.ctor "Bool" "true" [])
    | .falseBool => .ok (.ctor "Bool" "false" [])
    | .ttUnit => .ok (.ctor "Unit" "tt" [])
    | .natTy => .ok (.dataTy "Nat" [])
    | .boolTy => .ok (.dataTy "Bool" [])
    | .unitTy => .ok (.dataTy "Unit" [])
    | .emptyTy => .ok (.dataTy "Empty" [])
    | .hole0 => .ok (.mvar 0)
    | .var ident =>
      match findLocalIx? locals ident with
      | some ix => .ok (.bvar ix)
      | none => .ok (.global ident)
    | .u64Lit numStr =>
      match numStr.toNat? with
      | some n => .ok (.u64Lit n.toUInt64)
      | none => .error s!"Invalid U64 literal '{numStr}'"
    | .hole idStr =>
      match idStr.toNat? with
      | some id => .ok (.mvar id)
      | none => .error s!"Invalid hole id '{idStr}'"
    | .typeU lvlStr =>
      match lvlStr.toNat? with
      | some l => .ok (.uu l)
      | none => .error s!"Invalid universe level '{lvlStr}'"
    | .succNat nExp => do
      let n ← elabModernExpr fuel' T mode locals nExp
      .ok (.ctor "Nat" "succ" [n])
    | .pi x modStr domExp codExp => do
      let mp ← resolveModPath T mode modStr
      let dom ← elabModernExpr fuel' T mp.dom locals domExp
      let cod ← elabModernExpr fuel' T mode (x :: locals) codExp
      .ok (.pi x mp dom cod)
    | .arrow domExp codExp => do
      let mp := ModPath.id mode
      let dom ← elabModernExpr fuel' T mode locals domExp
      let cod ← elabModernExpr fuel' T mode ("_" :: locals) codExp
      .ok (.pi "_" mp dom cod)
    | .lamMod x modStr bodyExp => do
      let mp ← resolveModPath T mode modStr
      let body ← elabModernExpr fuel' T mode (x :: locals) bodyExp
      .ok (.lam x mp body)
    | .lam x bodyExp => do
      let mp := ModPath.id mode
      let body ← elabModernExpr fuel' T mode (x :: locals) bodyExp
      .ok (.lam x mp body)
    | .letIn x tyExp valExp bodyExp => do
      let ty ← elabModernExpr fuel' T mode locals tyExp
      let val ← elabModernExpr fuel' T mode locals valExp
      let body ← elabModernExpr fuel' T mode (x :: locals) bodyExp
      .ok (.letIn x ty val body)
    | .appMod fnExp modStr argExp => do
      let mp ← resolveModPath T mode modStr
      let fn ← elabModernExpr fuel' T mode locals fnExp
      let arg ← elabModernExpr fuel' T mp.dom locals argExp
      .ok (.app fn mp arg)
    | .boxTy modStr tyExp => do
      let mp ← resolveModPath T mode modStr
      let ty ← elabModernExpr fuel' T mp.dom locals tyExp
      .ok (.modalBox mp ty)
    | .boxIntro modStr subExp => do
      let mp ← resolveModPath T mode modStr
      let sub ← elabModernExpr fuel' T mp.dom locals subExp
      .ok (.boxIntro mp sub)
    | .record fieldExps => do
      let tele ← elabModernRecordTele fuel' T mode locals fieldExps
      .ok (.recordTy tele)
    | .tuple fieldExps => do
      let fs ← elabModernTupleFields fuel' T mode locals fieldExps
      .ok (.tuple fs)
    | .proj subExp fld => do
      let sub ← elabModernExpr fuel' T mode locals subExp
      .ok (.proj sub fld)
    | .funext x bodyExp => do
      let mp := ModPath.id mode
      let locals3 := (x ++ "2") :: (x ++ "1") :: (x ++ "0") :: locals
      let body ← elabModernExpr fuel' T mode locals3 bodyExp
      .ok (.funext Dir.hott mp body)
    | .hap pfExp a0Exp a1Exp paExp => do
      let pf ← elabModernExpr fuel' T mode locals pfExp
      let a0 ← elabModernExpr fuel' T mode locals a0Exp
      let a1 ← elabModernExpr fuel' T mode locals a1Exp
      let pa ← elabModernExpr fuel' T mode locals paExp
      .ok (.hap Dir.hott pf a0 a1 pa)
    | .ifz cExp zExp nzExp => do
      let c ← elabModernExpr fuel' T mode locals cExp
      let z ← elabModernExpr fuel' T mode locals zExp
      let nz ← elabModernExpr fuel' T mode locals nzExp
      .ok (.u64IfZero c z nz)
    | .repeatU64 cntStr initExp accVar stepExp =>
      match cntStr.toNat? with
      | none => .error s!"Invalid u64_repeat count '{cntStr}'"
      | some cnt => do
        let init ← elabModernExpr fuel' T mode locals initExp
        let step ← elabModernExpr fuel' T mode (accVar :: locals) stepExp
        .ok (.u64Repeat cnt.toUInt64 init step)
    | .obsId tyExp endExps => do
      let ty ← elabModernExpr fuel' T mode locals tyExp
      let ends ← endExps.mapM (elabModernExpr fuel' T mode locals)
      .ok (.obsEq Dir.hott ty ends)
    | .obsBr tyExp endExps => do
      let ty ← elabModernExpr fuel' T mode locals tyExp
      let ends ← endExps.mapM (elabModernExpr fuel' T mode locals)
      .ok (.obsEq (Dir.param 2) ty ends)
    | .obsDisp tyExp e0Exp => do
      let ty ← elabModernExpr fuel' T mode locals tyExp
      let e0 ← elabModernExpr fuel' T mode locals e0Exp
      .ok (.obsEq Dir.displayed ty [e0])
    | .obsFresh tyExp => do
      let ty ← elabModernExpr fuel' T mode locals tyExp
      .ok (.obsEq Dir.nominal ty [])
    | .refl subExp => do
      let sub ← elabModernExpr fuel' T mode locals subExp
      .ok (.refl Dir.hott sub)
    | .reflDir gStr subExp => do
      let g ← resolveDir gStr
      let sub ← elabModernExpr fuel' T mode locals subExp
      .ok (.refl g sub)
    | .glue aExp bExp relExp => do
      let a ← elabModernExpr fuel' T mode locals aExp
      let b ← elabModernExpr fuel' T mode locals bExp
      let r ← elabModernExpr fuel' T mode locals relExp
      .ok (.gel Dir.hott [a, b] r)
    | .gel aExp bExp relExp => do
      let a ← elabModernExpr fuel' T mode locals aExp
      let b ← elabModernExpr fuel' T mode locals bExp
      let r ← elabModernExpr fuel' T mode locals relExp
      .ok (.gel (Dir.param 2) [a, b] r)
    | .trr lineExp xExp => do
      let l ← elabModernExpr fuel' T mode locals lineExp
      let x ← elabModernExpr fuel' T mode locals xExp
      .ok (.trr Dir.hott l x)
    | .trl lineExp xExp => do
      let l ← elabModernExpr fuel' T mode locals lineExp
      let x ← elabModernExpr fuel' T mode locals xExp
      .ok (.trl Dir.hott l x)
    | .liftr lineExp xExp => do
      let l ← elabModernExpr fuel' T mode locals lineExp
      let x ← elabModernExpr fuel' T mode locals xExp
      .ok (.liftr Dir.hott l x)
    | .liftl lineExp xExp => do
      let l ← elabModernExpr fuel' T mode locals lineExp
      let x ← elabModernExpr fuel' T mode locals xExp
      .ok (.liftl Dir.hott l x)
    | .sym pExp => do
      let p ← elabModernExpr fuel' T mode locals pExp
      .ok (.sym Dir.hott p)
    | .trans pExp qExp => do
      let p ← elabModernExpr fuel' T mode locals pExp
      let q ← elabModernExpr fuel' T mode locals qExp
      .ok (.trans Dir.hott p q)
    | .arrowLine dExp cExp => do
      let d ← elabModernExpr fuel' T mode locals dExp
      let c ← elabModernExpr fuel' T mode locals cExp
      .ok (.arrowLine Dir.hott (ModPath.id mode) d c)
    | .prodLine fN sN fExp sExp => do
      let f ← elabModernExpr fuel' T mode locals fExp
      let s ← elabModernExpr fuel' T mode locals sExp
      .ok (.prodLine Dir.hott fN sN f s)
    | .boxLine modStr inExp => do
      let mp ← resolveModPath T mode modStr
      let inner ← elabModernExpr fuel' T mp.dom locals inExp
      .ok (.boxLine Dir.hott mp inner)
    | .binOp64 bop lExp rExp => do
      let l ← elabModernExpr fuel' T mode locals lExp
      let r ← elabModernExpr fuel' T mode locals rExp
      .ok (.u64BinOp bop l r)
    | .call fnExp argExps => do
      let fn ← elabModernExpr fuel' T mode locals fnExp
      let args ← argExps.mapM (elabModernExpr fuel' T mode locals)
      let mp := ModPath.id mode
      .ok (args.foldl (fun acc a => .app acc mp a) fn)

end

mutual

def ModernField.ofSExp (fuel : Nat) (fields : List SExp) : Except String (List ModernField) :=
  match fuel with
  | 0 => .error "ofSExp out of fuel"
  | fuel' + 1 =>
    match fields with
    | [] => .ok []
    | .list [.atom fname, .atom modStr, ftyExp] :: rest => do
      let fty ← ModernExpr.ofSExp fuel' ftyExp
      let fs ← ModernField.ofSExp fuel' rest
      .ok (.modal fname modStr fty :: fs)
    | .list [.atom fname, ftyExp] :: rest => do
      let fty ← ModernExpr.ofSExp fuel' ftyExp
      let fs ← ModernField.ofSExp fuel' rest
      .ok (.plain fname fty :: fs)
    | other :: _ => .error s!"Invalid record field SExp: {reprStr other}"

def ModernTupleField.ofSExp (fuel : Nat) (fields : List SExp) :
    Except String (List ModernTupleField) :=
  match fuel with
  | 0 => .error "ofSExp out of fuel"
  | fuel' + 1 =>
    match fields with
    | [] => .ok []
    | .list [.atom fname, valExp] :: rest => do
      let v ← ModernExpr.ofSExp fuel' valExp
      let fs ← ModernTupleField.ofSExp fuel' rest
      .ok (.assign fname v :: fs)
    | other :: _ => .error s!"Invalid tuple field SExp: {reprStr other}"

/-- Decode any legacy `.ny` `SExp` into a structured `ModernExpr`. -/
def ModernExpr.ofSExp (fuel : Nat) (sexp : SExp) : Except String ModernExpr :=
  match fuel with
  | 0 => .error "ofSExp out of fuel"
  | fuel' + 1 =>
    match sexp with
    | .atom ident =>
      match ofBuiltinAtom? ident with
      | some e => .ok e
      | none => .ok (.var ident)
    | .list [] => .error "Empty () expression"
    | .list (.list fnList :: argExps) =>
      if argExps.isEmpty then .error s!"Single-element list form not supported"
      else do
        let fn ← ModernExpr.ofSExp fuel' (.list fnList)
        let args ← argExps.mapM (ModernExpr.ofSExp fuel')
        .ok (.call fn args)
    | .list (.atom head :: argExps) =>
      if !isReservedListHead head then
        if argExps.isEmpty then .error s!"Single-element list form not supported: {head}"
        else do
          let fn ← ModernExpr.ofSExp fuel' (.atom head)
          let args ← argExps.mapM (ModernExpr.ofSExp fuel')
          .ok (.call fn args)
      else
        match head, argExps with
        | "u64", [.atom numStr] => .ok (.u64Lit numStr)
        | "?", [.atom idStr] | "hole", [.atom idStr] => .ok (.hole idStr)
        | "Type", [.atom lvlStr] => .ok (.typeU lvlStr)
        | "succ", [nExp] => do
          let n ← ModernExpr.ofSExp fuel' nExp
          .ok (.succNat n)
        | "pi", [.atom x, .atom modStr, domExp, codExp] => do
          let dom ← ModernExpr.ofSExp fuel' domExp
          let cod ← ModernExpr.ofSExp fuel' codExp
          .ok (.pi x modStr dom cod)
        | "arrow", [domExp, codExp] => do
          let dom ← ModernExpr.ofSExp fuel' domExp
          let cod ← ModernExpr.ofSExp fuel' codExp
          .ok (.arrow dom cod)
        | "lam", [.atom x, .atom modStr, bodyExp] => do
          let body ← ModernExpr.ofSExp fuel' bodyExp
          .ok (.lamMod x modStr body)
        | "fun", [.atom x, bodyExp] => do
          let body ← ModernExpr.ofSExp fuel' bodyExp
          .ok (.lam x body)
        | "let", [.atom x, tyExp, valExp, bodyExp] => do
          let ty ← ModernExpr.ofSExp fuel' tyExp
          let val ← ModernExpr.ofSExp fuel' valExp
          let body ← ModernExpr.ofSExp fuel' bodyExp
          .ok (.letIn x ty val body)
        | "app_mod", [fnExp, .atom modStr, argExp] => do
          let fn ← ModernExpr.ofSExp fuel' fnExp
          let arg ← ModernExpr.ofSExp fuel' argExp
          .ok (.appMod fn modStr arg)
        | "box", [.atom modStr, tyExp] => do
          let ty ← ModernExpr.ofSExp fuel' tyExp
          .ok (.boxTy modStr ty)
        | "box_intro", [.atom modStr, subExp] => do
          let sub ← ModernExpr.ofSExp fuel' subExp
          .ok (.boxIntro modStr sub)
        | "record", fieldExps => do
          let fs ← ModernField.ofSExp fuel' fieldExps
          .ok (.record fs)
        | "tuple", fieldExps => do
          let fs ← ModernTupleField.ofSExp fuel' fieldExps
          .ok (.tuple fs)
        | "proj", [subExp, .atom fld] => do
          let sub ← ModernExpr.ofSExp fuel' subExp
          .ok (.proj sub fld)
        | "funext", [.atom x, bodyExp] => do
          let body ← ModernExpr.ofSExp fuel' bodyExp
          .ok (.funext x body)
        | "hap", [pfExp, a0Exp, a1Exp, paExp] => do
          let pf ← ModernExpr.ofSExp fuel' pfExp
          let a0 ← ModernExpr.ofSExp fuel' a0Exp
          let a1 ← ModernExpr.ofSExp fuel' a1Exp
          let pa ← ModernExpr.ofSExp fuel' paExp
          .ok (.hap pf a0 a1 pa)
        | "u64_ifz", [cExp, zExp, nzExp] => do
          let c ← ModernExpr.ofSExp fuel' cExp
          let z ← ModernExpr.ofSExp fuel' zExp
          let nz ← ModernExpr.ofSExp fuel' nzExp
          .ok (.ifz c z nz)
        | "u64_repeat", [.atom cntStr, initExp, .atom accVar, stepExp] => do
          let init ← ModernExpr.ofSExp fuel' initExp
          let step ← ModernExpr.ofSExp fuel' stepExp
          .ok (.repeatU64 cntStr init accVar step)
        | "Id", tyExp :: endExps => do
          let ty ← ModernExpr.ofSExp fuel' tyExp
          let ends ← endExps.mapM (ModernExpr.ofSExp fuel')
          .ok (.obsId ty ends)
        | "Br", tyExp :: endExps => do
          let ty ← ModernExpr.ofSExp fuel' tyExp
          let ends ← endExps.mapM (ModernExpr.ofSExp fuel')
          .ok (.obsBr ty ends)
        | "Disp", [tyExp, e0Exp] => do
          let ty ← ModernExpr.ofSExp fuel' tyExp
          let e0 ← ModernExpr.ofSExp fuel' e0Exp
          .ok (.obsDisp ty e0)
        | "Fresh", [tyExp] => do
          let ty ← ModernExpr.ofSExp fuel' tyExp
          .ok (.obsFresh ty)
        | "refl", [subExp] => do
          let sub ← ModernExpr.ofSExp fuel' subExp
          .ok (.refl sub)
        | "refl_dir", [.atom dir, subExp] => do
          let sub ← ModernExpr.ofSExp fuel' subExp
          .ok (.reflDir dir sub)
        | "Glue", [aExp, bExp, relExp] => do
          let a ← ModernExpr.ofSExp fuel' aExp
          let b ← ModernExpr.ofSExp fuel' bExp
          let r ← ModernExpr.ofSExp fuel' relExp
          .ok (.glue a b r)
        | "Gel", [aExp, bExp, relExp] => do
          let a ← ModernExpr.ofSExp fuel' aExp
          let b ← ModernExpr.ofSExp fuel' bExp
          let r ← ModernExpr.ofSExp fuel' relExp
          .ok (.gel a b r)
        | "trr", [lineExp, xExp] => do
          let l ← ModernExpr.ofSExp fuel' lineExp
          let x ← ModernExpr.ofSExp fuel' xExp
          .ok (.trr l x)
        | "trl", [lineExp, xExp] => do
          let l ← ModernExpr.ofSExp fuel' lineExp
          let x ← ModernExpr.ofSExp fuel' xExp
          .ok (.trl l x)
        | "liftr", [lineExp, xExp] => do
          let l ← ModernExpr.ofSExp fuel' lineExp
          let x ← ModernExpr.ofSExp fuel' xExp
          .ok (.liftr l x)
        | "liftl", [lineExp, xExp] => do
          let l ← ModernExpr.ofSExp fuel' lineExp
          let x ← ModernExpr.ofSExp fuel' xExp
          .ok (.liftl l x)
        | "sym", [pExp] => do
          let p ← ModernExpr.ofSExp fuel' pExp
          .ok (.sym p)
        | "trans", [pExp, qExp] => do
          let p ← ModernExpr.ofSExp fuel' pExp
          let q ← ModernExpr.ofSExp fuel' qExp
          .ok (.trans p q)
        | "arrow_line", [dExp, cExp] => do
          let d ← ModernExpr.ofSExp fuel' dExp
          let c ← ModernExpr.ofSExp fuel' cExp
          .ok (.arrowLine d c)
        | "prod_line", [.atom fN, .atom sN, fExp, sExp] => do
          let f ← ModernExpr.ofSExp fuel' fExp
          let s ← ModernExpr.ofSExp fuel' sExp
          .ok (.prodLine fN sN f s)
        | "box_line", [.atom modStr, inExp] => do
          let inner ← ModernExpr.ofSExp fuel' inExp
          .ok (.boxLine modStr inner)
        | opStr, [lExp, rExp] =>
          match resolveBinOp64 opStr with
          | some bop => do
            let l ← ModernExpr.ofSExp fuel' lExp
            let r ← ModernExpr.ofSExp fuel' rExp
            .ok (.binOp64 bop l r)
          | none => do
            let l ← ModernExpr.ofSExp fuel' lExp
            let r ← ModernExpr.ofSExp fuel' rExp
            .ok (.call (.var opStr) [l, r])
        | head, args =>
          if args.isEmpty then .error s!"Single-element list form not supported: {head}"
          else do
            let fn ← ModernExpr.ofSExp fuel' (.atom head)
            let elArgs ← args.mapM (ModernExpr.ofSExp fuel')
            .ok (.call fn elArgs)

end

/-! ## 3. Machine-Checked Equivalence Proofs (`0 sorry`, `0 noncomputable`) -/

theorem resolveBinOp64_name (op : BinOp64) : resolveBinOp64 op.name = some op := by
  cases op <;> rfl

theorem resolveBinOp64_none_of_not_listKw {s : String} (h : isListKeyword s = false) :
    resolveBinOp64 s = none := by
  unfold resolveBinOp64
  split <;> try rfl
  all_goals (exfalso; subst_vars; revert h; with_unfolding_all decide)

theorem elabBuiltinAtom_eq_none_of_not_atomKw {ident : String} (h : isAtomKeyword ident = false) :
    elabBuiltinAtom? ident = none := by
  unfold isAtomKeyword at h
  cases hx : elabBuiltinAtom? ident
  · rfl
  · rw [hx] at h; cases h

theorem ofBuiltinAtom_eq_none_of_not_atomKw {ident : String} (h : isAtomKeyword ident = false) :
    ofBuiltinAtom? ident = none := by
  have hn := elabBuiltinAtom_eq_none_of_not_atomKw h
  unfold elabBuiltinAtom? at hn
  unfold ofBuiltinAtom?
  split <;> try rfl
  all_goals (exfalso; subst_vars; with_unfolding_all cases hn)

theorem elaborateSExp_var_nonKw (fuel : Nat) (T : ModeTheory) (mode : ModeId)
    (locals : List String) (ident : String) (h : isAtomKeyword ident = false) :
    elaborateSExp (fuel + 1) T mode locals (.atom ident) =
      match findLocalIx? locals ident with
      | some ix => .ok (.bvar ix)
      | none => .ok (.global ident) := by
  dsimp only [elaborateSExp]
  rw [elabBuiltinAtom_eq_none_of_not_atomKw h]
  rfl

private theorem mapM_elab_eq
    {T : ModeTheory} {mode : ModeId} {locals : List String} {fuel : Nat}
    (ih : ∀ m locs e, e.wf = true →
      elabModernExpr fuel T m locs e = elaborateSExp fuel T m locs e.toSExp)
    (es : List ModernExpr) (hwf : ModernExpr.listWf es = true) :
    es.mapM (elabModernExpr fuel T mode locals) =
      (ModernExpr.listToSExp es).mapM (elaborateSExp fuel T mode locals) := by
  induction es with
  | nil => rfl
  | cons hd tl ihtl =>
    simp only [ModernExpr.listWf, Bool.and_eq_true] at hwf
    dsimp only [ModernExpr.listToSExp]
    rw [List.mapM_cons, List.mapM_cons, ih mode locals hd hwf.1, ihtl hwf.2]

private theorem elabRecordTele_eq
    {T : ModeTheory} {fuel : Nat}
    (ih : ∀ k, k ≤ fuel → ∀ m locs e, e.wf = true →
      elabModernExpr k T m locs e = elaborateSExp k T m locs e.toSExp)
    (mode : ModeId) (locals : List String) (fs : List ModernField)
    (hwf : ModernField.listWf fs = true) :
    elabModernRecordTele fuel T mode locals fs =
      elabRecordTele fuel T mode locals (ModernField.listToSExp fs) := by
  induction fs generalizing fuel locals with
  | nil =>
    cases fuel <;> rfl
  | cons hd tl ihtl =>
    simp only [ModernField.listWf, Bool.and_eq_true] at hwf
    cases hd with
    | plain fname fty =>
      cases fuel with
      | zero => rfl
      | succ f' =>
        dsimp only [elabModernRecordTele, elabRecordTele, ModernField.listToSExp, ModernField.toSExp]
        rw [ih f' (Nat.le_succ f') mode locals fty hwf.1,
          ihtl (fun k hk => ih k (Nat.le_trans hk (Nat.le_succ f'))) (fname :: locals) hwf.2]
        cases fty.toSExp <;> rfl
    | modal fname modStr fty =>
      cases fuel with
      | zero => rfl
      | succ f' =>
        dsimp only [elabModernRecordTele, elabRecordTele, ModernField.listToSExp, ModernField.toSExp]
        cases resolveModPath T mode modStr with
        | error e => rfl
        | ok mp =>
          dsimp only [bind, Except.bind]
          rw [ih f' (Nat.le_succ f') mp.dom locals fty hwf.1,
            ihtl (fun k hk => ih k (Nat.le_trans hk (Nat.le_succ f'))) (fname :: locals) hwf.2]

private theorem elabTupleFields_eq
    {T : ModeTheory} {fuel : Nat}
    (ih : ∀ k, k ≤ fuel → ∀ m locs e, e.wf = true →
      elabModernExpr k T m locs e = elaborateSExp k T m locs e.toSExp)
    (mode : ModeId) (locals : List String) (fs : List ModernTupleField)
    (hwf : ModernTupleField.listWf fs = true) :
    elabModernTupleFields fuel T mode locals fs =
      elabTupleFields fuel T mode locals (ModernTupleField.listToSExp fs) := by
  induction fs generalizing fuel with
  | nil =>
    cases fuel <;> rfl
  | cons hd tl ihtl =>
    simp only [ModernTupleField.listWf, Bool.and_eq_true] at hwf
    cases hd with
    | assign fname val =>
      cases fuel with
      | zero => rfl
      | succ f' =>
        dsimp only [elabModernTupleFields, elabTupleFields, ModernTupleField.listToSExp, ModernTupleField.toSExp]
        rw [ih f' (Nat.le_succ f') mode locals val hwf.1,
          ihtl (fun k hk => ih k (Nat.le_trans hk (Nat.le_succ f'))) hwf.2]

private theorem toSExp_dichotomy_of_not_reserved (fn : ModernExpr)
    (hnr : fn.isReservedCallHead = false) :
    (∃ ident, fn = .var ident ∧ isReservedListHead ident = false) ∨
    (∃ fnList, fn.toSExp = .list fnList) := by
  cases fn <;> simp only [ModernExpr.isReservedCallHead] at hnr
  case var ident =>
    simp only [Bool.or_eq_false_iff, isListKeyword] at hnr
    exact .inl ⟨ident, rfl, hnr.2⟩
  case binOp64 op l r =>
    cases op <;> exact .inr ⟨_, rfl⟩
  all_goals
    first
    | exact .inr ⟨_, rfl⟩
    | exact Bool.noConfusion hnr

private theorem elaborateSExp_call_nonReserved
    (fuel' : Nat) (T : ModeTheory) (mode : ModeId) (locals : List String)
    (fn : ModernExpr) (args : List ModernExpr)
    (hnr : (!fn.isReservedCallHead) = true) :
    elaborateSExp (fuel' + 1) T mode locals (.list (fn.toSExp :: ModernExpr.listToSExp args)) =
      (do
        let fn' ← elaborateSExp fuel' T mode locals fn.toSExp
        let args' ← (ModernExpr.listToSExp args).mapM (elaborateSExp fuel' T mode locals)
        let mp := ModPath.id mode
        .ok (args'.foldl (fun acc a => .app acc mp a) fn')) := by
  have hnr' : fn.isReservedCallHead = false := by revert hnr; cases fn.isReservedCallHead <;> decide
  rcases toSExp_dichotomy_of_not_reserved fn hnr' with ⟨ident, rfl, hList⟩ | ⟨fnList, hEq⟩
  · dsimp only [ModernExpr.toSExp, elaborateSExp]
    rw [hList]
    rfl
  · rw [hEq]
    rfl

private theorem elabModernExpr_eq_bounded (bound : Nat) (T : ModeTheory) :
    ∀ fuel, fuel ≤ bound → ∀ mode locals (e : ModernExpr), e.wf = true →
      elabModernExpr fuel T mode locals e = elaborateSExp fuel T mode locals e.toSExp := by
  induction bound with
  | zero =>
    intro fuel hle mode locals e _
    have hz : fuel = 0 := Nat.eq_zero_of_le_zero hle
    subst hz
    rfl
  | succ b ih =>
    intro fuel hle mode locals e hwf
    cases fuel with
    | zero => rfl
    | succ f' =>
      have hf : f' ≤ b := Nat.le_of_succ_le_succ hle
      have ihf : ∀ m locs e', e'.wf = true →
          elabModernExpr f' T m locs e' = elaborateSExp f' T m locs e'.toSExp :=
        ih f' hf
      have ihSub : ∀ k, k ≤ f' → ∀ m locs e', e'.wf = true →
          elabModernExpr k T m locs e' = elaborateSExp k T m locs e'.toSExp :=
        fun k hk => ih k (Nat.le_trans hk hf)
      cases e with
      | typeU0 | typeU1 | typeU _ | typeExt | u64Ty
      | zeroNat | trueBool | falseBool | ttUnit
      | natTy | boolTy | unitTy | emptyTy | hole0 | hole _ | u64Lit _ =>
        with_unfolding_all rfl
      | var ident =>
        simp only [ModernExpr.wf, Bool.not_eq_true'] at hwf
        rw [ModernExpr.toSExp, elaborateSExp_var_nonKw f' T mode locals ident hwf]
        rfl
      | succNat n =>
        simp only [ModernExpr.wf] at hwf
        dsimp only [elabModernExpr]
        rw [ihf mode locals n hwf]
        with_unfolding_all rfl
      | pi x mod dom cod =>
        simp only [ModernExpr.wf, Bool.and_eq_true] at hwf
        have hRhs : elaborateSExp (f' + 1) T mode locals (ModernExpr.pi x mod dom cod).toSExp =
            (do
              let mp ← resolveModPath T mode mod
              let d ← elaborateSExp f' T mp.dom locals dom.toSExp
              let c ← elaborateSExp f' T mode (x :: locals) cod.toSExp
              .ok (.pi x mp d c)) := by with_unfolding_all rfl
        rw [hRhs]
        dsimp only [elabModernExpr]
        cases resolveModPath T mode mod with
        | error err => rfl
        | ok mp =>
          dsimp only [bind, Except.bind]
          rw [ihf mp.dom locals dom hwf.1, ihf mode (x :: locals) cod hwf.2]
      | arrow dom cod =>
        simp only [ModernExpr.wf, Bool.and_eq_true] at hwf
        dsimp only [elabModernExpr]
        rw [ihf mode locals dom hwf.1, ihf mode ("_" :: locals) cod hwf.2]
        with_unfolding_all rfl
      | lamMod x mod body =>
        simp only [ModernExpr.wf] at hwf
        have hRhs : elaborateSExp (f' + 1) T mode locals (ModernExpr.lamMod x mod body).toSExp =
            (do
              let mp ← resolveModPath T mode mod
              let b ← elaborateSExp f' T mode (x :: locals) body.toSExp
              .ok (.lam x mp b)) := by with_unfolding_all rfl
        rw [hRhs]
        dsimp only [elabModernExpr]
        cases resolveModPath T mode mod with
        | error err => rfl
        | ok mp =>
          dsimp only [bind, Except.bind]
          rw [ihf mode (x :: locals) body hwf]
      | lam x body =>
        simp only [ModernExpr.wf] at hwf
        dsimp only [elabModernExpr]
        rw [ihf mode (x :: locals) body hwf]
        with_unfolding_all rfl
      | letIn x ty val body =>
        simp only [ModernExpr.wf, Bool.and_eq_true] at hwf
        dsimp only [elabModernExpr]
        rw [ihf mode locals ty hwf.1.1, ihf mode locals val hwf.1.2, ihf mode (x :: locals) body hwf.2]
        with_unfolding_all rfl
      | appMod fn mod arg =>
        simp only [ModernExpr.wf, Bool.and_eq_true] at hwf
        have hRhs : elaborateSExp (f' + 1) T mode locals (ModernExpr.appMod fn mod arg).toSExp =
            (do
              let mp ← resolveModPath T mode mod
              let fn' ← elaborateSExp f' T mode locals fn.toSExp
              let arg' ← elaborateSExp f' T mp.dom locals arg.toSExp
              .ok (.app fn' mp arg')) := by with_unfolding_all rfl
        rw [hRhs]
        dsimp only [elabModernExpr]
        cases resolveModPath T mode mod with
        | error err => rfl
        | ok mp =>
          dsimp only [bind, Except.bind]
          rw [ihf mode locals fn hwf.1, ihf mp.dom locals arg hwf.2]
      | boxTy mod ty =>
        simp only [ModernExpr.wf] at hwf
        have hRhs : elaborateSExp (f' + 1) T mode locals (ModernExpr.boxTy mod ty).toSExp =
            (do
              let mp ← resolveModPath T mode mod
              let ty' ← elaborateSExp f' T mp.dom locals ty.toSExp
              .ok (.modalBox mp ty')) := by with_unfolding_all rfl
        rw [hRhs]
        dsimp only [elabModernExpr]
        cases resolveModPath T mode mod with
        | error err => rfl
        | ok mp =>
          dsimp only [bind, Except.bind]
          rw [ihf mp.dom locals ty hwf]
      | boxIntro mod sub =>
        simp only [ModernExpr.wf] at hwf
        have hRhs : elaborateSExp (f' + 1) T mode locals (ModernExpr.boxIntro mod sub).toSExp =
            (do
              let mp ← resolveModPath T mode mod
              let sub' ← elaborateSExp f' T mp.dom locals sub.toSExp
              .ok (.boxIntro mp sub')) := by with_unfolding_all rfl
        rw [hRhs]
        dsimp only [elabModernExpr]
        cases resolveModPath T mode mod with
        | error err => rfl
        | ok mp =>
          dsimp only [bind, Except.bind]
          rw [ihf mp.dom locals sub hwf]
      | record fs =>
        simp only [ModernExpr.wf] at hwf
        dsimp only [elabModernExpr]
        rw [elabRecordTele_eq ihSub mode locals fs hwf]
        with_unfolding_all rfl
      | tuple fs =>
        simp only [ModernExpr.wf] at hwf
        dsimp only [elabModernExpr]
        rw [elabTupleFields_eq ihSub mode locals fs hwf]
        with_unfolding_all rfl
      | proj sub fld =>
        simp only [ModernExpr.wf] at hwf
        dsimp only [elabModernExpr]
        rw [ihf mode locals sub hwf]
        with_unfolding_all rfl
      | funext x body =>
        simp only [ModernExpr.wf] at hwf
        dsimp only [elabModernExpr]
        rw [ihf mode ((x ++ "2") :: (x ++ "1") :: (x ++ "0") :: locals) body hwf]
        with_unfolding_all rfl
      | hap pf a0 a1 pa =>
        simp only [ModernExpr.wf, Bool.and_eq_true] at hwf
        dsimp only [elabModernExpr]
        rw [ihf mode locals pf hwf.1.1.1, ihf mode locals a0 hwf.1.1.2,
          ihf mode locals a1 hwf.1.2, ihf mode locals pa hwf.2]
        with_unfolding_all rfl
      | ifz c z nz =>
        simp only [ModernExpr.wf, Bool.and_eq_true] at hwf
        dsimp only [elabModernExpr]
        rw [ihf mode locals c hwf.1.1, ihf mode locals z hwf.1.2, ihf mode locals nz hwf.2]
        with_unfolding_all rfl
      | repeatU64 cntStr init accVar step =>
        simp only [ModernExpr.wf, Bool.and_eq_true] at hwf
        have hRhs : elaborateSExp (f' + 1) T mode locals (ModernExpr.repeatU64 cntStr init accVar step).toSExp =
            (match cntStr.toNat? with
             | none => .error s!"Invalid u64_repeat count '{cntStr}'"
             | some cnt => do
               let i ← elaborateSExp f' T mode locals init.toSExp
               let s ← elaborateSExp f' T mode (accVar :: locals) step.toSExp
               .ok (.u64Repeat cnt.toUInt64 i s)) := by with_unfolding_all rfl
        rw [hRhs]
        dsimp only [elabModernExpr]
        cases cntStr.toNat? with
        | none => rfl
        | some cnt =>
          rw [ihf mode locals init hwf.1, ihf mode (accVar :: locals) step hwf.2]
      | obsId ty ends =>
        simp only [ModernExpr.wf, Bool.and_eq_true] at hwf
        dsimp only [elabModernExpr]
        rw [ihf mode locals ty hwf.1, mapM_elab_eq ihf ends hwf.2]
        with_unfolding_all rfl
      | obsBr ty ends =>
        simp only [ModernExpr.wf, Bool.and_eq_true] at hwf
        dsimp only [elabModernExpr]
        rw [ihf mode locals ty hwf.1, mapM_elab_eq ihf ends hwf.2]
        with_unfolding_all rfl
      | obsDisp ty e0 =>
        simp only [ModernExpr.wf, Bool.and_eq_true] at hwf
        dsimp only [elabModernExpr]
        rw [ihf mode locals ty hwf.1, ihf mode locals e0 hwf.2]
        with_unfolding_all rfl
      | obsFresh ty =>
        simp only [ModernExpr.wf] at hwf
        dsimp only [elabModernExpr]
        rw [ihf mode locals ty hwf]
        with_unfolding_all rfl
      | refl sub =>
        simp only [ModernExpr.wf] at hwf
        dsimp only [elabModernExpr]
        rw [ihf mode locals sub hwf]
        with_unfolding_all rfl
      | reflDir dir sub =>
        simp only [ModernExpr.wf] at hwf
        have hRhs : elaborateSExp (f' + 1) T mode locals (ModernExpr.reflDir dir sub).toSExp =
            (do
              let g ← resolveDir dir
              let s ← elaborateSExp f' T mode locals sub.toSExp
              .ok (.refl g s)) := by with_unfolding_all rfl
        rw [hRhs]
        dsimp only [elabModernExpr]
        cases resolveDir dir with
        | error err => rfl
        | ok g =>
          dsimp only [bind, Except.bind]
          rw [ihf mode locals sub hwf]
      | glue a b rel =>
        simp only [ModernExpr.wf, Bool.and_eq_true] at hwf
        dsimp only [elabModernExpr]
        rw [ihf mode locals a hwf.1.1, ihf mode locals b hwf.1.2, ihf mode locals rel hwf.2]
        with_unfolding_all rfl
      | gel a b rel =>
        simp only [ModernExpr.wf, Bool.and_eq_true] at hwf
        dsimp only [elabModernExpr]
        rw [ihf mode locals a hwf.1.1, ihf mode locals b hwf.1.2, ihf mode locals rel hwf.2]
        with_unfolding_all rfl
      | trr l x =>
        simp only [ModernExpr.wf, Bool.and_eq_true] at hwf
        dsimp only [elabModernExpr]
        rw [ihf mode locals l hwf.1, ihf mode locals x hwf.2]
        with_unfolding_all rfl
      | trl l x =>
        simp only [ModernExpr.wf, Bool.and_eq_true] at hwf
        dsimp only [elabModernExpr]
        rw [ihf mode locals l hwf.1, ihf mode locals x hwf.2]
        with_unfolding_all rfl
      | liftr l x =>
        simp only [ModernExpr.wf, Bool.and_eq_true] at hwf
        dsimp only [elabModernExpr]
        rw [ihf mode locals l hwf.1, ihf mode locals x hwf.2]
        with_unfolding_all rfl
      | liftl l x =>
        simp only [ModernExpr.wf, Bool.and_eq_true] at hwf
        dsimp only [elabModernExpr]
        rw [ihf mode locals l hwf.1, ihf mode locals x hwf.2]
        with_unfolding_all rfl
      | sym p =>
        simp only [ModernExpr.wf] at hwf
        dsimp only [elabModernExpr]
        rw [ihf mode locals p hwf]
        with_unfolding_all rfl
      | trans p q =>
        simp only [ModernExpr.wf, Bool.and_eq_true] at hwf
        dsimp only [elabModernExpr]
        rw [ihf mode locals p hwf.1, ihf mode locals q hwf.2]
        with_unfolding_all rfl
      | arrowLine d c =>
        simp only [ModernExpr.wf, Bool.and_eq_true] at hwf
        dsimp only [elabModernExpr]
        rw [ihf mode locals d hwf.1, ihf mode locals c hwf.2]
        with_unfolding_all rfl
      | prodLine fN sN fL sL =>
        simp only [ModernExpr.wf, Bool.and_eq_true] at hwf
        dsimp only [elabModernExpr]
        rw [ihf mode locals fL hwf.1, ihf mode locals sL hwf.2]
        with_unfolding_all rfl
      | boxLine mod inner =>
        simp only [ModernExpr.wf] at hwf
        have hRhs : elaborateSExp (f' + 1) T mode locals (ModernExpr.boxLine mod inner).toSExp =
            (do
              let mp ← resolveModPath T mode mod
              let in' ← elaborateSExp f' T mp.dom locals inner.toSExp
              .ok (.boxLine Dir.hott mp in')) := by with_unfolding_all rfl
        rw [hRhs]
        dsimp only [elabModernExpr]
        cases resolveModPath T mode mod with
        | error err => rfl
        | ok mp =>
          dsimp only [bind, Except.bind]
          rw [ihf mp.dom locals inner hwf]
      | binOp64 op l r =>
        simp only [ModernExpr.wf, Bool.and_eq_true] at hwf
        dsimp only [elabModernExpr]
        rw [ihf mode locals l hwf.1, ihf mode locals r hwf.2]
        cases op <;> with_unfolding_all rfl
      | call fn args =>
        simp only [ModernExpr.wf, Bool.and_eq_true] at hwf
        rcases hwf with ⟨⟨⟨_, hnr⟩, hfnWf⟩, hargsWf⟩
        rw [ModernExpr.toSExp, elaborateSExp_call_nonReserved f' T mode locals fn args hnr]
        dsimp only [elabModernExpr]
        rw [ihf mode locals fn hfnWf, mapM_elab_eq ihf args hargsWf]

/-- **Landmark Theorem SYN.1 (`elabModernExpr_eq_elaborateSExp`, `0 sorry`)**:
    Direct elaboration of any well-formed Modern `.narya` AST `e` produces the **exact same
    `Except String Term`** as legacy Lisp `.ny` `elaborateSExp` across all fuel bounds,
    all 2-categorical `ModeTheory`s, all modes, and all binder environments! -/
theorem elabModernExpr_eq_elaborateSExp
    (fuel : Nat) (T : ModeTheory) (mode : ModeId) (locals : List String)
    (e : ModernExpr) (hwf : e.wf = true) :
    elabModernExpr fuel T mode locals e = elaborateSExp fuel T mode locals e.toSExp :=
  elabModernExpr_eq_bounded fuel T fuel (Nat.le_refl fuel) mode locals e hwf

/-! ### Roundtrip Depth & `ofSExp ∘ toSExp = ok` Theorem (`0 sorry`) -/

mutual

def ModernField.depth : ModernField → Nat
  | .plain _ fty => fty.depth + 1
  | .modal _ _ fty => fty.depth + 1

def ModernTupleField.depth : ModernTupleField → Nat
  | .assign _ val => val.depth + 1

def ModernExpr.listDepth : List ModernExpr → Nat
  | [] => 0
  | e :: es => Nat.max e.depth (ModernExpr.listDepth es)

def ModernField.listDepth : List ModernField → Nat
  | [] => 1
  | f :: fs => Nat.max f.depth (ModernField.listDepth fs + 1)

def ModernTupleField.listDepth : List ModernTupleField → Nat
  | [] => 1
  | f :: fs => Nat.max f.depth (ModernTupleField.listDepth fs + 1)

def ModernExpr.depth : ModernExpr → Nat
  | .typeU0 | .typeU1 | .typeU _ | .typeExt | .u64Ty
  | .zeroNat | .trueBool | .falseBool | .ttUnit
  | .natTy | .boolTy | .unitTy | .emptyTy | .hole0 | .hole _
  | .var _ | .u64Lit _ => 1
  | .succNat n => n.depth + 1
  | .pi _ _ dom cod => Nat.max dom.depth cod.depth + 1
  | .arrow dom cod => Nat.max dom.depth cod.depth + 1
  | .lamMod _ _ body => body.depth + 1
  | .lam _ body => body.depth + 1
  | .letIn _ ty val body => Nat.max (Nat.max ty.depth val.depth) body.depth + 1
  | .appMod fn _ arg => Nat.max fn.depth arg.depth + 1
  | .boxTy _ ty => ty.depth + 1
  | .boxIntro _ sub => sub.depth + 1
  | .record fs => ModernField.listDepth fs + 1
  | .tuple fs => ModernTupleField.listDepth fs + 1
  | .proj sub _ => sub.depth + 1
  | .funext _ body => body.depth + 1
  | .hap pf a0 a1 pa => Nat.max (Nat.max pf.depth a0.depth) (Nat.max a1.depth pa.depth) + 1
  | .ifz c z nz => Nat.max (Nat.max c.depth z.depth) nz.depth + 1
  | .repeatU64 _ init _ step => Nat.max init.depth step.depth + 1
  | .obsId ty ends => Nat.max ty.depth (ModernExpr.listDepth ends) + 1
  | .obsBr ty ends => Nat.max ty.depth (ModernExpr.listDepth ends) + 1
  | .obsDisp ty e0 => Nat.max ty.depth e0.depth + 1
  | .obsFresh ty => ty.depth + 1
  | .refl sub => sub.depth + 1
  | .reflDir _ sub => sub.depth + 1
  | .glue a b rel => Nat.max (Nat.max a.depth b.depth) rel.depth + 1
  | .gel a b rel => Nat.max (Nat.max a.depth b.depth) rel.depth + 1
  | .trr l x => Nat.max l.depth x.depth + 1
  | .trl l x => Nat.max l.depth x.depth + 1
  | .liftr l x => Nat.max l.depth x.depth + 1
  | .liftl l x => Nat.max l.depth x.depth + 1
  | .sym p => p.depth + 1
  | .trans p q => Nat.max p.depth q.depth + 1
  | .arrowLine d c => Nat.max d.depth c.depth + 1
  | .prodLine _ _ fL sL => Nat.max fL.depth sL.depth + 1
  | .boxLine _ inner => inner.depth + 1
  | .binOp64 _ l r => Nat.max l.depth r.depth + 1
  | .call fn args => Nat.max fn.depth (ModernExpr.listDepth args) + 1

end

private theorem ofSExp_var_nonKw (fuel : Nat) (ident : String) (h : isAtomKeyword ident = false) :
    ModernExpr.ofSExp (fuel + 1) (.atom ident) = .ok (.var ident) := by
  dsimp only [ModernExpr.ofSExp]
  rw [ofBuiltinAtom_eq_none_of_not_atomKw h]

private theorem ofSExp_list_roundtrip {fuel : Nat}
    (ih : ∀ e : ModernExpr, e.depth ≤ fuel → e.wf = true → ModernExpr.ofSExp fuel e.toSExp = .ok e)
    (es : List ModernExpr) (hd : ModernExpr.listDepth es ≤ fuel) (hwf : ModernExpr.listWf es = true) :
    (ModernExpr.listToSExp es).mapM (ModernExpr.ofSExp fuel) = .ok es := by
  induction es with
  | nil => rfl
  | cons x xs ihxs =>
    simp only [ModernExpr.listDepth] at hd
    simp only [ModernExpr.listWf, Bool.and_eq_true] at hwf
    have hx : x.depth ≤ fuel := Nat.le_trans (Nat.le_max_left _ _) hd
    have hxs : ModernExpr.listDepth xs ≤ fuel := Nat.le_trans (Nat.le_max_right _ _) hd
    dsimp only [ModernExpr.listToSExp]
    rw [List.mapM_cons, ih x hx hwf.1, ihxs hxs hwf.2]
    rfl

private theorem ofSExp_fields_roundtrip {fuel : Nat}
    (ih : ∀ k, k ≤ fuel → ∀ e : ModernExpr, e.depth ≤ k → e.wf = true →
      ModernExpr.ofSExp k e.toSExp = .ok e)
    (fs : List ModernField) (hd : ModernField.listDepth fs ≤ fuel) (hwf : ModernField.listWf fs = true) :
    ModernField.ofSExp fuel (ModernField.listToSExp fs) = .ok fs := by
  induction fs generalizing fuel with
  | nil =>
    cases fuel with
    | zero => exact absurd hd (Nat.not_succ_le_zero _)
    | succ _ => rfl
  | cons f rest ihrest =>
    simp only [ModernField.listDepth] at hd
    simp only [ModernField.listWf, Bool.and_eq_true] at hwf
    have hf : f.depth ≤ fuel := Nat.le_trans (Nat.le_max_left _ _) hd
    have hrest : ModernField.listDepth rest + 1 ≤ fuel := Nat.le_trans (Nat.le_max_right _ _) hd
    cases fuel with
    | zero => exact absurd hrest (Nat.not_succ_le_zero _)
    | succ f' =>
      have hrest' : ModernField.listDepth rest ≤ f' := Nat.le_of_succ_le_succ hrest
      have subIh : ∀ k, k ≤ f' → ∀ e : ModernExpr, e.depth ≤ k → e.wf = true →
          ModernExpr.ofSExp k e.toSExp = .ok e :=
        fun k hk => ih k (Nat.le_trans hk (Nat.le_succ f'))
      cases f with
      | plain fname fty =>
        simp only [ModernField.depth] at hf
        have hfty : fty.depth ≤ f' := Nat.le_of_succ_le_succ hf
        have hLhs : ModernField.ofSExp (f' + 1) (ModernField.listToSExp (.plain fname fty :: rest)) =
            (do
              let fty' ← ModernExpr.ofSExp f' fty.toSExp
              let fs' ← ModernField.ofSExp f' (ModernField.listToSExp rest)
              .ok (.plain fname fty' :: fs')) := by
          dsimp only [ModernField.listToSExp, ModernField.toSExp, ModernField.ofSExp]
          cases fty.toSExp <;> rfl
        rw [hLhs, ih f' (Nat.le_succ f') fty hfty hwf.1, ihrest subIh hrest' hwf.2]
        rfl
      | modal fname modStr fty =>
        simp only [ModernField.depth] at hf
        have hfty : fty.depth ≤ f' := Nat.le_of_succ_le_succ hf
        dsimp only [ModernField.listToSExp, ModernField.toSExp, ModernField.ofSExp]
        rw [ih f' (Nat.le_succ f') fty hfty hwf.1, ihrest subIh hrest' hwf.2]
        rfl

private theorem ofSExp_tupleFields_roundtrip {fuel : Nat}
    (ih : ∀ k, k ≤ fuel → ∀ e : ModernExpr, e.depth ≤ k → e.wf = true →
      ModernExpr.ofSExp k e.toSExp = .ok e)
    (fs : List ModernTupleField) (hd : ModernTupleField.listDepth fs ≤ fuel)
    (hwf : ModernTupleField.listWf fs = true) :
    ModernTupleField.ofSExp fuel (ModernTupleField.listToSExp fs) = .ok fs := by
  induction fs generalizing fuel with
  | nil =>
    cases fuel with
    | zero => exact absurd hd (Nat.not_succ_le_zero _)
    | succ _ => rfl
  | cons f rest ihrest =>
    simp only [ModernTupleField.listDepth] at hd
    simp only [ModernTupleField.listWf, Bool.and_eq_true] at hwf
    have hf : f.depth ≤ fuel := Nat.le_trans (Nat.le_max_left _ _) hd
    have hrest : ModernTupleField.listDepth rest + 1 ≤ fuel := Nat.le_trans (Nat.le_max_right _ _) hd
    cases fuel with
    | zero => exact absurd hrest (Nat.not_succ_le_zero _)
    | succ f' =>
      have hrest' : ModernTupleField.listDepth rest ≤ f' := Nat.le_of_succ_le_succ hrest
      have subIh : ∀ k, k ≤ f' → ∀ e : ModernExpr, e.depth ≤ k → e.wf = true →
          ModernExpr.ofSExp k e.toSExp = .ok e :=
        fun k hk => ih k (Nat.le_trans hk (Nat.le_succ f'))
      cases f with
      | assign fname val =>
        simp only [ModernTupleField.depth] at hf
        have hval : val.depth ≤ f' := Nat.le_of_succ_le_succ hf
        dsimp only [ModernTupleField.listToSExp, ModernTupleField.toSExp, ModernTupleField.ofSExp]
        rw [ih f' (Nat.le_succ f') val hval hwf.1, ihrest subIh hrest' hwf.2]
        rfl

private theorem ofSExp_call_nonReserved
    (fuel' : Nat) (fn : ModernExpr) (args : List ModernExpr)
    (hne : (!args.isEmpty) = true) (hnr : (!fn.isReservedCallHead) = true)
    (hfnOk : ModernExpr.ofSExp fuel' fn.toSExp = .ok fn)
    (hargsOk : (ModernExpr.listToSExp args).mapM (ModernExpr.ofSExp fuel') = .ok args) :
    ModernExpr.ofSExp (fuel' + 1) (.list (fn.toSExp :: ModernExpr.listToSExp args)) =
      .ok (.call fn args) := by
  have hnr' : fn.isReservedCallHead = false := by revert hnr; cases fn.isReservedCallHead <;> decide
  have hListNe : (ModernExpr.listToSExp args).isEmpty = false := by
    cases args with
    | nil => cases hne
    | cons _ _ => rfl
  rcases toSExp_dichotomy_of_not_reserved fn hnr' with ⟨ident, rfl, hList⟩ | ⟨fnList, hEq⟩
  · dsimp only [ModernExpr.toSExp, ModernExpr.ofSExp]
    rw [hList, hListNe]
    change (ModernExpr.ofSExp fuel' (.atom ident) >>= fun f =>
      (ModernExpr.listToSExp args).mapM (ModernExpr.ofSExp fuel') >>= fun a =>
        Except.ok (ModernExpr.call f a)) = _
    dsimp only [ModernExpr.toSExp] at hfnOk
    rw [hfnOk, hargsOk]
    rfl
  · rw [hEq] at hfnOk ⊢
    dsimp only [ModernExpr.ofSExp]
    rw [hListNe]
    change (ModernExpr.ofSExp fuel' (.list fnList) >>= fun f =>
      (ModernExpr.listToSExp args).mapM (ModernExpr.ofSExp fuel') >>= fun a =>
        Except.ok (ModernExpr.call f a)) = _
    rw [hfnOk, hargsOk]
    rfl

private theorem ofSExp_toSExp_bounded (bound : Nat) :
    ∀ fuel, fuel ≤ bound → ∀ (e : ModernExpr), e.depth ≤ fuel → e.wf = true →
      ModernExpr.ofSExp fuel e.toSExp = .ok e := by
  induction bound with
  | zero =>
    intro fuel hle e hd _
    have hz : fuel = 0 := Nat.eq_zero_of_le_zero hle
    subst hz
    cases e <;> exact absurd hd (Nat.not_succ_le_zero _)
  | succ b ih =>
    intro fuel hle e hd hwf
    cases fuel with
    | zero => cases e <;> exact absurd hd (Nat.not_succ_le_zero _)
    | succ f' =>
      have hf : f' ≤ b := Nat.le_of_succ_le_succ hle
      have ihf : ∀ e' : ModernExpr, e'.depth ≤ f' → e'.wf = true →
          ModernExpr.ofSExp f' e'.toSExp = .ok e' :=
        ih f' hf
      have ihSub : ∀ k, k ≤ f' → ∀ e' : ModernExpr, e'.depth ≤ k → e'.wf = true →
          ModernExpr.ofSExp k e'.toSExp = .ok e' :=
        fun k hk => ih k (Nat.le_trans hk hf)
      cases e with
      | typeU0 | typeU1 | typeU _ | typeExt | u64Ty
      | zeroNat | trueBool | falseBool | ttUnit
      | natTy | boolTy | unitTy | emptyTy | hole0 | hole _ | u64Lit _ =>
        with_unfolding_all rfl
      | var ident =>
        simp only [ModernExpr.wf, Bool.not_eq_true'] at hwf
        exact ofSExp_var_nonKw f' ident hwf
      | succNat n =>
        simp only [ModernExpr.depth, ModernExpr.wf] at hd hwf
        have hStep : ModernExpr.ofSExp (f' + 1) (ModernExpr.succNat n).toSExp =
            (ModernExpr.ofSExp f' n.toSExp >>= fun v => .ok (.succNat v)) := by with_unfolding_all rfl
        rw [hStep, ihf n (Nat.le_of_succ_le_succ hd) hwf]; rfl
      | pi x mod dom cod =>
        simp only [ModernExpr.depth, ModernExpr.wf, Bool.and_eq_true] at hd hwf
        have hm := Nat.le_of_succ_le_succ hd
        have hStep : ModernExpr.ofSExp (f' + 1) (ModernExpr.pi x mod dom cod).toSExp =
            (do let d ← ModernExpr.ofSExp f' dom.toSExp; let c ← ModernExpr.ofSExp f' cod.toSExp; .ok (.pi x mod d c)) := by
          with_unfolding_all rfl
        rw [hStep, ihf dom (Nat.le_trans (Nat.le_max_left _ _) hm) hwf.1,
          ihf cod (Nat.le_trans (Nat.le_max_right _ _) hm) hwf.2]; rfl
      | arrow dom cod =>
        simp only [ModernExpr.depth, ModernExpr.wf, Bool.and_eq_true] at hd hwf
        have hm := Nat.le_of_succ_le_succ hd
        have hStep : ModernExpr.ofSExp (f' + 1) (ModernExpr.arrow dom cod).toSExp =
            (do let d ← ModernExpr.ofSExp f' dom.toSExp; let c ← ModernExpr.ofSExp f' cod.toSExp; .ok (.arrow d c)) := by
          with_unfolding_all rfl
        rw [hStep, ihf dom (Nat.le_trans (Nat.le_max_left _ _) hm) hwf.1,
          ihf cod (Nat.le_trans (Nat.le_max_right _ _) hm) hwf.2]; rfl
      | lamMod x mod body =>
        simp only [ModernExpr.depth, ModernExpr.wf] at hd hwf
        have hStep : ModernExpr.ofSExp (f' + 1) (ModernExpr.lamMod x mod body).toSExp =
            (ModernExpr.ofSExp f' body.toSExp >>= fun b => .ok (.lamMod x mod b)) := by with_unfolding_all rfl
        rw [hStep, ihf body (Nat.le_of_succ_le_succ hd) hwf]; rfl
      | lam x body =>
        simp only [ModernExpr.depth, ModernExpr.wf] at hd hwf
        have hStep : ModernExpr.ofSExp (f' + 1) (ModernExpr.lam x body).toSExp =
            (ModernExpr.ofSExp f' body.toSExp >>= fun b => .ok (.lam x b)) := by with_unfolding_all rfl
        rw [hStep, ihf body (Nat.le_of_succ_le_succ hd) hwf]; rfl
      | letIn x ty val body =>
        simp only [ModernExpr.depth, ModernExpr.wf, Bool.and_eq_true] at hd hwf
        have hm := Nat.le_of_succ_le_succ hd
        have h12 := Nat.le_trans (Nat.le_max_left _ _) hm
        have hStep : ModernExpr.ofSExp (f' + 1) (ModernExpr.letIn x ty val body).toSExp =
            (do let t ← ModernExpr.ofSExp f' ty.toSExp; let v ← ModernExpr.ofSExp f' val.toSExp
                let b ← ModernExpr.ofSExp f' body.toSExp; .ok (.letIn x t v b)) := by with_unfolding_all rfl
        rw [hStep, ihf ty (Nat.le_trans (Nat.le_max_left _ _) h12) hwf.1.1,
          ihf val (Nat.le_trans (Nat.le_max_right _ _) h12) hwf.1.2,
          ihf body (Nat.le_trans (Nat.le_max_right _ _) hm) hwf.2]; rfl
      | appMod fn mod arg =>
        simp only [ModernExpr.depth, ModernExpr.wf, Bool.and_eq_true] at hd hwf
        have hm := Nat.le_of_succ_le_succ hd
        have hStep : ModernExpr.ofSExp (f' + 1) (ModernExpr.appMod fn mod arg).toSExp =
            (do let f ← ModernExpr.ofSExp f' fn.toSExp; let a ← ModernExpr.ofSExp f' arg.toSExp
                .ok (.appMod f mod a)) := by with_unfolding_all rfl
        rw [hStep, ihf fn (Nat.le_trans (Nat.le_max_left _ _) hm) hwf.1,
          ihf arg (Nat.le_trans (Nat.le_max_right _ _) hm) hwf.2]; rfl
      | boxTy mod ty =>
        simp only [ModernExpr.depth, ModernExpr.wf] at hd hwf
        have hStep : ModernExpr.ofSExp (f' + 1) (ModernExpr.boxTy mod ty).toSExp =
            (ModernExpr.ofSExp f' ty.toSExp >>= fun t => .ok (.boxTy mod t)) := by with_unfolding_all rfl
        rw [hStep, ihf ty (Nat.le_of_succ_le_succ hd) hwf]; rfl
      | boxIntro mod sub =>
        simp only [ModernExpr.depth, ModernExpr.wf] at hd hwf
        have hStep : ModernExpr.ofSExp (f' + 1) (ModernExpr.boxIntro mod sub).toSExp =
            (ModernExpr.ofSExp f' sub.toSExp >>= fun s => .ok (.boxIntro mod s)) := by with_unfolding_all rfl
        rw [hStep, ihf sub (Nat.le_of_succ_le_succ hd) hwf]; rfl
      | record fs =>
        simp only [ModernExpr.depth, ModernExpr.wf] at hd hwf
        have hStep : ModernExpr.ofSExp (f' + 1) (ModernExpr.record fs).toSExp =
            (ModernField.ofSExp f' (ModernField.listToSExp fs) >>= fun r => .ok (.record r)) := by
          with_unfolding_all rfl
        rw [hStep, ofSExp_fields_roundtrip ihSub fs (Nat.le_of_succ_le_succ hd) hwf]; rfl
      | tuple fs =>
        simp only [ModernExpr.depth, ModernExpr.wf] at hd hwf
        have hStep : ModernExpr.ofSExp (f' + 1) (ModernExpr.tuple fs).toSExp =
            (ModernTupleField.ofSExp f' (ModernTupleField.listToSExp fs) >>= fun r => .ok (.tuple r)) := by
          with_unfolding_all rfl
        rw [hStep, ofSExp_tupleFields_roundtrip ihSub fs (Nat.le_of_succ_le_succ hd) hwf]; rfl
      | proj sub fld =>
        simp only [ModernExpr.depth, ModernExpr.wf] at hd hwf
        have hStep : ModernExpr.ofSExp (f' + 1) (ModernExpr.proj sub fld).toSExp =
            (ModernExpr.ofSExp f' sub.toSExp >>= fun s => .ok (.proj s fld)) := by with_unfolding_all rfl
        rw [hStep, ihf sub (Nat.le_of_succ_le_succ hd) hwf]; rfl
      | funext x body =>
        simp only [ModernExpr.depth, ModernExpr.wf] at hd hwf
        have hStep : ModernExpr.ofSExp (f' + 1) (ModernExpr.funext x body).toSExp =
            (ModernExpr.ofSExp f' body.toSExp >>= fun b => .ok (.funext x b)) := by with_unfolding_all rfl
        rw [hStep, ihf body (Nat.le_of_succ_le_succ hd) hwf]; rfl
      | hap pf a0 a1 pa =>
        simp only [ModernExpr.depth, ModernExpr.wf, Bool.and_eq_true] at hd hwf
        have hm := Nat.le_of_succ_le_succ hd
        have hl := Nat.le_trans (Nat.le_max_left _ _) hm
        have hr := Nat.le_trans (Nat.le_max_right _ _) hm
        have hStep : ModernExpr.ofSExp (f' + 1) (ModernExpr.hap pf a0 a1 pa).toSExp =
            (do let p ← ModernExpr.ofSExp f' pf.toSExp; let x0 ← ModernExpr.ofSExp f' a0.toSExp
                let x1 ← ModernExpr.ofSExp f' a1.toSExp; let px ← ModernExpr.ofSExp f' pa.toSExp
                .ok (.hap p x0 x1 px)) := by with_unfolding_all rfl
        rw [hStep, ihf pf (Nat.le_trans (Nat.le_max_left _ _) hl) hwf.1.1.1,
          ihf a0 (Nat.le_trans (Nat.le_max_right _ _) hl) hwf.1.1.2,
          ihf a1 (Nat.le_trans (Nat.le_max_left _ _) hr) hwf.1.2,
          ihf pa (Nat.le_trans (Nat.le_max_right _ _) hr) hwf.2]; rfl
      | ifz c z nz =>
        simp only [ModernExpr.depth, ModernExpr.wf, Bool.and_eq_true] at hd hwf
        have hm := Nat.le_of_succ_le_succ hd
        have h12 := Nat.le_trans (Nat.le_max_left _ _) hm
        have hStep : ModernExpr.ofSExp (f' + 1) (ModernExpr.ifz c z nz).toSExp =
            (do let cv ← ModernExpr.ofSExp f' c.toSExp; let zv ← ModernExpr.ofSExp f' z.toSExp
                let nzv ← ModernExpr.ofSExp f' nz.toSExp; .ok (.ifz cv zv nzv)) := by with_unfolding_all rfl
        rw [hStep, ihf c (Nat.le_trans (Nat.le_max_left _ _) h12) hwf.1.1,
          ihf z (Nat.le_trans (Nat.le_max_right _ _) h12) hwf.1.2,
          ihf nz (Nat.le_trans (Nat.le_max_right _ _) hm) hwf.2]; rfl
      | repeatU64 cntStr init accVar step =>
        simp only [ModernExpr.depth, ModernExpr.wf, Bool.and_eq_true] at hd hwf
        have hm := Nat.le_of_succ_le_succ hd
        have hStep : ModernExpr.ofSExp (f' + 1) (ModernExpr.repeatU64 cntStr init accVar step).toSExp =
            (do let iv ← ModernExpr.ofSExp f' init.toSExp; let sv ← ModernExpr.ofSExp f' step.toSExp
                .ok (.repeatU64 cntStr iv accVar sv)) := by with_unfolding_all rfl
        rw [hStep, ihf init (Nat.le_trans (Nat.le_max_left _ _) hm) hwf.1,
          ihf step (Nat.le_trans (Nat.le_max_right _ _) hm) hwf.2]; rfl
      | obsId ty ends =>
        simp only [ModernExpr.depth, ModernExpr.wf, Bool.and_eq_true] at hd hwf
        have hm := Nat.le_of_succ_le_succ hd
        have hStep : ModernExpr.ofSExp (f' + 1) (ModernExpr.obsId ty ends).toSExp =
            (do let tv ← ModernExpr.ofSExp f' ty.toSExp
                let evs ← (ModernExpr.listToSExp ends).mapM (ModernExpr.ofSExp f')
                .ok (.obsId tv evs)) := by with_unfolding_all rfl
        rw [hStep, ihf ty (Nat.le_trans (Nat.le_max_left _ _) hm) hwf.1,
          ofSExp_list_roundtrip ihf ends (Nat.le_trans (Nat.le_max_right _ _) hm) hwf.2]; rfl
      | obsBr ty ends =>
        simp only [ModernExpr.depth, ModernExpr.wf, Bool.and_eq_true] at hd hwf
        have hm := Nat.le_of_succ_le_succ hd
        have hStep : ModernExpr.ofSExp (f' + 1) (ModernExpr.obsBr ty ends).toSExp =
            (do let tv ← ModernExpr.ofSExp f' ty.toSExp
                let evs ← (ModernExpr.listToSExp ends).mapM (ModernExpr.ofSExp f')
                .ok (.obsBr tv evs)) := by with_unfolding_all rfl
        rw [hStep, ihf ty (Nat.le_trans (Nat.le_max_left _ _) hm) hwf.1,
          ofSExp_list_roundtrip ihf ends (Nat.le_trans (Nat.le_max_right _ _) hm) hwf.2]; rfl
      | obsDisp ty e0 =>
        simp only [ModernExpr.depth, ModernExpr.wf, Bool.and_eq_true] at hd hwf
        have hm := Nat.le_of_succ_le_succ hd
        have hStep : ModernExpr.ofSExp (f' + 1) (ModernExpr.obsDisp ty e0).toSExp =
            (do let tv ← ModernExpr.ofSExp f' ty.toSExp; let ev ← ModernExpr.ofSExp f' e0.toSExp
                .ok (.obsDisp tv ev)) := by with_unfolding_all rfl
        rw [hStep, ihf ty (Nat.le_trans (Nat.le_max_left _ _) hm) hwf.1,
          ihf e0 (Nat.le_trans (Nat.le_max_right _ _) hm) hwf.2]; rfl
      | obsFresh ty =>
        simp only [ModernExpr.depth, ModernExpr.wf] at hd hwf
        have hStep : ModernExpr.ofSExp (f' + 1) (ModernExpr.obsFresh ty).toSExp =
            (ModernExpr.ofSExp f' ty.toSExp >>= fun t => .ok (.obsFresh t)) := by with_unfolding_all rfl
        rw [hStep, ihf ty (Nat.le_of_succ_le_succ hd) hwf]; rfl
      | refl sub =>
        simp only [ModernExpr.depth, ModernExpr.wf] at hd hwf
        have hStep : ModernExpr.ofSExp (f' + 1) (ModernExpr.refl sub).toSExp =
            (ModernExpr.ofSExp f' sub.toSExp >>= fun s => .ok (.refl s)) := by with_unfolding_all rfl
        rw [hStep, ihf sub (Nat.le_of_succ_le_succ hd) hwf]; rfl
      | reflDir dir sub =>
        simp only [ModernExpr.depth, ModernExpr.wf] at hd hwf
        have hStep : ModernExpr.ofSExp (f' + 1) (ModernExpr.reflDir dir sub).toSExp =
            (ModernExpr.ofSExp f' sub.toSExp >>= fun s => .ok (.reflDir dir s)) := by with_unfolding_all rfl
        rw [hStep, ihf sub (Nat.le_of_succ_le_succ hd) hwf]; rfl
      | glue a b rel =>
        simp only [ModernExpr.depth, ModernExpr.wf, Bool.and_eq_true] at hd hwf
        have hm := Nat.le_of_succ_le_succ hd
        have h12 := Nat.le_trans (Nat.le_max_left _ _) hm
        have hStep : ModernExpr.ofSExp (f' + 1) (ModernExpr.glue a b rel).toSExp =
            (do let av ← ModernExpr.ofSExp f' a.toSExp; let bv ← ModernExpr.ofSExp f' b.toSExp
                let rv ← ModernExpr.ofSExp f' rel.toSExp; .ok (.glue av bv rv)) := by with_unfolding_all rfl
        rw [hStep, ihf a (Nat.le_trans (Nat.le_max_left _ _) h12) hwf.1.1,
          ihf b (Nat.le_trans (Nat.le_max_right _ _) h12) hwf.1.2,
          ihf rel (Nat.le_trans (Nat.le_max_right _ _) hm) hwf.2]; rfl
      | gel a b rel =>
        simp only [ModernExpr.depth, ModernExpr.wf, Bool.and_eq_true] at hd hwf
        have hm := Nat.le_of_succ_le_succ hd
        have h12 := Nat.le_trans (Nat.le_max_left _ _) hm
        have hStep : ModernExpr.ofSExp (f' + 1) (ModernExpr.gel a b rel).toSExp =
            (do let av ← ModernExpr.ofSExp f' a.toSExp; let bv ← ModernExpr.ofSExp f' b.toSExp
                let rv ← ModernExpr.ofSExp f' rel.toSExp; .ok (.gel av bv rv)) := by with_unfolding_all rfl
        rw [hStep, ihf a (Nat.le_trans (Nat.le_max_left _ _) h12) hwf.1.1,
          ihf b (Nat.le_trans (Nat.le_max_right _ _) h12) hwf.1.2,
          ihf rel (Nat.le_trans (Nat.le_max_right _ _) hm) hwf.2]; rfl
      | trr l x =>
        simp only [ModernExpr.depth, ModernExpr.wf, Bool.and_eq_true] at hd hwf
        have hm := Nat.le_of_succ_le_succ hd
        have hStep : ModernExpr.ofSExp (f' + 1) (ModernExpr.trr l x).toSExp =
            (do let lv ← ModernExpr.ofSExp f' l.toSExp; let xv ← ModernExpr.ofSExp f' x.toSExp
                .ok (.trr lv xv)) := by with_unfolding_all rfl
        rw [hStep, ihf l (Nat.le_trans (Nat.le_max_left _ _) hm) hwf.1,
          ihf x (Nat.le_trans (Nat.le_max_right _ _) hm) hwf.2]; rfl
      | trl l x =>
        simp only [ModernExpr.depth, ModernExpr.wf, Bool.and_eq_true] at hd hwf
        have hm := Nat.le_of_succ_le_succ hd
        have hStep : ModernExpr.ofSExp (f' + 1) (ModernExpr.trl l x).toSExp =
            (do let lv ← ModernExpr.ofSExp f' l.toSExp; let xv ← ModernExpr.ofSExp f' x.toSExp
                .ok (.trl lv xv)) := by with_unfolding_all rfl
        rw [hStep, ihf l (Nat.le_trans (Nat.le_max_left _ _) hm) hwf.1,
          ihf x (Nat.le_trans (Nat.le_max_right _ _) hm) hwf.2]; rfl
      | liftr l x =>
        simp only [ModernExpr.depth, ModernExpr.wf, Bool.and_eq_true] at hd hwf
        have hm := Nat.le_of_succ_le_succ hd
        have hStep : ModernExpr.ofSExp (f' + 1) (ModernExpr.liftr l x).toSExp =
            (do let lv ← ModernExpr.ofSExp f' l.toSExp; let xv ← ModernExpr.ofSExp f' x.toSExp
                .ok (.liftr lv xv)) := by with_unfolding_all rfl
        rw [hStep, ihf l (Nat.le_trans (Nat.le_max_left _ _) hm) hwf.1,
          ihf x (Nat.le_trans (Nat.le_max_right _ _) hm) hwf.2]; rfl
      | liftl l x =>
        simp only [ModernExpr.depth, ModernExpr.wf, Bool.and_eq_true] at hd hwf
        have hm := Nat.le_of_succ_le_succ hd
        have hStep : ModernExpr.ofSExp (f' + 1) (ModernExpr.liftl l x).toSExp =
            (do let lv ← ModernExpr.ofSExp f' l.toSExp; let xv ← ModernExpr.ofSExp f' x.toSExp
                .ok (.liftl lv xv)) := by with_unfolding_all rfl
        rw [hStep, ihf l (Nat.le_trans (Nat.le_max_left _ _) hm) hwf.1,
          ihf x (Nat.le_trans (Nat.le_max_right _ _) hm) hwf.2]; rfl
      | sym p =>
        simp only [ModernExpr.depth, ModernExpr.wf] at hd hwf
        have hStep : ModernExpr.ofSExp (f' + 1) (ModernExpr.sym p).toSExp =
            (ModernExpr.ofSExp f' p.toSExp >>= fun pv => .ok (.sym pv)) := by with_unfolding_all rfl
        rw [hStep, ihf p (Nat.le_of_succ_le_succ hd) hwf]; rfl
      | trans p q =>
        simp only [ModernExpr.depth, ModernExpr.wf, Bool.and_eq_true] at hd hwf
        have hm := Nat.le_of_succ_le_succ hd
        have hStep : ModernExpr.ofSExp (f' + 1) (ModernExpr.trans p q).toSExp =
            (do let pv ← ModernExpr.ofSExp f' p.toSExp; let qv ← ModernExpr.ofSExp f' q.toSExp
                .ok (.trans pv qv)) := by with_unfolding_all rfl
        rw [hStep, ihf p (Nat.le_trans (Nat.le_max_left _ _) hm) hwf.1,
          ihf q (Nat.le_trans (Nat.le_max_right _ _) hm) hwf.2]; rfl
      | arrowLine d c =>
        simp only [ModernExpr.depth, ModernExpr.wf, Bool.and_eq_true] at hd hwf
        have hm := Nat.le_of_succ_le_succ hd
        have hStep : ModernExpr.ofSExp (f' + 1) (ModernExpr.arrowLine d c).toSExp =
            (do let dv ← ModernExpr.ofSExp f' d.toSExp; let cv ← ModernExpr.ofSExp f' c.toSExp
                .ok (.arrowLine dv cv)) := by with_unfolding_all rfl
        rw [hStep, ihf d (Nat.le_trans (Nat.le_max_left _ _) hm) hwf.1,
          ihf c (Nat.le_trans (Nat.le_max_right _ _) hm) hwf.2]; rfl
      | prodLine fN sN fL sL =>
        simp only [ModernExpr.depth, ModernExpr.wf, Bool.and_eq_true] at hd hwf
        have hm := Nat.le_of_succ_le_succ hd
        have hStep : ModernExpr.ofSExp (f' + 1) (ModernExpr.prodLine fN sN fL sL).toSExp =
            (do let fv ← ModernExpr.ofSExp f' fL.toSExp; let sv ← ModernExpr.ofSExp f' sL.toSExp
                .ok (.prodLine fN sN fv sv)) := by with_unfolding_all rfl
        rw [hStep, ihf fL (Nat.le_trans (Nat.le_max_left _ _) hm) hwf.1,
          ihf sL (Nat.le_trans (Nat.le_max_right _ _) hm) hwf.2]; rfl
      | boxLine mod inner =>
        simp only [ModernExpr.depth, ModernExpr.wf] at hd hwf
        have hStep : ModernExpr.ofSExp (f' + 1) (ModernExpr.boxLine mod inner).toSExp =
            (ModernExpr.ofSExp f' inner.toSExp >>= fun iv => .ok (.boxLine mod iv)) := by with_unfolding_all rfl
        rw [hStep, ihf inner (Nat.le_of_succ_le_succ hd) hwf]; rfl
      | binOp64 op l r =>
        simp only [ModernExpr.depth, ModernExpr.wf, Bool.and_eq_true] at hd hwf
        have hm := Nat.le_of_succ_le_succ hd
        have hl := ihf l (Nat.le_trans (Nat.le_max_left _ _) hm) hwf.1
        have hr := ihf r (Nat.le_trans (Nat.le_max_right _ _) hm) hwf.2
        have hStep : ModernExpr.ofSExp (f' + 1) (ModernExpr.binOp64 op l r).toSExp =
            (do let lv ← ModernExpr.ofSExp f' l.toSExp; let rv ← ModernExpr.ofSExp f' r.toSExp
                .ok (.binOp64 op lv rv)) := by
          cases op <;> with_unfolding_all rfl
        rw [hStep, hl, hr]; rfl
      | call fn args =>
        simp only [ModernExpr.depth, ModernExpr.wf, Bool.and_eq_true] at hd hwf
        rcases hwf with ⟨⟨⟨hne, hnr⟩, hfnWf⟩, hargsWf⟩
        have hm := Nat.le_of_succ_le_succ hd
        have hfnOk := ihf fn (Nat.le_trans (Nat.le_max_left _ _) hm) hfnWf
        have hargsOk := ofSExp_list_roundtrip ihf args (Nat.le_trans (Nat.le_max_right _ _) hm) hargsWf
        exact ofSExp_call_nonReserved f' fn args hne hnr hfnOk hargsOk

/-- **Landmark Theorem SYN.2 (`ofSExp_toSExp_roundtrip`, `0 sorry`)**:
    Every well-formed Modern `.narya` AST `e` roundtrips losslessly through legacy `.ny`
    S-expressions (`ModernExpr.ofSExp fuel e.toSExp = .ok e`) whenever `e.depth ≤ fuel`! -/
theorem ofSExp_toSExp_roundtrip
    (fuel : Nat) (e : ModernExpr) (hd : e.depth ≤ fuel) (hwf : e.wf = true) :
    ModernExpr.ofSExp fuel e.toSExp = .ok e :=
  ofSExp_toSExp_bounded fuel fuel (Nat.le_refl fuel) e hd hwf

/-! ## 4. Dynamic Lean-Style Extensible Syntax Templates & Soundness (`0 sorry`) -/

mutual

def substModernField (env : List (String × ModernExpr)) : ModernField → ModernField
  | .plain fn fty => .plain fn (substModernVars env fty)
  | .modal fn m fty => .modal fn m (substModernVars env fty)

def substModernTupleField (env : List (String × ModernExpr)) : ModernTupleField → ModernTupleField
  | .assign fn val => .assign fn (substModernVars env val)

def substModernList (env : List (String × ModernExpr)) : List ModernExpr → List ModernExpr
  | [] => []
  | x :: xs => substModernVars env x :: substModernList env xs

def substModernFields (env : List (String × ModernExpr)) : List ModernField → List ModernField
  | [] => []
  | f :: fs => substModernField env f :: substModernFields env fs

def substModernTupleFields (env : List (String × ModernExpr)) :
    List ModernTupleField → List ModernTupleField
  | [] => []
  | f :: fs => substModernTupleField env f :: substModernTupleFields env fs

/-- Substitute captured mixfix/operator hole arguments into a `ModernExpr` notation template. -/
def substModernVars (env : List (String × ModernExpr)) : ModernExpr → ModernExpr
  | .var ident =>
    match env.find? (fun (k, _) => k == ident) with
    | some (_, repl) => repl
    | none => .var ident
  | .succNat n => .succNat (substModernVars env n)
  | .pi x m d c =>
    let env' := env.filter (fun (k, _) => k != x)
    .pi x m (substModernVars env d) (substModernVars env' c)
  | .arrow d c => .arrow (substModernVars env d) (substModernVars env c)
  | .lamMod x m b =>
    let env' := env.filter (fun (k, _) => k != x)
    .lamMod x m (substModernVars env' b)
  | .lam x b =>
    let env' := env.filter (fun (k, _) => k != x)
    .lam x (substModernVars env' b)
  | .letIn x t v b =>
    let env' := env.filter (fun (k, _) => k != x)
    .letIn x (substModernVars env t) (substModernVars env v) (substModernVars env' b)
  | .appMod f m a => .appMod (substModernVars env f) m (substModernVars env a)
  | .boxTy m t => .boxTy m (substModernVars env t)
  | .boxIntro m s => .boxIntro m (substModernVars env s)
  | .record fs => .record (substModernFields env fs)
  | .tuple fs => .tuple (substModernTupleFields env fs)
  | .proj s f => .proj (substModernVars env s) f
  | .funext x b => .funext x (substModernVars env b)
  | .hap pf a0 a1 pa =>
    .hap (substModernVars env pf) (substModernVars env a0)
      (substModernVars env a1) (substModernVars env pa)
  | .ifz c z nz =>
    .ifz (substModernVars env c) (substModernVars env z) (substModernVars env nz)
  | .repeatU64 cnt init acc step =>
    let env' := env.filter (fun (k, _) => k != acc)
    .repeatU64 cnt (substModernVars env init) acc (substModernVars env' step)
  | .obsId t es => .obsId (substModernVars env t) (substModernList env es)
  | .obsBr t es => .obsBr (substModernVars env t) (substModernList env es)
  | .obsDisp t e0 => .obsDisp (substModernVars env t) (substModernVars env e0)
  | .obsFresh t => .obsFresh (substModernVars env t)
  | .refl s => .refl (substModernVars env s)
  | .reflDir d s => .reflDir d (substModernVars env s)
  | .glue a b r => .glue (substModernVars env a) (substModernVars env b) (substModernVars env r)
  | .gel a b r => .gel (substModernVars env a) (substModernVars env b) (substModernVars env r)
  | .trr l x => .trr (substModernVars env l) (substModernVars env x)
  | .trl l x => .trl (substModernVars env l) (substModernVars env x)
  | .liftr l x => .liftr (substModernVars env l) (substModernVars env x)
  | .liftl l x => .liftl (substModernVars env l) (substModernVars env x)
  | .sym p => .sym (substModernVars env p)
  | .trans p q => .trans (substModernVars env p) (substModernVars env q)
  | .arrowLine d c => .arrowLine (substModernVars env d) (substModernVars env c)
  | .prodLine fN sN fL sL =>
    .prodLine fN sN (substModernVars env fL) (substModernVars env sL)
  | .boxLine m i => .boxLine m (substModernVars env i)
  | .binOp64 op l r => .binOp64 op (substModernVars env l) (substModernVars env r)
  | .call fn args => .call (substModernVars env fn) (substModernList env args)
  | atomLeaf => atomLeaf

end

/-- Expand a unary `prefix`/`postfix` operator target `fnExpr` applied to `arg`. -/
def expandUnaryOp (fnExpr arg : ModernExpr) : ModernExpr :=
  match fnExpr with
  | .var "sym" => .sym arg
  | .var "refl" => .refl arg
  | .var "succ" => .succNat arg
  | .var "Fresh" => .obsFresh arg
  | _ => ModernExpr.mkCall fnExpr arg

/-- Expand a binary `infixl`/`infixr` operator target `fnExpr` applied to `(lhs, rhs)`. -/
def expandBinaryOp (fnExpr lhs rhs : ModernExpr) : ModernExpr :=
  match fnExpr with
  | .var "trans" => .trans lhs rhs
  | .var "trr" => .trr lhs rhs
  | .var "trl" => .trl lhs rhs
  | .var "arrow_line" => .arrowLine lhs rhs
  | .var s =>
    match resolveBinOp64 s with
    | some bop => .binOp64 bop lhs rhs
    | none => ModernExpr.mkCall (ModernExpr.mkCall (.var s) lhs) rhs
  | _ => ModernExpr.mkCall (ModernExpr.mkCall fnExpr lhs) rhs

/-- **Theorem SYN.3 (`infix_desugar_eq_elaborateSExp`, `0 sorry`)**:
    For any user-declared `infixl`/`infixr` operator targeting a non-reserved function `f`,
    expanding `lhs op rhs` via `expandBinaryOp (.var f) lhs rhs` and elaborating via
    `elabModernExpr` produces the **exact same `Except String Term`** as elaborating
    the legacy curried S-expression `(f lhs rhs)`! -/
theorem infix_desugar_eq_elaborateSExp
    (fuel : Nat) (T : ModeTheory) (mode : ModeId) (locals : List String)
    (f : String) (lhs rhs : ModernExpr)
    (hfAtom : isAtomKeyword f = false) (hfList : isListKeyword f = false)
    (hlWf : lhs.wf = true) (hrWf : rhs.wf = true) :
    elabModernExpr fuel T mode locals (expandBinaryOp (.var f) lhs rhs) =
      elaborateSExp fuel T mode locals (.list [.atom f, lhs.toSExp, rhs.toSExp]) := by
  have hexp : expandBinaryOp (.var f) lhs rhs = .call (.var f) [lhs, rhs] := by
    unfold expandBinaryOp
    split
    · exfalso; rename_i h; injection h with hs; subst hs; revert hfList; with_unfolding_all decide
    · exfalso; rename_i h; injection h with hs; subst hs; revert hfList; with_unfolding_all decide
    · exfalso; rename_i h; injection h with hs; subst hs; revert hfList; with_unfolding_all decide
    · exfalso; rename_i h; injection h with hs; subst hs; revert hfList; with_unfolding_all decide
    · rename_i s _ _ _ _ heq
      injection heq with hs; subst hs
      rw [resolveBinOp64_none_of_not_listKw hfList]
      rfl
    · rfl
  have hCallWf : (ModernExpr.call (.var f) [lhs, rhs]).wf = true := by
    simp [ModernExpr.wf, ModernExpr.isReservedCallHead, ModernExpr.listWf,
      hfAtom, hfList, hlWf, hrWf]
  rw [hexp, elabModernExpr_eq_elaborateSExp fuel T mode locals _ hCallWf]
  rfl

/-- **Theorem SYN.4 (`mixfix_id_desugar_eq_elaborateSExp`, `0 sorry`)**:
    Instantiating the custom mixfix notation `notation 50 a " ≡[" A "] " b => Id A a b`
    via `substModernVars` and elaborating via `elabModernExpr` produces the **exact same
    `Except String Term`** as legacy `(Id A a b)`! -/
theorem mixfix_id_desugar_eq_elaborateSExp
    (fuel : Nat) (T : ModeTheory) (mode : ModeId) (locals : List String)
    (eA ea eb : ModernExpr)
    (hAWf : eA.wf = true) (haWf : ea.wf = true) (hbWf : eb.wf = true) :
    elabModernExpr fuel T mode locals
      (substModernVars [("a", ea), ("A", eA), ("b", eb)]
        (.obsId (.var "A") [.var "a", .var "b"])) =
    elaborateSExp fuel T mode locals (.list [.atom "Id", eA.toSExp, ea.toSExp, eb.toSExp]) := by
  have hSub : substModernVars [("a", ea), ("A", eA), ("b", eb)]
      (.obsId (.var "A") [.var "a", .var "b"]) = .obsId eA [ea, eb] := by
    with_unfolding_all rfl
  have hIdWf : (ModernExpr.obsId eA [ea, eb]).wf = true := by
    simp [ModernExpr.wf, ModernExpr.listWf, hAWf, haWf, hbWf]
  rw [hSub, elabModernExpr_eq_elaborateSExp fuel T mode locals _ hIdWf]
  rfl

/-! ## 5. `.narya` Lexer, Dynamic `SyntaxEnv`, and Pratt + Mixfix Parser (`0 partial`, `0 sorry`) -/

/-- Source-positioned lexical token for `.narya` files (enabling Lean-style layout blocks). -/
structure ModTok where
  text        : String
  line        : Nat
  col         : Nat
  isStringLit : Bool := false
  deriving Repr, BEq, DecidableEq, Inhabited

private def isIdentStartChar (c : Char) : Bool :=
  c.isAlpha || c == '_' || c.val >= 0x0391 && c.val <= 0x03C9

private def isIdentContChar (c : Char) : Bool :=
  isIdentStartChar c || c.isDigit || c == '\'' || c == '?'

private def isSingleDelimChar (c : Char) : Bool :=
  c == '(' || c == ')' || c == '{' || c == '}' || c == '[' || c == ']' ||
  c == ',' || c == ';' || c == '.' || c == ':' ||
  c == '⟪' || c == '⟫' || c == '⟨' || c == '⟩' ||
  c == '⟦' || c == '⟧' || c == '«' || c == '»'

private def isSymOpChar (c : Char) : Bool :=
  c == '+' || c == '-' || c == '*' || c == '/' || c == '%' ||
  c == '&' || c == '|' || c == '^' || c == '!' || c == '~' ||
  c == '=' || c == '<' || c == '>' || c == '\\' ||
  c == '≡' || c == '≈' || c == '≅' || c == '⊕' || c == '⊗' ||
  c == '∘' || c == '∙' || c == '×' || c == '÷' || c == '≤' ||
  c == '≥' || c == '≠' || c == '↔' || c == '←' || c == '↦' ||
  c == '⊢' || c == '⊨' || c == '⇒'

private def skipLineComment : List Char → Nat → (List Char × Nat)
  | [], col => ([], col)
  | '\n' :: rest, col => ('\n' :: rest, col)
  | _ :: rest, col => skipLineComment rest (col + 1)

private def skipBlockComment : List Char → Nat → Nat → Nat → (List Char × Nat × Nat)
  | [], line, col, _ => ([], line, col)
  | '/' :: '-' :: rest, line, col, depth =>
    skipBlockComment rest line (col + 2) (depth + 1)
  | '-' :: '/' :: rest, line, col, depth =>
    if depth <= 1 then (rest, line, col + 2)
    else skipBlockComment rest line (col + 2) (depth - 1)
  | '\n' :: rest, line, _, depth =>
    skipBlockComment rest (line + 1) 1 depth
  | _ :: rest, line, col, depth =>
    skipBlockComment rest line (col + 1) depth

private def takeWhileChars (p : Char → Bool) : List Char → (List Char × List Char)
  | [] => ([], [])
  | c :: cs =>
    if p c then
      let (taken, rem) := takeWhileChars p cs
      (c :: taken, rem)
    else ([], c :: cs)

private def readStringLit : List Char → Nat → Nat → List Char → (String × List Char × Nat × Nat)
  | [], line, col, acc => (String.ofList acc.reverse, [], line, col)
  | '"' :: rest, line, col, acc => (String.ofList acc.reverse, rest, line, col + 1)
  | '\\' :: c :: rest, line, col, acc =>
    readStringLit rest line (col + 2) (c :: acc)
  | '\n' :: rest, line, _, acc =>
    readStringLit rest (line + 1) 1 ('\n' :: acc)
  | c :: rest, line, col, acc =>
    readStringLit rest line (col + 1) (c :: acc)

private def tokenizeModernLoop (fuel : Nat) (cs : List Char) (line col : Nat)
    (acc : List ModTok) : List ModTok :=
  match fuel with
  | 0 => acc.reverse
  | fuel' + 1 =>
    match cs with
    | [] => acc.reverse
    | ' ' :: rest | '\t' :: rest | '\r' :: rest =>
      tokenizeModernLoop fuel' rest line (col + 1) acc
    | '\n' :: rest =>
      tokenizeModernLoop fuel' rest (line + 1) 1 acc
    | '-' :: '-' :: rest =>
      let (rest', col') := skipLineComment rest (col + 2)
      tokenizeModernLoop fuel' rest' line col' acc
    | '/' :: '-' :: rest =>
      let (rest', line', col') := skipBlockComment rest line (col + 2) 1
      tokenizeModernLoop fuel' rest' line' col' acc
    | '@' :: '[' :: rest =>
      tokenizeModernLoop fuel' rest line (col + 2) ({ text := "@[", line, col } :: acc)
    | '□' :: '[' :: rest =>
      tokenizeModernLoop fuel' rest line (col + 2) ({ text := "□[", line, col } :: acc)
    | ':' :: '=' :: rest =>
      tokenizeModernLoop fuel' rest line (col + 2) ({ text := ":=", line, col } :: acc)
    | '=' :: '>' :: rest =>
      tokenizeModernLoop fuel' rest line (col + 2) ({ text := "=>", line, col } :: acc)
    | '-' :: '>' :: rest =>
      tokenizeModernLoop fuel' rest line (col + 2) ({ text := "->", line, col } :: acc)
    | '→' :: rest =>
      tokenizeModernLoop fuel' rest line (col + 1) ({ text := "->", line, col } :: acc)
    | '<' :: '<' :: rest =>
      tokenizeModernLoop fuel' rest line (col + 2) ({ text := "<<", line, col } :: acc)
    | '>' :: '>' :: rest =>
      tokenizeModernLoop fuel' rest line (col + 2) ({ text := ">>", line, col } :: acc)
    | '"' :: rest =>
      let (str, rest', line', col') := readStringLit rest line (col + 1) []
      tokenizeModernLoop fuel' rest' line' col'
        ({ text := str, line, col, isStringLit := true } :: acc)
    | '#' :: rest =>
      let (idChars, rest') := takeWhileChars isIdentContChar rest
      let txt := String.ofList ('#' :: idChars)
      tokenizeModernLoop fuel' rest' line (col + 1 + idChars.length)
        ({ text := txt, line, col } :: acc)
    | '?' :: rest =>
      let (digs, rest') := takeWhileChars Char.isDigit rest
      let txt := String.ofList ('?' :: digs)
      tokenizeModernLoop fuel' rest' line (col + 1 + digs.length)
        ({ text := txt, line, col } :: acc)
    | c :: rest =>
      if isSingleDelimChar c then
        tokenizeModernLoop fuel' rest line (col + 1)
          ({ text := String.singleton c, line, col } :: acc)
      else if c.isDigit then
        let (digs, rest1) := takeWhileChars Char.isDigit rest
        match rest1 with
        | 'u' :: '6' :: '4' :: rest2 | 'U' :: '6' :: '4' :: rest2 =>
          let txt := String.ofList (c :: digs) ++ "u64"
          tokenizeModernLoop fuel' rest2 line (col + 1 + digs.length + 3)
            ({ text := txt, line, col } :: acc)
        | _ =>
          let txt := String.ofList (c :: digs)
          tokenizeModernLoop fuel' rest1 line (col + 1 + digs.length)
            ({ text := txt, line, col } :: acc)
      else if isIdentStartChar c then
        let (cont, rest') := takeWhileChars isIdentContChar rest
        let txt := String.ofList (c :: cont)
        tokenizeModernLoop fuel' rest' line (col + 1 + cont.length)
          ({ text := txt, line, col } :: acc)
      else if isSymOpChar c then
        let (cont, rest') := takeWhileChars
          (fun d => isSymOpChar d) rest
        let txt := String.ofList (c :: cont)
        tokenizeModernLoop fuel' rest' line (col + 1 + cont.length)
          ({ text := txt, line, col } :: acc)
      else
        tokenizeModernLoop fuel' rest line (col + 1)
          ({ text := String.singleton c, line, col } :: acc)

/-- Tokenize `.narya` surface source with line/column coordinates and nested comments. -/
def tokenizeModern (src : String) : List ModTok :=
  let cs := src.toList
  tokenizeModernLoop (cs.length + 16) cs 1 1 []

/-- Tokenize a quoted notation chunk (e.g. `" ≡["` -> `["≡", "["]`). -/
def lexNotationChunk (chunk : String) : List String :=
  (tokenizeModern chunk).map (·.text)

/-- Item in a Lean-style mixfix `notation` rule. -/
inductive MixfixItem where
  | lit  (toks : List String)
  | hole (var : String)
  deriving Repr, BEq, DecidableEq

structure PrefixRule where
  prec   : Nat
  opToks : List String
  fnExpr : ModernExpr
  deriving Repr, BEq

structure PostfixRule where
  prec   : Nat
  opToks : List String
  fnExpr : ModernExpr
  deriving Repr, BEq

structure InfixRule where
  prec       : Nat
  rightAssoc : Bool
  opToks     : List String
  fnExpr     : ModernExpr
  deriving Repr, BEq

structure LeadingNotationRule where
  prec  : Nat
  items : List MixfixItem
  rhs   : ModernExpr
  deriving Repr, BEq

structure TrailingNotationRule where
  prec       : Nat
  rightAssoc : Bool
  leadVar    : String
  items      : List MixfixItem
  rhs        : ModernExpr
  deriving Repr, BEq

/-- Dynamic extensible grammar environment (`prefix`, `postfix`, `infixl`, `infixr`, `notation`).
    Threaded across module imports so user-declared syntax travels through package DAGs! -/
structure SyntaxEnv where
  prefixes  : List PrefixRule := []
  postfixes : List PostfixRule := []
  infixes   : List InfixRule := []
  leadings  : List LeadingNotationRule := []
  trailings : List TrailingNotationRule := []
  deriving Repr, BEq

/-- Standard `.narya` operator table: even standard 64-bit arithmetic & bitwise operators
    are ordinary `InfixRule` entries in `SyntaxEnv.standard`! -/
def SyntaxEnv.standard : SyntaxEnv where
  infixes := [
    { prec := 70, rightAssoc := false, opToks := ["*"],  fnExpr := .var "u64_mul" },
    { prec := 65, rightAssoc := false, opToks := ["+"],  fnExpr := .var "u64_add" },
    { prec := 65, rightAssoc := false, opToks := ["-"],  fnExpr := .var "u64_sub" },
    { prec := 60, rightAssoc := false, opToks := ["<<"], fnExpr := .var "u64_shl" },
    { prec := 60, rightAssoc := false, opToks := [">>"], fnExpr := .var "u64_shr" },
    { prec := 55, rightAssoc := false, opToks := ["&"],  fnExpr := .var "u64_and" },
    { prec := 52, rightAssoc := false, opToks := ["^"],  fnExpr := .var "u64_xor" },
    { prec := 50, rightAssoc := false, opToks := ["|"],  fnExpr := .var "u64_or" }
  ]

private def matchTokSeq (pat : List String) (toks : List ModTok) : Option (List ModTok) :=
  match pat, toks with
  | [], rest => some rest
  | p :: ps, t :: ts =>
    if !t.isStringLit && t.text == p then matchTokSeq ps ts else none
  | _ :: _, [] => none

private def findPrefixRule? (rules : List PrefixRule) (toks : List ModTok) :
    Option (PrefixRule × List ModTok) :=
  match rules with
  | [] => none
  | r :: rs =>
    match matchTokSeq r.opToks toks with
    | some rem => some (r, rem)
    | none => findPrefixRule? rs toks

private def findPostfixRule? (rules : List PostfixRule) (minPrec : Nat) (toks : List ModTok) :
    Option (PostfixRule × List ModTok) :=
  match rules with
  | [] => none
  | r :: rs =>
    if r.prec >= minPrec then
      match matchTokSeq r.opToks toks with
      | some rem => some (r, rem)
      | none => findPostfixRule? rs minPrec toks
    else findPostfixRule? rs minPrec toks

private def findInfixRule? (rules : List InfixRule) (minPrec : Nat) (toks : List ModTok) :
    Option (InfixRule × List ModTok) :=
  match rules with
  | [] => none
  | r :: rs =>
    if r.prec >= minPrec then
      match matchTokSeq r.opToks toks with
      | some rem => some (r, rem)
      | none => findInfixRule? rs minPrec toks
    else findInfixRule? rs minPrec toks

private def findLeadingRule? (rules : List LeadingNotationRule) (toks : List ModTok) :
    Option (LeadingNotationRule × List ModTok) :=
  match rules with
  | [] => none
  | r :: rs =>
    match r.items with
    | .lit pat :: _ =>
      match matchTokSeq pat toks with
      | some _ => some (r, toks)
      | none => findLeadingRule? rs toks
    | _ => findLeadingRule? rs toks

private def findTrailingRule? (rules : List TrailingNotationRule) (minPrec : Nat)
    (toks : List ModTok) : Option (TrailingNotationRule × List ModTok) :=
  match rules with
  | [] => none
  | r :: rs =>
    if r.prec >= minPrec then
      match r.items with
      | .lit pat :: _ =>
        match matchTokSeq pat toks with
        | some rem => some (r, rem)
        | none => findTrailingRule? rs minPrec toks
      | _ => findTrailingRule? rs minPrec toks
    else findTrailingRule? rs minPrec toks

private def isTopCmdStarterTxt (s : String) : Bool :=
  s == "import" || s == "theory" || s == "axiom" || s == "def" || s == "codef" ||
  s == "prefix" || s == "postfix" || s == "infixl" || s == "infixr" || s == "notation" ||
  s == "#check" || s == "#eval" || s == "#solve"

private def isClauseStopTxt (s : String) : Bool :=
  isTopCmdStarterTxt s ||
  s == ")" || s == "}" || s == "]" || s == "," || s == ";" ||
  s == ":=" || s == "=>" || s == "->" || s == ":" ||
  s == "then" || s == "else" || s == "from" || s == "with" || s == "in" ||
  s == "⟫" || s == "⟩" || s == "⟧" || s == "»"

private def isOffside (floorLine indentFloor : Nat) (tok : ModTok) : Bool :=
  indentFloor > 0 && tok.line > floorLine && tok.col <= indentFloor

/-- Resolve QTT semiring grades (`0`, `1`, `ω`/`omega`) to active `ModeTheory` modalities! -/
def resolveGradeModStr (T : ModeTheory) (grade : String) : String :=
  if grade == "0" then
    match T.findMod? "Ghost0" with
    | some _ => "Ghost0"
    | none => "_"
  else if grade == "1" then
    "_"
  else if grade == "ω" || grade == "omega" then
    match T.findMod? "F", T.findMod? "G" with
    | some _, some _ => "F.G"
    | _, _ => "_"
  else "_"

/-- Parse a composite modality path `F.G` up to `"]"`. -/
private def parseModBracket (toks : List ModTok) : Except String (String × List ModTok) :=
  match toks with
  | [] => .error "Unexpected EOF inside modality `[...]`"
  | first :: rest =>
    if first.text == "]" then .error s!"Empty modality `[]` at {first.line}:{first.col}"
    else
      let rec loop (fuel : Nat) (acc : String) (ts : List ModTok) :
          Except String (String × List ModTok) :=
        match fuel with
        | 0 => .error "Modality path too long"
        | f' + 1 =>
          match ts with
          | { text := "]", .. } :: rem => .ok (acc, rem)
          | { text := ".", .. } :: m :: rem => loop f' (acc ++ "." ++ m.text) rem
          | t :: _ => .error s!"Expected `]` after modality `{acc}`, got `{t.text}` at {t.line}:{t.col}"
          | [] => .error s!"Unclosed modality `[` for `{acc}`"
      loop 32 first.text rest

private def isDigitsOnly (s : String) : Bool :=
  !s.isEmpty && s.toList.all Char.isDigit

private def stripU64Suffix? (s : String) : Option String :=
  if s.endsWith "u64" && s.length > 3 then
    let numPart := (s.dropEnd 3).toString
    if isDigitsOnly numPart then some numPart else none
  else none

private def applyBuiltinHead (hd : ModernExpr) (args : List ModernExpr) : ModernExpr :=
  if args.isEmpty then hd
  else
    match hd, args with
    | .var "succ", [n] => .succNat n
    | .var "Id", ty :: ends => .obsId ty ends
    | .var "Br", ty :: ends => .obsBr ty ends
    | .var "Disp", [ty, e0] => .obsDisp ty e0
    | .var "Fresh", [ty] => .obsFresh ty
    | .var "refl", [sub] => .refl sub
    | .var "refl_dir", [.var d, sub] => .reflDir d sub
    | .var "Glue", [a, b, r] => .glue a b r
    | .var "Gel", [a, b, r] => .gel a b r
    | .var "trr", [l, x] => .trr l x
    | .var "trl", [l, x] => .trl l x
    | .var "liftr", [l, x] => .liftr l x
    | .var "liftl", [l, x] => .liftl l x
    | .var "sym", [p] => .sym p
    | .var "trans", [p, q] => .trans p q
    | .var "arrow_line", [d, c] | .var "arrowLine", [d, c] => .arrowLine d c
    | .var "prod_line", [.var fN, .var sN, fL, sL]
    | .var "prodLine", [.var fN, .var sN, fL, sL] => .prodLine fN sN fL sL
    | .var "hap", [pf, a0, a1, pa] => .hap pf a0 a1 pa
    | fn, as => .call fn as

/-- Parsed dependent binder `(name, modStr, domTy)`. -/
structure ParsedBinder where
  name   : String
  modStr : String
  dom    : ModernExpr
  deriving Repr

mutual

private def parseMixfixItems (fuel : Nat) (T : ModeTheory) (syn : SyntaxEnv)
    (rulePrec floorLine indentFloor : Nat) (stopEq : Bool)
    (items : List MixfixItem) (toks : List ModTok) :
    Except String (List (String × ModernExpr) × List ModTok) :=
  match fuel with
  | 0 => .error "Parser fuel exhausted in mixfix items"
  | fuel' + 1 =>
    match items with
    | [] => .ok ([], toks)
    | .lit pat :: rest =>
      match matchTokSeq pat toks with
      | some rem =>
        parseMixfixItems fuel' T syn rulePrec floorLine indentFloor stopEq rest rem
      | none =>
        let got := match toks with | t :: _ => s!"`{t.text}` at {t.line}:{t.col}" | [] => "EOF"
        .error s!"Expected notation literal `{String.intercalate " " pat}`, got {got}"
    | .hole v :: rest =>
      match rest with
      | .lit _ :: _ =>
        -- Delimited hole (e.g. `A` in `a " ≡[" A "] " b`): reset offside & parse at prec 0
        do
          let (arg, rem1) ← parseModernPrec fuel' T syn 0 0 0 false toks
          let (bs, rem2) ← parseMixfixItems fuel' T syn rulePrec floorLine indentFloor stopEq rest rem1
          .ok ((v, arg) :: bs, rem2)
      | _ =>
        -- Open trailing hole: parse at `rulePrec`
        do
          let (arg, rem1) ← parseModernPrec fuel' T syn rulePrec floorLine indentFloor stopEq toks
          let (bs, rem2) ← parseMixfixItems fuel' T syn rulePrec floorLine indentFloor stopEq rest rem1
          .ok ((v, arg) :: bs, rem2)

private def parseSigFields (fuel : Nat) (T : ModeTheory) (syn : SyntaxEnv)
    (toks : List ModTok) : Except String (List ModernField × List ModTok) :=
  match fuel with
  | 0 => .error "Parser fuel exhausted in `sig { ... }`"
  | fuel' + 1 =>
    match toks with
    | [] => .error "Unclosed `sig {` record type"
    | { text := "}", .. } :: rem => .ok ([], rem)
    | { text := ",", .. } :: rem | { text := ";", .. } :: rem =>
      parseSigFields fuel' T syn rem
    | fnameTok :: { text := "@[", .. } :: rest1 => do
      let (modStr, rest2) ← parseModBracket rest1
      match rest2 with
      | { text := ":", .. } :: rest3 =>
        let (fty, rest4) ← parseModernPrec fuel' T syn 0 0 0 false rest3
        let (more, rest5) ← parseSigFields fuel' T syn rest4
        .ok (.modal fnameTok.text modStr fty :: more, rest5)
      | _ => .error s!"Expected `:` after modal record field `{fnameTok.text}`"
    | fnameTok :: { text := ":", .. } :: { text := "@[", .. } :: rest1 => do
      let (modStr, rest2) ← parseModBracket rest1
      let (fty, rest3) ← parseModernPrec fuel' T syn 0 0 0 false rest2
      let (more, rest4) ← parseSigFields fuel' T syn rest3
      .ok (.modal fnameTok.text modStr fty :: more, rest4)
    | fnameTok :: { text := ":", .. } :: rest1 => do
      let (fty, rest2) ← parseModernPrec fuel' T syn 0 0 0 false rest1
      let (more, rest3) ← parseSigFields fuel' T syn rest2
      .ok (.plain fnameTok.text fty :: more, rest3)
    | t :: _ => .error s!"Invalid record field at `{t.text}` ({t.line}:{t.col})"

private def parseTupleAssigns (fuel : Nat) (T : ModeTheory) (syn : SyntaxEnv)
    (toks : List ModTok) : Except String (List ModernTupleField × List ModTok) :=
  match fuel with
  | 0 => .error "Parser fuel exhausted in `{ ... }` tuple"
  | fuel' + 1 =>
    match toks with
    | [] => .error "Unclosed `{` tuple literal"
    | { text := "}", .. } :: rem => .ok ([], rem)
    | { text := ",", .. } :: rem | { text := ";", .. } :: rem =>
      parseTupleAssigns fuel' T syn rem
    | fnameTok :: { text := ":=", .. } :: rest1 => do
      let (val, rest2) ← parseModernPrec fuel' T syn 0 0 0 false rest1
      let (more, rest3) ← parseTupleAssigns fuel' T syn rest2
      .ok (.assign fnameTok.text val :: more, rest3)
    | t :: _ => .error s!"Expected `field := expr` or `}` in tuple, got `{t.text}` ({t.line}:{t.col})"

/-- Parse a single parenthesized binder group `(x y : Dom)`, `(0 g : Dom)`, `(1 x : Dom)`,
    `(ω x : Dom)`, or `(x @[μ] : Dom)`. -/
private def parseOneParenBinderGroup (fuel : Nat) (T : ModeTheory) (syn : SyntaxEnv)
    (toks : List ModTok) : Except String (List ParsedBinder × List ModTok) :=
  match fuel with
  | 0 => .error "Parser fuel exhausted in binder group"
  | fuel' + 1 =>
    match toks with
    | { text := "(", .. } :: inner =>
      -- Check QTT grade prefix `0`, `1`, `ω`, `omega`
      let (gradeMod?, afterGrade) : (Option String × List ModTok) :=
        match inner with
        | gTok :: vTok :: rest =>
          if (gTok.text == "0" || gTok.text == "1" || gTok.text == "ω" || gTok.text == "omega") &&
             vTok.text != ":" && vTok.text != "@[" && vTok.text != ")" then
            (some (resolveGradeModStr T gTok.text), vTok :: rest)
          else (none, inner)
        | _ => (none, inner)
      -- Collect binder variable names up to `@[` or `:`
      let rec collectVars (vf : Nat) (acc : List String) (ts : List ModTok) :
          Except String (List String × Option String × List ModTok) :=
        match vf with
        | 0 => .error "Too many variables in binder group"
        | vf' + 1 =>
          match ts with
          | { text := ":", .. } :: { text := "@[", .. } :: r1 => do
            if acc.isEmpty then .error "Empty binder variable list"
            let (mStr, r2) ← parseModBracket r1
            .ok (acc.reverse, some mStr, r2)
          | { text := ":", .. } :: r1 =>
            if acc.isEmpty then .error "Empty binder variable list"
            else .ok (acc.reverse, none, r1)
          | { text := "@[", .. } :: r1 => do
            if acc.isEmpty then .error "Missing variable name before `@[...]`"
            let (mStr, r2) ← parseModBracket r1
            match r2 with
            | { text := ":", .. } :: r3 => .ok (acc.reverse, some mStr, r3)
            | _ => .error "Expected `:` after `@[...]` in binder"
          | v :: r1 =>
            if v.isStringLit || isClauseStopTxt v.text || isDigitsOnly v.text || v.text == "(" then
              .error s!"Not a binder variable `{v.text}`"
            else collectVars vf' (v.text :: acc) r1
          | [] => .error "Unclosed `(` in binder"
      do
        let (vars, explicitMod?, domToks) ← collectVars 32 [] afterGrade
        let finalMod := explicitMod?.getD (gradeMod?.getD "_")
        let (dom, afterDom) ← parseModernPrec fuel' T syn 0 0 0 false domToks
        match afterDom with
        | { text := ")", .. } :: rem =>
          .ok (vars.map (fun v => { name := v, modStr := finalMod, dom }), rem)
        | _ => .error "Expected `)` closing binder group"
    | _ => .error "Expected `(` starting binder group"

private def parseManyParenBinders (fuel : Nat) (T : ModeTheory) (syn : SyntaxEnv)
    (toks : List ModTok) : Except String (List ParsedBinder × List ModTok) :=
  match fuel with
  | 0 => .ok ([], toks)
  | fuel' + 1 =>
    match toks with
    | { text := "(", .. } :: _ =>
      match parseOneParenBinderGroup fuel' T syn toks with
      | .ok (bs, rem) => do
        let (more, rem2) ← parseManyParenBinders fuel' T syn rem
        .ok (bs ++ more, rem2)
      | .error _ => .ok ([], toks)
    | _ => .ok ([], toks)

private def parseFunParams (fuel : Nat) (T : ModeTheory) (syn : SyntaxEnv)
    (toks : List ModTok) : Except String (List (String × String) × List ModTok) :=
  match fuel with
  | 0 => .error "Parser fuel exhausted in `fun` parameters"
  | fuel' + 1 =>
    match toks with
    | { text := "=>", .. } :: rem => .ok ([], rem)
    | { text := "(", .. } :: inner =>
      -- Either a typed/graded binder group `(0 g : A)` / `(x @[μ] : A)` or untyped `(x @[μ])`
      match parseOneParenBinderGroup fuel' T syn toks with
      | .ok (bs, rem1) => do
        let (more, rem2) ← parseFunParams fuel' T syn rem1
        .ok (bs.map (fun b => (b.name, b.modStr)) ++ more, rem2)
      | .error _ =>
        match inner with
        | vTok :: { text := "@[", .. } :: r1 => do
          let (mStr, r2) ← parseModBracket r1
          match r2 with
          | { text := ")", .. } :: rem1 =>
            let (more, rem2) ← parseFunParams fuel' T syn rem1
            .ok ((vTok.text, mStr) :: more, rem2)
          | _ => .error s!"Expected `)` after `({vTok.text} @[{mStr}]`"
        | gTok :: vTok :: { text := ")", .. } :: rem1 => do
          let mStr := resolveGradeModStr T gTok.text
          let (more, rem2) ← parseFunParams fuel' T syn rem1
          .ok ((vTok.text, mStr) :: more, rem2)
        | _ => .error "Invalid parameter in `fun`"
    | vTok :: rem1 =>
      if vTok.isStringLit || isClauseStopTxt vTok.text then
        .error s!"Expected parameter or `=>` in `fun`, got `{vTok.text}` ({vTok.line}:{vTok.col})"
      else do
        let (more, rem2) ← parseFunParams fuel' T syn rem1
        .ok ((vTok.text, "_") :: more, rem2)
    | [] => .error "Unexpected EOF in `fun` before `=>`"

private def parsePostfixProjLoop (e : ModernExpr) (toks : List ModTok) :
    (ModernExpr × List ModTok) :=
  match toks with
  | { text := ".", .. } :: fldTok :: rem =>
    if !fldTok.isStringLit && !isClauseStopTxt fldTok.text && fldTok.text != "." then
      parsePostfixProjLoop (.proj e fldTok.text) rem
    else (e, toks)
  | _ => (e, toks)

private def parsePrimaryAtom (fuel : Nat) (T : ModeTheory) (syn : SyntaxEnv)
    (floorLine indentFloor : Nat) (stopEq : Bool) (toks : List ModTok) :
    Except String (ModernExpr × List ModTok) :=
  match fuel with
  | 0 => .error "Parser fuel exhausted in primary atom"
  | fuel' + 1 =>
    -- 1. Check leading mixfix `notation` rules first
    match findLeadingRule? syn.leadings toks with
    | some (rule, _) => do
      let (bindings, rem) ←
        parseMixfixItems fuel' T syn rule.prec floorLine indentFloor stopEq rule.items toks
      .ok (substModernVars bindings rule.rhs, rem)
    | none =>
      -- 2. Check user/standard `prefix` rules
      match findPrefixRule? syn.prefixes toks with
      | some (prule, rem1) => do
        let (arg, rem2) ← parseModernPrec fuel' T syn prule.prec floorLine indentFloor stopEq rem1
        .ok (expandUnaryOp prule.fnExpr arg, rem2)
      | none =>
        match toks with
        | [] => .error "Unexpected EOF while parsing expression"
        | tok :: rest =>
          if tok.isStringLit then
            .error s!"Unexpected string literal `\"{tok.text}\"` at {tok.line}:{tok.col}"
          else if tok.text == "(" then
            -- Check if `( ... ) -> Cod` dependent Pi type!
            match parseManyParenBinders fuel' T syn toks with
            | .ok (bs, { text := "->", .. } :: codToks) =>
              if !bs.isEmpty then do
                let (cod, rem) ← parseModernPrec fuel' T syn 25 floorLine indentFloor stopEq codToks
                let piExpr := bs.foldr (fun b acc => .pi b.name b.modStr b.dom acc) cod
                .ok (piExpr, rem)
              else do
                let (inner, afterInner) ← parseModernPrec fuel' T syn 0 0 0 false rest
                match afterInner with
                | { text := ")", .. } :: rem => .ok (parsePostfixProjLoop inner rem)
                | t :: _ => .error s!"Expected `)`, got `{t.text}` at {t.line}:{t.col}"
                | [] => .error s!"Unclosed `(` at {tok.line}:{tok.col}"
            | _ => do
              let (inner, afterInner) ← parseModernPrec fuel' T syn 0 0 0 false rest
              match afterInner with
              | { text := ")", .. } :: rem => .ok (parsePostfixProjLoop inner rem)
              | t :: _ => .error s!"Expected `)`, got `{t.text}` at {t.line}:{t.col}"
              | [] => .error s!"Unclosed `(` at {tok.line}:{tok.col}"
          else if tok.text == "sig" then
            match rest with
            | { text := "{", .. } :: sigRest => do
              let (fs, rem) ← parseSigFields fuel' T syn sigRest
              .ok (.record fs, rem)
            | _ => .error s!"Expected `\{` after `sig` at {tok.line}:{tok.col}"
          else if tok.text == "{" then do
            let (fs, rem) ← parseTupleAssigns fuel' T syn rest
            .ok (parsePostfixProjLoop (.tuple fs) rem)
          else if tok.text == "□[" then do
            let (modStr, rem1) ← parseModBracket rest
            let (ty, rem2) ← parseModernPrec fuel' T syn 90 floorLine indentFloor stopEq rem1
            .ok (.boxTy modStr ty, rem2)
          else if tok.text == "Box" then
            match rest with
            | { text := "[", .. } :: r1 => do
              let (modStr, rem1) ← parseModBracket r1
              let (ty, rem2) ← parseModernPrec fuel' T syn 90 floorLine indentFloor stopEq rem1
              .ok (.boxTy modStr ty, rem2)
            | _ => .ok (parsePostfixProjLoop (.var "Box") rest)
          else if tok.text == "box" then
            match rest with
            | { text := "[", .. } :: r1 => do
              let (modStr, rem1) ← parseModBracket r1
              let (sub, rem2) ← parseModernPrec fuel' T syn 90 floorLine indentFloor stopEq rem1
              .ok (.boxIntro modStr sub, rem2)
            | _ => .ok (parsePostfixProjLoop (.var "box") rest)
          else if tok.text == "box_line" || tok.text == "boxLine" then
            match rest with
            | { text := "[", .. } :: r1 => do
              let (modStr, rem1) ← parseModBracket r1
              let (sub, rem2) ← parseModernPrec fuel' T syn 90 floorLine indentFloor stopEq rem1
              .ok (.boxLine modStr sub, rem2)
            | mTok :: r1 => do
              let (sub, rem2) ← parsePrimaryAtom fuel' T syn floorLine indentFloor stopEq r1
              .ok (.boxLine mTok.text sub, rem2)
            | [] => .error s!"Expected modality after `{tok.text}`"
          else if tok.text == "fun" || tok.text == "λ" then do
            let (params, bodyToks) ← parseFunParams fuel' T syn rest
            if params.isEmpty then .error s!"`fun` requires at least one parameter at {tok.line}:{tok.col}"
            else
              let (body, rem) ← parseModernPrec fuel' T syn 0 floorLine indentFloor stopEq bodyToks
              let lamExpr := params.foldr
                (fun (v, m) acc => if m == "_" then .lam v acc else .lamMod v m acc) body
              .ok (lamExpr, rem)
          else if tok.text == "funext" then
            match rest with
            | xTok :: { text := "=>", .. } :: bodyToks => do
              let (body, rem) ← parseModernPrec fuel' T syn 0 floorLine indentFloor stopEq bodyToks
              .ok (.funext xTok.text body, rem)
            | _ => .error s!"Expected `funext x => body` at {tok.line}:{tok.col}"
          else if tok.text == "let" then
            match rest with
            | xTok :: { text := ":", .. } :: tyToks => do
              let (ty, afterTy) ← parseModernPrec fuel' T syn 0 tok.line tok.col stopEq tyToks
              match afterTy with
              | { text := ":=", .. } :: valToks => do
                -- Parse `val` with offside floor `(tok.line, tok.col)` so newline at `<= let.col` ends `val`!
                let (val, afterVal) ← parseModernPrec fuel' T syn 0 tok.line tok.col stopEq valToks
                let bodyToks :=
                  match afterVal with
                  | { text := ";", .. } :: r => r
                  | { text := "in", .. } :: r => r
                  | r => r
                let (body, rem) ← parseModernPrec fuel' T syn 0 floorLine indentFloor stopEq bodyToks
                .ok (.letIn xTok.text ty val body, rem)
              | _ => .error s!"Expected `:=` in `let {xTok.text}` at {tok.line}:{tok.col}"
            | _ => .error s!"Expected `let x : Type := val` at {tok.line}:{tok.col}"
          else if tok.text == "ifz" then do
            let (c, r1) ← parseModernPrec fuel' T syn 0 0 0 false rest
            match r1 with
            | { text := "then", .. } :: r2 => do
              let (z, r3) ← parseModernPrec fuel' T syn 0 0 0 false r2
              match r3 with
              | { text := "else", .. } :: r4 => do
                let (nz, rem) ← parseModernPrec fuel' T syn 0 floorLine indentFloor stopEq r4
                .ok (.ifz c z nz, rem)
              | _ => .error s!"Expected `else` in `ifz` starting at {tok.line}:{tok.col}"
            | _ => .error s!"Expected `then` in `ifz` starting at {tok.line}:{tok.col}"
          else if tok.text == "repeat" then
            match rest with
            | cntTok :: { text := "from", .. } :: r1 => do
              let (init, r2) ← parseModernPrec fuel' T syn 0 0 0 false r1
              match r2 with
              | { text := "with", .. } :: accTok :: { text := "=>", .. } :: r3 => do
                let (step, rem) ← parseModernPrec fuel' T syn 0 floorLine indentFloor stopEq r3
                .ok (.repeatU64 cntTok.text init accTok.text step, rem)
              | _ => .error s!"Expected `with acc => step` in `repeat` at {tok.line}:{tok.col}"
            | _ => .error s!"Expected `repeat <count> from <init> with <acc> => <step>` at {tok.line}:{tok.col}"
          else if tok.text == "Type" then
            match rest with
            | lvlTok :: r1 =>
              if isDigitsOnly lvlTok.text && !isOffside floorLine indentFloor lvlTok then
                .ok (.typeU lvlTok.text, r1)
              else .ok (.typeU0, rest)
            | [] => .ok (.typeU0, [])
          else if tok.text.startsWith "?" then
            let idPart := (tok.text.drop 1).toString
            .ok (if idPart.isEmpty then .hole0 else .hole idPart, rest)
          else
            match stripU64Suffix? tok.text with
            | some numStr => .ok (.u64Lit numStr, rest)
            | none =>
              if isDigitsOnly tok.text then
                .ok (.u64Lit tok.text, rest)
              else if isClauseStopTxt tok.text || (stopEq && tok.text == "=") then
                .error s!"Unexpected token `{tok.text}` at {tok.line}:{tok.col}"
              else
                let atomExpr :=
                  match ofBuiltinAtom? tok.text with
                  | some b => b
                  | none => .var tok.text
                .ok (parsePostfixProjLoop atomExpr rest)

private def canStartArg (syn : SyntaxEnv) (floorLine indentFloor : Nat) (stopEq : Bool)
    (toks : List ModTok) : Bool :=
  match toks with
  | [] => false
  | tok :: _ =>
    if tok.isStringLit then false
    else if isOffside floorLine indentFloor tok then false
    else if isClauseStopTxt tok.text then false
    else if stopEq && tok.text == "=" then false
    else if (findInfixRule? syn.infixes 0 toks).isSome then false
    else if (findPostfixRule? syn.postfixes 0 toks).isSome then false
    else if (findTrailingRule? syn.trailings 0 toks).isSome then false
    else true

private def parseAppArgsLoop (fuel : Nat) (T : ModeTheory) (syn : SyntaxEnv)
    (floorLine indentFloor : Nat) (stopEq : Bool)
    (curHead : ModernExpr) (pendingPlain : List ModernExpr) (toks : List ModTok) :
    Except String (ModernExpr × List ModTok) :=
  match fuel with
  | 0 => .ok (applyBuiltinHead curHead pendingPlain.reverse, toks)
  | fuel' + 1 =>
    match toks with
    | t :: rest1 =>
      if t.text == "@[" && !t.isStringLit then
        if isOffside floorLine indentFloor t then
          .ok (applyBuiltinHead curHead pendingPlain.reverse, toks)
        else do
          let flushed := applyBuiltinHead curHead pendingPlain.reverse
          let (modStr, rest2) ← parseModBracket rest1
          let (arg, rest3) ← parsePrimaryAtom fuel' T syn floorLine indentFloor stopEq rest2
          parseAppArgsLoop fuel' T syn floorLine indentFloor stopEq
            (.appMod flushed modStr arg) [] rest3
      else if canStartArg syn floorLine indentFloor stopEq toks then do
        let (arg, rest1) ← parsePrimaryAtom fuel' T syn floorLine indentFloor stopEq toks
        parseAppArgsLoop fuel' T syn floorLine indentFloor stopEq
          curHead (arg :: pendingPlain) rest1
      else
        .ok (applyBuiltinHead curHead pendingPlain.reverse, toks)
    | [] =>
      .ok (applyBuiltinHead curHead pendingPlain.reverse, [])

private def parsePrattClimb (fuel : Nat) (T : ModeTheory) (syn : SyntaxEnv)
    (minPrec floorLine indentFloor : Nat) (stopEq : Bool)
    (lhs : ModernExpr) (toks : List ModTok) :
    Except String (ModernExpr × List ModTok) :=
  match fuel with
  | 0 => .ok (lhs, toks)
  | fuel' + 1 =>
    match toks with
    | [] => .ok (lhs, [])
    | nextTok :: _ =>
      if isOffside floorLine indentFloor nextTok || (stopEq && nextTok.text == "=") then
        .ok (lhs, toks)
      else
        -- 1. Check trailing mixfix `notation` rules (e.g. `a ≡[ A ] b`)
        match findTrailingRule? syn.trailings minPrec toks with
        | some (trule, _) => do
          let nextMin := if trule.rightAssoc then trule.prec else trule.prec + 1
          let (bindings, rem1) ←
            parseMixfixItems fuel' T syn nextMin floorLine indentFloor stopEq trule.items toks
          let combined := substModernVars ((trule.leadVar, lhs) :: bindings) trule.rhs
          parsePrattClimb fuel' T syn minPrec floorLine indentFloor stopEq combined rem1
        | none =>
          -- 2. Check `postfix` rules
          match findPostfixRule? syn.postfixes minPrec toks with
          | some (prule, rem1) =>
            let combined := expandUnaryOp prule.fnExpr lhs
            parsePrattClimb fuel' T syn minPrec floorLine indentFloor stopEq combined rem1
          | none =>
            -- 3. Check `infixl` / `infixr` rules
            match findInfixRule? syn.infixes minPrec toks with
            | some (irule, rem1) => do
              let nextMin := if irule.rightAssoc then irule.prec else irule.prec + 1
              let (rhs, rem2) ←
                parseModernPrec fuel' T syn nextMin floorLine indentFloor stopEq rem1
              let combined := expandBinaryOp irule.fnExpr lhs rhs
              parsePrattClimb fuel' T syn minPrec floorLine indentFloor stopEq combined rem2
            | none =>
              -- 4. Right-associative non-dependent function arrow `A -> B` at precedence 25
              if nextTok.text == "->" && 25 >= minPrec then do
                let (rhs, rem2) ←
                  parseModernPrec fuel' T syn 25 floorLine indentFloor stopEq toks.tail
                parsePrattClimb fuel' T syn minPrec floorLine indentFloor stopEq
                  (.arrow lhs rhs) rem2
              else
                .ok (lhs, toks)

/-- Parse a `.narya` expression at minimum precedence `minPrec` with layout floor `(floorLine, indentFloor)`. -/
def parseModernPrec (fuel : Nat) (T : ModeTheory) (syn : SyntaxEnv)
    (minPrec floorLine indentFloor : Nat) (stopEq : Bool) (toks : List ModTok) :
    Except String (ModernExpr × List ModTok) :=
  match fuel with
  | 0 => .error "Parser fuel exhausted"
  | fuel' + 1 => do
    let (hd, rem1) ← parsePrimaryAtom fuel' T syn floorLine indentFloor stopEq toks
    let (appExpr, rem2) ← parseAppArgsLoop fuel' T syn floorLine indentFloor stopEq hd [] rem1
    parsePrattClimb fuel' T syn minPrec floorLine indentFloor stopEq appExpr rem2

end

/-- Parse a standalone `.narya` expression string into a `ModernExpr` AST. -/
def parseModernExpr (T : ModeTheory := pureHoTT) (syn : SyntaxEnv := SyntaxEnv.standard)
    (src : String) : Except String ModernExpr := do
  let toks := tokenizeModern src
  let (e, rem) ← parseModernPrec (toks.length * 8 + 64) T syn 0 0 0 false toks
  match rem with
  | [] => .ok e
  | t :: _ => .error s!"Unexpected trailing token `{t.text}` at {t.line}:{t.col}"

/-- Parse and elaborate a standalone `.narya` expression into a kernel `Term`. -/
def parseModernTerm (G : GlobalEnv) (syn : SyntaxEnv := SyntaxEnv.standard)
    (src : String) (mode : Option ModeId := none) : Except String Term := do
  let expr ← parseModernExpr G.theory syn src
  elabModernExpr 512 G.theory (mode.getD G.theory.defaultMode) [] expr

/-! ## 6. Top-Level `.narya` Script Runner & Unified `.ny`/`.narya` Dispatcher -/

private def parseNotationItemsLoop (fuel : Nat) (toks : List ModTok) :
    Except String (List MixfixItem × List ModTok) :=
  match fuel with
  | 0 => .error "Notation pattern too long"
  | fuel' + 1 =>
    match toks with
    | [] => .error "Expected `=>` in `notation` declaration"
    | { text := "=>", isStringLit := false, .. } :: rem => .ok ([], rem)
    | tok :: rest =>
      if tok.isStringLit then
        let pat := lexNotationChunk tok.text
        if pat.isEmpty then .error s!"Empty string chunk in `notation` at {tok.line}:{tok.col}"
        else do
          let (more, rem) ← parseNotationItemsLoop fuel' rest
          .ok (.lit pat :: more, rem)
      else do
        let (more, rem) ← parseNotationItemsLoop fuel' rest
        .ok (.hole tok.text :: more, rem)

/-- Extract `import <mod>` dependencies from a `.narya` source file. -/
def extractModernImports (src : String) : Except String (List String) := do
  let toks := tokenizeModern src
  let rec loop (fuel : Nat) (ts : List ModTok) (deps : List String) : List String :=
    match fuel with
    | 0 => deps
    | f' + 1 =>
      match ts with
      | { text := "import", isStringLit := false, .. } :: modTok :: rem =>
        let m := unquoteAtom modTok.text
        let deps' := if deps.contains m then deps else deps ++ [m]
        loop f' rem deps'
      | _ :: rem => loop f' rem deps
      | [] => deps
  return loop (toks.length + 16) toks []

private def runModernCommandsLoop (fuel : Nat) (freshPrelude : Bool)
    (G : GlobalEnv) (syn : SyntaxEnv) (logs : List String) (toks : List ModTok) :
    Except String (GlobalEnv × SyntaxEnv × List String) :=
  match fuel with
  | 0 => .error "Command runner fuel exhausted"
  | fuel' + 1 =>
    match toks with
    | [] => .ok (G, syn, logs)
    | { text := ";", isStringLit := false, .. } :: rem =>
      runModernCommandsLoop fuel' freshPrelude G syn logs rem
    | cmdTok :: rest =>
      let pFuel := rest.length * 8 + 64
      if cmdTok.text == "import" then
        match rest with
        | _modTok :: rem => runModernCommandsLoop fuel' freshPrelude G syn logs rem
        | [] => .error s!"Expected module name after `import` at {cmdTok.line}:{cmdTok.col}"
      else if cmdTok.text == "theory" then
        match rest with
        | tTok :: rem =>
          match standardCatalog.find? (fun t => t.name == tTok.text) with
          | some T' =>
            if !freshPrelude && G.theory.name == T'.name then
              runModernCommandsLoop fuel' freshPrelude G syn
                (logs ++ [s!"[theory] active '{T'.name}' (default mode: {T'.defaultMode})"]) rem
            else
              runModernCommandsLoop fuel' freshPrelude (GlobalEnv.withStdPrelude T') syn
                (logs ++ [s!"[theory] switched to '{T'.name}' (default mode: {T'.defaultMode})"]) rem
          | none => .error s!"Unknown standard mode theory '{tTok.text}'"
        | [] => .error s!"Expected mode theory name after `theory` at {cmdTok.line}:{cmdTok.col}"
      else if cmdTok.text == "axiom" then
        match rest with
        | nameTok :: afterName => do
          let (bs, afterBs) ← parseManyParenBinders pFuel G.theory syn afterName
          match afterBs with
          | { text := ":", .. } :: tyToks => do
            let (retTy, rem) ←
              parseModernPrec pFuel G.theory syn 0 cmdTok.line cmdTok.col false tyToks
            let fullTyExpr := bs.foldr (fun b acc => .pi b.name b.modStr b.dom acc) retTy
            let m := G.theory.defaultMode
            let ty ← elabModernExpr 512 G.theory m [] fullTyExpr
            let (ty', u) ← synthClosed G ty
            let _ ← ensureUniverse u
            let G' := G.add (.ax nameTok.text m ty')
            runModernCommandsLoop fuel' freshPrelude G' syn
              (logs ++ [s!"[axiom] {nameTok.text} : {prettyTerm [] ty'}"]) rem
          | _ => .error s!"Expected `:` in `axiom {nameTok.text}` at {cmdTok.line}:{cmdTok.col}"
        | [] => .error s!"Expected identifier after `axiom` at {cmdTok.line}:{cmdTok.col}"
      else if cmdTok.text == "def" || cmdTok.text == "codef" then
        let isCodef := cmdTok.text == "codef"
        match rest with
        | nameTok :: afterName => do
          let (bs, afterBs) ← parseManyParenBinders pFuel G.theory syn afterName
          match afterBs with
          | { text := ":", .. } :: tyToks => do
            let (retTy, afterRet) ←
              parseModernPrec pFuel G.theory syn 0 cmdTok.line cmdTok.col false tyToks
            match afterRet with
            | { text := ":=", .. } :: bodyToks => do
              let (rawBody, rem) ←
                parseModernPrec pFuel G.theory syn 0 cmdTok.line cmdTok.col false bodyToks
              let fullTyExpr := bs.foldr (fun b acc => .pi b.name b.modStr b.dom acc) retTy
              let fullBodyExpr := bs.foldr
                (fun b acc => if b.modStr == "_" then .lam b.name acc else .lamMod b.name b.modStr acc)
                rawBody
              let m := G.theory.defaultMode
              let ty ← elabModernExpr 512 G.theory m [] fullTyExpr
              let body ← elabModernExpr 512 G.theory m [] fullBodyExpr
              if !isCodef then
                checkLinearity G.theory m body
              let G' ←
                if isCodef then addSafeCheckedDef G nameTok.text ty body .potential
                else addSafeCheckedDef G nameTok.text ty body .kinetic
              let tag := if isCodef then "codef" else "def"
              runModernCommandsLoop fuel' freshPrelude G' syn
                (logs ++ [s!"[{tag}] {nameTok.text} : {prettyTerm [] ty}"]) rem
            | _ => .error s!"Expected `:=` in `{cmdTok.text} {nameTok.text}` at {cmdTok.line}:{cmdTok.col}"
          | _ => .error s!"Expected `: ReturnType` in `{cmdTok.text} {nameTok.text}` at {cmdTok.line}:{cmdTok.col}"
        | [] => .error s!"Expected identifier after `{cmdTok.text}` at {cmdTok.line}:{cmdTok.col}"
      else if cmdTok.text == "#check" then do
        let (tmExpr, rem) ← parseModernPrec pFuel G.theory syn 0 cmdTok.line cmdTok.col false rest
        let m := G.theory.defaultMode
        let tm ← elabModernExpr 512 G.theory m [] tmExpr
        let (tm', tyVal) ← synthClosed G tm
        runModernCommandsLoop fuel' freshPrelude G syn
          (logs ++ [s!"[check] {prettyTerm [] tm'} : {prettyVal G tyVal}"]) rem
      else if cmdTok.text == "#eval" then do
        let (tmExpr, rem) ← parseModernPrec pFuel G.theory syn 0 cmdTok.line cmdTok.col false rest
        let m := G.theory.defaultMode
        let tm ← elabModernExpr 512 G.theory m [] tmExpr
        let (tm', tyVal) ← synthClosed G tm
        let nf := normalize G [] 0 tm'
        runModernCommandsLoop fuel' freshPrelude G syn
          (logs ++ [s!"[eval] {prettyTerm [] nf} : {prettyVal G tyVal}"]) rem
      else if cmdTok.text == "#solve" then
        match rest with
        | hidTok :: lhsToks => do
          let hidStr := if hidTok.text.startsWith "?" then (hidTok.text.drop 1).toString else hidTok.text
          let hid := hidStr.toNat?.getD 0
          let (lhsExpr, afterLhs) ←
            parseModernPrec pFuel G.theory syn 0 cmdTok.line cmdTok.col true lhsToks
          match afterLhs with
          | { text := "=", .. } :: rhsToks => do
            let (rhsExpr, rem) ←
              parseModernPrec pFuel G.theory syn 0 cmdTok.line cmdTok.col false rhsToks
            let m := G.theory.defaultMode
            let lhs ← elabModernExpr 512 G.theory m [] lhsExpr
            let rhs ← elabModernExpr 512 G.theory m [] rhsExpr
            let mc0 := MetaCtx.empty.addUnsolved hid (.uu 0) 0
            match unifyTerms G mc0 0 lhs rhs with
            | .equal mc1 =>
              let msg := match mc1.lookupSolutionTerm? hid with
                | some sol => s!"[solve] ?{hid} := {prettyTerm [] sol}"
                | none => s!"[solve] unified (no binding needed for ?{hid})"
              runModernCommandsLoop fuel' freshPrelude G syn (logs ++ [msg]) rem
            | .blocked b _ => .error s!"Unification blocked on metavariable ?{b}"
            | .notEqual => .error "Unification failed: terms are not convertible"
          | _ => .error s!"Expected `=` in `#solve` at {cmdTok.line}:{cmdTok.col}"
        | [] => .error s!"Expected hole id after `#solve` at {cmdTok.line}:{cmdTok.col}"
      else if cmdTok.text == "prefix" || cmdTok.text == "postfix" ||
              cmdTok.text == "infixl" || cmdTok.text == "infixr" then
        match rest with
        | precTok :: opTok :: { text := "=>", .. } :: rhsToks => do
          let prec ← match precTok.text.toNat? with
            | some p => .ok p
            | none => .error s!"Expected precedence number after `{cmdTok.text}`, got `{precTok.text}`"
          let opSeq := if opTok.isStringLit then lexNotationChunk opTok.text else [opTok.text]
          if opSeq.isEmpty then .error s!"Empty operator in `{cmdTok.text}`"
          else do
            let (fnExpr, rem) ←
              parseModernPrec pFuel G.theory syn 0 cmdTok.line cmdTok.col false rhsToks
            let syn' :=
              if cmdTok.text == "prefix" then
                { syn with prefixes := { prec, opToks := opSeq, fnExpr } :: syn.prefixes }
              else if cmdTok.text == "postfix" then
                { syn with postfixes := { prec, opToks := opSeq, fnExpr } :: syn.postfixes }
              else
                let rightAssoc := cmdTok.text == "infixr"
                { syn with infixes := { prec, rightAssoc, opToks := opSeq, fnExpr } :: syn.infixes }
            let opDisp := String.intercalate "" opSeq
            runModernCommandsLoop fuel' freshPrelude G syn'
              (logs ++ [s!"[syntax] registered {cmdTok.text} {prec} \"{opDisp}\""]) rem
        | _ => .error s!"Expected `{cmdTok.text} <prec> \"<op>\" => <fn>` at {cmdTok.line}:{cmdTok.col}"
      else if cmdTok.text == "notation" then
        match rest with
        | precTok :: patToks => do
          let prec ← match precTok.text.toNat? with
            | some p => .ok p
            | none => .error s!"Expected precedence number after `notation`, got `{precTok.text}`"
          let (items, rhsToks) ← parseNotationItemsLoop (patToks.length + 4) patToks
          let (rhs, rem) ←
            parseModernPrec pFuel G.theory syn 0 cmdTok.line cmdTok.col false rhsToks
          match items with
          | .lit _ :: _ =>
            let syn' := { syn with leadings := { prec, items, rhs } :: syn.leadings }
            runModernCommandsLoop fuel' freshPrelude G syn'
              (logs ++ [s!"[syntax] registered leading notation (prec {prec})"]) rem
          | .hole leadVar :: (.lit _ :: _) =>
            let tailItems := items.tail
            let syn' := { syn with
              trailings := { prec, rightAssoc := false, leadVar, items := tailItems, rhs } :: syn.trailings }
            runModernCommandsLoop fuel' freshPrelude G syn'
              (logs ++ [s!"[syntax] registered trailing mixfix notation (prec {prec})"]) rem
          | _ => .error s!"`notation` must start with `\"lit\"` or `<var> \"lit\" ...` at {cmdTok.line}:{cmdTok.col}"
        | [] => .error s!"Invalid `notation` at {cmdTok.line}:{cmdTok.col}"
      else
        .error s!"Unrecognized top-level `.narya` command `{cmdTok.text}` at {cmdTok.line}:{cmdTok.col}"

/-- Execute a `.narya` script starting from existing `(G0, syn0)` state, returning
    updated `(GlobalEnv × SyntaxEnv × List String)`. -/
def runModernScriptWithEnv (G0 : GlobalEnv) (syn0 : SyntaxEnv := SyntaxEnv.standard)
    (src : String) : Except String (GlobalEnv × SyntaxEnv × List String) := do
  let toks := tokenizeModern src
  runModernCommandsLoop (toks.length + 32) false G0 syn0 [] toks

/-- Execute a standalone `.narya` script from a fresh `initTheory` prelude. -/
def runModernScript (initTheory : ModeTheory := pureHoTT) (src : String) :
    Except String (GlobalEnv × List String) := do
  let toks := tokenizeModern src
  let (G, _, logs) ←
    runModernCommandsLoop (toks.length + 32) true (GlobalEnv.withStdPrelude initTheory) SyntaxEnv.standard [] toks
  return (G, logs)

/-- Auto-detect whether `src` uses modern `.narya` syntax (`true`) or legacy Lisp `.ny` (`false`). -/
def isModernSource (src : String) : Bool :=
  match tokenizeModern src with
  | { text := "(", isStringLit := false, .. } :: _ => false
  | _ => true

/-- Unified import extractor supporting both `.narya` and `.ny` source files! -/
def extractAnyImports (src : String) : Except String (List String) :=
  if isModernSource src then extractModernImports src else extractImports src

/-- Unified script runner threading both `GlobalEnv` and `SyntaxEnv` across mixed `.narya`/`.ny` DAGs! -/
def runAnyScriptWithEnv (G0 : GlobalEnv) (syn0 : SyntaxEnv := SyntaxEnv.standard)
    (src : String) : Except String (GlobalEnv × SyntaxEnv × List String) :=
  if isModernSource src then
    runModernScriptWithEnv G0 syn0 src
  else do
    let (G1, logs) ← runScriptWithEnv G0 src
    return (G1, syn0, logs)

/-- Unified standalone script runner supporting both `.narya` and `.ny` files! -/
def runAnyScript (initTheory : ModeTheory := pureHoTT) (src : String) :
    Except String (GlobalEnv × List String) :=
  if isModernSource src then runModernScript initTheory src else runScript initTheory src

/-- Unified single-expression parser supporting both `.narya` and `.ny`! -/
def parseAnyTerm (G : GlobalEnv) (syn : SyntaxEnv := SyntaxEnv.standard)
    (src : String) (mode : Option ModeId := none) : Except String Term :=
  if isModernSource src then parseModernTerm G syn src mode else parseTerm G src mode

/-! ## 7. Idiomatic `.narya` Pretty-Printer & `.ny → .narya` Source Translator -/

private def binOpSymAndPrec : BinOp64 → (String × Nat)
  | .mul    => ("*", 70)
  | .add    => ("+", 65)
  | .sub    => ("-", 65)
  | .shl    => ("<<", 60)
  | .shr    => (">>", 60)
  | .bitAnd => ("&", 55)
  | .bitXor => ("^", 52)
  | .bitOr  => ("|", 50)

private def wrapParensIf (cond : Bool) (s : String) : String :=
  if cond then s!"({s})" else s

mutual

private def prettyModernField (fuel : Nat) : ModernField → String
  | .plain fn fty => s!"{fn} : {prettyModernPrec fuel 0 fty}"
  | .modal fn m fty => s!"{fn} @[{m}] : {prettyModernPrec fuel 0 fty}"

private def prettyModernFields (fuel : Nat) : List ModernField → String
  | [] => ""
  | [f] => prettyModernField fuel f
  | f :: fs => prettyModernField fuel f ++ ", " ++ prettyModernFields fuel fs

private def prettyModernTupleField (fuel : Nat) : ModernTupleField → String
  | .assign fn val => s!"{fn} := {prettyModernPrec fuel 0 val}"

private def prettyModernTupleFields (fuel : Nat) : List ModernTupleField → String
  | [] => ""
  | [f] => prettyModernTupleField fuel f
  | f :: fs => prettyModernTupleField fuel f ++ ", " ++ prettyModernTupleFields fuel fs

private def prettyModernAtomList (fuel : Nat) : List ModernExpr → String
  | [] => ""
  | [x] => prettyModernPrec fuel 105 x
  | x :: xs => prettyModernPrec fuel 105 x ++ " " ++ prettyModernAtomList fuel xs

/-- Pretty-print a `ModernExpr` as clean, Lisp-free `.narya` code at outer precedence `ctxPrec`. -/
def prettyModernPrec (fuel ctxPrec : Nat) (e : ModernExpr) : String :=
  match fuel with
  | 0 => "..."
  | f' + 1 =>
    match e with
    | .typeU0 => "Type"
    | .typeU1 => "Type1"
    | .typeExt => "Type_ext"
    | .natTy => "Nat"
    | .zeroNat => "zero"
    | .boolTy => "Bool"
    | .trueBool => "true"
    | .falseBool => "false"
    | .unitTy => "Unit"
    | .ttUnit => "tt"
    | .emptyTy => "Empty"
    | .u64Ty => "U64"
    | .hole0 => "?"
    | .var ident => ident
    | .u64Lit numStr => s!"{numStr}u64"
    | .hole idStr => s!"?{idStr}"
    | .typeU lvlStr => wrapParensIf (ctxPrec > 100) s!"Type {lvlStr}"
    | .succNat n => wrapParensIf (ctxPrec > 100) s!"succ {prettyModernPrec f' 105 n}"
    | .pi x "_" dom cod =>
      wrapParensIf (ctxPrec > 25) s!"({x} : {prettyModernPrec f' 0 dom}) -> {prettyModernPrec f' 25 cod}"
    | .pi x modStr dom cod =>
      wrapParensIf (ctxPrec > 25)
        s!"({x} @[{modStr}] : {prettyModernPrec f' 0 dom}) -> {prettyModernPrec f' 25 cod}"
    | .arrow dom cod =>
      wrapParensIf (ctxPrec > 25) s!"{prettyModernPrec f' 26 dom} -> {prettyModernPrec f' 25 cod}"
    | .lam x body =>
      wrapParensIf (ctxPrec > 0) s!"fun {x} => {prettyModernPrec f' 0 body}"
    | .lamMod x "_" body =>
      wrapParensIf (ctxPrec > 0) s!"fun {x} => {prettyModernPrec f' 0 body}"
    | .lamMod x modStr body =>
      wrapParensIf (ctxPrec > 0) s!"fun ({x} @[{modStr}]) => {prettyModernPrec f' 0 body}"
    | .letIn x ty val body =>
      wrapParensIf (ctxPrec > 0)
        s!"let {x} : {prettyModernPrec f' 0 ty} := {prettyModernPrec f' 0 val}; {prettyModernPrec f' 0 body}"
    | .appMod fn modStr arg =>
      wrapParensIf (ctxPrec > 100)
        s!"{prettyModernPrec f' 100 fn} @[{modStr}] {prettyModernPrec f' 105 arg}"
    | .boxTy modStr ty =>
      wrapParensIf (ctxPrec > 90) s!"□[{modStr}] {prettyModernPrec f' 90 ty}"
    | .boxIntro modStr sub =>
      wrapParensIf (ctxPrec > 90) s!"box[{modStr}] {prettyModernPrec f' 90 sub}"
    | .record fs =>
      if fs.isEmpty then "sig {}" else s!"sig \{ {prettyModernFields f' fs} }"
    | .tuple fs =>
      if fs.isEmpty then "{}" else s!"\{ {prettyModernTupleFields f' fs} }"
    | .proj sub fld => s!"{prettyModernPrec f' 110 sub}.{fld}"
    | .funext x body =>
      wrapParensIf (ctxPrec > 0) s!"funext {x} => {prettyModernPrec f' 0 body}"
    | .hap pf a0 a1 pa =>
      wrapParensIf (ctxPrec > 100)
        s!"hap {prettyModernPrec f' 105 pf} {prettyModernPrec f' 105 a0} {prettyModernPrec f' 105 a1} {prettyModernPrec f' 105 pa}"
    | .ifz c z nz =>
      wrapParensIf (ctxPrec > 0)
        s!"ifz {prettyModernPrec f' 0 c} then {prettyModernPrec f' 0 z} else {prettyModernPrec f' 0 nz}"
    | .repeatU64 cnt init acc step =>
      wrapParensIf (ctxPrec > 0)
        s!"repeat {cnt} from {prettyModernPrec f' 0 init} with {acc} => {prettyModernPrec f' 0 step}"
    | .obsId ty ends =>
      wrapParensIf (ctxPrec > 100)
        s!"Id {prettyModernPrec f' 105 ty} {prettyModernAtomList f' ends}"
    | .obsBr ty ends =>
      wrapParensIf (ctxPrec > 100)
        s!"Br {prettyModernPrec f' 105 ty} {prettyModernAtomList f' ends}"
    | .obsDisp ty e0 =>
      wrapParensIf (ctxPrec > 100)
        s!"Disp {prettyModernPrec f' 105 ty} {prettyModernPrec f' 105 e0}"
    | .obsFresh ty =>
      wrapParensIf (ctxPrec > 100) s!"Fresh {prettyModernPrec f' 105 ty}"
    | .refl sub =>
      wrapParensIf (ctxPrec > 100) s!"refl {prettyModernPrec f' 105 sub}"
    | .reflDir d sub =>
      wrapParensIf (ctxPrec > 100) s!"refl_dir {d} {prettyModernPrec f' 105 sub}"
    | .glue a b r =>
      wrapParensIf (ctxPrec > 100)
        s!"Glue {prettyModernPrec f' 105 a} {prettyModernPrec f' 105 b} {prettyModernPrec f' 105 r}"
    | .gel a b r =>
      wrapParensIf (ctxPrec > 100)
        s!"Gel {prettyModernPrec f' 105 a} {prettyModernPrec f' 105 b} {prettyModernPrec f' 105 r}"
    | .trr l x =>
      wrapParensIf (ctxPrec > 100) s!"trr {prettyModernPrec f' 105 l} {prettyModernPrec f' 105 x}"
    | .trl l x =>
      wrapParensIf (ctxPrec > 100) s!"trl {prettyModernPrec f' 105 l} {prettyModernPrec f' 105 x}"
    | .liftr l x =>
      wrapParensIf (ctxPrec > 100) s!"liftr {prettyModernPrec f' 105 l} {prettyModernPrec f' 105 x}"
    | .liftl l x =>
      wrapParensIf (ctxPrec > 100) s!"liftl {prettyModernPrec f' 105 l} {prettyModernPrec f' 105 x}"
    | .sym p =>
      wrapParensIf (ctxPrec > 100) s!"sym {prettyModernPrec f' 105 p}"
    | .trans p q =>
      wrapParensIf (ctxPrec > 100) s!"trans {prettyModernPrec f' 105 p} {prettyModernPrec f' 105 q}"
    | .arrowLine d c =>
      wrapParensIf (ctxPrec > 100) s!"arrow_line {prettyModernPrec f' 105 d} {prettyModernPrec f' 105 c}"
    | .prodLine fN sN fL sL =>
      wrapParensIf (ctxPrec > 100)
        s!"prod_line {fN} {sN} {prettyModernPrec f' 105 fL} {prettyModernPrec f' 105 sL}"
    | .boxLine m i =>
      wrapParensIf (ctxPrec > 90) s!"box_line[{m}] {prettyModernPrec f' 90 i}"
    | .binOp64 op l r =>
      let (sym, prec) := binOpSymAndPrec op
      wrapParensIf (ctxPrec > prec)
        s!"{prettyModernPrec f' prec l} {sym} {prettyModernPrec f' (prec + 1) r}"
    | .call fn args =>
      wrapParensIf (ctxPrec > 100)
        s!"{prettyModernPrec f' 100 fn} {prettyModernAtomList f' args}"

end

/-- Pretty-print a `ModernExpr` as clean `.narya` syntax. -/
def ModernExpr.pretty (e : ModernExpr) : String :=
  prettyModernPrec (e.depth + 32) 0 e

mutual

private def sexpMentionsAtom (target : String) : SExp → Bool
  | .atom s => s == target
  | .list xs => sexpListMentionsAtom target xs

private def sexpListMentionsAtom (target : String) : List SExp → Bool
  | [] => false
  | x :: xs => sexpMentionsAtom target x || sexpListMentionsAtom target xs

end

/-- Peel matching leading `pi`/`arrow` + `lam`/`lamMod` binders into idiomatic
    `def f (x : A) (y @[L] : B) : Ret := body` headers! -/
private def peelDefBinders : ModernExpr → ModernExpr → (List String × ModernExpr × ModernExpr)
  | .pi pName modStr dom cod, .lam v body =>
    if pName == v then
      let (more, rTy, rBody) := peelDefBinders cod body
      let bStr := if modStr == "_" then s!"({v} : {dom.pretty})" else s!"({v} @[{modStr}] : {dom.pretty})"
      (bStr :: more, rTy, rBody)
    else ([], .pi pName modStr dom cod, .lam v body)
  | .pi pName modStr dom cod, .lamMod v m2 body =>
    if pName == v && modStr == m2 then
      let (more, rTy, rBody) := peelDefBinders cod body
      let bStr := if modStr == "_" then s!"({v} : {dom.pretty})" else s!"({v} @[{modStr}] : {dom.pretty})"
      (bStr :: more, rTy, rBody)
    else ([], .pi pName modStr dom cod, .lamMod v m2 body)
  | .arrow dom cod, .lam v body =>
    if v == "_" || sexpMentionsAtom v cod.toSExp then
      ([], .arrow dom cod, .lam v body)
    else
      let (more, rTy, rBody) := peelDefBinders cod body
      (s!"({v} : {dom.pretty})" :: more, rTy, rBody)
  | ty, body => ([], ty, body)

/-- Automatically translate any legacy Lisp `.ny` source file into idiomatic `.narya` syntax! -/
def translateNyToModern (nySrc : String) : Except String String := do
  let toks := tokenize nySrc
  let (forms, rem) ← parseSExps (toks.length + 32) toks
  if !rem.isEmpty then .error s!"Trailing tokens in .ny source: {rem}"
  let mut outLines : List String := []
  for form in forms do
    match form with
    | .list [.atom "import", .atom modName] =>
      outLines := outLines ++ [s!"import {unquoteAtom modName}"]
    | .list [.atom "theory", .atom tName] =>
      outLines := outLines ++ [s!"theory {tName}"]
    | .list [.atom "axiom", .atom name, tyExp] =>
      let ty ← ModernExpr.ofSExp 512 tyExp
      outLines := outLines ++ [s!"axiom {name} : {ty.pretty}"]
    | .list [.atom "def", .atom name, tyExp, bodyExp] =>
      let ty ← ModernExpr.ofSExp 512 tyExp
      let body ← ModernExpr.ofSExp 512 bodyExp
      let (bStrs, retTy, innerBody) := peelDefBinders ty body
      let params := if bStrs.isEmpty then "" else " " ++ String.intercalate " " bStrs
      outLines := outLines ++ [s!"def {name}{params} : {retTy.pretty} :=\n  {innerBody.pretty}"]
    | .list [.atom "codef", .atom name, tyExp, bodyExp] =>
      let ty ← ModernExpr.ofSExp 512 tyExp
      let body ← ModernExpr.ofSExp 512 bodyExp
      let (bStrs, retTy, innerBody) := peelDefBinders ty body
      let params := if bStrs.isEmpty then "" else " " ++ String.intercalate " " bStrs
      outLines := outLines ++ [s!"codef {name}{params} : {retTy.pretty} :=\n  {innerBody.pretty}"]
    | .list [.atom "check", tmExp] =>
      let tm ← ModernExpr.ofSExp 512 tmExp
      outLines := outLines ++ [s!"#check {tm.pretty}"]
    | .list [.atom "eval", tmExp] =>
      let tm ← ModernExpr.ofSExp 512 tmExp
      outLines := outLines ++ [s!"#eval {tm.pretty}"]
    | .list [.atom "solve", .atom hid, lhsExp, rhsExp] =>
      let lhs ← ModernExpr.ofSExp 512 lhsExp
      let rhs ← ModernExpr.ofSExp 512 rhsExp
      outLines := outLines ++ [s!"#solve ?{hid} {lhs.pretty} = {rhs.pretty}"]
    | other =>
      throw s!"Unsupported top-level .ny form for translation: {reprStr other}"
  return String.intercalate "\n\n" outLines ++ "\n"

end Narya.Syntax
