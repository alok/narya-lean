/-
  Narya.Meta.ContentHash — Unison-Style Content-Addressed AST, Proof & Hardware ABI Hashing

  Combines Unison's content-addressed source model (designed for zero-conflict agentic AI
  refactoring and surgical proof caching) with Higher Observational Type Theory & `ThinEmitter`:

  1. **Nameless De Bruijn + `#hash`-Resolved Structural Hashing (`termContentHash`)**:
     - Bound variable names (`x` in `Π`, `λ`, `let`, `letBox`, `piLine`) are **completely erased**
       before hashing — cosmetic binder renamings never alter a term's hash!
     - Global references `.global g` hash via the target declaration's structural `#implHash`
       in `HashEnv`, NOT the identifier string `g` — renaming an upstream definition + updating
       call sites leaves every downstream proof and program hash invariant!
  2. **Three-Tier `DefDigest` (`specHash`, `implHash`, `abiHash`)**:
     - `specHash`: Content address of `(mode, energy, ty)` — the **Theorem / Type Specification**!
     - `implHash`: Content address of `(mode, energy, ty, body)` — the **Definitional Implementation**!
     - `abiHash` : Content address of raw ARMv8-A machine-code bytes (`thinCompileCore body`) when
       `ErasableCore [] body` holds — the **Hardware Execution Digest**!
  3. **Machine-Checked Invariance Theorems (`0 sorry`, `0 noncomputable`)**:
     - `termContentHash_alpha_invariant` (`CH.1`): Deep arbitrary α-renaming preserves hashes.
     - `global_rename_preserves_contentHash` (`CH.2`): Simultaneous α-renaming + global identifier
       refactoring preserves hashes whenever target `#implHash`es match.
     - `modern_and_legacy_same_contentHash` (`CH.3`): Modern `.narya` (`elabModernExpr`) and legacy
       Lisp `.ny` (`elaborateSExp`) produce **identical** Unison content hashes!
     - `same_erasure_same_abiHash` (`CH.4`): Any two terms with identical `HIR.eraseFromCore`
       produce identical 64-bit hardware `abiHash`es!
-/
import Narya.Syntax.Modern
import Narya.Fast.Arena
import Narya.Compiler.ThinEmitter

namespace Narya.Meta

open Narya.Dim Narya.Modal Narya.Core Narya.Syntax Narya.Fast Narya.Compiler Narya.Compiler.ThinEmitter

/-! ## 1. Content-Addressed `HashEnv` & Byte Hashing Primitives -/

/-- Maps global declaration names to their canonical 64-bit Unison `#implHash`. -/
abbrev HashEnv := List (String × UInt64)

/-- Look up a global constant's canonical 64-bit `#implHash` in `env`, falling back to
    a deterministic domain-separated seed for built-in prelude constructors/types. -/
def lookupGlobalHash (env : HashEnv) (name : String) : UInt64 :=
  match env.find? (fun (k, _) => k == name) with
  | some (_, h) => h
  | none => hashPair64 0x554E49534F4E5F47 (fnv1a64 name)

/-- Deterministic 64-bit FNV-1a + SplitMix64 digest over raw machine-code `ByteArray`s. -/
def byteArrayHash64 (ba : ByteArray) : UInt64 :=
  let raw := ba.foldl (init := (0xcbf29ce484222325 : UInt64)) fun h b =>
    (h ^^^ b.toUInt64) * 0x100000001b3
  hashPair64 0x41524D3634414249 raw

/-- Format a 64-bit digest as a 12-hex-digit Unison hash badge `#xxxxxxxxxxxx`. -/
def formatUnisonShortHex (h : UInt64) : String := Id.run do
  let hexChars := #['0','1','2','3','4','5','6','7','8','9','a','b','c','d','e','f']
  let mut chars : List Char := []
  let mut v := h
  for _ in [:12] do
    let nib := (v &&& 0xF).toNat
    chars := (hexChars[nib]?.getD '0') :: chars
    v := v >>> 4
  return "#" ++ String.ofList chars

/-- Format a full 16-hex-digit 64-bit hash string. -/
def formatHex64 (h : UInt64) : String := Id.run do
  let hexChars := #['0','1','2','3','4','5','6','7','8','9','a','b','c','d','e','f']
  let mut chars : List Char := []
  let mut v := h
  for _ in [:16] do
    let nib := (v &&& 0xF).toNat
    chars := (hexChars[nib]?.getD '0') :: chars
    v := v >>> 4
  return String.ofList chars

@[inline] private def hMod (mp : ModPath) : UInt64 := fnv1a64 (reprStr mp)
@[inline] private def hDir (g : Dir) : UInt64 := fnv1a64 (reprStr g)
@[inline] private def hCell (c : TwoCellExpr) : UInt64 := fnv1a64 (reprStr c)
@[inline] private def hBinOp (op : BinOp64) : UInt64 := fnv1a64 op.name
@[inline] private def hEnergy (e : Energy) : UInt64 :=
  match e with | .kinetic => 0x4B494E | .potential => 0x504F54

/-! ## 2. Nameless Structural `termContentHash` (Erasing Cosmetic Binder Names!) -/

mutual

def termListContentHash (env : HashEnv) : List Term → UInt64
  | [] => 0x4C4953545F4E494C
  | t :: ts => hashPair64 (termContentHash env t) (termListContentHash env ts)

def fieldTeleContentHash (env : HashEnv) : List (String × ModPath × Term) → UInt64
  | [] => 0x5245435F4E494C30
  | (fname, mp, fty) :: rest =>
    let hd := hashPair64 (fnv1a64 fname) (hashPair64 (hMod mp) (termContentHash env fty))
    hashPair64 hd (fieldTeleContentHash env rest)

def tupleFieldsContentHash (env : HashEnv) : List (String × Term) → UInt64
  | [] => 0x5455505F4E494C30
  | (fname, val) :: rest =>
    let hd := hashPair64 (fnv1a64 fname) (termContentHash env val)
    hashPair64 hd (tupleFieldsContentHash env rest)

def branchListContentHash (env : HashEnv) : List (String × Nat × Term) → UInt64
  | [] => 0x42525F4E494C3030
  | (cname, arity, body) :: rest =>
    let hd := hashPair64 (fnv1a64 cname) (hashPair64 arity.toUInt64 (termContentHash env body))
    hashPair64 hd (branchListContentHash env rest)

/-- Compute the Unison content-addressed 64-bit hash of a core `Term`:
    - Completely ignores cosmetic bound variable names (`_name` in `.pi`, `.lam`, `.letIn`, `.letBox`, `.piLine`)!
    - Resolves `.global g` via `lookupGlobalHash env g`! -/
def termContentHash (env : HashEnv) : Term → UInt64
  | .bvar ix => hashPair64 0x01 ix.toUInt64
  | .mvar id => hashPair64 0x02 id.toUInt64
  | .global name => hashPair64 0x03 (lookupGlobalHash env name)
  | .uu lvl => hashPair64 0x04 lvl.toUInt64
  | .uuExt lvl => hashPair64 0x05 lvl.toUInt64
  | .pi _name mod dom cod =>
    hashPair64 0x06 (hashPair64 (hMod mod)
      (hashPair64 (termContentHash env dom) (termContentHash env cod)))
  | .lam _name mod body =>
    hashPair64 0x07 (hashPair64 (hMod mod) (termContentHash env body))
  | .app fn mod arg =>
    hashPair64 0x08 (hashPair64 (hMod mod)
      (hashPair64 (termContentHash env fn) (termContentHash env arg)))
  | .letIn _name ty val body =>
    hashPair64 0x09 (hashPair64 (termContentHash env ty)
      (hashPair64 (termContentHash env val) (termContentHash env body)))
  | .key cell tm =>
    hashPair64 0x0A (hashPair64 (hCell cell) (termContentHash env tm))
  | .modalBox mod ty =>
    hashPair64 0x0B (hashPair64 (hMod mod) (termContentHash env ty))
  | .boxIntro mod tm =>
    hashPair64 0x0C (hashPair64 (hMod mod) (termContentHash env tm))
  | .letBox _name mod scrut motive body =>
    hashPair64 0x0D (hashPair64 (hMod mod)
      (hashPair64 (termContentHash env scrut)
        (hashPair64 (termContentHash env motive) (termContentHash env body))))
  | .recordTy fields =>
    hashPair64 0x0E (fieldTeleContentHash env fields)
  | .tuple fields =>
    hashPair64 0x0F (tupleFieldsContentHash env fields)
  | .proj tm fld =>
    hashPair64 0x10 (hashPair64 (termContentHash env tm) (fnv1a64 fld))
  | .dataTy dname params =>
    hashPair64 0x11 (hashPair64 (lookupGlobalHash env dname) (termListContentHash env params))
  | .ctor dname cname args =>
    hashPair64 0x12 (hashPair64 (lookupGlobalHash env dname)
      (hashPair64 (fnv1a64 cname) (termListContentHash env args)))
  | .pctor dname pname args =>
    hashPair64 0x13 (hashPair64 (lookupGlobalHash env dname)
      (hashPair64 (fnv1a64 pname) (termListContentHash env args)))
  | .matchData scrut winMod motive branches =>
    hashPair64 0x14 (hashPair64 (hMod winMod)
      (hashPair64 (termContentHash env scrut)
        (hashPair64 (termContentHash env motive) (branchListContentHash env branches))))
  | .elimHIT dname motive ptBr pathBr scrut =>
    hashPair64 0x15 (hashPair64 (lookupGlobalHash env dname)
      (hashPair64 (termContentHash env motive)
        (hashPair64 (branchListContentHash env ptBr)
          (hashPair64 (branchListContentHash env pathBr) (termContentHash env scrut)))))
  | .obsEq g ty ends =>
    hashPair64 0x16 (hashPair64 (hDir g)
      (hashPair64 (termContentHash env ty) (termListContentHash env ends)))
  | .obsHet g tyB ends =>
    hashPair64 0x17 (hashPair64 (hDir g)
      (hashPair64 (termContentHash env tyB) (termListContentHash env ends)))
  | .refl g tm =>
    hashPair64 0x18 (hashPair64 (hDir g) (termContentHash env tm))
  | .sym g p =>
    hashPair64 0x19 (hashPair64 (hDir g) (termContentHash env p))
  | .ap g fn argB =>
    hashPair64 0x1A (hashPair64 (hDir g)
      (hashPair64 (termContentHash env fn) (termContentHash env argB)))
  | .gel g tys rel =>
    hashPair64 0x1B (hashPair64 (hDir g)
      (hashPair64 (termListContentHash env tys) (termContentHash env rel)))
  | .gelIntro g ends wit =>
    hashPair64 0x1C (hashPair64 (hDir g)
      (hashPair64 (termListContentHash env ends) (termContentHash env wit)))
  | .ungel g bTm =>
    hashPair64 0x1D (hashPair64 (hDir g) (termContentHash env bTm))
  | .trr g l x =>
    hashPair64 0x1E (hashPair64 (hDir g)
      (hashPair64 (termContentHash env l) (termContentHash env x)))
  | .trl g l x =>
    hashPair64 0x1F (hashPair64 (hDir g)
      (hashPair64 (termContentHash env l) (termContentHash env x)))
  | .liftr g l x =>
    hashPair64 0x20 (hashPair64 (hDir g)
      (hashPair64 (termContentHash env l) (termContentHash env x)))
  | .liftl g l x =>
    hashPair64 0x21 (hashPair64 (hDir g)
      (hashPair64 (termContentHash env l) (termContentHash env x)))
  | .trans g p q =>
    hashPair64 0x22 (hashPair64 (hDir g)
      (hashPair64 (termContentHash env p) (termContentHash env q)))
  | .arrowLine g mod dL cL =>
    hashPair64 0x23 (hashPair64 (hDir g)
      (hashPair64 (hMod mod) (hashPair64 (termContentHash env dL) (termContentHash env cL))))
  | .piLine g _name mod dL c0 c1 cL =>
    hashPair64 0x24 (hashPair64 (hDir g)
      (hashPair64 (hMod mod)
        (hashPair64 (termContentHash env dL)
          (hashPair64 (termContentHash env c0)
            (hashPair64 (termContentHash env c1) (termContentHash env cL))))))
  | .prodLine g fN sN fL sL =>
    hashPair64 0x25 (hashPair64 (hDir g)
      (hashPair64 (hashPair64 (fnv1a64 fN) (fnv1a64 sN))
        (hashPair64 (termContentHash env fL) (termContentHash env sL))))
  | .sigLine g fN sN fM sM fL s0 s1 sL =>
    hashPair64 0x26 (hashPair64 (hDir g)
      (hashPair64 (hashPair64 (fnv1a64 fN) (fnv1a64 sN))
        (hashPair64 (hashPair64 (hMod fM) (hMod sM))
          (hashPair64 (termContentHash env fL)
            (hashPair64 (termContentHash env s0)
              (hashPair64 (termContentHash env s1) (termContentHash env sL)))))))
  | .boxLine g mod iL =>
    hashPair64 0x27 (hashPair64 (hDir g)
      (hashPair64 (hMod mod) (termContentHash env iL)))
  | .pathJ g ty base mot rCase tgt p =>
    hashPair64 0x28 (hashPair64 (hDir g)
      (hashPair64 (termContentHash env ty)
        (hashPair64 (termContentHash env base)
          (hashPair64 (termContentHash env mot)
            (hashPair64 (termContentHash env rCase)
              (hashPair64 (termContentHash env tgt) (termContentHash env p)))))))
  | .funext g mod body =>
    hashPair64 0x29 (hashPair64 (hDir g)
      (hashPair64 (hMod mod) (termContentHash env body)))
  | .hap g pf a0 a1 pa =>
    hashPair64 0x2A (hashPair64 (hDir g)
      (hashPair64 (termContentHash env pf)
        (hashPair64 (termContentHash env a0)
          (hashPair64 (termContentHash env a1) (termContentHash env pa)))))
  | .u64Ty => 0x2B55363454595045
  | .u64Lit val => hashPair64 0x2C val
  | .u64BinOp op l r =>
    hashPair64 0x2D (hashPair64 (hBinOp op)
      (hashPair64 (termContentHash env l) (termContentHash env r)))
  | .u64IfZero c z nz =>
    hashPair64 0x2E (hashPair64 (termContentHash env c)
      (hashPair64 (termContentHash env z) (termContentHash env nz)))
  | .u64Repeat iters init step =>
    hashPair64 0x2F (hashPair64 iters
      (hashPair64 (termContentHash env init) (termContentHash env step)))

end

/-! ## 3. Three-Tier Unison `DefDigest` (`specHash`, `implHash`, `abiHash`) -/

/-- Three-tier content-addressed Unison digest for a checked Narya declaration:
    - `specHash`: Content hash of `(mode, energy, ty)` (theorem / interface address)
    - `implHash`: Content hash of `(mode, energy, ty, body)` (implementation address)
    - `abiHash` : Content hash of emitted ARM64 machine code when `ErasableCore [] body`! -/
structure DefDigest where
  kind     : String       -- `"def"`, `"codef"`, or `"axiom"`
  specHash : UInt64
  implHash : UInt64
  abiHash  : Option UInt64 := none
  deriving Repr, BEq, DecidableEq, Inhabited

namespace DefDigest

def shortHex (d : DefDigest) : String :=
  formatUnisonShortHex d.implHash

def specShortHex (d : DefDigest) : String :=
  formatUnisonShortHex d.specHash

def abiShortHex? (d : DefDigest) : Option String :=
  d.abiHash.map formatUnisonShortHex

end DefDigest

/-- Compute the hardware `ABI` hash of raw `ThinEmitter` ARM64 machine code for `body`. -/
def computeRawAbiHash (body : Term) : UInt64 :=
  byteArrayHash64 (thinCompileCore body)

/-- Compute optional hardware `abiHash` for a kinetic definition when `ErasableCore [] body` holds. -/
def computeAbiHash? (energy : Energy) (body : Term) : Option UInt64 :=
  match energy with
  | .kinetic =>
    if ErasableCore [] body then some (computeRawAbiHash body) else none
  | .potential => none

private def dataSpecContentHash (env : HashEnv) (s : DataSpec) : UInt64 :=
  let hParams := termListContentHash env s.paramTys
  let hCtors := s.ctors.foldl (init := 0x43544F52) fun acc c =>
    hashPair64 acc (hashPair64 (fnv1a64 c.name) (termListContentHash env c.argTys))
  let hPCtors := s.pathCtors.foldl (init := 0x50435452) fun acc p =>
    hashPair64 acc (hashPair64 (fnv1a64 p.name)
      (hashPair64 (hDir p.dir)
        (hashPair64 (termListContentHash env p.argTys)
          (hashPair64 (termContentHash env p.lhs) (termContentHash env p.rhs)))))
  hashPair64 (fnv1a64 s.mode) (hashPair64 s.univLvl.toUInt64 (hashPair64 hParams (hashPair64 hCtors hPCtors)))

/-- Compute topological Unison `DefDigest`s for every user declaration in `G : GlobalEnv`! -/
def computeEnvDigests (G : GlobalEnv) : List (String × DefDigest) := Id.run do
  -- `G.entries` stores newest first; reverse to process in exact dependency order!
  let ordered := G.entries.reverse
  let mut hEnv : HashEnv := []
  let mut digests : List (String × DefDigest) := []
  for entry in ordered do
    match entry with
    | .ind spec =>
      let dh := dataSpecContentHash hEnv spec
      hEnv := (spec.name, dh) :: hEnv
    | .ax name mode ty =>
      let specH := hashPair64 0x4158494F4D (hashPair64 (fnv1a64 mode) (termContentHash hEnv ty))
      hEnv := (name, specH) :: hEnv
      digests := digests ++ [(name, { kind := "axiom", specHash := specH, implHash := specH, abiHash := none })]
    | .defn name mode energy ty body =>
      let specH := hashPair64 (hEnergy energy)
        (hashPair64 (fnv1a64 mode) (termContentHash hEnv ty))
      let implH := hashPair64 specH (termContentHash hEnv body)
      let abiH := computeAbiHash? energy body
      let kStr := match energy with | .kinetic => "def" | .potential => "codef"
      hEnv := (name, implH) :: hEnv
      digests := digests ++ [(name, { kind := kStr, specHash := specH, implHash := implH, abiHash := abiH })]
  return digests

/-- Render a clean Unison codebase digest table for CLI output (`narya hash` / `narya build`). -/
def renderDigestsReport (title : String) (digests : List (String × DefDigest)) : String := Id.run do
  let mut lines : Array String := #[]
  lines := lines.push s!"╔══════════════════════════════════════════════════════════════════════════════╗"
  lines := lines.push s!"║  Unison Content-Addressed Digests: {title}"
  lines := lines.push s!"╚══════════════════════════════════════════════════════════════════════════════╝"
  lines := lines.push "  Kind    Name                    Impl (#hash)     Spec (#type)     ARM64 ABI"
  lines := lines.push "  ────────────────────────────────────────────────────────────────────────────"
  for (name, d) in digests do
    let pad (s : String) (w : Nat) : String :=
      if s.length >= w then s else s ++ String.ofList (List.replicate (w - s.length) ' ')
    let abiStr := (d.abiShortHex?).getD "— (proof/HO)"
    let row :=
      "  " ++ pad d.kind 8 ++
      pad name 24 ++
      pad d.shortHex 17 ++
      pad d.specShortHex 17 ++
      abiStr
    lines := lines.push row
  return String.intercalate "\n" lines.toList

/-! ## 4. Machine-Checked Unison Hashing Invariance Theorems (`0 sorry`, `0 noncomputable`) -/

/-- Immediate root α-invariance on `λ`, `Π`, `let`, `letBox`, and `piLine`. -/
theorem termContentHash_alpha_lam (env : HashEnv) (x y : String) (m : ModPath) (b : Term) :
    termContentHash env (.lam x m b) = termContentHash env (.lam y m b) := rfl

theorem termContentHash_alpha_pi (env : HashEnv) (x y : String) (m : ModPath) (d c : Term) :
    termContentHash env (.pi x m d c) = termContentHash env (.pi y m d c) := rfl

theorem termContentHash_alpha_letIn (env : HashEnv) (x y : String) (t v b : Term) :
    termContentHash env (.letIn x t v b) = termContentHash env (.letIn y t v b) := rfl

theorem termContentHash_alpha_letBox (env : HashEnv) (x y : String) (m : ModPath) (s mot b : Term) :
    termContentHash env (.letBox x m s mot b) = termContentHash env (.letBox y m s mot b) := rfl

theorem termContentHash_alpha_piLine (env : HashEnv) (g : Dir) (x y : String)
    (m : ModPath) (dL c0 c1 cL : Term) :
    termContentHash env (.piLine g x m dL c0 c1 cL) =
      termContentHash env (.piLine g y m dL c0 c1 cL) := rfl

mutual

/-- Relational α-equivalence + global-hash-preserving refactoring between `(env₁, t₁)` and `(env₂, t₂)`:
    - Arbitrary bound-variable renamings (`x₁ ↦ x₂`) in `Π`, `λ`, `let`, `letBox`, `piLine`!
    - Arbitrary global identifier renamings (`g₁ ↦ g₂`) whenever `lookupGlobalHash env₁ g₁ = lookupGlobalHash env₂ g₂`! -/
inductive EnvRelRename (env₁ env₂ : HashEnv) : Term → Term → Prop where
  | bvar (ix : Ix) : EnvRelRename env₁ env₂ (.bvar ix) (.bvar ix)
  | mvar (id : Nat) : EnvRelRename env₁ env₂ (.mvar id) (.mvar id)
  | global {g₁ g₂ : String} (h : lookupGlobalHash env₁ g₁ = lookupGlobalHash env₂ g₂) :
      EnvRelRename env₁ env₂ (.global g₁) (.global g₂)
  | uu (l : Nat) : EnvRelRename env₁ env₂ (.uu l) (.uu l)
  | uuExt (l : Nat) : EnvRelRename env₁ env₂ (.uuExt l) (.uuExt l)
  | pi (x₁ x₂ : String) (m : ModPath) {d₁ d₂ c₁ c₂ : Term} :
      EnvRelRename env₁ env₂ d₁ d₂ → EnvRelRename env₁ env₂ c₁ c₂ →
      EnvRelRename env₁ env₂ (.pi x₁ m d₁ c₁) (.pi x₂ m d₂ c₂)
  | lam (x₁ x₂ : String) (m : ModPath) {b₁ b₂ : Term} :
      EnvRelRename env₁ env₂ b₁ b₂ →
      EnvRelRename env₁ env₂ (.lam x₁ m b₁) (.lam x₂ m b₂)
  | app (m : ModPath) {f₁ f₂ a₁ a₂ : Term} :
      EnvRelRename env₁ env₂ f₁ f₂ → EnvRelRename env₁ env₂ a₁ a₂ →
      EnvRelRename env₁ env₂ (.app f₁ m a₁) (.app f₂ m a₂)
  | letIn (x₁ x₂ : String) {t₁ t₂ v₁ v₂ b₁ b₂ : Term} :
      EnvRelRename env₁ env₂ t₁ t₂ → EnvRelRename env₁ env₂ v₁ v₂ → EnvRelRename env₁ env₂ b₁ b₂ →
      EnvRelRename env₁ env₂ (.letIn x₁ t₁ v₁ b₁) (.letIn x₂ t₂ v₂ b₂)
  | key (c : TwoCellExpr) {t₁ t₂ : Term} :
      EnvRelRename env₁ env₂ t₁ t₂ → EnvRelRename env₁ env₂ (.key c t₁) (.key c t₂)
  | modalBox (m : ModPath) {t₁ t₂ : Term} :
      EnvRelRename env₁ env₂ t₁ t₂ → EnvRelRename env₁ env₂ (.modalBox m t₁) (.modalBox m t₂)
  | boxIntro (m : ModPath) {t₁ t₂ : Term} :
      EnvRelRename env₁ env₂ t₁ t₂ → EnvRelRename env₁ env₂ (.boxIntro m t₁) (.boxIntro m t₂)
  | letBox (x₁ x₂ : String) (m : ModPath) {s₁ s₂ mot₁ mot₂ b₁ b₂ : Term} :
      EnvRelRename env₁ env₂ s₁ s₂ → EnvRelRename env₁ env₂ mot₁ mot₂ → EnvRelRename env₁ env₂ b₁ b₂ →
      EnvRelRename env₁ env₂ (.letBox x₁ m s₁ mot₁ b₁) (.letBox x₂ m s₂ mot₂ b₂)
  | recordTy {fs₁ fs₂ : List (String × ModPath × Term)} :
      EnvRelFields env₁ env₂ fs₁ fs₂ → EnvRelRename env₁ env₂ (.recordTy fs₁) (.recordTy fs₂)
  | tuple {fs₁ fs₂ : List (String × Term)} :
      EnvRelTuple env₁ env₂ fs₁ fs₂ → EnvRelRename env₁ env₂ (.tuple fs₁) (.tuple fs₂)
  | proj (fld : String) {t₁ t₂ : Term} :
      EnvRelRename env₁ env₂ t₁ t₂ → EnvRelRename env₁ env₂ (.proj t₁ fld) (.proj t₂ fld)
  | dataTy {d₁ d₂ : String} {ps₁ ps₂ : List Term}
      (hd : lookupGlobalHash env₁ d₁ = lookupGlobalHash env₂ d₂) :
      EnvRelList env₁ env₂ ps₁ ps₂ → EnvRelRename env₁ env₂ (.dataTy d₁ ps₁) (.dataTy d₂ ps₂)
  | ctor {d₁ d₂ : String} (cname : String) {as₁ as₂ : List Term}
      (hd : lookupGlobalHash env₁ d₁ = lookupGlobalHash env₂ d₂) :
      EnvRelList env₁ env₂ as₁ as₂ → EnvRelRename env₁ env₂ (.ctor d₁ cname as₁) (.ctor d₂ cname as₂)
  | pctor {d₁ d₂ : String} (pname : String) {as₁ as₂ : List Term}
      (hd : lookupGlobalHash env₁ d₁ = lookupGlobalHash env₂ d₂) :
      EnvRelList env₁ env₂ as₁ as₂ → EnvRelRename env₁ env₂ (.pctor d₁ pname as₁) (.pctor d₂ pname as₂)
  | matchData (w : ModPath) {s₁ s₂ m₁ m₂ : Term} {bs₁ bs₂ : List (String × Nat × Term)} :
      EnvRelRename env₁ env₂ s₁ s₂ → EnvRelRename env₁ env₂ m₁ m₂ → EnvRelBranches env₁ env₂ bs₁ bs₂ →
      EnvRelRename env₁ env₂ (.matchData s₁ w m₁ bs₁) (.matchData s₂ w m₂ bs₂)
  | elimHIT {d₁ d₂ : String} {m₁ m₂ s₁ s₂ : Term}
      {pt₁ pt₂ pb₁ pb₂ : List (String × Nat × Term)}
      (hd : lookupGlobalHash env₁ d₁ = lookupGlobalHash env₂ d₂) :
      EnvRelRename env₁ env₂ m₁ m₂ → EnvRelBranches env₁ env₂ pt₁ pt₂ →
      EnvRelBranches env₁ env₂ pb₁ pb₂ → EnvRelRename env₁ env₂ s₁ s₂ →
      EnvRelRename env₁ env₂ (.elimHIT d₁ m₁ pt₁ pb₁ s₁) (.elimHIT d₂ m₂ pt₂ pb₂ s₂)
  | obsEq (g : Dir) {t₁ t₂ : Term} {es₁ es₂ : List Term} :
      EnvRelRename env₁ env₂ t₁ t₂ → EnvRelList env₁ env₂ es₁ es₂ →
      EnvRelRename env₁ env₂ (.obsEq g t₁ es₁) (.obsEq g t₂ es₂)
  | obsHet (g : Dir) {t₁ t₂ : Term} {es₁ es₂ : List Term} :
      EnvRelRename env₁ env₂ t₁ t₂ → EnvRelList env₁ env₂ es₁ es₂ →
      EnvRelRename env₁ env₂ (.obsHet g t₁ es₁) (.obsHet g t₂ es₂)
  | refl (g : Dir) {t₁ t₂ : Term} :
      EnvRelRename env₁ env₂ t₁ t₂ → EnvRelRename env₁ env₂ (.refl g t₁) (.refl g t₂)
  | sym (g : Dir) {p₁ p₂ : Term} :
      EnvRelRename env₁ env₂ p₁ p₂ → EnvRelRename env₁ env₂ (.sym g p₁) (.sym g p₂)
  | ap (g : Dir) {f₁ f₂ a₁ a₂ : Term} :
      EnvRelRename env₁ env₂ f₁ f₂ → EnvRelRename env₁ env₂ a₁ a₂ →
      EnvRelRename env₁ env₂ (.ap g f₁ a₁) (.ap g f₂ a₂)
  | gel (g : Dir) {ts₁ ts₂ : List Term} {r₁ r₂ : Term} :
      EnvRelList env₁ env₂ ts₁ ts₂ → EnvRelRename env₁ env₂ r₁ r₂ →
      EnvRelRename env₁ env₂ (.gel g ts₁ r₁) (.gel g ts₂ r₂)
  | gelIntro (g : Dir) {es₁ es₂ : List Term} {w₁ w₂ : Term} :
      EnvRelList env₁ env₂ es₁ es₂ → EnvRelRename env₁ env₂ w₁ w₂ →
      EnvRelRename env₁ env₂ (.gelIntro g es₁ w₁) (.gelIntro g es₂ w₂)
  | ungel (g : Dir) {b₁ b₂ : Term} :
      EnvRelRename env₁ env₂ b₁ b₂ → EnvRelRename env₁ env₂ (.ungel g b₁) (.ungel g b₂)
  | trr (g : Dir) {l₁ l₂ x₁ x₂ : Term} :
      EnvRelRename env₁ env₂ l₁ l₂ → EnvRelRename env₁ env₂ x₁ x₂ →
      EnvRelRename env₁ env₂ (.trr g l₁ x₁) (.trr g l₂ x₂)
  | trl (g : Dir) {l₁ l₂ x₁ x₂ : Term} :
      EnvRelRename env₁ env₂ l₁ l₂ → EnvRelRename env₁ env₂ x₁ x₂ →
      EnvRelRename env₁ env₂ (.trl g l₁ x₁) (.trl g l₂ x₂)
  | liftr (g : Dir) {l₁ l₂ x₁ x₂ : Term} :
      EnvRelRename env₁ env₂ l₁ l₂ → EnvRelRename env₁ env₂ x₁ x₂ →
      EnvRelRename env₁ env₂ (.liftr g l₁ x₁) (.liftr g l₂ x₂)
  | liftl (g : Dir) {l₁ l₂ x₁ x₂ : Term} :
      EnvRelRename env₁ env₂ l₁ l₂ → EnvRelRename env₁ env₂ x₁ x₂ →
      EnvRelRename env₁ env₂ (.liftl g l₁ x₁) (.liftl g l₂ x₂)
  | trans (g : Dir) {p₁ p₂ q₁ q₂ : Term} :
      EnvRelRename env₁ env₂ p₁ p₂ → EnvRelRename env₁ env₂ q₁ q₂ →
      EnvRelRename env₁ env₂ (.trans g p₁ q₁) (.trans g p₂ q₂)
  | arrowLine (g : Dir) (m : ModPath) {d₁ d₂ c₁ c₂ : Term} :
      EnvRelRename env₁ env₂ d₁ d₂ → EnvRelRename env₁ env₂ c₁ c₂ →
      EnvRelRename env₁ env₂ (.arrowLine g m d₁ c₁) (.arrowLine g m d₂ c₂)
  | piLine (g : Dir) (x₁ x₂ : String) (m : ModPath) {d₁ d₂ a0 b0 a1 b1 aL bL : Term} :
      EnvRelRename env₁ env₂ d₁ d₂ → EnvRelRename env₁ env₂ a0 b0 →
      EnvRelRename env₁ env₂ a1 b1 → EnvRelRename env₁ env₂ aL bL →
      EnvRelRename env₁ env₂ (.piLine g x₁ m d₁ a0 a1 aL) (.piLine g x₂ m d₂ b0 b1 bL)
  | prodLine (g : Dir) (fN sN : String) {f₁ f₂ s₁ s₂ : Term} :
      EnvRelRename env₁ env₂ f₁ f₂ → EnvRelRename env₁ env₂ s₁ s₂ →
      EnvRelRename env₁ env₂ (.prodLine g fN sN f₁ s₁) (.prodLine g fN sN f₂ s₂)
  | sigLine (g : Dir) (fN sN : String) (fM sM : ModPath) {f₁ f₂ a0 b0 a1 b1 aL bL : Term} :
      EnvRelRename env₁ env₂ f₁ f₂ → EnvRelRename env₁ env₂ a0 b0 →
      EnvRelRename env₁ env₂ a1 b1 → EnvRelRename env₁ env₂ aL bL →
      EnvRelRename env₁ env₂ (.sigLine g fN sN fM sM f₁ a0 a1 aL)
        (.sigLine g fN sN fM sM f₂ b0 b1 bL)
  | boxLine (g : Dir) (m : ModPath) {i₁ i₂ : Term} :
      EnvRelRename env₁ env₂ i₁ i₂ → EnvRelRename env₁ env₂ (.boxLine g m i₁) (.boxLine g m i₂)
  | pathJ (g : Dir) {ty₁ ty₂ b₁ b₂ m₁ m₂ r₁ r₂ tg₁ tg₂ p₁ p₂ : Term} :
      EnvRelRename env₁ env₂ ty₁ ty₂ → EnvRelRename env₁ env₂ b₁ b₂ →
      EnvRelRename env₁ env₂ m₁ m₂ → EnvRelRename env₁ env₂ r₁ r₂ →
      EnvRelRename env₁ env₂ tg₁ tg₂ → EnvRelRename env₁ env₂ p₁ p₂ →
      EnvRelRename env₁ env₂ (.pathJ g ty₁ b₁ m₁ r₁ tg₁ p₁) (.pathJ g ty₂ b₂ m₂ r₂ tg₂ p₂)
  | funext (g : Dir) (m : ModPath) {b₁ b₂ : Term} :
      EnvRelRename env₁ env₂ b₁ b₂ → EnvRelRename env₁ env₂ (.funext g m b₁) (.funext g m b₂)
  | hap (g : Dir) {pf₁ pf₂ a0₁ a0₂ a1₁ a1₂ pa₁ pa₂ : Term} :
      EnvRelRename env₁ env₂ pf₁ pf₂ → EnvRelRename env₁ env₂ a0₁ a0₂ →
      EnvRelRename env₁ env₂ a1₁ a1₂ → EnvRelRename env₁ env₂ pa₁ pa₂ →
      EnvRelRename env₁ env₂ (.hap g pf₁ a0₁ a1₁ pa₁) (.hap g pf₂ a0₂ a1₂ pa₂)
  | u64Ty : EnvRelRename env₁ env₂ .u64Ty .u64Ty
  | u64Lit (v : UInt64) : EnvRelRename env₁ env₂ (.u64Lit v) (.u64Lit v)
  | u64BinOp (op : BinOp64) {l₁ l₂ r₁ r₂ : Term} :
      EnvRelRename env₁ env₂ l₁ l₂ → EnvRelRename env₁ env₂ r₁ r₂ →
      EnvRelRename env₁ env₂ (.u64BinOp op l₁ r₁) (.u64BinOp op l₂ r₂)
  | u64IfZero {c₁ c₂ z₁ z₂ nz₁ nz₂ : Term} :
      EnvRelRename env₁ env₂ c₁ c₂ → EnvRelRename env₁ env₂ z₁ z₂ → EnvRelRename env₁ env₂ nz₁ nz₂ →
      EnvRelRename env₁ env₂ (.u64IfZero c₁ z₁ nz₁) (.u64IfZero c₂ z₂ nz₂)
  | u64Repeat (iters : UInt64) {i₁ i₂ s₁ s₂ : Term} :
      EnvRelRename env₁ env₂ i₁ i₂ → EnvRelRename env₁ env₂ s₁ s₂ →
      EnvRelRename env₁ env₂ (.u64Repeat iters i₁ s₁) (.u64Repeat iters i₂ s₂)

inductive EnvRelList (env₁ env₂ : HashEnv) : List Term → List Term → Prop where
  | nil : EnvRelList env₁ env₂ [] []
  | cons {x₁ x₂ : Term} {xs₁ xs₂ : List Term} :
      EnvRelRename env₁ env₂ x₁ x₂ → EnvRelList env₁ env₂ xs₁ xs₂ →
      EnvRelList env₁ env₂ (x₁ :: xs₁) (x₂ :: xs₂)

inductive EnvRelFields (env₁ env₂ : HashEnv) :
    List (String × ModPath × Term) → List (String × ModPath × Term) → Prop where
  | nil : EnvRelFields env₁ env₂ [] []
  | cons (fn : String) (m : ModPath) {t₁ t₂ : Term} {fs₁ fs₂ : List (String × ModPath × Term)} :
      EnvRelRename env₁ env₂ t₁ t₂ → EnvRelFields env₁ env₂ fs₁ fs₂ →
      EnvRelFields env₁ env₂ ((fn, m, t₁) :: fs₁) ((fn, m, t₂) :: fs₂)

inductive EnvRelTuple (env₁ env₂ : HashEnv) :
    List (String × Term) → List (String × Term) → Prop where
  | nil : EnvRelTuple env₁ env₂ [] []
  | cons (fn : String) {v₁ v₂ : Term} {fs₁ fs₂ : List (String × Term)} :
      EnvRelRename env₁ env₂ v₁ v₂ → EnvRelTuple env₁ env₂ fs₁ fs₂ →
      EnvRelTuple env₁ env₂ ((fn, v₁) :: fs₁) ((fn, v₂) :: fs₂)

inductive EnvRelBranches (env₁ env₂ : HashEnv) :
    List (String × Nat × Term) → List (String × Nat × Term) → Prop where
  | nil : EnvRelBranches env₁ env₂ [] []
  | cons (cn : String) (ar : Nat) {b₁ b₂ : Term} {bs₁ bs₂ : List (String × Nat × Term)} :
      EnvRelRename env₁ env₂ b₁ b₂ → EnvRelBranches env₁ env₂ bs₁ bs₂ →
      EnvRelBranches env₁ env₂ ((cn, ar, b₁) :: bs₁) ((cn, ar, b₂) :: bs₂)

end

/-- Pure α-equivalence (`AlphaEq t₁ t₂`): arbitrary deep binder-name renaming under fixed `env`. -/
abbrev AlphaEq (env : HashEnv) (t₁ t₂ : Term) : Prop :=
  EnvRelRename env env t₁ t₂

mutual

/-- **Landmark Theorem CH.2 (`global_rename_preserves_contentHash`, `0 sorry`)**:
    Simultaneous deep binder α-renaming AND global-name refactoring `g₁ ↦ g₂` (whenever
    `lookupGlobalHash env₁ g₁ = lookupGlobalHash env₂ g₂`) preserves Unison `termContentHash`! -/
theorem global_rename_preserves_contentHash {env₁ env₂ : HashEnv} :
    ∀ {t₁ t₂ : Term}, EnvRelRename env₁ env₂ t₁ t₂ →
      termContentHash env₁ t₁ = termContentHash env₂ t₂
  | _, _, .bvar _ => rfl
  | _, _, .mvar _ => rfl
  | _, _, .global h => by dsimp only [termContentHash]; rw [h]
  | _, _, .uu _ => rfl
  | _, _, .uuExt _ => rfl
  | _, _, .pi _ _ _ r1 r2 => by
    dsimp only [termContentHash]
    rw [global_rename_preserves_contentHash r1, global_rename_preserves_contentHash r2]
  | _, _, .lam _ _ _ r1 => by
    dsimp only [termContentHash]; rw [global_rename_preserves_contentHash r1]
  | _, _, .app _ r1 r2 => by
    dsimp only [termContentHash]
    rw [global_rename_preserves_contentHash r1, global_rename_preserves_contentHash r2]
  | _, _, .letIn _ _ r1 r2 r3 => by
    dsimp only [termContentHash]
    rw [global_rename_preserves_contentHash r1, global_rename_preserves_contentHash r2,
        global_rename_preserves_contentHash r3]
  | _, _, .key _ r1 => by
    dsimp only [termContentHash]; rw [global_rename_preserves_contentHash r1]
  | _, _, .modalBox _ r1 => by
    dsimp only [termContentHash]; rw [global_rename_preserves_contentHash r1]
  | _, _, .boxIntro _ r1 => by
    dsimp only [termContentHash]; rw [global_rename_preserves_contentHash r1]
  | _, _, .letBox _ _ _ r1 r2 r3 => by
    dsimp only [termContentHash]
    rw [global_rename_preserves_contentHash r1, global_rename_preserves_contentHash r2,
        global_rename_preserves_contentHash r3]
  | _, _, .recordTy rf => by
    dsimp only [termContentHash]; rw [global_rename_preserves_fields rf]
  | _, _, .tuple rf => by
    dsimp only [termContentHash]; rw [global_rename_preserves_tuple rf]
  | _, _, .proj _ r1 => by
    dsimp only [termContentHash]; rw [global_rename_preserves_contentHash r1]
  | _, _, .dataTy hd rl => by
    dsimp only [termContentHash]; rw [hd, global_rename_preserves_list rl]
  | _, _, .ctor _ hd rl => by
    dsimp only [termContentHash]; rw [hd, global_rename_preserves_list rl]
  | _, _, .pctor _ hd rl => by
    dsimp only [termContentHash]; rw [hd, global_rename_preserves_list rl]
  | _, _, .matchData _ r1 r2 rb => by
    dsimp only [termContentHash]
    rw [global_rename_preserves_contentHash r1, global_rename_preserves_contentHash r2,
        global_rename_preserves_branches rb]
  | _, _, .elimHIT hd r1 rb1 rb2 r2 => by
    dsimp only [termContentHash]
    rw [hd, global_rename_preserves_contentHash r1, global_rename_preserves_branches rb1,
        global_rename_preserves_branches rb2, global_rename_preserves_contentHash r2]
  | _, _, .obsEq _ r1 rl => by
    dsimp only [termContentHash]
    rw [global_rename_preserves_contentHash r1, global_rename_preserves_list rl]
  | _, _, .obsHet _ r1 rl => by
    dsimp only [termContentHash]
    rw [global_rename_preserves_contentHash r1, global_rename_preserves_list rl]
  | _, _, .refl _ r1 => by
    dsimp only [termContentHash]; rw [global_rename_preserves_contentHash r1]
  | _, _, .sym _ r1 => by
    dsimp only [termContentHash]; rw [global_rename_preserves_contentHash r1]
  | _, _, .ap _ r1 r2 => by
    dsimp only [termContentHash]
    rw [global_rename_preserves_contentHash r1, global_rename_preserves_contentHash r2]
  | _, _, .gel _ rl r1 => by
    dsimp only [termContentHash]
    rw [global_rename_preserves_list rl, global_rename_preserves_contentHash r1]
  | _, _, .gelIntro _ rl r1 => by
    dsimp only [termContentHash]
    rw [global_rename_preserves_list rl, global_rename_preserves_contentHash r1]
  | _, _, .ungel _ r1 => by
    dsimp only [termContentHash]; rw [global_rename_preserves_contentHash r1]
  | _, _, .trr _ r1 r2 => by
    dsimp only [termContentHash]
    rw [global_rename_preserves_contentHash r1, global_rename_preserves_contentHash r2]
  | _, _, .trl _ r1 r2 => by
    dsimp only [termContentHash]
    rw [global_rename_preserves_contentHash r1, global_rename_preserves_contentHash r2]
  | _, _, .liftr _ r1 r2 => by
    dsimp only [termContentHash]
    rw [global_rename_preserves_contentHash r1, global_rename_preserves_contentHash r2]
  | _, _, .liftl _ r1 r2 => by
    dsimp only [termContentHash]
    rw [global_rename_preserves_contentHash r1, global_rename_preserves_contentHash r2]
  | _, _, .trans _ r1 r2 => by
    dsimp only [termContentHash]
    rw [global_rename_preserves_contentHash r1, global_rename_preserves_contentHash r2]
  | _, _, .arrowLine _ _ r1 r2 => by
    dsimp only [termContentHash]
    rw [global_rename_preserves_contentHash r1, global_rename_preserves_contentHash r2]
  | _, _, .piLine _ _ _ _ r1 r2 r3 r4 => by
    dsimp only [termContentHash]
    rw [global_rename_preserves_contentHash r1, global_rename_preserves_contentHash r2,
        global_rename_preserves_contentHash r3, global_rename_preserves_contentHash r4]
  | _, _, .prodLine _ _ _ r1 r2 => by
    dsimp only [termContentHash]
    rw [global_rename_preserves_contentHash r1, global_rename_preserves_contentHash r2]
  | _, _, .sigLine _ _ _ _ _ r1 r2 r3 r4 => by
    dsimp only [termContentHash]
    rw [global_rename_preserves_contentHash r1, global_rename_preserves_contentHash r2,
        global_rename_preserves_contentHash r3, global_rename_preserves_contentHash r4]
  | _, _, .boxLine _ _ r1 => by
    dsimp only [termContentHash]; rw [global_rename_preserves_contentHash r1]
  | _, _, .pathJ _ r1 r2 r3 r4 r5 r6 => by
    dsimp only [termContentHash]
    rw [global_rename_preserves_contentHash r1, global_rename_preserves_contentHash r2,
        global_rename_preserves_contentHash r3, global_rename_preserves_contentHash r4,
        global_rename_preserves_contentHash r5, global_rename_preserves_contentHash r6]
  | _, _, .funext _ _ r1 => by
    dsimp only [termContentHash]; rw [global_rename_preserves_contentHash r1]
  | _, _, .hap _ r1 r2 r3 r4 => by
    dsimp only [termContentHash]
    rw [global_rename_preserves_contentHash r1, global_rename_preserves_contentHash r2,
        global_rename_preserves_contentHash r3, global_rename_preserves_contentHash r4]
  | _, _, .u64Ty => rfl
  | _, _, .u64Lit _ => rfl
  | _, _, .u64BinOp _ r1 r2 => by
    dsimp only [termContentHash]
    rw [global_rename_preserves_contentHash r1, global_rename_preserves_contentHash r2]
  | _, _, .u64IfZero r1 r2 r3 => by
    dsimp only [termContentHash]
    rw [global_rename_preserves_contentHash r1, global_rename_preserves_contentHash r2,
        global_rename_preserves_contentHash r3]
  | _, _, .u64Repeat _ r1 r2 => by
    dsimp only [termContentHash]
    rw [global_rename_preserves_contentHash r1, global_rename_preserves_contentHash r2]

theorem global_rename_preserves_list {env₁ env₂ : HashEnv} :
    ∀ {as bs : List Term}, EnvRelList env₁ env₂ as bs →
      termListContentHash env₁ as = termListContentHash env₂ bs
  | _, _, .nil => rfl
  | _, _, .cons rx rxs => by
    dsimp only [termListContentHash]
    rw [global_rename_preserves_contentHash rx, global_rename_preserves_list rxs]

theorem global_rename_preserves_fields {env₁ env₂ : HashEnv} :
    ∀ {fs gs : List (String × ModPath × Term)}, EnvRelFields env₁ env₂ fs gs →
      fieldTeleContentHash env₁ fs = fieldTeleContentHash env₂ gs
  | _, _, .nil => rfl
  | _, _, .cons _ _ rt rfs => by
    dsimp only [fieldTeleContentHash]
    rw [global_rename_preserves_contentHash rt, global_rename_preserves_fields rfs]

theorem global_rename_preserves_tuple {env₁ env₂ : HashEnv} :
    ∀ {fs gs : List (String × Term)}, EnvRelTuple env₁ env₂ fs gs →
      tupleFieldsContentHash env₁ fs = tupleFieldsContentHash env₂ gs
  | _, _, .nil => rfl
  | _, _, .cons _ rv rfs => by
    dsimp only [tupleFieldsContentHash]
    rw [global_rename_preserves_contentHash rv, global_rename_preserves_tuple rfs]

theorem global_rename_preserves_branches {env₁ env₂ : HashEnv} :
    ∀ {bs cs : List (String × Nat × Term)}, EnvRelBranches env₁ env₂ bs cs →
      branchListContentHash env₁ bs = branchListContentHash env₂ cs
  | _, _, .nil => rfl
  | _, _, .cons _ _ rb rbs => by
    dsimp only [branchListContentHash]
    rw [global_rename_preserves_contentHash rb, global_rename_preserves_branches rbs]

end

/-- **Landmark Theorem CH.1 (`termContentHash_alpha_invariant`, `0 sorry`)**:
    Arbitrary deep α-renaming of bound variables anywhere inside a `Term` leaves
    `termContentHash` strictly unchanged! -/
theorem termContentHash_alpha_invariant (env : HashEnv) {t₁ t₂ : Term}
    (hAlpha : AlphaEq env t₁ t₂) :
    termContentHash env t₁ = termContentHash env t₂ :=
  global_rename_preserves_contentHash hAlpha

/-- **Landmark Theorem CH.3 (`modern_and_legacy_same_contentHash`, `0 sorry`)**:
    Elaborating any well-formed Modern `.narya` expression `e` (`elabModernExpr`) vs
    legacy Lisp `.ny` S-expression (`elaborateSExp`) yields **identical Unison content hashes**! -/
theorem modern_and_legacy_same_contentHash
    (env : HashEnv) (fuel : Nat) (T : ModeTheory) (mode : ModeId)
    (locals : List String) (e : ModernExpr) (hwf : e.wf = true) :
    (elabModernExpr fuel T mode locals e).map (termContentHash env) =
      (elaborateSExp fuel T mode locals e.toSExp).map (termContentHash env) := by
  rw [elabModernExpr_eq_elaborateSExp fuel T mode locals e hwf]

/-- **Landmark Theorem CH.4 (`same_erasure_same_abiHash`, `0 sorry`)**:
    Any two core terms whose proofs, modalities, and `Ghost0` arguments erase to the
    same `HIR` program (`HIR.eraseFromCore b₁ = HIR.eraseFromCore b₂`) produce the
    **exact same 64-bit ARMv8-A hardware `ABI` hash**! -/
theorem same_erasure_same_abiHash {b₁ b₂ : Term}
    (hErase : HIR.eraseFromCore b₁ = HIR.eraseFromCore b₂) :
    computeRawAbiHash b₁ = computeRawAbiHash b₂ := by
  unfold computeRawAbiHash thinCompileCore
  rw [hErase]

end Narya.Meta
