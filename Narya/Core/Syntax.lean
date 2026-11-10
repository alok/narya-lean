/-
  Narya.Core.Syntax — Unified Multi-Modal Higher Observational Core Syntax

  Port and unification of OCaml Narya's `lib/core/term.ml` and `lib/core/energy.ml`.
  Supports simultaneously in a single kernel:
  1. Multi-modal type theory (`MTT` / `MATT`) over any first-class `ModeTheory`
     (modal `Π`, positive `□`/`♭` modal boxes with windowed elimination, negative sinister
     modal codata fields `(x : L | _) .fld : A`, and explicit/synthesized 2-cell keys `tm #α`).
  2. Multi-directional higher observational types (`obsEq`, `obsHet`, `refl`, `ap`, `sym`)
     across HoTT paths (`Dir.hott`), $k$-ary parametricity bridges (`Dir.param k`),
     displayed unary bridges (`Dir.displayed`), and nominal fresh axes (`Dir.nominal`).
  3. Relational `Gel`/`ungel` bridge universes (giving parametricity & univalent `Glue`).
  4. HoTT fibrancy transport (`trr`, `liftr`, `J`) restricted to fibrant directions (`g.isFibrant`).
  5. Parametricity lockers (`uuExt` blocked under `mod.flags.isLocker`) for `-external` and
     coinductive Semisimplicial Types (`SST`) in `-dtt`.
-/
import Narya.Dim
import Narya.Modal

namespace Narya.Core

open Narya.Dim Narya.Modal

/-- Evaluation energy (`lib/core/energy.ml`):
    `kinetic` terms compute eagerly under NbE; `potential` global codata definitions
    unfold lazily only when projected/observed, ensuring productivity of coinductive
    types like Semisimplicial Types (`SST`)! -/
inductive Energy where
  | kinetic
  | potential
  deriving DecidableEq, Repr, Inhabited

/-- De Bruijn index (0 = innermost binder). -/
abbrev Ix := Nat

/-- De Bruijn level (0 = outermost binder in semantic environment). -/
abbrev Lvl := Nat

/-- Checked core terms of `narya-lean`. -/
inductive Term where
  /-- De Bruijn index variable `x_i`. -/
  | bvar (ix : Ix)
  /-- Global constant / definition reference. -/
  | global (name : String)
  /-- Parametric/observational universe `UU lvl`. -/
  | uu (lvl : Nat)
  /-- External discrete universe `UU_ext lvl` (permitted only when context lock is non-locking!). -/
  | uuExt (lvl : Nat)
  /-- Modal dependent function type `(x : mod | dom) → cod`. -/
  | pi (name : String) (mod : ModPath) (dom : Term) (cod : Term)
  /-- Modal lambda abstraction `λ (x : mod) => body`. -/
  | lam (name : String) (mod : ModPath) (body : Term)
  /-- Modal function application `fn (arg : mod)`. -/
  | app (fn : Term) (mod : ModPath) (arg : Term)
  /-- Local let-binding `let x : ty := val in body`. -/
  | letIn (name : String) (ty : Term) (val : Term) (body : Term)
  /-- Explicit 2-cell modal coercion `tm #cell` (`cell : μ ⇒ ν`). -/
  | key (cell : TwoCellExpr) (tm : Term)
  /-- Positive modal box type `⟨mod | ty⟩`. -/
  | modalBox (mod : ModPath) (ty : Term)
  /-- Positive modal constructor `box(mod, tm)`. -/
  | boxIntro (mod : ModPath) (tm : Term)
  /-- Positive modal windowed pattern elimination `let box(x : mod) := scrut in body`. -/
  | letBox (name : String) (mod : ModPath) (scrut : Term) (motive : Term) (body : Term)
  /-- Dependent record / negative modal codata type `sig (f₁ : μ₁ | A₁, ...)`.
      When `mod` has `sinister = true` (left adjoint `L ⊣ R`), `(self : L | _) .name : ty`
      is a negative modal codata field! -/
  | recordTy (fields : List (String × ModPath × Term))
  /-- Record / comatch tuple `⟨f₁ := t₁, ...⟩`. -/
  | tuple (fields : List (String × Term))
  /-- Field projection / negative modal observation `tm .field`. -/
  | proj (tm : Term) (field : String)
  /-- Built-in / user inductive datatype application `Data name params`. -/
  | dataTy (name : String) (params : List Term)
  /-- Inductive constructor `Ctor dataName ctorName args`. -/
  | ctor (dataName : String) (ctorName : String) (args : List Term)
  /-- Windowed inductive pattern matching (`winMod` filters discrete higher dimensions!).
      Branches are `(ctorName, arity, body)`. -/
  | matchData (scrut : Term) (winMod : ModPath) (motive : Term) (branches : List (String × Nat × Term))
  /-- Homogeneous observational bridge/path type `ObsEq g ty [a₀, ..., a_{k-1}]`. -/
  | obsEq (g : Dir) (ty : Term) (ends : List Term)
  /-- Heterogeneous observational bridge/path type `ObsHet g tyBridge [a₀, ..., a_{k-1}]`. -/
  | obsHet (g : Dir) (tyBridge : Term) (ends : List Term)
  /-- Reflexivity / degeneracy bridge `refl_g tm : ObsEq g A [tm, ..., tm]`. -/
  | refl (g : Dir) (tm : Term)
  /-- Binary bridge/path symmetry `sym_g p` (for arity-2 directions). -/
  | sym (g : Dir) (p : Term)
  /-- Observational congruence `ap_g fn argBridge`. -/
  | ap (g : Dir) (fn : Term) (argBridge : Term)
  /-- Relational Gel/Glue type `Gel_g [A₀, ..., A_{k-1}] rel : ObsEq g (UU l) [A₀, ..., A_{k-1}]`. -/
  | gel (g : Dir) (types : List Term) (rel : Term)
  /-- Gel bridge introduction `gelIntro_g [a₀, ..., a_{k-1}] wit`. -/
  | gelIntro (g : Dir) (ends : List Term) (wit : Term)
  /-- Observational Gel projection `ungel_g bridgeTm` extracting the relation witness `wit`! -/
  | ungel (g : Dir) (bridgeTm : Term)
  /-- Fibrant forward transport `trr g tyLine x₀` (requires `g.isFibrant = true`, e.g. `Dir.hott`). -/
  | trr (g : Dir) (tyLine : Term) (x₀ : Term)
  /-- Fibrant backward transport `trl g tyLine x₁` (requires `g.isFibrant = true`). -/
  | trl (g : Dir) (tyLine : Term) (x₁ : Term)
  /-- Fibrant path lift `liftr g tyLine x₀ : ObsHet g tyLine [x₀, trr g tyLine x₀]`. -/
  | liftr (g : Dir) (tyLine : Term) (x₀ : Term)
  /-- HoTT path induction `J` on fibrant direction `g`. -/
  | pathJ (g : Dir) (ty : Term) (base : Term) (motive : Term)
      (reflCase : Term) (target : Term) (path : Term)
  deriving BEq, Repr

instance : Inhabited Term := ⟨.uu 0⟩

/-- Field declaration `(name, mod, ty)` inside `Term.recordTy`. -/
abbrev FieldDecl := String × ModPath × Term

/-- Constructor branch `(ctorName, arity, body)` inside `Term.matchData`. -/
abbrev MatchBranch := String × Nat × Term

/-! ### Global Declarations, Inductive Signatures, and Modal Typing Contexts -/

/-- Constructor specification in an inductive datatype declaration. -/
structure CtorSpec where
  name : String
  /-- Argument types (each telescope step may depend on parameters + earlier args). -/
  argTys : List Term
  deriving BEq, Repr, Inhabited

/-- Inductive datatype declaration in the global signature. -/
structure DataSpec where
  name : String
  mode : ModeId
  paramTys : List Term
  univLvl : Nat := 0
  ctors : List CtorSpec
  deriving BEq, Repr, Inhabited

/-- Entry in the global environment `GlobalEntry`. -/
inductive GlobalEntry where
  /-- Transparent or potential (lazy coinductive) definition `def name : ty := body`. -/
  | defn (name : String) (mode : ModeId) (energy : Energy) (ty : Term) (body : Term)
  /-- Postulated / axiom constant `axiom name : ty`. -/
  | ax (name : String) (mode : ModeId) (ty : Term)
  /-- Inductive datatype signature. -/
  | ind (spec : DataSpec)
  deriving BEq, Repr, Inhabited

/-- Global environment pairing a first-class `ModeTheory` with checked declarations. -/
structure GlobalEnv where
  theory : ModeTheory
  entries : List GlobalEntry := []
  deriving BEq, Repr, Inhabited

namespace GlobalEnv

def empty (T : ModeTheory := Combinators.pureHoTT) : GlobalEnv :=
  { theory := T, entries := [] }

def lookup? (G : GlobalEnv) (name : String) : Option GlobalEntry :=
  G.entries.find? fun
    | .defn n _ _ _ _ => strEq n name
    | .ax n _ _ => strEq n name
    | .ind s => strEq s.name name

def lookupData? (G : GlobalEnv) (name : String) : Option DataSpec :=
  G.entries.findSome? fun
    | .ind s => if strEq s.name name then some s else none
    | _ => none

def add (G : GlobalEnv) (e : GlobalEntry) : GlobalEnv :=
  { G with entries := e :: G.entries }

/-- Built-in standard prelude containing `Empty`, `Unit`, `Bool`, and `Nat`. -/
def withStdPrelude (T : ModeTheory) : GlobalEnv :=
  let m := T.defaultMode
  let emptySpec : DataSpec :=
    { name := "Empty", mode := m, paramTys := [], ctors := [] }
  let unitSpec : DataSpec :=
    { name := "Unit", mode := m, paramTys := [], ctors := [{ name := "tt", argTys := [] }] }
  let boolSpec : DataSpec :=
    { name := "Bool", mode := m, paramTys := [],
      ctors := [{ name := "false", argTys := [] }, { name := "true", argTys := [] }] }
  let natSpec : DataSpec :=
    { name := "Nat", mode := m, paramTys := [],
      ctors := [{ name := "zero", argTys := [] }, { name := "succ", argTys := [.dataTy "Nat" []] }] }
  { theory := T
    entries := [.ind natSpec, .ind boolSpec, .ind unitSpec, .ind emptySpec] }

end GlobalEnv

/-- Modal context entry: `(x : mod | ty)` bound at De Bruijn level `lvl`.
    When context locks `lock : ModPath` are pushed (e.g., entering a modal domain or codata field),
    every existing entry's effective access modality becomes `lock ∘ entry.mod`! -/
structure CtxEntry (ValTy : Type) where
  name : String
  mod : ModPath
  ty : ValTy
  deriving Repr

/-- Modal + higher-dimensional typing context (`TCtx`):
    - `mode`: current active mode `M`
    - `dims`: active higher-dimensional cube directions `DimCtx`
    - `entries`: bound variables (head = most recent De Bruijn index 0)
    - `lock`: accumulated outer context lock `ModPath` (used to check `-external`/`-dtt` lockers!) -/
structure TCtx (ValTy : Type) where
  mode : ModeId
  dims : DimCtx := []
  entries : List (CtxEntry ValTy) := []
  lock : ModPath
  deriving Repr

namespace TCtx

def init (ValTy : Type) (m : ModeId) : TCtx ValTy :=
  { mode := m, dims := [], entries := [], lock := ModPath.id m }

def length {V : Type} (Γ : TCtx V) : Nat :=
  Γ.entries.length

/-- Extend `Γ` with a new variable `(x : μ | A)` in the current mode (`μ.cod = Γ.mode`). -/
def extend {V : Type} (Γ : TCtx V) (name : String) (μ : ModPath) (ty : V) : TCtx V :=
  { Γ with entries := { name := name, mod := μ, ty := ty } :: Γ.entries }

/-- **Modal Lock Action on Contexts (`lockCtx`)**:
    Entering a binder or modal position guarded by `μ : M' → Γ.mode` shifts the active mode
    to `M'`, composes `μ` onto every bound variable's modality (`ν ↦ ν ∘ ...` — wait: in MTT,
    locking context `Γ` by `μ : M' → M` turns `Γ` at `M` into `Γ.lock(μ)` at `M'`; when a variable
    `(x : ν | A)` in `Γ` (`ν : M_x → M`) is accessed inside `Γ, lock(μ)`? Wait: in MTT (`Gratzer et al.`),
    to bind `(x : μ | A)` where `μ : M_x → M`, `A` is checked in `Γ` locked by `μ`! Wait: if `L ⊣ R`
    (`L : D → C`, `R : C → D`), a variable `x` bound with `L` (`x : (L | A)` where `A` is at `D`)
    lives in `Γ` at mode `C` with annotation `L : D → C`. Pushing lock `R : C → D` onto `Γ`
    composes `R` on the OUTSIDE (`R ∘ L : D → D`), so `η : 1_D ⇒ R ∘ L` unlocks `x` at mode `D`!!
    Let's verify the variance!
    - `x` has modality `L : D → C` (`dom = D`, `cod = C`).
    - Context `Γ` is at mode `C`.
    - We enter a right-adjoint lock `R : C → D` (shifting active mode from `C` to `D`!).
    - Every variable `(y : ν | B)` in `Γ` had `ν : M_y → C`. Composing `R : C → D` on the left
      gives `R ∘ ν : M_y → D` (`dom = M_y`, `cod = D`)!
    - Now at mode `D`, to use `x` (whose locked modality is `R ∘ L : D → D`) at identity modality
      `1_D : D → D`, in MTT a 2-cell `α : 1_D ⇒ R ∘ L` (contravariant in lock / covariant in
      variable access, i.e., `η : 1_D ⇒ R ∘ L`!) coerces `(R ∘ L)`-guarded `x` to `1_D`!
    Look how `R ∘ L` composes cleanly: `ModPath.comp R L` has `dom = D`, `cod = D`! -/
def pushLock {V : Type} (Γ : TCtx V) (lockMod : ModPath) : TCtx V :=
  { mode := lockMod.cod
    dims := lockMod.filterDim Γ.dims
    entries := Γ.entries.map (fun e => { e with mod := ModPath.comp lockMod e.mod })
    lock := ModPath.comp lockMod Γ.lock }

/-- Look up De Bruijn index `ix` in `Γ`. -/
def lookup? {V : Type} (Γ : TCtx V) (ix : Ix) : Option (CtxEntry V) :=
  Γ.entries[ix]?

/-- Whether `Γ` is currently inside any parametricity locker (`isLocker = true`).
    When `isLocked = true`, `UU_ext` is forbidden (enforcing parametricity in `-external`/`-dtt`)! -/
def isLocked {V : Type} (Γ : TCtx V) : Bool :=
  Γ.lock.flags.isLocker || Γ.entries.any (fun e => e.mod.flags.isLocker)

end TCtx

end Narya.Core
