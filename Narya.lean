/-
  Narya — Unified Multi-Modal Higher Observational Type Theory & Verified Native Codegen in Lean 4

  Root library importing:
  - `Narya.Dim`      : Colored variable-arity multi-directional cube category (`hott`, `param k`, `displayed`, `nominal`)
  - `Narya.Modal`    : First-class 2-categorical mode theories, CSLib combinators, & BFS 2-cell key synthesis
  - `Narya.Core`     : Glued 3-tier NbE, observational equality, bidirectional MTT checker, & open-problem proofs
  - `Narya.Syntax`   : Pretty-printer & standalone `.ny` surface parser/script runner
  - `Narya.Elab`     : Lean 4 metaprogramming DSL (`narya!`, `narya_hoTT!`, `#narya_check`, `def_mode_theory`)
  - `Narya.Fast`     : Unboxed 64-bit `PackedSFace` / `PackedSDeg` cubical primitives with `bv_decide` proofs
  - `Narya.Compiler` : `TimeM` cost monad, `RepBridge`, and verified `HIR → MIR → LIR → Arm64` Mach-O pipeline
  - `Narya.Examples` : End-to-end checked showcase (`Tour.lean`)
-/
import Narya.Dim
import Narya.Modal
import Narya.Core
import Narya.Syntax
import Narya.Elab
import Narya.Fast
import Narya.Compiler
import Narya.Examples.Tour
