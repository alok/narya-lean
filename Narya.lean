/-
  Narya — Unified Multi-Modal Higher Observational Type Theory & Verified Native Codegen in Lean 4

  Root library importing:
  - `Narya.Dim`      : Colored variable-arity multi-directional cube category (`hott`, `param k`, `displayed`, `nominal`)
  - `Narya.Modal`    : First-class 2-categorical mode theories (21 built-in, incl. QTT/LNL), CSLib combinators, & BFS 2-cell synthesis
  - `Narya.Core`     : Glued 3-tier NbE, observational equality (`funext`/`hap`, codata bisimulation), `Mugen` levels, QTT linearity, & open-problem proofs
  - `Narya.Syntax`   : Pretty-printer & standalone `.ny` surface parser/script runner
  - `Narya.Elab`     : Lean 4 metaprogramming DSL (`narya!`, `narya_hoTT!`, `#narya_check`, `#narya_eval`, `#narya_jit`, `def_mode_theory`)
  - `Narya.Fast`     : Unboxed 64-bit `PackedSFace`, Sorbet 16-byte `PackedNode` `TermArena`, & flat-array linear `InteractionNet`
  - `Narya.Compiler` : `TimeM` cost monad, `RepBridge`, `Core.NbE → HIR → MIR → LIR → Arm64` erasure/compiler, & `ThinEmitter` W^X `MAP_JIT`
  - `Narya.Meta`     : Hierarchical nanosecond + heap-allocation `Profiler` & Lake-inspired Merkle `BuildTrace` package builder
  - `Narya.Examples` : End-to-end checked showcase (`Tour.lean`)
-/
import Narya.Dim
import Narya.Modal
import Narya.Core
import Narya.Syntax
import Narya.Elab
import Narya.Fast
import Narya.Compiler
import Narya.Meta
import Narya.Examples.Tour
