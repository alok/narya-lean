/-
  Narya.Meta — Profiling, Telemetry, Flamegraph Exporters & Lake-Style Merkle Package Builder

  Re-exports:
  - `Narya.Meta.Profiler` : Hierarchical nanosecond + heap-allocation (`IO.getNumHeartbeats`)
                            phase profiler with Chrome Trace JSON & Brendan Gregg `.folded` flamegraphs
  - `Narya.Meta.Build`    : Lake-inspired Merkle `BuildTrace` (`1723` seed) incremental DAG builder
                            (`narya.toml` + `.narya/build/*.trace`, `*.nyo`, `*.arm64.bin`)
-/
import Narya.Meta.ContentHash
import Narya.Meta.Profiler
import Narya.Meta.Build
