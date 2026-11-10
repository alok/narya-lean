# narya-lean — Agent & Developer Instructions

## Commands
```bash
lake build              # Build entire Narya library (must have 0 errors and 0 sorrys)
lake build +Narya.Dim   # Build single module + dependencies
lake test               # Run test suite (cubical laws, mode combinators, NbE, HoTT, ARM64 native execution)
lake exe narya -- --help # Run standalone CLI prover & compiler
```

## Architectural Rules
1. **Computability**: Every Lean 4 definition in `Narya.*` MUST be computable (`noncomputable` is forbidden in runtime/compiler/checker paths). Prefer `Fin`, `Array`, and `UInt64` over `Finset`.
2. **Zero-Sorry Theorems**: All metatheoretic theorems, cubical category laws, mode-theory coherence proofs, reference-to-packed refinement proofs, and `HIR → MIR → LIR → ARM64` compiler soundness proofs must compile with zero `sorry`.
3. **Reference vs. Fast Separation**:
   - `Narya.Dim` & `Narya.Core`: Transparent, intrinsically structured reference semantics faithful to Mike Shulman's Narya architecture (generalized to multi-directional dimensions and first-class mode theory combinators).
   - `Narya.Fast` & `Narya.Compiler`: Bit-packed unboxed representations (`UInt64` cubical operators), CSLib-style `TimeM` complexity monad, isomorphism-bridge optimization, and verified multi-IR (`HIR → MIR → LIR → ARM64`) compilation proved equivalent to reference semantics.
4. **Search & Git**: Use `rg` and `fd` exclusively. Make atomic commits per layer/feature.
