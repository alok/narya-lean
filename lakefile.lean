import Lake
open Lake DSL

package «narya-lean» where
  version := v!"0.1.0"
  description := "Multi-Modal Higher Observational Type Theory in Lean 4: Theory Combinators, Open Problem Proofs, and Verified ARM64 Compilation"
  license := "GPL-3.0-only"
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib Narya where

lean_exe narya where
  root := `Main

@[test_driver]
lean_exe narya_tests where
  root := `Tests.Main
