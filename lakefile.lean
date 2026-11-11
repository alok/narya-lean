import Lake
open System Lake DSL

package «narya-lean» where
  version := v!"0.1.0"
  description := "Multi-Modal Higher Observational Type Theory in Lean 4: Theory Combinators, Open Problem Proofs, and Verified ARM64 Compilation"
  license := "GPL-3.0-only"
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

input_file narya_jit.c where
  path := "cbits" / "narya_jit.c"
  text := true

target narya_jit.o pkg : FilePath := do
  let srcJob ← narya_jit.c.fetch
  let oFile := pkg.buildDir / "cbits" / "narya_jit.o"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  buildO oFile srcJob weakArgs #["-fPIC", "-O3"] "cc" getLeanTrace

target libnaryajit_static pkg : FilePath := do
  let jitO ← narya_jit.o.fetch
  let name := nameToStaticLib "naryajit"
  buildStaticLib (pkg.staticLibDir / name) #[jitO]

@[default_target]
lean_lib Narya where
  moreLinkObjs := #[libnaryajit_static]

lean_exe narya where
  root := `Main

@[test_driver]
lean_exe narya_tests where
  root := `Tests.Main
