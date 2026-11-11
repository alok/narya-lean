-- stdlib/collatz.ny — Proof-Carrying 64-Bit Kernels Erased to Native ARMv8-A (`ThinEmitter` + `MAP_JIT`)

(import "univalence")

(axiom arg0 U64)
(axiom arg1 U64)

-- Binds `uaBool` (univalence Glue line) and `extIdBool` (observational funext) from `univalence`
-- as 0-graded ghost `let` witnesses inside a 111-step Collatz loop:
-- `ErasableCore` erases both proofs to zero runtime instructions, `ThinEmitter` streams raw
-- ARMv8-A machine words into `.narya/build/collatz__collatz111.arm64.bin`, and `MAP_JIT` runs `collatz111(27) => 1`!
(def collatz111 U64
  (let p1 (Id Type Bool Bool) uaBool
    (let p2 (Id (arrow Bool Bool) idBoolFromCore (fun b b)) extIdBool
      (u64_repeat 111 arg0 n
        (u64_ifz (u64_and n (u64 1))
          (u64_shr n (u64 1))
          (u64_add (u64_mul n (u64 3)) (u64 1)))))))

-- 64-bit SplitMix64 hash avalancher (`0xBF58476D1CE4E5B9` = 13787848793156543929)
(def splitmix64 U64
  (let mixed U64 (u64_xor arg0 arg1)
    (let m1 U64 (u64_mul (u64_xor mixed (u64_shr mixed (u64 30))) (u64 13787848793156543929))
      (u64_xor m1 (u64_shr m1 (u64 31))))))
