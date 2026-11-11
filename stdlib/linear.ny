-- stdlib/linear.ny — Benton LNL (`linear_adjoint`) Quantitative/Linear Pipeline (`0 / 1 / ω` grades!)

(theory linear_adjoint)

-- 1. Grade `1` (`1_Lin` at linear mode `Lin`):
--    `x` MUST be consumed linearly (`checkLinearity` rejects contraction/weakening),
--    guaranteeing zero `DUP` fan nodes and zero reduction allocations in `InteractionNet`!
(def linearStep (arrow U64 U64)
  (fun x (u64_mul (u64_add x (u64 19)) (u64 2))))

-- 2. Grade `ω` (`! = F ∘ G` via `F.G : Lin -> Lin`):
--    Promotes a resource with grade `ω · ω = ω`, permitting duplication while BFS 2-cell
--    synthesis (`find2CellBFS?`) automatically inserts dereliction `ε_lnl : F∘G ⇒ 1_Lin`!
(def bangSquare (pi x F.G U64 U64)
  (lam x F.G (u64_mul x x)))

-- 3. Grade `0` (`Ghost0 : Cart -> Lin` with `grade = .zero`):
--    `g` is statically erased (`0` runtime uses allowed) while `x` is used linearly (`1` use)!
(def ghostErasedLinear (pi g Ghost0 U64 (arrow U64 U64))
  (lam g Ghost0 (fun x (u64_add x (u64 10)))))

(eval (linearStep (u64 7)))
(eval (app_mod bangSquare F.G (u64 9)))
