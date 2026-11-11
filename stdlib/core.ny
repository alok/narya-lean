-- stdlib/core.ny — Foundational HoTT combinators, guarded coinductive streams & hole synthesis

(def idTy (pi A _ Type (arrow A A))
  (fun A (fun x x)))

(def constBool (arrow Bool (arrow Bool Bool))
  (fun a (fun b a)))

-- Guarded coinductive stream of 64-bit hardware words (`Energy.potential` + unproductive-cycle check)
(codef StreamU64 Type
  (record (head U64) (tail StreamU64)))

(codef ones StreamU64
  (tuple (head (u64 1)) (tail ones)))

(check (proj (proj ones tail) head))

-- Interactive Miller pattern hole synthesis (`?0 := true`)
(solve 0 (idTy Bool ?) true)
