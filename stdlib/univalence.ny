-- stdlib/univalence.ny — Observational `funext`/`hap`, `Glue` univalence & transport

(import "core")

(def idBoolFromCore (arrow Bool Bool)
  (idTy Bool))

(def reflTrue (Id Bool (idBoolFromCore true) true)
  (refl true))

-- Higher-dimensional observational function extensionality (`funext` + `hap`)
(def extIdBool (Id (arrow Bool Bool) idBoolFromCore (fun b b))
  (funext b (hap (refl idBoolFromCore) b0 b1 b2)))

-- Univalence `Glue` line on `Bool` and computational `arrow_line` transport
(axiom notEquiv (arrow Bool (arrow Bool Type)))

(def uaBool (Id Type Bool Bool)
  (Glue Bool Bool notEquiv))

(eval (trr (arrow_line (refl Bool) (refl Bool)) idBoolFromCore))
