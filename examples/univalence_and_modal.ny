-- Sample standalone Narya-Lean `.ny` script
-- Run with: `lake exe narya run examples/univalence_and_modal.ny`

(theory pure_hott)
(def idBool (arrow Bool Bool) (fun b b))
(eval (idBool true))
(check (refl true))
(check (Fresh Bool))

-- Switch to Sinister Adjunction mode theory (`L : D -> C`, `R : C -> D`, `L -| R`)
(theory adjunction)
(check (box L Bool))
(def idBoxBool (arrow (box L Bool) (box L Bool)) (fun x x))
(eval (idBoxBool (box_intro L true)))

-- Switch to External Parametricity (`-external`)
(theory external_param)
(check Type_ext)
