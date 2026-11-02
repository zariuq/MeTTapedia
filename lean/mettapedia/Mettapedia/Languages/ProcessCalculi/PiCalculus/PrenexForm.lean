import Mettapedia.Languages.ProcessCalculi.PiCalculus.Blocks

/-!
# Prenex forms of π processes

π's canonical form is the restriction-block theory's at π's blocks (`Blocks.piBlock`): modulo π's static theory a
process is a block of restrictions over a bag of components, each an input, an output or a replicated input, with
canonical parts inside. The theory makes it sound and complete at every sort; the controls below read it on named
processes.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus.PrenexForm

open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (canon)
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Blocks (piBlock)
open Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance (piToPattern)

/-! ### Controls -/

/-- `(νa) 0` is `0`. -/
example : canon piBlock (piToPattern (.nu "a" .nil)) = canon piBlock (piToPattern .nil) := by decide +kernel

/-- Extrusion: `(νx)(x⟨w⟩ | a⟨b⟩)` and `(νx) x⟨w⟩ | a⟨b⟩`. -/
example :
    canon piBlock (piToPattern (.nu "x" (.par (.output "x" "w") (.output "a" "b")))) =
      canon piBlock (piToPattern (.par (.nu "x" (.output "x" "w")) (.output "a" "b"))) := by
  decide +kernel

/-- Exchange: `(νx)(νy) x⟨y⟩` and `(νy)(νx) x⟨y⟩`. -/
example :
    canon piBlock (piToPattern (.nu "x" (.nu "y" (.output "x" "y")))) =
      canon piBlock (piToPattern (.nu "y" (.nu "x" (.output "x" "y")))) := by
  decide +kernel

/-- Inside a guard: `a(z).(νx)0` and `a(z).0`. -/
example :
    canon piBlock (piToPattern (.input "a" "z" (.nu "x" .nil))) = canon piBlock (piToPattern (.input "a" "z" .nil)) := by
  decide +kernel

/-- **Negative**: a restriction does not leave a guard: `(νx) a(z).x⟨z⟩` and `a(z).(νx) x⟨z⟩` differ. -/
example :
    canon piBlock (piToPattern (.nu "x" (.input "a" "z" (.output "x" "z")))) ≠
      canon piBlock (piToPattern (.input "a" "z" (.nu "x" (.output "x" "z")))) := by
  decide +kernel

/-- **Negative**: two outputs on one private channel are not two outputs on two private channels. -/
example :
    canon piBlock (piToPattern (.nu "v" (.par (.output "c" "v") (.output "c" "v")))) ≠
      canon piBlock (piToPattern (.nu "v" (.nu "u" (.par (.output "c" "v") (.output "c" "u"))))) := by
  decide +kernel

end Mettapedia.Languages.ProcessCalculi.PiCalculus.PrenexForm
