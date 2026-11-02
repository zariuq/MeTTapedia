import Mettapedia.OSLF.NativeTypes.GeneratedLogic.RhoModelReading
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.FrontDoorAgreement
import Mettapedia.OSLF.NativeTypes.Instances.Normalized.RhoControls

/-!
# Controls: the normalized ρ profile through both front doors

The normalized ρ profile is installed with its driver and its native engine (`installed`). It is read in the reference
structure of ρ's model language on the class of ρ's carrier (`RhoModel.faithful`). So each decided runtime verdict about
a process there is the truth of the query's closed formula, and the generated front door, deciding that formula over
the model language's canonical forms (`RhoModel.forms`), agrees with the runtime at every budget.

The processes are those of the runtime controls: an output on `@(*@0)` beside an input on `@0` that drops what it
receives (`positive`), the same with the output on `@0` (`canonical`), and with the output on `@{}` (`negative`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.RhoModel.Controls

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax (Query)
open Mettapedia.OSLF.NativeTypes.Runtime (Installed)
open FrontDoorAgreement (frontDoor Agrees agrees_of_frontDoor)
open Mettapedia.OSLF.NativeTypes.Instances.Normalized
open Mettapedia.OSLF.NativeTypes.Instances.Normalized.RhoControls (positive negative)

/-- The installed normalized ρ profile: its driver and its native engine. -/
abbrev installed : Installed := RhoProfile.profile.installed

/-- Its reading at the front door, for formulas without separating conjunctions. -/
abbrev read := (faithful Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty).reading (kindOf := fun _ => .hashBag)

/-- An admitted process, decoded. -/
def decoded (raw : Pattern) (admitted : Source RhoProfile.generated [] RhoProfile.proc raw) :
    installed.native.Decoded raw :=
  ⟨raw, admitted, rfl⟩

/-- Every observation the driver looks up is covered. -/
theorem covered : ∀ name leaf, installed.native.lookup name = some leaf → read.covers leaf := by
  intro name leaf _
  have only : leaf = ⟨0, by decide⟩ := Fin.ext (by have := leaf.2; simp [RhoProfile.profile] at this; omega)
  subst only
  exact ⟨RhoProfile.done, rfl, done_tests, carrier_region done_carrier⟩

/-- **The runtime agrees with the generated front door** about a process of ρ's carrier. -/
theorem agrees {query : Query} (raw : Pattern) (admitted : Source RhoProfile.generated [] RhoProfile.proc raw)
    (inCarrier : carrier raw = true) {rounds : ℕ} {answer : Bool}
    (answered : frontDoor read [] 1 query raw rounds
      (some (forms Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty 0)) = some answer) :
    Agrees installed query raw answer :=
  agrees_of_frontDoor installed read covered (decoded raw admitted) (carrier_region inCarrier) (by rfl) answered

theorem positive_reaches_done : Agrees installed (.possibility (.constructor "Done")) positive true :=
  agrees positive (checkOpenPatternWellSorted_sound (by decide +kernel)) (by decide +kernel) (rounds := 3)
    (by decide +kernel)

theorem canonical_reaches_done : Agrees installed (.possibility (.constructor "Done")) RhoControls.canonical true :=
  agrees RhoControls.canonical (checkOpenPatternWellSorted_sound (by decide +kernel)) (by decide +kernel) (rounds := 3)
    (by decide +kernel)

/-- **Sending on `@{}` does not meet the input on `@0`**: the model keeps `{}` apart from `0`. -/
theorem negative_stuck : Agrees installed (.possibility (.constructor "Done")) negative false :=
  agrees negative (checkOpenPatternWellSorted_sound (by decide +kernel)) (by decide +kernel) (rounds := 3)
    (by decide +kernel)

theorem done_stuck : Agrees installed (.possibility (.constructor "Done")) RhoProfile.done false :=
  agrees RhoProfile.done (checkOpenPatternWellSorted_sound (by decide +kernel)) (by decide +kernel) (rounds := 3)
    (by decide +kernel)

theorem positive_every_done : Agrees installed (.outgoingUniversal (.constructor "Done")) positive true :=
  agrees positive (checkOpenPatternWellSorted_sound (by decide +kernel)) (by decide +kernel) (rounds := 3)
    (by decide +kernel)

theorem positive_not_every_bottom : Agrees installed (.outgoingUniversal .bottom) positive false :=
  agrees positive (checkOpenPatternWellSorted_sound (by decide +kernel)) (by decide +kernel) (rounds := 3)
    (by decide +kernel)

theorem done_is_done : Agrees installed (.constructor "Done") RhoProfile.done true :=
  agrees RhoProfile.done (checkOpenPatternWellSorted_sound (by decide +kernel)) (by decide +kernel) (rounds := 3)
    (by decide +kernel)

theorem positive_not_done : Agrees installed (.constructor "Done") positive false :=
  agrees positive (checkOpenPatternWellSorted_sound (by decide +kernel)) (by decide +kernel) (rounds := 3)
    (by decide +kernel)

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.RhoModel.Controls
