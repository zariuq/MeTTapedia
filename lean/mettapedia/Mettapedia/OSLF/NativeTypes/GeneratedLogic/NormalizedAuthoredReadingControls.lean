import Mettapedia.OSLF.NativeTypes.GeneratedLogic.NormalizedAuthoredReading
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.FrontDoorAgreement

/-!
# Controls: the authored normalized profile through both front doors

The authored profile is installed with its driver and its native engine (`installed`). It is read in the reference
structure of its language, with the provider's rows as the relation environment (`Authored.reading`). So each decided
runtime verdict about an admitted atom is the truth of the query's closed formula, and the generated front door,
deciding that formula over the language's canonical forms (`Authored.forms`), agrees with the runtime at every budget:

| query | atom | answer |
|---|---|---|
| some step reaches `Done` | `One` | yes |
| some step reaches `Done` | `Two` | yes |
| some step reaches `Done` | `Done` | no |
| every step reaches `Done` | `One` | yes |
| every step reaches `⊥` | `One` | no |
| `Done` | `Done` | yes |
| `Done` | `One` | no |

`One` steps because the equation `One = Two if allow(One)` holds, its query answered by the provider, and `Two ⇒ Done`
fires at `Two`; read as written, `One` matches no rule.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.NormalizedReading.Authored.Controls

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax (Query)
open Mettapedia.OSLF.NativeTypes.Runtime (Installed)
open FrontDoorAgreement (frontDoor Agrees agrees_of_frontDoor)
open Mettapedia.OSLF.MeTTaIL.GeneralCompletedFrontierControls (language one two done)
open Mettapedia.OSLF.NativeTypes.Instances.Normalized.AuthoredControls (profile)

/-- The installed authored profile: its driver and its native engine. -/
abbrev installed : Installed := profile.installed

/-- Its reading at the front door, for formulas without separating conjunctions. -/
abbrev read := reading.reading (kindOf := fun _ => .hashBag)

/-- An admitted atom, decoded. -/
def decoded (raw : Pattern) (admitted : Admitted raw) : installed.native.Decoded raw :=
  ⟨raw, (admitted_iff raw).mpr admitted, rfl⟩

/-- Every observation the driver looks up is covered. -/
theorem covered : ∀ name leaf, installed.native.lookup name = some leaf → read.covers leaf := by
  intro name leaf _
  have only : leaf = ⟨0, by decide⟩ := Fin.ext (by have := leaf.2; simp [profile] at this; omega)
  subst only
  exact ⟨done, rfl, done_tests, done_tests.admitted⟩

/-- **The runtime agrees with the generated front door** about an admitted atom. -/
theorem agrees {query : Query} (raw : Pattern) (admitted : Admitted raw) {rounds : ℕ} {answer : Bool}
    (answered : frontDoor read [] 1 query raw rounds (some (forms 0)) = some answer) :
    Agrees installed query raw answer :=
  agrees_of_frontDoor installed read covered (decoded raw admitted) ((admitted_iff raw).mpr admitted) (by rfl) answered

theorem one_reaches_done : Agrees installed (.possibility (.constructor "Done")) one true :=
  agrees one (.inl rfl) (rounds := 3) (by decide +kernel)

theorem two_reaches_done : Agrees installed (.possibility (.constructor "Done")) two true :=
  agrees two (.inr (.inl rfl)) (rounds := 3) (by decide +kernel)

theorem done_stuck : Agrees installed (.possibility (.constructor "Done")) done false :=
  agrees done (.inr (.inr rfl)) (rounds := 3) (by decide +kernel)

theorem one_every_done : Agrees installed (.outgoingUniversal (.constructor "Done")) one true :=
  agrees one (.inl rfl) (rounds := 3) (by decide +kernel)

theorem one_not_every_bottom : Agrees installed (.outgoingUniversal .bottom) one false :=
  agrees one (.inl rfl) (rounds := 3) (by decide +kernel)

theorem done_is_done : Agrees installed (.constructor "Done") done true :=
  agrees done (.inr (.inr rfl)) (rounds := 3) (by decide +kernel)

theorem one_not_done : Agrees installed (.constructor "Done") one false :=
  agrees one (.inl rfl) (rounds := 3) (by decide +kernel)

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.NormalizedReading.Authored.Controls
