import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.KnowledgeTensorCoreReadingInstances
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.KnowledgeTensorCoreFirstOrderIdentitiesControls

/-!
# Controls for zoned readings

* `the_identity_reading_reads_the_configuration`: the reading of the first-order step on
  occurrence identities reads the configuration that holds occurrence `1`.
* `no_reading_ignores_consistency`: no reading of the first-order step on identities that reads
  this configuration and names every firing as itself calls all knowledge consistent. The use
  that tells `1 = 2` fires in the zoned system and is no admitted firing, so the consistency of
  the final knowledge is a needed part of a reading.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore.Controls

open Mettapedia.Logic.LinearLogic
open AnnotatedRuns (Firing firstOrder)
open FirstOrderNativeRuns
open KnowledgeTensorFirstOrder (knowledge)
open KnowledgeTensorFirstOrderControls (plain)

theorem the_identity_reading_reads_the_configuration :
    (FirstOrder.identityReading plain id).Reads holdsOne () (knowledge plain holdsOne)
      holdsOne.present.val :=
  ⟨rfl, rfl⟩

/-- **The consistency of the final knowledge is a needed part of a reading.** -/
theorem no_reading_ignores_consistency :
    ¬ ∃ R : ZonedReading (firstOrder plain id).toStep (FirstOrder.identityZoned plain id),
      R.Reads holdsOne () (knowledge plain holdsOne) holdsOne.present.val ∧
        (∀ known : Set Unit, R.Good (a := ()) known) ∧
        ∀ (C : Configuration Nat Nat) (f : Firing Nat Unit Nat), R.use (s := C) f = ⟨(), f⟩ := by
  rintro ⟨R, reads, good, shape⟩
  obtain ⟨f, allowed, used, _⟩ :=
    R.back (s := holdsOne) (a := ()) contradicts reads contradicts_fires (good _)
  rw [shape] at used
  have same : f = contradicts := eq_of_heq (Sigma.mk.inj used).2
  subst same
  exact an_inconsistent_tell_is_a_zoned_proof_on_identities.2
    ⟨.cons contradicts allowed (.nil _), rfl⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore.Controls
