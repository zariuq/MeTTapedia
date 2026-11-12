import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.KnowledgeTensorCoreReading
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.KnowledgeTensorCoreHelperZoned
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.KnowledgeTensorCoreFirstOrderIdentities

/-!
# The two steps of the calculus have zoned readings

The theorem of `KnowledgeTensorCoreReading` is stated for an arbitrary step with a zoned reading.
Both steps of the calculus have one.

* `FirstOrder.identityReading`: the first-order step, read on occurrence identities at one frame.
  Good knowledge is a nonempty set of solutions; a good state has a consistent store.
* `HelperZoned.helperReading`: the binding-aware helper step, read over the declaration frames.
  Good knowledge is a nonempty set of solutions in later frames; a good state has solvable
  knowledge.
* `FirstOrder.identity_reading_run_iff_proves`, `HelperZoned.helper_reading_run_iff_proves`: the
  general theorem at each of the two.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore

open Mettapedia.Logic.LinearLogic
open _root_.CategoryTheory

section FirstOrder

open AnnotatedRuns (Firing firstOrder)
open KnowledgeTensorFirstOrder (knowledge)

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
  (A : SubstitutionAction T S) (label : O → T)

/-- **The first-order step has a zoned reading on occurrence identities.** -/
def FirstOrder.identityReading :
    ZonedReading (firstOrder A label).toStep (FirstOrder.identityZoned A label) where
  Reads := fun C _ known owned => known = knowledge A C ∧ owned = C.present.val
  use := fun f => ⟨(), f⟩
  Good := fun known => Set.Nonempty known
  good := fun C => A.Consistent C.equations
  good_of_le := fun refines nonempty => nonempty.mono refines
  good_of_know := fun _ _ nonempty => nonempty
  reads_good := fun reads => by
    obtain ⟨rfl, _⟩ := reads
    exact Iff.rfl
  forth := fun {C a _ _} f allowed reads => by
    obtain ⟨rfl, rfl⟩ := reads
    cases a
    exact ⟨f, _, _, rfl, FirstOrder.firesUnder_of_valid A label allowed, rfl, rfl⟩
  back := fun {C a _ _} declaration {_ _} reads fires consistent => by
    obtain ⟨rfl, rfl⟩ := reads
    cases a
    obtain ⟨valid, reaches, holds⟩ :=
      FirstOrder.valid_of_firesUnder A label C declaration fires consistent
    exact ⟨declaration, valid, rfl, reaches, holds⟩

/-- **The general theorem at the first-order step.** -/
theorem FirstOrder.identity_reading_run_iff_proves (C : Configuration T O)
    (word : List (Sigma (KnowledgeTensor.Const (Firing T S O)))) :
    (∃ run : (firstOrder A label).toStep.Run C,
        (FirstOrder.identityReading A label).uses run = word ∧ A.Consistent run.last.equations) ↔
      ∃ (last : Unit) (along : (() : Unit) ⟶ last) (reached : Set S) (left : Multiset O)
        (grade : Multiset O → Prop), grade 0 ∧
          (FirstOrder.identityZoned A label).Proves () 0 (knowledge A C) C.present.val grade word
            last along reached left ∧ reached.Nonempty :=
  (FirstOrder.identityReading A label).run_iff_proves (a := ()) ⟨rfl, rfl⟩ word

end FirstOrder

section Helper

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Helpers (State Firing helperStep)
open HelperZoned

variable {S : Signature} {O : Type} [DecidableEq O]

/-- **The binding-aware helper step has a zoned reading over the declaration frames.** -/
noncomputable def HelperZoned.helperReading :
    ZonedReading (helperStep (S := S) (O := O)).toStep (helperZoned S O) where
  Reads := fun s F known owned =>
    (⟨F, known, owned⟩ : Σ F : Frames.Frame S, Known S F × Multiset O) =
      ⟨s.frame, solutions (Frames.contextual S) s.knowledge, s.present.val⟩
  use := fun {s} f => ⟨s.frame, ruleOf f⟩
  Good := fun known => Set.Nonempty known
  good := fun s => (Frames.contextual S).Solvable s.knowledge
  good_of_le := fun refines nonempty => nonempty.mono refines
  good_of_know := fun step known nonempty => knowAlong_nonempty S step known nonempty
  reads_good := fun reads => by
    cases reads
    exact solvable_iff_nonempty _
  forth := fun {s _ _ _} f allowed reads => by
    cases reads
    exact ⟨ruleOf f, _, _, rfl, firesUnder_of_admits f allowed, rfl⟩
  back := fun {s _ _ _} declaration {_ _} reads fires consistent => by
    cases reads
    obtain ⟨allowed, reaches, holds⟩ := admits_of_firesUnder s declaration fires consistent
    subst reaches
    subst holds
    exact ⟨firingOf s declaration, allowed, rfl, rfl⟩

/-- **The general theorem at the helper step.** -/
theorem HelperZoned.helper_reading_run_iff_proves (s : State S O)
    (word : List (Sigma (Rule S O))) :
    (∃ run : helperStep.Run s, (helperReading (S := S) (O := O)).uses run = word ∧
        (Frames.contextual S).Solvable run.last.knowledge) ↔
      ∃ (last : Frames.Frame S) (along : FrameMap S s.frame last) (reached : Known S last)
        (left : Multiset O) (grade : Multiset O → Prop), grade 0 ∧
          (helperZoned S O).Proves s.frame 0 (solutions (Frames.contextual S) s.knowledge)
            s.present.val grade word last along reached left ∧ reached.Nonempty :=
  (helperReading (S := S) (O := O)).run_iff_proves (s := s) rfl word

end Helper

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore
