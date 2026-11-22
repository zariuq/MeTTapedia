import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.Barbed
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed.PositiveTell

/-!
# The faithful reflective calculus as a target of the separation

`rhoParallel ω` is the reflective calculus as a calculus with a parallel composition in the sense of
`NullsOnTheStep.ParallelClosed`: closed processes of the sealed carrier, the reduction
`rhoLanguageDefGSLT.Step` (communication modulo the equations), its own parallel composition `P | Q`
(the two-element bag, `par`), every pair composable, success the output barb on the canonical form of
`ω`, and the equations (`rhoProcessEquations`) as the static equivalence.

* **It is persistent** (`rhoParallel_persistent`): its reduction is closed beside any process
  (`rho_closedBeside`, from `CanonicalReaction.reaction_frame`), a barb of `P` is a barb of `P | R`,
  and reachable success is read up to the equations (steps and barbs depend on a process only through
  its canonical bag: `step_congr`, `barb_congr`).
* **The separation with the faithful calculus as target**: no uniform translation (homomorphic on
  parallel composition up to the equations, preserving and reflecting reachable success) goes into it
  from the step with the absence-guarded program (`no_uniformTranslation_absence`) or from the step with
  the positive program whose tell is on a shared unknown (`no_uniformTranslation_positiveTell`).
* **Control**: the criterion can be met with this target: the identity is a uniform translation of the
  calculus into itself (`identity_uniform`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical (canonicalize)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalBag
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed
  (ParallelCalculus UniformTranslation ClosedBeside isEmpty_uniformTranslation)
open ByInstantiation (sig G Closed read)

/-- The canonical bag of `P | Q` is the bag of `P` beside the bag of `Q`. -/
theorem fromProcess_par_bag (P Q : RhoProcess) :
    fromProcess (par P Q) = append (fromProcess P) (fromProcess Q) :=
  Subtype.ext (by rw [append_inventory]; exact fromProcess_par P Q)

/-- **The reflective calculus as a calculus with a parallel composition.** -/
def rhoParallel (ω : G [] .nm) : ParallelCalculus.{0} where
  Term := RhoProcess
  step := rhoLanguageDefGSLT.Step
  par := par
  composable _ _ := True
  success P := Barb P (canonicalize (read ω))
  same := rhoProcessEquations.r

/-- **The reduction is closed beside any process.** -/
theorem rho_closedBeside : ClosedBeside (T := RhoProcess) rhoLanguageDefGSLT.Step par := by
  intro P P' R step
  apply (CanonicalReaction.publicStep_iff _ _).mpr
  rw [fromProcess_par_bag, fromProcess_par_bag]
  exact CanonicalReaction.reaction_frame ((CanonicalReaction.publicStep_iff _ _).mp step) _

/-- A barb of `P` is a barb of `P | R`. -/
theorem barb_par_left (P R : RhoProcess) (c : Pattern) (shows : Barb P c) : Barb (par P R) c := by
  obtain ⟨payload, member⟩ := shows
  refine ⟨payload, ?_⟩
  rw [fromProcess_par]
  exact Multiset.mem_add.mpr (.inl member)

/-- Steps depend on a process only through its canonical bag. -/
theorem step_congr {P P' : RhoProcess} (same : rhoProcessEquations.r P P') (Q : RhoProcess) :
    rhoLanguageDefGSLT.Step P Q ↔ rhoLanguageDefGSLT.Step P' Q := by
  rw [CanonicalReaction.publicStep_iff, CanonicalReaction.publicStep_iff,
    (fromProcess_eq_iff P P').mpr same]

/-- Barbs depend on a process only through its canonical bag. -/
theorem barb_congr {P P' : RhoProcess} (same : rhoProcessEquations.r P P') (c : Pattern) :
    Barb P c ↔ Barb P' c := by
  unfold Barb
  rw [(fromProcess_eq_iff P P').mpr same]

/-- **The faithful reflective calculus is persistent**: closed beside, success persists beside, and
reachable success is read up to the equations. -/
theorem rhoParallel_persistent (ω : G [] .nm) : (rhoParallel ω).Persistent where
  closed := rho_closedBeside
  persists P R shows := barb_par_left P R _ shows
  respects := by
    rintro P P' same ⟨Q, run, shows⟩
    rcases Relation.ReflTransGen.cases_head run with rfl | ⟨Q₁, step, rest⟩
    · exact ⟨P, .refl, (barb_congr same _).mpr shows⟩
    · exact ⟨Q, .head ((step_congr same Q₁).mpr step) rest, shows⟩

/-- **No uniform translation of the step with the absence-guarded program into the faithful
reflective calculus**, for every success channel `ω`. -/
theorem no_uniformTranslation_absence (ω : G [] .nm) :
    IsEmpty (UniformTranslation NullsOnTheStep.ParallelClosed.source (rhoParallel ω)) :=
  isEmpty_uniformTranslation NullsOnTheStep.ParallelClosed.source_switchable (rhoParallel_persistent ω)

/-- **No uniform translation of the step with the positive program (a tell on a shared unknown) into
the faithful reflective calculus**, for every success channel `ω`. -/
theorem no_uniformTranslation_positiveTell (ω : G [] .nm) :
    IsEmpty (UniformTranslation NullsOnTheStep.ParallelClosed.PositiveTell.tellSource (rhoParallel ω)) :=
  isEmpty_uniformTranslation NullsOnTheStep.ParallelClosed.PositiveTell.tellSource_switchable
    (rhoParallel_persistent ω)

/-- **Control: the criterion can be met with this target.** The identity is a uniform translation of
the reflective calculus into itself. -/
def identity_uniform (ω : G [] .nm) : UniformTranslation (rhoParallel ω) (rhoParallel ω) where
  map := id
  homomorphic _ _ _ := rfl
  preserves _ succeeds := succeeds
  reflects _ succeeds := succeeds

#print axioms fromProcess_par_bag
#print axioms rho_closedBeside
#print axioms step_congr
#print axioms barb_congr
#print axioms rhoParallel_persistent
#print axioms no_uniformTranslation_absence
#print axioms no_uniformTranslation_positiveTell
#print axioms identity_uniform

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings
