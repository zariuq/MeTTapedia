import Mettapedia.Languages.MeTTa.PeTTa.GSLTBindingPatterns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MetaMeTTaComparison
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Disequality

/-!
# Computed binding answers in the step's disequation frames

The model's actual quoted-pattern unifier supplies a principal answer of the
existing Atom substitution action. The existing disequation-frame theorem then
decides compatibility with retained negative information. Disequations remain
part of the frame; a successful probe does not turn them into ordinary bindings.

This joins model unification to the step's information interface. Execution of
a particular native unifier or a MeTTa query remains a separate obligation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.UnifyingDisequality

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MetaMeTTaComparison (atomAction)
open Mettapedia.Languages.MeTTa.PeTTa.UnifyingConstraintPresentation (presentation)
open ListView Unifying

abbrev StepSubstitution := Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Subst

/-- Read the value of each variable under an independently supplied step substitution. -/
def valuation (candidate : StepSubstitution) : Valuation := fun name =>
  (candidate name).getD (.var name)

mutual
theorem step_apply (candidate : StepSubstitution) : ∀ term : Atom,
    atomAction.apply candidate term = instantiate (valuation candidate) term
  | .var _ => rfl
  | .symbol _ => rfl
  | .grounded _ => rfl
  | .expression items => by
      change Atom.expression _ = Atom.expression _
      exact congrArg Atom.expression (step_apply_list candidate items)

theorem step_apply_list (candidate : StepSubstitution) : ∀ items : List Atom,
    Mettapedia.Languages.MeTTa.SubstitutionAlgebra.subst.substList candidate items =
      instantiate.instantiateList (valuation candidate) items
  | [] => rfl
  | first :: rest => by
      simp only [Mettapedia.Languages.MeTTa.SubstitutionAlgebra.subst.substList,
        instantiate.instantiateList, ← step_apply, ← step_apply_list]
      rfl
end

theorem models_iff (candidate : StepSubstitution) (equations : EquationStore Atom) :
    atomAction.Models candidate equations ↔
      valuation candidate ∈ SolutionsOf EquationHolds equations := by
  change (∀ pair ∈ equations, atomAction.apply candidate pair.1 =
      atomAction.apply candidate pair.2) ↔ _
  simp only [step_apply, SolutionsOf, EquationHolds, Set.mem_ofPred_eq]

/-- A solved answer gives the image of each variable, leaving genuine open
values open. This is the computed substitution, not an arbitrary model. -/
def solved (bindings : Subst) : StepSubstitution := fun name =>
  some (valuationOf (UnifyingConstraintPresentation.environment bindings) name)

theorem solved_apply (bindings : Subst) (term : Atom) :
    atomAction.apply (solved bindings) term = resolve bindings term := by
  rw [step_apply]
  change instantiate (valuationOf (UnifyingConstraintPresentation.environment bindings)) term = _
  rw [instantiate_valuationOf, UnifyingConstraintPresentation.read_environment]

theorem solved_models (bindings : Subst) (valid : Idempotent bindings) :
    atomAction.Models (solved bindings) (presentation bindings) := by
  intro pair member
  obtain ⟨binding, _, rfl⟩ := List.mem_map.mp member
  change atomAction.apply (solved bindings) (.var binding.1) =
    atomAction.apply (solved bindings) (resolve bindings (.var binding.1))
  rw [solved_apply, solved_apply]
  exact (resolve_idem valid _).symm

/-- Every independent solution absorbs the computed solved substitution. -/
theorem models_absorb {bindings : Subst} {candidate : StepSubstitution}
    (models : atomAction.Models candidate (presentation bindings)) (term : Atom) :
    atomAction.apply candidate (resolve bindings term) = atomAction.apply candidate term := by
  have original := (models_iff candidate (presentation bindings)).mp models
  have absorbed := UnifyingConstraintPresentation.absorbs_of_solves
    (modelOf (valuation candidate)) bindings
    ((solves_modelOf (valuation candidate) (presentation bindings)).mpr original) term
  rw [read_modelOf, read_modelOf] at absorbed
  simpa only [← step_apply candidate] using absorbed

theorem quoted_models {bindings bound : Subst} {literal value : Atom}
    (valid : Idempotent bindings)
    (unified : unifyBinding bindings (GSLTBindingPatterns.quoted literal) value = .ok bound)
    (candidate : StepSubstitution) :
    atomAction.Models candidate (presentation bound) ↔
      atomAction.Models candidate (presentation bindings ++ [(literal, value)]) := by
  rw [models_iff, atomAction.models_append, atomAction.models_cons]
  simp only [atomAction.models_nil, and_true]
  rw [models_iff]
  have law := terms_ok_iff (fuelFor bindings literal value) valid unified (valuation candidate)
  change _ ↔ (_ ∧ atomAction.apply candidate literal = atomAction.apply candidate value)
  simpa only [step_apply, EquationHolds] using law

/-- The actual computed answer is principal for the incoming information and
the literal matching equation, against every independent step solution. -/
theorem quoted_principal {bindings bound : Subst} {literal value : Atom}
    (valid : Idempotent bindings)
    (unified : unifyBinding bindings (GSLTBindingPatterns.quoted literal) value = .ok bound) :
    atomAction.Principal (presentation bindings ++ [(literal, value)]) (solved bound) := by
  have boundValid := (unifyBinding_refines bindings bound _ value valid unified).1
  refine ⟨(quoted_models valid unified (solved bound)).mp (solved_models bound boundValid), ?_⟩
  intro candidate models
  refine ⟨candidate, fun term => ?_⟩
  rw [atomAction.apply_compose, solved_apply]
  exact (models_absorb ((quoted_models valid unified candidate).mpr models) term).symm

/-- Compatibility includes all retained disequations in the actual frame of
the existing step. No disequation is discarded by a successful binding probe. -/
theorem quoted_frame_solvable {bindings bound : Subst} {literal value : Atom}
    (frame : Disequality.Frame atomAction)
    (valid : Idempotent bindings)
    (unified : unifyBinding bindings (GSLTBindingPatterns.quoted literal) value = .ok bound) :
    (Disequality.frames atomAction).Solvable (a := frame)
        (presentation bindings ++ [(literal, value)]) ↔
      Disequality.Separates atomAction (solved bound) frame.1 :=
  Disequality.solvable_iff_separates (quoted_principal valid unified)

end Mettapedia.Languages.MeTTa.PeTTa.UnifyingDisequality
