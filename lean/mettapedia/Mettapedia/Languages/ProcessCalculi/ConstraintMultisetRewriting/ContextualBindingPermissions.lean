import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualInformation
import Mettapedia.OSLF.Syntax.ContextualFamilySupport
import Mettapedia.OSLF.Syntax.ContextualFamilyObservations

/-!
# Explicit binding grants preserve closed joint caller observations

The protected interface is closed under the old equation dependencies. New
equations may mention only granted names, and those grants must not cross
the protected dependency closure. These are structural permission checks;
neither asks nor preservation of observations is assumed as a field.

A model-gluing proof preserves an entire vector of contextual observations
with one witness. It applies in every future declaration family, including
observations beneath binders and in metavariable argument spines. This is a
sufficient permission discipline, not a complete test for conservative
updates or a claim that all returned solver representations are identical.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingPermissions

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {V W : Type} {declarations : V → MetaArity S}
  {future : W → MetaArity S} {Γ : Ctx S} {sort : S.Srt}

def equationNames (equation : Equation (Term (signature S declarations) Γ sort)) : List V :=
  support equation.1 ++ support equation.2

/-- Names are connected when an old equation mentions both of them. This
includes dependencies through compound terms, not only variable aliases. -/
inductive DependencyClosure
    (old : EquationStore (Term (signature S declarations) Γ sort)) (roots : Set V) : V → Prop
  | root {name : V} : name ∈ roots → DependencyClosure old roots name
  | equation {known name : V}
      (reached : DependencyClosure old roots known)
      (equation : Equation (Term (signature S declarations) Γ sort))
      (present : equation ∈ old) (knownMember : known ∈ equationNames equation)
      (namedMember : name ∈ equationNames equation) : DependencyClosure old roots name

/-- Every equation lies wholly inside or wholly outside the component. -/
def Closed (component : Set V)
    (old : EquationStore (Term (signature S declarations) Γ sort)) : Prop :=
  ∀ equation ∈ old,
    (∀ name ∈ equationNames equation, name ∈ component) ∨
      (∀ name ∈ equationNames equation, name ∉ component)

theorem dependencyClosure_closed
    (old : EquationStore (Term (signature S declarations) Γ sort)) (roots : Set V) :
    Closed (DependencyClosure old roots) old := by
  classical
  intro equation present
  by_cases touched : ∃ name ∈ equationNames equation, DependencyClosure old roots name
  · obtain ⟨known, inside, reached⟩ := touched
    exact Or.inl (fun name member => .equation reached equation present inside member)
  · exact Or.inr (fun name member reached => touched ⟨name, member, reached⟩)

/-- This closure is least among equation-closed components containing the
declared roots. Its transitive support is not an extra permission assumption. -/
theorem dependencyClosure_least
    {old : EquationStore (Term (signature S declarations) Γ sort)} {roots component : Set V}
    (included : roots ⊆ component) (closed : Closed component old) :
    ∀ name, DependencyClosure old roots name → name ∈ component := by
  intro name reached
  induction reached with
  | root atRoot => exact included atRoot
  | equation _ equation present knownMember namedMember earlier =>
      rcases closed equation present with inside | outside
      · exact inside _ namedMember
      · exact False.elim (outside _ knownMember earlier)

theorem dependencyClosure_nil_iff (roots : Set V) (name : V) :
    DependencyClosure ([] : EquationStore (Term (signature S declarations) Γ sort)) roots name ↔
      name ∈ roots := by
  constructor
  · intro reached
    cases reached with
    | root member => exact member
    | equation _ _ present _ _ => cases present
  · exact DependencyClosure.root

def observationRoots (observed : List (Observation S declarations)) : Set V :=
  fun name => ∃ observation ∈ observed, name ∈ support observation.2.2

def protectedComponent
    (old : EquationStore (Term (signature S declarations) Γ sort))
    (observed : List (Observation S declarations)) : Set V :=
  DependencyClosure old (observationRoots observed)

/-- Grants are explicit input. Passing a captured variable may grant it;
ungranted protected components remain untouched. -/
structure Permitted (granted : Set V)
    (old added : EquationStore (Term (signature S declarations) Γ sort))
    (observed : List (Observation S declarations)) : Prop where
  additions : ∀ equation ∈ added, ∀ name ∈ equationNames equation, name ∈ granted
  separated : ∀ name ∈ granted, name ∉ protectedComponent old observed

theorem empty_store_permitted (granted : Set V)
    (added : EquationStore (Term (signature S declarations) Γ sort))
    (observed : List (Observation S declarations))
    (additions : ∀ equation ∈ added, ∀ name ∈ equationNames equation, name ∈ granted)
    (disjoint : ∀ name ∈ observationRoots observed, name ∉ granted) :
    Permitted granted [] added observed := by
  refine ⟨additions, ?_⟩
  intro name allowed reached
  exact disjoint name ((dependencyClosure_nil_iff _ _).mp reached) allowed

theorem Permitted.avoids {granted : Set V}
    {old added : EquationStore (Term (signature S declarations) Γ sort)}
    {observed : List (Observation S declarations)} (permission : Permitted granted old added observed) :
    ∀ equation ∈ added, ∀ name ∈ equationNames equation,
      name ∉ protectedComponent old observed :=
  fun equation present name member => permission.separated name (permission.additions equation present name member)

theorem equation_congr (first second : Assignment declarations future)
    (equation : Equation (Term (signature S declarations) Γ sort))
    (agree : ∀ name ∈ equationNames equation, first name = second name) :
    (instantiate first equation.1 = instantiate first equation.2) ↔
      (instantiate second equation.1 = instantiate second equation.2) := by
  rw [instantiate_congr first second equation.1
    (fun name member => agree name (List.mem_append_left _ member)),
    instantiate_congr first second equation.2
      (fun name member => agree name (List.mem_append_right _ member))]

/-- A single extension agrees on the entire component. A consistent complete
model is transported to the desired future family, then glued to the caller
model along the equation-closed boundary. -/
theorem extend_joint_component (component : Set V)
    (old added : EquationStore (Term (signature S declarations) Γ sort))
    (closed : Closed component old)
    (avoids : ∀ equation ∈ added, ∀ name ∈ equationNames equation, name ∉ component)
    (consistent : (ContextualFamilies.action declarations Γ sort).Consistent (old ++ added))
    (caller : Assignment declarations future) (callerModel : ContextualFrameUnifier.Models caller old) :
    ∃ extended : Assignment declarations future,
      ContextualFrameUnifier.Models extended (old ++ added) ∧
        ∀ name ∈ component, extended name = caller name := by
  classical
  obtain ⟨solution, solutionModel⟩ := consistent
  have otherModel : ContextualFrameUnifier.Models (Assignment.compose caller solution) (old ++ added) :=
    ContextualFrameUnifier.models_compose solutionModel caller
  let glued : Assignment declarations future :=
    fun name => if name ∈ component then caller name else Assignment.compose caller solution name
  refine ⟨glued, ?_, fun name member => by simp [glued, member]⟩
  intro equation member
  rcases List.mem_append.mp member with prior | new
  · rcases closed equation prior with inside | outside
    · exact (equation_congr glued caller equation
        (fun name named => by simp [glued, inside name named])).mpr (callerModel equation prior)
    · exact (equation_congr glued (Assignment.compose caller solution) equation
        (fun name named => by simp [glued, outside name named])).mpr
          (otherModel equation (List.mem_append_left _ prior))
  · exact (equation_congr glued (Assignment.compose caller solution) equation
      (fun name named => by simp [glued, avoids equation new name named])).mpr
        (otherModel equation (List.mem_append_right _ new))

def jointView (candidate : Assignment declarations future)
    (observed : List (Observation S declarations)) : List (Observation S future) :=
  observed.map (instantiateObservation candidate)

theorem jointView_congr (first second : Assignment declarations future)
    (observed : List (Observation S declarations))
    (agree : ∀ name ∈ observationRoots observed, first name = second name) :
    jointView first observed = jointView second observed := by
  apply List.map_congr_left
  rintro ⟨context, result, term⟩ member
  exact congrArg observe (instantiate_congr first second term
    (fun name named => agree name ⟨_, member, named⟩))

theorem Permitted.extends_joint_view {granted : Set V}
    {old added : EquationStore (Term (signature S declarations) Γ sort)}
    {observed : List (Observation S declarations)} (permission : Permitted granted old added observed)
    (consistent : (ContextualFamilies.action declarations Γ sort).Consistent (old ++ added))
    (caller : Assignment declarations future) (callerModel : ContextualFrameUnifier.Models caller old) :
    ∃ extended : Assignment declarations future,
      ContextualFrameUnifier.Models extended (old ++ added) ∧
        jointView extended observed = jointView caller observed := by
  obtain ⟨extended, model, agree⟩ := extend_joint_component (protectedComponent old observed) old added
    (dependencyClosure_closed old (observationRoots observed)) permission.avoids consistent caller callerModel
  exact ⟨extended, model, jointView_congr extended caller observed
    (fun name root => agree name (DependencyClosure.root root))⟩

/-- Every predicate on the whole caller vector has the same possibilities.
This preserves correlations; separate singleton witnesses would not suffice. -/
theorem Permitted.joint_possible_iff {granted : Set V}
    {old added : EquationStore (Term (signature S declarations) Γ sort)}
    {observed : List (Observation S declarations)} (permission : Permitted granted old added observed)
    (consistent : (ContextualFamilies.action declarations Γ sort).Consistent (old ++ added))
    (question : List (Observation S future) → Prop) :
    (∃ candidate : Assignment declarations future,
      ContextualFrameUnifier.Models candidate (old ++ added) ∧ question (jointView candidate observed)) ↔
    ∃ candidate : Assignment declarations future,
      ContextualFrameUnifier.Models candidate old ∧ question (jointView candidate observed) := by
  constructor
  · rintro ⟨candidate, model, answer⟩
    exact ⟨candidate, ((ContextualFrameUnifier.models_append candidate old added).mp model).1, answer⟩
  · rintro ⟨caller, callerModel, answer⟩
    obtain ⟨extended, model, same⟩ := permission.extends_joint_view consistent caller callerModel
    exact ⟨extended, model, same.symm ▸ answer⟩

theorem Permitted.joint_entails_iff {granted : Set V}
    {old added : EquationStore (Term (signature S declarations) Γ sort)}
    {observed : List (Observation S declarations)} (permission : Permitted granted old added observed)
    (consistent : (ContextualFamilies.action declarations Γ sort).Consistent (old ++ added))
    (question : List (Observation S future) → Prop) :
    (∀ candidate : Assignment declarations future,
      ContextualFrameUnifier.Models candidate (old ++ added) → question (jointView candidate observed)) ↔
    ∀ candidate : Assignment declarations future,
      ContextualFrameUnifier.Models candidate old → question (jointView candidate observed) := by
  constructor
  · intro entailed caller callerModel
    obtain ⟨extended, model, same⟩ := permission.extends_joint_view consistent caller callerModel
    exact same ▸ entailed extended model
  · intro entailed candidate model
    exact entailed candidate (((ContextualFrameUnifier.models_append candidate old added).mp model).1)

/-- A returned endomorphic solution may change only explicitly granted
components. This syntactic check is sufficient, and may reject benign
renamings into fresh helpers. -/
structure AnswerPermitted (granted : Set V) (answer : Assignment declarations declarations)
    (observed : List (Observation S declarations)) : Prop where
  fixesOutside : ∀ name, name ∉ granted → answer name = generator declarations name
  protectedOutside : ∀ name ∈ observationRoots observed, name ∉ granted

theorem AnswerPermitted.compose_preserves_joint {granted : Set V}
    {answer : Assignment declarations declarations} {observed : List (Observation S declarations)}
    (permission : AnswerPermitted granted answer observed) (candidate : Assignment declarations future) :
    jointView (Assignment.compose candidate answer) observed = jointView candidate observed := by
  apply jointView_congr
  intro name named
  change instantiate candidate (answer name) = candidate name
  rw [permission.fixesOutside name (permission.protectedOutside name named), instantiate_generator]

/-- A checked concrete solution supplies an alternative structural criterion:
private bindings may mention protected values if the protected support itself
is fixed. This admits fresh-local aliases rejected by disjoint support. -/
theorem AnswerPermitted.joint_possible_iff {granted : Set V}
    {old added : EquationStore (Term (signature S declarations) Γ sort)}
    {answer : Assignment declarations declarations} {observed : List (Observation S declarations)}
    (permission : AnswerPermitted granted answer observed)
    (solved : ContextualFrameUnifier.Models answer (old ++ added))
    (question : List (Observation S future) → Prop) :
    (∃ candidate : Assignment declarations future,
      ContextualFrameUnifier.Models candidate (old ++ added) ∧ question (jointView candidate observed)) ↔
    ∃ candidate : Assignment declarations future,
      ContextualFrameUnifier.Models candidate old ∧ question (jointView candidate observed) := by
  constructor
  · rintro ⟨candidate, model, result⟩
    exact ⟨candidate, ((ContextualFrameUnifier.models_append candidate old added).mp model).1, result⟩
  · rintro ⟨caller, _oldModel, result⟩
    exact ⟨Assignment.compose caller answer, ContextualFrameUnifier.models_compose solved caller,
      (permission.compose_preserves_joint caller).symm ▸ result⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingPermissions
