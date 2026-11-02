import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrderAskLocality
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.GuardFreeProcessOrders

/-!
# Equation extensions preserving protected first-order possibilities

A protected component is unaffected when every old solution extends to a new
solution agreeing on that component. This preserves joint possibilities, not
just the value chosen by one solver. The reverse restriction is supplied by
the original append-only occurrence step.

Already implied equations and consistent equations outside a closed component
give actual extension witnesses. This criterion concerns information; a policy
requiring raw generators to remain identical is a separate, stronger boundary.
No native authorization mechanism is introduced here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrderConservativeExtension

open Mettapedia.Logic.LP
open FirstOrderAskLocality

universe u v
variable {signature : LPSignature.{u, u, v, u}}

/-- Every previous protected interpretation remains possible after extension. -/
def ConservativeOn (component : Set signature.vars)
    (old new : EquationStore (Term signature)) : Prop :=
  ∀ first, (FirstOrder.action signature).Models first old →
    ∃ second, (FirstOrder.action signature).Models second new ∧
      ∀ name ∈ component, second name = first name

theorem conservative_refl (component : Set signature.vars)
    (equations : EquationStore (Term signature)) : ConservativeOn component equations equations :=
  fun first model => ⟨first, model, fun _ _ => rfl⟩

/-- Compose the actual solution extensions, retaining their protected values. -/
theorem ConservativeOn.trans {component : Set signature.vars}
    {first middle last : EquationStore (Term signature)}
    (one : ConservativeOn component first middle)
    (two : ConservativeOn component middle last) : ConservativeOn component first last := by
  intro initial model
  obtain ⟨intermediate, intermediateModel, oneAgree⟩ := one initial model
  obtain ⟨final, finalModel, twoAgree⟩ := two intermediate intermediateModel
  exact ⟨final, finalModel, fun name inside => (twoAgree name inside).trans (oneAgree name inside)⟩

theorem ConservativeOn.restrict {all smaller : Set signature.vars}
    {old new : EquationStore (Term signature)} (preserves : ConservativeOn all old new)
    (subset : smaller ⊆ all) : ConservativeOn smaller old new := by
  intro first model
  obtain ⟨second, secondModel, agree⟩ := preserves first model
  exact ⟨second, secondModel, fun name inside => agree name (subset inside)⟩

theorem conservative_chain (component : Set signature.vars)
    (stores : Nat → EquationStore (Term signature))
    (next : ∀ n, ConservativeOn component (stores n) (stores (n + 1))) (n : Nat) :
    ConservativeOn component (stores 0) (stores n) := by
  induction n with
  | zero => exact conservative_refl component (stores 0)
  | succ n ih => exact ih.trans (next n)

theorem possible_iff {component : Set signature.vars} {old new : EquationStore (Term signature)}
    (preserves : ConservativeOn component old new)
    (restriction : (FirstOrder.action signature).Refines new old)
    (observation : Subst signature → Prop) (reads : ReadsOnly component observation) :
    (∃ assignment, (FirstOrder.action signature).Models assignment new ∧ observation assignment) ↔
      ∃ assignment, (FirstOrder.action signature).Models assignment old ∧ observation assignment := by
  constructor
  · rintro ⟨assignment, model, holds⟩
    exact ⟨assignment, restriction assignment model, holds⟩
  · rintro ⟨first, model, holds⟩
    obtain ⟨second, secondModel, agree⟩ := preserves first model
    exact ⟨second, secondModel, (reads second first agree).mpr holds⟩

theorem entails_iff {component : Set signature.vars} {old new : EquationStore (Term signature)}
    (preserves : ConservativeOn component old new)
    (restriction : (FirstOrder.action signature).Refines new old)
    (observation : Subst signature → Prop) (reads : ReadsOnly component observation) :
    (FirstOrder.action signature).Entails new observation ↔
      (FirstOrder.action signature).Entails old observation := by
  constructor
  · intro entailed first firstModel
    obtain ⟨second, secondModel, agree⟩ := preserves first firstModel
    exact (reads second first agree).mp (entailed second secondModel)
  · exact (FirstOrder.action signature).entails_of_refines restriction

theorem verdicts_iff {component : Set signature.vars} {old new : EquationStore (Term signature)}
    (preserves : ConservativeOn component old new)
    (restriction : (FirstOrder.action signature).Refines new old)
    (observation : Subst signature → Prop) (reads : ReadsOnly component observation) :
    ((FirstOrder.action signature).Entails new observation ↔
      (FirstOrder.action signature).Entails old observation) ∧
    ((FirstOrder.action signature).Entails new (fun assignment => ¬ observation assignment) ↔
      (FirstOrder.action signature).Entails old (fun assignment => ¬ observation assignment)) :=
  ⟨entails_iff preserves restriction observation reads,
    entails_iff preserves restriction _ (fun first second agree => not_congr (reads first second agree))⟩

theorem component_agreement_reads_only (component : Set signature.vars) (target : Subst signature) :
    ReadsOnly component (fun assignment => ∀ name ∈ component, assignment name = target name) := by
  intro first second agree
  constructor
  · intro same name inside
    exact (agree name inside).symm.trans (same name inside)
  · intro same name inside
    exact (agree name inside).trans (same name inside)

/-- Preservation is joint: correlations between protected names are retained. -/
theorem possible_component_iff {component : Set signature.vars}
    {old new : EquationStore (Term signature)} (preserves : ConservativeOn component old new)
    (restriction : (FirstOrder.action signature).Refines new old) (values : Subst signature) :
    (∃ assignment, (FirstOrder.action signature).Models assignment new ∧
      ∀ name ∈ component, assignment name = values name) ↔
    ∃ assignment, (FirstOrder.action signature).Models assignment old ∧
      ∀ name ∈ component, assignment name = values name :=
  possible_iff preserves restriction _ (component_agreement_reads_only component values)

theorem possible_value_iff [DecidableEq signature.vars] {component : Set signature.vars}
    {old new : EquationStore (Term signature)} (preserves : ConservativeOn component old new)
    (restriction : (FirstOrder.action signature).Refines new old)
    (term value : Term signature) (supported : ∀ name ∈ term.freeVars, name ∈ component) :
    (∃ assignment, (FirstOrder.action signature).Models assignment new ∧
      assignment.applyTerm term = value) ↔
    ∃ assignment, (FirstOrder.action signature).Models assignment old ∧
      assignment.applyTerm term = value := by
  apply possible_iff preserves restriction
  intro first second agree
  change first.applyTerm term = value ↔ second.applyTerm term = value
  rw [Subst.applyTerm_congr (t := term) (fun name member => agree name (supported name member))]

/-- Reflecting every local entailment is sufficient for actual model extension. -/
theorem conservative_of_entails_reflection (component : Set signature.vars)
    (old new : EquationStore (Term signature))
    (reflection : ∀ observation : Subst signature → Prop, ReadsOnly component observation →
      (FirstOrder.action signature).Entails new observation →
      (FirstOrder.action signature).Entails old observation) : ConservativeOn component old new := by
  classical
  intro first firstModel
  by_contra missing
  have refuted : (FirstOrder.action signature).Entails new
      (fun assignment => ¬ ∀ name ∈ component, assignment name = first name) := by
    intro second secondModel agree
    exact missing ⟨second, secondModel, agree⟩
  exact reflection _
    (fun left right agree => not_congr (component_agreement_reads_only component first left right agree))
    refuted first firstModel (fun _ _ => rfl)

theorem conservative_iff_entails_reflection (component : Set signature.vars)
    (old new : EquationStore (Term signature))
    (restriction : (FirstOrder.action signature).Refines new old) :
    ConservativeOn component old new ↔
      ∀ observation : Subst signature → Prop, ReadsOnly component observation →
        (FirstOrder.action signature).Entails new observation →
        (FirstOrder.action signature).Entails old observation := by
  constructor
  · intro preserves observation reads entailed
    exact (entails_iff preserves restriction observation reads).mp entailed
  · exact conservative_of_entails_reflection component old new

/-- An already implied tell preserves every model, even if normalization
replaces the displayed generator with its already determined value. -/
theorem conservative_of_entailed (component : Set signature.vars)
    (old added : EquationStore (Term signature))
    (implied : (FirstOrder.action signature).Refines old added) :
    ConservativeOn component old (old ++ added) := by
  intro first model
  exact ⟨first, ((FirstOrder.action signature).models_append _ _ _).mpr
    ⟨model, implied first model⟩, fun _ _ => rfl⟩

/-- Glue the old protected interpretation to a consistent new interpretation
outside the component. Each equation is justified by its actual support. -/
theorem conservative_of_closed_avoiding [DecidableEq signature.vars] (component : Set signature.vars)
    (old added : EquationStore (Term signature)) (closed : Closed component old)
    (avoids : Avoids component added)
    (consistent : (FirstOrder.action signature).Consistent (old ++ added)) :
    ConservativeOn component old (old ++ added) := by
  classical
  intro first firstModel
  obtain ⟨second, secondModel⟩ := consistent
  let glued : Subst signature := fun name => if name ∈ component then first name else second name
  refine ⟨glued, ?_, fun name inside => by simp [glued, inside]⟩
  intro equation member
  rcases List.mem_append.mp member with inOld | inAdded
  · rcases closed equation inOld with inside | outside
    · exact (solves_congr (fun name inEquation => by
        simp [glued, inside name inEquation])).mpr (firstModel equation inOld)
    · exact (solves_congr (fun name inEquation => by
        simp [glued, outside name inEquation])).mpr
          (secondModel equation (List.mem_append_left _ inOld))
  · exact (solves_congr (fun name inEquation => by
      simp [glued, avoids equation inAdded name inEquation])).mpr
        (secondModel equation (List.mem_append_right _ inAdded))

variable {O : Type*} [DecidableEq O]

theorem selected_conservative_of_entailed (component : Set signature.vars)
    (label : O → Term signature) (rule : RuleInstance (Term signature))
    (picked : Selection O) (before : Configuration (Term signature) O)
    (implied : (FirstOrder.action signature).Refines before.equations
      (GuardFreeProcessOrders.added label rule picked)) :
    ConservativeOn component before.equations (picked.result label rule before).equations := by
  rw [GuardFreeProcessOrders.result_equations]
  exact conservative_of_entailed component _ _ implied

theorem selected_conservative_of_closed_avoiding [DecidableEq signature.vars] (component : Set signature.vars)
    (label : O → Term signature) (rule : RuleInstance (Term signature))
    (picked : Selection O) (before : Configuration (Term signature) O)
    (valid : picked.Valid (FirstOrder.action signature) label rule before)
    (closed : Closed component before.equations)
    (avoids : Avoids component (GuardFreeProcessOrders.added label rule picked)) :
    ConservativeOn component before.equations (picked.result label rule before).equations := by
  rw [GuardFreeProcessOrders.result_equations]
  apply conservative_of_closed_avoiding component _ _ closed avoids
  simpa only [GuardFreeProcessOrders.problem_eq] using valid.consistent

/-- A real firing supplies restriction; it does not supply noninterference. -/
theorem step_possible_iff {component : Set signature.vars} {label : O → Term signature}
    {rule : RuleInstance (Term signature)} {before after : Configuration (Term signature) O}
    (step : Step (FirstOrder.action signature) label rule before after)
    (preserves : ConservativeOn component before.equations after.equations)
    (observation : Subst signature → Prop) (reads : ReadsOnly component observation) :
    (∃ assignment, (FirstOrder.action signature).Models assignment after.equations ∧ observation assignment) ↔
    ∃ assignment, (FirstOrder.action signature).Models assignment before.equations ∧ observation assignment :=
  possible_iff preserves step.refines observation reads

theorem step_verdicts_iff {component : Set signature.vars} {label : O → Term signature}
    {rule : RuleInstance (Term signature)} {before after : Configuration (Term signature) O}
    (step : Step (FirstOrder.action signature) label rule before after)
    (preserves : ConservativeOn component before.equations after.equations)
    (observation : Subst signature → Prop) (reads : ReadsOnly component observation) :
    ((FirstOrder.action signature).Entails after.equations observation ↔
      (FirstOrder.action signature).Entails before.equations observation) ∧
    ((FirstOrder.action signature).Entails after.equations (fun assignment => ¬ observation assignment) ↔
      (FirstOrder.action signature).Entails before.equations (fun assignment => ¬ observation assignment)) :=
  verdicts_iff preserves step.refines observation reads

/-- Path-level preservation uses each actual step's restriction and composes
the supplied model-extension witnesses. No schedule or fairness is assumed. -/
theorem step_chain_observations (component : Set signature.vars)
    (label : O → Term signature) (rules : Nat → RuleInstance (Term signature))
    (states : Nat → Configuration (Term signature) O)
    (steps : ∀ n, Step (FirstOrder.action signature) label (rules n) (states n) (states (n + 1)))
    (preserves : ∀ n, ConservativeOn component (states n).equations (states (n + 1)).equations)
    (n : Nat) (observation : Subst signature → Prop) (reads : ReadsOnly component observation) :
    ((∃ assignment, (FirstOrder.action signature).Models assignment (states n).equations ∧
      observation assignment) ↔
      ∃ assignment, (FirstOrder.action signature).Models assignment (states 0).equations ∧
        observation assignment) ∧
    ((FirstOrder.action signature).Entails (states n).equations observation ↔
      (FirstOrder.action signature).Entails (states 0).equations observation) ∧
    ((FirstOrder.action signature).Entails (states n).equations (fun assignment => ¬ observation assignment) ↔
      (FirstOrder.action signature).Entails (states 0).equations (fun assignment => ¬ observation assignment)) := by
  have restriction : ∀ index, (FirstOrder.action signature).Refines
      (states index).equations (states 0).equations := by
    intro index
    induction index with
    | zero => exact (FirstOrder.action signature).refines_refl _
    | succ index ih => exact (FirstOrder.action signature).refines_trans (steps index).refines ih
  have extended := conservative_chain component (fun index => (states index).equations) preserves n
  exact ⟨possible_iff extended (restriction n) observation reads,
    verdicts_iff extended (restriction n) observation reads⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrderConservativeExtension
