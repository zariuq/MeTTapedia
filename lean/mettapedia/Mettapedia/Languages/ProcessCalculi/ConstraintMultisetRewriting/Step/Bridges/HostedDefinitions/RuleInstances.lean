import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.RuleBuilder

/-!
# Closed instances of actual finite source equations

The helper lemmas retain equation-list membership. They expose the existing
binder-core rewrite relation, rather than introducing a new machine step.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.RuleInstances

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage SourceLanguage.Elaboration

abbrev Rule := ProgramBinders.Equation MSig [] ()
abbrev Steps (rows : List Rule) := Relation.ReflTransGen (ProgramBinders.Rewrites rows.get)

def left (rule : Rule) (environment : rule.Ground) : MClosed :=
  ProgramBinders.decode (instantiate (rule.assign environment (ProgramBinders.ground MSig)) rule.lhs)

def right (rule : Rule) (environment : rule.Ground) : MClosed :=
  ProgramBinders.decode (instantiate (rule.assign environment (ProgramBinders.ground MSig)) rule.rhs)

theorem answer (rule : Rule) (environment : rule.Ground) :
    ProgramBinders.Answers rule (left rule environment) (right rule environment) :=
  ⟨environment, (ProgramBinders.include_decode _).symm, (ProgramBinders.include_decode _).symm⟩

theorem of_member {rows : List Rule} {rule : Rule} {before after : MClosed}
    (member : rule ∈ rows) (answered : ProgramBinders.Answers rule before after) :
    ProgramBinders.Rewrites rows.get before after := by
  obtain ⟨index, small, rfl⟩ := List.getElem_of_mem member
  exact ⟨⟨index, small⟩, answered⟩

theorem fire {rows : List Rule} (rule : Rule) (member : rule ∈ rows) (environment : rule.Ground) :
    ProgramBinders.Rewrites rows.get (left rule environment) (right rule environment) :=
  of_member member (answer rule environment)

theorem template {rows : List Rule} {n : Nat} (lhs rhs : RuleBuilder.Template n)
    (member : RuleBuilder.equation lhs rhs ∈ rows) (environment : Fin n → MClosed) :
    ProgramBinders.Rewrites rows.get (RuleBuilder.materialize environment lhs) (RuleBuilder.materialize environment rhs) :=
  of_member member (RuleBuilder.instantiated_answer lhs rhs environment)

theorem rewrite_mono {one two : List Rule} (included : ∀ rule ∈ one, rule ∈ two)
    {before after : MClosed} (step : ProgramBinders.Rewrites one.get before after) :
    ProgramBinders.Rewrites two.get before after := by
  obtain ⟨index, answered⟩ := step
  exact of_member (included _ (List.get_mem _ _)) answered

theorem steps_mono {one two : List Rule} (included : ∀ rule ∈ one, rule ∈ two)
    {before after : MClosed} (steps : Steps one before after) : Steps two before after := by
  induction steps with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (rewrite_mono included step)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.RuleInstances
