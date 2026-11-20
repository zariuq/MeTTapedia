import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.RuleBuilder
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.ControlProtocol

/-!
# Reading the result of an actual done-pattern bind

A public result is returned only after the source language has equated the
machine's reply with the done pattern. Reading that returned result therefore
gives a reading of the original machine reply with the same done payload.
This is a law of the actual source store and contextual substitution.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.PublicReadout

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage SourceLanguage.Elaboration

def pattern {X : Type} {family : X → MetaArity MSig}
    (result : Term (signature MSig family) [] ()) : Term (signature MSig family) [] () :=
  Toolkit.tupleAt [Toolkit.symAt doneTag, result]

theorem instantiate_pattern {X Y : Type} {one : X → MetaArity MSig} {two : Y → MetaArity MSig}
    (assignment : Assignment one two) (result : Term (signature MSig one) [] ()) :
    instantiate assignment (pattern result) = pattern (instantiate assignment result) := by
  rw [pattern, RuleBuilder.instantiate_tuple]
  rfl

theorem include_done {X : Type} (family : X → MetaArity MSig) (value : MClosed) :
    pattern (Rigid.includeTerm family value) = Rigid.includeTerm family (doneC value) := by
  simpa only [pattern, doneC, List.map_cons, List.map_nil] using
    (DataEmbedding.include_nodeC family doneTag [value]).symm

theorem bind_reads_original {κ : Keys MSig} (store : List (Constraint κ [] ()))
    (result reply : Data κ [] ()) (site : κ.Site) (scope : Nat) (value : MClosed)
    (read : Reads (store ++ [(instantiate (openAt κ site scope) (pattern result), reply)])
      (instantiate (openAt κ site scope) result) value) :
    Reads store reply (doneC value) := by
  obtain ⟨X, family, assignment, solved, returned⟩ := read
  obtain ⟨old, bound⟩ := (models_append assignment _ _).mp solved
  have equation := (models_singleton assignment _).mp bound
  have done : instantiate assignment (instantiate (openAt κ site scope) (pattern result)) =
      Rigid.includeTerm family (doneC value) := by
    rw [instantiate_pattern, instantiate_pattern, returned]
    exact include_done family value
  exact ⟨X, family, assignment, old, equation.symm.trans done⟩

/-- A live successful bind cannot have read a reply with another literal
head. An unrelated or incomplete helper reply is not a public result. -/
theorem other_head_not_a_result {κ : Keys MSig} (store : List (Constraint κ [] ()))
    (result reply : Data κ [] ()) (site : κ.Site) (scope : Nat) (value : MClosed)
    {head : String} (headed : literalHead reply = some head) (different : head ≠ doneTag) :
    ¬ Reads (store ++ [(instantiate (openAt κ site scope) (pattern result), reply)])
      (instantiate (openAt κ site scope) result) value := by
  intro read
  have original := bind_reads_original store result reply site scope value read
  have heads := literalHead_of_reads headed original
  exact different (Option.some.inj heads.symm)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.PublicReadout

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.PublicReadout.bind_reads_original
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.PublicReadout.other_head_not_a_result
