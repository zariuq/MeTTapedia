import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.PublicAnswers
import Mettapedia.OSLF.Syntax.ContextualSupportSubstitution

/-!
# The actual binder-equation program satisfies source hosting's scope clauses

Each equation's holes are assigned to unopened names of its own site. This
supplies the exact existing scoping and arrow-fragment hypotheses for every
finite binder program, including the interpreter's generated table.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ProgramScope

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage SourceLanguage.Elaboration

variable (rows : List (ProgramBinders.Equation MSig [] ()))

theorem embedded_names (index : Fin rows.length)
    (term : Term (signature MSig (rows.get index).arity) [] ()) :
    NamesIn [index] (instantiate (BinderCore.embedAt rows index) term) := by
  apply bounded_instantiate
  intro hole _ name member
  change name ∈ support (generator (fam (BinderCore.keys rows)) ⟨[], ⟨index, hole⟩⟩) at member
  have same : name = ⟨[], ⟨index, hole⟩⟩ := by
    simpa only [support_generator, List.mem_singleton] using member
  subst name
  exact ⟨rfl, List.mem_singleton_self _⟩

theorem equations (D : Discipline MSig [] ()) :
    ∀ equation ∈ (BinderCore.program rows (Ty := D.Ty)).equations,
      equation.Scoped ∧ (equation.site :: equation.rhs.sites).Nodup ∧ Hosting.ArrowComp equation.rhs := by
  intro equation member
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
  exact ⟨⟨embedded_names rows index _, embedded_names rows index _⟩,
    List.nodup_singleton _, trivial⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ProgramScope

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ProgramScope.equations
