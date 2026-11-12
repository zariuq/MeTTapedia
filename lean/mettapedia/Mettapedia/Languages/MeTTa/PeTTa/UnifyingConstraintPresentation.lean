import Mettapedia.Languages.MeTTa.PeTTa.EagerDFS
import Mettapedia.Languages.MeTTa.PeTTa.UnifyingRefinement

/-!
# Solved branch substitutions as source constraint presentations

The streaming unifier retains a solved substitution; the destination source
judgment retains equations. This adapter uses the existing source term codec
and logical solver. It does not define source admission by a native answer.
Readback and model laws are separate from unifier completeness and operational
simulation of an entire producer.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.UnifyingConstraintPresentation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)

open EagerDFS

/-- First-match lookup is the runtime substitution's actual meaning. -/
def environment (bindings : Subst) : Destination.Environment := fun name =>
  match Subst.lookup bindings name with
  | none => .var name
  | some value => Destination.encode value

theorem read_expression (model : Destination.Environment) (items : List Atom) :
    Destination.read model (.expression items) = .expression (items.map (Destination.read model)) := by
  simp only [Destination.read,Destination.encode,Mettapedia.Logic.LP.Subst.applyTerm,Destination.decode]
  apply congrArg Atom.expression
  apply List.ext_getElem
  · simp
  · intro index firstBound secondBound
    simp only [List.getElem_ofFn,List.getElem_map,Fin.getElem_fin,Destination.read]

private theorem resolved_list (bindings : Subst) (items : List Atom) :
    applySubst.applySubstList bindings items = items.map (Unifying.resolve bindings) := by
  induction items with
  | nil => rfl
  | cons first rest ih => simp only [applySubst.applySubstList,List.map_cons,ih]

theorem read_environment (bindings : Subst) (term : Atom) :
    Destination.read (environment bindings) term = Unifying.resolve bindings term := by
  cases term with
  | var name =>
      cases found : Subst.lookup bindings name with
      | none => simp [Destination.read,Destination.encode,Destination.decode,
          environment,Unifying.resolve,applySubst,found]
      | some value => simp [Destination.read,Destination.encode,
          environment,Unifying.resolve,applySubst,found]
  | symbol name => simp [Destination.read,Destination.encode,Destination.decode,Unifying.resolve,applySubst]
  | grounded value => simp [Destination.read,Destination.encode,Destination.decode,Unifying.resolve,applySubst]
  | expression items =>
      rw [read_expression]
      simp only [Unifying.resolve,applySubst,resolved_list,Atom.expression.injEq]
      apply List.map_congr_left
      intro item present
      exact read_environment bindings item
termination_by sizeOf term
decreasing_by
  simp_wf
  exact Nat.lt_trans (List.sizeOf_lt_of_mem present) (by omega)

/-- Present the actual first-lookup graph, retaining its key occurrences.
An obsolete shadowed list entry is not a second logical assignment. -/
def presentation (bindings : Subst) : Destination.Equations :=
  bindings.map fun binding => (.var binding.1,Unifying.resolve bindings (.var binding.1))

private theorem lookup_has_key {bindings : Subst} {name : String} {value : Atom}
    (found : Subst.lookup bindings name = some value) : ∃ binding ∈ bindings, binding.1 = name := by
  induction bindings with
  | nil => simp [Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup] at found
  | cons first rest ih =>
      by_cases same : first.1 = name
      · exact ⟨first,List.mem_cons_self,same⟩
      · have later : Subst.lookup rest name = some value := by
          simpa [Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup,same] using found
        obtain ⟨binding,present,key⟩ := ih later
        exact ⟨binding,List.mem_cons_of_mem _ present,key⟩

theorem absorbs_of_solves (model : Destination.Environment) (bindings : Subst)
    (solved : Destination.Solves model (presentation bindings)) (term : Atom) :
    Destination.read model (Unifying.resolve bindings term) = Destination.read model term := by
  cases term with
  | symbol name => rfl
  | grounded value => rfl
  | var name =>
      cases found : Subst.lookup bindings name with
      | none => rw [Unifying.resolve_var_free found]
      | some value =>
          obtain ⟨binding,present,key⟩ := lookup_has_key found
          have equation := solved _ (List.mem_map.mpr ⟨binding,present,rfl⟩)
          simpa only [key] using equation.symm
  | expression items =>
      simp only [Unifying.resolve,applySubst,resolved_list,read_expression,Atom.expression.injEq,List.map_map]
      apply List.map_congr_left
      intro item present
      exact absorbs_of_solves model bindings solved item
termination_by sizeOf term
decreasing_by
  simp_wf
  exact Nat.lt_trans (List.sizeOf_lt_of_mem present) (by omega)

/-- A model of the equation graph absorbs exactly the runtime substitution
under every later source observation, not only the currently displayed value. -/
theorem solves_iff_absorbs (model : Destination.Environment) (bindings : Subst) :
    Destination.Solves model (presentation bindings) ↔
      ∀ term, Destination.read model (Unifying.resolve bindings term) = Destination.read model term := by
  constructor
  · exact absorbs_of_solves model bindings
  · intro absorbed pair present
    obtain ⟨binding,present,rfl⟩ := List.mem_map.mp present
    exact (absorbed (.var binding.1)).symm

theorem environment_models_presentation (bindings : Subst) (valid : Unifying.Idempotent bindings) :
    Destination.Solves (environment bindings) (presentation bindings) := by
  apply (solves_iff_absorbs _ _).mpr
  intro term
  rw [read_environment,read_environment]
  exact Unifying.resolve_idem valid term

theorem later_environment_models_earlier {earlier later : Subst} (refined : Unifying.Refines earlier later) :
    Destination.Solves (environment later) (presentation earlier) := by
  apply (solves_iff_absorbs _ _).mpr
  intro term
  rw [read_environment,read_environment]
  exact refined term

end Mettapedia.Languages.MeTTa.PeTTa.UnifyingConstraintPresentation
