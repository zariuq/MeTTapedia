import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExtensionAmalgamation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseWitnesses

/-!
# Finite row matches construct a joint clause model without changing bindings

The query and caller assignment are fixed before the individual nonbinding
matches. Their fresh witnesses are amalgamated, then placed in the actual
per-port scopes of the source problem. Existing shared names enter the
result by an injective extension. Per-port choices of query assignments
are not sufficient for this construction.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualMatchedClauseModels

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualConditionalRows ContextualConditionalRealizations ContextualClauseWitnesses
open ContextualGuardMatching

variable {S : Signature} {Query Local Shared Next O : Type}
    (queries : Query → MetaArity S) (locals : Local → MetaArity S) (captures : Shared → MetaArity S)
    {next : Next → MetaArity S} {Γ : Ctx S} {sort : S.Srt}

theorem model_from_matches (picked : Selection O)
    (code : RuleInstance (Term (signature S (queryFamily queries captures)) Γ sort))
    (rows : O → Row locals captures Γ sort) (before : ContextualResidual.Problem captures)
    (takeShape : code.take.length = picked.taken.length) (readShape : code.read.length = picked.read.length)
    (query : Assignment queries next) (candidate : Assignment captures next)
    (previous : ContextualResidual.Models candidate before)
    (tells : ContextualFrameUnifier.Models (valuation queries captures query candidate) code.tell)
    (taken : ∀ port : Fin picked.taken.length, Matches locals captures candidate
      (instantiate (valuation queries captures query candidate) (code.take.get ⟨port.val, takeShape.symm ▸ port.isLt⟩))
      (rows (picked.taken.get port)))
    (read : ∀ port : Fin picked.read.length, Matches locals captures candidate
      (instantiate (valuation queries captures query candidate) (code.read.get ⟨port.val, readShape.symm ▸ port.isLt⟩))
      (rows (picked.read.get port))) :
    ∃ extension : Extension next, ∃ model : Assignment (family queries locals captures) extension.declarations,
      ContextualResidual.Models model (ContextualConditionalSourceProblem.problem queries locals captures picked code rows before) ∧
      queryBodies queries locals captures model = Assignment.compose extension.assignment query ∧
      caller queries locals captures model = Assignment.compose extension.assignment candidate := by
  let takes : List (Term (signature S next) Γ sort × Row locals captures Γ sort) := List.ofFn
    fun port : Fin picked.taken.length =>
      (instantiate (valuation queries captures query candidate) (code.take.get ⟨port.val, takeShape.symm ▸ port.isLt⟩),
        rows (picked.taken.get port))
  let reads : List (Term (signature S next) Γ sort × Row locals captures Γ sort) := List.ofFn
    fun port : Fin picked.read.length =>
      (instantiate (valuation queries captures query candidate) (code.read.get ⟨port.val, readShape.symm ▸ port.isLt⟩),
        rows (picked.read.get port))
  have matched : ∀ request ∈ takes ++ reads, Matches locals captures candidate request.1 request.2 := by
    intro request member
    rcases List.mem_append.mp member with member | member
    · obtain ⟨port, rfl⟩ := List.mem_ofFn.mp member
      exact taken port
    · obtain ⟨port, rfl⟩ := List.mem_ofFn.mp member
      exact read port
  obtain ⟨extension, filler, realized⟩ := finite_realizations locals captures candidate (takes ++ reads) matched
  let witness : Witness queries locals captures picked code rows before takeShape readShape extension.declarations := by
    refine ⟨Assignment.compose extension.assignment query, Assignment.compose extension.assignment candidate, filler,
      ContextualResidual.models_compose previous extension.assignment, ?_, ?_, ?_⟩
    · rw [valuation_future]
      exact ContextualFrameUnifier.models_compose tells extension.assignment
    · intro port
      have row := realized _ (List.mem_append_left reads (List.mem_ofFn.mpr ⟨port, rfl⟩))
      rw [valuation_future, Assignment.instantiate_compose]
      exact row
    · intro port
      have row := realized _ (List.mem_append_right takes (List.mem_ofFn.mpr ⟨port, rfl⟩))
      rw [valuation_future, Assignment.instantiate_compose]
      exact row
  obtain ⟨model, solved, queryFixed, capturesFixed⟩ := witness.gives_model queries locals captures
  exact ⟨extension, model, solved, queryFixed, capturesFixed⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualMatchedClauseModels
