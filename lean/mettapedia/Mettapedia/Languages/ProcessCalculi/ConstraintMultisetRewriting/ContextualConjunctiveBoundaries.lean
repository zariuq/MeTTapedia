import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConjunctiveSingleton

/-!
# Empty conjunctions and empty physical worlds have different boundaries

There is exactly one empty candidate tuple. A consistent background admits
that empty conjunction, so its absence is false. A nonempty conjunction has
no tuple in an empty world, independently of the solver's fuel.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConjunctiveBoundaries

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualGuardMatching
open ContextualConjunctiveQueries
open ContextualConjunctiveAbsence

universe u
variable {S : Signature} {Query Local Shared Next : Type} {O : Type u}
  (queries : Query → MetaArity S) (locals : Local → MetaArity S) (captures : Shared → MetaArity S)
  {next : Next → MetaArity S}

def emptyChoice : Fin 0 → O := fun impossible => nomatch impossible

theorem the_empty_tuple_is_enumerated [DecidableEq O] (world : Finset O) :
    emptyChoice (O := O) ∈ candidates world 0 :=
  (mem_candidates world emptyChoice).mpr (fun port => Fin.elim0 port)

theorem empty_query_matches (candidate : Assignment captures next) {Γ : Ctx S} {sort : S.Srt}
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) :
    ContextualConjunctiveQueries.Matches queries locals captures candidate [] rows emptyChoice := by
  let privateDeclarations := sumDeclarations queries (rowLocals locals)
  let extension := Extension.withLocals privateDeclarations next
  refine ⟨extension, (fun name => generator extension.declarations (.inl (.inl name))),
    (fun name => generator extension.declarations (.inl (.inr name))), ?_⟩
  intro port
  exact Fin.elim0 port

theorem consistent_background_refuses_empty_absence (candidate : Assignment captures next)
    {Γ : Ctx S} {sort : S.Srt} (problem : EquationStore (Term (signature S captures) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (world : Finset O)
    (solved : ContextualFrameUnifier.Models candidate problem) :
    ¬ Ask queries locals captures problem [] rows world := by
  intro absent
  exact absent Next next candidate solved emptyChoice (fun port => Fin.elim0 port)
    (empty_query_matches queries locals captures candidate rows)

theorem nonempty_query_has_no_empty_world_tuple [DecidableEq O] {count : Nat} (nonempty : 0 < count) :
    candidates (∅ : Finset O) count = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro chosen member
  exact Finset.notMem_empty _ ((mem_candidates ∅ chosen).mp member ⟨0, nonempty⟩)

variable [DecidableEq Query] [DecidableEq Local] [DecidableEq Shared] [DecidableEq S.Srt]
  [∀ sort, DecidableEq (S.Op sort)] [DecidableEq O]

theorem no_fuel_can_certify_absence_of_a_consistent_empty_conjunction
    (candidate : Assignment captures next) (fuel : Nat) {Γ : Ctx S} {sort : S.Srt}
    (problem : EquationStore (Term (signature S captures) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (world : Finset O)
    (solved : ContextualFrameUnifier.Models candidate problem) :
    certifies queries locals captures fuel problem [] rows world = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  exact consistent_background_refuses_empty_absence queries locals captures candidate problem rows world solved
    (certifies_sound queries locals captures fuel problem [] rows world accepted)

theorem empty_world_certifies_a_nonempty_query (fuel : Nat) {Γ : Ctx S} {sort : S.Srt}
    (problem : EquationStore (Term (signature S captures) Γ sort))
    (patterns : List (Term (signature S (queryFamily queries captures)) Γ sort))
    (nonempty : 0 < patterns.length) (rows : O → ContextualStoredRows.Row locals captures Γ sort) :
    certifies queries locals captures fuel problem patterns rows ∅ = true := by
  simp only [certifies, nonempty_query_has_no_empty_world_tuple nonempty, Finset.notMem_empty,
    false_implies, implies_true, decide_true]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConjunctiveBoundaries
