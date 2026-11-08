import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualInformation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConjunctiveAskTransport

/-!
# Joined absence is an information obligation with its query interface intact

The existing joined query shares its query variables across all source ports,
freshens each stored-schema use independently and returns no caller binding.
This profile joins those obligations to the ordinary information admission;
it introduces no new source syntax or transition rule.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualInformationQueries

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

universe u
variable {S : Signature} {Query Local Shared Next : Type} {O : Type u}
  (queries : Query → MetaArity S) (locals : Local → MetaArity S)
  {captures : Shared → MetaArity S} {next : Next → MetaArity S}
  {Γ : Ctx S} {sort : S.Srt}

structure Admitted
    (problem : EquationStore (Term (signature S captures) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (world : Finset O)
    (checks : List (Check (Term (signature S captures) Γ sort)))
    (joined : List (List (Term (signature S (ContextualConjunctiveQueries.queryFamily queries captures)) Γ sort))) : Prop where
  ordinary : ContextualInformation.Admitted locals problem rows world checks
  absent : ∀ patterns ∈ joined, ContextualConjunctiveAbsence.Ask queries locals captures problem patterns rows world

theorem no_joined_iff
    (problem : EquationStore (Term (signature S captures) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (world : Finset O)
    (checks : List (Check (Term (signature S captures) Γ sort))) :
    Admitted queries locals problem rows world checks [] ↔
      ContextualInformation.Admitted locals problem rows world checks :=
  ⟨fun admitted => admitted.ordinary, fun ordinary => ⟨ordinary, by simp⟩⟩

theorem Admitted.transport
    {problem : EquationStore (Term (signature S captures) Γ sort)}
    {rows : O → ContextualStoredRows.Row locals captures Γ sort} {world : Finset O}
    {checks : List (Check (Term (signature S captures) Γ sort))}
    {joined : List (List (Term (signature S (ContextualConjunctiveQueries.queryFamily queries captures)) Γ sort))}
    (admitted : Admitted queries locals problem rows world checks joined)
    (change : Assignment captures next)
    (compatible : ContextualFrameUnifier.Solvable
      (ContextualFrameUnifier.mapProblem change problem)) :
    Admitted queries locals (ContextualFrameUnifier.mapProblem change problem)
      (fun occurrence => (rows occurrence).map locals change) world
      (checks.map (Check.map (instantiate change)))
      (joined.map (ContextualConjunctiveQueries.mapPatterns queries change)) := by
  refine ⟨⟨compatible, ?_⟩, ?_⟩
  · intro check member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    exact ContextualGuardSemantics.Ask.transport locals (admitted.ordinary.checks original present) change
  · intro patterns member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    exact ContextualConjunctiveAbsence.Ask.transport queries locals captures problem original rows world
      change (admitted.absent original present)

theorem Admitted.refine
    {problem stronger : EquationStore (Term (signature S captures) Γ sort)}
    {rows : O → ContextualStoredRows.Row locals captures Γ sort} {world : Finset O}
    {checks : List (Check (Term (signature S captures) Γ sort))}
    {joined : List (List (Term (signature S (ContextualConjunctiveQueries.queryFamily queries captures)) Γ sort))}
    (admitted : Admitted queries locals problem rows world checks joined)
    (refinement : ContextualInformation.Refines stronger problem)
    (compatible : ContextualFrameUnifier.Solvable stronger) :
    Admitted queries locals stronger rows world checks joined :=
  ⟨ContextualInformation.admitted_refinement locals refinement compatible admitted.ordinary,
    fun patterns present Future future candidate model => admitted.absent patterns present Future future candidate
      (refinement Future future candidate model)⟩

/-- The executable refuter supplies the joined obligations; fuel exhaustion
is not a refutation and cannot construct this admission. -/
theorem of_certified_refutations [DecidableEq O] [DecidableEq Query] [DecidableEq Local]
    [DecidableEq Shared] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
    (fuel : Nat) (problem : EquationStore (Term (signature S captures) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (world : Finset O)
    (checks : List (Check (Term (signature S captures) Γ sort)))
    (joined : List (List (Term (signature S (ContextualConjunctiveQueries.queryFamily queries captures)) Γ sort)))
    (ordinary : ContextualInformation.Admitted locals problem rows world checks)
    (refuted : ∀ patterns ∈ joined,
      ContextualConjunctiveAbsence.certifies queries locals captures fuel problem patterns rows world = true) :
    Admitted queries locals problem rows world checks joined :=
  ⟨ordinary, fun patterns present => ContextualConjunctiveAbsence.certifies_sound queries locals captures
    fuel problem patterns rows world (refuted patterns present)⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualInformationQueries
