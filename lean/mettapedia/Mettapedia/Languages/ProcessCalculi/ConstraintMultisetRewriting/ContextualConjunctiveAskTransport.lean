import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConjunctiveCaptureTransport
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConjunctiveAbsence
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPrefixAsks

/-!
# Original joined-absence asks transport and reflect unused declarations

The port bijection transports every occupied tuple, including repeated rows
and the empty tuple. Query-local images stay shared and row locals remain
private per use. All quantifiers are the existing all-future ask contract.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConjunctiveAbsence

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualPrefixModels

universe u
variable {S : Signature} {Extra Query Local Shared Later Next : Type} {O : Type u}
  (queries : Query → MetaArity S) (locals : Local → MetaArity S) (captures : Shared → MetaArity S)
  {later : Later → MetaArity S} {next : Next → MetaArity S}

theorem holds_after_capture_transport (change : Assignment captures later)
    (candidate : Assignment later next) {Γ : Ctx S} {sort : S.Srt}
    (patterns : List (Term (signature S (queryFamily queries captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (world : Finset O) :
    Holds queries locals later candidate (mapPatterns queries change patterns)
        (fun occurrence => (rows occurrence).map locals change) world ↔
      Holds queries locals captures (Assignment.compose candidate change) patterns rows world := by
  constructor
  · intro absent chosen present matched
    exact absent (mapChoice queries change patterns chosen)
      (fun port => present (sourcePort queries change patterns port))
      ((ContextualConjunctiveQueries.matches_after_capture_transport queries locals change candidate
        patterns rows chosen).mpr matched)
  · intro absent chosen present matched
    let original := restoreChoice queries change patterns chosen
    have oldMatch : ContextualConjunctiveQueries.Matches queries locals captures
        (Assignment.compose candidate change) patterns rows original := by
      apply (ContextualConjunctiveQueries.matches_after_capture_transport queries locals change candidate
        patterns rows original).mp
      rw [show mapChoice queries change patterns original = chosen from map_restore_choice queries change patterns chosen]
      exact matched
    exact absent original (fun port => present (targetPort queries change patterns port)) oldMatch

theorem Ask.transport {Γ : Ctx S} {sort : S.Srt}
    (problem : EquationStore (Term (signature S captures) Γ sort))
    (patterns : List (Term (signature S (queryFamily queries captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (world : Finset O)
    (change : Assignment captures later) (admitted : Ask queries locals captures problem patterns rows world) :
    Ask queries locals later (ContextualFrameUnifier.mapProblem change problem)
      (mapPatterns queries change patterns) (fun occurrence => (rows occurrence).map locals change) world := by
  intro Future future candidate solved
  have original := (ContextualFrameUnifier.models_mapProblem change candidate problem).mp solved
  exact (holds_after_capture_transport queries locals captures change candidate patterns rows world).mpr
    (admitted Future future (Assignment.compose candidate change) original)

theorem holds_inclusion_iff (unused : Extra → MetaArity S) (candidate : Assignment captures next)
    {Γ : Ctx S} {sort : S.Srt}
    (patterns : List (Term (signature S (queryFamily queries captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (world : Finset O) :
    Holds queries locals captures (Assignment.compose (inclusion unused next) candidate) patterns rows world ↔
      Holds queries locals captures candidate patterns rows world := by
  simp only [Holds, ContextualConjunctiveQueries.matches_inclusion_iff]

theorem Ask.unused_extension_iff (unused : Extra → MetaArity S) {Γ : Ctx S} {sort : S.Srt}
    (problem : EquationStore (Term (signature S captures) Γ sort))
    (patterns : List (Term (signature S (queryFamily queries captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (world : Finset O) :
    Ask queries locals (extended unused captures) (ContextualFrameUnifier.mapProblem (inclusion unused captures) problem)
        (mapPatterns queries (inclusion unused captures) patterns)
        (fun occurrence => (rows occurrence).map locals (inclusion unused captures)) world ↔
      Ask queries locals captures problem patterns rows world := by
  constructor
  · intro admitted Future future candidate solved
    have lifted := admitted (Extra ⊕ Future) (extended unused future)
      (ContextualStoredRows.liftCaptures unused candidate)
      ((lifted_prefix_models_iff unused candidate problem).mpr solved)
    have original := (holds_after_capture_transport queries locals captures (inclusion unused captures)
      (ContextualStoredRows.liftCaptures unused candidate) patterns rows world).mp lifted
    rw [lifted_capture_assignment] at original
    exact (holds_inclusion_iff queries locals captures unused candidate patterns rows world).mp original
  · intro admitted
    exact Ask.transport queries locals captures problem patterns rows world (inclusion unused captures) admitted

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConjunctiveAbsence
