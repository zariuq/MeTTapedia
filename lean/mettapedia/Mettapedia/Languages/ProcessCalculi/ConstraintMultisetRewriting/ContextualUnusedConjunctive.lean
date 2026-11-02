import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualUnusedMatching
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConjunctiveQueries

/-!
# Shared query assignments and fresh row uses survive unused declarations

The common extension is shared by the whole tuple. Query-local images remain
shared across ports; row-local images remain indexed by read use, including
two uses of the same physical row. Caller captures are unchanged.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConjunctiveQueries

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)
open ContextualGuardMatching (Extension)
open ContextualPrefixModels

universe u
variable {S : Signature} {Extra Query Local Shared Next : Type} {O : Type u}
  (queries : Query → MetaArity S) (locals : Local → MetaArity S)
  (unused : Extra → MetaArity S) (captures : Shared → MetaArity S)
  {next : Next → MetaArity S}

theorem matches_inclusion_iff (candidate : Assignment captures next) {Γ : Ctx S} {sort : S.Srt}
    (patterns : List (Term (signature S (queryFamily queries captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (chosen : Fin patterns.length → O) :
    Matches queries locals captures (Assignment.compose (inclusion unused next) candidate) patterns rows chosen ↔
      Matches queries locals captures candidate patterns rows chosen := by
  constructor
  · rintro ⟨extension, queryBodies, rowBodies, agrees⟩
    refine ⟨extension.restrictUnused unused, queryBodies, rowBodies, ?_⟩
    intro port
    have matched := agrees port
    rw [ContextualGuardMatching.instance_restrict_unused locals unused extension
      (fun name => rowBodies (ScopedVar.at (rowScope port) name)) candidate,
      ContextualGuardMatching.instance_restrict_unused queries unused extension queryBodies candidate] at matched
    exact matched
  · rintro ⟨extension, queryBodies, rowBodies, agrees⟩
    refine ⟨extension.addUnused unused,
      Assignment.compose (inclusion unused extension.declarations) queryBodies,
      Assignment.compose (inclusion unused extension.declarations) rowBodies, ?_⟩
    intro port
    have left := congrArg
      (fun assignment : Assignment (ContextualSelectionViews.source locals captures)
          (extended unused extension.declarations) =>
        instantiate assignment (ContextualStoredRows.asTemplate locals captures (rows (chosen port))))
      (ContextualGuardMatching.instance_add_unused locals unused extension
        (fun name => rowBodies (ScopedVar.at (rowScope port) name)) candidate)
    have right := congrArg
      (fun assignment : Assignment (queryFamily queries captures) (extended unused extension.declarations) =>
        instantiate assignment (patterns.get port))
      (ContextualGuardMatching.instance_add_unused queries unused extension queryBodies candidate)
    simp only [Assignment.instantiate_compose] at left right
    have mapped := congrArg (instantiate (inclusion unused extension.declarations)) (agrees port)
    exact left.symm.trans (mapped.trans right)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConjunctiveQueries
