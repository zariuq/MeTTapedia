import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalRowPacking
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualScheduleRowAssembly
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OccurrenceAllocationRenaming

/-!
# One conditional row view for entry occurrences and authored creations

The view takes source data: entry rows, their capture transport and saved
creation origins. It is independent of the source clause grammar. Private
declaration banks are packed once; initial physical names read entry rows,
and allocated names read their authored creation descriptions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualOccurrenceViews

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConditionalRows ContextualSourceSchedules

variable {S : Signature} {O First Entry Current Next : Type} [DecidableEq O]
    (first : First → MetaArity S) (entry : Entry → MetaArity S) (current : Current → MetaArity S)
    {next : Next → MetaArity S} {Γ : Ctx S} {sort : S.Srt}
    (origins : O → Origin current Γ sort)

def Variables : Option O → Type
  | none => First
  | some occurrence => (origins occurrence).Private

def declarations : ∀ index, Variables (First := First) current origins index → MetaArity S
  | none => first
  | some occurrence => (origins occurrence).privateDecl

abbrev bank := ContextualConditionalRowPacking.family
  (Variables (First := First) current origins) (declarations first current origins)

def inputRow (rows : O → Row first entry Γ sort) (transport : Assignment entry current) (occurrence : O) :
    Row (bank first current origins) current Γ sort :=
  ContextualConditionalRowPacking.pack (Variables (First := First) current origins) (declarations first current origins)
    current none ((rows occurrence).map first entry transport)

def creationRow (occurrence : O) : Row (bank first current origins) current Γ sort :=
  ContextualConditionalRowPacking.pack (Variables (First := First) current origins) (declarations first current origins)
    current (some occurrence) (origins occurrence).asRow

def physicalRows (rows : O → Row first entry Γ sort) (transport : Assignment entry current) :
    OccurrenceAllocationRenaming.Name O → Row (bank first current origins) current Γ sort
  | .inl occurrence => inputRow first entry current origins rows transport occurrence
  | .inr (_, occurrence) => creationRow first current origins occurrence

theorem input_matches (rows : O → Row first entry Γ sort) (transport : Assignment entry current)
    (occurrence : O) (candidate : Assignment current next) (pattern : Term (signature S next) Γ sort) :
    Matches (bank first current origins) current candidate pattern
        (inputRow first entry current origins rows transport occurrence) ↔
      Matches first entry (Assignment.compose candidate transport) pattern (rows occurrence) :=
  (ContextualConditionalRowPacking.matches_iff (Variables (First := First) current origins) (declarations first current origins)
    current none _ candidate pattern).trans (matches_map_iff first entry transport candidate pattern _)

theorem creation_matches (occurrence : O) (candidate : Assignment current next)
    (pattern : Term (signature S next) Γ sort) :
    Matches (bank first current origins) current candidate pattern (creationRow first current origins occurrence) ↔
      (origins occurrence).Instances candidate pattern :=
  (ContextualConditionalRowPacking.matches_iff (Variables (First := First) current origins) (declarations first current origins)
    current (some occurrence) _ candidate pattern).trans ((origins occurrence).asRow_instances candidate pattern)

/-- Geometry and an entry-origin identity suffice; no source guard or model
preservation premise is part of the view construction. -/
theorem physical_instances (rows : O → Row first entry Γ sort) (transport : Assignment entry current)
    (name : O → OccurrenceAllocationRenaming.Name O)
    (projects : ∀ occurrence, OccurrenceAllocationRenaming.erase (name occurrence) = occurrence)
    (retained : ∀ occurrence, name occurrence = .inl occurrence →
      origins occurrence = Origin.retained first entry (rows occurrence) transport)
    (occurrence : O) (candidate : Assignment current next) (pattern : Term (signature S next) Γ sort) :
    Matches (bank first current origins) current candidate pattern
        (physicalRows first entry current origins rows transport (name occurrence)) ↔
      (origins occurrence).Instances candidate pattern := by
  cases selected : name occurrence with
  | inl original =>
      have same := projects occurrence
      rw [selected] at same
      change original = occurrence at same
      subst original
      rw [retained occurrence selected]
      exact input_matches first entry current origins rows transport occurrence candidate pattern
  | inr created =>
      have same := projects occurrence
      rw [selected] at same
      change created.2 = occurrence at same
      change Matches _ _ candidate pattern (creationRow first current origins created.2) ↔ _
      rw [same]
      exact creation_matches first current origins occurrence candidate pattern

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualOccurrenceViews
