import Mettapedia.OSLF.Framework.SelectedNativeTypeFoundationTransport

/-!
# Grounded rewrite occurrences

Contextual-signature generation needs an occurrence typing together with
evidence that every carrier named by that typing belongs to the authored
source language. It does not need a modal-profile choice. This record is
therefore the exact atomic input of the profile-free signature compiler.

`SelectedNativeTypeFoundation.Demand` remains the canonical ordered batch
coordinate. `groundedOccurrences` exposes its proof-carrying atoms, while
`demandOfList` reconstructs the same batch coordinate. These maps are inverse
up to proof irrelevance, and both preserve ordered append.
-/

namespace Mettapedia.OSLF.Framework

open Mettapedia.GSLT.LanguageDef

/-- One displayed rewrite occurrence whose complete carrier support is
grounded in the authored source language. -/
structure GroundedRewriteOccurrence (source : ValidatedLanguageDef) where
  typing : DisplayedRewriteTyping source
  grounded : SelectedNativeTypeFoundation.CarrierGrounded typing

namespace GroundedRewriteOccurrence

/-- Grounding evidence is proof-valued, so the occurrence is determined by
its displayed typing. -/
@[ext]
theorem ext {source : ValidatedLanguageDef}
    {first second : GroundedRewriteOccurrence source}
    (typing : first.typing = second.typing) : first = second := by
  cases first
  cases second
  cases typing
  rfl

/-- Structural reindexing transports both the typing and its grounding
certificate. -/
noncomputable def map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (occurrence : GroundedRewriteOccurrence source) :
    GroundedRewriteOccurrence target where
  typing := occurrence.typing.map morphism
  grounded := occurrence.grounded.map morphism

@[simp]
theorem map_typing {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (occurrence : GroundedRewriteOccurrence source) :
    (occurrence.map morphism).typing = occurrence.typing.map morphism :=
  rfl

@[simp]
theorem map_id (source : ValidatedLanguageDef)
    (occurrence : GroundedRewriteOccurrence source) :
    occurrence.map (StructuralMorphism.id source) = occurrence := by
  apply GroundedRewriteOccurrence.ext
  exact DisplayedRewriteTyping.map_id source occurrence.typing

theorem map_comp {first second third : ValidatedLanguageDef}
    (earlier : StructuralMorphism first second)
    (later : StructuralMorphism second third)
    (occurrence : GroundedRewriteOccurrence first) :
    occurrence.map (StructuralMorphism.comp earlier later) =
      (occurrence.map earlier).map later := by
  apply GroundedRewriteOccurrence.ext
  exact DisplayedRewriteTyping.map_comp earlier later occurrence.typing

/-- One grounded occurrence as a singleton foundation demand. -/
def singletonDemand {source : ValidatedLanguageDef}
    (occurrence : GroundedRewriteOccurrence source) :
    SelectedNativeTypeFoundation.Demand source where
  typings := [occurrence.typing]
  grounded := by
    intro typing membership
    have equality : typing = occurrence.typing := List.mem_singleton.mp membership
    subst typing
    exact occurrence.grounded

/-- An ordered list of grounded atoms as one foundation demand. -/
def demandOfList {source : ValidatedLanguageDef}
    (occurrences : List (GroundedRewriteOccurrence source)) :
    SelectedNativeTypeFoundation.Demand source where
  typings := occurrences.map GroundedRewriteOccurrence.typing
  grounded := by
    intro typing membership
    obtain ⟨occurrence, _, rfl⟩ := List.mem_map.mp membership
    exact occurrence.grounded

@[simp]
theorem demandOfList_typings {source : ValidatedLanguageDef}
    (occurrences : List (GroundedRewriteOccurrence source)) :
    (demandOfList occurrences).typings =
      occurrences.map GroundedRewriteOccurrence.typing :=
  rfl

@[simp]
theorem demandOfList_nil (source : ValidatedLanguageDef) :
    demandOfList ([] : List (GroundedRewriteOccurrence source)) =
      SelectedNativeTypeFoundation.Demand.empty source := by
  apply SelectedNativeTypeFoundation.Demand.ext
  rfl

@[simp]
theorem demandOfList_cons {source : ValidatedLanguageDef}
    (occurrence : GroundedRewriteOccurrence source)
    (occurrences : List (GroundedRewriteOccurrence source)) :
    demandOfList (occurrence :: occurrences) =
      (singletonDemand occurrence).append (demandOfList occurrences) := by
  apply SelectedNativeTypeFoundation.Demand.ext
  rfl

@[simp]
theorem demandOfList_append {source : ValidatedLanguageDef}
    (first second : List (GroundedRewriteOccurrence source)) :
    demandOfList (first ++ second) =
      (demandOfList first).append (demandOfList second) := by
  apply SelectedNativeTypeFoundation.Demand.ext
  simp [List.map_append]

/-- A list of grounded occurrences is determined by its typing projection. -/
theorem list_ext {source : ValidatedLanguageDef}
    {first second : List (GroundedRewriteOccurrence source)}
    (typings : first.map GroundedRewriteOccurrence.typing =
      second.map GroundedRewriteOccurrence.typing) : first = second := by
  induction first generalizing second with
  | nil =>
      cases second with
      | nil => rfl
      | cons head tail => simp at typings
  | cons head tail inductionHypothesis =>
      cases second with
      | nil => simp at typings
      | cons other rest =>
          simp only [List.map_cons, List.cons.injEq] at typings
          obtain ⟨headTyping, tailTypings⟩ := typings
          have headEquality : head = other :=
            GroundedRewriteOccurrence.ext headTyping
          subst other
          exact congrArg (List.cons head) (inductionHypothesis tailTypings)

end GroundedRewriteOccurrence

namespace SelectedNativeTypeFoundation.Demand

/-- Expose the exact proof-carrying atoms of an ordered foundation demand. -/
def groundedOccurrences {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeFoundation.Demand source) :
    List (GroundedRewriteOccurrence source) :=
  demand.typings.attach.map fun attached =>
    { typing := attached.1
      grounded := demand.grounded attached.1 attached.2 }

@[simp]
theorem groundedOccurrences_typings {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeFoundation.Demand source) :
    demand.groundedOccurrences.map GroundedRewriteOccurrence.typing =
      demand.typings := by
  unfold groundedOccurrences
  rw [List.map_map]
  change demand.typings.attach.map Subtype.val = demand.typings
  exact List.attach_map_subtype_val demand.typings

@[simp]
theorem demandOfList_groundedOccurrences {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeFoundation.Demand source) :
    GroundedRewriteOccurrence.demandOfList demand.groundedOccurrences = demand := by
  apply SelectedNativeTypeFoundation.Demand.ext
  exact groundedOccurrences_typings demand

@[simp]
theorem groundedOccurrences_demandOfList {source : ValidatedLanguageDef}
    (occurrences : List (GroundedRewriteOccurrence source)) :
    (GroundedRewriteOccurrence.demandOfList occurrences).groundedOccurrences =
      occurrences := by
  apply GroundedRewriteOccurrence.list_ext
  simp

@[simp]
theorem groundedOccurrences_singletonDemand {source : ValidatedLanguageDef}
    (occurrence : GroundedRewriteOccurrence source) :
    occurrence.singletonDemand.groundedOccurrences = [occurrence] := by
  apply GroundedRewriteOccurrence.list_ext
  simp [GroundedRewriteOccurrence.singletonDemand]

@[simp]
theorem groundedOccurrences_empty (source : ValidatedLanguageDef) :
    (SelectedNativeTypeFoundation.Demand.empty source).groundedOccurrences = [] := by
  apply GroundedRewriteOccurrence.list_ext
  simp

@[simp]
theorem groundedOccurrences_append {source : ValidatedLanguageDef}
    (first second : SelectedNativeTypeFoundation.Demand source) :
    (first.append second).groundedOccurrences =
      first.groundedOccurrences ++ second.groundedOccurrences := by
  apply GroundedRewriteOccurrence.list_ext
  simp [List.map_append]

end SelectedNativeTypeFoundation.Demand

/-! ## Positive and negative controls -/

namespace GroundedRewriteOccurrence

namespace Canary

/-- Positive: atomization followed by batching recovers the exact foundation
demand. -/
theorem roundTrip {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeFoundation.Demand source) :
    demandOfList demand.groundedOccurrences = demand :=
  SelectedNativeTypeFoundation.Demand.demandOfList_groundedOccurrences demand

/-- Negative: an empty atom stream cannot represent a nonempty demand. -/
theorem empty_ne_singleton {source : ValidatedLanguageDef}
    (occurrence : GroundedRewriteOccurrence source) :
    demandOfList ([] : List (GroundedRewriteOccurrence source)) ≠
      singletonDemand occurrence := by
  intro equality
  have typings := congrArg SelectedNativeTypeFoundation.Demand.typings equality
  simp [singletonDemand] at typings

#print axioms ext
#print axioms map_id
#print axioms map_comp
#print axioms demandOfList_append
#print axioms list_ext
#print axioms SelectedNativeTypeFoundation.Demand.groundedOccurrences_append
#print axioms SelectedNativeTypeFoundation.Demand.groundedOccurrences_demandOfList
#print axioms SelectedNativeTypeFoundation.Demand.groundedOccurrences_singletonDemand
#print axioms Canary.roundTrip
#print axioms Canary.empty_ne_singleton

end Canary

end GroundedRewriteOccurrence

end Mettapedia.OSLF.Framework
