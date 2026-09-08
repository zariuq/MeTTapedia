import Mettapedia.GSLT.Core.ProofRelevantGSLT

/-!
# The category of proof-relevant GSLTs

A proof-relevant translation retains three pieces of executable structure:
the term map, the forward evidence map, and the local lifting algorithm.  This
module proves that the existing identity and composition operations satisfy
the category laws without quotienting any of those algorithms.

The equality of translations is therefore intentionally stronger than
equality of their proposition-valued operational shadows.  The functor
`forgetEvidence` performs that explicit erasure only after the category has
been constructed.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ProofRelevant

open CategoryTheory
open Mettapedia.GSLT.IndexedOperational

universe u

/-- Extensionality for proof-relevant translations includes both executable
evidence maps.  The equation-respect field is proof-irrelevant. -/
theorem Translation.ext_data
    {source target : ProofRelevantGSLT.{u}}
    {left right : Translation source target}
    (mapTerm : left.mapTerm = right.mapTerm)
    (mapEvidence : HEq (@Translation.mapEvidence _ _ left)
      (@Translation.mapEvidence _ _ right))
    (liftEvidence : HEq (@Translation.liftEvidence _ _ left)
      (@Translation.liftEvidence _ _ right)) :
    left = right := by
  cases left
  cases right
  cases mapTerm
  cases mapEvidence
  cases liftEvidence
  rfl

/-- Composing identity before a proof-relevant translation retains its chosen
lifting algorithm exactly. -/
theorem Translation.identity_comp
    {source target : ProofRelevantGSLT.{u}}
    (route : Translation source target) :
    Translation.comp (Translation.id source) route = route := by
  cases route with
  | mk mapTerm mapEquiv mapEvidence liftEvidence =>
    apply Translation.ext_data
    · rfl
    · rfl
    · apply heq_of_eq
      funext sourceTerm targetTerm targetEvidence
      obtain ⟨sourceTarget, sourceEvidence, endpoint⟩ :=
        liftEvidence targetEvidence
      rcases endpoint with ⟨⟨endpoint⟩⟩
      subst targetTerm
      simp [Translation.comp, Translation.id]

/-- Composing identity after a proof-relevant translation retains its chosen
lifting algorithm exactly. -/
theorem Translation.comp_identity
    {source target : ProofRelevantGSLT.{u}}
    (route : Translation source target) :
    Translation.comp route (Translation.id target) = route := by
  apply Translation.ext_data <;> rfl

/-- Proof-relevant translation composition is associative, including the
selected evidence returned by the three local lifting algorithms. -/
theorem Translation.comp_assoc
    {first second third fourth : ProofRelevantGSLT.{u}}
    (one : Translation first second)
    (two : Translation second third)
    (three : Translation third fourth) :
    Translation.comp (Translation.comp one two) three =
      Translation.comp one (Translation.comp two three) := by
  apply Translation.ext_data
  · rfl
  · rfl
  · apply heq_of_eq
    funext sourceTerm targetTerm targetEvidence
    obtain ⟨laterTarget, laterEvidence, laterEndpoint⟩ :=
      three.liftEvidence targetEvidence
    obtain ⟨middleTarget, middleEvidence, middleEndpoint⟩ :=
      two.liftEvidence laterEvidence
    obtain ⟨sourceTarget, sourceEvidence, sourceEndpoint⟩ :=
      one.liftEvidence middleEvidence
    rcases laterEndpoint with ⟨⟨laterEndpoint⟩⟩
    subst targetTerm
    rcases middleEndpoint with ⟨⟨middleEndpoint⟩⟩
    subst laterTarget
    rcases sourceEndpoint with ⟨⟨sourceEndpoint⟩⟩
    subst middleTarget
    simp [Translation.comp]

/-- Proof-relevant GSLTs and their two-sided evidence translations form a
category before any occurrence evidence is erased. -/
instance proofRelevantGSLTCategory :
    CategoryTheory.Category (ProofRelevantGSLT.{u}) where
  Hom := Translation
  id := Translation.id
  comp earlier later := Translation.comp earlier later
  id_comp := Translation.identity_comp
  comp_id := Translation.comp_identity
  assoc := Translation.comp_assoc

/-- Retained primitive events form a covariant functor out of the category of
proof-relevant GSLTs.  This is the categorical action shared by occurrence
indices, observation disciplines, biform meanings, and accounting ledgers. -/
def eventFunctor : ProofRelevantGSLT.{u} ⥤ Type u where
  obj system := system.Event
  map translation := TypeCat.ofHom translation.mapEvent
  map_id system := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext event
    exact Translation.mapEvent_id event
  map_comp earlier later := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext event
    exact Translation.mapEvent_comp earlier later event

/-- Erasing occurrence evidence is a functor to the existing category of
locally covered proposition-valued GSLTs. -/
def forgetEvidence : ProofRelevantGSLT.{u} ⥤ CoveredTheory.{u} where
  obj system := ⟨system.theory⟩
  map translation := translation.toCovered
  map_id _ := by
    apply CoveredTranslation.ext
    rfl
  map_comp _ _ := by
    apply CoveredTranslation.ext
    rfl

#print axioms Translation.ext_data
#print axioms Translation.identity_comp
#print axioms Translation.comp_identity
#print axioms Translation.comp_assoc
#print axioms eventFunctor
#print axioms forgetEvidence

end Mettapedia.GSLT.ProofRelevant
