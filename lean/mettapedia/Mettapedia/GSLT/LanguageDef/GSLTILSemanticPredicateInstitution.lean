import Mettapedia.GSLT.LanguageDef.GSLTILModalDoctrineAttachment
import Mettapedia.GSLT.LanguageDef.NIKMetalogic

/-!
# Semantic predicate institution for the OSLF modal base

The full predicate-valued OSLF semantics has a genuine institution-like
home.  Signatures are bounded operational GSLTs with variance reversed,
sentences are predicates on their states, and sentence translation is inverse
image along the bounded operational map.  Consequence is ordinary semantic
entailment: every state satisfying all premises satisfies the conclusion.

This construction deliberately uses all semantic predicates.  It is an
independent authority for a future generated native syntax, not that syntax
itself.  A generated typed GSLT still requires its own formula grammar,
proof-relevant derivations, reification, and adequacy theorem.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.GSLTIL.SemanticPredicateInstitution

open CategoryTheory
open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.GSLTIL.ModalDoctrineAttachment
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor

universe uState uTerm

/-! ## Semantic consequence in one state space -/

/-- Every state satisfying every premise also satisfies the conclusion. -/
def Entails {State : Type uState}
    (premises : Set (Set State)) (conclusion : Set State) : Prop :=
  ∀ state, (∀ predicate, predicate ∈ premises → state ∈ predicate) →
    state ∈ conclusion

/-- Semantic entailment is a Tarski closure operator on predicate sets. -/
def semanticConsequence (State : Type uState) :
    ClosureOperator (Set (Set State)) where
  toFun premises := { conclusion | Entails premises conclusion }
  monotone' := by
    intro source target subset conclusion entailsTarget state satisfiesTarget
    exact entailsTarget state fun predicate member =>
      satisfiesTarget predicate (subset member)
  le_closure' := by
    intro premises conclusion member state satisfies
    exact satisfies conclusion member
  idempotent' := by
    intro premises
    ext conclusion
    constructor
    · intro entailsConsequences state satisfiesPremises
      apply entailsConsequences state
      intro consequence consequenceMember
      exact consequenceMember state satisfiesPremises
    · intro entailsPremises state satisfiesConsequences
      exact satisfiesConsequences conclusion entailsPremises

@[simp] theorem mem_semanticConsequence_iff
    {State : Type uState} (premises : Set (Set State))
    (conclusion : Set State) :
    conclusion ∈ semanticConsequence State premises ↔
      Entails premises conclusion :=
  Iff.rfl

/-- With no premises, semantic consequences are exactly the universally true
predicates. -/
theorem mem_semanticConsequence_empty_iff
    {State : Type uState} (conclusion : Set State) :
    conclusion ∈ semanticConsequence State ∅ ↔
      ∀ state, state ∈ conclusion := by
  constructor
  · intro entails state
    exact entails state fun predicate impossible => False.elim impossible
  · intro universal state _
    exact universal state

/-! ## The indexed sentence family -/

/-- Predicates form a covariant sentence family on the opposite of the modal
base, because bounded operational maps act by inverse image. -/
def predicateSentence :
    CategoryTheory.Functor (ModallyCoveredTheory.{uTerm})ᵒᵖ
      (Type uTerm) where
  obj signature := Set signature.unop.theory.Term
  map translation := TypeCat.ofHom fun predicate =>
    Set.preimage translation.unop.mapTerm predicate
  map_id signature := by
    apply CategoryTheory.ConcreteCategory.hom_ext
    intro predicate
    ext state
    rfl
  map_comp earlier later := by
    apply CategoryTheory.ConcreteCategory.hom_ext
    intro predicate
    ext state
    rfl

@[simp] theorem predicateSentence_map
    {source target : (ModallyCoveredTheory.{uTerm})ᵒᵖ}
    (translation : source ⟶ target)
    (predicate : Set source.unop.theory.Term) :
    predicateSentence.map translation predicate =
      Set.preimage translation.unop.mapTerm predicate :=
  rfl

/-! ## Pi-institution structure -/

/-- The full semantic predicate authority as a Pi-institution. -/
def institution :
    PiInstitution (ModallyCoveredTheory.{uTerm})ᵒᵖ where
  sentence := predicateSentence
  consequence := fun signature =>
    semanticConsequence signature.unop.theory.Term
  translation := by
    intro source target translation premises mappedConclusion member
    rcases member with ⟨conclusion, conclusionMember, rfl⟩
    intro targetState satisfiesMappedPremises
    apply conclusionMember (translation.unop.mapTerm targetState)
    intro premise premiseMember
    have mappedMember :
        Set.preimage translation.unop.mapTerm premise ∈
          Set.image (predicateSentence.map translation) premises := by
      exact ⟨premise, premiseMember, rfl⟩
    exact satisfiesMappedPremises _ mappedMember

/-- Its consequence judgment is exactly semantic entailment. -/
theorem derives_iff_entails
    (signature : (ModallyCoveredTheory.{uTerm})ᵒᵖ)
    (premises : Set (Set signature.unop.theory.Term))
    (conclusion : Set signature.unop.theory.Term) :
    institution.Derives signature premises conclusion ↔
      Entails premises conclusion :=
  Iff.rfl

/-- The institution sentence action and the established OSLF modal functor
use exactly the same inverse-image map. -/
theorem sentence_transport_eq_oslf_pullback
    {source target : (ModallyCoveredTheory.{uTerm})ᵒᵖ}
    (translation : source ⟶ target)
    (predicate : Set source.unop.theory.Term) :
    predicateSentence.map translation predicate =
      (oslfModalFunctor.map translation).mapPred predicate :=
  rfl

/-! ## Positive and negative controls -/

/-- A premise is semantically derivable from itself. -/
theorem premise_derives_itself
    (signature : (ModallyCoveredTheory.{uTerm})ᵒᵖ)
    (predicate : Set signature.unop.theory.Term) :
    institution.Derives signature {predicate} predicate :=
  institution.derives_of_mem signature (Set.mem_singleton predicate)

/-- The empty predicate is not derivable from the empty context on an
inhabited state space. -/
theorem empty_not_derivable_without_premises
    (signature : (ModallyCoveredTheory.{uTerm})ᵒᵖ)
    (state : signature.unop.theory.Term) :
    ¬ institution.Derives signature ∅ (∅ : Set signature.unop.theory.Term) := by
  intro derives
  have universal :=
    (mem_semanticConsequence_empty_iff
      (∅ : Set signature.unop.theory.Term)).mp derives
  exact universal state

#print axioms semanticConsequence
#print axioms mem_semanticConsequence_empty_iff
#print axioms institution
#print axioms derives_iff_entails
#print axioms sentence_transport_eq_oslf_pullback
#print axioms premise_derives_itself
#print axioms empty_not_derivable_without_premises

end Mettapedia.GSLT.LanguageDef.GSLTIL.SemanticPredicateInstitution
