import Mettapedia.GSLT.LanguageDef.CompletenessSpectrum
import Mettapedia.GSLT.LanguageDef.ProofGSLTInterpretation
import Mettapedia.GSLT.LanguageDef.SemanticProofGSLTCategory
import Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelKripkeNeighborhoodCanonical

/-!
# Neighborhood semantics as a ProofGSLT authority

Neighborhood semantics is strictly broader than relational Kripke semantics:
a world may select an arbitrary family of supported propositions rather than
the supersets of one successor set.  This module connects that semantic breadth
to proof-carrying GSLT presentations.

An exact ProofGSLT presentation of a sound-and-complete neighborhood calculus
is promoted to exact authority for neighborhood WM consequence.  Consequently
existence of an accepted wire article is equivalent to the independently
defined neighborhood meaning.  Derivation-valued ProofGSLT interpretations
then transport source proofs into any target presentation that is sound for
the same meaning.

The final section gives both sides of the Kripke boundary.  Canonical Kripke
points are neighborhood-representable, while a one-world neighborhood model
with no supported sets refutes `box top`; no Kripke point can agree with it on
all modal formulas.
-/

namespace Mettapedia.PLN.Bridges.GSLT.NeighborhoodProofAuthority

open LO
open LO.Modal
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.ProofGSLT
open Mettapedia.GSLT.LanguageDef.CompletenessSpectrum
open Mettapedia.PLN.WorldModel.PLNWorldModel
open Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelNeighborhood

namespace NeighborhoodCompleteness

open Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelNeighborhoodCompleteness

abbrev ModalQuery :=
  Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelNeighborhood.ModalQuery

/-- The implication judgment used at the proof/semantics boundary. -/
structure ImplicationClaim where
  antecedent : ModalQuery
  consequent : ModalQuery

/-- Syntactic derivability of an implication in a chosen neighborhood
calculus. -/
def Provable {System : Type*} [Entailment System ModalQuery]
    (system : System) (claim : ImplicationClaim) : Prop :=
  system ⊢ (claim.antecedent ➝ claim.consequent)

/-- Independently defined neighborhood-WM meaning of an implication claim. -/
def Meaning (frameClass : Neighborhood.FrameClass)
    (claim : ImplicationClaim) : Prop :=
  singletonStrengthLEOn frameClass claim.antecedent claim.consequent

/-- Neighborhood consequence is contravariant in the class of models: a claim
valid on a larger class remains valid after restricting to a subclass.  This
is the semantic direction behind theorem-preserving translations between
neighborhood regimes; the converse is a separate reflection obligation. -/
theorem meaning_antitone
    {smaller larger : Neighborhood.FrameClass}
    (inclusion : smaller ⊆ larger) (claim : ImplicationClaim) :
    Meaning larger claim → Meaning smaller claim := by
  intro meaningful point pointInSmaller
  exact meaningful point (inclusion pointInSmaller)

/-- Restricting the model class gives a theorem-preserving semantic
translation.  It need not reflect meaning: a smaller model class can validate
strictly more claims. -/
def restrictFrameClass
    {smaller larger : Neighborhood.FrameClass}
    (inclusion : smaller ⊆ larger) :
    Mettapedia.GSLT.LanguageDef.ProofGSLT.Semantic.MeaningTranslation
      (Meaning larger) (Meaning smaller) where
  mapClaim := fun claim => claim
  preserves := meaning_antitone inclusion

/-- Soundness and completeness of the neighborhood calculus identify its
syntactic implication judgment with neighborhood-WM consequence. -/
theorem provable_iff_meaning
    {System : Type*} [Entailment System ModalQuery]
    (system : System) (frameClass : Neighborhood.FrameClass)
    [Sound system frameClass] [Complete system frameClass]
    (claim : ImplicationClaim) :
    Provable system claim ↔ Meaning frameClass claim := by
  exact provable_imp_iff_singletonStrengthLEOn
    (S := System) (𝓢 := system) (C := frameClass)

/-- Promote an exact presentation of syntactic neighborhood provability to an
exact presentation of the independently defined neighborhood-WM meaning. -/
def exactSemanticPresentation
    {System : Type*} [Entailment System ModalQuery]
    (system : System) (frameClass : Neighborhood.FrameClass)
    [Sound system frameClass] [Complete system frameClass]
    {presentation : ValidatedPresentation}
    (provability :
      ExactJudgmentPresentation ImplicationClaim (Provable system) presentation) :
    ExactJudgmentPresentation ImplicationClaim (Meaning frameClass) presentation where
  toJudgmentPresentationAdequacy :=
    { encode := provability.toJudgmentPresentationAdequacy.encode
      derivation_sound := fun claim derivation =>
        (provable_iff_meaning system frameClass claim).mp
          (provability.toJudgmentPresentationAdequacy.derivation_sound
            claim derivation) }
  derivation_complete := fun claim meaningful =>
    provability.derivation_complete claim
      ((provable_iff_meaning system frameClass claim).mpr meaningful)

/-- Package the promoted presentation as a semantically complete ProofGSLT. -/
def semanticProofGSLT
    {System : Type*} [Entailment System ModalQuery]
    (system : System) (frameClass : Neighborhood.FrameClass)
    [Sound system frameClass] [Complete system frameClass]
    {presentation : ValidatedPresentation}
    (provability :
      ExactJudgmentPresentation ImplicationClaim (Provable system) presentation) :
    SemanticallyCompleteProofGSLT ImplicationClaim (Meaning frameClass) where
  presentation := presentation
  adequacy := exactSemanticPresentation system frameClass provability

/-- The same authority as an object of the fixed-meaning semantic ProofGSLT
category.  This is the appropriate stage object for later filtered growth; no
colimit existence or preservation theorem is asserted here. -/
def exactSemanticObject
    {System : Type*} [Entailment System ModalQuery]
    (system : System) (frameClass : Neighborhood.FrameClass)
    [Sound system frameClass] [Complete system frameClass]
    {presentation : ValidatedPresentation}
    (provability :
      ExactJudgmentPresentation ImplicationClaim (Provable system) presentation) :
    Mettapedia.GSLT.LanguageDef.ProofGSLT.Semantic.ExactObject
      ImplicationClaim (Meaning frameClass) where
  toProofGSLT := ⟨presentation⟩
  adequacy := exactSemanticPresentation system frameClass provability

/-- Accepted ProofGSLT articles are neither merely sound certificates nor a
restatement of derivability: their existence is exactly neighborhood-WM
consequence for the declared frame class. -/
theorem exists_accepted_article_iff_meaning
    {AuthorityId : Type*} (authorityId : AuthorityId)
    {System : Type*} [Entailment System ModalQuery]
    (system : System) (frameClass : Neighborhood.FrameClass)
    [Sound system frameClass] [Complete system frameClass]
    {presentation : ValidatedPresentation}
    (provability :
      ExactJudgmentPresentation ImplicationClaim (Provable system) presentation)
    (claim : ImplicationClaim) :
    (∃ article,
        ((semanticProofGSLT system frameClass provability).checker authorityId).check
          claim article = true) ↔
      Meaning frameClass claim := by
  constructor
  · rintro ⟨article, accepted⟩
    exact ((semanticProofGSLT system frameClass provability).checker_authority
      authorityId).sound claim article accepted
  · intro meaningful
    exact ((semanticProofGSLT system frameClass provability).checker_authority
      authorityId).complete claim meaningful

/-- A derivation-valued ProofGSLT interpretation transports a source proof
into a target presentation.  If the target presentation is sound for
neighborhood meaning, the transported source proof therefore has that meaning.
This is the theorem-preserving direction; reflection requires separate data. -/
theorem meaning_of_interpreted_derivation
    {source target : Object}
    (interpretation : Interpretation source target)
    {frameClass : Neighborhood.FrameClass}
    (targetSound :
      JudgmentPresentationAdequacy ImplicationClaim (Meaning frameClass)
        target.presentation)
    (claim : ImplicationClaim)
    (sourceDerivation : Nonempty
      (Derivation source.presentation (targetSound.encode claim))) :
    Meaning frameClass claim := by
  obtain ⟨derivation⟩ := sourceDerivation
  exact targetSound.derivation_sound claim
    ⟨interpretation.mapDerivation derivation⟩

end NeighborhoodCompleteness

/-! ## The strict Kripke boundary -/

namespace KripkeBoundary

open Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelKripke
open Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelKripkeNeighborhoodCanonical

abbrev ModalQuery :=
  Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelNeighborhood.ModalQuery
abbrev PointedKripke :=
  Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelKripke.PointedKripke
abbrev PointedNeighborhood :=
  Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelNeighborhood.PointedNeighborhood

/-- A pointed neighborhood model is Kripke-representable when it agrees on all
modal formulas with some pointed Kripke model. -/
def KripkeRepresentable (point : PointedNeighborhood) : Prop :=
  ∃ kripkePoint : PointedKripke, ∀ formula : ModalQuery,
    point.satisfies formula ↔ kripkePoint.satisfies formula

/-- Every canonically translated Kripke point is represented by its source
Kripke point. -/
theorem canonical_point_representable (point : PointedKripke) :
    KripkeRepresentable (pointedKripkeToNeighborhood point) := by
  exact ⟨point, pointed_satisfies_iff point⟩

/-- A one-world neighborhood frame that supports no proposition sets. -/
def unsupportedFrame : Neighborhood.Frame where
  World := Unit
  world_nonempty := inferInstance
  𝒩 _ := ∅

/-- The valuation is irrelevant to the separating formula `box top`. -/
def unsupportedModel : Neighborhood.Model where
  toFrame := unsupportedFrame
  Val _ := ∅

/-- The unique point of `unsupportedModel`. -/
def unsupportedPoint : PointedNeighborhood where
  model := unsupportedModel
  world := ()

/-- The unsupported neighborhood point refutes `box top`. -/
theorem unsupportedPoint_not_box_top :
    ¬ unsupportedPoint.satisfies (□(⊤ : ModalQuery)) := by
  change () ∉ (∅ : Set Unit)
  exact fun member => (Set.mem_empty_iff_false ()).mp member

/-- Every Kripke point satisfies `box top`, independently of its accessibility
relation. -/
theorem kripkePoint_box_top (point : PointedKripke) :
    point.satisfies (□(⊤ : ModalQuery)) := by
  apply Formula.Kripke.Satisfies.box_def.mpr
  intro world _
  exact Formula.Kripke.Satisfies.top_def

/-- Neighborhood semantics is strictly more expressive than Kripke semantics:
the unsupported point has no modally equivalent Kripke point. -/
theorem unsupportedPoint_not_kripkeRepresentable :
    ¬ KripkeRepresentable unsupportedPoint := by
  rintro ⟨point, agrees⟩
  exact unsupportedPoint_not_box_top
    ((agrees (□(⊤ : ModalQuery))).mpr (kripkePoint_box_top point))

/-- The strict semantic boundary is visible directly in PLN evidence: the
unsupported singleton assigns zero strength to `box top`. -/
theorem unsupportedPoint_box_top_strength_zero :
    BinaryWorldModel.queryStrength
      (State := Multiset PointedNeighborhood) (Query := ModalQuery)
      ({unsupportedPoint} : Multiset PointedNeighborhood) (□(⊤ : ModalQuery)) = 0 :=
  queryStrength_singleton_of_not_satisfies unsupportedPoint
    (□(⊤ : ModalQuery)) unsupportedPoint_not_box_top

/-- Every Kripke singleton assigns unit strength to `box top`. -/
theorem kripkePoint_box_top_strength_one (point : PointedKripke) :
    BinaryWorldModel.queryStrength
      (State := Multiset PointedKripke) (Query := ModalQuery)
      ({point} : Multiset PointedKripke) (□(⊤ : ModalQuery)) = 1 :=
  Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelKripke.queryStrength_singleton_of_satisfies
    point (□(⊤ : ModalQuery)) (kripkePoint_box_top point)

/-! ## Strict semantic variance between frame classes -/

open NeighborhoodCompleteness
open Mettapedia.PLN.Bridges.Logic.WorldModel.PLNWorldModelNeighborhoodCompleteness
open LO.Entailment
open LO.Modal.Entailment

/-- The implication from truth to necessarily true separates arbitrary
neighborhood frames from frames containing the unit neighborhood. -/
def boxTopClaim : ImplicationClaim where
  antecedent := ⊤
  consequent := □⊤

/-- The claim holds on `EMN` frames because axiom N is available. -/
theorem boxTopClaim_meaning_EMN :
    Meaning Neighborhood.FrameClass.EMN boxTopClaim := by
  apply (provable_iff_meaning Modal.EMN Neighborhood.FrameClass.EMN boxTopClaim).mp
  exact C!_of_conseq! (d := axiomN!)

/-- The unsupported one-world frame refutes the same claim over the class of
all neighborhood frames. -/
theorem boxTopClaim_not_meaning_E :
    ¬ Meaning Neighborhood.FrameClass.E boxTopClaim := by
  intro meaningful
  have pointwise :
      pointwiseImpliesOn Neighborhood.FrameClass.E
        (⊤ : ModalQuery) (□(⊤ : ModalQuery)) :=
    (pointwiseImpliesOn_iff_singletonStrengthLEOn
      Neighborhood.FrameClass.E (⊤ : ModalQuery) (□(⊤ : ModalQuery))).mpr meaningful
  exact unsupportedPoint_not_box_top
    (pointwise unsupportedPoint (by simp) Formula.Neighborhood.Satisfies.def_top)

/-- Restriction from all neighborhood frames to `EMN` frames is
theorem-preserving. -/
def restrictEToEMN :=
  restrictFrameClass
    (smaller := Neighborhood.FrameClass.EMN)
    (larger := Neighborhood.FrameClass.E)
    (by intro frame _; simp)

/-- The frame-class restriction is not reflecting: `EMN` validates a claim
that fails over all neighborhood frames. -/
theorem restrictEToEMN_not_reflects :
    ¬ Mettapedia.GSLT.LanguageDef.ProofGSLT.Semantic.MeaningTranslation.Reflects
      restrictEToEMN := by
  intro reflects
  exact boxTopClaim_not_meaning_E
    (reflects boxTopClaim boxTopClaim_meaning_EMN)

end KripkeBoundary

end Mettapedia.PLN.Bridges.GSLT.NeighborhoodProofAuthority
