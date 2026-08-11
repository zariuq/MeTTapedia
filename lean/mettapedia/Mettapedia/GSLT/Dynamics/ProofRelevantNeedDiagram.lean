import Mettapedia.GSLT.Dynamics.ProofRelevantNeedProfile

/-!
# Open diagrams of proof-relevant need fragments

The maximal proof-relevant cell protocol is not a distinguished language
profile.  Its finite operator sets form a poset, and inclusion induces a
diagram of operational GSLTs.  A concrete language chooses an object of that
diagram, or moves forward along an inclusion when it admits more operators.

Demand rights form a second, independent diagram.  At each rights object the
visible operators are obtained by applying a chosen demand boundary to a
chosen vocabulary.  Rights inclusion induces the corresponding operational
translation.  Thus operator growth and demand attenuation remain separate
axes even though both can be executed through the same indexed GSLT waist.
-/

namespace Mettapedia.GSLT.Dynamics.ProofRelevantNeed

open CategoryTheory
open Mettapedia.GSLT.IndexedOperational

universe uCell uOrigin uValue uStableFault uRetryableFault uRight

/-! ## The open operator-fragment diagram -/

/-- Every finite operator vocabulary is an object; subset inclusion is its
unique forward route.  No particular chain of profiles is privileged. -/
def operatorDiagram
    {Cell : Type uCell} {Origin : Type uOrigin} {Value : Type uValue}
    {StableFault : Type uStableFault}
    (RetryableFault : Type uRetryableFault) (cell : Cell) :
    Diagram OperatorSet where
  obj operators :=
    ⟨fragmentTheory (Origin := Origin) (Value := Value)
      (StableFault := StableFault) operators RetryableFault cell⟩
  map {smaller larger} inclusion :=
    fragmentInclusion (Origin := Origin) (Value := Value)
      (StableFault := StableFault) (CategoryTheory.leOfHom inclusion)
      RetryableFault cell
  map_id operators := by
    apply OperationalTranslation.ext
    rfl
  map_comp earlier later := by
    apply OperationalTranslation.ext
    rfl

/-- Transport in the operator diagram is definitionally identity on cell
states: admitting new operators preserves old states while adding possible
event sites. -/
@[simp]
theorem operatorDiagram_mapTerm
    {Cell : Type uCell} {Origin : Type uOrigin} {Value : Type uValue}
    {StableFault : Type uStableFault}
    (RetryableFault : Type uRetryableFault) (cell : Cell)
    {smaller larger : OperatorSet} (inclusion : smaller ⟶ larger)
    (state : CellState Origin Value StableFault) :
    ((operatorDiagram (Origin := Origin) (Value := Value)
      (StableFault := StableFault) RetryableFault cell).map inclusion).mapTerm
        state = state :=
  rfl

/-! ## Demand is an independent indexed axis -/

/-- Fixing a demand boundary and an available vocabulary yields a diagram
indexed by held rights.  Adding rights may expose more of the vocabulary; it
cannot remove an already permitted event site. -/
def demandDiagram
    {Cell : Type uCell} {Origin : Type uOrigin} {Value : Type uValue}
    {StableFault : Type uStableFault}
    (boundary : DemandBoundary.{uRight}) (available : OperatorSet)
    (RetryableFault : Type uRetryableFault) (cell : Cell) :
    Diagram (Finset boundary.Right) where
  obj held :=
    ⟨fragmentTheory (Origin := Origin) (Value := Value)
      (StableFault := StableFault)
      (boundary.publicOperators available held) RetryableFault cell⟩
  map {smaller larger} inclusion :=
    fragmentInclusion (Origin := Origin) (Value := Value)
      (StableFault := StableFault)
      (boundary.publicOperators_mono_rights available
        (CategoryTheory.leOfHom inclusion)) RetryableFault cell
  map_id held := by
    apply OperationalTranslation.ext
    rfl
  map_comp earlier later := by
    apply OperationalTranslation.ext
    rfl

/-- The demand diagram is also identity-on-state along every rights route. -/
@[simp]
theorem demandDiagram_mapTerm
    {Cell : Type uCell} {Origin : Type uOrigin} {Value : Type uValue}
    {StableFault : Type uStableFault}
    (boundary : DemandBoundary.{uRight}) (available : OperatorSet)
    (RetryableFault : Type uRetryableFault) (cell : Cell)
    {smaller larger : Finset boundary.Right} (inclusion : smaller ⟶ larger)
    (state : CellState Origin Value StableFault) :
    ((demandDiagram (Origin := Origin) (Value := Value)
      (StableFault := StableFault) boundary available RetryableFault cell).map
        inclusion).mapTerm state = state :=
  rfl

/-! ## The two axes commute -/

/-- Enlarging the available vocabulary and then filtering by fixed rights
contains the result of filtering the smaller vocabulary. -/
def vocabularyRouteAtRights
    {Cell : Type uCell} {Origin : Type uOrigin} {Value : Type uValue}
    {StableFault : Type uStableFault}
    (boundary : DemandBoundary.{uRight})
    {smaller larger : OperatorSet} (included : smaller ⊆ larger)
    (held : Finset boundary.Right)
    (RetryableFault : Type uRetryableFault) (cell : Cell) :
    OperationalTranslation
      (fragmentTheory (Origin := Origin) (Value := Value)
        (StableFault := StableFault)
        (boundary.publicOperators smaller held) RetryableFault cell)
      (fragmentTheory (Origin := Origin) (Value := Value)
        (StableFault := StableFault)
        (boundary.publicOperators larger held) RetryableFault cell) :=
  fragmentInclusion (Origin := Origin) (Value := Value)
    (StableFault := StableFault)
    (boundary.publicOperators_mono_vocabulary held included)
    RetryableFault cell

/-- Vocabulary growth and rights growth form a commuting square of forward
operational translations.  Both paths retain the same cell state and the same
old event evidence. -/
theorem vocabulary_rights_square
    {Cell : Type uCell} {Origin : Type uOrigin} {Value : Type uValue}
    {StableFault : Type uStableFault}
    (boundary : DemandBoundary.{uRight})
    {smallerVocabulary largerVocabulary : OperatorSet}
    (vocabularyIncluded : smallerVocabulary ⊆ largerVocabulary)
    {smallerRights largerRights : Finset boundary.Right}
    (rightsIncluded : smallerRights ⊆ largerRights)
    (RetryableFault : Type uRetryableFault) (cell : Cell) :
    OperationalTranslation.comp
      (vocabularyRouteAtRights (Origin := Origin) (Value := Value)
        (StableFault := StableFault) boundary vocabularyIncluded smallerRights
        RetryableFault cell)
      (fragmentInclusion (Origin := Origin) (Value := Value)
        (StableFault := StableFault)
        (boundary.publicOperators_mono_rights largerVocabulary rightsIncluded)
        RetryableFault cell) =
    OperationalTranslation.comp
      (fragmentInclusion (Origin := Origin) (Value := Value)
        (StableFault := StableFault)
        (boundary.publicOperators_mono_rights smallerVocabulary rightsIncluded)
        RetryableFault cell)
      (vocabularyRouteAtRights (Origin := Origin) (Value := Value)
        (StableFault := StableFault) boundary vocabularyIncluded largerRights
        RetryableFault cell) := by
  apply OperationalTranslation.ext
  rfl

/-! ## Separating canaries -/

namespace DiagramCanary

def pureToStable : pureNeedOperators ⟶ stableFaultNeedOperators :=
  CategoryTheory.homOfLE pureNeedOperators_subset_stableFault

def stableToAll : stableFaultNeedOperators ⟶ allNeedOperators :=
  CategoryTheory.homOfLE stableFaultNeedOperators_subset_all

theorem pure_to_all_composes :
    (operatorDiagram (Origin := Nat) (Value := Nat)
      (StableFault := Nat) Nat 0).map
        (CategoryTheory.CategoryStruct.comp pureToStable stableToAll) =
      OperationalTranslation.comp
        ((operatorDiagram (Origin := Nat) (Value := Nat)
          (StableFault := Nat) Nat 0).map pureToStable)
        ((operatorDiagram (Origin := Nat) (Value := Nat)
          (StableFault := Nat) Nat 0).map stableToAll) := by
  apply OperationalTranslation.ext
  rfl

/-- Positive canary: adding the force right exposes evaluation through a
genuine route in the demand diagram. -/
def inspectToForceInspect :
    ProfileCanary.inspectRights ⟶ ProfileCanary.forceInspectRights := by
  apply CategoryTheory.homOfLE
  intro right member
  simp only [ProfileCanary.inspectRights, ProfileCanary.forceInspectRights,
    Finset.mem_singleton] at member ⊢
  subst right
  simp

theorem beginEvaluation_after_rights_growth :
    Operation.beginEvaluation ∈
      standardDemandBoundary.publicOperators allNeedOperators
        ProfileCanary.forceInspectRights :=
  ProfileCanary.adding_force_exposes_evaluation

/-- Negative canary: rights growth is not reflection.  Evaluation is absent
at the smaller stage even though it exists at the larger one. -/
theorem beginEvaluation_absent_before_rights_growth :
    Operation.beginEvaluation ∉
      standardDemandBoundary.publicOperators allNeedOperators
        ProfileCanary.inspectRights :=
  ProfileCanary.inspect_only_exposes_inspection.2

/-! ### GSLT-IL naturality canary -/

abbrev DemoOperatorDiagram :=
  operatorDiagram (Origin := Nat) (Value := Nat) (StableFault := Nat) Nat 0

def pureBeginEvent :
    AdmittedEvent pureNeedOperators Nat Nat Nat Nat Nat :=
  ⟨.beginEvaluation 0 7, by simp [pureNeedOperators, Event.operation]⟩

def pureBeginStep :
    (fragmentTheory (Origin := Nat) (Value := Nat) (StableFault := Nat)
      pureNeedOperators Nat 0).Step (.suspended 7) (.evaluating 7) :=
  ⟨⟨pureBeginEvent, .beginEvaluation 7⟩⟩

def pureBeginSemanticStep :
    SemanticStep
      (DemoOperatorDiagram.obj pureNeedOperators).theory
      (Quotient.mk _ (.suspended 7)) (Quotient.mk _ (.evaluating 7)) :=
  semanticStep_mk pureBeginStep

/-- Computing in the pure fragment and then admitting stable-fault operators
forms the same carried naturality square as any GSLT-IL fibre/route pair. -/
def pureStableNaturalityDiamond :=
  Command.naturalityDiamond DemoOperatorDiagram pureToStable
    pureBeginSemanticStep

/-- Negative canary: the same diagram cannot provide a reverse identity-on-
state route, because retry behavior in the larger protocol is genuinely not
present in the pure fragment. -/
theorem no_all_to_pure_identity_route :
    ¬ ∃ translation : OperationalTranslation
      (DemoOperatorDiagram.obj allNeedOperators).theory
      (DemoOperatorDiagram.obj pureNeedOperators).theory,
      translation.mapTerm = id :=
  ProfileCanary.no_identity_translation_all_to_pure

end DiagramCanary

end Mettapedia.GSLT.Dynamics.ProofRelevantNeed
