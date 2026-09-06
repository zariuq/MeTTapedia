import Mettapedia.GSLT.Core.SemanticImplementation
import Mettapedia.GSLT.Core.Composition
import Mettapedia.GSLT.LanguageDef.GSLTILSemanticPredicateInstitution
import Mettapedia.GSLT.LanguageDef.NIKMetalogic
import Mettapedia.OSLF.Framework.GSLTTypeSynthesis
import Mettapedia.GSLT.LanguageDef.ClosedTheorySemanticTarget

/-!
# Operational models of closed theories

A GSLT is an operational semantic object, not a replacement for a logic and
its models, and a consequence-closed theory need not be equipped with
artificial dynamics.  An `OperationalModel` of a closed theory interprets the
native sentences as equation-invariant predicates on the states of a GSLT,
validates native consequence pointwise, and makes every selected theorem hold
at every state: the transition system is a model of the theory.  A
`ModelledTheory` is a closed theory with one such model, and a morphism of
modelled theories pairs a theory morphism with an equation-class semantic
cover and requires the two satisfaction readings to commute.

Neither half can impersonate the other.  A theory morphism does not mint an
operational refinement, and a step-preserving compiler does not by itself
preserve native mathematical meaning.  Modelled theories form a category with
separate forgetful functors to the closed theories and to the covered
operational theories, and a further functor to the semantic NIK objects,
which forgets the operational model.

This is the consequence-level layer.  Model-valued institutions, explicit
model reducts, and the full satisfaction condition live in
`InstitutionConsequence`; projecting that structure recovers the definitions
here.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef

open CategoryTheory
open scoped CategoryTheory
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

universe uSignature uHom uSentence uTerm

variable {Signature : Type uSignature}
  [CategoryTheory.Category.{uHom} Signature]

/-! ## Operational models -/

/-- An operational interpretation of one closed logical theory.  Native
sentences become predicates invariant under the GSLT equations.  Every native
consequence is valid pointwise, and every sentence selected by the closed
theory holds at every operational state. -/
structure OperationalModel
    (institution : PiInstitution.{uSignature, uHom, uSentence} Signature)
    (logical : PiInstitution.TheoryObject institution) where
  system : GSLT.{uTerm}
  interpret : institution.sentence.obj logical.signature →
    EquationPredicate system
  consequence_sound :
    ∀ (premises : Set (institution.sentence.obj logical.signature))
      (conclusion : institution.sentence.obj logical.signature),
      institution.Derives logical.signature premises conclusion →
        ∀ state, (∀ premise, premise ∈ premises → interpret premise state) →
          interpret conclusion state
  theory_sound : ∀ {formula}, formula ∈ logical.theory.1 →
    ∀ state, interpret formula state

/-- A closed theory together with one operational model. -/
structure ModelledTheory
    (institution : PiInstitution.{uSignature, uHom, uSentence} Signature) where
  logical : PiInstitution.TheoryObject institution
  operational : OperationalModel.{uSignature, uHom, uSentence, uTerm}
    institution logical

/-! ## Routes carrying both contracts -/

/-- A morphism of modelled theories carries independent logical and
operational maps, plus the commuting satisfaction law that relates them. -/
structure ModelledTheory.Hom
    {institution : PiInstitution.{uSignature, uHom, uSentence} Signature}
    (source target : ModelledTheory.{uSignature, uHom, uSentence, uTerm}
      institution) where
  logical : PiInstitution.TheoryHom source.logical target.logical
  operational : SemanticCoveredTranslation
    source.operational.system target.operational.system
  satisfaction_natural :
    ∀ (formula : institution.sentence.obj source.logical.signature)
      (state : source.operational.system.Term),
      source.operational.interpret formula state ↔
        target.operational.interpret
          (institution.sentence.map logical.mapSignature formula)
          (operational.mapTerm state)

namespace ModelledTheory.Hom

variable
  {institution : PiInstitution.{uSignature, uHom, uSentence} Signature}
  {first middle last : ModelledTheory.{uSignature, uHom, uSentence, uTerm}
    institution}

@[ext]
theorem ext {left right : ModelledTheory.Hom first middle}
    (logical : left.logical = right.logical)
    (operational : left.operational = right.operational) : left = right := by
  cases left
  cases right
  cases logical
  cases operational
  rfl

/-- Identity preserves both contracts and their common satisfaction reading. -/
def id (theory : ModelledTheory.{uSignature, uHom, uSentence, uTerm}
    institution) : ModelledTheory.Hom theory theory where
  logical := PiInstitution.TheoryHom.identity theory.logical
  operational := SemanticCoveredTranslation.id theory.operational.system
  satisfaction_natural := by
    intro formula state
    change theory.operational.interpret formula state ↔
      theory.operational.interpret
        (institution.sentence.map
          (CategoryTheory.CategoryStruct.id theory.logical.signature) formula)
        state
    rw [institution.sentence.map_id_apply]

/-- Commuting logical/operational routes compose in execution order. -/
def comp (earlier : ModelledTheory.Hom first middle)
    (later : ModelledTheory.Hom middle last) : ModelledTheory.Hom first last where
  logical := PiInstitution.TheoryHom.comp earlier.logical later.logical
  operational := SemanticCoveredTranslation.comp
    earlier.operational later.operational
  satisfaction_natural := by
    intro formula state
    have firstLaw := earlier.satisfaction_natural formula state
    have secondLaw := later.satisfaction_natural
      (institution.sentence.map earlier.logical.mapSignature formula)
      (earlier.operational.mapTerm state)
    change first.operational.interpret formula state ↔
      last.operational.interpret
        (institution.sentence.map
          (CategoryTheory.CategoryStruct.comp earlier.logical.mapSignature
            later.logical.mapSignature) formula)
        (later.operational.mapTerm (earlier.operational.mapTerm state))
    rw [institution.sentence.map_comp_apply]
    exact firstLaw.trans secondLaw

/-- Forgetting the operational contract retains the logical theory map. -/
def toLogical (route : ModelledTheory.Hom first middle) :
    PiInstitution.TheoryHom first.logical middle.logical :=
  route.logical

/-- Forgetting the logical contract retains the equation-class operational
cover, but not its mathematical meaning theorem. -/
def toOperational (route : ModelledTheory.Hom first middle) :
    SemanticCoveredTranslation first.operational.system middle.operational.system :=
  route.operational

end ModelledTheory.Hom

instance
    (institution : PiInstitution.{uSignature, uHom, uSentence} Signature) :
    CategoryTheory.Category
      (ModelledTheory.{uSignature, uHom, uSentence, uTerm} institution) where
  Hom := ModelledTheory.Hom
  id := ModelledTheory.Hom.id
  comp := ModelledTheory.Hom.comp
  id_comp route := by
    apply ModelledTheory.Hom.ext
    · apply PiInstitution.TheoryHom.ext
      exact CategoryTheory.Category.id_comp route.logical.mapSignature
    · apply SemanticCoveredTranslation.ext
      rfl
  comp_id route := by
    apply ModelledTheory.Hom.ext
    · apply PiInstitution.TheoryHom.ext
      exact CategoryTheory.Category.comp_id route.logical.mapSignature
    · apply SemanticCoveredTranslation.ext
      rfl
  assoc earlier later latest := by
    apply ModelledTheory.Hom.ext
    · apply PiInstitution.TheoryHom.ext
      exact CategoryTheory.Category.assoc earlier.logical.mapSignature
        later.logical.mapSignature latest.logical.mapSignature
    · apply SemanticCoveredTranslation.ext
      rfl

/-- The logical projection of the modelled atlas. -/
def logicalProjection
    (institution : PiInstitution.{uSignature, uHom, uSentence} Signature) :
    CategoryTheory.Functor
      (ModelledTheory.{uSignature, uHom, uSentence, uTerm} institution)
      (PiInstitution.TheoryObject institution) where
  obj theory := theory.logical
  map route := route.logical
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The operational projection of the same atlas. -/
def operationalProjection
    (institution : PiInstitution.{uSignature, uHom, uSentence} Signature) :
    CategoryTheory.Functor
      (ModelledTheory.{uSignature, uHom, uSentence, uTerm} institution)
      SemanticCoveredTheory.{uTerm} where
  obj theory := ⟨theory.operational.system⟩
  map route := route.operational
  map_id _ := rfl
  map_comp _ _ := rfl

/-! ## Generic boundaries -/

/-- A target step escaping an encoded source image prevents a commuting
morphism with that operational map, regardless of which logical morphism was
available. -/
theorem ModelledTheory.no_hom_of_operational_escape
    {institution : PiInstitution.{uSignature, uHom, uSentence} Signature}
    {source target : ModelledTheory.{uSignature, uHom, uSentence, uTerm}
      institution}
    (translation : OperationalTranslation source.operational.system
      target.operational.system)
    (escape : EquationClassEscapingStep source.operational.system
      target.operational.system translation.mapTerm) :
    ¬ ∃ route : ModelledTheory.Hom source target,
        route.operational.mapTerm = translation.mapTerm := by
  rintro ⟨route, mapTerm⟩
  exact escape.not_semanticCoveredTranslation ⟨route.operational, mapTerm⟩

/-! ## The semantic NIK reading of a modelled theory -/

namespace ModelledTheory

/-- Forget a modelled theory to its native closed theory and expose that
theory as one semantic NIK fibre.  The operational model is not recoverable
from this reading. -/
def semanticTargetFunctor
    (institution : PiInstitution.{uSignature, uHom, uSentence} Signature) :
    CategoryTheory.Functor
      (ModelledTheory.{uSignature, uHom, uSentence, uTerm} institution)
      CertifiedTheoryCategory.TheoryObject.{0, uSignature, uSentence} :=
  CategoryTheory.Functor.comp (logicalProjection institution)
    (ClosedTheorySemanticTarget.closedTheoryFunctor (institution := institution))

@[simp]
theorem semanticTargetFunctor_obj_family
    (institution : PiInstitution.{uSignature, uHom, uSentence} Signature)
    (theory : ModelledTheory.{uSignature, uHom, uSentence, uTerm} institution) :
    ((semanticTargetFunctor institution).obj theory).family =
      ClosedTheorySemanticTarget.theoryFamily theory.logical :=
  rfl

@[simp]
theorem semanticTargetFunctor_map
    (institution : PiInstitution.{uSignature, uHom, uSentence} Signature)
    {source target : ModelledTheory.{uSignature, uHom, uSentence, uTerm} institution}
    (route : source ⟶ target) :
    (semanticTargetFunctor institution).map route =
      ClosedTheorySemanticTarget.theoryTranslation route.logical :=
  rfl

end ModelledTheory

/-! ## The semantic predicate institution supplies a genuine model -/

namespace SemanticPredicateCanary

open Mettapedia.GSLT.LanguageDef.GSLTIL.SemanticPredicateInstitution
open Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor

/-- The closed theory of universally valid semantic predicates on a GSLT. -/
def logicalTheory (system : ModallyCoveredTheory.{uTerm}) :
    PiInstitution.TheoryObject institution :=
  PiInstitution.generatedTheory institution (Opposite.op system) ∅

/-- Semantic equation classes themselves form an operational model of the
universally valid predicate theory. -/
def operationalFace (system : ModallyCoveredTheory.{uTerm}) :
    OperationalModel institution (logicalTheory system) where
  system := semanticTheory system.theory
  interpret := fun predicate =>
    ⟨fun state => predicate state, by
      intro left right equal
      subst right
      exact Iff.rfl⟩
  consequence_sound := by
    intro premises conclusion derives state satisfies
    exact derives state fun predicate member => satisfies predicate member
  theory_sound := by
    intro formula member state
    exact (mem_semanticConsequence_empty_iff formula).mp member state

/-- Package the semantic predicate construction as an modelled theory-graph node. -/
def equipped (system : ModallyCoveredTheory.{uTerm}) :
    ModelledTheory institution :=
  ⟨logicalTheory system, operationalFace system⟩

/-- Positive control: every equipped predicate theory has the commuting
identity route. -/
def identityRoute (system : ModallyCoveredTheory.{uTerm}) :
    ModelledTheory.Hom (equipped system) (equipped system) :=
  ModelledTheory.Hom.id (equipped system)

/-! ### A nontrivial representation refinement

The target below retains a private Boolean component which the logical
sentences cannot observe.  This is a small but genuine commuting theory-graph route:
the operational carrier changes, while every source predicate continues to
read the visible component exactly. -/

/-- The visible Boolean operational system used by the source node. -/
def visibleSystem : ModallyCoveredTheory :=
  ⟨GSLT.discrete Bool⟩

/-- A target state carries the visible Boolean together with one private bit. -/
def hiddenBitTheory : GSLT :=
  GSLT.discrete (Bool × Bool)

/-- Inject a visible equation class while initializing the private bit. -/
def insertHiddenBit :
    SemanticTerm (GSLT.discrete Bool) → SemanticTerm hiddenBitTheory :=
  Quotient.map (fun visible => (visible, false)) fun _ _ equal =>
    congrArg (fun visible => (visible, false)) equal

/-- Forget the private bit while retaining the visible equation class. -/
def projectVisible :
    SemanticTerm hiddenBitTheory → SemanticTerm (GSLT.discrete Bool) :=
  Quotient.map Prod.fst fun _ _ equal => congrArg Prod.fst equal

@[simp]
theorem projectVisible_insertHiddenBit
    (state : SemanticTerm (GSLT.discrete Bool)) :
    projectVisible (insertHiddenBit state) = state := by
  induction state using Quotient.inductionOn with
  | _ representative => rfl

/-- The state injection is a semantic cover.  Both systems are discrete, so
the only content beyond equation preservation is the nontrivial carrier map. -/
def hiddenBitCover :
    SemanticCoveredTranslation
      (semanticTheory (GSLT.discrete Bool))
      (semanticTheory hiddenBitTheory) where
  mapTerm := insertHiddenBit
  mapEquiv := fun equal => congrArg insertHiddenBit equal
  mapStep := by
    intro source target step
    rcases step with ⟨redex, contractum, _, impossible, _⟩
    exact impossible.elim
  liftStep := by
    intro source target step
    rcases step with ⟨redex, contractum, _, impossible, _⟩
    exact impossible.elim

/-- The hidden-state implementation interprets every predicate through the
visible projection. -/
def hiddenBitOperationalFace :
    OperationalModel institution (logicalTheory visibleSystem) where
  system := semanticTheory hiddenBitTheory
  interpret := fun predicate =>
    ⟨fun state => predicate (projectVisible state), by
      intro left right equal
      subst right
      exact Iff.rfl⟩
  consequence_sound := by
    intro premises conclusion derives state satisfies
    exact derives (projectVisible state) fun predicate member =>
      satisfies predicate member
  theory_sound := by
    intro formula member state
    exact (mem_semanticConsequence_empty_iff formula).mp member
      (projectVisible state)

/-- The target node implements the same logical theory with extra private
operational state. -/
def hiddenBitModelled : ModelledTheory institution :=
  ⟨logicalTheory visibleSystem, hiddenBitOperationalFace⟩

/-- Positive control: a nonidentity state representation can commute with the
native logical reading. -/
def hiddenBitRoute : ModelledTheory.Hom (equipped visibleSystem) hiddenBitModelled where
  logical := PiInstitution.TheoryHom.identity (logicalTheory visibleSystem)
  operational := hiddenBitCover
  satisfaction_natural := by
    intro formula state
    change formula state ↔
      (institution.sentence.map
        (CategoryTheory.CategoryStruct.id (logicalTheory visibleSystem).signature)
        formula) (projectVisible (insertHiddenBit state))
    rw [institution.sentence.map_id_apply, projectVisible_insertHiddenBit]

/-- The target really has private state: setting the hidden bit to true lies
outside the image of the source representation. -/
theorem hiddenTrue_not_in_image :
    ¬ ∃ source : SemanticTerm (GSLT.discrete Bool),
      insertHiddenBit source =
        Quotient.mk hiddenBitTheory.equations (false, true) := by
  rintro ⟨source, equalClasses⟩
  induction source using Quotient.inductionOn with
  | _ visible =>
      have equalPairs : (visible, false) = (false, true) :=
        Quotient.exact equalClasses
      exact Bool.false_ne_true (congrArg Prod.snd equalPairs)

/-- The same private distinction is intentionally invisible to every native
sentence of this node. -/
theorem hiddenBits_have_same_native_reading
    (formula : institution.sentence.obj (logicalTheory visibleSystem).signature) :
    hiddenBitOperationalFace.interpret formula
        (Quotient.mk hiddenBitTheory.equations (false, false)) ↔
      hiddenBitOperationalFace.interpret formula
        (Quotient.mk hiddenBitTheory.equations (false, true)) :=
  Iff.rfl

/-- Positive and negative control together: the visible and hidden-bit
modelled theories have one identical semantic NIK image, yet the hidden
operational state is not in the image of the visible representation. -/
theorem same_nik_object_but_private_operational_state :
    (ModelledTheory.semanticTargetFunctor institution).obj (equipped visibleSystem) =
      (ModelledTheory.semanticTargetFunctor institution).obj hiddenBitModelled ∧
    ¬ ∃ source : SemanticTerm (GSLT.discrete Bool),
      insertHiddenBit source =
        Quotient.mk hiddenBitTheory.equations (false, true) :=
  ⟨rfl, hiddenTrue_not_in_image⟩

end SemanticPredicateCanary

#print axioms ModelledTheory.Hom.id
#print axioms ModelledTheory.Hom.comp
#print axioms logicalProjection
#print axioms operationalProjection
#print axioms ModelledTheory.no_hom_of_operational_escape
#print axioms SemanticPredicateCanary.operationalFace
#print axioms SemanticPredicateCanary.hiddenBitRoute
#print axioms SemanticPredicateCanary.projectVisible_insertHiddenBit
#print axioms SemanticPredicateCanary.hiddenTrue_not_in_image
#print axioms SemanticPredicateCanary.hiddenBits_have_same_native_reading
#print axioms SemanticPredicateCanary.same_nik_object_but_private_operational_state
#print axioms ModelledTheory.semanticTargetFunctor

end Mettapedia.GSLT.LanguageDef
