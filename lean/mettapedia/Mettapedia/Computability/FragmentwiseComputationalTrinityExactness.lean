import Mettapedia.Computability.FragmentwiseComputationalTrinity
import Mathlib.CategoryTheory.Discrete.Basic

/-!
# Exactness on selected computational-trinity fragments

A commuting trinity comparison supplies forward interpretations, but a useful
local equivalence needs three logically independent properties:

* soundness: admitted source elements map to admitted target elements;
* completeness on the selected target: every admitted target element has an
  admitted source representative; and
* faithfulness: distinct admitted source elements remain distinct.

`ExactBridge` packages precisely these obligations.  Its interpretation is a
pointwise bijection between the selected subtypes, and exact bridges compose.
Two adjacent exact bridges therefore induce an exact program-to-space bridge
through a coherent computational-trinity triangle.

The canaries distinguish local exactness from global collapse.  The first-bit
interpretation is exact on a singleton fragment, while on the complete source
and target it is sound and complete but not faithful.  Thus agreement about
which judgments hold does not by itself preserve program or proof identity.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.FragmentwiseComputationalTrinityExactness

open CategoryTheory
open Mettapedia.Computability.ComputationalTrinity
open Mettapedia.Computability.FragmentwiseComputationalTrinity

universe u v w

variable {Context : Type u} [Category.{v} Context]

namespace Constraint

variable {face : Face.{u, v, w} Context}

/-- The selected elements of a contextual constraint form a subpresheaf.
Substitution closure is exactly the data needed for its functorial action. -/
def constraintSubface (constraint : Constraint face) : Face.{u, v, w} Context where
  obj context :=
    { element : face.obj context // constraint.holds context element }
  map {source target} substitution :=
    TypeCat.ofHom (fun element ↦
      ⟨face.map substitution element.1,
        constraint.map_closed substitution element.2⟩)
  map_id := by
    intro context
    ext element
    simp
  map_comp := by
    intro source middle target first second
    ext element
    simp

/-- The complete substitution-stable fragment of a face. -/
def total (face : Face.{u, v, w} Context) : Constraint face where
  holds _ _ := True
  map_closed := by
    intro source target substitution element admitted
    trivial

@[simp] theorem total_holds (context : Contextᵒᵖ) (element : face.obj context) :
    (total face).holds context element :=
  True.intro

end Constraint

/-! ## Exact bridges between selected fragments -/

/-- An interpretation is exact on two selected fragments when it is sound,
complete on the selected target, and faithful on admitted source elements.

Completeness is deliberately a representability statement, not merely the
reflection of truth along the interpretation. -/
structure ExactBridge
    {source target : Face.{u, v, w} Context}
    (interpretation : source ⟶ target)
    (sourceFragment : Constraint source)
    (targetFragment : Constraint target) where
  sound :
    (sourceFragment.pushforward interpretation).Entails targetFragment
  complete :
    targetFragment.Entails (sourceFragment.pushforward interpretation)
  faithful : ∀ context {left right},
    sourceFragment.holds context left →
      sourceFragment.holds context right →
        interpretation.app context left = interpretation.app context right →
          left = right

namespace ExactBridge

variable {source middle target : Face.{u, v, w} Context}
variable {sourceFragment : Constraint source}
variable {middleFragment : Constraint middle}
variable {targetFragment : Constraint target}

/-- The interpretation restricted to the selected source and target
subtypes. -/
def restrictedMap
    {interpretation : source ⟶ target}
    (bridge : ExactBridge interpretation sourceFragment targetFragment)
    (context : Contextᵒᵖ) :
    { element : source.obj context //
        sourceFragment.holds context element } →
      { element : target.obj context //
        targetFragment.holds context element } :=
  fun element ↦
    ⟨interpretation.app context element.1,
      bridge.sound context _ ⟨element.1, element.2, rfl⟩⟩

/-- Exactness is a pointwise bijection between the selected subobjects. -/
theorem restrictedMap_bijective
    {interpretation : source ⟶ target}
    (bridge : ExactBridge interpretation sourceFragment targetFragment)
    (context : Contextᵒᵖ) :
    Function.Bijective (bridge.restrictedMap context) := by
  constructor
  · intro left right equality
    apply Subtype.ext
    apply bridge.faithful context left.2 right.2
    exact congrArg Subtype.val equality
  · intro targetElement
    rcases bridge.complete context targetElement.1 targetElement.2 with
      ⟨sourceElement, admitted, represented⟩
    refine ⟨⟨sourceElement, admitted⟩, ?_⟩
    apply Subtype.ext
    exact represented

/-- The pointwise restricted maps commute with contextual substitution. -/
def restrictedNatTrans
    {interpretation : source ⟶ target}
    (bridge : ExactBridge interpretation sourceFragment targetFragment) :
    Constraint.constraintSubface sourceFragment ⟶
      Constraint.constraintSubface targetFragment where
  app context := TypeCat.ofHom (bridge.restrictedMap context)
  naturality := by
    intro first second substitution
    ext element
    apply Subtype.ext
    change interpretation.app second
        (source.map substitution element.1) =
      target.map substitution
        (interpretation.app first element.1)
    exact congrArg (fun morphism ↦ morphism element.1)
      (interpretation.naturality substitution)

/-- Every exact fragment bridge supplies an actual equivalence of its
selected pointwise carriers. -/
noncomputable def equivalenceAt
    {interpretation : source ⟶ target}
    (bridge : ExactBridge interpretation sourceFragment targetFragment)
    (context : Contextᵒᵖ) :
    { element : source.obj context //
        sourceFragment.holds context element } ≃
      { element : target.obj context //
        targetFragment.holds context element } :=
  Equiv.ofBijective (bridge.restrictedMap context)
    (bridge.restrictedMap_bijective context)

/-- An exact bridge is a natural isomorphism between the selected
subpresheaves, not merely a family of unrelated bijections. -/
noncomputable def subfaceIso
    {interpretation : source ⟶ target}
    (bridge : ExactBridge interpretation sourceFragment targetFragment) :
    Constraint.constraintSubface sourceFragment ≅
      Constraint.constraintSubface targetFragment :=
  NatIso.ofComponents
    (fun context ↦ (bridge.equivalenceAt context).toIso)
    (by
      intro first second substitution
      ext element
      apply Subtype.ext
      change interpretation.app second
          (source.map substitution element.1) =
        target.map substitution
          (interpretation.app first element.1)
      exact congrArg (fun morphism ↦ morphism element.1)
        (interpretation.naturality substitution))

/-- Exactness is stable under replacing an interpretation by an equal natural
transformation. -/
def congr
    {first second : source ⟶ target}
    (same : first = second)
    (bridge : ExactBridge first sourceFragment targetFragment) :
    ExactBridge second sourceFragment targetFragment := by
  subst second
  exact bridge

/-- Identity interpretation is exact on every selected fragment. -/
def identity (fragment : Constraint source) :
    ExactBridge (𝟙 source) fragment fragment where
  sound := by
    intro context element represented
    rcases represented with ⟨sourceElement, admitted, rfl⟩
    exact admitted
  complete := by
    intro context element admitted
    exact ⟨element, admitted, rfl⟩
  faithful := by
    intro context left right leftAdmitted rightAdmitted same
    exact same

/-- Exact bridges compose: soundness, selected-target coverage, and
faithfulness are each preserved. -/
def comp
    {first : source ⟶ middle} {second : middle ⟶ target}
    (sourceMiddle : ExactBridge first sourceFragment middleFragment)
    (middleTarget : ExactBridge second middleFragment targetFragment) :
    ExactBridge (first ≫ second) sourceFragment targetFragment where
  sound := by
    intro context targetElement represented
    rcases represented with ⟨sourceElement, sourceAdmitted, rfl⟩
    have middleAdmitted : middleFragment.holds context
        (first.app context sourceElement) :=
      sourceMiddle.sound context _ ⟨sourceElement, sourceAdmitted, rfl⟩
    exact middleTarget.sound context _
      ⟨first.app context sourceElement, middleAdmitted, rfl⟩
  complete := by
    intro context targetElement targetAdmitted
    rcases middleTarget.complete context targetElement targetAdmitted with
      ⟨middleElement, middleAdmitted, middleRepresents⟩
    rcases sourceMiddle.complete context middleElement middleAdmitted with
      ⟨sourceElement, sourceAdmitted, sourceRepresents⟩
    refine ⟨sourceElement, sourceAdmitted, ?_⟩
    change second.app context (first.app context sourceElement) = targetElement
    rw [sourceRepresents, middleRepresents]
  faithful := by
    intro context left right leftAdmitted rightAdmitted sameTarget
    have leftMiddleAdmitted : middleFragment.holds context
        (first.app context left) :=
      sourceMiddle.sound context _ ⟨left, leftAdmitted, rfl⟩
    have rightMiddleAdmitted : middleFragment.holds context
        (first.app context right) :=
      sourceMiddle.sound context _ ⟨right, rightAdmitted, rfl⟩
    have sameMiddle : first.app context left = first.app context right := by
      apply middleTarget.faithful context leftMiddleAdmitted rightMiddleAdmitted
      exact sameTarget
    exact sourceMiddle.faithful context leftAdmitted rightAdmitted sameMiddle

end ExactBridge

/-! ## Exact fragmentwise computational trinity -/

/-- A computational-trinity comparison which is exact only on three named
fragments.  No global equivalence of the complete faces is asserted. -/
structure ExactFragmentwiseComparison
    (comparison : Comparison.{u, v, w} Context) where
  programFragment : Constraint comparison.program
  logicFragment : Constraint comparison.logic
  spaceFragment : Constraint comparison.space
  programLogic : ExactBridge comparison.programToLogic
    programFragment logicFragment
  logicSpace : ExactBridge comparison.logicToSpace
    logicFragment spaceFragment

namespace ExactFragmentwiseComparison

variable {comparison : Comparison.{u, v, w} Context}

/-- Forget target coverage and faithfulness while retaining the existing
forward fragmentwise comparison. -/
def toFragmentwiseComparison
    (exact : ExactFragmentwiseComparison comparison) :
    ComputationalTrinity.FragmentwiseComparison comparison where
  programFragment := exact.programFragment
  logicFragment := exact.logicFragment
  spaceFragment := exact.spaceFragment
  programLogicCompatible := exact.programLogic.sound
  logicSpaceCompatible := exact.logicSpace.sound

/-- Two adjacent exact fragment bridges induce an exact direct
program-to-space bridge. -/
def programSpace (exact : ExactFragmentwiseComparison comparison) :
    ExactBridge comparison.programToSpace exact.programFragment
      exact.spaceFragment :=
  (exact.programLogic.comp exact.logicSpace).congr comparison.coherence

/-- The direct program-to-space interpretation is a pointwise bijection on
the selected fragments. -/
theorem programSpace_bijective
    (exact : ExactFragmentwiseComparison comparison)
    (context : Contextᵒᵖ) :
    Function.Bijective (exact.programSpace.restrictedMap context) :=
  exact.programSpace.restrictedMap_bijective context

end ExactFragmentwiseComparison

/-! ## Positive and negative first-bit canaries -/

namespace FirstBit

open ComputationalTrinity.FirstBitObservation

private def here : ComputationalTrinity.FirstBitObservation.Contextᵒᵖ :=
  Opposite.op (Discrete.mk PUnit.unit)

/-- A singleton operational slice on which the otherwise lossy first-bit map
becomes faithful. -/
def onlyFalseFalse : Constraint comparison.program where
  holds _ program := program = (false, false)
  map_closed := by
    intro source target substitution program admitted
    exact admitted

def onlyFalseLogic : Constraint comparison.logic where
  holds _ proposition := proposition = false
  map_closed := by
    intro source target substitution proposition admitted
    exact admitted

def onlyFalseSpace : Constraint comparison.space where
  holds _ point := point = false
  map_closed := by
    intro source target substitution point admitted
    exact admitted

/-- The first-bit interpretation is exact on the selected singleton slice. -/
def programLogicExact : ExactBridge comparison.programToLogic
    onlyFalseFalse onlyFalseLogic where
  sound := by
    intro context logicalElement represented
    rcases represented with ⟨program, admitted, rfl⟩
    change program.1 = false
    rw [admitted]
  complete := by
    intro context logicalElement admitted
    refine ⟨(false, false), rfl, ?_⟩
    exact admitted.symm
  faithful := by
    intro context left right leftAdmitted rightAdmitted same
    exact leftAdmitted.trans rightAdmitted.symm

def logicSpaceExact : ExactBridge comparison.logicToSpace
    onlyFalseLogic onlyFalseSpace where
  sound := by
    intro context point represented
    rcases represented with ⟨proposition, admitted, rfl⟩
    exact admitted
  complete := by
    intro context point admitted
    exact ⟨point, admitted, rfl⟩
  faithful := by
    intro context left right leftAdmitted rightAdmitted same
    exact same

/-- A genuine exact trinity exists on the selected slice even though the
ambient comparison remains information-losing. -/
def selectedExact : ExactFragmentwiseComparison comparison where
  programFragment := onlyFalseFalse
  logicFragment := onlyFalseLogic
  spaceFragment := onlyFalseSpace
  programLogic := programLogicExact
  logicSpace := logicSpaceExact

theorem selected_programSpace_bijective :
    Function.Bijective (selectedExact.programSpace.restrictedMap here) :=
  selectedExact.programSpace_bijective here

/-- Globally, the first-bit map is sound on the complete fragments. -/
theorem total_programLogic_sound :
    ((Constraint.total comparison.program).pushforward
      comparison.programToLogic).Entails
        (Constraint.total comparison.logic) := by
  intro context logicalElement represented
  trivial

/-- Globally, every logical bit is represented by a program pair, so the map
is also complete on the complete fragments. -/
theorem total_programLogic_complete :
    (Constraint.total comparison.logic).Entails
      ((Constraint.total comparison.program).pushforward
        comparison.programToLogic) := by
  intro context logicalElement admitted
  exact ⟨(logicalElement, false), trivial, rfl⟩

/-- Soundness and selected-target completeness do not recover the hidden
second bit: no exact bridge exists on the complete fragments. -/
theorem no_total_programLogic_exact :
    ¬ Nonempty
      (ExactBridge comparison.programToLogic
        (Constraint.total comparison.program)
        (Constraint.total comparison.logic)) := by
  rintro ⟨bridge⟩
  have equalPairs : (false, false) = (false, true) :=
    bridge.faithful here trivial trivial rfl
  have equalSeconds := congrArg Prod.snd equalPairs
  simp at equalSeconds

/-- The negative control isolates faithfulness as the missing obligation. -/
theorem sound_complete_but_not_exact :
    ((Constraint.total comparison.program).pushforward
        comparison.programToLogic).Entails
          (Constraint.total comparison.logic) ∧
      (Constraint.total comparison.logic).Entails
        ((Constraint.total comparison.program).pushforward
          comparison.programToLogic) ∧
      ¬ Nonempty
        (ExactBridge comparison.programToLogic
          (Constraint.total comparison.program)
          (Constraint.total comparison.logic)) :=
  ⟨total_programLogic_sound, total_programLogic_complete,
    no_total_programLogic_exact⟩

end FirstBit

#print axioms ExactBridge.restrictedMap_bijective
#print axioms ExactBridge.restrictedNatTrans
#print axioms ExactBridge.equivalenceAt
#print axioms ExactBridge.subfaceIso
#print axioms ExactBridge.comp
#print axioms ExactFragmentwiseComparison.programSpace_bijective
#print axioms FirstBit.selected_programSpace_bijective
#print axioms FirstBit.sound_complete_but_not_exact

end Mettapedia.Computability.FragmentwiseComputationalTrinityExactness
