import Mettapedia.Computability.ComputationalTrinity

/-!
# Fragmentwise computational trinity

A computational trinity need not be fixed globally before it can guide a
language design.  A useful fragment of any face is a contextual constraint: a
predicate on its generalized elements that is stable under substitution.  A
map of faces then transports constraints in both directions:

* existential image sends an admitted source fragment forward; and
* inverse image sends a requirement on a target face backward.

These transports form an adjunction.  Thus operational, logical, and spatial
requirements exert mathematically explicit pressure on one another without
assuming that any complete face has already been selected.  The commuting
triangle of a `Comparison` makes direct and two-step transport agree.

Information loss remains visible.  If an interpretation identifies two
source elements, no constraint pulled back from its target can distinguish
them.  An intensional distinction inside such a fibre must therefore remain
on the source side or force a refinement of the target and its interpretation.
-/

namespace Mettapedia.Computability.FragmentwiseComputationalTrinity

open CategoryTheory
open Mettapedia.Computability.ComputationalTrinity

universe u v w

variable {Context : Type u} [Category.{v} Context]

/-- A substitution-stable predicate on one contextual semantic face.  It is
the predicate presentation of a subpresheaf, used here because implication and
existential image are the relevant operations. -/
structure Constraint (face : Face.{u, v, w} Context) where
  holds : (context : Contextᵒᵖ) → face.obj context → Prop
  map_closed : ∀ {source target : Contextᵒᵖ}
      (substitution : source ⟶ target) {element : face.obj source},
    holds source element →
      holds target (face.map substitution element)

namespace Constraint

variable {sourceFace targetFace thirdFace : Face.{u, v, w} Context}

/-- Pointwise implication between contextual constraints. -/
def Entails (left right : Constraint sourceFace) : Prop :=
  ∀ context element, left.holds context element → right.holds context element

/-- Two constraints select the same contextual fragment. -/
def Equivalent (left right : Constraint sourceFace) : Prop :=
  left.Entails right ∧ right.Entails left

theorem entails_refl (constraint : Constraint sourceFace) :
    constraint.Entails constraint := by
  intro context element proof
  exact proof

theorem Entails.trans {first second third : Constraint sourceFace}
    (firstSecond : first.Entails second)
    (secondThird : second.Entails third) :
    first.Entails third := by
  intro context element proof
  exact secondThird context element (firstSecond context element proof)

theorem equivalent_refl (constraint : Constraint sourceFace) :
    constraint.Equivalent constraint :=
  ⟨entails_refl constraint, entails_refl constraint⟩

theorem Equivalent.symm {left right : Constraint sourceFace}
    (equivalent : left.Equivalent right) : right.Equivalent left :=
  ⟨equivalent.2, equivalent.1⟩

theorem Equivalent.trans {first second third : Constraint sourceFace}
    (firstSecond : first.Equivalent second)
    (secondThird : second.Equivalent third) :
    first.Equivalent third :=
  ⟨firstSecond.1.trans secondThird.1,
    secondThird.2.trans firstSecond.2⟩

private theorem naturality_apply
    (interpretation : sourceFace ⟶ targetFace)
    {source target : Contextᵒᵖ} (substitution : source ⟶ target)
    (element : sourceFace.obj source) :
    interpretation.app target (sourceFace.map substitution element) =
      targetFace.map substitution (interpretation.app source element) := by
  exact
    congrArg (fun morphism => morphism element)
      (interpretation.naturality substitution)

/-- Inverse image transports a requirement on a target face back to the
source face. -/
def pullback (interpretation : sourceFace ⟶ targetFace)
    (targetConstraint : Constraint targetFace) : Constraint sourceFace where
  holds context sourceElement :=
    targetConstraint.holds context
      (interpretation.app context sourceElement)
  map_closed := by
    intro source target substitution element proof
    rw [naturality_apply interpretation substitution element]
    exact targetConstraint.map_closed substitution proof

/-- Existential image transports an admitted source fragment forward.  It
retains a source witness rather than assuming that the interpretation is
surjective or injective. -/
def pushforward (interpretation : sourceFace ⟶ targetFace)
    (sourceConstraint : Constraint sourceFace) : Constraint targetFace where
  holds context targetElement :=
    ∃ sourceElement, sourceConstraint.holds context sourceElement ∧
      interpretation.app context sourceElement = targetElement
  map_closed := by
    intro source target substitution targetElement proof
    rcases proof with ⟨sourceElement, admitted, rfl⟩
    refine ⟨sourceFace.map substitution sourceElement,
      sourceConstraint.map_closed substitution admitted, ?_⟩
    exact naturality_apply interpretation substitution sourceElement

/-- Existential image is left adjoint to inverse image on the entailment
preorders of contextual constraints.  This is the formal bidirectional-design
law: sending an admitted fragment forward is equivalent to pulling the target
requirement backward. -/
theorem pushforward_entails_iff_entails_pullback
    (interpretation : sourceFace ⟶ targetFace)
    (sourceConstraint : Constraint sourceFace)
    (targetConstraint : Constraint targetFace) :
    (sourceConstraint.pushforward interpretation).Entails targetConstraint ↔
      sourceConstraint.Entails
        (targetConstraint.pullback interpretation) := by
  constructor
  · intro forward context sourceElement admitted
    exact forward context (interpretation.app context sourceElement)
      ⟨sourceElement, admitted, rfl⟩
  · intro backward context targetElement represented
    rcases represented with ⟨sourceElement, admitted, rfl⟩
    exact backward context sourceElement admitted

theorem pullback_mono (interpretation : sourceFace ⟶ targetFace)
    {first second : Constraint targetFace} (entails : first.Entails second) :
    (first.pullback interpretation).Entails
      (second.pullback interpretation) := by
  intro context element proof
  exact entails context (interpretation.app context element) proof

theorem pushforward_mono (interpretation : sourceFace ⟶ targetFace)
    {first second : Constraint sourceFace} (entails : first.Entails second) :
    (first.pushforward interpretation).Entails
      (second.pushforward interpretation) := by
  intro context targetElement proof
  rcases proof with ⟨sourceElement, admitted, represented⟩
  exact ⟨sourceElement, entails context sourceElement admitted, represented⟩

/-! ## Extensionalization along an interpretation

Sending a source constraint forward and pulling it back saturates the
constraint along the fibres of the interpretation.  This is the precise
constraint-level form of forgetting intensional information: once two source
elements have the same target image, the saturated constraint treats them
alike. -/

/-- The least constraint obtained from `sourceConstraint` by making every
interpretation fibre observationally uniform. -/
def saturate (interpretation : sourceFace ⟶ targetFace)
    (sourceConstraint : Constraint sourceFace) : Constraint sourceFace :=
  (sourceConstraint.pushforward interpretation).pullback interpretation

/-- A constraint is extensional for an interpretation when it is constant
along every interpretation fibre. -/
def FibreClosed (interpretation : sourceFace ⟶ targetFace)
    (sourceConstraint : Constraint sourceFace) : Prop :=
  ∀ context left right,
    interpretation.app context left = interpretation.app context right →
      sourceConstraint.holds context left →
        sourceConstraint.holds context right

/-- Extensionalization never removes an admitted source element. -/
theorem entails_saturate
    (interpretation : sourceFace ⟶ targetFace)
    (sourceConstraint : Constraint sourceFace) :
    sourceConstraint.Entails (sourceConstraint.saturate interpretation) := by
  intro context sourceElement admitted
  exact ⟨sourceElement, admitted, rfl⟩

/-- A saturated constraint is constant on interpretation fibres. -/
theorem saturate_fibreClosed
    (interpretation : sourceFace ⟶ targetFace)
    (sourceConstraint : Constraint sourceFace) :
    (sourceConstraint.saturate interpretation).FibreClosed interpretation := by
  intro context left right sameImage leftSaturated
  rcases leftSaturated with ⟨witness, admitted, witnessImage⟩
  exact ⟨witness, admitted, witnessImage.trans sameImage⟩

/-- Saturation entails the original constraint exactly when the original was
already constant on every interpretation fibre. -/
theorem saturate_entails_iff_fibreClosed
    (interpretation : sourceFace ⟶ targetFace)
    (sourceConstraint : Constraint sourceFace) :
    (sourceConstraint.saturate interpretation).Entails sourceConstraint ↔
      sourceConstraint.FibreClosed interpretation := by
  constructor
  · intro saturatedToSource context left right sameImage leftAdmitted
    exact saturatedToSource context right
      ⟨left, leftAdmitted, sameImage⟩
  · intro fibreClosed context targetElement saturated
    rcases saturated with ⟨sourceElement, admitted, sameImage⟩
    exact fibreClosed context sourceElement targetElement sameImage admitted

/-- A constraint is unchanged by extensionalization exactly when it was
already extensional for the chosen interpretation. -/
theorem equivalent_saturate_iff_fibreClosed
    (interpretation : sourceFace ⟶ targetFace)
    (sourceConstraint : Constraint sourceFace) :
    sourceConstraint.Equivalent (sourceConstraint.saturate interpretation) ↔
      sourceConstraint.FibreClosed interpretation := by
  constructor
  · intro equivalent
    exact (saturate_entails_iff_fibreClosed interpretation
      sourceConstraint).1 equivalent.2
  · intro fibreClosed
    exact ⟨entails_saturate interpretation sourceConstraint,
      (saturate_entails_iff_fibreClosed interpretation
        sourceConstraint).2 fibreClosed⟩

/-- Extensionalization is idempotent up to the extensional equality of
constraints. -/
theorem saturate_idempotent
    (interpretation : sourceFace ⟶ targetFace)
    (sourceConstraint : Constraint sourceFace) :
    (sourceConstraint.saturate interpretation).saturate interpretation
      |>.Equivalent (sourceConstraint.saturate interpretation) := by
  exact
    ((equivalent_saturate_iff_fibreClosed interpretation
      (sourceConstraint.saturate interpretation)).2
        (saturate_fibreClosed interpretation sourceConstraint)).symm

/-- Reflecting a target requirement to the source and projecting it back
cannot invent a target element outside that requirement. -/
theorem pushforward_pullback_entails
    (interpretation : sourceFace ⟶ targetFace)
    (targetConstraint : Constraint targetFace) :
    (targetConstraint.pullback interpretation |>.pushforward interpretation)
      |>.Entails targetConstraint := by
  intro context targetElement represented
  rcases represented with ⟨sourceElement, admitted, rfl⟩
  exact admitted

/-- Pulling a requirement back along two interpretations agrees with pulling
it back along their composite. -/
theorem pullback_comp_equivalent
    (first : sourceFace ⟶ targetFace)
    (second : targetFace ⟶ thirdFace)
    (constraint : Constraint thirdFace) :
    (constraint.pullback second |>.pullback first).Equivalent
      (constraint.pullback (first ≫ second)) := by
  constructor <;> intro context element proof <;> exact proof

/-- Sending a fragment forward in two steps agrees with sending it along the
composite; the intermediate witness is retained existentially. -/
theorem pushforward_comp_equivalent
    (first : sourceFace ⟶ targetFace)
    (second : targetFace ⟶ thirdFace)
    (constraint : Constraint sourceFace) :
    (constraint.pushforward first |>.pushforward second).Equivalent
      (constraint.pushforward (first ≫ second)) := by
  constructor
  · intro context targetElement proof
    rcases proof with
      ⟨middleElement, ⟨sourceElement, admitted, sourceToMiddle⟩,
        middleToTarget⟩
    refine ⟨sourceElement, admitted, ?_⟩
    subst middleElement
    exact middleToTarget
  · intro context targetElement proof
    rcases proof with ⟨sourceElement, admitted, represented⟩
    refine ⟨first.app context sourceElement,
      ⟨sourceElement, admitted, rfl⟩, ?_⟩
    exact represented

/-- A target-side requirement cannot distinguish elements identified by the
interpretation.  This is the exact obstruction to recovering an intensional
distinction from a more extensional face. -/
theorem pullback_agrees_on_fibre
    (interpretation : sourceFace ⟶ targetFace)
    (constraint : Constraint targetFace)
    {context : Contextᵒᵖ} {left right : sourceFace.obj context}
    (sameImage : interpretation.app context left =
      interpretation.app context right) :
    (constraint.pullback interpretation).holds context left ↔
      (constraint.pullback interpretation).holds context right := by
  change constraint.holds context (interpretation.app context left) ↔
    constraint.holds context (interpretation.app context right)
  rw [sameImage]

/-- If a source constraint separates two elements in one interpretation
fibre, it cannot be equivalent to any requirement pulled back from the target.
The target or the interpretation must be refined if that distinction is to
become spatially or logically visible. -/
theorem not_equivalent_pullback_of_separates_fibre
    (interpretation : sourceFace ⟶ targetFace)
    (sourceConstraint : Constraint sourceFace)
    (targetConstraint : Constraint targetFace)
    {context : Contextᵒᵖ} {left right : sourceFace.obj context}
    (sameImage : interpretation.app context left =
      interpretation.app context right)
    (leftAdmitted : sourceConstraint.holds context left)
    (rightRejected : ¬ sourceConstraint.holds context right) :
    ¬ sourceConstraint.Equivalent
      (targetConstraint.pullback interpretation) := by
  intro equivalent
  have leftPulledBack := equivalent.1 context left leftAdmitted
  have rightPulledBack :=
    (pullback_agrees_on_fibre interpretation targetConstraint sameImage).1
      leftPulledBack
  exact rightRejected (equivalent.2 context right rightPulledBack)

end Constraint

/-! ## Local compatibility inside a comparison candidate -/

namespace ComputationalTrinity

/-- One fragmentwise, revisable candidate inside a comparison triangle.  It
does not assert global equivalence of the faces.  Each field says only that an
admitted fragment is carried into the next selected fragment. -/
structure FragmentwiseComparison
    (comparison : Comparison.{u, v, w} Context) where
  programFragment : Constraint comparison.program
  logicFragment : Constraint comparison.logic
  spaceFragment : Constraint comparison.space
  programLogicCompatible :
    (programFragment.pushforward comparison.programToLogic).Entails
      logicFragment
  logicSpaceCompatible :
    (logicFragment.pushforward comparison.logicToSpace).Entails
      spaceFragment

namespace FragmentwiseComparison

variable {comparison : Comparison.{u, v, w} Context}

/-- Compatibility with the direct program-to-space interpretation follows
from the two local compatibility obligations and triangle coherence. -/
theorem programSpaceCompatible
    (fragmentwise : FragmentwiseComparison comparison) :
    (fragmentwise.programFragment.pushforward
      comparison.programToSpace).Entails fragmentwise.spaceFragment := by
  intro context spatialElement represented
  rcases represented with ⟨program, admitted, rfl⟩
  have logicAdmitted : fragmentwise.logicFragment.holds context
      (comparison.programToLogic.app context program) :=
    fragmentwise.programLogicCompatible context _
      ⟨program, admitted, rfl⟩
  have spaceAdmitted : fragmentwise.spaceFragment.holds context
      (comparison.logicToSpace.app context
        (comparison.programToLogic.app context program)) :=
    fragmentwise.logicSpaceCompatible context _
      ⟨comparison.programToLogic.app context program,
        logicAdmitted, rfl⟩
  rw [comparison.coherence_apply context program] at spaceAdmitted
  exact spaceAdmitted

/-- A spatial requirement exerts the same inverse pressure on programs
whether transported directly or through the logic face. -/
theorem spacePressureCoherent
    (comparison : Comparison.{u, v, w} Context)
    (requirement : Constraint comparison.space) :
    (requirement.pullback comparison.logicToSpace |>.pullback
      comparison.programToLogic).Equivalent
        (requirement.pullback comparison.programToSpace) := by
  constructor <;> intro context program proof
  · show requirement.holds context
      (comparison.programToSpace.app context program)
    rw [← comparison.coherence_apply context program]
    exact proof
  · show requirement.holds context
      (comparison.logicToSpace.app context
        (comparison.programToLogic.app context program))
    rw [comparison.coherence_apply context program]
    exact proof

/-- A selected program fragment exerts the same forward pressure on spaces
whether transported directly or through the logic face. -/
theorem programPressureCoherent
    (comparison : Comparison.{u, v, w} Context)
    (fragment : Constraint comparison.program) :
    (fragment.pushforward comparison.programToLogic |>.pushforward
      comparison.logicToSpace).Equivalent
        (fragment.pushforward comparison.programToSpace) := by
  constructor
  · intro context spatialElement represented
    rcases represented with
      ⟨logicalElement, ⟨program, admitted, programToLogic⟩,
        logicToSpace⟩
    subst logicalElement
    refine ⟨program, admitted, ?_⟩
    rw [← comparison.coherence_apply context program]
    exact logicToSpace
  · intro context spatialElement represented
    rcases represented with ⟨program, admitted, programToSpace⟩
    refine ⟨comparison.programToLogic.app context program,
      ⟨program, admitted, rfl⟩, ?_⟩
    rw [comparison.coherence_apply context program]
    exact programToSpace

end FragmentwiseComparison

end ComputationalTrinity

#print axioms Constraint.pushforward_entails_iff_entails_pullback
#print axioms Constraint.equivalent_saturate_iff_fibreClosed
#print axioms Constraint.saturate_idempotent
#print axioms Constraint.pushforward_pullback_entails
#print axioms Constraint.pullback_agrees_on_fibre
#print axioms Constraint.not_equivalent_pullback_of_separates_fibre
#print axioms ComputationalTrinity.FragmentwiseComparison.programSpaceCompatible
#print axioms ComputationalTrinity.FragmentwiseComparison.spacePressureCoherent
#print axioms ComputationalTrinity.FragmentwiseComparison.programPressureCoherent

end Mettapedia.Computability.FragmentwiseComputationalTrinity
