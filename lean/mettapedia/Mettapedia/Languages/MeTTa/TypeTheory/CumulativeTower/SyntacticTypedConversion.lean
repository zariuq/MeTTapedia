import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.SyntacticJudgmentalSigmaId

/-!
# Conversion whose intermediate types are intrinsically formed

The formed-endpoint conversion layer deliberately refines Prime's existing
raw conversion relation. Its intermediate syntax is retained, but formation
of those intermediate codes is not inferred from endpoint formation.

This module gives the stronger object without assuming subject expansion.
A displayed universe is itself a formed type. A displayed type is an
intrinsic term of that universe. Consequently a conversion between displayed
types is just ordinary proof-relevant term conversion inside one universe
fibre. Every reflexive, symmetric, or transitive intermediate is then
intrinsically typed by construction.

The construction is cumulative-presentation agnostic: it asks the hosted
calculus only for the two universe heads and the native formation judgment
between them. Forgetting a typed conversion yields the earlier
formed-endpoint conversion, but no converse is claimed. Lifting an arbitrary
raw path would require the separately named computation-preservation and,
for reversed steps, subject-expansion data.
-/

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace SyntacticTypedConversion

open CategoryTheory
open Declaration
open ProofRelevantStructuralComputation
open SyntacticContextual
open SyntacticJudgmentalPi
open SyntacticConversionEnrichment
open Mettapedia.TypeTheory.JudgmentalEquality

universe uEvidence

/-! ## Types displayed as terms of one universe -/

/-- A universe head displayed as a formed type in one context. The lower
head classifies the types in the fibre; the upper head classifies the
universe term itself. -/
structure DisplayedUniverse {rules : Rules Head}
    (context : FormedContext rules) where
  level : Head
  upper : Head
  levelIsUniverse : rules.isUniverse level
  upperIsUniverse : rules.isUniverse upper
  formation : rules.headTyping level upper

namespace DisplayedUniverse

/-- The universe code as a formed type over the ambient context. -/
def type {rules : Rules Head} {context : FormedContext rules}
    (display : DisplayedUniverse context) : TypeOver context where
  code := .head display.level
  level := display.upper
  isUniverse := display.upperIsUniverse
  formed := .headType display.formation

/-- A change of ambient context leaves the universe levels unchanged. -/
def reindex {rules : Rules Head}
    {source target : FormedContext rules}
    (display : DisplayedUniverse target) (_morphism : source ⟶ target) :
    DisplayedUniverse source where
  level := display.level
  upper := display.upper
  levelIsUniverse := display.levelIsUniverse
  upperIsUniverse := display.upperIsUniverse
  formation := display.formation

/-- Reindexing the formed universe type agrees exactly with the reindexed
display. -/
theorem type_reindex {rules : Rules Head}
    {source target : FormedContext rules}
    (display : DisplayedUniverse target) (morphism : source ⟶ target) :
    display.type.reindex morphism = (display.reindex morphism).type := by
  apply TypeOver.ext
  · rfl
  · rfl

end DisplayedUniverse

/-- A type displayed at one universe level is literally an intrinsic term of
that universe. This reuses the existing term judgment rather than introducing
a parallel type-formation relation. -/
abbrev DisplayedType {rules : Rules Head}
    {context : FormedContext rules} (display : DisplayedUniverse context) :=
  Term context display.type

namespace DisplayedType

/-- Forget that a displayed type was presented as a term of its universe,
retaining the same code and formation derivation as a TypeOver value. -/
def toTypeOver {rules : Rules Head}
    {context : FormedContext rules} {display : DisplayedUniverse context}
    (type : DisplayedType display) : TypeOver context where
  code := type.code
  level := display.level
  isUniverse := display.levelIsUniverse
  formed := type.typed

/-- Typed context substitution transports a displayed type into the
reindexed universe. -/
def reindex {rules : Rules Head}
    {source target : FormedContext rules}
    {display : DisplayedUniverse target}
    (type : DisplayedType display) (morphism : source ⟶ target) :
    DisplayedType (display.reindex morphism) :=
  Term.reindex type morphism

@[simp] theorem reindex_code {rules : Rules Head}
    {source target : FormedContext rules}
    {display : DisplayedUniverse target}
    (type : DisplayedType display) (morphism : source ⟶ target) :
    (type.reindex morphism).code =
      Presentation.subst morphism.substitution type.code := by
  rfl

end DisplayedType

/-! ## Fully typed conversion -/

/-- Proof-relevant conversion between types in one displayed universe. Every
intermediate of the conversion is a DisplayedType, hence carries its
formation derivation at the same universe level. -/
abbrev TypedTypeConversion {rules : Rules Head}
    (retained : RetainedRoot.{uEvidence} rules)
    {context : FormedContext rules}
    (display : DisplayedUniverse context)
    (source target : DisplayedType display) : Type uEvidence :=
  ConversionEvidence (termComputation retained context) source target

namespace TypedTypeConversion

/-- Forget intermediate formation while retaining the complete raw
structural conversion receipt. -/
def toStructural
    {retained : RetainedRoot.{uEvidence} rules}
    {context : FormedContext rules}
    {display : DisplayedUniverse context}
    {source target : DisplayedType display} :
    TypedTypeConversion retained display source target →
      StructuralConversionReceipt retained.computation rules.headEq
        source.code target.code
  | .step receipt => .step receipt
  | .refl state =>
      ConversionEvidence.refl
        (computation := rawStructuralComputation retained.computation
          rules.headEq context.arity)
        state.code
  | .symm conversion =>
      ConversionEvidence.symm
        (TypedTypeConversion.toStructural conversion)
  | .trans first second =>
      ConversionEvidence.trans
        (TypedTypeConversion.toStructural first)
        (TypedTypeConversion.toStructural second)

/-- A fully typed conversion forgets to the formed-endpoint conversion layer.
The reverse direction is intentionally absent. -/
def toEndpointConversion
    {retained : RetainedRoot.{uEvidence} rules}
    {context : FormedContext rules}
    {display : DisplayedUniverse context}
    {source target : DisplayedType display}
    (conversion : TypedTypeConversion retained display source target) :
    TypeConversion retained source.toTypeOver target.toTypeOver where
  receipt := conversion.toStructural

/-- Reindex a fully typed conversion. The recursion transports every
intermediate typed state and every proof-relevant structural step. -/
def reindex
    {retained : RetainedRoot.{uEvidence} rules}
    {sourceContext targetContext : FormedContext rules}
    {display : DisplayedUniverse targetContext}
    {source target : DisplayedType display}
    (conversion : TypedTypeConversion retained display source target)
    (morphism : sourceContext ⟶ targetContext) :
    TypedTypeConversion retained (display.reindex morphism)
      (source.reindex morphism) (target.reindex morphism) :=
  match conversion with
  | .step receipt =>
      ConversionEvidence.step
        (computation := termComputation retained sourceContext)
        (by
          change StructuralStepReceipt retained.computation rules.headEq
            (source.reindex morphism).code (target.reindex morphism).code
          simpa only [DisplayedType.reindex, Term.cast_code,
            Term.reindex] using
            receipt.substitute morphism.substitution)
  | .refl state =>
      ConversionEvidence.refl
        (computation := termComputation retained sourceContext)
        (DisplayedType.reindex state morphism)
  | .symm nested =>
      ConversionEvidence.symm (TypedTypeConversion.reindex nested morphism)
  | .trans first second =>
      ConversionEvidence.trans
        (TypedTypeConversion.reindex first morphism)
        (TypedTypeConversion.reindex second morphism)

/-- Forgetting intrinsic intermediate formation is natural in the ambient
context: typed substitution followed by erasure is exactly raw substitution
of the retained structural receipt. -/
theorem toStructural_reindex
    {retained : RetainedRoot.{uEvidence} rules}
    {sourceContext targetContext : FormedContext rules}
    {display : DisplayedUniverse targetContext}
    {source target : DisplayedType display}
    (conversion : TypedTypeConversion retained display source target)
    (morphism : sourceContext ⟶ targetContext) :
    (conversion.reindex morphism).toStructural =
      conversion.toStructural.substitute morphism.substitution :=
  match conversion with
  | .step _ => rfl
  | .refl _ => rfl
  | .symm nested => by
      simp only [TypedTypeConversion.reindex,
        TypedTypeConversion.toStructural,
        StructuralConversionReceipt.substitute,
        StructuralConversionReceipt.mapCompatible]
      change ConversionEvidence.symm _ = ConversionEvidence.symm _
      exact congrArg
          (fun next => ConversionEvidence.symm next)
          (TypedTypeConversion.toStructural_reindex nested morphism)
  | .trans first second => by
      simp only [TypedTypeConversion.reindex,
        TypedTypeConversion.toStructural,
        StructuralConversionReceipt.substitute,
        StructuralConversionReceipt.mapCompatible]
      change ConversionEvidence.trans _ _ = ConversionEvidence.trans _ _
      exact congrArg₂
          (fun left right => ConversionEvidence.trans left right)
          (TypedTypeConversion.toStructural_reindex first morphism)
          (TypedTypeConversion.toStructural_reindex second morphism)

end TypedTypeConversion

/-! ## Oriented primitive receipt traces -/

/-- One primitive structural receipt together with the direction in which a
conversion traverses it.  The receipt retains its raw source and target as
dependent indices; `backward` changes only the traversal direction. -/
inductive OrientedStructuralReceipt
    (computation : ProofRelevantRootComputation.{uEvidence} Head)
    (headEq : Head → Head → Prop) (arity : Nat) :
    Type (max uEvidence 0) where
  | forward {source target : Tm Head arity} :
      StructuralStepReceipt computation headEq source target →
        OrientedStructuralReceipt computation headEq arity
  | backward {source target : Tm Head arity} :
      StructuralStepReceipt computation headEq source target →
        OrientedStructuralReceipt computation headEq arity

namespace OrientedStructuralReceipt

/-- Reverse the traversal direction without changing the retained primitive
receipt. -/
def reverse
    {computation : ProofRelevantRootComputation.{uEvidence} Head}
    {headEq : Head → Head → Prop} {arity : Nat} :
    OrientedStructuralReceipt computation headEq arity →
      OrientedStructuralReceipt computation headEq arity
  | .forward receipt => .backward receipt
  | .backward receipt => .forward receipt

@[simp] theorem reverse_reverse
    {computation : ProofRelevantRootComputation.{uEvidence} Head}
    {headEq : Head → Head → Prop} {arity : Nat}
    (receipt : OrientedStructuralReceipt computation headEq arity) :
    receipt.reverse.reverse = receipt := by
  cases receipt <;> rfl

end OrientedStructuralReceipt

namespace StructuralReceiptTrace

/-- Reverse a sequential trace: reverse its chronological order and reverse
the direction of every primitive receipt. -/
def reverse
    {computation : ProofRelevantRootComputation.{uEvidence} Head}
    {headEq : Head → Head → Prop} {arity : Nat}
    (trace : List (OrientedStructuralReceipt computation headEq arity)) :
    List (OrientedStructuralReceipt computation headEq arity) :=
  trace.reverse.map OrientedStructuralReceipt.reverse

@[simp] theorem reverse_nil
    {computation : ProofRelevantRootComputation.{uEvidence} Head}
    {headEq : Head → Head → Prop} {arity : Nat} :
    reverse ([] : List
      (OrientedStructuralReceipt computation headEq arity)) = [] := by
  rfl

@[simp] theorem reverse_singleton
    {computation : ProofRelevantRootComputation.{uEvidence} Head}
    {headEq : Head → Head → Prop} {arity : Nat}
    (receipt : OrientedStructuralReceipt computation headEq arity) :
    reverse [receipt] = [receipt.reverse] := by
  rfl

theorem reverse_append
    {computation : ProofRelevantRootComputation.{uEvidence} Head}
    {headEq : Head → Head → Prop} {arity : Nat}
    (first second :
      List (OrientedStructuralReceipt computation headEq arity)) :
    reverse (first ++ second) = reverse second ++ reverse first := by
  simp only [reverse, List.reverse_append, List.map_append]

@[simp] theorem reverse_reverse
    {computation : ProofRelevantRootComputation.{uEvidence} Head}
    {headEq : Head → Head → Prop} {arity : Nat}
    (trace : List (OrientedStructuralReceipt computation headEq arity)) :
    reverse (reverse trace) = trace := by
  simp only [reverse, List.map_reverse, List.reverse_reverse,
    List.map_map]
  have functionEquality :
      (OrientedStructuralReceipt.reverse ∘
          OrientedStructuralReceipt.reverse) =
        (id : OrientedStructuralReceipt computation headEq arity →
          OrientedStructuralReceipt computation headEq arity) := by
    funext receipt
    exact OrientedStructuralReceipt.reverse_reverse receipt
  rw [functionEquality, List.map_id]

/-- Flatten a raw conversion into its exact chronological sequence of
oriented primitive receipts.  Reflexivity contributes no primitive event;
symmetry reverses chronology and direction; transitivity concatenates. -/
def ofRaw
    {computation : ProofRelevantRootComputation.{uEvidence} Head}
    {headEq : Head → Head → Prop} {arity : Nat}
    {source target : Tm Head arity} :
    StructuralConversionReceipt computation headEq source target →
      List (OrientedStructuralReceipt computation headEq arity)
  | .step receipt => [.forward receipt]
  | .refl _ => []
  | .symm conversion => reverse (ofRaw conversion)
  | .trans first second => ofRaw first ++ ofRaw second

/-- Flatten an intrinsic typed conversion into the same raw oriented receipt
alphabet.  Only the typed states are forgotten; no primitive receipt is
discarded. -/
def ofTyped
    {rules : Rules Head}
    {retained : RetainedRoot.{uEvidence} rules}
    {context : FormedContext rules} {fibre : TypeOver context}
    {source target : Term context fibre} :
    ConversionEvidence (termComputation retained context) source target →
      List (OrientedStructuralReceipt retained.computation rules.headEq
        context.arity)
  | .step receipt => [.forward receipt]
  | .refl _ => []
  | .symm conversion => reverse (ofTyped conversion)
  | .trans first second => ofTyped first ++ ofTyped second

/-- Changing only the proof-carrying representation of the final typed state
does not change the primitive receipt trace. -/
@[simp] theorem ofTyped_castTarget
    {rules : Rules Head}
    {retained : RetainedRoot.{uEvidence} rules}
    {context : FormedContext rules} {fibre : TypeOver context}
    {source target target' : Term context fibre}
    (sameTarget : target = target')
    (conversion : ConversionEvidence (termComputation retained context)
      source target) :
    ofTyped (sameTarget ▸ conversion) = ofTyped conversion := by
  cases sameTarget
  rfl

/-- Erasing an already intrinsic conversion preserves its normalized
oriented primitive trace exactly. -/
theorem ofTyped_eq_ofRaw_toStructural
    {rules : Rules Head}
    {retained : RetainedRoot.{uEvidence} rules}
    {context : FormedContext rules}
    {display : DisplayedUniverse context}
    {source target : DisplayedType display}
    (conversion : TypedTypeConversion retained display source target) :
    ofTyped conversion = ofRaw conversion.toStructural := by
  refine ConversionEvidence.recOn
    (motive := fun _source _target conversion =>
      ofTyped conversion =
        ofRaw (TypedTypeConversion.toStructural
          (retained := retained) (context := context) (display := display)
          conversion))
    conversion ?_ ?_ ?_ ?_
  · intro _source _target _receipt
    rfl
  · intro _state
    rfl
  · intro _source _target _nested inductionHypothesis
    simpa only [ofTyped, TypedTypeConversion.toStructural, ofRaw] using
      congrArg reverse inductionHypothesis
  · intro _source _middle _target _first _second
      firstInduction secondInduction
    simpa only [ofTyped, TypedTypeConversion.toStructural, ofRaw] using
      congrArg₂ (fun left right => left ++ right)
        firstInduction secondInduction

end StructuralReceiptTrace

/-! ## The exact hypothesis needed to lift raw conversion -/

/-- A raw structural step is closed in both directions inside one formed
judgment fibre.  `forward` is ordinary subject reduction.  `backward` is the
additional subject-expansion obligation exposed by symmetric conversion.

This structure is deliberately stronger than the one-way preservation law
for an evaluator.  It is the exact local datum used below; no declaration
calculus is asserted to provide it until its native rules have been checked. -/
structure BidirectionalStepTyping {Head : Type} {rules : Rules Head}
    (retained : RetainedRoot.{uEvidence} rules)
    (context : FormedContext rules) (fibre : TypeOver context) where
  forward : ∀ {source target : Tm Head context.arity},
    StructuralStepReceipt retained.computation rules.headEq source target →
      HasType rules context.context source fibre.code →
        HasType rules context.context target fibre.code
  backward : ∀ {source target : Tm Head context.arity},
    StructuralStepReceipt retained.computation rules.headEq source target →
      HasType rules context.context target fibre.code →
        HasType rules context.context source fibre.code

namespace BidirectionalStepTyping

/-- The result of lifting toward one raw endpoint: a typing derivation for
that endpoint together with the intrinsically typed conversion that reaches
it.  A named structure is needed because `HasType` is proposition-valued,
while the retained conversion receipt is proof-relevant data. -/
structure LiftResult {Head : Type} {rules : Rules Head}
    {retained : RetainedRoot.{uEvidence} rules}
    {context : FormedContext rules} {fibre : TypeOver context}
    (source : Term context fibre) (targetCode : Tm Head context.arity) where
  targetTyped : HasType rules context.context targetCode fibre.code
  conversion : ConversionEvidence (termComputation retained context)
    source (⟨targetCode, targetTyped⟩ : Term context fibre)

/-- Both typed directions induced by one raw conversion.  Constructing the
two directions together makes symmetry structural: a symmetric raw path
exchanges the fields, rather than invoking a hidden expansion principle. -/
structure LiftDirections {Head : Type} {rules : Rules Head}
    {retained : RetainedRoot.{uEvidence} rules}
    {context : FormedContext rules} {fibre : TypeOver context}
    (sourceCode targetCode : Tm Head context.arity) where
  forward : ∀ sourceTyped :
      HasType rules context.context sourceCode fibre.code,
    LiftResult (retained := retained)
      (⟨sourceCode, sourceTyped⟩ : Term context fibre) targetCode
  backward : ∀ targetTyped :
      HasType rules context.context targetCode fibre.code,
    LiftResult (retained := retained)
      (⟨targetCode, targetTyped⟩ : Term context fibre) sourceCode

/-- A complete raw conversion induces both intrinsically typed directions
when every primitive step preserves and expands the selected judgment
fibre. -/
noncomputable def liftDirections
    {Head : Type} {rules : Rules Head}
    {retained : RetainedRoot.{uEvidence} rules}
    {context : FormedContext rules} {fibre : TypeOver context}
    (typing : BidirectionalStepTyping retained context fibre)
    {source target : Tm Head context.arity}
    (conversion : StructuralConversionReceipt retained.computation
      rules.headEq source target) :
    LiftDirections (retained := retained) (fibre := fibre) source target := by
  change ConversionEvidence
    (rawStructuralComputation retained.computation rules.headEq context.arity)
      source target at conversion
  refine ConversionEvidence.recOn
    (motive := fun source target _ =>
      LiftDirections (retained := retained) (fibre := fibre) source target)
    conversion ?_ ?_ ?_ ?_
  · intro source target receipt
    exact
      { forward := fun sourceTyped =>
          let targetTyped := typing.forward receipt sourceTyped
          { targetTyped := targetTyped
            conversion := ConversionEvidence.step
              (computation := termComputation retained context) receipt }
        backward := fun targetTyped =>
          let sourceTyped := typing.backward receipt targetTyped
          { targetTyped := sourceTyped
            conversion := ConversionEvidence.symm
              (ConversionEvidence.step
                (computation := termComputation retained context) receipt) } }
  · intro state
    exact
      { forward := fun stateTyped =>
          { targetTyped := stateTyped
            conversion := ConversionEvidence.refl
              (computation := termComputation retained context)
              (⟨state, stateTyped⟩ : Term context fibre) }
        backward := fun stateTyped =>
          { targetTyped := stateTyped
            conversion := ConversionEvidence.refl
              (computation := termComputation retained context)
              (⟨state, stateTyped⟩ : Term context fibre) } }
  · intro source target nested inductionHypothesis
    exact
      { forward := inductionHypothesis.backward
        backward := inductionHypothesis.forward }
  · intro source middle target first second firstInduction secondInduction
    exact
      { forward := fun sourceTyped =>
          let middleLift := firstInduction.forward sourceTyped
          let targetLift := secondInduction.forward middleLift.targetTyped
          { targetTyped := targetLift.targetTyped
            conversion := ConversionEvidence.trans
              middleLift.conversion targetLift.conversion }
        backward := fun targetTyped =>
          let middleLift := secondInduction.backward targetTyped
          let sourceLift := firstInduction.backward middleLift.targetTyped
          { targetTyped := sourceLift.targetTyped
            conversion := ConversionEvidence.trans
              middleLift.conversion sourceLift.conversion } }

/-- Lift a complete raw conversion in its authored direction, constructing
the target typing derivation and retaining every primitive receipt in the
intrinsic judgment fibre. Symmetric subpaths are oriented toward the requested
endpoint, so their composition tree may be normalized. -/
noncomputable def liftForward
    {Head : Type} {rules : Rules Head}
    {retained : RetainedRoot.{uEvidence} rules}
    {context : FormedContext rules} {fibre : TypeOver context}
    (typing : BidirectionalStepTyping retained context fibre)
    {source target : Tm Head context.arity}
    (conversion : StructuralConversionReceipt retained.computation
      rules.headEq source target)
    (sourceTyped : HasType rules context.context source fibre.code) :
    LiftResult (retained := retained)
      (⟨source, sourceTyped⟩ : Term context fibre) target :=
  (liftDirections (fibre := fibre) typing conversion).forward sourceTyped

/-- Lift a raw conversion in the reverse direction. Primitive steps use
`backward`; transitive paths are traversed in reverse order. -/
noncomputable def liftBackward
    {Head : Type} {rules : Rules Head}
    {retained : RetainedRoot.{uEvidence} rules}
    {context : FormedContext rules} {fibre : TypeOver context}
    (typing : BidirectionalStepTyping retained context fibre)
    {source target : Tm Head context.arity}
    (conversion : StructuralConversionReceipt retained.computation
      rules.headEq source target)
    (targetTyped : HasType rules context.context target fibre.code) :
    LiftResult (retained := retained)
      (⟨target, targetTyped⟩ : Term context fibre) source :=
  (liftDirections (fibre := fibre) typing conversion).backward targetTyped

/-- Under explicit forward preservation and backward expansion, every raw
formed-endpoint conversion lifts to a conversion whose intermediates are all
intrinsically typed. -/
noncomputable def liftStructural
    {Head : Type} {rules : Rules Head}
    {retained : RetainedRoot.{uEvidence} rules}
    {context : FormedContext rules}
    {display : DisplayedUniverse context}
    (typing : BidirectionalStepTyping retained context display.type)
    {source target : DisplayedType display}
    (conversion : StructuralConversionReceipt retained.computation
      rules.headEq source.code target.code) :
    TypedTypeConversion retained display source target := by
  let lifted := liftForward typing conversion source.typed
  have targetEquality :
      (⟨target.code, lifted.targetTyped⟩ : Term context display.type) = target :=
    Term.ext rfl
  exact targetEquality ▸ lifted.conversion

/-! ## Path-local reversible admission -/

/-- A raw conversion annotated exactly where each primitive step is
reversible in one typing fibre.  Unlike `BidirectionalStepTyping`, this does
not quantify over an evaluator's other steps.  It is therefore the suitable
boundary certificate for admitting one raw conversion into the intrinsic
typed language. -/
inductive PathTyping {Head : Type} {rules : Rules Head}
    (retained : RetainedRoot.{uEvidence} rules)
    (context : FormedContext rules) (fibre : TypeOver context) :
    {source target : Tm Head context.arity} →
      StructuralConversionReceipt retained.computation rules.headEq
        source target → Type (max uEvidence 0) where
  | step {source target : Tm Head context.arity}
      (receipt : StructuralStepReceipt retained.computation rules.headEq
        source target)
      (forward : HasType rules context.context source fibre.code →
        HasType rules context.context target fibre.code)
      (backward : HasType rules context.context target fibre.code →
        HasType rules context.context source fibre.code) :
      PathTyping retained context fibre (.step receipt)
  | refl (state : Tm Head context.arity) :
      PathTyping retained context fibre
        (ConversionEvidence.refl
          (computation := rawStructuralComputation retained.computation
            rules.headEq context.arity) state)
  | symm {source target : Tm Head context.arity}
      {conversion : StructuralConversionReceipt retained.computation
        rules.headEq source target} :
      PathTyping retained context fibre conversion →
      PathTyping retained context fibre (.symm conversion)
  | trans {source middle target : Tm Head context.arity}
      {first : StructuralConversionReceipt retained.computation
        rules.headEq source middle}
      {second : StructuralConversionReceipt retained.computation
        rules.headEq middle target} :
      PathTyping retained context fibre first →
      PathTyping retained context fibre second →
      PathTyping retained context fibre (.trans first second)

namespace PathTyping

/-- A path-local reversibility certificate constructs both intrinsic typed
directions while retaining every primitive receipt. Reversing a path also
reverses its composition order, so the oriented tree may be normalized. -/
noncomputable def toLiftDirections
    {Head : Type} {rules : Rules Head}
    {retained : RetainedRoot.{uEvidence} rules}
    {context : FormedContext rules} {fibre : TypeOver context}
    {source target : Tm Head context.arity}
    {conversion : StructuralConversionReceipt retained.computation
      rules.headEq source target} :
    PathTyping retained context fibre conversion →
      LiftDirections (retained := retained) (fibre := fibre) source target
  | .step receipt forward backward =>
      { forward := fun sourceTyped =>
          let targetTyped := forward sourceTyped
          { targetTyped := targetTyped
            conversion := ConversionEvidence.step
              (computation := termComputation retained context) receipt }
        backward := fun targetTyped =>
          let sourceTyped := backward targetTyped
          { targetTyped := sourceTyped
            conversion := ConversionEvidence.symm
              (ConversionEvidence.step
                (computation := termComputation retained context) receipt) } }
  | .refl state =>
      { forward := fun stateTyped =>
          { targetTyped := stateTyped
            conversion := ConversionEvidence.refl
              (computation := termComputation retained context)
              (⟨state, stateTyped⟩ : Term context fibre) }
        backward := fun stateTyped =>
          { targetTyped := stateTyped
            conversion := ConversionEvidence.refl
              (computation := termComputation retained context)
              (⟨state, stateTyped⟩ : Term context fibre) } }
  | .symm nested =>
      let inner := toLiftDirections nested
      { forward := inner.backward
        backward := inner.forward }
  | .trans first second =>
      let firstLift := toLiftDirections first
      let secondLift := toLiftDirections second
      { forward := fun sourceTyped =>
          let middleLift := firstLift.forward sourceTyped
          let targetLift := secondLift.forward middleLift.targetTyped
          { targetTyped := targetLift.targetTyped
            conversion := ConversionEvidence.trans
              middleLift.conversion targetLift.conversion }
        backward := fun targetTyped =>
          let middleLift := secondLift.backward targetTyped
          let sourceLift := firstLift.backward middleLift.targetTyped
          { targetTyped := sourceLift.targetTyped
            conversion := ConversionEvidence.trans
              middleLift.conversion sourceLift.conversion } }

/-- Path-local admission preserves the exact normalized chronology and
orientation of every primitive receipt.  The backward direction is the
oriented reverse of the same trace; it does not invent a second receipt. -/
theorem toLiftDirections_trace
    {Head : Type} {rules : Rules Head}
    {retained : RetainedRoot.{uEvidence} rules}
    {context : FormedContext rules} {fibre : TypeOver context}
    {source target : Tm Head context.arity}
    {conversion : StructuralConversionReceipt retained.computation
      rules.headEq source target}
    (certificate : PathTyping retained context fibre conversion) :
    (∀ sourceTyped :
        HasType rules context.context source fibre.code,
      StructuralReceiptTrace.ofTyped
          (certificate.toLiftDirections.forward sourceTyped).conversion =
        StructuralReceiptTrace.ofRaw conversion) ∧
    (∀ targetTyped :
        HasType rules context.context target fibre.code,
      StructuralReceiptTrace.ofTyped
          (certificate.toLiftDirections.backward targetTyped).conversion =
        StructuralReceiptTrace.reverse
          (StructuralReceiptTrace.ofRaw conversion)) := by
  induction certificate with
  | step receipt forward backward =>
      constructor <;> intro _typing <;> rfl
  | refl state =>
      constructor <;> intro _typing <;> rfl
  | symm nested inductionHypothesis =>
      constructor
      · intro targetTyped
        simpa only [toLiftDirections, StructuralReceiptTrace.ofRaw] using
          inductionHypothesis.2 targetTyped
      · intro sourceTyped
        simpa only [toLiftDirections, StructuralReceiptTrace.ofRaw,
          StructuralReceiptTrace.reverse_reverse] using
          inductionHypothesis.1 sourceTyped
  | trans first second firstInduction secondInduction =>
      constructor
      · intro sourceTyped
        simp only [toLiftDirections, StructuralReceiptTrace.ofTyped,
          StructuralReceiptTrace.ofRaw]
        rw [firstInduction.1 sourceTyped]
        rw [secondInduction.1]
      · intro targetTyped
        simp only [toLiftDirections, StructuralReceiptTrace.ofTyped,
          StructuralReceiptTrace.ofRaw]
        rw [secondInduction.2 targetTyped]
        rw [firstInduction.2]
        exact (StructuralReceiptTrace.reverse_append _ _).symm

/-- Admit one path-local reversible raw conversion into the intrinsic typed
conversion language.  No property of unrelated evaluator steps is needed. -/
noncomputable def liftCertified
    {Head : Type} {rules : Rules Head}
    {retained : RetainedRoot.{uEvidence} rules}
    {context : FormedContext rules}
    {display : DisplayedUniverse context}
    {source target : DisplayedType display}
    {conversion : StructuralConversionReceipt retained.computation
      rules.headEq source.code target.code}
    (certificate : PathTyping retained context display.type conversion) :
    TypedTypeConversion retained display source target := by
  let lifted := certificate.toLiftDirections.forward source.typed
  have targetEquality :
      (⟨target.code, lifted.targetTyped⟩ : Term context display.type) = target :=
    Term.ext rfl
  exact targetEquality ▸ lifted.conversion

/-- The admitted typed conversion has exactly the normalized oriented
primitive trace of the certified raw path. -/
theorem liftCertified_trace
    {Head : Type} {rules : Rules Head}
    {retained : RetainedRoot.{uEvidence} rules}
    {context : FormedContext rules}
    {display : DisplayedUniverse context}
    {source target : DisplayedType display}
    {conversion : StructuralConversionReceipt retained.computation
      rules.headEq source.code target.code}
    (certificate : PathTyping retained context display.type conversion) :
    StructuralReceiptTrace.ofTyped (liftCertified certificate) =
      StructuralReceiptTrace.ofRaw conversion := by
  unfold liftCertified
  exact certificate.toLiftDirections_trace.1 source.typed

end PathTyping

end BidirectionalStepTyping

/-! ## Tower controls -/

namespace TowerExamples

open SyntacticContextual.TowerExamples

private abbrev levelOne : LevelExpr := .succ Tower.zero
private abbrev levelTwo : LevelExpr := .succ levelOne
private abbrev retainedTower :=
  SyntacticJudgmentalPi.TowerExamples.retainedTower

/-- The Tower universe U1 displayed as a type in U2. -/
def universeOneDisplay : DisplayedUniverse empty where
  level := .sort levelOne
  upper := .sort levelTwo
  levelIsUniverse := .sort levelOne
  upperIsUniverse := .sort levelTwo
  formation := .sort levelOne

/-- The displayed universe is exactly the existing formed U1 type. -/
theorem universeOneDisplay_type :
    universeOneDisplay.type = universeOne := by
  rfl

/-- The beta source of the native identity function, now regarded as a type
displayed in U1. -/
def betaSource : DisplayedType universeOneDisplay :=
  SyntacticJudgmentalPi.TowerExamples.identityApplication

/-- The corresponding beta target, retained as another displayed type. -/
def betaTarget : DisplayedType universeOneDisplay :=
  SyntacticJudgmentalPi.TowerExamples.identityBetaTarget

/-- Pi beta is a fully typed conversion of types: all conversion
intermediates remain terms of U1. -/
def betaTypedConversion :
    TypedTypeConversion
      SyntacticJudgmentalPi.TowerExamples.retainedTower
      universeOneDisplay betaSource betaTarget := by
  exact
    SyntacticJudgmentalPi.TowerExamples.identityBetaConversion

/-- Forgetting the fully typed beta conversion recovers a formed-endpoint
conversion without claiming that all raw conversions admit such a lift. -/
def betaEndpointConversion :
    TypeConversion SyntacticJudgmentalPi.TowerExamples.retainedTower
      betaSource.toTypeOver betaTarget.toTypeOver :=
  betaTypedConversion.toEndpointConversion

/-- The same beta step admitted from its raw receipt using only local
reversibility at the displayed U1 fibre. -/
def betaPathTyping :
    BidirectionalStepTyping.PathTyping retainedTower empty universeOne
      betaTypedConversion.toStructural :=
  .step
    (SyntacticJudgmentalPi.TowerExamples.identityProduct.betaReceipt
      retainedTower SyntacticJudgmentalPi.TowerExamples.identityBody
      universeZero)
    (fun _sourceTyping => betaTarget.typed)
    (fun _targetTyping => betaSource.typed)

/-- Positive boundary control: a locally certified raw path reconstructs an
intrinsic typed conversion without requiring evaluator-wide subject
expansion. -/
noncomputable def betaLiftedFromRaw :
    TypedTypeConversion retainedTower universeOneDisplay betaSource betaTarget :=
  BidirectionalStepTyping.PathTyping.liftCertified betaPathTyping

/-- The concrete boundary admission retains exactly the authored beta
receipt as one forward primitive event. -/
theorem betaLiftedFromRaw_trace :
    StructuralReceiptTrace.ofTyped betaLiftedFromRaw =
      [OrientedStructuralReceipt.forward
        (StructuralStepReceipt.betaPi
          (computation := retainedTower.computation)
          (headEq := Tower.rules.headEq)
          SyntacticJudgmentalPi.TowerExamples.identityBody.code
          universeZero.code)] := by
  unfold betaLiftedFromRaw
  rw [BidirectionalStepTyping.PathTyping.liftCertified_trace]
  rfl

/-- The typed conversion is nontrivial: its displayed endpoint codes are not
equal in the host theory. -/
theorem betaTypedConversion_endpoints_ne :
    betaSource.code ≠ betaTarget.code := by
  simpa only [betaSource, betaTarget, Term.cast_code] using
    SyntacticJudgmentalPi.TowerExamples.identityApplication_code_ne_target

/-- U2 is a distinct judgment fibre from U1. -/
theorem universeOne_ne_universeTwo :
    universeOne ≠ SyntacticJudgmentalPi.TowerExamples.universeTwo :=
  SyntacticJudgmentalPi.TowerExamples.universeOne_ne_universeTwo

/-- Negative control: proof-relevant conversion cannot cross from the U1
term fibre to the U2 term fibre without first carrying equality of the
formed universe indices. -/
theorem noConversionAcrossUniverseFibres :
    IsEmpty
      (TotalConversion
        (termComputation
          SyntacticJudgmentalPi.TowerExamples.retainedTower empty)
        ⟨universeOne, universeZero⟩
        ⟨SyntacticJudgmentalPi.TowerExamples.universeTwo,
          SyntacticJudgmentalPi.TowerExamples.universeOneTerm⟩) := by
  exact noTotalConversionOfIndexNe
    (computation :=
      termComputation
        SyntacticJudgmentalPi.TowerExamples.retainedTower empty)
    universeOne_ne_universeTwo

/-! ## Why raw conversion has no unconditional typed lift -/

/-- A deliberately absent declaration used as an ill-typed beta argument. -/
def missingArgumentName : DeclName := `Prime.TypedConversion.MissingArgument

/-- The absent constant as a closed raw term. -/
def missingArgument : Tm Tower.Head empty.arity := .const missingArgumentName

/-- A beta redex whose body ignores its argument.  Raw computation can erase
the absent constant even though the application has no typing derivation. -/
def illTypedBetaSource : Tm Tower.Head empty.arity :=
  .app (.lam (rename wk universeZero.code)) missingArgument

/-- The structural beta receipt exists independently of typing. -/
def illTypedBetaStep :
    StructuralStepReceipt retainedTower.computation Tower.rules.headEq
      illTypedBetaSource universeZero.code := by
  simpa only [illTypedBetaSource, missingArgument, inst0_rename_wk] using
    (StructuralStepReceipt.betaPi
      (computation := retainedTower.computation)
      (headEq := Tower.rules.headEq)
      (rename wk universeZero.code) missingArgument)

/-- The redex is not typable at U1: application generation would require a
typing derivation for the deliberately undeclared argument. -/
theorem illTypedBetaSource_not_typed :
    ¬ HasType Tower.rules empty.context illTypedBetaSource universeOne.code := by
  intro sourceTyping
  rcases sourceTyping.appGeneration with
    ⟨_domain, _codomain, _functionTyping, argumentTyping, _adjustment⟩
  exact argumentTyping.constantImpossibleWhenMissing rfl

/-- Negative control: raw structural computation cannot globally provide
subject expansion in a formed type fibre.  Consequently the conditional
lifting interface above must be instantiated only by a genuinely reversible
typed rule fragment; it is not an evaluator-wide law. -/
theorem noGlobalBidirectionalStepTyping :
    IsEmpty
      (BidirectionalStepTyping retainedTower empty universeOne) := by
  constructor
  intro typing
  exact illTypedBetaSource_not_typed
    (typing.backward illTypedBetaStep universeZero.typed)

end TowerExamples

/-! ## Axiom audit -/

#print axioms DisplayedUniverse.type
#print axioms DisplayedUniverse.type_reindex
#print axioms DisplayedType.toTypeOver
#print axioms DisplayedType.reindex
#print axioms TypedTypeConversion.toStructural
#print axioms TypedTypeConversion.toEndpointConversion
#print axioms TypedTypeConversion.reindex
#print axioms TypedTypeConversion.toStructural_reindex
#print axioms OrientedStructuralReceipt.reverse_reverse
#print axioms StructuralReceiptTrace.reverse_reverse
#print axioms StructuralReceiptTrace.ofTyped_eq_ofRaw_toStructural
#print axioms BidirectionalStepTyping.liftDirections
#print axioms BidirectionalStepTyping.liftForward
#print axioms BidirectionalStepTyping.liftBackward
#print axioms BidirectionalStepTyping.liftStructural
#print axioms BidirectionalStepTyping.PathTyping.toLiftDirections
#print axioms BidirectionalStepTyping.PathTyping.toLiftDirections_trace
#print axioms BidirectionalStepTyping.PathTyping.liftCertified
#print axioms BidirectionalStepTyping.PathTyping.liftCertified_trace
#print axioms TowerExamples.betaTypedConversion
#print axioms TowerExamples.betaPathTyping
#print axioms TowerExamples.betaLiftedFromRaw
#print axioms TowerExamples.betaLiftedFromRaw_trace
#print axioms TowerExamples.betaTypedConversion_endpoints_ne
#print axioms TowerExamples.noConversionAcrossUniverseFibres
#print axioms TowerExamples.illTypedBetaStep
#print axioms TowerExamples.illTypedBetaSource_not_typed
#print axioms TowerExamples.noGlobalBidirectionalStepTyping

end SyntacticTypedConversion
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
