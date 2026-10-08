import Mettapedia.CategoryTheory.RelativeClosedSyntaxSoundness
import Mettapedia.CategoryTheory.RelativeClosedSyntaxPresentedEqualizers
import Mettapedia.CategoryTheory.RelativeClosedSyntaxClosed

/-!
# Local comparison declarations for the base closed category

The base category's chosen terminal, products, exponentials and equalizers
are compared with formal syntax by independently declared inverse arrows.
Two authored equations for each comparison give its two inverse diagrams.
Their actual earlier-stage typing trees are constructed here. Preservation
of the base structures is a consequence of these local diagrams, not a field
of a syntax interpretation or a generated-category construction.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.BaseComparisons

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory

universe u v

variable (C : Type u) [Category.{v} C]

inductive Choice : Type (max u v) where
  | terminal
  | product (first second : C)
  | equalizer {source target : C} (before after : source ⟶ target)
  | exponential (argument result : C)

def symbols : Symbols.{max u v} where
  ObjectName := ULift.{max u v} Empty
  ArrowName := Choice C
  EquationName := Choice C × Bool

variable {C}
variable [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C]

def selected : Choice C → C
  | .terminal => 𝟙_ C
  | .product first second => first ⊗ second
  | .equalizer before after => Limits.equalizer before after
  | .exponential argument result => argument ⟶[C] result

def sourceCode : Choice C → ObjectCode C (symbols C)
  | .terminal => .terminal
  | .product first second => .product (.base first) (.base second)
  | .equalizer (source := source) (target := target) before after =>
      .equalizer (.base source) (.base target) (.base before) (.base after)
  | .exponential argument result => .exponential (.base argument) (.base result)

def targetCode (choice : Choice C) : ObjectCode C (symbols C) := .base (selected choice)

def forwardCode : Choice C → ArrowCode C (symbols C)
  | .terminal => .terminal (.base (𝟙_ C))
  | .product first second =>
      .pair (.base (CartesianMonoidalCategory.fst first second))
        (.base (CartesianMonoidalCategory.snd first second))
  | .equalizer (source := source) (target := target) before after =>
      .equalizerLift (.base source) (.base target) (.base before) (.base after)
        (.base (Limits.equalizer before after)) (.base (equalizer.ι before after))
  | .exponential argument result =>
      .curry (.base (argument ⟶[C] result)) (.base argument) (.base result)
        (.compose (.name (.product (argument ⟶[C] result) argument))
          (.base (Interpretation.evaluation argument result)))

def equationObject (origin : Choice C × Bool) : ObjectCode C (symbols C) :=
  if origin.2 then sourceCode origin.1 else targetCode origin.1

def leftCode (origin : Choice C × Bool) : ArrowCode C (symbols C) :=
  if origin.2 then .compose (.name origin.1) (forwardCode origin.1)
    else .compose (forwardCode origin.1) (.name origin.1)

def rightCode (origin : Choice C × Bool) : ArrowCode C (symbols C) :=
  .identity (equationObject origin)

def signature : Signature (C := C) (symbols := symbols C) where
  objectRank _ := 0
  arrowRank _ := 1
  source := sourceCode
  target := targetCode
  source_before choice := by
    cases choice <;> simp only [sourceCode, ObjectCode.before, ArrowCode.before] <;> trivial
  target_before _ := trivial
  equationRank _ := 2
  equationSource := equationObject
  equationTarget := equationObject
  left := leftCode
  right := rightCode
  equation_before origin := by
    rcases origin with ⟨choice, side⟩
    cases choice <;> cases side <;>
      simp only [leftCode, rightCode, equationObject, sourceCode, targetCode, forwardCode,
        Bool.false_eq_true, ↓reduceIte, ObjectCode.before, ArrowCode.before] <;> decide

def sourceFormation (choice : Choice C) : Derivation (signature (C := C)) (.object (sourceCode choice)) :=
  match choice with
  | .terminal => .terminalObject
  | .product first second => .productObject (.baseObject first) (.baseObject second)
  | .equalizer (source := source) (target := target) before after =>
      .equalizerObject (.baseObject source) (.baseObject target) (.baseArrow before) (.baseArrow after)
  | .exponential argument result => .exponentialObject (.baseObject argument) (.baseObject result)

def targetFormation (choice : Choice C) : Derivation (signature (C := C)) (.object (targetCode choice)) :=
  .baseObject (selected choice)

def inverseTyped (choice : Choice C) : Derivation (signature (C := C))
    (.arrow (sourceCode choice) (targetCode choice) (.name choice)) :=
  .arrowName (signature := signature (C := C)) choice (sourceFormation choice) (targetFormation choice)

def baseEqualizerCondition {source target : C} (before after : source ⟶ target) :
    Derivation (signature (C := C))
      (.equation (.base (Limits.equalizer before after)) (.base target)
        (.compose (.base (equalizer.ι before after)) (.base before))
        (.compose (.base (equalizer.ι before after)) (.base after))) :=
  .transitivity (.symmetry (.baseComposition (equalizer.ι before after) before))
    (.transitivity (.baseEquality (equalizer.condition before after))
      (.baseComposition (equalizer.ι before after) after))

def forwardTyped (choice : Choice C) : Derivation (signature (C := C))
    (.arrow (targetCode choice) (sourceCode choice) (forwardCode choice)) :=
  match choice with
  | .terminal => .terminalArrow (.baseObject (𝟙_ C))
  | .product first second =>
      .pair (.baseArrow (CartesianMonoidalCategory.fst first second))
        (.baseArrow (CartesianMonoidalCategory.snd first second))
  | .equalizer (source := source) (target := target) before after =>
      .equalizerLift (.baseObject source) (.baseObject target)
        (.baseObject (Limits.equalizer before after)) (.baseArrow before) (.baseArrow after)
        (.baseArrow (equalizer.ι before after)) (baseEqualizerCondition before after)
  | .exponential argument result =>
      .curry (.baseObject (argument ⟶[C] result)) (.baseObject argument) (.baseObject result)
        (.compose (inverseTyped (.product (argument ⟶[C] result) argument))
          (.baseArrow (Interpretation.evaluation argument result)))

def equationFormation (origin : Choice C × Bool) :
    Derivation (signature (C := C)) (.object (equationObject origin)) :=
  match origin with
  | ⟨choice, false⟩ => targetFormation choice
  | ⟨choice, true⟩ => sourceFormation choice

def leftTyped (origin : Choice C × Bool) :
    Derivation (signature (C := C))
      (.arrow (equationObject origin) (equationObject origin) (leftCode origin)) :=
  match origin with
  | ⟨choice, false⟩ => .compose (forwardTyped choice) (inverseTyped choice)
  | ⟨choice, true⟩ => .compose (inverseTyped choice) (forwardTyped choice)

def rightTyped (origin : Choice C × Bool) :
    Derivation (signature (C := C))
      (.arrow (equationObject origin) (equationObject origin) (rightCode origin)) :=
  .identity (equationFormation origin)

def headers : HeaderFormation (signature (C := C)) where
  source := sourceFormation
  target := targetFormation
  left := leftTyped
  right := rightTyped

theorem sourceFormation_bounded (choice : Choice C) (stage : Nat) :
    (sourceFormation choice).bounded stage := by
  cases choice <;> simp only [sourceFormation, Derivation.bounded] <;> trivial

theorem targetFormation_bounded (choice : Choice C) (stage : Nat) :
    (targetFormation choice).bounded stage := trivial

theorem inverseTyped_bounded (choice : Choice C) {stage : Nat} (earlier : 1 < stage) :
    (inverseTyped choice).bounded stage := by
  change 1 < stage ∧ (sourceFormation choice).bounded stage ∧ (targetFormation choice).bounded stage
  exact ⟨earlier, sourceFormation_bounded choice stage, targetFormation_bounded choice stage⟩

theorem forwardTyped_bounded (choice : Choice C) {stage : Nat} (earlier : 1 < stage) :
    (forwardTyped choice).bounded stage := by
  cases choice with
  | terminal => trivial
  | product first second => trivial
  | equalizer before after =>
      change True ∧ True ∧ True ∧ True ∧ True ∧ True ∧
        (baseEqualizerCondition before after).bounded stage
      refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, ?_⟩
      trivial
  | exponential argument result =>
      exact ⟨trivial, trivial, trivial, inverseTyped_bounded _ earlier, trivial⟩

def orderedHeaders : OrderedHeaderFormation (signature (C := C)) where
  formation := headers
  source_before choice := sourceFormation_bounded choice 1
  target_before choice := targetFormation_bounded choice 1
  left_before origin := by
    rcases origin with ⟨choice, side⟩
    cases side
    · change (forwardTyped choice).bounded 2 ∧ (inverseTyped choice).bounded 2
      exact ⟨forwardTyped_bounded choice (by decide), inverseTyped_bounded choice (by decide)⟩
    · change (inverseTyped choice).bounded 2 ∧ (forwardTyped choice).bounded 2
      exact ⟨inverseTyped_bounded choice (by decide), forwardTyped_bounded choice (by decide)⟩
  right_before origin := by
    rcases origin with ⟨choice, side⟩
    cases side
    · exact targetFormation_bounded choice 2
    · exact sourceFormation_bounded choice 2

end Mettapedia.CategoryTheory.RelativeClosedSyntax.BaseComparisons
