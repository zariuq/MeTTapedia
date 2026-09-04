import Mathlib.Tactic

/-!
# Semantic separation and constructor faithfulness for conversion

An interpretation of a conversion relation can serve two distinct purposes.

* Soundness plus semantic disjointness rules out conversion between two
  constructor families.
* Recovering conversion of constructor arguments additionally requires both
  faithfulness of the interpreted constructor and reflection of semantic
  equality back into conversion.

The second requirement is easy to hide when an argument is described only as
"a model proves constructor injectivity".  This module records the complete
property bag.  It is independent of any particular syntax, reduction system,
normalizer, domain construction, or type theory.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Conversion

universe uι ut us

/-- A sound interpretation of an indexed conversion relation. -/
structure SoundInterpretation
    {Index : Type uι} (Term : Index → Type ut)
    (Conversion : (index : Index) → Term index → Term index → Prop)
    (Meaning : Index → Type us) where
  denote : {index : Index} → Term index → Meaning index
  sound : ∀ {index : Index} {left right : Term index},
    Conversion index left right → denote left = denote right

/-- Semantic equality is complete for the interpreted conversion relation. -/
def ReflectsEquality
    {Index : Type uι} {Term : Index → Type ut}
    {Conversion : (index : Index) → Term index → Term index → Prop}
    {Meaning : Index → Type us}
    (interpretation : SoundInterpretation Term Conversion Meaning) : Prop :=
  ∀ {index : Index} {left right : Term index},
    interpretation.denote left = interpretation.denote right →
      Conversion index left right

/-- Two syntactic families are separated by their semantic images. -/
def SemanticallyDisjoint
    {Index : Type uι} {Term : Index → Type ut}
    {Conversion : (index : Index) → Term index → Term index → Prop}
    {Meaning : Index → Type us}
    (interpretation : SoundInterpretation Term Conversion Meaning)
    {index : Index} {Left : Type*} {Right : Type*}
    (leftFamily : Left → Term index) (rightFamily : Right → Term index) : Prop :=
  ∀ left right,
    interpretation.denote (leftFamily left) ≠
      interpretation.denote (rightFamily right)

/-- Soundness and semantic separation suffice to refute conversion.  No
reflection or normalization theorem is needed for this direction. -/
theorem not_conversion_of_semanticallyDisjoint
    {Index : Type uι} {Term : Index → Type ut}
    {Conversion : (index : Index) → Term index → Term index → Prop}
    {Meaning : Index → Type us}
    (interpretation : SoundInterpretation Term Conversion Meaning)
    {index : Index} {Left : Type*} {Right : Type*}
    {leftFamily : Left → Term index} {rightFamily : Right → Term index}
    (disjoint : SemanticallyDisjoint interpretation leftFamily rightFamily)
    (left : Left) (right : Right) :
    ¬ Conversion index (leftFamily left) (rightFamily right) := by
  intro conversion
  exact disjoint left right (interpretation.sound conversion)

/-- The semantic image of a binary constructor determines the semantic images
of both arguments.  The two argument indices may differ, as for a dependent
function constructor whose codomain lives in an extended context. -/
structure BinaryConstructorFaithful
    {Index : Type uι} {Term : Index → Type ut}
    {Conversion : (index : Index) → Term index → Term index → Prop}
    {Meaning : Index → Type us}
    (interpretation : SoundInterpretation Term Conversion Meaning)
    {leftIndex rightIndex resultIndex : Index}
    (constructor : Term leftIndex → Term rightIndex → Term resultIndex) : Prop where
  left : ∀ {left right left' right'},
    interpretation.denote (constructor left right) =
        interpretation.denote (constructor left' right') →
      interpretation.denote left = interpretation.denote left'
  right : ∀ {left right left' right'},
    interpretation.denote (constructor left right) =
        interpretation.denote (constructor left' right') →
      interpretation.denote right = interpretation.denote right'

/-- A faithful constructor yields semantic equality of its components from a
conversion of constructed terms. -/
theorem semanticComponents_of_conversion
    {Index : Type uι} {Term : Index → Type ut}
    {Conversion : (index : Index) → Term index → Term index → Prop}
    {Meaning : Index → Type us}
    (interpretation : SoundInterpretation Term Conversion Meaning)
    {leftIndex rightIndex resultIndex : Index}
    {constructor : Term leftIndex → Term rightIndex → Term resultIndex}
    (faithful : BinaryConstructorFaithful interpretation constructor)
    {left right left' right'}
    (conversion : Conversion resultIndex
      (constructor left right) (constructor left' right')) :
    interpretation.denote left = interpretation.denote left' ∧
      interpretation.denote right = interpretation.denote right' := by
  have equality := interpretation.sound conversion
  exact ⟨faithful.left equality, faithful.right equality⟩

/-- To recover syntactic conversion of constructor arguments, semantic
constructor faithfulness must be paired with equality reflection. -/
theorem conversionComponents_of_faithfulInterpretation
    {Index : Type uι} {Term : Index → Type ut}
    {Conversion : (index : Index) → Term index → Term index → Prop}
    {Meaning : Index → Type us}
    (interpretation : SoundInterpretation Term Conversion Meaning)
    (reflects : ReflectsEquality interpretation)
    {leftIndex rightIndex resultIndex : Index}
    {constructor : Term leftIndex → Term rightIndex → Term resultIndex}
    (faithful : BinaryConstructorFaithful interpretation constructor)
    {left right left' right'}
    (conversion : Conversion resultIndex
      (constructor left right) (constructor left' right')) :
    Conversion leftIndex left left' ∧ Conversion rightIndex right right' := by
  rcases semanticComponents_of_conversion interpretation faithful conversion with
    ⟨leftEquality, rightEquality⟩
  exact ⟨reflects leftEquality, reflects rightEquality⟩

/-! ## Positive control: a distinct semantic copy of a small term algebra -/

namespace Controls

inductive DemoTerm where
  | atom : Nat → DemoTerm
  | pair : DemoTerm → DemoTerm → DemoTerm
  | head : Nat → DemoTerm
  deriving DecidableEq

inductive DemoMeaning where
  | atom : Nat → DemoMeaning
  | pair : DemoMeaning → DemoMeaning → DemoMeaning
  | head : Nat → DemoMeaning
  deriving DecidableEq

def demoDenote : DemoTerm → DemoMeaning
  | .atom value => .atom value
  | .pair left right => .pair (demoDenote left) (demoDenote right)
  | .head value => .head value

theorem demoDenote_injective : Function.Injective demoDenote := by
  intro left
  induction left with
  | atom value =>
      intro right equality
      cases right <;> simp_all [demoDenote]
  | pair left right leftHypothesis rightHypothesis =>
      intro other equality
      cases other with
      | atom value => simp_all [demoDenote]
      | pair otherLeft otherRight =>
          simp only [demoDenote, DemoMeaning.pair.injEq] at equality
          exact congrArg₂ DemoTerm.pair
            (leftHypothesis equality.1) (rightHypothesis equality.2)
      | head value => simp_all [demoDenote]
  | head value =>
      intro right equality
      cases right <;> simp_all [demoDenote]

abbrev DemoFamily (_index : Unit) := DemoTerm

def DemoConversion (_index : Unit) : DemoTerm → DemoTerm → Prop := Eq

abbrev DemoSemanticFamily (_index : Unit) := DemoMeaning

def demoInterpretation :
    SoundInterpretation DemoFamily DemoConversion DemoSemanticFamily where
  denote := demoDenote
  sound conversion := congrArg demoDenote conversion

theorem demo_reflectsEquality : ReflectsEquality demoInterpretation :=
  fun equality => demoDenote_injective equality

theorem demo_pair_faithful :
    BinaryConstructorFaithful
      (leftIndex := ()) (rightIndex := ()) (resultIndex := ())
      demoInterpretation DemoTerm.pair := by
  constructor
  · intro left right left' right' equality
    change DemoMeaning.pair (demoDenote left) (demoDenote right) =
      DemoMeaning.pair (demoDenote left') (demoDenote right') at equality
    exact (DemoMeaning.pair.inj equality).1
  · intro left right left' right' equality
    change DemoMeaning.pair (demoDenote left) (demoDenote right) =
      DemoMeaning.pair (demoDenote left') (demoDenote right') at equality
    exact (DemoMeaning.pair.inj equality).2

theorem demo_pair_head_disjoint :
    SemanticallyDisjoint (index := ()) demoInterpretation
      (fun pair : DemoTerm × DemoTerm => DemoTerm.pair pair.1 pair.2)
      DemoTerm.head := by
  intro pair value equality
  cases equality

/-- Positive component control through the full semantic property bag. -/
theorem demo_pair_conversion_components
    {left right left' right' : DemoTerm}
    (conversion : DemoConversion ()
      (.pair left right) (.pair left' right')) :
    DemoConversion () left left' ∧ DemoConversion () right right' :=
  conversionComponents_of_faithfulInterpretation
    demoInterpretation demo_reflectsEquality demo_pair_faithful conversion

/-- Positive separation control: pair and head cannot convert. -/
theorem demo_pair_not_conversion_head (left right : DemoTerm) (value : Nat) :
    ¬ DemoConversion () (.pair left right) (.head value) :=
  not_conversion_of_semanticallyDisjoint demoInterpretation
    demo_pair_head_disjoint (left, right) value

/-! ## Negative control: soundness and constructor faithfulness are not enough -/

abbrev CollapsedFamily (_index : Unit) := Bool
abbrev CollapsedMeaning (_index : Unit) := Unit

def collapsedConversion (_index : Unit) : Bool → Bool → Prop := Eq

def collapsedInterpretation : SoundInterpretation
    CollapsedFamily collapsedConversion CollapsedMeaning where
  denote _ := ()
  sound _ := rfl

def collapsedConstructor (_left _right : Bool) : Bool := false

theorem collapsedConstructor_faithful :
    BinaryConstructorFaithful
      (leftIndex := ()) (rightIndex := ()) (resultIndex := ())
      collapsedInterpretation collapsedConstructor := by
  constructor <;> intros <;> rfl

/-- The constructed terms convert even when their left arguments do not. -/
theorem collapsed_conversion_without_component_conversion :
    collapsedConversion ()
        (collapsedConstructor false false)
        (collapsedConstructor true true) ∧
      ¬ collapsedConversion () false true := by
  exact ⟨rfl, Bool.noConfusion⟩

/-- Equality reflection fails in the collapsed interpretation.  This is the
missing hypothesis exposed by the preceding negative control. -/
theorem collapsedInterpretation_not_reflecting :
    ¬ ReflectsEquality collapsedInterpretation := by
  intro reflects
  have semanticEquality :
      collapsedInterpretation.denote (index := ()) false =
        collapsedInterpretation.denote (index := ()) true := rfl
  exact Bool.noConfusion
    (reflects (index := ()) (left := false) (right := true) semanticEquality)

end Controls

/-! ## Axiom audit -/

#print axioms not_conversion_of_semanticallyDisjoint
#print axioms semanticComponents_of_conversion
#print axioms conversionComponents_of_faithfulInterpretation
#print axioms Controls.demo_pair_conversion_components
#print axioms Controls.demo_pair_not_conversion_head
#print axioms Controls.collapsed_conversion_without_component_conversion
#print axioms Controls.collapsedInterpretation_not_reflecting

end Mettapedia.Logic.Conversion
