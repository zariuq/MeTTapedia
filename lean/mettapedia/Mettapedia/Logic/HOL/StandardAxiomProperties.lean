import Mettapedia.Logic.HOL.CanonicalTheory
import Mettapedia.Logic.HOL.ClassicalExcludedMiddle
import Mettapedia.Logic.HOL.Semantics.ModelProperties
import Mettapedia.Logic.HOL.Soundness

/-!
# Property-explicit choice and infinity axioms for simple type theory

The name `HOL` covers several calculi and package disciplines.  This module
therefore states two commonly selected theorem axioms independently:

* a Hilbert-choice axiom at each selected simple type; and
* Dedekind infinity at one selected base type.

Function extensionality belongs to the derivation relation, excluded middle
is a separate logical schema, and constant/type-operator definitions are
separate conservative-extension mechanisms.  Type polymorphism here is
schematic: `choiceFormula` is indexed externally by a simple type.  No
object-level quantification over types is introduced.

The semantic theorems identify the exact model properties consumed by the
two formulas.  In particular, neither axiom is inferred from the syntax or
from extensionality alone.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.StandardAxiomProperties

open Mettapedia.Logic.HOL

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

/-! ## Hilbert choice -/

/-- The closed choice formula at `type`:

`exists choose, forall predicate, (exists x, predicate x) ->
  predicate (choose predicate)`.

The chosen function is quantified as an ordinary HOL value.  Consequently
the formula also entails inhabitance of the selected type. -/
def choiceFormula (type : Ty Base) : ClosedFormula Const :=
  let predicateType : Ty Base := type ⇒ .prop
  let chooserType : Ty Base := predicateType ⇒ type
  .ex
    (.all
      (.imp
        (.ex
          (.app
            (.var (.vs .vz) :
              Term Const [type, predicateType, chooserType] predicateType)
            (.var .vz)))
        (.app
          (.var .vz :
            Term Const [predicateType, chooserType] predicateType)
          (.app
            (.var (.vs .vz) :
              Term Const [predicateType, chooserType] chooserType)
            (.var .vz)))))

/-- The schematic family of choice formulas, one for each simple type. -/
def choiceTheory : ClosedTheorySet Const :=
  {formula | ∃ type : Ty Base, formula = choiceFormula type}

/-- A semantic Hilbert-choice family validates every choice formula. -/
theorem models_choiceFormula
    (M : HenkinModel.{u, v, w} Base Const)
    (choice : M.HilbertChoice) (type : Ty Base) :
    M.models (choiceFormula (Const := Const) type) := by
  change ∃ chooser, M.adm ((type ⇒ .prop) ⇒ type) chooser ∧
    ∀ predicate, M.adm (type ⇒ .prop) predicate →
      ((∃ value, M.adm type value ∧ (predicate value).down) →
        (predicate (chooser predicate)).down)
  exact ⟨choice.choose type, choice.choose_admissible type,
    choice.specified type⟩

/-- A model with semantic Hilbert choice validates the complete schematic
choice theory. -/
theorem models_choiceTheory
    (M : HenkinModel.{u, v, w} Base Const)
    (choice : M.HilbertChoice) :
    ∀ formula ∈ (choiceTheory : ClosedTheorySet Const), M.models formula := by
  intro formula membership
  rcases membership with ⟨type, rfl⟩
  exact models_choiceFormula M choice type

/-! ## Dedekind infinity -/

/-- Injectivity of the function bound in the one-variable context. -/
def injectiveBody (base : Base) :
    Formula Const [(.base base ⇒ .base base)] :=
  .all
    (.all
      (.imp
        (.eq
          (.app
            (.var (.vs (.vs .vz)) :
              Term Const
                [.base base, .base base, (.base base ⇒ .base base)]
                (.base base ⇒ .base base))
            (.var (.vs .vz)))
          (.app
            (.var (.vs (.vs .vz)) :
              Term Const
                [.base base, .base base, (.base base ⇒ .base base)]
                (.base base ⇒ .base base))
            (.var .vz)))
        (.eq (.var (.vs .vz)) (.var .vz))))

/-- Existence of a point omitted by the function bound in the one-variable
context. -/
def omittedPointBody (base : Base) :
    Formula Const [(.base base ⇒ .base base)] :=
  .ex
    (.all
      (.not
        (.eq
          (.app
            (.var (.vs (.vs .vz)) :
              Term Const
                [.base base, .base base, (.base base ⇒ .base base)]
                (.base base ⇒ .base base))
            (.var .vz))
          (.var (.vs .vz)))))

/-- Dedekind infinity of one selected base type: an injective self-map with
an omitted point exists. -/
def infinityFormula (base : Base) : ClosedFormula Const :=
  .ex (.and (injectiveBody (Const := Const) base)
    (omittedPointBody (Const := Const) base))

/-- The singleton theory containing the selected base-infinity formula. -/
def infinityTheory (base : Base) : ClosedTheorySet Const :=
  {formula | formula = infinityFormula base}

/-- A Dedekind-infinity witness validates the corresponding closed formula. -/
theorem models_infinityFormula
    (M : HenkinModel.{u, v, w} Base Const) (base : Base)
    (witness : M.DedekindInfinityWitness base) :
    M.models (infinityFormula (Const := Const) base) := by
  change ∃ successor, M.adm (.base base ⇒ .base base) successor ∧
    ((∀ left, M.adm (.base base) left →
      ∀ right, M.adm (.base base) right →
        successor left = successor right → left = right) ∧
      ∃ omitted, M.adm (.base base) omitted ∧
        ∀ value, M.adm (.base base) value →
          ¬ successor value = omitted)
  refine ⟨witness.successor, witness.successor_admissible, ?_,
    witness.omitted, witness.omitted_admissible, ?_⟩
  · intro left _leftAdmissible right _rightAdmissible equalImages
    exact witness.successor_injective equalImages
  · intro value _valueAdmissible
    exact witness.omitted_not_image value

/-- The closed infinity formula is semantically exact: a Henkin model
validates it precisely when the selected base carrier has a Dedekind-infinity
witness.  Base-type quantifiers range over the entire carrier, so no
full-domain hypothesis is needed here. -/
theorem models_infinityFormula_iff_hasWitness
    (M : HenkinModel.{u, v, w} Base Const) (base : Base) :
    M.models (infinityFormula (Const := Const) base) ↔
      M.HasDedekindInfiniteBase base := by
  constructor
  · rintro ⟨successor, successorAdmissible, injective,
      omitted, _omittedAdmissible, omittedNotImage⟩
    refine ⟨
      { successor := successor
        successor_admissible := successorAdmissible
        successor_injective := ?_
        omitted := omitted
        omitted_not_image := ?_ }⟩
    · intro left right equalImages
      exact injective left (M.base_mem base left) right
        (M.base_mem base right) equalImages
    · intro value
      exact omittedNotImage value (M.base_mem base value)
  · rintro ⟨witness⟩
    exact models_infinityFormula M base witness

/-- A model with the selected infinity witness validates its singleton
infinity theory. -/
theorem models_infinityTheory
    (M : HenkinModel.{u, v, w} Base Const) (base : Base)
    (witness : M.DedekindInfinityWitness base) :
    ∀ formula ∈ infinityTheory (Const := Const) base, M.models formula := by
  intro formula membership
  subst formula
  exact models_infinityFormula M base witness

/-! ## Theory closure and consistency -/

/-- The independent choice and selected-infinity axiom families combined by
ordinary theory union.  Function extensionality and excluded middle remain
outside this set. -/
def choiceInfinityTheory (base : Base) : ClosedTheorySet Const :=
  choiceTheory ∪ infinityTheory base

/-- Exact soundness of finite derivability from any model-validated closed
theory in the extensional calculus. -/
theorem provable_sound_of_models
    (M : HenkinModel.{u, v, w} Base Const)
    (extensional : M.FunctionsRespectEqv)
    (theory : ClosedTheorySet Const)
    (modelsTheory : ∀ formula ∈ theory, M.models formula)
    {conclusion : ClosedFormula Const}
    (derivation : ClosedTheorySet.Provable theory conclusion) :
    M.models conclusion := by
  rcases derivation with ⟨hypotheses, hypothesesInTheory, proof⟩
  exact Soundness.extDerivation_sound proof
    (M := M) (ρ := fun v => nomatch v)
    extensional
    (by intro type v; nomatch v)
    (by
      intro formula membership
      exact modelsTheory formula (hypothesesInTheory formula membership))

/-- The selected model-property bundle validates the union of choice and
infinity axioms. -/
theorem models_choiceInfinityTheory
    (M : HenkinModel.{u, v, w} Base Const) (base : Base)
    (properties : M.ExtensionalChoiceInfinity base) :
    ∀ formula ∈ choiceInfinityTheory (Const := Const) base,
      M.models formula := by
  intro formula membership
  rcases membership with choiceMembership | infinityMembership
  · exact models_choiceTheory M properties.choice formula choiceMembership
  · exact models_infinityTheory M base properties.infinity formula
      infinityMembership

/-- Model qualification separates the property-explicit choice/infinity
theory from falsity. -/
theorem choiceInfinityTheory_consistent
    (M : HenkinModel.{u, v, w} Base Const) (base : Base)
    (properties : M.ExtensionalChoiceInfinity base) :
    (choiceInfinityTheory (Const := Const) base).Consistent := by
  intro derivesBottom
  exact M.models_bot
    (provable_sound_of_models M properties.extensional
      (choiceInfinityTheory (Const := Const) base)
      (models_choiceInfinityTheory M base properties) derivesBottom)

/-! ## Adding classical logic without conflating the components -/

/-- Every Henkin model validates the excluded-middle schema used by the
classical theory extension.  Classicality enters here through the ambient
`Prop`-valued semantics; it is not a field of `HilbertChoice` or of an
infinity witness. -/
theorem models_excludedMiddleSchema
    (M : HenkinModel.{u, v, w} Base (WithParams Const)) :
    ∀ formula ∈ EMSchema Const, M.models formula := by
  let empty : M.Valuation ([] : Ctx Base) := fun {_type} v => nomatch v
  intro formula membership
  rcases membership with ⟨body, rfl⟩ | ⟨type, body, rfl⟩
  · change (M.denote body empty).down ∨ ¬(M.denote body empty).down
    exact Classical.em _
  · change ∀ value, M.adm type value →
      (M.denote (.or body (.not body))
        (M.extend empty value)).down
    intro value admissible
    exact M.validatesExcludedMiddle body
      (M.extend empty value)
      (M.extend_admissible (by intro otherType v; nomatch v) admissible)

/-- A property-explicit classical simple-type theory: excluded middle,
schematic Hilbert choice, and Dedekind infinity are combined only by set
union.  The extensional equality rules remain in `ExtDerivation`, and
definitions remain outside this axiom set. -/
def classicalChoiceInfinityTheory (base : Base) :
    ClosedTheorySet (WithParams Const) :=
  EMSchema Const ∪
    (choiceTheory ∪ infinityTheory base)

/-- The three independent semantic properties validate the corresponding
classical axiom union. -/
theorem models_classicalChoiceInfinityTheory
    (M : HenkinModel.{u, v, w} Base (WithParams Const)) (base : Base)
    (properties : M.ExtensionalChoiceInfinity base) :
    ∀ formula ∈
      classicalChoiceInfinityTheory (Const := Const) base,
        M.models formula := by
  intro formula membership
  rcases membership with excludedMiddleMembership | remainingMembership
  · exact models_excludedMiddleSchema M formula excludedMiddleMembership
  · rcases remainingMembership with choiceMembership | infinityMembership
    · exact models_choiceTheory M properties.choice formula choiceMembership
    · exact models_infinityTheory M base properties.infinity formula
        infinityMembership

/-- Any model carrying the three selected properties qualifies the
property-explicit classical theory as syntactically consistent. -/
theorem classicalChoiceInfinityTheory_consistent
    (M : HenkinModel.{u, v, w} Base (WithParams Const)) (base : Base)
    (properties : M.ExtensionalChoiceInfinity base) :
    (classicalChoiceInfinityTheory (Const := Const) base).Consistent := by
  intro derivesBottom
  exact M.models_bot
    (provable_sound_of_models M properties.extensional
      (classicalChoiceInfinityTheory (Const := Const) base)
      (models_classicalChoiceInfinityTheory M base properties) derivesBottom)

/-! ## Combined property class without a product-level logic name -/

/-- A model carrying the independent extensionality, choice, and infinity
properties validates both theorem-axiom families.  Extensionality is retained
as a separate conclusion because it is consumed by the equality calculus,
not by either formula above. -/
theorem extensionalChoiceInfinity_semantic_obligations
    (M : HenkinModel.{u, v, w} Base Const) (base : Base)
    (properties : M.ExtensionalChoiceInfinity base) :
    M.FunctionsRespectEqv ∧
      (∀ formula ∈ (choiceTheory : ClosedTheorySet Const), M.models formula) ∧
      (∀ formula ∈ infinityTheory (Const := Const) base,
        M.models formula) :=
  ⟨properties.extensional,
    models_choiceTheory M properties.choice,
    models_infinityTheory M base properties.infinity⟩

/-! ## Positive and negative controls -/

namespace Canary

open HenkinModel.ModelPropertyCanary

/-- Extensional full-domain semantics and formula-level excluded middle do
not force the choice axiom: the selected empty base type has no chooser. -/
theorem empty_model_refutes_base_choice_formula :
    ¬ emptyBaseModel.models
      (choiceFormula (Const := NoConstants Unit) (.base ())) := by
  intro validatesChoice
  change ∃ chooser,
      emptyBaseModel.adm
        (((.base () : Ty Unit) ⇒ .prop) ⇒ .base ()) chooser ∧
      ∀ predicate,
        emptyBaseModel.adm ((.base () : Ty Unit) ⇒ .prop) predicate →
          ((∃ value, emptyBaseModel.adm (.base ()) value ∧
              (predicate value).down) →
            (predicate (chooser predicate)).down) at validatesChoice
  rcases validatesChoice with ⟨chooser, _admissible, _specified⟩
  let predicate : LiftedEmpty → ULift Prop := fun _ => .up True
  have impossible : LiftedEmpty := chooser predicate
  exact nomatch impossible.down

/-- The natural-number base model validates both property-defined axiom
families and supplies extensional equality. -/
theorem natural_model_validates_standard_properties :
    naturalBaseModel.FunctionsRespectEqv ∧
      (∀ formula ∈
        (choiceTheory : ClosedTheorySet (NoConstants Unit)),
          naturalBaseModel.models formula) ∧
      (∀ formula ∈ infinityTheory
        (Const := NoConstants Unit) (), naturalBaseModel.models formula) :=
  extensionalChoiceInfinity_semantic_obligations naturalBaseModel ()
    naturalBaseModel_extensionalChoiceInfinity

/-- Choice does not force infinity: the finite Boolean base model validates
every choice formula but refutes the existence of a semantic infinity
witness. -/
theorem choice_without_infinity :
    (∀ formula ∈
      (choiceTheory : ClosedTheorySet (NoConstants Unit)),
        booleanBaseModel.models formula) ∧
      ¬ booleanBaseModel.HasDedekindInfiniteBase () :=
  ⟨models_choiceTheory booleanBaseModel booleanBaseModel_choice,
    booleanBaseModel_not_infinite⟩

/-- The finite Boolean model not only lacks an infinity witness; by semantic
exactness it refutes the selected infinity formula itself. -/
theorem boolean_model_refutes_infinity_formula :
    ¬ booleanBaseModel.models
      (infinityFormula (Const := NoConstants Unit) ()) := by
  rw [models_infinityFormula_iff_hasWitness]
  exact booleanBaseModel_not_infinite

end Canary

#print axioms models_choiceFormula
#print axioms models_choiceTheory
#print axioms models_infinityFormula
#print axioms models_infinityFormula_iff_hasWitness
#print axioms models_infinityTheory
#print axioms provable_sound_of_models
#print axioms models_choiceInfinityTheory
#print axioms choiceInfinityTheory_consistent
#print axioms models_excludedMiddleSchema
#print axioms models_classicalChoiceInfinityTheory
#print axioms classicalChoiceInfinityTheory_consistent
#print axioms extensionalChoiceInfinity_semantic_obligations
#print axioms Canary.natural_model_validates_standard_properties
#print axioms Canary.empty_model_refutes_base_choice_formula
#print axioms Canary.choice_without_infinity
#print axioms Canary.boolean_model_refutes_infinity_formula

end Mettapedia.Logic.HOL.StandardAxiomProperties
