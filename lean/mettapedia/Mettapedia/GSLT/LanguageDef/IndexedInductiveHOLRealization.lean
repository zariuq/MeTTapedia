import Mettapedia.GSLT.LanguageDef.IndexedInductiveHOLTerms
import Mettapedia.GSLT.LanguageDef.PositiveInductiveBlockBridge
import Mettapedia.Logic.HOL.IndexedContainerFieldGuards

/-!
# Primitive interpretations of admitted arithmetic-indexed constructors

The source natural carrier is the admitted Natural declaration. Its existing
representation and primitive arithmetic laws determine all index-expression
readings. Element membership remains a separate image predicate, so an empty
source sort never requires an equivalence with an inhabited HOL carrier.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.GSLT.LanguageDef.IndexedInductiveHOLRealization
open Mettapedia.Logic.HOL
open Mettapedia.TypeTheory
open IndexedPolynomial.Description IndexedContainerPositionTerms
open IndexedInductiveNatVec IndexedInductiveHOLTerms
universe u v w
variable {Base : Type u} {Const : Ty Base → Type v}
  (arithmetic : Arithmetic Const) (model : HenkinModel.{u,v,w} Base Const)

structure Numbers where
  equivalence : Nat ≃ Ty.denote model.Carrier arithmetic.number
  zero : Arithmetic.denotes model arithmetic.zero = equivalence 0
  successor : ∀ n, Arithmetic.denotes model arithmetic.successor (equivalence n) = equivalence (n+1)
  addition : ∀ n m, Arithmetic.denotes model arithmetic.addition (equivalence n) (equivalence m) = equivalence (n+m)

structure Elements (A : Type) where
  value : A → Ty.denote model.Carrier arithmetic.element
  predicate : ClosedTerm Const (arithmetic.element ⇒ .prop)
  image : ∀ target, (model.denote predicate (Arithmetic.emptyValuation model) target).down ↔
    ∃ source, value source = target

noncomputable section
variable (A : Type) (numbers : Numbers arithmetic model) (elements : Elements arithmetic model A)

abbrev registry := IndexedPositiveContainer.Unindexed.liftRegistry PositiveInductiveBlockBridge.Direct.registry (Vectors.interface A)

def ordered : (registry A).OrderedFinitary where
  containerOrdered := by
    intro name entry found
    simp only [registry, IndexedPositiveContainer.Unindexed.liftRegistry,
      PositiveInductiveBlockBridge.Direct.registry, Option.map_none] at found
    cases found

def reading : Reading (Vectors.interface A) (registry A) Const where
  indices := arithmetic.reading A
  number := arithmetic.number
  one := .app arithmetic.successor arithmetic.zero
  shapeType _ _ found := by
    simp only [registry, IndexedPositiveContainer.Unindexed.liftRegistry,
      PositiveInductiveBlockBridge.Direct.registry, Option.map_none] at found
    cases found
  count _ _ found _ := by
    simp only [registry, IndexedPositiveContainer.Unindexed.liftRegistry,
      PositiveInductiveBlockBridge.Direct.registry, Option.map_none] at found
    cases found

def naturalValues : Natural.Carrier ≃ Ty.denote model.Carrier arithmetic.number :=
  Natural.representation.trans numbers.equivalence

def values : ∀ sort, Vectors.value A sort → Ty.denote model.Carrier (arithmetic.sort sort)
  | .length => naturalValues arithmetic model numbers
  | .payload => elements.value

theorem values_eq : values arithmetic model A numbers elements =
    arithmetic.encodeData A model (naturalValues arithmetic model numbers) elements.value := by
  funext sort
  cases sort <;> rfl

theorem natural_zero : Arithmetic.denotes model arithmetic.zero =
    naturalValues arithmetic model numbers Natural.zero := numbers.zero

theorem natural_successor (source : Natural.Carrier) :
    Arithmetic.denotes model arithmetic.successor (naturalValues arithmetic model numbers source) =
      naturalValues arithmetic model numbers (Natural.succ source) :=
  numbers.successor (Natural.toNat source)

theorem natural_addition (first second : Natural.Carrier) :
    Arithmetic.denotes model arithmetic.addition (naturalValues arithmetic model numbers first)
      (naturalValues arithmetic model numbers second) =
        naturalValues arithmetic model numbers (Natural.add first second) := by
  change Arithmetic.denotes model arithmetic.addition (numbers.equivalence (Natural.toNat first))
    (numbers.equivalence (Natural.toNat second)) = numbers.equivalence (Natural.toNat (Natural.add first second))
  rw [Natural.toNat_add]
  exact numbers.addition _ _

private theorem closed_denote {type : Ty Base} (term : ClosedTerm Const type)
    (values : model.Valuation []) : model.denote term values = Arithmetic.denotes model term := by
  apply congrArg (model.denote term)
  funext type impossible
  exact nomatch impossible

def realization : IndexedContainerPositionTerms.Realization (reading arithmetic A) (ordered A) model where
  numbers := numbers.equivalence
  value := values arithmetic model A numbers elements
  index := naturalValues arithmetic model numbers
  shape _ _ found _ _ := by
    simp only [registry, IndexedPositiveContainer.Unindexed.liftRegistry,
      PositiveInductiveBlockBridge.Direct.registry, Option.map_none] at found
    cases found
  parameterValues := Arithmetic.emptyValuation model
  index_correct := by
    intro context expression environment
    change model.denote (arithmetic.term expression)
      ((arithmetic.reading A).valuation model (values arithmetic model A numbers elements)
        (Arithmetic.emptyValuation model) environment) =
      naturalValues arithmetic model numbers (expression.eval environment)
    rw [values_eq]
    exact arithmetic.term_denote A model (naturalValues arithmetic model numbers) elements.value
      (natural_zero arithmetic model numbers) (natural_successor arithmetic model numbers)
      (natural_addition arithmetic model numbers) expression environment
  one_correct := by
    intro valuation
    change model.denote arithmetic.successor valuation (model.denote arithmetic.zero valuation) = numbers.equivalence 1
    rw [closed_denote, closed_denote, numbers.zero]
    exact numbers.successor 0
  count_correct := by
    intro context name entry found
    simp only [registry, IndexedPositiveContainer.Unindexed.liftRegistry,
      PositiveInductiveBlockBridge.Direct.registry, Option.map_none] at found
    cases found

def guards : FieldGuards (reading arithmetic A) where
  value sort := match sort with
    | .length => .lam .top
    | .payload => elements.predicate
  shape _ _ found _ := by
    simp only [registry, IndexedPositiveContainer.Unindexed.liftRegistry,
      PositiveInductiveBlockBridge.Direct.registry, Option.map_none] at found
    cases found

theorem images : FieldImages (realization arithmetic model A numbers elements) (guards arithmetic model A elements) where
  value_correct := by
    intro sort target
    cases sort with
    | length =>
        constructor
        · intro _
          exact (naturalValues arithmetic model numbers).surjective target
        · intro _
          exact True.intro
    | payload => exact elements.image target
  shape_correct := by
    intro context name entry found
    simp only [registry, IndexedPositiveContainer.Unindexed.liftRegistry,
      PositiveInductiveBlockBridge.Direct.registry, Option.map_none] at found
    cases found

theorem injections (element_injective : Function.Injective elements.value) :
    FieldInjective (realization arithmetic model A numbers elements) where
  value := by
    intro sort
    cases sort with
    | length => exact (naturalValues arithmetic model numbers).injective
    | payload => exact element_injective
  shape := by
    intro name entry found
    simp only [registry, IndexedPositiveContainer.Unindexed.liftRegistry,
      PositiveInductiveBlockBridge.Direct.registry, Option.map_none] at found
    cases found

/-- A full scalar guard is justified by a primitive carrier equivalence. -/
def fullElements (equivalence : A ≃ Ty.denote model.Carrier arithmetic.element) :
    Elements arithmetic model A where
  value := equivalence
  predicate := .lam .top
  image := by
    intro target
    constructor
    · intro _; exact equivalence.surjective target
    · intro _; exact True.intro

/-- The ambient HOL carrier remains available; its source membership is empty. -/
def emptyElements : Elements arithmetic model Empty where
  value := Empty.elim
  predicate := .lam .bot
  image := by
    intro target
    change False ↔ ∃ source : Empty, Empty.elim source = target
    constructor
    · exact False.elim
    · rintro ⟨source, _⟩; exact source.elim

#print axioms realization
#print axioms images
#print axioms emptyElements
end
end Mettapedia.GSLT.LanguageDef.IndexedInductiveHOLRealization
