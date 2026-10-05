import Mettapedia.TypeTheory.ContextualSmallFamilyTypeFormerCoherence
import Mettapedia.TypeTheory.ContextualCoherentSmallMaps
import Mettapedia.TypeTheory.MaterialSets.Hypersets.CoveredFuturePowerClassifier

/-!
# Small power families on complete contextual futures

For an authored small displayed family over an independently wider base,
each power fibre is the full type of stable predicates on its actual small
future cone. Prefixing an actual arrow constructs restriction, with proved
identity and composition. The power remains at the original fibre bound.

Whole compatible power sections correspond exactly to stable subfamilies of
the original displayed family. This is the full future classifier, not a
present-subset operation. Its universe code and decoder are constructed.
The construction uses full proposition-valued subsets and propositional
extensionality; it does not establish a predicative powerclass principle.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualSmallFamilyPowers

open _root_.CategoryTheory ContextualWitnessCover ContextualSmallFamilyTypeFormers
open MaterialSets.Hypersets.CoveredFuturePowerClassifier

universe u v
variable {D : Type u} [Category.{u} D] {base : D ⥤ Type v}
variable (domain : base.Elements ⥤ Type u)

abbrev PowerAt (point : base.Elements) : Type u := StablePredicate (futureDomain domain point)

def powerMap {first second : base.Elements} (step : first ⟶ second) (predicate : PowerAt domain first) :
    PowerAt domain second where
  holds argument := predicate.holds ((prefixArguments domain step).obj argument)
  closed move admitted := predicate.closed ((prefixArguments domain step).map move) admitted

theorem powerMap_id (point : base.Elements) (predicate : PowerAt domain point) :
    powerMap domain (𝟙 point) predicate = predicate := by
  apply StablePredicate.ext
  intro argument
  change predicate.holds ((prefixArguments domain (𝟙 point)).obj argument) ↔ predicate.holds argument
  exact Iff.of_eq (congrArg predicate.holds (prefixArguments_id domain point argument))

theorem powerMap_comp {first middle last : base.Elements} (earlier : first ⟶ middle) (later : middle ⟶ last)
    (predicate : PowerAt domain first) : powerMap domain (earlier ≫ later) predicate =
      powerMap domain later (powerMap domain earlier predicate) := by
  apply StablePredicate.ext
  intro argument
  change predicate.holds ((prefixArguments domain (earlier ≫ later)).obj argument) ↔
    predicate.holds ((prefixArguments domain earlier).obj ((prefixArguments domain later).obj argument))
  exact Iff.of_eq (congrArg predicate.holds (prefixArguments_comp domain earlier later argument))

def power : base.Elements ⥤ Type u where
  obj := PowerAt domain
  map step := TypeCat.ofHom (powerMap domain step)
  map_id point := by
    apply ConcreteCategory.hom_ext
    exact powerMap_id domain point
  map_comp earlier later := by
    apply ConcreteCategory.hom_ext
    exact powerMap_comp domain earlier later

def member (point : base.Elements) (argument : domain.obj point) (predicate : PowerAt domain point) : Prop :=
  predicate.holds (currentArgument domain point argument)

theorem member_transport {first second : base.Elements} (step : first ⟶ second)
    (argument : domain.obj first) (predicate : PowerAt domain first)
    (admitted : member domain first argument predicate) :
    member domain second (domain.map step argument) (powerMap domain step predicate) :=
  predicate.closed (currentArgumentStep domain step argument) admitted

structure Subfamily where
  holds : domain.Elements → Prop
  closed : ∀ {first second} (_step : first ⟶ second), holds first → holds second

namespace Subfamily

theorem ext (first second : Subfamily domain) (same : ∀ point, first.holds point ↔ second.holds point) :
    first = second := by
  cases first with
  | mk first firstLaw =>
    cases second with
    | mk second secondLaw =>
      have predicates : first = second := funext fun point => propext (same point)
      cases predicates
      rfl

end Subfamily

def classify (subfamily : Subfamily domain) : (power domain).sections :=
  ⟨fun point => {
    holds argument := subfamily.holds ((futureArguments domain point).obj argument)
    closed step admitted := subfamily.closed ((futureArguments domain point).map step) admitted }, by
    intro first second step
    apply StablePredicate.ext
    intro argument
    change subfamily.holds ((futureArguments domain first).obj ((prefixArguments domain step).obj argument)) ↔
      subfamily.holds ((futureArguments domain second).obj argument)
    exact (prefixArguments_embedding domain step argument) ▸ Iff.rfl⟩

def recover (term : (power domain).sections) : Subfamily domain where
  holds point := member domain point.1 point.2 (term.val point.1)
  closed {first second} step admitted := by
    have transported := member_transport domain step.1 first.2 (term.val first.1) admitted
    have natural := term.property step.1
    change powerMap domain step.1 (term.val first.1) = term.val second.1 at natural
    rw [natural] at transported
    exact step.2 ▸ transported

theorem recover_classify (subfamily : Subfamily domain) : recover domain (classify domain subfamily) = subfamily := by
  apply Subfamily.ext
  intro point
  change subfamily.holds ((futureArguments domain point.1).obj (currentArgument domain point.1 point.2)) ↔
    subfamily.holds point
  exact (currentArgument_embedding domain point.1 point.2) ▸ Iff.rfl

theorem classify_recover (term : (power domain).sections) : classify domain (recover domain term) = term := by
  apply Subtype.ext
  funext point
  apply StablePredicate.ext
  intro argument
  have natural := term.property (futureRootArrow domain point argument)
  have evaluated := congrArg
    (fun predicate : PowerAt domain ((futureArguments domain point).obj argument).1 =>
      predicate.holds (currentArgument domain ((futureArguments domain point).obj argument).1
        ((futureArguments domain point).obj argument).2)) natural
  change (term.val point).holds ((prefixArguments domain (futureRootArrow domain point argument)).obj
      (currentArgument domain ((futureArguments domain point).obj argument).1
        ((futureArguments domain point).obj argument).2)) =
    (term.val ((futureArguments domain point).obj argument).1).holds
      (currentArgument domain ((futureArguments domain point).obj argument).1
        ((futureArguments domain point).obj argument).2) at evaluated
  have returns := prefixCurrent_returns domain point argument
  exact Iff.of_eq ((congrArg (term.val point).holds returns).symm.trans evaluated).symm

def sectionSubfamilyEquiv : (power domain).sections ≃ Subfamily domain where
  toFun := recover domain
  invFun := classify domain
  left_inv := classify_recover domain
  right_inv := recover_classify domain

theorem classified_member (subfamily : Subfamily domain) (point : base.Elements) (argument : domain.obj point) :
    member domain point argument ((classify domain subfamily).val point) ↔ subfamily.holds ⟨point, argument⟩ :=
  (currentArgument_embedding domain point argument) ▸ Iff.rfl

abbrev code := ContextualSmallFamilyUniverse.classifier (power domain)

theorem whole_power_decodes : ContextualSmallFamilyUniverse.decodedFamily (code domain) = power domain :=
  ContextualSmallFamilyUniverse.decoded_classifier_eq (power domain)

def powerProjectionData : ContextualCoherentSmallMaps.Data
    (ContextualSmallFamilyUniverse.projection (power domain)) :=
  ContextualCoherentSmallMaps.projectionData (power domain)

theorem powerProjection_small : ContextualImageFactorization.SmallFibres
    (ContextualSmallFamilyUniverse.projection (power domain)) :=
  (powerProjectionData domain).smallFibres

end Mettapedia.TypeTheory.ContextualSmallFamilyPowers
