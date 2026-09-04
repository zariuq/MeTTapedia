import Mettapedia.GSLT.Core.ContextualTypeReindexing
import Mettapedia.TypeTheory.CategoryIndexedFamilyCwf
import Mettapedia.TypeTheory.ContextualIdentityTypes
import Mettapedia.TypeTheory.ContextualSumComparison
import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Yoneda

/-!
# Dependent type formers for category-indexed families

Proof-relevant contexts are small categories and dependent types are
covariant functors into `Type`.  Dependent sums and fibrewise extensional
identity require only forward functorial transport.  Pointwise dependent
products require the domain functor to send every route to an equivalence,
because transporting a dependent function forward must move its argument
backward.

This is the proof-relevant counterpart of the route-family variance theorem.
It does not add intrinsic intensional identity elimination.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.CategoryIndexedFamilyTypeFormers

open CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.GSLT.Core.ContextualLadder.TypeOver
open Mettapedia.TypeTheory.CategoryIndexedFamilyCwf
open Mettapedia.TypeTheory.ContextualIdentityTypes
open Mettapedia.TypeTheory.ContextualProductComparison
open Mettapedia.TypeTheory.ContextualSumComparison

universe u

/-! ## Lifting substitutions through comprehension -/

/-- The concrete functor between categories of elements induced by a base
substitution. -/
def liftIndexedSubstitution {source target : Context.{u}}
    (substitution : ContextHom source target)
    (family : IndexedFamily target) :
    ContextHom (extend source (reindexFamily family substitution))
      (extend target family) where
  obj point := ⟨substitution.obj point.1, point.2⟩
  map route := CategoryOfElements.homMk _ _
    (substitution.map route.val) route.property
  map_id point := by
    apply CategoryOfElements.ext family
    exact substitution.map_id point.1
  map_comp earlier later := by
    apply CategoryOfElements.ext family
    exact substitution.map_comp earlier.val later.val

/-- The concrete lift is the generic CwF extension substitution. -/
theorem liftIndexedSubstitution_eq_extensionSubstitution
    {source target : Context.{u}}
    (substitution : ContextHom source target)
    (family : IndexedFamily target) :
    liftIndexedSubstitution substitution family =
      extensionSubstitution (C := categoryIndexedCwf) substitution family := by
  apply CategoryTheory.Functor.ext (fun _ => rfl)

/-! ## Dependent sums -/

/-- The canonical lift of a base morphism at one element of a family. -/
def elementLift {context : Context.{u}} (family : IndexedFamily context)
    {source target : context} (route : source ⟶ target)
    (value : family.obj source) :
    (show extend context family from ⟨source, value⟩) ⟶
      (show extend context family from
        ⟨target, family.map route value⟩) :=
  CategoryOfElements.homMk _ _ route rfl

/-- The base arrow of an equality-induced morphism between elements is the
equality-induced morphism between their base objects. -/
private theorem elements_eqToHom_val
    {context : Context.{u}} {family : IndexedFamily context}
    {left right : family.Elements} (equality : left = right) :
    (eqToHom equality : left ⟶ right).val =
      eqToHom (congrArg Sigma.fst equality) := by
  cases equality
  rfl

/-- Equality of the corresponding nested total-space objects implies equality
of dependent values in one base fibre. -/
private theorem sigmaValue_eq_of_total_eq
    {context : Context.{u}} {domain : IndexedFamily context}
    {codomain : IndexedFamily (extend context domain)}
    {point : context} {leftArgument rightArgument : domain.obj point}
    {leftResult : codomain.obj ⟨point, leftArgument⟩}
    {rightResult : codomain.obj ⟨point, rightArgument⟩}
    (equality :
      (⟨⟨point, leftArgument⟩, leftResult⟩ : codomain.Elements) =
        ⟨⟨point, rightArgument⟩, rightResult⟩) :
    (⟨leftArgument, leftResult⟩ :
      Sigma fun argument : domain.obj point =>
        codomain.obj ⟨point, argument⟩) =
      ⟨rightArgument, rightResult⟩ := by
  cases equality
  rfl

/-- Equality in a dependent fibre induces equality of the corresponding
nested total-space objects. -/
private theorem total_eq_of_sigmaValue_eq
    {context : Context.{u}} {domain : IndexedFamily context}
    {codomain : IndexedFamily (extend context domain)}
    {point : context} {leftArgument rightArgument : domain.obj point}
    {leftResult : codomain.obj ⟨point, leftArgument⟩}
    {rightResult : codomain.obj ⟨point, rightArgument⟩}
    (equality :
      (⟨leftArgument, leftResult⟩ :
        Sigma fun argument : domain.obj point =>
          codomain.obj ⟨point, argument⟩) =
        ⟨rightArgument, rightResult⟩) :
    (⟨⟨point, leftArgument⟩, leftResult⟩ : codomain.Elements) =
      ⟨⟨point, rightArgument⟩, rightResult⟩ := by
  cases equality
  rfl

/-- Equality of total-space objects transports the dependent component along
the equality-induced morphism between their indices. -/
private theorem elements_snd_transport
    {base : Type u} [Category.{u} base] {family : base ⥤ Type u}
    {left right : family.Elements} (equality : left = right) :
    family.map (eqToHom (congrArg Sigma.fst equality)) left.snd =
      right.snd := by
  cases equality
  exact family.map_id_apply _ _

/-- A functor to types maps an equality-induced arrow to dependent equality
transport. -/
private theorem map_eqToHom_apply_of_heq
    {base : Type u} [Category.{u} base] (family : base ⥤ Type u)
    {leftPoint rightPoint : base} (pointEquality : leftPoint = rightPoint)
    {leftValue : family.obj leftPoint}
    {rightValue : family.obj rightPoint}
    (valueEquality : HEq leftValue rightValue) :
    family.map (eqToHom pointEquality) leftValue = rightValue := by
  cases pointEquality
  simpa using eq_of_heq valueEquality

/-- Fibrewise dependent summation, with both components transported along
the selected proof-relevant route. -/
def sigmaFamily {context : Context.{u}} (domain : IndexedFamily context)
    (codomain : IndexedFamily (extend context domain)) :
    IndexedFamily context where
  obj point := Sigma fun argument : domain.obj point =>
    codomain.obj ⟨point, argument⟩
  map route := TypeCat.ofHom fun value =>
    ⟨domain.map route value.1,
      codomain.map (elementLift domain route value.1) value.2⟩
  map_id point := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext value
    rcases value with ⟨argument, result⟩
    let sourcePoint : domain.Elements := ⟨point, argument⟩
    let mappedPoint : domain.Elements :=
      ⟨point, domain.map (𝟙 point) argument⟩
    have pointIdentity : mappedPoint = sourcePoint := by
      apply Functor.Elements.ext mappedPoint sourcePoint rfl
      simp [mappedPoint, sourcePoint]
    have liftRoundtrip :
        elementLift domain (𝟙 point) argument ≫ eqToHom pointIdentity =
          𝟙 sourcePoint := by
      apply CategoryOfElements.ext domain
      change (𝟙 point) ≫ (eqToHom pointIdentity).val = 𝟙 point
      rw [elements_eqToHom_val]
      have baseEquality : congrArg Sigma.fst pointIdentity = rfl :=
        Subsingleton.elim _ _
      rw [baseEquality]
      simp [mappedPoint, sourcePoint]
    have resultIdentity :
        codomain.map (eqToHom pointIdentity)
            (codomain.map (elementLift domain (𝟙 point) argument) result) =
          result := by
      calc
        _ = codomain.map
              (elementLift domain (𝟙 point) argument ≫
                eqToHom pointIdentity) result :=
          (codomain.map_comp_apply _ _ result).symm
        _ = codomain.map (𝟙 sourcePoint) result := by rw [liftRoundtrip]
        _ = result := codomain.map_id_apply sourcePoint result
    exact sigmaValue_eq_of_total_eq
      (Functor.Elements.ext _ _ pointIdentity resultIdentity)
  map_comp earlier later := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext value
    rcases value with ⟨argument, result⟩
    let directPoint : domain.Elements :=
      ⟨_, domain.map (earlier ≫ later) argument⟩
    let sequentialPoint : domain.Elements :=
      ⟨_, domain.map later (domain.map earlier argument)⟩
    have pointComposite : directPoint = sequentialPoint := by
      apply Functor.Elements.ext directPoint sequentialPoint rfl
      simp [directPoint, sequentialPoint]
    have liftComposite :
        elementLift domain (earlier ≫ later) argument ≫
            eqToHom pointComposite =
          elementLift domain earlier argument ≫
            elementLift domain later (domain.map earlier argument) := by
      apply CategoryOfElements.ext domain
      change
        (earlier ≫ later) ≫ (eqToHom pointComposite).val =
          earlier ≫ later
      rw [elements_eqToHom_val]
      have baseEquality : congrArg Sigma.fst pointComposite = rfl :=
        Subsingleton.elim _ _
      rw [baseEquality]
      simp [directPoint, sequentialPoint]
    have resultComposite :
        codomain.map (eqToHom pointComposite)
            (codomain.map
              (elementLift domain (earlier ≫ later) argument) result) =
          codomain.map
            (elementLift domain later (domain.map earlier argument))
            (codomain.map (elementLift domain earlier argument) result) := by
      calc
        _ = codomain.map
              (elementLift domain (earlier ≫ later) argument ≫
                eqToHom pointComposite) result :=
          (codomain.map_comp_apply _ _ result).symm
        _ = codomain.map
              (elementLift domain earlier argument ≫
                elementLift domain later (domain.map earlier argument))
              result := by rw [liftComposite]
        _ = _ := codomain.map_comp_apply _ _ result
    exact sigmaValue_eq_of_total_eq
      (Functor.Elements.ext _ _ pointComposite resultComposite)

/-- Pair two compatible natural sections into a dependent-sum section. -/
def sigmaPair {context : Context.{u}} {domain : IndexedFamily context}
    {codomain : IndexedFamily (extend context domain)}
    (first : IndexedSection domain)
    (second : categoryIndexedCwf.Tm context
      (categoryIndexedCwf.tySub codomain
        (selfExtend categoryIndexedCwf first))) :
    IndexedSection (sigmaFamily domain codomain) :=
  ⟨fun point => ⟨first.1 point, second.1 point⟩, by
    intro source target route
    let sourcePoint : domain.Elements := ⟨source, first.1 source⟩
    let mappedPoint : domain.Elements :=
      ⟨target, domain.map route (first.1 source)⟩
    let targetPoint : domain.Elements := ⟨target, first.1 target⟩
    have pointNatural : mappedPoint = targetPoint := by
      apply Functor.Elements.ext mappedPoint targetPoint rfl
      simp [mappedPoint, targetPoint]
    have graphFactorization :
        elementLift domain route (first.1 source) ≫
            eqToHom pointNatural =
          (selfExtend categoryIndexedCwf first).map route := by
      apply CategoryOfElements.ext domain
      change route ≫ (eqToHom pointNatural).val = route
      have equalityBase :=
        elements_eqToHom_val (family := domain) pointNatural
      have baseEquality : congrArg Sigma.fst pointNatural = rfl :=
        Subsingleton.elim _ _
      calc
        _ = route ≫ eqToHom (congrArg Sigma.fst pointNatural) :=
          congrArg (fun baseRoute => route ≫ baseRoute) equalityBase
        _ = route ≫ eqToHom rfl := by rw [baseEquality]
        _ = route := by simp
    have secondNatural := second.2 route
    change
      codomain.map ((selfExtend categoryIndexedCwf first).map route)
          (second.1 source) = second.1 target at secondNatural
    have mappedFactorization :
        codomain.map
            (elementLift domain route (first.1 source) ≫
              eqToHom pointNatural) (second.1 source) =
          codomain.map
            ((selfExtend categoryIndexedCwf first).map route)
            (second.1 source) :=
      congrArg
        (fun selectedRoute =>
          codomain.map selectedRoute (second.1 source))
        graphFactorization
    have resultNatural :
        codomain.map (eqToHom pointNatural)
            (codomain.map
              (elementLift domain route (first.1 source))
              (second.1 source)) =
          second.1 target := by
      exact (codomain.map_comp_apply _ _ _).symm.trans
        (mappedFactorization.trans secondNatural)
    exact sigmaValue_eq_of_total_eq
      (Functor.Elements.ext _ _ pointNatural resultNatural)⟩

/-- First projection of a category-indexed dependent sum. -/
def sigmaFst {context : Context.{u}} {domain : IndexedFamily context}
    {codomain : IndexedFamily (extend context domain)}
    (value : IndexedSection (sigmaFamily domain codomain)) :
    IndexedSection domain :=
  ⟨fun point => (value.1 point).1, fun route =>
    congrArg Sigma.fst (value.2 route)⟩

/-- Second projection of a category-indexed dependent sum. -/
def sigmaSnd {context : Context.{u}} {domain : IndexedFamily context}
    {codomain : IndexedFamily (extend context domain)}
    (value : IndexedSection (sigmaFamily domain codomain)) :
    categoryIndexedCwf.Tm context
      (categoryIndexedCwf.tySub codomain
        (selfExtend categoryIndexedCwf (sigmaFst value))) :=
  ⟨fun point => (value.1 point).2, by
    intro source target route
    have wholeNatural := value.2 route
    have totalNatural :
        (⟨⟨target, domain.map route (value.1 source).1⟩,
            codomain.map
              (elementLift domain route (value.1 source).1)
              (value.1 source).2⟩ : codomain.Elements) =
          ⟨⟨target, (value.1 target).1⟩, (value.1 target).2⟩ :=
      total_eq_of_sigmaValue_eq wholeNatural
    let mappedPoint : extend context domain :=
      ⟨target, domain.map route (value.1 source).1⟩
    let targetPoint : extend context domain :=
      ⟨target, (value.1 target).1⟩
    let pointNatural : mappedPoint = targetPoint := by
      simpa [mappedPoint, targetPoint] using
        congrArg Sigma.fst totalNatural
    have resultNatural :
        codomain.map (eqToHom pointNatural)
            (codomain.map
              (elementLift domain route (value.1 source).1)
              (value.1 source).2) =
          (value.1 target).2 :=
      by
        simpa [pointNatural, mappedPoint, targetPoint] using
          elements_snd_transport totalNatural
    have graphFactorization :
        elementLift domain route (value.1 source).1 ≫
            eqToHom pointNatural =
          (selfExtend categoryIndexedCwf (sigmaFst value)).map route := by
      apply CategoryOfElements.ext domain
      change route ≫ (eqToHom pointNatural).val = route
      have equalityBase :=
        elements_eqToHom_val (family := domain) pointNatural
      have baseEquality : congrArg Sigma.fst pointNatural = rfl :=
        Subsingleton.elim _ _
      calc
        _ = route ≫ eqToHom (congrArg Sigma.fst pointNatural) :=
          congrArg (fun baseRoute => route ≫ baseRoute) equalityBase
        _ = route ≫ eqToHom rfl := by rw [baseEquality]
        _ = route := by simp
    have mappedFactorization :
        codomain.map
            (elementLift domain route (value.1 source).1 ≫
              eqToHom pointNatural) (value.1 source).2 =
          codomain.map
            ((selfExtend categoryIndexedCwf (sigmaFst value)).map route)
            (value.1 source).2 :=
      congrArg
        (fun selectedRoute =>
          codomain.map selectedRoute (value.1 source).2)
        graphFactorization
    exact mappedFactorization.symm.trans
      ((codomain.map_comp_apply _ _ _).trans resultNatural)⟩

/-- Category-indexed families carry the full beta fragment of dependent
sums. -/
def indexedDependentSums : DependentSumBeta categoryIndexedCwf where
  sigma := sigmaFamily
  pair := sigmaPair
  fst := sigmaFst
  snd := sigmaSnd
  fst_pair first second := by
    apply Subtype.ext
    rfl
  snd_pair first second := HEq.rfl

/-- Dependent-sum formation commutes with functor substitution. -/
theorem sigmaFamily_reindex {source target : Context.{u}}
    (domain : IndexedFamily target)
    (codomain : IndexedFamily (extend target domain))
    (substitution : ContextHom source target) :
    reindexFamily (sigmaFamily domain codomain) substitution =
      sigmaFamily (reindexFamily domain substitution)
        (reindexFamily codomain
          (liftIndexedSubstitution substitution domain)) := by
  exact CategoryTheory.Functor.ext (fun _ => rfl)

/-! ## Fibrewise extensional identity -/

/-- Lifted equality witnesses are subsingletons. -/
@[reducible] def liftedEqualitySubsingleton {Value : Type u}
    (left right : Value) :
    Subsingleton (ULift (PLift (left = right))) where
  allEq first second := by
    rcases first with ⟨⟨firstProof⟩⟩
    rcases second with ⟨⟨secondProof⟩⟩
    cases Subsingleton.elim firstProof secondProof
    rfl

/-- Equality in each fibre, transported by congruence and naturality of its
endpoints. -/
def identityFamily {context : Context.{u}}
    (family : IndexedFamily context)
    (left right : IndexedSection family) : IndexedFamily context where
  obj point := ULift (PLift (left.1 point = right.1 point))
  map route := TypeCat.ofHom fun witness =>
    ⟨⟨(left.2 route).symm.trans
      ((congrArg (family.map route) witness.down.down).trans
        (right.2 route))⟩⟩
  map_id point := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext witness
    exact (liftedEqualitySubsingleton _ _).allEq _ _
  map_comp earlier later := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext witness
    exact (liftedEqualitySubsingleton _ _).allEq _ _

/-- Fibrewise equality is substitution-stable. -/
def indexedIdentityFormation : IdentityFormation categoryIndexedCwf where
  idTy := identityFamily
  idTy_sub _ _ _ _ := rfl

/-- Reflexivity is a natural section of fibrewise equality. -/
def indexedIdentityReflexivity :
    IdentityReflexivity categoryIndexedCwf indexedIdentityFormation where
  refl _term :=
    ⟨fun _ => ⟨⟨rfl⟩⟩, fun _ =>
      (liftedEqualitySubsingleton _ _).allEq _ _⟩
  refl_sub := by
    intro source target substitution family term
    exact HEq.rfl

/-- The selected extensional identity is proof-irrelevant. -/
theorem indexedIdentityProofIrrelevance :
    IdentityProofIrrelevance categoryIndexedCwf indexedIdentityFormation := by
  intro context family left right
  constructor
  intro first second
  apply Subtype.ext
  funext point
  exact (liftedEqualitySubsingleton _ _).allEq _ _

/-- An inhabited selected identity family reflects equality of sections. -/
theorem indexedIdentityEndpointReflection :
    IdentityEndpointReflection categoryIndexedCwf indexedIdentityFormation := by
  intro context family left right witness
  apply Subtype.ext
  funext point
  exact (witness.1 point).down.down

/-! ## Dependent products with invertible domain action -/

/-- Every map of the domain functor is selected as the forward map of an
equivalence. -/
structure FibrewiseEquivalenceAction {context : Context.{u}}
    (family : IndexedFamily context) : Type (u + 1) where
  equivalence : {source target : context} ->
    (route : source ⟶ target) -> family.obj source ≃ family.obj target
  apply_eq_map : forall {source target : context}
    (route : source ⟶ target) (value : family.obj source),
    equivalence route value = family.map route value

namespace FibrewiseEquivalenceAction

/-- Transport a target value backward along the selected equivalence. -/
def inverse {context : Context.{u}} {family : IndexedFamily context}
    (action : FibrewiseEquivalenceAction family)
    {source target : context} (route : source ⟶ target)
    (value : family.obj target) : family.obj source :=
  (action.equivalence route).symm value

/-- Forward action after inverse action returns the target value. -/
theorem map_inverse {context : Context.{u}}
    {family : IndexedFamily context}
    (action : FibrewiseEquivalenceAction family)
    {source target : context} (route : source ⟶ target)
    (value : family.obj target) :
    family.map route (action.inverse route value) = value := by
  rw [← action.apply_eq_map]
  exact (action.equivalence route).apply_symm_apply value

/-- Inverse action after forward action returns the source value. -/
theorem inverse_map {context : Context.{u}}
    {family : IndexedFamily context}
    (action : FibrewiseEquivalenceAction family)
    {source target : context} (route : source ⟶ target)
    (value : family.obj source) :
    action.inverse route (family.map route value) = value := by
  rw [← action.apply_eq_map]
  exact (action.equivalence route).symm_apply_apply value

/-- Pullback along a base functor preserves invertible fibre action. -/
def reindex {source target : Context.{u}}
    {family : IndexedFamily target}
    (action : FibrewiseEquivalenceAction family)
    (substitution : ContextHom source target) :
    FibrewiseEquivalenceAction (reindexFamily family substitution) where
  equivalence route := action.equivalence (substitution.map route)
  apply_eq_map route value :=
    action.apply_eq_map (substitution.map route) value

/-- Constant families have identity equivalence action. -/
def constant (context : Context.{u}) (valueType : Type u) :
    FibrewiseEquivalenceAction
      ((Functor.const (context : Type u)).obj valueType) where
  equivalence _ := Equiv.refl valueType
  apply_eq_map _ _ := rfl

/-- Every family over a groupoid has invertible fibre action, because every
context morphism already has an inverse. -/
def ofGroupoid {base : Type u} [SmallGroupoid base]
    (family : base ⥤ Type u) :
    FibrewiseEquivalenceAction (context := Cat.of base) family where
  equivalence route :=
    { toFun := family.map route
      invFun := family.map (Groupoid.inv route)
      left_inv := fun value => by
        calc
          family.map (Groupoid.inv route) (family.map route value) =
              family.map (route ≫ Groupoid.inv route) value :=
            (family.map_comp_apply route (Groupoid.inv route) value).symm
          _ = family.map (𝟙 _) value := by rw [Groupoid.comp_inv]
          _ = value := family.map_id_apply _ value
      right_inv := fun value => by
        calc
          family.map route (family.map (Groupoid.inv route) value) =
              family.map (Groupoid.inv route ≫ route) value :=
            (family.map_comp_apply (Groupoid.inv route) route value).symm
          _ = family.map (𝟙 _) value := by rw [Groupoid.inv_comp]
          _ = value := family.map_id_apply _ value }
  apply_eq_map _ _ := rfl

end FibrewiseEquivalenceAction

/-! ## Pointwise dependent products on the invertible-action fragment -/

/-- Lift a base route to the category of elements by pulling a target
argument backward through the selected equivalence. -/
def equivalenceElementLift {context : Context.{u}}
    {family : IndexedFamily context}
    (action : FibrewiseEquivalenceAction family)
    {source target : context} (route : source ⟶ target)
    (targetValue : family.obj target) :
    (show extend context family from
      ⟨source, action.inverse route targetValue⟩) ⟶
      (show extend context family from ⟨target, targetValue⟩) :=
  CategoryOfElements.homMk _ _ route
    (action.map_inverse route targetValue)

/-- Pointwise dependent functions form a functor whenever every domain action
is invertible. -/
def piFamily {context : Context.{u}} (domain : IndexedFamily context)
    (domainAction : FibrewiseEquivalenceAction domain)
    (codomain : IndexedFamily (extend context domain)) :
    IndexedFamily context where
  obj point := forall argument : domain.obj point,
    codomain.obj ⟨point, argument⟩
  map route := TypeCat.ofHom fun function targetArgument =>
    codomain.map
      (equivalenceElementLift domainAction route targetArgument)
      (function (domainAction.inverse route targetArgument))
  map_id point := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext function
    funext argument
    let inverseArgument := domainAction.inverse (𝟙 point) argument
    have inverseIdentity : inverseArgument = argument := by
      calc
        inverseArgument = domainAction.inverse (𝟙 point)
            (domain.map (𝟙 point) argument) :=
          congrArg (domainAction.inverse (𝟙 point))
            (domain.map_id_apply point argument).symm
        _ = argument := domainAction.inverse_map (𝟙 point) argument
    let inversePoint : extend context domain :=
      ⟨point, inverseArgument⟩
    let targetPoint : extend context domain := ⟨point, argument⟩
    let pointIdentity : inversePoint = targetPoint :=
      congrArg
        (fun selectedArgument =>
          (show extend context domain from ⟨point, selectedArgument⟩))
        inverseIdentity
    have liftIdentity :
        equivalenceElementLift domainAction (𝟙 point) argument =
          eqToHom pointIdentity := by
      apply CategoryOfElements.ext domain
      change (𝟙 point) = (eqToHom pointIdentity).val
      have equalityBase :=
        elements_eqToHom_val (family := domain) pointIdentity
      have baseEquality : congrArg Sigma.fst pointIdentity = rfl :=
        Subsingleton.elim _ _
      calc
        _ = eqToHom rfl := by simp [inversePoint]
        _ = eqToHom (congrArg Sigma.fst pointIdentity) := by rw [baseEquality]
        _ = (eqToHom pointIdentity).val := equalityBase.symm
    have functionIdentity : HEq (function inverseArgument) (function argument) :=
      congr_arg_heq function inverseIdentity
    calc
      codomain.map
          (equivalenceElementLift domainAction (𝟙 point) argument)
          (function inverseArgument) =
          codomain.map (eqToHom pointIdentity)
            (function inverseArgument) := by rw [liftIdentity]
      _ = function argument :=
        map_eqToHom_apply_of_heq codomain pointIdentity functionIdentity
  map_comp earlier later := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext function
    funext argument
    let directInverse :=
      domainAction.inverse (earlier ≫ later) argument
    let sequentialInverse :=
      domainAction.inverse earlier (domainAction.inverse later argument)
    have directForward :
        domain.map (earlier ≫ later) directInverse = argument :=
      domainAction.map_inverse (earlier ≫ later) argument
    have sequentialForward :
        domain.map (earlier ≫ later) sequentialInverse = argument := by
      calc
        _ = domain.map later (domain.map earlier sequentialInverse) :=
          domain.map_comp_apply earlier later sequentialInverse
        _ = domain.map later (domainAction.inverse later argument) := by
          rw [domainAction.map_inverse]
        _ = argument := domainAction.map_inverse later argument
    have inverseComposite : directInverse = sequentialInverse := by
      apply (domainAction.equivalence (earlier ≫ later)).injective
      rw [domainAction.apply_eq_map, domainAction.apply_eq_map]
      exact directForward.trans sequentialForward.symm
    let directPoint : extend context domain := ⟨_, directInverse⟩
    let sequentialPoint : extend context domain := ⟨_, sequentialInverse⟩
    let sourceEquality : directPoint = sequentialPoint :=
      congrArg
        (fun selectedArgument =>
          (show extend context domain from ⟨_, selectedArgument⟩))
        inverseComposite
    have functionTransport :
        codomain.map (eqToHom sourceEquality) (function directInverse) =
          function sequentialInverse :=
      map_eqToHom_apply_of_heq codomain sourceEquality
        (congr_arg_heq function inverseComposite)
    have liftComposite :
        eqToHom sourceEquality ≫
            equivalenceElementLift domainAction earlier
              (domainAction.inverse later argument) ≫
            equivalenceElementLift domainAction later argument =
          equivalenceElementLift domainAction (earlier ≫ later) argument := by
      apply CategoryOfElements.ext domain
      change
        (eqToHom sourceEquality).val ≫ earlier ≫ later = earlier ≫ later
      have equalityBase :=
        elements_eqToHom_val (family := domain) sourceEquality
      have baseEquality : congrArg Sigma.fst sourceEquality = rfl :=
        Subsingleton.elim _ _
      calc
        _ = eqToHom (congrArg Sigma.fst sourceEquality) ≫
              earlier ≫ later :=
          congrArg
            (fun baseRoute => baseRoute ≫ earlier ≫ later)
            equalityBase
        _ = eqToHom rfl ≫ earlier ≫ later := by rw [baseEquality]
        _ = earlier ≫ later := by simp
    calc
      codomain.map
          (equivalenceElementLift domainAction (earlier ≫ later) argument)
          (function directInverse) =
          codomain.map
            (eqToHom sourceEquality ≫
              equivalenceElementLift domainAction earlier
                (domainAction.inverse later argument) ≫
              equivalenceElementLift domainAction later argument)
            (function directInverse) := by rw [liftComposite]
      _ = codomain.map
            (equivalenceElementLift domainAction later argument)
            (codomain.map
              (equivalenceElementLift domainAction earlier
                (domainAction.inverse later argument))
              (codomain.map (eqToHom sourceEquality)
                (function directInverse))) := by
          rw [codomain.map_comp_apply, codomain.map_comp_apply]
      _ = codomain.map
            (equivalenceElementLift domainAction later argument)
            (codomain.map
              (equivalenceElementLift domainAction earlier
                (domainAction.inverse later argument))
              (function sequentialInverse)) := by rw [functionTransport]

/-! ## Product introduction, elimination, and beta -/

/-- Lambda abstraction for products with invertible domain action. -/
def piLam {context : Context.{u}} {domain : IndexedFamily context}
    (domainAction : FibrewiseEquivalenceAction domain)
    {codomain : IndexedFamily (extend context domain)}
    (body : IndexedSection codomain) :
    IndexedSection (piFamily domain domainAction codomain) :=
  ⟨fun point argument => body.1 ⟨point, argument⟩, by
    intro source target route
    funext targetArgument
    exact body.2
      (equivalenceElementLift domainAction route targetArgument)⟩

/-- Application for products with invertible domain action. -/
def piApp {context : Context.{u}} {domain : IndexedFamily context}
    (domainAction : FibrewiseEquivalenceAction domain)
    {codomain : IndexedFamily (extend context domain)}
    (function : IndexedSection (piFamily domain domainAction codomain))
    (argument : IndexedSection domain) :
    categoryIndexedCwf.Tm context
      (categoryIndexedCwf.tySub codomain
        (selfExtend categoryIndexedCwf argument)) :=
  ⟨fun point => function.1 point (argument.1 point), by
    intro source target route
    let inverseArgument :=
      domainAction.inverse route (argument.1 target)
    have inverseNatural : inverseArgument = argument.1 source := by
      calc
        inverseArgument = domainAction.inverse route
            (domain.map route (argument.1 source)) :=
          congrArg (domainAction.inverse route)
            (argument.2 route).symm
        _ = argument.1 source :=
          domainAction.inverse_map route (argument.1 source)
    let sourcePoint : extend context domain :=
      ⟨source, argument.1 source⟩
    let inversePoint : extend context domain :=
      ⟨source, inverseArgument⟩
    let sourceEquality : sourcePoint = inversePoint :=
      congrArg
        (fun selectedArgument =>
          (show extend context domain from ⟨source, selectedArgument⟩))
        inverseNatural.symm
    have argumentTransport :
        codomain.map (eqToHom sourceEquality)
            (function.1 source (argument.1 source)) =
          function.1 source inverseArgument :=
      map_eqToHom_apply_of_heq codomain sourceEquality
        (congr_arg_heq (function.1 source) inverseNatural.symm)
    have graphFactorization :
        eqToHom sourceEquality ≫
            equivalenceElementLift domainAction route
              (argument.1 target) =
          (selfExtend categoryIndexedCwf argument).map route := by
      apply CategoryOfElements.ext domain
      change (eqToHom sourceEquality).val ≫ route = route
      have equalityBase :=
        elements_eqToHom_val (family := domain) sourceEquality
      have baseEquality : congrArg Sigma.fst sourceEquality = rfl :=
        Subsingleton.elim _ _
      calc
        _ = eqToHom (congrArg Sigma.fst sourceEquality) ≫ route :=
          congrArg (fun baseRoute => baseRoute ≫ route) equalityBase
        _ = eqToHom rfl ≫ route := by rw [baseEquality]
        _ = route := by simp
    have mappedFactorization :
        codomain.map
            (eqToHom sourceEquality ≫
              equivalenceElementLift domainAction route
                (argument.1 target))
            (function.1 source (argument.1 source)) =
          codomain.map
            ((selfExtend categoryIndexedCwf argument).map route)
            (function.1 source (argument.1 source)) :=
      congrArg
        (fun selectedRoute =>
          codomain.map selectedRoute
            (function.1 source (argument.1 source)))
        graphFactorization
    have functionNatural := congrFun (function.2 route) (argument.1 target)
    change
      codomain.map ((selfExtend categoryIndexedCwf argument).map route)
          (function.1 source (argument.1 source)) =
        function.1 target (argument.1 target)
    exact mappedFactorization.symm.trans
      ((codomain.map_comp_apply _ _ _).trans
        ((congrArg
          (fun selectedValue =>
            codomain.map
              (equivalenceElementLift domainAction route
                (argument.1 target)) selectedValue)
          argumentTransport).trans functionNatural))⟩

/-- Beta computation for the restricted dependent product. -/
theorem pi_beta {context : Context.{u}} {domain : IndexedFamily context}
    (domainAction : FibrewiseEquivalenceAction domain)
    {codomain : IndexedFamily (extend context domain)}
    (body : IndexedSection codomain) (argument : IndexedSection domain) :
    piApp domainAction (piLam domainAction body) argument =
      categoryIndexedCwf.tmSub body
        (selfExtend categoryIndexedCwf argument) := by
  apply Subtype.ext
  rfl

/-- Restricted dependent-product formation commutes with functor
substitution. -/
theorem piFamily_reindex {source target : Context.{u}}
    (domain : IndexedFamily target)
    (domainAction : FibrewiseEquivalenceAction domain)
    (codomain : IndexedFamily (extend target domain))
    (substitution : ContextHom source target) :
    reindexFamily (piFamily domain domainAction codomain) substitution =
      piFamily (reindexFamily domain substitution)
        (domainAction.reindex substitution)
        (reindexFamily codomain
          (liftIndexedSubstitution substitution domain)) := by
  exact CategoryTheory.Functor.ext (fun _ => rfl)

/-! ## Positive and negative variance controls -/

namespace Canary

/-- The walking directed edge.  Its only nonidentity morphism points from
`source` to `target`; there is no route back. -/
inductive DirectedPoint : Type
  | source
  | target

/-- Morphisms of the walking directed edge. -/
inductive DirectedHom : DirectedPoint -> DirectedPoint -> Type
  | stay (point : DirectedPoint) : DirectedHom point point
  | forward : DirectedHom .source .target

namespace DirectedHom

/-- Composition of directed-edge morphisms. -/
def compose {first middle last : DirectedPoint} :
    DirectedHom first middle -> DirectedHom middle last ->
      DirectedHom first last
  | .stay _, later => later
  | .forward, .stay .target => .forward

end DirectedHom

/-- The walking directed edge as a small category. -/
instance directedCategory : SmallCategory DirectedPoint where
  Hom := DirectedHom
  id := DirectedHom.stay
  comp := DirectedHom.compose
  id_comp route := by cases route <;> rfl
  comp_id route := by cases route <;> rfl
  assoc first second third := by
    cases first <;> cases second <;> cases third <;> rfl

/-- The directed two-point proof-relevant context. -/
def directedContext : Context.{0} := Cat.of DirectedPoint

/-- A covariant domain whose forward map includes `PUnit` into `Bool` at
`false`; the target value `true` has no preimage. -/
def directedVaryingDomain : IndexedFamily directedContext where
  obj
    | .source => PUnit
    | .target => Bool
  map route := TypeCat.ofHom <| match route with
    | .stay .source => id
    | .stay .target => id
    | .forward => fun _ => false
  map_id point := by cases point <;> rfl
  map_comp := fun {startPoint middlePoint endPoint} earlier later => by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext value
    cases startPoint <;> cases middlePoint <;> cases endPoint <;>
      cases earlier <;> cases later <;> rfl

/-- The source object in the category of elements. -/
def sourceElement : extend directedContext directedVaryingDomain :=
  ⟨.source, PUnit.unit⟩

/-- The target argument outside the image of forward domain transport. -/
def missingElement : extend directedContext directedVaryingDomain :=
  ⟨.target, true⟩

/-- No total-space morphism reaches the missing target argument from the
source element. -/
theorem noHom_source_to_missing :
    (sourceElement ⟶ missingElement) -> False := by
  rintro ⟨baseRoute, transported⟩
  cases baseRoute with
  | forward =>
      change false = true at transported
      exact Bool.false_ne_true transported

/-- A representable dependent codomain.  Its fibre at a total-space point is
the type of routes from the source element to that point. -/
def missingPreimageCodomain :
    IndexedFamily (extend directedContext directedVaryingDomain) :=
  coyoneda.obj (Opposite.op sourceElement)

/-- The raw pointwise carrier expected of a dependent product. -/
def PointwisePiFibre (point : directedContext) : Type :=
  forall argument : directedVaryingDomain.obj point,
    missingPreimageCodomain.obj ⟨point, argument⟩

/-- The pointwise product at the source is inhabited by identity routes. -/
def sourcePointwiseFunction : PointwisePiFibre .source := by
  intro argument
  cases argument
  exact 𝟙 sourceElement

/-- The target pointwise product is empty because it would have to produce a
route to the missing Boolean argument. -/
theorem targetPointwiseFunction_empty :
    IsEmpty (PointwisePiFibre .target) :=
  ⟨fun function => noHom_source_to_missing (function true)⟩

/-- No category-indexed family can have fibres even equivalent to these
pointwise dependent-function fibres.  Forward transport would map an
inhabited source fibre into an empty target fibre. -/
theorem no_equivalent_pointwisePi_indexedFamily :
    ¬ Exists fun product : IndexedFamily directedContext =>
      forall point : directedContext,
        Nonempty (product.obj point ≃ PointwisePiFibre point) := by
  rintro ⟨product, fibreEquivalence⟩
  rcases fibreEquivalence .source with ⟨sourceEquivalence⟩
  rcases fibreEquivalence .target with ⟨targetEquivalence⟩
  let sourceValue : product.obj .source :=
    sourceEquivalence.symm sourcePointwiseFunction
  let targetValue : product.obj .target :=
    product.map DirectedHom.forward sourceValue
  let impossible : PointwisePiFibre .target :=
    targetEquivalence targetValue
  exact targetPointwiseFunction_empty.false impossible

/-- Families over groupoids supply the inverse action required by pointwise
products, while a genuine directed context refutes unrestricted pointwise
products even up to fibrewise equivalence. -/
theorem dependent_product_variance_boundary :
    (forall (base : Type) [SmallGroupoid base]
      (family : base ⥤ Type),
      Nonempty
        (FibrewiseEquivalenceAction (context := Cat.of base) family)) /\
    ¬ Exists fun product : IndexedFamily directedContext =>
      forall point : directedContext,
        Nonempty (product.obj point ≃ PointwisePiFibre point) :=
  ⟨fun _ _ family => ⟨FibrewiseEquivalenceAction.ofGroupoid family⟩,
    no_equivalent_pointwisePi_indexedFamily⟩

end Canary

#print axioms sigmaFamily
#print axioms liftIndexedSubstitution_eq_extensionSubstitution
#print axioms indexedDependentSums
#print axioms sigmaFamily_reindex
#print axioms identityFamily
#print axioms indexedIdentityFormation
#print axioms indexedIdentityReflexivity
#print axioms indexedIdentityProofIrrelevance
#print axioms indexedIdentityEndpointReflection
#print axioms FibrewiseEquivalenceAction.map_inverse
#print axioms FibrewiseEquivalenceAction.inverse_map
#print axioms FibrewiseEquivalenceAction.reindex
#print axioms FibrewiseEquivalenceAction.ofGroupoid
#print axioms equivalenceElementLift
#print axioms piFamily
#print axioms piLam
#print axioms piApp
#print axioms pi_beta
#print axioms piFamily_reindex
#print axioms Canary.noHom_source_to_missing
#print axioms Canary.targetPointwiseFunction_empty
#print axioms Canary.no_equivalent_pointwisePi_indexedFamily
#print axioms Canary.dependent_product_variance_boundary

end Mettapedia.TypeTheory.CategoryIndexedFamilyTypeFormers
