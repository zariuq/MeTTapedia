import Mettapedia.TypeTheory.CategoryIndexedFamilyTypeFormers

/-!
# Thin descent and category-indexed dependent type formers

A category-indexed family descends to proposition-truncated reachability
exactly when parallel context morphisms act identically.  This module proves
how that criterion interacts with the checked dependent type formers.

Parallel invariance is stable under substitution.  It is also stable under
dependent sums when both the domain family and the dependent codomain are
parallel invariant.  Fibrewise extensional identity is always parallel
invariant because its witness fibres are subsingletons, even when the ambient
data family retains route-sensitive information.

The corresponding descent results are derived through the established exact
criterion `ThinDescent.nonempty_iff_parallelInvariant`; no second erasure
interface is introduced.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.CategoryIndexedFamilyThinDescentTypeFormers

open CategoryTheory
open Mettapedia.TypeTheory.CategoryIndexedFamilyCwf
open Mettapedia.TypeTheory.CategoryIndexedFamilyTypeFormers

universe u

/-! ## General closure laws -/

/-- Pullback along a context functor preserves insensitivity to parallel
route identity. -/
theorem parallelInvariant_reindex
    {source target : Context.{u}} {family : IndexedFamily target}
    (invariant : ParallelInvariant family)
    (substitution : ContextHom source target) :
    ParallelInvariant (reindexFamily family substitution) := by
  intro first last left right value
  exact invariant (substitution.map left) (substitution.map right) value

/-- Consequently, every thin-descending family remains thin-descending after
arbitrary context substitution. -/
theorem thinDescent_reindex
    {source target : Context.{u}} {family : IndexedFamily target}
    (descent : ThinDescent family) (substitution : ContextHom source target) :
    Nonempty (ThinDescent (reindexFamily family substitution)) :=
  (ThinDescent.nonempty_iff_parallelInvariant _).2
    (parallelInvariant_reindex descent.parallelInvariant substitution)

/-- Equality of nested total-space objects implies equality of the
corresponding dependent-pair values in one base fibre. -/
private theorem sigmaValue_eq_of_nestedElement_eq
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

/-- Dependent summation preserves parallel invariance when both its domain
and its dependent codomain are parallel invariant. -/
theorem parallelInvariant_sigma
    {context : Context.{u}} {domain : IndexedFamily context}
    {codomain : IndexedFamily (extend context domain)}
    (domainInvariant : ParallelInvariant domain)
    (codomainInvariant : ParallelInvariant codomain) :
    ParallelInvariant (sigmaFamily domain codomain) := by
  intro source target left right value
  rcases value with ⟨argument, result⟩
  let leftPoint : domain.Elements :=
    ⟨target, domain.map left argument⟩
  let rightPoint : domain.Elements :=
    ⟨target, domain.map right argument⟩
  have argumentEquality :
      domain.map left argument = domain.map right argument :=
    domainInvariant left right argument
  have pointEquality : leftPoint = rightPoint := by
    apply Functor.Elements.ext leftPoint rightPoint rfl
    simpa [leftPoint, rightPoint] using argumentEquality
  let leftLift := elementLift domain left argument
  let rightLift := elementLift domain right argument
  have resultEquality :
      codomain.map (eqToHom pointEquality)
          (codomain.map leftLift result) =
        codomain.map rightLift result := by
    calc
      _ = codomain.map (leftLift ≫ eqToHom pointEquality) result :=
        (codomain.map_comp_apply leftLift (eqToHom pointEquality) result).symm
      _ = codomain.map rightLift result :=
        codomainInvariant (leftLift ≫ eqToHom pointEquality) rightLift result
  have nestedEquality :
      (⟨leftPoint, codomain.map leftLift result⟩ : codomain.Elements) =
        ⟨rightPoint, codomain.map rightLift result⟩ :=
    Functor.Elements.ext _ _ pointEquality resultEquality
  exact sigmaValue_eq_of_nestedElement_eq nestedEquality

/-- The corresponding dependent sum admits thin descent. -/
theorem thinDescent_sigma
    {context : Context.{u}} {domain : IndexedFamily context}
    {codomain : IndexedFamily (extend context domain)}
    (domainDescent : ThinDescent domain)
    (codomainDescent : ThinDescent codomain) :
    Nonempty (ThinDescent (sigmaFamily domain codomain)) :=
  (ThinDescent.nonempty_iff_parallelInvariant _).2
    (parallelInvariant_sigma domainDescent.parallelInvariant
      codomainDescent.parallelInvariant)

/-- Fibrewise extensional equality cannot distinguish parallel context
routes: every target witness fibre is a subsingleton. -/
theorem parallelInvariant_identity
    {context : Context.{u}} (family : IndexedFamily context)
    (left right : IndexedSection family) :
    ParallelInvariant (identityFamily family left right) := by
  intro source target first second witness
  exact (liftedEqualitySubsingleton _ _).allEq _ _

/-- Every selected fibrewise extensional identity family descends to thin
reachability, independently of whether its ambient data family descends. -/
theorem thinDescent_identity
    {context : Context.{u}} (family : IndexedFamily context)
    (left right : IndexedSection family) :
    Nonempty (ThinDescent (identityFamily family left right)) :=
  (ThinDescent.nonempty_iff_parallelInvariant _).2
    (parallelInvariant_identity family left right)

/-! ## Restricted dependent products -/

/-- Parallel base routes have the same selected inverse action whenever the
domain family is parallel invariant. -/
theorem inverse_eq_of_parallelInvariant
    {context : Context.{u}} {domain : IndexedFamily context}
    (domainAction : FibrewiseEquivalenceAction domain)
    (domainInvariant : ParallelInvariant domain)
    {source target : context} (left right : source ⟶ target)
    (targetValue : domain.obj target) :
    domainAction.inverse left targetValue =
      domainAction.inverse right targetValue := by
  apply (domainAction.equivalence right).injective
  rw [domainAction.apply_eq_map, domainAction.apply_eq_map]
  calc
    domain.map right (domainAction.inverse left targetValue) =
        domain.map left (domainAction.inverse left targetValue) :=
      domainInvariant right left _
    _ = targetValue := domainAction.map_inverse left targetValue
    _ = domain.map right (domainAction.inverse right targetValue) :=
      (domainAction.map_inverse right targetValue).symm

/-- The invertible-domain dependent product preserves parallel invariance
when both its domain and dependent codomain are parallel invariant. -/
theorem parallelInvariant_pi
    {context : Context.{u}} {domain : IndexedFamily context}
    (domainAction : FibrewiseEquivalenceAction domain)
    {codomain : IndexedFamily (extend context domain)}
    (domainInvariant : ParallelInvariant domain)
    (codomainInvariant : ParallelInvariant codomain) :
    ParallelInvariant (piFamily domain domainAction codomain) := by
  intro source target left right function
  apply funext
  intro targetArgument
  let leftInverse := domainAction.inverse left targetArgument
  let rightInverse := domainAction.inverse right targetArgument
  have inverseEquality : leftInverse = rightInverse :=
    inverse_eq_of_parallelInvariant
    domainAction domainInvariant left right targetArgument
  let leftPoint : domain.Elements := ⟨source, leftInverse⟩
  let rightPoint : domain.Elements := ⟨source, rightInverse⟩
  let pointEquality : leftPoint = rightPoint :=
    congrArg
      (fun argument =>
        (show domain.Elements from ⟨source, argument⟩))
      inverseEquality
  have functionEquality :
      codomain.map (eqToHom pointEquality) (function leftInverse) =
        function rightInverse :=
    map_eqToHom_apply_of_heq codomain pointEquality
      (congr_arg_heq function inverseEquality)
  let leftLift :=
    equivalenceElementLift domainAction left targetArgument
  let rightLift :=
    equivalenceElementLift domainAction right targetArgument
  calc
    codomain.map leftLift (function leftInverse) =
        codomain.map (eqToHom pointEquality ≫ rightLift)
          (function leftInverse) :=
      codomainInvariant leftLift (eqToHom pointEquality ≫ rightLift) _
    _ = codomain.map rightLift
          (codomain.map (eqToHom pointEquality) (function leftInverse)) :=
      codomain.map_comp_apply (eqToHom pointEquality) rightLift _
    _ = codomain.map rightLift (function rightInverse) := by
      rw [functionEquality]

/-- The corresponding restricted dependent product admits thin descent. -/
theorem thinDescent_pi
    {context : Context.{u}} {domain : IndexedFamily context}
    (domainAction : FibrewiseEquivalenceAction domain)
    {codomain : IndexedFamily (extend context domain)}
    (domainDescent : ThinDescent domain)
    (codomainDescent : ThinDescent codomain) :
    Nonempty (ThinDescent (piFamily domain domainAction codomain)) :=
  (ThinDescent.nonempty_iff_parallelInvariant _).2
    (parallelInvariant_pi domainAction domainDescent.parallelInvariant
      codomainDescent.parallelInvariant)

/-! ## Route-sensitive data with a thin equality judgment -/

namespace Canary

open Mettapedia.TypeTheory.CategoryIndexedFamilyCwf.Canary

/-- The two-loop action on optional Booleans fixes `none` but flips every
inhabited Boolean value along the nontrivial loop. -/
def fixedPointToggleAction (route : Bool) : Option Bool → Option Bool :=
  fun value => value.map (xor route)

/-- A route-sensitive family which nevertheless has a global fixed point. -/
def fixedPointToggleFamily : IndexedFamily toggleContext where
  obj _ := Option Bool
  map route := TypeCat.ofHom (fixedPointToggleAction route)
  map_id point := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext value
    cases value with
    | none => rfl
    | some bit => cases bit <;> rfl
  map_comp earlier later := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext value
    cases earlier <;> cases later <;> cases value with
    | none => rfl
    | some bit => cases bit <;> rfl

/-- The absent value is fixed by both loops and therefore forms a natural
section. -/
def noneSection : IndexedSection fixedPointToggleFamily :=
  ⟨fun _ => none, fun route => by cases route <;> rfl⟩

/-- The inhabited Boolean value still distinguishes the two parallel loops. -/
theorem fixedPointToggleFamily_distinguishes_routes :
    fixedPointToggleFamily.map stayRoute (some false) ≠
      fixedPointToggleFamily.map flipRoute (some false) := by
  change some false ≠ some true
  simp

/-- Hence the data family itself does not descend to thin reachability. -/
theorem fixedPointToggleFamily_does_not_descend :
    ¬ Nonempty (ThinDescent fixedPointToggleFamily) := by
  intro descent
  have invariant : ParallelInvariant fixedPointToggleFamily :=
    (ThinDescent.nonempty_iff_parallelInvariant
      fixedPointToggleFamily).1 descent
  exact fixedPointToggleFamily_distinguishes_routes
    (invariant (source := TogglePoint.star) (target := TogglePoint.star)
      stayRoute flipRoute (some false))

/-- A constant dependent codomain over the route-sensitive data family. -/
def unitCodomain :
    IndexedFamily (extend toggleContext fixedPointToggleFamily) :=
  (Functor.const fixedPointToggleFamily.Elements).obj PUnit

/-- Adding a trivial dependent component does not erase the route-sensitive
first component of a dependent sum. -/
theorem fixedPointSigma_distinguishes_routes :
    (sigmaFamily fixedPointToggleFamily unitCodomain).map stayRoute
        ⟨some false, PUnit.unit⟩ ≠
      (sigmaFamily fixedPointToggleFamily unitCodomain).map flipRoute
        ⟨some false, PUnit.unit⟩ := by
  intro equality
  have firstEquality := congrArg Sigma.fst equality
  change some false = some true at firstEquality
  simp at firstEquality

/-- Consequently, dependent summation does not manufacture thin descent when
its domain hypothesis is absent. -/
theorem fixedPointSigma_does_not_descend :
    ¬ Nonempty
      (ThinDescent (sigmaFamily fixedPointToggleFamily unitCodomain)) := by
  intro descent
  have invariant :
      ParallelInvariant
        (sigmaFamily fixedPointToggleFamily unitCodomain) :=
    (ThinDescent.nonempty_iff_parallelInvariant _).1 descent
  exact fixedPointSigma_distinguishes_routes
    (invariant (source := TogglePoint.star) (target := TogglePoint.star)
      stayRoute flipRoute ⟨some false, PUnit.unit⟩)

/-- The equality judgment of the fixed term does descend even though its
ambient data family does not. -/
theorem fixedPointIdentity_descends :
    Nonempty
      (ThinDescent
        (identityFamily fixedPointToggleFamily noneSection noneSection)) :=
  thinDescent_identity fixedPointToggleFamily noneSection noneSection

/-- Route-sensitive data and a route-insensitive equality judgment coexist. -/
theorem data_and_identity_descent_separate :
    (¬ Nonempty (ThinDescent fixedPointToggleFamily)) ∧
      Nonempty
        (ThinDescent
          (identityFamily fixedPointToggleFamily noneSection noneSection)) :=
  ⟨fixedPointToggleFamily_does_not_descend,
    fixedPointIdentity_descends⟩

/-- The complete canary: route-sensitive data and its trivial dependent sum
remain non-descending, while the selected equality judgment descends. -/
theorem sigma_and_identity_descent_separate :
    (¬ Nonempty (ThinDescent fixedPointToggleFamily)) ∧
      (¬ Nonempty
        (ThinDescent (sigmaFamily fixedPointToggleFamily unitCodomain))) ∧
      Nonempty
        (ThinDescent
          (identityFamily fixedPointToggleFamily noneSection noneSection)) :=
  ⟨fixedPointToggleFamily_does_not_descend,
    fixedPointSigma_does_not_descend,
    fixedPointIdentity_descends⟩

end Canary

/-! ## Axiom audit -/

#print axioms parallelInvariant_reindex
#print axioms thinDescent_reindex
#print axioms parallelInvariant_sigma
#print axioms thinDescent_sigma
#print axioms parallelInvariant_identity
#print axioms thinDescent_identity
#print axioms inverse_eq_of_parallelInvariant
#print axioms parallelInvariant_pi
#print axioms thinDescent_pi
#print axioms Canary.fixedPointToggleFamily_does_not_descend
#print axioms Canary.fixedPointSigma_does_not_descend
#print axioms Canary.fixedPointIdentity_descends
#print axioms Canary.data_and_identity_descent_separate
#print axioms Canary.sigma_and_identity_descent_separate

end Mettapedia.TypeTheory.CategoryIndexedFamilyThinDescentTypeFormers
