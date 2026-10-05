import Mettapedia.TypeTheory.ContextualSmallFamilyPowers

/-!
# Independent substitution of small complete-future powers

An arbitrary wider parameter map gives an independently formed power of
the reindexed family. Its full future predicates have constructed inverse
natural comparisons with the reindexed original power. Both whole laws,
member interpretation and compatible sections are preserved.

The parameter's actual value and each actual future arrow remain retained.
No injectivity, selected receipt inverse or native equality reflection is
required for this substitution comparison.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualSmallFamilyPowerCoherence

open _root_.CategoryTheory ContextualWitnessCover ContextualSmallFamilyPowers
open ContextualSmallFamilyTypeFormers ContextualSmallFamilyTypeFormerCoherence
open MaterialSets.Hypersets.CoveredFuturePowerClassifier
open MaterialSets.Hypersets.PowerClassPresheafBaseChange

universe u v w
variable {D : Type u} [Category.{u} D] {base : D ⥤ Type v} {other : D ⥤ Type w}
variable (change : NaturalHom other base) (domain : base.Elements ⥤ Type u)

def predicateTransport {E : Type u} [Category.{u} E] {first second : E ⥤ Type u} (same : first = second) :
    StablePredicate first ≃ StablePredicate second :=
  ContextualSmallFamilyUniverse.typeEqualityEquiv (congrArg StablePredicate same)

theorem predicateTransport_holds {E : Type u} [Category.{u} E] {first second : E ⥤ Type u}
    (same : first = second) (predicate : StablePredicate first) (argument : second.Elements) :
    (predicateTransport same predicate).holds argument ↔
      predicate.holds ((Cat.elementsTransport same.symm).obj argument) := by
  cases same
  rfl

def powerComparison (point : other.Elements) :
    PowerAt domain ((ContextualSmallFamilyUniverse.elementMap change).obj point) ≃
      PowerAt (domainUnder change domain) point :=
  predicateTransport (futureDomain_change change domain point).symm

theorem powerComparison_holds (point : other.Elements)
    (predicate : PowerAt domain ((ContextualSmallFamilyUniverse.elementMap change).obj point))
    (argument : (futureDomain (domainUnder change domain) point).Elements) :
    (powerComparison change domain point predicate).holds argument ↔
      predicate.holds ((futureArgumentChange change domain point).obj argument) :=
  predicateTransport_holds (futureDomain_change change domain point).symm predicate argument

def powerSubstitution :
    NatTrans (ContextualSmallFamilyUniverse.substitutedFamily (power domain) change)
      (power (domainUnder change domain)) where
  app point := TypeCat.ofHom (powerComparison change domain point)
  naturality first second step := by
    apply ConcreteCategory.hom_ext
    intro predicate
    apply StablePredicate.ext
    intro argument
    exact (powerComparison_holds change domain second
      (powerMap domain ((ContextualSmallFamilyUniverse.elementMap change).map step) predicate) argument).trans
        ((Iff.of_eq (congrArg predicate.holds (futureArgumentChange_prefix change domain step argument))).trans
          (powerComparison_holds change domain first predicate
            ((prefixArguments (domainUnder change domain) step).obj argument)).symm)

def powerSubstitutionInverse :
    NatTrans (power (domainUnder change domain))
      (ContextualSmallFamilyUniverse.substitutedFamily (power domain) change) where
  app point := TypeCat.ofHom (powerComparison change domain point).symm
  naturality first second step := by
    apply ConcreteCategory.hom_ext
    intro predicate
    change (powerComparison change domain second).symm (powerMap (domainUnder change domain) step predicate) =
      powerMap domain ((ContextualSmallFamilyUniverse.elementMap change).map step)
        ((powerComparison change domain first).symm predicate)
    apply (powerComparison change domain second).injective
    have natural := congrArg (fun map => map ((powerComparison change domain first).symm predicate))
      ((powerSubstitution change domain).naturality step)
    exact ((powerComparison change domain second).apply_symm_apply _).trans
      (natural.trans (congrArg (powerMap (domainUnder change domain) step)
        ((powerComparison change domain first).apply_symm_apply predicate))).symm

theorem substitution_left :
    composeNat (powerSubstitution change domain) (powerSubstitutionInverse change domain) =
      identityNat (ContextualSmallFamilyUniverse.substitutedFamily (power domain) change) := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  exact (powerComparison change domain point).symm_apply_apply

theorem substitution_right :
    composeNat (powerSubstitutionInverse change domain) (powerSubstitution change domain) =
      identityNat (power (domainUnder change domain)) := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  exact (powerComparison change domain point).apply_symm_apply

theorem member_substitution (point : other.Elements)
    (predicate : PowerAt domain ((ContextualSmallFamilyUniverse.elementMap change).obj point))
    (argument : (domainUnder change domain).obj point) :
    member (domainUnder change domain) point argument (powerComparison change domain point predicate) ↔
      member domain ((ContextualSmallFamilyUniverse.elementMap change).obj point) argument predicate :=
  (powerComparison_holds change domain point predicate
    (currentArgument (domainUnder change domain) point argument)).trans
      (Iff.of_eq (congrArg predicate.holds (futureArgumentChange_current change domain point argument)))

def wholeSectionComparison :
    (ContextualSmallFamilyUniverse.substitutedFamily (power domain) change).sections ≃
      (power (domainUnder change domain)).sections where
  toFun := mapSectionNat (powerSubstitution change domain)
  invFun := mapSectionNat (powerSubstitutionInverse change domain)
  left_inv term := Subtype.ext (funext fun point => (powerComparison change domain point).symm_apply_apply (term.val point))
  right_inv term := Subtype.ext (funext fun point => (powerComparison change domain point).apply_symm_apply (term.val point))

end Mettapedia.TypeTheory.ContextualSmallFamilyPowerCoherence
