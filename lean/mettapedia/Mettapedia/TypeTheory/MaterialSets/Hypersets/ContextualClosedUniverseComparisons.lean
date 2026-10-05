import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualClosedUniverseCodes
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGeneratedWBaseChange

/-!
# Decoder comparisons for substituted closed codes

Transported Pi labels preserve the actual material carrier and member values.
Fresh formation after substitution has a genuine semantic comparison. W uses
the full natural-tree equivalence over the actual comprehension square; fresh
world and arrow labels need not preserve its material graph values.

No comparison in this file is an equation identifying formation codes merely
because their carriers or semantic families agree.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualClosedUniverseComparisons

open CategoryTheory
open ContextualGeneratedUniverse (LabelledContext MaterialFamily)
open ContextualClosedUniverseCodes

universe u
variable {C : Type u} [Category.{u} C]
variable (seeds : (context : LabelledContext C) → Type (u + 1))
variable (seedModel : (context : LabelledContext C) → seeds context → MaterialFamily context)
variable (arrows : (first second : Cᵒᵖ) → ArgumentCoding (first ⟶ second))
variable {context other : LabelledContext C}
variable (change : NatTrans other.base context.base)
variable (domain : Code seeds seedModel arrows context)
variable (body : Code seeds seedModel arrows (decodeFamily seeds seedModel arrows domain).extension)

/-- Exact deliberately transported labels give the full future Pi
comparison. This is not a universal fresh-label material equality. -/
def piComparison (point : other.base.Elements) :
    (decodeFamily seeds seedModel arrows (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change (pi seeds seedModel arrows domain body))).family.obj point ≃
      (decodeFamily seeds seedModel arrows (piUnder seeds seedModel arrows change domain body)).family.obj point := by
  simpa only [ContextualClosedUniverseCodes.pi, ContextualClosedUniverseCodes.piUnder, decode_reindex, decode_binary, decode_under, materialBinary, materialUnder] using
    ContextualGeneratedUniverse.MaterialFamily.piComparison
      (decodeFamily seeds seedModel arrows domain) (decodeFamily seeds seedModel arrows body) arrows change point

theorem piComparison_value (point : other.base.Elements)
    (term : (decodeFamily seeds seedModel arrows
      (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change (pi seeds seedModel arrows domain body))).family.obj point) :
    ((decodeFamily seeds seedModel arrows (piUnder seeds seedModel arrows change domain body)).model point).value
      (piComparison seeds seedModel arrows change domain body point term) =
        ((decodeFamily seeds seedModel arrows
          (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change (pi seeds seedModel arrows domain body))).model point).value term := by
  revert body
  refine Quotient.inductionOn domain ?_
  intro raw body
  refine Quotient.inductionOn body ?_
  intro rawBody term
  exact raw.1.piUnder_value rawBody.1 arrows change point term

theorem piUnder_carrier (point : other.base.Elements) :
    ((decodeFamily seeds seedModel arrows (piUnder seeds seedModel arrows change domain body)).model point).carrier =
      ((decodeFamily seeds seedModel arrows
        (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change (pi seeds seedModel arrows domain body))).model point).carrier := by
  revert body
  refine Quotient.inductionOn domain ?_
  intro raw body
  refine Quotient.inductionOn body ?_
  intro rawBody
  exact raw.1.piUnder_carrier rawBody.1 arrows change point


theorem piComparison_natural {point next : other.base.Elements} (step : point ⟶ next)
    (term : (decodeFamily seeds seedModel arrows
      (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change (pi seeds seedModel arrows domain body))).family.obj point) :
    piComparison seeds seedModel arrows change domain body next
      ((decodeFamily seeds seedModel arrows
        (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change (pi seeds seedModel arrows domain body))).family.map step term) =
      (decodeFamily seeds seedModel arrows (piUnder seeds seedModel arrows change domain body)).family.map step
        (piComparison seeds seedModel arrows change domain body point term) := by
  revert body
  refine Quotient.inductionOn domain ?_
  intro raw body
  refine Quotient.inductionOn body ?_
  intro rawBody term
  exact congrArg (fun operation => operation term)
    ((PowerClassPresheafBaseChange.piBaseChange change raw.1.family
      (PowerClassPresheafProducts.indexedBody raw.1.family rawBody.1.family)).naturality step)

def piMember (point : other.base.Elements)
    (member : {value : HSet.{u} // value ∈ ((decodeFamily seeds seedModel arrows
      (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change (pi seeds seedModel arrows domain body))).model point).carrier}) :
    {value : HSet.{u} // value ∈
      ((decodeFamily seeds seedModel arrows (piUnder seeds seedModel arrows change domain body)).model point).carrier} :=
  ⟨member.1, (piUnder_carrier seeds seedModel arrows change domain body point).symm ▸ member.2⟩

theorem piMember_value (point : other.base.Elements)
    (member : {value : HSet.{u} // value ∈ ((decodeFamily seeds seedModel arrows
      (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change (pi seeds seedModel arrows domain body))).model point).carrier}) :
    (piMember seeds seedModel arrows change domain body point member).val = member.val := rfl

theorem piMember_decode (point : other.base.Elements)
    (member : {value : HSet.{u} // value ∈ ((decodeFamily seeds seedModel arrows
      (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change (pi seeds seedModel arrows domain body))).model point).carrier}) :
    ((decodeFamily seeds seedModel arrows (piUnder seeds seedModel arrows change domain body)).model point).decode
      (piMember seeds seedModel arrows change domain body point member) =
        piComparison seeds seedModel arrows change domain body point
          (((decodeFamily seeds seedModel arrows
            (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change (pi seeds seedModel arrows domain body))).model point).decode member) := by
  apply ((decodeFamily seeds seedModel arrows (piUnder seeds seedModel arrows change domain body)).model point).value_injective
  exact (((decodeFamily seeds seedModel arrows (piUnder seeds seedModel arrows change domain body)).model point).value_decode
    (piMember seeds seedModel arrows change domain body point member)).trans
    ((((decodeFamily seeds seedModel arrows
      (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change (pi seeds seedModel arrows domain body))).model point).value_decode member).symm.trans
      (piComparison_value seeds seedModel arrows change domain body point _).symm)

theorem sigmaFormation :
    (decodeFamily seeds seedModel arrows
      (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change (sigma seeds seedModel arrows domain body))).family =
        (decodeFamily seeds seedModel arrows (sigmaUnder seeds seedModel arrows change domain body)).family := by
  revert body
  refine Quotient.inductionOn domain ?_
  intro raw body
  refine Quotient.inductionOn body ?_
  intro rawBody
  exact raw.1.sigmaUnder_formation rawBody.1 change

def sigmaTerm (point : other.base.Elements)
    (term : (decodeFamily seeds seedModel arrows
      (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change (sigma seeds seedModel arrows domain body))).family.obj point) :
    (decodeFamily seeds seedModel arrows (sigmaUnder seeds seedModel arrows change domain body)).family.obj point :=
  cast (congrArg (fun family => family.obj point) (sigmaFormation seeds seedModel arrows change domain body)) term

theorem sigmaTerm_value (point : other.base.Elements)
    (term : (decodeFamily seeds seedModel arrows
      (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change (sigma seeds seedModel arrows domain body))).family.obj point) :
    ((decodeFamily seeds seedModel arrows (sigmaUnder seeds seedModel arrows change domain body)).model point).value
      (sigmaTerm seeds seedModel arrows change domain body point term) =
        ((decodeFamily seeds seedModel arrows
          (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change (sigma seeds seedModel arrows domain body))).model point).value term := by
  revert body
  refine Quotient.inductionOn domain ?_
  intro raw body
  refine Quotient.inductionOn body ?_
  intro rawBody term
  exact raw.1.sigmaUnder_value rawBody.1 change point term

/-- Base change of a dependent body uses the constructed comprehension
lift. It keeps the actual argument, not merely an inhabitedness predicate. -/
def comprehensionChange : NatTrans
    (decodeFamily seeds seedModel arrows (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change domain)).extension.base
    (decodeFamily seeds seedModel arrows domain).extension.base := by
  rw [decode_reindex]
  exact PowerClassPresheafBaseChange.comprehensionChange change (decodeFamily seeds seedModel arrows domain).family

def bodyReindex : Code seeds seedModel arrows
    (decodeFamily seeds seedModel arrows (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change domain)).extension :=
  ContextualClosedUniverseCodes.reindex seeds seedModel arrows (comprehensionChange seeds seedModel arrows change domain) body

def freshW : Code seeds seedModel arrows other :=
  w seeds seedModel arrows (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change domain)
    (bodyReindex seeds seedModel arrows change domain body)

theorem freshW_family :
    (decodeFamily seeds seedModel arrows (freshW seeds seedModel arrows change domain body)).family =
      ContextualWTypes.family
        (PowerClassPresheafProducts.reindex change (decodeFamily seeds seedModel arrows domain).family)
        (PowerClassPresheafBaseChange.bodyReindex change (decodeFamily seeds seedModel arrows domain).family
          (PowerClassPresheafProducts.indexedBody (decodeFamily seeds seedModel arrows domain).family
            (decodeFamily seeds seedModel arrows body).family)) := by
  revert body
  refine Quotient.inductionOn domain ?_
  intro raw body
  refine Quotient.inductionOn body ?_
  intro rawBody
  exact congrArg (ContextualWTypes.family (PowerClassPresheafProducts.reindex change raw.1.family))
    (PowerClassPresheafBaseChange.indexedBody_reindex change raw.1.family rawBody.1.family)


private def functorObjectEquiv {D : Type u} [Category.{u} D] {first second : D ⥤ Type u}
    (same : first = second) (point : D) : first.obj point ≃ second.obj point :=
  Mettapedia.TypeTheory.DependentFamilySectionDescent.equalityEquiv (congrArg (fun family => family.obj point) same)

private theorem functorObjectEquiv_natural {D : Type u} [Category.{u} D] {first second : D ⥤ Type u}
    (same : first = second) {point next : D} (step : point ⟶ next) (term : first.obj point) :
    functorObjectEquiv same next (first.map step term) = second.map step (functorObjectEquiv same point term) := by
  cases same
  rfl


def freshPi : Code seeds seedModel arrows other :=
  pi seeds seedModel arrows (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change domain)
    (bodyReindex seeds seedModel arrows change domain body)

theorem freshPi_family :
    (decodeFamily seeds seedModel arrows (freshPi seeds seedModel arrows change domain body)).family =
      (decodeFamily seeds seedModel arrows (piUnder seeds seedModel arrows change domain body)).family := by
  revert body
  refine Quotient.inductionOn domain ?_
  intro raw body
  refine Quotient.inductionOn body ?_
  intro rawBody
  exact PowerClassPresheafBaseChange.pi_comprehension_baseChange change raw.1.family rawBody.1.family

/-- Fresh Pi is a genuine full-future semantic comparison. Its material
function graph uses the fresh labels, which are not assumed equal. -/
def piFreshComparison (point : other.base.Elements) :
    (decodeFamily seeds seedModel arrows
      (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change (pi seeds seedModel arrows domain body))).family.obj point ≃
        (decodeFamily seeds seedModel arrows (freshPi seeds seedModel arrows change domain body)).family.obj point :=
  (piComparison seeds seedModel arrows change domain body point).trans
    (functorObjectEquiv (freshPi_family seeds seedModel arrows change domain body).symm point)

theorem piFreshComparison_natural {point next : other.base.Elements} (step : point ⟶ next)
    (term : (decodeFamily seeds seedModel arrows
      (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change (pi seeds seedModel arrows domain body))).family.obj point) :
    piFreshComparison seeds seedModel arrows change domain body next
      ((decodeFamily seeds seedModel arrows
        (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change (pi seeds seedModel arrows domain body))).family.map step term) =
      (decodeFamily seeds seedModel arrows (freshPi seeds seedModel arrows change domain body)).family.map step
        (piFreshComparison seeds seedModel arrows change domain body point term) := by
  dsimp only [piFreshComparison, Equiv.trans_apply]
  rw [piComparison_natural]
  exact functorObjectEquiv_natural (freshPi_family seeds seedModel arrows change domain body).symm step _

def piFreshMemberEquiv (point : other.base.Elements) :
    {value : HSet.{u} // value ∈ ((decodeFamily seeds seedModel arrows
      (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change (pi seeds seedModel arrows domain body))).model point).carrier} ≃
    {value : HSet.{u} // value ∈ ((decodeFamily seeds seedModel arrows
      (freshPi seeds seedModel arrows change domain body)).model point).carrier} :=
  (((decodeFamily seeds seedModel arrows
    (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change (pi seeds seedModel arrows domain body))).model point).decode.trans
      (piFreshComparison seeds seedModel arrows change domain body point)).trans
        ((decodeFamily seeds seedModel arrows (freshPi seeds seedModel arrows change domain body)).model point).decode.symm

theorem piFreshMember_decode (point : other.base.Elements)
    (member : {value : HSet.{u} // value ∈ ((decodeFamily seeds seedModel arrows
      (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change (pi seeds seedModel arrows domain body))).model point).carrier}) :
    ((decodeFamily seeds seedModel arrows (freshPi seeds seedModel arrows change domain body)).model point).decode
      (piFreshMemberEquiv seeds seedModel arrows change domain body point member) =
        piFreshComparison seeds seedModel arrows change domain body point
          (((decodeFamily seeds seedModel arrows
            (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change (pi seeds seedModel arrows domain body))).model point).decode member) :=
  ((decodeFamily seeds seedModel arrows (freshPi seeds seedModel arrows change domain body)).model point).decode.apply_symm_apply _


theorem piFreshMember_natural {point next : other.base.Elements} (step : point ⟶ next)
    (member : {value : HSet.{u} // value ∈ ((decodeFamily seeds seedModel arrows
      (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change (pi seeds seedModel arrows domain body))).model point).carrier}) :
    piFreshMemberEquiv seeds seedModel arrows change domain body next
      ((decodeFamily seeds seedModel arrows
        (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change (pi seeds seedModel arrows domain body))).memberRestriction step member) =
      (decodeFamily seeds seedModel arrows (freshPi seeds seedModel arrows change domain body)).memberRestriction step
        (piFreshMemberEquiv seeds seedModel arrows change domain body point member) := by
  let source := decodeFamily seeds seedModel arrows
    (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change (pi seeds seedModel arrows domain body))
  let target := decodeFamily seeds seedModel arrows (freshPi seeds seedModel arrows change domain body)
  apply (target.model next).decode.injective
  exact (piFreshMember_decode seeds seedModel arrows change domain body next _).trans
    ((congrArg (piFreshComparison seeds seedModel arrows change domain body next)
      (source.memberRestriction_decode step member)).trans
      ((piFreshComparison_natural seeds seedModel arrows change domain body step _).trans
        ((congrArg (target.family.map step)
          (piFreshMember_decode seeds seedModel arrows change domain body point member).symm).trans
          (target.memberRestriction_decode step
            (piFreshMemberEquiv seeds seedModel arrows change domain body point member)).symm)))

def freshSigma : Code seeds seedModel arrows other :=
  sigma seeds seedModel arrows (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change domain)
    (bodyReindex seeds seedModel arrows change domain body)

theorem freshSigma_family :
    (decodeFamily seeds seedModel arrows
      (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change (sigma seeds seedModel arrows domain body))).family =
        (decodeFamily seeds seedModel arrows (freshSigma seeds seedModel arrows change domain body)).family := by
  revert body
  refine Quotient.inductionOn domain ?_
  intro raw body
  refine Quotient.inductionOn body ?_
  intro rawBody
  exact PowerClassPresheafBaseChange.sigma_comprehension_baseChange change raw.1.family rawBody.1.family

def sigmaFreshTerm (point : other.base.Elements)
    (term : (decodeFamily seeds seedModel arrows
      (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change (sigma seeds seedModel arrows domain body))).family.obj point) :
    (decodeFamily seeds seedModel arrows (freshSigma seeds seedModel arrows change domain body)).family.obj point :=
  functorObjectEquiv (freshSigma_family seeds seedModel arrows change domain body) point term

theorem sigmaFreshTerm_value (point : other.base.Elements)
    (term : (decodeFamily seeds seedModel arrows
      (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change (sigma seeds seedModel arrows domain body))).family.obj point) :
    ((decodeFamily seeds seedModel arrows (freshSigma seeds seedModel arrows change domain body)).model point).value
      (sigmaFreshTerm seeds seedModel arrows change domain body point term) =
        ((decodeFamily seeds seedModel arrows
          (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change (sigma seeds seedModel arrows domain body))).model point).value term := by
  revert body
  refine Quotient.inductionOn domain ?_
  intro raw body
  refine Quotient.inductionOn body ?_
  intro rawBody term
  rfl



theorem sigmaFreshTerm_natural {point next : other.base.Elements} (step : point ⟶ next)
    (term : (decodeFamily seeds seedModel arrows
      (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change (sigma seeds seedModel arrows domain body))).family.obj point) :
    sigmaFreshTerm seeds seedModel arrows change domain body next
      ((decodeFamily seeds seedModel arrows
        (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change (sigma seeds seedModel arrows domain body))).family.map step term) =
      (decodeFamily seeds seedModel arrows (freshSigma seeds seedModel arrows change domain body)).family.map step
        (sigmaFreshTerm seeds seedModel arrows change domain body point term) :=
  functorObjectEquiv_natural (freshSigma_family seeds seedModel arrows change domain body) step term

def sectionReindex (sectionValue : (decodeFamily seeds seedModel arrows domain).family.sections) :
    (decodeFamily seeds seedModel arrows (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change domain)).family.sections := by
  rw [decode_reindex]
  exact PowerClassPresheafProducts.reindexSection change (decodeFamily seeds seedModel arrows domain).family sectionValue

def freshIdentity (left right : (decodeFamily seeds seedModel arrows domain).family.sections) :
    Code seeds seedModel arrows other :=
  ContextualClosedUniverseCodes.identity seeds seedModel arrows
    (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change domain)
    (sectionReindex seeds seedModel arrows change domain left)
    (sectionReindex seeds seedModel arrows change domain right)

theorem freshIdentity_family (left right : (decodeFamily seeds seedModel arrows domain).family.sections) :
    (decodeFamily seeds seedModel arrows (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change
      (ContextualClosedUniverseCodes.identity seeds seedModel arrows domain left right))).family =
        (decodeFamily seeds seedModel arrows (freshIdentity seeds seedModel arrows change domain left right)).family := by
  revert left right
  refine Quotient.inductionOn domain ?_
  intro raw left right
  exact raw.1.identity_reindex change left right

def identityFreshTerm (left right : (decodeFamily seeds seedModel arrows domain).family.sections)
    (point : other.base.Elements)
    (term : (decodeFamily seeds seedModel arrows (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change
      (ContextualClosedUniverseCodes.identity seeds seedModel arrows domain left right))).family.obj point) :
    (decodeFamily seeds seedModel arrows (freshIdentity seeds seedModel arrows change domain left right)).family.obj point :=
  functorObjectEquiv (freshIdentity_family seeds seedModel arrows change domain left right) point term

theorem identityFreshTerm_value (left right : (decodeFamily seeds seedModel arrows domain).family.sections)
    (point : other.base.Elements)
    (term : (decodeFamily seeds seedModel arrows (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change
      (ContextualClosedUniverseCodes.identity seeds seedModel arrows domain left right))).family.obj point) :
    ((decodeFamily seeds seedModel arrows (freshIdentity seeds seedModel arrows change domain left right)).model point).value
      (identityFreshTerm seeds seedModel arrows change domain left right point term) =
        ((decodeFamily seeds seedModel arrows (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change
          (ContextualClosedUniverseCodes.identity seeds seedModel arrows domain left right))).model point).value term := by
  revert left right
  refine Quotient.inductionOn domain ?_
  intro raw left right term
  rfl

theorem identityFreshTerm_natural (left right : (decodeFamily seeds seedModel arrows domain).family.sections)
    {point next : other.base.Elements} (step : point ⟶ next)
    (term : (decodeFamily seeds seedModel arrows (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change
      (ContextualClosedUniverseCodes.identity seeds seedModel arrows domain left right))).family.obj point) :
    identityFreshTerm seeds seedModel arrows change domain left right next
      ((decodeFamily seeds seedModel arrows (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change
        (ContextualClosedUniverseCodes.identity seeds seedModel arrows domain left right))).family.map step term) =
      (decodeFamily seeds seedModel arrows (freshIdentity seeds seedModel arrows change domain left right)).family.map step
        (identityFreshTerm seeds seedModel arrows change domain left right point term) :=
  functorObjectEquiv_natural (freshIdentity_family seeds seedModel arrows change domain left right) step term

theorem reindexedW_family :
    (decodeFamily seeds seedModel arrows
      (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change (w seeds seedModel arrows domain body))).family =
        (((decodeFamily seeds seedModel arrows domain).w (decodeFamily seeds seedModel arrows body) arrows).reindex change).family := by
  simp only [w, decode_reindex, decode_binary, materialBinary]

/-- Fresh W formation is compared semantically. Its material encodings use
the fresh target labels, so their values are deliberately not equated. -/
noncomputable def wFreshComparison (point : other.base.Elements) :
    (decodeFamily seeds seedModel arrows
      (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change (w seeds seedModel arrows domain body))).family.obj point ≃
        (decodeFamily seeds seedModel arrows (freshW seeds seedModel arrows change domain body)).family.obj point :=
  (functorObjectEquiv (reindexedW_family seeds seedModel arrows change domain body) point).trans
    ((ContextualGeneratedWBaseChange.wComparison
      (decodeFamily seeds seedModel arrows domain) (decodeFamily seeds seedModel arrows body) arrows change point).trans
        (functorObjectEquiv (freshW_family seeds seedModel arrows change domain body).symm point))

theorem wFreshComparison_natural {point next : other.base.Elements} (step : point ⟶ next)
    (tree : (decodeFamily seeds seedModel arrows
      (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change (w seeds seedModel arrows domain body))).family.obj point) :
    wFreshComparison seeds seedModel arrows change domain body next
      ((decodeFamily seeds seedModel arrows
        (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change (w seeds seedModel arrows domain body))).family.map step tree) =
      (decodeFamily seeds seedModel arrows (freshW seeds seedModel arrows change domain body)).family.map step
        (wFreshComparison seeds seedModel arrows change domain body point tree) := by
  dsimp only [wFreshComparison, Equiv.trans_apply]
  rw [functorObjectEquiv_natural]
  rw [ContextualGeneratedWBaseChange.wUnder_restriction]
  exact functorObjectEquiv_natural (freshW_family seeds seedModel arrows change domain body).symm step _

noncomputable def wFreshMemberEquiv (point : other.base.Elements) :
    {value : HSet.{u} // value ∈ ((decodeFamily seeds seedModel arrows
      (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change (w seeds seedModel arrows domain body))).model point).carrier} ≃
    {value : HSet.{u} // value ∈ ((decodeFamily seeds seedModel arrows
      (freshW seeds seedModel arrows change domain body)).model point).carrier} :=
  (((decodeFamily seeds seedModel arrows
    (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change (w seeds seedModel arrows domain body))).model point).decode.trans
      (wFreshComparison seeds seedModel arrows change domain body point)).trans
        ((decodeFamily seeds seedModel arrows (freshW seeds seedModel arrows change domain body)).model point).decode.symm

theorem wFreshMember_decode (point : other.base.Elements)
    (member : {value : HSet.{u} // value ∈ ((decodeFamily seeds seedModel arrows
      (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change (w seeds seedModel arrows domain body))).model point).carrier}) :
    ((decodeFamily seeds seedModel arrows (freshW seeds seedModel arrows change domain body)).model point).decode
      (wFreshMemberEquiv seeds seedModel arrows change domain body point member) =
        wFreshComparison seeds seedModel arrows change domain body point
          (((decodeFamily seeds seedModel arrows
            (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change (w seeds seedModel arrows domain body))).model point).decode member) :=
  ((decodeFamily seeds seedModel arrows (freshW seeds seedModel arrows change domain body)).model point).decode.apply_symm_apply _


theorem wFreshMember_natural {point next : other.base.Elements} (step : point ⟶ next)
    (member : {value : HSet.{u} // value ∈ ((decodeFamily seeds seedModel arrows
      (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change (w seeds seedModel arrows domain body))).model point).carrier}) :
    wFreshMemberEquiv seeds seedModel arrows change domain body next
      ((decodeFamily seeds seedModel arrows
        (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change (w seeds seedModel arrows domain body))).memberRestriction step member) =
      (decodeFamily seeds seedModel arrows (freshW seeds seedModel arrows change domain body)).memberRestriction step
        (wFreshMemberEquiv seeds seedModel arrows change domain body point member) := by
  let source := decodeFamily seeds seedModel arrows
    (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change (w seeds seedModel arrows domain body))
  let target := decodeFamily seeds seedModel arrows (freshW seeds seedModel arrows change domain body)
  apply (target.model next).decode.injective
  exact (wFreshMember_decode seeds seedModel arrows change domain body next _).trans
    ((congrArg (wFreshComparison seeds seedModel arrows change domain body next)
      (source.memberRestriction_decode step member)).trans
      ((wFreshComparison_natural seeds seedModel arrows change domain body step _).trans
        ((congrArg (target.family.map step)
          (wFreshMember_decode seeds seedModel arrows change domain body point member).symm).trans
          (target.memberRestriction_decode step
            (wFreshMemberEquiv seeds seedModel arrows change domain body point member)).symm)))


/-- Every independently formed W code retains its faithfully labelled
context in the material root. This is stronger than member injectivity
within one fixed fibre. -/
theorem w_values_separate_contexts {firstPoint secondPoint : context.base.Elements}
    (different : firstPoint ≠ secondPoint)
    (first : (decodeFamily seeds seedModel arrows (w seeds seedModel arrows domain body)).family.obj firstPoint)
    (second : (decodeFamily seeds seedModel arrows (w seeds seedModel arrows domain body)).family.obj secondPoint) :
    ((decodeFamily seeds seedModel arrows (w seeds seedModel arrows domain body)).model firstPoint).value first ≠
      ((decodeFamily seeds seedModel arrows (w seeds seedModel arrows domain body)).model secondPoint).value second := by
  revert body
  refine Quotient.inductionOn domain ?_
  intro raw body
  refine Quotient.inductionOn body ?_
  intro rawBody first second same
  let positions := PowerClassPresheafProducts.indexedBody raw.1.family rawBody.1.family
  let arrowLabels := ContextualGeneratedUniverse.MaterialFamily.elementArrowCoding (context := context) arrows
  let outputModels := fun argument : raw.1.family.Elements => rawBody.1.model ⟨argument.1.1, ⟨argument.1.2, argument.2⟩⟩
  rcases first with ⟨first, _firstNatural⟩
  rcases second with ⟨second, _secondNatural⟩
  cases first with
  | sup label children =>
    cases second with
    | sup other successors =>
      change MaterialContextualWTypes.encode raw.1.family positions context.labels arrowLabels raw.1.model outputModels
        (.sup label children) =
        MaterialContextualWTypes.encode raw.1.family positions context.labels arrowLabels raw.1.model outputModels
          (.sup other successors) at same
      have row := (MaterialContextualWTypes.mem_encode_sup_iff raw.1.family positions context.labels arrowLabels
        raw.1.model outputModels label children
        (HSet.kpair (ContextualWLabels.shapeTag context.labels firstPoint ((raw.1.model firstPoint).value label)) ∅)).mpr
          (Or.inl rfl)
      rw [same] at row
      rcases (MaterialContextualWTypes.mem_encode_sup_iff raw.1.family positions context.labels arrowLabels
        raw.1.model outputModels other successors _).mp row with sameShape | ⟨branch, sameBranch⟩
      · exact different (context.labels.injective
          (HSet.kpair_inj.mp (HSet.kpair_inj.mp (HSet.kpair_inj.mp sameShape).1).2).1)
      · exact (ContextualWLabels.shapeTag_ne_positionTag raw.1.family positions context.labels arrowLabels
          raw.1.model outputModels firstPoint ((raw.1.model firstPoint).value label) ⟨secondPoint, other⟩ branch
            (HSet.kpair_inj.mp sameBranch).1).elim

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualClosedUniverseComparisons
