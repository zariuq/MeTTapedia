import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSyntacticSumReadout
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualSigmaAnnotationComparison

/-!
# Complete generated refinement sum-elimination readouts

The full refinement grammar supplies actual dependent motive and branch
readouts, transported through the chosen sum
and tuple presentations. The earned packing square justifies their typed
conversion across changed annotations. Reconstruction preserves the authored
eliminator code and its complete supplied result class.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.SyntacticReification

open _root_.CategoryTheory
open Mettapedia.TypeTheory.ContextualModelTelescopes
open DependentTypes QuotientComprehensionSyntax SigmaEliminationComparison SigmaAnnotationComparison
open Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)
open Mettapedia.TypeTheory.ContextualSumComprehension

universe u
variable {S : Symbols.{u}} {D : Signature S}

noncomputable def rawSumPresentation {context : QuotientCwf.QContext D}
    (domain : QuotientCwf.Ty context) (codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)) :
    (QuotientCwf.ext context (Sums.sigma domain codomain)).as ≅
      extend context.as (rawSigma (QuotientCwf.typeRepresentative domain) (QuotientCwf.typeRepresentative codomain)) :=
  extensionComparison (QuotientCwf.typeRepresentative (Sums.sigma domain codomain))
    (rawSigma (QuotientCwf.typeRepresentative domain) (QuotientCwf.typeRepresentative codomain))
    ((QType.mk_eq_iff _ _).mp (QuotientCwf.typeRepresentative_class (Sums.sigma domain codomain)))

noncomputable def canonicalMotive {context : QuotientCwf.QContext D}
    (domain : QuotientCwf.Ty context) (codomain : QuotientCwf.Ty (QuotientCwf.ext context domain))
    (motive : TypeOver (QuotientCwf.ext context (Sums.sigma domain codomain)).as) :
    TypeOver (extend context.as
      (rawSigma (QuotientCwf.typeRepresentative domain) (QuotientCwf.typeRepresentative codomain))) :=
  motive.reindex (rawSumPresentation domain codomain).inv

set_option backward.isDefEq.respectTransparency false in
theorem canonicalMotive_code {context : QuotientCwf.QContext D}
    (domain : QuotientCwf.Ty context) (codomain : QuotientCwf.Ty (QuotientCwf.ext context domain))
    (motive : TypeOver (QuotientCwf.ext context (Sums.sigma domain codomain)).as) :
    (canonicalMotive domain codomain motive).code = motive.code := by
  change motive.code.substitute (rawSumPresentation domain codomain).inv.substitution = _
  rw [show (rawSumPresentation domain codomain).inv.substitution = TermExpr.var from
    extensionComparison_inv_substitution _ _ _, TypeExpr.substitute_identity]

set_option backward.isDefEq.respectTransparency false in
theorem canonicalMotive_native {context : QuotientCwf.QContext D}
    (domain : QuotientCwf.Ty context) (codomain : QuotientCwf.Ty (QuotientCwf.ext context domain))
    (motive : TypeOver (QuotientCwf.ext context (Sums.sigma domain codomain)).as) :
    nativeMotive domain codomain (canonicalMotive domain codomain motive) = QType.mk motive := by
  change QuotientCwf.tySub (QuotientCwf.tySub (QType.mk motive)
    (QuotientCwf.project (rawSumPresentation domain codomain).inv))
      (QuotientCwf.project (rawSumPresentation domain codomain).hom) = _
  rw [← QuotientCwf.tySub_comp, ← (quotientProjection D).map_comp,
    (rawSumPresentation domain codomain).hom_inv_id, (quotientProjection D).map_id,
    QuotientCwf.tySub_id]

set_option backward.isDefEq.respectTransparency false in
theorem section_presentation {context : QuotientCwf.QContext D} (annotation : TypeOver context.as)
    (supplied : QuotientCwf.Tm context (QType.mk annotation)) (actual : Term context.as annotation)
    (classes : QTerm.mk actual = supplied.val) :
    QuotientCwf.project (nativeSection actual) ≫ (QuotientCwf.extPresentation context.as annotation).inv =
      selfExtend (QuotientCwf.cwf D) supplied := by
  let selected := QuotientCwf.typeRepresentative (QType.mk annotation)
  let same := (QType.mk_eq_iff selected annotation).mp (QuotientCwf.typeRepresentative_class (QType.mk annotation))
  let comparison := extensionComparison selected annotation same
  let converted := actual.convertType selected (typeEquality_symm same)
  have sections : nativeSection actual ≫ comparison.inv = nativeSection converted := by
    apply Hom.ext
    change composeSubstitution comparison.inv.substitution (nativeSection actual).substitution =
      (nativeSection converted).substitution
    rw [show comparison.inv.substitution = TermExpr.var from extensionComparison_inv_substitution _ _ _,
      identity_composeSubstitution, nativeSection_substitution, nativeSection_substitution,
      Term.convertType_code]
  change QuotientCwf.project (nativeSection actual) ≫ QuotientCwf.project comparison.inv = _
  rw [← (quotientProjection D).map_comp, sections]
  exact nativeSection_projects_of_class supplied converted
    ((QTerm.mk_convertType actual selected (typeEquality_symm same)).trans classes)

theorem eliminate_class {context : QuotientCwf.QContext D}
    (domain : QuotientCwf.Ty context) (codomain : QuotientCwf.Ty (QuotientCwf.ext context domain))
    {first second : QuotientCwf.Ty (QuotientCwf.ext context (Sums.sigma domain codomain))}
    (same : first = second)
    (firstBody : QuotientCwf.Tm (QuotientCwf.ext (QuotientCwf.ext context domain) codomain)
      (QuotientCwf.tySub first (pack (SumElimination.stable D) domain codomain)))
    (secondBody : QuotientCwf.Tm (QuotientCwf.ext (QuotientCwf.ext context domain) codomain)
      (QuotientCwf.tySub second (pack (SumElimination.stable D) domain codomain)))
    (classes : firstBody.val = secondBody.val) :
    (eliminate (SumElimination.stable D) domain codomain first firstBody).val =
      (eliminate (SumElimination.stable D) domain codomain second secondBody).val := by
  cases same
  have bodies : firstBody = secondBody := Subtype.ext classes
  rw [bodies]

set_option backward.isDefEq.respectTransparency false in
theorem sigma_elimination_readout {context : QuotientCwf.QContext D} {domain : QuotientCwf.Ty context}
    {codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)}
    {motive : QuotientCwf.Ty (QuotientCwf.ext context (Sums.sigma domain codomain))}
    {domainCode : TypeExpr S context.as.arity} {bodyCode : TypeExpr S (context.as.arity + 1)}
    {motiveCode : TypeExpr S (context.as.arity + 1)}
    {branchCode : TermExpr S (context.as.arity + 2)} {valueCode : TermExpr S context.as.arity}
    (first : TypeReadout context domainCode domain)
    (second : TypeReadout (QuotientCwf.ext context domain) bodyCode codomain)
    (third : TypeReadout (QuotientCwf.ext context (Sums.sigma domain codomain)) motiveCode motive)
    (branch : QuotientCwf.Tm (QuotientCwf.ext (QuotientCwf.ext context domain) codomain)
      (QuotientCwf.tySub motive (pack (SumElimination.stable D) domain codomain)))
    (value : QuotientCwf.Tm context (Sums.sigma domain codomain))
    (branchRead : TermReadout (QuotientCwf.ext (QuotientCwf.ext context domain) codomain) branchCode
      ⟨QuotientCwf.tySub motive (pack (SumElimination.stable D) domain codomain), branch⟩)
    (valueRead : TermReadout context valueCode ⟨Sums.sigma domain codomain, value⟩) :
    TermReadout context (.sigmaElim domainCode bodyCode motiveCode branchCode valueCode)
      ⟨QuotientCwf.tySub motive (selfExtend (QuotientCwf.cwf D) value),
        QuotientCwf.tmSub (eliminate (SumElimination.stable D) domain codomain motive branch)
          (selfExtend (QuotientCwf.cwf D) value)⟩ := by
  rcases first with ⟨annotation, codeRead, domainClass⟩
  rcases second with ⟨body, bodyCodeRead, bodyClass⟩
  rcases third with ⟨rawMotive, motiveCodeRead, motiveClass⟩
  let firstDomain := QuotientCwf.typeRepresentative domain
  let firstBody := QuotientCwf.typeRepresentative codomain
  let secondBody := authoredBody annotation domainClass body
  let sameDomain := domain_equality annotation domainClass
  let sameBody := body_equality annotation domainClass body bodyClass
  let sameSum := rawSigma_typeEquality firstDomain annotation sameDomain firstBody secondBody sameBody
  let tuple := tupleComparison firstDomain annotation sameDomain firstBody secondBody sameBody
  let sum := extensionComparison (rawSigma firstDomain firstBody) (rawSigma annotation secondBody) sameSum
  let firstMotive := canonicalMotive domain codomain rawMotive
  let secondMotive := firstMotive.reindex sum.inv
  have motives : nativeMotive domain codomain firstMotive = motive :=
    (canonicalMotive_native domain codomain rawMotive).trans motiveClass
  have branchType : QType.mk (firstMotive.reindex (rawPack firstDomain firstBody)) =
      QuotientCwf.tySub motive (pack (SumElimination.stable D) domain codomain) :=
    (nativeMotive_at_pack domain codomain firstMotive).symm.trans
      (congrArg (fun type => QuotientCwf.tySub type (pack (SumElimination.stable D) domain codomain)) motives)
  rcases retype branchRead (firstMotive.reindex (rawPack firstDomain firstBody)) branchType.symm with
    ⟨firstBranch, branchCodeRead, branchClass⟩
  let secondBranch := (firstBranch.reindex tuple.inv).convertType
    (secondMotive.reindex (rawPack annotation secondBody))
    (branch_annotation firstDomain annotation sameDomain firstBody secondBody sameBody firstMotive)
  have secondBranchCode : secondBranch.code = firstBranch.code := by
    rw [Term.convertType_code]
    change firstBranch.code.substitute tuple.inv.substitution = _
    rw [show tuple.inv.substitution = TermExpr.var from tupleComparison_inv_substitution _ _ _ _ _ _,
      TermExpr.substitute_identity]
  have secondMotiveCode : secondMotive.code = firstMotive.code := by
    change firstMotive.code.substitute sum.inv.substitution = _
    rw [show sum.inv.substitution = TermExpr.var from extensionComparison_inv_substitution _ _ _,
      TypeExpr.substitute_identity]
  have sameMotive : Holds D (.typeEq (extend context.as (rawSigma firstDomain firstBody)).raw
      firstMotive.code (secondMotive.reindex sum.hom).code) := by
    change Holds D (.typeEq _ firstMotive.code ((firstMotive.reindex sum.inv).reindex sum.hom).code)
    rw [← TypeOver.reindex_comp, sum.hom_inv_id, TypeOver.reindex_id]
    exact typeEquality_refl _
  have branches : Holds D (.termEq (rawTuple firstDomain firstBody).raw
      firstBranch.code secondBranch.code (firstMotive.reindex (rawPack firstDomain firstBody)).code) := by
    rw [secondBranchCode]
    exact termEquality_refl firstBranch
  rcases retype valueRead (rawSigma annotation secondBody)
    (sigma_class annotation domainClass body bodyClass).symm with
    ⟨secondValue, valueCodeRead, valueClass⟩
  let firstValue := Sums.pairRepresentative value
  have values := (QTerm.mk_eq_iff _ _).mp ((Sums.pairRepresentative_class value).trans valueClass.symm)
  let reconstructed := rawEliminate annotation secondBody secondMotive secondBranch secondValue
  refine ⟨_, reconstructed, ?_, ?_⟩
  · change TermExpr.sigmaElim annotation.code secondBody.code secondMotive.code secondBranch.code secondValue.code = _
    rw [secondBranchCode, secondMotiveCode, canonicalMotive_code, authoredBody_code,
      codeRead, bodyCodeRead, motiveCodeRead, branchCodeRead, valueCodeRead]
  · have compared := rawEliminate_compared firstDomain annotation sameDomain firstBody secondBody sameBody
      firstMotive secondMotive sameMotive firstBranch secondBranch branches firstValue secondValue values.2
    have interpreted := authored_elimination_is_contextual domain codomain firstMotive firstBranch firstValue
    have branchesNative := eliminate_class domain codomain motives
      (nativeBranch domain codomain firstMotive firstBranch) branch branchClass
    have sections := section_presentation (rawSigma firstDomain firstBody) value firstValue
      (Sums.pairRepresentative_class value)
    exact compared.symm.trans (interpreted.trans
      (congrArg₂ (fun operation arrow => QuotientCwf.totalSub operation arrow) branchesNative sections))

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.SyntacticReification
