import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualSigmaEliminationComparison
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualPresentation

/-!
# Full refinement sum packing under generated annotation equations

In the independent mixed refinement grammar, the domain and body equations
give an actual typed isomorphism of the two
component contexts. Packing retains both component positions; its comparison
uses the mixed pair rule, since its pair annotations need not be equal syntax.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.SigmaAnnotationComparison

open _root_.CategoryTheory
open DependentTypes QuotientComprehensionSyntax SigmaEliminationComparison

universe u
variable {S : Symbols.{u}} {D : Signature S}

theorem domainContextEquality {context : Context D} (first second : TypeOver context)
    (same : Holds D (.typeEq context.raw first.code second.code)) :
    Holds D (.contextEq (extend context first).raw (extend context second).raw) :=
  conclude (.contextExtendEquality context.raw context.raw first.code second.code)
    ⟨Presentation.contextEquality_refl context.formed, same, second.formed, trivial⟩

theorem tupleContextEquality {context : Context D} (first second : TypeOver context)
    (sameDomain : Holds D (.typeEq context.raw first.code second.code))
    (firstBody : TypeOver (extend context first)) (secondBody : TypeOver (extend context second))
    (sameBody : Holds D (.typeEq (extend context first).raw firstBody.code
      (secondBody.reindex (extensionComparison first second sameDomain).hom).code)) :
    Holds D (.contextEq (rawTuple first firstBody).raw (rawTuple second secondBody).raw) := by
  rw [extensionComparison_type_code] at sameBody
  exact conclude (.contextExtendEquality (extend context first).raw (extend context second).raw
    firstBody.code secondBody.code)
    ⟨domainContextEquality first second sameDomain, sameBody, secondBody.formed, trivial⟩

def tupleComparison {context : Context D} (first second : TypeOver context)
    (sameDomain : Holds D (.typeEq context.raw first.code second.code))
    (firstBody : TypeOver (extend context first)) (secondBody : TypeOver (extend context second))
    (sameBody : Holds D (.typeEq (extend context first).raw firstBody.code
      (secondBody.reindex (extensionComparison first second sameDomain).hom).code)) :
    rawTuple first firstBody ≅ rawTuple second secondBody :=
  Presentation.contextIso _ _ _ _ (tupleContextEquality first second sameDomain firstBody secondBody sameBody)

@[simp] theorem tupleComparison_hom_substitution {context : Context D} (first second : TypeOver context)
    (sameDomain : Holds D (.typeEq context.raw first.code second.code))
    (firstBody : TypeOver (extend context first)) (secondBody : TypeOver (extend context second))
    (sameBody : Holds D (.typeEq (extend context first).raw firstBody.code
      (secondBody.reindex (extensionComparison first second sameDomain).hom).code)) :
    (tupleComparison first second sameDomain firstBody secondBody sameBody).hom.substitution = TermExpr.var := rfl

@[simp] theorem tupleComparison_inv_substitution {context : Context D} (first second : TypeOver context)
    (sameDomain : Holds D (.typeEq context.raw first.code second.code))
    (firstBody : TypeOver (extend context first)) (secondBody : TypeOver (extend context second))
    (sameBody : Holds D (.typeEq (extend context first).raw firstBody.code
      (secondBody.reindex (extensionComparison first second sameDomain).hom).code)) :
    (tupleComparison first second sameDomain firstBody secondBody sameBody).inv.substitution = TermExpr.var := rfl

theorem genericPair_equality {context : Context D} (first second : TypeOver context)
    (sameDomain : Holds D (.typeEq context.raw first.code second.code))
    (firstBody : TypeOver (extend context first)) (secondBody : TypeOver (extend context second))
    (sameBody : Holds D (.typeEq (extend context first).raw firstBody.code
      (secondBody.reindex (extensionComparison first second sameDomain).hom).code)) :
    Holds D (.termEq (rawTuple first firstBody).raw
      (genericPair first.code firstBody.code) (genericPair second.code secondBody.code)
      ((rawSigma first firstBody).reindex (rawTupleBase first firstBody)).code) := by
  let comparison := tupleComparison first second sameDomain firstBody secondBody sameBody
  have domains := reindex_typeEquality sameDomain (rawTupleBase first firstBody)
  change Holds D (.typeEq _ (first.code.substitute _) (second.code.substitute _)) at domains
  rw [rawTupleBase_substitution, TypeExpr.substitute_variables, TypeExpr.substitute_variables] at domains
  have bodies := sameBody
  rw [extensionComparison_type_code] at bodies
  have weakenedBodies := reindex_typeEquality bodies (rawLift (rawTupleBase first firstBody) first)
  change Holds D (.typeEq _ (firstBody.code.substitute _) (secondBody.code.substitute _)) at weakenedBodies
  rw [rawLift_substitution, rawTupleBase_substitution, liftSubstitution_variables,
    TypeExpr.substitute_variables, TypeExpr.substitute_variables] at weakenedBodies
  change Holds D (.typeEq (.snoc (rawTuple first firstBody).raw
    (first.code.substitute (rawTupleBase first firstBody).substitution)) _ _) at weakenedBodies
  rw [rawTupleBase_substitution, TypeExpr.substitute_variables] at weakenedBodies
  let rightBody := secondBody.reindex (rawLift (comparison.hom ≫ rawTupleBase second secondBody) second)
  have rightBodyFormed := rightBody.formed
  change Holds D (.type _ (secondBody.code.substitute _)) at rightBodyFormed
  rw [rawLift_substitution] at rightBodyFormed
  change Holds D (.type _ (secondBody.code.substitute
    (liftSubstitution (composeSubstitution (rawTupleBase second secondBody).substitution
      comparison.hom.substitution)))) at rightBodyFormed
  rw [show comparison.hom.substitution = TermExpr.var from tupleComparison_hom_substitution _ _ _ _ _ _,
    composeSubstitution_identity, rawTupleBase_substitution, liftSubstitution_variables,
    TypeExpr.substitute_variables] at rightBodyFormed
  change Holds D (.type (.snoc (rawTuple first firstBody).raw
    (second.code.substitute (composeSubstitution (rawTupleBase second secondBody).substitution
      comparison.hom.substitution))) _) at rightBodyFormed
  rw [show comparison.hom.substitution = TermExpr.var from tupleComparison_hom_substitution _ _ _ _ _ _,
    composeSubstitution_identity, rawTupleBase_substitution, TypeExpr.substitute_variables] at rightBodyFormed
  have firsts := termEquality_refl (rawFirst first firstBody)
  rw [rawFirst_code] at firsts
  change Holds D (.termEq _ _ _ (first.code.substitute _)) at firsts
  rw [rawTupleBase_substitution, TypeExpr.substitute_variables] at firsts
  have seconds := termEquality_refl (rawSecond first firstBody)
  rw [rawSecond_code] at seconds
  change Holds D (.termEq _ _ _ ((firstBody.code.substitute _).substitute _)) at seconds
  rw [rawLift_substitution, rawTupleBase_substitution, liftSubstitution_variables,
    TypeExpr.substitute_variables, nativeSection_substitution, rawFirst_code] at seconds
  have rightFirst := conclude (.transportTerm (rawTuple second secondBody).raw
    (rawTuple first firstBody).raw (rawFirst second secondBody).code
    (second.reindex (rawTupleBase second secondBody)).code)
    ⟨Presentation.contextEquality_symm (tupleContextEquality _ _ _ _ _ sameBody),
      (rawFirst second secondBody).typed, trivial⟩
  rw [rawFirst_code] at rightFirst
  change Holds D (.term _ _ (second.code.substitute _)) at rightFirst
  rw [rawTupleBase_substitution, TypeExpr.substitute_variables] at rightFirst
  have rightSecond := conclude (.transportTerm (rawTuple second secondBody).raw
    (rawTuple first firstBody).raw (rawSecond second secondBody).code
    (((secondBody.reindex (rawLift (rawTupleBase second secondBody) second)).reindex
      (nativeSection (rawFirst second secondBody))).code))
    ⟨Presentation.contextEquality_symm (tupleContextEquality _ _ _ _ _ sameBody),
      (rawSecond second secondBody).typed, trivial⟩
  rw [rawSecond_code] at rightSecond
  change Holds D (.term _ _ ((secondBody.code.substitute _).substitute _)) at rightSecond
  rw [rawLift_substitution, rawTupleBase_substitution, liftSubstitution_variables,
    TypeExpr.substitute_variables, nativeSection_substitution, rawFirst_code] at rightSecond
  change Holds D (.termEq _ _ _ ((rawSigma first firstBody).code.substitute _))
  rw [rawTupleBase_substitution, TypeExpr.substitute_variables]
  exact conclude (.pairAnnotationCongruence (rawTuple first firstBody).raw
    (first.code.rename (Fin.succ ∘ Fin.succ)) (second.code.rename (Fin.succ ∘ Fin.succ))
    (firstBody.code.rename (liftRenaming (Fin.succ ∘ Fin.succ)))
    (secondBody.code.rename (liftRenaming (Fin.succ ∘ Fin.succ)))
    (.var 1) (.var 1) (.var 0) (.var 0))
    ⟨domains, weakenedBodies, rightBodyFormed, firsts, seconds, rightFirst, rightSecond, trivial⟩

set_option backward.isDefEq.respectTransparency false in
theorem packing_comparison {context : Context D} (first second : TypeOver context)
    (sameDomain : Holds D (.typeEq context.raw first.code second.code))
    (firstBody : TypeOver (extend context first)) (secondBody : TypeOver (extend context second))
    (sameBody : Holds D (.typeEq (extend context first).raw firstBody.code
      (secondBody.reindex (extensionComparison first second sameDomain).hom).code)) :
    homEquality D
      (rawPack first firstBody ≫ (extensionComparison (rawSigma first firstBody)
        (rawSigma second secondBody) (rawSigma_typeEquality _ _ sameDomain _ _ sameBody)).hom)
      ((tupleComparison first second sameDomain firstBody secondBody sameBody).hom ≫
        rawPack second secondBody) := by
  let tuple := tupleComparison first second sameDomain firstBody secondBody sameBody
  let sameSum := rawSigma_typeEquality first second sameDomain firstBody secondBody sameBody
  let rightBase := tuple.hom ≫ rawTupleBase second secondBody
  have bases : rawTupleBase first firstBody = rightBase := by
    apply Hom.ext
    change (rawTupleBase first firstBody).substitution =
      composeSubstitution (rawTupleBase second secondBody).substitution tuple.hom.substitution
    rw [show tuple.hom.substitution = TermExpr.var from tupleComparison_hom_substitution _ _ _ _ _ _,
      composeSubstitution_identity, rawTupleBase_substitution, rawTupleBase_substitution]
  change homEquality D
    (Contextual.pair (rawTupleBase first firstBody) (rawGenericPair first firstBody) ≫
      (extensionComparison _ _ sameSum).hom)
    (tuple.hom ≫ Contextual.pair (rawTupleBase second secondBody) (rawGenericPair second secondBody))
  rw [extensionComparison_pair]
  rw [show tuple.hom ≫ Contextual.pair (rawTupleBase second secondBody) (rawGenericPair second secondBody) =
    Contextual.pair rightBase
      (((rawGenericPair second secondBody).reindex tuple.hom).cast
        ((rawSigma second secondBody).reindex_comp tuple.hom (rawTupleBase second secondBody)).symm) from
      comprehension_natural ⟨rawTupleBase second secondBody, rawGenericPair second secondBody⟩ tuple.hom]
  apply homEquality_pair
  · rw [← bases]
    exact homEquality_refl _
  · have compared := termEquality_convert
      (genericPair_equality first second sameDomain firstBody secondBody sameBody)
      (reindex_typeEquality sameSum (rawTupleBase first firstBody))
    simpa only [Term.convertType_code, Term.cast_code, Term.reindex, TypeOver.reindex, rawGenericPair_code,
      show tuple.hom.substitution = TermExpr.var from tupleComparison_hom_substitution _ _ _ _ _ _,
      TermExpr.substitute_identity] using compared

set_option backward.isDefEq.respectTransparency false in
theorem packing_square {context : Context D} (first second : TypeOver context)
    (sameDomain : Holds D (.typeEq context.raw first.code second.code))
    (firstBody : TypeOver (extend context first)) (secondBody : TypeOver (extend context second))
    (sameBody : Holds D (.typeEq (extend context first).raw firstBody.code
      (secondBody.reindex (extensionComparison first second sameDomain).hom).code)) :
    QuotientCwf.project (rawPack first firstBody) ≫ QuotientCwf.project
      (extensionComparison (rawSigma first firstBody) (rawSigma second secondBody)
        (rawSigma_typeEquality _ _ sameDomain _ _ sameBody)).hom =
      QuotientCwf.project (tupleComparison first second sameDomain firstBody secondBody sameBody).hom ≫
        QuotientCwf.project (rawPack second secondBody) := by
  rw [← (quotientProjection D).map_comp, ← (quotientProjection D).map_comp]
  exact (quotientProjection_map_eq_iff _ _).mpr (packing_comparison _ _ _ _ _ sameBody)

set_option backward.isDefEq.respectTransparency false in
theorem inverse_packing_square {context : Context D} (first second : TypeOver context)
    (sameDomain : Holds D (.typeEq context.raw first.code second.code))
    (firstBody : TypeOver (extend context first)) (secondBody : TypeOver (extend context second))
    (sameBody : Holds D (.typeEq (extend context first).raw firstBody.code
      (secondBody.reindex (extensionComparison first second sameDomain).hom).code)) :
    QuotientCwf.project (rawPack second secondBody) ≫ QuotientCwf.project
      (extensionComparison (rawSigma first firstBody) (rawSigma second secondBody)
        (rawSigma_typeEquality _ _ sameDomain _ _ sameBody)).inv =
      QuotientCwf.project (tupleComparison first second sameDomain firstBody secondBody sameBody).inv ≫
        QuotientCwf.project (rawPack first firstBody) := by
  let tuple := (quotientProjection D).mapIso (tupleComparison _ _ sameDomain _ _ sameBody)
  let sum := (quotientProjection D).mapIso
    (extensionComparison (rawSigma first firstBody) (rawSigma second secondBody)
      (rawSigma_typeEquality _ _ sameDomain _ _ sameBody))
  have square := packing_square first second sameDomain firstBody secondBody sameBody
  change QuotientCwf.project (rawPack first firstBody) ≫ sum.hom =
    tuple.hom ≫ QuotientCwf.project (rawPack second secondBody) at square
  change QuotientCwf.project (rawPack second secondBody) ≫ sum.inv =
    tuple.inv ≫ QuotientCwf.project (rawPack first firstBody)
  calc
    _ = tuple.inv ≫ (tuple.hom ≫ QuotientCwf.project (rawPack second secondBody)) ≫ sum.inv := by
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    _ = tuple.inv ≫ (QuotientCwf.project (rawPack first firstBody) ≫ sum.hom) ≫ sum.inv :=
      congrArg (fun operation => tuple.inv ≫ operation ≫ sum.inv) square.symm
    _ = _ := by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
theorem branch_annotation {context : Context D} (first second : TypeOver context)
    (sameDomain : Holds D (.typeEq context.raw first.code second.code))
    (firstBody : TypeOver (extend context first)) (secondBody : TypeOver (extend context second))
    (sameBody : Holds D (.typeEq (extend context first).raw firstBody.code
      (secondBody.reindex (extensionComparison first second sameDomain).hom).code))
    (motive : TypeOver (extend context (rawSigma first firstBody))) :
    Holds D (.typeEq (rawTuple second secondBody).raw
      (((motive.reindex (rawPack first firstBody)).reindex
        (tupleComparison first second sameDomain firstBody secondBody sameBody).inv).code)
      (((motive.reindex (extensionComparison (rawSigma first firstBody) (rawSigma second secondBody)
        (rawSigma_typeEquality _ _ sameDomain _ _ sameBody)).inv).reindex
          (rawPack second secondBody)).code)) := by
  apply (QType.mk_eq_iff _ _).mp
  change QuotientCwf.tySub (QuotientCwf.tySub (QType.mk motive) (QuotientCwf.project (rawPack first firstBody)))
      (QuotientCwf.project (tupleComparison _ _ sameDomain _ _ sameBody).inv) =
    QuotientCwf.tySub (QuotientCwf.tySub (QType.mk motive) (QuotientCwf.project
      (extensionComparison _ _ (rawSigma_typeEquality _ _ sameDomain _ _ sameBody)).inv))
        (QuotientCwf.project (rawPack second secondBody))
  rw [← QuotientCwf.tySub_comp, ← QuotientCwf.tySub_comp, inverse_packing_square]

theorem rawEliminate_compared {context : Context D}
    (first second : TypeOver context) (sameDomain : Holds D (.typeEq context.raw first.code second.code))
    (firstBody : TypeOver (extend context first)) (secondBody : TypeOver (extend context second))
    (sameBody : Holds D (.typeEq (extend context first).raw firstBody.code
      (secondBody.reindex (extensionComparison first second sameDomain).hom).code))
    (firstMotive : TypeOver (extend context (rawSigma first firstBody)))
    (secondMotive : TypeOver (extend context (rawSigma second secondBody)))
    (sameMotive : Holds D (.typeEq (extend context (rawSigma first firstBody)).raw firstMotive.code
      (secondMotive.reindex (extensionComparison (rawSigma first firstBody) (rawSigma second secondBody)
        (rawSigma_typeEquality _ _ sameDomain _ _ sameBody)).hom).code))
    (firstBranch : Term (rawTuple first firstBody) (firstMotive.reindex (rawPack first firstBody)))
    (secondBranch : Term (rawTuple second secondBody) (secondMotive.reindex (rawPack second secondBody)))
    (branches : Holds D (.termEq (rawTuple first firstBody).raw firstBranch.code secondBranch.code
      (firstMotive.reindex (rawPack first firstBody)).code))
    (firstValue : Term context (rawSigma first firstBody)) (secondValue : Term context (rawSigma second secondBody))
    (values : Holds D (.termEq context.raw firstValue.code secondValue.code (rawSigma first firstBody).code)) :
    QTerm.mk (rawEliminate first firstBody firstMotive firstBranch firstValue) =
      QTerm.mk (rawEliminate second secondBody secondMotive secondBranch secondValue) := by
  apply (QTerm.mk_eq_iff _ _).mpr
  refine ⟨rawInstantiation_typeEquality _ _ (rawSigma_typeEquality _ _ sameDomain _ _ sameBody)
    _ _ sameMotive _ _ values, ?_⟩
  rw [extensionComparison_type_code] at sameBody sameMotive
  have secondTyped := secondBranch.typed
  change Holds D (.term _ _ (secondMotive.code.substitute (rawPack second secondBody).substitution)) at secondTyped
  rw [rawPack_substitution] at secondTyped
  change Holds D (.termEq _ _ _ (firstMotive.code.substitute (rawPack first firstBody).substitution)) at branches
  rw [rawPack_substitution] at branches
  change Holds D (.termEq context.raw _ _ (firstMotive.code.substitute (nativeSection firstValue).substitution))
  rw [nativeSection_substitution]
  exact conclude (.sigmaEliminationAnnotationCongruence context.raw first.code second.code firstBody.code secondBody.code
    firstMotive.code secondMotive.code firstBranch.code secondBranch.code firstValue.code secondValue.code)
    ⟨sameDomain, sameBody, secondBody.formed, sameMotive, secondMotive.formed, branches,
      secondTyped, values, secondValue.typed, trivial⟩

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.SigmaAnnotationComparison
