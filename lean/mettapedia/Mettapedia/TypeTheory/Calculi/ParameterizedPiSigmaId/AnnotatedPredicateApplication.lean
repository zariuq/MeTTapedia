import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateInstantiation
import Mettapedia.Logic.HOL.IndexedMotiveInhabitance

/-!
# Applying an annotated dependent product interpretation

Opening the source family and instantiating its HOL reading use the same
argument. Product-code coherence transports the supplied function proof to
the interpreted product before retained elimination. The result keeps both
source readings and the actual proof syntax for the application judgment.
Readings alone do not establish a source typing derivation. Function and
argument predicate-membership proofs remain explicit inputs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading

open Mettapedia.Logic
open Presentation TypedEquality.Annotated
universe u v
variable {Head : Type} {Base : Type u} {Const : HOL.Ty Base → Type v}
    {lex : LexicalReading Head Base Const} {Γ : HOL.Ctx Base}

def applyProduct {domain codomain : HOL.Ty Base}
    {sourceDomain : CTm Head Γ.length} {sourceFamily : CTm Head (domain :: Γ).length}
    {sourceFunction sourceArgument : CTm Head Γ.length}
    {domainCode : HOL.Term Const Γ (.arr domain .prop)}
    {familyCode : HOL.Term Const (domain :: Γ) (.arr codomain .prop)}
    {productCode : HOL.Term Const Γ (.arr (.arr domain codomain) .prop)}
    {functionCode : HOL.Term Const Γ (.arr domain codomain)} {argumentCode : HOL.Term Const Γ domain}
    {assumptions : List (HOL.Formula Const Γ)}
    (productReading : Reads lex (.pi sourceDomain sourceFamily) productCode)
    (domainReading : Reads lex sourceDomain domainCode) (familyReading : Reads lex sourceFamily familyCode)
    (functionReading : Reads lex sourceFunction functionCode) (argumentReading : Reads lex sourceArgument argumentCode)
    (functionTyped : HOL.ProofSyntax Const assumptions (.app productCode functionCode))
    (argumentTyped : HOL.ProofSyntax Const assumptions (.app domainCode argumentCode)) :
    {_proof : HOL.ProofSyntax Const assumptions
      (.app (HOL.instantiate argumentCode familyCode) (.app functionCode argumentCode)) //
      Reads lex (.app sourceFunction sourceArgument) (.app functionCode argumentCode) ∧
      Reads lex (sourceFamily.subst (CTm.subst0 sourceArgument)) (HOL.instantiate argumentCode familyCode)} := by
  classical
  have equal := Reader.term_unique productReading (Reads.product domainReading familyReading)
  have typed : HOL.ProofSyntax Const assumptions
      (.app (HOL.PredicateProducts.pi domainCode familyCode) functionCode) :=
    HOL.ProofSyntax.castIndices rfl (congrArg (fun code => HOL.Term.app code functionCode) equal) functionTyped
  exact ⟨HOL.PredicateProducts.eliminate domainCode familyCode functionCode argumentCode typed argumentTyped,
    Reads.application functionReading argumentReading, familyReading.instantiate argumentReading⟩

theorem applyProduct_free {domain codomain : HOL.Ty Base}
    {sourceDomain : CTm Head Γ.length} {sourceFamily : CTm Head (domain :: Γ).length}
    {sourceFunction sourceArgument : CTm Head Γ.length}
    {domainCode : HOL.Term Const Γ (.arr domain .prop)}
    {familyCode : HOL.Term Const (domain :: Γ) (.arr codomain .prop)}
    {productCode : HOL.Term Const Γ (.arr (.arr domain codomain) .prop)}
    {functionCode : HOL.Term Const Γ (.arr domain codomain)} {argumentCode : HOL.Term Const Γ domain}
    {assumptions : List (HOL.Formula Const Γ)}
    (productReading : Reads lex (.pi sourceDomain sourceFamily) productCode)
    (domainReading : Reads lex sourceDomain domainCode) (familyReading : Reads lex sourceFamily familyCode)
    (functionReading : Reads lex sourceFunction functionCode) (argumentReading : Reads lex sourceArgument argumentCode)
    (functionTyped : HOL.ProofSyntax Const assumptions (.app productCode functionCode))
    (argumentTyped : HOL.ProofSyntax Const assumptions (.app domainCode argumentCode))
    (functionFree : functionTyped.FunctionExtensionalityFree) (argumentFree : argumentTyped.FunctionExtensionalityFree) :
    (applyProduct productReading domainReading familyReading functionReading argumentReading functionTyped argumentTyped).val.FunctionExtensionalityFree := by
  unfold applyProduct
  apply HOL.PredicateProducts.eliminate_free
  · exact (HOL.ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr functionFree
  · exact argumentFree

def inhabitReadResult {index space result : HOL.Ty Base}
    {sourceType : CTm Head Γ.length} {typeCode : HOL.Term Const Γ (.arr result .prop)}
    (motive : HOL.Term Const Γ (.arr index (.arr space (.arr result .prop))))
    (point : HOL.Term Const Γ space) (target : HOL.Term Const Γ index) (value : HOL.Term Const Γ result)
    {assumptions : List (HOL.Formula Const Γ)}
    (typeReading : Reads lex sourceType typeCode)
    (motiveReading : Reads lex sourceType (.app (.app motive target) point))
    (typed : HOL.ProofSyntax Const assumptions (.app typeCode value)) :
    HOL.ProofSyntax Const assumptions
      (.app (.app (HOL.IndexedMotiveInhabitance.predicate motive) point) target) := by
  classical
  have equal := Reader.term_unique typeReading motiveReading
  have resultTyped : HOL.ProofSyntax Const assumptions (.app (.app (.app motive target) point) value) :=
    .castIndices rfl (congrArg (fun code => HOL.Term.app code value) equal) typed
  exact HOL.IndexedMotiveInhabitance.introduce motive point target value resultTyped

theorem inhabitReadResult_free {index space result : HOL.Ty Base}
    {sourceType : CTm Head Γ.length} {typeCode : HOL.Term Const Γ (.arr result .prop)}
    (motive : HOL.Term Const Γ (.arr index (.arr space (.arr result .prop))))
    (point : HOL.Term Const Γ space) (target : HOL.Term Const Γ index) (value : HOL.Term Const Γ result)
    {assumptions : List (HOL.Formula Const Γ)}
    (typeReading : Reads lex sourceType typeCode)
    (motiveReading : Reads lex sourceType (.app (.app motive target) point))
    (typed : HOL.ProofSyntax Const assumptions (.app typeCode value))
    (free : typed.FunctionExtensionalityFree) :
    (inhabitReadResult motive point target value typeReading motiveReading typed).FunctionExtensionalityFree := by
  unfold inhabitReadResult
  apply HOL.IndexedMotiveInhabitance.introduce_free
  exact (HOL.ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr free

#print axioms Reads.instantiate
#print axioms applyProduct_free
#print axioms inhabitReadResult_free

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading
