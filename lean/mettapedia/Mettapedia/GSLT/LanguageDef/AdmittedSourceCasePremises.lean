import Mettapedia.GSLT.LanguageDef.AdmittedContainerInduction
import Mettapedia.Logic.HOL.IndexedContainerGuardElimination
import Mettapedia.Logic.HOL.GuardedConstructorMethod

/-!
# Reading the actual scoped source-case premises

The context is the one supplied by ScopedSourceIndexedCases: the original
field guard, the applied child predicate, and the method assumptions. Guard
elimination recovers the original field evidence. Substitution and retained
beta computation expose the full child condition from the second premise.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.AdmittedContainerHOL

open Mettapedia.Logic Mettapedia.Logic.HOL Mettapedia.TypeTheory
open IndexedContainerPositionTerms IndexedPolynomial.Description
open FiniteConstructorEncoding CurriedPredicates
universe u v w
variable {I : Interface.{u}} {source : PositiveInductiveBlock.Registry} {parameterCount : Nat}
  {context : List I.SortCode} {Base : Type v} {Const : Ty Base → Type w} {Γ Ξ : Ctx Base}
  (block : PositiveInductiveBlock.Admitted source I parameterCount context) (registered : block.WellRegistered)
  {reading : Reading I (IndexedPositiveContainer.Unindexed.liftRegistry source I) Const}
  (guards : FieldGuards reading)
  (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
  (numeral : Nat → Term Const Γ reading.number)
  {space : Ty Base}
  (constructorCode : Term Const Γ (reading.number ⇒
    payloadType ((codes block registered).map reading.fields) ⇒ (reading.number ⇒ space) ⇒ space))
  (zero : ClosedTerm Const reading.number) (successor : ClosedTerm Const (reading.number ⇒ reading.number))
  (bottomCode : Term Const Γ space) (predicate : Term Const Γ (space ⇒ .prop))
  (assumptions : List (Formula Const Γ))

def scopedSourceCaseAssumptions
    (images : Subst Const
      (recursiveSignature block registered (guards := guards) rho numeral zero successor bottomCode constructorCode).constructorContext Ξ)
    (occurrence : Fin ((codes block registered).map reading.fields).length)
    (arguments : Arguments Const Ξ (reading.fields (codeAt reading (codes block registered) occurrence))) :
    List (Formula Const Ξ) :=
  let signature := recursiveSignature block registered (guards := guards) rho numeral zero successor bottomCode constructorCode
  let images0 : Subst Const Γ signature.constructorContext := Subst.ofRename signature.constructorRenaming
  let condition := signature.constructorScope.childPredicate (weaken (weaken (weaken predicate))) signature.constructorChildren
  applyArguments _ (guards.compile (codeAt reading (codes block registered) occurrence)
      (Subst.comp images (Subst.comp images0 rho))) arguments ::
    .app (HOL.subst images condition) (payloadTerm reading (codes block registered) occurrence arguments) ::
    (signature.methodAssumptions (assumptions := assumptions) predicate).map (HOL.subst images)

def scopedSourceFieldEvidence
    (images : Subst Const
      (recursiveSignature block registered (guards := guards) rho numeral zero successor bottomCode constructorCode).constructorContext Ξ)
    (occurrence : Fin ((codes block registered).map reading.fields).length)
    (arguments : Arguments Const Ξ (reading.fields (codeAt reading (codes block registered) occurrence))) :
    let signature := recursiveSignature block registered (guards := guards) rho numeral zero successor bottomCode constructorCode
    let images0 : Subst Const Γ signature.constructorContext := Subst.ofRename signature.constructorRenaming
    guards.Evidence (scopedSourceCaseAssumptions block registered guards rho numeral constructorCode zero successor
      bottomCode predicate assumptions images occurrence arguments)
      (codeAt reading (codes block registered) occurrence) (Subst.comp images (Subst.comp images0 rho)) arguments := by
  apply guards.eliminate
  exact .hyp ⟨0, by simp only [scopedSourceCaseAssumptions, List.length_cons]; omega⟩

theorem scopedSourceFieldEvidence_free
    (images : Subst Const
      (recursiveSignature block registered (guards := guards) rho numeral zero successor bottomCode constructorCode).constructorContext Ξ)
    (occurrence : Fin ((codes block registered).map reading.fields).length)
    (arguments : Arguments Const Ξ (reading.fields (codeAt reading (codes block registered) occurrence))) :
    let signature := recursiveSignature block registered (guards := guards) rho numeral zero successor bottomCode constructorCode
    let images0 : Subst Const Γ signature.constructorContext := Subst.ofRename signature.constructorRenaming
    guards.EvidenceFree (scopedSourceCaseAssumptions block registered guards rho numeral constructorCode zero successor
      bottomCode predicate assumptions images occurrence arguments)
      (codeAt reading (codes block registered) occurrence) (Subst.comp images (Subst.comp images0 rho)) arguments
      (scopedSourceFieldEvidence block registered guards rho numeral constructorCode zero successor
        bottomCode predicate assumptions images occurrence arguments) := by
  apply guards.eliminate_free
  trivial

def scopedSourceChildConditions
    (images : Subst Const
      (recursiveSignature block registered (guards := guards) rho numeral zero successor bottomCode constructorCode).constructorContext Ξ)
    (occurrence : Fin ((codes block registered).map reading.fields).length)
    (arguments : Arguments Const Ξ (reading.fields (codeAt reading (codes block registered) occurrence))) :
    let signature := recursiveSignature block registered (guards := guards) rho numeral zero successor bottomCode constructorCode
    ProofSyntax Const (scopedSourceCaseAssumptions block registered guards rho numeral constructorCode zero successor
      bottomCode predicate assumptions images occurrence arguments)
      ((signature.constructorScope.subst images).childConditions
        (HOL.subst images (weaken (weaken (weaken predicate))))
        (payloadTerm reading (codes block registered) occurrence arguments)
        (HOL.subst images signature.constructorChildren)) := by
  let signature := recursiveSignature block registered (guards := guards) rho numeral zero successor bottomCode constructorCode
  let predicate3 : Term Const signature.constructorContext (space ⇒ .prop) :=
    weaken (weaken (weaken predicate))
  let payload := payloadTerm reading (codes block registered) occurrence arguments
  let hypotheses := scopedSourceCaseAssumptions block registered guards rho numeral constructorCode zero successor
    bottomCode predicate assumptions images occurrence arguments
  have original : ProofSyntax Const hypotheses
      (.app (HOL.subst images (signature.constructorScope.childPredicate predicate3 signature.constructorChildren)) payload) :=
    .hyp ⟨1, by simp only [hypotheses, scopedSourceCaseAssumptions, List.length_cons]; omega⟩
  have transported : ProofSyntax Const hypotheses
      (.app ((signature.constructorScope.subst images).childPredicate
        (HOL.subst images predicate3) (HOL.subst images signature.constructorChildren)) payload) :=
    .castIndices rfl (congrArg (fun term => Term.app term payload)
      (signature.constructorScope.childPredicate_subst predicate3 signature.constructorChildren images)) original
  exact .impE (.eqPropEL ((signature.constructorScope.subst images).childPredicate_beta
    (HOL.subst images predicate3) payload (HOL.subst images signature.constructorChildren))) transported

theorem scopedSourceChildConditions_free
    (images : Subst Const
      (recursiveSignature block registered (guards := guards) rho numeral zero successor bottomCode constructorCode).constructorContext Ξ)
    (occurrence : Fin ((codes block registered).map reading.fields).length)
    (arguments : Arguments Const Ξ (reading.fields (codeAt reading (codes block registered) occurrence))) :
    (scopedSourceChildConditions block registered guards rho numeral constructorCode zero successor
      bottomCode predicate assumptions images occurrence arguments).FunctionExtensionalityFree := by
  unfold scopedSourceChildConditions
  constructor
  · exact RecursiveSpacePredicate.Contextual.childPredicate_beta_free _ _ _ _
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    trivial

#print axioms scopedSourceFieldEvidence_free
#print axioms scopedSourceChildConditions_free

end Mettapedia.GSLT.LanguageDef.AdmittedContainerHOL
