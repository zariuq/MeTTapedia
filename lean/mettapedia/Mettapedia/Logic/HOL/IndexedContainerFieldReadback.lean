import Mettapedia.Logic.HOL.IndexedContainerFieldProofs

/-!
# Retained readback of registered field guards

Elimination follows the original constructor description and recovers every
primitive field proof. Recursive positions keep the same field telescope;
nested positions retain their original shape predicate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.CurriedPredicates
open FiniteConstructorEncoding
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
  {assumptions : List (Formula Const Γ)} {domain : Ty Base}

def head_parts (fields : List (Ty Base)) (predicate : Term Const Γ (domain ⇒ .prop))
    (body : Term Const (domain :: Γ) (handlerType fields))
    (argument : Term Const Γ domain) (arguments : Arguments Const Γ fields)
    (present : ProofSyntax Const assumptions (applyArguments (domain :: fields)
      (.lam (conjoin fields (constant fields (.app (weaken predicate) (.var .vz))) body))
      (argument, arguments))) :
    ProofSyntax Const assumptions (.and (.app predicate argument)
      (applyArguments fields (instantiate argument body) arguments)) := by
  have reduced := ProofSyntax.impE (ProofSyntax.eqPropEL
    (applyArguments_congr fields _ _ arguments (.beta argument _))) present
  have combined := ProofSyntax.castIndices rfl
    (congrArg (fun term => applyArguments fields term arguments)
      (instantiate_head_body fields predicate body argument)) reduced
  have parts := ProofSyntax.impE (ProofSyntax.eqPropEL (conjoin_beta fields _ _ arguments)) combined
  exact .andI (.impE (.eqPropEL (constant_beta fields (.app predicate argument) arguments)) (.andEL parts))
    (.andER parts)

theorem head_parts_free (fields : List (Ty Base)) (predicate : Term Const Γ (domain ⇒ .prop))
    (body : Term Const (domain :: Γ) (handlerType fields))
    (argument : Term Const Γ domain) (arguments : Arguments Const Γ fields)
    (present : ProofSyntax Const assumptions (applyArguments (domain :: fields)
      (.lam (conjoin fields (constant fields (.app (weaken predicate) (.var .vz))) body))
      (argument, arguments))) (free : present.FunctionExtensionalityFree) :
    (head_parts fields predicate body argument arguments present).FunctionExtensionalityFree := by
  unfold head_parts
  have betaFree := applyArguments_congr_free fields _ _ arguments
    (ProofSyntax.beta (Δ := assumptions) argument
      (conjoin fields (constant fields (.app (weaken predicate) (.var .vz))) body)) (by trivial)
  simp only [ProofSyntax.FunctionExtensionalityFree, ProofSyntax.functionExtensionalityFree_castIndices,
    conjoin_beta_free, constant_beta_free, free, betaFree, and_self]

end Mettapedia.Logic.HOL.CurriedPredicates

namespace Mettapedia.Logic.HOL.IndexedContainerPositionTerms.FieldGuards
open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.TypeTheory.IndexedPositiveContainer
open CurriedPredicates FiniteConstructorEncoding
universe u v w
variable {I : Interface.{u}} {registry : Registry I} {Base : Type v}
  {Const : Ty Base → Type w} {parameters : Nat} {Γ : Ctx Base}
  {reading : Reading I registry Const} (guards : FieldGuards reading)
  {assumptions : List (Formula Const Γ)}

def readEvidence : {context : List I.SortCode} → (code : Code I registry parameters context) →
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ) →
    (arguments : Arguments Const Γ (reading.fields code)) →
    ProofSyntax Const assumptions (applyArguments (reading.fields code) (guards.compile code rho) arguments) →
    guards.Evidence assumptions code rho arguments
  | _, .result _, _, _, _ => PUnit.unit
  | context, .data sort body, rho, arguments, present => by
      have parts := head_parts (reading.fields body)
        (HOL.subst (reading.parameterSubst (context := context) rho) (guards.value sort))
        (guards.compile body (Subst.lift rho)) arguments.1 arguments.2 present
      have tail := ProofSyntax.castIndices rfl
        (congrArg (fun target => applyArguments (reading.fields body) target arguments.2)
          (guards.compile_instantiate_data sort body rho arguments.1)) (ProofSyntax.andER parts)
      exact ⟨.andEL parts, readEvidence body (Subst.cons arguments.1 rho) arguments.2 tail⟩
  | _, .recursive _ rest, rho, arguments, present => readEvidence rest rho arguments present
  | _, .nested name entry registered output _ rest, rho, arguments, present => by
      have parts := head_parts (reading.fields rest) (HOL.subst rho (guards.shape name entry registered output))
        (guards.compile rest (fun entry => weaken (rho entry))) arguments.1 arguments.2 present
      have tail := ProofSyntax.castIndices rfl
        (congrArg (fun target => applyArguments (reading.fields rest) target arguments.2)
          (guards.compile_instantiate_weaken rest rho arguments.1)) (ProofSyntax.andER parts)
      exact ⟨.andEL parts, readEvidence rest rho arguments.2 tail⟩

theorem readEvidence_free : {context : List I.SortCode} → (code : Code I registry parameters context) →
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ) →
    (arguments : Arguments Const Γ (reading.fields code)) →
    (present : ProofSyntax Const assumptions (applyArguments (reading.fields code) (guards.compile code rho) arguments)) →
    present.FunctionExtensionalityFree →
    guards.EvidenceFree assumptions code rho arguments (guards.readEvidence code rho arguments present)
  | _, .result _, _, _, _, _ => True.intro
  | context, .data sort body, rho, arguments, present, free => by
      have partsFree := head_parts_free (reading.fields body)
        (HOL.subst (reading.parameterSubst (context := context) rho) (guards.value sort))
        (guards.compile body (Subst.lift rho)) arguments.1 arguments.2 present free
      refine ⟨partsFree, ?_⟩
      apply readEvidence_free body (Subst.cons arguments.1 rho) arguments.2
      exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr partsFree
  | _, .recursive _ rest, rho, arguments, present, free => readEvidence_free rest rho arguments present free
  | _, .nested name entry registered output _ rest, rho, arguments, present, free => by
      have partsFree := head_parts_free (reading.fields rest) (HOL.subst rho (guards.shape name entry registered output))
        (guards.compile rest (fun entry => weaken (rho entry))) arguments.1 arguments.2 present free
      refine ⟨partsFree, ?_⟩
      apply readEvidence_free rest rho arguments.2
      exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr partsFree

#print axioms readEvidence
#print axioms readEvidence_free
end Mettapedia.Logic.HOL.IndexedContainerPositionTerms.FieldGuards
