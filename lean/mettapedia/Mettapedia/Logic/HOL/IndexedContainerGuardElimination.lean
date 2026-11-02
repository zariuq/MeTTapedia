import Mettapedia.Logic.HOL.IndexedContainerFieldProofs

/-!
# Recovering retained evidence from generated field guards

Elimination follows the same constructor description and source field order
as guard introduction. Recursive membership stays in the separate child
condition; data and nested-shape guards recover their actual premise proofs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.CurriedPredicates

open FiniteConstructorEncoding
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}

def applyLam_elim {assumptions : List (Formula Const Γ)} {domain : Ty Base}
    (fields : List (Ty Base)) (body : Term Const (domain :: Γ) (handlerType fields))
    (argument : Term Const Γ domain) (arguments : Arguments Const Γ fields)
    (present : ProofSyntax Const assumptions
      (applyArguments (domain :: fields) (.lam body) (argument, arguments))) :
    ProofSyntax Const assumptions (applyArguments fields (instantiate argument body) arguments) :=
  .impE (.eqPropEL (applyArguments_congr fields _ _ arguments (.beta argument body))) present

theorem applyLam_elim_free {assumptions : List (Formula Const Γ)} {domain : Ty Base}
    (fields : List (Ty Base)) (body : Term Const (domain :: Γ) (handlerType fields))
    (argument : Term Const Γ domain) (arguments : Arguments Const Γ fields)
    (present : ProofSyntax Const assumptions
      (applyArguments (domain :: fields) (.lam body) (argument, arguments)))
    (free : present.FunctionExtensionalityFree) :
    (applyLam_elim fields body argument arguments present).FunctionExtensionalityFree := by
  constructor
  · exact applyArguments_congr_free _ _ _ _ _ True.intro
  · exact free

def head_elim {assumptions : List (Formula Const Γ)} {domain : Ty Base}
    (fields : List (Ty Base)) (predicate : Term Const Γ (domain ⇒ .prop))
    (body : Term Const (domain :: Γ) (handlerType fields))
    (argument : Term Const Γ domain) (arguments : Arguments Const Γ fields)
    (present : ProofSyntax Const assumptions (applyArguments (domain :: fields)
      (.lam (conjoin fields (constant fields (.app (weaken predicate) (.var .vz))) body)) (argument, arguments))) :
    ProofSyntax Const assumptions (.and (.app predicate argument)
      (applyArguments fields (instantiate argument body) arguments)) := by
  have applied := applyLam_elim fields _ argument arguments present
  have instantiated : ProofSyntax Const assumptions
      (applyArguments fields (conjoin fields (constant fields (.app predicate argument))
        (instantiate argument body)) arguments) :=
    .castIndices rfl (congrArg (fun term => applyArguments fields term arguments)
      (instantiate_head_body fields predicate body argument)) applied
  have components := ProofSyntax.impE (.eqPropEL (conjoin_beta fields
    (constant fields (.app predicate argument)) (instantiate argument body) arguments)) instantiated
  exact .andI (.impE (.eqPropEL (constant_beta fields (.app predicate argument) arguments)) (.andEL components))
    (.andER components)

theorem head_elim_free {assumptions : List (Formula Const Γ)} {domain : Ty Base}
    (fields : List (Ty Base)) (predicate : Term Const Γ (domain ⇒ .prop))
    (body : Term Const (domain :: Γ) (handlerType fields))
    (argument : Term Const Γ domain) (arguments : Arguments Const Γ fields)
    (present : ProofSyntax Const assumptions (applyArguments (domain :: fields)
      (.lam (conjoin fields (constant fields (.app (weaken predicate) (.var .vz))) body)) (argument, arguments)))
    (free : present.FunctionExtensionalityFree) :
    (head_elim fields predicate body argument arguments present).FunctionExtensionalityFree := by
  unfold head_elim
  have shared : ∀ (proof : ProofSyntax Const assumptions
      (applyArguments fields (conjoin fields (constant fields (.app predicate argument))
        (instantiate argument body)) arguments)), proof.FunctionExtensionalityFree →
      (ProofSyntax.impE (.eqPropEL (conjoin_beta fields (constant fields (.app predicate argument))
        (instantiate argument body) arguments)) proof).FunctionExtensionalityFree := by
    intro proof proofFree
    exact ⟨conjoin_beta_free _ _ _ _, proofFree⟩
  constructor
  · constructor
    · exact constant_beta_free _ _ _
    · apply shared
      apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      exact applyLam_elim_free _ _ _ _ _ free
  · apply shared
    apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    exact applyLam_elim_free _ _ _ _ _ free

end Mettapedia.Logic.HOL.CurriedPredicates

namespace Mettapedia.Logic.HOL.IndexedContainerPositionTerms.FieldGuards

open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.TypeTheory.IndexedPositiveContainer
open CurriedPredicates FiniteConstructorEncoding
universe u v w
variable {I : Interface.{u}} {registry : Registry I} {Base : Type v}
    {Const : Ty Base → Type w} {parameters : Nat} {Γ : Ctx Base}
    {reading : Reading I registry Const} (guards : FieldGuards reading)

def eliminate {assumptions : List (Formula Const Γ)} :
    {context : List I.SortCode} → (code : Code I registry parameters context) →
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ) →
    (arguments : Arguments Const Γ (reading.fields code)) →
    ProofSyntax Const assumptions (applyArguments (reading.fields code) (guards.compile code rho) arguments) →
    guards.Evidence assumptions code rho arguments
  | _, .result _, _, _, _ => PUnit.unit
  | context, .data sort body, rho, arguments, present => by
      have components := head_elim (reading.fields body)
        (HOL.subst (reading.parameterSubst (context := context) rho) (guards.value sort))
        (guards.compile body (Subst.lift rho)) arguments.1 arguments.2 present
      have tail := ProofSyntax.castIndices rfl
        (congrArg (fun target => applyArguments (reading.fields body) target arguments.2)
          (guards.compile_instantiate_data sort body rho arguments.1)) (.andER components)
      exact ⟨.andEL components, eliminate body (Subst.cons arguments.1 rho) arguments.2 tail⟩
  | _, .recursive _ rest, rho, arguments, present => eliminate rest rho arguments present
  | _, .nested name entry registered output _ rest, rho, arguments, present => by
      have components := head_elim (reading.fields rest) (HOL.subst rho (guards.shape name entry registered output))
        (guards.compile rest (fun value => weaken (rho value))) arguments.1 arguments.2 present
      have tail := ProofSyntax.castIndices rfl
        (congrArg (fun target => applyArguments (reading.fields rest) target arguments.2)
          (guards.compile_instantiate_weaken rest rho arguments.1)) (.andER components)
      exact ⟨.andEL components, eliminate rest rho arguments.2 tail⟩

theorem eliminate_free {assumptions : List (Formula Const Γ)} :
    ∀ {context : List I.SortCode} (code : Code I registry parameters context)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (arguments : Arguments Const Γ (reading.fields code))
    (present : ProofSyntax Const assumptions (applyArguments (reading.fields code) (guards.compile code rho) arguments)),
    present.FunctionExtensionalityFree →
      guards.EvidenceFree assumptions code rho arguments (guards.eliminate code rho arguments present)
  | _, .result _, _, _, _, _ => True.intro
  | _, .data _ body, rho, arguments, present, free => by
      unfold eliminate
      constructor
      · exact head_elim_free _ _ _ _ _ _ free
      · apply eliminate_free
        apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
        exact head_elim_free _ _ _ _ _ _ free
  | _, .recursive _ rest, rho, arguments, present, free => eliminate_free rest rho arguments present free
  | _, .nested _ _ _ _ _ rest, rho, arguments, present, free => by
      unfold eliminate
      constructor
      · exact head_elim_free _ _ _ _ _ _ free
      · apply eliminate_free
        apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
        exact head_elim_free _ _ _ _ _ _ free

#print axioms eliminate
#print axioms eliminate_free

end Mettapedia.Logic.HOL.IndexedContainerPositionTerms.FieldGuards
