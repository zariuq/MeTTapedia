import Mettapedia.Logic.HOL.IndexedContainerConstructorPrograms
import Mettapedia.Logic.HOL.CurriedPredicateProofs
import Mettapedia.Logic.HOL.Syntax.SubstitutionExtension

/-!
# Retained field proofs for registered constructor descriptions

Typed substitutions act on the generated predicates and result programs.
The proof producer follows the original code, consumes primitive field
evidence and uses explicit beta and propositional inferences.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL.IndexedContainerPositionTerms
open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.TypeTheory.IndexedPositiveContainer
open CurriedPredicates FiniteConstructorEncoding
universe u v w
variable {I : Interface.{u}} {registry : Registry I} {Base : Type v}
  {Const : Ty Base → Type w} {parameters : Nat} {Γ Δ : Ctx Base}

namespace Reading
variable (reading : Reading I registry Const)

theorem resultProgram_subst : ∀ {context : List I.SortCode} (code : Code I registry parameters context)
    {Γ Δ : Ctx Base} (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (theta : Subst Const Γ Δ),
    HOL.subst theta (reading.resultProgram code rho) = reading.resultProgram code (Subst.comp theta rho)
  | _, .result _, _, _, _, _ => HOL.subst_comp _ _ _
  | _, .data _ body, _, _, rho, theta => by
      simp only [resultProgram, HOL.subst]
      rw [resultProgram_subst body (Subst.lift rho) (Subst.lift theta), Subst.lift_comp_eq]
  | _, .recursive _ rest, _, _, rho, theta => resultProgram_subst rest rho theta
  | _, .nested _ _ _ _ _ rest, _, _, rho, theta => by
      simp only [resultProgram, HOL.subst]
      rw [resultProgram_subst rest _ (Subst.lift theta)]
      apply congrArg Term.lam
      apply congrArg (reading.resultProgram rest)
      funext type entry
      exact HOL.subst_weaken theta (rho entry)

theorem resultProgram_instantiate_data {context : List I.SortCode} (sort : I.SortCode)
    (body : Code I registry parameters (sort :: context))
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (argument : Term Const Γ (reading.indices.sort sort)) :
    instantiate argument (reading.resultProgram body (Subst.lift rho)) =
      reading.resultProgram body (Subst.cons argument rho) := by
  rw [instantiate, reading.resultProgram_subst, Subst.single_lift_eq_cons]

theorem resultProgram_instantiate_weaken {context : List I.SortCode} (code : Code I registry parameters context)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    {domain : Ty Base} (argument : Term Const Γ domain) :
    instantiate argument (reading.resultProgram code (fun entry => weaken (rho entry))) =
      reading.resultProgram code rho := by
  rw [instantiate, reading.resultProgram_subst]
  apply congrArg (reading.resultProgram code)
  funext type entry
  exact instantiate_weaken argument (rho entry)

def indexTerm : {context : List I.SortCode} → (code : Code I registry parameters context) →
    {Γ : Ctx Base} → Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ →
    Arguments Const Γ (reading.fields code) → Term Const Γ reading.indices.index
  | _, .result expression, _, rho, _ => HOL.subst rho (reading.indices.term expression)
  | _, .data _ body, _, rho, arguments => indexTerm body (Subst.cons arguments.1 rho) arguments.2
  | _, .recursive _ rest, _, rho, arguments => indexTerm rest rho arguments
  | _, .nested _ _ _ _ _ rest, _, rho, arguments => indexTerm rest rho arguments.2

def resultProof {assumptions : List (Formula Const Γ)} :
    {context : List I.SortCode} → (code : Code I registry parameters context) →
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ) →
    (arguments : Arguments Const Γ (reading.fields code)) →
    ProofSyntax Const assumptions (.eq (applyFields (reading.fields code) (reading.resultProgram code rho) arguments)
      (reading.indexTerm code rho arguments))
  | _, .result _, _, _ => .eqRefl _
  | _, .data sort body, rho, arguments => by
      have beta := applyFields_beta (assumptions := assumptions) (reading.fields body)
        (reading.resultProgram body (Subst.lift rho)) arguments.1 arguments.2
      have beta' := ProofSyntax.castIndices rfl
        (congrArg (fun target => Term.eq
          (applyFields (reading.fields body) (.app (.lam (reading.resultProgram body (Subst.lift rho))) arguments.1) arguments.2)
          (applyFields (reading.fields body) target arguments.2))
          (reading.resultProgram_instantiate_data sort body rho arguments.1)) beta
      exact .eqTrans beta' (resultProof body (Subst.cons arguments.1 rho) arguments.2)
  | _, .recursive _ rest, rho, arguments => resultProof rest rho arguments
  | _, .nested _ _ _ _ _ rest, rho, arguments => by
      have beta := applyFields_beta (assumptions := assumptions) (reading.fields rest)
        (reading.resultProgram rest (fun entry => weaken (rho entry))) arguments.1 arguments.2
      have beta' := ProofSyntax.castIndices rfl
        (congrArg (fun target => Term.eq
          (applyFields (reading.fields rest)
            (.app (.lam (reading.resultProgram rest (fun entry => weaken (rho entry)))) arguments.1) arguments.2)
          (applyFields (reading.fields rest) target arguments.2))
          (reading.resultProgram_instantiate_weaken rest rho arguments.1)) beta
      exact .eqTrans beta' (resultProof rest rho arguments.2)

theorem resultProof_free {assumptions : List (Formula Const Γ)} :
    ∀ {context : List I.SortCode} (code : Code I registry parameters context)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (arguments : Arguments Const Γ (reading.fields code)),
    (reading.resultProof (assumptions := assumptions) code rho arguments).FunctionExtensionalityFree
  | _, .result _, _, _ => True.intro
  | _, .data _ body, rho, arguments => by
      unfold resultProof
      constructor
      · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
        exact applyFields_beta_free _ _ _ _
      · exact resultProof_free body (Subst.cons arguments.1 rho) arguments.2
  | _, .recursive _ rest, rho, arguments => resultProof_free rest rho arguments
  | _, .nested _ _ _ _ _ rest, rho, arguments => by
      unfold resultProof
      constructor
      · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
        exact applyFields_beta_free _ _ _ _
      · exact resultProof_free rest rho arguments.2

end Reading

namespace FieldGuards
variable {reading : Reading I registry Const} (guards : FieldGuards reading)

theorem compile_subst : ∀ {context : List I.SortCode} (code : Code I registry parameters context)
    {Γ Δ : Ctx Base} (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (theta : Subst Const Γ Δ),
    HOL.subst theta (guards.compile code rho) = guards.compile code (Subst.comp theta rho)
  | _, .result _, _, _, _, _ => rfl
  | _, .data _ body, _, _, rho, theta => by
      simp only [compile, HOL.subst, conjoin_subst, constant_subst, HOL.subst_weaken, Subst.lift]
      rw [compile_subst body (Subst.lift rho) (Subst.lift theta), Subst.lift_comp_eq]
      simp only [HOL.subst_comp]
      rfl
  | _, .recursive _ rest, _, _, rho, theta => compile_subst rest rho theta
  | _, .nested _ _ _ _ _ rest, _, _, rho, theta => by
      simp only [compile, HOL.subst, conjoin_subst, constant_subst, HOL.subst_weaken, Subst.lift]
      rw [compile_subst rest _ (Subst.lift theta)]
      simp only [HOL.subst_comp]
      apply congrArg Term.lam
      apply congrArg (conjoin (reading.fields rest) _)
      apply congrArg (guards.compile rest)
      funext type entry
      exact HOL.subst_weaken theta (rho entry)

theorem compile_instantiate_data {context : List I.SortCode} (sort : I.SortCode)
    (body : Code I registry parameters (sort :: context))
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (argument : Term Const Γ (reading.indices.sort sort)) :
    instantiate argument (guards.compile body (Subst.lift rho)) = guards.compile body (Subst.cons argument rho) := by
  rw [instantiate, guards.compile_subst, Subst.single_lift_eq_cons]

theorem compile_instantiate_weaken {context : List I.SortCode} (code : Code I registry parameters context)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    {domain : Ty Base} (argument : Term Const Γ domain) :
    instantiate argument (guards.compile code (fun entry => weaken (rho entry))) = guards.compile code rho := by
  rw [instantiate, guards.compile_subst]
  apply congrArg (guards.compile code)
  funext type entry
  exact instantiate_weaken argument (rho entry)

def Evidence (assumptions : List (Formula Const Γ)) :
    {context : List I.SortCode} → (code : Code I registry parameters context) →
    Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ →
    Arguments Const Γ (reading.fields code) → Type (max v w)
  | context, .data sort body, rho, arguments =>
      ProofSyntax Const assumptions (.app
        (HOL.subst (reading.parameterSubst (context := context) rho) (guards.value sort)) arguments.1) ×
      Evidence assumptions body (Subst.cons arguments.1 rho) arguments.2
  | _, .result _, _, _ => PUnit
  | _, .recursive _ rest, rho, arguments => Evidence assumptions rest rho arguments
  | _, .nested name entry registered output _ rest, rho, arguments =>
      ProofSyntax Const assumptions (.app (HOL.subst rho (guards.shape name entry registered output)) arguments.1) ×
      Evidence assumptions rest rho arguments.2

def introduce {assumptions : List (Formula Const Γ)} :
    {context : List I.SortCode} → (code : Code I registry parameters context) →
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ) →
    (arguments : Arguments Const Γ (reading.fields code)) → guards.Evidence assumptions code rho arguments →
    ProofSyntax Const assumptions (applyArguments (reading.fields code) (guards.compile code rho) arguments)
  | _, .result _, _, _, _ => .topI
  | context, .data sort body, rho, arguments, evidence => by
      have tail := introduce body (Subst.cons arguments.1 rho) arguments.2 evidence.2
      have tail' := ProofSyntax.castIndices rfl
        (congrArg (fun target => applyArguments (reading.fields body) target arguments.2)
          (guards.compile_instantiate_data sort body rho arguments.1).symm) tail
      exact head_intro (reading.fields body)
        (HOL.subst (reading.parameterSubst (context := context) rho) (guards.value sort))
        (guards.compile body (Subst.lift rho)) arguments.1 arguments.2 evidence.1 tail'
  | _, .recursive _ rest, rho, arguments, evidence => introduce rest rho arguments evidence
  | _, .nested name entry registered output _ rest, rho, arguments, evidence => by
      have tail := introduce rest rho arguments.2 evidence.2
      have tail' := ProofSyntax.castIndices rfl
        (congrArg (fun target => applyArguments (reading.fields rest) target arguments.2)
          (guards.compile_instantiate_weaken rest rho arguments.1).symm) tail
      exact head_intro (reading.fields rest) (HOL.subst rho (guards.shape name entry registered output))
        (guards.compile rest (fun entry => weaken (rho entry))) arguments.1 arguments.2 evidence.1 tail'

def EvidenceFree (assumptions : List (Formula Const Γ)) :
    {context : List I.SortCode} → (code : Code I registry parameters context) →
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ) →
    (arguments : Arguments Const Γ (reading.fields code)) → guards.Evidence assumptions code rho arguments → Prop
  | _, .result _, _, _, _ => True
  | _, .data _ body, rho, arguments, evidence => evidence.1.FunctionExtensionalityFree ∧
      EvidenceFree assumptions body (Subst.cons arguments.1 rho) arguments.2 evidence.2
  | _, .recursive _ rest, rho, arguments, evidence => EvidenceFree assumptions rest rho arguments evidence
  | _, .nested _ _ _ _ _ rest, rho, arguments, evidence => evidence.1.FunctionExtensionalityFree ∧
      EvidenceFree assumptions rest rho arguments.2 evidence.2

theorem introduce_free {assumptions : List (Formula Const Γ)} :
    ∀ {context : List I.SortCode} (code : Code I registry parameters context)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (arguments : Arguments Const Γ (reading.fields code)) (evidence : guards.Evidence assumptions code rho arguments),
    guards.EvidenceFree assumptions code rho arguments evidence →
      (guards.introduce code rho arguments evidence).FunctionExtensionalityFree
  | _, .result _, _, _, _, _ => True.intro
  | _, .data _ body, rho, arguments, evidence, free => by
      unfold introduce
      apply head_intro_free
      · exact free.1
      · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
        exact introduce_free body (Subst.cons arguments.1 rho) arguments.2 evidence.2 free.2
  | _, .recursive _ rest, rho, arguments, evidence, free => introduce_free rest rho arguments evidence free
  | _, .nested _ _ _ _ _ rest, rho, arguments, evidence, free => by
      unfold introduce
      apply head_intro_free
      · exact free.1
      · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
        exact introduce_free rest rho arguments.2 evidence.2 free.2

#print axioms compile_subst
#print axioms introduce_free
end FieldGuards

def inventoryArguments (reading : Reading I registry Const) {context : List I.SortCode}
    (codes : List (Code I registry parameters context)) (occurrence : Fin (codes.map reading.fields).length)
    (arguments : Arguments Const Γ (reading.fields (codeAt reading codes occurrence))) :
    Arguments Const Γ ((codes.map reading.fields).get occurrence) :=
  (fields_get reading codes occurrence).symm ▸ arguments

def payloadTerm (reading : Reading I registry Const) {context : List I.SortCode}
    (codes : List (Code I registry parameters context)) (occurrence : Fin (codes.map reading.fields).length)
    (arguments : Arguments Const Γ (reading.fields (codeAt reading codes occurrence))) :
    Term Const Γ (payloadType (codes.map reading.fields)) :=
  encode (codes.map reading.fields) occurrence (inventoryArguments reading codes occurrence arguments)

private def reindexConditionProof {assumptions : List (Formula Const Γ)}
    {first second : List (Ty Base)} (same : first = second)
    (condition : Term Const Γ (handlerType second)) (arguments : Arguments Const Γ second)
    (proof : ProofSyntax Const assumptions (applyArguments second condition arguments)) :
    ProofSyntax Const assumptions (applyArguments first (same.symm ▸ condition) (same.symm ▸ arguments)) := by
  cases same
  exact proof

private theorem reindexConditionProof_free {assumptions : List (Formula Const Γ)}
    {first second : List (Ty Base)} (same : first = second)
    (condition : Term Const Γ (handlerType second)) (arguments : Arguments Const Γ second)
    (proof : ProofSyntax Const assumptions (applyArguments second condition arguments))
    (free : proof.FunctionExtensionalityFree) :
    (reindexConditionProof same condition arguments proof).FunctionExtensionalityFree := by
  cases same
  exact free

private theorem applyFields_reindex {first second : List (Ty Base)} (same : first = second)
    {result : Ty Base} (function : Term Const Γ (FunctionType second result)) (arguments : Arguments Const Γ second) :
    applyFields first (same.symm ▸ function) (same.symm ▸ arguments) = applyFields second function arguments := by
  cases same
  rfl

namespace FieldGuards
variable {reading : Reading I registry Const} (guards : FieldGuards reading)

def inventoryFieldProof {assumptions : List (Formula Const Γ)} {context : List I.SortCode}
    (codes : List (Code I registry parameters context))
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (numeral : Nat → Term Const Γ reading.number) (occurrence : Fin (codes.map reading.fields).length)
    (arguments : Arguments Const Γ (reading.fields (codeAt reading codes occurrence)))
    (evidence : guards.Evidence assumptions (codeAt reading codes occurrence) rho arguments) :
    ProofSyntax Const assumptions (applyArguments ((codes.map reading.fields).get occurrence)
      ((guards.constructors codes rho numeral).allowed occurrence) (inventoryArguments reading codes occurrence arguments)) :=
  reindexConditionProof (fields_get reading codes occurrence) _ arguments
    (guards.introduce (codeAt reading codes occurrence) rho arguments evidence)

def payloadProof {assumptions : List (Formula Const Γ)} {context : List I.SortCode}
    (codes : List (Code I registry parameters context))
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (numeral : Nat → Term Const Γ reading.number) (occurrence : Fin (codes.map reading.fields).length)
    (arguments : Arguments Const Γ (reading.fields (codeAt reading codes occurrence)))
    (evidence : guards.Evidence assumptions (codeAt reading codes occurrence) rho arguments) :
    ProofSyntax Const assumptions
      (ConstructorDataPredicates.guard (codes.map reading.fields) (guards.constructors codes rho numeral).allowed
        (payloadTerm reading codes occurrence arguments)) :=
  ConstructorDataPredicates.introduce _ _ occurrence (inventoryArguments reading codes occurrence arguments)
    (guards.inventoryFieldProof codes rho numeral occurrence arguments evidence)

def shapeProof {assumptions : List (Formula Const Γ)} {context : List I.SortCode}
    (codes : List (Code I registry parameters context))
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (numeral : Nat → Term Const Γ reading.number) (occurrence : Fin (codes.map reading.fields).length)
    (arguments : Arguments Const Γ (reading.fields (codeAt reading codes occurrence)))
    (evidence : guards.Evidence assumptions (codeAt reading codes occurrence) rho arguments) :
    ProofSyntax Const assumptions ((guards.constructors codes rho numeral).shapeGuard (numeral occurrence.val)
      (payloadTerm reading codes occurrence arguments)) :=
  ConstructorDataPredicates.introduce _ _ occurrence (inventoryArguments reading codes occurrence arguments)
    (conjoin_intro _ (inventoryArguments reading codes occurrence arguments)
      (guards.inventoryFieldProof codes rho numeral occurrence arguments evidence)
      (constant_intro _ (inventoryArguments reading codes occurrence arguments) (.eqRefl (numeral occurrence.val))))

def inventoryResultProof {assumptions : List (Formula Const Γ)} {context : List I.SortCode}
    (codes : List (Code I registry parameters context))
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (numeral : Nat → Term Const Γ reading.number) (occurrence : Fin (codes.map reading.fields).length)
    (arguments : Arguments Const Γ (reading.fields (codeAt reading codes occurrence))) :
    ProofSyntax Const assumptions (.eq
      (applyFields ((codes.map reading.fields).get occurrence) ((guards.constructors codes rho numeral).result occurrence)
        (inventoryArguments reading codes occurrence arguments))
      (reading.indexTerm (codeAt reading codes occurrence) rho arguments)) :=
  ProofSyntax.castIndices rfl
    (congrArg (fun term => Term.eq term (reading.indexTerm (codeAt reading codes occurrence) rho arguments))
      (applyFields_reindex (fields_get reading codes occurrence) _ arguments).symm)
    (reading.resultProof (codeAt reading codes occurrence) rho arguments)

def resultGuardProof {assumptions : List (Formula Const Γ)} {context : List I.SortCode}
    (codes : List (Code I registry parameters context))
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (numeral : Nat → Term Const Γ reading.number) (occurrence : Fin (codes.map reading.fields).length)
    (arguments : Arguments Const Γ (reading.fields (codeAt reading codes occurrence)))
    (evidence : guards.Evidence assumptions (codeAt reading codes occurrence) rho arguments) :
    ProofSyntax Const assumptions ((guards.constructors codes rho numeral).resultGuard
      (payloadTerm reading codes occurrence arguments) (reading.indexTerm (codeAt reading codes occurrence) rho arguments)) :=
  ConstructorDataPredicates.introduce _ _ occurrence (inventoryArguments reading codes occurrence arguments)
    (conjoin_intro _ (inventoryArguments reading codes occurrence arguments)
      (guards.inventoryFieldProof codes rho numeral occurrence arguments evidence)
      (equalTo_intro _ _ _ (inventoryArguments reading codes occurrence arguments)
        (guards.inventoryResultProof codes rho numeral occurrence arguments)))

theorem inventoryFieldProof_free {assumptions : List (Formula Const Γ)} {context : List I.SortCode}
    (codes : List (Code I registry parameters context))
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (numeral : Nat → Term Const Γ reading.number) (occurrence : Fin (codes.map reading.fields).length)
    (arguments : Arguments Const Γ (reading.fields (codeAt reading codes occurrence)))
    (evidence : guards.Evidence assumptions (codeAt reading codes occurrence) rho arguments)
    (free : guards.EvidenceFree assumptions (codeAt reading codes occurrence) rho arguments evidence) :
    (guards.inventoryFieldProof codes rho numeral occurrence arguments evidence).FunctionExtensionalityFree :=
  reindexConditionProof_free _ _ _ _ (guards.introduce_free _ _ _ _ free)

theorem payloadProof_free {assumptions : List (Formula Const Γ)} {context : List I.SortCode}
    (codes : List (Code I registry parameters context))
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (numeral : Nat → Term Const Γ reading.number) (occurrence : Fin (codes.map reading.fields).length)
    (arguments : Arguments Const Γ (reading.fields (codeAt reading codes occurrence)))
    (evidence : guards.Evidence assumptions (codeAt reading codes occurrence) rho arguments)
    (free : guards.EvidenceFree assumptions (codeAt reading codes occurrence) rho arguments evidence) :
    (guards.payloadProof codes rho numeral occurrence arguments evidence).FunctionExtensionalityFree :=
  ConstructorDataPredicates.introduce_free _ _ _ _ _
    (guards.inventoryFieldProof_free codes rho numeral occurrence arguments evidence free)

theorem shapeProof_free {assumptions : List (Formula Const Γ)} {context : List I.SortCode}
    (codes : List (Code I registry parameters context))
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (numeral : Nat → Term Const Γ reading.number) (occurrence : Fin (codes.map reading.fields).length)
    (arguments : Arguments Const Γ (reading.fields (codeAt reading codes occurrence)))
    (evidence : guards.Evidence assumptions (codeAt reading codes occurrence) rho arguments)
    (free : guards.EvidenceFree assumptions (codeAt reading codes occurrence) rho arguments evidence) :
    (guards.shapeProof codes rho numeral occurrence arguments evidence).FunctionExtensionalityFree :=
  ConstructorDataPredicates.introduce_free _ _ _ _ _
    (conjoin_intro_free _ _ _ _
      (guards.inventoryFieldProof_free codes rho numeral occurrence arguments evidence free)
      (constant_intro_free _ _ _ True.intro))

theorem inventoryResultProof_free {assumptions : List (Formula Const Γ)} {context : List I.SortCode}
    (codes : List (Code I registry parameters context))
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (numeral : Nat → Term Const Γ reading.number) (occurrence : Fin (codes.map reading.fields).length)
    (arguments : Arguments Const Γ (reading.fields (codeAt reading codes occurrence))) :
    (guards.inventoryResultProof (assumptions := assumptions) codes rho numeral occurrence arguments).FunctionExtensionalityFree := by
  unfold inventoryResultProof
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact reading.resultProof_free _ _ _

theorem resultGuardProof_free {assumptions : List (Formula Const Γ)} {context : List I.SortCode}
    (codes : List (Code I registry parameters context))
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (numeral : Nat → Term Const Γ reading.number) (occurrence : Fin (codes.map reading.fields).length)
    (arguments : Arguments Const Γ (reading.fields (codeAt reading codes occurrence)))
    (evidence : guards.Evidence assumptions (codeAt reading codes occurrence) rho arguments)
    (free : guards.EvidenceFree assumptions (codeAt reading codes occurrence) rho arguments evidence) :
    (guards.resultGuardProof codes rho numeral occurrence arguments evidence).FunctionExtensionalityFree :=
  ConstructorDataPredicates.introduce_free _ _ _ _ _
    (conjoin_intro_free _ _ _ _
      (guards.inventoryFieldProof_free codes rho numeral occurrence arguments evidence free)
      (equalTo_intro_free _ _ _ _ _ (guards.inventoryResultProof_free codes rho numeral occurrence arguments)))

#print axioms resultGuardProof_free

end FieldGuards
end Mettapedia.Logic.HOL.IndexedContainerPositionTerms
