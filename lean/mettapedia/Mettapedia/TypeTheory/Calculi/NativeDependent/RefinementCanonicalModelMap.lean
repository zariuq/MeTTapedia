import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSyntacticQualification
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualPredicatePreservation
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractModelUniverseLift
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractModelMap

/-!
# Declaration comparisons of the generated refinement interpretation

The canonical interpreter maps every chosen mixed header successively.
Its primitive family, section and predicate readouts retain the independent
target declarations. Actual comparison isomorphisms connect the chosen
source header to its authored presentation. These local readings assemble
the earned contextual interpretation into a logical model map; no whole
expression or whole derivation compatibility is a field.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.Interpretation

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualPredicateModel
open Mettapedia.TypeTheory.ContextualPredicateModelScopes
open Mettapedia.TypeTheory.ContextualPredicateScopeMorphism
open Mettapedia.TypeTheory.ContextualTelescopeMorphism (imageType imageType_heq)
open Mettapedia.TypeTheory.ContextualComprehensionMorphism
open Mettapedia.TypeTheory.ContextualCwfUniverseLift
open Mettapedia.TypeTheory.ContextualPredicateModelScopeUniverseLift
open Refinement.Abstract
open SyntacticReification

universe u c s t m p z
variable {S : Symbols.{u}} {D : Signature S} {C : CwfWithTerminal.{c,s,t,m}}

noncomputable abbrev sourceData (headers : HeaderFormation D) :=
  (SyntacticModel.data headers).lift.{u,u,u,u,u,u,
    max u z,max u z,max u z,max u z,0}

variable (model : QualifiedModel.{u,c,s,t,m,p} D C)

abbrev targetData := model.data.lift.{u,c,s,t,m,p,
  max u c s t m,max u c s t m,max u c s t m,max u c s t m,0}

private theorem mixed_snoc_equal {E : CwfWithTerminal.{c,s,t,m}}
    {localModel : LocalModel.{c,s,t,m,p} E} {n : Nat}
    {first second : ModelScope E localModel n} (contexts : first = second)
    {A : E.toCwf.Ty first.1} {B : E.toCwf.Ty second.1} (types : HEq A B) :
    first.snoc A = second.snoc B := by
  cases contexts
  cases eq_of_heq types
  rfl

private theorem mixed_assume_equal {E : CwfWithTerminal.{c,s,t,m}}
    {localModel : LocalModel.{c,s,t,m,p} E} {n : Nat}
    {first second : ModelScope E localModel n} (contexts : first = second)
    {φ : localModel.doctrine.Predicate first.1} {ψ : localModel.doctrine.Predicate second.1}
    (predicates : HEq φ ψ) : first.assume φ = second.assume ψ := by
  cases contexts
  cases eq_of_heq predicates
  rfl

/-- The complete mixed image is built binder by binder. Guard assumptions
retain their inclusion and variable readings, as do dependent extensions. -/
theorem scope_image_context : {n : Nat} → {Γ : QuotientCwf.QContext D} →
    (scope : ScopeData (SyntacticModel.C D) (generatedModel D).doctrine
      (generatedModel D).assumptions n Γ) →
    HEq (imageScope (strictMorphism model) (assumptions_preserved model)
      (liftScope.{u,u,u,u,u,max u c s t m,max u c s t m,max u c s t m,max u c s t m,0}
        (⟨Γ,scope⟩ : ModelScope (SyntacticModel.C D) (generatedModel D) n)))
      (liftScope.{c,s,t,m,p,max u c s t m,max u c s t m,max u c s t m,max u c s t m,0}
        (contextValue model Γ.as))
  | _, _, .nil => by
      erw [context_empty]
      rfl
  | _, _, @ScopeData.snoc _ _ _ n Γ previous A => by
      have ih := scope_image_context previous
      have counts := SyntacticScopes.scope_arity previous
      cases counts
      let original : ModelScope (SyntacticModel.C D) (generatedModel D) Γ.as.arity := ⟨Γ,previous⟩
      let lifted := liftScope.{u,u,u,u,u,max u c s t m,max u c s t m,
        max u c s t m,max u c s t m,0} original
      have contexts := eq_of_heq ih
      have types := (imageType_heq (strictMorphism model)
        (imageScope_comparison (strictMorphism model) (assumptions_preserved model) lifted).contexts
        (ULift.up A)).symm
      change HEq ((imageScope (strictMorphism model) (assumptions_preserved model) lifted).snoc
        (imageType (strictMorphism model)
          (imageScope_comparison (strictMorphism model) (assumptions_preserved model) lifted).contexts
          (ULift.up A))) _
      erw [represented_extension, liftScope_snoc]
      exact heq_of_eq (mixed_snoc_equal contexts types)
  | _, _, @ScopeData.assume _ _ _ n Γ previous φ => by
      have ih := scope_image_context previous
      have counts := SyntacticScopes.scope_arity previous
      cases counts
      let original : ModelScope (SyntacticModel.C D) (generatedModel D) Γ.as.arity := ⟨Γ,previous⟩
      let lifted := liftScope.{u,u,u,u,u,max u c s t m,max u c s t m,
        max u c s t m,max u c s t m,0} original
      have contexts := eq_of_heq ih
      have predicates := (imagePredicate_heq (doctrine_preserved model)
        (imageScope_comparison (strictMorphism model) (assumptions_preserved model) lifted).contexts
        (ULift.up φ)).symm
      change HEq ((imageScope (strictMorphism model) (assumptions_preserved model) lifted).assume
        (imagePredicate (doctrine_preserved model)
          (imageScope_comparison (strictMorphism model) (assumptions_preserved model) lifted).contexts
          (ULift.up φ))) _
      erw [represented_assumption, liftScope_assume]
      exact heq_of_eq (mixed_assume_equal contexts predicates)

/-- A generated context equation retains the complete satisfying scope. -/
theorem selected_context_value (raw : Context D) :
    contextValue model (Presentation.selectedContext raw) = contextValue model raw := by
  let selection := Presentation.select raw.raw raw.formed
  exact Abstract.Derivation.contextValue_equation model.data model.realization
    model.products_substitution model.products_beta model.products_eta
    (Classical.choice (Presentation.selectedContext raw).formed.judgment)
    (Classical.choice raw.formed.judgment) (Classical.choice selection.equivalent)

theorem type_header_value (headers : HeaderFormation D) (symbol : S.TypeSymbol) :
    contextValue model (Presentation.selectedContext (SyntacticModel.typeHeader headers symbol)) =
      model.data.typeParameters symbol :=
  (selected_context_value model (SyntacticModel.typeHeader headers symbol)).trans
    (Option.some.inj ((context_readout model (SyntacticModel.typeHeader headers symbol)).symm.trans
      (model.realization.typeHeader symbol)))

theorem term_header_value (headers : HeaderFormation D) (symbol : S.TermSymbol) :
    contextValue model (Presentation.selectedContext (SyntacticModel.termHeader headers symbol)) =
      model.data.termParameters symbol :=
  (selected_context_value model (SyntacticModel.termHeader headers symbol)).trans
    (Option.some.inj ((context_readout model (SyntacticModel.termHeader headers symbol)).symm.trans
      (model.realization.termHeader symbol)))

theorem predicate_header_value (headers : HeaderFormation D) (symbol : S.PredicateSymbol) :
    contextValue model (Presentation.selectedContext (SyntacticModel.predicateHeader headers symbol)) =
      model.data.predicateParameters symbol :=
  (selected_context_value model (SyntacticModel.predicateHeader headers symbol)).trans
    (Option.some.inj ((context_readout model (SyntacticModel.predicateHeader headers symbol)).symm.trans
      (model.realization.predicateHeader symbol)))

theorem type_parameter_image (headers : HeaderFormation D) (symbol : S.TypeSymbol) :
    ScopeImage (strictMorphism model)
      ((sourceData.{u,max c s t m} headers).typeParameters symbol)
      ((targetData model).typeParameters symbol) := by
  let header := SyntacticModel.typeHeader headers symbol
  have selected := scope_image_context model (Presentation.selectedScopeData header)
  have actual := heq_of_eq (congrArg
    (liftScope.{c,s,t,m,p,max u c s t m,max u c s t m,max u c s t m,max u c s t m,0})
    (type_header_value model headers symbol))
  have contexts := eq_of_heq (selected.trans actual)
  change ScopeImage (strictMorphism model)
    (liftScope.{u,u,u,u,u,max u c s t m,max u c s t m,max u c s t m,max u c s t m,0}
      (SyntacticModel.parameterScope header))
    (liftScope.{c,s,t,m,p,max u c s t m,max u c s t m,max u c s t m,max u c s t m,0} _)
  rw [← contexts]
  exact imageScope_comparison (strictMorphism model) (assumptions_preserved model) _

theorem term_parameter_image (headers : HeaderFormation D) (symbol : S.TermSymbol) :
    ScopeImage (strictMorphism model)
      ((sourceData.{u,max c s t m} headers).termParameters symbol)
      ((targetData model).termParameters symbol) := by
  let header := SyntacticModel.termHeader headers symbol
  have selected := scope_image_context model (Presentation.selectedScopeData header)
  have actual := heq_of_eq (congrArg
    (liftScope.{c,s,t,m,p,max u c s t m,max u c s t m,max u c s t m,max u c s t m,0})
    (term_header_value model headers symbol))
  have contexts := eq_of_heq (selected.trans actual)
  change ScopeImage (strictMorphism model)
    (liftScope.{u,u,u,u,u,max u c s t m,max u c s t m,max u c s t m,max u c s t m,0}
      (SyntacticModel.parameterScope header))
    (liftScope.{c,s,t,m,p,max u c s t m,max u c s t m,max u c s t m,max u c s t m,0} _)
  rw [← contexts]
  exact imageScope_comparison (strictMorphism model) (assumptions_preserved model) _

theorem predicate_parameter_image (headers : HeaderFormation D) (symbol : S.PredicateSymbol) :
    ScopeImage (strictMorphism model)
      ((sourceData.{u,max c s t m} headers).predicateParameters symbol)
      ((targetData model).predicateParameters symbol) := by
  let header := SyntacticModel.predicateHeader headers symbol
  have selected := scope_image_context model (Presentation.selectedScopeData header)
  have actual := heq_of_eq (congrArg
    (liftScope.{c,s,t,m,p,max u c s t m,max u c s t m,max u c s t m,max u c s t m,0})
    (predicate_header_value model headers symbol))
  have contexts := eq_of_heq (selected.trans actual)
  change ScopeImage (strictMorphism model)
    (liftScope.{u,u,u,u,u,max u c s t m,max u c s t m,max u c s t m,max u c s t m,0}
      (SyntacticModel.parameterScope header))
    (liftScope.{c,s,t,m,p,max u c s t m,max u c s t m,max u c s t m,max u c s t m,0} _)
  rw [← contexts]
  exact imageScope_comparison (strictMorphism model) (assumptions_preserved model) _

theorem supplied_family_heq {n : Nat}
    {first second : ModelScope C model.localModel n} (contexts : first = second)
    (code : TypeExpr S n) {A : C.toCwf.Ty first.1} {B : C.toCwf.Ty second.1}
    (firstRead : model.data.evaluateType first code = some A)
    (secondRead : model.data.evaluateType second code = some B) : HEq A B := by
  cases contexts
  exact heq_of_eq (Option.some.inj (firstRead.symm.trans secondRead))

theorem supplied_primitive_heq {n : Nat}
    {first second : ModelScope C model.localModel n} (contexts : first = second)
    (code : TermExpr S n) {A : C.toCwf.Ty first.1} {B : C.toCwf.Ty second.1}
    {a : C.toCwf.Tm first.1 A} {b : C.toCwf.Tm second.1 B}
    (firstRead : model.data.evaluateTerm first code = some ⟨A,a⟩)
    (secondRead : model.data.evaluateTerm second code = some ⟨B,b⟩) : HEq a b := by
  cases contexts
  exact (Sigma.mk.inj (Option.some.inj (firstRead.symm.trans secondRead))).2

theorem supplied_predicate_heq {n : Nat}
    {first second : ModelScope C model.localModel n} (contexts : first = second)
    (code : PropExpr S n)
    {φ : model.localModel.doctrine.Predicate first.1} {ψ : model.localModel.doctrine.Predicate second.1}
    (firstRead : model.data.evaluatePredicate first code = some φ)
    (secondRead : model.data.evaluatePredicate second code = some ψ) : HEq φ ψ := by
  cases contexts
  exact heq_of_eq (Option.some.inj (firstRead.symm.trans secondRead))

theorem type_family_value (headers : HeaderFormation D) (symbol : S.TypeSymbol) :
    HEq (typeValue model ((SyntacticModel.data headers).typeFamily symbol))
      (model.data.typeFamily symbol) := by
  have read := model.data.evaluate_family (model.data.typeParameters symbol) symbol TermExpr.var
    (C.toCwf.idS _) (fun index => by
      change some ((model.data.typeParameters symbol).2.lookup index) = _
      rw [ScopeData.components, Value.substitute_identity])
  have exactFamily := read.trans (congrArg some (C.toCwf.tySub_id (model.data.typeFamily symbol)))
  exact supplied_family_heq model (type_header_value model headers symbol)
    (SyntacticModel.rawFamily headers symbol).code
    (type_readout model (SyntacticModel.rawFamily headers symbol)) exactFamily

theorem term_type_value (headers : HeaderFormation D) (symbol : S.TermSymbol) :
    HEq (typeValue model ((SyntacticModel.data headers).termType symbol))
      (model.data.termType symbol) :=
  supplied_family_heq model (term_header_value model headers symbol)
    (SyntacticModel.rawResult headers symbol).code
    (type_readout model (SyntacticModel.rawResult headers symbol))
    (model.realization.termResult symbol)

theorem term_primitive_value (headers : HeaderFormation D) (symbol : S.TermSymbol) :
    HEq (termValue model ((SyntacticModel.data headers).termValue symbol))
      (model.data.termValue symbol) := by
  have read := model.data.evaluate_primitive (model.data.termParameters symbol) symbol TermExpr.var
    (C.toCwf.idS _) (fun index => by
      change some ((model.data.termParameters symbol).2.lookup index) = _
      rw [ScopeData.components, Value.substitute_identity])
  have exactPrimitive := read.trans (congrArg some (Value.substitute_identity
    (⟨model.data.termType symbol,model.data.termValue symbol⟩ :
      Value C.toCwf (model.data.termParameters symbol).1)))
  have values := supplied_primitive_heq model (term_header_value model headers symbol)
    (SyntacticModel.rawPrimitive headers symbol).code
    (term_readout model (SyntacticModel.rawPrimitive headers symbol)) exactPrimitive
  exact (termValue_retains_section model ((SyntacticModel.data headers).termValue symbol)).trans values

theorem primitive_predicate_value (headers : HeaderFormation D) (symbol : S.PredicateSymbol) :
    HEq (predicateValue model ((SyntacticModel.data headers).predicateValue symbol))
      (model.data.predicateValue symbol) := by
  have read := model.data.evaluate_predicateAtom (model.data.predicateParameters symbol) symbol TermExpr.var
    (C.toCwf.idS _) (fun index => by
      change some ((model.data.predicateParameters symbol).2.lookup index) = _
      rw [ScopeData.components, Value.substitute_identity])
  have exactPredicate := read.trans
    (congrArg some (model.localModel.doctrine.reindex_id (model.data.predicateValue symbol)))
  exact supplied_predicate_heq model (predicate_header_value model headers symbol)
    (SyntacticModel.rawPredicate headers symbol).code
    (predicate_readout model (SyntacticModel.rawPredicate headers symbol)) exactPredicate

/-- Every independently sized qualified target receives an actual map
preserving the three kinds of declarations and all local logical operations. -/
noncomputable def canonicalModelMap (headers : HeaderFormation D) :
    ModelMap (sourceData.{u,max c s t m} headers) (targetData model) where
  morphism := strictMorphism model
  logical := logical_preservation model
  predicates := predicate_logical_preservation model
  typeParameters := type_parameter_image model headers
  typeFamily symbol := up_heq (type_family_value model headers symbol)
  termParameters := term_parameter_image model headers
  termType symbol := up_heq (term_type_value model headers symbol)
  termValue symbol := up_heq (term_primitive_value model headers symbol)
  predicateParameters := predicate_parameter_image model headers
  predicateValue symbol := up_heq (primitive_predicate_value model headers symbol)

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.Interpretation
