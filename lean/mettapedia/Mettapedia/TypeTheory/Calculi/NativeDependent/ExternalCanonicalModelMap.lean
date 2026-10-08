import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalSyntacticQualification
import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalContextualLogicalMorphism
import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalModelUniverseReadout
import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalModelMap

/-!
# Primitive declaration comparisons of the canonical interpreter

Actual finite comprehension determines the image of each chosen source
header. Generated context equations compare that header with its authored
presentation. Local primitive evaluation then retains the independently
supplied family and section. These declaration comparisons assemble the
logical contextual interpretation into a model map.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.Interpretation

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualTelescopeMorphism
open Mettapedia.TypeTheory.ContextualComprehensionMorphism
open Mettapedia.TypeTheory.ContextualCwfUniverseLift
open SyntacticReification

universe u c s t m
variable {S : Symbols.{u}} {D : Signature S} {C : CwfWithTerminal.{c,s,t,m}}
variable (model : QualifiedModel D C)

/-- The image telescope is computed successively, rather than selected
from the equality of its endpoint alone. -/
theorem telescope_image_context : {n : Nat} → {Γ : QuotientCwf.QContext D} →
    (telescope : Telescope (QuotientCwf.withTerminal D) n Γ) →
    HEq (imageContext (strictMorphism model)
      (liftContext.{u,u,u,u,max u c s t m,max u c s t m,max u c s t m,max u c s t m}
        (⟨Γ,telescope⟩ : Mettapedia.TypeTheory.ContextualModelTelescopes.Context
          (QuotientCwf.withTerminal D) n)))
      (liftContext.{c,s,t,m,max u c s t m,max u c s t m,max u c s t m,max u c s t m}
        (contextValue model Γ.as))
  | _, _, .nil => by
      erw [context_empty]
      rfl
  | _, _, @Telescope.snoc _ n Γ previous A => by
      have ih := telescope_image_context previous
      have counts := SyntacticTelescopes.telescope_arity previous
      cases counts
      have contexts := eq_of_heq ih
      let source := liftContext.{u,u,u,u,max u c s t m,max u c s t m,max u c s t m,max u c s t m}
        (⟨Γ,previous⟩ : Mettapedia.TypeTheory.ContextualModelTelescopes.Context
          (QuotientCwf.withTerminal D) Γ.as.arity)
      have types := (imageType_heq (strictMorphism model)
        (imageContext_comparison (strictMorphism model) source).contexts (ULift.up A)).symm
      have extended := context_snoc_heq contexts types
      change HEq ((imageContext (strictMorphism model) source).snoc
        (imageType (strictMorphism model)
          (imageContext_comparison (strictMorphism model) source).contexts (ULift.up A))) _
      erw [represented_extension, liftContext_snoc]
      exact heq_of_eq extended

/-- The generated presentation equation is sound in the independently
supplied model. -/
theorem selected_context_value (raw : Context D) :
    contextValue model (Presentation.selectedContext raw) = contextValue model raw := by
  let selection := Presentation.select raw.raw raw.formed
  exact (Classical.choice (Presentation.selectedContext raw).formed.judgment).contextValue_equation
    model.data model.realization model.products_substitution model.products_beta model.products_eta
    (Classical.choice raw.formed.judgment) (Classical.choice selection.equivalent)

/-- Each primitive header's independently supplied telescope is recovered,
including every generic-variable reading. -/
theorem type_parameter_image (headers : HeaderFormation D) (symbol : S.TypeSymbol) :
    ContextImage (strictMorphism model)
      (((SyntacticModel.data headers).commonUniverseLift.{u,u,u,u,u,max c s t m}).typeParameters symbol)
      ((model.data.commonUniverseLift.{u,c,s,t,m,u}).typeParameters symbol) := by
  let header := SyntacticModel.typeHeader headers symbol
  have selected := telescope_image_context model (Presentation.selectedTelescope header)
  have selectedValue := selected_context_value model header
  have headerValue : contextValue model header = model.data.typeParameters symbol :=
    Option.some.inj ((context_readout model header).symm.trans (model.realization.typeHeader symbol))
  have actual := heq_of_eq (congrArg
    (liftContext.{c,s,t,m,max u c s t m,max u c s t m,max u c s t m,max u c s t m})
    (selectedValue.trans headerValue))
  have contexts := eq_of_heq (selected.trans actual)
  change ContextImage (strictMorphism model)
    (liftContext.{u,u,u,u,max u c s t m,max u c s t m,max u c s t m,max u c s t m}
      (SyntacticModel.parameterContext header))
    (liftContext.{c,s,t,m,max u c s t m,max u c s t m,max u c s t m,max u c s t m} _)
  rw [← contexts]
  exact imageContext_comparison (strictMorphism model) _

/-- Term declarations retain the complete authored parameter telescope. -/
theorem term_parameter_image (headers : HeaderFormation D) (symbol : S.TermSymbol) :
    ContextImage (strictMorphism model)
      (((SyntacticModel.data headers).commonUniverseLift.{u,u,u,u,u,max c s t m}).termParameters symbol)
      ((model.data.commonUniverseLift.{u,c,s,t,m,u}).termParameters symbol) := by
  let header := SyntacticModel.termHeader headers symbol
  have selected := telescope_image_context model (Presentation.selectedTelescope header)
  have selectedValue := selected_context_value model header
  have headerValue : contextValue model header = model.data.termParameters symbol :=
    Option.some.inj ((context_readout model header).symm.trans (model.realization.termHeader symbol))
  have actual := heq_of_eq (congrArg
    (liftContext.{c,s,t,m,max u c s t m,max u c s t m,max u c s t m,max u c s t m})
    (selectedValue.trans headerValue))
  have contexts := eq_of_heq (selected.trans actual)
  change ContextImage (strictMorphism model)
    (liftContext.{u,u,u,u,max u c s t m,max u c s t m,max u c s t m,max u c s t m}
      (SyntacticModel.parameterContext header))
    (liftContext.{c,s,t,m,max u c s t m,max u c s t m,max u c s t m,max u c s t m} _)
  rw [← contexts]
  exact imageContext_comparison (strictMorphism model) _

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

/-- Equality of the actual evaluated telescope transports only the readout,
retaining the independently supplied family. -/
theorem supplied_family_heq {n : Nat}
    {first second : Mettapedia.TypeTheory.ContextualModelTelescopes.Context C n}
    (contexts : first = second) (code : TypeExpr S n)
    {A : C.toCwf.Ty first.1} {B : C.toCwf.Ty second.1}
    (firstRead : model.data.evaluateType first code = some A)
    (secondRead : model.data.evaluateType second code = some B) : HEq A B := by
  cases contexts
  exact heq_of_eq (Option.some.inj (firstRead.symm.trans secondRead))

theorem supplied_primitive_heq {n : Nat}
    {first second : Mettapedia.TypeTheory.ContextualModelTelescopes.Context C n}
    (contexts : first = second) (code : TermExpr S n)
    {A : C.toCwf.Ty first.1} {B : C.toCwf.Ty second.1}
    {a : C.toCwf.Tm first.1 A} {b : C.toCwf.Tm second.1 B}
    (firstRead : model.data.evaluateTerm first code = some ⟨A,a⟩)
    (secondRead : model.data.evaluateTerm second code = some ⟨B,b⟩) : HEq a b := by
  cases contexts
  exact (Sigma.mk.inj (Option.some.inj (firstRead.symm.trans secondRead))).2

theorem type_family_value (headers : HeaderFormation D) (symbol : S.TypeSymbol) :
    HEq (typeValue model ((SyntacticModel.data headers).typeFamily symbol))
      (model.data.typeFamily symbol) := by
  have read := model.data.evaluate_family (model.data.typeParameters symbol) symbol TermExpr.var
    (C.toCwf.idS _) (fun index => by
      change some ((model.data.typeParameters symbol).2.lookup index) = _
      rw [Telescope.components, Value.substitute_identity])
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
      rw [Telescope.components, Value.substitute_identity])
  have exactPrimitive := read.trans (congrArg some (Value.substitute_identity
    (⟨model.data.termType symbol, model.data.termValue symbol⟩ :
      Value C.toCwf (model.data.termParameters symbol).1)))
  have values := supplied_primitive_heq model (term_header_value model headers symbol)
    (SyntacticModel.rawPrimitive headers symbol).code
    (term_readout model (SyntacticModel.rawPrimitive headers symbol)) exactPrimitive
  exact (termValue_retains_section model ((SyntacticModel.data headers).termValue symbol)).trans values

/-- The canonical model map exists for every locally qualified independent
model, after retaining all four carriers at a common external level. -/
noncomputable def canonicalModelMap (headers : HeaderFormation D) :
    ModelMap ((SyntacticModel.data headers).commonUniverseLift.{u,u,u,u,u,max c s t m})
      (model.data.commonUniverseLift.{u,c,s,t,m,u}) where
  morphism := strictMorphism model
  logical := logical_preservation model
  typeParameters := type_parameter_image model headers
  typeFamily symbol := up_heq (type_family_value model headers symbol)
  termParameters := term_parameter_image model headers
  termType symbol := up_heq (term_type_value model headers symbol)
  termValue symbol := up_heq (term_primitive_value model headers symbol)

end Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.Interpretation
