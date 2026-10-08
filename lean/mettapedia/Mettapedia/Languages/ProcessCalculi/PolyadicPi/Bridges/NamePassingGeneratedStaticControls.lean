import Mettapedia.Languages.ProcessCalculi.PolyadicPi.BindingClosedScopeSetModel
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.BindingClosedGeneratedControls

/-!
# Complete generated compiler and scope-admission controls

The actual equation-extended source functor is read on independently supplied
nonconstant function values. Its application scope equation retains the
argument and external return. An ordered tree constructor model rejects that
same equation, so constructor formation alone cannot supply schema admission.

Set-valued readings forget occurrence multiplicity. These controls concern
the generated static compiler, rather than operational edges or rho execution.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedStaticControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory
open Mettapedia.OSLF.Binding
open Mettapedia.Languages.LambdaCalculus
open Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation (ArrowValue)
open NamePassingContinuationOperations

abbrev Token := BindingClosedScopeSetModel.Token
abbrev primitives := BindingClosedPrimitiveOperations.continuation BindingClosedScopeSetModel.operations
abbrev sourceOperations := NamePassingGeneratedStatic.operations BindingClosedScopeSetModel.operations

def stored : Nat ⟶ Set Token := ↾fun result => {(37, [result])}
def active (offset : Nat) : Nat ⟶ Set Token := ↾fun result => {(47, [offset, result])}

abbrev scope : Ctx NamePassing.Presentation.signature := [.nm, .tm, .tm, .nm]

def before : NamePassing.Presentation.Program scope :=
  NamePassing.Presentation.application
    (NamePassing.Presentation.carrier (.var .zero) (.var (.succ .zero))
      (.var (.succ (.succ .zero)))) (.var (.succ (.succ (.succ .zero))))

def after : NamePassing.Presentation.Program scope :=
  NamePassing.Presentation.carrier (.var .zero) (.var (.succ .zero))
    (NamePassing.Presentation.application (.var (.succ (.succ .zero)))
      (.var (.succ (.succ (.succ .zero)))))

def actualImage (term : NamePassing.Presentation.Program scope) : ArrowValue (Type) :=
  ⟨BindingClosedScopeSetModel.sourceCompiler.functor.obj
      ((ClosedPresentation.AuthoredPresentation.inclusion.{0} NamePassing.AuthoredEquations.equations).functor.obj
        (ClosedPresentation.contextObject.{0} NamePassing.Presentation.signature scope)),
    BindingClosedScopeSetModel.sourceCompiler.functor.obj
      ((ClosedPresentation.AuthoredPresentation.inclusion.{0} NamePassing.AuthoredEquations.equations).functor.obj
        (ClosedPresentation.sortObject NamePassing.Presentation.signature .tm)),
    BindingClosedScopeSetModel.sourceCompiler.functor.map
      ((ClosedPresentation.AuthoredPresentation.inclusion.{0} NamePassing.AuthoredEquations.equations).functor.map
        (ClosedPresentation.termArrow NamePassing.Presentation.signature term))⟩

def read (term : NamePassing.Presentation.Program scope) (offset argument result : Nat) : Option (Set Token) :=
  (ArrowValue.readAt (some (actualImage term)) (sourceOperations.context scope) (Nat ⟶ Set Token)).map
    (fun arrow => arrow ((5 : Nat), stored, active offset, argument, PUnit.unit) result)

theorem read_complete (term : NamePassing.Presentation.Program scope) (offset argument result : Nat) :
    read term offset argument result =
      some ((show Nat ⟶ Set Token from (NamePassingConstructorInterpretation.meaning primitives term)
        ((5 : Nat), stored, active offset, argument, PUnit.unit)) result) := by
  rw [read, actualImage, BindingClosedScopeSetModel.sourceCompiler]
  erw [NamePassingGeneratedStatic.complete_open_term]
  change Option.map _ (ArrowValue.readAt
    (some (⟨sourceOperations.context scope, (Nat ⟶ Set Token),
      NamePassingBindingClosedOperations.contextMap primitives scope ≫
        NamePassingConstructorInterpretation.meaning primitives term⟩ : ArrowValue (Type)))
    (sourceOperations.context scope) (Nat ⟶ Set Token)) = _
  rw [ArrowValue.readAt_supplied]
  rfl

def observations (offset argument result : Nat) : Set Token :=
  {token | (∃ privateName : Nat, token = (47, [offset, privateName])) ∨
    (∃ privateName : Nat, token = (privateName, [argument, result])) ∨
      token = (5, []) ∨ (∃ reply : Nat, token = (37, [reply]))}

theorem actual_before_readout (offset argument result : Nat) :
    read before offset argument result = some (observations offset argument result) := by
  rw [read_complete]
  apply congrArg some
  simp only [before, NamePassing.Presentation.application, NamePassing.Presentation.carrier,
    NamePassingConstructorInterpretation.meaning, NamePassingConstructorInterpretation.nameMeaning,
    NamePassing.Presentation.nameVariable,
    NamePassingConstructorInterpretation.contextValue, NamePassingConstructorInterpretation.sortValue, scope]
  change {token : Token | ∃ privateName : Nat,
      token ∈ ({(47, [offset, privateName])} ∪
        ({(5, [])} ∪ {token | ∃ reply : Nat × PUnit, token ∈ ({(37, [reply.1])} : Set Token)})) ∪
          {(privateName, [argument, result])}} = observations offset argument result
  ext token
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff, observations]
  constructor
  · rintro ⟨privateName, (body | declaration | stored) | message⟩
    · exact Or.inl ⟨privateName, body⟩
    · exact Or.inr (Or.inr (Or.inl declaration))
    · rcases stored with ⟨reply, member⟩
      exact Or.inr (Or.inr (Or.inr ⟨reply.1, member⟩))
    · exact Or.inr (Or.inl ⟨privateName, message⟩)
  · rintro (⟨privateName, body⟩ | ⟨privateName, message⟩ | declaration | stored)
    · exact ⟨privateName, Or.inl (Or.inl body)⟩
    · exact ⟨privateName, Or.inr message⟩
    · exact ⟨0, Or.inl (Or.inr (Or.inl declaration))⟩
    · rcases stored with ⟨reply, member⟩
      exact ⟨0, Or.inl (Or.inr (Or.inr ⟨(reply, PUnit.unit), member⟩))⟩

theorem actual_scope_equation (offset argument result : Nat) :
    read before offset argument result = read after offset argument result := by
  rw [read_complete, read_complete]
  let Z := NamePassingConstructorInterpretation.contextValue primitives scope
  let name : Z ⟶ BindingClosedPrimitiveOperations.names BindingClosedScopeSetModel.operations :=
    NamePassingConstructorInterpretation.projection primitives (.zero : Var scope .nm)
  let value : Z ⟶ primitives.termObject :=
    NamePassingConstructorInterpretation.projection primitives (.succ .zero : Var scope .tm)
  let body : Z ⟶ primitives.termObject :=
    NamePassingConstructorInterpretation.projection primitives (.succ (.succ .zero) : Var scope .tm)
  let suppliedArgument : Z ⟶ BindingClosedPrimitiveOperations.names BindingClosedScopeSetModel.operations :=
    NamePassingConstructorInterpretation.projection primitives (.succ (.succ (.succ .zero)) : Var scope .nm)
  have comparison := NamePassingGeneratedScopeEquations.application_carrier
    BindingClosedScopeSetModel.operations BindingClosedScopeSetModel.structural_schemas
    name value body suppliedArgument
  simpa only [before, after, NamePassing.Presentation.application, NamePassing.Presentation.carrier,
    NamePassingConstructorInterpretation.meaning, NamePassingConstructorInterpretation.nameMeaning,
    NamePassing.Presentation.nameVariable, name, value, body, suppliedArgument, primitives] using
    congrArg (fun arrow : Z ⟶ primitives.termObject =>
      some ((show Nat ⟶ Set Token from
        arrow ((5 : Nat), stored, active offset, argument, PUnit.unit)) result)) comparison

theorem actual_after_readout (offset argument result : Nat) :
    read after offset argument result = some (observations offset argument result) :=
  (actual_scope_equation offset argument result).symm.trans (actual_before_readout offset argument result)

theorem returned_message (offset argument result : Nat) :
    (read before offset argument result).map (fun tokens => (8, [argument, result]) ∈ tokens) = some True := by
  rw [actual_before_readout]
  change some ((8, [argument, result]) ∈ observations offset argument result) = some True
  congr 1
  apply propext
  exact ⟨fun _ => trivial, fun _ => Or.inr (Or.inl ⟨8, rfl⟩)⟩

theorem external_return_retained : read before 19 7 11 ≠ read before 19 7 13 := by
  rw [actual_before_readout, actual_before_readout]
  intro same
  have member : (8, [7, 11]) ∈ observations 19 7 11 := Or.inr (Or.inl ⟨8, rfl⟩)
  rw [Option.some.inj same] at member
  simp [observations] at member

theorem application_argument_retained : read before 19 7 11 ≠ read before 19 9 11 := by
  rw [actual_before_readout, actual_before_readout]
  intro same
  have member : (8, [7, 11]) ∈ observations 19 7 11 := Or.inr (Or.inl ⟨8, rfl⟩)
  rw [Option.some.inj same] at member
  simp [observations] at member

def sourceBody (offset : Nat) : (Nat × PUnit) ⟶ (Nat ⟶ Set Token) :=
  ↾fun reference => ↾fun result => {(47, [offset, reference.1, result])}

abbrev definitionTerm := Term NamePassing.AuthoredEquations.schemaSig
  NamePassing.AuthoredEquations.appDefinition.ctx NamePassing.Presentation.Srt.tm

def schemaImage (term : definitionTerm) : ArrowValue (Type) :=
  ⟨BindingClosedScopeSetModel.sourceCompiler.functor.obj
      ((ClosedPresentation.AuthoredPresentation.inclusion.{0} NamePassing.AuthoredEquations.equations).functor.obj
        (ClosedPresentation.SchemaExpressions.genericStage.{0} NamePassing.Presentation.signature
          NamePassing.AuthoredEquations.metas NamePassing.AuthoredEquations.appDefinition.ctx)),
    BindingClosedScopeSetModel.sourceCompiler.functor.obj
      ((ClosedPresentation.AuthoredPresentation.inclusion.{0} NamePassing.AuthoredEquations.equations).functor.obj
        (ClosedPresentation.sortObject NamePassing.Presentation.signature .tm)),
    BindingClosedScopeSetModel.sourceCompiler.functor.map
      ((ClosedPresentation.AuthoredPresentation.inclusion.{0} NamePassing.AuthoredEquations.equations).functor.map
        (Mettapedia.CategoryTheory.RelativeClosedSyntax.GeneratedCategory.classOf
          (ClosedPresentation.SchemaExpressions.expression NamePassing.Presentation.signature term)))⟩

def readDefinition (term : definitionTerm) (offset argument result : Nat) : Option (Set Token) :=
  (ArrowValue.readAt (some (schemaImage term))
    (sourceOperations.context NamePassing.AuthoredEquations.appDefinition.ctx ⊗
      sourceOperations.family NamePassing.AuthoredEquations.metas) (Nat ⟶ Set Token)).map
    (fun arrow => arrow ((stored, argument, PUnit.unit), (sourceBody offset, PUnit.unit)) result)

theorem readDefinition_complete (term : definitionTerm) (offset argument result : Nat) :
    readDefinition term offset argument result =
      some ((show Nat ⟶ Set Token from
        (sourceOperations.model.generic NamePassing.AuthoredEquations.metas term)
          ((stored, argument, PUnit.unit), (sourceBody offset, PUnit.unit))) result) := by
  rw [readDefinition, schemaImage, BindingClosedScopeSetModel.sourceCompiler]
  erw [NamePassingGeneratedStatic.complete_schema_readout]
  change Option.map _ (ArrowValue.readAt
    (some (⟨sourceOperations.context NamePassing.AuthoredEquations.appDefinition.ctx ⊗
        sourceOperations.family NamePassing.AuthoredEquations.metas,
      (Nat ⟶ Set Token), sourceOperations.model.generic NamePassing.AuthoredEquations.metas term⟩ :
      ArrowValue (Type))) _ (Nat ⟶ Set Token)) = _
  rw [ArrowValue.readAt_supplied]
  rfl

def definitionObservations (offset argument result : Nat) : Set Token :=
  {token | (∃ reference privateName : Nat, token = (47, [offset, reference, privateName])) ∨
    (∃ privateName : Nat, token = (privateName, [argument, result])) ∨
      (∃ reference : Nat, token = (reference, [])) ∨ (∃ reply : Nat, token = (37, [reply]))}

theorem actual_definition_readout (offset argument result : Nat) :
    readDefinition NamePassing.AuthoredEquations.appDefinition.lhs offset argument result =
      some (definitionObservations offset argument result) := by
  rw [readDefinition_complete]
  apply congrArg some
  unfold CategoricalBindingModel.Model.generic
  erw [NamePassingBindingClosedSchemas.definition_left_value]
  change {token : Token | ∃ privateName : Nat,
    token ∈ {token | ∃ reference : Nat,
      token ∈ ({(47, [offset, reference, privateName])} ∪
        ({(reference, [])} ∪ {token | ∃ reply : Nat × PUnit, token ∈ ({(37, [reply.1])} : Set Token)}))} ∪
      {(privateName, [argument, result])}} = definitionObservations offset argument result
  ext token
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff, definitionObservations]
  constructor
  · rintro ⟨privateName, ⟨reference, body | declaration | stored⟩ | message⟩
    · exact Or.inl ⟨reference, privateName, body⟩
    · exact Or.inr (Or.inr (Or.inl ⟨reference, declaration⟩))
    · rcases stored with ⟨reply, member⟩
      exact Or.inr (Or.inr (Or.inr ⟨reply.1, member⟩))
    · exact Or.inr (Or.inl ⟨privateName, message⟩)
  · rintro (⟨reference, privateName, body⟩ | ⟨privateName, message⟩ | ⟨reference, declaration⟩ | stored)
    · exact ⟨privateName, Or.inl ⟨reference, Or.inl body⟩⟩
    · exact ⟨privateName, Or.inr message⟩
    · exact ⟨0, Or.inl ⟨reference, Or.inr (Or.inl declaration)⟩⟩
    · rcases stored with ⟨reply, member⟩
      exact ⟨0, Or.inl ⟨0, Or.inr (Or.inr ⟨(reply, PUnit.unit), member⟩)⟩⟩

theorem actual_definition_scope_equation (offset argument result : Nat) :
    readDefinition NamePassing.AuthoredEquations.appDefinition.lhs offset argument result =
      readDefinition NamePassing.AuthoredEquations.appDefinition.rhs offset argument result := by
  rw [readDefinition_complete, readDefinition_complete]
  have same := (sourceOperations.schema_generic_eq_iff
    NamePassing.AuthoredEquations.appDefinition.lhs NamePassing.AuthoredEquations.appDefinition.rhs).mpr
      (NamePassingGeneratedStatic.definition_schema_satisfied
        BindingClosedScopeSetModel.operations BindingClosedScopeSetModel.structural_schemas)
  exact congrArg (fun arrow => some ((show Nat ⟶ Set Token from
    arrow ((stored, argument, PUnit.unit), (sourceBody offset, PUnit.unit))) result)) same

theorem definition_metadata_retained :
    readDefinition NamePassing.AuthoredEquations.appDefinition.lhs 19 7 11 ≠
      readDefinition NamePassing.AuthoredEquations.appDefinition.lhs 23 7 11 := by
  rw [actual_definition_readout, actual_definition_readout]
  intro same
  have member : (47, [19, 5, 8]) ∈ definitionObservations 19 7 11 := Or.inl ⟨5, 8, rfl⟩
  rw [Option.some.inj same] at member
  simp [definitionObservations] at member

abbrev treePrimitives := BindingClosedPrimitiveOperations.continuation BindingClosedGeneratedControls.operations
def treeBody : Nat ⟶ BindingClosedGeneratedControls.Tree := ↾fun result => .emitted 31 [result]

theorem constructor_scope_rejected :
    lift
      (lift (↾fun _ : PUnit => (5 : Nat))
        (lift (↾fun _ : PUnit => treeBody) (↾fun _ : PUnit => treeBody)) ≫ treePrimitives.carrier)
      (↾fun _ : PUnit => (7 : Nat)) ≫ treePrimitives.application ≠
    lift (↾fun _ : PUnit => (5 : Nat))
      (lift (↾fun _ : PUnit => treeBody)
        (lift (↾fun _ : PUnit => treeBody) (↾fun _ : PUnit => (7 : Nat)) ≫ treePrimitives.application)) ≫
      treePrimitives.carrier := by
  intro same
  have read := congrArg
    (fun arrow : PUnit ⟶ (Nat ⟶ BindingClosedGeneratedControls.Tree) => arrow PUnit.unit 11) same
  change BindingClosedGeneratedControls.Tree.fresh _ = BindingClosedGeneratedControls.Tree.parallel _ _ at read
  cases read

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedStaticControls
