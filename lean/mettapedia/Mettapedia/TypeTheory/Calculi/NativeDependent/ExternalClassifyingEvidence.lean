import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalClassifyingUniversalProperty
import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalPresheafCertificateSubstitution

/-!
# Classifying images of retained generated certificates

The supplied generated tree earns its raw context, annotation and term. Its
chosen finite presentation retains the expression and every variable position.
The actual classifying model map sends that independently constructed term
class to the checked native section. The same section is obtained by every
qualified logical and primitive-preserving model map, after the earned context
and annotation comparisons. A program interface substitutes this full section;
it does not erase the supplied proof tree or infer a guest typing judgment.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.ClassifyingEvidence

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualCwfUniverseLift
open SyntacticReification

universe u c s t m z v w
variable {S : Symbols.{u}} {D : Signature S} {C : CwfWithTerminal.{c,s,t,m}}
variable {n : Nat} {context : ContextExpr S n} {term : TermExpr S n} {type : TypeExpr S n}

abbrev Tree := Derivation D (.term context term type)

/-- Formation and typing come from the actual supplied tree. -/
def sourceContext (tree : Tree (D := D) (context := context) (term := term) (type := type)) :
    Context D := ⟨n,context,JudgmentRegularity.termContext ⟨tree⟩⟩

def sourceType (tree : Tree (D := D) (context := context) (term := term) (type := type)) :
    TypeOver (sourceContext tree) := ⟨type,JudgmentRegularity.termType ⟨tree⟩⟩

def sourceTerm (tree : Tree (D := D) (context := context) (term := term) (type := type)) :
    Term (sourceContext tree) (sourceType tree) := ⟨term,⟨tree⟩⟩

noncomputable def chosenContext (tree : Tree (D := D) (context := context) (term := term) (type := type)) :
    Context D := Presentation.selectedContext (sourceContext tree)

noncomputable def chosenType (tree : Tree (D := D) (context := context) (term := term) (type := type)) :
    TypeOver (chosenContext tree) :=
  (sourceType tree).reindex (Presentation.comparison (sourceContext tree)).hom

noncomputable def chosenTerm (tree : Tree (D := D) (context := context) (term := term) (type := type)) :
    Term (chosenContext tree) (chosenType tree) :=
  (sourceTerm tree).reindex (Presentation.comparison (sourceContext tree)).hom

/-- The scope is the actual selected CwF telescope of the authored context. -/
noncomputable def sourceScope (tree : Tree (D := D) (context := context) (term := term) (type := type)) :
    Scope D n := ⟨(chosenContext tree).raw,(chosenContext tree).formed,
      Presentation.selectedTelescope (sourceContext tree)⟩

theorem sourceScope_semantic (tree : Tree (D := D) (context := context) (term := term) (type := type)) :
    (sourceScope tree).semantic = SyntacticModel.parameterContext (sourceContext tree) := rfl

theorem chosenType_code (tree : Tree (D := D) (context := context) (term := term) (type := type)) :
    (chosenType tree).code = type :=
  Presentation.comparison_type_code (sourceContext tree) (sourceType tree)

theorem chosenTerm_code (tree : Tree (D := D) (context := context) (term := term) (type := type)) :
    (chosenTerm tree).code = term :=
  Presentation.comparison_term_code (sourceContext tree) (sourceTerm tree)

noncomputable def termClass (tree : Tree (D := D) (context := context) (term := term) (type := type)) :
    QuotientCwf.Tm ((quotientProjection D).obj (chosenContext tree)) (QType.mk (chosenType tree)) :=
  ⟨QTerm.mk (chosenTerm tree),rfl⟩

variable (headers : HeaderFormation D) (model : Interpretation.QualifiedModel D C)
variable (tree : Tree (D := D) (context := context) (term := term) (type := type))
variable (Γ : Mettapedia.TypeTheory.ContextualModelTelescopes.Context C n)
variable (A : C.toCwf.Ty Γ.1)
variable (contextRead : model.data.evaluateContext context = some Γ)
variable (typeRead : model.data.evaluateType Γ type = some A)

theorem type_readout_unique {n : Nat} {Γ Δ : Mettapedia.TypeTheory.ContextualModelTelescopes.Context C n}
    (contexts : Γ = Δ) (code : TypeExpr S n) {left : C.toCwf.Ty Γ.1} {right : C.toCwf.Ty Δ.1}
    (first : model.data.evaluateType Γ code = some left)
    (second : model.data.evaluateType Δ code = some right) : HEq left right := by
  cases contexts
  exact heq_of_eq (Option.some.inj (first.symm.trans second))

theorem term_readout_unique {n : Nat} {Γ Δ : Mettapedia.TypeTheory.ContextualModelTelescopes.Context C n}
    (contexts : Γ = Δ) (code : TermExpr S n) {left : Value C.toCwf Γ.1} {right : Value C.toCwf Δ.1}
    (first : model.data.evaluateTerm Γ code = some left)
    (second : model.data.evaluateTerm Δ code = some right) : HEq left.2 right.2 := by
  cases contexts
  exact (Sigma.mk.inj (Option.some.inj (first.symm.trans second))).2

include contextRead in
theorem context_value : Interpretation.contextValue model (chosenContext tree) = Γ :=
  (Interpretation.selected_context_value model (sourceContext tree)).trans
    (Option.some.inj ((Interpretation.context_readout model (sourceContext tree)).symm.trans contextRead))

include contextRead typeRead in
theorem type_value : HEq (Interpretation.typeValue model (QType.mk (chosenType tree))) A := by
  have read := Interpretation.type_readout model (chosenType tree)
  rw [chosenType_code tree] at read
  exact type_readout_unique model (context_value model tree Γ contextRead) type read typeRead

theorem term_value : HEq (Interpretation.termValue model (termClass tree))
    (tree.termSection model.data model.realization model.products_substitution model.products_beta
      model.products_eta Γ A contextRead typeRead) := by
  have read := Interpretation.represented_term_readout model (termClass tree) (chosenTerm tree) rfl
  rw [chosenTerm_code tree] at read
  have other := tree.termSection_readout model.data model.realization model.products_substitution
    model.products_beta model.products_eta Γ A contextRead typeRead
  exact term_readout_unique model (context_value model tree Γ contextRead) term read other

noncomputable def liftedTerm :
    (Interpretation.SourceModel.{u,z} D).toCwf.Tm
      (ULift.up ((quotientProjection D).obj (chosenContext tree)))
      (ULift.up (QType.mk (chosenType tree))) := ULift.up (termClass tree)

/-- This is the actual contextual map image of the supplied syntactic class. -/
noncomputable def mappedTerm
    (mapping : ModelMap (ClassifyingCells.sourceModel.{u,max c s t m} headers).data
      (model.commonUniverseLift.{u,c,s,t,m,u}).data) :=
  mapping.morphism.toFamilyMorphism.mapTerm (liftedTerm.{u,max c s t m} tree)

theorem native_term_types {Γ Δ : C.toCwf.Ctx} (contexts : Γ = Δ)
    {A : C.toCwf.Ty Γ} {B : C.toCwf.Ty Δ} (types : HEq A B) :
    C.toCwf.Tm Γ A = C.toCwf.Tm Δ B := by
  cases contexts
  cases eq_of_heq types
  rfl

theorem canonical_term_image : HEq
    (mappedTerm headers model tree (Classifying.interpretation headers model)).down
    (tree.termSection model.data model.realization model.products_substitution model.products_beta
      model.products_eta Γ A contextRead typeRead) := by
  change HEq (Interpretation.termValue model (termClass tree)) _
  exact term_value model tree Γ A contextRead typeRead

/-- All actual logical and primitive-preserving maps have the same complete
term image on this earned finite scope, not merely the same scalar observation. -/
theorem term_image
    (mapping : ModelMap (ClassifyingCells.sourceModel.{u,max c s t m} headers).data
      (model.commonUniverseLift.{u,c,s,t,m,u}).data) : HEq
    (mappedTerm headers model tree mapping).down
    (tree.termSection model.data model.realization model.products_substitution model.products_beta
      model.products_eta Γ A contextRead typeRead) := by
  have images := LiftedModelMapComparison.term_heq headers mapping
    (Classifying.interpretation headers model) (sourceScope tree) (liftedTerm.{u,max c s t m} tree)
  have contexts := congrArg ULift.down (LiftedModelMapComparison.context_equal headers mapping
    (Classifying.interpretation headers model) (sourceScope tree))
  have types := LiftedModelMapComparison.type_heq headers mapping
    (Classifying.interpretation headers model) (sourceScope tree) (ULift.up (QType.mk (chosenType tree)))
  have nativeTypes := Mettapedia.TypeTheory.ContextualCwfUniverseLift.down_heq
    (congrArg C.toCwf.Ty contexts) types
  have lowered := Mettapedia.TypeTheory.ContextualCwfUniverseLift.down_heq
    (native_term_types contexts nativeTypes) images
  exact lowered.trans (canonical_term_image headers model tree Γ A contextRead typeRead)

include contextRead in
theorem mapped_context
    (mapping : ModelMap (ClassifyingCells.sourceModel.{u,max c s t m} headers).data
      (model.commonUniverseLift.{u,c,s,t,m,u}).data) :
    ((mapping.morphism.toFamilyMorphism.base.obj
      ⟨ULift.up ((quotientProjection D).obj (chosenContext tree))⟩).val).down = Γ.1 := by
  have comparison := congrArg ULift.down (LiftedModelMapComparison.context_equal headers mapping
    (Classifying.interpretation headers model) (sourceScope tree))
  exact comparison.trans (congrArg Sigma.fst (context_value model tree Γ contextRead))

include contextRead typeRead in
theorem mapped_type
    (mapping : ModelMap (ClassifyingCells.sourceModel.{u,max c s t m} headers).data
      (model.commonUniverseLift.{u,c,s,t,m,u}).data) :
    HEq (mapping.morphism.toFamilyMorphism.mapType
      (Γ := ULift.up ((quotientProjection D).obj (chosenContext tree)))
      (ULift.up (QType.mk (chosenType tree)))).down A := by
  have contexts := congrArg ULift.down (LiftedModelMapComparison.context_equal headers mapping
    (Classifying.interpretation headers model) (sourceScope tree))
  have comparison := LiftedModelMapComparison.type_heq headers mapping
    (Classifying.interpretation headers model) (sourceScope tree) (ULift.up (QType.mk (chosenType tree)))
  exact (down_heq (congrArg C.toCwf.Ty contexts) comparison).trans
    (type_value model tree Γ A contextRead typeRead)

/-- Only earned context and family equations adjust the image's displayed
type. The input value remains the actual model-map term image. -/
noncomputable def sectionImage
    (mapping : ModelMap (ClassifyingCells.sourceModel.{u,max c s t m} headers).data
      (model.commonUniverseLift.{u,c,s,t,m,u}).data) : C.toCwf.Tm Γ.1 A :=
  cast (native_term_types (mapped_context headers model tree Γ contextRead mapping)
    (mapped_type headers model tree Γ A contextRead typeRead mapping))
    (mappedTerm headers model tree mapping).down

/-- The complete section is the image of the actual source class, for every
admitted logical/primitive interpretation, independently of its chosen data. -/
theorem sectionImage_readout
    (mapping : ModelMap (ClassifyingCells.sourceModel.{u,max c s t m} headers).data
      (model.commonUniverseLift.{u,c,s,t,m,u}).data) :
    sectionImage headers model tree Γ A contextRead typeRead mapping =
      tree.termSection model.data model.realization model.products_substitution model.products_beta
        model.products_eta Γ A contextRead typeRead :=
  eq_of_heq ((cast_heq _ _).trans (term_image headers model tree Γ A contextRead typeRead mapping))

end Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.ClassifyingEvidence

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalPresheafCertificates.Interpretation

open _root_.CategoryTheory
open Mettapedia.Computability.ComputationalTrinity
open Mettapedia.TypeTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension
open External.Contextual.ClassifyingEvidence

universe u
variable {C : Type u} [Category.{u} C] {S : External.Symbols.{u}} {D : External.Signature S}
variable {n : Nat} {context : External.ContextExpr S n} {term : External.TermExpr S n}
variable {type : External.TypeExpr S n} {P Q : Face.{u,u,u} C}
variable (interpretation : Interpretation D context term type P)

/-- The existing independently interpreted native specification supplies
exactly the local qualification of the classifying model theorem. -/
def qualifiedModel : External.Contextual.Interpretation.QualifiedModel D (nativeModel C) where
  data := interpretation.model
  realization := interpretation.realization
  products_substitution := interpretation.stable
  products_beta := interpretation.beta
  products_eta := interpretation.eta

variable (headers : External.HeaderFormation D)
variable (tree : External.Derivation D (.term context term type))

/-- A source-class image under the actual classifying morphism, transported
by earned context and annotation equations to the supplied native family. -/
noncomputable def classifyingSection : interpretation.decodedFamily.sections :=
  sectionImage headers interpretation.qualifiedModel tree interpretation.semanticContext
    interpretation.semanticType interpretation.contextRead interpretation.typeRead
    (External.Contextual.Classifying.interpretation headers interpretation.qualifiedModel)

theorem classifyingSection_eq_nativeSection :
    interpretation.classifyingSection headers tree = interpretation.nativeSection tree :=
  sectionImage_readout headers interpretation.qualifiedModel tree interpretation.semanticContext
    interpretation.semanticType interpretation.contextRead interpretation.typeRead
    (External.Contextual.Classifying.interpretation headers interpretation.qualifiedModel)

/-- The interface substitutes the full classifying section into the actual
program family, without identifying the two context categories. -/
noncomputable def classifyingValueSection : interpretation.valueFamily.sections :=
  reindexDisplayedSection interpretation.interface interpretation.decodedFamily
    (interpretation.classifyingSection headers tree)

theorem classifyingValueSection_eq_valueSection :
    interpretation.classifyingValueSection headers tree = interpretation.valueSection tree :=
  congrArg (reindexDisplayedSection interpretation.interface interpretation.decodedFamily)
    (interpretation.classifyingSection_eq_nativeSection headers tree)

theorem classifying_value_readout (point : P.Elements) :
    (interpretation.valueSection tree).val point =
      (interpretation.classifyingSection headers tree).val (interpretation.interface.mapElements.obj point) := by
  rw [interpretation.classifyingSection_eq_nativeSection headers tree]
  exact interpretation.valueSection_readout tree point

/-- The supplied certificate's value is fixed by its actual source-term
image, while the certificate still retains that exact generated tree. -/
theorem certificate_classifying_readout (point : P.Elements)
    (certificate : interpretation.Certificate point) :
    certificate.value = (interpretation.classifyingSection headers certificate.tree).val
      (interpretation.interface.mapElements.obj point) :=
  certificate.checked.trans (interpretation.classifying_value_readout headers certificate.tree point)

/-- Interface substitution commutes with the actual source-class image,
including the complete dependent section. -/
theorem classifyingValueSection_substitution (f : Q ⟶ P) :
    (ExternalPresheafCertificateSubstitution.reindex interpretation f).classifyingValueSection headers tree =
      reindexDisplayedSection f interpretation.valueFamily
        (interpretation.classifyingValueSection headers tree) := by
  rw [(ExternalPresheafCertificateSubstitution.reindex interpretation f).classifyingValueSection_eq_valueSection]
  rw [interpretation.classifyingValueSection_eq_valueSection]
  exact ExternalPresheafCertificateSubstitution.valueSection_substitution interpretation f tree

theorem classifyingSection_derivation_independent
    (other : External.Derivation D (.term context term type)) :
    interpretation.classifyingSection headers tree = interpretation.classifyingSection headers other := by
  rw [interpretation.classifyingSection_eq_nativeSection, interpretation.classifyingSection_eq_nativeSection]
  exact External.Derivation.termSection_derivation_independent interpretation.model
    interpretation.realization interpretation.stable interpretation.beta interpretation.eta tree other
    interpretation.semanticContext interpretation.semanticType interpretation.contextRead interpretation.typeRead

end Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalPresheafCertificates.Interpretation
