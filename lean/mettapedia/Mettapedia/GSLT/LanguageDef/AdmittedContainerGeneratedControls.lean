import Mettapedia.GSLT.LanguageDef.AdmittedContainerGenerated
import Mettapedia.GSLT.LanguageDef.IndexedInductiveHOLRealization

/-!
# Actual admitted Vector controls for generated constructor representations

The target is a full HOL model with ordinary arithmetic and recursive trees.
Its payload type is the actual Nil/Cons handler encoding. Constructor fields
are proved faithful directly from tree constructors, independently of the
generated representation. Empty source sorts and malformed encodings remain
separate observations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.AdmittedContainerGeneratedControls

open Mettapedia.Logic.HOL
open Mettapedia.TypeTheory
open IndexedPolynomial.Description
open IndexedInductiveNatVec
open IndexedContainerPositionTerms
open AdmittedContainerHOL

noncomputable section

inductive BaseCode where | number | element | space
abbrev number : Ty BaseCode := .base .number
abbrev element : Ty BaseCode := .base .element
abbrev space : Ty BaseCode := .base .space
abbrev payload : Ty BaseCode := FiniteConstructorEncoding.payloadType [[], [number, element]]

def scalarCarrier : BaseCode → Type 1
  | .number => ULift.{1} Nat
  | .element => ULift.{1} Bool
  | .space => ULift.{1} Unit

abbrev Payload := Ty.denote.{0,0} scalarCarrier payload

def carrier : BaseCode → Type 1
  | .number => ULift.{1} Nat
  | .element => ULift.{1} Bool
  | .space => ULift.{1} (RecursiveSpace.Tree Payload)

inductive Symbol : Ty BaseCode → Type where
  | zero : Symbol number
  | successor : Symbol (number ⇒ number)
  | addition : Symbol (number ⇒ number ⇒ number)
  | flagTrue : Symbol element
  | bottom : Symbol space
  | construct : Symbol (number ⇒ payload ⇒ (number ⇒ space) ⇒ space)

def model : HenkinModel.{0,0,0} BaseCode Symbol := .standard carrier (fun symbol => match symbol with
  | .zero => .up 0
  | .successor => fun n => .up (n.down + 1)
  | .addition => fun n m => .up (n.down + m.down)
  | .flagTrue => .up true
  | .bottom => .up RecursiveSpace.bottom
  | .construct => fun tag data children =>
      .up (RecursiveSpace.construct tag.down data (fun n => (children (.up n)).down)))

def arithmetic : IndexedInductiveHOLTerms.Arithmetic Symbol :=
  ⟨number, element, .const .zero, .const .successor, .const .addition⟩

def numbers : IndexedInductiveHOLRealization.Numbers arithmetic model where
  equivalence := Equiv.ulift.symm
  zero := rfl
  successor _ := rfl
  addition _ _ := rfl

def elements : IndexedInductiveHOLRealization.Elements arithmetic model Bool :=
  IndexedInductiveHOLRealization.fullElements arithmetic model Bool Equiv.ulift.symm

def block := PositiveInductiveBlockBridge.Direct.admitted 0 (Vectors.admitted Bool)
theorem registered : block.WellRegistered := PositiveInductiveBlockBridge.Direct.admitted_registered 0 (Vectors.admitted Bool)

def sourceOrder : ∀ name container, PositiveInductiveBlockBridge.Direct.registry.lookup name = some container →
    IndexedContainer.OrderedFinitary container := by
  intro _ _ impossible
  cases impossible

def reading := IndexedInductiveHOLRealization.reading arithmetic Bool

def interpreted : IndexedContainerPositionTerms.Realization reading
    (IndexedPositiveContainer.Unindexed.liftOrdered sourceOrder) model where
  numbers := (IndexedInductiveHOLRealization.realization arithmetic model Bool numbers elements).numbers
  value := (IndexedInductiveHOLRealization.realization arithmetic model Bool numbers elements).value
  index := (IndexedInductiveHOLRealization.realization arithmetic model Bool numbers elements).index
  shape := (IndexedInductiveHOLRealization.realization arithmetic model Bool numbers elements).shape
  parameterValues := (IndexedInductiveHOLRealization.realization arithmetic model Bool numbers elements).parameterValues
  index_correct := (IndexedInductiveHOLRealization.realization arithmetic model Bool numbers elements).index_correct
  one_correct := (IndexedInductiveHOLRealization.realization arithmetic model Bool numbers elements).one_correct
  count_correct := by
    intro _ _ _ impossible
    cases impossible

theorem injections : FieldInjective interpreted where
  value := by
    intro sort
    cases sort with
    | length => exact (IndexedInductiveHOLRealization.naturalValues arithmetic model numbers).injective
    | payload => intro first second same; exact congrArg ULift.down same
  shape := by intro _ _ impossible; cases impossible

def empty : model.Valuation [] := fun impossible => nomatch impossible
def bottomCode : ClosedTerm Symbol space := .const .bottom
def constructorCode : ClosedTerm Symbol (number ⇒ payload ⇒ (number ⇒ space) ⇒ space) := .const .construct

theorem constructor_fields : ∀ tag data children otherTag otherData otherChildren,
    model.denote constructorCode empty tag data children = model.denote constructorCode empty otherTag otherData otherChildren →
      data = otherData ∧ children = otherChildren := by
  intro tag data children otherTag otherData otherChildren same
  have trees := congrArg ULift.down same
  change RecursiveSpace.construct tag.down data (fun n => (children (.up n)).down) =
    RecursiveSpace.construct otherTag.down otherData (fun n => (otherChildren (.up n)).down) at trees
  obtain ⟨_, dataEqual, childEqual⟩ := (RecursiveSpace.construct_injective _ _ _ _ _ _).mp trees
  refine ⟨dataEqual, ?_⟩
  funext value
  cases value with
  | up n => apply ULift.ext; exact congrFun childEqual n

theorem constructor_shape_separation :
    HOLShapeSeparation block registered sourceOrder interpreted constructorCode empty :=
  HOLShapeSeparation.of_raw block registered sourceOrder interpreted constructorCode empty constructor_fields

theorem constructor_separated : ∀ tag data children,
    model.denote constructorCode empty tag data children ≠ model.denote bottomCode empty := by
  intro tag data children same
  exact RecursiveSpace.construct_ne_bottom tag.down data (fun n => (children (.up n)).down)
    (congrArg ULift.down same)

def algebra := nativeAlgebra block registered sourceOrder interpreted bottomCode constructorCode empty
def represented := nativeGeneratedRepresentation block registered sourceOrder interpreted bottomCode constructorCode empty
  injections constructor_shape_separation
def equivalence := generatedBlockEquivalence block registered sourceOrder interpreted bottomCode constructorCode empty
  injections constructor_shape_separation

abbrev environment : Env (Vectors.interface Bool).Value [] := PUnit.unit

def nilShape : (IndexedPositiveContainer.Unindexed.blockPolynomial block registered).Shape environment Natural.zero := by
  refine ⟨⟨0, by decide⟩, ?_⟩
  change ULift (PLift (Natural.zero = Natural.zero))
  exact ⟨⟨rfl⟩⟩
def consShape (length : Natural.Carrier) (head : Bool) :
    (IndexedPositiveContainer.Unindexed.blockPolynomial block registered).Shape environment (Natural.succ length) := by
  refine ⟨⟨1, by decide⟩, ?_⟩
  change Σ n : Natural.Carrier, Σ _ : Bool, ULift (PLift (Natural.succ n = Natural.succ length))
  exact ⟨length, head, ⟨⟨rfl⟩⟩⟩

def nilValue := algebra.act environment Natural.zero ⟨nilShape, fun impossible => nomatch impossible⟩
def consValue (head : Bool) := algebra.act environment (Natural.succ Natural.zero)
  ⟨consShape Natural.zero head, fun _ => nilValue⟩

theorem nil_generated : IndexedPolynomial.Algebra.Generated algebra environment Natural.zero nilValue :=
  IndexedPolynomial.Algebra.generated_closed algebra environment Natural.zero nilShape _ (fun impossible => nomatch impossible)

theorem cons_generated (head : Bool) :
    IndexedPolynomial.Algebra.Generated algebra environment (Natural.succ Natural.zero) (consValue head) :=
  IndexedPolynomial.Algebra.generated_closed algebra environment (Natural.succ Natural.zero) (consShape Natural.zero head)
    (fun _ => nilValue) (fun position => by cases position with | none => exact nil_generated | some impossible => nomatch impossible)

theorem wrong_index_refused : ¬ IndexedPolynomial.Algebra.Generated algebra environment Natural.zero (consValue true) := by
  intro wrong
  have indices := nativeGenerated_index_unique block registered sourceOrder interpreted bottomCode constructorCode empty
    injections constructor_shape_separation environment (consValue true) _ _ (cons_generated true) wrong
  exact Natural.succ_ne_zero Natural.zero indices

theorem head_retained : consValue true ≠ consValue false := by
  intro same
  have layers := nativeAlgebra_injective block registered sourceOrder interpreted bottomCode constructorCode empty
    injections constructor_shape_separation environment (Natural.succ Natural.zero) same
  have shapes := congrArg Sigma.fst layers
  have fields := eq_of_heq (Sigma.mk.inj shapes).2
  have heads : true = false := congrArg (fun sourceShape => sourceShape.2.1) fields
  cases heads

theorem primitive_data_injective : Function.Injective (nativePayload block registered sourceOrder interpreted environment) :=
  nativePayload_injective block registered sourceOrder interpreted injections environment

theorem representation_roundtrip (index : Natural.Carrier) (value : block.Family environment index) :
    (equivalence environment index).symm (equivalence environment index value) = value :=
  (equivalence environment index).symm_apply_apply value

def guards := IndexedInductiveHOLRealization.guards arithmetic model Bool elements
theorem images : FieldImages interpreted guards where
  value_correct := (IndexedInductiveHOLRealization.images arithmetic model Bool numbers elements).value_correct
  shape_correct := by intro _ _ _ impossible; cases impossible

theorem full : model.FullDomains := by intro _ _; exact True.intro
theorem index_injective : Function.Injective interpreted.index :=
  (IndexedInductiveHOLRealization.naturalValues arithmetic model numbers).injective
theorem represented_context : interpreted.Represents environment Subst.id empty := by
  intro _ impossible
  exact nomatch impossible

def numeral : Nat → ClosedTerm Symbol number
  | 0 => .const .zero
  | n + 1 => .app (.const .successor) (numeral n)

theorem numeral_meaning (n : Nat) : model.denote (numeral n) empty = interpreted.numbers n := by
  induction n with
  | zero => rfl
  | succ n previous =>
    change ULift.up ((model.denote (numeral n) empty).down + 1) = ULift.up (n+1)
    rw [previous]
    rfl

def nilOccurrence : Fin ((codes block registered).map reading.fields).length := ⟨0, by decide⟩
def consOccurrence : Fin ((codes block registered).map reading.fields).length := ⟨1, by decide⟩
def nilArguments : FiniteConstructorEncoding.Arguments Symbol [] (reading.fields (codeAt reading (codes block registered) nilOccurrence)) :=
  PUnit.unit
def consArguments : FiniteConstructorEncoding.Arguments Symbol [] (reading.fields (codeAt reading (codes block registered) consOccurrence)) :=
  (.const .zero, .const .flagTrue, PUnit.unit)

def nilEvidence : guards.Evidence [] (codeAt reading (codes block registered) nilOccurrence) Subst.id nilArguments := PUnit.unit
def consEvidence : guards.Evidence [] (codeAt reading (codes block registered) consOccurrence) Subst.id consArguments :=
  ⟨.impE (.eqPropER (.beta _ _)) .topI, .impE (.eqPropER (.beta _ _)) .topI, PUnit.unit⟩

theorem nilEvidence_free : guards.EvidenceFree [] (codeAt reading (codes block registered) nilOccurrence) Subst.id nilArguments nilEvidence :=
  True.intro
theorem consEvidence_free : guards.EvidenceFree [] (codeAt reading (codes block registered) consOccurrence) Subst.id consArguments consEvidence := by
  change _ ∧ _ ∧ True
  simp only [consEvidence, ProofSyntax.FunctionExtensionalityFree, and_self]

def bottomChildren : ClosedTerm Symbol (number ⇒ space) := .lam (weaken bottomCode)
def constructorInventory := inventory block registered guards Subst.id numeral
def nilProgram := constructorInventory.constructorValue constructorCode nilOccurrence
  (inventoryArguments reading (codes block registered) nilOccurrence nilArguments) bottomChildren
def consProgram := constructorInventory.constructorValue constructorCode consOccurrence
  (inventoryArguments reading (codes block registered) consOccurrence consArguments) bottomChildren
def nilIndex := reading.indexTerm (codeAt reading (codes block registered) nilOccurrence) Subst.id nilArguments
def consIndex := reading.indexTerm (codeAt reading (codes block registered) consOccurrence) Subst.id consArguments

theorem nilIndex_meaning : model.denote nilIndex empty = interpreted.index Natural.zero := by
  apply argumentIndex_denote sourceOrder interpreted _ Subst.id full environment empty represented_context
    (constructorPoint block registered (reading := reading) environment ⟨Natural.zero, nilShape⟩).2.2 nilArguments
  rfl
theorem consIndex_meaning : model.denote consIndex empty = interpreted.index (Natural.succ Natural.zero) := by
  apply argumentIndex_denote sourceOrder interpreted _ Subst.id full environment empty represented_context
    (constructorPoint block registered (reading := reading) environment ⟨Natural.succ Natural.zero, consShape Natural.zero true⟩).2.2 consArguments
  change (model.denote (.const .zero) empty, model.denote (.const .flagTrue) empty, PUnit.unit) =
    (interpreted.value .length Natural.zero, interpreted.value .payload true, PUnit.unit)
  apply Prod.ext
  · exact IndexedInductiveHOLRealization.natural_zero arithmetic model numbers
  · rfl

def nilRootProof := rootProof block registered guards Subst.id numeral constructorCode bottomChildren nilOccurrence nilArguments nilEvidence
def consRootProof := rootProof block registered guards Subst.id numeral constructorCode bottomChildren consOccurrence consArguments consEvidence
theorem nilRootProof_free : nilRootProof.FunctionExtensionalityFree :=
  rootProof_free block registered guards Subst.id numeral constructorCode bottomChildren nilOccurrence nilArguments nilEvidence nilEvidence_free
theorem consRootProof_free : consRootProof.FunctionExtensionalityFree :=
  rootProof_free block registered guards Subst.id numeral constructorCode bottomChildren consOccurrence consArguments consEvidence consEvidence_free

private theorem proof_holds {formula : ClosedFormula Symbol} (proof : ProofSyntax Symbol [] formula) :
    (model.denote formula empty).down :=
  Soundness.extDerivation_sound proof.erase (M := model) (ρ := empty)
    (model.functionsRespectEqv_of_fullDomains full) (by intro _ impossible; nomatch impossible)
    (by intro _ impossible; nomatch impossible)

theorem nilRoot_holds : (model.denote (constructorInventory.rootIndex constructorCode nilProgram nilIndex) empty).down :=
  proof_holds nilRootProof
theorem consRoot_holds : (model.denote (constructorInventory.rootIndex constructorCode consProgram consIndex) empty).down :=
  proof_holds consRootProof

theorem compiled_nil_root : IndexedPolynomial.RecursiveSpaceRepresentation.ConstructorRoot
    (IndexedPositiveContainer.RecursiveSpaceRepresentation.blockPresentation sourceOrder block registered)
    (nativePayload block registered sourceOrder interpreted)
    (fun _ => nativeConstructor block registered sourceOrder interpreted constructorCode empty)
    environment Natural.zero (model.denote nilProgram empty) :=
  (compiledRoot_iff block registered sourceOrder interpreted constructorCode empty images index_injective
    Subst.id numeral full numeral_meaning environment represented_context nilProgram nilIndex Natural.zero nilIndex_meaning).mp nilRoot_holds

theorem compiled_cons_root : IndexedPolynomial.RecursiveSpaceRepresentation.ConstructorRoot
    (IndexedPositiveContainer.RecursiveSpaceRepresentation.blockPresentation sourceOrder block registered)
    (nativePayload block registered sourceOrder interpreted)
    (fun _ => nativeConstructor block registered sourceOrder interpreted constructorCode empty)
    environment (Natural.succ Natural.zero) (model.denote consProgram empty) :=
  (compiledRoot_iff block registered sourceOrder interpreted constructorCode empty images index_injective
    Subst.id numeral full numeral_meaning environment represented_context consProgram consIndex (Natural.succ Natural.zero) consIndex_meaning).mp consRoot_holds

theorem bottom_not_generated : ¬ ∃ index, IndexedPolynomial.Algebra.Generated algebra environment index (model.denote bottomCode empty) := by
  rintro ⟨index, generated⟩
  obtain ⟨shape, children, equation⟩ := IndexedPolynomial.RecursiveSpaceRepresentation.generated_constructorRoot
    (IndexedPositiveContainer.RecursiveSpaceRepresentation.blockPresentation sourceOrder block registered)
    (nativePayload block registered sourceOrder interpreted) (fun _ => model.denote bottomCode empty)
    (fun _ => nativeConstructor block registered sourceOrder interpreted constructorCode empty)
    environment index _ generated
  exact constructor_separated _ _ _ equation.symm

def badConsValue := algebra.act environment (Natural.succ Natural.zero)
  ⟨consShape Natural.zero true, fun _ => model.denote bottomCode empty⟩

theorem bad_cons_refused : ¬ IndexedPolynomial.Algebra.Generated algebra environment (Natural.succ Natural.zero) badConsValue := by
  intro generated
  have children := (IndexedPolynomial.RecursiveSpaceRepresentation.generated_constructor_iff
    (IndexedPositiveContainer.RecursiveSpaceRepresentation.blockPresentation sourceOrder block registered)
    (nativePayload block registered sourceOrder interpreted) (fun _ => model.denote bottomCode empty)
    (fun _ => nativeConstructor block registered sourceOrder interpreted constructorCode empty)
    (nativePayload_injective block registered sourceOrder interpreted injections)
    (nativeConstructor_fields block registered sourceOrder interpreted constructorCode empty constructor_shape_separation)
    environment (Natural.succ Natural.zero) (consShape Natural.zero true) (fun _ => model.denote bottomCode empty)).mp generated
  exact bottom_not_generated ⟨_, children none⟩

theorem root_alone_insufficient :
    IndexedPolynomial.RecursiveSpaceRepresentation.ConstructorRoot
      (IndexedPositiveContainer.RecursiveSpaceRepresentation.blockPresentation sourceOrder block registered)
      (nativePayload block registered sourceOrder interpreted)
      (fun _ => nativeConstructor block registered sourceOrder interpreted constructorCode empty)
      environment (Natural.succ Natural.zero) badConsValue ∧
    ¬ IndexedPolynomial.Algebra.Generated algebra environment (Natural.succ Natural.zero) badConsValue :=
  ⟨⟨consShape Natural.zero true,
    ((IndexedPositiveContainer.RecursiveSpaceRepresentation.blockPresentation sourceOrder block registered).coding
      (consShape Natural.zero true)).extend (model.denote bottomCode empty) (fun _ => model.denote bottomCode empty), rfl⟩,
    bad_cons_refused⟩

#print axioms constructor_fields
#print axioms wrong_index_refused
#print axioms head_retained
#print axioms representation_roundtrip
#print axioms compiled_nil_root
#print axioms compiled_cons_root
#print axioms root_alone_insufficient

end
end Mettapedia.GSLT.LanguageDef.AdmittedContainerGeneratedControls
