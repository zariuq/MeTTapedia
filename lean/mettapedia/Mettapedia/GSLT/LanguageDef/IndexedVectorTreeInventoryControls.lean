import Mettapedia.Logic.HOL.IndexedContainerInventoryPredicate
import Mettapedia.GSLT.LanguageDef.ModuleSource.IndexedPositiveVectorLowering

/-!
# The complete textual VectorTree inventory in an indexed HOL model

The source list contains solved and branch in its declared order. Vector
counts read the original arity expression; the retained shape field is a
separate canonical Unit encoding. The model uses Boolean answers, natural
numbers and actual recursive trees. No constructor or family parameter is
identified with the earlier mixed-constructor interface.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedVectorTreeInventoryControls
open Mettapedia.Logic.HOL Mettapedia.TypeTheory
open IndexedPolynomial.Description IndexedPositiveContainer IndexedContainerPositionTerms

noncomputable section

abbrev I := VectorControl.interface
abbrev registry := VectorControl.registry
abbrev ordered := VectorControl.orderedFinitary

def codes : List (Code I registry 0 []) :=
  ModuleSource.IndexedPositiveVectorLowering.Controls.family.constructors.map
    (fun constructor => constructor.body.erase)

theorem codes_source :
    codes = [ModuleSource.IndexedPositiveVectorLowering.Controls.solved.body.erase,
      ModuleSource.IndexedPositiveVectorLowering.Controls.branch.body.erase] := rfl

inductive Base where | number | answer | space
abbrev N : Ty Base := .base .number
abbrev A : Ty Base := .base .answer
abbrev S : Ty Base := .base .space
abbrev PayloadTy : Ty Base := FiniteConstructorEncoding.payloadType [[A],[N,N]]

def scalarCarrier : Base → Type 1
  | .number => ULift.{1} Nat
  | .answer => ULift.{1} Bool
  | .space => ULift.{1} Unit
abbrev Payload := Ty.denote.{0,0} scalarCarrier PayloadTy

def carrier : Base → Type 1
  | .number => ULift.{1} Nat
  | .answer => ULift.{1} Bool
  | .space => ULift.{1} (RecursiveSpace.Tree Payload)

inductive Symbol : Ty Base → Type where
  | zero : Symbol N
  | successor : Symbol (N ⇒ N)
  | answer (value : Bool) : Symbol A
  | bottom : Symbol S
  | construct : Symbol (N ⇒ PayloadTy ⇒ (N ⇒ S) ⇒ S)

def model : HenkinModel.{0,0,0} Base Symbol := .standard carrier (fun symbol => match symbol with
  | .zero => .up 0
  | .successor => fun n => .up (n.down+1)
  | .answer value => .up value
  | .bottom => .up RecursiveSpace.bottom
  | .construct => fun tag payload children =>
      .up (RecursiveSpace.construct tag.down payload (fun n => (children (.up n)).down)))

def empty : model.Valuation [] := fun impossible => nomatch impossible
theorem full : model.FullDomains := HenkinModel.fullDomains_standard _ _
def zero : ClosedTerm Symbol N := .const .zero
def successor : ClosedTerm Symbol (N ⇒ N) := .const .successor

def dataType : I.SortCode → Ty Base
  | .length => N
  | .payload => A

def lengthVariable : {context : List I.SortCode} → VectorControl.LengthExpr context →
    Var (context.map dataType ++ []) N
  | _,.here => .vz
  | _,.there prior => .vs (lengthVariable prior)

def indices : IndexedConstructorTerms.Reading I Symbol where
  sort := dataType
  index := .prop
  parameters := []
  term _ := .top

theorem registered_entry {name : String} {entry : Entry I}
    (found : registry.lookup name = some entry) : entry = VectorControl.entry := by
  by_cases same : name = "Vector"
  · simpa [registry,VectorControl.registry,same] using found.symm
  · simp [registry,VectorControl.registry,same] at found

theorem registered_name {name : String} {entry : Entry I}
    (found : registry.lookup name = some entry) : name = "Vector" := by
  by_contra different
  simp [registry,VectorControl.registry,different] at found

def countTerm {context : List I.SortCode} (name : String) (entry : Entry I)
    (found : registry.lookup name = some entry) (output : entry.OutputExpr context) :
    Term Symbol (context.map indices.sort ++ indices.parameters) (N ⇒ N) := by
  obtain rfl := registered_entry found
  exact .lam (weaken (.var (lengthVariable output)))

def reading : Reading I registry Symbol where
  indices := indices
  number := N
  one := .app successor zero
  shapeType := fun _ _ _ => N
  count := countTerm

def encodeValue : ∀ sort, I.Value sort → Ty.denote.{0,0} model.Carrier (indices.sort sort)
  | .length,value => .up value
  | .payload,value => .up value

def encodeShape (name : String) (entry : Entry I) (found : registry.lookup name = some entry)
    (_output : entry.Output) (_shape : entry.container.Shape _output) :
    Ty.denote.{0,0} model.Carrier (reading.shapeType name entry found) := .up 0

theorem length_denote {context : List I.SortCode} (expression : VectorControl.LengthExpr context)
    (environment : Env I.Value context) :
    model.denote (.var (lengthVariable expression)) (indices.valuation model encodeValue empty environment) =
      ULift.up (VectorControl.evalLength expression environment) := by
  induction expression with
  | here => rfl
  | there prior previous => exact previous environment.2

def realization : Realization reading ordered model where
  numbers := Equiv.ulift.symm
  value := encodeValue
  index _ := ULift.up True
  shape := encodeShape
  parameterValues := empty
  index_correct := by intros; rfl
  one_correct := by intros; rfl
  count_correct := by
    intro context name entry found output environment shape
    obtain rfl := registered_name found
    obtain rfl := registered_entry found
    change model.denote (.var (lengthVariable output)) (indices.valuation model encodeValue empty environment) =
      ULift.up (List.ofFn (fun index : Fin (VectorControl.evalLength output environment) => index)).length
    simpa only [List.length_ofFn] using length_denote output environment

def shapeGuard {context : List I.SortCode} (name : String) (entry : Entry I)
    (found : registry.lookup name = some entry) (_output : entry.OutputExpr context) :
    Term Symbol (context.map indices.sort ++ indices.parameters) (reading.shapeType name entry found ⇒ .prop) :=
  .lam (.eq (.var .vz) (weakenCtx _ zero))

def guards : FieldGuards reading where
  value _ := .lam .top
  shape := shapeGuard

theorem images : FieldImages realization guards where
  value_correct := by
    intro sort target
    cases sort <;>
      exact ⟨fun _ => ⟨target.down,rfl⟩,fun _ => True.intro⟩
  shape_correct := by
    intro context name entry found output environment target
    obtain rfl := registered_name found
    obtain rfl := registered_entry found
    change target = model.denote (weakenCtx _ zero)
      (model.extend (indices.valuation model encodeValue empty environment) target) ↔ _
    rw [model.denote_weakenCtx]
    change target = ULift.up 0 ↔ ∃ _shape : Unit, ULift.up 0 = target
    exact ⟨fun same => ⟨(),same.symm⟩,fun ⟨_,same⟩ => same.symm⟩

theorem injections : FieldInjective realization where
  value := by
    intro sort
    cases sort <;> exact fun first second same => congrArg ULift.down same
  shape := by
    intro name entry found output first second _
    obtain rfl := registered_name found
    obtain rfl := registered_entry found
    change Unit at first second
    exact Subsingleton.elim first second

def numeral : Nat → ClosedTerm Symbol N
  | 0 => zero
  | n+1 => .app successor (numeral n)
theorem numeral_meaning (n : Nat) : model.denote (numeral n) empty = realization.numbers n := by
  induction n with
  | zero => rfl
  | succ n previous =>
      change ULift.up ((model.denote (numeral n) empty).down+1) = ULift.up (n+1)
      rw [previous]
      rfl

theorem source_fields : codes.map reading.fields = [[A],[N,N]] := rfl
def bottom : ClosedTerm Symbol S := .const .bottom
def constructor : ClosedTerm Symbol (N ⇒ FiniteConstructorEncoding.payloadType (codes.map reading.fields) ⇒ (N ⇒ S) ⇒ S) :=
  .const .construct

theorem constructor_fields : ∀ tag payload children otherTag otherPayload otherChildren,
    model.denote constructor empty tag payload children =
      model.denote constructor empty otherTag otherPayload otherChildren →
      payload = otherPayload ∧ children = otherChildren := by
  intro tag payload children otherTag otherPayload otherChildren same
  have trees := congrArg ULift.down same
  change RecursiveSpace.construct tag.down payload (fun n => (children (.up n)).down) =
    RecursiveSpace.construct otherTag.down otherPayload (fun n => (otherChildren (.up n)).down) at trees
  obtain ⟨_,payloads,descendants⟩ := (RecursiveSpace.construct_injective _ _ _ _ _ _).mp trees
  refine ⟨payloads,?_⟩
  funext value
  cases value with
  | up n => apply ULift.ext; exact congrFun descendants n


abbrev environment : Env I.Value [] := PUnit.unit

theorem represented_context : realization.Represents environment Subst.id empty := by
  intro type impossible
  nomatch impossible

theorem index_injective : Function.Injective realization.index := by
  intro first second _
  change Unit at first second
  exact Subsingleton.elim first second

theorem constructor_shape_separation :
    IndexedContainerInventory.HOLShapeSeparation codes ordered realization constructor empty :=
  IndexedContainerInventory.HOLShapeSeparation.of_raw codes ordered realization constructor empty constructor_fields

def algebra := IndexedContainerInventory.nativeAlgebra codes ordered realization bottom constructor empty
def represented := IndexedContainerInventory.nativeGeneratedRepresentation codes ordered realization bottom constructor empty
  injections constructor_shape_separation

def program := IndexedContainerInventory.memberProgram codes (guards := guards)
  Subst.id numeral zero successor bottom constructor

theorem program_exact (value : Ty.denote model.Carrier S) (index : Unit) :
    (model.denote program empty value (realization.index index)).down ↔
      IndexedPolynomial.Algebra.Generated algebra environment index value :=
  IndexedContainerInventory.memberProgram_denote codes ordered realization images Subst.id numeral empty environment
    represented_context zero successor full empty rfl (fun _ => rfl) bottom constructor injections
    constructor_shape_separation index_injective numeral_meaning value index

def comparison (index : Unit) := IndexedContainerInventory.nativeFamilyEquivalence codes ordered realization images
  Subst.id numeral empty environment represented_context zero successor full empty rfl (fun _ => rfl)
  bottom constructor injections constructor_shape_separation index_injective numeral_meaning index

theorem source_roundtrip (index : Unit) (tree : Inventory.Family codes environment index) :
    (comparison index).symm (comparison index tree) = tree :=
  (comparison index).symm_apply_apply tree

theorem target_roundtrip (index : Unit)
    (value : {value : Ty.denote model.Carrier S // (model.denote program empty value (realization.index index)).down}) :
    comparison index ((comparison index).symm value) = value :=
  (comparison index).apply_symm_apply value

def solvedShape (answer : Bool) : (Inventory.polynomial codes).Shape environment () := by
  refine ⟨⟨0,by decide⟩,?_⟩
  change Code.Shape (show Code I registry 0 [] from .data VectorControl.DataSort.payload (.result ())) environment ()
  exact ⟨answer,⟨⟨rfl⟩⟩⟩

def branchShape (length : Nat) : (Inventory.polynomial codes).Shape environment () :=
  ⟨⟨1,by decide⟩,VectorControl.shapeAt length⟩

def solvedValue (answer : Bool) : Ty.denote.{0,0} model.Carrier S :=
  algebra.act environment () ⟨solvedShape answer,fun impossible => nomatch impossible⟩

def branchValue (length : Nat) : Ty.denote.{0,0} model.Carrier S :=
  algebra.act environment () ⟨branchShape length,fun _ => solvedValue false⟩

theorem solved_generated (answer : Bool) :
    IndexedPolynomial.Algebra.Generated algebra environment () (solvedValue answer) :=
  IndexedPolynomial.Algebra.generated_closed algebra environment () (solvedShape answer) _
    (fun impossible => nomatch impossible)

theorem branch_generated (length : Nat) :
    IndexedPolynomial.Algebra.Generated algebra environment () (branchValue length) :=
  IndexedPolynomial.Algebra.generated_closed algebra environment () (branchShape length) _
    (fun _ => solved_generated false)

theorem solved_member (answer : Bool) :
    (model.denote program empty (solvedValue answer) (realization.index ())).down :=
  (program_exact _ ()).mpr (solved_generated answer)

theorem branch_member (length : Nat) :
    (model.denote program empty (branchValue length) (realization.index ())).down :=
  (program_exact _ ()).mpr (branch_generated length)

theorem wrong_index_refused (value : Ty.denote model.Carrier S) :
    ¬ (model.denote program empty value (ULift.up False)).down := by
  apply IndexedContainerInventory.memberProgram_junk_index_refused codes ordered realization images
    Subst.id numeral empty environment represented_context zero successor full bottom constructor
  intro index same
  exact Eq.mp (congrArg ULift.down same) True.intro

def branchPoint (length : Nat) : ConstructorPoint reading codes environment :=
  ⟨⟨1,by decide⟩,(),VectorControl.shapeAt length⟩

theorem active_branch_iff (length slot : Nat) :
    (model.denote (guards.positions codes Subst.id numeral zero successor).activeProgram empty
      (IndexedContainerInventory.nativePayload codes ordered realization environment
        (IndexedContainerInventory.sourcePoint codes environment (branchPoint length)))
      (realization.numbers slot)).down ↔ slot < length := by
  apply (IndexedContainerInventory.activeProgram_exact codes ordered realization images Subst.id numeral empty
    environment represented_context zero successor full empty rfl (fun _ => rfl) (branchPoint length) slot).trans
  change (∃ position, ((IndexedPositiveContainer.RecursiveSpaceRepresentation.codePresentation
    ordered VectorControl.code).coding (VectorControl.shapeAt length)).decode slot = some position) ↔ slot < length
  exact IndexedPositiveContainer.RecursiveSpaceRepresentation.vector_active_iff length slot

theorem two_refuses_two :
    ¬ (model.denote (guards.positions codes Subst.id numeral zero successor).activeProgram empty
      (IndexedContainerInventory.nativePayload codes ordered realization environment
        (IndexedContainerInventory.sourcePoint codes environment (branchPoint 2)))
      (realization.numbers 2)).down :=
  fun active => (Nat.lt_irrefl 2) ((active_branch_iff 2 2).mp active)

theorem three_accepts_two :
    (model.denote (guards.positions codes Subst.id numeral zero successor).activeProgram empty
      (IndexedContainerInventory.nativePayload codes ordered realization environment
        (IndexedContainerInventory.sourcePoint codes environment (branchPoint 3)))
      (realization.numbers 2)).down :=
  (active_branch_iff 3 2).mpr (by decide)


theorem solved_branch_distinct (answer : Bool) (length : Nat) :
    solvedValue answer ≠ branchValue length := by
  intro same
  have layers := IndexedContainerInventory.nativeAlgebra_injective codes ordered realization bottom constructor empty
    injections constructor_shape_separation environment () same
  have ordinals := congrArg (fun layer => layer.1.1.val) layers
  have impossible : (0 : Nat) = 1 := ordinals
  omega

theorem solved_answers_distinct : solvedValue true ≠ solvedValue false := by
  intro same
  have layers := IndexedContainerInventory.nativeAlgebra_injective codes ordered realization bottom constructor empty
    injections constructor_shape_separation environment () same
  have shapes : solvedShape true = solvedShape false := congrArg Sigma.fst layers
  have fields := (Sigma.mk.inj_iff.mp shapes).2
  have values : (true : Bool) = false := congrArg Sigma.fst (eq_of_heq fields)
  cases values

theorem changed_length_distinct {first second : Nat} (different : first ≠ second) :
    branchValue first ≠ branchValue second := by
  intro same
  have layers := IndexedContainerInventory.nativeAlgebra_injective codes ordered realization bottom constructor empty
    injections constructor_shape_separation environment () same
  have shapes : branchShape first = branchShape second := congrArg Sigma.fst layers
  have fields := (Sigma.mk.inj_iff.mp shapes).2
  have lengths : first = second := congrArg Sigma.fst (eq_of_heq fields)
  exact different lengths


def orderedChildren (first second : Bool) (position : (Inventory.polynomial codes).Position (branchShape 2)) :
    Ty.denote.{0,0} model.Carrier S :=
  if (VectorControl.positionEquiv 2 position).val = 0 then solvedValue first else solvedValue second

def orderedBranch (first second : Bool) : Ty.denote.{0,0} model.Carrier S :=
  algebra.act environment () ⟨branchShape 2,orderedChildren first second⟩

theorem ordered_branch_generated (first second : Bool) :
    IndexedPolynomial.Algebra.Generated algebra environment () (orderedBranch first second) := by
  apply IndexedPolynomial.Algebra.generated_closed algebra environment () (branchShape 2)
  intro position
  unfold orderedChildren
  split <;> exact solved_generated _

theorem ordered_branch_member (first second : Bool) :
    (model.denote program empty (orderedBranch first second) (realization.index ())).down :=
  (program_exact _ ()).mpr (ordered_branch_generated first second)

theorem exchanged_children_distinct : orderedBranch true false ≠ orderedBranch false true := by
  intro same
  have layers := IndexedContainerInventory.nativeAlgebra_injective codes ordered realization bottom constructor empty
    injections constructor_shape_separation environment () same
  have functions : orderedChildren true false = orderedChildren false true :=
    eq_of_heq (Sigma.mk.inj_iff.mp layers).2
  have observed := congrFun functions ((VectorControl.positionEquiv 2).symm ⟨0,by decide⟩)
  change (if (VectorControl.positionEquiv 2 ((VectorControl.positionEquiv 2).symm ⟨0,by decide⟩)).val = 0
      then solvedValue true else solvedValue false) =
    (if (VectorControl.positionEquiv 2 ((VectorControl.positionEquiv 2).symm ⟨0,by decide⟩)).val = 0
      then solvedValue false else solvedValue true) at observed
  rw [Equiv.apply_symm_apply] at observed
  exact solved_answers_distinct observed

#print axioms ordered_branch_member
#print axioms exchanged_children_distinct

#print axioms solved_branch_distinct
#print axioms solved_answers_distinct
#print axioms changed_length_distinct

#print axioms program_exact
#print axioms source_roundtrip
#print axioms target_roundtrip
#print axioms solved_member
#print axioms branch_member
#print axioms wrong_index_refused
#print axioms active_branch_iff
#print axioms two_refuses_two
#print axioms three_accepts_two

#print axioms codes_source
#print axioms realization
#print axioms images
#print axioms injections
#print axioms source_fields
#print axioms constructor_fields
end
end Mettapedia.GSLT.LanguageDef.IndexedVectorTreeInventoryControls
