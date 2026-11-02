import Mettapedia.GSLT.LanguageDef.AdmittedContainerPredicate
import Mettapedia.GSLT.LanguageDef.AdmittedContainerGeneratedControls

/-!
# Full recursive membership and open-parameter controls

The admitted Vector example uses the actual generated membership program.
Parent-only evidence, invalid children and wrong indices remain distinguishable.
A separate open signature retains all operation variables under the generated
binders and responds to changes in its shape parameter.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.AdmittedContainerPredicateControls
open Mettapedia.Logic.HOL Mettapedia.TypeTheory
open AdmittedContainerHOL AdmittedContainerGeneratedControls IndexedInductiveNatVec

noncomputable section

namespace Closed
def zeroCode : ClosedTerm Symbol number := .const .zero
def successorCode : ClosedTerm Symbol (number ⇒ number) := .const .successor
theorem zero_meaning : model.denote zeroCode empty = interpreted.numbers 0 := rfl
theorem successor_meaning (n : Nat) :
    model.denote successorCode empty (interpreted.numbers n) = interpreted.numbers (n+1) := rfl

def program := memberProgram block registered (guards := guards) Subst.id numeral zeroCode successorCode bottomCode constructorCode

theorem program_exact (value : Ty.denote model.Carrier space) (index : Natural.Carrier) :
    (model.denote program empty value (interpreted.index index)).down ↔
      IndexedPolynomial.Algebra.Generated algebra environment index value :=
  memberProgram_denote block registered sourceOrder interpreted images Subst.id numeral empty environment represented_context
    zeroCode successorCode full empty zero_meaning successor_meaning bottomCode constructorCode injections constructor_shape_separation
    index_injective numeral_meaning value index

theorem nil_member : (model.denote program empty nilValue (interpreted.index Natural.zero)).down :=
  (program_exact _ _).mpr nil_generated
theorem cons_member (head : Bool) :
    (model.denote program empty (consValue head) (interpreted.index (Natural.succ Natural.zero))).down :=
  (program_exact _ _).mpr (cons_generated head)
theorem wrong_index_refused : ¬ (model.denote program empty (consValue true) (interpreted.index Natural.zero)).down :=
  fun member => AdmittedContainerGeneratedControls.wrong_index_refused ((program_exact _ _).mp member)
theorem bad_child_refused :
    ¬ (model.denote program empty badConsValue (interpreted.index (Natural.succ Natural.zero))).down :=
  fun member => bad_cons_refused ((program_exact _ _).mp member)
theorem bottom_refused (index : Natural.Carrier) :
    ¬ (model.denote program empty (model.denote bottomCode empty) (interpreted.index index)).down :=
  fun member => bottom_not_generated ⟨index, (program_exact _ _).mp member⟩

def comparison (index : Natural.Carrier) :=
  nativeFamilyEquivalence block registered sourceOrder interpreted images Subst.id numeral empty environment represented_context
    zeroCode successorCode full empty zero_meaning successor_meaning bottomCode constructorCode injections constructor_shape_separation
    index_injective numeral_meaning index

theorem comparison_injective (index : Natural.Carrier) :
    Function.Injective (fun source : block.Family environment index => (comparison index source).val) := by
  intro first second same
  exact (comparison index).injective (Subtype.ext same)

theorem comparison_recursor (index : Natural.Carrier) (source : block.Family environment index) :
    (comparison index source).val = block.recursor
      ((IndexedPositiveContainer.Unindexed.blockSignatureEquiv block registered).pullAlgebra algebra) environment index source :=
  nativeFamilyEquivalence_recursor block registered sourceOrder interpreted images Subst.id numeral empty environment represented_context
    zeroCode successorCode full empty zero_meaning successor_meaning bottomCode constructorCode injections constructor_shape_separation
    index_injective numeral_meaning index source

theorem comparison_roundtrip (index : Natural.Carrier) (source : block.Family environment index) :
    (comparison index).symm (comparison index source) = source := (comparison index).symm_apply_apply source

theorem target_roundtrip (index : Natural.Carrier)
    (target : {value : Ty.denote model.Carrier space // (model.denote program empty value (interpreted.index index)).down}) :
    comparison index ((comparison index).symm target) = target := (comparison index).apply_symm_apply target
end Closed

namespace Open
abbrev ConstructorType : Ty BaseCode := number ⇒ payload ⇒ (number ⇒ space) ⇒ space
abbrev ShapeType : Ty BaseCode := number ⇒ payload ⇒ .prop
abbrev ActiveType : Ty BaseCode := payload ⇒ number ⇒ .prop
abbrev EdgeType : Ty BaseCode := payload ⇒ number ⇒ space ⇒ .prop
abbrev context : Ctx BaseCode := [space, ConstructorType, ShapeType, ActiveType, EdgeType]

def signature : RecursiveSpacePredicate.Contextual Symbol context where
  number := number
  payload := payload
  space := space
  bottom := .var .vz
  construct := .var (.vs .vz)
  validShape := .var (.vs (.vs .vz))
  active := .var (.vs (.vs (.vs .vz)))
  validEdge := .var (.vs (.vs (.vs (.vs .vz))))

def values (enabled : Prop) : model.Valuation context :=
  model.extend (σ := space) (model.extend (σ := ConstructorType) (model.extend (σ := ShapeType)
    (model.extend (σ := ActiveType) (model.extend (σ := EdgeType) empty
    ((fun _ _ _ => ULift.up True) : Ty.denote.{0,0} model.Carrier EdgeType))
    ((fun _ _ => ULift.up False) : Ty.denote.{0,0} model.Carrier ActiveType))
    ((fun _ _ => ULift.up enabled) : Ty.denote.{0,0} model.Carrier ShapeType))
    (model.denote constructorCode empty)) (model.denote bottomCode empty)

def leafPayload : Ty.denote.{0,0} model.Carrier payload := model.denote
  (IndexedContainerPositionTerms.payloadTerm reading (codes block registered) nilOccurrence nilArguments) empty
def leaf : Ty.denote.{0,0} model.Carrier space :=
  model.denote constructorCode empty (interpreted.numbers 0) leafPayload (fun _ => model.denote bottomCode empty)

theorem enabled_leaf : (model.denote signature.least (values True) leaf).down := by
  rw [RecursiveSpacePredicate.Contextual.least, PredicateFixedPoint.least_denote]
  intro property _ closed
  apply closed leaf (full _ _)
  apply (signature.operator_meaning model full (values True) property leaf).mpr
  refine ⟨interpreted.numbers 0, leafPayload, (fun _ => model.denote bottomCode empty), True.intro, rfl, ?_⟩
  intro slot
  constructor
  · intro impossible
    exact False.elim impossible
  · intro _
    rfl

theorem disabled_empty (value : Ty.denote model.Carrier space) :
    ¬ (model.denote signature.least (values False) value).down := by
  rw [RecursiveSpacePredicate.Contextual.least, PredicateFixedPoint.least_denote]
  intro member
  apply member (fun _ => ULift.up False) (full _ _)
  intro point _ step
  obtain ⟨_, _, _, impossible, _⟩ :=
    (signature.operator_meaning model full (values False) (fun _ => ULift.up False) point).mp step
  exact impossible

theorem parameter_observed : model.denote signature.least (values True) ≠ model.denote signature.least (values False) := by
  intro same
  have observed := enabled_leaf
  rw [same] at observed
  exact disabled_empty leaf observed

def disable : Subst Symbol context context := fun index => match index with
  | .vz => .var .vz
  | .vs .vz => .var (.vs .vz)
  | .vs (.vs .vz) => .lam (.lam .bot)
  | .vs (.vs (.vs .vz)) => .var (.vs (.vs (.vs .vz)))
  | .vs (.vs (.vs (.vs .vz))) => .var (.vs (.vs (.vs (.vs .vz))))
  | .vs (.vs (.vs (.vs (.vs impossible)))) => nomatch impossible

def disabledSignature : RecursiveSpacePredicate.Contextual Symbol context :=
  { signature with validShape := .lam (.lam .bot) }

theorem substitution_retains_scope : Mettapedia.Logic.HOL.subst disable signature.least = disabledSignature.least := by
  rw [signature.subst_least]
  rfl

theorem fixed_point_free :
    (signature.fixedPoint (assumptions := [])).FunctionExtensionalityFree := signature.fixedPoint_free
end Open

namespace AdmittedOpen
abbrev context : Ctx BaseCode := [Open.ConstructorType]
def substitution : Subst Symbol [] context := fun impossible => nomatch impossible
def values : model.Valuation context := model.extend (σ := Open.ConstructorType) empty (model.denote constructorCode empty)
def bottom : Term Symbol context space := weaken bottomCode
def constructor : Term Symbol context Open.ConstructorType := .var .vz
def numeral (n : Nat) : Term Symbol context number := weaken (AdmittedContainerGeneratedControls.numeral n)

theorem represented : interpreted.Represents environment substitution values := by
  intro _ impossible
  nomatch impossible
theorem numeral_meaning (n : Nat) : model.denote (numeral n) values = interpreted.numbers n := by
  exact (Soundness.denote_weaken (σ := Open.ConstructorType) model
    (AdmittedContainerGeneratedControls.numeral n) empty (model.denote constructorCode empty)).trans
    (AdmittedContainerGeneratedControls.numeral_meaning n)
theorem constructor_fields : ∀ tag data children otherTag otherData otherChildren,
    model.denote constructor values tag data children = model.denote constructor values otherTag otherData otherChildren →
      data = otherData ∧ children = otherChildren := AdmittedContainerGeneratedControls.constructor_fields

theorem constructor_shape_separation :
    HOLShapeSeparation block registered sourceOrder interpreted constructor values :=
  HOLShapeSeparation.of_raw block registered sourceOrder interpreted constructor values constructor_fields

def algebra := nativeAlgebra block registered sourceOrder interpreted bottom constructor values
def nilValue := algebra.act environment Natural.zero ⟨nilShape, fun impossible => nomatch impossible⟩
theorem nil_generated : IndexedPolynomial.Algebra.Generated algebra environment Natural.zero nilValue :=
  IndexedPolynomial.Algebra.generated_closed algebra environment Natural.zero nilShape _ (fun impossible => nomatch impossible)
def program := memberProgram block registered (guards := guards) substitution numeral
  Closed.zeroCode Closed.successorCode bottom constructor
theorem nil_member : (model.denote program values nilValue (interpreted.index Natural.zero)).down :=
  (memberProgram_denote block registered sourceOrder interpreted images substitution numeral values environment represented
    Closed.zeroCode Closed.successorCode full empty Closed.zero_meaning Closed.successor_meaning bottom constructor injections
    constructor_shape_separation index_injective numeral_meaning nilValue Natural.zero).mpr nil_generated
end AdmittedOpen

namespace JunkIndex
def interface : IndexedPolynomial.Description.Interface where
  SortCode := Empty
  Value := fun impossible => nomatch impossible
  Index := Empty
  IndexExpr := fun _ => Empty
  evalIndex := fun impossible _ => nomatch impossible

abbrev registry := IndexedPositiveContainer.Unindexed.liftRegistry PositiveInductiveBlockBridge.Direct.registry interface
def reading : IndexedContainerPositionTerms.Reading interface registry Symbol where
  indices := {
    sort := fun impossible => nomatch impossible
    index := .prop
    parameters := []
    term := fun impossible => nomatch impossible }
  number := number
  one := .app (.const .successor) (.const .zero)
  shapeType _ _ impossible := by cases impossible
  count _ _ impossible _ := by cases impossible

def realization : IndexedContainerPositionTerms.Realization reading
    (IndexedPositiveContainer.Unindexed.liftOrdered sourceOrder) model where
  numbers := interpreted.numbers
  value := fun impossible => nomatch impossible
  index := fun impossible => nomatch impossible
  shape _ _ impossible := by cases impossible
  parameterValues := empty
  index_correct := by intro _ impossible; cases impossible
  one_correct := by intro _; rfl
  count_correct := by intro _ _ _ impossible; cases impossible

def guards : IndexedContainerPositionTerms.FieldGuards reading where
  value := fun impossible => nomatch impossible
  shape _ _ impossible := by cases impossible
theorem images : IndexedContainerPositionTerms.FieldImages realization guards where
  value_correct := by intro impossible; cases impossible
  shape_correct := by intro _ _ _ impossible; cases impossible

def block : PositiveInductiveBlock.Admitted PositiveInductiveBlockBridge.Direct.registry interface 0 [] where
  constructors := []
  uniqueNames := by decide
theorem registered : block.WellRegistered := by intro _ impossible; cases impossible

abbrev ConstructorType : Ty BaseCode := number ⇒ .prop ⇒ (number ⇒ space) ⇒ space
abbrev context : Ctx BaseCode := [ConstructorType]
def substitution : Subst Symbol [] context := fun impossible => nomatch impossible
def constructor : Term Symbol context ConstructorType := .var .vz
def bottom : Term Symbol context space := weaken bottomCode
def numeral (n : Nat) : Term Symbol context number := weaken (AdmittedContainerGeneratedControls.numeral n)
def program := memberProgram block registered (guards := guards) substitution numeral
  Closed.zeroCode Closed.successorCode bottom constructor

theorem represented (values : model.Valuation context) :
    realization.Represents (context := []) (PUnit.unit : IndexedPolynomial.Description.Env interface.Value []) substitution values := by
  intro _ impossible
  nomatch impossible

theorem foreign_index_refused (values : model.Valuation context) (value : Ty.denote.{0,0} model.Carrier space) :
    ¬ (model.denote program values value (ULift.up False)).down :=
  memberProgram_junk_index_refused block registered sourceOrder realization images substitution numeral values PUnit.unit
    (represented values) Closed.zeroCode Closed.successorCode full bottom constructor value (ULift.up False)
    (fun impossible => nomatch impossible)
end JunkIndex

#print axioms Closed.program_exact
#print axioms Closed.bad_child_refused
#print axioms Closed.comparison_recursor
#print axioms Open.enabled_leaf
#print axioms Open.disabled_empty
#print axioms Open.substitution_retains_scope
#print axioms AdmittedOpen.nil_member
#print axioms JunkIndex.foreign_index_refused

end
end Mettapedia.GSLT.LanguageDef.AdmittedContainerPredicateControls
