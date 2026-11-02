import Mettapedia.Logic.HOL.IndexedContainerConstructorPrograms
import Mettapedia.GSLT.LanguageDef.IndexedContainerPositionTermsControls

/-!
# Parameter-dependent field-image controls

One fixed guard program reads a declared numerical parameter. Boolean fields
are represented by that number and its successor. Two interleaved data
binders must keep reading the original parameter. Replacing it by an earlier
field would accept the separating mixed-world example incorrectly.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.GSLT.LanguageDef.IndexedContainerParameterGuardControls
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.IndexedContainerPositionTerms
open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.TypeTheory.IndexedPositiveContainer
open IndexedContainerPositionTermsControls (number Symbol model empty zero successor full)

def interface : Interface where
  SortCode := Unit
  Value := fun _ => Bool
  Index := Unit
  IndexExpr := fun _ => Unit
  evalIndex := fun _ _ => ()

def registry : Registry interface where lookup _ := none
def ordered : registry.OrderedFinitary where
  containerOrdered := by intro name entry registered; simp [registry] at registered

def indices : IndexedConstructorTerms.Reading interface Symbol where
  sort := fun _ => number
  index := .prop
  parameters := [number]
  term _ := .top

def reading : Reading interface registry Symbol where
  indices := indices
  number := number
  one := .app successor zero
  shapeType := fun _ _ _ => number
  count := by intro context name entry registered; simp [registry] at registered

def parameterValues (offset : Nat) : model.Valuation [number] :=
  model.extend (σ := number) empty (ULift.up offset)

def encodeValue (offset : Nat) : Bool → Ty.denote.{0,0} model.Carrier number
  | false => ULift.up offset
  | true => ULift.up (offset + 1)

def realization (offset : Nat) : Realization reading ordered model where
  numbers := Equiv.ulift.symm
  value := fun _ => encodeValue offset
  index := fun _ => ULift.up True
  shape := by intro name entry registered; simp [registry] at registered
  parameterValues := parameterValues offset
  index_correct := by intro context expression environment; rfl
  one_correct := by intro values; rfl
  count_correct := by intro context name entry registered; simp [registry] at registered

def parameterGuard : Term Symbol [number] (number ⇒ .prop) :=
  .lam (.or (.eq (.var .vz) (.var (.vs .vz)))
    (.eq (.var .vz) (.app (.const .successor) (.var (.vs .vz)))))

def guards : FieldGuards reading where
  value := fun _ => parameterGuard
  shape := by intro context name entry registered; simp [registry] at registered

theorem value_image (offset : Nat) (sort : interface.SortCode)
    (target : Ty.denote.{0,0} model.Carrier number) :
    (model.denote (guards.value sort) (realization offset).parameterValues target).down ↔
      ∃ source : interface.Value sort, (realization offset).value sort source = target := by
  cases sort
  change (target = ULift.up offset ∨ target = ULift.up (offset + 1)) ↔
    ∃ source : Bool, encodeValue offset source = target
  constructor
  · rintro (base | next)
    · exact ⟨false, base.symm⟩
    · exact ⟨true, next.symm⟩
  · rintro ⟨source, rfl⟩
    cases source with
    | false => exact Or.inl rfl
    | true => exact Or.inr rfl

theorem images (offset : Nat) : FieldImages (realization offset) guards where
  value_correct := value_image offset
  shape_correct := by intro context name entry registered; simp [registry] at registered

def pairCode : Code interface registry 0 [] := .data () (.data () (.result ()))
def pairShape (first second : Bool) : Code.Shape pairCode PUnit.unit () := ⟨first, second, ⟨⟨rfl⟩⟩⟩
def fields (first second : Nat) : Env (Ty.denote.{0,0} model.Carrier) (reading.fields pairCode) :=
  (ULift.up first, ULift.up second, PUnit.unit)

theorem parameter_represented (offset : Nat) :
    (realization offset).Represents (context := []) PUnit.unit Subst.id (parameterValues offset) := by
  intro type entry
  cases entry with
  | vz => rfl
  | vs impossible => exact nomatch impossible

theorem pair_image_exact (offset : Nat) (data : Env (Ty.denote.{0,0} model.Carrier) (reading.fields pairCode)) :
    CurriedPredicates.holds model (reading.fields pairCode) (guards.compile pairCode Subst.id) (parameterValues offset) data ↔
      ∃ (index : interface.Index) (sourceShape : Code.Shape pairCode PUnit.unit index),
        (realization offset).encodeFields pairCode sourceShape = data :=
  (images offset).compile_holds pairCode PUnit.unit Subst.id (parameterValues offset) (parameter_represented offset) data

theorem pair_image_two (data : Env (Ty.denote.{0,0} model.Carrier) (reading.fields pairCode)) :
    CurriedPredicates.holds model (reading.fields pairCode) (guards.compile pairCode Subst.id) (parameterValues 2) data ↔
      ∃ (index : interface.Index) (sourceShape : Code.Shape pairCode PUnit.unit index),
        (realization 2).encodeFields pairCode sourceShape = data :=
  (images 2).compile_holds pairCode PUnit.unit Subst.id (parameterValues 2) (parameter_represented 2) data

theorem allowed_pair (offset first second : Nat) :
    CurriedPredicates.holds model (reading.fields pairCode) (guards.compile pairCode Subst.id)
      (parameterValues offset) (fields first second) ↔
      (first = offset ∨ first = offset + 1) ∧ (second = offset ∨ second = offset + 1) := by
  change (((ULift.up first : ULift.{1} Nat) = ULift.up offset ∨ ULift.up first = ULift.up (offset + 1)) ∧
    ((ULift.up second = ULift.up offset ∨ ULift.up second = ULift.up (offset + 1)) ∧ True)) ↔ _
  simp only [and_true, ULift.up.injEq]

theorem world_two_accepts : CurriedPredicates.holds model (reading.fields pairCode)
    (guards.compile pairCode Subst.id) (parameterValues 2) (fields 2 3) :=
  (allowed_pair _ _ _).mpr ⟨Or.inl rfl, Or.inr rfl⟩

theorem reversed_fields_accept : CurriedPredicates.holds model (reading.fields pairCode)
    (guards.compile pairCode Subst.id) (parameterValues 2) (fields 3 2) :=
  (allowed_pair _ _ _).mpr ⟨Or.inr rfl, Or.inl rfl⟩

theorem world_three_accepts : CurriedPredicates.holds model (reading.fields pairCode)
    (guards.compile pairCode Subst.id) (parameterValues 3) (fields 3 4) :=
  (allowed_pair _ _ _).mpr ⟨Or.inl rfl, Or.inr rfl⟩

theorem earlier_field_capture_refused : ¬ CurriedPredicates.holds model (reading.fields pairCode)
    (guards.compile pairCode Subst.id) (parameterValues 2) (fields 3 4) :=
  fun accepted => (by decide : ¬ ((3 = 2 ∨ 3 = 2 + 1) ∧ (4 = 2 ∨ 4 = 2 + 1)))
    ((allowed_pair _ _ _).mp accepted)

theorem changed_world_refused : ¬ CurriedPredicates.holds model (reading.fields pairCode)
    (guards.compile pairCode Subst.id) (parameterValues 3) (fields 2 3) :=
  fun accepted => (by decide : ¬ ((2 = 3 ∨ 2 = 3 + 1) ∧ (3 = 3 ∨ 3 = 3 + 1)))
    ((allowed_pair _ _ _).mp accepted)

theorem parameter_survives_data :
    (indices.valuation model (realization 2).value (parameterValues 2)
      (context := [(), ()]) (false, true, PUnit.unit))
      (Rename.weakenPrefix [number, number] (.vz : Var [number] number)) = ULift.up 2 :=
  (realization 2).parameter_valuation (context := [(), ()]) (false, true, PUnit.unit) .vz

def two : ClosedTerm Symbol number := .app successor (.app successor zero)
def closedParameters : Subst Symbol [number] []
  | _, .vz => two
  | _, .vs impossible => nomatch impossible

theorem closed_represented : (realization 2).Represents (context := []) PUnit.unit closedParameters empty := by
  intro type entry
  cases entry with
  | vz => rfl
  | vs impossible => exact nomatch impossible

theorem closed_instance_accepted : CurriedPredicates.holds model (reading.fields pairCode)
    (guards.compile pairCode closedParameters) empty (fields 2 3) :=
  ((images 2).compile_holds pairCode PUnit.unit closedParameters empty closed_represented (fields 2 3)).mpr
    ⟨(), pairShape false true, rfl⟩

theorem wrong_parameter_context_refused :
    ¬ (realization 2).Represents (context := []) PUnit.unit Subst.id (parameterValues 3) := by
  intro represented
  have same := represented (.vz : Var [number] number)
  have impossible : (3 : Nat) = 2 := congrArg ULift.down same
  cases impossible

theorem closed_parameter_denotes :
    model.denote (Mettapedia.Logic.HOL.subst (reading.parameterSubst (context := []) closedParameters) parameterGuard) empty =
      model.denote parameterGuard (realization 2).parameterValues :=
  (realization 2).parameterSubst_denote (context := []) PUnit.unit closedParameters empty closed_represented parameterGuard

#print axioms pair_image_exact
#print axioms closed_instance_accepted
#print axioms closed_parameter_denotes
end Mettapedia.GSLT.LanguageDef.IndexedContainerParameterGuardControls
