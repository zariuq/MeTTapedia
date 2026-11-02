import Mettapedia.Logic.HOL.IndexedContainerConstructorPrograms
import Mettapedia.GSLT.LanguageDef.IndexedContainerPositionTermsControls

/-!
# Field-image and constructor-inventory controls

The concrete readings distinguish natural values, Boolean encodings, List
shape lengths and the canonical Vector shape. Invalid shape fields must be
refused even when the position counts are unchanged. Constructor occurrences
and empty result fibres remain explicit.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.GSLT.LanguageDef.IndexedContainerFieldGuardControls

open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.IndexedContainerPositionTerms
open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.TypeTheory.IndexedPositiveContainer
open Mettapedia.TypeTheory
open IndexedContainerPositionTermsControls

def valueGuard : (sort : interface.SortCode) → ClosedTerm Symbol (indices.sort sort ⇒ .prop)
  | .length => .lam .top
  | .payload => .lam (.or (.eq (.var .vz) (weaken zero))
      (.eq (.var .vz) (weaken (.app successor zero))))

def shapeGuard {context : List interface.SortCode} (name : String) (_entry : Entry interface)
    (_registered : registry.lookup name = some _entry) (_output : _entry.OutputExpr context) :
    Term Symbol (context.map indices.sort ++ indices.parameters) (number ⇒ .prop) :=
  if name = "List" then .lam .top else .lam (.eq (.var .vz) (weakenCtx _ zero))

def guards : FieldGuards reading where
  value := valueGuard
  shape := shapeGuard

theorem value_image (sort : interface.SortCode) (values : model.Valuation [])
    (target : Ty.denote.{0,0} model.Carrier (indices.sort sort)) :
    (model.denote (valueGuard sort) values target).down ↔
      ∃ source : interface.Value sort, realization.value sort source = target := by
  cases sort with
  | length =>
      change True ↔ ∃ source : Nat, ULift.up source = target
      exact ⟨fun _ => ⟨target.down, rfl⟩, fun _ => True.intro⟩
  | payload =>
      change (target = ULift.up 0 ∨ target = ULift.up 1) ↔
        ∃ source : Bool, encodeValue .payload source = target
      constructor
      · rintro (zero | one)
        · exact ⟨false, zero.symm⟩
        · exact ⟨true, one.symm⟩
      · rintro ⟨source, rfl⟩
        cases source with
        | false => exact Or.inl rfl
        | true => exact Or.inr rfl

theorem shape_image {context : List interface.SortCode} (name : String) (entry : Entry interface)
    (registered : registry.lookup name = some entry) (output : entry.OutputExpr context)
    (environment : Env interface.Value context) (target : Ty.denote.{0,0} model.Carrier number) :
    (model.denote (shapeGuard name entry registered output)
      (indices.valuation model encodeValue empty environment) target).down ↔
      ∃ source : entry.container.Shape (entry.evalOutput output environment),
        encodeShape name entry registered _ source = target := by
  by_cases list : name = "List"
  · subst name
    have same : listEntry = entry := by simpa [registry] using registered
    subst entry
    change True ↔ ∃ source : Nat, ULift.up source = target
    exact ⟨fun _ => ⟨target.down, rfl⟩, fun _ => True.intro⟩
  · by_cases vector : name = "Vector"
    · subst name
      have same : vectorEntry = entry := by simpa [registry] using registered
      subst entry
      simp only [shapeGuard, show ("Vector" : String) ≠ "List" by decide, if_false]
      change target = model.denote (weakenCtx _ zero)
        (model.extend (indices.valuation model encodeValue empty environment) target) ↔ _
      rw [model.denote_weakenCtx]
      change target = ULift.up 0 ↔ ∃ _source : Unit, ULift.up 0 = target
      exact ⟨fun same => ⟨(), same.symm⟩, fun ⟨_, same⟩ => same.symm⟩
    · simp [registry, list, vector] at registered

theorem images : FieldImages realization guards where
  value_correct := fun sort target => value_image sort empty target
  shape_correct := shape_image

def mixedFields (outer listLength inner vectorShape : Nat) :
    Env (Ty.denote.{0,0} model.Carrier) (reading.fields mixedCode) :=
  (ULift.up outer, ULift.up listLength, ULift.up inner, ULift.up vectorShape, PUnit.unit)

theorem allowed_mixed (outer listLength inner vectorShape : Nat) :
    CurriedPredicates.holds model (reading.fields mixedCode) (guards.compile mixedCode Subst.id) empty
      (mixedFields outer listLength inner vectorShape) ↔ vectorShape = 0 := by
  change (True ∧ (True ∧ (True ∧ ((ULift.up vectorShape : ULift.{1} Nat) = ULift.up 0 ∧ True)))) ↔ vectorShape = 0
  simp only [true_and, and_true, ULift.up.injEq]

theorem source_fields_accepted : CurriedPredicates.holds model (reading.fields mixedCode)
    (guards.compile mixedCode Subst.id) empty (mixedFields 7 3 2 0) :=
  (allowed_mixed _ _ _ _).mpr rfl

theorem forged_vector_shape_refused : ¬ CurriedPredicates.holds model (reading.fields mixedCode)
    (guards.compile mixedCode Subst.id) empty (mixedFields 7 3 2 9) :=
  fun accepted => (by decide : (9 : Nat) ≠ 0) ((allowed_mixed _ _ _ _).mp accepted)

theorem forged_shape_keeps_counts :
    OrderedPositionPrograms.evaluateFields model realization.numbers (reading.fields mixedCode) empty
      (mixedFields 7 3 2 9) (reading.compile mixedCode Subst.id) =
      [(1, ULift.up 7), (3, ULift.up 7), (2, ULift.up 7), (1, ULift.up 2)] := rfl

theorem mixed_image_exact (data : Env (Ty.denote.{0,0} model.Carrier) (reading.fields mixedCode)) :
    CurriedPredicates.holds model (reading.fields mixedCode) (guards.compile mixedCode Subst.id) empty data ↔
      ∃ (index : interface.Index) (sourceShape : Code.Shape mixedCode PUnit.unit index), realization.encodeFields mixedCode sourceShape = data :=
  images.compile_holds mixedCode PUnit.unit Subst.id empty (fun impossible => nomatch impossible) data

def boolCode : Code interface registry 0 [.length] := .data .payload (.result (.there .here))
def boolValues (outer : Nat) : model.Valuation [number] := model.extend (σ := number) empty (ULift.up outer)
def boolFields (raw : Nat) : Env (Ty.denote.{0,0} model.Carrier) (reading.fields boolCode) :=
  (ULift.up raw, PUnit.unit)

theorem bool_represented (outer : Nat) :
    realization.Represents (context := [.length]) (outer, PUnit.unit) Subst.id (boolValues outer) := by
  intro type entry
  cases entry with
  | vz => rfl
  | vs impossible => exact nomatch impossible

theorem allowed_bool (outer raw : Nat) :
    CurriedPredicates.holds model (reading.fields boolCode) (guards.compile boolCode Subst.id)
      (boolValues outer) (boolFields raw) ↔ raw = 0 ∨ raw = 1 := by
  change (((ULift.up raw : ULift.{1} Nat) = ULift.up 0 ∨ ULift.up raw = ULift.up 1) ∧ True) ↔ _
  simp only [and_true, ULift.up.injEq]

theorem false_field_accepted : CurriedPredicates.holds model (reading.fields boolCode)
    (guards.compile boolCode Subst.id) (boolValues 7) (boolFields 0) :=
  (allowed_bool _ _).mpr (Or.inl rfl)
theorem true_field_accepted : CurriedPredicates.holds model (reading.fields boolCode)
    (guards.compile boolCode Subst.id) (boolValues 7) (boolFields 1) :=
  (allowed_bool _ _).mpr (Or.inr rfl)
theorem non_boolean_field_refused : ¬ CurriedPredicates.holds model (reading.fields boolCode)
    (guards.compile boolCode Subst.id) (boolValues 7) (boolFields 2) :=
  fun accepted => (by decide : ¬ ((2 : Nat) = 0 ∨ 2 = 1)) ((allowed_bool _ _).mp accepted)

theorem wrong_index_empty (outer : Nat) : IsEmpty (Code.Shape boolCode (outer, PUnit.unit) (outer + 1)) where
  false sourceShape := by
    obtain ⟨_, ⟨⟨same⟩⟩⟩ := sourceShape
    change outer = outer + 1 at same
    omega

theorem wrong_index_refused (outer : Nat) (data : Env (Ty.denote.{0,0} model.Carrier) (reading.fields boolCode)) :
    ¬ (CurriedPredicates.holds model (reading.fields boolCode) (guards.compile boolCode Subst.id) (boolValues outer) data ∧
      CurriedPredicates.applyValues model (reading.fields boolCode)
        (model.denote (reading.resultProgram boolCode Subst.id) (boolValues outer)) data = ULift.up (outer + 1)) :=
  images.empty_index_refused (fun _ _ same => congrArg ULift.down same) boolCode
    (outer, PUnit.unit) Subst.id (boolValues outer) (bool_represented outer) data (outer + 1) (wrong_index_empty outer)

def codes : List (Code interface registry 0 []) := [mixedCode, mixedCode]
def numeral : Nat → ClosedTerm Symbol number
  | 0 => zero
  | n + 1 => .app successor (numeral n)
def inventory := guards.constructors codes Subst.id numeral
def positions := guards.positions codes Subst.id numeral zero successor
def first : Fin inventory.fields.length := ⟨0, by decide⟩
def second : Fin inventory.fields.length := ⟨1, by decide⟩
def firstData := encodeConstructorData realization codes first (mixedShape 7 3 2)
def secondData := encodeConstructorData realization codes second (mixedShape 7 3 2)

theorem inventory_source_accepted : inventory.dataAllowed model empty firstData :=
  images.encoded_data_allowed codes PUnit.unit Subst.id numeral empty (fun impossible => nomatch impossible) first (mixedShape 7 3 2)

theorem inventory_result : inventory.resultValue model empty firstData = ULift.up 2 :=
  FieldImages.encoded_data_result (guards := guards) (realization := realization)
    codes PUnit.unit Subst.id numeral empty (fun impossible => nomatch impossible) first (mixedShape 7 3 2)

theorem inventory_at_source_index : inventory.dataAllowed model empty firstData ∧
    inventory.resultValue model empty firstData = realization.index (2 : Nat) := by
  apply (images.inventory_at_index (fun _ _ same => congrArg ULift.down same) codes PUnit.unit Subst.id numeral empty
    (fun impossible => nomatch impossible) firstData (2 : Nat)).mpr
  exact ⟨mixedShape 7 3 2, rfl⟩

theorem inventory_positions_source_exact (slot : Nat) (target : Ty.denote.{0,0} model.Carrier number) :
    positions.related model empty firstData (ULift.up slot) target ↔
      ∃ position, ((RecursiveSpaceRepresentation.codePresentation ordered mixedCode).coding (mixedShape 7 3 2)).decode slot =
        some position ∧ realization.index (Code.next mixedCode (mixedShape 7 3 2) position) = target :=
  FieldImages.encoded_positions_exact (guards := guards) (realization := realization)
    codes PUnit.unit Subst.id numeral zero successor full empty rfl (fun _ => rfl) empty
      (fun impossible => nomatch impossible) first (mixedShape 7 3 2) slot target

theorem inventory_position_accepted : positions.related model empty firstData (ULift.up 5) (ULift.up 7) := by
  apply (inventory_positions_source_exact _ _).mpr
  obtain ⟨position, decoded, same⟩ := (reads_source_position 7 3 2 5 7).mp vector_slot
  exact ⟨position, decoded, congrArg (ULift.up : Nat → ULift.{1} Nat) same⟩

theorem inventory_position_refused : ¬ positions.related model empty firstData (ULift.up 5) (ULift.up 2) := by
  intro accepted
  obtain ⟨position, decoded, same⟩ := (inventory_positions_source_exact _ _).mp accepted
  exact wrong_child_refused ((reads_source_position 7 3 2 5 2).mpr ⟨position, decoded, congrArg ULift.down same⟩)

theorem inventory_image_exact (data : inventory.Data model) :
    inventory.dataAllowed model empty data ↔
      ∃ (index : interface.Index) (sourceShape : Code.Shape (codeAt reading codes data.1) PUnit.unit index),
        realization.encodeFields (codeAt reading codes data.1) sourceShape = fields_get reading codes data.1 ▸ data.2 :=
  images.inventory_allowed codes PUnit.unit Subst.id numeral empty (fun impossible => nomatch impossible) data

theorem inventory_forged_shape_refused :
    ¬ inventory.dataAllowed model empty ⟨first, mixedFields 7 3 2 9⟩ := by
  change ¬ CurriedPredicates.holds model (reading.fields mixedCode) (guards.compile mixedCode Subst.id) empty
    (mixedFields 7 3 2 9)
  exact forged_vector_shape_refused

theorem duplicate_descriptions_keep_occurrences :
    FiniteConstructorEncoding.encode (Ty.denote.{0,0} model.Carrier) inventory.fields firstData ≠
      FiniteConstructorEncoding.encode (Ty.denote.{0,0} model.Carrier) inventory.fields secondData := by
  intro same
  have dataSame := FiniteConstructorEncoding.encode_injective (Ty.denote.{0,0} model.Carrier) inventory.fields same
  have tags := congrArg (fun data => data.1.val) dataSame
  change (0 : Nat) = 1 at tags
  cases tags

theorem empty_inventory_refuses (payload : ClosedTerm Symbol (Mettapedia.Logic.HOL.FiniteConstructorEncoding.payloadType []))
    (target : ClosedTerm Symbol number) :
    ¬ (model.denote ((guards.constructors ([] : List (Code interface registry 0 [])) Subst.id numeral).resultGuard payload target) empty).down := by
  intro accepted
  obtain ⟨occurrence, _⟩ :=
    (images.resultGuard_exact ([] : List (Code interface registry 0 [])) PUnit.unit Subst.id numeral full empty
      (fun impossible => nomatch impossible) payload target).mp accepted
  exact Fin.elim0 occurrence

theorem field_injective : FieldInjective realization where
  value sort := by
    cases sort with
    | length => exact fun _ _ same => congrArg ULift.down same
    | payload =>
        intro first second same
        change Bool at first second
        cases first <;> cases second
        · rfl
        · have values : (0 : Nat) = 1 := congrArg ULift.down same
          cases values
        · have values : (1 : Nat) = 0 := congrArg ULift.down same
          cases values
        · rfl
  shape name entry registered output := by
    by_cases list : name = "List"
    · subst name
      have same : listEntry = entry := by simpa [registry] using registered
      subst entry
      exact fun _ _ same => congrArg ULift.down same
    · by_cases vector : name = "Vector"
      · subst name
        have same : vectorEntry = entry := by simpa [registry] using registered
        subst entry
        intro first second _
        cases first
        cases second
        rfl
      · simp [registry, list, vector] at registered

theorem nonempty_fields_identify : (2 : Nat) = 2 ∧ HEq (mixedShape 7 3 2) (mixedShape 7 3 2) :=
  field_injective.encodeFields_heq mixedCode (mixedShape 7 3 2) (mixedShape 7 3 2) rfl

theorem concrete_empty_index_refused :
    ¬ (CurriedPredicates.holds model (reading.fields boolCode) (guards.compile boolCode Subst.id) (boolValues 7) (boolFields 1) ∧
      CurriedPredicates.applyValues model (reading.fields boolCode)
        (model.denote (reading.resultProgram boolCode Subst.id) (boolValues 7)) (boolFields 1) = ULift.up 8) :=
  images.empty_index_refused (fun _ _ same => congrArg ULift.down same) boolCode
    ((7 : Nat), PUnit.unit) Subst.id (boolValues 7) (bool_represented 7) (boolFields 1) (8 : Nat) (wrong_index_empty 7)

theorem constructor_payload_injective :
    Function.Injective (fun point : ConstructorPoint reading codes PUnit.unit =>
      FiniteConstructorEncoding.encode (Ty.denote.{0,0} model.Carrier) (codes.map reading.fields)
        (encodeConstructorData realization codes point.1 point.2.2)) :=
  field_injective.constructorPayload_injective codes PUnit.unit

theorem carrier_image_exact
    (payload : Ty.denote.{0,0} model.Carrier (Mettapedia.Logic.HOL.FiniteConstructorEncoding.payloadType inventory.fields))
    (target : Ty.denote.{0,0} model.Carrier number) :
    (model.denote inventory.resultProgram empty payload target).down ↔
      ∃ (occurrence : Fin inventory.fields.length) (index : interface.Index)
        (sourceShape : Code.Shape (codeAt reading codes occurrence) PUnit.unit index),
        realization.index index = target ∧
        Mettapedia.Logic.HOL.FiniteConstructorEncoding.payloadEquivalence model inventory.fields payload =
          FiniteConstructorEncoding.encode (Ty.denote.{0,0} model.Carrier) inventory.fields
            (encodeConstructorData realization codes occurrence sourceShape) :=
  images.resultProgram_exact codes PUnit.unit Subst.id numeral full empty (fun impossible => nomatch impossible) payload target

def firstPayload : Ty.denote.{0,0} model.Carrier (Mettapedia.Logic.HOL.FiniteConstructorEncoding.payloadType inventory.fields) :=
  (Mettapedia.Logic.HOL.FiniteConstructorEncoding.payloadEquivalence model inventory.fields).symm
    (FiniteConstructorEncoding.encode (Ty.denote.{0,0} model.Carrier) inventory.fields firstData)

theorem carrier_source_accepted : (model.denote inventory.resultProgram empty firstPayload (ULift.up 2)).down := by
  apply (carrier_image_exact _ _).mpr
  exact ⟨first, (2 : Nat), mixedShape 7 3 2, rfl,
    (Mettapedia.Logic.HOL.FiniteConstructorEncoding.payloadEquivalence model inventory.fields).apply_symm_apply _⟩

theorem carrier_wrong_index_refused : ¬ (model.denote inventory.resultProgram empty firstPayload (ULift.up 3)).down := by
  intro accepted
  obtain ⟨data, ⟨_, result⟩, same⟩ := (inventory.resultProgram_denote model full empty firstPayload (ULift.up 3)).mp accepted
  have dataSame : data = firstData := FiniteConstructorEncoding.encode_injective
    (Ty.denote.{0,0} model.Carrier) inventory.fields
    (same.symm.trans ((Mettapedia.Logic.HOL.FiniteConstructorEncoding.payloadEquivalence model inventory.fields).apply_symm_apply _))
  rw [dataSame, inventory_result] at result
  have impossible : (2 : Nat) = 3 := congrArg ULift.down result
  cases impossible

theorem empty_carrier_refused
    (payload : Ty.denote.{0,0} model.Carrier (Mettapedia.Logic.HOL.FiniteConstructorEncoding.payloadType []))
    (target : Ty.denote.{0,0} model.Carrier number) :
    ¬ (model.denote (guards.constructors ([] : List (Code interface registry 0 [])) Subst.id numeral).resultProgram empty payload target).down := by
  intro accepted
  obtain ⟨occurrence, _⟩ :=
    (images.resultProgram_exact ([] : List (Code interface registry 0 [])) PUnit.unit Subst.id numeral full empty
      (fun impossible => nomatch impossible) payload target).mp accepted
  exact Fin.elim0 occurrence

#print axioms mixed_image_exact
#print axioms inventory_image_exact
#print axioms empty_inventory_refuses
#print axioms constructor_payload_injective
#print axioms carrier_image_exact

end Mettapedia.GSLT.LanguageDef.IndexedContainerFieldGuardControls
