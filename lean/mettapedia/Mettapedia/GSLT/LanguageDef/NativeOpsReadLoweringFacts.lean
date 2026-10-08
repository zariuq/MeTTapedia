import Mettapedia.GSLT.LanguageDef.NativeOpsReadFragments
import Mettapedia.GSLT.LanguageDef.NativeOpsScalarProfiles

/-!
# Actual read lowering and declared field types

Each decomposition retains the successful existing lowerer, its exact
operand order, guards and private result. Declared field lists supply result
tags; a nominal record tag alone does not. These facts grant neither missing
cell contents nor arbitrary allocator or call behavior.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

open NativeIR (Atom)
open NativeLowering (Expression)

theorem read_load_lowering_exact {interface : Interface} {scope : Scope}
    {reference : Expr} {supply : NativeIR.Supply} {output : Expression}
    (compiled : NativeLowering.expression? interface scope (.load reference) supply = some output) :
    ∃ type location, inferExpr interface scope (.load reference) = some type ∧
      NativeLowering.location? interface scope (.load reference) supply = some location ∧
      output = NativeLowering.prependCode location.code
        (NativeLowering.pureTemporary location.supply type (.indirectRead location.result)) := by
  rw [NativeLowering.expression?] at compiled
  obtain ⟨type, inferred, compiled⟩ := Option.bind_eq_some_iff.mp compiled
  obtain ⟨location, located, compiled⟩ := Option.bind_eq_some_iff.mp compiled
  exact ⟨type, location, inferred, located, (Option.some.inj compiled).symm⟩

theorem read_index_lowering_exact {interface : Interface} {scope : Scope}
    {array index : Expr} {supply : NativeIR.Supply} {output : Expression}
    (compiled : NativeLowering.expression? interface scope (.index array index) supply = some output) :
    ∃ type location, inferExpr interface scope (.index array index) = some type ∧
      NativeLowering.location? interface scope (.index array index) supply = some location ∧
      output = NativeLowering.prependCode location.code
        (NativeLowering.pureTemporary location.supply type (.indirectRead location.result)) := by
  rw [NativeLowering.expression?] at compiled
  obtain ⟨type, inferred, compiled⟩ := Option.bind_eq_some_iff.mp compiled
  obtain ⟨location, located, compiled⟩ := Option.bind_eq_some_iff.mp compiled
  exact ⟨type, location, inferred, located, (Option.some.inj compiled).symm⟩

theorem read_address_lowering_exact {interface : Interface} {scope : Scope}
    {location : Expr} {supply : NativeIR.Supply} {output : Expression}
    (compiled : NativeLowering.expression? interface scope (.address location) supply = some output) :
    ∃ type located, inferExpr interface scope (.address location) = some type ∧
      NativeLowering.location? interface scope location supply = some located ∧
      output = NativeLowering.prependCode located.code
        (NativeLowering.pureTemporary located.supply type (.copy located.result)) := by
  rw [NativeLowering.expression?] at compiled
  obtain ⟨type, inferred, compiled⟩ := Option.bind_eq_some_iff.mp compiled
  obtain ⟨located, locatedCompiled, compiled⟩ := Option.bind_eq_some_iff.mp compiled
  exact ⟨type, located, inferred, locatedCompiled, (Option.some.inj compiled).symm⟩

theorem read_length_lowering_exact {interface : Interface} {scope : Scope}
    {array : Expr} {supply : NativeIR.Supply} {output : Expression}
    (compiled : NativeLowering.expression? interface scope (.length array) supply = some output) :
    ∃ type child, inferExpr interface scope (.length array) = some type ∧
      NativeLowering.expression? interface scope array supply = some child ∧
      output = NativeLowering.prependCode child.code
        (NativeLowering.pureTemporary child.supply type (.length child.result)) := by
  rw [NativeLowering.expression?] at compiled
  obtain ⟨type, inferred, compiled⟩ := Option.bind_eq_some_iff.mp compiled
  obtain ⟨child, childCompiled, compiled⟩ := Option.bind_eq_some_iff.mp compiled
  exact ⟨type, child, inferred, childCompiled, (Option.some.inj compiled).symm⟩

theorem read_value_field_lowering_exact {interface : Interface} {scope : Scope}
    {base : Expr} {member record : String} {supply : NativeIR.Supply} {output : Expression}
    (baseTyping : inferExpr interface scope base = some (.named record))
    (compiled : NativeLowering.expression? interface scope (.field base member) supply = some output) :
    ∃ type child index, inferExpr interface scope (.field base member) = some type ∧
      NativeLowering.expression? interface scope base supply = some child ∧
      NativeLowering.fieldLayout? interface record member = some index ∧
      output = NativeLowering.prependCode child.code
        (NativeLowering.pureTemporary child.supply type (.fieldValue child.result record index)) := by
  rw [NativeLowering.expression?] at compiled
  obtain ⟨type, inferred, compiled⟩ := Option.bind_eq_some_iff.mp compiled
  obtain ⟨baseType, baseInferred, compiled⟩ := Option.bind_eq_some_iff.mp compiled
  cases Option.some.inj (baseTyping.symm.trans baseInferred)
  obtain ⟨child, childCompiled, compiled⟩ := Option.bind_eq_some_iff.mp compiled
  obtain ⟨index, layout, compiled⟩ := Option.bind_eq_some_iff.mp compiled
  exact ⟨type, child, index, inferred, childCompiled, layout, (Option.some.inj compiled).symm⟩

theorem read_reference_field_lowering_exact {interface : Interface} {scope : Scope}
    {base : Expr} {member record : String} {supply : NativeIR.Supply} {output : Expression}
    (baseTyping : inferExpr interface scope base = some (.ref (.named record)))
    (compiled : NativeLowering.expression? interface scope (.field base member) supply = some output) :
    ∃ type location, inferExpr interface scope (.field base member) = some type ∧
      NativeLowering.location? interface scope (.field base member) supply = some location ∧
      output = NativeLowering.prependCode location.code
        (NativeLowering.pureTemporary location.supply type (.indirectRead location.result)) := by
  rw [NativeLowering.expression?] at compiled
  obtain ⟨type, inferred, compiled⟩ := Option.bind_eq_some_iff.mp compiled
  obtain ⟨baseType, baseInferred, compiled⟩ := Option.bind_eq_some_iff.mp compiled
  cases Option.some.inj (baseTyping.symm.trans baseInferred)
  obtain ⟨location, located, compiled⟩ := Option.bind_eq_some_iff.mp compiled
  exact ⟨type, location, inferred, located, (Option.some.inj compiled).symm⟩

theorem read_load_location_lowering_exact {interface : Interface} {scope : Scope}
    {reference : Expr} {supply : NativeIR.Supply} {output : Expression}
    (compiled : NativeLowering.location? interface scope (.load reference) supply = some output) :
    ∃ type child, inferLocation interface scope (.load reference) = some type ∧
      NativeLowering.expression? interface scope reference supply = some child ∧
      output = ⟨child.code ++ NativeLowering.checkReference child.result, child.result, child.supply⟩ := by
  rw [NativeLowering.location?] at compiled
  obtain ⟨type, inferred, compiled⟩ := Option.bind_eq_some_iff.mp compiled
  obtain ⟨child, childCompiled, compiled⟩ := Option.bind_eq_some_iff.mp compiled
  exact ⟨type, child, inferred, childCompiled, (Option.some.inj compiled).symm⟩

theorem read_load_combined_lowering_exact {interface : Interface} {scope : Scope}
    {reference : Expr} {supply : NativeIR.Supply} {output : Expression}
    (compiled : NativeLowering.expression? interface scope (.load reference) supply = some output) :
    ∃ type child, inferExpr interface scope (.load reference) = some type ∧
      NativeLowering.expression? interface scope reference supply = some child ∧
      output = NativeLowering.prependCode (child.code ++ NativeLowering.checkReference child.result)
        (NativeLowering.pureTemporary child.supply type (.indirectRead child.result)) := by
  obtain ⟨type, location, typing, located, same⟩ := read_load_lowering_exact compiled
  obtain ⟨_, child, _, childCompiled, exactLocation⟩ := read_load_location_lowering_exact located
  subst location
  exact ⟨type, child, typing, childCompiled, same⟩

theorem read_index_location_lowering_exact {interface : Interface} {scope : Scope}
    {array index : Expr} {supply : NativeIR.Supply} {output : Expression}
    (compiled : NativeLowering.location? interface scope (.index array index) supply = some output) :
    ∃ type first second, inferLocation interface scope (.index array index) = some type ∧
      NativeLowering.expression? interface scope array supply = some first ∧
      NativeLowering.expression? interface scope index first.supply = some second ∧
      output = ⟨first.code ++ second.code ++
        [.helper (some (.temporary (NativeIR.fresh second.supply).1 (.ref type)))
          (.index first.result second.result type), .checkContext],
        .temporary (NativeIR.fresh second.supply).1 (.ref type), (NativeIR.fresh second.supply).2⟩ := by
  rw [NativeLowering.location?] at compiled
  obtain ⟨type, inferred, compiled⟩ := Option.bind_eq_some_iff.mp compiled
  obtain ⟨first, firstCompiled, compiled⟩ := Option.bind_eq_some_iff.mp compiled
  obtain ⟨second, secondCompiled, compiled⟩ := Option.bind_eq_some_iff.mp compiled
  exact ⟨type, first, second, inferred, firstCompiled, secondCompiled, (Option.some.inj compiled).symm⟩

theorem read_reference_field_location_lowering_exact {interface : Interface} {scope : Scope}
    {base : Expr} {member record : String} {supply : NativeIR.Supply} {output : Expression}
    (baseTyping : inferExpr interface scope base = some (.ref (.named record)))
    (compiled : NativeLowering.location? interface scope (.field base member) supply = some output) :
    ∃ type child index, inferLocation interface scope (.field base member) = some type ∧
      NativeLowering.expression? interface scope base supply = some child ∧
      NativeLowering.fieldLayout? interface record member = some index ∧
      output = NativeLowering.prependCode (child.code ++ NativeLowering.checkReference child.result)
        (NativeLowering.pureTemporary child.supply (.ref type) (.fieldAddress child.result record index)) := by
  rw [NativeLowering.location?] at compiled
  obtain ⟨type, inferred, compiled⟩ := Option.bind_eq_some_iff.mp compiled
  obtain ⟨baseType, baseInferred, compiled⟩ := Option.bind_eq_some_iff.mp compiled
  cases Option.some.inj (baseTyping.symm.trans baseInferred)
  obtain ⟨child, childCompiled, compiled⟩ := Option.bind_eq_some_iff.mp compiled
  obtain ⟨index, layout, compiled⟩ := Option.bind_eq_some_iff.mp compiled
  exact ⟨type, child, index, inferred, childCompiled, layout, (Option.some.inj compiled).symm⟩

theorem read_value_field_location_lowering_exact {interface : Interface} {scope : Scope}
    {base : Expr} {member record : String} {supply : NativeIR.Supply} {output : Expression}
    (baseTyping : inferExpr interface scope base = some (.named record))
    (compiled : NativeLowering.location? interface scope (.field base member) supply = some output) :
    ∃ type child index, inferLocation interface scope (.field base member) = some type ∧
      NativeLowering.location? interface scope base supply = some child ∧
      NativeLowering.fieldLayout? interface record member = some index ∧
      output = NativeLowering.prependCode child.code
        (NativeLowering.pureTemporary child.supply (.ref type) (.fieldAddress child.result record index)) := by
  rw [NativeLowering.location?] at compiled
  obtain ⟨type, inferred, compiled⟩ := Option.bind_eq_some_iff.mp compiled
  obtain ⟨baseType, baseInferred, compiled⟩ := Option.bind_eq_some_iff.mp compiled
  cases Option.some.inj (baseTyping.symm.trans baseInferred)
  obtain ⟨child, childCompiled, compiled⟩ := Option.bind_eq_some_iff.mp compiled
  obtain ⟨index, layout, compiled⟩ := Option.bind_eq_some_iff.mp compiled
  exact ⟨type, child, index, inferred, childCompiled, layout, (Option.some.inj compiled).symm⟩

theorem read_length_inferred {interface : Interface} {scope : Scope} {array : Expr} {type : NativeType}
    (inferred : inferExpr interface scope (.length array) = some type) :
    type = .word ∧ ∃ element, inferExpr interface scope array = some (.array element) := by
  rw [inferExpr] at inferred
  obtain ⟨input, child, inferred⟩ := Option.bind_eq_some_iff.mp inferred
  cases input <;> simp only [reduceCtorEq] at inferred
  case array element => cases inferred; exact ⟨rfl, element, child⟩

theorem read_load_inferred {interface : Interface} {scope : Scope} {reference : Expr} {type : NativeType}
    (inferred : inferExpr interface scope (.load reference) = some type) :
    inferExpr interface scope reference = some (.ref type) := by
  rw [inferExpr] at inferred
  obtain ⟨input, child, inferred⟩ := Option.bind_eq_some_iff.mp inferred
  cases input <;> simp only [reduceCtorEq] at inferred
  case ref element =>
    split at inferred
    · cases inferred; exact child
    · cases inferred

/-- Declared record fields carry their actual member types in order. -/
def SourceDeclaredFields (fields : List Parameter) (values : List SourceValue) : Prop :=
  List.Forall₂ (fun field value => SourceOuterTag field.type value) fields values

def TargetDeclaredFields (fields : List Parameter) (values : List TargetValue) : Prop :=
  List.Forall₂ (fun field value => TargetOuterTag field.type value) fields values

theorem declared_fields_preservation {fields : List Parameter} {values : List SourceValue}
    (tagged : SourceDeclaredFields fields values) : TargetDeclaredFields fields (encodeValues values) := by
  induction tagged with
  | nil => exact .nil
  | cons head tail ih => exact .cons (outer_tag_preservation head) ih

theorem declared_fields_length {fields : List Parameter} {values : List SourceValue}
    (tagged : SourceDeclaredFields fields values) : fields.length = values.length :=
  List.Forall₂.length_eq tagged

theorem declared_field_selected_tag {fields : List Parameter} {values : List SourceValue}
    (tagged : SourceDeclaredFields fields values) (index : Nat) (field : Parameter) (value : SourceValue)
    (member : fields[index]? = some field) (selected : values[index]? = some value) :
    SourceOuterTag field.type value := by
  induction tagged generalizing index with
  | nil => cases member
  | cons head tail ih =>
      cases index with
      | zero => cases member; cases selected; exact head
      | succ index => exact ih index member selected

theorem source_zero_fields_declared {interface : Interface} {fields : List Parameter} {values : List SourceValue}
    (zero : SourceZeroFields interface fields values) : SourceDeclaredFields fields values := by
  cases zero with
  | nil => exact .nil
  | cons head tail => exact .cons (source_zero_outer_tag head) (source_zero_fields_declared tail)
termination_by fields.length
decreasing_by simp_wf

theorem declared_fields_store {fields : List Parameter} {values : List SourceValue}
    (tagged : SourceDeclaredFields fields values) (index : Nat) (field : Parameter) (value : SourceValue)
    (member : fields[index]? = some field) (replacement : SourceOuterTag field.type value) :
    SourceDeclaredFields fields (values.set index value) := by
  induction tagged generalizing index with
  | nil => cases member
  | cons head tail ih =>
      cases index with
      | zero => cases member; exact .cons replacement tail
      | succ index => exact .cons head (ih index member)

theorem declared_record_field_write {fields : List Parameter} {values : List SourceValue}
    (tagged : SourceDeclaredFields fields values) (name : String) (index : Nat)
    (field : Parameter) (value updated : SourceValue)
    (member : fields[index]? = some field) (replacement : SourceOuterTag field.type value)
    (written : sourceWritePath [index] value (.record name values) = some updated) :
    updated = .record name (values.set index value) ∧
      SourceDeclaredFields fields (values.set index value) := by
  change (values[index]?).bind (fun _ => some (.record name (values.set index value))) = some updated at written
  obtain ⟨_, _, same⟩ := Option.bind_eq_some_iff.mp written
  exact ⟨(Option.some.inj same).symm, declared_fields_store tagged index field value member replacement⟩

theorem source_zero_record_fields_declared {interface : Interface} {name : String}
    {declaration : Record} {values : List SourceValue}
    (layout : lookupRecord interface name = some declaration)
    (zero : SourceZero interface (.named name) (.record name values)) :
    SourceDeclaredFields declaration.fields values := by
  cases zero with
  | record found fields =>
      cases Option.some.inj (layout.symm.trans found)
      exact source_zero_fields_declared fields

theorem field_position_selected {fields : List Parameter} {member : String} {index : Nat}
    (selected : NativeLowering.fieldPosition? fields member = some index) :
    ∃ field, fields[index]? = some field ∧
      fields.find? (fun candidate => candidate.name == member) = some field := by
  induction fields generalizing index with
  | nil => cases selected
  | cons field rest ih =>
      unfold NativeLowering.fieldPosition? at selected
      by_cases same : field.name == member
      · simp only [same, if_true] at selected
        cases selected
        exact ⟨field, rfl, by simp only [List.find?_cons, same]⟩
      · simp only [same, Bool.false_eq_true, if_false] at selected
        obtain ⟨offset, tail, exactIndex⟩ := Option.map_eq_some_iff.mp selected
        subst index
        obtain ⟨chosen, read, found⟩ := ih tail
        exact ⟨chosen, read, by simp only [List.find?_cons, same, found]⟩

theorem declared_record_field_tag {interface : Interface} {name member : String}
    {declaration : Record} {values : List SourceValue} {index : Nat} {type : NativeType} {value : SourceValue}
    (layout : lookupRecord interface name = some declaration)
    (tagged : SourceDeclaredFields declaration.fields values)
    (position : NativeLowering.fieldLayout? interface name member = some index)
    (typing : lookupField interface name member = some type)
    (selected : values[index]? = some value) : SourceOuterTag type value := by
  have fieldPosition : NativeLowering.fieldPosition? declaration.fields member = some index := by
    unfold NativeLowering.fieldLayout? at position
    rw [layout] at position
    exact position
  obtain ⟨field, memberAt, found⟩ := field_position_selected fieldPosition
  have fieldType : field.type = type := by
    unfold lookupField at typing
    rw [layout] at typing
    change (declaration.fields.find? (fun candidate => candidate.name == member)).bind
      (fun chosen => some chosen.type) = some type at typing
    rw [found] at typing
    exact Option.some.inj typing
  rw [← fieldType]
  exact declared_field_selected_tag tagged index field value memberAt selected

theorem target_atom_state_irrelevant {World : Type} {interface : Interface} {frame : TargetFrame}
    {before : TargetState World} {atom : Atom} {value : TargetValue}
    (read : TargetAtomEval interface frame before atom value) (after : TargetState World) :
    TargetAtomEval interface frame after atom value := by
  cases read with
  | temporary found live => exact .temporary found live
  | iterationCounter found live => exact .iterationCounter found live
  | localAddress found => exact .localAddress found
  | word value => exact .word value
  | zero initialized => exact .zero initialized
  | unit => exact .unit

theorem read_index_inferred {interface : Interface} {scope : Scope}
    {array index : Expr} {type : NativeType}
    (inferred : inferExpr interface scope (.index array index) = some type) :
    inferExpr interface scope array = some (.array type) ∧
      inferExpr interface scope index = some .word := by
  rw [inferExpr] at inferred
  obtain ⟨arrayType, arrayTyped, inferred⟩ := Option.bind_eq_some_iff.mp inferred
  obtain ⟨indexType, indexTyped, inferred⟩ := Option.bind_eq_some_iff.mp inferred
  cases arrayType <;> simp only [reduceCtorEq] at inferred
  case array element =>
    split at inferred
    · rename_i same
      subst indexType
      cases inferred
      exact ⟨arrayTyped, indexTyped⟩
    · cases inferred

theorem read_index_combined_lowering_exact {interface : Interface} {scope : Scope}
    {array index : Expr} {supply : NativeIR.Supply} {output : NativeLowering.Expression}
    (compiled : NativeLowering.expression? interface scope (.index array index) supply = some output) :
    ∃ type first second, inferExpr interface scope (.index array index) = some type ∧
      NativeLowering.expression? interface scope array supply = some first ∧
      NativeLowering.expression? interface scope index first.supply = some second ∧
      output = NativeLowering.prependCode (first.code ++ second.code)
        ⟨[.helper (some (.temporary (NativeIR.fresh second.supply).1 (.ref type)))
            (.index first.result second.result type), .checkContext] ++
            (NativeLowering.pureTemporary (NativeIR.fresh second.supply).2 type
              (.indirectRead (.temporary (NativeIR.fresh second.supply).1 (.ref type)))).code,
          (NativeLowering.pureTemporary (NativeIR.fresh second.supply).2 type
              (.indirectRead (.temporary (NativeIR.fresh second.supply).1 (.ref type)))).result,
          (NativeIR.fresh (NativeIR.fresh second.supply).2).2⟩ := by
  obtain ⟨type, location, typing, located, same⟩ := read_index_lowering_exact compiled
  obtain ⟨locationType, first, second, locationTyping, firstCompiled, secondCompiled, exactLocation⟩ :=
    read_index_location_lowering_exact located
  simp only [inferLocation] at locationTyping
  cases Option.some.inj (typing.symm.trans locationTyping)
  subst location
  exact ⟨type, first, second, typing, firstCompiled, secondCompiled,
    by simpa only [NativeLowering.prependCode, NativeLowering.pureTemporary, List.append_assoc] using same⟩


theorem read_slice_inferred {interface : Interface} {scope : Scope}
    {array start count : Expr} {element : NativeType}
    (inferred : inferExpr interface scope (.slice array start count) = some (.array element)) :
    inferExpr interface scope array = some (.array element) ∧
      inferExpr interface scope start = some .word ∧ inferExpr interface scope count = some .word := by
  rw [inferExpr] at inferred
  obtain ⟨arrayType, arrayTyped, inferred⟩ := Option.bind_eq_some_iff.mp inferred
  obtain ⟨startType, startTyped, inferred⟩ := Option.bind_eq_some_iff.mp inferred
  obtain ⟨countType, countTyped, inferred⟩ := Option.bind_eq_some_iff.mp inferred
  cases arrayType <;> simp only [reduceCtorEq] at inferred
  case array actualElement =>
    split at inferred
    · rename_i same
      obtain ⟨rfl, rfl⟩ := same
      cases inferred
      exact ⟨arrayTyped, startTyped, countTyped⟩
    · cases inferred

theorem read_slice_combined_lowering_exact {interface : Interface} {scope : Scope}
    {array start count : Expr} {supply : NativeIR.Supply} {output : NativeLowering.Expression}
    (compiled : NativeLowering.expression? interface scope (.slice array start count) supply = some output) :
    ∃ element first second third,
      inferExpr interface scope (.slice array start count) = some (.array element) ∧
      NativeLowering.expression? interface scope array supply = some first ∧
      NativeLowering.expression? interface scope start first.supply = some second ∧
      NativeLowering.expression? interface scope count second.supply = some third ∧
      output = NativeLowering.prependCode (first.code ++ second.code ++ third.code)
        ⟨(NativeLowering.pureTemporary third.supply (.array element) (.zero (.array element))).code ++
          [.helper (some (.arrayData
              (NativeLowering.pureTemporary third.supply (.array element) (.zero (.array element))).result element))
              (.slice first.result second.result third.result element),
            .checkContext, .assign (.arrayLength
              (NativeLowering.pureTemporary third.supply (.array element) (.zero (.array element))).result) third.result],
          (NativeLowering.pureTemporary third.supply (.array element) (.zero (.array element))).result,
          (NativeLowering.pureTemporary third.supply (.array element) (.zero (.array element))).supply⟩ := by
  rw [NativeLowering.expression?] at compiled
  obtain ⟨type, typing, afterTyping⟩ := Option.bind_eq_some_iff.mp compiled
  clear compiled
  obtain ⟨first, firstCompiled, afterFirst⟩ := Option.bind_eq_some_iff.mp afterTyping
  clear afterTyping
  obtain ⟨second, secondCompiled, afterSecond⟩ := Option.bind_eq_some_iff.mp afterFirst
  clear afterFirst
  obtain ⟨third, thirdCompiled, compiled⟩ := Option.bind_eq_some_iff.mp afterSecond
  clear afterSecond
  cases type <;> simp only [reduceCtorEq] at compiled
  case array element =>
    exact ⟨element, first, second, third, typing, firstCompiled, secondCompiled, thirdCompiled,
      by simpa only [NativeLowering.prependCode, List.append_assoc] using (Option.some.inj compiled).symm⟩

end Mettapedia.GSLT.LanguageDef.NativeOps
