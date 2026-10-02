import Mettapedia.GSLT.LanguageDef.NativeOpsSourceEval
import Mettapedia.GSLT.LanguageDef.NativeOpsLowering
import Mettapedia.GSLT.LanguageDef.NativeOpsValueDeterminism

/-!
# Declared field positions and independent record reads

The source reader looks up a member in its declared record. The lowering
reader separately chooses the emitted positional access. These laws compare
the two traversals and the actual target value projection, without treating
reference non-nullness as proof of a live dereference.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

theorem member_position_correspondence (fields : List Parameter) (name : String) :
    NativeLowering.fieldPosition? fields name = sourceMemberIndex? fields name := by
  induction fields with
  | nil => rfl
  | cons field rest ih =>
      change (if decide (field.name = name) then some 0 else
        (NativeLowering.fieldPosition? rest name).map (· + 1)) =
        (if field.name = name then some 0 else (sourceMemberIndex? rest name).map Nat.succ)
      by_cases same : field.name = name
      · simp only [same, decide_true, if_true]
      · simp only [same, decide_false, Bool.false_eq_true, if_false, ih]

theorem field_layout_correspondence (interface : Interface) (record name : String) :
    NativeLowering.fieldLayout? interface record name = sourceFieldIndex? interface record name := by
  unfold NativeLowering.fieldLayout? sourceFieldIndex?
  cases allocated : lookupRecord interface record with
  | none => rfl
  | some declaration => exact member_position_correspondence declaration.fields name

theorem source_record_field_exact {World : Type} (interface : Interface)
    (heap : SourceHeapSemantics World) (calls : SourceCalls World) (frame : SourceFrame)
    (base : Expr) (record member : String) (fields : List SourceValue) (index : Nat)
    (position : NativeLowering.fieldLayout? interface record member = some index)
    (state : SourceState World) (out : SourceOutcome World) :
    sourcePrimitive interface heap calls frame (.field base member)
      [.record record fields] state out ↔
      ∃ value, fields[index]? = some value ∧ out = ⟨.ok value, state⟩ := by
  have sourcePosition := (field_layout_correspondence interface record member).symm.trans position
  change (∃ actual value, sourceFieldIndex? interface record member = some actual ∧
    fields[actual]? = some value ∧ out = ⟨.ok value, state⟩) ↔ _
  constructor
  · rintro ⟨actual, value, selected, read, observed⟩
    have same := Option.some.inj (sourcePosition.symm.trans selected)
    subst actual
    exact ⟨value, read, observed⟩
  · rintro ⟨value, read, observed⟩
    exact ⟨index, value, sourcePosition, read, observed⟩

theorem target_record_field_exact {World : Type} (interface : Interface)
    (frame : TargetFrame) (state : TargetState World) (atom : NativeIR.Atom)
    (record : String) (fields : List SourceValue) (index : Nat)
    (read : TargetAtomEval interface frame state atom (.record record (encodeValues fields)))
    (value : TargetValue) :
    TargetPureEval interface frame state (.fieldValue atom record index) value ↔
      ∃ source, fields[index]? = some source ∧ value = encodeValue source := by
  constructor
  · intro evaluated
    cases evaluated with
    | fieldValue otherRead selected =>
        have same := target_atom_unique read otherRead
        cases same
        rw [encodeValues_getElem?] at selected
        rcases Option.map_eq_some_iff.mp selected with ⟨source, sourceRead, encoded⟩
        exact ⟨source, sourceRead, encoded.symm⟩
  · rintro ⟨source, selected, same⟩
    subst value
    apply TargetPureEval.fieldValue read
    rw [encodeValues_getElem?, selected]
    rfl

end Mettapedia.GSLT.LanguageDef.NativeOps
