import Mettapedia.GSLT.LanguageDef.NativeOpsTargetEval

/-!
# Protected private temporaries during operand evaluation

Compilation identities are ordinary natural names, not guest word values.
The relations below retain all source-visible local addresses and the exact
values of already-created private temporaries. Runtime memory and faults are
separate state components. Thus later argument evaluation may update aliased
locals while keeping its earlier by-value argument results.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

/-- All live private names lie in the compilation supply already consumed. -/
def TemporaryNamesBound (frame : TargetFrame) (bound : Nat) : Prop :=
  ∀ identity, frame.temporaryNames.contains identity = true → identity ≤ bound

/-- A private map contains no value outside its live lexical names. -/
def TemporariesScoped (frame : TargetFrame) : Prop :=
  ∀ identity, frame.temporaryNames.contains identity = false → frame.temporaries identity = none

structure TemporaryProtection (bound : Nat) (before after : TargetFrame) : Prop where
  storage : after.storage = before.storage
  nextLocal : after.nextLocal = before.nextLocal
  bindings : after.bindings = before.bindings
  names : ∀ identity, identity ≤ bound →
    after.temporaryNames.contains identity = before.temporaryNames.contains identity
  values : ∀ identity, identity ≤ bound → after.temporaries identity = before.temporaries identity

def atomWithin (bound : Nat) : NativeIR.Atom → Prop
  | .temporary identity _ | .iterationCounter identity => identity ≤ bound
  | .localAddress _ _ | .word _ | .zero _ | .unit => True

theorem atom_within_weaken {small large : Nat} (within : small ≤ large)
    (atom : NativeIR.Atom) (bounded : atomWithin small atom) : atomWithin large atom := by
  cases atom <;> simp only [atomWithin] at bounded ⊢
  · exact bounded.trans within
  · exact bounded.trans within

theorem temporary_names_bound_weaken {small large : Nat} {frame : TargetFrame}
    (within : small ≤ large) (bounded : TemporaryNamesBound frame small) :
    TemporaryNamesBound frame large := fun identity live => (bounded identity live).trans within

theorem temporary_protection_refl (bound : Nat) (frame : TargetFrame) :
    TemporaryProtection bound frame frame := ⟨rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩

theorem temporary_protection_trans {bound : Nat} {first middle last : TargetFrame}
    (left : TemporaryProtection bound first middle)
    (right : TemporaryProtection bound middle last) : TemporaryProtection bound first last :=
  ⟨right.storage.trans left.storage, right.nextLocal.trans left.nextLocal,
    right.bindings.trans left.bindings, fun identity within =>
      (right.names identity within).trans (left.names identity within),
    fun identity within => (right.values identity within).trans (left.values identity within)⟩

theorem temporary_protection_weaken {small large : Nat} {before after : TargetFrame}
    (within : small ≤ large) (protection : TemporaryProtection large before after) :
    TemporaryProtection small before after :=
  ⟨protection.storage, protection.nextLocal, protection.bindings,
    fun identity inside => protection.names identity (inside.trans within),
    fun identity inside => protection.values identity (inside.trans within)⟩

theorem temporary_protection_preserves_source_frame {bound : Nat}
    {source : SourceFrame} {before after : TargetFrame}
    (frames : FrameRelated source before) (protection : TemporaryProtection bound before after) :
    FrameRelated source after :=
  ⟨protection.storage.trans frames.storage, protection.nextLocal.trans frames.nextLocal,
    protection.bindings.trans frames.bindings⟩

theorem temporary_bound_fresh {frame : TargetFrame} {bound identity : Nat}
    (bounded : TemporaryNamesBound frame bound) (fresh : bound < identity) :
    frame.temporaryNames.contains identity = false := by
  cases found : frame.temporaryNames.contains identity with
  | false => rfl
  | true => exact False.elim ((Nat.not_le_of_lt fresh) (bounded identity found))

/-- A call cannot reuse a live result identity as a fresh result slot. This
is an actual instruction refusal, rather than a comparison of equal values. -/
theorem call_live_temporary_refused {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World) (result type : NativeType)
    (target : NativeIR.CallTarget) (arguments : List NativeIR.Atom)
    (frame : TargetFrame) (state : TargetState World) (identity : Nat) (held : TargetValue)
    (out : TargetBlockOutcome World) :
    ¬ TargetInstructionEval interface heap calls result
      (.call (some (.temporary identity type)) target arguments)
      (targetDeclareTemporary frame identity held) state out := by
  intro ran
  cases ran with
  | call _ _ stored =>
      cases stored with
      | fresh unused => simp [targetDeclareTemporary] at unused
      | existing notTemporary _ => exact (notTemporary identity type) rfl

theorem declare_temporary_protects {bound identity : Nat} (frame : TargetFrame)
    (value : TargetValue) (fresh : bound < identity) :
    TemporaryProtection bound frame (targetDeclareTemporary frame identity value) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · intro candidate within
    have different : candidate ≠ identity := fun same => by subst candidate; omega
    simp only [targetDeclareTemporary, List.contains_cons, beq_eq_false_iff_ne.mpr different,
      Bool.false_or]
  · intro candidate within
    have different : candidate ≠ identity := fun same => by subst candidate; omega
    simp only [targetDeclareTemporary, different, if_false]

theorem update_temporary_protects {bound identity : Nat} (frame : TargetFrame)
    (value : TargetValue) (fresh : bound < identity) :
    TemporaryProtection bound frame (targetUpdateTemporary frame identity value) := by
  refine ⟨rfl, rfl, rfl, fun _ _ => rfl, ?_⟩
  intro candidate within
  have different : candidate ≠ identity := fun same => by subst candidate; omega
  simp only [targetUpdateTemporary, different, if_false]

theorem declared_temporary_bound {frame : TargetFrame} {before after identity : Nat}
    (bounded : TemporaryNamesBound frame before) (extended : before ≤ after)
    (within : identity ≤ after) (value : TargetValue) :
    TemporaryNamesBound (targetDeclareTemporary frame identity value) after := by
  intro candidate live
  simp only [targetDeclareTemporary, List.contains_cons, Bool.or_eq_true] at live
  rcases live with same | old
  · have equal : candidate = identity := eq_of_beq same
    subst candidate; exact within
  · exact (bounded candidate old).trans extended

theorem updated_temporary_bound {frame : TargetFrame} {bound identity : Nat}
    (bounded : TemporaryNamesBound frame bound) (value : TargetValue) :
    TemporaryNamesBound (targetUpdateTemporary frame identity value) bound := bounded

theorem declared_temporaries_completeNames {frame : TargetFrame}
    (completeNames : TemporariesScoped frame) (identity : Nat) (value : TargetValue) :
    TemporariesScoped (targetDeclareTemporary frame identity value) :=
  declare_temporary_scoped frame identity value completeNames

/-- A fresh result preserves every older temporary and keeps the new frame
within its declared name bound. This profile does not constrain runtime effects. -/
theorem declared_temporary_frame_profile {frame : TargetFrame} {lower upper identity : Nat}
    (bounded : TemporaryNamesBound frame lower) (hscope : TemporariesScoped frame)
    (fresh : lower < identity) (within : identity ≤ upper) (value : TargetValue) :
    TemporaryProtection lower frame (targetDeclareTemporary frame identity value) ∧
    TemporaryNamesBound (targetDeclareTemporary frame identity value) upper ∧
    TemporariesScoped (targetDeclareTemporary frame identity value) :=
  ⟨declare_temporary_protects frame value fresh,
    declared_temporary_bound bounded (fresh.le.trans within) within value,
    declared_temporaries_completeNames hscope identity value⟩

theorem temporary_protection_local_address {bound : Nat} {before after : TargetFrame}
    (protection : TemporaryProtection bound before after) (name : String) :
    targetLocalAddress after name = targetLocalAddress before name := by
  simp only [targetLocalAddress, protection.bindings, protection.storage]

theorem protection_atom_evaluation {World : Type} {interface : Interface}
    {bound : Nat} {before after : TargetFrame}
    (protection : TemporaryProtection bound before after) (atom : NativeIR.Atom)
    (within : atomWithin bound atom) (initial final : TargetState World) (value : TargetValue) :
    TargetAtomEval interface before initial atom value ↔
      TargetAtomEval interface after final atom value := by
  constructor
  · intro read
    cases read with
    | temporary found live =>
        exact .temporary ((protection.values _ within).trans found)
          ((protection.names _ within).trans live)
    | iterationCounter found live =>
        exact .iterationCounter ((protection.values _ within).trans found)
          ((protection.names _ within).trans live)
    | localAddress found =>
        exact .localAddress ((temporary_protection_local_address protection _).trans found)
    | word value => exact .word value
    | zero initialized => exact .zero initialized
    | unit => exact .unit
  · intro read
    cases read with
    | temporary found live =>
        exact .temporary ((protection.values _ within).symm.trans found)
          ((protection.names _ within).symm.trans live)
    | iterationCounter found live =>
        exact .iterationCounter ((protection.values _ within).symm.trans found)
          ((protection.names _ within).symm.trans live)
    | localAddress found =>
        exact .localAddress ((temporary_protection_local_address protection _).symm.trans found)
    | word value => exact .word value
    | zero initialized => exact .zero initialized
    | unit => exact .unit

theorem protection_atoms_evaluation {World : Type} {interface : Interface}
    {bound : Nat} {before after : TargetFrame}
    (protection : TemporaryProtection bound before after) (atoms : List NativeIR.Atom)
    (within : ∀ atom ∈ atoms, atomWithin bound atom)
    (initial final : TargetState World) (values : List TargetValue) :
    TargetAtomsEval interface before initial atoms values ↔
      TargetAtomsEval interface after final atoms values := by
  induction atoms generalizing values with
  | nil => constructor <;> intro read <;> cases read <;> exact .nil
  | cons head rest ih =>
      constructor
      · intro read
        cases read with
        | cons first tail =>
            exact .cons ((protection_atom_evaluation protection head (within head (by simp)) _ _ _).mp first)
              ((ih (fun atom member => within atom (by simp [member])) _).mp tail)
      · intro read
        cases read with
        | cons first tail =>
            exact .cons ((protection_atom_evaluation protection head (within head (by simp)) _ _ _).mpr first)
              ((ih (fun atom member => within atom (by simp [member])) _).mpr tail)

theorem target_pure_temporary_any_exact {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World) (result : NativeType)
    (root : List NativeIR.Instruction) (frame : TargetFrame) (state : TargetState World)
    (identity : Nat) (type : NativeType) (operation : NativeIR.PureOperation)
    (unused : frame.temporaryNames.contains identity = false) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result root [.temporary identity type operation] frame state out ↔
      ∃ value, TargetPureEval interface frame state operation value ∧
        out = ⟨.normal, targetDeclareTemporary frame identity value, state⟩ := by
  constructor
  · intro ran
    cases ran with
    | next first rest =>
        cases first with
        | temporary _ computed =>
            cases rest
            exact ⟨_, computed, rfl⟩
    | «return» first | resume first _ _ | escape first _ => cases first
  · rintro ⟨value, computed, same⟩
    subst out
    exact .next (.temporary unused computed) (.nil _ _ _)

theorem updated_temporary_atom {World : Type} (interface : Interface) (frame : TargetFrame)
    (state : TargetState World) (identity : Nat) (type : NativeType) (value : TargetValue)
    (live : frame.temporaryNames.contains identity = true) :
    TargetAtomEval interface (targetUpdateTemporary frame identity value) state
      (.temporary identity type) value :=
  .temporary (by simp only [targetUpdateTemporary, if_true]) live

theorem target_update_temporary_scoped {frame : TargetFrame} (hscope : TemporariesScoped frame)
    {identity : Nat} (live : frame.temporaryNames.contains identity = true) (value : TargetValue) :
    TemporariesScoped (targetUpdateTemporary frame identity value) := by
  intro candidate absent
  change frame.temporaryNames.contains candidate = false at absent
  have different : candidate ≠ identity := by
    intro same
    subst candidate
    rw [live] at absent
    cases absent
  simp only [targetUpdateTemporary, different, if_false]
  exact hscope candidate absent

/-- Updating a live newer descriptor preserves older private operands and
keeps the exact live-name inventory. Runtime memory is a separate state. -/
theorem updated_temporary_frame_profile {frame : TargetFrame} {lower upper identity : Nat}
    (bounded : TemporaryNamesBound frame upper) (hscope : TemporariesScoped frame)
    (live : frame.temporaryNames.contains identity = true) (newer : lower < identity)
    (value : TargetValue) :
    TemporaryProtection lower frame (targetUpdateTemporary frame identity value) ∧
    TemporaryNamesBound (targetUpdateTemporary frame identity value) upper ∧
    TemporariesScoped (targetUpdateTemporary frame identity value) :=
  ⟨update_temporary_protects frame value newer, updated_temporary_bound bounded value,
    target_update_temporary_scoped hscope live value⟩


theorem target_atom_read_within {World : Type} {interface : Interface}
    {frame : TargetFrame} {state : TargetState World} {bound : Nat}
    (bounded : TemporaryNamesBound frame bound) {atom : NativeIR.Atom} {value : TargetValue}
    (read : TargetAtomEval interface frame state atom value) : atomWithin bound atom := by
  cases read with
  | temporary _ live => exact bounded _ live
  | iterationCounter _ live => exact bounded _ live
  | localAddress _ => trivial
  | word _ => trivial
  | zero _ => trivial
  | unit => trivial

end Mettapedia.GSLT.LanguageDef.NativeOps
