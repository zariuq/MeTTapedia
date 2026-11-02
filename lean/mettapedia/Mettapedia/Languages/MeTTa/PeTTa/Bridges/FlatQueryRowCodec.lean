import Mettapedia.GSLT.Dynamics.ConjunctiveRowMatching
import Mettapedia.GSLT.LanguageDef.FiniteEnvironmentCompilation
import Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics

/-!
# PeTTa flat-row matching and typed query bindings

The generated variable inventory gives each query variable one slot. A
round-tripping literal codec relates row values to actual source Atoms.
Captured query bindings must decode exactly; an unsupported bound Atom must
not become an unbound slot. Other caller bindings are retained in the source
substitution and are not invented by this projection.

The bridge uses PeTTa's actual directional `matchValue`, not a supplied
matching oracle. Its ordinary relation-head fragment excludes the special
`cons` pattern view. Stored open terms require their separate unifying route.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.FlatQueryRowCodec

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.GSLT.LanguageDef.FiniteEnvironmentCompilation
open Mettapedia.GSLT.Dynamics ConjunctiveRegionProvenance ConjunctiveRowMatching
open SpaceSemantics

structure Codec (Value : Type) where
  encode : Value → Atom
  decode : Atom → Option Value
  roundtrip : ∀ value, decode (encode value) = some value
  exact : ∀ atom value, decode atom = some value → encode value = atom
  literal : ∀ value, Literal (encode value)

variable {Value : Type}

theorem Codec.injective (codec : Codec Value) : Function.Injective codec.encode := by
  intro first second same
  have decoded := congrArg codec.decode same
  simpa only [codec.roundtrip, Option.some.injEq] using decoded

def integers : Codec Int where
  encode value := .grounded (.int value)
  decode atom := match atom with | .grounded (.int value) => some value | _ => none
  roundtrip _ := rfl
  exact atom value decoded := by
    split at decoded
    · cases decoded; rfl
    · cases decoded
  literal value := .grounded (.int value)

def booleans : Codec Bool where
  encode value := .grounded (.bool value)
  decode atom := match atom with | .grounded (.bool value) => some value | _ => none
  roundtrip _ := rfl
  exact atom value decoded := by
    split at decoded
    · cases decoded; rfl
    · cases decoded
  literal value := .grounded (.bool value)

def Represents (codec : Codec Value) (names : Inventory String)
    (environment : DenseEnvironment names Value) (bindings : Subst) : Prop :=
  ∀ slot, Subst.lookup bindings (names.reify slot) = (environment slot).map codec.encode

instance (codec : Codec Value) (names : Inventory String)
    (environment : DenseEnvironment names Value) (bindings : Subst) : Decidable (Represents codec names environment bindings) :=
  inferInstanceAs (Decidable (∀ slot, Subst.lookup bindings (names.reify slot) = (environment slot).map codec.encode))

def readback (codec : Codec Value) (names : Inventory String) (bindings : Subst) : DenseEnvironment names Value :=
  fun slot => (Subst.lookup bindings (names.reify slot)).bind codec.decode

theorem readback_exact (codec : Codec Value) (names : Inventory String)
    (environment : DenseEnvironment names Value) (bindings : Subst) (represented : Represents codec names environment bindings) :
    readback codec names bindings = environment := by
  funext slot
  unfold readback
  rw [represented slot]
  cases environment slot <;> simp [codec.roundtrip]

def capture (codec : Codec Value) (names : Inventory String) (bindings : Subst) :
    Option {environment : DenseEnvironment names Value // Represents codec names environment bindings} :=
  if represented : Represents codec names (readback codec names bindings) bindings then
    some ⟨readback codec names bindings, represented⟩ else none

theorem capture_exact (codec : Codec Value) (names : Inventory String) (bindings : Subst) :
    (capture codec names bindings).isSome = true ↔ ∃ environment, Represents codec names environment bindings := by
  unfold capture
  split
  next represented => exact ⟨fun _ => ⟨_, represented⟩, fun _ => rfl⟩
  next rejected =>
    constructor
    · intro impossible; cases impossible
    · rintro ⟨environment, represented⟩
      exact False.elim (rejected (by rw [readback_exact codec names environment bindings represented]; exact represented))

theorem unsupported_capture_refuses (codec : Codec Value) (names : Inventory String) (bindings : Subst)
    (slot : names.Slot) (atom : Atom) (found : Subst.lookup bindings (names.reify slot) = some atom)
    (unsupported : codec.decode atom = none) : capture codec names bindings = none := by
  unfold capture
  split
  next represented =>
    have same := represented slot
    simp only [readback, found, Option.bind_some, unsupported, Option.map_none] at same
    cases same
  next => rfl

private theorem reify_injective (names : Inventory String) : Function.Injective names.reify := by
  intro first second same
  have decoded := congrArg names.resolve? same
  simpa only [Inventory.resolve_reify, Option.some.injEq] using decoded

theorem represents_cons_update (codec : Codec Value) (names : Inventory String)
    (environment : DenseEnvironment names Value) (bindings : Subst) (represented : Represents codec names environment bindings)
    (slot : names.Slot) (value : Value) :
    Represents codec names (Function.update environment slot (some value))
      ((names.reify slot, codec.encode value) :: bindings) := by
  intro other
  by_cases same : other = slot
  · subst other
    simp [Subst.lookup]
  · have distinct : names.reify slot ≠ names.reify other := fun equal => same ((reify_injective names equal).symm)
    simp only [Function.update_of_ne same]
    simpa [Subst.lookup, distinct] using represented other

def encodeCell (codec : Codec Value) (names : Inventory String) : Cell names.Slot Value → Atom
  | .constant value => codec.encode value
  | .variable slot => .var (names.reify slot)

variable [DecidableEq Value]

theorem match_cell (codec : Codec Value) (names : Inventory String)
    (environment : DenseEnvironment names Value) (bindings : Subst) (represented : Represents codec names environment bindings)
    (cell : Cell names.Slot Value) (value : Value) :
    Option.Rel (Represents codec names) (bindCell environment cell value)
      (matchValue bindings (encodeCell codec names cell) (codec.encode value)) := by
  cases cell with
  | constant expected =>
      simp only [encodeCell, matchValue_literal (codec.literal expected)]
      have equality : codec.encode expected = codec.encode value ↔ expected = value := codec.injective.eq_iff
      simp only [equality]
      by_cases same : expected = value
      · simp only [bindCell, same, ↓reduceIte]
        exact .some represented
      · simp [bindCell, same]
  | «variable» slot =>
      simp only [encodeCell, matchValue, Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, represented slot]
      cases old : environment slot with
      | none =>
          simp only [bindCell, old, Option.map_none]
          exact .some (represents_cons_update codec names environment bindings represented slot value)
      | some expected =>
          by_cases same : expected = value
          · subst expected
            simp only [bindCell, old, Option.map_some, beq_self_eq_true, ↓reduceIte]
            exact .some represented
          · have different : codec.encode value ≠ codec.encode expected := fun equal => same (codec.injective equal).symm
            simp [bindCell, old, same, different]

theorem match_values (codec : Codec Value) (names : Inventory String)
    (environment : DenseEnvironment names Value) (bindings : Subst) (represented : Represents codec names environment bindings)
    (cells : List (Cell names.Slot Value)) (values : List Value) :
    Option.Rel (Represents codec names) (bindValues environment cells values)
      (matchValue.matchValues bindings (cells.map (encodeCell codec names)) (values.map codec.encode)) := by
  induction cells generalizing environment bindings values with
  | nil =>
      cases values with
      | nil =>
          simp only [bindValues, List.map_nil, matchValue.matchValues]
          exact .some represented
      | cons => simp [bindValues, matchValue.matchValues]
  | cons cell cells ih =>
      cases values with
      | nil => simp [bindValues, matchValue.matchValues]
      | cons value values =>
          have first := match_cell codec names environment bindings represented cell value
          generalize targetEq : bindCell environment cell value = target at first
          generalize sourceEq : matchValue bindings (encodeCell codec names cell) (codec.encode value) = source at first
          cases first with
          | none => simp [bindValues, targetEq, matchValue.matchValues, sourceEq]
          | @some next bound related =>
              simp only [bindValues, targetEq, List.map_cons, matchValue.matchValues, sourceEq, Option.bind_some]
              exact ih next bound related values

def pattern (codec : Codec Value) (names : Inventory String) (head : String) (cells : List (Cell names.Slot Value)) : Atom :=
  .expression (.symbol head :: cells.map (encodeCell codec names))

def row (codec : Codec Value) (head : String) (values : List Value) : Atom :=
  .expression (.symbol head :: values.map codec.encode)

theorem match_row (codec : Codec Value) (names : Inventory String)
    (environment : DenseEnvironment names Value) (bindings : Subst) (represented : Represents codec names environment bindings)
    (head : String) (ordinary : head ≠ "cons") (cells : List (Cell names.Slot Value)) (values : List Value) :
    Option.Rel (Represents codec names) (bindValues environment cells values)
      (matchValue bindings (pattern codec names head cells) (row codec head values)) := by
  unfold pattern row
  rw [matchValue_expression_of_not_cons bindings _ _ (by
    intro first rest same
    exact ordinary (by simpa using (List.cons.inj same).1))]
  simp only [matchValue.matchValues, matchValue, Mettapedia.Languages.ProcessCalculi.MORK.matchAtom,
    beq_self_eq_true, ↓reduceIte]
  exact match_values codec names environment bindings represented cells values

theorem row_readback_exact (codec : Codec Value) (names : Inventory String)
    (environment : DenseEnvironment names Value) (bindings : Subst) (represented : Represents codec names environment bindings)
    (head : String) (ordinary : head ≠ "cons") (cells : List (Cell names.Slot Value)) (values : List Value) :
    (matchValue bindings (pattern codec names head cells) (row codec head values)).map (readback codec names) =
      bindValues environment cells values := by
  have related := match_row codec names environment bindings represented head ordinary cells values
  generalize targetEq : bindValues environment cells values = target at related ⊢
  generalize sourceEq : matchValue bindings (pattern codec names head cells) (row codec head values) = source at related ⊢
  cases related with
  | none => rfl
  | some represented => exact congrArg some (readback_exact _ _ _ _ represented)

namespace Controls

def oneName : Inventory String := ⟨["x"], by decide⟩
def only : oneName.Slot := ⟨0, by decide⟩

theorem unsupported_boolean_is_not_an_unbound_integer :
    (capture integers oneName [("x", .grounded (.bool true))]).isNone = true := by decide +kernel

theorem captured_integer_roundtrips :
    (capture integers oneName [("x", .grounded (.int 7))]).map (fun captured => captured.val only) =
      some (some 7) := by decide +kernel

theorem row_repeated_variable_rejects_conflict :
    matchValue [] (pattern integers oneName "r" [.variable only, .variable only]) (row integers "r" [1, 2]) = none := by decide +kernel

theorem row_repeated_variable_keeps_correlation :
    (matchValue [] (pattern integers oneName "r" [.variable only, .variable only]) (row integers "r" [1, 1])).map
      (readback integers oneName) = some (fun _ => some 1) := by
  rw [row_readback_exact integers oneName (fun _ => none) [] (by intro slot; rfl) "r" (by decide)]
  decide +kernel

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.FlatQueryRowCodec
