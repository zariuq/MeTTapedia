import Mettapedia.Languages.ProcessCalculi.MORK.WorkQueueExec

/-!
# Physical ordering from the executable location prefix

MORK orders ordinary MM2 directives by the compact bytes of the complete
`(exec location input output)` atom.  The location occurs before the input and
output, so a strict difference inside the location decides the order without
inspecting either rule body.  This module exposes that prefix decomposition for
proofs about generated executable presentations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-- An atom has the ordinary four-field MM2 executable shell at `location`. -/
def ExecSurfaceAt (atom location : Atom) : Prop :=
  ∃ input output,
    atom = .expression [.symbol "exec", location, input, output]

/-- Compact bytes of a nonempty, physically representable MM2 symbol. -/
def compactSymbolBytes (name : String) : List Nat :=
  (0xC0 + (morkUtf8Bytes name).length) ::
    (morkUtf8Bytes name).map UInt8.toNat

/-- The exact compact encoding of one representable symbol preserves the
variable environment. -/
theorem morkCompactEncodeAtom_symbol_exact (environment : List String)
    (name : String)
    (positive : 0 < (morkUtf8Bytes name).length)
    (bounded : (morkUtf8Bytes name).length < 64) :
    morkCompactEncodeAtom environment (.symbol name) =
      some (compactSymbolBytes name, environment) := by
  simp [morkCompactEncodeAtom, compactSymbolBytes, positive, bounded]

private theorem twoSymbolLocation_exact
    (priority name : String)
    (priorityPositive : 0 < (morkUtf8Bytes priority).length)
    (priorityBounded : (morkUtf8Bytes priority).length < 64)
    (namePositive : 0 < (morkUtf8Bytes name).length)
    (nameBounded : (morkUtf8Bytes name).length < 64) :
    morkCompactEncodeAtom []
        (.expression [.symbol priority, .symbol name]) =
      some
        (2 :: (compactSymbolBytes priority ++ compactSymbolBytes name), []) := by
  simp only [morkCompactEncodeAtom]
  rw [if_pos (by simp)]
  simp only [morkCompactEncodeAtom.encodeList]
  rw [morkCompactEncodeAtom_symbol_exact [] priority priorityPositive
      priorityBounded]
  simp only
  rw [morkCompactEncodeAtom_symbol_exact [] name namePositive nameBounded]
  simp

/-- A successful compact encoding of an ordinary executable begins with the
exact bytes for `exec` and its two-symbol location.  The body remains an opaque
suffix, so clients do not normalize generated patterns or sinks merely to
establish scheduler priority. -/
theorem morkCompactExec_location_prefix
    {atom location : Atom} (priority name : String) (input output : Atom)
    (key : List Nat)
    (surface :
      atom = .expression [.symbol "exec", location, input, output])
    (locationExact :
      location = .expression [.symbol priority, .symbol name])
    (priorityPositive : 0 < (morkUtf8Bytes priority).length)
    (priorityBounded : (morkUtf8Bytes priority).length < 64)
    (namePositive : 0 < (morkUtf8Bytes name).length)
    (nameBounded : (morkUtf8Bytes name).length < 64)
    (keyExact : morkCompactKey? atom = some key) :
    ∃ rest,
      key =
        [4, 196, 101, 120, 101, 99, 2] ++
          compactSymbolBytes priority ++ compactSymbolBytes name ++ rest := by
  subst atom
  subst location
  have execExact :
      morkCompactEncodeAtom [] (.symbol "exec") =
        some ([196, 101, 120, 101, 99], []) := by
    decide
  have locationEncoded :=
    twoSymbolLocation_exact priority name priorityPositive priorityBounded
      namePositive nameBounded
  unfold morkCompactKey? at keyExact
  simp only [morkCompactEncodeAtom] at keyExact
  rw [if_pos (by simp)] at keyExact
  simp only [morkCompactEncodeAtom.encodeList] at keyExact
  rw [execExact] at keyExact
  simp only at keyExact
  rw [locationEncoded] at keyExact
  simp only at keyExact
  cases inputExact : morkCompactEncodeAtom [] input with
  | none => simp [inputExact] at keyExact
  | some inputResult =>
      rcases inputResult with ⟨inputBytes, inputEnvironment⟩
      simp only [inputExact] at keyExact
      cases outputExact : morkCompactEncodeAtom inputEnvironment output with
      | none => simp [outputExact] at keyExact
      | some outputResult =>
          rcases outputResult with ⟨outputBytes, outputEnvironment⟩
          simp only [outputExact] at keyExact
          simp only [Option.map_some, Option.some.injEq] at keyExact
          subst key
          exact ⟨inputBytes ++ outputBytes, by simp⟩

/-- Boolean success of the exact compact encoder gives physical
representability without exposing the encoded body. -/
theorem morkCompactRepresentable_of_isSome {atom : Atom}
    (encoded : (morkCompactKey? atom).isSome = true) :
    MorkCompactRepresentable atom := by
  cases exact : morkCompactKey? atom with
  | none => simp [exact] at encoded
  | some key => exact ⟨key, exact⟩

/-- Prefix decomposition for the total scheduler key of a representable
ordinary executable. -/
theorem totalMorkCompactExec_location_prefix
    {atom location : Atom} (priority name : String) (input output : Atom)
    (surface :
      atom = .expression [.symbol "exec", location, input, output])
    (locationExact :
      location = .expression [.symbol priority, .symbol name])
    (priorityPositive : 0 < (morkUtf8Bytes priority).length)
    (priorityBounded : (morkUtf8Bytes priority).length < 64)
    (namePositive : 0 < (morkUtf8Bytes name).length)
    (nameBounded : (morkUtf8Bytes name).length < 64)
    (representable : MorkCompactRepresentable atom) :
    ∃ rest,
      totalMorkCompactKey atom =
        [4, 196, 101, 120, 101, 99, 2] ++
          compactSymbolBytes priority ++ compactSymbolBytes name ++ rest := by
  obtain ⟨key, keyExact⟩ := representable
  obtain ⟨rest, prefixExact⟩ :=
    morkCompactExec_location_prefix priority name input output key surface
      locationExact priorityPositive priorityBounded namePositive nameBounded
      keyExact
  refine ⟨rest, ?_⟩
  unfold totalMorkCompactKey
  rw [keyExact]
  exact prefixExact

section Canaries

theorem compact_symbol_positive_canary :
    compactSymbolBytes "00" = [194, 48, 48] := by
  decide

theorem physical_priority_prefix_positive_canary (left right : List Nat) :
    lexLt
        ([4, 196, 101, 120, 101, 99, 2] ++ compactSymbolBytes "00" ++ left)
        ([4, 196, 101, 120, 101, 99, 2] ++ compactSymbolBytes "08" ++ right) =
      true := by
  rfl

theorem physical_priority_prefix_negative_canary (left right : List Nat) :
    lexLt
        ([4, 196, 101, 120, 101, 99, 2] ++ compactSymbolBytes "08" ++ left)
        ([4, 196, 101, 120, 101, 99, 2] ++ compactSymbolBytes "00" ++ right) =
      false := by
  rfl

end Canaries

#print axioms morkCompactEncodeAtom_symbol_exact
#print axioms morkCompactExec_location_prefix
#print axioms morkCompactRepresentable_of_isSome
#print axioms totalMorkCompactExec_location_prefix
#print axioms physical_priority_prefix_positive_canary
#print axioms physical_priority_prefix_negative_canary

end Mettapedia.Languages.ProcessCalculi.MORK
