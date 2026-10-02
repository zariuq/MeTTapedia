import Mettapedia.Machines.IncrementalConformance.CallableForeignBoundary

/-!
# Authored names and generated callable identities

The prepared-callable codec is an inverse on its callable domain. This does
not make it an inverse on arbitrary authored symbols: a symbol with the same
foreign atom image is decoded as the dictionary-owned callable.

These results use the actual serializers, decoder and prepared dictionary.
They isolate the additional name-separation obligation, exhibit loss of the
data/callable distinction, and show why qualifying both names by the same
space does not supply that distinction. They do not certify a native repair.
Exact representation recovery is stronger than preserving an alias-aware
observer: deliberately equating a name and its callable is not prohibited.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.IncrementalConformance.CallableNameSeparation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open CallableForeignBoundary

theorem symbol_roundtrip_iff_name_unowned (entries : List Entry) (name : String) :
    decodePublic entries (serializeData (.symbol name)) = .data (.symbol name) ↔
      lookupName name entries = none := by
  cases found : lookupName name entries with
  | none => simp [serializeData, decodePublic, decodeCallable, found, decodeData]
  | some entry => simp [serializeData, decodePublic, decodeCallable, found]

theorem owned_name_changes_symbol_role (entries : List Entry) (name : String)
    (entry : Entry) (found : lookupName name entries = some entry) :
    decodePublic entries (serializeData (.symbol name)) =
      .callable ⟨entry.code, []⟩ := by
  simp [serializeData, decodePublic, decodeCallable, found]

/-- Two independently specified input roles have the same actual wire image. -/
theorem prepared_callable_and_authored_symbol_collide
    (scope : String) (counter : Nat) (source : NominalCallables.Declaration) :
    serializePublic (dictionary scope counter [source])
        (.callable (NominalCallables.close (counter + 1) source [])) =
      serializePublic (dictionary scope counter [source])
        (.data (.symbol (generatedName scope (counter + 1)))) := by
  simp [serializePublic, serializeCallable, dictionary_cons, lookupToken,
    NominalCallables.close, codeToken_canonical, serializeData]

/-- Exact recovery of both roles is impossible for any decoder of this image. -/
theorem no_exact_decoder_for_both_roles
    (scope : String) (counter : Nat) (source : NominalCallables.Declaration) :
    ¬ ∃ decode : Option ForeignTerm → NativeValue,
      (∀ value : NativeValue,
        decode (serializePublic (dictionary scope counter [source]) value) = value) := by
  rintro ⟨decode, inverse⟩
  have callable := inverse (.callable (NominalCallables.close (counter + 1) source []))
  have symbol := inverse (.data (.symbol (generatedName scope (counter + 1))))
  rw [prepared_callable_and_authored_symbol_collide] at callable
  rw [symbol] at callable
  cases callable

/-- An ordinary name can lose its data interpretation after catalogue growth. -/
theorem adding_owner_reclassifies_existing_symbol
    (scope : String) (counter : Nat) (source : NominalCallables.Declaration) :
    decodePublic [] (.atom (generatedName scope (counter + 1))) =
        .data (.symbol (generatedName scope (counter + 1))) ∧
      decodePublic (dictionary scope counter [source])
        (.atom (generatedName scope (counter + 1))) =
        .callable (NominalCallables.close (counter + 1) source []) := by
  simp [decodePublic, decodeCallable, decodeData, lookupName, dictionary_cons,
    NominalCallables.close]

/-- Bounded fresh allocation skips occupied names. Fuel models the remaining
nonwrapping counter range, not a semantic limit on evaluation. -/
def chooseFresh (label : Nat → String) (occupied : List String)
    (next : Nat) : Nat → Option Nat
  | 0 => none
  | fuel + 1 =>
      if label next ∈ occupied then chooseFresh label occupied (next + 1) fuel
      else some next

theorem accepted_name_unoccupied (label : Nat → String) (occupied : List String)
    (next fuel token : Nat) (accepted : chooseFresh label occupied next fuel = some token) :
    label token ∉ occupied := by
  induction fuel generalizing next with
  | zero => simp [chooseFresh] at accepted
  | succ fuel ih =>
      simp only [chooseFresh] at accepted
      split at accepted
      · exact ih (next + 1) accepted
      · cases accepted
        assumption

theorem accepted_token_in_range (label : Nat → String) (occupied : List String)
    (next fuel token : Nat) (accepted : chooseFresh label occupied next fuel = some token) :
    next ≤ token ∧ token < next + fuel := by
  induction fuel generalizing next with
  | zero => simp [chooseFresh] at accepted
  | succ fuel ih =>
      simp only [chooseFresh] at accepted
      split at accepted
      · have range := ih (next + 1) accepted
        omega
      · cases accepted
        omega

theorem successive_tokens_distinct (label : Nat → String) (occupied : List String)
    (first second fuel : Nat)
    (accepted : chooseFresh label occupied (first + 1) fuel = some second) :
    first ≠ second := by
  have range := accepted_token_in_range label occupied (first + 1) fuel second accepted
  omega

theorem exhausted_iff_candidates_occupied (label : Nat → String) (occupied : List String)
    (next fuel : Nat) :
    chooseFresh label occupied next fuel = none ↔
      ∀ offset, offset < fuel → label (next + offset) ∈ occupied := by
  induction fuel generalizing next with
  | zero => simp [chooseFresh]
  | succ fuel ih =>
      by_cases blocked : label next ∈ occupied
      · simp only [chooseFresh, blocked, ↓reduceIte, ih]
        constructor
        · intro rest offset bound
          cases offset with
          | zero => simpa using blocked
          | succ offset =>
              have present := rest offset (by omega)
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using present
        · intro all offset bound
          have present := all (offset + 1) (by omega)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using present
      · simp only [chooseFresh, blocked, ↓reduceIte, Option.some_ne_none, false_iff]
        intro all
        exact blocked (by simpa using all 0 (by omega))

namespace Controls

def source : NominalCallables.Declaration := ⟨["x"], .bvar 0, []⟩

theorem ordinary_symbol_preserved :
    decodePublic (dictionary "runtime" 0 [source])
        (serializeData (.symbol "ordinary")) = .data (.symbol "ordinary") := by
  rw [symbol_roundtrip_iff_name_unowned]
  decide

theorem source_name_and_callable_have_same_bytes :
    serializePublic (dictionary "runtime" 0 [source])
        (.callable (NominalCallables.close 1 source [])) =
      serializePublic (dictionary "runtime" 0 [source])
        (.data (.symbol "runtime:lambda_1")) :=
  prepared_callable_and_authored_symbol_collide "runtime" 0 source

theorem adding_scope_does_not_separate_roles :
    ¬ ∃ decode : Option ForeignTerm → NativeValue,
      (∀ value : NativeValue,
        decode (serializePublic (dictionary "isolated-space" 0 [source]) value) = value) :=
  no_exact_decoder_for_both_roles "isolated-space" 0 source

theorem new_owner_changes_existing_symbol :
    decodePublic [] (.atom "runtime:lambda_1") = .data (.symbol "runtime:lambda_1") ∧
      decodePublic (dictionary "runtime" 0 [source]) (.atom "runtime:lambda_1") =
        .callable (NominalCallables.close 1 source []) :=
  adding_owner_reclassifies_existing_symbol "runtime" 0 source

theorem skip_two_occupied_names :
    chooseFresh (generatedName "runtime")
        ["runtime:lambda_1", "runtime:lambda_2"] 1 3 = some 3 := by decide

theorem retain_first_free_name :
    chooseFresh (generatedName "runtime") ["runtime:lambda_2"] 1 3 = some 1 := by decide

theorem no_counter_wrap_when_all_available_names_occupied :
    chooseFresh (generatedName "runtime")
        ["runtime:lambda_1", "runtime:lambda_2"] 1 2 = none := by decide

end Controls

end Mettapedia.Machines.IncrementalConformance.CallableNameSeparation
