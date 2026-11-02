import Mettapedia.OSLF.NativeTypes.Certificates.Search

/-!
# Checked finite prefixes of fair certificate search

An ordered finite prefix may contain arbitrary certificate candidates. Each is
checked against the requested independent judgment before it is accepted. The
complete raw-code stream follows the prefix; adding seeds preserves fairness.
A paused cursor retains the position in both phases and conclusive results stop.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Certificates.SeededSearch

universe u

variable {P : Presentation.{u}} [Encodable P.Rule]

def candidate (seeds : List (Tree P)) (position : Nat) : Option (Tree P) :=
  if position < seeds.length then seeds[position]? else
    Encodable.decode (α := Tree P) (position - seeds.length)

theorem candidate_at_encoded (seeds : List (Tree P)) (certificate : Tree P) :
    candidate seeds (seeds.length + Encodable.encode certificate) = some certificate := by
  rw [candidate, if_neg (by omega), Nat.add_sub_cancel_left, Tree.decode_encode]

variable [DecidableEq P.Judgment]

def step (seeds : List (Tree P)) (judgment : P.Judgment) (state : Search.State P) : Search.State P :=
  Search.Scheduled.step (candidate seeds) judgment state

def run (seeds : List (Tree P)) (judgment : P.Judgment) : Nat → Search.State P → Search.State P :=
  Search.Scheduled.run (candidate seeds) judgment

def search (seeds : List (Tree P)) (judgment : P.Judgment) (budget : Nat) : Search.State P :=
  run seeds judgment budget Search.initial

theorem run_add (seeds : List (Tree P)) (judgment : P.Judgment)
    (first second : Nat) (state : Search.State P) :
    run seeds judgment (first + second) state =
      run seeds judgment second (run seeds judgment first state) :=
  Search.Scheduled.run_add (candidate seeds) judgment first second state

theorem run_settled (seeds : List (Tree P)) (judgment : P.Judgment)
    (budget : Nat) (state : Search.State P) (certificate : Tree P)
    (settled : state.found = some certificate) : run seeds judgment budget state = state :=
  Search.Scheduled.run_settled (candidate seeds) judgment budget state certificate settled

theorem step_valid (seeds : List (Tree P)) (judgment : P.Judgment) (state : Search.State P)
    (valid : state.Valid judgment) : (step seeds judgment state).Valid judgment :=
  Search.Scheduled.step_valid (candidate seeds) judgment state valid

theorem run_valid (seeds : List (Tree P)) (judgment : P.Judgment) (budget : Nat)
    (state : Search.State P) (valid : state.Valid judgment) : (run seeds judgment budget state).Valid judgment :=
  Search.Scheduled.run_valid (candidate seeds) judgment budget state valid

theorem search_sound (seeds : List (Tree P)) (judgment : P.Judgment) (budget : Nat)
    (certificate : Tree P) (found : (search seeds judgment budget).found = some certificate) :
    ∃ derivation : P.Derivation judgment, Tree.erase derivation = certificate :=
  Search.Scheduled.run_sound (candidate seeds) judgment budget certificate found

theorem step_cursor (seeds : List (Tree P)) (judgment : P.Judgment) (state : Search.State P)
    (unresolved : state.found = none) : (step seeds judgment state).cursor = state.cursor + 1 :=
  Search.Scheduled.step_cursor (candidate seeds) judgment state unresolved

theorem step_at_encoded (seeds : List (Tree P)) (judgment : P.Judgment)
    (state : Search.State P) (certificate : Tree P) (unresolved : state.found = none)
    (cursor : state.cursor = seeds.length + Encodable.encode certificate)
    (accepted : certificate.check judgment = true) :
    (step seeds judgment state).found = some certificate :=
  Search.Scheduled.step_at (candidate seeds) judgment state certificate unresolved
    (by simpa only [cursor] using candidate_at_encoded seeds certificate) accepted

theorem complete_from (seeds : List (Tree P)) (judgment : P.Judgment)
    (certificate : Tree P) (accepted : certificate.check judgment = true)
    (budget : Nat) (state : Search.State P)
    (before : state.cursor ≤ seeds.length + Encodable.encode certificate)
    (sufficient : seeds.length + Encodable.encode certificate < state.cursor + budget) :
    ∃ result, (run seeds judgment budget state).found = some result :=
  Search.Scheduled.complete_from_at (candidate seeds) judgment certificate accepted _
    (candidate_at_encoded seeds certificate) budget state before sufficient

def discoveryBound (prefixLength wireBits : Nat) : Nat := prefixLength + Tree.discoveryBound wireBits

theorem discover_within_wire_bound (seeds : List (Tree P)) (judgment : P.Judgment)
    (certificate : Tree P) (accepted : certificate.check judgment = true) :
    ∃ result,
      (search seeds judgment (discoveryBound seeds.length (Tree.wireSize certificate))).found = some result := by
  apply complete_from seeds judgment certificate accepted _ Search.initial (Nat.zero_le _)
  simpa only [Search.initial, discoveryBound, Nat.zero_add] using
    Nat.add_lt_add_left (Tree.code_lt_discoveryBound certificate) seeds.length

theorem stable_conclusion (seeds : List (Tree P)) (judgment : P.Judgment)
    (budget extra : Nat) (certificate : Tree P)
    (found : (search seeds judgment budget).found = some certificate) :
    search seeds judgment (budget + extra) = search seeds judgment budget :=
  (run_add seeds judgment budget extra Search.initial).trans
    (run_settled seeds judgment extra (search seeds judgment budget) certificate found)

end Mettapedia.OSLF.NativeTypes.Certificates.SeededSearch
