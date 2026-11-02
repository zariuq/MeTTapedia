import Mettapedia.OSLF.NativeTypes.Certificates.SeededSearch

/-!
# Deferred finite prefixes of fair native certificate search

Candidate factories are retained without constructing their trees. One work
unit forces only the factory at the current cursor, then checks its original
judgment. An absent candidate still consumes its ordered slot. After every
prefix slot, the same fair certificate-code stream follows. The eager option
specification retains these slots and independently specifies the comparison.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Certificates.DeferredSeededSearch

universe u

variable {P : Presentation.{u}} [Encodable P.Rule]

abbrev Prefix (P : Presentation.{u}) := List (Unit → Option (Tree P))

def candidate (seeds : Prefix P) (position : Nat) : Option (Tree P) :=
  if position < seeds.length then (seeds[position]?).bind (fun factory => factory ()) else
    Encodable.decode (α := Tree P) (position - seeds.length)

namespace Eager

def candidate (seeds : List (Option (Tree P))) (position : Nat) : Option (Tree P) :=
  if position < seeds.length then (seeds[position]?).bind id else
    Encodable.decode (α := Tree P) (position - seeds.length)

variable [DecidableEq P.Judgment]

def step (seeds : List (Option (Tree P))) (judgment : P.Judgment)
    (state : Search.State P) : Search.State P :=
  match state.found with
  | some _ => state
  | none =>
      match candidate seeds state.cursor with
      | none => ⟨state.cursor + 1, none⟩
      | some certificate =>
          if certificate.check judgment then ⟨state.cursor + 1, some certificate⟩
          else ⟨state.cursor + 1, none⟩

def run (seeds : List (Option (Tree P))) (judgment : P.Judgment) :
    Nat → Search.State P → Search.State P
  | 0, state => state
  | budget + 1, state => run seeds judgment budget (step seeds judgment state)

def search (seeds : List (Option (Tree P))) (judgment : P.Judgment)
    (budget : Nat) : Search.State P := run seeds judgment budget Search.initial

end Eager

/-- The eagerly materialized reference sequence retains absent slots. -/
def freeze (seeds : Prefix P) : List (Option (Tree P)) := seeds.map (fun factory => factory ())

theorem candidate_freeze (seeds : Prefix P) (position : Nat) :
    candidate seeds position = Eager.candidate (freeze seeds) position := by
  simp only [candidate, Eager.candidate, freeze, List.length_map, List.getElem?_map,
    Option.bind_map, Function.comp_def, id_eq]

/-- Embedding a concrete prefix preserves the previous all-present schedule. -/
def ofSeeds (seeds : List (Tree P)) : Prefix P := seeds.map (fun tree _ => some tree)

theorem candidate_ofSeeds (seeds : List (Tree P)) (position : Nat) :
    candidate (ofSeeds seeds) position = SeededSearch.candidate seeds position := by
  simp only [candidate, ofSeeds, SeededSearch.candidate, List.length_map, List.getElem?_map,
    Option.bind_map, Function.comp_def, Option.bind_fun_some]

theorem candidate_at_encoded (seeds : Prefix P) (certificate : Tree P) :
    candidate seeds (seeds.length + Encodable.encode certificate) = some certificate := by
  rw [candidate, if_neg (by omega), Nat.add_sub_cancel_left, Tree.decode_encode]

variable [DecidableEq P.Judgment]

def step (seeds : Prefix P) (judgment : P.Judgment) (state : Search.State P) : Search.State P :=
  Search.Scheduled.step (candidate seeds) judgment state

def run (seeds : Prefix P) (judgment : P.Judgment) : Nat → Search.State P → Search.State P :=
  Search.Scheduled.run (candidate seeds) judgment

def search (seeds : Prefix P) (judgment : P.Judgment) (budget : Nat) : Search.State P :=
  run seeds judgment budget Search.initial

theorem step_freeze (seeds : Prefix P) (judgment : P.Judgment) (state : Search.State P) :
    step seeds judgment state = Eager.step (freeze seeds) judgment state := by
  simp only [step, Search.Scheduled.step, Eager.step, candidate_freeze]
  rfl

theorem run_freeze (seeds : Prefix P) (judgment : P.Judgment)
    (budget : Nat) (state : Search.State P) :
    run seeds judgment budget state = Eager.run (freeze seeds) judgment budget state := by
  induction budget generalizing state with
  | zero => rfl
  | succ budget ih =>
      change run seeds judgment budget (step seeds judgment state) =
        Eager.run (freeze seeds) judgment budget (Eager.step (freeze seeds) judgment state)
      rw [step_freeze, ih]

theorem step_ofSeeds (seeds : List (Tree P)) (judgment : P.Judgment) (state : Search.State P) :
    step (ofSeeds seeds) judgment state = SeededSearch.step seeds judgment state := by
  simp only [step, SeededSearch.step, Search.Scheduled.step, candidate_ofSeeds]

theorem run_ofSeeds (seeds : List (Tree P)) (judgment : P.Judgment)
    (budget : Nat) (state : Search.State P) :
    run (ofSeeds seeds) judgment budget state = SeededSearch.run seeds judgment budget state := by
  unfold run SeededSearch.run
  rw [show candidate (ofSeeds seeds) = SeededSearch.candidate seeds from funext (candidate_ofSeeds seeds)]

theorem step_current (seeds : Prefix P) (judgment : P.Judgment)
    (state : Search.State P) (factory : Unit → Option (Tree P))
    (unresolved : state.found = none) (scheduled : seeds[state.cursor]? = some factory) :
    step seeds judgment state =
      match factory () with
      | none => ⟨state.cursor + 1, none⟩
      | some certificate =>
          if certificate.check judgment then ⟨state.cursor + 1, some certificate⟩
          else ⟨state.cursor + 1, none⟩ := by
  have before : state.cursor < seeds.length := List.getElem?_eq_some_iff.mp scheduled |>.1
  simp only [step, Search.Scheduled.step, unresolved, candidate, before, if_true, scheduled, Option.bind_some]
  rfl

theorem step_absent (seeds : Prefix P) (judgment : P.Judgment)
    (state : Search.State P) (factory : Unit → Option (Tree P))
    (unresolved : state.found = none) (scheduled : seeds[state.cursor]? = some factory)
    (absent : factory () = none) : step seeds judgment state = ⟨state.cursor + 1, none⟩ := by
  simpa only [absent] using step_current seeds judgment state factory unresolved scheduled

theorem search_freeze (seeds : Prefix P) (judgment : P.Judgment) (budget : Nat) :
    search seeds judgment budget = Eager.search (freeze seeds) judgment budget :=
  run_freeze seeds judgment budget Search.initial

theorem search_ofSeeds (seeds : List (Tree P)) (judgment : P.Judgment) (budget : Nat) :
    search (ofSeeds seeds) judgment budget = SeededSearch.search seeds judgment budget :=
  run_ofSeeds seeds judgment budget Search.initial

theorem run_add (seeds : Prefix P) (judgment : P.Judgment)
    (first second : Nat) (state : Search.State P) :
    run seeds judgment (first + second) state =
      run seeds judgment second (run seeds judgment first state) :=
  Search.Scheduled.run_add (candidate seeds) judgment first second state

theorem run_settled (seeds : Prefix P) (judgment : P.Judgment)
    (budget : Nat) (state : Search.State P) (certificate : Tree P)
    (settled : state.found = some certificate) : run seeds judgment budget state = state :=
  Search.Scheduled.run_settled (candidate seeds) judgment budget state certificate settled

theorem step_valid (seeds : Prefix P) (judgment : P.Judgment) (state : Search.State P)
    (valid : state.Valid judgment) : (step seeds judgment state).Valid judgment :=
  Search.Scheduled.step_valid (candidate seeds) judgment state valid

theorem run_valid (seeds : Prefix P) (judgment : P.Judgment) (budget : Nat)
    (state : Search.State P) (valid : state.Valid judgment) : (run seeds judgment budget state).Valid judgment :=
  Search.Scheduled.run_valid (candidate seeds) judgment budget state valid

theorem search_sound (seeds : Prefix P) (judgment : P.Judgment) (budget : Nat)
    (certificate : Tree P) (found : (search seeds judgment budget).found = some certificate) :
    ∃ derivation : P.Derivation judgment, Tree.erase derivation = certificate :=
  Search.Scheduled.run_sound (candidate seeds) judgment budget certificate found

theorem step_cursor (seeds : Prefix P) (judgment : P.Judgment) (state : Search.State P)
    (unresolved : state.found = none) : (step seeds judgment state).cursor = state.cursor + 1 :=
  Search.Scheduled.step_cursor (candidate seeds) judgment state unresolved

theorem step_at_encoded (seeds : Prefix P) (judgment : P.Judgment)
    (state : Search.State P) (certificate : Tree P) (unresolved : state.found = none)
    (cursor : state.cursor = seeds.length + Encodable.encode certificate)
    (accepted : certificate.check judgment = true) :
    (step seeds judgment state).found = some certificate :=
  Search.Scheduled.step_at (candidate seeds) judgment state certificate unresolved
    (by simpa only [cursor] using candidate_at_encoded seeds certificate) accepted

theorem complete_from (seeds : Prefix P) (judgment : P.Judgment)
    (certificate : Tree P) (accepted : certificate.check judgment = true)
    (budget : Nat) (state : Search.State P)
    (before : state.cursor ≤ seeds.length + Encodable.encode certificate)
    (sufficient : seeds.length + Encodable.encode certificate < state.cursor + budget) :
    ∃ result, (run seeds judgment budget state).found = some result :=
  Search.Scheduled.complete_from_at (candidate seeds) judgment certificate accepted _
    (candidate_at_encoded seeds certificate) budget state before sufficient

def discoveryBound (prefixLength wireBits : Nat) : Nat := prefixLength + Tree.discoveryBound wireBits

theorem discover_within_wire_bound (seeds : Prefix P) (judgment : P.Judgment)
    (certificate : Tree P) (accepted : certificate.check judgment = true) :
    ∃ result,
      (search seeds judgment (discoveryBound seeds.length (Tree.wireSize certificate))).found = some result := by
  apply complete_from seeds judgment certificate accepted _ Search.initial (Nat.zero_le _)
  simpa only [Search.initial, discoveryBound, Nat.zero_add] using
    Nat.add_lt_add_left (Tree.code_lt_discoveryBound certificate) seeds.length

theorem stable_conclusion (seeds : Prefix P) (judgment : P.Judgment)
    (budget extra : Nat) (certificate : Tree P)
    (found : (search seeds judgment budget).found = some certificate) :
    search seeds judgment (budget + extra) = search seeds judgment budget :=
  (run_add seeds judgment budget extra Search.initial).trans
    (run_settled seeds judgment extra (search seeds judgment budget) certificate found)

end Mettapedia.OSLF.NativeTypes.Certificates.DeferredSeededSearch
