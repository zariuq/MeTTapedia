import Mettapedia.Languages.MeTTa.PeTTa.ValueOccurrences
import Mettapedia.Machines.ParameterizedBodyEntry

/-!
# One lexical parameter sequence for several lowerings

Fresh choices need no promised counter order. The sequence builder keeps
parameter positions and excludes prior identities. The renaming loop opens
an already elaborated lexical occurrence view; its independent source reads
the resulting parameter environment instead of rewriting the body.

The loop preserves PeTTa value occurrences, including shared values whose
syntax names an executable call. Binding-aware ABT representation, ownership
and the C fresh-identity allocator retain their native qualification controls.
This does not identify opaque quotation with first-order substitution.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.LexicalSourceOpening

section FreshSequence

variable {Name : Type}

/-- A finite allocator may refuse. No incomplete parameter sequence is published. -/
def generate (choose : List Name → Option Name) : Nat → List Name → Option (List Name)
  | 0, _ => some []
  | count + 1, used =>
      (choose used).bind fun next =>
        (generate choose count (next :: used)).map (next :: ·)

theorem generated_length (choose : List Name → Option Name) (count : Nat)
    (used parameters : List Name) (made : generate choose count used = some parameters) :
    parameters.length = count := by
  induction count generalizing used parameters with
  | zero =>
      have same : parameters = [] := by simpa [generate] using made.symm
      simp [same]
  | succ count ih =>
      cases selected : choose used with
      | none => simp [generate, selected] at made
      | some next =>
          cases later : generate choose count (next :: used) with
          | none => simp [generate, selected, later] at made
          | some rest =>
              have same : next :: rest = parameters := by simpa [generate, selected, later] using made
              subst parameters
              simpa using congrArg Nat.succ (ih (next :: used) rest later)

theorem generated_avoids (choose : List Name → Option Name)
    (fresh : ∀ used name, choose used = some name → name ∉ used) (count : Nat)
    (used parameters : List Name) (made : generate choose count used = some parameters) :
    ∀ name ∈ parameters, name ∉ used := by
  induction count generalizing used parameters with
  | zero =>
      have same : parameters = [] := by simpa [generate] using made.symm
      simp [same]
  | succ count ih =>
      cases selected : choose used with
      | none => simp [generate, selected] at made
      | some next =>
          cases later : generate choose count (next :: used) with
          | none => simp [generate, selected, later] at made
          | some rest =>
              have same : next :: rest = parameters := by simpa [generate, selected, later] using made
              subst parameters
              intro name member
              rcases List.mem_cons.mp member with same | tail
              · subst name
                exact fresh used next selected
              · intro present
                exact ih (next :: used) rest later name tail (List.mem_cons_of_mem _ present)

theorem generated_distinct (choose : List Name → Option Name)
    (fresh : ∀ used name, choose used = some name → name ∉ used) (count : Nat)
    (used parameters : List Name) (made : generate choose count used = some parameters) :
    parameters.Nodup := by
  induction count generalizing used parameters with
  | zero =>
      have same : parameters = [] := by simpa [generate] using made.symm
      simp [same]
  | succ count ih =>
      cases selected : choose used with
      | none => simp [generate, selected] at made
      | some next =>
          cases later : generate choose count (next :: used) with
          | none => simp [generate, selected, later] at made
          | some rest =>
              have same : next :: rest = parameters := by simpa [generate, selected, later] using made
              subst parameters
              simp only [List.nodup_cons]
              refine ⟨?_, ih (next :: used) rest later⟩
              intro member
              exact generated_avoids choose fresh count (next :: used) rest later
                next member (List.mem_cons_self ..)

theorem generation_split (choose : List Name → Option Name) (first later : Nat) (used : List Name) :
    generate choose (first + later) used =
      (generate choose first used).bind fun earlier =>
        (generate choose later (earlier.reverse ++ used)).map (earlier ++ ·) := by
  induction first generalizing used with
  | zero => simp [generate]
  | succ first ih =>
      cases selected : choose used with
      | none => simp [generate, selected, Nat.succ_add]
      | some next =>
          simp only [Nat.succ_add, generate, selected, Option.bind_some]
          rw [ih]
          cases generate choose first (next :: used) with
          | none => simp
          | some terms =>
              simp [List.reverse_cons, List.append_assoc, Option.map_map, Function.comp_def]

theorem generated_slot_entry {Value : Type} [DecidableEq Name]
    (choose : List Name → Option Name)
    (fresh : ∀ used name, choose used = some name → name ∉ used)
    (count : Nat) (used parameters : List Name)
    (made : generate choose count used = some parameters) (values : List Value) (locals : Nat)
    (arity : values.length = count) :
    ParameterizedBodyEntry.admitted parameters values = true ∧
      ParameterizedBodyEntry.source parameters values =
        ParameterizedBodyEntry.target parameters values locals := by
  have lengths : parameters.length = values.length :=
    (generated_length choose count used parameters made).trans arity.symm
  constructor
  · simp [ParameterizedBodyEntry.admitted, generated_distinct choose fresh count used parameters made, lengths]
  · exact ParameterizedBodyEntry.environments_refine _ _ _ lengths

theorem allocation_refusal (choose : List Name → Option Name) (count : Nat) (used : List Name)
    (refused : choose used = none) : generate choose (count + 1) used = none := by
  simp [generate, refused]

end FreshSequence

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.SubstitutionAlgebra (Subst subst)
open Mettapedia.Languages.MeTTa.PeTTa.ValueOccurrences

structure Rename where
  parameter : String
  fresh : String
  deriving DecidableEq, Repr

/-- Iterative source opening uses one ordered sequence, not parallel maps. -/
def openBody (steps : List Rename) (body : Atom) : Atom :=
  steps.foldl (fun term step => subst (renameTo step.parameter step.fresh) term) body

/-- The reference follows each source parameter into the remaining value
environment. Missing values remain the corresponding free variables. -/
def sourceEnvironment : List Rename → Subst → Subst
  | [], values => values
  | step :: rest, values =>
      let later := sourceEnvironment rest values
      fun name => if name = step.parameter then
        some ((later step.fresh).getD (.var step.fresh)) else later name

theorem step_environment (step : Rename) (values : Subst) :
    Mettapedia.Languages.MeTTa.SubstitutionAlgebra.comp
      (renameTo step.parameter step.fresh) values =
      fun name => if name = step.parameter then
        some ((values step.fresh).getD (.var step.fresh)) else values name := by
  funext name
  by_cases same : name = step.parameter
  · cases found : values step.fresh <;>
      simp [Mettapedia.Languages.MeTTa.SubstitutionAlgebra.comp, renameTo, subst, same, found]
  · simp [Mettapedia.Languages.MeTTa.SubstitutionAlgebra.comp, renameTo, same]

theorem opening_refines (program : Program) (steps : List Rename)
    (values : Subst) (body : Atom) :
    evalIn program values (openBody steps body) =
      evalIn program (sourceEnvironment steps values) body := by
  induction steps generalizing body with
  | nil => rfl
  | cons step rest ih =>
      simp only [openBody, List.foldl_cons]
      change evalIn program values
        (openBody rest (subst (renameTo step.parameter step.fresh) body)) = _
      rw [ih, evalIn_subst_of_renaming program _ _
        (renameTo_isRenaming step.parameter step.fresh) body, step_environment]
      rfl

theorem opening_split (first later : List Rename) (body : Atom) :
    openBody (first ++ later) body = openBody later (openBody first body) := by
  simp [openBody, List.foldl_append]

/-- An exact-arity inquiry inspects at most the requested prefix and one
terminal node, even when a source has many more parameters. -/
def scanArity {A : Type} : Nat → List A → Bool × Nat
  | 0, items => (items.isEmpty, 1)
  | _ + 1, [] => (false, 1)
  | count + 1, _ :: rest =>
      let next := scanArity count rest
      (next.1, next.2 + 1)

theorem arity_scan_refines {A : Type} (requested : Nat) (items : List A) :
    (scanArity requested items).1 = decide (items.length = requested) := by
  induction requested generalizing items with
  | zero => cases items <;> simp [scanArity]
  | succ requested ih => cases items <;> simp [scanArity, ih]

theorem arity_scan_reads_bounded {A : Type} (requested : Nat) (items : List A) :
    (scanArity requested items).2 ≤ requested + 1 := by
  induction requested generalizing items with
  | zero => simp [scanArity]
  | succ requested ih =>
      cases items with
      | nil => simp [scanArity]
      | cons first rest => simpa [scanArity] using Nat.add_le_add_right (ih rest) 1

def prepare (maximum requested : Nat) (steps : List Rename) (body : Atom) : Option Atom :=
  if requested = 0 ∨ maximum < requested ∨ !(scanArity requested steps).1 then none
  else some (openBody steps body)

theorem preparation_refines (program : Program) (maximum requested : Nat)
    (steps : List Rename) (values : Subst) (body : Atom) :
    (prepare maximum requested steps body).map (evalIn program values) =
      if requested = 0 ∨ maximum < requested ∨ steps.length ≠ requested then none
      else some (evalIn program (sourceEnvironment steps values) body) := by
  have negate : (!decide (steps.length = requested)) = true ↔ steps.length ≠ requested := by
    by_cases same : steps.length = requested <;> simp [same]
  simp only [prepare, arity_scan_refines, negate]
  split <;> simp [opening_refines]

theorem no_partial_parameter_prefix (maximum requested : Nat)
    (steps : List Rename) (body : Atom) (different : steps.length ≠ requested) :
    prepare maximum requested steps body = none := by
  simp [prepare, arity_scan_refines, different]

namespace Controls

def boundedChoice (maximum : Nat) (used : List Nat) : Option Nat :=
  (List.range maximum).find? fun name => !used.contains name

theorem bounded_choice_is_fresh (maximum : Nat) (used : List Nat) (name : Nat)
    (chosen : boundedChoice maximum used = some name) : name ∉ used := by
  have accepted := List.find?_some (p := fun candidate => !used.contains candidate) chosen
  simpa using accepted

theorem finite_choice_reaches_capacity :
    generate (boundedChoice 2) 2 [] = some [0, 1] := by decide

theorem finite_choice_refuses_unpublished_suffix :
    generate (boundedChoice 2) 3 [] = none := by decide

def body : Atom := .expression [.var "x", .var "z", .var "x"]
def callValue : Atom := .expression [.symbol "foo"]
def values : Subst := bindAt (bindAt Mettapedia.Languages.MeTTa.SubstitutionAlgebra.empty
  "a" callValue) "b" (.grounded (.int 7))

theorem parameter_values_are_shared_data :
    evalIn Examples.callsSymbols values
      (openBody [⟨"x", "a"⟩, ⟨"z", "b"⟩] body) =
      [.expression [callValue, .grounded (.int 7), callValue]] := by decide

theorem collapsed_parameters_change_observation :
    evalIn Examples.callsSymbols values
      (openBody [⟨"x", "a"⟩, ⟨"z", "a"⟩] body) ≠
      evalIn Examples.callsSymbols values
        (openBody [⟨"x", "a"⟩, ⟨"z", "b"⟩] body) := by decide

theorem incomplete_sequence_refused :
    prepare 64 2 [⟨"x", "a"⟩] body = none := by decide

theorem zero_and_oversized_refused :
    prepare 64 0 [] body = none ∧ prepare 64 65 [] body = none := by decide

end Controls
end Mettapedia.Machines.LexicalSourceOpening
