import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.EquationPlans

/-!
# Bounded sharing of prepared equations

The cache folds repeated entry requests to one plan. Dynamic scopes
are arguments to the plan, so another opening needs no new entry.
Weighted admission accounts for both the control templates and their
operands. The program's authored generators supply a static budget.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.EquationCache

open Elaboration
open EquationPlans (Cached)

variable {D : Discipline MSig [] ()}

abbrev Entry (program : Program mkeys [] () D.Ty) (budget : Nat) :=
  (head : PreparedCall.Head) × Cached program head budget

def size {program : Program mkeys [] () D.Ty} {budget : Nat}
    (entries : List (Entry program budget)) : Nat :=
  (entries.map fun entry => entry.2.body.size).sum

structure Table (program : Program mkeys [] () D.Ty) (budget : Nat) where
  entries : List (Entry program budget)
  used : Nat
  exactSize : size entries = used
  bounded : used ≤ budget
  unique : (entries.map Sigma.fst).Nodup

variable {program : Program mkeys [] () D.Ty} {budget : Nat}

def empty : Table program budget :=
  ⟨[], 0, rfl, Nat.zero_le _, List.nodup_nil⟩

def lookup (head : PreparedCall.Head) : List (Entry program budget) → Option (Cached program head budget)
  | [] => none
  | entry :: later =>
    if same : entry.1 = head then some (same ▸ entry.2) else lookup head later

theorem lookup_none (head : PreparedCall.Head) (entries : List (Entry program budget)) :
    lookup head entries = none ↔ head ∉ entries.map Sigma.fst := by
  induction entries with
  | nil => simp [lookup]
  | cons entry later ih =>
    by_cases same : entry.1 = head
    · simp [lookup, same]
    · simp [lookup, same, Ne.symm same, ih]

def request (cache : Table program budget) (head : PreparedCall.Head) : Table program budget :=
  if absent : (lookup head cache.entries).isNone then
    match EquationPlans.compile (D := D) program head budget with
    | none => cache
    | some candidate =>
      if room : cache.used + candidate.body.size ≤ budget then
        ⟨⟨head, candidate⟩ :: cache.entries, cache.used + candidate.body.size,
          by simp [size, ← cache.exactSize, Nat.add_comm],
          room, List.nodup_cons.mpr ⟨(lookup_none _ _).mp (by simpa using absent), cache.unique⟩⟩
      else cache
  else cache

theorem request_uses_existing (cache : Table program budget) (head : PreparedCall.Head)
    {selected : Cached program head budget} (found : lookup head cache.entries = some selected) :
    request cache head = cache := by simp [request, found]

theorem request_folds (cache : Table program budget) (head : PreparedCall.Head) :
    request (request cache head) head = request cache head := by
  cases found : lookup head cache.entries with
  | some selected => rw [request_uses_existing cache head found, request_uses_existing cache head found]
  | none =>
    cases built : EquationPlans.compile (D := D) program head budget with
    | none => simp [request, found, built]
    | some candidate =>
      by_cases fits : cache.used + candidate.body.size ≤ budget
      · have installed : lookup head (request cache head).entries = some candidate := by
          simp [request, found, built, fits, lookup]
        exact request_uses_existing (request cache head) head installed
      · simp [request, found, built, fits]

def authoredBudget (program : Program mkeys [] () D.Ty) : Nat :=
  (program.equations.map fun equation =>
    match BindingPlans.recognize equation.rhs with
    | none => 0
    | some admitted => 3 * admitted.2.size + 1).sum

def prepare (program : Program mkeys [] () D.Ty) (heads : List PreparedCall.Head) :
    Table program (authoredBudget (D := D) program) :=
  heads.foldl request empty

theorem prepare_size (program : Program mkeys [] () D.Ty) (heads : List PreparedCall.Head) :
    size (prepare program heads).entries ≤ authoredBudget (D := D) program := by
  rw [(prepare program heads).exactSize]
  exact (prepare program heads).bounded

theorem prepare_distinct (program : Program mkeys [] () D.Ty) (heads : List PreparedCall.Head) :
    ((prepare program heads).entries.map Sigma.fst).Nodup := (prepare program heads).unique

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.EquationCache
