import Mettapedia.Machines.TIsa.Derivation.SymbolicAllocation
import Mettapedia.Machines.TIsa.Derivation.SymbolicBatch

/-!
# Allocating a population of matches at one snapshot

Members open in disjoint namespaces and receive consecutive, disjoint
blocks of output identities. These are reservations, not store
updates. In particular, a member cannot find another member's new
output using the batch's entry-snapshot guards.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.Derivation.SymbolicBatch

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open RuleSyntax (Program)
open RuleSyntax.OneFrame (Terms ext)
open RuleSyntax.JointFirings (OneMember Bag bagOf)
open RuleSyntax.SchematicRows.FreshNamespaces (opening fresh)
open SymbolicFiring (LiveWorld act)

variable {signature : LPSignature} {program : Program (Terms (Term signature))}

/-- The choices that a scheduler can make before it opens any rule.
A claimed collection is tested at the observation boundary separately. -/
structure Request (program : Program (Terms (Term signature))) where
  rule : RuleSyntax.Rule (Terms (Term signature))
  member : rule ∈ program
  taken : List ℕ
  read : List ℕ
  seen : List (Finset ℕ)
  takeWidth : rule.body.take.length = taken.length
  readWidth : rule.body.read.length = read.length
  collectWidth : rule.collect.length = seen.length

def Request.instantiate (before : LiveWorld signature) [DecidableEq signature.vars]
    (slots : signature.vars ≃ ℕ) (request : Request program) (index offset : ℕ) :
    OneMember (FirstOrder.action signature) ℕ program :=
  ⟨request.rule, request.member, opening slots (before.variableBound slots) index,
    ⟨request.taken, request.read, before.reserve offset request.rule.body.produce.length⟩, request.seen⟩

def outputWidth : List (Request program) → ℕ
  | [] => 0
  | first :: rest => first.rule.body.produce.length + outputWidth rest

variable (before : LiveWorld signature) [DecidableEq signature.vars] (slots : signature.vars ≃ ℕ)

def allocate : List (Request program) → ℕ → ℕ →
    List (ℕ × OneMember (FirstOrder.action signature) ℕ program)
  | [], _, _ => []
  | first :: rest, index, offset =>
    (index, first.instantiate before slots index offset) ::
      allocate rest (index + 1) (offset + first.rule.body.produce.length)

private theorem indices (requests : List (Request program)) (index offset : ℕ) :
    (allocate before slots requests index offset).map Prod.fst = List.range' index requests.length := by
  induction requests generalizing index offset with
  | nil => rfl
  | cons head tail ih =>
    rw [allocate, List.map_cons, ih, List.length_cons, List.range'_succ]

private theorem opened (requests : List (Request program)) (index offset : ℕ)
    (entry : ℕ × OneMember (FirstOrder.action signature) ℕ program)
    (inside : entry ∈ allocate before slots requests index offset) :
    entry.2.opening = opening slots (before.variableBound slots) entry.1 := by
  induction requests generalizing index offset with
  | nil => cases inside
  | cons head tail ih =>
    rcases List.mem_cons.mp inside with atHead | later
    · subst entry
      rfl
    · exact ih _ _ later

private theorem selection_widths (requests : List (Request program)) (index offset : ℕ)
    (entry : ℕ × OneMember (FirstOrder.action signature) ℕ program)
    (inside : entry ∈ allocate before slots requests index offset) :
    entry.2.rule.body.take.length = entry.2.selection.taken.length ∧
      entry.2.rule.body.read.length = entry.2.selection.read.length ∧
      entry.2.rule.body.produce.length = entry.2.selection.made.length ∧
      entry.2.rule.collect.length = entry.2.seen.length := by
  induction requests generalizing index offset with
  | nil => cases inside
  | cons head tail ih =>
    rcases List.mem_cons.mp inside with atHead | later
    · subst entry
      exact ⟨head.takeWidth, head.readWidth, (before.reserve_length _ _).symm, head.collectWidth⟩
    · exact ih _ _ later

def requestBatch (requests : List (Request program)) :
    Bag ℕ (ext (FirstOrder.action signature)) program before.state.frame :=
  bagOf (FirstOrder.action signature) ((allocate before slots requests 0 0).map Prod.snd)

theorem requestBatch_fresh (requests : List (Request program)) :
    (requestBatch before slots requests).Fresh (act signature) before.state := by
  have same : before.state = ⟨PUnit.unit, before.state.knowledge, before.state.present, before.state.label⟩ := by
    cases before.state with
    | mk frame knowledge present label => cases frame; rfl
  let family := allocate before slots requests 0 0
  have unique : (family.map Prod.fst).Nodup := by rw [indices]; exact List.nodup_range'
  have underBound : ∀ term, before.state.Mentions term → ∀ name ∈ term.freeVars,
      slots name < before.variableBound slots := fun term observed name used =>
    before.below_variableBound slots observed used
  change (⟨PUnit.unit, family.map Prod.snd⟩ :
    Bag ℕ (ext (FirstOrder.action signature)) program before.state.frame).Fresh (act signature) before.state
  have proof := fresh slots (before.variableBound slots) before.state.knowledge before.state.present before.state.label
    family unique (opened before slots requests 0 0) (fun term observed =>
      underBound term (same ▸ observed))
  exact same ▸ proof

private theorem made_block (requests : List (Request program)) (index offset : ℕ) :
    (allocate before slots requests index offset).flatMap (fun entry => entry.2.selection.made) =
      before.reserve offset (outputWidth requests) := by
  induction requests generalizing index offset with
  | nil => rfl
  | cons head tail ih =>
    rw [allocate, List.flatMap_cons, ih, outputWidth]
    simpa only [Request.instantiate, LiveWorld.reserve, ← Nat.add_assoc] using
      (List.range'_append_1 (s := before.next + offset) (m := head.rule.body.produce.length)
        (n := outputWidth tail))

theorem requestBatch_made (requests : List (Request program)) :
    (requestBatch before slots requests).selection.made = before.reserve 0 (outputWidth requests) := by
  simp only [requestBatch, bagOf, Bag.selection, List.flatMap_map]
  exact made_block before slots requests 0 0

theorem requestBatch_fits (requests : List (Request program))
    (takes : (requestBatch before slots requests).selection.taken.Nodup) :
    (requestBatch before slots requests).Fits (act signature) before.state := by
  refine ⟨requestBatch_fresh before slots requests, takes, ?_, ?_⟩
  · rw [requestBatch_made]
    exact before.reserve_distinct _ _
  · intro member inside
    change member ∈ (allocate before slots requests 0 0).map Prod.snd at inside
    obtain ⟨entry, listed, rfl⟩ := List.mem_map.mp inside
    exact selection_widths before slots requests 0 0 entry listed

theorem requestBatch_width (requests : List (Request program)) :
    (requestBatch before slots requests).members.length = requests.length := by
  change ((allocate before slots requests 0 0).map Prod.snd).length = requests.length
  have width := congrArg List.length (indices before slots requests 0 0)
  simpa only [List.length_map, List.length_range'] using width

theorem requestBatch_reserved (requests : List (Request program)) :
    let batch := requestBatch before slots requests
    batch.selection.made = before.reserve 0 batch.selection.made.length := by
  dsimp only
  have interval := requestBatch_made before slots requests
  have width := congrArg List.length interval
  rw [before.reserve_length] at width
  rw [width]
  exact interval

/-- Prepare the batch only after testing the global physical exclusion
of overlapping takes. This does not test that the values or guards match. -/
def prepareRequests (requests : List (Request program)) : Option (Prepared (program := program) before.state) :=
  let batch := requestBatch before slots requests
  if positive : batch.members.length ≠ 0 then
    if takes : batch.selection.taken.Nodup then
      some ⟨batch, fun empty => positive (congrArg List.length empty), requestBatch_fits before slots requests takes⟩
    else none
  else none

theorem prepareRequests_some_iff (requests : List (Request program)) :
    (prepareRequests before slots requests).isSome = true ↔
      requests ≠ [] ∧ (requestBatch before slots requests).selection.taken.Nodup := by
  by_cases nonempty : requests = []
  · simp [prepareRequests, nonempty, requestBatch_width]
  · have width : (requestBatch before slots requests).members.length ≠ 0 := by
      intro zero
      rw [requestBatch_width] at zero
      exact nonempty (List.eq_nil_of_length_eq_zero zero)
    by_cases takes : (requestBatch before slots requests).selection.taken.Nodup <;>
      simp [prepareRequests, width, takes, nonempty]

/-- The batch's only publication uses the same occurrence ledger as the
one-member machine. No intermediate reservation changes what is present. -/
def publishRequests (requests : List (Request program)) : LiveWorld signature :=
  let batch := requestBatch before slots requests
  before.commitDelta batch.selection (batch.result (act signature) before.state) rfl (requestBatch_reserved before slots requests)

theorem prepared_batch (requests : List (Request program)) {ready : Prepared (program := program) before.state}
    (computed : prepareRequests before slots requests = some ready) :
    ready.batch = requestBatch before slots requests := by
  unfold prepareRequests at computed
  dsimp only at computed
  split at computed
  · split at computed
    · exact congrArg Prepared.batch (Option.some.inj computed).symm
    · cases computed
  · cases computed

variable [DecidableEq signature.constants] [DecidableEq signature.functionSymbols]

def advanceRequests (reading : Reading) (requests : List (Request program)) :
    Option (Subst signature × LiveWorld signature) := do
  let ready ← prepareRequests before slots requests
  let (answer, _) ← evaluate reading ready
  pure (answer, publishRequests before slots requests)

theorem advanceRequests_exact (reading : Reading) (requests : List (Request program))
    (answer : Subst signature) (after : LiveWorld signature) :
    advanceRequests before slots reading requests = some (answer, after) ↔
      ∃ ready, prepareRequests before slots requests = some ready ∧
        Admits reading ready ∧ unifyTotal (ready.batch.information (act signature) before.state) = some answer ∧
        after = publishRequests before slots requests := by
  constructor
  · intro executed
    obtain ⟨ready, prepared, checked⟩ := Option.bind_eq_some_iff.mp executed
    obtain ⟨⟨solution, state⟩, computed, published⟩ := Option.bind_eq_some_iff.mp checked
    change some (solution, publishRequests before slots requests) = some (answer, after) at published
    obtain ⟨rfl, sameWorld⟩ := Prod.mk.inj (Option.some.inj published)
    obtain ⟨unified, licensed, _⟩ := (evaluate_exact reading ready solution state).mp computed
    exact ⟨ready, prepared, licensed, unified, sameWorld.symm⟩
  · rintro ⟨ready, prepared, licensed, unified, rfl⟩
    have computed := (evaluate_exact reading ready answer _).mpr ⟨unified, licensed, rfl⟩
    simp [advanceRequests, prepared, computed]

end Mettapedia.Machines.TIsa.Derivation.SymbolicBatch
