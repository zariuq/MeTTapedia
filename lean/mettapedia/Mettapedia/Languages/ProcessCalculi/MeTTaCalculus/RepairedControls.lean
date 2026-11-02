import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Repaired
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Controls

/-!
# Positive and separating controls for the repaired store interpretation

The comparison starts from L. G. Meredith's *The MeTTa calculus*. Requests
here use the proposed explicit resource modes while value constraints use
the existing first-order substitution action. The read binds both its local
pattern and a caller variable; two equal data values retain two identities.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Repaired.Controls

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Logic.LP
open ConstraintMultisetRewriting.Controls (signature)

abbrev Atom := Mettapedia.Logic.LP.Term signature
abbrev A := FirstOrder.action signature

def answer : Subst signature := fun _ => .const 7
def initial : Configuration (Row Unit Atom) Nat := ⟨[], {0, 1, 2}⟩
def label (operation : Operation) (occurrence : Nat) : Row Unit Atom :=
  if occurrence = 0 then request operation () (.var 1)
  else if occurrence = 3 then reply operation () (.var 0)
  else data () (.const 7)

def readSelection : Selection Nat := ⟨[0], [1], [3]⟩
def eraseSelection : Selection Nat := ⟨[0, 1], [], [3]⟩

theorem read_is_admitted :
    readSelection.Valid (action A) (label .read) (operationRule .read () (.var 0)) initial := by
  refine ⟨by decide, by decide, rfl, rfl, rfl, ?_, ⟨answer, ?_⟩, ?_⟩
  · refine ⟨by decide, by decide, by decide, by decide, ?_⟩
    intro query member; cases member
  · intro equation member
    change equation ∈ [(request .read () (.var 0), request .read () (.var 1)),
      (data () (.var 0), data () (.const 7))] at member
    rcases List.mem_cons.mp member with first | last
    · subst equation; exact ⟨rfl, rfl⟩
    · have only := List.mem_singleton.mp last
      subst equation; exact ⟨rfl, rfl⟩
  · intro check member; cases member

theorem erase_is_admitted :
    eraseSelection.Valid (action A) (label .erase) (operationRule .erase () (.var 0)) initial := by
  refine ⟨by decide, by decide, rfl, rfl, rfl, ?_, ⟨answer, ?_⟩, ?_⟩
  · refine ⟨by decide, by decide, by decide, by decide, ?_⟩
    intro query member; cases member
  · intro equation member
    change equation ∈ [(request .erase () (.var 0), request .erase () (.var 1)),
      (data () (.var 0), data () (.const 7))] at member
    rcases List.mem_cons.mp member with first | last
    · subst equation; exact ⟨rfl, rfl⟩
    · have only := List.mem_singleton.mp last
      subst equation; exact ⟨rfl, rfl⟩
  · intro check member; cases member

def afterRead := readSelection.result (label .read) (operationRule .read () (.var 0)) initial
def afterErase := eraseSelection.result (label .erase) (operationRule .erase () (.var 0)) initial

theorem read_keeps_both_equal_data_occurrences : afterRead.present = {1, 2, 3} := by decide +kernel
theorem erase_removes_one_and_keeps_the_other : afterErase.present = {2, 3} := by decide +kernel

theorem read_and_erase_have_different_observations : afterRead.present ≠ afterErase.present := by decide +kernel

theorem every_read_answer_binds_the_caller (candidate : Subst signature)
    (model : (action A).Models candidate afterRead.equations) :
    candidate 1 = .const 7 ∧ candidate 0 = .const 7 := by
  have linked := (model (request .read () (.var 0), request .read () (.var 1))
    (by change _ ∈ [_, _]; exact List.mem_cons_self)).2
  have found := (model (data () (.var 0), data () (.const 7))
    (by change _ ∈ [_, _]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _))).2
  change candidate 0 = candidate 1 at linked
  change candidate 0 = .const 7 at found
  exact ⟨linked.symm.trans found, found⟩

def insertLabel (occurrence : Nat) : Row Unit Atom :=
  if occurrence = 0 then request .insert () (.const 7)
  else if occurrence = 3 then data () (.var 0)
  else if occurrence = 4 then reply .insert () (.var 0)
  else data () (.const 7)
def insertSelection : Selection Nat := ⟨[0], [], [3, 4]⟩

theorem insertion_is_admitted :
    insertSelection.Valid (action A) insertLabel (operationRule .insert () (.var 0)) initial := by
  refine ⟨by decide, by decide, rfl, rfl, rfl, ?_, ⟨answer, ?_⟩, ?_⟩
  · refine ⟨by decide, by decide, by decide, by decide, ?_⟩
    intro query member; cases member
  · intro equation member
    change equation ∈ [(request .insert () (.var 0), request .insert () (.const 7))] at member
    have only := List.mem_singleton.mp member
    subst equation; exact ⟨rfl, rfl⟩
  · intro check member; cases member

theorem insertion_retains_old_data_and_makes_a_fresh_occurrence :
    (insertSelection.result insertLabel (operationRule .insert () (.var 0)) initial).present = {1, 2, 3, 4} := by
  decide +kernel

def onlyData : Configuration (Row Unit Atom) Nat := ⟨[], {1, 2}⟩

theorem two_passive_facts_do_not_start_an_operation (operation : Operation) :
    ¬ ∃ picked : Selection Nat,
      picked.Valid (action A) (label operation) (operationRule operation () (.var 0)) onlyData := by
  apply passive_data_do_not_supply_requests
  intro occurrence member
  have cases : occurrence = 1 ∨ occurrence = 2 := by simpa [onlyData] using member
  rcases cases with rfl | rfl <;> rfl

def queriesOnlyLabel (occurrence : Nat) : Row Unit Atom := request .read () (.var occurrence)

theorem two_queries_do_not_supply_a_data_witness :
    ¬ ∃ picked : Selection Nat,
      picked.Valid (action A) queriesOnlyLabel (operationRule .read () (.var 0))
        (⟨[], {0, 1}⟩ : Configuration (Row Unit Atom) Nat) := by
  apply requests_cannot_answer_an_empty_data_store
  intro occurrence _ same
  cases same

def incompatibleBefore : Configuration (Row Unit Atom) Nat :=
  ⟨[(request .read () (.var 1), request .read () (.const 0))], initial.present⟩

theorem an_incompatible_retained_binding_blocks_the_read :
    ¬ readSelection.Valid (action A) (label .read)
      (operationRule .read () (.var 0)) incompatibleBefore := by
  intro valid
  obtain ⟨_, _, _, candidate, old, requested, stored⟩ :=
    (read_admission_iff A (label .read) () (.var 0) (.var 1) (.const 7)
      incompatibleBefore 0 1 3 rfl rfl rfl).mp valid
  have prior := (old _ (List.mem_singleton_self _)).2
  change candidate 1 = .const 0 at prior
  change candidate 0 = candidate 1 at requested
  change candidate 0 = .const 7 at stored
  have impossible : (Term.const 0 : Atom) = .const 7 := prior.symm.trans (requested.symm.trans stored)
  cases impossible

def peerLabel (occurrence : Nat) : Row Unit Atom :=
  if occurrence = 0 then party () (.var 2)
  else if occurrence = 1 then party () (.const 7)
  else data () (.var 0)
def peerRule : RuleInstance (Row Unit Atom) := rendezvousRule () (.var 0) (.var 1) [data () (.var 0)]
def peerSelection : Selection Nat := ⟨[0, 1], [], [2]⟩
def peerBefore : Configuration (Row Unit Atom) Nat := ⟨[], {0, 1}⟩

theorem active_peers_really_rendezvous :
    peerSelection.Valid (action A) peerLabel peerRule peerBefore := by
  refine ⟨by decide, by decide, rfl, rfl, rfl, ?_, ⟨answer, ?_⟩, ?_⟩
  · refine ⟨by decide, by decide, by decide, by decide, ?_⟩
    intro query member; cases member
  · intro equation member
    change equation ∈ [(party () (.var 0), party () (.var 2)),
      (party () (.var 1), party () (.const 7)), (party () (.var 0), party () (.var 1))] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with first | second | third
    · subst equation; exact ⟨rfl, rfl⟩
    · subst equation; exact ⟨rfl, rfl⟩
    · subst equation; exact ⟨rfl, rfl⟩
  · intro check member; cases member

theorem rendezvous_links_both_locals_and_the_caller (candidate : Subst signature)
    (model : (action A).Models candidate (peerSelection.problem peerLabel peerRule peerBefore)) :
    candidate 0 = .const 7 ∧ candidate 1 = .const 7 ∧ candidate 2 = .const 7 := by
  have bound := (model (party () (.var 0), party () (.var 2))
    List.mem_cons_self).2
  have value := (model (party () (.var 1), party () (.const 7))
    (List.mem_cons_of_mem _ List.mem_cons_self)).2
  have together := rendezvous_uses_one_joint_solution A peerLabel () (.var 0) (.var 1)
    [data () (.var 0)] active_peers_really_rendezvous candidate model
  change candidate 0 = candidate 2 at bound
  change candidate 1 = .const 7 at value
  change candidate 0 = candidate 1 at together
  exact ⟨together.trans value, value, bound.symm.trans (together.trans value)⟩

theorem rendezvous_consumes_the_two_active_parties :
    (peerSelection.result peerLabel peerRule peerBefore).present = {2} := by decide +kernel

def reversedPeerSelection : Selection Nat := ⟨[1, 0], [], [2]⟩

theorem the_opposite_peer_selection_is_also_admitted :
    reversedPeerSelection.Valid (action A) peerLabel peerRule peerBefore := by
  refine ⟨by decide, by decide, rfl, rfl, rfl, ?_, ⟨answer, ?_⟩, ?_⟩
  · refine ⟨by decide, by decide, by decide, by decide, ?_⟩
    intro query member; cases member
  · intro equation member
    change equation ∈ [(party () (.var 0), party () (.const 7)),
      (party () (.var 1), party () (.var 2)), (party () (.var 0), party () (.var 1))] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with first | second | third
    · subst equation; exact ⟨rfl, rfl⟩
    · subst equation; exact ⟨rfl, rfl⟩
    · subst equation; exact ⟨rfl, rfl⟩
  · intro check member; cases member

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Repaired.Controls
