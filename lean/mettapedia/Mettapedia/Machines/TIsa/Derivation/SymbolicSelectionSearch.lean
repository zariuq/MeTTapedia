import Mettapedia.Machines.TIsa.Derivation.SymbolicFiring
import Mettapedia.Machines.TIsa.Derivation.AnswerTable

/-!
# Searching physical selections at a symbolic opening

Enumerate ordered take and read ports of the actual firing. Takes are
distinct and not read; read ports may share occurrences. Outputs and
the fresh opening are already allocated. The enumerator neither
assumes ground labels nor tests a guard against a partial selection.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.Derivation.SymbolicFiring

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open RuleSyntax (Program)
open RuleSyntax.OneFrame (Terms ext)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled)

def tuples {O : Type*} (available : List O) (arity : ℕ) : List (List O) :=
  AnswerTable.choices (fun _ : Unit => available) (List.replicate arity ())

theorem mem_tuples {O : Type*} (available : List O) (arity : ℕ) (picked : List O) :
    picked ∈ tuples available arity ↔ picked.length = arity ∧ ∀ o ∈ picked, o ∈ available := by
  rw [tuples, AnswerTable.mem_choices]
  induction arity generalizing picked with
  | zero => cases picked <;> simp
  | succ arity ih =>
    cases picked with
    | nil => simp [List.replicate_succ]
    | cons occurrence rest =>
      simp [List.replicate_succ, ih, and_left_comm]

variable {O : Type} [DecidableEq O]

def portChoices (available : List O) (takeCount readCount : ℕ) : List (List O × List O) :=
  ((tuples available takeCount).filter fun chosen => decide chosen.Nodup).flatMap fun taken =>
    (tuples (available.filter fun occurrence => !(taken.contains occurrence)) readCount).map
      fun read => (taken, read)

theorem portChoices_iff (available : List O) (takeCount readCount : ℕ) (taken read : List O) :
    (taken, read) ∈ portChoices available takeCount readCount ↔
      taken.length = takeCount ∧ read.length = readCount ∧ taken.Nodup ∧
      (∀ occurrence ∈ taken, occurrence ∈ available) ∧
      (∀ occurrence ∈ read, occurrence ∈ available ∧ occurrence ∉ taken) := by
  constructor
  · intro published
    unfold portChoices at published
    obtain ⟨chosen, availableTake, paths⟩ := List.mem_flatMap.mp published
    obtain ⟨observed, availableRead, same⟩ := List.mem_map.mp paths
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
    obtain ⟨takeTuple, unique⟩ := List.mem_filter.mp availableTake
    obtain ⟨takeLength, takeMember⟩ := (mem_tuples _ _ _).mp takeTuple
    obtain ⟨readLength, readMember⟩ := (mem_tuples _ _ _).mp availableRead
    refine ⟨takeLength, readLength, of_decide_eq_true unique, takeMember, ?_⟩
    intro occurrence reads
    simpa using List.mem_filter.mp (readMember occurrence reads)
  · rintro ⟨takeLength, readLength, unique, takeMember, readMember⟩
    apply List.mem_flatMap.mpr
    refine ⟨taken, List.mem_filter.mpr ⟨(mem_tuples _ _ _).mpr ⟨takeLength, takeMember⟩, by simp [unique]⟩, ?_⟩
    apply List.mem_map.mpr
    refine ⟨read, (mem_tuples _ _ _).mpr ⟨readLength, ?_⟩, rfl⟩
    intro occurrence found
    have covered := readMember occurrence found
    exact List.mem_filter.mpr ⟨covered.1, by simpa using covered.2⟩

variable {signature : LPSignature} {program : Program (Terms (Term signature))}

/-- The parts of a firing fixed before assigning take and read ports.
No solution of the equations or of the guard is assumed. -/
structure PreparedOpening (before : World signature O) where
  template : RuleSyntax.Firing O (ext (FirstOrder.action signature)) program before.frame
  fresh : template.Fresh (act signature) before
  madeDistinct : template.selection.made.Nodup
  madeFresh : Disjoint template.selection.made.toFinset before.present
  makes : template.rule.body.produce.length = template.selection.made.length
  collects : template.rule.collect.length = template.seen.length

namespace PreparedOpening

variable {before : World signature O} (prepared : PreparedOpening (program := program) before)

def withPorts (taken read : List O) :
    RuleSyntax.Firing O (ext (FirstOrder.action signature)) program before.frame :=
  { prepared.template with selection := ⟨taken, read, prepared.template.selection.made⟩ }

abbrev ports (available : List O) :=
  portChoices available prepared.template.rule.body.take.length prepared.template.rule.body.read.length

def selected (available : List O) (visible : available.toFinset = before.present)
    (choice : {p // p ∈ prepared.ports available}) : Selection (program := program) before where
  firing := prepared.withPorts choice.val.1 choice.val.2
  shaped := by
    have listed : (choice.val.1, choice.val.2) ∈ prepared.ports available := choice.property
    obtain ⟨takeLength, readLength, unique, _, _⟩ := (portChoices_iff available _ _ _ _).mp listed
    exact ⟨prepared.fresh, unique, prepared.madeDistinct, takeLength.symm, readLength.symm,
      prepared.makes, prepared.collects⟩
  enabled := by
    have listed : (choice.val.1, choice.val.2) ∈ prepared.ports available := choice.property
    obtain ⟨_, _, _, allTakes, allReads⟩ := (portChoices_iff available _ _ _ _).mp listed
    refine ⟨?_, ?_, ?_, prepared.madeFresh, ?_⟩
    · intro occurrence found
      rw [← visible]
      exact List.mem_toFinset.mpr (allTakes _ (List.mem_toFinset.mp found))
    · intro occurrence found
      rw [← visible]
      exact List.mem_toFinset.mpr (allReads _ (List.mem_toFinset.mp found)).1
    · apply Finset.disjoint_left.mpr
      intro occurrence take read
      exact (allReads _ (List.mem_toFinset.mp read)).2 (List.mem_toFinset.mp take)
    · intro query found
      exact (List.not_mem_nil found).elim

def enumerate (available : List O) (visible : available.toFinset = before.present) :
    List (Selection (program := program) before) :=
  (prepared.ports available).attach.map (prepared.selected available visible)

@[simp] theorem selected_firing (available : List O) (visible : available.toFinset = before.present)
    (choice : {p // p ∈ prepared.ports available}) :
    (prepared.selected available visible choice).firing = prepared.withPorts choice.val.1 choice.val.2 := rfl

/-- Every admitted firing with this opening and these allocated outputs
has its take/read choice in the finite search. In particular, this
direction does not assume a ground normal form of the store. -/
theorem admitted_ports_listed (available : List O) (visible : available.toFinset = before.present)
    (taken read : List O) (seen : List (Finset O))
    (admitted : ({prepared.withPorts taken read with seen := seen}).Admits (act signature) before) :
    (taken, read) ∈ prepared.ports available := by
  have shape := admitted.1
  have enabled := admitted.2.1
  apply (portChoices_iff available _ _ taken read).mpr
  refine ⟨shape.2.2.2.1.symm, shape.2.2.2.2.1.symm, shape.2.1, ?_, ?_⟩
  · intro occurrence chosen
    apply List.mem_toFinset.mp
    rw [visible]
    exact enabled.taken_subset (List.mem_toFinset.mpr chosen)
  · intro occurrence chosen
    have kept := List.mem_toFinset.mpr chosen
    refine ⟨List.mem_toFinset.mp (visible.symm ▸ enabled.kept_subset kept), ?_⟩
    intro alsoTaken
    exact Finset.disjoint_left.mp enabled.apart (List.mem_toFinset.mpr alsoTaken) kept

variable [DecidableEq signature.vars] [DecidableEq signature.constants] [DecidableEq signature.functionSymbols]

def firingsAt (available : List O) (visible : available.toFinset = before.present) :
    List (Subst signature × Selection (program := program) before) :=
  (prepared.enumerate available visible).filterMap evaluateInferred

theorem firingsAt_sound (available : List O) (visible : available.toFinset = before.present)
    {answer : Subst signature} {chosen : Selection (program := program) before}
    (member : (answer, chosen) ∈ prepared.firingsAt available visible) :
    Admitted chosen ∧ unifyTotal (problem chosen) = some answer := by
  obtain ⟨_, _, found⟩ := List.mem_filterMap.mp member
  obtain ⟨proposal, allowed⟩ := (evaluateInferred_exact _ _ _).mp found
  exact ⟨allowed, proposed_principal_solution proposal⟩

/-- The finite evaluator misses no firing at the supplied opening and
output allocation, even when the collect sets were not known on entry. -/
theorem firingsAt_complete (available : List O) (visible : available.toFinset = before.present)
    (taken read : List O) (seen : List (Finset O))
    (admitted : ({prepared.withPorts taken read with seen := seen}).Admits (act signature) before) :
    ∃ answer chosen, (answer, chosen) ∈ prepared.firingsAt available visible ∧
      chosen.firing = {prepared.withPorts taken read with seen := seen} := by
  have listed := prepared.admitted_ports_listed available visible taken read seen admitted
  let choice : { p // p ∈ prepared.ports available } := ⟨(taken, read), listed⟩
  let seed := prepared.selected available visible choice
  have width : seed.firing.rule.collect.length = seen.length := admitted.1.2.2.2.2.2.2
  let chosen := seed.withSeen seen width
  have sameFiring : chosen.firing = {prepared.withPorts taken read with seen := seen} := rfl
  have ready : Admitted chosen := admitted
  obtain ⟨answer, proposed⟩ := proposed_collections_include_every_admitted_choice seed seen width ready
  refine ⟨answer, chosen, List.mem_filterMap.mpr ⟨seed, ?_, (evaluateInferred_exact _ _ _).mpr ⟨proposed, ready⟩⟩,
    sameFiring⟩
  exact List.mem_map.mpr ⟨choice, List.mem_attach _ _, rfl⟩

end PreparedOpening

theorem a_read_may_share_but_a_take_cannot :
    (([] : List ℕ), [7, 7]) ∈ portChoices [7] 0 2 ∧
      (([7] : List ℕ), [7]) ∉ portChoices [7] 1 1 := by
  simp [portChoices_iff]

end Mettapedia.Machines.TIsa.Derivation.SymbolicFiring
