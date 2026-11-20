import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreOrderedBags

/-!
# Outcome licences for the positive set-store disciplines

The disciplines below use the existing occurrence admission predicates and
actual serial executions. The comparison is for ground, range-restricted,
non-consuming propagation. It selects no language default and makes no trace,
work-budget, or general shared-unknown equivalence claim.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreSyntax

open Mettapedia.Logic.LP
open OneFrame (Terms frames ext)
open JointFirings
open LogicOverTheStep.StepSpan (Succ)

variable {signature : LPSignature} [DecidableEq signature.vars]
  [DecidableEq signature.constants] [DecidableEq signature.functionSymbols]
  {P : Program (Terms (Term signature))}

inductive Discipline where
  | one | round | synchronous | joint | every | maximal | unique
  deriving DecidableEq

def SerialRound (rows : Finset (Term signature)) (bag : SetStore.Candidate P) : Prop :=
  bag.AdmitsOwn X (SetStore.represent rows) ∧
    ∃ members : List (OneMember (FirstOrder.action signature) (Term signature × ℕ) P),
      bag = bagOf (FirstOrder.action signature) members ∧
        ∀ later, members.Perm later →
          Relation.ReflTransGen (Succ (step X (Term signature × ℕ) E P).toStep) (SetStore.represent rows)
            ((bagOf (FirstOrder.action signature) later).result X (SetStore.represent rows)) ∧
          ((bagOf (FirstOrder.action signature) later).result X (SetStore.represent rows)).present =
            (bag.result X (SetStore.represent rows)).present ∧
          ((bagOf (FirstOrder.action signature) later).result X (SetStore.represent rows)).label =
            (bag.result X (SetStore.represent rows)).label ∧
          ((bagOf (FirstOrder.action signature) later).result X (SetStore.represent rows)).knowledge.Perm
            (bag.result X (SetStore.represent rows)).knowledge

def Allowed (discipline : Discipline) (rows : Finset (Term signature)) (bag : SetStore.Candidate P) : Prop :=
  match discipline with
  | .one => bag.members.length = 1
  | .round => SerialRound rows bag
  | .synchronous => bag.AdmitsSnapshot X (SetStore.represent rows)
  | .joint => bag.Admits X (SetStore.represent rows)
  | .every => bag.AdmitsEveryBy X (SetStore.represent rows) SymmetricMatches.identity Set.univ
  | .maximal => bag.AdmitsMaximal X (SetStore.represent rows)
  | .unique => bag.AdmitsUniqueBy X (SetStore.represent rows) SymmetricMatches.identity Set.univ

/-- In the non-consuming fragment, entry-wise enabling is exactly joint enabling. -/
theorem snapshot_iff_joint_of_no_takes (rows : Finset (Term signature))
    (bag : SetStore.Candidate P) (noTake : ∀ rule ∈ P, rule.body.take = []) :
    bag.AdmitsSnapshot X (SetStore.represent rows) ↔ bag.Admits X (SetStore.represent rows) := by
  constructor
  · intro snapshot
    have empty : bag.selection.taken = [] := by
      apply List.flatMap_eq_nil_iff.mpr
      intro member inside
      have lengths := (snapshot.1.2.2.2 member inside).1
      rw [noTake member.rule member.member, List.length_nil] at lengths
      exact List.eq_nil_of_length_eq_zero lengths.symm
    refine ⟨snapshot.1, ⟨?_, ?_, ?_, ?_, ?_⟩, snapshot.2.2.1, snapshot.2.2.2⟩
    · simp [Selection.commit, empty]
    · intro o read
      obtain ⟨member, inside, selected⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp read)
      exact (snapshot.2.1 member inside).kept_subset (List.mem_toFinset.mpr selected)
    · simp [Selection.commit, empty]
    · apply Finset.disjoint_left.mpr
      intro o made present
      obtain ⟨member, inside, selected⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp made)
      exact Finset.disjoint_left.mp (snapshot.2.1 member inside).fresh (List.mem_toFinset.mpr selected) present
    · intro query inside
      simp [Selection.commit] at inside
  · exact Bag.admitsSnapshot_of_admits X

def DisciplinedStep (discipline : Discipline) (timing : SetStore.AskTiming)
    (P : Program (Terms (Term signature))) (rows after : Finset (Term signature)) : Prop :=
  ∃ bag : SetStore.Candidate P, bag.members ≠ [] ∧ SetStore.admitted timing rows bag ∧ Allowed discipline rows bag ∧
    ∃ answer, unifyTotal (bag.information X (SetStore.represent rows)) = some answer ∧
      after = SetStore.setResult rows bag answer ∧ ¬ SetStore.SameRows rows after

theorem disciplined_is_step {discipline : Discipline} {timing : SetStore.AskTiming}
    {rows after : Finset (Term signature)} (yes : DisciplinedStep discipline timing P rows after) :
    SetStore.Step timing P rows after := by
  obtain ⟨bag, nonempty, admitted, _, answer, accepted, result, changed⟩ := yes
  exact ⟨bag, nonempty, admitted, answer, accepted, result, changed⟩

theorem serialRound_of_own (rows : Finset (Term signature)) (pure : ∀ rule ∈ P, Propagates rule)
    (bag : SetStore.Candidate P) (own : bag.AdmitsOwn X (SetStore.represent rows)) : SerialRound rows bag := by
  obtain ⟨⟨⟩, members⟩ := bag
  refine ⟨own, members, rfl, fun later perm => ?_⟩
  exact any_order (FirstOrder.action signature) (fun member _ => (pure member.rule member.member).positive) own perm

def Determinate (rows : Finset (Term signature)) : Prop :=
  ∀ first second : F (P := P), first.Admits X (SetStore.represent rows) →
    second.Admits X (SetStore.represent rows) → SymmetricMatches.identity.key first = SymmetricMatches.identity.key second

theorem unique_of_determinate (rows : Finset (Term signature)) (bag : SetStore.Candidate P)
    (every : bag.AdmitsEveryBy X (SetStore.represent rows) SymmetricMatches.identity Set.univ)
    (nonempty : bag.members ≠ []) (determinate : Determinate (P := P) rows) :
    bag.AdmitsUniqueBy X (SetStore.represent rows) SymmetricMatches.identity Set.univ := by
  refine ⟨every, ?_⟩
  obtain ⟨⟨⟩, members⟩ := bag
  cases members with
  | nil => exact False.elim (nonempty rfl)
  | cons first rest =>
    cases rest with
    | nil => rfl
    | cons second later =>
      have firstYes := Bag.admits_member X (fun _ _ => ⟨Subst.id signature⟩) every.1 List.mem_cons_self
      have secondYes := Bag.admits_member X (fun _ _ => ⟨Subst.id signature⟩) every.1
        (List.mem_cons_of_mem _ List.mem_cons_self)
      have equal := determinate first.firing second.firing firstYes secondYes
      have distinct := every.2.2.1
      change (SymmetricMatches.identity.key first.firing :: SymmetricMatches.identity.key second.firing ::
        later.map (fun m => SymmetricMatches.identity.key m.firing)).Nodup at distinct
      exact False.elim ((List.nodup_cons.mp distinct).1 (List.mem_cons.mpr (Or.inl equal)))

theorem single_progress_witness (timing : SetStore.AskTiming) (rows : Finset (Term signature)) (ground : GroundRows rows)
    (match_ : GroundMatch P) (enabled : (consequence match_).read ⊆ rows)
    (outside : ¬ (consequence match_).made ⊆ rows) :
    ∃ answer, unifyTotal ((Bag.single match_.firing).information X (SetStore.represent rows)) = some answer ∧
      (Bag.single match_.firing).members ≠ [] ∧ SetStore.admitted timing rows (Bag.single match_.firing) ∧
        ¬ SetStore.SameRows rows (SetStore.setResult rows (Bag.single match_.firing) answer) := by
  have yes := firing_admitted match_ rows ground enabled
  have bagYes := (Bag.single_admits_iff X _ match_.firing).mpr yes
  obtain ⟨answer, accepted⟩ := (FirstOrder.accepted_iff_consistent (problem match_)).mpr
    ⟨match_.assignment, problem_solved match_⟩
  refine ⟨answer, ?_, List.cons_ne_nil _ _, ?_, ?_⟩
  · simp only [Bag.single, Bag.information_single, Member.firing_ofFiring]
    rwa [firing_information]
  · cases timing with
    | afterTells => exact bagYes
    | beforeTells =>
      apply (Bag.beforeTells_iff_of_no_tells X _ (Bag.single match_.firing) ?_).mpr bagYes
      intro member inside
      obtain rfl := List.mem_singleton.mp inside
      change match_.rule.body.tell.map _ = []
      rw [match_.propagates.noTell, List.map_nil]
  · intro same
    have equal := sameRows_ground_eq ground same
    rw [lifted_result match_ rows ground answer (unifyTotal_sound _ _ accepted)] at equal
    exact outside (Finset.union_eq_left.mp equal)

theorem step_with_witness (discipline : Discipline) (timing : SetStore.AskTiming)
    (rows : Finset (Term signature)) (bag : SetStore.Candidate P) (allowed : Allowed discipline rows bag)
    (witness : ∃ answer, unifyTotal (bag.information X (SetStore.represent rows)) = some answer ∧
      bag.members ≠ [] ∧ SetStore.admitted timing rows bag ∧
        ¬ SetStore.SameRows rows (SetStore.setResult rows bag answer)) :
    ∃ after, DisciplinedStep discipline timing P rows after := by
  obtain ⟨answer, accepted, nonempty, admitted, changed⟩ := witness
  exact ⟨_, bag, nonempty, admitted, allowed, answer, accepted, rfl, changed⟩

theorem discipline_progress (slots : signature.vars ≃ ℕ) (discipline : Discipline) (timing : SetStore.AskTiming)
    (rows : Finset (Term signature)) (ground : GroundRows rows) (pure : ∀ rule ∈ P, Propagates rule)
    (rules : List (Rule (Terms (Term signature)))) (covers : ∀ rule ∈ P, rule ∈ rules)
    (uniquePolicy : discipline = .unique → Determinate (P := P) rows)
    (notClosed : ¬ SetStoreClosure.Closed (consequence (P := P)) rows) :
    ∃ after, DisciplinedStep discipline timing P rows after := by
  have small : ∃ match_ : GroundMatch P, (consequence match_).read ⊆ rows ∧ ¬ (consequence match_).made ⊆ rows := by
    obtain ⟨match_, failure⟩ := Classical.not_forall.mp notClosed
    exact ⟨match_, Classical.not_imp.mp failure⟩
  obtain ⟨match_, enabled, outside⟩ := small
  have singleWitness := single_progress_witness timing rows ground match_ enabled outside
  have singleYes := (Bag.single_admits_iff X _ match_.firing).mpr (firing_admitted match_ rows ground enabled)
  have singleOwn := (Bag.admitsOwn_single X (SetStore.represent rows) (Member.ofFiring match_.firing)).mpr
    (firing_admitted match_ rows ground enabled)
  cases discipline with
  | one => exact step_with_witness .one timing rows (Bag.single match_.firing) rfl singleWitness
  | round => exact step_with_witness .round timing rows _ (serialRound_of_own rows pure _ singleOwn) singleWitness
  | synchronous => exact step_with_witness .synchronous timing rows _ (Bag.admitsSnapshot_of_admits X singleYes) singleWitness
  | joint => exact step_with_witness .joint timing rows _ singleYes singleWitness
  | every =>
    obtain ⟨bag, every⟩ := exists_every_bag slots rows ground pure rules covers
    exact step_with_witness .every timing rows bag every
      (complete_progress_witness timing rows ground pure bag every.1 every.2.2.2 notClosed)
  | maximal =>
    obtain ⟨bag, own, maximal, complete⟩ := exists_maximal_complete_bag slots rows ground pure rules covers
    exact step_with_witness .maximal timing rows bag maximal
      (complete_progress_witness timing rows ground pure bag own complete notClosed)
  | unique =>
    obtain ⟨bag, every⟩ := exists_every_bag slots rows ground pure rules covers
    have witness := complete_progress_witness timing rows ground pure bag every.1 every.2.2.2 notClosed
    obtain ⟨answer, accepted, nonempty, admitted, changed⟩ := witness
    exact step_with_witness .unique timing rows bag (unique_of_determinate rows bag every nonempty (uniquePolicy rfl))
      ⟨answer, accepted, nonempty, admitted, changed⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreSyntax
