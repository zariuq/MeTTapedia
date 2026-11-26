import Mettapedia.Machines.TIsa.Derivation.SymbolicSchedules

/-!
# Two independent makes defeat a one-member maximal plan

Both rules have empty premises. There are exactly two distinct
matches at the empty snapshot. The scheduler can extend the first
one; it cannot extend the batch containing both.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.Derivation.SymbolicScheduleSearch.Examples

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open RuleSyntax.Controls (atoms)
open RuleSyntax.Examples (c)
open RuleSyntax.OneFrame (Terms)
open RuleSyntax.JointFirings (Bag)
open SymbolicFiring (act LiveWorld Rules World)
open SymbolicBatch (Request requestBatch)

private def emit (value : ℕ) : RuleSyntax.Rule (Terms (Term atoms)) :=
  ⟨PUnit.unit, ⟨[], [], [], [], [c value]⟩, []⟩

private def studio : Rules atoms := [emit 1, emit 2]

private def empty : World atoms ℕ := ⟨PUnit.unit, [], ∅, fun _ => c 0⟩
private def before : LiveWorld atoms := LiveWorld.initial empty [] rfl List.nodup_nil
private def slots : atoms.vars ≃ ℕ := Equiv.refl ℕ

private def request (value : ℕ) (authored : emit value ∈ studio.program) : Request studio.program :=
  ⟨emit value, authored, [], [], [], rfl, rfl, rfl⟩

private def two : List (Request studio.program) :=
  [request 1 List.mem_cons_self, request 2 (List.mem_cons_of_mem _ List.mem_cons_self)]

private def both := requestBatch before slots two

private theorem both_joint : both.Admits (act atoms) before.state := by
  refine ⟨SymbolicBatch.requestBatch_fits before slots two List.nodup_nil, ?_, ?_, ?_⟩
  · change Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Enabled
      (fun _ : ℕ => ()) ∅ ((⟨[], [], [1, 2]⟩ :
        Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Selection ℕ).commit (T := Unit))
    decide +kernel
  · refine ⟨PUnit.unit, Subst.id atoms, ?_⟩
    change Unifies (Subst.id atoms) []
    intro _ member
    cases member
  · intro point solution _ member inside
    cases point
    change member ∈ (SymbolicBatch.allocate before slots two 0 0).map Prod.snd at inside
    have nilChecks : (member.firing.opened (act atoms)).checks = [] := by
      rcases List.mem_cons.mp inside with rfl | later
      · rfl
      · obtain rfl := List.mem_singleton.mp later
        rfl
    have nilCollects : member.firing.collectOpened (act atoms) = [] := by
      rcases List.mem_cons.mp inside with rfl | later
      · rfl
      · obtain rfl := List.mem_singleton.mp later
        rfl
    exact ⟨fun _ found => (List.not_mem_nil (nilChecks ▸ found)).elim, fun _ found => by
      simp [nilCollects] at found⟩

private theorem both_keys :
    both.members.map RuleSyntax.JointFirings.Member.key = [(emit 1, [], []), (emit 2, [], [])] := rfl

private theorem distinct_emit : emit 1 ≠ emit 2 := by
  intro equal
  have outputs : (emit 1).body.produce = (emit 2).body.produce := by
    let words (r : RuleSyntax.Rule (Terms (Term atoms))) : List (Term atoms) := r.body.produce
    exact congrArg words equal
  change [c 1] = [c 2] at outputs
  have distinct : (1 : ℕ) ≠ 2 := by decide
  exact distinct (Term.const.inj (List.cons.inj outputs).1)

private theorem both_unique : both.Distinct := by
  change (both.members.map RuleSyntax.JointFirings.Member.key).Nodup
  rw [both_keys]
  exact List.nodup_cons.mpr ⟨fun twin => distinct_emit (congrArg Prod.fst (List.mem_singleton.mp twin)),
    List.nodup_singleton _⟩

theorem one_of_two_is_extendible :
    extensionSeen before slots studio [(emit 1, [], [])] = true := by
  apply (extensionSeen_exact before slots studio _).mpr
  refine ⟨both, both_joint, both_unique, ?_, (emit 2, [], []), ?_, ?_⟩
  · rw [both_keys]
    intro key inside
    obtain rfl := List.mem_singleton.mp inside
    exact List.mem_cons_self
  · rw [both_keys]
    exact List.mem_cons_of_mem _ List.mem_cons_self
  · intro equal
    exact distinct_emit ((congrArg Prod.fst (List.mem_singleton.mp equal)).symm)

theorem both_leave_no_extension :
    extensionSeen before slots studio [(emit 1, [], []), (emit 2, [], [])] = false := by
  have closes := maximal_of_full before studio both both_joint both_unique (by decide +kernel)
  apply Bool.eq_false_iff.mpr
  intro extended
  obtain ⟨larger, yes, distinct, subset, key, included, extra⟩ :=
    (extensionSeen_exact before slots studio _).mp extended
  have same := closes.2.2 larger yes distinct (fun key here => subset (both_keys ▸ here)) key included
  exact extra (both_keys ▸ same)

private theorem both_own : both.AdmitsOwn (act atoms) before.state := by
  refine ⟨both_joint.1, both_joint.2.1, both_joint.2.2.1, ?_⟩
  intro member inside point solution _
  cases point
  apply both_joint.2.2.2 PUnit.unit solution _ member inside
  change Unifies solution []
  intro _ member
  cases member

private def maximal : SymbolicSchedules.Discipline.{0, 0, 0} studio := .maximal
private def every : SymbolicSchedules.Discipline.{0, 0, 0} studio :=
  .every (SymbolicComplete.ordered studio) (fun _ => true)

private theorem known_maximal : SymbolicSchedules.EnabledAt slots maximal 2 before := by
  obtain ⟨requests, found, allowed, keys⟩ :=
    atWidth_covers_joint before slots studio both.members both_joint
  have length : requests.length = 2 := (SymbolicFiring.mem_tuples _ _ _).mp found |>.1
  refine ⟨requests, ?_, ?_⟩
  · apply (SymbolicSchedules.mem_options studio 2 before requests).mpr
    refine ⟨fun empty => by simp [empty] at length, length.le, ?_⟩
    rw [length]
    exact found
  · have count := congrArg List.length keys
    simp only [List.length_map] at count
    apply maximal_of_full before studio _ allowed
    · change (List.map RuleSyntax.JointFirings.Member.key _).Nodup
      rw [keys]
      exact both_unique
    · rw [count]
      decide +kernel

/-- The shared driver stops on budget without touching the store, even
with a known two-member maximal publication ready. -/
theorem maximal_budget_is_not_quiescence :
    SnapshotMachine.Runs (SymbolicSchedules.schedule slots maximal 2)
      (.entry 0 before) (.halt (.exhausted before)) := by
  have admitted := known_maximal
  apply (SnapshotMachine.machine_run_iff (SymbolicSchedules.schedule slots maximal 2) 0 before _).mpr
  cases found : SnapshotMachine.search (SymbolicSchedules.schedule slots maximal 2) before with
  | none => exact (((SymbolicSchedules.search_empty_iff slots maximal 2 before).mp found) admitted).elim
  | some _ => simp [SnapshotMachine.run, found]

private theorem width_one_is_not_complete : ¬SymbolicSchedules.EnabledAt slots every 1 before := by
  rintro ⟨requests, offered, allows⟩
  have under := ((SymbolicSchedules.mem_options studio 1 before requests).mp offered).2.1
  let proposed := requestBatch before slots requests
  let keying := SymbolicComplete.ordered studio
  have offeredKeys : both.members.map RuleSyntax.JointFirings.Member.key ⊆
      proposed.members.map RuleSyntax.JointFirings.Member.key := by
    intro key inside
    obtain ⟨member, found, rfl⟩ := List.mem_map.mp inside
    have admitted := Bag.admits_member (act atoms) (fun _ _ => ⟨Subst.id atoms⟩) both_own (m := member) found
    have complete : proposed.CompleteBy (act atoms) before.state keying.identity {k | true = true} := allows.2.2.2
    exact complete member.firing rfl admitted
  have length := both_unique.length_le_of_subset offeredKeys
  simp only [List.length_map] at length
  have two : both.members.length = 2 := rfl
  change both.members.length ≤ (requestBatch before slots requests).members.length at length
  rw [SymbolicBatch.requestBatch_width] at length
  omega

/-- The width bounds the scheduler's proposals, not which matches
exist for the `every` observation. -/
theorem width_one_every_cannot_publish (fuel : ℕ) :
    SnapshotMachine.run (SymbolicSchedules.schedule slots every 1) fuel before = .quiescent before := by
  have empty := (SymbolicSchedules.search_empty_iff slots every 1 before).mpr width_one_is_not_complete
  cases fuel <;> simp [SnapshotMachine.run, empty]

end Mettapedia.Machines.TIsa.Derivation.SymbolicScheduleSearch.Examples
