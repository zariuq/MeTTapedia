import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStore
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreSyntax
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.FirstOrderFreshFamily

/-! # Actual rule-syntax firings supply ground propagation instances -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreSyntax

open Mettapedia.Logic.LP
open OneFrame (Terms frames ext)
open JointFirings

variable {signature : LPSignature} [DecidableEq signature.vars]
  [DecidableEq signature.constants] [DecidableEq signature.functionSymbols]
  {P : Program (Terms (Term signature))}

abbrev X := frames (FirstOrder.action signature)
abbrev E := ext (FirstOrder.action signature)

theorem present_value (rows : Finset (Term signature)) {o : Term signature × ℕ}
    (inside : o ∈ (SetStore.represent rows).present) : o.1 ∈ rows := by
  obtain ⟨value, member, rfl⟩ := Finset.mem_image.mp inside
  exact member

/-- A selected read of a ground source fixes that entire pattern under the joint solution. -/
theorem selected_read_value (rows : Finset (Term signature)) (ground : GroundRows rows)
    (candidate : SetStore.Candidate P) (yes : candidate.Admits X (SetStore.represent rows))
    (answer : Subst signature)
    (solved : X.Models (a := PUnit.unit) (b := PUnit.unit) answer
      (candidate.information X (SetStore.represent rows)))
    (member : OneMember (FirstOrder.action signature) (Term signature × ℕ) P)
    (inside : member ∈ candidate.members) (term : Term signature) (read : term ∈ member.rule.body.read) :
    (answer.comp member.opening).applyTerm term ∈ rows := by
  have fits := yes.1.2.2.2 member inside
  have lengths : (member.firing.opened X).read.length = member.selection.read.length := by
    simpa only [Firing.opened, RuleInstance.map, List.length_map] using fits.2.1
  obtain ⟨o, pair⟩ := SetStore.zip_left lengths
    (List.mem_map.mpr ⟨term, read, rfl⟩)
  have enabled := Bag.enabled_member yes.2.1 inside
  have present := enabled.kept_subset (List.mem_toFinset.mpr (List.of_mem_zip pair).2)
  have value := present_value rows present
  have equal := member.firing.read_solved (X := X) (s := SetStore.represent rows)
    (Bag.models_member X inside solved) pair
  change answer.applyTerm (member.opening.applyTerm term) =
    answer.applyTerm ((Subst.id signature).applyTerm o.1) at equal
  rw [Subst.applyTerm_id, FirstOrder.ground_fixed answer o.1 (ground o.1 value)] at equal
  rw [Subst.applyTerm_comp, equal]
  exact value

def settledMember (rows : Finset (Term signature)) (ground : GroundRows rows)
    (pure : ∀ rule ∈ P, Propagates rule)
    (candidate : SetStore.Candidate P) (yes : candidate.Admits X (SetStore.represent rows))
    (answer : Subst signature)
    (solved : X.Models (a := PUnit.unit) (b := PUnit.unit) answer
      (candidate.information X (SetStore.represent rows)))
    (member : OneMember (FirstOrder.action signature) (Term signature × ℕ) P)
    (inside : member ∈ candidate.members) : GroundMatch P where
  rule := member.rule
  member := member.member
  propagates := pure member.rule member.member
  assignment := answer.comp member.opening
  groundReads term read := ground _ (selected_read_value rows ground candidate yes answer solved member inside term read)
  checked left right check := by
    have holds := (yes.2.2.2 PUnit.unit answer solved) member inside
    have opened : Check.equal (member.opening.applyTerm left) (member.opening.applyTerm right) ∈
        (member.firing.opened X).checks :=
      List.mem_map.mpr ⟨Check.equal left right, check, rfl⟩
    have checked := holds.1 _ opened
    change answer.applyTerm (member.opening.applyTerm left) =
      answer.applyTerm (member.opening.applyTerm right) at checked
    simpa only [Subst.applyTerm_comp] using checked

theorem settledMember_enabled (rows : Finset (Term signature)) (ground : GroundRows rows)
    (pure : ∀ rule ∈ P, Propagates rule)
    (candidate : SetStore.Candidate P) (yes : candidate.Admits X (SetStore.represent rows))
    (answer : Subst signature)
    (solved : X.Models (a := PUnit.unit) (b := PUnit.unit) answer
      (candidate.information X (SetStore.represent rows)))
    (member : OneMember (FirstOrder.action signature) (Term signature × ℕ) P)
    (inside : member ∈ candidate.members) :
    (consequence (settledMember rows ground pure candidate yes answer solved member inside)).read ⊆ rows := by
  intro value inRead
  obtain ⟨term, read, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp inRead)
  exact selected_read_value rows ground candidate yes answer solved member inside term read

theorem propagation_no_takes (rows : Finset (Term signature))
    (pure : ∀ rule ∈ P, Propagates rule) (candidate : SetStore.Candidate P)
    (yes : candidate.Admits X (SetStore.represent rows)) : candidate.selection.taken = [] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro member inside
  have lengths := (yes.1.2.2.2 member inside).1
  rw [(pure member.rule member.member).noTake, List.length_nil] at lengths
  exact List.eq_nil_of_length_eq_zero lengths.symm

theorem actual_step_preserves_ground {timing : SetStore.AskTiming}
    (pure : ∀ rule ∈ P, Propagates rule) {rows after : Finset (Term signature)}
    (ground : GroundRows rows) (step : SetStore.Step timing P rows after) : GroundRows after := by
  obtain ⟨candidate, _, admitted, answer, accepted, rfl, _⟩ := step
  have yes := SetStore.admitted_after admitted
  have solved : X.Models (a := PUnit.unit) (b := PUnit.unit) answer
      (candidate.information X (SetStore.represent rows)) := unifyTotal_sound _ _ accepted
  have takes := propagation_no_takes rows pure candidate yes
  intro value member
  change value ∈ SetStore.setResult rows candidate answer at member
  simp only [SetStore.setResult, takes, List.toFinset_nil, Finset.image_empty,
    SetStore.update, Finset.sdiff_empty, Finset.mem_union, Finset.mem_image] at member
  rcases member with ⟨term, old, rfl⟩ | ⟨term, made, rfl⟩
  · rw [FirstOrder.ground_fixed answer term (ground term old)]
    exact ground term old
  · obtain ⟨m, inside, produced⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp made)
    obtain ⟨source, sourceMade, rfl⟩ := List.mem_map.mp produced
    have generated := instance_ground (settledMember rows ground pure candidate yes answer solved m inside)
    apply generated
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨source, sourceMade, Subst.applyTerm_comp _ _ _⟩)

theorem actual_step_le_closure {timing : SetStore.AskTiming}
    (pure : ∀ rule ∈ P, Propagates rule) (seed : Finset (Term signature))
    {rows after : Finset (Term signature)} (ground : GroundRows rows)
    (old : (rows : Set (Term signature)) ⊆ SetStoreClosure.closure (consequence (P := P)) seed)
    (step : SetStore.Step timing P rows after) :
    (after : Set (Term signature)) ⊆ SetStoreClosure.closure (consequence (P := P)) seed := by
  obtain ⟨candidate, _, admitted, answer, accepted, rfl, _⟩ := step
  have yes := SetStore.admitted_after admitted
  have solved : X.Models (a := PUnit.unit) (b := PUnit.unit) answer
      (candidate.information X (SetStore.represent rows)) := unifyTotal_sound _ _ accepted
  have takes := propagation_no_takes rows pure candidate yes
  intro value member
  change value ∈ SetStore.setResult rows candidate answer at member
  simp only [SetStore.setResult, takes, List.toFinset_nil, Finset.image_empty,
    SetStore.update, Finset.sdiff_empty, Finset.mem_union, Finset.mem_image] at member
  rcases member with ⟨term, prior, rfl⟩ | ⟨term, made, rfl⟩
  · rw [FirstOrder.ground_fixed answer term (ground term prior)]
    exact old prior
  · obtain ⟨m, inside, produced⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp made)
    obtain ⟨source, sourceMade, rfl⟩ := List.mem_map.mp produced
    let groundMatch := settledMember rows ground pure candidate yes answer solved m inside
    apply SetStoreClosure.closure_closed (consequence (P := P)) seed groundMatch
    refine ⟨fun term read => old (settledMember_enabled rows ground pure candidate yes answer solved m inside read), ?_⟩
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨source, sourceMade, Subst.applyTerm_comp _ _ _⟩)

theorem actual_step_extensive {timing : SetStore.AskTiming}
    (pure : ∀ rule ∈ P, Propagates rule) {rows after : Finset (Term signature)}
    (ground : GroundRows rows) (step : SetStore.Step timing P rows after) : rows ⊆ after := by
  obtain ⟨candidate, _, admitted, answer, _, rfl, _⟩ := step
  have takes := propagation_no_takes rows pure candidate (SetStore.admitted_after admitted)
  intro value inside
  apply (SetStore.mem_update).mpr
  left
  refine ⟨value, inside, ?_, FirstOrder.ground_fixed answer value (ground value inside)⟩
  simp [takes]

theorem closed_ground_terminal {timing : SetStore.AskTiming}
    (pure : ∀ rule ∈ P, Propagates rule) (rows : Finset (Term signature)) (ground : GroundRows rows)
    (closed : SetStoreClosure.Closed (consequence (P := P)) rows) :
    ∀ after, ¬ SetStore.Step timing P rows after := by
  have closure_eq : SetStoreClosure.closure (consequence (P := P)) rows = (rows : Set (Term signature)) := by
    apply Set.Subset.antisymm
    · exact (Mettapedia.GSLT.OpenEnded.ChaoticIteration.isLeast_target
        (fun m => SetStoreClosure.action (consequence m)) (rows : Set (Term signature))).2
          ⟨Set.Subset.refl _, (SetStoreClosure.closed_action_iff _ _).mp closed⟩
    · exact SetStoreClosure.seed_subset_closure _ _
  intro after step
  have upper := actual_step_le_closure pure rows ground (SetStoreClosure.seed_subset_closure _ _) step
  rw [closure_eq] at upper
  have equal : after = rows := Finset.Subset.antisymm upper (actual_step_extensive pure ground step)
  exact SetStore.unchanged_is_not_step (equal ▸ SetStore.sameRows_refl rows) step

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreSyntax
