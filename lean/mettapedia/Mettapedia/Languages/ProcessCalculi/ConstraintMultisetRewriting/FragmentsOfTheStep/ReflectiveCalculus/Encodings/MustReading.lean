import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.DividingLineControls

/-!
# Success read on every maximal run: positive systems are switched off by positive neighbours

`succeeds_beside` is about reachable success (a may reading). Under the must reading, success on
every maximal run:

* **The cited control does not witness the must reading.** In `neighbour_rule_takes_success_row` the
  system's row `ω!(0)` is present at the start, so the composite shows success at its first state
  (`eater_control_shows_at_once`), and every maximal run passes through success.
* **A witness that does.** `mustSystem ω`: one positive rule (take `*@0`, make `ω!(0)`) and the row
  `*@0`. Alone its start shows no barb, it can move, and every move shows the barb
  (`must_alone`): every maximal run passes through success. Beside `eatSystem` (one positive rule,
  take `*@0` and make nothing; no row) the two are composable and reachable success is kept, but one
  move of the neighbour's rule leads to a state with no move, and neither state shows the barb
  (`must_reading_switched`). That run is finite and maximal, so no fairness assumption removes it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.MustReading

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open ByInstantiation (sig G Closed Similar ObsSimilar Grounding knowledge groundFrame someGrounding zeroT dropqT)
open Interface.Frames (Frame)

/-! ## The cited control shows success at once -/

/-- **The composite of `neighbour_rule_takes_success_row` shows success at its first state.** -/
theorem eater_control_shows_at_once {ω : G [] .nm} (closed : Closed ω) :
    (stepParallelSolvable ω).success ((stepParallelSolvable ω).par (outputSystem ω) (eaterSystem ω)) :=
  success_persists_composable ω _ _ (neighbour_rule_takes_success_row closed).1 (single_output_barb closed)

/-! ## The systems -/

/-- **Take `*@0`, make `ω!(0)`.** -/
abbrev fireRule (ω : G [] .nm) : RuleSyntax.Rule (RuleSyntax.Contextual.Terms sig) where
  locals := groundFrame
  body := { take := [ByInstantiation.obs blockerRow], read := [], tell := [], checks := [],
            produce := [ByInstantiation.obs (successRow ω)] }
  collect := []

/-- **Take `*@0`, make nothing.** -/
abbrev eatRule : RuleSyntax.Rule (RuleSyntax.Contextual.Terms sig) where
  locals := groundFrame
  body := { take := [ByInstantiation.obs blockerRow], read := [], tell := [], checks := [], produce := [] }
  collect := []

/-- The system: the rule `fireRule ω` and the row `*@0`. -/
def mustSystem (ω : G [] .nm) : System := ⟨{fireRule ω}, single blockerRow⟩

/-- The neighbour: the rule `eatRule` and no row. -/
def eatSystem : System := ⟨{eatRule}, emptyState⟩

theorem mustSystem_positive (ω : G [] .nm) : ∀ r ∈ (mustSystem ω).program, RuleSyntax.Scope.Positive r := by
  intro r member
  rw [Set.mem_singleton_iff.mp member]
  exact ⟨fun _ inside => absurd inside List.not_mem_nil, rfl⟩

theorem eatSystem_positive : ∀ r ∈ eatSystem.program, RuleSyntax.Scope.Positive r := by
  intro r member
  rw [Set.mem_singleton_iff.mp member]
  exact ⟨fun _ inside => absurd inside List.not_mem_nil, rfl⟩

theorem must_composable (ω : G [] .nm) : (stepParallelSolvable ω).composable (mustSystem ω) eatSystem := by
  refine (ByInstantiation.solvable_iff _).mpr ⟨someGrounding _, ?_⟩
  intro e member
  change e ∈ knowledge.applyStore _ ([] : List _) ++ knowledge.applyStore _ ([] : List _) at member
  simp [Interface.Frames.applyStore] at member

/-! ## No barb where the only rows are `*@0` -/

theorem single_blocker_no_barb (ω : G [] .nm) : ¬ OutBarb ω (single blockerRow) := by
  rintro ⟨o, _, B, σ, h, _, equal⟩
  have similar := equal (someGrounding B)
  change ObsSimilar
      (instantiateObservation (someGrounding B) (instantiateObservation σ (ByInstantiation.obs blockerRow)))
      (instantiateObservation (someGrounding B)
        (instantiateObservation h ⟨[], .pr, ByInstantiation.outputT (embed ω) payloadUnknown⟩)) at similar
  have left : instantiateObservation (someGrounding B)
      (instantiateObservation σ (ByInstantiation.obs blockerRow)) = ByInstantiation.obs blockerRow :=
    ground_back _ _ _
  rw [left] at similar
  have closed := ByInstantiation.obsSimilar_closed.mp similar
  change Similar (dropqT zeroT) (ByInstantiation.outputT _ _) at closed
  cases closed

theorem composite_no_barb (ω : G [] .nm) : ¬ OutBarb ω (tensor (single blockerRow) emptyState) := by
  rintro ⟨o, present, B, σ, h, _, equal⟩
  rcases mem_tensor.mp present with ⟨k, _, rfl⟩ | ⟨k, inside, _⟩
  · have similar := equal (someGrounding B)
    change ObsSimilar
        (instantiateObservation (someGrounding B)
          (instantiateObservation σ ((tensor (single blockerRow) emptyState).label (2 * k))))
        (instantiateObservation (someGrounding B)
          (instantiateObservation h ⟨[], .pr, ByInstantiation.outputT (embed ω) payloadUnknown⟩)) at similar
    have label : (tensor (single blockerRow) emptyState).label (2 * k) =
        instantiateObservation (leftIn (single blockerRow).frame emptyState.frame)
          (ByInstantiation.obs blockerRow) :=
      tensor_label_even (single blockerRow) emptyState k
    have left : instantiateObservation (someGrounding B)
        (instantiateObservation σ ((tensor (single blockerRow) emptyState).label (2 * k))) =
          ByInstantiation.obs blockerRow := by
      rw [label]
      exact ground_back₃ (leftIn (single blockerRow).frame emptyState.frame) σ (someGrounding B)
        (ByInstantiation.obs blockerRow)
    rw [left] at similar
    have closed := ByInstantiation.obsSimilar_closed.mp similar
    change Similar (dropqT zeroT) (ByInstantiation.outputT _ _) at closed
    cases closed
  · exact absurd inside (Finset.notMem_empty k)

/-! ## Alone: every maximal run passes through success -/

abbrev fireFiring (ω : G [] .nm) :
    RuleSyntax.Firing ℕ decl ({fireRule ω} : Prog) (single blockerRow).frame :=
  RuleSyntax.Contextual.canonical (F := (single blockerRow).frame) (fireRule ω) (Set.mem_singleton _)
    ⟨[0], [], [1]⟩ []

theorem fireFiring_admitted (ω : G [] .nm) : (fireFiring ω).Admits knowledge (single blockerRow) := by
  refine ⟨⟨canonical_fresh_knowledge _ (fireRule ω) _ _ _, List.nodup_singleton 0, List.nodup_singleton 1,
    rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
  · change Enabled (fun _ : ℕ => ()) ({0} : Finset ℕ) ((⟨[0], [], [1]⟩ : Selection ℕ).commit (T := Unit))
    decide
  · refine ⟨groundFrame, someGrounding _, ?_⟩
    intro e inside
    change e ∈ [(knowledge.act (fireFiring ω).opening (ByInstantiation.obs blockerRow),
      knowledge.act (decl.weaken (fireFiring ω).ext) (ByInstantiation.obs blockerRow))] at inside
    obtain rfl := List.mem_singleton.mp inside
    exact equal_of_grounds (o := ByInstantiation.obs blockerRow)
      (fun g => ground_back₃ (fireFiring ω).opening (someGrounding _) g (ByInstantiation.obs blockerRow))
      (fun g => ground_back₃ (decl.weaken (fireFiring ω).ext) (someGrounding _) g (ByInstantiation.obs blockerRow))
  · intro b σ _
    exact ⟨fun c inside => (nomatch inside), fun q inside => (nomatch inside)⟩

/-- **Every move of the system alone shows the barb.** -/
theorem alone_moves_show (ω : G [] .nm) (T : System) (move : SystemReduces (mustSystem ω) T) :
    OutBarb ω T.state := by
  obtain ⟨P, s⟩ := T
  obtain ⟨_, f, admitted, rfl⟩ := move
  obtain ⟨rule, member, ext, opening, ⟨taken, read, made⟩, seen⟩ := f
  have isFire : rule = fireRule ω := member
  subst isFire
  obtain ⟨⟨_, _, _, takeLength, _, produceLength, _⟩, enabled, _, _⟩ := admitted
  obtain ⟨o, rfl⟩ : ∃ o, taken = [o] := by
    match taken, takeLength with
    | [o], _ => exact ⟨o, rfl⟩
  obtain ⟨m, rfl⟩ : ∃ m, made = [m] := by
    match made, produceLength with
    | [m], _ => exact ⟨m, rfl⟩
  have isZero : o = 0 :=
    Finset.mem_singleton.mp (enabled.taken_subset (List.mem_toFinset.mpr (List.mem_singleton_self o)))
  subst isZero
  refine outBarb_of_ground (o := m) ?_ ?_ ?_
  · change m ∈ fire ({0} : Finset ℕ) ((⟨[0], read, [m]⟩ : Selection ℕ).commit (T := Unit))
    rw [mem_fire]
    exact .inr (by simp [Selection.commit])
  · intro e inside
    change e ∈ [(knowledge.act opening (ByInstantiation.obs blockerRow),
      knowledge.act (decl.weaken ext) (ByInstantiation.obs blockerRow))] at inside
    obtain rfl := List.mem_singleton.mp inside
    exact equal_of_grounds (o := ByInstantiation.obs blockerRow)
      (fun g => ground_back₃ opening (someGrounding _) g (ByInstantiation.obs blockerRow))
      (fun g => ground_back₃ (decl.weaken ext) (someGrounding _) g (ByInstantiation.obs blockerRow))
  · show instantiateObservation (someGrounding _)
      (RuleSyntax.relabel (Tm := RuleSyntax.Contextual.Terms sig) _ [m]
        [knowledge.act opening (ByInstantiation.obs (successRow ω))] m) = _
    simp only [RuleSyntax.relabel, if_pos]
    exact ground_back opening (someGrounding _) (ByInstantiation.obs (successRow ω))

/-- **Alone, success is on every maximal run**: the start shows no barb, the system can move, and every
move shows the barb. -/
theorem must_alone (ω : G [] .nm) :
    ¬ OutBarb ω (mustSystem ω).state ∧ (∃ T, SystemReduces (mustSystem ω) T) ∧
      ∀ T, SystemReduces (mustSystem ω) T → OutBarb ω T.state :=
  ⟨single_blocker_no_barb ω,
    ⟨⟨{fireRule ω}, (fireFiring ω).result knowledge (single blockerRow)⟩,
      ⟨rfl, fireFiring ω, fireFiring_admitted ω, rfl⟩⟩,
    alone_moves_show ω⟩

/-! ## Beside the eater: a maximal run with no success -/

abbrev eatFiring (ω : G [] .nm) :
    RuleSyntax.Firing ℕ decl (({fireRule ω} ∪ {eatRule} : Prog))
      (tensor (single blockerRow) emptyState).frame :=
  RuleSyntax.Contextual.canonical (F := (tensor (single blockerRow) emptyState).frame) eatRule
    (Set.mem_union_right _ (Set.mem_singleton _)) ⟨[0], [], []⟩ []

theorem eatFiring_admitted (ω : G [] .nm) :
    (eatFiring (ω := ω)).Admits knowledge (tensor (single blockerRow) emptyState) := by
  refine ⟨⟨canonical_fresh_knowledge _ eatRule _ _ _, List.nodup_singleton 0, List.nodup_nil,
    rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
  · change Enabled (fun _ : ℕ => ())
      (({0} : Finset ℕ).map evenEmbedding ∪ (∅ : Finset ℕ).map oddEmbedding)
      ((⟨[0], [], []⟩ : Selection ℕ).commit (T := Unit))
    decide
  · refine ⟨groundFrame, someGrounding _, ?_⟩
    intro e inside
    change e ∈ [(knowledge.act (eatFiring (ω := ω)).opening (ByInstantiation.obs blockerRow),
      knowledge.act (decl.weaken (eatFiring (ω := ω)).ext)
        ((tensor (single blockerRow) emptyState).label 0))] at inside
    obtain rfl := List.mem_singleton.mp inside
    have label : (tensor (single blockerRow) emptyState).label 0 =
        instantiateObservation (leftIn (single blockerRow).frame emptyState.frame)
          (ByInstantiation.obs blockerRow) :=
      tensor_label_even (single blockerRow) emptyState 0
    show knowledge.E
      (knowledge.act (b := groundFrame) (someGrounding _)
        (knowledge.act (eatFiring (ω := ω)).opening (ByInstantiation.obs blockerRow)))
      (knowledge.act (b := groundFrame) (someGrounding _)
        (knowledge.act (decl.weaken (eatFiring (ω := ω)).ext) ((tensor (single blockerRow) emptyState).label 0)))
    rw [label]
    exact equal_of_grounds (o := ByInstantiation.obs blockerRow)
      (fun g => ground_back₃ (eatFiring (ω := ω)).opening (someGrounding _) g (ByInstantiation.obs blockerRow))
      (fun g => ground_back₄ (leftIn (single blockerRow).frame emptyState.frame)
        (decl.weaken (eatFiring (ω := ω)).ext) (someGrounding _) g (ByInstantiation.obs blockerRow))
  · intro b σ _
    exact ⟨fun c inside => (nomatch inside), fun q inside => (nomatch inside)⟩

theorem eat_result_empty (ω : G [] .nm) :
    ((eatFiring (ω := ω)).result knowledge (tensor (single blockerRow) emptyState)).present = ∅ := by
  change fire (({0} : Finset ℕ).map evenEmbedding ∪ (∅ : Finset ℕ).map oddEmbedding)
    ((⟨[0], [], []⟩ : Selection ℕ).commit (T := Unit)) = ∅
  decide

theorem composite_takes (ω : G [] .nm) :
    ∀ r ∈ ({fireRule ω} ∪ {eatRule} : Prog), r.body.take ≠ [] := by
  intro r member
  rcases (Set.mem_union r _ _).mp member with isFire | isEat
  · rw [Set.mem_singleton_iff.mp isFire]
    simp
  · rw [Set.mem_singleton_iff.mp isEat]
    simp

/-- **Under the must reading a positive system is switched off by a positive composable neighbour.**
Both programs are positive and the systems are composable; alone, every maximal run passes through
success (`must_alone`); side by side reachable success is kept, and yet one move of the neighbour's
rule leads from a state with no barb to a state with no move and no barb: a finite maximal run without
success. -/
theorem must_reading_switched (ω : G [] .nm) :
    (∀ r ∈ (mustSystem ω).program, RuleSyntax.Scope.Positive r) ∧
      (∀ r ∈ eatSystem.program, RuleSyntax.Scope.Positive r) ∧
      (stepParallelSolvable ω).composable (mustSystem ω) eatSystem ∧
      (stepParallelSolvable ω).Succeeds ((stepParallelSolvable ω).par (mustSystem ω) eatSystem) ∧
      ∃ U, SystemReduces ((stepParallelSolvable ω).par (mustSystem ω) eatSystem) U ∧
        ¬ OutBarb ω ((stepParallelSolvable ω).par (mustSystem ω) eatSystem).state ∧
        ¬ OutBarb ω U.state ∧ ∀ U', ¬ SystemReduces U U' := by
  obtain ⟨_, ⟨T, move⟩, shows⟩ := must_alone ω
  refine ⟨mustSystem_positive ω, eatSystem_positive, must_composable ω,
    succeeds_beside (fun r member => positive_monotone (mustSystem_positive ω r member)) (must_composable ω)
      ⟨T, .single move, shows T move⟩,
    ⟨{fireRule ω} ∪ {eatRule}, (eatFiring (ω := ω)).result knowledge (tensor (single blockerRow) emptyState)⟩,
    ⟨rfl, eatFiring ω, eatFiring_admitted ω, rfl⟩, composite_no_barb ω,
    no_barb_of_empty (eat_result_empty ω), ?_⟩
  rintro U' ⟨_, f, admitted, _⟩
  exact stuck_of_empty (eat_result_empty ω) (composite_takes ω) f admitted

#print axioms eater_control_shows_at_once
#print axioms single_blocker_no_barb
#print axioms composite_no_barb
#print axioms fireFiring_admitted
#print axioms alone_moves_show
#print axioms must_alone
#print axioms eatFiring_admitted
#print axioms eat_result_empty
#print axioms must_reading_switched

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.MustReading
