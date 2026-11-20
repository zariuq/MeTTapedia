import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.DividingLineControls

/-!
# A collect query over a ground pattern is switched off, by a neighbour whose row has an unknown of its own

`collect_switched` uses a collect pattern that is the rule's own unknown. Here the rule has no unknown
at all (`groundCollectSpawn`: its frame is the frame with no unknowns): no check, the collect pattern
`*@0`, and it makes `ω!(0)`.

* Alone, with no row, it succeeds (`groundCollectSystem_succeeds`).
* Beside the system with one row `*@z`, where `z` is an unknown of that system's own frame and its
  knowledge is empty (`freeSystem`), the two are composable, and the composite never succeeds
  (`groundCollect_switched_by_free`): the collect query must report the same rows at every solution, and
  `z := 0` makes the row match `*@0` while `z := *@0` does not.
* Beside the system with the ground row `*@0` it still succeeds (`groundCollect_beside_ground`): with
  ground rows the collect query is determined, the rule reports the row and fires.

So what switches a collect query off is that the neighbour can make the set of rows it matches depend on the
solution; the unknown that does it may be the neighbour's.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.GroundCollect

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open ByInstantiation (sig G Similar ObsSimilar Grounding knowledge groundFrame someGrounding zeroT dropqT)
open Interface.Frames (Frame)

/-! ## The rule and the two neighbours -/

/-- **A collect query over a ground pattern**: no unknown, no check, the collect pattern `*@0`, and it makes
`ω!(0)`. -/
abbrev groundCollectSpawn (ω : G [] .nm) : RuleSyntax.Rule (RuleSyntax.Contextual.Terms sig) where
  locals := groundFrame
  body := { take := [], read := [], tell := [], checks := [],
            produce := [ByInstantiation.obs (successRow ω)] }
  collect := [ByInstantiation.obs blockerRow]

/-- Its system, with no row. -/
def groundCollectSystem (ω : G [] .nm) : System := ⟨{groundCollectSpawn ω}, emptyState⟩

/-- **The state with one row `*@z`**, `z` an unknown of its own frame, and no knowledge. -/
abbrev freeState : ByInstantiation.State :=
  ⟨payloadFrame, [], {0}, fun _ => ⟨[], .pr, dropqT payloadUnknown⟩⟩

/-- Its system: no rule. -/
def freeSystem : System := ⟨∅, freeState⟩

theorem free_label : (tensor emptyState freeState).label 1 =
    instantiateObservation (rightIn emptyState.frame freeState.frame) ⟨[], .pr, dropqT payloadUnknown⟩ :=
  tensor_label_odd emptyState freeState 0

/-- The grounding of the composite frame that sends `z` to `v`. -/
abbrev zTo (v : G [] .pr) : Assignment (tensor emptyState freeState).frame.arity groundFrame.arity :=
  RuleSyntax.Contextual.copair sig (F := emptyState.frame) (N := freeState.frame) (B := groundFrame)
    (someGrounding emptyState.frame) (fun _ => v : Assignment payloadFrame.arity groundFrame.arity)

/-- At that grounding the neighbour's row is `*@v`. -/
theorem free_value (v : G [] .pr) :
    instantiateObservation (zTo v) ((tensor emptyState freeState).label 1) = ByInstantiation.obs (dropqT v) := by
  rw [free_label]
  refine (RuleSyntax.Contextual.copair_opening sig (F := emptyState.frame) (N := freeState.frame)
    (B := groundFrame) (someGrounding emptyState.frame)
    (fun _ => v : Assignment payloadFrame.arity groundFrame.arity) _).trans ?_
  show (⟨[], .pr, dropqT (instantiate (fun _ => v : Assignment payloadFrame.arity groundFrame.arity)
    payloadUnknown)⟩ : Observation sig ByInstantiation.noUnknowns) = _
  rw [instantiate_generator]

/-! ## Alone, the ground collect query succeeds -/

abbrev groundCollectFiring (ω : G [] .nm) :
    RuleSyntax.Firing ℕ decl ({groundCollectSpawn ω} : Prog) emptyState.frame :=
  RuleSyntax.Contextual.canonical (F := emptyState.frame) (groundCollectSpawn ω) (Set.mem_singleton _)
    ⟨[], [], [0]⟩ [∅]

theorem groundCollect_information (ω : G [] .nm) :
    (groundCollectFiring ω).information knowledge emptyState = [] := rfl

theorem groundCollect_admitted (ω : G [] .nm) : (groundCollectFiring ω).Admits knowledge emptyState := by
  refine ⟨⟨canonical_fresh_knowledge _ (groundCollectSpawn ω) _ _ _, List.nodup_nil, List.nodup_singleton 0,
    rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
  · change Enabled (fun _ : ℕ => ()) (∅ : Finset ℕ) ((⟨[], [], [0]⟩ : Selection ℕ).commit (T := Unit))
    decide
  · refine ⟨groundFrame, someGrounding _, ?_⟩
    rw [groundCollect_information]
    exact fun e inside => nomatch inside
  · intro b σ _
    refine ⟨fun c inside => (nomatch inside), fun q inside => ?_⟩
    change q ∈ [(knowledge.act (groundCollectFiring ω).opening (ByInstantiation.obs blockerRow),
      (∅ : Finset ℕ))] at inside
    rw [List.mem_singleton] at inside
    subst inside
    show RuleSyntax.matchesAt knowledge σ _ (∅ : Finset ℕ) _ = ∅
    ext o
    rw [RuleSyntax.mem_matchesAt]
    simp

/-- **Alone, the ground collect query succeeds.** -/
theorem groundCollectSystem_succeeds (ω : G [] .nm) :
    (stepParallelSolvable ω).Succeeds (groundCollectSystem ω) := by
  refine ⟨⟨{groundCollectSpawn ω}, (groundCollectFiring ω).result knowledge emptyState⟩,
    .single ⟨rfl, groundCollectFiring ω, groundCollect_admitted ω, rfl⟩, ?_⟩
  refine outBarb_of_ground (o := 0) ?_ ?_ ?_
  · change 0 ∈ fire (∅ : Finset ℕ) ((⟨[], [], [0]⟩ : Selection ℕ).commit (T := Unit))
    rw [mem_fire]
    exact .inr (by simp [Selection.commit])
  · intro e inside
    change e ∈ (groundCollectFiring ω).information knowledge emptyState at inside
    rw [groundCollect_information] at inside
    exact nomatch inside
  · show instantiateObservation (someGrounding _)
      (instantiateObservation (groundCollectFiring ω).opening (ByInstantiation.obs (successRow ω))) = _
    exact ground_back _ _ _

/-! ## Beside a row with an unknown of the neighbour's own, it never succeeds -/

theorem free_composable (ω : G [] .nm) :
    (stepParallelSolvable ω).composable (groundCollectSystem ω) freeSystem := by
  refine (ByInstantiation.solvable_iff _).mpr ⟨someGrounding _, ?_⟩
  intro e member
  change e ∈ knowledge.applyStore _ ([] : List _) ++ knowledge.applyStore _ ([] : List _) at member
  simp [Interface.Frames.applyStore] at member

/-- The composite shows no output barb: its one row is a drop. -/
theorem free_no_barb (ω : G [] .nm) : ¬ OutBarb ω (tensor emptyState freeState) := by
  rintro ⟨o, present, B, σ, h, _, equal⟩
  have isOne : o = 1 := by
    rcases mem_tensor.mp present with ⟨k, inside, _⟩ | ⟨k, inside, rfl⟩
    · exact absurd inside (Finset.notMem_empty k)
    · rw [Finset.mem_singleton.mp inside]
  subst isOne
  have similar := equal (someGrounding B)
  change ObsSimilar
      (instantiateObservation (someGrounding B) (instantiateObservation σ ((tensor emptyState freeState).label 1)))
      (instantiateObservation (someGrounding B)
        (instantiateObservation h ⟨[], .pr, ByInstantiation.outputT (embed ω) payloadUnknown⟩)) at similar
  rw [free_label] at similar
  have closed := ByInstantiation.obsSimilar_closed.mp similar
  change Similar (dropqT _) (ByInstantiation.outputT _ _) at closed
  cases closed

/-- **Beside `*@z`, the ground collect query is refused**: its information is empty, so every instantiation
solves it; one that sends `z` to `0` makes the row match `*@0`, one that sends `z` to `*@0` does not,
and no report holds at both. -/
theorem groundCollect_blocked_free (ω : G [] .nm)
    (f : RuleSyntax.Firing ℕ decl (({groundCollectSpawn ω} : Prog) ∪ ∅) (tensor emptyState freeState).frame) :
    ¬ f.Admits knowledge (tensor emptyState freeState) := by
  obtain ⟨rule, member, ext, opening, selection, seen⟩ := f
  have isCollect : rule = groundCollectSpawn ω := by
    rcases member with inside | inside
    · exact inside
    · exact inside.elim
  subst isCollect
  rintro ⟨⟨fresh, _, _, _, _, _, collectLength⟩, _, _, entails⟩
  obtain ⟨reported, rfl⟩ : ∃ reported, seen = [reported] := by
    match seen, collectLength with
    | [reported], _ => exact ⟨reported, rfl⟩
  have information : RuleSyntax.Firing.information knowledge (tensor emptyState freeState)
      ⟨groundCollectSpawn ω, member, ext, opening, selection, [reported]⟩ = [] := rfl
  have solved : ∀ u : Assignment (decl.target ext).arity groundFrame.arity,
      knowledge.Models u (RuleSyntax.Firing.information knowledge (tensor emptyState freeState)
        ⟨groundCollectSpawn ω, member, ext, opening, selection, [reported]⟩) := by
    intro u e inside
    rw [information] at inside
    exact nomatch inside
  have present : (1 : ℕ) ∈ (tensor emptyState freeState).present :=
    mem_tensor.mpr (.inr ⟨0, Finset.mem_singleton_self 0, rfl⟩)
  have mentioned : (tensor emptyState freeState).Mentions ((tensor emptyState freeState).label 1) :=
    Or.inr (Or.inr ⟨1, present, rfl⟩)
  have symm := fun {x y : Observation sig groundFrame.arity} (same : knowledge.E x y) =>
    (knowledge.equivalence groundFrame).symm same
  have trans := fun {x y z : Observation sig groundFrame.arity} (one : knowledge.E x y)
    (two : knowledge.E y z) => (knowledge.equivalence groundFrame).trans one two
  -- the pattern, at every instantiation, is `*@0`
  have pattern : ∀ u : Assignment (decl.target ext).arity groundFrame.arity,
      knowledge.act u (knowledge.act (a := groundFrame) opening (ByInstantiation.obs blockerRow)) =
        ByInstantiation.obs blockerRow :=
    fun u => ground_back opening u (ByInstantiation.obs blockerRow)
  have reports : ∀ u : Assignment (decl.target ext).arity groundFrame.arity,
      RuleSyntax.matchesAt knowledge (b := groundFrame) u
        (RuleSyntax.Firing.row knowledge (tensor emptyState freeState)
          ⟨groundCollectSpawn ω, member, ext, opening, selection, [reported]⟩)
        (tensor emptyState freeState).present
          (knowledge.act (a := groundFrame) opening (ByInstantiation.obs blockerRow)) =
        reported := fun u =>
    (entails groundFrame u (solved u)).2
      (knowledge.act (a := groundFrame) opening (ByInstantiation.obs blockerRow), reported)
      (List.mem_singleton_self _)
  -- `z := 0`: the row is `*@0` and is seen
  obtain ⟨u₁, onState₁, _⟩ := fresh groundFrame (zTo zeroT) (someGrounding _)
  have seen₁ : 1 ∈ reported := by
    rw [← reports u₁, RuleSyntax.mem_matchesAt]
    refine ⟨present, ?_⟩
    rw [pattern u₁]
    have value : knowledge.E (knowledge.act (zTo zeroT) ((tensor emptyState freeState).label 1))
        (ByInstantiation.obs blockerRow) := by
      show knowledge.E (instantiateObservation (zTo zeroT) ((tensor emptyState freeState).label 1)) _
      rw [free_value]
      exact (knowledge.equivalence groundFrame).refl _
    exact symm (trans (onState₁ _ mentioned) value)
  -- `z := *@0`: the row is `*@*@0` and is not seen
  obtain ⟨u₂, onState₂, _⟩ := fresh groundFrame (zTo (dropqT zeroT)) (someGrounding _)
  have unseen₂ : 1 ∉ reported := by
    rw [← reports u₂, RuleSyntax.mem_matchesAt]
    rintro ⟨_, equal⟩
    rw [pattern u₂] at equal
    have value : knowledge.E (knowledge.act (zTo (dropqT zeroT)) ((tensor emptyState freeState).label 1))
        (ByInstantiation.obs (dropqT (dropqT zeroT))) := by
      show knowledge.E (instantiateObservation (zTo (dropqT zeroT)) ((tensor emptyState freeState).label 1)) _
      rw [free_value]
      exact (knowledge.equivalence groundFrame).refl _
    have both := trans equal (trans (onState₂ _ mentioned) value)
    have similar := both (fun e => nomatch e)
    change ObsSimilar
      (instantiateObservation (fun e => nomatch e : Grounding groundFrame) (ByInstantiation.obs blockerRow))
      (instantiateObservation (fun e => nomatch e : Grounding groundFrame)
        (ByInstantiation.obs (dropqT (dropqT zeroT)))) at similar
    rw [ByInstantiation.instantiateObservation_ground, ByInstantiation.instantiateObservation_ground]
      at similar
    have closed := ByInstantiation.obsSimilar_closed.mp similar
    change Similar (dropqT zeroT) (dropqT (dropqT zeroT)) at closed
    cases closed with
    | dropq inner => exact zero_not_similar_drop inner
  exact unseen₂ seen₁

/-- **A collect query over a ground pattern is switched off by a composable neighbour**, one whose row has an
unknown of its own. The rule has no unknown and no check; alone it succeeds; beside the neighbour it
never does. -/
theorem groundCollect_switched_by_free (ω : G [] .nm) :
    (groundCollectSpawn ω).locals = groundFrame ∧ (groundCollectSpawn ω).body.checks = [] ∧
      (groundCollectSpawn ω).collect ≠ [] ∧
      (stepParallelSolvable ω).composable (groundCollectSystem ω) freeSystem ∧
      (stepParallelSolvable ω).Succeeds (groundCollectSystem ω) ∧
      ¬ (stepParallelSolvable ω).Succeeds ((stepParallelSolvable ω).par (groundCollectSystem ω) freeSystem) :=
  ⟨rfl, rfl, by simp, free_composable ω, groundCollectSystem_succeeds ω,
    never_succeeds_of_stuck (groundCollect_blocked_free ω) (free_no_barb ω)⟩

/-! ## Control: beside a ground row, the ground collect query still fires -/

abbrev besideGroundFiring (ω : G [] .nm) :
    RuleSyntax.Firing ℕ decl (({groundCollectSpawn ω} : Prog) ∪ ∅) (tensor emptyState (single blockerRow)).frame :=
  RuleSyntax.Contextual.canonical (F := (tensor emptyState (single blockerRow)).frame) (groundCollectSpawn ω)
    (Set.mem_union_left _ (Set.mem_singleton _)) ⟨[], [], [0]⟩ [{1}]

theorem besideGround_information (ω : G [] .nm) :
    (besideGroundFiring ω).information knowledge (tensor emptyState (single blockerRow)) = [] := rfl

theorem besideGround_admitted (ω : G [] .nm) :
    (besideGroundFiring ω).Admits knowledge (tensor emptyState (single blockerRow)) := by
  refine ⟨⟨canonical_fresh_knowledge _ (groundCollectSpawn ω) _ _ _, List.nodup_nil, List.nodup_singleton 0,
    rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
  · change Enabled (fun _ : ℕ => ())
      ((∅ : Finset ℕ).map evenEmbedding ∪ ({0} : Finset ℕ).map oddEmbedding)
      ((⟨[], [], [0]⟩ : Selection ℕ).commit (T := Unit))
    decide
  · refine ⟨groundFrame, someGrounding _, ?_⟩
    rw [besideGround_information]
    exact fun e inside => nomatch inside
  · intro b σ _
    refine ⟨fun c inside => (nomatch inside), fun q inside => ?_⟩
    change q ∈ [(knowledge.act (besideGroundFiring ω).opening (ByInstantiation.obs blockerRow),
      ({1} : Finset ℕ))] at inside
    rw [List.mem_singleton] at inside
    subst inside
    show RuleSyntax.matchesAt knowledge σ ((besideGroundFiring ω).row knowledge (tensor emptyState (single blockerRow)))
      (tensor emptyState (single blockerRow)).present
        (knowledge.act (besideGroundFiring ω).opening (ByInstantiation.obs blockerRow)) = {1}
    ext o
    rw [RuleSyntax.mem_matchesAt]
    constructor
    · rintro ⟨inside, _⟩
      rcases mem_tensor.mp inside with ⟨k, empty, _⟩ | ⟨k, one, rfl⟩
      · exact absurd empty (Finset.notMem_empty k)
      · rw [Finset.mem_singleton.mp one]
        exact Finset.mem_singleton_self 1
    · intro one
      rw [Finset.mem_singleton.mp one]
      refine ⟨mem_tensor.mpr (.inr ⟨0, Finset.mem_singleton_self 0, rfl⟩), ?_⟩
      have label : (tensor emptyState (single blockerRow)).label 1 =
          instantiateObservation (rightIn emptyState.frame (single blockerRow).frame)
            (ByInstantiation.obs blockerRow) :=
        tensor_label_odd emptyState (single blockerRow) 0
      show knowledge.E _ (knowledge.act σ (knowledge.act (decl.weaken (besideGroundFiring ω).ext)
        ((tensor emptyState (single blockerRow)).label 1)))
      rw [label]
      exact equal_of_grounds (o := ByInstantiation.obs blockerRow)
        (fun g => ground_back₃ (besideGroundFiring ω).opening σ g (ByInstantiation.obs blockerRow))
        (fun g => ground_back₄ (rightIn emptyState.frame (single blockerRow).frame)
          (decl.weaken (besideGroundFiring ω).ext) σ g (ByInstantiation.obs blockerRow))

/-- **Control: beside the ground row `*@0`, the ground collect query still succeeds**: the collect query is
determined, the rule reports the row and makes `ω!(0)`. -/
theorem groundCollect_beside_ground (ω : G [] .nm) :
    (stepParallelSolvable ω).composable (groundCollectSystem ω) blockerSystem ∧
      (stepParallelSolvable ω).Succeeds ((stepParallelSolvable ω).par (groundCollectSystem ω) blockerSystem) := by
  refine ⟨?_, ⟨⟨{groundCollectSpawn ω} ∪ ∅, (besideGroundFiring ω).result knowledge
      (tensor emptyState (single blockerRow))⟩,
    .single ⟨rfl, besideGroundFiring ω, besideGround_admitted ω, rfl⟩, ?_⟩⟩
  · refine (ByInstantiation.solvable_iff _).mpr ⟨someGrounding _, ?_⟩
    intro e member
    change e ∈ knowledge.applyStore _ ([] : List _) ++ knowledge.applyStore _ ([] : List _) at member
    simp [Interface.Frames.applyStore] at member
  · refine outBarb_of_ground (o := 0) ?_ ?_ ?_
    · change 0 ∈ fire ((∅ : Finset ℕ).map evenEmbedding ∪ ({0} : Finset ℕ).map oddEmbedding)
        ((⟨[], [], [0]⟩ : Selection ℕ).commit (T := Unit))
      rw [mem_fire]
      exact .inr (by simp [Selection.commit])
    · intro e inside
      change e ∈ (besideGroundFiring ω).information knowledge (tensor emptyState (single blockerRow)) at inside
      rw [besideGround_information] at inside
      exact nomatch inside
    · show instantiateObservation (someGrounding _)
        (instantiateObservation (besideGroundFiring ω).opening (ByInstantiation.obs (successRow ω))) = _
      exact ground_back _ _ _

#print axioms free_value
#print axioms groundCollect_admitted
#print axioms groundCollectSystem_succeeds
#print axioms free_composable
#print axioms free_no_barb
#print axioms groundCollect_blocked_free
#print axioms groundCollect_switched_by_free
#print axioms besideGround_admitted
#print axioms groundCollect_beside_ground

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.GroundCollect
