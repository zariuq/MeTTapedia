import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.DividingLine

/-!
# Controls for the dividing line

`succeeds_beside` has two hypotheses on the system (its rules have only equation checks and `any`
queries, and no collect pattern) and one on the neighbour (its knowledge is solvable); the neighbour's rows and rules
are free. Each control below fails exactly one hypothesis, or shows that a free clause is exercised.

* **The neighbour's rules** (free): the rule `eater` takes a row `ω!(0)`. Beside it, the system of the
  four-rule program with the row `ω!(0)` still succeeds (`succeeds_beside`), and the neighbour's rule
  does fire on the system's success row, to a system that never succeeds
  (`neighbour_rule_takes_success_row`). Rules of a neighbour act on the system's rows; under
  may-success they only add runs. Success read on every run would be switched off here.
* **A count check** (fails the first hypothesis only): `countSpawn` makes `ω!(0)` when exactly one
  row is `*@0`; it has no collect pattern. With the row `*@0` it succeeds; beside the composable
  system holding a second `*@0` it never does (`count_switched`).
* **A collect pattern** (fails the second hypothesis only): `collectSpawn` has no check, makes `ω!(0)`,
  and has the collect pattern of one unknown, so it must report exactly the rows it sees at every
  solution. With no row it succeeds; beside the composable system holding the row `*@0`, the rows the
  pattern sees depend on the solution, no report holds at all of them, and the composite never
  succeeds (`collect_switched`).
* **Absence** is `solvable_switchable`; **knowledge without a solution**, once every pair is
  composable, is `junk_switches`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical (canonicalize)
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open ByInstantiation (sig G Closed Similar ObsSimilar Grounding GroundSolves read outputT zeroT dropqT
  knowledge groundFrame someGrounding)
open Interface.Frames (Frame)

/-! ## Helpers -/

/-- A ground observation, instantiated along three assignments and then grounded, is itself. -/
theorem ground_back₄ {W W' W'' : Type} {D : W → MetaArity sig} {D' : W' → MetaArity sig}
    {D'' : W'' → MetaArity sig} (a : Assignment ByInstantiation.noUnknowns D) (b : Assignment D D')
    (c : Assignment D' D'') (g : Assignment D'' ByInstantiation.noUnknowns)
    (o : Observation sig ByInstantiation.noUnknowns) :
    instantiateObservation g (instantiateObservation c (instantiateObservation b (instantiateObservation a o))) =
      o := by
  rw [instantiateObservation_comp a b, ground_back₃]

/-- Two observations that every grounding sends to the same ground observation are equal in the
knowledge. -/
theorem equal_of_grounds {F : Frame sig} {x y : Observation sig F.arity}
    {o : Observation sig ByInstantiation.noUnknowns}
    (onX : ∀ g : Grounding F, instantiateObservation g x = o)
    (onY : ∀ g : Grounding F, instantiateObservation g y = o) : knowledge.E x y := by
  intro g
  show ObsSimilar (instantiateObservation g x) (instantiateObservation g y)
  rw [onX g, onY g]
  exact ByInstantiation.obsSimilar_refl o

/-- `0` and `*@0` are not name-equivalent. -/
theorem zero_not_similar_drop : ¬ Similar (zeroT : G [] .pr) (dropqT zeroT) := by
  intro similar
  have same := ByInstantiation.similar_canonical similar
  revert same
  decide

/-- A system with no admitted firing and no barb never succeeds. -/
theorem never_succeeds_of_stuck {ω : G [] .nm} {S : System}
    (stuck : ∀ f : RuleSyntax.Firing ℕ decl S.program S.state.frame, ¬ f.Admits knowledge S.state)
    (noBarb : ¬ OutBarb ω S.state) : ¬ (stepParallelSolvable ω).Succeeds S := by
  rintro ⟨T, run, shows⟩
  rcases Relation.ReflTransGen.cases_head run with rfl | ⟨T₁, ⟨_, f, admitted, _⟩, _⟩
  · exact noBarb shows
  · exact stuck f admitted

/-- A state with no row shows no output barb. -/
theorem no_barb_of_empty {ω : G [] .nm} {s : ByInstantiation.State} (empty : s.present = ∅) :
    ¬ OutBarb ω s := by
  rintro ⟨o, present, _⟩
  rw [empty] at present
  exact Finset.notMem_empty o present

/-- At a state with no row, no rule that takes a row is admitted. -/
theorem stuck_of_empty {P : Prog} {s : ByInstantiation.State} (empty : s.present = ∅)
    (takes : ∀ r ∈ P, r.body.take ≠ []) (f : RuleSyntax.Firing ℕ decl P s.frame) :
    ¬ f.Admits knowledge s := by
  rintro ⟨⟨_, _, _, takeLength, _⟩, enabled, _⟩
  have none : f.selection.taken = [] := List.eq_nil_iff_forall_not_mem.mpr fun o inside => by
    have present := enabled.taken_subset (List.mem_toFinset.mpr inside)
    rw [empty] at present
    exact Finset.notMem_empty o present
  rw [none] at takeLength
  exact takes f.rule f.member (List.eq_nil_of_length_eq_zero takeLength)

/-- A row on the output pattern of `ω`, made ground, shows the output barb on `ω`. -/
theorem outBarb_of_ground {ω : G [] .nm} {s : ByInstantiation.State} {o : ℕ} (present : o ∈ s.present)
    (solved : knowledge.Models (a := s.frame) (b := groundFrame) (someGrounding s.frame) s.knowledge)
    (ground : instantiateObservation (someGrounding s.frame) (s.label o) =
      ByInstantiation.obs (successRow ω)) : OutBarb ω s := by
  refine ⟨o, present, groundFrame, someGrounding _, fun _ => zeroT, solved, fun g => ?_⟩
  show ObsSimilar (instantiateObservation g (instantiateObservation (someGrounding _) (s.label o)))
    (instantiateObservation g (instantiateObservation (fun _ => zeroT : Assignment payloadFrame.arity
      ByInstantiation.noUnknowns)
        (⟨[], .pr, outputT (embed ω) payloadUnknown⟩ : Observation sig payloadFrame.arity)))
  rw [ground, outPattern_ground ω zeroT]
  exact ByInstantiation.obsSimilar_refl _

/-! ## The neighbour's rules: a rule that takes the system's success row -/

/-- **A rule that takes a row `ω!(0)`**, and does nothing else. -/
abbrev eater (ω : G [] .nm) : RuleSyntax.Rule (RuleSyntax.Contextual.Terms sig) where
  locals := groundFrame
  body := { take := [ByInstantiation.obs (successRow ω)], read := [], tell := [], checks := [],
            produce := [] }
  collect := []

/-- The neighbour: the eater, and no row. -/
def eaterSystem (ω : G [] .nm) : System := ⟨{eater ω}, emptyState⟩

/-- The composite state: the row `ω!(0)` beside no row. -/
abbrev eaterState (ω : G [] .nm) : ByInstantiation.State := tensor (single (outputT ω zeroT)) emptyState

/-- The eater taking the system's row, identity `0`. -/
abbrev eaterFiring (ω : G [] .nm) :
    RuleSyntax.Firing ℕ decl (ByInstantiation.program ∪ {eater ω}) (eaterState ω).frame :=
  RuleSyntax.Contextual.canonical (F := (eaterState ω).frame) (eater ω)
    (Set.mem_union_right _ (Set.mem_singleton _)) ⟨[0], [], []⟩ []

theorem eater_information (ω : G [] .nm) :
    (eaterFiring ω).information knowledge (eaterState ω) =
      [(knowledge.act (eaterFiring ω).opening (ByInstantiation.obs (successRow ω)),
        knowledge.act (decl.weaken (eaterFiring ω).ext) ((eaterState ω).label 0))] := rfl

theorem eater_admitted (ω : G [] .nm) : (eaterFiring ω).Admits knowledge (eaterState ω) := by
  refine ⟨⟨canonical_fresh_knowledge _ (eater ω) _ _ _, List.nodup_singleton 0, List.nodup_nil, rfl, rfl,
    rfl, rfl⟩, ?_, ?_, ?_⟩
  · change Enabled (fun _ : ℕ => ())
      (({0} : Finset ℕ).map evenEmbedding ∪ (∅ : Finset ℕ).map oddEmbedding)
      ((⟨[0], [], []⟩ : Selection ℕ).commit (T := Unit))
    decide
  · refine ⟨groundFrame, someGrounding _, ?_⟩
    rw [eater_information]
    intro e inside
    obtain rfl := List.mem_singleton.mp inside
    have label : (eaterState ω).label 0 =
        knowledge.act (leftIn (single (outputT ω zeroT)).frame emptyState.frame)
          (ByInstantiation.obs (successRow ω)) :=
      tensor_label_even (single (outputT ω zeroT)) emptyState 0
    show knowledge.E
      (knowledge.act (b := groundFrame) (someGrounding _)
        (knowledge.act (eaterFiring ω).opening (ByInstantiation.obs (successRow ω))))
      (knowledge.act (b := groundFrame) (someGrounding _)
        (knowledge.act (decl.weaken (eaterFiring ω).ext) ((eaterState ω).label 0)))
    rw [label]
    exact equal_of_grounds (o := ByInstantiation.obs (successRow ω))
      (fun g => ground_back₃ (eaterFiring ω).opening (someGrounding (decl.target (eaterFiring ω).ext)) g
        (ByInstantiation.obs (successRow ω)))
      (fun g => ground_back₄ (leftIn (single (outputT ω zeroT)).frame emptyState.frame)
        (decl.weaken (eaterFiring ω).ext) (someGrounding (decl.target (eaterFiring ω).ext)) g
        (ByInstantiation.obs (successRow ω)))
  · intro b σ _
    exact ⟨fun c inside => (nomatch inside), fun q inside => (nomatch inside)⟩

theorem eater_result_empty (ω : G [] .nm) :
    ((eaterFiring ω).result knowledge (eaterState ω)).present = ∅ := by
  change fire (({0} : Finset ℕ).map evenEmbedding ∪ (∅ : Finset ℕ).map oddEmbedding)
    ((⟨[0], [], []⟩ : Selection ℕ).commit (T := Unit)) = ∅
  decide

/-- Every rule of the four-rule program and the eater takes a row. -/
theorem eater_takes (ω : G [] .nm) : ∀ r ∈ ByInstantiation.program ∪ {eater ω}, r.body.take ≠ [] := by
  intro r member
  rcases (Set.mem_union r _ _).mp member with inProgram | isEater
  · rcases ByInstantiation.mem_program.mp inProgram with h | h | h | h <;> rw [h] <;> simp
  · rw [Set.mem_singleton_iff.mp isEater]
    simp

/-- **The rules clause.** The system of the four-rule program with the row `ω!(0)` and the eater
system are composable; side by side they succeed; and the eater fires on the system's success row,
to a system that never succeeds. -/
theorem neighbour_rule_takes_success_row {ω : G [] .nm} (closed : Closed ω) :
    (stepParallelSolvable ω).composable (outputSystem ω) (eaterSystem ω) ∧
      (stepParallelSolvable ω).Succeeds ((stepParallelSolvable ω).par (outputSystem ω) (eaterSystem ω)) ∧
      ∃ U, SystemReduces ((stepParallelSolvable ω).par (outputSystem ω) (eaterSystem ω)) U ∧
        ¬ (stepParallelSolvable ω).Succeeds U := by
  have composable : (stepParallelSolvable ω).composable (outputSystem ω) (eaterSystem ω) := by
    refine (ByInstantiation.solvable_iff _).mpr ⟨someGrounding _, ?_⟩
    intro e member
    change e ∈ knowledge.applyStore _ ([] : List _) ++ knowledge.applyStore _ ([] : List _) at member
    simp [Interface.Frames.applyStore] at member
  refine ⟨composable, succeeds_beside (fun r member => positive_monotone (image_positive r member)) composable
    ⟨outputSystem ω, .refl, single_output_barb closed⟩,
    ⟨ByInstantiation.program ∪ {eater ω}, (eaterFiring ω).result knowledge (eaterState ω)⟩,
    ⟨rfl, eaterFiring ω, eater_admitted ω, rfl⟩, ?_⟩
  exact never_succeeds_of_stuck (stuck_of_empty (eater_result_empty ω) (eater_takes ω))
    (no_barb_of_empty (eater_result_empty ω))

/-! ## A count check -/

/-- **Make `ω!(0)` where exactly one row is `*@0`**: a count check, no collect pattern. -/
abbrev countSpawn (ω : G [] .nm) : RuleSyntax.Rule (RuleSyntax.Contextual.Terms sig) where
  locals := groundFrame
  body := { take := [], read := [], tell := [], checks := [.count (ByInstantiation.obs blockerRow) 1],
            produce := [ByInstantiation.obs (successRow ω)] }
  collect := []

/-- The system of the count-checked rule, with one row `*@0`. -/
def countSystem (ω : G [] .nm) : System := ⟨{countSpawn ω}, single blockerRow⟩

/-- The firing of the count-checked rule alone, making identity `1`. -/
abbrev countFiring (ω : G [] .nm) :
    RuleSyntax.Firing ℕ decl ({countSpawn ω} : Prog) (single blockerRow).frame :=
  RuleSyntax.Contextual.canonical (F := (single blockerRow).frame) (countSpawn ω) (Set.mem_singleton _)
    ⟨[], [], [1]⟩ []

theorem count_information (ω : G [] .nm) :
    (countFiring ω).information knowledge (single blockerRow) = [] := rfl

theorem count_admitted (ω : G [] .nm) : (countFiring ω).Admits knowledge (single blockerRow) := by
  refine ⟨⟨canonical_fresh_knowledge _ (countSpawn ω) _ _ _, List.nodup_nil, List.nodup_singleton 1, rfl,
    rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
  · change Enabled (fun _ : ℕ => ()) ({0} : Finset ℕ) ((⟨[], [], [1]⟩ : Selection ℕ).commit (T := Unit))
    decide
  · refine ⟨groundFrame, someGrounding _, ?_⟩
    rw [count_information]
    exact fun e inside => nomatch inside
  · intro b σ _
    refine ⟨fun c inside => ?_, fun q inside => nomatch inside⟩
    change c ∈ [Check.map (knowledge.act (countFiring ω).opening)
      (Check.count (ByInstantiation.obs blockerRow) 1)] at inside
    rw [List.mem_singleton] at inside
    subst inside
    show (RuleSyntax.matchesAt knowledge σ ((countFiring ω).row knowledge (single blockerRow))
      (single blockerRow).present
        (knowledge.act (countFiring ω).opening (ByInstantiation.obs blockerRow))).card = 1
    have only : RuleSyntax.matchesAt knowledge σ ((countFiring ω).row knowledge (single blockerRow))
        (single blockerRow).present
          (knowledge.act (countFiring ω).opening (ByInstantiation.obs blockerRow)) = {0} := by
      ext o
      rw [RuleSyntax.mem_matchesAt]
      constructor
      · exact fun ⟨present, _⟩ => present
      · intro present
        refine ⟨present, ?_⟩
        rw [Finset.mem_singleton.mp present]
        exact equal_of_grounds (o := ByInstantiation.obs blockerRow)
          (fun g => ground_back₃ (countFiring ω).opening σ g (ByInstantiation.obs blockerRow))
          (fun g => ground_back₃ (decl.weaken (countFiring ω).ext) σ g (ByInstantiation.obs blockerRow))
    rw [only]
    rfl

/-- **Alone, the count-checked system succeeds**: one row `*@0`, the rule fires and makes `ω!(0)`. -/
theorem countSystem_succeeds (ω : G [] .nm) : (stepParallelSolvable ω).Succeeds (countSystem ω) := by
  refine ⟨⟨{countSpawn ω}, (countFiring ω).result knowledge (single blockerRow)⟩,
    .single ⟨rfl, countFiring ω, count_admitted ω, rfl⟩, ?_⟩
  refine outBarb_of_ground (o := 1) ?_ ?_ ?_
  · change 1 ∈ fire (single blockerRow).present ((⟨[], [], [1]⟩ : Selection ℕ).commit (T := Unit))
    rw [mem_fire]
    exact .inr (by simp [Selection.commit])
  · intro e inside
    change e ∈ (countFiring ω).information knowledge (single blockerRow) at inside
    rw [count_information] at inside
    exact nomatch inside
  · show instantiateObservation (someGrounding _)
      (instantiateObservation (RuleSyntax.Contextual.canonicalOpening sig groundFrame groundFrame)
        (ByInstantiation.obs (successRow ω))) = _
    exact ground_back _ _ _

/-- The two rows `*@0`, side by side, represent `*@0 | *@0`. -/
theorem twoBlockers_represents :
    ByInstantiation.RepresentsBy (tensor (single blockerRow) (single blockerRow))
      (par (ByInstantiation.rowProcess blockerRow (by decide)) (ByInstantiation.rowProcess blockerRow (by decide)))
      (tensorValue (fun _ => blockerRow) (fun _ => blockerRow)) :=
  tensor_represents (ByInstantiation.initial_represents (ByInstantiation.rowProcess blockerRow (by decide)) rfl)
    (ByInstantiation.initial_represents (ByInstantiation.rowProcess blockerRow (by decide)) rfl)
    (fromProcess_par _ _)

/-- Two rows `*@0` show no output barb. -/
theorem twoBlockers_no_barb (ω : G [] .nm) : ¬ OutBarb ω (tensor (single blockerRow) (single blockerRow)) := by
  intro shows
  obtain ⟨o, present, c', q, shape, _⟩ := (outBarb_iff twoBlockers_represents ω).mp shows
  rcases mem_tensor.mp present with ⟨k, _, rfl⟩ | ⟨k, _, rfl⟩
  · rw [tensorValue_even] at shape
    cases shape
  · rw [tensorValue_odd] at shape
    cases shape

/-- **Beside a second `*@0`, the count-checked rule is refused**: two rows match its pattern at every
solution. -/
theorem count_blocked (ω : G [] .nm)
    (f : RuleSyntax.Firing ℕ decl (({countSpawn ω} : Prog) ∪ ∅)
      (tensor (single blockerRow) (single blockerRow)).frame) :
    ¬ f.Admits knowledge (tensor (single blockerRow) (single blockerRow)) := by
  obtain ⟨rule, member, ext, opening, selection, seen⟩ := f
  have isCount : rule = countSpawn ω := by
    rcases member with inside | inside
    · exact inside
    · exact inside.elim
  subst isCount
  rintro ⟨_, _, _, entails⟩
  have information : RuleSyntax.Firing.information knowledge (tensor (single blockerRow) (single blockerRow))
      ⟨countSpawn ω, member, ext, opening, selection, seen⟩ = [] := rfl
  have holds := entails groundFrame (someGrounding (decl.target ext)) (by
    intro e inside
    rw [information] at inside
    exact nomatch inside)
  have counted : (RuleSyntax.matchesAt knowledge (b := groundFrame) (someGrounding (decl.target ext))
      (RuleSyntax.Firing.row knowledge (tensor (single blockerRow) (single blockerRow))
        ⟨countSpawn ω, member, ext, opening, selection, seen⟩)
      (tensor (single blockerRow) (single blockerRow)).present
      (knowledge.act opening (ByInstantiation.obs blockerRow))).card = 1 :=
    holds.1 (.count (knowledge.act opening (ByInstantiation.obs blockerRow)) 1) (List.mem_singleton_self _)
  have both : ({0, 1} : Finset ℕ) ⊆ RuleSyntax.matchesAt knowledge (b := groundFrame)
      (someGrounding (decl.target ext))
      (RuleSyntax.Firing.row knowledge (tensor (single blockerRow) (single blockerRow))
        ⟨countSpawn ω, member, ext, opening, selection, seen⟩)
      (tensor (single blockerRow) (single blockerRow)).present
      (knowledge.act opening (ByInstantiation.obs blockerRow)) := by
    intro o inside
    rw [RuleSyntax.mem_matchesAt]
    rcases Finset.mem_insert.mp inside with rfl | inside'
    · refine ⟨mem_tensor.mpr (.inl ⟨0, Finset.mem_singleton_self 0, rfl⟩), ?_⟩
      have label : (tensor (single blockerRow) (single blockerRow)).label 0 =
          knowledge.act (leftIn (single blockerRow).frame (single blockerRow).frame)
            (ByInstantiation.obs blockerRow) :=
        tensor_label_even (single blockerRow) (single blockerRow) 0
      show knowledge.E _ (knowledge.act (b := groundFrame) (someGrounding _) (knowledge.act (decl.weaken ext)
        ((tensor (single blockerRow) (single blockerRow)).label 0)))
      rw [label]
      exact equal_of_grounds (o := ByInstantiation.obs blockerRow)
        (fun g => ground_back₃ opening (someGrounding (decl.target ext)) g (ByInstantiation.obs blockerRow))
        (fun g => ground_back₄ (leftIn (single blockerRow).frame (single blockerRow).frame)
          (decl.weaken ext) (someGrounding (decl.target ext)) g (ByInstantiation.obs blockerRow))
    · rw [Finset.mem_singleton.mp inside']
      refine ⟨mem_tensor.mpr (.inr ⟨0, Finset.mem_singleton_self 0, rfl⟩), ?_⟩
      have label : (tensor (single blockerRow) (single blockerRow)).label 1 =
          knowledge.act (rightIn (single blockerRow).frame (single blockerRow).frame)
            (ByInstantiation.obs blockerRow) :=
        tensor_label_odd (single blockerRow) (single blockerRow) 0
      show knowledge.E _ (knowledge.act (b := groundFrame) (someGrounding _) (knowledge.act (decl.weaken ext)
        ((tensor (single blockerRow) (single blockerRow)).label 1)))
      rw [label]
      exact equal_of_grounds (o := ByInstantiation.obs blockerRow)
        (fun g => ground_back₃ opening (someGrounding (decl.target ext)) g (ByInstantiation.obs blockerRow))
        (fun g => ground_back₄ (rightIn (single blockerRow).frame (single blockerRow).frame)
          (decl.weaken ext) (someGrounding (decl.target ext)) g (ByInstantiation.obs blockerRow))
  have bound := Finset.card_le_card both
  rw [counted] at bound
  exact absurd bound (by decide)

/-- **A count check is switched off by a composable neighbour.** The count-checked rule has no
collect pattern and a check that is not an equation; its system and the system holding the row `*@0`
are composable; alone it succeeds; side by side it never does. -/
theorem count_switched (ω : G [] .nm) :
    (countSpawn ω).collect = [] ∧ (∃ c ∈ (countSpawn ω).body.checks, ∀ l l', c ≠ Check.equal l l') ∧
      (stepParallelSolvable ω).composable (countSystem ω) blockerSystem ∧
      (stepParallelSolvable ω).Succeeds (countSystem ω) ∧
      ¬ (stepParallelSolvable ω).Succeeds ((stepParallelSolvable ω).par (countSystem ω) blockerSystem) := by
  refine ⟨rfl, ⟨_, List.mem_singleton_self _, fun l l' same => by cases same⟩, ?_, countSystem_succeeds ω,
    never_succeeds_of_stuck (count_blocked ω) (twoBlockers_no_barb ω)⟩
  refine (ByInstantiation.solvable_iff _).mpr ⟨someGrounding _, ?_⟩
  intro e member
  change e ∈ knowledge.applyStore _ ([] : List _) ++ knowledge.applyStore _ ([] : List _) at member
  simp [Interface.Frames.applyStore] at member

/-! ## A collect pattern -/

/-- The collect pattern of the collect query rule: the rule's one unknown. -/
abbrev collectPattern : Observation sig payloadFrame.arity := ⟨[], .pr, payloadUnknown⟩

/-- **Make `ω!(0)`, reporting the rows that match the rule's unknown**: no check, one collect pattern. -/
abbrev collectSpawn (ω : G [] .nm) : RuleSyntax.Rule (RuleSyntax.Contextual.Terms sig) where
  locals := payloadFrame
  body := { take := [], read := [], tell := [], checks := [],
            produce := [ByInstantiation.obs (embed (successRow ω))] }
  collect := [collectPattern]

/-- The system of the collect query rule, with no row. -/
def collectSystem (ω : G [] .nm) : System := ⟨{collectSpawn ω}, emptyState⟩

/-- The firing of the collect query rule alone, reporting no row and making identity `0`. -/
abbrev collectFiring (ω : G [] .nm) :
    RuleSyntax.Firing ℕ decl ({collectSpawn ω} : Prog) emptyState.frame :=
  RuleSyntax.Contextual.canonical (F := emptyState.frame) (collectSpawn ω) (Set.mem_singleton _)
    ⟨[], [], [0]⟩ [∅]

theorem collect_information (ω : G [] .nm) :
    (collectFiring ω).information knowledge emptyState = [] := rfl

theorem collect_admitted (ω : G [] .nm) : (collectFiring ω).Admits knowledge emptyState := by
  refine ⟨⟨canonical_fresh_knowledge _ (collectSpawn ω) _ _ _, List.nodup_nil, List.nodup_singleton 0, rfl,
    rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
  · change Enabled (fun _ : ℕ => ()) (∅ : Finset ℕ) ((⟨[], [], [0]⟩ : Selection ℕ).commit (T := Unit))
    decide
  · refine ⟨groundFrame, someGrounding _, ?_⟩
    rw [collect_information]
    exact fun e inside => nomatch inside
  · intro b σ _
    refine ⟨fun c inside => (nomatch inside), fun q inside => ?_⟩
    change q ∈ [(knowledge.act (collectFiring ω).opening collectPattern, (∅ : Finset ℕ))] at inside
    rw [List.mem_singleton] at inside
    subst inside
    show RuleSyntax.matchesAt knowledge σ _ (∅ : Finset ℕ) _ = ∅
    ext o
    rw [RuleSyntax.mem_matchesAt]
    simp

/-- **Alone, the collect query system succeeds**: no row, the rule reports none and makes `ω!(0)`. -/
theorem collectSystem_succeeds (ω : G [] .nm) : (stepParallelSolvable ω).Succeeds (collectSystem ω) := by
  refine ⟨⟨{collectSpawn ω}, (collectFiring ω).result knowledge emptyState⟩,
    .single ⟨rfl, collectFiring ω, collect_admitted ω, rfl⟩, ?_⟩
  refine outBarb_of_ground (o := 0) ?_ ?_ ?_
  · change 0 ∈ fire (∅ : Finset ℕ) ((⟨[], [], [0]⟩ : Selection ℕ).commit (T := Unit))
    rw [mem_fire]
    exact .inr (by simp [Selection.commit])
  · intro e inside
    change e ∈ (collectFiring ω).information knowledge emptyState at inside
    rw [collect_information] at inside
    exact nomatch inside
  · show (⟨[], .pr, instantiate (someGrounding _) (instantiate (collectFiring ω).opening
        (embed (successRow ω)))⟩ : Observation sig ByInstantiation.noUnknowns) = _
    rw [instantiate_embed, instantiate_embed, embed_ground]

/-- **Beside the row `*@0`, the collect query rule is refused**: the pattern is the rule's own unknown, so
whether it sees the row depends on the solution, and freshness of the opening gives a solution where
it does and one where it does not; no report holds at both. -/
theorem collect_blocked (ω : G [] .nm)
    (f : RuleSyntax.Firing ℕ decl (({collectSpawn ω} : Prog) ∪ ∅)
      (tensor emptyState (single blockerRow)).frame) :
    ¬ f.Admits knowledge (tensor emptyState (single blockerRow)) := by
  obtain ⟨rule, member, ext, opening, selection, seen⟩ := f
  have isCollect : rule = collectSpawn ω := by
    rcases member with inside | inside
    · exact inside
    · exact inside.elim
  subst isCollect
  rintro ⟨⟨fresh, _, _, _, _, _, collectLength⟩, _, _, entails⟩
  obtain ⟨reported, rfl⟩ : ∃ reported, seen = [reported] := by
    match seen, collectLength with
    | [reported], _ => exact ⟨reported, rfl⟩
  have information : RuleSyntax.Firing.information knowledge (tensor emptyState (single blockerRow))
      ⟨collectSpawn ω, member, ext, opening, selection, [reported]⟩ = [] := rfl
  have solved : ∀ u : Assignment (decl.target ext).arity groundFrame.arity,
      knowledge.Models u (RuleSyntax.Firing.information knowledge (tensor emptyState (single blockerRow))
        ⟨collectSpawn ω, member, ext, opening, selection, [reported]⟩) := by
    intro u e inside
    rw [information] at inside
    exact nomatch inside
  have present : (1 : ℕ) ∈ (tensor emptyState (single blockerRow)).present :=
    mem_tensor.mpr (.inr ⟨0, Finset.mem_singleton_self 0, rfl⟩)
  have mentioned : (tensor emptyState (single blockerRow)).Mentions
      ((tensor emptyState (single blockerRow)).label 1) := Or.inr (Or.inr ⟨1, present, rfl⟩)
  have label : instantiateObservation (someGrounding _) ((tensor emptyState (single blockerRow)).label 1) =
      ByInstantiation.obs blockerRow := by
    rw [show (tensor emptyState (single blockerRow)).label 1 =
      knowledge.act (rightIn emptyState.frame (single blockerRow).frame) (ByInstantiation.obs blockerRow) from
        tensor_label_odd emptyState (single blockerRow) 0]
    exact ground_back (rightIn emptyState.frame (single blockerRow).frame)
      (someGrounding (tensor emptyState (single blockerRow)).frame) (ByInstantiation.obs blockerRow)
  have inTerms : collectPattern ∈ (collectSpawn ω).terms := by
    simp [RuleSyntax.Rule.terms]
  have symm := fun {x y : Observation sig groundFrame.arity} (same : knowledge.E x y) =>
    (knowledge.equivalence groundFrame).symm same
  have trans := fun {x y z : Observation sig groundFrame.arity} (one : knowledge.E x y)
    (two : knowledge.E y z) => (knowledge.equivalence groundFrame).trans one two
  -- a solution where the pattern is `*@0`: the row is seen
  obtain ⟨u₁, onState₁, onRule₁⟩ := fresh groundFrame (someGrounding _) (fun _ => dropqT zeroT)
  have seen₁ : 1 ∈ reported := by
    have reports : RuleSyntax.matchesAt knowledge (b := groundFrame) u₁
        (RuleSyntax.Firing.row knowledge (tensor emptyState (single blockerRow))
          ⟨collectSpawn ω, member, ext, opening, selection, [reported]⟩)
        (tensor emptyState (single blockerRow)).present (knowledge.act opening collectPattern) = reported :=
      (entails groundFrame u₁ (solved u₁)).2 (knowledge.act opening collectPattern, reported)
        (List.mem_singleton_self _)
    rw [← reports, RuleSyntax.mem_matchesAt]
    refine ⟨present, trans (onRule₁ collectPattern inTerms) (symm (trans (onState₁ _ mentioned) ?_))⟩
    show knowledge.E (instantiateObservation (someGrounding _) ((tensor emptyState (single blockerRow)).label 1))
      (instantiateObservation (fun _ => dropqT zeroT : Assignment payloadFrame.arity groundFrame.arity)
        collectPattern)
    rw [label]
    exact equal_of_grounds (o := ByInstantiation.obs blockerRow)
      (fun g => ByInstantiation.instantiateObservation_ground g _)
      (fun g => by
        show instantiateObservation g ⟨[], .pr, instantiate (fun _ => dropqT zeroT :
          Assignment payloadFrame.arity groundFrame.arity) payloadUnknown⟩ = _
        rw [instantiate_generator]
        exact ByInstantiation.instantiateObservation_ground g _)
  -- a solution where the pattern is `0`: the row is not seen
  obtain ⟨u₂, onState₂, onRule₂⟩ := fresh groundFrame (someGrounding _) (fun _ => zeroT)
  have unseen₂ : 1 ∉ reported := by
    have reports : RuleSyntax.matchesAt knowledge (b := groundFrame) u₂
        (RuleSyntax.Firing.row knowledge (tensor emptyState (single blockerRow))
          ⟨collectSpawn ω, member, ext, opening, selection, [reported]⟩)
        (tensor emptyState (single blockerRow)).present (knowledge.act opening collectPattern) = reported :=
      (entails groundFrame u₂ (solved u₂)).2 (knowledge.act opening collectPattern, reported)
        (List.mem_singleton_self _)
    rw [← reports, RuleSyntax.mem_matchesAt]
    rintro ⟨_, equal⟩
    have zeroDrop := trans (symm (onRule₂ collectPattern inTerms)) (trans equal (onState₂ _ mentioned))
    have similar := zeroDrop (fun e => nomatch e)
    change ObsSimilar
      (instantiateObservation (fun e => nomatch e : Grounding groundFrame)
        (instantiateObservation (fun _ => zeroT : Assignment payloadFrame.arity groundFrame.arity)
          collectPattern))
      (instantiateObservation (fun e => nomatch e : Grounding groundFrame)
        (instantiateObservation (someGrounding _) ((tensor emptyState (single blockerRow)).label 1)))
      at similar
    rw [label, ByInstantiation.instantiateObservation_ground] at similar
    change ObsSimilar
      (instantiateObservation (fun e => nomatch e : Grounding groundFrame)
        ⟨[], .pr, instantiate (fun _ => zeroT : Assignment payloadFrame.arity groundFrame.arity)
          payloadUnknown⟩)
      (ByInstantiation.obs blockerRow) at similar
    rw [instantiate_generator, ByInstantiation.instantiateObservation_ground] at similar
    exact zero_not_similar_drop (ByInstantiation.obsSimilar_closed.mp similar)
  exact unseen₂ seen₁

/-- **A collect pattern is switched off by a composable neighbour.** The collect query rule has no check and
one collect pattern; its system and the system holding the row `*@0` are composable; alone it
succeeds; side by side it never does. -/
theorem collect_switched (ω : G [] .nm) :
    (collectSpawn ω).body.checks = [] ∧ (collectSpawn ω).collect ≠ [] ∧
      (stepParallelSolvable ω).composable (collectSystem ω) blockerSystem ∧
      (stepParallelSolvable ω).Succeeds (collectSystem ω) ∧
      ¬ (stepParallelSolvable ω).Succeeds ((stepParallelSolvable ω).par (collectSystem ω) blockerSystem) := by
  refine ⟨rfl, by simp, ?_, collectSystem_succeeds ω,
    never_succeeds_of_stuck (collect_blocked ω) (blocked_no_barb ω)⟩
  refine (ByInstantiation.solvable_iff _).mpr ⟨someGrounding _, ?_⟩
  intro e member
  change e ∈ knowledge.applyStore _ ([] : List _) ++ knowledge.applyStore _ ([] : List _) at member
  simp [Interface.Frames.applyStore] at member

#print axioms ground_back₄
#print axioms equal_of_grounds
#print axioms zero_not_similar_drop
#print axioms never_succeeds_of_stuck
#print axioms stuck_of_empty
#print axioms outBarb_of_ground
#print axioms eater_admitted
#print axioms eater_result_empty
#print axioms neighbour_rule_takes_success_row
#print axioms count_admitted
#print axioms countSystem_succeeds
#print axioms twoBlockers_no_barb
#print axioms count_blocked
#print axioms count_switched
#print axioms collect_admitted
#print axioms collectSystem_succeeds
#print axioms collect_blocked
#print axioms collect_switched

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings
