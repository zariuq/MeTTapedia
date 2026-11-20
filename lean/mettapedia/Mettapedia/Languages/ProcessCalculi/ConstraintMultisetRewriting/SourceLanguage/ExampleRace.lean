import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Toolkit
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Outcomes
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Worlds

/-!
# Two alternatives that share a space: a set of bags, or alternatives as worlds

Over the empty program and an empty space at the address `s0`, the queries

* p6: `(choice (add s0 a (ret 1)) (query s0 a (ret 2)))`, the addition written first;
* p7: `(choice (query s0 a (ret 2)) (add s0 a (ret 1)))`, the query written first.

**In the reference semantics** (alternatives share the world) the alternatives race on the space
(`race_at_choice`). A run that moves the addition first ends with the bag `{2, 1}`, one that moves the
query first with `{1}` (`race`): both bags are what p6 answers (`p6_outcomes`). The two alternatives
of a `choice` form a bag, so p6 and p7 reach the same configuration in one step and have the same set
of outcomes (`outcomes_swap`).

**Alternatives as worlds** (`Worlds`): each alternative sees the space as it was when the `choice`
made it, empty, so the query finds nothing and both p6 and p7 end with the bag `{1}`
(`worlds_p6`, `worlds_p7`).

**Measured** (one query per file, with `new-space` for the address): real HE answers p6 with `[1]`
and p7 with `[2, 1]`; the engine's HE lane answers p6 with `[1, 2]` and p7 with `[1]`. Each answer is
one of the bags of the shared semantics, so each implementation is one schedule of it; each
implementation answers one of the two queries with `2`, which alternatives as worlds never gives.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleRace

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Elaboration Toolkit SharedWorld Worlds

abbrev D : Discipline MSig [] () := ⟨MTy, fun _ _ => True⟩

/-- The empty program. -/
def program : Program mkeys [] () MTy := ⟨[], fun t => .apply t⟩

def supply : ℕ → MClosed := fun _ => csym "fresh"

/-- The address of the space. -/
def h0 : MClosed := csym "s0"

def H : MData := Rigid.includeTerm (fam mkeys) h0

def a : MData := sym "a"

def addAlt : Comp mkeys [] () MTy := .add H a (.ret (num 1))
def queryAlt : Comp mkeys [] () MTy := .query H a (.ret (num 2))

/-- p6: the addition written first. -/
def query6 : Comp mkeys [] () MTy := .choice addAlt queryAlt

/-- p7: the query written first. -/
def query7 : Comp mkeys [] () MTy := .choice queryAlt addAlt

def start6 : Config mkeys [] () MTy := Config.initial (fun _ => 0) query6
def start7 : Config mkeys [] () MTy := Config.initial (fun _ => 0) query7

theorem query6_wellFormed : QueryWellFormed program [7] query6 := by decide
theorem query7_wellFormed : QueryWellFormed program [7] query7 := by decide

theorem H_determined : Determines ([] : List (Constraint mkeys [] ())) H h0 :=
  ⟨live_nil, fun _ σ _ => Rigid.instantiate_include σ h0⟩

def W0 : World mkeys [] () := ⟨0, 0, fun _ => 0⟩

def row : Row mkeys [] () := ⟨a, []⟩

/-- The space after the addition. -/
noncomputable def S1 : MClosed → Multiset (Row mkeys [] ()) :=
  setSpace (fun _ => 0) h0 ((fun _ : MClosed => (0 : Multiset (Row mkeys [] ()))) h0 + {row})

theorem S1_at : S1 h0 = {row} := by
  simp only [S1, setSpace_same, zero_add]

def bAdd : Branch mkeys [] () MTy := ⟨[], .eval addAlt, [], []⟩
def bQuery : Branch mkeys [] () MTy := ⟨[], .eval queryAlt, [], []⟩
def bRet1 : Branch mkeys [] () MTy := ⟨[], .eval (.ret (num 1)), [], []⟩
def bOne : Branch mkeys [] () MTy := ⟨[], .value (num 1), [], []⟩

def K2 : List (Constraint mkeys [] ()) := [] ++ rowUse 0 row a
def bRet2 : Branch mkeys [] () MTy := ⟨K2, .eval (.ret (num 2)), [], []⟩
def bTwo : Branch mkeys [] () MTy := ⟨K2, .value (num 2), [], []⟩

theorem K2_live : Solvable K2 :=
  ⟨Empty, noNames, closeNames [] (csym "a"), fun e member => by
    simp only [K2, rowUse, copyStore, row, List.map_nil, List.nil_append, List.mem_singleton] at member
    subst member
    rfl⟩

/-! ## The shared world -/

/-- After the `choice`: the two alternatives, a bag. -/
def C1 : Config mkeys [] () MTy := ⟨W0, bAdd ::ₘ bQuery ::ₘ 0⟩

/-- **A race**: the addition writes the space the query reads. -/
theorem race_at_choice : Race (D := D) C1 :=
  ⟨bAdd, bQuery, 0, h0, rfl, live_nil, live_nil, ⟨H, a, .ret (num 1), .inl rfl, H_determined⟩,
    ⟨H, a, .ret (num 2), .inl rfl, H_determined⟩⟩

theorem step6 : Step D program supply start6 C1 :=
  Step.of_eq (D := D) (P := program) (supply := supply) (b := ⟨[], .eval query6, [], []⟩) (rest := 0) rfl
    (by rfl) live_nil (.choice W0 [] _ _ [] [])

theorem step7 : Step D program supply start7 C1 :=
  Step.of_eq (D := D) (P := program) (supply := supply) (b := ⟨[], .eval query7, [], []⟩) (rest := 0) rfl
    (by rw [add_zero]; exact Multiset.cons_swap _ _ _) live_nil (.choice W0 [] _ _ [] [])

noncomputable def finalA : Config mkeys [] () MTy := ⟨⟨1, 0, S1⟩, bTwo ::ₘ bOne ::ₘ 0⟩

/-- The addition moves first; the query sees the row. -/
theorem runsA : Runs D program supply C1 finalA := by
  show Runs D program supply C1 ⟨⟨1, 0, S1⟩, bTwo ::ₘ bOne ::ₘ 0⟩
  refine Relation.ReflTransGen.tail (b := ⟨⟨1, 0, S1⟩, bTwo ::ₘ bRet1 ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := program) (supply := supply) (b := bRet1) (rest := bTwo ::ₘ 0) (bs := bOne ::ₘ 0)
      (Multiset.cons_swap _ _ _) (by rw [Multiset.cons_add, zero_add, Multiset.cons_swap]) live_nil
      (.ret _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨1, 0, S1⟩, bRet2 ::ₘ bRet1 ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := program) (supply := supply) (b := bRet2) (rest := bRet1 ::ₘ 0) (bs := bTwo ::ₘ 0)
      rfl (by rw [Multiset.cons_add, zero_add]) K2_live (.ret _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨0, 0, S1⟩, bQuery ::ₘ bRet1 ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := program) (supply := supply) (b := bQuery) (rest := bRet1 ::ₘ 0) rfl
      (by
        show bRet2 ::ₘ bRet1 ::ₘ 0 = ((S1 h0).map fun r =>
          (⟨[] ++ rowUse 0 r a, .eval (.ret (num 2)), [], []⟩ : Branch mkeys [] () MTy)) + (bRet1 ::ₘ 0)
        rw [S1_at, Multiset.map_singleton, Multiset.singleton_add]
        rfl)
      live_nil (.query ⟨0, 0, S1⟩ [] H a (.ret (num 2)) [] [] h0 H_determined))
  exact Relation.ReflTransGen.single
    (Step.of_eq (D := D) (P := program) (supply := supply) (b := bAdd) (rest := bQuery ::ₘ 0) (bs := bRet1 ::ₘ 0)
      rfl (by rw [Multiset.cons_add, zero_add, Multiset.cons_swap]) live_nil
      (.add W0 [] H a (.ret (num 1)) [] [] h0 H_determined))

noncomputable def finalB : Config mkeys [] () MTy := ⟨⟨1, 0, S1⟩, bOne ::ₘ 0⟩

/-- The query moves first and sees an empty space. -/
theorem runsB : Runs D program supply C1 finalB := by
  show Runs D program supply C1 ⟨⟨1, 0, S1⟩, bOne ::ₘ 0⟩
  refine Relation.ReflTransGen.tail (b := ⟨⟨1, 0, S1⟩, bRet1 ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := program) (supply := supply) (b := bRet1) (rest := 0) (bs := bOne ::ₘ 0) rfl
      (by rw [add_zero]) live_nil (.ret _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨1, 0, fun _ => 0⟩, bAdd ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := program) (supply := supply) (b := bAdd) (rest := 0) (bs := bRet1 ::ₘ 0) rfl
      (by rw [add_zero]) live_nil (.add ⟨1, 0, fun _ => 0⟩ [] H a (.ret (num 1)) [] [] h0 H_determined))
  exact Relation.ReflTransGen.single
    (Step.of_eq (D := D) (P := program) (supply := supply) (b := bQuery) (rest := bAdd ::ₘ 0)
      (Multiset.cons_swap _ _ _)
      (by
        show bAdd ::ₘ 0 = (((fun _ : MClosed => (0 : Multiset (Row mkeys [] ()))) h0).map fun r =>
          (⟨[] ++ rowUse 0 r a, .eval (.ret (num 2)), [], []⟩ : Branch mkeys [] () MTy)) + (bAdd ::ₘ 0)
        rw [Multiset.map_zero, zero_add])
      live_nil (.query W0 [] H a (.ret (num 2)) [] [] h0 H_determined))

theorem bOne_finished : Branch.Finished (D := D) bOne := ⟨rfl, _, rfl⟩
theorem bTwo_finished : Branch.Finished (D := D) bTwo := ⟨rfl, _, rfl⟩

theorem finalA_quiescent : Config.Quiescent (D := D) program supply finalA :=
  Config.quiescent_of_finished fun b member _ => by
    have member' : b ∈ bTwo ::ₘ bOne ::ₘ 0 := member
    simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at member'
    rcases member' with rfl | rfl
    · exact bTwo_finished
    · exact bOne_finished

theorem finalB_quiescent : Config.Quiescent (D := D) program supply finalB :=
  Config.quiescent_of_finished fun b member _ => by
    have member' : b ∈ bOne ::ₘ 0 := member
    simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at member'
    subst member'
    exact bOne_finished

theorem one_answer : Branch.answer (D := D) bOne = {cnum 1} :=
  answer_of_determines rfl ⟨live_nil, fun _ _ _ => rfl⟩

theorem two_answer : Branch.answer (D := D) bTwo = {cnum 2} :=
  answer_of_determines rfl ⟨K2_live, fun _ _ _ => rfl⟩

theorem answersA : Config.answers (D := D) finalA = {{cnum 2}, {cnum 1}} := by
  show Config.answers (D := D) (⟨⟨1, 0, S1⟩, bTwo ::ₘ bOne ::ₘ 0⟩ : Config mkeys [] () MTy) = _
  rw [answers_cons_finished (D := D) bTwo_finished K2_live,
    answers_cons_finished (D := D) bOne_finished live_nil, answers_zero, one_answer, two_answer]
  rfl

theorem answersB : Config.answers (D := D) finalB = {{cnum 1}} := by
  show Config.answers (D := D) (⟨⟨1, 0, S1⟩, bOne ::ₘ 0⟩ : Config mkeys [] () MTy) = _
  rw [answers_cons_finished (D := D) bOne_finished live_nil, answers_zero, one_answer]
  rfl

/-- **The race**: one well-formed query, two runs that both end, two different bags of answers. -/
theorem race :
    Runs D program supply start6 finalA ∧ Config.Quiescent (D := D) program supply finalA ∧
      Runs D program supply start6 finalB ∧ Config.Quiescent (D := D) program supply finalB ∧
      Config.answers (D := D) finalA = {{cnum 2}, {cnum 1}} ∧ Config.answers (D := D) finalB = {{cnum 1}} ∧
      Config.answers (D := D) finalA ≠ Config.answers (D := D) finalB := by
  refine ⟨(Relation.ReflTransGen.single step6).trans runsA, finalA_quiescent,
    (Relation.ReflTransGen.single step6).trans runsB, finalB_quiescent, answersA, answersB, ?_⟩
  rw [answersA, answersB]
  intro same
  have := congrArg Multiset.card same
  simp at this

/-- **Both bags are what p6 answers.** -/
theorem p6_outcomes :
    {{cnum 2}, {cnum 1}} ∈ Outcomes D program supply start6 ∧ {{cnum 1}} ∈ Outcomes D program supply start6 :=
  ⟨⟨finalA, (Relation.ReflTransGen.single step6).trans runsA, finalA_quiescent, answersA⟩,
    ⟨finalB, (Relation.ReflTransGen.single step6).trans runsB, finalB_quiescent, answersB⟩⟩

/-- A step, unfolded (for any discipline and program over MeTTa data). -/
theorem step_cases {D' : Discipline MSig [] ()} {P' : Program mkeys [] () D'.Ty} {supply' : ℕ → MClosed}
    {C₀ C : Config mkeys [] () D'.Ty} (step : Step D' P' supply' C₀ C) :
    ∃ w w' b rest bs, C₀ = ⟨w, b ::ₘ rest⟩ ∧ C = ⟨w', bs + rest⟩ ∧ Move D' P' supply' w b w' bs := by
  cases step with
  | move w w' b rest bs _ moved => exact ⟨w, w', b, rest, bs, rfl, rfl, moved⟩

/-- A `choice` moves only by splitting. -/
theorem choice_move {D' : Discipline MSig [] ()} {P' : Program mkeys [] () D'.Ty} {supply' : ℕ → MClosed}
    {w w' : World mkeys [] ()} {K : List (Constraint mkeys [] ())} {c d : Comp mkeys [] () D'.Ty}
    {fs : List (Frame mkeys [] () D'.Ty)} {ps : List (MData × Comp mkeys [] () D'.Ty)}
    {bs : Multiset (Branch mkeys [] () D'.Ty)} (moved : Move D' P' supply' w ⟨K, .eval (.choice c d), fs, ps⟩ w' bs) :
    w' = w ∧ bs = {⟨K, .eval c, fs, ps⟩, ⟨K, .eval d, fs, ps⟩} := by
  cases moved
  exact ⟨rfl, rfl⟩

/-- The only step from the start of a `choice` is the `choice`. -/
theorem step_from_start {C₀ C : Config mkeys [] () MTy} (c d : Comp mkeys [] () MTy)
    (step : Step D program supply C₀ C) (at_start : C₀ = Config.initial (fun _ => 0) (.choice c d)) :
    C = ⟨W0, ⟨[], .eval c, [], []⟩ ::ₘ ⟨[], .eval d, [], []⟩ ::ₘ 0⟩ := by
  obtain ⟨w, w', b, rest, bs, rfl, rfl, moved⟩ := step_cases step
  have hw : w = W0 := congrArg Config.world at_start
  have hb : ({⟨[], .eval (.choice c d), [], []⟩} : Multiset (Branch mkeys [] () MTy)) = b ::ₘ rest :=
    (congrArg Config.branches at_start).symm
  obtain ⟨rfl, rfl⟩ := (Multiset.singleton_eq_cons_iff _).mp hb
  subst hw
  obtain ⟨rfl, rfl⟩ := choice_move moved
  rw [add_zero]
  rfl

theorem not_quiescent_start {c d : Comp mkeys [] () MTy} :
    ¬ Config.Quiescent (D := D) program supply (Config.initial (fun _ => 0) (.choice c d)) :=
  fun quiescent => quiescent _ (Multiset.mem_singleton_self _) live_nil _ _ (.choice _ _ _ _ _ _)

/-- Every run from the start of a `choice` stays at the start or passes through the configuration after
its step. -/
theorem runs_through {c d : Comp mkeys [] () MTy} {C : Config mkeys [] () MTy}
    (runs : Runs D program supply (Config.initial (fun _ => 0) (.choice c d)) C) :
    C = Config.initial (fun _ => 0) (.choice c d) ∨
      Runs D program supply ⟨W0, ⟨[], .eval c, [], []⟩ ::ₘ ⟨[], .eval d, [], []⟩ ::ₘ 0⟩ C := by
  rcases Relation.ReflTransGen.cases_head runs with same | ⟨C', first, rest⟩
  · exact .inl same.symm
  · rw [step_from_start c d first rfl] at rest
    exact .inr rest

/-- **The order a `choice` is written in is not observed**: p6 and p7 have the same outcomes. -/
theorem outcomes_swap : Outcomes D program supply start6 = Outcomes D program supply start7 := by
  have swapped : (⟨W0, ⟨[], .eval queryAlt, [], []⟩ ::ₘ ⟨[], .eval addAlt, [], []⟩ ::ₘ 0⟩ :
      Config mkeys [] () MTy) = C1 := by
    show (⟨W0, _⟩ : Config mkeys [] () MTy) = ⟨W0, _⟩
    rw [Multiset.cons_swap]
    rfl
  ext A
  constructor
  · rintro ⟨C, runs, quiescent, answers⟩
    rcases runs_through runs with rfl | through
    · exact absurd quiescent not_quiescent_start
    · exact ⟨C, (Relation.ReflTransGen.single step7).trans through, quiescent, answers⟩
  · rintro ⟨C, runs, quiescent, answers⟩
    rcases runs_through runs with rfl | through
    · exact absurd quiescent not_quiescent_start
    · rw [swapped] at through
      exact ⟨C, (Relation.ReflTransGen.single step6).trans through, quiescent, answers⟩

/-! ## Alternatives as worlds -/

/-- A start as worlds: one alternative, seeing the empty spaces. -/
def wstart (q : Comp mkeys [] () MTy) : WConfig mkeys [] () MTy :=
  ⟨0, 0, fun _ => 0, {⟨⟨[], .eval q, [], []⟩, fun _ => 0, Writes.none⟩}⟩

/-- The writes recorded by a move that changed nothing. -/
noncomputable def still : Writes mkeys [] () := Writes.none.record (fun _ => 0) (fun _ => 0)

/-- After the `choice`, as worlds: both alternatives see the empty space. -/
noncomputable def W1 : WConfig mkeys [] () MTy :=
  ⟨0, 0, fun _ => 0, {⟨bAdd, fun _ => 0, still⟩, ⟨bQuery, fun _ => 0, still⟩}⟩

noncomputable def wfinal : WConfig mkeys [] () MTy :=
  ⟨1, 0, fun _ => 0, ⟨bOne, S1, (still.record (fun _ => 0) S1).record S1 S1⟩ ::ₘ 0⟩

theorem wstep6 : WStep D program supply (wstart query6) W1 :=
  WStep.move (D := D) (P := program) (supply := supply) 0 0 (fun _ => 0)
    ⟨⟨[], .eval query6, [], []⟩, fun _ => 0, Writes.none⟩ 0 W0 _ live_nil
    (Move.choice (D := D) (P := program) (supply := supply) ⟨0, 0, fun _ => 0⟩ [] addAlt queryAlt [] [])

theorem wstep7 : WStep D program supply (wstart query7) W1 := by
  have moved := WStep.move (D := D) (P := program) (supply := supply) 0 0 (fun _ => 0)
    ⟨⟨[], .eval query7, [], []⟩, fun _ => 0, Writes.none⟩ 0 W0 _ live_nil
    (Move.choice (D := D) (P := program) (supply := supply) ⟨0, 0, fun _ => 0⟩ [] queryAlt addAlt [] [])
  have swapped : W1 = ⟨0, 0, fun _ => 0, ⟨bQuery, fun _ => 0, still⟩ ::ₘ ⟨bAdd, fun _ => 0, still⟩ ::ₘ 0⟩ := by
    show (⟨0, 0, fun _ => 0, ⟨bAdd, fun _ => 0, still⟩ ::ₘ ⟨bQuery, fun _ => 0, still⟩ ::ₘ 0⟩ :
      WConfig mkeys [] () MTy) = _
    rw [Multiset.cons_swap]
  rw [swapped]
  exact moved

/-- After the addition, in its own world. -/
noncomputable def Wa : WConfig mkeys [] () MTy :=
  ⟨0, 0, fun _ => 0, ⟨bRet1, S1, still.record (fun _ => 0) S1⟩ ::ₘ ⟨bQuery, fun _ => 0, still⟩ ::ₘ 0⟩

/-- After its `ret`. -/
noncomputable def Wb : WConfig mkeys [] () MTy :=
  ⟨0, 0, fun _ => 0, ⟨bOne, S1, (still.record (fun _ => 0) S1).record S1 S1⟩ ::ₘ ⟨bQuery, fun _ => 0, still⟩ ::ₘ 0⟩

/-- **The worlds run**: the addition writes its own world; the query sees the space as the `choice`
left it, empty, and makes no alternative. -/
theorem wruns : WRuns D program supply W1 wfinal := by
  have add : WStep D program supply W1 Wa :=
    WStep.move (D := D) (P := program) (supply := supply) 0 0 (fun _ => 0)
      ⟨bAdd, fun _ => 0, still⟩ (⟨bQuery, fun _ => 0, still⟩ ::ₘ 0) ⟨0, 0, S1⟩ _ live_nil
      (Move.add (D := D) (P := program) (supply := supply) ⟨0, 0, fun _ => 0⟩ [] H a (.ret (num 1)) [] [] h0
        H_determined)
  have ret : WStep D program supply Wa Wb :=
    WStep.move (D := D) (P := program) (supply := supply) 0 0 (fun _ => 0)
      ⟨bRet1, S1, still.record (fun _ => 0) S1⟩ (⟨bQuery, fun _ => 0, still⟩ ::ₘ 0) ⟨0, 0, S1⟩ _ live_nil
      (Move.ret (D := D) (P := program) (supply := supply) ⟨0, 0, S1⟩ [] (num 1) [] [])
  have query : WStep D program supply
      ⟨0, 0, fun _ => 0, ⟨bQuery, fun _ => 0, still⟩ ::ₘ ⟨bOne, S1, (still.record (fun _ => 0) S1).record S1 S1⟩ ::ₘ 0⟩
      wfinal :=
    WStep.move (D := D) (P := program) (supply := supply) 0 0 (fun _ => 0)
      ⟨bQuery, fun _ => 0, still⟩ (⟨bOne, S1, (still.record (fun _ => 0) S1).record S1 S1⟩ ::ₘ 0) ⟨1, 0, fun _ => 0⟩
      0 live_nil (Move.query (D := D) (P := program) (supply := supply) ⟨0, 0, fun _ => 0⟩ [] H a (.ret (num 2))
        [] [] h0 H_determined)
  have swapped : Wb = ⟨0, 0, fun _ => 0,
      ⟨bQuery, fun _ => 0, still⟩ ::ₘ ⟨bOne, S1, (still.record (fun _ => 0) S1).record S1 S1⟩ ::ₘ 0⟩ := by
    show (⟨0, 0, fun _ => 0, _⟩ : WConfig mkeys [] () MTy) = _
    rw [Multiset.cons_swap]
  exact (Relation.ReflTransGen.single add).trans
    ((Relation.ReflTransGen.single ret).trans (Relation.ReflTransGen.single (swapped ▸ query)))

theorem wfinal_quiescent : WConfig.Quiescent (D := D) program supply wfinal := by
  intro alt member _ w' bs moved
  have only : alt = ⟨bOne, S1, (still.record (fun _ => 0) S1).record S1 S1⟩ := Multiset.mem_singleton.mp member
  subst only
  exact Move.value_still moved

theorem wfinal_answers : wfinal.answers (D := D) = {{cnum 1}} := by
  show Config.answers (D := D) (⟨⟨1, 0, fun _ => 0⟩, {bOne}⟩ : Config mkeys [] () MTy) = _
  rw [answers_singleton (D := D) bOne_finished live_nil, one_answer]

/-- **As worlds, p6 ends with `{1}`.** -/
theorem worlds_p6 :
    WRuns D program supply (wstart query6) wfinal ∧ WConfig.Quiescent (D := D) program supply wfinal ∧
      wfinal.answers (D := D) = {{cnum 1}} :=
  ⟨(Relation.ReflTransGen.single wstep6).trans wruns, wfinal_quiescent, wfinal_answers⟩

/-- **As worlds, p7 ends with `{1}` too.** -/
theorem worlds_p7 :
    WRuns D program supply (wstart query7) wfinal ∧ WConfig.Quiescent (D := D) program supply wfinal ∧
      wfinal.answers (D := D) = {{cnum 1}} :=
  ⟨(Relation.ReflTransGen.single wstep7).trans wruns, wfinal_quiescent, wfinal_answers⟩

/-- **The first worlds step writes nothing, and it is the shared step** (an instance of
`Worlds.wstep_shared`). -/
theorem W1_still : ∀ alt ∈ W1.alts, alt.view = W1.base := by
  intro alt member
  have member' : alt ∈ (⟨bAdd, fun _ => 0, still⟩ : WAlt mkeys [] () MTy) ::ₘ
      (⟨bQuery, fun _ => 0, still⟩ : WAlt mkeys [] () MTy) ::ₘ 0 := member
  rcases Multiset.mem_cons.mp member' with rfl | other
  · rfl
  · rcases Multiset.mem_cons.mp other with rfl | none
    · rfl
    · exact absurd none (Multiset.notMem_zero _)

theorem wstep6_shared : ∃ C', Step D program supply start6 C' ∧ W1 = embed C' :=
  wstep_shared (D := D) (P := program) (supply := supply) (C := start6) (W' := W1)
    (wstep6 : WStep D program supply (embed start6) W1) W1_still

/-- **A step of the shared semantics that writes nothing is a worlds step** (an instance of
`Worlds.step_embed`). -/
theorem step6_embed : WStep D program supply (embed start6) (embed C1) := step_embed step6 rfl

/-- **A copy of a row that two alternatives both remove is removed once** (an instance of
`Worlds.merge_removes_once`): from two copies of `a`, each alternative removed one. -/
theorem removed_once :
    Writes.onto (fun _ => {row, row}) ((⟨fun _ => 0, fun _ => {row}⟩ : Writes mkeys [] ()).merge
      ⟨fun _ => 0, fun _ => {row}⟩) h0 = {row} :=
  merge_removes_once _ h0 row _ _ rfl rfl rfl rfl rfl

#print axioms wstep6_shared
#print axioms step6_embed
#print axioms removed_once
#print axioms race_at_choice
#print axioms race
#print axioms p6_outcomes
#print axioms outcomes_swap
#print axioms worlds_p6
#print axioms worlds_p7

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleRace
