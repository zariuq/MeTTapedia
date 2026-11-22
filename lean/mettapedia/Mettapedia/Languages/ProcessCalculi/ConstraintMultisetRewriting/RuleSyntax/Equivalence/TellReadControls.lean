import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Controls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.ReadLaw

/-!
# Instances and controls of the tell law and the read law, at one frame

## Law 6: a told equation the rule already entails, with kept sides, is a no-op

`entailedTell_congruent` asks that the rule's tells entail the equation and that both its sides be
terms the results keep (`keptTerms`).

* **An instance** (`tell_example`): the rule that tells `x = 5`, and the same rule telling `5 = x` as
  well, differ as syntax and are congruent beside every program, at every state.
* **The equation must be entailed** (`tell_not_entailed_separated`): the rule that reads any row `x`
  and makes `5`, and the same rule telling `x = 5`. Both sides are terms its results keep; its tells
  (none) do not entail the equation; at one row `6` the first moves and the second does not.
* **Its sides must be kept** (`tell_unkept_separated`): the rule that does nothing (`idle`), and the
  same rule telling `y = y`. The equation, a tautology, is entailed by the tells of `idle`, and `y` is
  not a term the results of `idle` keep. Without rows the two programs are not congruent: telling `y = y` reserves the unknown
  it is opened as, so after a context adds the rule that tells `x = 5`, only the other side can bind
  that unknown, and a context that adds a row `y` sees the difference (the mechanism of
  `support_separates`).

## Law 7: reading a row is taking it and making it again

`readTakeMake_congruent` asks for infinitely many identities, and for barbs that see neither a
renaming of identities nor a change modulo the knowledge.

* **An instance** (`read_example`): "read `7`, make `5`" and "take `7`, make `5` and `7`" differ as
  syntax and are congruent beside every program, at every state, with identities `ℕ`.
* **The identities must be infinite** (`read_needs_infinite`): with one identity, at one row `7`,
  the rule that reads `7` moves and the rule that takes `7` and makes it again does not, since its
  made row has no identity absent from the store. The may-barbs keep the other two hypotheses.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.AtOneFrame

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open Mettapedia.Logic.LP
open RuleSyntax.Examples (Tm X E x c fresh_of_ground)
open RuleSyntax.Controls (atoms action)

/-! ## Law 6 -/

/-- **Law 6, an instance**: the rule that tells `x = 5`, and the same rule telling `5 = x` as well,
differ as syntax and are congruent beside every program, at every state. -/
theorem tell_example (Q : Program Tm) (s : State Tm ℕ) :
    withTell tellX (c 5, x) ≠ tellX ∧
      Cong ⟨Q ∪ {withTell tellX (c 5, x)}, s⟩ ⟨Q ∪ {tellX}, s⟩ := by
  refine ⟨fun same => ?_, entailedTell_congruent (r := tellX) (e := (c 5, x))
    (fun related q => mayBarb_modulo related q)
    (fun b _ told => (X.equivalence b).symm (told (x, c 5) (List.mem_singleton_self _)))
    (by simp [keptTerms, tellX]) (by simp [keptTerms, tellX]) Q s⟩
  have lengths := congrArg (fun r : Rule Tm => r.body.tell.length) same
  simp [tellX] at lengths

/-- **Telling `x = 5` stops `readMake` at the row `6`**: the read equates the opened `x` with `6`. -/
theorem told_readMake_stuck : ¬ Moves ⟨∅ ∪ {withTell readMake (x, c 5)}, rowSix⟩ := by
  rintro ⟨T, -, ⟨rule, member, ext, ι, selection, seen⟩, admitted, -⟩
  rcases (Set.mem_union _ _ _).mp member with none | isRule
  · exact Set.notMem_empty _ none
  have same : rule = withTell readMake (x, c 5) := isRule
  subst same
  obtain ⟨-, ⟨-, -, -, readLength, -, -⟩, -, ⟨b, σ, solved⟩, -, -⟩ := (admits_iff _).mp admitted
  obtain ⟨o, read⟩ := List.length_eq_one_iff.mp readLength.symm
  have read' : selection.read = [o] := read
  have told := Firing.tell_solved _ solved (e := (Subst.applyTerm ι x, Subst.applyTerm ι (c 5)))
    List.mem_cons_self
  have equated := Firing.read_solved _ solved (p := Subst.applyTerm ι x) (o := o) (by
    show (Subst.applyTerm ι x, o) ∈ [Subst.applyTerm ι x].zip selection.read
    rw [read']
    exact List.mem_cons_self)
  have five : Subst.applyTerm σ (Subst.applyTerm ι x) = c 5 := told
  have six : Subst.applyTerm σ (Subst.applyTerm ι x) =
      Subst.applyTerm σ (Subst.applyTerm (Subst.id atoms) (c 6)) := equated
  rw [five] at six
  exact absurd (Term.const.inj six) (by decide)

/-- **Law 6 needs the equation to be entailed**: both sides of `x = 5` are terms the results of
`readMake` keep, its tells do not entail the equation, and the rule with and without the tell are not
congruent at the row `6`. The one hypothesis that fails is entailment. -/
theorem tell_not_entailed_separated :
    (x, c 5).1 ∈ keptTerms readMake ∧ (x, c 5).2 ∈ keptTerms readMake ∧
      ¬ X.Entails (a := PUnit.unit) readMake.body.tell (fun b h => X.E (a := b)
        (X.act (a := PUnit.unit) (b := b) h x) (X.act (a := PUnit.unit) (b := b) h (c 5))) ∧
      ¬ Cong ⟨∅ ∪ {withTell readMake (x, c 5)}, rowSix⟩ ⟨∅ ∪ {readMake}, rowSix⟩ := by
  refine ⟨by simp [keptTerms, readMake], by simp [keptTerms, readMake], fun entailed => ?_,
    fun related => told_readMake_stuck (moves_of_congruent related.symm readMake_moves)⟩
  have holds : Subst.applyTerm (fun _ => c 6) x = Subst.applyTerm (fun _ => c 6) (c 5) :=
    entailed PUnit.unit (fun _ => c 6) (fun e inside => absurd inside List.not_mem_nil)
  exact absurd (Term.const.inj holds) (by decide)

/-! ## Law 7 -/

/-- **Law 7, an instance**: "read `7`, make `5`" and "take `7`, make `5` and `7`" differ as syntax and
are congruent beside every program, at every state. -/
theorem read_example (Q : Program Tm) (s : State Tm ℕ) :
    withRead spawn (c 7) ≠ withTakeMake spawn (c 7) ∧
      Cong ⟨Q ∪ {withRead spawn (c 7)}, s⟩ ⟨Q ∪ {withTakeMake spawn (c 7)}, s⟩ := by
  refine ⟨fun same => ?_, readTakeMake_congruent_mayBarb spawn (c 7) Q s⟩
  have lengths := congrArg (fun r : Rule Tm => r.body.read.length) same
  simp [spawn] at lengths

/-- A rule with nothing in it. -/
def idle : Rule Tm := ⟨PUnit.unit, ⟨[], [], [], [], []⟩, []⟩

/-- One row `7` at the one identity. -/
def sevenAtUnit : State Tm Unit := ⟨PUnit.unit, [], {()}, fun _ => c 7⟩

/-- **With one identity, reading the row `7` moves.** -/
theorem read_moves_unit : ∃ T, Reduces X Unit E ⟨∅ ∪ {withRead idle (c 7)}, sevenAtUnit⟩ T := by
  let f : Firing Unit E (∅ ∪ {withRead idle (c 7)}) sevenAtUnit.frame :=
    ⟨withRead idle (c 7), Or.inr (Set.mem_singleton _), PUnit.unit, Subst.id atoms,
      ⟨[], [()], []⟩, []⟩
  have admitted : f.Admits X sevenAtUnit := by
    refine (admits_iff f).mpr ⟨?_, ⟨List.nodup_nil, List.nodup_nil, rfl, rfl, rfl, rfl⟩, ?_, ?_,
      fun check inside => absurd inside List.not_mem_nil,
      fun q inside => absurd inside List.not_mem_nil⟩
    · apply fresh_of_ground action sevenAtUnit f
      intro t member σ
      simp only [f, idle, Rule.terms, List.map_nil, List.flatMap_nil, List.nil_append,
        List.append_nil, List.mem_singleton] at member
      subst member
      rfl
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [f, Selection.commit]
      · simp [f, Selection.commit, sevenAtUnit]
      · simp [f, Selection.commit]
      · simp [f, Selection.commit]
      · intro q inside
        simp [f, Selection.commit] at inside
    · refine ⟨PUnit.unit, Subst.id atoms, fun e inside => ?_⟩
      have unfolded : e ∈ ([] : EquationStore (Term atoms)) ++ [] ++
          [(Subst.applyTerm (Subst.id atoms) (c 7), Subst.applyTerm (Subst.id atoms) (c 7))] ++ [] :=
        inside
      simp only [List.nil_append, List.append_nil, List.mem_singleton] at unfolded
      subst unfolded
      rfl
  exact ⟨_, reduces_of_admits f admitted⟩

/-- **With one identity, taking the row `7` to make it again does not move**: the made row needs an
identity absent from the store, and there is none. -/
theorem takeMake_stuck_unit :
    ¬ ∃ T, Reduces X Unit E ⟨∅ ∪ {withTakeMake idle (c 7)}, sevenAtUnit⟩ T := by
  rintro ⟨T, -, ⟨rule, member, ext, ι, selection, seen⟩, admitted, -⟩
  rcases (Set.mem_union _ _ _).mp member with none | isRule
  · exact Set.notMem_empty _ none
  have same : rule = withTakeMake idle (c 7) := isRule
  subst same
  obtain ⟨-, ⟨-, -, -, -, produceLength, -⟩, enabled, -, -, -⟩ := (admits_iff _).mp admitted
  obtain ⟨m, made⟩ := List.length_eq_one_iff.mp produceLength.symm
  have made' : selection.made = [m] := made
  exact Finset.disjoint_left.mp enabled.fresh (by simp [Selection.commit, made'])
    (Finset.mem_singleton.mpr rfl)

/-- **Law 7 needs infinitely many identities**: with one identity the may-barbs still see neither a
renaming of identities nor a change modulo the knowledge, and at one row `7` the rule that reads `7`
and the rule that takes `7` and makes it again are not congruent. The one hypothesis that fails is
that the identities are infinite. -/
theorem read_needs_infinite :
    (∀ (π : Equiv.Perm Unit) (β : Pattern Tm) (s : State Tm Unit),
        MayBarb X β (renameState π s) ↔ MayBarb X β s) ∧
      (∀ {s t : State Tm Unit}, Modulo X s t → ∀ β, MayBarb X β s → MayBarb X β t) ∧
      ¬ Infinite Unit ∧
      ¬ Congruent X Unit E (MayBarb X) ⟨∅ ∪ {withRead idle (c 7)}, sevenAtUnit⟩
        ⟨∅ ∪ {withTakeMake idle (c 7)}, sevenAtUnit⟩ :=
  ⟨fun π β s => mayBarb_renameState X π β s, fun related β => mayBarb_modulo related β,
    not_infinite_iff_finite.mpr inferInstance,
    fun related => takeMake_stuck_unit (related.moves read_moves_unit)⟩

/-! ## Law 6 needs the sides of the told equation to be kept -/

/-- The solution that sends `y` to `6` and every other unknown to `5`. -/
def sixAtY : Subst atoms := fun v => if v = 1 then c 6 else c 5

/-- **A fresh opening sends an unknown of its rule to an unknown**, apart from `y` where the state
mentions `y`. -/
theorem opening_apart {P : Program Tm} {s : State Tm ℕ} (f : Firing ℕ E P s.frame)
    (fresh : f.Fresh X s) {v : ℕ} (term : (Term.var v : Term atoms) ∈ f.rule.terms) :
    ∃ w, f.opening v = .var w ∧ (s.Mentions y → w ≠ 1) := by
  obtain ⟨u, state, rule⟩ := fresh PUnit.unit (fun _ => c 0) (fun _ => c 1)
  obtain ⟨u', -, rule'⟩ := fresh PUnit.unit (fun _ => c 0) (fun _ => c 2)
  have one : Subst.applyTerm u (f.opening v) = c 1 := rule _ term
  have two : Subst.applyTerm u' (f.opening v) = c 2 := rule' _ term
  cases opened : f.opening v with
  | var w =>
      refine ⟨w, rfl, fun mentioned same => ?_⟩
      subst same
      have seen : u 1 = c 0 := state y mentioned
      rw [opened] at one
      have bad : (c 0 : Term atoms) = c 1 := seen.symm.trans one
      exact absurd (Term.const.inj bad) (by decide)
  | const k =>
      rw [opened] at one two
      exact absurd ((Term.const.inj one).symm.trans (Term.const.inj two)) (by decide)
  | app fn _ => exact nomatch fn

/-- A row labelled by the unknown `w` may be `6`, at a solution of the knowledge that sends `w` to
`6`. -/
theorem six_at_row {s : State Tm ℕ} (w : ℕ) {ids : Finset ℕ} {o : ℕ} (inside : o ∈ ids)
    (σ : Subst atoms) (solved : X.Models (a := PUnit.unit) (b := PUnit.unit) σ s.knowledge)
    (six : σ w = c 6) : MayBarb X (pat (c 6)) (addRows s ids (fun _ => .var w)) := by
  refine ⟨o, Finset.mem_union_right _ inside, PUnit.unit, σ, Subst.id atoms, solved, ?_⟩
  show Subst.applyTerm σ (if o ∈ ids then Term.var w else s.label o) =
    Subst.applyTerm (Subst.id atoms) (c 6)
  rw [if_pos inside]
  exact six

/-- A row labelled by the unknown `w` is not `6` where the knowledge binds `w` to `5` and no other
row is present. -/
theorem not_six_at_row {s : State Tm ℕ} (w : ℕ) (ids : Finset ℕ)
    (bound : (Term.var w, c 5) ∈ s.knowledge) (rows : s.present = ∅) :
    ¬ MayBarb X (pat (c 6)) (addRows s ids (fun _ => .var w)) := by
  rintro ⟨o, present, b, σ, h, known, equated⟩
  have inside : o ∈ ids := by
    rcases Finset.mem_union.mp present with old | new
    · rw [rows] at old
      exact absurd old (Finset.notMem_empty o)
    · exact new
  have five : σ w = c 5 := known _ bound
  have six : Subst.applyTerm σ (if o ∈ ids then Term.var w else s.label o) = Subst.applyTerm h (c 6) :=
    equated
  rw [if_pos inside] at six
  have six' : σ w = c 6 := six
  rw [five] at six'
  exact absurd (Term.const.inj six') (by decide)

/-- A firing of a rule that makes nothing, at a state with no rows, leaves no rows. -/
theorem result_rows_empty {P : Program Tm} {s : State Tm ℕ} (g : Firing ℕ E P s.frame)
    (admitted : g.Admits X s) (rows : s.present = ∅) (noMake : g.rule.body.produce = []) :
    (g.result X s).present = ∅ := by
  obtain ⟨-, ⟨-, -, -, -, produceLength, -⟩, -, -, -, -⟩ := (admits_iff g).mp admitted
  rw [noMake] at produceLength
  have none : g.selection.made = [] := List.length_eq_zero_iff.mp produceLength.symm
  ext o
  simp only [Finset.notMem_empty, iff_false]
  intro inside
  rcases mem_fire.mp inside with ⟨old, -⟩ | made
  · rw [rows] at old
    exact Finset.notMem_empty o old
  · have made' : o ∈ g.selection.made := by simpa [Selection.commit] using made
    rw [none] at made'
    exact List.not_mem_nil made'

/-- **Law 6 needs the sides of the told equation to be terms the results keep**: `y = y`, a tautology,
is entailed by the tells of `idle`, and `y` is not a term the results of `idle` keep (both sides of the
equation are that one term). Without rows, the programs `idle` and `idle` telling `y = y` are not
congruent: telling `y = y` reserves the unknown it is opened as; after a context adds the rule that
tells `x = 5`, the other side binds an unknown that this side keeps free, and a context that adds a
row labelled by that unknown tells the two apart. The hypothesis that fails is that the equation's
sides are kept. -/
theorem tell_unkept_separated :
    X.Entails (a := PUnit.unit) idle.body.tell (fun b h => X.E (a := b)
        (X.act (a := PUnit.unit) (b := b) h y) (X.act (a := PUnit.unit) (b := b) h y)) ∧
      y ∉ keptTerms idle ∧
      ¬ Cong ⟨{withTell idle (y, y)}, unmentioned⟩ ⟨{idle}, unmentioned⟩ := by
  refine ⟨fun b _ _ => (X.equivalence b).refl _, by simp [keptTerms, idle], fun related => ?_⟩
  have related₁ : Cong ⟨{withTell idle (y, y)} ∪ {tellX}, unmentioned⟩
      ⟨{idle} ∪ {tellX}, unmentioned⟩ := related.addRules {tellX}
  -- The left tells `y = y`, opened as itself.
  let f : Firing ℕ E ({withTell idle (y, y)} ∪ {tellX}) unmentioned.frame :=
    ⟨withTell idle (y, y), Or.inl (Set.mem_singleton _), PUnit.unit, Subst.id atoms, ⟨[], [], []⟩,
      []⟩
  have admitted : f.Admits X unmentioned := by
    refine (admits_iff f).mpr ⟨?_, ⟨List.nodup_nil, List.nodup_nil, rfl, rfl, rfl, rfl⟩, ?_, ?_,
      fun check inside => absurd inside List.not_mem_nil,
      fun q inside => absurd inside List.not_mem_nil⟩
    · intro b g h
      refine ⟨h, fun t mentioned => ?_, fun t inside => ?_⟩
      · rcases mentioned with none | none | ⟨o, present, -⟩
        · exact absurd none List.not_mem_nil
        · exact absurd none List.not_mem_nil
        · exact absurd present (Finset.notMem_empty o)
      · have isY : t = y := by simpa [f, idle, Rule.terms] using inside
        subst isY
        rfl
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [f, Selection.commit]
    · refine ⟨PUnit.unit, Subst.id atoms, fun e inside => ?_⟩
      have unfolded : e ∈ ([] : EquationStore (Term atoms)) ++ [] ++ [] ++ [(y, y)] := inside
      simp only [List.nil_append, List.mem_singleton] at unfolded
      subst unfolded
      rfl
  have leftRows : (f.result X unmentioned).present = ∅ := by
    show fire ∅ ((⟨[], [], []⟩ : Selection ℕ).commit (T := Unit)) = ∅
    decide
  have leftKnowledge : (f.result X unmentioned).knowledge = [(y, y)] := rfl
  have leftMentions : (f.result X unmentioned).Mentions y := by
    left
    rw [leftKnowledge]
    exact List.mem_singleton_self _
  -- The right answers by `idle` or by the tell of `x = 5`.
  obtain ⟨R₁, moved, related₂⟩ := candidate_congruent.reduces related₁ (reduces_of_admits f admitted)
  obtain ⟨program₁, ⟨rule, member, ext, ι, selection, seen⟩, admittedG, reached⟩ := moved
  obtain ⟨P₁, s₁⟩ := R₁
  simp only at program₁ reached
  subst program₁ reached
  rcases (Set.mem_union _ _ _).mp member with isIdle | isTell
  · -- The right did nothing. It tells `x = 5` with `x` opened as `y`, which it does not mention.
    have same : rule = idle := isIdle
    subst same
    have rowsR₁ : (Firing.result X unmentioned
        (⟨idle, member, ext, ι, selection, seen⟩ :
          Firing ℕ E ({idle} ∪ {tellX}) unmentioned.frame)).present = ∅ :=
      result_rows_empty _ admittedG rfl rfl
    let s₁ := Firing.result X unmentioned
      (⟨idle, member, ext, ι, selection, seen⟩ : Firing ℕ E ({idle} ∪ {tellX}) unmentioned.frame)
    let h₁ : Firing ℕ E ({idle} ∪ {tellX}) s₁.frame :=
      ⟨tellX, Or.inr (Set.mem_singleton _), PUnit.unit, fun _ => y, ⟨[], [], []⟩, []⟩
    have admittedH : h₁.Admits X s₁ := by
      refine (admits_iff h₁).mpr ⟨?_, ⟨List.nodup_nil, List.nodup_nil, rfl, rfl, rfl, rfl⟩, ?_, ?_,
        fun check inside => absurd inside List.not_mem_nil,
        fun q inside => absurd inside List.not_mem_nil⟩
      · intro b g h
        refine ⟨fun _ => h 0, fun t mentioned => ?_, fun t inside => ?_⟩
        · rcases mentioned with none | none | ⟨o, present, -⟩
          · exact absurd none List.not_mem_nil
          · exact absurd none List.not_mem_nil
          · exact absurd present (by rw [rowsR₁]; exact Finset.notMem_empty o)
        · have cases : t = x ∨ t = c 5 := by simpa [h₁, tellX, Rule.terms] using inside
          rcases cases with rfl | rfl <;> rfl
      · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [h₁, Selection.commit]
      · refine ⟨PUnit.unit, fun _ => c 5, fun e inside => ?_⟩
        have unfolded : e ∈ ([] : EquationStore (Term atoms)) ++ [] ++ [] ++ [(y, c 5)] := inside
        simp only [List.nil_append, List.mem_singleton] at unfolded
        subst unfolded
        rfl
    have rowsR₂ : (h₁.result X s₁).present = ∅ := result_rows_empty h₁ admittedH rowsR₁ rfl
    have boundR : ((Term.var 1 : Term atoms), c 5) ∈ (h₁.result X s₁).knowledge :=
      List.mem_append_right _ (List.mem_singleton_self _)
    -- The left must answer; it mentions `y`, so it binds no `y`.
    obtain ⟨L₂, movedL, relatedL⟩ :=
      candidate_congruent.reduces related₂.symm (reduces_of_admits h₁ admittedH)
    obtain ⟨programL, ⟨ruleL, memberL, extL, ιL, selectionL, seenL⟩, admittedL, reachedL⟩ := movedL
    obtain ⟨PL, sL⟩ := L₂
    simp only at programL reachedL
    subst programL reachedL
    obtain ⟨freshL, -⟩ := (admits_iff _).mp admittedL
    have solvedL : X.Models (a := PUnit.unit) (b := PUnit.unit) sixAtY
        (Firing.result X (f.result X unmentioned)
          (⟨ruleL, memberL, extL, ιL, selectionL, seenL⟩ :
            Firing ℕ E ({withTell idle (y, y)} ∪ {tellX}) (f.result X unmentioned).frame)).knowledge := by
      intro e inside
      rcases (mem_information _).mp inside with old | take | read | tells
      · have old' : e ∈ [(y, y)] := old
        rw [List.mem_singleton] at old'
        subst old'
        rfl
      · obtain ⟨p, o, paired, -⟩ := (mem_matching _).mp take
        rcases (Set.mem_union _ _ _).mp memberL with isTold | isTellX
        · have same : ruleL = withTell idle (y, y) := isTold
          subst same
          exact absurd paired List.not_mem_nil
        · have same : ruleL = tellX := isTellX
          subst same
          exact absurd paired List.not_mem_nil
      · obtain ⟨p, o, paired, -⟩ := (mem_matching _).mp read
        rcases (Set.mem_union _ _ _).mp memberL with isTold | isTellX
        · have same : ruleL = withTell idle (y, y) := isTold
          subst same
          exact absurd paired List.not_mem_nil
        · have same : ruleL = tellX := isTellX
          subst same
          exact absurd paired List.not_mem_nil
      · rcases (Set.mem_union _ _ _).mp memberL with isTold | isTellX
        · have same : ruleL = withTell idle (y, y) := isTold
          subst same
          have tells' : e ∈ [(Subst.applyTerm ιL y, Subst.applyTerm ιL y)] := tells
          rw [List.mem_singleton] at tells'
          subst tells'
          rfl
        · have same : ruleL = tellX := isTellX
          subst same
          obtain ⟨w, opened, apart⟩ := opening_apart
            (⟨tellX, memberL, extL, ιL, selectionL, seenL⟩ :
              Firing ℕ E ({withTell idle (y, y)} ∪ {tellX}) (f.result X unmentioned).frame)
            freshL (v := 0) (by simp [tellX, Rule.terms, x])
          have tells' : e ∈ [(Subst.applyTerm ιL x, Subst.applyTerm ιL (c 5))] := tells
          rw [List.mem_singleton] at tells'
          subst tells'
          show Subst.applyTerm sixAtY (ιL 0) = Subst.applyTerm sixAtY (c 5)
          have opened' : ιL 0 = .var w := opened
          rw [opened']
          show (if w = 1 then c 6 else c 5) = c 5
          rw [if_neg (apart leftMentions)]
    have rowsL : (Firing.result X (f.result X unmentioned)
        (⟨ruleL, memberL, extL, ιL, selectionL, seenL⟩ :
          Firing ℕ E ({withTell idle (y, y)} ∪ {tellX}) (f.result X unmentioned).frame)).present = ∅ := by
      apply result_rows_empty _ admittedL leftRows
      rcases (Set.mem_union _ _ _).mp memberL with isTold | isTellX
      · have same : ruleL = withTell idle (y, y) := isTold
        subst same
        rfl
      · have same : ruleL = tellX := isTellX
        subst same
        rfl
    -- A context adds a row `y`: at the right it is `5`, at the left it may be `6`.
    obtain ⟨π, -, related₄⟩ := relatedL.addRows {0} (fun _ _ => y)
      (by rw [rowsR₂]; exact Finset.disjoint_empty_right _)
    have atLeft := six_at_row 1 (ids := ({0} : Finset ℕ).map π.toEmbedding) (o := π 0)
      (Finset.mem_map_equiv.mpr (by simp)) sixAtY solvedL rfl
    exact not_six_at_row 1 {0} boundR rowsR₂
      (candidate_congruent.barbs related₄.symm (pat (c 6)) atLeft)
  · -- The right told `x = 5` with `x` opened as an unknown `w`; a row `w` tells the two apart.
    have same : rule = tellX := isTell
    subst same
    obtain ⟨freshG, -⟩ := (admits_iff _).mp admittedG
    obtain ⟨w, opened, -⟩ := opening_apart
      (⟨tellX, member, ext, ι, selection, seen⟩ : Firing ℕ E ({idle} ∪ {tellX}) unmentioned.frame)
      freshG (v := 0) (by simp [tellX, Rule.terms, x])
    have opened' : ι 0 = .var w := opened
    have rowsR₁ : (Firing.result X unmentioned
        (⟨tellX, member, ext, ι, selection, seen⟩ :
          Firing ℕ E ({idle} ∪ {tellX}) unmentioned.frame)).present = ∅ :=
      result_rows_empty _ admittedG rfl rfl
    have boundR : (Term.var w, c 5) ∈ (Firing.result X unmentioned
        (⟨tellX, member, ext, ι, selection, seen⟩ :
          Firing ℕ E ({idle} ∪ {tellX}) unmentioned.frame)).knowledge := by
      show (Term.var w, c 5) ∈ ([] : EquationStore (Term atoms)) ++ [] ++ [] ++ [(ι 0, c 5)]
      rw [opened']
      exact List.mem_singleton_self _
    obtain ⟨π, -, related₃⟩ := related₂.addRows {0} (fun _ _ => .var w)
      (by rw [leftRows]; exact Finset.disjoint_empty_right _)
    have atLeft := six_at_row w (ids := ({0} : Finset ℕ)) (o := 0) (Finset.mem_singleton_self 0)
      (fun _ => c 6) (by
        rw [leftKnowledge]
        intro e inside
        rw [List.mem_singleton] at inside
        subst inside
        rfl) rfl
    exact not_six_at_row w (({0} : Finset ℕ).map π.toEmbedding) boundR rowsR₁
      (candidate_congruent.barbs related₃ (pat (c 6)) atLeft)

#print axioms tell_example
#print axioms told_readMake_stuck
#print axioms tell_not_entailed_separated
#print axioms opening_apart
#print axioms six_at_row
#print axioms not_six_at_row
#print axioms result_rows_empty
#print axioms tell_unkept_separated
#print axioms read_example
#print axioms read_moves_unit
#print axioms takeMake_stuck_unit
#print axioms read_needs_infinite

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.AtOneFrame
