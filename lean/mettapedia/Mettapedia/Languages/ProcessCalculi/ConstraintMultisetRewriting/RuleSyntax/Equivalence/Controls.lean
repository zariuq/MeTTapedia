import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Separations
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.ProgramLaws

/-!
# Controls for the laws, related pairs, and what each barb sees, at one frame

## Different systems that are congruent

* `renamed_example`: one row `7` at identity `0` and at identity `1` (Law 1).
* `modulo_example`: the knowledge `x = 5` with a row `x`, against `5 = x` with a row `5` (Law 2).
* `dead_example`: a rule whose tells are unsolvable may be dropped.
* `guard_example`: the guard `x = 5` of the rule that tells `x = 5` may be dropped.

## Each hypothesis of a law is needed

* **Law 1, new rows at absent identities** (`overlap_separates`): a row added at an identity present
  at one side only overwrites it there, and the barbs then differ.
* **Law 2, the same support** (`support_separates`): the empty knowledge and the knowledge `y = y`
  have the same solutions. A rule with its own unknown, opened as `y` where `y` is not mentioned, binds
  `y`; where `y` is mentioned it must use another unknown; a context that then names `y` sees the
  difference.
* **So the knowledge is not observed up to logical equivalence** (`tautology_observable`): with no
  rows and no rules, the empty knowledge and the knowledge `y = y`, a tautology, are not congruent.

## Where the support comes from, and what a congruence on observable names would change

Two features of the definitions, not of the one-frame instance, make the support observable. A
context is a family indexed by frames (`Basic`: its labels, equations and extensions are given at
every frame), so a context applied after a firing can name every unknown of the frame it meets,
including one the firing has just opened. And freshness (`Firing.Fresh`) lets an opening send a rule's
unknown to any unknown of the frame that the state does not mention. A congruence indexed by a set of
observable names would have to change both: its contexts would name only the unknowns of that set,
given once and carried along the weakenings of a run rather than chosen at the frame they meet, and
the unknowns outside the set would be private to the system, so that Law 2 would ask for the same
support on the observable names only. That congruence is not built here.
* **Dropping a rule, the condition is on the rule alone** (`dormant_rule_separated`): a rule that waits
  for a row `9` fires in no state the system reaches, and still cannot be dropped.
* **Dropping a guard, it must be entailed** (`guard_not_entailed_separated`): the guard `x = 5` on a
  rule that reads `x` and tells nothing refuses a firing the unguarded rule makes. Its terms need not
  be terms of the rule at this instance, nor at any first-order frame with the numbers as unknowns
  (`entailedGuard_congruent_oneFrame`, `AtFirstOrder.entailedGuard_congruent_firstOrder`, in
  `GuardTerms`); at the frame with one unknown they must (`AtOneUnknown.guard_terms_needed`), because
  that frame has no fresh unknown to open a new term as (`AtOneUnknown.fresh_supply_needed`).
* **Laws 6 and 7**: their instances and controls are in `TellReadControls`.

## What the barbs see

* `may_not_must`: a row labelled by a free unknown is a may-barb of `5` and not a must-barb; a row `5`
  is both.
* `unsolvable_barbs`: at unsolvable knowledge every must-barb of a present row holds and no may-barb.
* `sevens_barbs` (in `Separations`): may-barbs do not count rows; contexts do (`count_separates`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.AtOneFrame

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open Mettapedia.Logic.LP
open RuleSyntax.Examples (Tm X E x c fresh_of_ground)
open RuleSyntax.Controls (atoms action)

/-! ## Related pairs -/

/-- **Law 1, an instance**: one row `7` at identity `0` and at identity `1`. -/
theorem renamed_example :
    Cong ⟨∅, oneSeven⟩ ⟨∅, renameState (Equiv.swap 0 1) oneSeven⟩ ∧
      oneSeven.present ≠ (renameState (Equiv.swap 0 1) oneSeven).present := by
  refine ⟨rename_congruent_mayBarb (Equiv.swap 0 1) ∅ oneSeven, fun same => ?_⟩
  have inside : (0 : ℕ) ∈ (renameState (Equiv.swap 0 1) oneSeven).present := by
    rw [← same]
    simp [oneSeven]
  simp [renameState, oneSeven] at inside

/-- The knowledge `x = 5` with a row `x`. -/
def boundX : State Tm ℕ := ⟨PUnit.unit, [(x, c 5)], {0}, fun _ => x⟩

/-- **Law 2, an instance**: `x = 5` with a row `x`, against `5 = x` with a row `5`. -/
theorem modulo_example (P : Program Tm) :
    Cong ⟨P, boundX⟩ ⟨P, ⟨PUnit.unit, [(c 5, x)], {0}, fun _ => c 5⟩⟩ := by
  refine modulo_congruent_mayBarb P ⟨[(c 5, x)], fun _ => c 5, ⟨fun b σ => ?_, ?_, ?_⟩, rfl⟩
  · constructor
    · intro solved e inside
      have same : e = (c 5, x) := List.mem_singleton.mp inside
      subst same
      exact (solved (x, c 5) (List.mem_singleton_self _)).symm
    · intro solved e inside
      have same : e = (x, c 5) := List.mem_singleton.mp inside
      subst same
      exact (solved (c 5, x) (List.mem_singleton_self _)).symm
  · intro o _ b σ solved
    exact solved (x, c 5) (List.mem_singleton_self _)
  · intro b φ ψ
    constructor
    · intro agree t mentioned
      rcases mentioned with inFst | inSnd | ⟨o, _, rfl⟩
      · have same : t = c 5 := List.mem_singleton.mp inFst
        subst same
        rfl
      · have same : t = x := List.mem_singleton.mp inSnd
        subst same
        exact agree x (Or.inl (List.mem_singleton_self _))
      · rfl
    · intro agree t mentioned
      rcases mentioned with inFst | inSnd | ⟨o, _, rfl⟩
      · have same : t = x := List.mem_singleton.mp inFst
        subst same
        exact agree x (Or.inr (Or.inl (List.mem_singleton_self _)))
      · have same : t = c 5 := List.mem_singleton.mp inSnd
        subst same
        rfl
      · exact agree x (Or.inr (Or.inl (List.mem_singleton_self _)))

/-- A rule that tells `1 = 2`. -/
def deadRule : Rule Tm := ⟨PUnit.unit, ⟨[], [], [(c 1, c 2)], [], []⟩, []⟩

theorem deadRule_neverFires : NeverFires X deadRule := by
  intro b h told
  have same : Subst.applyTerm h (c 1) = Subst.applyTerm h (c 2) :=
    told (c 1, c 2) (List.mem_singleton_self _)
  exact absurd (Term.const.inj same) (by decide)

/-- **A rule that never fires may be dropped, an instance.** -/
theorem dead_example : Cong ⟨∅ ∪ {deadRule}, oneSeven⟩ ⟨∅, oneSeven⟩ :=
  neverFires_congruent deadRule_neverFires ∅ oneSeven

/-- Tell `x = 5`. -/
def tellX : Rule Tm := ⟨PUnit.unit, ⟨[], [], [(x, c 5)], [], []⟩, []⟩

/-- **An entailed guard may be dropped, an instance**: tell `x = 5` and guard `x = 5`. -/
theorem guard_example (s : State Tm ℕ) :
    Cong ⟨∅ ∪ {withGuard tellX x (c 5)}, s⟩ ⟨∅ ∪ {tellX}, s⟩ :=
  entailedGuard_congruent (fun _ h told => told (x, c 5) (List.mem_singleton_self _))
    (by simp [tellX, Rule.terms]) (by simp [tellX, Rule.terms]) ∅ s

/-! ## Law 1 needs new rows at absent identities -/

/-- **A context that overwrites a present identity separates a state from its renamed copy.** -/
theorem overlap_separates :
    Cong ⟨∅, oneSeven⟩ ⟨∅, renameState (Equiv.swap 0 1) oneSeven⟩ ∧
      Disjoint ({1} : Finset ℕ) oneSeven.present ∧
      ¬ Disjoint ({1} : Finset ℕ) (renameState (Equiv.swap 0 1) oneSeven).present ∧
      MayBarb X (pat (c 7)) (addRows oneSeven {1} (fun _ => c 8)) ∧
      ¬ MayBarb X (pat (c 7)) (addRows (renameState (Equiv.swap 0 1) oneSeven) {1} (fun _ => c 8)) := by
  refine ⟨rename_congruent_mayBarb (Equiv.swap 0 1) ∅ oneSeven, by simp [oneSeven], ?_, ?_, ?_⟩
  · simp [renameState, oneSeven]
  · exact ⟨0, by simp [addRows, oneSeven], PUnit.unit, Subst.id atoms, Subst.id atoms,
      Frames.models_nil (X := X) _, by simp [addRows, oneSeven]; rfl⟩
  · rintro ⟨o, present, b, σ, h, -, equated⟩
    have one : o = 1 := by simpa [addRows, renameState, oneSeven] using present
    subst one
    simp only [addRows, renameState, oneSeven, Finset.mem_singleton, if_true] at equated
    have eight : Subst.applyTerm σ (c 8) = Subst.applyTerm h (c 7) := equated
    exact absurd (Term.const.inj eight) (by decide)

/-! ## Law 2 needs the same support -/

/-- No knowledge and no rows. -/
def unmentioned : State Tm ℕ := ⟨PUnit.unit, [], ∅, fun _ => c 0⟩

/-- The knowledge `y = y`, which every solution solves, and no rows. -/
def mentionsY : State Tm ℕ := ⟨PUnit.unit, [(y, y)], ∅, fun _ => c 0⟩

/-- An opening of `tellX` that is fresh where `y` is mentioned sends `x` to a variable other than
`y`. -/
theorem opening_avoids_y (ext : PUnit) (ι : Subst atoms) (selection : Selection ℕ)
    (seen : List (Finset ℕ))
    (fresh : (⟨tellX, Set.mem_singleton _, ext, ι, selection, seen⟩ :
      Firing ℕ E ({tellX} : Program Tm) mentionsY.frame).Fresh X mentionsY) :
    ∃ z, z ≠ 1 ∧ ι 0 = .var z := by
  obtain ⟨u, state, rule⟩ := fresh PUnit.unit (fun _ => c 0) (fun _ => c 1)
  obtain ⟨u', -, rule'⟩ := fresh PUnit.unit (fun _ => c 0) (fun _ => c 2)
  have uy : u 1 = c 0 := state y (Or.inl (List.mem_singleton_self _))
  have xTerm : x ∈ tellX.terms := by simp [tellX, Rule.terms]
  have ux : Subst.applyTerm u (ι 0) = c 1 := rule x xTerm
  have ux' : Subst.applyTerm u' (ι 0) = c 2 := rule' x xTerm
  cases h : ι 0 with
  | var z =>
      refine ⟨z, fun same => ?_, rfl⟩
      subst same
      rw [h] at ux
      have bad : (c 0 : Term atoms) = c 1 := uy.symm.trans ux
      exact absurd (Term.const.inj bad) (by decide)
  | const k =>
      rw [h] at ux ux'
      have one : k = 1 := Term.const.inj ux
      have two : k = 2 := Term.const.inj ux'
      have bad : (1 : ℕ) = 2 := one.symm.trans two
      exact absurd bad (by decide)
  | app f _ => exact f.elim

/-- **Equivalence modulo the knowledge without the same support is not a congruence.** -/
theorem support_separates :
    X.Equivalent (a := PUnit.unit) unmentioned.knowledge mentionsY.knowledge ∧
      ¬ Cong ⟨{tellX}, unmentioned⟩ ⟨{tellX}, mentionsY⟩ := by
  refine ⟨fun b σ => ⟨fun _ e inside => ?_, fun _ e inside => absurd inside List.not_mem_nil⟩, ?_⟩
  · rw [show mentionsY.knowledge = [(y, y)] from rfl, List.mem_singleton] at inside
    subst inside
    rfl
  intro related
  -- The left side opens the rule's unknown as `y`, which it does not mention, and binds it.
  let ι : Subst atoms := fun _ => y
  let f : Firing ℕ E ({tellX} : Program Tm) unmentioned.frame :=
    ⟨tellX, Set.mem_singleton _, PUnit.unit, ι, ⟨[], [], []⟩, []⟩
  have admitted : f.Admits X unmentioned := by
    refine (admits_iff f).mpr ⟨?_, ⟨List.nodup_nil, List.nodup_nil, rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
    · intro b g h
      refine ⟨fun _ => h 0, fun t mentioned => ?_, fun t inside => ?_⟩
      · rcases mentioned with none | none | ⟨o, present, -⟩
        · exact absurd none List.not_mem_nil
        · exact absurd none List.not_mem_nil
        · exact absurd present (Finset.notMem_empty o)
      · have cases : t = x ∨ t = c 5 := by simpa [f, tellX, Rule.terms] using inside
        rcases cases with rfl | rfl <;> rfl
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [f, Selection.commit]
    · refine ⟨PUnit.unit, fun _ => c 5, fun e inside => ?_⟩
      have unfolded : e ∈ ([] : EquationStore (Term atoms)) ++ [] ++ [] ++ [(y, c 5)] := inside
      simp only [List.nil_append, List.mem_singleton] at unfolded
      subst unfolded
      rfl
    · intro check inside
      exact absurd inside List.not_mem_nil
    · intro q inside
      exact absurd inside List.not_mem_nil
  obtain ⟨T', moved, related'⟩ := candidate_congruent.reduces related (reduces_of_admits f admitted)
  obtain ⟨program, ⟨rule, member, ext, ι', selection, seen⟩, admittedG, reached⟩ := moved
  have isRule : rule = tellX := member
  subst isRule
  obtain ⟨freshG, -, -, -, -, -⟩ := (admits_iff _).mp admittedG
  obtain ⟨z, notOne, opened⟩ := opening_avoids_y ext ι' selection seen freshG
  -- A context names `y`.
  have leftEmpty : (f.result X unmentioned).present = ∅ := by
    show fire ∅ ((⟨[], [], []⟩ : Selection ℕ).commit (T := Unit)) = ∅
    decide
  obtain ⟨π, -, related''⟩ := related'.addRows {0} (fun _ _ => y)
    (by rw [leftEmpty]; exact Finset.disjoint_empty_right _)
  -- At the right the row `y` can be `6`: the rule's unknown went to `z`, not to `y`.
  have atRight : MayBarb X (pat (c 6))
      (addRows T'.state (({0} : Finset ℕ).map π.toEmbedding) (fun _ => y)) := by
    refine ⟨π 0, Finset.mem_union_right _ (Finset.mem_map_of_mem _ (Finset.mem_singleton_self 0)),
      PUnit.unit, fun v => if v = z then c 5 else c 6, Subst.id atoms, ?_, ?_⟩
    · intro e inside
      have inside' : e ∈ (⟨tellX, Set.mem_singleton _, ext, ι', selection, seen⟩ :
          Firing ℕ E ({tellX} : Program Tm) mentionsY.frame).information X mentionsY := by
        rw [← reached] at inside
        exact inside
      have unfolded : e ∈ [(Subst.applyTerm (Subst.id atoms) y, Subst.applyTerm (Subst.id atoms) y)] ++
          [] ++ [] ++ [(Subst.applyTerm ι' x, Subst.applyTerm ι' (c 5))] := inside'
      simp only [List.append_nil, List.mem_append, List.mem_singleton] at unfolded
      rcases unfolded with rfl | rfl
      · rfl
      · show Subst.applyTerm (fun v => if v = z then c 5 else c 6) (ι' 0) = c 5
        rw [opened]
        exact if_pos rfl
    · show Subst.applyTerm (fun v => if v = z then c 5 else c 6)
        (if π 0 ∈ ({0} : Finset ℕ).map π.toEmbedding then y else T'.state.label (π 0)) =
          Subst.applyTerm (Subst.id atoms) (c 6)
      have inside : π 0 ∈ ({0} : Finset ℕ).map π.toEmbedding :=
        Finset.mem_map_equiv.mpr (by simp)
      rw [if_pos inside]
      show (if (1 : ℕ) = z then c 5 else c 6) = c 6
      rw [if_neg (fun same => notOne same.symm)]
  -- At the left the row `y` is `5` at every solution.
  obtain ⟨o, present, b, σ, h, known, equated⟩ :=
    candidate_congruent.barbs related''.symm (pat (c 6)) atRight
  have zero : o = 0 := by
    rcases Finset.mem_union.mp present with old | new
    · rw [leftEmpty] at old
      exact absurd old (Finset.notMem_empty o)
    · exact Finset.mem_singleton.mp new
  subst zero
  have bound : σ 1 = c 5 := known (y, c 5) (List.mem_append_right _ (List.mem_singleton_self _))
  have six : σ 1 = Subst.applyTerm h (c 6) := by
    simp [addRows, y] at equated
    exact equated
  rw [bound] at six
  exact absurd (Term.const.inj six) (by decide)

/-- **The knowledge is not observed up to logical equivalence**: with no rows and no rules, the empty
knowledge and the knowledge `y = y`, which every substitution solves, are not congruent. The context
that adds the rule telling `x = 5` leads to `support_separates`. -/
theorem tautology_observable :
    (∀ σ : Subst atoms, X.Solves (a := PUnit.unit) (b := PUnit.unit) σ (y, y)) ∧
      ¬ Cong ⟨∅, unmentioned⟩ ⟨∅, mentionsY⟩ := by
  refine ⟨fun σ => rfl, fun related => support_separates.2 ?_⟩
  have added : Cong ⟨∅ ∪ {tellX}, unmentioned⟩ ⟨∅ ∪ {tellX}, mentionsY⟩ := related.addRules {tellX}
  rw [Set.empty_union] at added
  exact added

/-! ## A rule that waits for a row cannot be dropped -/

/-- Take a `9`, make a `5`. -/
def takeNine : Rule Tm := ⟨PUnit.unit, ⟨[c 9], [], [], [], [c 5]⟩, []⟩

theorem takeNine_stuck_empty : ¬ Moves ⟨{takeNine}, empty⟩ := by
  rintro ⟨T, -, ⟨rule, member, ext, ι, selection, seen⟩, admitted, -⟩
  have isRule : rule = takeNine := member
  subst isRule
  obtain ⟨-, ⟨-, -, takeLength, -, -, -⟩, enabled, -, -, -⟩ := (admits_iff _).mp admitted
  obtain ⟨o, taken⟩ := List.length_eq_one_iff.mp takeLength.symm
  have taken' : selection.taken = [o] := taken
  have inside : o ∈ empty.present := enabled.taken_subset (by simp [Selection.commit, taken'])
  exact absurd inside (Finset.notMem_empty o)

/-- **A rule that fires in no reachable state may still not be dropped**: a context adds the row it
waits for. -/
theorem dormant_rule_separated :
    Bisim ⟨{takeNine}, empty⟩ ⟨∅, empty⟩ ∧ ¬ Cong ⟨{takeNine}, empty⟩ ⟨∅, empty⟩ := by
  refine ⟨bisimilar_of_stuck takeNine_stuck_empty (empty_stuck _) fun _ => Iff.rfl, fun related => ?_⟩
  obtain ⟨π, -, related'⟩ := related.addRows {0} (fun _ _ => c 9) (by simp [empty])
  apply empty_stuck _ (moves_of_congruent related' ?_)
  let s := addRows empty {0} (fun _ => c 9)
  let f : Firing ℕ E ({takeNine} : Program Tm) s.frame :=
    ⟨takeNine, Set.mem_singleton _, PUnit.unit, Subst.id atoms, ⟨[0], [], [1]⟩, []⟩
  have admitted : f.Admits X s := by
    refine (admits_iff f).mpr ⟨?_, ⟨List.nodup_singleton _, List.nodup_singleton _, rfl, rfl, rfl,
      rfl⟩, ?_, ?_, ?_, ?_⟩
    · apply fresh_of_ground action s f
      intro t member σ
      simp [f, takeNine, Rule.terms] at member
      rcases member with rfl | rfl <;> rfl
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [f, s, Selection.commit, addRows, empty]
      · simp [f, Selection.commit]
      · simp [f, Selection.commit]
      · simp [f, s, Selection.commit, addRows, empty]
      · intro q inside
        simp [f, Selection.commit] at inside
    · refine ⟨PUnit.unit, Subst.id atoms, fun e inside => ?_⟩
      have unfolded : e ∈ ([] : EquationStore (Term atoms)) ++
          [(Subst.applyTerm (Subst.id atoms) (c 9),
            Subst.applyTerm (Subst.id atoms) (if (0 : ℕ) ∈ ({0} : Finset ℕ) then c 9 else c 0))] ++
          [] ++ [] := inside
      simp only [List.nil_append, List.append_nil, List.mem_singleton] at unfolded
      subst unfolded
      rfl
    · intro check inside
      exact absurd inside List.not_mem_nil
    · intro q inside
      exact absurd inside List.not_mem_nil
  exact ⟨_, reduces_of_admits f admitted⟩

/-! ## A guard that is not entailed cannot be dropped -/

/-- Read any row `x`, make a `5`. -/
def readMake : Rule Tm := ⟨PUnit.unit, ⟨[], [x], [], [], [c 5]⟩, []⟩

/-- One row `6`. -/
def rowSix : State Tm ℕ := ⟨PUnit.unit, [], {0}, fun _ => c 6⟩

theorem readMake_moves : Moves ⟨∅ ∪ {readMake}, rowSix⟩ := by
  let f : Firing ℕ E (∅ ∪ {readMake}) rowSix.frame :=
    ⟨readMake, Or.inr (Set.mem_singleton _), PUnit.unit, Subst.id atoms, ⟨[], [0], [1]⟩, []⟩
  have admitted : f.Admits X rowSix := by
    refine (admits_iff f).mpr ⟨?_, ⟨List.nodup_nil, List.nodup_singleton _, rfl, rfl, rfl, rfl⟩,
      ?_, ?_, ?_, ?_⟩
    · intro b g h
      refine ⟨h, fun t mentioned => ?_, fun t inside => ?_⟩
      · rcases mentioned with none | none | ⟨o, _, rfl⟩
        · exact absurd none List.not_mem_nil
        · exact absurd none List.not_mem_nil
        · rfl
      · simp only [f, readMake, Rule.terms, List.map_nil, List.flatMap_nil, List.nil_append,
          List.append_nil, List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at inside
        rcases inside with rfl | rfl <;> rfl
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [f, Selection.commit]
      · simp [f, Selection.commit, rowSix]
      · simp [f, Selection.commit]
      · simp [f, Selection.commit, rowSix]
      · intro q inside
        simp [f, Selection.commit] at inside
    · refine ⟨PUnit.unit, fun _ => c 6, fun e inside => ?_⟩
      have unfolded : e ∈ ([] : EquationStore (Term atoms)) ++ [] ++
          [(Subst.applyTerm (Subst.id atoms) x, Subst.applyTerm (Subst.id atoms) (c 6))] ++ [] := inside
      simp only [List.nil_append, List.append_nil, List.mem_singleton] at unfolded
      subst unfolded
      rfl
    · intro check inside
      exact absurd inside List.not_mem_nil
    · intro q inside
      exact absurd inside List.not_mem_nil
  exact ⟨_, reduces_of_admits f admitted⟩

theorem guarded_readMake_stuck : ¬ Moves ⟨∅ ∪ {withGuard readMake x (c 5)}, rowSix⟩ := by
  rintro ⟨T, -, ⟨rule, member, ext, ι, selection, seen⟩, admitted, -⟩
  rcases (Set.mem_union _ _ _).mp member with none | isRule
  · exact Set.notMem_empty _ none
  have same : rule = withGuard readMake x (c 5) := isRule
  subst same
  obtain ⟨-, ⟨-, -, -, readLength, -, -⟩, enabled, ⟨b, σ, solved⟩, checks, -⟩ :=
    (admits_iff _).mp admitted
  obtain ⟨o, read⟩ := List.length_eq_one_iff.mp readLength.symm
  have read' : selection.read = [o] := read
  have guard := checks (.equal (Subst.applyTerm ι x) (c 5)) (List.mem_cons_self) b σ solved
  have equated := Firing.read_solved _ solved (p := Subst.applyTerm ι x) (o := o) (by
    show (Subst.applyTerm ι x, o) ∈ [Subst.applyTerm ι x].zip selection.read
    rw [read']
    exact List.mem_cons_self)
  have five : Subst.applyTerm σ (Subst.applyTerm ι x) = c 5 := guard
  have six : Subst.applyTerm σ (Subst.applyTerm ι x) =
      Subst.applyTerm σ (Subst.applyTerm (Subst.id atoms) (c 6)) := equated
  rw [five] at six
  exact absurd (Term.const.inj six) (by decide)

/-- **A guard that the rule's tells do not entail cannot be dropped.** -/
theorem guard_not_entailed_separated :
    ¬ X.Entails (a := PUnit.unit) readMake.body.tell (fun b h => X.E (a := b)
        (X.act (a := PUnit.unit) (b := b) h x) (X.act (a := PUnit.unit) (b := b) h (c 5))) ∧
      ¬ Cong ⟨∅ ∪ {withGuard readMake x (c 5)}, rowSix⟩ ⟨∅ ∪ {readMake}, rowSix⟩ := by
  refine ⟨fun entailed => ?_, fun related => guarded_readMake_stuck
    (moves_of_congruent related.symm readMake_moves)⟩
  have holds : Subst.applyTerm (fun _ => c 6) x = Subst.applyTerm (fun _ => c 6) (c 5) :=
    entailed PUnit.unit (fun _ => c 6) (fun e inside => absurd inside List.not_mem_nil)
  exact absurd (Term.const.inj holds) (by decide)

/-! ## A context without queries separates by multiplicity -/

/-- Take two `7`s, make a `5`: no check, no collect query. -/
def takeTwoSevens : Rule Tm := ⟨PUnit.unit, ⟨[c 7, c 7], [], [], [], [c 5]⟩, []⟩

theorem takeTwo_moves : Moves ⟨∅ ∪ {takeTwoSevens}, twoSevens⟩ := by
  let f : Firing ℕ E (∅ ∪ {takeTwoSevens}) twoSevens.frame :=
    ⟨takeTwoSevens, Or.inr (Set.mem_singleton _), PUnit.unit, Subst.id atoms, ⟨[0, 1], [], [2]⟩, []⟩
  have admitted : f.Admits X twoSevens := by
    refine (admits_iff f).mpr ⟨?_, ⟨by decide, List.nodup_singleton _, rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
    · apply fresh_of_ground action twoSevens f
      intro t member σ
      simp [f, takeTwoSevens, Rule.terms] at member
      rcases member with rfl | rfl <;> rfl
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [f, Selection.commit, twoSevens]
      · simp [f, Selection.commit]
      · simp [f, Selection.commit]
      · simp [f, Selection.commit, twoSevens]
      · intro q inside
        simp [f, Selection.commit] at inside
    · refine ⟨PUnit.unit, Subst.id atoms, fun e inside => ?_⟩
      have unfolded : e ∈ ([] : EquationStore (Term atoms)) ++
          [(c 7, Subst.applyTerm (Subst.id atoms) (c 7)), (c 7, Subst.applyTerm (Subst.id atoms) (c 7))] ++
          [] ++ [] := inside
      simp only [List.nil_append, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at unfolded
      rcases unfolded with rfl | rfl <;> rfl
    · intro check inside
      exact absurd inside List.not_mem_nil
    · intro q inside
      exact absurd inside List.not_mem_nil
  exact ⟨_, reduces_of_admits f admitted⟩

theorem takeTwo_stuck : ¬ Moves ⟨∅ ∪ {takeTwoSevens}, oneSeven⟩ := by
  rintro ⟨T, -, ⟨rule, member, ext, ι, selection, seen⟩, admitted, -⟩
  rcases (Set.mem_union _ _ _).mp member with none | isRule
  · exact Set.notMem_empty _ none
  have same : rule = takeTwoSevens := isRule
  subst same
  obtain ⟨-, ⟨takenNodup, -, takeLength, -, -, -⟩, enabled, -, -, -⟩ := (admits_iff _).mp admitted
  have inside : selection.taken.toFinset ⊆ oneSeven.present := enabled.taken_subset
  have card := Finset.card_le_card inside
  rw [List.toFinset_card_of_nodup takenNodup] at card
  have two : selection.taken.length = 2 := takeLength.symm
  rw [two] at card
  exact absurd card (by decide)

/-- **A rule with no query separates one row `7` from two**: closed bisimilarity is not preserved by
adding a rule even when neither the systems nor the context ask any query. -/
theorem queryFree_count_separates :
    takeTwoSevens.body.checks = [] ∧ takeTwoSevens.collect = [] ∧
      Bisim ⟨∅, oneSeven⟩ ⟨∅, twoSevens⟩ ∧ ¬ Cong ⟨∅, oneSeven⟩ ⟨∅, twoSevens⟩ :=
  ⟨rfl, rfl, sevens_bisimilar, fun related =>
    takeTwo_stuck (moves_of_congruent (related.addRules {takeTwoSevens}).symm takeTwo_moves)⟩

/-! ## What the barbs see -/

/-- One row `5`. -/
def rowFive : State Tm ℕ := ⟨PUnit.unit, [], {0}, fun _ => c 5⟩

/-- **A free unknown is a may-barb of `5` and not a must-barb; a row `5` is both.** -/
theorem may_not_must :
    MayBarb X (pat (c 5)) rowX ∧ ¬ MustBarb X (pat (c 5)) rowX ∧ MustBarb X (pat (c 5)) rowFive := by
  refine ⟨variable_barbs 0 _, ?_, ⟨0, Finset.mem_singleton_self 0, fun b σ _ => ⟨σ, rfl⟩⟩⟩
  rintro ⟨o, -, every⟩
  obtain ⟨h, equated⟩ := every PUnit.unit (fun _ => c 6) (Frames.models_nil (X := X) _)
  have six : (c 6 : Term atoms) = Subst.applyTerm h (c 5) := equated
  exact absurd (Term.const.inj six) (by decide)

/-- Knowledge that equates two distinct constants. -/
def contradictory : State Tm ℕ := ⟨PUnit.unit, [(c 1, c 2)], {0}, fun _ => c 0⟩

/-- **At unsolvable knowledge every must-barb holds and no may-barb.** -/
theorem unsolvable_barbs :
    (∀ p : Pattern Tm, MustBarb X p contradictory) ∧ ∀ p : Pattern Tm, ¬ MayBarb X p contradictory := by
  have unsolvable : ¬ X.Solvable contradictory.knowledge := by
    rintro ⟨b, σ, solved⟩
    have same : Subst.applyTerm σ (c 1) = Subst.applyTerm σ (c 2) :=
      solved (c 1, c 2) (List.mem_singleton_self _)
    exact absurd (Term.const.inj same) (by decide)
  exact ⟨fun _ => mustBarb_of_unsolvable unsolvable (Finset.mem_singleton_self 0),
    fun _ => not_mayBarb_of_unsolvable unsolvable⟩

#print axioms renamed_example
#print axioms modulo_example
#print axioms deadRule_neverFires
#print axioms dead_example
#print axioms guard_example
#print axioms overlap_separates
#print axioms opening_avoids_y
#print axioms support_separates
#print axioms tautology_observable
#print axioms takeNine_stuck_empty
#print axioms dormant_rule_separated
#print axioms readMake_moves
#print axioms guarded_readMake_stuck
#print axioms guard_not_entailed_separated
#print axioms takeTwo_moves
#print axioms takeTwo_stuck
#print axioms queryFree_count_separates
#print axioms may_not_must
#print axioms unsolvable_barbs

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.AtOneFrame
