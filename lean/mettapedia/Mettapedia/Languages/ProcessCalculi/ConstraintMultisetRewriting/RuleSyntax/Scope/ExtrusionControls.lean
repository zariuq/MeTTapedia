import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope.RenamingControls

/-!
# Extrusion of a fresh unknown by a made row

The system holds a token row `0`. Its rule `makeRule` takes the token and makes a row labelled by
the rule's own unknown, which the opening makes fresh: the made row `2` carries the new unknown
`x₅`, which nothing else mentions. The neighbour (`RenamingControls.ownRow`) has its own unknown
`x₃`, a row `7` labelled `x₃`, and the knowledge `x₃ = 6`.

* **The law that holds** (`make_is_private`): the making firing is a private step of the system
  beside the neighbour, and after it the system is still private from the neighbour
  (`Composition.privateFrom_of_step`): a made row stays on the system's side.
* **What a reader may then do** (`extrusion_by_make`): the read-and-tell of the made row is admitted
  beside the neighbour; a cross reader (`RenamingControls.joinRule`) reads the made row and the
  neighbour's row together and is admitted; after it, the same read-and-tell is refused, since
  `x₅` is now tied to `x₃ = 6`.
* **The law that fails**: privacy of the made unknown is not kept by firings that read rows of both
  sides; the made row is a channel to every reader of it, as in scope extrusion.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope.ExtrusionControls

open Mettapedia.Logic.LP
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open LogicOverTheStep.StepSpan (Succ)
open Examples (Tm X E x c everywhere)
open CompositionControls (tellRule tellRule_positive tellRule_terms freeVars_var freeVars_const)
open RenamingControls (joinRule ownRow three ownRow_unknowns)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls
  (atoms action)

/-- **Take the token `0`, make a row labelled by the rule's own unknown.** -/
def makeRule : Rule Tm := ⟨PUnit.unit, ⟨[c 0], [], [], [], [x]⟩, []⟩

theorem makeRule_positive : Positive makeRule :=
  ⟨fun _ member => absurd member List.not_mem_nil, rfl⟩

theorem makeRule_terms {t : Term atoms} (member : t ∈ makeRule.terms) : t = c 0 ∨ t = x := by
  simp only [makeRule, Rule.terms, List.map_nil, List.flatMap_nil, List.nil_append, List.append_nil,
    List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at member
  exact member

/-- The program: make, cross read, read-and-tell. -/
def madeProgram : Program Tm := {makeRule, joinRule, tellRule}

/-- The system: one token row `0`. -/
def token : State Tm ℕ := ⟨PUnit.unit, [], {0}, fun _ => c 0⟩

/-- The opening that renames each unknown `n` to `n + k`. -/
def shiftBy (k : ℕ) : Subst atoms := fun v => Term.var (v + k)

/-- Take the token, make row `2`, the rule's unknown opened as `x₅`. -/
def makeAt : Firing ℕ E madeProgram PUnit.unit :=
  ⟨makeRule, Or.inl rfl, PUnit.unit, shiftBy 5, ⟨[0], [], [2]⟩, []⟩

/-- The unknown `x₅`. -/
def five : Term atoms := .var 5

theorem token_mentions {t : Term atoms} (mentioned : token.Mentions t) : t = c 0 := by
  rcases mentioned with first | second | ⟨o, -, rfl⟩
  · simp [token] at first
  · simp [token] at second
  · rfl

theorem makeAt_admitted : (step X ℕ E madeProgram).Admits (s := token) makeAt := by
  refine (admits_iff makeAt).mpr ⟨?_, ⟨List.nodup_singleton 0, List.nodup_singleton 2, rfl, rfl, rfl,
    rfl⟩, ?_, ?_, ?_, ?_⟩
  · intro b g h
    refine ⟨fun v => if v = 5 then h 0 else g v, fun t mentioned => ?_, fun t member => ?_⟩
    · rw [token_mentions mentioned]
      rfl
    · rcases makeRule_terms member with rfl | rfl <;> rfl
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [makeAt, token, Selection.commit]
  · refine ⟨PUnit.unit, Subst.id atoms, fun e member => ?_⟩
    have known : makeAt.information X token = [(c 0, c 0)] := rfl
    rw [known, List.mem_singleton] at member
    subst member
    rfl
  · intro check member
    simp [makeAt, makeRule, Firing.opened, RuleInstance.map] at member
  · intro q member
    simp [makeAt, makeRule, Firing.collectOpened] at member

/-- After the make: the made row `2` carries the fresh unknown `x₅`. -/
def afterMake : State Tm ℕ := makeAt.result X token

theorem afterMake_label : afterMake.label 2 = five := rfl

theorem makeAt_footprint_unknowns {v : ℕ} (inside : UnknownsOf (Footprint action token makeAt) v) : v = 5 := by
  obtain ⟨t, foot, member⟩ := inside
  rcases foot with mentioned | opened
  · rw [token_mentions mentioned] at member
    exact (freeVars_const 0 member).elim
  · obtain ⟨t₀, member₀, rfl⟩ := List.mem_map.mp opened
    rcases makeRule_terms member₀ with rfl | rfl
    · exact (freeVars_const 0 member).elim
    · exact freeVars_var 5 member

/-- **The law that holds**: making the row with the fresh unknown is a private step of the system
beside the neighbour, and afterwards the system is still private from the neighbour. -/
theorem make_is_private :
    PrivateStep action madeProgram ownRow token afterMake ∧ PrivateFrom action ownRow afterMake := by
  have step' : PrivateStep action madeProgram ownRow token afterMake := by
    refine ⟨makeAt, makeAt_admitted, makeRule_positive, ?_, by simp [makeAt, ownRow], rfl⟩
    apply independent_of_disjoint
    intro v inD inFoot
    have isThree := ownRow_unknowns inD
    have isFive := makeAt_footprint_unknowns inFoot
    omega
  exact ⟨step', privateFrom_of_step step'⟩

/-- The neighbour beside the system after the make, written out. -/
def besideAfter : State Tm ℕ :=
  ⟨PUnit.unit, [(three, c 6), (c 0, c 0)], {2, 7},
    fun o => if o = 7 then three else if o = 2 then five else c 0⟩

theorem besideAfter_eq : beside ownRow afterMake = besideAfter := by
  apply state_ext
  · rfl
  · show ({7} ∪ fire {0} ((⟨[0], [], [2]⟩ : Selection ℕ).commit (T := Unit)) : Finset ℕ) = {2, 7}
    decide
  · funext o
    show (if o ∈ ({7} : Finset ℕ) then three else afterMake.label o) =
      (if o = 7 then three else if o = 2 then five else c 0)
    by_cases seven : o = 7
    · subst seven
      simp
    · rw [if_neg (by simpa using seven), if_neg seven]
      show relabel (makeAt.row X token) [2] [Subst.applyTerm (shiftBy 5) x] o = if o = 2 then five else c 0
      by_cases two : o = 2
      · subst two
        rfl
      · simp only [relabel, if_neg two]
        rfl

/-- The read-and-tell of the made row: read row `2`, tell it equal to `5`, make row `11`; the rule's
unknown opened as `x₁₀`. -/
def tellMade : Firing ℕ E madeProgram PUnit.unit :=
  ⟨tellRule, Or.inr (Or.inr rfl), PUnit.unit, shiftBy 10, ⟨[], [2], [11]⟩, []⟩

/-- The cross reader of the made row and the neighbour's row, its unknowns opened as `x₈`, `x₉`. -/
def joinMade : Firing ℕ E madeProgram PUnit.unit :=
  ⟨joinRule, Or.inr (Or.inl rfl), PUnit.unit, shiftBy 8, ⟨[], [2, 7], []⟩, []⟩

theorem afterMake_mentions {t : Term atoms} (mentioned : afterMake.Mentions t) : t = c 0 ∨ t = five := by
  rcases mentioned with first | second | ⟨o, present, rfl⟩
  · have known : afterMake.knowledge = [(c 0, c 0)] := rfl
    rw [known] at first
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at first
    exact Or.inl first
  · have known : afterMake.knowledge = [(c 0, c 0)] := rfl
    rw [known] at second
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at second
    exact Or.inl second
  · have isTwo : o = 2 := by
      have inside : o ∈ fire ({0} : Finset ℕ) ((⟨[0], [], [2]⟩ : Selection ℕ).commit (T := Unit)) := present
      simpa [fire, Selection.commit] using inside
    subst isTwo
    exact Or.inr rfl

theorem tellMade_admitted_alone : (step X ℕ E madeProgram).Admits (s := afterMake) tellMade := by
  refine (admits_iff tellMade).mpr ⟨?_, ⟨List.nodup_nil, List.nodup_singleton 11, rfl, rfl, rfl,
    rfl⟩, ?_, ?_, ?_, ?_⟩
  · intro b g h
    refine ⟨fun v => if v = 10 then h 0 else g v, fun t mentioned => ?_, fun t member => ?_⟩
    · rcases afterMake_mentions mentioned with rfl | rfl <;> rfl
    · rcases tellRule_terms member with rfl | rfl | rfl <;> rfl
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [tellMade, afterMake, makeAt, token, Firing.result, fire,
      Selection.commit]
  · refine ⟨PUnit.unit, everywhere 5, fun e member => ?_⟩
    have known : tellMade.information X afterMake =
        [(c 0, c 0), ((Term.var 10 : Term atoms), five), ((Term.var 10 : Term atoms), c 5)] := rfl
    rw [known] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> rfl
  · intro check member
    simp [tellMade, tellRule, Firing.opened, RuleInstance.map] at member
  · intro q member
    simp [tellMade, tellRule, Firing.collectOpened] at member

theorem tellMade_footprint_unknowns {v : ℕ} (inside : UnknownsOf (Footprint action afterMake tellMade) v) :
    v = 5 ∨ v = 10 := by
  obtain ⟨t, foot, member⟩ := inside
  rcases foot with mentioned | opened
  · rcases afterMake_mentions mentioned with rfl | rfl
    · exact (freeVars_const 0 member).elim
    · exact Or.inl (freeVars_var 5 member)
  · obtain ⟨t₀, member₀, rfl⟩ := List.mem_map.mp opened
    rcases tellRule_terms member₀ with rfl | rfl | rfl
    · exact Or.inr (freeVars_var 10 member)
    · exact (freeVars_const 5 member).elim
    · exact (freeVars_const 9 member).elim

theorem apart_after : Disjoint ownRow.present afterMake.present := by
  show Disjoint ({7} : Finset ℕ) (fire ({0} : Finset ℕ) ((⟨[0], [], [2]⟩ : Selection ℕ).commit (T := Unit)))
  decide

/-- **Before the cross read, the read-and-tell of the made row is admitted beside the neighbour.** -/
theorem tellMade_admitted_before : (step X ℕ E madeProgram).Admits (s := besideAfter) tellMade := by
  rw [← besideAfter_eq]
  refine admits_beside action tellRule_positive tellMade_admitted_alone apart_after
    (by simp [ownRow, tellMade]) ⟨everywhere 6, fun e member => by
      simp only [ownRow, List.mem_singleton] at member
      subst member
      rfl⟩ ?_
  apply independent_of_disjoint
  intro v inD inFoot
  have isThree := ownRow_unknowns inD
  rcases tellMade_footprint_unknowns inFoot with isFive | isTen <;> omega

theorem joinMade_admitted : (step X ℕ E madeProgram).Admits (s := besideAfter) joinMade := by
  refine (admits_iff joinMade).mpr ⟨?_, ⟨List.nodup_nil, List.nodup_nil, rfl, rfl, rfl, rfl⟩, ?_, ?_,
    ?_, ?_⟩
  · intro b g h
    refine ⟨fun v => if v = 8 then h 0 else if v = 9 then h 1 else g v, ?_, ?_⟩
    · rintro t (first | second | ⟨o, present, rfl⟩)
      · simp only [besideAfter, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
          or_false] at first
        rcases first with rfl | rfl <;> rfl
      · simp only [besideAfter, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
          or_false] at second
        rcases second with rfl | rfl <;> rfl
      · simp only [besideAfter, Finset.mem_insert, Finset.mem_singleton] at present
        rcases present with rfl | rfl <;> rfl
    · intro t member
      simp only [joinMade, joinRule, Rule.terms, List.map_cons, List.map_nil, List.flatMap_nil,
        List.nil_append, List.append_nil, List.cons_append, List.mem_cons, List.not_mem_nil,
        or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> rfl
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [joinMade, besideAfter, Selection.commit]
  · refine ⟨PUnit.unit, everywhere 6, fun e member => ?_⟩
    have known : joinMade.information X besideAfter =
        [(three, c 6), (c 0, c 0), ((Term.var 8 : Term atoms), five), ((Term.var 9 : Term atoms), three),
          ((Term.var 8 : Term atoms), (Term.var 9 : Term atoms))] := rfl
    rw [known] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> rfl
  · intro check member
    simp [joinMade, joinRule, Firing.opened, RuleInstance.map] at member
  · intro q member
    simp [joinMade, joinRule, Firing.collectOpened] at member

theorem tellMade_refused_after :
    ¬ (step X ℕ E madeProgram).Admits (s := joinMade.result X besideAfter) tellMade := by
  intro admitted
  obtain ⟨-, -, -, ⟨_, σ, solved⟩, -, -⟩ :=
    (admits_iff (s := joinMade.result X besideAfter) tellMade).mp admitted
  have known : tellMade.information X (joinMade.result X besideAfter) =
      [(three, c 6), (c 0, c 0), ((Term.var 8 : Term atoms), five), ((Term.var 9 : Term atoms), three),
        ((Term.var 8 : Term atoms), (Term.var 9 : Term atoms)), ((Term.var 10 : Term atoms), five),
        ((Term.var 10 : Term atoms), c 5)] := rfl
  rw [known] at solved
  have six : σ 3 = c 6 := solved (three, c 6) (by simp)
  have eight : σ 8 = σ 5 := solved ((Term.var 8 : Term atoms), five) (by simp)
  have nine : σ 9 = σ 3 := solved ((Term.var 9 : Term atoms), three) (by simp)
  have linked : σ 8 = σ 9 := solved ((Term.var 8 : Term atoms), (Term.var 9 : Term atoms)) (by simp)
  have ten : σ 10 = σ 5 := solved ((Term.var 10 : Term atoms), five) (by simp)
  have told : σ 10 = c 5 := solved ((Term.var 10 : Term atoms), c 5) (by simp)
  have same : (c 5 : Term atoms) = c 6 :=
    told.symm.trans (ten.trans (eight.symm.trans (linked.trans (nine.trans six))))
  exact absurd (Term.const.inj same) (by decide)

/-- **Extrusion by a made row.** The make is a private step; afterwards, the read-and-tell of the made
row is admitted beside the neighbour; a cross reader of the made row and the neighbour's row is
admitted; after it, the same read-and-tell is refused. -/
theorem extrusion_by_make :
    PrivateStep action madeProgram ownRow token afterMake ∧
      (step X ℕ E madeProgram).Admits (s := beside ownRow afterMake) tellMade ∧
      (step X ℕ E madeProgram).Admits (s := beside ownRow afterMake) joinMade ∧
      ¬ (step X ℕ E madeProgram).Admits (s := joinMade.result X (beside ownRow afterMake)) tellMade := by
  rw [besideAfter_eq]
  exact ⟨make_is_private.1, tellMade_admitted_before, joinMade_admitted, tellMade_refused_after⟩

#print axioms make_is_private
#print axioms tellMade_admitted_before
#print axioms joinMade_admitted
#print axioms tellMade_refused_after
#print axioms extrusion_by_make

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope.ExtrusionControls
