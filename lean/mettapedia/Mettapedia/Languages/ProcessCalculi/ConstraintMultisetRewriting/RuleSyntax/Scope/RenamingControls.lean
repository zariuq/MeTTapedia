import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope.Renaming
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope.CompositionControls

/-!
# Controls for scope: the side condition of scope extension, and extrusion through a row

Over the program and states of `CompositionControls`.

* **Scope extension needs the neighbour to be fixed** (`scope_extension_needs_fixed`): the swap of
  the unknowns `x` and `x₇` moves the unknown the neighbour constrains (`x = 6`). Beside the
  neighbour the request never succeeds (`CompositionControls.shared_success_unreachable`); beside the
  same neighbour the renamed request succeeds. So `scope_extension` fails without its hypothesis.
* **Extrusion through a row** (`extrusion_through_row`). A row is readable by every firing of the
  program, so a row whose label mentions a system's unknown hands that unknown to every reader. The
  system is the request (its row `0` labelled `x`); the neighbour has its own unknown `x₃`, a row `7`
  labelled `x₃` and the knowledge `x₃ = 6`. The two are private from each other, and the request's
  read-and-tell is admitted beside the neighbour (`admits_beside`). A **cross reader** (`joinRule`:
  read two rows, tell them equal) reads row `0` and row `7` together; after it, the same
  read-and-tell is refused, because the neighbour's knowledge now constrains `x` through `x₃`.
  What holds: privacy is kept by private steps, including those that make rows mentioning the
  system's own unknowns (`Composition.privateFrom_of_step`), since such rows stay on the system's
  side. What fails: privacy is not kept by firings that read rows of both sides; a present row
  mentioning an unknown is a channel to every reader of it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope.RenamingControls

open Mettapedia.Logic.LP
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open LogicOverTheStep.StepSpan (Succ)
open Examples (Tm X E x c shift everywhere)
open CompositionControls
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls
  (atoms action)

/-! ## Scope extension needs the neighbour to be fixed -/

/-- The swap of the unknowns `x` and `x₇`. -/
def swapSeven : Renaming action := permutation (sig := atoms) (Equiv.swap (0 : ℕ) 7)

theorem swapSeven_var (n : ℕ) : Subst.applyTerm swapSeven.forward (Term.var n) =
    Term.var ((Equiv.swap (0 : ℕ) 7) n) := rfl

theorem swapSeven_const (n : ℕ) : Subst.applyTerm swapSeven.forward (c n) = c n := rfl

/-- The swap does not fix the neighbour: it moves `x`. -/
theorem swapSeven_moves_neighbour :
    ¬ ∀ t, neighbour.Mentions t → Subst.applyTerm swapSeven.forward t = t := by
  intro fixed
  have moved := fixed x (Or.inl (by simp [neighbour]))
  rw [show x = (Term.var 0 : Term atoms) from rfl, swapSeven_var, Equiv.swap_apply_left] at moved
  exact absurd (Term.var.inj moved) (by decide)

theorem nine_fixed (t : Term atoms) : Subst.applyTerm swapSeven.forward t = c 9 ↔ t = c 9 := by
  constructor
  · intro moved
    have back : Subst.applyTerm swapSeven.backward (Subst.applyTerm swapSeven.forward t) = t :=
      swapSeven.back_forward t
    rw [moved] at back
    exact back.symm
  · rintro rfl
    rfl

theorem neighbour_unknowns {v : ℕ} (inside : UnknownsOf neighbour.Mentions v) : v = 0 := by
  obtain ⟨t, mentioned, member⟩ := inside
  rcases mentioned with first | second | ⟨o, present, -⟩
  · simp only [neighbour, List.map_cons, List.map_nil, List.mem_singleton] at first
    subst first
    exact freeVars_var 0 member
  · simp only [neighbour, List.map_cons, List.map_nil, List.mem_singleton] at second
    subst second
    exact (freeVars_const 6 member).elim
  · simp [neighbour] at present

/-- The unknowns of the renamed firing's footprint at the renamed request: `x₇` and `x₁`. -/
theorem renamed_footprint_unknowns {v : ℕ}
    (inside : UnknownsOf (Footprint action (renameState swapSeven request) (renameFiring swapSeven tellAt)) v) :
    v = 7 ∨ v = 1 := by
  obtain ⟨t, foot, member⟩ := inside
  rcases foot with mentioned | opened
  · obtain ⟨t₀, mentioned₀, rfl⟩ := (mentions_rename swapSeven request).mp mentioned
    have moved : action.apply swapSeven.forward t₀ = (Term.var 7 : Term atoms) := by
      rw [request_mentions mentioned₀]
      show (Term.var ((Equiv.swap (0 : ℕ) 7) 0) : Term atoms) = (Term.var 7 : Term atoms)
      rw [Equiv.swap_apply_left]
    rw [moved] at member
    exact Or.inl (freeVars_var 7 member)
  · obtain ⟨t₀, member₀, rfl⟩ := List.mem_map.mp opened
    rcases tellRule_terms member₀ with rfl | rfl | rfl
    · have opened' : action.apply (renameFiring swapSeven tellAt).opening x = (Term.var 1 : Term atoms) := by
        show Subst.applyTerm swapSeven.forward (Subst.applyTerm shift x) = (Term.var 1 : Term atoms)
        show (Term.var ((Equiv.swap (0 : ℕ) 7) 1) : Term atoms) = (Term.var 1 : Term atoms)
        rw [Equiv.swap_apply_of_ne_of_ne (a := (0 : ℕ)) (b := 7) (x := 1) (by decide) (by decide)]
      rw [opened'] at member
      exact Or.inr (freeVars_var 1 member)
    · exact (freeVars_const 5 member).elim
    · exact (freeVars_const 9 member).elim

/-- **Scope extension needs its side condition**: the swap moves the unknown the neighbour
constrains; beside the neighbour the request never succeeds, and the renamed request succeeds. -/
theorem scope_extension_needs_fixed :
    (¬ ∀ t, neighbour.Mentions t → Subst.applyTerm swapSeven.forward t = t) ∧
      (¬ ∃ t, Relation.ReflTransGen (Succ (step X ℕ E tellProgram).toStep) (beside neighbour request) t ∧
        Succeeds (· = c 9) t) ∧
      ∃ t, Relation.ReflTransGen (Succ (step X ℕ E tellProgram).toStep)
        (beside neighbour (renameState swapSeven request)) t ∧ Succeeds (· = c 9) t := by
  refine ⟨swapSeven_moves_neighbour, shared_success_unreachable, ?_⟩
  have admitted : (step X ℕ E tellProgram).Admits (s := renameState swapSeven request)
      (renameFiring swapSeven tellAt) := (admits_rename_iff swapSeven tellAt request).mpr tellAt_admitted
  have independent : Independent action neighbour.Mentions
      (Footprint action (renameState swapSeven request) (renameFiring swapSeven tellAt)) := by
    apply independent_of_disjoint
    intro v inD inFoot
    have zero := neighbour_unknowns inD
    rcases renamed_footprint_unknowns inFoot with seven | one <;> omega
  have succeeds : Succeeds (· = c 9) ((renameFiring swapSeven tellAt).result X (renameState swapSeven request)) := by
    rw [result_rename]
    exact (succeeds_rename_iff swapSeven nine_fixed _).mpr result_succeeds
  exact success_persists (.single ⟨renameFiring swapSeven tellAt, admitted, tellRule_positive, independent,
    by simp [neighbour], rfl⟩) succeeds (Finset.disjoint_empty_left _)
    ⟨everywhere 6, fun e member => by
      simp only [neighbour, List.mem_singleton] at member
      subst member
      rfl⟩

/-! ## Extrusion through a row -/

/-- **A cross reader**: read two rows and tell them equal. -/
def joinRule : Rule Tm := ⟨PUnit.unit, ⟨[], [x, .var 1], [(x, .var 1)], [], []⟩, []⟩

/-- The program with the read-and-tell and the cross reader. -/
def extrusionProgram : Program Tm := {tellRule, joinRule}

/-- The unknown `x₃`. -/
def three : Term atoms := .var 3

/-- **The neighbour with its own unknown**: a row `7` labelled `x₃`, and the knowledge `x₃ = 6`. -/
def ownRow : State Tm ℕ := ⟨PUnit.unit, [(three, c 6)], {7}, fun _ => three⟩

/-- The two side by side, written out. -/
def together : State Tm ℕ := ⟨PUnit.unit, [(three, c 6)], {0, 7}, fun o => if o = 7 then three else x⟩

theorem ownRow_apart : Disjoint ownRow.present request.present := by
  show Disjoint ({7} : Finset ℕ) ({0} : Finset ℕ)
  exact Finset.disjoint_singleton.mpr (by decide)

theorem together_eq : beside ownRow request = together := by
  apply state_ext
  · rfl
  · show ({7} ∪ {0} : Finset ℕ) = {0, 7}
    decide
  · funext o
    show (if o ∈ ({7} : Finset ℕ) then three else x) = (if o = 7 then three else x)
    by_cases seven : o = 7
    · subst seven
      simp
    · rw [if_neg (by simpa using seven), if_neg seven]

/-- The read-and-tell of the extrusion program, at row `0`. -/
def tellZero : Firing ℕ E extrusionProgram PUnit.unit :=
  ⟨tellRule, Or.inl rfl, PUnit.unit, shift, ⟨[], [0], [1]⟩, []⟩

/-- The opening that renames each unknown `n` to `n + 4`. -/
def shiftFour : Subst atoms := fun v => Term.var (v + 4)

/-- The cross reader at rows `0` and `7`, its unknowns opened as `x₄` and `x₅`. -/
def joinAt : Firing ℕ E extrusionProgram PUnit.unit :=
  ⟨joinRule, Or.inr rfl, PUnit.unit, shiftFour, ⟨[], [0, 7], []⟩, []⟩

theorem ownRow_unknowns {v : ℕ} (inside : UnknownsOf ownRow.Mentions v) : v = 3 := by
  obtain ⟨t, mentioned, member⟩ := inside
  rcases mentioned with first | second | ⟨o, -, rfl⟩
  · simp only [ownRow, List.map_cons, List.map_nil, List.mem_singleton] at first
    subst first
    exact freeVars_var 3 member
  · simp only [ownRow, List.map_cons, List.map_nil, List.mem_singleton] at second
    subst second
    exact (freeVars_const 6 member).elim
  · exact freeVars_var 3 member

/-- The footprint of the read-and-tell at the request. -/
theorem footprint_tellZero {t : Term atoms} (foot : Footprint action request tellZero t) :
    t = x ∨ t = (Term.var 1 : Term atoms) ∨ t = c 5 ∨ t = c 9 := by
  rcases foot with mentioned | opened
  · exact Or.inl (request_mentions mentioned)
  · obtain ⟨t₀, member, rfl⟩ := List.mem_map.mp opened
    rcases tellRule_terms member with rfl | rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))

theorem tellZero_admitted_alone : (step X ℕ E extrusionProgram).Admits (s := request) tellZero := by
  refine (admits_iff tellZero).mpr ⟨?_, ⟨List.nodup_nil, List.nodup_singleton 1, rfl, rfl, rfl,
    rfl⟩, ?_, ?_, ?_, ?_⟩
  · intro b g h
    refine ⟨fun v => if v = 1 then h 0 else g v, ?_, ?_⟩
    · intro t mentioned
      rw [request_mentions mentioned]
      rfl
    · intro t member
      rcases tellRule_terms member with rfl | rfl | rfl <;> rfl
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [tellZero, request, Selection.commit]
  · refine ⟨PUnit.unit, everywhere 5, fun e member => ?_⟩
    have known : tellZero.information X request =
        [((Term.var 1 : Term atoms), x), ((Term.var 1 : Term atoms), c 5)] := rfl
    rw [known] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl
  · intro check member
    simp [tellZero, tellRule, Firing.opened, RuleInstance.map] at member
  · intro q member
    simp [tellZero, tellRule, Firing.collectOpened] at member

/-- **Before the cross read, the read-and-tell is admitted beside the neighbour.** -/
theorem tellZero_admitted_before : (step X ℕ E extrusionProgram).Admits (s := together) tellZero := by
  rw [← together_eq]
  refine admits_beside action tellRule_positive tellZero_admitted_alone ownRow_apart
    (by simp [ownRow, tellZero]) ⟨everywhere 6, fun e member => by
      simp only [ownRow, List.mem_singleton] at member
      subst member
      rfl⟩ ?_
  apply independent_of_disjoint
  intro v inD inFoot
  have isThree := ownRow_unknowns inD
  obtain ⟨t, foot, member⟩ := inFoot
  rcases footprint_tellZero foot with rfl | rfl | rfl | rfl
  · have := freeVars_var 0 member
    omega
  · have := freeVars_var 1 member
    omega
  · exact freeVars_const 5 member
  · exact freeVars_const 9 member

theorem joinAt_information :
    joinAt.information X together =
      [(three, c 6), (Term.var 4, x), (Term.var 5, three), (Term.var 4, Term.var 5)] :=
  rfl

/-- **The cross reader is admitted**: it reads the request's row and the neighbour's row. -/
theorem joinAt_admitted : (step X ℕ E extrusionProgram).Admits (s := together) joinAt := by
  refine (admits_iff joinAt).mpr ⟨?_, ⟨List.nodup_nil, List.nodup_nil, rfl, rfl, rfl, rfl⟩, ?_, ?_,
    ?_, ?_⟩
  · intro b g h
    refine ⟨fun v => if v = 4 then h 0 else if v = 5 then h 1 else g v, ?_, ?_⟩
    · rintro t (first | second | ⟨o, present, rfl⟩)
      · simp only [together, List.map_cons, List.map_nil, List.mem_singleton] at first
        subst first
        rfl
      · simp only [together, List.map_cons, List.map_nil, List.mem_singleton] at second
        subst second
        rfl
      · simp only [together, Finset.mem_insert, Finset.mem_singleton] at present
        rcases present with rfl | rfl <;> rfl
    · intro t member
      simp only [joinAt, joinRule, Rule.terms, List.map_cons, List.map_nil, List.flatMap_nil,
        List.nil_append, List.append_nil, List.cons_append, List.mem_cons, List.not_mem_nil,
        or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> rfl
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [joinAt, together, Selection.commit]
  · rw [joinAt_information]
    refine ⟨PUnit.unit, everywhere 6, fun e member => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> rfl
  · intro check member
    simp [joinAt, joinRule, Firing.opened, RuleInstance.map] at member
  · intro q member
    simp [joinAt, joinRule, Firing.collectOpened] at member

/-- **After the cross read, the same read-and-tell is refused**: the neighbour's knowledge now
constrains `x`. -/
theorem tellZero_refused_after :
    ¬ (step X ℕ E extrusionProgram).Admits (s := joinAt.result X together) tellZero := by
  intro admitted
  obtain ⟨-, -, -, ⟨_, σ, solved⟩, -, -⟩ := (admits_iff (s := joinAt.result X together) tellZero).mp admitted
  have known : tellZero.information X (joinAt.result X together) =
      [(three, c 6), (Term.var 4, x), (Term.var 5, three), (Term.var 4, Term.var 5), (Term.var 1, x),
        (Term.var 1, c 5)] := rfl
  rw [known] at solved
  have six : σ 3 = c 6 := solved (three, c 6) (by simp)
  have four : σ 4 = σ 0 := solved (Term.var 4, x) (by simp)
  have five : σ 5 = σ 3 := solved (Term.var 5, three) (by simp)
  have linked : σ 4 = σ 5 := solved (Term.var 4, Term.var 5) (by simp)
  have one : σ 1 = σ 0 := solved (Term.var 1, x) (by simp)
  have told : σ 1 = c 5 := solved (Term.var 1, c 5) (by simp)
  have same : (c 5 : Term atoms) = c 6 :=
    told.symm.trans (one.trans (four.symm.trans (linked.trans (five.trans six))))
  exact absurd (Term.const.inj same) (by decide)

/-- **Extrusion through a row.** The request and the neighbour share no unknown; the read-and-tell of
the request is admitted beside the neighbour; a cross reader of the request's row and the
neighbour's row is admitted; after it, the same read-and-tell is refused. -/
theorem extrusion_through_row :
    Independent action ownRow.Mentions request.Mentions ∧
      (step X ℕ E extrusionProgram).Admits (s := beside ownRow request) tellZero ∧
      (step X ℕ E extrusionProgram).Admits (s := beside ownRow request) joinAt ∧
      ¬ (step X ℕ E extrusionProgram).Admits (s := joinAt.result X (beside ownRow request)) tellZero := by
  rw [together_eq]
  refine ⟨?_, tellZero_admitted_before, joinAt_admitted, tellZero_refused_after⟩
  apply independent_of_disjoint
  intro v inD inC
  have isThree := ownRow_unknowns inD
  obtain ⟨t, mentioned, member⟩ := inC
  rw [request_mentions mentioned] at member
  have := freeVars_var 0 member
  omega

#print axioms scope_extension_needs_fixed
#print axioms tellZero_admitted_before
#print axioms joinAt_admitted
#print axioms tellZero_refused_after
#print axioms extrusion_through_row

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope.RenamingControls
