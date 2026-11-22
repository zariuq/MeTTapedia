import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope.Composition
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Examples

/-!
# Controls for composition: each hypothesis is needed

Over first-order atoms at the one frame (`Examples`), one positive program: `tellRule` reads any row
`y`, tells `y = 5` and makes the row `9`. It has no check and no collect query (`tellRule_positive`). The
request holds one row labelled by the caller's unknown `x`; alone it fires and succeeds
(`tellAt_admitted`, `request_succeeds`).

* **A shared unknown** (a positive program; no absence is involved): the neighbour has no rows and
  knowledge `x = 6`. The two are composable (`shared_composable`: disjoint rows, jointly solvable
  knowledge), they share the unknown `x` (`shared_not_independent`), and beside the neighbour no
  firing of the program is admitted (`nothing_admitted_beside`), so success is unreachable
  (`shared_success_unreachable`). What fails is exactly the joint solution of `admits_beside_iff`
  (`shared_no_joint`).
* **A private neighbour** (`privateNeighbour`, knowledge `x₅ = 6`): it shares no unknown with the
  footprint (`private_independent`), the firing is admitted beside it (`private_admitted`) and success
  persists (`private_succeeds`), by `admits_beside` and `success_persists`.
* **Absence is not saved by privacy**: over ground rows every family is independent of every other
  (`ground_independent`), yet a firing that makes `8` where `7` is absent is admitted alone and refused
  beside a ground row `7` (`absence_refused_beside_ground`); so is a collect query that claims to see no row
  `7` (`collect_refused_beside_ground`). Positivity (equation checks, no collect query) is needed.
* **The neighbour must be solvable**: a neighbour with private but contradictory knowledge is
  independent of the footprint and still refuses (`unsolvable_refuses`).
* **The firing's own unknowns are in its footprint**: a neighbour whose knowledge only mentions the
  unknown the opening uses (`x₁ = x₁`, which constrains nothing) leaves a joint solution
  (`opened_joint`) and makes the opening not fresh (`opened_not_fresh`), so the firing is refused;
  the same rule opened apart (`tellAtTwo`) is admitted beside it (`reopened_admitted`). This sharing
  is removed by renaming the opening, not by any change of knowledge.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope.CompositionControls

open Mettapedia.Logic.LP
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open LogicOverTheStep.StepSpan (Succ)
open Examples (Tm X E x c shift everywhere fresh_of_ground)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls
  (atoms action)

/-! ## The positive program and the request -/

/-- **The positive rule**: read any row `y`, tell `y = 5`, make the row `9`. -/
def tellRule : Rule Tm := ⟨PUnit.unit, ⟨[], [x], [(x, c 5)], [], [c 9]⟩, []⟩

theorem tellRule_positive : Positive tellRule :=
  ⟨fun _ member => absurd member List.not_mem_nil, rfl⟩

/-- The program of that one rule. -/
def tellProgram : Program Tm := {tellRule}

/-- A request row at identity `0`, labelled by the caller's unknown `x`. -/
def request : State Tm ℕ := ⟨PUnit.unit, [], {0}, fun _ => x⟩

/-- Read the request with the rule's `y` opened as `x₁`, make identity `1`. -/
def tellAt : Firing ℕ E tellProgram PUnit.unit :=
  ⟨tellRule, rfl, PUnit.unit, shift, ⟨[], [0], [1]⟩, []⟩

/-- The opening that renames each unknown `n` to `n + 2`. -/
def shiftTwo : Subst atoms := fun v => Term.var (v + 2)

/-- The same firing with the rule's `y` opened as `x₂`. -/
def tellAtTwo : Firing ℕ E tellProgram PUnit.unit :=
  ⟨tellRule, rfl, PUnit.unit, shiftTwo, ⟨[], [0], [1]⟩, []⟩

theorem request_mentions {t : Term atoms} (mentioned : request.Mentions t) : t = x := by
  rcases mentioned with first | second | ⟨o, -, rfl⟩
  · simp [request] at first
  · simp [request] at second
  · rfl

theorem tellRule_terms {t : Term atoms} (member : t ∈ tellRule.terms) :
    t = x ∨ t = c 5 ∨ t = c 9 := by
  simp only [tellRule, Rule.terms, List.map_cons, List.map_nil, List.flatMap_nil,
    List.nil_append, List.append_nil, List.cons_append, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

/-- The footprint of a firing of the rule at the request: the caller's unknown, the opened unknown,
and the constants `5` and `9`. -/
theorem footprint_request (g : Firing ℕ E tellProgram PUnit.unit) (rule : g.rule = tellRule)
    {t : Term atoms} (foot : Footprint action request g t) :
    t = x ∨ t = Subst.applyTerm g.opening x ∨ t = c 5 ∨ t = c 9 := by
  rcases foot with mentioned | opened
  · exact Or.inl (request_mentions mentioned)
  · obtain ⟨t₀, member, rfl⟩ := List.mem_map.mp opened
    rw [rule] at member
    rcases tellRule_terms member with rfl | rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))

theorem freeVars_var (n : ℕ) {v : ℕ} (inside : v ∈ (Term.var n : Term atoms).freeVars) : v = n := by
  simpa [Term.freeVars] using inside

theorem freeVars_const (n : ℕ) {v : ℕ} (inside : v ∈ (Term.const n : Term atoms).freeVars) : False := by
  simp [Term.freeVars] at inside

/-- The unknowns of the footprint of `tellAt` at the request are `x` and `x₁`. -/
theorem footprint_unknowns {v : ℕ} (inside : UnknownsOf (Footprint action request tellAt) v) :
    v = 0 ∨ v = 1 := by
  obtain ⟨t, foot, member⟩ := inside
  rcases footprint_request tellAt rfl foot with rfl | rfl | rfl | rfl
  · exact Or.inl (freeVars_var 0 member)
  · exact Or.inr (freeVars_var 1 member)
  · exact (freeVars_const 5 member).elim
  · exact (freeVars_const 9 member).elim

/-- The unknowns of the footprint of `tellAtTwo` at the request are `x` and `x₂`. -/
theorem footprintTwo_unknowns {v : ℕ} (inside : UnknownsOf (Footprint action request tellAtTwo) v) :
    v = 0 ∨ v = 2 := by
  obtain ⟨t, foot, member⟩ := inside
  rcases footprint_request tellAtTwo rfl foot with rfl | rfl | rfl | rfl
  · exact Or.inl (freeVars_var 0 member)
  · exact Or.inr (freeVars_var 2 member)
  · exact (freeVars_const 5 member).elim
  · exact (freeVars_const 9 member).elim

/-! ## Alone, the request fires and succeeds -/

theorem tellAt_information : tellAt.information X request = [(.var 1, x), (.var 1, c 5)] := rfl

theorem tellAtTwo_information : tellAtTwo.information X request = [(.var 2, x), (.var 2, c 5)] := rfl

theorem tellAt_fresh : tellAt.Fresh X request := by
  intro b g h
  refine ⟨fun v => if v = 1 then h 0 else g v, ?_, ?_⟩
  · intro t mentioned
    rw [request_mentions mentioned]
    rfl
  · intro t member
    rcases tellRule_terms member with rfl | rfl | rfl <;> rfl

theorem tellAtTwo_fresh : tellAtTwo.Fresh X request := by
  intro b g h
  refine ⟨fun v => if v = 2 then h 0 else g v, ?_, ?_⟩
  · intro t mentioned
    rw [request_mentions mentioned]
    rfl
  · intro t member
    rcases tellRule_terms member with rfl | rfl | rfl <;> rfl

theorem tellAt_admitted : (step X ℕ E tellProgram).Admits (s := request) tellAt := by
  refine (admits_iff tellAt).mpr ⟨tellAt_fresh, ⟨List.nodup_nil, List.nodup_singleton 1, rfl, rfl, rfl,
    rfl⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [tellAt, request, Selection.commit]
  · rw [tellAt_information]
    refine ⟨PUnit.unit, everywhere 5, fun e member => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl
  · intro check member
    simp [tellAt, tellRule, Firing.opened, RuleInstance.map] at member
  · intro q member
    simp [tellAt, tellRule, Firing.collectOpened] at member

theorem tellAtTwo_admitted : (step X ℕ E tellProgram).Admits (s := request) tellAtTwo := by
  refine (admits_iff tellAtTwo).mpr ⟨tellAtTwo_fresh, ⟨List.nodup_nil, List.nodup_singleton 1, rfl, rfl,
    rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [tellAtTwo, request, Selection.commit]
  · rw [tellAtTwo_information]
    refine ⟨PUnit.unit, everywhere 5, fun e member => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl
  · intro check member
    simp [tellAtTwo, tellRule, Firing.opened, RuleInstance.map] at member
  · intro q member
    simp [tellAtTwo, tellRule, Firing.collectOpened] at member

theorem result_succeeds : Succeeds (· = c 9) (tellAt.result X request) :=
  ⟨1, by simp [Firing.result, tellAt, request, fire, Selection.commit], rfl⟩

/-- **Alone, the request succeeds.** -/
theorem request_succeeds :
    ∃ t, Relation.ReflTransGen (Succ (step X ℕ E tellProgram).toStep) request t ∧
      Succeeds (· = c 9) t :=
  ⟨_, .single ⟨tellAt, tellAt_admitted, rfl⟩, result_succeeds⟩

/-! ## A shared unknown: the neighbour's knowledge contradicts the tell -/

/-- **The neighbour**: no rows, and the knowledge `x = 6`. -/
def neighbour : State Tm ℕ := ⟨PUnit.unit, [(x, c 6)], ∅, fun _ => c 0⟩

theorem neighbour_apart : Disjoint neighbour.present request.present := Finset.disjoint_empty_left _

/-- **Composable**: disjoint rows, jointly solvable knowledge. -/
theorem shared_composable :
    Disjoint neighbour.present request.present ∧
      action.Consistent (neighbour.knowledge ++ request.knowledge) :=
  ⟨neighbour_apart, ⟨everywhere 6, fun e member => by
    simp only [neighbour, request, List.append_nil, List.mem_singleton] at member
    subst member
    rfl⟩⟩

/-- **They share the unknown `x`**: the neighbour is not independent of the footprint. -/
theorem shared_not_independent :
    ¬ Independent action neighbour.Mentions (Footprint action request tellAt) :=
  not_independent_of_shared (a := c 0) (b := c 1) (v := 0) (by simp [c])
    ⟨x, Or.inl (by simp [neighbour]), by simp [x, Term.freeVars]⟩
    ⟨x, Or.inl (Or.inr (Or.inr ⟨0, Finset.mem_singleton_self 0, rfl⟩)), by simp [x, Term.freeVars]⟩

/-- **No joint solution**: what `admits_beside_iff` asks fails. -/
theorem shared_no_joint :
    ¬ ∃ σ : Subst atoms, action.Models σ (tellAt.information X request) ∧
      action.Models σ neighbour.knowledge := by
  rintro ⟨σ, onC, onD⟩
  rw [tellAt_information] at onC
  have six : σ 0 = c 6 := onD (x, c 6) List.mem_cons_self
  have read : σ 1 = σ 0 := onC (.var 1, x) List.mem_cons_self
  have five : σ 1 = c 5 := onC (.var 1, c 5) (List.mem_cons_of_mem _ List.mem_cons_self)
  have same : (c 5 : Term atoms) = c 6 := five.symm.trans (read.trans six)
  exact absurd (Term.const.inj same) (by decide)

/-- **Beside the neighbour no firing of the program is admitted**: every firing reads the request
row, so its information equates `5` and `6` through `x`. -/
theorem nothing_admitted_beside (g : Firing ℕ E tellProgram PUnit.unit) :
    ¬ (step X ℕ E tellProgram).Admits (s := beside neighbour request) g := by
  obtain ⟨rule, member, ext, opening, ⟨taken, read, made⟩, seen⟩ := g
  have isTell : rule = tellRule := member
  subst isTell
  intro admitted
  obtain ⟨-, ⟨-, -, takeLength, readLength, -, -⟩, enabled, ⟨_, σ, solved⟩, -, -⟩ :=
    (admits_iff (s := beside neighbour request) _).mp admitted
  have noTake : taken = [] := List.length_eq_zero_iff.mp takeLength.symm
  subst noTake
  obtain ⟨o, rfl⟩ := List.length_eq_one_iff.mp readLength.symm
  have present : o ∈ (beside neighbour request).present :=
    enabled.kept_subset (by simp [Selection.commit])
  have isZero : o = 0 := by simpa [beside, neighbour, request] using present
  subst isZero
  have known := information_beside action
    ⟨tellRule, member, ext, opening, ⟨[], [0], made⟩, seen⟩ neighbour_apart (by
      rintro o (inside | inside)
      · simp at inside
      · simp only [List.mem_singleton] at inside
        subst inside
        exact Finset.mem_singleton_self 0)
  rw [known] at solved
  have atRequest : Firing.information X request ⟨tellRule, member, ext, opening, ⟨[], [0], made⟩, seen⟩ =
      [(Subst.applyTerm opening x, x), (Subst.applyTerm opening x, c 5)] := rfl
  rw [atRequest] at solved
  have six : σ 0 = c 6 := solved (x, c 6) List.mem_cons_self
  have read : Subst.applyTerm σ (Subst.applyTerm opening x) = σ 0 :=
    solved _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have five : Subst.applyTerm σ (Subst.applyTerm opening x) = c 5 :=
    solved _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have same : (c 5 : Term atoms) = c 6 := five.symm.trans (read.trans six)
  exact absurd (Term.const.inj same) (by decide)

/-- **Beside the neighbour, success is unreachable.** -/
theorem shared_success_unreachable :
    ¬ ∃ t, Relation.ReflTransGen (Succ (step X ℕ E tellProgram).toStep) (beside neighbour request) t ∧
      Succeeds (· = c 9) t := by
  rintro ⟨t, run, succeeds⟩
  rcases Relation.ReflTransGen.cases_head run with rfl | ⟨_, ⟨g, admitted, -⟩, -⟩
  · obtain ⟨o, present, isNine⟩ := succeeds
    have isZero : o = 0 := by simpa [beside, neighbour, request] using present
    subst isZero
    have label : (beside neighbour request).label 0 = x :=
      beside_label_right neighbour_apart (Finset.mem_singleton_self 0)
    have wrong : (x : Term atoms) = c 9 := label.symm.trans isNine
    exact absurd wrong (by simp [x, c])
  · exact nothing_admitted_beside g admitted

/-! ## A private neighbour -/

/-- **A private neighbour**: no rows, and the knowledge `x₅ = 6`. -/
def privateNeighbour : State Tm ℕ := ⟨PUnit.unit, [(.var 5, c 6)], ∅, fun _ => c 0⟩

theorem privateNeighbour_unknowns {v : ℕ} (inside : UnknownsOf privateNeighbour.Mentions v) :
    v = 5 := by
  obtain ⟨t, mentioned, member⟩ := inside
  rcases mentioned with first | second | ⟨o, present, -⟩
  · simp only [privateNeighbour, List.map_cons, List.map_nil, List.mem_singleton] at first
    subst first
    exact freeVars_var 5 member
  · simp only [privateNeighbour, List.map_cons, List.map_nil, List.mem_singleton] at second
    subst second
    exact (freeVars_const 6 member).elim
  · simp [privateNeighbour] at present

/-- **It shares no unknown with the footprint.** -/
theorem private_independent :
    Independent action privateNeighbour.Mentions (Footprint action request tellAt) := by
  apply independent_of_disjoint
  intro v inD inFoot
  have five := privateNeighbour_unknowns inD
  rcases footprint_unknowns inFoot with zero | one <;> omega

/-- **The firing is admitted beside it.** -/
theorem private_admitted :
    (step X ℕ E tellProgram).Admits (s := beside privateNeighbour request) tellAt :=
  admits_beside action tellRule_positive tellAt_admitted (Finset.disjoint_empty_left _)
    (by simp [privateNeighbour]) ⟨everywhere 6, fun e member => by
      simp only [privateNeighbour, List.mem_singleton] at member
      subst member
      rfl⟩ private_independent

/-- **Success persists beside it.** -/
theorem private_succeeds :
    ∃ t, Relation.ReflTransGen (Succ (step X ℕ E tellProgram).toStep) (beside privateNeighbour request) t ∧
      Succeeds (· = c 9) t :=
  success_persists (.single ⟨tellAt, tellAt_admitted, tellRule_positive, private_independent,
    by simp [privateNeighbour], rfl⟩) result_succeeds (Finset.disjoint_empty_left _)
    ⟨everywhere 6, fun e member => by
      simp only [privateNeighbour, List.mem_singleton] at member
      subst member
      rfl⟩

/-! ## Absence over ground rows: independent, and still refused -/

/-- Make `8` where `7` is absent. -/
def spawnRule : Rule Tm := ⟨PUnit.unit, ⟨[], [], [], [.predicate .none (c 7)], [c 8]⟩, []⟩

/-- The program of that one rule. -/
def spawnProgram : Program Tm := {spawnRule}

/-- The empty store. -/
def emptyState : State Tm ℕ := ⟨PUnit.unit, [], ∅, fun _ => c 0⟩

/-- One ground row `7`. -/
def groundRow : State Tm ℕ := ⟨PUnit.unit, [], {0}, fun _ => c 7⟩

/-- The spawn firing, making identity `1`. -/
def spawnAt : Firing ℕ E spawnProgram PUnit.unit :=
  ⟨spawnRule, rfl, PUnit.unit, Subst.id atoms, ⟨[], [], [1]⟩, []⟩

theorem spawnAt_admitted : (step X ℕ E spawnProgram).Admits (s := emptyState) spawnAt := by
  refine (admits_iff spawnAt).mpr ⟨?_, ⟨List.nodup_nil, List.nodup_singleton 1, rfl, rfl, rfl, rfl⟩,
    ?_, ⟨PUnit.unit, Subst.id atoms, fun e member => by cases member⟩, ?_, ?_⟩
  · apply fresh_of_ground action emptyState spawnAt
    intro t member σ
    simp only [spawnAt, spawnRule, Rule.terms, checkTerms, List.map_nil, List.flatMap_cons,
      List.flatMap_nil, List.nil_append, List.append_nil, List.cons_append, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [spawnAt, emptyState, Selection.commit]
  · intro check member b σ _
    simp only [spawnAt, spawnRule, Firing.opened, RuleInstance.map, List.map_cons, List.map_nil,
      Check.map, List.mem_singleton] at member
    subst member
    intro o present
    simp [emptyState] at present
  · intro q member
    simp [spawnAt, spawnRule, Firing.collectOpened] at member

theorem groundRow_fixed : Fixed action groundRow.Mentions := by
  rintro t (first | second | ⟨o, -, rfl⟩) σ
  · simp [groundRow] at first
  · simp [groundRow] at second
  · rfl

/-- **Over ground rows everything is independent.** -/
theorem ground_independent : Independent action groundRow.Mentions (Footprint action emptyState spawnAt) :=
  (independent_of_fixed groundRow_fixed).symm

/-- **Absence is not saved by privacy**: the spawn firing is admitted alone, the neighbour shares no
unknown with it, and it is refused beside the neighbour's ground row `7`. -/
theorem absence_refused_beside_ground :
    Independent action groundRow.Mentions (Footprint action emptyState spawnAt) ∧
      (step X ℕ E spawnProgram).Admits (s := emptyState) spawnAt ∧
      ¬ (step X ℕ E spawnProgram).Admits (s := beside groundRow emptyState) spawnAt := by
  refine ⟨ground_independent, spawnAt_admitted, fun admitted => ?_⟩
  obtain ⟨-, -, -, -, checks, -⟩ := (admits_iff (s := beside groundRow emptyState) spawnAt).mp admitted
  have known : spawnAt.information X (beside groundRow emptyState) = [] := rfl
  have solved : X.Models (a := PUnit.unit) (b := PUnit.unit) (Subst.id atoms)
      (spawnAt.information X (beside groundRow emptyState)) := by
    rw [known]
    exact fun e member => by cases member
  have label : (beside groundRow emptyState).label 0 = c 7 := beside_label_left (Finset.mem_singleton_self 0)
  have holds := checks (.predicate .none (c 7)) (List.mem_singleton_self _) PUnit.unit _ solved
  apply holds 0 (Finset.mem_union_left _ (Finset.mem_singleton_self 0))
  show (c 7 : Term atoms) = Subst.applyTerm (Subst.id atoms)
    (Subst.applyTerm (Subst.id atoms) ((beside groundRow emptyState).label 0))
  rw [label]
  rfl

/-- Make `8`, claiming that no row `7` is present (a collect query with the empty claim). -/
def collectRule : Rule Tm := ⟨PUnit.unit, ⟨[], [], [], [], [c 8]⟩, [c 7]⟩

/-- The program of that one rule. -/
def collectProgram : Program Tm := {collectRule}

/-- The collect query firing, making identity `1`, seeing no row. -/
def collectAt : Firing ℕ E collectProgram PUnit.unit :=
  ⟨collectRule, rfl, PUnit.unit, Subst.id atoms, ⟨[], [], [1]⟩, [∅]⟩

theorem collectAt_admitted : (step X ℕ E collectProgram).Admits (s := emptyState) collectAt := by
  refine (admits_iff collectAt).mpr ⟨?_, ⟨List.nodup_nil, List.nodup_singleton 1, rfl, rfl, rfl, rfl⟩,
    ?_, ⟨PUnit.unit, Subst.id atoms, fun e member => by cases member⟩, ?_, ?_⟩
  · apply fresh_of_ground action emptyState collectAt
    intro t member σ
    simp only [collectAt, collectRule, Rule.terms, List.map_nil, List.flatMap_nil, List.nil_append,
      List.append_nil, List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [collectAt, emptyState, Selection.commit]
  · intro check member
    simp [collectAt, collectRule, Firing.opened, RuleInstance.map] at member
  · intro q member b σ _
    simp only [collectAt, collectRule, Firing.collectOpened, List.map_cons, List.map_nil, List.zip_cons_cons,
      List.zip_nil_right, List.mem_singleton] at member
    subst member
    ext o
    rw [mem_matchesAt]
    simp [emptyState]

/-- **A collect query is not saved by privacy either**: the collect query firing claiming no row `7` is admitted
alone, shares no unknown with the ground neighbour, and is refused beside the row `7`. -/
theorem collect_refused_beside_ground :
    Independent action groundRow.Mentions (Footprint action emptyState collectAt) ∧
      (step X ℕ E collectProgram).Admits (s := emptyState) collectAt ∧
      ¬ (step X ℕ E collectProgram).Admits (s := beside groundRow emptyState) collectAt := by
  refine ⟨(independent_of_fixed groundRow_fixed).symm, collectAt_admitted, fun admitted => ?_⟩
  obtain ⟨-, -, -, -, -, collect⟩ := (admits_iff (s := beside groundRow emptyState) collectAt).mp admitted
  have known : collectAt.information X (beside groundRow emptyState) = [] := rfl
  have solved : X.Models (a := PUnit.unit) (b := PUnit.unit) (Subst.id atoms)
      (collectAt.information X (beside groundRow emptyState)) := by
    rw [known]
    exact fun e member => by cases member
  have seen := collect (c 7, ∅) List.mem_cons_self PUnit.unit _ solved
  have label : (beside groundRow emptyState).label 0 = c 7 := beside_label_left (Finset.mem_singleton_self 0)
  have inside : (0 : ℕ) ∈ matchesAt X (a := PUnit.unit) (b := PUnit.unit) (Subst.id atoms)
      (collectAt.row X (beside groundRow emptyState)) (beside groundRow emptyState).present (c 7) := by
    rw [mem_matchesAt]
    refine ⟨Finset.mem_union_left _ (Finset.mem_singleton_self 0), ?_⟩
    show (c 7 : Term atoms) = Subst.applyTerm (Subst.id atoms)
      (Subst.applyTerm (Subst.id atoms) ((beside groundRow emptyState).label 0))
    rw [label]
    rfl
  rw [seen] at inside
  exact Finset.notMem_empty 0 inside

/-! ## The neighbour must be solvable -/

/-- Private but contradictory knowledge: `x₅ = 0` and `x₅ = 1`. -/
def unsolvableNeighbour : State Tm ℕ := ⟨PUnit.unit, [(.var 5, c 0), (.var 5, c 1)], ∅, fun _ => c 0⟩

theorem unsolvableNeighbour_unknowns {v : ℕ} (inside : UnknownsOf unsolvableNeighbour.Mentions v) :
    v = 5 := by
  obtain ⟨t, mentioned, member⟩ := inside
  rcases mentioned with first | second | ⟨o, present, -⟩
  · simp only [unsolvableNeighbour, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false, or_self] at first
    subst first
    exact freeVars_var 5 member
  · simp only [unsolvableNeighbour, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at second
    rcases second with rfl | rfl
    · exact (freeVars_const 0 member).elim
    · exact (freeVars_const 1 member).elim
  · simp [unsolvableNeighbour] at present

/-- **An unsolvable neighbour refuses**, although it shares no unknown with the footprint. -/
theorem unsolvable_refuses :
    Independent action unsolvableNeighbour.Mentions (Footprint action request tellAt) ∧
      ¬ action.Consistent unsolvableNeighbour.knowledge ∧
      ¬ (step X ℕ E tellProgram).Admits (s := beside unsolvableNeighbour request) tellAt := by
  have inconsistent : ¬ action.Consistent unsolvableNeighbour.knowledge := by
    rintro ⟨σ, solved⟩
    have zero : σ 5 = c 0 := solved (.var 5, c 0) List.mem_cons_self
    have one : σ 5 = c 1 := solved (.var 5, c 1) (List.mem_cons_of_mem _ List.mem_cons_self)
    exact absurd (Term.const.inj (zero.symm.trans one)) (by decide)
  refine ⟨?_, inconsistent, fun admitted => ?_⟩
  · apply independent_of_disjoint
    intro v inD inFoot
    have five := unsolvableNeighbour_unknowns inD
    rcases footprint_unknowns inFoot with zero | one <;> omega
  · obtain ⟨-, -, -, ⟨_, σ, solved⟩, -, -⟩ :=
      (admits_iff (s := beside unsolvableNeighbour request) tellAt).mp admitted
    have known := information_beside action (D := unsolvableNeighbour) (C := request) tellAt
      (Finset.disjoint_empty_left _) (by
      rintro o (inside | inside)
      · simp [tellAt] at inside
      · simp only [tellAt, List.mem_singleton] at inside
        subst inside
        exact Finset.mem_singleton_self 0)
    rw [known] at solved
    exact inconsistent ⟨σ, ((Interface.Frames.models_append _ _ _).mp solved).1⟩

/-! ## The firing's own unknowns are in its footprint -/

/-- A neighbour whose knowledge only mentions the opened unknown `x₁`, and constrains nothing. -/
def mentionsOpened : State Tm ℕ := ⟨PUnit.unit, [(.var 1, .var 1)], ∅, fun _ => c 0⟩

theorem mentionsOpened_unknowns {v : ℕ} (inside : UnknownsOf mentionsOpened.Mentions v) : v = 1 := by
  obtain ⟨t, mentioned, member⟩ := inside
  rcases mentioned with first | second | ⟨o, present, -⟩
  · simp only [mentionsOpened, List.map_cons, List.map_nil, List.mem_singleton] at first
    subst first
    exact freeVars_var 1 member
  · simp only [mentionsOpened, List.map_cons, List.map_nil, List.mem_singleton] at second
    subst second
    exact freeVars_var 1 member
  · simp [mentionsOpened] at present

/-- **A joint solution exists.** -/
theorem opened_joint :
    ∃ σ : Subst atoms, action.Models σ (tellAt.information X request) ∧
      action.Models σ mentionsOpened.knowledge := by
  refine ⟨everywhere 5, ?_, fun e member => ?_⟩
  · rw [tellAt_information]
    intro e member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl
  · simp only [mentionsOpened, List.mem_singleton] at member
    subst member
    rfl

/-- **The opening is not fresh beside it**: the neighbour mentions the unknown the rule is opened
as. -/
theorem opened_not_fresh : ¬ tellAt.Fresh X (beside mentionsOpened request) := by
  intro fresh
  obtain ⟨u, onState, onRule⟩ := fresh PUnit.unit (everywhere 0) (everywhere 1)
  have mentioned : (beside mentionsOpened request).Mentions (.var 1) :=
    Or.inl (by simp [beside, mentionsOpened])
  have seen : u 1 = c 0 := onState (.var 1) mentioned
  have opened : u 1 = c 1 := onRule x (by simp [tellAt, tellRule, Rule.terms])
  exact absurd (Term.const.inj (seen.symm.trans opened)) (by decide)

/-- **Refused beside it, and admitted when opened apart**: the sharing is removed by renaming the
opening. -/
theorem reopened_admitted :
    ¬ (step X ℕ E tellProgram).Admits (s := beside mentionsOpened request) tellAt ∧
      (step X ℕ E tellProgram).Admits (s := beside mentionsOpened request) tellAtTwo := by
  refine ⟨fun admitted => opened_not_fresh ((admits_iff (s := beside mentionsOpened request) tellAt).mp
    admitted).1, ?_⟩
  refine admits_beside action tellRule_positive tellAtTwo_admitted (Finset.disjoint_empty_left _)
    (by simp [mentionsOpened]) ⟨everywhere 0, fun e member => by
      simp only [mentionsOpened, List.mem_singleton] at member
      subst member
      rfl⟩ ?_
  apply independent_of_disjoint
  intro v inD inFoot
  have one := mentionsOpened_unknowns inD
  rcases footprintTwo_unknowns inFoot with zero | two <;> omega

#print axioms tellAt_admitted
#print axioms request_succeeds
#print axioms shared_composable
#print axioms shared_not_independent
#print axioms shared_no_joint
#print axioms nothing_admitted_beside
#print axioms shared_success_unreachable
#print axioms private_independent
#print axioms private_admitted
#print axioms private_succeeds
#print axioms ground_independent
#print axioms absence_refused_beside_ground
#print axioms collect_refused_beside_ground
#print axioms unsolvable_refuses
#print axioms opened_joint
#print axioms opened_not_fresh
#print axioms reopened_admitted

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope.CompositionControls
