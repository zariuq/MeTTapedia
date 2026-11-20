import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.Neighbours

/-!
# Composition of hosted programs: the controls

Each control fails one condition of `Composition.Neighbours` and nothing else. `P0` has no equation,
`Q` has `(= (g) d)`, the query is the call `(g)`; the source of `P0` answers `(g)` (`p0_answers_g`,
`p0_only_g`) and the source of `Q` answers `d` (`only_d`).

* **Rules without rows** (the rows of `Systems.hosted_union` are needed). The rules of `P0 ∪ Q`, run
  from the rows of `P0`, reach a finished state that answers `(g)` (`mixed_answers_g`); every
  configuration a source run of `P0 ∪ Q` reaches answers only `d` (`union_answers_only_d`).
* **Knowledge** (condition 1). With knowledge that has no solution no firing of any program is
  admitted (`no_firing_of_unsolvable`); the start of `P0`'s query with the equation `a ≐ b` between two
  symbols added to its knowledge has no firing (`knowledge_switches_off`), no other row, no other rule.
  A solution does not keep the query: the start of the query `ret $x` with `$x ≐ c` added to its
  knowledge, which has a solution (`constrained_solvable`), answers `{c}` (`knowledge_changes_answer`),
  where the source answers every closed term (`source_answers_all`, `c_ne_all`); that state represents
  the query `ret c`, and `{c}` is the source's answer of that instance
  (`Composition.Knowledge.constrained_is_instance`, `Composition.Knowledge.constrained_answers`). The
  control of the clause on equation rows is `Composition.Knowledge.RowName.extra_answer`.
* **An equation row that matches** (condition 2). The start of `P0`'s query with one more row
  `eqn((g))` (`one_more_row`) has no firing of `P0`'s translation (`neighbour_stuck`). What decides is
  matching, not the head of the row: beside the row `eqn((g a))`, which has the call's head and does
  not match the call `(g)`, the call still has its firing (`same_head_fires`); beside the row `eqn($x)`
  with `$x` the row's private name, which has no head and matches every call, it has none
  (`variable_row_stuck`). And the condition is
  asked only of unmatched calls: `Q` and the query have no reachable unmatched call (`matched_Q`), and
  beside the row `eqn((g))`, which matches its call (`rowG_matches`), the answers the translated program
  of `Q` shows are still the source's (`matching_row_harmless`).
* **A row that reads as an alternative's row** (condition 3). The start of `P0`'s query with one more
  row, the alternative's row of the query `ret d` (`twoAlternatives`), represents the query's
  alternative beside that row (`twoAlternatives_beside`); the row reads as an alternative's row
  (`row_reads_alternative`); the translated program fires on it and reaches a finished row that answers
  `d` (`alternative_row_answers`), which no configuration of the source of `P0` answers (`p0_only_g`).
  The forward direction is not disturbed: it is used here, on the other row, to make that run.
* **A rule that takes a hosted row** (condition 4). At the start of `Q`'s query the rule `takeEqn`
  takes the equation row (`takeEqn_fires`, `takeEqn_not_apart`); in the state it makes, the translated
  program's rule for the unmatched call fires and reaches a finished row that answers `(g)`
  (`rule_takes_row`), which no configuration of the source of `Q` answers (`only_d`). **Reading is not
  taking**: the rule `readEqn` reads the same row (`readEqn_fires`), that one firing is apart from the
  hosted rows (`read_apart`), and after it the answers the translated program shows are, as a set, the
  source's (`reading_keeps`). The rule's firings are not apart at every state
  (`Composition.Readers.Flex.readEqn_not_disciplined`). And reading is not enough either way: the rule `pinRule` reads the
  alternative's row of the query `ret $x`, takes no row (`pin_fires`, `pin_takes_none`), and tells
  `$x ≐ c`; its firing adds knowledge of the hosted row (`pin_not_apart`), and after it the translated
  program answers `{c}` where the source answers every closed term (`pin_changes_answer`,
  `source_answers_all`).

Control rows are data of the source's own signature: `eqn_node_is_data`, `alt_node_is_data`. Nothing
but the conditions above keeps a neighbour's data from being read as control.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.Controls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage SourceLanguage.Elaboration SourceLanguage.Toolkit
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open Classical

/-- The trivial discipline, with its type language on the nose. -/
abbrev D : Discipline MSig [] () := ⟨MTy, fun _ _ => True⟩
abbrev N := mettaNodes

def supply : ℕ → MClosed := fun _ => csym "space"
abbrev sp : MClosed → Multiset (Row mkeys [] ()) := fun _ => 0

def gT : MData := tuple [sym "g"]
def dT : MData := sym "d"
def gC : MClosed := ctuple [csym "g"]
def dC : MClosed := csym "d"

/-- The query `(g)`, called. -/
def q : Comp mkeys [] () MTy := .apply gT

/-- No equations. -/
def P0 : SourceLanguage.Program mkeys [] () MTy := ⟨[], fun t => .apply t⟩

/-- `(= (g) d)`. -/
def eg : SourceLanguage.Equation mkeys [] () MTy := ⟨[300], gT, .ret dT⟩
def Q : SourceLanguage.Program mkeys [] () MTy := ⟨[eg], fun t => .apply t⟩

/-- A program whose one equation has the left side `lhs`: its start is `P0`'s with the row `eqn(lhs)`. -/
def rowProgram (lhs : MData) : SourceLanguage.Program mkeys [] () MTy := ⟨[⟨[301], lhs, .fail⟩], fun t => .apply t⟩

theorem q_unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = [] := by
  intro t member x inside
  simp only [q, Comp.data, List.mem_singleton] at member
  subst member
  simp [gT, tuple, tupleArgs, sym, support, supportArgs] at inside

/-! ## Firings do not depend on the program beyond their rule -/

theorem fires_mono {P P' : SourceLanguage.Program mkeys [] () MTy} (sub : translate N P ⊆ translate N P')
    {s s' : HostState MSig} (fires : Fires N P s s') : Fires N P' s s' := by
  obtain ⟨⟨rule, member, ext, opening, selection, seen⟩, admitted, result⟩ := fires
  exact ⟨⟨rule, sub member, ext, opening, selection, seen⟩, admitted, result⟩

theorem sub_of_no_equations (P : SourceLanguage.Program mkeys [] () MTy) : translate N P0 ⊆ translate N P := by
  intro r member
  rcases (mem_translate N).mp member with control | ⟨e, eMember, _⟩
  · exact (mem_translate N).mpr (.inl control)
  · cases eMember

/-! ## The source of `P0` answers `(g)`, and only `(g)` -/

abbrev W0 : World mkeys [] () := ⟨0, 0, sp⟩

abbrev B0 : Branch mkeys [] () MTy := ⟨[], .eval (.apply gT), [], []⟩
abbrev Bv : Branch mkeys [] () MTy := ⟨[], .value gT, [], []⟩

def final0 : Config mkeys [] () MTy := ⟨W0, {Bv}⟩

theorem determines_g : Determines ([] : List (Constraint mkeys [] ())) gT gC :=
  ⟨live_nil, fun _ _ _ => rfl⟩

theorem determines_d0 : Determines ([] : List (Constraint mkeys [] ())) dT dC :=
  ⟨live_nil, fun _ _ _ => rfl⟩

theorem p0_answers_g :
    Runs D P0 supply (Config.initial sp q) final0 ∧ Config.answers (D := D) final0 = {{gC}} := by
  refine ⟨Relation.ReflTransGen.single (step_one live_nil (.unmatched W0 [] gT [] [] ?_)), ?_⟩
  · intro e member
    cases member
  · show Config.answers (D := D) ⟨W0, {⟨[], .value gT, [], []⟩}⟩ = _
    rw [answers_singleton (D := D) ⟨rfl, _, rfl⟩ live_nil, answer_of_determines rfl determines_g]

def Inv0 (C : Config mkeys [] () MTy) : Prop := ∀ b ∈ C.branches, b = B0 ∨ b = Bv

theorem move_B0_none {w w' : World mkeys [] ()} {b : Branch mkeys [] () D.Ty}
    {bs : Multiset (Branch mkeys [] () D.Ty)} (move : Move D P0 supply w b w' bs) (hb : b = B0) :
    ∀ b' ∈ bs, b' = Bv := by
  cases move <;> cases hb
  · rename_i matched
    obtain ⟨e, eMember, _⟩ := matched
    cases eMember
  · intro b' made
    exact Multiset.mem_singleton.mp made

theorem inv0_runs {C : Config mkeys [] () MTy} (runs : Runs D P0 supply (Config.initial sp q) C) : Inv0 C := by
  induction runs with
  | refl =>
      intro b member
      exact .inl (Multiset.mem_singleton.mp member)
  | tail _ step ih =>
      obtain ⟨w, w', b, rest, bs, _, move⟩ := step
      have bShape := ih b (Multiset.mem_cons_self _ _)
      intro b' member
      rcases Multiset.mem_add.mp member with made | kept
      · rcases bShape with hb | hb
        · exact .inr (move_B0_none move hb b' made)
        · subst hb
          exact absurd move Move.value_still
      · exact ih b' (Multiset.mem_cons_of_mem kept)

/-- **The source of `P0` answers only `(g)`**: every answer of every configuration a run reaches. -/
theorem p0_only_g {C : Config mkeys [] () MTy} (runs : Runs D P0 supply (Config.initial sp q) C) :
    ∀ A ∈ Config.answers (D := D) C, A = {gC} := by
  have inv := inv0_runs runs
  intro A member
  unfold Config.answers at member
  obtain ⟨b, inside, rfl⟩ := Multiset.mem_map.mp member
  obtain ⟨bMember, finished, _⟩ := Multiset.mem_filter.mp inside
  rcases inv b bMember with rfl | rfl
  · obtain ⟨_, t, focus⟩ := finished
    cases focus
  · exact answer_of_determines rfl determines_g

theorem gC_ne_dC : gC ≠ dC := by
  intro same
  simp [gC, dC, ctuple, csym] at same

theorem g_ne_d : ({gC} : Set MClosed) ≠ {dC} :=
  fun same => gC_ne_dC (Set.singleton_eq_singleton_iff.mp same)

/-! ## Rules without rows: the rules of `P0 ∪ Q` from the rows of `P0` -/

theorem sub_union : translate N P0 ⊆ translate N (P0.union Q) := by
  rw [translate_union]
  exact Set.subset_union_left

/-- **Rules without rows**: the rules of `P0 ∪ Q`, from the start of `P0`, reach in one firing a
finished state whose answer is `{(g)}`. -/
theorem mixed_answers_g :
    ∃ s a, Fires N (P0.union Q) (Hosting.start N P0 q) s ∧ StateFinished N s a ∧ stateAnswer N s a = {gC} := by
  have rep := start_represents N P0 q q_unopened
  have plainP : PlainProgram P0 := fun _ member => by cases member
  have plain : PlainBranch (initialBranch (Ty := MTy) q) := ⟨rfl, .inl ⟨q, rfl, trivial⟩⟩
  have move : Move D P0 supply W0 (initialBranch q) W0 {⟨[], .value gT, [], []⟩} :=
    .unmatched W0 [] gT [] [] (fun _ member => by cases member)
  obtain ⟨s, a, fires, rep', _⟩ := simulation N (D := D) plainP move rep plain
    (Multiset.mem_singleton_self _) live_nil
  have finished : Branch.Finished (D := D) (⟨[], .value gT, [], []⟩ : Branch mkeys [] () MTy) := ⟨rfl, _, rfl⟩
  refine ⟨s, a, fires_mono sub_union fires, (finished_iff N (D := D) rep').mp ⟨finished, live_nil⟩, ?_⟩
  rw [answer_eq N (D := D) rep' finished, answer_of_determines rfl determines_g]

abbrev B1 : Branch mkeys [] () MTy := ⟨[(gT, gT)], .eval (.ret dT), [], []⟩
abbrev B2 : Branch mkeys [] () MTy := ⟨[(gT, gT)], .value dT, [], []⟩

def Inv (C : Config mkeys [] () MTy) : Prop := ∀ b ∈ C.branches, b = B0 ∨ b = B1 ∨ b = B2

theorem callBranch_g (n : ℕ) : callBranch D n [] gT [] [] eg = B1 := rfl

theorem live_gg : Solvable ([(gT, gT)] : List (Constraint mkeys [] ())) :=
  ⟨Empty, noNames, closeNames [] (csym "a"), fun e member => by
    simp only [List.mem_singleton] at member
    subst member
    rfl⟩

theorem move_B0 {P : SourceLanguage.Program mkeys [] () D.Ty} (hP : P.equations = [eg])
    {w w' : World mkeys [] ()} {b : Branch mkeys [] () D.Ty} {bs : Multiset (Branch mkeys [] () D.Ty)}
    (move : Move D P supply w b w' bs) (hb : b = B0) : ∀ b' ∈ bs, b' = B1 := by
  cases move <;> cases hb
  · intro b' made
    rw [hP] at made
    simp only [List.map_cons, List.map_nil, Multiset.coe_singleton, Multiset.mem_singleton] at made
    rw [made, callBranch_g]
  · rename_i none
    exact absurd (show Solvable ([] ++ [(instantiate (copyAt mkeys w.scope) eg.lhs, gT)]) from live_gg)
      (none eg (by rw [hP]; exact List.mem_singleton_self _))

theorem move_B1 {P : SourceLanguage.Program mkeys [] () D.Ty}
    {w w' : World mkeys [] ()} {b : Branch mkeys [] () D.Ty} {bs : Multiset (Branch mkeys [] () D.Ty)}
    (move : Move D P supply w b w' bs) (hb : b = B1) : ∀ b' ∈ bs, b' = B2 := by
  cases move <;> cases hb
  intro b' made
  exact Multiset.mem_singleton.mp made

theorem inv_runs {P : SourceLanguage.Program mkeys [] () D.Ty} (hP : P.equations = [eg])
    {C : Config mkeys [] () MTy} (runs : Runs D P supply (Config.initial sp q) C) : Inv C := by
  induction runs with
  | refl =>
      intro b member
      exact .inl (Multiset.mem_singleton.mp member)
  | tail _ step ih =>
      obtain ⟨w, w', b, rest, bs, _, move⟩ := step
      have bShape := ih b (Multiset.mem_cons_self _ _)
      intro b' member
      rcases Multiset.mem_add.mp member with made | kept
      · rcases bShape with hb | hb | hb
        · exact .inr (.inl (move_B0 hP move hb b' made))
        · exact .inr (.inr (move_B1 move hb b' made))
        · subst hb
          exact absurd move Move.value_still
      · exact ih b' (Multiset.mem_cons_of_mem kept)

theorem determines_d : Determines ([(gT, gT)] : List (Constraint mkeys [] ())) dT dC :=
  ⟨live_gg, fun _ _ _ => rfl⟩

/-- **A program whose one equation is `(= (g) d)` never answers `(g)`**: every answer of every
configuration a run reaches is `{d}`. -/
theorem only_d {P : SourceLanguage.Program mkeys [] () D.Ty} (hP : P.equations = [eg])
    {C : Config mkeys [] () MTy} (runs : Runs D P supply (Config.initial sp q) C) :
    ∀ A ∈ Config.answers (D := D) C, A = {dC} := by
  have inv := inv_runs hP runs
  intro A member
  unfold Config.answers at member
  obtain ⟨b, inside, rfl⟩ := Multiset.mem_map.mp member
  obtain ⟨bMember, finished, _⟩ := Multiset.mem_filter.mp inside
  rcases inv b bMember with rfl | rfl | rfl
  · obtain ⟨_, t, focus⟩ := finished
    cases focus
  · obtain ⟨_, t, focus⟩ := finished
    cases focus
  · exact answer_of_determines rfl determines_d

/-- **The source of `P0 ∪ Q` never answers `(g)`.** -/
theorem union_answers_only_d {C : Config mkeys [] () MTy}
    (runs : Runs D (P0.union Q) supply (Config.initial sp q) C) : ∀ A ∈ Config.answers (D := D) C, A = {dC} :=
  only_d rfl runs

/-! ## Knowledge that has no solution -/

/-- **With knowledge that has no solution, no firing of any program is admitted.** -/
theorem no_firing_of_unsolvable {S : Signature} {Prog : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)}
    {s : HostState S} (dead : ¬ (Interface.Frames.contextual S).Solvable s.knowledge)
    (f : RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S) Prog s.frame) :
    ¬ f.Admits (Interface.Frames.contextual S) s := by
  rintro ⟨_, _, ⟨B, u, solved⟩, _⟩
  exact dead ⟨_, _, RuleSyntax.Firing.knowledge_solved (X := Interface.Frames.contextual S) f solved⟩

/-- The start of `P0`'s query with the equation `a ≐ b` between two symbols added to its knowledge. -/
def contradicted : HostState MSig :=
  ⟨startFrame mkeys,
    [(observe (symAt "a" : Term (signature MSig (startArity mkeys)) [] ()),
      observe (symAt "b" : Term (signature MSig (startArity mkeys)) [] ()))],
    (Hosting.start N P0 q).present, (Hosting.start N P0 q).label⟩

theorem contradicted_unsolvable : ¬ (Interface.Frames.contextual MSig).Solvable contradicted.knowledge := by
  rintro ⟨B, σ, solved⟩
  have same : observe (instantiate σ (symAt "a" : Term (signature MSig (startArity mkeys)) [] ())) =
      observe (instantiate σ (symAt "b" : Term (signature MSig (startArity mkeys)) [] ())) :=
    solved _ (List.mem_singleton_self _)
  have terms := observe_injective same
  change (Term.op (Sum.inl (MOp.sym "a")) .nil : Term (signature MSig B.arity) [] ()) =
    Term.op (Sum.inl (MOp.sym "b")) .nil at terms
  simp at terms

/-- **Knowledge that has no solution switches the hosted program off**: the rows and labels are those
of `P0`'s start, there is no other row and no other rule, and no firing is admitted; the source
answers `(g)` (`p0_answers_g`). -/
theorem knowledge_switches_off (s' : HostState MSig) : ¬ Fires N P0 contradicted s' := by
  rintro ⟨f, admitted, _⟩
  exact no_firing_of_unsolvable contradicted_unsolvable f admitted

/-! ## Knowledge that has a solution and says more of a hosted name -/

/-- The query `$x`, returned: the name is the query's own, unopened. -/
def qx : Comp mkeys [] () MTy := .ret xName

def cT : MData := sym "c"
def cC : MClosed := csym "c"

theorem qx_unopened : ∀ t ∈ qx.data, ∀ x ∈ support t, x.scopes = [] := by decide

/-- The start of the query `ret $x` with the equation `$x ≐ c` added to its knowledge. -/
def constrained : HostState MSig :=
  ⟨startFrame mkeys, [(observe (instantiate queryNames xName), observe (instantiate queryNames cT))],
    (Hosting.start N P0 qx).present, (Hosting.start N P0 qx).label⟩

/-- The alternative whose store has `$x ≐ c`. -/
abbrev Bx : Branch mkeys [] () MTy := ⟨[(xName, cT)], .eval (.ret xName), [], []⟩

theorem live_xc : Solvable ([(xName, cT)] : List (Constraint mkeys [] ())) :=
  ⟨Empty, noNames, closeNames [(([], [7], 0), cC)] (csym "a"), fun e member => by
    simp only [List.mem_singleton] at member
    subst member
    rfl⟩

theorem determines_xc : Determines ([(xName, cT)] : List (Constraint mkeys [] ())) xName cC :=
  ⟨live_xc, fun _ _ solved => (solved _ (List.mem_singleton_self _)).trans rfl⟩

/-- **The knowledge has a solution**: it is jointly solvable with everything the start knows. -/
theorem constrained_solvable : (Interface.Frames.contextual MSig).Solvable constrained.knowledge :=
  ⟨⟨Empty, noNames⟩, startFill (closeNames [(([], [7], 0), cC)] (csym "a")), fun e member => by
    rw [List.mem_singleton.mp member]
    rfl⟩

/-- The state represents the alternative whose store has the equation: not the query's alternative. -/
theorem constrained_represents : Represents N P0 0 Bx constrained 0 := by
  have read : ∀ {B : Interface.Frames.Frame MSig} (σ : Assignment (startArity mkeys) B.arity) (t : MData),
      instantiate σ (instantiate queryNames t) = instantiate (fun x => σ (.inl x)) t := by
    intro B σ t
    rw [instantiate_comp]
    apply congrArg (fun ρ => instantiate ρ t)
    funext x
    exact instantiate_generator σ (.inl x)
  have readAlt : ∀ {B : Interface.Frames.Frame MSig} (σ : Assignment (startArity mkeys) B.arity),
      instantiateObservation σ (constrained.label 0) =
        observe (encAlt N (instantiate (fun x => σ (.inl x))) (.eval qx) []) := by
    intro B σ
    show observe (instantiate σ (encAlt N (instantiate queryNames) (.eval qx) [])) = _
    rw [instantiate_encAlt]
    apply congrArg observe
    apply congrArg (fun g => encAlt N g (.eval qx) [])
    funext t
    exact read σ t
  have known_iff : ∀ {B : Interface.Frames.Frame MSig} (σ : Assignment (startArity mkeys) B.arity),
      (Interface.Frames.contextual MSig).Models σ constrained.knowledge ↔
        Models (fun x => σ (.inl x)) [(xName, cT)] := by
    intro B σ
    constructor
    · intro solved e member
      rw [List.mem_singleton.mp member]
      have same : observe (instantiate σ (instantiate queryNames xName)) =
          observe (instantiate σ (instantiate queryNames cT)) := solved _ (List.mem_singleton_self _)
      have terms := observe_injective same
      rw [read, read] at terms
      exact terms
    · intro solved e member
      rw [List.mem_singleton.mp member]
      show observe (instantiate σ (instantiate queryNames xName)) =
        observe (instantiate σ (instantiate queryNames cT))
      rw [read, read]
      exact congrArg observe (solved _ (List.mem_singleton_self _))
  refine ⟨le_refl _, rfl, ?_, ?_, ?_, ?_, rfl⟩
  · intro B r
    constructor
    · rintro ⟨σ, known, rfl⟩
      exact ⟨fun x => σ (.inl x), (known_iff σ).mp known, (readAlt σ).symm⟩
    · rintro ⟨σ, solved, rfl⟩
      refine ⟨startFill σ, (known_iff (startFill σ)).mpr solved, ?_⟩
      rw [readAlt]
      rfl
  · intro B σ _ i hi
    exact absurd hi (Nat.not_lt_zero i)
  · intro B σ _ i hi
    exact absurd hi (Nat.not_lt_zero i)
  · refine ⟨?_, ?_, ?_⟩
    · intro e member
      rw [List.mem_singleton.mp member]
      exact ⟨dependsBelow_of_unopened 0 (by decide), dependsBelow_of_unopened 0 (by decide)⟩
    · intro t member
      exact dependsBelow_of_unopened 0 (qx_unopened t member)
    · intro fr member
      cases member

/-- **Knowledge that has a solution and says more of a hosted name changes the answer**: the rows and
labels are those of the start of the query `ret $x`, there is no other row and no other rule, the
knowledge `$x ≐ c` has a solution, and the translated program reaches a finished state whose answer is
`{c}`; the source's answer to the query is every closed term (`source_answers_all`). Joint solvability
of the knowledge does not keep the query: `{c}` is the source's answer of its instance `ret c`
(`Composition.Knowledge.constrained_answers`). -/
theorem knowledge_changes_answer :
    ∃ s a, Fires N P0 constrained s ∧ StateFinished N s a ∧ stateAnswer N s a = {cC} := by
  have plainP : PlainProgram P0 := fun _ member => by cases member
  have move : Move D P0 supply W0 Bx W0 {⟨[(xName, cT)], .value xName, [], []⟩} :=
    .ret W0 [(xName, cT)] xName [] []
  obtain ⟨s, a, fires, rep', _⟩ := simulation N (D := D) plainP move constrained_represents
    ⟨rfl, .inl ⟨_, rfl, trivial⟩⟩ (Multiset.mem_singleton_self _) live_xc
  have finished : Branch.Finished (D := D)
      (⟨[(xName, cT)], .value xName, [], []⟩ : Branch mkeys [] () MTy) := ⟨rfl, _, rfl⟩
  refine ⟨s, a, fires, (finished_iff N (D := D) rep').mp ⟨finished, live_xc⟩, ?_⟩
  rw [answer_eq N (D := D) rep' finished, answer_of_determines rfl determines_xc]

/-- **The source's answer to the query `ret $x` is every closed term.** -/
theorem source_answers_all :
    Runs D P0 supply (Config.initial sp qx) ⟨W0, {⟨[], .value xName, [], []⟩}⟩ ∧
      Config.answers (D := D) (⟨W0, {⟨[], .value xName, [], []⟩}⟩ : Config mkeys [] () MTy) = {Set.univ} := by
  refine ⟨Relation.ReflTransGen.single (step_one live_nil (.ret W0 [] xName [] [])), ?_⟩
  rw [answers_singleton (D := D) ⟨rfl, _, rfl⟩ live_nil]
  congr 1
  ext g
  simp only [Set.mem_univ, iff_true]
  have solved : Models (closeNames [(([], [7], 0), g)] (csym "a"))
      ([] : List (Constraint mkeys [] ())) := by
    intro e member
    cases member
  refine ⟨xName, rfl, Empty, noNames, closeNames [(([], [7], 0), g)] (csym "a"), solved, ?_⟩
  show instantiate _ (foD [] [7] 0) = _
  rw [instantiate_foD]
  rfl

theorem c_ne_all : ({cC} : Set MClosed) ≠ Set.univ := by
  intro same
  have inside : dC ∈ ({cC} : Set MClosed) := same ▸ Set.mem_univ dC
  simp [cC, dC, csym] at inside

/-! ## An equation row that matches the call -/

/-- The start of the program with the one row `eqn(lhs)` is the start of `P0`'s query with one more
row, numbered first. -/
theorem one_more_row (lhs : MData) :
    (Hosting.start N (rowProgram lhs) q).frame = (Hosting.start N P0 q).frame ∧
    (Hosting.start N (rowProgram lhs) q).knowledge = [] ∧ (Hosting.start N P0 q).knowledge = [] ∧
    (Hosting.start N P0 q).present = {0} ∧ (Hosting.start N (rowProgram lhs) q).present = {1, 0} ∧
    (Hosting.start N (rowProgram lhs) q).label 1 = (Hosting.start N P0 q).label 0 ∧
    (Hosting.start N (rowProgram lhs) q).label 0 = observe (eqnN N (instantiate (rowNames 0) lhs)) := by
  refine ⟨rfl, rfl, rfl, by decide, ?_, rfl, rfl⟩
  show insert 1 (Finset.range 1) = ({1, 0} : Finset ℕ)
  decide

/-- **A row that matches the call switches the hosted program off**: from the start of `P0`'s query
with the row `eqn(lhs)` added, where a copy of `lhs` unifies with the call `(g)`, the translated
program of `P0` has no admitted firing at all. -/
theorem stuck_of_matching_row (lhs : MData)
    (matches' : Solvable ([] ++ [(instantiate (copyAt mkeys 0) lhs, gT)] : List (Constraint mkeys [] ())))
    (s' : HostState MSig) : ¬ Fires N P0 (Hosting.start N (rowProgram lhs) q) s' := by
  rintro ⟨⟨rule, member, ext, opening, selection, seen⟩, admitted, _⟩
  have rep := start_represents N (rowProgram lhs) q q_unopened
  have admitted' : RuleSyntax.Firing.Admits (Interface.Frames.contextual MSig) (Hosting.start N (rowProgram lhs) q)
      (⟨rule, sub_of_no_equations (rowProgram lhs) member, ext, opening, selection, seen⟩ :
        RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations MSig) (translate N (rowProgram lhs))
          (Hosting.start N (rowProgram lhs) q).frame) := admitted
  rcases (mem_translate N).mp member with control | ⟨e, eMember, _⟩
  · rcases (mem_controlRules N).mp control with rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨_, _, _, B, h, reads, _⟩ := admitted_takes_alternative N rep admitted' rfl rfl rfl
        (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
      obtain ⟨t, focus⟩ := shape_ret N reads
      cases focus
    · obtain ⟨a', simple, _, _, _, _, _⟩ := admitted_takes_alternative N rep admitted' rfl rfl rfl
        (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
      exact unmatched_none N rep simple admitted' _ (List.mem_singleton_self _) matches'
    · obtain ⟨_, _, _, B, h, reads, _⟩ := admitted_takes_alternative N rep admitted' rfl rfl rfl
        (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
      obtain ⟨c, d, focus⟩ := shape_choice N reads
      cases focus
    · obtain ⟨_, _, _, B, h, reads, _⟩ := admitted_takes_alternative N rep admitted' rfl rfl rfl
        (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
      obtain ⟨c, d, focus⟩ := shape_choice N reads
      cases focus
    · obtain ⟨_, _, _, B, h, reads, _⟩ := admitted_takes_alternative N rep admitted' rfl rfl rfl
        (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
      obtain ⟨_, _, _, _, focus⟩ := shape_bindStart N reads
      cases focus
    · obtain ⟨_, _, _, B, h, reads, _⟩ := admitted_takes_alternative N rep admitted' rfl rfl rfl
        (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
      obtain ⟨_, _, _, _, frames⟩ := shape_bindValue N reads
      cases frames
  · cases eMember

/-- **The row `eqn((g))` switches the call `(g)` off.** -/
theorem neighbour_stuck (s' : HostState MSig) : ¬ Fires N P0 (Hosting.start N (rowProgram gT) q) s' :=
  stuck_of_matching_row gT live_gg s'

/-- **The row `eqn($x)`, which has no head, switches the call off**: `$x` is the row's private name, so
the row matches every call. -/
theorem variable_row_stuck (s' : HostState MSig) : ¬ Fires N P0 (Hosting.start N (rowProgram xName) q) s' :=
  stuck_of_matching_row xName
    ⟨Empty, noNames, closeNames [(([0], [7], 0), gC)] (csym "a"), fun e member => by
      simp only [List.nil_append, List.mem_singleton] at member
      subst member
      rfl⟩ s'

/-- The datum `(g a)`: the head of the call `(g)`, and another length. -/
def gaT : MData := tuple [sym "g", sym "a"]

/-- A neighbour's equation row `eqn((g a))`. -/
def rowGa : Observation MSig (startArity mkeys) := observe (eqnN N (instantiate (rowNames 7) gaT))

/-- Two tuples of different lengths are never made equal, by any two assignments. -/
theorem tuple_length_ne' {X : Type} {target : X → MetaArity MSig} (σ σ' : Assignment (fam mkeys) target)
    {ts ts' : List MData} (different : ts.length ≠ ts'.length) :
    instantiate σ (tuple ts) ≠ instantiate σ' (tuple ts') := by
  intro same
  change (Term.op (Sum.inl (MOp.tup ts.length)) _ : Term (signature MSig target) [] ()) =
    Term.op (Sum.inl (MOp.tup ts'.length)) _ at same
  injection same with _ _ hop _
  simp at hop
  exact different hop

/-- **A row with the call's head that does not match the call does not switch it off**: beside the row
`eqn((g a))` the call `(g)` still has its firing. -/
theorem same_head_fires : ∃ w', Fires N P0 (startWith N P0 q rowGa) w' := by
  have beside := startWith_beside N (P := P0) q rowGa q_unopened
  have label : ∀ {B : Interface.Frames.Frame MSig} (σ : Assignment (startArity mkeys) B.arity),
      instantiateObservation σ ((startWith N P0 q rowGa).label (P0.equations.length + 1)) =
        observe (eqnN N (instantiate σ (instantiate (rowNames 7) gaT))) := by
    intro B σ
    show instantiateObservation σ (Function.update (startLabel N P0 q) (P0.equations.length + 1) rowGa
      (P0.equations.length + 1)) = _
    rw [Function.update_self]
    exact congrArg observe (instantiate_eqnN N σ _)
  refine (unmatched_beside_iff N beside ?_ (fun e member => by cases member) live_nil).mpr ?_
  · intro o inside B σ _ reads
    obtain ⟨x, y, same⟩ := reads
    rw [Finset.mem_singleton.mp inside, label σ] at same
    exact absurd (N.tag_eq (observe_injective same)) (by decide)
  · intro o inside B σ known x y readsA sameRow
    rw [Finset.mem_singleton.mp inside, label σ] at sameRow
    have rowIs := vec1_inj (N.args_eq (observe_injective sameRow))
    obtain ⟨t, σ', focus, _, onCall⟩ := shape_apply N ((beside.hosted.reads B _).mp ⟨σ, known, readsA⟩)
    simp only [initialBranch, q, Focus.eval.injEq, Comp.apply.injEq] at focus
    subst focus
    rw [instantiate_comp, ← onCall] at rowIs
    exact tuple_length_ne' _ σ' (by decide) rowIs

/-! ## A row that reads as an alternative's row -/

/-- The query `d`, returned. -/
def q₂ : Comp mkeys [] () MTy := .ret dT

theorem q₂_unopened : ∀ t ∈ q₂.data, ∀ x ∈ support t, x.scopes = [] := by
  intro t member x inside
  simp only [q₂, Comp.data, List.mem_singleton] at member
  subst member
  simp [dT, sym, support, supportArgs] at inside

/-- The alternative's row of the query `ret d`. -/
def altRow : Observation MSig (startArity mkeys) := startLabel N P0 q₂ 0

/-- The start of the query `(g)` with one more row: the alternative's row of the query `ret d`. -/
def twoAlternatives : HostState MSig := startWith N P0 q altRow

/-- The state represents the alternative of `(g)`, at row `0`, beside the other row. -/
theorem twoAlternatives_beside : Beside N P0 0 (initialBranch q) twoAlternatives 0 {1} :=
  startWith_beside N (P := P0) q altRow q_unopened

/-- The same state represents the alternative of `ret d`, at row `1`, beside the row of `(g)`. -/
theorem twoAlternatives_beside' : Beside N P0 0 (initialBranch q₂) twoAlternatives 1 {0} := by
  refine ⟨?_, by decide, by decide⟩
  have renamed := represents_rename N (start_represents N P0 q₂ q₂_unopened) (a' := 1) (Nat.zero_le 1)
  refine represents_relabel N renamed (Function.update (startLabel N P0 q) 1 altRow) ?_
  intro o inside
  have isOne : o = 1 := by simpa [P0] using inside
  subst isOne
  show Function.update (startLabel N P0 q) 1 altRow 1 =
    Function.update (Hosting.start N P0 q₂).label 1 ((Hosting.start N P0 q₂).label 0) 1
  rw [Function.update_self, Function.update_self]
  rfl

/-- **The other row reads as an alternative's row.** -/
theorem row_reads_alternative : ¬ NeverReads (IsAlternative N) twoAlternatives {1} := by
  intro quiet
  have solved : Models (closeNames [] (csym "a")) (initialBranch (Ty := MTy) q₂).store := by
    intro e member
    simp [initialBranch] at member
  have reads : branchReads N (initialBranch (Ty := MTy) q₂) ⟨Empty, noNames⟩
      (observe (encBranch N (instantiate (closeNames [] (csym "a"))) (initialBranch q₂))) :=
    ⟨closeNames [] (csym "a"), solved, rfl⟩
  obtain ⟨g, known, read⟩ := (twoAlternatives_beside'.hosted.reads _ _).mpr reads
  exact quiet 1 (Finset.mem_singleton_self 1) _ g known ⟨_, _, read⟩

/-- **The translated program fires on the other row and answers what the source never answers**: from
the state, one firing reaches a finished present row whose answer is `{d}`; every answer of the source
of `P0` on the query `(g)` is `{(g)}` (`p0_only_g`). -/
theorem alternative_row_answers :
    ∃ w a, Fires N P0 twoAlternatives w ∧ a ∈ w.present ∧ StateFinished N w a ∧ stateAnswer N w a = {dC} := by
  have arrow : ArrowBranch (initialBranch (Ty := MTy) q₂) := ⟨trivial, .inl ⟨q₂, rfl, trivial⟩⟩
  have move : Move D P0 supply W0 (initialBranch q₂) W0 {⟨[], .value dT, [], []⟩} := .ret W0 [] dT [] []
  obtain ⟨w, a, fires, beside, _, _⟩ :=
    simulation_beside N (D := D) (supply := supply) (fun _ member => by cases member) move
      twoAlternatives_beside' arrow (hygienic_of_plain ⟨rfl, .inl ⟨q₂, rfl, trivial⟩⟩)
      (fun t focus _ => by simp [initialBranch, q₂] at focus) (Multiset.mem_singleton_self _) live_nil
  have finished : Branch.Finished (D := D) (⟨[], .value dT, [], []⟩ : Branch mkeys [] () MTy) := ⟨rfl, _, rfl⟩
  refine ⟨w, a, fires, beside.row_present N,
    (finished_iff N (D := D) (s := restrict w (hostedRows P0 a)) beside.hosted).mp ⟨finished, live_nil⟩, ?_⟩
  rw [show stateAnswer N w a = stateAnswer N (restrict w (hostedRows P0 a)) a from rfl,
    answer_eq N (D := D) beside.hosted finished, answer_of_determines rfl determines_d0]

/-! ## A rule that takes a hosted row -/

/-- **A rule without checks fires wherever its take pattern matches a present row at a solution of the
knowledge**: its canonical firing is admitted, whatever other rows and rules there are. -/
theorem canonical_admits {S : Signature} {Prog : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)}
    {s : HostState S} {r : RuleSyntax.Rule (RuleSyntax.Contextual.Terms S)} (member : r ∈ Prog)
    {pat out : Observation S r.locals.arity} (htake : r.body.take = [pat]) (hread : r.body.read = [])
    (hprod : r.body.produce = [out]) (hchecks : r.body.checks = []) (hcollect : r.collect = []) {a : ℕ}
    (present : a ∈ s.present) {B : Interface.Frames.Frame S} (g : Assignment s.frame.arity B.arity)
    (h : Assignment r.locals.arity B.arity) (known : (Interface.Frames.contextual S).Models g s.knowledge)
    (told : (Interface.Frames.contextual S).Models h r.body.tell)
    (matched : instantiateObservation h pat = instantiateObservation g (s.label a)) :
    (canonicalAt s r member a).Admits (Interface.Frames.contextual S) s := by
  have simple := canonical_simple (s := s) (member := member) (a := a) htake hread hprod
  have shapes := canonical_shapes (s := s) (member := member) (a := a) htake hread hprod hcollect
  obtain ⟨u, solved, _⟩ := simple_amalgamate simple shapes.1 present g h known told matched
  exact ⟨shapes, enabled_single present (freshId_not_mem s), ⟨_, u, solved⟩, entails_of_no_checks hchecks hcollect⟩

/-- A neighbour's rule: take an equation row `eqn(T)`, make the row `outside`. -/
def takeEqn : RuleSyntax.Rule (RuleSyntax.Contextual.Terms MSig) where
  locals := controlFrame [] ()
  body := { take := [observe (eqnN N (unk .datum))], read := [], tell := [], checks := [],
            produce := [observe (N.node .outside ![])] }
  collect := []

/-- The neighbour's program: that one rule. -/
abbrev takeProgram : RuleSyntax.Program (RuleSyntax.Contextual.Terms MSig) := {takeEqn}

/-- The firing of `takeEqn` on the equation row of the start of `Q`'s query. -/
def takeFiring : RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations MSig) takeProgram
    (Hosting.start N Q q).frame :=
  canonicalAt (Hosting.start N Q q) takeEqn (Set.mem_singleton _) 0

theorem takeSimple : Simple takeFiring 0 (freshId (Hosting.start N Q q)) (observe (eqnN N (unk .datum)))
    (observe (N.node .outside ![])) :=
  canonical_simple rfl rfl rfl

theorem start_Q_empty {B : Interface.Frames.Frame MSig} (g : Assignment (startArity mkeys) B.arity) :
    (Interface.Frames.contextual MSig).Models g (Hosting.start N Q q).knowledge := by
  intro e member
  exact absurd member List.not_mem_nil

/-- The instantiation of `takeEqn`'s unknowns that reads its pattern as the equation row. -/
def takeFill {B : Interface.Frames.Frame MSig} (g : Assignment (startArity mkeys) B.arity) :
    Assignment (unknownArity (S := MSig) [] ()) B.arity :=
  fill (instantiate g (instantiate (rowNames 0) gT)) (instantiate g (instantiate (rowNames 0) gT))
    (instantiate g (instantiate (rowNames 0) gT)) (instantiate g (instantiate (rowNames 0) gT))
    (instantiate g (instantiate (rowNames 0) gT))

theorem take_matched {B : Interface.Frames.Frame MSig} (g : Assignment (startArity mkeys) B.arity) :
    instantiateObservation (takeFill g) (observe (eqnN N (unk .datum))) =
      instantiateObservation g ((Hosting.start N Q q).label 0) := by
  show observe (instantiate (takeFill g) (eqnN N (unk .datum))) =
    observe (instantiate g (eqnN N (instantiate (rowNames 0) gT)))
  rw [instantiate_eqnN, instantiate_eqnN, instantiate_unk]
  rfl

theorem take_told {B : Interface.Frames.Frame MSig} (h : Assignment (unknownArity (S := MSig) [] ()) B.arity) :
    (Interface.Frames.contextual MSig).Models h takeEqn.body.tell := by
  intro e member
  exact absurd member List.not_mem_nil

/-- **The neighbour's rule fires on the equation row** of the start of `Q`'s query. -/
theorem takeEqn_fires : takeFiring.Admits (Interface.Frames.contextual MSig) (Hosting.start N Q q) :=
  canonical_admits (Set.mem_singleton _) rfl rfl rfl rfl rfl (B := ⟨Empty, noNames⟩) (by decide)
    (startFill (closeNames [] (csym "a"))) (takeFill _) (start_Q_empty _) (take_told _) (take_matched _)

/-- **That firing is not apart from the hosted rows of `Q`**: it takes one. -/
theorem takeEqn_not_apart : ¬ Apart Q 1 (Hosting.start N Q q) takeFiring :=
  fun apart => apart.taken 0 (List.mem_singleton_self 0) (by decide)

/-- The start of `Q`'s query represents the alternative of `P0`'s query, at row `1`, beside the
equation row. -/
theorem start_Q_beside : Beside N P0 0 (initialBranch q) (Hosting.start N Q q) 1 {0} := by
  refine ⟨?_, by decide, by decide⟩
  have renamed := represents_rename N (start_represents N P0 q q_unopened) (a' := 1) (Nat.zero_le 1)
  refine represents_relabel N renamed (startLabel N Q q) ?_
  intro o inside
  have isOne : o = 1 := by simpa [P0] using inside
  subst isOne
  show startLabel N Q q 1 = Function.update (Hosting.start N P0 q).label 1 ((Hosting.start N P0 q).label 0) 1
  rw [Function.update_self]
  rfl

/-- For `P0` the firing is apart: it takes a row that is not one of `P0`'s, and adds no knowledge of
the alternative's row. -/
theorem take_apart : Apart P0 1 (Hosting.start N Q q) takeFiring := by
  refine ⟨?_, ?_⟩
  · intro o taken
    rw [List.mem_singleton.mp taken]
    decide
  · intro B g known
    obtain ⟨u, solved, _, onRows, _⟩ :=
      simple_amalgamate takeSimple takeEqn_fires.1.1 (by decide) g (takeFill g) known (take_told _)
        (take_matched g)
    refine ⟨u, solved, fun o inside => onRows o ?_⟩
    have isOne : o = 1 := by simpa [P0] using inside
    subst isOne
    decide

/-- **A rule that takes a hosted row changes what the hosted program answers**: after the neighbour's
rule has taken the equation row of `Q`, the translated program of `Q` reaches a finished present row
whose answer is `{(g)}`; every answer of the source of `Q` is `{d}` (`only_d`). -/
theorem rule_takes_row :
    ∃ w a, Fires N Q (takeFiring.result (Interface.Frames.contextual MSig) (Hosting.start N Q q)) w ∧
      a ∈ w.present ∧ StateFinished N w a ∧ stateAnswer N w a = {gC} := by
  have besideAfter := beside_after_other N start_Q_beside takeEqn_fires take_apart
  have quietEqn : NeverReads (IsEquationRow N)
      (takeFiring.result (Interface.Frames.contextual MSig) (Hosting.start N Q q))
      (fire {0} (takeFiring.selection.commit (T := Unit))) := by
    intro o inside B σ _ reads
    rcases mem_fire.mp inside with ⟨inO, notTaken⟩ | isMade
    · exact notTaken (by
        rw [Finset.mem_singleton.mp inO]
        exact List.mem_toFinset.mpr (List.mem_singleton_self 0))
    · have isK : o = freshId (Hosting.start N Q q) := List.mem_singleton.mp (List.mem_toFinset.mp isMade)
      subst isK
      rw [simple_label_made takeSimple takeEqn_fires.1] at reads
      obtain ⟨x, same⟩ := reads
      change observe (instantiate σ (instantiate _ (N.node .outside ![]))) = _ at same
      rw [instantiate_outside, instantiate_outside] at same
      exact absurd (N.tag_eq (observe_injective same)) (by decide)
  have arrow : ArrowBranch (initialBranch (Ty := MTy) q) := ⟨trivial, .inl ⟨q, rfl, trivial⟩⟩
  have move : Move D P0 supply W0 (initialBranch q) W0 {⟨[], .value gT, [], []⟩} :=
    .unmatched W0 [] gT [] [] (fun _ member => by cases member)
  obtain ⟨w, a, fires, beside, _, _⟩ :=
    simulation_beside N (D := D) (supply := supply) (fun _ member => by cases member) move besideAfter arrow
      (hygienic_of_plain ⟨rfl, .inl ⟨q, rfl, trivial⟩⟩)
      (fun _ _ _ => noMatchingRow_of_neverReads N quietEqn) (Multiset.mem_singleton_self _) live_nil
  have finished : Branch.Finished (D := D) (⟨[], .value gT, [], []⟩ : Branch mkeys [] () MTy) := ⟨rfl, _, rfl⟩
  refine ⟨w, a, fires_mono (sub_of_no_equations Q) fires, beside.row_present N,
    (finished_iff N (D := D) (s := restrict w (hostedRows P0 a)) beside.hosted).mp ⟨finished, live_nil⟩, ?_⟩
  rw [show stateAnswer N w a = stateAnswer N (restrict w (hostedRows P0 a)) a from rfl,
    answer_eq N (D := D) beside.hosted finished, answer_of_determines rfl determines_g]

/-! ## A rule that reads a hosted row -/

/-- A neighbour's rule: read an equation row `eqn(T)`, make the row `outside`. -/
def readEqn : RuleSyntax.Rule (RuleSyntax.Contextual.Terms MSig) where
  locals := controlFrame [] ()
  body := { take := [], read := [observe (eqnN N (unk .datum))], tell := [], checks := [],
            produce := [observe (N.node .outside ![])] }
  collect := []

/-- The firing of `readEqn` that reads the equation row of the start of `Q`'s query. -/
def readFiring : RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations MSig)
    ({readEqn} : RuleSyntax.Program (RuleSyntax.Contextual.Terms MSig)) (Hosting.start N Q q).frame :=
  RuleSyntax.Contextual.canonical (F := (Hosting.start N Q q).frame) readEqn (Set.mem_singleton _)
    ⟨[], [0], [freshId (Hosting.start N Q q)]⟩ []

theorem enabled_read {present : Finset ℕ} {a a' : ℕ} (ha : a ∈ present) (ha' : a' ∉ present) :
    Enabled (fun _ : ℕ => ()) present ((⟨[], [a], [a']⟩ : Selection ℕ).commit (T := Unit)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [Selection.commit]
  · simp [Selection.commit, ha]
  · simp [Selection.commit]
  · simp [Selection.commit, ha']
  · simp [Selection.commit]

/-- The instantiation of the reading firing's frame from one of the start's names: the start's names
as given, the rule's unknown as the reading of the equation row. -/
def readSolution {B : Interface.Frames.Frame MSig} (g : Assignment (startArity mkeys) B.arity) :
    Assignment (RuleSyntax.Contextual.extend MSig (startFrame mkeys) (controlFrame [] ())).arity B.arity :=
  RuleSyntax.Contextual.copair MSig (F := startFrame mkeys) (N := controlFrame [] ()) g (takeFill g)

/-- Every instantiation of the start's names extends to a solution of the reading firing's
information that reads every row of the state as before. -/
theorem read_models {B : Interface.Frames.Frame MSig} (g : Assignment (startArity mkeys) B.arity) :
    (Interface.Frames.contextual MSig).Models (readSolution g)
      (readFiring.information (Interface.Frames.contextual MSig) (Hosting.start N Q q)) := by
  intro e member
  have single : e ∈ [(instantiateObservation readFiring.opening (observe (eqnN N (unk .datum))),
      readFiring.row (Interface.Frames.contextual MSig) (Hosting.start N Q q) 0)] := member
  rw [List.mem_singleton] at single
  subst single
  show instantiateObservation (readSolution g)
      (instantiateObservation
        (RuleSyntax.Contextual.canonicalOpening MSig (startFrame mkeys) (controlFrame [] ()))
        (observe (eqnN N (unk .datum)))) =
    instantiateObservation (readSolution g)
      (instantiateObservation (RuleSyntax.Contextual.weakenNames MSig (startFrame mkeys) (controlFrame [] ()))
        ((Hosting.start N Q q).label 0))
  unfold readSolution
  rw [RuleSyntax.Contextual.copair_opening, RuleSyntax.Contextual.copair_weaken]
  exact take_matched g

/-- **The neighbour's rule reads the equation row** of the start of `Q`'s query. -/
theorem readEqn_fires : readFiring.Admits (Interface.Frames.contextual MSig) (Hosting.start N Q q) :=
  ⟨⟨RuleSyntax.Contextual.canonical_fresh (Hosting.start N Q q) readEqn (Set.mem_singleton _) _ _,
      List.nodup_nil, List.nodup_singleton _, rfl, rfl, rfl, rfl⟩,
    enabled_read (by decide) (freshId_not_mem _),
    ⟨⟨Empty, noNames⟩, readSolution (startFill (closeNames [] (csym "a"))), read_models _⟩,
    entails_of_no_checks rfl rfl⟩

/-- **The reading firing is apart from the hosted rows of `Q`**: it takes none, and adds no knowledge of
them. -/
theorem read_apart : Apart Q 1 (Hosting.start N Q q) readFiring := by
  refine ⟨?_, ?_⟩
  · intro o taken
    exact absurd taken List.not_mem_nil
  · intro B g _
    refine ⟨readSolution g, read_models g, fun o _ => ?_⟩
    exact RuleSyntax.Contextual.copair_weaken MSig (F := startFrame mkeys) (N := controlFrame [] ()) g
      (takeFill g) _

/-- A row whose label is the opened node `outside` never reads as an alternative's row or as an
equation row. -/
theorem outside_never {w : HostState MSig} {F : Interface.Frames.Frame MSig}
    (opening : Assignment F.arity w.frame.arity) {k : ℕ}
    (label : w.label k = instantiateObservation opening (observe (N.node .outside ![]))) :
    NeverReads (IsAlternative N) w {k} ∧ NeverReads (IsEquationRow N) w {k} := by
  constructor
  · intro o inside B σ _ reads
    rw [Finset.mem_singleton.mp inside, label] at reads
    obtain ⟨x, y, same⟩ := reads
    change observe (instantiate σ (instantiate opening (N.node .outside ![]))) = _ at same
    rw [instantiate_outside, instantiate_outside] at same
    exact absurd (N.tag_eq (observe_injective same)) (by decide)
  · intro o inside B σ _ reads
    rw [Finset.mem_singleton.mp inside, label] at reads
    obtain ⟨x, same⟩ := reads
    change observe (instantiate σ (instantiate opening (N.node .outside ![]))) = _ at same
    rw [instantiate_outside, instantiate_outside] at same
    exact absurd (N.tag_eq (observe_injective same)) (by decide)

/-- `Q` and the query satisfy the clauses of the run theorems of the fragment with `let`. -/
theorem Q_scoped :
    (∀ e ∈ Q.equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs) ∧
    q.Scoped [[311]] ∧ (([311] : List ℕ) :: q.sites).Nodup ∧ ArrowComp q := by
  refine ⟨?_, by decide, by decide, trivial⟩
  intro e member
  rw [List.mem_singleton.mp member]
  exact ⟨by decide, by decide, trivial⟩

/-- **A rule that reads a hosted row leaves the hosted program as it is**: after the neighbour's rule
has read the equation row of `Q`, the answers the translated program of `Q` shows are, as a set, the
source's. -/
theorem reading_keeps :
    stepAnswersFrom N Q (readFiring.result (Interface.Frames.contextual MSig) (Hosting.start N Q q)) =
      Answers.sourceAnswers D Q supply sp q := by
  have startBeside : Beside N Q 0 (initialBranch q) (Hosting.start N Q q) 1 ∅ :=
    (beside_empty N).mpr (start_represents N Q q q_unopened)
  have after := beside_after_other N startBeside readEqn_fires read_apart
  have rows : fire (∅ : Finset ℕ) (readFiring.selection.commit (T := Unit)) =
      {freshId (Hosting.start N Q q)} := by
    show ((∅ : Finset ℕ) \ ([] : List ℕ).toFinset) ∪ [freshId (Hosting.start N Q q)].toFinset = _
    simp
  rw [rows] at after
  have label : (readFiring.result (Interface.Frames.contextual MSig) (Hosting.start N Q q)).label
      (freshId (Hosting.start N Q q)) =
      instantiateObservation readFiring.opening (observe (N.node .outside ![])) :=
    RuleSyntax.Firing.result_label_made readFiring readEqn_fires.1 (List.mem_singleton_self _)
  obtain ⟨noAlternative, noEquationRow⟩ :=
    outside_never (w := readFiring.result (Interface.Frames.contextual MSig) (Hosting.start N Q q))
      (F := controlFrame [] ()) readFiring.opening label
  exact answers_beside N (D := D) (supply := supply) sp q Q_scoped.1 Q_scoped.2.1 Q_scoped.2.2.1
    Q_scoped.2.2.2 after noAlternative noEquationRow

/-! ## A rule that reads a hosted row and tells more of it -/

/-- A neighbour's rule: read an alternative's row `alt(eval(ret T), FS)`, tell `T ≐ c`, make the row
`outside`. It takes no row. -/
def pinRule : RuleSyntax.Rule (RuleSyntax.Contextual.Terms MSig) where
  locals := controlFrame [] ()
  body := { take := [], read := [observe (altN N (evalN N (retN N (unk .datum))) (unk .stack))],
            tell := [(observe (unk .datum),
              observe (symAt "c" : Term (signature MSig (unknownArity (S := MSig) [] ())) [] ()))],
            checks := [], produce := [observe (N.node .outside ![])] }
  collect := []

/-- The firing of `pinRule` that reads the alternative's row of the start of the query `ret $x`. -/
def pinFiring : RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations MSig)
    ({pinRule} : RuleSyntax.Program (RuleSyntax.Contextual.Terms MSig)) (Hosting.start N P0 qx).frame :=
  RuleSyntax.Contextual.canonical (F := (Hosting.start N P0 qx).frame) pinRule (Set.mem_singleton _)
    ⟨[], [0], [freshId (Hosting.start N P0 qx)]⟩ []

theorem read_queryNames {B : Interface.Frames.Frame MSig} (σ : Assignment (startArity mkeys) B.arity)
    (t : MData) : instantiate σ (instantiate queryNames t) = instantiate (fun x => σ (.inl x)) t := by
  rw [instantiate_comp]
  apply congrArg (fun ρ => instantiate ρ t)
  funext x
  exact instantiate_generator σ (.inl x)

/-- The alternative's row of the start of `ret $x`, read by an instantiation of the start's names. -/
theorem start_qx_reads {B : Interface.Frames.Frame MSig} (σ : Assignment (startArity mkeys) B.arity) :
    instantiateObservation σ ((Hosting.start N P0 qx).label 0) =
      observe (altN N (evalN N (retN N (instantiate (fun x => σ (.inl x)) xName))) (emptyN N)) := by
  show observe (instantiate σ (encAlt N (instantiate queryNames) (.eval qx) [])) = _
  rw [instantiate_encAlt]
  exact congrArg (fun z => observe (altN N (evalN N (retN N z)) (emptyN N))) (read_queryNames σ xName)

/-- The instantiation of `pinRule`'s unknowns from a reading of the source's names. -/
def pinFill {B : Interface.Frames.Frame MSig} (σ : Assignment (fam mkeys) B.arity) :
    Assignment (unknownArity (S := MSig) [] ()) B.arity :=
  fill (instantiate σ xName) (instantiate σ xName) (instantiate σ xName) (instantiate σ xName) (emptyN N)

/-- The instantiation of the firing's frame from a reading of the source's names. -/
def pinSolution {B : Interface.Frames.Frame MSig} (σ : Assignment (fam mkeys) B.arity) :
    Assignment (RuleSyntax.Contextual.extend MSig (startFrame mkeys) (controlFrame [] ())).arity B.arity :=
  RuleSyntax.Contextual.copair MSig (F := startFrame mkeys) (N := controlFrame [] ()) (startFill σ) (pinFill σ)

/-- The two equations of the firing's information: the read, and the tell. -/
theorem pin_information (e : Equation (Observation MSig
      ((RuleSyntax.Contextual.declarations MSig).target pinFiring.ext).arity))
    (member : e ∈ pinFiring.information (Interface.Frames.contextual MSig) (Hosting.start N P0 qx)) :
    e = (instantiateObservation pinFiring.opening
          (observe (altN N (evalN N (retN N (unk .datum))) (unk .stack))),
        pinFiring.row (Interface.Frames.contextual MSig) (Hosting.start N P0 qx) 0) ∨
    e = (instantiateObservation pinFiring.opening (observe (unk .datum)),
        instantiateObservation pinFiring.opening
          (observe (symAt "c" : Term (signature MSig (unknownArity (S := MSig) [] ())) [] ()))) := by
  have two : e ∈ [(instantiateObservation pinFiring.opening
          (observe (altN N (evalN N (retN N (unk .datum))) (unk .stack))),
        pinFiring.row (Interface.Frames.contextual MSig) (Hosting.start N P0 qx) 0),
      (instantiateObservation pinFiring.opening (observe (unk .datum)),
        instantiateObservation pinFiring.opening
          (observe (symAt "c" : Term (signature MSig (unknownArity (S := MSig) [] ())) [] ())))] := member
  rcases List.mem_cons.mp two with first | rest
  · exact .inl first
  · exact .inr (List.mem_singleton.mp rest)

/-- A reading of the source's names that sends `$x` to `c` solves the firing's information. -/
theorem pin_models {B : Interface.Frames.Frame MSig} (σ : Assignment (fam mkeys) B.arity)
    (pinned : instantiate σ xName = symAt "c") :
    (Interface.Frames.contextual MSig).Models (pinSolution σ)
      (pinFiring.information (Interface.Frames.contextual MSig) (Hosting.start N P0 qx)) := by
  intro e member
  rcases pin_information e member with rfl | rfl
  · show instantiateObservation (pinSolution σ)
        (instantiateObservation
          (RuleSyntax.Contextual.canonicalOpening MSig (startFrame mkeys) (controlFrame [] ()))
          (observe (altN N (evalN N (retN N (unk .datum))) (unk .stack)))) =
      instantiateObservation (pinSolution σ)
        (instantiateObservation (RuleSyntax.Contextual.weakenNames MSig (startFrame mkeys) (controlFrame [] ()))
          ((Hosting.start N P0 qx).label 0))
    unfold pinSolution
    rw [RuleSyntax.Contextual.copair_opening, RuleSyntax.Contextual.copair_weaken, start_qx_reads]
    show observe (instantiate (pinFill σ) (altN N (evalN N (retN N (unk .datum))) (unk .stack))) = _
    rw [instantiate_altN, instantiate_evalN, instantiate_retN, instantiate_unk, instantiate_unk]
    rfl
  · show instantiateObservation (pinSolution σ)
        (instantiateObservation
          (RuleSyntax.Contextual.canonicalOpening MSig (startFrame mkeys) (controlFrame [] ()))
          (observe (unk .datum))) =
      instantiateObservation (pinSolution σ)
        (instantiateObservation
          (RuleSyntax.Contextual.canonicalOpening MSig (startFrame mkeys) (controlFrame [] ()))
          (observe (symAt "c" : Term (signature MSig (unknownArity (S := MSig) [] ())) [] ())))
    unfold pinSolution
    rw [RuleSyntax.Contextual.copair_opening, RuleSyntax.Contextual.copair_opening]
    show observe (instantiate (pinFill σ) (unk .datum)) = observe (instantiate (pinFill σ)
      (symAt "c" : Term (signature MSig (unknownArity (S := MSig) [] ())) [] ()))
    rw [instantiate_unk]
    exact congrArg observe pinned

/-- What a solution of the firing's information says: the name `$x`, read through it, is `c`. -/
theorem pin_solved {B : Interface.Frames.Frame MSig}
    (u : Assignment ((RuleSyntax.Contextual.declarations MSig).target pinFiring.ext).arity B.arity)
    (solved : (Interface.Frames.contextual MSig).Models u
      (pinFiring.information (Interface.Frames.contextual MSig) (Hosting.start N P0 qx))) :
    instantiate (fun x => Assignment.compose u
        ((RuleSyntax.Contextual.declarations MSig).weaken pinFiring.ext) (.inl x)) xName = symAt "c" := by
  have readMember : (instantiateObservation pinFiring.opening
        (observe (altN N (evalN N (retN N (unk .datum))) (unk .stack))),
      pinFiring.row (Interface.Frames.contextual MSig) (Hosting.start N P0 qx) 0) ∈
      pinFiring.information (Interface.Frames.contextual MSig) (Hosting.start N P0 qx) := by
    show _ ∈ [_, _]
    exact List.mem_cons_self
  have toldMember : (instantiateObservation pinFiring.opening (observe (unk .datum)),
      instantiateObservation pinFiring.opening
        (observe (symAt "c" : Term (signature MSig (unknownArity (S := MSig) [] ())) [] ()))) ∈
      pinFiring.information (Interface.Frames.contextual MSig) (Hosting.start N P0 qx) := by
    show _ ∈ [_, _]
    exact List.mem_cons_of_mem _ List.mem_cons_self
  have first : instantiateObservation u (instantiateObservation pinFiring.opening
        (observe (altN N (evalN N (retN N (unk .datum))) (unk .stack)))) =
      instantiateObservation u (pinFiring.row (Interface.Frames.contextual MSig) (Hosting.start N P0 qx) 0) :=
    solved _ readMember
  have second : instantiateObservation u (instantiateObservation pinFiring.opening (observe (unk .datum))) =
      instantiateObservation u (instantiateObservation pinFiring.opening
        (observe (symAt "c" : Term (signature MSig (unknownArity (S := MSig) [] ())) [] ()))) :=
    solved _ toldMember
  have row : instantiateObservation u (pinFiring.row (Interface.Frames.contextual MSig) (Hosting.start N P0 qx) 0) =
      instantiateObservation (Assignment.compose u ((RuleSyntax.Contextual.declarations MSig).weaken pinFiring.ext))
        ((Hosting.start N P0 qx).label 0) := instantiateObservation_comp _ _ _
  have whole := first.trans row
  rw [instantiateObservation_comp, start_qx_reads] at whole
  change observe (instantiate _ (altN N (evalN N (retN N (unk .datum))) (unk .stack))) = _ at whole
  rw [instantiate_altN, instantiate_evalN, instantiate_retN, instantiate_unk, instantiate_unk] at whole
  obtain ⟨onFocus, _⟩ := vec2_inj (N.args_eq (observe_injective whole))
  have onDatum := vec1_inj (N.args_eq (vec1_inj (N.args_eq onFocus)))
  rw [instantiateObservation_comp, instantiateObservation_comp] at second
  have told : observe (instantiate (Assignment.compose u pinFiring.opening) (unk .datum)) =
      observe (instantiate (Assignment.compose u pinFiring.opening)
        (symAt "c" : Term (signature MSig (unknownArity (S := MSig) [] ())) [] ())) := second
  have terms := observe_injective told
  rw [instantiate_unk] at terms
  exact onDatum.symm.trans terms

theorem pinned_c :
    instantiate (closeNames [(([], [7], 0), cC)] (csym "a")) xName =
      (symAt "c" : Term (signature MSig noNames) [] ()) := by
  show instantiate _ (foD [] [7] 0) = _
  rw [instantiate_foD]
  rfl

/-- **The neighbour's rule reads the alternative's row** of the start of the query `ret $x`. -/
theorem pin_fires : pinFiring.Admits (Interface.Frames.contextual MSig) (Hosting.start N P0 qx) :=
  ⟨⟨RuleSyntax.Contextual.canonical_fresh (Hosting.start N P0 qx) pinRule (Set.mem_singleton _) _ _,
      List.nodup_nil, List.nodup_singleton _, rfl, rfl, rfl, rfl⟩,
    enabled_read (by decide) (freshId_not_mem _),
    ⟨⟨Empty, noNames⟩, pinSolution (closeNames [(([], [7], 0), cC)] (csym "a")), pin_models _ pinned_c⟩,
    entails_of_no_checks rfl rfl⟩

/-- **It takes no hosted row.** -/
theorem pin_takes_none : ∀ o ∈ pinFiring.selection.taken, o ∉ hostedRows P0 0 :=
  fun _ taken => absurd taken List.not_mem_nil

/-- **It is not apart from the hosted rows**: it adds knowledge of the alternative's row. The reading
of the start that sends `$x` to `d` does not extend to a solution of its information. -/
theorem pin_not_apart : ¬ Apart P0 0 (Hosting.start N P0 qx) pinFiring := by
  intro apart
  obtain ⟨u, solved, onRows⟩ := apart.conservative ⟨Empty, noNames⟩
    (startFill (B := ⟨Empty, noNames⟩) (closeNames [(([], [7], 0), dC)] (csym "a")))
    (fun _ member => absurd member List.not_mem_nil)
  have isC := pin_solved u solved
  have row := onRows 0 (Finset.mem_insert_self _ _)
  have left : instantiateObservation u (pinFiring.row (Interface.Frames.contextual MSig) (Hosting.start N P0 qx) 0) =
      instantiateObservation (Assignment.compose u ((RuleSyntax.Contextual.declarations MSig).weaken pinFiring.ext))
        ((Hosting.start N P0 qx).label 0) := instantiateObservation_comp _ _ _
  have both := left.symm.trans row
  rw [start_qx_reads, start_qx_reads] at both
  obtain ⟨onFocus, _⟩ := vec2_inj (N.args_eq (observe_injective both))
  have onDatum := vec1_inj (N.args_eq (vec1_inj (N.args_eq onFocus)))
  have isD : instantiate (fun x => startFill (B := ⟨Empty, noNames⟩)
        (closeNames [(([], [7], 0), dC)] (csym "a")) (.inl x)) xName =
      (symAt "d" : Term (signature MSig noNames) [] ()) := by
    show instantiate (closeNames [(([], [7], 0), dC)] (csym "a")) (foD [] [7] 0) = _
    rw [instantiate_foD]
    rfl
  have clash := isC.symm.trans (onDatum.trans isD)
  change (Term.op (Sum.inl (MOp.sym "c")) .nil : Term (signature MSig noNames) [] ()) =
    Term.op (Sum.inl (MOp.sym "d")) .nil at clash
  simp at clash

/-- For the program with no equation, the representation is carried by the readings of the
alternative's row alone. -/
theorem represents_of_reads {n : ℕ} {b : Branch mkeys [] () MTy} {s s' : HostState MSig} {a a' : ℕ}
    (rep : Represents N P0 n b s a) (present' : s'.present = insert a' (Finset.range P0.equations.length))
    (same : ∀ (B : Interface.Frames.Frame MSig) (r : Observation MSig B.arity),
      rowReads s' a' B r ↔ rowReads s a B r) : Represents N P0 n b s' a' := by
  refine ⟨Nat.zero_le a', present', fun B r => (same B r).trans (rep.reads B r), ?_, ?_, rep.fresh,
    rep.noPending⟩
  · intro B σ _ i hi
    exact absurd hi (Nat.not_lt_zero i)
  · intro B σ _ i hi
    exact absurd hi (Nat.not_lt_zero i)

/-- After the firing, the alternative's row reads as it does with `$x ≐ c` in the knowledge. -/
theorem pin_reads (B : Interface.Frames.Frame MSig) (r : Observation MSig B.arity) :
    rowReads (pinFiring.result (Interface.Frames.contextual MSig) (Hosting.start N P0 qx)) 0 B r ↔
      rowReads constrained 0 B r := by
  have label : (pinFiring.result (Interface.Frames.contextual MSig) (Hosting.start N P0 qx)).label 0 =
      pinFiring.row (Interface.Frames.contextual MSig) (Hosting.start N P0 qx) 0 := by
    apply RuleSyntax.Firing.result_label_other
    intro inside
    have same : 0 = freshId (Hosting.start N P0 qx) := List.mem_singleton.mp inside
    exact absurd same.symm (Nat.succ_ne_zero _)
  constructor
  · rintro ⟨u, solved, rfl⟩
    have isC := pin_solved u solved
    refine ⟨Assignment.compose u ((RuleSyntax.Contextual.declarations MSig).weaken pinFiring.ext), ?_, ?_⟩
    · intro e member
      rw [List.mem_singleton.mp member]
      show observe (instantiate _ (instantiate queryNames xName)) =
        observe (instantiate _ (instantiate queryNames cT))
      rw [read_queryNames, read_queryNames, isC]
      rfl
    · rw [label]
      exact (instantiateObservation_comp _ _ _).symm
  · rintro ⟨g, known, rfl⟩
    have pinned : instantiate (fun x => g (.inl x)) xName = symAt "c" := by
      have same : observe (instantiate g (instantiate queryNames xName)) =
          observe (instantiate g (instantiate queryNames cT)) := known _ (List.mem_singleton_self _)
      have terms := observe_injective same
      rw [read_queryNames, read_queryNames] at terms
      exact terms
    refine ⟨pinSolution (fun x => g (.inl x)), pin_models _ pinned, ?_⟩
    rw [label]
    show instantiateObservation (pinSolution (fun x => g (.inl x)))
        (instantiateObservation (RuleSyntax.Contextual.weakenNames MSig (startFrame mkeys) (controlFrame [] ()))
          ((Hosting.start N P0 qx).label 0)) =
      instantiateObservation g ((Hosting.start N P0 qx).label 0)
    unfold pinSolution
    rw [RuleSyntax.Contextual.copair_weaken, start_qx_reads, start_qx_reads]
    rfl

/-- **A rule that takes no hosted row and tells more of one changes the answer**: after the
neighbour's rule has read the alternative's row of the query `ret $x` and told `$x ≐ c`, the translated
program reaches a finished present row whose answer is `{c}`; the source's answer to the query is every
closed term (`source_answers_all`, `c_ne_all`). -/
theorem pin_changes_answer :
    ∃ w a, Fires N P0 (pinFiring.result (Interface.Frames.contextual MSig) (Hosting.start N P0 qx)) w ∧
      a ∈ w.present ∧ StateFinished N w a ∧ stateAnswer N w a = {cC} := by
  have present : (pinFiring.result (Interface.Frames.contextual MSig) (Hosting.start N P0 qx)).present =
      hostedRows P0 0 ∪ {freshId (Hosting.start N P0 qx)} := by
    show (hostedRows P0 0 \ ([] : List ℕ).toFinset) ∪ [freshId (Hosting.start N P0 qx)].toFinset = _
    simp
  have hosted : Represents N P0 0 Bx
      (restrict (pinFiring.result (Interface.Frames.contextual MSig) (Hosting.start N P0 qx)) (hostedRows P0 0))
      0 :=
    represents_of_reads constrained_represents rfl (fun B r => pin_reads B r)
  have besideAfter : Beside N P0 0 Bx
      (pinFiring.result (Interface.Frames.contextual MSig) (Hosting.start N P0 qx)) 0
      {freshId (Hosting.start N P0 qx)} :=
    ⟨hosted, present, Finset.disjoint_singleton_right.mpr (freshId_not_mem (Hosting.start N P0 qx))⟩
  have move : Move D P0 supply W0 Bx W0 {⟨[(xName, cT)], .value xName, [], []⟩} :=
    .ret W0 [(xName, cT)] xName [] []
  obtain ⟨w, a, fires, beside, _, _⟩ :=
    simulation_beside N (D := D) (supply := supply) (fun _ member => by cases member) move besideAfter
      ⟨trivial, .inl ⟨_, rfl, trivial⟩⟩ (hygienic_of_plain ⟨rfl, .inl ⟨_, rfl, trivial⟩⟩)
      (fun t focus _ => by cases focus) (Multiset.mem_singleton_self _) live_xc
  have finished : Branch.Finished (D := D)
      (⟨[(xName, cT)], .value xName, [], []⟩ : Branch mkeys [] () MTy) := ⟨rfl, _, rfl⟩
  refine ⟨w, a, fires, beside.row_present N,
    (finished_iff N (D := D) (s := restrict w (hostedRows P0 a)) beside.hosted).mp ⟨finished, live_xc⟩, ?_⟩
  rw [show stateAnswer N w a = stateAnswer N (restrict w (hostedRows P0 a)) a from rfl,
    answer_eq N (D := D) beside.hosted finished, answer_of_determines rfl determines_xc]

/-! ## A program with no reachable unmatched call beside a row that matches its call -/

/-- **`Q` and the query `(g)` have no reachable unmatched call**: the only call is `(g)`, and the
equation matches it. -/
theorem matched_Q : NoUnmatchedCall D Q supply sp q := by
  intro C runs b member _ t focus
  rcases inv_runs (P := Q) rfl runs b member with rfl | rfl | rfl
  · cases focus
    exact ⟨eg, List.mem_singleton_self _, live_gg⟩
  · cases focus
  · cases focus

/-- A neighbour's equation row `eqn((g))`: it matches the call `(g)`. -/
def rowG : Observation MSig (startArity mkeys) := observe (eqnN N (instantiate (rowNames 7) gT))

theorem rowG_label {B : Interface.Frames.Frame MSig} (σ : Assignment (startArity mkeys) B.arity) :
    instantiateObservation σ ((startWith N Q q rowG).label (Q.equations.length + 1)) =
      observe (eqnN N (instantiate σ (instantiate (rowNames 7) gT))) := by
  show instantiateObservation σ (Function.update (startLabel N Q q) (Q.equations.length + 1) rowG
    (Q.equations.length + 1)) = _
  rw [Function.update_self]
  exact congrArg observe (instantiate_eqnN N σ _)

/-- **The row matches the call**: the condition on matching rows fails at this state. -/
theorem rowG_matches :
    ¬ NoMatchingRow N (startWith N Q q rowG) Q.equations.length {Q.equations.length + 1} := by
  intro noRow
  refine noRow (Q.equations.length + 1) (Finset.mem_singleton_self _) ⟨Empty, noNames⟩
    (startFill (closeNames [] (csym "a"))) (fun _ member => absurd member List.not_mem_nil)
    (instantiate (startFill (closeNames [] (csym "a"))) (instantiate queryNames gT)) (emptyN N) ?_ ?_
  · show observe (instantiate (startFill (closeNames [] (csym "a")))
      (encAlt N (instantiate queryNames) (.eval q) [])) = _
    rw [instantiate_encAlt]
    rfl
  · rw [rowG_label]
    rfl

/-- **A program with no reachable unmatched call is not disturbed by a row that matches its call**:
beside the row `eqn((g))`, the answers the translated program of `Q` shows are, as a set, the source's.
The same row leaves `P0`, whose call is unmatched, without a firing (`neighbour_stuck`). -/
theorem matching_row_harmless :
    stepAnswersFrom N Q (startWith N Q q rowG) = Answers.sourceAnswers D Q supply sp q := by
  refine answers_beside_of_matched N (D := D) (supply := supply) sp q Q_scoped.1 Q_scoped.2.1
    Q_scoped.2.2.1 Q_scoped.2.2.2 matched_Q (startWith_beside N (P := Q) q rowG q_unopened) ?_
  intro o inside B σ _ reads
  obtain ⟨x, y, same⟩ := reads
  rw [Finset.mem_singleton.mp inside, rowG_label σ] at same
  exact absurd (N.tag_eq (observe_injective same)) (by decide)

/-! ## Control rows are ordinary data -/

/-- The equation row's node is the MeTTa datum `(eqn t)`: control and user data share one signature. -/
theorem eqn_node_is_data (t : MData) : (mettaNodes.node .eqn ![t] : MData) = tuple [sym "eqn", t] := rfl

/-- So is an alternative's row `(alt (eval (apply t)) (empty))`. -/
theorem alt_node_is_data (t : MData) :
    (altN mettaNodes (evalN mettaNodes (applyN mettaNodes t)) (emptyN mettaNodes) : MData) =
      tuple [sym "alt", tuple [sym "eval", tuple [sym "apply", t]], tuple [sym "empty"]] := rfl

#print axioms p0_answers_g
#print axioms p0_only_g
#print axioms mixed_answers_g
#print axioms union_answers_only_d
#print axioms g_ne_d
#print axioms no_firing_of_unsolvable
#print axioms knowledge_switches_off
#print axioms constrained_solvable
#print axioms constrained_represents
#print axioms knowledge_changes_answer
#print axioms source_answers_all
#print axioms c_ne_all
#print axioms one_more_row
#print axioms neighbour_stuck
#print axioms variable_row_stuck
#print axioms same_head_fires
#print axioms twoAlternatives_beside
#print axioms twoAlternatives_beside'
#print axioms row_reads_alternative
#print axioms alternative_row_answers
#print axioms canonical_admits
#print axioms takeEqn_fires
#print axioms takeEqn_not_apart
#print axioms start_Q_beside
#print axioms take_apart
#print axioms rule_takes_row
#print axioms readEqn_fires
#print axioms read_apart
#print axioms reading_keeps
#print axioms pin_fires
#print axioms pin_takes_none
#print axioms pin_not_apart
#print axioms pin_reads
#print axioms pin_changes_answer
#print axioms matched_Q
#print axioms rowG_matches
#print axioms matching_row_harmless
#print axioms only_d
#print axioms eqn_node_is_data
#print axioms alt_node_is_data

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.Controls
