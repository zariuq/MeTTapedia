import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.WellFormedRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Toolkit

/-!
# The control on a whole run: a name used outside its scope

The query is `(let $x (let $x two one) $x)` where the inner arrow's pattern is written as the
**outer** arrow's `$x` (site `[7]`), inside the computation the outer arrow binds. The scope rule
forbids exactly this: an arrow's own names occur only in its pattern and its body. The query fails
the scope clause and only it (`query_not_scoped`, `query_other_clauses`).

* The source (`runs_to_unhygienic`, `runs_to_final`, `final_answers`): the inner arrow binds the
  outer `$x` to `two` (it is not the inner arrow's own name, so the inner bind does not open it);
  the alternative then returns `one` to the outer frame with `$x` already in its store: it is not
  hygienic (`not_hygienic`). The outer bind opens a fresh copy of `$x` and binds it to `one`; the
  bag of answers at the end is `{one}`.
* The step (`step_reaches`, `no_firing`, `reached_inv`, `no_step_answers`): it follows the same run,
  by runs of the step from the translation's start, to a state that represents the non-hygienic
  alternative, and there **it has no firing at all** (`no_firing`): the rule's bind would tell the
  outer `$x`, which the knowledge already equates with `two`, equal to `one` (`step_dies` computes
  what such a firing would make, a dead alternative), while an admitted firing's information has a
  solution. Every state that runs of the translated program reach from the start represents one of
  the six alternatives of the source run before its outer bind (`reached_inv`), and none of them has
  finished: **no run of the step answers** (`no_step_answers`).

So outside the scope clause of the hygiene lemma, and only outside it, the source answers `one` and
no run of the step answers anything (`source_and_step_part`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.ExampleOutOfScope

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage SourceLanguage.Elaboration SourceLanguage.Toolkit

abbrev D := untyped.discipline
abbrev N := mettaNodes

/-! ## The query -/

/-- No equations. -/
def program : SourceLanguage.Program mkeys [] () MTy := ⟨[], fun t => .apply t⟩

def supply : ℕ → MClosed := fun _ => csym "space"

/-- The outer arrow's frame `let $x = □ in $x`, and the inner arrow's frame, whose pattern is the outer
`$x`. -/
def outerFrame : SourceLanguage.Frame mkeys [] () MTy := .bindTo [7] xName (.ret xName)
def innerFrame : SourceLanguage.Frame mkeys [] () MTy := .bindTo [8] xName (.ret (sym "one"))

/-- `(let $x (let $x two one) $x)`, the inner pattern being the outer `$x`. -/
def query : Comp mkeys [] () MTy :=
  .let_ [7] xName (.let_ [8] xName (.ret (sym "two")) (.ret (sym "one"))) (.ret xName)

/-- The scope clause fails. -/
theorem query_not_scoped : ¬ Comp.Scoped (κ := mkeys) [[100]] query := by decide

/-- The other clauses of a well-formed query hold. -/
theorem query_other_clauses :
    ((∀ p ∈ query.patterns, IsPattern p) ∧
      ∀ t ∈ query.data, flexOk (fun x => query.patterns.any fun p => decide (x ∈ support p)) t = true) ∧
    ([100] :: query.sites ++ program.sites).Nodup := by decide

theorem query_not_wellFormed : ¬ QueryWellFormed program [100] query :=
  fun wf => query_not_scoped wf.inScope

theorem query_arrows : ArrowComp query := ⟨⟨trivial, trivial⟩, trivial⟩

theorem query_unopened : ∀ t ∈ query.data, ∀ x ∈ support t, x.scopes = [] := by decide

theorem program_arrows : ArrowProgram program := fun _ member => nomatch member

/-! ## The source run -/

/-- The fresh copy of `$x` that the outer bind opens at scope `1`. -/
def x1 : MData := instantiate (openAt mkeys [7] 1) xName

abbrev B0 : Branch mkeys [] () MTy := ⟨[], .eval query, [], []⟩
abbrev B1 : Branch mkeys [] () MTy :=
  ⟨[], .eval (.let_ [8] xName (.ret (sym "two")) (.ret (sym "one"))), [outerFrame], []⟩
abbrev B2 : Branch mkeys [] () MTy := ⟨[], .eval (.ret (sym "two")), [innerFrame, outerFrame], []⟩
abbrev B3 : Branch mkeys [] () MTy := ⟨[], .value (sym "two"), [innerFrame, outerFrame], []⟩
abbrev B4 : Branch mkeys [] () MTy := ⟨[(xName, sym "two")], .eval (.ret (sym "one")), [outerFrame], []⟩
abbrev B6 : Branch mkeys [] () MTy := ⟨[(xName, sym "two"), (x1, sym "one")], .eval (.ret x1), [], []⟩
abbrev B7 : Branch mkeys [] () MTy := ⟨[(xName, sym "two"), (x1, sym "one")], .value x1, [], []⟩

abbrev W0 : World mkeys [] () := ⟨0, 0, fun _ => 0⟩
abbrev W1 : World mkeys [] () := ⟨1, 0, fun _ => 0⟩
abbrev W2 : World mkeys [] () := ⟨2, 0, fun _ => 0⟩

/-- The configuration holding the non-hygienic alternative. -/
def reached : Config mkeys [] () MTy := ⟨W1, {unhygienic}⟩

/-- The configuration at the end. -/
def final : Config mkeys [] () MTy := ⟨W2, {B7}⟩

/-- A solution of the whole store: `$x = two`, its fresh copy `= one`. -/
def solution : Assignment (fam mkeys) noNames :=
  closeNames [(([], [7], 0), csym "two"), (([1], [7], 0), csym "one")] (csym "a")

theorem live_two : Solvable [(xName, sym "two")] :=
  ⟨Empty, noNames, solution, fun e member => by
    simp only [List.mem_singleton] at member
    subst member
    rfl⟩

theorem live_both : Solvable [(xName, sym "two"), (x1, sym "one")] :=
  ⟨Empty, noNames, solution, fun e member => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl⟩

theorem s1 : SourceLanguage.Step D program supply (Config.initial (fun _ => 0) query) ⟨W0, {B1}⟩ :=
  Step.of_eq (rest := 0) rfl (add_zero _).symm live_nil
    (Move.letStart (D := D) (P := program) (supply := supply) W0 [] [7] xName
      (.let_ [8] xName (.ret (sym "two")) (.ret (sym "one"))) (.ret xName) [] [])

theorem s2 : SourceLanguage.Step D program supply ⟨W0, {B1}⟩ ⟨W0, {B2}⟩ :=
  Step.of_eq (rest := 0) rfl (add_zero _).symm live_nil
    (Move.letStart (D := D) (P := program) (supply := supply) W0 [] [8] xName (.ret (sym "two"))
      (.ret (sym "one")) [outerFrame] [])

theorem s3 : SourceLanguage.Step D program supply ⟨W0, {B2}⟩ ⟨W0, {B3}⟩ :=
  Step.of_eq (rest := 0) rfl (add_zero _).symm live_nil
    (Move.ret (D := D) (P := program) (supply := supply) W0 [] (sym "two") [innerFrame, outerFrame] [])

/-- The inner bind, at scope `0`: the outer `$x` is not of the inner site, so it is not opened. -/
theorem s4 : SourceLanguage.Step D program supply ⟨W0, {B3}⟩ ⟨W1, {B4}⟩ :=
  Step.of_eq (rest := 0) rfl (add_zero _).symm live_nil
    (Move.letBind (D := D) (P := program) (supply := supply) W0 [] (sym "two") [8] xName
      (.ret (sym "one")) [outerFrame] [])

theorem s5 : SourceLanguage.Step D program supply ⟨W1, {B4}⟩ reached :=
  Step.of_eq (rest := 0) rfl (add_zero _).symm live_two
    (Move.ret (D := D) (P := program) (supply := supply) W1 [(xName, sym "two")] (sym "one") [outerFrame] [])

/-- The outer bind, at scope `1`: a fresh copy of `$x` is bound to `one`. -/
theorem s6 : SourceLanguage.Step D program supply reached ⟨W2, {B6}⟩ :=
  Step.of_eq (rest := 0) rfl (add_zero _).symm live_two
    (Move.letBind (D := D) (P := program) (supply := supply) W1 [(xName, sym "two")] (sym "one") [7] xName
      (.ret xName) [] [])

theorem s7 : SourceLanguage.Step D program supply ⟨W2, {B6}⟩ final :=
  Step.of_eq (rest := 0) rfl (add_zero _).symm live_both
    (Move.ret (D := D) (P := program) (supply := supply) W2 [(xName, sym "two"), (x1, sym "one")] x1 [] [])

theorem runs_to_unhygienic : Runs D program supply (Config.initial (fun _ => 0) query) reached :=
  ((((Relation.ReflTransGen.single s1).tail s2).tail s3).tail s4).tail s5

theorem runs_to_final : Runs D program supply reached final :=
  (Relation.ReflTransGen.single s6).tail s7

/-- **The alternative the run reaches is not hygienic**: the frame's own `$x` is in the store. -/
theorem not_hygienic : ¬ Hygienic unhygienic :=
  fun hygienic => hygiene_needed.1 (hygienic _ _ _ _ _ _ _ rfl)

theorem determines_one : Determines [(xName, sym "two"), (x1, sym "one")] x1 (csym "one") := by
  refine ⟨live_both, fun target τ solved => ?_⟩
  have copy : instantiate τ (foD [1] [7] 0) = symAt "one" :=
    solved (x1, sym "one") (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  show instantiate τ (foD [1] [7] 0) = _
  rw [copy]
  rfl

/-- **The source's answers at the end**: `{one}`. -/
theorem final_answers : Config.answers (D := D) final = {{csym "one"}} := by
  have finished : Branch.Finished (D := D) B7 := ⟨rfl, _, rfl⟩
  show Config.answers (D := D) ⟨W2, {B7}⟩ = _
  rw [answers_singleton finished live_both, answer_of_determines rfl determines_one]

/-! ## The step -/

theorem hygienic_of_focus_eval {b : Branch mkeys [] () MTy} {c : Comp mkeys [] () MTy}
    (focus : b.focus = .eval c) : Hygienic b := by
  intro K v s p k fs ps same
  subst same
  cases focus

/-- The inner frame binds no name of its own site: its bind is hygienic. -/
theorem inner_private :
    FramePrivate [8] xName (.ret (sym "one")) [] (sym "two") [outerFrame] := by
  intro W target σ σ' agree
  have same : σ = σ' := funext fun y => agree y (by
    rintro ⟨site, inP | ⟨t, inK, inT⟩⟩
    · simp only [xName, foD, support, supportArgs, List.mem_singleton] at inP
      subst inP
      exact absurd site (by decide)
    · simp only [Comp.data, List.mem_singleton] at inK
      subst inK
      simp [sym, support, supportArgs] at inT)
  subst same
  exact ⟨fun _ _ => ⟨rfl, rfl⟩, rfl, fun _ _ _ _ => rfl⟩

open Classical in
/-- **The step follows the run to the non-hygienic alternative**: a state reached from the
translation's start represents it. -/
theorem step_reaches :
    ∃ (s : HostState MSig) (a : ℕ), Relation.ReflTransGen (Fires N program) (Hosting.start N program query) s ∧
      Represents N program 1 unhygienic s a := by
  have f0 := arrowFrontier_initial N (D := D) (P := program) (fun _ => 0) query query_arrows query_unopened
  have r0 : ∀ x ∈ ({(initialBranch query, Hosting.start N program query, program.equations.length)} :
      Multiset (Branch mkeys [] () MTy × HostState MSig × ℕ)),
      Relation.ReflTransGen (Fires N program) (Hosting.start N program query) x.2.1 := by
    intro x member
    rw [Multiset.mem_singleton.mp member]
  have single : ∀ {b : Branch mkeys [] () MTy} {c : Comp mkeys [] () MTy}, b.focus = .eval c →
      ∀ w, ∀ b' ∈ (⟨w, {b}⟩ : Config mkeys [] () MTy).branches, Hygienic b' := by
    intro b c focus w b' member
    rw [Multiset.mem_singleton.mp member]
    exact hygienic_of_focus_eval focus
  obtain ⟨L1, f1, r1⟩ := arrowFrontier_reached_step N program_arrows f0 r0 (single rfl W0) s1
  obtain ⟨L2, f2, r2⟩ := arrowFrontier_reached_step N program_arrows f1 r1 (single rfl W0) s2
  obtain ⟨L3, f3, r3⟩ := arrowFrontier_reached_step N program_arrows f2 r2 (single rfl W0) s3
  have hygienic3 : ∀ b ∈ (⟨W0, {B3}⟩ : Config mkeys [] () MTy).branches, Hygienic b := by
    intro b member
    rw [Multiset.mem_singleton.mp member]
    intro K v s p k fs ps same
    cases same
    exact inner_private
  obtain ⟨L4, f4, r4⟩ := arrowFrontier_reached_step N program_arrows f3 r3 hygienic3 s4
  obtain ⟨L5, f5, r5⟩ := arrowFrontier_reached_step N program_arrows f4 r4 (single rfl W1) s5
  have inside : unhygienic ∈ L5.map Prod.fst := by
    rw [f5.branches]
    exact Multiset.mem_filter.mpr ⟨Multiset.mem_singleton_self _, live_two⟩
  obtain ⟨x, member, first⟩ := Multiset.mem_map.mp inside
  have rep := (f5.represents x member).1
  rw [first] at rep
  exact ⟨x.2.1, x.2.2, r5 x member, rep⟩

/-- The alternative a bind of the step would make: the outer `$x` bound to `one` with no fresh copy. -/
def stepChild : Branch mkeys [] () MTy := ⟨[(xName, sym "two"), (xName, sym "one")], .eval (.ret xName), [], []⟩

theorem stepChild_dead : ¬ Solvable stepChild.store := by
  rintro ⟨X, target, σ, solved⟩
  have two := solved _ (List.mem_cons_self ..)
  have one := solved _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have both := two.symm.trans one
  change (Term.op (Sum.inl (MOp.sym "two")) .nil : Term (signature MSig target) [] ()) =
    Term.op (Sum.inl (MOp.sym "one")) .nil at both
  simp at both

theorem stepChild_below (n : ℕ) : BranchBelow n stepChild := by
  refine ⟨?_, ?_, ?_⟩
  · intro e member
    simp only [stepChild, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;>
      exact ⟨dependsBelow_of_unopened n (by decide), dependsBelow_of_unopened n (by decide)⟩
  · intro t member
    simp only [stepChild, focusData, Comp.data, List.mem_singleton] at member
    subst member
    exact dependsBelow_of_unopened n (by decide)
  · intro fr member
    exact absurd member (by simp [stepChild])

/-- **What a firing there would make**: a firing at a state that represents the non-hygienic
alternative would make a state that represents the dead alternative `stepChild`, after which nothing
fires. There is no such firing (`no_firing`): this lemma is the computation that shows it. -/
theorem step_dies {n a : ℕ} {s s' : HostState MSig} (rep : Represents N program n unhygienic s a)
    (fires : Fires N program s s') :
    (∃ a', Represents N program n stepChild s' a') ∧ ∀ s'', ¬ Fires N program s' s'' := by
  have child : ∃ a', Represents N program n stepChild s' a' := by
    obtain ⟨⟨rule, member, ext, opening, selection, seen⟩, admitted, rfl⟩ := fires
    rcases (mem_translate N).mp member with control | ⟨e, eMember, _⟩
    · rcases (mem_controlRules N).mp control with rfl | rfl | rfl | rfl | rfl | rfl
      · obtain ⟨_, _, _, B, h, reads, _⟩ := admitted_takes_alternative N rep admitted rfl rfl rfl
          (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
        obtain ⟨t, focus⟩ := shape_ret N reads
        cases focus
      · obtain ⟨_, _, _, B, h, reads, _⟩ := admitted_takes_alternative N rep admitted rfl rfl rfl
          (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
        change branchReads N _ B (observe (instantiate h _)) at reads
        rw [instantiate_altN, instantiate_evalN, instantiate_applyN] at reads
        obtain ⟨t, _, focus, _⟩ := shape_apply N reads
        cases focus
      · obtain ⟨_, _, _, B, h, reads, _⟩ := admitted_takes_alternative N rep admitted rfl rfl rfl
          (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
        obtain ⟨c, d, focus⟩ := shape_choice N reads
        cases focus
      · obtain ⟨_, _, _, B, h, reads, _⟩ := admitted_takes_alternative N rep admitted rfl rfl rfl
          (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
        obtain ⟨c, d, focus⟩ := shape_choice N reads
        cases focus
      · obtain ⟨_, _, _, B, h, reads, _⟩ := admitted_takes_alternative N rep admitted rfl rfl rfl
          (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
        obtain ⟨_, _, _, _, focus⟩ := shape_bindStart N reads
        cases focus
      · obtain ⟨a', simple, fresh, _⟩ := admitted_takes_alternative N rep admitted rfl rfl rfl
          (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
        refine ⟨a', represents_after N rep simple admitted.1 fresh ?_ (stepChild_below n) rfl⟩
        intro B q
        constructor
        · intro exists'
          exact absurd exists' (hygiene_needed.2.2 B q)
        · rintro ⟨σ, solved, _⟩
          exact absurd ⟨_, _, σ, solved⟩ stepChild_dead
    · cases eMember
  refine ⟨child, fun s'' fires' => ?_⟩
  obtain ⟨a', rep'⟩ := child
  exact stepChild_dead (live_of_fires N (D := D) rep' fires')

/-- **The step is stuck** at a state that represents the non-hygienic alternative: an admitted
firing's information is the made state's knowledge, so the made state would read its row, and the
alternative it represents (`step_dies`) has no reading. -/
theorem no_firing {n a : ℕ} {s s' : HostState MSig} (rep : Represents N program n unhygienic s a) :
    ¬ Fires N program s s' := by
  intro fires
  obtain ⟨⟨a', rep'⟩, _⟩ := step_dies rep fires
  obtain ⟨f, admitted, rfl⟩ := fires
  obtain ⟨B, u, solved⟩ := admitted.2.2.1
  obtain ⟨σ, solvedσ, _⟩ := (rep'.reads B _).mp ⟨u, solved, rfl⟩
  exact stepChild_dead ⟨_, _, σ, solvedσ⟩

/-! ## Every state the step reaches -/

/-- The trivial discipline with its type language on the nose (for case analysis on moves). -/
abbrev Dc : Discipline MSig [] () := ⟨MTy, fun _ _ => True⟩
abbrev sp : MClosed → Multiset (Row mkeys [] ()) := fun _ => 0

section Moves

variable {w w' : World mkeys [] ()} {b : Branch mkeys [] () Dc.Ty} {bs : Multiset (Branch mkeys [] () Dc.Ty)}

theorem move_B0 (move : Move Dc program supply w b w' bs) (hb : b = B0) : w' = w ∧ ∀ b' ∈ bs, b' = B1 := by
  cases move <;> cases hb
  exact ⟨rfl, fun b' made => Multiset.mem_singleton.mp made⟩

theorem move_B1 (move : Move Dc program supply w b w' bs) (hb : b = B1) : w' = w ∧ ∀ b' ∈ bs, b' = B2 := by
  cases move <;> cases hb
  exact ⟨rfl, fun b' made => Multiset.mem_singleton.mp made⟩

theorem move_B2 (move : Move Dc program supply w b w' bs) (hb : b = B2) : w' = w ∧ ∀ b' ∈ bs, b' = B3 := by
  cases move <;> cases hb
  exact ⟨rfl, fun b' made => Multiset.mem_singleton.mp made⟩

theorem move_B3 (move : Move Dc program supply w b w' bs) (hb : b = B3) :
    w'.scope = w.scope + 1 ∧ ∀ b' ∈ bs, b' = B4 := by
  cases move <;> cases hb
  refine ⟨rfl, fun b' made => ?_⟩
  rw [Multiset.mem_singleton.mp made]
  rfl

theorem move_B4 (move : Move Dc program supply w b w' bs) (hb : b = B4) :
    w' = w ∧ ∀ b' ∈ bs, b' = unhygienic := by
  cases move <;> cases hb
  exact ⟨rfl, fun b' made => Multiset.mem_singleton.mp made⟩

end Moves

/-- The six alternatives of the source run before its outer bind, each represented at its scope. -/
def Inv (s : HostState MSig) : Prop :=
  ∃ a, Represents N program 0 B0 s a ∨ Represents N program 0 B1 s a ∨ Represents N program 0 B2 s a ∨
    Represents N program 0 B3 s a ∨ Represents N program 1 B4 s a ∨ Represents N program 1 unhygienic s a

theorem hygienic3 : Hygienic B3 := by
  intro K v s p k fs ps same
  cases same
  exact inner_private

theorem inv_step {s s' : HostState MSig} (inv : Inv s) (fires : Fires N program s s') : Inv s' := by
  obtain ⟨a, rep | rep | rep | rep | rep | rep⟩ := inv
  · obtain ⟨w', bs, b', a', move, child, rep', _⟩ := reflection_arrows N (D := Dc) (supply := supply)
      (w := ⟨0, 0, sp⟩) program_arrows rep ⟨trivial, .inl ⟨_, rfl, query_arrows⟩⟩
      (hygienic_of_focus_eval rfl) fires
    obtain ⟨hw, hb⟩ := move_B0 move rfl
    rw [hb b' child, hw] at rep'
    exact ⟨a', .inr (.inl rep')⟩
  · obtain ⟨w', bs, b', a', move, child, rep', _⟩ := reflection_arrows N (D := Dc) (supply := supply)
      (w := ⟨0, 0, sp⟩) program_arrows rep ⟨⟨trivial, trivial⟩, .inl ⟨_, rfl, ⟨trivial, trivial⟩⟩⟩
      (hygienic_of_focus_eval rfl) fires
    obtain ⟨hw, hb⟩ := move_B1 move rfl
    rw [hb b' child, hw] at rep'
    exact ⟨a', .inr (.inr (.inl rep'))⟩
  · obtain ⟨w', bs, b', a', move, child, rep', _⟩ := reflection_arrows N (D := Dc) (supply := supply)
      (w := ⟨0, 0, sp⟩) program_arrows rep ⟨⟨trivial, trivial, trivial⟩, .inl ⟨_, rfl, trivial⟩⟩
      (hygienic_of_focus_eval rfl) fires
    obtain ⟨hw, hb⟩ := move_B2 move rfl
    rw [hb b' child, hw] at rep'
    exact ⟨a', .inr (.inr (.inr (.inl rep')))⟩
  · obtain ⟨w', bs, b', a', move, child, rep', _⟩ := reflection_arrows N (D := Dc) (supply := supply)
      (w := ⟨0, 0, sp⟩) program_arrows rep ⟨⟨trivial, trivial, trivial⟩, .inr ⟨_, rfl⟩⟩ hygienic3 fires
    obtain ⟨hw, hb⟩ := move_B3 move rfl
    rw [hb b' child, hw] at rep'
    exact ⟨a', .inr (.inr (.inr (.inr (.inl rep'))))⟩
  · obtain ⟨w', bs, b', a', move, child, rep', _⟩ := reflection_arrows N (D := Dc) (supply := supply)
      (w := ⟨1, 0, sp⟩) program_arrows rep ⟨⟨trivial, trivial⟩, .inl ⟨_, rfl, trivial⟩⟩
      (hygienic_of_focus_eval rfl) fires
    obtain ⟨hw, hb⟩ := move_B4 move rfl
    rw [hb b' child, hw] at rep'
    exact ⟨a', .inr (.inr (.inr (.inr (.inr rep'))))⟩
  · exact absurd fires (no_firing rep)

/-- **Every state that runs of the translated program reach from the start** represents one of the six
alternatives of the source run before its outer bind. -/
theorem reached_inv {s : HostState MSig}
    (run : Relation.ReflTransGen (Fires N program) (Hosting.start N program query) s) : Inv s := by
  induction run with
  | refl => exact ⟨_, .inl (start_represents N program query query_unopened)⟩
  | tail _ fires ih => exact inv_step ih fires

theorem not_finished {n a : ℕ} {s : HostState MSig} {b : Branch mkeys [] () MTy}
    (rep : Represents N program n b s a) (unfinished : ¬ b.Finished (D := Dc)) : ¬ StateFinished N s a :=
  fun fin => unfinished ((finished_iff N (D := Dc) rep).mpr fin).1

theorem only_row {n a a' : ℕ} {s : HostState MSig} {b : Branch mkeys [] () MTy}
    (rep : Represents N program n b s a) (present : a' ∈ s.present) : a' = a := by
  rw [rep.present] at present
  simpa [program] using present

/-- **No run of the step answers**: no state that runs of the translated program reach from the start
has a finished row. The source's bag at the end of its run is `{one}` (`final_answers`). -/
theorem no_step_answers {s : HostState MSig}
    (run : Relation.ReflTransGen (Fires N program) (Hosting.start N program query) s) :
    ∀ a ∈ s.present, ¬ StateFinished N s a := by
  intro a' present
  obtain ⟨a, rep | rep | rep | rep | rep | rep⟩ := reached_inv run
  all_goals
    rw [only_row rep present]
    refine not_finished rep ?_
    rintro ⟨frames, t, focus⟩
    cases focus <;> cases frames

/-- **The control on a whole run.** Outside the scope clause (and only outside it), the source runs to
a non-hygienic alternative and on to the answers `{one}`; the step follows the same run to a state that
represents that alternative, where it has no firing, and no state that runs of the step reach from the
start has a finished row. -/
theorem source_and_step_part :
    ¬ Comp.Scoped (κ := mkeys) [[100]] query ∧
    Runs D program supply (Config.initial (fun _ => 0) query) reached ∧ unhygienic ∈ reached.branches ∧
    ¬ Hygienic unhygienic ∧
    Runs D program supply reached final ∧ Config.answers (D := D) final = {{csym "one"}} ∧
    (∃ (s : HostState MSig) (a : ℕ), Relation.ReflTransGen (Fires N program) (Hosting.start N program query) s ∧
      Represents N program 1 unhygienic s a ∧ ∀ s', ¬ Fires N program s s') ∧
    ∀ s, Relation.ReflTransGen (Fires N program) (Hosting.start N program query) s →
      ∀ a ∈ s.present, ¬ StateFinished N s a := by
  obtain ⟨s, a, run, rep⟩ := step_reaches
  exact ⟨query_not_scoped, runs_to_unhygienic, Multiset.mem_singleton_self _, not_hygienic, runs_to_final,
    final_answers, ⟨s, a, run, rep, fun _ => no_firing rep⟩, fun _ run' => no_step_answers run'⟩

#print axioms query_not_scoped
#print axioms query_other_clauses
#print axioms not_hygienic
#print axioms final_answers
#print axioms step_reaches
#print axioms step_dies
#print axioms no_firing
#print axioms reached_inv
#print axioms no_step_answers
#print axioms source_and_step_part

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.ExampleOutOfScope
