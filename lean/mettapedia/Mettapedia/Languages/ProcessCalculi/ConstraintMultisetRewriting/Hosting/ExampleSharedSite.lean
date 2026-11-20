import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.WellFormedRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Toolkit

/-!
# The second control: two arrows sharing a site

The hygiene lemma uses two clauses of well-formedness: scope (its control is `ExampleOutOfScope`) and
distinct binder sites. This is the control for the second. The query is
`(let $x one (let $y two $x))` with **both arrows at the site `[7]`**: it is scoped, and only the
distinctness of sites fails (`query_scoped`, `query_sites_shared`).

* The run (`runs_to_unhygienic`): the outer bind opens the site `[7]` at scope `0`, which renames
  both `$x` and the inner arrow's `$y`; the inner arrow then returns `two` to its frame while the
  store already holds the opened `$x`, which is of the inner arrow's site and occurs in its body: the
  alternative is not hygienic (`not_hygienic`).
* The capture (`runs_to_final`, `final_answers`): the inner bind opens the site `[7]` again, and so
  renames the `$x` of its body into a fresh name that nothing binds: the source's answer is every
  closed term, where the program means `one`.
* The step (`step_reaches`, `step_answers_one`, `disagree`): it follows the source to the
  non-hygienic alternative; its bind tells the pattern equal to the value without reopening the site,
  so the body's `$x` stays the outer one, and a run of the translated program from the start reaches a
  finished state whose answer is `{one}`.

So without distinct sites the lemma's conclusion fails on a reachable alternative, the source itself
captures a name, and the source and the step disagree.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.ExampleSharedSite

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage SourceLanguage.Elaboration SourceLanguage.Toolkit

abbrev D := untyped.discipline
abbrev N := mettaNodes

/-- No equations. -/
def program : SourceLanguage.Program mkeys [] () MTy := ⟨[], fun t => .apply t⟩

def supply : ℕ → MClosed := fun _ => csym "space"

/-- `$x` and `$y`, both of the site `[7]`. -/
def xShared : MData := foD [] [7] 0
def yShared : MData := foD [] [7] 1

/-- `(let $x one (let $y two $x))`, both arrows at the site `[7]`. -/
def query : Comp mkeys [] () MTy :=
  .let_ [7] xShared (.ret (sym "one")) (.let_ [7] yShared (.ret (sym "two")) (.ret xShared))

/-- The scope clause holds. -/
theorem query_scoped : Comp.Scoped (κ := mkeys) [[100]] query := by decide

/-- The distinctness of sites fails. -/
theorem query_sites_shared : ¬ ([100] :: query.sites ++ program.sites).Nodup := by decide

theorem query_not_wellFormed : ¬ QueryWellFormed program [100] query :=
  fun wf => query_sites_shared wf.distinctSites

/-! ## The run -/

/-- `$x` and `$y` opened at scope `0` by the outer bind; `$y` and `$x` opened again at scope `1` by
the inner bind. -/
def x0 : MData := foD [0] [7] 0
def y0 : MData := foD [0] [7] 1
def x10 : MData := foD [1, 0] [7] 0
def y10 : MData := foD [1, 0] [7] 1

/-- The outer frame and the inner frame (after the outer bind). -/
def outerFrame : SourceLanguage.Frame mkeys [] () MTy :=
  .bindTo [7] xShared (.let_ [7] yShared (.ret (sym "two")) (.ret xShared))
def innerFrame : SourceLanguage.Frame mkeys [] () MTy := .bindTo [7] y0 (.ret x0)

abbrev B1 : Branch mkeys [] () MTy := ⟨[], .eval (.ret (sym "one")), [outerFrame], []⟩
abbrev B2 : Branch mkeys [] () MTy := ⟨[], .value (sym "one"), [outerFrame], []⟩
abbrev B3 : Branch mkeys [] () MTy := ⟨[(x0, sym "one")], .eval (.let_ [7] y0 (.ret (sym "two")) (.ret x0)), [], []⟩
abbrev B4 : Branch mkeys [] () MTy := ⟨[(x0, sym "one")], .eval (.ret (sym "two")), [innerFrame], []⟩
/-- **The non-hygienic alternative.** -/
abbrev B5 : Branch mkeys [] () MTy := ⟨[(x0, sym "one")], .value (sym "two"), [innerFrame], []⟩
abbrev B6 : Branch mkeys [] () MTy := ⟨[(x0, sym "one"), (y10, sym "two")], .eval (.ret x10), [], []⟩
abbrev B7 : Branch mkeys [] () MTy := ⟨[(x0, sym "one"), (y10, sym "two")], .value x10, [], []⟩

abbrev W0 : World mkeys [] () := ⟨0, 0, fun _ => 0⟩
abbrev W1 : World mkeys [] () := ⟨1, 0, fun _ => 0⟩
abbrev W2 : World mkeys [] () := ⟨2, 0, fun _ => 0⟩

def reached : Config mkeys [] () MTy := ⟨W1, {B5}⟩
def final : Config mkeys [] () MTy := ⟨W2, {B7}⟩

/-- A solution of the store, reading the fresh `$x` as `g`. -/
def solution (g : MClosed) : Assignment (fam mkeys) noNames :=
  closeNames [(([0], [7], 0), csym "one"), (([1, 0], [7], 1), csym "two"), (([1, 0], [7], 0), g)] (csym "a")

theorem models_store (g : MClosed) : Models (solution g) [(x0, sym "one"), (y10, sym "two")] := by
  intro e member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> rfl

theorem live_one : Solvable [(x0, sym "one")] :=
  ⟨Empty, noNames, solution (csym "a"), fun e member =>
    models_store (csym "a") e (List.mem_cons.mpr (.inl (List.mem_singleton.mp member)))⟩

theorem live_both : Solvable [(x0, sym "one"), (y10, sym "two")] :=
  ⟨Empty, noNames, solution (csym "a"), models_store (csym "a")⟩

theorem s1 : SourceLanguage.Step D program supply (Config.initial (fun _ => 0) query) ⟨W0, {B1}⟩ :=
  Step.of_eq (rest := 0) rfl (add_zero _).symm live_nil
    (Move.letStart (D := D) (P := program) (supply := supply) W0 [] [7] xShared (.ret (sym "one"))
      (.let_ [7] yShared (.ret (sym "two")) (.ret xShared)) [] [])

theorem s2 : SourceLanguage.Step D program supply ⟨W0, {B1}⟩ ⟨W0, {B2}⟩ :=
  Step.of_eq (rest := 0) rfl (add_zero _).symm live_nil
    (Move.ret (D := D) (P := program) (supply := supply) W0 [] (sym "one") [outerFrame] [])

/-- The outer bind at scope `0` opens the site `[7]`: both `$x` and the inner `$y`. -/
theorem s3 : SourceLanguage.Step D program supply ⟨W0, {B2}⟩ ⟨W1, {B3}⟩ :=
  Step.of_eq (rest := 0) rfl (add_zero _).symm live_nil
    (Move.letBind (D := D) (P := program) (supply := supply) W0 [] (sym "one") [7] xShared
      (.let_ [7] yShared (.ret (sym "two")) (.ret xShared)) [] [])

theorem s4 : SourceLanguage.Step D program supply ⟨W1, {B3}⟩ ⟨W1, {B4}⟩ :=
  Step.of_eq (rest := 0) rfl (add_zero _).symm live_one
    (Move.letStart (D := D) (P := program) (supply := supply) W1 [(x0, sym "one")] [7] y0
      (.ret (sym "two")) (.ret x0) [] [])

theorem s5 : SourceLanguage.Step D program supply ⟨W1, {B4}⟩ reached :=
  Step.of_eq (rest := 0) rfl (add_zero _).symm live_one
    (Move.ret (D := D) (P := program) (supply := supply) W1 [(x0, sym "one")] (sym "two") [innerFrame] [])

theorem runs_to_unhygienic : Runs D program supply (Config.initial (fun _ => 0) query) reached :=
  ((((Relation.ReflTransGen.single s1).tail s2).tail s3).tail s4).tail s5

/-- The inner bind at scope `1` opens the site `[7]` again: the `$x` of its body is renamed. -/
theorem runs_to_final : Runs D program supply reached final := by
  have s6 : SourceLanguage.Step D program supply reached ⟨W2, {B6}⟩ :=
    Step.of_eq (rest := 0) rfl (add_zero _).symm live_one
      (Move.letBind (D := D) (P := program) (supply := supply) W1 [(x0, sym "one")] (sym "two") [7] y0
        (.ret x0) [] [])
  have s7 : SourceLanguage.Step D program supply ⟨W2, {B6}⟩ final :=
    Step.of_eq (rest := 0) rfl (add_zero _).symm live_both
      (Move.ret (D := D) (P := program) (supply := supply) W2 [(x0, sym "one"), (y10, sym "two")] x10 [] [])
  exact (Relation.ReflTransGen.single s6).tail s7

/-- **The alternative the run reaches is not hygienic**: the opened `$x` is of the inner arrow's site,
occurs in its body, and is in the store. -/
theorem not_hygienic : ¬ Hygienic B5 := by
  intro hygienic
  have private' : FramePrivate [7] y0 (.ret x0) [(x0, sym "one")] (sym "two")
      ([] : List (SourceLanguage.Frame mkeys [] () MTy)) :=
    hygienic _ _ _ _ _ _ _ rfl
  let one : Assignment (fam mkeys) noNames := closeNames [] (csym "one")
  let two : Assignment (fam mkeys) noNames := closeNames [(([0], [7], 0), csym "two")] (csym "one")
  obtain ⟨onStore, _, _⟩ := private' one two (by
    intro y notOwn
    rcases y with ⟨scopes, ⟨site, index, ⟨Δ, u⟩⟩⟩
    cases u
    cases Δ with
    | cons _ _ => rfl
    | nil =>
        by_cases hit : scopes = [0] ∧ site = [7] ∧ index = 0
        · obtain ⟨rfl, rfl, rfl⟩ := hit
          exact absurd ⟨rfl, .inr ⟨x0, List.mem_singleton_self _, List.mem_singleton_self _⟩⟩ notOwn
        · simp only [one, two, closeNames, List.lookup]
          split
          · rename_i heq
            simp only [beq_iff_eq, Prod.mk.injEq] at heq
            exact absurd heq hit
          · rfl)
  have := (onStore _ (List.mem_singleton_self _)).1
  change Rigid.includeTerm noNames (csym "one") = Rigid.includeTerm noNames (csym "two") at this
  have := Rigid.include_injective _ _ _ this
  simp [csym] at this

/-- **The capture**: the answer at the end is every closed term. -/
theorem final_answers : Config.answers (D := D) final = {Set.univ} := by
  have finished : Branch.Finished (D := D) B7 := ⟨rfl, _, rfl⟩
  show Config.answers (D := D) ⟨W2, {B7}⟩ = _
  rw [answers_singleton finished live_both]
  congr 1
  ext g
  simp only [Set.mem_univ, iff_true]
  refine ⟨x10, rfl, Empty, noNames, solution g, models_store g, ?_⟩
  rw [x10, instantiate_foD]
  rfl

/-! ## The step -/

theorem query_arrows : ArrowComp query := ⟨trivial, trivial, trivial⟩

theorem query_unopened : ∀ t ∈ query.data, ∀ x ∈ support t, x.scopes = [] := by decide

theorem program_arrows : ArrowProgram program := fun _ member => nomatch member

theorem hygienic_eval {b : Branch mkeys [] () MTy} {c : Comp mkeys [] () MTy} (focus : b.focus = .eval c) :
    Hygienic b := by
  intro K v s p k fs ps same
  subst same
  cases focus

/-- The outer bind is hygienic: the store is empty and the value closed. -/
theorem outer_private :
    FramePrivate [7] xShared (.let_ [7] yShared (.ret (sym "two")) (.ret xShared)) [] (sym "one")
      ([] : List (SourceLanguage.Frame mkeys [] () MTy)) := by
  intro W target σ σ' _
  refine ⟨?_, rfl, ?_⟩
  · intro e member
    cases member
  · intro fr member
    cases member

open Classical in
/-- **The step follows the source to the non-hygienic alternative.** -/
theorem step_reaches :
    ∃ (s : HostState MSig) (a : ℕ), Relation.ReflTransGen (Fires N program) (Hosting.start N program query) s ∧
      Represents N program 1 B5 s a := by
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
    exact hygienic_eval focus
  obtain ⟨L1, f1, r1⟩ := arrowFrontier_reached_step N program_arrows f0 r0 (single rfl W0) s1
  obtain ⟨L2, f2, r2⟩ := arrowFrontier_reached_step N program_arrows f1 r1 (single rfl W0) s2
  have hygienic2 : ∀ b ∈ (⟨W0, {B2}⟩ : Config mkeys [] () MTy).branches, Hygienic b := by
    intro b member
    rw [Multiset.mem_singleton.mp member]
    intro K v s p k fs ps same
    cases same
    exact outer_private
  obtain ⟨L3, f3, r3⟩ := arrowFrontier_reached_step N program_arrows f2 r2 hygienic2 s3
  obtain ⟨L4, f4, r4⟩ := arrowFrontier_reached_step N program_arrows f3 r3 (single rfl W1) s4
  obtain ⟨L5, f5, r5⟩ := arrowFrontier_reached_step N program_arrows f4 r4 (single rfl W1) s5
  have inside : B5 ∈ L5.map Prod.fst := by
    rw [f5.branches]
    exact Multiset.mem_filter.mpr ⟨Multiset.mem_singleton_self _, live_one⟩
  obtain ⟨x, member, first⟩ := Multiset.mem_map.mp inside
  have rep := (f5.represents x member).1
  rw [first] at rep
  exact ⟨x.2.1, x.2.2, r5 x member, rep⟩

/-- What the step's bind makes: `$y` bound to `two` in place, the body reading the outer `$x`. -/
abbrev V6 : Branch mkeys [] () MTy := ⟨[(x0, sym "one"), (y0, sym "two")], .eval (.ret x0), [], []⟩
abbrev V7 : Branch mkeys [] () MTy := ⟨[(x0, sym "one"), (y0, sym "two")], .value x0, [], []⟩

def σ6 : Assignment (fam mkeys) noNames := closeNames [(([0], [7], 0), csym "one"), (([0], [7], 1), csym "two")] (csym "a")

theorem live6 : Solvable V6.store :=
  ⟨Empty, noNames, σ6, fun e member => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl⟩

/-- The rule's bind at the non-hygienic alternative transforms its readings into those of `V6`. -/
theorem transfer6 {B : Interface.Frames.Frame MSig} (q : Observation MSig B.arity) :
    (∃ h : Assignment (unknownArity [] ()) B.arity,
      branchReads N B5 B (instantiateObservation h (bindValuePattern N)) ∧
      (Interface.Frames.contextual MSig).Models (a := controlFrame [] ()) (b := B) h
        (bindValueTell (S := MSig) (Γ := []) (star := ())) ∧
      instantiateObservation h (bindValueMade N) = q) ↔
    branchReads N V6 B q := by
  refine (bindValue_rule_side N (K := [(x0, sym "one")]) (v := sym "two") (s := [7]) (p := y0) (k := .ret x0)
    (fs := []) (ps := []) q).trans ?_
  constructor
  · rintro ⟨σ, solved, matched, rfl⟩
    refine ⟨σ, ?_, rfl⟩
    intro e member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact solved _ (List.mem_singleton_self _)
    · exact matched
  · rintro ⟨σ, solved, rfl⟩
    exact ⟨σ, fun e member => solved e (List.mem_cons.mpr (.inl (List.mem_singleton.mp member))),
      solved _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)), rfl⟩

theorem below_name {n : ℕ} (scopes site : List ℕ) (index : ℕ) (head : ∀ m, scopes.head? = some m → m < n) :
    DependsBelow n (foD scopes site index) := by
  intro W target σ σ' agree
  rw [instantiate_foD, instantiate_foD]
  exact agree _ head

theorem fresh6 : BranchBelow 1 V6 := by
  have bx : DependsBelow 1 x0 := below_name [0] [7] 0 (fun m head => by simp at head; omega)
  have by' : DependsBelow 1 y0 := below_name [0] [7] 1 (fun m head => by simp at head; omega)
  refine ⟨?_, ?_, ?_⟩
  · intro e member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨bx, fun _ _ _ => rfl⟩
    · exact ⟨by', fun _ _ _ => rfl⟩
  · intro t member
    simp only [focusData, Comp.data, List.mem_singleton] at member
    subst member
    exact bx
  · intro fr member
    cases member

theorem determines7 : Determines V7.store x0 (csym "one") :=
  ⟨live6, fun _ _ solved => solved _ (List.mem_cons_self ..)⟩

/-- **The step answers `one`**: a run of the translated program from the start reaches a finished
state whose answer is `{one}`. -/
theorem step_answers_one :
    ∃ s a, Relation.ReflTransGen (Fires N program) (Hosting.start N program query) s ∧
      StateFinished N s a ∧ stateAnswer N s a = {csym "one"} := by
  obtain ⟨s5, a5, run5, rep5⟩ := step_reaches
  obtain ⟨s6, a6, fires6, rep6⟩ := fire_simple N (bindValueRule_mem N program) rfl rfl rfl rfl rep5
    (fun _ q => transfer6 q) live6 (entails_of_no_checks rfl rfl) fresh6 rfl
  have move : Move D program supply ⟨1, 0, fun _ => 0⟩ V6 ⟨1, 0, fun _ => 0⟩ {V7} :=
    .ret _ [(x0, sym "one"), (y0, sym "two")] x0 [] []
  obtain ⟨s7, a7, fires7, rep7, _⟩ := simulation_arrows N (D := D) program_arrows move rep6
    ⟨trivial, .inl ⟨_, rfl, trivial⟩⟩ (hygienic_eval rfl) (Multiset.mem_singleton_self _) live6
  have finished : Branch.Finished (D := D) V7 := ⟨rfl, _, rfl⟩
  refine ⟨s7, a7, (run5.tail fires6).tail fires7, (finished_iff N (D := D) rep7).mp ⟨finished, live6⟩, ?_⟩
  rw [answer_eq N (D := D) rep7 finished, answer_of_determines rfl determines7]

/-- **The two disagree**: the source's bag is every closed term, while a run of the step answers `one`. -/
theorem disagree : Config.answers (D := D) final = {Set.univ} ∧ ({csym "one"} : Set MClosed) ≠ Set.univ := by
  refine ⟨final_answers, fun same => ?_⟩
  have : csym "two" ∈ ({csym "one"} : Set MClosed) := same ▸ Set.mem_univ _
  simp [csym] at this

#print axioms query_scoped
#print axioms query_sites_shared
#print axioms runs_to_unhygienic
#print axioms not_hygienic
#print axioms runs_to_final
#print axioms final_answers
#print axioms step_reaches
#print axioms transfer6
#print axioms step_answers_one
#print axioms disagree

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.ExampleSharedSite
