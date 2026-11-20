import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Divergence.Preserved

/-!
# Divergence and termination: one program for each

* **A program that diverges.** `(= (loop) (loop))` with the query `(loop)`: the source has an infinite
  run (`source_diverges`: after `k` calls the one alternative's store holds `k` trivial equations), so
  the translated program has an infinite run from its start (`step_diverges`, by
  `divergence_preserved`; `step_diverges_arrow`, by `arrow_divergence_preserved` under the clauses of
  the fragment with `let`, which the program and the query satisfy: `loop_scoped`).
* **A program that terminates.** No equation and the query `ret d`: the translated program has no
  infinite run from its start (`ret_terminates`), so the source has none from the query
  (`ret_source_terminates`, by `source_terminates`).
* **A step that no state follows at the relation `TracksPlain`** (`no_forward_at_fail`): the query
  `fail`. The relation between a configuration and a state that represents one of its alternatives
  relates nothing to a configuration without alternatives, so it has no forward law there; another
  relation has both halves at the same query (`OneAnswer.failCorrespondence`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Divergence.Examples

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage SourceLanguage.Elaboration SourceLanguage.Toolkit
open Classical

/-- The trivial discipline, with its type language on the nose. -/
abbrev D : Discipline MSig [] () := ⟨MTy, fun _ _ => True⟩
abbrev N := mettaNodes

def supply : ℕ → MClosed := fun _ => csym "space"
abbrev sp : MClosed → Multiset (Row mkeys [] ()) := fun _ => 0

/-! ## A program that diverges -/

def loopT : MData := tuple [sym "loop"]

/-- `(= (loop) (loop))`. -/
def eLoop : SourceLanguage.Equation mkeys [] () MTy := ⟨[310], loopT, .apply loopT⟩
def program : SourceLanguage.Program mkeys [] () MTy := ⟨[eLoop], fun t => .apply t⟩

/-- The query `(loop)`, called. -/
def query : Comp mkeys [] () MTy := .apply loopT

/-- The configuration after `k` calls: one alternative, whose store holds `k` trivial equations. -/
def run (k : ℕ) : Config mkeys [] () MTy :=
  ⟨⟨k, 0, sp⟩, {⟨List.replicate k (loopT, loopT), .eval (.apply loopT), [], []⟩}⟩

theorem live (k : ℕ) : Solvable (List.replicate k (loopT, loopT) : List (Constraint mkeys [] ())) :=
  ⟨Empty, noNames, closeNames [] (csym "a"), fun e member => by rw [List.eq_of_mem_replicate member]⟩

theorem run_step (k : ℕ) : SourceLanguage.Step D program supply (run k) (run (k + 1)) := by
  have matched : ∃ e ∈ program.equations, Solvable (List.replicate k (loopT, loopT) ++
      [(instantiate (copyAt mkeys (⟨k, 0, sp⟩ : World mkeys [] ()).scope) e.lhs, loopT)]) := by
    refine ⟨eLoop, List.mem_singleton_self _, ?_⟩
    show Solvable (List.replicate k (loopT, loopT) ++ [(loopT, loopT)])
    rw [← List.replicate_succ']
    exact live (k + 1)
  have step := Step.single (D := D) (P := program) (supply := supply) (live k)
    (Move.apply ⟨k, 0, sp⟩ (List.replicate k (loopT, loopT)) loopT [] [] matched)
  have same : run (k + 1) =
      ⟨⟨k + 1, 0, sp⟩, {⟨List.replicate k (loopT, loopT) ++ [(loopT, loopT)], .eval (.apply loopT), [], []⟩}⟩ := by
    unfold run
    rw [List.replicate_succ']
  rw [same]
  exact step

/-- **The source diverges** from the query `(loop)`. -/
theorem source_diverges : ∃ run : ℕ → Config mkeys [] () MTy, run 0 = Config.initial sp query ∧
    ∀ k, SourceLanguage.Step D program supply (run k) (run (k + 1)) :=
  ⟨run, rfl, run_step⟩

theorem query_unopened : ∀ t ∈ query.data, ∀ x ∈ support t, x.scopes = [] := by
  intro t member x inside
  simp only [query, Comp.data, List.mem_singleton] at member
  subst member
  simp [loopT, tuple, tupleArgs, sym, support, supportArgs] at inside

theorem plainProgram : PlainProgram program := by
  intro e member
  rw [List.mem_singleton.mp member]
  trivial

/-- **So the translated program diverges from its start** (the first fragment). -/
theorem step_diverges : ∃ f : ℕ → HostState MSig, f 0 = Hosting.start N program query ∧
    ∀ k, Fires N program (f k) (f (k + 1)) :=
  divergence_preserved N (D := D) (supply := supply) sp query plainProgram trivial query_unopened run rfl run_step

/-- The program and the query satisfy the clauses of the run theorems of the fragment with `let`. -/
theorem loop_scoped :
    (∀ e ∈ program.equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs) ∧
    query.Scoped [[311]] ∧ (([311] : List ℕ) :: query.sites).Nodup ∧ ArrowComp query := by
  refine ⟨?_, by decide, by decide, trivial⟩
  intro e member
  rw [List.mem_singleton.mp member]
  exact ⟨by decide, by decide, trivial⟩

/-- **So the translated program diverges from its start** (the fragment with `let`). -/
theorem step_diverges_arrow : ∃ f : ℕ → HostState MSig, f 0 = Hosting.start N program query ∧
    ∀ k, Fires N program (f k) (f (k + 1)) :=
  arrow_divergence_preserved N (D := D) (supply := supply) sp query loop_scoped.1 loop_scoped.2.1
    loop_scoped.2.2.1 loop_scoped.2.2.2 run rfl run_step

/-! ## A program that terminates -/

def dT : MData := sym "d"

/-- No equations. -/
def empty : SourceLanguage.Program mkeys [] () MTy := ⟨[], fun t => .apply t⟩

/-- The query `d`, returned. -/
def returned : Comp mkeys [] () MTy := .ret dT

theorem returned_unopened : ∀ t ∈ returned.data, ∀ x ∈ support t, x.scopes = [] := by
  intro t member x inside
  simp only [returned, Comp.data, List.mem_singleton] at member
  subst member
  simp [dT, sym, support, supportArgs] at inside

theorem plainEmpty : PlainProgram empty := fun _ member => by cases member

/-- The only move of the alternative that returns `d` makes the alternative with the value `d`. -/
theorem move_returned {w w' : World mkeys [] ()} {b : Branch mkeys [] () D.Ty}
    {bs : Multiset (Branch mkeys [] () D.Ty)} (move : Move D empty supply w b w' bs)
    (hb : b = ⟨[], .eval (.ret dT), [], []⟩) : ∀ b' ∈ bs, b' = ⟨[], .value dT, [], []⟩ := by
  cases move <;> cases hb
  intro b' made
  exact Multiset.mem_singleton.mp made

/-- **The translated program terminates** from the start of the query `ret d`: one firing, and then
none. -/
theorem ret_terminates : Acc (fun s' s => Fires N empty s s') (Hosting.start N empty returned) := by
  refine Acc.intro _ fun s' fires => ?_
  obtain ⟨w', bs, b', a', move, child, rep', plain'⟩ :=
    reflection N (D := D) (supply := supply) (w := ⟨0, 0, sp⟩) plainEmpty
      (start_represents N empty returned returned_unopened) ⟨rfl, .inl ⟨returned, rfl, trivial⟩⟩ fires
  refine Acc.intro _ fun s'' fires' => ?_
  have finished : b'.Finished (D := D) := by
    rw [move_returned move rfl b' child]
    exact ⟨rfl, _, rfl⟩
  exact absurd fires' (finished_still N (supply := supply) plainEmpty rep' plain' finished)

/-- **So the source terminates** from the query `ret d`. -/
theorem ret_source_terminates :
    Acc (fun C' C => SourceLanguage.Step D empty supply C C') (Config.initial sp returned) :=
  source_terminates N (D := D) (supply := supply) sp returned plainEmpty
    (show PlainComp (Comp.ret dT) from trivial) returned_unopened ret_terminates

/-! ## The configuration-level relation has no forward law -/

/-- **A step that no state follows at the relation `TracksPlain`**: the start of the query `fail`
tracks its initial configuration; the source steps to the configuration with no alternative; and no
state tracks that configuration, since `TracksPlain` relates a state to a configuration only through one
of its alternatives. This is a property of the relation. The reason the forward half of the hosting,
configuration by configuration, is a frontier of several states and not one state is that a reachable
state shows at most one answer (`OneAnswer.no_state_shows_both`). -/
theorem no_forward_at_fail :
    TracksPlain (D := D) N empty (Config.initial sp (.fail : Comp mkeys [] () MTy))
      (Hosting.start N empty .fail) ∧
    SourceLanguage.Step D empty supply (Config.initial sp (.fail : Comp mkeys [] () MTy)) ⟨⟨0, 0, sp⟩, 0⟩ ∧
    ∀ s : HostState MSig, ¬ TracksPlain (D := D) N empty (⟨⟨0, 0, sp⟩, 0⟩ : Config mkeys [] () MTy) s := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨initialBranch .fail, _, Multiset.mem_singleton_self _, start_represents N empty .fail ?_, rfl,
      .inl ⟨.fail, rfl, trivial⟩⟩
    intro t member
    cases member
  · exact step_one live_nil (.fail ⟨0, 0, sp⟩ [] [] [])
  · rintro s ⟨b, a, member, _⟩
    exact absurd member (Multiset.notMem_zero b)

#print axioms no_forward_at_fail
#print axioms source_diverges
#print axioms step_diverges
#print axioms loop_scoped
#print axioms step_diverges_arrow
#print axioms ret_terminates
#print axioms ret_source_terminates

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Divergence.Examples
