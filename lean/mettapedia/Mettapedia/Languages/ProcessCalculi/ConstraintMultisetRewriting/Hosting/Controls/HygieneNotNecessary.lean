import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.ArrowRuns

/-!
# Hygiene is sufficient for a bind, and not necessary; a `let` program on the hygienic run theorem

* **Hygiene is sufficient, not the exact condition.** A frame whose store mentions the frame's own
  name harmlessly (`x = x`) is not hygienic (`not_private`), and the rule's bind still transforms
  readings exactly as the source's bind (`transfer_holds`): the equivalence that `transfer_bindValue`
  proves for hygienic frames holds here without hygiene. So `FramePrivate` is not necessary for the
  bind's correspondence; `hygiene_needed` shows only that some condition is.
* **A program with a `let` on which the hygienic run theorem applies.** The well-formed program
  `(= (g) d)` and the query `let y = (g) in (pair y y)` (`Q_wellFormed`, `letQ_scoped`): every
  alternative a run reaches is hygienic (`letQ_hygienic`, by a complete description of the reachable
  alternatives, `inv8_runs`), so `arrow_runs_forward_of_hygienic` applies: the run that ends with the
  bag `{(pair d d)}` has a frontier of states reached by the step of the translated program, with the
  same bag (`let_query_hosted`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Controls.HygieneNotNecessary

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open SourceLanguage SourceLanguage.Elaboration SourceLanguage.Toolkit
open Hosting
open Classical

/-- The trivial discipline, with its type language on the nose. -/
abbrev D : Discipline MSig [] () := ⟨MTy, fun _ _ => True⟩
abbrev N := mettaNodes

def supply : ℕ → MClosed := fun _ => csym "space"
abbrev sp : MClosed → Multiset (Row mkeys [] ()) := fun _ => 0

/-! ## Hygiene is sufficient, not necessary -/

/-- The name `x` of the site `[7]`, unopened. -/
abbrev x7 : MData := foD [] [7] 0
def oneT : MData := sym "one"

/-- A store that mentions the frame's own name harmlessly. -/
abbrev K7 : List (Constraint mkeys [] ()) := [(x7, x7)]

/-- The alternative: value `one` returned to the frame `let x = □ in (ret x)`, store `x = x`. -/
abbrev alt7 : Branch mkeys [] () MTy := ⟨K7, .value oneT, [.bindTo [7] x7 (.ret x7)], []⟩

/-- What the source's bind at scope `0` makes of it. -/
abbrev child7 : Branch mkeys [] () MTy :=
  ⟨K7 ++ [(instantiate (openAt mkeys [7] 0) x7, oneT)], .eval ((Comp.ret x7).inst (openAt mkeys [7] 0)), [], []⟩

/-- **The frame is not hygienic**: its store depends on its own name. -/
theorem not_private :
    ¬ FramePrivate [7] x7 (.ret x7) K7 oneT ([] : List (SourceLanguage.Frame mkeys [] () MTy)) := by
  intro private'
  let σa : Assignment (fam mkeys) noNames := closeNames [] (csym "two")
  let σb : Assignment (fam mkeys) noNames := closeNames [(([], [7], 0), csym "one")] (csym "two")
  obtain ⟨onStore, _, _⟩ := private' σa σb (by
    intro y notOwn
    rcases y with ⟨scopes, ⟨site, index, ⟨Δ, u⟩⟩⟩
    cases u
    cases Δ with
    | cons _ _ => rfl
    | nil =>
        by_cases hit : scopes = [] ∧ site = [7] ∧ index = 0
        · obtain ⟨rfl, rfl, rfl⟩ := hit
          exact absurd ⟨rfl, .inl (by decide)⟩ notOwn
        · simp only [σa, σb, closeNames, List.lookup]
          split
          · rename_i heq
            simp only [beq_iff_eq, Prod.mk.injEq] at heq
            exact absurd heq hit
          · rfl)
  have := (onStore _ (List.mem_singleton_self _)).1
  change Rigid.includeTerm noNames (csym "two") = Rigid.includeTerm noNames (csym "one") at this
  have := Rigid.include_injective _ _ _ this
  simp [csym] at this

theorem below_x7 : DependsBelow 0 x7 := by
  intro W target σ σ' agree
  rw [instantiate_foD, instantiate_foD]
  exact agree _ (fun m head => by simp at head)

theorem below_one : DependsBelow 0 oneT := fun _ _ _ => rfl

theorem fresh7 : BranchBelow 0 alt7 := by
  refine ⟨?_, ?_, ?_⟩
  · intro e member
    simp only [List.mem_singleton] at member
    subst member
    exact ⟨below_x7, below_x7⟩
  · intro t member
    simp only [focusData, List.mem_singleton] at member
    subst member
    exact below_one
  · intro fr member t inside
    simp only [List.mem_singleton] at member
    subst member
    simp only [frameData, Comp.data, List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl <;> exact below_x7

/-- **Without hygiene, the rule's bind still transforms readings exactly as the source's bind.** -/
theorem transfer_holds {B : Interface.Frames.Frame MSig} (q : Observation MSig B.arity) :
    (∃ h : Assignment (unknownArity [] ()) B.arity,
      branchReads N alt7 B (instantiateObservation h (bindValuePattern N)) ∧
      (Interface.Frames.contextual MSig).Models (a := controlFrame [] ()) (b := B) h
        (bindValueTell (S := MSig) (Γ := []) (star := ())) ∧
      instantiateObservation h (bindValueMade N) = q) ↔
    branchReads N child7 B q := by
  rw [bindValue_rule_side N q]
  constructor
  · rintro ⟨σ, solved, matched, rfl⟩
    exact bindValue_forward N fresh7 solved matched
  · rintro ⟨σ', solved', rfl⟩
    refine ⟨fun y => instantiate σ' (openAt mkeys [7] 0 y), ?_, ?_, ?_⟩
    · intro e member
      simp only [List.mem_singleton] at member
      subst member
      rfl
    · have bound := solved' _ (List.mem_append_right _ (List.mem_singleton_self _))
      change instantiate σ' (instantiate (openAt mkeys [7] 0) x7) = instantiate σ' oneT at bound
      rw [← instantiate_comp (openAt mkeys [7] 0) σ' x7, bound]
      rfl
    · change observe (N.node .alt ![N.node .eval ![N.node .ret
          ![instantiate σ' (instantiate (openAt mkeys [7] 0) x7)]], N.node .empty ![]]) =
        observe (N.node .alt ![N.node .eval ![N.node .ret
          ![instantiate (fun y => instantiate σ' (openAt mkeys [7] 0 y)) x7]], N.node .empty ![]])
      rw [instantiate_comp (openAt mkeys [7] 0) σ' x7]

/-! ## A well-formed program with a `let`, hosted for whole runs -/

def gT : MData := tuple [sym "g"]
def dT : MData := sym "d"

/-- `(= (g) d)` -/
def eg : SourceLanguage.Equation mkeys [] () MTy := ⟨[300], gT, .ret dT⟩
def Q : SourceLanguage.Program mkeys [] () MTy := ⟨[eg], fun t => .apply t⟩

abbrev y8 : MData := foD [] [8] 0
def pairYY : MData := tuple [sym "pair", y8, y8]

/-- `let y = (g) in (pair y y)`, the call's value bound first. -/
def letQ : Comp mkeys [] () MTy := .let_ [8] y8 (.apply gT) (.ret pairYY)

theorem Q_wellFormed : WellFormed Q := by decide

/-- The scope and site clauses of a well-formed query. -/
theorem letQ_scoped : letQ.Scoped [[3]] ∧ ([3] :: letQ.sites ++ Program.sites Q).Nodup := by decide

abbrev fr8 : SourceLanguage.Frame mkeys [] () MTy := .bindTo [8] y8 (.ret pairYY)

abbrev A0 : Branch mkeys [] () MTy := ⟨[], .eval (.let_ [8] y8 (.apply gT) (.ret pairYY)), [], []⟩
abbrev A1 : Branch mkeys [] () MTy := ⟨[], .eval (.apply gT), [fr8], []⟩
abbrev A2 : Branch mkeys [] () MTy := ⟨[(gT, gT)], .eval (.ret dT), [fr8], []⟩
abbrev A3 : Branch mkeys [] () MTy := ⟨[(gT, gT)], .value dT, [fr8], []⟩
abbrev A4 (n : ℕ) : Branch mkeys [] () MTy :=
  ⟨[(gT, gT)] ++ [(instantiate (openAt mkeys [8] n) y8, dT)], .eval ((Comp.ret pairYY).inst (openAt mkeys [8] n)), [], []⟩
abbrev A5 (n : ℕ) : Branch mkeys [] () MTy :=
  ⟨[(gT, gT)] ++ [(instantiate (openAt mkeys [8] n) y8, dT)], .value (instantiate (openAt mkeys [8] n) pairYY), [], []⟩

/-- The reachable alternatives, all of them. -/
def Inv8 (C : Config mkeys [] () MTy) : Prop :=
  ∀ b ∈ C.branches, b = A0 ∨ b = A1 ∨ b = A2 ∨ b = A3 ∨ ∃ n, b = A4 n ∨ b = A5 n

theorem callBranch_g (n : ℕ) : callBranch D n [] gT [fr8] [] eg = A2 := rfl

theorem live_gg : Solvable ([(gT, gT)] : List (Constraint mkeys [] ())) :=
  ⟨Empty, noNames, closeNames [] (csym "a"), fun e member => by
    simp only [List.mem_singleton] at member
    subst member
    rfl⟩

section Moves

variable {w w' : World mkeys [] ()} {b : Branch mkeys [] () D.Ty} {bs : Multiset (Branch mkeys [] () D.Ty)}

theorem move_A0 (move : Move D Q supply w b w' bs) (hb : b = A0) : ∀ b' ∈ bs, b' = A1 := by
  cases move <;> cases hb
  intro b' made
  exact Multiset.mem_singleton.mp made

theorem move_A1 (move : Move D Q supply w b w' bs) (hb : b = A1) : ∀ b' ∈ bs, b' = A2 := by
  cases move <;> cases hb
  · intro b' made
    change b' ∈ (([callBranch D w.scope [] gT [fr8] [] eg] : List (Branch mkeys [] () MTy)) :
      Multiset (Branch mkeys [] () MTy)) at made
    simp only [Multiset.coe_singleton, Multiset.mem_singleton] at made
    rw [made, callBranch_g]
  · rename_i none
    exact absurd (show Solvable ([] ++ [(instantiate (copyAt mkeys w.scope) eg.lhs, gT)]) from live_gg)
      (none eg (List.mem_singleton_self _))

theorem move_A2 (move : Move D Q supply w b w' bs) (hb : b = A2) : ∀ b' ∈ bs, b' = A3 := by
  cases move <;> cases hb
  intro b' made
  exact Multiset.mem_singleton.mp made

theorem move_A3 (move : Move D Q supply w b w' bs) (hb : b = A3) : ∀ b' ∈ bs, b' = A4 w.scope := by
  cases move <;> cases hb
  intro b' made
  exact Multiset.mem_singleton.mp made

theorem move_A4 {n : ℕ} (move : Move D Q supply w b w' bs) (hb : b = A4 n) : ∀ b' ∈ bs, b' = A5 n := by
  cases move <;> cases hb
  intro b' made
  exact Multiset.mem_singleton.mp made

end Moves

theorem inv8_step {C C' : Config mkeys [] () MTy} (inv : Inv8 C) (step : SourceLanguage.Step D Q supply C C') :
    Inv8 C' := by
  obtain ⟨w, w', b, rest, bs, _, move⟩ := step
  have bShape := inv b (Multiset.mem_cons_self _ _)
  intro b' member
  rcases Multiset.mem_add.mp member with made | kept
  · rcases bShape with hb | hb | hb | hb | ⟨n, hb | hb⟩
    · exact .inr (.inl (move_A0 move hb b' made))
    · exact .inr (.inr (.inl (move_A1 move hb b' made)))
    · exact .inr (.inr (.inr (.inl (move_A2 move hb b' made))))
    · exact .inr (.inr (.inr (.inr ⟨w.scope, .inl (move_A3 move hb b' made)⟩)))
    · exact .inr (.inr (.inr (.inr ⟨n, .inr (move_A4 move hb b' made)⟩)))
    · subst hb
      exact absurd move Move.value_still
  · exact inv b' (Multiset.mem_cons_of_mem kept)

theorem inv8_runs {C : Config mkeys [] () MTy} (runs : Runs D Q supply (Config.initial sp letQ) C) : Inv8 C := by
  induction runs with
  | refl =>
      intro b member
      exact .inl (Multiset.mem_singleton.mp member)
  | tail _ step ih => exact inv8_step ih step

/-- The one frame a value meets is hygienic: its store and value are closed. -/
theorem private8 : FramePrivate [8] y8 (.ret pairYY) [(gT, gT)] dT ([] : List (SourceLanguage.Frame mkeys [] () MTy)) :=
  fun _ _ _ => ⟨fun e member => by
    simp only [List.mem_singleton] at member
    subst member
    exact ⟨rfl, rfl⟩, rfl, fun _ member => by cases member⟩

/-- **Every alternative every run of the query reaches is hygienic.** -/
theorem letQ_hygienic : ReachableHygienic (D := D) sp letQ Q supply := by
  intro C runs b member K v s p k fs ps same
  rcases inv8_runs runs b member with rfl | rfl | rfl | rfl | ⟨n, rfl | rfl⟩
  · cases same
  · cases same
  · cases same
  · cases same
    exact private8
  · cases same
  · cases same

/-! ## The run, its bag, and the frontier the theorem gives -/

def pairDD : MClosed := ctuple [csym "pair", csym "d", csym "d"]

def final8 : Config mkeys [] () MTy := ⟨⟨2, 0, sp⟩, {A5 1}⟩

theorem store_live : Solvable ([(gT, gT)] ++ [(instantiate (openAt mkeys [8] 1) y8, dT)] : List (Constraint mkeys [] ())) :=
  ⟨Empty, noNames, closeNames [(([1], [8], 0), csym "d")] (csym "a"), fun e member => by
    simp only [List.mem_append, List.mem_singleton] at member
    rcases member with rfl | rfl <;> rfl⟩

theorem runs8 : Runs D Q supply (Config.initial sp letQ) final8 := by
  have m1 : ∃ e ∈ Q.equations, Solvable ([] ++ [(instantiate (copyAt mkeys 0) e.lhs, gT)]) :=
    ⟨eg, List.mem_singleton_self _, live_gg⟩
  refine Relation.ReflTransGen.tail (b := ⟨⟨2, 0, sp⟩, {A4 1}⟩) ?_
    (step_one store_live (.ret _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨1, 0, sp⟩, {A3}⟩) ?_
    (step_one live_gg (.letBind _ _ _ _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨1, 0, sp⟩, {A2}⟩) ?_
    (step_one live_gg (.ret _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨0, 0, sp⟩, {A1}⟩) ?_
    (Step.of_eq (rest := 0) rfl rfl live_nil (.apply _ _ _ _ _ m1))
  exact Relation.ReflTransGen.single (step_one live_nil (.letStart _ _ _ _ _ _ _ _))

theorem determines8 : Determines ([(gT, gT)] ++ [(instantiate (openAt mkeys [8] 1) y8, dT)])
    (instantiate (openAt mkeys [8] 1) pairYY) pairDD := by
  refine ⟨store_live, fun target σ solved => ?_⟩
  have bound := solved _ (List.mem_append_right _ (List.mem_singleton_self _))
  change instantiate σ (foD [1] [8] 0) = instantiate σ dT at bound
  rw [instantiate_foD] at bound
  show tupleAt [symAt "pair", instantiate σ (foD [1] [8] 0), instantiate σ (foD [1] [8] 0)] = _
  rw [instantiate_foD, bound]
  rfl

theorem final8_answers : Config.answers (D := D) final8 = {{pairDD}} := by
  show Config.answers (D := D) ⟨⟨2, 0, sp⟩, {A5 1}⟩ = _
  rw [answers_singleton (D := D) ⟨rfl, _, rfl⟩ store_live, answer_of_determines rfl determines8]

theorem final8_quiescent : Config.Quiescent (D := D) Q supply final8 :=
  Config.quiescent_of_finished fun b member _ => by
    rw [Multiset.mem_singleton.mp member]
    exact ⟨rfl, _, rfl⟩

theorem arrowQ : ArrowComp letQ := ⟨trivial, trivial⟩

theorem arrowP : ArrowProgram Q := by
  intro e member
  rw [List.mem_singleton.mp member]
  trivial

theorem letQ_unopened : ∀ t ∈ letQ.data, ∀ x ∈ support t, x.scopes = [] := by
  have hy : NamesIn [[8]] y8 := by decide
  have hp : NamesIn [[8]] pairYY := by decide
  have hg : NamesIn [[8]] gT := by decide
  intro t member x inside
  simp only [letQ, Comp.data, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact (hy x inside).1
  · exact (hg x inside).1
  · exact (hp x inside).1

/-- **The hygienic run theorem at a program with a `let`.** The run of the query
`let y = (g) in (pair y y)` ends, quiescent, with the bag `{(pair d d)}`; through the translation,
that configuration has a frontier of states reached by the step's runs from the start, with the same
bag. -/
theorem let_query_hosted :
    Runs D Q supply (Config.initial sp letQ) final8 ∧ Config.Quiescent (D := D) Q supply final8 ∧
      Config.answers (D := D) final8 = {{pairDD}} ∧
      ∃ L, ArrowFrontier (D := D) N Q final8 L ∧
        (∀ x ∈ L, Relation.ReflTransGen (Fires N Q) (Hosting.start N Q letQ) x.2.1) ∧
        frontierAnswers N L = {{pairDD}} := by
  obtain ⟨L, frontier, reached⟩ := arrow_runs_forward_of_hygienic N (D := D) (P := Q) (supply := supply)
    sp letQ arrowP arrowQ letQ_unopened letQ_hygienic runs8
  exact ⟨runs8, final8_quiescent, final8_answers, L, frontier, reached,
    (arrowFrontier_answers N frontier).symm.trans final8_answers⟩

#print axioms not_private
#print axioms transfer_holds
#print axioms Q_wellFormed
#print axioms letQ_scoped
#print axioms letQ_hygienic
#print axioms let_query_hosted

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Controls.HygieneNotNecessary
