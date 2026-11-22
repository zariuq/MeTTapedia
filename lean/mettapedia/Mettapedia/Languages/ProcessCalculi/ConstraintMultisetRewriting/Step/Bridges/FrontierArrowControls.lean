import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.FrontierArrowFunctionVariables
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Answers.Bags

/-!
# Rejected binds, pending probes, and duplicate equations behind sequencing

A rejected bind is an ordinary source step, advancing scope and producing a
dead child. Its native controller expansion is empty and retires the parent.
A pending probe cannot claim that result. Duplicate equation ordinals remain
two alternatives even after entering through a let continuation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierArrow.Controls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage SourceLanguage.Elaboration SourceLanguage.Toolkit Hosting Hosting.Answers.Bags
open Classical

private theorem equations1 : ∀ e ∈ P1.equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs := by
  intro e member
  rw [show P1.equations = [eqF] from rfl, List.mem_singleton] at member
  subst e
  exact ⟨by decide, by decide, trivial⟩

private theorem equations2 : ∀ e ∈ P2.equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs := by
  intro e member
  simp only [P2, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> exact ⟨by decide, by decide, trivial⟩

def rejectedQuery : Comp mkeys [] () MTy :=
  .let_ [9] (sym "two") (.ret (sym "one")) (.ret (sym "done"))
def beforeBind : Branch mkeys [] () MTy :=
  ⟨[], .value (sym "one"), [.bindTo [9] (sym "two") (.ret (sym "done"))], []⟩
def afterBind : Branch mkeys [] () MTy :=
  ⟨[(sym "two", sym "one")], .eval (.ret (sym "done")), [], []⟩
def bindConfig : Config mkeys [] () MTy := ⟨W0, {beforeBind}⟩
def rejectedConfig : Config mkeys [] () MTy := ⟨W1, {afterBind}⟩

theorem bind_reachable : Runs D P1 supply (Config.initial sp rejectedQuery) bindConfig := by
  refine Relation.ReflTransGen.tail (b := ⟨W0, {⟨[], .eval (.ret (sym "one")),
    [.bindTo [9] (sym "two") (.ret (sym "done"))], []⟩}⟩) ?_ (step_one live_nil (.ret _ _ _ _ _))
  exact Relation.ReflTransGen.single (step_one live_nil (.letStart _ _ _ _ _ _ _ _))

theorem bind_moves : Move D P1 supply W0 beforeBind W1 {afterBind} := .letBind _ _ _ _ _ _ _ _

theorem bind_source_step : SourceLanguage.Step D P1 supply bindConfig rejectedConfig :=
  step_one live_nil bind_moves

theorem rejected_scope_advances : rejectedConfig.world.scope = bindConfig.world.scope + 1 := rfl

theorem bind_child_dead : ¬ Solvable afterBind.store :=
  SourceLanguage.FunctionVariables.dead_of_rootClash (K := []) (a := sym "two") (b := sym "one") (by decide)

theorem rejected_has_no_live_child :
    rejectedConfig.branches.filter (fun child => Solvable child.store) = 0 := by
  change ({afterBind} : Multiset (Branch mkeys [] () MTy)).filter _ = _
  simp [Multiset.filter_singleton, bind_child_dead]

theorem before_not_fail : beforeBind.focus ≠ .eval .fail := by intro impossible; cases impossible

theorem bind_hygienic : Hygienic beforeBind :=
  reachableHygienic_of_scoped (D := D) (P := P1) (supply := supply) sp rejectedQuery equations1 (qsite := [3]) (by decide) (by decide)
    ⟨trivial, trivial⟩ _ bind_reachable beforeBind (Multiset.mem_singleton_self _)

theorem bind_not_finished : ¬ beforeBind.Finished (D := D) := by
  rintro ⟨frames, _, _⟩
  cases frames

theorem bind_no_native_name {leaf : Leaf MSig} (paired : LeafRep (D := D) N P1 W0 beforeBind leaf) :
    ∀ name, ¬ Enabled (D := D) N P1 leaf name := by
  rintro name ⟨invocation⟩
  obtain ⟨next, child, named, _, live⟩ := invocation_reflect (D := D) N P1
    (fun e member => (equations1 e member).2.2) paired bind_hygienic invocation
  change NamedMove P1 W0 ⟨[], .value (sym "one"), [.bindTo [9] (sym "two") (.ret (sym "done"))], []⟩
    name next child at named
  cases named
  exact bind_child_dead live

/-- Completed negative evidence, supplied by the actual bind's contradiction. -/
def bindProbe {leaf : Leaf MSig} (paired : LeafRep (D := D) N P1 W0 beforeBind leaf) (name : Name) :
    FrontierNativeCore.ProbeResult Nat (catalogue (D := D) N P1) leaf name :=
  .ok (.inr ⟨bind_no_native_name paired name⟩)

theorem bindProbe_ready {leaf : Leaf MSig} (paired : LeafRep (D := D) N P1 W0 beforeBind leaf) :
    FrontierNativeCore.Ready (catalogue (D := D) N P1) (bindProbe paired) := by
  intro name member
  rfl

def bindExpansion {leaf : Leaf MSig} (paired : LeafRep (D := D) N P1 W0 beforeBind leaf) :
    Expansion (D := D) N P1 leaf :=
  FrontierNativeCore.fromProbes (catalogue (D := D) N P1) (bindProbe paired) (bindProbe_ready paired)

theorem bindExpansion_empty {leaf : Leaf MSig} (paired : LeafRep (D := D) N P1 W0 beforeBind leaf) :
    (bindExpansion paired).names = ∅ := by
  ext name
  rw [(bindExpansion paired).complete]
  exact ⟨fun enabled => (bind_no_native_name paired name enabled).elim, fun absent => by simp at absent⟩

theorem bind_retires {leaf : Leaf MSig} (paired : LeafRep (D := D) N P1 W0 beforeBind leaf)
    (old : Multiset (Leaf MSig)) : Step (D := D) N P1 ⟨{leaf}, old⟩ ⟨0, leaf ::ₘ old⟩ := by
  have emptyChildren : (bindExpansion paired).children = 0 := by
    apply Multiset.card_eq_zero.mp
    rw [(bindExpansion paired).children_card, bindExpansion_empty paired]
    rfl
  have unfinished : ¬ StateFinished N leaf.state leaf.active := fun done =>
    bind_not_finished ((Hosting.finished_iff N paired.1).mpr done).1
  have moved := FrontierNativeCore.Step.expand (finished := fun leaf => StateFinished N leaf.state leaf.active) leaf 0 old (valid (D := D) N P1 paired live_nil)
    unfinished (bindExpansion paired)
  simpa only [Step, Multiset.cons_zero, emptyChildren, zero_add, FrontierNativeCore.Expansion.retire, bindExpansion_empty paired,
    Finset.card_empty, ite_true] using moved

def pendingProbe (leaf : Leaf MSig) (name : Name) :
    FrontierNativeCore.ProbeResult Nat (catalogue (D := D) N P1) leaf name := .error 0

theorem pending_bind_is_not_a_refutation (leaf : Leaf MSig) :
    (pendingProbe leaf .bindValue).verdict = .suspended ∧
      ¬ FrontierNativeCore.Ready (catalogue (D := D) N P1) (pendingProbe leaf) := by
  refine ⟨rfl, FrontierNativeCore.pending_not_ready (catalogue (D := D) N P1)
    (pendingProbe leaf) (name := .bindValue) ?_ rfl⟩
  simp [catalogue, names]

theorem rejected_controller_reachable : ∃ before after,
    (target (D := D) N P1).MultiStep (initialState (D := D) N P1 rejectedQuery) before ∧
      Step (D := D) N P1 before after ∧ before.leaves.card = 1 ∧ after.leaves = 0 ∧
      after.retired.card = before.retired.card + 1 := by
  obtain ⟨before, path, related, _⟩ := source_run (D := D) N P1 supply sp rejectedQuery equations1
    (qsite := [3]) (by decide) (by decide) ⟨trivial, trivial⟩ bind_reachable
  have pairs := related.leaves
  change Multiset.Rel _ (({beforeBind} : Multiset (Branch mkeys [] () MTy)).filter _) before.leaves at pairs
  rw [Multiset.filter_singleton, if_pos (show Solvable beforeBind.store from live_nil)] at pairs
  obtain ⟨leaf, rest, pair, empty, split⟩ := Multiset.rel_cons_left.mp pairs
  have noRest := Multiset.rel_zero_left.mp empty
  rw [noRest] at split
  refine ⟨before, ⟨0, leaf ::ₘ before.retired⟩, path, ?_, ?_, rfl, by simp⟩
  · change Step (D := D) N P1 ⟨before.leaves, before.retired⟩ _
    rw [split]
    exact bind_retires pair before.retired
  · rw [split]
    rfl


def duplicateQuery : Comp mkeys [] () MTy := .let_ [9] oneT (.ret oneT) (.apply fT)
def beforeCallK : List (Constraint mkeys [] ()) := [(oneT, oneT)]
def afterCallK : List (Constraint mkeys [] ()) := beforeCallK ++ [(fT, fT)]
def duplicateCall : Branch mkeys [] () MTy := ⟨beforeCallK, .eval (.apply fT), [], []⟩
def duplicateChild : Branch mkeys [] () MTy := ⟨afterCallK, .eval (.ret oneT), [], []⟩
def duplicateValue : Branch mkeys [] () MTy := ⟨afterCallK, .value oneT, [], []⟩
def duplicateWorld : World mkeys [] () := ⟨2, 0, sp⟩
def duplicateFinal : Config mkeys [] () MTy := ⟨duplicateWorld, {duplicateValue, duplicateValue}⟩

theorem beforeCall_live : Solvable beforeCallK :=
  ⟨Empty, noNames, closeNames [] (csym "a"), fun equation member => by
    rw [show beforeCallK = [(oneT, oneT)] from rfl, List.mem_singleton] at member
    subst equation
    rfl⟩

theorem afterCall_live : Solvable afterCallK :=
  ⟨Empty, noNames, closeNames [] (csym "a"), fun equation member => by
    simp only [afterCallK, beforeCallK, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl⟩

theorem duplicate_runs : Runs D P2 supply (Config.initial sp duplicateQuery) duplicateFinal := by
  refine Relation.ReflTransGen.tail (b := ⟨duplicateWorld, {duplicateValue, duplicateChild}⟩) ?_
    (SourceLanguage.Step.of_eq (D := D) (P := P2) (supply := supply) (b := duplicateChild) (rest := {duplicateValue})
      (Multiset.cons_swap _ _ _) rfl afterCall_live (.ret _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨duplicateWorld, {duplicateChild, duplicateChild}⟩) ?_
    (SourceLanguage.Step.of_eq (D := D) (P := P2) (supply := supply) (b := duplicateChild) (rest := {duplicateChild})
      rfl rfl afterCall_live (.ret _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨W1, {duplicateCall}⟩) ?_
    (SourceLanguage.Step.of_eq (D := D) (P := P2) (supply := supply) (rest := 0) rfl rfl beforeCall_live
      (.apply W1 beforeCallK fT [] [] ⟨eqF, List.mem_cons_self, afterCall_live⟩))
  refine Relation.ReflTransGen.tail (b := ⟨W0, {⟨[], .value oneT,
    [.bindTo [9] oneT (.apply fT)], []⟩}⟩) ?_ (step_one live_nil (.letBind _ _ _ _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨W0, {⟨[], .eval (.ret oneT),
    [.bindTo [9] oneT (.apply fT)], []⟩}⟩) ?_ (step_one live_nil (.ret _ _ _ _ _))
  exact Relation.ReflTransGen.single (step_one live_nil (.letStart _ _ _ _ _ _ _ _))

theorem duplicate_answers : Config.answers (D := D) duplicateFinal = {{oneC}, {oneC}} := by
  have determines : Determines afterCallK oneT oneC := ⟨afterCall_live, fun _ _ _ => rfl⟩
  show Config.answers (D := D) ⟨duplicateWorld, duplicateValue ::ₘ {duplicateValue}⟩ = _
  rw [answers_cons_finished (D := D) ⟨rfl, _, rfl⟩ afterCall_live,
    answers_singleton (D := D) ⟨rfl, _, rfl⟩ afterCall_live,
    answer_of_determines rfl determines]
  rfl

theorem duplicates_behind_let_native : ∃ next,
    (target (D := D) N P2).MultiStep (initialState (D := D) N P2 duplicateQuery) next ∧
      answers N next = {{oneC}, {oneC}} := by
  obtain ⟨next, path, _, same⟩ := source_run (D := D) N P2 supply sp duplicateQuery equations2
    (qsite := [3]) (by decide) (by decide) ⟨trivial, trivial⟩ duplicate_runs
  exact ⟨next, path, same.symm.trans duplicate_answers⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierArrow.Controls
