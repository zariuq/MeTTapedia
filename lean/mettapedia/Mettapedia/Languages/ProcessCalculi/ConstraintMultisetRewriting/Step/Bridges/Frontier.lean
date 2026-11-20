import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventMultiplicity
import Mettapedia.GSLT.Core.OperationalReadback
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Multiset.AddSub

/-!
# Unfolding all named alternatives in a finite frontier

One controller step replaces one unfinished leaf by all its choice successors.
The successors form a multiset, so different choices with equal results remain
different alternatives. A leaf with no choices and no finished observation is
retired to a graveyard. Finished leaves remain available for observation.

Finite choice fibres are a hypothesis of this controller, not of the ambient
event system. Choice-fibre bisimulation lifts to a two-way correspondence of
frontier controllers, provided it also respects the finished observation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Frontier

open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational
open EventMultiplicity

universe uS uT uA uC uD

structure State (S : Type uS) where
  leaves : Multiset S
  retired : Multiset S

variable {S : Type uS} {T : Type uT} {A : Type uA}

def children (system : System.{uS,uA,uC} S A) [∀ s, Fintype (system.Choice s)] (state : S) : Multiset S :=
  Finset.univ.val.map (system.next state)

def retire (system : System.{uS,uA,uC} S A) [∀ s, Fintype (system.Choice s)]
    (state : S) (previous : Multiset S) : Multiset S :=
  if Fintype.card (system.Choice state) = 0 then state ::ₘ previous else previous

inductive Unfold (system : System.{uS,uA,uC} S A) [∀ s, Fintype (system.Choice s)]
    (finished : S → Prop) : State S → State S → Prop
  | expand (state : S) (rest retired : Multiset S) (unfinished : ¬ finished state) :
      Unfold system finished ⟨state ::ₘ rest, retired⟩
        ⟨children system state + rest, retire system state retired⟩

def theory (system : System.{uS,uA,uC} S A) [∀ s, Fintype (system.Choice s)] (finished : S → Prop) : GSLT :=
  Mettapedia.OSLF.Framework.GSLTTypeSynthesis.equalityGSLT (State S) (Unfold system finished)

def Related (R : S → T → Prop) (left : State S) (right : State T) : Prop :=
  Multiset.Rel R left.leaves right.leaves ∧ Multiset.Rel R left.retired right.retired

theorem Related.swap {R : S → T → Prop} {left : State S} {right : State T} (related : Related R left right) :
    Related (fun t s => R s t) right left :=
  ⟨Multiset.rel_flip.mpr related.1, Multiset.rel_flip.mpr related.2⟩

variable {left : System.{uS,uA,uC} S A} {right : System.{uT,uA,uD} T A}
  [∀ s, Fintype (left.Choice s)] [∀ t, Fintype (right.Choice t)] {R : S → T → Prop}

theorem children_related (comparison : Bisimulation left right R) {s : S} {t : T} (related : R s t) :
    Multiset.Rel R (children left s) (children right t) := by
  unfold children
  rw [← Multiset.map_univ_val_equiv (comparison.choices related), Multiset.map_map]
  apply Multiset.rel_map.mpr
  exact Multiset.rel_refl_of_refl_on fun choice _ => comparison.successors related choice

theorem retired_related (comparison : Bisimulation left right R) {s : S} {t : T} (related : R s t)
    {past : Multiset S} {past' : Multiset T} (history : Multiset.Rel R past past') :
    Multiset.Rel R (retire left s past) (retire right t past') := by
  have cards := Fintype.card_congr (comparison.choices related)
  unfold retire
  rw [cards]
  split
  · exact history.cons related
  · exact history

theorem forward (comparison : Bisimulation left right R)
    {leftFinished : S → Prop} {rightFinished : T → Prop}
    (finished : ∀ {s t}, R s t → (leftFinished s ↔ rightFinished t))
    {before after : State S} {current : State T}
    (related : Related R before current) (step : Unfold left leftFinished before after) :
    ∃ next, Unfold right rightFinished current next ∧ Related R after next := by
  cases step with
  | expand s rest past unfinished =>
    obtain ⟨t, tail, pair, tails, shape⟩ := Multiset.rel_cons_left.mp related.1
    rcases current with ⟨leaves, retired⟩
    change leaves = t ::ₘ tail at shape
    subst leaves
    refine ⟨_, .expand t tail retired (fun done => unfinished ((finished pair).mpr done)),
      (children_related comparison pair).add tails, retired_related comparison pair related.2⟩

theorem backward (comparison : Bisimulation left right R)
    {leftFinished : S → Prop} {rightFinished : T → Prop}
    (finished : ∀ {s t}, R s t → (leftFinished s ↔ rightFinished t))
    {before : State S} {current next : State T}
    (related : Related R before current) (step : Unfold right rightFinished current next) :
    ∃ after, Unfold left leftFinished before after ∧ Related R after next := by
  obtain ⟨after, moved, paired⟩ :=
    forward comparison.symm (fun pair => (finished pair).symm) related.swap step
  exact ⟨after, moved, paired.swap⟩

def correspondence (comparison : Bisimulation left right R)
    {leftFinished : S → Prop} {rightFinished : T → Prop}
    (finished : ∀ {s t}, R s t → (leftFinished s ↔ rightFinished t)) :
    OperationalCorrespondence (theory left leftFinished) (theory right rightFinished) where
  related := Related R
  readStep related step := .inr (backward comparison finished related step)
  forward related step := by
    obtain ⟨next, moved, paired⟩ := forward comparison finished related step
    exact ⟨next, ⟨.cons ⟨moved⟩ (.refl next)⟩, paired⟩

noncomputable def answers {V : Type*} (finished : S → Prop) (view : S → V) (state : State S) : Multiset V := by
  classical
  exact (state.leaves.filter finished).map view

theorem answers_eq {V : Type*} {leftFinished : S → Prop} {rightFinished : T → Prop}
    (finished : ∀ {s t}, R s t → (leftFinished s ↔ rightFinished t))
    (leftView : S → V) (rightView : T → V)
    (views : ∀ {s t}, R s t → leftFinished s → leftView s = rightView t)
    {before : State S} {current : State T} (related : Related R before current) :
    answers leftFinished leftView before = answers rightFinished rightView current := by
  classical
  have lift {as : Multiset S} {bs : Multiset T} (pairedBags : Multiset.Rel R as bs) :
      (as.filter leftFinished).map leftView = (bs.filter rightFinished).map rightView := by
    induction pairedBags with
    | zero => rfl
    | @cons s t as bs paired rest ih =>
      rw [Multiset.filter_cons, Multiset.filter_cons]
      by_cases done : leftFinished s
      · rw [if_pos done, if_pos ((finished paired).mp done), Multiset.map_add, Multiset.map_add,
          Multiset.map_singleton, Multiset.map_singleton, views paired done, ih]
      · rw [if_neg done, if_neg (fun yes => done ((finished paired).mpr yes)), zero_add, zero_add, ih]
  exact lift related.1

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Frontier

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Frontier.children_related
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Frontier.correspondence
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Frontier.answers_eq
