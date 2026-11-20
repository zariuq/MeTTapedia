import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds.Product
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.TransitionMaps

/-!
# Refining the local executions of actual worlds

An inclusion of local successor relations lifts through the existing firing and
world-move constructors. Fork, publication and merge are retained verbatim.
These are endpoint and reachability laws: an inclusion need not preserve event
fibres, actions or multiplicities, and does not give backward lifting,
divergence reflection or termination preservation.

The singleton comparison is a functional bisimulation for any supplied local
event family. Its target is the existing proposition-valued `Worlds.Fires`;
it does not count world occurrences or proofs of the firing relation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Worlds

open RuleSyntax RuleSyntax.Worlds
open RuleSyntax.Equivalence (System)
open FragmentsOfTheStep.TransitionMaps (FunctionalBisimulation)

universe uO uT uH uOcc uA uB

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {O : Type uOcc} {A : Type uA} {B : Type uB}
  {left : LocalSteps Tm O A} {right : LocalSteps Tm O B}

/-- Local refinement keeps the same actual world endpoints. -/
theorem fires_mono
    (refines : ∀ program before after,
      Advances left program before after → Advances right program before after)
    {W W' : Bag Tm O} (fired : Fires left W W') : Fires right W W' := by
  cases fired with
  | fire rest space S choice =>
      obtain ⟨other, same⟩ := refines _ _ _ ⟨choice, rfl⟩
      have lifted := Fires.fire (family := right) rest space S other
      rw [same] at lifted
      exact lifted

theorem fires_runs_mono
    (refines : ∀ program before after,
      Advances left program before after → Advances right program before after)
    {W W' : Bag Tm O} (run : Relation.ReflTransGen (Fires left) W W') :
    Relation.ReflTransGen (Fires right) W W' := by
  induction run with
  | refl => exact .refl
  | tail _ last earlier => exact earlier.tail (fires_mono refines last)

theorem reaches_mono
    (refines : ∀ program before after,
      Advances left program before after → Advances right program before after)
    (barb : State Tm O → Prop) {W : Bag Tm O} (reached : Reaches left barb W) :
    Reaches right barb W := by
  obtain ⟨last, run, observed⟩ := reached
  exact ⟨last, fires_runs_mono refines run, observed⟩

theorem fires_congr
    (same : ∀ program before after,
      Advances left program before after ↔ Advances right program before after)
    (W W' : Bag Tm O) : Fires left W W' ↔ Fires right W W' :=
  ⟨fires_mono (fun p s t => (same p s t).mp),
    fires_mono (fun p s t => (same p s t).mpr)⟩

section Moves

variable [DecidableEq O] (X : Frames Tm Hom) (J : Joining X O)

/-- Refining local firings does not erase the other world operations. -/
theorem moves_mono
    (refines : ∀ program before after,
      Advances left program before after → Advances right program before after)
    {W W' : Bag Tm O} (moved : Move X J left W W') : Move X J right W W' := by
  cases moved with
  | fire rest space S choice =>
      obtain ⟨other, same⟩ := refines _ _ _ ⟨choice, rfl⟩
      have lifted := Move.fire (X := X) (J := J) (family := right) rest space S other
      rw [same] at lifted
      exact lifted
  | fork rest space S => exact Move.fork rest space S
  | publish rest space S occurrence present => exact Move.publish rest space S occurrence present
  | merge rest space S T alive => exact Move.merge rest space S T alive

theorem moves_runs_mono
    (refines : ∀ program before after,
      Advances left program before after → Advances right program before after)
    {W W' : Bag Tm O} (run : Relation.ReflTransGen (Move X J left) W W') :
    Relation.ReflTransGen (Move X J right) W W' := by
  induction run with
  | refl => exact .refl
  | tail _ last earlier => exact earlier.tail (moves_mono X J refines last)

theorem succeeds_mono
    (refines : ∀ program before after,
      Advances left program before after → Advances right program before after)
    (barb : State Tm O → Prop) {W : Bag Tm O}
    (succeeded : (bagParallel X J left barb).Succeeds W) :
    (bagParallel X J right barb).Succeeds W := by
  obtain ⟨last, run, observed⟩ := succeeded
  exact ⟨last, moves_runs_mono X J refines run, observed⟩

theorem moves_congr
    (same : ∀ program before after,
      Advances left program before after ↔ Advances right program before after)
    (W W' : Bag Tm O) : Move X J left W W' ↔ Move X J right W W' :=
  ⟨moves_mono X J (fun p s t => (same p s t).mp),
    moves_mono X J (fun p s t => (same p s t).mpr)⟩

end Moves

/-! ## Refinement on a rule-defined region -/

/-- Every rule visible to every world satisfies the stated rule property. -/
def RulesSatisfy (good : Rule Tm → Prop) (W : Bag Tm O) : Prop :=
  ∀ S ∈ W.worlds, ∀ rule ∈ S.program ∪ W.space, good rule

section RuleRegion

open Hosting.Alternatives.Worlds (snapshot)

variable [DecidableEq O] (X : Frames Tm Hom) (J : Joining X O)
  (good : Rule Tm → Prop)

/-- Local firing changes no rules, fork copies them, merge unions them, and
publication adds precisely its closed snapshot. -/
theorem rulesSatisfy_move
    (snapshot_good : ∀ (state : State Tm O) (atom : Tm state.frame), good (snapshot state atom))
    {W W' : Bag Tm O} (valid : RulesSatisfy good W) (moved : Move X J left W W') :
    RulesSatisfy good W' := by
  cases moved with
  | fire rest space S choice =>
      intro T member rule visible
      rcases Multiset.mem_cons.mp member with rfl | member
      · exact valid S (Multiset.mem_cons_self S rest) rule visible
      · exact valid T (Multiset.mem_cons_of_mem member) rule visible
  | fork rest space S =>
      intro T member rule visible
      rcases Multiset.mem_cons.mp member with rfl | member
      · exact valid T (Multiset.mem_cons_self T rest) rule visible
      · exact valid T member rule visible
  | publish rest space S occurrence present =>
      have enlarged : ∀ T ∈ S ::ₘ rest,
          ∀ rule ∈ T.program ∪ insert (snapshot S.state (S.state.label occurrence)) space,
            good rule := by
        intro T member rule visible
        rcases visible with own | shared
        · exact valid T member rule (Or.inl own)
        · rcases Set.mem_insert_iff.mp shared with rfl | shared
          · exact snapshot_good _ _
          · exact valid T member rule (Or.inr shared)
      intro T member rule visible
      rcases Multiset.mem_cons.mp member with rfl | member
      · exact enlarged S (Multiset.mem_cons_self S rest) rule visible
      · exact enlarged T (Multiset.mem_cons_of_mem member) rule visible
  | merge rest space S T alive =>
      intro U member rule visible
      rcases Multiset.mem_cons.mp member with rfl | member
      · rcases visible with own | shared
        · rcases own with fromS | fromT
          · exact valid S (Multiset.mem_cons_self S (T ::ₘ rest)) rule (Or.inl fromS)
          · exact valid T (Multiset.mem_cons_of_mem (Multiset.mem_cons_self T rest)) rule
              (Or.inl fromT)
        · exact valid S (Multiset.mem_cons_self S (T ::ₘ rest)) rule (Or.inr shared)
      · exact valid U (Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem member)) rule visible

theorem rulesSatisfy_runs
    (snapshot_good : ∀ (state : State Tm O) (atom : Tm state.frame), good (snapshot state atom))
    {W W' : Bag Tm O} (valid : RulesSatisfy good W)
    (run : Relation.ReflTransGen (Move X J left) W W') : RulesSatisfy good W' := by
  induction run with
  | refl => exact valid
  | tail _ last earlier => exact rulesSatisfy_move X J good snapshot_good earlier last

/-- A local comparison is needed only on the rule region actually used by
the source world. The other world operations are not simulated away. -/
theorem moves_mono_of_rules
    (refines : ∀ program, (∀ rule ∈ program, good rule) →
      ∀ before after, Advances left program before after → Advances right program before after)
    {W W' : Bag Tm O} (valid : RulesSatisfy good W) (moved : Move X J left W W') :
    Move X J right W W' := by
  cases moved with
  | fire rest space S choice =>
      obtain ⟨other, same⟩ := refines (S.program ∪ space)
        (valid S (Multiset.mem_cons_self S rest)) _ _ ⟨choice, rfl⟩
      have lifted := Move.fire (X := X) (J := J) (family := right) rest space S other
      rw [same] at lifted
      exact lifted
  | fork rest space S => exact Move.fork rest space S
  | publish rest space S occurrence present => exact Move.publish rest space S occurrence present
  | merge rest space S T alive => exact Move.merge rest space S T alive

/-- Rule-region refinement persists along actual runs because each world
operation preserves the region, including the checked publication case. -/
theorem moves_runs_mono_of_rules
    (snapshot_good : ∀ (state : State Tm O) (atom : Tm state.frame), good (snapshot state atom))
    (refines : ∀ program, (∀ rule ∈ program, good rule) →
      ∀ before after, Advances left program before after → Advances right program before after)
    {W W' : Bag Tm O} (valid : RulesSatisfy good W)
    (run : Relation.ReflTransGen (Move X J left) W W') :
    Relation.ReflTransGen (Move X J right) W W' := by
  induction run with
  | refl => exact .refl
  | tail prior last earlier =>
      have valid_here := rulesSatisfy_runs X J good snapshot_good valid prior
      exact earlier.tail (moves_mono_of_rules X J good refines valid_here last)

theorem moves_runs_congr_of_rules
    (snapshot_good : ∀ (state : State Tm O) (atom : Tm state.frame), good (snapshot state atom))
    (same : ∀ program, (∀ rule ∈ program, good rule) →
      ∀ before after, Advances left program before after ↔ Advances right program before after)
    {W W' : Bag Tm O} (valid : RulesSatisfy good W) :
    Relation.ReflTransGen (Move X J left) W W' ↔
      Relation.ReflTransGen (Move X J right) W W' :=
  ⟨moves_runs_mono_of_rules X J good snapshot_good
      (fun p allowed s t => (same p allowed s t).mp) valid,
    moves_runs_mono_of_rules X J good snapshot_good
      (fun p allowed s t => (same p allowed s t).mpr) valid⟩

end RuleRegion

section Singleton

variable (family : LocalSteps Tm O A)

/-- The singleton target is characterized by its actual local event choice. -/
theorem singleton_fires_iff (S : System Tm O) (shared : Program Tm) (W' : Bag Tm O) :
    Fires family ⟨{S}, shared⟩ W' ↔
      ∃ after, Advances family (S.program ∪ shared) S.state after ∧
        W' = ⟨{(⟨S.program, after⟩ : System Tm O)}, shared⟩ := by
  constructor
  · intro fired
    generalize same : (⟨{S}, shared⟩ : Bag Tm O) = W at fired
    cases fired with
    | fire rest space chosen choice =>
        injection same with worlds_eq space_eq
        obtain ⟨rfl, rfl⟩ := (Multiset.singleton_eq_cons_iff rest).mp worlds_eq
        subst space_eq
        exact ⟨_, ⟨choice, rfl⟩, rfl⟩
  · rintro ⟨after, ⟨choice, rfl⟩, rfl⟩
    exact Fires.fire 0 shared S choice

/-- Every local step is represented, and every firing out of the singleton
image lifts. This is independent of the chosen commit and guard policy. -/
theorem singleton_local_bisimulation (program shared : Program Tm) :
    FunctionalBisimulation (Advances family (program ∪ shared)) (Fires family)
      (fun state => (⟨{(⟨program, state⟩ : System Tm O)}, shared⟩ : Bag Tm O)) where
  zig := by
    rintro before after ⟨choice, rfl⟩
    exact Fires.fire 0 shared ⟨program, before⟩ choice
  zag := by
    intro before last fired
    obtain ⟨after, advanced, same⟩ := (singleton_fires_iff family _ shared last).mp fired
    exact ⟨after, advanced, same.symm⟩

end Singleton

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Worlds
