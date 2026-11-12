import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.FrameIndexing
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Interface

/-!
# Scope identities on actual effect and admission profiles

A scope key distinguishes context occurrences with the same underlying
declaration shape. Within one scope, preparation, permission, effects and
optional exactness preserve the native profile. Occurrence identities remain
unchanged; copying a scope is not copying its resources or creating a world.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open MeTTaCalculus.OccurrenceCommits (Enabled)

universe uO uT uH uOcc uS uF uK

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}

namespace EffectCore

variable (effect : EffectCore X O State Firing) (Key : Type uK)

theorem unpackScopePreparation {state : Key × State} (firing : Firing state.2)
    (prepared : effect.Shapes firing ∧
      Enabled (fun _ : O => ()) (effect.present state.2) ((effect.selection firing).commit (T := Unit)) ∧
      (X.copies Key).Solvable (a := (state.1, effect.target firing)) (effect.information firing)) :
    effect.Prepares firing :=
  ⟨prepared.1, prepared.2.1,
    (Frames.copies_solvable_iff X (state.1, effect.target firing) (effect.information firing)).mp prepared.2.2⟩

def withScopeKeys : EffectCore (X.copies Key) O (Key × State) (fun state => Firing state.2) where
  frame state := (state.1, effect.frame state.2)
  knowledge state := effect.knowledge state.2
  present state := effect.present state.2
  selection firing := effect.selection firing
  target {s} firing := (s.1, effect.target firing)
  extension firing := effect.extension firing
  information firing := effect.information firing
  information_refines := by
    intro state firing target mapping solved
    exact effect.information_refines firing mapping solved
  Shapes firing := effect.Shapes firing
  preparedResult {s} firing prepared :=
    (s.1, effect.preparedResult firing (effect.unpackScopePreparation Key firing prepared))
  present_preparedResult firing prepared :=
    effect.present_preparedResult firing (effect.unpackScopePreparation Key firing prepared)
  preparedSettle firing prepared :=
    effect.preparedSettle firing (effect.unpackScopePreparation Key firing prepared)
  result_refines := by
    intro state firing prepared target mapping solved
    exact effect.result_refines firing (effect.unpackScopePreparation Key firing prepared) mapping solved

theorem scope_prepares_iff (key : Key) {state : State} (firing : Firing state) :
    (effect.withScopeKeys Key).Prepares (s := (key, state)) firing ↔ effect.Prepares firing :=
  and_congr Iff.rfl (and_congr Iff.rfl
    (Frames.copies_solvable_iff X (key, effect.target firing) (effect.information firing)))

theorem scope_exact (exactness : effect.ExactKnowledge) : (effect.withScopeKeys Key).ExactKnowledge := by
  intro state firing prepared target mapping solved
  exact exactness firing (effect.unpackScopePreparation Key firing prepared) mapping solved

def scopedAdmission (allow : effect.Admission) : (effect.withScopeKeys Key).Admission :=
  fun firing prepared => allow firing (effect.unpackScopePreparation Key firing prepared)

theorem scope_key_preserved {state : Key × State} (firing : Firing state.2)
    (prepared : (effect.withScopeKeys Key).Prepares (s := state) firing) :
    ((effect.withScopeKeys Key).preparedResult (s := state) firing prepared).1 = state.1 := rfl

end EffectCore

namespace Step

variable (P : Step X O State Firing) (Key : Type uK)

def withScopeKeys : Step (X.copies Key) O (Key × State) (fun state => Firing state.2) :=
  Step.ofEffect (P.effectCore.withScopeKeys Key) (P.effectCore.scopedAdmission Key P.eventAdmission)

theorem scope_admits_iff (key : Key) {state : State} (firing : Firing state) :
    (P.withScopeKeys Key).Admits (s := (key, state)) firing ↔ P.Admits firing := by
  constructor
  · rintro ⟨_, allowed⟩
    exact allowed
  · intro allowed
    exact ⟨(P.effectCore.scope_prepares_iff Key key firing).mpr (P.prepares allowed), allowed⟩

theorem scope_result {key : Key} {state : State} (firing : Firing state)
    (allowed : (P.withScopeKeys Key).Admits (s := (key, state)) firing) :
    (P.withScopeKeys Key).result (s := (key, state)) firing allowed =
      (key, P.result (s := state) firing ((P.scope_admits_iff Key key firing).mp allowed)) := rfl

end Step

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
