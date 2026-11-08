import Mettapedia.Machines.ReadOnlyQueryRelation

/-!
# Adaptive query relations under growing observation worlds

The query syntax and state-threaded interpreter are unchanged. A read may
extend a correspondence world: newly allocated private names become related
while earlier keys and replies remain related. One final world relates the
entire ordered trace, not independent renamings of its elements.

The optional interpreter compares matched completion evidence. It does not
assert that warm and cold computations use equal physical work or that a
cached answer licenses ignoring an observable budget.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ReadOnlyQueryWorldRelation

open ReadOnlyQuery ReadOnlyQueryDemand

variable {World Key Reply Answer Other State OtherState : Type}

structure Worlds (World Key Reply : Type) where
  grows : World → World → Prop
  grows_refl : ∀ world, grows world world
  grows_trans : ∀ {first middle last}, grows first middle → grows middle last → grows first last
  keys : World → Key → Key → Prop
  replies : World → Reply → Reply → Prop
  keys_mono : ∀ {first last}, grows first last → ∀ {left right}, keys first left right → keys last left right
  replies_mono : ∀ {first last}, grows first last → ∀ {left right},
    replies first left right → replies last left right

inductive Related (worlds : Worlds World Key Reply) (answers : World → Answer → Answer → Prop) :
    World → Program Key Reply Answer → Program Key Reply Answer → Prop where
  | pure {world first second} : answers world first second →
      Related worlds answers world (.pure first) (.pure second)
  | read {world firstKey secondKey} {first second : Reply → Program Key Reply Answer} :
      worlds.keys world firstKey secondKey →
      (∀ next, worlds.grows world next → ∀ left right, worlds.replies next left right →
        Related worlds answers next (first left) (second right)) →
      Related worlds answers world (.read firstKey first) (.read secondKey second)

theorem bind_related (worlds : Worlds World Key Reply)
    (answers : World → Answer → Answer → Prop) (results : World → Other → Other → Prop)
    {world : World} {first second : Program Key Reply Answer}
    (related : Related worlds answers world first second)
    (nextFirst nextSecond : Answer → Program Key Reply Other)
    (later : ∀ next, worlds.grows world next → ∀ left right, answers next left right →
      Related worlds results next (nextFirst left) (nextSecond right)) :
    Related worlds results world (bind first nextFirst) (bind second nextSecond) := by
  revert later
  induction related with
  | pure good =>
      intro later
      exact later _ (worlds.grows_refl _) _ _ good
  | @read world firstKey secondKey first second keys children ih =>
      intro later
      apply Related.read keys
      intro next advanced left right replies
      apply ih next advanced left right replies
      intro last extended firstAnswer secondAnswer answersRelated
      exact later last (worlds.grows_trans advanced extended) firstAnswer secondAnswer answersRelated

theorem map_related (worlds : Worlds World Key Reply)
    (answers : World → Answer → Answer → Prop) (results : World → Other → Other → Prop)
    {world : World} {first second : Program Key Reply Answer}
    (related : Related worlds answers world first second) (firstMap secondMap : Answer → Other)
    (preserves : ∀ next, worlds.grows world next → ∀ left right, answers next left right →
      results next (firstMap left) (secondMap right)) :
    Related worlds results world (map firstMap first) (map secondMap second) := by
  apply bind_related worlds answers results related
  intro next advanced left right relatedAnswers
  exact .pure (preserves next advanced left right relatedAnswers)

/-- A static restriction on reached inquiries, independent of private
allocation. This can express a recursive call rank without constraining
which replies an inquiry may return. -/
def restrictKeys (worlds : Worlds World Key Reply) (allowed : Key → Prop) : Worlds World Key Reply where
  grows := worlds.grows
  grows_refl := worlds.grows_refl
  grows_trans := worlds.grows_trans
  keys world first second := worlds.keys world first second ∧ allowed first
  replies := worlds.replies
  keys_mono := fun {_ _} grown {_ _} keys => ⟨worlds.keys_mono grown keys.1, keys.2⟩
  replies_mono := worlds.replies_mono

/-- The restriction is earned from the actual left program's key invariant.
The unrestricted reply predicate is deliberate: no successful or preferred
answer is assumed to prove that recursive calls get smaller. -/
theorem restrict_related (worlds : Worlds World Key Reply) (allowed : Key → Prop)
    (answers : World → Answer → Answer → Prop) {world : World}
    {first second : Program Key Reply Answer} (related : Related worlds answers world first second)
    (keys : ReadOnlyQuerySafety.Guarantees allowed (fun _ => True) (fun _ => True) first) :
    Related (restrictKeys worlds allowed) answers world first second := by
  induction related with
  | pure good => exact .pure good
  | read pair children ih =>
      cases keys with
      | read allowedHere later =>
          exact .read ⟨pair, allowedHere⟩ (fun next grown left right replies =>
            ih next grown left right replies (later left trivial))

def EventRelated (worlds : Worlds World Key Reply) (world : World)
    (first second : Key × Option Reply) : Prop :=
  worlds.keys world first.1 second.1 ∧ Option.Rel (worlds.replies world) first.2 second.2

theorem optional_reply_mono (worlds : Worlds World Key Reply) {first last : World}
    (advanced : worlds.grows first last) {left right : Option Reply}
    (related : Option.Rel (worlds.replies first) left right) :
    Option.Rel (worlds.replies last) left right := by
  cases related with
  | none => exact .none
  | some good => exact .some (worlds.replies_mono advanced good)

theorem event_mono (worlds : Worlds World Key Reply) {first last : World}
    (advanced : worlds.grows first last) {left right : Key × Option Reply}
    (related : EventRelated worlds first left right) : EventRelated worlds last left right :=
  ⟨worlds.keys_mono advanced related.1, optional_reply_mono worlds advanced related.2⟩

/-- Per-read service correspondence, including its actual private-state
change. This is not a premise about a whole query execution. -/
def ServicesRelated (worlds : Worlds World Key Reply) (states : World → State → OtherState → Prop)
    (first : State → Key → Option Reply × State)
    (second : OtherState → Key → Option Reply × OtherState) : Prop :=
  ∀ world left right, states world left right → ∀ firstKey secondKey,
    worlds.keys world firstKey secondKey →
    ∃ next, worlds.grows world next ∧
      states next (first left firstKey).2 (second right secondKey).2 ∧
      Option.Rel (worlds.replies next) (first left firstKey).1 (second right secondKey).1

/-- Both final states and every read occurrence use one final correspondence
world. Missing replies stop the existing demand interpreter on both sides. -/
theorem demand_run_related (worlds : Worlds World Key Reply)
    (answers : World → Answer → Answer → Prop) (states : World → State → OtherState → Prop)
    (firstService : State → Key → Option Reply × State)
    (secondService : OtherState → Key → Option Reply × OtherState)
    (services : ServicesRelated worlds states firstService secondService)
    {world : World} {first second : Program Key Reply Answer}
    (related : Related worlds answers world first second)
    (left : State) (right : OtherState) (initial : states world left right) :
    let firstRun := QueryState.run firstService (demand first) left
    let secondRun := QueryState.run secondService (demand second) right
    ∃ last, worlds.grows world last ∧ states last firstRun.state secondRun.state ∧
      Option.Rel (answers last) firstRun.answer secondRun.answer ∧
      List.Forall₂ (EventRelated worlds last) firstRun.reads secondRun.reads := by
  dsimp only
  induction related generalizing left right with
  | pure good =>
      exact ⟨_, worlds.grows_refl _, initial, .some good, .nil⟩
  | @read world firstKey secondKey first second keys children ih =>
      obtain ⟨middle, advanced, middleStates, replies⟩ :=
        services world left right initial firstKey secondKey keys
      cases firstReply : (firstService left firstKey).1 with
      | none =>
          have secondReply : (secondService right secondKey).1 = none := by
            rw [firstReply] at replies
            cases found : (secondService right secondKey).1 with
            | none => rfl
            | some value => simp only [found, Option.not_rel_none_some] at replies
          simp only [demand, QueryState.run, firstReply, secondReply]
          exact ⟨middle, advanced, middleStates, .none,
            .cons ⟨worlds.keys_mono advanced keys, .none⟩ .nil⟩
      | some firstValue =>
          obtain ⟨secondValue, secondReply, replyRelated⟩ :
              ∃ value, (secondService right secondKey).1 = some value ∧
                worlds.replies middle firstValue value := by
            rw [firstReply] at replies
            cases found : (secondService right secondKey).1 with
            | none => simp only [found, Option.not_rel_some_none] at replies
            | some value =>
                exact ⟨value, rfl, by simpa only [found, Option.rel_some_some] using replies⟩
          obtain ⟨last, extended, finalStates, finalAnswers, finalReads⟩ :=
            ih middle advanced firstValue secondValue replyRelated
              (firstService left firstKey).2 (secondService right secondKey).2 middleStates
          simp only [demand, QueryState.run, firstReply, secondReply]
          exact ⟨last, worlds.grows_trans advanced extended, finalStates, finalAnswers,
            .cons ⟨worlds.keys_mono (worlds.grows_trans advanced extended) keys,
              .some (worlds.replies_mono extended replyRelated)⟩ finalReads⟩

end Mettapedia.Machines.ReadOnlyQueryWorldRelation
