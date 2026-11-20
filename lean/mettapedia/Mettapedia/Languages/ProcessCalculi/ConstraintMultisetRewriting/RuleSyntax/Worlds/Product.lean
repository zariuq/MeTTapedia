import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds.Bag

/-!
# Without publication and merge, side by side is a product

A bag of worlds interacts through two moves only: a publication to the space and a merge. This
module states what the bag is without them.

* `Fires`: the moves of a bag in which a world makes an actual choice of the supplied local event
  family, at its visible program. They are moves (`Fires.move`) and leave the space as it is
  (`Fires.space_eq`).
* `fires_split`: a firing of a bag that is the sum of two bags is a firing of one of the two, the
  other unchanged; `runs_split`: so every run of firings of the sum is a pair of runs, one of each.
* **`product`**: with one space and firings only, **the sum of two bags reaches the observation
  exactly when one of the two does.** No neighbour switches a bag off, and none switches it on.
* `reaches_succeeds`: what firings reach, the moves reach.

These laws hold for every local event family, including policies that are not monotone in the
visible program. Adding worlds here leaves the shared space unchanged. Unioning another space is a
different operation and needs its own licence. Publication and merge remain explicit moves.
The product observation is reaching `Shows`; event fibres and counted histories require their own
comparisons.
-/

set_option autoImplicit false

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence (System)

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds

open Interface (Frames)

universe uO uT uH uOcc uA

variable {Obj : Type uO} {Tm : Obj → Type uT} {O : Type uOcc} {Action : Type uA}

/-- **A firing move of a bag**: a world makes an actual local event choice at its visible program. -/
inductive Fires (family : LocalSteps Tm O Action) : Bag Tm O → Bag Tm O → Prop
  | fire (rest : Multiset (System Tm O)) (space : Program Tm) (S : System Tm O)
      (choice : (family (S.program ∪ space)).Choice S.state) :
      Fires family ⟨S ::ₘ rest, space⟩
        ⟨(⟨S.program, (family (S.program ∪ space)).next S.state choice⟩ : System Tm O) ::ₘ rest, space⟩

variable {family : LocalSteps Tm O Action}

section Move

variable {Hom : Obj → Obj → Type uH} [DecidableEq O] (X : Frames Tm Hom) (J : Joining X O)

/-- A firing move is a move. -/
theorem Fires.move {W W' : Bag Tm O} (fires : Fires family W W') : Move X J family W W' := by
  cases fires with
  | fire rest space S choice => exact Move.fire rest space S choice

end Move

/-- A firing move leaves the space as it is. -/
theorem Fires.space_eq {W W' : Bag Tm O} (fires : Fires family W W') : W'.space = W.space := by
  cases fires with
  | fire rest space S choice => rfl

/-- A firing move of a bag is a firing move of the bag with more worlds, on the right. -/
theorem Fires.add_right {W W' : Bag Tm O} (fires : Fires family W W') (more : Multiset (System Tm O)) :
    Fires family ⟨W.worlds + more, W.space⟩ ⟨W'.worlds + more, W'.space⟩ := by
  cases fires with
  | fire rest space S choice =>
      show Fires family ⟨S ::ₘ rest + more, space⟩
        ⟨(⟨S.program, (family (S.program ∪ space)).next S.state choice⟩ : System Tm O) ::ₘ rest + more, space⟩
      simp only [Multiset.cons_add]
      exact Fires.fire (rest + more) space S choice

/-- A firing move of a bag is a firing move of the bag with more worlds, on the left. -/
theorem Fires.add_left {W W' : Bag Tm O} (fires : Fires family W W') (more : Multiset (System Tm O)) :
    Fires family ⟨more + W.worlds, W.space⟩ ⟨more + W'.worlds, W'.space⟩ := by
  cases fires with
  | fire rest space S choice =>
      show Fires family ⟨more + S ::ₘ rest, space⟩
        ⟨more + (⟨S.program, (family (S.program ∪ space)).next S.state choice⟩ : System Tm O) ::ₘ rest, space⟩
      simp only [Multiset.add_cons]
      exact Fires.fire (more + rest) space S choice

theorem runs_add_right {W W' : Bag Tm O} (run : Relation.ReflTransGen (Fires family) W W')
    (more : Multiset (System Tm O)) :
    Relation.ReflTransGen (Fires family) ⟨W.worlds + more, W.space⟩ ⟨W'.worlds + more, W'.space⟩ := by
  induction run with
  | refl => exact .refl
  | tail _ last ih => exact ih.tail (Fires.add_right last more)

theorem runs_add_left {W W' : Bag Tm O} (run : Relation.ReflTransGen (Fires family) W W')
    (more : Multiset (System Tm O)) :
    Relation.ReflTransGen (Fires family) ⟨more + W.worlds, W.space⟩ ⟨more + W'.worlds, W'.space⟩ := by
  induction run with
  | refl => exact .refl
  | tail _ last ih => exact ih.tail (Fires.add_left last more)

/-- **A firing of the sum of two bags is a firing of one of the two**, the other unchanged. -/
theorem fires_split {ws₁ ws₂ : Multiset (System Tm O)} {R : Program Tm} {W' : Bag Tm O}
    (fires : Fires family ⟨ws₁ + ws₂, R⟩ W') :
    (∃ ws₁', Fires family ⟨ws₁, R⟩ ⟨ws₁', R⟩ ∧ W' = ⟨ws₁' + ws₂, R⟩) ∨
      ∃ ws₂', Fires family ⟨ws₂, R⟩ ⟨ws₂', R⟩ ∧ W' = ⟨ws₁ + ws₂', R⟩ := by
  generalize hW : (⟨ws₁ + ws₂, R⟩ : Bag Tm O) = W at fires
  cases fires with
  | fire rest space S choice =>
      injection hW with hws hR
      subst hR
      have member : S ∈ ws₁ + ws₂ := by
        rw [hws]
        exact Multiset.mem_cons_self S rest
      rcases Multiset.mem_add.mp member with inLeft | inRight
      · obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem inLeft
        rw [Multiset.cons_add] at hws
        have restIs : t + ws₂ = rest := (Multiset.cons_inj_right S).mp hws
        subst restIs
        exact Or.inl ⟨(⟨S.program, (family (S.program ∪ R)).next S.state choice⟩ : System Tm O) ::ₘ t,
          Fires.fire t R S choice,
          congrArg (fun m => (⟨m, R⟩ : Bag Tm O)) (Multiset.cons_add _ _ _).symm⟩
      · obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem inRight
        rw [Multiset.add_cons] at hws
        have restIs : ws₁ + t = rest := (Multiset.cons_inj_right S).mp hws
        subst restIs
        exact Or.inr ⟨(⟨S.program, (family (S.program ∪ R)).next S.state choice⟩ : System Tm O) ::ₘ t,
          Fires.fire t R S choice,
          congrArg (fun m => (⟨m, R⟩ : Bag Tm O)) (Multiset.add_cons _ _ _).symm⟩

/-- **Every run of firings of the sum of two bags is a pair of runs**, one of each. -/
theorem runs_split {R : Program Tm} {ws₁ ws₂ : Multiset (System Tm O)} {W' : Bag Tm O}
    (run : Relation.ReflTransGen (Fires family) ⟨ws₁ + ws₂, R⟩ W') :
    ∃ a b, W' = ⟨a + b, R⟩ ∧ Relation.ReflTransGen (Fires family) ⟨ws₁, R⟩ ⟨a, R⟩ ∧
      Relation.ReflTransGen (Fires family) ⟨ws₂, R⟩ ⟨b, R⟩ := by
  induction run with
  | refl => exact ⟨ws₁, ws₂, rfl, .refl, .refl⟩
  | tail _ last ih =>
      obtain ⟨a, b, rfl, runLeft, runRight⟩ := ih
      rcases fires_split last with ⟨a', fired, rfl⟩ | ⟨b', fired, rfl⟩
      · exact ⟨a', b, rfl, runLeft.tail fired, runRight⟩
      · exact ⟨a, b', rfl, runLeft, runRight.tail fired⟩

/-- **Reaching the observation by firings alone.** -/
def Reaches (family : LocalSteps Tm O Action) (barb : State Tm O → Prop)
    (W : Bag Tm O) : Prop :=
  ∃ W', Relation.ReflTransGen (Fires family) W W' ∧ Shows barb W'

/-- **Without publication and merge, side by side is a product**: with one space and firings only, the
sum of two bags reaches the observation exactly when one of the two does. -/
theorem product (barb : State Tm O → Prop) (R : Program Tm) (ws₁ ws₂ : Multiset (System Tm O)) :
    Reaches family barb ⟨ws₁ + ws₂, R⟩ ↔ Reaches family barb ⟨ws₁, R⟩ ∨ Reaches family barb ⟨ws₂, R⟩ := by
  constructor
  · rintro ⟨W', run, shows⟩
    obtain ⟨a, b, rfl, runLeft, runRight⟩ := runs_split run
    obtain ⟨S, member, holds⟩ := shows
    rcases Multiset.mem_add.mp member with inLeft | inRight
    · exact Or.inl ⟨⟨a, R⟩, runLeft, S, inLeft, holds⟩
    · exact Or.inr ⟨⟨b, R⟩, runRight, S, inRight, holds⟩
  · rintro (⟨W', run, S, member, holds⟩ | ⟨W', run, S, member, holds⟩)
    · exact ⟨⟨W'.worlds + ws₂, W'.space⟩, runs_add_right run ws₂, S,
        Multiset.mem_add.mpr (Or.inl member), holds⟩
    · exact ⟨⟨ws₁ + W'.worlds, W'.space⟩, runs_add_left run ws₁, S,
        Multiset.mem_add.mpr (Or.inr member), holds⟩

section Moves

variable {Hom : Obj → Obj → Type uH} [DecidableEq O] (X : Frames Tm Hom) (J : Joining X O)

/-- A run of firings is a run of moves. -/
theorem moves_of_fires {W W' : Bag Tm O}
    (run : Relation.ReflTransGen (Fires family) W W') : Relation.ReflTransGen (Move X J family) W W' := by
  induction run with
  | refl => exact .refl
  | tail _ last ih => exact ih.tail (Fires.move X J last)

/-- **What firings reach, the moves reach.** -/
theorem reaches_succeeds (barb : State Tm O → Prop) {W : Bag Tm O}
    (reaches : Reaches family barb W) : (bagParallel X J family barb).Succeeds W := by
  obtain ⟨W', run, shows⟩ := reaches
  exact ⟨W', moves_of_fires X J run, shows⟩

end Moves

#print axioms Fires.move
#print axioms Fires.space_eq
#print axioms fires_split
#print axioms runs_split
#print axioms product
#print axioms reaches_succeeds

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds
