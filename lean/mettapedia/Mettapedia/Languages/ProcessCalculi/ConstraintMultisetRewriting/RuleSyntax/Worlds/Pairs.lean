import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds.Events
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds.Product

/-!
# Two worlds of a bag fire as the asynchronous composition of their steps

The tree puts two systems of events side by side, with nothing shared, by
`Interface.EventMultiplicity.asynchronous`. This module says that the firings of a bag of two worlds
with a fixed space are that composition, of the steps of the two programs with the space.

* `one_world_fires`: the firing moves of a bag of one world with the space `R` are the admitted
  firings of the world's program with `R`: the events of `events X O E (P ∪ R)`.
* `pairBag`, **`pair_fires_iff`**: the firing moves of the bag of two worlds are the events of the
  asynchronous composition of the two steps, through the map of a pair of states to the bag.

With `dead_beside_bisimilar` (a world with unsolvable knowledge beside any system of events is not
there, counting events), confinement is a statement about that composition.
-/

set_option autoImplicit false

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence (System)

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds

open Interface (Frames)
open Interface.EventMultiplicity (asynchronous)

universe uO uT uH uE uOcc

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH} {O : Type uOcc}
  [DecidableEq O] {X : Frames Tm Hom} {E : Extensions.{uO, uH, uE} Hom}

/-- **The firings of one world**: the firing moves of a bag of one world are the admitted firings of
its rules with the space. -/
theorem one_world_fires (S : System Tm O) (R : Program Tm) (W' : Bag Tm O) :
    Fires (events X O E) ⟨{S}, R⟩ W' ↔
      ∃ f : Firing O E (S.program ∪ R) S.state.frame, f.Admits X S.state ∧
        W' = ⟨{(⟨S.program, f.result X S.state⟩ : System Tm O)}, R⟩ := by
  constructor
  · intro fires
    generalize hW : (⟨{S}, R⟩ : Bag Tm O) = W at fires
    cases fires with
    | fire rest space S₀ choice =>
        obtain ⟨f, admitted⟩ := choice
        injection hW with hws hR
        obtain ⟨rfl, rfl⟩ := (Multiset.singleton_eq_cons_iff rest).mp hws
        subst hR
        exact ⟨f, admitted, rfl⟩
  · rintro ⟨f, admitted, rfl⟩
    exact Fires.fire (family := events X O E) 0 R S ⟨f, admitted⟩

/-- The bag of two worlds with the given rules, the given pair of states, and the given space. -/
def pairBag (P₁ P₂ R : Program Tm) (p : State Tm O × State Tm O) : Bag Tm O :=
  ⟨{(⟨P₁, p.1⟩ : System Tm O)} + {(⟨P₂, p.2⟩ : System Tm O)}, R⟩

/-- **Two worlds of a bag fire as the asynchronous composition of their steps**: the firing moves of
the bag of two worlds are the events of the asynchronous composition of the steps of the two programs
with the space, and each reaches the bag of the next pair of states. -/
theorem pair_fires_iff (P₁ P₂ R : Program Tm) (p : State Tm O × State Tm O) (W' : Bag Tm O) :
    Fires (events X O E) (pairBag P₁ P₂ R p) W' ↔
      ∃ c : (asynchronous (events X O E (P₁ ∪ R)) (events X O E (P₂ ∪ R))).Choice p,
        W' = pairBag P₁ P₂ R
          ((asynchronous (events X O E (P₁ ∪ R)) (events X O E (P₂ ∪ R))).next p c) := by
  constructor
  · intro fires
    rcases fires_split fires with ⟨ws', fired, rfl⟩ | ⟨ws', fired, rfl⟩
    · obtain ⟨f, admitted, same⟩ := (one_world_fires _ R _).mp fired
      injection same with hws _
      subst hws
      exact ⟨Sum.inl ⟨f, admitted⟩, rfl⟩
    · obtain ⟨f, admitted, same⟩ := (one_world_fires _ R _).mp fired
      injection same with hws _
      subst hws
      exact ⟨Sum.inr ⟨f, admitted⟩, rfl⟩
  · rintro ⟨c | c, rfl⟩
    · exact Fires.add_right (Fires.fire (family := events X O E) 0 R ⟨P₁, p.1⟩ c) {(⟨P₂, p.2⟩ : System Tm O)}
    · exact Fires.add_left (Fires.fire (family := events X O E) 0 R ⟨P₂, p.2⟩ c) {(⟨P₁, p.1⟩ : System Tm O)}

#print axioms one_world_fires
#print axioms pair_fires_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds
