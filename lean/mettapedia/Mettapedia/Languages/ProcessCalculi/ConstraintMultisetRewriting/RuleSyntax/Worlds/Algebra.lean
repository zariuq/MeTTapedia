import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds.Sharing

/-!
# The merge distributes over side by side, through a copy

A bag of worlds has two ways of putting worlds together: side by side (`Bag.beside`, the sum of the
bags), and the merge of two worlds into one (`Move.merge`, by a joining). They are related as a sum
and a product are.

* **`merge_distributes`**: a world `c` is merged with each of two worlds `a` and `b` that are side by
  side by one copy of `c` and two merges, when both joint knowledges are solvable: from `a`, `b` and
  `c` side by side the bag reaches the merge of `a` with `c` side by side with the merge of `b` with
  `c`.

The other laws are in `Worlds.Bag` and `Worlds.Confinement`: side by side is commutative and
associative with the empty bag as unit, and worlds cancel; a world whose knowledge has no solution is
a unit of side by side for reachable success (`dead_world_is_no_neighbour`) and is absorbing for the
merge (`Joining.left_alive`, `Joining.right_alive`: a merge with it is never admitted).
-/

set_option autoImplicit false

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence (System)

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds

open Interface (Frames)

universe uO uT uH uE uOcc

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH} {O : Type uOcc}
  [DecidableEq O] {X : Frames Tm Hom} {E : Extensions.{uO, uH, uE} Hom} {J : Joining X O}

omit [DecidableEq O] in
/-- Bags with equal bags of worlds and the same space. -/
theorem bag_of_worlds_eq {ws ws' : Multiset (System Tm O)} (same : ws = ws') (R : Program Tm) :
    (⟨ws, R⟩ : Bag Tm O) = ⟨ws', R⟩ :=
  congrArg (fun m => (⟨m, R⟩ : Bag Tm O)) same

/-- **The merge distributes over side by side, through a copy**: from `a`, `b` and `c` side by side,
the bag reaches the merge of `a` with `c` side by side with the merge of `b` with `c`, by one copy of
`c` and two merges, when both joint knowledges are solvable. -/
theorem merge_distributes (rest : Multiset (System Tm O)) (R : Program Tm) (a b c : System Tm O)
    (aliveA : X.Solvable (J.join a.state c.state).knowledge)
    (aliveB : X.Solvable (J.join b.state c.state).knowledge) :
    Relation.ReflTransGen (Move X J (events X O E)) ⟨a ::ₘ b ::ₘ c ::ₘ rest, R⟩
      ⟨(⟨a.program ∪ c.program, J.join a.state c.state⟩ : System Tm O) ::ₘ
        (⟨b.program ∪ c.program, J.join b.state c.state⟩ : System Tm O) ::ₘ rest, R⟩ := by
  have copied : Move X J (events X O E) ⟨a ::ₘ b ::ₘ c ::ₘ rest, R⟩ ⟨a ::ₘ c ::ₘ c ::ₘ b ::ₘ rest, R⟩ :=
    Move.cast (Move.fork (family := events X O E) (a ::ₘ b ::ₘ rest) R c)
      (bag_of_worlds_eq ((Multiset.cons_swap c a (b ::ₘ rest)).trans
        (congrArg (fun m => a ::ₘ m) (Multiset.cons_swap c b rest))) R)
      (bag_of_worlds_eq ((congrArg (fun m => c ::ₘ m) (Multiset.cons_swap c a (b ::ₘ rest))).trans
        (Multiset.cons_swap c a (c ::ₘ b ::ₘ rest))) R)
  have first : Move X J (events X O E) ⟨a ::ₘ c ::ₘ c ::ₘ b ::ₘ rest, R⟩
      ⟨(⟨a.program ∪ c.program, J.join a.state c.state⟩ : System Tm O) ::ₘ c ::ₘ b ::ₘ rest, R⟩ :=
    Move.merge (family := events X O E) (c ::ₘ b ::ₘ rest) R a c aliveA
  have second : Move X J (events X O E)
      ⟨(⟨a.program ∪ c.program, J.join a.state c.state⟩ : System Tm O) ::ₘ c ::ₘ b ::ₘ rest, R⟩
      ⟨(⟨a.program ∪ c.program, J.join a.state c.state⟩ : System Tm O) ::ₘ
        (⟨b.program ∪ c.program, J.join b.state c.state⟩ : System Tm O) ::ₘ rest, R⟩ :=
    Move.cast
      (Move.merge (family := events X O E) ((⟨a.program ∪ c.program, J.join a.state c.state⟩ : System Tm O) ::ₘ rest) R b c
        aliveB)
      (bag_of_worlds_eq ((congrArg (fun m => b ::ₘ m) (Multiset.cons_swap c _ rest)).trans
        ((Multiset.cons_swap b _ (c ::ₘ rest)).trans
          (congrArg (fun m => _ ::ₘ m) (Multiset.cons_swap b c rest)))) R)
      (bag_of_worlds_eq (Multiset.cons_swap _ _ rest) R)
  exact ((Relation.ReflTransGen.single copied).tail first).tail second

#print axioms merge_distributes

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds
