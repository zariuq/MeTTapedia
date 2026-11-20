import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Locality
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Representation.Characterization

/-!
# The step of a finite program has finitely many results, found in a bounded search

At the one first-order frame over rows with unknowns, for a finite list of range-restricted rules and a bag of
ground rows:

* **Finitely many successors** (`successors_finite`): the bags the list rewrites the bag to form a finite set.
  The proof gives the search space: a rule of the list, a list of rows of the bag for its take patterns and a
  list of rows of the bag for its read patterns. At each point of that space there is at most one successor
  (`successorsAt_subsingleton`): the instances of the takes and reads fix every unknown they bind, and by range
  restriction the made rows mention no other unknown. Whether a point has a successor is first-order matching
  of the rule's patterns against the chosen rows, with its equations; this module proves the finiteness and the
  bound, and gives no matching function.
* **On the step** (`results_finite`): at a state that reads as a bag, the results of the admitted firings of a
  finite range-restricted positive program read as finitely many bags. What a result does not read is not
  counted: the made identities, the opening, and which of several identities carrying the same row is taken.
  `selections_finite` (in the module `Locality`) counts the firings themselves, for one rule, one opening and
  one choice of made identities.

So a relation with infinitely many successors of one bag is the rewriting of no finite list of range-restricted
rules (`infinitely_branching_not_finite`).

## Controls

* Range restriction is needed (`unrestricted_infinite`): the rule that takes nothing and makes an unknown has
  every one-row bag as a successor of the empty bag. On the step such a made row is read by no solution
  (`Presentation.Schematic.Boundary`).
* A program of any size may branch infinitely: the oracle construction of `Characterization` presents every
  frame-closed relation, among them `Rewrites [freeMake]`, with infinitely many ground rules
  (`guess_presented`), and no finite list of range-restricted rules does (`guess_not_finite`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Representation

open Mettapedia.Logic.LP
open Interface (Frames)
open NamesOnTheStep (Expr)
open LogicOverTheStep.ProgramAdequacy (listsOver listsOver_finite)
open Presentation.Schematic
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines

universe uO

/-! ## The search space, and one successor at each of its points -/

/-- **The successors of a bag by a rule at chosen rows**: the bags the rule rewrites the bag to at the
instantiations that send its takes and its reads to the chosen rows. -/
def successorsAt (r : SRule) (M : Multiset Expr) (takes reads : List Expr) : Set (Multiset Expr) :=
  {M' | ∃ θ : ℕ → Expr, r.body.take.map (inst θ) = takes ∧ r.body.read.map (inst θ) = reads ∧
    M' = (r.body.produce.map (inst θ) : Multiset Expr) + (M - (takes : Multiset Expr))}

/-- **At chosen rows a range-restricted rule has at most one successor.** -/
theorem successorsAt_subsingleton {r : SRule} (restricted : RangeRestricted r) (M : Multiset Expr)
    (takes reads : List Expr) : (successorsAt r M takes reads).Subsingleton := by
  rintro _ ⟨θ, takesθ, readsθ, rfl⟩ _ ⟨θ', takesθ', readsθ', rfl⟩
  have agree : ∀ x, Bound r x → θ x = θ' x := by
    rintro x ⟨t, member, vars⟩
    rcases List.mem_append.mp member with inTake | inRead
    · exact agree_of_inst_eq t (List.map_inj_left.mp (takesθ.trans takesθ'.symm) t inTake) x vars
    · exact agree_of_inst_eq t (List.map_inj_left.mp (readsθ.trans readsθ'.symm) t inRead) x vars
  have same : r.body.produce.map (inst θ) = r.body.produce.map (inst θ') :=
    List.map_congr_left fun t member => inst_congr t fun x vars =>
      agree x (restricted t (mem_written_of_produce member) x vars)
  rw [same]

/-! ## Finitely many successors -/

/-- **A finite list of range-restricted rules rewrites a bag to finitely many bags.** -/
theorem successors_finite (rules : List SRule) (restricted : ∀ r ∈ rules, RangeRestricted r)
    (M : Multiset Expr) : {M' | Rewrites rules M M'}.Finite := by
  have inner : ∀ r ∈ {r | r ∈ rules}, (⋃ p ∈ (listsOver M.toFinset r.body.take.length) ×ˢ
      (listsOver M.toFinset r.body.read.length), successorsAt r M p.1 p.2).Finite := fun r member =>
    ((listsOver_finite _ _).prod (listsOver_finite _ _)).biUnion fun p _ =>
      (successorsAt_subsingleton (restricted r member) M p.1 p.2).finite
  refine ((List.finite_toSet rules).biUnion inner).subset ?_
  rintro M' ⟨r, member, θ, rest, split, readsIn, -, rfl⟩
  have inBag : ∀ x ∈ rest, x ∈ M.toFinset := fun x inside => by
    rw [Multiset.mem_toFinset, ← split]
    exact Multiset.mem_add.mpr (Or.inr inside)
  refine Set.mem_iUnion₂.mpr ⟨r, member, Set.mem_iUnion₂.mpr
    ⟨(r.body.take.map (inst θ), r.body.read.map (inst θ)), ⟨⟨List.length_map .., ?_⟩, ⟨List.length_map .., ?_⟩⟩,
      θ, rfl, rfl, ?_⟩⟩
  · intro x inside
    rw [Multiset.mem_toFinset, ← split]
    exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_coe.mpr inside))
  · intro x inside
    obtain ⟨q, inRead, rfl⟩ := List.mem_map.mp inside
    exact inBag _ (readsIn q inRead)
  · show ((r.body.produce.map (inst θ) : List Expr) : Multiset Expr) + rest =
      ((r.body.produce.map (inst θ) : List Expr) : Multiset Expr) +
        (M - ((r.body.take.map (inst θ) : List Expr) : Multiset Expr))
    rw [← split, add_tsub_cancel_left]

/-- **On the step**: at a state that reads as a bag, the results of the admitted firings of a finite
range-restricted positive program read as finitely many bags. -/
theorem results_finite {O : Type uO} [DecidableEq O] (rules : List SRule)
    (fragment : ∀ r ∈ rules, RangeRestrictedPositive r) {s : SState O} {M : Multiset Expr}
    (reads : ReadsBag s M) :
    {bag' | ∃ (g : Firing O E {r | r ∈ rules} s.frame)
        (admitted : (schematicStep O rules).Admits (s := s) g),
        ReadsBag ((schematicStep O rules).result g admitted) bag'}.Finite := by
  refine (successors_finite rules (fun r member => (fragment r member).2.2) M).subset ?_
  rintro bag' ⟨g, admitted, reads'⟩
  obtain ⟨bag'', rewrites, readsToo⟩ := readsBag_backward fragment reads g admitted
  have same : bag'' = bag' :=
    readsAs_unique (ReadsBag.readsAs readsToo).1 (ReadsBag.readsAs readsToo).2 (ReadsBag.readsAs reads').2
  rw [← same]
  exact rewrites

/-- **A relation with infinitely many successors of one bag is the rewriting of no finite list of
range-restricted rules.** -/
theorem infinitely_branching_not_finite {R : Multiset Expr → Multiset Expr → Prop} {M : Multiset Expr}
    (branching : {M' | R M M'}.Infinite) :
    ¬ ∃ rules : List SRule, (∀ r ∈ rules, RangeRestricted r) ∧ ∀ M M', Rewrites rules M M' ↔ R M M' := by
  rintro ⟨rules, restricted, same⟩
  apply branching
  refine (successors_finite rules restricted M).subset ?_
  intro M' related
  exact (same M M').mpr related

/-! ## Controls -/

/-- The rule that takes nothing and makes an unknown row. -/
def freeMake : SRule := ⟨PUnit.unit, ⟨[], [], [], [], [.var 0]⟩, []⟩

/-- **Range restriction is needed**: the rule that makes an unknown rewrites the empty bag to every one-row
bag of a constant. -/
theorem unrestricted_infinite : {M' | Rewrites [freeMake] 0 M'}.Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => ({Expr.sym k} : Multiset Expr)) ?_ ?_
  · intro j k same
    exact Expr.sym.inj (Multiset.singleton_inj.mp same)
  · intro k
    exact ⟨freeMake, List.mem_singleton_self _, fun _ => .sym k, 0, add_zero _,
      fun q member => absurd member List.not_mem_nil, fun e member => absurd member List.not_mem_nil,
      (add_zero _).symm⟩

/-- **A program of any size may branch infinitely**: that relation is rewriting by a set of positive ground
rules. -/
theorem guess_presented :
    ∃ P : Program (OneFrame.Terms Tm), (∀ r ∈ P, RangeRestrictedPositive r) ∧
      ∀ M M', SetRewrites P M M' ↔ Rewrites [freeMake] M M' :=
  (presented_iff_frameClosed _).mpr fun _ _ N related => rewrites_frame N related

/-- **No finite list of range-restricted rules does.** -/
theorem guess_not_finite :
    ¬ ∃ rules : List SRule, (∀ r ∈ rules, RangeRestricted r) ∧
      ∀ M M', Rewrites rules M M' ↔ Rewrites [freeMake] M M' :=
  infinitely_branching_not_finite (R := Rewrites [freeMake]) (M := 0) unrestricted_infinite

#print axioms successorsAt_subsingleton
#print axioms successors_finite
#print axioms results_finite
#print axioms infinitely_branching_not_finite
#print axioms unrestricted_infinite
#print axioms guess_presented
#print axioms guess_not_finite

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Representation
