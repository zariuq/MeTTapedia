import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualArgumentCodings

/-!
# Authored integer reading dictionaries

Integer readings retain the sign and natural magnitude through distinct
material tags. Named readings retain their declared field as well as the
integer value. Injectivity is proved from material pairing and finite chains;
no inverse enumeration or arithmetic pairing decoder is selected.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.DiscreteReadingCodings

open Mettapedia.TypeTheory.MaterialSets.Hypersets

def integerGraph : Int → AccessiblePointedGraph
  | .ofNat magnitude => AccessiblePointedGraph.kpairGraph AccessiblePointedGraph.empty
      (OutcomeLabels.chainGraph magnitude)
  | .negSucc magnitude => AccessiblePointedGraph.kpairGraph
      (AccessiblePointedGraph.singletonGraph AccessiblePointedGraph.empty)
      (OutcomeLabels.chainGraph magnitude)

theorem integerGraph_injective : Function.Injective (fun value => HSet.mk (integerGraph value)) := by
  intro first second same
  cases first with
  | ofNat first =>
      cases second with
      | ofNat second =>
          change HSet.mk (AccessiblePointedGraph.kpairGraph _ _) =
            HSet.mk (AccessiblePointedGraph.kpairGraph _ _) at same
          simp only [AccessiblePointedGraph.mk_kpairGraph, HSet.mk_empty, OutcomeLabels.mk_chainGraph] at same
          exact congrArg Int.ofNat (OutcomeLabels.chainValue_injective (HSet.kpair_inj.mp same).2)
      | negSucc second =>
          change HSet.mk (AccessiblePointedGraph.kpairGraph _ _) =
            HSet.mk (AccessiblePointedGraph.kpairGraph _ _) at same
          simp only [AccessiblePointedGraph.mk_kpairGraph, AccessiblePointedGraph.mk_singletonGraph,
            HSet.mk_empty] at same
          exact (HSet.empty_ne_singleton_empty (HSet.kpair_inj.mp same).1).elim
  | negSucc first =>
      cases second with
      | ofNat second =>
          change HSet.mk (AccessiblePointedGraph.kpairGraph _ _) =
            HSet.mk (AccessiblePointedGraph.kpairGraph _ _) at same
          simp only [AccessiblePointedGraph.mk_kpairGraph, AccessiblePointedGraph.mk_singletonGraph,
            HSet.mk_empty] at same
          exact (HSet.empty_ne_singleton_empty (HSet.kpair_inj.mp same).1.symm).elim
      | negSucc second =>
          change HSet.mk (AccessiblePointedGraph.kpairGraph _ _) =
            HSet.mk (AccessiblePointedGraph.kpairGraph _ _) at same
          simp only [AccessiblePointedGraph.mk_kpairGraph, AccessiblePointedGraph.mk_singletonGraph,
            HSet.mk_empty, OutcomeLabels.mk_chainGraph] at same
          exact congrArg Int.negSucc (OutcomeLabels.chainValue_injective (HSet.kpair_inj.mp same).2)

def integers : ArgumentCoding Int := ⟨integerGraph, integerGraph_injective⟩

def namedIntegers {Name : Type} (names : ArgumentCoding Name) : ArgumentCoding (Name × Int) where
  graph reading := AccessiblePointedGraph.kpairGraph (names.graph reading.1) (integerGraph reading.2)
  injective := by
    intro first second same
    change HSet.mk (AccessiblePointedGraph.kpairGraph (names.graph first.1) (integerGraph first.2)) =
      HSet.mk (AccessiblePointedGraph.kpairGraph (names.graph second.1) (integerGraph second.2)) at same
    rw [AccessiblePointedGraph.mk_kpairGraph, AccessiblePointedGraph.mk_kpairGraph] at same
    exact Prod.ext (names.injective (HSet.kpair_inj.mp same).1)
      (integerGraph_injective (HSet.kpair_inj.mp same).2)

theorem infinitely_many_nonnegative_readings : Function.Injective
    (fun magnitude : Nat => integers.reading (.ofNat magnitude)) := by
  intro first second same
  exact Int.ofNat.inj (integers.injective same)

theorem negative_and_zero_differ : integers.reading (-1) ≠ integers.reading 0 := by
  intro same
  exact Int.noConfusion (integers.injective same)

theorem distinct_fields_differ {Name : Type} (names : ArgumentCoding Name)
    (first second : Name) (different : first ≠ second) (value : Int) :
    (namedIntegers names).reading (first, value) ≠ (namedIntegers names).reading (second, value) :=
  fun same => different (congrArg Prod.fst ((namedIntegers names).injective same))

end Mettapedia.GSLT.DiscreteReadingCodings
