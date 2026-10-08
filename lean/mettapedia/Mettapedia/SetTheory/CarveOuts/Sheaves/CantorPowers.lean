import Mettapedia.SetTheory.CarveOuts.Sheaves.Representability
import Mettapedia.SetTheory.CarveOuts.Sheaves.Naturals
import Mettapedia.SetTheory.CarveOuts.Sheaves.Cantor

/-!
# The basic small-map axioms on sheaves over Cantor space

**One universe up, in the host theory.** For sheaves of sets on a space whose open sets form a
`w`-small type, with values in a universe above `w`, the small maps satisfy
(S1)–(S5), (P1), (I) and (R)
(`sheaf_basicSmallMapAxioms_of_small`). Cantor space lifted to the universe `w + 1`
(`CantorUp`) is such a space (`cantorUp_opens_small`), so its sheaves satisfy
`BasicSmallMapAxioms` with no named hypothesis (`cantorUp_basicSmallMapAxioms`), as well
as (M) and collection. Host choice occurs in these constructions. The ambient categorical
structure and the indexed final-coalgebra construction remain separate obligations; this
module does not construct that coalgebra or interpret its material set axioms. The bundle was
first named after the final coalgebra; it holds the basic small-map axioms only.

* The class is not every map: on `CantorUp` the map to the terminal sheaf from the sheaf of
  functions into `Type w` is not small (`cantorUp_not_all_small`).

**Not in the universe of the space.** For Cantor space `ℕ → Bool : Type`, sheaves of sets take
values in `Type`, every type of which is `w`-small. So every map is small
(`cantor_sheafSmall_all`), power classes and the smallness of the natural numbers hold in the
degenerate form of a class of all maps, and representability fails by Cantor's theorem
(`cantor_sheaf_not_representable`). In particular `cantor_sheaf_basicSmallMapAxioms` of
`Sheaves.Cantor`, which assumes (R) for these sheaves, has an unsatisfiable hypothesis
(`cantor_sheaf_not_basicSmallMapAxioms`).
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.CarveOuts.Sheaves

open CategoryTheory Limits TopologicalSpace Opposite
open Mettapedia.SetTheory.CarveOuts.Sites.SmallMaps

universe w u

/-! ## Any space with small open sets, one universe up -/

/-- The small-map axioms (S1)–(S5), (P1), (I) and (R) for sheaves on a space whose open sets
form a `w`-small type, with values in a universe above `w`. -/
theorem sheaf_basicSmallMapAxioms_of_small {X : Type (max u (w + 1))} [TopologicalSpace X]
    [Small.{w} (Opens X)] :
    BasicSmallMapAxioms (sheafSmall.{w} : MorphismProperty (SheafOn X)) :=
  ⟨sheafSmall_smallMapClass, sheafSmall_powerClassAxiom, sheafSmall_naturalsSmall,
    sheafSmall_representable⟩

/-! ## Cantor space one universe up -/

/-- Cantor space, in the universe `w + 1`. -/
abbrev CantorUp : Type (w + 1) :=
  ULift.{w + 1} (ℕ → Bool)

/-- The open sets of the lifted Cantor space form a `w`-small type. -/
instance cantorUp_opens_small : Small.{w} (Opens CantorUp.{w}) :=
  small_of_injective (Homeomorph.ulift.opensCongr).injective

/-- Sheaves on Cantor space, one universe up, satisfy the small-map package without
additional hypotheses beyond the host theory. -/
theorem cantorUp_basicSmallMapAxioms :
    BasicSmallMapAxioms (sheafSmall.{w} : MorphismProperty (SheafOn CantorUp.{w})) :=
  sheaf_basicSmallMapAxioms_of_small.{w, 0}

/-- (M) on sheaves over the lifted Cantor space. -/
theorem cantorUp_monosSmall :
    MonosSmall (sheafSmall.{w} : MorphismProperty (SheafOn CantorUp.{w})) :=
  sheafSmall_monosSmall

/-- Collection on sheaves over the lifted Cantor space, with host choice. -/
theorem cantorUp_collection_of_choice :
    CollectionAxiom (sheafSmall.{w} : MorphismProperty (SheafOn CantorUp.{w})) :=
  sheafSmall_collection_of_choice

/-- **Control: not every map is small.** The functions from the points of the lifted Cantor space
into `Type w` form a sheaf whose map to the terminal sheaf has a fibre that is not `w`-small. -/
theorem cantorUp_not_all_small :
    ¬ sheafSmall.{w} (terminal.from (funSheaf (X := CantorUp.{w}) (Type w))) := by
  intro h
  obtain ⟨pt⟩ := terminal_sections_nonempty (X := CantorUp.{w}) ⊤
  have := h (op ⊤) pt
  apply not_small_type.{w, w}
  refine small_of_injective
    (β := {y // (terminal.from (funSheaf (X := CantorUp.{w}) (Type w))).hom.app (op ⊤) y = pt})
    (f := fun α => ⟨fun _ => α, @Subsingleton.elim _ (terminal_sections_subsingleton _) _ _⟩) ?_
  intro α β e
  exact congrFun (congrArg Subtype.val e) ⟨ULift.up fun _ => true, trivial⟩

/-! ## Cantor space in the universe of its points -/

/-- With values in `Type`, every map of sheaves over Cantor space is small. -/
theorem cantor_sheafSmall_all {A B : SheafOn (ℕ → Bool)} (f : A ⟶ B) : sheafSmall.{w} f :=
  fun _ _ => inferInstance

/-- (P1) on sheaves over Cantor space with values in `Type`: power objects, every map being
small. -/
theorem cantor_sheaf_powerClassAxiom :
    PowerClassAxiom (sheafSmall.{w} : MorphismProperty (SheafOn (ℕ → Bool))) :=
  sheafSmall_powerClassAxiom

/-- (I) on sheaves over Cantor space with values in `Type`. -/
theorem cantor_sheaf_naturalsSmall :
    NaturalsSmallAxiom (sheafSmall.{w} : MorphismProperty (SheafOn (ℕ → Bool))) :=
  sheafSmall_naturalsSmall

/-- **(R) fails on sheaves over Cantor space with values in `Type`.** -/
theorem cantor_sheaf_not_representable :
    ¬ RepresentabilityAxiom (sheafSmall.{w} : MorphismProperty (SheafOn (ℕ → Bool))) :=
  sheafSmall_not_representable_of_univLE.{w, 0}

/-- **The basic small-map axioms fail on sheaves over Cantor space with values in `Type`**: the
hypothesis (R) of `cantor_sheaf_basicSmallMapAxioms` cannot be met. -/
theorem cantor_sheaf_not_basicSmallMapAxioms :
    ¬ BasicSmallMapAxioms (sheafSmall.{w} : MorphismProperty (SheafOn (ℕ → Bool))) :=
  fun h => cantor_sheaf_not_representable h.representable

end Mettapedia.SetTheory.CarveOuts.Sheaves
