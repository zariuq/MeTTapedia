import Mettapedia.OSLF.Syntax.CartesianModelLexEventInterpretations
import Mettapedia.OSLF.Syntax.CartesianModelLexPresheafFullness
import Mettapedia.OSLF.Syntax.VaryingEventObservations

/-!
# Chosen reduction predicates over relative context interpretations

The authored and finite-limit context interpretation categories already
retain individual event objects and endpoint maps. Each now has a category of
chosen reduction subobjects containing those endpoints. This construction
needs no images: an image requirement is a separate doctrine on suitable
targets. A map of observed interpretations preserves the base context map,
the event map and the chosen reduction predicate.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.CartesianContextModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.OSLF.Binding.VaryingEventObservations

universe uD vD

/-- The event object and paired program endpoint object vary together with
an authored product-context interpretation. -/
noncomputable def authoredEventDiagram
    (C : Type) [SmallCategory C] [HasFiniteProducts C]
    (D : Type uD) [Category.{vD} D] [HasFiniteLimits D]
    (program : C) :
    EventDiagram (AuthoredEventInterpretations C D program) D where
  events := Comma.fst (𝟭 D) (authoredProgramPair C D program)
  pairs := Comma.snd (𝟭 D) (authoredProgramPair C D program) ⋙
    authoredProgramPair C D program
  endpoints :=
    { app := fun X => X.hom
      naturality := by
        intro X Y f
        change f.left ≫ Y.hom = X.hom ≫
          (authoredProgramPair C D program).map f.right
        exact f.w }

/-- The corresponding diagram after relative finite-limit completion of
the authored context category. -/
noncomputable def leftExactEventDiagram
    (C : Type) [SmallCategory C] [HasFiniteProducts C]
    (D : Type uD) [Category.{vD} D] [HasFiniteLimits D]
    (program : C) :
    EventDiagram (LeftExactEventInterpretations C D program) D where
  events := Comma.fst (𝟭 D)
    (restrictLeftExactTarget C D ⋙ authoredProgramPair C D program)
  pairs := Comma.snd (𝟭 D)
      (restrictLeftExactTarget C D ⋙ authoredProgramPair C D program) ⋙
    (restrictLeftExactTarget C D ⋙ authoredProgramPair C D program)
  endpoints :=
    { app := fun X => X.hom
      naturality := by
        intro X Y f
        change f.left ≫ Y.hom = X.hom ≫
          (restrictLeftExactTarget C D ⋙
            authoredProgramPair C D program).map f.right
        exact f.w }

/-- An authored context interpretation with retained firing events and a
chosen reduction predicate. The event object is part of its base model,
independently of the predicate. -/
abbrev AuthoredObservedInterpretations
    (C : Type) [SmallCategory C] [HasFiniteProducts C]
    (D : Type uD) [Category.{vD} D] [HasFiniteLimits D]
    (program : C) :=
  Observation (authoredEventDiagram C D program)

/-- The analogous structure over relative finite-limit interpretations. -/
abbrev LeftExactObservedInterpretations
    (C : Type) [SmallCategory C] [HasFiniteProducts C]
    (D : Type uD) [Category.{vD} D] [HasFiniteLimits D]
    (program : C) :=
  Observation (leftExactEventDiagram C D program)

/-- The event and endpoint diagrams of the finite-limit interpretation are
the pullback of the authored diagram along the established restriction
equivalence. This is the coherence condition needed to lift observations. -/
theorem leftExactEventDiagram_eq_reindex
    (C : Type) [SmallCategory C] [HasFiniteProducts C]
    (D : Type) [SmallCategory D] [HasFiniteLimits D]
    (program : C) :
    leftExactEventDiagram C D program =
      (authoredEventDiagram C D program).reindex
        (eventInterpretationEquivalence C D program).functor := by
  have eventEq : (leftExactEventDiagram C D program).events =
      ((authoredEventDiagram C D program).reindex
        (eventInterpretationEquivalence C D program).functor).events := by
    rfl
  have pairEq : (leftExactEventDiagram C D program).pairs =
      ((authoredEventDiagram C D program).reindex
        (eventInterpretationEquivalence C D program).functor).pairs := by
    rfl
  apply EventDiagram.ext eventEq pairEq
  apply heq_of_eq
  apply NatTrans.ext
  funext X
  simp [leftExactEventDiagram, EventDiagram.reindex,
    authoredEventDiagram, eventInterpretationEquivalence,
    liftEventInterpretationEquivalence, Functor.asEquivalence,
    Comma.map, Functor.rightUnitor]

/-- Relative finite-limit completion classifies interpretations carrying
both individual firing events and a chosen reduction predicate, provided
the interpretation maps preserve that predicate. The target need not have
images: this theorem does not identify the predicate with an image. -/
noncomputable def observedInterpretationEquivalence
    (C : Type) [SmallCategory C] [HasFiniteProducts C]
    (D : Type) [SmallCategory D] [HasFiniteLimits D]
    (program : C) :
    LeftExactObservedInterpretations C D program ≌
      AuthoredObservedInterpretations C D program := by
  change Observation (leftExactEventDiagram C D program) ≌
    Observation (authoredEventDiagram C D program)
  rw [leftExactEventDiagram_eq_reindex C D program]
  exact (reindexFunctor (authoredEventDiagram C D program)
    (eventInterpretationEquivalence C D program).functor).asEquivalence

/-- The same observed comparison in a presheaf target, which is generally
large and contains the canonical proof-relevant operational models. -/
theorem presheafLeftExactEventDiagram_eq_reindex
    (C : Type) [SmallCategory C] [HasFiniteProducts C]
    (B : Type) [SmallCategory B] (program : C) :
    leftExactEventDiagram C (Bᵒᵖ ⥤ Type) program =
      (authoredEventDiagram C (Bᵒᵖ ⥤ Type) program).reindex
        (presheafEventInterpretationEquivalence C B program).functor := by
  have eventEq : (leftExactEventDiagram C (Bᵒᵖ ⥤ Type) program).events =
      ((authoredEventDiagram C (Bᵒᵖ ⥤ Type) program).reindex
        (presheafEventInterpretationEquivalence C B program).functor).events := by
    rfl
  have pairEq : (leftExactEventDiagram C (Bᵒᵖ ⥤ Type) program).pairs =
      ((authoredEventDiagram C (Bᵒᵖ ⥤ Type) program).reindex
        (presheafEventInterpretationEquivalence C B program).functor).pairs := by
    rfl
  apply EventDiagram.ext eventEq pairEq
  apply heq_of_eq
  apply NatTrans.ext
  funext X
  simp [leftExactEventDiagram, EventDiagram.reindex,
    authoredEventDiagram, presheafEventInterpretationEquivalence,
    liftEventInterpretationEquivalence, Functor.asEquivalence,
    Comma.map, Functor.rightUnitor]

/-- Observed interpretation equivalence also holds for presheaf targets,
without treating those large categories as small. -/
noncomputable def presheafObservedInterpretationEquivalence
    (C : Type) [SmallCategory C] [HasFiniteProducts C]
    (B : Type) [SmallCategory B] (program : C) :
    LeftExactObservedInterpretations C (Bᵒᵖ ⥤ Type) program ≌
      AuthoredObservedInterpretations C (Bᵒᵖ ⥤ Type) program := by
  change Observation (leftExactEventDiagram C (Bᵒᵖ ⥤ Type) program) ≌
    Observation (authoredEventDiagram C (Bᵒᵖ ⥤ Type) program)
  rw [presheafLeftExactEventDiagram_eq_reindex C B program]
  exact (reindexFunctor (authoredEventDiagram C (Bᵒᵖ ⥤ Type) program)
    (presheafEventInterpretationEquivalence C B program).functor).asEquivalence

/-- Any authored observed-interpretation map sends its source firing events
into the target's chosen reduction predicate. This uses the comma-category
endpoint square and the predicate-preservation factorization. -/
theorem authored_mapped_event_factors
    (C : Type) [SmallCategory C] [HasFiniteProducts C]
    (D : Type uD) [Category.{vD} D] [HasFiniteLimits D]
    (program : C)
    {X Y : AuthoredObservedInterpretations C D program} (f : X ⟶ Y) :
    Y.reduction.Factors
      (f.base.left ≫ Y.base.hom) := by
  exact mapped_event_factors (authoredEventDiagram C D program) f

end Mettapedia.OSLF.CartesianContextModels
