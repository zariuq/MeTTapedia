import Mettapedia.OSLF.Syntax.CartesianModelLexObservedInterpretations
import Mettapedia.OSLF.Syntax.RhoSourceLexEventInterpretations
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Images

/-!
# Observed source rho interpretation

The source rho model retains the actual COMM and Drop event presheaf over
raw substitution contexts. Its reduction predicate is the image of the
endpoint map. The relative finite-limit comparison transports the same
event object and chosen predicate back to authored contexts.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoSourceLexObservedInterpretations

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.OSLF.CartesianContextModels
open Mettapedia.OSLF.Binding.VaryingEventObservations
open Mettapedia.OSLF.Binding.RhoSourceLexEventInterpretations
open Mettapedia.OSLF.Binding.RhoSourceEquationLexClassification
open Mettapedia.OSLF.Binding.RhoSchema

private instance : HasFiniteProducts SourceContexts :=
  hasFiniteProducts_of_has_binary_and_terminal

/-- The actual source operational interpretation with its least endpoint
predicate, retaining all individual firing occurrences. -/
noncomputable def sourceObservedInterpretation :
    LeftExactObservedInterpretations SourceContexts RawPresheaves program :=
  imageObservation
    (leftExactEventDiagram SourceContexts RawPresheaves program)
    sourceOperationalInterpretation

/-- In the presheaf target, endpoint images are functorial and freely
equip every relative finite-limit event interpretation with its least
reduction predicate. -/
noncomputable def sourceObservedImageAdjunction :
    imageFunctor
      (leftExactEventDiagram SourceContexts RawPresheaves program) ⊣
    forget
      (leftExactEventDiagram SourceContexts RawPresheaves program) :=
  imageAdjunction _

/-- The chosen predicate is exactly the image of the actual endpoint map. -/
theorem sourceObserved_reduction_is_image :
    sourceObservedInterpretation.reduction =
      imageSubobject sourceOperationalInterpretation.hom := rfl

/-- Restrict the observed operational model to authored source contexts.
The comparison retains events as well as their reduction image. -/
noncomputable def authoredObservedInterpretation :
    AuthoredObservedInterpretations SourceContexts RawPresheaves program :=
  (presheafObservedInterpretationEquivalence
    SourceContexts RawCloneContexts program).functor.obj
      sourceObservedInterpretation

/-- The observed restriction still contains an actual source Drop firing. -/
theorem authoredObserved_has_drop_event :
    Nonempty (authoredObservedInterpretation.base.left.obj closedRawContext) := by
  have hbase : authoredObservedInterpretation.base =
      authoredSourceOperationalInterpretation := by
    rfl
  rw [hbase]
  exact authoredSource_has_drop_event

end Mettapedia.OSLF.Binding.RhoSourceLexObservedInterpretations
