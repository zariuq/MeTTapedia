import Mettapedia.TypeTheory.DisplayedPresheafClassifierCoherence
import Mettapedia.TypeTheory.DependentProductRestrictionControls

/-!
# A strict truth-comparison inclusion

The two constant theory functors select different actual worlds. Their
transformation follows a genuine noninvertible arrow. A proper future
sieve gives bottom through one truth comparison and top through the other
path of the displayed comparison square. Thus the general inclusion law
cannot be replaced by equality.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedPresheafClassifierCoherenceControls

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafSliceSubstitution DisplayedPresheafClassifier
open DisplayedPresheafTheoryTransformation DisplayedPresheafClassifierCoherence
open DependentProductRestrictionControls

def earlier : Small ⥤ Large := initialWorld
def later : Small ⥤ Large := terminalWorld
def advance : earlier ⟶ later := (Functor.const Small).map WalkingParallelPairHom.left
def base : Largeᵒᵖ ⥤ Type := (Functor.const _).obj PUnit

def point : (later.op ⋙ base).Elements :=
  ⟨Opposite.op (Discrete.mk ()), PUnit.unit⟩

def direct : Sieve (Discrete.mk ()) := (comparison later base).app point properFuture

def throughChange : Sieve (Discrete.mk ()) :=
  ((reindexFunctor (baseMap advance base)).map (comparison earlier base)).app point
    ((familyMap advance base (propositions base)).app point properFuture)

theorem direct_bottom : direct = ⊥ := classifier_loses_future

theorem throughChange_top : throughChange = ⊤ := by
  apply Sieve.ext
  intro future arrow
  change WalkingParallelPair.zero = WalkingParallelPair.zero ↔ True
  simp only [eq_self]

/-- The qualified general theorem holds for this concrete transformation. -/
theorem actual_inclusion : direct ≤ throughChange :=
  transformation_le advance base point properFuture

/-- The supplied noninvertible transformation does not give an equality
of native truth comparisons, even though their base carriers coincide. -/
theorem comparison_square_not_equal : direct ≠ throughChange := by
  rw [direct_bottom, throughChange_top]
  intro same
  have member : (⊤ : Sieve (Discrete.mk ())).arrows (𝟙 (Discrete.mk ())) := trivial
  rw [← same] at member
  exact member

theorem transformation_not_invertible : ¬ IsIso advance := by
  intro invertible
  have square := transformation_iso (asIso advance) base
  have atPoint := congrArg (fun map => map.app point properFuture) square
  exact comparison_square_not_equal atPoint.symm

/-- Every actual invertible theory change gives the stronger square;
the result covers arbitrary program and sieve families. -/
theorem invertible_positive {C D : Type} [Category C] [Category D]
    {F G : C ⥤ D} (change : F ≅ G) (P : Dᵒᵖ ⥤ Type) :
    familyMap change.hom P (propositions P) ≫
      (reindexFunctor (baseMap change.hom P)).map (comparison F P) = comparison G P :=
  transformation_iso change P

end Mettapedia.TypeTheory.DisplayedPresheafClassifierCoherenceControls
