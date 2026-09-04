import Mathlib.CategoryTheory.Discrete.Basic
import Mettapedia.Computability.FragmentwiseComputationalTrinityExactness
import Mettapedia.TypeTheory.ExtensionalReadout

/-!
# Computational-trinity comparisons induced by split readouts

A split extensional readout always gives a commuting comparison from a richer
source carrier to an extensional target and then to the same target as an
observation space.  Global exactness is available exactly when the readout is
faithful.  Without faithfulness, the comparison is nevertheless exact on the
canonical representatives selected by the split.

This is the categorical boundary needed for an extensional companion:
surjectivity gives visible completeness, while faithfulness remains a separate
obligation.  Route, occurrence, evidence, provenance, and cost distinctions
may therefore remain outside the exact fragment unless their observations are
proved invariant on readout fibres.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.SplitReadoutComparison

open CategoryTheory
open Mettapedia.Computability.ComputationalTrinity
open Mettapedia.Computability.FragmentwiseComputationalTrinity
open Mettapedia.Computability.FragmentwiseComputationalTrinityExactness
open Mettapedia.TypeTheory.ExtensionalReadout

universe u

abbrev Context := Discrete PUnit

private def here : Contextᵒᵖ :=
  Opposite.op (Discrete.mk PUnit.unit)

def sourceFace (Source : Type u) : Face.{0, 0, u} Context :=
  (Functor.const Contextᵒᵖ).obj Source

def targetFace (Target : Type u) : Face.{0, 0, u} Context :=
  (Functor.const Contextᵒᵖ).obj Target

def readoutMap {Source Target : Type u}
    (readout : SplitReadout Source Target) :
    sourceFace Source ⟶ targetFace Target :=
  (Functor.const Contextᵒᵖ).map (↾readout.observe)

/-- The source, extensional target, and extensional observation space form a
commuting comparison for every split readout. -/
def comparison {Source Target : Type u}
    (readout : SplitReadout Source Target) : Comparison.{0, 0, u} Context where
  program := sourceFace Source
  logic := targetFace Target
  space := targetFace Target
  programToLogic := readoutMap readout
  logicToSpace := 𝟙 _
  programToSpace := readoutMap readout
  coherence := by
    ext context source
    rfl

/-- A faithful readout loses no source distinction in the induced
computational-trinity comparison. -/
theorem not_loses_of_faithful {Source Target : Type u}
    (readout : SplitReadout Source Target) (faithful : readout.Faithful) :
    ¬ (comparison readout).LosesProgramInformation := by
  rintro ⟨context, left, right, different, sameObservation⟩
  exact different (faithful sameObservation)

/-- Conversely, if the induced comparison loses no source distinction, then
the readout is faithful. -/
theorem faithful_of_not_loses {Source Target : Type u}
    (readout : SplitReadout Source Target)
    (noLoss : ¬ (comparison readout).LosesProgramInformation) :
    readout.Faithful := by
  intro left right sameObservation
  apply Classical.byContradiction
  intro different
  exact noLoss ⟨here, left, right, different, sameObservation⟩

/-- Information preservation of the induced trinity is exactly faithfulness
of the extensional readout. -/
theorem not_loses_iff_faithful {Source Target : Type u}
    (readout : SplitReadout Source Target) :
    (¬ (comparison readout).LosesProgramInformation) ↔ readout.Faithful :=
  ⟨faithful_of_not_loses readout, not_loses_of_faithful readout⟩

/-! ## The canonical exact fragment -/

/-- Source elements already equal to their selected canonical representative
form a substitution-stable fragment of the constant source face. -/
def canonicalConstraint {Source Target : Type u}
    (readout : SplitReadout Source Target) :
    Constraint (sourceFace Source) where
  holds _ source := readout.canonicalize source = source
  map_closed := by
    intro first second substitution source canonical
    exact canonical

/-- The canonical representatives are exactly related to the complete target
by the readout. -/
def canonicalBridge {Source Target : Type u}
    (readout : SplitReadout Source Target) :
    ExactBridge (readoutMap readout) (canonicalConstraint readout)
      (Constraint.total (targetFace Target)) where
  sound := by
    intro context target represented
    trivial
  complete := by
    intro context target admitted
    refine ⟨readout.representative target, ?_, ?_⟩
    · change readout.canonicalize (readout.representative target) =
        readout.representative target
      unfold SplitReadout.canonicalize
      rw [readout.observe_representative]
    · exact readout.observe_representative target
  faithful := by
    intro context left right leftCanonical rightCanonical sameObservation
    change Source at left right
    change readout.canonicalize left = left at leftCanonical
    change readout.canonicalize right = right at rightCanonical
    change readout.observe left = readout.observe right at sameObservation
    calc
      left = readout.canonicalize left := leftCanonical.symm
      _ = readout.canonicalize right := by
        unfold SplitReadout.canonicalize
        rw [sameObservation]
      _ = right := rightCanonical

/-- Identity is exact on the complete extensional target face. -/
def targetIdentityBridge {Target : Type u} :
    ExactBridge (𝟙 (targetFace Target))
      (Constraint.total (targetFace Target))
      (Constraint.total (targetFace Target)) :=
  ExactBridge.identity _

/-- Every split readout induces an exact computational trinity on its
canonical source representatives, even when the ambient readout is lossy. -/
def canonicalExactComparison {Source Target : Type u}
    (readout : SplitReadout Source Target) :
    ExactFragmentwiseComparison (comparison readout) where
  programFragment := canonicalConstraint readout
  logicFragment := Constraint.total (targetFace Target)
  spaceFragment := Constraint.total (targetFace Target)
  programLogic := canonicalBridge readout
  logicSpace := targetIdentityBridge

/-! ## Global exactness -/

/-- Faithfulness upgrades the complete source fragment to an exact bridge. -/
def totalBridgeOfFaithful {Source Target : Type u}
    (readout : SplitReadout Source Target) (faithful : readout.Faithful) :
    ExactBridge (readoutMap readout)
      (Constraint.total (sourceFace Source))
      (Constraint.total (targetFace Target)) where
  sound := by
    intro context target represented
    trivial
  complete := by
    intro context target admitted
    obtain ⟨source, represents⟩ := readout.surjective target
    exact ⟨source, trivial, represents⟩
  faithful := by
    intro context left right leftAdmitted rightAdmitted sameObservation
    exact faithful sameObservation

/-- A total exact bridge forces the readout to be faithful. -/
theorem faithful_of_totalBridge {Source Target : Type u}
    (readout : SplitReadout Source Target)
    (bridge : ExactBridge (readoutMap readout)
      (Constraint.total (sourceFace Source))
      (Constraint.total (targetFace Target))) :
    readout.Faithful := by
  intro left right sameObservation
  exact bridge.faithful here trivial trivial sameObservation

/-- Global exactness of the extensional interface exists exactly when the
readout is faithful. -/
theorem totalBridge_nonempty_iff_faithful {Source Target : Type u}
    (readout : SplitReadout Source Target) :
    Nonempty
      (ExactBridge (readoutMap readout)
        (Constraint.total (sourceFace Source))
        (Constraint.total (targetFace Target))) ↔
      readout.Faithful := by
  constructor
  · rintro ⟨bridge⟩
    exact faithful_of_totalBridge readout bridge
  · intro faithful
    exact ⟨totalBridgeOfFaithful readout faithful⟩

/-! ## Route-sensitive negative and fragmentwise positive controls -/

namespace Canary

open Mettapedia.TypeTheory.ExtensionalReadout.Canary
open Mettapedia.TypeTheory.DependencyExtensionalityOrthogonality

/-- The route-sensitive carrier has no globally exact extensional bridge. -/
theorem routeReadout_has_no_total_exact_bridge :
    ¬ Nonempty
      (ExactBridge (readoutMap routeReadout)
        (Constraint.total (sourceFace simpleRouteSensitive.Function))
        (Constraint.total (targetFace Bool))) := by
  rw [totalBridge_nonempty_iff_faithful]
  exact routeReadout_not_faithful

/-- Nevertheless its canonical route-free representatives form an exact
fragmentwise computational trinity. -/
def routeReadout_canonical_exact :
    ExactFragmentwiseComparison (comparison routeReadout) :=
  canonicalExactComparison routeReadout

/-- The ambient comparison genuinely loses the retained route tag. -/
theorem routeReadout_comparison_loses :
    (comparison routeReadout).LosesProgramInformation := by
  exact ⟨here, (false, false), (false, true), by
    intro equality
    exact Bool.false_ne_true (congrArg Prod.snd equality), rfl⟩

end Canary

#print axioms not_loses_iff_faithful
#print axioms canonicalBridge
#print axioms canonicalExactComparison
#print axioms totalBridge_nonempty_iff_faithful
#print axioms Canary.routeReadout_has_no_total_exact_bridge
#print axioms Canary.routeReadout_canonical_exact
#print axioms Canary.routeReadout_comparison_loses

end Mettapedia.Computability.SplitReadoutComparison
