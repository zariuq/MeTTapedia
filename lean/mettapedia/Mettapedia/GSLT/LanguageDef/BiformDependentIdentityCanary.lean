import Mettapedia.GSLT.LanguageDef.BiformDependentContext
import Mettapedia.GSLT.LanguageDef.BiformTheoryCanary

/-!
# Dependent identity over proof-relevant biform histories

One extensional loop has two authored Boolean occurrences.  Its logical
theorem and endpoint relation do not distinguish them, but the representable
family of histories does: transport of the reflexive history along the two
occurrences yields different inhabitants.

This is a small vertical criterion for dependent typing.  A constant
observation descends to proposition-valued reachability; the authentic
history family provably does not.  Moreover, two biform routes with the same
logical translation induce different maps of dependent path contexts.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.BiformDependentIdentityCanary

open _root_.CategoryTheory
open scoped _root_.CategoryTheory
open Mettapedia.GSLT.ProofRelevant
open Mettapedia.GSLT.LanguageDef.BiformDependentContext
open Mettapedia.GSLT.LanguageDef.BiformTheoryCanary
open Mettapedia.TypeTheory.CategoryIndexedFamilyCwf
open Mettapedia.TypeTheory.ProofRelevantRouteFamilyBridge

/-- A retained occurrence path over the one-state Boolean evidence system. -/
abbrev OccurrencePath := EvidencePath Canary.boolSystem () ()

/-- Select the first authored occurrence. -/
def falsePath : OccurrencePath :=
  .cons false (.refl ())

/-- Select the second authored occurrence over the same extensional step. -/
def truePath : OccurrencePath :=
  .cons true (.refl ())

/-- Observe the first retained occurrence of a nonempty history. -/
def firstOccurrence : OccurrencePath → Option Bool
  | .refl _ => none
  | .cons evidence _ => some evidence

@[simp] theorem falsePath_firstOccurrence :
    firstOccurrence falsePath = some false :=
  rfl

@[simp] theorem truePath_firstOccurrence :
    firstOccurrence truePath = some true :=
  rfl

/-- The two proof-relevant paths share endpoints and extensional support but
retain distinct authored occurrences. -/
theorem falsePath_ne_truePath : falsePath ≠ truePath := by
  intro equality
  have observed := congrArg firstOccurrence equality
  simp at observed

/-- Histories from the unique state form the representable dependent family
used by the negative descent test. -/
def occurrenceHistoryFamily : IndexedFamily
    (Mettapedia.TypeTheory.ProofRelevantRouteFamilyBridge.evidenceContext
      Canary.boolSystem) :=
  evidencePathFamily Canary.boolSystem ()

/-- Transporting the reflexive history along parallel occurrences remembers
which occurrence was selected. -/
theorem occurrenceHistoryFamily_distinguishes_paths :
    occurrenceHistoryFamily.map falsePath (.refl ()) ≠
      occurrenceHistoryFamily.map truePath (.refl ()) := by
  change falsePath ≠ truePath
  exact falsePath_ne_truePath

/-- Negative control: an occurrence-sensitive dependent family cannot descend
to proposition-truncated reachability. -/
theorem occurrenceHistoryFamily_does_not_descend :
    ¬ Nonempty (ThinDescent occurrenceHistoryFamily) := by
  intro descended
  have invariant : ParallelInvariant occurrenceHistoryFamily :=
    (ThinDescent.nonempty_iff_parallelInvariant
      occurrenceHistoryFamily).1 descended
  exact occurrenceHistoryFamily_distinguishes_paths
    (invariant
      (source := ())
      (target := ())
      falsePath truePath (.refl ()))

/-- Positive control: a constant observation ignores occurrence identity and
therefore descends to proposition-truncated reachability. -/
theorem constantObservation_descends :
    Nonempty (ThinDescent
      (Mettapedia.TypeTheory.CategoryIndexedFamilyCwf.Canary.constantBoolFamily
        (Mettapedia.TypeTheory.ProofRelevantRouteFamilyBridge.evidenceContext
          Canary.boolSystem))) :=
  Mettapedia.TypeTheory.CategoryIndexedFamilyCwf.Canary.constantBool_descends _

/-- The identity biform route retains the false occurrence. -/
theorem retainedContext_maps_false :
    (evidenceContext.map retainRoute).toFunctor.map falsePath = falsePath :=
  rfl

/-- The alternative route flips the same occurrence to true. -/
theorem flippedContext_maps_false :
    (evidenceContext.map flipRoute).toFunctor.map falsePath = truePath :=
  rfl

/-- The induced dependent-context map retains a distinction already erased by
the logical projection. -/
theorem dependentContext_images_distinct :
    evidenceContext.map retainRoute ≠ evidenceContext.map flipRoute := by
  intro equality
  have retainedImage := retainedContext_maps_false
  rw [equality, flippedContext_maps_false] at retainedImage
  exact falsePath_ne_truePath retainedImage.symm

/-- The vertical seam in one statement: the theorem-level translation is the
same, while the dependent operational action is not. -/
theorem logical_same_dependentContext_different :
    BiformTheory.logicalProjection.map retainRoute =
        BiformTheory.logicalProjection.map flipRoute ∧
      evidenceContext.map retainRoute ≠ evidenceContext.map flipRoute :=
  ⟨logical_images_equal, dependentContext_images_distinct⟩

#print axioms falsePath_ne_truePath
#print axioms occurrenceHistoryFamily_does_not_descend
#print axioms constantObservation_descends
#print axioms dependentContext_images_distinct
#print axioms logical_same_dependentContext_different

end Mettapedia.GSLT.LanguageDef.BiformDependentIdentityCanary
