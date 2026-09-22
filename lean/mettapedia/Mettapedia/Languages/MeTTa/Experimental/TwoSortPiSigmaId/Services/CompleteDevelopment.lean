import Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Services.CheckingService
import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DefEq
import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Parallel

/-!
# One-pass complete development for the two-sort experiment

This service exposes the complete development `cdev` and certificates that
the result is reachable and convertible to the input. One complete
development can leave redexes: neither normalization nor a complete
conversion decision follows from this service. The exact normalizer for
formed declaration-free terms is the separate mathematical module
`TypeTheory/Calculi/TwoSortPiSigmaId/Regular/Normalization.lean`.
-/

namespace Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Services

open Mettapedia.Languages.MeTTa.ElaboratedCore

open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Syntax
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Reduction
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Confluence
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Parallel
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing
open Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Adapters.PatternBridge

structure CanonicalClosedTwoSortTerm where
  input : ScopedTerm 0
  canonicalDevelopment : ScopedTerm 0
  reductionToCanonicalDevelopment : RedStar input canonicalDevelopment
  conversionToCanonicalDevelopment : Conv input canonicalDevelopment

namespace CanonicalClosedTwoSortTerm

def reduction (result : CanonicalClosedTwoSortTerm) :
    RedStar result.input result.canonicalDevelopment :=
  result.reductionToCanonicalDevelopment

def conversion (result : CanonicalClosedTwoSortTerm) :
    Conv result.input result.canonicalDevelopment :=
  result.conversionToCanonicalDevelopment

@[simp] theorem reduction_eq_reductionToCanonicalDevelopment
    (result : CanonicalClosedTwoSortTerm) :
    result.reduction = result.reductionToCanonicalDevelopment := rfl

@[simp] theorem conversion_eq_conversionToCanonicalDevelopment
    (result : CanonicalClosedTwoSortTerm) :
    result.conversion = result.conversionToCanonicalDevelopment := rfl

def artifact (result : CanonicalClosedTwoSortTerm) : SharedArtifact :=
  ⟨quoteClosedTm result.canonicalDevelopment⟩

theorem quoteAgreement (result : CanonicalClosedTwoSortTerm) :
    result.artifact.pattern = quoteClosedTm result.canonicalDevelopment := rfl

end CanonicalClosedTwoSortTerm

def canonicalizeClosedTwoSortTerm (t : ScopedTerm 0) : CanonicalClosedTwoSortTerm :=
  { input := t
    canonicalDevelopment := cdev t
    reductionToCanonicalDevelopment := par_to_redStar (par_to_cdev_self t)
    conversionToCanonicalDevelopment := conv_to_cdev t }

structure ClosedDefEqWitness (A B : ScopedTerm 0) where
  commonCanonicalDevelopment : ScopedTerm 0
  leftReduction : RedStar A commonCanonicalDevelopment
  rightReduction : RedStar B commonCanonicalDevelopment
  conv : Conv A B

def defEqClosed? (A B : ScopedTerm 0) : Option (ClosedDefEqWitness A B) :=
  let left := canonicalizeClosedTwoSortTerm A
  let right := canonicalizeClosedTwoSortTerm B
  if h : left.canonicalDevelopment = right.canonicalDevelopment then
    some
      { commonCanonicalDevelopment := left.canonicalDevelopment
        leftReduction := left.reductionToCanonicalDevelopment
        rightReduction := by
          rw [show left.canonicalDevelopment = right.canonicalDevelopment from h]
          exact right.reductionToCanonicalDevelopment
        conv := conv_of_cdev_eq h }
  else
    none

structure ClosedPiView (t : ScopedTerm 0) where
  canonical : CanonicalClosedTwoSortTerm
  dom : ScopedTerm 0
  cod : ScopedTerm 1
  canonicalDevelopment_eq : canonical.canonicalDevelopment = .pi dom cod
  conv : Conv t (.pi dom cod)

def asPiClosed? (t : ScopedTerm 0) : Option (ClosedPiView t) :=
  let canonical := canonicalizeClosedTwoSortTerm t
  match hcanon : canonical.canonicalDevelopment with
  | .pi dom cod =>
      some
        { canonical := canonical
          dom := dom
          cod := cod
          canonicalDevelopment_eq := hcanon
          conv := by
            rw [show (dom.pi cod) = canonical.canonicalDevelopment from hcanon.symm]
            exact canonical.conversionToCanonicalDevelopment }
  | _ => none

structure ClosedSigmaView (t : ScopedTerm 0) where
  canonical : CanonicalClosedTwoSortTerm
  dom : ScopedTerm 0
  cod : ScopedTerm 1
  canonicalDevelopment_eq : canonical.canonicalDevelopment = .sigma dom cod
  conv : Conv t (.sigma dom cod)

def asSigmaClosed? (t : ScopedTerm 0) : Option (ClosedSigmaView t) :=
  let canonical := canonicalizeClosedTwoSortTerm t
  match hcanon : canonical.canonicalDevelopment with
  | .sigma dom cod =>
      some
        { canonical := canonical
          dom := dom
          cod := cod
          canonicalDevelopment_eq := hcanon
          conv := by
            rw [show (dom.sigma cod) = canonical.canonicalDevelopment from hcanon.symm]
            exact canonical.conversionToCanonicalDevelopment }
  | _ => none

def TwoSortCheckingBoundary.canonicalizeClosed
    (_svc : TwoSortCheckingBoundary)
    (term : ScopedTerm 0) :
    CanonicalClosedTwoSortTerm :=
  canonicalizeClosedTwoSortTerm term

def TwoSortCheckingBoundary.canonicalizeClosedArtifact
    (svc : TwoSortCheckingBoundary)
    (term : ScopedTerm 0) :
    SharedArtifact :=
  (svc.canonicalizeClosed term).artifact

def TwoSortCheckingBoundary.defEqClosed?
    (_svc : TwoSortCheckingBoundary)
    (A B : ScopedTerm 0) :
    Option (ClosedDefEqWitness A B) :=
  Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Services.defEqClosed? A B

def TwoSortCheckingBoundary.asCanonicalPiClosed?
    (_svc : TwoSortCheckingBoundary)
    (t : ScopedTerm 0) :
    Option (ClosedPiView t) :=
  asPiClosed? t

def TwoSortCheckingBoundary.asCanonicalSigmaClosed?
    (_svc : TwoSortCheckingBoundary)
    (t : ScopedTerm 0) :
    Option (ClosedSigmaView t) :=
  asSigmaClosed? t

theorem TwoSortCheckingBoundary.canonicalizeClosed_term
    (svc : TwoSortCheckingBoundary)
    (term : ScopedTerm 0) :
    (svc.canonicalizeClosed term).input = term := by
  simp [TwoSortCheckingBoundary.canonicalizeClosed, canonicalizeClosedTwoSortTerm]

theorem TwoSortCheckingBoundary.canonicalizeClosed_cdev
    (svc : TwoSortCheckingBoundary)
    (term : ScopedTerm 0) :
    (svc.canonicalizeClosed term).canonicalDevelopment = cdev term := by
  rfl

end Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Services
