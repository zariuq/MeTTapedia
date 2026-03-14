import Mettapedia.Languages.MeTTa.PureCheckingService
import Mettapedia.Languages.MeTTa.PureKernel.DefEq
import Mettapedia.Languages.MeTTa.PureKernel.Parallel

/-!
# Pure Canonicalization Service

Canonical closed-term canonicalization and definitional equality service for the
current Pure semantic waist.

The authoritative object exposed here is the current Pure kernel's complete
development `cdev`. This is the canonical conversion anchor for the current
closed fragment. It is stronger and more central than the CLI-level executable
stepper, but it is not the same thing as a final executable normal form.
-/

namespace Mettapedia.Languages.MeTTa.ElaboratedCore

open Mettapedia.Languages.MeTTa.PureKernel
open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.Reduction
open Mettapedia.Languages.MeTTa.PureKernel.Confluence
open Mettapedia.Languages.MeTTa.PureKernel.Parallel
open Mettapedia.Languages.MeTTa.PureKernel.Typing
open Mettapedia.Languages.MeTTa.PureKernel.PatternBridge

structure CanonicalClosedPureTerm where
  input : PureTm 0
  canonicalDevelopment : PureTm 0
  reductionToCanonicalDevelopment : RedStar input canonicalDevelopment
  conversionToCanonicalDevelopment : Conv input canonicalDevelopment

namespace CanonicalClosedPureTerm

def reduction (result : CanonicalClosedPureTerm) :
    RedStar result.input result.canonicalDevelopment :=
  result.reductionToCanonicalDevelopment

def conversion (result : CanonicalClosedPureTerm) :
    Conv result.input result.canonicalDevelopment :=
  result.conversionToCanonicalDevelopment

@[simp] theorem reduction_eq_reductionToCanonicalDevelopment
    (result : CanonicalClosedPureTerm) :
    result.reduction = result.reductionToCanonicalDevelopment := rfl

@[simp] theorem conversion_eq_conversionToCanonicalDevelopment
    (result : CanonicalClosedPureTerm) :
    result.conversion = result.conversionToCanonicalDevelopment := rfl

def artifact (result : CanonicalClosedPureTerm) : SharedArtifact :=
  ⟨quoteClosedTm result.canonicalDevelopment⟩

theorem quoteAgreement (result : CanonicalClosedPureTerm) :
    result.artifact.pattern = quoteClosedTm result.canonicalDevelopment := rfl

end CanonicalClosedPureTerm

def canonicalizeClosedPureTerm (t : PureTm 0) : CanonicalClosedPureTerm :=
  { input := t
    canonicalDevelopment := cdev t
    reductionToCanonicalDevelopment := par_to_redStar (par_to_cdev_self t)
    conversionToCanonicalDevelopment := conv_to_cdev t }

structure ClosedDefEqWitness (A B : PureTm 0) where
  commonCanonicalDevelopment : PureTm 0
  leftReduction : RedStar A commonCanonicalDevelopment
  rightReduction : RedStar B commonCanonicalDevelopment
  conv : Conv A B

def defEqClosed? (A B : PureTm 0) : Option (ClosedDefEqWitness A B) :=
  let left := canonicalizeClosedPureTerm A
  let right := canonicalizeClosedPureTerm B
  if h : left.canonicalDevelopment = right.canonicalDevelopment then
    some
      { commonCanonicalDevelopment := left.canonicalDevelopment
        leftReduction := left.reductionToCanonicalDevelopment
        rightReduction := by simpa [h] using right.reductionToCanonicalDevelopment
        conv := conv_of_cdev_eq h }
  else
    none

structure ClosedPiView (t : PureTm 0) where
  canonical : CanonicalClosedPureTerm
  dom : PureTm 0
  cod : PureTm 1
  canonicalDevelopment_eq : canonical.canonicalDevelopment = .pi dom cod
  conv : Conv t (.pi dom cod)

def asPiClosed? (t : PureTm 0) : Option (ClosedPiView t) :=
  let canonical := canonicalizeClosedPureTerm t
  match hcanon : canonical.canonicalDevelopment with
  | .pi dom cod =>
      some
        { canonical := canonical
          dom := dom
          cod := cod
          canonicalDevelopment_eq := hcanon
          conv := by simpa [hcanon] using canonical.conversionToCanonicalDevelopment }
  | _ => none

structure ClosedSigmaView (t : PureTm 0) where
  canonical : CanonicalClosedPureTerm
  dom : PureTm 0
  cod : PureTm 1
  canonicalDevelopment_eq : canonical.canonicalDevelopment = .sigma dom cod
  conv : Conv t (.sigma dom cod)

def asSigmaClosed? (t : PureTm 0) : Option (ClosedSigmaView t) :=
  let canonical := canonicalizeClosedPureTerm t
  match hcanon : canonical.canonicalDevelopment with
  | .sigma dom cod =>
      some
        { canonical := canonical
          dom := dom
          cod := cod
          canonicalDevelopment_eq := hcanon
          conv := by simpa [hcanon] using canonical.conversionToCanonicalDevelopment }
  | _ => none

def PureCheckingBoundary.canonicalizeClosed
    (_svc : PureCheckingBoundary)
    (term : PureTm 0) :
    CanonicalClosedPureTerm :=
  canonicalizeClosedPureTerm term

def PureCheckingBoundary.canonicalizeClosedArtifact
    (svc : PureCheckingBoundary)
    (term : PureTm 0) :
    SharedArtifact :=
  (svc.canonicalizeClosed term).artifact

def PureCheckingBoundary.defEqClosed?
    (_svc : PureCheckingBoundary)
    (A B : PureTm 0) :
    Option (ClosedDefEqWitness A B) :=
  Mettapedia.Languages.MeTTa.ElaboratedCore.defEqClosed? A B

def PureCheckingBoundary.asCanonicalPiClosed?
    (_svc : PureCheckingBoundary)
    (t : PureTm 0) :
    Option (ClosedPiView t) :=
  asPiClosed? t

def PureCheckingBoundary.asCanonicalSigmaClosed?
    (_svc : PureCheckingBoundary)
    (t : PureTm 0) :
    Option (ClosedSigmaView t) :=
  asSigmaClosed? t

theorem PureCheckingBoundary.canonicalizeClosed_term
    (svc : PureCheckingBoundary)
    (term : PureTm 0) :
    (svc.canonicalizeClosed term).input = term := by
  simp [PureCheckingBoundary.canonicalizeClosed, canonicalizeClosedPureTerm]

theorem PureCheckingBoundary.canonicalizeClosed_cdev
    (svc : PureCheckingBoundary)
    (term : PureTm 0) :
    (svc.canonicalizeClosed term).canonicalDevelopment = cdev term := by
  rfl

end Mettapedia.Languages.MeTTa.ElaboratedCore
