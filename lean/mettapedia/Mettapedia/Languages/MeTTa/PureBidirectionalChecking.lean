import Mettapedia.Languages.MeTTa.PureCheckingService
import Mettapedia.Languages.MeTTa.PureKernel.AlgorithmicTyping

namespace Mettapedia.Languages.MeTTa.ElaboratedCore

open Mettapedia.Languages.MeTTa.PureKernel
open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.Context
open Mettapedia.Languages.MeTTa.PureKernel.Typing
open Mettapedia.Languages.MeTTa.PureKernel.PatternBridge

structure PureCheckSuccess where
  term : SurfacePureTm 0
  claimedType : PureTm 0
  typing : HasType .nil term.toPureTm claimedType

def PureCheckSuccess.certificate (result : PureCheckSuccess) : CheckedPureCertificate :=
  pureCheckingBoundary.checkSurface result.term result.claimedType result.typing

theorem PureCheckSuccess.quoteAgreement (result : PureCheckSuccess) :
    result.certificate.artifact.pattern = quoteClosedTm result.certificate.term :=
  result.certificate.quoteAgreement

def inferSurfacePure (surface : SurfacePureTm 0) : Except String PureCheckSuccess := do
  let inferred <- inferClosedPureType surface.toPureTm
  pure
    { term := surface
      claimedType := inferred.type
      typing := inferred.typing }

def checkSurfacePure
    (surface : SurfacePureTm 0)
    (claimedType : SurfacePureTm 0) :
    Except String PureCheckSuccess := do
  let _ <- checkIsPureType .nil claimedType.toPureTm
  let typing <- checkClosedPureType surface.toPureTm claimedType.toPureTm
  pure
    { term := surface
      claimedType := claimedType.toPureTm
      typing := typing.typing }

def checkSurfacePureWithOptionalType
    (surface : SurfacePureTm 0)
    (claimedType? : Option (SurfacePureTm 0)) :
    Except String PureCheckSuccess := do
  match claimedType? with
  | some claimedType => checkSurfacePure surface claimedType
  | none => inferSurfacePure surface

end Mettapedia.Languages.MeTTa.ElaboratedCore
