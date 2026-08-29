import Mettapedia.Languages.MeTTa.PureCheckingService
import Mettapedia.Languages.MeTTa.Pure.Intrinsic.AlgorithmicTyping

namespace Mettapedia.Languages.MeTTa.ElaboratedCore

open Mettapedia.Languages.MeTTa.Pure.Intrinsic
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Syntax
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Context
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Typing
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.PatternBridge

structure PureCheckSuccess where
  term : PureSyntaxTerm 0
  claimedType : PureTm 0
  typing : HasType .nil term.toPureTm claimedType

def PureCheckSuccess.certificate (result : PureCheckSuccess) : CheckedPureCertificate :=
  pureCheckingBoundary.checkSyntax result.term result.claimedType result.typing

theorem PureCheckSuccess.quoteAgreement (result : PureCheckSuccess) :
    result.certificate.artifact.pattern = quoteClosedTm result.certificate.term :=
  result.certificate.quoteAgreement

def inferPureSyntax (sourceTerm : PureSyntaxTerm 0) : Except String PureCheckSuccess := do
  let inferred <- inferClosedPureType sourceTerm.toPureTm
  pure
    { term := sourceTerm
      claimedType := inferred.type
      typing := inferred.typing }

def checkPureSyntax
    (sourceTerm : PureSyntaxTerm 0)
    (claimedType : PureSyntaxTerm 0) :
    Except String PureCheckSuccess := do
  let _ <- checkIsPureType .nil claimedType.toPureTm
  let typing <- checkClosedPureType sourceTerm.toPureTm claimedType.toPureTm
  pure
    { term := sourceTerm
      claimedType := claimedType.toPureTm
      typing := typing.typing }

def checkPureSyntaxWithOptionalType
    (sourceTerm : PureSyntaxTerm 0)
    (claimedType? : Option (PureSyntaxTerm 0)) :
    Except String PureCheckSuccess := do
  match claimedType? with
  | some claimedType => checkPureSyntax sourceTerm claimedType
  | none => inferPureSyntax sourceTerm

end Mettapedia.Languages.MeTTa.ElaboratedCore
