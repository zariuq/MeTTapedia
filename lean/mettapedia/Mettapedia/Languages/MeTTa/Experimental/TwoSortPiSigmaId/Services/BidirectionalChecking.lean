import Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Services.CheckingService
import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.AlgorithmicTyping

namespace Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Services

open Mettapedia.Languages.MeTTa.ElaboratedCore

open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Syntax
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Context
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing
open Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Adapters.PatternBridge

structure TwoSortCheckSuccess where
  term : TwoSortSyntaxTerm 0
  claimedType : ScopedTerm 0
  typing : HasType .nil term.toScopedTerm claimedType

def TwoSortCheckSuccess.certificate (result : TwoSortCheckSuccess) : CheckedTwoSortCertificate :=
  twoSortCheckingBoundary.checkSyntax result.term result.claimedType result.typing

theorem TwoSortCheckSuccess.quoteAgreement (result : TwoSortCheckSuccess) :
    result.certificate.artifact.pattern = quoteClosedTm result.certificate.term :=
  result.certificate.quoteAgreement

def inferTwoSortSyntax (sourceTerm : TwoSortSyntaxTerm 0) : Except String TwoSortCheckSuccess := do
  let inferred <- inferClosedTwoSortType sourceTerm.toScopedTerm
  pure
    { term := sourceTerm
      claimedType := inferred.type
      typing := inferred.typing }

def checkTwoSortSyntax
    (sourceTerm : TwoSortSyntaxTerm 0)
    (claimedType : TwoSortSyntaxTerm 0) :
    Except String TwoSortCheckSuccess := do
  let _ <- checkIsTwoSortType .nil claimedType.toScopedTerm
  let typing <- checkClosedTwoSortType sourceTerm.toScopedTerm claimedType.toScopedTerm
  pure
    { term := sourceTerm
      claimedType := claimedType.toScopedTerm
      typing := typing.typing }

def checkTwoSortSyntaxWithOptionalType
    (sourceTerm : TwoSortSyntaxTerm 0)
    (claimedType? : Option (TwoSortSyntaxTerm 0)) :
    Except String TwoSortCheckSuccess := do
  match claimedType? with
  | some claimedType => checkTwoSortSyntax sourceTerm claimedType
  | none => inferTwoSortSyntax sourceTerm

end Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Services
