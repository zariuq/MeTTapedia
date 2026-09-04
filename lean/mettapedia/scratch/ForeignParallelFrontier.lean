import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryStaticPairApex

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open RhoCommonRestorationApex

private def baseDeclaration : ReflectivePresentationDecl :=
  costStaticReflectivePresentationDecl rhoCIGSLT .base
    rhoReflectivePresentation.toReflectivePresentationDecl

private def wrappedDeclaration : ReflectivePresentationDecl :=
  costStaticReflectivePresentationDecl rhoCIGSLT .wrapped
    rhoReflectivePresentation.toReflectivePresentationDecl

private def baseUnit : Pattern :=
  .apply baseDeclaration.parallelUnitConstructor []

private def wrappedUnit : Pattern :=
  .apply wrappedDeclaration.parallelUnitConstructor []

private def mixedParallel : Pattern :=
  .collection rhoReflectivePresentation.parallelCollection
    [.bvar 0, baseUnit,
      .collection rhoReflectivePresentation.parallelCollection
        [baseUnit, .fvar "a"] none]
    none

example : parallelLeaves baseDeclaration baseUnit = [] := by
  decide

example : parallelLeaves wrappedDeclaration baseUnit = [baseUnit] := by
  decide

example :
    parallelLeaves baseDeclaration mixedParallel =
      (parallelLeaves wrappedDeclaration mixedParallel).filter
        (· ≠ baseUnit) := by
  decide

example : parallelLeaves wrappedDeclaration wrappedUnit = [] := by
  decide

example : parallelLeaves baseDeclaration wrappedUnit = [wrappedUnit] := by
  decide

example :
    parallelLeaves baseDeclaration wrappedUnit ≠
      (parallelLeaves wrappedDeclaration wrappedUnit).filter
        (· ≠ baseUnit) := by
  decide

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
