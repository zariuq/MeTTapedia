import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryVariableLeafRoutes

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryLeafDichotomyProbe

namespace ForeignPairOpacityCanary

private def emptyParallel : Pattern :=
  .collection rhoReflectivePresentation.parallelCollection [] none

private def nestedEmptyParallel : Pattern :=
  .collection rhoReflectivePresentation.parallelCollection
    [emptyParallel] none

/-- A small exact collision representative.  Either generated declaration
canonicalizes an empty parallel and a singleton parallel containing that
empty parallel to the same result. -/
theorem empty_nested_collision (color : CostStaticColor) :
    let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
      rhoReflectivePresentation.toReflectivePresentationDecl
    canonicalize declaration emptyParallel =
      canonicalize declaration nestedEmptyParallel := by
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation.toReflectivePresentationDecl
  have parallel : declaration.parallelCollection =
      rhoReflectivePresentation.parallelCollection :=
    rhoDecl_parallelCollection color
  change canonicalize declaration emptyParallel =
    canonicalize declaration nestedEmptyParallel
  unfold nestedEmptyParallel
  rw [← parallel]
  exact (canonicalize_parallel_singleton declaration emptyParallel).symm

/-- The collision transfers to the other declaration as a pair even though
pointwise absorption of one declaration through the other is too strong. -/
theorem empty_nested_pair_transfer (viewColor : CostStaticColor) :
    let own := costStaticReflectivePresentationDecl rhoCIGSLT viewColor
      rhoReflectivePresentation.toReflectivePresentationDecl
    let foreign := costStaticReflectivePresentationDecl rhoCIGSLT viewColor.flip
      rhoReflectivePresentation.toReflectivePresentationDecl
    canonicalize foreign emptyParallel =
        canonicalize foreign nestedEmptyParallel ∧
      canonicalize own emptyParallel =
        canonicalize own nestedEmptyParallel := by
  exact ⟨empty_nested_collision viewColor.flip,
    empty_nested_collision viewColor⟩

/-- Negative control: the foreign empty-parallel unit remains a foreign rigid
constructor under the own declaration, whereas direct own canonicalization
inserts the own unit. -/
theorem not_pointwise_absorption_empty (viewColor : CostStaticColor) :
    let own := costStaticReflectivePresentationDecl rhoCIGSLT viewColor
      rhoReflectivePresentation.toReflectivePresentationDecl
    let foreign := costStaticReflectivePresentationDecl rhoCIGSLT viewColor.flip
      rhoReflectivePresentation.toReflectivePresentationDecl
    canonicalize own (canonicalize foreign emptyParallel) ≠
      canonicalize own emptyParallel := by
  dsimp only
  let own := costStaticReflectivePresentationDecl rhoCIGSLT viewColor
    rhoReflectivePresentation.toReflectivePresentationDecl
  let foreign := costStaticReflectivePresentationDecl rhoCIGSLT viewColor.flip
    rhoReflectivePresentation.toReflectivePresentationDecl
  have foreignEmpty : canonicalize foreign emptyParallel =
      .apply foreign.parallelUnitConstructor [] := by
    calc
      canonicalize foreign emptyParallel =
          canonicalize foreign (.apply foreign.parallelUnitConstructor []) := by
        exact canonicalize_emptyParallel_eq_canonicalize_unit foreign
          (rhoDecl_parallelCollection viewColor.flip)
          (rhoDecl_unit_ne_quote viewColor.flip)
      _ = .apply foreign.parallelUnitConstructor [] := by
        rw [canonicalize_apply_of_ne_quote foreign
          (rhoDecl_unit_ne_quote viewColor.flip)]
        rfl
  have ownEmpty : canonicalize own emptyParallel =
      .apply own.parallelUnitConstructor [] := by
    calc
      canonicalize own emptyParallel =
          canonicalize own (.apply own.parallelUnitConstructor []) := by
        exact canonicalize_emptyParallel_eq_canonicalize_unit own
          (rhoDecl_parallelCollection viewColor)
          (rhoDecl_unit_ne_quote viewColor)
      _ = .apply own.parallelUnitConstructor [] := by
        rw [canonicalize_apply_of_ne_quote own
          (rhoDecl_unit_ne_quote viewColor)]
        rfl
  have foreignUnitNeOwnQuote : foreign.parallelUnitConstructor ≠
      own.quoteConstructor := by
    cases viewColor <;> decide
  have unitsDistinct : foreign.parallelUnitConstructor ≠
      own.parallelUnitConstructor := by
    cases viewColor <;> decide
  change canonicalize own (canonicalize foreign emptyParallel) ≠
    canonicalize own emptyParallel
  rw [foreignEmpty,
    canonicalize_apply_of_ne_quote own foreignUnitNeOwnQuote, ownEmpty]
  simpa using unitsDistinct

end ForeignPairOpacityCanary

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
