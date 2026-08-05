/-
# The current one-root conversion boundary

This module records the conversion boundary encountered while routing the
immutable DTTBench traces from the syntactic Pure checker to indexed LF.  The
generic proof-calculus vocabulary now contains both binder-eliminating
substitution and unused-binder elimination.  This module establishes two
executable facts:

* the two generic side conditions have distinct depth contracts;
* the diagnostic eta normalizer is intentionally untyped and erases the lambda
  domain, so a typing client must independently check the well-formedness of
  both endpoints selected by a rooted structural eta certificate.

The profiled `Eq_symm` trace is the motivating runtime witness: syntactic Pure
rejects it at the first beta-equivalent delivery, while beta-only diagnostic
replay accepts it.  That recorded computation is intentionally not rebranded as
an LF theorem here.

The rooted `ConversionDecl` remains the only conversion entry point.  The
unused-binder side condition closes the structural freshness seam.  It supports
a raw rooted reduction rule, while profile typing remains a separate checked
obligation rather than a hidden Boolean side condition.
-/

import Mettapedia.GSLT.LanguageDef.ConversionCertificate
import Mettapedia.GSLT.LanguageDef.DependentTypingCanary
import Mettapedia.GSLT.LanguageDef.LF.ProfileChecker
import Mettapedia.GSLT.LanguageDef.Pure.BetaEtaConversion

namespace Mettapedia.GSLT.LanguageDef.LFConversionInterfaceBoundary

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.Pure

/-- Exhaustive account of the generic side-condition vocabulary.  Typing
premises remain ordinary rooted judgments rather than hidden Boolean cases. -/
theorem sideCondition_cases (condition : RuleSideCondition) :
    (∃ ambientDepth bodyArgument replacementArgument resultArgument,
      condition = .explicitSubstitution ambientDepth bodyArgument
        replacementArgument resultArgument) ∨
    (∃ ambientDepth bodyArgument resultArgument,
      condition = .unusedBinderElimination ambientDepth bodyArgument
        resultArgument) := by
  cases condition with
  | explicitSubstitution ambientDepth bodyArgument replacementArgument
      resultArgument =>
      exact .inl
        ⟨ambientDepth, bodyArgument, replacementArgument, resultArgument, rfl⟩
  | unusedBinderElimination ambientDepth bodyArgument resultArgument =>
      exact .inr ⟨ambientDepth, bodyArgument, resultArgument, rfl⟩

private def etaBody : Expr := .app (.bvar 1) (.bvar 0)

private def etaSource (domain : Expr) : Expr := .lam domain etaBody

private def etaTarget : Expr := .bvar 0

/-- The existing executable eta diagnostic contracts the same body regardless
of its lambda domain.  Both displayed domains are closed and syntactically
different.  A typing client must therefore validate both endpoints with its
profile checker rather than reuse this Boolean as typing evidence. -/
theorem betaEtaDiagnostic_is_domain_blind :
    Mettapedia.GSLT.LanguageDef.PureBetaEta.convBool
        (etaSource .sort) etaTarget = true ∧
      Mettapedia.GSLT.LanguageDef.PureBetaEta.convBool
        (etaSource (.pi .sort .sort)) etaTarget = true := by
  decide

private def capturedEtaSource : Expr :=
  .lam .sort (.app (.bvar 0) (.bvar 0))

/-- Positive guard on the diagnostic itself: a genuinely captured binder is
not eta-contracted.  This does not repair domain blindness; both obligations
remain required when a structural certificate is consumed by a typing
client. -/
theorem betaEtaDiagnostic_rejects_captured_binder :
    Mettapedia.GSLT.LanguageDef.PureBetaEta.convBool
      capturedEtaSource etaTarget = false := by
  decide

#print axioms sideCondition_cases
#print axioms betaEtaDiagnostic_is_domain_blind
#print axioms betaEtaDiagnostic_rejects_captured_binder

end Mettapedia.GSLT.LanguageDef.LFConversionInterfaceBoundary
