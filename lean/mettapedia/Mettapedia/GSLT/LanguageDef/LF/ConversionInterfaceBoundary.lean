/-
# The current one-root conversion boundary

This module records the exact boundary encountered while routing the immutable
DTTBench traces from the syntactic Pure checker to indexed LF.  It does not add
a conversion rule.  Instead it establishes two executable facts:

* the sole generic rule-side-condition constructor currently certifies explicit
  binder substitution;
* that diagnostic eta normalizer is intentionally untyped and erases the lambda
  domain, so it cannot be promoted to the rooted LF authority without a typed
  eta/freshness extension and its negative cases.

The profiled `Eq_symm` trace is the motivating runtime witness: syntactic Pure
rejects it at the first beta-equivalent delivery, while beta-only diagnostic
replay accepts it.  That recorded computation is intentionally not rebranded as
an LF theorem here.

The rooted `ConversionDecl` remains the only conversion entry point.  Until its
ordinary rules can carry the missing typed eta evidence, conversion-inclusive
LF authentication must stop here rather than treating the diagnostic replay as
an authority.
-/

import Mettapedia.GSLT.LanguageDef.ConversionCertificate
import Mettapedia.GSLT.LanguageDef.DependentTypingCanary
import Mettapedia.GSLT.LanguageDef.LF.ProfileChecker
import Mettapedia.GSLT.LanguageDef.Pure.BetaEtaConversion

namespace Mettapedia.GSLT.LanguageDef.LFConversionInterfaceBoundary

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.Pure

/-- Exhaustive account of the current generic side-condition vocabulary.  In
particular, there is no direct typed-eta or freshness constructor hidden in the
checker. -/
theorem sideCondition_is_explicitSubstitution
    (condition : RuleSideCondition) :
    ∃ ambientDepth bodyArgument replacementArgument resultArgument,
      condition = .explicitSubstitution ambientDepth bodyArgument
        replacementArgument resultArgument := by
  cases condition with
  | explicitSubstitution ambientDepth bodyArgument replacementArgument
      resultArgument =>
      exact ⟨ambientDepth, bodyArgument, replacementArgument, resultArgument,
        rfl⟩

private def etaBody : Expr := .app (.bvar 1) (.bvar 0)

private def etaSource (domain : Expr) : Expr := .lam domain etaBody

private def etaTarget : Expr := .bvar 0

/-- The existing executable eta diagnostic contracts the same body regardless
of its lambda domain.  Both displayed domains are closed and syntactically
different.  A typed LF conversion rule must therefore validate the domain from
typing evidence rather than reuse this Boolean as a root side condition. -/
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
are required by a future typed eta rule. -/
theorem betaEtaDiagnostic_rejects_captured_binder :
    Mettapedia.GSLT.LanguageDef.PureBetaEta.convBool
      capturedEtaSource etaTarget = false := by
  decide

#print axioms sideCondition_is_explicitSubstitution
#print axioms betaEtaDiagnostic_is_domain_blind
#print axioms betaEtaDiagnostic_rejects_captured_binder

end Mettapedia.GSLT.LanguageDef.LFConversionInterfaceBoundary
