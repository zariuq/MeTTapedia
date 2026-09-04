import Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionSurface
import Mettapedia.Languages.ProcessCalculi.MORK.RuleScopedMatchFactorOrigin

/-!
# Pending-factor origin for the decorated assertion matcher

The decorated assertion input contains one pending-request factor.  Any
successful compatible match replays that factor from a concrete row in the
matcher read space.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionPendingOrigin

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionSurface
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable

theorem directAssertionPendingTemplate_mem_decoratedPatterns :
    directAssertionPendingTemplate ∈ decoratedDirectAssertionPatterns := by
  simp [decoratedDirectAssertionPatterns, directAssertionPatterns]

/-- Any ordinary decorated-assertion matcher row replays the pending factor
from one concrete carrier in its read space. -/
theorem decoratedAssertionMatcher_pending_replay_origin
    (read : List Atom) {substitution : Subst}
    (member : substitution ∈
      (cmatchInputSpec [] read
        decoratedDirectAssertionDirective.rule.input).map Prod.fst) :
    ∃ carrier ∈ read,
      applySubst substitution directAssertionPendingTemplate = carrier := by
  rw [decoratedDirectAssertionDirective_input_exact] at member
  exact cmatchInputSpec_compat_factor_replay_origin read
    (mkPattern decoratedDirectAssertionPatterns)
    directAssertionPendingTemplate
    directAssertionPendingTemplate_mem_decoratedPatterns
    member

/-- The compact-key matcher has the same factor-origin property because its
compatible branch is the canonical complete pattern matcher. -/
theorem decoratedAssertionMorkMatcher_pending_replay_origin
    (read : List Atom) {substitution : Subst} {witnesses : List Atom}
    (member : (substitution, witnesses) ∈
      cMatchInputSpecMork [] read
        decoratedDirectAssertionDirective.rule.input) :
    ∃ carrier ∈ read,
      applySubst substitution directAssertionPendingTemplate = carrier := by
  exact cMatchInputSpecMork_compat_factor_replay_origin read
    decoratedDirectAssertionDirective.rule.input
    (mkPattern decoratedDirectAssertionPatterns)
    directAssertionPendingTemplate
    decoratedDirectAssertionDirective_input_exact
    directAssertionPendingTemplate_mem_decoratedPatterns member

#print axioms decoratedAssertionMatcher_pending_replay_origin
#print axioms decoratedAssertionMorkMatcher_pending_replay_origin

end Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionPendingOrigin
