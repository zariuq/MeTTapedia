import Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionLaunch
import Mettapedia.Languages.ProcessCalculi.MORK.ComputableInputMonotonicity

/-!
# Matcher extension for decorated assertion source frames

Positive MM2 matching is preserved when source-derived passive rows extend
the canonical decorated assertion slice.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionMatchExtension

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionFrame
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionLaunch
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionMatch
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionSurface
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable

private theorem canonical_decorated_assertion_shell
    (context : DirectAssertionContext) :
    decoratedDirectAssertionDirective.atom ∈
      canonicalDecoratedDirectAssertionSpace context := by
  unfold canonicalDecoratedDirectAssertionSpace
  unfold decoratedDirectAssertionMatchSlice decoratedDirectAssertionDataSlice
  simp

theorem ExactDecoratedDirectAssertionLaunch.append
    (context : DirectAssertionContext) {space : List Atom}
    (launch : ExactDecoratedDirectAssertionLaunch context space)
    (shell : decoratedDirectAssertionDirective.atom ∈ space)
    (extra : List Atom) :
    ExactDecoratedDirectAssertionLaunch context (space ++ extra) := by
  rcases launch with ⟨substitution, rowMember, outputs⟩
  refine ⟨substitution, ?_, outputs⟩
  rw [decoratedDirectAssertionDirective_input_exact] at rowMember ⊢
  exact cmatchInputSpec_compat_append_after_erase []
    decoratedDirectAssertionDirective.atom space extra
    decoratedDirectAssertionPatterns shell rowMember

theorem canonical_exact_decorated_direct_assertion_launch_append
    (context : DirectAssertionContext) (extra : List Atom) :
    ExactDecoratedDirectAssertionLaunch context
      (canonicalDecoratedDirectAssertionSpace context ++ extra) :=
  ExactDecoratedDirectAssertionLaunch.append context
    (canonical_exact_decorated_direct_assertion_launch context)
    (canonical_decorated_assertion_shell context) extra

#print axioms canonical_exact_decorated_direct_assertion_launch_append

end Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionMatchExtension
