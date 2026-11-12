import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypingStates
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.Preservation

/-!
# Typed transform states for the declaration-based certified program

The candidate's rule certificates instantiate the independent transform
state-typing theorem. The generic state and helper interfaces do not depend
on this candidate or on its concrete computation rules.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.TypingStates

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram

variable {O : Type} [DecidableEq O]

/-- Computation firings over the candidate's certified linearized rules
preserve the generic state-typing invariant. -/
theorem linear_compute_preserves {s : LState Confluence.linearRules O} (f : Compute s)
    (admitted : (computeStep (rules := Confluence.linearRules) (O := O)).Admits f)
    (typed : Typed s.frame s.present s.label) :
    Typed f.after.frame f.after.present f.after.label :=
  compute_preserves_of (fun judgment step => Preservation.step_preserves judgment step) f admitted typed

#print axioms linear_compute_preserves

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.TypingStates
