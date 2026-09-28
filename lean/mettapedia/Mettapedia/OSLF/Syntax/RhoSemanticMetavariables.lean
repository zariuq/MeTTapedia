import Mettapedia.OSLF.Syntax.BindingEquationalModels
import Mettapedia.OSLF.Syntax.RhoCommunicationSchema

/-!
# A semantic continuation metavariable in the reflective presentation

The communication schema's continuation has the dependency context `[nm]`.
Its two authored instantiations, discard and unquote, therefore determine
distinct substitution-natural operations in the term binding clone. Applying
them to the quoted payload gives distinct processes. The comparison uses the
actual rho signature and authored continuation bodies.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoSemanticMetavariables

open Mettapedia.OSLF.Binding.RhoSchema
open Mettapedia.OSLF.Binding.FreeBindingTerms
open Mettapedia.OSLF.Binding.BindingEquationalModels

private def quotedPayload : Term sig G Srt.nm :=
  .op Op.quo (.cons (.var (.succ .zero)) .nil)

private def payloadArgs :
    FamilyArgs sig (Term sig) [([], Srt.nm)] G :=
  .cons quotedPayload .nil

/-- The continuation that discards its input remains null after semantic
metavariable application. -/
theorem discard_payload :
    applyMeta (Mettapedia.OSLF.Binding.BindingCloneAlgebra.terms sig)
      (contDiscard 0) payloadArgs =
        Term.op (S := sig) (Γ := G) Op.nil .nil := rfl

/-- The continuation that unquotes its input retains the emitted payload
under the authored drop constructor. -/
theorem unquote_payload :
    applyMeta (Mettapedia.OSLF.Binding.BindingCloneAlgebra.terms sig)
      (contUnquote 0) payloadArgs =
        Term.op (S := sig) (Γ := G) Op.drp
          (.cons quotedPayload .nil) := rfl

/-- The positive and negative continuation controls remain different after
passing through the semantic operation representation. -/
theorem discard_ne_unquote_at_payload :
    applyMeta (Mettapedia.OSLF.Binding.BindingCloneAlgebra.terms sig)
      (contDiscard 0) payloadArgs ≠
    applyMeta (Mettapedia.OSLF.Binding.BindingCloneAlgebra.terms sig)
      (contUnquote 0) payloadArgs := by
  rw [discard_payload, unquote_payload]
  intro h
  cases h

/-- Their natural semantic operations are different, not just their chosen
syntactic presentations. -/
theorem discard_operation_ne_unquote_operation :
    NaturalMetaOperation.ofBody
      (Mettapedia.OSLF.Binding.BindingCloneAlgebra.terms sig)
        (contDiscard 0) ≠
    NaturalMetaOperation.ofBody
      (Mettapedia.OSLF.Binding.BindingCloneAlgebra.terms sig)
        (contUnquote 0) := by
  intro h
  have hAt := congrArg (fun op : NaturalMetaOperation
      (Mettapedia.OSLF.Binding.BindingCloneAlgebra.terms sig)
      [Srt.nm] Srt.pr => op.apply payloadArgs) h
  exact discard_ne_unquote_at_payload hAt

end Mettapedia.OSLF.Binding.RhoSemanticMetavariables
