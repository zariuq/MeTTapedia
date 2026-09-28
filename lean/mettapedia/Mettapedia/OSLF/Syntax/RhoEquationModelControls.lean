import Mettapedia.OSLF.Syntax.BindingEquationInterpretation
import Mettapedia.OSLF.Syntax.RhoCommunicationSchema

/-!
# Equation-model controls for the reflective presentation

The raw rho term algebra does not satisfy the authored commutativity equation:
its two process variables remain distinct constructor arguments. The existing
equational quotient identifies every commutativity instance. These controls
mark the difference between free binding terms and the equation rung.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoEquationModelControls

open Mettapedia.OSLF.Binding.RhoSchema
open Mettapedia.OSLF.Binding.BindingEquationInterpretation

/-- The unquotiented term binding clone is not a model of the actual rho
equations. A claimed equation-model interface cannot silently use raw terms. -/
theorem raw_terms_do_not_satisfy_rho_equations :
    ¬ Satisfies (Mettapedia.OSLF.Binding.BindingCloneAlgebra.terms sig) rhoE := by
  intro h
  have comm := h 0
    (fun k => contDiscard k)
    (Γ := [Srt.pr, Srt.pr])
    (fun _ v => Term.var v)
  have comm' :
      (Term.op (S := sig) (Γ := [Srt.pr, Srt.pr]) Op.par
        (.cons (.var .zero) (.cons (.var (.succ .zero)) .nil))) =
      Term.op (S := sig) Op.par
        (.cons (.var (.succ .zero)) (.cons (.var .zero) .nil)) := by
    simpa [rhoE, commPar, interpretSchema, interpretSchemaArgs,
      Mettapedia.OSLF.Binding.BindingCloneAlgebra.terms,
      Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra.terms,
      Mettapedia.OSLF.Binding.FreeBindingTerms.terms,
      Mettapedia.OSLF.Binding.FreeBindingTerms.terms.familyToSyntax,
      bind, bindArgs, liftSub] using comm
  cases comm'

/-- Every pair of processes gives an actual commutativity class equality in
the equation quotient, with arbitrary ambient free variables retained. -/
theorem parallel_commutes_in_quotient
    {Γ : Ctx sig} (left right : Term sig Γ Srt.pr) :
    (Quotient.mk _
      (Term.op (S := sig) Op.par (.cons left (.cons right .nil))) :
      TermQ rhoE Γ Srt.pr) =
    Quotient.mk _
      (Term.op (S := sig) Op.par (.cons right (.cons left .nil))) := by
  let close : Sub sig [Srt.pr, Srt.pr] Γ :=
    fun _ v =>
      match v with
      | .zero => left
      | .succ .zero => right
  have h := EqClosure.ax (E := rhoE) (i := 0) contDiscard close
  exact Quotient.sound h

end Mettapedia.OSLF.Binding.RhoEquationModelControls
