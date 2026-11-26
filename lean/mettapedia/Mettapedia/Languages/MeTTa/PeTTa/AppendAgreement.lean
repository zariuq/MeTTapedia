import Mettapedia.Languages.MeTTa.PeTTa.Eval

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Eval

open SpaceSemantics (Program)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-- An extension can use any declaration check that agrees on arrow declarations. -/
theorem appended_program_agreement_of_checks (allowed : String → Bool) (first extension : Program)
    (equations : extension.equations.all (fun equation => !allowed equation.head) = true)
    {fresh : Atom → Bool} (declarations : extension.declarations.all fresh = true)
    (calls : ∀ head types,
      fresh (.expression [.symbol ":", .symbol head, .expression (.symbol "->" :: types)]) =
        !allowed head) :
    ProgramAgreementOn allowed first (first.append extension) := by
  apply appended_program_agreement
  · intro equation member
    have row := List.all_eq_true.mp equations equation member
    simpa only [Bool.not_eq_true'] using row
  · intro head types member
    have row := List.all_eq_true.mp declarations _ member
    simpa only [calls head types, Bool.not_eq_true'] using row

/-- Fresh equation rows and call declarations preserve the old calls, including
their order and multiplicity. -/
theorem appended_program_agreement_of_all (allowed : String → Bool) (first extension : Program)
    (equations : extension.equations.all (fun equation => !allowed equation.head) = true)
    (declarations : extension.declarations.all (fun declaration =>
      !retainedCallDeclaration allowed declaration) = true) :
    ProgramAgreementOn allowed first (first.append extension) :=
  appended_program_agreement_of_checks allowed first extension equations declarations (fun _ _ => rfl)

end Mettapedia.Languages.MeTTa.PeTTa.Eval
