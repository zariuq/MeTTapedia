import Mettapedia.OSLF.Syntax.BindingVariableSpines

/-!
# Recognized spines are the common renamed generator applications

The executable recognizer reads the existing typed arguments. Its recovered
map describes exactly the application's syntax, including permutations and
repeated variables; injectivity is a separate condition on that map.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.VariableSpines

open ContextualFamily

variable {S : Signature} {V : Type} {declaration : V → MetaArity S}

theorem arguments_eq_rename_selfArgs (parameters : Ctx S) {Γ : Ctx S}
    (arguments : Args S (parameters.map fun sort => ([], sort)) Γ)
    (rho : Ren S parameters Γ)
    (spine : ∀ sort index, argsToSub arguments sort index = .var (rho sort index)) :
    arguments = renameArgs rho (selfArgs parameters) := by
  calc
    arguments = bindArgs (argsToSub arguments) (selfArgs parameters) :=
      (bindArgs_selfArgs parameters arguments).symm
    _ = bindArgs (fun sort index => .var (rho sort index)) (selfArgs parameters) := by
      rw [funext fun sort => funext fun index => spine sort index]
    _ = renameArgs rho (selfArgs parameters) := bindArgs_var_eq_renameArgs rho _

theorem application_eq_rename_generator (identity : V) {Γ : Ctx S}
    (arguments : Args (signature S declaration) ((declaration identity).1.map fun sort => ([], sort)) Γ)
    (rho : Ren S (declaration identity).1 Γ)
    (spine : ∀ sort index, argsToSub arguments sort index = .var (rho sort index)) :
    Term.op (S := signature S declaration) (.inr (.mk identity)) arguments =
      rename (S := signature S declaration) rho (generator declaration identity) := by
  rw [generator, rename]
  exact congrArg (Term.op (S := signature S declaration) (.inr (.mk identity)))
    (arguments_eq_rename_selfArgs (S := signature S declaration) _ arguments rho spine)

end Mettapedia.OSLF.Binding.VariableSpines
