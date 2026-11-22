import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualResidual
import Mettapedia.OSLF.Syntax.BindingArgumentSlots
import Mettapedia.OSLF.Syntax.ContextualFamilyDeclarations

/-!
# Rigid imitation with fresh contextual fields

For a hole applied to object variables and equated to a rigid constructor,
replace its image by that constructor with one fresh hole per field. Each
helper declares the original parameters plus that field's bound variables.
All original equations are instantiated and retained for subsequent solving.

The construction preserves every solution, including assignments into later
declaration families. Variable spines may repeat or reorder parameters. No
claim of uniquely recovering a repeated spine, or of deciding every residual,
is needed. A compound occurrence argument is outside this imitation case.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualImitation

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual

variable {S : Signature} {Other : Type}

abbrev sourceDeclarations (parameters : Ctx S) (result : S.Srt) (others : Other → MetaArity S) :
    Unit ⊕ Other → MetaArity S := sumDeclarations (fun _ => (parameters, result)) others

abbrev targetDeclarations (parameters : Ctx S) {result : S.Srt} (operator : S.Op result)
    (others : Other → MetaArity S) : ArgumentSlots.Slot (S.arity operator) ⊕ Other → MetaArity S :=
  sumDeclarations (fun slot => (slot.1.1 ++ parameters, slot.1.2)) others

def freshFields (parameters : Ctx S) {result : S.Srt} (operator : S.Op result)
    (others : Other → MetaArity S) :
    Args (signature S (targetDeclarations parameters operator others)) (S.arity operator) parameters :=
  ArgumentSlots.tabulate (S := signature S (targetDeclarations parameters operator others))
    (Γ := parameters) (S.arity operator)
    (fun field position => generator (targetDeclarations parameters operator others) (.inl ⟨field, position⟩))

def answer (parameters : Ctx S) {result : S.Srt} (operator : S.Op result)
    (others : Other → MetaArity S) :
    Assignment (sourceDeclarations parameters result others) (targetDeclarations parameters operator others)
  | .inl () => .op (.inl operator) (freshFields parameters operator others)
  | .inr identity => generator (targetDeclarations parameters operator others) (.inr identity)

def residual {Variables : Type} {next : Variables → MetaArity S}
    (parameters : Ctx S) {result : S.Srt} (operator : S.Op result) (others : Other → MetaArity S)
    (candidate : Assignment (sourceDeclarations parameters result others) next)
    (fields : Args (signature S next) (S.arity operator) parameters) :
    Assignment (targetDeclarations parameters operator others) next
  | .inl ⟨field, position⟩ => ArgumentSlots.get fields field position
  | .inr identity => candidate (.inr identity)

theorem instantiate_freshFields {Variables : Type} {next : Variables → MetaArity S}
    (parameters : Ctx S) {result : S.Srt} (operator : S.Op result) (others : Other → MetaArity S)
    (candidate : Assignment (sourceDeclarations parameters result others) next)
    (fields : Args (signature S next) (S.arity operator) parameters) :
    instantiateArgs (residual parameters operator others candidate fields) (freshFields parameters operator others) = fields := by
  apply ArgumentSlots.ext
  intro field position
  rw [ArgumentSlots.get_instantiate, freshFields, ArgumentSlots.get_tabulate, instantiate_generator]
  rfl

theorem factors_of_head {Variables : Type} {next : Variables → MetaArity S}
    (parameters : Ctx S) {result : S.Srt} (operator : S.Op result) (others : Other → MetaArity S)
    (candidate : Assignment (sourceDeclarations parameters result others) next)
    (fields : Args (signature S next) (S.arity operator) parameters)
    (head : candidate (.inl ()) = Term.op (S := signature S next) (.inl operator) fields) :
    ∀ identity, candidate identity =
      instantiate (residual parameters operator others candidate fields) (answer parameters operator others identity)
  | .inl () => by
      simp only [answer, instantiate, instantiate_freshFields]
      exact head
  | .inr identity => by rw [answer, instantiate_generator]; rfl

/-- The selected equation establishes the constructor shape; all other
equations remain in the residual queue, including constraints absent from
the selected equation's vocabulary. -/
theorem reduction (parameters : Ctx S) {result : S.Srt}
    (operator : S.Op result) (others : Other → MetaArity S) {Γ : Ctx S}
    (rho : Ren S parameters Γ)
    (right : Args (signature S (sourceDeclarations parameters result others)) (S.arity operator) Γ)
    (problem : Problem (sourceDeclarations parameters result others))
    (selected :
      (observe (rename (S := signature S (sourceDeclarations parameters result others)) rho
        (generator (sourceDeclarations parameters result others) (.inl ()))),
       observe (Term.op (.inl operator) right)) ∈ problem) :
    Reduction problem (answer parameters operator others)
      (mapProblem (answer parameters operator others) problem) := by
  constructor
  · intro Next declaration candidate solved
    exact (models_mapProblem _ _ _).mp solved
  · intro Next declaration candidate solved
    have same := observe_injective (solved _ selected)
    rw [ContextualFamily.instantiate_rename, instantiate_generator] at same
    change rename (S := signature S declaration) rho (candidate (.inl ())) =
      Term.op (S := signature S declaration) (.inl operator) (instantiateArgs candidate right) at same
    obtain ⟨fields, head, _⟩ := ArgumentSlots.rename_eq_operator (S := signature S declaration) rho (candidate (.inl ()))
      (.inl operator) (instantiateArgs candidate right) same
    let rest := residual parameters operator others candidate fields
    have factors := factors_of_head parameters operator others candidate fields head
    exact ⟨rest, (models_of_components candidate (answer parameters operator others) rest factors problem).mp solved, factors⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualImitation
