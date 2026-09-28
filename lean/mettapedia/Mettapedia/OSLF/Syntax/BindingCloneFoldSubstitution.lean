import Mettapedia.OSLF.Syntax.BindingCloneAlgebra

/-!
# The free binding fold respects semantic substitution

The unique constructor fold into a binding-clone algebra is natural under
renaming and simultaneous substitution. The proof first handles renaming,
then identifies the semantic lift of a folded environment with the fold of
the syntactic lift beneath every authored binder list. The substitution law
follows by mutual induction over terms and argument vectors.

No equation satisfaction or quotient universal property is assumed here.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.BindingCloneFoldSubstitution

open Mettapedia.OSLF.Binding.BindingCloneAlgebra
open Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra
open Mettapedia.OSLF.Binding.FreeBindingTerms

universe u

variable {S : Signature}

/-- Interpret a raw scoped term in a substitution-compatible binding model. -/
def interpret (A : BindingCloneAlgebra.Algebra.{u} S)
    {Γ : Ctx S} {sort : S.Srt} (term : Term S Γ sort) :
    A.substitution.Carrier Γ sort :=
  FreeBindingTerms.fold A.toRaw term

/-- Interpret its complete binder-indexed argument vector. -/
def interpretArgs (A : BindingCloneAlgebra.Algebra.{u} S)
    {Γ : Ctx S} {arity : List (List S.Srt × S.Srt)}
    (args : Args S arity Γ) :
    FamilyArgs S A.substitution.Carrier arity Γ :=
  FreeBindingTerms.foldArgs A.toRaw args

/-- Lifting a semantic environment of projections agrees pointwise with
lifting its variable renaming beneath any binder list. -/
theorem liftProjection_apply (A : BindingCloneAlgebra.Algebra.{u} S)
    {Γ Δ : Ctx S} (rho : Ren S Γ Δ) :
    ∀ (binders : List S.Srt) (sort : S.Srt)
      (x : Var (binders ++ Γ) sort),
      A.substitution.liftEnvironment
        (fun s v => A.substitution.injectVar (rho s v)) binders sort x =
      A.substitution.injectVar (liftRen rho binders sort x)
  | [], _, _ => rfl
  | _ :: binders, _, .zero => rfl
  | _ :: binders, sort, .succ old => by
      change A.substitution.weaken
        (A.substitution.liftEnvironment
          (fun s v => A.substitution.injectVar (rho s v)) binders sort old) =
        A.substitution.injectVar
          (.succ (liftRen rho binders sort old))
      rw [liftProjection_apply A rho binders sort old]
      unfold BindingSubstitutionAlgebra.Algebra.weaken
      exact A.substitution.substitute_var
        (fun _ v => A.substitution.injectVar (.succ v)) _

mutual

/-- Every binding-clone interpretation commutes with variable renaming. -/
theorem interpret_rename (A : BindingCloneAlgebra.Algebra.{u} S) :
    ∀ {Γ Δ : Ctx S} {sort : S.Srt}
      (rho : Ren S Γ Δ) (term : Term S Γ sort),
      interpret A (rename rho term) =
        A.substitution.substitute
          (fun s v => A.substitution.injectVar (rho s v))
          (interpret A term)
  | _, _, _, rho, .var x => by
      change A.substitution.injectVar (rho _ x) =
        A.substitution.substitute
          (fun s v => A.substitution.injectVar (rho s v))
          (A.substitution.injectVar x)
      exact (A.substitution.substitute_var
        (fun s v => A.substitution.injectVar (rho s v)) x).symm
  | _, _, _, rho, .op o args => by
      change A.operation o (interpretArgs A (renameArgs rho args)) =
        A.substitution.substitute
          (fun s v => A.substitution.injectVar (rho s v))
          (A.operation o (interpretArgs A args))
      rw [A.operation_substitute]
      exact congrArg (A.operation o) (interpretArgs_rename A rho args)

theorem interpretArgs_rename (A : BindingCloneAlgebra.Algebra.{u} S) :
    ∀ {Γ Δ : Ctx S} {arity : List (List S.Srt × S.Srt)}
      (rho : Ren S Γ Δ) (args : Args S arity Γ),
      interpretArgs A (renameArgs rho args) =
        A.substitution.substituteArgs
          (fun s v => A.substitution.injectVar (rho s v))
          (interpretArgs A args)
  | _, _, _, _, .nil => rfl
  | _, _, _, rho, .cons (bs := binders) head tail => by
      change FamilyArgs.cons (interpret A (rename (liftRen rho binders) head))
          (interpretArgs A (renameArgs rho tail)) =
        FamilyArgs.cons
          (A.substitution.substitute
            (A.substitution.liftEnvironment
              (fun s v => A.substitution.injectVar (rho s v)) binders)
            (interpret A head))
          (A.substitution.substituteArgs
            (fun s v => A.substitution.injectVar (rho s v))
            (interpretArgs A tail))
      have lifted :
          A.substitution.liftEnvironment
            (fun s v => A.substitution.injectVar (rho s v)) binders =
          (fun s v => A.substitution.injectVar
            (liftRen rho binders s v) :
              Environment S A.substitution.Carrier
                (binders ++ _) (binders ++ _)) := by
        funext sort x
        exact liftProjection_apply A rho binders sort x
      rw [lifted]
      exact congrArg₂ FamilyArgs.cons
        (interpret_rename A (liftRen rho binders) head)
        (interpretArgs_rename A rho tail)

end

/-- Weakening the source term and weakening its semantic interpretation
agree. This is the ingredient needed for substituted values under binders. -/
theorem interpret_weaken (A : BindingCloneAlgebra.Algebra.{u} S)
    {Γ : Ctx S} {sort fresh : S.Srt} (term : Term S Γ sort) :
    interpret A (weaken (t := fresh) term) =
      A.substitution.weaken (interpret A term) := by
  exact interpret_rename A (fun _ v => Var.succ v) term

/-- Folding a syntactic environment and then lifting it beneath binders is
the same as folding the syntactically lifted environment. -/
theorem liftedInterpretation_apply (A : BindingCloneAlgebra.Algebra.{u} S)
    {Γ Δ : Ctx S} (sigma : Sub S Γ Δ) :
    ∀ (binders : List S.Srt) (sort : S.Srt)
      (x : Var (binders ++ Γ) sort),
      A.substitution.liftEnvironment
        (fun s v => interpret A (sigma s v)) binders sort x =
      interpret A (liftSub sigma binders sort x)
  | [], _, _ => rfl
  | _ :: binders, _, .zero => rfl
  | _ :: binders, sort, .succ old => by
      change A.substitution.weaken
        (A.substitution.liftEnvironment
          (fun s v => interpret A (sigma s v)) binders sort old) =
        interpret A (weaken (liftSub sigma binders sort old))
      rw [liftedInterpretation_apply A sigma binders sort old]
      exact (interpret_weaken A (liftSub sigma binders sort old)).symm

mutual

/-- The raw initial fold is a homomorphism for simultaneous semantic
substitution, including substitution beneath every authored binder list. -/
theorem interpret_bind (A : BindingCloneAlgebra.Algebra.{u} S) :
    ∀ {Γ Δ : Ctx S} {sort : S.Srt}
      (sigma : Sub S Γ Δ) (term : Term S Γ sort),
      interpret A (bind sigma term) =
        A.substitution.substitute
          (fun s v => interpret A (sigma s v)) (interpret A term)
  | _, _, _, sigma, .var x => by
      change interpret A (sigma _ x) =
        A.substitution.substitute
          (fun s v => interpret A (sigma s v))
          (A.substitution.injectVar x)
      exact (A.substitution.substitute_var
        (fun s v => interpret A (sigma s v)) x).symm
  | _, _, _, sigma, .op o args => by
      change A.operation o (interpretArgs A (bindArgs sigma args)) =
        A.substitution.substitute
          (fun s v => interpret A (sigma s v))
          (A.operation o (interpretArgs A args))
      rw [A.operation_substitute]
      exact congrArg (A.operation o) (interpretArgs_bind A sigma args)

theorem interpretArgs_bind (A : BindingCloneAlgebra.Algebra.{u} S) :
    ∀ {Γ Δ : Ctx S} {arity : List (List S.Srt × S.Srt)}
      (sigma : Sub S Γ Δ) (args : Args S arity Γ),
      interpretArgs A (bindArgs sigma args) =
        A.substitution.substituteArgs
          (fun s v => interpret A (sigma s v))
          (interpretArgs A args)
  | _, _, _, _, .nil => rfl
  | _, _, _, sigma, .cons (bs := binders) head tail => by
      change FamilyArgs.cons (interpret A (bind (liftSub sigma binders) head))
          (interpretArgs A (bindArgs sigma tail)) =
        FamilyArgs.cons
          (A.substitution.substitute
            (A.substitution.liftEnvironment
              (fun s v => interpret A (sigma s v)) binders)
            (interpret A head))
          (A.substitution.substituteArgs
            (fun s v => interpret A (sigma s v))
            (interpretArgs A tail))
      have lifted :
          A.substitution.liftEnvironment
            (fun s v => interpret A (sigma s v)) binders =
          (fun s v => interpret A (liftSub sigma binders s v) :
            Environment S A.substitution.Carrier
              (binders ++ _) (binders ++ _)) := by
        funext sort x
        exact liftedInterpretation_apply A sigma binders sort x
      rw [lifted]
      exact congrArg₂ FamilyArgs.cons
        (interpret_bind A (liftSub sigma binders) head)
        (interpretArgs_bind A sigma tail)

end

end Mettapedia.OSLF.Binding.BindingCloneFoldSubstitution
