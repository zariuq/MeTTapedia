import Mettapedia.OSLF.Syntax.ContextualFamily

/-!
# Original binding terms inside an arbitrary contextual declaration family

The original signature's terms embed by retaining variables, operators and
their binding arities. Contextual assignment cannot change these rigid
terms. Object substitution and plugging commute with that inclusion.
No finiteness or supply of metavariable declarations is required.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ContextualFamily.Rigid

variable {S : Signature} {V W : Type} (declaration : V → MetaArity S)

mutual

def includeTerm : {Γ : Ctx S} → {sort : S.Srt} → Term S Γ sort →
    Term (signature S declaration) Γ sort
  | _, _, .var position => .var position
  | _, _, .op operator arguments => .op (.inl operator) (includeArgs arguments)

def includeArgs : {arities : List (List S.Srt × S.Srt)} → {Γ : Ctx S} → Args S arities Γ →
    Args (signature S declaration) arities Γ
  | _, _, .nil => .nil
  | _, _, .cons head tail => .cons (includeTerm head) (includeArgs tail)

end

mutual

theorem include_rename {Γ Δ : Ctx S} (rho : Ren S Γ Δ) :
    ∀ {sort : S.Srt} (term : Term S Γ sort),
    includeTerm declaration (rename rho term) = rename (S := signature S declaration) rho (includeTerm declaration term)
  | _, .var _ => rfl
  | _, .op operator arguments => congrArg (Term.op (S := signature S declaration) (Sum.inl operator)) (includeArgs_rename rho arguments)

theorem includeArgs_rename {Γ Δ : Ctx S} (rho : Ren S Γ Δ) :
    ∀ {arities : List (List S.Srt × S.Srt)} (arguments : Args S arities Γ),
    includeArgs declaration (renameArgs rho arguments) = renameArgs (S := signature S declaration) rho (includeArgs declaration arguments)
  | _, .nil => rfl
  | _, .cons (bs := binders) head tail =>
      congrArg₂ Args.cons (include_rename (liftRen rho binders) head)
        (includeArgs_rename rho tail)

end

theorem include_liftSub {Γ Δ : Ctx S} (environment : Sub S Γ Δ) :
    ∀ (binders : Ctx S) (sort : S.Srt) (position : Var (binders ++ Γ) sort),
      includeTerm declaration (liftSub environment binders sort position) =
        liftSub (fun sort position => includeTerm declaration (environment sort position)) binders sort position
  | [], _, _ => rfl
  | _ :: _, _, .zero => rfl
  | _ :: binders, sort, .succ position => by
      simp only [liftSub, weaken, include_rename, include_liftSub environment binders sort position]

mutual

theorem include_bind {Γ Δ : Ctx S} (environment : Sub S Γ Δ) :
    ∀ {sort : S.Srt} (term : Term S Γ sort),
      includeTerm declaration (bind environment term) =
        bind (fun sort position => includeTerm declaration (environment sort position)) (includeTerm declaration term)
  | _, .var _ => rfl
  | _, .op operator arguments => congrArg (Term.op (S := signature S declaration) (Sum.inl operator)) (includeArgs_bind environment arguments)

theorem includeArgs_bind {Γ Δ : Ctx S} (environment : Sub S Γ Δ) :
    ∀ {arities : List (List S.Srt × S.Srt)} (arguments : Args S arities Γ),
      includeArgs declaration (bindArgs environment arguments) =
        bindArgs (fun sort position => includeTerm declaration (environment sort position)) (includeArgs declaration arguments)
  | _, .nil => rfl
  | _, .cons (bs := binders) head tail => by
      have lifted : (fun sort position => includeTerm declaration (liftSub environment binders sort position)) =
          liftSub (fun sort position => includeTerm declaration (environment sort position)) binders := by
        funext sort position
        exact include_liftSub declaration environment binders sort position
      simp only [bindArgs, includeArgs, include_bind, includeArgs_bind, lifted]

end

theorem include_inst {Γ : Ctx S} {name sort : S.Srt} (body : Term S (name :: Γ) sort)
    (argument : Term S Γ name) :
    includeTerm declaration (inst body argument) =
      inst (includeTerm declaration body) (includeTerm declaration argument) := by
  unfold inst
  rw [include_bind]
  congr 1
  funext result position
  cases position <;> rfl

variable {source : V → MetaArity S} {target : W → MetaArity S}

mutual

theorem instantiate_include (assignment : Assignment source target) :
    ∀ {Γ : Ctx S} {sort : S.Srt} (term : Term S Γ sort),
      instantiate assignment (includeTerm source term) = includeTerm target term
  | _, _, .var _ => rfl
  | _, _, .op operator arguments =>
      congrArg (Term.op (S := signature S target) (Sum.inl operator)) (instantiateArgs_include assignment arguments)

theorem instantiateArgs_include (assignment : Assignment source target) :
    ∀ {arities : List (List S.Srt × S.Srt)} {Γ : Ctx S} (arguments : Args S arities Γ),
      instantiateArgs assignment (includeArgs source arguments) = includeArgs target arguments
  | _, _, .nil => rfl
  | _, _, .cons head tail => congrArg₂ Args.cons (instantiate_include assignment head)
      (instantiateArgs_include assignment tail)

end

end Mettapedia.OSLF.Binding.ContextualFamily.Rigid
