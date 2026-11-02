import Mettapedia.OSLF.Syntax.ContextualFamily

/-!
# Finite metavariable support in contextual binding terms

Terms over an arbitrary declaration family still have finite support.
The executable membership check characterizes support inclusion. Instantiation
depends only on assignment components in that support, including metavariables
used inside argument spines and beneath object binders.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {V W : Type}
  {source : V → MetaArity S} {target : W → MetaArity S}

mutual

def support : {Γ : Ctx S} → {sort : S.Srt} → Term (signature S source) Γ sort → List V
  | _, _, .var _ => []
  | _, _, .op (.inl _) arguments => supportArgs arguments
  | _, _, .op (.inr (.mk identity)) arguments => identity :: supportArgs arguments

def supportArgs : {arities : List (List S.Srt × S.Srt)} → {Γ : Ctx S} →
    Args (signature S source) arities Γ → List V
  | _, _, .nil => []
  | _, _, .cons head tail => support head ++ supportArgs tail

end

def checkSupport [DecidableEq V] (allowed : List V) {Γ : Ctx S} {sort : S.Srt}
    (term : Term (signature S source) Γ sort) : Bool :=
  (support term).all fun identity => decide (identity ∈ allowed)

theorem checkSupport_iff [DecidableEq V] (allowed : List V) {Γ : Ctx S} {sort : S.Srt}
    (term : Term (signature S source) Γ sort) :
    checkSupport allowed term = true ↔ ∀ identity ∈ support term, identity ∈ allowed := by
  simp [checkSupport, List.all_eq_true]

mutual

/-- Equality on the actual support suffices, even for images containing
unresolved metavariables and compound or repeated application arguments. -/
theorem instantiate_congr (first second : Assignment source target) :
    ∀ {Γ : Ctx S} {sort : S.Srt} (term : Term (signature S source) Γ sort),
      (∀ identity ∈ support term, first identity = second identity) →
      instantiate first term = instantiate second term
  | _, _, .var _, _ => rfl
  | _, _, .op (.inl original) arguments, agree => by
      exact congrArg (Term.op (S := signature S target) (.inl original))
        (instantiateArgs_congr first second arguments agree)
  | _, _, .op (.inr (.mk identity)) arguments, agree => by
      have sameImage := agree identity (by simp [support])
      have sameArguments := instantiateArgs_congr first second arguments
        (fun name member => agree name (by simp [support, member]))
      simp only [instantiate, sameImage, sameArguments]

theorem instantiateArgs_congr (first second : Assignment source target) :
    ∀ {arities : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (arguments : Args (signature S source) arities Γ),
      (∀ identity ∈ supportArgs arguments, first identity = second identity) →
      instantiateArgs first arguments = instantiateArgs second arguments
  | _, _, .nil, _ => rfl
  | _, _, .cons head tail, agree => by
      exact congrArg₂ Args.cons
        (instantiate_congr first second head
          (fun name member => agree name (List.mem_append_left _ member)))
        (instantiateArgs_congr first second tail
          (fun name member => agree name (List.mem_append_right _ member)))

end

mutual

theorem support_rename :
    ∀ {Γ Δ : Ctx S} {sort : S.Srt} (rho : Ren S Γ Δ)
      (term : Term (signature S source) Γ sort),
      support (rename (S := signature S source) rho term) = support term
  | _, _, _, _, .var _ => rfl
  | _, _, _, rho, .op (.inl _) arguments => supportArgs_renameArgs rho arguments
  | _, _, _, rho, .op (.inr (.mk identity)) arguments =>
      congrArg (List.cons identity) (supportArgs_renameArgs rho arguments)

theorem supportArgs_renameArgs :
    ∀ {arities : List (List S.Srt × S.Srt)} {Γ Δ : Ctx S} (rho : Ren S Γ Δ)
      (arguments : Args (signature S source) arities Γ),
      supportArgs (renameArgs (S := signature S source) rho arguments) = supportArgs arguments
  | _, _, _, _, .nil => rfl
  | _, _, _, rho, .cons (bs := binders) head tail =>
      congrArg₂ List.append (support_rename (liftRen rho binders) head)
        (supportArgs_renameArgs rho tail)

end

theorem supportArgs_selfArgs : ∀ (parameters : Ctx S),
    supportArgs (selfArgs (T := signature S source) parameters) = []
  | [] => rfl
  | _ :: rest => by
      simp only [selfArgs, supportArgs, support, List.nil_append,
        supportArgs_renameArgs, supportArgs_selfArgs rest]

theorem support_generator (identity : V) : support (generator source identity) = [identity] := by
  simp only [generator, support, supportArgs_selfArgs]

end Mettapedia.OSLF.Binding.ContextualFamily
