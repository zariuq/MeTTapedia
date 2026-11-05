import Mettapedia.Logic.HOL.ConstructorArgumentRecoveryLaws

/-!
# Reusing a retained universal constructor-recovery theorem

Typed substitution and explicit premise-occurrence transport move a retained
recovery theorem to the caller's context. Three universal eliminations and
the supplied admission proof then recover the original payload. This gives
equivalence of proof existence, including the extensionality-free fragment;
it does not identify the resulting proof trees or their observations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.ConstructorArgumentMap

universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base}
  {first source target third : Ty Base} {premises : List (Formula Const Γ)}

theorem recoveryStatement_subst (images : Subst Const Γ Ξ)
    (lower : Term Const Γ (source ⇒ target)) (raise : Term Const Γ (target ⇒ source))
    (domain : Term Const Γ (GuardedConstructorProjections.Admission first source third)) :
    HOL.subst images (recoveryStatement lower raise domain) =
      recoveryStatement (HOL.subst images lower) (HOL.subst images raise) (HOL.subst images domain) := by
  simp only [recoveryStatement, GuardedConstructorProjections.admitted, ConstructorProjections.apply,
    HOL.subst, subst_weaken, Subst.lift, HOL.rename, Rename.weaken]

private theorem subst_vars {type : Ty Base} (term : Term Const Γ type) :
    HOL.subst (fun {type} (index : Var Γ type) => Term.var index) term = term := subst_id term

private theorem subst_drop_shift {bound type : Ty Base} (value : Term Const Γ bound)
    (term : Term Const Γ type) :
    HOL.subst (Subst.comp (Subst.single value) (fun index => Term.var (.vs index))) term = term := by
  have identity : (Subst.comp (Subst.single value) (fun index => Term.var (.vs index)) : Subst Const Γ Γ) =
      (fun {type} (index : Var Γ type) => Term.var index) := by
    funext type index
    rfl
  rw [identity]
  exact subst_id term

@[irreducible] def specializeRecoveryLaw {assumptions : List (Formula Const Γ)}
    (lower : Term Const Γ (source ⇒ target)) (raise : Term Const Γ (target ⇒ source))
    (domain : Term Const Γ (GuardedConstructorProjections.Admission first source third))
    (tag : Term Const Γ first) (payload : Term Const Γ source) (children : Term Const Γ third)
    (law : ProofSyntax Const assumptions (recoveryStatement lower raise domain)) :
    ProofSyntax Const assumptions (.imp (GuardedConstructorProjections.admitted domain tag payload children)
      (.eq (.app raise (.app lower payload)) payload)) := by
  apply ProofSyntax.castIndices rfl ?_ (.allE children (.allE payload (.allE tag law)))
  simp [instantiate, GuardedConstructorProjections.admitted, ConstructorProjections.apply,
    HOL.subst, subst_weaken, Subst.single, Subst.lift, Rename.weaken,
    subst_rename, subst_comp, subst_drop_shift, subst_vars]

theorem specializeRecoveryLaw_free {assumptions : List (Formula Const Γ)}
    (lower : Term Const Γ (source ⇒ target)) (raise : Term Const Γ (target ⇒ source))
    (domain : Term Const Γ (GuardedConstructorProjections.Admission first source third))
    (tag : Term Const Γ first) (payload : Term Const Γ source) (children : Term Const Γ third)
    (law : ProofSyntax Const assumptions (recoveryStatement lower raise domain))
    (lawFree : law.FunctionExtensionalityFree) :
    (specializeRecoveryLaw lower raise domain tag payload children law).FunctionExtensionalityFree := by
  unfold specializeRecoveryLaw
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact lawFree

@[irreducible] def recoveryOfLaw (lower : Term Const Γ (source ⇒ target))
    (raise : Term Const Γ (target ⇒ source))
    (domain : Term Const Γ (GuardedConstructorProjections.Admission first source third))
    (law : ProofSyntax Const premises (recoveryStatement lower raise domain)) :
    Recovery premises lower raise domain := by
  intro Ξ images assumptions transport tag payload children present
  have currentLaw : ProofSyntax Const assumptions
      (recoveryStatement (HOL.subst images lower) (HOL.subst images raise) (HOL.subst images domain)) :=
    .castIndices rfl (recoveryStatement_subst images lower raise domain) (.mono transport (law.subst images))
  exact .impE (specializeRecoveryLaw (HOL.subst images lower) (HOL.subst images raise)
    (HOL.subst images domain) tag payload children currentLaw) present

theorem recoveryOfLaw_free (lower : Term Const Γ (source ⇒ target))
    (raise : Term Const Γ (target ⇒ source))
    (domain : Term Const Γ (GuardedConstructorProjections.Admission first source third))
    (law : ProofSyntax Const premises (recoveryStatement lower raise domain))
    (lawFree : law.FunctionExtensionalityFree) : Recovery.Free (recoveryOfLaw lower raise domain law) := by
  intro Ξ images assumptions transport tag payload children present presentFree
  unfold recoveryOfLaw
  refine ⟨?_, presentFree⟩
  apply specializeRecoveryLaw_free
  exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    ((ProofSyntax.functionExtensionalityFree_mono _ _).mpr
      ((ProofSyntax.functionExtensionalityFree_subst _ _).mpr lawFree))

theorem recovery_nonempty_iff_statement (lower : Term Const Γ (source ⇒ target))
    (raise : Term Const Γ (target ⇒ source))
    (domain : Term Const Γ (GuardedConstructorProjections.Admission first source third)) :
    Nonempty (Recovery premises lower raise domain) ↔
      Nonempty (ProofSyntax Const premises (recoveryStatement lower raise domain)) := by
  constructor
  · rintro ⟨recover⟩
    exact ⟨recoveryLaw lower raise domain recover⟩
  · rintro ⟨law⟩
    exact ⟨recoveryOfLaw lower raise domain law⟩

theorem free_recovery_iff_free_statement (lower : Term Const Γ (source ⇒ target))
    (raise : Term Const Γ (target ⇒ source))
    (domain : Term Const Γ (GuardedConstructorProjections.Admission first source third)) :
    (∃ recover : Recovery premises lower raise domain, Recovery.Free recover) ↔
      ∃ law : ProofSyntax Const premises (recoveryStatement lower raise domain),
        law.FunctionExtensionalityFree := by
  constructor
  · rintro ⟨recover, free⟩
    exact ⟨recoveryLaw lower raise domain recover, recoveryLaw_free lower raise domain recover free⟩
  · rintro ⟨law, free⟩
    exact ⟨recoveryOfLaw lower raise domain law, recoveryOfLaw_free lower raise domain law free⟩

#print axioms recoveryStatement_subst
#print axioms specializeRecoveryLaw_free
#print axioms recoveryOfLaw
#print axioms recoveryOfLaw_free
#print axioms recovery_nonempty_iff_statement
#print axioms free_recovery_iff_free_statement

end Mettapedia.Logic.HOL.ConstructorArgumentMap
