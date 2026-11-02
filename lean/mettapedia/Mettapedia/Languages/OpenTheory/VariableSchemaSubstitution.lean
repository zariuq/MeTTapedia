import Mettapedia.Languages.OpenTheory.ReverseTranslation
import Mettapedia.Logic.HOL.TermInterpretationLaws

/-!
# Native substitution for HOL schemas with variable parameters

The source uses the existing HOL grammar with no user constants. Logical
constructors and arbitrarily typed variable parameters remain available.
Native simultaneous substitution acts on their encoded variable images and
commutes with every syntax constructor, including beneath binders.

Actual replacement images may contain arbitrary symbols and may mention the
substitution's own keys. No disjointness or injectivity condition is imposed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.OpenTheory.ReverseTranslation.VariableSchema
open Mettapedia.Logic

abbrev ParameterTerm (context : HOL.Ctx AtomicTy) (type : HOL.Ty AtomicTy) :=
  HOL.Term (fun _ : HOL.Ty AtomicTy => Empty) context type

def embed {Γ : HOL.Ctx AtomicTy} {type : HOL.Ty AtomicTy} (term : ParameterTerm Γ type) :
    HOL.Term Symbol Γ type := HOL.mapConst (fun impossible => nomatch impossible) term

def mapped (substitution : TermSubst) {Γ : HOL.Ctx AtomicTy} {type : HOL.Ty AtomicTy}
    (term : ParameterTerm Γ type) :
    HOL.Term Symbol (Γ.map (HOL.Ty.substitute substitution.types.baseInstance))
      (HOL.Ty.substitute substitution.types.baseInstance type) :=
  HOL.mapTypes substitution.types.baseInstance (fun impossible => nomatch impossible) term

def reading (types : TypeSubst) :
    HOL.TermInterpretation AtomicTy (fun _ : HOL.Ty AtomicTy => Empty) AtomicTy Symbol :=
  ⟨types.baseInstance, fun impossible => nomatch impossible⟩

theorem mapped_read (substitution : TermSubst) :
    ∀ {Γ : HOL.Ctx AtomicTy} {type : HOL.Ty AtomicTy} (term : ParameterTerm Γ type),
      mapped substitution term = (reading substitution.types).term term
  | _, _, .var _ => rfl
  | _, _, .const impossible => nomatch impossible
  | _, _, .app function argument => by
    simp only [mapped, HOL.mapTypes, HOL.TermInterpretation.term_app]
    exact congrArg₂ HOL.Term.app (mapped_read substitution function) (mapped_read substitution argument)
  | _, _, .lam body => by
    simp only [mapped, HOL.mapTypes, HOL.TermInterpretation.term_lam]
    exact congrArg HOL.Term.lam (mapped_read substitution body)
  | _, _, .top => rfl
  | _, _, .bot => rfl
  | _, _, .and first second => by
    simp only [mapped, HOL.mapTypes, HOL.TermInterpretation.term_and]
    exact congrArg₂ HOL.Term.and (mapped_read substitution first) (mapped_read substitution second)
  | _, _, .or first second => by
    simp only [mapped, HOL.mapTypes, HOL.TermInterpretation.term_or]
    exact congrArg₂ HOL.Term.or (mapped_read substitution first) (mapped_read substitution second)
  | _, _, .imp first second => by
    simp only [mapped, HOL.mapTypes, HOL.TermInterpretation.term_imp]
    exact congrArg₂ HOL.Term.imp (mapped_read substitution first) (mapped_read substitution second)
  | _, _, .not body => by
    simp only [mapped, HOL.mapTypes, HOL.TermInterpretation.term_not]
    exact congrArg HOL.Term.not (mapped_read substitution body)
  | _, _, .eq first second => by
    simp only [mapped, HOL.mapTypes, HOL.TermInterpretation.term_eq]
    exact congrArg₂ HOL.Term.eq (mapped_read substitution first) (mapped_read substitution second)
  | _, _, .all body => by
    simp only [mapped, HOL.mapTypes, HOL.TermInterpretation.term_all]
    exact congrArg HOL.Term.all (mapped_read substitution body)
  | _, _, .ex body => by
    simp only [mapped, HOL.mapTypes, HOL.TermInterpretation.term_ex]
    exact congrArg HOL.Term.ex (mapped_read substitution body)

theorem lift_compatible (substitution : TermSubst) {Γ : HOL.Ctx AtomicTy} {domain : HOL.Ty AtomicTy}
    (env : VarEnv Γ) (target : VarEnv (Γ.map (HOL.Ty.substitute substitution.types.baseInstance)))
    (compatible : ∀ {type : HOL.Ty AtomicTy} (index : HOL.Var Γ type),
      target (index.mapTypes substitution.types.baseInstance) = substitution.applyDB (env index)) :
    ∀ {type : HOL.Ty AtomicTy} (index : HOL.Var (domain :: Γ) type),
      VarEnv.lift target (index.mapTypes substitution.types.baseInstance) =
        substitution.applyDB (VarEnv.lift env index) := by
  intro type index
  cases index with
  | vz => simp only [HOL.Var.mapTypes, VarEnv.lift, TermSubst.applyDB_bound]
  | vs index =>
    change shiftLoose 0 (target (index.mapTypes substitution.types.baseInstance)) =
      substitution.applyDB (shiftLoose 0 (env index))
    rw [applyDB_shiftLoose, compatible index]

theorem reverse_action (substitution : TermSubst) :
    ∀ {Γ : HOL.Ctx AtomicTy} {type : HOL.Ty AtomicTy} (term : ParameterTerm Γ type)
      (env : VarEnv Γ) (target : VarEnv (Γ.map (HOL.Ty.substitute substitution.types.baseInstance))),
      (∀ {type : HOL.Ty AtomicTy} (index : HOL.Var Γ type),
        target (index.mapTypes substitution.types.baseInstance) = substitution.applyDB (env index)) →
      reverseTermWith target (mapped substitution term) =
        substitution.applyDB (reverseTermWith env (embed term))
  | _, _, .var index, env, target, compatible => compatible index
  | _, _, .const impossible, _, _, _ => nomatch impossible
  | _, _, .app function argument, env, target, compatible => by
    simp only [mapped, embed, HOL.mapConst, HOL.mapTypes, reverseTermWith, TermSubst.applyDB_app]
    exact congrArg₂ DBTerm.app (reverse_action substitution function env target compatible)
      (reverse_action substitution argument env target compatible)
  | _, _, .lam (σ := domain) body, env, target, compatible => by
    simp only [mapped, embed, HOL.mapConst, HOL.mapTypes, reverseTermWith, TermSubst.applyDB_abs]
    rw [reverseTy_substitute]
    exact congrArg (DBTerm.abs _) (reverse_action substitution body (VarEnv.lift env) (VarEnv.lift target)
      (lift_compatible substitution env target compatible))
  | _, _, .top, _, _, _ => (applyDB_truthDB substitution).symm
  | _, _, .bot, _, _, _ => (applyDB_falsityDefinitionDB substitution).symm
  | _, _, .and first second, env, target, compatible => by
    simp only [mapped, embed, HOL.mapConst, HOL.mapTypes, reverseTermWith, TermSubst.applyDB_app, applyDB_andDB]
    exact congrArg₂ (fun left right => DBTerm.app (.app ExcludedMiddle.andDB left) right)
      (reverse_action substitution first env target compatible) (reverse_action substitution second env target compatible)
  | _, _, .or first second, env, target, compatible => by
    simp only [mapped, embed, HOL.mapConst, HOL.mapTypes, reverseTermWith, TermSubst.applyDB_app, applyDB_orDB]
    exact congrArg₂ (fun left right => DBTerm.app (.app ExcludedMiddle.orDB left) right)
      (reverse_action substitution first env target compatible) (reverse_action substitution second env target compatible)
  | _, _, .imp first second, env, target, compatible => by
    simp only [mapped, embed, HOL.mapConst, HOL.mapTypes, reverseTermWith, ExcludedMiddle.impAppDB,
      TermSubst.applyDB_app, applyDB_impDB]
    exact congrArg₂ (fun left right => DBTerm.app (.app ExcludedMiddle.impDB left) right)
      (reverse_action substitution first env target compatible) (reverse_action substitution second env target compatible)
  | _, _, .not body, env, target, compatible => by
    simp only [mapped, embed, HOL.mapConst, HOL.mapTypes, reverseTermWith, TermSubst.applyDB_app, applyDB_notDB]
    exact congrArg (DBTerm.app ExcludedMiddle.notDB) (reverse_action substitution body env target compatible)
  | _, _, .eq (τ := operand) first second, env, target, compatible => by
    simp only [mapped, embed, HOL.mapConst, HOL.mapTypes, reverseTermWith, CanonicalTerm.equalityDB,
      TermSubst.applyDB_app, TermSubst.applyDB_const, TypeSubst.apply_equality]
    rw [reverseTy_substitute]
    exact congrArg₂ (fun left right => DBTerm.app (.app (.const Const.equality _) left) right)
      (reverse_action substitution first env target compatible) (reverse_action substitution second env target compatible)
  | _, _, .all (σ := domain) body, env, target, compatible => by
    simp only [mapped, embed, HOL.mapConst, HOL.mapTypes, reverseTermWith, TermSubst.applyDB_app, TermSubst.applyDB_abs]
    rw [reverseTy_substitute, applyDB_forallDB]
    exact congrArg (fun body => DBTerm.app (ExcludedMiddle.forallDB _) (.abs _ body))
      (reverse_action substitution body (VarEnv.lift env) (VarEnv.lift target)
        (lift_compatible substitution env target compatible))
  | _, _, .ex (σ := domain) body, env, target, compatible => by
    simp only [mapped, embed, HOL.mapConst, HOL.mapTypes, reverseTermWith, TermSubst.applyDB_app, TermSubst.applyDB_abs]
    rw [reverseTy_substitute, applyDB_existsDB]
    exact congrArg (fun body => DBTerm.app (DefinedConnectives.existsDB _) (.abs _ body))
      (reverse_action substitution body (VarEnv.lift env) (VarEnv.lift target)
        (lift_compatible substitution env target compatible))

theorem named_action (substitution : TermSubst) {Γ Δ : HOL.Ctx AtomicTy} {type : HOL.Ty AtomicTy}
    (term : ParameterTerm Γ type) (sourceNames : Naming Γ) (targetNames : Naming Δ)
    (theta : HOL.Subst Symbol (Γ.map (HOL.Ty.substitute substitution.types.baseInstance)) Δ)
    (compatible : ∀ {type : HOL.Ty AtomicTy} (index : HOL.Var Γ type),
      reverseTerm targetNames (theta (index.mapTypes substitution.types.baseInstance)) =
        substitution.applyDB (Naming.env sourceNames index)) :
    reverseTerm targetNames (HOL.subst theta (mapped substitution term)) =
      substitution.applyDB (reverseTerm sourceNames (embed term)) := by
  change reverseTermWith (Naming.env targetNames) (HOL.subst theta (mapped substitution term)) = _
  rw [reverseTermWith_subst]
  exact reverse_action substitution term (Naming.env sourceNames)
    (fun index => reverseTerm targetNames (theta index)) compatible

theorem canonical_action (substitution : TypeCorrectTermSubstitution) {Γ Δ : HOL.Ctx AtomicTy} {type : HOL.Ty AtomicTy}
    (term : ParameterTerm Γ type) (sourceNames : Naming Γ) (targetNames : Naming Δ)
    (theta : HOL.Subst Symbol (Γ.map (HOL.Ty.substitute substitution.raw.types.baseInstance)) Δ)
    (compatible : ∀ {type : HOL.Ty AtomicTy} (index : HOL.Var Γ type),
      reverseTerm targetNames (theta (index.mapTypes substitution.raw.types.baseInstance)) =
        substitution.raw.applyDB (Naming.env sourceNames index)) :
    substitution.apply (reverseCanonical sourceNames (embed term)) =
      reverseCanonical targetNames (HOL.subst theta (mapped substitution.raw term)) := by
  apply CanonicalTerm.ext_term
  exact (named_action substitution.raw term sourceNames targetNames theta compatible).symm

#print axioms reverse_action
#print axioms lift_compatible
#print axioms canonical_action

end Mettapedia.Languages.OpenTheory.ReverseTranslation.VariableSchema
