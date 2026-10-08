import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalFormationSoundness

/-!
# Structural rules and equations have actual model readouts

Authored substitutions are interpreted componentwise and composed as genuine
model arrows. Context and annotation conversion use equality of independently
evaluated model data. Typed equation substitution follows the proved complete
syntax/model substitution theorem.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualTypeOperations
open Mettapedia.TypeTheory.ContextualSumComprehension (sigma_second_heq)

universe u c s t m

variable {S : Symbols.{u}} {C : CwfWithTerminal.{c, s, t, m}}

namespace ModelData

variable (model : ModelData S C) {n k l : Nat}

theorem substitutionNil_sound (context : ContextExpr S n)
    (interpreted : Interprets model (.context context)) :
    Interprets model (.substitution context .nil Fin.elim0) := by
  rcases interpreted with ⟨Γ, contextRead⟩
  exact ⟨Γ, Context.nil C, C.toEmpty Γ.1, contextRead, rfl, rfl⟩

theorem substitutionExtend_sound (stable : StrictPiSubstitution model.products)
    (source : ContextExpr S n) (target : ContextExpr S k) (type : TypeExpr S k)
    (substitution : Substitution S k n) (term : TermExpr S n)
    (substitutionInterpreted : Interprets model (.substitution source target substitution))
    (typeInterpreted : Interprets model (.type target type))
    (termInterpreted : Interprets model (.term source term (type.substitute substitution))) :
    Interprets model (.substitution source (.snoc target type) (extendSubstitution substitution term)) := by
  rcases substitutionInterpreted with ⟨Γ, Δ, σ, sourceRead, targetRead, substitutionRead⟩
  rcases typeInterpreted.typeAt Δ targetRead with ⟨A, typeRead⟩
  let modelMap := ModelSubstitution.ofEvaluated model Γ Δ substitution σ substitutionRead
  have substituted := model.evaluateType_substitute stable type Γ Δ substitution modelMap A typeRead
  rcases termInterpreted.termAt Γ _ sourceRead substituted with ⟨value, termRead⟩
  exact ⟨Γ, Δ.snoc A, C.toCwf.pair σ A value, sourceRead,
    model.evaluateContext_snoc target type Δ A targetRead typeRead,
    (modelMap.extend A term value termRead).evaluate⟩

theorem substitutionIdentity_sound (context : ContextExpr S n)
    (interpreted : Interprets model (.context context)) :
    Interprets model (.substitution context context TermExpr.var) := by
  rcases interpreted with ⟨Γ, contextRead⟩
  exact ⟨Γ, Γ, C.toCwf.idS Γ.1, contextRead, contextRead, model.evaluateSubstitution_identity Γ⟩

theorem substitutionCompose_sound (stable : StrictPiSubstitution model.products)
    (source : ContextExpr S n) (middle : ContextExpr S k) (target : ContextExpr S l)
    (first : Substitution S k n) (second : Substitution S l k)
    (firstInterpreted : Interprets model (.substitution source middle first))
    (secondInterpreted : Interprets model (.substitution middle target second)) :
    Interprets model (.substitution source target (composeSubstitution second first)) := by
  rcases firstInterpreted with ⟨Γ, Δ, σ, sourceRead, middleRead, firstRead⟩
  rcases secondInterpreted with ⟨actual, Θ, τ, actualRead, targetRead, secondRead⟩
  cases Option.some.inj (actualRead.symm.trans middleRead)
  exact ⟨Γ, Θ, C.toCwf.compS τ σ, sourceRead, targetRead,
    model.evaluateSubstitution_composition stable Δ Θ Γ second first τ σ secondRead firstRead⟩

theorem substitutionWeaken_sound (context : ContextExpr S n) (type : TypeExpr S n)
    (interpreted : Interprets model (.type context type)) :
    Interprets model (.substitution (.snoc context type) context (fun index => .var index.succ)) := by
  rcases interpreted with ⟨Γ, A, contextRead, typeRead⟩
  refine ⟨Γ.snoc A, Γ, C.toCwf.wk A,
    model.evaluateContext_snoc context type Γ A contextRead typeRead, contextRead, ?_⟩
  exact (model.evaluateSubstitution_eq_some_iff _ _ _ _).mpr (fun _ => rfl)

theorem substituteType_sound (stable : StrictPiSubstitution model.products)
    (source : ContextExpr S n) (target : ContextExpr S k) (substitution : Substitution S k n)
    (type : TypeExpr S k) (substitutionInterpreted : Interprets model (.substitution source target substitution))
    (typeInterpreted : Interprets model (.type target type)) :
    Interprets model (.type source (type.substitute substitution)) := by
  rcases substitutionInterpreted with ⟨Γ, Δ, σ, sourceRead, targetRead, substitutionRead⟩
  rcases typeInterpreted.typeAt Δ targetRead with ⟨A, typeRead⟩
  exact ⟨Γ, C.toCwf.tySub A σ, sourceRead,
    model.evaluateType_substitute stable type Γ Δ substitution
      (ModelSubstitution.ofEvaluated model Γ Δ substitution σ substitutionRead) A typeRead⟩

theorem substituteTerm_sound (stable : StrictPiSubstitution model.products)
    (source : ContextExpr S n) (target : ContextExpr S k) (substitution : Substitution S k n)
    (term : TermExpr S k) (type : TypeExpr S k)
    (substitutionInterpreted : Interprets model (.substitution source target substitution))
    (termInterpreted : Interprets model (.term target term type)) :
    Interprets model (.term source (term.substitute substitution) (type.substitute substitution)) := by
  rcases substitutionInterpreted with ⟨Γ, Δ, σ, sourceRead, targetRead, substitutionRead⟩
  rcases termInterpreted with ⟨actual, A, value, actualRead, typeRead, termRead⟩
  cases Option.some.inj (actualRead.symm.trans targetRead)
  let modelMap := ModelSubstitution.ofEvaluated model Γ Δ substitution σ substitutionRead
  exact ⟨Γ, C.toCwf.tySub A σ, C.toCwf.tmSub value σ, sourceRead,
    model.evaluateType_substitute stable type Γ Δ substitution modelMap A typeRead,
    model.evaluateTerm_substitute stable term Γ Δ substitution modelMap ⟨A, value⟩ termRead⟩

theorem contextReflexivity_sound (context : ContextExpr S n)
    (interpreted : Interprets model (.context context)) : Interprets model (.contextEq context context) := by
  rcases interpreted with ⟨Γ, contextRead⟩
  exact ⟨Γ, contextRead, contextRead⟩

theorem contextSymmetry_sound (first second : ContextExpr S n)
    (interpreted : Interprets model (.contextEq first second)) : Interprets model (.contextEq second first) := by
  rcases interpreted with ⟨Γ, firstRead, secondRead⟩
  exact ⟨Γ, secondRead, firstRead⟩

theorem contextTransitivity_sound (first middle last : ContextExpr S n)
    (firstInterpreted : Interprets model (.contextEq first middle))
    (secondInterpreted : Interprets model (.contextEq middle last)) : Interprets model (.contextEq first last) := by
  rcases firstInterpreted with ⟨Γ, firstRead, middleRead⟩
  exact ⟨Γ, firstRead, secondInterpreted.contextEqAt Γ middleRead⟩

theorem contextExtendEquality_sound (first second : ContextExpr S n)
    (firstType secondType : TypeExpr S n)
    (contextsInterpreted : Interprets model (.contextEq first second))
    (typesInterpreted : Interprets model (.typeEq first firstType secondType)) :
    Interprets model (.contextEq (.snoc first firstType) (.snoc second secondType)) := by
  rcases typesInterpreted with ⟨Γ, A, firstRead, firstTypeRead, secondTypeRead⟩
  exact ⟨Γ.snoc A, model.evaluateContext_snoc first firstType Γ A firstRead firstTypeRead,
    model.evaluateContext_snoc second secondType Γ A
      (contextsInterpreted.contextEqAt Γ firstRead) secondTypeRead⟩

theorem transportType_sound (first second : ContextExpr S n) (type : TypeExpr S n)
    (contextsInterpreted : Interprets model (.contextEq first second))
    (typeInterpreted : Interprets model (.type first type)) : Interprets model (.type second type) := by
  rcases typeInterpreted with ⟨Γ, A, contextRead, typeRead⟩
  exact ⟨Γ, A, contextsInterpreted.contextEqAt Γ contextRead, typeRead⟩

theorem transportTerm_sound (first second : ContextExpr S n) (term : TermExpr S n) (type : TypeExpr S n)
    (contextsInterpreted : Interprets model (.contextEq first second))
    (termInterpreted : Interprets model (.term first term type)) : Interprets model (.term second term type) := by
  rcases termInterpreted with ⟨Γ, A, value, contextRead, typeRead, termRead⟩
  exact ⟨Γ, A, value, contextsInterpreted.contextEqAt Γ contextRead, typeRead, termRead⟩

theorem transportSubstitution_sound (source source' : ContextExpr S n) (target target' : ContextExpr S k)
    (substitution : Substitution S k n)
    (sourcesInterpreted : Interprets model (.contextEq source source'))
    (targetsInterpreted : Interprets model (.contextEq target target'))
    (substitutionInterpreted : Interprets model (.substitution source target substitution)) :
    Interprets model (.substitution source' target' substitution) := by
  rcases substitutionInterpreted with ⟨Γ, Δ, σ, sourceRead, targetRead, substitutionRead⟩
  exact ⟨Γ, Δ, σ, sourcesInterpreted.contextEqAt Γ sourceRead,
    targetsInterpreted.contextEqAt Δ targetRead, substitutionRead⟩

theorem typeReflexivity_sound (context : ContextExpr S n) (type : TypeExpr S n)
    (interpreted : Interprets model (.type context type)) : Interprets model (.typeEq context type type) := by
  rcases interpreted with ⟨Γ, A, contextRead, typeRead⟩
  exact ⟨Γ, A, contextRead, typeRead, typeRead⟩

theorem typeSymmetry_sound (context : ContextExpr S n) (first second : TypeExpr S n)
    (interpreted : Interprets model (.typeEq context first second)) : Interprets model (.typeEq context second first) := by
  rcases interpreted with ⟨Γ, A, contextRead, firstRead, secondRead⟩
  exact ⟨Γ, A, contextRead, secondRead, firstRead⟩

theorem typeTransitivity_sound (context : ContextExpr S n) (first middle last : TypeExpr S n)
    (firstInterpreted : Interprets model (.typeEq context first middle))
    (secondInterpreted : Interprets model (.typeEq context middle last)) : Interprets model (.typeEq context first last) := by
  rcases firstInterpreted with ⟨Γ, A, contextRead, firstRead, middleRead⟩
  exact ⟨Γ, A, contextRead, firstRead, secondInterpreted.typeEqAt Γ A contextRead middleRead⟩

theorem termReflexivity_sound (context : ContextExpr S n) (term : TermExpr S n) (type : TypeExpr S n)
    (interpreted : Interprets model (.term context term type)) : Interprets model (.termEq context term term type) := by
  rcases interpreted with ⟨Γ, A, value, contextRead, typeRead, termRead⟩
  exact ⟨Γ, A, value, contextRead, typeRead, termRead, termRead⟩

theorem termSymmetry_sound (context : ContextExpr S n) (first second : TermExpr S n) (type : TypeExpr S n)
    (interpreted : Interprets model (.termEq context first second type)) :
    Interprets model (.termEq context second first type) := by
  rcases interpreted with ⟨Γ, A, value, contextRead, typeRead, firstRead, secondRead⟩
  exact ⟨Γ, A, value, contextRead, typeRead, secondRead, firstRead⟩

theorem termTransitivity_sound (context : ContextExpr S n) (first middle last : TermExpr S n) (type : TypeExpr S n)
    (firstInterpreted : Interprets model (.termEq context first middle type))
    (secondInterpreted : Interprets model (.termEq context middle last type)) :
    Interprets model (.termEq context first last type) := by
  rcases firstInterpreted with ⟨Γ, A, value, contextRead, typeRead, firstRead, middleRead⟩
  rcases secondInterpreted.termEqAt Γ A contextRead typeRead with ⟨actual, actualMiddle, lastRead⟩
  have same : value = actual :=
    eq_of_heq (sigma_second_heq (Option.some.inj (middleRead.symm.trans actualMiddle)))
  cases same
  exact ⟨Γ, A, value, contextRead, typeRead, firstRead, lastRead⟩

theorem equalityConversion_sound (context : ContextExpr S n) (first second : TermExpr S n)
    (firstType secondType : TypeExpr S n)
    (termsInterpreted : Interprets model (.termEq context first second firstType))
    (typesInterpreted : Interprets model (.typeEq context firstType secondType)) :
    Interprets model (.termEq context first second secondType) := by
  rcases termsInterpreted with ⟨Γ, A, value, contextRead, typeRead, firstRead, secondRead⟩
  exact ⟨Γ, A, value, contextRead, typesInterpreted.typeEqAt Γ A contextRead typeRead, firstRead, secondRead⟩

theorem transportTypeEquality_sound (source target : ContextExpr S n) (first second : TypeExpr S n)
    (contextsInterpreted : Interprets model (.contextEq source target))
    (typesInterpreted : Interprets model (.typeEq source first second)) :
    Interprets model (.typeEq target first second) := by
  rcases typesInterpreted with ⟨Γ, A, contextRead, firstRead, secondRead⟩
  exact ⟨Γ, A, contextsInterpreted.contextEqAt Γ contextRead, firstRead, secondRead⟩

theorem transportTermEquality_sound (source target : ContextExpr S n) (first second : TermExpr S n)
    (type : TypeExpr S n) (contextsInterpreted : Interprets model (.contextEq source target))
    (termsInterpreted : Interprets model (.termEq source first second type)) :
    Interprets model (.termEq target first second type) := by
  rcases termsInterpreted with ⟨Γ, A, value, contextRead, typeRead, firstRead, secondRead⟩
  exact ⟨Γ, A, value, contextsInterpreted.contextEqAt Γ contextRead, typeRead, firstRead, secondRead⟩

theorem substituteTypeEquality_sound (stable : StrictPiSubstitution model.products)
    (source : ContextExpr S n) (target : ContextExpr S k) (substitution : Substitution S k n)
    (first second : TypeExpr S k)
    (substitutionInterpreted : Interprets model (.substitution source target substitution))
    (typesInterpreted : Interprets model (.typeEq target first second)) :
    Interprets model (.typeEq source (first.substitute substitution) (second.substitute substitution)) := by
  rcases substitutionInterpreted with ⟨Γ, Δ, σ, sourceRead, targetRead, substitutionRead⟩
  rcases typesInterpreted with ⟨actual, A, actualRead, firstRead, secondRead⟩
  cases Option.some.inj (actualRead.symm.trans targetRead)
  let modelMap := ModelSubstitution.ofEvaluated model Γ Δ substitution σ substitutionRead
  exact ⟨Γ, C.toCwf.tySub A σ, sourceRead,
    model.evaluateType_substitute stable first Γ Δ substitution modelMap A firstRead,
    model.evaluateType_substitute stable second Γ Δ substitution modelMap A secondRead⟩

theorem substituteTermEquality_sound (stable : StrictPiSubstitution model.products)
    (source : ContextExpr S n) (target : ContextExpr S k) (substitution : Substitution S k n)
    (first second : TermExpr S k) (type : TypeExpr S k)
    (substitutionInterpreted : Interprets model (.substitution source target substitution))
    (termsInterpreted : Interprets model (.termEq target first second type)) :
    Interprets model (.termEq source (first.substitute substitution) (second.substitute substitution)
      (type.substitute substitution)) := by
  rcases substitutionInterpreted with ⟨Γ, Δ, σ, sourceRead, targetRead, substitutionRead⟩
  rcases termsInterpreted with ⟨actual, A, value, actualRead, typeRead, firstRead, secondRead⟩
  cases Option.some.inj (actualRead.symm.trans targetRead)
  let modelMap := ModelSubstitution.ofEvaluated model Γ Δ substitution σ substitutionRead
  exact ⟨Γ, C.toCwf.tySub A σ, C.toCwf.tmSub value σ, sourceRead,
    model.evaluateType_substitute stable type Γ Δ substitution modelMap A typeRead,
    model.evaluateTerm_substitute stable first Γ Δ substitution modelMap ⟨A, value⟩ firstRead,
    model.evaluateTerm_substitute stable second Γ Δ substitution modelMap ⟨A, value⟩ secondRead⟩

theorem substitutionReflexivity_sound (source : ContextExpr S n) (target : ContextExpr S k)
    (substitution : Substitution S k n)
    (interpreted : Interprets model (.substitution source target substitution)) :
    Interprets model (.substitutionEq source target substitution substitution) := by
  rcases interpreted with ⟨Γ, Δ, σ, sourceRead, targetRead, substitutionRead⟩
  exact ⟨Γ, Δ, σ, sourceRead, targetRead, substitutionRead, substitutionRead⟩

theorem substitutionSymmetry_sound (source : ContextExpr S n) (target : ContextExpr S k)
    (first second : Substitution S k n)
    (interpreted : Interprets model (.substitutionEq source target first second)) :
    Interprets model (.substitutionEq source target second first) := by
  rcases interpreted with ⟨Γ, Δ, σ, sourceRead, targetRead, firstRead, secondRead⟩
  exact ⟨Γ, Δ, σ, sourceRead, targetRead, secondRead, firstRead⟩

theorem substitutionTransitivity_sound (source : ContextExpr S n) (target : ContextExpr S k)
    (first middle last : Substitution S k n)
    (firstInterpreted : Interprets model (.substitutionEq source target first middle))
    (secondInterpreted : Interprets model (.substitutionEq source target middle last)) :
    Interprets model (.substitutionEq source target first last) := by
  rcases firstInterpreted with ⟨Γ, Δ, σ, sourceRead, targetRead, firstRead, middleRead⟩
  rcases secondInterpreted.substitutionEqAt Γ Δ sourceRead targetRead with ⟨τ, actualMiddle, lastRead⟩
  cases Option.some.inj (middleRead.symm.trans actualMiddle)
  exact ⟨Γ, Δ, σ, sourceRead, targetRead, firstRead, lastRead⟩

theorem substitutionExtendEquality_sound (stable : StrictPiSubstitution model.products)
    (source : ContextExpr S n) (target : ContextExpr S k) (type : TypeExpr S k)
    (first second : Substitution S k n) (firstTerm secondTerm : TermExpr S n)
    (substitutionsInterpreted : Interprets model (.substitutionEq source target first second))
    (typeInterpreted : Interprets model (.type target type))
    (termsInterpreted : Interprets model (.termEq source firstTerm secondTerm (type.substitute first))) :
    Interprets model (.substitutionEq source (.snoc target type)
      (extendSubstitution first firstTerm) (extendSubstitution second secondTerm)) := by
  rcases substitutionsInterpreted with ⟨Γ, Δ, σ, sourceRead, targetRead, firstRead, secondRead⟩
  rcases typeInterpreted.typeAt Δ targetRead with ⟨A, typeRead⟩
  let firstMap := ModelSubstitution.ofEvaluated model Γ Δ first σ firstRead
  let secondMap := ModelSubstitution.ofEvaluated model Γ Δ second σ secondRead
  have substituted := model.evaluateType_substitute stable type Γ Δ first firstMap A typeRead
  rcases termsInterpreted.termEqAt Γ _ sourceRead substituted with ⟨value, firstTermRead, secondTermRead⟩
  exact ⟨Γ, Δ.snoc A, C.toCwf.pair σ A value, sourceRead,
    model.evaluateContext_snoc target type Δ A targetRead typeRead,
    (firstMap.extend A firstTerm value firstTermRead).evaluate,
    (secondMap.extend A secondTerm value secondTermRead).evaluate⟩

theorem typeSubstitutionCongruence_sound (stable : StrictPiSubstitution model.products)
    (source : ContextExpr S n) (target : ContextExpr S k) (first second : Substitution S k n)
    (type : TypeExpr S k)
    (substitutionsInterpreted : Interprets model (.substitutionEq source target first second))
    (typeInterpreted : Interprets model (.type target type)) :
    Interprets model (.typeEq source (type.substitute first) (type.substitute second)) := by
  rcases substitutionsInterpreted with ⟨Γ, Δ, σ, sourceRead, targetRead, firstRead, secondRead⟩
  rcases typeInterpreted.typeAt Δ targetRead with ⟨A, typeRead⟩
  exact ⟨Γ, C.toCwf.tySub A σ, sourceRead,
    model.evaluateType_substitute stable type Γ Δ first
      (ModelSubstitution.ofEvaluated model Γ Δ first σ firstRead) A typeRead,
    model.evaluateType_substitute stable type Γ Δ second
      (ModelSubstitution.ofEvaluated model Γ Δ second σ secondRead) A typeRead⟩

theorem termSubstitutionCongruence_sound (stable : StrictPiSubstitution model.products)
    (source : ContextExpr S n) (target : ContextExpr S k) (first second : Substitution S k n)
    (term : TermExpr S k) (type : TypeExpr S k)
    (substitutionsInterpreted : Interprets model (.substitutionEq source target first second))
    (termInterpreted : Interprets model (.term target term type)) :
    Interprets model (.termEq source (term.substitute first) (term.substitute second) (type.substitute first)) := by
  rcases substitutionsInterpreted with ⟨Γ, Δ, σ, sourceRead, targetRead, firstRead, secondRead⟩
  rcases termInterpreted with ⟨actual, A, value, actualRead, typeRead, termRead⟩
  cases Option.some.inj (actualRead.symm.trans targetRead)
  let firstMap := ModelSubstitution.ofEvaluated model Γ Δ first σ firstRead
  exact ⟨Γ, C.toCwf.tySub A σ, C.toCwf.tmSub value σ, sourceRead,
    model.evaluateType_substitute stable type Γ Δ first firstMap A typeRead,
    model.evaluateTerm_substitute stable term Γ Δ first firstMap ⟨A, value⟩ termRead,
    model.evaluateTerm_substitute stable term Γ Δ second
      (ModelSubstitution.ofEvaluated model Γ Δ second σ secondRead) ⟨A, value⟩ termRead⟩

end ModelData

end Mettapedia.TypeTheory.Calculi.NativeDependent.External
