import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualSubstitution

/-!
# Admitted binder substitutions for judgment regularity

Instantiation, lifting and pair packing are built from actual generated
substitution rules. Their component equations preserve the supplied typed
terms. These lemmas require local formation and typing judgments, with no
semantic interpretation or global declaration-realization assumption.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
namespace JudgmentRegularity

open Contextual

universe u
variable {S : Symbols.{u}} {D : Signature S}

theorem identity {n : Nat} {context : ContextExpr S n}
    (formed : Formed D context) : Holds D (.substitution context context TermExpr.var) :=
  conclude (.substitutionIdentity context) ⟨formed.judgment, trivial⟩

theorem weaken {n : Nat} {context : ContextExpr S n} {type : TypeExpr S n}
    (typed : Holds D (.type context type)) :
    Holds D (.substitution (.snoc context type) context (fun index => .var index.succ)) :=
  conclude (.substitutionWeaken context type) ⟨typed, trivial⟩

theorem instantiationSubstitution {n : Nat} {context : ContextExpr S n} {type : TypeExpr S n}
    {term : TermExpr S n} (formed : Formed D context)
    (typed : Holds D (.type context type)) (admitted : Holds D (.term context term type)) :
    Holds D (.substitution context (.snoc context type) (instantiate term)) := by
  have value : Holds D (.term context term (type.substitute TermExpr.var)) := by
    simpa only [TypeExpr.substitute_identity] using admitted
  exact conclude (.substitutionExtend context context type TermExpr.var term)
    ⟨identity formed, typed, value, trivial⟩

theorem predicateSubstitute {n m : Nat} {source : ContextExpr S n} {target : ContextExpr S m}
    {substitution : Substitution S m n} {predicate : PropExpr S m}
    (admitted : Holds D (.substitution source target substitution))
    (formed : Holds D (.predicate target predicate)) :
    Holds D (.predicate source (predicate.substitute substitution)) :=
  conclude (.substitutePredicate source target substitution predicate) ⟨admitted, formed, trivial⟩

theorem predicateAt {n : Nat} {context : ContextExpr S n} {domain : TypeExpr S n}
    {predicate : PropExpr S (n + 1)} {term : TermExpr S n}
    (formed : Formed D context) (domainTyped : Holds D (.type context domain))
    (predicateFormed : Holds D (.predicate (.snoc context domain) predicate))
    (termTyped : Holds D (.term context term domain)) :
    Holds D (.predicate context (predicate.substitute (instantiate term))) :=
  predicateSubstitute (instantiationSubstitution formed domainTyped termTyped) predicateFormed

theorem typeAt {n : Nat} {context : ContextExpr S n} {domain : TypeExpr S n}
    {body : TypeExpr S (n + 1)} {term : TermExpr S n}
    (formed : Formed D context) (domainTyped : Holds D (.type context domain))
    (bodyTyped : Holds D (.type (.snoc context domain) body))
    (termTyped : Holds D (.term context term domain)) :
    Holds D (.type context (body.substitute (instantiate term))) :=
  typeSubstitute (instantiationSubstitution formed domainTyped termTyped) bodyTyped

theorem termAt {n : Nat} {context : ContextExpr S n} {domain : TypeExpr S n}
    {body : TypeExpr S (n + 1)} {term : TermExpr S (n + 1)} {argument : TermExpr S n}
    (formed : Formed D context) (domainTyped : Holds D (.type context domain))
    (typed : Holds D (.term (.snoc context domain) term body))
    (argumentTyped : Holds D (.term context argument domain)) :
    Holds D (.term context (term.substitute (instantiate argument))
      (body.substitute (instantiate argument))) :=
  termSubstitute (instantiationSubstitution formed domainTyped argumentTyped) typed

theorem convert {n : Nat} {context : ContextExpr S n} {term : TermExpr S n}
    {first second : TypeExpr S n} (typed : Holds D (.term context term first))
    (same : Holds D (.typeEq context first second)) : Holds D (.term context term second) :=
  conclude (.termConversion context term first second) ⟨typed, same, trivial⟩

theorem typeSymmetry {n : Nat} {context : ContextExpr S n} {first second : TypeExpr S n}
    (same : Holds D (.typeEq context first second)) : Holds D (.typeEq context second first) :=
  conclude (.typeSymmetry context first second) ⟨same, trivial⟩

theorem typeTransitivity {n : Nat} {context : ContextExpr S n} {first middle last : TypeExpr S n}
    (earlier : Holds D (.typeEq context first middle)) (later : Holds D (.typeEq context middle last)) :
    Holds D (.typeEq context first last) :=
  conclude (.typeTransitivity context first middle last) ⟨earlier, later, trivial⟩

theorem sectionEquality {n : Nat} {context : ContextExpr S n} {domain : TypeExpr S n}
    {first second : TermExpr S n} (formed : Formed D context)
    (domainTyped : Holds D (.type context domain))
    (same : Holds D (.termEq context first second domain))
    (secondTyped : Holds D (.term context second domain)) :
    Holds D (.substitutionEq context (.snoc context domain) (instantiate first) (instantiate second)) := by
  have base := conclude (.substitutionReflexivity context context TermExpr.var)
    ⟨identity formed, trivial⟩
  have values : Holds D (.termEq context first second (domain.substitute TermExpr.var)) := by
    simpa only [TypeExpr.substitute_identity] using same
  have secondValue : Holds D (.term context second (domain.substitute TermExpr.var)) := by
    simpa only [TypeExpr.substitute_identity] using secondTyped
  exact conclude (.substitutionExtendEquality context context domain TermExpr.var TermExpr.var first second)
    ⟨base, domainTyped, values, secondValue, trivial⟩

theorem typeAtCongruence {n : Nat} {context : ContextExpr S n} {domain : TypeExpr S n}
    {firstBody secondBody : TypeExpr S (n + 1)} {first second : TermExpr S n}
    (formed : Formed D context) (domainTyped : Holds D (.type context domain))
    (bodyTyped : Holds D (.type (.snoc context domain) firstBody))
    (bodies : Holds D (.typeEq (.snoc context domain) firstBody secondBody))
    (arguments : Holds D (.termEq context first second domain))
    (secondTyped : Holds D (.term context second domain)) :
    Holds D (.typeEq context (firstBody.substitute (instantiate first))
      (secondBody.substitute (instantiate second))) := by
  have argumentChange := conclude (.typeSubstitutionCongruence context (.snoc context domain)
    (instantiate first) (instantiate second) firstBody)
    ⟨sectionEquality formed domainTyped arguments secondTyped, bodyTyped, trivial⟩
  have bodyChange := conclude (.substituteTypeEquality context (.snoc context domain)
    (instantiate second) firstBody secondBody)
    ⟨instantiationSubstitution formed domainTyped secondTyped, bodies, trivial⟩
  exact typeTransitivity argumentChange bodyChange

theorem typeAtArgumentEquality {n : Nat} {context : ContextExpr S n} {domain : TypeExpr S n}
    {body : TypeExpr S (n + 1)} {first second : TermExpr S n}
    (formed : Formed D context) (domainTyped : Holds D (.type context domain))
    (bodyTyped : Holds D (.type (.snoc context domain) body))
    (arguments : Holds D (.termEq context first second domain))
    (secondTyped : Holds D (.term context second domain)) :
    Holds D (.typeEq context (body.substitute (instantiate first))
      (body.substitute (instantiate second))) :=
  conclude (.typeSubstitutionCongruence context (.snoc context domain)
    (instantiate first) (instantiate second) body)
    ⟨sectionEquality formed domainTyped arguments secondTyped, bodyTyped, trivial⟩

theorem components {n : Nat} {context : ContextExpr S n} {domain : TypeExpr S n}
    {body : TypeExpr S (n + 1)} {first second : TermExpr S n}
    (formed : Formed D context) (domainTyped : Holds D (.type context domain))
    (bodyTyped : Holds D (.type (.snoc context domain) body))
    (firstTyped : Holds D (.term context first domain))
    (secondTyped : Holds D (.term context second (body.substitute (instantiate first)))) :
    Holds D (.substitution context (.snoc (.snoc context domain) body)
      (instantiateComponents first second)) :=
  conclude (.substitutionExtend context (.snoc context domain) body (instantiate first) second)
    ⟨instantiationSubstitution formed domainTyped firstTyped, bodyTyped, secondTyped, trivial⟩

theorem lifted {n m : Nat} {source : ContextExpr S n} {target : ContextExpr S m}
    {substitution : Substitution S m n} {domain : TypeExpr S m}
    (sourceFormed : Formed D source)
    (admitted : Holds D (.substitution source target substitution))
    (domainTyped : Holds D (.type target domain)) :
    Holds D (.substitution (.snoc source (domain.substitute substitution)) (.snoc target domain)
      (liftSubstitution substitution)) := by
  have pulledDomain := typeSubstitute admitted domainTyped
  have extendedFormed : Formed D (.snoc source (domain.substitute substitution)) :=
    .snoc sourceFormed pulledDomain
  have base := substitutionCompose (weaken pulledDomain) admitted
  have head := conclude (.variable (.snoc source (domain.substitute substitution)) 0)
    ⟨extendedFormed.judgment, trivial⟩
  have headType : Holds D (.term (.snoc source (domain.substitute substitution)) (.var 0)
      (domain.substitute (composeSubstitution substitution (fun index => .var index.succ)))) := by
    change Holds D (.term (.snoc source (domain.substitute substitution)) (.var 0)
      (domain.substitute (fun index => (substitution index).substitute (fun index => .var index.succ))))
    rw [← TypeExpr.substitute_comp, TypeExpr.substitute_variables]
    simpa only [RuleCode.conclusion, ContextExpr.lookup_zero] using head
  have result := conclude (.substitutionExtend (.snoc source (domain.substitute substitution))
    target domain (composeSubstitution substitution (fun index => .var index.succ)) (.var 0))
    ⟨base, domainTyped, headType, trivial⟩
  have mapping : extendSubstitution
      (composeSubstitution substitution (fun index => .var index.succ)) (.var 0) =
      liftSubstitution substitution := by
    funext index
    cases index using Fin.cases with
    | zero => rfl
    | succ index => exact TermExpr.substitute_variables Fin.succ (substitution index)
  simpa only [RuleCode.conclusion, mapping] using result

theorem typeWeaken {n : Nat} {context : ContextExpr S n} {domain type : TypeExpr S n}
    (domainTyped : Holds D (.type context domain)) (typed : Holds D (.type context type)) :
    Holds D (.type (.snoc context domain) (type.rename Fin.succ)) := by
  simpa only [TypeExpr.substitute_variables] using typeSubstitute (weaken domainTyped) typed

theorem termWeaken {n : Nat} {context : ContextExpr S n} {domain type : TypeExpr S n}
    {term : TermExpr S n} (domainTyped : Holds D (.type context domain))
    (typed : Holds D (.term context term type)) :
    Holds D (.term (.snoc context domain) (term.rename Fin.succ) (type.rename Fin.succ)) := by
  simpa only [TypeExpr.substitute_variables, TermExpr.substitute_variables] using
    termSubstitute (weaken domainTyped) typed

theorem bodyWeaken {n : Nat} {context : ContextExpr S n} {domain : TypeExpr S n}
    {body : TypeExpr S (n + 1)} (formed : Formed D context)
    (domainTyped : Holds D (.type context domain))
    (bodyTyped : Holds D (.type (.snoc context domain) body)) :
    Holds D (.type (.snoc (.snoc context domain) (domain.rename Fin.succ))
      (body.rename (liftRenaming Fin.succ))) := by
  have admitted := lifted (.snoc formed domainTyped) (weaken domainTyped) domainTyped
  have mapping : liftSubstitution (fun index : Fin n => (TermExpr.var index.succ : TermExpr S (n + 1))) =
      TermExpr.var ∘ liftRenaming Fin.succ := by
    funext index
    cases index using Fin.cases <;> rfl
  simpa only [mapping, Function.comp_def, TypeExpr.substitute_variables] using typeSubstitute admitted bodyTyped

theorem piEtaAdmission {n : Nat} {context : ContextExpr S n} {domain : TypeExpr S n}
    {body : TypeExpr S (n + 1)} {function : TermExpr S n}
    (formed : Formed D context) (domainTyped : Holds D (.type context domain))
    (bodyTyped : Holds D (.type (.snoc context domain) body))
    (functionTyped : Holds D (.term context function (.pi domain body))) :
    Holds D (.term context (.lam domain body (.app (domain.rename Fin.succ)
      (body.rename (liftRenaming Fin.succ)) (function.rename Fin.succ) (.var 0))) (.pi domain body)) := by
  have first := typeWeaken domainTyped domainTyped
  have second := bodyWeaken formed domainTyped bodyTyped
  have functionAdmitted := termWeaken domainTyped functionTyped
  have argument := conclude (.variable (.snoc context domain) 0)
    ⟨(Formed.snoc formed domainTyped).judgment, trivial⟩
  have argumentTyped : Holds D (.term (.snoc context domain) (.var 0) (domain.rename Fin.succ)) := by
    simpa only [RuleCode.conclusion, ContextExpr.lookup_zero] using argument
  have result := conclude (.application (.snoc context domain) (domain.rename Fin.succ)
    (body.rename (liftRenaming Fin.succ)) (function.rename Fin.succ) (.var 0))
    ⟨first, second, functionAdmitted, argumentTyped, trivial⟩
  have resultTyped : Holds D (.term (.snoc context domain)
      (.app (domain.rename Fin.succ) (body.rename (liftRenaming Fin.succ))
        (function.rename Fin.succ) (.var 0)) body) := by
    simpa only [RuleCode.conclusion, TypeExpr.etaBody_instantiate] using result
  exact conclude (.lambda context domain body _)
    ⟨domainTyped, bodyTyped, resultTyped, trivial⟩

theorem pack {n : Nat} {context : ContextExpr S n} {domain : TypeExpr S n}
    {body : TypeExpr S (n + 1)} (formed : Formed D context)
    (domainTyped : Holds D (.type context domain))
    (bodyTyped : Holds D (.type (.snoc context domain) body)) :
    Holds D (.substitution (.snoc (.snoc context domain) body)
      (.snoc context (.sigma domain body)) (packSubstitution domain body)) := by
  let componentContext := ContextExpr.snoc (.snoc context domain) body
  have componentFormed : Formed D componentContext := .snoc (.snoc formed domainTyped) bodyTyped
  have base := substitutionCompose (weaken bodyTyped) (weaken domainTyped)
  have baseMapping : composeSubstitution (fun index : Fin n => (TermExpr.var index.succ : TermExpr S (n + 1)))
      (fun index : Fin (n + 1) => (TermExpr.var index.succ : TermExpr S (n + 2))) =
      TermExpr.var ∘ (Fin.succ ∘ Fin.succ) := rfl
  have baseTyped : Holds D (.substitution componentContext context
      (TermExpr.var ∘ (Fin.succ ∘ Fin.succ))) := by simpa only [baseMapping] using base
  have firstType : Holds D (.type componentContext (domain.rename (Fin.succ ∘ Fin.succ))) := by
    simpa only [Function.comp_def, TypeExpr.substitute_variables] using typeSubstitute baseTyped domainTyped
  have liftedBase := lifted componentFormed baseTyped domainTyped
  have liftedMapping : liftSubstitution (TermExpr.var ∘ (Fin.succ ∘ Fin.succ) : Substitution S n (n + 2)) =
      TermExpr.var ∘ liftRenaming (Fin.succ ∘ Fin.succ) := by
    funext index
    cases index using Fin.cases <;> rfl
  have secondType : Holds D (.type (.snoc componentContext (domain.rename (Fin.succ ∘ Fin.succ)))
      (body.rename (liftRenaming (Fin.succ ∘ Fin.succ)))) := by
    have typed := typeSubstitute liftedBase bodyTyped
    rw [liftedMapping] at typed
    simpa only [Function.comp_def, TypeExpr.substitute_variables] using typed
  have originalFirst := conclude (.variable (.snoc context domain) 0)
    ⟨(Formed.snoc formed domainTyped).judgment, trivial⟩
  have originalFirstTyped : Holds D (.term (.snoc context domain) (.var 0) (domain.rename Fin.succ)) := by
    simpa only [RuleCode.conclusion, ContextExpr.lookup_zero] using originalFirst
  have first := termWeaken bodyTyped originalFirstTyped
  have firstTyped : Holds D (.term componentContext (.var 1) (domain.rename (Fin.succ ∘ Fin.succ))) := by
    simpa only [componentContext, TermExpr.rename, TypeExpr.rename_comp,
      show (0 : Fin (n + 1)).succ = (1 : Fin (n + 2)) from Fin.ext rfl] using first
  have second := conclude (.variable componentContext 0) ⟨componentFormed.judgment, trivial⟩
  have secondTyped : Holds D (.term componentContext (.var 0)
      ((body.rename (liftRenaming (Fin.succ ∘ Fin.succ))).substitute (instantiate (.var 1)))) := by
    simpa only [RuleCode.conclusion, componentContext, ContextExpr.lookup_zero,
      genericPair_body] using second
  have pairTyped := conclude (.pairIntroduction componentContext (domain.rename (Fin.succ ∘ Fin.succ))
    (body.rename (liftRenaming (Fin.succ ∘ Fin.succ))) (.var 1) (.var 0))
    ⟨firstType, secondType, firstTyped, secondTyped, trivial⟩
  have value : Holds D (.term componentContext (genericPair domain body)
      ((.sigma domain body : TypeExpr S n).substitute (TermExpr.var ∘ (Fin.succ ∘ Fin.succ)))) := by
    simpa only [RuleCode.conclusion, genericPair, Function.comp_def, TypeExpr.substitute_variables,
      TypeExpr.rename] using pairTyped
  have sigmaTyped := conclude (.sigmaFormation context domain body) ⟨domainTyped, bodyTyped, trivial⟩
  exact conclude (.substitutionExtend componentContext context (.sigma domain body)
    (TermExpr.var ∘ (Fin.succ ∘ Fin.succ)) (genericPair domain body))
    ⟨baseTyped, sigmaTyped, value, trivial⟩

end JudgmentRegularity
end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
