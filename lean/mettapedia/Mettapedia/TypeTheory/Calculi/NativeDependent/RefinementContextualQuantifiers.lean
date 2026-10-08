import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualAssumptionDisplays

/-!
# Generated quantifiers and their display adjunctions

Universal and existential predicates are formed from actual admitted bodies.
Their adjunctions use guarded assumption substitutions across the supplied
data display. Existential elimination transports entailment only; it does not
extract a selected data inhabitant from erased existence.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.Quantifiers

open _root_.CategoryTheory
open QuotientComprehensionSyntax AssumptionDisplays

universe u
variable {S : Symbols.{u}} {D : Signature S}

def rawForall {context : Context D} (domain : TypeOver context)
    (predicate : PredicateOver (extend context domain)) : PredicateOver context :=
  ⟨.all domain.code predicate.code,
    conclude (.universalFormation context.raw domain.code predicate.code)
      ⟨domain.formed, predicate.formed, trivial⟩⟩

def rawExists {context : Context D} (domain : TypeOver context)
    (predicate : PredicateOver (extend context domain)) : PredicateOver context :=
  ⟨.exists domain.code predicate.code,
    conclude (.existentialFormation context.raw domain.code predicate.code)
      ⟨domain.formed, predicate.formed, trivial⟩⟩

theorem rawForall_reindex {source target : Context D} (morphism : source ⟶ target)
    (domain : TypeOver target) (predicate : PredicateOver (extend target domain)) :
    (rawForall domain predicate).reindex morphism =
      rawForall (domain.reindex morphism) (predicate.reindex (rawLift morphism domain)) := by
  apply PredicateOver.ext
  change PropExpr.all (domain.code.substitute morphism.substitution)
      (predicate.code.substitute (liftSubstitution morphism.substitution)) =
    PropExpr.all (domain.code.substitute morphism.substitution)
      (predicate.code.substitute (rawLift morphism domain).substitution)
  rw [rawLift_substitution]

theorem rawExists_reindex {source target : Context D} (morphism : source ⟶ target)
    (domain : TypeOver target) (predicate : PredicateOver (extend target domain)) :
    (rawExists domain predicate).reindex morphism =
      rawExists (domain.reindex morphism) (predicate.reindex (rawLift morphism domain)) := by
  apply PredicateOver.ext
  change PropExpr.exists (domain.code.substitute morphism.substitution)
      (predicate.code.substitute (liftSubstitution morphism.substitution)) =
    PropExpr.exists (domain.code.substitute morphism.substitution)
      (predicate.code.substitute (rawLift morphism domain).substitution)
  rw [rawLift_substitution]

theorem lift_then_instantiate {n m : Nat} (substitution : Substitution S n m)
    (term : TermExpr S m) :
    composeSubstitution (liftSubstitution substitution) (instantiate term) =
      extendSubstitution substitution term := by
  funext index
  cases index using Fin.cases with
  | zero => rfl
  | succ index => exact TermExpr.instantiate_weaken term (substitution index)

theorem predicate_at_pair {source target : Context D} (morphism : source ⟶ target)
    {domain : TypeOver target} (predicate : PredicateOver (extend target domain))
    (term : Term source (domain.reindex morphism)) :
    ((predicate.reindex (rawLift morphism domain)).code.substitute (instantiate term.code)) =
      (predicate.reindex (Contextual.pair morphism term)).code := by
  change (predicate.code.substitute (rawLift morphism domain).substitution).substitute
      (instantiate term.code) = predicate.code.substitute (extendSubstitution morphism.substitution term.code)
  rw [rawLift_substitution, PropExpr.substitute_comp]
  exact congrArg (fun substitution => predicate.code.substitute substitution)
    (lift_then_instantiate morphism.substitution term.code)

theorem forall_apply {source target : Context D} (morphism : source ⟶ target)
    {domain : TypeOver target} (predicate : PredicateOver (extend target domain))
    (term : Term source (domain.reindex morphism))
    (evidence : Holds D (.entails source.raw ((rawForall domain predicate).reindex morphism).code)) :
    Holds D (.entails source.raw (predicate.reindex (Contextual.pair morphism term)).code) := by
  rw [rawForall_reindex] at evidence
  have applied := conclude (.universalElimination source.raw (domain.reindex morphism).code
    (predicate.reindex (rawLift morphism domain)).code term.code)
    ⟨(domain.reindex morphism).formed, (predicate.reindex (rawLift morphism domain)).formed,
      evidence, term.typed, trivial⟩
  change Holds D (.entails source.raw
    ((predicate.reindex (rawLift morphism domain)).code.substitute (instantiate term.code))) at applied
  rw [predicate_at_pair] at applied
  exact applied

theorem exists_introduce {source target : Context D} (morphism : source ⟶ target)
    {domain : TypeOver target} (predicate : PredicateOver (extend target domain))
    (term : Term source (domain.reindex morphism))
    (guard : Holds D (.entails source.raw (predicate.reindex (Contextual.pair morphism term)).code)) :
    Holds D (.entails source.raw ((rawExists domain predicate).reindex morphism).code) := by
  rw [rawExists_reindex]
  have localGuard : Holds D (.entails source.raw
      ((predicate.reindex (rawLift morphism domain)).code.substitute (instantiate term.code))) := by
    rw [predicate_at_pair]
    exact guard
  exact conclude (.existentialIntroduction source.raw (domain.reindex morphism).code
    (predicate.reindex (rawLift morphism domain)).code term.code)
    ⟨(domain.reindex morphism).formed, (predicate.reindex (rawLift morphism domain)).formed,
      term.typed, localGuard, trivial⟩

theorem body_in_before {context : Context D} (domain : TypeOver context)
    (predicate : PredicateOver (extend context domain)) (assumption : PredicateOver context) :
    Holds D (.predicate (before context domain assumption).raw predicate.code) := by
  have supplied := (predicate.reindex (dataMap domain assumption)).formed
  change Holds D (.predicate (before context domain assumption).raw
    (predicate.code.substitute TermExpr.var)) at supplied
  simpa only [PropExpr.substitute_identity] using supplied

def afterArgument {context : Context D} (domain : TypeOver context) (assumption : PredicateOver context) :
    Term (after context domain assumption) (domain.reindex (afterBase domain assumption)) :=
  ((newest context domain).reindex
    (assumptionInclusion (extend context domain) (assumption.reindex (projectionHom context domain)))).cast
    (domain.reindex_comp
      (assumptionInclusion (extend context domain) (assumption.reindex (projectionHom context domain)))
      (projectionHom context domain)).symm

theorem after_pair {context : Context D} (domain : TypeOver context) (assumption : PredicateOver context) :
    Contextual.pair (afterBase domain assumption) (afterArgument domain assumption) =
      assumptionInclusion (extend context domain) (assumption.reindex (projectionHom context domain)) := by
  apply Hom.ext
  change extendSubstitution (afterBase domain assumption).substitution
    (afterArgument domain assumption).code = TermExpr.var
  rw [afterBase_tuple]
  have newestCode : (afterArgument domain assumption).code = .var 0 := by
    unfold afterArgument afterBase
    rw [Term.cast_code]
    rfl
  rw [newestCode]
  funext index
  cases index using Fin.cases <;> rfl

theorem raw_forall_adjoint {context : Context D} (domain : TypeOver context)
    (first : PredicateOver context) (second : PredicateOver (extend context domain)) :
    Logic.RawOrder (first.reindex (projectionHom context domain)) second ↔
      Logic.RawOrder first (rawForall domain second) := by
  constructor
  · intro consequence
    have transported := conclude (.substituteEntailment (before context domain first).raw
      (after context domain first).raw TermExpr.var second.code)
      ⟨(forward domain first).admitted, consequence, trivial⟩
    have body : Holds D (.entails (before context domain first).raw second.code) := by
      change Holds D (.entails (before context domain first).raw
        (second.code.substitute TermExpr.var)) at transported
      simpa only [PropExpr.substitute_identity] using transported
    exact conclude (.universalIntroduction (assumed context first).raw domain.code second.code)
      ⟨(assumedType first domain).formed, body_in_before domain second first, body, trivial⟩
  · intro consequence
    let base := afterBase domain first
    let guarded := select first base (after_guard domain first)
    have transported := conclude (.substituteEntailment (after context domain first).raw
      (assumed context first).raw base.substitution (rawForall domain second).code)
      ⟨guarded.admitted, consequence, trivial⟩
    have applied := forall_apply base second (afterArgument domain first) transported
    rw [after_pair] at applied
    change Holds D (.entails (after context domain first).raw
      (second.code.substitute TermExpr.var)) at applied
    simpa only [PropExpr.substitute_identity] using applied

theorem raw_exists_adjoint {context : Context D} (domain : TypeOver context)
    (first : PredicateOver (extend context domain)) (second : PredicateOver context) :
    Logic.RawOrder (rawExists domain first) second ↔
      Logic.RawOrder first (second.reindex (projectionHom context domain)) := by
  constructor
  · intro consequence
    let source := assumed (extend context domain) first
    let inclusion := assumptionInclusion (extend context domain) first
    let base : source ⟶ context := inclusion ≫ projectionHom context domain
    let argument := ((newest context domain).reindex inclusion).cast
      (domain.reindex_comp inclusion (projectionHom context domain)).symm
    have paired : Contextual.pair base argument = inclusion := by
      apply Hom.ext
      change extendSubstitution (composeSubstitution (projectionHom context domain).substitution
        inclusion.substitution) argument.code = inclusion.substitution
      change extendSubstitution (composeSubstitution (fun index => .var index.succ) TermExpr.var)
        argument.code = TermExpr.var
      rw [composeSubstitution_identity]
      have argumentCode : argument.code = .var 0 := by rw [Term.cast_code]; rfl
      rw [argumentCode]
      funext index
      cases index using Fin.cases <;> rfl
    have guard : Holds D (.entails source.raw (first.reindex (Contextual.pair base argument)).code) := by
      rw [paired]
      change Holds D (.entails source.raw (first.code.substitute TermExpr.var))
      simpa only [PropExpr.substitute_identity] using Logic.hypothesis first
    exact Logic.apply_order consequence base (exists_introduce base first argument guard)
  · intro consequence
    let assumption := rawExists domain first
    have lifted := conclude (.substitutionAssumptionLift (before context domain assumption).raw
      (extend context domain).raw first.code TermExpr.var)
      ⟨(dataMap domain assumption).admitted, first.formed, trivial⟩
    change Holds D (.substitution
      (.assume (before context domain assumption).raw (first.code.substitute TermExpr.var))
      (assumed (extend context domain) first).raw TermExpr.var) at lifted
    rw [PropExpr.substitute_identity] at lifted
    have transported := conclude (.substituteEntailment
      (.assume (before context domain assumption).raw first.code)
      (assumed (extend context domain) first).raw TermExpr.var
      (second.reindex (projectionHom context domain)).code)
      ⟨lifted, consequence, trivial⟩
    have branch : Holds D (.entails (.assume (before context domain assumption).raw first.code)
        (second.code.rename Fin.succ)) := by
      change Holds D (.entails (.assume (before context domain assumption).raw first.code)
        ((second.code.substitute (fun index => .var index.succ)).substitute TermExpr.var)) at transported
      simpa only [PropExpr.substitute_identity, PropExpr.substitute_variables] using transported
    exact conclude (.existentialElimination (assumed context assumption).raw domain.code first.code second.code)
      ⟨(assumedType assumption domain).formed, body_in_before domain first assumption,
        Logic.predicate_weaken assumption second, Logic.hypothesis assumption, branch, trivial⟩

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.Quantifiers
