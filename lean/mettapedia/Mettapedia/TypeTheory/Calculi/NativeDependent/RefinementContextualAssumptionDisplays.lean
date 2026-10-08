import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualHeyting
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualComprehensionSyntax

/-!
# Assumptions across generated data displays

A predicate assumed before a data binder compares with its actual weakening
assumed after the binder. Both directions are assembled from typed generated
substitutions and their complete guards. The data tuple is retained, while
the two raw context presentations remain separate objects.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.AssumptionDisplays

open _root_.CategoryTheory
open QuotientComprehensionSyntax

universe u
variable {S : Symbols.{u}} {D : Signature S}

def assumedType {context : Context D} (predicate : PredicateOver context) (domain : TypeOver context) :
    TypeOver (assumed context predicate) := ⟨domain.code, by
      have transported := (domain.reindex (assumptionInclusion context predicate)).formed
      change Holds D (.type (assumed context predicate).raw
        (domain.code.substitute TermExpr.var)) at transported
      simpa only [TypeExpr.substitute_identity] using transported⟩

abbrev before (context : Context D) (domain : TypeOver context) (predicate : PredicateOver context) :=
  extend (assumed context predicate) (assumedType predicate domain)

abbrev after (context : Context D) (domain : TypeOver context) (predicate : PredicateOver context) :=
  assumed (extend context domain) (predicate.reindex (projectionHom context domain))

def dataMap {context : Context D} (domain : TypeOver context) (predicate : PredicateOver context) :
    before context domain predicate ⟶ extend context domain := ⟨TermExpr.var, by
      change Holds D (.substitution (.snoc (assumed context predicate).raw domain.code)
        (.snoc context.raw domain.code) TermExpr.var)
      have transported := conclude (.substitutionLift (assumed context predicate).raw context.raw
        domain.code TermExpr.var)
        ⟨(assumptionInclusion context predicate).admitted, domain.formed, trivial⟩
      change Holds D (.substitution
        (.snoc (assumed context predicate).raw (domain.code.substitute TermExpr.var))
        (.snoc context.raw domain.code) (liftSubstitution TermExpr.var)) at transported
      simpa only [TypeExpr.substitute_identity, liftSubstitution_identity] using transported⟩

theorem before_guard {context : Context D} (domain : TypeOver context) (predicate : PredicateOver context) :
    Holds D (.entails (before context domain predicate).raw
      ((predicate.reindex (projectionHom context domain)).code.substitute
        (dataMap domain predicate).substitution)) := by
  have transported := conclude (.substituteEntailment (before context domain predicate).raw
    (assumed context predicate).raw (fun index => .var index.succ) predicate.code)
    ⟨(projectionHom (assumed context predicate) (assumedType predicate domain)).admitted,
      Logic.hypothesis predicate, trivial⟩
  change Holds D (.entails (before context domain predicate).raw
    ((predicate.code.substitute (fun index => .var index.succ)).substitute TermExpr.var))
  simpa only [PropExpr.substitute_identity] using transported

def forward {context : Context D} (domain : TypeOver context) (predicate : PredicateOver context) :
    before context domain predicate ⟶ after context domain predicate :=
  select (predicate.reindex (projectionHom context domain)) (dataMap domain predicate)
    (before_guard domain predicate)

@[simp] theorem forward_tuple {context : Context D} (domain : TypeOver context)
    (predicate : PredicateOver context) : (forward domain predicate).substitution = TermExpr.var := rfl

def afterBase {context : Context D} (domain : TypeOver context) (predicate : PredicateOver context) :
    after context domain predicate ⟶ context :=
  assumptionInclusion (extend context domain) (predicate.reindex (projectionHom context domain)) ≫
    projectionHom context domain

@[simp] theorem afterBase_tuple {context : Context D} (domain : TypeOver context)
    (predicate : PredicateOver context) :
    (afterBase domain predicate).substitution = fun index => .var index.succ := by
  change composeSubstitution (fun index => .var index.succ) TermExpr.var = _
  exact composeSubstitution_identity _

theorem after_guard {context : Context D} (domain : TypeOver context) (predicate : PredicateOver context) :
    Holds D (.entails (after context domain predicate).raw
      (predicate.code.substitute (afterBase domain predicate).substitution)) := by
  rw [afterBase_tuple]
  exact Logic.hypothesis (predicate.reindex (projectionHom context domain))

def backward {context : Context D} (domain : TypeOver context) (predicate : PredicateOver context) :
    after context domain predicate ⟶ before context domain predicate := ⟨TermExpr.var, by
      have selected := (select predicate (afterBase domain predicate) (after_guard domain predicate)).admitted
      change Holds D (.substitution (after context domain predicate).raw
        (assumed context predicate).raw (afterBase domain predicate).substitution) at selected
      rw [afterBase_tuple] at selected
      have newestEntry := conclude (.variable (after context domain predicate).raw 0)
        ⟨(after context domain predicate).formed.judgment, trivial⟩
      have newestTyped : Holds D (.term (after context domain predicate).raw (.var 0)
          (domain.code.substitute (fun index => .var index.succ))) := by
        change Holds D (.term (after context domain predicate).raw (.var 0)
          (domain.code.rename Fin.succ)) at newestEntry
        simpa only [TypeExpr.substitute_variables] using newestEntry
      have paired := conclude (.substitutionExtend (after context domain predicate).raw
        (assumed context predicate).raw domain.code (fun index => .var index.succ) (.var 0))
        ⟨selected, (assumedType predicate domain).formed, newestTyped, trivial⟩
      have identityTuple : extendSubstitution
          (fun index : Fin context.arity => (TermExpr.var index.succ : TermExpr S (context.arity + 1)))
          (.var 0) = (TermExpr.var : Substitution S (context.arity + 1) (context.arity + 1)) := by
        funext index
        cases index using Fin.cases <;> rfl
      change Holds D (.substitution (after context domain predicate).raw
        (before context domain predicate).raw
        (extendSubstitution (fun index => .var index.succ) (.var 0))) at paired
      simpa only [identityTuple] using paired⟩

@[simp] theorem backward_tuple {context : Context D} (domain : TypeOver context)
    (predicate : PredicateOver context) : (backward domain predicate).substitution = TermExpr.var := rfl

def comparison {context : Context D} (domain : TypeOver context) (predicate : PredicateOver context) :
    before context domain predicate ≅ after context domain predicate where
  hom := forward domain predicate
  inv := backward domain predicate
  hom_inv_id := Hom.ext (composeSubstitution_identity _)
  inv_hom_id := Hom.ext (composeSubstitution_identity _)

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.AssumptionDisplays
