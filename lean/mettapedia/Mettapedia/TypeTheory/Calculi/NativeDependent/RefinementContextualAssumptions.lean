import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualQuotient

/-!
# Assumption comprehension in the generated mixed context category

An arrow into an assumed context is exactly a typed data substitution together
with an actual derivation of the substituted assumption. Its inclusion forgets
the guard without adding a data variable. Both the raw and equation-quotient
inclusions are monic, and the factorization commutes with precomposition.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual

open _root_.CategoryTheory

universe u
variable {S : Symbols.{u}} {D : Signature S}

structure PredicateOver (context : Context D) where
  code : PropExpr S context.arity
  formed : Holds D (.predicate context.raw code)

@[ext] theorem PredicateOver.ext {context : Context D} {first second : PredicateOver context}
    (same : first.code = second.code) : first = second := by
  cases first
  cases second
  cases same
  rfl

def PredicateOver.reindex {source target : Context D} (predicate : PredicateOver target)
    (morphism : source ⟶ target) : PredicateOver source :=
  ⟨predicate.code.substitute morphism.substitution,
    conclude (.substitutePredicate source.raw target.raw morphism.substitution predicate.code)
      ⟨morphism.admitted, predicate.formed, trivial⟩⟩

theorem PredicateOver.reindex_id {context : Context D} (predicate : PredicateOver context) :
    predicate.reindex (𝟙 context) = predicate :=
  PredicateOver.ext (PropExpr.substitute_identity predicate.code)

theorem PredicateOver.reindex_comp {source middle target : Context D}
    (predicate : PredicateOver target) (earlier : source ⟶ middle) (later : middle ⟶ target) :
    predicate.reindex (earlier ≫ later) = (predicate.reindex later).reindex earlier :=
  PredicateOver.ext (PropExpr.substitute_comp later.substitution earlier.substitution predicate.code).symm

abbrev assumed (context : Context D) (predicate : PredicateOver context) : Context D :=
  ⟨context.arity, .assume context.raw predicate.code, .assume context.formed predicate.formed⟩

def assumptionInclusion (context : Context D) (predicate : PredicateOver context) :
    assumed context predicate ⟶ context :=
  ⟨TermExpr.var, conclude (.substitutionWeakenAssumption context.raw predicate.code)
    ⟨predicate.formed, trivial⟩⟩

@[simp] theorem assumptionInclusion_substitution {source target : Context D}
    (predicate : PredicateOver target) (morphism : source ⟶ assumed target predicate) :
    (morphism ≫ assumptionInclusion target predicate).substitution = morphism.substitution := by
  change composeSubstitution TermExpr.var morphism.substitution = morphism.substitution
  exact identity_composeSubstitution morphism.substitution

def select {source target : Context D} (predicate : PredicateOver target)
    (morphism : source ⟶ target)
    (guard : Holds D (.entails source.raw (predicate.code.substitute morphism.substitution))) :
    source ⟶ assumed target predicate :=
  ⟨morphism.substitution,
    conclude (.substitutionIntoAssumption source.raw target.raw predicate.code morphism.substitution)
      ⟨morphism.admitted, predicate.formed, guard, trivial⟩⟩

theorem select_inclusion {source target : Context D} (predicate : PredicateOver target)
    (morphism : source ⟶ target)
    (guard : Holds D (.entails source.raw (predicate.code.substitute morphism.substitution))) :
    select predicate morphism guard ≫ assumptionInclusion target predicate = morphism :=
  Hom.ext (identity_composeSubstitution morphism.substitution)

theorem selectedGuard {source target : Context D} (predicate : PredicateOver target)
    (morphism : source ⟶ assumed target predicate) :
    Holds D (.entails source.raw (predicate.code.substitute morphism.substitution)) :=
  substitutionAssumptionGuard target.formed predicate.formed morphism.admitted

def SelectedArrow (source target : Context D) (predicate : PredicateOver target) :=
  {morphism : source ⟶ target //
    Holds D (.entails source.raw (predicate.code.substitute morphism.substitution))}

def selectionEquiv (source target : Context D) (predicate : PredicateOver target) :
    (source ⟶ assumed target predicate) ≃ SelectedArrow source target predicate where
  toFun morphism := ⟨morphism ≫ assumptionInclusion target predicate, by
    simpa only [assumptionInclusion_substitution] using
      selectedGuard predicate morphism⟩
  invFun entry := select predicate entry.val entry.property
  left_inv morphism := by
    apply Hom.ext
    exact identity_composeSubstitution morphism.substitution
  right_inv entry := Subtype.ext (select_inclusion predicate entry.val entry.property)

def SelectedArrow.precompose {first source target : Context D} {predicate : PredicateOver target}
    (entry : SelectedArrow source target predicate) (earlier : first ⟶ source) :
    SelectedArrow first target predicate :=
  ⟨earlier ≫ entry.val, by
    have transported := conclude (.substituteEntailment first.raw source.raw earlier.substitution
      (predicate.code.substitute entry.val.substitution)) ⟨earlier.admitted, entry.property, trivial⟩
    change Holds D (.entails first.raw
      ((predicate.code.substitute entry.val.substitution).substitute earlier.substitution)) at transported
    rw [PropExpr.substitute_comp] at transported
    exact transported⟩

theorem selection_natural {first source target : Context D} (predicate : PredicateOver target)
    (morphism : source ⟶ assumed target predicate) (earlier : first ⟶ source) :
    (selectionEquiv first target predicate) (earlier ≫ morphism) =
      ((selectionEquiv source target predicate) morphism).precompose earlier :=
  Subtype.ext (Category.assoc earlier morphism (assumptionInclusion target predicate))

instance assumptionInclusion_mono (context : Context D) (predicate : PredicateOver context) :
    Mono (assumptionInclusion context predicate) where
  right_cancellation first second same := by
    apply Hom.ext
    have tuples := congrArg Hom.substitution same
    simpa only [assumptionInclusion_substitution] using tuples

/-- Both guards remain admitted when data substitutions are identified by
their actual generated equations. -/
theorem select_equation {source target : Context D} (predicate : PredicateOver target)
    {first second : source ⟶ target} (same : homEquality D first second)
    (firstGuard : Holds D (.entails source.raw (predicate.code.substitute first.substitution)))
    (secondGuard : Holds D (.entails source.raw (predicate.code.substitute second.substitution))) :
    homEquality D (select predicate first firstGuard) (select predicate second secondGuard) :=
  conclude (.substitutionIntoAssumptionEquality source.raw target.raw predicate.code
    first.substitution second.substitution) ⟨same, predicate.formed, firstGuard, secondGuard, trivial⟩

/-- The quotient inclusion is monic by complete component equality and
the actual target guards, rather than by injectivity of raw syntax. -/
instance quotientAssumptionInclusion_mono (context : Context D) (predicate : PredicateOver context) :
    Mono ((quotientProjection D).map (assumptionInclusion context predicate)) where
  right_cancellation {source} first second same := by
    induction first using Quot.inductionOn with
    | h first =>
      induction second using Quot.inductionOn with
      | h second =>
        change Hom source.as (assumed context predicate) at first second
        apply (quotientProjection_map_eq_iff first second).mpr
        have bases : homEquality D (first ≫ assumptionInclusion context predicate)
            (second ≫ assumptionInclusion context predicate) :=
          (quotientProjection_map_eq_iff _ _).mp same
        apply componentEquationsSubstitution source.as.formed (assumed context predicate).formed
          first.substitution second.substitution first.components second.components
          (substitutionGuards (assumed context predicate).formed first.admitted)
          (substitutionGuards (assumed context predicate).formed second.admitted)
        have components := substitutionComponentEquations context.formed bases
        simp only [assumptionInclusion_substitution] at components
        exact components

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual
