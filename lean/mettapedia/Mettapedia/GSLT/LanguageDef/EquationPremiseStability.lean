import Mettapedia.GSLT.LanguageDef.EquationSemantics
import Mettapedia.OSLF.MeTTaIL.MatchSpec

/-!
# Equation meaning depends on its premise environment

Authored equations and executable rewrites remain distinct. Nevertheless, an
equation's congruence premises consult the authored rewrite relation. Keeping
only its source text unchanged therefore need not preserve its meaning.

This leaf transports actual equation instances when their premise judgments
agree, and transports the generated contextual equivalence when the declared
grammar also agrees. A sufficient noncontextual case uses the existing
`NoncontextualPremises` judgment and unchanged base-premise readouts. In
particular, premise-free equations tolerate arbitrary program-rewrite changes
without changing their equational meaning, provided the grammar is retained.

The controls use validated four-constructor LanguageDefs. Adding the ordinary
rewrite C -> D enables the unchanged conditional equation A = B. A separate
premise-free A = B remains nontrivial and stable under that same rewrite
addition. These are statements about the actual LanguageDef semantics, not
claims about a C implementation, a selected mathematical theory, or automatic
promotion of an experimental rewrite into native judgmental conversion.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.EquationPremiseStability

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.GSLT.LanguageDef.EquationSemantics

variable {source target : LanguageDef} {sourceBase targetBase : BasePremiseEvaluator}

/-- Agreement is local to the retained equations and their actual binding
environments. This is a premise-level obligation, not the desired equation
equivalence assumed as a field. -/
def PremisesAgree (sourceBase targetBase : BasePremiseEvaluator)
    (source target : LanguageDef) : Prop :=
  ∀ equation ∈ source.equations, ∀ fuel initial final,
    PremisesAt sourceBase source fuel initial equation.premises final ↔
      PremisesAt targetBase target fuel initial equation.premises final

theorem PremisesAgree.symm
    (equations : source.equations = target.equations)
    (agreement : PremisesAgree sourceBase targetBase source target) :
    PremisesAgree targetBase sourceBase target source := by
  intro equation member fuel initial final
  exact (agreement equation (equations ▸ member) fuel initial final).symm

/-- Matching, equation identity, output substitution and depth are retained;
only the premise derivation is transported. -/
theorem equationInstanceAt_forward
    (equations : source.equations = target.equations)
    (agreement : PremisesAgree sourceBase targetBase source target)
    {fuel : Nat} {left right : Pattern}
    (evidence : EquationInstanceAt sourceBase source fuel left right) :
    EquationInstanceAt targetBase target fuel left right := by
  cases evidence with
  | forward member matched premises result =>
      exact .forward (equations ▸ member) matched
        ((agreement _ member _ _ _).mp premises) result
  | reverse member matched premises result =>
      exact .reverse (equations ▸ member) matched
        ((agreement _ member _ _ _).mp premises) result

theorem equationInstanceAt_iff
    (equations : source.equations = target.equations)
    (agreement : PremisesAgree sourceBase targetBase source target)
    (fuel : Nat) (left right : Pattern) :
    EquationInstanceAt sourceBase source fuel left right ↔
      EquationInstanceAt targetBase target fuel left right :=
  ⟨equationInstanceAt_forward equations agreement,
    equationInstanceAt_forward equations.symm (agreement.symm equations)⟩

theorem equationInstance_iff
    (equations : source.equations = target.equations)
    (agreement : PremisesAgree sourceBase targetBase source target)
    (left right : Pattern) :
    EquationInstance sourceBase source left right ↔
      EquationInstance targetBase target left right := by
  exact exists_congr fun fuel => equationInstanceAt_iff equations agreement fuel left right

/-! ## A sufficient premise-level condition -/

/-- Noncontextual premise lists require no agreement of the program rewrite
relation. The actual base readout is still required to agree, including for
`forAll`; calling a premise noncontextual does not erase that dependency. -/
theorem premisesAt_iff_of_noncontextual
    {premises : List Premise} (noncontextual : NoncontextualPremises premises)
    (baseAgreement : ∀ premise ∈ premises, ∀ bindings,
      sourceBase source bindings premise = targetBase target bindings premise)
    (fuel : Nat) (initial final : Bindings) :
    PremisesAt sourceBase source fuel initial premises final ↔
      PremisesAt targetBase target fuel initial premises final := by
  induction noncontextual generalizing initial final with
  | nil =>
      constructor <;> intro evidence <;> cases evidence <;> exact .nil _
  | freshness rest ih =>
      have first := baseAgreement _ (List.mem_cons_self ..)
      have tail := ih (fun premise member => baseAgreement premise (by simp [member]))
      constructor
      · intro evidence
        cases evidence with
        | cons head rest =>
            cases head with
            | freshness member =>
                exact .cons (.freshness (by simpa only [← first] using member))
                  ((tail _ _).mp rest)
      · intro evidence
        cases evidence with
        | cons head rest =>
            cases head with
            | freshness member =>
                exact .cons (.freshness (by simpa only [first] using member))
                  ((tail _ _).mpr rest)
  | relationQuery rest ih =>
      have first := baseAgreement _ (List.mem_cons_self ..)
      have tail := ih (fun premise member => baseAgreement premise (by simp [member]))
      constructor
      · intro evidence
        cases evidence with
        | cons head rest =>
            cases head with
            | relationQuery member =>
                exact .cons (.relationQuery (by simpa only [← first] using member))
                  ((tail _ _).mp rest)
      · intro evidence
        cases evidence with
        | cons head rest =>
            cases head with
            | relationQuery member =>
                exact .cons (.relationQuery (by simpa only [first] using member))
                  ((tail _ _).mpr rest)
  | forAll rest ih =>
      have first := baseAgreement _ (List.mem_cons_self ..)
      have tail := ih (fun premise member => baseAgreement premise (by simp [member]))
      constructor
      · intro evidence
        cases evidence with
        | cons head rest =>
            cases head with
            | forAll member =>
                exact .cons (.forAll (by simpa only [← first] using member))
                  ((tail _ _).mp rest)
      · intro evidence
        cases evidence with
        | cons head rest =>
            cases head with
            | forAll member =>
                exact .cons (.forAll (by simpa only [first] using member))
                  ((tail _ _).mpr rest)

theorem premisesAgree_of_noncontextual
    (noncontextual : ∀ equation ∈ source.equations,
      NoncontextualPremises equation.premises)
    (baseAgreement : ∀ equation ∈ source.equations,
      ∀ premise ∈ equation.premises, ∀ bindings,
        sourceBase source bindings premise = targetBase target bindings premise) :
    PremisesAgree sourceBase targetBase source target := by
  intro equation member fuel initial final
  exact premisesAt_iff_of_noncontextual (noncontextual equation member)
    (baseAgreement equation member) fuel initial final

/-- Premise-free equations do not consult either the base environment or the
rewrite relation. This derives their stability rather than assuming it. -/
theorem premisesAgree_of_premise_free
    (free : ∀ equation ∈ source.equations, equation.premises = []) :
    PremisesAgree sourceBase targetBase source target := by
  apply premisesAgree_of_noncontextual
  · intro equation member
    rw [free equation member]
    exact .nil
  · intro equation member premise premiseMember
    rw [free equation member] at premiseMember
    exact (List.not_mem_nil premiseMember).elim

/-! ## Retaining the presentation-derived equations as well -/

private def sameGrammarMorphism (source target : ValidatedLanguageDef)
    (types : source.language.types = target.language.types)
    (terms : source.language.terms = target.language.terms) :
    SignatureMorphism source target where
  symbols := LanguageDefSymbolMap.id
  mapsTypes declaration member := by
    simpa only [mapTypeDecl_id, ← types] using member
  mapsTerms rule member := by
    simpa only [mapGrammarRule_id, ← terms] using member

theorem sortedAt_forward_of_same_grammar (source target : ValidatedLanguageDef)
    (types : source.language.types = target.language.types)
    (terms : source.language.terms = target.language.terms)
    {pattern : Pattern} {sort : String}
    (sorted : SortedAt source.language pattern sort) :
    SortedAt target.language pattern sort := by
  obtain ⟨free, bound, typed⟩ := sorted
  refine ⟨free, bound, ?_⟩
  simpa only [sameGrammarMorphism, mapPattern_id, mapTypeExpr_id,
    show mapTypeExpr LanguageDefSymbolMap.id = id from funext mapTypeExpr_id,
    WellSorted.FreeTypeContext.map_id, List.map_id] using
    typed.mapSignature (sameGrammarMorphism source target types terms)

theorem derivedInstance_forward_of_same_grammar (source target : ValidatedLanguageDef)
    (types : source.language.types = target.language.types)
    (terms : source.language.terms = target.language.terms)
    {left right : Pattern} (evidence : DerivedInstance source.language left right) :
    DerivedInstance target.language left right := by
  have carrier : ∀ {rule kind}, CollectionCarrierRule source.language rule kind →
      CollectionCarrierRule target.language rule kind := by
    intro rule kind declaration
    exact ⟨terms ▸ declaration.authored, declaration.selfSorted⟩
  have algebra : ∀ {rule kind laws}, AlgebraRule source.language rule kind laws →
      AlgebraRule target.language rule kind laws := by
    intro rule kind laws declaration
    exact ⟨terms ▸ declaration.authored, declaration.declared,
      declaration.selfSorted, fun unit member => terms ▸ declaration.unitAuthored unit member⟩
  have sorted : ∀ {pattern sort}, SortedAt source.language pattern sort →
      SortedAt target.language pattern sort :=
    sortedAt_forward_of_same_grammar source target types terms
  cases evidence with
  | bagPerm declaration typed permutation => exact .bagPerm (carrier declaration) (sorted typed) permutation
  | setPerm declaration typed permutation => exact .setPerm (carrier declaration) (sorted typed) permutation
  | setDedup declaration typed => exact .setDedup (carrier declaration) (sorted typed)
  | flatten declaration flat typed => exact .flatten (algebra declaration) flat (sorted typed)
  | singleton declaration flat typed => exact .singleton (algebra declaration) flat (sorted typed)
  | unitElim declaration unit typed => exact .unitElim (algebra declaration) unit (sorted typed)
  | emptyUnit declaration unit typed => exact .emptyUnit (algebra declaration) unit (sorted typed)

/-- Local equation-premise agreement and retained grammar suffice for the
whole contextual equivalence, including its presentation-derived laws. No
equality of program rewrite tables is required. -/
theorem equationEquiv_forward (source target : ValidatedLanguageDef)
    (types : source.language.types = target.language.types)
    (terms : source.language.terms = target.language.terms)
    (equations : source.language.equations = target.language.equations)
    (agreement : PremisesAgree sourceBase targetBase source.language target.language)
    {left right : Pattern} (equivalent : EquationEquiv sourceBase source.language left right) :
    EquationEquiv targetBase target.language left right := by
  induction equivalent with
  | rel left right step =>
      apply Relation.EqvGen.rel
      cases step with
      | inContext context generator =>
          apply EquationContextStep.inContext
          rcases generator with authored | derived
          · exact Or.inl ((equationInstance_iff equations agreement _ _).mp authored)
          · exact Or.inr (derivedInstance_forward_of_same_grammar source target types terms derived)
  | refl pattern => exact .refl pattern
  | symm left right _ ih => exact .symm _ _ ih
  | trans left middle right _ _ first second => exact .trans _ _ _ first second

theorem equationEquiv_iff (source target : ValidatedLanguageDef)
    (types : source.language.types = target.language.types)
    (terms : source.language.terms = target.language.terms)
    (equations : source.language.equations = target.language.equations)
    (agreement : PremisesAgree sourceBase targetBase source.language target.language)
    (left right : Pattern) :
    EquationEquiv sourceBase source.language left right ↔
      EquationEquiv targetBase target.language left right :=
  ⟨equationEquiv_forward source target types terms equations agreement,
    equationEquiv_forward target source types.symm terms.symm equations.symm
      (agreement.symm equations)⟩

theorem premise_free_equationEquiv_iff (source target : ValidatedLanguageDef)
    (types : source.language.types = target.language.types)
    (terms : source.language.terms = target.language.terms)
    (equations : source.language.equations = target.language.equations)
    (free : ∀ equation ∈ source.language.equations, equation.premises = [])
    (sourceBase targetBase : BasePremiseEvaluator) (left right : Pattern) :
    EquationEquiv sourceBase source.language left right ↔
      EquationEquiv targetBase target.language left right :=
  equationEquiv_iff source target types terms equations
    (premisesAgree_of_premise_free free) left right

/-! ## An actual equation becomes enabled by an ordinary rewrite -/

namespace Controls

def a : Pattern := .apply "A" []
def b : Pattern := .apply "B" []
def c : Pattern := .apply "C" []
def d : Pattern := .apply "D" []

def constant (label : String) : GrammarRule :=
  { label, category := "Term", params := [], syntaxPattern := [] }

def conditionalEquation : Equation :=
  { name := "conditional-AB", typeContext := [],
    premises := [.congruence c d], left := a, right := b }

def ordinaryRewrite : RewriteRule :=
  { name := "ordinary-CD", typeContext := [], premises := [], left := c, right := d }

def before : LanguageDef :=
  { name := "EquationPremiseBefore", types := [.plain "Term"],
    terms := [constant "A", constant "B", constant "C", constant "D"],
    equations := [conditionalEquation], rewrites := [] }

def after : LanguageDef := { before with rewrites := [ordinaryRewrite] }

local macro "validate_premise_example" : tactic =>
  `(tactic| (
    apply LanguageDef.validate_eq_nil_of_constructorEquationsAndRewrites
    all_goals
      simp [before, after, constant, conditionalEquation, ordinaryRewrite, a, b, c, d,
        LanguageDef.typeNames, TypeDecl.plain, LanguageDef.validateEquation,
        LanguageDef.validateRewrite, LanguageDef.validatePatternConstructors,
        LanguageDef.validateRulePatterns, LanguageDef.patternFvarNames,
        LanguageDef.patternBinderNames, LanguageDef.premisePatterns,
        LanguageDef.premiseFvarNames, LanguageDef.premiseProducedFvarNames,
        LanguageDef.premiseForAllParams, Pattern.constructorRefs,
        Pattern.constructorRefsList, Pattern.freeFvarNames, Pattern.isWellScoped,
        Pattern.isWellScopedAt, Pattern.isWellScopedListAt, TermParam.typeExpr]))

theorem before_valid : before.validate = [] := by validate_premise_example
theorem after_valid : after.validate = [] := by validate_premise_example

def base : BasePremiseEvaluator := engineBasePremises RelationEnv.empty

theorem same_equation_syntax : before.equations = after.equations := rfl

theorem ordinary_rewrite_executes : rewriteAt base after 1 c = [d] := by decide +kernel

theorem ordinary_rewrite_step : StepAt base after 1 c d :=
  mem_rewriteAt_iff_stepAt.mp (by rw [ordinary_rewrite_executes]; simp)

private theorem nullary_matches (label : String) :
    ([] : Bindings) ∈ matchPattern (.apply label []) (.apply label []) := by
  rw [Mettapedia.OSLF.MeTTaIL.MatchSpec.matchPattern_iff_matchRel]
  exact .apply .nil rfl

theorem after_premises : PremisesAt base after 1 [] conditionalEquation.premises [] := by
  exact .cons (.congruence (by simpa [c, d, applyBindings] using ordinary_rewrite_step)
    (nullary_matches "D") rfl) (.nil [])

theorem after_equation_instance : EquationInstanceAt base after 1 a b := by
  exact .forward (equation := conditionalEquation) (initialBindings := [])
    (finalBindings := []) (.head []) (nullary_matches "A")
    after_premises (by simp [conditionalEquation, b, applyBindings])

theorem after_equivalent : EquationEquiv base after a b :=
  equationInstance_equivalent ⟨1, after_equation_instance⟩

theorem before_no_step (fuel : Nat) (left right : Pattern) :
    ¬ StepAt base before fuel left right := by
  intro step
  cases step with
  | rule member _ _ _ => exact List.not_mem_nil member

theorem before_no_premises (fuel : Nat) (initial final : Bindings) :
    ¬ PremisesAt base before fuel initial conditionalEquation.premises final := by
  intro evidence
  cases evidence with
  | cons premise _ =>
      cases premise with
      | congruence step _ _ => exact before_no_step _ _ _ step

theorem before_no_equation_instance (left right : Pattern) :
    ¬ EquationInstance base before left right := by
  rintro ⟨fuel, evidence⟩
  cases evidence with
  | forward member _ premises _ =>
      have same : _ = conditionalEquation := List.mem_singleton.mp member
      subst same
      exact before_no_premises _ _ _ premises
  | reverse member _ premises _ =>
      have same : _ = conditionalEquation := List.mem_singleton.mp member
      subst same
      exact before_no_premises _ _ _ premises

private theorem before_no_derived (left right : Pattern) :
    ¬ DerivedInstance before left right :=
  no_derivedInstance_of_no_derived_laws (by decide) (by decide) (by decide) left right

theorem before_equiv_iff_eq (left right : Pattern) :
    EquationEquiv base before left right ↔ left = right := by
  constructor
  · intro equivalent
    induction equivalent with
    | rel left right step =>
        cases step with
        | inContext context generator =>
            rcases generator with authored | derived
            · exact (before_no_equation_instance _ _ authored).elim
            · exact (before_no_derived _ _ derived).elim
    | refl pattern => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ first second => exact first.trans second
  · rintro rfl
    exact .refl _

theorem before_not_equivalent : ¬ EquationEquiv base before a b := by
  rw [before_equiv_iff_eq]
  decide

/-- Identical equation text is insufficient. The newly enabled premise is
the actual execution of an ordinary authored rewrite. -/
theorem unchanged_equations_new_meaning :
    before.equations = after.equations ∧
    rewriteAt base after 1 c = [d] ∧
    ¬ EquationEquiv base before a b ∧ EquationEquiv base after a b :=
  ⟨same_equation_syntax, ordinary_rewrite_executes, before_not_equivalent, after_equivalent⟩

theorem premise_environment_changed : ¬ PremisesAgree base base before after := by
  intro agreement
  exact before_no_premises 1 [] []
    ((agreement conditionalEquation (by simp [before]) 1 [] []).mpr after_premises)

/-! ## A nontrivial premise-free equation is stable under the same extension -/

def unconditionalEquation : Equation := { conditionalEquation with premises := [] }
def unconditionalBefore : LanguageDef := { before with equations := [unconditionalEquation] }
def unconditionalAfter : LanguageDef := { unconditionalBefore with rewrites := [ordinaryRewrite] }

theorem unconditional_before_valid : unconditionalBefore.validate = [] := by
  dsimp only [unconditionalBefore, unconditionalEquation]
  validate_premise_example

theorem unconditional_after_valid : unconditionalAfter.validate = [] := by
  dsimp only [unconditionalAfter, unconditionalBefore, unconditionalEquation]
  validate_premise_example

theorem unconditional_equations_stable (left right : Pattern) :
    EquationEquiv base unconditionalBefore left right ↔
      EquationEquiv base unconditionalAfter left right := by
  apply premise_free_equationEquiv_iff
    ⟨unconditionalBefore, unconditional_before_valid⟩
    ⟨unconditionalAfter, unconditional_after_valid⟩ rfl rfl rfl
  intro equation member
  have same : equation = unconditionalEquation := List.mem_singleton.mp member
  subst equation
  rfl

theorem unconditional_nontrivial : a ≠ b ∧ EquationEquiv base unconditionalBefore a b := by
  refine ⟨by decide, ?_⟩
  apply equationInstance_equivalent
  exact ⟨0, .forward (equation := unconditionalEquation) (initialBindings := [])
    (finalBindings := []) (.head []) (nullary_matches "A") (.nil [])
    (by simp [unconditionalEquation, conditionalEquation, b, applyBindings])⟩

theorem unconditional_rewrite_executes : rewriteAt base unconditionalAfter 1 c = [d] := by decide +kernel

end Controls

#print axioms equationInstance_iff
#print axioms premisesAgree_of_noncontextual
#print axioms equationEquiv_iff
#print axioms premise_free_equationEquiv_iff
#print axioms Controls.unchanged_equations_new_meaning
#print axioms Controls.premise_environment_changed
#print axioms Controls.unconditional_equations_stable
#print axioms Controls.unconditional_nontrivial

end Mettapedia.GSLT.LanguageDef.EquationPremiseStability
