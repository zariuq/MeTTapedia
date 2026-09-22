import Mettapedia.OSLF.Framework.GeneratedModalFamily

/-!
# Declaration extension by generated type-former vocabulary

Proposition 19.1 says the induced endofunctor sends a theory to "the underlying
theory of its free extension by generated type formers".  Two readings of that
were separated elsewhere: under the reading where the layers are extra structure
over an unchanged theory, the composite is the identity, proved there by `rfl`,
which alone constructs neither an adjunction nor a monad. Here the generated
declarations enter the underlying language definition.

The declaration-level construction is built here. A theory's sites are enumerated
from its rewrites, and the extension adjoins one declaration per site, with one
slot per rely variable and one for the output. Every slot ranges over the adjoined type sort, so a former
records the arity the modal layer assigns its site, not the sorts of the site's
rely variables.  The authored sorts, grammar, equations and rewrites are retained
unchanged.

Four things follow, and the first is the one that distinguishes the readings.

* `extends_a_theory_with_a_site`: the extension is **not** the identity.  A
  theory with a redex site has strictly more declarations after it than before,
  so the composite this reading gives really is an extension.  Under the other
  reading that statement is false for every theory and every generator.
* `authored_retained` and `rewrites_unchanged`: the authored declaration lists
  are retained, and the rewrite-rule list is unchanged. This does not alone
  establish semantic conservativity of the extended language.
* `redexSites_unchanged`: the extension has the same enumerated sites. A second
  application repeats the declarations and may fail validation. A monad need
  not be idempotent; freshness alone would not establish its multiplication laws.
* `rhoOnce_validate_eq_nil`: extending the reflective calculus once passes the
  validation gate, so the construction yields a language definition; extending it
  twice does not (`rhoTwice_rejected`).

Generated typing rules, structural/propositional layers, generic validation
preservation, a morphism action and a free-extension universal property are not
built here. Declaration growth establishes nonidentity, not an adjunction or
monad.
-/

namespace Mettapedia.OSLF.Framework.TypeFormerExtension

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.GeneratedModalFamily

set_option autoImplicit false

/-- The label of the type former generated at a redex site: the rule it comes
from and the position within that rule's left-hand side. -/
def modalityLabel (site : Site) : String :=
  "Mod_" ++ site.1.name ++ "_" ++ toString site.2

/-- The type former generated at a site: one slot per rely variable and one for
the output, each ranging over the type sort. -/
def modalityDeclaration (typeSort : String) (site : Site) : GrammarRule where
  label := modalityLabel site
  category := typeSort
  params := (List.range (siteSlotCount site)).map fun index =>
    .simple s!"slot{index}" (.base typeSort)
  syntaxPattern := [.terminal (modalityLabel site)]

/-- Retain authored declarations and adjoin one parameterized declaration per
enumerated site. No free-extension universal property is asserted. -/
def typeFormerExtension (lang : LanguageDef) (typeSort : String) : LanguageDef where
  name := lang.name ++ "+Types"
  types := lang.types ++ [TypeDecl.plain typeSort]
  terms := lang.terms ++ (redexSites lang).map (modalityDeclaration typeSort)
  equations := lang.equations
  rewrites := lang.rewrites

/-! ## The original theory sits inside its extension -/

/-- **Nothing authored is lost or renamed.**  The sorts, grammar and rules
survive as prefixes, in order. -/
theorem authored_retained (lang : LanguageDef) (typeSort : String) :
    lang.types <+: (typeFormerExtension lang typeSort).types
      ∧ lang.terms <+: (typeFormerExtension lang typeSort).terms
      ∧ lang.rewrites <+: (typeFormerExtension lang typeSort).rewrites :=
  ⟨List.prefix_append _ _, List.prefix_append _ _, by simp [typeFormerExtension]⟩

/-- The rewrite-rule list is unchanged. This field equality alone does not
establish semantic conservativity of the entire language extension. -/
theorem rewrites_unchanged (lang : LanguageDef) (typeSort : String) :
    (typeFormerExtension lang typeSort).rewrites = lang.rewrites := rfl

/-- The equations are untouched too. -/
theorem equations_unchanged (lang : LanguageDef) (typeSort : String) :
    (typeFormerExtension lang typeSort).equations = lang.equations := rfl

/-- **And so the sites are the same.**  Since sites are read off the rewrites
and the rewrites do not move, the extension has exactly the sites the theory
had -- which is why a second application would re-adjoin the formers the first
one already declared. -/
theorem redexSites_unchanged (lang : LanguageDef) (typeSort : String) :
    redexSites (typeFormerExtension lang typeSort) = redexSites lang := rfl

/-! ## The composite is not the identity

This is what separates the two readings of the proposition.  Under the
extra-structure reading the composite is `rfl`-equal to the identity for every
theory and every generator.  Here it is not the identity for any theory with a
redex site. -/

/-- A theory with an enumerated site gains declarations, so the object-level
extension is not the identity. No functorial action is supplied by this theorem. -/
theorem extends_a_theory_with_a_site (lang : LanguageDef) (typeSort : String)
    (hasSite : redexSites lang ≠ []) :
    typeFormerExtension lang typeSort ≠ lang := by
  intro equal
  have lengths : (typeFormerExtension lang typeSort).terms.length
      = lang.terms.length := by rw [equal]
  have grown : (typeFormerExtension lang typeSort).terms.length
      = lang.terms.length + (redexSites lang).length := by
    simp [typeFormerExtension]
  have positive : 0 < (redexSites lang).length :=
    List.length_pos_iff.mpr hasSite
  omega

/-- The reflective calculus has redex sites, so it is one of the theories the
previous theorem strictly extends. -/
theorem rhoCalc_has_a_site : redexSites rhoCalc ≠ [] := by decide

/-- **So the reflective calculus is strictly extended**, and the composite this
reading gives is not the identity on it. -/
theorem rhoCalc_strictly_extended (typeSort : String) :
    typeFormerExtension rhoCalc typeSort ≠ rhoCalc :=
  extends_a_theory_with_a_site rhoCalc typeSort rhoCalc_has_a_site

/-- A theory with no rewrites has no sites, so it is extended only by the type
sort itself -- the construction does not manufacture formers out of nothing. -/
theorem no_formers_without_sites (lang : LanguageDef) (typeSort : String)
    (noSites : redexSites lang = []) :
    (typeFormerExtension lang typeSort).terms = lang.terms := by
  simp [typeFormerExtension, noSites]


/-! ## A second application is not merely inert -- it is invalid

Because the sites do not move, a second application adjoins **the same formers
again**, under the same labels.  The result is not a theory that gained nothing;
it is a declaration with duplicate constructor labels, which the validation gate
rejects.  So the construction must be applied once, or given a freshness
discipline -- the same qualification the observer extension needs, arising here
for the same reason. -/

/-- The reflective calculus, extended once. -/
def rhoOnce : LanguageDef := typeFormerExtension rhoCalc "Type"

/-- And twice. -/
def rhoTwice : LanguageDef := typeFormerExtension rhoOnce "Type"

/-- **One application keeps every label distinct.**  Ten sites, ten new formers,
no collision with the authored grammar. -/
theorem rhoOnce_labels_distinct :
    (rhoOnce.terms.map GrammarRule.label).eraseDups.length
      = rhoOnce.terms.length := by decide

/-- **A second application duplicates every one of them.**  Twenty-six
declarations, sixteen distinct labels: the ten formers the first application
adjoined are adjoined again. -/
theorem rhoTwice_labels_collide :
    rhoTwice.terms.length = 26
      ∧ (rhoTwice.terms.map GrammarRule.label).eraseDups.length = 16 := by
  refine ⟨by decide, by decide⟩

/-- **So the twice-extended declaration is not label-distinct**, and the
construction is not idempotent in the strong sense a monad would need without a
freshness discipline. -/
theorem rhoTwice_not_label_distinct :
    (rhoTwice.terms.map GrammarRule.label).eraseDups.length
      ≠ rhoTwice.terms.length := by decide

/-! ## Validity -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem rhoOnce_terms_valid :
    ∀ term ∈ rhoOnce.terms, LanguageDef.validateTerm rhoOnce term = [] := by
  intro term member
  simp only [rhoOnce, typeFormerExtension, List.mem_append, List.mem_map] at member
  rcases member with authored | ⟨site, -, rfl⟩
  · simp only [rhoCalc, List.mem_cons, List.mem_nil_iff, or_false] at authored
    rcases authored with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp +decide [LanguageDef.validateTerm, rhoOnce, typeFormerExtension, rhoCalc,
        LanguageDef.typeNames, TypeDecl.plain, TermParam.bodyName, TermParam.binderNames,
        TermParam.typeExpr]
  · simp +decide only [LanguageDef.validateTerm, modalityDeclaration, rhoOnce, typeFormerExtension,
      LanguageDef.typeNames, TypeDecl.plain, TermParam.bodyName, TermParam.binderNames,
      TermParam.typeExpr, List.map_append, List.mem_append, List.append_eq_nil_iff,
      List.flatMap_eq_nil_iff, List.flatMap_map]
    refine ⟨⟨by simp, fun index _ => LanguageDef.validateTypeExpr_eq_nil_of_baseNames _ _ _ ?_⟩,
      LanguageDef.validateSyntaxPattern_terminalsAndBoundNonTerminals _ _ _ (by simp)⟩
    simp [TypeExpr.baseNames]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem rhoOnce_rewrites_valid :
    ∀ rewrite ∈ rhoOnce.rewrites, LanguageDef.validateRewrite rhoOnce rewrite = [] := by
  intro rewrite member
  simp only [rhoOnce, typeFormerExtension, rhoCalc, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl
  all_goals
    simp +decide [LanguageDef.validateRewrite, rhoOnce, typeFormerExtension, rhoCalc,
      rhoCommRewrite, rhoParCongRewrite, LanguageDef.typeNames,
      LanguageDef.validatePatternConstructors, LanguageDef.validateRulePatterns,
      LanguageDef.patternFvarNames, LanguageDef.patternBinderNames,
      LanguageDef.premiseProducedFvarNames, LanguageDef.premisePatterns,
      LanguageDef.premiseFvarNames, LanguageDef.premiseForAllParams, Pattern.constructorRefs,
      Pattern.constructorRefsList, Pattern.freeFvarNames]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem rhoOnce_equations_valid :
    ∀ equation ∈ rhoOnce.equations, LanguageDef.validateEquation rhoOnce equation = [] := by
  intro equation member
  simp only [rhoOnce, typeFormerExtension, rhoCalc, List.mem_cons, List.mem_nil_iff, or_false] at member
  subst member
  simp +decide [LanguageDef.validateEquation, rhoOnce, typeFormerExtension, rhoCalc,
    LanguageDef.typeNames, LanguageDef.validatePatternConstructors, LanguageDef.validateRulePatterns,
    LanguageDef.patternFvarNames, LanguageDef.patternBinderNames, Pattern.constructorRefs,
    Pattern.constructorRefsList, Pattern.freeFvarNames]

set_option maxRecDepth 100000 in
/-- **The extension is a language definition**: extending the reflective calculus
once passes the validation gate. -/
theorem rhoOnce_validate_eq_nil : rhoOnce.validate = [] :=
  LanguageDef.validate_eq_nil_of_rows rhoOnce (by decide) (by decide) (by decide) (by decide)
    rhoOnce_terms_valid rhoOnce_equations_valid rhoOnce_rewrites_valid

set_option maxRecDepth 100000 in
/-- **And extending twice is rejected** by the same gate, for its duplicated
formers. -/
theorem rhoTwice_rejected : rhoTwice.validate ≠ [] := by
  intro valid
  simp only [LanguageDef.validate, List.append_eq_nil_iff] at valid
  have labels := (LanguageDef.duplicateErrors_eq_nil_iff_nodup _ _ _).mp valid.1.1.1.1.1.2
  exact absurd labels (by decide)

end Mettapedia.OSLF.Framework.TypeFormerExtension
