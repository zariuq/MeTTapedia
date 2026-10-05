import Mettapedia.GSLT.LanguageDef.Interaction.Controls.ContactContinued

/-!
# The forgetful functor from continued theories is not full

A morphism of continued theories is injective on canonical keys.  The
morphism of iGSLTs from the law-free contact theory to itself that sends the
constant `B` to the constant `A` preserves bisimilarity and identifies two
canonical keys.  It is a morphism between the underlying iGSLTs of a
continued theory with no lift, so the forgetful functor is not full, with
morphisms taken as defined or up to their underlying theory map.

The same morphism is a morphism of the wrappable theories under that
continued theory.  The failure of fullness therefore already occurs when only
the section is forgotten.
-/

set_option autoImplicit false

open CategoryTheory

namespace Mettapedia.GSLT.LanguageDef.CIGSLT

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.Interaction.Controls.EquationalContact
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- A closed term of the law-free contact theory as a canonical key: with no
law, every term is its own normal form. -/
def bareKey (term : barePresentation.Term) : bareContinued.CanonicalKey :=
  ⟨⟨term.1, ⟨term.2.1, term.2.2.2.1, term.2.2.2.2.1, term.2.2.2.2.2⟩,
    ReflectiveWellSorted.reflectiveScopeSafeAt_empty _ _⟩, rfl⟩

@[simp] theorem bareKey_pattern (term : barePresentation.Term) :
    (bareKey term).1.1 = term.1 :=
  rfl

/-- The two constants are distinct canonical keys. -/
theorem bareKey_constants_distinct : bareKey closedA ≠ bareKey closedB := by
  intro same
  have patterns : termA = termB := congrArg (fun key => key.1.1) same
  revert patterns
  decide

/-- **The key-collapsing morphism has no lift.**  A morphism of continued
theories over it would send two distinct canonical keys to one pattern. -/
theorem collapse_has_no_lift :
    ¬ ∃ lift : bareContinued ⟶ bareContinued, forget.map lift = collapse := by
  rintro ⟨lift, liftsCollapse⟩
  have underlying : lift.underlying = collapse := liftsCollapse
  apply bareKey_constants_distinct
  apply lift.quoteFaithful
  show mapPattern lift.underlying.structural.structural.symbols termA =
    mapPattern lift.underlying.structural.structural.symbols termB
  rw [underlying]
  show mapPattern collapseSymbols termA = mapPattern collapseSymbols termB
  decide +kernel

/-- **Not full.**  The forgetful functor from continued theories is not full. -/
theorem forget_not_full : ¬ forget.Full := by
  intro full
  exact collapse_has_no_lift (full.map_surjective (X := bareContinued) (Y := bareContinued)
    collapse)

/-- Nor is it full when morphisms are taken up to their underlying theory
map. -/
theorem forgetUpToTheoryMap_not_full : ¬ forgetUpToTheoryMap.Full := by
  intro full
  obtain ⟨preimage, image⟩ := full.map_surjective
    (X := (CategoryTheory.Quotient.functor forget.homRel).obj bareContinued)
    (Y := (CategoryTheory.Quotient.functor forget.homRel).obj bareContinued) collapse
  obtain ⟨lift, rfl⟩ := (CategoryTheory.Quotient.functor forget.homRel).map_surjective preimage
  exact collapse_has_no_lift ⟨lift, image⟩

/-! ## The section laws are what exclude it

The key-collapsing morphism satisfies every law of a morphism of wrappable
theories.  So the functor that forgets the section is not full: of the laws
of a continued morphism, the two about the section are the ones it breaks. -/

/-- The renaming changes no type: it fixes every sort. -/
theorem mapTypeExpr_collapse (type : TypeExpr) : mapTypeExpr collapseSymbols type = type := by
  induction type with
  | base sort => rfl
  | arrow domain codomain domainFixed codomainFixed =>
      simp [mapTypeExpr, domainFixed, codomainFixed]
  | multiBinder body bodyFixed => simp [mapTypeExpr, bodyFixed]
  | collection collectionType element elementFixed => simp [mapTypeExpr, elementFixed]

/-- So it changes no constructor parameter. -/
theorem mapTermParam_collapse (parameter : TermParam) :
    mapTermParam collapseSymbols parameter = parameter := by
  cases parameter <;> simp [mapTermParam, mapTypeExpr_collapse]

/-- A declaration renamed to one whose label is neither `A` nor `B` and which
has no collection algebra is that declaration. -/
theorem eq_of_mapGrammarRule_collapse {rule target : GrammarRule}
    (notA : target.label ≠ "A") (notB : target.label ≠ "B")
    (plain : target.algebra? = none)
    (image : mapGrammarRule collapseSymbols rule = target) : rule = target := by
  obtain ⟨label, category, params, syntaxPattern, evalPolicy, algebra⟩ := rule
  subst image
  simp only [mapGrammarRule] at notA notB plain ⊢
  have labelFixed : label = collapseSymbols.constructor label :=
    (collapse_eq_iff notA notB).mp rfl
  have paramsFixed : params.map (mapTermParam collapseSymbols) = params := by
    conv_rhs => rw [← List.map_id params]
    exact List.map_congr_left fun parameter _ => mapTermParam_collapse parameter
  have algebraFixed : algebra = none := by
    cases algebra with
    | none => rfl
    | some value => simp at plain
  subst algebraFixed
  rw [paramsFixed, ← labelFixed]
  rfl

/-- **The key-collapsing morphism is a morphism of wrappable theories.**  It
fixes the cut and both introductions, and it reflects them, since only the
constant `B` is renamed. -/
def collapseWrappable :
    bareContinued.toWrappableIGSLT ⟶ bareContinued.toWrappableIGSLT where
  underlying := collapse
  reflectionSymbols := ReflectionExtension.ReflectionSymbols.id
  mapsReflectivePresentations := by
    intro declaration membership
    cases membership
  mapsReflectiveRules := by
    intro declaration membership
    cases membership
  mapsReflectiveScope := fun _ => ReflectiveWellSorted.reflectiveScopeSafeAt_empty _ _
  mapsCoreSort := Subtype.ext rfl
  mapsCoreContactConstructor := Subtype.ext (by decide +kernel)
  mapsCorePattern := by decide +kernel
  mapsSourceEnvelope := rfl
  reflectsInteractingSort := fun _ same => same
  mapsWrappedLabelMembership := by
    intro sourceLabel
    by_cases isB : sourceLabel = "B"
    · subst isB
      decide +kernel
    · have fixed : collapseSymbols.constructor sourceLabel = sourceLabel := by
        simp [collapseSymbols, isB]
      show collapseSymbols.constructor sourceLabel ∈ _ ↔ sourceLabel ∈ _
      rw [fixed]
  reflectsProgramConstructor := fun _ image =>
    eq_of_mapGrammarRule_collapse (by decide) (by decide) rfl image
  reflectsEnvironmentConstructor := fun _ image =>
    eq_of_mapGrammarRule_collapse (by decide) (by decide) rfl image
  mapsProgramConstructor := Subtype.ext (by decide +kernel)
  mapsEnvironmentConstructor := Subtype.ext (by decide +kernel)
  mapsProgramContinuationIndex := rfl
  mapsEnvironmentContinuationIndex := rfl
  mapsProgramKind := rfl
  mapsEnvironmentKind := rfl
  mapsProgramSchema := by decide +kernel
  mapsEnvironmentSchema := by decide +kernel
  mapsProgramContinuation := rfl
  mapsEnvironmentContinuation := rfl
  mapsProgramSubject := rfl
  mapsEnvironmentSubject := rfl

/-- **Forgetting the section is not full.**  The key-collapsing morphism is a
morphism between the wrappable theories under one continued theory, and no
continued morphism lies over it: the section laws exclude it. -/
theorem toWrappable_not_full : ¬ toWrappable.Full := by
  intro full
  obtain ⟨lift, liftsCollapse⟩ := full.map_surjective (X := bareContinued)
    (Y := bareContinued) collapseWrappable
  exact collapse_has_no_lift
    ⟨lift, congrArg WrappableIGSLT.Morphism.underlying liftsCollapse⟩

end Mettapedia.GSLT.LanguageDef.CIGSLT
