import Mettapedia.OSLF.NativeTypes.GeneratedLogic.AlgebraCanonicalForms

/-!
# Canonical forms for a bag algebra, in the typed reading, in several sorts

`AlgebraCanonicalForms` reads a bag algebra's laws as the syntax theory, in one sort: there, a law read from right to
left can wrap a term in a bag, and only one sort guarantees that the bag is sorted. Read as the **typed judgment at
the sorts** (`reading`), each law relates two closed terms of one sort, so no sortedness argument is needed, and the
language may have several sorts:

- **The domain** (`domain`): closed terms of one of the listed sorts. Each closed object of a sort has a listed sort
  (`SortsCover`) and canonical binder metadata (`MetadataOfTyped`); then a step of the typed reading relates terms of
  the domain only to terms of the domain.
- **The bag normal form gives canonical forms** read off them (`canonicalDetermined`, `canonical`): a closed term
  of a sort reaches its normal form through closed terms of that sort (`path_normalForm`), and equivalent terms have
  one normal form (`normalForm_eq_of_equationEquiv`).

The ambient calculus, with processes and names, is an instance.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.AlgebraTyped

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.OSLF.MeTTaIL.ContextualStep (BasePremiseEvaluator)
open Mettapedia.GSLT.LanguageDef (defaultBasePremises)
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.BagNormalForm

/-- **The typed reading at the sorts**: each law relates two closed terms of one sort; the rules by the reference
relation. -/
def reading : LanguageReading := { equations := .typed .raw .empty .sorts none }

variable (language : LanguageDef) (unit : Option String) (sorts : List String)

/-- **Every closed object of a sort has a listed sort.** -/
def SortsCover : Prop :=
  ∀ {term : Pattern} {sort : String}, HasType language FreeTypeContext.empty [] term (.base sort) →
    isObjectPattern term = true → sort ∈ sorts

/-- **Every closed object of a sort has canonical binder metadata.** -/
def MetadataOfTyped : Prop :=
  ∀ {term : Pattern} {sort : String}, HasType language FreeTypeContext.empty [] term (.base sort) →
    isObjectPattern term = true → term.hasCanonicalBinderMetadata = true

/-- **The domain**: closed terms of one of the listed sorts. -/
def domain (term : Pattern) : Bool :=
  sorts.any fun sort => checkOpenPatternWellSorted language FreeTypeContext.empty [] (.base sort) term

/-- **The canonical form**: the bag normal form on the domain, the term itself elsewhere. -/
def canon (term : Pattern) : Pattern :=
  if domain language sorts term then normalForm unit term else term

variable {language unit sorts} {bag : GrammarRule}

theorem domain_iff {term : Pattern} :
    domain language sorts term = true ↔
      ∃ sort ∈ sorts, Admissible language FreeTypeContext.empty [] (.base sort) term := by
  unfold domain
  simp only [List.any_eq_true, checkOpenPatternWellSorted_eq_true_iff]
  constructor
  · rintro ⟨sort, member, typed, canonical, object, -⟩
    exact ⟨sort, member, typed, canonical, object⟩
  · rintro ⟨sort, member, admissible⟩
    exact ⟨sort, member, admissible.typed, admissible.canonical, admissible.object,
      by simpa [ScopeSafeAt] using admissible.typed.isWellScopedAt⟩

/-- A closed object of a sort is admitted, when sorts cover and typing gives the metadata. -/
theorem domain_of_typed (cover : SortsCover language sorts) (metadata : MetadataOfTyped language)
    {term : Pattern} {sort : String} (typed : HasType language FreeTypeContext.empty [] term (.base sort))
    (object : isObjectPattern term = true) : domain language sorts term = true :=
  domain_iff.mpr ⟨sort, cover typed object, typed, metadata typed object, object⟩

theorem normalForm_admissible (laws : BareBagTheory language bag unit) {term : Pattern} {sort : String}
    (admissible : Admissible language FreeTypeContext.empty [] (.base sort) term) :
    Admissible language FreeTypeContext.empty [] (.base sort) (normalForm unit term) :=
  path_admissible laws (path_normalForm laws defaultBasePremises term admissible rfl) admissible rfl

variable {relEnv : RelationEnv}

/-- **A chain of laws from a closed term of a sort is an equivalence in the typed reading.** -/
theorem objectEquivalent_of_path (laws : BareBagTheory language bag unit) {base : BasePremiseEvaluator}
    {source target : Pattern} {sort : String} (path : Path base language source target)
    (admissible : Admissible language FreeTypeContext.empty [] (.base sort) source) :
    ObjectEquivalent relEnv language reading source target := by
  induction path with
  | refl => exact Relation.EqvGen.refl _
  | tail before step previous =>
    have middle := path_admissible laws before admissible rfl
    have last := step_admissible laws step middle rfl
    refine Relation.EqvGen.trans _ _ _ previous (Relation.EqvGen.rel _ _ ⟨middle.object, last.object, .base sort,
      ⟨sort, rfl⟩, ⟨middle.object, middle.typed, by simp⟩, ⟨last.object, last.typed, by simp⟩, ?_⟩)
    exact disciplinedStep_raw_iff.mpr (AlgebraForms.step_of_equationContextStep laws.equationsEmpty step)

/-- **A step of the typed reading relates admitted terms to admitted terms**, both ways. -/
theorem domain_iff_of_step (cover : SortsCover language sorts) (metadata : MetadataOfTyped language)
    {first second : Pattern} (step : ObjectStep relEnv language reading first second) :
    domain language sorts first = true ∧ domain language sorts second = true := by
  obtain ⟨-, -, type, ⟨sort, rfl⟩, firstFormed, secondFormed, -⟩ := step
  exact ⟨domain_of_typed cover metadata firstFormed.typed firstFormed.object,
    domain_of_typed cover metadata secondFormed.typed secondFormed.object⟩

/-- **The typed reading keeps the domain**, both ways. -/
theorem domain_iff_of_equivalent (cover : SortsCover language sorts) (metadata : MetadataOfTyped language)
    {first second : Pattern} (equivalent : ObjectEquivalent relEnv language reading first second) :
    domain language sorts first = true ↔ domain language sorts second = true := by
  induction equivalent with
  | rel _ _ step =>
    obtain ⟨firstAdmitted, secondAdmitted⟩ := domain_iff_of_step cover metadata step
    exact iff_of_true firstAdmitted secondAdmitted
  | refl => exact Iff.rfl
  | symm _ _ _ same => exact same.symm
  | trans _ _ _ _ _ first second => exact first.trans second

/-- **Equivalent terms have one normal form**, in every reading. -/
theorem normalForm_eq_of_objectEquivalent (laws : BareBagTheory language bag unit) {anyReading : LanguageReading}
    {first second : Pattern} (equivalent : ObjectEquivalent relEnv language anyReading first second) :
    normalForm unit first = normalForm unit second :=
  normalForm_eq_of_equationEquiv laws.toBagTheory
    (AlgebraForms.equationEquiv_of_objectEquivalent laws.equationsEmpty defaultBasePremises equivalent.toSyntax)

/-- **The bag normal form gives canonical forms** on closed terms of the listed sorts, in the typed reading, read off
them. -/
theorem canonicalDetermined (laws : BareBagTheory language bag unit) (cover : SortsCover language sorts)
    (metadata : MetadataOfTyped language) :
    CanonicalDetermined relEnv language (canon language unit sorts) (domain language sorts) reading where
  object admitted := by
    obtain ⟨_, _, admissible⟩ := domain_iff.mp admitted
    exact admissible.object
  determined term := by
    unfold canon
    by_cases admitted : domain language sorts term = true
    · rw [if_pos admitted, admitted]
      obtain ⟨sort, member, admissible⟩ := domain_iff.mp admitted
      exact domain_iff.mpr ⟨sort, member, normalForm_admissible laws admissible⟩
    · rw [if_neg admitted]
  equivalent {term} admitted := by
    unfold canon
    rw [if_pos admitted]
    obtain ⟨sort, -, admissible⟩ := domain_iff.mp admitted
    exact objectEquivalent_of_path laws (path_normalForm laws defaultBasePremises term admissible rfl) admissible
  same {first second} admitted equivalent := by
    have secondAdmitted := (domain_iff_of_equivalent cover metadata equivalent).mp admitted
    unfold canon
    rw [if_pos admitted, if_pos secondAdmitted]
    exact normalForm_eq_of_objectEquivalent laws equivalent
  closed {term} admitted := by
    unfold canon
    rw [if_pos admitted]
    obtain ⟨sort, -, admissible⟩ := domain_iff.mp admitted
    have before := admissible.typed.isWellScopedAt
    have after := (normalForm_admissible laws admissible).typed.isWellScopedAt
    simp only [List.length_nil] at before after
    rw [before, after]

/-- **The bag normal form gives canonical forms** on closed terms of the listed sorts, in the typed reading. -/
theorem canonical (laws : BareBagTheory language bag unit) (cover : SortsCover language sorts)
    (metadata : MetadataOfTyped language) :
    Canonical relEnv language (canon language unit sorts) (domain language sorts) reading :=
  (canonicalDetermined laws cover metadata).canonical

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.AlgebraTyped
