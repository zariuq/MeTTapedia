import Mettapedia.Languages.ProcessCalculi.CCS.RecursiveSteps
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalRegions
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Certificates

/-!
# Canonical forms for CCS with recursion

`ccsRecCalc` runs in the environment of its definitions (`definitionsEnv`). Its static theory is finite CCS's, with
calls as atoms: the parallel bag and the sums together with ν of inaction, exchange of restrictions, scope extrusion
and the empty sum. The restriction-block canonical form decides it on object processes, and here it becomes the
canonical forms the front door takes, in the typed reading, for any admitted definitions:

- **The domain**: object processes with no free bound variable, their free variables names. A typed object has one
  sort, so the reading relates the domain only to the domain.
- **Equivalent to the canonical form, through processes**, and **the same canonical form** for equivalent processes:
  soundness and completeness of the block canonical form.
- **Coherent for plain steps**: a reaction or a silent step of a process, a call taking part through its body, is
  matched by a step of its canonical form, to a contractum with the same canonical form (`simulation`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.CCSRecForms

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.OSLF.MeTTaIL.ContextualStep (engineBasePremises)
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationEquiv)
open Mettapedia.GSLT.LanguageDef.BagNormalForm (Admissible)
open Mettapedia.Languages.ProcessCalculi.CCS.Recursive (ccsRecCalc ccsRecBlockLanguage Definition admits definitionsEnv
  RecRawStep step_iff_raw typed_of_raw simulation)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (BaseContext SortedEquiv ProcEquiv canon_sound canon_complete
  metadata_of_typed equationEquiv_isObject equationStep_iff step_isObject)
open Mettapedia.Languages.ProcessCalculi.CCS.Blocks (ccsBlock)

/-- **The reading of CCS with recursion**: the typed reading, each law between two object terms of one sort whose free variables are names
of the name sort; the rules by the reference relation. -/
def reading : LanguageReading := { equations := .typed .raw .empty .sorts (some "Name") }

/-- The context of the free names. -/
abbrev names : FreeTypeContext := EquationReading.nameContext (some "Name")

theorem names_context : BaseContext names [] :=
  ⟨fun _ _ found => ⟨"Name", by simpa [names, EquationReading.nameContext] using found.symm⟩,
    fun _ member => by simp at member⟩

/-- **Object processes with no free bound variable**, their free variables names. -/
def domain (term : Pattern) : Bool :=
  Mettapedia.GSLT.LanguageDef.WellSorted.checkOpenPatternWellSorted ccsRecCalc names [] (.base "Proc") term

/-- **The canonical form**: the block canonical form on the domain, the term itself elsewhere. -/
def canon (term : Pattern) : Pattern :=
  if domain term then Mettapedia.GSLT.LanguageDef.RestrictionBlocks.canon ccsBlock term else term

theorem typed_of_domain {term : Pattern} (admitted : domain term = true) :
    HasType ccsRecCalc names [] term (.base "Proc") ∧ isObjectPattern term = true := by
  unfold domain at admitted
  rw [checkOpenPatternWellSorted_eq_true_iff] at admitted
  exact ⟨admitted.1, admitted.2.2.1⟩

theorem domain_of_typed {term : Pattern} (typed : HasType ccsRecCalc names [] term (.base "Proc"))
    (object : isObjectPattern term = true) : domain term = true := by
  unfold domain
  rw [checkOpenPatternWellSorted_eq_true_iff]
  exact ⟨typed, (metadata_of_typed (block := ccsBlock) _ typed object).1 ⟨_, rfl⟩, object,
    by simpa [ScopeSafeAt] using typed.isWellScopedAt⟩

/-- **A typed object has one sort**: a free name has the name sort, a constructor's label determines its sort, and a
bag is a process. -/
theorem sort_unique {term : Pattern} {first second : String} (firstTyped : HasType ccsRecCalc names [] term (.base first))
    (secondTyped : HasType ccsRecCalc names [] term (.base second)) (object : isObjectPattern term = true) :
    first = second := by
  have firstCopy := firstTyped
  cases firstTyped with
  | bvar lookup => simp at lookup
  | fvar lookup =>
      cases secondTyped with
      | fvar lookup' =>
          simp only [names, EquationReading.nameContext, Option.some.injEq, TypeExpr.base.injEq] at lookup lookup'
          exact lookup.symm.trans lookup'
  | constructor member =>
      obtain ⟨rule', member', labelIs, -, typeIs, -⟩ := hasType_apply_inversion secondTyped
      simp only [TypeExpr.base.injEq] at typeIs
      rw [typeIs, ccsRecBlockLanguage.rule_eq_of_label member member' labelIs]
  | subst => simp [isObjectPattern] at object
  | collectionConstructor =>
      exact (ccsRecBlockLanguage.bag_members firstCopy).2.1.trans (ccsRecBlockLanguage.bag_members secondTyped).2.1.symm

/-- **A step of the reading relates the domain only to the domain**, both ways. -/
theorem domain_iff_of_step {relEnv : RelationEnv} {first second : Pattern}
    (step : ObjectStep relEnv ccsRecCalc reading first second) : domain first = true ↔ domain second = true := by
  obtain ⟨-, -, type, ⟨sort, rfl⟩, firstFormed, secondFormed, -⟩ := step
  constructor
  · intro admitted
    obtain ⟨typed, object⟩ := typed_of_domain admitted
    obtain rfl := sort_unique firstFormed.typed typed object
    exact domain_of_typed secondFormed.typed secondFormed.object
  · intro admitted
    obtain ⟨typed, object⟩ := typed_of_domain admitted
    obtain rfl := sort_unique secondFormed.typed typed object
    exact domain_of_typed firstFormed.typed firstFormed.object

theorem domain_iff_of_equivalent {relEnv : RelationEnv} {first second : Pattern}
    (equivalent : ObjectEquivalent relEnv ccsRecCalc reading first second) : domain first = true ↔ domain second = true := by
  induction equivalent with
  | rel _ _ step => exact domain_iff_of_step step
  | refl => exact Iff.rfl
  | symm _ _ _ same => exact same.symm
  | trans _ _ _ _ _ first second => exact first.trans second

/-- **A chain through processes, from an object, is an equivalence of the reading.** -/
theorem objectEquivalent_of_sortedEquiv (relEnv : RelationEnv) {first second : Pattern}
    (equivalent : ProcEquiv ccsRecCalc ccsBlock names [] first second) :
    isObjectPattern first = true → ObjectEquivalent relEnv ccsRecCalc reading first second := by
  induction equivalent with
  | rel first second step =>
      intro firstObject
      have secondObject : isObjectPattern second = true := by
        rw [← step_isObject (block := ccsBlock) step.step]; exact firstObject
      exact .rel _ _ ⟨firstObject, secondObject, .base "Proc", ⟨"Proc", rfl⟩,
        ⟨firstObject, step.firstTyped, by simp⟩, ⟨secondObject, step.secondTyped, by simp⟩,
        disciplinedStep_raw_iff.mpr ((equationStep_iff (block := ccsBlock) relEnv _).mpr step.step)⟩
  | refl => intro _; exact .refl _
  | symm first second chain recurse =>
      intro object
      exact .symm _ _ (recurse (by
        rw [equationEquiv_isObject (block := ccsBlock) (SortedEquiv.toEquationEquiv chain)]; exact object))
  | trans first middle third left _ leftRecurse rightRecurse =>
      intro object
      exact .trans _ _ _ (leftRecurse object)
        (rightRecurse (by rw [← equationEquiv_isObject (block := ccsBlock) (SortedEquiv.toEquationEquiv left)]; exact object))

/-- **Every reading's equivalence is part of the static theory.** -/
theorem equationEquiv_of_objectEquivalent {relEnv : RelationEnv} {anyReading : LanguageReading} {first second : Pattern}
    (equivalent : ObjectEquivalent relEnv ccsRecCalc anyReading first second) :
    EquationEquiv (engineBasePremises RelationEnv.empty) ccsRecCalc first second :=
  Relation.EqvGen.mono (fun _ _ step => (equationStep_iff (block := ccsBlock) relEnv _).mp step) _ _
    equivalent.equivalent

theorem profile : ReferenceProfile ccsRecCalc := profile_of_aligned (by decide)

section Forms

variable {definitions : List Definition}

/-- The reference steps of `ccsRecCalc` in the environment of the definitions are the steps of its occurrence
specification. -/
theorem reference_iff_raw {source target : Pattern} :
    (∃ witness, StepValid (definitionsEnv definitions) ccsRecCalc source witness target) ↔
      RecRawStep definitions source target :=
  (contextualStep_iff_step (definitionsEnv definitions) ccsRecCalc profile).symm.trans (step_iff_raw source target)

theorem admissible_of_typed {term : Pattern} (typed : HasType ccsRecCalc names [] term (.base "Proc"))
    (object : isObjectPattern term = true) : Admissible ccsRecCalc names [] (.base "Proc") term :=
  ⟨typed, (metadata_of_typed (block := ccsBlock) _ typed object).1 ⟨_, rfl⟩, object⟩

variable (admitted : admits definitions = true)
include admitted

/-- **The block canonical form gives canonical forms** on object processes, in the typed reading. -/
theorem canonical : Canonical (definitionsEnv definitions) ccsRecCalc canon domain reading where
  object admitted := (typed_of_domain admitted).2
  admitted_canon {term} admitted := by
    obtain ⟨typed, object⟩ := typed_of_domain admitted
    obtain ⟨canonTyped, equivalent⟩ := canon_sound (block := ccsBlock) names_context typed
    unfold canon
    rw [if_pos admitted]
    exact domain_of_typed canonTyped
      (by rw [← equationEquiv_isObject (block := ccsBlock) equivalent.toEquationEquiv]; exact object)
  invariant admitted equivalent := (domain_iff_of_equivalent equivalent).mp admitted
  stepsAdmitted {redex witness contractum} inDomain _ valid _ := by
    obtain ⟨typed, object⟩ := typed_of_domain inDomain
    have raw := (reference_iff_raw (source := redex) (target := contractum)).mp ⟨witness, valid⟩
    obtain ⟨steppedTyped, steppedObject⟩ := typed_of_raw admitted raw typed object
    exact domain_of_typed steppedTyped steppedObject
  equivalent {term} admitted := by
    obtain ⟨typed, object⟩ := typed_of_domain admitted
    obtain ⟨canonTyped, equivalent⟩ := canon_sound (block := ccsBlock) names_context typed
    unfold canon
    rw [if_pos admitted]
    exact objectEquivalent_of_sortedEquiv _ equivalent object
  same {first second} admitted equivalent := by
    have secondAdmitted := (domain_iff_of_equivalent equivalent).mp admitted
    unfold canon
    rw [if_pos admitted, if_pos secondAdmitted]
    exact canon_complete (block := ccsBlock) (typed_of_domain admitted).2 (equationEquiv_of_objectEquivalent equivalent)
  closed {term} admitted := by
    obtain ⟨typed, object⟩ := typed_of_domain admitted
    unfold canon
    rw [if_pos admitted]
    have before := typed.isWellScopedAt
    have after := (canon_sound (block := ccsBlock) names_context typed).1.isWellScopedAt
    simp only [List.length_nil] at before after
    rw [before, after]

/-- **Coherence for plain steps**: a step from any process equivalent to a canonical one is matched, up to canonical
form, by a step listed at it, wherever the fuel lists its steps. -/
theorem coherentPlain (fuel : ℕ) :
    CoherentPlain (definitionsEnv definitions) ccsRecCalc fuel canon domain List.singleton reading :=
  coherentPlain_of_simulation (canonical admitted) fun {redex witness contractum} _ inDomain valid => by
    obtain ⟨typed, object⟩ := typed_of_domain inDomain
    have raw := reference_iff_raw.mp ⟨witness, valid⟩
    obtain ⟨contractum', raw', same⟩ := simulation admitted names_context raw typed object
    obtain ⟨witness', valid'⟩ := reference_iff_raw.mpr raw'
    obtain ⟨canonTyped, canonEquivalent⟩ := canon_sound (block := ccsBlock) names_context typed
    have canonObject : isObjectPattern (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.canon ccsBlock redex) = true := by
      rw [← equationEquiv_isObject (block := ccsBlock) canonEquivalent.toEquationEquiv]
      exact object
    have contractumAdmitted : domain contractum = true := by
      obtain ⟨steppedTyped, steppedObject⟩ := typed_of_raw admitted raw typed object
      exact domain_of_typed steppedTyped steppedObject
    have contractum'Admitted : domain contractum' = true := by
      obtain ⟨steppedTyped, steppedObject⟩ := typed_of_raw admitted raw' canonTyped canonObject
      exact domain_of_typed steppedTyped steppedObject
    refine ⟨witness', contractum', ?_, ?_⟩
    · unfold canon
      rw [if_pos inDomain]
      exact valid'
    · unfold canon
      rw [if_pos contractumAdmitted, if_pos contractum'Admitted]
      exact same

/-- **The canonical forms of CCS with recursion, as the front door takes them**: in the environment of admitted
definitions, in the typed reading, coherent for plain steps. -/
def forms (fuel : ℕ) : CanonicalForms (definitionsEnv definitions) ccsRecCalc fuel where
  reading := reading
  canon := canon
  domain := domain
  canonical := canonical admitted
  labels := plainLabel
  coherent := CoherentPlain.on (coherentPlain admitted fuel)

end Forms

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.CCSRecForms
