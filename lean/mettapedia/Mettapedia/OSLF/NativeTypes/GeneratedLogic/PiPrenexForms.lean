import Mettapedia.Languages.ProcessCalculi.PiCalculus.PrenexSteps
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationObjects
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiCanonicalForms

/-!
# Canonical forms for the π-calculus with its restriction laws

`piCalc`'s static theory is its bag together with ν of inaction, exchange of restrictions, scope extrusion and the laws
of replication. Its canonical form (the replication theory's at π's blocks) decides that theory on object processes,
and here it becomes the canonical forms the front door takes, in π's typed reading (`reading`: each law between two
object terms of one sort, their free variables names of the name sort):

- **The domain**: object processes with no free bound variable, their free variables names. Typed processes carry no
  binder names. A typed object has one sort (`sort_unique`), so the reading relates the domain only to the domain.
- **Equivalent to the canonical form, through processes**: soundness gives a chain of laws, and every chain of laws
  between object processes runs through object processes (`objectEquivalent_of_equationEquiv`).
- **Same canonical form**: completeness, since the typed reading is part of the static theory.
- **Coherent for plain steps**: a step of a process is matched by a step of a presentation of its canonical form, to
  a contractum with the same canonical form (`PrenexForm.presented`). A presentation is an unfolding of the replicated
  components: within two unfoldings when every replicated component copies one component, π's redexes having two
  parts, and within twice the ceiling read off the form otherwise. Every presentation is a process with that canonical
  form.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiPrenexForms

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.OSLF.MeTTaIL.ContextualStep (engineBasePremises)
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationEquiv)
open Mettapedia.GSLT.LanguageDef.BagNormalForm (Admissible)
open Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance (piCalc PiRawStep pi_step_iff_raw)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (BaseContext SortedEquiv ProcEquiv canonR canonR_sound
  canonR_complete metadata_of_typed equationStep_iff_replication restrictionsBind_of_typed isObject_canonR
  replicationPresentations replicationPresentations_admitted ObjectChain objectChain_of_equationEquiv)
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Blocks (piBlock piRepBlock)

/-- **π's reading**: the typed reading, each law between two object terms of one sort whose free variables are names
of the name sort; the rules by the reference relation. -/
def reading : LanguageReading := { equations := .typed .raw .empty .sorts (some "Name") }

/-- The context of π's free names. -/
abbrev names : FreeTypeContext := EquationReading.nameContext (some "Name")

theorem names_eq : names = Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance.piNameContext := rfl

theorem names_context : BaseContext names [] :=
  ⟨fun _ _ found => ⟨"Name", by simpa [names, EquationReading.nameContext] using found.symm⟩,
    fun _ member => by simp at member⟩

/-- **Object processes with no free bound variable**, their free variables names. -/
def domain (term : Pattern) : Bool :=
  Mettapedia.GSLT.LanguageDef.WellSorted.checkOpenPatternWellSorted piCalc names [] (.base "Proc") term

/-- **The canonical form**: π's canonical form with replication on the domain, the term itself elsewhere. -/
def canon (term : Pattern) : Pattern :=
  if domain term then canonR piRepBlock term else term

/-- **The presentations of a state**: its unfoldings within the presentation depth of its canonical block, π's
redexes having two parts. -/
def presentations (state : Pattern) : List Pattern := replicationPresentations piRepBlock 2 state

theorem typed_of_domain {term : Pattern} (admitted : domain term = true) :
    HasType piCalc names [] term (.base "Proc") ∧ isObjectPattern term = true := by
  unfold domain at admitted
  rw [checkOpenPatternWellSorted_eq_true_iff] at admitted
  exact ⟨admitted.1, admitted.2.2.1⟩

theorem domain_of_typed {term : Pattern} (typed : HasType piCalc names [] term (.base "Proc"))
    (object : isObjectPattern term = true) : domain term = true := by
  unfold domain
  rw [checkOpenPatternWellSorted_eq_true_iff]
  exact ⟨typed, (metadata_of_typed (block := piBlock) _ typed object).1 ⟨_, rfl⟩, object,
    by simpa [ScopeSafeAt] using typed.isWellScopedAt⟩

/-- **A typed object has one sort**: a free name has the name sort, and every constructor of π makes a process. -/
theorem sort_unique {term : Pattern} {first second : String} (firstTyped : HasType piCalc names [] term (.base first))
    (secondTyped : HasType piCalc names [] term (.base second)) (object : isObjectPattern term = true) :
    first = second := by
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
      rw [Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance.category_of_member member, typeIs,
        Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance.category_of_member member']
  | subst => simp [isObjectPattern] at object
  | collectionConstructor member =>
      rw [Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance.category_of_member member]
      exact ((Mettapedia.Languages.ProcessCalculi.PiCalculus.Blocks.piBlockSignature.bag_members secondTyped).2.1).symm

/-- **A step of π's reading relates the domain only to the domain**, both ways. -/
theorem domain_iff_of_step {relEnv : RelationEnv} {first second : Pattern}
    (step : ObjectStep relEnv piCalc reading first second) : domain first = true ↔ domain second = true := by
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
    (equivalent : ObjectEquivalent relEnv piCalc reading first second) : domain first = true ↔ domain second = true := by
  induction equivalent with
  | rel _ _ step => exact domain_iff_of_step step
  | refl => exact Iff.rfl
  | symm _ _ _ same => exact same.symm
  | trans _ _ _ _ _ first second => exact first.trans second

/-- **A chain of laws through object processes is an equivalence of π's reading.** -/
theorem objectEquivalent_of_objectChain (relEnv : RelationEnv) {first second : Pattern}
    (chain : ObjectChain piCalc names [] (.base "Proc") first second) :
    ObjectEquivalent relEnv piCalc reading first second := by
  induction chain with
  | rel first second step =>
      obtain ⟨step, firstObject, secondObject⟩ := step
      exact .rel _ _ ⟨firstObject, secondObject, .base "Proc", ⟨"Proc", rfl⟩,
        ⟨firstObject, step.firstTyped, by simp⟩, ⟨secondObject, step.secondTyped, by simp⟩,
        disciplinedStep_raw_iff.mpr ((equationStep_iff_replication (block := piRepBlock) relEnv _).mpr step.step)⟩
  | refl => exact .refl _
  | symm _ _ _ recurse => exact .symm _ _ recurse
  | trans _ _ _ _ _ left right => exact .trans _ _ _ left right

/-- **Equivalent object processes are equivalent in π's reading**: a chain of laws between them, read through its
object reading, passes through object processes only. -/
theorem objectEquivalent_of_equationEquiv (relEnv : RelationEnv) {first second : Pattern}
    (firstTyped : HasType piCalc names [] first (.base "Proc")) (secondTyped : HasType piCalc names [] second (.base "Proc"))
    (firstObject : isObjectPattern first = true) (secondObject : isObjectPattern second = true)
    (equivalent : EquationEquiv (engineBasePremises RelationEnv.empty) piCalc first second) :
    ObjectEquivalent relEnv piCalc reading first second :=
  objectEquivalent_of_objectChain relEnv (objectChain_of_equationEquiv (block := piRepBlock) names_context firstTyped
    secondTyped firstObject secondObject equivalent)

/-- **Every reading's equivalence is part of π's static theory.** -/
theorem equationEquiv_of_objectEquivalent {relEnv : RelationEnv} {anyReading : LanguageReading} {first second : Pattern}
    (equivalent : ObjectEquivalent relEnv piCalc anyReading first second) :
    EquationEquiv (engineBasePremises RelationEnv.empty) piCalc first second :=
  Relation.EqvGen.mono (fun _ _ step => (equationStep_iff_replication (block := piRepBlock) relEnv _).mp step) _ _
    equivalent.equivalent

theorem profile : ReferenceProfile piCalc := profile_of_aligned (by decide)

/-- The reference steps of `piCalc` are the steps of its occurrence specification. -/
theorem step_iff_raw {source target : Pattern} :
    (∃ witness, StepValid RelationEnv.empty piCalc source witness target) ↔ PiRawStep source target :=
  (contextualStep_iff_step RelationEnv.empty piCalc profile).symm.trans (pi_step_iff_raw source target)

theorem admissible_of_typed {term : Pattern} (typed : HasType piCalc names [] term (.base "Proc"))
    (object : isObjectPattern term = true) : Admissible piCalc names [] (.base "Proc") term :=
  ⟨typed, (metadata_of_typed (block := piBlock) _ typed object).1 ⟨_, rfl⟩, object⟩

/-- **π's canonical form with replication gives canonical forms** on closed object processes, in the typed
reading. -/
theorem canonical : Canonical RelationEnv.empty piCalc canon domain reading where
  object admitted := (typed_of_domain admitted).2
  admitted_canon {term} admitted := by
    obtain ⟨typed, object⟩ := typed_of_domain admitted
    unfold canon
    rw [if_pos admitted]
    exact domain_of_typed (canonR_sound (block := piRepBlock) names_context typed).1
      (isObject_canonR (block := piRepBlock) object)
  invariant admitted equivalent := (domain_iff_of_equivalent equivalent).mp admitted
  stepsAdmitted {redex witness contractum} admitted _ valid _ := by
    obtain ⟨typed, object⟩ := typed_of_domain admitted
    have raw := (step_iff_raw (source := redex) (target := contractum)).mp ⟨witness, valid⟩
    have stepped := PiForms.admissible_of_raw raw (admissible_of_typed typed object)
    exact domain_of_typed stepped.typed stepped.object
  equivalent {term} admitted := by
    obtain ⟨typed, object⟩ := typed_of_domain admitted
    obtain ⟨canonTyped, equivalent⟩ := canonR_sound (block := piRepBlock) names_context typed
    unfold canon
    rw [if_pos admitted]
    exact objectEquivalent_of_equationEquiv RelationEnv.empty typed canonTyped object
      (isObject_canonR (block := piRepBlock) object) equivalent.toEquationEquiv
  same {first second} admitted equivalent := by
    have secondAdmitted := (domain_iff_of_equivalent equivalent).mp admitted
    obtain ⟨firstTyped, firstObject⟩ := typed_of_domain admitted
    obtain ⟨-, secondObject⟩ := typed_of_domain secondAdmitted
    unfold canon
    rw [if_pos admitted, if_pos secondAdmitted]
    exact canonR_complete (block := piRepBlock) firstObject secondObject
      (restrictionsBind_of_typed (block := piRepBlock) first firstTyped) (equationEquiv_of_objectEquivalent equivalent)
  closed {term} admitted := by
    obtain ⟨typed, object⟩ := typed_of_domain admitted
    unfold canon
    rw [if_pos admitted]
    have before := typed.isWellScopedAt
    have after := (canonR_sound (block := piRepBlock) names_context typed).1.isWellScopedAt
    simp only [List.length_nil] at before after
    rw [before, after]

/-- **A presentation of a process's canonical form is a process with that canonical form.** -/
theorem presentation_process {state shown : Pattern} (stateIn : domain state = true)
    (presented : shown ∈ presentations (canon state)) : domain shown = true ∧ canon shown = canon state := by
  obtain ⟨typed, object⟩ := typed_of_domain stateIn
  obtain ⟨canonTyped, canonEquivalent⟩ := canonR_sound (block := piRepBlock) names_context typed
  have canonObject := isObject_canonR (block := piRepBlock) object
  unfold canon at presented ⊢
  rw [if_pos stateIn] at presented ⊢
  obtain ⟨shownTyped, shownObject, shownCanon⟩ :=
    replicationPresentations_admitted (block := piRepBlock) names_context canonTyped canonObject 2 shown presented
  have shownIn := domain_of_typed shownTyped shownObject
  refine ⟨shownIn, ?_⟩
  rw [if_pos shownIn, shownCanon]
  exact canonR_complete (block := piRepBlock) (base := engineBasePremises RelationEnv.empty) canonObject object
    (restrictionsBind_of_typed (block := piRepBlock) _ canonTyped)
    (Relation.EqvGen.symm _ _ canonEquivalent.toEquationEquiv)

/-- **Coherence for plain steps**: a step from any process equivalent to a canonical one is matched, up to canonical
form, by a step listed at a presentation of it, wherever the fuel lists their steps. -/
theorem coherentPlain (fuel : ℕ) :
    CoherentPlain RelationEnv.empty piCalc fuel canon domain presentations reading :=
  coherentPlain_of_presented_simulation canonical fun {redex witness contractum} _ admitted valid => by
    obtain ⟨typed, object⟩ := typed_of_domain admitted
    have raw := step_iff_raw.mp ⟨witness, valid⟩
    obtain ⟨shown, presented, contractum', raw', equivalent⟩ :=
      Mettapedia.Languages.ProcessCalculi.PiCalculus.PrenexForm.presented names_context raw typed object
    obtain ⟨witness', valid'⟩ := step_iff_raw.mpr raw'
    obtain ⟨shownTyped, shownObject, -⟩ :=
      replicationPresentations_admitted (block := piRepBlock) names_context
        (canonR_sound (block := piRepBlock) names_context typed).1 (isObject_canonR (block := piRepBlock) object) 2 shown
        presented
    have contractumAdmitted : domain contractum = true := by
      have stepped := PiForms.admissible_of_raw raw (admissible_of_typed typed object)
      exact domain_of_typed stepped.typed stepped.object
    have contractum'Admitted : domain contractum' = true := by
      have stepped := PiForms.admissible_of_raw raw' (admissible_of_typed shownTyped shownObject)
      exact domain_of_typed stepped.typed stepped.object
    refine ⟨shown, ?_, witness', contractum', valid', ?_⟩
    · unfold canon presentations
      rw [if_pos admitted]
      exact presented
    · unfold canon
      rw [if_pos contractum'Admitted, if_pos contractumAdmitted]
      exact canonR_complete (block := piRepBlock) (typed_of_domain contractum'Admitted).2
        (typed_of_domain contractumAdmitted).2
        (restrictionsBind_of_typed (block := piRepBlock) _ (typed_of_domain contractum'Admitted).1) equivalent

/-- **π's canonical forms, as the front door takes them**: in the typed reading, with the unfoldings of replicated
components as the presentations of a state, coherent for plain steps. -/
def forms (fuel : ℕ) : CanonicalForms RelationEnv.empty piCalc fuel where
  reading := reading
  canon := canon
  domain := domain
  canonical := canonical
  presentations := presentations
  labels := plainLabel
  coherent := CoherentPlain.on (coherentPlain fuel)

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiPrenexForms
