import Mettapedia.Languages.ProcessCalculi.CCS.ReplicatedSteps
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationObjects
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalRegions
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Certificates

/-!
# Canonical forms for CCS with replication

`ccsRepCalc`'s static theory is its bag and the multisets of its sums together with ν of inaction, exchange of
restrictions, scope extrusion, the empty sum and the laws of replication. Its canonical form (the replication theory's
at CCS's blocks) decides that theory on object processes, and here it becomes the canonical forms the front door
takes, in the typed reading (`reading`: each law between two object terms of one sort, their free variables names of
the name sort):

- **The domain**: object processes with no free bound variable, their free variables names. A typed object has one
  sort (`sort_unique`), so the reading relates the domain only to the domain.
- **Equivalent to the canonical form, through processes**: soundness gives a chain of laws, and every chain of laws
  between object processes runs through object processes (`objectEquivalent_of_equationEquiv`).
- **Same canonical form**: completeness, since the typed reading is part of the static theory.
- **Coherent for plain steps**: a step of a process is matched by a step of a presentation of its canonical form, an
  unfolding of its replicated components, to a contractum with the same canonical form
  (`ReplicatedSteps.presented`). Every presentation is a process with that canonical form.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.CCSRepForms

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.OSLF.MeTTaIL.ContextualStep (engineBasePremises)
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationEquiv)
open Mettapedia.GSLT.LanguageDef.BagNormalForm (Admissible)
open Mettapedia.Languages.ProcessCalculi.CCS (CCSRawStep)
open Mettapedia.Languages.ProcessCalculi.CCS.Replicated (ccsRepCalc ccsRepBlock ccsRepReplicationLanguage
  ccsRepBlockSignature)
open Mettapedia.Languages.ProcessCalculi.CCS.Blocks (ccsBlock)
open Mettapedia.Languages.ProcessCalculi.CCS.ReplicatedSteps (typed_of_raw)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (BaseContext SortedEquiv ProcEquiv canonR canonR_sound
  canonR_complete metadata_of_typed equationStep_iff_replication restrictionsBind_of_typed isObject_canonR
  replicationPresentations replicationPresentations_admitted ObjectChain objectChain_of_equationEquiv)

/-- **The reading of CCS with replication**: the typed reading, each law between two object terms of one sort whose
free variables are names of the name sort; the rules by the reference relation. -/
def reading : LanguageReading := { equations := .typed .raw .empty .sorts (some "Name") }

/-- The context of the free names. -/
abbrev names : FreeTypeContext := EquationReading.nameContext (some "Name")

theorem names_context : BaseContext names [] :=
  ⟨fun _ _ found => ⟨"Name", by simpa [names, EquationReading.nameContext] using found.symm⟩,
    fun _ member => by simp at member⟩

/-- **Object processes with no free bound variable**, their free variables names. -/
def domain (term : Pattern) : Bool :=
  Mettapedia.GSLT.LanguageDef.WellSorted.checkOpenPatternWellSorted ccsRepCalc names [] (.base "Proc") term

/-- **The canonical form**: the canonical form with replication on the domain, the term itself elsewhere. -/
def canon (term : Pattern) : Pattern :=
  if domain term then canonR ccsRepBlock term else term

/-- **The presentations of a state**: its unfoldings within the presentation depth of its canonical block, the
redexes having two parts. -/
def presentations (state : Pattern) : List Pattern := replicationPresentations ccsRepBlock 2 state

theorem typed_of_domain {term : Pattern} (admitted : domain term = true) :
    HasType ccsRepCalc names [] term (.base "Proc") ∧ isObjectPattern term = true := by
  unfold domain at admitted
  rw [checkOpenPatternWellSorted_eq_true_iff] at admitted
  exact ⟨admitted.1, admitted.2.2.1⟩

theorem domain_of_typed {term : Pattern} (typed : HasType ccsRepCalc names [] term (.base "Proc"))
    (object : isObjectPattern term = true) : domain term = true := by
  unfold domain
  rw [checkOpenPatternWellSorted_eq_true_iff]
  exact ⟨typed, (metadata_of_typed (block := ccsBlock) _ typed object).1 ⟨_, rfl⟩, object,
    by simpa [ScopeSafeAt] using typed.isWellScopedAt⟩

/-- **A typed object has one sort**: a free name has the name sort, and a constructor makes terms of its own sort. -/
theorem sort_unique {term : Pattern} {first second : String} (firstTyped : HasType ccsRepCalc names [] term (.base first))
    (secondTyped : HasType ccsRepCalc names [] term (.base second)) (object : isObjectPattern term = true) :
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
      rw [typeIs, ccsRepBlockSignature.rule_eq_of_label member member' labelIs]
  | subst => simp [isObjectPattern] at object
  | collectionConstructor =>
      exact (ccsRepBlockSignature.bag_members firstCopy).2.1.trans (ccsRepBlockSignature.bag_members secondTyped).2.1.symm

/-- **A step of the reading relates the domain only to the domain**, both ways. -/
theorem domain_iff_of_step {relEnv : RelationEnv} {first second : Pattern}
    (step : ObjectStep relEnv ccsRepCalc reading first second) : domain first = true ↔ domain second = true := by
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
    (equivalent : ObjectEquivalent relEnv ccsRepCalc reading first second) : domain first = true ↔ domain second = true := by
  induction equivalent with
  | rel _ _ step => exact domain_iff_of_step step
  | refl => exact Iff.rfl
  | symm _ _ _ same => exact same.symm
  | trans _ _ _ _ _ first second => exact first.trans second

/-- **A chain of laws through object processes is an equivalence of the reading.** -/
theorem objectEquivalent_of_objectChain (relEnv : RelationEnv) {first second : Pattern}
    (chain : ObjectChain ccsRepCalc names [] (.base "Proc") first second) :
    ObjectEquivalent relEnv ccsRepCalc reading first second := by
  induction chain with
  | rel first second step =>
      obtain ⟨step, firstObject, secondObject⟩ := step
      exact .rel _ _ ⟨firstObject, secondObject, .base "Proc", ⟨"Proc", rfl⟩,
        ⟨firstObject, step.firstTyped, by simp⟩, ⟨secondObject, step.secondTyped, by simp⟩,
        disciplinedStep_raw_iff.mpr ((equationStep_iff_replication (block := ccsRepBlock) relEnv _).mpr step.step)⟩
  | refl => exact .refl _
  | symm _ _ _ recurse => exact .symm _ _ recurse
  | trans _ _ _ _ _ left right => exact .trans _ _ _ left right

/-- **Equivalent object processes are equivalent in the reading**: a chain of laws between them, read through its
object reading, passes through object processes only. -/
theorem objectEquivalent_of_equationEquiv (relEnv : RelationEnv) {first second : Pattern}
    (firstTyped : HasType ccsRepCalc names [] first (.base "Proc"))
    (secondTyped : HasType ccsRepCalc names [] second (.base "Proc"))
    (firstObject : isObjectPattern first = true) (secondObject : isObjectPattern second = true)
    (equivalent : EquationEquiv (engineBasePremises RelationEnv.empty) ccsRepCalc first second) :
    ObjectEquivalent relEnv ccsRepCalc reading first second :=
  objectEquivalent_of_objectChain relEnv (objectChain_of_equationEquiv (block := ccsRepBlock) names_context firstTyped
    secondTyped firstObject secondObject equivalent)

/-- **Every reading's equivalence is part of the static theory.** -/
theorem equationEquiv_of_objectEquivalent {relEnv : RelationEnv} {anyReading : LanguageReading} {first second : Pattern}
    (equivalent : ObjectEquivalent relEnv ccsRepCalc anyReading first second) :
    EquationEquiv (engineBasePremises RelationEnv.empty) ccsRepCalc first second :=
  Relation.EqvGen.mono (fun _ _ step => (equationStep_iff_replication (block := ccsRepBlock) relEnv _).mp step) _ _
    equivalent.equivalent

theorem profile : ReferenceProfile ccsRepCalc := profile_of_aligned (by decide)

/-- The reference steps of `ccsRepCalc` are the steps of its occurrence specification. -/
theorem step_iff_raw {source target : Pattern} :
    (∃ witness, StepValid RelationEnv.empty ccsRepCalc source witness target) ↔ CCSRawStep source target :=
  (contextualStep_iff_step RelationEnv.empty ccsRepCalc profile).symm.trans
    (Mettapedia.Languages.ProcessCalculi.CCS.ReplicatedSteps.step_iff_raw source target)

theorem admissible_of_typed {term : Pattern} (typed : HasType ccsRepCalc names [] term (.base "Proc"))
    (object : isObjectPattern term = true) : Admissible ccsRepCalc names [] (.base "Proc") term :=
  ⟨typed, (metadata_of_typed (block := ccsBlock) _ typed object).1 ⟨_, rfl⟩, object⟩

/-- **The canonical form with replication gives canonical forms** on closed object processes, in the typed
reading. -/
theorem canonical : Canonical RelationEnv.empty ccsRepCalc canon domain reading where
  object admitted := (typed_of_domain admitted).2
  admitted_canon {term} admitted := by
    obtain ⟨typed, object⟩ := typed_of_domain admitted
    unfold canon
    rw [if_pos admitted]
    exact domain_of_typed (canonR_sound (block := ccsRepBlock) names_context typed).1
      (isObject_canonR (block := ccsRepBlock) object)
  invariant admitted equivalent := (domain_iff_of_equivalent equivalent).mp admitted
  stepsAdmitted {redex witness contractum} admitted _ valid _ := by
    obtain ⟨typed, object⟩ := typed_of_domain admitted
    have raw := (step_iff_raw (source := redex) (target := contractum)).mp ⟨witness, valid⟩
    obtain ⟨steppedTyped, steppedObject⟩ := typed_of_raw raw typed object
    exact domain_of_typed steppedTyped steppedObject
  equivalent {term} admitted := by
    obtain ⟨typed, object⟩ := typed_of_domain admitted
    obtain ⟨canonTyped, equivalent⟩ := canonR_sound (block := ccsRepBlock) names_context typed
    unfold canon
    rw [if_pos admitted]
    exact objectEquivalent_of_equationEquiv RelationEnv.empty typed canonTyped object
      (isObject_canonR (block := ccsRepBlock) object) equivalent.toEquationEquiv
  same {first second} admitted equivalent := by
    have secondAdmitted := (domain_iff_of_equivalent equivalent).mp admitted
    obtain ⟨firstTyped, firstObject⟩ := typed_of_domain admitted
    obtain ⟨-, secondObject⟩ := typed_of_domain secondAdmitted
    unfold canon
    rw [if_pos admitted, if_pos secondAdmitted]
    exact canonR_complete (block := ccsRepBlock) firstObject secondObject
      (restrictionsBind_of_typed (block := ccsRepBlock) first firstTyped) (equationEquiv_of_objectEquivalent equivalent)
  closed {term} admitted := by
    obtain ⟨typed, object⟩ := typed_of_domain admitted
    unfold canon
    rw [if_pos admitted]
    have before := typed.isWellScopedAt
    have after := (canonR_sound (block := ccsRepBlock) names_context typed).1.isWellScopedAt
    simp only [List.length_nil] at before after
    rw [before, after]

/-- **A presentation of a process's canonical form is a process with that canonical form.** -/
theorem presentation_process {state shown : Pattern} (stateIn : domain state = true)
    (presented : shown ∈ presentations (canon state)) : domain shown = true ∧ canon shown = canon state := by
  obtain ⟨typed, object⟩ := typed_of_domain stateIn
  obtain ⟨canonTyped, canonEquivalent⟩ := canonR_sound (block := ccsRepBlock) names_context typed
  have canonObject := isObject_canonR (block := ccsRepBlock) object
  unfold canon at presented ⊢
  rw [if_pos stateIn] at presented ⊢
  obtain ⟨shownTyped, shownObject, shownCanon⟩ :=
    replicationPresentations_admitted (block := ccsRepBlock) names_context canonTyped canonObject 2 shown presented
  have shownIn := domain_of_typed shownTyped shownObject
  refine ⟨shownIn, ?_⟩
  rw [if_pos shownIn, shownCanon]
  exact canonR_complete (block := ccsRepBlock) (base := engineBasePremises RelationEnv.empty) canonObject object
    (restrictionsBind_of_typed (block := ccsRepBlock) _ canonTyped)
    (Relation.EqvGen.symm _ _ canonEquivalent.toEquationEquiv)

/-- **Coherence for plain steps**: a step from any process equivalent to a canonical one is matched, up to canonical
form, by a step listed at a presentation of it, wherever the fuel lists their steps. -/
theorem coherentPlain (fuel : ℕ) :
    CoherentPlain RelationEnv.empty ccsRepCalc fuel canon domain presentations reading :=
  coherentPlain_of_presented_simulation canonical fun {redex witness contractum} _ admitted valid => by
    obtain ⟨typed, object⟩ := typed_of_domain admitted
    have raw := step_iff_raw.mp ⟨witness, valid⟩
    obtain ⟨shown, presented, contractum', raw', equivalent⟩ :=
      Mettapedia.Languages.ProcessCalculi.CCS.ReplicatedSteps.presented names_context raw typed object
    obtain ⟨witness', valid'⟩ := step_iff_raw.mpr raw'
    obtain ⟨shownTyped, shownObject, -⟩ :=
      replicationPresentations_admitted (block := ccsRepBlock) names_context
        (canonR_sound (block := ccsRepBlock) names_context typed).1 (isObject_canonR (block := ccsRepBlock) object) 2 shown
        presented
    have contractumAdmitted : domain contractum = true := by
      obtain ⟨steppedTyped, steppedObject⟩ := typed_of_raw raw typed object
      exact domain_of_typed steppedTyped steppedObject
    have contractum'Admitted : domain contractum' = true := by
      obtain ⟨steppedTyped, steppedObject⟩ := typed_of_raw raw' shownTyped shownObject
      exact domain_of_typed steppedTyped steppedObject
    refine ⟨shown, ?_, witness', contractum', valid', ?_⟩
    · unfold canon presentations
      rw [if_pos admitted]
      exact presented
    · unfold canon
      rw [if_pos contractum'Admitted, if_pos contractumAdmitted]
      exact canonR_complete (block := ccsRepBlock) (typed_of_domain contractum'Admitted).2
        (typed_of_domain contractumAdmitted).2
        (restrictionsBind_of_typed (block := ccsRepBlock) _ (typed_of_domain contractum'Admitted).1) equivalent

/-- **The canonical forms of CCS with replication, as the front door takes them**: in the typed reading, with the
unfoldings of replicated components as the presentations of a state, coherent for plain steps. -/
def forms (fuel : ℕ) : CanonicalForms RelationEnv.empty ccsRepCalc fuel where
  reading := reading
  canon := canon
  domain := domain
  canonical := canonical
  presentations := presentations
  labels := plainLabel
  coherent := CoherentPlain.on (coherentPlain fuel)

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.CCSRepForms
