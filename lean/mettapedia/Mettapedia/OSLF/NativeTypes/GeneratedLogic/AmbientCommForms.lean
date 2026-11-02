import Mettapedia.Languages.ProcessCalculi.Ambient.ReadComm
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalRegions
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Certificates

/-!
# Mobile ambients with communication and paths, read located

`ambientCommCalc` is the calculus of mobile ambients with communication: capabilities and paths of capabilities, the
capability prefix, and inputs and outputs of names and of capability terms. Its static theory is the bag, the laws of
restriction and replication and the boundary law, together with the laws of paths: `ε.P = P`, `(M.N).P = M.(N.P)`. A
process is equivalent to its path normal form, a process of the same calculus with no path left in a prefix, and the
laws of the calculus relate path normal forms by the laws without paths, which the located calculus reads.

In the typed reading (`reading`: each law between two object terms of one sort, their free variables names of the
name sort):

- **The domain**: object processes with no free bound variable, their free variables names. A typed object has one
  sort, so the reading relates the domain only to the domain (`domain_iff_of_equivalent`).
- **Equivalences of the reading are chains of laws through processes** (`objectChain_of_objectEquivalent`,
  `objectEquivalent_of_objectChain`).
- **Canonical forms** (`canonical`): a process's canonical form is the located canonical form of its path normal form
  at a root location bound outside it, read back (`canonComm`), then put in the canonical form of the restriction and
  replication laws. It is a closed process of the domain equivalent to the process (`canon_facts`), and equivalent
  processes have one (`canonComm_same`).
- **Coherent for plain steps** (`coherentPlain`): a step of a process is matched by a step of its path normal form
  (`AmbCommRawStep.normal`), and that by a step of one of the path normal form's presentations, a communication
  included (`presented_pruned_comm`), to an equivalent contractum. Equivalent processes have path normal forms that
  share their root canonical block, so a state and its canonical form have one list of presentations
  (`presentations_canon`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.AmbientCommForms

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.OSLF.MeTTaIL.ContextualStep (engineBasePremises)
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (BaseContext metadata_of_typed ObjectChain ProcEquiv canonR
  canonR_sound isObject_canonR SortedEquiv.typed_iff equationStep_iff_of_plain)
open Mettapedia.Languages.ProcessCalculi.Ambient.Full (ambientBlock ambientRepBlock ambient_objectChain)
open Mettapedia.Languages.ProcessCalculi.Ambient.Comm (ambientCoreCalc ambientCommCalc coreSignature comm_plain
  comm_terms_core core_terms_comm comm_objectChain canonComm canonComm_facts canonComm_same comm_of_core pathNF
  pathNF_typed isObject_pathNF pathNF_chain AmbCommRawStep commStep_typed)
open Mettapedia.Languages.ProcessCalculi.Ambient.Encoding (NameContext)

/-- **The reading of mobile ambients with communication**: the typed reading, each law between two object terms of
one sort whose free variables are names of the name sort; the rules by the reference relation. -/
def reading : LanguageReading := { equations := .typed .raw .empty .sorts (some "Name") }

/-- The context of the free names. -/
abbrev names : FreeTypeContext := EquationReading.nameContext (some "Name")

theorem names_context : BaseContext names [] :=
  ⟨fun _ _ found => ⟨"Name", by simpa [names, EquationReading.nameContext] using found.symm⟩,
    fun _ member => by simp at member⟩

/-- Every free variable is a name. -/
theorem names_names : NameContext names :=
  ⟨fun _ _ found => by simpa [names, EquationReading.nameContext] using found.symm⟩

/-- A process of the calculus with communication is a process of its core: the two have the same constructors. -/
theorem core_typed {free : FreeTypeContext} {bound : List TypeExpr} {term : Pattern} {type : TypeExpr}
    (typed : HasType ambientCommCalc free bound term type) : HasType ambientCoreCalc free bound term type :=
  typed.of_terms_subset comm_terms_core

theorem comm_typed {free : FreeTypeContext} {bound : List TypeExpr} {term : Pattern} {type : TypeExpr}
    (typed : HasType ambientCoreCalc free bound term type) : HasType ambientCommCalc free bound term type :=
  typed.of_terms_subset core_terms_comm

/-- **Object processes with no free bound variable**, their free variables names. -/
def domain (term : Pattern) : Bool :=
  Mettapedia.GSLT.LanguageDef.WellSorted.checkOpenPatternWellSorted ambientCommCalc names [] (.base "Proc") term

theorem typed_of_domain {term : Pattern} (admitted : domain term = true) :
    HasType ambientCommCalc names [] term (.base "Proc") ∧ isObjectPattern term = true := by
  unfold domain at admitted
  rw [checkOpenPatternWellSorted_eq_true_iff] at admitted
  exact ⟨admitted.1, admitted.2.2.1⟩

theorem domain_of_typed {term : Pattern} (typed : HasType ambientCommCalc names [] term (.base "Proc"))
    (object : isObjectPattern term = true) : domain term = true := by
  unfold domain
  rw [checkOpenPatternWellSorted_eq_true_iff]
  exact ⟨typed, (metadata_of_typed (block := ambientBlock) _ (core_typed typed) object).1 ⟨_, rfl⟩, object,
    by simpa [ScopeSafeAt] using typed.isWellScopedAt⟩

/-- **A typed object has one sort**: a free name has the name sort, and a constructor makes terms of its own sort. -/
theorem sort_unique {term : Pattern} {first second : String}
    (firstTyped : HasType ambientCommCalc names [] term (.base first))
    (secondTyped : HasType ambientCommCalc names [] term (.base second)) (object : isObjectPattern term = true) :
    first = second := by
  have firstCore := core_typed firstTyped
  have secondCore := core_typed secondTyped
  have firstCopy := firstCore
  cases firstCore with
  | bvar lookup => simp at lookup
  | fvar lookup =>
      cases secondCore with
      | fvar lookup' =>
          simp only [names, EquationReading.nameContext, Option.some.injEq, TypeExpr.base.injEq] at lookup lookup'
          exact lookup.symm.trans lookup'
  | constructor member =>
      obtain ⟨rule', member', labelIs, -, typeIs, -⟩ := hasType_apply_inversion secondCore
      simp only [TypeExpr.base.injEq] at typeIs
      rw [typeIs, coreSignature.rule_eq_of_label member member' labelIs]
  | subst => simp [isObjectPattern] at object
  | collectionConstructor =>
      exact (coreSignature.bag_members firstCopy).2.1.trans (coreSignature.bag_members secondCore).2.1.symm

/-- **A step of the reading relates the domain only to the domain**, both ways. -/
theorem domain_iff_of_step {relEnv : RelationEnv} {first second : Pattern}
    (step : ObjectStep relEnv ambientCommCalc reading first second) : domain first = true ↔ domain second = true := by
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
    (equivalent : ObjectEquivalent relEnv ambientCommCalc reading first second) :
    domain first = true ↔ domain second = true := by
  induction equivalent with
  | rel _ _ step => exact domain_iff_of_step step
  | refl => exact Iff.rfl
  | symm _ _ _ same => exact same.symm
  | trans _ _ _ _ _ first second => exact first.trans second

/-- **An equivalence of the reading from a process of the domain is a chain of laws through processes.** -/
theorem objectChain_of_objectEquivalent {relEnv : RelationEnv} {first second : Pattern}
    (equivalent : ObjectEquivalent relEnv ambientCommCalc reading first second) (admitted : domain first = true) :
    ObjectChain ambientCommCalc names [] (.base "Proc") first second := by
  induction equivalent with
  | rel first second step =>
      obtain ⟨-, -, type, ⟨sort, rfl⟩, firstFormed, secondFormed, disciplined⟩ := step
      obtain ⟨typed, object⟩ := typed_of_domain admitted
      obtain rfl := sort_unique firstFormed.typed typed object
      exact .rel _ _ ⟨⟨(equationStep_iff_of_plain comm_plain relEnv _).mp (disciplinedStep_raw_iff.mp disciplined),
        firstFormed.typed, secondFormed.typed⟩, firstFormed.object, secondFormed.object⟩
  | refl => exact .refl _
  | symm _ _ inner recurse =>
      exact .symm _ _ (recurse ((domain_iff_of_equivalent inner).mpr admitted))
  | trans _ _ _ firstPart _ firstRecurse secondRecurse =>
      exact .trans _ _ _ (firstRecurse admitted) (secondRecurse ((domain_iff_of_equivalent firstPart).mp admitted))

/-- **A chain of laws through object processes is an equivalence of the reading.** -/
theorem objectEquivalent_of_objectChain (relEnv : RelationEnv) {first second : Pattern}
    (chain : ObjectChain ambientCommCalc names [] (.base "Proc") first second) :
    ObjectEquivalent relEnv ambientCommCalc reading first second := by
  induction chain with
  | rel first second step =>
      obtain ⟨step, firstObject, secondObject⟩ := step
      exact .rel _ _ ⟨firstObject, secondObject, .base "Proc", ⟨"Proc", rfl⟩,
        ⟨firstObject, step.firstTyped, by simp⟩, ⟨secondObject, step.secondTyped, by simp⟩,
        disciplinedStep_raw_iff.mpr ((equationStep_iff_of_plain comm_plain relEnv _).mpr step.step)⟩
  | refl => exact .refl _
  | symm _ _ _ recurse => exact .symm _ _ recurse
  | trans _ _ _ _ _ left right => exact .trans _ _ _ left right

/-- **The canonical form of a process of the domain**: the located canonical form of its path normal form at a root
location, read back, in the canonical form of the restriction and replication laws. -/
def canon (term : Pattern) : Pattern :=
  if domain term then canonR ambientRepBlock (canonComm term) else term

/-- **The canonical form of a process of the domain is a closed object process equivalent to it.** -/
theorem canon_facts {term : Pattern} (admitted : domain term = true) :
    HasType ambientCommCalc names [] (canon term) (.base "Proc") ∧ isObjectPattern (canon term) = true ∧
      ProcEquiv ambientCommCalc ambientBlock names [] term (canon term) := by
  obtain ⟨typed, object⟩ := typed_of_domain admitted
  obtain ⟨readTyped, readObject, readEquivalent⟩ := canonComm_facts names_names typed object
  obtain ⟨canonTyped, canonEquivalent⟩ := canonR_sound (block := ambientRepBlock) names_context (core_typed readTyped)
  unfold canon
  rw [if_pos admitted]
  exact ⟨comm_typed canonTyped, isObject_canonR (block := ambientRepBlock) readObject,
    .trans _ _ _ readEquivalent (comm_of_core canonEquivalent)⟩

/-- **The located canonical form of the path normal form read back gives canonical forms** on closed object
processes, in the typed reading. -/
theorem canonical (relEnv : RelationEnv) : Canonical relEnv ambientCommCalc canon domain reading where
  object admitted := (typed_of_domain admitted).2
  admitted_canon {term} admitted := by
    obtain ⟨canonTyped, canonObject, -⟩ := canon_facts admitted
    exact domain_of_typed canonTyped canonObject
  invariant admitted equivalent := (domain_iff_of_equivalent equivalent).mp admitted
  stepsAdmitted {redex witness contractum} _ _ _ canonAdmitted := by
    by_contra notAdmitted
    unfold canon at canonAdmitted
    rw [if_neg notAdmitted] at canonAdmitted
    exact notAdmitted canonAdmitted
  equivalent {term} admitted := by
    obtain ⟨-, object⟩ := typed_of_domain admitted
    obtain ⟨-, canonObject, equivalent⟩ := canon_facts admitted
    exact objectEquivalent_of_objectChain relEnv (comm_objectChain names_context equivalent object canonObject)
  same {first second} admitted equivalent := by
    have secondAdmitted := (domain_iff_of_equivalent equivalent).mp admitted
    obtain ⟨firstTyped, firstObject⟩ := typed_of_domain admitted
    obtain ⟨secondTyped, secondObject⟩ := typed_of_domain secondAdmitted
    unfold canon
    rw [if_pos admitted, if_pos secondAdmitted]
    exact congrArg (canonR ambientRepBlock) (canonComm_same names_names names_context firstTyped firstObject
      secondTyped secondObject (objectChain_of_objectEquivalent equivalent admitted))
  closed {term} admitted := by
    obtain ⟨typed, -⟩ := typed_of_domain admitted
    obtain ⟨canonTyped, -, -⟩ := canon_facts admitted
    have before := typed.isWellScopedAt
    have after := canonTyped.isWellScopedAt
    simp only [List.length_nil] at before after
    rw [before, after]

/-! ## Coherence -/

open Mettapedia.Languages.ProcessCalculi.Ambient.Located (locatedRepBlock)
open Mettapedia.Languages.ProcessCalculi.Ambient.Decoding (rootForm rootForm_same)
open Mettapedia.Languages.ProcessCalculi.Ambient.Steps (presentationsA presented_pruned_comm pruneTop pruneTop_facts
  presentation_facts)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (presentationDepth)

/-- **The presentations of a state**: the unfoldings of the root canonical block of its path normal form within the
presentation depth, each presented without its unused outermost restrictions. -/
def presentations (state : Pattern) : List Pattern :=
  (presentationsA (presentationDepth locatedRepBlock 3 (rootForm (pathNF state))) (pathNF state)).map pruneTop

theorem profile : ReferenceProfile ambientCommCalc := profile_of_aligned (by decide)

/-- The reference steps of `ambientCommCalc` are the steps of its specification. -/
theorem step_iff_raw {source target : Pattern} :
    (∃ witness, StepValid RelationEnv.empty ambientCommCalc source witness target) ↔ AmbCommRawStep source target :=
  (contextualStep_iff_step RelationEnv.empty ambientCommCalc profile).symm.trans
    (Mettapedia.Languages.ProcessCalculi.Ambient.Comm.step_iff_raw source target)

/-- **A process and its canonical form have one list of presentations**: both are read off the root canonical block
of a path normal form, which equivalent processes share. -/
theorem presentations_canon {term : Pattern} (admitted : domain term = true) :
    presentations (canon term) = presentations term := by
  obtain ⟨typed, object⟩ := typed_of_domain admitted
  obtain ⟨canonTyped, canonObject, equivalent⟩ := canon_facts admitted
  have normalEquivalent := pathNF_chain names_context
    (comm_objectChain names_context (.symm _ _ equivalent) canonObject object)
  have same := rootForm_same names_names (pathNF_typed (core_typed canonTyped) canonObject)
    (isObject_pathNF _ canonObject) (pathNF_typed (core_typed typed) object) (isObject_pathNF _ object)
    (ambient_objectChain names_context normalEquivalent (isObject_pathNF _ canonObject) (isObject_pathNF _ object))
  unfold presentations presentationsA
  rw [same]

/-- **A firing is matched at a presentation**: a firing of a process is matched, up to the canonical form, by a firing
of one of the presentations of its canonical form. -/
theorem presented_simulation {redex contractum : Pattern} (admitted : domain redex = true)
    (raw : AmbCommRawStep redex contractum) :
    ∃ shown ∈ presentations (canon redex), ∃ contractum', AmbCommRawStep shown contractum' ∧
      canon contractum' = canon contractum := by
  obtain ⟨typed, object⟩ := typed_of_domain admitted
  -- the step of the path normal form, and of one of its presentations
  obtain ⟨target', normalStep, normalEquivalent⟩ :=
    Mettapedia.Languages.ProcessCalculi.Ambient.Comm.AmbCommRawStep.normal raw names_context (core_typed typed)
      object
  have normalTyped := pathNF_typed (core_typed typed) object
  have normalObject := isObject_pathNF _ object
  obtain ⟨shown, shownIn, contractum', raw', equivalent⟩ :=
    presented_pruned_comm names_names normalStep normalTyped normalObject
  obtain ⟨unpruned, unprunedIn, rfl⟩ := List.mem_map.mp shownIn
  obtain ⟨unprunedTyped, unprunedObject, -⟩ :=
    presentation_facts names_names normalTyped normalObject _ unpruned unprunedIn
  obtain ⟨shownTyped, shownObject, -⟩ := pruneTop_facts unpruned unprunedTyped unprunedObject
  obtain ⟨contractumTyped, contractumObject⟩ := commStep_typed raw (core_typed typed) object
  obtain ⟨contractum'Typed, contractum'Object⟩ := commStep_typed raw' shownTyped shownObject
  refine ⟨pruneTop unpruned, ?_, contractum', raw', ?_⟩
  · rw [presentations_canon admitted]
    exact shownIn
  · unfold canon
    rw [if_pos (domain_of_typed (comm_typed contractum'Typed) contractum'Object),
      if_pos (domain_of_typed (comm_typed contractumTyped) contractumObject)]
    exact congrArg (canonR ambientRepBlock) (canonComm_same names_names names_context
      (comm_typed contractum'Typed) contractum'Object (comm_typed contractumTyped) contractumObject
      (comm_objectChain names_context (.trans _ _ _ (comm_of_core equivalent) normalEquivalent)
        contractum'Object contractumObject))

/-- **Coherence for plain steps**: a step from any process equivalent to a canonical one is matched, up to canonical
form, by a step listed at a presentation of it, wherever the fuel lists their steps. -/
theorem coherentPlain (fuel : ℕ) :
    CoherentPlain RelationEnv.empty ambientCommCalc fuel canon domain presentations reading :=
  coherentPlain_of_presented_simulation (canonical RelationEnv.empty)
    fun {redex witness contractum} _ admitted valid => by
      obtain ⟨shown, shownIn, contractum', raw', same⟩ := presented_simulation admitted (step_iff_raw.mp ⟨witness, valid⟩)
      obtain ⟨witness', valid'⟩ := step_iff_raw.mpr raw'
      exact ⟨shown, shownIn, witness', contractum', valid', same⟩

/-- **The canonical forms of ambients with communication and paths, as the front door takes them**: in the typed
reading, steps listed at the presentations of a state's path normal form, coherent for plain steps. -/
def forms (fuel : ℕ) : CanonicalForms RelationEnv.empty ambientCommCalc fuel where
  reading := reading
  canon := canon
  domain := domain
  canonical := canonical RelationEnv.empty
  presentations := presentations
  labels := plainLabel
  coherent := CoherentPlain.on (coherentPlain fuel)

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.AmbientCommForms
