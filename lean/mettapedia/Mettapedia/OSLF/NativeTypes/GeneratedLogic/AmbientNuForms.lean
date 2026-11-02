import Mettapedia.Languages.ProcessCalculi.Ambient.ReadCanon
import Mettapedia.Languages.ProcessCalculi.Ambient.Pure
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalRegions
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Certificates

/-!
# Mobile ambients with restriction, read located

`ambientNuCalc`'s static theory is its bag together with the laws of restriction, the laws of replication and the
boundary law: a restriction crosses an ambient it does not name. Its processes are processes of the core of the
calculus with communication, which has the same laws and adds only constructors of communication; the core's laws keep
a pure process pure, so a chain of laws of the core from a pure process is a chain of the pure calculus. The core's
processes are read in the located calculus, a flat calculus whose static theory is the restriction-block theory with
replication; there the boundary law is scope extrusion and exchange of the ambient's location.

In the typed reading (`reading`: each law between two object terms of one sort, their free variables names of the
name sort):

- **The domain**: object processes with no free bound variable, their free variables names. A typed object has one
  sort (`sort_unique`), so the reading relates the domain only to the domain (`domain_iff_of_equivalent`).
- **Equivalences of the reading are chains of laws through processes**: every equivalence of the reading from the
  domain is one (`objectChain_of_objectEquivalent`), and every chain of laws between object processes passes through
  object processes, an equivalence of the reading (`objectEquivalent_of_objectChain`).
- **Canonical forms** (`canonical`): a process's canonical form is its located canonical form at a root location
  bound outside it, read back (`canonA`), then put in the canonical form of the ambient calculus's own restriction
  and replication laws, which drops the restrictions the read-back keeps for locations and never uses. It is a closed
  process of the domain, equivalent to the process (`canon_facts`), and equivalent processes have one, since the
  located form carries a chain of laws to a chain of laws of the located calculus, which its canonical form decides.
- **Coherent for plain steps** (`coherentPlain`): a step of a process is matched by a step of one of its presentations
  (`presented_pruned`), to an equivalent contractum. The presentations of a state are the unfoldings of its root
  canonical block within three times the block's ceiling, an ambient redex having three parts, each read back at the
  root with every ambient's content a bag and without its unused outermost restrictions; equivalent processes share
  their root canonical block, so a state and its canonical form have one list of presentations
  (`presentations_canon`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.AmbientNuForms

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.OSLF.MeTTaIL.ContextualStep (engineBasePremises)
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (BaseContext metadata_of_typed ObjectChain ProcEquiv canonR
  canonR_sound isObject_canonR SortedEquiv.typed_iff SortedEquiv.avoids_iff equationStep_iff_of_plain)
open Mettapedia.Languages.ProcessCalculi.Ambient.Full (ambientNuCalc ambientBlock ambientRepBlock ambient_plain
  ambient_objectChain)
open Mettapedia.Languages.ProcessCalculi.Ambient.Comm (ambientCoreCalc coreSignature)
open Mettapedia.Languages.ProcessCalculi.Ambient.Pure (coreExtension coreKeeps AmbNuRawStep.avoids)
open Mettapedia.Languages.ProcessCalculi.Ambient.Encoding (NameContext)
open Mettapedia.Languages.ProcessCalculi.Ambient.Decoding (canonA canonA_facts canonA_same)

/-- **The reading of mobile ambients**: the typed reading, each law between two object terms of one sort whose free
variables are names of the name sort; the rules by the reference relation. -/
def reading : LanguageReading := { equations := .typed .raw .empty .sorts (some "Name") }

/-- The context of the free names. -/
abbrev names : FreeTypeContext := EquationReading.nameContext (some "Name")

theorem names_context : BaseContext names [] :=
  ⟨fun _ _ found => ⟨"Name", by simpa [names, EquationReading.nameContext] using found.symm⟩,
    fun _ member => by simp at member⟩

/-- Every free variable is a name. -/
theorem names_names : NameContext names :=
  ⟨fun _ _ found => by simpa [names, EquationReading.nameContext] using found.symm⟩

/-- A process of the pure calculus is a process of the core. -/
theorem core_typed {free : FreeTypeContext} {bound : List TypeExpr} {term : Pattern} {type : TypeExpr}
    (typed : HasType ambientNuCalc free bound term type) : HasType ambientCoreCalc free bound term type :=
  typed.of_terms_subset coreExtension.terms

/-- **A chain of laws of the core from a pure process is a chain of the pure calculus**, to a pure process. -/
theorem pure_equiv {free : FreeTypeContext} {bound : List TypeExpr} {first second : Pattern}
    (equivalent : ProcEquiv ambientCoreCalc ambientBlock free bound first second)
    (typed : HasType ambientNuCalc free bound first (.base "Proc")) :
    HasType ambientNuCalc free bound second (.base "Proc") ∧ ProcEquiv ambientNuCalc ambientBlock free bound first second := by
  have pure := coreExtension.sortedEquiv_restrict (coreKeeps _) equivalent (coreExtension.avoids_of_typed typed)
  exact ⟨(SortedEquiv.typed_iff pure).mp typed, pure⟩

/-- **A chain of laws of the pure calculus between object processes passes through object processes.** -/
theorem pure_objectChain {first second : Pattern} (equivalent : ProcEquiv ambientNuCalc ambientBlock names [] first second)
    (typed : HasType ambientNuCalc names [] first (.base "Proc")) (firstObject : isObjectPattern first = true)
    (secondObject : isObjectPattern second = true) : ObjectChain ambientNuCalc names [] (.base "Proc") first second :=
  coreExtension.objectChain_restrict (coreKeeps _)
    (ambient_objectChain names_context (coreExtension.sortedEquiv_extend equivalent) firstObject secondObject)
    (coreExtension.avoids_of_typed typed)

/-- **Object processes with no free bound variable**, their free variables names. -/
def domain (term : Pattern) : Bool :=
  Mettapedia.GSLT.LanguageDef.WellSorted.checkOpenPatternWellSorted ambientNuCalc names [] (.base "Proc") term

theorem typed_of_domain {term : Pattern} (admitted : domain term = true) :
    HasType ambientNuCalc names [] term (.base "Proc") ∧ isObjectPattern term = true := by
  unfold domain at admitted
  rw [checkOpenPatternWellSorted_eq_true_iff] at admitted
  exact ⟨admitted.1, admitted.2.2.1⟩

theorem domain_of_typed {term : Pattern} (typed : HasType ambientNuCalc names [] term (.base "Proc"))
    (object : isObjectPattern term = true) : domain term = true := by
  unfold domain
  rw [checkOpenPatternWellSorted_eq_true_iff]
  exact ⟨typed, (metadata_of_typed (block := ambientBlock) _ (core_typed typed) object).1 ⟨_, rfl⟩, object,
    by simpa [ScopeSafeAt] using typed.isWellScopedAt⟩

/-- **A typed object has one sort**: a free name has the name sort, and a constructor makes terms of its own sort. -/
theorem sort_unique {term : Pattern} {first second : String}
    (firstTyped : HasType ambientNuCalc names [] term (.base first))
    (secondTyped : HasType ambientNuCalc names [] term (.base second)) (object : isObjectPattern term = true) :
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
    (step : ObjectStep relEnv ambientNuCalc reading first second) : domain first = true ↔ domain second = true := by
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
    (equivalent : ObjectEquivalent relEnv ambientNuCalc reading first second) :
    domain first = true ↔ domain second = true := by
  induction equivalent with
  | rel _ _ step => exact domain_iff_of_step step
  | refl => exact Iff.rfl
  | symm _ _ _ same => exact same.symm
  | trans _ _ _ _ _ first second => exact first.trans second

/-- **An equivalence of the reading from a process of the domain is a chain of laws through processes.** -/
theorem objectChain_of_objectEquivalent {relEnv : RelationEnv} {first second : Pattern}
    (equivalent : ObjectEquivalent relEnv ambientNuCalc reading first second) (admitted : domain first = true) :
    ObjectChain ambientNuCalc names [] (.base "Proc") first second := by
  induction equivalent with
  | rel first second step =>
      obtain ⟨-, -, type, ⟨sort, rfl⟩, firstFormed, secondFormed, disciplined⟩ := step
      obtain ⟨typed, object⟩ := typed_of_domain admitted
      obtain rfl := sort_unique firstFormed.typed typed object
      exact .rel _ _ ⟨⟨(equationStep_iff_of_plain (ambient_plain (language := ambientNuCalc) rfl) relEnv _).mp (disciplinedStep_raw_iff.mp disciplined),
        firstFormed.typed, secondFormed.typed⟩, firstFormed.object, secondFormed.object⟩
  | refl => exact .refl _
  | symm _ _ inner recurse =>
      exact .symm _ _ (recurse ((domain_iff_of_equivalent inner).mpr admitted))
  | trans _ _ _ firstPart _ firstRecurse secondRecurse =>
      exact .trans _ _ _ (firstRecurse admitted) (secondRecurse ((domain_iff_of_equivalent firstPart).mp admitted))

/-- **A chain of laws through object processes is an equivalence of the reading.** -/
theorem objectEquivalent_of_objectChain (relEnv : RelationEnv) {first second : Pattern}
    (chain : ObjectChain ambientNuCalc names [] (.base "Proc") first second) :
    ObjectEquivalent relEnv ambientNuCalc reading first second := by
  induction chain with
  | rel first second step =>
      obtain ⟨step, firstObject, secondObject⟩ := step
      exact .rel _ _ ⟨firstObject, secondObject, .base "Proc", ⟨"Proc", rfl⟩,
        ⟨firstObject, step.firstTyped, by simp⟩, ⟨secondObject, step.secondTyped, by simp⟩,
        disciplinedStep_raw_iff.mpr ((equationStep_iff_of_plain (ambient_plain (language := ambientNuCalc) rfl) relEnv _).mpr step.step)⟩
  | refl => exact .refl _
  | symm _ _ _ recurse => exact .symm _ _ recurse
  | trans _ _ _ _ _ left right => exact .trans _ _ _ left right

/-- **The canonical form of a process of the domain**: its located canonical form at a root location, read back. -/
def canon (term : Pattern) : Pattern :=
  if domain term then canonR ambientRepBlock (canonA term) else term

/-- **The canonical form of a process of the domain is a closed object process equivalent to it.** -/
theorem canon_facts {term : Pattern} (admitted : domain term = true) :
    HasType ambientNuCalc names [] (canon term) (.base "Proc") ∧ isObjectPattern (canon term) = true ∧
      ProcEquiv ambientNuCalc ambientBlock names [] term (canon term) := by
  obtain ⟨typed, object⟩ := typed_of_domain admitted
  obtain ⟨readTyped, readObject, -, readEquivalent⟩ := canonA_facts names_names (core_typed typed) object
  obtain ⟨-, canonEquivalent⟩ := canonR_sound (block := ambientRepBlock) names_context readTyped
  obtain ⟨canonTyped, equivalent⟩ := pure_equiv (.trans _ _ _ readEquivalent canonEquivalent) typed
  unfold canon
  rw [if_pos admitted]
  exact ⟨canonTyped, isObject_canonR (block := ambientRepBlock) readObject, equivalent⟩

/-- **The located canonical form read back gives canonical forms** on closed object processes, in the typed
reading. -/
theorem canonical (relEnv : RelationEnv) : Canonical relEnv ambientNuCalc canon domain reading where
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
    obtain ⟨typed, object⟩ := typed_of_domain admitted
    obtain ⟨-, canonObject, equivalent⟩ := canon_facts admitted
    exact objectEquivalent_of_objectChain relEnv (pure_objectChain equivalent typed object canonObject)
  same {first second} admitted equivalent := by
    have secondAdmitted := (domain_iff_of_equivalent equivalent).mp admitted
    obtain ⟨firstTyped, firstObject⟩ := typed_of_domain admitted
    obtain ⟨secondTyped, secondObject⟩ := typed_of_domain secondAdmitted
    unfold canon
    rw [if_pos admitted, if_pos secondAdmitted]
    exact congrArg (canonR ambientRepBlock) (canonA_same names_names (core_typed firstTyped) firstObject
      (core_typed secondTyped) secondObject
      (coreExtension.objectChain_extend (objectChain_of_objectEquivalent equivalent admitted)))
  closed {term} admitted := by
    obtain ⟨typed, -⟩ := typed_of_domain admitted
    obtain ⟨canonTyped, -, -⟩ := canon_facts admitted
    have before := typed.isWellScopedAt
    have after := canonTyped.isWellScopedAt
    simp only [List.length_nil] at before after
    rw [before, after]

/-! ## Coherence -/

open Mettapedia.Languages.ProcessCalculi.Ambient.Full (AmbNuRawStep)
open Mettapedia.Languages.ProcessCalculi.Ambient.Located (locatedRepBlock)
open Mettapedia.Languages.ProcessCalculi.Ambient.Decoding (rootForm rootForm_same)
open Mettapedia.Languages.ProcessCalculi.Ambient.Steps (presentationsA presented_pruned pruneTop pruneTop_facts
  step_typed presentation_facts)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (presentationDepth)

/-- **The presentations of a state**: the unfoldings of its root canonical block within the presentation depth, an
ambient redex having three parts (three unfoldings when the replicated components copy molecules, three times the
block's ceiling otherwise), each presented without its unused outermost restrictions. -/
def presentations (state : Pattern) : List Pattern :=
  (presentationsA (presentationDepth locatedRepBlock 3 (rootForm state)) state).map pruneTop

theorem profile : ReferenceProfile ambientNuCalc := profile_of_aligned (by decide)

/-- The reference steps of `ambientNuCalc` are the steps of its specification. -/
theorem step_iff_raw {source target : Pattern} :
    (∃ witness, StepValid RelationEnv.empty ambientNuCalc source witness target) ↔ AmbNuRawStep source target :=
  (contextualStep_iff_step RelationEnv.empty ambientNuCalc profile).symm.trans
    (Mettapedia.Languages.ProcessCalculi.Ambient.Full.step_iff_raw source target)

/-- **A process and its canonical form have one list of presentations**: both are read off the root canonical block,
which equivalent processes share. -/
theorem presentations_canon {term : Pattern} (admitted : domain term = true) :
    presentations (canon term) = presentations term := by
  obtain ⟨typed, object⟩ := typed_of_domain admitted
  obtain ⟨canonTyped, canonObject, equivalent⟩ := canon_facts admitted
  have same := rootForm_same names_names (core_typed canonTyped) canonObject (core_typed typed) object
    (ambient_objectChain names_context (coreExtension.sortedEquiv_extend (.symm _ _ equivalent)) canonObject object)
  unfold presentations presentationsA
  rw [same]

/-- **Coherence for plain steps**: a step from any process equivalent to a canonical one is matched, up to canonical
form, by a step listed at a presentation of it, wherever the fuel lists their steps. -/
theorem coherentPlain (fuel : ℕ) :
    CoherentPlain RelationEnv.empty ambientNuCalc fuel canon domain presentations reading :=
  coherentPlain_of_presented_simulation (canonical RelationEnv.empty)
    fun {redex witness contractum} _ admitted valid => by
      obtain ⟨typed, object⟩ := typed_of_domain admitted
      have avoiding := coreExtension.avoids_of_typed typed
      have raw := step_iff_raw.mp ⟨witness, valid⟩
      obtain ⟨shown, shownIn, contractum', raw', equivalent⟩ := presented_pruned names_names raw (core_typed typed) object
      obtain ⟨witness', valid'⟩ := step_iff_raw.mpr raw'
      obtain ⟨unpruned, unprunedIn, rfl⟩ := List.mem_map.mp shownIn
      obtain ⟨unprunedTyped, unprunedObject, unprunedEquivalent⟩ :=
        presentation_facts names_names (core_typed typed) object _ unpruned unprunedIn
      obtain ⟨shownTyped, shownObject, shownEquivalent⟩ := pruneTop_facts unpruned unprunedTyped unprunedObject
      have shownAvoiding := (SortedEquiv.avoids_iff (coreKeeps _)
        (.trans _ _ _ unprunedEquivalent shownEquivalent)).mp avoiding
      obtain ⟨contractumTyped, contractumObject⟩ := step_typed raw (core_typed typed) object
      obtain ⟨contractum'Typed, contractum'Object⟩ := step_typed raw' shownTyped shownObject
      have contractumPure := coreExtension.typed_restrict contractumTyped (AmbNuRawStep.avoids raw avoiding)
      have contractum'Pure := coreExtension.typed_restrict contractum'Typed (AmbNuRawStep.avoids raw' shownAvoiding)
      refine ⟨pruneTop unpruned, ?_, witness', contractum', valid', ?_⟩
      · rw [presentations_canon admitted]
        exact shownIn
      · unfold canon
        rw [if_pos (domain_of_typed contractum'Pure contractum'Object),
          if_pos (domain_of_typed contractumPure contractumObject)]
        exact congrArg (canonR ambientRepBlock) (canonA_same names_names contractum'Typed contractum'Object
          contractumTyped contractumObject
          (ambient_objectChain names_context equivalent contractum'Object contractumObject))

/-- **The canonical forms of ambients with restriction, as the front door takes them**: in the typed reading, steps
listed at the presentations of a state, coherent for plain steps. -/
def forms (fuel : ℕ) : CanonicalForms RelationEnv.empty ambientNuCalc fuel where
  reading := reading
  canon := canon
  domain := domain
  canonical := canonical RelationEnv.empty
  presentations := presentations
  labels := plainLabel
  coherent := CoherentPlain.on (coherentPlain fuel)

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.AmbientNuForms
