import Mettapedia.Languages.ProcessCalculi.PiCalculus.AuthoredStepReflection
import Mettapedia.Languages.ProcessCalculi.PiCalculus.AuthoredSemantics
import Mettapedia.OSLF.MeTTaIL.ContextSubstitution
import Mettapedia.GSLT.LanguageDef.BagNormalFormTyping

/-!
# Atomic names in the authored pi operational fragment

The one-sort declaration accepts more messages than atomic pi. The predicates
here identify atomic free/bound names and the process grammar over them.
They retain the ambient binder depth and canonical binder metadata. The
operational closure theorem concerns actual internal execution; closure under
the raw equation relation is a separate obligation.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL

/-- Atomic names are free names or variables in the current binder context. -/
inductive AtomicName : Nat → Pattern → Prop where
  | free (depth : Nat) (name : String) : AtomicName depth (.fvar name)
  | bound {depth index : Nat} (inScope : index < depth) : AtomicName depth (.bvar index)

/-- The atomic-name process grammar, with flat or nested parallel bags. -/
inductive AtomicPi : Nat → Pattern → Prop where
  | nil (depth : Nat) : AtomicPi depth (.apply "PiNil" [])
  | input {depth : Nat} {channel body : Pattern}
      (name : AtomicName depth channel) (continuation : AtomicPi (depth + 1) body) :
      AtomicPi depth (.apply "PiInp" [channel, .lambda none body])
  | output {depth : Nat} {channel datum : Pattern}
      (subject : AtomicName depth channel) (payload : AtomicName depth datum) :
      AtomicPi depth (.apply "PiOut" [channel, datum])
  | restriction {depth : Nat} {body : Pattern}
      (continuation : AtomicPi (depth + 1) body) :
      AtomicPi depth (.apply "PiNu" [.lambda none body])
  | server {depth : Nat} {channel body : Pattern}
      (name : AtomicName depth channel) (continuation : AtomicPi (depth + 1) body) :
      AtomicPi depth (.apply "PiRep" [channel, .lambda none body])
  | parallel {depth : Nat} {elements : List Pattern}
      (components : ∀ element ∈ elements, AtomicPi depth element) :
      AtomicPi depth (.collection .hashBag elements none)

theorem AtomicName.lift {depth : Nat} {name : Pattern} (atomic : AtomicName depth name)
    (amount : Nat) : AtomicName (depth + amount) (liftBVars 0 amount name) := by
  cases atomic with
  | free name => exact .free _ _
  | bound inScope => simpa only [liftBVars, Nat.zero_le, ite_true] using
      (AtomicName.bound (depth := depth + amount) (by omega))

theorem AtomicName.substitute {source target : Nat} {name : Pattern}
    (atomic : AtomicName source name) (assignment : ContextSubstitution.Assignment)
    (images : ∀ index, index < source → AtomicName target (assignment index)) :
    AtomicName target (ContextSubstitution.substitute assignment name) := by
  cases atomic with
  | free name => exact .free _ _
  | bound inScope => exact images _ inScope

private theorem atomic_lift_assignment {source target : Nat} {assignment : ContextSubstitution.Assignment}
    (images : ∀ index, index < source → AtomicName target (assignment index)) :
    ∀ index, index < source + 1 →
      AtomicName (target + 1) (ContextSubstitution.lift 1 assignment index) := by
  intro index inScope
  by_cases localIndex : index < 1
  · simpa only [ContextSubstitution.lift, localIndex, ite_true] using
      (AtomicName.bound (depth := target + 1) (index := index) (by omega))
  · simpa only [ContextSubstitution.lift, localIndex, ite_false] using (images (index - 1) (by omega)).lift 1

/-- Any scoped substitution by atomic names preserves the process grammar. -/
theorem AtomicPi.substitute {source target : Nat} {process : Pattern}
    (atomic : AtomicPi source process) (assignment : ContextSubstitution.Assignment)
    (images : ∀ index, index < source → AtomicName target (assignment index)) :
    AtomicPi target (ContextSubstitution.substitute assignment process) := by
  induction atomic generalizing target assignment with
  | nil => exact .nil _
  | input name _ ih =>
    exact .input (name.substitute assignment images) (ih _ (atomic_lift_assignment images))
  | output subject payload =>
    exact .output (subject.substitute assignment images) (payload.substitute assignment images)
  | restriction _ ih => exact .restriction (ih _ (atomic_lift_assignment images))
  | server name _ ih =>
    exact .server (name.substitute assignment images) (ih _ (atomic_lift_assignment images))
  | parallel _ ih =>
    simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map]
    apply AtomicPi.parallel
    intro element present
    obtain ⟨original, member, rfl⟩ := List.mem_map.mp present
    exact ih original member assignment images

/-- Eliminating an input binder with an atomic message stays at the ambient depth. -/
theorem AtomicPi.instantiate {depth : Nat} {body datum : Pattern}
    (atomic : AtomicPi (depth + 1) body) (message : AtomicName depth datum) :
    AtomicPi depth (instantiateBVar datum body) := by
  rw [← ContextSubstitution.substitute_single_eq_instantiateBVar]
  apply atomic.substitute
  intro index inScope
  cases index with
  | zero => exact message
  | succ index => exact .bound (by omega)

theorem AtomicName.closeFVar {depth : Nat} {name : Pattern}
    (atomic : AtomicName depth name) (index : Nat) (inScope : index ≤ depth) (free : String) :
    AtomicName (depth + 1) (Substitution.closeFVar index free name) := by
  cases atomic with
  | free name =>
    simp only [Substitution.closeFVar]
    split
    · exact .bound (by omega)
    · exact .free _ _
  | bound boundScope => simpa only [Substitution.closeFVar] using
      (AtomicName.bound (depth := depth + 1) (by omega))

/-- Closing a free atomic name preserves the grammar in an enlarged index
range. Arbitrary cutoffs certify this scope property; outer-binder insertion
uses the current depth as its cutoff. -/
theorem AtomicPi.closeFVar {depth : Nat} {process : Pattern} (atomic : AtomicPi depth process)
    (index : Nat) (inScope : index ≤ depth) (free : String) :
    AtomicPi (depth + 1) (Substitution.closeFVar index free process) := by
  induction atomic generalizing index with
  | nil => simpa only [Substitution.closeFVar, List.map_nil] using AtomicPi.nil _
  | input name _ ih =>
    simp only [Substitution.closeFVar, List.map_cons, List.map_nil]
    exact .input (name.closeFVar index inScope free) (ih (index + 1) (by omega))
  | output subject payload =>
    simp only [Substitution.closeFVar, List.map_cons, List.map_nil]
    exact .output (subject.closeFVar index inScope free) (payload.closeFVar index inScope free)
  | restriction _ ih =>
    simp only [Substitution.closeFVar, List.map_cons, List.map_nil]
    exact .restriction (ih (index + 1) (by omega))
  | server name _ ih =>
    simp only [Substitution.closeFVar, List.map_cons, List.map_nil]
    exact .server (name.closeFVar index inScope free) (ih (index + 1) (by omega))
  | parallel _ ih =>
    simp only [Substitution.closeFVar]
    apply AtomicPi.parallel
    intro element present
    obtain ⟨original, member, rfl⟩ := List.mem_map.mp present
    exact ih original member index inScope

private theorem atomic_components {depth : Nat} {process : Pattern} (atomic : AtomicPi depth process) :
    ∀ component ∈ piComponents process, AtomicPi depth component := by
  cases atomic <;> simp only [piComponents, List.mem_singleton]
  all_goals first | assumption | (intro _ equal; subst equal; constructor <;> assumption)

theorem AtomicPi.piPar {depth : Nat} {left right : Pattern}
    (first : AtomicPi depth left) (second : AtomicPi depth right) :
    AtomicPi depth (piPar left right) := by
  rw [piPar_components]
  apply AtomicPi.parallel
  intro element present
  rcases List.mem_append.mp present with present | present
  · exact atomic_components first element present
  · exact atomic_components second element present

/-- All named processes inhabit the atomic fragment, including shadowing and
colliding binder names. -/
theorem piToPattern_atomic (process : Process) : AtomicPi 0 (piToPattern process) := by
  induction process with
  | nil => exact .nil _
  | par _ _ ihFirst ihSecond => exact ihFirst.piPar ihSecond
  | input channel bound _ ih => exact .input (.free _ channel) (ih.closeFVar 0 (by omega) bound)
  | output channel datum => exact .output (.free _ channel) (.free _ datum)
  | nu bound _ ih => exact .restriction (ih.closeFVar 0 (by omega) bound)
  | replicate channel bound _ ih => exact .server (.free _ channel) (ih.closeFVar 0 (by omega) bound)

private theorem atomic_parallel_member {depth : Nat} {elements : List Pattern}
    (atomic : AtomicPi depth (.collection .hashBag elements none))
    {element : Pattern} (member : element ∈ elements) : AtomicPi depth element := by
  cases atomic with
  | parallel components => exact components element member

private theorem atomic_input_inversion {depth : Nat} {channel body : Pattern} {binder : Option String}
    (atomic : AtomicPi depth (.apply "PiInp" [channel, .lambda binder body])) :
    binder = none ∧ AtomicName depth channel ∧ AtomicPi (depth + 1) body := by
  generalize shape : Pattern.apply "PiInp" [channel, .lambda binder body] = process at atomic
  cases atomic <;> simp_all

private theorem atomic_output_inversion {depth : Nat} {channel datum : Pattern}
    (atomic : AtomicPi depth (.apply "PiOut" [channel, datum])) :
    AtomicName depth channel ∧ AtomicName depth datum := by
  generalize shape : Pattern.apply "PiOut" [channel, datum] = process at atomic
  cases atomic <;> simp_all

private theorem atomic_server_inversion {depth : Nat} {channel body : Pattern} {binder : Option String}
    (atomic : AtomicPi depth (.apply "PiRep" [channel, .lambda binder body])) :
    binder = none ∧ AtomicName depth channel ∧ AtomicPi (depth + 1) body := by
  generalize shape : Pattern.apply "PiRep" [channel, .lambda binder body] = process at atomic
  cases atomic <;> simp_all

private theorem atomic_restriction_inversion {depth : Nat} {body : Pattern} {binder : Option String}
    (atomic : AtomicPi depth (.apply "PiNu" [.lambda binder body])) :
    binder = none ∧ AtomicPi (depth + 1) body := by
  generalize shape : Pattern.apply "PiNu" [.lambda binder body] = process at atomic
  cases atomic <;> simp_all

/-- Actual authored internal execution cannot introduce a process-valued
message or a dangling index into the atomic-name fragment. -/
theorem PiRawStep.atomic {source target : Pattern} (step : PiRawStep source target)
    {depth : Nat} (atomic : AtomicPi depth source) : AtomicPi depth target := by
  induction step generalizing depth with
  | @comm elements tail i hi j hj channel binder body datum atInput atOutput =>
    cases atomic with
    | parallel components =>
      have inputTyped := components elements[i] (List.getElem_mem hi)
      rw [atInput] at inputTyped
      have outputMember : (elements.eraseIdx i)[j] ∈ elements :=
        List.mem_of_mem_eraseIdx (List.getElem_mem hj)
      have outputTyped := components _ outputMember
      rw [atOutput] at outputTyped
      obtain ⟨_, _, continuation⟩ := atomic_input_inversion inputTyped
      obtain ⟨_, message⟩ := atomic_output_inversion outputTyped
      apply AtomicPi.parallel
      intro element member
      rcases List.mem_cons.mp member with rfl | residual
      · exact continuation.instantiate message
      · exact components element (List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx residual))
  | @repComm elements tail i hi j hj channel binder body datum atInput atOutput =>
    cases atomic with
    | parallel components =>
      have inputTyped := components elements[i] (List.getElem_mem hi)
      rw [atInput] at inputTyped
      have outputMember : (elements.eraseIdx i)[j] ∈ elements :=
        List.mem_of_mem_eraseIdx (List.getElem_mem hj)
      have outputTyped := components _ outputMember
      rw [atOutput] at outputTyped
      obtain ⟨_, subject, continuation⟩ := atomic_server_inversion inputTyped
      obtain ⟨_, message⟩ := atomic_output_inversion outputTyped
      apply AtomicPi.parallel
      intro element member
      simp only [List.cons_append, List.nil_append, List.mem_cons] at member
      rcases member with rfl | rfl | residual
      · exact continuation.instantiate message
      · exact .server subject continuation
      · exact components element (List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx residual))
  | @par elements tail i hi target _ ih =>
    cases atomic with
    | parallel components =>
      apply AtomicPi.parallel
      intro element member
      rcases List.mem_cons.mp member with rfl | residual
      · exact ih (components _ (List.getElem_mem hi))
      · exact components element (List.mem_of_mem_eraseIdx residual)
  | res binder _ ih =>
    exact .restriction (ih (atomic_restriction_inversion atomic).2)

theorem atomic_step_preservation {depth : Nat} {source target : Pattern}
    (atomic : AtomicPi depth source)
    (step : Step (engineBasePremises RelationEnv.empty) piCalc source target) :
    AtomicPi depth target := (piRawStep_of_step step).atomic atomic

/-- Preservation holds for every supplied finite authored path. -/
theorem atomic_path_preservation {depth : Nat} {source target : Pattern}
    (atomic : AtomicPi depth source)
    (path : Relation.ReflTransGen (Step (engineBasePremises RelationEnv.empty) piCalc) source target) :
    AtomicPi depth target := by
  induction path with
  | refl => exact atomic
  | tail _ step ih => exact atomic_step_preservation ih step

/-- A process is not an atomic message, even though the one-sort declaration
can assign it the process sort. -/
theorem inaction_not_atomic_name (depth : Nat) : ¬ AtomicName depth (.apply "PiNil" []) := by
  intro atomic
  cases atomic

theorem process_message_not_atomic (depth : Nat) :
    ¬ AtomicPi depth (.apply "PiOut" [.fvar "a", .apply "PiNil" []]) := by
  intro atomic
  exact inaction_not_atomic_name depth (atomic_output_inversion atomic).2

theorem AtomicName.canonical {depth : Nat} {name : Pattern} (atomic : AtomicName depth name) :
    name.hasCanonicalBinderMetadata = true := by cases atomic <;> rfl

theorem AtomicPi.canonical {depth : Nat} {process : Pattern} (atomic : AtomicPi depth process) :
    process.hasCanonicalBinderMetadata = true := by
  induction atomic with
  | nil => rfl
  | input name _ ih | server name _ ih =>
    simp [Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList, name.canonical, ih]
  | output subject payload =>
    simp [Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList,
      subject.canonical, payload.canonical]
  | restriction _ ih =>
    simp [Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList, ih]
  | parallel _ ih =>
    change Pattern.hasCanonicalBinderMetadataList _ = true
    exact Mettapedia.GSLT.LanguageDef.BagNormalForm.hasCanonicalBinderMetadataList_iff.mpr ih

open Mettapedia.GSLT.LanguageDef.WellSorted in
theorem AtomicName.object {depth : Nat} {name : Pattern} (atomic : AtomicName depth name) :
    isObjectPattern name = true := by cases atomic <;> rfl

open Mettapedia.GSLT.LanguageDef.WellSorted in
theorem AtomicPi.object {depth : Nat} {process : Pattern} (atomic : AtomicPi depth process) :
    isObjectPattern process = true := by
  induction atomic with
  | nil => rfl
  | input name _ ih | server name _ ih =>
    simp [isObjectPattern, isObjectPatternList, name.object, ih]
  | output subject payload =>
    simp [isObjectPattern, isObjectPatternList, subject.object, payload.object]
  | restriction _ ih => simp [isObjectPattern, isObjectPatternList, ih]
  | parallel _ ih =>
    change isObjectPatternList _ = true
    exact Mettapedia.GSLT.LanguageDef.BagNormalForm.isObjectPatternList_iff.mpr ih

open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.BagNormalForm
open Mettapedia.OSLF.MeTTaIL.PatternCode

theorem AtomicName.hasType {depth : Nat} {name : Pattern} (atomic : AtomicName depth name) :
    HasType piCalc piNameContext (List.replicate depth (.base "Proc")) name (.base "Proc") := by
  cases atomic with
  | free name => exact .fvar rfl
  | bound inScope => exact .bvar (List.getElem?_replicate_of_lt inScope)

/-- The fragment supplies actual declaration typing at every ambient depth. -/
theorem AtomicPi.hasType {depth : Nat} {process : Pattern} (atomic : AtomicPi depth process) :
    HasType piCalc piNameContext (List.replicate depth (.base "Proc")) process (.base "Proc") := by
  induction atomic with
  | nil =>
    exact .constructor (List.getElem_mem (l := piCalc.terms) (n := 0) (by decide))
      (by simp [UsesBareCollection, piCalc]) .nil
  | input name _ ih =>
    exact .constructor (List.getElem_mem (l := piCalc.terms) (n := 2) (by decide))
      (by simp [UsesBareCollection, piCalc]) (.cons trivial rfl name.hasType
        (.cons trivial rfl (.lambda (by simpa [List.replicate_succ] using ih)) .nil))
  | output subject payload =>
    exact .constructor (List.getElem_mem (l := piCalc.terms) (n := 3) (by decide))
      (by simp [UsesBareCollection, piCalc])
      (.cons trivial rfl subject.hasType (.cons trivial rfl payload.hasType .nil))
  | restriction _ ih =>
    exact .constructor (List.getElem_mem (l := piCalc.terms) (n := 4) (by decide))
      (by simp [UsesBareCollection, piCalc])
      (.cons trivial rfl (.lambda (by simpa [List.replicate_succ] using ih)) .nil)
  | server name _ ih =>
    exact .constructor (List.getElem_mem (l := piCalc.terms) (n := 5) (by decide))
      (by simp [UsesBareCollection, piCalc]) (.cons trivial rfl name.hasType
        (.cons trivial rfl (.lambda (by simpa [List.replicate_succ] using ih)) .nil))
  | parallel _ ih => exact bag_hasType piBagTheory (elementsHaveType_iff.mpr ih)

theorem AtomicName.normalForm {depth : Nat} {name : Pattern} (atomic : AtomicName depth name) :
    normalForm (some "PiNil") name = name := by cases atomic <;> rfl

private theorem atomic_splice {depth : Nat} {process : Pattern} (atomic : AtomicPi depth process) :
    ∀ element ∈ splice process, AtomicPi depth element := by
  cases atomic <;> simp only [splice, List.mem_singleton]
  all_goals first | assumption | (intro _ equal; subst equal; constructor <;> assumption)

/-- Sorting, flattening, removing units, and collapsing singleton bags preserve
the atomic process grammar; no comparison of sorting codes is evaluated. -/
theorem AtomicPi.normalizeBag {depth : Nat} {elements : List Pattern}
    (components : ∀ element ∈ elements, AtomicPi depth element) :
    AtomicPi depth (normalizeBag (some "PiNil") elements) := by
  have kept : ∀ element ∈ sortPatterns (bagContents "PiNil" elements), AtomicPi depth element := by
    intro element member
    rw [mem_sortPatterns] at member
    have flattened := (List.mem_filter.mp member).1
    obtain ⟨original, present, inside⟩ := List.mem_flatMap.mp flattened
    exact atomic_splice (components original present) element inside
  change AtomicPi depth (collapse "PiNil" (sortPatterns (bagContents "PiNil" elements)))
  cases sorted : sortPatterns (bagContents "PiNil" elements) with
  | nil => exact .nil _
  | cons head rest =>
    rw [sorted] at kept
    cases rest with
    | nil => exact kept head (by simp)
    | cons second tail => exact .parallel kept

theorem AtomicPi.normalForm {depth : Nat} {process : Pattern} (atomic : AtomicPi depth process) :
    AtomicPi depth (normalForm (some "PiNil") process) := by
  induction atomic with
  | nil => exact .nil _
  | input name _ ih =>
    simpa only [Mettapedia.GSLT.LanguageDef.BagNormalForm.normalForm, normalFormList,
      name.normalForm] using AtomicPi.input name ih
  | output subject payload =>
    simpa only [Mettapedia.GSLT.LanguageDef.BagNormalForm.normalForm, normalFormList,
      subject.normalForm, payload.normalForm] using
      AtomicPi.output subject payload
  | restriction _ ih => exact .restriction ih
  | server name _ ih =>
    simpa only [Mettapedia.GSLT.LanguageDef.BagNormalForm.normalForm, normalFormList,
      name.normalForm] using AtomicPi.server name ih
  | parallel _ ih =>
    rw [normalForm_bag]
    apply AtomicPi.normalizeBag
    intro element present
    obtain ⟨original, member, rfl⟩ := List.mem_map.mp present
    exact ih original member

end Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance
