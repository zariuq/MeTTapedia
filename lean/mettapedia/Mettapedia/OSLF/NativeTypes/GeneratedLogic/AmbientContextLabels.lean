import Mettapedia.OSLF.NativeTypes.GeneratedLogic.AmbientCommForms
import Mettapedia.Languages.ProcessCalculi.Ambient.CommSuccessors
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CCSPartnerAdequacy

/-!
# Two-level context labels for mobile ambients

A process of mobile ambients meets its environment across ambient boundaries: a redex can span the process, its
enclosing ambient and the ambient enclosing that. The contexts that enable a process's steps are therefore of four
families (`AmbientContext`), each the hole beside a partner:

- **parallel**: `□ | R`;
- **parent**: `m[□ | R]`, the process inside an ambient;
- **sibling**: `n[□ | Q] | m[S]`, the process inside an ambient beside another ambient;
- **grandparent**: `m[n[□ | Q] | R]`, the process inside an ambient inside another.

At the front door of `ambientCommCalc`:

- **A step in such a context is a reduction of the filled context** (`step_label_iff`): the contexts are congruent, a
  chain of laws carried through the hole (`congruent`).
- **Context steps keep the processes** (`closedUnder`), and **they are finitely many up to the laws** (`finiteUpTo`): a
  reduction is matched, up to the canonical form, by a firing of one of the presentations of the canonical form of the
  filled context (`AmbientCommForms.presented_simulation`), and a presentation's firings are listed
  (`Comm.mem_commSuccessors`).
- So **two processes have the same native types under the two-level contexts exactly when they are forward bisimilar
  under them** (`agree_iff_forwardBisimilar`), and **that is two-level saturated reduction bisimilarity**
  (`agree_iff_saturated`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.AmbientContextLabels

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts (OneHoleContext)
open Mettapedia.OSLF.MeTTaIL.Substitution (freeVars)
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.BagNormalForm (elementsHaveType_iff isObjectPatternList_iff)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (BaseContext SortedEquiv ProcEquiv ObjectChain isObject_bag)
open Mettapedia.Languages.ProcessCalculi.Ambient.Comm (AmbCommRawStep commSuccessors mem_commSuccessors
  ambientCommCalc comm_objectChain amb_typed commSignature)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.AmbientCommForms (reading domain canon canonical typed_of_domain
  domain_of_typed names names_context domain_iff_of_equivalent objectChain_of_objectEquivalent
  objectEquivalent_of_objectChain presentations presented_simulation step_iff_raw core_typed comm_typed)

/-! ## The contexts -/

/-- **The two-level ambient contexts**: the hole beside a partner, at the top; inside an ambient; inside an ambient
beside another ambient; inside an ambient inside another. -/
inductive AmbientContext where
  /-- `□ | R`. -/
  | par (partner : Pattern)
  /-- `m[□ | R]`. -/
  | parent (outer : String) (partner : Pattern)
  /-- `n[□ | Q] | m[S]`. -/
  | sibling (inner : String) (partner : Pattern) (target : String) (host : Pattern)
  /-- `m[n[□ | Q] | R]`. -/
  | grandparent (outer : String) (partner : Pattern) (inner : String) (innerPartner : Pattern)
  deriving DecidableEq

namespace AmbientContext

/-- The ambient of a name. -/
def ambOf (name : String) (content : Pattern) : Pattern := .apply "AAmb" [.fvar name, content]

/-- **The one-hole context.** -/
def hole : AmbientContext → OneHoleContext
  | .par partner => .collection .hashBag [] .hole [partner] none
  | .parent outer partner => .apply "AAmb" [.fvar outer] (.collection .hashBag [] .hole [partner] none) []
  | .sibling inner partner target host =>
      .collection .hashBag [] (.apply "AAmb" [.fvar inner] (.collection .hashBag [] .hole [partner] none) [])
        [ambOf target host] none
  | .grandparent outer partner inner innerPartner =>
      .apply "AAmb" [.fvar outer] (.collection .hashBag []
        (.apply "AAmb" [.fvar inner] (.collection .hashBag [] .hole [innerPartner] none) []) [partner] none) []

/-- The processes of a context. -/
def partners : AmbientContext → List Pattern
  | .par partner => [partner]
  | .parent _ partner => [partner]
  | .sibling _ partner _ host => [partner, host]
  | .grandparent _ partner _ innerPartner => [partner, innerPartner]

/-- The names of a context. -/
def namesOf : AmbientContext → List String
  | .par _ => []
  | .parent outer _ => [outer]
  | .sibling inner _ target _ => [inner, target]
  | .grandparent outer _ inner _ => [outer, inner]

/-- **An admitted context**: its processes are processes not using the hole's name, and its names are not the hole's. -/
def admits (holeName : String) (context : AmbientContext) : Bool :=
  context.partners.all (fun partner => domain partner && avoidsHole holeName partner) &&
    context.namesOf.all (fun name => name != holeName)

/-- **The context, read from its pattern.** -/
def read? (holeName : String) : Pattern → Option AmbientContext
  | .collection .hashBag [.fvar name, partner] none => if name = holeName then some (.par partner) else none
  | .apply "AAmb" [.fvar outer, .collection .hashBag [.fvar name, partner] none] =>
      if name = holeName then some (.parent outer partner) else none
  | .collection .hashBag [.apply "AAmb" [.fvar inner, .collection .hashBag [.fvar name, partner] none],
      .apply "AAmb" [.fvar target, host]] none =>
      if name = holeName then some (.sibling inner partner target host) else none
  | .apply "AAmb" [.fvar outer, .collection .hashBag
      [.apply "AAmb" [.fvar inner, .collection .hashBag [.fvar name, innerPartner] none], partner] none] =>
      if name = holeName then some (.grandparent outer partner inner innerPartner) else none
  | _ => none

theorem read?_fill (holeName : String) (context : AmbientContext) :
    read? holeName (context.hole.fill (.fvar holeName)) = some context := by
  cases context <;> simp [hole, OneHoleContext.fill, read?, ambOf]

theorem fill_of_read? {holeName : String} {pattern : Pattern} {context : AmbientContext}
    (found : read? holeName pattern = some context) : pattern = context.hole.fill (.fvar holeName) := by
  unfold read? at found
  split at found <;> (try split_ifs at found with same) <;> (try subst same) <;> cases found <;>
    simp [hole, OneHoleContext.fill, ambOf]

end AmbientContext

/-! ## Labels -/

/-- **The label of a context**: a step of the process placed in it. -/
abbrev contextLabel (holeName : String) (context : AmbientContext) : StepLabel :=
  .context holeName (context.hole.fill (.fvar holeName)) .any

/-- **Whether a label is a two-level context's**, read plainly, with an admitted context. -/
def isContextLabel : StepLabel → Bool
  | .context holeName pattern .any =>
      match AmbientContext.read? holeName pattern with
      | some context => context.admits holeName
      | none => false
  | _ => false

theorem isContextLabel_contextLabel {holeName : String} {context : AmbientContext}
    (admitted : context.admits holeName = true) : isContextLabel (contextLabel holeName context) = true := by
  simp [isContextLabel, AmbientContext.read?_fill, admitted]

theorem exists_of_isContextLabel {label : StepLabel} (labelled : isContextLabel label = true) :
    ∃ holeName context, label = contextLabel holeName context ∧ context.admits holeName = true := by
  match label, labelled with
  | .context holeName pattern .any, labelled =>
      simp only [isContextLabel] at labelled
      split at labelled
      · rename_i context found
        exact ⟨holeName, context, by rw [AmbientContext.fill_of_read? found], labelled⟩
      · cases labelled

/-! ## Filled contexts -/

/-- **The front door of mobile ambients with communication.** -/
abbrev frontDoor : NativeStructure Pattern := referenceStructure RelationEnv.empty ambientCommCalc reading

/-- The processes: object processes with no free bound variable, their free variables names. -/
abbrev processes (term : Pattern) : Prop := domain term = true

/-- **A reduction**: a plain step of the front door. -/
def Reduces (source target : Pattern) : Prop := frontDoor.step source .any target

theorem isState_of_process {term : Pattern} (admitted : processes term) : IsState term :=
  ⟨by simpa using (typed_of_domain admitted).1.isWellScopedAt, (typed_of_domain admitted).2⟩

theorem name_typed {bound : List TypeExpr} (name : String) :
    HasType ambientCommCalc names bound (.fvar name) (.base "Name") :=
  .fvar (by simp [names, EquationReading.nameContext])

theorem bag_typed {bound : List TypeExpr} {elements : List Pattern}
    (each : ∀ element ∈ elements, HasType ambientCommCalc names bound element (.base "Proc")) :
    HasType ambientCommCalc names bound (.collection .hashBag elements none) (.base "Proc") :=
  commSignature.bag_typed (elementsHaveType_iff.mpr each)

theorem ambOf_typed {bound : List TypeExpr} {name : String} {content : Pattern}
    (typed : HasType ambientCommCalc names bound content (.base "Proc")) :
    HasType ambientCommCalc names bound (AmbientContext.ambOf name content) (.base "Proc") :=
  amb_typed (name_typed name) typed

namespace AmbientContext

theorem admits_parts {holeName : String} {context : AmbientContext} (admitted : context.admits holeName = true) :
    (∀ partner ∈ context.partners, processes partner ∧ avoidsHole holeName partner = true) ∧
      ∀ name ∈ context.namesOf, name ≠ holeName := by
  simp only [admits, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq] at admitted
  exact ⟨fun partner member => admitted.1 partner member, admitted.2⟩

/-- **A filled context types as a process.** -/
theorem fill_typed {holeName : String} {context : AmbientContext} (admitted : context.admits holeName = true)
    {filling : Pattern} (typed : HasType ambientCommCalc names [] filling (.base "Proc")) :
    HasType ambientCommCalc names [] (context.hole.fill filling) (.base "Proc") := by
  obtain ⟨partnersIn, -⟩ := admits_parts admitted
  have partnerTyped : ∀ partner ∈ context.partners, HasType ambientCommCalc names [] partner (.base "Proc") :=
    fun partner member => (typed_of_domain (partnersIn partner member).1).1
  cases context with
  | par partner =>
      simp only [hole, OneHoleContext.fill, List.nil_append]
      exact bag_typed fun element member => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact typed
        · exact partnerTyped _ (by simp [partners])
  | parent outer partner =>
      simp only [hole, OneHoleContext.fill, List.nil_append, List.cons_append]
      exact ambOf_typed (name := outer) (bag_typed fun element member => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact typed
        · exact partnerTyped _ (by simp [partners]))
  | sibling inner partner target host =>
      simp only [hole, OneHoleContext.fill, List.nil_append, List.cons_append]
      exact bag_typed fun element member => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact ambOf_typed (name := inner) (bag_typed fun element member => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at member
            rcases member with rfl | rfl
            · exact typed
            · exact partnerTyped _ (by simp [partners]))
        · exact ambOf_typed (partnerTyped _ (by simp [partners]))
  | grandparent outer partner inner innerPartner =>
      simp only [hole, OneHoleContext.fill, List.nil_append, List.cons_append]
      exact ambOf_typed (name := outer) (bag_typed fun element member => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact ambOf_typed (name := inner) (bag_typed fun element member => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at member
            rcases member with rfl | rfl
            · exact typed
            · exact partnerTyped _ (by simp [partners]))
        · exact partnerTyped _ (by simp [partners]))

/-- A filled context is an object when the filling is. -/
theorem fill_object {holeName : String} {context : AmbientContext} (admitted : context.admits holeName = true)
    {filling : Pattern} (object : isObjectPattern filling = true) :
    isObjectPattern (context.hole.fill filling) = true := by
  obtain ⟨partnersIn, -⟩ := admits_parts admitted
  have partnerObject : ∀ partner ∈ context.partners, isObjectPattern partner = true :=
    fun partner member => (typed_of_domain (partnersIn partner member).1).2
  cases context <;>
    simp only [partners, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at partnerObject <;>
    simp [hole, OneHoleContext.fill, ambOf, isObjectPattern, isObjectPatternList, object, partnerObject]

/-- **A filled context is a process.** -/
theorem fill_process {holeName : String} {context : AmbientContext} (admitted : context.admits holeName = true)
    {filling : Pattern} (fillingIn : processes filling) : processes (context.hole.fill filling) :=
  domain_of_typed (fill_typed admitted (typed_of_domain fillingIn).1) (fill_object admitted (typed_of_domain fillingIn).2)

/-- The context avoids the hole's name. -/
theorem avoids {holeName : String} {context : AmbientContext} (admitted : context.admits holeName = true) :
    contextAvoidsHole holeName context.hole = true := by
  obtain ⟨partnersIn, namesOut⟩ := admits_parts admitted
  have partnerAvoids : ∀ partner ∈ context.partners, avoidsHole holeName partner = true :=
    fun partner member => (partnersIn partner member).2
  cases context <;>
    simp_all [hole, contextAvoidsHole, avoidsHoleList, avoidsHole, ambOf, partners, namesOf]

/-- **Placing a closed process in the context is filling the hole.** -/
theorem plug_eq {holeName : String} {context : AmbientContext} (admitted : context.admits holeName = true)
    {process : Pattern} (closed : process.isWellScopedAt 0 = true) :
    plug holeName (context.hole.fill (.fvar holeName)) process = context.hole.fill process :=
  plug_fill context.hole (avoids admitted) closed

/-- **Equivalent processes fill a context to equivalent processes.** -/
theorem fill_congr {holeName : String} {context : AmbientContext} (admitted : context.admits holeName = true)
    {first second : Pattern} (firstIn : processes first) (secondIn : processes second)
    (equivalent : ObjectEquivalent RelationEnv.empty ambientCommCalc reading first second) :
    ObjectEquivalent RelationEnv.empty ambientCommCalc reading (context.hole.fill first) (context.hole.fill second) := by
  have chain := objectChain_of_objectEquivalent equivalent firstIn
  have filled : SortedEquiv ambientCommCalc names [] (.base "Proc") (context.hole.fill first)
      (context.hole.fill second) :=
    SortedEquiv.fill context.hole (fun _ typed => fill_typed admitted typed) chain.toSortedEquiv
  exact objectEquivalent_of_objectChain RelationEnv.empty (comm_objectChain names_context filled
    (fill_object admitted (typed_of_domain firstIn).2) (fill_object admitted (typed_of_domain secondIn).2))

end AmbientContext

/-- A reduction keeps a process a process. -/
theorem reduces_process {source target : Pattern} (sourceIn : processes source) (reduces : Reduces source target) :
    processes target := by
  obtain ⟨-, -, redex, contractum, witness, before, -, valid, -, after, -⟩ := reduces
  have redexIn : processes redex := (domain_iff_of_equivalent before).mp sourceIn
  obtain ⟨contractumTyped, contractumObject⟩ :=
    Mettapedia.Languages.ProcessCalculi.Ambient.Comm.commStep_typed (step_iff_raw.mp ⟨witness, valid⟩)
      (core_typed (typed_of_domain redexIn).1) (typed_of_domain redexIn).2
  exact (domain_iff_of_equivalent after).mp (domain_of_typed (comm_typed contractumTyped) contractumObject)

/-- **A step in a two-level context is a reduction of the filled context.** -/
theorem step_label_iff {holeName : String} {context : AmbientContext} (admitted : context.admits holeName = true)
    {source target : Pattern} (sourceIn : processes source) :
    frontDoor.step source (contextLabel holeName context) target ↔ Reduces (context.hole.fill source) target := by
  rw [step_context_iff]
  constructor
  · rintro ⟨-, presentation, presents, presentationState, step⟩
    have presentationIn := (domain_iff_of_equivalent presents).mp sourceIn
    rw [AmbientContext.plug_eq admitted presentationState.1] at step
    have equivalent := AmbientContext.fill_congr admitted presentationIn sourceIn (.symm _ _ presents)
    exact (referenceStructure_saturated RelationEnv.empty ambientCommCalc reading).stepSource
      (Indistinct.of_states (isState_of_process (AmbientContext.fill_process admitted presentationIn))
        (isState_of_process (AmbientContext.fill_process admitted sourceIn)) equivalent) step
  · intro step
    refine ⟨isState_of_process sourceIn, source, .refl _, isState_of_process sourceIn, ?_⟩
    rw [AmbientContext.plug_eq admitted (isState_of_process sourceIn).1]
    exact step

/-! ## Finitely many context steps, keeping the processes -/

/-- **Context steps keep the processes.** -/
theorem closedUnder : frontDoor.ClosedUnder isContextLabel processes := by
  intro source label target sourceIn labelled step
  obtain ⟨holeName, context, rfl, admitted⟩ := exists_of_isContextLabel labelled
  exact reduces_process (AmbientContext.fill_process admitted sourceIn) ((step_label_iff admitted sourceIn).mp step)

/-- A firing's target with the canonical form of a process is a process. -/
theorem process_of_canon_eq {term other : Pattern} (otherIn : processes other) (same : canon term = canon other) :
    processes term := by
  by_contra outside
  have canonIs : canon term = term := by
    unfold canon
    rw [if_neg outside]
  rw [canonIs] at same
  exact outside (same ▸ (canonical RelationEnv.empty).admitted_canon otherIn)

/-- **Context steps are finitely many up to the laws**: the firings of the presentations of the canonical form of the
filled context. -/
theorem finiteUpTo : frontDoor.FiniteUpTo isContextLabel processes
    (Indistinct RelationEnv.empty ambientCommCalc reading) := by
  classical
  intro source sourceIn label labelled
  obtain ⟨holeName, context, rfl, admitted⟩ := exists_of_isContextLabel labelled
  have filledIn := AmbientContext.fill_process admitted sourceIn
  refine ⟨((presentations (canon (context.hole.fill source))).flatMap commSuccessors).filter
    (fun next => decide (frontDoor.step source (contextLabel holeName context) next)), ?_, ?_⟩
  · intro listed member
    exact of_decide_eq_true (List.mem_filter.mp member).2
  · intro target step
    have reduction := (step_label_iff admitted sourceIn).mp step
    have targetIn := reduces_process filledIn reduction
    obtain ⟨-, -, redex, contractum, witness, before, -, valid, -, after, -⟩ := reduction
    have redexIn : processes redex := (domain_iff_of_equivalent before).mp filledIn
    have raw := step_iff_raw.mp ⟨witness, valid⟩
    obtain ⟨shown, shownIn, contractum', raw', same⟩ := presented_simulation redexIn raw
    rw [← (canonical RelationEnv.empty).same filledIn before] at shownIn
    have listed : contractum' ∈ (presentations (canon (context.hole.fill source))).flatMap commSuccessors :=
      List.mem_flatMap.mpr ⟨shown, shownIn, mem_commSuccessors raw'⟩
    obtain ⟨contractumTyped, contractumObject⟩ :=
      Mettapedia.Languages.ProcessCalculi.Ambient.Comm.commStep_typed raw (core_typed (typed_of_domain redexIn).1)
        (typed_of_domain redexIn).2
    have contractumIn : processes contractum := domain_of_typed (comm_typed contractumTyped) contractumObject
    have contractum'In : processes contractum' := process_of_canon_eq contractumIn same
    have equivalent : ObjectEquivalent RelationEnv.empty ambientCommCalc reading target contractum' :=
      .trans _ _ _ (.symm _ _ after) (.trans _ _ _ ((canonical RelationEnv.empty).equivalent contractumIn)
        (same ▸ .symm _ _ ((canonical RelationEnv.empty).equivalent contractum'In)))
    have indistinct := Indistinct.of_states (isState_of_process targetIn) (isState_of_process contractum'In) equivalent
    have stepped := (referenceStructure_saturated RelationEnv.empty ambientCommCalc reading).stepTarget indistinct step
    exact ⟨contractum', List.mem_filter.mpr ⟨listed, decide_eq_true stepped⟩, indistinct⟩

/-! ## The characterization -/

/-- **Two processes have the same native types under the two-level contexts exactly when they are forward bisimilar
under them.** -/
theorem agree_iff_forwardBisimilar {first second : Pattern} (firstIn : processes first) (secondIn : processes second) :
    frontDoor.AgreeOn (Formula.forwardOn isContextLabel) first second ↔
      frontDoor.ForwardBisimilar isContextLabel first second :=
  NativeStructure.agree_iff_forwardBisimilar (referenceStructure_saturated RelationEnv.empty ambientCommCalc reading)
    finiteUpTo closedUnder firstIn secondIn

/-- **A two-level saturated reduction bisimulation**: in every admitted two-level context, a reduction of either side
is matched by one of the other, to related processes. -/
def IsSaturated (relation : Pattern → Pattern → Prop) : Prop :=
  ∀ ⦃first second⦄, relation first second → ∀ (holeName : String) (context : AmbientContext),
    context.admits holeName = true →
    (∀ next, Reduces (context.hole.fill first) next →
      ∃ matched, Reduces (context.hole.fill second) matched ∧ relation next matched) ∧
    (∀ next, Reduces (context.hole.fill second) next →
      ∃ matched, Reduces (context.hole.fill first) matched ∧ relation matched next)

/-- **Two-level saturated reduction bisimilarity** of processes. -/
def SaturatedBisimilar (first second : Pattern) : Prop :=
  ∃ relation, IsSaturated relation ∧ (∀ ⦃left right⦄, relation left right → processes left ∧ processes right) ∧
    relation first second

/-- **Forward bisimilarity under the two-level contexts is two-level saturated reduction bisimilarity.** -/
theorem forwardBisimilar_iff_saturated {first second : Pattern} (firstIn : processes first)
    (secondIn : processes second) :
    frontDoor.ForwardBisimilar isContextLabel first second ↔ SaturatedBisimilar first second := by
  constructor
  · rintro ⟨relation, bisimulation, related⟩
    refine ⟨fun left right => processes left ∧ processes right ∧ relation left right, ?_,
      fun _ _ both => ⟨both.1, both.2.1⟩, firstIn, secondIn, related⟩
    rintro left right ⟨leftIn, rightIn, relatedHere⟩ holeName context admitted
    have labelled := isContextLabel_contextLabel admitted
    refine ⟨fun next step => ?_, fun next step => ?_⟩
    · obtain ⟨matched, step', relatedNext⟩ := bisimulation.forth relatedHere labelled
        ((step_label_iff admitted leftIn).mpr step)
      exact ⟨matched, (step_label_iff admitted rightIn).mp step',
        closedUnder leftIn labelled ((step_label_iff admitted leftIn).mpr step),
        closedUnder rightIn labelled step', relatedNext⟩
    · obtain ⟨matched, step', relatedNext⟩ := bisimulation.back relatedHere labelled
        ((step_label_iff admitted rightIn).mpr step)
      exact ⟨matched, (step_label_iff admitted leftIn).mp step', closedUnder leftIn labelled step',
        closedUnder rightIn labelled ((step_label_iff admitted rightIn).mpr step), relatedNext⟩
  · rintro ⟨relation, saturated, inProcesses, related⟩
    refine ⟨relation, ⟨?_, ?_⟩, related⟩
    · intro left right label next relatedHere labelled step
      obtain ⟨holeName, context, rfl, admitted⟩ := exists_of_isContextLabel labelled
      obtain ⟨leftIn, rightIn⟩ := inProcesses relatedHere
      obtain ⟨matched, step', relatedNext⟩ :=
        (saturated relatedHere holeName context admitted).1 next ((step_label_iff admitted leftIn).mp step)
      exact ⟨matched, (step_label_iff admitted rightIn).mpr step', relatedNext⟩
    · intro left right label next' relatedHere labelled step
      obtain ⟨holeName, context, rfl, admitted⟩ := exists_of_isContextLabel labelled
      obtain ⟨leftIn, rightIn⟩ := inProcesses relatedHere
      obtain ⟨matched, step', relatedNext⟩ :=
        (saturated relatedHere holeName context admitted).2 next' ((step_label_iff admitted rightIn).mp step)
      exact ⟨matched, (step_label_iff admitted leftIn).mpr step', relatedNext⟩

/-- **The front door's two-level context-labelled native types of mobile ambients characterize two-level saturated
reduction bisimilarity.** -/
theorem agree_iff_saturated {first second : Pattern} (firstIn : processes first) (secondIn : processes second) :
    frontDoor.AgreeOn (Formula.forwardOn isContextLabel) first second ↔ SaturatedBisimilar first second :=
  (agree_iff_forwardBisimilar firstIn secondIn).trans (forwardBisimilar_iff_saturated firstIn secondIn)

/-! ## The front door lists the context steps -/

open Mettapedia.Languages.ProcessCalculi.Ambient.Comm (pathNF pathNF_typed isObject_pathNF pathNF_equivalent
  comm_of_core)
open Mettapedia.Languages.ProcessCalculi.Ambient.Steps (pruneTop pruneTop_facts presentation_facts)
open Mettapedia.Languages.ProcessCalculi.Ambient.Full (ambientBlock)

/-- **A presentation of a process is equivalent to it.** -/
theorem presentation_equivalent {state shown : Pattern} (stateIn : processes state)
    (member : shown ∈ presentations state) :
    ObjectEquivalent RelationEnv.empty ambientCommCalc reading state shown := by
  obtain ⟨typed, object⟩ := typed_of_domain stateIn
  unfold presentations at member
  obtain ⟨unpruned, unprunedIn, rfl⟩ := List.mem_map.mp member
  have normalEquivalent := pathNF_equivalent _ (Nat.lt_succ_self _) typed object
  have normalTyped := pathNF_typed (core_typed typed) object
  have normalObject := isObject_pathNF _ object
  obtain ⟨unprunedTyped, unprunedObject, presented⟩ :=
    presentation_facts AmbientCommForms.names_names normalTyped normalObject _ unpruned unprunedIn
  obtain ⟨-, shownObject, pruned⟩ := pruneTop_facts unpruned unprunedTyped unprunedObject
  have chain : ProcEquiv ambientCommCalc ambientBlock names [] state (pruneTop unpruned) :=
    .trans _ _ _ normalEquivalent (comm_of_core (.trans _ _ _ presented pruned))
  exact objectEquivalent_of_objectChain _ (comm_objectChain names_context chain object shownObject)

/-- **A firing of a presentation of the canonical form is a reduction.** -/
theorem reduces_of_listed {source next : Pattern} (sourceIn : processes source)
    (member : next ∈ (presentations (canon source)).flatMap commSuccessors) : Reduces source next := by
  obtain ⟨shown, shownIn, listed⟩ := List.mem_flatMap.mp member
  have canonIn : processes (canon source) := (canonical RelationEnv.empty).admitted_canon sourceIn
  have shownEquivalent := presentation_equivalent canonIn shownIn
  have shownIn' : processes shown := (domain_iff_of_equivalent shownEquivalent).mp canonIn
  have raw : AmbCommRawStep shown next :=
    Mettapedia.Languages.ProcessCalculi.Ambient.Comm.commSuccessors_sound _ (Nat.lt_succ_self _) listed
  obtain ⟨contractumTyped, contractumObject⟩ :=
    Mettapedia.Languages.ProcessCalculi.Ambient.Comm.commStep_typed raw (core_typed (typed_of_domain shownIn').1)
      (typed_of_domain shownIn').2
  have nextIn : processes next := domain_of_typed (comm_typed contractumTyped) contractumObject
  obtain ⟨witness, valid⟩ := step_iff_raw.mpr raw
  exact ⟨isState_of_process sourceIn, isState_of_process nextIn, shown, next, witness,
    .trans _ _ _ ((canonical RelationEnv.empty).equivalent sourceIn) shownEquivalent, isState_of_process shownIn',
    valid, isState_of_process nextIn, .refl _, rfl⟩

/-- **A reduction is matched by a listed firing**: up to the laws, by a firing of a presentation of the canonical form. -/
theorem reduces_matched {source target : Pattern} (sourceIn : processes source)
    (reduces : Reduces source target) :
    ∃ next ∈ (presentations (canon source)).flatMap commSuccessors,
      ObjectEquivalent RelationEnv.empty ambientCommCalc reading next target := by
  obtain ⟨-, -, redex, contractum, witness, before, -, valid, -, after, -⟩ := reduces
  have redexIn : processes redex := (domain_iff_of_equivalent before).mp sourceIn
  have raw := step_iff_raw.mp ⟨witness, valid⟩
  obtain ⟨shown, shownIn, contractum', raw', same⟩ := presented_simulation redexIn raw
  rw [← (canonical RelationEnv.empty).same sourceIn before] at shownIn
  obtain ⟨contractumTyped, contractumObject⟩ :=
    Mettapedia.Languages.ProcessCalculi.Ambient.Comm.commStep_typed raw (core_typed (typed_of_domain redexIn).1)
      (typed_of_domain redexIn).2
  have contractumIn : processes contractum := domain_of_typed (comm_typed contractumTyped) contractumObject
  have contractum'In : processes contractum' := process_of_canon_eq contractumIn same
  refine ⟨contractum', List.mem_flatMap.mpr ⟨shown, shownIn, mem_commSuccessors raw'⟩, ?_⟩
  exact .trans _ _ _ ((canonical RelationEnv.empty).equivalent contractum'In)
    (.trans _ _ _ (same ▸ .symm _ _ ((canonical RelationEnv.empty).equivalent contractumIn)) after)

/-- The listed successors: under a plain label, the firings of the presentations of the canonical form; under the
label of an admitted two-level context, those of the filled context. -/
def successorList : StepLabel → Pattern → Option (List Pattern)
  | .any, term => if domain term then some ((presentations (canon term)).flatMap commSuccessors) else none
  | .context holeName pattern .any, term =>
      match AmbientContext.read? holeName pattern with
      | some context =>
          if context.admits holeName && domain term then
            some ((presentations (canon (context.hole.fill term))).flatMap commSuccessors)
          else none
      | none => none
  | _, _ => none

/-- **The successors of mobile ambients, complete up to the laws**, for plain steps and for steps in two-level
contexts. -/
def successors : Successors RelationEnv.empty ambientCommCalc reading where
  list := successorList
  sound := by
    intro label term next listed target member
    unfold successorList at listed
    split at listed
    · split_ifs at listed with termIn
      cases listed
      exact reduces_of_listed termIn member
    · rename_i holeName pattern
      split at listed
      · rename_i context found
        split_ifs at listed with conditions
        cases listed
        simp only [Bool.and_eq_true] at conditions
        obtain ⟨admitted, termIn⟩ := conditions
        rw [AmbientContext.fill_of_read? found]
        exact (step_label_iff admitted termIn).mpr
          (reduces_of_listed (AmbientContext.fill_process admitted termIn) member)
      · cases listed
    · cases listed
  complete := by
    intro label term next listed target step
    unfold successorList at listed
    split at listed
    · split_ifs at listed with termIn
      cases listed
      exact reduces_matched termIn step
    · rename_i holeName pattern
      split at listed
      · rename_i context found
        split_ifs at listed with conditions
        cases listed
        simp only [Bool.and_eq_true] at conditions
        obtain ⟨admitted, termIn⟩ := conditions
        rw [AmbientContext.fill_of_read? found] at step
        exact reduces_matched (AmbientContext.fill_process admitted termIn) ((step_label_iff admitted termIn).mp step)
      · cases listed
    · cases listed

/-- **The modal decider of mobile ambients**: the step modalities, two-level context labels included, evaluated at the
listed successors, over named terms by canonical forms. -/
def decider : Decider RelationEnv.empty ambientCommCalc reading :=
  modalDecider successors (namedDecider canon domain (canonical RelationEnv.empty))

theorem decided_holds {formula : Formula 0} {term : Pattern} (decided : decider.decide formula term = some true) :
    frontDoor.sat Env.closed formula term :=
  (decider.exact decided).mpr rfl

theorem decided_fails {formula : Formula 0} {term : Pattern} (decided : decider.decide formula term = some false) :
    ¬ frontDoor.sat Env.closed formula term :=
  fun holds => Bool.false_ne_true ((decider.exact decided).mp holds)

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.AmbientContextLabels
