import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CCSCanonicalForms
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.ForwardEquivalence
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.ContextLabels

/-!
# CCS's parallel partners at the front door

A CCS process meets its environment in parallel composition, so the contexts that can enable its steps are its
parallel partners: the context `{□, Q}` with a process `Q` beside the hole, the hole named by a name `Q` does not use
(`partnerLabel`). The front door reads `ccsCalc` modulo its bag, its sums and its restriction laws
(`CCSForms.reading`), and there:

- **A step in a partner's context is a reduction beside the partner** (`step_partner_iff`).
- **Partner steps keep the processes** (`closedUnder`), and **they are finitely many up to the laws**
  (`finiteUpTo`): every reduction beside a partner is matched, up to the laws, by a reaction or a silent step of the
  canonical form of the bag, and a pattern has finitely many of them (`mem_rawSuccessors`).
- So **two processes have the same native types under parallel partners exactly when they are forward bisimilar
  under partners** (`agree_iff_forwardBisimilar`), by the forward Hennessy–Milner theorem.
- **That bisimilarity is CCS's saturated reduction bisimilarity** (`forwardBisimilar_iff_saturated`), so the front
  door's partner-labelled native types characterize it (`agree_iff_saturated`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.CCSPartners

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.OSLF.MeTTaIL.ContextualStep (engineBasePremises)
open Mettapedia.OSLF.MeTTaIL.DerivedContexts (OneHoleContext)
open Mettapedia.OSLF.MeTTaIL.Substitution (freeVars)
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationEquiv equationEquiv_fill)
open Mettapedia.GSLT.LanguageDef.BagNormalForm (isObjectPatternList_iff)
open Mettapedia.Languages.ProcessCalculi.CCS (ccsCalc CCSRawStep)
open Mettapedia.Languages.ProcessCalculi.CCS.Steps (typed_of_raw)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.CCSForms (reading domain canon typed_of_domain domain_of_typed
  canonical admissible_of_typed names names_context domain_iff_of_equivalent equationEquiv_of_objectEquivalent
  reference_iff_raw)

/-! ## The successors of a pattern -/

/-- The reaction of the `first` member of a bag with the `second` of the others, at summand `left` of the first and
summand `right` of the second, when they are an action and the co-action on one name. -/
def reactAt (elements : List Pattern) (first second left right : Nat) : Option Pattern :=
  match elements[first]?, (elements.eraseIdx first)[second]? with
  | some (.apply "CSum" [.collection .hashBag guards _]), some (.apply "CSum" [.collection .hashBag guards' _]) =>
      match guards[left]?, guards'[right]? with
      | some (.apply "CAct" [name, continuation]), some (.apply "CCoAct" [name', continuation']) =>
          if name = name' then
            some (.collection .hashBag (continuation :: continuation' :: (elements.eraseIdx first).eraseIdx second)
              none)
          else none
      | _, _ => none
  | _, _ => none

/-- The number of summands of a sum, and none otherwise. -/
def summands : Pattern → Nat
  | .apply "CSum" [.collection .hashBag guards _] => guards.length
  | _ => 0

/-- The reactions between members of a bag. -/
def reactions (elements : List Pattern) : List Pattern :=
  (List.range elements.length).flatMap fun first =>
    (List.range elements.length).flatMap fun second =>
      (List.range (summands (elements[first]?.getD (.apply "CNil" [])))).flatMap fun left =>
        (List.range (summands ((elements.eraseIdx first)[second]?.getD (.apply "CNil" [])))).filterMap fun right =>
          reactAt elements first second left right

/-- The silent summands of a sum, taken. -/
def silents : List Pattern → List Pattern
  | [] => []
  | .apply "CTau" [continuation] :: guards => continuation :: silents guards
  | _ :: guards => silents guards

mutual
  /-- **The successors of a pattern**, a list holding every target of a step. -/
  def rawSuccessors : Pattern → List Pattern
    | .collection .hashBag elements _ => reactions elements ++ insideSteps [] elements
    | .apply "CSum" [.collection .hashBag guards _] => silents guards
    | .apply "CNu" [.lambda _ body] => (rawSuccessors body).map fun target => .apply "CNu" [.lambda none target]
    | _ => []

  /-- The steps of the members of a bag, the members before them already passed. -/
  def insideSteps (before : List Pattern) : List Pattern → List Pattern
    | [] => []
    | element :: after =>
        (rawSuccessors element).map (fun target => .collection .hashBag (target :: (before ++ after)) none) ++
          insideSteps (before ++ [element]) after
end

theorem mem_insideSteps {target : Pattern} : ∀ (before elements : List Pattern) (index : Nat)
    (inside : index < elements.length), target ∈ rawSuccessors elements[index] →
      .collection .hashBag (target :: (before ++ elements.eraseIdx index)) none ∈ insideSteps before elements
  | _, [], _, inside, _ => absurd inside (by simp)
  | before, element :: after, 0, _, member => by
      simp only [insideSteps, List.mem_append, List.mem_map]
      exact .inl ⟨target, member, by simp⟩
  | before, element :: after, index + 1, inside, member => by
      simp only [insideSteps, List.mem_append]
      refine .inr ?_
      have later := mem_insideSteps (before ++ [element]) after index (by simpa using inside) member
      simpa using later

theorem mem_silents {continuation : Pattern} : ∀ {guards : List Pattern} (index : Nat) (inside : index < guards.length),
    guards[index] = .apply "CTau" [continuation] → continuation ∈ silents guards
  | [], _, inside, _ => absurd inside (by simp)
  | guard :: guards, 0, _, atIndex => by
      simp only [List.getElem_cons_zero] at atIndex
      subst atIndex
      simp [silents]
  | guard :: guards, index + 1, inside, atIndex => by
      have later := mem_silents (guards := guards) index (by simpa using inside) (by simpa using atIndex)
      unfold silents
      split <;> simp_all

/-- **Every target of a step is a successor.** -/
theorem mem_rawSuccessors {source target : Pattern} (step : CCSRawStep source target) :
    target ∈ rawSuccessors source := by
  induction step with
  | @react elements tail first firstInside second secondInside guards guards' sumTail sumTail' left leftInside right
      rightInside name continuation continuation' firstAt secondAt acting coacting =>
      simp only [rawSuccessors, List.mem_append]
      refine .inl ?_
      simp only [reactions, List.mem_flatMap, List.mem_range, List.mem_filterMap]
      refine ⟨first, firstInside, second, Nat.lt_of_lt_of_le secondInside (List.length_eraseIdx_le _ _), left, ?_,
        right, ?_, ?_⟩
      · simp [List.getElem?_eq_getElem firstInside, firstAt, summands, leftInside]
      · simp [List.getElem?_eq_getElem secondInside, secondAt, summands, rightInside]
      · simp [reactAt, List.getElem?_eq_getElem firstInside, List.getElem?_eq_getElem secondInside, firstAt, secondAt,
          List.getElem?_eq_getElem leftInside, List.getElem?_eq_getElem rightInside, acting, coacting]
  | @tau guards sumTail index inside continuation silent =>
      simp only [rawSuccessors]
      exact mem_silents index inside silent
  | @par elements tail index inside target inner recurse =>
      simp only [rawSuccessors, List.mem_append]
      exact .inr (by simpa using mem_insideSteps [] elements index inside recurse)
  | @res binder source target inner recurse =>
      simp only [rawSuccessors, List.mem_map]
      exact ⟨target, recurse, rfl⟩

/-- **A listed reaction is a step.** -/
theorem reactAt_sound {elements : List Pattern} {first second left right : Nat} {target : Pattern}
    (tail : Option String) (listed : reactAt elements first second left right = some target) :
    CCSRawStep (.collection .hashBag elements tail) target := by
  unfold reactAt at listed
  split at listed
  · rename_i guards firstTail guards' secondTail firstIs secondIs
    obtain ⟨firstInside, firstAt⟩ := List.getElem?_eq_some_iff.mp firstIs
    obtain ⟨secondInside, secondAt⟩ := List.getElem?_eq_some_iff.mp secondIs
    split at listed
    · rename_i name continuation name' continuation' leftIs rightIs
      obtain ⟨leftInside, leftAt⟩ := List.getElem?_eq_some_iff.mp leftIs
      obtain ⟨rightInside, rightAt⟩ := List.getElem?_eq_some_iff.mp rightIs
      split_ifs at listed with sameName
      cases listed
      subst sameName
      exact .react first firstInside second secondInside left leftInside right rightInside name continuation
        continuation' firstAt secondAt leftAt rightAt
    · cases listed
  · cases listed

theorem mem_reactions {elements : List Pattern} {target : Pattern} (member : target ∈ reactions elements) :
    ∃ first second left right, reactAt elements first second left right = some target := by
  simp only [reactions, List.mem_flatMap, List.mem_range, List.mem_filterMap] at member
  obtain ⟨first, -, second, -, left, -, right, -, listed⟩ := member
  exact ⟨first, second, left, right, listed⟩

theorem of_mem_silents {continuation : Pattern} : ∀ {guards : List Pattern}, continuation ∈ silents guards →
    ∃ (index : Nat) (inside : index < guards.length), guards[index] = .apply "CTau" [continuation]
  | [], member => by simp [silents] at member
  | guard :: guards, member => by
      have later : continuation ∈ silents guards → ∃ (index : Nat) (inside : index < (guard :: guards).length),
          (guard :: guards)[index] = .apply "CTau" [continuation] := fun member => by
        obtain ⟨index, inside, atIndex⟩ := of_mem_silents member
        exact ⟨index + 1, by simpa using inside, by simpa using atIndex⟩
      unfold silents at member
      split at member
      · simp at member
      · rename_i body rest same
        obtain ⟨rfl, rfl⟩ := List.cons.inj same
        rcases List.mem_cons.mp member with rfl | member
        · exact ⟨0, by simp, rfl⟩
        · exact later member
      · rename_i head rest _ same
        obtain ⟨rfl, rfl⟩ := List.cons.inj same
        exact later member

theorem of_mem_insideSteps {target : Pattern} : ∀ (before elements : List Pattern),
    target ∈ insideSteps before elements → ∃ (index : Nat) (inside : index < elements.length) (inner : Pattern),
      inner ∈ rawSuccessors elements[index] ∧
        target = .collection .hashBag (inner :: (before ++ elements.eraseIdx index)) none
  | _, [], member => by simp [insideSteps] at member
  | before, element :: after, member => by
      simp only [insideSteps, List.mem_append, List.mem_map] at member
      rcases member with ⟨inner, innerMember, rfl⟩ | later
      · exact ⟨0, by simp, inner, innerMember, by simp⟩
      · obtain ⟨index, inside, inner, innerMember, rfl⟩ := of_mem_insideSteps (before ++ [element]) after later
        exact ⟨index + 1, by simpa using inside, inner, innerMember, by simp⟩

/-- **Every successor is the target of a step.** -/
theorem rawSuccessors_sound : ∀ (size : Nat) {source target : Pattern}, sizeOf source < size →
    target ∈ rawSuccessors source → CCSRawStep source target
  | 0, _, _, small, _ => absurd small (Nat.not_lt_zero _)
  | size + 1, source, target, small, member => by
      unfold rawSuccessors at member
      split at member
      · rename_i elements tail
        rcases List.mem_append.mp member with reacted | inside
        · obtain ⟨first, second, left, right, listed⟩ := mem_reactions reacted
          exact reactAt_sound tail listed
        · obtain ⟨index, indexInside, inner, innerMember, rfl⟩ := of_mem_insideSteps [] elements inside
          have smaller : sizeOf elements[index] < size := by
            have inList := List.sizeOf_lt_of_mem (List.getElem_mem indexInside)
            simp only [Pattern.collection.sizeOf_spec] at small
            omega
          simpa using CCSRawStep.par (tail := tail) index indexInside (rawSuccessors_sound size smaller innerMember)
      · rename_i guards sumTail
        obtain ⟨index, inside, atIndex⟩ := of_mem_silents member
        exact .tau index inside target atIndex
      · rename_i binder body
        obtain ⟨inner, innerMember, rfl⟩ := List.mem_map.mp member
        have smaller : sizeOf body < size := by
          simp only [Pattern.apply.sizeOf_spec, List.cons.sizeOf_spec, Pattern.lambda.sizeOf_spec] at small
          omega
        exact .res binder (rawSuccessors_sound size smaller innerMember)
      · simp at member

/-! ## Processes -/

/-- **The front door of CCS**, in its reading. -/
abbrev frontDoor : NativeStructure Pattern := referenceStructure RelationEnv.empty ccsCalc reading

/-- The processes: object processes with no free bound variable, their free variables names. -/
abbrev processes (term : Pattern) : Prop := domain term = true

theorem isState_of_process {term : Pattern} (admitted : processes term) : IsState term :=
  ⟨by simpa using (typed_of_domain admitted).1.isWellScopedAt, (typed_of_domain admitted).2⟩

theorem equivalent_of_canon_eq {first second : Pattern} (firstIn : processes first) (secondIn : processes second)
    (same : canon first = canon second) : ObjectEquivalent RelationEnv.empty ccsCalc reading first second :=
  .trans _ _ _ (canonical.equivalent firstIn) (same ▸ .symm _ _ (canonical.equivalent secondIn))

/-- Parallel composition, as a bag of two. -/
def par (first second : Pattern) : Pattern := .collection .hashBag [first, second] none

theorem par_process {first second : Pattern} (firstIn : processes first) (secondIn : processes second) :
    processes (par first second) := by
  apply domain_of_typed
  · apply Mettapedia.GSLT.LanguageDef.RestrictionBlocks.bag_typed (block := Mettapedia.Languages.ProcessCalculi.CCS.Blocks.ccsBlock) (rest := none)
    intro element member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact (typed_of_domain firstIn).1
    · exact (typed_of_domain secondIn).1
  · simp [par, isObjectPattern, isObjectPatternList, (typed_of_domain firstIn).2, (typed_of_domain secondIn).2]

/-- **Equivalent processes beside one partner are equivalent.** -/
theorem par_congr {first first' partner : Pattern} (firstIn : processes first) (firstIn' : processes first')
    (partnerIn : processes partner) (equivalent : ObjectEquivalent RelationEnv.empty ccsCalc reading first first') :
    ObjectEquivalent RelationEnv.empty ccsCalc reading (par first partner) (par first' partner) := by
  refine equivalent_of_canon_eq (par_process firstIn partnerIn) (par_process firstIn' partnerIn) ?_
  unfold canon
  rw [if_pos (par_process firstIn partnerIn), if_pos (par_process firstIn' partnerIn)]
  apply Mettapedia.GSLT.LanguageDef.RestrictionBlocks.canon_complete (language := ccsCalc) (block := Mettapedia.Languages.ProcessCalculi.CCS.Blocks.ccsBlock)
    (isState_of_process (par_process firstIn partnerIn)).2
  have inside := equationEquiv_fill (.collection .hashBag [] .hole [partner] none)
    (equationEquiv_of_objectEquivalent equivalent)
  simpa [OneHoleContext.fill, par] using inside

/-! ## Reductions -/

/-- **A reduction**: a plain step of the front door, a step of `ccsCalc` modulo its laws. -/
def Reduces (source target : Pattern) : Prop := frontDoor.step source .any target

theorem process_of_raw {source target : Pattern} (sourceIn : processes source) (step : CCSRawStep source target) :
    processes target := by
  obtain ⟨steppedTyped, steppedObject⟩ := typed_of_raw step (typed_of_domain sourceIn).1 (typed_of_domain sourceIn).2
  exact domain_of_typed steppedTyped steppedObject

theorem reduces_process {source target : Pattern} (sourceIn : processes source) (step : Reduces source target) :
    processes target := by
  obtain ⟨-, -, redex, contractum, witness, before, -, valid, -, after, -⟩ := step
  have redexIn := (domain_iff_of_equivalent before).mp sourceIn
  have contractumIn := process_of_raw redexIn (reference_iff_raw.mp ⟨witness, valid⟩)
  exact (domain_iff_of_equivalent after).mp contractumIn

/-- **A reduction is matched by a reaction or silent step of the canonical form**, to a process with the same canonical form. -/
theorem reduces_canonical {source target : Pattern} (sourceIn : processes source) (step : Reduces source target) :
    ∃ next ∈ rawSuccessors (canon source), Reduces source next ∧
      ObjectEquivalent RelationEnv.empty ccsCalc reading target next := by
  obtain ⟨sourceState, targetState, redex, contractum, witness, before, redexState, valid, contractumState, after,
    -⟩ := step
  have redexIn := (domain_iff_of_equivalent before).mp sourceIn
  have raw := reference_iff_raw.mp ⟨witness, valid⟩
  obtain ⟨next, raw', same⟩ := Mettapedia.Languages.ProcessCalculi.CCS.Steps.simulation names_context raw
    (typed_of_domain redexIn).1 (typed_of_domain redexIn).2
  have canonSame : canon redex = canon source := (canonical.same sourceIn before).symm
  have canonIs : canon source = Mettapedia.GSLT.LanguageDef.RestrictionBlocks.canon Mettapedia.Languages.ProcessCalculi.CCS.Blocks.ccsBlock redex := by
    rw [← canonSame]
    unfold canon
    rw [if_pos redexIn]
  have canonIn : processes (canon source) := canonical.admitted_canon sourceIn
  have nextIn : processes next := process_of_raw canonIn (by rw [canonIs]; exact raw')
  have contractumIn := process_of_raw redexIn raw
  obtain ⟨witness', valid'⟩ := reference_iff_raw.mpr (show CCSRawStep (canon source) next by rw [canonIs]; exact raw')
  refine ⟨next, mem_rawSuccessors (by rw [canonIs]; exact raw'), ?_, ?_⟩
  · exact ⟨sourceState, isState_of_process nextIn, canon source, next, witness', canonical.equivalent sourceIn,
      isState_of_process canonIn, valid', isState_of_process nextIn, .refl _, rfl⟩
  · refine .trans _ _ _ (.symm _ _ after) (equivalent_of_canon_eq contractumIn nextIn ?_)
    unfold canon
    rw [if_pos contractumIn, if_pos nextIn]
    exact same.symm

/-! ## Partners -/

/-- **A partner's context**: the hole, named `hole`, beside the partner. -/
def partnerContext (hole : String) (partner : Pattern) : Pattern := .collection .hashBag [.fvar hole, partner] none

/-- **The label of a partner**: a step of the process beside the partner. -/
abbrev partnerLabel (hole : String) (partner : Pattern) : StepLabel := .context hole (partnerContext hole partner) .any

/-- **Whether a label is a partner's**: a context label whose context is a process beside the hole, the process
not using the hole's name, read plainly. -/
def isPartnerLabel : StepLabel → Bool
  | .context hole (.collection .hashBag [.fvar hole', partner] none) .any =>
    hole == hole' && avoidsHole hole partner && domain partner
  | _ => false

theorem isPartnerLabel_partnerLabel {hole : String} {partner : Pattern} (avoids : avoidsHole hole partner = true)
    (partnerIn : processes partner) : isPartnerLabel (partnerLabel hole partner) = true := by
  simp [isPartnerLabel, partnerLabel, partnerContext, avoids, partnerIn]

theorem exists_of_isPartnerLabel {label : StepLabel} (partnerOf : isPartnerLabel label = true) :
    ∃ hole partner, label = partnerLabel hole partner ∧ avoidsHole hole partner = true ∧ processes partner := by
  match label, partnerOf with
  | .context hole (.collection .hashBag [.fvar hole', partner] none) .any, partnerOf =>
    simp only [isPartnerLabel, Bool.and_eq_true, beq_iff_eq] at partnerOf
    obtain ⟨⟨rfl, avoids⟩, admitted⟩ := partnerOf
    exact ⟨hole, partner, rfl, avoids, admitted⟩

/-- **Placing a process beside the partner is their parallel composition.** -/
theorem plug_partner {hole : String} {partner source : Pattern} (avoids : avoidsHole hole partner = true)
    (closed : source.isWellScopedAt 0 = true) : plug hole (partnerContext hole partner) source = par source partner := by
  have filled := plug_fill (hole := hole) (.collection .hashBag [] .hole [partner] none)
    (by simp [contextAvoidsHole, avoidsHoleList, avoids]) closed
  simpa [OneHoleContext.fill, partnerContext, par] using filled

/-- **A step in a partner's context is a reduction beside the partner.** -/
theorem step_partner_iff {hole : String} {partner source target : Pattern} (avoids : avoidsHole hole partner = true)
    (partnerIn : processes partner) (sourceIn : processes source) :
    frontDoor.step source (partnerLabel hole partner) target ↔ Reduces (par source partner) target := by
  rw [step_context_iff]
  constructor
  · rintro ⟨-, presentation, presents, presentationState, step⟩
    have presentationIn := (domain_iff_of_equivalent presents).mp sourceIn
    rw [plug_partner avoids presentationState.1] at step
    have equivalent := par_congr presentationIn sourceIn partnerIn (.symm _ _ presents)
    exact (referenceStructure_saturated RelationEnv.empty ccsCalc reading).stepSource
      (Indistinct.of_states (isState_of_process (par_process presentationIn partnerIn))
        (isState_of_process (par_process sourceIn partnerIn)) equivalent) step
  · intro step
    refine ⟨isState_of_process sourceIn, source, .refl _, isState_of_process sourceIn, ?_⟩
    rw [plug_partner avoids (isState_of_process sourceIn).1]
    exact step

/-! ## Finitely many partner steps, keeping the processes -/

/-- **Partner steps keep the processes.** -/
theorem closedUnder : frontDoor.ClosedUnder isPartnerLabel processes := by
  intro source label target sourceIn partnerOf step
  obtain ⟨hole, partner, rfl, avoids, partnerIn⟩ := exists_of_isPartnerLabel partnerOf
  exact reduces_process (par_process sourceIn partnerIn) ((step_partner_iff avoids partnerIn sourceIn).mp step)

/-- **Partner steps are finitely many up to the laws**: the reactions and silent steps of the canonical form of the bag. -/
theorem finiteUpTo : frontDoor.FiniteUpTo isPartnerLabel processes (Indistinct RelationEnv.empty ccsCalc reading) := by
  classical
  intro source sourceIn label partnerOf
  obtain ⟨hole, partner, rfl, avoids, partnerIn⟩ := exists_of_isPartnerLabel partnerOf
  have bagIn := par_process sourceIn partnerIn
  refine ⟨(rawSuccessors (canon (par source partner))).filter
    (fun next => decide (frontDoor.step source (partnerLabel hole partner) next)), ?_, ?_⟩
  · intro listed member
    exact of_decide_eq_true (List.mem_filter.mp member).2
  · intro target step
    have reduction := (step_partner_iff avoids partnerIn sourceIn).mp step
    obtain ⟨next, member, nextStep, equivalent⟩ := reduces_canonical bagIn reduction
    have targetIn := reduces_process bagIn reduction
    have nextIn := reduces_process bagIn nextStep
    refine ⟨next, List.mem_filter.mpr ⟨member, decide_eq_true ((step_partner_iff avoids partnerIn sourceIn).mpr
      nextStep)⟩, Indistinct.of_states (isState_of_process targetIn) (isState_of_process nextIn) equivalent⟩

/-! ## The characterization -/

/-- **Two processes have the same native types under parallel partners exactly when they are forward bisimilar
under partners.** -/
theorem agree_iff_forwardBisimilar {first second : Pattern} (firstIn : processes first) (secondIn : processes second) :
    frontDoor.AgreeOn (Formula.forwardOn isPartnerLabel) first second ↔
      frontDoor.ForwardBisimilar isPartnerLabel first second :=
  NativeStructure.agree_iff_forwardBisimilar (referenceStructure_saturated RelationEnv.empty ccsCalc reading)
    finiteUpTo closedUnder firstIn secondIn

/-- **A saturated reduction bisimulation** of CCS's processes: beside every process, a reduction of either side is
matched by one of the other, to related processes. -/
def IsSaturatedReduction (relation : Pattern → Pattern → Prop) : Prop :=
  ∀ ⦃first second⦄, relation first second → ∀ partner, processes partner →
    (∀ next, Reduces (par first partner) next → ∃ matched, Reduces (par second partner) matched ∧ relation next matched) ∧
    (∀ next, Reduces (par second partner) next → ∃ matched, Reduces (par first partner) matched ∧ relation matched next)

/-- **Saturated reduction bisimilarity** of CCS's processes. -/
def SaturatedReductionBisimilar (first second : Pattern) : Prop :=
  ∃ relation, IsSaturatedReduction relation ∧ (∀ ⦃left right⦄, relation left right → processes left ∧ processes right) ∧
    relation first second

theorem avoidsHole_of_not_mem {hole : String} (pattern : Pattern) (object : isObjectPattern pattern = true)
    (absent : hole ∉ freeVars pattern) : avoidsHole hole pattern = true := by
  induction pattern using Pattern.inductionOn with
  | hbvar => rfl
  | hfvar name =>
      simp only [freeVars, List.mem_singleton] at absent
      simp only [avoidsHole, bne_iff_ne, ne_eq]
      exact fun same => absent same.symm
  | happly label arguments recurse =>
      simp only [freeVars, List.mem_flatMap, not_exists, not_and] at absent
      simp only [isObjectPattern, isObjectPatternList_iff] at object
      simp only [avoidsHole, avoidsHoleList_iff]
      exact fun argument member => recurse argument member (object argument member) (absent argument member)
  | hlambda binder body recurse =>
      simp only [freeVars] at absent
      simp only [isObjectPattern] at object
      simpa [avoidsHole] using recurse object absent
  | hmultiLambda arity binders body recurse =>
      simp only [freeVars] at absent
      simp only [isObjectPattern] at object
      simpa [avoidsHole] using recurse object absent
  | hsubst => simp [isObjectPattern] at object
  | hcollection kind elements rest recurse =>
      simp only [freeVars, List.mem_flatMap, not_exists, not_and] at absent
      simp only [isObjectPattern, Bool.and_eq_true, isObjectPatternList_iff, Option.isNone_iff_eq_none] at object
      obtain ⟨rfl, object⟩ := object
      simp only [avoidsHole, avoidsHoleList_iff, Bool.and_eq_true, bne_iff_ne, ne_eq, reduceCtorEq, not_false_eq_true,
        and_true]
      exact fun element member => recurse element member (object element member) (absent element member)

/-- Every process has a hole name it does not use. -/
theorem exists_hole {partner : Pattern} (partnerIn : processes partner) : ∃ hole, avoidsHole hole partner = true := by
  obtain ⟨hole, absent⟩ := Infinite.exists_notMem_finset (freeVars partner).toFinset
  exact ⟨hole, avoidsHole_of_not_mem partner (typed_of_domain partnerIn).2 (fun member =>
    absent (List.mem_toFinset.mpr member))⟩

/-- **Forward bisimilarity under partners is CCS's saturated reduction bisimilarity.** -/
theorem forwardBisimilar_iff_saturated {first second : Pattern} (firstIn : processes first) (secondIn : processes second) :
    frontDoor.ForwardBisimilar isPartnerLabel first second ↔ SaturatedReductionBisimilar first second := by
  constructor
  · rintro ⟨relation, bisimulation, related⟩
    refine ⟨fun left right => processes left ∧ processes right ∧ relation left right, ?_, fun _ _ both => ⟨both.1, both.2.1⟩,
      firstIn, secondIn, related⟩
    rintro left right ⟨leftIn, rightIn, relatedHere⟩ partner partnerIn
    obtain ⟨hole, avoids⟩ := exists_hole partnerIn
    have admitted := isPartnerLabel_partnerLabel avoids partnerIn
    refine ⟨fun next step => ?_, fun next step => ?_⟩
    · obtain ⟨matched, step', relatedNext⟩ := bisimulation.forth relatedHere admitted
        ((step_partner_iff avoids partnerIn leftIn).mpr step)
      exact ⟨matched, (step_partner_iff avoids partnerIn rightIn).mp step',
        closedUnder leftIn admitted ((step_partner_iff avoids partnerIn leftIn).mpr step),
        closedUnder rightIn admitted step', relatedNext⟩
    · obtain ⟨matched, step', relatedNext⟩ := bisimulation.back relatedHere admitted
        ((step_partner_iff avoids partnerIn rightIn).mpr step)
      exact ⟨matched, (step_partner_iff avoids partnerIn leftIn).mp step',
        closedUnder leftIn admitted step', closedUnder rightIn admitted ((step_partner_iff avoids partnerIn rightIn).mpr
          step), relatedNext⟩
  · rintro ⟨relation, saturated, inProcesses, related⟩
    refine ⟨relation, ⟨?_, ?_⟩, related⟩
    · intro left right label next relatedHere partnerOf step
      obtain ⟨hole, partner, rfl, avoids, partnerIn⟩ := exists_of_isPartnerLabel partnerOf
      obtain ⟨leftIn, rightIn⟩ := inProcesses relatedHere
      obtain ⟨matched, step', relatedNext⟩ :=
        (saturated relatedHere partner partnerIn).1 next ((step_partner_iff avoids partnerIn leftIn).mp step)
      exact ⟨matched, (step_partner_iff avoids partnerIn rightIn).mpr step', relatedNext⟩
    · intro left right label next' relatedHere partnerOf step
      obtain ⟨hole, partner, rfl, avoids, partnerIn⟩ := exists_of_isPartnerLabel partnerOf
      obtain ⟨leftIn, rightIn⟩ := inProcesses relatedHere
      obtain ⟨matched, step', relatedNext⟩ :=
        (saturated relatedHere partner partnerIn).2 next' ((step_partner_iff avoids partnerIn rightIn).mp step)
      exact ⟨matched, (step_partner_iff avoids partnerIn leftIn).mpr step', relatedNext⟩

/-- **The front door's partner-labelled native types of CCS characterize its saturated reduction bisimilarity**: two
processes satisfy the same forward formulas under parallel partners exactly when, beside every process, each one's
reductions are matched by the other's. -/
theorem agree_iff_saturated {first second : Pattern} (firstIn : processes first) (secondIn : processes second) :
    frontDoor.AgreeOn (Formula.forwardOn isPartnerLabel) first second ↔ SaturatedReductionBisimilar first second :=
  (agree_iff_forwardBisimilar firstIn secondIn).trans (forwardBisimilar_iff_saturated firstIn secondIn)


/-! ## The front door lists CCS's successors -/

/-- **A successor of the canonical form is a reduction's target.** -/
theorem reduces_of_listed {source next : Pattern} (sourceIn : processes source)
    (member : next ∈ rawSuccessors (canon source)) : Reduces source next := by
  have raw := rawSuccessors_sound _ (Nat.lt_succ_self _) member
  have canonIn : processes (canon source) := canonical.admitted_canon sourceIn
  have nextIn := process_of_raw canonIn raw
  obtain ⟨witness, valid⟩ := reference_iff_raw.mpr raw
  exact ⟨isState_of_process sourceIn, isState_of_process nextIn, canon source, next, witness,
    canonical.equivalent sourceIn, isState_of_process canonIn, valid, isState_of_process nextIn, .refl _, rfl⟩

/-- The listed successors: under a plain label, the reactions and silent steps of the canonical form; under a partner's label,
those of the canonical form of the bag with the partner. -/
def successorList : StepLabel → Pattern → Option (List Pattern)
  | .any, term => if domain term then some (rawSuccessors (canon term)) else none
  | .context hole (.collection .hashBag [.fvar hole', partner] none) .any, term =>
      if hole == hole' && avoidsHole hole partner && domain partner && domain term then
        some (rawSuccessors (canon (par term partner)))
      else none
  | _, _ => none

/-- **CCS's successors, complete up to the laws** for plain steps and for partners' steps. -/
def successors : Successors RelationEnv.empty ccsCalc reading where
  list := successorList
  sound := by
    intro label term next listed target member
    unfold successorList at listed
    split at listed
    · split_ifs at listed with termIn
      cases listed
      exact reduces_of_listed termIn member
    · rename_i hole hole' partner
      split_ifs at listed with conditions
      cases listed
      simp only [Bool.and_eq_true, beq_iff_eq] at conditions
      obtain ⟨⟨⟨rfl, avoids⟩, partnerIn⟩, termIn⟩ := conditions
      exact (step_partner_iff avoids partnerIn termIn).mpr (reduces_of_listed (par_process termIn partnerIn) member)
    · cases listed
  complete := by
    intro label term next listed target step
    unfold successorList at listed
    split at listed
    · split_ifs at listed with termIn
      cases listed
      obtain ⟨next', member, -, equivalent⟩ := reduces_canonical termIn step
      exact ⟨next', member, .symm _ _ equivalent⟩
    · rename_i hole hole' partner
      split_ifs at listed with conditions
      cases listed
      simp only [Bool.and_eq_true, beq_iff_eq] at conditions
      obtain ⟨⟨⟨rfl, avoids⟩, partnerIn⟩, termIn⟩ := conditions
      obtain ⟨next', member, -, equivalent⟩ :=
        reduces_canonical (par_process termIn partnerIn) ((step_partner_iff avoids partnerIn termIn).mp step)
      exact ⟨next', member, .symm _ _ equivalent⟩
    · cases listed

/-- **CCS's modal decider**: the step modalities, partners' labels included, evaluated at the listed successors, over
named terms by canonical forms. -/
def decider : Decider RelationEnv.empty ccsCalc reading :=
  modalDecider successors (namedDecider canon domain canonical)

theorem decided_holds {formula : Formula 0} {term : Pattern} (decided : decider.decide formula term = some true) :
    frontDoor.sat Env.closed formula term :=
  (decider.exact decided).mpr rfl

theorem decided_fails {formula : Formula 0} {term : Pattern} (decided : decider.decide formula term = some false) :
    ¬ frontDoor.sat Env.closed formula term :=
  fun holds => Bool.false_ne_true ((decider.exact decided).mp holds)

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.CCSPartners
