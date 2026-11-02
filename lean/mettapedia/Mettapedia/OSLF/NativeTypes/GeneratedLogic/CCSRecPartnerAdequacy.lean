import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CCSRecPartners
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CCSPartnerAdequacy

/-!
# Parallel partners of CCS with recursion at the front door

The contexts that can enable a step of a process of `ccsRecCalc` are its parallel partners: the context `{□, Q}` with a
process `Q` beside the hole, the hole named by a name `Q` does not use (`partnerLabel`). In the environment of any
admitted definitions:

- **A step in a partner's context is a reduction beside the partner** (`step_partner_iff`).
- **Partner steps keep the processes** (`closedUnder`), and **they are finitely many up to the laws** (`finiteUpTo`):
  every reduction beside a partner is matched, up to the laws, by a successor of the canonical form of the bag, and a
  pattern's successors are listed (`mem_recSuccessors`): its silent summands and the silent summands of a call's body,
  the reactions of two offering members of a bag, and the steps inside a bag and under a restriction.
- So **two processes have the same native types under parallel partners exactly when they are forward bisimilar
  under partners** (`agree_iff_forwardBisimilar`), and **that is saturated reduction bisimilarity**
  (`agree_iff_saturated`).

With recursion that equivalence is strictly coarser than strong bisimilarity (`CCSRecPartnerControls`): a silent
loop answers every reduction beside a partner. Strong bisimilarity is characterized by the least partners with a
fresh sentinel (`leastPartnerBisimilar_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.CCSRecPartners

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts (OneHoleContext)
open Mettapedia.OSLF.MeTTaIL.Substitution (freeVars)
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationEquiv equationEquiv_fill)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks
open Mettapedia.Languages.ProcessCalculi.CCS.Blocks (ccsBlock)
open Mettapedia.Languages.ProcessCalculi.CCS.Recursive
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.CCSRecForms (reading domain typed_of_domain domain_of_typed names
  names_context domain_iff_of_equivalent equationEquiv_of_objectEquivalent objectEquivalent_of_sortedEquiv
  reference_iff_raw)

variable {definitions : List Definition}

/-! ## The successors of a pattern -/

/-- The summands a component offers, none if it offers none. -/
def offered (definitions : List Definition) (component : Pattern) : List Pattern :=
  (offers definitions component).getD []

/-- The continuations of the silent summands a component offers. -/
def silentsOf (definitions : List Definition) (component : Pattern) : List Pattern :=
  (offered definitions component).filterMap fun guard =>
    match guard with
    | .apply "CTau" [continuation] => some continuation
    | _ => none

/-- The reaction of an action and a co-action, if the guards are such on one name. -/
def reactPair (rest : List Pattern) : Option Pattern → Option Pattern → Option Pattern
  | some (.apply "CAct" [name, continuation]), some (.apply "CCoAct" [name', continuation']) =>
      if name = name' then some (.collection .hashBag (continuation :: continuation' :: rest) none) else none
  | _, _ => none

/-- The reactions between offering members of a bag. -/
def reactions (definitions : List Definition) (elements : List Pattern) : List Pattern :=
  (List.range elements.length).flatMap fun first =>
    (List.range (elements.length - 1)).flatMap fun second =>
      (List.range (offered definitions (elements.getD first (.apply "CNil" []))).length).flatMap fun left =>
        (List.range (offered definitions ((elements.eraseIdx first).getD second (.apply "CNil" []))).length).filterMap
          fun right => reactPair ((elements.eraseIdx first).eraseIdx second)
            (offered definitions (elements.getD first (.apply "CNil" [])))[left]?
            (offered definitions ((elements.eraseIdx first).getD second (.apply "CNil" [])))[right]?

mutual
  /-- **The successors of a pattern**, a list holding every target of a step. -/
  def recSuccessors (definitions : List Definition) (source : Pattern) : List Pattern :=
    silentsOf definitions source ++
      match source with
      | .collection .hashBag elements _ => reactions definitions elements ++ insideSteps definitions [] elements
      | .apply "CNu" [.lambda _ body] =>
          (recSuccessors definitions body).map fun target => .apply "CNu" [.lambda none target]
      | _ => []

  /-- The steps of the members of a bag, the members before them already passed. -/
  def insideSteps (definitions : List Definition) (before : List Pattern) : List Pattern → List Pattern
    | [] => []
    | element :: after =>
        (recSuccessors definitions element).map (fun target => .collection .hashBag (target :: (before ++ after)) none) ++
          insideSteps definitions (before ++ [element]) after
end

theorem mem_insideSteps {target : Pattern} : ∀ (before elements : List Pattern) (index : Nat)
    (inside : index < elements.length), target ∈ recSuccessors definitions elements[index] →
      .collection .hashBag (target :: (before ++ elements.eraseIdx index)) none ∈ insideSteps definitions before elements
  | _, [], _, inside, _ => absurd inside (by simp)
  | before, element :: after, 0, _, member => by
      simp only [insideSteps, List.mem_append, List.mem_map]
      exact .inl ⟨target, member, by simp⟩
  | before, element :: after, index + 1, inside, member => by
      simp only [insideSteps, List.mem_append]
      refine .inr ?_
      have later := mem_insideSteps (before ++ [element]) after index (by simpa using inside) member
      simpa using later

theorem offered_eq {component : Pattern} {guards : List Pattern} (found : offers definitions component = some guards) :
    offered definitions component = guards := by
  simp [offered, found]

/-- **Every target of a step is a successor.** -/
theorem mem_recSuccessors {source target : Pattern} (step : RecRawStep definitions source target) :
    target ∈ recSuccessors definitions source := by
  induction step with
  | @react elements tail i hi j hj guards guards' k hk l hl name continuation continuation' first second acting
      coacting =>
      rw [recSuccessors]
      refine List.mem_append_right _ (List.mem_append_left _ ?_)
      have firstIs : elements.getD i (.apply "CNil" []) = elements[i] := List.getD_eq_getElem _ _ hi
      have secondIs : (elements.eraseIdx i).getD j (.apply "CNil" []) = (elements.eraseIdx i)[j] :=
        List.getD_eq_getElem _ _ hj
      have hj' : j < elements.length - 1 := by simpa [List.length_eraseIdx_of_lt hi] using hj
      simp only [reactions, List.mem_flatMap, List.mem_range, List.mem_filterMap]
      refine ⟨i, hi, j, hj', k, ?_, l, ?_, ?_⟩
      · rw [firstIs, offered_eq first]; exact hk
      · rw [secondIs, offered_eq second]; exact hl
      · rw [firstIs, secondIs, offered_eq first, offered_eq second, List.getElem?_eq_getElem hk,
          List.getElem?_eq_getElem hl, acting, coacting]
        simp [reactPair]
  | @tau source guards k hk continuation offeredHere silent =>
      unfold recSuccessors
      refine List.mem_append_left _ ?_
      simp only [silentsOf, offered_eq offeredHere, List.mem_filterMap]
      exact ⟨guards[k], List.getElem_mem hk, by simp [silent]⟩
  | @par elements tail i hi target inner recurse =>
      rw [recSuccessors]
      refine List.mem_append_right _ ?_
      simp only [List.mem_append]
      exact .inr (by simpa using mem_insideSteps (definitions := definitions) [] elements i hi recurse)
  | @res binder source target inner recurse =>
      rw [recSuccessors]
      refine List.mem_append_right _ ?_
      simp only [List.mem_map]
      exact ⟨target, recurse, rfl⟩

/-! ## Every successor is a step's target -/

theorem offers_of_offered {component : Pattern} {index : Nat} (inside : index < (offered definitions component).length) :
    offers definitions component = some (offered definitions component) := by
  unfold offered at inside ⊢
  cases found : offers definitions component with
  | none => simp [found] at inside
  | some guards => rfl

theorem getD_of_lt {list : List Pattern} {index : Nat} (fallback : Pattern) (inside : index < list.length) :
    list.getD index fallback = list[index] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inside]

theorem reactPair_sound {elements : List Pattern} {tail : Option String} {first second left right : Nat}
    (hi : first < elements.length) (hj : second < (elements.eraseIdx first).length)
    (hk : left < (offered definitions elements[first]).length)
    (hl : right < (offered definitions (elements.eraseIdx first)[second]).length) {target : Pattern}
    (listed : reactPair ((elements.eraseIdx first).eraseIdx second) (offered definitions elements[first])[left]?
      (offered definitions (elements.eraseIdx first)[second])[right]? = some target) :
    RecRawStep definitions (.collection .hashBag elements tail) target := by
  rw [List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hl] at listed
  unfold reactPair at listed
  split at listed
  · rename_i name continuation name' continuation' acting coacting
    split_ifs at listed with same
    cases listed
    subst same
    exact .react first hi second hj left hk right hl name continuation continuation' (offers_of_offered hk)
      (offers_of_offered hl) (Option.some.inj acting) (Option.some.inj coacting)
  · cases listed

theorem of_mem_silentsOf {component continuation : Pattern} (member : continuation ∈ silentsOf definitions component) :
    RecRawStep definitions component continuation := by
  unfold silentsOf at member
  obtain ⟨guard, guardIn, taken⟩ := List.mem_filterMap.mp member
  obtain ⟨index, inside, rfl⟩ := List.getElem_of_mem guardIn
  split at taken
  · rename_i inner silent
    cases taken
    exact .tau index inside _ (offers_of_offered inside) silent
  · cases taken

theorem of_mem_insideSteps {target : Pattern} : ∀ (before elements : List Pattern),
    target ∈ insideSteps definitions before elements → ∃ (index : Nat) (inside : index < elements.length) (inner : Pattern),
      inner ∈ recSuccessors definitions elements[index] ∧
        target = .collection .hashBag (inner :: (before ++ elements.eraseIdx index)) none
  | _, [], member => by simp [insideSteps] at member
  | before, element :: after, member => by
      simp only [insideSteps, List.mem_append, List.mem_map] at member
      rcases member with ⟨inner, innerMember, rfl⟩ | later
      · exact ⟨0, by simp, inner, innerMember, by simp⟩
      · obtain ⟨index, inside, inner, innerMember, rfl⟩ := of_mem_insideSteps (before ++ [element]) after later
        exact ⟨index + 1, by simpa using inside, inner, innerMember, by simp⟩

/-- **Every successor is the target of a step.** -/
theorem recSuccessors_sound : ∀ (size : Nat) {source target : Pattern}, sizeOf source < size →
    target ∈ recSuccessors definitions source → RecRawStep definitions source target
  | 0, _, _, small, _ => absurd small (Nat.not_lt_zero _)
  | size + 1, source, target, small, member => by
      unfold recSuccessors at member
      rcases List.mem_append.mp member with silent | structural
      · exact of_mem_silentsOf silent
      · split at structural
        · rename_i elements tail
          rcases List.mem_append.mp structural with reacted | inside
          · simp only [reactions, List.mem_flatMap, List.mem_range, List.mem_filterMap] at reacted
            obtain ⟨first, hi, second, hj', left, hk, right, hl, listed⟩ := reacted
            have hj : second < (elements.eraseIdx first).length := by
              simpa [List.length_eraseIdx_of_lt hi] using hj'
            rw [getD_of_lt _ hi] at hk listed
            rw [getD_of_lt _ hj] at hl listed
            exact reactPair_sound hi hj hk hl listed
          · obtain ⟨index, indexInside, inner, innerMember, rfl⟩ := of_mem_insideSteps [] elements inside
            have smaller : sizeOf elements[index] < size := by
              have inList := List.sizeOf_lt_of_mem (List.getElem_mem indexInside)
              simp only [Pattern.collection.sizeOf_spec] at small
              omega
            simpa using RecRawStep.par (tail := tail) index indexInside (recSuccessors_sound size smaller innerMember)
        · rename_i binder body
          obtain ⟨inner, innerMember, rfl⟩ := List.mem_map.mp structural
          have smaller : sizeOf body < size := by
            simp only [Pattern.apply.sizeOf_spec, List.cons.sizeOf_spec, Pattern.lambda.sizeOf_spec] at small
            omega
          exact .res binder (recSuccessors_sound size smaller innerMember)
        · simp at structural

/-! ## Reductions through the canonical form -/

/-- **A reduction is matched by a successor of the canonical form**, which is a reduction's target with the same
canonical form. -/
theorem reduces_canonical (admitted : admits definitions = true) {source target : Pattern} (sourceIn : processes source)
    (reduces : Reduces definitions source target) :
    ∃ next ∈ recSuccessors definitions (blockCanon source), Reduces definitions source next ∧
      ObjectEquivalent (definitionsEnv definitions) ccsRecCalc reading target next := by
  have targetIn := reduces_process admitted sourceIn reduces
  obtain ⟨-, -, redex, contractum, witness, before, -, valid, -, after, -⟩ := reduces
  have redexIn : processes redex := (domain_iff_of_equivalent before).mp sourceIn
  have raw := reference_iff_raw.mp ⟨witness, valid⟩
  obtain ⟨next, raw', same⟩ := simulation admitted names_context raw (typed_of_domain redexIn).1
    (typed_of_domain redexIn).2
  have canonSame : blockCanon redex = blockCanon source := (canon_eq_of_equivalent sourceIn before).symm
  obtain ⟨sourceTyped, sourceObject⟩ := typed_of_domain sourceIn
  obtain ⟨canonTyped, canonEquivalent⟩ := canon_sound (block := ccsBlock) names_context sourceTyped
  have canonObject : isObjectPattern (blockCanon source) = true := by
    rw [← equationEquiv_isObject (block := ccsBlock) canonEquivalent.toEquationEquiv]; exact sourceObject
  have canonIn : processes (blockCanon source) := domain_of_typed canonTyped canonObject
  have canonSame' : Mettapedia.GSLT.LanguageDef.RestrictionBlocks.canon ccsBlock redex =
      Mettapedia.GSLT.LanguageDef.RestrictionBlocks.canon ccsBlock source := canonSame
  rw [canonSame'] at raw'
  obtain ⟨nextTyped, nextObject⟩ := typed_of_raw admitted raw' canonTyped canonObject
  have nextIn : processes next := domain_of_typed nextTyped nextObject
  obtain ⟨contractumTyped, contractumObject⟩ :=
    typed_of_raw admitted raw (typed_of_domain redexIn).1 (typed_of_domain redexIn).2
  have contractumIn : processes contractum := domain_of_typed contractumTyped contractumObject
  obtain ⟨witness', valid'⟩ := reference_iff_raw.mpr raw'
  refine ⟨next, mem_recSuccessors raw', ⟨isState_of_process sourceIn, isState_of_process nextIn, _, next, witness',
    objectEquivalent_of_sortedEquiv _ canonEquivalent sourceObject, isState_of_process canonIn, valid',
    isState_of_process nextIn, .refl _, rfl⟩, ?_⟩
  exact .trans _ _ _ (.symm _ _ after) (equivalent_of_canon_eq contractumIn nextIn same.symm)

/-! ## Partners -/

/-- **A partner's context**: the hole, named `hole`, beside the partner. -/
def partnerContext (hole : String) (partnerProcess : Pattern) : Pattern :=
  .collection .hashBag [.fvar hole, partnerProcess] none

/-- **The label of a partner**: a step of the process beside the partner. -/
abbrev partnerLabel (hole : String) (partnerProcess : Pattern) : StepLabel :=
  .context hole (partnerContext hole partnerProcess) .any

/-- **Whether a label is a partner's**: a context label whose context is a process beside the hole, the process
not using the hole's name, read plainly. -/
def isPartnerLabel : StepLabel → Bool
  | .context hole (.collection .hashBag [.fvar hole', partnerProcess] none) .any =>
    hole == hole' && avoidsHole hole partnerProcess && domain partnerProcess
  | _ => false

theorem isPartnerLabel_partnerLabel {hole : String} {partnerProcess : Pattern}
    (avoids : avoidsHole hole partnerProcess = true) (partnerIn : processes partnerProcess) :
    isPartnerLabel (partnerLabel hole partnerProcess) = true := by
  simp [isPartnerLabel, partnerLabel, partnerContext, avoids, partnerIn]

theorem exists_of_isPartnerLabel {label : StepLabel} (partnerOf : isPartnerLabel label = true) :
    ∃ hole partnerProcess, label = partnerLabel hole partnerProcess ∧ avoidsHole hole partnerProcess = true ∧
      processes partnerProcess := by
  match label, partnerOf with
  | .context hole (.collection .hashBag [.fvar hole', partnerProcess] none) .any, partnerOf =>
    simp only [isPartnerLabel, Bool.and_eq_true, beq_iff_eq] at partnerOf
    obtain ⟨⟨rfl, avoids⟩, admitted⟩ := partnerOf
    exact ⟨hole, partnerProcess, rfl, avoids, admitted⟩

/-- **Placing a process beside the partner is their parallel composition.** -/
theorem plug_partner {hole : String} {partnerProcess source : Pattern} (avoids : avoidsHole hole partnerProcess = true)
    (closed : source.isWellScopedAt 0 = true) :
    plug hole (partnerContext hole partnerProcess) source = par source partnerProcess := by
  have filled := plug_fill (hole := hole) (.collection .hashBag [] .hole [partnerProcess] none)
    (by simp [contextAvoidsHole, avoidsHoleList, avoids]) closed
  simpa [OneHoleContext.fill, partnerContext, par] using filled

/-- **Equivalent processes beside one partner are equivalent.** -/
theorem par_congr {first first' partnerProcess : Pattern} (firstIn : processes first) (firstIn' : processes first')
    (partnerIn : processes partnerProcess)
    (equivalent : ObjectEquivalent (definitionsEnv definitions) ccsRecCalc reading first first') :
    ObjectEquivalent (definitionsEnv definitions) ccsRecCalc reading (par first partnerProcess)
      (par first' partnerProcess) := by
  refine equivalent_of_canon_eq (par_process firstIn partnerIn) (par_process firstIn' partnerIn) ?_
  apply canon_complete (language := ccsRecCalc) (block := ccsBlock) (isState_of_process (par_process firstIn partnerIn)).2
  have inside := equationEquiv_fill (.collection .hashBag [] .hole [partnerProcess] none)
    (equationEquiv_of_objectEquivalent equivalent)
  simpa [OneHoleContext.fill, par] using inside

/-- **A step in a partner's context is a reduction beside the partner.** -/
theorem step_partner_iff {hole : String} {partnerProcess source target : Pattern}
    (avoids : avoidsHole hole partnerProcess = true) (partnerIn : processes partnerProcess)
    (sourceIn : processes source) :
    (frontDoor definitions).step source (partnerLabel hole partnerProcess) target ↔
      Reduces definitions (par source partnerProcess) target := by
  rw [step_context_iff]
  constructor
  · rintro ⟨-, presentation, presents, presentationState, step⟩
    have presentationIn := (domain_iff_of_equivalent presents).mp sourceIn
    rw [plug_partner avoids presentationState.1] at step
    have equivalent := par_congr presentationIn sourceIn partnerIn (.symm _ _ presents)
    exact (referenceStructure_saturated (definitionsEnv definitions) ccsRecCalc reading).stepSource
      (Indistinct.of_states (isState_of_process (par_process presentationIn partnerIn))
        (isState_of_process (par_process sourceIn partnerIn)) equivalent) step
  · intro step
    refine ⟨isState_of_process sourceIn, source, .refl _, isState_of_process sourceIn, ?_⟩
    rw [plug_partner avoids (isState_of_process sourceIn).1]
    exact step

/-! ## Finitely many partner steps, keeping the processes -/

/-- **Partner steps keep the processes.** -/
theorem closedUnder (admitted : admits definitions = true) :
    (frontDoor definitions).ClosedUnder isPartnerLabel processes := by
  intro source label target sourceIn partnerOf step
  obtain ⟨hole, partnerProcess, rfl, avoids, partnerIn⟩ := exists_of_isPartnerLabel partnerOf
  exact reduces_process admitted (par_process sourceIn partnerIn) ((step_partner_iff avoids partnerIn sourceIn).mp step)

/-- **Partner steps are finitely many up to the laws**: the successors of the canonical form of the bag. -/
theorem finiteUpTo (admitted : admits definitions = true) :
    (frontDoor definitions).FiniteUpTo isPartnerLabel processes
      (Indistinct (definitionsEnv definitions) ccsRecCalc reading) := by
  classical
  intro source sourceIn label partnerOf
  obtain ⟨hole, partnerProcess, rfl, avoids, partnerIn⟩ := exists_of_isPartnerLabel partnerOf
  have bagIn := par_process sourceIn partnerIn
  refine ⟨(recSuccessors definitions (blockCanon (par source partnerProcess))).filter
    (fun next => decide ((frontDoor definitions).step source (partnerLabel hole partnerProcess) next)), ?_, ?_⟩
  · intro listed member
    exact of_decide_eq_true (List.mem_filter.mp member).2
  · intro target step
    have reduction := (step_partner_iff avoids partnerIn sourceIn).mp step
    obtain ⟨next, member, nextStep, equivalent⟩ := reduces_canonical admitted bagIn reduction
    have targetIn := reduces_process admitted bagIn reduction
    have nextIn := reduces_process admitted bagIn nextStep
    refine ⟨next, List.mem_filter.mpr ⟨member, decide_eq_true ((step_partner_iff avoids partnerIn sourceIn).mpr
      nextStep)⟩, Indistinct.of_states (isState_of_process targetIn) (isState_of_process nextIn) equivalent⟩

/-! ## The characterization -/

/-- **Two processes have the same native types under parallel partners exactly when they are forward bisimilar
under partners.** -/
theorem agree_iff_forwardBisimilar (admitted : admits definitions = true) {first second : Pattern}
    (firstIn : processes first) (secondIn : processes second) :
    (frontDoor definitions).AgreeOn (Formula.forwardOn isPartnerLabel) first second ↔
      (frontDoor definitions).ForwardBisimilar isPartnerLabel first second :=
  NativeStructure.agree_iff_forwardBisimilar (referenceStructure_saturated (definitionsEnv definitions) ccsRecCalc reading)
    (finiteUpTo admitted) (closedUnder admitted) firstIn secondIn

/-- Every process has a hole name it does not use. -/
theorem exists_hole {partnerProcess : Pattern} (partnerIn : processes partnerProcess) :
    ∃ hole, avoidsHole hole partnerProcess = true := by
  obtain ⟨hole, absent⟩ := Infinite.exists_notMem_finset (freeVars partnerProcess).toFinset
  exact ⟨hole, CCSPartners.avoidsHole_of_not_mem partnerProcess (typed_of_domain partnerIn).2 (fun member =>
    absent (List.mem_toFinset.mpr member))⟩

/-- **Forward bisimilarity under partners is saturated reduction bisimilarity.** -/
theorem forwardBisimilar_iff_saturated (admitted : admits definitions = true) {first second : Pattern}
    (firstIn : processes first) (secondIn : processes second) :
    (frontDoor definitions).ForwardBisimilar isPartnerLabel first second ↔
      SaturatedReductionBisimilar definitions first second := by
  constructor
  · rintro ⟨relation, bisimulation, related⟩
    refine ⟨fun left right => processes left ∧ processes right ∧ relation left right, ?_,
      fun _ _ both => ⟨both.1, both.2.1⟩, firstIn, secondIn, related⟩
    rintro left right ⟨leftIn, rightIn, relatedHere⟩ partnerProcess partnerIn
    obtain ⟨hole, avoids⟩ := exists_hole partnerIn
    have partnerOf := isPartnerLabel_partnerLabel avoids partnerIn
    refine ⟨fun next step => ?_, fun next step => ?_⟩
    · obtain ⟨matched, step', relatedNext⟩ := bisimulation.forth relatedHere partnerOf
        ((step_partner_iff avoids partnerIn leftIn).mpr step)
      exact ⟨matched, (step_partner_iff avoids partnerIn rightIn).mp step',
        closedUnder admitted leftIn partnerOf ((step_partner_iff avoids partnerIn leftIn).mpr step),
        closedUnder admitted rightIn partnerOf step', relatedNext⟩
    · obtain ⟨matched, step', relatedNext⟩ := bisimulation.back relatedHere partnerOf
        ((step_partner_iff avoids partnerIn rightIn).mpr step)
      exact ⟨matched, (step_partner_iff avoids partnerIn leftIn).mp step',
        closedUnder admitted leftIn partnerOf step',
        closedUnder admitted rightIn partnerOf ((step_partner_iff avoids partnerIn rightIn).mpr step), relatedNext⟩
  · rintro ⟨relation, saturated, inProcesses, related⟩
    refine ⟨relation, ⟨?_, ?_⟩, related⟩
    · intro left right label next relatedHere partnerOf step
      obtain ⟨hole, partnerProcess, rfl, avoids, partnerIn⟩ := exists_of_isPartnerLabel partnerOf
      obtain ⟨leftIn, rightIn⟩ := inProcesses relatedHere
      obtain ⟨matched, step', relatedNext⟩ :=
        (saturated relatedHere partnerProcess partnerIn).1 next ((step_partner_iff avoids partnerIn leftIn).mp step)
      exact ⟨matched, (step_partner_iff avoids partnerIn rightIn).mpr step', relatedNext⟩
    · intro left right label next' relatedHere partnerOf step
      obtain ⟨hole, partnerProcess, rfl, avoids, partnerIn⟩ := exists_of_isPartnerLabel partnerOf
      obtain ⟨leftIn, rightIn⟩ := inProcesses relatedHere
      obtain ⟨matched, step', relatedNext⟩ :=
        (saturated relatedHere partnerProcess partnerIn).2 next' ((step_partner_iff avoids partnerIn rightIn).mp step)
      exact ⟨matched, (step_partner_iff avoids partnerIn leftIn).mpr step', relatedNext⟩

/-- **The front door's partner-labelled native types of CCS with recursion characterize its saturated reduction
bisimilarity**: two processes satisfy the same forward formulas under parallel partners exactly when, beside every
process, each one's reductions are matched by the other's. -/
theorem agree_iff_saturated (admitted : admits definitions = true) {first second : Pattern}
    (firstIn : processes first) (secondIn : processes second) :
    (frontDoor definitions).AgreeOn (Formula.forwardOn isPartnerLabel) first second ↔
      SaturatedReductionBisimilar definitions first second :=
  (agree_iff_forwardBisimilar admitted firstIn secondIn).trans (forwardBisimilar_iff_saturated admitted firstIn secondIn)

/-- **Strongly bisimilar processes have the same partner-labelled native types.** -/
theorem agree_of_bisimilar (admitted : admits definitions = true) {first second : Pattern}
    (firstIn : processes first) (secondIn : processes second) (bisimilar : Bisimilar definitions first second) :
    (frontDoor definitions).AgreeOn (Formula.forwardOn isPartnerLabel) first second :=
  (agree_iff_saturated admitted firstIn secondIn).mpr (saturated_of_bisimilar admitted firstIn secondIn bisimilar)

/-! ## The front door lists the partner steps -/

/-- **A successor of the canonical form is a reduction's target.** -/
theorem reduces_of_listed (admitted : admits definitions = true) {source next : Pattern} (sourceIn : processes source)
    (member : next ∈ recSuccessors definitions (blockCanon source)) : Reduces definitions source next := by
  have raw := recSuccessors_sound _ (Nat.lt_succ_self _) member
  obtain ⟨sourceTyped, sourceObject⟩ := typed_of_domain sourceIn
  obtain ⟨canonTyped, canonEquivalent⟩ := canon_sound (block := ccsBlock) names_context sourceTyped
  have canonObject : isObjectPattern (blockCanon source) = true := by
    rw [← equationEquiv_isObject (block := ccsBlock) canonEquivalent.toEquationEquiv]; exact sourceObject
  have canonIn : processes (blockCanon source) := domain_of_typed canonTyped canonObject
  obtain ⟨nextTyped, nextObject⟩ := typed_of_raw admitted raw canonTyped canonObject
  have nextIn : processes next := domain_of_typed nextTyped nextObject
  obtain ⟨witness, valid⟩ := reference_iff_raw.mpr raw
  exact ⟨isState_of_process sourceIn, isState_of_process nextIn, _, next, witness,
    objectEquivalent_of_sortedEquiv _ canonEquivalent sourceObject, isState_of_process canonIn, valid,
    isState_of_process nextIn, .refl _, rfl⟩

variable (definitions) in
/-- The listed successors: under a plain label, the steps of the canonical form; under a partner's label, those of
the canonical form of the bag with the partner. -/
def successorList : StepLabel → Pattern → Option (List Pattern)
  | .any, term => if domain term then some (recSuccessors definitions (blockCanon term)) else none
  | .context hole (.collection .hashBag [.fvar hole', partnerProcess] none) .any, term =>
      if hole == hole' && avoidsHole hole partnerProcess && domain partnerProcess && domain term then
        some (recSuccessors definitions (blockCanon (par term partnerProcess)))
      else none
  | _, _ => none

/-- **The successors of CCS with recursion, complete up to the laws**, for plain steps and for partners' steps. -/
def successors (admitted : admits definitions = true) : Successors (definitionsEnv definitions) ccsRecCalc reading where
  list := successorList definitions
  sound := by
    intro label term next listed target member
    unfold successorList at listed
    split at listed
    · split_ifs at listed with termIn
      cases listed
      exact reduces_of_listed admitted termIn member
    · rename_i hole hole' partnerProcess
      split_ifs at listed with conditions
      cases listed
      simp only [Bool.and_eq_true, beq_iff_eq] at conditions
      obtain ⟨⟨⟨rfl, avoids⟩, partnerIn⟩, termIn⟩ := conditions
      exact (step_partner_iff avoids partnerIn termIn).mpr
        (reduces_of_listed admitted (par_process termIn partnerIn) member)
    · cases listed
  complete := by
    intro label term next listed target step
    unfold successorList at listed
    split at listed
    · split_ifs at listed with termIn
      cases listed
      obtain ⟨next', member, -, equivalent⟩ := reduces_canonical admitted termIn step
      exact ⟨next', member, .symm _ _ equivalent⟩
    · rename_i hole hole' partnerProcess
      split_ifs at listed with conditions
      cases listed
      simp only [Bool.and_eq_true, beq_iff_eq] at conditions
      obtain ⟨⟨⟨rfl, avoids⟩, partnerIn⟩, termIn⟩ := conditions
      obtain ⟨next', member, -, equivalent⟩ :=
        reduces_canonical admitted (par_process termIn partnerIn) ((step_partner_iff avoids partnerIn termIn).mp step)
      exact ⟨next', member, .symm _ _ equivalent⟩
    · cases listed

/-- **The modal decider of CCS with recursion**: the step modalities, partners' labels included, evaluated at the
listed successors, over named terms by canonical forms. -/
def decider (admitted : admits definitions = true) : Decider (definitionsEnv definitions) ccsRecCalc reading :=
  modalDecider (successors admitted) (namedDecider CCSRecForms.canon domain (CCSRecForms.canonical admitted))

theorem decided_holds (admitted : admits definitions = true) {formula : Formula 0} {term : Pattern}
    (decided : (decider admitted).decide formula term = some true) :
    (frontDoor definitions).sat Env.closed formula term :=
  ((decider admitted).exact decided).mpr rfl

theorem decided_fails (admitted : admits definitions = true) {formula : Formula 0} {term : Pattern}
    (decided : (decider admitted).decide formula term = some false) :
    ¬ (frontDoor definitions).sat Env.closed formula term :=
  fun holds => Bool.false_ne_true (((decider admitted).exact decided).mp holds)

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.CCSRecPartners
