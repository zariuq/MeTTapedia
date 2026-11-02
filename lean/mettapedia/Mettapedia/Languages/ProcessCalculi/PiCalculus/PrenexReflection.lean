import Mettapedia.Languages.ProcessCalculi.PiCalculus.PrenexSteps
import Mettapedia.Languages.ProcessCalculi.PiCalculus.ReadBackCanonical
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationReflection

/-!
# π's canonical presentations, reflected into a process's own guards

A communication of a presentation of a process's canonical form is a communication of the process's own guards beside
copies of its own servers' inputs, to an equivalent contractum (`reflect_presented`):

- **Guards read canonically as guards** (`canonP_guard`): an input and a server with their continuations read
  canonically, an output as it is.
- **A step of restricted guards is a communication of two of them** (`rawStep_guards`).
- The canonical guards of a block come from its guards (`replication_reflection`), and a communication of canonical
  guards is one of the guards they read, the continuations equivalent.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus.PrenexForm

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Blocks (piBlock piRepBlock piBlockSignature)
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance (piCalc PiRawStep)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (engineBasePremises)
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationEquiv)
open Mettapedia.OSLF.MeTTaIL.Substitution (instantiateBVar)

/-! ## Guards read canonically -/

/-- **A guard read canonically**: an input and a server with their continuations read canonically, an output as it
is. -/
def canonGuard : Pattern → Pattern
  | .apply "PiInp" [channel, .lambda binder body] => .apply "PiInp" [channel, .lambda binder (canonR piRepBlock body)]
  | .apply "PiRep" [.apply "PiInp" [channel, .lambda binder body]] =>
      .apply "PiRep" [.apply "PiInp" [channel, .lambda binder (canonR piRepBlock body)]]
  | other => other

theorem fresh_pi : piRepBlock.replicate ∉ piRepBlock.emptyUnits :=
  replicate_not_emptyUnit (block := piRepBlock) (language := piCalc)

theorem restrictFresh_pi : piRepBlock.replicate ≠ piRepBlock.restrict :=
  replicate_ne_restrict (block := piRepBlock) (language := piCalc)

/-- A typed body's canonical pattern is its own canonical pattern. -/
theorem canonicalOf_canonR {free : FreeTypeContext} {bound : List TypeExpr} {body : Pattern}
    (typed : HasType piCalc free bound body (.base "Proc")) (object : isObjectPattern body = true) :
    canonicalOf piRepBlock (canonR piRepBlock body) = canonR piRepBlock body := by
  have facts := canonFacts fresh_pi restrictFresh_pi object (restrictionsBind_of_typed (block := piRepBlock) _ typed)
  exact canonicalOf_toPattern_fixed facts.atomic facts.used facts.fixed

theorem decompose_input (channel : Pattern) (binder : Option String) (body : Pattern) :
    decompose piRepBlock.toBlock (.apply "PiInp" [channel, .lambda binder body]) =
      Prenex.atom (.apply "PiInp" [channel, .lambda binder body]) :=
  decompose_atom (by simp) (fun _ _ equal => by simp at equal) (fun _ equal => by simp at equal)
    (fun _ _ equal => by simp at equal)

theorem decompose_server (input : Pattern) :
    decompose piRepBlock.toBlock (.apply "PiRep" [input]) = Prenex.atom (.apply "PiRep" [input]) :=
  decompose_atom (by simp) (fun _ _ equal => by simp at equal) (fun _ equal => by simp at equal)
    (fun _ _ equal listed => by simp at listed)

/-- **An input with a canonical continuation reads canonically as itself.** -/
theorem canonicalOf_input {channel body : Pattern}
    (channelName : (∃ index, channel = .bvar index) ∨ ∃ name', channel = .fvar name')
    (canonical : canonicalOf piRepBlock body = body) :
    canonicalOf piRepBlock (.apply "PiInp" [channel, .lambda none body]) = .apply "PiInp" [channel, .lambda none body] := by
  rw [canonicalOf_atom (decompose_input channel none body), recanon_apply]
  simp only [List.map_cons, List.map_nil, partOf]
  rw [if_neg (by decide), if_neg (by decide)]
  rw [canonicalOf_atom (decompose_lambda none body), recanon_lambda, canonical]
  rcases channelName with ⟨index, rfl⟩ | ⟨name', rfl⟩
  · rw [canonicalOf_atom (decompose_bvar index), recanon_bvar]
  · rw [canonicalOf_atom (decompose_fvar name'), recanon_fvar]

/-- The replicated molecules of an input's block: the replication of the input read canonically. -/
theorem replicatedOf_input (canonical : Pattern → Pattern) (channel : Pattern) (binder : Option String) (body : Pattern) :
    replicatedOf piRepBlock canonical (Prenex.atom (.apply "PiInp" [channel, .lambda binder body])) =
      [.apply "PiRep" [canonical (.apply "PiInp" [channel, .lambda binder body])]] := by
  have identity : Prenex.groupIndex 0 [] = id := by
    funext index
    simp [Prenex.groupIndex]
  simp [replicatedOf, groups, insertComponent, insertUsing, usedRestrictions, Prenex.atom, Prenex.molecule, identity,
    rename_id, Prenex.toPattern, Prenex.restricts, Prenex.body]

/-- **Guards read canonically as guards**: an input and a server with their continuations read canonically, an output
as it is. -/
theorem canonP_guard {free : FreeTypeContext} {bound : List TypeExpr} {guard : Pattern}
    (typed : HasType piCalc free bound guard (.base "Proc")) (object : isObjectPattern guard = true)
    (isGuardHere : isGuard guard = true) : canonP piRepBlock guard = Prenex.atom (canonGuard guard) := by
  rcases guard_cases isGuardHere with ⟨channel, binder, body, rfl⟩ | ⟨channel, binder, body, rfl⟩ |
    ⟨channel, datum, rfl⟩
  · cases binder_of_typed typed object
    obtain ⟨channelTyped, -⟩ := listener_parts typed
    have channelObject : isObjectPattern channel = true := by
      simp only [isObjectPattern, isObjectPatternList, Bool.and_eq_true] at object
      exact object.1
    rw [canonP_pair]
    simp [canonsP, canonP_name (name_cases channelTyped channelObject), canonP, argumentOf, canonGuard]
    rfl
  · have inputTyped := replicate_argument_typed (block := piRepBlock) typed
    have inputObject : isObjectPattern (.apply "PiInp" [channel, .lambda binder body]) = true := by
      simpa [isObjectPattern, isObjectPatternList] using object
    cases binder_of_typed inputTyped inputObject
    obtain ⟨channelTyped, bodyTyped⟩ := listener_parts inputTyped
    have channelObject : isObjectPattern channel = true := by
      simp only [isObjectPattern, isObjectPatternList, Bool.and_eq_true] at inputObject
      exact inputObject.1
    have bodyObject : isObjectPattern body = true := by
      simp only [isObjectPattern, isObjectPatternList, Bool.and_eq_true] at inputObject
      exact inputObject.2.1
    have channelName := name_cases channelTyped channelObject
    have inputCanon : canonP piRepBlock (.apply "PiInp" [channel, .lambda none body]) =
        Prenex.atom (.apply "PiInp" [channel, .lambda none (canonR piRepBlock body)]) := by
      rw [canonP_pair]
      simp [canonsP, canonP_name channelName, canonP, argumentOf]
      rfl
    have canonicalInput := canonicalOf_input channelName (canonicalOf_canonR bodyTyped bodyObject)
    rw [canonP_replicate (fun _ _ equal => by simp at equal), inputCanon, replicatedOf_input, canonicalInput]
    show Mettapedia.GSLT.LanguageDef.RestrictionBlocks.normal piRepBlock (Prenex.atom _) = _
    rw [normal_atom fresh_pi restrictFresh_pi (decompose_server _), recanon_apply]
    simp only [List.map_cons, List.map_nil, partOf]
    rw [if_neg (by decide), if_neg (by decide), canonicalInput]
    rfl
  · obtain ⟨channelTyped, datumTyped⟩ := output_parts typed
    have objects : isObjectPattern channel = true ∧ isObjectPattern datum = true := by
      simpa [isObjectPattern, isObjectPatternList] using object
    rw [canonP_pair]
    simp [canonsP, canonP_name (name_cases channelTyped objects.1), canonP_name (name_cases datumTyped objects.2),
      argumentOf, canonGuard]
    rfl

/-! ## Steps of restricted guards -/

/-- What steps is a bag or a restriction. -/
theorem rawStep_source {source target : Pattern} (stepped : PiRawStep source target) :
    (∃ elements tail, source = .collection .hashBag elements tail) ∨
      ∃ binder body, source = .apply "PiNu" [.lambda binder body] := by
  cases stepped with
  | comm => exact .inl ⟨_, _, rfl⟩
  | par => exact .inl ⟨_, _, rfl⟩
  | res binder inner => exact .inr ⟨_, _, rfl⟩

/-- **A guard does not step**: its continuations are behind prefixes. -/
theorem guard_stuck {guard target : Pattern} (isGuardHere : isGuard guard = true) : ¬ PiRawStep guard target := by
  intro stepped
  rcases rawStep_source stepped with ⟨_, _, equal⟩ | ⟨_, _, equal⟩ <;>
    rcases guard_cases isGuardHere with ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ <;> simp at equal

/-- **A guard read again is a guard.** -/
theorem isGuard_recanon {guard : Pattern} (isGuardHere : isGuard guard = true) :
    isGuard (recanon piRepBlock guard) = true := by
  rcases guard_cases isGuardHere with ⟨channel, binder, body, rfl⟩ | ⟨channel, binder, body, rfl⟩ |
    ⟨channel, datum, rfl⟩
  · rw [recanon_apply]
    simp only [List.map_cons, List.map_nil, partOf]
    rw [if_neg (by decide), if_neg (by decide), canonicalOf_atom (decompose_lambda binder body), recanon_lambda]
    rfl
  · rw [recanon_apply]
    simp only [List.map_cons, List.map_nil, partOf]
    rw [if_neg (by decide), if_neg (by decide), canonicalOf_atom (decompose_input channel binder body), recanon_apply]
    simp only [List.map_cons, List.map_nil, partOf]
    rw [if_neg (by decide), if_neg (by decide), canonicalOf_atom (decompose_lambda binder body), recanon_lambda]
    rfl
  · rw [recanon_apply]
    rfl

/-- **A step of restricted guards is a communication of two of them.** -/
theorem rawStep_guards : ∀ (count : Nat) {components : List Pattern} {target : Pattern},
    (∀ component ∈ components, isGuard component = true) →
    PiRawStep (Prenex.restricts piBlock count (Prenex.body piBlock components)) target →
      ∃ (first : Nat) (firstInside : first < components.length) (second : Nat)
        (secondInside : second < (components.eraseIdx first).length) (channel : Pattern) (binder : Option String)
        (body datum : Pattern), components[first] = .apply "PiInp" [channel, .lambda binder body] ∧
        (components.eraseIdx first)[second] = .apply "PiOut" [channel, datum] ∧
        target = Prenex.restricts piBlock count
          (.collection .hashBag (instantiateBVar datum body :: (components.eraseIdx first).eraseIdx second) none)
  | 0, components, target, guards, stepped => by
      match components, guards, stepped with
      | [], _, stepped =>
          rcases rawStep_source stepped with ⟨_, _, equal⟩ | ⟨_, _, equal⟩ <;>
            simp [Prenex.body, Prenex.restricts] at equal
      | [component], guards, stepped =>
          exact absurd stepped (guard_stuck (guards component (List.mem_singleton_self _)))
      | first :: second :: rest, guards, stepped =>
          cases stepped with
          | comm i hi j hj channel binder body datum input output =>
              exact ⟨i, hi, j, hj, channel, binder, body, datum, input, output, rfl⟩
          | par i hi inner => exact absurd inner (guard_stuck (guards _ (List.getElem_mem hi)))
  | count + 1, components, target, guards, stepped => by
      rw [Prenex.restricts_succ] at stepped
      cases stepped with
      | res binder inner =>
          obtain ⟨first, firstInside, second, secondInside, channel, binder', body, datum, input, output, rfl⟩ :=
            rawStep_guards count guards inner
          exact ⟨first, firstInside, second, secondInside, channel, binder', body, datum, input, output, rfl⟩

/-! ## Guards read canonically, as patterns -/

/-- **A guard's canonical pattern is the guard read canonically.** -/
theorem canonR_guard {free : FreeTypeContext} {bound : List TypeExpr} {guard : Pattern}
    (typed : HasType piCalc free bound guard (.base "Proc")) (object : isObjectPattern guard = true)
    (isGuardHere : isGuard guard = true) : canonR piRepBlock guard = canonGuard guard := by
  unfold canonR
  rw [canonP_guard typed object isGuardHere]
  rfl

theorem isGuard_canonGuard {guard : Pattern} (isGuardHere : isGuard guard = true) : isGuard (canonGuard guard) = true := by
  rcases guard_cases isGuardHere with ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ <;> rfl

/-- **A guard read canonically reads canonically as itself.** -/
theorem canonP_canonGuard {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound)
    {guard : Pattern} (typed : HasType piCalc free bound guard (.base "Proc")) (object : isObjectPattern guard = true)
    (isGuardHere : isGuard guard = true) : canonP piRepBlock (canonGuard guard) = Prenex.atom (canonGuard guard) := by
  have canonIs := canonR_guard typed object isGuardHere
  have canonTyped := (canonR_sound (block := piRepBlock) context typed).1
  have canonObject := isObject_canonR (block := piRepBlock) object
  rw [canonIs] at canonTyped canonObject
  have twice := canonR_canonR (block := piRepBlock) (language := piCalc) context typed object
  rw [canonIs] at twice
  have facts := canonFacts fresh_pi restrictFresh_pi canonObject
    (restrictionsBind_of_typed (block := piRepBlock) _ canonTyped)
  have factsGuard := canonFacts fresh_pi restrictFresh_pi object (restrictionsBind_of_typed (block := piRepBlock) _ typed)
  have same : canonP piRepBlock (canonGuard guard) = canonP piRepBlock guard :=
    toPattern_injective facts.atomic factsGuard.atomic (by
      show canonR piRepBlock (canonGuard guard) = canonR piRepBlock guard
      rw [twice, canonIs])
  rw [same, canonP_guard typed object isGuardHere]

/-- **A guard read canonically as a server is a server of an input read canonically.** -/
theorem canonGuard_server {guard argument : Pattern} (isGuardHere : isGuard guard = true)
    (serverIs : canonGuard guard = .apply "PiRep" [argument]) :
    ∃ input, guard = .apply "PiRep" [input] ∧ isGuard input = true ∧ argument = canonGuard input ∧
      ∃ channel binder body, input = .apply "PiInp" [channel, .lambda binder body] := by
  rcases guard_cases isGuardHere with ⟨_, _, _, rfl⟩ | ⟨channel, binder, body, rfl⟩ | ⟨_, _, rfl⟩
  · simp [canonGuard] at serverIs
  · simp only [canonGuard, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at serverIs
    exact ⟨_, rfl, rfl, serverIs.symm, channel, binder, body, rfl⟩
  · simp [canonGuard] at serverIs

/-- **A guard read canonically as an input is an input.** -/
theorem canonGuard_input {guard channel body : Pattern} {binder : Option String} (isGuardHere : isGuard guard = true)
    (inputIs : canonGuard guard = .apply "PiInp" [channel, .lambda binder body]) :
    ∃ raw, guard = .apply "PiInp" [channel, .lambda binder raw] ∧ body = canonR piRepBlock raw := by
  rcases guard_cases isGuardHere with ⟨channel', binder', raw, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩
  · simp only [canonGuard, Pattern.apply.injEq, List.cons.injEq, Pattern.lambda.injEq, and_true, true_and] at inputIs
    obtain ⟨rfl, rfl, rfl⟩ := inputIs
    exact ⟨raw, rfl, rfl⟩
  · simp [canonGuard] at inputIs
  · simp [canonGuard] at inputIs

/-- **A guard read canonically as an output is that output.** -/
theorem canonGuard_output {guard channel datum : Pattern} (isGuardHere : isGuard guard = true)
    (outputIs : canonGuard guard = .apply "PiOut" [channel, datum]) : guard = .apply "PiOut" [channel, datum] := by
  rcases guard_cases isGuardHere with ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩
  · simp [canonGuard] at outputIs
  · simp [canonGuard] at outputIs
  · exact outputIs

/-! ## A communication of a presentation, reflected into the process -/

/-- **A communication of a presentation of a process's canonical form is a communication of the process's own guards
beside copies of its servers' inputs**, to an equivalent contractum. -/
theorem reflect_presented {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound)
    {state : Pattern} (typed : HasType piCalc free bound state (.base "Proc")) (object : isObjectPattern state = true)
    (guards : ∀ component ∈ (decompose piBlock state).components, isGuard component = true)
    {shown next : Pattern} (presented : shown ∈ replicationPresentations piRepBlock 2 (canonR piRepBlock state))
    (stepped : PiRawStep shown next) :
    ∃ copies : List Pattern,
      (∀ copy ∈ copies, Pattern.apply "PiRep" [copy] ∈ (decompose piBlock state).components) ∧
      ∃ target, PiRawStep (Prenex.restricts piBlock (decompose piBlock state).count
          (Prenex.body piBlock ((decompose piBlock state).components ++ copies))) target ∧
        EquationEquiv (engineBasePremises RelationEnv.empty) piCalc target next := by
  classical
  set form := decompose piBlock state with formIs
  obtain ⟨members, blockEquivalent⟩ := decompose_sound (block := piBlock) typed
  have objects := objects_of_decompose (block := piBlock) object
  set frame := List.replicate form.count (TypeExpr.base "Name") ++ bound with frameIs
  have frameContext : BaseContext free frame := context.replicate form.count "Name"
  -- the guards read canonically
  set canonical := form.components.map canonGuard with canonicalIs
  have canonicalFacts : ∀ guard ∈ form.components, HasType piCalc free frame (canonGuard guard) (.base "Proc") ∧
      isObjectPattern (canonGuard guard) = true ∧ isGuard (canonGuard guard) = true ∧
      canonP piRepBlock (canonGuard guard) = Prenex.atom (canonGuard guard) := by
    intro guard member
    have canonIs := canonR_guard (members guard member) (objects guard member) (guards guard member)
    have canonTyped := (canonR_sound (block := piRepBlock) frameContext (members guard member)).1
    have canonObject := isObject_canonR (block := piRepBlock) (objects guard member)
    rw [canonIs] at canonTyped canonObject
    exact ⟨canonTyped, canonObject, isGuard_canonGuard (guards guard member),
      canonP_canonGuard frameContext (members guard member) (objects guard member) (guards guard member)⟩
  have canonicalMembers : Members piCalc piBlock free frame canonical := by
    intro element member
    obtain ⟨guard, inForm, rfl⟩ := List.mem_map.mp member
    exact (canonicalFacts guard inForm).1
  -- the canonical form of the process is that of its guards read canonically
  have bagTyped : HasType piCalc free bound
      (Prenex.restricts piBlock form.count (.collection .hashBag form.components none)) (.base "Proc") :=
    restricts_typed (block := piBlock) form.count (bag_typed (block := piBlock) members)
  have bagObject : isObjectPattern (Prenex.restricts piBlock form.count (.collection .hashBag form.components none)) =
      true := by
    rw [isObject_restricts, isObject_bag]
    exact objects
  have stateBag : EquationEquiv (engineBasePremises RelationEnv.empty) piCalc state
      (Prenex.restricts piBlock form.count (.collection .hashBag form.components none)) :=
    Relation.EqvGen.trans _ _ _ blockEquivalent.toEquationEquiv (restricts_equation (block := piBlock) form.count
      (Relation.EqvGen.symm _ _ (bag_body_equivalent (block := piBlock) members).toEquationEquiv))
  have stateFacts := canonFacts fresh_pi restrictFresh_pi object (restrictionsBind_of_typed (block := piRepBlock) _ typed)
  have bagFacts := canonFacts fresh_pi restrictFresh_pi bagObject
    (restrictionsBind_of_typed (block := piRepBlock) _ bagTyped)
  have sameCanon : canonP piRepBlock state =
      canonP piRepBlock (Prenex.restricts piBlock form.count (.collection .hashBag form.components none)) :=
    toPattern_injective stateFacts.atomic bagFacts.atomic (canonR_complete (block := piRepBlock) object bagObject
      (restrictionsBind_of_typed (block := piRepBlock) _ typed) stateBag)
  have canonIs : canonP piRepBlock state =
      Mettapedia.GSLT.LanguageDef.RestrictionBlocks.normal piRepBlock ⟨form.count, canonical⟩ := by
    rw [sameCanon]
    have atBag := canonP_restricts_bag (block := piRepBlock) fresh_pi restrictFresh_pi form.count (parts := [])
      (rest := form.components) (by simp) objects (by simp)
      (fun other member => restrictionsBind_of_typed (block := piRepBlock) _ (members other member)) (by simp)
    simp only [List.nil_append, List.map_nil] at atBag
    rw [atBag]
    have atoms : form.components.map (canonP piRepBlock) = canonical.map Prenex.atom := by
      rw [canonicalIs, List.map_map]
      exact List.map_congr_left fun guard member =>
        canonP_guard (members guard member) (objects guard member) (guards guard member)
    rw [atoms, foldr_par_atoms]
    simp
  set K := Mettapedia.GSLT.LanguageDef.RestrictionBlocks.normal piRepBlock ⟨form.count, canonical⟩ with KIs
  have canonicalAtomic : (Prenex.mk form.count canonical).Atomic piRepBlock.toBlock := by
    intro component member
    obtain ⟨guard, inForm, rfl⟩ := List.mem_map.mp member
    obtain ⟨canonTyped, canonObject, -, canonAtom⟩ := canonicalFacts guard inForm
    have atomicHere := (canonFacts fresh_pi restrictFresh_pi canonObject
      (restrictionsBind_of_typed (block := piRepBlock) _ canonTyped)).atomic
    rw [canonAtom] at atomicHere
    exact atomicHere _ (List.mem_singleton_self _)
  -- the presentation is an unfolding of the canonical form
  obtain ⟨unfolded, inUnfoldings, rfl⟩ := List.mem_map.mp presented
  have decomposed : decompose piRepBlock.toBlock (canonR piRepBlock state) = K := by
    unfold canonR
    rw [decompose_toPattern stateFacts.atomic stateFacts.used, canonIs]
  rw [decomposed] at inUnfoldings
  have unfolds := (mem_unfoldings _ _ _).mp inUnfoldings
  -- the canonical form's components and the copies are guards
  have kGuards : ∀ component ∈ K.components, isGuard component = true := by
    intro component member
    obtain ⟨relabel, original, inCanonical, rfl⟩ :=
      normal_mem_read fresh_pi restrictFresh_pi canonicalAtomic component member
    obtain ⟨guard, inForm, rfl⟩ := List.mem_map.mp inCanonical
    exact isGuard_recanon (isGuard_rename relabel (isGuard_canonGuard (guards guard inForm)))
  have kServers : ∀ component ∈ K.components, ∀ argument, component = .apply piRepBlock.replicate [argument] →
      decompose piRepBlock.toBlock argument = Prenex.atom argument ∧ isReplicated piRepBlock argument = false := by
    intro component member argument componentIs
    have guard := kGuards component member
    rcases guard_cases guard with ⟨_, _, _, rfl⟩ | ⟨channel, binder, body, rfl⟩ | ⟨_, _, rfl⟩
    · simp at componentIs
    · simp only [Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at componentIs
      subst componentIs
      exact ⟨decompose_input channel binder body, rfl⟩
    · simp at componentIs
  obtain ⟨pairs, unfoldedIs, pairsFacts⟩ := unfolds_atomic fresh_pi restrictFresh_pi unfolds kServers
  have uGuards : ∀ component ∈ unfolded.components, isGuard component = true := by
    rw [unfoldedIs]
    intro component member
    rcases List.mem_append.mp member with inK | inCopies
    · exact kGuards component inK
    · obtain ⟨pair, inPairs, rfl⟩ := List.mem_map.mp inCopies
      obtain ⟨argument, serverIs, inK, copyIs⟩ := pairsFacts pair inPairs
      have serverGuard := kGuards _ inK
      rw [serverIs] at serverGuard
      rw [copyIs]
      rcases guard_cases serverGuard with ⟨_, _, _, equal⟩ | ⟨channel, binder, body, equal⟩ | ⟨_, _, equal⟩
      · simp at equal
      · simp only [Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at equal
        subst equal
        exact isGuard_recanon rfl
      · simp at equal
  -- the presentation's communication
  have kMembers := (normal_sound (block := piRepBlock) (language := piCalc) context
    (form := ⟨form.count, canonical⟩) canonicalMembers).1
  have uMembers := unfolds.members context kMembers
  have uObjects := unfolds.objects (normal_objects fun component member => by
    obtain ⟨guard, inForm, rfl⟩ := List.mem_map.mp member
    exact (canonicalFacts guard inForm).2.1)
  obtain ⟨first, firstInside, second, secondInside, channel, binder, body, datum, inputAt, outputAt, nextIs⟩ :=
    rawStep_guards unfolded.count uGuards stepped
  have inputTyped := uMembers _ (List.getElem_mem firstInside)
  have inputObject := uObjects _ (List.getElem_mem firstInside)
  rw [inputAt] at inputTyped inputObject
  cases binder_of_typed inputTyped inputObject
  let redex : Redex := ⟨channel, body, datum⟩
  have split : unfolded.components.Perm (piReactions.parts redex ++ (unfolded.components.eraseIdx first).eraseIdx second) := by
    have twoPerm := perm_two unfolded.components first firstInside second secondInside
    rw [inputAt, outputAt] at twoPerm
    exact twoPerm
  have plain : ∀ part ∈ piReactions.parts redex, isReplicated piRepBlock part = false := by
    intro part member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl
  -- the canonical guards communicate, beside copies of their servers' inputs
  have serversFacts : ∀ component ∈ canonical, ∀ argument, component = .apply piRepBlock.replicate [argument] →
      canonP piRepBlock argument = Prenex.atom argument ∧ isReplicated piRepBlock argument = false := by
    intro component member argument componentIs
    obtain ⟨guard, inForm, rfl⟩ := List.mem_map.mp member
    obtain ⟨input, guardIs, inputGuard, argumentIs, channel', binder', body', inputIs⟩ :=
      canonGuard_server (guards guard inForm) componentIs
    have guardTyped := members guard inForm
    rw [guardIs] at guardTyped
    have inputTyped := replicate_argument_typed (block := piRepBlock) guardTyped
    have inputObject : isObjectPattern input = true := by
      have object' := objects guard inForm
      rw [guardIs] at object'
      simpa [isObjectPattern, isObjectPatternList] using object'
    rw [argumentIs]
    refine ⟨canonP_canonGuard frameContext inputTyped inputObject inputGuard, ?_⟩
    rw [inputIs]
    rfl
  obtain ⟨copies, copiesIn, targetW, steppedW, targetWIs⟩ := replication_reflection piReactions context
    (count := form.count) (components := canonical) canonicalMembers
    (fun component member => by
      obtain ⟨guard, inForm, rfl⟩ := List.mem_map.mp member
      exact (canonicalFacts guard inForm).2.1)
    (fun component member => by
      obtain ⟨guard, inForm, rfl⟩ := List.mem_map.mp member
      exact (canonicalFacts guard inForm).2.2.2)
    serversFacts unfolds split plain
  -- each copy is the input of a server among the guards, read canonically
  have copyFound : ∀ copy ∈ copies, ∃ raw ∈ form.components.map argumentOf?,
      Pattern.apply "PiRep" [raw] ∈ form.components ∧ canonGuard raw = copy ∧ isGuard raw = true := by
    intro copy member
    obtain ⟨guard, inForm, guardIs⟩ := List.mem_map.mp (copiesIn copy member)
    obtain ⟨input, rfl, inputGuard, copyIs, -⟩ := canonGuard_server (guards _ inForm) guardIs
    exact ⟨input, List.mem_map.mpr ⟨_, inForm, rfl⟩, inForm, copyIs.symm, inputGuard⟩
  obtain ⟨raws, rawsRelated, -⟩ := exists_forall₂_of_forall copyFound
  have rawFacts : ∀ raw ∈ raws, Pattern.apply "PiRep" [raw] ∈ form.components ∧ isGuard raw = true := by
    intro raw member
    obtain ⟨copy, -, related⟩ := forall₂_mem_right rawsRelated member
    exact ⟨related.1, related.2.2⟩
  have copiesIs : copies = raws.map canonGuard :=
    forall₂_eq_map (forall₂_imp_mem_both rawsRelated fun _ _ _ _ related => related.2.1.symm)
  set V := form.components ++ raws with VIs
  have vGuards : ∀ v ∈ V, isGuard v = true := by
    intro v member
    rcases List.mem_append.mp member with inForm | inRaws
    · exact guards v inForm
    · exact (rawFacts v inRaws).2
  have vMembers : Members piCalc piBlock free frame V := by
    intro v member
    rcases List.mem_append.mp member with inForm | inRaws
    · exact members v inForm
    · exact replicate_argument_typed (block := piRepBlock) (members _ (rawFacts v inRaws).1)
  have vObjects : ∀ v ∈ V, isObjectPattern v = true := by
    intro v member
    rcases List.mem_append.mp member with inForm | inRaws
    · exact objects v inForm
    · have serverObject := objects _ (rawFacts v inRaws).1
      simpa [isObjectPattern, isObjectPatternList] using serverObject
  have mapped : canonical ++ copies = V.map canonGuard := by
    rw [VIs, List.map_append, copiesIs]
  rw [mapped] at steppedW
  obtain ⟨i, hi, j, hj, channelW, binderW, bodyW, datumW, inputW, outputW, targetWIs'⟩ :=
    rawStep_guards form.count (fun component member => by
      obtain ⟨v, inV, rfl⟩ := List.mem_map.mp member
      exact isGuard_canonGuard (vGuards v inV)) steppedW
  have hiV : i < V.length := by simpa using hi
  have hjV : j < (V.eraseIdx i).length := by
    rw [map_eraseIdx] at hj
    simpa using hj
  -- the guards the canonical ones read
  have inputRead : canonGuard V[i] = .apply "PiInp" [channelW, .lambda binderW bodyW] := by
    rw [← inputW, List.getElem_map]
  obtain ⟨bodyV, inputV, bodyIs⟩ := canonGuard_input (vGuards _ (List.getElem_mem hiV)) inputRead
  have outputRead : canonGuard (V.eraseIdx i)[j] = .apply "PiOut" [channelW, datumW] := by
    rw [← outputW]
    simp only [map_eraseIdx, List.getElem_map]
  have outputV := canonGuard_output (vGuards _ (List.mem_of_mem_eraseIdx (List.getElem_mem hjV))) outputRead
  have long : 2 ≤ V.length := by
    have := List.length_eraseIdx_of_lt hiV
    omega
  have steppedV : PiRawStep (Prenex.restricts piBlock form.count (Prenex.body piBlock V))
      (Prenex.restricts piBlock form.count
        (.collection .hashBag (instantiateBVar datumW bodyV :: (V.eraseIdx i).eraseIdx j) none)) := by
    rw [body_of_long long]
    exact piReactions.restricts_step form.count
      (PiRawStep.comm (tail := none) i hiV j hjV channelW binderW bodyV datumW inputV outputV)
  -- what the guards leave reads as what the canonical guards leave
  have inputTyped' := vMembers _ (List.getElem_mem hiV)
  have inputObject' := vObjects _ (List.getElem_mem hiV)
  rw [inputV] at inputTyped' inputObject'
  cases binder_of_typed inputTyped' inputObject'
  obtain ⟨-, bodyVTyped⟩ := listener_parts inputTyped'
  have bodyVObject : isObjectPattern bodyV = true := by
    simp only [isObjectPattern, isObjectPatternList, Bool.and_eq_true] at inputObject'
    exact inputObject'.2.1
  have outputTyped' := vMembers _ (List.mem_of_mem_eraseIdx (List.getElem_mem hjV))
  have outputObject' := vObjects _ (List.mem_of_mem_eraseIdx (List.getElem_mem hjV))
  rw [outputV] at outputTyped' outputObject'
  obtain ⟨-, datumTyped⟩ := output_parts outputTyped'
  have datumObject : isObjectPattern datumW = true := by
    simp only [isObjectPattern, isObjectPatternList, Bool.and_eq_true] at outputObject'
    exact outputObject'.2.1
  obtain ⟨canonBodyTyped, bodyEquivalent⟩ := canonR_sound (block := piRepBlock) (frameContext.cons "Name") bodyVTyped
  have received := sortedEquiv_instantiate_replication (block := piRepBlock) frameContext datumTyped datumObject
    bodyVTyped canonBodyTyped bodyVObject (isObject_canonR bodyVObject) bodyEquivalent.toEquationEquiv
  have restRelated : List.Forall₂ (EquationEquiv (engineBasePremises RelationEnv.empty) piCalc)
      ((V.eraseIdx i).eraseIdx j) (((V.eraseIdx i).eraseIdx j).map canonGuard) := by
    rw [List.forall₂_map_right_iff]
    refine List.forall₂_same.mpr fun v member => ?_
    have inV := List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx member)
    have canonIs := canonR_guard (vMembers v inV) (vObjects v inV) (vGuards v inV)
    have sound := (canonR_sound (block := piRepBlock) frameContext (vMembers v inV)).2.toEquationEquiv
    rw [canonIs] at sound
    exact sound
  have bagSame := collection_equation (language := piCalc) (.cons received restRelated) []
  simp only [List.nil_append] at bagSame
  refine ⟨raws, fun raw member => (rawFacts raw member).1, _, steppedV, ?_⟩
  refine Relation.EqvGen.trans _ _ _ (restricts_equation (block := piBlock) form.count bagSame) ?_
  have isTarget : Prenex.restricts piBlock form.count (.collection .hashBag
      (instantiateBVar datumW (canonR piRepBlock bodyV) :: ((V.eraseIdx i).eraseIdx j).map canonGuard) none) =
        targetW := by
    rw [targetWIs', bodyIs, map_eraseIdx, map_eraseIdx]
  rw [isTarget, nextIs]
  exact targetWIs

end Mettapedia.Languages.ProcessCalculi.PiCalculus.PrenexForm
