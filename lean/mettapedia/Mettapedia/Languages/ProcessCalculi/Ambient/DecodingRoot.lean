import Mettapedia.Languages.ProcessCalculi.Ambient.DecodingEncode
import Mettapedia.Languages.ProcessCalculi.Ambient.FullObjects
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationSimulation

/-!
# A process read at its root location

A process is read located at a root location bound outside it: its located canonical form with the outermost bound
variable as the root (`rootForm`). Reading back reads only the names a block holds, never its locations
(`decode_unread`), and always gives an object term (`decode_object`). So the root read-back (`rootRead`) does not use
the root, and dropping it gives **the ambient canonical form** (`canonA`): a closed object process equivalent to the
process (`canonA_facts`), the same for processes related by a chain of laws (`canonA_same`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Decoding

open Mettapedia.Languages.ProcessCalculi.Ambient.Comm (ambientCoreCalc)

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (FreeIn freeIn_bvar freeIn_apply)
open Mettapedia.GSLT.LanguageDef.WellSorted (HasType FreeTypeContext isObjectPattern)
open Mettapedia.GSLT.LanguageDef.BagNormalForm (isObjectPatternList_iff)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (Prenex ProcEquiv ObjectChain decompose canonP canonR rename
  dropIndex rename_comp rename_congr rename_id liftBVars_eq_rename shiftAbove isObject_toPattern freeIn_toPattern
  freeIn_body drop_typed restrict_fill garbage_equivalent restricts_typed body_typed canonFacts decompose_toPattern
  canonR_complete restrictionsBind_of_typed isObjectPattern_rename size)
open Mettapedia.Languages.ProcessCalculi.Ambient.Full (ambientBlock ambientRepBlock)
open Mettapedia.Languages.ProcessCalculi.Ambient.Located (locatedCalc locatedBlock locatedRepBlock)
open Mettapedia.Languages.ProcessCalculi.Ambient.Encoding (NameContext nameType procType encode encode_typed
  located located_object located_chain LocatedFrame)
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (engineBasePremises)

/-! ## What a read-back holds -/

theorem isObject_of_variable {pattern : Pattern} (isVar : isVariable pattern = true) :
    isObjectPattern pattern = true := by
  cases pattern <;> simp_all [isVariable, isObjectPattern]

theorem isObject_apply {label : String} {arguments : List Pattern}
    (objects : ∀ argument ∈ arguments, isObjectPattern argument = true) :
    isObjectPattern (.apply label arguments) = true := by
  simpa [isObjectPattern, isObjectPatternList_iff] using objects

theorem wrapContent_object (label : String) {name content : Pattern} (nameObject : isObjectPattern name = true)
    (contentObject : isObjectPattern content = true) : isObjectPattern (wrapContent label name content) = true := by
  unfold wrapContent
  split_ifs
  · exact isObject_apply fun argument member => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact nameObject
      · exact contentObject
  · exact contentObject

/-- **A read-back is an object term**: its leaves are variables and inaction. -/
theorem decode_object : ∀ (fuel : Nat),
    (∀ (place : Pattern) (form : Prenex), ∀ out ∈ (decodeForm fuel place form).components,
      isObjectPattern out = true) ∧
    (∀ (place : Pattern) (components : List Pattern), ∀ out ∈ readPlaced fuel place components,
      isObjectPattern out = true) ∧
    (∀ (place component : Pattern) (elsewhere : List Pattern),
      isObjectPattern (readComponent fuel place component elsewhere) = true)
  | 0 => ⟨fun _ _ _ member => by simp [decodeForm, Prenex.nil] at member,
      fun _ _ _ member => by simp [readPlaced] at member, fun _ _ _ => rfl⟩
  | fuel + 1 => by
      obtain ⟨formsBelow, placedBelow, componentBelow⟩ := decode_object fuel
      have toPatternObject : ∀ (place : Pattern) (form : Prenex),
          isObjectPattern (Prenex.toPattern ambientBlock (decodeForm fuel place form)) = true :=
        fun place form => isObject_toPattern (formsBelow place form)
      have bodyObject : ∀ (place : Pattern) (components : List Pattern),
          isObjectPattern (Prenex.body ambientBlock (readPlaced fuel place components)) = true :=
        fun place components => isObject_toPattern (form := ⟨0, readPlaced fuel place components⟩)
          (placedBelow place components)
      have inactionObject : isObjectPattern inaction = true := rfl
      refine ⟨fun place form out member => placedBelow _ _ out member, fun place components out member => ?_,
        fun place component elsewhere => ?_⟩
      · rw [readPlaced_succ] at member
        obtain ⟨original, -, rfl⟩ := List.mem_map.mp member
        exact componentBelow _ _ _
      · cases component with
        | apply label arguments =>
            match arguments with
            | [_, second, third] =>
                simp only [readComponent]
                split_ifs with isMarker isVar isCap isVar' isLCap isMsg
                · exact wrapContent_object _ (isObject_of_variable isVar) (bodyObject _ _)
                · exact inactionObject
                · exact isObject_apply fun argument member => by
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
                    rcases member with rfl | rfl
                    · exact isObject_of_variable isVar'
                    · exact toPatternObject _ _
                · exact inactionObject
                · exact isObject_apply fun argument member => by
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
                    rcases member with rfl | rfl
                    · exact message_object isMsg
                    · exact toPatternObject _ _
                · exact inactionObject
                · exact inactionObject
            | [_, second] =>
                simp only [readComponent]
                split_ifs with isInput isOutput isMsg
                · cases second with
                  | lambda binder body =>
                      exact isObject_apply fun argument member => by
                        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
                        subst member
                        simpa [isObjectPattern] using toPatternObject _ _
                  | _ => exact inactionObject
                · exact isObject_apply fun argument member => by
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
                    subst member
                    exact message_object isMsg
                · exact inactionObject
                · exact inactionObject
            | [argument] =>
                simp only [readComponent]
                split_ifs
                · exact isObject_apply fun argument member => by
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
                    subst member
                    exact toPatternObject _ _
                · exact inactionObject
            | [] => simp [readComponent, inactionObject]
            | _ :: _ :: _ :: _ :: _ => simp [readComponent, inactionObject]
        | _ => simp [readComponent, inactionObject]

theorem freeIn_variable {pattern : Pattern} {index : Nat} (isVar : isVariable pattern = true)
    (free : FreeIn index pattern) : pattern = .bvar index := by
  cases pattern with
  | bvar other => rw [freeIn_bvar] at free; rw [free]
  | fvar => cases free
  | _ => simp [isVariable] at isVar

/-- What a marker's content, read, uses: the marker's name or the content. -/
theorem freeIn_wrapContent {label : String} {name content : Pattern} {index : Nat}
    (free : FreeIn index (wrapContent label name content)) : FreeIn index name ∨ FreeIn index content := by
  unfold wrapContent at free
  split_ifs at free
  · obtain ⟨argument, inArguments, argumentFree⟩ := freeIn_apply.mp free
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inArguments
    rcases inArguments with rfl | rfl
    · exact .inl argumentFree
    · exact .inr argumentFree
  · exact .inr free

theorem not_freeIn_inaction {index : Nat} : ¬ FreeIn index inaction := by
  simp [inaction, freeIn_apply]

/-- **Reading back reads no location**: every free variable of a block read back from a well-located block is a name
the block holds, never a location. -/
theorem decode_unread : ∀ (fuel : Nat),
    (∀ {isLoc : Pattern → Prop} {place : Pattern} {form : Prenex}, WellLocated isLoc place form → ∀ index,
      FreeIn index (Prenex.toPattern ambientBlock (decodeForm fuel place form)) → ¬ isLoc (.bvar index)) ∧
    (∀ {isLoc : Pattern → Prop} {place : Pattern} {count : Nat} {components : List Pattern},
      WellLocated isLoc place ⟨count, components⟩ → ∀ (at' : Pattern) (part : List Pattern),
      (∀ component ∈ part, component ∈ components) → ∀ out ∈ readPlaced fuel at' part, ∀ index,
      FreeIn index out → ¬ insideLoc isLoc count components (.bvar index)) ∧
    (∀ {isLoc : Pattern → Prop} {place : Pattern} {count : Nat} {components : List Pattern},
      WellLocated isLoc place ⟨count, components⟩ → ∀ (at' component : Pattern) (elsewhere : List Pattern),
      component ∈ components → placeAt component = some at' → (∀ other ∈ elsewhere, other ∈ components) →
      ∀ index, FreeIn index (readComponent fuel at' component elsewhere) →
        ¬ insideLoc isLoc count components (.bvar index))
  | 0 => ⟨fun _ index free => by
        simp [decodeForm, Prenex.nil, Prenex.toPattern, Prenex.restricts, Prenex.body, freeIn_apply] at free,
      fun _ _ _ _ _ member => by simp [readPlaced] at member,
      fun _ _ _ _ _ _ _ index free => absurd free not_freeIn_inaction⟩
  | fuel + 1 => by
      obtain ⟨formsBelow, placedBelow, componentBelow⟩ := decode_unread fuel
      refine ⟨fun {isLoc place form} well index free => ?_,
        fun {isLoc place count components} well at' part sub out member index free => ?_,
        fun {isLoc place count components} well at' component elsewhere member sits sub index free => ?_⟩
      · obtain ⟨count, components⟩ := form
        obtain ⟨out, member, outFree⟩ := (freeIn_toPattern (block := ambientRepBlock)).mp free
        simp only [decodeForm] at member outFree
        have unread := placedBelow well _ components (fun _ inside => inside) out member (index + count) outFree
        simpa [insideLoc] using unread
      · rw [readPlaced_succ] at member
        obtain ⟨component, inFiltered, rfl⟩ := List.mem_map.mp member
        obtain ⟨inPart, isPlaced⟩ := List.mem_filter.mp inFiltered
        exact componentBelow well at' component _ (sub _ inPart) (by simpa [placedAt] using isPlaced)
          (fun other inRest => sub _ (List.mem_filter.mp inRest).1) index free
      · cases well with
        | intro _ _ _ _ names caps reps _ _ messages capConts bodies =>
        cases component with
        | apply label arguments =>
            rcases arguments with _ | ⟨first, _ | ⟨second, _ | ⟨third, _ | ⟨fourth, rest⟩⟩⟩⟩
            · simp [readComponent, not_freeIn_inaction] at free
            · -- a replication
              simp only [readComponent] at free
              split_ifs at free with isRep
              · obtain ⟨inner, inArguments, innerFree⟩ := freeIn_apply.mp free
                simp only [List.mem_cons, List.not_mem_nil, or_false] at inArguments
                subst inArguments
                rw [isRep] at member sits
                exact formsBelow (reps _ member first at' rfl sits) index innerFree
              · exact absurd free not_freeIn_inaction
            · -- an input or an output
              cases second with
              | lambda binder body =>
                  by_cases isInput : label ∈ inputs
                  · rw [readComponent_input isInput] at free
                    obtain ⟨argument, inArguments, argumentFree⟩ := freeIn_apply.mp free
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at inArguments
                    subst inArguments
                    have placeIs : first = at' := by
                      rw [placeAt_input isInput] at sits
                      exact Option.some.inj sits
                    subst placeIs
                    have unread := formsBelow (bodies _ member label first binder body rfl isInput) (index + 1)
                      (Mettapedia.OSLF.MeTTaIL.CanonicalBags.freeIn_lambda.mp argumentFree)
                    simpa [underName] using unread
                  · by_cases isOutput : label ∈ outputs
                    · rw [readComponent_output isOutput] at free
                      split_ifs at free with isMsg
                      · obtain ⟨argument, inArguments, argumentFree⟩ := freeIn_apply.mp free
                        simp only [List.mem_cons, List.not_mem_nil, or_false] at inArguments
                        subst inArguments
                        simp [isMessage] at isMsg
                      · exact absurd free not_freeIn_inaction
                    · simp [readComponent, isInput, isOutput, not_freeIn_inaction] at free
              | _ =>
                  by_cases isOutput : label ∈ outputs
                  · rw [readComponent_output isOutput] at free
                    split_ifs at free with isMsg
                    · obtain ⟨argument, inArguments, argumentFree⟩ := freeIn_apply.mp free
                      simp only [List.mem_cons, List.not_mem_nil, or_false] at inArguments
                      subst inArguments
                      exact (messages _ member _ (by simp [messageOf, isOutput])).2 _
                        (freeIn_messageVariables isMsg argumentFree)
                    · exact absurd free not_freeIn_inaction
                  · simp [readComponent, isOutput, not_freeIn_inaction] at free
            · simp only [readComponent] at free
              split_ifs at free with isMarker isVar isCap isVar' isLCap isMsg
              · -- a marker: its name, and what sits at its location
                rcases freeIn_wrapContent free with argumentFree | argumentFree
                · have named := (names _ member third (by simp [nameOf, isMarker])).2
                  rwa [freeIn_variable isVar argumentFree] at named
                · obtain ⟨out, outMember, outFree⟩ := (freeIn_body (block := ambientRepBlock)).mp argumentFree
                  exact placedBelow (.intro ‹_› ‹_› ‹_› ‹_› names caps reps ‹_› ‹_› messages capConts bodies) second
                    elsewhere sub out outMember index outFree
              · exact absurd free not_freeIn_inaction
              · -- a capability: its name, and its continuation read at its place
                obtain ⟨argument, inArguments, argumentFree⟩ := freeIn_apply.mp free
                simp only [List.mem_cons, List.not_mem_nil, or_false] at inArguments
                rcases inArguments with rfl | rfl
                · have named := (names _ member argument (by simp [nameOf, isMarker, isCap])).2
                  rwa [freeIn_variable isVar' argumentFree] at named
                · have placeIs : first = at' := by
                    rw [placeAt_capability isCap] at sits
                    exact Option.some.inj sits
                  subst placeIs
                  exact formsBelow (caps _ member label first second third rfl isCap) index argumentFree
              · exact absurd free not_freeIn_inaction
              · -- a prefix by a capability term: its message, and its continuation read at its place
                subst isLCap
                obtain ⟨argument, inArguments, argumentFree⟩ := freeIn_apply.mp free
                simp only [List.mem_cons, List.not_mem_nil, or_false] at inArguments
                rcases inArguments with rfl | rfl
                · exact (messages _ member argument (by simp [messageOf])).2 _
                    (freeIn_messageVariables isMsg argumentFree)
                · have placeIs : first = at' := by
                    rw [placeAt_cap] at sits
                    exact Option.some.inj sits
                  subst placeIs
                  exact formsBelow (capConts _ member first second third rfl) index argumentFree
              · exact absurd free not_freeIn_inaction
              · exact absurd free not_freeIn_inaction
            · simp [readComponent, not_freeIn_inaction] at free
        | _ => simp [readComponent, not_freeIn_inaction] at free

/-! ## The root location -/

/-- **A process located at the root**: its located canonical form, at a root location bound outside it. -/
def rootForm (process : Pattern) : Prenex := canonP locatedRepBlock (located process)

/-- **The root read-back**: the root block read back at the root, with fuel enough to settle. -/
def rootRead (process : Pattern) : Pattern :=
  Prenex.toPattern ambientBlock (decodeForm (3 * (rootForm process).mass + 3) (.bvar 0) (rootForm process))

/-- **The ambient canonical form**: the root read-back, which does not use the root, without it. -/
def canonA (process : Pattern) : Pattern := rename (dropIndex 0) (rootRead process)

variable {free : FreeTypeContext}

theorem root_locVariables : LocVariables (· = Pattern.bvar 0) := fun _ same => by subst same; rfl

/-- **The root block reads back as the process**, the root bound outside it. -/
theorem rootForm_facts (names : NameContext free) {process : Pattern}
    (typed : HasType ambientCoreCalc free [] process procType) (object : isObjectPattern process = true) :
    EncodeFacts free (· = Pattern.bvar 0) 0 [nameType] (rootForm process) (rename Nat.succ process) :=
  decode_encode names (size process + 1) (count := 0) (count' := 1) (relabel := Nat.succ) (here := 0)
    (isLoc := (· = Pattern.bvar 0)) (Nat.lt_succ_self _) (fun _ below => absurd below (Nat.not_lt_zero _))
    (by omega) root_locVariables rfl (fun _ below => absurd below (Nat.not_lt_zero _)) (fun _ same => by cases same)
    typed object

theorem rootRead_typed {process reading : Pattern}
    (facts : EncodeFacts free (· = Pattern.bvar 0) 0 [nameType] (rootForm process) reading) :
    HasType ambientCoreCalc free [nameType] (rootRead process) procType :=
  restricts_typed (language := ambientCoreCalc) (block := ambientBlock) _
    (body_typed ((decode_typed (free := free) _).1 (bound := [nameType]) (.bvar 0) (rootForm process) facts.2.1))

/-- **The root read-back does not use the root.** -/
theorem rootRead_unused {process reading : Pattern}
    (facts : EncodeFacts free (· = Pattern.bvar 0) 0 [nameType] (rootForm process) reading) :
    ¬ FreeIn 0 (rootRead process) :=
  fun used => (decode_unread _).1 facts.1 0 used rfl

theorem rootRead_equivalent {process reading : Pattern}
    (facts : EncodeFacts free (· = Pattern.bvar 0) 0 [nameType] (rootForm process) reading) :
    ProcEquiv ambientCoreCalc ambientBlock free [nameType] (rootRead process) reading := by
  obtain ⟨-, -, least, reads⟩ := facts
  have settled := decodeForm_settled (.bvar 0) (rootForm process) (first := 3 * (rootForm process).mass + 3)
    (second := max least (3 * (rootForm process).mass + 3)) le_rfl (le_max_right _ _)
  unfold rootRead
  rw [settled]
  exact reads _ (le_max_left _ _)

/-- **The ambient canonical form of a closed process** is a closed object process equivalent to it: the root read-back
lifted past the root. -/
theorem canonA_facts (names : NameContext free) {process : Pattern}
    (typed : HasType ambientCoreCalc free [] process procType) (object : isObjectPattern process = true) :
    HasType ambientCoreCalc free [] (canonA process) procType ∧ isObjectPattern (canonA process) = true ∧
      liftBVars 0 1 (canonA process) = rootRead process ∧
      ProcEquiv ambientCoreCalc ambientBlock free [] process (canonA process) := by
  have facts := rootForm_facts names typed object
  have readTyped := rootRead_typed facts
  have unused := rootRead_unused facts
  have canonTyped : HasType ambientCoreCalc free [] (canonA process) procType := by
    simpa [canonA] using drop_typed (language := ambientCoreCalc) (inner := []) (outer := []) readTyped unused
  have lifted : liftBVars 0 1 (canonA process) = rootRead process := by
    unfold canonA
    rw [liftBVars_eq_rename, rename_comp]
    conv_rhs => rw [← rename_id (rootRead process)]
    refine rename_congr _ fun index used => ?_
    have positive : index ≠ 0 := fun same => unused (same ▸ used)
    simp only [Function.comp, shiftAbove, dropIndex, id]
    split_ifs <;> omega
  have canonObject : isObjectPattern (canonA process) = true := by
    unfold canonA rootRead
    rw [isObjectPattern_rename]
    exact isObject_toPattern ((decode_object _).1 _ _)
  refine ⟨canonTyped, canonObject, lifted, ?_⟩
  have equivalent := rootRead_equivalent facts
  have succIs : rename Nat.succ process = liftBVars 0 1 process := by
    simpa [rename_id] using rename_succ_comp id process
  rw [← lifted, succIs] at equivalent
  exact .trans _ _ _ (.symm _ _ (garbage_equivalent (language := ambientCoreCalc) (block := ambientBlock) typed))
    (.trans _ _ _ (restrict_fill (language := ambientCoreCalc) (block := ambientBlock) (.symm _ _ equivalent))
      (garbage_equivalent (language := ambientCoreCalc) (block := ambientBlock) canonTyped))

/-- **Processes related by a chain of laws have one root canonical block**: their root located forms are related by a
chain of laws of the located calculus, which its canonical form decides. -/
theorem rootForm_same (names : NameContext free) {first second : Pattern}
    (firstTyped : HasType ambientCoreCalc free [] first procType) (firstObject : isObjectPattern first = true)
    (secondTyped : HasType ambientCoreCalc free [] second procType) (secondObject : isObjectPattern second = true)
    (chain : ObjectChain ambientCoreCalc free [] procType first second) : rootForm first = rootForm second := by
  have fresh : locatedRepBlock.replicate ∉ locatedRepBlock.emptyUnits := by decide
  have restrictFresh : locatedRepBlock.replicate ≠ locatedRepBlock.restrict := by decide
  have hereTyped : HasType locatedCalc free (List.replicate 1 nameType) (.bvar 0) nameType := .bvar rfl
  have locatedChain := located_chain names
    (LocatedFrame.ofNames (count := 0) (count' := 1) (relabel := Nat.succ)
      fun _ below => absurd below (Nat.not_lt_zero _)) hereTyped rfl chain
  have encodedBinds : ∀ {process : Pattern}, HasType ambientCoreCalc free [] process procType →
      isObjectPattern process = true →
      Mettapedia.GSLT.LanguageDef.RestrictionBlocks.restrictionsBind locatedRepBlock.toBlock (located process) = true :=
    fun typed object => restrictionsBind_of_typed (block := locatedRepBlock) _
      (encode_typed names (size _ + 1) (Nat.lt_succ_self _) (count := 0) (count' := 1)
        (fun _ below => absurd below (Nat.not_lt_zero _)) hereTyped rfl typed object)
  have same := canonR_complete (block := locatedRepBlock) (base := engineBasePremises RelationEnv.empty)
    (located_object firstObject) (located_object secondObject) (encodedBinds firstTyped firstObject)
    locatedChain.toEquationEquiv
  have firstFacts := canonFacts fresh restrictFresh (located_object firstObject) (encodedBinds firstTyped firstObject)
  have secondFacts := canonFacts fresh restrictFresh (located_object secondObject)
    (encodedBinds secondTyped secondObject)
  have decomposed := congrArg (decompose locatedRepBlock.toBlock) same
  unfold canonR at decomposed
  rwa [decompose_toPattern firstFacts.atomic firstFacts.used,
    decompose_toPattern secondFacts.atomic secondFacts.used] at decomposed

/-- **Processes related by a chain of laws have one ambient canonical form.** -/
theorem canonA_same (names : NameContext free) {first second : Pattern}
    (firstTyped : HasType ambientCoreCalc free [] first procType) (firstObject : isObjectPattern first = true)
    (secondTyped : HasType ambientCoreCalc free [] second procType) (secondObject : isObjectPattern second = true)
    (chain : ObjectChain ambientCoreCalc free [] procType first second) : canonA first = canonA second := by
  unfold canonA rootRead
  rw [rootForm_same names firstTyped firstObject secondTyped secondObject chain]

end Mettapedia.Languages.ProcessCalculi.Ambient.Decoding
