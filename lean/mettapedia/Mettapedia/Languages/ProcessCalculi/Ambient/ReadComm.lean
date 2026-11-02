import Mettapedia.Languages.ProcessCalculi.Ambient.ReadCanon
import Mettapedia.Languages.ProcessCalculi.Ambient.LocatedComm
import Mettapedia.Languages.ProcessCalculi.Ambient.DecodingWellSubstitution

/-!
# A located communication, read back as a step

A communication of a well-located block — an input and an output at one place — reads back, from the place, as a
communication of the place's readings: the input reads as an input whose body is its body's block read under the
binder, the output as the output of its message, and the two step, in the bag of the padded readings at the place, to
the body's reading with the message received (`comm_local`). That is the received body read at the place
(`decode_instantiate`), padding commuting with receiving a message (`padA_instantiate`); the received body's block
stands, in the reacted block, at the place, beside the components the communication leaves (`commList`), under its
own restrictions. Down the path of ambients from the root the step is taken inside each ambient, or in place past an
opened one, as for every located reaction (`path_step_of`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Steps

open Mettapedia.Languages.ProcessCalculi.Ambient.Comm (ambientCoreCalc AmbCommRawStep channels)

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars instantiateBVar)
open Mettapedia.OSLF.MeTTaIL.ContextSubstitution (Assignment substitute lift single substituteList_eq_map
  substitute_single_eq_instantiateBVar)
open Mettapedia.GSLT.LanguageDef.WellSorted (HasType FreeTypeContext isObjectPattern isObjectPatternList)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (Prenex Members ProcEquiv rename decompose sizeList size
  body_congr body_perm_equivalent bag_body_equivalent restricts_congr restricts_typed body_typed liftBVars_eq_rename)
open Mettapedia.Languages.ProcessCalculi.Ambient.Full (ambientBlock)
open Mettapedia.Languages.ProcessCalculi.Ambient.Located (locatedCalc locatedBlock)
open Mettapedia.Languages.ProcessCalculi.Ambient.Encoding (nameType procType single_messages)
open Mettapedia.Languages.ProcessCalculi.Ambient.Decoding (isVariable isMessage Reaches placedAt placeAt childOf
  readPlaced readComponent readPlaced_succ decodeForm decodeAt inputs outputs ambientInput ambientOutput
  readComponent_input readComponent_output placeAt_input placeAt_output decode_typed decode_object decodeForm_settled
  decodeForm_typed restricts_body_split readComponent_lifted lift_ne_owned WellLocated underName messages_liftN
  decode_instantiate)

variable {free : FreeTypeContext}

/-! ## Padding a received message -/

/-- An ambient's content as a bag, after a substitution of messages, is the substituted content as a bag. -/
theorem asBag_substitute {assignment : Assignment} (messages : ∀ index, isMessage (assignment index) = true)
    (content : Pattern) : substitute assignment (asBag content) = asBag (substitute assignment content) := by
  cases content with
  | bvar index =>
      have notBag : ∀ elements, assignment index ≠ .collection .hashBag elements none := fun elements same => by
        have isMsg := messages index
        rw [same] at isMsg
        simp [isMessage] at isMsg
      show Pattern.collection .hashBag [assignment index] none = asBag (assignment index)
      unfold asBag
      split
      · rename_i elements same
        exact absurd same (notBag elements)
      · rfl
  | collection kind elements rest =>
      cases kind <;> cases rest <;> simp [asBag, substitute, substituteList_eq_map]
  | _ => simp [asBag, substitute, substituteList_eq_map]

theorem padApply_substitute {assignment : Assignment} (messages : ∀ index, isMessage (assignment index) = true)
    (label : String) (arguments : List Pattern) :
    substitute assignment (padApply label arguments) = padApply label (arguments.map (substitute assignment)) := by
  match arguments with
  | [name, content] =>
      simp only [padApply, List.map_cons, List.map_nil]
      split_ifs
      · simp only [substitute, substituteList_eq_map, List.map_cons, List.map_nil, asBag_substitute messages]
      · simp [substitute, substituteList_eq_map]
  | [] => simp [padApply, substitute]
  | [_] => simp [padApply, substitute, substituteList_eq_map]
  | _ :: _ :: _ :: _ => simp [padApply, substitute, substituteList_eq_map]

/-- **Padding commutes with a substitution of messages**: messages hold no ambient. -/
theorem padA_substitute (pattern : Pattern) : ∀ {assignment : Assignment},
    (∀ index, isMessage (assignment index) = true) →
      padA (substitute assignment pattern) = substitute assignment (padA pattern) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro assignment messages; exact padA_message (messages index)
  | hfvar => intros; rfl
  | happly label arguments recurse =>
      intro assignment messages
      simp only [substitute, substituteList_eq_map, padA, padAList_eq_map, List.map_map]
      rw [padApply_substitute messages, List.map_map]
      congr 1
      exact List.map_congr_left fun argument member => by
        simp only [Function.comp]
        exact recurse argument member messages
  | hlambda binder body recurse =>
      intro assignment messages
      simp only [substitute, padA]
      rw [recurse (messages_liftN messages 1)]
  | hmultiLambda arity binders body recurse =>
      intro assignment messages
      simp only [substitute, padA]
      rw [recurse (messages_liftN messages arity)]
  | hsubst body replacement bodyRecurse replacementRecurse =>
      intro assignment messages
      simp only [substitute, padA]
      rw [bodyRecurse (messages_liftN messages 1), replacementRecurse messages]
  | hcollection kind elements rest recurse =>
      intro assignment messages
      simp only [substitute, substituteList_eq_map, padA, padAList_eq_map, List.map_map]
      congr 1
      exact List.map_congr_left fun element member => by
        simp only [Function.comp]
        exact recurse element member messages

/-- **Padding commutes with receiving a message.** -/
theorem padA_instantiate {message : Pattern} (isMsg : isMessage message = true) (body : Pattern) :
    instantiateBVar message (padA body) = padA (instantiateBVar message body) := by
  rw [← substitute_single_eq_instantiateBVar, ← substitute_single_eq_instantiateBVar,
    padA_substitute body (single_messages isMsg)]

/-! ## What a communication leaves, in place -/

/-- **The components a communication leaves, in place**: its input and its output gone. -/
def commList (comm : LocComm) (components : List Pattern) : List Pattern :=
  (components.erase comm.input).erase comm.output

theorem commList_filter (comm : LocComm) (keep : Pattern → Bool) (components : List Pattern) :
    (commList comm components).filter keep = commList comm (components.filter keep) := by
  unfold commList
  rw [← List.erase_filter, ← List.erase_filter]

theorem commList_untouched {comm : LocComm} {components : List Pattern} (noInput : comm.input ∉ components)
    (noOutput : comm.output ∉ components) : commList comm components = components := by
  unfold commList
  rw [List.erase_of_not_mem noInput, List.erase_of_not_mem noOutput]

theorem mem_commList {comm : LocComm} {component : Pattern} {components : List Pattern}
    (member : component ∈ commList comm components) : component ∈ components :=
  List.mem_of_mem_erase (List.mem_of_mem_erase member)

/-- **What a communication leaves, in place, is the rest.** -/
theorem commList_perm {comm : LocComm} {components rest : List Pattern}
    (split : components.Perm (comm.parts ++ rest)) : (commList comm components).Perm rest := by
  unfold commList
  have first : (components.erase comm.input).Perm (comm.output :: rest) := by
    simpa [LocComm.parts] using split.erase comm.input
  simpa using first.erase comm.output

theorem LocComm.input_ne_output (comm : LocComm) : comm.input ≠ comm.output := by
  cases capability : comm.capability <;>
    simp [LocComm.input, LocComm.output, LocComm.inputLabel, LocComm.outputLabel, capability]

/-! ## Steps with communication of bags of one -/

/-- **A bag of one process steps only inside it**, with communication too. -/
theorem comm_bag_single_step {item result : Pattern} {tail : Option String}
    (step : AmbCommRawStep (.collection .hashBag [item] tail) result) :
    ∃ inner, AmbCommRawStep item inner ∧ result = .collection .hashBag [inner] none := by
  cases step with
  | «open» i hi j hj =>
      have zero : i = 0 := by simpa using hi
      subst zero
      simp at hj
  | enter i hi j hj =>
      have zero : i = 0 := by simpa using hi
      subst zero
      simp at hj
  | comm listed i hi j hj =>
      have zero : i = 0 := by simpa using hi
      subst zero
      simp at hj
  | par i hi inner =>
      have zero : i = 0 := by simpa using hi
      subst zero
      exact ⟨_, inner, rfl⟩

/-! ## A communication at its place -/

open Mettapedia.Languages.ProcessCalculi.Ambient.Decoding (placeAt_rename)

/-- **A communication at its place reads as a communication there**: the input and the output, read at the place,
step to the input's body read with the message received, which is the received body read at the place, standing with
the components the communication leaves under the received body's restrictions. -/
theorem comm_local {bound : List TypeExpr} {count : Nat} {components : List Pattern} {depth : Nat → Nat}
    (children : ∀ component ∈ components, ∀ child, childOf component = some child →
      ∃ index < count, child = .bvar index)
    (grows : ∀ component ∈ components, ∀ index child, index < count → child < count →
      placeAt component = some (.bvar index) → childOf component = some (.bvar child) → depth index < depth child)
    (typed : Members locatedCalc locatedBlock free bound components)
    {comm : LocComm} {isLoc : Pattern → Prop}
    (bodyWell : WellLocated (underName isLoc) (liftBVars 0 1 comm.place) (decompose locatedBlock comm.body))
    (bodyTyped : HasType locatedCalc free (.base (LocComm.sort comm.capability) :: bound) comm.body procType)
    (isMsg : isMessage comm.message = true)
    (nameVar : TypeExpr.base (LocComm.sort comm.capability) = nameType → isVariable comm.message = true)
    {owned : Nat} {group : List Pattern}
    (decomposed : decompose locatedBlock (instantiateBVar comm.message comm.body) = ⟨owned, group⟩)
    (groupPlaced : ∀ component ∈ group, ∀ at', placeAt component = some at' →
      at' = liftBVars 0 owned comm.place ∨ ∃ index < owned, at' = .bvar index)
    (groupChildren : ∀ component ∈ group, ∀ child, childOf component = some child →
      ∃ index < owned, child = .bvar index)
    (groupTyped : Members locatedCalc locatedBlock free (List.replicate owned nameType ++ bound) group)
    {list : List Pattern} (sub : list.Sublist components)
    (inputIn : comm.input ∈ list) (outputIn : comm.output ∈ list)
    (fuel : Nat) (enough : 3 * size (instantiateBVar comm.message comm.body) + 6 ≤ fuel) :
    ∃ result, AmbCommRawStep (.collection .hashBag ((readPlaced fuel comm.place list).map padA) none) result ∧
      ProcEquiv ambientCoreCalc ambientBlock free bound result (Prenex.restricts ambientBlock owned
        (Prenex.body ambientBlock (readPlaced fuel (liftBVars 0 owned comm.place)
          ((commList comm list).map (liftBVars 0 owned) ++ group)))) := by
  have within : ∀ component ∈ list, component ∈ components := fun component inList => sub.subset inList
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 3 := ⟨fuel - 3, by omega⟩
  have inputListed := LocComm.inputLabel_mem comm.capability
  have outputListed := LocComm.outputLabel_mem comm.capability
  have inputPlaced : placedAt comm.place comm.input = true := by
    simp [placedAt, LocComm.input, placeAt_input inputListed]
  have outputPlaced : placedAt comm.place comm.output = true := by
    simp [placedAt, LocComm.output, placeAt_output outputListed]
  set here := list.filter (placedAt comm.place) with hereIs
  set elsewhere := list.filter fun other => !placedAt comm.place other with elsewhereIs
  have inputHere : comm.input ∈ here := List.mem_filter.mpr ⟨inputIn, inputPlaced⟩
  have outputHere : comm.output ∈ here := List.mem_filter.mpr ⟨outputIn, outputPlaced⟩
  -- the input and the output among the components at the place
  obtain ⟨i, hi, inputAt⟩ := List.getElem_of_mem inputHere
  have outputRest : comm.output ∈ here.eraseIdx i := by
    obtain ⟨j₀, hj₀, outputAt₀⟩ := List.getElem_of_mem outputHere
    refine List.mem_eraseIdx_iff_getElem.mpr ⟨j₀, hj₀, fun same => ?_, outputAt₀⟩
    subst same
    rw [inputAt] at outputAt₀
    exact LocComm.input_ne_output comm outputAt₀
  obtain ⟨j, hj, outputAt⟩ := List.getElem_of_mem outputRest
  set others := (here.eraseIdx i).eraseIdx j with othersIs
  have hereSplit : here.Perm (comm.input :: comm.output :: others) := by
    have split := perm_two here i hi j hj
    rwa [inputAt, outputAt] at split
  have othersHere : ∀ component ∈ others, component ∈ here := fun component inOthers =>
    hereSplit.symm.subset (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ inOthers))
  -- the source: the communication of the padded items at the place
  set readS := fun component => readComponent (f + 2) comm.place component elsewhere with readSIs
  have sourceIs : (readPlaced (f + 3) comm.place list).map padA = here.map (padA ∘ readS) := by
    rw [readPlaced_succ, List.map_map]
  set received := decodeAt (f + 1) (liftBVars 0 1 comm.place) comm.body with receivedIs
  have inputRead : (padA ∘ readS) comm.input =
      .apply (ambientInput (LocComm.inputLabel comm.capability)) [.lambda none (padA received)] := by
    simp only [Function.comp, readSIs, LocComm.input]
    rw [readComponent_input inputListed]
    simp [padA, padAList, padApply]
    rfl
  have outputRead : (padA ∘ readS) comm.output =
      .apply (ambientOutput (LocComm.outputLabel comm.capability)) [comm.message] := by
    simp only [Function.comp, readSIs, LocComm.output]
    rw [readComponent_output outputListed, if_pos isMsg]
    simp [padA, padAList, padApply, padA_message isMsg]
  have hiItems : i < (here.map (padA ∘ readS)).length := by simpa using hi
  have inputItem : (here.map (padA ∘ readS))[i] =
      .apply (ambientInput (LocComm.inputLabel comm.capability)) [.lambda none (padA received)] := by
    rw [List.getElem_map, inputAt, inputRead]
  have erasedMap : (here.map (padA ∘ readS)).eraseIdx i = (here.eraseIdx i).map (padA ∘ readS) :=
    List.eraseIdx_map _ _ _
  have hjItems : j < ((here.map (padA ∘ readS)).eraseIdx i).length := by rw [erasedMap]; simpa using hj
  have outputItem : ((here.map (padA ∘ readS)).eraseIdx i)[j] =
      .apply (ambientOutput (LocComm.outputLabel comm.capability)) [comm.message] := by
    refine (List.getElem_of_eq erasedMap hjItems).trans ?_
    rw [List.getElem_map, outputAt, outputRead]
  have channel : (ambientInput (LocComm.inputLabel comm.capability),
      ambientOutput (LocComm.outputLabel comm.capability)) ∈ channels := by
    cases comm.capability <;>
      simp [ambientInput, ambientOutput, LocComm.inputLabel, LocComm.outputLabel, channels]
  have step := AmbCommRawStep.comm (tail := none) channel i hiItems j hjItems none (padA received) comm.message
    inputItem outputItem
  have restIs : ((here.map (padA ∘ readS)).eraseIdx i).eraseIdx j = others.map (padA ∘ readS) := by
    rw [erasedMap, List.eraseIdx_map]
  rw [restIs] at step
  rw [sourceIs]
  refine ⟨_, step, ?_⟩
  -- the target: the components left at the lifted place, beside the received body's
  have notElsewhere : ∀ {piece : Pattern}, placedAt comm.place piece = true → piece ∉ elsewhere :=
    fun placed inElsewhere => by simp [elsewhereIs, placed] at inElsewhere
  have reactedHere : (commList comm list).filter (placedAt comm.place) = commList comm here :=
    commList_filter comm _ list
  have reactedElsewhere : (commList comm list).filter (fun other => !placedAt comm.place other) = elsewhere := by
    rw [commList_filter]
    exact commList_untouched (notElsewhere inputPlaced) (notElsewhere outputPlaced)
  set groupHere := group.filter (placedAt (liftBVars 0 owned comm.place)) with groupHereIs
  set groupDeep := group.filter fun other => !placedAt (liftBVars 0 owned comm.place) other with groupDeepIs
  set readT := fun component => readComponent (f + 2) (liftBVars 0 owned comm.place) component
    (elsewhere.map (liftBVars 0 owned) ++ groupDeep) with readTIs
  have hereT : ((commList comm list).map (liftBVars 0 owned) ++ group).filter
      (placedAt (liftBVars 0 owned comm.place)) = (commList comm here).map (liftBVars 0 owned) ++ groupHere := by
    rw [List.filter_append, filter_lift_at, reactedHere]
  have elsewhereT : ((commList comm list).map (liftBVars 0 owned) ++ group).filter
      (fun other => !placedAt (liftBVars 0 owned comm.place) other) =
      elsewhere.map (liftBVars 0 owned) ++ groupDeep := by
    rw [List.filter_append, filter_lift_elsewhere, reactedElsewhere]
  have targetIs : readPlaced (f + 3) (liftBVars 0 owned comm.place)
      ((commList comm list).map (liftBVars 0 owned) ++ group) =
      ((commList comm here).map (liftBVars 0 owned)).map readT ++ groupHere.map readT := by
    rw [readPlaced_succ, hereT, elsewhereT, List.map_append]
  rw [targetIs]
  -- the deep part of the received body sits at its own locations
  have groupDeepPlaced : ∀ component ∈ groupDeep, ∀ at', placeAt component = some at' →
      at' = liftBVars 0 owned comm.place ∨ ∃ index < owned, at' = .bvar index := fun component inDeep =>
    groupPlaced component (List.mem_filter.mp inDeep).1
  have groupDeepChildren : ∀ component ∈ groupDeep, ∀ child, childOf component = some child →
      ∃ index < owned, child = .bvar index := fun component inDeep =>
    groupChildren component (List.mem_filter.mp inDeep).1
  have liftedApart : ∀ component ∈ elsewhere.map (liftBVars 0 owned), ∀ at', placeAt component = some at' →
      ∀ index < owned, at' ≠ .bvar index := by
    intro component inLifted at' sits index below same
    obtain ⟨original, -, rfl⟩ := List.mem_map.mp inLifted
    rw [liftBVars_eq_rename, placeAt_rename] at sits
    cases found : placeAt original with
    | none => rw [found] at sits; cases sits
    | some originalAt =>
        rw [found, Option.map_some, Option.some.injEq, ← liftBVars_eq_rename] at sits
        rw [← sits] at same
        exact lift_ne_owned below same
  -- each component left, read
  have othersRead : ∀ component ∈ others,
      readT (liftBVars 0 owned component) = liftBVars 0 owned (readS component) := by
    intro component inOthers
    have inHere := othersHere component inOthers
    exact readComponent_lifted groupDeepPlaced (f + 2) comm.place component fun child isChild =>
      not_reaches_back children grows within (List.mem_filter.mp inHere).1 (List.mem_filter.mp inHere).2 isChild
  have groupRead : ∀ component ∈ groupHere, readT component =
      readComponent (f + 2) (liftBVars 0 owned comm.place) component groupDeep := by
    intro component inHere'
    exact group_reads groupDeepChildren liftedApart (f + 2) _ component
      (groupChildren component (List.mem_filter.mp inHere').1)
  -- the received body, read at the place
  set continuationRead := Prenex.toPattern ambientBlock
    (decodeForm (f + 1) comm.place (decompose locatedBlock (instantiateBVar comm.message comm.body)))
    with continuationReadIs
  have massBound : 3 * Prenex.mass ⟨owned, group⟩ + 3 ≤ f + 1 := by
    have massLe := Mettapedia.GSLT.LanguageDef.RestrictionBlocks.mass_decompose (block := locatedBlock)
      (instantiateBVar comm.message comm.body)
    rw [decomposed] at massLe
    omega
  have continuationIs : continuationRead = Prenex.restricts ambientBlock owned (Prenex.body ambientBlock
      (groupHere.map fun component => readComponent (f + 2) (liftBVars 0 owned comm.place) component groupDeep)) := by
    rw [continuationReadIs, decomposed, decodeForm_settled comm.place _ massBound (show 3 * _ + 3 ≤ f + 4 by omega)]
    simp only [decodeForm, Prenex.toPattern]
    rw [readPlaced_succ]
  have receivedRead : instantiateBVar comm.message (padA received) = padA continuationRead := by
    rw [padA_instantiate isMsg, receivedIs, ← decode_instantiate bodyWell bodyTyped isMsg nameVar (f + 1)]
    rfl
  -- typing
  have elsewhereMembers : Members locatedCalc locatedBlock free bound elsewhere := fun component inElsewhere =>
    typed component (within component (List.mem_filter.mp inElsewhere).1)
  have readSTyped : ∀ component ∈ others, HasType ambientCoreCalc free bound (readS component) procType :=
    fun component inOthers => (decode_typed (f + 2)).2.2 comm.place component elsewhere
      (typed component (within component (List.mem_filter.mp (othersHere component inOthers)).1)) elsewhereMembers
  have readSObject : ∀ component, isObjectPattern (readS component) = true := fun component =>
    (decode_object (f + 2)).2.2 comm.place component elsewhere
  have continuationTyped : HasType ambientCoreCalc free bound continuationRead procType := by
    rw [continuationReadIs, decomposed]
    exact decodeForm_typed (f + 1) comm.place groupTyped
  have continuationObject : isObjectPattern continuationRead = true :=
    Mettapedia.GSLT.LanguageDef.RestrictionBlocks.isObject_toPattern ((decode_object (f + 1)).1 comm.place _)
  have keptMembers : Members ambientCoreCalc ambientBlock free bound (others.map readS) := by
    intro item inItems
    obtain ⟨original, inOthers, rfl⟩ := List.mem_map.mp inItems
    exact readSTyped original inOthers
  have groupItems : groupHere.map readT = groupHere.map
      (fun component => readComponent (f + 2) (liftBVars 0 owned comm.place) component groupDeep) :=
    List.map_congr_left groupRead
  have groupMembers : Members ambientCoreCalc ambientBlock free (List.replicate owned nameType ++ bound)
      (groupHere.map readT) := by
    rw [groupItems]
    have groupReading := (decode_typed (f + 3)).2.1 (liftBVars 0 owned comm.place) group groupTyped
    rw [readPlaced_succ] at groupReading
    exact groupReading
  have liftedKept : Members ambientCoreCalc ambientBlock free (List.replicate owned nameType ++ bound)
      ((others.map readS).map (liftBVars 0 owned)) := by
    have lifted := Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Members.lift (language := ambientCoreCalc)
      (block := ambientBlock) (List.replicate owned nameType) keptMembers
    rwa [List.length_replicate] at lifted
  -- the components left at the place: the others, in another order
  have reactedPerm : (commList comm here).Perm others := by
    unfold commList
    have erased : (here.erase comm.input).Perm (comm.output :: others) := by
      simpa using hereSplit.erase comm.input
    simpa using erased.erase comm.output
  have itemsPerm : (((commList comm here).map (liftBVars 0 owned)).map readT).Perm
      ((others.map readS).map (liftBVars 0 owned)) := by
    have mapped := (reactedPerm.map (liftBVars 0 owned)).map readT
    refine mapped.trans (.of_eq ?_)
    simp only [List.map_map]
    exact List.map_congr_left fun component inOthers => othersRead component inOthers
  -- assembled
  have targetSide : ProcEquiv ambientCoreCalc ambientBlock free bound
      (Prenex.restricts ambientBlock owned (Prenex.body ambientBlock
        (((commList comm here).map (liftBVars 0 owned)).map readT ++ groupHere.map readT)))
      (Prenex.body ambientBlock (continuationRead :: others.map readS)) := by
    have allMembers : Members ambientCoreCalc ambientBlock free (List.replicate owned nameType ++ bound)
        (((commList comm here).map (liftBVars 0 owned)).map readT ++ groupHere.map readT) :=
      fun item inItems => (liftedKept.append groupMembers) item ((itemsPerm.append_right _).subset inItems)
    refine .trans _ _ _ (restricts_congr (language := ambientCoreCalc) (block := ambientBlock) owned
      (body_perm_equivalent allMembers (itemsPerm.append_right _))) ?_
    refine .trans _ _ _ (restricts_body_split owned keptMembers groupMembers) ?_
    rw [groupItems, ← continuationIs]
    exact .refl _
  have sourceMembers : Members ambientCoreCalc ambientBlock free bound
      (padA continuationRead :: others.map (padA ∘ readS)) := by
    intro item inItems
    rcases List.mem_cons.mp inItems with rfl | inRest
    · exact padA_typed continuationTyped continuationObject
    · obtain ⟨original, inOthers, rfl⟩ := List.mem_map.mp inRest
      exact padA_typed (readSTyped original inOthers) (readSObject original)
  have sourceSide : ProcEquiv ambientCoreCalc ambientBlock free bound
      (.collection .hashBag (padA continuationRead :: others.map (padA ∘ readS)) none)
      (Prenex.body ambientBlock (continuationRead :: others.map readS)) := by
    refine .trans _ _ _ (bag_body_equivalent (language := ambientCoreCalc) (block := ambientBlock) sourceMembers) ?_
    refine body_congr sourceMembers (.cons ?_ ?_)
    · exact Relation.EqvGen.symm _ _ (padA_equivalent (size continuationRead + 1) (Nat.lt_succ_self _)
        continuationTyped continuationObject)
    · refine List.forall₂_map_left_iff.mpr (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun component
        inOthers => ?_))
      exact Relation.EqvGen.symm _ _ (padA_equivalent (size (readS component) + 1) (Nat.lt_succ_self _)
        (readSTyped component inOthers) (readSObject component))
  rw [receivedRead]
  exact .trans _ _ _ sourceSide (Relation.EqvGen.symm _ _ targetSide)

/-! ## The received body's block -/

open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (decompose_substitute toPattern_substituteOuter)
open Mettapedia.Languages.ProcessCalculi.Ambient.Encoding (shiftName_eq_liftBVars substitute_single_shiftName)
open Mettapedia.Languages.ProcessCalculi.Ambient.Decoding (messages_atomic placeAt_substitute substitute_lift_outer
  substitute_lift_below isVariable_lift underName_locVariables childOf_bvar_of_kind markers childOf_substitute)

/-- **The block of an input's body receiving a message**: its restrictions are the body's; its components sit at the
input's place or at its own locations, and place ambients at its own locations. -/
theorem received_block {isLoc : Pattern → Prop} {place body message : Pattern}
    (bodyWell : WellLocated (underName isLoc) (liftBVars 0 1 place) (decompose locatedBlock body))
    (isMsg : isMessage message = true) :
    (decompose locatedBlock (instantiateBVar message body)).count = (decompose locatedBlock body).count ∧
      (∀ component ∈ (decompose locatedBlock (instantiateBVar message body)).components, ∀ at',
        placeAt component = some at' →
          at' = liftBVars 0 (decompose locatedBlock body).count place ∨
            ∃ index < (decompose locatedBlock body).count, at' = .bvar index) ∧
      (∀ component ∈ (decompose locatedBlock (instantiateBVar message body)).components, ∀ child,
        childOf component = some child → ∃ index < (decompose locatedBlock body).count, child = .bvar index) := by
  have placeVar : isVariable place = true := by
    have lifted := underName_locVariables isLoc _ bodyWell.placeIsLoc
    rwa [isVariable_lift] at lifted
  have messages := single_messages isMsg
  rw [← substitute_single_eq_instantiateBVar, decompose_substitute (messages_atomic messages)]
  generalize formIs : decompose locatedBlock body = form
  rw [formIs] at bodyWell
  obtain ⟨owned, components⟩ := form
  have liftedMessages := messages_liftN messages owned
  have homeIs : substitute (lift owned (single message)) (liftBVars 0 owned (liftBVars 0 1 place)) =
      liftBVars 0 owned place := by
    rw [substitute_lift_outer, ← shiftName_eq_liftBVars, substitute_single_shiftName]
  -- the places of the body's components receive variables
  have placesVariables : ∀ component ∈ components, ∀ at', placeAt component = some at' →
      (at' = liftBVars 0 owned (liftBVars 0 1 place) ∨ ∃ index < owned, at' = .bvar index) ∧
        isVariable (substitute (lift owned (single message)) at') = true := by
    intro component member at' sits
    rcases bodyWell.placed component member at' sits with same | ⟨index, below, rfl, -⟩
    · refine ⟨.inl same, ?_⟩
      rw [same, homeIs, isVariable_lift]
      exact placeVar
    · exact ⟨.inr ⟨index, below, rfl⟩, by rw [substitute_lift_below below]; rfl⟩
  refine ⟨rfl, fun component member at' sits => ?_, fun component member child isChild => ?_⟩
  · simp only [Prenex.substituteOuter] at member
    obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp member
    rw [placeAt_substitute liftedMessages (fun index found => (placesVariables original inOriginal _ found).2)]
      at sits
    cases found : placeAt original with
    | none => rw [found] at sits; cases sits
    | some originalAt =>
        rw [found, Option.map_some, Option.some.injEq] at sits
        subst sits
        rcases (placesVariables original inOriginal originalAt found).1 with same | ⟨index, below, rfl⟩
        · exact .inl (by rw [same, homeIs])
        · exact .inr ⟨index, below, substitute_lift_below below⟩
  · simp only [Prenex.substituteOuter] at member
    obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp member
    rw [childOf_substitute liftedMessages] at isChild
    cases found : childOf original with
    | none => rw [found] at isChild; cases isChild
    | some originalChild =>
        rw [found, Option.map_some, Option.some.injEq] at isChild
        subst isChild
        obtain ⟨index, below, rfl⟩ := childOf_bvar_of_kind (bodyWell.kinds original inOriginal) found
        exact ⟨index, below, substitute_lift_below below⟩

/-! ## A communication read from the root -/

/-- **A communication of a well-located block reads, from the root, as a step with communication**: the bag of the
padded items read at the root steps to what the components the communication leaves, beside the received body's,
read as there, under the received body's restrictions. -/
theorem root_reacts_comm {isLoc : Pattern → Prop} {place : Pattern} {bound : List TypeExpr} {count : Nat}
    {components : List Pattern} (well : WellLocated isLoc place ⟨count, components⟩)
    (typed : Members locatedCalc locatedBlock free (List.replicate count nameType ++ bound) components)
    {comm : LocComm} {rest : List Pattern} (split : components.Perm (comm.parts ++ rest))
    {owned : Nat} {group : List Pattern}
    (decomposed : decompose locatedBlock (instantiateBVar comm.message comm.body) = ⟨owned, group⟩)
    (fuel : Nat) (enough : 3 * sizeList components + 3 * size (instantiateBVar comm.message comm.body) + 12 ≤ fuel) :
    ∃ result, AmbCommRawStep
        (.collection .hashBag ((readPlaced fuel (liftBVars 0 count place) components).map padA) none) result ∧
      ProcEquiv ambientCoreCalc ambientBlock free (List.replicate count nameType ++ bound) result
        (Prenex.restricts ambientBlock owned (Prenex.body ambientBlock
          (readPlaced fuel (liftBVars 0 owned (liftBVars 0 count place))
            ((commList comm components).map (liftBVars 0 owned) ++ group)))) := by
  have signature : Mettapedia.GSLT.LanguageDef.RestrictionBlocks.BlockSignature locatedCalc locatedBlock :=
    Mettapedia.Languages.ProcessCalculi.Ambient.Located.locatedLanguage.toBlockSignature
  -- what the block gives the path down to the communication
  obtain ⟨depth, grows⟩ := well.nested
  have children : ∀ component ∈ components, ∀ child, childOf component = some child →
      ∃ index < count, child = .bvar index := fun component member _ isChild =>
    childOf_bvar_of_kind (well.kinds component member) isChild
  have unique := well.unique_any
  have markersOf := WellLocated.markersOf well
  have partsMembers : Members locatedCalc locatedBlock free (List.replicate count nameType ++ bound) comm.parts :=
    fun part member => typed part (split.symm.subset (List.mem_append_left _ member))
  have inputIn : comm.input ∈ components := split.symm.subset (by simp [LocComm.parts])
  have outputIn : comm.output ∈ components := split.symm.subset (by simp [LocComm.parts])
  -- the input's body and the output's message
  have inputTyped : HasType locatedCalc free (List.replicate count nameType ++ bound)
      (.apply (LocComm.inputLabel comm.capability) [comm.place, .lambda none comm.body]) procType :=
    typed _ inputIn
  obtain ⟨-, body', same, bodyTyped⟩ := LocComm.input_inv inputTyped
  simp only [Pattern.lambda.injEq, true_and] at same
  subst same
  have outputTyped : HasType locatedCalc free (List.replicate count nameType ++ bound)
      (.apply (LocComm.outputLabel comm.capability) [comm.place, comm.message]) procType :=
    typed _ outputIn
  have messageTyped := (LocComm.output_inv outputTyped).2
  have bodyWell := well.bodies _ inputIn (LocComm.inputLabel comm.capability) comm.place none comm.body rfl
    (LocComm.inputLabel_mem comm.capability)
  have isMsg : isMessage comm.message = true :=
    (well.messages _ outputIn comm.message (by
      simp only [Mettapedia.Languages.ProcessCalculi.Ambient.Decoding.messageOf, LocComm.output]
      rw [if_pos (LocComm.outputLabel_mem comm.capability)])).1
  have nameVar : TypeExpr.base (LocComm.sort comm.capability) = nameType → isVariable comm.message = true := by
    intro isName
    rw [isName] at messageTyped
    rcases Mettapedia.Languages.ProcessCalculi.Ambient.Encoding.name_cases_located messageTyped rfl
      (Mettapedia.Languages.ProcessCalculi.Ambient.Decoding.message_object isMsg) with ⟨_, same, _⟩ | ⟨_, same, _⟩ <;>
      rw [same] <;> rfl
  -- the received body's block
  have receivedTyped : HasType locatedCalc free (List.replicate count nameType ++ bound)
      (instantiateBVar comm.message comm.body) procType :=
    LocComm.result_members comm partsMembers _ (by simp [LocComm.result])
  have groupTyped := (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.decompose_sound (language := locatedCalc)
    (block := locatedBlock) receivedTyped).1
  rw [decomposed] at groupTyped
  obtain ⟨countIs, groupPlaced, groupChildren⟩ := received_block bodyWell isMsg
  rw [decomposed] at countIs groupPlaced groupChildren
  simp only at countIs groupPlaced groupChildren
  rw [← countIs] at groupPlaced groupChildren
  -- the input sits at its place, reached from the root
  have inputAt : placeAt comm.input = some comm.place :=
    placeAt_input (LocComm.inputLabel_mem comm.capability) _ _
  have reached := WellLocated.reached well _ inputIn comm.place inputAt
  have placedOther : ∀ {piece : Pattern} {place' : Pattern}, placeAt piece = some comm.place →
      place' ∉ [comm.place] → placedAt place' piece = false := fun {piece place'} sits notTouched => by
    have different : comm.place ≠ place' := fun same => notTouched (same ▸ List.mem_cons_self)
    simp [placedAt, sits, different]
  have outputAt : placeAt comm.output = some comm.place :=
    placeAt_output (LocComm.outputLabel_mem comm.capability) _ _
  obtain ⟨result, step, equivalent⟩ := path_step_of (redexPlace := comm.place) (touched := [comm.place])
    (home := comm.place) (Step := AmbCommRawStep) (react := commList comm)
    (Holds := fun list => comm.input ∈ list ∧ comm.output ∈ list)
    (extra := 3 * size (instantiateBVar comm.message comm.body) + 6)
    children grows unique markersOf typed groupPlaced groupTyped List.mem_cons_self
    (fun {_} i hi {_} inner => .par i hi inner) (fun name {_ _} inner => .ambient name inner) comm_bag_single_step
    (fun list place' notTouched => by
      rw [commList_filter]
      refine commList_untouched (fun member => ?_) (fun member => ?_)
      · simp [placedOther inputAt notTouched] at member
      · simp [placedOther outputAt notTouched] at member)
    (fun list place' _ => commList_filter comm _ list)
    (fun list members component member => members component (mem_commList member))
    (fun list place' holds notTouched =>
      ⟨List.mem_filter.mpr ⟨holds.1, by simp [placedOther inputAt notTouched]⟩,
        List.mem_filter.mpr ⟨holds.2, by simp [placedOther outputAt notTouched]⟩⟩)
    (fun list holds start reached' x inTouched => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at inTouched
      subst inTouched
      exact reached')
    (fun list holds => ⟨_, holds.1, by simp [placedAt, inputAt]⟩)
    (fun list holds sub fuel' enough' => comm_local children grows typed bodyWell bodyTyped isMsg nameVar decomposed
      groupPlaced groupChildren groupTyped sub holds.1 holds.2 fuel' (by omega))
    reached rfl (List.Sublist.refl _) ⟨inputIn, outputIn⟩ fuel (by omega)
  exact ⟨result, step, equivalent⟩

/-! ## Steps with communication, renamed, restricted, and their variables -/

open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (rename_apply rename_lambda rename_collection rename_instantiate
  freeIn_instantiate)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (FreeIn)
open Mettapedia.Languages.ProcessCalculi.Ambient.Mobile (amb)

/-- **A step with communication renamed is a step with communication.** -/
theorem AmbCommRawStep.rename_step {source target : Pattern} (step : AmbCommRawStep source target) :
    ∀ relabel : Nat → Nat, AmbCommRawStep (rename relabel source) (rename relabel target) := by
  induction step with
  | «open» i hi j hj name process content capability boundary =>
      exact fun relabel => Mettapedia.Languages.ProcessCalculi.Ambient.Comm.AmbNuRawStep.toComm
        (AmbNuRawStep.rename_step (.open i hi j hj name process content capability boundary) relabel)
  | enter i hi j hj name target process host k hk mover capability destination =>
      exact fun relabel => Mettapedia.Languages.ProcessCalculi.Ambient.Comm.AmbNuRawStep.toComm
        (AmbNuRawStep.rename_step (.enter i hi j hj name target process host k hk mover capability destination)
          relabel)
  | exit i hi name parent process k hk mover capability =>
      exact fun relabel => Mettapedia.Languages.ProcessCalculi.Ambient.Comm.AmbNuRawStep.toComm
        (AmbNuRawStep.rename_step (.exit i hi name parent process k hk mover capability) relabel)
  | @comm elements tail input output listed i hi j hj binder body message receiving sending =>
      intro relabel
      rw [rename_collection, rename_collection, List.map_cons, ← List.eraseIdx_map, ← List.eraseIdx_map,
        rename_instantiate]
      refine .comm (tail := tail) listed i (by simpa using hi) j (by simpa [List.eraseIdx_map] using hj) binder
        (rename (Mettapedia.OSLF.MeTTaIL.CanonicalBags.liftIndex 1 relabel) body) (rename relabel message) ?_ ?_
      · rw [List.getElem_map, receiving, rename_apply]
        simp [rename_lambda]
      · rw [List.getElem_of_eq (List.eraseIdx_map _ _ _) (by simpa [List.eraseIdx_map] using hj), List.getElem_map,
          sending, rename_apply]
        rfl
  | @par elements tail i hi target inner recurse =>
      intro relabel
      rw [rename_collection, rename_collection, List.map_cons, ← List.eraseIdx_map]
      exact .par (tail := tail) i (by simpa using hi) (by rw [List.getElem_map]; exact recurse relabel)
  | res binder inner recurse =>
      intro relabel
      simp only [rename_apply, List.map_cons, List.map_nil, rename_lambda]
      exact .res binder (recurse _)
  | ambient name inner recurse =>
      intro relabel
      rw [rename_amb, rename_amb]
      exact .ambient _ (recurse relabel)

/-- **A step with communication uses no variable its source does not.** -/
theorem AmbCommRawStep.freeIn_source {source target : Pattern} (step : AmbCommRawStep source target) :
    ∀ {index : Nat}, FreeIn index target → FreeIn index source := by
  have inBag : ∀ {elements : List Pattern} {tail : Option String} {element : Pattern} {index : Nat},
      element ∈ elements → FreeIn index element → FreeIn index (.collection .hashBag elements tail) :=
    fun member free => .element member free
  have fromBag : ∀ {elements : List Pattern} {tail : Option String} {index : Nat},
      FreeIn index (.collection .hashBag elements tail) → ∃ element ∈ elements, FreeIn index element := fun free =>
    Mettapedia.OSLF.MeTTaIL.CanonicalBags.freeIn_collection.mp free
  have fromAmb : ∀ {name content : Pattern} {index : Nat}, FreeIn index (amb name content) →
      FreeIn index name ∨ FreeIn index content := by
    intro name content index free
    obtain ⟨argument, member, argumentFree⟩ := Mettapedia.OSLF.MeTTaIL.CanonicalBags.freeIn_apply.mp free
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .inl argumentFree
    · exact .inr argumentFree
  have inAmb : ∀ {name content : Pattern} {index : Nat}, (FreeIn index name ∨ FreeIn index content) →
      FreeIn index (amb name content) := by
    intro name content index free
    rcases free with free | free
    · exact .apply (List.mem_cons_self) free
    · exact .apply (List.mem_cons_of_mem _ List.mem_cons_self) free
  induction step with
  | «open» i hi j hj name process content capability boundary =>
      exact AmbNuRawStep.freeIn_source (.open i hi j hj name process content capability boundary)
  | enter i hi j hj name target process host k hk mover capability destination =>
      exact AmbNuRawStep.freeIn_source (.enter i hi j hj name target process host k hk mover capability destination)
  | exit i hi name parent process k hk mover capability =>
      exact AmbNuRawStep.freeIn_source (.exit i hi name parent process k hk mover capability)
  | @comm elements tail input output listed i hi j hj binder body message receiving sending =>
      intro index free
      obtain ⟨element, member, elementFree⟩ := fromBag free
      rcases List.mem_cons.mp member with rfl | inRest
      · rcases freeIn_instantiate elementFree with inBody | inMessage
        · exact inBag (List.getElem_mem hi) (by
            rw [receiving]
            exact .apply List.mem_cons_self (.lambda inBody))
        · exact inBag (List.mem_of_mem_eraseIdx (List.getElem_mem hj)) (by
            rw [sending]
            exact .apply List.mem_cons_self inMessage)
      · exact inBag (List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx inRest)) elementFree
  | @par elements tail i hi target inner recurse =>
      intro index free
      obtain ⟨element, member, elementFree⟩ := fromBag free
      rcases List.mem_cons.mp member with rfl | inRest
      · exact inBag (List.getElem_mem hi) (recurse elementFree)
      · exact inBag (List.mem_of_mem_eraseIdx inRest) elementFree
  | res binder inner recurse =>
      intro index free
      obtain ⟨argument, member, argumentFree⟩ := Mettapedia.OSLF.MeTTaIL.CanonicalBags.freeIn_apply.mp free
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      subst member
      rw [Mettapedia.OSLF.MeTTaIL.CanonicalBags.freeIn_lambda] at argumentFree
      exact .apply List.mem_cons_self (.lambda (recurse argumentFree))
  | ambient name inner recurse =>
      intro index free
      rcases fromAmb free with nameFree | contentFree
      · exact inAmb (.inl nameFree)
      · exact inAmb (.inr (recurse contentFree))

/-- **A step with communication under restrictions** is a step with communication. -/
theorem AmbCommRawStep.restricts_step : ∀ (count : Nat) {source target : Pattern}, AmbCommRawStep source target →
    AmbCommRawStep (Prenex.restricts ambientBlock count source) (Prenex.restricts ambientBlock count target)
  | 0, _, _, step => step
  | count + 1, _, _, step => by
      rw [Prenex.restricts_succ, Prenex.restricts_succ]
      exact .res none (AmbCommRawStep.restricts_step count step)

/-- A bag of nothing does not step. -/
theorem AmbCommRawStep.bag_nil_no_step {tail : Option String} {result : Pattern}
    (step : AmbCommRawStep (.collection .hashBag [] tail) result) : False := by
  cases step with
  | «open» i hi => simp at hi
  | enter i hi => simp at hi
  | comm listed i hi => simp at hi
  | par i hi => simp at hi

/-! ## The step of a presentation, with communication -/

open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (dropIndex rename_comp rename_congr rename_id shiftAbove
  restricts_add)
open Mettapedia.Languages.ProcessCalculi.Ambient.Decoding (decode_unread)
open Mettapedia.Languages.ProcessCalculi.Ambient.Comm (commStep_typed)

/-- **A communication of a well-located block steps the block's presentation**, to a process that, lifted past the
root, is the reacted block read back at the root. -/
theorem present_reacts_comm {count : Nat} {components : List Pattern}
    (well : WellLocated (· = Pattern.bvar 0) (.bvar 0) ⟨count, components⟩)
    (typed : Members locatedCalc locatedBlock free (List.replicate count nameType ++ [nameType]) components)
    {comm : LocComm} {rest : List Pattern} (split : components.Perm (comm.parts ++ rest))
    {owned : Nat} {group : List Pattern}
    (decomposed : decompose locatedBlock (instantiateBVar comm.message comm.body) = ⟨owned, group⟩)
    (fuel : Nat) (enough : 3 * sizeList components + 3 * size (instantiateBVar comm.message comm.body) + 12 ≤ fuel) :
    ∃ contractum, AmbCommRawStep (presentBlock ⟨count, components⟩) contractum ∧
      ProcEquiv ambientCoreCalc ambientBlock free [nameType] (liftBVars 0 1 contractum)
        (Prenex.toPattern ambientBlock (decodeForm (fuel + 1) (.bvar 0)
          ⟨count + owned, (commList comm components).map (liftBVars 0 owned) ++ group⟩)) := by
  set root := liftBVars 0 count (Pattern.bvar 0) with rootIs
  set reacted := commList comm components with reactedIs
  obtain ⟨result, step, equivalent⟩ := root_reacts_comm (bound := [nameType]) well typed split decomposed fuel enough
  -- the presentation, its items at the root read with enough fuel
  have settled : readPlaced (3 * (Prenex.mk count components).mass + 2) root components =
      readPlaced fuel root components :=
    readPlaced_settled root components
      (by simp only [Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Prenex.mass]; omega) (by omega)
  have presentIs : presentBlock ⟨count, components⟩ = rename (dropIndex 0)
      (Prenex.restricts ambientBlock count (padA (Prenex.body ambientBlock (readPlaced fuel root components)))) := by
    unfold presentBlock
    simp only [decodeForm, Prenex.toPattern]
    rw [padA_rename, padA_restricts, settled]
  -- its step: the padded root items step, under the block's restrictions, the root dropped
  have nonempty : readPlaced fuel root components ≠ [] := by
    intro empty
    rw [empty] at step
    exact AmbCommRawStep.bag_nil_no_step step
  obtain ⟨result', bodyStep, related⟩ := body_step_of comm_bag_single_step nonempty step
  have restricted := AmbCommRawStep.restricts_step count bodyStep
  have renamed := AmbCommRawStep.rename_step restricted (dropIndex 0)
  refine ⟨_, by rw [presentIs]; exact renamed, ?_⟩
  -- the contractum does not use the root
  have readIs : Prenex.restricts ambientBlock count (Prenex.body ambientBlock (readPlaced fuel root components)) =
      Prenex.toPattern ambientBlock (decodeForm (fuel + 1) (.bvar 0) ⟨count, components⟩) := by
    simp only [decodeForm, Prenex.toPattern]
    rfl
  have unused : ¬ FreeIn 0 (Prenex.restricts ambientBlock count result') := by
    intro used
    have sourceUsed := AmbCommRawStep.freeIn_source restricted used
    rw [← padA_restricts] at sourceUsed
    have readUsed := freeIn_of_padA _ sourceUsed
    rw [readIs] at readUsed
    exact (decode_unread (fuel + 1)).1 well 0 readUsed rfl
  have liftIs : liftBVars 0 1 (rename (dropIndex 0) (Prenex.restricts ambientBlock count result')) =
      Prenex.restricts ambientBlock count result' := by
    rw [liftBVars_eq_rename, rename_comp]
    conv_rhs => rw [← rename_id (Prenex.restricts ambientBlock count result')]
    refine rename_congr _ fun index used => ?_
    have positive : index ≠ 0 := fun same => unused (same ▸ used)
    simp only [Function.comp, shiftAbove, dropIndex, id]
    split_ifs <;> omega
  rw [liftIs]
  -- the stepped root items, typed
  have readMembers : Members ambientCoreCalc ambientBlock free (List.replicate count nameType ++ [nameType])
      (readPlaced fuel root components) := (decode_typed fuel).2.1 root components typed
  have readObjects : ∀ item ∈ readPlaced fuel root components, isObjectPattern item = true :=
    (decode_object fuel).2.1 root components
  have bodyTyped := body_typed readMembers
  have bodyObject : isObjectPattern (Prenex.body ambientBlock (readPlaced fuel root components)) = true :=
    Mettapedia.GSLT.LanguageDef.RestrictionBlocks.isObject_toPattern (form := ⟨0, readPlaced fuel root components⟩)
      readObjects
  obtain ⟨result'Typed, -⟩ := commStep_typed bodyStep (padA_typed bodyTyped bodyObject) (padA_object _ bodyObject)
  have result'Equivalent : ProcEquiv ambientCoreCalc ambientBlock free (List.replicate count nameType ++ [nameType])
      result' result := by
    rcases related with rfl | isBag
    · exact .refl _
    · rw [isBag]
      exact Relation.EqvGen.symm _ _ (bag_body_equivalent (language := ambientCoreCalc) (block := ambientBlock)
        (Members.cons result'Typed Members.nil))
  have rootLifted : liftBVars 0 owned root = liftBVars 0 (count + owned) (Pattern.bvar 0) := by
    simp [rootIs, liftBVars]
  have targetIs : Prenex.restricts ambientBlock count (Prenex.restricts ambientBlock owned (Prenex.body ambientBlock
      (readPlaced fuel (liftBVars 0 owned root) (reacted.map (liftBVars 0 owned) ++ group)))) =
      Prenex.toPattern ambientBlock (decodeForm (fuel + 1) (.bvar 0)
        ⟨count + owned, reacted.map (liftBVars 0 owned) ++ group⟩) := by
    rw [restricts_add, rootLifted]
    simp only [decodeForm, Prenex.toPattern]
  rw [← targetIs]
  exact .trans _ _ _ (restricts_congr (language := ambientCoreCalc) (block := ambientBlock) count result'Equivalent)
    (restricts_congr (language := ambientCoreCalc) (block := ambientBlock) count equivalent)

/-! ## The block a communication leaves -/

open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (engineBasePremises)
open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationEquiv)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (BlockSignature canonP canonR bag_perm_equivalent bag_fill
  bag_block_equivalent restricts_equation lift_members isObject_liftBVars isObject_toPattern objects_of_decompose
  restrictionsBind_of_typed canonR_complete presentationDepth mem_unfoldings)
open Mettapedia.Languages.ProcessCalculi.Ambient.Located (locatedRepBlock locatedLanguage)
open Mettapedia.Languages.ProcessCalculi.Ambient.Encoding (NameContext)
open Mettapedia.Languages.ProcessCalculi.Ambient.Decoding (Marked insideLoc messageOf EncodeFacts decode_canonForm
  decompose_canonR decode_unfolds rootForm rootForm_facts root_locVariables names_base rename_succ_comp
  insideLoc_locVariables)

theorem commList_sublist (comm : LocComm) (components : List Pattern) :
    (commList comm components).Sublist components :=
  List.erase_sublist.trans List.erase_sublist

/-- **A communication keeps the block's locations**: its input and its output place no ambient. -/
theorem commList_marked (comm : LocComm) (components : List Pattern) (index : Nat) :
    Marked (commList comm components) index ↔ Marked components index := by
  constructor
  · rintro ⟨component, member, isChild⟩
    exact ⟨component, mem_commList member, isChild⟩
  · rintro ⟨component, member, isChild⟩
    have notInput : component ≠ comm.input := fun same => by
      subst same
      simp [childOf, LocComm.input] at isChild
    have notOutput : component ≠ comm.output := fun same => by
      subst same
      simp [childOf, LocComm.output] at isChild
    exact ⟨component, (List.mem_erase_of_ne notOutput).mpr ((List.mem_erase_of_ne notInput).mpr member), isChild⟩

/-- **The block a communication leaves is well-located**: the block without the input and the output, its components
lifted past the received body's restrictions, beside the received body's components. -/
theorem comm_reacted_well {isLoc : Pattern → Prop} {place : Pattern} {bound : List TypeExpr} {count : Nat}
    {components : List Pattern} (well : WellLocated isLoc place ⟨count, components⟩)
    (typed : Members locatedCalc locatedBlock free (List.replicate count nameType ++ bound) components)
    {comm : LocComm} {rest : List Pattern} (split : components.Perm (comm.parts ++ rest))
    {owned : Nat} {group : List Pattern}
    (decomposed : decompose locatedBlock (instantiateBVar comm.message comm.body) = ⟨owned, group⟩) :
    WellLocated isLoc place ⟨count + owned, (commList comm components).map (liftBVars 0 owned) ++ group⟩ := by
  have inputIn : comm.input ∈ components := split.symm.subset (by simp [LocComm.parts])
  have outputIn : comm.output ∈ components := split.symm.subset (by simp [LocComm.parts])
  have reactedWell := WellLocated.sublist_marked well (commList_sublist comm components) (commList_marked comm _)
  -- the received body's block, well-located at the input's place
  have inputTyped : HasType locatedCalc free (List.replicate count nameType ++ bound)
      (.apply (LocComm.inputLabel comm.capability) [comm.place, .lambda none comm.body]) procType :=
    typed _ inputIn
  obtain ⟨-, body', same, bodyTyped⟩ := LocComm.input_inv inputTyped
  simp only [Pattern.lambda.injEq, true_and] at same
  subst same
  have outputTyped : HasType locatedCalc free (List.replicate count nameType ++ bound)
      (.apply (LocComm.outputLabel comm.capability) [comm.place, comm.message]) procType :=
    typed _ outputIn
  have messageTyped := (LocComm.output_inv outputTyped).2
  have bodyWell := well.bodies _ inputIn (LocComm.inputLabel comm.capability) comm.place none comm.body rfl
    (LocComm.inputLabel_mem comm.capability)
  obtain ⟨isMsg, messageApart⟩ := well.messages _ outputIn comm.message (by
    simp only [messageOf, LocComm.output]
    rw [if_pos (LocComm.outputLabel_mem comm.capability)])
  have nameVar : TypeExpr.base (LocComm.sort comm.capability) = nameType → isVariable comm.message = true := by
    intro isName
    rw [isName] at messageTyped
    rcases Mettapedia.Languages.ProcessCalculi.Ambient.Encoding.name_cases_located messageTyped rfl
      (Mettapedia.Languages.ProcessCalculi.Ambient.Decoding.message_object isMsg) with ⟨_, same, _⟩ | ⟨_, same, _⟩ <;>
      rw [same] <;> rfl
  have groupWell := Mettapedia.Languages.ProcessCalculi.Ambient.Decoding.WellLocated.instantiate bodyWell bodyTyped
    isMsg nameVar messageApart (insideLoc_locVariables isLoc count components)
  rw [decomposed] at groupWell
  exact join_well reactedWell (commList_marked comm components) groupWell
    (well.placed _ inputIn comm.place (placeAt_input (LocComm.inputLabel_mem comm.capability) _ _))

/-- **The block a communication leaves is what it leaves beside the rest**: typed, and equivalent in the located
calculus to the received body beside the rest under the block's restrictions. -/
theorem comm_reacted_equivalent {bound : List TypeExpr} {count : Nat} {components : List Pattern}
    (typed : Members locatedCalc locatedBlock free (List.replicate count nameType ++ bound) components)
    {comm : LocComm} {rest : List Pattern} (split : components.Perm (comm.parts ++ rest))
    {owned : Nat} {group : List Pattern}
    (decomposed : decompose locatedBlock (instantiateBVar comm.message comm.body) = ⟨owned, group⟩) :
    Members locatedCalc locatedBlock free (List.replicate (count + owned) nameType ++ bound)
        ((commList comm components).map (liftBVars 0 owned) ++ group) ∧
      EquationEquiv (engineBasePremises RelationEnv.empty) locatedCalc
        (Prenex.restricts locatedBlock count (.collection .hashBag (comm.result ++ rest) none))
        (Prenex.toPattern locatedBlock ⟨count + owned, (commList comm components).map (liftBVars 0 owned) ++ group⟩) := by
  have signature : BlockSignature locatedCalc locatedBlock := locatedLanguage.toBlockSignature
  set reacted := commList comm components with reactedIs
  set inner := List.replicate count nameType ++ bound with innerIs
  -- what the communication leaves, typed
  have partsMembers : Members locatedCalc locatedBlock free inner comm.parts := fun part member =>
    typed part (split.symm.subset (List.mem_append_left _ member))
  have resultMembers := LocComm.result_members comm partsMembers
  have continuationTyped := resultMembers (instantiateBVar comm.message comm.body) (by simp [LocComm.result])
  have reactedMembers : Members locatedCalc locatedBlock free inner reacted := fun element member =>
    typed element (mem_commList member)
  have sound := Mettapedia.GSLT.LanguageDef.RestrictionBlocks.decompose_sound (language := locatedCalc)
    (block := locatedBlock) continuationTyped
  have groupMembers : Members locatedCalc locatedBlock free (List.replicate owned nameType ++ inner) group := by
    have groupSound := sound.1
    rw [decomposed] at groupSound
    exact groupSound
  have continuationEquivalent : ProcEquiv locatedCalc locatedBlock free inner
      (instantiateBVar comm.message comm.body)
      (Prenex.restricts locatedBlock owned (Prenex.body locatedBlock group)) := by
    have equivalentSound := sound.2
    rw [decomposed] at equivalentSound
    exact equivalentSound
  -- the block's components, typed
  have liftedMembers : Members locatedCalc locatedBlock free (List.replicate owned nameType ++ inner)
      (reacted.map (liftBVars 0 owned)) := lift_members owned reactedMembers
  have joinedMembers : Members locatedCalc locatedBlock free (List.replicate owned nameType ++ inner)
      (reacted.map (liftBVars 0 owned) ++ group) := fun element member => by
    rcases List.mem_append.mp member with inLifted | inGroup
    · exact liftedMembers element inLifted
    · exact groupMembers element inGroup
  have contextIs : List.replicate owned nameType ++ inner = List.replicate (count + owned) nameType ++ bound := by
    rw [innerIs, ← List.append_assoc, ← List.replicate_add, Nat.add_comm]
  refine ⟨contextIs ▸ joinedMembers, ?_⟩
  -- what the communication leaves beside the rest is the received body beside the components left
  have leftMembers : Members locatedCalc locatedBlock free inner (comm.result ++ rest) := fun element member => by
    rcases List.mem_append.mp member with inResult | inRest
    · exact resultMembers element inResult
    · exact typed element (split.symm.subset (List.mem_append_right _ inRest))
  have leftPerm : (comm.result ++ rest).Perm (instantiateBVar comm.message comm.body :: reacted) := by
    simp only [LocComm.result, List.cons_append, List.nil_append]
    exact .cons _ (commList_perm split).symm
  have reordered := (bag_perm_equivalent (language := locatedCalc) (block := locatedRepBlock) leftMembers
    leftPerm).toEquationEquiv
  -- the received body, a block of restrictions over a bag
  have continuationBlock : ProcEquiv locatedCalc locatedBlock free inner (instantiateBVar comm.message comm.body)
      (Prenex.restricts locatedBlock owned (.collection .hashBag group none)) :=
    .trans _ _ _ continuationEquivalent
      (restricts_congr (language := locatedCalc) (block := locatedBlock) owned
        (.symm _ _ (bag_body_equivalent groupMembers)))
  have filled := (bag_fill (before := []) (after := reacted) (rest := none) Members.nil reactedMembers
    continuationBlock).toEquationEquiv
  simp only [List.nil_append] at filled
  -- its restrictions leave the bag, and the bag joined is the block's body
  have extruded := bag_block_equivalent groupMembers reactedMembers
  have groupFirst : Members locatedCalc locatedBlock free (List.replicate owned nameType ++ inner)
      (group ++ reacted.map (liftBVars 0 owned)) := fun element member =>
    joinedMembers element (List.perm_append_comm.subset member)
  have toBody := (restricts_congr (language := locatedCalc) (block := locatedBlock) owned
    (.trans _ _ _ (bag_perm_equivalent (language := locatedCalc) (block := locatedRepBlock) groupFirst
      List.perm_append_comm) (bag_body_equivalent joinedMembers))).toEquationEquiv
  have whole := restricts_equation (block := locatedBlock) count
    (.trans _ _ _ reordered (.trans _ _ _ filled (.trans _ _ _ extruded toBody)))
  rw [restricts_add] at whole
  exact whole

/-- **The block a communication leaves reads back as the step's contractum**, lifted past the root: it is
equivalent in the located calculus to the located form of the contractum, so the two have one canonical block, and a
well-located block reads back as its canonical block does. -/
theorem comm_reacted_reads (names : NameContext free) {count : Nat} {components : List Pattern}
    (well : WellLocated (· = Pattern.bvar 0) (.bvar 0) ⟨count, components⟩)
    (typed : Members locatedCalc locatedBlock free (List.replicate count nameType ++ [nameType]) components)
    (objects : ∀ component ∈ components, isObjectPattern component = true)
    {comm : LocComm} {rest : List Pattern} (split : components.Perm (comm.parts ++ rest))
    {owned : Nat} {group : List Pattern}
    (decomposed : decompose locatedBlock (instantiateBVar comm.message comm.body) = ⟨owned, group⟩)
    {located target : Pattern} (locatedTyped : HasType locatedCalc free [nameType] located procType)
    (locatedObject : isObjectPattern located = true)
    (reaches : EquationEquiv (engineBasePremises RelationEnv.empty) locatedCalc
      (Prenex.restricts locatedBlock count (.collection .hashBag (comm.result ++ rest) none)) located)
    (facts : EncodeFacts free (· = .bvar 0) 0 [nameType] (canonP locatedRepBlock located) (rename Nat.succ target)) :
    ∃ least, ∀ fuel, least ≤ fuel → ProcEquiv ambientCoreCalc ambientBlock free [nameType]
      (Prenex.toPattern ambientBlock (decodeForm fuel (.bvar 0)
        ⟨count + owned, (commList comm components).map (liftBVars 0 owned) ++ group⟩))
      (rename Nat.succ target) := by
  have signature : BlockSignature locatedCalc locatedBlock := locatedLanguage.toBlockSignature
  have reactedWell := comm_reacted_well well typed split decomposed
  obtain ⟨members, equivalent⟩ := comm_reacted_equivalent typed split decomposed
  set reacted := commList comm components with reactedIs
  -- the reacted block's components are objects
  have partsObjects : ∀ part ∈ comm.parts, isObjectPattern part = true := fun part member =>
    objects part (split.symm.subset (List.mem_append_left _ member))
  have continuationObject := LocComm.result_objects comm partsObjects (instantiateBVar comm.message comm.body)
    (by simp [LocComm.result])
  have groupObjects : ∀ component ∈ group, isObjectPattern component = true := by
    have inner := objects_of_decompose (block := locatedBlock) continuationObject
    rw [decomposed] at inner
    exact inner
  have blockObjects : ∀ component ∈ reacted.map (liftBVars 0 owned) ++ group,
      isObjectPattern component = true := by
    intro component member
    rcases List.mem_append.mp member with inLifted | inGroup
    · obtain ⟨original, inReacted, rfl⟩ := List.mem_map.mp inLifted
      rw [isObject_liftBVars]
      exact objects _ (mem_commList inReacted)
    · exact groupObjects component inGroup
  -- the reacted block and the contractum's located form have one canonical block
  set reactedBlock : Prenex := ⟨count + owned, reacted.map (liftBVars 0 owned) ++ group⟩ with reactedBlockIs
  have blockTyped : HasType locatedCalc free [nameType] (Prenex.toPattern locatedBlock reactedBlock) procType :=
    restricts_typed (language := locatedCalc) (block := locatedBlock) _ (body_typed members)
  have blockObject : isObjectPattern (Prenex.toPattern locatedBlock reactedBlock) = true :=
    isObject_toPattern blockObjects
  have same := canonR_complete (block := locatedRepBlock) (base := engineBasePremises RelationEnv.empty)
    blockObject locatedObject (restrictionsBind_of_typed (block := locatedRepBlock) _ blockTyped)
    (.trans _ _ _ (.symm _ _ equivalent) reaches)
  have canonSame : canonP locatedRepBlock (Prenex.toPattern locatedBlock reactedBlock) =
      canonP locatedRepBlock located := by
    rw [← decompose_canonR blockTyped blockObject, ← decompose_canonR locatedTyped locatedObject, same]
  -- the reacted block reads back as its canonical block, which reads back as the contractum
  obtain ⟨-, -, least, reads⟩ := decode_canonForm (free := free) reactedBlock reactedWell root_locVariables
    (names_base names 1) members blockObjects
  rw [canonSame] at reads
  obtain ⟨-, -, least', reads'⟩ := facts
  exact ⟨max least least', fun fuel enough =>
    .trans _ _ _ (.symm _ _ (reads fuel (le_of_max_le_left enough))) (reads' fuel (le_of_max_le_right enough))⟩

/-! ## A step with communication matched at a presentation -/

/-- **A step with communication of a closed object process is matched by a step of one of its presentations**,
within three times the ceiling of its root canonical block, to an equivalent contractum. -/
theorem presented_comm (names : NameContext free) {source target : Pattern} (step : AmbCommRawStep source target)
    (typed : HasType ambientCoreCalc free [] source procType) (object : isObjectPattern source = true) :
    ∃ shown ∈ presentationsA (presentationDepth locatedRepBlock 3 (rootForm source)) source,
      ∃ contractum, AmbCommRawStep shown contractum ∧
        ProcEquiv ambientCoreCalc ambientBlock free [] contractum target := by
  obtain ⟨unfolded, unfolds, redex, rest, split, -, members, objects, located, locatedTyped, locatedObject, reaches,
    facts⟩ := root_reaction_comm names (names_base names 1) step typed object
  have rootFacts := rootForm_facts names typed object
  obtain ⟨unfoldedWell, -⟩ := decode_unfolds (names_base names 1) unfolds rootFacts.1 rootFacts.2.1
  have shownIn : presentBlock unfolded ∈
      presentationsA (presentationDepth locatedRepBlock 3 (rootForm source)) source :=
    List.mem_map.mpr ⟨unfolded, (mem_unfoldings _ _ _).mpr unfolds, rfl⟩
  obtain ⟨shownTyped, shownObject, -⟩ := presentation_facts names typed object _ _ shownIn
  obtain ⟨targetTyped, -⟩ := commStep_typed step typed object
  have succIs : rename Nat.succ target = liftBVars 0 1 target := by
    simpa [rename_id] using rename_succ_comp id target
  obtain ⟨count, components⟩ := unfolded
  simp only at members objects split reaches
  cases redex with
  | marker redex =>
      simp only [LocReaction.parts, LocReaction.result] at split reaches
      generalize decomposed : decompose locatedBlock redex.continuationOf = form
      obtain ⟨owned, group⟩ := form
      obtain ⟨least, reads⟩ := reacted_reads names unfoldedWell members objects split decomposed locatedTyped
        locatedObject reaches facts
      obtain ⟨contractum, stepped, lifted⟩ := present_reacts unfoldedWell members split decomposed
        (max (3 * sizeList components + 9) least) (le_max_left _ _)
      have toTarget := Relation.EqvGen.trans _ _ _ lifted
        (reads _ (le_trans (le_max_right _ _) (Nat.le_succ _)))
      rw [succIs] at toTarget
      obtain ⟨contractumTyped, -⟩ := step_typed stepped shownTyped shownObject
      exact ⟨_, shownIn, contractum, Mettapedia.Languages.ProcessCalculi.Ambient.Comm.AmbNuRawStep.toComm stepped,
        unlift_equivalent contractumTyped targetTyped toTarget⟩
  | comm comm =>
      simp only [LocReaction.parts, LocReaction.result] at split reaches
      generalize decomposed : decompose locatedBlock (instantiateBVar comm.message comm.body) = form
      obtain ⟨owned, group⟩ := form
      obtain ⟨least, reads⟩ := comm_reacted_reads names unfoldedWell members objects split decomposed locatedTyped
        locatedObject reaches facts
      obtain ⟨contractum, stepped, lifted⟩ := present_reacts_comm unfoldedWell members split decomposed
        (max (3 * sizeList components + 3 * size (instantiateBVar comm.message comm.body) + 12) least)
        (le_max_left _ _)
      have toTarget := Relation.EqvGen.trans _ _ _ lifted
        (reads _ (le_trans (le_max_right _ _) (Nat.le_succ _)))
      rw [succIs] at toTarget
      obtain ⟨contractumTyped, -⟩ := commStep_typed stepped shownTyped shownObject
      exact ⟨_, shownIn, contractum, stepped, unlift_equivalent contractumTyped targetTyped toTarget⟩

/-! ## Presentations without unused restrictions, with communication -/

open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (mentions_iff isObject_restriction restrict_fill)
open Mettapedia.Languages.ProcessCalculi.Ambient.Comm (coreSignature)

/-- **A step with communication under a restriction is a step of its body.** -/
theorem AmbCommRawStep.res_inv {binder : Option String} {body target : Pattern}
    (step : AmbCommRawStep (.apply "ANu" [.lambda binder body]) target) :
    ∃ inner, target = .apply "ANu" [.lambda none inner] ∧ AmbCommRawStep body inner := by
  generalize sourceIs : Pattern.apply "ANu" [.lambda binder body] = source at step
  cases step with
  | res binder' inner =>
      simp only [Pattern.apply.injEq, List.cons.injEq, Pattern.lambda.injEq, true_and, and_true] at sourceIs
      obtain ⟨-, rfl⟩ := sourceIs
      exact ⟨_, rfl, inner⟩
  | _ => simp [amb] at sourceIs

/-- **Dropping the unused outermost restrictions keeps the steps with communication**: a step of a process is
matched by a step of the process without them, to an equivalent contractum. -/
theorem pruneTop_step_comm (pattern : Pattern) : ∀ {bound : List TypeExpr} {target : Pattern},
    AmbCommRawStep pattern target → HasType ambientCoreCalc free bound pattern procType →
      isObjectPattern pattern = true →
      ∃ target', AmbCommRawStep (pruneTop pattern) target' ∧
        ProcEquiv ambientCoreCalc ambientBlock free bound target' target := by
  induction pattern using pruneTop.induct with
  | case1 binder body used recurse =>
      intro bound target step typed object
      obtain ⟨inner, rfl, innerStep⟩ := AmbCommRawStep.res_inv step
      obtain ⟨bodyTyped, -, rfl⟩ := coreSignature.restriction_typed typed
      rw [isObject_restriction] at object
      obtain ⟨inner', innerStep', innerEquivalent⟩ := recurse innerStep bodyTyped object
      rw [pruneTop, if_pos used]
      exact ⟨_, .res none innerStep', restrict_fill (language := ambientCoreCalc) (block := ambientBlock)
        innerEquivalent⟩
  | case2 binder body unused recurse =>
      intro bound target step typed object
      obtain ⟨inner, rfl, innerStep⟩ := AmbCommRawStep.res_inv step
      obtain ⟨bodyTyped, -, rfl⟩ := coreSignature.restriction_typed typed
      rw [isObject_restriction] at object
      obtain ⟨inner', innerStep', innerEquivalent⟩ := recurse innerStep bodyTyped object
      rw [pruneTop, if_neg unused]
      have notFree : ¬ FreeIn 0 (pruneTop body) := fun free => unused ((mentions_iff _ 0).mpr free)
      have innerUnused : ¬ FreeIn 0 inner' := fun free => notFree (AmbCommRawStep.freeIn_source innerStep' free)
      obtain ⟨prunedTyped, prunedObject, -⟩ := pruneTop_facts body bodyTyped object
      obtain ⟨inner'Typed, -⟩ := commStep_typed innerStep' prunedTyped prunedObject
      obtain ⟨-, dropped⟩ := garbage_dropped inner'Typed innerUnused
      exact ⟨_, AmbCommRawStep.rename_step innerStep' (dropIndex 0),
        .trans _ _ _ (.symm _ _ dropped) (restrict_fill (language := ambientCoreCalc) (block := ambientBlock)
          innerEquivalent)⟩
  | case3 other notRestriction =>
      intro bound target step typed object
      refine ⟨target, ?_, .refl _⟩
      rw [pruneTop.eq_def]
      split
      · rename_i binder body
        exact absurd rfl (notRestriction binder body)
      · exact step

/-- **A step with communication of a closed object process is matched by a step of one of its presentations, without
their unused outermost restrictions**, to an equivalent contractum. -/
theorem presented_pruned_comm (names : NameContext free) {source target : Pattern}
    (step : AmbCommRawStep source target) (typed : HasType ambientCoreCalc free [] source procType)
    (object : isObjectPattern source = true) :
    ∃ shown ∈ (presentationsA (presentationDepth locatedRepBlock 3 (rootForm source)) source).map pruneTop,
      ∃ contractum, AmbCommRawStep shown contractum ∧
        ProcEquiv ambientCoreCalc ambientBlock free [] contractum target := by
  obtain ⟨shown, shownIn, contractum, stepped, equivalent⟩ := presented_comm names step typed object
  obtain ⟨shownTyped, shownObject, -⟩ := presentation_facts names typed object _ shown shownIn
  obtain ⟨contractum', stepped', equivalent'⟩ := pruneTop_step_comm shown stepped shownTyped shownObject
  exact ⟨pruneTop shown, List.mem_map_of_mem shownIn, contractum', stepped', .trans _ _ _ equivalent' equivalent⟩

end Mettapedia.Languages.ProcessCalculi.Ambient.Steps
