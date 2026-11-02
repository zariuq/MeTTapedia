import Mettapedia.Languages.ProcessCalculi.Ambient.DecodingMolecules
import Mettapedia.Languages.ProcessCalculi.Ambient.EncodingSteps

/-!
# The located canonical form reads back as the process

The canonical block of an ambient process's located form, read back at the process's location, is the process with
its free variables renamed as the located form renames them (`decode_encode_sorted`, in a context of names and
capabilities; `decode_encode`, in one of names), and is well-located there. The proof follows the process: inaction
reads as inaction; a restriction closes its body's block, which reads as the restriction of its reading; an ambient
closes a marker beside its content's block, read as the ambient around the content's reading, its location garbage; a
capability and a prefix by a capability term are one component, its continuation read at its place; an input is one
component, its body read at its place under its binder; an output is one component; a replication is its replicated
molecules (`decode_replicatedOf`); a bag joins its members' blocks side by side. Every block normalized on the way
reads back as before normalizing (`decode_normal`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Decoding

open Mettapedia.Languages.ProcessCalculi.Ambient.Comm (ambientCoreCalc coreSignature commTerms capRule capType)

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (FreeIn liftIndex)
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (Prenex Members ProcEquiv rename canonP canonR canonicalOf normal
  decompose canonP_atomCase canonP_restrict canonP_bag canonP_unit objectArgument BaseContext)
open Mettapedia.Languages.ProcessCalculi.Ambient.Full (ambientBlock ambientRepBlock)
open Mettapedia.Languages.ProcessCalculi.Ambient.Located (locatedCalc locatedBlock locatedRepBlock)
open Mettapedia.Languages.ProcessCalculi.Ambient.Encoding (nameType procType encode shiftName LocatedFrame)

variable {free : FreeTypeContext}

/-- **The empty block is well-located** at any location. -/
theorem WellLocated.nil {isLoc : Pattern → Prop} {place : Pattern} (placeLoc : isLoc place) :
    WellLocated isLoc place Prenex.nil :=
  .intro placeLoc (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) ⟨id, by simp⟩ (by simp)
    (by simp) (by simp)

theorem canonP_variable {pattern : Pattern} (isVar : isVariable pattern = true) :
    canonP locatedRepBlock pattern = Prenex.atom pattern := by
  cases pattern <;> simp_all [isVariable, canonP]

/-- **A located component of three arguments is its own canonical block**: its first two arguments are variables,
its third read canonically. -/
theorem canonP_triple {label : String} (notRestrict : label ≠ "LNu") {first second third : Pattern}
    (firstVar : isVariable first = true) (secondVar : isVariable second = true)
    (thirdObject : isObjectPattern third = true) :
    canonP locatedRepBlock (.apply label [first, second, third]) =
      Prenex.atom (.apply label [first, second, Prenex.toPattern locatedBlock (canonP locatedRepBlock third)]) := by
  have objects : ∀ argument ∈ [first, second, third], isObjectPattern argument = true := by
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · cases argument <;> simp_all [isVariable, isObjectPattern]
    · cases argument <;> simp_all [isVariable, isObjectPattern]
    · exact thirdObject
  rw [canonP_atomCase (block := locatedRepBlock) objects notRestrict (by simp) (by simp) (by simp)]
  simp [objectArgument, canonP_variable firstVar, canonP_variable secondVar, Prenex.atom, Prenex.toPattern,
    Prenex.restricts, Prenex.body]

/-- **A message is an object.** -/
theorem message_object : ∀ {message : Pattern}, isMessage message = true → isObjectPattern message = true
  | .bvar _, _ => rfl
  | .fvar _, _ => rfl
  | .apply _ [], _ => rfl
  | .apply _ [name], isMsg => by
      simp only [isMessage, Bool.and_eq_true] at isMsg
      cases name <;> simp_all [isVariable, isObjectPattern, isObjectPatternList]
  | .apply _ [first, second], isMsg => by
      simp only [isMessage, Bool.and_eq_true] at isMsg
      simp [isObjectPattern, isObjectPatternList, message_object isMsg.1.2, message_object isMsg.2]
  | .apply _ (_ :: _ :: _ :: _), isMsg => by simp [isMessage] at isMsg
  | .lambda _ _, isMsg => by simp [isMessage] at isMsg
  | .multiLambda _ _ _, isMsg => by simp [isMessage] at isMsg
  | .subst _ _, isMsg => by simp [isMessage] at isMsg
  | .collection _ _ _, isMsg => by simp [isMessage] at isMsg

/-- **A message is its own canonical block.** -/
theorem canonP_message : ∀ {message : Pattern}, isMessage message = true →
    canonP locatedRepBlock message = Prenex.atom message
  | .bvar _, _ => canonP_variable rfl
  | .fvar _, _ => canonP_variable rfl
  | .apply label [], isMsg => by
      simp only [isMessage, beq_iff_eq] at isMsg
      subst isMsg
      simp [canonP]
  | .apply label [name], isMsg => by
      have object := message_object isMsg
      simp only [isMessage, Bool.and_eq_true, decide_eq_true_eq] at isMsg
      obtain ⟨listed, nameVar⟩ := isMsg
      have objects : ∀ argument ∈ [name], isObjectPattern argument = true := by
        simpa [isObjectPattern, isObjectPatternList] using object
      simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
      rw [canonP_atomCase (block := locatedRepBlock) objects (by rcases listed with rfl | rfl | rfl <;> decide)
        (by simp) (by rcases listed with rfl | rfl | rfl <;> simp) (by simp)]
      simp [objectArgument, canonP_variable nameVar, Prenex.atom, Prenex.toPattern, Prenex.restricts, Prenex.body]
  | .apply label [first, second], isMsg => by
      have object := message_object isMsg
      simp only [isMessage, Bool.and_eq_true, beq_iff_eq] at isMsg
      obtain ⟨⟨rfl, firstMsg⟩, secondMsg⟩ := isMsg
      have objects : ∀ argument ∈ [first, second], isObjectPattern argument = true := by
        simpa [isObjectPattern, isObjectPatternList] using object
      rw [canonP_atomCase (block := locatedRepBlock) objects (by decide) (by simp) (by simp) (by simp)]
      simp [objectArgument, canonP_message firstMsg, canonP_message secondMsg, Prenex.atom, Prenex.toPattern,
        Prenex.restricts, Prenex.body]
  | .apply _ (_ :: _ :: _ :: _), isMsg => by simp [isMessage] at isMsg
  | .lambda _ _, isMsg => by simp [isMessage] at isMsg
  | .multiLambda _ _ _, isMsg => by simp [isMessage] at isMsg
  | .subst _ _, isMsg => by simp [isMessage] at isMsg
  | .collection _ _ _, isMsg => by simp [isMessage] at isMsg

/-- **A located prefix by a capability term is its own canonical block**: its place a variable, its message its
own, its continuation read canonically. -/
theorem canonP_cap {first message third : Pattern} (firstVar : isVariable first = true)
    (messageIs : isMessage message = true) (thirdObject : isObjectPattern third = true) :
    canonP locatedRepBlock (.apply "LCap" [first, message, third]) =
      Prenex.atom (.apply "LCap" [first, message, Prenex.toPattern locatedBlock (canonP locatedRepBlock third)]) := by
  have objects : ∀ argument ∈ [first, message, third], isObjectPattern argument = true := by
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · cases argument <;> simp_all [isVariable, isObjectPattern]
    · exact message_object messageIs
    · exact thirdObject
  rw [canonP_atomCase (block := locatedRepBlock) objects (by decide) (by simp) (by simp) (by simp)]
  simp [objectArgument, canonP_variable firstVar, canonP_message messageIs, Prenex.atom, Prenex.toPattern,
    Prenex.restricts, Prenex.body]

/-- **A located input is its own canonical block**: its place a variable, its body read canonically. -/
theorem canonP_input {label : String} (listed : label ∈ inputs) {first body : Pattern} {binder : Option String}
    (firstVar : isVariable first = true) (bodyObject : isObjectPattern body = true) :
    canonP locatedRepBlock (.apply label [first, .lambda binder body]) =
      Prenex.atom (.apply label [first, .lambda binder (Prenex.toPattern locatedBlock (canonP locatedRepBlock body))]) := by
  have objects : ∀ argument ∈ [first, .lambda binder body], isObjectPattern argument = true := by
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · cases argument <;> simp_all [isVariable, isObjectPattern]
    · simpa [isObjectPattern] using bodyObject
  simp only [inputs, List.mem_cons, List.not_mem_nil, or_false] at listed
  rw [canonP_atomCase (block := locatedRepBlock) objects (by rcases listed with rfl | rfl <;> decide) (by simp)
    (by simp) (by simp)]
  simp [objectArgument, canonP_variable firstVar, Mettapedia.GSLT.LanguageDef.RestrictionBlocks.canonP_lambda,
    Prenex.atom, Prenex.toPattern, Prenex.restricts, Prenex.body]

/-- **A located output is its own canonical block.** -/
theorem canonP_output {label : String} (listed : label ∈ outputs) {first message : Pattern}
    (firstVar : isVariable first = true) (messageIs : isMessage message = true) :
    canonP locatedRepBlock (.apply label [first, message]) = Prenex.atom (.apply label [first, message]) := by
  have objects : ∀ argument ∈ [first, message], isObjectPattern argument = true := by
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · cases argument <;> simp_all [isVariable, isObjectPattern]
    · exact message_object messageIs
  simp only [outputs, List.mem_cons, List.not_mem_nil, or_false] at listed
  rw [canonP_atomCase (block := locatedRepBlock) objects (by rcases listed with rfl | rfl <;> decide) (by simp)
    (by simp) (by simp)]
  simp [objectArgument, canonP_variable firstVar, canonP_message messageIs, Prenex.atom, Prenex.toPattern,
    Prenex.restricts, Prenex.body]

/-! ## What a located canonical form keeps -/

open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (normal_sound par_members par_equivalent bag_cons_equivalent
  bag_body_equivalent body_congr body_typed restricts_typed)

/-- **What the located canonical form of a process keeps**: the block is well-located at the location, typed, and
reads back as the expected process. -/
def EncodeFacts (free : FreeTypeContext) (isLoc : Pattern → Prop) (here : Nat) (bound : List TypeExpr)
    (form : Prenex) (reading : Pattern) : Prop :=
  WellLocated isLoc (.bvar here) form ∧
    Members locatedCalc locatedBlock free (List.replicate form.count nameType ++ bound) form.components ∧
    ∃ least, ∀ fuel, least ≤ fuel → ProcEquiv ambientCoreCalc ambientBlock free bound
      (Prenex.toPattern ambientBlock (decodeForm fuel (.bvar here) form)) reading

/-- A context of names and capabilities is a context of base sorts. -/
theorem sorted_base (names : Mettapedia.Languages.ProcessCalculi.Ambient.Encoding.NameContext free)
    {bound : List TypeExpr} (sorted : ∀ type ∈ bound, type = nameType ∨ type = capType) : BaseContext free bound :=
  ⟨fun name type found => ⟨"Name", names.free name type found⟩, fun type member => by
    rcases sorted type member with rfl | rfl
    · exact ⟨"Name", rfl⟩
    · exact ⟨"Cap", rfl⟩⟩

theorem names_base (names : Mettapedia.Languages.ProcessCalculi.Ambient.Encoding.NameContext free) (count : Nat) :
    BaseContext free (List.replicate count nameType) :=
  sorted_base names fun _ member => .inl (List.eq_of_mem_replicate member)

namespace EncodeFacts

variable {isLoc : Pattern → Prop} {here : Nat} {bound : List TypeExpr} {form : Prenex} {reading : Pattern}

/-- An equivalent reading. -/
theorem congr (facts : EncodeFacts free isLoc here bound form reading) {other : Pattern}
    (equivalent : ProcEquiv ambientCoreCalc ambientBlock free bound reading other) :
    EncodeFacts free isLoc here bound form other := by
  obtain ⟨well, members, least, reads⟩ := facts
  exact ⟨well, members, least, fun fuel enough => .trans _ _ _ (reads fuel enough) equivalent⟩

/-- **Normalizing keeps what a block keeps.** -/
theorem normal (facts : EncodeFacts free isLoc here bound form reading) (context : BaseContext free bound)
    (locVariables : LocVariables isLoc) :
    EncodeFacts free isLoc here bound (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.normal locatedRepBlock form)
      reading := by
  obtain ⟨well, members, least, reads⟩ := facts
  obtain ⟨normalWell, normalReads⟩ := decode_normal form well locVariables context members
  refine ⟨normalWell, (normal_sound (language := locatedCalc) (block := locatedRepBlock) context members).1,
    least + 3 * form.mass + 3 * (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.normal locatedRepBlock form).mass + 3,
    fun fuel enough => ?_⟩
  exact .trans _ _ _ (normalReads fuel (by omega) (by omega)) (reads fuel (by omega))

end EncodeFacts

/-- **Inaction reads back as inaction.** -/
theorem encodeFacts_zero {isLoc : Pattern → Prop} {here : Nat} {bound : List TypeExpr} (hereLoc : isLoc (.bvar here)) :
    EncodeFacts free isLoc here bound Prenex.nil (.apply "AZero" []) := by
  refine ⟨WellLocated.nil hereLoc, fun _ member => by simp [Prenex.nil] at member, 1, fun fuel enough => ?_⟩
  obtain ⟨step, rfl⟩ : ∃ step, fuel = step + 1 := ⟨fuel - 1, by omega⟩
  have empty : readPlaced step (liftBVars 0 0 (.bvar here)) [] = [] := by cases step <;> rfl
  simp only [decodeForm, Prenex.nil, empty, Prenex.toPattern, Prenex.restricts, Prenex.body]
  exact .refl _

/-- **Blocks side by side read back as their readings side by side.** -/
theorem encodeFacts_par {isLoc : Pattern → Prop} {here : Nat} {bound : List TypeExpr} {first second : Prenex}
    {firstReading secondReading : Pattern}
    (firstFacts : EncodeFacts free isLoc here bound first firstReading)
    (secondFacts : EncodeFacts free isLoc here bound second secondReading) :
    EncodeFacts free isLoc here bound (first.par second)
      (.collection .hashBag [firstReading, secondReading] none) := by
  obtain ⟨firstWell, firstMembers, firstLeast, firstReads⟩ := firstFacts
  obtain ⟨secondWell, secondMembers, secondLeast, secondReads⟩ := secondFacts
  refine ⟨firstWell.par secondWell, par_members (language := locatedCalc) (block := locatedBlock) firstMembers
    secondMembers, firstLeast + secondLeast + 1, fun fuel enough => ?_⟩
  obtain ⟨step, rfl⟩ : ∃ step, fuel = step + 1 := ⟨fuel - 1, by omega⟩
  rw [decodeForm_par step (.bvar here) firstWell.rooted secondWell.rooted]
  have firstDecoded := (decode_typed (free := free) (step + 1)).1 (.bvar here) first firstMembers
  have secondDecoded := (decode_typed (free := free) (step + 1)).1 (.bvar here) second secondMembers
  refine .trans _ _ _ (Relation.EqvGen.symm _ _ (par_equivalent (language := ambientCoreCalc) (block := ambientBlock)
    firstDecoded secondDecoded)) ?_
  have pairMembers : Members ambientCoreCalc ambientBlock free bound
      [Prenex.toPattern ambientBlock (decodeForm (step + 1) (.bvar here) first),
        Prenex.toPattern ambientBlock (decodeForm (step + 1) (.bvar here) second)] :=
    Members.cons (restricts_typed (language := ambientCoreCalc) (block := ambientBlock) _ (body_typed firstDecoded))
      (Members.cons (restricts_typed (language := ambientCoreCalc) (block := ambientBlock) _ (body_typed secondDecoded))
        Members.nil)
  exact body_congr pairMembers (.cons (firstReads _ (by omega)) (.cons (secondReads _ (by omega)) .nil))

/-- **A bag's members' blocks side by side read back as the bag of their readings.** -/
theorem encodeFacts_bag {isLoc : Pattern → Prop} {here : Nat} {bound : List TypeExpr} (hereLoc : isLoc (.bvar here))
    {block : Pattern → Prenex} {reading : Pattern → Pattern} :
    ∀ (elements : List Pattern), (∀ element ∈ elements, EncodeFacts free isLoc here bound (block element)
        (reading element)) →
      (∀ element ∈ elements, HasType ambientCoreCalc free bound (reading element) procType) →
      EncodeFacts free isLoc here bound ((elements.map block).foldr Prenex.par Prenex.nil)
        (.collection .hashBag (elements.map reading) none)
  | [], _, _ => (encodeFacts_zero hereLoc).congr
      (Relation.EqvGen.symm _ _ (bag_body_equivalent (language := ambientCoreCalc) (block := ambientBlock) Members.nil))
  | element :: rest, facts, typed => by
      have restFacts := encodeFacts_bag hereLoc rest (fun other member => facts other (List.mem_cons_of_mem _ member))
        (fun other member => typed other (List.mem_cons_of_mem _ member))
      have restMembers : Members ambientCoreCalc ambientBlock free bound (rest.map reading) := by
        intro other member
        obtain ⟨original, inRest, rfl⟩ := List.mem_map.mp member
        exact typed original (List.mem_cons_of_mem _ inRest)
      simp only [List.map_cons, List.foldr_cons]
      exact (encodeFacts_par (facts element List.mem_cons_self) restFacts).congr
        (bag_cons_equivalent (language := ambientCoreCalc) (block := ambientBlock) (typed element List.mem_cons_self)
          restMembers)

/-! ## Restrictions, ambients, capabilities, replications -/

open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (close_sound restrict_fill garbage_equivalent lift_typed rename_bvar
  replicatedOf replicate_fill replicate_typed)
open Mettapedia.Languages.ProcessCalculi.Ambient.Full (amb_typed amb_fill prefix_fill acap_fill input_fill)
open Mettapedia.Languages.ProcessCalculi.Ambient.Encoding (marker_typed markerOf_typed capability_typed lcap_typed
  linput_typed loutput_typed)

theorem shiftName_bvar (here : Nat) : shiftName (.bvar here) = .bvar (here + 1) := by
  simp [shiftName, rename_bvar]

/-- **A restriction closes its body's block, which reads back as the restriction of the body's reading.** -/
theorem encodeFacts_close {isLoc : Pattern → Prop} {here : Nat} {bound : List TypeExpr} {inner : Prenex}
    {reading : Pattern} (facts : EncodeFacts free (underName isLoc) (here + 1) (nameType :: bound) inner reading) :
    EncodeFacts free isLoc here bound inner.close (.apply "ANu" [.lambda none reading]) := by
  have signature : Mettapedia.GSLT.LanguageDef.RestrictionBlocks.BlockSignature locatedCalc locatedBlock :=
    Mettapedia.Languages.ProcessCalculi.Ambient.Located.locatedLanguage.toBlockSignature
  obtain ⟨innerWell, innerMembers, least, reads⟩ := facts
  have closeWell : WellLocated isLoc (.bvar here) inner.close :=
    WellLocated.close_name (by rw [shiftName_bvar]; exact innerWell)
  have membersAround : Members locatedCalc locatedBlock free
      (List.replicate inner.count nameType ++ (nameType :: bound)) inner.components := innerMembers
  obtain ⟨closeMembers, -⟩ := close_sound (language := locatedCalc) (block := locatedBlock) membersAround
  refine ⟨closeWell, closeMembers, least + 1, fun fuel enough => ?_⟩
  obtain ⟨step, rfl⟩ : ∃ step, fuel = step + 1 := ⟨fuel - 1, by omega⟩
  refine .trans _ _ _ (decode_close step (.bvar here) inner membersAround) ?_
  rw [shiftName_bvar]
  exact restrict_fill (language := ambientCoreCalc) (block := ambientBlock) (reads (step + 1) (by omega))

/-- **An ambient's located form reads back as the ambient**: the marker beside its content's block under the location
reads as the ambient around the content's reading, or as that reading in place for an opened marker, and the location
is garbage. -/
theorem encodeFacts_marker {isLoc : Pattern → Prop} {here : Nat} {bound : List TypeExpr} {inner : Prenex}
    {label : String} (isMarker : label ∈ markers) {name content : Pattern} (hereLoc : isLoc (.bvar here))
    (hereTyped : bound[here]? = some nameType) (nameVar : isVariable name = true)
    (nameApart : ¬ underLocation isLoc (liftBVars 0 1 name))
    (nameTyped : HasType locatedCalc free bound name nameType)
    (contentTyped : HasType ambientCoreCalc free bound content procType)
    (facts : EncodeFacts free (underLocation isLoc) 0 (nameType :: bound) inner (liftBVars 0 1 content)) :
    EncodeFacts free isLoc here bound
      ((Prenex.atom (.apply label [shiftName (.bvar here), .bvar 0, liftBVars 0 1 name])).par inner).close
      (wrapContent label name content) := by
  have signature : Mettapedia.GSLT.LanguageDef.RestrictionBlocks.BlockSignature locatedCalc locatedBlock :=
    Mettapedia.Languages.ProcessCalculi.Ambient.Located.locatedLanguage.toBlockSignature
  obtain ⟨innerWell, innerMembers, least, reads⟩ := facts
  have liftedVar : isVariable (liftBVars 0 1 name) = true := by rw [isVariable_lift]; exact nameVar
  have closeWell := WellLocated.close_marker isMarker hereLoc liftedVar nameApart innerWell
  have liftedNameTyped : HasType locatedCalc free (nameType :: bound) (liftBVars 0 1 name) nameType := by
    simpa using lift_typed (language := locatedCalc) (inner := []) (inserted := [nameType]) (outer := bound) nameTyped
  have ambientName : HasType ambientCoreCalc free bound name nameType :=
    variable_typed nameTyped nameVar
  have ambientLiftedName : HasType ambientCoreCalc free (nameType :: bound) (liftBVars 0 1 name)
      nameType := variable_typed liftedNameTyped liftedVar
  have markerTyped : HasType locatedCalc free (nameType :: bound)
      (.apply label [shiftName (.bvar here), .bvar 0, liftBVars 0 1 name]) procType := by
    rw [shiftName_bvar]
    exact markerOf_typed isMarker (.bvar (by simpa using hereTyped)) (.bvar (by simp)) liftedNameTyped
  have atomMembers : Members locatedCalc locatedBlock free
      (List.replicate (Prenex.atom (.apply label [shiftName (.bvar here), .bvar 0, liftBVars 0 1 name])).count
        nameType ++ (nameType :: bound))
      (Prenex.atom (.apply label [shiftName (.bvar here), .bvar 0, liftBVars 0 1 name])).components := by
    intro element member
    simp only [Prenex.atom, List.mem_singleton] at member
    subst member
    simpa [Prenex.atom] using markerTyped
  have membersAround := par_members (language := locatedCalc) (block := locatedBlock) atomMembers innerMembers
  obtain ⟨closeMembers, -⟩ := close_sound (language := locatedCalc) (block := locatedBlock) membersAround
  refine ⟨closeWell, closeMembers, least + 4, fun fuel enough => ?_⟩
  obtain ⟨step, rfl⟩ : ∃ step, fuel = step + 4 := ⟨fuel - 4, by omega⟩
  refine .trans _ _ _ (decode_close (step + 3) (.bvar here) _ membersAround) ?_
  rw [decode_marker isMarker (step + 1) (.bvar here) (liftBVars 0 1 name) liftedVar innerWell.rooted]
  -- the ambient around its content's reading, under the content's restrictions
  have contentDecoded := (decode_typed (free := free) (step + 2)).1 (.bvar 0) inner innerMembers
  have contentBody : HasType ambientCoreCalc free (List.replicate inner.count nameType ++ (nameType :: bound))
      (Prenex.body ambientBlock (readPlaced (step + 1) (.bvar inner.count) inner.components)) procType := by
    have := body_typed contentDecoded
    simpa [decodeForm, liftBVars] using this
  have aroundAmbient := restricts_wrapContent_equivalent (free := free) label inner.count ambientLiftedName contentBody
  have contentIs : Prenex.restricts ambientBlock inner.count
      (Prenex.body ambientBlock (readPlaced (step + 1) (.bvar inner.count) inner.components)) =
      Prenex.toPattern ambientBlock (decodeForm (step + 2) (.bvar 0) inner) := by
    simp [decodeForm, Prenex.toPattern, liftBVars]
  rw [contentIs] at aroundAmbient
  have filled := wrapContent_fill label ambientLiftedName (reads (step + 2) (by omega))
  have liftedAmbient : wrapContent label (liftBVars 0 1 name) (liftBVars 0 1 content) =
      liftBVars 0 1 (wrapContent label name content) := by
    simp only [Mettapedia.GSLT.LanguageDef.RestrictionBlocks.liftBVars_eq_rename, wrapContent_rename]
  rw [liftedAmbient] at filled
  have inside : ProcEquiv ambientCoreCalc ambientBlock free (nameType :: bound)
      (Prenex.toPattern ambientBlock ⟨inner.count, [wrapContent label (liftBVars 0 inner.count (liftBVars 0 1 name))
        (Prenex.body ambientBlock (readPlaced (step + 1) (.bvar inner.count) inner.components))]⟩)
      (liftBVars 0 1 (wrapContent label name content)) :=
    .trans _ _ _ aroundAmbient filled
  exact .trans _ _ _ (restrict_fill (language := ambientCoreCalc) (block := ambientBlock) inside)
    (garbage_equivalent (language := ambientCoreCalc) (block := ambientBlock)
      (wrapContent_typed label ambientName contentTyped))

/-- **A capability's located form is one component, its continuation read canonically at its place**, which reads
back as the capability on the continuation's reading. -/
theorem encodeFacts_capability {isLoc : Pattern → Prop} {here : Nat} {bound : List TypeExpr} {label : String}
    (listed : label ∈ capabilities) {inner : Prenex} {name reading : Pattern}
    (locVariables : LocVariables isLoc) (hereLoc : isLoc (.bvar here)) (hereTyped : bound[here]? = some nameType)
    (nameVar : isVariable name = true) (nameApart : ¬ isLoc name)
    (nameTyped : HasType locatedCalc free bound name nameType)
    (decomposed : decompose locatedBlock (Prenex.toPattern locatedBlock inner) = inner)
    (facts : EncodeFacts free isLoc here bound inner reading) :
    EncodeFacts free isLoc here bound
      (Prenex.atom (.apply label [.bvar here, name, Prenex.toPattern locatedBlock inner]))
      (.apply (ambientCapability label) [name, reading]) := by
  have signature : Mettapedia.GSLT.LanguageDef.RestrictionBlocks.BlockSignature locatedCalc locatedBlock :=
    Mettapedia.Languages.ProcessCalculi.Ambient.Located.locatedLanguage.toBlockSignature
  obtain ⟨innerWell, innerMembers, least, reads⟩ := facts
  have notMarker := not_marker_of_capability listed
  have notRep : label ≠ "LRep" := by rintro rfl; simp at listed
  set component : Pattern := .apply label [.bvar here, name, Prenex.toPattern locatedBlock inner] with componentIs
  have componentPlace : placeAt component = some (.bvar here) := placeAt_capability listed _ _ _
  have insideIs : ∀ pattern, insideLoc isLoc 0 [component] pattern → isLoc pattern := by
    intro pattern inside
    cases pattern with
    | bvar index => simpa [insideLoc] using inside
    | fvar name => simpa [insideLoc] using inside
    | _ => simp [insideLoc] at inside
  have hereInside : insideLoc isLoc 0 [component] (.bvar here) := by simpa [insideLoc] using hereLoc
  have continuationTyped : HasType locatedCalc free bound (Prenex.toPattern locatedBlock inner) procType :=
    restricts_typed (language := locatedCalc) (block := locatedBlock) _ (body_typed innerMembers)
  have componentTyped : HasType locatedCalc free bound component procType :=
    capability_typed listed (.bvar hereTyped) nameTyped continuationTyped
  have notCap : label ≠ "LCap" := by rintro rfl; simp at listed
  refine ⟨.intro hereLoc ?_ ?_ ?_ ?_ ?_ ?_ ?_ ⟨id, ?_⟩ ?_ ?_ ?_, ?_, least + 3, fun fuel enough => ?_⟩
  · intro other member
    simp only [List.mem_singleton] at member
    subst member
    exact .capability listed
  · intro other member at' isPlaced
    simp only [List.mem_singleton] at member
    subst member
    rw [componentPlace, Option.some.injEq] at isPlaced
    exact .inl (by rw [← isPlaced]; simp [liftBVars])
  · intro index
    exact (List.length_filter_le _ _).trans (by simp)
  · intro other member found isName
    simp only [List.mem_singleton] at member
    subst member
    simp only [componentIs, nameOf, if_neg notMarker, if_pos listed, Option.some.injEq] at isName
    subst isName
    exact ⟨nameVar, fun inside => nameApart (insideIs _ inside)⟩
  · intro other member label' at' name' continuation isCap listed'
    simp only [List.mem_singleton] at member
    subst member
    simp only [componentIs, Pattern.apply.injEq, List.cons.injEq, and_true] at isCap
    obtain ⟨rfl, rfl, rfl, rfl⟩ := isCap
    rw [decomposed]
    exact innerWell.mono locVariables insideIs hereInside
  · intro other member argument at' isRep
    simp only [List.mem_singleton] at member
    subst member
    simp [componentIs] at isRep
  · intro other member argument isRep
    simp only [List.mem_singleton] at member
    subst member
    simp [componentIs] at isRep
  · intro other member index child below childBelow isPlaced isChild
    simp only [List.mem_singleton] at member
    subst member
    simp [componentIs, childOf, notMarker] at isChild
  · intro other member message isMsgOf
    simp only [List.mem_singleton] at member
    subst member
    simp [componentIs, messageOf, notCap] at isMsgOf
  · intro other member at' message continuation isCapComponent
    simp only [List.mem_singleton] at member
    subst member
    simp only [componentIs, Pattern.apply.injEq] at isCapComponent
    exact absurd isCapComponent.1 notCap
  · intro other member label' at' binder body isInput listed'
    simp only [List.mem_singleton] at member
    subst member
    simp [componentIs] at isInput
  · intro other member
    simp only [Prenex.atom, List.mem_singleton] at member
    subst member
    simpa [Prenex.atom] using componentTyped
  · obtain ⟨step, rfl⟩ : ∃ step, fuel = step + 3 := ⟨fuel - 3, by omega⟩
    have placedHere : placedAt (.bvar here) component = true := by simp [placedAt, componentPlace]
    have lifted : liftBVars 0 0 (Pattern.bvar here) = .bvar here := by simp [liftBVars]
    have read : Prenex.toPattern ambientBlock (decodeForm (step + 3) (.bvar here) (Prenex.atom component)) =
        .apply (ambientCapability label) [name, Prenex.toPattern ambientBlock (decodeForm step (.bvar here) inner)] := by
      simp only [decodeForm, Prenex.atom, readPlaced_succ, lifted, List.filter_cons, placedHere, Bool.not_true,
        Bool.false_eq_true, if_true, if_false, List.filter_nil, List.map_cons, List.map_nil, Prenex.toPattern,
        Prenex.restricts, Prenex.body]
      simp only [readComponent, componentIs, if_neg notMarker, if_pos listed, if_pos nameVar, decomposed]
      simp only [Prenex.toPattern, Prenex.body]
    rw [read]
    exact prefix_fill (ambientCapability_mem listed) (variable_typed nameTyped nameVar) (reads step (by omega))

/-- **A prefix by a capability term's located form is one component, its continuation read canonically at its
place**, which reads back as the prefix on the continuation's reading. -/
theorem encodeFacts_cap {isLoc : Pattern → Prop} {here : Nat} {bound : List TypeExpr} {inner : Prenex}
    {message reading : Pattern} (locVariables : LocVariables isLoc) (hereLoc : isLoc (.bvar here))
    (hereTyped : bound[here]? = some nameType) (messageIs : isMessage message = true)
    (messageApart : ∀ name ∈ messageVariables message, ¬ isLoc name)
    (messageTyped : HasType locatedCalc free bound message capType)
    (decomposed : decompose locatedBlock (Prenex.toPattern locatedBlock inner) = inner)
    (facts : EncodeFacts free isLoc here bound inner reading) :
    EncodeFacts free isLoc here bound
      (Prenex.atom (.apply "LCap" [.bvar here, message, Prenex.toPattern locatedBlock inner]))
      (.apply "ACap" [message, reading]) := by
  have signature : Mettapedia.GSLT.LanguageDef.RestrictionBlocks.BlockSignature locatedCalc locatedBlock :=
    Mettapedia.Languages.ProcessCalculi.Ambient.Located.locatedLanguage.toBlockSignature
  obtain ⟨innerWell, innerMembers, least, reads⟩ := facts
  set component : Pattern := .apply "LCap" [.bvar here, message, Prenex.toPattern locatedBlock inner] with componentIs
  have componentPlace : placeAt component = some (.bvar here) := placeAt_cap _ _ _
  have insideIs : ∀ pattern, insideLoc isLoc 0 [component] pattern → isLoc pattern := by
    intro pattern inside
    cases pattern with
    | bvar index => simpa [insideLoc] using inside
    | fvar name => simpa [insideLoc] using inside
    | _ => simp [insideLoc] at inside
  have hereInside : insideLoc isLoc 0 [component] (.bvar here) := by simpa [insideLoc] using hereLoc
  have continuationTyped : HasType locatedCalc free bound (Prenex.toPattern locatedBlock inner) procType :=
    restricts_typed (language := locatedCalc) (block := locatedBlock) _ (body_typed innerMembers)
  have componentTyped : HasType locatedCalc free bound component procType :=
    lcap_typed (.bvar hereTyped) messageTyped continuationTyped
  refine ⟨.intro hereLoc ?_ ?_ ?_ ?_ ?_ ?_ ?_ ⟨id, ?_⟩ ?_ ?_ ?_, ?_, least + 3, fun fuel enough => ?_⟩
  · intro other member
    simp only [List.mem_singleton] at member
    subst member
    exact .cap
  · intro other member at' isPlaced
    simp only [List.mem_singleton] at member
    subst member
    rw [componentPlace, Option.some.injEq] at isPlaced
    exact .inl (by rw [← isPlaced]; simp [liftBVars])
  · intro index
    exact (List.length_filter_le _ _).trans (by simp)
  · intro other member found isName
    simp only [List.mem_singleton] at member
    subst member
    simp [componentIs, nameOf, markers, capabilities] at isName
  · intro other member label' at' name' continuation isCap listed'
    simp only [List.mem_singleton] at member
    subst member
    simp only [componentIs, Pattern.apply.injEq] at isCap
    obtain ⟨rfl, -⟩ := isCap
    simp [capabilities] at listed'
  · intro other member argument at' isRep
    simp only [List.mem_singleton] at member
    subst member
    simp [componentIs] at isRep
  · intro other member argument isRep
    simp only [List.mem_singleton] at member
    subst member
    simp [componentIs] at isRep
  · intro other member index child below childBelow isPlaced isChild
    simp only [List.mem_singleton] at member
    subst member
    simp [componentIs, childOf, markers] at isChild
  · intro other member message' isMsgOf
    simp only [List.mem_singleton] at member
    subst member
    simp only [componentIs, messageOf, if_true, Option.some.injEq] at isMsgOf
    subst isMsgOf
    exact ⟨messageIs, fun name inVariables inside => messageApart name inVariables (insideIs _ inside)⟩
  · intro other member at' message' continuation isCapComponent
    simp only [List.mem_singleton] at member
    subst member
    simp only [componentIs, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at isCapComponent
    obtain ⟨rfl, rfl, rfl⟩ := isCapComponent
    rw [decomposed]
    exact innerWell.mono locVariables insideIs hereInside
  · intro other member label' at' binder body isInput listed'
    simp only [List.mem_singleton] at member
    subst member
    simp [componentIs] at isInput
  · intro other member
    simp only [Prenex.atom, List.mem_singleton] at member
    subst member
    simpa [Prenex.atom] using componentTyped
  · obtain ⟨step, rfl⟩ : ∃ step, fuel = step + 3 := ⟨fuel - 3, by omega⟩
    have placedHere : placedAt (.bvar here) component = true := by simp [placedAt, componentPlace]
    have lifted : liftBVars 0 0 (Pattern.bvar here) = .bvar here := by simp [liftBVars]
    have read : Prenex.toPattern ambientBlock (decodeForm (step + 3) (.bvar here) (Prenex.atom component)) =
        .apply "ACap" [message, Prenex.toPattern ambientBlock (decodeForm step (.bvar here) inner)] := by
      simp only [decodeForm, Prenex.atom, readPlaced_succ, lifted, List.filter_cons, placedHere, Bool.not_true,
        Bool.false_eq_true, if_true, if_false, List.filter_nil, List.map_cons, List.map_nil, Prenex.toPattern,
        Prenex.restricts, Prenex.body]
      rw [componentIs, readComponent_cap, if_pos messageIs]
      simp only [decodeAt]
      rw [decomposed]
      simp only [Prenex.toPattern, Prenex.body]
    rw [read]
    exact acap_fill (message_typed messageTyped messageIs) (reads step (by omega))

/-- **An input's located form is one component, its body read canonically at its place under the binder**, which
reads back as the input over the body's reading. -/
theorem encodeFacts_input {isLoc : Pattern → Prop} {here : Nat} {bound : List TypeExpr} {label sort : String}
    (listed : (label, sort) ∈ [("LInName", "Name"), ("LInCap", "Cap")]) {inner : Prenex} {reading : Pattern}
    (hereLoc : isLoc (.bvar here)) (hereTyped : bound[here]? = some nameType)
    (decomposed : decompose locatedBlock (Prenex.toPattern locatedBlock inner) = inner)
    (facts : EncodeFacts free (underName isLoc) (here + 1) (.base sort :: bound) inner reading) :
    EncodeFacts free isLoc here bound
      (Prenex.atom (.apply label [.bvar here, .lambda none (Prenex.toPattern locatedBlock inner)]))
      (.apply (ambientInput label) [.lambda none reading]) := by
  have signature : Mettapedia.GSLT.LanguageDef.RestrictionBlocks.BlockSignature locatedCalc locatedBlock :=
    Mettapedia.Languages.ProcessCalculi.Ambient.Located.locatedLanguage.toBlockSignature
  obtain ⟨innerWell, innerMembers, least, reads⟩ := facts
  have isInput : label ∈ inputs := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at listed
    rcases listed with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  set component : Pattern := .apply label [.bvar here, .lambda none (Prenex.toPattern locatedBlock inner)]
    with componentIs
  have componentPlace : placeAt component = some (.bvar here) := placeAt_input isInput _ _
  have insideIs : ∀ pattern, insideLoc isLoc 0 [component] pattern → isLoc pattern := by
    intro pattern inside
    cases pattern with
    | bvar index => simpa [insideLoc] using inside
    | fvar name => simpa [insideLoc] using inside
    | _ => simp [insideLoc] at inside
  have hereInside : insideLoc isLoc 0 [component] (.bvar here) := by simpa [insideLoc] using hereLoc
  have bodyTyped : HasType locatedCalc free (.base sort :: bound) (Prenex.toPattern locatedBlock inner) procType :=
    restricts_typed (language := locatedCalc) (block := locatedBlock) _ (body_typed innerMembers)
  have componentTyped : HasType locatedCalc free bound component procType :=
    linput_typed (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at listed ⊢
      rcases listed with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp) (.bvar hereTyped) bodyTyped
  refine ⟨.intro hereLoc ?_ ?_ ?_ ?_ ?_ ?_ ?_ ⟨id, ?_⟩ ?_ ?_ ?_, ?_, least + 3, fun fuel enough => ?_⟩
  · intro other member
    simp only [List.mem_singleton] at member
    subst member
    exact .input isInput
  · intro other member at' isPlaced
    simp only [List.mem_singleton] at member
    subst member
    rw [componentPlace, Option.some.injEq] at isPlaced
    exact .inl (by rw [← isPlaced]; simp [liftBVars])
  · intro index
    exact (List.length_filter_le _ _).trans (by simp)
  · intro other member found isName
    simp only [List.mem_singleton] at member
    subst member
    simp [componentIs, nameOf] at isName
  · intro other member label' at' name' continuation isCap listed'
    simp only [List.mem_singleton] at member
    subst member
    simp [componentIs] at isCap
  · intro other member argument at' isRep
    simp only [List.mem_singleton] at member
    subst member
    simp [componentIs] at isRep
  · intro other member argument isRep
    simp only [List.mem_singleton] at member
    subst member
    simp [componentIs] at isRep
  · intro other member index child below childBelow isPlaced isChild
    simp only [List.mem_singleton] at member
    subst member
    simp [componentIs, childOf] at isChild
  · intro other member message isMsgOf
    simp only [List.mem_singleton] at member
    subst member
    simp [componentIs, messageOf, not_output_of_input isInput] at isMsgOf
  · intro other member at' message continuation isCapComponent
    simp only [List.mem_singleton] at member
    subst member
    simp [componentIs] at isCapComponent
  · intro other member label' at' binder body isInput' listed'
    simp only [List.mem_singleton] at member
    subst member
    simp only [componentIs, Pattern.apply.injEq, List.cons.injEq, Pattern.lambda.injEq, and_true] at isInput'
    obtain ⟨rfl, rfl, rfl, rfl⟩ := isInput'
    rw [decomposed, show liftBVars 0 1 (Pattern.bvar here) = .bvar (here + 1) by simp [liftBVars]]
    exact innerWell.mono (underName_locVariables _) (underName_mono insideIs) (by simpa [underName] using hereInside)
  · intro other member
    simp only [Prenex.atom, List.mem_singleton] at member
    subst member
    simpa [Prenex.atom] using componentTyped
  · obtain ⟨step, rfl⟩ : ∃ step, fuel = step + 3 := ⟨fuel - 3, by omega⟩
    have placedHere : placedAt (.bvar here) component = true := by simp [placedAt, componentPlace]
    have lifted : liftBVars 0 0 (Pattern.bvar here) = .bvar here := by simp [liftBVars]
    have read : Prenex.toPattern ambientBlock (decodeForm (step + 3) (.bvar here) (Prenex.atom component)) =
        .apply (ambientInput label)
          [.lambda none (Prenex.toPattern ambientBlock (decodeForm step (.bvar (here + 1)) inner))] := by
      simp only [decodeForm, Prenex.atom, readPlaced_succ, lifted, List.filter_cons, placedHere, Bool.not_true,
        Bool.false_eq_true, if_true, if_false, List.filter_nil, List.map_cons, List.map_nil, Prenex.toPattern,
        Prenex.restricts, Prenex.body]
      rw [componentIs, readComponent_input isInput]
      simp only [decodeAt]
      rw [decomposed, show liftBVars 0 1 (Pattern.bvar here) = .bvar (here + 1) by simp [liftBVars]]
      simp only [Prenex.toPattern, Prenex.body]
    rw [read]
    exact input_fill (ambientInput_listed listed) (reads step (by omega))

/-- **An output's located form is one component**, which reads back as the output. -/
theorem encodeFacts_output {isLoc : Pattern → Prop} {here : Nat} {bound : List TypeExpr} {label sort : String}
    (listed : (label, sort) ∈ [("LOutName", "Name"), ("LOutCap", "Cap")]) {message : Pattern}
    (hereLoc : isLoc (.bvar here)) (hereTyped : bound[here]? = some nameType) (messageIs : isMessage message = true)
    (messageApart : ∀ name ∈ messageVariables message, ¬ isLoc name)
    (messageTyped : HasType locatedCalc free bound message (.base sort)) :
    EncodeFacts free isLoc here bound (Prenex.atom (.apply label [.bvar here, message]))
      (.apply (ambientOutput label) [message]) := by
  have isOutput : label ∈ outputs := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at listed
    rcases listed with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  set component : Pattern := .apply label [.bvar here, message] with componentIs
  have componentPlace : placeAt component = some (.bvar here) := placeAt_output isOutput _ _
  have insideIs : ∀ pattern, insideLoc isLoc 0 [component] pattern → isLoc pattern := by
    intro pattern inside
    cases pattern with
    | bvar index => simpa [insideLoc] using inside
    | fvar name => simpa [insideLoc] using inside
    | _ => simp [insideLoc] at inside
  have componentTyped : HasType locatedCalc free bound component procType :=
    loutput_typed (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at listed ⊢
      rcases listed with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp) (.bvar hereTyped) messageTyped
  refine ⟨.intro hereLoc ?_ ?_ ?_ ?_ ?_ ?_ ?_ ⟨id, ?_⟩ ?_ ?_ ?_, ?_, 3, fun fuel enough => ?_⟩
  · intro other member
    simp only [List.mem_singleton] at member
    subst member
    exact .output isOutput
  · intro other member at' isPlaced
    simp only [List.mem_singleton] at member
    subst member
    rw [componentPlace, Option.some.injEq] at isPlaced
    exact .inl (by rw [← isPlaced]; simp [liftBVars])
  · intro index
    exact (List.length_filter_le _ _).trans (by simp)
  · intro other member found isName
    simp only [List.mem_singleton] at member
    subst member
    simp [componentIs, nameOf] at isName
  · intro other member label' at' name' continuation isCap listed'
    simp only [List.mem_singleton] at member
    subst member
    simp [componentIs] at isCap
  · intro other member argument at' isRep
    simp only [List.mem_singleton] at member
    subst member
    simp [componentIs] at isRep
  · intro other member argument isRep
    simp only [List.mem_singleton] at member
    subst member
    simp [componentIs] at isRep
  · intro other member index child below childBelow isPlaced isChild
    simp only [List.mem_singleton] at member
    subst member
    simp [componentIs, childOf] at isChild
  · intro other member message' isMsgOf
    simp only [List.mem_singleton] at member
    subst member
    simp only [componentIs, messageOf, if_pos isOutput, Option.some.injEq] at isMsgOf
    subst isMsgOf
    exact ⟨messageIs, fun name inVariables inside => messageApart name inVariables (insideIs _ inside)⟩
  · intro other member at' message' continuation isCapComponent
    simp only [List.mem_singleton] at member
    subst member
    simp [componentIs] at isCapComponent
  · intro other member label' at' binder body isInput listed'
    simp only [List.mem_singleton] at member
    subst member
    simp only [componentIs, Pattern.apply.injEq] at isInput
    obtain ⟨rfl, -⟩ := isInput
    exact absurd isOutput (not_output_of_input listed')
  · intro other member
    simp only [Prenex.atom, List.mem_singleton] at member
    subst member
    simpa [Prenex.atom] using componentTyped
  · obtain ⟨step, rfl⟩ : ∃ step, fuel = step + 3 := ⟨fuel - 3, by omega⟩
    have placedHere : placedAt (.bvar here) component = true := by simp [placedAt, componentPlace]
    have lifted : liftBVars 0 0 (Pattern.bvar here) = .bvar here := by simp [liftBVars]
    have read : Prenex.toPattern ambientBlock (decodeForm (step + 3) (.bvar here) (Prenex.atom component)) =
        .apply (ambientOutput label) [message] := by
      simp only [decodeForm, Prenex.atom, readPlaced_succ, lifted, List.filter_cons, placedHere, Bool.not_true,
        Bool.false_eq_true, if_true, if_false, List.filter_nil, List.map_cons, List.map_nil, Prenex.toPattern,
        Prenex.restricts, Prenex.body]
      rw [componentIs, readComponent_output isOutput, if_pos messageIs]
    rw [read]
    exact .refl _

/-- **A replication's located form, its replicated molecules, reads back as the replication of its argument's
reading.** -/
theorem encodeFacts_replicated {isLoc : Pattern → Prop} {here : Nat} {bound : List TypeExpr} {inner : Prenex}
    {reading : Pattern} (context : BaseContext free bound)
    (locVariables : LocVariables isLoc) (facts : EncodeFacts free isLoc here bound inner reading) :
    EncodeFacts free isLoc here bound ⟨0, replicatedOf locatedRepBlock (canonicalOf locatedRepBlock) inner⟩
      (.apply "ARep" [reading]) := by
  obtain ⟨innerWell, innerMembers, least, reads⟩ := facts
  obtain ⟨innerCount, innerComponents⟩ := inner
  obtain ⟨repWell, repMembers, repLeast, repReads⟩ :=
    decode_replicatedOf innerWell locVariables context innerMembers
  refine ⟨repWell, repMembers, repLeast + least + 3, fun fuel enough => ?_⟩
  obtain ⟨step, rfl⟩ : ∃ step, fuel = step + 3 := ⟨fuel - 3, by omega⟩
  exact .trans _ _ _ (repReads step (by omega))
    (replicate_fill (language := ambientCoreCalc) (block := ambientRepBlock) (reads (step + 1) (by omega)))

/-! ## The located canonical form reads back as the process -/

open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (rename_comp liftBVars_eq_rename shiftAbove rename_apply
  rename_lambda rename_collection rename_typed canonFacts restrictionsBind_of_typed canonsP_eq_map par_nil
  normal_close_normal foldr_par_atomic par_atomic restriction_binder canonP_replicate_all size decompose_atom
  decompose_toPattern)
open Mettapedia.GSLT.LanguageDef.BagNormalForm (elementsHaveType_iff isObjectPatternList_iff)
open Mettapedia.Languages.ProcessCalculi.Ambient.Full (terms prefixRule)
open Mettapedia.Languages.ProcessCalculi.Ambient.Encoding (NameContext encode_zero encode_nu encode_rep encode_amb
  encode_in encode_out encode_open encode_bag encode_typed encode_object rename_name_typed name_cases_ambient
  liftIndex_inside shiftName_typed)

theorem rename_succ_comp (relabel : Nat → Nat) (pattern : Pattern) :
    rename (Nat.succ ∘ relabel) pattern = liftBVars 0 1 (rename relabel pattern) := by
  rw [liftBVars_eq_rename, rename_comp]
  congr 1

theorem rename_process_typed {count count' : Nat} {relabel : Nat → Nat}
    (inside : ∀ index < count, relabel index < count') {process : Pattern} {type : TypeExpr}
    (typed : HasType ambientCoreCalc free (List.replicate count nameType) process type) :
    HasType ambientCoreCalc free (List.replicate count' nameType) (rename relabel process) type :=
  rename_typed (language := ambientCoreCalc) typed fun index sort lookup => by
    simp only [List.getElem?_replicate] at lookup
    split_ifs at lookup with below
    simp only [Option.some.injEq] at lookup
    subst lookup
    simp [inside index below]

theorem canonP_located_restrict (binder : Option String) (body : Pattern) :
    canonP locatedRepBlock (.apply "LNu" [.lambda binder body]) =
      normal locatedRepBlock (canonP locatedRepBlock body).close :=
  canonP_restrict binder body

theorem canonP_located_replicate {argument : Pattern} (notLambda : ∀ binder body, argument ≠ .lambda binder body) :
    canonP locatedRepBlock (.apply "LRep" [argument]) =
      normal locatedRepBlock ⟨0, replicatedOf locatedRepBlock (canonicalOf locatedRepBlock)
        (canonP locatedRepBlock argument)⟩ :=
  Mettapedia.GSLT.LanguageDef.RestrictionBlocks.canonP_replicate notLambda

/-- A variable is a message. -/
theorem message_of_variable {pattern : Pattern} (isVar : isVariable pattern = true) : isMessage pattern = true := by
  cases pattern <;> simp_all [isVariable, isMessage]

open Mettapedia.Languages.ProcessCalculi.Ambient.Encoding (cap_apply_inv rename_name_sorted rename_cap_typed
  encode_typed_frame shiftName_sorted encode_cap encode_inName encode_inCap encode_outName encode_outCap)
open Mettapedia.Languages.ProcessCalculi.Ambient.Comm (commTerms capRule)

/-- **A typed capability term of the core is a message.** -/
theorem cap_isMessage {bound : List TypeExpr} : ∀ {message : Pattern},
    HasType ambientCoreCalc free bound message capType → isObjectPattern message = true → isMessage message = true
  | .bvar _, _, _ => rfl
  | .fvar _, _, _ => rfl
  | .apply label [], typed, _ => by
      rcases cap_apply_inv typed with ⟨-, _, same, -⟩ | ⟨rfl, -⟩ | ⟨-, _, _, same, -⟩
      · simp at same
      · rfl
      · simp at same
  | .apply label [name], typed, object => by
      rcases cap_apply_inv typed with ⟨listed, name', same, nameTyped⟩ | ⟨-, same⟩ | ⟨-, _, _, same, -⟩
      · simp only [List.cons.injEq, and_true] at same
        subst same
        have nameObject : isObjectPattern name = true := by simpa [isObjectPattern, isObjectPatternList] using object
        rcases name_cases_ambient nameTyped rfl nameObject with ⟨index, rfl, -⟩ | ⟨other, rfl, -⟩ <;>
          simpa [isMessage, isVariable] using listed
      · simp at same
      · simp at same
  | .apply label [first, second], typed, object => by
      rcases cap_apply_inv typed with ⟨-, _, same, -⟩ | ⟨-, same⟩ |
        ⟨rfl, first', second', same, firstTyped, secondTyped⟩
      · simp at same
      · simp at same
      · simp only [List.cons.injEq, and_true] at same
        obtain ⟨rfl, rfl⟩ := same
        have objects : isObjectPattern first = true ∧ isObjectPattern second = true := by
          simpa [isObjectPattern, isObjectPatternList] using object
        simp [isMessage, cap_isMessage firstTyped objects.1, cap_isMessage secondTyped objects.2]
  | .apply label (_ :: _ :: _ :: _), typed, _ => by
      rcases cap_apply_inv typed with ⟨-, _, same, -⟩ | ⟨-, same⟩ | ⟨-, _, _, same, -⟩ <;> simp at same
  | .lambda _ _, typed, _ => by cases typed
  | .multiLambda _ _ _, typed, _ => by cases typed
  | .subst _ _, _, object => by simp [isObjectPattern] at object
  | .collection _ _ _, typed, _ => by
      rcases hasType_collection_inversion typed with ⟨_, typeIs, _⟩ |
        ⟨rule, parameterName, elementType, member, collectionShape, typeIs, -⟩
      · cases typeIs
      simp only [ambientCoreCalc, terms, commTerms, prefixRule, capRule, List.cons_append,
        List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;> simp_all [GrammarRule.bareParams]

/-- **The located canonical form of an ambient process reads back as the process**, in a context of names and
capabilities: its free variables renamed as the located form renames them, every one to one of its sort, and well-located
at the process's location. -/
theorem decode_encode_sorted (names : NameContext free) :
    ∀ (fuel : Nat) {bound bound' : List TypeExpr} {relabel : Nat → Nat} {here : Nat} {isLoc : Pattern → Prop}
      {process : Pattern}, size process < fuel → LocatedFrame bound bound' relabel →
      (∀ type ∈ bound', type = nameType ∨ type = capType) → bound'[here]? = some nameType →
      LocVariables isLoc → isLoc (.bvar here) → (∀ index < bound.length, ¬ isLoc (.bvar (relabel index))) →
      (∀ name, ¬ isLoc (.fvar name)) →
      HasType ambientCoreCalc free bound process procType → isObjectPattern process = true →
      EncodeFacts free isLoc here bound' (canonP locatedRepBlock (encode relabel (.bvar here) process))
        (rename relabel process)
  | 0, _, _, _, _, _, _, small, _, _, _, _, _, _, _, _, _ => absurd small (Nat.not_lt_zero _)
  | fuel + 1, bound, bound', relabel, here, isLoc, process, small, frame, sorted', hereTyped, locVariables, hereLoc,
      namesApart, fvarsApart, typed, object => by
      have fresh : locatedRepBlock.replicate ∉ locatedRepBlock.emptyUnits := by decide
      have restrictFresh : locatedRepBlock.replicate ≠ locatedRepBlock.restrict := by decide
      have context := sorted_base names sorted'
      have hereLocated : HasType locatedCalc free bound' (.bvar here) nameType := .bvar hereTyped
      -- the facts of a located form's canonical block
      have facts : ∀ {bound₀ bound₁ : List TypeExpr} {relabel' : Nat → Nat} {here' part : Pattern},
          LocatedFrame bound₀ bound₁ relabel' → HasType locatedCalc free bound₁ here' nameType →
          isObjectPattern here' = true → HasType ambientCoreCalc free bound₀ part procType →
          isObjectPattern part = true →
          Mettapedia.GSLT.LanguageDef.RestrictionBlocks.CanonFacts locatedRepBlock (encode relabel' here' part) := by
        intro bound₀ bound₁ relabel' here' part frame' hereTyped' hereObject' partTyped partObject
        exact canonFacts fresh restrictFresh (encode_object (size part + 1) (Nat.lt_succ_self _) hereObject'
          partObject) (restrictionsBind_of_typed (block := locatedRepBlock) _
            (encode_typed_frame names frame' hereTyped' hereObject' partTyped partObject))
      -- under a binder of a name or a capability
      have liftedApart : ∀ sort : TypeExpr, ∀ index < (sort :: bound).length,
          ¬ underName isLoc (.bvar (liftIndex 1 relabel index)) := by
        intro sort index below
        cases index with
        | zero => simp [liftIndex, underName]
        | succ index =>
            simp only [liftIndex, show ¬ index + 1 < 1 by omega, if_false, Nat.add_sub_cancel, underName]
            exact namesApart index (by simpa using below)
      have sortedCons : ∀ sort : TypeExpr, sort = nameType ∨ sort = capType →
          ∀ type ∈ sort :: bound', type = nameType ∨ type = capType := by
        intro sort sortIs type member
        rcases List.mem_cons.mp member with rfl | inside
        · exact sortIs
        · exact sorted' type inside
      cases process with
      | bvar index =>
          cases typed with
          | bvar found =>
              rcases frame.sorted _ (List.mem_of_getElem? found) with same | same <;> exact absurd same (by decide)
      | fvar name =>
          cases typed with
          | fvar found => exact absurd (names.free _ _ found) (by decide)
      | lambda binder body => cases typed
      | multiLambda arity binders body => cases typed
      | subst body replacement => simp [isObjectPattern] at object
      | collection kind elements rest =>
          rcases hasType_collection_inversion typed with ⟨_, typeIs, _⟩ |
            ⟨rule, parameterName, elementType, member, shape, typeIs, elementsTyped⟩
          · cases typeIs
          · simp only [ambientCoreCalc, terms, commTerms, prefixRule, capRule, List.cons_append,
              List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
            rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
              rfl | rfl | rfl <;>
              simp [GrammarRule.bareParams] at shape
            obtain ⟨rfl, rfl, rfl⟩ := shape
            have tailNone : rest = none := by
              simpa [isObjectPattern] using (Bool.and_eq_true _ _).mp object |>.1
            subst tailNone
            have objects : ∀ element ∈ elements, isObjectPattern element = true := by
              simpa [isObjectPattern, isObjectPatternList_iff] using object
            have elementTyped : ∀ element ∈ elements, HasType ambientCoreCalc free bound element procType :=
              fun element member => elementsHaveType_iff.mp elementsTyped element member
            have elementSmall : ∀ element ∈ elements, size element < fuel := by
              intro element member
              have := Mettapedia.GSLT.LanguageDef.RestrictionBlocks.size_lt_of_mem member
              simp only [size] at small
              omega
            rw [encode_bag, canonP_bag, canonsP_eq_map, List.map_map, rename_collection]
            exact (encodeFacts_bag hereLoc elements
              (fun element member => decode_encode_sorted names fuel (elementSmall element member) frame sorted'
                hereTyped locVariables hereLoc namesApart fvarsApart (elementTyped element member)
                (objects element member))
              (fun element member => rename_typed (language := ambientCoreCalc) (elementTyped element member)
                frame.sorts)).normal context locVariables
      | apply label arguments =>
          obtain ⟨rule, member, rfl, notBare, typeIs, argumentsTyped⟩ := hasType_apply_inversion typed
          have objects : ∀ argument ∈ arguments, isObjectPattern argument = true := by
            simpa [isObjectPattern, isObjectPatternList_iff] using object
          have argumentSmall : ∀ argument ∈ arguments, size argument < fuel := by
            intro argument inArguments
            have := Mettapedia.GSLT.LanguageDef.RestrictionBlocks.size_lt_of_mem inArguments
            simp only [size] at small
            omega
          -- a name renamed as the located form renames it is a variable, neither the location nor, lifted, under
          -- a new location
          have nameFacts : ∀ {name : Pattern}, HasType ambientCoreCalc free bound name nameType →
              isObjectPattern name = true →
              isVariable (rename relabel name) = true ∧ ¬ isLoc (rename relabel name) ∧
                ¬ underLocation isLoc (liftBVars 0 1 (rename relabel name)) := by
            intro name nameTyped nameObject
            rcases name_cases_ambient nameTyped rfl nameObject with ⟨index, rfl, found⟩ | ⟨name, rfl, found⟩
            · have below : index < bound.length := (List.getElem?_eq_some_iff.mp found).1
              refine ⟨rfl, namesApart index below, ?_⟩
              simpa [rename_bvar, liftBVars, underLocation] using namesApart index below
            · exact ⟨rfl, fvarsApart name, fvarsApart name⟩
          simp only [ambientCoreCalc, terms, commTerms, prefixRule, capRule, List.cons_append,
            List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl <;>
            simp only [procType, TypeExpr.base.injEq] at typeIs <;> try (exact absurd typeIs (by decide))
          · -- inaction
            cases argumentsTyped
            rw [encode_zero, show Pattern.apply "LZero" [] = .apply locatedRepBlock.unit [] from rfl,
              Mettapedia.GSLT.LanguageDef.RestrictionBlocks.canonP_unit, rename_apply, List.map_nil]
            exact encodeFacts_zero hereLoc
          · exact absurd ⟨"ps", .hashBag, .base "Proc", rfl⟩ notBare
          · -- restriction
            cases argumentsTyped with
            | cons representation parameterType argumentTyped rest =>
                cases rest
                obtain ⟨body, rfl⟩ :=
                  (matchesParameterRepresentation_abstractionNamed_iff _ _ _ _).mp representation
                simp only [parameterType?, Option.some.injEq] at parameterType
                subst parameterType
                cases argumentTyped with
                | lambda bodyTyped =>
                    have bodySmall : size body < fuel := by
                      have := argumentSmall _ List.mem_cons_self
                      simp only [size] at this
                      omega
                    have bodyObject : isObjectPattern body = true := by
                      simpa [isObjectPattern] using objects _ List.mem_cons_self
                    have inner := decode_encode_sorted names fuel (here := here + 1) (isLoc := underName isLoc)
                      bodySmall (frame.lift (sort := nameType) (.inl rfl)) (sortedCons nameType (.inl rfl))
                      (by simpa using hereTyped) (underName_locVariables isLoc) (by simpa [underName] using hereLoc)
                      (liftedApart nameType) (fun name => by simpa [underName] using fvarsApart name) bodyTyped
                      bodyObject
                    rw [encode_nu, shiftName_bvar, canonP_located_restrict, rename_apply, List.map_cons,
                      List.map_nil, rename_lambda]
                    exact (encodeFacts_close inner).normal context locVariables
          · -- replication
            cases argumentsTyped with
            | @cons _ argument _ _ _ _ representation parameterType argumentTyped rest =>
                cases rest
                simp only [parameterType?, Option.some.injEq] at parameterType
                subst parameterType
                have inner := decode_encode_sorted names fuel (argumentSmall _ List.mem_cons_self) frame sorted'
                  hereTyped locVariables hereLoc namesApart fvarsApart argumentTyped (objects _ List.mem_cons_self)
                have encodedTyped := encode_typed_frame names frame hereLocated rfl argumentTyped
                  (objects _ List.mem_cons_self)
                rw [encode_rep _ _ (fun binder body same => by subst same; cases argumentTyped),
                  canonP_located_replicate (fun binder body same => by rw [same] at encodedTyped; cases encodedTyped),
                  rename_apply, List.map_cons, List.map_nil]
                exact (encodeFacts_replicated context locVariables inner).normal context locVariables
          · -- an ambient
            cases argumentsTyped with
            | @cons _ name _ _ _ _ nameRepresentation nameParameter nameTyped rest =>
                cases rest with
                | @cons _ content _ _ _ _ contentRepresentation contentParameter contentTyped last =>
                    cases last
                    simp only [parameterType?, Option.some.injEq] at nameParameter contentParameter
                    subst nameParameter contentParameter
                    have nameObject : isObjectPattern name = true := objects _ List.mem_cons_self
                    have contentObject : isObjectPattern content = true :=
                      objects _ (List.mem_cons_of_mem _ List.mem_cons_self)
                    have contentSmall : size content < fuel :=
                      argumentSmall _ (List.mem_cons_of_mem _ List.mem_cons_self)
                    obtain ⟨nameVar, -, nameApart⟩ := nameFacts nameTyped nameObject
                    have inner := decode_encode_sorted names fuel (relabel := Nat.succ ∘ relabel) (here := 0)
                      (isLoc := underLocation isLoc) contentSmall frame.location (sortedCons nameType (.inl rfl))
                      (by simp) (underLocation_locVariables isLoc) (by simp [underLocation])
                      (fun index below => by
                        simpa [underLocation, Function.comp] using namesApart index below)
                      (fun name => by simpa [underLocation] using fvarsApart name) contentTyped contentObject
                    rw [rename_succ_comp] at inner
                    have contentFacts := facts (here' := .bvar 0) frame.location (.bvar (by simp)) rfl
                      contentTyped contentObject
                    have renamedObject : isObjectPattern (rename (Nat.succ ∘ relabel) name) = true := by
                      rw [Mettapedia.GSLT.LanguageDef.RestrictionBlocks.isObjectPattern_rename]
                      exact nameObject
                    have renamedVar : isVariable (rename (Nat.succ ∘ relabel) name) = true := by
                      rw [isVariable_rename, ← isVariable_rename relabel name]
                      exact nameVar
                    have markerCanon : canonP locatedRepBlock
                        (.apply "LAmb" [shiftName (.bvar here), .bvar 0, rename (Nat.succ ∘ relabel) name]) =
                        Prenex.atom (.apply "LAmb" [shiftName (.bvar here), .bvar 0,
                          liftBVars 0 1 (rename relabel name)]) := by
                      rw [shiftName_bvar, canonP_triple (by decide) rfl rfl renamedObject,
                        canonP_variable renamedVar, rename_succ_comp]
                      rfl
                    have markerAtomic : (Prenex.atom (.apply "LAmb" [shiftName (.bvar here), .bvar 0,
                        liftBVars 0 1 (rename relabel name)])).Atomic locatedRepBlock.toBlock := by
                      intro component member
                      simp only [Prenex.atom, List.mem_singleton] at member
                      subst member
                      rw [shiftName_bvar]
                      exact decompose_atom (by simp) (by simp) (by simp) (by simp)
                    rw [encode_amb, canonP_located_restrict, canonP_bag, canonsP_eq_map, List.map_cons,
                      List.map_cons, List.map_nil, List.foldr_cons, List.foldr_cons, List.foldr_nil, par_nil,
                      markerCanon, normal_close_normal fresh restrictFresh (par_atomic markerAtomic contentFacts.atomic),
                      rename_apply, List.map_cons, List.map_cons, List.map_nil]
                    have ambientFacts := encodeFacts_marker (show "LAmb" ∈ markers by simp [markers]) hereLoc
                      hereTyped nameVar nameApart (rename_name_sorted frame.sorts nameTyped nameObject)
                      (rename_typed (language := ambientCoreCalc) contentTyped frame.sorts) inner
                    rw [wrapContent_amb] at ambientFacts
                    exact ambientFacts.normal context locVariables
          rotate_left 3
          · -- a prefix by a capability term
            cases argumentsTyped with
            | @cons _ capability _ _ _ _ capRepresentation capParameter capabilityTyped rest =>
                cases rest with
                | @cons _ content _ _ _ _ contentRepresentation contentParameter contentTyped last =>
                    cases last
                    simp only [parameterType?, Option.some.injEq] at capParameter contentParameter
                    subst capParameter contentParameter
                    have capabilityObject : isObjectPattern capability = true := objects _ List.mem_cons_self
                    have contentObject : isObjectPattern content = true :=
                      objects _ (List.mem_cons_of_mem _ List.mem_cons_self)
                    have contentSmall : size content < fuel :=
                      argumentSmall _ (List.mem_cons_of_mem _ List.mem_cons_self)
                    have renamedMessage : isMessage (rename relabel capability) = true := by
                      rw [isMessage_rename]; exact cap_isMessage capabilityTyped capabilityObject
                    have inner := decode_encode_sorted names fuel contentSmall frame sorted' hereTyped locVariables
                      hereLoc namesApart fvarsApart contentTyped contentObject
                    have contentFacts := facts frame hereLocated rfl contentTyped contentObject
                    have encodedObject : isObjectPattern (encode relabel (.bvar here) content) = true :=
                      encode_object (size content + 1) (Nat.lt_succ_self _) rfl contentObject
                    rw [encode_cap, canonP_cap rfl renamedMessage encodedObject, rename_apply, List.map_cons,
                      List.map_cons, List.map_nil]
                    exact encodeFacts_cap locVariables hereLoc hereTyped renamedMessage
                      (messageVariables_apart namesApart fvarsApart capabilityTyped.isWellScopedAt)
                      (rename_cap_typed names (size capability + 1) (Nat.lt_succ_self _) frame.sorts capabilityTyped
                        capabilityObject)
                      (decompose_toPattern contentFacts.atomic contentFacts.used) inner
          · -- an input of a name: its body under the binder of a name
            cases argumentsTyped with
            | cons representation parameterType argumentTyped rest =>
                cases rest
                obtain ⟨body, rfl⟩ :=
                  (matchesParameterRepresentation_abstractionNamed_iff _ _ _ _).mp representation
                simp only [parameterType?, Option.some.injEq] at parameterType
                subst parameterType
                cases argumentTyped with
                | lambda bodyTyped =>
                    have bodySmall : size body < fuel := by
                      have := argumentSmall _ List.mem_cons_self
                      simp only [size] at this
                      omega
                    have bodyObject : isObjectPattern body = true := by
                      simpa [isObjectPattern] using objects _ List.mem_cons_self
                    have lifted := frame.lift (sort := nameType) (.inl rfl)
                    have inner := decode_encode_sorted names fuel (here := here + 1) (isLoc := underName isLoc)
                      bodySmall lifted (sortedCons nameType (.inl rfl)) (by simpa using hereTyped)
                      (underName_locVariables isLoc) (by simpa [underName] using hereLoc) (liftedApart nameType)
                      (fun name => by simpa [underName] using fvarsApart name) bodyTyped bodyObject
                    have bodyFacts := facts (here' := .bvar (here + 1)) lifted (.bvar (by simpa using hereTyped)) rfl
                      bodyTyped bodyObject
                    have encodedObject : isObjectPattern (encode (liftIndex 1 relabel) (.bvar (here + 1)) body) =
                        true := encode_object (size body + 1) (Nat.lt_succ_self _) rfl bodyObject
                    rw [encode_inName, shiftName_bvar, canonP_input (label := "LInName") (by simp) rfl encodedObject,
                      rename_apply, List.map_cons, List.map_nil, rename_lambda]
                    have input := encodeFacts_input (label := "LInName") (sort := "Name") (by simp) hereLoc
                      hereTyped (decompose_toPattern bodyFacts.atomic bodyFacts.used) inner
                    rw [show ambientInput "LInName" = "AInName" by decide] at input
                    exact input
          · -- an output of a name
            cases argumentsTyped with
            | @cons _ message _ _ _ _ representation parameterType messageTyped rest =>
                cases rest
                simp only [parameterType?, Option.some.injEq] at parameterType
                subst parameterType
                have messageObject : isObjectPattern message = true := objects _ List.mem_cons_self
                obtain ⟨messageVar, -, -⟩ := nameFacts messageTyped messageObject
                have notLambda : ∀ binder body, message ≠ .lambda binder body := by
                  rintro binder body rfl
                  cases messageTyped
                have renamedMessage := message_of_variable messageVar
                rw [encode_outName _ _ notLambda, canonP_output (label := "LOutName") (by simp) rfl renamedMessage,
                  rename_apply, List.map_cons, List.map_nil]
                have output := encodeFacts_output (label := "LOutName") (sort := "Name") (by simp) hereLoc hereTyped
                  renamedMessage
                  (messageVariables_apart namesApart fvarsApart messageTyped.isWellScopedAt)
                  (rename_name_sorted frame.sorts messageTyped messageObject)
                rw [show ambientOutput "LOutName" = "AOutName" by decide] at output
                exact output
          · -- an input of a capability: its body under the binder of a capability
            cases argumentsTyped with
            | cons representation parameterType argumentTyped rest =>
                cases rest
                obtain ⟨body, rfl⟩ :=
                  (matchesParameterRepresentation_abstractionNamed_iff _ _ _ _).mp representation
                simp only [parameterType?, Option.some.injEq] at parameterType
                subst parameterType
                cases argumentTyped with
                | lambda bodyTyped =>
                    have bodySmall : size body < fuel := by
                      have := argumentSmall _ List.mem_cons_self
                      simp only [size] at this
                      omega
                    have bodyObject : isObjectPattern body = true := by
                      simpa [isObjectPattern] using objects _ List.mem_cons_self
                    have lifted := frame.lift (sort := capType) (.inr rfl)
                    have inner := decode_encode_sorted names fuel (here := here + 1) (isLoc := underName isLoc)
                      bodySmall lifted (sortedCons capType (.inr rfl)) (by simpa using hereTyped)
                      (underName_locVariables isLoc) (by simpa [underName] using hereLoc) (liftedApart capType)
                      (fun name => by simpa [underName] using fvarsApart name) bodyTyped bodyObject
                    have bodyFacts := facts (here' := .bvar (here + 1)) lifted (.bvar (by simpa using hereTyped)) rfl
                      bodyTyped bodyObject
                    have encodedObject : isObjectPattern (encode (liftIndex 1 relabel) (.bvar (here + 1)) body) =
                        true := encode_object (size body + 1) (Nat.lt_succ_self _) rfl bodyObject
                    rw [encode_inCap, shiftName_bvar, canonP_input (label := "LInCap") (by simp) rfl encodedObject,
                      rename_apply, List.map_cons, List.map_nil, rename_lambda]
                    have input := encodeFacts_input (label := "LInCap") (sort := "Cap") (by simp) hereLoc
                      hereTyped (decompose_toPattern bodyFacts.atomic bodyFacts.used) inner
                    rw [show ambientInput "LInCap" = "AInCap" by decide] at input
                    exact input
          · -- an output of a capability
            cases argumentsTyped with
            | @cons _ message _ _ _ _ representation parameterType messageTyped rest =>
                cases rest
                simp only [parameterType?, Option.some.injEq] at parameterType
                subst parameterType
                have messageObject : isObjectPattern message = true := objects _ List.mem_cons_self
                have notLambda : ∀ binder body, message ≠ .lambda binder body := by
                  rintro binder body rfl
                  cases messageTyped
                have renamedMessage : isMessage (rename relabel message) = true := by
                  rw [isMessage_rename]; exact cap_isMessage messageTyped messageObject
                rw [encode_outCap _ _ notLambda, canonP_output (label := "LOutCap") (by simp) rfl renamedMessage,
                  rename_apply, List.map_cons, List.map_nil]
                have output := encodeFacts_output (label := "LOutCap") (sort := "Cap") (by simp) hereLoc hereTyped
                  renamedMessage
                  (messageVariables_apart namesApart fvarsApart messageTyped.isWellScopedAt)
                  (rename_cap_typed names (size message + 1) (Nat.lt_succ_self _) frame.sorts messageTyped
                    messageObject)
                rw [show ambientOutput "LOutCap" = "AOutCap" by decide] at output
                exact output
          -- `in n.P`, `out n.P`, `open n.P`
          all_goals
            cases argumentsTyped with
            | @cons _ name _ _ _ _ nameRepresentation nameParameter nameTyped rest =>
                cases rest with
                | @cons _ content _ _ _ _ contentRepresentation contentParameter contentTyped last =>
                    cases last
                    simp only [parameterType?, Option.some.injEq] at nameParameter contentParameter
                    subst nameParameter contentParameter
                    have nameObject : isObjectPattern name = true := objects _ List.mem_cons_self
                    have contentObject : isObjectPattern content = true :=
                      objects _ (List.mem_cons_of_mem _ List.mem_cons_self)
                    have contentSmall : size content < fuel :=
                      argumentSmall _ (List.mem_cons_of_mem _ List.mem_cons_self)
                    obtain ⟨nameVar, nameApart, -⟩ := nameFacts nameTyped nameObject
                    have inner := decode_encode_sorted names fuel contentSmall frame sorted' hereTyped locVariables
                      hereLoc namesApart fvarsApart contentTyped contentObject
                    have contentFacts := facts frame hereLocated rfl contentTyped contentObject
                    have encodedObject : isObjectPattern (encode relabel (.bvar here) content) = true :=
                      encode_object (size content + 1) (Nat.lt_succ_self _) rfl contentObject
                    have capabilityOf : ∀ label ∈ capabilities, EncodeFacts free isLoc here bound'
                        (Prenex.atom (.apply label [.bvar here, rename relabel name,
                          Prenex.toPattern locatedBlock (canonP locatedRepBlock (encode relabel (.bvar here) content))]))
                        (.apply (ambientCapability label) [rename relabel name, rename relabel content]) :=
                      fun label listed => encodeFacts_capability listed locVariables hereLoc hereTyped nameVar
                        nameApart (rename_name_sorted frame.sorts nameTyped nameObject)
                        (decompose_toPattern contentFacts.atomic contentFacts.used) inner
                    first
                      | rw [encode_in, canonP_triple (by decide) rfl nameVar encodedObject, rename_apply,
                          List.map_cons, List.map_cons, List.map_nil]
                        have capability := capabilityOf "LIn" (by simp)
                        rw [show ambientCapability "LIn" = "AIn" by decide] at capability
                        exact capability
                      | rw [encode_out, canonP_triple (by decide) rfl nameVar encodedObject, rename_apply,
                          List.map_cons, List.map_cons, List.map_nil]
                        have capability := capabilityOf "LOut" (by simp)
                        rw [show ambientCapability "LOut" = "AOut" by decide] at capability
                        exact capability
                      | rw [encode_open, canonP_triple (by decide) rfl nameVar encodedObject, rename_apply,
                          List.map_cons, List.map_cons, List.map_nil]
                        have capability := capabilityOf "LOpen" (by simp)
                        rw [show ambientCapability "LOpen" = "AOpen" by decide] at capability
                        exact capability

/-- **The located canonical form of an ambient process reads back as the process**, in a context of names, its free
variables renamed as the located form renames them, and is well-located at the process's location. -/
theorem decode_encode (names : NameContext free) (fuel : Nat) {count count' : Nat} {relabel : Nat → Nat}
    {here : Nat} {isLoc : Pattern → Prop} {process : Pattern} (small : size process < fuel)
    (inside : ∀ index < count, relabel index < count') (hereBelow : here < count')
    (locVariables : LocVariables isLoc) (hereLoc : isLoc (.bvar here))
    (namesApart : ∀ index < count, ¬ isLoc (.bvar (relabel index))) (fvarsApart : ∀ name, ¬ isLoc (.fvar name))
    (typed : HasType ambientCoreCalc free (List.replicate count nameType) process procType)
    (object : isObjectPattern process = true) :
    EncodeFacts free isLoc here (List.replicate count' nameType)
      (canonP locatedRepBlock (encode relabel (.bvar here) process)) (rename relabel process) :=
  decode_encode_sorted names fuel small (LocatedFrame.ofNames inside)
    (fun _ member => .inl (List.eq_of_mem_replicate member)) (by simp [hereBelow]) locVariables hereLoc
    (fun index below => namesApart index (by simpa using below)) fvarsApart typed object

end Mettapedia.Languages.ProcessCalculi.Ambient.Decoding
