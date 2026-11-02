import Mettapedia.Languages.ProcessCalculi.Ambient.Presentations
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationSubstitution

/-!
# Steps of the located calculus

Entering and leaving are reactions of three located atoms (`LocRedex.move`): the marker of the ambient that moves,
the capability at its location, and the marker of the ambient it enters or leaves. Entering moves the mover's marker
from the place both ambients sit at to the target's location; leaving moves it from the target's location to the
place the target sits at; the capability leaves its continuation at the mover's location. Opening is a reaction of
two (`LocRedex.open`): the capability and the marker of the ambient it opens, both at one place; the marker is left
opened, so what stands at the ambient's location stands at the place, and the continuation is left at the place. The
rest of the block is untouched, so these steps are flat: a reaction of parts beside the rest (`LocStep`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Steps

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (instantiateBVar)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (liftIndex)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (Prenex rename rename_apply rename_lambda rename_instantiate)
open Mettapedia.Languages.ProcessCalculi.Ambient.Located (locatedBlock)

/-- **A located redex**: an ambient named `moverName` at location `mover` enters (or leaves) the ambient named
`targetName` at location `target`, which sits at `parent`, by a capability with `continuation` at `mover`. -/
inductive LocRedex
  | move (entering : Bool) (parent mover target moverName targetName continuation : Pattern)
  /-- The ambient named `name` at location `location`, sitting at `place`, is opened by a capability at `place` with
  `continuation`. -/
  | «open» (place location name continuation : Pattern)

namespace LocRedex

/-- Where the mover's marker sits before the step: beside the target when entering, inside it when leaving. -/
def before (entering : Bool) (parent target : Pattern) : Pattern := if entering then parent else target

/-- Where the mover's marker sits after the step. -/
def after (entering : Bool) (parent target : Pattern) : Pattern := if entering then target else parent

/-- The capability's label. -/
def capability (entering : Bool) : String := if entering then "LIn" else "LOut"

/-- **The parts of a redex**: the mover's marker, the capability, the target's marker; the capability and the
marker of the ambient it opens. -/
def parts : LocRedex → List Pattern
  | .move entering parent mover target moverName targetName continuation =>
      [.apply "LAmb" [before entering parent target, mover, moverName],
        .apply (capability entering) [mover, targetName, continuation],
        .apply "LAmb" [parent, target, targetName]]
  | .open place location name continuation =>
      [.apply "LOpen" [place, name, continuation], .apply "LAmb" [place, location, name]]

/-- **What a redex leaves**: the mover's marker moved, the continuation, the target's marker; the continuation and the
opened marker. -/
def result : LocRedex → List Pattern
  | .move entering parent mover target moverName targetName continuation =>
      [.apply "LAmb" [after entering parent target, mover, moverName], continuation,
        .apply "LAmb" [parent, target, targetName]]
  | .open place location name continuation =>
      [continuation, .apply "LOpened" [place, location, name]]

/-- Renaming a redex's variables. -/
def relabel (relabel : Nat → Nat) : LocRedex → LocRedex
  | .move entering parent mover target moverName targetName continuation =>
      .move entering (rename relabel parent) (rename relabel mover)
        (rename relabel target) (rename relabel moverName)
        (rename relabel targetName) (rename relabel continuation)
  | .open place location name continuation =>
      .open (rename relabel place) (rename relabel location) (rename relabel name) (rename relabel continuation)

theorem before_rename (relabel : Nat → Nat) (entering : Bool) (parent target : Pattern) :
    before entering (rename relabel parent) (rename relabel target) =
      rename relabel (before entering parent target) := by
  cases entering <;> rfl

theorem after_rename (relabel : Nat → Nat) (entering : Bool) (parent target : Pattern) :
    after entering (rename relabel parent) (rename relabel target) =
      rename relabel (after entering parent target) := by
  cases entering <;> rfl

theorem parts_relabel (relabel : Nat → Nat) (redex : LocRedex) :
    parts (redex.relabel relabel) = (parts redex).map (rename relabel) := by
  cases redex with
  | move entering parent mover target moverName targetName continuation =>
      simp [parts, LocRedex.relabel, rename_apply, before_rename]
  | «open» place location name continuation => simp [parts, LocRedex.relabel, rename_apply]

theorem result_relabel (relabel : Nat → Nat) (redex : LocRedex) :
    result (redex.relabel relabel) = (result redex).map (rename relabel) := by
  cases redex with
  | move entering parent mover target moverName targetName continuation =>
      simp [result, LocRedex.relabel, rename_apply, after_rename]
  | «open» place location name continuation => simp [result, LocRedex.relabel, rename_apply]

end LocRedex

/-! ## Communication -/

/-- **A located communication**: an input of a name, or of a capability term when `capability`, at `place`, binding a
variable in `body`, receives the message of an output at `place`. -/
structure LocComm where
  capability : Bool
  place : Pattern
  body : Pattern
  message : Pattern

namespace LocComm

/-- The located input's label. -/
def inputLabel (capability : Bool) : String := if capability then "LInCap" else "LInName"

/-- The located output's label. -/
def outputLabel (capability : Bool) : String := if capability then "LOutCap" else "LOutName"

/-- The sort a communication sends: a name, or a capability term. -/
def sort (capability : Bool) : String := if capability then "Cap" else "Name"

/-- The input. -/
def input (comm : LocComm) : Pattern := .apply (inputLabel comm.capability) [comm.place, .lambda none comm.body]

/-- The output. -/
def output (comm : LocComm) : Pattern := .apply (outputLabel comm.capability) [comm.place, comm.message]

/-- **The parts of a communication**: the input and the output, at one place. -/
def parts (comm : LocComm) : List Pattern := [comm.input, comm.output]

/-- **What a communication leaves**: the input's body, receiving the message. -/
def result (comm : LocComm) : List Pattern := [instantiateBVar comm.message comm.body]

/-- Renaming a communication's variables. -/
def relabel (relabel : Nat → Nat) (comm : LocComm) : LocComm :=
  ⟨comm.capability, rename relabel comm.place, rename (liftIndex 1 relabel) comm.body, rename relabel comm.message⟩

theorem parts_relabel (relabel : Nat → Nat) (comm : LocComm) :
    (comm.relabel relabel).parts = comm.parts.map (rename relabel) := by
  simp [parts, input, output, LocComm.relabel, rename_apply, rename_lambda]

theorem result_relabel (relabel : Nat → Nat) (comm : LocComm) :
    (comm.relabel relabel).result = comm.result.map (rename relabel) := by
  simp [result, LocComm.relabel, rename_instantiate]

end LocComm

/-- **A located reaction**: a capability rewriting a marker, or a communication. -/
inductive LocReaction
  | marker (redex : LocRedex)
  | comm (comm : LocComm)

namespace LocReaction

/-- The parts of a reaction. -/
def parts : LocReaction → List Pattern
  | .marker redex => redex.parts
  | .comm communication => communication.parts

/-- What a reaction leaves. -/
def result : LocReaction → List Pattern
  | .marker redex => redex.result
  | .comm communication => communication.result

/-- Renaming a reaction's variables. -/
def relabel (relabel : Nat → Nat) : LocReaction → LocReaction
  | .marker redex => .marker (redex.relabel relabel)
  | .comm communication => .comm (communication.relabel relabel)

theorem parts_relabel (relabel : Nat → Nat) (reaction : LocReaction) :
    (reaction.relabel relabel).parts = reaction.parts.map (rename relabel) := by
  cases reaction with
  | marker redex => exact LocRedex.parts_relabel relabel redex
  | comm communication => exact LocComm.parts_relabel relabel communication

theorem result_relabel (relabel : Nat → Nat) (reaction : LocReaction) :
    (reaction.relabel relabel).result = reaction.result.map (rename relabel) := by
  cases reaction with
  | marker redex => exact LocRedex.result_relabel relabel redex
  | comm communication => exact LocComm.result_relabel relabel communication

end LocReaction

/-- **A step of the located calculus**: a reaction's parts in a bag react, leaving what they leave beside the rest;
and a step under a restriction. -/
inductive LocStep : Pattern → Pattern → Prop
  | react {redex : LocReaction} {components rest : List Pattern} :
      components.Perm (LocReaction.parts redex ++ rest) →
      LocStep (Prenex.body locatedBlock components) (.collection .hashBag (LocReaction.result redex ++ rest) none)
  | restrict {source target : Pattern} : LocStep source target →
      LocStep (.apply "LNu" [.lambda none source]) (.apply "LNu" [.lambda none target])


/-! ## Located atoms read again -/

open Mettapedia.OSLF.MeTTaIL.CanonicalBags (FreeIn freeIn_apply)
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (engineBasePremises)
open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationEquiv)
open Mettapedia.GSLT.LanguageDef.WellSorted (HasType FreeTypeContext isObjectPattern isObjectPatternList
  hasType_apply_inversion parameterType?)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (ReplicationReactions Members BaseContext AlikeR canonP canonR
  canonicalOf canonArgument recanon isReplicated canonicalOf_sound canonR_sound recanon_apply_other
  recanon_apply_restrict recanon_lambda recanon_collection recanon_bvar recanon_fvar recanon_subst)
open Mettapedia.Languages.ProcessCalculi.Ambient.Located (locatedCalc locatedRepBlock locatedLanguage
  capabilityRule capTermRule inputRule outputRule)
open Mettapedia.Languages.ProcessCalculi.Ambient.Encoding (nameType procType name_cases_located marker_typed
  opened_typed capability_typed)
open Mettapedia.Languages.ProcessCalculi.Ambient.Decoding (triple_inv canonArgument_variable canonP_triple
  canonP_variable capabilities markers isVariable not_capability_of_marker not_marker_of_capability)

theorem name_variable {free : FreeTypeContext} {bound : List TypeExpr} {name : Pattern}
    (typed : HasType locatedCalc free bound name nameType) (object : isObjectPattern name = true) :
    isVariable name = true := by
  rcases name_cases_located typed rfl object with ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ <;> rfl

/-- The place of a typed located marker or capability is a name. -/
theorem triple_first {free : FreeTypeContext} {bound : List TypeExpr} {label : String}
    {first second third : Pattern}
    (typed : HasType locatedCalc free bound (.apply label [first, second, third]) procType) :
    HasType locatedCalc free bound first nameType := by
  obtain ⟨rule, member, rfl, notBare, typeIs, arguments⟩ := hasType_apply_inversion typed
  simp only [locatedCalc, capabilityRule, capTermRule, inputRule, outputRule, List.mem_cons,
        List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;>
    simp only [procType, TypeExpr.base.injEq] at typeIs <;> try (exact absurd typeIs (by decide))
  · cases arguments
  · exact absurd ⟨"ps", .hashBag, .base "Proc", rfl⟩ notBare
  · cases arguments with
    | cons _ _ _ rest => cases rest
  · cases arguments with
    | cons _ _ _ rest => cases rest
  all_goals
    cases arguments with
    | cons _ firstParameter firstTyped rest =>
        simp only [parameterType?, Option.some.injEq] at firstParameter
        subst firstParameter
        exact firstTyped

/-- **What a typed object located marker or capability holds**: variables first and second; a variable third in a
marker, a process in a capability. -/
theorem triple_facts {free : FreeTypeContext} {bound : List TypeExpr} {label : String} {first second third : Pattern}
    (notCap : label ≠ "LCap") (typed : HasType locatedCalc free bound (.apply label [first, second, third]) procType)
    (object : isObjectPattern (.apply label [first, second, third]) = true) :
    isVariable first = true ∧ isVariable second = true ∧ isObjectPattern third = true ∧
      ((label ∈ markers ∧ isVariable third = true) ∨
        (label ∈ capabilities ∧ HasType locatedCalc free bound third procType)) := by
  simp only [isObjectPattern, isObjectPatternList, Bool.and_eq_true, Bool.and_true] at object
  obtain ⟨firstObject, secondObject, thirdObject⟩ := object
  refine ⟨name_variable (triple_first typed) firstObject, ?_, thirdObject, ?_⟩
  · rcases triple_inv typed with ⟨-, secondTyped, -⟩ | ⟨-, secondTyped, -⟩ | ⟨isCap, -, -⟩
    · exact name_variable secondTyped secondObject
    · exact name_variable secondTyped secondObject
    · exact absurd isCap notCap
  · rcases triple_inv typed with ⟨isMarker, -, thirdTyped⟩ | ⟨listed, -, thirdTyped⟩ | ⟨isCap, -, -⟩
    · exact .inl ⟨isMarker, name_variable thirdTyped thirdObject⟩
    · exact .inr ⟨listed, thirdTyped⟩
    · exact absurd isCap notCap

/-- **A component read again as a located triple reads is that triple**, its third argument read as it reads. -/
theorem shown_triple {free : FreeTypeContext} {bound : List TypeExpr} {shown first second reading : Pattern}
    {label : String} (shownTyped : HasType locatedCalc free bound shown procType)
    (shownObject : isObjectPattern shown = true) (notRestrict : label ≠ "LNu") (notCap : label ≠ "LCap")
    (read : recanon locatedRepBlock shown = .apply label [first, second, reading]) :
    ∃ third, shown = .apply label [first, second, third] ∧
      canonArgument (canonicalOf locatedRepBlock) third = reading := by
  cases shown with
  | apply label' arguments =>
      by_cases isRestrict : label' = locatedRepBlock.restrict
      · subst isRestrict
        rw [recanon_apply_restrict] at read
        simp only [Pattern.apply.injEq] at read
        exact absurd read.1.symm notRestrict
      rw [recanon_apply_other isRestrict (by simp)] at read
      simp only [Pattern.apply.injEq] at read
      obtain ⟨rfl, mapped⟩ := read
      have lengthThree : arguments.length = 3 := by simpa using congrArg List.length mapped
      obtain ⟨first', second', third', rfl⟩ := List.length_eq_three.mp lengthThree
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at mapped
      obtain ⟨firstIs, secondIs, thirdIs⟩ := mapped
      obtain ⟨firstVar, secondVar, -, -⟩ := triple_facts notCap shownTyped shownObject
      rw [canonArgument_variable firstVar] at firstIs
      rw [canonArgument_variable secondVar] at secondIs
      subst firstIs secondIs
      exact ⟨third', rfl, thirdIs⟩
  | collection kind elements rest =>
      rw [recanon_collection] at read
      cases read
  | lambda binder body =>
      rw [recanon_lambda] at read
      cases read
  | bvar index =>
      rw [recanon_bvar] at read
      cases read
  | fvar name' =>
      rw [recanon_fvar] at read
      cases read
  | subst body replacement =>
      rw [recanon_subst] at read
      cases read
  | multiLambda => cases shownTyped

/-- **An argument read canonically is equivalent to it.** -/
theorem canonArgument_equivalent {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound)
    {argument : Pattern} {sort : String} (typed : HasType locatedCalc free bound argument (.base sort)) :
    EquationEquiv (engineBasePremises RelationEnv.empty) locatedCalc
      (canonArgument (canonicalOf locatedRepBlock) argument) argument := by
  cases argument with
  | lambda => cases typed
  | multiLambda => cases typed
  | bvar => exact .refl _
  | fvar => exact .refl _
  | subst => exact .refl _
  | apply =>
      exact .symm _ _ (canonicalOf_sound (block := locatedRepBlock) context typed).2.toEquationEquiv
  | collection =>
      exact .symm _ _ (canonicalOf_sound (block := locatedRepBlock) context typed).2.toEquationEquiv

theorem recanon_eq_of_alike {first second : Pattern} (alike : AlikeR locatedRepBlock first second) :
    recanon locatedRepBlock first = recanon locatedRepBlock second := by
  have read := alike.2.2.1 id Function.injective_id
  rwa [Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_id,
    Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_id] at read


/-! ## Entering and leaving as reactions -/

open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (canonP_apply restrictionsBind)

/-- **A located triple is its own canonical block**, its arguments read canonically. -/
theorem canonP_three (label : String) (first second third : Pattern) :
    canonP locatedRepBlock (.apply label [first, second, third]) =
      Prenex.atom (canonR locatedRepBlock (.apply label [first, second, third])) := by
  have atomIs := canonP_apply (block := locatedRepBlock) (label := label) (arguments := [first, second, third])
    (by simp) (by simp) (by simp) (by simp)
  rw [canonR, atomIs]
  rfl

/-- The canonical form of a located triple of variables is itself, its third argument read canonically. -/
theorem canonR_triple {label : String} (notRestrict : label ≠ "LNu") {first second third : Pattern}
    (firstVar : isVariable first = true) (secondVar : isVariable second = true)
    (thirdObject : isObjectPattern third = true) :
    canonR locatedRepBlock (.apply label [first, second, third]) =
      .apply label [first, second, canonR locatedRepBlock third] := by
  rw [canonR, canonP_triple notRestrict firstVar secondVar thirdObject]
  rfl

theorem recanon_triple {label : String} (notRestrict : label ≠ "LNu") {first second third : Pattern}
    (firstVar : isVariable first = true) (secondVar : isVariable second = true) :
    recanon locatedRepBlock (.apply label [first, second, third]) =
      .apply label [first, second, canonArgument (canonicalOf locatedRepBlock) third] := by
  rw [recanon_apply_other notRestrict (by simp)]
  simp [canonArgument_variable firstVar, canonArgument_variable secondVar]

/-- A marker of variables is its own canonical form. -/
theorem canonR_marker {parent here name : Pattern} (parentVar : isVariable parent = true)
    (hereVar : isVariable here = true) (nameVar : isVariable name = true) :
    canonR locatedRepBlock (.apply "LAmb" [parent, here, name]) = .apply "LAmb" [parent, here, name] := by
  rw [canonR_triple (by decide) parentVar hereVar (by cases name <;> simp_all [isVariable, isObjectPattern])]
  rw [canonR, canonP_variable nameVar]
  rfl

namespace LocRedex

variable {free : FreeTypeContext}

theorem capability_listed (entering : Bool) : capability entering ∈ capabilities := by
  cases entering <;> simp [capability]

theorem capability_ne (entering : Bool) : capability entering ≠ "LNu" ∧ capability entering ∉ markers := by
  cases entering <;> simp [capability, markers]

/-- **A component read alike to a marker of variables is that marker.** -/
theorem alike_marker {bound : List TypeExpr} {shown parent here name : Pattern}
    (typed : HasType locatedCalc free bound (.apply "LAmb" [parent, here, name]) procType)
    (object : isObjectPattern (.apply "LAmb" [parent, here, name]) = true)
    (shownTyped : HasType locatedCalc free bound shown procType) (shownObject : isObjectPattern shown = true)
    (alike : AlikeR locatedRepBlock shown (canonR locatedRepBlock (.apply "LAmb" [parent, here, name]))) :
    shown = .apply "LAmb" [parent, here, name] := by
  obtain ⟨parentVar, hereVar, -, kind⟩ := triple_facts (by decide) typed object
  have nameVar : isVariable name = true := by
    rcases kind with ⟨-, isVar⟩ | ⟨listed, -⟩
    · exact isVar
    · simp at listed
  have read := recanon_eq_of_alike alike
  rw [canonR_marker parentVar hereVar nameVar, recanon_triple (by decide) parentVar hereVar,
    canonArgument_variable nameVar] at read
  obtain ⟨third, rfl, thirdIs⟩ := shown_triple shownTyped shownObject (by decide) (by decide) read
  obtain ⟨-, -, -, shownKind⟩ := triple_facts (by decide) shownTyped shownObject
  rcases shownKind with ⟨-, thirdVar⟩ | ⟨listed, -⟩
  · rw [canonArgument_variable thirdVar] at thirdIs
    rw [thirdIs]
  · simp at listed

/-- **A component read alike to a capability is that capability**, its continuation equivalent to the original
one. -/
theorem alike_capability {bound : List TypeExpr} (context : BaseContext free bound) {label : String}
    (listed : label ∈ capabilities) {shown place name continuation : Pattern}
    (typed : HasType locatedCalc free bound (.apply label [place, name, continuation]) procType)
    (object : isObjectPattern (.apply label [place, name, continuation]) = true)
    (shownTyped : HasType locatedCalc free bound shown procType) (shownObject : isObjectPattern shown = true)
    (alike : AlikeR locatedRepBlock shown (canonR locatedRepBlock (.apply label [place, name, continuation]))) :
    ∃ continuation', shown = .apply label [place, name, continuation'] ∧
      EquationEquiv (engineBasePremises RelationEnv.empty) locatedCalc continuation' continuation := by
  have notRestrict : label ≠ "LNu" := by
    simp only [capabilities, List.mem_cons, List.not_mem_nil, or_false] at listed
    rcases listed with rfl | rfl | rfl <;> decide
  have notCap : label ≠ "LCap" := by rintro rfl; simp [capabilities] at listed
  obtain ⟨placeVar, nameVar, continuationObject, kind⟩ := triple_facts notCap typed object
  have continuationTyped : HasType locatedCalc free bound continuation procType := by
    rcases kind with ⟨isMarker, -⟩ | ⟨-, typed⟩
    · exact absurd listed (not_capability_of_marker isMarker)
    · exact typed
  have read := recanon_eq_of_alike alike
  rw [canonR_triple notRestrict placeVar nameVar continuationObject,
    recanon_triple notRestrict placeVar nameVar] at read
  obtain ⟨continuation', rfl, continuationIs⟩ := shown_triple shownTyped shownObject notRestrict notCap read
  obtain ⟨-, -, -, shownKind⟩ := triple_facts notCap shownTyped shownObject
  have continuation'Typed : HasType locatedCalc free bound continuation' procType := by
    rcases shownKind with ⟨isMarker, -⟩ | ⟨-, typed⟩
    · exact absurd listed (not_capability_of_marker isMarker)
    · exact typed
  obtain ⟨canonTyped, toCanon⟩ := canonR_sound (block := locatedRepBlock) context continuationTyped
  have shownSide := canonArgument_equivalent context continuation'Typed
  have originalSide := canonArgument_equivalent context canonTyped
  rw [continuationIs] at shownSide
  exact ⟨continuation', rfl,
    .trans _ _ _ (.symm _ _ shownSide) (.trans _ _ _ originalSide (.symm _ _ toCanon.toEquationEquiv))⟩

/-- **Components read alike to the canonical forms of a redex's parts are a redex**, its continuation equivalent
to the original one. -/
theorem alike {bound : List TypeExpr} (context : BaseContext free bound) (redex : LocRedex) (shown : List Pattern)
    (partsMembers : Members locatedCalc locatedBlock free bound redex.parts)
    (partsObjects : ∀ part ∈ redex.parts, isObjectPattern part = true)
    (shownMembers : Members locatedCalc locatedBlock free bound shown)
    (shownObjects : ∀ part ∈ shown, isObjectPattern part = true)
    (related : List.Forall₂ (fun part original => AlikeR locatedRepBlock part (canonR locatedRepBlock original))
      shown redex.parts) :
    ∃ redex' : LocRedex, redex'.parts = shown ∧
      List.Forall₂ (EquationEquiv (engineBasePremises RelationEnv.empty) locatedCalc) redex'.result redex.result := by
  cases redex with
  | move entering parent mover target moverName targetName continuation =>
      simp only [parts] at partsMembers partsObjects related
      cases related with
      | cons firstAlike rest =>
      cases rest with
      | cons secondAlike rest =>
      cases rest with
      | cons thirdAlike last =>
      cases last
      rename_i moverShown capabilityShown targetShown
      have moverShownIs := alike_marker (partsMembers _ (by simp)) (partsObjects _ (by simp))
        (shownMembers moverShown (by simp)) (shownObjects moverShown (by simp)) firstAlike
      have targetShownIs := alike_marker (partsMembers _ (by simp)) (partsObjects _ (by simp))
        (shownMembers targetShown (by simp)) (shownObjects targetShown (by simp)) thirdAlike
      obtain ⟨continuation', capabilityIs, continued⟩ := alike_capability context (capability_listed entering)
        (partsMembers _ (by simp)) (partsObjects _ (by simp)) (shownMembers capabilityShown (by simp))
        (shownObjects capabilityShown (by simp)) secondAlike
      refine ⟨.move entering parent mover target moverName targetName continuation', ?_, ?_⟩
      · simp only [parts, moverShownIs, capabilityIs, targetShownIs]
      · exact .cons (.refl _) (.cons continued (.cons (.refl _) .nil))
  | «open» place location name continuation =>
      simp only [parts] at partsMembers partsObjects related
      cases related with
      | cons firstAlike rest =>
      cases rest with
      | cons secondAlike last =>
      cases last
      rename_i capabilityShown markerShown
      have markerShownIs := alike_marker (partsMembers _ (by simp)) (partsObjects _ (by simp))
        (shownMembers markerShown (by simp)) (shownObjects markerShown (by simp)) secondAlike
      obtain ⟨continuation', capabilityIs, continued⟩ := alike_capability context
        (show "LOpen" ∈ capabilities by simp [capabilities])
        (partsMembers _ (by simp)) (partsObjects _ (by simp)) (shownMembers capabilityShown (by simp))
        (shownObjects capabilityShown (by simp)) firstAlike
      refine ⟨.open place location name continuation', ?_, ?_⟩
      · simp only [parts, capabilityIs, markerShownIs]
      · exact .cons continued (.cons (.refl _) .nil)


/-- **What a redex leaves are processes**, wherever its parts are. -/
theorem result_members {bound : List TypeExpr} (redex : LocRedex)
    (members : Members locatedCalc locatedBlock free bound redex.parts) :
    Members locatedCalc locatedBlock free bound redex.result := by
  cases redex with
  | move entering parent mover target moverName targetName continuation =>
  simp only [parts] at members
  have moverTyped := members (.apply "LAmb" [before entering parent target, mover, moverName]) (by simp)
  have capabilityTyped := members (.apply (capability entering) [mover, targetName, continuation]) (by simp)
  have targetTyped := members (.apply "LAmb" [parent, target, targetName]) (by simp)
  obtain ⟨-, capNotMarker⟩ := capability_ne entering
  have parentTyped := triple_first targetTyped
  have moverName' : HasType locatedCalc free bound mover nameType := triple_first capabilityTyped
  obtain ⟨targetLocTyped, moverNameTyped⟩ : HasType locatedCalc free bound target nameType ∧
      HasType locatedCalc free bound moverName nameType := by
    rcases triple_inv targetTyped with ⟨-, second, -⟩ | ⟨listed, -, -⟩ | ⟨isCap, -, -⟩
    · rcases triple_inv moverTyped with ⟨-, -, third⟩ | ⟨listed', -, -⟩ | ⟨isCap', -, -⟩
      · exact ⟨second, third⟩
      · simp at listed'
      · simp at isCap'
    · simp at listed
    · simp at isCap
  have continuationTyped : HasType locatedCalc free bound continuation procType := by
    rcases triple_inv capabilityTyped with ⟨isMarker, -⟩ | ⟨-, -, third⟩ | ⟨-, -, third⟩
    · exact absurd isMarker capNotMarker
    · exact third
    · exact third
  intro element member
  simp only [result, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · cases entering
    · exact marker_typed parentTyped moverName' moverNameTyped
    · exact marker_typed targetLocTyped moverName' moverNameTyped
  · exact continuationTyped
  · exact targetTyped
  | «open» place location name continuation =>
  simp only [parts] at members
  have capabilityTyped := members (.apply "LOpen" [place, name, continuation]) (by simp)
  have markerTyped := members (.apply "LAmb" [place, location, name]) (by simp)
  have placeTyped := triple_first markerTyped
  obtain ⟨locationTyped, nameTyped⟩ : HasType locatedCalc free bound location nameType ∧
      HasType locatedCalc free bound name nameType := by
    rcases triple_inv markerTyped with ⟨-, second, third⟩ | ⟨listed, -, -⟩ | ⟨isCap, -, -⟩
    · exact ⟨second, third⟩
    · simp at listed
    · simp at isCap
  have continuationTyped : HasType locatedCalc free bound continuation procType := by
    rcases triple_inv capabilityTyped with ⟨isMarker, -⟩ | ⟨-, -, third⟩ | ⟨-, -, third⟩
    · simp [markers] at isMarker
    · exact third
    · exact third
  intro element member
  simp only [result, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact continuationTyped
  · exact opened_typed placeTyped locationTyped nameTyped

theorem result_objects (redex : LocRedex) (objects : ∀ part ∈ redex.parts, isObjectPattern part = true) :
    ∀ element ∈ redex.result, isObjectPattern element = true := by
  cases redex with
  | move entering parent mover target moverName targetName continuation =>
  simp only [parts] at objects
  have moverObject := objects (.apply "LAmb" [before entering parent target, mover, moverName]) (by simp)
  have capabilityObject := objects (.apply (capability entering) [mover, targetName, continuation]) (by simp)
  have targetObject := objects (.apply "LAmb" [parent, target, targetName]) (by simp)
  simp only [isObjectPattern, isObjectPatternList, Bool.and_eq_true, Bool.and_true] at moverObject
  simp only [isObjectPattern, isObjectPatternList, Bool.and_eq_true, Bool.and_true] at capabilityObject
  simp only [isObjectPattern, isObjectPatternList, Bool.and_eq_true, Bool.and_true] at targetObject
  intro element member
  simp only [result, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · cases entering <;>
      simp [isObjectPattern, isObjectPatternList, after, moverObject.2.1, moverObject.2.2, targetObject.1,
        targetObject.2.1]
  · exact capabilityObject.2.2
  · simp [isObjectPattern, isObjectPatternList, targetObject.1, targetObject.2.1, targetObject.2.2]
  | «open» place location name continuation =>
  simp only [parts] at objects
  have capabilityObject := objects (.apply "LOpen" [place, name, continuation]) (by simp)
  have markerObject := objects (.apply "LAmb" [place, location, name]) (by simp)
  simp only [isObjectPattern, isObjectPatternList, Bool.and_eq_true, Bool.and_true] at capabilityObject
  simp only [isObjectPattern, isObjectPatternList, Bool.and_eq_true, Bool.and_true] at markerObject
  intro element member
  simp only [result, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact capabilityObject.2.2
  · simp [isObjectPattern, isObjectPatternList, markerObject.1, markerObject.2.1, markerObject.2.2]

/-- **What a redex leaves uses only the variables of its parts.** -/
theorem freeIn_result (redex : LocRedex) {index : Nat} {element : Pattern} (member : element ∈ redex.result)
    (free : FreeIn index element) : ∃ part ∈ redex.parts, FreeIn index part := by
  cases redex with
  | move entering parent mover target moverName targetName continuation =>
  simp only [result, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | same <;> subst same
  · obtain ⟨argument, inArguments, argumentFree⟩ := freeIn_apply.mp free
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inArguments
    rcases inArguments with same | same | same
    · refine ⟨.apply "LAmb" [parent, target, targetName], by simp [parts],
        freeIn_apply.mpr ⟨argument, ?_, argumentFree⟩⟩
      rw [same]
      cases entering <;> simp [after]
    · exact ⟨.apply "LAmb" [before entering parent target, mover, moverName], by simp [parts],
        freeIn_apply.mpr ⟨argument, by simp [same], argumentFree⟩⟩
    · exact ⟨.apply "LAmb" [before entering parent target, mover, moverName], by simp [parts],
        freeIn_apply.mpr ⟨argument, by simp [same], argumentFree⟩⟩
  · exact ⟨.apply (capability entering) [mover, targetName, element], by simp [parts],
      freeIn_apply.mpr ⟨element, by simp, free⟩⟩
  · exact ⟨.apply "LAmb" [parent, target, targetName], by simp [parts], free⟩
  | «open» place location name continuation =>
  simp only [result, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same <;> subst same
  · exact ⟨.apply "LOpen" [place, name, element], by simp [parts], freeIn_apply.mpr ⟨element, by simp, free⟩⟩
  · obtain ⟨argument, inArguments, argumentFree⟩ := freeIn_apply.mp free
    exact ⟨.apply "LAmb" [place, location, name], by simp [parts],
      freeIn_apply.mpr ⟨argument, by simpa using inArguments, argumentFree⟩⟩

end LocRedex

theorem isReplicated_canonR_three (label : String) (first second third : Pattern) :
    isReplicated locatedRepBlock (canonR locatedRepBlock (.apply label [first, second, third])) = false := by
  have atomIs := canonP_apply (block := locatedRepBlock) (label := label) (arguments := [first, second, third])
    (by simp) (by simp) (by simp) (by simp)
  rw [canonR, atomIs]
  simp [isReplicated, Prenex.atom, Prenex.toPattern, Prenex.restricts, Prenex.body,
    Mettapedia.GSLT.LanguageDef.RestrictionBlocks.canonsP_eq_map]

/-- **A part of a marker reaction is its own canonical block.** -/
theorem LocRedex.canonicalAtoms (redex : LocRedex) :
    ∀ part ∈ redex.parts, canonP locatedRepBlock part = Prenex.atom (canonR locatedRepBlock part) := by
  intro part member
  cases redex with
  | move entering parent mover target moverName targetName continuation =>
      simp only [LocRedex.parts, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;> exact canonP_three _ _ _ _
  | «open» place location name continuation =>
      simp only [LocRedex.parts, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> exact canonP_three _ _ _ _

/-- **A part of a marker reaction, read canonically, is not replicated.** -/
theorem LocRedex.plain (redex : LocRedex) :
    ∀ part ∈ redex.parts, isReplicated locatedRepBlock (canonR locatedRepBlock part) = false := by
  intro part member
  cases redex with
  | move entering parent mover target moverName targetName continuation =>
      simp only [LocRedex.parts, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;> exact isReplicated_canonR_three _ _ _ _
  | «open» place location name continuation =>
      simp only [LocRedex.parts, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> exact isReplicated_canonR_three _ _ _ _

theorem LocRedex.arity_le (redex : LocRedex) : redex.parts.length ≤ 3 := by
  cases redex <;> simp [LocRedex.parts]

/-- **Entering, leaving and opening are the pure calculus's located reactions**, in the replication theory's sense:
flat reactions of three or two located atoms beside the rest of a block. -/
def locatedReactions : ReplicationReactions locatedCalc locatedRepBlock LocStep where
  Redex := LocRedex
  parts := LocRedex.parts
  result := LocRedex.result
  rename relabel redex := redex.relabel relabel
  parts_rename := LocRedex.parts_relabel
  result_rename := LocRedex.result_relabel
  canonicalAtoms redex part member _ _ := LocRedex.canonicalAtoms redex part member
  plain redex part member _ _ := LocRedex.plain redex part member
  arity := 3
  arity_le redex := LocRedex.arity_le redex
  result_members redex members := LocRedex.result_members redex members
  result_objects redex objects := LocRedex.result_objects redex objects
  freeIn_result redex _ _ member free := LocRedex.freeIn_result redex member free
  alike context redex shown members objects shownMembers shownObjects related :=
    LocRedex.alike context redex shown members objects shownMembers shownObjects related
  react redex _ _ permutation _ _ := ⟨_, .react (redex := .marker redex) permutation, .refl _⟩
  restrict stepped := .restrict stepped

/-! ## Communication as a reaction -/

open Mettapedia.Languages.ProcessCalculi.Ambient.Comm (capType)
open Mettapedia.OSLF.MeTTaIL.ContextSubstitution (substitute_single_eq_instantiateBVar)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (freeIn_lambda)
open Mettapedia.GSLT.LanguageDef.WellSorted (hasType_collection_inversion)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (isObject_substitute freeIn_instantiate
  sortedEquiv_instantiate_replication)
open Mettapedia.Languages.ProcessCalculi.Ambient.Located (capTermRule)
open Mettapedia.Languages.ProcessCalculi.Ambient.Encoding (name_cases_located)
open Mettapedia.Languages.ProcessCalculi.Ambient.Decoding (pair_inv inputs outputs canonP_input canonP_output
  recanon_input recanon_output canonArgument_message message_of_variable isMessage)

/-- **A capability term of the located calculus is built by a constructor**: `in n`, `out n` or `open n` over a name,
the empty path, or the path of two capability terms. -/
theorem located_cap_apply_inv {free : FreeTypeContext} {bound : List TypeExpr} {label : String}
    {arguments : List Pattern} (typed : HasType locatedCalc free bound (.apply label arguments) capType) :
    (label ∈ ["CapIn", "CapOut", "CapOpen"] ∧ ∃ name, arguments = [name] ∧
        HasType locatedCalc free bound name nameType) ∨
      (label = "CapEps" ∧ arguments = []) ∨
      (label = "CapPath" ∧ ∃ left right, arguments = [left, right] ∧
        HasType locatedCalc free bound left capType ∧ HasType locatedCalc free bound right capType) := by
  obtain ⟨rule, member, rfl, -, typeIs, argumentsTyped⟩ := hasType_apply_inversion typed
  simp only [locatedCalc, capabilityRule, capTermRule, inputRule, outputRule, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;>
    simp only [capType, TypeExpr.base.injEq] at typeIs <;> try (exact absurd typeIs (by decide))
  all_goals try (
    cases argumentsTyped with
    | cons _ parameter nameTyped rest =>
        cases rest
        simp only [parameterType?, Option.some.injEq] at parameter
        subst parameter
        exact .inl ⟨by simp, _, rfl, nameTyped⟩)
  · cases argumentsTyped
    exact .inr (.inl ⟨rfl, rfl⟩)
  · cases argumentsTyped with
    | cons _ leftParameter leftTyped rest =>
        cases rest with
        | cons _ rightParameter rightTyped last =>
            cases last
            simp only [parameterType?, Option.some.injEq] at leftParameter rightParameter
            subst leftParameter rightParameter
            exact .inr (.inr ⟨rfl, _, _, rfl, leftTyped, rightTyped⟩)

/-- **A typed object capability term of the located calculus is a message.** -/
theorem located_cap_isMessage {free : FreeTypeContext} {bound : List TypeExpr} : ∀ {message : Pattern},
    HasType locatedCalc free bound message capType → isObjectPattern message = true → isMessage message = true
  | .bvar _, _, _ => rfl
  | .fvar _, _, _ => rfl
  | .apply label [], typed, _ => by
      rcases located_cap_apply_inv typed with ⟨-, _, same, -⟩ | ⟨rfl, -⟩ | ⟨-, _, _, same, -⟩
      · simp at same
      · rfl
      · simp at same
  | .apply label [name], typed, object => by
      rcases located_cap_apply_inv typed with ⟨listed, name', same, nameTyped⟩ | ⟨-, same⟩ | ⟨-, _, _, same, -⟩
      · simp only [List.cons.injEq, and_true] at same
        subst same
        have nameObject : isObjectPattern name = true := by simpa [isObjectPattern, isObjectPatternList] using object
        rcases name_cases_located nameTyped rfl nameObject with ⟨index, rfl, -⟩ | ⟨other, rfl, -⟩ <;>
          simpa [isMessage, Mettapedia.Languages.ProcessCalculi.Ambient.Decoding.isVariable] using listed
      · simp at same
      · simp at same
  | .apply label [first, second], typed, object => by
      rcases located_cap_apply_inv typed with ⟨-, _, same, -⟩ | ⟨-, same⟩ |
        ⟨rfl, first', second', same, firstTyped, secondTyped⟩
      · simp at same
      · simp at same
      · simp only [List.cons.injEq, and_true] at same
        obtain ⟨rfl, rfl⟩ := same
        have objects : isObjectPattern first = true ∧ isObjectPattern second = true := by
          simpa [isObjectPattern, isObjectPatternList] using object
        simp [isMessage, located_cap_isMessage firstTyped objects.1, located_cap_isMessage secondTyped objects.2]
  | .apply label (_ :: _ :: _ :: _), typed, _ => by
      rcases located_cap_apply_inv typed with ⟨-, _, same, -⟩ | ⟨-, same⟩ | ⟨-, _, _, same, -⟩ <;> simp at same
  | .lambda _ _, typed, _ => by cases typed
  | .multiLambda _ _ _, typed, _ => by cases typed
  | .subst _ _, _, object => by simp [isObjectPattern] at object
  | .collection _ _ _, typed, _ => by
      rcases hasType_collection_inversion typed with ⟨_, typeIs, _⟩ |
        ⟨rule, parameterName, elementType, member, collectionShape, typeIs, -⟩
      · cases typeIs
      simp only [locatedCalc, capabilityRule, capTermRule, inputRule, outputRule, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl <;> simp_all [GrammarRule.bareParams]

/-- A located pair of two arguments is its own canonical block, its arguments read canonically. -/
theorem canonP_two (label : String) (first second : Pattern) :
    canonP locatedRepBlock (.apply label [first, second]) =
      Prenex.atom (canonR locatedRepBlock (.apply label [first, second])) := by
  have atomIs := canonP_apply (block := locatedRepBlock) (label := label) (arguments := [first, second])
    (by simp) (by simp) (by simp) (by simp)
  rw [canonR, atomIs]
  rfl

theorem isReplicated_canonR_two (label : String) (first second : Pattern) :
    isReplicated locatedRepBlock (canonR locatedRepBlock (.apply label [first, second])) = false := by
  have atomIs := canonP_apply (block := locatedRepBlock) (label := label) (arguments := [first, second])
    (by simp) (by simp) (by simp) (by simp)
  rw [canonR, atomIs]
  simp [isReplicated, Prenex.atom, Prenex.toPattern, Prenex.restricts, Prenex.body,
    Mettapedia.GSLT.LanguageDef.RestrictionBlocks.canonsP_eq_map]

/-- **A component read again as a located pair reads is a pair of that label**, its arguments read as the pair's. -/
theorem shown_pair {free : FreeTypeContext} {bound : List TypeExpr} {shown first second : Pattern}
    {label : String} (shownTyped : HasType locatedCalc free bound shown procType) (notRestrict : label ≠ "LNu")
    (read : recanon locatedRepBlock shown = .apply label [first, second]) :
    ∃ first' second', shown = .apply label [first', second'] ∧
      canonArgument (canonicalOf locatedRepBlock) first' = first ∧
      canonArgument (canonicalOf locatedRepBlock) second' = second := by
  cases shown with
  | apply label' arguments =>
      by_cases isRestrict : label' = locatedRepBlock.restrict
      · subst isRestrict
        rw [recanon_apply_restrict] at read
        simp only [Pattern.apply.injEq] at read
        exact absurd read.1.symm notRestrict
      rw [recanon_apply_other isRestrict (by simp)] at read
      simp only [Pattern.apply.injEq] at read
      obtain ⟨rfl, mapped⟩ := read
      have lengthTwo : arguments.length = 2 := by simpa using congrArg List.length mapped
      obtain ⟨first', second', rfl⟩ := List.length_eq_two.mp lengthTwo
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at mapped
      exact ⟨first', second', rfl, mapped.1, mapped.2⟩
  | collection kind elements rest =>
      rw [recanon_collection] at read
      cases read
  | lambda binder body =>
      rw [recanon_lambda] at read
      cases read
  | bvar index =>
      rw [recanon_bvar] at read
      cases read
  | fvar name' =>
      rw [recanon_fvar] at read
      cases read
  | subst body replacement =>
      rw [recanon_subst] at read
      cases read
  | multiLambda => cases shownTyped

namespace LocComm

variable {free : FreeTypeContext}

theorem inputLabel_mem (capability : Bool) : inputLabel capability ∈ inputs := by
  cases capability <;> simp [inputLabel, inputs]

theorem outputLabel_mem (capability : Bool) : outputLabel capability ∈ outputs := by
  cases capability <;> simp [outputLabel, outputs]

theorem inputLabel_ne_restrict (capability : Bool) : inputLabel capability ≠ "LNu" := by
  cases capability <;> simp [inputLabel]

theorem outputLabel_ne_restrict (capability : Bool) : outputLabel capability ≠ "LNu" := by
  cases capability <;> simp [outputLabel]

/-- **A typed located input**: its place a name, its body a process binding a variable of the sort it receives. -/
theorem input_inv {bound : List TypeExpr} {capability : Bool} {place second : Pattern}
    (typed : HasType locatedCalc free bound (.apply (inputLabel capability) [place, second]) procType) :
    HasType locatedCalc free bound place nameType ∧ ∃ body, second = .lambda none body ∧
      HasType locatedCalc free (.base (sort capability) :: bound) body procType := by
  obtain ⟨placeTyped, inputCase | outputCase⟩ := pair_inv typed
  · obtain ⟨sort', body, listed, rfl, bodyTyped⟩ := inputCase
    refine ⟨placeTyped, body, rfl, ?_⟩
    cases capability
    · have same : sort' = "Name" := by simpa [inputLabel] using listed
      subst same
      exact bodyTyped
    · have same : sort' = "Cap" := by simpa [inputLabel] using listed
      subst same
      exact bodyTyped
  · obtain ⟨sort', listed, -⟩ := outputCase
    cases capability <;> simp [inputLabel] at listed

/-- **A typed located output**: its place a name, its message of the sort it sends. -/
theorem output_inv {bound : List TypeExpr} {capability : Bool} {place message : Pattern}
    (typed : HasType locatedCalc free bound (.apply (outputLabel capability) [place, message]) procType) :
    HasType locatedCalc free bound place nameType ∧
      HasType locatedCalc free bound message (.base (sort capability)) := by
  obtain ⟨placeTyped, inputCase | outputCase⟩ := pair_inv typed
  · obtain ⟨sort', body, listed, -, -⟩ := inputCase
    cases capability <;> simp [outputLabel] at listed
  · obtain ⟨sort', listed, messageTyped⟩ := outputCase
    refine ⟨placeTyped, ?_⟩
    cases capability
    · have same : sort' = "Name" := by simpa [outputLabel] using listed
      subst same
      exact messageTyped
    · have same : sort' = "Cap" := by simpa [outputLabel] using listed
      subst same
      exact messageTyped

/-- **A typed object term of the sort a communication sends is a message.** -/
theorem message_of_typed {bound : List TypeExpr} {capability : Bool} {message : Pattern}
    (typed : HasType locatedCalc free bound message (.base (sort capability)))
    (object : isObjectPattern message = true) : isMessage message = true := by
  cases capability
  · exact message_of_variable (name_variable typed object)
  · exact located_cap_isMessage typed object

/-- **What a communication leaves is a process**, wherever its parts are. -/
theorem result_members {bound : List TypeExpr} (comm : LocComm)
    (members : Members locatedCalc locatedBlock free bound comm.parts) :
    Members locatedCalc locatedBlock free bound comm.result := by
  have inputTyped : HasType locatedCalc free bound
      (.apply (inputLabel comm.capability) [comm.place, .lambda none comm.body]) procType :=
    members _ (by simp [parts, input])
  have outputTyped : HasType locatedCalc free bound
      (.apply (outputLabel comm.capability) [comm.place, comm.message]) procType :=
    members _ (by simp [parts, output])
  obtain ⟨-, body, same, bodyTyped⟩ := input_inv inputTyped
  simp only [Pattern.lambda.injEq, true_and] at same
  subst same
  have messageTyped := (output_inv outputTyped).2
  intro element member
  rw [result, List.mem_singleton] at member
  subst member
  rw [← substitute_single_eq_instantiateBVar]
  refine Mettapedia.GSLT.LanguageDef.WellSorted.HasType.substituteBoundOnSupport bodyTyped _
    fun index type _ lookup => ?_
  cases index with
  | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at lookup
      subst lookup
      exact messageTyped
  | succ index => exact HasType.bvar (by simpa using lookup)

theorem result_objects (comm : LocComm) (objects : ∀ part ∈ comm.parts, isObjectPattern part = true) :
    ∀ element ∈ comm.result, isObjectPattern element = true := by
  have inputObject := objects comm.input (by simp [parts])
  have outputObject := objects comm.output (by simp [parts])
  simp only [input, output, isObjectPattern, isObjectPatternList, Bool.and_eq_true, Bool.and_true]
    at inputObject outputObject
  intro element member
  rw [result, List.mem_singleton] at member
  subst member
  rw [← substitute_single_eq_instantiateBVar]
  refine isObject_substitute _ (fun index => ?_) inputObject.2
  cases index with
  | zero => exact outputObject.2
  | succ => rfl

/-- **What a communication leaves uses only the variables of its parts.** -/
theorem freeIn_result (comm : LocComm) {index : Nat} {element : Pattern} (member : element ∈ comm.result)
    (free : FreeIn index element) : ∃ part ∈ comm.parts, FreeIn index part := by
  rw [result, List.mem_singleton] at member
  subst member
  rcases freeIn_instantiate free with inBody | inMessage
  · exact ⟨comm.input, by simp [parts], by
      unfold input
      exact freeIn_apply.mpr ⟨.lambda none comm.body, by simp, freeIn_lambda.mpr inBody⟩⟩
  · exact ⟨comm.output, by simp [parts], by
      unfold output
      exact freeIn_apply.mpr ⟨comm.message, by simp, inMessage⟩⟩

/-- **Components read alike to the canonical forms of a communication's parts are a communication**, its body
equivalent to the original one, so that what it leaves is equivalent too. -/
theorem alike {bound : List TypeExpr} (context : BaseContext free bound) (comm : LocComm) (shown : List Pattern)
    (partsMembers : Members locatedCalc locatedBlock free bound comm.parts)
    (partsObjects : ∀ part ∈ comm.parts, isObjectPattern part = true)
    (shownMembers : Members locatedCalc locatedBlock free bound shown)
    (shownObjects : ∀ part ∈ shown, isObjectPattern part = true)
    (related : List.Forall₂ (fun part original => AlikeR locatedRepBlock part (canonR locatedRepBlock original))
      shown comm.parts) :
    ∃ comm' : LocComm, comm'.parts = shown ∧
      List.Forall₂ (EquationEquiv (engineBasePremises RelationEnv.empty) locatedCalc) comm'.result comm.result := by
  obtain ⟨capability, place, body, message⟩ := comm
  simp only [parts, input, output] at partsMembers partsObjects related
  cases related with
  | cons inputAlike rest =>
  cases rest with
  | cons outputAlike last =>
  cases last
  rename_i inputShown outputShown
  have inputTyped := partsMembers (.apply (inputLabel capability) [place, .lambda none body]) (by simp)
  have outputTyped := partsMembers (.apply (outputLabel capability) [place, message]) (by simp)
  have inputObject := partsObjects (.apply (inputLabel capability) [place, .lambda none body]) (by simp)
  have outputObject := partsObjects (.apply (outputLabel capability) [place, message]) (by simp)
  simp only [isObjectPattern, isObjectPatternList, Bool.and_eq_true, Bool.and_true] at inputObject outputObject
  obtain ⟨placeTyped, body₀, same, bodyTyped⟩ := input_inv inputTyped
  simp only [Pattern.lambda.injEq, true_and] at same
  subst same
  have messageTyped := (output_inv outputTyped).2
  have placeVar := name_variable placeTyped inputObject.1
  have bodyObject : isObjectPattern body = true := inputObject.2
  have messageObject : isObjectPattern message = true := outputObject.2
  have messageIs := message_of_typed messageTyped messageObject
  -- the exposed input
  have inputCanon : canonR locatedRepBlock (.apply (inputLabel capability) [place, .lambda none body]) =
      .apply (inputLabel capability) [place, .lambda none (canonR locatedRepBlock body)] := by
    rw [canonR, canonP_input (inputLabel_mem capability) placeVar bodyObject]
    rfl
  have inputRead := recanon_eq_of_alike inputAlike
  rw [inputCanon, recanon_input (inputLabel_mem capability) placeVar] at inputRead
  have inputShownTyped := shownMembers inputShown (by simp)
  have inputShownObject := shownObjects inputShown (by simp)
  obtain ⟨first', second', rfl, firstIs, secondIs⟩ :=
    shown_pair inputShownTyped (inputLabel_ne_restrict capability) inputRead
  obtain ⟨firstTyped, body', rfl, body'Typed⟩ := input_inv inputShownTyped
  simp only [isObjectPattern, isObjectPatternList, Bool.and_eq_true, Bool.and_true] at inputShownObject
  rw [canonArgument_variable (name_variable firstTyped inputShownObject.1)] at firstIs
  subst first'
  simp only [canonArgument, Pattern.lambda.injEq, true_and] at secondIs
  -- the exposed output
  have outputCanon : canonR locatedRepBlock (.apply (outputLabel capability) [place, message]) =
      .apply (outputLabel capability) [place, message] := by
    rw [canonR, canonP_output (outputLabel_mem capability) placeVar messageIs]
    rfl
  have outputRead := recanon_eq_of_alike outputAlike
  rw [outputCanon, recanon_output (outputLabel_mem capability) placeVar messageIs] at outputRead
  have outputShownTyped := shownMembers outputShown (by simp)
  have outputShownObject := shownObjects outputShown (by simp)
  obtain ⟨first'', message', rfl, firstIs', messageIs'⟩ :=
    shown_pair outputShownTyped (outputLabel_ne_restrict capability) outputRead
  obtain ⟨firstTyped', message'Typed⟩ := output_inv outputShownTyped
  simp only [isObjectPattern, isObjectPatternList, Bool.and_eq_true, Bool.and_true] at outputShownObject
  rw [canonArgument_variable (name_variable firstTyped' outputShownObject.1)] at firstIs'
  subst first''
  rw [canonArgument_message (message_of_typed message'Typed outputShownObject.2)] at messageIs'
  subst message'
  refine ⟨⟨capability, place, body', message⟩, rfl, ?_⟩
  -- the bodies are equivalent, and stay so once the message is received
  have body'Object : isObjectPattern body' = true := inputShownObject.2
  have bodyContext := context.cons (sort capability)
  have toCanonical := (canonicalOf_sound (block := locatedRepBlock) bodyContext body'Typed).2.toEquationEquiv
  obtain ⟨canonRTyped, toCanonR⟩ := canonR_sound (block := locatedRepBlock) bodyContext bodyTyped
  have canonRCanonical := (canonicalOf_sound (block := locatedRepBlock) bodyContext canonRTyped).2.toEquationEquiv
  rw [secondIs] at toCanonical
  have chain : EquationEquiv (engineBasePremises RelationEnv.empty) locatedCalc body' body :=
    .trans _ _ _ toCanonical (.trans _ _ _ (.symm _ _ canonRCanonical) (.symm _ _ toCanonR.toEquationEquiv))
  exact .cons (sortedEquiv_instantiate_replication (block := locatedRepBlock) context message'Typed outputShownObject.2
    body'Typed bodyTyped body'Object bodyObject chain) .nil

end LocComm

/-- **Entering, leaving, opening and communication are the located calculus's reactions**, in the replication
theory's sense: flat reactions of located atoms beside the rest of a block. -/
def locatedCommReactions : ReplicationReactions locatedCalc locatedRepBlock LocStep where
  Redex := LocReaction
  parts := LocReaction.parts
  result := LocReaction.result
  rename relabel redex := redex.relabel relabel
  parts_rename := LocReaction.parts_relabel
  result_rename := LocReaction.result_relabel
  canonicalAtoms redex part member object binds := by
    cases redex with
    | marker redex => exact LocRedex.canonicalAtoms redex part member
    | comm communication =>
        simp only [LocReaction.parts, LocComm.parts, LocComm.input, LocComm.output, List.mem_cons, List.not_mem_nil,
          or_false] at member
        rcases member with rfl | rfl <;> exact canonP_two _ _ _
  plain redex part member object binds := by
    cases redex with
    | marker redex => exact LocRedex.plain redex part member
    | comm communication =>
        simp only [LocReaction.parts, LocComm.parts, LocComm.input, LocComm.output, List.mem_cons, List.not_mem_nil,
          or_false] at member
        rcases member with rfl | rfl <;> exact isReplicated_canonR_two _ _ _
  arity := 3
  arity_le redex := by
    cases redex with
    | marker redex => exact LocRedex.arity_le redex
    | comm communication => simp [LocReaction.parts, LocComm.parts]
  result_members redex members := by
    cases redex with
    | marker redex => exact LocRedex.result_members redex members
    | comm communication => exact LocComm.result_members communication members
  result_objects redex objects := by
    cases redex with
    | marker redex => exact LocRedex.result_objects redex objects
    | comm communication => exact LocComm.result_objects communication objects
  freeIn_result redex _ _ member free := by
    cases redex with
    | marker redex => exact LocRedex.freeIn_result redex member free
    | comm communication => exact LocComm.freeIn_result communication member free
  alike context redex shown members objects shownMembers shownObjects related := by
    cases redex with
    | marker redex =>
        obtain ⟨redex', same, results⟩ :=
          LocRedex.alike context redex shown members objects shownMembers shownObjects related
        exact ⟨.marker redex', same, results⟩
    | comm communication =>
        obtain ⟨comm', same, results⟩ :=
          LocComm.alike context communication shown members objects shownMembers shownObjects related
        exact ⟨.comm comm', same, results⟩
  react redex _ _ permutation _ _ := ⟨_, .react permutation, .refl _⟩
  restrict stepped := .restrict stepped

end Mettapedia.Languages.ProcessCalculi.Ambient.Steps
