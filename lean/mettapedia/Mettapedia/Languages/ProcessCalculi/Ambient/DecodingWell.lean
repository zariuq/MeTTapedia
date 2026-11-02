import Mettapedia.Languages.ProcessCalculi.Ambient.DecodingSettle

/-!
# Well-located blocks

The located form of an ambient process at a place is a block rooted there, shaped like a tree of ambients
(`WellLocated`):

- every component is a marker, a capability, a prefix by a capability term, an input, an output or a replication;
- every component sits at the place or at one of the block's **locations**, the restrictions some marker places an
  ambient at, and every location has one marker;
- a name position holds a variable that is no location, and a message's variables are no locations: places and
  names never mix;
- a capability's continuation, a prefix's continuation and a replication's argument are well-located blocks at the
  component's place, and an input's body is one at that place under the input's binder (`underName`).

Locations outside a block are given (`isLoc`); inside, a restriction is a location when a marker places an ambient at it
(`insideLoc`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Decoding

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (Prenex decompose)
open Mettapedia.Languages.ProcessCalculi.Ambient.Located (locatedBlock)

/-- Whether a restriction of a block is a location: some marker places an ambient at it. -/
def Marked (components : List Pattern) (index : Nat) : Prop :=
  ∃ component ∈ components, childOf component = some (.bvar index)

/-- **How locations are read inside a block**: one of its restrictions when it is marked, an outer variable as
outside. -/
def insideLoc (isLoc : Pattern → Prop) (count : Nat) (components : List Pattern) : Pattern → Prop
  | .bvar index => if index < count then Marked components index else isLoc (.bvar (index - count))
  | .fvar name => isLoc (.fvar name)
  | _ => False

/-- Locations under one more binder that is a name. -/
def underName (isLoc : Pattern → Prop) : Pattern → Prop
  | .bvar 0 => False
  | .bvar (index + 1) => isLoc (.bvar index)
  | .fvar name => isLoc (.fvar name)
  | _ => False

/-- The kinds of a block's components: markers of a variable location, opened or not, capabilities, prefixes by a
capability term, inputs over an abstraction, outputs, replications. -/
inductive ComponentKind (count : Nat) : Pattern → Prop
  | marker {label : String} {parent name : Pattern} {index : Nat} : label ∈ markers → index < count →
      ComponentKind count (.apply label [parent, .bvar index, name])
  | capability {label : String} {place name continuation : Pattern} : label ∈ capabilities →
      ComponentKind count (.apply label [place, name, continuation])
  | replication {argument : Pattern} : ComponentKind count (.apply "LRep" [argument])
  | cap {place message continuation : Pattern} : ComponentKind count (.apply "LCap" [place, message, continuation])
  | input {label : String} {place : Pattern} {binder : Option String} {body : Pattern} : label ∈ inputs →
      ComponentKind count (.apply label [place, .lambda binder body])
  | output {label : String} {place message : Pattern} : label ∈ outputs →
      ComponentKind count (.apply label [place, message])

/-- The name a component holds: a marker's ambient name, a capability's name. -/
def nameOf : Pattern → Option Pattern
  | .apply label [_, second, third] =>
      if label ∈ markers then some third else if label ∈ capabilities then some second else none
  | _ => none

/-- The message a component holds: a prefix's capability term, an output's message. -/
def messageOf : Pattern → Option Pattern
  | .apply label [_, second, _] => if label = "LCap" then some second else none
  | .apply label [_, second] => if label ∈ outputs then some second else none
  | _ => none

/-- The variables of a message. -/
def messageVariables : Pattern → List Pattern
  | .bvar index => [.bvar index]
  | .fvar name => [.fvar name]
  | .apply _ [name] => messageVariables name
  | .apply _ [first, second] => messageVariables first ++ messageVariables second
  | _ => []

/-- **The locations of a block nest**: a depth on its restrictions grows from the place of every marker sitting at a
restriction to the restriction it places its ambient at, so no ambient sits inside itself. -/
def Nested (count : Nat) (components : List Pattern) : Prop :=
  ∃ depth : Nat → Nat, ∀ component ∈ components, ∀ index child, index < count → child < count →
    placeAt component = some (.bvar index) → childOf component = some (.bvar child) → depth index < depth child

/-- **A well-located block at a place.** -/
inductive WellLocated : (Pattern → Prop) → Pattern → Prenex → Prop
  | intro {isLoc : Pattern → Prop} {place : Pattern} {count : Nat} {components : List Pattern} :
      isLoc place →
      (∀ component ∈ components, ComponentKind count component) →
      (∀ component ∈ components, ∀ at', placeAt component = some at' →
        at' = liftBVars 0 count place ∨ ∃ index < count, at' = .bvar index ∧ Marked components index) →
      (∀ index, (components.filter fun component => childOf component == some (.bvar index)).length ≤ 1) →
      (∀ component ∈ components, ∀ name, nameOf component = some name →
        isVariable name = true ∧ ¬ insideLoc isLoc count components name) →
      (∀ component ∈ components, ∀ label at' name continuation, component = .apply label [at', name, continuation] →
        label ∈ capabilities → WellLocated (insideLoc isLoc count components) at' (decompose locatedBlock continuation)) →
      (∀ component ∈ components, ∀ argument at', component = .apply "LRep" [argument] → placeAt component = some at' →
        WellLocated (insideLoc isLoc count components) at' (decompose locatedBlock argument)) →
      (∀ component ∈ components, ∀ argument, component = .apply "LRep" [argument] → (placeAt component).isSome = true) →
      Nested count components →
      (∀ component ∈ components, ∀ message, messageOf component = some message →
        isMessage message = true ∧ ∀ name ∈ messageVariables message, ¬ insideLoc isLoc count components name) →
      (∀ component ∈ components, ∀ at' message continuation, component = .apply "LCap" [at', message, continuation] →
        WellLocated (insideLoc isLoc count components) at' (decompose locatedBlock continuation)) →
      (∀ component ∈ components, ∀ label at' binder body, component = .apply label [at', .lambda binder body] →
        label ∈ inputs →
        WellLocated (underName (insideLoc isLoc count components)) (liftBVars 0 1 at') (decompose locatedBlock body)) →
      WellLocated isLoc place ⟨count, components⟩

namespace WellLocated

variable {isLoc : Pattern → Prop} {place : Pattern} {form : Prenex}

theorem placeIsLoc (well : WellLocated isLoc place form) : isLoc place := by
  cases well with
  | intro placeLoc _ _ _ _ _ _ _ _ _ _ _ => exact placeLoc

theorem kinds (well : WellLocated isLoc place form) : ∀ component ∈ form.components, ComponentKind form.count component := by
  cases well with
  | intro _ kinds _ _ _ _ _ _ _ _ _ _ => exact kinds

theorem placed (well : WellLocated isLoc place form) : ∀ component ∈ form.components, ∀ at', placeAt component = some at' →
    at' = liftBVars 0 form.count place ∨ ∃ index < form.count, at' = .bvar index ∧ Marked form.components index := by
  cases well with
  | intro _ _ placed _ _ _ _ _ _ _ _ _ => exact placed

theorem unique (well : WellLocated isLoc place form) : ∀ index,
    (form.components.filter fun component => childOf component == some (.bvar index)).length ≤ 1 := by
  cases well with
  | intro _ _ _ unique _ _ _ _ _ _ _ _ => exact unique

theorem names (well : WellLocated isLoc place form) : ∀ component ∈ form.components, ∀ name,
    nameOf component = some name → isVariable name = true ∧ ¬ insideLoc isLoc form.count form.components name := by
  cases well with
  | intro _ _ _ _ names _ _ _ _ _ _ _ => exact names

theorem repsPlaced (well : WellLocated isLoc place form) : ∀ component ∈ form.components, ∀ argument,
    component = .apply "LRep" [argument] → (placeAt component).isSome = true := by
  cases well with
  | intro _ _ _ _ _ _ _ repsPlaced _ _ _ _ => exact repsPlaced

theorem nested (well : WellLocated isLoc place form) : Nested form.count form.components := by
  cases well with
  | intro _ _ _ _ _ _ _ _ nested _ _ _ => exact nested

theorem messages (well : WellLocated isLoc place form) : ∀ component ∈ form.components, ∀ message,
    messageOf component = some message → isMessage message = true ∧
      ∀ name ∈ messageVariables message, ¬ insideLoc isLoc form.count form.components name := by
  cases well with
  | intro _ _ _ _ _ _ _ _ _ messages _ _ => exact messages

theorem capConts (well : WellLocated isLoc place form) : ∀ component ∈ form.components, ∀ at' message continuation,
    component = .apply "LCap" [at', message, continuation] →
    WellLocated (insideLoc isLoc form.count form.components) at' (decompose locatedBlock continuation) := by
  cases well with
  | intro _ _ _ _ _ _ _ _ _ _ capConts _ => exact capConts

theorem bodies (well : WellLocated isLoc place form) : ∀ component ∈ form.components, ∀ label at' binder body,
    component = .apply label [at', .lambda binder body] → label ∈ inputs →
    WellLocated (underName (insideLoc isLoc form.count form.components)) (liftBVars 0 1 at')
      (decompose locatedBlock body) := by
  cases well with
  | intro _ _ _ _ _ _ _ _ _ _ _ bodies => exact bodies

/-- **A well-located block is rooted at its place.** -/
theorem rooted (well : WellLocated isLoc place form) : Rooted place form := by
  refine ⟨fun component member at' found => ?_, fun component member child isChild => ?_⟩
  · rcases well.placed component member at' found with same | ⟨index, below, same, -⟩
    · exact .inl same
    · exact .inr ⟨index, below, same⟩
  · cases well.kinds component member with
    | marker isMarker below => simp [childOf, isMarker] at isChild; exact ⟨_, below, isChild.symm⟩
    | capability listed =>
        simp only [childOf] at isChild
        split_ifs at isChild with isMarker
        · exact absurd listed (not_capability_of_marker isMarker)
    | replication => simp [childOf] at isChild
    | cap => simp [childOf, markers] at isChild
    | input => simp [childOf] at isChild
    | output => simp [childOf] at isChild

end WellLocated

/-! ## Renaming a well-located block -/

open Mettapedia.OSLF.MeTTaIL.CanonicalBags (liftIndex)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (rename rename_bvar rename_fvar rename_apply rename_comp
  liftBVars_eq_rename shiftAbove decompose_renameOuter rename_injective liftIndex_injective)

/-- Locations are read only off variables. -/
def LocVariables (isLoc : Pattern → Prop) : Prop := ∀ pattern, isLoc pattern → isVariable pattern = true

theorem nameOf_rename (relabel : Nat → Nat) (component : Pattern) :
    nameOf (rename relabel component) = (nameOf component).map (rename relabel) := by
  cases component with
  | apply label arguments =>
      match arguments with
      | [_, _, _] =>
          simp only [rename_apply, List.map_cons, List.map_nil, nameOf]
          split_ifs <;> rfl
      | [] => simp [rename_apply, nameOf]
      | [_] => simp [rename_apply, nameOf]
      | [_, _] => simp [rename_apply, nameOf]
      | _ :: _ :: _ :: _ :: _ => simp [rename_apply, nameOf]
  | _ => simp [rename_bvar, rename_fvar, Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_lambda,
      Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_multiLambda,
      Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_subst,
      Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_collection, nameOf]

theorem marked_rename {count : Nat} {relabel : Nat → Nat} {components : List Pattern} {index : Nat}
    (below : index < count) :
    Marked (components.map (rename (liftIndex count relabel))) index ↔ Marked components index := by
  constructor
  · rintro ⟨component, member, isChild⟩
    obtain ⟨original, inComponents, rfl⟩ := List.mem_map.mp member
    rw [childOf_rename] at isChild
    cases found : childOf original with
    | none => rw [found] at isChild; cases isChild
    | some child =>
        rw [found, Option.map_some, Option.some.injEq] at isChild
        refine ⟨original, inComponents, ?_⟩
        rw [found]
        cases child with
        | bvar other =>
            simp only [rename_bvar, Pattern.bvar.injEq, liftIndex] at isChild
            split_ifs at isChild with otherBelow
            · rw [isChild]
            · omega
        | _ => simp [rename_fvar, rename_apply, Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_lambda,
            Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_multiLambda,
            Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_subst,
            Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_collection] at isChild
  · rintro ⟨component, member, isChild⟩
    refine ⟨rename (liftIndex count relabel) component, List.mem_map.mpr ⟨component, member, rfl⟩, ?_⟩
    rw [childOf_rename, isChild, Option.map_some, rename_bvar]
    simp [liftIndex, below]

theorem insideLoc_locVariables (isLoc : Pattern → Prop) (count : Nat) (components : List Pattern) :
    LocVariables (insideLoc isLoc count components) := by
  intro pattern isLocation
  cases pattern <;> simp_all [insideLoc, isVariable]

/-- Locations inside a renamed block are the renamed locations. -/
theorem insideLoc_rename {relabel : Nat → Nat} {isLoc isLoc' : Pattern → Prop}
    (compat : ∀ pattern, isVariable pattern = true → (isLoc' (rename relabel pattern) ↔ isLoc pattern))
    (count : Nat) (components : List Pattern) (pattern : Pattern) (isVar : isVariable pattern = true) :
    insideLoc isLoc' count (components.map (rename (liftIndex count relabel)))
        (rename (liftIndex count relabel) pattern) ↔ insideLoc isLoc count components pattern := by
  cases pattern with
  | bvar index =>
      simp only [rename_bvar, insideLoc, liftIndex]
      by_cases below : index < count
      · simp only [below, if_true]
        exact marked_rename below
      · have notBelow : ¬ relabel (index - count) + count < count := by omega
        simp only [below, if_false, notBelow]
        have := compat (.bvar (index - count)) rfl
        simpa [rename_bvar, show relabel (index - count) + count - count = relabel (index - count) by omega] using this
  | fvar name =>
      simp only [rename_fvar, insideLoc]
      simpa [rename_fvar] using compat (.fvar name) rfl
  | _ => simp [isVariable] at isVar

theorem rename_liftBVars_place (relabel : Nat → Nat) (count : Nat) (place : Pattern) :
    rename (liftIndex count relabel) (liftBVars 0 count place) = liftBVars 0 count (rename relabel place) := by
  rw [liftBVars_eq_rename, liftBVars_eq_rename, rename_comp, rename_comp]
  congr 1
  funext index
  simp [Function.comp, shiftAbove, liftIndex]

theorem rename_eq_bvar {relabel : Nat → Nat} {pattern : Pattern} {index : Nat}
    (same : rename relabel pattern = .bvar index) : ∃ original, pattern = .bvar original ∧ relabel original = index := by
  cases pattern with
  | bvar original => simp only [rename_bvar, Pattern.bvar.injEq] at same; exact ⟨original, rfl, same⟩
  | _ => simp [rename_fvar, rename_apply, Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_lambda,
      Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_multiLambda,
      Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_subst,
      Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_collection] at same

theorem liftIndex_below {count index target : Nat} {relabel : Nat → Nat}
    (same : liftIndex count relabel index = target) (below : target < count) : index = target := by
  simp only [liftIndex] at same
  split_ifs at same with small
  · exact same
  · omega

theorem underName_locVariables (isLoc : Pattern → Prop) : LocVariables (underName isLoc) := by
  intro pattern isLocation
  cases pattern with
  | bvar index => rfl
  | fvar name => rfl
  | _ => simp [underName] at isLocation

/-- Locations under a name binder, renamed past it. -/
theorem underName_compat {relabel : Nat → Nat} {isLoc isLoc' : Pattern → Prop}
    (compat : ∀ pattern, isVariable pattern = true → (isLoc' (rename relabel pattern) ↔ isLoc pattern)) :
    ∀ pattern, isVariable pattern = true →
      (underName isLoc' (rename (liftIndex 1 relabel) pattern) ↔ underName isLoc pattern) := by
  intro pattern isVar
  cases pattern with
  | bvar index =>
      cases index with
      | zero => simp [rename_bvar, liftIndex, underName]
      | succ index =>
          have moved : liftIndex 1 relabel (index + 1) = relabel index + 1 := by simp [liftIndex]
          simp only [rename_bvar, moved, underName]
          simpa [rename_bvar] using compat (.bvar index) rfl
  | fvar name => simpa [rename_fvar, underName] using compat (.fvar name) rfl
  | _ => simp [isVariable] at isVar

theorem childOf_bvar_of_kind {count : Nat} {component child : Pattern} (kind : ComponentKind count component)
    (isChild : childOf component = some child) : ∃ index < count, child = .bvar index := by
  cases kind with
  | marker isMarker below => simp [childOf, isMarker] at isChild; exact ⟨_, below, isChild.symm⟩
  | capability listed =>
      simp only [childOf] at isChild
      split_ifs at isChild with isMarker
      · exact absurd listed (not_capability_of_marker isMarker)
  | replication => simp [childOf] at isChild
  | cap => simp [childOf, markers] at isChild
  | input => simp [childOf] at isChild
  | output => simp [childOf] at isChild

theorem messageOf_rename (relabel : Nat → Nat) (component : Pattern) :
    messageOf (rename relabel component) = (messageOf component).map (rename relabel) := by
  cases component with
  | apply label arguments =>
      match arguments with
      | [_, _, _] =>
          simp only [rename_apply, List.map_cons, List.map_nil, messageOf]
          split_ifs <;> rfl
      | [_, _] =>
          simp only [rename_apply, List.map_cons, List.map_nil, messageOf]
          split_ifs <;> rfl
      | [] => simp [rename_apply, messageOf]
      | [_] => simp [rename_apply, messageOf]
      | _ :: _ :: _ :: _ :: _ => simp [rename_apply, messageOf]
  | _ => simp [rename_bvar, rename_fvar, Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_lambda,
      Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_multiLambda,
      Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_subst,
      Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_collection, messageOf]

theorem messageVariables_rename (relabel : Nat → Nat) : ∀ message : Pattern,
    messageVariables (rename relabel message) = (messageVariables message).map (rename relabel)
  | .bvar _ => by simp [messageVariables, rename_bvar]
  | .fvar _ => by simp [messageVariables, rename_fvar]
  | .apply _ [] => by simp [messageVariables, rename_apply]
  | .apply _ [name] => by simp [messageVariables, rename_apply, messageVariables_rename relabel name]
  | .apply _ [first, second] => by
      simp [messageVariables, rename_apply, messageVariables_rename relabel first,
        messageVariables_rename relabel second]
  | .apply _ (_ :: _ :: _ :: _) => by simp [messageVariables, rename_apply]
  | .lambda _ _ => by simp [messageVariables, Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_lambda]
  | .multiLambda _ _ _ => by
      simp [messageVariables, Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_multiLambda]
  | .subst _ _ => by simp [messageVariables, Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_subst]
  | .collection _ _ _ => by
      simp [messageVariables, Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_collection]

/-- The variables of a message are variables. -/
theorem isVariable_of_messageVariables : ∀ {message name : Pattern}, name ∈ messageVariables message →
    isVariable name = true
  | .bvar _, _, member => by simp [messageVariables] at member; subst member; rfl
  | .fvar _, _, member => by simp [messageVariables] at member; subst member; rfl
  | .apply _ [], _, member => by simp [messageVariables] at member
  | .apply _ [name], _, member => isVariable_of_messageVariables (message := name) (by simpa [messageVariables] using member)
  | .apply _ [first, second], _, member => by
      simp only [messageVariables, List.mem_append] at member
      rcases member with inFirst | inSecond
      · exact isVariable_of_messageVariables inFirst
      · exact isVariable_of_messageVariables inSecond
  | .apply _ (_ :: _ :: _ :: _), _, member => by simp [messageVariables] at member
  | .lambda _ _, _, member => by simp [messageVariables] at member
  | .multiLambda _ _ _, _, member => by simp [messageVariables] at member
  | .subst _ _, _, member => by simp [messageVariables] at member
  | .collection _ _ _, _, member => by simp [messageVariables] at member

/-- A message renamed apart from renamed locations stays apart from them. -/
theorem messages_rename {relabel : Nat → Nat} {isLoc isLoc' : Pattern → Prop}
    (compat : ∀ pattern, isVariable pattern = true → (isLoc' (rename relabel pattern) ↔ isLoc pattern))
    {message : Pattern} :
    ((∀ name ∈ messageVariables (rename relabel message), ¬ isLoc' name) ↔
      ∀ name ∈ messageVariables message, ¬ isLoc name) := by
  rw [messageVariables_rename]
  constructor
  · intro apart name member inside
    exact apart _ (List.mem_map_of_mem member) ((compat name (isVariable_of_messageVariables member)).mpr inside)
  · intro apart name member inside
    obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp member
    exact apart original inOriginal ((compat original (isVariable_of_messageVariables inOriginal)).mp inside)

/-! ## Nested locations -/

namespace Nested

theorem sublist {count : Nat} {components smaller : List Pattern} (nested : Nested count components)
    (within : ∀ component ∈ smaller, component ∈ components) : Nested count smaller := by
  obtain ⟨depth, grows⟩ := nested
  exact ⟨depth, fun component member => grows component (within component member)⟩

/-- Renaming a block's outside keeps its locations nested. -/
theorem renameOuter {count : Nat} {components : List Pattern} (nested : Nested count components)
    (relabel : Nat → Nat) : Nested count (components.map (rename (liftIndex count relabel))) := by
  obtain ⟨depth, grows⟩ := nested
  refine ⟨depth, fun component member index child below childBelow isPlaced isChild => ?_⟩
  obtain ⟨original, inComponents, rfl⟩ := List.mem_map.mp member
  rw [placeAt_rename] at isPlaced
  rw [childOf_rename] at isChild
  obtain ⟨originalPlace, placeFound, placeIs⟩ := Option.map_eq_some_iff.mp isPlaced
  obtain ⟨originalChild, childFound, childIs⟩ := Option.map_eq_some_iff.mp isChild
  obtain ⟨placeIndex, rfl, placeMoved⟩ := rename_eq_bvar placeIs
  obtain ⟨childIndex, rfl, childMoved⟩ := rename_eq_bvar childIs
  rw [liftIndex_below placeMoved below] at placeFound
  rw [liftIndex_below childMoved childBelow] at childFound
  exact grows original inComponents index child below childBelow placeFound childFound

/-- A block whose outside renamed has nested locations has them. -/
theorem unrename {count : Nat} {components : List Pattern} {relabel : Nat → Nat}
    (nested : Nested count (components.map (rename (liftIndex count relabel)))) : Nested count components := by
  obtain ⟨depth, grows⟩ := nested
  refine ⟨depth, fun component member index child below childBelow isPlaced isChild => ?_⟩
  refine grows _ (List.mem_map.mpr ⟨component, member, rfl⟩) index child below childBelow ?_ ?_
  · rw [placeAt_rename, isPlaced, Option.map_some, rename_bvar]
    simp [liftIndex, below]
  · rw [childOf_rename, isChild, Option.map_some, rename_bvar]
    simp [liftIndex, childBelow]

/-- Blocks side by side keep their locations nested: each keeps its own. -/
theorem par {outer inner : Nat} {first second : List Pattern} (firstNested : Nested outer first)
    (secondNested : Nested inner second) :
    Nested (outer + inner) (first.map (liftBVars 0 inner) ++ second.map (liftBVars inner outer)) := by
  obtain ⟨firstDepth, firstGrows⟩ := firstNested
  obtain ⟨secondDepth, secondGrows⟩ := secondNested
  refine ⟨fun index => if index < inner then secondDepth index else firstDepth (index - inner),
    fun component member index child below childBelow isPlaced isChild => ?_⟩
  rcases List.mem_append.mp member with inFirst | inSecond
  · obtain ⟨original, inComponents, rfl⟩ := List.mem_map.mp inFirst
    rw [liftBVars_eq_rename, placeAt_rename] at isPlaced
    rw [liftBVars_eq_rename, childOf_rename] at isChild
    obtain ⟨originalPlace, placeFound, placeIs⟩ := Option.map_eq_some_iff.mp isPlaced
    obtain ⟨originalChild, childFound, childIs⟩ := Option.map_eq_some_iff.mp isChild
    obtain ⟨placeIndex, rfl, placeMoved⟩ := rename_eq_bvar placeIs
    obtain ⟨childIndex, rfl, childMoved⟩ := rename_eq_bvar childIs
    simp only [shiftAbove, Nat.not_lt_zero, if_false] at placeMoved childMoved
    have grows := firstGrows original inComponents placeIndex childIndex (by omega) (by omega) placeFound childFound
    simp only [show ¬ index < inner by omega, show ¬ child < inner by omega, if_false]
    rw [show index - inner = placeIndex by omega, show child - inner = childIndex by omega]
    exact grows
  · obtain ⟨original, inComponents, rfl⟩ := List.mem_map.mp inSecond
    rw [liftBVars_eq_rename, placeAt_rename] at isPlaced
    rw [liftBVars_eq_rename, childOf_rename] at isChild
    obtain ⟨originalPlace, placeFound, placeIs⟩ := Option.map_eq_some_iff.mp isPlaced
    obtain ⟨originalChild, childFound, childIs⟩ := Option.map_eq_some_iff.mp isChild
    obtain ⟨placeIndex, rfl, placeMoved⟩ := rename_eq_bvar placeIs
    obtain ⟨childIndex, rfl, childMoved⟩ := rename_eq_bvar childIs
    simp only [shiftAbove] at placeMoved childMoved
    split_ifs at placeMoved childMoved with placeSmall childSmall childSmall
    · have grows := secondGrows original inComponents placeIndex childIndex placeSmall childSmall placeFound childFound
      simp only [show index < inner by omega, show child < inner by omega, if_true]
      rw [← placeMoved, ← childMoved]
      exact grows
    all_goals omega

/-- Closing a restriction no marker places an ambient at keeps a block's locations nested. -/
theorem close {count : Nat} {components : List Pattern} (nested : Nested count components)
    (childrenBelow : ∀ component ∈ components, ∀ child, childOf component = some (.bvar child) → child < count) :
    Nested (count + 1) components := by
  obtain ⟨depth, grows⟩ := nested
  refine ⟨fun index => if index < count then depth index + 1 else 0,
    fun component member index child below childBelow isPlaced isChild => ?_⟩
  have childSmall := childrenBelow component member child isChild
  simp only [childSmall, if_true]
  split_ifs with placeSmall
  · exact Nat.succ_lt_succ (grows component member index child placeSmall childSmall isPlaced isChild)
  · exact Nat.succ_pos _

/-- A component sitting at no restriction keeps a block's locations nested. -/
theorem cons_outside {count : Nat} {components : List Pattern} {component : Pattern}
    (nested : Nested count components)
    (outside : ∀ index, placeAt component = some (.bvar index) → count ≤ index) :
    Nested count (component :: components) := by
  obtain ⟨depth, grows⟩ := nested
  refine ⟨depth, fun other member index child below childBelow isPlaced isChild => ?_⟩
  rcases List.mem_cons.mp member with rfl | inComponents
  · exact absurd (outside index isPlaced) (by omega)
  · exact grows other inComponents index child below childBelow isPlaced isChild

end Nested

/-- **A well-located block renamed injectively from outside is well-located**, its locations read through the
renaming. -/
theorem WellLocated.renameOuter {isLoc : Pattern → Prop} {place : Pattern} {form : Prenex}
    (well : WellLocated isLoc place form) :
    ∀ {relabel : Nat → Nat}, Function.Injective relabel → ∀ {isLoc' : Pattern → Prop},
      (∀ pattern, isVariable pattern = true → (isLoc' (rename relabel pattern) ↔ isLoc pattern)) →
      LocVariables isLoc → WellLocated isLoc' (rename relabel place) (form.renameOuter relabel) := by
  induction well with
  | @intro isLoc place count components placeLoc kinds placed unique names caps reps repsPlaced nested messages capConts
      bodies capsIH repsIH capContsIH bodiesIH =>
      intro relabel injective isLoc' compat locVariables
      have lifted := liftIndex_injective injective count
      have compat' := insideLoc_rename (isLoc := isLoc) (isLoc' := isLoc') compat count components
      simp only [Prenex.renameOuter]
      refine .intro ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · exact (compat place (locVariables place placeLoc)).mpr placeLoc
      · intro component member
        obtain ⟨original, inComponents, rfl⟩ := List.mem_map.mp member
        cases kinds original inComponents with
        | marker isMarker below =>
            simp only [rename_apply, List.map_cons, List.map_nil, rename_bvar]
            exact .marker isMarker (by simp [liftIndex, below])
        | capability listed =>
            simp only [rename_apply, List.map_cons, List.map_nil]
            exact .capability listed
        | replication =>
            simp only [rename_apply, List.map_cons, List.map_nil]
            exact .replication
        | cap =>
            simp only [rename_apply, List.map_cons, List.map_nil]
            exact .cap
        | input listed =>
            simp only [rename_apply, List.map_cons, List.map_nil,
              Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_lambda]
            exact .input listed
        | output listed =>
            simp only [rename_apply, List.map_cons, List.map_nil]
            exact .output listed
      · intro component member at' isPlaced
        obtain ⟨original, inComponents, rfl⟩ := List.mem_map.mp member
        rw [placeAt_rename] at isPlaced
        cases found : placeAt original with
        | none => rw [found] at isPlaced; cases isPlaced
        | some originalPlace =>
            rw [found, Option.map_some, Option.some.injEq] at isPlaced
            subst isPlaced
            rcases placed original inComponents originalPlace found with rfl | ⟨index, below, rfl, isMarked⟩
            · exact .inl (rename_liftBVars_place relabel count place)
            · refine .inr ⟨index, below, by simp [rename_bvar, liftIndex, below], (marked_rename below).mpr isMarked⟩
      · intro index
        rw [List.filter_map, List.length_map]
        refine le_trans (le_of_eq ?_) (unique index)
        congr 1
        apply List.filter_congr
        intro component member
        simp only [Function.comp, childOf_rename]
        cases found : childOf component with
        | none => simp
        | some child =>
            simp only [Option.map_some]
            obtain ⟨childIndex, childBelow, rfl⟩ := childOf_bvar_of_kind (kinds component member) found
            simp only [rename_bvar, liftIndex, childBelow, if_true]
      · intro component member name isName
        obtain ⟨original, inComponents, rfl⟩ := List.mem_map.mp member
        rw [nameOf_rename] at isName
        cases found : nameOf original with
        | none => rw [found] at isName; cases isName
        | some originalName =>
            rw [found, Option.map_some, Option.some.injEq] at isName
            subst isName
            obtain ⟨isVar, apart⟩ := names original inComponents originalName found
            exact ⟨by rw [isVariable_rename]; exact isVar, fun inside => apart ((compat' originalName isVar).mp inside)⟩
      · intro component member label at' name continuation isCap listed
        obtain ⟨original, inComponents, rfl⟩ := List.mem_map.mp member
        cases original with
        | apply originalLabel arguments =>
            match arguments, isCap with
            | [originalAt, originalName, originalContinuation], isCap =>
                simp only [rename_apply, List.map_cons, List.map_nil, Pattern.apply.injEq, List.cons.injEq,
                  and_true] at isCap
                obtain ⟨rfl, rfl, rfl, rfl⟩ := isCap
                rw [decompose_renameOuter]
                exact capsIH _ inComponents _ _ _ _ rfl listed lifted compat'
                  (insideLoc_locVariables isLoc count components)
        | _ => simp [rename_bvar, rename_fvar, Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_lambda,
            Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_multiLambda,
            Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_subst,
            Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_collection] at isCap
      · intro component member argument at' isRep isPlaced
        obtain ⟨original, inComponents, rfl⟩ := List.mem_map.mp member
        rw [placeAt_rename] at isPlaced
        cases found : placeAt original with
        | none => rw [found] at isPlaced; cases isPlaced
        | some originalPlace =>
            rw [found, Option.map_some, Option.some.injEq] at isPlaced
            subst isPlaced
            cases original with
            | apply originalLabel arguments =>
                match arguments, isRep with
                | [originalArgument], isRep =>
                    simp only [rename_apply, List.map_cons, List.map_nil, Pattern.apply.injEq, List.cons.injEq,
                      and_true] at isRep
                    obtain ⟨rfl, rfl⟩ := isRep
                    rw [decompose_renameOuter]
                    exact repsIH _ inComponents _ _ rfl found lifted compat'
                      (insideLoc_locVariables isLoc count components)
            | _ => simp [rename_bvar, rename_fvar, Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_lambda,
                Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_multiLambda,
                Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_subst,
                Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_collection] at isRep
      · intro component member argument isRep
        obtain ⟨original, inComponents, rfl⟩ := List.mem_map.mp member
        rw [placeAt_rename]
        cases original with
        | apply originalLabel arguments =>
            match arguments, isRep with
            | [originalArgument], isRep =>
                simp only [rename_apply, List.map_cons, List.map_nil, Pattern.apply.injEq, List.cons.injEq,
                  and_true] at isRep
                obtain ⟨rfl, -⟩ := isRep
                have := repsPlaced _ inComponents originalArgument rfl
                cases found : placeAt (Pattern.apply "LRep" [originalArgument]) with
                | none => rw [found] at this; cases this
                | some at' => rfl
        | _ => simp [rename_bvar, rename_fvar, Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_lambda,
            Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_multiLambda,
            Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_subst,
            Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_collection] at isRep
      · exact nested.renameOuter relabel
      · intro component member message isMsgOf
        obtain ⟨original, inComponents, rfl⟩ := List.mem_map.mp member
        rw [messageOf_rename] at isMsgOf
        cases found : messageOf original with
        | none => rw [found] at isMsgOf; cases isMsgOf
        | some originalMessage =>
            rw [found, Option.map_some, Option.some.injEq] at isMsgOf
            subst isMsgOf
            obtain ⟨isMsg, apart⟩ := messages original inComponents originalMessage found
            exact ⟨by rw [isMessage_rename]; exact isMsg, (messages_rename compat').mpr apart⟩
      · intro component member at' message continuation isCapComponent
        obtain ⟨original, inComponents, rfl⟩ := List.mem_map.mp member
        cases original with
        | apply originalLabel arguments =>
            match arguments, isCapComponent with
            | [originalAt, originalMessage, originalContinuation], isCapComponent =>
                simp only [rename_apply, List.map_cons, List.map_nil, Pattern.apply.injEq, List.cons.injEq,
                  and_true] at isCapComponent
                obtain ⟨rfl, rfl, rfl, rfl⟩ := isCapComponent
                rw [decompose_renameOuter]
                exact capContsIH _ inComponents _ _ _ rfl lifted compat'
                  (insideLoc_locVariables isLoc count components)
        | _ => simp [rename_bvar, rename_fvar, Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_lambda,
            Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_multiLambda,
            Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_subst,
            Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_collection] at isCapComponent
      · intro component member label at' binder body isInput listed
        obtain ⟨original, inComponents, rfl⟩ := List.mem_map.mp member
        cases original with
        | apply originalLabel arguments =>
            match arguments, isInput with
            | [originalAt, originalSecond], isInput =>
                cases originalSecond with
                | lambda originalBinder originalBody =>
                    simp only [rename_apply, List.map_cons, List.map_nil,
                      Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_lambda, Pattern.apply.injEq,
                      List.cons.injEq, Pattern.lambda.injEq, and_true] at isInput
                    obtain ⟨rfl, rfl, rfl, rfl⟩ := isInput
                    rw [decompose_renameOuter, ← rename_liftBVars_place]
                    exact bodiesIH _ inComponents _ _ _ _ rfl listed (liftIndex_injective lifted 1)
                      (underName_compat compat') (underName_locVariables _)
                | _ => simp [rename_apply, rename_bvar, rename_fvar,
                    Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_multiLambda,
                    Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_subst,
                    Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_collection] at isInput
            | _ :: _ :: _ :: _, isInput => simp [rename_apply] at isInput
        | _ => simp [rename_bvar, rename_fvar, Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_lambda,
            Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_multiLambda,
            Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_subst,
            Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_collection] at isInput

/-! ## Blocks side by side -/

theorem ComponentKind.triple_inv {count : Nat} {label : String} {first second third : Pattern}
    (kind : ComponentKind count (.apply label [first, second, third])) :
    (label ∈ markers ∧ ∃ index < count, second = .bvar index) ∨ label ∈ capabilities ∨ label = "LCap" := by
  cases kind with
  | marker isMarker below => exact .inl ⟨isMarker, _, below, rfl⟩
  | capability listed => exact .inr (.inl listed)
  | cap => exact .inr (.inr rfl)

theorem ComponentKind.pair_inv {count : Nat} {label : String} {first second : Pattern}
    (kind : ComponentKind count (.apply label [first, second])) :
    (label ∈ inputs ∧ ∃ binder body, second = .lambda binder body) ∨ label ∈ outputs := by
  cases kind with
  | input listed => exact .inl ⟨listed, _, _, rfl⟩
  | output listed => exact .inr listed

theorem ComponentKind.single_inv {count : Nat} {label : String} {argument : Pattern}
    (kind : ComponentKind count (.apply label [argument])) : label = "LRep" := by
  cases kind; rfl

theorem ComponentKind.apply_inv {count : Nat} {component : Pattern} (kind : ComponentKind count component) :
    ∃ label arguments, component = .apply label arguments ∧
      (arguments.length = 3 ∨ arguments.length = 2 ∨ arguments.length = 1) := by
  cases kind <;> exact ⟨_, _, rfl, by simp⟩

/-- **A block whose injective renaming is well-located is well-located**, its locations read back through the
renaming. -/
theorem WellLocated.unrename {isLoc' : Pattern → Prop} {renamedPlace : Pattern} {renamed : Prenex}
    (well : WellLocated isLoc' renamedPlace renamed) :
    ∀ {relabel : Nat → Nat}, Function.Injective relabel → ∀ {isLoc : Pattern → Prop} {place : Pattern} {form : Prenex},
      (∀ pattern, isVariable pattern = true → (isLoc' (rename relabel pattern) ↔ isLoc pattern)) →
      LocVariables isLoc' → renamedPlace = rename relabel place → renamed = form.renameOuter relabel →
      WellLocated isLoc place form := by
  induction well with
  | @intro isLoc' renamedPlace count renamedComponents placeLoc kinds placed unique names caps reps repsPlaced nested
      messages capConts bodies capsIH repsIH capContsIH bodiesIH =>
      intro relabel injective isLoc place form compat locVariables placeIs formIs
      obtain ⟨formCount, components⟩ := form
      simp only [Prenex.renameOuter, Prenex.mk.injEq] at formIs
      obtain ⟨rfl, rfl⟩ := formIs
      subst placeIs
      have lifted := liftIndex_injective injective count
      have renamedInjective := rename_injective lifted
      have compat' := insideLoc_rename (isLoc := isLoc) (isLoc' := isLoc') compat count components
      have member : ∀ {component}, component ∈ components →
          rename (liftIndex count relabel) component ∈ components.map (rename (liftIndex count relabel)) :=
        fun inComponents => List.mem_map.mpr ⟨_, inComponents, rfl⟩
      refine .intro ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · have isVar := locVariables _ placeLoc
        rw [isVariable_rename] at isVar
        exact (compat place isVar).mp placeLoc
      · intro component inComponents
        have kind := kinds _ (member inComponents)
        cases component with
        | apply label arguments =>
            obtain ⟨label', arguments', same, arity⟩ := ComponentKind.apply_inv kind
            simp only [rename_apply, Pattern.apply.injEq] at same
            obtain ⟨rfl, argumentsIs⟩ := same
            have arityHere : arguments.length = 3 ∨ arguments.length = 2 ∨ arguments.length = 1 := by
              rw [← argumentsIs, List.length_map] at arity; exact arity
            match arguments, arityHere, kind with
            | [parent, child, name], _, kind =>
                simp only [rename_apply, List.map_cons, List.map_nil] at kind
                rcases ComponentKind.triple_inv kind with ⟨isMarker, index, below, isChild⟩ | listed | rfl
                · obtain ⟨original, rfl, mapped⟩ := rename_eq_bvar isChild
                  simp only [liftIndex] at mapped
                  split_ifs at mapped with originalBelow
                  · subst mapped
                    exact .marker isMarker originalBelow
                  · omega
                · exact .capability listed
                · exact .cap
            | [first, second], _, kind =>
                simp only [rename_apply, List.map_cons, List.map_nil] at kind
                rcases ComponentKind.pair_inv kind with ⟨listed, binder, body, isLambda⟩ | listed
                · cases second with
                  | lambda originalBinder originalBody => exact .input listed
                  | _ => simp [rename_bvar, rename_fvar, rename_apply,
                      Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_multiLambda,
                      Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_subst,
                      Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_collection] at isLambda
                · exact .output listed
            | [argument], _, kind =>
                simp only [rename_apply, List.map_cons, List.map_nil] at kind
                obtain rfl := ComponentKind.single_inv kind
                exact .replication
        | _ =>
            obtain ⟨label', arguments', same, -⟩ := ComponentKind.apply_inv kind
            simp [rename_bvar, rename_fvar, Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_lambda,
              Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_multiLambda,
              Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_subst,
              Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_collection] at same
      · intro component inComponents at' isPlaced
        have renamedPlaced := placed _ (member inComponents) (rename (liftIndex count relabel) at')
          (by rw [placeAt_rename, isPlaced, Option.map_some])
        rcases renamedPlaced with same | ⟨index, below, same, isMarked⟩
        · rw [← rename_liftBVars_place] at same
          exact .inl (renamedInjective same)
        · obtain ⟨original, rfl, mapped⟩ := rename_eq_bvar same
          simp only [liftIndex] at mapped
          split_ifs at mapped with originalBelow
          · subst mapped
            exact .inr ⟨original, originalBelow, rfl, (marked_rename originalBelow).mp isMarked⟩
          · omega
      · intro index
        refine le_trans (le_of_eq ?_) (unique index)
        rw [List.filter_map, List.length_map]
        congr 1
        apply List.filter_congr
        intro component inComponents
        simp only [Function.comp, childOf_rename]
        cases found : childOf component with
        | none => simp
        | some child =>
            simp only [Option.map_some]
            have renamedKind := kinds _ (member inComponents)
            have renamedChild : childOf (rename (liftIndex count relabel) component) =
                some (rename (liftIndex count relabel) child) := by rw [childOf_rename, found, Option.map_some]
            obtain ⟨childIndex, childBelow, isIndex⟩ := childOf_bvar_of_kind renamedKind renamedChild
            obtain ⟨original, rfl, mapped⟩ := rename_eq_bvar isIndex
            simp only [liftIndex] at mapped
            split_ifs at mapped with originalBelow
            · subst mapped
              simp [rename_bvar, liftIndex, originalBelow]
            · omega
      · intro component inComponents name isName
        obtain ⟨isVar, apart⟩ := names _ (member inComponents) (rename (liftIndex count relabel) name)
          (by rw [nameOf_rename, isName, Option.map_some])
        rw [isVariable_rename] at isVar
        exact ⟨isVar, fun inside => apart ((compat' name isVar).mpr inside)⟩
      · intro component inComponents label at' name continuation isCap listed
        subst isCap
        have inner := capsIH _ (member inComponents) label (rename (liftIndex count relabel) at')
          (rename (liftIndex count relabel) name) (rename (liftIndex count relabel) continuation)
          (by simp [rename_apply]) listed lifted compat' (insideLoc_locVariables isLoc' count _) rfl
          (decompose_renameOuter _ continuation)
        exact inner
      · intro component inComponents argument at' isRep isPlaced
        subst isRep
        exact repsIH _ (member inComponents) (rename (liftIndex count relabel) argument)
          (rename (liftIndex count relabel) at') (by simp [rename_apply])
          (by rw [placeAt_rename, isPlaced, Option.map_some]) lifted compat'
          (insideLoc_locVariables isLoc' count _) rfl (decompose_renameOuter _ argument)
      · intro component inComponents argument isRep
        subst isRep
        have renamedPlaced := repsPlaced _ (member inComponents) (rename (liftIndex count relabel) argument)
          (by simp [rename_apply])
        rw [placeAt_rename] at renamedPlaced
        cases found : placeAt (Pattern.apply "LRep" [argument]) with
        | none => rw [found] at renamedPlaced; cases renamedPlaced
        | some at' => rfl
      · exact nested.unrename
      · intro component inComponents message isMsgOf
        obtain ⟨isMsg, apart⟩ := messages _ (member inComponents) (rename (liftIndex count relabel) message)
          (by rw [messageOf_rename, isMsgOf, Option.map_some])
        rw [isMessage_rename] at isMsg
        exact ⟨isMsg, (messages_rename compat').mp apart⟩
      · intro component inComponents at' message continuation isCapComponent
        subst isCapComponent
        exact capContsIH _ (member inComponents) (rename (liftIndex count relabel) at')
          (rename (liftIndex count relabel) message) (rename (liftIndex count relabel) continuation)
          (by simp [rename_apply]) lifted compat' (insideLoc_locVariables isLoc' count _) rfl
          (decompose_renameOuter _ continuation)
      · intro component inComponents label at' binder body isInput listed
        subst isInput
        exact bodiesIH _ (member inComponents) label (rename (liftIndex count relabel) at') binder
          (rename (liftIndex 1 (liftIndex count relabel)) body)
          (by simp [rename_apply, Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_lambda]) listed
          (liftIndex_injective lifted 1) (underName_compat compat') (underName_locVariables _)
          (rename_liftBVars_place _ 1 at').symm (decompose_renameOuter _ body)

/-- The restrictions marked in two blocks side by side: those of each, moved where the juxtaposition puts them. -/
theorem marked_par {outer inner : Nat} {first second : List Pattern}
    (firstKinds : ∀ component ∈ first, ComponentKind outer component)
    (secondKinds : ∀ component ∈ second, ComponentKind inner component) (index : Nat) :
    Marked (first.map (liftBVars 0 inner) ++ second.map (liftBVars inner outer)) index ↔
      (inner ≤ index ∧ Marked first (index - inner)) ∨ (index < inner ∧ Marked second index) := by
  constructor
  · rintro ⟨component, member, isChild⟩
    rcases List.mem_append.mp member with inFirst | inSecond
    · obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp inFirst
      rw [liftBVars_eq_rename, childOf_rename] at isChild
      cases found : childOf original with
      | none => rw [found] at isChild; cases isChild
      | some child =>
          rw [found, Option.map_some, Option.some.injEq] at isChild
          obtain ⟨childIndex, below, rfl⟩ := childOf_bvar_of_kind (firstKinds original originalMember) found
          simp only [rename_bvar, shiftAbove, Nat.not_lt_zero, if_false, Pattern.bvar.injEq] at isChild
          subst isChild
          exact .inl ⟨by omega, original, originalMember, by rw [found]; simp⟩
    · obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp inSecond
      rw [liftBVars_eq_rename, childOf_rename] at isChild
      cases found : childOf original with
      | none => rw [found] at isChild; cases isChild
      | some child =>
          rw [found, Option.map_some, Option.some.injEq] at isChild
          obtain ⟨childIndex, below, rfl⟩ := childOf_bvar_of_kind (secondKinds original originalMember) found
          simp only [rename_bvar, shiftAbove, below, if_true, Pattern.bvar.injEq] at isChild
          subst isChild
          exact .inr ⟨below, original, originalMember, found⟩
  · rintro (⟨above, component, member, isChild⟩ | ⟨below, component, member, isChild⟩)
    · refine ⟨liftBVars 0 inner component, List.mem_append_left _ (List.mem_map.mpr ⟨component, member, rfl⟩), ?_⟩
      rw [liftBVars_eq_rename, childOf_rename, isChild, Option.map_some, rename_bvar]
      simp only [shiftAbove, Nat.not_lt_zero, if_false]
      congr 2
      omega
    · refine ⟨liftBVars inner outer component, List.mem_append_right _ (List.mem_map.mpr ⟨component, member, rfl⟩), ?_⟩
      rw [liftBVars_eq_rename, childOf_rename, isChild, Option.map_some, rename_bvar]
      simp [shiftAbove, below]

/-- **One half of blocks side by side**: the components of a well-located block, moved by an injective renaming
into a bigger block that reads its locations alike, are components of a well-located block there. -/
theorem WellLocated.embed {isLoc isLocBig : Pattern → Prop} {place placeBig : Pattern}
    {count total : Nat} {components bigger : List Pattern} {relabel : Nat → Nat}
    (well : WellLocated isLoc place ⟨count, components⟩) (injective : Function.Injective relabel)
    (placeMoved : rename relabel (liftBVars 0 count place) = liftBVars 0 total placeBig ∨
      ∃ index < total, rename relabel (liftBVars 0 count place) = .bvar index ∧ Marked bigger index)
    (inside : ∀ index < count, relabel index < total)
    (markedMoved : ∀ index < count, Marked bigger (relabel index) ↔ Marked components index)
    (locMoved : ∀ pattern, isVariable pattern = true →
      (insideLoc isLocBig total bigger (rename relabel pattern) ↔ insideLoc isLoc count components pattern)) :
    ∀ component ∈ components.map (rename relabel),
      ComponentKind total component ∧
      (∀ at', placeAt component = some at' →
        at' = liftBVars 0 total placeBig ∨ ∃ index < total, at' = .bvar index ∧ Marked bigger index) ∧
      (∀ name, nameOf component = some name → isVariable name = true ∧ ¬ insideLoc isLocBig total bigger name) ∧
      (∀ label at' name continuation, component = .apply label [at', name, continuation] → label ∈ capabilities →
        WellLocated (insideLoc isLocBig total bigger) at' (decompose locatedBlock continuation)) ∧
      (∀ argument at', component = .apply "LRep" [argument] → placeAt component = some at' →
        WellLocated (insideLoc isLocBig total bigger) at' (decompose locatedBlock argument)) ∧
      (∀ argument, component = .apply "LRep" [argument] → (placeAt component).isSome = true) ∧
      (∀ message, messageOf component = some message →
        isMessage message = true ∧ ∀ name ∈ messageVariables message, ¬ insideLoc isLocBig total bigger name) ∧
      (∀ at' message continuation, component = .apply "LCap" [at', message, continuation] →
        WellLocated (insideLoc isLocBig total bigger) at' (decompose locatedBlock continuation)) ∧
      (∀ label at' binder body, component = .apply label [at', .lambda binder body] → label ∈ inputs →
        WellLocated (underName (insideLoc isLocBig total bigger)) (liftBVars 0 1 at') (decompose locatedBlock body)) := by
  cases well with
  | intro placeLoc kinds placed unique names caps reps repsPlaced _ messages capConts bodies =>
      intro component member
      obtain ⟨original, inComponents, rfl⟩ := List.mem_map.mp member
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · cases kinds original inComponents with
        | marker isMarker below =>
            simp only [rename_apply, List.map_cons, List.map_nil, rename_bvar]
            exact .marker isMarker (inside _ below)
        | capability listed =>
            simp only [rename_apply, List.map_cons, List.map_nil]
            exact .capability listed
        | replication =>
            simp only [rename_apply, List.map_cons, List.map_nil]
            exact .replication
        | cap =>
            simp only [rename_apply, List.map_cons, List.map_nil]
            exact .cap
        | input listed =>
            simp only [rename_apply, List.map_cons, List.map_nil,
              Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_lambda]
            exact .input listed
        | output listed =>
            simp only [rename_apply, List.map_cons, List.map_nil]
            exact .output listed
      · intro at' isPlaced
        rw [placeAt_rename] at isPlaced
        cases found : placeAt original with
        | none => rw [found] at isPlaced; cases isPlaced
        | some originalPlace =>
            rw [found, Option.map_some, Option.some.injEq] at isPlaced
            subst isPlaced
            rcases placed original inComponents originalPlace found with rfl | ⟨index, below, rfl, isMarked⟩
            · exact placeMoved
            · exact .inr ⟨relabel index, inside index below, rename_bvar _ _, (markedMoved index below).mpr isMarked⟩
      · intro name isName
        rw [nameOf_rename] at isName
        cases found : nameOf original with
        | none => rw [found] at isName; cases isName
        | some originalName =>
            rw [found, Option.map_some, Option.some.injEq] at isName
            subst isName
            obtain ⟨isVar, apart⟩ := names original inComponents originalName found
            exact ⟨by rw [isVariable_rename]; exact isVar, fun insideLoc => apart ((locMoved originalName isVar).mp
              insideLoc)⟩
      · intro label at' name continuation isCap listed
        cases original with
        | apply originalLabel arguments =>
            match arguments, isCap with
            | [_, _, _], isCap =>
                simp only [rename_apply, List.map_cons, List.map_nil, Pattern.apply.injEq, List.cons.injEq,
                  and_true] at isCap
                obtain ⟨rfl, rfl, rfl, rfl⟩ := isCap
                rw [decompose_renameOuter]
                exact (caps _ inComponents _ _ _ _ rfl listed).renameOuter injective locMoved
                  (insideLoc_locVariables isLoc count components)
        | _ => simp [rename_bvar, rename_fvar, Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_lambda,
            Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_multiLambda,
            Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_subst,
            Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_collection] at isCap
      · intro argument at' isRep isPlaced
        rw [placeAt_rename] at isPlaced
        cases found : placeAt original with
        | none => rw [found] at isPlaced; cases isPlaced
        | some originalPlace =>
            rw [found, Option.map_some, Option.some.injEq] at isPlaced
            subst isPlaced
            cases original with
            | apply originalLabel arguments =>
                match arguments, isRep with
                | [_], isRep =>
                    simp only [rename_apply, List.map_cons, List.map_nil, Pattern.apply.injEq, List.cons.injEq,
                      and_true] at isRep
                    obtain ⟨rfl, rfl⟩ := isRep
                    rw [decompose_renameOuter]
                    exact (reps _ inComponents _ _ rfl found).renameOuter injective locMoved
                      (insideLoc_locVariables isLoc count components)
            | _ => simp [rename_bvar, rename_fvar, Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_lambda,
                Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_multiLambda,
                Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_subst,
                Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_collection] at isRep
      · intro argument isRep
        rw [placeAt_rename]
        cases original with
        | apply originalLabel arguments =>
            match arguments, isRep with
            | [originalArgument], isRep =>
                simp only [rename_apply, List.map_cons, List.map_nil, Pattern.apply.injEq, List.cons.injEq,
                  and_true] at isRep
                obtain ⟨rfl, -⟩ := isRep
                have := repsPlaced _ inComponents originalArgument rfl
                cases found : placeAt (Pattern.apply "LRep" [originalArgument]) with
                | none => rw [found] at this; cases this
                | some at' => rfl
        | _ => simp [rename_bvar, rename_fvar, Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_lambda,
            Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_multiLambda,
            Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_subst,
            Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_collection] at isRep
      · intro message isMsgOf
        rw [messageOf_rename] at isMsgOf
        cases found : messageOf original with
        | none => rw [found] at isMsgOf; cases isMsgOf
        | some originalMessage =>
            rw [found, Option.map_some, Option.some.injEq] at isMsgOf
            subst isMsgOf
            obtain ⟨isMsg, apart⟩ := messages original inComponents originalMessage found
            exact ⟨by rw [isMessage_rename]; exact isMsg, (messages_rename locMoved).mpr apart⟩
      · intro at' message continuation isCapComponent
        cases original with
        | apply originalLabel arguments =>
            match arguments, isCapComponent with
            | [_, _, _], isCapComponent =>
                simp only [rename_apply, List.map_cons, List.map_nil, Pattern.apply.injEq, List.cons.injEq,
                  and_true] at isCapComponent
                obtain ⟨rfl, rfl, rfl, rfl⟩ := isCapComponent
                rw [decompose_renameOuter]
                exact (capConts _ inComponents _ _ _ rfl).renameOuter injective locMoved
                  (insideLoc_locVariables isLoc count components)
        | _ => simp [rename_bvar, rename_fvar, Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_lambda,
            Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_multiLambda,
            Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_subst,
            Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_collection] at isCapComponent
      · intro label at' binder body isInput listed
        cases original with
        | apply originalLabel arguments =>
            match arguments, isInput with
            | [_, originalSecond], isInput =>
                cases originalSecond with
                | lambda originalBinder originalBody =>
                    simp only [rename_apply, List.map_cons, List.map_nil,
                      Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_lambda, Pattern.apply.injEq,
                      List.cons.injEq, Pattern.lambda.injEq, and_true] at isInput
                    obtain ⟨rfl, rfl, rfl, rfl⟩ := isInput
                    rw [decompose_renameOuter, ← rename_liftBVars_place]
                    exact (bodies _ inComponents _ _ _ _ rfl listed).renameOuter (liftIndex_injective injective 1)
                      (underName_compat locMoved) (underName_locVariables _)
                | _ => simp [rename_apply, rename_bvar, rename_fvar,
                    Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_multiLambda,
                    Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_subst,
                    Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_collection] at isInput
            | _ :: _ :: _ :: _, isInput => simp [rename_apply] at isInput
        | _ => simp [rename_bvar, rename_fvar, Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_lambda,
            Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_multiLambda,
            Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_subst,
            Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_collection] at isInput

/-- Locations read through blocks side by side. -/
theorem insideLoc_par {isLoc : Pattern → Prop} {outer inner : Nat} {first second : List Pattern}
    (firstKinds : ∀ component ∈ first, ComponentKind outer component)
    (secondKinds : ∀ component ∈ second, ComponentKind inner component) :
    (∀ pattern, isVariable pattern = true →
      (insideLoc isLoc (outer + inner) (first.map (liftBVars 0 inner) ++ second.map (liftBVars inner outer))
        (rename (shiftAbove 0 inner) pattern) ↔ insideLoc isLoc outer first pattern)) ∧
    (∀ pattern, isVariable pattern = true →
      (insideLoc isLoc (outer + inner) (first.map (liftBVars 0 inner) ++ second.map (liftBVars inner outer))
        (rename (shiftAbove inner outer) pattern) ↔ insideLoc isLoc inner second pattern)) := by
  have marked := marked_par (first := first) (second := second) firstKinds secondKinds
  constructor
  · intro pattern isVar
    cases pattern with
    | bvar index =>
        simp only [rename_bvar, shiftAbove, Nat.not_lt_zero, if_false, insideLoc]
        by_cases below : index < outer
        · simp only [show index + inner < outer + inner by omega, below, if_true, marked]
          constructor
          · rintro (⟨-, isMarked⟩ | ⟨tooSmall, -⟩)
            · simpa using isMarked
            · omega
          · intro isMarked
            exact .inl ⟨by omega, by simpa using isMarked⟩
        · simp only [show ¬ index + inner < outer + inner by omega, below, if_false]
          rw [show index + inner - (outer + inner) = index - outer by omega]
    | fvar name => simp [rename_fvar, insideLoc]
    | _ => simp [isVariable] at isVar
  · intro pattern isVar
    cases pattern with
    | bvar index =>
        simp only [rename_bvar, shiftAbove, insideLoc]
        by_cases below : index < inner
        · simp only [below, if_true, show index < outer + inner by omega, marked]
          constructor
          · rintro (⟨tooBig, -⟩ | ⟨-, isMarked⟩)
            · omega
            · exact isMarked
          · intro isMarked
            exact .inr ⟨trivial, isMarked⟩
        · simp only [below, if_false, show ¬ index + outer < outer + inner by omega]
          rw [show index + outer - (outer + inner) = index - inner by omega]
    | fvar name => simp [rename_fvar, insideLoc]
    | _ => simp [isVariable] at isVar

/-- **Well-located blocks side by side at one place are well-located.** -/
theorem WellLocated.par {isLoc : Pattern → Prop} {place : Pattern} {first second : Prenex}
    (firstWell : WellLocated isLoc place first) (secondWell : WellLocated isLoc place second) :
    WellLocated isLoc place (first.par second) := by
  obtain ⟨outer, firstComponents⟩ := first
  obtain ⟨inner, secondComponents⟩ := second
  have firstKinds := firstWell.kinds
  have secondKinds := secondWell.kinds
  have firstUnique := firstWell.unique
  have secondUnique := secondWell.unique
  simp only at firstKinds secondKinds firstUnique secondUnique
  obtain ⟨firstLoc, secondLoc⟩ := insideLoc_par (isLoc := isLoc) firstKinds secondKinds
  have marked := marked_par (first := firstComponents) (second := secondComponents) firstKinds secondKinds
  have liftIs : ∀ cutoff shift, liftBVars cutoff shift = rename (shiftAbove cutoff shift) :=
    fun cutoff shift => funext fun pattern => liftBVars_eq_rename cutoff shift pattern
  have firstHalf := WellLocated.embed (total := outer + inner)
    (bigger := firstComponents.map (liftBVars 0 inner) ++ secondComponents.map (liftBVars inner outer))
    firstWell (shiftAbove_injective 0 inner)
    (.inl (by rw [← liftIs, liftBVars_par_outer])) (fun index below => by simp [shiftAbove]; omega)
    (fun index below => by
      simp only [shiftAbove, Nat.not_lt_zero, if_false, marked]
      constructor
      · rintro (⟨-, isMarked⟩ | ⟨tooSmall, -⟩)
        · simpa using isMarked
        · omega
      · intro isMarked
        exact .inl ⟨by omega, by simpa using isMarked⟩) firstLoc
  have secondHalf := WellLocated.embed (total := outer + inner)
    (bigger := firstComponents.map (liftBVars 0 inner) ++ secondComponents.map (liftBVars inner outer))
    secondWell (shiftAbove_injective inner outer)
    (.inl (by rw [← liftIs, liftBVars_par_inner])) (fun index below => by simp [shiftAbove, below]; omega)
    (fun index below => by
      simp only [shiftAbove, below, if_true, marked]
      constructor
      · rintro (⟨tooBig, -⟩ | ⟨-, isMarked⟩)
        · omega
        · exact isMarked
      · intro isMarked
        exact .inr ⟨trivial, isMarked⟩) secondLoc
  simp only [← liftIs] at firstHalf secondHalf
  have both : ∀ component ∈ firstComponents.map (liftBVars 0 inner) ++ secondComponents.map (liftBVars inner outer),
      _ := fun component member => (List.mem_append.mp member).elim (firstHalf component) (secondHalf component)
  simp only [Prenex.par]
  refine .intro firstWell.placeIsLoc (fun component member => (both component member).1)
    (fun component member => (both component member).2.1) ?_ (fun component member => (both component member).2.2.1)
    (fun component member => (both component member).2.2.2.1)
    (fun component member => (both component member).2.2.2.2.1)
    (fun component member => (both component member).2.2.2.2.2.1)
    (Nested.par firstWell.nested secondWell.nested) (fun component member => (both component member).2.2.2.2.2.2.1)
    (fun component member => (both component member).2.2.2.2.2.2.2.1)
    (fun component member => (both component member).2.2.2.2.2.2.2.2)
  intro index
  rw [List.filter_append, List.length_append]
  have firstPart : (firstComponents.map (liftBVars 0 inner)).filter
      (fun component => childOf component == some (.bvar index)) =
      if inner ≤ index then (firstComponents.filter fun component => childOf component == some (.bvar (index - inner))).map
        (liftBVars 0 inner) else [] := by
    rw [List.filter_map]
    split_ifs with above
    · congr 1
      apply List.filter_congr
      intro component member
      simp only [Function.comp, liftIs, childOf_rename]
      cases found : childOf component with
      | none => simp
      | some child =>
          obtain ⟨childIndex, below, rfl⟩ := childOf_bvar_of_kind (firstKinds component member) found
          rw [Bool.eq_iff_iff]
          simp only [Option.map_some, rename_bvar, shiftAbove, Nat.not_lt_zero, if_false, beq_iff_eq,
            Option.some.injEq, Pattern.bvar.injEq]
          constructor <;> intro same <;> omega
    · rw [List.filter_eq_nil_iff.mpr]
      · rfl
      intro original originalMember isChild
      simp only [Function.comp, liftIs, childOf_rename, beq_iff_eq] at isChild
      cases found : childOf original with
      | none => rw [found] at isChild; cases isChild
      | some child =>
          rw [found] at isChild
          obtain ⟨childIndex, below, rfl⟩ := childOf_bvar_of_kind (firstKinds original originalMember) found
          simp [rename_bvar, shiftAbove] at isChild
          omega
  have secondPart : (secondComponents.map (liftBVars inner outer)).filter
      (fun component => childOf component == some (.bvar index)) =
      if index < inner then (secondComponents.filter fun component => childOf component == some (.bvar index)).map
        (liftBVars inner outer) else [] := by
    rw [List.filter_map]
    split_ifs with below
    · congr 1
      apply List.filter_congr
      intro component member
      simp only [Function.comp, liftIs, childOf_rename]
      cases found : childOf component with
      | none => simp
      | some child =>
          obtain ⟨childIndex, childBelow, rfl⟩ := childOf_bvar_of_kind (secondKinds component member) found
          simp [rename_bvar, shiftAbove, childBelow]
    · rw [List.filter_eq_nil_iff.mpr]
      · rfl
      intro original originalMember isChild
      simp only [Function.comp, liftIs, childOf_rename, beq_iff_eq] at isChild
      cases found : childOf original with
      | none => rw [found] at isChild; cases isChild
      | some child =>
          rw [found] at isChild
          obtain ⟨childIndex, childBelow, rfl⟩ := childOf_bvar_of_kind (secondKinds original originalMember) found
          simp [rename_bvar, shiftAbove, childBelow] at isChild
          omega
  rw [firstPart, secondPart]
  split_ifs with above below below
  · omega
  · simpa using firstUnique (index - inner)
  · simpa using secondUnique index
  · simp

/-! ## Closing a restriction -/

theorem underName_rename (isLoc : Pattern → Prop) (pattern : Pattern) (isVar : isVariable pattern = true) :
    underName isLoc (rename Nat.succ pattern) ↔ isLoc pattern := by
  cases pattern <;> simp_all [rename_bvar, rename_fvar, underName, isVariable]

theorem marked_ge {count : Nat} {components : List Pattern} (kinds : ∀ component ∈ components,
    ComponentKind count component) {index : Nat} (above : count ≤ index) : ¬ Marked components index := by
  rintro ⟨component, member, isChild⟩
  obtain ⟨childIndex, below, same⟩ := childOf_bvar_of_kind (kinds component member) isChild
  simp only [Pattern.bvar.injEq] at same
  omega

/-- **Closing a name over a well-located block keeps it well-located.** -/
theorem WellLocated.close_name {isLoc : Pattern → Prop} {here : Pattern} {form : Prenex}
    (well : WellLocated (underName isLoc) (Mettapedia.Languages.ProcessCalculi.Ambient.Encoding.shiftName here) form) :
    WellLocated isLoc here form.close := by
  obtain ⟨count, components⟩ := form
  have kinds := well.kinds
  simp only at kinds
  by_cases used : components.any (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.mentions count) = true
  · have closed : (Prenex.mk count components).close = ⟨count + 1, components⟩ := by
      simp [Prenex.close, used, Prenex.restrict]
    rw [closed]
    have half := WellLocated.embed (relabel := id) (total := count + 1) (bigger := components) (placeBig := here)
      (isLocBig := isLoc) well (fun _ _ same => same)
      (.inl (by
        rw [Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_id,
          Mettapedia.Languages.ProcessCalculi.Ambient.Decoding.shiftName_eq, liftBVars_par_outer, Nat.add_comm]))
      (fun index below => by simp; omega) (fun index below => Iff.rfl)
      (fun pattern isVar => by
        rw [Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_id]
        cases pattern with
        | bvar index =>
            simp only [insideLoc]
            by_cases below : index < count
            · simp [below, show index < count + 1 by omega]
            · by_cases equal : index = count
              · subst equal
                simp [marked_ge kinds (Nat.le_refl _), underName]
              · have above : ¬ index < count + 1 := by omega
                obtain ⟨rest, restIs⟩ : ∃ rest, index - count = rest + 1 := ⟨index - count - 1, by omega⟩
                simp only [above, below, if_false, restIs, underName]
                rw [show index - (count + 1) = rest by omega]
        | fvar name => simp [insideLoc, underName]
        | _ => simp [isVariable] at isVar)
    rw [show components.map (rename id) = components from by
      conv_rhs => rw [← List.map_id components]
      exact List.map_congr_left fun component _ => Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_id component]
      at half
    refine .intro ((underName_rename isLoc here ?_).mp well.placeIsLoc) (fun component member => (half component member).1)
      (fun component member => (half component member).2.1) well.unique (fun component member => (half component member).2.2.1)
      (fun component member => (half component member).2.2.2.1)
      (fun component member => (half component member).2.2.2.2.1)
      (fun component member => (half component member).2.2.2.2.2.1)
      ((show Nested count components from well.nested).close fun component member child isChild => by
        obtain ⟨childIndex, below, same⟩ := childOf_bvar_of_kind (kinds component member) isChild
        simp only [Pattern.bvar.injEq] at same
        change childIndex < count at below
        omega)
      (fun component member => (half component member).2.2.2.2.2.2.1)
      (fun component member => (half component member).2.2.2.2.2.2.2.1)
      (fun component member => (half component member).2.2.2.2.2.2.2.2)
    have := underName_locVariables isLoc _ well.placeIsLoc
    rw [Mettapedia.Languages.ProcessCalculi.Ambient.Encoding.shiftName, isVariable_rename] at this
    exact this
  · have unused : components.any (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.mentions count) = false := by
      simpa using used
    have closed : (Prenex.mk count components).close =
        ⟨count, components.map (rename (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.dropIndex count))⟩ := by
      simp [Prenex.close, unused]
    rw [closed]
    exact well.unrename Nat.succ_injective (fun pattern isVar => underName_rename isLoc pattern isVar)
      (underName_locVariables isLoc) rfl (by simp only [Prenex.renameOuter, drop_lift_unused unused])

/-- Locations under one more binder that is a location. -/
def underLocation (isLoc : Pattern → Prop) : Pattern → Prop
  | .bvar 0 => True
  | .bvar (index + 1) => isLoc (.bvar index)
  | .fvar name => isLoc (.fvar name)
  | _ => False

theorem underLocation_locVariables (isLoc : Pattern → Prop) : LocVariables (underLocation isLoc) := by
  intro pattern isLocation
  cases pattern with
  | bvar index => rfl
  | fvar name => rfl
  | _ => simp [underLocation] at isLocation

/-- **Closing an ambient's location over its marker, opened or not, and its content keeps them well-located.** -/
theorem WellLocated.close_marker {markerLabel : String} (isMarker : markerLabel ∈ markers) {isLoc : Pattern → Prop}
    {here name : Pattern} {form : Prenex} (hereLoc : isLoc here)
    (nameVar : isVariable name = true) (nameApart : ¬ underLocation isLoc name)
    (well : WellLocated (underLocation isLoc) (.bvar 0) form) :
    WellLocated isLoc here ((Prenex.atom (.apply markerLabel
      [Mettapedia.Languages.ProcessCalculi.Ambient.Encoding.shiftName here, .bvar 0, name])).par form).close := by
  obtain ⟨count, components⟩ := form
  have kinds := well.kinds
  have unique := well.unique
  simp only at kinds unique
  set marker : Pattern := .apply markerLabel [liftBVars 0 count (Mettapedia.Languages.ProcessCalculi.Ambient.Encoding.shiftName
    here), .bvar count, liftBVars 0 count name] with markerIs
  have markerLifted : liftBVars 0 count (.apply markerLabel
      [Mettapedia.Languages.ProcessCalculi.Ambient.Encoding.shiftName here, .bvar 0, name]) = marker := by
    simp [markerIs, liftBVars, Mettapedia.OSLF.MeTTaIL.Substitution.liftBVarsList_eq_map]
  have componentsSame : components.map (liftBVars count 0) = components := by
    conv_rhs => rw [← List.map_id components]
    exact List.map_congr_left fun component _ => Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero component count
  have parIs : (Prenex.atom (.apply markerLabel [Mettapedia.Languages.ProcessCalculi.Ambient.Encoding.shiftName here,
      .bvar 0, name])).par ⟨count, components⟩ = ⟨count, marker :: components⟩ := by
    simp [Prenex.par, Prenex.atom, markerLifted, componentsSame]
  have used : (marker :: components).any (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.mentions count) = true := by
    simp [markerIs, Mettapedia.GSLT.LanguageDef.RestrictionBlocks.mentions,
      Mettapedia.GSLT.LanguageDef.RestrictionBlocks.mentionsList]
  rw [parIs, show (Prenex.mk count (marker :: components)).close = ⟨count + 1, marker :: components⟩ by
    simp [Prenex.close, used, Prenex.restrict]]
  have markerChild : childOf marker = some (.bvar count) := by simp [markerIs, childOf, isMarker]
  have markedTop : Marked (marker :: components) count := ⟨marker, List.mem_cons_self, markerChild⟩
  have markedBelow : ∀ index < count, (Marked (marker :: components) index ↔ Marked components index) := by
    intro index below
    constructor
    · rintro ⟨component, member, isChild⟩
      rcases List.mem_cons.mp member with rfl | inComponents
      · rw [markerChild] at isChild; simp at isChild; omega
      · exact ⟨component, inComponents, isChild⟩
    · rintro ⟨component, member, isChild⟩
      exact ⟨component, List.mem_cons_of_mem _ member, isChild⟩
  have locIs : ∀ pattern, isVariable pattern = true →
      (insideLoc isLoc (count + 1) (marker :: components) pattern ↔
        insideLoc (underLocation isLoc) count components pattern) := by
    intro pattern isVar
    cases pattern with
    | bvar index =>
        simp only [insideLoc]
        by_cases below : index < count
        · simp [below, show index < count + 1 by omega, markedBelow index below]
        · by_cases equal : index = count
          · subst equal
            simp [markedTop, underLocation]
          · have above : ¬ index < count + 1 := by omega
            obtain ⟨rest, restIs⟩ : ∃ rest, index - count = rest + 1 := ⟨index - count - 1, by omega⟩
            simp only [above, below, if_false, restIs, underLocation]
            rw [show index - (count + 1) = rest by omega]
    | fvar name => simp [insideLoc, underLocation]
    | _ => simp [isVariable] at isVar
  have half := WellLocated.embed (relabel := id) (total := count + 1) (bigger := marker :: components)
    (placeBig := here) (isLocBig := isLoc) well (fun _ _ same => same)
    (.inr ⟨count, Nat.lt_succ_self _, by simp [Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_id, liftBVars],
      markedTop⟩)
    (fun index below => by simp; omega) (fun index below => markedBelow index below)
    (fun pattern isVar => by rw [Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_id]; exact locIs pattern isVar)
  rw [show components.map (rename id) = components from by
    conv_rhs => rw [← List.map_id components]
    exact List.map_congr_left fun component _ => Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_id component]
    at half
  have markerPlace : placeAt marker = some (liftBVars 0 (count + 1) here) := by
    rw [markerIs, placeAt_ofMarker isMarker, Mettapedia.Languages.ProcessCalculi.Ambient.Decoding.shiftName_eq,
      liftBVars_par_outer, Nat.add_comm]
  refine .intro hereLoc ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro component member
    rcases List.mem_cons.mp member with rfl | inComponents
    · exact .marker isMarker (Nat.lt_succ_self _)
    · exact (half component inComponents).1
  · intro component member at' isPlaced
    rcases List.mem_cons.mp member with rfl | inComponents
    · rw [markerPlace, Option.some.injEq] at isPlaced
      exact .inl isPlaced.symm
    · exact (half component inComponents).2.1 at' isPlaced
  · intro index
    rw [List.filter_cons]
    by_cases equal : index = count
    · subst equal
      rw [if_pos (by simp [markerChild]), List.length_cons, List.filter_eq_nil_iff.mpr]
      · simp
      intro component member isChild
      obtain ⟨childIndex, below, same⟩ := childOf_bvar_of_kind (kinds component member)
        (by simpa using isChild)
      simp at same; omega
    · rw [if_neg (by simp [markerChild, Ne.symm equal])]
      exact unique index
  · intro component member found isName
    rcases List.mem_cons.mp member with rfl | inComponents
    · simp only [markerIs, nameOf, if_pos isMarker, Option.some.injEq] at isName
      subst isName
      refine ⟨by cases name <;> simp_all [isVariable, liftBVars], fun inside => nameApart ?_⟩
      cases name with
      | bvar index =>
          simp only [liftBVars, Nat.zero_le, if_true, insideLoc] at inside
          by_cases zero : index = 0
          · subst zero
            simp [underLocation]
          · obtain ⟨rest, rfl⟩ : ∃ rest, index = rest + 1 := ⟨index - 1, by omega⟩
            split_ifs at inside with tooSmall
            · omega
            · simp only [underLocation]
              convert inside using 2
              omega
      | fvar name => simpa [liftBVars, insideLoc, underLocation] using inside
      | _ => simp [isVariable] at nameVar
    · exact (half component inComponents).2.2.1 found isName
  · intro component member label at' found continuation isCap listed
    rcases List.mem_cons.mp member with rfl | inComponents
    · simp only [markerIs, Pattern.apply.injEq] at isCap
      obtain ⟨rfl, -⟩ := isCap
      exact absurd listed (not_capability_of_marker isMarker)
    · exact (half component inComponents).2.2.2.1 label at' found continuation isCap listed
  · intro component member argument at' isRep isPlaced
    rcases List.mem_cons.mp member with rfl | inComponents
    · simp [markerIs] at isRep
    · exact (half component inComponents).2.2.2.2.1 argument at' isRep isPlaced
  · intro component member argument isRep
    rcases List.mem_cons.mp member with rfl | inComponents
    · simp [markerIs] at isRep
    · exact (half component inComponents).2.2.2.2.2.1 argument isRep
  · refine ((show Nested count components from well.nested).close fun component member child isChild => ?_).cons_outside
      fun index isPlaced => ?_
    · obtain ⟨childIndex, below, same⟩ := childOf_bvar_of_kind (kinds component member) isChild
      simp only [Pattern.bvar.injEq] at same
      change childIndex < count at below
      omega
    · rw [markerPlace, Option.some.injEq] at isPlaced
      by_contra small
      exact liftBVars_ne_bvar count here (by omega) isPlaced
  · intro component member message isMsgOf
    rcases List.mem_cons.mp member with rfl | inComponents
    · simp only [markerIs, messageOf] at isMsgOf
      split_ifs at isMsgOf with isCap
      subst isCap
      simp [markers] at isMarker
    · exact (half component inComponents).2.2.2.2.2.2.1 message isMsgOf
  · intro component member at' message continuation isCapComponent
    rcases List.mem_cons.mp member with rfl | inComponents
    · simp only [markerIs, Pattern.apply.injEq] at isCapComponent
      obtain ⟨rfl, -⟩ := isCapComponent
      simp [markers] at isMarker
    · exact (half component inComponents).2.2.2.2.2.2.2.1 at' message continuation isCapComponent
  · intro component member label at' binder body isInput listed
    rcases List.mem_cons.mp member with rfl | inComponents
    · simp [markerIs] at isInput
    · exact (half component inComponents).2.2.2.2.2.2.2.2 label at' binder body isInput listed

/-! ## What a well-located block uses from outside -/

open Mettapedia.OSLF.MeTTaIL.CanonicalBags (FreeIn freeIn_bvar freeIn_apply freeIn_lambda)

theorem not_freeIn_fvar {index : Nat} {name : String} : ¬ FreeIn index (.fvar name) := by
  intro free; cases free

/-- **A message's bound variables are ones it uses.** -/
theorem freeIn_of_messageVariables : ∀ {message : Pattern} {index : Nat},
    Pattern.bvar index ∈ messageVariables message → FreeIn index message
  | .bvar _, _, member => by
      simp only [messageVariables, List.mem_singleton, Pattern.bvar.injEq] at member
      subst member
      exact .bvar _
  | .fvar _, _, member => by simp [messageVariables] at member
  | .apply _ [], _, member => by simp [messageVariables] at member
  | .apply _ [name], _, member =>
      freeIn_apply.mpr ⟨name, List.mem_singleton_self _,
        freeIn_of_messageVariables (by simpa [messageVariables] using member)⟩
  | .apply _ [first, second], _, member => by
      simp only [messageVariables, List.mem_append] at member
      rcases member with inFirst | inSecond
      · exact freeIn_apply.mpr ⟨first, by simp, freeIn_of_messageVariables inFirst⟩
      · exact freeIn_apply.mpr ⟨second, by simp, freeIn_of_messageVariables inSecond⟩
  | .apply _ (_ :: _ :: _ :: _), _, member => by simp [messageVariables] at member
  | .lambda _ _, _, member => by simp [messageVariables] at member
  | .multiLambda _ _ _, _, member => by simp [messageVariables] at member
  | .subst _ _, _, member => by simp [messageVariables] at member
  | .collection _ _ _, _, member => by simp [messageVariables] at member

/-- **A renamed scoped message keeps apart from locations** when the renamed variables in scope and the free names
are no locations. -/
theorem messageVariables_apart {isLoc : Pattern → Prop} {relabel : Nat → Nat} {depth : Nat}
    (namesApart : ∀ index < depth, ¬ isLoc (.bvar (relabel index))) (fvarsApart : ∀ name, ¬ isLoc (.fvar name))
    {message : Pattern} (inScope : message.isWellScopedAt depth = true) :
    ∀ name ∈ messageVariables (rename relabel message), ¬ isLoc name := by
  intro name member
  rw [messageVariables_rename] at member
  obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp member
  cases original with
  | bvar index =>
      have free := freeIn_of_messageVariables inOriginal
      simpa [rename_bvar] using namesApart index (free.lt_of_scoped inScope)
  | fvar name => simpa [rename_fvar] using fvarsApart name
  | _ => exact absurd (isVariable_of_messageVariables inOriginal) (by simp [isVariable])

/-- **A variable a message uses is one of its variables.** -/
theorem freeIn_messageVariables : ∀ {message : Pattern} {index : Nat}, isMessage message = true →
    FreeIn index message → Pattern.bvar index ∈ messageVariables message
  | .bvar _, _, _, free => by rw [freeIn_bvar] at free; subst free; simp [messageVariables]
  | .fvar _, _, _, free => absurd free not_freeIn_fvar
  | .apply _ [], _, _, free => by obtain ⟨_, member, _⟩ := freeIn_apply.mp free; simp at member
  | .apply _ [name], _, isMsg, free => by
      simp only [isMessage, Bool.and_eq_true] at isMsg
      obtain ⟨argument, member, freeArgument⟩ := freeIn_apply.mp free
      simp only [List.mem_singleton] at member
      subst member
      cases argument with
      | bvar other => rw [freeIn_bvar] at freeArgument; subst freeArgument; simp [messageVariables]
      | fvar _ => exact absurd freeArgument not_freeIn_fvar
      | _ => simp [isVariable] at isMsg
  | .apply _ [first, second], _, isMsg, free => by
      simp only [isMessage, Bool.and_eq_true] at isMsg
      obtain ⟨argument, member, freeArgument⟩ := freeIn_apply.mp free
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      simp only [messageVariables, List.mem_append]
      rcases member with rfl | rfl
      · exact .inl (freeIn_messageVariables isMsg.1.2 freeArgument)
      · exact .inr (freeIn_messageVariables isMsg.2 freeArgument)
  | .apply _ (_ :: _ :: _ :: _), _, isMsg, _ => by simp [isMessage] at isMsg
  | .lambda _ _, _, isMsg, _ => by simp [isMessage] at isMsg
  | .multiLambda _ _ _, _, isMsg, _ => by simp [isMessage] at isMsg
  | .subst _ _, _, isMsg, _ => by simp [isMessage] at isMsg
  | .collection _ _ _, _, isMsg, _ => by simp [isMessage] at isMsg

/-- **A well-located block uses from outside only its place and names that are no locations.** -/
theorem WellLocated.freeIn_outer {isLoc : Pattern → Prop} {place : Pattern} {form : Prenex}
    (well : WellLocated isLoc place form) : LocVariables isLoc →
    ∀ component ∈ form.components, ∀ index, FreeIn index component → form.count ≤ index →
      Pattern.bvar (index - form.count) = place ∨ ¬ isLoc (.bvar (index - form.count)) := by
  induction well with
  | @intro isLoc place count components placeLoc kinds placed unique names caps reps repsPlaced _ messages capConts
      bodies capsIH repsIH capContsIH bodiesIH =>
      intro locVariables component member index free above
      change count ≤ index at above
      change Pattern.bvar (index - count) = place ∨ ¬ isLoc (.bvar (index - count))
      have atPlace : ∀ at', placeAt component = some at' → FreeIn index at' →
          Pattern.bvar (index - count) = place ∨ ¬ isLoc (.bvar (index - count)) := by
        intro at' found freeAt
        rcases placed component member at' found with rfl | ⟨inside, below, rfl, -⟩
        · have isVar := locVariables place placeLoc
          cases place with
          | bvar outer =>
              simp only [liftBVars, Nat.zero_le, if_true, freeIn_bvar] at freeAt
              left
              simp only [Pattern.bvar.injEq]
              omega
          | fvar name => simp [liftBVars] at freeAt; exact absurd freeAt not_freeIn_fvar
          | _ => simp [isVariable] at isVar
        · rw [freeIn_bvar] at freeAt
          omega
      have atName : ∀ name, nameOf component = some name → FreeIn index name → ¬ isLoc (.bvar (index - count)) := by
        intro name found freeName
        obtain ⟨isVar, apart⟩ := names component member name found
        cases name with
        | bvar other =>
            rw [freeIn_bvar] at freeName
            subst freeName
            simpa [insideLoc, show ¬ index < count by omega] using apart
        | fvar _ => exact absurd freeName not_freeIn_fvar
        | _ => simp [isVariable] at isVar
      have inner : ∀ at' block, placeAt component = some at' →
          (∀ component' ∈ (decompose locatedBlock block).components, ∀ index', FreeIn index' component' →
            (decompose locatedBlock block).count ≤ index' →
            Pattern.bvar (index' - (decompose locatedBlock block).count) = at' ∨
              ¬ insideLoc isLoc count components (.bvar (index' - (decompose locatedBlock block).count))) →
          FreeIn index block → Pattern.bvar (index - count) = place ∨ ¬ isLoc (.bvar (index - count)) := by
        intro at' block found recurse freeBlock
        obtain ⟨component', member', free'⟩ :=
          (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.freeIn_decompose (block := locatedBlock) block index).mp
            freeBlock
        rcases recurse component' member' _ free' (Nat.le_add_left _ _) with same | apart
        · rw [Nat.add_sub_cancel] at same
          exact atPlace at' found (by rw [← same]; exact .bvar index)
        · rw [Nat.add_sub_cancel] at apart
          right
          simpa [insideLoc, show ¬ index < count by omega] using apart
      have atMessage : ∀ message, messageOf component = some message → FreeIn index message →
          ¬ isLoc (.bvar (index - count)) := by
        intro message found freeMessage
        obtain ⟨isMsg, apart⟩ := messages component member message found
        simpa [insideLoc, show ¬ index < count by omega] using
          apart _ (freeIn_messageVariables isMsg freeMessage)
      have innerBody : ∀ at' body, placeAt component = some at' →
          (∀ component' ∈ (decompose locatedBlock body).components, ∀ index', FreeIn index' component' →
            (decompose locatedBlock body).count ≤ index' →
            Pattern.bvar (index' - (decompose locatedBlock body).count) = liftBVars 0 1 at' ∨
              ¬ underName (insideLoc isLoc count components) (.bvar (index' - (decompose locatedBlock body).count))) →
          FreeIn (index + 1) body → Pattern.bvar (index - count) = place ∨ ¬ isLoc (.bvar (index - count)) := by
        intro at' body found recurse freeBody
        obtain ⟨component', member', free'⟩ :=
          (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.freeIn_decompose (block := locatedBlock) body (index + 1)).mp
            freeBody
        rcases recurse component' member' _ free' (Nat.le_add_left _ _) with same | apart
        · rw [Nat.add_sub_cancel] at same
          have atIs : at' = .bvar index := by
            cases at' with
            | bvar other =>
                simp only [liftBVars, Nat.zero_le, if_true, Pattern.bvar.injEq] at same
                simp only [Pattern.bvar.injEq]
                omega
            | _ => simp [liftBVars] at same
          exact atPlace at' found (by rw [atIs]; exact .bvar index)
        · rw [Nat.add_sub_cancel] at apart
          right
          simpa [underName, insideLoc, show ¬ index < count by omega] using apart
      cases kinds component member with
      | @marker label parent name childIndex isMarker below =>
          obtain ⟨argument, inArguments, freeArgument⟩ := freeIn_apply.mp free
          simp only [List.mem_cons, List.not_mem_nil, or_false] at inArguments
          rcases inArguments with rfl | rfl | rfl
          · exact atPlace _ (placeAt_ofMarker isMarker _ _ _) freeArgument
          · rw [freeIn_bvar] at freeArgument; omega
          · exact .inr (atName _ (by simp [nameOf, isMarker]) freeArgument)
      | capability listed =>
          rename_i label at' name continuation
          obtain ⟨argument, inArguments, freeArgument⟩ := freeIn_apply.mp free
          have found : placeAt (.apply label [at', name, continuation]) = some at' := by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
            rcases listed with rfl | rfl | rfl <;> simp [placeAt, placeOf]
          have notMarker := not_marker_of_capability listed
          simp only [List.mem_cons, List.not_mem_nil, or_false] at inArguments
          rcases inArguments with rfl | rfl | rfl
          · exact atPlace _ found freeArgument
          · exact .inr (atName _ (by simp [nameOf, notMarker, listed]) freeArgument)
          · exact inner at' _ found (fun component' member' index' free' above' =>
              capsIH _ member label at' _ argument rfl listed (insideLoc_locVariables isLoc count components)
                component' member' index' free' above') freeArgument
      | replication =>
          rename_i argument
          obtain ⟨argument', inArguments, freeArgument⟩ := freeIn_apply.mp free
          simp only [List.mem_cons, List.not_mem_nil, or_false] at inArguments
          subst inArguments
          have hasPlace := repsPlaced _ member argument' rfl
          cases found : placeAt (Pattern.apply "LRep" [argument']) with
          | none => rw [found] at hasPlace; cases hasPlace
          | some at' =>
              exact inner at' _ found (fun component' member' index' free' above' =>
                repsIH _ member argument' at' rfl found (insideLoc_locVariables isLoc count components)
                  component' member' index' free' above') freeArgument
      | cap =>
          rename_i at' message continuation
          obtain ⟨argument, inArguments, freeArgument⟩ := freeIn_apply.mp free
          have found : placeAt (.apply "LCap" [at', message, continuation]) = some at' := by simp [placeAt, placeOf]
          simp only [List.mem_cons, List.not_mem_nil, or_false] at inArguments
          rcases inArguments with rfl | rfl | rfl
          · exact atPlace _ found freeArgument
          · exact .inr (atMessage _ (by simp [messageOf]) freeArgument)
          · exact inner at' _ found (fun component' member' index' free' above' =>
              capContsIH _ member at' message argument rfl (insideLoc_locVariables isLoc count components)
                component' member' index' free' above') freeArgument
      | input listed =>
          rename_i label at' binder body
          obtain ⟨argument, inArguments, freeArgument⟩ := freeIn_apply.mp free
          have found : placeAt (.apply label [at', .lambda binder body]) = some at' := by
            simp only [inputs, List.mem_cons, List.not_mem_nil, or_false] at listed
            rcases listed with rfl | rfl <;> simp [placeAt, placeOf]
          simp only [List.mem_cons, List.not_mem_nil, or_false] at inArguments
          rcases inArguments with rfl | rfl
          · exact atPlace _ found freeArgument
          · exact innerBody at' body found (fun component' member' index' free' above' =>
              bodiesIH _ member label at' binder body rfl listed (underName_locVariables _)
                component' member' index' free' above') (freeIn_lambda.mp freeArgument)
      | output listed =>
          rename_i label at' message
          obtain ⟨argument, inArguments, freeArgument⟩ := freeIn_apply.mp free
          have found : placeAt (.apply label [at', message]) = some at' := by
            simp only [outputs, List.mem_cons, List.not_mem_nil, or_false] at listed
            rcases listed with rfl | rfl <;> simp [placeAt, placeOf]
          simp only [List.mem_cons, List.not_mem_nil, or_false] at inArguments
          rcases inArguments with rfl | rfl
          · exact atPlace _ found freeArgument
          · exact .inr (atMessage _ (by simp [messageOf, listed]) freeArgument)

end Mettapedia.Languages.ProcessCalculi.Ambient.Decoding
