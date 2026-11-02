import Mettapedia.Languages.ProcessCalculi.Ambient.DecodingCopies

/-!
# Parts of well-located blocks

Well-locatedness carries over to the blocks a reading takes apart:

- to fewer locations, when the place stays one (`WellLocated.mono`);
- to the components left after dropping some, when no ambient of the dropped ones holds a component left
  (`WellLocated.drop`);
- back through a reindexing of a block's restrictions (`WellLocated.comap`);
- to a block's innermost restrictions and the components using them, read at their own place
  (`WellLocated.innerPart`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Decoding

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (FreeIn liftIndex)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (Prenex decompose rename rename_bvar rename_fvar rename_apply
  liftBVars_eq_rename shiftAbove decompose_renameOuter rename_injective)
open Mettapedia.Languages.ProcessCalculi.Ambient.Located (locatedBlock)

/-- The place of a block, lifted past its restrictions, is a location inside it. -/
theorem insideLoc_lift_place {isLoc : Pattern → Prop} {place : Pattern} (placeVar : isVariable place = true)
    (count : Nat) (components : List Pattern) :
    insideLoc isLoc count components (liftBVars 0 count place) ↔ isLoc place := by
  cases place with
  | bvar outer =>
      simp only [liftBVars, Nat.zero_le, if_true, insideLoc, show ¬ outer + count < count by omega, if_false,
        show outer + count - count = outer by omega]
  | fvar name => simp [liftBVars, insideLoc]
  | _ => simp [isVariable] at placeVar

/-- **The place of a component of a well-located block is a location there.** -/
theorem WellLocated.placeInside {isLoc : Pattern → Prop} {place : Pattern} {count : Nat} {components : List Pattern}
    (well : WellLocated isLoc place ⟨count, components⟩) (locVariables : LocVariables isLoc) :
    ∀ component ∈ components, ∀ at', placeAt component = some at' → insideLoc isLoc count components at' := by
  intro component member at' isPlaced
  rcases well.placed component member at' isPlaced with same | ⟨index, below, same, isMarked⟩
  · change at' = liftBVars 0 count place at same
    rw [same, insideLoc_lift_place (locVariables place well.placeIsLoc)]
    exact well.placeIsLoc
  · change index < count at below
    rw [same]
    simp only [insideLoc, below, if_true]
    exact isMarked

/-- A capability's place, read off the capability. -/
theorem placeAt_capability {label : String} (listed : label ∈ capabilities) (at' name continuation : Pattern) :
    placeAt (.apply label [at', name, continuation]) = some at' := by
  simp [placeAt, placeOf, listed]

/-- A prefix's place, read off the prefix. -/
theorem placeAt_cap (at' message continuation : Pattern) :
    placeAt (.apply "LCap" [at', message, continuation]) = some at' := by
  simp [placeAt, placeOf]

/-- An input's place, read off the input. -/
theorem placeAt_input {label : String} (listed : label ∈ inputs) (at' second : Pattern) :
    placeAt (.apply label [at', second]) = some at' := by
  simp [placeAt, placeOf, listed]

/-- An output's place, read off the output. -/
theorem placeAt_output {label : String} (listed : label ∈ outputs) (at' message : Pattern) :
    placeAt (.apply label [at', message]) = some at' := by
  simp [placeAt, placeOf, listed]

/-- A place read under a name binder is a location there when it is one outside. -/
theorem underName_liftBVars {isLoc : Pattern → Prop} {pattern : Pattern} (isVar : isVariable pattern = true) :
    underName isLoc (liftBVars 0 1 pattern) ↔ isLoc pattern := by
  cases pattern with
  | bvar index => simp [liftBVars, underName]
  | fvar name => simp [liftBVars, underName]
  | _ => simp [isVariable] at isVar

/-- Fewer locations outside a name binder are fewer locations under it. -/
theorem underName_mono {isLoc isLoc' : Pattern → Prop} (smaller : ∀ pattern, isLoc' pattern → isLoc pattern) :
    ∀ pattern, underName isLoc' pattern → underName isLoc pattern := by
  intro pattern inside
  cases pattern with
  | bvar index =>
      cases index with
      | zero => exact inside.elim
      | succ index => exact smaller _ inside
  | fvar name => exact smaller _ inside
  | _ => exact inside.elim

/-- **Fewer locations, the place still one, keep a block well-located.** -/
theorem WellLocated.mono {isLoc : Pattern → Prop} {place : Pattern} {form : Prenex}
    (well : WellLocated isLoc place form) (locVariables : LocVariables isLoc) :
    ∀ {isLoc' : Pattern → Prop}, (∀ pattern, isLoc' pattern → isLoc pattern) → isLoc' place →
      WellLocated isLoc' place form := by
  induction well with
  | @intro isLoc place count components placeLoc kinds placed unique names caps reps repsPlaced nested messages
      capConts bodies capsIH repsIH capContsIH bodiesIH =>
      intro isLoc' smaller placeLoc'
      have insideSmaller : ∀ pattern, insideLoc isLoc' count components pattern →
          insideLoc isLoc count components pattern := by
        intro pattern inside
        cases pattern with
        | bvar index =>
            simp only [insideLoc] at inside ⊢
            split_ifs at inside ⊢
            · exact inside
            · exact smaller _ inside
        | fvar name => exact smaller _ inside
        | _ => simp [insideLoc] at inside
      have placeInside' : ∀ component ∈ components, ∀ at', placeAt component = some at' →
          insideLoc isLoc' count components at' := by
        intro component member at' isPlaced
        rcases placed component member at' isPlaced with rfl | ⟨index, below, rfl, isMarked⟩
        · rw [insideLoc_lift_place (locVariables place placeLoc)]
          exact placeLoc'
        · simp only [insideLoc, below, if_true]
          exact isMarked
      refine .intro placeLoc' kinds placed unique (fun component member name isName => ?_)
        (fun component member label at' name continuation isCap listed => ?_)
        (fun component member argument at' isRep isPlaced => ?_) repsPlaced nested
        (fun component member message isMsgOf => ?_)
        (fun component member at' message continuation isCapComponent => ?_)
        (fun component member label at' binder body isInput listed => ?_)
      · obtain ⟨isVar, apart⟩ := names component member name isName
        exact ⟨isVar, fun inside => apart (insideSmaller _ inside)⟩
      · have atInside := placeInside' component member at' (by rw [isCap]; exact placeAt_capability listed _ _ _)
        exact capsIH component member label at' name continuation isCap listed
          (insideLoc_locVariables isLoc count components) insideSmaller atInside
      · exact repsIH component member argument at' isRep isPlaced (insideLoc_locVariables isLoc count components)
          insideSmaller (placeInside' component member at' isPlaced)
      · obtain ⟨isMsg, apart⟩ := messages component member message isMsgOf
        exact ⟨isMsg, fun name inVariables inside => apart name inVariables (insideSmaller _ inside)⟩
      · have atInside := placeInside' component member at' (by rw [isCapComponent]; exact placeAt_cap _ _ _)
        exact capContsIH component member at' message continuation isCapComponent
          (insideLoc_locVariables isLoc count components) insideSmaller atInside
      · have atInside := placeInside' component member at' (by rw [isInput]; exact placeAt_input listed _ _)
        exact bodiesIH component member label at' binder body isInput listed (underName_locVariables _)
          (underName_mono insideSmaller)
          ((underName_liftBVars (insideLoc_locVariables isLoc' count components at' atInside)).mpr atInside)

/-- Locations inside a block are marked by fewer components only fewer. -/
theorem insideLoc_sub {isLoc : Pattern → Prop} {count : Nat} {smaller components : List Pattern}
    (sub : ∀ component ∈ smaller, component ∈ components) :
    ∀ pattern, insideLoc isLoc count smaller pattern → insideLoc isLoc count components pattern := by
  intro pattern inside
  cases pattern with
  | bvar index =>
      simp only [insideLoc] at inside ⊢
      split_ifs at inside ⊢
      · obtain ⟨marker, member, isChild⟩ := inside
        exact ⟨marker, sub marker member, isChild⟩
      · exact inside
  | fvar name => exact inside
  | _ => simp [insideLoc] at inside

/-- **Dropping components no ambient left needs keeps a block well-located**: the components left sit at the place or
at locations whose markers are left. -/
theorem WellLocated.drop {isLoc : Pattern → Prop} {place : Pattern} {count : Nat} {components dropped kept : List Pattern}
    (well : WellLocated isLoc place ⟨count, components⟩) (locVariables : LocVariables isLoc)
    (split : components.Perm (dropped ++ kept))
    (holds : ∀ component ∈ kept, ∀ index, placeAt component = some (.bvar index) → ∀ marker ∈ dropped,
      childOf marker ≠ some (.bvar index)) :
    WellLocated isLoc place ⟨count, kept⟩ := by
  have inComponents : ∀ component ∈ kept, component ∈ components :=
    fun component member => split.symm.subset (List.mem_append_right _ member)
  have markedKept : ∀ component ∈ kept, ∀ index, placeAt component = some (.bvar index) → index < count →
      Marked components index → Marked kept index := by
    intro component member index isPlaced below ⟨marker, markerMember, isChild⟩
    rcases List.mem_append.mp (split.subset markerMember) with inDropped | inKept
    · exact absurd isChild (holds component member index isPlaced marker inDropped)
    · exact ⟨marker, inKept, isChild⟩
  have placedKept : ∀ component ∈ kept, ∀ at', placeAt component = some at' →
      at' = liftBVars 0 count place ∨ ∃ index < count, at' = .bvar index ∧ Marked kept index := by
    intro component member at' isPlaced
    rcases well.placed component (inComponents component member) at' isPlaced with same | ⟨index, below, rfl, isMarked⟩
    · exact .inl same
    · exact .inr ⟨index, below, rfl, markedKept component member index isPlaced below isMarked⟩
  have placeInside : ∀ component ∈ kept, ∀ at', placeAt component = some at' → insideLoc isLoc count kept at' := by
    intro component member at' isPlaced
    rcases placedKept component member at' isPlaced with rfl | ⟨index, below, rfl, isMarked⟩
    · rw [insideLoc_lift_place (locVariables place well.placeIsLoc)]
      exact well.placeIsLoc
    · simp only [insideLoc, below, if_true]
      exact isMarked
  have insideSmaller := insideLoc_sub (isLoc := isLoc) (count := count) inComponents
  refine .intro well.placeIsLoc (fun component member => well.kinds component (inComponents component member))
    placedKept (fun index => ?_) (fun component member name isName => ?_)
    (fun component member label at' name continuation isCap listed => ?_)
    (fun component member argument at' isRep isPlaced => ?_)
    (fun component member => well.repsPlaced component (inComponents component member))
    (well.nested.sublist inComponents) (fun component member message isMsgOf => ?_)
    (fun component member at' message continuation isCapComponent => ?_)
    (fun component member label at' binder body isInput listed => ?_)
  · have whole := well.unique index
    simp only at whole
    have counted := (split.filter fun component => childOf component == some (.bvar index)).length_eq
    rw [List.filter_append, List.length_append] at counted
    omega
  · obtain ⟨isVar, apart⟩ := well.names component (inComponents component member) name isName
    exact ⟨isVar, fun inside => apart (insideSmaller _ inside)⟩
  · have atInside := placeInside component member at' (by rw [isCap]; exact placeAt_capability listed _ _ _)
    cases well with
    | intro _ _ _ _ _ caps _ _ _ _ _ _ =>
        exact (caps component (inComponents component member) label at' name continuation isCap listed).mono
          (insideLoc_locVariables isLoc count components) insideSmaller atInside
  · cases well with
    | intro _ _ _ _ _ _ reps _ _ _ _ _ =>
        exact (reps component (inComponents component member) argument at' isRep isPlaced).mono
          (insideLoc_locVariables isLoc count components) insideSmaller
          (placeInside component member at' isPlaced)
  · obtain ⟨isMsg, apart⟩ := well.messages component (inComponents component member) message isMsgOf
    exact ⟨isMsg, fun name inVariables inside => apart name inVariables (insideSmaller _ inside)⟩
  · have atInside := placeInside component member at' (by rw [isCapComponent]; exact placeAt_cap _ _ _)
    exact (well.capConts component (inComponents component member) at' message continuation isCapComponent).mono
      (insideLoc_locVariables isLoc count components) insideSmaller atInside
  · have atInside := placeInside component member at' (by rw [isInput]; exact placeAt_input listed _ _)
    exact (well.bodies component (inComponents component member) label at' binder body isInput listed).mono
      (underName_locVariables _) (underName_mono insideSmaller)
      ((underName_liftBVars (insideLoc_locVariables isLoc count kept at' atInside)).mpr atInside)

/-- **One marker places an ambient at any one location**, whatever is asked of a child. -/
theorem WellLocated.unique_any {isLoc : Pattern → Prop} {place : Pattern} {count : Nat} {components : List Pattern}
    (well : WellLocated isLoc place ⟨count, components⟩) :
    ∀ child, (components.filter fun component => childOf component == some child).length ≤ 1 := by
  intro child
  cases child with
  | bvar index => exact well.unique index
  | _ =>
      rw [List.filter_eq_nil_iff.mpr]
      · simp
      intro component member isChild
      obtain ⟨index, -, same⟩ := childOf_bvar_of_kind (well.kinds component member) (beq_iff_eq.mp isChild)
      cases same

/-! ## Reindexing restrictions -/

/-- Markers of reindexed components mark the reindexed restrictions. -/
theorem marked_comap {relabel : Nat → Nat} (injective : Function.Injective relabel) {components : List Pattern}
    (index : Nat) : Marked (components.map (rename relabel)) (relabel index) ↔ Marked components index := by
  constructor
  · rintro ⟨component, member, isChild⟩
    obtain ⟨original, inComponents, rfl⟩ := List.mem_map.mp member
    rw [childOf_rename] at isChild
    obtain ⟨child, found, same⟩ := Option.map_eq_some_iff.mp isChild
    obtain ⟨childIndex, rfl, mapped⟩ := rename_eq_bvar same
    exact ⟨original, inComponents, by rw [found, injective mapped]⟩
  · rintro ⟨component, member, isChild⟩
    refine ⟨rename relabel component, List.mem_map.mpr ⟨component, member, rfl⟩, ?_⟩
    rw [childOf_rename, isChild, Option.map_some, rename_bvar]

/-- Locations inside a reindexed block are the reindexed locations. -/
theorem insideLoc_comap {isLoc : Pattern → Prop} {count count' : Nat} {relabel : Nat → Nat}
    (injective : Function.Injective relabel) (inside : ∀ index < count', relabel index < count)
    (outside : ∀ offset, relabel (count' + offset) = count + offset) (components : List Pattern) (pattern : Pattern)
    (isVar : isVariable pattern = true) :
    insideLoc isLoc count (components.map (rename relabel)) (rename relabel pattern) ↔
      insideLoc isLoc count' components pattern := by
  cases pattern with
  | bvar index =>
      simp only [rename_bvar, insideLoc]
      by_cases below : index < count'
      · simp only [inside index below, below, if_true]
        exact marked_comap injective index
      · obtain ⟨offset, rfl⟩ : ∃ offset, index = count' + offset := ⟨index - count', by omega⟩
        rw [outside offset]
        simp only [show ¬ count + offset < count by omega, below, if_false]
        rw [show count + offset - count = count' + offset - count' by omega]
  | fvar name => simp [rename_fvar, insideLoc]
  | _ => simp [isVariable] at isVar

/-- **A block whose reindexing is well-located is well-located**: its restrictions read back through an injective
reindexing that keeps the outside in place. -/
theorem WellLocated.comap {isLoc : Pattern → Prop} {place : Pattern} {count count' : Nat} {components : List Pattern}
    {relabel : Nat → Nat} (injective : Function.Injective relabel) (inside : ∀ index < count', relabel index < count)
    (outside : ∀ offset, relabel (count' + offset) = count + offset)
    (well : WellLocated isLoc place ⟨count, components.map (rename relabel)⟩) (locVariables : LocVariables isLoc) :
    WellLocated isLoc place ⟨count', components⟩ := by
  have renamedInjective := rename_injective injective
  have member : ∀ {component}, component ∈ components →
      rename relabel component ∈ components.map (rename relabel) :=
    fun inComponents => List.mem_map.mpr ⟨_, inComponents, rfl⟩
  have backInside : ∀ {index : Nat}, relabel index < count → index < count' := by
    intro index below
    by_contra notBelow
    obtain ⟨offset, rfl⟩ : ∃ offset, index = count' + offset := ⟨index - count', by omega⟩
    rw [outside offset] at below
    omega
  have placeLifted : rename relabel (liftBVars 0 count' place) = liftBVars 0 count place := by
    have placeVar := locVariables place well.placeIsLoc
    cases place with
    | bvar outer =>
        simp only [liftBVars, Nat.zero_le, if_true, rename_bvar]
        rw [show outer + count' = count' + outer by omega, outside outer, Nat.add_comm]
    | fvar name => simp [liftBVars, rename_fvar]
    | _ => simp [isVariable] at placeVar
  have compat := insideLoc_comap (isLoc := isLoc) injective inside outside components
  have kindBack : ∀ {component}, component ∈ components → ComponentKind count' component := by
    intro component inComponents
    have kind := well.kinds _ (member inComponents)
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
              subst mapped
              exact .marker isMarker (backInside below)
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
  refine .intro well.placeIsLoc (fun component inComponents => kindBack inComponents) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro component inComponents at' isPlaced
    have renamedPlaced := well.placed _ (member inComponents) (rename relabel at')
      (by rw [placeAt_rename, isPlaced, Option.map_some])
    rcases renamedPlaced with same | ⟨index, below, same, isMarked⟩
    · rw [← placeLifted] at same
      exact .inl (renamedInjective same)
    · obtain ⟨original, rfl, mapped⟩ := rename_eq_bvar same
      subst mapped
      exact .inr ⟨original, backInside below, rfl, (marked_comap injective original).mp isMarked⟩
  · intro index
    refine le_trans (le_of_eq ?_) (well.unique (relabel index))
    simp only
    rw [List.filter_map, List.length_map]
    congr 1
    apply List.filter_congr
    intro component inComponents
    simp only [Function.comp, childOf_rename]
    cases found : childOf component with
    | none => simp
    | some child =>
        simp only [Option.map_some]
        obtain ⟨childIndex, -, rfl⟩ := childOf_bvar_of_kind (kindBack inComponents) found
        rw [Bool.eq_iff_iff]
        simp only [rename_bvar, beq_iff_eq, Option.some.injEq, Pattern.bvar.injEq]
        exact ⟨fun same => by rw [same], fun same => injective same⟩
  · intro component inComponents name isName
    obtain ⟨isVar, apart⟩ := well.names _ (member inComponents) (rename relabel name)
      (by rw [nameOf_rename, isName, Option.map_some])
    rw [isVariable_rename] at isVar
    exact ⟨isVar, fun insideHere => apart ((compat name isVar).mpr insideHere)⟩
  · intro component inComponents label at' name continuation isCap listed
    subst isCap
    cases well with
    | intro _ _ _ _ _ caps _ _ _ _ _ _ =>
        have inner := caps _ (member inComponents) label (rename relabel at') (rename relabel name)
          (rename relabel continuation) (by simp [rename_apply]) listed
        rw [decompose_renameOuter] at inner
        exact inner.unrename injective compat (insideLoc_locVariables isLoc count _) rfl rfl
  · intro component inComponents argument at' isRep isPlaced
    subst isRep
    cases well with
    | intro _ _ _ _ _ _ reps _ _ _ _ _ =>
        have inner := reps _ (member inComponents) (rename relabel argument) (rename relabel at')
          (by simp [rename_apply]) (by rw [placeAt_rename, isPlaced, Option.map_some])
        rw [decompose_renameOuter] at inner
        exact inner.unrename injective compat (insideLoc_locVariables isLoc count _) rfl rfl
  · intro component inComponents argument isRep
    subst isRep
    have renamedPlaced := well.repsPlaced _ (member inComponents) (rename relabel argument) (by simp [rename_apply])
    rw [placeAt_rename] at renamedPlaced
    cases found : placeAt (Pattern.apply "LRep" [argument]) with
    | none => rw [found] at renamedPlaced; cases renamedPlaced
    | some at' => rfl
  · obtain ⟨depth, grows⟩ := well.nested
    refine ⟨depth ∘ relabel, fun component inComponents index child below childBelow isPlaced isChild => ?_⟩
    exact grows _ (member inComponents) (relabel index) (relabel child) (inside index below) (inside child childBelow)
      (by rw [placeAt_rename, isPlaced, Option.map_some, rename_bvar])
      (by rw [childOf_rename, isChild, Option.map_some, rename_bvar])
  · intro component inComponents message isMsgOf
    obtain ⟨isMsg, apart⟩ := well.messages _ (member inComponents) (rename relabel message)
      (by rw [messageOf_rename, isMsgOf, Option.map_some])
    rw [isMessage_rename] at isMsg
    exact ⟨isMsg, (messages_rename compat).mp apart⟩
  · intro component inComponents at' message continuation isCapComponent
    subst isCapComponent
    have inner := well.capConts _ (member inComponents) (rename relabel at') (rename relabel message)
      (rename relabel continuation) (by simp [rename_apply])
    rw [decompose_renameOuter] at inner
    exact inner.unrename injective compat (insideLoc_locVariables isLoc count _) rfl rfl
  · intro component inComponents label at' binder body isInput listed
    subst isInput
    have inner := well.bodies _ (member inComponents) label (rename relabel at') binder
      (rename (liftIndex 1 relabel) body)
      (by simp [rename_apply, Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_lambda]) listed
    rw [decompose_renameOuter] at inner
    exact inner.unrename (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.liftIndex_injective injective 1)
      (underName_compat compat) (underName_locVariables _) (rename_liftBVars_place relabel 1 at').symm rfl

/-! ## The innermost restrictions -/

/-- **The innermost restrictions of a block and the components using them, read at their own place, are a
well-located block**, its outside the rest of the block. -/
theorem WellLocated.innerPart {isLoc : Pattern → Prop} {place home : Pattern} {count owned : Nat}
    {rest part : List Pattern} (well : WellLocated isLoc place ⟨count, rest ++ part⟩) (ownedBelow : owned ≤ count)
    (restApart : ∀ component ∈ rest, ∀ index < owned, ¬ FreeIn index component)
    (partPlaced : ∀ component ∈ part, ∀ at', placeAt component = some at' →
      at' = liftBVars 0 owned home ∨ ∃ index < owned, at' = .bvar index)
    (partChildren : ∀ component ∈ part, ∀ child, childOf component = some child →
      ∃ index < owned, child = .bvar index)
    (homeLoc : insideLoc isLoc count (rest ++ part) (liftBVars 0 owned home)) :
    WellLocated (fun pattern => insideLoc isLoc count (rest ++ part) (liftBVars 0 owned pattern)) home
      ⟨owned, part⟩ := by
  have inWhole : ∀ component ∈ part, component ∈ rest ++ part := fun component member => List.mem_append_right _ member
  have markedPart : ∀ index < owned, (Marked part index ↔ Marked (rest ++ part) index) := by
    intro index below
    constructor
    · rintro ⟨marker, member, isChild⟩
      exact ⟨marker, inWhole marker member, isChild⟩
    · rintro ⟨marker, member, isChild⟩
      rcases List.mem_append.mp member with inRest | inPart
      · exact absurd (freeIn_child isChild) (restApart marker inRest index below)
      · exact ⟨marker, inPart, isChild⟩
  have insideSame : insideLoc (fun pattern => insideLoc isLoc count (rest ++ part) (liftBVars 0 owned pattern)) owned
      part = insideLoc isLoc count (rest ++ part) := by
    funext pattern
    apply propext
    cases pattern with
    | bvar index =>
        by_cases below : index < owned
        · simp only [insideLoc, below, if_true, show index < count by omega]
          exact markedPart index below
        · simp only [insideLoc, below, if_false, liftBVars, Nat.zero_le, if_true]
          rw [show index - owned + owned = index by omega]
    | fvar name => simp [insideLoc, liftBVars]
    | _ => simp [insideLoc]
  refine .intro homeLoc (fun component member => ?_) (fun component member at' isPlaced => ?_) (fun index => ?_)
    (fun component member name isName => ?_) ?_ ?_
    (fun component member => well.repsPlaced component (inWhole component member)) ?_ ?_ ?_ ?_
  · cases well.kinds component (inWhole component member) with
    | marker isMarker below =>
        obtain ⟨index, indexBelow, same⟩ := partChildren _ member _ (childOf_ofMarker isMarker _ _ _)
        simp only [Pattern.bvar.injEq] at same
        subst same
        exact .marker isMarker indexBelow
    | capability listed => exact .capability listed
    | replication => exact .replication
    | cap => exact .cap
    | input listed => exact .input listed
    | output listed => exact .output listed
  · rcases partPlaced component member at' isPlaced with same | ⟨index, below, rfl⟩
    · exact .inl same
    · refine .inr ⟨index, below, rfl, (markedPart index below).mpr ?_⟩
      rcases well.placed component (inWhole component member) _ isPlaced with same | ⟨other, -, same, isMarked⟩
      · cases place with
        | bvar outer => simp [liftBVars] at same; omega
        | _ => simp [liftBVars] at same
      · simp only [Pattern.bvar.injEq] at same
        subst same
        exact isMarked
  · have whole : ((rest ++ part).filter fun component => childOf component == some (.bvar index)).length ≤ 1 :=
      well.unique index
    rw [List.filter_append, List.length_append] at whole
    change (part.filter fun component => childOf component == some (.bvar index)).length ≤ 1
    omega
  · obtain ⟨isVar, apart⟩ := well.names component (inWhole component member) name isName
    exact ⟨isVar, by rw [insideSame]; exact apart⟩
  · intro component member label at' name continuation isCap listed
    rw [insideSame]
    cases well with
    | intro _ _ _ _ _ caps _ _ _ _ _ _ => exact caps component (inWhole component member) label at' name continuation isCap listed
  · intro component member argument at' isRep isPlaced
    rw [insideSame]
    cases well with
    | intro _ _ _ _ _ _ reps _ _ _ _ _ => exact reps component (inWhole component member) argument at' isRep isPlaced
  · obtain ⟨depth, grows⟩ := well.nested
    exact ⟨depth, fun component member index child below childBelow isPlaced isChild =>
      grows component (inWhole component member) index child (by change index < count; omega)
        (by change child < count; omega) isPlaced isChild⟩
  · intro component member message isMsgOf
    obtain ⟨isMsg, apart⟩ := well.messages component (inWhole component member) message isMsgOf
    exact ⟨isMsg, by rw [insideSame]; exact apart⟩
  · intro component member at' message continuation isCapComponent
    rw [insideSame]
    exact well.capConts component (inWhole component member) at' message continuation isCapComponent
  · intro component member label at' binder body isInput listed
    rw [insideSame]
    exact well.bodies component (inWhole component member) label at' binder body isInput listed

end Mettapedia.Languages.ProcessCalculi.Ambient.Decoding
