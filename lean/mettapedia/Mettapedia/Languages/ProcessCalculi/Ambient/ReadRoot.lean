import Mettapedia.Languages.ProcessCalculi.Ambient.ReadMoves
import Mettapedia.Languages.ProcessCalculi.Ambient.Presentations

/-!
# A reaction read back from the root

A reaction of a well-located block reads back, from the block's root, as a step: the bag of the padded items read at
the root steps to what the reacted components read as there, under the continuation's restrictions. Every place of a
well-located block is reached from its root (`WellLocated.reached`), and the reaction's parts are the capability, the
marker it rewrites and the parts it leaves (`LocRedex.parts_perm`), so the path down to the reaction
(`path_step`) ends in the reaction's step at its place (`open_local`, `enter_local`, `exit_local`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Steps

open Mettapedia.Languages.ProcessCalculi.Ambient.Comm (ambientCoreCalc)

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)
open Mettapedia.GSLT.LanguageDef.WellSorted (HasType FreeTypeContext isObjectPattern)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (Prenex Members ProcEquiv sizeList size decompose)
open Mettapedia.Languages.ProcessCalculi.Ambient.Full (AmbNuRawStep ambientBlock)
open Mettapedia.Languages.ProcessCalculi.Ambient.Located (locatedCalc locatedBlock)
open Mettapedia.Languages.ProcessCalculi.Ambient.Encoding (nameType procType)
open Mettapedia.Languages.ProcessCalculi.Ambient.Decoding (isVariable Reaches placedAt placeAt childOf readPlaced
  markers capabilities placeAt_ofMarker placeAt_capability triple_inv WellLocated ComponentKind Marked nameOf
  insideLoc childOf_eq_some childOf_bvar_of_kind)

variable {free : FreeTypeContext}

/-! ## Reaching the places of a well-located block -/

/-- **Reaching a marker's place reaches its location.** -/
theorem Reaches.extend {marker child : Pattern} : ∀ {components : List Pattern} {start place : Pattern},
    Reaches components start place → marker ∈ components → placeAt marker = some place →
    childOf marker = some child → Reaches components start child := by
  intro components start place reached
  induction reached with
  | here =>
      intro member isPlaced isChild
      exact .down member (by simp [placedAt, isPlaced]) isChild .here
  | @down components start child' place marker' member' isPlaced' isChild' below recurse =>
      intro member isPlaced isChild
      by_cases same : start = place
      · subst same
        exact .down member (by simp [placedAt, isPlaced]) isChild .here
      · have kept : marker ∈ components.filter fun other => !placedAt start other :=
          List.mem_filter.mpr ⟨member, by simp [placedAt, isPlaced, Ne.symm same]⟩
        exact .down member' isPlaced' isChild' (recurse kept isPlaced isChild)

/-- **Every place of a well-located block is reached from its root.** -/
theorem WellLocated.reached {isLoc : Pattern → Prop} {place : Pattern} {count : Nat} {components : List Pattern}
    (well : WellLocated isLoc place ⟨count, components⟩) :
    ∀ component ∈ components, ∀ at', placeAt component = some at' →
      Reaches components (liftBVars 0 count place) at' := by
  obtain ⟨depth, grows⟩ := well.nested
  have marked : ∀ bound, ∀ index < count, depth index < bound → Marked components index →
      Reaches components (liftBVars 0 count place) (.bvar index) := by
    intro bound
    induction bound with
    | zero => intro _ _ small; omega
    | succ bound recurse =>
        intro index below small isMarked
        obtain ⟨marker, member, isChild⟩ := isMarked
        obtain ⟨label, parent, name, isMarker, rfl⟩ := childOf_eq_some isChild
        have markerPlaced : placeAt (.apply label [parent, .bvar index, name]) = some parent :=
          placeAt_ofMarker isMarker _ _ _
        rcases well.placed _ member parent markerPlaced with atRoot | ⟨parentIndex, parentBelow, rfl, parentMarked⟩
        · exact Reaches.extend (by rw [atRoot]; exact .here) member markerPlaced isChild
        · have deeper := grows _ member parentIndex index parentBelow below markerPlaced isChild
          exact Reaches.extend (recurse parentIndex parentBelow (by omega) parentMarked) member markerPlaced isChild
  intro component member at' sits
  rcases well.placed component member at' sits with atRoot | ⟨index, below, rfl, isMarked⟩
  · rw [atRoot]
    exact .here
  · exact marked _ index below (Nat.lt_succ_self _) isMarked

/-- **A marker of a well-located block holds a variable name.** -/
theorem WellLocated.markersOf {isLoc : Pattern → Prop} {place : Pattern} {count : Nat} {components : List Pattern}
    (well : WellLocated isLoc place ⟨count, components⟩) :
    ∀ component ∈ components, ∀ child, childOf component = some child →
      ∃ label parent name, label ∈ markers ∧ component = .apply label [parent, child, name] ∧
        isVariable name = true := by
  intro component member child isChild
  obtain ⟨label, parent, name, isMarker, rfl⟩ := childOf_eq_some isChild
  exact ⟨label, parent, name, isMarker, rfl,
    (well.names _ member name (by simp [nameOf, isMarker])).1⟩

/-- **A capability of a well-located block holds a variable name.** -/
theorem WellLocated.capabilityName {isLoc : Pattern → Prop} {place : Pattern} {count : Nat}
    {components : List Pattern} (well : WellLocated isLoc place ⟨count, components⟩) {label : String}
    {at' name continuation : Pattern} (member : .apply label [at', name, continuation] ∈ components)
    (listed : label ∈ capabilities) : isVariable name = true :=
  (well.names _ member name (by
    simp [nameOf, listed, Mettapedia.Languages.ProcessCalculi.Ambient.Decoding.not_marker_of_capability listed])).1

/-- **A capability's continuation in a well-located block is well-located at the capability's place.** -/
theorem WellLocated.continuation {isLoc : Pattern → Prop} {place : Pattern} {count : Nat}
    {components : List Pattern} (well : WellLocated isLoc place ⟨count, components⟩) {label : String}
    {at' name continuation : Pattern} (member : .apply label [at', name, continuation] ∈ components)
    (listed : label ∈ capabilities) :
    WellLocated (insideLoc isLoc count components) at' (decompose locatedBlock continuation) := by
  cases well with
  | intro _ _ _ _ _ caps _ _ _ _ _ _ => exact caps _ member label at' name continuation rfl listed

/-- A filter keeping at most one keeps no two members of a list. -/
theorem two_kept_absurd {keep : Pattern → Bool} {list rest : List Pattern} {first second : Pattern}
    (atMostOne : (list.filter keep).length ≤ 1) (split : list.Perm (first :: second :: rest))
    (firstKept : keep first = true) (secondKept : keep second = true) : False := by
  have counted := (split.filter keep).length_eq
  rw [List.filter_cons_of_pos firstKept, List.filter_cons_of_pos secondKept] at counted
  simp only [List.length_cons] at counted
  omega

/-! ## The shape of a located reaction -/

namespace LocRedex

/-- **The capability a redex fires.** -/
def capabilityPart : LocRedex → Pattern
  | .move entering _ mover _ _ targetName continuation => .apply (capability entering) [mover, targetName, continuation]
  | .open place _ name continuation => .apply "LOpen" [place, name, continuation]

/-- **The marker a redex rewrites.** -/
def markerPart : LocRedex → Pattern
  | .move entering parent mover target moverName _ _ => .apply "LAmb" [before entering parent target, mover, moverName]
  | .open place location name _ => .apply "LAmb" [place, location, name]

/-- **What the rewritten marker becomes.** -/
def movedPart : LocRedex → Pattern
  | .move entering parent mover target moverName _ _ => .apply "LAmb" [after entering parent target, mover, moverName]
  | .open place location name _ => .apply "LOpened" [place, location, name]

/-- **The parts a redex leaves as they are.** -/
def keptParts : LocRedex → List Pattern
  | .move _ parent _ target _ targetName _ => [.apply "LAmb" [parent, target, targetName]]
  | .open _ _ _ _ => []

/-- **The continuation a redex leaves.** -/
def continuationOf : LocRedex → Pattern
  | .move _ _ _ _ _ _ continuation => continuation
  | .open _ _ _ continuation => continuation

theorem parts_perm (redex : LocRedex) :
    redex.parts.Perm (redex.capabilityPart :: redex.markerPart :: redex.keptParts) := by
  cases redex with
  | move entering parent mover target moverName targetName continuation =>
      exact .swap _ _ _
  | «open» place location name continuation => exact .refl _

theorem result_perm (redex : LocRedex) :
    redex.result.Perm (redex.continuationOf :: redex.movedPart :: redex.keptParts) := by
  cases redex with
  | move entering parent mover target moverName targetName continuation =>
      exact .swap _ _ _
  | «open» place location name continuation => exact .refl _

end LocRedex

/-! ## The reaction read from the root -/

/-- **A reaction of a well-located block reads, from the root, as a step**: the bag of the padded items read at the
root steps to what the reacted components read as there, under the continuation's restrictions. -/
theorem root_reacts {isLoc : Pattern → Prop} {place : Pattern} {bound : List TypeExpr} {count : Nat}
    {components : List Pattern} (well : WellLocated isLoc place ⟨count, components⟩)
    (typed : Members locatedCalc locatedBlock free (List.replicate count nameType ++ bound) components)
    {redex : LocRedex} {rest : List Pattern} (split : components.Perm (redex.parts ++ rest))
    {owned : Nat} {group : List Pattern} (decomposed : decompose locatedBlock redex.continuationOf = ⟨owned, group⟩)
    (fuel : Nat) (enough : 3 * sizeList components + 9 ≤ fuel) :
    ∃ result, AmbNuRawStep
        (.collection .hashBag ((readPlaced fuel (liftBVars 0 count place) components).map padA) none) result ∧
      ProcEquiv ambientCoreCalc ambientBlock free (List.replicate count nameType ++ bound) result
        (Prenex.restricts ambientBlock owned (Prenex.body ambientBlock
          (readPlaced fuel (liftBVars 0 owned (liftBVars 0 count place))
            ((reactList redex.capabilityPart redex.markerPart redex.movedPart components).map (liftBVars 0 owned) ++
              group)))) := by
  have signature : Mettapedia.GSLT.LanguageDef.RestrictionBlocks.BlockSignature locatedCalc locatedBlock :=
    Mettapedia.Languages.ProcessCalculi.Ambient.Located.locatedLanguage.toBlockSignature
  -- what the block gives the path down to the reaction
  obtain ⟨depth, grows⟩ := well.nested
  have children : ∀ component ∈ components, ∀ child, childOf component = some child →
      ∃ index < count, child = .bvar index := fun component member _ isChild =>
    childOf_bvar_of_kind (well.kinds component member) isChild
  have unique := well.unique_any
  have markersOf := WellLocated.markersOf well
  have partsIn : ∀ part ∈ redex.capabilityPart :: redex.markerPart :: redex.keptParts, part ∈ components :=
    fun part member => split.symm.subset (List.mem_append_left _ ((LocRedex.parts_perm redex).symm.subset member))
  have capabilityIn := partsIn _ List.mem_cons_self
  have markerIn := partsIn _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have keptIn : ∀ part ∈ redex.keptParts, part ∈ components := fun part member =>
    partsIn part (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member))
  have twoParts : components.Perm (redex.markerPart :: redex.capabilityPart :: (redex.keptParts ++ rest)) :=
    split.trans (((LocRedex.parts_perm redex).append_right rest).trans (.swap _ _ _))
  -- the continuation, at the capability's place
  have continuationFacts : ∀ {label : String} {at' name : Pattern},
      redex.capabilityPart = .apply label [at', name, redex.continuationOf] → label ∈ capabilities →
      (∀ component ∈ group, ∀ at'', placeAt component = some at'' →
        at'' = liftBVars 0 owned at' ∨ ∃ index < owned, at'' = .bvar index) ∧
      (∀ component ∈ group, ∀ child, childOf component = some child → ∃ index < owned, child = .bvar index) ∧
      Members locatedCalc locatedBlock free (List.replicate owned nameType ++ (List.replicate count nameType ++ bound))
        group := by
    intro label at' name shape listed
    rw [shape] at capabilityIn
    have inner := WellLocated.continuation well capabilityIn listed
    rw [decomposed] at inner
    have continuationTyped : HasType locatedCalc free (List.replicate count nameType ++ bound) redex.continuationOf
        procType := by
      rcases triple_inv (typed _ capabilityIn) with ⟨isMarker, -, -⟩ | ⟨-, -, third⟩ | ⟨-, -, third⟩
      · exact absurd listed (Mettapedia.Languages.ProcessCalculi.Ambient.Decoding.not_capability_of_marker isMarker)
      · exact third
      · exact third
    have sound := (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.decompose_sound (language := locatedCalc)
      (block := locatedBlock) continuationTyped).1
    rw [decomposed] at sound
    refine ⟨fun component member at'' sits => ?_, fun component member child isChild => ?_, sound⟩
    · rcases inner.placed component member at'' sits with same | ⟨index, below, same, -⟩
      · exact .inl same
      · exact .inr ⟨index, below, same⟩
    · exact childOf_bvar_of_kind (inner.kinds component member) isChild
  -- the parts typed
  have placeTyped : ∀ {label : String} {first second third : Pattern},
      Pattern.apply label [first, second, third] ∈ components →
      HasType locatedCalc free (List.replicate count nameType ++ bound) first nameType := fun member =>
    triple_first (typed _ member)
  have namesTyped : ∀ {label : String} {first second third : Pattern},
      Pattern.apply label [first, second, third] ∈ components → label ∈ markers →
      HasType locatedCalc free (List.replicate count nameType ++ bound) second nameType ∧
        HasType locatedCalc free (List.replicate count nameType ++ bound) third nameType := by
    intro label first second third member isMarker
    rcases triple_inv (typed _ member) with ⟨-, second', third'⟩ | ⟨listed, -, -⟩ | ⟨rfl, -, -⟩
    · exact ⟨second', third'⟩
    · exact absurd listed (Mettapedia.Languages.ProcessCalculi.Ambient.Decoding.not_capability_of_marker isMarker)
    · simp [markers] at isMarker
  have rootPlace := liftBVars 0 count place
  cases redex with
  | «open» at' location name continuation =>
      simp only [LocRedex.capabilityPart, LocRedex.markerPart, LocRedex.movedPart, LocRedex.continuationOf]
        at capabilityIn markerIn decomposed continuationFacts ⊢
      have openListed : "LOpen" ∈ capabilities := by simp [capabilities]
      obtain ⟨groupPlaced, groupChildren, groupTyped⟩ := continuationFacts rfl openListed
      have ambMarker : "LAmb" ∈ markers := by simp [markers]
      have nameVar : isVariable name = true := (well.names _ markerIn name (by simp [nameOf, markers])).1
      obtain ⟨locationTyped, nameTyped⟩ := namesTyped markerIn ambMarker
      have marker'Typed : HasType locatedCalc free (List.replicate count nameType ++ bound)
          (.apply "LOpened" [at', location, name]) procType :=
        Mettapedia.Languages.ProcessCalculi.Ambient.Encoding.opened_typed (placeTyped markerIn) locationTyped nameTyped
      have capabilityAt : placeAt (.apply "LOpen" [at', name, continuation]) = some at' :=
        placeAt_capability openListed _ _ _
      have reached := WellLocated.reached well _ capabilityIn at' capabilityAt
      obtain ⟨result, step, equivalent⟩ := path_step (redexPlace := at') (touched := [at']) (home := at')
        (Holds := fun list => Pattern.apply "LOpen" [at', name, continuation] ∈ list ∧
          Pattern.apply "LAmb" [at', location, name] ∈ list) (extra := 6)
        children grows unique markersOf typed groupPlaced groupTyped marker'Typed List.mem_cons_self
        (fun x sits => by rw [capabilityAt] at sits; cases sits; exact List.mem_cons_self)
        (fun x sits => by
          rw [placeAt_ofMarker ambMarker] at sits
          cases sits
          exact List.mem_cons_self)
        (fun x sits => by
          rw [placeAt_ofMarker (show "LOpened" ∈ markers by simp [markers])] at sits
          cases sits
          exact List.mem_cons_self)
        (fun list place' holds notTouched => by
          have apart : place' ≠ at' := fun same => notTouched (same ▸ List.mem_cons_self)
          exact ⟨List.mem_filter.mpr ⟨holds.1, by simp [placedAt, capabilityAt, Ne.symm apart]⟩,
            List.mem_filter.mpr ⟨holds.2, by simp [placedAt, placeAt_ofMarker ambMarker, Ne.symm apart]⟩⟩)
        (fun list holds start reached' x inTouched => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at inTouched
          subst inTouched
          exact reached')
        (fun list holds => ⟨_, holds.1, by simp [placedAt, capabilityAt]⟩)
        (fun list holds sub fuel' enough' => open_local children grows unique typed nameVar decomposed
          groupPlaced groupChildren groupTyped sub holds.1 holds.2 fuel' (by omega))
        reached rfl (List.Sublist.refl _) ⟨capabilityIn, markerIn⟩ fuel (by omega)
      exact ⟨result, step, equivalent⟩
  | move entering parent mover target moverName targetName continuation =>
      cases entering with
      | true =>
          simp only [LocRedex.capabilityPart, LocRedex.markerPart, LocRedex.movedPart, LocRedex.continuationOf,
            LocRedex.keptParts, LocRedex.capability, LocRedex.before, LocRedex.after, if_true]
            at capabilityIn markerIn keptIn twoParts decomposed continuationFacts ⊢
          have inListed : "LIn" ∈ capabilities := by simp [capabilities]
          have ambMarker : "LAmb" ∈ markers := by simp [markers]
          obtain ⟨groupPlaced, groupChildren, groupTyped⟩ := continuationFacts rfl inListed
          have destinationIn := keptIn _ List.mem_cons_self
          have moverNameVar : isVariable moverName = true :=
            (well.names _ markerIn moverName (by simp [nameOf, markers])).1
          have targetNameVar := WellLocated.capabilityName well capabilityIn inListed
          have apartTargets : mover ≠ target := by
            intro same
            subst same
            exact two_kept_absurd (keep := fun component => childOf component == some mover) (unique mover)
              (twoParts.trans (.cons _ (.swap _ _ _))) (by simp [childOf, markers]) (by simp [childOf, markers])
          obtain ⟨moverTyped, moverNameTyped⟩ := namesTyped markerIn ambMarker
          obtain ⟨targetTyped, -⟩ := namesTyped destinationIn ambMarker
          have marker'Typed : HasType locatedCalc free (List.replicate count nameType ++ bound)
              (.apply "LAmb" [target, mover, moverName]) procType :=
            Mettapedia.Languages.ProcessCalculi.Ambient.Encoding.marker_typed targetTyped moverTyped moverNameTyped
          have destinationAt : placeAt (.apply "LAmb" [parent, target, targetName]) = some parent :=
            placeAt_ofMarker ambMarker _ _ _
          have markerAt : placeAt (.apply "LAmb" [parent, mover, moverName]) = some parent :=
            placeAt_ofMarker ambMarker _ _ _
          have reached := WellLocated.reached well _ destinationIn parent destinationAt
          obtain ⟨result, step, equivalent⟩ := path_step (redexPlace := parent) (touched := [parent, mover, target])
            (home := mover)
            (Holds := fun list => Pattern.apply "LAmb" [parent, mover, moverName] ∈ list ∧
              Pattern.apply "LIn" [mover, targetName, continuation] ∈ list ∧
              Pattern.apply "LAmb" [parent, target, targetName] ∈ list) (extra := 6)
            children grows unique markersOf typed groupPlaced groupTyped marker'Typed (by simp)
            (fun x sits => by rw [placeAt_capability inListed] at sits; cases sits; simp)
            (fun x sits => by rw [markerAt] at sits; cases sits; simp)
            (fun x sits => by rw [placeAt_ofMarker ambMarker] at sits; cases sits; simp)
            (fun list place' holds notTouched => by
              simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at notTouched
              obtain ⟨notParent, notMover, notTarget⟩ := notTouched
              exact ⟨List.mem_filter.mpr ⟨holds.1, by simp [placedAt, markerAt, Ne.symm notParent]⟩,
                List.mem_filter.mpr ⟨holds.2.1, by
                  simp [placedAt, placeAt_capability inListed, Ne.symm notMover]⟩,
                List.mem_filter.mpr ⟨holds.2.2, by simp [placedAt, destinationAt, Ne.symm notParent]⟩⟩)
            (fun list holds start reached' x inTouched => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at inTouched
              rcases inTouched with rfl | rfl | rfl
              · exact reached'
              · exact Reaches.extend reached' holds.1 markerAt (by simp [childOf, markers])
              · exact Reaches.extend reached' holds.2.2 destinationAt (by simp [childOf, markers]))
            (fun list holds => ⟨_, holds.2.2, by simp [placedAt, destinationAt]⟩)
            (fun list holds sub fuel' enough' => enter_local children grows unique typed moverNameVar targetNameVar
              decomposed groupPlaced groupChildren groupTyped sub holds.1 holds.2.1 holds.2.2 apartTargets fuel'
              enough')
            reached rfl (List.Sublist.refl _) ⟨markerIn, capabilityIn, destinationIn⟩ fuel (by omega)
          exact ⟨result, step, equivalent⟩
      | false =>
          simp only [LocRedex.capabilityPart, LocRedex.markerPart, LocRedex.movedPart, LocRedex.continuationOf,
            LocRedex.keptParts, LocRedex.capability, LocRedex.before, LocRedex.after, Bool.false_eq_true, if_false]
            at capabilityIn markerIn keptIn twoParts decomposed continuationFacts ⊢
          have outListed : "LOut" ∈ capabilities := by simp [capabilities]
          have ambMarker : "LAmb" ∈ markers := by simp [markers]
          obtain ⟨groupPlaced, groupChildren, groupTyped⟩ := continuationFacts rfl outListed
          have destinationIn := keptIn _ List.mem_cons_self
          have moverNameVar : isVariable moverName = true :=
            (well.names _ markerIn moverName (by simp [nameOf, markers])).1
          have targetNameVar := WellLocated.capabilityName well capabilityIn outListed
          obtain ⟨moverTyped, moverNameTyped⟩ := namesTyped markerIn ambMarker
          have marker'Typed : HasType locatedCalc free (List.replicate count nameType ++ bound)
              (.apply "LAmb" [parent, mover, moverName]) procType :=
            Mettapedia.Languages.ProcessCalculi.Ambient.Encoding.marker_typed (placeTyped destinationIn) moverTyped
              moverNameTyped
          have destinationAt : placeAt (.apply "LAmb" [parent, target, targetName]) = some parent :=
            placeAt_ofMarker ambMarker _ _ _
          have markerAt : placeAt (.apply "LAmb" [target, mover, moverName]) = some target :=
            placeAt_ofMarker ambMarker _ _ _
          have reached := WellLocated.reached well _ destinationIn parent destinationAt
          obtain ⟨result, step, equivalent⟩ := path_step (redexPlace := parent) (touched := [parent, target, mover])
            (home := mover)
            (Holds := fun list => Pattern.apply "LAmb" [target, mover, moverName] ∈ list ∧
              Pattern.apply "LOut" [mover, targetName, continuation] ∈ list ∧
              Pattern.apply "LAmb" [parent, target, targetName] ∈ list) (extra := 6)
            children grows unique markersOf typed groupPlaced groupTyped marker'Typed (by simp)
            (fun x sits => by rw [placeAt_capability outListed] at sits; cases sits; simp)
            (fun x sits => by rw [markerAt] at sits; cases sits; simp)
            (fun x sits => by rw [placeAt_ofMarker ambMarker] at sits; cases sits; simp)
            (fun list place' holds notTouched => by
              simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at notTouched
              obtain ⟨notParent, notTarget, notMover⟩ := notTouched
              exact ⟨List.mem_filter.mpr ⟨holds.1, by simp [placedAt, markerAt, Ne.symm notTarget]⟩,
                List.mem_filter.mpr ⟨holds.2.1, by
                  simp [placedAt, placeAt_capability outListed, Ne.symm notMover]⟩,
                List.mem_filter.mpr ⟨holds.2.2, by simp [placedAt, destinationAt, Ne.symm notParent]⟩⟩)
            (fun list holds start reached' x inTouched => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at inTouched
              have toTarget : Reaches list start target :=
                Reaches.extend reached' holds.2.2 destinationAt (by simp [childOf, markers])
              rcases inTouched with rfl | rfl | rfl
              · exact reached'
              · exact toTarget
              · exact Reaches.extend toTarget holds.1 markerAt (by simp [childOf, markers]))
            (fun list holds => ⟨_, holds.2.2, by simp [placedAt, destinationAt]⟩)
            (fun list holds sub fuel' enough' => exit_local children grows unique typed moverNameVar targetNameVar
              decomposed groupPlaced groupChildren groupTyped sub holds.1 holds.2.1 holds.2.2 fuel' enough')
            reached rfl (List.Sublist.refl _) ⟨markerIn, capabilityIn, destinationIn⟩ fuel (by omega)
          exact ⟨result, step, equivalent⟩

/-! ## Padding, renaming and restrictions -/

open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (rename rename_apply rename_lambda rename_multiLambda rename_subst
  rename_collection rename_bvar rename_fvar)
open Mettapedia.Languages.ProcessCalculi.Ambient.Mobile (amb)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (FreeIn)

theorem asBag_rename (relabel : Nat → Nat) (process : Pattern) :
    asBag (rename relabel process) = rename relabel (asBag process) := by
  cases process with
  | collection kind elements rest => cases kind <;> cases rest <;> simp [asBag, rename_collection]
  | bvar index => simp [asBag, rename_collection, rename_bvar]
  | fvar name => simp [asBag, rename_collection, rename_fvar]
  | apply label arguments => simp [asBag, rename_collection, rename_apply]
  | lambda binder body => simp [asBag, rename_collection, rename_lambda]
  | multiLambda arity binders body => simp [asBag, rename_collection, rename_multiLambda]
  | subst body replacement => simp [asBag, rename_collection, rename_subst]

/-- A padded content uses no variable the content does not. -/
theorem freeIn_of_asBag {process : Pattern} {index : Nat} (free : FreeIn index (asBag process)) :
    FreeIn index process := by
  have single : FreeIn index (.collection .hashBag [process] none) → FreeIn index process := fun inSingle => by
    obtain ⟨element, member, elementFree⟩ := Mettapedia.OSLF.MeTTaIL.CanonicalBags.freeIn_collection.mp inSingle
    rw [List.mem_singleton] at member
    subst member
    exact elementFree
  cases process with
  | collection kind elements rest => cases kind <;> cases rest <;> first | exact free | exact single free
  | _ => exact single free

theorem padApply_rename (relabel : Nat → Nat) (label : String) (arguments : List Pattern) :
    padApply label (arguments.map (rename relabel)) = rename relabel (padApply label arguments) := by
  match arguments with
  | [name, content] =>
      simp only [List.map_cons, List.map_nil, padApply]
      split_ifs with isAmb
      · rw [rename_apply, List.map_cons, List.map_cons, List.map_nil, asBag_rename]
      · rw [rename_apply]
        rfl
  | [] => simp [padApply, rename_apply]
  | [_] => simp [padApply, rename_apply]
  | _ :: _ :: _ :: _ => simp [padApply, rename_apply]

/-- **Padding commutes with renaming.** -/
theorem padA_rename (pattern : Pattern) : ∀ relabel : Nat → Nat,
    padA (rename relabel pattern) = rename relabel (padA pattern) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro relabel; rfl
  | hfvar name => intro relabel; rfl
  | happly label arguments recurse =>
      intro relabel
      rw [rename_apply]
      simp only [padA, padAList_eq_map, List.map_map]
      have argumentsIs : arguments.map (padA ∘ rename relabel) = (arguments.map padA).map (rename relabel) := by
        rw [List.map_map]
        exact List.map_congr_left fun argument member => recurse argument member relabel
      rw [argumentsIs]
      exact padApply_rename relabel label (arguments.map padA)
  | hlambda binder body recurse =>
      intro relabel
      rw [rename_lambda]
      simp only [padA]
      rw [rename_lambda, recurse]
  | hmultiLambda arity binders body recurse =>
      intro relabel
      rw [rename_multiLambda]
      simp only [padA]
      rw [rename_multiLambda, recurse]
  | hsubst body replacement recurseBody recurseReplacement =>
      intro relabel
      rw [rename_subst]
      simp only [padA]
      rw [rename_subst, recurseBody, recurseReplacement]
  | hcollection kind elements rest recurse =>
      intro relabel
      rw [rename_collection]
      simp only [padA, padAList_eq_map]
      rw [rename_collection, List.map_map, List.map_map]
      congr 1
      exact List.map_congr_left fun element member => recurse element member relabel

/-- **Padding commutes with restrictions.** -/
theorem padA_restricts : ∀ (count : Nat) (process : Pattern),
    padA (Prenex.restricts ambientBlock count process) = Prenex.restricts ambientBlock count (padA process)
  | 0, _ => rfl
  | count + 1, process => by
      rw [Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Prenex.restricts_succ,
        Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Prenex.restricts_succ]
      simp only [padA, padAList_eq_map, List.map_cons, List.map_nil, padApply]
      rw [padA_restricts count process]

/-- **Padding uses no variable the process does not.** -/
theorem freeIn_of_padA (pattern : Pattern) : ∀ {index : Nat}, FreeIn index (padA pattern) → FreeIn index pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro _ free; exact free
  | hfvar name => intro _ free; exact free
  | happly label arguments recurse =>
      intro index free
      simp only [padA, padAList_eq_map] at free
      rw [Mettapedia.OSLF.MeTTaIL.CanonicalBags.freeIn_apply]
      have fromPadded : ∀ argument ∈ arguments.map padA, FreeIn index argument →
          ∃ original ∈ arguments, FreeIn index original := fun argument member argumentFree => by
        obtain ⟨original, inArguments, rfl⟩ := List.mem_map.mp member
        exact ⟨original, inArguments, recurse original inArguments argumentFree⟩
      unfold padApply at free
      split at free
      · rename_i name content same
        split_ifs at free with isAmb
        · rw [Mettapedia.OSLF.MeTTaIL.CanonicalBags.freeIn_apply] at free
          obtain ⟨argument, member, argumentFree⟩ := free
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl
          · exact fromPadded _ (by rw [same]; simp) argumentFree
          · exact fromPadded _ (by rw [same]; simp) (freeIn_of_asBag argumentFree)
        · rw [Mettapedia.OSLF.MeTTaIL.CanonicalBags.freeIn_apply] at free
          obtain ⟨argument, member, argumentFree⟩ := free
          exact fromPadded argument (by rw [same]; exact member) argumentFree
      · rw [Mettapedia.OSLF.MeTTaIL.CanonicalBags.freeIn_apply] at free
        obtain ⟨argument, member, argumentFree⟩ := free
        exact fromPadded argument member argumentFree
  | hlambda binder body recurse =>
      intro index free
      simp only [padA] at free
      rw [Mettapedia.OSLF.MeTTaIL.CanonicalBags.freeIn_lambda] at free ⊢
      exact recurse free
  | hmultiLambda arity binders body recurse =>
      intro index free
      simp only [padA] at free
      cases free with
      | multiLambda inner => exact .multiLambda (recurse inner)
  | hsubst body replacement recurseBody recurseReplacement =>
      intro index free
      simp only [padA] at free
      cases free with
      | substBody inner => exact .substBody (recurseBody inner)
      | substReplacement inner => exact .substReplacement (recurseReplacement inner)
  | hcollection kind elements rest recurse =>
      intro index free
      simp only [padA, padAList_eq_map] at free
      rw [Mettapedia.OSLF.MeTTaIL.CanonicalBags.freeIn_collection] at free ⊢
      obtain ⟨element, member, elementFree⟩ := free
      obtain ⟨original, inElements, rfl⟩ := List.mem_map.mp member
      exact ⟨original, inElements, recurse original inElements elementFree⟩

/-! ## Steps under renaming, and the variables they use -/

theorem rename_amb (relabel : Nat → Nat) (name content : Pattern) :
    rename relabel (amb name content) = amb (rename relabel name) (rename relabel content) := by
  simp [amb, rename_apply]

/-- **A step renamed is a step.** -/
theorem AmbNuRawStep.rename_step {source target : Pattern} (step : AmbNuRawStep source target) :
    ∀ relabel : Nat → Nat, AmbNuRawStep (rename relabel source) (rename relabel target) := by
  induction step with
  | @«open» elements tail i hi j hj name process content capability boundary =>
      intro relabel
      rw [rename_collection, rename_collection, List.map_cons, List.map_cons, ← List.eraseIdx_map,
        ← List.eraseIdx_map]
      refine .open (tail := tail) i (by simpa using hi) j (by simpa [List.eraseIdx_map] using hj) (rename relabel name)
        (rename relabel process) (rename relabel content) ?_ ?_
      · rw [List.getElem_map, capability, rename_apply]
        rfl
      · rw [List.getElem_of_eq (List.eraseIdx_map _ _ _) (by simpa [List.eraseIdx_map] using hj), List.getElem_map,
          boundary, rename_amb]
  | @enter elements tail i hi j hj name target process host inner innerTail k hk mover capability destination =>
      intro relabel
      rw [rename_collection, rename_collection, List.map_cons, rename_amb, rename_collection, List.map_cons,
        List.map_cons, List.map_nil, rename_amb, rename_collection, List.map_cons, ← List.eraseIdx_map,
        ← List.eraseIdx_map, ← List.eraseIdx_map]
      refine .enter (tail := tail) (inner := inner.map (rename relabel)) (innerTail := innerTail) i
        (by simpa using hi) j (by simpa [List.eraseIdx_map] using hj) (rename relabel name) (rename relabel target)
        (rename relabel process) (rename relabel host) k (by simpa using hk) ?_ ?_ ?_
      · rw [List.getElem_map, mover, rename_amb, rename_collection]
      · rw [List.getElem_map, capability, rename_apply]
        rfl
      · rw [List.getElem_of_eq (List.eraseIdx_map _ _ _) (by simpa [List.eraseIdx_map] using hj), List.getElem_map,
          destination, rename_amb]
  | @exit contents tail i hi name parent process inner innerTail k hk mover capability =>
      intro relabel
      rw [rename_amb, rename_collection, rename_collection, List.map_cons, List.map_cons, List.map_nil, rename_amb,
        rename_collection, List.map_cons, rename_amb, rename_collection, ← List.eraseIdx_map, ← List.eraseIdx_map]
      refine .exit (tail := tail) (inner := inner.map (rename relabel)) (innerTail := innerTail) i
        (by simpa using hi) (rename relabel name) (rename relabel parent) (rename relabel process) k
        (by simpa using hk) ?_ ?_
      · rw [List.getElem_map, mover, rename_amb, rename_collection]
      · rw [List.getElem_map, capability, rename_apply]
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

/-- **A step uses no variable its source does not.** -/
theorem AmbNuRawStep.freeIn_source {source target : Pattern} (step : AmbNuRawStep source target) :
    ∀ {index : Nat}, FreeIn index target → FreeIn index source := by
  have inBag : ∀ {elements : List Pattern} {tail : Option String} {element : Pattern} {index : Nat},
      element ∈ elements → FreeIn index element → FreeIn index (.collection .hashBag elements tail) :=
    fun member free => .element member free
  have inAmb : ∀ {name content : Pattern} {index : Nat}, (FreeIn index name ∨ FreeIn index content) →
      FreeIn index (amb name content) := by
    intro name content index free
    rcases free with free | free
    · exact .apply (List.mem_cons_self) free
    · exact .apply (List.mem_cons_of_mem _ List.mem_cons_self) free
  have inPair : ∀ {label : String} {first second : Pattern} {index : Nat}, FreeIn index second →
      FreeIn index (.apply label [first, second]) := fun free =>
    .apply (List.mem_cons_of_mem _ List.mem_cons_self) free
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
  induction step with
  | @«open» elements tail i hi j hj name process content capability boundary =>
      intro index free
      obtain ⟨element, member, elementFree⟩ := fromBag free
      simp only [List.mem_cons] at member
      rcases member with rfl | rfl | inRest
      · exact inBag (List.getElem_mem hi) (by rw [capability]; exact inPair elementFree)
      · exact inBag (List.mem_of_mem_eraseIdx (List.getElem_mem hj)) (by rw [boundary]; exact inAmb (.inr elementFree))
      · exact inBag (List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx inRest)) elementFree
  | @enter elements tail i hi j hj name target process host inner innerTail k hk mover capability destination =>
      intro index free
      have fromMover : (FreeIn index name ∨ (∃ element ∈ inner, FreeIn index element)) →
          FreeIn index (.collection .hashBag elements tail) := by
        intro found
        refine inBag (List.getElem_mem hi) ?_
        rw [mover]
        rcases found with free | ⟨element, member, free⟩
        · exact inAmb (.inl free)
        · exact inAmb (.inr (inBag member free))
      have fromDestination : (FreeIn index target ∨ FreeIn index host) →
          FreeIn index (.collection .hashBag elements tail) := fun found =>
        inBag (List.mem_of_mem_eraseIdx (List.getElem_mem hj)) (by rw [destination]; exact inAmb found)
      obtain ⟨element, member, elementFree⟩ := fromBag free
      simp only [List.mem_cons] at member
      rcases member with rfl | inRest
      · rcases fromAmb elementFree with targetFree | contentFree
        · exact fromDestination (.inl targetFree)
        · obtain ⟨item, itemIn, itemFree⟩ := fromBag contentFree
          simp only [List.mem_cons, List.not_mem_nil, or_false] at itemIn
          rcases itemIn with rfl | rfl
          · rcases fromAmb itemFree with nameFree | innerFree
            · exact fromMover (.inl nameFree)
            · obtain ⟨piece, pieceIn, pieceFree⟩ := fromBag innerFree
              simp only [List.mem_cons] at pieceIn
              rcases pieceIn with rfl | inErased
              · exact fromMover (.inr ⟨inner[k], List.getElem_mem hk, by
                  rw [capability]; exact inPair pieceFree⟩)
              · exact fromMover (.inr ⟨piece, List.mem_of_mem_eraseIdx inErased, pieceFree⟩)
          · exact fromDestination (.inr itemFree)
      · exact inBag (List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx inRest)) elementFree
  | @exit contents tail i hi name parent process inner innerTail k hk mover capability =>
      intro index free
      have fromMover : (FreeIn index name ∨ ∃ element ∈ inner, FreeIn index element) →
          FreeIn index (amb parent (.collection .hashBag contents tail)) := by
        intro found
        refine inAmb (.inr (inBag (List.getElem_mem hi) ?_))
        rw [mover]
        rcases found with free | ⟨element, member, free⟩
        · exact inAmb (.inl free)
        · exact inAmb (.inr (inBag member free))
      obtain ⟨element, member, elementFree⟩ := fromBag free
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · rcases fromAmb elementFree with nameFree | contentFree
        · exact fromMover (.inl nameFree)
        · obtain ⟨piece, pieceIn, pieceFree⟩ := fromBag contentFree
          simp only [List.mem_cons] at pieceIn
          rcases pieceIn with rfl | inErased
          · exact fromMover (.inr ⟨inner[k], List.getElem_mem hk, by rw [capability]; exact inPair pieceFree⟩)
          · exact fromMover (.inr ⟨piece, List.mem_of_mem_eraseIdx inErased, pieceFree⟩)
      · rcases fromAmb elementFree with parentFree | contentFree
        · exact inAmb (.inl parentFree)
        · obtain ⟨piece, pieceIn, pieceFree⟩ := fromBag contentFree
          exact inAmb (.inr (inBag (List.mem_of_mem_eraseIdx pieceIn) pieceFree))
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

/-! ## The step of a presentation -/

open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (dropIndex rename_comp rename_congr rename_id liftBVars_eq_rename
  shiftAbove restricts_congr restricts_add restricts_typed body_typed bag_body_equivalent)
open Mettapedia.Languages.ProcessCalculi.Ambient.Decoding (decodeForm decode_typed decode_object decode_unread
  readPlaced_succ)

/-- A bag of nothing does not step. -/
theorem bag_nil_no_step {tail : Option String} {result : Pattern}
    (step : AmbNuRawStep (.collection .hashBag [] tail) result) : False := by
  cases step with
  | «open» i hi => simp at hi
  | enter i hi => simp at hi
  | par i hi => simp at hi

/-- **A reaction of a well-located block steps the block's presentation**, to a process that, lifted past the root,
is the reacted block read back at the root. -/
theorem present_reacts {count : Nat} {components : List Pattern}
    (well : WellLocated (· = Pattern.bvar 0) (.bvar 0) ⟨count, components⟩)
    (typed : Members locatedCalc locatedBlock free (List.replicate count nameType ++ [nameType]) components)
    {redex : LocRedex} {rest : List Pattern} (split : components.Perm (redex.parts ++ rest))
    {owned : Nat} {group : List Pattern} (decomposed : decompose locatedBlock redex.continuationOf = ⟨owned, group⟩)
    (fuel : Nat) (enough : 3 * sizeList components + 9 ≤ fuel) :
    ∃ contractum, AmbNuRawStep (presentBlock ⟨count, components⟩) contractum ∧
      ProcEquiv ambientCoreCalc ambientBlock free [nameType] (liftBVars 0 1 contractum)
        (Prenex.toPattern ambientBlock (decodeForm (fuel + 1) (.bvar 0)
          ⟨count + owned, (reactList redex.capabilityPart redex.markerPart redex.movedPart components).map
            (liftBVars 0 owned) ++ group⟩)) := by
  set root := liftBVars 0 count (Pattern.bvar 0) with rootIs
  set reacted := reactList redex.capabilityPart redex.markerPart redex.movedPart components with reactedIs
  obtain ⟨result, step, equivalent⟩ := root_reacts (bound := [nameType]) well typed split decomposed fuel enough
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
    exact bag_nil_no_step step
  obtain ⟨result', bodyStep, related⟩ := body_step nonempty step
  have restricted := restricts_step count bodyStep
  have renamed := AmbNuRawStep.rename_step restricted (dropIndex 0)
  refine ⟨_, by rw [presentIs]; exact renamed, ?_⟩
  -- the contractum does not use the root
  have readIs : Prenex.restricts ambientBlock count (Prenex.body ambientBlock (readPlaced fuel root components)) =
      Prenex.toPattern ambientBlock (decodeForm (fuel + 1) (.bvar 0) ⟨count, components⟩) := by
    simp only [decodeForm, Prenex.toPattern]
    rfl
  have unused : ¬ FreeIn 0 (Prenex.restricts ambientBlock count result') := by
    intro used
    have sourceUsed := AmbNuRawStep.freeIn_source restricted used
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
  obtain ⟨result'Typed, -⟩ := step_typed bodyStep (padA_typed bodyTyped bodyObject) (padA_object _ bodyObject)
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

end Mettapedia.Languages.ProcessCalculi.Ambient.Steps
