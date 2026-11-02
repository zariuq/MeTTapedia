import Mettapedia.Languages.ProcessCalculi.Ambient.ReadWell
import Mettapedia.Languages.ProcessCalculi.Ambient.DecodingCanonForm

/-!
# A step of an ambient process, matched at a presentation

A step of a closed object ambient process is matched by a step of one of its presentations (`presented`). The step
is a reaction of an unfolding of the process's root canonical block (`root_reaction`); the unfolding, presented,
steps (`present_reacts`) to a process reading back as the reacted block; and the reacted block reads back as the
step's contractum (`reacted_reads`). The reacted block is equivalent, in the located calculus, to what the redex
leaves beside the rest (`reacted_equivalent`), hence to the located form of the contractum, so the two have one
canonical block, and a well-located block reads back as its canonical block does (`decode_canonForm`).

A presentation reads back under a restriction for each location of its block, which it never uses. Dropping the
unused outermost restrictions (`pruneTop`) keeps the process (`pruneTop_facts`) and its steps (`pruneTop_step`), so a
step is matched at a presentation without them too (`presented_pruned`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Steps

open Mettapedia.Languages.ProcessCalculi.Ambient.Comm (ambientCoreCalc coreSignature)

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (engineBasePremises)
open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationEquiv)
open Mettapedia.GSLT.LanguageDef.WellSorted (HasType FreeTypeContext isObjectPattern)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (Prenex Members ProcEquiv BlockSignature decompose canonP canonR
  rename rename_id sizeList presentationDepth mem_unfoldings restrictionsBind_of_typed canonR_complete restricts_typed
  body_typed bag_body_equivalent bag_perm_equivalent bag_fill bag_block_equivalent restricts_congr
  restricts_equation restricts_add lift_members isObject_liftBVars isObject_toPattern objects_of_decompose)
open Mettapedia.Languages.ProcessCalculi.Ambient.Full (AmbNuRawStep ambientBlock)
open Mettapedia.Languages.ProcessCalculi.Ambient.Located (locatedCalc locatedBlock locatedRepBlock locatedLanguage)
open Mettapedia.Languages.ProcessCalculi.Ambient.Encoding (NameContext nameType procType)
open Mettapedia.Languages.ProcessCalculi.Ambient.Decoding (WellLocated EncodeFacts childOf markers decodeForm
  decode_canonForm decompose_canonR decode_unfolds rootForm rootForm_facts root_locVariables names_base
  rename_succ_comp)

variable {free : FreeTypeContext}

/-! ## What a reaction leaves, in place -/

namespace LocRedex

/-- **The marker a redex rewrites places an ambient.** -/
theorem marker_child (redex : LocRedex) : ∃ child, childOf redex.markerPart = some child := by
  cases redex <;> simp [markerPart, childOf, markers]

/-- **The capability a redex fires is not the marker it rewrites.** -/
theorem capability_ne_marker (redex : LocRedex) : redex.capabilityPart ≠ redex.markerPart := by
  cases redex with
  | move entering parent mover target moverName targetName continuation =>
      cases entering <;> simp [capabilityPart, markerPart, capability]
  | «open» place location name continuation => simp [capabilityPart, markerPart]

end LocRedex

/-- **What a reaction leaves, in place, is the rewritten marker beside the parts it keeps and the rest**, when the
marker is not among them. -/
theorem reactList_perm {redex : LocRedex} {components rest : List Pattern}
    (split : components.Perm (redex.parts ++ rest)) (markerOnce : redex.markerPart ∉ redex.keptParts ++ rest) :
    (reactList redex.capabilityPart redex.markerPart redex.movedPart components).Perm
      (redex.movedPart :: (redex.keptParts ++ rest)) := by
  have front : components.Perm (redex.capabilityPart :: redex.markerPart :: (redex.keptParts ++ rest)) :=
    split.trans ((LocRedex.parts_perm redex).append_right rest)
  have erased : (components.erase redex.capabilityPart).Perm (redex.markerPart :: (redex.keptParts ++ rest)) := by
    simpa using front.erase redex.capabilityPart
  unfold reactList
  have mapped := erased.map (fun component => if component = redex.markerPart then redex.movedPart else component)
  rw [List.map_cons, if_pos rfl] at mapped
  have othersSame : (redex.keptParts ++ rest).map
      (fun component => if component = redex.markerPart then redex.movedPart else component) =
      redex.keptParts ++ rest := by
    conv_rhs => rw [← List.map_id (redex.keptParts ++ rest)]
    exact List.map_congr_left fun component inOthers => by
      have different : component ≠ redex.markerPart := fun same => markerOnce (same ▸ inOthers)
      simp [different]
  rwa [othersSame] at mapped

/-- **A reaction of a well-located block leaves, in place, the rewritten marker beside the parts it keeps and the
rest**: the marker it rewrites sits once in the block. -/
theorem reacted_perm {isLoc : Pattern → Prop} {place : Pattern} {count : Nat} {components : List Pattern}
    (well : WellLocated isLoc place ⟨count, components⟩) {redex : LocRedex} {rest : List Pattern}
    (split : components.Perm (redex.parts ++ rest)) :
    (reactList redex.capabilityPart redex.markerPart redex.movedPart components).Perm
      (redex.movedPart :: (redex.keptParts ++ rest)) := by
  obtain ⟨child, isChild⟩ := redex.marker_child
  have twoParts : components.Perm (redex.markerPart :: redex.capabilityPart :: (redex.keptParts ++ rest)) :=
    split.trans (((LocRedex.parts_perm redex).append_right rest).trans (.swap _ _ _))
  have once := not_mem_of_perm_unique (keep := fun component => childOf component == some child)
    (well.unique_any child) twoParts (by simp [isChild])
  exact reactList_perm split fun inOthers => once (List.mem_cons_of_mem _ inOthers)

/-! ## The reacted block in the located calculus -/

/-- **The reacted block is what the redex leaves beside the rest**: the reacted components lifted past the
continuation's restrictions, beside the continuation's components, under the block's restrictions and the
continuation's, are typed and equivalent in the located calculus to what the redex leaves beside the rest under the
block's restrictions. -/
theorem reacted_equivalent {isLoc : Pattern → Prop} {place : Pattern} {bound : List TypeExpr} {count : Nat}
    {components : List Pattern} (well : WellLocated isLoc place ⟨count, components⟩)
    (typed : Members locatedCalc locatedBlock free (List.replicate count nameType ++ bound) components)
    {redex : LocRedex} {rest : List Pattern} (split : components.Perm (redex.parts ++ rest))
    {owned : Nat} {group : List Pattern} (decomposed : decompose locatedBlock redex.continuationOf = ⟨owned, group⟩) :
    Members locatedCalc locatedBlock free (List.replicate (count + owned) nameType ++ bound)
        ((reactList redex.capabilityPart redex.markerPart redex.movedPart components).map (liftBVars 0 owned) ++
          group) ∧
      EquationEquiv (engineBasePremises RelationEnv.empty) locatedCalc
        (Prenex.restricts locatedBlock count (.collection .hashBag (redex.result ++ rest) none))
        (Prenex.toPattern locatedBlock ⟨count + owned,
          (reactList redex.capabilityPart redex.markerPart redex.movedPart components).map (liftBVars 0 owned) ++
            group⟩) := by
  have signature : BlockSignature locatedCalc locatedBlock := locatedLanguage.toBlockSignature
  set reacted := reactList redex.capabilityPart redex.markerPart redex.movedPart components with reactedIs
  set inner := List.replicate count nameType ++ bound with innerIs
  -- what the redex leaves, typed
  have partsMembers : Members locatedCalc locatedBlock free inner redex.parts := fun part member =>
    typed part (split.symm.subset (List.mem_append_left _ member))
  have resultMembers := LocRedex.result_members redex partsMembers
  have movedTyped := resultMembers _ ((LocRedex.result_perm redex).symm.subset
    (List.mem_cons_of_mem _ List.mem_cons_self))
  have continuationTyped := resultMembers _ ((LocRedex.result_perm redex).symm.subset List.mem_cons_self)
  have reactedMembers : Members locatedCalc locatedBlock free inner reacted := fun element member => by
    rcases mem_reactList member with inComponents | rfl
    · exact typed element inComponents
    · exact movedTyped
  have sound := Mettapedia.GSLT.LanguageDef.RestrictionBlocks.decompose_sound (language := locatedCalc)
    (block := locatedBlock) continuationTyped
  have groupMembers : Members locatedCalc locatedBlock free (List.replicate owned nameType ++ inner) group := by
    have groupSound := sound.1
    rw [decomposed] at groupSound
    exact groupSound
  have continuationEquivalent : ProcEquiv locatedCalc locatedBlock free inner redex.continuationOf
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
  -- what the redex leaves beside the rest is the continuation beside the reacted components
  have leftMembers : Members locatedCalc locatedBlock free inner (redex.result ++ rest) := fun element member => by
    rcases List.mem_append.mp member with inResult | inRest
    · exact resultMembers element inResult
    · exact typed element (split.symm.subset (List.mem_append_right _ inRest))
  have leftPerm : (redex.result ++ rest).Perm (redex.continuationOf :: reacted) :=
    ((LocRedex.result_perm redex).append_right rest).trans (.cons _ (reacted_perm well split).symm)
  have reordered := (bag_perm_equivalent (language := locatedCalc) (block := locatedRepBlock) leftMembers
    leftPerm).toEquationEquiv
  -- the continuation, a block of restrictions over a bag
  have continuationBlock : ProcEquiv locatedCalc locatedBlock free inner redex.continuationOf
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

/-! ## The reacted block read back -/

/-- **The reacted block reads back as the step's contractum**, lifted past the root: it is equivalent in the located
calculus to the located form of the contractum, so the two have one canonical block, and a well-located block reads
back as its canonical block does. -/
theorem reacted_reads (names : NameContext free) {count : Nat} {components : List Pattern}
    (well : WellLocated (· = Pattern.bvar 0) (.bvar 0) ⟨count, components⟩)
    (typed : Members locatedCalc locatedBlock free (List.replicate count nameType ++ [nameType]) components)
    (objects : ∀ component ∈ components, isObjectPattern component = true)
    {redex : LocRedex} {rest : List Pattern} (split : components.Perm (redex.parts ++ rest))
    {owned : Nat} {group : List Pattern} (decomposed : decompose locatedBlock redex.continuationOf = ⟨owned, group⟩)
    {located target : Pattern} (locatedTyped : HasType locatedCalc free [nameType] located procType)
    (locatedObject : isObjectPattern located = true)
    (reaches : EquationEquiv (engineBasePremises RelationEnv.empty) locatedCalc
      (Prenex.restricts locatedBlock count (.collection .hashBag (redex.result ++ rest) none)) located)
    (facts : EncodeFacts free (· = .bvar 0) 0 [nameType] (canonP locatedRepBlock located) (rename Nat.succ target)) :
    ∃ least, ∀ fuel, least ≤ fuel → ProcEquiv ambientCoreCalc ambientBlock free [nameType]
      (Prenex.toPattern ambientBlock (decodeForm fuel (.bvar 0)
        ⟨count + owned, (reactList redex.capabilityPart redex.markerPart redex.movedPart components).map
          (liftBVars 0 owned) ++ group⟩))
      (rename Nat.succ target) := by
  have signature : BlockSignature locatedCalc locatedBlock := locatedLanguage.toBlockSignature
  have reactedWell := reacted_well well split decomposed
  obtain ⟨members, equivalent⟩ := reacted_equivalent well typed split decomposed
  set reacted := reactList redex.capabilityPart redex.markerPart redex.movedPart components with reactedIs
  -- the reacted block's components are objects
  have partsObjects : ∀ part ∈ redex.parts, isObjectPattern part = true := fun part member =>
    objects part (split.symm.subset (List.mem_append_left _ member))
  have resultObjects := LocRedex.result_objects redex partsObjects
  have movedObject := resultObjects _ ((LocRedex.result_perm redex).symm.subset
    (List.mem_cons_of_mem _ List.mem_cons_self))
  have continuationObject := resultObjects _ ((LocRedex.result_perm redex).symm.subset List.mem_cons_self)
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
      rcases mem_reactList inReacted with inComponents | rfl
      · exact objects _ inComponents
      · exact movedObject
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

/-! ## A step matched at a presentation -/

/-- **A step of a closed object ambient process is matched by a step of one of its presentations**, within three
times the ceiling of its root canonical block, to an equivalent contractum. -/
theorem presented (names : NameContext free) {source target : Pattern} (step : AmbNuRawStep source target)
    (typed : HasType ambientCoreCalc free [] source procType) (object : isObjectPattern source = true) :
    ∃ shown ∈ presentationsA (presentationDepth locatedRepBlock 3 (rootForm source)) source,
      ∃ contractum, AmbNuRawStep shown contractum ∧
        ProcEquiv ambientCoreCalc ambientBlock free [] contractum target := by
  obtain ⟨unfolded, unfolds, redex, rest, split, -, members, objects, located, locatedTyped, locatedObject, reaches,
    facts⟩ := root_reaction names (names_base names 1) step typed object
  have rootFacts := rootForm_facts names typed object
  obtain ⟨unfoldedWell, -⟩ := decode_unfolds (names_base names 1) unfolds rootFacts.1 rootFacts.2.1
  have shownIn : presentBlock unfolded ∈ presentationsA (presentationDepth locatedRepBlock 3 (rootForm source)) source :=
    List.mem_map.mpr ⟨unfolded, (mem_unfoldings _ _ _).mpr unfolds, rfl⟩
  obtain ⟨shownTyped, shownObject, -⟩ := presentation_facts names typed object _ _ shownIn
  obtain ⟨count, components⟩ := unfolded
  simp only at members objects split reaches
  generalize decomposed : decompose locatedBlock redex.continuationOf = form
  obtain ⟨owned, group⟩ := form
  obtain ⟨least, reads⟩ := reacted_reads names unfoldedWell members objects split decomposed locatedTyped
    locatedObject reaches facts
  obtain ⟨contractum, stepped, lifted⟩ := present_reacts unfoldedWell members split decomposed
    (max (3 * sizeList components + 9) least) (le_max_left _ _)
  have toTarget := Relation.EqvGen.trans _ _ _ lifted
    (reads _ (le_trans (le_max_right _ _) (Nat.le_succ _)))
  have succIs : rename Nat.succ target = liftBVars 0 1 target := by
    simpa [rename_id] using rename_succ_comp id target
  rw [succIs] at toTarget
  obtain ⟨contractumTyped, -⟩ := step_typed stepped shownTyped shownObject
  obtain ⟨targetTyped, -⟩ := step_typed step typed object
  exact ⟨_, shownIn, contractum, stepped, unlift_equivalent contractumTyped targetTyped toTarget⟩

/-! ## Presentations without unused restrictions -/

open Mettapedia.OSLF.MeTTaIL.CanonicalBags (FreeIn)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (mentions mentions_iff dropIndex shiftAbove rename_comp
  rename_congr liftBVars_eq_rename isObjectPattern_rename isObject_restriction garbage_equivalent restrict_fill
  restrict_typed drop_typed)


/-- **A process with its unused outermost restrictions dropped.** A located block reads back under a restriction for
each of its locations, which the read-back never uses; steps happen beneath them. -/
def pruneTop : Pattern → Pattern
  | .apply "ANu" [.lambda binder body] =>
      if mentions 0 (pruneTop body) then .apply "ANu" [.lambda binder (pruneTop body)]
      else rename (dropIndex 0) (pruneTop body)
  | other => other

/-- A pattern that does not use the outermost bound variable is the lift of its drop. -/
theorem lift_drop {pattern : Pattern} (unused : ¬ FreeIn 0 pattern) :
    liftBVars 0 1 (rename (dropIndex 0) pattern) = pattern := by
  rw [liftBVars_eq_rename, rename_comp]
  conv_rhs => rw [← rename_id pattern]
  refine rename_congr _ fun index used => ?_
  have positive : index ≠ 0 := fun same => unused (same ▸ used)
  simp only [Function.comp, shiftAbove, dropIndex, id]
  split_ifs <;> omega

/-- **An unused restriction is garbage**: the body, its bound variable dropped, is a process equivalent to the
restriction. -/
theorem garbage_dropped {bound : List TypeExpr} {pattern : Pattern}
    (typed : HasType ambientCoreCalc free (nameType :: bound) pattern procType) (unused : ¬ FreeIn 0 pattern) :
    HasType ambientCoreCalc free bound (rename (dropIndex 0) pattern) procType ∧
      ProcEquiv ambientCoreCalc ambientBlock free bound (.apply "ANu" [.lambda none pattern])
        (rename (dropIndex 0) pattern) := by
  have droppedTyped : HasType ambientCoreCalc free bound (rename (dropIndex 0) pattern) procType := by
    simpa using drop_typed (language := ambientCoreCalc) (inner := []) (outer := bound) typed unused
  have garbage := garbage_equivalent (language := ambientCoreCalc) (block := ambientBlock) droppedTyped
  rw [lift_drop unused] at garbage
  exact ⟨droppedTyped, garbage⟩

/-- **Dropping the unused outermost restrictions keeps a process**: typed, an object, equivalent. -/
theorem pruneTop_facts (pattern : Pattern) : ∀ {bound : List TypeExpr},
    HasType ambientCoreCalc free bound pattern procType → isObjectPattern pattern = true →
      HasType ambientCoreCalc free bound (pruneTop pattern) procType ∧ isObjectPattern (pruneTop pattern) = true ∧
        ProcEquiv ambientCoreCalc ambientBlock free bound pattern (pruneTop pattern) := by
  induction pattern using pruneTop.induct with
  | case1 binder body used recurse =>
      intro bound typed object
      obtain ⟨bodyTyped, -, rfl⟩ := coreSignature.restriction_typed typed
      rw [isObject_restriction] at object
      obtain ⟨prunedTyped, prunedObject, prunedEquivalent⟩ := recurse bodyTyped object
      rw [pruneTop, if_pos used]
      exact ⟨restrict_typed (language := ambientCoreCalc) (block := ambientBlock) prunedTyped,
        by rw [isObject_restriction]; exact prunedObject,
        restrict_fill (language := ambientCoreCalc) (block := ambientBlock) prunedEquivalent⟩
  | case2 binder body unused recurse =>
      intro bound typed object
      obtain ⟨bodyTyped, -, rfl⟩ := coreSignature.restriction_typed typed
      rw [isObject_restriction] at object
      obtain ⟨prunedTyped, prunedObject, prunedEquivalent⟩ := recurse bodyTyped object
      rw [pruneTop, if_neg unused]
      have notFree : ¬ FreeIn 0 (pruneTop body) := fun free => unused ((mentions_iff _ 0).mpr free)
      obtain ⟨droppedTyped, dropped⟩ := garbage_dropped prunedTyped notFree
      exact ⟨droppedTyped, by rw [isObjectPattern_rename]; exact prunedObject,
        .trans _ _ _ (restrict_fill (language := ambientCoreCalc) (block := ambientBlock) prunedEquivalent) dropped⟩
  | case3 other notRestriction =>
      intro bound typed object
      rw [pruneTop.eq_def]
      split
      · rename_i binder body
        exact absurd rfl (notRestriction binder body)
      · exact ⟨typed, object, .refl _⟩

/-- **A step under a restriction is a step of its body.** -/
theorem AmbNuRawStep.res_inv {binder : Option String} {body target : Pattern}
    (step : AmbNuRawStep (.apply "ANu" [.lambda binder body]) target) :
    ∃ inner, target = .apply "ANu" [.lambda none inner] ∧ AmbNuRawStep body inner := by
  generalize sourceIs : Pattern.apply "ANu" [.lambda binder body] = source at step
  cases step with
  | res binder' inner =>
      simp only [Pattern.apply.injEq, List.cons.injEq, Pattern.lambda.injEq, true_and, and_true] at sourceIs
      obtain ⟨-, rfl⟩ := sourceIs
      exact ⟨_, rfl, inner⟩
  | _ => simp [Mettapedia.Languages.ProcessCalculi.Ambient.Mobile.amb] at sourceIs

/-- **Dropping the unused outermost restrictions keeps the steps**: a step of a process is matched by a step of the
process without them, to an equivalent contractum. -/
theorem pruneTop_step (pattern : Pattern) : ∀ {bound : List TypeExpr} {target : Pattern},
    AmbNuRawStep pattern target → HasType ambientCoreCalc free bound pattern procType →
      isObjectPattern pattern = true →
      ∃ target', AmbNuRawStep (pruneTop pattern) target' ∧
        ProcEquiv ambientCoreCalc ambientBlock free bound target' target := by
  induction pattern using pruneTop.induct with
  | case1 binder body used recurse =>
      intro bound target step typed object
      obtain ⟨inner, rfl, innerStep⟩ := AmbNuRawStep.res_inv step
      obtain ⟨bodyTyped, -, rfl⟩ := coreSignature.restriction_typed typed
      rw [isObject_restriction] at object
      obtain ⟨inner', innerStep', innerEquivalent⟩ := recurse innerStep bodyTyped object
      rw [pruneTop, if_pos used]
      exact ⟨_, .res none innerStep', restrict_fill (language := ambientCoreCalc) (block := ambientBlock)
        innerEquivalent⟩
  | case2 binder body unused recurse =>
      intro bound target step typed object
      obtain ⟨inner, rfl, innerStep⟩ := AmbNuRawStep.res_inv step
      obtain ⟨bodyTyped, -, rfl⟩ := coreSignature.restriction_typed typed
      rw [isObject_restriction] at object
      obtain ⟨inner', innerStep', innerEquivalent⟩ := recurse innerStep bodyTyped object
      rw [pruneTop, if_neg unused]
      have notFree : ¬ FreeIn 0 (pruneTop body) := fun free => unused ((mentions_iff _ 0).mpr free)
      have innerUnused : ¬ FreeIn 0 inner' := fun free => notFree (AmbNuRawStep.freeIn_source innerStep' free)
      obtain ⟨prunedTyped, prunedObject, -⟩ := pruneTop_facts body bodyTyped object
      obtain ⟨inner'Typed, -⟩ := step_typed innerStep' prunedTyped prunedObject
      obtain ⟨-, dropped⟩ := garbage_dropped inner'Typed innerUnused
      exact ⟨_, AmbNuRawStep.rename_step innerStep' (dropIndex 0),
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

/-- **A step of a closed object ambient process is matched by a step of one of its presentations, without their
unused outermost restrictions**, to an equivalent contractum. -/
theorem presented_pruned (names : NameContext free) {source target : Pattern} (step : AmbNuRawStep source target)
    (typed : HasType ambientCoreCalc free [] source procType) (object : isObjectPattern source = true) :
    ∃ shown ∈ (presentationsA (presentationDepth locatedRepBlock 3 (rootForm source)) source).map pruneTop,
      ∃ contractum, AmbNuRawStep shown contractum ∧
        ProcEquiv ambientCoreCalc ambientBlock free [] contractum target := by
  obtain ⟨shown, shownIn, contractum, stepped, equivalent⟩ := presented names step typed object
  obtain ⟨shownTyped, shownObject, -⟩ := presentation_facts names typed object _ shown shownIn
  obtain ⟨contractum', stepped', equivalent'⟩ := pruneTop_step shown stepped shownTyped shownObject
  exact ⟨pruneTop shown, List.mem_map_of_mem shownIn, contractum', stepped', .trans _ _ _ equivalent' equivalent⟩

end Mettapedia.Languages.ProcessCalculi.Ambient.Steps
