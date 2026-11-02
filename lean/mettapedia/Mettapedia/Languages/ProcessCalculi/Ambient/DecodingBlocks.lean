import Mettapedia.Languages.ProcessCalculi.Ambient.DecodingTyped

/-!
# Reading back closed blocks

Closing a restriction over a block reads back as the restriction over the block's reading, up to the ambient laws
(`decode_close`): a restriction the block uses stays in place, and one it does not use is garbage.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Decoding

open Mettapedia.Languages.ProcessCalculi.Ambient.Comm (ambientCoreCalc)

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (liftIndex FreeIn)
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (Prenex Members ProcEquiv BlockSignature body_typed restricts_typed
  rename rename_comp rename_congr liftBVars_eq_rename shiftAbove mentions mentions_iff dropIndex close_sound
  garbage_equivalent)
open Mettapedia.Languages.ProcessCalculi.Ambient.Full (ambientBlock)
open Mettapedia.Languages.ProcessCalculi.Ambient.Located (locatedCalc locatedBlock locatedLanguage)
open Mettapedia.Languages.ProcessCalculi.Ambient.Encoding (nameType procType shiftName)

/-- A name read under one more binder is lifted past it. -/
theorem shiftName_eq (here : Pattern) : shiftName here = liftBVars 0 1 here := by
  rw [shiftName, liftBVars_eq_rename]
  congr 1

/-- **The read-back of a typed located block is a typed ambient process.** -/
theorem decodeForm_typed {free : FreeTypeContext} {bound : List TypeExpr} (fuel : Nat) (place : Pattern)
    {form : Prenex}
    (members : Members locatedCalc locatedBlock free (List.replicate form.count nameType ++ bound) form.components) :
    HasType ambientCoreCalc free bound (Prenex.toPattern ambientBlock (decodeForm fuel place form)) procType :=
  restricts_typed (language := ambientCoreCalc) (block := ambientBlock) _
    (body_typed ((decode_typed (free := free) fuel).1 place form members))

/-- Components that do not use the variable just past a block's restrictions are lifted past it again once it is
dropped. -/
theorem drop_lift_unused {count : Nat} {components : List Pattern}
    (unused : components.any (mentions count) = false) :
    (components.map (rename (dropIndex count))).map (rename (liftIndex count Nat.succ)) = components := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id components]
  refine List.map_congr_left fun component member => ?_
  simp only [Function.comp, id]
  have notFree : ¬ FreeIn count component := by
    intro free
    have mentioned := (mentions_iff component count).mpr free
    exact absurd (List.any_eq_true.mpr ⟨component, member, mentioned⟩) (by simp [unused])
  rw [rename_comp]
  conv_rhs => rw [← Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_id component]
  apply rename_congr
  intro index free
  have different : index ≠ count := fun same => notFree (same ▸ free)
  simp only [Function.comp, dropIndex, liftIndex, id]
  split_ifs <;> omega

/-- **Closing a restriction over a block reads back as the restriction over its reading**: a used restriction stays
in place, an unused one is garbage. -/
theorem decode_close {free : FreeTypeContext} {bound : List TypeExpr} (fuel : Nat) (here : Pattern) (form : Prenex)
    (members : Members locatedCalc locatedBlock free (List.replicate form.count nameType ++ (nameType :: bound))
      form.components) :
    ProcEquiv ambientCoreCalc ambientBlock free bound (Prenex.toPattern ambientBlock (decodeForm (fuel + 1) here form.close))
      (.apply "ANu" [.lambda none (Prenex.toPattern ambientBlock (decodeForm (fuel + 1) (shiftName here) form))]) := by
  have signature : BlockSignature locatedCalc locatedBlock := locatedLanguage.toBlockSignature
  obtain ⟨closedMembers, -⟩ := close_sound (language := locatedCalc) (block := locatedBlock) members
  obtain ⟨count, components⟩ := form
  by_cases used : components.any (mentions count) = true
  · have closed : (Prenex.mk count components).close = ⟨count + 1, components⟩ := by
      simp [Prenex.close, used, Prenex.restrict]
    rw [closed]
    have samePlace : liftBVars 0 (count + 1) here = liftBVars 0 count (shiftName here) := by
      rw [shiftName_eq, Mettapedia.Languages.ProcessCalculi.Ambient.Decoding.liftBVars_par_outer, Nat.add_comm]
    simp only [decodeForm, Prenex.toPattern, Prenex.restricts_succ, samePlace]
    exact .refl _
  · have unused : components.any (mentions count) = false := by simpa using used
    have closed : (Prenex.mk count components).close = ⟨count, components.map (rename (dropIndex count))⟩ := by
      simp [Prenex.close, unused]
    rw [closed] at closedMembers ⊢
    have renamed : Prenex.mk count components =
        (Prenex.mk count (components.map (rename (dropIndex count)))).renameOuter Nat.succ := by
      simp only [Prenex.renameOuter, drop_lift_unused unused]
    have shifted : shiftName here = rename Nat.succ here := rfl
    rw [renamed, shifted, (decode_rename (fuel + 1) Nat.succ_injective).1, toPattern_renameOuter]
    have liftedIs : rename Nat.succ (Prenex.toPattern ambientBlock
        (decodeForm (fuel + 1) here ⟨count, components.map (rename (dropIndex count))⟩)) =
        liftBVars 0 1 (Prenex.toPattern ambientBlock
          (decodeForm (fuel + 1) here ⟨count, components.map (rename (dropIndex count))⟩)) := by
      rw [liftBVars_eq_rename]
      congr 1
    rw [liftedIs]
    exact Relation.EqvGen.symm _ _ (garbage_equivalent (language := ambientCoreCalc) (block := ambientBlock)
      (decodeForm_typed (fuel + 1) here closedMembers))

/-! ## An ambient's marker beside its content -/

open Mettapedia.Languages.ProcessCalculi.Ambient.Full (amb_typed amb_fill boundary_equivalent)

/-- A marker sits at its parent. -/
theorem placeAt_marker (parent child name : Pattern) :
    placeAt (.apply "LAmb" [parent, child, name]) = some parent := by
  simp [placeAt, placeOf]

theorem childOf_marker (parent child name : Pattern) : childOf (.apply "LAmb" [parent, child, name]) = some child := by
  simp [childOf]

/-- A marker, opened or not, sits at its parent. -/
theorem placeAt_ofMarker {label : String} (isMarker : label ∈ markers) (parent child name : Pattern) :
    placeAt (.apply label [parent, child, name]) = some parent := by
  simp [placeAt, placeOf, isMarker]

theorem childOf_ofMarker {label : String} (isMarker : label ∈ markers) (parent child name : Pattern) :
    childOf (.apply label [parent, child, name]) = some child := by
  simp [childOf, isMarker]

/-- A place read under a block and one more binder is none of their variables. -/
theorem liftBVars_ne_bvar (count : Nat) (place : Pattern) {index : Nat} (below : index ≤ count) :
    liftBVars 0 (count + 1) place ≠ .bvar index := by
  cases place with
  | bvar outer => simp [liftBVars]; omega
  | _ => simp [liftBVars]

/-- **A marker beside its content, read back where the marker sits**: the ambient around the reading of the content
at the ambient's location, or that reading in place for an opened marker, under the content's restrictions. -/
theorem decode_marker {label : String} (isMarker : label ∈ markers) (fuel : Nat) (here name : Pattern)
    (isName : isVariable name = true) {form : Prenex} (rooted : Rooted (.bvar 0) form) :
    decodeForm (fuel + 3) (shiftName here) ((Prenex.atom (.apply label [shiftName here, .bvar 0, name])).par form) =
      ⟨form.count, [wrapContent label (liftBVars 0 form.count name)
        (Prenex.body ambientBlock (readPlaced fuel (.bvar form.count) form.components))]⟩ := by
  obtain ⟨count, components⟩ := form
  obtain ⟨placed, children⟩ := rooted
  simp only at placed children
  set top := liftBVars 0 count (shiftName here) with topIs
  have topApart : ∀ index ≤ count, top ≠ .bvar index := fun index below => by
    rw [topIs, shiftName_eq, liftBVars_par_outer, Nat.add_comm]
    exact liftBVars_ne_bvar count here below
  have markerIs : liftBVars 0 count (.apply label [shiftName here, .bvar 0, name]) =
      .apply label [top, .bvar count, liftBVars 0 count name] := by
    simp [topIs, liftBVars, Mettapedia.OSLF.MeTTaIL.Substitution.liftBVarsList_eq_map]
  have componentsSame : components.map (liftBVars count 0) = components := by
    conv_rhs => rw [← List.map_id components]
    exact List.map_congr_left fun component _ => Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero component count
  -- no component of the content sits where the marker sits
  have apart : ∀ component ∈ components, placedAt top component = false := by
    intro component member
    cases found : placeAt component with
    | none => simp [placedAt, found]
    | some at' =>
        have different : at' ≠ top := by
          rcases placed component member at' found with rfl | ⟨index, below, rfl⟩
          · exact fun same => topApart count (Nat.le_refl _) (by simpa [liftBVars] using same.symm)
          · exact fun same => topApart index (Nat.le_of_lt below) same.symm
        simp [placedAt, found, different]
  simp only [decodeForm, Prenex.par, Prenex.atom, Nat.zero_add, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, markerIs, componentsSame]
  congr 1
  rw [readPlaced_succ]
  have filtered : (Pattern.apply label [top, .bvar count, liftBVars 0 count name] :: components).filter
      (placedAt top) = [.apply label [top, .bvar count, liftBVars 0 count name]] := by
    rw [List.filter_cons, if_pos (by simp [placedAt, placeAt_ofMarker isMarker]), List.filter_eq_nil_iff.mpr
      (fun component member => by simp [apart component member])]
  rw [filtered, List.map_singleton]
  have nameVariable : isVariable (liftBVars 0 count name) = true := by
    cases name <;> simp [isVariable, liftBVars] at isName ⊢
  simp only [readComponent, if_pos isMarker, nameVariable, if_true]
  -- the ambient's content is everything else
  have elsewhereIs : (Pattern.apply label [top, .bvar count, liftBVars 0 count name] :: components).filter
      (fun other => !placedAt (liftBVars 0 count (shiftName here)) other) = components := by
    rw [← topIs, List.filter_cons, if_neg (by simp [placedAt, placeAt_ofMarker isMarker])]
    conv_rhs => rw [← List.filter_true components]
    exact List.filter_congr fun component member => by simp [apart component member]
  rw [elsewhereIs]

/-- **An ambient's name crosses the restrictions of its content**: `(νx̄) m↑[P] ≡ m[(νx̄) P]`. -/
theorem restricts_amb_equivalent {free : FreeTypeContext} : ∀ (count : Nat) {bound : List TypeExpr}
    {name process : Pattern}, HasType ambientCoreCalc free bound name nameType →
    HasType ambientCoreCalc free (List.replicate count nameType ++ bound) process procType →
    ProcEquiv ambientCoreCalc ambientBlock free bound
      (Prenex.restricts ambientBlock count (.apply "AAmb" [liftBVars 0 count name, process]))
      (.apply "AAmb" [name, Prenex.restricts ambientBlock count process])
  | 0, bound, name, process, _, _ => by
      simp only [Prenex.restricts, Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero]
      exact .refl _
  | count + 1, bound, name, process, nameTyped, processTyped => by
      have liftedTyped : HasType ambientCoreCalc free (nameType :: bound) (liftBVars 0 1 name) nameType := by
        simpa using Mettapedia.GSLT.LanguageDef.RestrictionBlocks.lift_typed (language := ambientCoreCalc)
          (inner := []) (inserted := [nameType]) (outer := bound) nameTyped
      have inner := restricts_amb_equivalent count (bound := nameType :: bound) (name := liftBVars 0 1 name)
        (process := process) liftedTyped (by simpa [List.replicate_succ', List.append_assoc] using processTyped)
      rw [Mettapedia.GSLT.LanguageDef.RestrictionBlocks.liftBVars_zero_add] at inner
      rw [Prenex.restricts_succ, Prenex.restricts_succ]
      refine .trans _ _ _ (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.restrict_fill (language := ambientCoreCalc)
        (block := ambientBlock) inner) ?_
      exact Relation.EqvGen.symm _ _ (boundary_equivalent nameTyped
        (restricts_typed (language := ambientCoreCalc) (block := ambientBlock) count
          (by simpa [List.replicate_succ', List.append_assoc] using processTyped)))

/-- **A marker's name crosses the restrictions of its content**, the marker opened or not. -/
theorem restricts_wrapContent_equivalent {free : FreeTypeContext} (label : String) (count : Nat)
    {bound : List TypeExpr} {name process : Pattern} (nameTyped : HasType ambientCoreCalc free bound name nameType)
    (processTyped : HasType ambientCoreCalc free (List.replicate count nameType ++ bound) process procType) :
    ProcEquiv ambientCoreCalc ambientBlock free bound
      (Prenex.restricts ambientBlock count (wrapContent label (liftBVars 0 count name) process))
      (wrapContent label name (Prenex.restricts ambientBlock count process)) := by
  unfold wrapContent
  split_ifs
  · exact restricts_amb_equivalent count nameTyped processTyped
  · exact .refl _

end Mettapedia.Languages.ProcessCalculi.Ambient.Decoding
