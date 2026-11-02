import Mettapedia.Languages.ProcessCalculi.Ambient.Padding

/-!
# Unfoldings of a well-located block

Unfolding a replicated component puts a copy of its argument beside the block, the copy's restrictions innermost and
the block's components lifted past them (`Prenex.unfoldWith`). The copy sits where the replicated component sits, so
the unfolded block is well-located (`WellLocated.unfoldWith`): its locations are the block's and the copy's, read as
the block reads them and as the copy reads them inside the block.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Decoding

open Mettapedia.Languages.ProcessCalculi.Ambient.Comm (ambientCoreCalc)

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (Prenex rename rename_bvar rename_fvar rename_id liftBVars_eq_rename
  shiftAbove liftBVars_zero_add)

/-- **The locations marked in an unfolded block**: the block's, lifted past the copy's restrictions, and the
copy's. -/
theorem marked_unfold {count copies : Nat} {components copy : List Pattern}
    (kinds : ∀ component ∈ components, ComponentKind count component)
    (copyKinds : ∀ component ∈ copy, ComponentKind copies component) (index : Nat) :
    Marked (components.map (liftBVars 0 copies) ++ copy) index ↔
      (copies ≤ index ∧ Marked components (index - copies)) ∨ (index < copies ∧ Marked copy index) := by
  constructor
  · rintro ⟨component, member, isChild⟩
    rcases List.mem_append.mp member with inFirst | inCopy
    · obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp inFirst
      rw [liftBVars_eq_rename, childOf_rename] at isChild
      cases found : childOf original with
      | none => rw [found] at isChild; cases isChild
      | some child =>
          rw [found, Option.map_some, Option.some.injEq] at isChild
          obtain ⟨childIndex, below, rfl⟩ := childOf_bvar_of_kind (kinds original originalMember) found
          simp only [rename_bvar, shiftAbove, Nat.not_lt_zero, if_false, Pattern.bvar.injEq] at isChild
          subst isChild
          exact .inl ⟨by omega, original, originalMember, by rw [found]; simp⟩
    · obtain ⟨childIndex, below, same⟩ := childOf_bvar_of_kind (copyKinds component inCopy) isChild
      simp only [Pattern.bvar.injEq] at same
      subst same
      exact .inr ⟨below, component, inCopy, isChild⟩
  · rintro (⟨above, component, member, isChild⟩ | ⟨below, component, member, isChild⟩)
    · refine ⟨liftBVars 0 copies component, List.mem_append_left _ (List.mem_map.mpr ⟨component, member, rfl⟩), ?_⟩
      rw [liftBVars_eq_rename, childOf_rename, isChild, Option.map_some, rename_bvar]
      simp only [shiftAbove, Nat.not_lt_zero, if_false]
      congr 2
      omega
    · exact ⟨component, List.mem_append_right _ member, isChild⟩

/-- **How an unfolded block reads locations**: the block's components, lifted, as the block reads them; the copy's
components as the copy reads them inside the block. -/
theorem insideLoc_unfold {isLoc : Pattern → Prop} {count copies : Nat} {components copy : List Pattern}
    (kinds : ∀ component ∈ components, ComponentKind count component)
    (copyKinds : ∀ component ∈ copy, ComponentKind copies component) :
    (∀ pattern, isVariable pattern = true →
      (insideLoc isLoc (copies + count) (components.map (liftBVars 0 copies) ++ copy)
        (rename (shiftAbove 0 copies) pattern) ↔ insideLoc isLoc count components pattern)) ∧
    (∀ pattern, isVariable pattern = true →
      (insideLoc isLoc (copies + count) (components.map (liftBVars 0 copies) ++ copy) pattern ↔
        insideLoc (insideLoc isLoc count components) copies copy pattern)) := by
  have marked := marked_unfold (copies := copies) kinds copyKinds
  constructor
  · intro pattern isVar
    cases pattern with
    | bvar index =>
        simp only [rename_bvar, shiftAbove, Nat.not_lt_zero, if_false, insideLoc]
        by_cases below : index < count
        · simp only [show index + copies < copies + count by omega, below, if_true, marked]
          constructor
          · rintro (⟨-, isMarked⟩ | ⟨tooSmall, -⟩)
            · simpa using isMarked
            · omega
          · intro isMarked
            exact .inl ⟨by omega, by simpa using isMarked⟩
        · simp only [show ¬ index + copies < copies + count by omega, below, if_false]
          rw [show index + copies - (copies + count) = index - count by omega]
    | fvar name => simp [rename_fvar, insideLoc]
    | _ => simp [isVariable] at isVar
  · intro pattern isVar
    cases pattern with
    | bvar index =>
        simp only [insideLoc]
        by_cases below : index < copies
        · simp only [below, if_true, show index < copies + count by omega, marked]
          constructor
          · rintro (⟨tooBig, -⟩ | ⟨-, isMarked⟩)
            · omega
            · exact isMarked
          · intro isMarked
            exact .inr ⟨trivial, isMarked⟩
        · simp only [below, if_false]
          by_cases inside : index < copies + count
          · simp only [inside, if_true, marked, show index - copies < count by omega]
            constructor
            · rintro (⟨-, isMarked⟩ | ⟨tooSmall, -⟩)
              · exact isMarked
              · omega
            · intro isMarked
              exact .inl ⟨by omega, isMarked⟩
          · simp only [inside, if_false, show ¬ index - copies < count by omega]
            rw [show index - copies - count = index - (copies + count) by omega]
    | fvar name => simp [insideLoc]
    | _ => simp [isVariable] at isVar

/-- **The locations of an unfolded block nest**: the copy's locations sit deeper than every location of the block. -/
theorem Nested.unfold {count copies : Nat} {components copy : List Pattern}
    (nested : Nested count components) (copyNested : Nested copies copy)
    (kinds : ∀ component ∈ components, ComponentKind count component)
    (copyKinds : ∀ component ∈ copy, ComponentKind copies component) :
    Nested (copies + count) (components.map (liftBVars 0 copies) ++ copy) := by
  classical
  obtain ⟨depth, deeper⟩ := nested
  obtain ⟨copyDepth, copyDeeper⟩ := copyNested
  set ceiling := (Finset.range count).sup depth + 1 with ceilingIs
  have belowCeiling : ∀ index < count, depth index < ceiling := fun index below =>
    Nat.lt_succ_of_le (Finset.le_sup (f := depth) (Finset.mem_range.mpr below))
  refine ⟨fun index => if index < copies then copyDepth index + ceiling else depth (index - copies), ?_⟩
  intro component member index child below childBelow sits isChild
  rcases List.mem_append.mp member with inFirst | inCopy
  · obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp inFirst
    rw [liftBVars_eq_rename, placeAt_rename] at sits
    rw [liftBVars_eq_rename, childOf_rename] at isChild
    cases placed : placeAt original with
    | none => rw [placed] at sits; cases sits
    | some at' =>
        rw [placed, Option.map_some, Option.some.injEq] at sits
        cases found : childOf original with
        | none => rw [found] at isChild; cases isChild
        | some childPattern =>
            rw [found, Option.map_some, Option.some.injEq] at isChild
            obtain ⟨childIndex, childIn, rfl⟩ := childOf_bvar_of_kind (kinds original originalMember) found
            simp only [rename_bvar, shiftAbove, Nat.not_lt_zero, if_false, Pattern.bvar.injEq] at isChild
            subst isChild
            obtain ⟨placeIndex, rfl, mapped⟩ := rename_eq_bvar sits
            simp only [shiftAbove, Nat.not_lt_zero, if_false] at mapped
            subst mapped
            simp only [show ¬ placeIndex + copies < copies by omega, show ¬ childIndex + copies < copies by omega,
              if_false, Nat.add_sub_cancel]
            exact deeper original originalMember placeIndex childIndex (by omega) childIn placed found
  · obtain ⟨childIndex, childIn, same⟩ := childOf_bvar_of_kind (copyKinds component inCopy) isChild
    simp only [Pattern.bvar.injEq] at same
    subst same
    simp only [childIn, if_true]
    by_cases placeIn : index < copies
    · simp only [placeIn, if_true]
      have := copyDeeper component inCopy index child placeIn childIn sits isChild
      omega
    · simp only [placeIn, if_false]
      have := belowCeiling (index - copies) (by omega)
      omega

/-- **An unfolded block is well-located**: a copy well-located at the place where the replicated component sits,
read inside the block, beside the block's components lifted past the copy's restrictions. -/
theorem WellLocated.unfoldWith {isLoc : Pattern → Prop} {place : Pattern} {form copy : Prenex}
    (well : WellLocated isLoc place form) {at' : Pattern}
    (atPlaced : at' = liftBVars 0 form.count place ∨
      ∃ index < form.count, at' = .bvar index ∧ Marked form.components index)
    (copyWell : WellLocated (insideLoc isLoc form.count form.components) at' copy) :
    WellLocated isLoc place (form.unfoldWith copy) := by
  obtain ⟨count, components⟩ := form
  obtain ⟨copies, copyComponents⟩ := copy
  have kinds := well.kinds
  have copyKinds := copyWell.kinds
  have unique := well.unique
  have copyUnique := copyWell.unique
  simp only at kinds copyKinds unique copyUnique atPlaced
  obtain ⟨formLoc, copyLoc⟩ := insideLoc_unfold (isLoc := isLoc) kinds copyKinds
  have marked := marked_unfold (copies := copies) (components := components) (copy := copyComponents) kinds copyKinds
  have liftIs : ∀ cutoff shift, liftBVars cutoff shift = rename (shiftAbove cutoff shift) :=
    fun cutoff shift => funext fun pattern => liftBVars_eq_rename cutoff shift pattern
  have formHalf := WellLocated.embed (total := copies + count)
    (bigger := components.map (liftBVars 0 copies) ++ copyComponents)
    well (shiftAbove_injective 0 copies)
    (.inl (by rw [← liftIs, liftBVars_zero_add])) (fun index below => by simp [shiftAbove]; omega)
    (fun index below => by
      simp only [shiftAbove, Nat.not_lt_zero, if_false, marked]
      constructor
      · rintro (⟨-, isMarked⟩ | ⟨tooSmall, -⟩)
        · simpa using isMarked
        · omega
      · intro isMarked
        exact .inl ⟨by omega, by simpa using isMarked⟩) formLoc
  have copyHalf := WellLocated.embed (total := copies + count)
    (bigger := components.map (liftBVars 0 copies) ++ copyComponents) (relabel := id)
    copyWell Function.injective_id
    (by
      rcases atPlaced with rfl | ⟨index, below, rfl, isMarked⟩
      · exact .inl (by rw [rename_id, liftBVars_zero_add])
      · refine .inr ⟨index + copies, by omega, ?_, marked _ |>.mpr (.inl ⟨by omega, by simpa using isMarked⟩)⟩
        rw [rename_id, liftBVars_eq_rename, rename_bvar]
        simp [shiftAbove])
    (fun index below => by simp only [id]; omega)
    (fun index below => by
      simp only [id, marked]
      constructor
      · rintro (⟨tooBig, -⟩ | ⟨-, isMarked⟩)
        · omega
        · exact isMarked
      · intro isMarked
        exact .inr ⟨below, isMarked⟩)
    (fun pattern isVar => by rw [rename_id]; exact copyLoc pattern isVar)
  simp only [← liftIs] at formHalf
  have copyIs : copyComponents.map (rename id) = copyComponents := by
    conv_rhs => rw [← List.map_id copyComponents]
    exact List.map_congr_left fun component _ => rename_id component
  rw [copyIs] at copyHalf
  have both : ∀ component ∈ components.map (liftBVars 0 copies) ++ copyComponents, _ := fun component member =>
    (List.mem_append.mp member).elim (formHalf component) (copyHalf component)
  simp only [Prenex.unfoldWith]
  refine .intro well.placeIsLoc (fun component member => (both component member).1)
    (fun component member => (both component member).2.1) ?_ (fun component member => (both component member).2.2.1)
    (fun component member => (both component member).2.2.2.1)
    (fun component member => (both component member).2.2.2.2.1)
    (fun component member => (both component member).2.2.2.2.2.1)
    (Nested.unfold well.nested copyWell.nested kinds copyKinds)
    (fun component member => (both component member).2.2.2.2.2.2.1)
    (fun component member => (both component member).2.2.2.2.2.2.2.1)
    (fun component member => (both component member).2.2.2.2.2.2.2.2)
  intro index
  rw [List.filter_append, List.length_append]
  have formPart : (components.map (liftBVars 0 copies)).filter
      (fun component => childOf component == some (.bvar index)) =
      if copies ≤ index then (components.filter fun component => childOf component == some (.bvar (index - copies))).map
        (liftBVars 0 copies) else [] := by
    rw [List.filter_map]
    split_ifs with above
    · congr 1
      apply List.filter_congr
      intro component member
      simp only [Function.comp, liftIs, childOf_rename]
      cases found : childOf component with
      | none => simp
      | some child =>
          obtain ⟨childIndex, below, rfl⟩ := childOf_bvar_of_kind (kinds component member) found
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
          obtain ⟨childIndex, below, rfl⟩ := childOf_bvar_of_kind (kinds original originalMember) found
          simp [rename_bvar, shiftAbove] at isChild
          omega
  have copyPart : copyComponents.filter (fun component => childOf component == some (.bvar index)) =
      if index < copies then copyComponents.filter (fun component => childOf component == some (.bvar index))
      else [] := by
    split_ifs with below
    · rfl
    · rw [List.filter_eq_nil_iff]
      intro original originalMember isChild
      simp only [beq_iff_eq] at isChild
      obtain ⟨childIndex, childBelow, same⟩ := childOf_bvar_of_kind (copyKinds original originalMember) isChild
      simp only [Pattern.bvar.injEq] at same
      omega
  rw [formPart, copyPart]
  split_ifs with above below below
  · omega
  · simpa using unique (index - copies)
  · simpa using copyUnique index
  · simp


/-! ## An unfolding reads back as the block -/

open Mettapedia.GSLT.LanguageDef.WellSorted (HasType FreeTypeContext)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (Members ProcEquiv BaseContext normal decompose normal_sound
  decompose_sound restricts_congr restricts_add)
open Mettapedia.Languages.ProcessCalculi.Ambient.Full (ambientBlock)
open Mettapedia.Languages.ProcessCalculi.Ambient.Located (locatedCalc locatedBlock locatedRepBlock)
open Mettapedia.Languages.ProcessCalculi.Ambient.Encoding (nameType)

/-- **An unfolding reads back as the block**: the copy beside the block is a copy group of the replicated component,
absorbed at its place at any depth; the unfolded block is well-located. -/
theorem decode_unfoldWith {free : FreeTypeContext} {isLoc : Pattern → Prop} {outer : Nat} {bound : List TypeExpr}
    {form : Prenex} {argument : Pattern} (well : WellLocated isLoc (.bvar outer) form)
    (context : BaseContext free bound)
    (members : Members locatedCalc locatedBlock free (List.replicate form.count nameType ++ bound) form.components)
    (replicated : Pattern.apply "LRep" [argument] ∈ form.components) :
    WellLocated isLoc (.bvar outer) (form.unfoldWith (normal locatedRepBlock (decompose locatedBlock argument))) ∧
      ∃ least, ∀ fuel, least ≤ fuel → ProcEquiv ambientCoreCalc ambientBlock free bound
        (Prenex.toPattern ambientBlock (decodeForm fuel (.bvar outer)
          (form.unfoldWith (normal locatedRepBlock (decompose locatedBlock argument)))))
        (Prenex.toPattern ambientBlock (decodeForm fuel (.bvar outer) form)) := by
  obtain ⟨count, components⟩ := form
  have kinds : ∀ component ∈ components, ComponentKind count component := well.kinds
  have unique : ∀ index, (components.filter fun component => childOf component == some (.bvar index)).length ≤ 1 :=
    well.unique
  have members : Members locatedCalc locatedBlock free (List.replicate count nameType ++ bound) components := members
  have replicated : Pattern.apply "LRep" [argument] ∈ components := replicated
  -- where the replicated component sits
  obtain ⟨at', sits⟩ : ∃ at', placeAt (.apply "LRep" [argument]) = some at' :=
    Option.isSome_iff_exists.mp (well.repsPlaced _ replicated argument rfl)
  have atPlaced := well.placed _ replicated at' sits
  have argumentWell : WellLocated (insideLoc isLoc count components) at' (decompose locatedBlock argument) := by
    cases well with
    | intro _ _ _ _ _ _ reps _ _ _ _ _ => exact reps _ replicated argument at' rfl sits
  obtain ⟨home, rfl⟩ : ∃ home, at' = .bvar home := by
    rcases atPlaced with same | ⟨index, -, same, -⟩
    · exact ⟨outer + count, by simpa [liftBVars] using same⟩
    · exact ⟨index, same⟩
  -- the copy: the argument's canonical block, well-located at the replicated component's place
  have innerContext : BaseContext free (List.replicate count nameType ++ bound) := context.replicate count "Name"
  have signature : Mettapedia.GSLT.LanguageDef.RestrictionBlocks.BlockSignature locatedCalc locatedBlock :=
    Mettapedia.Languages.ProcessCalculi.Ambient.Located.locatedLanguage.toBlockSignature
  have argumentTyped := rep_inv (members _ replicated)
  have argumentMembers := (decompose_sound (language := locatedCalc) (block := locatedBlock) argumentTyped).1
  obtain ⟨copyWell, copyReads⟩ := decode_normal (decompose locatedBlock argument) argumentWell
    (insideLoc_locVariables isLoc count components) innerContext argumentMembers
  have copyMembers := (normal_sound (language := locatedCalc) (block := locatedRepBlock) innerContext
    argumentMembers).1
  refine ⟨well.unfoldWith atPlaced copyWell, ?_⟩
  set copy := normal locatedRepBlock (decompose locatedBlock argument) with copyIs
  -- the copy reads back as the argument
  set floor := 3 * (decompose locatedBlock argument).mass + 3 + 3 * copy.mass + 3 with floorIs
  have copyEquiv : ∀ fuel, floor ≤ fuel → ProcEquiv ambientCoreCalc ambientBlock free
      (List.replicate count nameType ++ bound)
      (Prenex.restricts ambientBlock copy.count
        (Prenex.body ambientBlock (readPlaced (fuel + 2) (liftBVars 0 copy.count (.bvar home)) copy.components)))
      (Prenex.toPattern ambientBlock (decodeForm fuel (.bvar home) (decompose locatedBlock argument))) := by
    intro fuel enough
    have reads := copyReads (fuel + 3) (by omega) (by omega)
    rw [decodeForm_settled (.bvar home) (decompose locatedBlock argument) (first := fuel + 3) (second := fuel)
      (by omega) (by omega)] at reads
    exact reads
  have groupPlaced : ∀ component ∈ copy.components, ∀ at', placeAt component = some at' →
      at' = liftBVars 0 copy.count (.bvar home) ∨ ∃ index < copy.count, at' = .bvar index := by
    intro component member at' found
    rcases copyWell.placed component member at' found with same | ⟨index, below, same, -⟩
    · exact .inl same
    · exact .inr ⟨index, below, same⟩
  have groupChildren : ∀ component ∈ copy.components, ∀ child, childOf component = some child →
      ∃ index < copy.count, child = .bvar index := fun component member child isChild =>
    childOf_bvar_of_kind (copyWell.kinds component member) isChild
  have absorbed := absorb_core (free := free) (bound := List.replicate count nameType ++ bound) copyMembers
    groupPlaced groupChildren copyEquiv
  refine ⟨floor + 3 + 2 * components.length, fun fuel enough => ?_⟩
  obtain ⟨step, rfl⟩ : ∃ step, fuel = step + 1 := ⟨fuel - 1, by omega⟩
  have top : ∀ component ∈ components, childOf component ≠ some (liftBVars 0 count (.bvar outer)) := by
    intro component member isChild
    obtain ⟨index, below, same⟩ := childOf_bvar_of_kind (kinds component member) isChild
    simp [liftBVars] at same
    omega
  have namesVariable : ∀ component ∈ components, ∀ name, nameOf component = some name → isVariable name = true :=
    fun component member name named => (well.names component member name named).1
  have uniqueAll : ∀ child, (components.filter fun component => childOf component == some child).length ≤ 1 := by
    intro child
    cases child with
    | bvar index => exact unique index
    | _ =>
        rw [List.filter_eq_nil_iff.mpr]
        · simp
        intro component member isChild
        simp only [beq_iff_eq] at isChild
        obtain ⟨index, -, same⟩ := childOf_bvar_of_kind (kinds component member) isChild
        cases same
  have related := absorbed step members replicated sits top uniqueAll namesVariable (by omega)
  have closed := restricts_congr (language := ambientCoreCalc) (block := ambientBlock) count related
  rw [restricts_add, liftBVars_zero_add] at closed
  rw [Nat.add_comm count copy.count] at closed
  simp only [decodeForm, Prenex.unfoldWith, Prenex.toPattern]
  exact closed


open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (UnfoldsWithin UnfoldsWithin.members UnfoldsWithin.single)

/-- **Every unfolding of a well-located block is well-located and reads back as the block.** -/
theorem decode_unfolds {free : FreeTypeContext} {isLoc : Pattern → Prop} {outer : Nat} {bound : List TypeExpr}
    (context : BaseContext free bound) {depth : Nat} {form unfolded : Prenex}
    (unfolds : UnfoldsWithin locatedRepBlock depth form unfolded) :
    WellLocated isLoc (.bvar outer) form →
      Members locatedCalc locatedBlock free (List.replicate form.count nameType ++ bound) form.components →
      WellLocated isLoc (.bvar outer) unfolded ∧
        ∃ least, ∀ fuel, least ≤ fuel → ProcEquiv ambientCoreCalc ambientBlock free bound
          (Prenex.toPattern ambientBlock (decodeForm fuel (.bvar outer) unfolded))
          (Prenex.toPattern ambientBlock (decodeForm fuel (.bvar outer) form)) := by
  induction unfolds with
  | refl => exact fun well _ => ⟨well, 0, fun _ _ => .refl _⟩
  | @step depth form next argument member rest recurse =>
      intro well members
      obtain ⟨stepWell, stepLeast, stepReads⟩ := decode_unfoldWith well context members member
      have stepMembers := UnfoldsWithin.members (language := locatedCalc) context (UnfoldsWithin.single member)
        members
      obtain ⟨nextWell, nextLeast, nextReads⟩ := recurse stepWell stepMembers
      exact ⟨nextWell, stepLeast + nextLeast, fun fuel enough =>
        .trans _ _ _ (nextReads fuel (by omega)) (stepReads fuel (by omega))⟩

end Mettapedia.Languages.ProcessCalculi.Ambient.Decoding
