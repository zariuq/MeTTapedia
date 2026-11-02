import Mettapedia.Languages.ProcessCalculi.Ambient.EncodingReacts

/-!
# Entering and leaving in located form

An ambient entering a sibling, or leaving its parent, is in located form a reaction of three located atoms at the
front of a block with two restrictions: the target's location outside, the mover's inside, as the contractum nests
them. Both located forms are read as such blocks: two ambients side by side are one block of their locations
(`par_equivalent`), and the content bags are regrouped so that the capability, or its continuation, stands beside the
rest of the mover's content as one bag (`regroup`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Steps

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)
open Mettapedia.GSLT.LanguageDef.WellSorted (HasType FreeTypeContext isObjectPattern isObjectPatternList)
open Mettapedia.GSLT.LanguageDef.BagNormalForm (elementsHaveType_iff)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (Prenex ProcEquiv Members SortedEquiv rename rename_bvar rename_comp
  liftBVars_eq_rename shiftAbove bag_perm_equivalent)
open Mettapedia.Languages.ProcessCalculi.Ambient.Located (locatedCalc locatedBlock locatedRepBlock locatedLanguage)
open Mettapedia.Languages.ProcessCalculi.Ambient.Encoding (nameType procType encode shiftName rename_encode)

variable {free : FreeTypeContext}

/-! ## Bags of located processes -/

/-- **A bag inside a bag is flattened.** -/
theorem flatten_equivalent {bound : List TypeExpr} {pre inner post : List Pattern}
    (members : Members locatedCalc locatedBlock free bound (pre ++ inner ++ post)) :
    ProcEquiv locatedCalc locatedBlock free bound
      (.collection .hashBag (pre ++ .collection .hashBag inner none :: post) none)
      (.collection .hashBag (pre ++ inner ++ post) none) := by
  have signature : Mettapedia.GSLT.LanguageDef.RestrictionBlocks.BlockSignature locatedCalc locatedBlock :=
    locatedLanguage.toBlockSignature
  have innerTyped : HasType locatedCalc free bound (.collection .hashBag inner none) procType :=
    signature.bag_typed (rest := none) (elementsHaveType_iff.mpr fun element member =>
      members element (by simp [member]))
  have sourceTyped : HasType locatedCalc free bound
      (.collection .hashBag (pre ++ .collection .hashBag inner none :: post) none) procType :=
    signature.bag_typed (rest := none) (elementsHaveType_iff.mpr fun element member => by
      simp only [List.mem_append, List.mem_cons] at member
      rcases member with inPre | rfl | inPost
      · exact members element (by simp [inPre])
      · exact innerTyped
      · exact members element (by simp [inPost]))
  have targetTyped : HasType locatedCalc free bound (.collection .hashBag (pre ++ inner ++ post) none) procType :=
    signature.bag_typed (rest := none) (elementsHaveType_iff.mpr members)
  exact SortedEquiv.ofDerived (signature.flatten sourceTyped) sourceTyped targetTyped

/-- **A bag holding one more member is regrouped**: the member that the mover's content holds first, the rest of the
content as one bag, and the other members after. -/
theorem regroup {bound : List TypeExpr} {front inner rest : List Pattern} {head : Pattern}
    (permutation : inner.Perm (head :: rest))
    (members : Members locatedCalc locatedBlock free bound (front ++ inner)) :
    ProcEquiv locatedCalc locatedBlock free bound
      (.collection .hashBag (front ++ [.collection .hashBag inner none]) none)
      (.collection .hashBag (head :: .collection .hashBag rest none :: front) none) := by
  have flatMembers : Members locatedCalc locatedBlock free bound (front ++ inner ++ []) := by
    simpa using members
  have flattened := flatten_equivalent (pre := front) (post := []) flatMembers
  simp only [List.append_nil] at flattened
  have permuted : (front ++ inner).Perm ([head] ++ rest ++ front) :=
    (List.perm_append_comm.trans (List.Perm.append_right front permutation))
  have reMembers : Members locatedCalc locatedBlock free bound ([head] ++ rest ++ front) :=
    fun element member => members element (permuted.symm.subset member)
  have unflattened := flatten_equivalent (pre := [head]) (inner := rest) (post := front) reMembers
  exact .trans _ _ _ flattened (.trans _ _ _ (bag_perm_equivalent (language := locatedCalc)
    (block := locatedRepBlock) members permuted) (.symm _ _ unflattened))

/-! ## Lifting located forms past the locations -/

theorem shiftAbove_one_succ : shiftAbove 1 1 ∘ Nat.succ = Nat.succ ∘ Nat.succ := by
  funext index
  simp [shiftAbove]

theorem shiftAbove_zero_succ : shiftAbove 0 1 ∘ Nat.succ = Nat.succ ∘ Nat.succ := by
  funext index
  simp [shiftAbove]

/-- A located form read one location deeper, its own location innermost. -/
theorem lift_inner_encode (relabel : Nat → Nat) (process : Pattern) :
    liftBVars 1 1 (encode (Nat.succ ∘ relabel) (.bvar 0) process) =
      encode (Nat.succ ∘ Nat.succ ∘ relabel) (.bvar 0) process := by
  rw [liftBVars_eq_rename, rename_encode _ (Nat.lt_succ_self _), rename_bvar]
  congr 1

/-- A located form read under one more location outside it. -/
theorem lift_outer_encode (relabel : Nat → Nat) (process : Pattern) :
    liftBVars 0 1 (encode (Nat.succ ∘ relabel) (.bvar 0) process) =
      encode (Nat.succ ∘ Nat.succ ∘ relabel) (.bvar 1) process := by
  rw [liftBVars_eq_rename, rename_encode _ (Nat.lt_succ_self _), rename_bvar]
  congr 1

theorem lift_inner_name (relabel : Nat → Nat) (name : Pattern) :
    liftBVars 1 1 (rename (Nat.succ ∘ relabel) name) = rename (Nat.succ ∘ Nat.succ ∘ relabel) name := by
  rw [liftBVars_eq_rename, rename_comp]
  congr 1

theorem lift_outer_name (relabel : Nat → Nat) (name : Pattern) :
    liftBVars 0 1 (rename (Nat.succ ∘ relabel) name) = rename (Nat.succ ∘ Nat.succ ∘ relabel) name := by
  rw [liftBVars_eq_rename, rename_comp]
  congr 1

/-- The place of the ambients, read under both locations, alike from either. -/
theorem lift_place (here : Pattern) : liftBVars 1 1 (shiftName here) = liftBVars 0 1 (shiftName here) := by
  rw [liftBVars_eq_rename, liftBVars_eq_rename, shiftName, rename_comp, rename_comp, shiftAbove_one_succ,
    shiftAbove_zero_succ]


/-! ## Entering: the redex as a block -/

open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (BlockSignature par_equivalent par_members restricts_congr
  members_of_bag)
open Mettapedia.Languages.ProcessCalculi.Ambient.Encoding (encode_amb encode_bag encode_in)
open Mettapedia.Languages.ProcessCalculi.Ambient.Decoding (shiftName_bvar)

/-- Lifting a bag lifts its members. -/
theorem liftBVars_bag (cutoff shift : Nat) (elements : List Pattern) :
    liftBVars cutoff shift (.collection .hashBag elements none) =
      .collection .hashBag (elements.map (liftBVars cutoff shift)) none := by
  simp [liftBVars, Mettapedia.OSLF.MeTTaIL.Substitution.liftBVarsList_eq_map]

/-- **Two sibling ambients, the first holding an entry capability, are a block of their locations**: the target's
location outside, the mover's inside, the redex's parts in front of the rest of the mover's content as one bag and
the target's content. -/
theorem enter_source_block {bound : List TypeExpr} {relabel : Nat → Nat} {here name target process host : Pattern}
    {inner : List Pattern} {k : Nat} (inside : k < inner.length)
    (capability : inner[k] = .apply "AIn" [target, process])
    (pairTyped : HasType locatedCalc free bound (.collection .hashBag
      [encode relabel here (.apply "AAmb" [name, .collection .hashBag inner none]),
        encode relabel here (.apply "AAmb" [target, host])] none) procType) :
    ProcEquiv locatedCalc locatedBlock free bound
      (.collection .hashBag [encode relabel here (.apply "AAmb" [name, .collection .hashBag inner none]),
        encode relabel here (.apply "AAmb" [target, host])] none)
      (Prenex.restricts locatedBlock 2 (.collection .hashBag
        (LocRedex.parts (.move true (liftBVars 0 1 (shiftName here)) (.bvar 0) (.bvar 1)
            (rename (Nat.succ ∘ Nat.succ ∘ relabel) name) (rename (Nat.succ ∘ Nat.succ ∘ relabel) target)
            (encode (Nat.succ ∘ Nat.succ ∘ relabel) (.bvar 0) process)) ++
          [.collection .hashBag ((inner.eraseIdx k).map (encode (Nat.succ ∘ Nat.succ ∘ relabel) (.bvar 0))) none,
            encode (Nat.succ ∘ Nat.succ ∘ relabel) (.bvar 1) host]) none)) := by
  have signature : BlockSignature locatedCalc locatedBlock := locatedLanguage.toBlockSignature
  -- the two ambients as blocks of their locations
  set moverBlock : Prenex := ⟨1, [.apply "LAmb" [shiftName here, .bvar 0, rename (Nat.succ ∘ relabel) name],
    .collection .hashBag (inner.map (encode (Nat.succ ∘ relabel) (.bvar 0))) none]⟩ with moverBlockIs
  set targetBlock : Prenex := ⟨1, [.apply "LAmb" [shiftName here, .bvar 0, rename (Nat.succ ∘ relabel) target],
    encode (Nat.succ ∘ relabel) (.bvar 0) host]⟩ with targetBlockIs
  have moverIs : encode relabel here (.apply "AAmb" [name, .collection .hashBag inner none]) =
      moverBlock.toPattern locatedBlock := by
    rw [encode_amb, encode_bag]
    rfl
  have targetIs : encode relabel here (.apply "AAmb" [target, host]) = targetBlock.toPattern locatedBlock := by
    rw [encode_amb]
    rfl
  rw [moverIs, targetIs] at pairTyped ⊢
  have pairMembers := members_of_bag (language := locatedCalc) (block := locatedBlock) pairTyped
  obtain ⟨moverBody, -, -⟩ := signature.restriction_typed (pairMembers (moverBlock.toPattern locatedBlock) (by simp))
  obtain ⟨targetBody, -, -⟩ := signature.restriction_typed (pairMembers (targetBlock.toPattern locatedBlock) (by simp))
  have moverMembers : Members locatedCalc locatedBlock free (List.replicate moverBlock.count nameType ++ bound)
      moverBlock.components := members_of_bag (language := locatedCalc) (block := locatedBlock) moverBody
  have targetMembers : Members locatedCalc locatedBlock free (List.replicate targetBlock.count nameType ++ bound)
      targetBlock.components := members_of_bag (language := locatedCalc) (block := locatedBlock) targetBody
  -- side by side, the target's location outside
  have swapped := bag_perm_equivalent (language := locatedCalc) (block := locatedRepBlock) pairMembers
    (List.Perm.swap (targetBlock.toPattern locatedBlock) (moverBlock.toPattern locatedBlock) [])
  have joined := par_equivalent (language := locatedCalc) (block := locatedBlock) targetMembers moverMembers
  have joinedMembers := par_members (language := locatedCalc) (block := locatedBlock) targetMembers moverMembers
  -- the mover's content regrouped: the capability first, the rest as one bag
  set front := [liftBVars 0 1 (.apply "LAmb" [shiftName here, .bvar 0, rename (Nat.succ ∘ relabel) target]),
    liftBVars 0 1 (encode (Nat.succ ∘ relabel) (.bvar 0) host),
    liftBVars 1 1 (.apply "LAmb" [shiftName here, .bvar 0, rename (Nat.succ ∘ relabel) name])] with frontIs
  have contentPerm : (inner.map (fun element => liftBVars 1 1 (encode (Nat.succ ∘ relabel) (.bvar 0) element))).Perm
      (liftBVars 1 1 (encode (Nat.succ ∘ relabel) (.bvar 0) inner[k]) ::
        (inner.eraseIdx k).map (fun element => liftBVars 1 1 (encode (Nat.succ ∘ relabel) (.bvar 0) element))) := by
    rw [← List.eraseIdx_map]
    have := List.getElem_cons_eraseIdx_perm (l := inner.map
      (fun element => liftBVars 1 1 (encode (Nat.succ ∘ relabel) (.bvar 0) element))) (by simpa using inside)
    simpa using this.symm
  have flatComponents : (targetBlock.par moverBlock).components =
      front ++ [.collection .hashBag
        (inner.map (fun element => liftBVars 1 1 (encode (Nat.succ ∘ relabel) (.bvar 0) element))) none] := by
    simp [Prenex.par, frontIs, moverBlockIs, targetBlockIs, liftBVars_bag, List.map_map, Function.comp_def]
  have contentMembers : Members locatedCalc locatedBlock free (List.replicate 2 nameType ++ bound)
      (front ++ inner.map (fun element => liftBVars 1 1 (encode (Nat.succ ∘ relabel) (.bvar 0) element))) := by
    have whole : Members locatedCalc locatedBlock free (List.replicate 2 nameType ++ bound)
        (front ++ [.collection .hashBag
          (inner.map (fun element => liftBVars 1 1 (encode (Nat.succ ∘ relabel) (.bvar 0) element))) none]) := by
      rw [← flatComponents]
      exact joinedMembers
    intro element member
    rcases List.mem_append.mp member with inFront | inContent
    · exact whole element (List.mem_append_left _ inFront)
    · exact members_of_bag (language := locatedCalc) (block := locatedBlock)
        (whole _ (List.mem_append_right _ (List.mem_singleton_self _))) element inContent
  have regrouped := restricts_congr (language := locatedCalc) (block := locatedBlock) 2
    (regroup contentPerm contentMembers)
  have leftTyped : HasType locatedCalc free bound (Prenex.restricts locatedBlock 2 (.collection .hashBag
      (front ++ [.collection .hashBag
        (inner.map (fun element => liftBVars 1 1 (encode (Nat.succ ∘ relabel) (.bvar 0) element))) none]) none))
      procType := by
    apply Mettapedia.GSLT.LanguageDef.RestrictionBlocks.restricts_typed (language := locatedCalc)
      (block := locatedBlock) 2
    apply signature.bag_typed (rest := none)
    apply elementsHaveType_iff.mpr
    intro element member
    rcases List.mem_append.mp member with inFront | inBag
    · exact contentMembers element (List.mem_append_left _ inFront)
    · simp only [List.mem_singleton] at inBag
      subst inBag
      exact signature.bag_typed (rest := none) (elementsHaveType_iff.mpr fun inner' member' =>
        contentMembers inner' (List.mem_append_right _ member'))
  have rightTyped := (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.SortedEquiv.typed_iff regrouped).mp leftTyped
  -- the regrouped block, read with the redex's own variables
  have headIs : liftBVars 1 1 (encode (Nat.succ ∘ relabel) (.bvar 0) inner[k]) =
      .apply "LIn" [.bvar 0, rename (Nat.succ ∘ Nat.succ ∘ relabel) target,
        encode (Nat.succ ∘ Nat.succ ∘ relabel) (.bvar 0) process] := by
    rw [capability, encode_in]
    simp only [liftBVars, Mettapedia.OSLF.MeTTaIL.Substitution.liftBVarsList_eq_map, List.map_cons, List.map_nil]
    rw [lift_inner_name, lift_inner_encode]
    simp
  have restIs : (inner.eraseIdx k).map (fun element => liftBVars 1 1 (encode (Nat.succ ∘ relabel) (.bvar 0) element)) =
      (inner.eraseIdx k).map (encode (Nat.succ ∘ Nat.succ ∘ relabel) (.bvar 0)) :=
    List.map_congr_left fun element _ => lift_inner_encode relabel element
  have frontIs' : front = [.apply "LAmb" [liftBVars 0 1 (shiftName here), .bvar 1,
        rename (Nat.succ ∘ Nat.succ ∘ relabel) target],
      encode (Nat.succ ∘ Nat.succ ∘ relabel) (.bvar 1) host,
      .apply "LAmb" [liftBVars 0 1 (shiftName here), .bvar 0, rename (Nat.succ ∘ Nat.succ ∘ relabel) name]] := by
    simp only [frontIs, liftBVars, Mettapedia.OSLF.MeTTaIL.Substitution.liftBVarsList_eq_map, List.map_cons,
      List.map_nil]
    rw [lift_outer_name, lift_outer_encode, lift_inner_name, lift_place]
    simp
  rw [headIs, restIs, frontIs'] at regrouped rightTyped
  -- in the redex's order
  obtain ⟨outerBody, -, -⟩ := signature.restriction_typed rightTyped
  obtain ⟨typedBody, -, -⟩ := signature.restriction_typed outerBody
  have reachedMembers := members_of_bag (language := locatedCalc) (block := locatedBlock) typedBody
  have reordered := restricts_congr (language := locatedCalc) (block := locatedBlock) 2
    (bag_perm_equivalent (language := locatedCalc) (block := locatedRepBlock) reachedMembers
      ((List.perm_middle (l₁ := [_, _, _, _]) (l₂ := [])).trans
        (((List.Perm.swap _ _ [_]).cons _).cons _)))
  refine .trans _ _ _ swapped (.trans _ _ _ joined ?_)
  have flatIs : (targetBlock.par moverBlock).toPattern locatedBlock = Prenex.restricts locatedBlock 2
      (.collection .hashBag (front ++ [.collection .hashBag
        (inner.map (fun element => liftBVars 1 1 (encode (Nat.succ ∘ relabel) (.bvar 0) element))) none]) none) := by
    rw [Prenex.toPattern, flatComponents]
    rfl
  rw [flatIs, frontIs']
  exact .trans _ _ _ regrouped reordered


open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (restrict_fill)

/-- **The ambient that was entered, holding the mover, is a block of their locations**, the redex's results in
front of the same rest. -/
theorem enter_target_block {bound : List TypeExpr} {relabel : Nat → Nat} {here name target process host : Pattern}
    {inner : List Pattern}
    (typed : HasType locatedCalc free bound (encode relabel here (.apply "AAmb" [target, .collection .hashBag
      [.apply "AAmb" [name, .collection .hashBag (process :: inner) none], host] none])) procType) :
    ProcEquiv locatedCalc locatedBlock free bound
      (encode relabel here (.apply "AAmb" [target, .collection .hashBag
        [.apply "AAmb" [name, .collection .hashBag (process :: inner) none], host] none]))
      (Prenex.restricts locatedBlock 2 (.collection .hashBag
        (LocRedex.result (.move true (liftBVars 0 1 (shiftName here)) (.bvar 0) (.bvar 1)
            (rename (Nat.succ ∘ Nat.succ ∘ relabel) name) (rename (Nat.succ ∘ Nat.succ ∘ relabel) target)
            (encode (Nat.succ ∘ Nat.succ ∘ relabel) (.bvar 0) process)) ++
          [.collection .hashBag (inner.map (encode (Nat.succ ∘ Nat.succ ∘ relabel) (.bvar 0))) none,
            encode (Nat.succ ∘ Nat.succ ∘ relabel) (.bvar 1) host]) none)) := by
  have signature : BlockSignature locatedCalc locatedBlock := locatedLanguage.toBlockSignature
  set marker := Pattern.apply "LAmb" [shiftName here, .bvar 0, rename (Nat.succ ∘ relabel) target] with markerIs
  set hostRead := encode (Nat.succ ∘ relabel) (.bvar 0) host with hostReadIs
  set moverBlock : Prenex := ⟨1, [.apply "LAmb" [.bvar 1, .bvar 0, rename (Nat.succ ∘ Nat.succ ∘ relabel) name],
    .collection .hashBag ((process :: inner).map (encode (Nat.succ ∘ Nat.succ ∘ relabel) (.bvar 0))) none]⟩
    with moverBlockIs
  set outerBlock : Prenex := ⟨0, [marker, hostRead]⟩ with outerBlockIs
  have readIs : encode relabel here (.apply "AAmb" [target, .collection .hashBag
      [.apply "AAmb" [name, .collection .hashBag (process :: inner) none], host] none]) =
      .apply "LNu" [.lambda none (.collection .hashBag [marker, .collection .hashBag
        [moverBlock.toPattern locatedBlock, hostRead] none] none)] := by
    rw [encode_amb, encode_bag]
    simp only [List.map_cons, List.map_nil]
    rw [encode_amb, encode_bag, shiftName_bvar]
    rfl
  rw [readIs] at typed ⊢
  -- inside the target's location
  obtain ⟨insideTyped, -, -⟩ := signature.restriction_typed typed
  have insideMembers := members_of_bag (language := locatedCalc) (block := locatedBlock) insideTyped
  have pairTyped := insideMembers (.collection .hashBag [moverBlock.toPattern locatedBlock, hostRead] none) (by simp)
  have pairMembers := members_of_bag (language := locatedCalc) (block := locatedBlock) pairTyped
  have markerTyped := insideMembers marker (by simp)
  have moverTyped := pairMembers (moverBlock.toPattern locatedBlock) (by simp)
  have hostTyped := pairMembers hostRead (by simp)
  obtain ⟨moverBody, -, -⟩ := signature.restriction_typed moverTyped
  have moverMembers : Members locatedCalc locatedBlock free (List.replicate moverBlock.count nameType ++
      (nameType :: bound)) moverBlock.components := members_of_bag (language := locatedCalc) (block := locatedBlock)
    moverBody
  have outerMembers : Members locatedCalc locatedBlock free (List.replicate outerBlock.count nameType ++
      (nameType :: bound)) outerBlock.components := by
    intro element member
    simp only [outerBlockIs, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact markerTyped
    · exact hostTyped
  have flatMembers : Members locatedCalc locatedBlock free (nameType :: bound)
      ([marker] ++ [moverBlock.toPattern locatedBlock, hostRead] ++ []) := by
    intro element member
    simp only [List.append_nil, List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact markerTyped
    · exact moverTyped
    · exact hostTyped
  have flattened := flatten_equivalent (pre := [marker]) (post := []) flatMembers
  simp only [List.append_nil, List.singleton_append] at flattened
  have swappedMembers : Members locatedCalc locatedBlock free (nameType :: bound)
      [marker, moverBlock.toPattern locatedBlock, hostRead] := by simpa using flatMembers
  have swapped := bag_perm_equivalent (language := locatedCalc) (block := locatedRepBlock) swappedMembers
    ((List.Perm.swap hostRead (moverBlock.toPattern locatedBlock) []).cons marker)
  have regroupMembers : Members locatedCalc locatedBlock free (nameType :: bound)
      ([] ++ [marker, hostRead] ++ [moverBlock.toPattern locatedBlock]) := by
    intro element member
    exact swappedMembers element (by simp at member ⊢; tauto)
  have grouped := flatten_equivalent (pre := []) (inner := [marker, hostRead])
    (post := [moverBlock.toPattern locatedBlock]) regroupMembers
  simp only [List.nil_append, List.cons_append] at grouped
  have joined := par_equivalent (language := locatedCalc) (block := locatedBlock) outerMembers moverMembers
  have insideChain : ProcEquiv locatedCalc locatedBlock free (nameType :: bound)
      (.collection .hashBag [marker, .collection .hashBag [moverBlock.toPattern locatedBlock, hostRead] none] none)
      ((outerBlock.par moverBlock).toPattern locatedBlock) :=
    .trans _ _ _ flattened (.trans _ _ _ swapped (.trans _ _ _ (.symm _ _ grouped) joined))
  have closed := restrict_fill (language := locatedCalc) (block := locatedBlock) insideChain
  -- the joined block, regrouped and read with the redex's own variables
  have flatIs : Pattern.apply locatedBlock.restrict [.lambda none ((outerBlock.par moverBlock).toPattern locatedBlock)] =
      Prenex.restricts locatedBlock 2 (.collection .hashBag
        ([liftBVars 0 1 marker, liftBVars 0 1 hostRead,
          .apply "LAmb" [.bvar 1, .bvar 0, rename (Nat.succ ∘ Nat.succ ∘ relabel) name]] ++
        [.collection .hashBag ((process :: inner).map (encode (Nat.succ ∘ Nat.succ ∘ relabel) (.bvar 0))) none])
        none) := by
    simp only [Prenex.toPattern, Prenex.par, outerBlockIs, moverBlockIs, List.map_cons, List.map_nil,
      Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero]
    rfl
  have contentMembers : Members locatedCalc locatedBlock free (List.replicate 2 nameType ++ bound)
      ([liftBVars 0 1 marker, liftBVars 0 1 hostRead,
          .apply "LAmb" [.bvar 1, .bvar 0, rename (Nat.succ ∘ Nat.succ ∘ relabel) name]] ++
        (process :: inner).map (encode (Nat.succ ∘ Nat.succ ∘ relabel) (.bvar 0))) := by
    have joinedMembers := par_members (language := locatedCalc) (block := locatedBlock) outerMembers moverMembers
    have whole : Members locatedCalc locatedBlock free (List.replicate 2 nameType ++ bound)
        ([liftBVars 0 1 marker, liftBVars 0 1 hostRead,
          .apply "LAmb" [.bvar 1, .bvar 0, rename (Nat.succ ∘ Nat.succ ∘ relabel) name]] ++
        [.collection .hashBag ((process :: inner).map (encode (Nat.succ ∘ Nat.succ ∘ relabel) (.bvar 0))) none]) := by
      have componentsIs : (outerBlock.par moverBlock).components =
          [liftBVars 0 1 marker, liftBVars 0 1 hostRead,
            .apply "LAmb" [.bvar 1, .bvar 0, rename (Nat.succ ∘ Nat.succ ∘ relabel) name]] ++
          [.collection .hashBag ((process :: inner).map (encode (Nat.succ ∘ Nat.succ ∘ relabel) (.bvar 0))) none] := by
        simp only [Prenex.par, outerBlockIs, moverBlockIs, List.map_cons, List.map_nil,
          Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero]
        rfl
      rw [← componentsIs]
      exact joinedMembers
    intro element member
    rcases List.mem_append.mp member with inFront | inContent
    · exact whole element (List.mem_append_left _ inFront)
    · exact members_of_bag (language := locatedCalc) (block := locatedBlock)
        (whole _ (List.mem_append_right _ (List.mem_singleton_self _))) element inContent
  have regrouped := restricts_congr (language := locatedCalc) (block := locatedBlock) 2
    (regroup (List.Perm.refl _) contentMembers)
  have leftTyped := (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.SortedEquiv.typed_iff closed).mp typed
  rw [flatIs] at closed leftTyped
  have rightTyped := (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.SortedEquiv.typed_iff regrouped).mp leftTyped
  have frontIs : [liftBVars 0 1 marker, liftBVars 0 1 hostRead,
        Pattern.apply "LAmb" [.bvar 1, .bvar 0, rename (Nat.succ ∘ Nat.succ ∘ relabel) name]] =
      [.apply "LAmb" [liftBVars 0 1 (shiftName here), .bvar 1, rename (Nat.succ ∘ Nat.succ ∘ relabel) target],
        encode (Nat.succ ∘ Nat.succ ∘ relabel) (.bvar 1) host,
        .apply "LAmb" [.bvar 1, .bvar 0, rename (Nat.succ ∘ Nat.succ ∘ relabel) name]] := by
    simp only [markerIs, hostReadIs, liftBVars, Mettapedia.OSLF.MeTTaIL.Substitution.liftBVarsList_eq_map,
      List.map_cons, List.map_nil]
    rw [lift_outer_name, lift_outer_encode]
    simp
  rw [frontIs] at regrouped rightTyped closed
  simp only [List.map_cons] at closed regrouped
  obtain ⟨outerBody, -, -⟩ := signature.restriction_typed rightTyped
  obtain ⟨typedBody, -, -⟩ := signature.restriction_typed outerBody
  have reachedMembers := members_of_bag (language := locatedCalc) (block := locatedBlock) typedBody
  have reordered := restricts_congr (language := locatedCalc) (block := locatedBlock) 2
    (bag_perm_equivalent (language := locatedCalc) (block := locatedRepBlock) reachedMembers
      ((List.perm_middle (l₁ := [_, _, _, _]) (l₂ := [])).trans
        (((List.Perm.swap _ _ [_]).cons _).cons _)))
  exact .trans _ _ _ closed (.trans _ _ _ regrouped reordered)


/-! ## Entering as a reaction -/

open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (isObjectPattern_rename size ReplicationStepAt ReactsAt)
open Mettapedia.Languages.ProcessCalculi.Ambient.Encoding (encode_object)

theorem perm_two (elements : List Pattern) (first : Nat) (firstInside : first < elements.length) (second : Nat)
    (secondInside : second < (elements.eraseIdx first).length) :
    elements.Perm (elements[first] :: (elements.eraseIdx first)[second] ::
      (elements.eraseIdx first).eraseIdx second) :=
  (List.getElem_cons_eraseIdx_perm firstInside).symm.trans
    ((List.getElem_cons_eraseIdx_perm secondInside).symm.cons _)

theorem lift_object {pattern : Pattern} (cutoff shift : Nat) (object : isObjectPattern pattern = true) :
    isObjectPattern (liftBVars cutoff shift pattern) = true := by
  rw [liftBVars_eq_rename, isObjectPattern_rename]
  exact object

theorem encode_object' {relabel : Nat → Nat} {here process : Pattern} (hereObject : isObjectPattern here = true)
    (object : isObjectPattern process = true) : isObjectPattern (encode relabel here process) = true :=
  encode_object (size process + 1) (Nat.lt_succ_self _) hereObject object

/-- **Two sibling ambients, one entering the other, react as located atoms** at the front of the block of their
locations. -/
theorem reacts_enter_core {bound : List TypeExpr} {relabel : Nat → Nat} {here name target process host : Pattern}
    {inner : List Pattern} {k : Nat} (inside : k < inner.length)
    (capability : inner[k] = .apply "AIn" [target, process])
    (hereObject : isObjectPattern here = true) (nameObject : isObjectPattern name = true)
    (targetObject : isObjectPattern target = true) (processObject : isObjectPattern process = true)
    (hostObject : isObjectPattern host = true) (innerObjects : ∀ element ∈ inner, isObjectPattern element = true)
    (pairTyped : HasType locatedCalc free bound (.collection .hashBag
      [encode relabel here (.apply "AAmb" [name, .collection .hashBag inner none]),
        encode relabel here (.apply "AAmb" [target, host])] none) procType)
    (contractumTyped : HasType locatedCalc free bound (encode relabel here (.apply "AAmb" [target,
      .collection .hashBag [.apply "AAmb" [name, .collection .hashBag (process :: inner.eraseIdx k) none], host] none]))
      procType) :
    ∃ count redex rest, ReplicationStepAt locatedReactions free bound
      (.collection .hashBag [encode relabel here (.apply "AAmb" [name, .collection .hashBag inner none]),
        encode relabel here (.apply "AAmb" [target, host])] none)
      (encode relabel here (.apply "AAmb" [target, .collection .hashBag
        [.apply "AAmb" [name, .collection .hashBag (process :: inner.eraseIdx k) none], host] none]))
      count redex rest := by
  have signature : BlockSignature locatedCalc locatedBlock := locatedLanguage.toBlockSignature
  have source := enter_source_block inside capability pairTyped
  have target' := enter_target_block (inner := inner.eraseIdx k) contractumTyped
  refine ⟨2, LocRedex.move true (liftBVars 0 1 (shiftName here)) (.bvar 0) (.bvar 1)
      (rename (Nat.succ ∘ Nat.succ ∘ relabel) name) (rename (Nat.succ ∘ Nat.succ ∘ relabel) target)
      (encode (Nat.succ ∘ Nat.succ ∘ relabel) (.bvar 0) process),
    [.collection .hashBag ((inner.eraseIdx k).map (encode (Nat.succ ∘ Nat.succ ∘ relabel) (.bvar 0))) none,
      encode (Nat.succ ∘ Nat.succ ∘ relabel) (.bvar 1) host],
    ⟨?_, ?_, source.toEquationEquiv, target'.toEquationEquiv⟩⟩
  · have blockTyped := (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.SortedEquiv.typed_iff source).mp pairTyped
    obtain ⟨outerBody, -, -⟩ := signature.restriction_typed blockTyped
    obtain ⟨typedBody, -, -⟩ := signature.restriction_typed outerBody
    exact members_of_bag (language := locatedCalc) (block := locatedBlock) typedBody
  · have placeObject : isObjectPattern (liftBVars 0 1 (shiftName here)) = true :=
      lift_object 0 1 (by rw [shiftName, isObjectPattern_rename]; exact hereObject)
    have renamedObject : ∀ {pattern : Pattern}, isObjectPattern pattern = true →
        isObjectPattern (rename (Nat.succ ∘ Nat.succ ∘ relabel) pattern) = true := fun object => by
      rw [isObjectPattern_rename]; exact object
    intro element member
    simp only [locatedReactions, LocRedex.parts, LocRedex.before, LocRedex.capability, if_true, List.cons_append,
      List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · simp [isObjectPattern, isObjectPatternList, placeObject, renamedObject nameObject]
    · simp [isObjectPattern, isObjectPatternList, renamedObject targetObject,
        encode_object' (here := .bvar 0) rfl processObject]
    · simp [isObjectPattern, isObjectPatternList, placeObject, renamedObject targetObject]
    · simp only [isObjectPattern, Bool.and_eq_true, Option.isNone_none, true_and,
        Mettapedia.GSLT.LanguageDef.BagNormalForm.isObjectPatternList_iff]
      intro element member
      obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp member
      exact encode_object' rfl (innerObjects original (List.mem_of_mem_eraseIdx inOriginal))
    · exact encode_object' rfl hostObject


/-- **An ambient entering a sibling, among other components, reacts as located atoms** at the front of a block. -/
theorem reacts_enter {bound : List TypeExpr} {relabel : Nat → Nat} {here : Pattern} {elements : List Pattern}
    {i j k : Nat} (hi : i < elements.length) (hj : j < (elements.eraseIdx i).length)
    {name target process host : Pattern} {inner : List Pattern} (hk : k < inner.length)
    (mover : elements[i] = .apply "AAmb" [name, .collection .hashBag inner none])
    (capability : inner[k] = .apply "AIn" [target, process])
    (destination : (elements.eraseIdx i)[j] = .apply "AAmb" [target, host])
    (hereObject : isObjectPattern here = true) (objects : ∀ element ∈ elements, isObjectPattern element = true)
    (sourceTyped : HasType locatedCalc free bound (encode relabel here (.collection .hashBag elements none)) procType)
    (contractumTyped : HasType locatedCalc free bound (encode relabel here (.collection .hashBag
      (.apply "AAmb" [target, .collection .hashBag [.apply "AAmb" [name, .collection .hashBag
        (process :: inner.eraseIdx k) none], host] none] :: (elements.eraseIdx i).eraseIdx j) none)) procType) :
    ∃ count redex rest, ReplicationStepAt locatedReactions free bound
      (encode relabel here (.collection .hashBag elements none))
      (encode relabel here (.collection .hashBag
        (.apply "AAmb" [target, .collection .hashBag [.apply "AAmb" [name, .collection .hashBag
          (process :: inner.eraseIdx k) none], host] none] :: (elements.eraseIdx i).eraseIdx j) none))
      count redex rest := by
  have signature : BlockSignature locatedCalc locatedRepBlock.toBlock := locatedLanguage.toBlockSignature
  set others := (elements.eraseIdx i).eraseIdx j with othersIs
  -- the pieces are object terms
  have moverObject := objects _ (List.getElem_mem hi)
  have destinationObject := objects _ (List.mem_of_mem_eraseIdx (List.getElem_mem hj))
  rw [mover] at moverObject
  rw [destination] at destinationObject
  obtain ⟨nameObject, innerBagObject⟩ := pair_objects moverObject
  obtain ⟨targetObject, hostObject⟩ := pair_objects destinationObject
  obtain ⟨-, innerObjects⟩ := bag_objects innerBagObject
  have capabilityObject := innerObjects _ (List.getElem_mem hk)
  rw [capability] at capabilityObject
  obtain ⟨-, processObject⟩ := pair_objects capabilityObject
  -- the two ambients first, as one member
  have permutation := perm_two elements i hi j hj
  rw [mover, destination] at permutation
  rw [encode_bag] at sourceTyped ⊢
  rw [encode_bag, List.map_cons] at contractumTyped ⊢
  have sourceMembers := members_of_bag (language := locatedCalc) (block := locatedBlock) sourceTyped
  have mappedPerm := permutation.map (encode relabel here)
  simp only [List.map_cons] at mappedPerm
  have pairMembers : Members locatedCalc locatedBlock free bound
      [encode relabel here (.apply "AAmb" [name, .collection .hashBag inner none]),
        encode relabel here (.apply "AAmb" [target, host])] := fun element member =>
    sourceMembers element (mappedPerm.symm.subset (by simp at member ⊢; tauto))
  have pairTyped := signature.bag_typed (rest := none) (elementsHaveType_iff.mpr pairMembers)
  have contractumMembers := members_of_bag (language := locatedCalc) (block := locatedBlock) contractumTyped
  obtain ⟨count, redex, rest, core⟩ := reacts_enter_core hk capability hereObject nameObject targetObject
    processObject hostObject (fun element member => innerObjects element member) pairTyped
    (contractumMembers _ List.mem_cons_self)
  have othersMembers : Members locatedCalc locatedBlock free bound (others.map (encode relabel here)) :=
    fun element member => sourceMembers element (mappedPerm.symm.subset (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ member)))
  have groupedMembers : Members locatedCalc locatedBlock free bound
      (.collection .hashBag [encode relabel here (.apply "AAmb" [name, .collection .hashBag inner none]),
        encode relabel here (.apply "AAmb" [target, host])] none :: others.map (encode relabel here)) := by
    intro element member
    rcases List.mem_cons.mp member with rfl | inOthers
    · exact pairTyped
    · exact othersMembers element inOthers
  have groupedTyped := signature.bag_typed (rest := none) (elementsHaveType_iff.mpr groupedMembers)
  have groupedObjects : ∀ element ∈ .collection .hashBag [encode relabel here (.apply "AAmb" [name,
      .collection .hashBag inner none]), encode relabel here (.apply "AAmb" [target, host])] none ::
      others.map (encode relabel here), isObjectPattern element = true := by
    intro element member
    rcases List.mem_cons.mp member with rfl | inOthers
    · simp only [isObjectPattern, Bool.and_eq_true, Option.isNone_none, true_and,
        Mettapedia.GSLT.LanguageDef.BagNormalForm.isObjectPatternList_iff, List.mem_cons, List.not_mem_nil,
        or_false]
      rintro element (rfl | rfl)
      · exact encode_object' hereObject moverObject
      · exact encode_object' hereObject destinationObject
    · obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp inOthers
      exact encode_object' hereObject (objects original (List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx
        inOriginal)))
  have lifted := ReactsAt.inBag 0 (by simp) (locatedReactions.result_members redex) groupedTyped groupedObjects core
  simp only [List.eraseIdx_cons_zero] at lifted
  -- the located source is the grouped bag
  have flatMembers : Members locatedCalc locatedBlock free bound
      ([] ++ [encode relabel here (.apply "AAmb" [name, .collection .hashBag inner none]),
        encode relabel here (.apply "AAmb" [target, host])] ++ others.map (encode relabel here)) := by
    intro element member
    exact sourceMembers element (mappedPerm.symm.subset (by simpa using member))
  have ungrouped := flatten_equivalent (pre := []) (post := others.map (encode relabel here)) flatMembers
  simp only [List.nil_append, List.cons_append] at ungrouped
  have reordered := bag_perm_equivalent (language := locatedCalc) (block := locatedRepBlock) sourceMembers
    mappedPerm
  exact ⟨count, redex, _, ReactsAt.congr lifted
    (.trans _ _ _ reordered.toEquationEquiv (.symm _ _ ungrouped.toEquationEquiv)) (.refl _)⟩


/-! ## Leaving: the redex as a block -/

open Mettapedia.Languages.ProcessCalculi.Ambient.Encoding (encode_out)

/-- **The ambient that left, beside the ambient it left, is a block of their locations**, the redex's results in front
of the rest of the mover's content and of the parent's content, each as one bag. -/
theorem exit_target_block {bound : List TypeExpr} {relabel : Nat → Nat} {here name parent process : Pattern}
    {inner others : List Pattern}
    (pairTyped : HasType locatedCalc free bound (.collection .hashBag
      [encode relabel here (.apply "AAmb" [name, .collection .hashBag (process :: inner) none]),
        encode relabel here (.apply "AAmb" [parent, .collection .hashBag others none])] none) procType) :
    ProcEquiv locatedCalc locatedBlock free bound
      (.collection .hashBag [encode relabel here (.apply "AAmb" [name, .collection .hashBag (process :: inner) none]),
        encode relabel here (.apply "AAmb" [parent, .collection .hashBag others none])] none)
      (Prenex.restricts locatedBlock 2 (.collection .hashBag
        (LocRedex.result (.move false (liftBVars 0 1 (shiftName here)) (.bvar 0) (.bvar 1)
            (rename (Nat.succ ∘ Nat.succ ∘ relabel) name) (rename (Nat.succ ∘ Nat.succ ∘ relabel) parent)
            (encode (Nat.succ ∘ Nat.succ ∘ relabel) (.bvar 0) process)) ++
          [.collection .hashBag (inner.map (encode (Nat.succ ∘ Nat.succ ∘ relabel) (.bvar 0))) none,
            .collection .hashBag (others.map (encode (Nat.succ ∘ Nat.succ ∘ relabel) (.bvar 1))) none]) none)) := by
  have signature : BlockSignature locatedCalc locatedBlock := locatedLanguage.toBlockSignature
  set moverBlock : Prenex := ⟨1, [.apply "LAmb" [shiftName here, .bvar 0, rename (Nat.succ ∘ relabel) name],
    .collection .hashBag ((process :: inner).map (encode (Nat.succ ∘ relabel) (.bvar 0))) none]⟩ with moverBlockIs
  set parentBlock : Prenex := ⟨1, [.apply "LAmb" [shiftName here, .bvar 0, rename (Nat.succ ∘ relabel) parent],
    .collection .hashBag (others.map (encode (Nat.succ ∘ relabel) (.bvar 0))) none]⟩ with parentBlockIs
  have moverIs : encode relabel here (.apply "AAmb" [name, .collection .hashBag (process :: inner) none]) =
      moverBlock.toPattern locatedBlock := by
    rw [encode_amb, encode_bag]
    rfl
  have parentIs : encode relabel here (.apply "AAmb" [parent, .collection .hashBag others none]) =
      parentBlock.toPattern locatedBlock := by
    rw [encode_amb, encode_bag]
    rfl
  rw [moverIs, parentIs] at pairTyped ⊢
  have pairMembers := members_of_bag (language := locatedCalc) (block := locatedBlock) pairTyped
  obtain ⟨moverBody, -, -⟩ := signature.restriction_typed (pairMembers (moverBlock.toPattern locatedBlock) (by simp))
  obtain ⟨parentBody, -, -⟩ := signature.restriction_typed (pairMembers (parentBlock.toPattern locatedBlock) (by simp))
  have moverMembers : Members locatedCalc locatedBlock free (List.replicate moverBlock.count nameType ++ bound)
      moverBlock.components := members_of_bag (language := locatedCalc) (block := locatedBlock) moverBody
  have parentMembers : Members locatedCalc locatedBlock free (List.replicate parentBlock.count nameType ++ bound)
      parentBlock.components := members_of_bag (language := locatedCalc) (block := locatedBlock) parentBody
  have swapped := bag_perm_equivalent (language := locatedCalc) (block := locatedRepBlock) pairMembers
    (List.Perm.swap (parentBlock.toPattern locatedBlock) (moverBlock.toPattern locatedBlock) [])
  have joined := par_equivalent (language := locatedCalc) (block := locatedBlock) parentMembers moverMembers
  have joinedMembers := par_members (language := locatedCalc) (block := locatedBlock) parentMembers moverMembers
  set front := [liftBVars 0 1 (.apply "LAmb" [shiftName here, .bvar 0, rename (Nat.succ ∘ relabel) parent]),
    liftBVars 0 1 (.collection .hashBag (others.map (encode (Nat.succ ∘ relabel) (.bvar 0))) none),
    liftBVars 1 1 (.apply "LAmb" [shiftName here, .bvar 0, rename (Nat.succ ∘ relabel) name])] with frontIs
  have flatComponents : (parentBlock.par moverBlock).components =
      front ++ [.collection .hashBag
        ((process :: inner).map (fun element => liftBVars 1 1 (encode (Nat.succ ∘ relabel) (.bvar 0) element)))
        none] := by
    simp [Prenex.par, frontIs, moverBlockIs, parentBlockIs, liftBVars_bag, List.map_map, Function.comp_def]
  have contentMembers : Members locatedCalc locatedBlock free (List.replicate 2 nameType ++ bound)
      (front ++ (process :: inner).map
        (fun element => liftBVars 1 1 (encode (Nat.succ ∘ relabel) (.bvar 0) element))) := by
    have whole : Members locatedCalc locatedBlock free (List.replicate 2 nameType ++ bound)
        (front ++ [.collection .hashBag ((process :: inner).map
          (fun element => liftBVars 1 1 (encode (Nat.succ ∘ relabel) (.bvar 0) element))) none]) := by
      rw [← flatComponents]
      exact joinedMembers
    intro element member
    rcases List.mem_append.mp member with inFront | inContent
    · exact whole element (List.mem_append_left _ inFront)
    · exact members_of_bag (language := locatedCalc) (block := locatedBlock)
        (whole _ (List.mem_append_right _ (List.mem_singleton_self _))) element inContent
  have regrouped := restricts_congr (language := locatedCalc) (block := locatedBlock) 2
    (regroup (head := liftBVars 1 1 (encode (Nat.succ ∘ relabel) (.bvar 0) process))
      (rest := inner.map (fun element => liftBVars 1 1 (encode (Nat.succ ∘ relabel) (.bvar 0) element)))
      (List.Perm.refl _) contentMembers)
  have leftTyped : HasType locatedCalc free bound (Prenex.restricts locatedBlock 2 (.collection .hashBag
      (front ++ [.collection .hashBag ((process :: inner).map
        (fun element => liftBVars 1 1 (encode (Nat.succ ∘ relabel) (.bvar 0) element))) none]) none)) procType := by
    apply Mettapedia.GSLT.LanguageDef.RestrictionBlocks.restricts_typed (language := locatedCalc)
      (block := locatedBlock) 2
    apply signature.bag_typed (rest := none)
    apply elementsHaveType_iff.mpr
    intro element member
    rcases List.mem_append.mp member with inFront | inBag
    · exact contentMembers element (List.mem_append_left _ inFront)
    · simp only [List.mem_singleton] at inBag
      subst inBag
      exact signature.bag_typed (rest := none) (elementsHaveType_iff.mpr fun inner' member' =>
        contentMembers inner' (List.mem_append_right _ member'))
  have rightTyped := (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.SortedEquiv.typed_iff regrouped).mp leftTyped
  have restIs : inner.map (fun element => liftBVars 1 1 (encode (Nat.succ ∘ relabel) (.bvar 0) element)) =
      inner.map (encode (Nat.succ ∘ Nat.succ ∘ relabel) (.bvar 0)) :=
    List.map_congr_left fun element _ => lift_inner_encode relabel element
  have othersIs : (others.map (encode (Nat.succ ∘ relabel) (.bvar 0))).map (liftBVars 0 1) =
      others.map (encode (Nat.succ ∘ Nat.succ ∘ relabel) (.bvar 1)) := by
    rw [List.map_map]
    exact List.map_congr_left fun element _ => lift_outer_encode relabel element
  have frontIs' : front = [.apply "LAmb" [liftBVars 0 1 (shiftName here), .bvar 1,
        rename (Nat.succ ∘ Nat.succ ∘ relabel) parent],
      .collection .hashBag (others.map (encode (Nat.succ ∘ Nat.succ ∘ relabel) (.bvar 1))) none,
      .apply "LAmb" [liftBVars 0 1 (shiftName here), .bvar 0, rename (Nat.succ ∘ Nat.succ ∘ relabel) name]] := by
    rw [frontIs, liftBVars_bag, othersIs]
    simp only [liftBVars, Mettapedia.OSLF.MeTTaIL.Substitution.liftBVarsList_eq_map, List.map_cons, List.map_nil]
    rw [lift_outer_name, lift_inner_name, lift_place]
    simp
  rw [lift_inner_encode, restIs, frontIs'] at regrouped rightTyped
  obtain ⟨outerBody, -, -⟩ := signature.restriction_typed rightTyped
  obtain ⟨typedBody, -, -⟩ := signature.restriction_typed outerBody
  have reachedMembers := members_of_bag (language := locatedCalc) (block := locatedBlock) typedBody
  have reordered := restricts_congr (language := locatedCalc) (block := locatedBlock) 2
    (bag_perm_equivalent (language := locatedCalc) (block := locatedRepBlock) reachedMembers
      ((List.perm_middle (l₁ := [_, _, _, _]) (l₂ := [])).trans
        (((List.Perm.swap _ _ [_]).cons _).cons _)))
  refine .trans _ _ _ swapped (.trans _ _ _ joined ?_)
  have flatIs : (parentBlock.par moverBlock).toPattern locatedBlock = Prenex.restricts locatedBlock 2
      (.collection .hashBag (front ++ [.collection .hashBag ((process :: inner).map
        (fun element => liftBVars 1 1 (encode (Nat.succ ∘ relabel) (.bvar 0) element))) none]) none) := by
    rw [Prenex.toPattern, flatComponents]
    rfl
  rw [flatIs, frontIs']
  simp only [List.map_cons]
  rw [lift_inner_encode, restIs]
  exact .trans _ _ _ regrouped reordered


/-- **An ambient holding an ambient with an exit capability for it is a block of their locations**: the parent's
location outside, the mover's inside, the redex's parts in front of the rest of the mover's content and of the
parent's content, each as one bag. -/
theorem exit_source_block {bound : List TypeExpr} {relabel : Nat → Nat} {here name parent process : Pattern}
    {contents inner : List Pattern} {i k : Nat} (hi : i < contents.length)
    (mover : contents[i] = .apply "AAmb" [name, .collection .hashBag inner none])
    (hk : k < inner.length) (capability : inner[k] = .apply "AOut" [parent, process])
    (typed : HasType locatedCalc free bound
      (encode relabel here (.apply "AAmb" [parent, .collection .hashBag contents none])) procType) :
    ProcEquiv locatedCalc locatedBlock free bound
      (encode relabel here (.apply "AAmb" [parent, .collection .hashBag contents none]))
      (Prenex.restricts locatedBlock 2 (.collection .hashBag
        (LocRedex.parts (.move false (liftBVars 0 1 (shiftName here)) (.bvar 0) (.bvar 1)
            (rename (Nat.succ ∘ Nat.succ ∘ relabel) name) (rename (Nat.succ ∘ Nat.succ ∘ relabel) parent)
            (encode (Nat.succ ∘ Nat.succ ∘ relabel) (.bvar 0) process)) ++
          [.collection .hashBag ((inner.eraseIdx k).map (encode (Nat.succ ∘ Nat.succ ∘ relabel) (.bvar 0))) none,
            .collection .hashBag ((contents.eraseIdx i).map (encode (Nat.succ ∘ Nat.succ ∘ relabel) (.bvar 1)))
              none]) none)) := by
  have signature : BlockSignature locatedCalc locatedBlock := locatedLanguage.toBlockSignature
  set marker := Pattern.apply "LAmb" [shiftName here, .bvar 0, rename (Nat.succ ∘ relabel) parent] with markerIs
  set restRead := Pattern.collection .hashBag
    ((contents.eraseIdx i).map (encode (Nat.succ ∘ relabel) (.bvar 0))) none with restReadIs
  set moverBlock : Prenex := ⟨1, [.apply "LAmb" [.bvar 1, .bvar 0, rename (Nat.succ ∘ Nat.succ ∘ relabel) name],
    .collection .hashBag (inner.map (encode (Nat.succ ∘ Nat.succ ∘ relabel) (.bvar 0))) none]⟩ with moverBlockIs
  set outerBlock : Prenex := ⟨0, [marker, restRead]⟩ with outerBlockIs
  have readIs : encode relabel here (.apply "AAmb" [parent, .collection .hashBag contents none]) =
      .apply "LNu" [.lambda none (.collection .hashBag [marker, .collection .hashBag
        (contents.map (encode (Nat.succ ∘ relabel) (.bvar 0))) none] none)] := by
    rw [encode_amb, encode_bag]
  have moverIs : encode (Nat.succ ∘ relabel) (.bvar 0) contents[i] = moverBlock.toPattern locatedBlock := by
    rw [mover, encode_amb, encode_bag, shiftName_bvar]
    rfl
  rw [readIs] at typed ⊢
  -- inside the parent's location
  obtain ⟨insideTyped, -, -⟩ := signature.restriction_typed typed
  have insideMembers := members_of_bag (language := locatedCalc) (block := locatedBlock) insideTyped
  have markerTyped := insideMembers marker (by simp)
  have contentMembers := members_of_bag (language := locatedCalc) (block := locatedBlock)
    (insideMembers (.collection .hashBag (contents.map (encode (Nat.succ ∘ relabel) (.bvar 0))) none) (by simp))
  -- the mover found in the content, last
  have contentPerm : (contents.map (encode (Nat.succ ∘ relabel) (.bvar 0))).Perm
      ((contents.eraseIdx i).map (encode (Nat.succ ∘ relabel) (.bvar 0)) ++ [moverBlock.toPattern locatedBlock]) := by
    have found := List.getElem_cons_eraseIdx_perm (l := contents.map (encode (Nat.succ ∘ relabel) (.bvar 0)))
      (n := i) (by simpa using hi)
    simp only [List.getElem_map, List.eraseIdx_map] at found
    rw [moverIs] at found
    exact found.symm.trans (List.perm_append_singleton _ _).symm
  have restMembers : Members locatedCalc locatedBlock free (nameType :: bound)
      ((contents.eraseIdx i).map (encode (Nat.succ ∘ relabel) (.bvar 0))) := fun element member =>
    contentMembers element (contentPerm.symm.subset (List.mem_append_left _ member))
  have moverTyped := contentMembers _ (contentPerm.symm.subset (List.mem_append_right _ (List.mem_singleton_self _)))
  have restTyped : HasType locatedCalc free (nameType :: bound) restRead procType :=
    signature.bag_typed (rest := none) (elementsHaveType_iff.mpr restMembers)
  obtain ⟨moverBody, -, -⟩ := signature.restriction_typed moverTyped
  have moverMembers : Members locatedCalc locatedBlock free (List.replicate moverBlock.count nameType ++
      (nameType :: bound)) moverBlock.components := members_of_bag (language := locatedCalc) (block := locatedBlock)
    moverBody
  have outerMembers : Members locatedCalc locatedBlock free (List.replicate outerBlock.count nameType ++
      (nameType :: bound)) outerBlock.components := by
    intro element member
    simp only [outerBlockIs, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact markerTyped
    · exact restTyped
  -- the content flattened, the mover last, the parent's rest regrouped beside its marker
  have flatMembers : Members locatedCalc locatedBlock free (nameType :: bound)
      ([marker] ++ contents.map (encode (Nat.succ ∘ relabel) (.bvar 0)) ++ []) := by
    intro element member
    simp only [List.append_nil, List.singleton_append, List.mem_cons] at member
    rcases member with rfl | inContent
    · exact markerTyped
    · exact contentMembers element inContent
  have flattened := flatten_equivalent (pre := [marker]) (post := []) flatMembers
  simp only [List.append_nil, List.singleton_append] at flattened
  have permMembers : Members locatedCalc locatedBlock free (nameType :: bound)
      (marker :: contents.map (encode (Nat.succ ∘ relabel) (.bvar 0))) := by simpa using flatMembers
  have permuted := bag_perm_equivalent (language := locatedCalc) (block := locatedRepBlock) permMembers
    (contentPerm.cons marker)
  have splitMembers : Members locatedCalc locatedBlock free (nameType :: bound)
      ([marker] ++ (contents.eraseIdx i).map (encode (Nat.succ ∘ relabel) (.bvar 0)) ++
        [moverBlock.toPattern locatedBlock]) := by
    intro element member
    simp only [List.cons_append, List.mem_cons] at member
    rcases member with rfl | inRest
    · exact markerTyped
    · exact contentMembers element (contentPerm.symm.subset inRest)
  have restGrouped := flatten_equivalent (pre := [marker]) (post := [moverBlock.toPattern locatedBlock]) splitMembers
  simp only [List.cons_append] at restGrouped
  have pairMembers : Members locatedCalc locatedBlock free (nameType :: bound)
      ([] ++ [marker, restRead] ++ [moverBlock.toPattern locatedBlock]) := by
    intro element member
    simp only [List.nil_append, List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact markerTyped
    · exact restTyped
    · exact moverTyped
  have outerGrouped := flatten_equivalent (pre := []) (inner := [marker, restRead])
    (post := [moverBlock.toPattern locatedBlock]) pairMembers
  simp only [List.nil_append, List.cons_append] at outerGrouped
  have joined := par_equivalent (language := locatedCalc) (block := locatedBlock) outerMembers moverMembers
  have insideChain : ProcEquiv locatedCalc locatedBlock free (nameType :: bound)
      (.collection .hashBag [marker, .collection .hashBag (contents.map (encode (Nat.succ ∘ relabel) (.bvar 0))) none]
        none)
      ((outerBlock.par moverBlock).toPattern locatedBlock) :=
    .trans _ _ _ flattened (.trans _ _ _ permuted (.trans _ _ _ (.symm _ _ restGrouped)
      (.trans _ _ _ (.symm _ _ outerGrouped) joined)))
  have closed := restrict_fill (language := locatedCalc) (block := locatedBlock) insideChain
  -- the joined block, regrouped and read with the redex's own variables
  have flatIs : Pattern.apply locatedBlock.restrict [.lambda none ((outerBlock.par moverBlock).toPattern locatedBlock)] =
      Prenex.restricts locatedBlock 2 (.collection .hashBag
        ([liftBVars 0 1 marker, liftBVars 0 1 restRead,
          .apply "LAmb" [.bvar 1, .bvar 0, rename (Nat.succ ∘ Nat.succ ∘ relabel) name]] ++
        [.collection .hashBag (inner.map (encode (Nat.succ ∘ Nat.succ ∘ relabel) (.bvar 0))) none])
        none) := by
    simp only [Prenex.toPattern, Prenex.par, outerBlockIs, moverBlockIs, List.map_cons, List.map_nil,
      Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero]
    rfl
  have blockMembers : Members locatedCalc locatedBlock free (List.replicate 2 nameType ++ bound)
      ([liftBVars 0 1 marker, liftBVars 0 1 restRead,
          .apply "LAmb" [.bvar 1, .bvar 0, rename (Nat.succ ∘ Nat.succ ∘ relabel) name]] ++
        inner.map (encode (Nat.succ ∘ Nat.succ ∘ relabel) (.bvar 0))) := by
    have joinedMembers := par_members (language := locatedCalc) (block := locatedBlock) outerMembers moverMembers
    have whole : Members locatedCalc locatedBlock free (List.replicate 2 nameType ++ bound)
        ([liftBVars 0 1 marker, liftBVars 0 1 restRead,
          .apply "LAmb" [.bvar 1, .bvar 0, rename (Nat.succ ∘ Nat.succ ∘ relabel) name]] ++
        [.collection .hashBag (inner.map (encode (Nat.succ ∘ Nat.succ ∘ relabel) (.bvar 0))) none]) := by
      have componentsIs : (outerBlock.par moverBlock).components =
          [liftBVars 0 1 marker, liftBVars 0 1 restRead,
            .apply "LAmb" [.bvar 1, .bvar 0, rename (Nat.succ ∘ Nat.succ ∘ relabel) name]] ++
          [.collection .hashBag (inner.map (encode (Nat.succ ∘ Nat.succ ∘ relabel) (.bvar 0))) none] := by
        simp only [Prenex.par, outerBlockIs, moverBlockIs, List.map_cons, List.map_nil,
          Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero]
        rfl
      rw [← componentsIs]
      exact joinedMembers
    intro element member
    rcases List.mem_append.mp member with inFront | inContent
    · exact whole element (List.mem_append_left _ inFront)
    · exact members_of_bag (language := locatedCalc) (block := locatedBlock)
        (whole _ (List.mem_append_right _ (List.mem_singleton_self _))) element inContent
  have capabilityPerm : (inner.map (encode (Nat.succ ∘ Nat.succ ∘ relabel) (.bvar 0))).Perm
      (encode (Nat.succ ∘ Nat.succ ∘ relabel) (.bvar 0) inner[k] ::
        (inner.eraseIdx k).map (encode (Nat.succ ∘ Nat.succ ∘ relabel) (.bvar 0))) := by
    have found := List.getElem_cons_eraseIdx_perm (l := inner.map (encode (Nat.succ ∘ Nat.succ ∘ relabel) (.bvar 0)))
      (n := k) (by simpa using hk)
    simp only [List.getElem_map, List.eraseIdx_map] at found
    exact found.symm
  have regrouped := restricts_congr (language := locatedCalc) (block := locatedBlock) 2
    (regroup capabilityPerm blockMembers)
  have leftTyped := (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.SortedEquiv.typed_iff closed).mp typed
  rw [flatIs] at closed leftTyped
  have rightTyped := (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.SortedEquiv.typed_iff regrouped).mp leftTyped
  have headIs : encode (Nat.succ ∘ Nat.succ ∘ relabel) (.bvar 0) inner[k] =
      .apply "LOut" [.bvar 0, rename (Nat.succ ∘ Nat.succ ∘ relabel) parent,
        encode (Nat.succ ∘ Nat.succ ∘ relabel) (.bvar 0) process] := by
    rw [capability, encode_out]
  have othersIs : ((contents.eraseIdx i).map (encode (Nat.succ ∘ relabel) (.bvar 0))).map (liftBVars 0 1) =
      (contents.eraseIdx i).map (encode (Nat.succ ∘ Nat.succ ∘ relabel) (.bvar 1)) := by
    rw [List.map_map]
    exact List.map_congr_left fun element _ => lift_outer_encode relabel element
  have frontIs : [liftBVars 0 1 marker, liftBVars 0 1 restRead,
        Pattern.apply "LAmb" [.bvar 1, .bvar 0, rename (Nat.succ ∘ Nat.succ ∘ relabel) name]] =
      [.apply "LAmb" [liftBVars 0 1 (shiftName here), .bvar 1, rename (Nat.succ ∘ Nat.succ ∘ relabel) parent],
        .collection .hashBag ((contents.eraseIdx i).map (encode (Nat.succ ∘ Nat.succ ∘ relabel) (.bvar 1))) none,
        .apply "LAmb" [.bvar 1, .bvar 0, rename (Nat.succ ∘ Nat.succ ∘ relabel) name]] := by
    rw [restReadIs, liftBVars_bag, othersIs]
    simp only [markerIs, liftBVars, Mettapedia.OSLF.MeTTaIL.Substitution.liftBVarsList_eq_map, List.map_cons,
      List.map_nil]
    rw [lift_outer_name]
    simp
  rw [headIs, frontIs] at regrouped rightTyped
  rw [frontIs] at closed
  obtain ⟨outerBody, -, -⟩ := signature.restriction_typed rightTyped
  obtain ⟨typedBody, -, -⟩ := signature.restriction_typed outerBody
  have reachedMembers := members_of_bag (language := locatedCalc) (block := locatedBlock) typedBody
  have reordered := restricts_congr (language := locatedCalc) (block := locatedBlock) 2
    (bag_perm_equivalent (language := locatedCalc) (block := locatedRepBlock) reachedMembers
      ((List.perm_middle (l₁ := [_, _, _, _]) (l₂ := [])).trans
        (((List.Perm.swap _ _ [_]).cons _).cons _)))
  exact .trans _ _ _ closed (.trans _ _ _ regrouped reordered)


/-! ## Leaving as a reaction -/

/-- **An ambient leaving its parent reacts as located atoms** at the front of the block of their locations. -/
theorem reacts_exit {bound : List TypeExpr} {relabel : Nat → Nat} {here name parent process : Pattern}
    {contents inner : List Pattern} {i k : Nat} (hi : i < contents.length)
    (mover : contents[i] = .apply "AAmb" [name, .collection .hashBag inner none])
    (hk : k < inner.length) (capability : inner[k] = .apply "AOut" [parent, process])
    (hereObject : isObjectPattern here = true)
    (object : isObjectPattern (.apply "AAmb" [parent, .collection .hashBag contents none]) = true)
    (sourceTyped : HasType locatedCalc free bound
      (encode relabel here (.apply "AAmb" [parent, .collection .hashBag contents none])) procType)
    (contractumTyped : HasType locatedCalc free bound (encode relabel here (.collection .hashBag
      [.apply "AAmb" [name, .collection .hashBag (process :: inner.eraseIdx k) none],
        .apply "AAmb" [parent, .collection .hashBag (contents.eraseIdx i) none]] none)) procType) :
    ∃ count redex rest, ReplicationStepAt locatedReactions free bound
      (encode relabel here (.apply "AAmb" [parent, .collection .hashBag contents none]))
      (encode relabel here (.collection .hashBag
        [.apply "AAmb" [name, .collection .hashBag (process :: inner.eraseIdx k) none],
          .apply "AAmb" [parent, .collection .hashBag (contents.eraseIdx i) none]] none))
      count redex rest := by
  have signature : BlockSignature locatedCalc locatedBlock := locatedLanguage.toBlockSignature
  -- the pieces are object terms
  obtain ⟨parentObject, contentsBagObject⟩ := pair_objects object
  obtain ⟨-, contentsObjects⟩ := bag_objects contentsBagObject
  have moverObject := contentsObjects _ (List.getElem_mem hi)
  rw [mover] at moverObject
  obtain ⟨nameObject, innerBagObject⟩ := pair_objects moverObject
  obtain ⟨-, innerObjects⟩ := bag_objects innerBagObject
  have capabilityObject := innerObjects _ (List.getElem_mem hk)
  rw [capability] at capabilityObject
  obtain ⟨-, processObject⟩ := pair_objects capabilityObject
  -- the source and the contractum as blocks
  have source := exit_source_block hi mover hk capability sourceTyped
  rw [encode_bag] at contractumTyped ⊢
  simp only [List.map_cons, List.map_nil] at contractumTyped ⊢
  have target' := exit_target_block (inner := inner.eraseIdx k) (others := contents.eraseIdx i) contractumTyped
  refine ⟨2, LocRedex.move false (liftBVars 0 1 (shiftName here)) (.bvar 0) (.bvar 1)
      (rename (Nat.succ ∘ Nat.succ ∘ relabel) name) (rename (Nat.succ ∘ Nat.succ ∘ relabel) parent)
      (encode (Nat.succ ∘ Nat.succ ∘ relabel) (.bvar 0) process),
    [.collection .hashBag ((inner.eraseIdx k).map (encode (Nat.succ ∘ Nat.succ ∘ relabel) (.bvar 0))) none,
      .collection .hashBag ((contents.eraseIdx i).map (encode (Nat.succ ∘ Nat.succ ∘ relabel) (.bvar 1))) none],
    ⟨?_, ?_, source.toEquationEquiv, target'.toEquationEquiv⟩⟩
  · have blockTyped := (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.SortedEquiv.typed_iff source).mp sourceTyped
    obtain ⟨outerBody, -, -⟩ := signature.restriction_typed blockTyped
    obtain ⟨typedBody, -, -⟩ := signature.restriction_typed outerBody
    exact members_of_bag (language := locatedCalc) (block := locatedBlock) typedBody
  · have placeObject : isObjectPattern (liftBVars 0 1 (shiftName here)) = true :=
      lift_object 0 1 (by rw [shiftName, isObjectPattern_rename]; exact hereObject)
    have renamedObject : ∀ {pattern : Pattern}, isObjectPattern pattern = true →
        isObjectPattern (rename (Nat.succ ∘ Nat.succ ∘ relabel) pattern) = true := fun object => by
      rw [isObjectPattern_rename]; exact object
    intro element member
    simp only [locatedReactions, LocRedex.parts, LocRedex.before, LocRedex.capability, Bool.false_eq_true,
      if_false, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · simp [isObjectPattern, isObjectPatternList, renamedObject nameObject]
    · simp [isObjectPattern, isObjectPatternList, renamedObject parentObject,
        encode_object' (here := .bvar 0) rfl processObject]
    · simp [isObjectPattern, isObjectPatternList, placeObject, renamedObject parentObject]
    · simp only [isObjectPattern, Bool.and_eq_true, Option.isNone_none, true_and,
        Mettapedia.GSLT.LanguageDef.BagNormalForm.isObjectPatternList_iff]
      intro element member
      obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp member
      exact encode_object' rfl (innerObjects original (List.mem_of_mem_eraseIdx inOriginal))
    · simp only [isObjectPattern, Bool.and_eq_true, Option.isNone_none, true_and,
        Mettapedia.GSLT.LanguageDef.BagNormalForm.isObjectPatternList_iff]
      intro element member
      obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp member
      exact encode_object' rfl (contentsObjects original (List.mem_of_mem_eraseIdx inOriginal))

end Mettapedia.Languages.ProcessCalculi.Ambient.Steps
