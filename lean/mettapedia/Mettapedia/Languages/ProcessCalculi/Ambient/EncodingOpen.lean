import Mettapedia.Languages.ProcessCalculi.Ambient.EncodingMoves

/-!
# Opening in located form

An ambient opened by a capability beside it is, in located form, a reaction of two located atoms at the front of the
block of the ambient's location: the capability and the ambient's marker. The capability leaves its continuation where
it stood, and the marker is left opened (`openedForm`): what stands at the ambient's location then stands where the
ambient stood, which is how an opened marker reads back (`decode_opened`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Steps

open Mettapedia.Languages.ProcessCalculi.Ambient.Comm (ambientCoreCalc)

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)
open Mettapedia.GSLT.LanguageDef.WellSorted (HasType FreeTypeContext isObjectPattern isObjectPatternList)
open Mettapedia.GSLT.LanguageDef.BagNormalForm (elementsHaveType_iff)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (Prenex ProcEquiv Members rename rename_bvar canonP
  canonFacts restrictionsBind_of_typed canonsP_eq_map par_nil normal_close_normal par_atomic decompose_atom
  isObjectPattern_rename size)

open Mettapedia.Languages.ProcessCalculi.Ambient.Located (locatedCalc locatedBlock locatedRepBlock locatedLanguage)
open Mettapedia.Languages.ProcessCalculi.Ambient.Encoding (NameContext nameType procType encode shiftName
  encode_typed encode_object rename_name_typed name_cases_ambient)
open Mettapedia.Languages.ProcessCalculi.Ambient.Decoding (EncodeFacts LocVariables underLocation names_base
  underLocation_locVariables decode_encode encodeFacts_marker wrapContent_opened markers rename_succ_comp
  rename_process_typed canonP_located_restrict canonP_triple canonP_variable shiftName_bvar isVariable
  isVariable_rename)

variable {free : FreeTypeContext}

/-- **An opened ambient in located form**: its opened marker beside its content's located form, under its
location. -/
def openedForm (relabel : Nat → Nat) (here name content : Pattern) : Pattern :=
  .apply "LNu" [.lambda none (.collection .hashBag
    [.apply "LOpened" [shiftName here, .bvar 0, rename (Nat.succ ∘ relabel) name],
      encode (Nat.succ ∘ relabel) (.bvar 0) content] none)]

/-- **An opened ambient's located form reads back as its content**, its location garbage. -/
theorem decode_opened (names : NameContext free) {count count' : Nat} {relabel : Nat → Nat} {here : Nat}
    {isLoc : Pattern → Prop} {name content : Pattern} (inside : ∀ index < count, relabel index < count')
    (hereBelow : here < count') (locVariables : LocVariables isLoc) (hereLoc : isLoc (.bvar here))
    (namesApart : ∀ index < count, ¬ isLoc (.bvar (relabel index))) (fvarsApart : ∀ name, ¬ isLoc (.fvar name))
    (nameTyped : HasType ambientCoreCalc free (List.replicate count nameType) name nameType)
    (nameObject : isObjectPattern name = true)
    (contentTyped : HasType ambientCoreCalc free (List.replicate count nameType) content procType)
    (contentObject : isObjectPattern content = true) :
    EncodeFacts free isLoc here (List.replicate count' nameType)
      (canonP locatedRepBlock (openedForm relabel (.bvar here) name content)) (rename relabel content) := by
  have fresh : locatedRepBlock.replicate ∉ locatedRepBlock.emptyUnits := by decide
  have restrictFresh : locatedRepBlock.replicate ≠ locatedRepBlock.restrict := by decide
  -- the name, renamed, is a variable apart from the locations
  obtain ⟨nameVar, nameApart⟩ : isVariable (rename relabel name) = true ∧
      ¬ underLocation isLoc (liftBVars 0 1 (rename relabel name)) := by
    rcases name_cases_ambient nameTyped rfl nameObject with ⟨index, rfl, found⟩ | ⟨name, rfl, found⟩
    · have below : index < count := by
        have := List.getElem?_eq_some_iff.mp found
        simpa using this.1
      exact ⟨rfl, by simpa [rename_bvar, liftBVars, underLocation] using namesApart index below⟩
    · exact ⟨rfl, fvarsApart name⟩
  have shifted : ∀ index < count, (Nat.succ ∘ relabel) index < count' + 1 := fun index below => by
    have := inside index below
    simp only [Function.comp]
    omega
  -- the content read at the ambient's location
  have inner := decode_encode names (size content + 1) (count' := count' + 1)
    (relabel := Nat.succ ∘ relabel) (here := 0) (isLoc := underLocation isLoc) (Nat.lt_succ_self _) shifted
    (by omega) (underLocation_locVariables isLoc) (by simp [underLocation])
    (fun index below => by simpa [underLocation, Function.comp] using namesApart index below)
    (fun name => by simpa [underLocation] using fvarsApart name) contentTyped contentObject
  rw [rename_succ_comp] at inner
  have contentFacts : Mettapedia.GSLT.LanguageDef.RestrictionBlocks.CanonFacts locatedRepBlock
      (encode (Nat.succ ∘ relabel) (.bvar 0) content) :=
    canonFacts fresh restrictFresh (encode_object (size content + 1) (Nat.lt_succ_self _) rfl contentObject)
      (restrictionsBind_of_typed (block := locatedRepBlock) _ (encode_typed names (size content + 1)
        (Nat.lt_succ_self _) shifted (.bvar (by simp)) rfl contentTyped contentObject))
  have renamedObject : isObjectPattern (rename (Nat.succ ∘ relabel) name) = true := by
    rw [isObjectPattern_rename]
    exact nameObject
  have renamedVar : isVariable (rename (Nat.succ ∘ relabel) name) = true := by
    rw [isVariable_rename, ← isVariable_rename relabel name]
    exact nameVar
  have markerCanon : canonP locatedRepBlock
      (.apply "LOpened" [shiftName (.bvar here), .bvar 0, rename (Nat.succ ∘ relabel) name]) =
      Prenex.atom (.apply "LOpened" [shiftName (.bvar here), .bvar 0, liftBVars 0 1 (rename relabel name)]) := by
    rw [shiftName_bvar, canonP_triple (by decide) rfl rfl renamedObject, canonP_variable renamedVar,
      rename_succ_comp]
    rfl
  have markerAtomic : (Prenex.atom (.apply "LOpened" [shiftName (.bvar here), .bvar 0,
      liftBVars 0 1 (rename relabel name)])).Atomic locatedRepBlock.toBlock := by
    intro component member
    simp only [Prenex.atom, List.mem_singleton] at member
    subst member
    rw [shiftName_bvar]
    exact decompose_atom (by simp) (by simp) (by simp) (by simp)
  rw [openedForm, canonP_located_restrict, Mettapedia.GSLT.LanguageDef.RestrictionBlocks.canonP_bag, canonsP_eq_map,
    List.map_cons, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_cons, List.foldr_nil, par_nil,
    markerCanon, normal_close_normal fresh restrictFresh (par_atomic markerAtomic contentFacts.atomic)]
  have openedFacts := encodeFacts_marker (show "LOpened" ∈ markers by simp [markers]) hereLoc
    (by simp [hereBelow]) nameVar nameApart (rename_name_typed inside nameTyped nameObject)
    (rename_process_typed inside contentTyped) inner
  rw [wrapContent_opened] at openedFacts
  exact openedFacts.normal (names_base names count') locVariables


/-! ## Opening: the redex as a block -/

open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (BlockSignature SortedEquiv par_equivalent members_of_bag
  liftBVars_eq_rename shiftAbove ReplicationStepAt ReactsAt)
open Mettapedia.Languages.ProcessCalculi.Ambient.Encoding (encode_amb encode_open encode_bag rename_encode
  opened_typed)
open Mettapedia.Languages.ProcessCalculi.Ambient.Decoding (shiftName_eq triple_inv)

/-- A located form read under one more name outside it, its place read there too. -/
theorem lift_encode (relabel : Nat → Nat) (here process : Pattern) :
    liftBVars 0 1 (encode relabel here process) = encode (Nat.succ ∘ relabel) (shiftName here) process := by
  rw [liftBVars_eq_rename, rename_encode _ (Nat.lt_succ_self _), shiftName]
  have succIs : shiftAbove 0 1 = Nat.succ := by
    funext index
    simp [shiftAbove]
  rw [succIs]

/-- **A capability opening an ambient beside it is, with the ambient, a block of the ambient's location**: the
redex's parts in front of the ambient's content. -/
theorem open_source_block {bound : List TypeExpr} {relabel : Nat → Nat} {here name process content : Pattern}
    (pairTyped : HasType locatedCalc free bound (.collection .hashBag
      [encode relabel here (.apply "AOpen" [name, process]), encode relabel here (.apply "AAmb" [name, content])]
      none) procType) :
    ProcEquiv locatedCalc locatedBlock free bound
      (.collection .hashBag [encode relabel here (.apply "AOpen" [name, process]),
        encode relabel here (.apply "AAmb" [name, content])] none)
      (Prenex.restricts locatedBlock 1 (.collection .hashBag
        (LocRedex.parts (.open (shiftName here) (.bvar 0) (rename (Nat.succ ∘ relabel) name)
            (encode (Nat.succ ∘ relabel) (shiftName here) process)) ++
          [encode (Nat.succ ∘ relabel) (.bvar 0) content]) none)) := by
  have signature : BlockSignature locatedCalc locatedBlock := locatedLanguage.toBlockSignature
  set capability := encode relabel here (.apply "AOpen" [name, process]) with capabilityIs
  set ambient : Prenex := ⟨1, [.apply "LAmb" [shiftName here, .bvar 0, rename (Nat.succ ∘ relabel) name],
    encode (Nat.succ ∘ relabel) (.bvar 0) content]⟩ with ambientIs
  have ambientRead : encode relabel here (.apply "AAmb" [name, content]) = ambient.toPattern locatedBlock := by
    rw [encode_amb]
    rfl
  rw [ambientRead] at pairTyped ⊢
  have pairMembers := members_of_bag (language := locatedCalc) (block := locatedBlock) pairTyped
  have capabilityTyped := pairMembers capability (by simp)
  obtain ⟨ambientBody, -, -⟩ := signature.restriction_typed (pairMembers (ambient.toPattern locatedBlock) (by simp))
  have ambientMembers : Members locatedCalc locatedBlock free (List.replicate ambient.count nameType ++ bound)
      ambient.components := members_of_bag (language := locatedCalc) (block := locatedBlock) ambientBody
  have atomMembers : Members locatedCalc locatedBlock free
      (List.replicate (Prenex.atom capability).count nameType ++ bound) (Prenex.atom capability).components := by
    intro element member
    simp only [Prenex.atom, List.mem_singleton] at member
    subst member
    simpa [Prenex.atom] using capabilityTyped
  have liftedCapability : liftBVars 0 1 capability = .apply "LOpen" [shiftName here,
      rename (Nat.succ ∘ relabel) name, encode (Nat.succ ∘ relabel) (shiftName here) process] := by
    rw [capabilityIs, encode_open]
    simp only [liftBVars, Mettapedia.OSLF.MeTTaIL.Substitution.liftBVarsList_eq_map, List.map_cons, List.map_nil]
    rw [← shiftName_eq, ← rename_succ_comp, lift_encode]
  have joined := par_equivalent (language := locatedCalc) (block := locatedBlock) atomMembers ambientMembers
  have flatIs : ((Prenex.atom capability).par ambient).toPattern locatedBlock =
      Prenex.restricts locatedBlock 1 (.collection .hashBag
        (LocRedex.parts (.open (shiftName here) (.bvar 0) (rename (Nat.succ ∘ relabel) name)
            (encode (Nat.succ ∘ relabel) (shiftName here) process)) ++
          [encode (Nat.succ ∘ relabel) (.bvar 0) content]) none) := by
    simp only [Prenex.toPattern, Prenex.par, Prenex.atom, ambientIs, List.map_cons, List.map_nil,
      Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero, liftedCapability]
    rfl
  rw [flatIs] at joined
  exact joined

/-- **A continuation beside an opened ambient is a block of the ambient's location**: the redex's results in front of
the ambient's content. -/
theorem open_target_block {bound : List TypeExpr} {relabel : Nat → Nat} {here name process content : Pattern}
    (pairTyped : HasType locatedCalc free bound (.collection .hashBag
      [encode relabel here process, openedForm relabel here name content] none) procType) :
    ProcEquiv locatedCalc locatedBlock free bound
      (.collection .hashBag [encode relabel here process, openedForm relabel here name content] none)
      (Prenex.restricts locatedBlock 1 (.collection .hashBag
        (LocRedex.result (.open (shiftName here) (.bvar 0) (rename (Nat.succ ∘ relabel) name)
            (encode (Nat.succ ∘ relabel) (shiftName here) process)) ++
          [encode (Nat.succ ∘ relabel) (.bvar 0) content]) none)) := by
  have signature : BlockSignature locatedCalc locatedBlock := locatedLanguage.toBlockSignature
  set continuation := encode relabel here process with continuationIs
  set opened : Prenex := ⟨1, [.apply "LOpened" [shiftName here, .bvar 0, rename (Nat.succ ∘ relabel) name],
    encode (Nat.succ ∘ relabel) (.bvar 0) content]⟩ with openedIs
  have openedRead : openedForm relabel here name content = opened.toPattern locatedBlock := rfl
  rw [openedRead] at pairTyped ⊢
  have pairMembers := members_of_bag (language := locatedCalc) (block := locatedBlock) pairTyped
  have continuationTyped := pairMembers continuation (by simp)
  obtain ⟨openedBody, -, -⟩ := signature.restriction_typed (pairMembers (opened.toPattern locatedBlock) (by simp))
  have openedMembers : Members locatedCalc locatedBlock free (List.replicate opened.count nameType ++ bound)
      opened.components := members_of_bag (language := locatedCalc) (block := locatedBlock) openedBody
  have atomMembers : Members locatedCalc locatedBlock free
      (List.replicate (Prenex.atom continuation).count nameType ++ bound) (Prenex.atom continuation).components := by
    intro element member
    simp only [Prenex.atom, List.mem_singleton] at member
    subst member
    simpa [Prenex.atom] using continuationTyped
  have joined := par_equivalent (language := locatedCalc) (block := locatedBlock) atomMembers openedMembers
  have flatIs : ((Prenex.atom continuation).par opened).toPattern locatedBlock =
      Prenex.restricts locatedBlock 1 (.collection .hashBag
        (LocRedex.result (.open (shiftName here) (.bvar 0) (rename (Nat.succ ∘ relabel) name)
            (encode (Nat.succ ∘ relabel) (shiftName here) process)) ++
          [encode (Nat.succ ∘ relabel) (.bvar 0) content]) none) := by
    simp only [Prenex.toPattern, Prenex.par, Prenex.atom, openedIs, List.map_cons, List.map_nil,
      Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero, continuationIs, lift_encode]
    rfl
  rw [flatIs] at joined
  exact joined

/-! ## Opening as a reaction -/

/-- **An opened ambient's located form is typed** where the ambient's is. -/
theorem openedForm_typed {bound : List TypeExpr} {relabel : Nat → Nat} {here name content : Pattern}
    (typed : HasType locatedCalc free bound (encode relabel here (.apply "AAmb" [name, content])) procType) :
    HasType locatedCalc free bound (openedForm relabel here name content) procType := by
  have signature : BlockSignature locatedCalc locatedBlock := locatedLanguage.toBlockSignature
  rw [encode_amb] at typed
  obtain ⟨body, -, -⟩ := signature.restriction_typed typed
  have members := members_of_bag (language := locatedCalc) (block := locatedBlock) body
  have markerTyped := members (.apply "LAmb" [shiftName here, .bvar 0, rename (Nat.succ ∘ relabel) name]) (by simp)
  have contentTyped := members (encode (Nat.succ ∘ relabel) (.bvar 0) content) (by simp)
  obtain ⟨locationTyped, nameTyped⟩ : HasType locatedCalc free (nameType :: bound) (.bvar 0) nameType ∧
      HasType locatedCalc free (nameType :: bound) (rename (Nat.succ ∘ relabel) name) nameType := by
    rcases triple_inv markerTyped with ⟨-, second, third⟩ | ⟨listed, -, -⟩ | ⟨isCap, -, -⟩
    · exact ⟨second, third⟩
    · simp at listed
    · simp at isCap
  have openedTyped := opened_typed (triple_first markerTyped) locationTyped nameTyped
  have bagTyped : HasType locatedCalc free (nameType :: bound) (.collection .hashBag
      [.apply "LOpened" [shiftName here, .bvar 0, rename (Nat.succ ∘ relabel) name],
        encode (Nat.succ ∘ relabel) (.bvar 0) content] none) procType := by
    apply signature.bag_typed (rest := none)
    apply elementsHaveType_iff.mpr
    intro element member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact openedTyped
    · exact contentTyped
  exact Mettapedia.GSLT.LanguageDef.RestrictionBlocks.restricts_typed (language := locatedCalc)
    (block := locatedBlock) 1 bagTyped

/-- **A capability opening an ambient beside it reacts with the ambient's marker**, at the front of the block of the
ambient's location. -/
theorem reacts_open_core {bound : List TypeExpr} {relabel : Nat → Nat} {here name process content : Pattern}
    (hereObject : isObjectPattern here = true) (nameObject : isObjectPattern name = true)
    (processObject : isObjectPattern process = true) (contentObject : isObjectPattern content = true)
    (pairTyped : HasType locatedCalc free bound (.collection .hashBag
      [encode relabel here (.apply "AOpen" [name, process]), encode relabel here (.apply "AAmb" [name, content])]
      none) procType)
    (contractumTyped : HasType locatedCalc free bound (.collection .hashBag
      [encode relabel here process, openedForm relabel here name content] none) procType) :
    ∃ count redex rest, ReplicationStepAt locatedReactions free bound
      (.collection .hashBag [encode relabel here (.apply "AOpen" [name, process]),
        encode relabel here (.apply "AAmb" [name, content])] none)
      (.collection .hashBag [encode relabel here process, openedForm relabel here name content] none)
      count redex rest := by
  have signature : BlockSignature locatedCalc locatedBlock := locatedLanguage.toBlockSignature
  have source := open_source_block pairTyped
  have target' := open_target_block contractumTyped
  refine ⟨1, LocRedex.open (shiftName here) (.bvar 0) (rename (Nat.succ ∘ relabel) name)
      (encode (Nat.succ ∘ relabel) (shiftName here) process),
    [encode (Nat.succ ∘ relabel) (.bvar 0) content],
    ⟨?_, ?_, source.toEquationEquiv, target'.toEquationEquiv⟩⟩
  · have blockTyped := (SortedEquiv.typed_iff source).mp pairTyped
    obtain ⟨typedBody, -, -⟩ := signature.restriction_typed blockTyped
    exact members_of_bag (language := locatedCalc) (block := locatedBlock) typedBody
  · have placeObject : isObjectPattern (shiftName here) = true := by
      rw [shiftName, isObjectPattern_rename]
      exact hereObject
    have renamedObject : isObjectPattern (rename (Nat.succ ∘ relabel) name) = true := by
      rw [isObjectPattern_rename]
      exact nameObject
    intro element member
    simp only [locatedReactions, LocRedex.parts, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · simp [isObjectPattern, isObjectPatternList, placeObject, renamedObject,
        encode_object' (relabel := Nat.succ ∘ relabel) placeObject processObject]
    · simp [isObjectPattern, isObjectPatternList, placeObject, renamedObject]
    · exact encode_object' rfl contentObject


open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (bag_perm_equivalent)

/-- **A capability opening an ambient beside it, among other components, reacts** at the front of a block, leaving
its continuation beside the opened ambient. -/
theorem reacts_open {bound : List TypeExpr} {relabel : Nat → Nat} {here : Pattern} {elements : List Pattern}
    {i j : Nat} (hi : i < elements.length) (hj : j < (elements.eraseIdx i).length) {name process content : Pattern}
    (capability : elements[i] = .apply "AOpen" [name, process])
    (boundary : (elements.eraseIdx i)[j] = .apply "AAmb" [name, content])
    (hereObject : isObjectPattern here = true) (objects : ∀ element ∈ elements, isObjectPattern element = true)
    (sourceTyped : HasType locatedCalc free bound (encode relabel here (.collection .hashBag elements none))
      procType) :
    ∃ count redex rest, ReplicationStepAt locatedReactions free bound
      (encode relabel here (.collection .hashBag elements none))
      (.collection .hashBag (encode relabel here process :: openedForm relabel here name content ::
        ((elements.eraseIdx i).eraseIdx j).map (encode relabel here)) none) count redex rest := by
  have signature : BlockSignature locatedCalc locatedRepBlock.toBlock := locatedLanguage.toBlockSignature
  set others := (elements.eraseIdx i).eraseIdx j with othersIs
  -- the pieces are object terms
  have capabilityObject := objects _ (List.getElem_mem hi)
  have boundaryObject := objects _ (List.mem_of_mem_eraseIdx (List.getElem_mem hj))
  rw [capability] at capabilityObject
  rw [boundary] at boundaryObject
  obtain ⟨nameObject, processObject⟩ := pair_objects capabilityObject
  obtain ⟨-, contentObject⟩ := pair_objects boundaryObject
  -- the capability and the ambient first, as one member
  have permutation := perm_two elements i hi j hj
  rw [capability, boundary] at permutation
  rw [encode_bag] at sourceTyped ⊢
  have sourceMembers := members_of_bag (language := locatedCalc) (block := locatedBlock) sourceTyped
  have mappedPerm := permutation.map (encode relabel here)
  simp only [List.map_cons] at mappedPerm
  have pairMembers : Members locatedCalc locatedBlock free bound
      [encode relabel here (.apply "AOpen" [name, process]), encode relabel here (.apply "AAmb" [name, content])] :=
    fun element member => sourceMembers element (mappedPerm.symm.subset (by simp at member ⊢; tauto))
  have pairTyped := signature.bag_typed (rest := none) (elementsHaveType_iff.mpr pairMembers)
  -- what is left is typed where the capability and the ambient are
  have capabilityTyped := pairMembers _ List.mem_cons_self
  rw [encode_open] at capabilityTyped
  have continuationTyped : HasType locatedCalc free bound (encode relabel here process) procType := by
    rcases triple_inv capabilityTyped with ⟨isMarker, -⟩ | ⟨-, -, third⟩ | ⟨-, -, third⟩
    · simp [markers] at isMarker
    · exact third
    · exact third
  have openedTyped := openedForm_typed (pairMembers (encode relabel here (.apply "AAmb" [name, content])) (by simp))
  have contractumMembers : Members locatedCalc locatedBlock free bound
      [encode relabel here process, openedForm relabel here name content] := by
    intro element member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact continuationTyped
    · exact openedTyped
  have contractumTyped := signature.bag_typed (rest := none) (elementsHaveType_iff.mpr contractumMembers)
  obtain ⟨count, redex, rest, core⟩ := reacts_open_core hereObject nameObject processObject contentObject pairTyped
    contractumTyped
  have othersMembers : Members locatedCalc locatedBlock free bound (others.map (encode relabel here)) :=
    fun element member => sourceMembers element (mappedPerm.symm.subset (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ member)))
  have groupedMembers : Members locatedCalc locatedBlock free bound
      (.collection .hashBag [encode relabel here (.apply "AOpen" [name, process]),
        encode relabel here (.apply "AAmb" [name, content])] none :: others.map (encode relabel here)) := by
    intro element member
    rcases List.mem_cons.mp member with rfl | inOthers
    · exact pairTyped
    · exact othersMembers element inOthers
  have groupedTyped := signature.bag_typed (rest := none) (elementsHaveType_iff.mpr groupedMembers)
  have groupedObjects : ∀ element ∈ .collection .hashBag [encode relabel here (.apply "AOpen" [name, process]),
      encode relabel here (.apply "AAmb" [name, content])] none :: others.map (encode relabel here),
      isObjectPattern element = true := by
    intro element member
    rcases List.mem_cons.mp member with rfl | inOthers
    · simp only [isObjectPattern, Bool.and_eq_true, Option.isNone_none, true_and,
        Mettapedia.GSLT.LanguageDef.BagNormalForm.isObjectPatternList_iff, List.mem_cons, List.not_mem_nil,
        or_false]
      rintro element (rfl | rfl)
      · exact encode_object' hereObject capabilityObject
      · exact encode_object' hereObject boundaryObject
    · obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp inOthers
      exact encode_object' hereObject (objects original (List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx
        inOriginal)))
  have lifted := ReactsAt.inBag 0 (by simp) (locatedReactions.result_members redex) groupedTyped groupedObjects core
  simp only [List.eraseIdx_cons_zero] at lifted
  -- the located source is the grouped bag, and the contractum ungrouped
  have flatMembers : Members locatedCalc locatedBlock free bound
      ([] ++ [encode relabel here (.apply "AOpen" [name, process]),
        encode relabel here (.apply "AAmb" [name, content])] ++ others.map (encode relabel here)) := by
    intro element member
    exact sourceMembers element (mappedPerm.symm.subset (by simpa using member))
  have ungrouped := flatten_equivalent (pre := []) (post := others.map (encode relabel here)) flatMembers
  simp only [List.nil_append, List.cons_append] at ungrouped
  have reordered := bag_perm_equivalent (language := locatedCalc) (block := locatedRepBlock) sourceMembers
    mappedPerm
  have targetFlatMembers : Members locatedCalc locatedBlock free bound
      ([] ++ [encode relabel here process, openedForm relabel here name content] ++
        others.map (encode relabel here)) := by
    intro element member
    simp only [List.nil_append, List.cons_append, List.mem_cons] at member
    rcases member with rfl | rfl | inOthers
    · exact continuationTyped
    · exact openedTyped
    · exact othersMembers element inOthers
  have targetUngrouped := flatten_equivalent (pre := []) (post := others.map (encode relabel here))
    targetFlatMembers
  simp only [List.nil_append, List.cons_append] at targetUngrouped
  exact ⟨count, redex, _, ReactsAt.congr lifted
    (.trans _ _ _ reordered.toEquationEquiv (.symm _ _ ungrouped.toEquationEquiv))
    (.symm _ _ targetUngrouped.toEquationEquiv)⟩

end Mettapedia.Languages.ProcessCalculi.Ambient.Steps
