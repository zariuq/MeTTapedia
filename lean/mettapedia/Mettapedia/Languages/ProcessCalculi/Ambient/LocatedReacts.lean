import Mettapedia.Languages.ProcessCalculi.Ambient.EncodingOpen
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationMolecular

/-!
# Every step of an ambient process is a located reaction

A step of a typed object ambient process is, in located form, a reaction of the located calculus (`located_reacts`):
the located form of the process reacts to a located form that reads back as the step's contractum. Entering and leaving
react to the located form of the contractum itself; opening reacts to the continuation beside the opened ambient, which
reads back as the continuation beside the ambient's content; a step inside a bag, under a restriction or inside an
ambient reacts in the located form around it, which reads back around the contractum's reading.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Steps

open Mettapedia.Languages.ProcessCalculi.Ambient.Comm (ambientCoreCalc coreSignature)

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (liftIndex)
open Mettapedia.GSLT.LanguageDef.WellSorted (HasType FreeTypeContext isObjectPattern isObjectPatternList)
open Mettapedia.GSLT.LanguageDef.BagNormalForm (elementsHaveType_iff isObjectPatternList_iff)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (Prenex Members ReplicationReactions rename rename_apply
  rename_lambda rename_collection canonP canonFacts restrictionsBind_of_typed canonsP_eq_map par_nil
  normal_close_normal par_atomic
  decompose_atom isObjectPattern_rename size members_of_bag BlockSignature ReplicationStepAt bag_body_equivalent
  bag_cons_equivalent restricts_typed CanonFacts)
open Mettapedia.Languages.ProcessCalculi.Ambient.Full (AmbNuRawStep ambientBlock)
open Mettapedia.Languages.ProcessCalculi.Ambient.Located (locatedCalc locatedBlock locatedRepBlock locatedLanguage)
open Mettapedia.Languages.ProcessCalculi.Ambient.Encoding (NameContext nameType procType encode shiftName
  encode_typed encode_object encode_bag encode_amb amb_inv prefix_inv rename_name_typed name_cases_ambient
  liftIndex_inside)
open Mettapedia.Languages.ProcessCalculi.Ambient.Decoding (EncodeFacts LocVariables underLocation
  underLocation_locVariables underName underName_locVariables decode_encode encodeFacts_marker encodeFacts_close
  names_base
  encodeFacts_par encodeFacts_zero wrapContent_amb markers rename_succ_comp rename_process_typed
  canonP_located_restrict canonP_triple canonP_variable shiftName_bvar isVariable isVariable_rename forall₂_map_map
  triple_inv)

variable {free : FreeTypeContext}

/-! ## Bags of located forms read back -/

/-- **Blocks side by side read back as the bag of their readings.** -/
theorem encodeFacts_bagOf {isLoc : Pattern → Prop} {here count : Nat} (hereLoc : isLoc (.bvar here)) :
    ∀ (forms : List Prenex) (readings : List Pattern),
      List.Forall₂ (EncodeFacts free isLoc here (List.replicate count nameType)) forms readings →
      (∀ reading ∈ readings, HasType ambientCoreCalc free (List.replicate count nameType) reading procType) →
      EncodeFacts free isLoc here (List.replicate count nameType) (forms.foldr Prenex.par Prenex.nil)
        (.collection .hashBag readings none)
  | [], [], .nil, _ => (encodeFacts_zero hereLoc).congr
      (Relation.EqvGen.symm _ _ (bag_body_equivalent (language := ambientCoreCalc) (block := ambientBlock) Members.nil))
  | form :: forms, reading :: readings, .cons first rest, typed => by
      have restFacts := encodeFacts_bagOf hereLoc forms readings rest
        (fun other member => typed other (List.mem_cons_of_mem _ member))
      have restMembers : Members ambientCoreCalc ambientBlock free (List.replicate count nameType) readings :=
        fun other member => typed other (List.mem_cons_of_mem _ member)
      simp only [List.foldr_cons]
      exact (encodeFacts_par first restFacts).congr
        (bag_cons_equivalent (language := ambientCoreCalc) (block := ambientBlock) (typed reading List.mem_cons_self)
          restMembers)

/-- **A bag of located forms reads back as the bag of their readings**, its canonical block normalizing theirs. -/
theorem encodeFacts_canonBag (names : NameContext free) {isLoc : Pattern → Prop} {here count : Nat}
    (locVariables : LocVariables isLoc) (hereLoc : isLoc (.bvar here)) {located readings : List Pattern}
    (facts : List.Forall₂ (fun part reading =>
      EncodeFacts free isLoc here (List.replicate count nameType) (canonP locatedRepBlock part)
      reading) located readings)
    (typed : ∀ reading ∈ readings, HasType ambientCoreCalc free (List.replicate count nameType) reading procType) :
    EncodeFacts free isLoc here (List.replicate count nameType)
      (canonP locatedRepBlock (.collection .hashBag located none))
      (.collection .hashBag readings none) := by
  rw [Mettapedia.GSLT.LanguageDef.RestrictionBlocks.canonP_bag, canonsP_eq_map]
  exact (encodeFacts_bagOf hereLoc _ _ (List.forall₂_map_left_iff.mpr facts) typed).normal (names_base names count)
    locVariables

/-- **An opened ambient's located form is an object term** where the ambient's is. -/
theorem openedForm_object {relabel : Nat → Nat} {here name content : Pattern}
    (object : isObjectPattern (encode relabel here (.apply "AAmb" [name, content])) = true) :
    isObjectPattern (openedForm relabel here name content) = true := by
  rw [encode_amb] at object
  simpa [openedForm, isObjectPattern, isObjectPatternList] using object

/-! ## Steps in context, located -/

/-- **What the located form of a step reaches**, for a system of located reactions: from the located form of the
step's source, in a context of names and locations, a reaction to a typed object located form whose canonical block
reads back as the contractum. -/
abbrev LocatedReaches (reactions : ReplicationReactions locatedCalc locatedRepBlock LocStep) (free : FreeTypeContext)
    (source target : Pattern) : Prop :=
  ∀ {count count' : Nat} {relabel : Nat → Nat} {here : Nat} {isLoc : Pattern → Prop},
    (∀ index < count, relabel index < count') → here < count' → LocVariables isLoc → isLoc (.bvar here) →
    (∀ index < count, ¬ isLoc (.bvar (relabel index))) → (∀ name, ¬ isLoc (.fvar name)) →
    HasType ambientCoreCalc free (List.replicate count nameType) source procType → isObjectPattern source = true →
    ∃ located, HasType locatedCalc free (List.replicate count' nameType) located procType ∧
      isObjectPattern located = true ∧
      (∃ reactionCount redex rest, ReplicationStepAt reactions free (List.replicate count' nameType)
        (encode relabel (.bvar here) source) located reactionCount redex rest) ∧
      EncodeFacts free isLoc here (List.replicate count' nameType) (canonP locatedRepBlock located)
        (rename relabel target)

/-- **A step inside a bag reacts in the bag's located form**, beside the located forms of the other members. -/
theorem located_par (names : NameContext free) {reactions : ReplicationReactions locatedCalc locatedRepBlock LocStep}
    {elements : List Pattern} {tail : Option String} {i : Nat} (hi : i < elements.length) {target' : Pattern}
    (preserves : ∀ {bound : List TypeExpr}, HasType ambientCoreCalc free bound elements[i] procType →
      isObjectPattern elements[i] = true → HasType ambientCoreCalc free bound target' procType)
    (recurse : LocatedReaches reactions free elements[i] target') :
    LocatedReaches reactions free (.collection .hashBag elements tail)
      (.collection .hashBag (target' :: elements.eraseIdx i) none) := by
  intro count count' relabel here isLoc inside hereBelow locVariables hereLoc namesApart fvarsApart typed object
  obtain ⟨rfl, objects⟩ := bag_objects object
  have members := members_of_bag (language := ambientCoreCalc) (block := ambientBlock) typed
  have hereTyped : HasType locatedCalc free (List.replicate count' nameType) (.bvar here) nameType :=
    .bvar (by simp [hereBelow])
  have steppedTyped := preserves (members _ (List.getElem_mem hi)) (objects _ (List.getElem_mem hi))
  obtain ⟨located', locatedTyped', locatedObject', reached, facts'⟩ := recurse inside hereBelow locVariables
    hereLoc namesApart fvarsApart (members _ (List.getElem_mem hi)) (objects _ (List.getElem_mem hi))
  have sourceTyped := encode_typed names _ (Nat.lt_succ_self _) inside hereTyped rfl typed object
  rw [encode_bag] at sourceTyped
  have restIn : ∀ other ∈ elements.eraseIdx i, other ∈ elements := fun other member => List.mem_of_mem_eraseIdx member
  refine ⟨_, ?_, ?_, reacts_par hi sourceTyped (fun element member => by
    obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp member
    exact encode_object' rfl (objects original inOriginal)) reached, ?_⟩
  · apply (locatedLanguage.toBlockSignature).bag_typed (rest := none)
    apply elementsHaveType_iff.mpr
    intro element member
    rcases List.mem_cons.mp member with rfl | inRest
    · exact locatedTyped'
    · obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp inRest
      exact encode_typed names _ (Nat.lt_succ_self _) inside hereTyped rfl (members original (restIn original
        inOriginal)) (objects original (restIn original inOriginal))
  · simp only [isObjectPattern, Bool.and_eq_true, Option.isNone_none, true_and, isObjectPatternList_iff,
      List.mem_cons]
    rintro element (rfl | inRest)
    · exact locatedObject'
    · obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp inRest
      exact encode_object' rfl (objects original (restIn original inOriginal))
  · rw [rename_collection, List.map_cons]
    refine encodeFacts_canonBag names locVariables hereLoc (.cons facts' (forall₂_map_map fun other member =>
      decode_encode names _ (Nat.lt_succ_self _) inside hereBelow locVariables hereLoc namesApart fvarsApart
        (members other (restIn other member)) (objects other (restIn other member)))) ?_
    intro reading member
    rcases List.mem_cons.mp member with rfl | inRest
    · exact rename_process_typed inside steppedTyped
    · obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp inRest
      exact rename_process_typed inside (members original (restIn original inOriginal))

/-- **A step under a restriction reacts under the restriction**, in the located form. -/
theorem located_res (names : NameContext free) {reactions : ReplicationReactions locatedCalc locatedRepBlock LocStep}
    {binder : Option String} {source' target' : Pattern} (recurse : LocatedReaches reactions free source' target') :
    LocatedReaches reactions free (.apply "ANu" [.lambda binder source']) (.apply "ANu" [.lambda none target']) := by
  intro count count' relabel here isLoc inside hereBelow locVariables hereLoc namesApart fvarsApart typed object
  have signature : BlockSignature locatedCalc locatedBlock := locatedLanguage.toBlockSignature
  obtain ⟨bodyTyped, -, rfl⟩ := coreSignature.restriction_typed typed
  have bodyObject : isObjectPattern source' = true := by
    simpa [isObjectPattern, isObjectPatternList] using object
  obtain ⟨located', locatedTyped', locatedObject', ⟨reactionCount, redex, rest, reached⟩, facts'⟩ :=
    recurse (count := count + 1) (count' := count' + 1) (relabel := liftIndex 1 relabel) (here := here + 1)
      (isLoc := underName isLoc) (liftIndex_inside inside) (by omega) (underName_locVariables isLoc)
      (by simpa [underName] using hereLoc)
      (fun index below => by
        cases index with
        | zero => simp [liftIndex, underName]
        | succ index =>
            simp only [liftIndex, show ¬ index + 1 < 1 by omega, if_false, Nat.add_sub_cancel, underName]
            exact namesApart index (by omega))
      (fun name => by simpa [underName] using fvarsApart name)
      (by simpa [List.replicate_succ] using bodyTyped) bodyObject
  refine ⟨.apply "LNu" [.lambda none located'],
    restricts_typed (language := locatedCalc) (block := locatedBlock) 1 locatedTyped',
    by simpa [isObjectPattern, isObjectPatternList] using locatedObject',
    reacts_res ⟨reactionCount, redex, rest, by rw [shiftName_bvar]; exact reached⟩, ?_⟩
  rw [canonP_located_restrict, rename_apply, List.map_cons, List.map_nil, rename_lambda]
  exact (encodeFacts_close facts').normal (names_base names count') locVariables

/-- **A step inside an ambient reacts at the ambient's location**, beside the ambient's marker, in the located form. -/
theorem located_ambient (names : NameContext free)
    {reactions : ReplicationReactions locatedCalc locatedRepBlock LocStep} (name : Pattern) {content target' : Pattern}
    (preserves : ∀ {bound : List TypeExpr}, HasType ambientCoreCalc free bound content procType →
      isObjectPattern content = true → HasType ambientCoreCalc free bound target' procType)
    (recurse : LocatedReaches reactions free content target') :
    LocatedReaches reactions free (Mettapedia.Languages.ProcessCalculi.Ambient.Mobile.amb name content)
      (Mettapedia.Languages.ProcessCalculi.Ambient.Mobile.amb name target') := by
  intro count count' relabel here isLoc inside hereBelow locVariables hereLoc namesApart fvarsApart typed object
  have signature : BlockSignature locatedCalc locatedBlock := locatedLanguage.toBlockSignature
  have fresh : locatedRepBlock.replicate ∉ locatedRepBlock.emptyUnits := by decide
  have restrictFresh : locatedRepBlock.replicate ≠ locatedRepBlock.restrict := by decide
  obtain ⟨nameTyped, contentTyped⟩ := amb_inv typed
  obtain ⟨nameObject, contentObject⟩ := pair_objects object
  have steppedTyped := preserves contentTyped contentObject
  have hereTyped : HasType locatedCalc free (List.replicate count' nameType) (.bvar here) nameType :=
    .bvar (by simp [hereBelow])
  -- the name, renamed, is a variable apart from the locations
  obtain ⟨nameVar, nameApart⟩ : isVariable (rename relabel name) = true ∧
      ¬ underLocation isLoc (liftBVars 0 1 (rename relabel name)) := by
    rcases name_cases_ambient nameTyped rfl nameObject with ⟨index, rfl, found⟩ | ⟨name, rfl, found⟩
    · have below : index < count := by
        have := List.getElem?_eq_some_iff.mp found
        simpa using this.1
      exact ⟨rfl, by simpa [Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_bvar, liftBVars,
        underLocation] using namesApart index below⟩
    · exact ⟨rfl, fvarsApart name⟩
  have shifted : ∀ index < count, (Nat.succ ∘ relabel) index < count' + 1 := fun index below => by
    have := inside index below
    simp only [Function.comp]
    omega
  obtain ⟨located', locatedTyped', locatedObject', reached, facts'⟩ :=
    recurse (count' := count' + 1) (relabel := Nat.succ ∘ relabel) (here := 0) (isLoc := underLocation isLoc)
      shifted (by omega) (underLocation_locVariables isLoc) (by simp [underLocation])
      (fun index below => by simpa [underLocation, Function.comp] using namesApart index below)
      (fun name => by simpa [underLocation] using fvarsApart name) contentTyped contentObject
  rw [rename_succ_comp] at facts'
  -- the ambient's located form: its marker beside its content's
  have ambientTyped := encode_typed names _ (Nat.lt_succ_self _) inside hereTyped rfl typed object
  rw [show Mettapedia.Languages.ProcessCalculi.Ambient.Mobile.amb name content = .apply "AAmb" [name, content]
    from rfl, encode_amb] at ambientTyped
  obtain ⟨ambientBody, -, -⟩ := (locatedLanguage.toBlockSignature).restriction_typed ambientTyped
  have ambientMembers := members_of_bag (language := locatedCalc) (block := locatedBlock) ambientBody
  have markerTyped := ambientMembers (.apply "LAmb" [shiftName (.bvar here), .bvar 0,
    rename (Nat.succ ∘ relabel) name]) (by simp)
  have contentLocatedTyped := ambientMembers (encode (Nat.succ ∘ relabel) (.bvar 0) content) (by simp)
  have renamedObject : isObjectPattern (rename (Nat.succ ∘ relabel) name) = true := by
    rw [isObjectPattern_rename]
    exact nameObject
  have renamedVar : isVariable (rename (Nat.succ ∘ relabel) name) = true := by
    rw [isVariable_rename, ← isVariable_rename relabel name]
    exact nameVar
  have markerObject : isObjectPattern (.apply "LAmb" [shiftName (.bvar here), .bvar 0,
      rename (Nat.succ ∘ relabel) name]) = true := by
    simp [isObjectPattern, isObjectPatternList, shiftName_bvar, renamedObject]
  have bagTyped : HasType locatedCalc free (nameType :: List.replicate count' nameType) (.collection .hashBag
      [.apply "LAmb" [shiftName (.bvar here), .bvar 0, rename (Nat.succ ∘ relabel) name], located'] none)
      procType := by
    apply (locatedLanguage.toBlockSignature).bag_typed (rest := none)
    apply elementsHaveType_iff.mpr
    intro element member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact markerTyped
    · exact locatedTyped'
  refine ⟨.apply "LNu" [.lambda none (.collection .hashBag [.apply "LAmb" [shiftName (.bvar here), .bvar 0,
      rename (Nat.succ ∘ relabel) name], located'] none)],
    restricts_typed (language := locatedCalc) (block := locatedBlock) 1 bagTyped,
    by simpa [isObjectPattern, isObjectPatternList, shiftName_bvar, renamedObject] using locatedObject',
    reacts_ambient markerTyped markerObject contentLocatedTyped (encode_object' rfl contentObject) locatedTyped'
      reached, ?_⟩
  -- read back: the ambient around the contractum's reading
  have contentFacts : CanonFacts locatedRepBlock located' :=
    canonFacts fresh restrictFresh locatedObject' (restrictionsBind_of_typed (block := locatedRepBlock) _
      locatedTyped')
  have markerCanon : canonP locatedRepBlock
      (.apply "LAmb" [shiftName (.bvar here), .bvar 0, rename (Nat.succ ∘ relabel) name]) =
      Prenex.atom (.apply "LAmb" [shiftName (.bvar here), .bvar 0, liftBVars 0 1 (rename relabel name)]) := by
    rw [shiftName_bvar, canonP_triple (by decide) rfl rfl renamedObject, canonP_variable renamedVar,
      rename_succ_comp]
    rfl
  have markerAtomic : (Prenex.atom (.apply "LAmb" [shiftName (.bvar here), .bvar 0,
      liftBVars 0 1 (rename relabel name)])).Atomic locatedRepBlock.toBlock := by
    intro component member
    simp only [Prenex.atom, List.mem_singleton] at member
    subst member
    rw [shiftName_bvar]
    exact decompose_atom (by simp) (by simp) (by simp) (by simp)
  show EncodeFacts free isLoc here (List.replicate count' nameType) (canonP locatedRepBlock (.apply "LNu" [.lambda none
    (.collection .hashBag [.apply "LAmb" [shiftName (.bvar here), .bvar 0, rename (Nat.succ ∘ relabel) name],
      located'] none)])) (rename relabel (.apply "AAmb" [name, target']))
  rw [canonP_located_restrict, Mettapedia.GSLT.LanguageDef.RestrictionBlocks.canonP_bag, canonsP_eq_map,
    List.map_cons, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_cons, List.foldr_nil, par_nil,
    markerCanon, normal_close_normal fresh restrictFresh (par_atomic markerAtomic contentFacts.atomic),
    rename_apply, List.map_cons, List.map_cons, List.map_nil]
  have ambientFacts := encodeFacts_marker (show "LAmb" ∈ markers by simp [markers]) hereLoc (by simp [hereBelow])
    nameVar
    nameApart (rename_name_typed inside nameTyped nameObject) (rename_process_typed inside steppedTyped) facts'
  rw [wrapContent_amb] at ambientFacts
  exact ambientFacts.normal (names_base names count') locVariables

/-! ## The located form of a step -/

/-- **Every step of a typed object ambient process is a reaction of its located form**, to a typed object located form
whose canonical block reads back, wherever the process's does, as the contractum. -/
theorem located_reacts (names : NameContext free) {source target : Pattern} (step : AmbNuRawStep source target) :
    ∀ {count count' : Nat} {relabel : Nat → Nat} {here : Nat} {isLoc : Pattern → Prop},
      (∀ index < count, relabel index < count') → here < count' → LocVariables isLoc → isLoc (.bvar here) →
      (∀ index < count, ¬ isLoc (.bvar (relabel index))) → (∀ name, ¬ isLoc (.fvar name)) →
      HasType ambientCoreCalc free (List.replicate count nameType) source procType → isObjectPattern source = true →
      ∃ located, HasType locatedCalc free (List.replicate count' nameType) located procType ∧
        isObjectPattern located = true ∧
        (∃ reactionCount redex rest, ReplicationStepAt locatedReactions free (List.replicate count' nameType)
          (encode relabel (.bvar here) source) located reactionCount redex rest) ∧
        EncodeFacts free isLoc here (List.replicate count' nameType) (canonP locatedRepBlock located)
          (rename relabel target) := by
  induction step with
  | @«open» elements tail i hi j hj name process content capability boundary =>
      intro count count' relabel here isLoc inside hereBelow locVariables hereLoc namesApart fvarsApart typed object
      obtain ⟨rfl, objects⟩ := bag_objects object
      have hereTyped : HasType locatedCalc free (List.replicate count' nameType) (.bvar here) nameType :=
        .bvar (by simp [hereBelow])
      have members := members_of_bag (language := ambientCoreCalc) (block := ambientBlock) typed
      have capabilityTyped := members _ (List.getElem_mem hi)
      have capabilityObject := objects _ (List.getElem_mem hi)
      rw [capability] at capabilityTyped capabilityObject
      have boundaryTyped := members _ (List.mem_of_mem_eraseIdx (List.getElem_mem hj))
      have boundaryObject := objects _ (List.mem_of_mem_eraseIdx (List.getElem_mem hj))
      rw [boundary] at boundaryTyped boundaryObject
      obtain ⟨-, processTyped⟩ := prefix_inv (by simp) capabilityTyped
      obtain ⟨nameTyped, contentTyped⟩ := amb_inv boundaryTyped
      obtain ⟨nameObject, processObject⟩ := pair_objects capabilityObject
      obtain ⟨-, contentObject⟩ := pair_objects boundaryObject
      have encodedTyped : ∀ {part : Pattern},
          HasType ambientCoreCalc free (List.replicate count nameType) part procType → isObjectPattern part = true →
          HasType locatedCalc free (List.replicate count' nameType) (encode relabel (.bvar here) part) procType :=
        fun partTyped partObject => encode_typed names _ (Nat.lt_succ_self _) inside hereTyped rfl partTyped partObject
      have encodedFacts : ∀ {part : Pattern},
          HasType ambientCoreCalc free (List.replicate count nameType) part procType → isObjectPattern part = true →
          EncodeFacts free isLoc here (List.replicate count' nameType)
            (canonP locatedRepBlock (encode relabel (.bvar here) part))
            (rename relabel part) :=
        fun partTyped partObject => decode_encode names _ (Nat.lt_succ_self _) inside hereBelow locVariables hereLoc
          namesApart fvarsApart partTyped partObject
      have ambientTyped := encodedTyped boundaryTyped boundaryObject
      have othersIn : ∀ other ∈ (elements.eraseIdx i).eraseIdx j, other ∈ elements :=
        fun other member => List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx member)
      refine ⟨_, ?_, ?_, reacts_open hi hj capability boundary rfl objects (encodedTyped typed object), ?_⟩
      · apply (locatedLanguage.toBlockSignature).bag_typed (rest := none)
        apply elementsHaveType_iff.mpr
        intro element member
        simp only [List.mem_cons] at member
        rcases member with rfl | rfl | inOthers
        · exact encodedTyped processTyped processObject
        · exact openedForm_typed ambientTyped
        · obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp inOthers
          exact encodedTyped (members original (othersIn original inOriginal))
            (objects original (othersIn original inOriginal))
      · simp only [isObjectPattern, Bool.and_eq_true, Option.isNone_none, true_and, isObjectPatternList_iff,
          List.mem_cons]
        rintro element (rfl | rfl | inOthers)
        · exact encode_object' rfl processObject
        · exact openedForm_object (encode_object' rfl boundaryObject)
        · obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp inOthers
          exact encode_object' rfl (objects original (othersIn original inOriginal))
      · rw [rename_collection, List.map_cons, List.map_cons]
        refine encodeFacts_canonBag names locVariables hereLoc (.cons (encodedFacts processTyped processObject)
          (.cons (decode_opened names inside hereBelow locVariables hereLoc namesApart fvarsApart nameTyped nameObject
            contentTyped contentObject) (forall₂_map_map fun other member =>
              encodedFacts (members other (othersIn other member)) (objects other (othersIn other member))))) ?_
        intro reading member
        simp only [List.mem_cons] at member
        rcases member with rfl | rfl | inOthers
        · exact rename_process_typed inside processTyped
        · exact rename_process_typed inside contentTyped
        · obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp inOthers
          exact rename_process_typed inside (members original (othersIn original inOriginal))
  | @enter elements tail i hi j hj name target' process host inner innerTail k hk mover capability destination =>
      intro count count' relabel here isLoc inside hereBelow locVariables hereLoc namesApart fvarsApart typed object
      obtain ⟨rfl, objects⟩ := bag_objects object
      have moverObject := objects _ (List.getElem_mem hi)
      rw [mover] at moverObject
      obtain ⟨-, innerBagObject⟩ := pair_objects moverObject
      obtain ⟨rfl, -⟩ := bag_objects innerBagObject
      obtain ⟨contractumTyped, contractumObject⟩ :=
        step_typed (AmbNuRawStep.enter (tail := none) i hi j hj name target' process host k hk mover capability
          destination) typed object
      have hereTyped : HasType locatedCalc free (List.replicate count' nameType) (.bvar here) nameType :=
        .bvar (by simp [hereBelow])
      have locatedTyped := encode_typed names _ (Nat.lt_succ_self _) inside hereTyped rfl contractumTyped
        contractumObject
      exact ⟨_, locatedTyped, encode_object' rfl contractumObject,
        reacts_enter hi hj hk mover capability destination rfl objects
          (encode_typed names _ (Nat.lt_succ_self _) inside hereTyped rfl typed object) locatedTyped,
        decode_encode names _ (Nat.lt_succ_self _) inside hereBelow locVariables hereLoc namesApart fvarsApart
          contractumTyped contractumObject⟩
  | @exit contents tail i hi name parent process inner innerTail k hk mover capability =>
      intro count count' relabel here isLoc inside hereBelow locVariables hereLoc namesApart fvarsApart typed object
      obtain ⟨-, contentsObject⟩ := pair_objects object
      obtain ⟨rfl, objects⟩ := bag_objects contentsObject
      have moverObject := objects _ (List.getElem_mem hi)
      rw [mover] at moverObject
      obtain ⟨-, innerBagObject⟩ := pair_objects moverObject
      obtain ⟨rfl, -⟩ := bag_objects innerBagObject
      obtain ⟨contractumTyped, contractumObject⟩ :=
        step_typed (AmbNuRawStep.exit (tail := none) i hi name parent process k hk mover capability) typed object
      have hereTyped : HasType locatedCalc free (List.replicate count' nameType) (.bvar here) nameType :=
        .bvar (by simp [hereBelow])
      have locatedTyped := encode_typed names _ (Nat.lt_succ_self _) inside hereTyped rfl contractumTyped
        contractumObject
      exact ⟨_, locatedTyped, encode_object' rfl contractumObject,
        reacts_exit hi mover hk capability rfl object
          (encode_typed names _ (Nat.lt_succ_self _) inside hereTyped rfl typed object) locatedTyped,
        decode_encode names _ (Nat.lt_succ_self _) inside hereBelow locVariables hereLoc namesApart fvarsApart
          contractumTyped contractumObject⟩
  | @par elements tail i hi target' inner recurse =>
      exact located_par names hi (fun typed object => (step_typed inner typed object).1) recurse
  | @res binder source' target' inner recurse => exact located_res names recurse
  | @ambient name content target' inner recurse =>
      exact located_ambient names name (fun typed object => (step_typed inner typed object).1) recurse


/-! ## At the root -/

open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (engineBasePremises)
open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationEquiv)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (BaseContext UnfoldsWithin presentationDepth isReplicated
  replication_reaction compress_molecular moleculeServers_spec canonP_sound_all)
open Mettapedia.Languages.ProcessCalculi.Ambient.Decoding (rootForm root_locVariables)

/-- **A located reaction of a closed object process is a reaction of an unfolding of its root canonical block**, for
any system of located reactions, within the presentation depth (three unfoldings when the replicated components copy
molecules, three times the block's ceiling otherwise): the reaction's parts beside the unfolding's other components,
leaving, under the unfolding's restrictions, a located form whose canonical block reads back at the root as the
contractum. -/
theorem root_reaction_of {reactions : ReplicationReactions locatedCalc locatedRepBlock LocStep}
    (arity : reactions.arity = 3) (names : NameContext free) (context : BaseContext free [nameType]) {source target : Pattern}
    (reaches : LocatedReaches reactions free source target) (typed : HasType ambientCoreCalc free [] source procType)
    (object : isObjectPattern source = true) :
    ∃ unfolded, UnfoldsWithin locatedRepBlock (presentationDepth locatedRepBlock 3 (rootForm source))
        (rootForm source) unfolded ∧
      ∃ (redex : reactions.Redex) (rest : List Pattern), unfolded.components.Perm (reactions.parts redex ++ rest) ∧
        (∀ part ∈ reactions.parts redex, isReplicated locatedRepBlock part = false) ∧
        Members locatedCalc locatedBlock free (List.replicate unfolded.count nameType ++ [nameType])
          unfolded.components ∧
        (∀ component ∈ unfolded.components, isObjectPattern component = true) ∧
        ∃ located, HasType locatedCalc free [nameType] located procType ∧ isObjectPattern located = true ∧
          EquationEquiv (engineBasePremises RelationEnv.empty) locatedCalc
            (Prenex.restricts locatedBlock unfolded.count
              (.collection .hashBag (reactions.result redex ++ rest) none))
            located ∧
          EncodeFacts free (· = .bvar 0) 0 [nameType] (canonP locatedRepBlock located) (rename Nat.succ target) := by
  have hereTyped : HasType locatedCalc free (List.replicate 1 nameType) (.bvar 0) nameType := .bvar (by simp)
  obtain ⟨located, locatedTyped, locatedObject, ⟨reactionCount, redex, rest, reached⟩, facts⟩ :=
    reaches (count := 0) (count' := 1) (relabel := Nat.succ) (here := 0)
      (isLoc := (· = .bvar 0)) (fun _ below => absurd below (Nat.not_lt_zero _)) (by omega) root_locVariables rfl
      (fun _ below => absurd below (Nat.not_lt_zero _)) (fun _ same => by cases same) typed object
  have sourceTyped := encode_typed names _ (Nat.lt_succ_self _) (relabel := Nat.succ)
    (fun _ below => absurd below (Nat.not_lt_zero _)) hereTyped rfl typed object
  obtain ⟨unfolded, unfolds, redex', rest', split, plain, members, objects, reaches⟩ :=
    replication_reaction reactions context reached sourceTyped (encode_object' rfl object)
  rw [arity] at unfolds
  -- within the arity when the replicated components copy molecules: the copies the redex does not take are dropped
  unfold presentationDepth
  split_ifs with molecular
  · obtain ⟨compressed, compressedWithin, redexC, restC, splitC, plainC, membersC, objectsC, compressedReads⟩ :=
      compress_molecular reactions context (moleculeServers_spec molecular)
        ((canonP_sound_all _).1.members context sourceTyped) unfolds split plain members objects
    rw [arity] at compressedWithin
    exact ⟨compressed, compressedWithin, redexC, restC, splitC, plainC, membersC, objectsC, located, locatedTyped,
      locatedObject, Relation.EqvGen.trans _ _ _ compressedReads reaches, facts⟩
  · exact ⟨unfolded, unfolds, redex', rest', split, plain, members, objects, located, locatedTyped, locatedObject,
      reaches, facts⟩

/-- **A step of a closed object process is a reaction of an unfolding of its root canonical block**: a marker
reaction, its parts beside the unfolding's other components, leaving, under the unfolding's restrictions, a located
form whose canonical block reads back at the root as the contractum. -/
theorem root_reaction (names : NameContext free) (context : BaseContext free [nameType]) {source target : Pattern}
    (step : AmbNuRawStep source target) (typed : HasType ambientCoreCalc free [] source procType)
    (object : isObjectPattern source = true) :
    ∃ unfolded, UnfoldsWithin locatedRepBlock (presentationDepth locatedRepBlock 3 (rootForm source))
        (rootForm source) unfolded ∧
      ∃ (redex : LocRedex) (rest : List Pattern), unfolded.components.Perm (redex.parts ++ rest) ∧
        (∀ part ∈ redex.parts, isReplicated locatedRepBlock part = false) ∧
        Members locatedCalc locatedBlock free (List.replicate unfolded.count nameType ++ [nameType])
          unfolded.components ∧
        (∀ component ∈ unfolded.components, isObjectPattern component = true) ∧
        ∃ located, HasType locatedCalc free [nameType] located procType ∧ isObjectPattern located = true ∧
          EquationEquiv (engineBasePremises RelationEnv.empty) locatedCalc
            (Prenex.restricts locatedBlock unfolded.count (.collection .hashBag (redex.result ++ rest) none))
            located ∧
          EncodeFacts free (· = .bvar 0) 0 [nameType] (canonP locatedRepBlock located) (rename Nat.succ target) :=
  root_reaction_of (reactions := locatedReactions) rfl names context (located_reacts names step) typed object

end Mettapedia.Languages.ProcessCalculi.Ambient.Steps
