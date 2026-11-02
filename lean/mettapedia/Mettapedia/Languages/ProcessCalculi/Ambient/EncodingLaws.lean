import Mettapedia.Languages.ProcessCalculi.Ambient.EncodingRename

/-!
# The located forms of the two sides of an ambient law agree

Every law of the ambient calculus relates two processes whose located forms the restriction-block theory relates
(`encode_shape`): the laws of the bag, of restriction and of replication are the located calculus's own laws, read at
the same location; the boundary law becomes scope extrusion and exchange of the restriction with the ambient's
location.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Encoding

open Mettapedia.Languages.ProcessCalculi.Ambient.Comm (ambientCoreCalc coreSignature commTerms capRule capType)

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (liftIndex)
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (rename size sizeList Members ProcEquiv SortedEquiv swapInner
  members_of_bag rename_bvar rename_apply rename_comp liftBVars_eq_rename shiftAbove)
open Mettapedia.GSLT.LanguageDef.BagNormalForm (elementsHaveType_iff isObjectPatternList_iff)
open Mettapedia.Languages.ProcessCalculi.Ambient.Full (terms prefixRule ambientRepBlock ambientBlock AmbShape)
open Mettapedia.Languages.ProcessCalculi.Ambient.Located (locatedCalc locatedRepBlock locatedBlock locatedLanguage
  capabilityRule)

/-! ## Typed ambient processes, inverted -/

/-- A typed restriction binds a name over a typed process, with no binder name. -/
theorem nu_inv {free : FreeTypeContext} {bound : List TypeExpr} {binder : Option String} {body : Pattern}
    (typed : HasType ambientCoreCalc free bound (.apply "ANu" [.lambda binder body]) procType) :
    binder = none ∧ HasType ambientCoreCalc free (nameType :: bound) body procType := by
  obtain ⟨rule, member, labelIs, -, -, arguments⟩ := hasType_apply_inversion typed
  simp only [ambientCoreCalc, terms, commTerms, prefixRule, capRule, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;> simp at labelIs
  cases arguments with
  | cons representation parameterType argumentTyped rest =>
      obtain ⟨_, same⟩ := (matchesParameterRepresentation_abstractionNamed_iff _ _ _ _).mp representation
      cases same
      simp only [parameterType?, Option.some.injEq] at parameterType
      subst parameterType
      cases argumentTyped with
      | lambda bodyTyped => exact ⟨rfl, bodyTyped⟩

/-- A typed replication replicates a typed process. -/
theorem rep_inv {free : FreeTypeContext} {bound : List TypeExpr} {process : Pattern}
    (typed : HasType ambientCoreCalc free bound (.apply "ARep" [process]) procType) :
    HasType ambientCoreCalc free bound process procType := by
  obtain ⟨rule, member, labelIs, -, -, arguments⟩ := hasType_apply_inversion typed
  simp only [ambientCoreCalc, terms, commTerms, prefixRule, capRule, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;> simp at labelIs
  cases arguments with
  | cons _ parameterType argumentTyped _ =>
      simp only [parameterType?, Option.some.injEq] at parameterType
      subst parameterType
      exact argumentTyped

/-- A typed ambient names its content with a name. -/
theorem amb_inv {free : FreeTypeContext} {bound : List TypeExpr} {name content : Pattern}
    (typed : HasType ambientCoreCalc free bound (.apply "AAmb" [name, content]) procType) :
    HasType ambientCoreCalc free bound name nameType ∧ HasType ambientCoreCalc free bound content procType := by
  obtain ⟨rule, member, labelIs, -, -, arguments⟩ := hasType_apply_inversion typed
  simp only [ambientCoreCalc, terms, commTerms, prefixRule, capRule, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;> simp at labelIs
  cases arguments with
  | cons _ nameParameter nameTyped rest =>
      cases rest with
      | cons _ contentParameter contentTyped _ =>
          simp only [parameterType?, Option.some.injEq] at nameParameter contentParameter
          subst nameParameter contentParameter
          exact ⟨nameTyped, contentTyped⟩

/-- The members of a typed bag of ambient processes are typed. -/
theorem bag_inv {free : FreeTypeContext} {bound : List TypeExpr} {elements : List Pattern} {rest : Option String}
    (typed : HasType ambientCoreCalc free bound (.collection .hashBag elements rest) procType) :
    Members ambientCoreCalc ambientBlock free bound elements :=
  members_of_bag (language := ambientCoreCalc) (block := ambientBlock) typed

/-- A typed prefix by a capability term prefixes a typed process with a capability. -/
theorem acap_inv {free : FreeTypeContext} {bound : List TypeExpr} {capability process : Pattern}
    (typed : HasType ambientCoreCalc free bound (.apply "ACap" [capability, process]) procType) :
    HasType ambientCoreCalc free bound capability capType ∧ HasType ambientCoreCalc free bound process procType := by
  obtain ⟨rule, member, labelIs, -, -, arguments⟩ := hasType_apply_inversion typed
  simp only [ambientCoreCalc, terms, commTerms, prefixRule, capRule, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;> simp at labelIs
  cases arguments with
  | cons _ capabilityParameter capabilityTyped rest =>
      cases rest with
      | cons _ processParameter processTyped _ =>
          simp only [parameterType?, Option.some.injEq] at capabilityParameter processParameter
          subst capabilityParameter processParameter
          exact ⟨capabilityTyped, processTyped⟩

/-- A typed input binds a variable of its sort over a typed process, with no binder name. -/
theorem input_inv {free : FreeTypeContext} {bound : List TypeExpr} {label sort : String} {binder : Option String}
    {body : Pattern} (listed : (label, sort) ∈ [("AInName", "Name"), ("AInCap", "Cap")])
    (typed : HasType ambientCoreCalc free bound (.apply label [.lambda binder body]) procType) :
    binder = none ∧ HasType ambientCoreCalc free (.base sort :: bound) body procType := by
  obtain ⟨rule, member, labelIs, -, -, arguments⟩ := hasType_apply_inversion typed
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at listed
  simp only [ambientCoreCalc, terms, commTerms, prefixRule, capRule, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases listed with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;> simp at labelIs
  all_goals
    cases arguments with
    | cons representation parameterType argumentTyped rest =>
        obtain ⟨_, same⟩ := (matchesParameterRepresentation_abstractionNamed_iff _ _ _ _).mp representation
        cases same
        simp only [parameterType?, Option.some.injEq] at parameterType
        subst parameterType
        cases argumentTyped with
        | lambda bodyTyped => exact ⟨rfl, bodyTyped⟩

/-- A typed output sends a message of its sort. -/
theorem output_inv {free : FreeTypeContext} {bound : List TypeExpr} {label sort : String} {message : Pattern}
    (listed : (label, sort) ∈ [("AOutName", "Name"), ("AOutCap", "Cap")])
    (typed : HasType ambientCoreCalc free bound (.apply label [message]) procType) :
    HasType ambientCoreCalc free bound message (.base sort) := by
  obtain ⟨rule, member, labelIs, -, -, arguments⟩ := hasType_apply_inversion typed
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at listed
  simp only [ambientCoreCalc, terms, commTerms, prefixRule, capRule, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases listed with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;> simp at labelIs
  all_goals
    cases arguments with
    | cons _ parameterType messageTyped _ =>
        simp only [parameterType?, Option.some.injEq] at parameterType
        subst parameterType
        exact messageTyped

/-! ## Renamings past binders -/

theorem shiftAbove_zero_one : shiftAbove 0 1 = Nat.succ := by
  funext index
  simp [shiftAbove]

/-- Exchanging the two innermost binders commutes with a renaming lifted past both. -/
theorem swapInner_liftIndex_two (relabel : Nat → Nat) :
    swapInner ∘ liftIndex 1 (liftIndex 1 relabel) = liftIndex 1 (liftIndex 1 relabel) ∘ swapInner := by
  funext index
  rcases index with _ | _ | index <;> simp [swapInner, liftIndex]

/-- Exchanging the two innermost binders leaves a name lifted past both. -/
theorem rename_swapInner_shift_shift (here : Pattern) :
    rename swapInner (shiftName (shiftName here)) = shiftName (shiftName here) := by
  simp only [shiftName, rename_comp]
  congr 1

/-- **Lifting past one binder commutes with the located form**, read under the binder. -/
theorem encode_liftBVars (relabel : Nat → Nat) (here pattern : Pattern) :
    encode (liftIndex 1 relabel) (shiftName here) (liftBVars 0 1 pattern) =
      liftBVars 0 1 (encode relabel here pattern) := by
  rw [liftBVars_eq_rename, liftBVars_eq_rename, shiftAbove_zero_one,
    encode_rename (size pattern + 1) (Nat.lt_succ_self _), liftIndex_one_succ,
    rename_encode (size pattern + 1) (Nat.lt_succ_self _)]
  rfl

/-! ## The located form of typed processes, without fuel -/

section Located

variable {free : FreeTypeContext} (names : NameContext free) {bound bound' : List TypeExpr} {relabel : Nat → Nat}
  {here : Pattern} (frame : LocatedFrame bound bound' relabel)
  (hereTyped : HasType locatedCalc free bound' here nameType)
  (hereObject : isObjectPattern here = true)

include names frame hereTyped hereObject

/-- **A typed ambient process reads as a typed located process.** -/
theorem located_typed {process : Pattern}
    (typed : HasType ambientCoreCalc free (bound) process procType)
    (object : isObjectPattern process = true) :
    HasType locatedCalc free (bound') (encode relabel here process) procType :=
  encode_typed_frame names frame hereTyped hereObject typed object

/-- **Typed members read as typed located members.** -/
theorem located_members {elements : List Pattern}
    (typed : Members ambientCoreCalc ambientBlock free (bound) elements)
    (objects : ∀ element ∈ elements, isObjectPattern element = true) :
    Members locatedCalc locatedBlock free (bound') (elements.map (encode relabel here)) := by
  intro element member
  obtain ⟨original, inElements, rfl⟩ := List.mem_map.mp member
  exact located_typed names frame hereTyped hereObject (typed original inElements) (objects original inElements)

open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (LawShape bag_perm_equivalent extrusion_equivalent exchange_equivalent
  restriction_nil_equivalent unfold_equivalent replicate_nil_equivalent replicate_twice_equivalent
  replicate_par_equivalent replicate_idempotent_equivalent replicate_fill restrict_fill replicate_typed
  perm_getElem_eraseIdx BlockSignature)

omit names frame hereTyped hereObject in
/-- An object collection has no tail. -/
theorem tail_none {kind : CollType} {elements : List Pattern} {tail : Option String}
    (object : isObjectPattern (.collection kind elements tail) = true) : tail = none := by
  simp only [isObjectPattern, Bool.and_eq_true, Option.isNone_iff_eq_none] at object
  exact object.1

/-- **The located forms of the two sides of a law of the bag, of restriction or of replication agree.** -/
theorem encode_lawShape {source target : Pattern} (shape : LawShape ambientRepBlock source target)
    (sourceTyped : HasType ambientCoreCalc free (bound) source procType)
    (targetTyped : HasType ambientCoreCalc free (bound) target procType)
    (sourceObject : isObjectPattern source = true) (targetObject : isObjectPattern target = true) :
    ProcEquiv locatedCalc locatedBlock free (bound') (encode relabel here source)
      (encode relabel here target) := by
  have located := fun {process : Pattern} (typed : HasType ambientCoreCalc free (bound) process
    procType) (object : isObjectPattern process = true) => located_typed names frame hereTyped hereObject typed object
  have signature : BlockSignature locatedCalc locatedBlock := locatedLanguage.toBlockSignature
  have notLambda : ∀ {process : Pattern}, HasType ambientCoreCalc free (bound) process procType →
      ∀ binder body, process ≠ .lambda binder body := fun typed binder body same => by subst same; cases typed
  cases shape
  case restrictionNil binder =>
      obtain ⟨rfl, -⟩ := nu_inv sourceTyped
      rw [encode_nu, encode_zero, encode_zero]
      exact restriction_nil_equivalent (language := locatedCalc) (block := locatedBlock)
  case exchange outerBinder innerBinder body =>
      obtain ⟨rfl, innerTyped⟩ := nu_inv sourceTyped
      obtain ⟨rfl, bodyTyped⟩ := nu_inv innerTyped
      have bodyObject : isObjectPattern body = true := by
        simpa [isObjectPattern, isObjectPatternList] using sourceObject
      have twoInside := (frame.lift (sort := nameType) (.inl rfl)).lift (sort := nameType) (.inl rfl)
      have hereTwo : HasType locatedCalc free (nameType :: nameType :: bound') (shiftName (shiftName here))
          nameType := shiftName_sorted nameType (shiftName_sorted nameType hereTyped)
      have hereTwoObject : isObjectPattern (shiftName (shiftName here)) = true := by
        simp only [shiftName, Mettapedia.GSLT.LanguageDef.RestrictionBlocks.isObjectPattern_rename]
        exact hereObject
      have innerTyped' := located_typed names twoInside hereTwo hereTwoObject
        (by simpa [List.replicate_succ] using bodyTyped) bodyObject
      have swapped : encode (liftIndex 1 (liftIndex 1 relabel)) (shiftName (shiftName here)) (rename swapInner body) =
          rename swapInner (encode (liftIndex 1 (liftIndex 1 relabel)) (shiftName (shiftName here)) body) := by
        rw [encode_rename (size body + 1) (Nat.lt_succ_self _), rename_encode (size body + 1) (Nat.lt_succ_self _),
          swapInner_liftIndex_two, rename_swapInner_shift_shift]
      rw [encode_nu, encode_nu, encode_nu, encode_nu, swapped]
      exact exchange_equivalent (language := locatedCalc) (block := locatedBlock)
        (by simpa [List.replicate_succ] using innerTyped')
  case extrusion members selected inside' binder body chosen =>
      have members' := bag_inv sourceTyped
      have objects : ∀ element ∈ members, isObjectPattern element = true := by
        simpa [isObjectPattern, isObjectPatternList_iff] using sourceObject
      have chosenTyped := members' _ (List.getElem_mem inside')
      rw [chosen] at chosenTyped
      obtain ⟨rfl, bodyTyped⟩ := nu_inv chosenTyped
      have bodyObject : isObjectPattern body = true := by
        have := objects _ (List.getElem_mem inside')
        rw [chosen] at this
        simpa [isObjectPattern, isObjectPatternList] using this
      have others' : Members ambientCoreCalc ambientBlock free (bound)
          (members.eraseIdx selected) := fun element member => members' element (List.mem_of_mem_eraseIdx member)
      have othersObjects : ∀ element ∈ members.eraseIdx selected, isObjectPattern element = true :=
        fun element member => objects element (List.mem_of_mem_eraseIdx member)
      have bodyLocated := located_typed names ((frame.lift (.inl rfl)))
        (by simpa [List.replicate_succ] using shiftName_sorted nameType hereTyped)
        (by rw [shiftName, Mettapedia.GSLT.LanguageDef.RestrictionBlocks.isObjectPattern_rename]; exact hereObject)
        (by simpa [List.replicate_succ] using bodyTyped) bodyObject
      have othersLocated := located_members names frame hereTyped hereObject others' othersObjects
      have permuted : (members.map (encode relabel here)).Perm
          (encode relabel here members[selected] :: (members.eraseIdx selected).map (encode relabel here)) := by
        have := (perm_getElem_eraseIdx members selected inside').map (encode relabel here)
        simpa using this
      rw [encode_bag, encode_nu, encode_bag]
      refine .trans _ _ _ (bag_perm_equivalent (block := locatedRepBlock)
        (located_members names frame hereTyped hereObject members' objects) permuted) ?_
      rw [chosen, encode_nu]
      have extruded := extrusion_equivalent (language := locatedCalc) (block := locatedBlock)
        (by simpa [List.replicate_succ] using bodyLocated) othersLocated
      have mapsEq : (members.eraseIdx selected).map (encode (liftIndex 1 relabel) (shiftName here) ∘ liftBVars 0 1) =
          ((members.eraseIdx selected).map (encode relabel here)).map (liftBVars 0 1) := by
        rw [List.map_map]
        exact List.map_congr_left fun element _ => encode_liftBVars relabel here element
      simp only [List.map_cons, List.map_map]
      rw [mapsEq]
      exact extruded
  case extrusionReverse binder members selected inside' originals erased =>
      obtain ⟨rfl, bagTyped⟩ := nu_inv sourceTyped
      have members' := bag_inv bagTyped
      have objects : ∀ element ∈ members, isObjectPattern element = true := by
        simpa [isObjectPattern, isObjectPatternList_iff] using sourceObject
      have targetMembers := bag_inv targetTyped
      have originalsTyped : Members ambientCoreCalc ambientBlock free (bound) originals :=
        fun element member => targetMembers element (List.mem_cons_of_mem _ member)
      have originalsObjects : ∀ element ∈ originals, isObjectPattern element = true := by
        have all : ∀ element ∈ .apply "ANu" [.lambda none members[selected]] :: originals,
            isObjectPattern element = true := by
          simpa [isObjectPattern, isObjectPatternList_iff] using targetObject
        exact fun element member => all element (List.mem_cons_of_mem _ member)
      have hereShifted : HasType locatedCalc free (nameType :: bound') (shiftName here) nameType :=
        by simpa [List.replicate_succ] using shiftName_sorted nameType hereTyped
      have hereShiftedObject : isObjectPattern (shiftName here) = true := by
        rw [shiftName, Mettapedia.GSLT.LanguageDef.RestrictionBlocks.isObjectPattern_rename]; exact hereObject
      have chosenLocated := located_typed names ((frame.lift (.inl rfl))) hereShifted hereShiftedObject
        (by simpa [List.replicate_succ] using members' _ (List.getElem_mem inside'))
        (objects _ (List.getElem_mem inside'))
      have originalsLocated := located_members names frame hereTyped hereObject originalsTyped originalsObjects
      rw [encode_nu, encode_bag, encode_bag, List.map_cons, encode_nu]
      apply Relation.EqvGen.symm
      refine .trans _ _ _ (extrusion_equivalent (language := locatedCalc) (block := locatedBlock)
        (by simpa [List.replicate_succ] using chosenLocated) originalsLocated) ?_
      apply restrict_fill (language := locatedCalc) (block := locatedBlock)
      have liftedOriginals : (originals.map (encode relabel here)).map (liftBVars 0 1) =
          (members.eraseIdx selected).map (encode (liftIndex 1 relabel) (shiftName here)) := by
        rw [erased, List.map_map, List.map_map]
        exact List.map_congr_left fun element _ => (encode_liftBVars relabel here element).symm
      rw [liftedOriginals]
      have permuted : (members.map (encode (liftIndex 1 relabel) (shiftName here))).Perm
          (encode (liftIndex 1 relabel) (shiftName here) members[selected] ::
            (members.eraseIdx selected).map (encode (liftIndex 1 relabel) (shiftName here))) := by
        have := (perm_getElem_eraseIdx members selected inside').map (encode (liftIndex 1 relabel) (shiftName here))
        simpa using this
      exact Relation.EqvGen.symm _ _ (bag_perm_equivalent (block := locatedRepBlock)
        (located_members names ((frame.lift (.inl rfl))) hereShifted hereShiftedObject
          (fun element member => by simpa [List.replicate_succ] using members' element member) objects) permuted)
  case emptyUnit label listed binder => exact absurd (show label ∈ ([] : List String) from listed) List.not_mem_nil
  case unfold process rest =>
      obtain rfl := tail_none sourceObject
      have members' := bag_inv sourceTyped
      have processTyped := members' _ List.mem_cons_self
      have processObject : isObjectPattern process = true := by
        simpa [isObjectPattern, isObjectPatternList_iff] using sourceObject
      rw [encode_bag, encode_rep _ _ (notLambda processTyped)]
      simp only [List.map_cons, List.map_nil, encode_rep _ _ (notLambda processTyped)]
      exact Relation.EqvGen.symm _ _ (unfold_equivalent (block := locatedRepBlock) (located processTyped processObject))
  case unfoldSwap process rest =>
      obtain rfl := tail_none sourceObject
      have members' := bag_inv sourceTyped
      have processTyped := members' _ (List.mem_cons_of_mem _ List.mem_cons_self)
      have processObject : isObjectPattern process = true := by
        simpa [isObjectPattern, isObjectPatternList_iff] using sourceObject
      rw [encode_bag, encode_rep _ _ (notLambda processTyped)]
      simp only [List.map_cons, List.map_nil, encode_rep _ _ (notLambda processTyped)]
      have processLocated := located processTyped processObject
      have swapped := bag_perm_equivalent (block := locatedRepBlock)
        (first := [.apply "LRep" [encode relabel here process], encode relabel here process])
        (second := [encode relabel here process, .apply "LRep" [encode relabel here process]])
        (fun element member => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl
          · exact replicate_typed (block := locatedRepBlock) processLocated
          · exact processLocated) (List.Perm.swap _ _ _)
      exact .trans _ _ _ swapped (Relation.EqvGen.symm _ _ (unfold_equivalent (block := locatedRepBlock) processLocated))
  case replicationNil =>
      rw [encode_rep _ _ (by intro binder body same; cases same), encode_zero]
      exact replicate_nil_equivalent (block := locatedRepBlock)
  case twice process =>
      have processTyped := rep_inv (rep_inv sourceTyped)
      have processObject : isObjectPattern process = true := by
        simpa [isObjectPattern, isObjectPatternList] using sourceObject
      rw [encode_rep _ _ (by intro binder body same; cases same), encode_rep _ _ (notLambda processTyped)]
      exact replicate_twice_equivalent (block := locatedRepBlock) (located processTyped processObject)
  case par first second rest swapped =>
      have bagTyped := rep_inv sourceTyped
      have bagObject : isObjectPattern (.collection .hashBag (if swapped then [second, first] else [first, second]) rest)
          = true := by simpa [isObjectPattern, isObjectPatternList] using sourceObject
      obtain rfl := tail_none bagObject
      have members' := bag_inv bagTyped
      have objects : ∀ element ∈ (if swapped then [second, first] else [first, second]), isObjectPattern element = true :=
        by simpa [isObjectPattern, isObjectPatternList_iff] using bagObject
      have firstIn : first ∈ (if swapped then [second, first] else [first, second]) := by cases swapped <;> simp
      have secondIn : second ∈ (if swapped then [second, first] else [first, second]) := by cases swapped <;> simp
      have firstTyped := members' first firstIn
      have secondTyped := members' second secondIn
      have firstLocated := located firstTyped (objects first firstIn)
      have secondLocated := located secondTyped (objects second secondIn)
      have parred := replicate_par_equivalent (block := locatedRepBlock) firstLocated secondLocated
      rw [encode_rep _ _ (by intro binder body same; cases same), encode_bag, encode_bag]
      cases swapped with
      | false =>
          simp only [Bool.false_eq_true, if_false, List.map_cons, List.map_nil, encode_rep _ _ (notLambda firstTyped),
            encode_rep _ _ (notLambda secondTyped)]
          exact parred
      | true =>
          simp only [if_true, List.map_cons, List.map_nil, encode_rep _ _ (notLambda firstTyped),
            encode_rep _ _ (notLambda secondTyped)]
          refine .trans _ _ _ (replicate_fill (block := locatedRepBlock) (bag_perm_equivalent (block := locatedRepBlock)
            (fun element member => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at member
              rcases member with rfl | rfl
              · exact secondLocated
              · exact firstLocated) (List.Perm.swap _ _ _))) ?_
          exact parred
  case parReverse first second rest swapped =>
      obtain rfl := tail_none sourceObject
      have targetBag := rep_inv targetTyped
      have members' := bag_inv targetBag
      have objects : ∀ element ∈ [first, second], isObjectPattern element = true := by
        simpa [isObjectPattern, isObjectPatternList_iff, isObjectPatternList] using targetObject
      have firstTyped := members' first List.mem_cons_self
      have secondTyped := members' second (List.mem_cons_of_mem _ List.mem_cons_self)
      have firstLocated := located firstTyped (objects first List.mem_cons_self)
      have secondLocated := located secondTyped (objects second (List.mem_cons_of_mem _ List.mem_cons_self))
      have repFirst := replicate_typed (block := locatedRepBlock) firstLocated
      have repSecond := replicate_typed (block := locatedRepBlock) secondLocated
      have parred := replicate_par_equivalent (block := locatedRepBlock) firstLocated secondLocated
      rw [encode_rep _ _ (by intro binder body same; cases same), encode_bag, encode_bag]
      cases swapped with
      | false =>
          simp only [Bool.false_eq_true, if_false, List.map_cons, List.map_nil, encode_rep _ _ (notLambda firstTyped),
            encode_rep _ _ (notLambda secondTyped)]
          exact Relation.EqvGen.symm _ _ parred
      | true =>
          simp only [if_true, List.map_cons, List.map_nil, encode_rep _ _ (notLambda firstTyped),
            encode_rep _ _ (notLambda secondTyped)]
          refine .trans _ _ _ (bag_perm_equivalent (block := locatedRepBlock)
            (fun element member => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at member
              rcases member with rfl | rfl
              · exact repSecond
              · exact repFirst) (List.Perm.swap _ _ _)) ?_
          exact Relation.EqvGen.symm _ _ parred
  case idempotent process rest =>
      obtain rfl := tail_none sourceObject
      have processTyped := rep_inv targetTyped
      have processObject : isObjectPattern process = true := by
        simpa [isObjectPattern, isObjectPatternList] using targetObject
      rw [encode_bag, encode_rep _ _ (notLambda processTyped)]
      simp only [List.map_cons, List.map_nil, encode_rep _ _ (notLambda processTyped)]
      exact replicate_idempotent_equivalent (block := locatedRepBlock) (located processTyped processObject)
  case bagPerm first second permutation =>
      have members' := bag_inv sourceTyped
      have objects : ∀ element ∈ first, isObjectPattern element = true := by
        simpa [isObjectPattern, isObjectPatternList_iff] using sourceObject
      rw [encode_bag, encode_bag]
      exact bag_perm_equivalent (block := locatedRepBlock)
        (located_members names frame hereTyped hereObject members' objects) (permutation.map _)
  case flatten pre inner post =>
      have sourceLocated := located sourceTyped sourceObject
      have targetLocated := located targetTyped targetObject
      simp only [encode_bag, List.map_append, List.map_cons] at sourceLocated targetLocated ⊢
      exact Mettapedia.GSLT.LanguageDef.RestrictionBlocks.SortedEquiv.ofDerived
        (signature.flatten sourceLocated) sourceLocated targetLocated
  case singleton notLambda' =>
      have sourceLocated := located sourceTyped sourceObject
      have targetLocated := located targetTyped targetObject
      rw [encode_bag] at sourceLocated ⊢
      simp only [List.map_cons, List.map_nil] at sourceLocated ⊢
      exact Mettapedia.GSLT.LanguageDef.RestrictionBlocks.SortedEquiv.ofDerived
        (signature.singleton targetLocated) sourceLocated targetLocated
  case unitElim pre post =>
      have sourceLocated := located sourceTyped sourceObject
      have targetLocated := located targetTyped targetObject
      simp only [encode_bag, List.map_append, List.map_cons, encode_zero] at sourceLocated targetLocated ⊢
      exact Mettapedia.GSLT.LanguageDef.RestrictionBlocks.SortedEquiv.ofDerived
        (signature.unitElim sourceLocated) sourceLocated targetLocated
  case emptyBag =>
      have sourceLocated := located sourceTyped sourceObject
      have targetLocated := located targetTyped targetObject
      rw [encode_bag] at sourceLocated ⊢
      rw [encode_zero] at targetLocated ⊢
      simp only [List.map_nil] at sourceLocated ⊢
      exact Mettapedia.GSLT.LanguageDef.RestrictionBlocks.SortedEquiv.ofDerived
        signature.emptyUnit sourceLocated targetLocated

omit names frame hereTyped hereObject in
/-- Exchanging the two innermost binders after reading under an ambient's location and then a restriction is reading
under the restriction and then the location. -/
theorem swapInner_liftIndex_succ (relabel : Nat → Nat) :
    swapInner ∘ liftIndex 1 (Nat.succ ∘ relabel) = Nat.succ ∘ liftIndex 1 relabel := by
  funext index
  rcases index with _ | index <;> simp [swapInner, liftIndex]

omit names frame hereTyped hereObject in
theorem swapInner_succ_succ : swapInner ∘ Nat.succ ∘ Nat.succ = Nat.succ ∘ Nat.succ := by
  funext index
  simp [swapInner]

omit hereObject in
/-- **The boundary law, read located**: the ambient's location restricted around its marker and its content, the
restriction inside, is the restriction around the location: scope extrusion past the marker and exchange of the two
restrictions. -/
theorem encode_boundary {name body : Pattern} {binder : Option String}
    (sourceTyped : HasType ambientCoreCalc free (bound)
      (.apply "AAmb" [name, .apply "ANu" [.lambda binder body]]) procType)
    (sourceObject : isObjectPattern (.apply "AAmb" [name, .apply "ANu" [.lambda binder body]]) = true) :
    ProcEquiv locatedCalc locatedBlock free (bound')
      (encode relabel here (.apply "AAmb" [name, .apply "ANu" [.lambda binder body]]))
      (encode relabel here (.apply "ANu" [.lambda none (.apply "AAmb" [liftBVars 0 1 name, body])])) := by
  obtain ⟨nameTyped, contentTyped⟩ := amb_inv sourceTyped
  obtain ⟨rfl, bodyTyped⟩ := nu_inv contentTyped
  have nameObject : isObjectPattern name = true := by
    simp [isObjectPattern, isObjectPatternList] at sourceObject
    exact sourceObject.1
  have bodyObject : isObjectPattern body = true := by
    simp [isObjectPattern, isObjectPatternList] at sourceObject
    exact sourceObject.2
  have signature : BlockSignature locatedCalc locatedBlock := locatedLanguage.toBlockSignature
  -- the contexts of names
  set outer := bound' with outerIs
  have shifted := frame.location
  have twoInside := shifted.lift (sort := nameType) (.inl rfl)
  have locationTyped : HasType locatedCalc free (nameType :: bound') (.bvar 0) nameType :=
    .bvar (by simp)
  have locationTwo : HasType locatedCalc free (nameType :: nameType :: bound') (.bvar 1) nameType :=
    .bvar (by simp)
  -- the parts
  set marker : Pattern := .apply "LAmb" [shiftName here, .bvar 0, rename (Nat.succ ∘ relabel) name] with markerIs
  set inner : Pattern := encode (liftIndex 1 (Nat.succ ∘ relabel)) (.bvar 1) body with innerIs
  have markerTyped : HasType locatedCalc free (nameType :: outer) marker procType := by
    simpa [List.replicate_succ] using marker_typed (shiftName_sorted nameType hereTyped) locationTyped
      (rename_name_sorted shifted.sorts nameTyped nameObject)
  have innerTyped : HasType locatedCalc free (nameType :: nameType :: outer) inner procType := by
    have typed := located_typed names twoInside locationTwo rfl
      (by simpa [List.replicate_succ] using bodyTyped) bodyObject
    simpa [List.replicate_succ] using typed
  have restrictedTyped : HasType locatedCalc free (nameType :: outer) (.apply "LNu" [.lambda none inner]) procType :=
    signature.restrict_typed innerTyped
  have liftedMarkerTyped : HasType locatedCalc free (nameType :: nameType :: outer) (liftBVars 0 1 marker) procType := by
    simpa using Mettapedia.GSLT.LanguageDef.RestrictionBlocks.lift_typed (language := locatedCalc)
      (inner := []) (inserted := [nameType]) (outer := nameType :: outer) markerTyped
  -- the source: the location around the marker and the restricted content
  have sourceIs : encode relabel here (.apply "AAmb" [name, .apply "ANu" [.lambda none body]]) =
      .apply "LNu" [.lambda none (.collection .hashBag [marker, .apply "LNu" [.lambda none inner]] none)] := by
    rw [encode_amb, encode_nu]
    rfl
  -- the target: the restriction around the location
  set marker' : Pattern := .apply "LAmb" [shiftName (shiftName here), .bvar 0,
    rename (Nat.succ ∘ liftIndex 1 relabel) (liftBVars 0 1 name)] with markerIs'
  set inner' : Pattern := encode (Nat.succ ∘ liftIndex 1 relabel) (.bvar 0) body with innerIs'
  have targetIs : encode relabel here (.apply "ANu" [.lambda none (.apply "AAmb" [liftBVars 0 1 name, body])]) =
      .apply "LNu" [.lambda none (.apply "LNu" [.lambda none (.collection .hashBag [marker', inner'] none)])] := by
    rw [encode_nu, encode_amb]
  -- the parts read again after the exchange
  have innerSwapped : rename swapInner inner = inner' := by
    rw [innerIs, rename_encode (size body + 1) (Nat.lt_succ_self _), swapInner_liftIndex_succ]
    rfl
  have markerSwapped : rename swapInner (liftBVars 0 1 marker) = marker' := by
    rw [liftBVars_eq_rename, shiftAbove_zero_one, rename_comp, markerIs, markerIs']
    simp only [rename_apply, List.map_cons, List.map_nil, rename_bvar, shiftName, rename_comp, liftBVars_eq_rename,
      shiftAbove_zero_one]
    congr 3
  rw [sourceIs, targetIs]
  -- move the restricted content first, extrude the restriction past the marker, exchange, and reorder
  refine .trans _ _ _ (restrict_fill (language := locatedCalc) (block := locatedBlock)
    (bag_perm_equivalent (block := locatedRepBlock) (first := [marker, .apply "LNu" [.lambda none inner]])
      (second := [.apply "LNu" [.lambda none inner], marker])
      (fun element member => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact markerTyped
        · exact restrictedTyped) (List.Perm.swap _ _ _))) ?_
  refine .trans _ _ _ (restrict_fill (language := locatedCalc) (block := locatedBlock)
    (extrusion_equivalent (language := locatedCalc) (block := locatedBlock) (others := [marker]) innerTyped
      (fun element member => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl
        exact markerTyped))) ?_
  have bodyTyped' : HasType locatedCalc free (nameType :: nameType :: outer)
      (.collection .hashBag [inner, liftBVars 0 1 marker] none) procType :=
    signature.bag_typed (elementsHaveType_iff.mpr fun element member => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact innerTyped
      · exact liftedMarkerTyped)
  refine .trans _ _ _ (exchange_equivalent (language := locatedCalc) (block := locatedBlock) bodyTyped') ?_
  simp only [List.map_cons, List.map_nil, Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_collection,
    innerSwapped, markerSwapped]
  have innerTyped' : HasType locatedCalc free (nameType :: nameType :: outer) inner' procType := by
    rw [← innerSwapped]
    exact Mettapedia.GSLT.LanguageDef.RestrictionBlocks.swapped_typed (language := locatedCalc)
      (block := locatedBlock) innerTyped
  have markerTyped' : HasType locatedCalc free (nameType :: nameType :: outer) marker' procType := by
    rw [← markerSwapped]
    exact Mettapedia.GSLT.LanguageDef.RestrictionBlocks.swapped_typed (language := locatedCalc)
      (block := locatedBlock) liftedMarkerTyped
  exact restrict_fill (language := locatedCalc) (block := locatedBlock)
    (restrict_fill (language := locatedCalc) (block := locatedBlock)
      (bag_perm_equivalent (block := locatedRepBlock)
        (fun element member => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl
          · exact innerTyped'
          · exact markerTyped') (List.Perm.swap _ _ _)))

/-- **The located forms of the two sides of every law of the ambient calculus agree.** -/
theorem encode_shape {source target : Pattern} (shape : AmbShape source target)
    (sourceTyped : HasType ambientCoreCalc free (bound) source procType)
    (targetTyped : HasType ambientCoreCalc free (bound) target procType)
    (sourceObject : isObjectPattern source = true) (targetObject : isObjectPattern target = true) :
    ProcEquiv locatedCalc locatedBlock free (bound') (encode relabel here source)
      (encode relabel here target) := by
  cases shape with
  | law shape =>
      exact encode_lawShape names frame hereTyped hereObject shape sourceTyped targetTyped sourceObject targetObject
  | boundary name binder body => exact encode_boundary names frame hereTyped sourceTyped sourceObject
  | boundaryReverse name binder body =>
      obtain ⟨rfl, -⟩ := nu_inv sourceTyped
      exact Relation.EqvGen.symm _ _ (encode_boundary names frame hereTyped targetTyped targetObject)

end Located

end Mettapedia.Languages.ProcessCalculi.Ambient.Encoding
