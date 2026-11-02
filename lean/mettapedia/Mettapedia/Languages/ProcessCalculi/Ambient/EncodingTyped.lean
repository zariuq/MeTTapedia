import Mettapedia.Languages.ProcessCalculi.Ambient.Encoding
import Mettapedia.Languages.ProcessCalculi.Ambient.FullLaws

/-!
# The located form of a typed ambient process is typed

Free variables and bound variables of an ambient process are names. Read at a name-typed location, with bound names
renamed to bound names, a typed ambient process is a typed located process (`encode_typed`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Encoding

open Mettapedia.Languages.ProcessCalculi.Ambient.Comm (ambientCoreCalc coreSignature commTerms capRule capType)

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (liftIndex)
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (rename size sizeList replicate_typed restrict_typed)
open Mettapedia.GSLT.LanguageDef.BagNormalForm (elementsHaveType_iff isObjectPatternList_iff)
open Mettapedia.Languages.ProcessCalculi.Ambient.Full (terms prefixRule ambientRepBlock ambientBlock)
open Mettapedia.Languages.ProcessCalculi.Ambient.Located (locatedCalc locatedRepBlock locatedBlock locatedLanguage
  capabilityRule capTermRule inputRule outputRule)

/-- The type of names. -/
abbrev nameType : TypeExpr := .base "Name"

/-- The type of processes. -/
abbrev procType : TypeExpr := .base "Proc"

/-- **Every variable is a name**: the free variables, and the bound ones of a context of names. -/
structure NameContext (free : FreeTypeContext) : Prop where
  free : ∀ name type, free name = some type → type = nameType

/-- A pattern of the name sort in either calculus is a variable. -/
theorem name_cases_located {free : FreeTypeContext} {bound : List TypeExpr} {pattern : Pattern}
    {type : TypeExpr} (typed : HasType locatedCalc free bound pattern type) (isName : type = nameType)
    (object : isObjectPattern pattern = true) :
    (∃ index, pattern = .bvar index ∧ bound[index]? = some nameType) ∨
      (∃ name, pattern = .fvar name ∧ free name = some nameType) := by
  cases typed with
  | bvar found => exact .inl ⟨_, rfl, isName ▸ found⟩
  | fvar found => exact .inr ⟨_, rfl, isName ▸ found⟩
  | constructor member _ _ =>
      simp only [locatedCalc, capabilityRule, capTermRule, inputRule, outputRule, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl <;> simp_all
  | collectionConstructor member _ _ =>
      simp only [locatedCalc, capabilityRule, capTermRule, inputRule, outputRule, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl <;> simp_all
  | lambda => cases isName
  | multiLambda => cases isName
  | subst => simp [isObjectPattern] at object
  | collection => cases isName

theorem name_cases_ambient {free : FreeTypeContext} {bound : List TypeExpr} {pattern : Pattern}
    {type : TypeExpr} (typed : HasType ambientCoreCalc free bound pattern type) (isName : type = nameType)
    (object : isObjectPattern pattern = true) :
    (∃ index, pattern = .bvar index ∧ bound[index]? = some nameType) ∨
      (∃ name, pattern = .fvar name ∧ free name = some nameType) := by
  cases typed with
  | bvar found => exact .inl ⟨_, rfl, isName ▸ found⟩
  | fvar found => exact .inr ⟨_, rfl, isName ▸ found⟩
  | constructor member _ _ =>
      simp only [ambientCoreCalc, terms, commTerms, prefixRule, capRule, List.cons_append,
        List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;> simp_all
  | collectionConstructor member _ _ =>
      simp only [ambientCoreCalc, terms, commTerms, prefixRule, capRule, List.cons_append,
        List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;> simp_all
  | lambda => cases isName
  | multiLambda => cases isName
  | subst => simp [isObjectPattern] at object
  | collection => cases isName

/-- **A name renamed into a context of names is a name there.** -/
theorem rename_name_typed {free : FreeTypeContext} {count count' : Nat} {relabel : Nat → Nat}
    (inside : ∀ index < count, relabel index < count') {name : Pattern}
    (typed : HasType ambientCoreCalc free (List.replicate count nameType) name nameType)
    (object : isObjectPattern name = true) :
    HasType locatedCalc free (List.replicate count' nameType) (rename relabel name) nameType := by
  rcases name_cases_ambient typed rfl object with ⟨index, rfl, found⟩ | ⟨name, rfl, found⟩
  · have below : index < count := by
      have := List.getElem?_eq_some_iff.mp found
      simpa using this.1
    show HasType locatedCalc free _ (.bvar (relabel index)) nameType
    exact .bvar (by simp [inside index below])
  · exact .fvar found

/-- A located name read under one more name binder. -/
theorem shiftName_typed {free : FreeTypeContext} {count : Nat} {here : Pattern}
    (typed : HasType locatedCalc free (List.replicate count nameType) here nameType)
    (object : isObjectPattern here = true) :
    HasType locatedCalc free (List.replicate (count + 1) nameType) (shiftName here) nameType := by
  rcases name_cases_located typed rfl object with ⟨index, rfl, found⟩ | ⟨name, rfl, found⟩
  · have below : index < count := by
      have := List.getElem?_eq_some_iff.mp found
      simpa using this.1
    show HasType locatedCalc free _ (.bvar (index + 1)) nameType
    exact .bvar (by simp [below])
  · exact .fvar found

/-- **A located capability over two names and a process is a process.** -/
theorem capability_typed {free : FreeTypeContext} {bound : List TypeExpr} {label : String}
    (listed : label ∈ ["LIn", "LOut", "LOpen"]) {here name continuation : Pattern}
    (hereTyped : HasType locatedCalc free bound here nameType) (nameTyped : HasType locatedCalc free bound name nameType)
    (continuationTyped : HasType locatedCalc free bound continuation procType) :
    HasType locatedCalc free bound (.apply label [here, name, continuation]) procType := by
  have arguments : ArgumentsHaveTypes locatedCalc free bound [here, name, continuation]
      [.simple "l" (.base "Name"), .simple "n" (.base "Name"), .simple "k" (.base "Proc")] :=
    .cons trivial rfl hereTyped (.cons trivial rfl nameTyped (.cons trivial rfl continuationTyped .nil))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl | rfl
  · exact .constructor (rule := locatedCalc.terms[5]) (List.getElem_mem (by decide))
      (by simp [UsesBareCollection, GrammarRule.bareParams, locatedCalc, capabilityRule]) arguments
  · exact .constructor (rule := locatedCalc.terms[6]) (List.getElem_mem (by decide))
      (by simp [UsesBareCollection, GrammarRule.bareParams, locatedCalc, capabilityRule]) arguments
  · exact .constructor (rule := locatedCalc.terms[7]) (List.getElem_mem (by decide))
      (by simp [UsesBareCollection, GrammarRule.bareParams, locatedCalc, capabilityRule]) arguments

theorem marker_typed {free : FreeTypeContext} {bound : List TypeExpr} {parent here name : Pattern}
    (parentTyped : HasType locatedCalc free bound parent nameType) (hereTyped : HasType locatedCalc free bound here nameType)
    (nameTyped : HasType locatedCalc free bound name nameType) :
    HasType locatedCalc free bound (.apply "LAmb" [parent, here, name]) procType :=
  .constructor (rule := locatedCalc.terms[4]) (List.getElem_mem (by decide))
    (by simp [UsesBareCollection, GrammarRule.bareParams, locatedCalc])
    (.cons trivial rfl parentTyped (.cons trivial rfl hereTyped (.cons trivial rfl nameTyped .nil)))

/-- **An opened marker over three names is a process.** -/
theorem opened_typed {free : FreeTypeContext} {bound : List TypeExpr} {parent here name : Pattern}
    (parentTyped : HasType locatedCalc free bound parent nameType) (hereTyped : HasType locatedCalc free bound here nameType)
    (nameTyped : HasType locatedCalc free bound name nameType) :
    HasType locatedCalc free bound (.apply "LOpened" [parent, here, name]) procType :=
  .constructor (rule := locatedCalc.terms[8]) (List.getElem_mem (by decide))
    (by simp [UsesBareCollection, GrammarRule.bareParams, locatedCalc])
    (.cons trivial rfl parentTyped (.cons trivial rfl hereTyped (.cons trivial rfl nameTyped .nil)))

/-- **A marker over three names, opened or not, is a process.** -/
theorem markerOf_typed {free : FreeTypeContext} {bound : List TypeExpr} {label : String}
    (isMarker : label ∈ ["LAmb", "LOpened"]) {parent here name : Pattern}
    (parentTyped : HasType locatedCalc free bound parent nameType) (hereTyped : HasType locatedCalc free bound here nameType)
    (nameTyped : HasType locatedCalc free bound name nameType) :
    HasType locatedCalc free bound (.apply label [parent, here, name]) procType := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at isMarker
  rcases isMarker with rfl | rfl
  · exact marker_typed parentTyped hereTyped nameTyped
  · exact opened_typed parentTyped hereTyped nameTyped

theorem encodeList_eq_map (relabel : Nat → Nat) (here : Pattern) :
    ∀ elements : List Pattern, encodeList relabel here elements = elements.map (encode relabel here)
  | [] => rfl
  | first :: rest => by simp [encodeList, encodeList_eq_map relabel here rest]

/-! ## The located form, constructor by constructor -/

theorem encode_zero (relabel : Nat → Nat) (here : Pattern) :
    encode relabel here (.apply "AZero" []) = .apply "LZero" [] := by simp [encode]

theorem encode_nu (relabel : Nat → Nat) (here : Pattern) (binder : Option String) (body : Pattern) :
    encode relabel here (.apply "ANu" [.lambda binder body]) =
      .apply "LNu" [.lambda binder (encode (liftIndex 1 relabel) (shiftName here) body)] := by simp [encode]

theorem encode_rep (relabel : Nat → Nat) (here : Pattern) {process : Pattern}
    (notLambda : ∀ binder body, process ≠ .lambda binder body) :
    encode relabel here (.apply "ARep" [process]) = .apply "LRep" [encode relabel here process] := by
  cases process with
  | lambda binder body => exact absurd rfl (notLambda binder body)
  | _ => simp [encode]

theorem encode_amb (relabel : Nat → Nat) (here name process : Pattern) :
    encode relabel here (.apply "AAmb" [name, process]) =
      .apply "LNu" [.lambda none (.collection .hashBag
        [.apply "LAmb" [shiftName here, .bvar 0, rename (Nat.succ ∘ relabel) name],
          encode (Nat.succ ∘ relabel) (.bvar 0) process] none)] := by simp [encode]

theorem encode_in (relabel : Nat → Nat) (here name process : Pattern) :
    encode relabel here (.apply "AIn" [name, process]) =
      .apply "LIn" [here, rename relabel name, encode relabel here process] := by simp [encode]

theorem encode_out (relabel : Nat → Nat) (here name process : Pattern) :
    encode relabel here (.apply "AOut" [name, process]) =
      .apply "LOut" [here, rename relabel name, encode relabel here process] := by simp [encode]

theorem encode_open (relabel : Nat → Nat) (here name process : Pattern) :
    encode relabel here (.apply "AOpen" [name, process]) =
      .apply "LOpen" [here, rename relabel name, encode relabel here process] := by simp [encode]

theorem encode_cap (relabel : Nat → Nat) (here capability process : Pattern) :
    encode relabel here (.apply "ACap" [capability, process]) =
      .apply "LCap" [here, rename relabel capability, encode relabel here process] := by simp [encode]

theorem encode_inName (relabel : Nat → Nat) (here : Pattern) (binder : Option String) (body : Pattern) :
    encode relabel here (.apply "AInName" [.lambda binder body]) =
      .apply "LInName" [here, .lambda binder (encode (liftIndex 1 relabel) (shiftName here) body)] := by
  simp [encode]

theorem encode_inCap (relabel : Nat → Nat) (here : Pattern) (binder : Option String) (body : Pattern) :
    encode relabel here (.apply "AInCap" [.lambda binder body]) =
      .apply "LInCap" [here, .lambda binder (encode (liftIndex 1 relabel) (shiftName here) body)] := by
  simp [encode]

theorem encode_outName (relabel : Nat → Nat) (here : Pattern) {message : Pattern}
    (notLambda : ∀ binder body, message ≠ .lambda binder body) :
    encode relabel here (.apply "AOutName" [message]) = .apply "LOutName" [here, rename relabel message] := by
  cases message with
  | lambda binder body => exact absurd rfl (notLambda binder body)
  | _ => simp [encode]

theorem encode_outCap (relabel : Nat → Nat) (here : Pattern) {message : Pattern}
    (notLambda : ∀ binder body, message ≠ .lambda binder body) :
    encode relabel here (.apply "AOutCap" [message]) = .apply "LOutCap" [here, rename relabel message] := by
  cases message with
  | lambda binder body => exact absurd rfl (notLambda binder body)
  | _ => simp [encode]

theorem encode_bag (relabel : Nat → Nat) (here : Pattern) (elements : List Pattern) (rest : Option String) :
    encode relabel here (.collection .hashBag elements rest) =
      .collection .hashBag (elements.map (encode relabel here)) rest := by
  simp [encode, encodeList_eq_map]

/-- Lifting a renaming past one binder keeps it within a context of names one longer. -/
theorem liftIndex_inside {count count' : Nat} {relabel : Nat → Nat} (inside : ∀ index < count, relabel index < count') :
    ∀ index < count + 1, liftIndex 1 relabel index < count' + 1 := by
  intro index below
  simp only [liftIndex]
  split_ifs with zero
  · omega
  · have := inside (index - 1) (by omega)
    omega

/-! ## Located communication -/

/-- A located prefix by a capability term. -/
theorem lcap_typed {free : FreeTypeContext} {bound : List TypeExpr} {here capability continuation : Pattern}
    (hereTyped : HasType locatedCalc free bound here nameType)
    (capabilityTyped : HasType locatedCalc free bound capability capType)
    (continuationTyped : HasType locatedCalc free bound continuation procType) :
    HasType locatedCalc free bound (.apply "LCap" [here, capability, continuation]) procType :=
  .constructor (rule := locatedCalc.terms[14]) (List.getElem_mem (by decide))
    (by simp [UsesBareCollection, GrammarRule.bareParams, locatedCalc, capabilityRule, capTermRule])
    (.cons trivial rfl hereTyped (.cons trivial rfl capabilityTyped (.cons trivial rfl continuationTyped .nil)))

/-- A located input, of a name or of a capability. -/
theorem linput_typed {free : FreeTypeContext} {bound : List TypeExpr} {label : String} {sort : String}
    (listed : (label, sort) ∈ [("LInName", "Name"), ("LInCap", "Cap")]) {here body : Pattern}
    (hereTyped : HasType locatedCalc free bound here nameType)
    (bodyTyped : HasType locatedCalc free (.base sort :: bound) body procType) :
    HasType locatedCalc free bound (.apply label [here, .lambda none body]) procType := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at listed
  rcases listed with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact .constructor (rule := locatedCalc.terms[15]) (List.getElem_mem (by decide))
      (by simp [UsesBareCollection, GrammarRule.bareParams, locatedCalc, capabilityRule, capTermRule, inputRule])
      (.cons trivial rfl hereTyped (.cons trivial rfl (.lambda bodyTyped) .nil))
  · exact .constructor (rule := locatedCalc.terms[17]) (List.getElem_mem (by decide))
      (by simp [UsesBareCollection, GrammarRule.bareParams, locatedCalc, capabilityRule, capTermRule, inputRule])
      (.cons trivial rfl hereTyped (.cons trivial rfl (.lambda bodyTyped) .nil))

/-- A located output, of a name or of a capability. -/
theorem loutput_typed {free : FreeTypeContext} {bound : List TypeExpr} {label : String} {sort : String}
    (listed : (label, sort) ∈ [("LOutName", "Name"), ("LOutCap", "Cap")]) {here message : Pattern}
    (hereTyped : HasType locatedCalc free bound here nameType)
    (messageTyped : HasType locatedCalc free bound message (.base sort)) :
    HasType locatedCalc free bound (.apply label [here, message]) procType := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at listed
  rcases listed with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact .constructor (rule := locatedCalc.terms[16]) (List.getElem_mem (by decide))
      (by simp [UsesBareCollection, GrammarRule.bareParams, locatedCalc, capabilityRule, capTermRule, outputRule])
      (.cons trivial rfl hereTyped (.cons trivial rfl messageTyped .nil))
  · exact .constructor (rule := locatedCalc.terms[18]) (List.getElem_mem (by decide))
      (by simp [UsesBareCollection, GrammarRule.bareParams, locatedCalc, capabilityRule, capTermRule, outputRule])
      (.cons trivial rfl hereTyped (.cons trivial rfl messageTyped .nil))

/-- **A name renamed by a renaming that keeps sorts is a name.** -/
theorem rename_name_sorted {free : FreeTypeContext} {bound bound' : List TypeExpr} {relabel : Nat → Nat}
    (sorts : ∀ index type, bound[index]? = some type → bound'[relabel index]? = some type) {name : Pattern}
    (typed : HasType ambientCoreCalc free bound name nameType) (object : isObjectPattern name = true) :
    HasType locatedCalc free bound' (rename relabel name) nameType := by
  rcases name_cases_ambient typed rfl object with ⟨index, rfl, found⟩ | ⟨name, rfl, found⟩
  · show HasType locatedCalc free _ (.bvar (relabel index)) nameType
    exact .bvar (sorts _ _ found)
  · exact .fvar found

/-- **A capability term renamed by a renaming that keeps sorts is a located capability term**: the capability
constructors are the same in both calculi. -/
theorem rename_cap_typed {free : FreeTypeContext} (names : NameContext free) :
    ∀ (fuel : Nat) {bound bound' : List TypeExpr} {relabel : Nat → Nat} {capability : Pattern},
      size capability < fuel → (∀ index type, bound[index]? = some type → bound'[relabel index]? = some type) →
      HasType ambientCoreCalc free bound capability capType → isObjectPattern capability = true →
      HasType locatedCalc free bound' (rename relabel capability) capType
  | 0, _, _, _, _, small, _, _, _ => absurd small (Nat.not_lt_zero _)
  | fuel + 1, bound, bound', relabel, capability, small, sorts, typed, object => by
      cases capability with
      | bvar index =>
          cases typed with
          | bvar found => exact .bvar (sorts _ _ found)
      | fvar name =>
          cases typed with
          | fvar found => exact absurd (names.free _ _ found) (by decide)
      | lambda binder body => cases typed
      | multiLambda arity binders body => cases typed
      | subst body replacement => simp [isObjectPattern] at object
      | collection kind elements rest =>
          rcases hasType_collection_inversion typed with ⟨_, typeIs, _⟩ |
            ⟨rule, parameterName, elementType, member, shape, typeIs, elementsTyped⟩
          · cases typeIs
          · simp only [ambientCoreCalc, terms, commTerms, prefixRule, capRule, List.cons_append,
              List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
            rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
              rfl | rfl | rfl <;> simp_all [GrammarRule.bareParams]
      | apply label arguments =>
          obtain ⟨rule, member, rfl, notBare, typeIs, argumentsTyped⟩ := hasType_apply_inversion typed
          have objects : ∀ argument ∈ arguments, isObjectPattern argument = true := by
            simpa [isObjectPattern, isObjectPatternList_iff] using object
          have argumentSmall : ∀ argument ∈ arguments, size argument < fuel := by
            intro argument inArguments
            have := Mettapedia.GSLT.LanguageDef.RestrictionBlocks.size_lt_of_mem inArguments
            simp only [size] at small
            omega
          simp only [ambientCoreCalc, terms, commTerms, prefixRule, capRule, List.cons_append,
            List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl <;>
            simp only [capType, TypeExpr.base.injEq] at typeIs <;>
            try (exact absurd typeIs (by decide))
          -- `in n`, `out n`, `open n`
          all_goals try (
            cases argumentsTyped with
            | cons _ parameter nameTyped rest =>
                cases rest
                simp only [parameterType?, Option.some.injEq] at parameter
                subst parameter
                rw [Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_apply]
                simp only [List.map_cons, List.map_nil]
                first
                  | exact .constructor (rule := locatedCalc.terms[9]) (List.getElem_mem (by decide))
                      (by simp [UsesBareCollection, GrammarRule.bareParams, locatedCalc, capTermRule])
                      (.cons trivial rfl (rename_name_sorted sorts nameTyped (objects _ List.mem_cons_self)) .nil)
                  | exact .constructor (rule := locatedCalc.terms[10]) (List.getElem_mem (by decide))
                      (by simp [UsesBareCollection, GrammarRule.bareParams, locatedCalc, capTermRule])
                      (.cons trivial rfl (rename_name_sorted sorts nameTyped (objects _ List.mem_cons_self)) .nil)
                  | exact .constructor (rule := locatedCalc.terms[11]) (List.getElem_mem (by decide))
                      (by simp [UsesBareCollection, GrammarRule.bareParams, locatedCalc, capTermRule])
                      (.cons trivial rfl (rename_name_sorted sorts nameTyped (objects _ List.mem_cons_self)) .nil))
          -- the empty path
          · cases argumentsTyped
            rw [Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_apply]
            exact .constructor (rule := locatedCalc.terms[12]) (List.getElem_mem (by decide))
              (by simp [UsesBareCollection, GrammarRule.bareParams, locatedCalc]) .nil
          -- a path
          · cases argumentsTyped with
            | cons _ firstParameter firstTyped rest =>
                cases rest with
                | cons _ secondParameter secondTyped last =>
                    cases last
                    simp only [parameterType?, Option.some.injEq] at firstParameter secondParameter
                    subst firstParameter secondParameter
                    rw [Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_apply]
                    simp only [List.map_cons, List.map_nil]
                    exact .constructor (rule := locatedCalc.terms[13]) (List.getElem_mem (by decide))
                      (by simp [UsesBareCollection, GrammarRule.bareParams, locatedCalc])
                      (.cons trivial rfl (rename_cap_typed names fuel (argumentSmall _ List.mem_cons_self) sorts
                          firstTyped (objects _ List.mem_cons_self))
                        (.cons trivial rfl (rename_cap_typed names fuel
                          (argumentSmall _ (List.mem_cons_of_mem _ List.mem_cons_self)) sorts secondTyped
                          (objects _ (List.mem_cons_of_mem _ List.mem_cons_self))) .nil))

/-- A renaming that keeps sorts, lifted past one binder of a sort. -/
theorem liftIndex_sorts {bound bound' : List TypeExpr} {relabel : Nat → Nat}
    (sorts : ∀ index type, bound[index]? = some type → bound'[relabel index]? = some type) (sort : TypeExpr) :
    ∀ index type, (sort :: bound)[index]? = some type → (sort :: bound')[liftIndex 1 relabel index]? = some type := by
  intro index type found
  cases index with
  | zero => simpa [liftIndex] using found
  | succ index =>
      have inner := sorts index type (by simpa using found)
      simpa [liftIndex] using inner

/-- **The located form of a typed ambient process is a typed located process**, in a context of names and
capabilities: read at a location of the name sort, every bound variable renamed to one of its sort. -/
theorem encode_typed_sorted {free : FreeTypeContext} (names : NameContext free) :
    ∀ (fuel : Nat) {bound bound' : List TypeExpr} {relabel : Nat → Nat} {here process : Pattern},
      size process < fuel → (∀ type ∈ bound, type = nameType ∨ type = capType) →
      (∀ index type, bound[index]? = some type → bound'[relabel index]? = some type) →
      HasType locatedCalc free bound' here nameType → isObjectPattern here = true →
      HasType ambientCoreCalc free bound process procType → isObjectPattern process = true →
      HasType locatedCalc free bound' (encode relabel here process) procType
  | 0, _, _, _, _, _, small, _, _, _, _, _, _ => absurd small (Nat.not_lt_zero _)
  | fuel + 1, bound, bound', relabel, here, process, small, sorted, sorts, hereTyped, hereObject, typed, object => by
      cases process with
      | bvar index =>
          cases typed with
          | bvar found =>
              rcases sorted _ (List.mem_of_getElem? found) with same | same <;> exact absurd same (by decide)
      | fvar name =>
          cases typed with
          | fvar found => exact absurd (names.free _ _ found) (by decide)
      | lambda binder body => cases typed
      | multiLambda arity binders body => cases typed
      | subst body replacement => simp [isObjectPattern] at object
      | collection kind elements rest =>
          rcases hasType_collection_inversion typed with ⟨_, typeIs, _⟩ |
            ⟨rule, parameterName, elementType, member, shape, typeIs, elementsTyped⟩
          · cases typeIs
          · simp only [ambientCoreCalc, terms, commTerms, prefixRule, capRule, List.cons_append,
              List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
            rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
              rfl | rfl | rfl <;>
              simp [GrammarRule.bareParams] at shape
            obtain ⟨rfl, rfl, rfl⟩ := shape
            have tailNone : rest = none := by
              simpa [isObjectPattern] using (Bool.and_eq_true _ _).mp object |>.1
            subst tailNone
            have objects : ∀ element ∈ elements, isObjectPattern element = true := by
              simpa [isObjectPattern, isObjectPatternList_iff] using object
            rw [encode_bag]
            apply locatedLanguage.toBlockSignature.bag_typed
            apply elementsHaveType_iff.mpr
            intro element inMapped
            obtain ⟨original, inElements, rfl⟩ := List.mem_map.mp inMapped
            have originalSmall : size original < fuel := by
              have := Mettapedia.GSLT.LanguageDef.RestrictionBlocks.size_lt_of_mem inElements
              simp only [size] at small
              omega
            exact encode_typed_sorted names fuel originalSmall sorted sorts hereTyped hereObject
              (elementsHaveType_iff.mp elementsTyped original inElements) (objects original inElements)
      | apply label arguments =>
          obtain ⟨rule, member, rfl, notBare, typeIs, argumentsTyped⟩ := hasType_apply_inversion typed
          have objects : ∀ argument ∈ arguments, isObjectPattern argument = true := by
            simpa [isObjectPattern, isObjectPatternList_iff] using object
          have argumentSmall : ∀ argument ∈ arguments, size argument < fuel := by
            intro argument inArguments
            have := Mettapedia.GSLT.LanguageDef.RestrictionBlocks.size_lt_of_mem inArguments
            simp only [size] at small
            omega
          have shiftedTyped : HasType locatedCalc free (nameType :: bound') (shiftName here) nameType :=
            Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_typed_on_support hereTyped
              fun index sort _ found => by simpa using found
          have shiftedTypedCap : HasType locatedCalc free (capType :: bound') (shiftName here) nameType :=
            Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_typed_on_support hereTyped
              fun index sort _ found => by simpa using found
          have shiftedObject : isObjectPattern (shiftName here) = true := by
            rw [shiftName, Mettapedia.GSLT.LanguageDef.RestrictionBlocks.isObjectPattern_rename]
            exact hereObject
          have sortedCons : ∀ sort, sort = nameType ∨ sort = capType →
              ∀ type ∈ sort :: bound, type = nameType ∨ type = capType := by
            intro sort sortIs type member
            rcases List.mem_cons.mp member with rfl | inside
            · exact sortIs
            · exact sorted type inside
          simp only [ambientCoreCalc, terms, commTerms, prefixRule, capRule, List.cons_append,
            List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl <;>
            simp only [procType, TypeExpr.base.injEq] at typeIs <;> try (exact absurd typeIs (by decide))
          · -- inaction
            cases argumentsTyped
            rw [encode_zero]
            exact locatedLanguage.toBlockSignature.unit_typed
          · exact absurd ⟨"ps", .hashBag, .base "Proc", rfl⟩ notBare
          · -- restriction
            cases argumentsTyped with
            | cons representation parameterType argumentTyped rest =>
                cases rest
                obtain ⟨body, rfl⟩ :=
                  (matchesParameterRepresentation_abstractionNamed_iff _ _ _ _).mp representation
                simp only [parameterType?, Option.some.injEq] at parameterType
                subst parameterType
                cases argumentTyped with
                | lambda bodyTyped =>
                    have bodySmall : size body < fuel := by
                      have := argumentSmall _ List.mem_cons_self
                      simp only [size] at this
                      omega
                    have bodyObject : isObjectPattern body = true := by
                      simpa [isObjectPattern] using objects _ List.mem_cons_self
                    have inner := encode_typed_sorted names fuel bodySmall (sortedCons nameType (.inl rfl))
                      (liftIndex_sorts sorts nameType) shiftedTyped shiftedObject bodyTyped bodyObject
                    rw [encode_nu]
                    exact locatedLanguage.toBlockSignature.restrict_typed inner
          · -- replication
            cases argumentsTyped with
            | cons representation parameterType argumentTyped rest =>
                cases rest
                simp only [parameterType?, Option.some.injEq] at parameterType
                subst parameterType
                have inner := encode_typed_sorted names fuel (argumentSmall _ List.mem_cons_self) sorted sorts
                  hereTyped hereObject argumentTyped (objects _ List.mem_cons_self)
                rw [encode_rep _ _ fun binder body same => by subst same; cases argumentTyped]
                exact replicate_typed (block := locatedRepBlock) inner
          · -- an ambient
            cases argumentsTyped with
            | cons nameRepresentation nameParameter nameTyped rest =>
                cases rest with
                | cons contentRepresentation contentParameter contentTyped last =>
                    cases last
                    simp only [parameterType?, Option.some.injEq] at nameParameter contentParameter
                    subst nameParameter contentParameter
                    have shifted : ∀ index type, bound[index]? = some type →
                        (nameType :: bound')[(Nat.succ ∘ relabel) index]? = some type := fun index type found => by
                      simpa using sorts index type found
                    have locationTyped : HasType locatedCalc free (nameType :: bound') (.bvar 0) nameType :=
                      .bvar (by simp)
                    have contentSmall : size _ < fuel := argumentSmall _ (List.mem_cons_of_mem _ List.mem_cons_self)
                    have inner := encode_typed_sorted names fuel contentSmall sorted shifted locationTyped rfl
                      contentTyped (objects _ (List.mem_cons_of_mem _ List.mem_cons_self))
                    rw [encode_amb]
                    apply locatedLanguage.toBlockSignature.restrict_typed
                    apply locatedLanguage.toBlockSignature.bag_typed
                    apply elementsHaveType_iff.mpr
                    intro element inElements
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at inElements
                    rcases inElements with rfl | rfl
                    · exact marker_typed shiftedTyped locationTyped
                        (rename_name_sorted shifted nameTyped (objects _ List.mem_cons_self))
                    · exact inner
          -- `in n.P`, `out n.P`, `open n.P`
          all_goals try (
            cases argumentsTyped with
            | cons nameRepresentation nameParameter nameTyped rest =>
                cases rest with
                | cons contentRepresentation contentParameter contentTyped last =>
                    cases last
                    simp only [parameterType?, Option.some.injEq] at nameParameter contentParameter
                    subst nameParameter contentParameter
                    have inner := encode_typed_sorted names fuel
                      (argumentSmall _ (List.mem_cons_of_mem _ List.mem_cons_self)) sorted sorts hereTyped hereObject
                      contentTyped (objects _ (List.mem_cons_of_mem _ List.mem_cons_self))
                    first
                      | rw [encode_in]
                      | rw [encode_out]
                      | rw [encode_open]
                    exact capability_typed (by simp) hereTyped
                      (rename_name_sorted sorts nameTyped (objects _ List.mem_cons_self)) inner)
          -- a prefix by a capability term
          · cases argumentsTyped with
            | @cons _ capability _ _ _ _ capRepresentation capParameter capabilityTyped rest =>
                cases rest with
                | @cons _ content _ _ _ _ contentRepresentation contentParameter contentTyped last =>
                    cases last
                    simp only [parameterType?, Option.some.injEq] at capParameter contentParameter
                    subst capParameter contentParameter
                    have inner := encode_typed_sorted names fuel
                      (argumentSmall _ (List.mem_cons_of_mem _ List.mem_cons_self)) sorted sorts hereTyped hereObject
                      contentTyped (objects _ (List.mem_cons_of_mem _ List.mem_cons_self))
                    rw [encode_cap]
                    exact lcap_typed hereTyped (rename_cap_typed names (size _ + 1) (Nat.lt_succ_self _) sorts
                      capabilityTyped (objects _ List.mem_cons_self)) inner
          -- inputs: their bodies under their binders
          all_goals try (
            cases argumentsTyped with
            | cons representation parameterType argumentTyped rest =>
                cases rest
                obtain ⟨body, rfl⟩ :=
                  (matchesParameterRepresentation_abstractionNamed_iff _ _ _ _).mp representation
                simp only [parameterType?, Option.some.injEq] at parameterType
                subst parameterType
                cases argumentTyped with
                | lambda bodyTyped =>
                    have bodySmall : size body < fuel := by
                      have := argumentSmall _ List.mem_cons_self
                      simp only [size] at this
                      omega
                    have bodyObject : isObjectPattern body = true := by
                      simpa [isObjectPattern] using objects _ List.mem_cons_self
                    first
                      | (have inner := encode_typed_sorted names fuel bodySmall (sortedCons nameType (.inl rfl))
                          (liftIndex_sorts sorts nameType) shiftedTyped shiftedObject bodyTyped bodyObject
                         rw [encode_inName]
                         exact linput_typed (sort := "Name") (by simp) hereTyped inner)
                      | (have inner := encode_typed_sorted names fuel bodySmall (sortedCons capType (.inr rfl))
                          (liftIndex_sorts sorts capType) shiftedTypedCap shiftedObject bodyTyped bodyObject
                         rw [encode_inCap]
                         exact linput_typed (sort := "Cap") (by simp) hereTyped inner))
          -- outputs: their messages
          all_goals
            cases argumentsTyped with
            | @cons _ message _ _ _ _ representation parameterType messageTyped rest =>
                cases rest
                simp only [parameterType?, Option.some.injEq] at parameterType
                subst parameterType
                have notLambda : ∀ binder body, message ≠ .lambda binder body := by
                  rintro binder body rfl
                  cases messageTyped
                first
                  | (rw [encode_outName _ _ notLambda]
                     exact loutput_typed (sort := "Name") (by simp) hereTyped
                       (rename_name_sorted sorts messageTyped (objects _ List.mem_cons_self)))
                  | (rw [encode_outCap _ _ notLambda]
                     exact loutput_typed (sort := "Cap") (by simp) hereTyped
                       (rename_cap_typed names (size _ + 1) (Nat.lt_succ_self _) sorts messageTyped
                         (objects _ List.mem_cons_self)))

/-! ## Frames: contexts of names and capabilities, renamed -/

/-- **A frame for the located form**: a context of names and capabilities, renamed into a located context by a renaming
that keeps every variable's sort. -/
structure LocatedFrame (bound bound' : List TypeExpr) (relabel : Nat → Nat) : Prop where
  sorted : ∀ type ∈ bound, type = nameType ∨ type = capType
  sorts : ∀ index type, bound[index]? = some type → bound'[relabel index]? = some type

/-- A frame lifted past a binder of a name or a capability. -/
theorem LocatedFrame.lift {bound bound' : List TypeExpr} {relabel : Nat → Nat}
    (frame : LocatedFrame bound bound' relabel) {sort : TypeExpr} (sortIs : sort = nameType ∨ sort = capType) :
    LocatedFrame (sort :: bound) (sort :: bound') (liftIndex 1 relabel) where
  sorted := fun type member => by
    rcases List.mem_cons.mp member with rfl | inside
    · exact sortIs
    · exact frame.sorted type inside
  sorts := liftIndex_sorts frame.sorts sort

/-- A frame past an ambient's location: the located context binds the location. -/
theorem LocatedFrame.location {bound bound' : List TypeExpr} {relabel : Nat → Nat}
    (frame : LocatedFrame bound bound' relabel) : LocatedFrame bound (nameType :: bound') (Nat.succ ∘ relabel) where
  sorted := frame.sorted
  sorts := fun index type found => by simpa using frame.sorts index type found

/-- A frame of names. -/
theorem LocatedFrame.ofNames {count count' : Nat} {relabel : Nat → Nat} (inside : ∀ index < count, relabel index < count') :
    LocatedFrame (List.replicate count nameType) (List.replicate count' nameType) relabel where
  sorted := fun type member => .inl (List.eq_of_mem_replicate member)
  sorts := fun index type found => by
    have ⟨below, typeIs⟩ := List.getElem?_eq_some_iff.mp found
    simp only [List.length_replicate] at below
    simp only [List.getElem_replicate] at typeIs
    subst typeIs
    simp [inside index below]

/-- A location read one binder deeper is a location. -/
theorem shiftName_sorted {free : FreeTypeContext} {bound : List TypeExpr} {here : Pattern} (sort : TypeExpr)
    (typed : HasType locatedCalc free bound here nameType) :
    HasType locatedCalc free (sort :: bound) (shiftName here) nameType :=
  Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename_typed_on_support typed
    fun index sort' _ found => by simpa using found

theorem shiftName_object {here : Pattern} (object : isObjectPattern here = true) :
    isObjectPattern (shiftName here) = true := by
  rw [shiftName, Mettapedia.GSLT.LanguageDef.RestrictionBlocks.isObjectPattern_rename]
  exact object

/-- **The located form of a typed process in a frame is typed.** -/
theorem encode_typed_frame {free : FreeTypeContext} (names : NameContext free) {bound bound' : List TypeExpr}
    {relabel : Nat → Nat} (frame : LocatedFrame bound bound' relabel) {here process : Pattern}
    (hereTyped : HasType locatedCalc free bound' here nameType) (hereObject : isObjectPattern here = true)
    (typed : HasType ambientCoreCalc free bound process procType) (object : isObjectPattern process = true) :
    HasType locatedCalc free bound' (encode relabel here process) procType :=
  encode_typed_sorted names (size process + 1) (Nat.lt_succ_self _) frame.sorted frame.sorts hereTyped hereObject
    typed object

/-- **The located form of a typed ambient process is a typed located process**, read at a location of the name sort
with bound names renamed to bound names. -/
theorem encode_typed {free : FreeTypeContext} (names : NameContext free) (fuel : Nat) {count count' : Nat}
    {relabel : Nat → Nat} {here process : Pattern} (small : size process < fuel)
    (inside : ∀ index < count, relabel index < count')
    (hereTyped : HasType locatedCalc free (List.replicate count' nameType) here nameType)
    (hereObject : isObjectPattern here = true)
    (typed : HasType ambientCoreCalc free (List.replicate count nameType) process procType)
    (object : isObjectPattern process = true) :
    HasType locatedCalc free (List.replicate count' nameType) (encode relabel here process) procType :=
  encode_typed_sorted names fuel small (fun type member => .inl (List.eq_of_mem_replicate member))
    (fun index type found => by
      have ⟨below, typeIs⟩ := List.getElem?_eq_some_iff.mp found
      simp only [List.length_replicate] at below
      simp only [List.getElem_replicate] at typeIs
      subst typeIs
      simp [inside index below]) hereTyped hereObject typed object

end Mettapedia.Languages.ProcessCalculi.Ambient.Encoding
