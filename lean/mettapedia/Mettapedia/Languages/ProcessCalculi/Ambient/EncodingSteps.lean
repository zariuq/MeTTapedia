import Mettapedia.Languages.ProcessCalculi.Ambient.EncodingLaws
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationObjects

/-!
# Equivalent ambient processes have equivalent located forms

The located form reads an ambient process constructor by constructor, so a law applied anywhere inside a process is a
law of the located calculus applied at the corresponding place of its located form, at the location and under the
binders the reading passed on its way there (`located_fill`). Each step of the ambient calculus's static theory
between typed processes therefore relates their located forms (`located_step`), and so does every chain of such steps
through object processes (`located_chain`).

A law relates processes: no side of a law is an abstraction, and no law relates two variables, so no law applies at a
name (`not_names`) or inside a capability term (`not_caps`). Inside an input, a law applies in its body, under the
binder of a name or of a capability, so the reading carries a frame of both sorts (`LocatedFrame`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Encoding

open Mettapedia.Languages.ProcessCalculi.Ambient.Comm (ambientCoreCalc commTerms capRule capType)

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (liftIndex)
open Mettapedia.OSLF.MeTTaIL.DerivedContexts (OneHoleContext)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (BasePremiseEvaluator)
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (rename size sizeList Members ProcEquiv SortedEquiv ObjectChain
  BlockSignature bag_fill restrict_fill replicate_fill)
open Mettapedia.GSLT.LanguageDef.BagNormalForm (elementsHaveType_iff isObjectPatternList_iff)
open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationContextStep)
open Mettapedia.Languages.ProcessCalculi.Ambient.Full (terms prefixRule ambientRepBlock ambientBlock
  AmbShape ambient_generator_shape)
open Mettapedia.Languages.ProcessCalculi.Ambient.Located (locatedCalc locatedRepBlock locatedBlock locatedLanguage
  capabilityRule)

/-! ## What a law relates -/

/-- The arguments of a typed constructor are as many as its parameters. -/
theorem arguments_length {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr} :
    ∀ {arguments : List Pattern} {params : List TermParam},
      ArgumentsHaveTypes language free bound arguments params → arguments.length = params.length
  | [], _, typed => by cases typed; rfl
  | _ :: _, _, typed => by
      cases typed with
      | cons _ _ _ rest => simp [arguments_length rest]

/-- **A name holds no term but a variable**: a typed object name is a variable, so a context filled to a name is the
hole, filled with a variable. -/
theorem no_names {free : FreeTypeContext} {bound : List TypeExpr} {inner : Pattern}
    (notVariable : (∀ index, inner ≠ .bvar index) ∧ ∀ name, inner ≠ .fvar name) (context : OneHoleContext)
    (typed : HasType ambientCoreCalc free bound (context.fill inner) nameType)
    (object : isObjectPattern (context.fill inner) = true) : False := by
  have variable_of : ∀ {pattern : Pattern}, HasType ambientCoreCalc free bound pattern nameType →
      isObjectPattern pattern = true → ¬ ((∀ index, pattern ≠ .bvar index) ∧ ∀ name, pattern ≠ .fvar name) := by
    intro pattern typed object ⟨notBound, notFree⟩
    rcases name_cases_ambient typed rfl object with ⟨index, rfl, -⟩ | ⟨name, rfl, -⟩
    · exact notBound index rfl
    · exact notFree name rfl
  cases context
  case hole =>
    simp only [OneHoleContext.fill] at typed object
    exact variable_of typed object notVariable
  all_goals exact variable_of typed object ⟨by simp [OneHoleContext.fill], by simp [OneHoleContext.fill]⟩

/-- **No law applies at a name**: two fillings of one context by the two sides of a law are not both object names. -/
theorem not_names {free : FreeTypeContext} {bound : List TypeExpr} {source target : Pattern}
    (shape : AmbShape source target ∨ AmbShape target source) (context : OneHoleContext)
    (sourceTyped : HasType ambientCoreCalc free bound (context.fill source) nameType)
    (targetTyped : HasType ambientCoreCalc free bound (context.fill target) nameType)
    (sourceObject : isObjectPattern (context.fill source) = true)
    (targetObject : isObjectPattern (context.fill target) = true) : False := by
  rcases shape with shape | shape
  · exact no_names shape.notVariable context sourceTyped sourceObject
  · exact no_names shape.notVariable context targetTyped targetObject

/-- A typed capability prefixes a typed process with a name. -/
theorem prefix_inv {free : FreeTypeContext} {bound : List TypeExpr} {label : String} {name process : Pattern}
    (listed : label ∈ ["AIn", "AOut", "AOpen"])
    (typed : HasType ambientCoreCalc free bound (.apply label [name, process]) procType) :
    HasType ambientCoreCalc free bound name nameType ∧ HasType ambientCoreCalc free bound process procType := by
  obtain ⟨rule, member, labelIs, -, -, arguments⟩ := hasType_apply_inversion typed
  simp only [ambientCoreCalc, terms, commTerms, prefixRule, capRule, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;>
    rcases listed with rfl | rfl | rfl <;> simp at labelIs
  all_goals
    cases arguments with
    | cons _ nameParameter nameTyped rest =>
        cases rest with
        | cons _ contentParameter contentTyped _ =>
            simp only [parameterType?, Option.some.injEq] at nameParameter contentParameter
            subst nameParameter contentParameter
            exact ⟨nameTyped, contentTyped⟩

/-- A located capability carries chains through its continuation. -/
theorem capability_fill {free : FreeTypeContext} {bound : List TypeExpr} {label : String}
    (listed : label ∈ ["LIn", "LOut", "LOpen"]) {here name first second : Pattern}
    (hereTyped : HasType locatedCalc free bound here nameType) (nameTyped : HasType locatedCalc free bound name nameType)
    (equivalent : ProcEquiv locatedCalc locatedBlock free bound first second) :
    ProcEquiv locatedCalc locatedBlock free bound (.apply label [here, name, first]) (.apply label [here, name, second]) :=
  SortedEquiv.fill (.apply label [here, name] .hole []) (fun _ typed => capability_typed listed hereTyped nameTyped typed)
    equivalent

/-- A located prefix by a capability term carries chains through its continuation. -/
theorem lcap_fill {free : FreeTypeContext} {bound : List TypeExpr} {here capability first second : Pattern}
    (hereTyped : HasType locatedCalc free bound here nameType)
    (capabilityTyped : HasType locatedCalc free bound capability capType)
    (equivalent : ProcEquiv locatedCalc locatedBlock free bound first second) :
    ProcEquiv locatedCalc locatedBlock free bound (.apply "LCap" [here, capability, first])
      (.apply "LCap" [here, capability, second]) :=
  SortedEquiv.fill (.apply "LCap" [here, capability] .hole [])
    (fun _ typed => lcap_typed hereTyped capabilityTyped typed) equivalent

/-- A located input carries chains through its body, under its binder. -/
theorem linput_fill {free : FreeTypeContext} {bound : List TypeExpr} {label sort : String}
    (listed : (label, sort) ∈ [("LInName", "Name"), ("LInCap", "Cap")]) {here first second : Pattern}
    (hereTyped : HasType locatedCalc free bound here nameType)
    (equivalent : ProcEquiv locatedCalc locatedBlock free (.base sort :: bound) first second) :
    ProcEquiv locatedCalc locatedBlock free bound (.apply label [here, .lambda none first])
      (.apply label [here, .lambda none second]) :=
  SortedEquiv.fill (.apply label [here] (.lambda none .hole) [])
    (fun _ typed => linput_typed listed hereTyped typed) equivalent

/-- One argument at one place: the others are none. -/
theorem positions_one {before after : List Pattern} {middle : Pattern} (length : (before ++ middle :: after).length = 1) :
    before = [] ∧ after = [] := by
  simp only [List.length_append, List.length_cons] at length
  exact ⟨List.eq_nil_of_length_eq_zero (by omega), List.eq_nil_of_length_eq_zero (by omega)⟩

/-- One argument of two: the first or the second. -/
theorem positions_two {before after : List Pattern} {middle : Pattern} (length : (before ++ middle :: after).length = 2) :
    (before = [] ∧ ∃ last, after = [last]) ∨ (∃ first, before = [first] ∧ after = []) := by
  rcases before with _ | ⟨first, _ | ⟨second, rest⟩⟩
  · rcases after with _ | ⟨last, _ | ⟨other, rest⟩⟩
    · simp at length
    · exact .inl ⟨rfl, last, rfl⟩
    · simp at length
  · rcases after with _ | ⟨last, rest⟩
    · exact .inr ⟨first, rfl, rfl⟩
    · simp at length
  · simp only [List.length_append, List.length_cons] at length
    omega

/-! ## No law applies inside a capability term -/

/-- A capability term of the core built by a constructor: `in n`, `out n` or `open n` over a name, the empty path, or
the path of two capability terms. -/
theorem cap_apply_inv {free : FreeTypeContext} {bound : List TypeExpr} {label : String} {arguments : List Pattern}
    (typed : HasType ambientCoreCalc free bound (.apply label arguments) capType) :
    (label ∈ ["CapIn", "CapOut", "CapOpen"] ∧ ∃ name, arguments = [name] ∧
        HasType ambientCoreCalc free bound name nameType) ∨
      (label = "CapEps" ∧ arguments = []) ∨
      (label = "CapPath" ∧ ∃ left right, arguments = [left, right] ∧
        HasType ambientCoreCalc free bound left capType ∧ HasType ambientCoreCalc free bound right capType) := by
  obtain ⟨rule, member, rfl, -, typeIs, argumentsTyped⟩ := hasType_apply_inversion typed
  simp only [ambientCoreCalc, terms, commTerms, prefixRule, capRule, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;>
    simp only [capType, TypeExpr.base.injEq] at typeIs <;> try (exact absurd typeIs (by decide))
  -- `in n`, `out n`, `open n`
  all_goals try (
    cases argumentsTyped with
    | cons _ parameter nameTyped rest =>
        cases rest
        simp only [parameterType?, Option.some.injEq] at parameter
        subst parameter
        exact .inl ⟨by simp, _, rfl, nameTyped⟩)
  -- the empty path
  · cases argumentsTyped
    exact .inr (.inl ⟨rfl, rfl⟩)
  -- a path
  · cases argumentsTyped with
    | cons _ leftParameter leftTyped rest =>
        cases rest with
        | cons _ rightParameter rightTyped last =>
            cases last
            simp only [parameterType?, Option.some.injEq] at leftParameter rightParameter
            subst leftParameter rightParameter
            exact .inr (.inr ⟨rfl, _, _, rfl, leftTyped, rightTyped⟩)

/-- **A law relates processes**: the side a law reads is no capability term. -/
theorem shape_not_cap {free : FreeTypeContext} {bound : List TypeExpr} {source target : Pattern}
    (shape : AmbShape source target) (typed : HasType ambientCoreCalc free bound source capType) : False := by
  have capLabel : ∀ {label : String} {arguments : List Pattern},
      HasType ambientCoreCalc free bound (.apply label arguments) capType →
      label ∈ ["CapIn", "CapOut", "CapOpen", "CapEps", "CapPath"] := fun typed => by
    rcases cap_apply_inv typed with ⟨listed, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at listed ⊢
      rcases listed with rfl | rfl | rfl <;> simp
    · simp
    · simp
  have notBag : ∀ {elements : List Pattern} {rest : Option String},
      ¬ HasType ambientCoreCalc free bound (.collection .hashBag elements rest) capType := fun typed => by
    rcases hasType_collection_inversion typed with ⟨_, typeIs, _⟩ |
      ⟨rule, parameterName, elementType, member, collectionShape, typeIs, -⟩
    · cases typeIs
    simp only [ambientCoreCalc, terms, commTerms, prefixRule, capRule, List.cons_append,
      List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;> simp_all [GrammarRule.bareParams]
  cases shape with
  | law shape =>
      cases shape with
      | emptyUnit listed => simp at listed
      | _ => first | exact notBag typed | simpa using capLabel typed
  | boundary => simpa using capLabel typed
  | boundaryReverse => simpa using capLabel typed

/-- **A capability holds no term but capabilities and names**: a context filled to a typed object capability holds,
at its hole, a variable or a capability term. -/
theorem no_caps {free : FreeTypeContext} {bound : List TypeExpr} {inner : Pattern}
    (notVariable : (∀ index, inner ≠ .bvar index) ∧ ∀ name, inner ≠ .fvar name)
    (notCap : ¬ HasType ambientCoreCalc free bound inner capType) (context : OneHoleContext)
    (typed : HasType ambientCoreCalc free bound (context.fill inner) capType)
    (object : isObjectPattern (context.fill inner) = true) : False := by
  induction context with
  | hole => exact notCap typed
  | lambda binder inner' _ => cases typed
  | multiLambda arity binders inner' _ => cases typed
  | substBody inner' replacement _ => simp [OneHoleContext.fill, isObjectPattern] at object
  | substReplacement body inner' _ => simp [OneHoleContext.fill, isObjectPattern] at object
  | collection kind before inner' after rest _ =>
      simp only [OneHoleContext.fill] at typed
      rcases hasType_collection_inversion typed with ⟨_, typeIs, _⟩ |
        ⟨rule, parameterName, elementType, member, collectionShape, typeIs, -⟩
      · cases typeIs
      simp only [ambientCoreCalc, terms, commTerms, prefixRule, capRule, List.cons_append,
        List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;> simp_all [GrammarRule.bareParams]
  | apply label before inner' after recurse =>
      simp only [OneHoleContext.fill] at typed object
      have objects : ∀ element ∈ before ++ inner'.fill inner :: after, isObjectPattern element = true := by
        simpa [isObjectPattern, isObjectPatternList_iff] using object
      rcases cap_apply_inv typed with ⟨listed, name, same, nameTyped⟩ | ⟨rfl, same⟩ |
        ⟨rfl, left, right, same, leftTyped, rightTyped⟩
      · -- `in n`, `out n`, `open n`: the hole is at the name
        obtain ⟨rfl, rfl⟩ := positions_one (congrArg List.length same)
        simp only [List.nil_append, List.cons.injEq, and_true] at same
        subst same
        exact no_names notVariable inner' nameTyped (objects _ (by simp))
      · -- the empty path has no argument
        simp at same
      · -- a path: the hole is inside one of its capability terms
        rcases positions_two (congrArg List.length same) with ⟨rfl, last, rfl⟩ | ⟨first, rfl, rfl⟩
        · simp only [List.nil_append, List.cons.injEq] at same
          obtain ⟨rfl, -⟩ := same
          exact recurse leftTyped (objects _ (by simp))
        · simp only [List.singleton_append, List.cons.injEq] at same
          obtain ⟨-, rfl, -⟩ := same
          exact recurse rightTyped (objects _ (by simp))

/-- **No law applies inside a capability term**: two fillings of one context by the two sides of a law are not both
capability terms. A capability term holds only names and capability terms. -/
theorem not_caps {free : FreeTypeContext} {bound : List TypeExpr} {source target : Pattern}
    (shape : AmbShape source target ∨ AmbShape target source) (context : OneHoleContext)
    (sourceTyped : HasType ambientCoreCalc free bound (context.fill source) capType)
    (targetTyped : HasType ambientCoreCalc free bound (context.fill target) capType)
    (sourceObject : isObjectPattern (context.fill source) = true)
    (targetObject : isObjectPattern (context.fill target) = true) : False := by
  rcases shape with shape | shape
  · exact no_caps shape.notVariable (shape_not_cap shape) context sourceTyped sourceObject
  · exact no_caps shape.notVariable (shape_not_cap shape) context targetTyped targetObject

/-- **A law inside an abstracting argument is inside its body**: the argument is an abstraction, and no side of a law
is one. -/
theorem abstraction_context {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}
    {source : Pattern} (notLambda : ∀ binder body, source ≠ .lambda binder body) {inner : OneHoleContext}
    {others : List Pattern} {binderName : Option String} {bodyName : String} {type : TypeExpr}
    {rest : List TermParam}
    (typed : ArgumentsHaveTypes language free bound (inner.fill source :: others)
      (.abstractionNamed binderName bodyName type :: rest)) :
    ∃ binder body, inner = .lambda binder body := by
  cases typed with
  | cons representation _ _ _ =>
      obtain ⟨body, isLambda⟩ := (matchesParameterRepresentation_abstractionNamed_iff _ _ _ _).mp representation
      cases inner with
      | hole =>
          simp only [OneHoleContext.fill] at isLambda
          exact absurd isLambda (notLambda _ _)
      | lambda binder inner => exact ⟨binder, inner, rfl⟩
      | _ => simp [OneHoleContext.fill] at isLambda

/-- **The side of a law a context holds is no abstraction.** -/
theorem source_notLambda {source target : Pattern} (shape : AmbShape source target ∨ AmbShape target source) :
    ∀ binder body, source ≠ .lambda binder body := by
  rcases shape with shape | shape
  · exact shape.notLambda.1
  · exact shape.notLambda.2

/-- **The located form of an object process is an object**, at an object location. -/
theorem encode_object : ∀ (fuel : Nat) {relabel : Nat → Nat} {here process : Pattern}, size process < fuel →
    isObjectPattern here = true → isObjectPattern process = true → isObjectPattern (encode relabel here process) = true
  | 0, _, _, _, small, _, _ => absurd small (Nat.not_lt_zero _)
  | fuel + 1, relabel, here, process, small, hereObject, object => by
      have renamedBy : ∀ (relabel' : Nat → Nat) (pattern : Pattern), isObjectPattern pattern = true →
          isObjectPattern (rename relabel' pattern) = true := fun relabel' pattern isObject => by
        rw [Mettapedia.GSLT.LanguageDef.RestrictionBlocks.isObjectPattern_rename]; exact isObject
      have renamed := renamedBy relabel
      have shiftedObject : isObjectPattern (shiftName here) = true := by
        rw [shiftName, Mettapedia.GSLT.LanguageDef.RestrictionBlocks.isObjectPattern_rename]; exact hereObject
      cases process with
      | bvar index => exact renamed _ object
      | fvar name => exact renamed _ object
      | lambda binder body => exact renamed _ object
      | multiLambda arity binders body => exact renamed _ object
      | subst body replacement => simp [isObjectPattern] at object
      | collection kind elements rest =>
          cases kind with
          | hashBag =>
              rw [encode_bag]
              simp only [isObjectPattern, Bool.and_eq_true, isObjectPatternList_iff] at object ⊢
              refine ⟨object.1, fun element member => ?_⟩
              obtain ⟨original, inElements, rfl⟩ := List.mem_map.mp member
              have originalSmall : size original < fuel := by
                have := size_lt_of_mem' inElements
                simp only [size] at small
                omega
              exact encode_object fuel originalSmall hereObject (object.2 original inElements)
          | _ => exact renamed _ object
      | apply label arguments =>
          have objects : ∀ argument ∈ arguments, isObjectPattern argument = true := by
            simpa [isObjectPattern, isObjectPatternList_iff] using object
          have argumentSmall : ∀ argument ∈ arguments, size argument < fuel := by
            intro argument inArguments
            have := size_lt_of_mem' inArguments
            simp only [size] at small
            omega
          match arguments, objects, argumentSmall with
          | [], _, _ =>
              simp only [encode]
              split_ifs <;> rfl
          | [argument], objects, argumentSmall =>
              by_cases isLambda : ∃ binder body, argument = .lambda binder body
              · obtain ⟨binder, body, rfl⟩ := isLambda
                have bodySmall : size body < fuel := by
                  have := argumentSmall _ List.mem_cons_self
                  simp only [size] at this
                  omega
                have bodyObject : isObjectPattern body = true := by
                  simpa [isObjectPattern] using objects _ List.mem_cons_self
                have inner := encode_object fuel (relabel := liftIndex 1 relabel) bodySmall shiftedObject bodyObject
                rw [encode_single_lambda]
                split_ifs
                · simp only [isObjectPattern, isObjectPatternList, Bool.and_true]
                  exact inner
                · simp only [isObjectPattern, isObjectPatternList, Bool.and_true, Bool.and_eq_true]
                  exact ⟨hereObject, inner⟩
                · simp only [isObjectPattern, isObjectPatternList, Bool.and_true, Bool.and_eq_true]
                  exact ⟨hereObject, inner⟩
                · exact renamed _ object
              · push Not at isLambda
                rw [encode_single _ isLambda]
                split_ifs
                · simp only [isObjectPattern, isObjectPatternList, Bool.and_true]
                  exact encode_object fuel (argumentSmall _ List.mem_cons_self) hereObject
                    (objects _ List.mem_cons_self)
                · simp only [isObjectPattern, isObjectPatternList, Bool.and_true, Bool.and_eq_true]
                  exact ⟨hereObject, renamed _ (objects _ List.mem_cons_self)⟩
                · simp only [isObjectPattern, isObjectPatternList, Bool.and_true, Bool.and_eq_true]
                  exact ⟨hereObject, renamed _ (objects _ List.mem_cons_self)⟩
                · exact renamed _ object
          | [name, process], objects, argumentSmall =>
              have nameObject := objects _ List.mem_cons_self
              have processObject := objects _ (List.mem_cons_of_mem _ List.mem_cons_self)
              have processSmall := argumentSmall _ (List.mem_cons_of_mem _ List.mem_cons_self)
              rw [encode_pair]
              split_ifs
              · simp only [isObjectPattern, isObjectPatternList, Bool.and_true, Bool.and_eq_true,
                  Option.isNone_none, true_and]
                exact ⟨⟨shiftedObject, renamedBy _ _ nameObject⟩, encode_object fuel processSmall rfl processObject⟩
              all_goals first
                | exact renamed _ object
                | simp only [isObjectPattern, isObjectPatternList, Bool.and_true, Bool.and_eq_true]
                  exact ⟨hereObject, renamed _ nameObject, encode_object fuel processSmall hereObject processObject⟩
          | _ :: _ :: _ :: _, _, _ =>
              simp only [encode]
              exact renamed _ object

/-- The located form of an object process at the root is an object. -/
theorem located_object {process : Pattern} (object : isObjectPattern process = true) :
    isObjectPattern (located process) = true :=
  encode_object (size process + 1) (Nat.lt_succ_self _) rfl object

/-! ## A law in a context -/

/-- **A law anywhere inside a typed ambient process is a chain of laws inside its located form**, at the location
and under the binders the reading passes on its way to the law. -/
theorem located_fill {free : FreeTypeContext} (names : NameContext free) {source target : Pattern}
    (shape : AmbShape source target ∨ AmbShape target source) :
    ∀ (fuel : Nat) (context : OneHoleContext) {bound bound' : List TypeExpr} {relabel : Nat → Nat} {here : Pattern},
      size (context.fill source) < fuel → LocatedFrame bound bound' relabel →
      HasType locatedCalc free bound' here nameType → isObjectPattern here = true →
      HasType ambientCoreCalc free bound (context.fill source) procType →
      HasType ambientCoreCalc free bound (context.fill target) procType →
      isObjectPattern (context.fill source) = true → isObjectPattern (context.fill target) = true →
      ProcEquiv locatedCalc locatedBlock free bound'
        (encode relabel here (context.fill source)) (encode relabel here (context.fill target))
  | 0, _, _, _, _, _, small, _, _, _, _, _, _, _ => absurd small (Nat.not_lt_zero _)
  | fuel + 1, context, bound, bound', relabel, here, small, frame, hereTyped, hereObject, sourceTyped, targetTyped,
      sourceObject, targetObject => by
      have signature : BlockSignature locatedCalc locatedBlock := locatedLanguage.toBlockSignature
      have notLambda : ∀ {process : Pattern}, HasType ambientCoreCalc free bound process procType →
          ∀ binder body, process ≠ .lambda binder body := fun typed binder body same => by
        subst same; cases typed
      cases context with
      | hole =>
          simp only [OneHoleContext.fill] at sourceTyped targetTyped sourceObject targetObject ⊢
          rcases shape with shape | shape
          · exact encode_shape names frame hereTyped hereObject shape sourceTyped targetTyped sourceObject
              targetObject
          · exact Relation.EqvGen.symm _ _ (encode_shape names frame hereTyped hereObject shape targetTyped
              sourceTyped targetObject sourceObject)
      | lambda binder inner => cases sourceTyped
      | multiLambda arity binders inner => cases sourceTyped
      | substBody inner replacement => simp [OneHoleContext.fill, isObjectPattern] at sourceObject
      | substReplacement body inner => simp [OneHoleContext.fill, isObjectPattern] at sourceObject
      | collection kind before inner after rest =>
          simp only [OneHoleContext.fill] at small sourceTyped targetTyped sourceObject targetObject ⊢
          rcases hasType_collection_inversion sourceTyped with ⟨_, typeIs, _⟩ |
            ⟨rule, parameterName, elementType, member, collectionShape, typeIs, elementsTyped⟩
          · cases typeIs
          simp only [ambientCoreCalc, terms, commTerms, prefixRule, capRule, List.cons_append,
            List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl <;>
            simp [GrammarRule.bareParams] at collectionShape
          obtain ⟨rfl, rfl, rfl⟩ := collectionShape
          obtain rfl := tail_none sourceObject
          have sourceMembers := bag_inv sourceTyped
          have targetMembers := bag_inv targetTyped
          have sourceObjects : ∀ element ∈ before ++ inner.fill source :: after, isObjectPattern element = true := by
            simpa [isObjectPattern, isObjectPatternList_iff] using sourceObject
          have targetObjects : ∀ element ∈ before ++ inner.fill target :: after, isObjectPattern element = true := by
            simpa [isObjectPattern, isObjectPatternList_iff] using targetObject
          have innerSmall : size (inner.fill source) < fuel := by
            have := size_lt_of_mem' (element := inner.fill source) (elements := before ++ inner.fill source :: after)
              (by simp)
            simp only [size] at small
            omega
          have recurse := located_fill names shape fuel inner innerSmall frame hereTyped hereObject
            (sourceMembers _ (by simp)) (targetMembers _ (by simp)) (sourceObjects _ (by simp))
            (targetObjects _ (by simp))
          have beforeLocated := located_members names frame hereTyped hereObject (elements := before)
            (fun element member => sourceMembers element (by simp [member]))
            (fun element member => sourceObjects element (by simp [member]))
          have afterLocated := located_members names frame hereTyped hereObject (elements := after)
            (fun element member => sourceMembers element (by simp [member]))
            (fun element member => sourceObjects element (by simp [member]))
          rw [encode_bag, encode_bag, List.map_append, List.map_cons, List.map_append, List.map_cons]
          exact bag_fill (language := locatedCalc) (block := locatedBlock) beforeLocated afterLocated recurse
      | apply label before inner after =>
          simp only [OneHoleContext.fill] at small sourceTyped targetTyped sourceObject targetObject ⊢
          obtain ⟨rule, member, rfl, notBare, typeIs, argumentsTyped⟩ := hasType_apply_inversion sourceTyped
          have length := arguments_length argumentsTyped
          simp only [ambientCoreCalc, terms, commTerms, prefixRule, capRule, List.cons_append,
            List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl <;>
            simp only [procType, TypeExpr.base.injEq] at typeIs <;> try (exact absurd typeIs (by decide))
          · simp at length
          · exact absurd ⟨"ps", .hashBag, .base "Proc", rfl⟩ notBare
          · -- restriction: the law is in its body
            obtain ⟨rfl, rfl⟩ := positions_one length
            simp only [List.nil_append] at argumentsTyped
            obtain ⟨binder, body, rfl⟩ := abstraction_context (source_notLambda shape) argumentsTyped
            simp only [OneHoleContext.fill, List.nil_append] at small sourceTyped targetTyped
            simp only [OneHoleContext.fill, List.nil_append] at sourceObject targetObject ⊢
            obtain ⟨rfl, bodyTyped⟩ := nu_inv sourceTyped
            obtain ⟨-, targetBodyTyped⟩ := nu_inv targetTyped
            have bodySmall : size (body.fill source) < fuel := by
              simp only [size, sizeList] at small
              omega
            have recurse := located_fill names shape fuel body bodySmall (frame.lift (sort := nameType) (.inl rfl))
              (shiftName_sorted nameType hereTyped) (shiftName_object hereObject) bodyTyped targetBodyTyped
              (by simpa [isObjectPattern, isObjectPatternList] using sourceObject)
              (by simpa [isObjectPattern, isObjectPatternList] using targetObject)
            rw [encode_nu, encode_nu]
            exact restrict_fill (language := locatedCalc) (block := locatedBlock) recurse
          · -- replication
            obtain ⟨rfl, rfl⟩ := positions_one length
            simp only [List.nil_append] at small sourceTyped targetTyped sourceObject targetObject ⊢
            have innerTyped := rep_inv sourceTyped
            have targetInnerTyped := rep_inv targetTyped
            have innerSmall : size (inner.fill source) < fuel := by
              simp only [size, sizeList] at small
              omega
            have recurse := located_fill names shape fuel inner innerSmall frame hereTyped hereObject innerTyped
              targetInnerTyped (by simpa [isObjectPattern, isObjectPatternList] using sourceObject)
              (by simpa [isObjectPattern, isObjectPatternList] using targetObject)
            rw [encode_rep _ _ (notLambda innerTyped), encode_rep _ _ (notLambda targetInnerTyped)]
            exact replicate_fill (block := locatedRepBlock) recurse
          · -- an ambient
            rcases positions_two length with ⟨rfl, last, rfl⟩ | ⟨first, rfl, rfl⟩
            · -- its name
              obtain ⟨nameTyped, -⟩ := amb_inv sourceTyped
              obtain ⟨targetNameTyped, -⟩ := amb_inv targetTyped
              exact (not_names shape inner nameTyped targetNameTyped
                (by simp [isObjectPattern, isObjectPatternList] at sourceObject; exact sourceObject.1)
                (by simp [isObjectPattern, isObjectPatternList] at targetObject; exact targetObject.1)).elim
            · -- its content, read at the ambient's location
              simp only [List.singleton_append] at small sourceTyped targetTyped sourceObject targetObject ⊢
              obtain ⟨nameTyped, contentTyped⟩ := amb_inv sourceTyped
              obtain ⟨-, targetContentTyped⟩ := amb_inv targetTyped
              have nameObject : isObjectPattern first = true := by
                simp [isObjectPattern, isObjectPatternList] at sourceObject; exact sourceObject.1
              have locationTyped : HasType locatedCalc free (nameType :: bound') (.bvar 0) nameType :=
                .bvar (by simp)
              have contentSmall : size (inner.fill source) < fuel := by
                simp only [size, sizeList] at small
                omega
              have recurse := located_fill names shape fuel inner contentSmall frame.location locationTyped rfl
                contentTyped targetContentTyped
                (by simp [isObjectPattern, isObjectPatternList] at sourceObject; exact sourceObject.2)
                (by simp [isObjectPattern, isObjectPatternList] at targetObject; exact targetObject.2)
              have markerTyped := marker_typed (shiftName_sorted nameType hereTyped) locationTyped
                (rename_name_sorted frame.location.sorts nameTyped nameObject)
              rw [encode_amb, encode_amb]
              refine restrict_fill (language := locatedCalc) (block := locatedBlock) ?_
              exact bag_fill (language := locatedCalc) (block := locatedBlock) (rest := none)
                (before := [.apply "LAmb" [shiftName here, .bvar 0, rename (Nat.succ ∘ relabel) first]]) (after := [])
                (fun element member => by
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
                  subst member
                  exact markerTyped)
                (fun element member => by simp at member) recurse
          all_goals first
            | -- a prefix by a name, `in n.P`, `out n.P`, `open n.P`
              rcases positions_two length with ⟨rfl, last, rfl⟩ | ⟨first, rfl, rfl⟩
              · -- its name
                obtain ⟨nameTyped, -⟩ := prefix_inv (by simp) sourceTyped
                obtain ⟨targetNameTyped, -⟩ := prefix_inv (by simp) targetTyped
                exact (not_names shape inner nameTyped targetNameTyped
                  (by simp [isObjectPattern, isObjectPatternList] at sourceObject; exact sourceObject.1)
                  (by simp [isObjectPattern, isObjectPatternList] at targetObject; exact targetObject.1)).elim
              · -- its continuation
                simp only [List.singleton_append] at small sourceTyped targetTyped sourceObject targetObject ⊢
                obtain ⟨nameTyped, contentTyped⟩ := prefix_inv (by simp) sourceTyped
                obtain ⟨-, targetContentTyped⟩ := prefix_inv (by simp) targetTyped
                have nameObject : isObjectPattern first = true := by
                  simp [isObjectPattern, isObjectPatternList] at sourceObject; exact sourceObject.1
                have contentSmall : size (inner.fill source) < fuel := by
                  simp only [size, sizeList] at small
                  omega
                have recurse := located_fill names shape fuel inner contentSmall frame hereTyped hereObject
                  contentTyped targetContentTyped
                  (by simp [isObjectPattern, isObjectPatternList] at sourceObject; exact sourceObject.2)
                  (by simp [isObjectPattern, isObjectPatternList] at targetObject; exact targetObject.2)
                first
                  | rw [encode_in, encode_in]
                  | rw [encode_out, encode_out]
                  | rw [encode_open, encode_open]
                exact capability_fill (by simp) hereTyped (rename_name_sorted frame.sorts nameTyped nameObject)
                  recurse
            | -- a prefix by a capability term, `M.P`
              rcases positions_two length with ⟨rfl, last, rfl⟩ | ⟨first, rfl, rfl⟩
              · -- its capability term
                obtain ⟨capabilityTyped, -⟩ := acap_inv sourceTyped
                obtain ⟨targetCapabilityTyped, -⟩ := acap_inv targetTyped
                exact (not_caps shape inner capabilityTyped targetCapabilityTyped
                  (by simp [isObjectPattern, isObjectPatternList] at sourceObject; exact sourceObject.1)
                  (by simp [isObjectPattern, isObjectPatternList] at targetObject; exact targetObject.1)).elim
              · -- its continuation
                simp only [List.singleton_append] at small sourceTyped targetTyped sourceObject targetObject ⊢
                obtain ⟨capabilityTyped, contentTyped⟩ := acap_inv sourceTyped
                obtain ⟨-, targetContentTyped⟩ := acap_inv targetTyped
                have capabilityObject : isObjectPattern first = true := by
                  simp [isObjectPattern, isObjectPatternList] at sourceObject; exact sourceObject.1
                have contentSmall : size (inner.fill source) < fuel := by
                  simp only [size, sizeList] at small
                  omega
                have recurse := located_fill names shape fuel inner contentSmall frame hereTyped hereObject
                  contentTyped targetContentTyped
                  (by simp [isObjectPattern, isObjectPatternList] at sourceObject; exact sourceObject.2)
                  (by simp [isObjectPattern, isObjectPatternList] at targetObject; exact targetObject.2)
                rw [encode_cap, encode_cap]
                exact lcap_fill hereTyped (rename_cap_typed names (size first + 1) (Nat.lt_succ_self _) frame.sorts
                  capabilityTyped capabilityObject) recurse
            | -- the input of a name: the law is in its body, under the binder of a name
              obtain ⟨rfl, rfl⟩ := positions_one length
              simp only [List.nil_append] at argumentsTyped
              obtain ⟨binder, body, rfl⟩ := abstraction_context (source_notLambda shape) argumentsTyped
              simp only [OneHoleContext.fill, List.nil_append] at small sourceTyped targetTyped
              simp only [OneHoleContext.fill, List.nil_append] at sourceObject targetObject ⊢
              obtain ⟨rfl, bodyTyped⟩ := input_inv (sort := "Name") List.mem_cons_self sourceTyped
              obtain ⟨-, targetBodyTyped⟩ := input_inv (sort := "Name") List.mem_cons_self targetTyped
              have bodySmall : size (body.fill source) < fuel := by
                simp only [size, sizeList] at small
                omega
              have recurse := located_fill names shape fuel body bodySmall (frame.lift (sort := nameType) (.inl rfl))
                (shiftName_sorted nameType hereTyped) (shiftName_object hereObject) bodyTyped targetBodyTyped
                (by simpa [isObjectPattern, isObjectPatternList] using sourceObject)
                (by simpa [isObjectPattern, isObjectPatternList] using targetObject)
              rw [encode_inName, encode_inName]
              exact linput_fill (sort := "Name") (by simp) hereTyped recurse
            | -- the input of a capability: the law is in its body, under the binder of a capability
              obtain ⟨rfl, rfl⟩ := positions_one length
              simp only [List.nil_append] at argumentsTyped
              obtain ⟨binder, body, rfl⟩ := abstraction_context (source_notLambda shape) argumentsTyped
              simp only [OneHoleContext.fill, List.nil_append] at small sourceTyped targetTyped
              simp only [OneHoleContext.fill, List.nil_append] at sourceObject targetObject ⊢
              obtain ⟨rfl, bodyTyped⟩ :=
                input_inv (sort := "Cap") (List.mem_cons_of_mem _ List.mem_cons_self) sourceTyped
              obtain ⟨-, targetBodyTyped⟩ :=
                input_inv (sort := "Cap") (List.mem_cons_of_mem _ List.mem_cons_self) targetTyped
              have bodySmall : size (body.fill source) < fuel := by
                simp only [size, sizeList] at small
                omega
              have recurse := located_fill names shape fuel body bodySmall (frame.lift (sort := capType) (.inr rfl))
                (shiftName_sorted capType hereTyped) (shiftName_object hereObject) bodyTyped targetBodyTyped
                (by simpa [isObjectPattern, isObjectPatternList] using sourceObject)
                (by simpa [isObjectPattern, isObjectPatternList] using targetObject)
              rw [encode_inCap, encode_inCap]
              exact linput_fill (sort := "Cap") (by simp) hereTyped recurse
            | -- an output: its message is a name or a capability term, inside which no law applies
              obtain ⟨rfl, rfl⟩ := positions_one length
              simp only [List.nil_append] at sourceTyped targetTyped sourceObject targetObject
              have messageObject : isObjectPattern (inner.fill source) = true := by
                simpa [isObjectPattern, isObjectPatternList] using sourceObject
              have targetMessageObject : isObjectPattern (inner.fill target) = true := by
                simpa [isObjectPattern, isObjectPatternList] using targetObject
              first
                | exact (not_names shape inner (output_inv (sort := "Name") List.mem_cons_self sourceTyped)
                    (output_inv (sort := "Name") List.mem_cons_self targetTyped) messageObject targetMessageObject).elim
                | exact (not_caps shape inner (output_inv (sort := "Cap")
                    (List.mem_cons_of_mem _ List.mem_cons_self) sourceTyped)
                    (output_inv (sort := "Cap")
                    (List.mem_cons_of_mem _ List.mem_cons_self) targetTyped) messageObject targetMessageObject).elim

/-! ## Steps and chains -/

/-- **A step of the static theory between typed ambient processes relates their located forms.** -/
theorem located_step {free : FreeTypeContext} (names : NameContext free) {base : BasePremiseEvaluator}
    {bound bound' : List TypeExpr} {relabel : Nat → Nat} {here first second : Pattern}
    (frame : LocatedFrame bound bound' relabel) (hereTyped : HasType locatedCalc free bound' here nameType)
    (hereObject : isObjectPattern here = true) (step : EquationContextStep base ambientCoreCalc first second)
    (firstTyped : HasType ambientCoreCalc free bound first procType)
    (secondTyped : HasType ambientCoreCalc free bound second procType)
    (firstObject : isObjectPattern first = true) (secondObject : isObjectPattern second = true) :
    ProcEquiv locatedCalc locatedBlock free bound' (encode relabel here first) (encode relabel here second) := by
  obtain ⟨context, generator⟩ := step
  exact located_fill names (ambient_generator_shape generator) _ context (Nat.lt_succ_self _) frame hereTyped
    hereObject firstTyped secondTyped firstObject secondObject

/-- **A chain of laws through typed ambient object processes relates their located forms.** -/
theorem located_chain {free : FreeTypeContext} (names : NameContext free) {bound bound' : List TypeExpr}
    {relabel : Nat → Nat} {here first second : Pattern} (frame : LocatedFrame bound bound' relabel)
    (hereTyped : HasType locatedCalc free bound' here nameType) (hereObject : isObjectPattern here = true)
    (chain : ObjectChain ambientCoreCalc free bound procType first second) :
    ProcEquiv locatedCalc locatedBlock free bound' (encode relabel here first) (encode relabel here second) := by
  induction chain with
  | rel first second step =>
      obtain ⟨step, firstObject, secondObject⟩ := step
      exact located_step names frame hereTyped hereObject step.step step.firstTyped step.secondTyped firstObject
        secondObject
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ recurse => exact Relation.EqvGen.symm _ _ recurse
  | trans _ _ _ _ _ left right => exact Relation.EqvGen.trans _ _ _ left right

end Mettapedia.Languages.ProcessCalculi.Ambient.Encoding
