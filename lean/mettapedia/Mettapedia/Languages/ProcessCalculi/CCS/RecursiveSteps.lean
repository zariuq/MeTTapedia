import Mettapedia.Languages.ProcessCalculi.CCS.RecursiveReflection
import Mettapedia.Languages.ProcessCalculi.CCS.Steps
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.DecomposeSubstitution

/-!
# Steps of CCS with recursion through the canonical form

A step of CCS with recursion is a reaction (`recReactions`): of two components standing side by side, one offering an
action and the other the co-action on its name, both leave their continuations; a component offering a silent guard
leaves its continuation. A component offers guards when it is a sum, its summands, or a call, the summands of its
body (`Offer`).

A call is an atom of a block and its own canonical form (`canon_call`), so it offers the same guards at the canonical
form; a canonical sum offers the canonical forms of its summands. The calls of admitted definitions commute with
renaming (`offers_rename`), and what a call's body offers uses only the call's names (`freeIn_offered`). A step
therefore reaches a block with a redex at its front (`step_block`), and the canonical form steps too, to a contractum
with the same canonical form (`simulation`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.CCS.Recursive

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Prenex
open Mettapedia.Languages.ProcessCalculi.CCS
open Mettapedia.Languages.ProcessCalculi.CCS.Blocks (ccsBlock)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (FreeIn freeIn_apply freeIn_collection)
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationEquiv DerivedInstance derivedInstance_equivalent)
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (engineBasePremises)
open Mettapedia.GSLT.LanguageDef.BagNormalForm (elementsHaveType_iff isObjectPatternList_iff)
open Mettapedia.OSLF.MeTTaIL.ContextSubstitution (substitute)

/-! ## Typing -/

/-- **The summands of a typed sum are guards.** -/
theorem sum_guards {free : FreeTypeContext} {bound : List TypeExpr} {guards : List Pattern} {tail : Option String}
    (typed : HasType ccsRecCalc free bound (.apply "CSum" [.collection .hashBag guards tail]) (.base "Proc")) :
    ∀ guard ∈ guards, HasType ccsRecCalc free bound guard (.base "Guard") := by
  obtain ⟨rule, member, labelIs, -, -, parameterName, elementSort, argument, params, -, argumentsIs, argumentTyped⟩ :=
    multiset_argument (block := ccsBlock) typed (by simp)
  have sortIs : elementSort = "Guard" := by
    simp only [ccsRecCalc, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all [ccsCalc, callRule, constZeroRule, constSuccRule, argumentsNilRule, argumentsConsRule, TypeExpr.bag]
  subst sortIs
  simp only [List.cons.injEq, and_true] at argumentsIs
  subst argumentsIs
  rcases hasType_collection_inversion argumentTyped with ⟨elementType, typeIs, elementsTyped⟩ |
    ⟨rule', -, -, -, -, typeIs, -⟩
  · simp only [TypeExpr.collection.injEq, true_and] at typeIs
    subst typeIs
    exact elementsHaveType_iff.mp elementsTyped
  · cases typeIs

/-- **A typed prefix** carries a name and a process. -/
theorem prefix_parts {free : FreeTypeContext} {bound : List TypeExpr} {label : String} {name continuation : Pattern}
    (isPrefix : label = "CAct" ∨ label = "CCoAct")
    (typed : HasType ccsRecCalc free bound (.apply label [name, continuation]) (.base "Guard")) :
    HasType ccsRecCalc free bound name (.base "Name") ∧ HasType ccsRecCalc free bound continuation (.base "Proc") := by
  obtain ⟨rule, member, labelIs, -, -, arguments⟩ := hasType_apply_inversion typed
  simp only [ccsRecCalc, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases isPrefix with rfl | rfl <;>
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [ccsCalc, callRule, constZeroRule, constSuccRule, argumentsNilRule, argumentsConsRule] at labelIs <;>
    · cases arguments with
      | cons _ nameType nameTyped rest =>
          cases rest with
          | cons _ continuationType continuationTyped _ =>
              simp only [parameterType?, Option.some.injEq] at nameType continuationType
              subst nameType continuationType
              exact ⟨nameTyped, continuationTyped⟩

/-- **A typed silent prefix** carries a process. -/
theorem tau_part {free : FreeTypeContext} {bound : List TypeExpr} {continuation : Pattern}
    (typed : HasType ccsRecCalc free bound (tau continuation) (.base "Guard")) :
    HasType ccsRecCalc free bound continuation (.base "Proc") := by
  obtain ⟨rule, member, labelIs, -, -, arguments⟩ := hasType_apply_inversion typed
  simp only [ccsRecCalc, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [ccsCalc, callRule, constZeroRule, constSuccRule, argumentsNilRule, argumentsConsRule] at labelIs
  cases arguments with
  | cons _ continuationType continuationTyped _ =>
      simp only [parameterType?, Option.some.injEq] at continuationType
      subst continuationType
      exact continuationTyped

/-- **The arguments of a typed call** are a typed list of arguments. -/
theorem call_arguments {free : FreeTypeContext} {bound : List TypeExpr} {name args : Pattern}
    (typed : HasType ccsRecCalc free bound (.apply "CCall" [name, args]) (.base "Proc")) :
    HasType ccsRecCalc free bound args (.base "Args") := by
  obtain ⟨rule, member, labelIs, -, -, arguments⟩ := hasType_apply_inversion typed
  simp only [ccsRecCalc, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [ccsCalc, callRule, constZeroRule, constSuccRule, argumentsNilRule, argumentsConsRule] at labelIs
  cases arguments with
  | cons _ _ _ rest =>
      cases rest with
      | cons _ argsType argsTyped _ =>
          simp only [parameterType?, Option.some.injEq] at argsType
          subst argsType
          exact argsTyped

/-- **The members of a typed list of arguments are names.** -/
theorem arguments_names {free : FreeTypeContext} {bound : List TypeExpr} :
    ∀ {names : List Pattern}, HasType ccsRecCalc free bound (arguments names) (.base "Args") →
      ∀ name ∈ names, HasType ccsRecCalc free bound name (.base "Name")
  | [], _ => by simp
  | first :: others, typed => by
      obtain ⟨rule, member, labelIs, -, -, argumentsTyped⟩ := hasType_apply_inversion typed
      simp only [ccsRecCalc, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [ccsCalc, callRule, constZeroRule, constSuccRule, argumentsNilRule, argumentsConsRule]
          at labelIs
      cases argumentsTyped with
      | cons _ firstType firstTyped rest =>
          cases rest with
          | cons _ restType restTyped _ =>
              simp only [parameterType?, Option.some.injEq] at firstType restType
              subst firstType restType
              intro name member'
              rcases List.mem_cons.mp member' with rfl | inOthers
              · exact firstTyped
              · exact arguments_names restTyped name inOthers

theorem arguments_objects : ∀ {names : List Pattern}, isObjectPattern (arguments names) = true →
    ∀ name ∈ names, isObjectPattern name = true
  | [], _ => by simp
  | first :: others, object => by
      simp only [arguments, isObjectPattern, isObjectPatternList, Bool.and_true, Bool.and_eq_true] at object
      intro name member
      rcases List.mem_cons.mp member with rfl | inOthers
      · exact object.1
      · exact arguments_objects object.2 name inOthers

/-- **A typed name object is a variable**: no constructor makes names. -/
theorem name_variable {free : FreeTypeContext} {bound : List TypeExpr} {name : Pattern}
    (typed : HasType ccsRecCalc free bound name (.base "Name")) (object : isObjectPattern name = true) :
    (∃ index, name = .bvar index) ∨ ∃ held, name = .fvar held := by
  cases name with
  | bvar index => exact .inl ⟨index, rfl⟩
  | fvar held => exact .inr ⟨held, rfl⟩
  | apply label args =>
      obtain ⟨rule, member, -, -, typeIs, -⟩ := hasType_apply_inversion typed
      simp only [ccsRecCalc, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [ccsCalc, callRule, constZeroRule, constSuccRule, argumentsNilRule, argumentsConsRule] at typeIs
  | lambda => cases typed
  | multiLambda => cases typed
  | subst => simp [isObjectPattern] at object
  | collection kind elements rest =>
      rcases hasType_collection_inversion typed with ⟨_, typeIs, _⟩ | ⟨rule, _, _, member, _, typeIs, _⟩
      · cases typeIs
      · simp only [ccsRecCalc, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [ccsCalc, callRule, constZeroRule, constSuccRule, argumentsNilRule, argumentsConsRule] at typeIs

/-! ## What a component offers -/

theorem body_some {definitions : List Definition} {name args : Pattern} {guards : List Pattern}
    (found : body definitions name args = some guards) :
    ∃ definition names, lookup definitions name = some definition ∧
      argumentsOf definition.arity args = some names ∧ guards = definition.instantiate names := by
  simp only [body, Option.bind_eq_some_iff, Option.map_eq_some_iff] at found
  obtain ⟨definition, found, names, namesFound, rfl⟩ := found
  exact ⟨definition, names, found, namesFound, rfl⟩

theorem lookup_constant {definitions : List Definition} {name : Pattern} {definition : Definition}
    (found : lookup definitions name = some definition) : ∃ index, name = constant index := by
  unfold lookup at found
  obtain ⟨index, indexFound, -⟩ := Option.bind_eq_some_iff.mp found
  have holds := List.find?_some indexFound
  exact ⟨index, (beq_iff_eq.mp holds).symm⟩

/-- **What a typed object component offers are typed object guards.** -/
theorem offers_typed {definitions : List Definition} (admitted : admits definitions = true) {free : FreeTypeContext}
    {bound : List TypeExpr} {component : Pattern} {guards : List Pattern}
    (typed : HasType ccsRecCalc free bound component (.base "Proc")) (object : isObjectPattern component = true)
    (offered : offers definitions component = some guards) :
    ∀ guard ∈ guards, HasType ccsRecCalc free bound guard (.base "Guard") ∧ isObjectPattern guard = true := by
  rcases offers_cases offered with ⟨tail, rfl⟩ | ⟨name, args, rfl, found⟩
  · cases bag_tail_none (kind := .hashBag) (elements := guards) (tail := tail)
      (by simpa [isObjectPattern, isObjectPatternList] using object)
    intro guard member
    exact ⟨sum_guards typed guard member, Steps.object_of_sum object guard member⟩
  · obtain ⟨definition, names, lookupFound, namesFound, rfl⟩ := body_some found
    obtain ⟨rfl, length⟩ := arguments_of_argumentsOf namesFound
    have argsObject : isObjectPattern (arguments names) = true := by
      simp only [isObjectPattern, isObjectPatternList, Bool.and_true, Bool.and_eq_true] at object
      exact object.2
    intro guard member
    exact ⟨instantiate_typed admitted (lookup_mem lookupFound) length
        (arguments_names (call_arguments typed)) guard member,
      instantiate_objects admitted (lookup_mem lookupFound) (arguments_objects argsObject) guard member⟩

/-- A typing derivation bounds the free indices. -/
theorem freeIn_lt {depth index : Nat} {pattern : Pattern} (wellScoped : pattern.isWellScopedAt depth = true)
    (free : FreeIn index pattern) : index < depth := by
  induction free generalizing depth with
  | bvar => simpa [Pattern.isWellScopedAt] using wellScoped
  | @apply index label arguments argument member _ recurse =>
      apply recurse
      simp only [Pattern.isWellScopedAt] at wellScoped
      induction arguments with
      | nil => cases member
      | cons first others inner =>
          simp only [Pattern.isWellScopedListAt, Bool.and_eq_true] at wellScoped
          rcases List.mem_cons.mp member with rfl | inOthers
          · exact wellScoped.1
          · exact inner inOthers wellScoped.2
  | lambda _ recurse => exact Nat.lt_of_succ_lt_succ (recurse (by simpa [Pattern.isWellScopedAt] using wellScoped))
  | @multiLambda index arity _ _ _ recurse =>
      have := recurse (depth := depth + arity) (by simpa [Pattern.isWellScopedAt] using wellScoped)
      omega
  | substBody _ recurse =>
      simp only [Pattern.isWellScopedAt, Bool.and_eq_true] at wellScoped
      exact Nat.lt_of_succ_lt_succ (recurse wellScoped.1)
  | substReplacement _ recurse =>
      simp only [Pattern.isWellScopedAt, Bool.and_eq_true] at wellScoped
      exact recurse wellScoped.2
  | @element index kind elements element rest member _ recurse =>
      apply recurse
      simp only [Pattern.isWellScopedAt] at wellScoped
      induction elements with
      | nil => cases member
      | cons first others inner =>
          simp only [Pattern.isWellScopedListAt, Bool.and_eq_true] at wellScoped
          rcases List.mem_cons.mp member with rfl | inOthers
          · exact wellScoped.1
          · exact inner inOthers wellScoped.2

/-- The free indices of a summand of an admitted definition are its parameters. -/
theorem guard_freeIn {definitions : List Definition} (admitted : admits definitions = true)
    {definition : Definition} (member : definition ∈ definitions) {guard : Pattern}
    (guardMember : guard ∈ definition.guards) {index : Nat} (free : FreeIn index guard) : index < definition.arity := by
  have wellScoped := (guard_admitted admitted member guardMember).1.isWellScopedAt
  simp only [List.length_replicate] at wellScoped
  exact freeIn_lt wellScoped free

theorem rename_constant (relabel : Nat → Nat) : ∀ index : Nat, rename relabel (constant index) = constant index
  | 0 => by simp [constant, rename_apply]
  | index + 1 => by simp [constant, rename_apply, rename_constant relabel index]

theorem rename_arguments (relabel : Nat → Nat) : ∀ names : List Pattern,
    rename relabel (arguments names) = arguments (names.map (rename relabel))
  | [] => by simp [arguments, rename_apply]
  | name :: names => by simp [arguments, rename_apply, rename_arguments relabel names]

/-- **Instantiating a definition commutes with renaming its arguments.** -/
theorem instantiate_rename {definitions : List Definition} (admitted : admits definitions = true)
    {definition : Definition} (member : definition ∈ definitions) (relabel : Nat → Nat) {names : List Pattern}
    (length : names.length = definition.arity) :
    definition.instantiate (names.map (rename relabel)) = (definition.instantiate names).map (rename relabel) := by
  simp only [Definition.instantiate, List.map_map]
  apply List.map_congr_left
  intro guard guardMember
  simp only [Function.comp_apply, rename_substitute]
  apply substitute_congr_free
  intro index free
  have inRange := guard_freeIn admitted member guardMember free
  have present : index < names.length := length ▸ inRange
  simp [argumentAssignment, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem present]

/-- **The calls of admitted definitions commute with renaming**: a renamed component offers the renamed guards. -/
theorem offers_rename {definitions : List Definition} (admitted : admits definitions = true) (relabel : Nat → Nat)
    {component : Pattern} {guards : List Pattern} (offered : offers definitions component = some guards) :
    offers definitions (rename relabel component) = some (guards.map (rename relabel)) := by
  rcases offers_cases offered with ⟨tail, rfl⟩ | ⟨name, args, rfl, found⟩
  · simp [rename_apply, rename_collection, offers]
  · obtain ⟨definition, names, lookupFound, namesFound, rfl⟩ := body_some found
    obtain ⟨rfl, length⟩ := arguments_of_argumentsOf namesFound
    obtain ⟨index, rfl⟩ := lookup_constant lookupFound
    rw [rename_apply]
    simp only [List.map_cons, List.map_nil, rename_constant, rename_arguments, offers, body, lookupFound,
      Option.bind_some]
    rw [show definition.arity = (names.map (rename relabel)).length by simp [length], argumentsOf_arguments]
    simp [instantiate_rename admitted (lookup_mem lookupFound) relabel length]

/-- **What a component offers uses only the component's named.** -/
theorem freeIn_offered {definitions : List Definition} (admitted : admits definitions = true) {component : Pattern}
    {guards : List Pattern} (offered : offers definitions component = some guards) {guard : Pattern}
    (member : guard ∈ guards) {index : Nat} (free : FreeIn index guard) : FreeIn index component := by
  rcases offers_cases offered with ⟨tail, rfl⟩ | ⟨name, args, rfl, found⟩
  · exact freeIn_apply.mpr ⟨.collection .hashBag guards tail, by simp, freeIn_collection.mpr ⟨guard, member, free⟩⟩
  · obtain ⟨definition, names, lookupFound, namesFound, rfl⟩ := body_some found
    obtain ⟨rfl, length⟩ := arguments_of_argumentsOf namesFound
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨parameter, parameterFree, imageFree⟩ := freeIn_substitute original free
    have inRange := guard_freeIn admitted (lookup_mem lookupFound) originalMember parameterFree
    have present : parameter < names.length := length ▸ inRange
    simp only [argumentAssignment, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem present,
      Option.getD_some] at imageFree
    refine freeIn_apply.mpr ⟨arguments names, by simp, ?_⟩
    have inArguments : ∀ (names : List Pattern) (position : Nat) (inside : position < names.length),
        FreeIn index names[position] → FreeIn index (arguments names) := by
      intro names
      induction names with
      | nil => intro position inside; simp at inside
      | cons first others inner =>
          intro position inside freeAt
          cases position with
          | zero => exact freeIn_apply.mpr ⟨first, by simp, freeAt⟩
          | succ position =>
              exact freeIn_apply.mpr ⟨arguments others, by simp,
                inner position (by simpa using inside) freeAt⟩
    exact inArguments names parameter present imageFree

/-! ## Canonical calls -/

/-- A numeral is its own block. -/
theorem constant_atom (index : Nat) : decompose ccsBlock (constant index) = Prenex.atom (constant index) := by
  cases index <;>
    exact decompose_atom (by simp [constant]) (by simp [constant]) (by simp [constant])
      (by intro label argument equal; cases equal <;> decide)

theorem canonArgument_constant (canonical : Pattern → Pattern) (index : Nat) :
    canonArgument canonical (constant index) = canonical (constant index) := by
  cases index <;> rfl

/-- **A numeral is its own canonical form.** -/
theorem canonComponentWith_constant : ∀ (fuel index : Nat),
    canonComponentWith ccsBlock fuel (constant index) = constant index
  | 0, _ => rfl
  | _ + 1, 0 => by simp [constant, canonComponentWith]
  | fuel + 1, index + 1 => by
      simp only [constant, canonComponentWith, List.mem_singleton, List.map_cons, List.map_nil]
      rw [if_neg (by decide : ¬ ("CS" = "CSum"))]
      congr 2
      rw [canonArgument_constant]
      cases fuel with
      | zero => rfl
      | succ fuel =>
          rw [canonWith_atom fuel (constant_atom index)]
          exact canonComponentWith_constant fuel index

/-- A typed name object is its own canonical argument. -/
theorem argumentCanon_name {free : FreeTypeContext} {bound : List TypeExpr} {name : Pattern}
    (typed : HasType ccsRecCalc free bound name (.base "Name")) (object : isObjectPattern name = true) (fuel : Nat) :
    Steps.argumentCanon fuel name = name := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      rcases name_variable typed object with ⟨index, rfl⟩ | ⟨held, rfl⟩ <;> rfl

theorem canonComponentWith_arguments : ∀ {names : List Pattern}, (∀ name ∈ names,
    (∃ index, name = .bvar index) ∨ ∃ held, name = .fvar held) →
      ∀ fuel, canonComponentWith ccsBlock fuel (arguments names) = arguments names
  | [], _, 0 => rfl
  | [], _, _ + 1 => by simp [arguments, canonComponentWith]
  | _ :: _, _, 0 => rfl
  | first :: others, named, fuel + 1 => by
      simp only [arguments, canonComponentWith, List.mem_singleton, List.map_cons, List.map_nil]
      rw [if_neg (by decide : ¬ ("CArgCons" = "CSum"))]
      have firstCanon : canonArgument (canonWith ccsBlock fuel) first = first := by
        rcases named first (by simp) with ⟨index, rfl⟩ | ⟨held, rfl⟩ <;> rfl
      have othersCanon : canonArgument (canonWith ccsBlock fuel) (arguments others) = arguments others := by
        have shape : canonArgument (canonWith ccsBlock fuel) (arguments others) =
            canonWith ccsBlock fuel (arguments others) := by
          cases others <;> rfl
        rw [shape]
        cases fuel with
        | zero => rfl
        | succ fuel =>
            rw [canonWith_atom fuel (by
              cases others <;>
                exact decompose_atom (by simp [arguments]) (by simp [arguments]) (by simp [arguments])
                  (by intro label argument equal; cases equal))]
            exact canonComponentWith_arguments (fun name member => named name (by simp [member])) fuel
      rw [firstCanon, othersCanon]

/-- **A call is its own canonical form.** -/
theorem canon_call {free : FreeTypeContext} {bound : List TypeExpr} {index : Nat} {names : List Pattern}
    (typed : HasType ccsRecCalc free bound (.apply "CCall" [constant index, arguments names]) (.base "Proc"))
    (object : isObjectPattern (.apply "CCall" [constant index, arguments names]) = true) (fuel : Nat) :
    canonComponentWith ccsBlock fuel (.apply "CCall" [constant index, arguments names]) =
      .apply "CCall" [constant index, arguments names] := by
  have argsObject : isObjectPattern (arguments names) = true := by
    simp only [isObjectPattern, isObjectPatternList, Bool.and_true, Bool.and_eq_true] at object
    exact object.2
  have named : ∀ name ∈ names, (∃ index, name = .bvar index) ∨ ∃ held, name = .fvar held := fun name member =>
    name_variable (arguments_names (call_arguments typed) name member) (arguments_objects argsObject name member)
  cases fuel with
  | zero => rfl
  | succ fuel =>
      simp only [canonComponentWith, List.mem_singleton, List.map_cons, List.map_nil]
      rw [if_neg (by decide : ¬ ("CCall" = "CSum")), canonArgument_constant]
      have argsShape : canonArgument (canonWith ccsBlock fuel) (arguments names) =
          canonWith ccsBlock fuel (arguments names) := by
        cases names <;> rfl
      rw [argsShape]
      cases fuel with
      | zero => rfl
      | succ fuel =>
          rw [canonWith_atom fuel (constant_atom index), canonComponentWith_constant,
            canonWith_atom fuel (by
              cases names <;>
                exact decompose_atom (by simp [arguments]) (by simp [arguments]) (by simp [arguments])
                  (by intro label argument equal; cases equal)),
            canonComponentWith_arguments named]

/-- **The canonical form of a typed sum** is the sum of its canonical summands. -/
theorem canon_sum {free : FreeTypeContext} {bound : List TypeExpr} (fuel : Nat) {guards : List Pattern}
    (typed : HasType ccsRecCalc free bound (sum guards) (.base "Proc")) :
    canonComponentWith ccsBlock (fuel + 1) (sum guards) = sum (Steps.guardsCanon fuel guards) := by
  cases fuel with
  | zero => simp [canonComponentWith, sum, Steps.guardsCanon, canonMultisetWith]
  | succ fuel =>
      simp only [sum, canonComponentWith, List.mem_singleton, ↓reduceIte, List.map_cons,
        List.map_nil, Steps.guardsCanon]
      rw [canonMultisetWith_atoms fuel fun guard member =>
        decompose_other (sum_guards typed guard member) (by decide)]

theorem argumentCanon_equivalent {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound)
    (fuel : Nat) {argument : Pattern} {sort : String} (typed : HasType ccsRecCalc free bound argument (.base sort)) :
    EquationEquiv (engineBasePremises RelationEnv.empty) ccsRecCalc (Steps.argumentCanon fuel argument) argument := by
  cases fuel with
  | zero => exact .refl _
  | succ fuel => exact canonArgument_equivalent (block := ccsBlock) context fuel typed

/-! ## Offers and redexes -/

variable {definitions : List Definition}

/-- **A component offering a guard**: the component, the guards it offers, and the position of the one taken. -/
structure Offer (definitions : List Definition) where
  component : Pattern
  guards : List Pattern
  offered : offers definitions component = some guards
  position : Nat
  inside : position < guards.length

/-- The guard taken. -/
def Offer.guard (offer : Offer definitions) : Pattern := offer.guards[offer.position]'offer.inside

theorem Offer.guard_mem (offer : Offer definitions) : offer.guard ∈ offer.guards := List.getElem_mem _

/-- Rename an offer's variables. -/
def Offer.rename (admitted : admits definitions = true) (relabel : Nat → Nat) (offer : Offer definitions) :
    Offer definitions :=
  ⟨Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename relabel offer.component, offer.guards.map (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename relabel),
    offers_rename admitted relabel offer.offered, offer.position, by simpa using offer.inside⟩

theorem Offer.rename_guard (admitted : admits definitions = true) (relabel : Nat → Nat) (offer : Offer definitions) :
    (offer.rename admitted relabel).guard = Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename relabel offer.guard := by
  simp [Offer.guard, Offer.rename]

/-- **A redex of CCS with recursion**: an action and the co-action on its name, offered by two components; or a
silent guard offered by one. -/
inductive Redex (definitions : List Definition) where
  | react (first second : Offer definitions) (name continuation continuation' : Pattern)
      (acting : first.guard = .apply "CAct" [name, continuation])
      (coacting : second.guard = .apply "CCoAct" [name, continuation'])
  | silent (offer : Offer definitions) (continuation : Pattern) (taken : offer.guard = .apply "CTau" [continuation])

namespace Redex

/-- The components that react. -/
def parts : Redex definitions → List Pattern
  | react first second _ _ _ _ _ => [first.component, second.component]
  | silent offer _ _ => [offer.component]

/-- The continuations they release. -/
def result : Redex definitions → List Pattern
  | react _ _ _ continuation continuation' _ _ => [continuation, continuation']
  | silent _ continuation _ => [continuation]

/-- Rename a redex's variables. -/
def rename (admitted : admits definitions = true) (relabel : Nat → Nat) : Redex definitions → Redex definitions
  | react first second name continuation continuation' acting coacting =>
      react (first.rename admitted relabel) (second.rename admitted relabel)
        (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename relabel name) (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename relabel continuation)
        (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename relabel continuation')
        (by rw [Offer.rename_guard, acting, rename_apply]; rfl)
        (by rw [Offer.rename_guard, coacting, rename_apply]; rfl)
  | silent offer continuation taken =>
      silent (offer.rename admitted relabel) (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename relabel continuation)
        (by rw [Offer.rename_guard, taken, rename_apply]; rfl)

theorem parts_rename (admitted : admits definitions = true) (relabel : Nat → Nat) (redex : Redex definitions) :
    (redex.rename admitted relabel).parts = redex.parts.map (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename relabel) := by
  cases redex <;> rfl

theorem result_rename (admitted : admits definitions = true) (relabel : Nat → Nat) (redex : Redex definitions) :
    (redex.rename admitted relabel).result = redex.result.map (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename relabel) := by
  cases redex <;> rfl

end Redex

/-- What a typed component offers are guards. -/
theorem offers_guards_typed {definitions : List Definition} (admitted : admits definitions = true)
    {free : FreeTypeContext} {bound : List TypeExpr} {component : Pattern} {guards : List Pattern}
    (typed : HasType ccsRecCalc free bound component (.base "Proc")) (offered : offers definitions component = some guards) :
    ∀ guard ∈ guards, HasType ccsRecCalc free bound guard (.base "Guard") := by
  rcases offers_cases offered with ⟨tail, rfl⟩ | ⟨name, args, rfl, found⟩
  · exact sum_guards typed
  · obtain ⟨definition, names, lookupFound, namesFound, rfl⟩ := body_some found
    obtain ⟨rfl, length⟩ := arguments_of_argumentsOf namesFound
    exact instantiate_typed admitted (lookup_mem lookupFound) length (arguments_names (call_arguments typed))

/-- What an object component offers are objects. -/
theorem offers_guards_objects {definitions : List Definition} (admitted : admits definitions = true)
    {component : Pattern} {guards : List Pattern} (object : isObjectPattern component = true)
    (offered : offers definitions component = some guards) : ∀ guard ∈ guards, isObjectPattern guard = true := by
  rcases offers_cases offered with ⟨tail, rfl⟩ | ⟨name, args, rfl, found⟩
  · cases bag_tail_none (kind := .hashBag) (elements := guards) (tail := tail)
      (by simpa [isObjectPattern, isObjectPatternList] using object)
    exact Steps.object_of_sum object
  · obtain ⟨definition, names, lookupFound, namesFound, rfl⟩ := body_some found
    obtain ⟨rfl, -⟩ := arguments_of_argumentsOf namesFound
    have argsObject : isObjectPattern (arguments names) = true := by
      simp only [isObjectPattern, isObjectPatternList, Bool.and_true, Bool.and_eq_true] at object
      exact object.2
    exact instantiate_objects admitted (lookup_mem lookupFound) (arguments_objects argsObject)

/-- **A component offering a guard that is its own block is its own block.** -/
theorem Offer.atom (offer : Offer definitions) (guardAtom : decompose ccsBlock offer.guard = Prenex.atom offer.guard) :
    decompose ccsBlock offer.component = Prenex.atom offer.component := by
  rcases offers_cases offer.offered with ⟨tail, componentIs⟩ | ⟨name, args, componentIs, -⟩
  · rw [componentIs]
    apply decompose_multiset_atom (by simp)
    rintro ⟨-, empty⟩
    cases tail with
    | none =>
        rw [decompose_bag] at empty
        exact Steps.decomposeList_components guardAtom offer.guard_mem (by rw [empty]; rfl)
    | some held => simp [decompose, Prenex.atom, Prenex.nil] at empty
  · rw [componentIs]
    exact decompose_atom (by simp) (by simp) (by simp) (by intro label argument equal; cases equal)

namespace Redex

theorem atoms (redex : Redex definitions) : ∀ part ∈ redex.parts, decompose ccsBlock part = Prenex.atom part := by
  intro part member
  cases redex with
  | react first second name continuation continuation' acting coacting =>
      simp only [parts, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact first.atom (by rw [acting]; exact Steps.act_atom name continuation)
      · exact second.atom (by rw [coacting]; exact Steps.coact_atom name continuation')
  | silent offer continuation taken =>
      simp only [parts, List.mem_singleton] at member
      subst member
      exact offer.atom (by rw [taken]; exact Steps.tau_atom continuation)

/-- **What a redex releases are processes.** -/
theorem result_members (admitted : admits definitions = true) {free : FreeTypeContext} {bound : List TypeExpr}
    (redex : Redex definitions) (members : Members ccsRecCalc ccsBlock free bound redex.parts) :
    Members ccsRecCalc ccsBlock free bound redex.result := by
  cases redex with
  | react first second name continuation continuation' acting coacting =>
      have firstGuard := offers_guards_typed admitted (members first.component (by simp [parts])) first.offered
        first.guard first.guard_mem
      have secondGuard := offers_guards_typed admitted (members second.component (by simp [parts])) second.offered
        second.guard second.guard_mem
      rw [acting] at firstGuard
      rw [coacting] at secondGuard
      intro element member
      simp only [result, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact (prefix_parts (.inl rfl) firstGuard).2
      · exact (prefix_parts (.inr rfl) secondGuard).2
  | silent offer continuation taken =>
      have guard := offers_guards_typed admitted (members offer.component (by simp [parts])) offer.offered
        offer.guard offer.guard_mem
      rw [taken] at guard
      intro element member
      simp only [result, List.mem_singleton] at member
      subst member
      exact tau_part guard

theorem result_objects (admitted : admits definitions = true) (redex : Redex definitions)
    (objects : ∀ part ∈ redex.parts, isObjectPattern part = true) :
    ∀ element ∈ redex.result, isObjectPattern element = true := by
  cases redex with
  | react first second name continuation continuation' acting coacting =>
      have firstGuard := offers_guards_objects admitted (objects first.component (by simp [parts])) first.offered
        first.guard first.guard_mem
      have secondGuard := offers_guards_objects admitted (objects second.component (by simp [parts])) second.offered
        second.guard second.guard_mem
      rw [acting] at firstGuard
      rw [coacting] at secondGuard
      intro element member
      simp only [result, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact Steps.object_of_prefix firstGuard
      · exact Steps.object_of_prefix secondGuard
  | silent offer continuation taken =>
      have guard := offers_guards_objects admitted (objects offer.component (by simp [parts])) offer.offered
        offer.guard offer.guard_mem
      rw [taken] at guard
      intro element member
      simp only [result, List.mem_singleton] at member
      subst member
      exact Steps.object_of_tau guard

theorem freeIn_result (admitted : admits definitions = true) (redex : Redex definitions) {index : Nat}
    {element : Pattern} (member : element ∈ redex.result) (free : FreeIn index element) :
    ∃ part ∈ redex.parts, FreeIn index part := by
  cases redex with
  | react first second name continuation continuation' acting coacting =>
      simp only [result, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · refine ⟨first.component, by simp [parts], freeIn_offered admitted first.offered first.guard_mem ?_⟩
        rw [acting]
        exact freeIn_apply.mpr ⟨element, by simp, free⟩
      · refine ⟨second.component, by simp [parts], freeIn_offered admitted second.offered second.guard_mem ?_⟩
        rw [coacting]
        exact freeIn_apply.mpr ⟨element, by simp, free⟩
  | silent offer continuation taken =>
      simp only [result, List.mem_singleton] at member
      subst member
      refine ⟨offer.component, by simp [parts], freeIn_offered admitted offer.offered offer.guard_mem ?_⟩
      rw [taken]
      exact freeIn_apply.mpr ⟨element, by simp, free⟩

end Redex

/-! ## Canonical parts of a redex -/

/-- **An offer at the canonical form**: a call offers what it offered, a canonical sum the canonical form of the
guard taken. -/
theorem Offer.canonical (offer : Offer definitions) {free : FreeTypeContext} {bound : List TypeExpr} (fuel : Nat)
    (typed : HasType ccsRecCalc free bound offer.component (.base "Proc"))
    (object : isObjectPattern offer.component = true) :
    ∃ offer' : Offer definitions, offer'.component = canonComponentWith ccsBlock (fuel + 1) offer.component ∧
      (offer'.guard = offer.guard ∨ offer'.guard = canonComponentWith ccsBlock (fuel - 1) offer.guard) := by
  rcases offers_cases offer.offered with ⟨tail, componentIs⟩ | ⟨name, args, componentIs, found⟩
  · rw [componentIs] at object typed
    cases bag_tail_none (kind := .hashBag) (elements := offer.guards) (tail := tail)
      (by simpa [isObjectPattern, isObjectPatternList] using object)
    obtain ⟨position, inside, at'⟩ :=
      List.getElem_of_mem (Steps.mem_guardsCanon fuel (guards := offer.guards) offer.guard_mem)
    refine ⟨⟨sum (Steps.guardsCanon fuel offer.guards), Steps.guardsCanon fuel offer.guards, rfl, position, inside⟩,
      ?_, .inr at'⟩
    rw [componentIs]
    exact (canon_sum fuel typed).symm
  · obtain ⟨definition, names, lookupFound, namesFound, -⟩ := body_some found
    obtain ⟨rfl, -⟩ := arguments_of_argumentsOf namesFound
    obtain ⟨index, rfl⟩ := lookup_constant lookupFound
    rw [componentIs] at object typed
    refine ⟨offer, ?_, .inl rfl⟩
    rw [componentIs, canon_call typed object]

/-- At the canonical form, an offered prefix keeps its name, and its continuation is equivalent to the original. -/
theorem Offer.canonical_prefix {offer offer' : Offer definitions} {free : FreeTypeContext} {bound : List TypeExpr}
    (context : BaseContext free bound) (fuel : Nat) {label : String} (isPrefix : label = "CAct" ∨ label = "CCoAct")
    {name continuation : Pattern} (guardIs : offer.guard = .apply label [name, continuation])
    (typed : HasType ccsRecCalc free bound offer.guard (.base "Guard")) (object : isObjectPattern offer.guard = true)
    (canonical : offer'.guard = offer.guard ∨ offer'.guard = canonComponentWith ccsBlock (fuel - 1) offer.guard) :
    ∃ continuation', offer'.guard = .apply label [name, continuation'] ∧
      EquationEquiv (engineBasePremises RelationEnv.empty) ccsRecCalc continuation' continuation := by
  rw [guardIs] at typed object canonical
  obtain ⟨nameTyped, continuationTyped⟩ := prefix_parts isPrefix typed
  have nameObject : isObjectPattern name = true := by
    simp only [isObjectPattern, isObjectPatternList, Bool.and_true, Bool.and_eq_true] at object
    exact object.1
  rcases canonical with same | canonicalIs
  · exact ⟨continuation, same, .refl _⟩
  · refine ⟨Steps.argumentCanon (fuel - 1) continuation, ?_, argumentCanon_equivalent context _ continuationTyped⟩
    rw [canonicalIs]
    rcases isPrefix with rfl | rfl
    · rw [show Pattern.apply "CAct" [name, continuation] = act name continuation from rfl, Steps.canon_act,
        argumentCanon_name nameTyped nameObject]
      rfl
    · rw [show Pattern.apply "CCoAct" [name, continuation] = coact name continuation from rfl, Steps.canon_coact,
        argumentCanon_name nameTyped nameObject]
      rfl

theorem Offer.canonical_tau {offer offer' : Offer definitions} {free : FreeTypeContext} {bound : List TypeExpr}
    (context : BaseContext free bound) (fuel : Nat) {continuation : Pattern}
    (guardIs : offer.guard = .apply "CTau" [continuation])
    (typed : HasType ccsRecCalc free bound offer.guard (.base "Guard"))
    (canonical : offer'.guard = offer.guard ∨ offer'.guard = canonComponentWith ccsBlock (fuel - 1) offer.guard) :
    ∃ continuation', offer'.guard = .apply "CTau" [continuation'] ∧
      EquationEquiv (engineBasePremises RelationEnv.empty) ccsRecCalc continuation' continuation := by
  rw [guardIs] at typed canonical
  have continuationTyped := tau_part typed
  rcases canonical with same | canonicalIs
  · exact ⟨continuation, same, .refl _⟩
  · refine ⟨Steps.argumentCanon (fuel - 1) continuation, ?_, argumentCanon_equivalent context _ continuationTyped⟩
    rw [canonicalIs, show Pattern.apply "CTau" [continuation] = tau continuation from rfl, Steps.canon_tau]
    rfl

/-- **A redex with canonical parts**, releasing what the redex releases, up to the static theory. -/
theorem Redex.canonical (admitted : admits definitions = true) {free : FreeTypeContext} {bound : List TypeExpr}
    (context : BaseContext free bound) (fuel : Nat) (redex : Redex definitions)
    (members : Members ccsRecCalc ccsBlock free bound redex.parts)
    (objects : ∀ part ∈ redex.parts, isObjectPattern part = true) :
    ∃ redex' : Redex definitions, redex'.parts = redex.parts.map (canonComponentWith ccsBlock (fuel + 1)) ∧
      List.Forall₂ (EquationEquiv (engineBasePremises RelationEnv.empty) ccsRecCalc) redex'.result redex.result := by
  cases redex with
  | react first second name continuation continuation' acting coacting =>
      have firstTyped := members first.component (by simp [Redex.parts])
      have secondTyped := members second.component (by simp [Redex.parts])
      have firstObject := objects first.component (by simp [Redex.parts])
      have secondObject := objects second.component (by simp [Redex.parts])
      obtain ⟨first', firstIs, firstCanonical⟩ := first.canonical fuel firstTyped firstObject
      obtain ⟨second', secondIs, secondCanonical⟩ := second.canonical fuel secondTyped secondObject
      obtain ⟨continuation₁, acting', equivalent₁⟩ := Offer.canonical_prefix context fuel (.inl rfl) acting
        (offers_guards_typed admitted firstTyped first.offered first.guard first.guard_mem)
        (offers_guards_objects admitted firstObject first.offered first.guard first.guard_mem) firstCanonical
      obtain ⟨continuation₂, coacting', equivalent₂⟩ := Offer.canonical_prefix context fuel (.inr rfl) coacting
        (offers_guards_typed admitted secondTyped second.offered second.guard second.guard_mem)
        (offers_guards_objects admitted secondObject second.offered second.guard second.guard_mem) secondCanonical
      refine ⟨.react first' second' name continuation₁ continuation₂ acting' coacting', ?_,
        .cons equivalent₁ (.cons equivalent₂ .nil)⟩
      simp [Redex.parts, firstIs, secondIs]
  | silent offer continuation taken =>
      have offerTyped := members offer.component (by simp [Redex.parts])
      have offerObject := objects offer.component (by simp [Redex.parts])
      obtain ⟨offer', offerIs, offerCanonical⟩ := offer.canonical fuel offerTyped offerObject
      obtain ⟨continuation', taken', equivalent⟩ := Offer.canonical_tau context fuel taken
        (offers_guards_typed admitted offerTyped offer.offered offer.guard offer.guard_mem) offerCanonical
      exact ⟨.silent offer' continuation' taken', by simp [Redex.parts, offerIs], .cons equivalent .nil⟩

/-! ## Firing a redex -/

/-- **A redex reacts in any bag that holds its parts.** -/
theorem Redex.fires (admitted : admits definitions = true) {free : FreeTypeContext} {bound : List TypeExpr}
    (redex : Redex definitions) {components rest : List Pattern}
    (permutation : components.Perm (redex.parts ++ rest)) (members : Members ccsRecCalc ccsBlock free bound components) :
    ∃ target, RecRawStep definitions (Prenex.body ccsBlock components) target ∧
      EquationEquiv (engineBasePremises RelationEnv.empty) ccsRecCalc target
        (.collection .hashBag (redex.result ++ rest) none) := by
  have released := redex.result_members admitted (fun part member => members part (permutation.mem_iff.mpr
    (List.mem_append_left _ member)))
  cases redex with
  | react first second name continuation continuation' acting coacting =>
      simp only [Redex.parts, List.cons_append, List.nil_append] at permutation
      have long : 2 ≤ components.length := by rw [permutation.length_eq]; simp
      obtain ⟨i, hi, j, hj, firstAt, secondAt, restPerm⟩ := indices_of_perm_two permutation
      refine ⟨.collection .hashBag (continuation :: continuation' :: (components.eraseIdx i).eraseIdx j) none, ?_, ?_⟩
      · rw [body_of_long long]
        exact .react i hi j hj first.position first.inside second.position second.inside name continuation
          continuation' (by rw [firstAt]; exact first.offered) (by rw [secondAt]; exact second.offered) acting coacting
      · have contractumMembers : Members ccsRecCalc ccsBlock free bound
            (continuation :: continuation' :: (components.eraseIdx i).eraseIdx j) := by
          intro element member
          simp only [List.mem_cons] at member
          rcases member with rfl | rfl | inRest
          · exact released _ (by simp [Redex.result])
          · exact released _ (by simp [Redex.result])
          · exact members element (List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx inRest))
        exact derivedInstance_equivalent (DerivedInstance.bagPerm_of_sorted
          ⟨free, bound, bag_typed (rest := none) contractumMembers⟩ ((restPerm.cons _).cons _))
  | silent offer continuation taken =>
      simp only [Redex.parts, List.cons_append, List.nil_append] at permutation
      have continuationTyped := released continuation (by simp [Redex.result])
      cases rest with
      | nil =>
          obtain rfl := List.perm_singleton.mp permutation
          refine ⟨continuation, .tau offer.position offer.inside continuation offer.offered taken, ?_⟩
          exact .symm _ _ (derivedInstance_equivalent (ccsRecBlockLanguage.singleton continuationTyped))
      | cons other others =>
          have long : 2 ≤ components.length := by rw [permutation.length_eq]; simp
          obtain ⟨i, hi, firstAt, restPerm⟩ := index_of_perm_one permutation
          refine ⟨.collection .hashBag (continuation :: components.eraseIdx i) none, ?_, ?_⟩
          · rw [body_of_long long]
            exact .par i hi (by rw [firstAt]; exact .tau offer.position offer.inside continuation offer.offered taken)
          · have contractumMembers : Members ccsRecCalc ccsBlock free bound (continuation :: components.eraseIdx i) := by
              intro element member
              rcases List.mem_cons.mp member with rfl | inRest
              · exact continuationTyped
              · exact members element (List.mem_of_mem_eraseIdx inRest)
            exact derivedInstance_equivalent (DerivedInstance.bagPerm_of_sorted
              ⟨free, bound, bag_typed (rest := none) contractumMembers⟩ (restPerm.cons _))

/-! ## The reactions of CCS with recursion -/

/-- **The reactions of CCS with recursion**: an action and its co-action offered by two components, or a silent guard
offered by one. -/
abbrev recReactions (admitted : admits definitions = true) :
    Reactions ccsRecCalc ccsBlock (RecRawStep definitions) where
  Redex := Redex definitions
  parts := Redex.parts
  result := Redex.result
  rename := Redex.rename admitted
  parts_rename := Redex.parts_rename admitted
  result_rename := Redex.result_rename admitted
  atoms := Redex.atoms
  result_members redex members := redex.result_members admitted members
  result_objects := Redex.result_objects admitted
  freeIn_result := Redex.freeIn_result admitted
  canonical context fuel redex members objects := redex.canonical admitted context fuel members objects
  react redex _ _ permutation members _ := redex.fires admitted permutation members
  restrict stepped := .res none stepped

/-- **A step is a reaction of the components of a block**, up to the static theory. -/
theorem step_block (admitted : admits definitions = true) {source target : Pattern}
    (step : RecRawStep definitions source target) :
    ∀ {free : FreeTypeContext} {bound : List TypeExpr}, BaseContext free bound →
      HasType ccsRecCalc free bound source (.base "Proc") → isObjectPattern source = true →
        StepBlock (recReactions admitted) free bound source target := by
  induction step with
  | @react elements tail i hi j hj guards guards' k hk l hl name continuation continuation' first second acting
      coacting =>
      intro free bound _ typed object
      cases bag_tail_none object
      have members := members_of_bag (block := ccsBlock) typed
      have objects := bag_objects object
      let redex : Redex definitions :=
        .react ⟨elements[i], guards, first, k, hk⟩ ⟨(elements.eraseIdx i)[j], guards', second, l, hl⟩ name continuation
          continuation' acting coacting
      have permutation := (perm_getElem_eraseIdx elements i hi).trans
        ((perm_getElem_eraseIdx (elements.eraseIdx i) j hj).cons _)
      exact ⟨0, redex, (elements.eraseIdx i).eraseIdx j, ReactsAt.ofPerm typed members objects permutation (.refl _)⟩
  | @tau source guards k hk continuation offered taken =>
      intro free bound _ typed object
      let redex : Redex definitions := .silent ⟨source, guards, offered, k, hk⟩ continuation taken
      have continuationTyped := tau_part (taken ▸ offers_guards_typed admitted typed offered _ (List.getElem_mem hk))
      exact ⟨0, redex, [], StepBlockAt.single (reactions := recReactions admitted) (redex := redex) rfl typed object
        (.symm _ _ (derivedInstance_equivalent (ccsRecBlockLanguage.singleton continuationTyped)))⟩
  | @par elements tail i hi target inner recurse =>
      intro free bound context typed object
      cases bag_tail_none object
      have members := members_of_bag (block := ccsBlock) typed
      have objects := bag_objects object
      obtain ⟨count, redex, rest, stepBlock⟩ :=
        recurse context (members _ (List.getElem_mem hi)) (objects _ (List.getElem_mem hi))
      exact ⟨count, redex, _, stepBlock.inBag i hi typed objects⟩
  | @res binder source target inner recurse =>
      intro free bound context typed object
      cases restriction_binder (block := ccsBlock) typed
      have bodyTyped := restriction_body (block := ccsBlock) typed
      have bodyObject : isObjectPattern source = true := by rwa [isObject_restriction] at object
      obtain ⟨count, redex, rest, stepBlock⟩ := recurse (context.cons "Name") bodyTyped bodyObject
      exact ⟨count + 1, redex, rest, stepBlock.restrict⟩

/-- **A step keeps a typed object process a typed object process.** -/
theorem typed_of_raw (admitted : admits definitions = true) {source target : Pattern}
    (step : RecRawStep definitions source target) :
    ∀ {free : FreeTypeContext} {bound : List TypeExpr}, HasType ccsRecCalc free bound source (.base "Proc") →
      isObjectPattern source = true →
        HasType ccsRecCalc free bound target (.base "Proc") ∧ isObjectPattern target = true := by
  induction step with
  | @react elements tail i hi j hj guards guards' k hk l hl name continuation continuation' first second acting
      coacting =>
      intro free bound typed object
      cases bag_tail_none object
      have members := members_of_bag (block := ccsBlock) typed
      have objects := bag_objects object
      have firstMember := List.getElem_mem hi
      have secondMember := List.mem_of_mem_eraseIdx (List.getElem_mem hj)
      have actTyped := acting ▸ offers_guards_typed admitted (members _ firstMember) first _ (List.getElem_mem hk)
      have coactTyped := coacting ▸ offers_guards_typed admitted (members _ secondMember) second _
        (List.getElem_mem hl)
      have actObject := acting ▸ offers_guards_objects admitted (objects _ firstMember) first _ (List.getElem_mem hk)
      have coactObject := coacting ▸ offers_guards_objects admitted (objects _ secondMember) second _
        (List.getElem_mem hl)
      have released : Members ccsRecCalc ccsBlock free bound
          (continuation :: continuation' :: (elements.eraseIdx i).eraseIdx j) := by
        intro element member
        simp only [List.mem_cons] at member
        rcases member with rfl | rfl | inRest
        · exact (prefix_parts (.inl rfl) actTyped).2
        · exact (prefix_parts (.inr rfl) coactTyped).2
        · exact members element (List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx inRest))
      refine ⟨bag_typed (block := ccsBlock) released, isObject_bag.mpr ?_⟩
      intro element member
      simp only [List.mem_cons] at member
      rcases member with rfl | rfl | inRest
      · exact Steps.object_of_prefix actObject
      · exact Steps.object_of_prefix coactObject
      · exact objects element (List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx inRest))
  | @tau source guards k hk continuation offered taken =>
      intro free bound typed object
      have tauTyped := taken ▸ offers_guards_typed admitted typed offered _ (List.getElem_mem hk)
      have tauObject := taken ▸ offers_guards_objects admitted object offered _ (List.getElem_mem hk)
      exact ⟨tau_part tauTyped, Steps.object_of_tau tauObject⟩
  | @par elements tail i hi target inner recurse =>
      intro free bound typed object
      cases bag_tail_none object
      have members := members_of_bag (block := ccsBlock) typed
      have objects := bag_objects object
      obtain ⟨innerTyped, innerObject⟩ := recurse (members _ (List.getElem_mem hi)) (objects _ (List.getElem_mem hi))
      refine ⟨bag_typed (block := ccsBlock) ?_, isObject_bag.mpr ?_⟩
      · intro element member
        rcases List.mem_cons.mp member with rfl | inRest
        · exact innerTyped
        · exact members element (List.mem_of_mem_eraseIdx inRest)
      · intro element member
        rcases List.mem_cons.mp member with rfl | inRest
        · exact innerObject
        · exact objects element (List.mem_of_mem_eraseIdx inRest)
  | @res binder source target inner recurse =>
      intro free bound typed object
      cases restriction_binder (block := ccsBlock) typed
      have bodyObject : isObjectPattern source = true := by rwa [isObject_restriction] at object
      obtain ⟨innerTyped, innerObject⟩ := recurse (restriction_body (block := ccsBlock) typed) bodyObject
      exact ⟨ccsRecBlockLanguage.restrict_typed innerTyped, by rwa [isObject_restriction]⟩

/-- **A step of a process is matched by a step of its canonical form**, to a contractum with the same canonical
form. -/
theorem simulation (admitted : admits definitions = true) {free : FreeTypeContext} {bound : List TypeExpr}
    (context : BaseContext free bound) {source target : Pattern} (step : RecRawStep definitions source target)
    (typed : HasType ccsRecCalc free bound source (.base "Proc")) (object : isObjectPattern source = true) :
    ∃ target', RecRawStep definitions (canon ccsBlock source) target' ∧ canon ccsBlock target' = canon ccsBlock target :=
  Mettapedia.GSLT.LanguageDef.RestrictionBlocks.simulation (recReactions admitted) context
    (step_block admitted step context typed object) object

end Mettapedia.Languages.ProcessCalculi.CCS.Recursive
