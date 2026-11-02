import Mettapedia.Languages.ProcessCalculi.CCS.Blocks
import Mettapedia.Languages.ProcessCalculi.CCS.Reflection
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Reactions

/-!
# Steps through CCS's canonical form

CCS's steps are reactions (`ccsReactions`): two sums side by side in a parallel composition, one with an action
among its summands and the other with the co-action on the same name, leave both continuations; a sum with a silent
summand leaves its continuation. The other summands are discarded. A step of a process therefore reaches a block with
a redex at its front (`step_block`), and the canonical form steps too, to a contractum with the same canonical form
(`simulation`, the restriction-block theory's).

The summands of a canonical sum are sorted, so the selected summand stands anywhere in it: a redex records the
summands before and after it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.CCS.Steps

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Prenex
open Mettapedia.Languages.ProcessCalculi.CCS.Blocks (ccsBlock ccsBlockLanguage)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (FreeIn freeIn_apply freeIn_collection)
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationEquiv DerivedInstance derivedInstance_equivalent)
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (engineBasePremises)
open Mettapedia.GSLT.LanguageDef.BagNormalForm (elementsHaveType_iff isObjectPatternList_iff)

/-! ## Typing of sums and guards -/

/-- **The summands of a typed sum are guards.** -/
theorem sum_guards {free : FreeTypeContext} {bound : List TypeExpr} {guards : List Pattern}
    (typed : HasType ccsCalc free bound (sum guards) (.base "Proc")) :
    ∀ guard ∈ guards, HasType ccsCalc free bound guard (.base "Guard") := by
  obtain ⟨rule, member, labelIs, -, -, parameterName, elementSort, argument, params, -, argumentsIs, argumentTyped⟩ :=
    multiset_argument (block := ccsBlock) typed (by simp)
  have sortIs : elementSort = "Guard" := by
    simp only [ccsCalc, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [TypeExpr.bag]
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
    (typed : HasType ccsCalc free bound (.apply label [name, continuation]) (.base "Guard")) :
    HasType ccsCalc free bound name (.base "Name") ∧ HasType ccsCalc free bound continuation (.base "Proc") := by
  obtain ⟨rule, member, labelIs, -, -, arguments⟩ := hasType_apply_inversion typed
  simp only [ccsCalc, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases isPrefix with rfl | rfl <;>
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at labelIs <;>
    · cases arguments with
      | cons _ nameType nameTyped rest =>
          cases rest with
          | cons _ continuationType continuationTyped _ =>
              simp only [parameterType?, Option.some.injEq] at nameType continuationType
              subst nameType continuationType
              exact ⟨nameTyped, continuationTyped⟩

/-- **A typed silent prefix** carries a process. -/
theorem tau_part {free : FreeTypeContext} {bound : List TypeExpr} {continuation : Pattern}
    (typed : HasType ccsCalc free bound (tau continuation) (.base "Guard")) :
    HasType ccsCalc free bound continuation (.base "Proc") := by
  obtain ⟨rule, member, labelIs, -, -, arguments⟩ := hasType_apply_inversion typed
  simp only [ccsCalc, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at labelIs
  cases arguments with
  | cons _ continuationType continuationTyped _ =>
      simp only [parameterType?, Option.some.injEq] at continuationType
      subst continuationType
      exact continuationTyped

/-- A guard is its own block. -/
theorem guard_atom {free : FreeTypeContext} {bound : List TypeExpr} {guard : Pattern}
    (typed : HasType ccsCalc free bound guard (.base "Guard")) : decompose ccsBlock guard = Prenex.atom guard :=
  decompose_other typed (by simp)

theorem act_atom (name continuation : Pattern) :
    decompose ccsBlock (act name continuation) = Prenex.atom (act name continuation) := by
  apply decompose_atom <;> simp [act]

theorem coact_atom (name continuation : Pattern) :
    decompose ccsBlock (coact name continuation) = Prenex.atom (coact name continuation) := by
  apply decompose_atom <;> simp [coact]

theorem tau_atom (continuation : Pattern) :
    decompose ccsBlock (tau continuation) = Prenex.atom (tau continuation) := by
  apply decompose_atom <;> simp [tau]

/-- The blocks of a bag with an atom among its members have a component. -/
theorem decomposeList_components {element : Pattern} (atomic : decompose ccsBlock element = Prenex.atom element) :
    ∀ {elements : List Pattern}, element ∈ elements → (decomposeList ccsBlock elements).components ≠ []
  | [], member => absurd member (by simp)
  | first :: others, member => by
      rw [decomposeList]
      rcases List.mem_cons.mp member with rfl | inOthers
      · simp [Prenex.par, atomic, Prenex.atom]
      · have inner := decomposeList_components atomic inOthers
        simp only [Prenex.par, ne_eq, List.append_eq_nil_iff, List.map_eq_nil_iff, not_and]
        exact fun _ => inner

/-- **A sum with an atom among its summands is its own block.** -/
theorem sum_atom {guard : Pattern} (atomic : decompose ccsBlock guard = Prenex.atom guard) {guards : List Pattern}
    (member : guard ∈ guards) : decompose ccsBlock (sum guards) = Prenex.atom (sum guards) := by
  apply decompose_multiset_atom
  · intro binder body equal
    simp at equal
  · rintro ⟨-, empty⟩
    rw [decompose_bag] at empty
    exact decomposeList_components atomic member (by rw [empty]; rfl)

/-! ## Objects -/

theorem object_of_sum {guards : List Pattern} (object : isObjectPattern (sum guards) = true) :
    ∀ guard ∈ guards, isObjectPattern guard = true := by
  simp only [sum, isObjectPattern, isObjectPatternList, Bool.and_true, Option.isNone_none,
    Bool.true_and] at object
  exact (isObjectPatternList_iff.mp object)

theorem object_of_prefix {label : String} {name continuation : Pattern}
    (object : isObjectPattern (.apply label [name, continuation]) = true) : isObjectPattern continuation = true := by
  simp only [isObjectPattern, isObjectPatternList, Bool.and_true, Bool.and_eq_true] at object
  exact object.2

theorem object_of_tau {continuation : Pattern} (object : isObjectPattern (tau continuation) = true) :
    isObjectPattern continuation = true := by
  simpa [tau, isObjectPattern, isObjectPatternList] using object

/-! ## Redexes -/

/-- **A redex of CCS**: an action and the co-action on one name, each a summand of a sum, with the summands before
and after each; or a silent summand of a sum, with the summands before and after it. -/
inductive Redex where
  | react (name continuation continuation' : Pattern) (before after before' after' : List Pattern)
  | silent (continuation : Pattern) (before after : List Pattern)

namespace Redex

/-- The sums that react. -/
def parts : Redex → List Pattern
  | react name continuation continuation' before after before' after' =>
      [sum (before ++ act name continuation :: after), sum (before' ++ coact name continuation' :: after')]
  | silent continuation before after => [sum (before ++ tau continuation :: after)]

/-- The continuations they release. -/
def result : Redex → List Pattern
  | react _ continuation continuation' _ _ _ _ => [continuation, continuation']
  | silent continuation _ _ => [continuation]

/-- Rename a redex's variables. -/
def rename (relabel : Nat → Nat) : Redex → Redex
  | react name continuation continuation' before after before' after' =>
      react (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename relabel name) (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename relabel continuation)
        (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename relabel continuation') (before.map (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename relabel))
        (after.map (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename relabel)) (before'.map (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename relabel))
        (after'.map (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename relabel))
  | silent continuation before after =>
      silent (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename relabel continuation) (before.map (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename relabel))
        (after.map (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename relabel))

theorem parts_rename (relabel : Nat → Nat) (redex : Redex) :
    (redex.rename relabel).parts = redex.parts.map (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename relabel) := by
  cases redex <;> simp [rename, parts, sum, act, coact, tau, rename_apply, rename_collection]

theorem result_rename (relabel : Nat → Nat) (redex : Redex) :
    (redex.rename relabel).result = redex.result.map (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename relabel) := by
  cases redex <;> simp [rename, result]

theorem atoms (redex : Redex) : ∀ part ∈ redex.parts, decompose ccsBlock part = Prenex.atom part := by
  intro part member
  cases redex with
  | react name continuation continuation' before after before' after' =>
      simp only [parts, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact sum_atom (act_atom name continuation) (by simp)
      · exact sum_atom (coact_atom name continuation') (by simp)
  | silent continuation before after =>
      simp only [parts, List.mem_singleton] at member
      subst member
      exact sum_atom (tau_atom continuation) (by simp)

/-- **What a redex releases are processes.** -/
theorem result_members {free : FreeTypeContext} {bound : List TypeExpr} (redex : Redex)
    (members : Members ccsCalc ccsBlock free bound redex.parts) : Members ccsCalc ccsBlock free bound redex.result := by
  cases redex with
  | react name continuation continuation' before after before' after' =>
      have first := sum_guards (members (sum (before ++ act name continuation :: after)) (by simp [parts])) (act name continuation) (by simp)
      have second := sum_guards (members (sum (before' ++ coact name continuation' :: after')) (by simp [parts])) (coact name continuation') (by simp)
      intro element member
      simp only [result, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact (prefix_parts (.inl rfl) first).2
      · exact (prefix_parts (.inr rfl) second).2
  | silent continuation before after =>
      have guard := sum_guards (members (sum (before ++ tau continuation :: after)) (by simp [parts])) (tau continuation) (by simp)
      intro element member
      simp only [result, List.mem_singleton] at member
      subst member
      exact tau_part guard

theorem result_objects (redex : Redex) (objects : ∀ part ∈ redex.parts, isObjectPattern part = true) :
    ∀ element ∈ redex.result, isObjectPattern element = true := by
  cases redex with
  | react name continuation continuation' before after before' after' =>
      intro element member
      simp only [result, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact object_of_prefix (object_of_sum (objects (sum (before ++ act name element :: after)) (by simp [parts]))
          (act name element) (by simp))
      · exact object_of_prefix (object_of_sum (objects (sum (before' ++ coact name element :: after')) (by simp [parts]))
          (coact name element) (by simp))
  | silent continuation before after =>
      intro element member
      simp only [result, List.mem_singleton] at member
      subst member
      exact object_of_tau (object_of_sum (objects (sum (before ++ tau element :: after)) (by simp [parts]))
        (tau element) (by simp))

/-- A variable of a summand's continuation is a variable of the sum. -/
theorem freeIn_sum {index : Nat} {guard continuation : Pattern} {guards : List Pattern} (member : guard ∈ guards)
    (inGuard : FreeIn index continuation → FreeIn index guard) (free : FreeIn index continuation) :
    FreeIn index (sum guards) :=
  freeIn_apply.mpr ⟨.collection .hashBag guards none, by simp, freeIn_collection.mpr ⟨guard, member, inGuard free⟩⟩

theorem freeIn_result (redex : Redex) {index : Nat} {element : Pattern} (member : element ∈ redex.result)
    (free : FreeIn index element) : ∃ part ∈ redex.parts, FreeIn index part := by
  cases redex with
  | react name continuation continuation' before after before' after' =>
      simp only [result, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact ⟨sum (before ++ act name element :: after), by simp [parts],
          freeIn_sum (guard := act name element) (by simp)
            (fun inner => freeIn_apply.mpr ⟨element, by simp, inner⟩) free⟩
      · exact ⟨sum (before' ++ coact name element :: after'), by simp [parts],
          freeIn_sum (guard := coact name element) (by simp)
            (fun inner => freeIn_apply.mpr ⟨element, by simp, inner⟩) free⟩
  | silent continuation before after =>
      simp only [result, List.mem_singleton] at member
      subst member
      exact ⟨sum (before ++ tau element :: after), by simp [parts], freeIn_sum (guard := tau element) (by simp)
        (fun inner => freeIn_apply.mpr ⟨element, by simp, inner⟩) free⟩

end Redex

/-! ## Canonical parts of a redex -/

/-- The canonical argument of a guard's parts, within a fuel. -/
def argumentCanon : Nat → Pattern → Pattern
  | 0, argument => argument
  | fuel + 1, argument => canonArgument (canonWith ccsBlock fuel) argument

/-- The canonical summands of a sum, within a fuel. -/
def guardsCanon : Nat → List Pattern → List Pattern
  | 0, guards => guards
  | fuel + 1, guards => sortComponents (guards.map (canonComponentWith ccsBlock fuel))

theorem canon_act (fuel : Nat) (name continuation : Pattern) :
    canonComponentWith ccsBlock fuel (act name continuation) =
      act (argumentCanon fuel name) (argumentCanon fuel continuation) := by
  cases fuel <;> simp [canonComponentWith, act, argumentCanon]

theorem canon_coact (fuel : Nat) (name continuation : Pattern) :
    canonComponentWith ccsBlock fuel (coact name continuation) =
      coact (argumentCanon fuel name) (argumentCanon fuel continuation) := by
  cases fuel <;> simp [canonComponentWith, coact, argumentCanon]

theorem canon_tau (fuel : Nat) (continuation : Pattern) :
    canonComponentWith ccsBlock fuel (tau continuation) = tau (argumentCanon fuel continuation) := by
  cases fuel <;> simp [canonComponentWith, tau, argumentCanon]

/-- **A typed sum's canonical form** is the sum of its canonical summands. -/
theorem canon_sum {free : FreeTypeContext} {bound : List TypeExpr} (fuel : Nat) {guards : List Pattern}
    (typed : HasType ccsCalc free bound (sum guards) (.base "Proc")) :
    canonComponentWith ccsBlock (fuel + 1) (sum guards) = sum (guardsCanon fuel guards) := by
  cases fuel with
  | zero => simp [canonComponentWith, sum, guardsCanon, canonMultisetWith]
  | succ fuel =>
      simp only [sum, canonComponentWith, List.mem_singleton, ↓reduceIte, List.map_cons,
        List.map_nil, guardsCanon]
      rw [canonMultisetWith_atoms fuel fun guard member => guard_atom (sum_guards typed guard member)]

/-- A summand's canonical form is among the canonical summands; within no fuel, both are the summands themselves. -/
theorem mem_guardsCanon (fuel : Nat) {guard : Pattern} {guards : List Pattern} (member : guard ∈ guards) :
    canonComponentWith ccsBlock (fuel - 1) guard ∈ guardsCanon fuel guards := by
  cases fuel with
  | zero => simpa [canonComponentWith, guardsCanon] using member
  | succ fuel =>
      simp only [guardsCanon, sortComponents, Nat.add_sub_cancel]
      exact (List.perm_insertionSort _ _).symm.mem_iff.mp
        (List.mem_map_of_mem (f := canonComponentWith ccsBlock fuel) member)

/-- A part of a guard is related to its canonical argument. -/
theorem argumentCanon_equivalent {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound)
    (fuel : Nat) {argument : Pattern} {sort : String} (typed : HasType ccsCalc free bound argument (.base sort)) :
    EquationEquiv (engineBasePremises RelationEnv.empty) ccsCalc (argumentCanon fuel argument) argument := by
  cases fuel with
  | zero => exact .refl _
  | succ fuel => exact canonArgument_equivalent (block := ccsBlock) context fuel typed

/-- **A redex with canonical parts**, releasing what the redex releases, up to the static theory. -/
theorem Redex.canonical {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound)
    (fuel : Nat) (redex : Redex) (members : Members ccsCalc ccsBlock free bound redex.parts) :
    ∃ redex' : Redex, redex'.parts = redex.parts.map (canonComponentWith ccsBlock (fuel + 1)) ∧
      List.Forall₂ (EquationEquiv (engineBasePremises RelationEnv.empty) ccsCalc) redex'.result redex.result := by
  cases redex with
  | react name continuation continuation' before after before' after' =>
      have firstTyped := members (sum (before ++ act name continuation :: after)) (by simp [Redex.parts])
      have secondTyped := members (sum (before' ++ coact name continuation' :: after')) (by simp [Redex.parts])
      have actTyped := sum_guards firstTyped (act name continuation) (by simp)
      have coactTyped := sum_guards secondTyped (coact name continuation') (by simp)
      obtain ⟨newBefore, newAfter, firstIs⟩ := List.append_of_mem
        (mem_guardsCanon fuel (guard := act name continuation) (guards := before ++ act name continuation :: after)
          (by simp))
      obtain ⟨newBefore', newAfter', secondIs⟩ := List.append_of_mem
        (mem_guardsCanon fuel (guard := coact name continuation')
          (guards := before' ++ coact name continuation' :: after') (by simp))
      rw [canon_act] at firstIs
      rw [canon_coact] at secondIs
      refine ⟨.react (argumentCanon (fuel - 1) name) (argumentCanon (fuel - 1) continuation)
        (argumentCanon (fuel - 1) continuation') newBefore newAfter newBefore' newAfter', ?_, ?_⟩
      · simp only [Redex.parts, List.map_cons, List.map_nil, canon_sum fuel firstTyped, canon_sum fuel secondTyped,
          firstIs, secondIs]
      · exact .cons (argumentCanon_equivalent context (fuel - 1) (prefix_parts (.inl rfl) actTyped).2)
          (.cons (argumentCanon_equivalent context (fuel - 1) (prefix_parts (.inr rfl) coactTyped).2) .nil)
  | silent continuation before after =>
      have sumTyped := members (sum (before ++ tau continuation :: after)) (by simp [Redex.parts])
      have tauTyped := sum_guards sumTyped (tau continuation) (by simp)
      obtain ⟨newBefore, newAfter, guardsIs⟩ := List.append_of_mem
        (mem_guardsCanon fuel (guard := tau continuation) (guards := before ++ tau continuation :: after) (by simp))
      rw [canon_tau] at guardsIs
      refine ⟨.silent (argumentCanon (fuel - 1) continuation) newBefore newAfter, ?_, ?_⟩
      · simp only [Redex.parts, List.map_cons, List.map_nil, canon_sum fuel sumTyped, guardsIs]
      · exact .cons (argumentCanon_equivalent context (fuel - 1) (tau_part tauTyped)) .nil

/-! ## Firing a redex -/

/-- A list split around its member at an index. -/
theorem split_at {α : Type} (elements : List α) (index : Nat) (inside : index < elements.length) :
    elements = elements.take index ++ elements[index] :: elements.drop (index + 1) := by
  rw [List.getElem_cons_drop inside, List.take_append_drop]

theorem getElem_split {α : Type} (before after : List α) (element : α) :
    (before ++ element :: after)[before.length]'(by simp) = element := by
  simp

/-- **A redex reacts in any bag that holds its parts.** -/
theorem Redex.fires {free : FreeTypeContext} {bound : List TypeExpr} (redex : Redex) {components rest : List Pattern}
    (permutation : components.Perm (redex.parts ++ rest)) (members : Members ccsCalc ccsBlock free bound components) :
    ∃ target, CCSRawStep (Prenex.body ccsBlock components) target ∧
      EquationEquiv (engineBasePremises RelationEnv.empty) ccsCalc target
        (.collection .hashBag (redex.result ++ rest) none) := by
  cases redex with
  | react name continuation continuation' before after before' after' =>
      simp only [Redex.parts, List.cons_append, List.nil_append] at permutation
      have long : 2 ≤ components.length := by rw [permutation.length_eq]; simp
      obtain ⟨i, hi, j, hj, firstAt, secondAt, restPerm⟩ := indices_of_perm_two permutation
      refine ⟨.collection .hashBag (continuation :: continuation' :: (components.eraseIdx i).eraseIdx j) none, ?_, ?_⟩
      · rw [body_of_long long]
        exact .react i hi j hj before.length (by simp) before'.length (by simp) name continuation continuation'
          firstAt secondAt (getElem_split _ _ _) (getElem_split _ _ _)
      · have contractumMembers : Members ccsCalc ccsBlock free bound
            (continuation :: continuation' :: (components.eraseIdx i).eraseIdx j) := by
          have released := Redex.result_members (.react name continuation continuation' before after before' after')
            (fun part member => members part (permutation.mem_iff.mpr (by
              simp only [Redex.parts, List.mem_cons, List.not_mem_nil, or_false] at member
              rcases member with rfl | rfl <;> simp)))
          intro element member
          simp only [List.mem_cons] at member
          rcases member with rfl | rfl | inRest
          · exact released _ (by simp [Redex.result])
          · exact released _ (by simp [Redex.result])
          · exact members element (List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx inRest))
        exact derivedInstance_equivalent (DerivedInstance.bagPerm_of_sorted
          ⟨free, bound, bag_typed (rest := none) contractumMembers⟩ ((restPerm.cons _).cons _))
  | silent continuation before after =>
      simp only [Redex.parts, List.cons_append, List.nil_append] at permutation
      have silentTyped := members (sum (before ++ tau continuation :: after)) (permutation.mem_iff.mpr (by simp))
      have continuationTyped := tau_part (sum_guards silentTyped (tau continuation) (by simp))
      cases rest with
      | nil =>
          obtain rfl := List.perm_singleton.mp permutation
          refine ⟨continuation, .tau before.length (by simp) continuation (getElem_split _ _ _), ?_⟩
          exact .symm _ _ (derivedInstance_equivalent (ccsBlockLanguage.singleton continuationTyped))
      | cons other others =>
          have long : 2 ≤ components.length := by rw [permutation.length_eq]; simp
          obtain ⟨i, hi, firstAt, restPerm⟩ := index_of_perm_one permutation
          refine ⟨.collection .hashBag (continuation :: components.eraseIdx i) none, ?_, ?_⟩
          · rw [body_of_long long]
            exact .par i hi (by rw [firstAt]; exact .tau before.length (by simp) continuation (getElem_split _ _ _))
          · have contractumMembers : Members ccsCalc ccsBlock free bound (continuation :: components.eraseIdx i) := by
              intro element member
              rcases List.mem_cons.mp member with rfl | inRest
              · exact continuationTyped
              · exact members element (List.mem_of_mem_eraseIdx inRest)
            exact derivedInstance_equivalent (DerivedInstance.bagPerm_of_sorted
              ⟨free, bound, bag_typed (rest := none) contractumMembers⟩ (restPerm.cons _))

/-! ## CCS's reactions -/

/-- **CCS's reactions**: an action and its co-action in two sums, or a silent summand. -/
abbrev ccsReactions : Reactions ccsCalc ccsBlock CCSRawStep where
  Redex := Redex
  parts := Redex.parts
  result := Redex.result
  rename := Redex.rename
  parts_rename := Redex.parts_rename
  result_rename := Redex.result_rename
  atoms := Redex.atoms
  result_members redex members := redex.result_members members
  result_objects := Redex.result_objects
  freeIn_result := Redex.freeIn_result
  canonical context fuel redex members _ := redex.canonical context fuel members
  react redex _ _ permutation members _ := redex.fires permutation members
  restrict stepped := .res none stepped

/-- **A step is a reaction of the components of a block**, up to CCS's static theory. -/
theorem step_block {source target : Pattern} (step : CCSRawStep source target) :
    ∀ {free : FreeTypeContext} {bound : List TypeExpr}, BaseContext free bound →
      HasType ccsCalc free bound source (.base "Proc") → isObjectPattern source = true →
        StepBlock ccsReactions free bound source target := by
  induction step with
  | @react elements tail i hi j hj guards guards' sumTail sumTail' k hk l hl name continuation continuation' first
      second acting coacting =>
      intro free bound _ typed object
      cases bag_tail_none object
      have members := members_of_bag (block := ccsBlock) typed
      have objects := bag_objects object
      have firstObject := objects _ (List.getElem_mem hi)
      have secondObject := objects _ (List.mem_of_mem_eraseIdx (List.getElem_mem hj))
      rw [first] at firstObject
      rw [second] at secondObject
      cases bag_tail_none (kind := .hashBag) (elements := guards) (tail := sumTail)
        (by simpa [isObjectPattern, isObjectPatternList] using firstObject)
      cases bag_tail_none (kind := .hashBag) (elements := guards') (tail := sumTail')
        (by simpa [isObjectPattern, isObjectPatternList] using secondObject)
      let redex : Redex := .react name continuation continuation' (guards.take k) (guards.drop (k + 1))
        (guards'.take l) (guards'.drop (l + 1))
      have firstIs : elements[i] = sum (guards.take k ++ act name continuation :: guards.drop (k + 1)) := by
        rw [first, sum, act, ← acting, ← split_at guards k hk]
      have secondIs : (elements.eraseIdx i)[j] =
          sum (guards'.take l ++ coact name continuation' :: guards'.drop (l + 1)) := by
        rw [second, sum, coact, ← coacting, ← split_at guards' l hl]
      have permutation := (perm_getElem_eraseIdx elements i hi).trans
        ((perm_getElem_eraseIdx (elements.eraseIdx i) j hj).cons _)
      rw [firstIs, secondIs] at permutation
      exact ⟨0, redex, (elements.eraseIdx i).eraseIdx j,
        ReactsAt.ofPerm typed members objects permutation (.refl _)⟩
  | @tau guards sumTail k hk continuation silent =>
      intro free bound _ typed object
      cases bag_tail_none (kind := .hashBag) (elements := guards) (tail := sumTail)
        (by simpa [isObjectPattern, isObjectPatternList] using object)
      let redex : Redex := .silent continuation (guards.take k) (guards.drop (k + 1))
      have sumIs : Pattern.apply "CSum" [.collection .hashBag guards none] =
          sum (guards.take k ++ tau continuation :: guards.drop (k + 1)) := by
        rw [sum, tau, ← silent, ← split_at guards k hk]
      have continuationTyped := tau_part (sum_guards (sumIs ▸ typed) (tau continuation) (by simp))
      exact ⟨0, redex, [], StepBlockAt.single (reactions := ccsReactions) (redex := redex) (by simp [redex, Redex.parts, sumIs])
        typed object (.symm _ _ (derivedInstance_equivalent (ccsBlockLanguage.singleton continuationTyped)))⟩
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

/-- Every constructor of CCS makes a process or a guard. -/
theorem category_of_member {rule : GrammarRule} (member : rule ∈ ccsCalc.terms) :
    rule.category = "Proc" ∨ rule.category = "Guard" := by
  simp only [ccsCalc, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- The summand at an index of the summands of a typed object sum is a typed object guard. -/
theorem sum_member {free : FreeTypeContext} {bound : List TypeExpr} {guards : List Pattern} {sumTail : Option String}
    (typed : HasType ccsCalc free bound (.apply "CSum" [.collection .hashBag guards sumTail]) (.base "Proc"))
    (object : isObjectPattern (.apply "CSum" [.collection .hashBag guards sumTail]) = true) :
    sumTail = none ∧ ∀ guard ∈ guards, HasType ccsCalc free bound guard (.base "Guard") ∧
      isObjectPattern guard = true := by
  obtain rfl := bag_tail_none (kind := .hashBag) (elements := guards) (tail := sumTail)
    (by simpa [isObjectPattern, isObjectPatternList] using object)
  exact ⟨rfl, fun guard member => ⟨sum_guards typed guard member, object_of_sum object guard member⟩⟩

/-- **A step keeps a typed object process a typed object process.** -/
theorem typed_of_raw {source target : Pattern} (step : CCSRawStep source target) :
    ∀ {free : FreeTypeContext} {bound : List TypeExpr}, HasType ccsCalc free bound source (.base "Proc") →
      isObjectPattern source = true →
        HasType ccsCalc free bound target (.base "Proc") ∧ isObjectPattern target = true := by
  induction step with
  | @react elements tail i hi j hj guards guards' sumTail sumTail' k hk l hl name continuation continuation' first
      second acting coacting =>
      intro free bound typed object
      cases bag_tail_none object
      have members := members_of_bag (block := ccsBlock) typed
      have objects := bag_objects object
      have firstMember := List.getElem_mem hi
      have secondMember := List.mem_of_mem_eraseIdx (List.getElem_mem hj)
      have firstTyped := members _ firstMember
      have firstObject := objects _ firstMember
      have secondTyped := members _ secondMember
      have secondObject := objects _ secondMember
      rw [first] at firstTyped firstObject
      rw [second] at secondTyped secondObject
      obtain ⟨-, firstGuards⟩ := sum_member firstTyped firstObject
      obtain ⟨-, secondGuards⟩ := sum_member secondTyped secondObject
      obtain ⟨actTyped, actObject⟩ := firstGuards _ (acting ▸ List.getElem_mem hk)
      obtain ⟨coactTyped, coactObject⟩ := secondGuards _ (coacting ▸ List.getElem_mem hl)
      have released : Members ccsCalc ccsBlock free bound
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
      · exact object_of_prefix actObject
      · exact object_of_prefix coactObject
      · exact objects element (List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx inRest))
  | @tau guards sumTail k hk continuation silent =>
      intro free bound typed object
      obtain ⟨-, summands⟩ := sum_member typed object
      obtain ⟨tauTyped, tauObject⟩ := summands _ (silent ▸ List.getElem_mem hk)
      exact ⟨tau_part tauTyped, object_of_tau tauObject⟩
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
      exact ⟨ccsBlockLanguage.restrict_typed innerTyped, by rwa [isObject_restriction]⟩

/-- **A step of a process is matched by a step of its canonical form**, to a contractum with the same canonical
form. -/
theorem simulation {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound)
    {source target : Pattern} (step : CCSRawStep source target)
    (typed : HasType ccsCalc free bound source (.base "Proc")) (object : isObjectPattern source = true) :
    ∃ target', CCSRawStep (canon ccsBlock source) target' ∧ canon ccsBlock target' = canon ccsBlock target :=
  Mettapedia.GSLT.LanguageDef.RestrictionBlocks.simulation ccsReactions context (step_block step context typed object) object

end Mettapedia.Languages.ProcessCalculi.CCS.Steps
