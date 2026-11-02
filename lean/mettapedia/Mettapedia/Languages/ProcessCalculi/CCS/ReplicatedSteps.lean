import Mettapedia.Languages.ProcessCalculi.CCS.Replicated
import Mettapedia.Languages.ProcessCalculi.CCS.Reflection
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationPresentations
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationMultisets

/-!
# CCS with replication: steps through the canonical form

The steps of CCS with replication are reactions (`ccsRepReactions`): two sums side by side, an action among the
summands of the first and the co-action on its name among those of the second, leave both continuations; a sum with a
silent summand leaves its continuation. The other summands are discarded. A redex records the summands before and
after the one that acts, so its parts are the sums as they stand. The authored rules are finite CCS's, and they fire
as `CCSRawStep` says in any language that has them (`step_iff_raw`).

Components read alike to the canonical forms of a redex's parts are sums whose summands read, one for one, as the
canonical summands of the parts (`plain_reads_alike`), so one of them is an action, a co-action or a silent prefix read
as the redex's, and they are a redex leaving equivalent processes (`Redex.alike`). A step reaches a block with a redex
at its front (`step_block`), so some unfolding of its canonical form steps to an equivalent contractum
(`simulation`), and so does a presentation of the canonical form (`presented`): a replicated sum is one component, so
within two unfoldings.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.CCS.ReplicatedSteps

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Prenex
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (FreeIn freeIn_apply freeIn_collection)
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationEquiv DerivedInstance derivedInstance_equivalent)
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (engineBasePremises)
open Mettapedia.GSLT.LanguageDef.BagNormalForm (elementsHaveType_iff isObjectPatternList_iff)
open Mettapedia.Languages.ProcessCalculi.CCS (ccsCalc CCSRawStep ccsReactRewrite ccsTauRewrite ccsParCongRewrite
  ccsResCongRewrite)
open Mettapedia.Languages.ProcessCalculi.CCS.Blocks (ccsBlock)
open Mettapedia.Languages.ProcessCalculi.CCS.Replicated (ccsRepCalc ccsRepRule ccsRepBlock ccsRepCalc_rewrites
  ccsRepBlockSignature)

/-- **The authored rules of CCS with replication fire exactly as the specification says.** -/
theorem step_iff_raw (source target : Pattern) :
    Mettapedia.OSLF.MeTTaIL.ContextualStep.Step (engineBasePremises RelationEnv.empty) ccsRepCalc source target ↔
      CCSRawStep source target :=
  Mettapedia.Languages.ProcessCalculi.CCS.step_iff_raw_of ccsRepCalc_rewrites source target

/-! ## Sums and guards -/

/-- A sum of guards. -/
def sum (guards : List Pattern) : Pattern := .apply "CSum" [.collection .hashBag guards none]

/-- An action guard. -/
def act (name continuation : Pattern) : Pattern := .apply "CAct" [name, continuation]

/-- A co-action guard. -/
def coact (name continuation : Pattern) : Pattern := .apply "CCoAct" [name, continuation]

/-- A silent guard. -/
def tau (continuation : Pattern) : Pattern := .apply "CTau" [continuation]

/-- The parameters of the guards and of replication, by label. -/
theorem params_of_label {rule : GrammarRule} (member : rule ∈ ccsRepCalc.terms) :
    (rule.label = "CAct" → rule.params = [.simple "a" (.base "Name"), .simple "p" (.base "Proc")]) ∧
    (rule.label = "CCoAct" → rule.params = [.simple "a" (.base "Name"), .simple "p" (.base "Proc")]) ∧
    (rule.label = "CTau" → rule.params = [.simple "p" (.base "Proc")]) ∧
    (rule.label = "CRep" → rule.params = [.simple "p" (.base "Proc")]) := by
  simp only [ccsRepCalc, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [ccsCalc, ccsRepRule]

/-- Every constructor makes a process or a guard. -/
theorem category_of_member {rule : GrammarRule} (member : rule ∈ ccsRepCalc.terms) :
    rule.category = "Proc" ∨ rule.category = "Guard" := by
  simp only [ccsRepCalc, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [ccsCalc, ccsRepRule]

/-- **The summands of a typed sum are guards.** -/
theorem sum_guards {free : FreeTypeContext} {bound : List TypeExpr} {guards : List Pattern}
    (typed : HasType ccsRepCalc free bound (sum guards) (.base "Proc")) :
    ∀ guard ∈ guards, HasType ccsRepCalc free bound guard (.base "Guard") := by
  obtain ⟨rule, member, labelIs, -, -, parameterName, elementSort, argument, params, -, argumentsIs, argumentTyped⟩ :=
    multiset_argument (block := ccsBlock) typed (by simp)
  have sortIs : elementSort = "Guard" := by
    simp only [ccsRepCalc, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all [ccsCalc, ccsRepRule, TypeExpr.bag]
  subst sortIs
  simp only [List.cons.injEq, and_true] at argumentsIs
  subst argumentsIs
  rcases hasType_collection_inversion argumentTyped with ⟨elementType, typeIs, elementsTyped⟩ |
    ⟨rule', -, -, -, -, typeIs, -⟩
  · simp only [TypeExpr.collection.injEq, true_and] at typeIs
    subst typeIs
    exact elementsHaveType_iff.mp elementsTyped
  · cases typeIs

/-- **A typed action or co-action** is on a name, followed by a process. -/
theorem prefix_parts {free : FreeTypeContext} {bound : List TypeExpr} {label : String} {name continuation : Pattern}
    (prefixed : label = "CAct" ∨ label = "CCoAct")
    (typed : HasType ccsRepCalc free bound (.apply label [name, continuation]) (.base "Guard")) :
    HasType ccsRepCalc free bound name (.base "Name") ∧ HasType ccsRepCalc free bound continuation (.base "Proc") := by
  obtain ⟨rule, member, labelIs, -, -, arguments⟩ := hasType_apply_inversion typed
  have paramsIs : rule.params = [.simple "a" (.base "Name"), .simple "p" (.base "Proc")] := by
    rcases prefixed with rfl | rfl
    · exact (params_of_label member).1 labelIs.symm
    · exact (params_of_label member).2.1 labelIs.symm
  rw [paramsIs] at arguments
  cases arguments with
  | cons _ nameType nameTyped rest =>
      cases rest with
      | cons _ continuationType continuationTyped _ =>
          simp only [parameterType?, Option.some.injEq] at nameType continuationType
          subst nameType continuationType
          exact ⟨nameTyped, continuationTyped⟩

/-- **A typed silent guard** is followed by a process. -/
theorem tau_part {free : FreeTypeContext} {bound : List TypeExpr} {continuation : Pattern}
    (typed : HasType ccsRepCalc free bound (.apply "CTau" [continuation]) (.base "Guard")) :
    HasType ccsRepCalc free bound continuation (.base "Proc") := by
  obtain ⟨rule, member, labelIs, -, -, arguments⟩ := hasType_apply_inversion typed
  rw [(params_of_label member).2.2.1 labelIs.symm] at arguments
  cases arguments with
  | cons _ continuationType continuationTyped _ =>
      simp only [parameterType?, Option.some.injEq] at continuationType
      subst continuationType
      exact continuationTyped

theorem object_of_sum {guards : List Pattern} (object : isObjectPattern (sum guards) = true) :
    ∀ guard ∈ guards, isObjectPattern guard = true := by
  simp only [sum, isObjectPattern, isObjectPatternList, Bool.and_true, Option.isNone_none,
    Bool.true_and] at object
  exact isObjectPatternList_iff.mp object

theorem binds_of_sum {guards : List Pattern} (binds : restrictionsBind ccsBlock (sum guards) = true) :
    ∀ guard ∈ guards, restrictionsBind ccsBlock guard = true := by
  simp only [sum, restrictionsBind, restrictionsBindList, Bool.and_true, Bool.and_eq_true] at binds
  rw [restrictionsBindList_eq_all, List.all_eq_true] at binds
  exact binds.2

/-! ## Redexes -/

/-- **A redex of CCS with replication**: an action and the co-action on one name, each a summand of a sum, with the
summands before and after each; or a silent summand of a sum, with the summands before and after it. -/
inductive Redex where
  | react (name continuation continuation' : Pattern) (before after before' after' : List Pattern)
  | silent (continuation : Pattern) (before after : List Pattern)

namespace Redex

/-- The sums that react. -/
def parts : Redex → List Pattern
  | react name continuation continuation' before after before' after' =>
      [sum (before ++ act name continuation :: after), sum (before' ++ coact name continuation' :: after')]
  | silent continuation before after => [sum (before ++ tau continuation :: after)]

/-- What they leave: both continuations, or the silent summand's continuation. -/
def result : Redex → List Pattern
  | react _ continuation continuation' _ _ _ _ => [continuation, continuation']
  | silent continuation _ _ => [continuation]

/-- Rename a redex's variables. -/
def rename (relabel : Nat → Nat) : Redex → Redex
  | react name continuation continuation' before after before' after' =>
      react (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename relabel name)
        (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename relabel continuation)
        (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename relabel continuation')
        (before.map (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename relabel))
        (after.map (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename relabel))
        (before'.map (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename relabel))
        (after'.map (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename relabel))
  | silent continuation before after =>
      silent (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename relabel continuation)
        (before.map (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename relabel))
        (after.map (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename relabel))

theorem parts_rename (relabel : Nat → Nat) (redex : Redex) :
    (redex.rename relabel).parts = redex.parts.map (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename relabel) := by
  cases redex <;> simp [rename, parts, sum, act, coact, tau, rename_apply, rename_collection]

theorem result_rename (relabel : Nat → Nat) (redex : Redex) :
    (redex.rename relabel).result = redex.result.map (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename relabel) := by
  cases redex <;> simp [rename, result]

/-- **What a redex leaves are processes.** -/
theorem result_members {free : FreeTypeContext} {bound : List TypeExpr} (redex : Redex)
    (members : Members ccsRepCalc ccsBlock free bound redex.parts) :
    Members ccsRepCalc ccsBlock free bound redex.result := by
  cases redex with
  | react name continuation continuation' before after before' after' =>
      have acting := sum_guards (members _ (List.mem_cons_self)) (act name continuation) (by simp)
      have coacting := sum_guards (members _ (List.mem_cons_of_mem _ List.mem_cons_self))
        (coact name continuation') (by simp)
      obtain ⟨-, continuationTyped⟩ := prefix_parts (.inl rfl) acting
      obtain ⟨-, continuation'Typed⟩ := prefix_parts (.inr rfl) coacting
      intro element member
      simp only [result, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact continuationTyped
      · exact continuation'Typed
  | silent continuation before after =>
      have silentTyped := sum_guards (members _ List.mem_cons_self) (tau continuation) (by simp)
      intro element member
      simp only [result, List.mem_singleton] at member
      subst member
      exact tau_part silentTyped

theorem result_objects (redex : Redex) (objects : ∀ part ∈ redex.parts, isObjectPattern part = true) :
    ∀ element ∈ redex.result, isObjectPattern element = true := by
  cases redex with
  | react name continuation continuation' before after before' after' =>
      have acting := object_of_sum (objects _ List.mem_cons_self) (act name continuation) (by simp)
      have coacting := object_of_sum (objects _ (List.mem_cons_of_mem _ List.mem_cons_self))
        (coact name continuation') (by simp)
      simp only [act, isObjectPattern, isObjectPatternList, Bool.and_true, Bool.and_eq_true] at acting
      simp only [coact, isObjectPattern, isObjectPatternList, Bool.and_true, Bool.and_eq_true] at coacting
      intro element member
      simp only [result, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact acting.2
      · exact coacting.2
  | silent continuation before after =>
      have silentObject := object_of_sum (objects _ List.mem_cons_self) (tau continuation) (by simp)
      intro element member
      simp only [result, List.mem_singleton] at member
      subst member
      simpa [tau, isObjectPattern, isObjectPatternList] using silentObject

/-- A variable of a summand is a variable of the sum. -/
theorem freeIn_sum {index : Nat} {guard : Pattern} {guards : List Pattern} (member : guard ∈ guards)
    (free : FreeIn index guard) : FreeIn index (sum guards) :=
  freeIn_apply.mpr ⟨.collection .hashBag guards none, by simp, freeIn_collection.mpr ⟨guard, member, free⟩⟩

theorem freeIn_result (redex : Redex) {index : Nat} {element : Pattern} (member : element ∈ redex.result)
    (free : FreeIn index element) : ∃ part ∈ redex.parts, FreeIn index part := by
  cases redex with
  | react name continuation continuation' before after before' after' =>
      simp only [result, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact ⟨_, List.mem_cons_self, freeIn_sum (guard := act name element) (by simp)
          (freeIn_apply.mpr ⟨element, by simp, free⟩)⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self,
          freeIn_sum (guard := coact name element) (by simp) (freeIn_apply.mpr ⟨element, by simp, free⟩)⟩
  | silent continuation before after =>
      simp only [result, List.mem_singleton] at member
      subst member
      exact ⟨_, List.mem_cons_self, freeIn_sum (guard := tau element) (by simp)
        (freeIn_apply.mpr ⟨element, by simp, free⟩)⟩

end Redex

/-! ## Canonical guards and sums -/

theorem sumFresh : ccsRepBlock.replicate ∉ ccsRepBlock.emptyUnits :=
  replicate_not_emptyUnit (block := ccsRepBlock) (language := ccsRepCalc)

theorem sumRestrictFresh : ccsRepBlock.replicate ≠ ccsRepBlock.restrict :=
  replicate_ne_restrict (block := ccsRepBlock) (language := ccsRepCalc)

/-- A typed guard's constructor is an action, a co-action or a silent prefix. -/
theorem guard_label {free : FreeTypeContext} {bound : List TypeExpr} {label : String} {arguments : List Pattern}
    (typed : HasType ccsRepCalc free bound (.apply label arguments) (.base "Guard")) :
    label = "CAct" ∨ label = "CCoAct" ∨ label = "CTau" := by
  obtain ⟨rule, member, labelIs, -, typeIs, -⟩ := hasType_apply_inversion typed
  simp only [TypeExpr.base.injEq] at typeIs
  subst labelIs
  simp only [ccsRepCalc, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd typeIs (by simp [ccsCalc])
  · exact absurd typeIs (by simp [ccsCalc])
  · exact absurd typeIs (by simp [ccsCalc])
  · exact absurd typeIs (by simp [ccsCalc])
  · exact .inl rfl
  · exact .inr (.inl rfl)
  · exact .inr (.inr rfl)
  · exact absurd typeIs (by simp [ccsRepRule])

/-- An application of one argument other than restriction and replication reads canonically as one component. -/
theorem canonP_single (label : String) (argument : Pattern) (notRestrict : label ≠ "CNu")
    (notReplicate : label ≠ "CRep") (notEmpty : label ≠ "CSum") :
    canonP ccsRepBlock (.apply label [argument]) =
      Prenex.atom (.apply label [argumentOf ccsRepBlock label argument (canonP ccsRepBlock argument)]) := by
  rw [canonP_apply (by simp) (fun _ _ same => notRestrict same.1) (fun _ _ same => notReplicate same.1)
    (fun _ _ _ listed => absurd (by simpa using listed) notEmpty)]
  rw [canonsP, canonsP]
  rfl

theorem canonP_pair (label : String) (first second : Pattern) :
    canonP ccsRepBlock (.apply label [first, second]) =
      Prenex.atom (.apply label (List.zipWith (argumentOf ccsRepBlock label) [first, second]
        (canonsP ccsRepBlock [first, second]))) :=
  canonP_apply (by simp) (by simp) (by simp) (by simp)

/-- **A typed guard is its own block, not replicated, and reads canonically as one component.** -/
theorem guard_facts {free : FreeTypeContext} {bound : List TypeExpr} {guard : Pattern}
    (typed : HasType ccsRepCalc free bound guard (.base "Guard")) (object : isObjectPattern guard = true) :
    decompose ccsBlock guard = Prenex.atom guard ∧ isReplicated ccsRepBlock guard = false ∧
      canonP ccsRepBlock guard = Prenex.atom (canonR ccsRepBlock guard) := by
  refine ⟨decompose_other typed (by simp), ?_, ?_⟩
  · cases replicated : isReplicated ccsRepBlock guard
    · rfl
    · obtain ⟨argument, rfl⟩ := isReplicated_shape replicated
      rcases guard_label typed with labelIs | labelIs | labelIs <;> simp at labelIs
  · cases guard with
    | bvar => rfl
    | fvar => rfl
    | apply label arguments =>
        have labels := guard_label typed
        unfold canonR
        rw [canonP_apply (fun same => by rcases labels with rfl | rfl | rfl <;> simp_all)
          (fun _ _ same => by rcases labels with rfl | rfl | rfl <;> simp_all)
          (fun _ _ same => by rcases labels with rfl | rfl | rfl <;> simp_all)
          (fun _ _ _ listed => by rcases labels with rfl | rfl | rfl <;> simp_all)]
        rfl
    | lambda => cases typed
    | multiLambda => cases typed
    | subst => simp [isObjectPattern] at object
    | collection =>
        have sortIs := (ccsRepBlockSignature.bag_members typed).2.1
        simp at sortIs

theorem canonsP_guards {free : FreeTypeContext} {bound : List TypeExpr} : ∀ {guards : List Pattern},
    (∀ guard ∈ guards, HasType ccsRepCalc free bound guard (.base "Guard")) →
    (∀ guard ∈ guards, isObjectPattern guard = true) →
    canonsP ccsRepBlock guards = (guards.map (canonR ccsRepBlock)).map Prenex.atom
  | [], _, _ => rfl
  | guard :: guards, typed, objects => by
      rw [canonsP, (guard_facts (typed guard List.mem_cons_self) (objects guard List.mem_cons_self)).2.2,
        canonsP_guards (fun other member => typed other (List.mem_cons_of_mem _ member))
          (fun other member => objects other (List.mem_cons_of_mem _ member))]
      rfl

/-- **A typed sum with a summand reads canonically as the sum of the canonical block of its summands read
canonically.** -/
theorem canonR_sum {free : FreeTypeContext} {bound : List TypeExpr} {guards : List Pattern}
    (typed : HasType ccsRepCalc free bound (sum guards) (.base "Proc")) (object : isObjectPattern (sum guards) = true)
    (nonempty : guards ≠ []) :
    canonR ccsRepBlock (sum guards) =
      sum (normal ccsRepBlock ⟨0, guards.map (canonR ccsRepBlock)⟩).components := by
  have guardsTyped := sum_guards typed
  have guardsObject := object_of_sum object
  have guardsBind := binds_of_sum (restrictionsBind_of_typed (block := ccsRepBlock) _ typed)
  have bagIs : canonP ccsRepBlock (.collection .hashBag guards none) =
      normal ccsRepBlock ⟨0, guards.map (canonR ccsRepBlock)⟩ := by
    simp only [canonP]
    rw [canonsP_guards guardsTyped guardsObject, foldr_par_atoms]
  obtain ⟨guard, member⟩ := List.exists_mem_of_ne_nil guards nonempty
  have bagNotNil : canonP ccsRepBlock (.collection .hashBag guards none) ≠ Prenex.nil :=
    canonP_bag_ne_nil sumFresh sumRestrictFresh guardsObject guardsBind
      ⟨guard, member, by
        rw [(guard_facts (guardsTyped guard member) (guardsObject guard member)).2.2]
        simp [Prenex.atom, Prenex.nil]⟩
  unfold canonR
  rw [sum, canonP_apply (by simp) (by simp) (by simp) (fun argument _ same _ => by
    simp only [List.cons.injEq, and_true] at same
    subst same
    exact bagNotNil)]
  simp only [canonsP, List.zipWith_cons_cons, List.zipWith_nil_right, argumentOf, bagIs]
  simp only [List.mem_singleton, if_true, multisetOf, normal_count_zero]
  rfl

/-- **A sum of atoms read again** is the sum of their canonical block. -/
theorem recanon_sum {guards : List Pattern} (atomic : ∀ guard ∈ guards, decompose ccsBlock guard = Prenex.atom guard) :
    recanon ccsRepBlock (sum guards) = sum (normal ccsRepBlock ⟨0, guards⟩).components := by
  rw [sum, recanon_apply_multiset (by decide) (by simp)]
  simp only [List.map_cons, List.map_nil]
  rw [multisetPart_other (by simp) (by simp), decompose_bag, decomposeList_atoms atomic]
  simp [multisetOf, normal_count_zero, sum]

theorem prenex_ext {first second : Prenex} (count : first.count = second.count)
    (components : first.components = second.components) : first = second := by
  cases first
  cases second
  simp_all

/-- Alike components read again alike. -/
theorem recanon_eq_of_alike {first second : Pattern} (alike : AlikeR ccsRepBlock first second) :
    recanon ccsRepBlock first = recanon ccsRepBlock second := by
  have read := alike.2.2.1 id Function.injective_id
  rwa [rename_id, rename_id] at read

/-- A typed argument of a collection type is a collection, its members as they stand. -/
theorem collection_of_typed {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound)
    {argument : Pattern} {kind : CollType} {elementType : TypeExpr}
    (typed : HasType ccsRepCalc free bound argument (.collection kind elementType))
    (object : isObjectPattern argument = true) : ∃ elements, argument = .collection kind elements none := by
  cases argument with
  | bvar index =>
      cases typed with
      | bvar lookup =>
          obtain ⟨sort, sortIs⟩ := context.bound _ (List.mem_of_getElem? lookup)
          cases sortIs
  | fvar name =>
      cases typed with
      | fvar lookup =>
          obtain ⟨sort, sortIs⟩ := context.free _ _ lookup
          cases sortIs
  | apply label arguments =>
      obtain ⟨rule, -, -, -, typeIs, -⟩ := hasType_apply_inversion typed
      cases typeIs
  | lambda => cases typed
  | multiLambda => cases typed
  | subst => simp [isObjectPattern] at object
  | collection kind' elements rest =>
      rcases hasType_collection_inversion typed with ⟨elementType', typeIs, -⟩ | ⟨rule, -, -, -, -, typeIs, -⟩
      · simp only [TypeExpr.collection.injEq] at typeIs
        obtain ⟨rfl, -⟩ := typeIs
        have restNone : rest = none := by
          simp only [isObjectPattern, Bool.and_eq_true, Option.isNone_iff_eq_none] at object
          exact object.1
        subst restNone
        exact ⟨elements, rfl⟩
      · cases typeIs

/-- **A typed process whose reading again is a sum is a sum.** -/
theorem sum_of_recanon {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound)
    {shown : Pattern} {guards : List Pattern} (typed : HasType ccsRepCalc free bound shown (.base "Proc"))
    (object : isObjectPattern shown = true) (read : recanon ccsRepBlock shown = sum guards) :
    ∃ shownGuards, shown = sum shownGuards := by
  cases shown with
  | apply label arguments =>
      by_cases isRestrict : label = ccsRepBlock.restrict
      · subst isRestrict
        rw [recanon_apply_restrict] at read
        simp [sum] at read
      by_cases listed : label ∈ ccsRepBlock.multisets
      · have labelIs : label = "CSum" := by simpa using listed
        subst labelIs
        obtain ⟨rule, -, -, -, -, parameterName, elementSort, argument, -, -, argumentsIs, argumentTyped⟩ :=
          multiset_argument (block := ccsBlock) typed (by simp)
        subst argumentsIs
        have argumentObject : isObjectPattern argument = true := by
          simpa [isObjectPattern, isObjectPatternList] using object
        obtain ⟨elements, rfl⟩ := collection_of_typed context argumentTyped argumentObject
        exact ⟨elements, rfl⟩
      · rw [recanon_apply_other isRestrict listed] at read
        simp only [sum, Pattern.apply.injEq] at read
        exact absurd (by rw [read.1]; simp) listed
  | collection kind elements rest =>
      rw [recanon_collection] at read
      cases read
  | lambda binder body =>
      rw [recanon_lambda] at read
      cases read
  | bvar index =>
      rw [recanon_bvar] at read
      cases read
  | fvar name =>
      rw [recanon_fvar] at read
      cases read
  | subst body replacement =>
      rw [recanon_subst] at read
      cases read
  | multiLambda => cases typed

/-- **A component read alike to a typed sum's canonical form is a sum with a summand read again as each summand of
the sum read canonically.** -/
theorem matched_summand {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound)
    {shown : Pattern} {guards : List Pattern} {guard : Pattern}
    (shownTyped : HasType ccsRepCalc free bound shown (.base "Proc")) (shownObject : isObjectPattern shown = true)
    (sumTyped : HasType ccsRepCalc free bound (sum guards) (.base "Proc"))
    (sumObject : isObjectPattern (sum guards) = true) (member : guard ∈ guards)
    (alike : AlikeR ccsRepBlock shown (canonR ccsRepBlock (sum guards))) :
    ∃ shownGuards, shown = sum shownGuards ∧ ∃ shownGuard ∈ shownGuards,
      recanon ccsRepBlock shownGuard = recanon ccsRepBlock (canonR ccsRepBlock guard) := by
  have guardsTyped := sum_guards sumTyped
  have guardsObject := object_of_sum sumObject
  -- the canonical summands
  have canonIs := canonR_sum sumTyped sumObject (List.ne_nil_of_mem member)
  set canonical := (normal ccsRepBlock ⟨0, guards.map (canonR ccsRepBlock)⟩).components with canonicalIs
  have mappedFacts : ∀ component ∈ guards.map (canonR ccsRepBlock),
      decompose ccsBlock component = Prenex.atom component ∧ isReplicated ccsRepBlock component = false := by
    intro component inMapped
    obtain ⟨original, inGuards, rfl⟩ := List.mem_map.mp inMapped
    obtain ⟨atomic, plain, -⟩ := guard_facts (canonR_sound (block := ccsRepBlock) context
      (guardsTyped original inGuards)).1 (isObject_canonR (block := ccsRepBlock) (guardsObject original inGuards))
    exact ⟨atomic, plain⟩
  have mappedAtomic : (Prenex.mk 0 (guards.map (canonR ccsRepBlock))).Atomic ccsBlock :=
    fun component inMapped => (mappedFacts component inMapped).1
  have canonicalPerm : canonical.Perm ((guards.map (canonR ccsRepBlock)).map (recanon ccsRepBlock)) :=
    normal_plain_perm sumFresh sumRestrictFresh mappedAtomic fun component inMapped => (mappedFacts component inMapped).2
  have canonicalAtomic : (Prenex.mk 0 canonical).Atomic ccsBlock :=
    normal_atomic sumFresh sumRestrictFresh mappedAtomic
  have canonicalPlain : ∀ component ∈ canonical, isReplicated ccsRepBlock component = false := by
    intro component inCanonical
    obtain ⟨original, inMapped, rfl⟩ := List.mem_map.mp (canonicalPerm.subset inCanonical)
    rw [isReplicated_recanon]
    exact (mappedFacts original inMapped).2
  -- the shown component is a sum read as the canonical summands
  have readSame := recanon_eq_of_alike alike
  rw [canonIs, recanon_sum canonicalAtomic] at readSame
  obtain ⟨shownGuards, rfl⟩ := sum_of_recanon context shownTyped shownObject readSame
  have shownGuardsTyped := sum_guards shownTyped
  have shownGuardsObject := object_of_sum shownObject
  have shownAtomic : (Prenex.mk 0 shownGuards).Atomic ccsBlock := fun component inShown =>
    (guard_facts (shownGuardsTyped component inShown) (shownGuardsObject component inShown)).1
  have shownPlain : ∀ component ∈ shownGuards, isReplicated ccsRepBlock component = false :=
    fun component inShown => (guard_facts (shownGuardsTyped component inShown) (shownGuardsObject component inShown)).2.1
  rw [recanon_sum shownAtomic] at readSame
  have sameNormal : normal ccsRepBlock ⟨0, shownGuards⟩ = normal ccsRepBlock ⟨0, canonical⟩ :=
    prenex_ext (by rw [normal_count_zero, normal_count_zero]) (by simpa [sum] using readSame)
  have readPerm := plain_reads_alike sumFresh sumRestrictFresh shownAtomic canonicalAtomic shownPlain canonicalPlain
    sameNormal
  -- the summand read as the given one
  have inCanonical : recanon ccsRepBlock (canonR ccsRepBlock guard) ∈ canonical :=
    canonicalPerm.symm.subset (List.mem_map_of_mem (List.mem_map_of_mem member))
  obtain ⟨shownGuard, inShownGuards, readIs⟩ :=
    List.mem_map.mp (readPerm.symm.subset (List.mem_map_of_mem inCanonical))
  refine ⟨shownGuards, rfl, shownGuard, inShownGuards, ?_⟩
  rw [readIs, recanon_recanon sumFresh sumRestrictFresh (idemUpTo_all sumFresh sumRestrictFresh _)]

/-! ## Components alike to the canonical parts -/

/-- **A typed object name is a variable**: CCS has no constructor of names. -/
theorem name_cases {free : FreeTypeContext} {bound : List TypeExpr} {name : Pattern}
    (typed : HasType ccsRepCalc free bound name (.base "Name")) (object : isObjectPattern name = true) :
    (∃ index, name = .bvar index) ∨ ∃ name', name = .fvar name' := by
  cases name with
  | bvar index => exact .inl ⟨index, rfl⟩
  | fvar name' => exact .inr ⟨name', rfl⟩
  | lambda => cases typed
  | multiLambda => cases typed
  | subst => simp [isObjectPattern] at object
  | apply =>
      obtain ⟨rule, member, -, -, typeIs, -⟩ := hasType_apply_inversion typed
      simp only [TypeExpr.base.injEq] at typeIs
      rcases category_of_member member with categoryIs | categoryIs <;>
        exact absurd (typeIs.trans categoryIs) (by decide)
  | collection =>
      have sortIs := (ccsRepBlockSignature.bag_members typed).2.1
      exact absurd sortIs (by simp)

theorem canonP_name {name : Pattern} (isName : (∃ index, name = .bvar index) ∨ ∃ name', name = .fvar name') :
    canonP ccsRepBlock name = Prenex.atom name := by
  rcases isName with ⟨index, rfl⟩ | ⟨name', rfl⟩ <;> rfl

theorem canonArgument_var {name : Pattern} (isName : (∃ index, name = .bvar index) ∨ ∃ name', name = .fvar name') :
    canonArgument (canonicalOf ccsRepBlock) name = name := by
  rcases isName with ⟨index, rfl⟩ | ⟨name', rfl⟩ <;> rfl

theorem canonR_act {name continuation : Pattern}
    (nameIs : (∃ index, name = .bvar index) ∨ ∃ name', name = .fvar name') :
    canonR ccsRepBlock (act name continuation) = .apply "CAct" [name, canonR ccsRepBlock continuation] := by
  unfold canonR
  rw [act, canonP_pair]
  simp [canonsP, canonP_name nameIs, argumentOf]
  rfl

theorem canonR_coact {name continuation : Pattern}
    (nameIs : (∃ index, name = .bvar index) ∨ ∃ name', name = .fvar name') :
    canonR ccsRepBlock (coact name continuation) = .apply "CCoAct" [name, canonR ccsRepBlock continuation] := by
  unfold canonR
  rw [coact, canonP_pair]
  simp [canonsP, canonP_name nameIs, argumentOf]
  rfl

theorem canonR_tau {continuation : Pattern} :
    canonR ccsRepBlock (tau continuation) = .apply "CTau" [canonR ccsRepBlock continuation] := by
  unfold canonR
  rw [tau, canonP_single "CTau" continuation (by decide) (by decide) (by decide)]
  simp [argumentOf]
  rfl

theorem recanon_prefix {label : String} (labelIs : label = "CAct" ∨ label = "CCoAct") {name reading : Pattern}
    (nameIs : (∃ index, name = .bvar index) ∨ ∃ name', name = .fvar name') :
    recanon ccsRepBlock (.apply label [name, reading]) =
      .apply label [name, canonArgument (canonicalOf ccsRepBlock) reading] := by
  rw [recanon_apply_other (by rcases labelIs with rfl | rfl <;> simp) (by rcases labelIs with rfl | rfl <;> simp)]
  simp only [List.map_cons, List.map_nil, canonArgument_var nameIs]

theorem recanon_tau (reading : Pattern) :
    recanon ccsRepBlock (.apply "CTau" [reading]) =
      .apply "CTau" [canonArgument (canonicalOf ccsRepBlock) reading] := by
  rw [recanon_apply_other (by simp) (by simp)]
  simp only [List.map_cons, List.map_nil]

/-- The label of a guard read again is its own. -/
theorem recanon_guard {free : FreeTypeContext} {bound : List TypeExpr} {label : String} {arguments : List Pattern}
    (typed : HasType ccsRepCalc free bound (.apply label arguments) (.base "Guard")) :
    recanon ccsRepBlock (.apply label arguments) =
      .apply label (arguments.map (canonArgument (canonicalOf ccsRepBlock))) := by
  have labels := guard_label typed
  exact recanon_apply_other (by rcases labels with rfl | rfl | rfl <;> simp)
    (by rcases labels with rfl | rfl | rfl <;> simp)

/-- **A guard read again as an action or a co-action reads is that prefix on that name**, its continuation read
canonically as that prefix's continuation. -/
theorem shown_prefix {free : FreeTypeContext} {bound : List TypeExpr} {label : String} {shown name reading : Pattern}
    (labelIs : label = "CAct" ∨ label = "CCoAct")
    (typed : HasType ccsRepCalc free bound shown (.base "Guard")) (object : isObjectPattern shown = true)
    (read : recanon ccsRepBlock shown = .apply label [name, reading]) :
    ∃ continuation, shown = .apply label [name, continuation] ∧
      canonArgument (canonicalOf ccsRepBlock) continuation = reading := by
  cases shown with
  | apply label' arguments =>
      rw [recanon_guard typed] at read
      simp only [Pattern.apply.injEq] at read
      obtain ⟨rfl, mapped⟩ := read
      have lengthTwo : arguments.length = 2 := by simpa using congrArg List.length mapped
      obtain ⟨first, second, rfl⟩ := List.length_eq_two.mp lengthTwo
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at mapped
      obtain ⟨nameIs, continuationIs⟩ := mapped
      obtain ⟨nameTyped, -⟩ := prefix_parts labelIs typed
      simp only [isObjectPattern, isObjectPatternList, Bool.and_eq_true, Bool.and_true] at object
      rw [canonArgument_var (name_cases nameTyped object.1)] at nameIs
      subst nameIs
      exact ⟨second, rfl, continuationIs⟩
  | collection kind elements rest =>
      rw [recanon_collection] at read
      cases read
  | lambda binder body =>
      rw [recanon_lambda] at read
      cases read
  | bvar index =>
      rw [recanon_bvar] at read
      cases read
  | fvar name' =>
      rw [recanon_fvar] at read
      cases read
  | subst body replacement =>
      rw [recanon_subst] at read
      cases read
  | multiLambda => cases typed

/-- **A guard read again as a silent prefix reads is a silent prefix**, its continuation read canonically as that
prefix's continuation. -/
theorem shown_tau {free : FreeTypeContext} {bound : List TypeExpr} {shown reading : Pattern}
    (typed : HasType ccsRepCalc free bound shown (.base "Guard"))
    (read : recanon ccsRepBlock shown = .apply "CTau" [reading]) :
    ∃ continuation, shown = .apply "CTau" [continuation] ∧
      canonArgument (canonicalOf ccsRepBlock) continuation = reading := by
  cases shown with
  | apply label arguments =>
      rw [recanon_guard typed] at read
      simp only [Pattern.apply.injEq] at read
      obtain ⟨rfl, mapped⟩ := read
      have lengthOne : arguments.length = 1 := by simpa using congrArg List.length mapped
      obtain ⟨first, rfl⟩ := List.length_eq_one_iff.mp lengthOne
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at mapped
      exact ⟨first, rfl, mapped⟩
  | collection kind elements rest =>
      rw [recanon_collection] at read
      cases read
  | lambda binder body =>
      rw [recanon_lambda] at read
      cases read
  | bvar index =>
      rw [recanon_bvar] at read
      cases read
  | fvar name' =>
      rw [recanon_fvar] at read
      cases read
  | subst body replacement =>
      rw [recanon_subst] at read
      cases read
  | multiLambda => cases typed

/-- **A typed argument read canonically is equivalent to it.** -/
theorem canonArgument_canonicalOf_equivalent {free : FreeTypeContext} {bound : List TypeExpr}
    (context : BaseContext free bound) {argument : Pattern} {sort : String}
    (typed : HasType ccsRepCalc free bound argument (.base sort)) :
    EquationEquiv (engineBasePremises RelationEnv.empty) ccsRepCalc
      (canonArgument (canonicalOf ccsRepBlock) argument) argument := by
  cases argument with
  | lambda => cases typed
  | multiLambda => cases typed
  | bvar => exact .refl _
  | fvar => exact .refl _
  | subst => exact .refl _
  | apply => exact .symm _ _ (canonicalOf_sound (block := ccsRepBlock) context typed).2.toEquationEquiv
  | collection => exact .symm _ _ (canonicalOf_sound (block := ccsRepBlock) context typed).2.toEquationEquiv

/-- Processes whose canonical arguments read alike are equivalent. -/
theorem continuation_equivalent {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound)
    {shown original : Pattern} (shownTyped : HasType ccsRepCalc free bound shown (.base "Proc"))
    (originalTyped : HasType ccsRepCalc free bound original (.base "Proc"))
    (read : canonArgument (canonicalOf ccsRepBlock) shown =
      canonArgument (canonicalOf ccsRepBlock) (canonR ccsRepBlock original)) :
    EquationEquiv (engineBasePremises RelationEnv.empty) ccsRepCalc shown original := by
  obtain ⟨canonTyped, toCanon⟩ := canonR_sound (block := ccsRepBlock) context originalTyped
  have shownSide := canonArgument_canonicalOf_equivalent context shownTyped
  have originalSide := canonArgument_canonicalOf_equivalent context canonTyped
  rw [read] at shownSide
  exact .trans _ _ _ (.symm _ _ shownSide) (.trans _ _ _ originalSide (.symm _ _ toCanon.toEquationEquiv))

/-- A list split around its member at an index. -/
theorem split_at {α : Type} (elements : List α) (index : Nat) (inside : index < elements.length) :
    elements = elements.take index ++ elements[index] :: elements.drop (index + 1) := by
  rw [List.getElem_cons_drop inside, List.take_append_drop]

theorem getElem_split {α : Type} (before after : List α) (element : α) :
    (before ++ element :: after)[before.length]'(by simp) = element := by
  simp

/-- **Components read alike to the canonical forms of a redex's parts are a redex** leaving processes equivalent to
what the redex leaves. -/
theorem Redex.alike {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound) (redex : Redex)
    (shown : List Pattern) (partsMembers : Members ccsRepCalc ccsBlock free bound redex.parts)
    (partsObjects : ∀ part ∈ redex.parts, isObjectPattern part = true)
    (shownMembers : Members ccsRepCalc ccsBlock free bound shown)
    (shownObjects : ∀ part ∈ shown, isObjectPattern part = true)
    (related : List.Forall₂ (fun part original => AlikeR ccsRepBlock part (canonR ccsRepBlock original)) shown
      redex.parts) :
    ∃ redex' : Redex, redex'.parts = shown ∧
      List.Forall₂ (EquationEquiv (engineBasePremises RelationEnv.empty) ccsRepCalc) redex'.result redex.result := by
  cases redex with
  | react name continuation continuation' before after before' after' =>
      cases related with
      | cons firstAlike rest =>
          cases rest with
          | cons secondAlike last =>
              cases last
              rename_i firstShown secondShown
              have firstTyped := partsMembers _ List.mem_cons_self
              have secondTyped := partsMembers _ (List.mem_cons_of_mem _ List.mem_cons_self)
              have firstObject := partsObjects _ List.mem_cons_self
              have secondObject := partsObjects _ (List.mem_cons_of_mem _ List.mem_cons_self)
              have acting := sum_guards firstTyped (act name continuation) (by simp)
              have coacting := sum_guards secondTyped (coact name continuation') (by simp)
              have actingObject := object_of_sum firstObject (act name continuation) (by simp)
              obtain ⟨nameTyped, continuationTyped⟩ := prefix_parts (.inl rfl) acting
              obtain ⟨-, continuation'Typed⟩ := prefix_parts (.inr rfl) coacting
              simp only [act, isObjectPattern, isObjectPatternList, Bool.and_true, Bool.and_eq_true] at actingObject
              have nameIs := name_cases nameTyped actingObject.1
              -- the summands read as the action and the co-action
              have firstShownTyped := shownMembers _ List.mem_cons_self
              have secondShownTyped := shownMembers _ (List.mem_cons_of_mem _ List.mem_cons_self)
              have firstShownObject := shownObjects _ List.mem_cons_self
              have secondShownObject := shownObjects _ (List.mem_cons_of_mem _ List.mem_cons_self)
              obtain ⟨firstGuards, rfl, actor, actorIn, actorRead⟩ :=
                matched_summand context firstShownTyped firstShownObject firstTyped firstObject
                  (guard := act name continuation) (by simp) firstAlike
              obtain ⟨secondGuards, rfl, coactor, coactorIn, coactorRead⟩ :=
                matched_summand context secondShownTyped secondShownObject secondTyped secondObject
                  (guard := coact name continuation') (by simp) secondAlike
              rw [canonR_act nameIs, recanon_prefix (.inl rfl) nameIs] at actorRead
              rw [canonR_coact nameIs, recanon_prefix (.inr rfl) nameIs] at coactorRead
              have actorTyped := sum_guards firstShownTyped actor actorIn
              have coactorTyped := sum_guards secondShownTyped coactor coactorIn
              obtain ⟨shownContinuation, rfl, continuationRead⟩ := shown_prefix (.inl rfl) actorTyped
                (object_of_sum firstShownObject _ actorIn) actorRead
              obtain ⟨shownContinuation', rfl, continuation'Read⟩ := shown_prefix (.inr rfl) coactorTyped
                (object_of_sum secondShownObject _ coactorIn) coactorRead
              obtain ⟨before1, after1, firstSplit⟩ := List.append_of_mem actorIn
              obtain ⟨before2, after2, secondSplit⟩ := List.append_of_mem coactorIn
              refine ⟨.react name shownContinuation shownContinuation' before1 after1 before2 after2, ?_, ?_⟩
              · rw [firstSplit, secondSplit]
                rfl
              obtain ⟨-, shownTyped⟩ := prefix_parts (.inl rfl) actorTyped
              obtain ⟨-, shownTyped'⟩ := prefix_parts (.inr rfl) coactorTyped
              exact .cons (continuation_equivalent context shownTyped continuationTyped continuationRead)
                (.cons (continuation_equivalent context shownTyped' continuation'Typed continuation'Read) .nil)
  | silent continuation before after =>
      cases related with
      | cons silentAlike last =>
          cases last
          rename_i silentShown
          have silentTyped := partsMembers _ List.mem_cons_self
          have silentObject := partsObjects _ List.mem_cons_self
          have continuationTyped := tau_part (sum_guards silentTyped (tau continuation) (by simp))
          have shownTyped := shownMembers _ List.mem_cons_self
          have shownObject := shownObjects _ List.mem_cons_self
          obtain ⟨guards, rfl, guard, guardIn, guardRead⟩ :=
            matched_summand context shownTyped shownObject silentTyped silentObject (guard := tau continuation)
              (by simp) silentAlike
          rw [canonR_tau, recanon_tau] at guardRead
          have guardTyped := sum_guards shownTyped guard guardIn
          obtain ⟨continuation', rfl, continuationRead⟩ := shown_tau guardTyped guardRead
          obtain ⟨before1, after1, split⟩ := List.append_of_mem guardIn
          refine ⟨.silent continuation' before1 after1, ?_, ?_⟩
          · rw [split]
            rfl
          exact .cons (continuation_equivalent context (tau_part guardTyped) continuationTyped continuationRead) .nil

/-! ## The reactions of CCS with replication -/

theorem canonP_act_ne_nil (name continuation : Pattern) : canonP ccsRepBlock (act name continuation) ≠ Prenex.nil := by
  rw [act, canonP_pair]
  simp [Prenex.atom, Prenex.nil]

theorem canonP_coact_ne_nil (name continuation : Pattern) :
    canonP ccsRepBlock (coact name continuation) ≠ Prenex.nil := by
  rw [coact, canonP_pair]
  simp [Prenex.atom, Prenex.nil]

theorem canonP_tau_ne_nil (continuation : Pattern) : canonP ccsRepBlock (tau continuation) ≠ Prenex.nil := by
  rw [tau, canonP_single "CTau" continuation (by decide) (by decide) (by decide)]
  simp [Prenex.atom, Prenex.nil]

/-- **A sum with a guard reading as one component is one component**, read canonically as itself. -/
theorem canonP_sum_atom {guards : List Pattern} {guard : Pattern} (member : guard ∈ guards)
    (guardNotNil : canonP ccsRepBlock guard ≠ Prenex.nil) (object : isObjectPattern (sum guards) = true)
    (binds : restrictionsBind ccsBlock (sum guards) = true) :
    canonP ccsRepBlock (sum guards) = Prenex.atom (canonR ccsRepBlock (sum guards)) ∧
      isReplicated ccsRepBlock (canonR ccsRepBlock (sum guards)) = false := by
  have bagNotNil := canonP_bag_ne_nil sumFresh sumRestrictFresh (object_of_sum object) (binds_of_sum binds)
    ⟨guard, member, guardNotNil⟩
  unfold canonR
  rw [sum, canonP_apply (by simp) (by simp) (by simp) (fun argument _ same _ => by
    simp only [List.cons.injEq, and_true] at same
    subst same
    exact bagNotNil)]
  refine ⟨rfl, ?_⟩
  simp only [canonsP, List.zipWith_cons_cons, List.zipWith_nil_right]
  rfl

theorem Redex.atoms (redex : Redex) : ∀ part ∈ redex.parts, isObjectPattern part = true →
    restrictionsBind ccsBlock part = true →
      canonP ccsRepBlock part = Prenex.atom (canonR ccsRepBlock part) ∧
        isReplicated ccsRepBlock (canonR ccsRepBlock part) = false := by
  intro part member object binds
  cases redex with
  | react name continuation continuation' before after before' after' =>
      simp only [Redex.parts, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact canonP_sum_atom (guard := act name continuation) (by simp) (canonP_act_ne_nil _ _) object binds
      · exact canonP_sum_atom (guard := coact name continuation') (by simp) (canonP_coact_ne_nil _ _) object binds
  | silent continuation before after =>
      simp only [Redex.parts, List.mem_singleton] at member
      subst member
      exact canonP_sum_atom (guard := tau continuation) (by simp) (canonP_tau_ne_nil _) object binds

/-- **A redex reacts in any bag that holds its parts.** -/
theorem Redex.fires {free : FreeTypeContext} {bound : List TypeExpr} (redex : Redex) {components rest : List Pattern}
    (permutation : components.Perm (redex.parts ++ rest))
    (members : Members ccsRepCalc ccsBlock free bound components) :
    ∃ target, CCSRawStep (Prenex.body ccsBlock components) target ∧
      EquationEquiv (engineBasePremises RelationEnv.empty) ccsRepCalc target
        (.collection .hashBag (redex.result ++ rest) none) := by
  have released := redex.result_members fun part member => members part (permutation.mem_iff.mpr
    (List.mem_append_left _ member))
  cases redex with
  | react name continuation continuation' before after before' after' =>
      simp only [Redex.parts, List.cons_append, List.nil_append] at permutation
      have long : 2 ≤ components.length := by rw [permutation.length_eq]; simp
      obtain ⟨i, hi, j, hj, firstAt, secondAt, restPerm⟩ := indices_of_perm_two permutation
      refine ⟨.collection .hashBag (continuation :: continuation' :: (components.eraseIdx i).eraseIdx j) none, ?_, ?_⟩
      · rw [body_of_long long]
        exact .react i hi j hj before.length (by simp) before'.length (by simp) name continuation continuation'
          firstAt secondAt (getElem_split _ _ _) (getElem_split _ _ _)
      · have contractumMembers : Members ccsRepCalc ccsBlock free bound
            (continuation :: continuation' :: (components.eraseIdx i).eraseIdx j) := by
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
      have continuationTyped := released continuation (by simp [Redex.result])
      cases rest with
      | nil =>
          obtain rfl := List.perm_singleton.mp permutation
          refine ⟨continuation, .tau before.length (by simp) continuation (getElem_split _ _ _), ?_⟩
          exact .symm _ _ (derivedInstance_equivalent (ccsRepBlockSignature.singleton continuationTyped))
      | cons other others =>
          have long : 2 ≤ components.length := by rw [permutation.length_eq]; simp
          obtain ⟨i, hi, firstAt, restPerm⟩ := index_of_perm_one permutation
          refine ⟨.collection .hashBag (continuation :: components.eraseIdx i) none, ?_, ?_⟩
          · rw [body_of_long long]
            exact .par i hi (by rw [firstAt]; exact .tau before.length (by simp) continuation (getElem_split _ _ _))
          · have contractumMembers : Members ccsRepCalc ccsBlock free bound
                (continuation :: components.eraseIdx i) := by
              intro element member
              rcases List.mem_cons.mp member with rfl | inRest
              · exact continuationTyped
              · exact members element (List.mem_of_mem_eraseIdx inRest)
            exact derivedInstance_equivalent (DerivedInstance.bagPerm_of_sorted
              ⟨free, bound, bag_typed (rest := none) contractumMembers⟩ (restPerm.cons _))

/-- **The reactions of CCS with replication**: an action and the co-action on its name in two sums, or a silent
summand. -/
abbrev ccsRepReactions : ReplicationReactions ccsRepCalc ccsRepBlock CCSRawStep where
  Redex := Redex
  parts := Redex.parts
  result := Redex.result
  rename := Redex.rename
  parts_rename := Redex.parts_rename
  result_rename := Redex.result_rename
  canonicalAtoms redex part member object binds := (redex.atoms part member object binds).1
  plain redex part member object binds := (redex.atoms part member object binds).2
  arity := 2
  arity_le redex := by cases redex <;> simp [Redex.parts]
  result_members redex members := redex.result_members members
  result_objects := Redex.result_objects
  freeIn_result := Redex.freeIn_result
  alike context redex shown members objects shownMembers shownObjects related :=
    Redex.alike context redex shown members objects shownMembers shownObjects related
  react redex _ _ permutation members _ := redex.fires permutation members
  restrict stepped := .res none stepped

/-- **A step is a reaction of the components of a block**, up to the static theory. -/
theorem step_block {source target : Pattern} (step : CCSRawStep source target) :
    ∀ {free : FreeTypeContext} {bound : List TypeExpr}, BaseContext free bound →
      HasType ccsRepCalc free bound source (.base "Proc") → isObjectPattern source = true →
        ∃ count redex rest, ReplicationStepAt ccsRepReactions free bound source target count redex rest := by
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
      exact ⟨0, redex, [], ReactsAt.single (by simp [redex, Redex.parts, sumIs]) typed object
        (.symm _ _ (derivedInstance_equivalent (ccsRepBlockSignature.singleton continuationTyped)))⟩
  | @par elements tail i hi target inner recurse =>
      intro free bound context typed object
      cases bag_tail_none object
      have members := members_of_bag (block := ccsBlock) typed
      have objects := bag_objects object
      obtain ⟨count, redex, rest, stepBlock⟩ :=
        recurse context (members _ (List.getElem_mem hi)) (objects _ (List.getElem_mem hi))
      exact ⟨count, redex, _, ReactsAt.inBag i hi (ccsRepReactions.result_members redex) typed objects stepBlock⟩
  | @res binder source target inner recurse =>
      intro free bound context typed object
      cases restriction_binder (block := ccsBlock) typed
      have bodyTyped := (ccsRepBlockSignature.restriction_typed typed).1
      have bodyObject : isObjectPattern source = true := by rwa [isObject_restriction] at object
      obtain ⟨count, redex, rest, stepBlock⟩ := recurse (context.cons "Name") bodyTyped bodyObject
      exact ⟨count + 1, redex, rest, ReactsAt.restrict stepBlock⟩

/-- **A step of a process is matched by a step of an unfolding of its canonical form**, within twice the ceiling read
off that form, to an equivalent contractum. -/
theorem simulation {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound)
    {source target : Pattern} (step : CCSRawStep source target)
    (typed : HasType ccsRepCalc free bound source (.base "Proc")) (object : isObjectPattern source = true) :
    ∃ unfolded, UnfoldsWithin ccsRepBlock (2 * ceilingOf ccsRepBlock (canonP ccsRepBlock source))
        (canonP ccsRepBlock source) unfolded ∧
      ∃ target', CCSRawStep (unfolded.toPattern ccsBlock) target' ∧
        EquationEquiv (engineBasePremises RelationEnv.empty) ccsRepCalc target' target := by
  obtain ⟨count, redex, rest, reached⟩ := step_block step context typed object
  exact replication_simulation ccsRepReactions context reached typed object

/-- **A step of a process is matched by a step of a presentation of its canonical form**, to an equivalent
contractum: within two unfoldings when every replicated component of the canonical form copies one component. -/
theorem presented {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound)
    {source target : Pattern} (step : CCSRawStep source target)
    (typed : HasType ccsRepCalc free bound source (.base "Proc")) (object : isObjectPattern source = true) :
    ∃ shown ∈ replicationPresentations ccsRepBlock 2 (canonR ccsRepBlock source), ∃ target',
      CCSRawStep shown target' ∧ EquationEquiv (engineBasePremises RelationEnv.empty) ccsRepCalc target' target := by
  obtain ⟨count, redex, rest, reached⟩ := step_block step context typed object
  exact replication_presented ccsRepReactions context reached typed object

/-- **A step keeps a typed object process a typed object.** -/
theorem typed_of_raw {source target : Pattern} (step : CCSRawStep source target) :
    ∀ {free : FreeTypeContext} {bound : List TypeExpr}, HasType ccsRepCalc free bound source (.base "Proc") →
      isObjectPattern source = true →
        HasType ccsRepCalc free bound target (.base "Proc") ∧ isObjectPattern target = true := by
  induction step with
  | @react elements tail i hi j hj guards guards' sumTail sumTail' k hk l hl name continuation continuation' first
      second acting coacting =>
      intro free bound typed object
      have members := members_of_bag (block := ccsBlock) typed
      have objects := bag_objects object
      have firstTyped := members _ (List.getElem_mem hi)
      have secondTyped := members _ (List.mem_of_mem_eraseIdx (List.getElem_mem hj))
      have firstObject := objects _ (List.getElem_mem hi)
      have secondObject := objects _ (List.mem_of_mem_eraseIdx (List.getElem_mem hj))
      rw [first] at firstTyped firstObject
      rw [second] at secondTyped secondObject
      cases bag_tail_none (kind := .hashBag) (elements := guards) (tail := sumTail)
        (by simpa [isObjectPattern, isObjectPatternList] using firstObject)
      cases bag_tail_none (kind := .hashBag) (elements := guards') (tail := sumTail')
        (by simpa [isObjectPattern, isObjectPatternList] using secondObject)
      have actorTyped := sum_guards firstTyped _ (List.getElem_mem hk)
      have coactorTyped := sum_guards secondTyped _ (List.getElem_mem hl)
      have actorObject := object_of_sum firstObject _ (List.getElem_mem hk)
      have coactorObject := object_of_sum secondObject _ (List.getElem_mem hl)
      rw [acting] at actorTyped actorObject
      rw [coacting] at coactorTyped coactorObject
      obtain ⟨-, continuationTyped⟩ := prefix_parts (.inl rfl) actorTyped
      obtain ⟨-, continuation'Typed⟩ := prefix_parts (.inr rfl) coactorTyped
      simp only [isObjectPattern, isObjectPatternList, Bool.and_true, Bool.and_eq_true] at actorObject coactorObject
      have contractumMembers : Members ccsRepCalc ccsBlock free bound
          (continuation :: continuation' :: (elements.eraseIdx i).eraseIdx j) := by
        intro element member
        simp only [List.mem_cons] at member
        rcases member with rfl | rfl | inRest
        · exact continuationTyped
        · exact continuation'Typed
        · exact members element (List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx inRest))
      refine ⟨bag_typed (rest := none) contractumMembers, ?_⟩
      rw [isObject_bag]
      intro element member
      simp only [List.mem_cons] at member
      rcases member with rfl | rfl | inRest
      · exact actorObject.2
      · exact coactorObject.2
      · exact objects element (List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx inRest))
  | @tau guards sumTail k hk continuation silent =>
      intro free bound typed object
      cases bag_tail_none (kind := .hashBag) (elements := guards) (tail := sumTail)
        (by simpa [isObjectPattern, isObjectPatternList] using object)
      have guardTyped := sum_guards typed _ (List.getElem_mem hk)
      have guardObject := object_of_sum object _ (List.getElem_mem hk)
      rw [silent] at guardTyped guardObject
      exact ⟨tau_part guardTyped, by simpa [isObjectPattern, isObjectPatternList] using guardObject⟩
  | @par elements tail i hi target inner recurse =>
      intro free bound typed object
      have members := members_of_bag (block := ccsBlock) typed
      have objects := bag_objects object
      obtain ⟨targetTyped, targetObject⟩ :=
        recurse (members _ (List.getElem_mem hi)) (objects _ (List.getElem_mem hi))
      have contractumMembers : Members ccsRepCalc ccsBlock free bound (target :: elements.eraseIdx i) := by
        intro element member
        rcases List.mem_cons.mp member with rfl | inRest
        · exact targetTyped
        · exact members element (List.mem_of_mem_eraseIdx inRest)
      refine ⟨bag_typed (rest := none) contractumMembers, ?_⟩
      rw [isObject_bag]
      intro element member
      rcases List.mem_cons.mp member with rfl | inRest
      · exact targetObject
      · exact objects element (List.mem_of_mem_eraseIdx inRest)
  | @res binder source target inner recurse =>
      intro free bound typed object
      have bodyTyped := (ccsRepBlockSignature.restriction_typed typed).1
      have bodyObject : isObjectPattern source = true := by rwa [isObject_restriction] at object
      obtain ⟨targetTyped, targetObject⟩ := recurse bodyTyped bodyObject
      exact ⟨restricts_typed (block := ccsBlock) 1 (by simpa [Prenex.restricts] using targetTyped),
        by rw [isObject_restriction]; exact targetObject⟩

end Mettapedia.Languages.ProcessCalculi.CCS.ReplicatedSteps
