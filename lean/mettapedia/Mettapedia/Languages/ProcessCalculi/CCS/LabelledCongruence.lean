import Mettapedia.Languages.ProcessCalculi.CCS.LabelledStatic

/-!
# The static theory is a strong bisimulation: laws in context

The laws of the static theory, applied anywhere in a typed object process, keep its labelled transitions.

**Where a law applies** (`LawPosition`, `lawPosition`). In a typed object process a law applies at the process itself,
at a member of a parallel bag, in the body of a restriction, to the summands of a sum, or in the continuation of a
guard. Constants, argument lists and names hold no process (`callPart_hole`), and the source of a law is a process
when it has a sort at all (`source_proc`). Between the summands of a sum, a law is a reordering
(`generator_summands`).

**Each law matches transitions where it applies at the root** (`generator_matched`): the cases of `LabelledStatic`,
each brought to its front form by reordering a bag.

**Matching is closed under the positions**: a member replaced by a matching one (`matched_member`), a body under a
restriction (`matched_restrict`), summands reordered (`matched_sumPerm`), and the continuation of one guard replaced
by an equivalent one (`matched_sumGuard`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.CCS.Recursive

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)
open Mettapedia.OSLF.MeTTaIL.DerivedContexts (OneHoleContext)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationEquiv EquationGenerator EquationContextStep
  DerivedInstance equationEquiv_fill)
open Mettapedia.GSLT.LanguageDef.BagNormalForm (elementsHaveType_iff)
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (engineBasePremises)
open Mettapedia.Languages.ProcessCalculi.CCS.Blocks (ccsBlock)

variable {definitions : List Definition}

/-! ## Arguments at a hole -/

/-- The argument at a hole of an application with one parameter is its only argument. -/
theorem one_argument {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}
    {before after : List Pattern} {middle : Pattern} {parameter : TermParam}
    (arguments : ArgumentsHaveTypes language free bound (before ++ middle :: after) [parameter]) :
    before = [] ∧ after = [] ∧ ∃ expected, parameterType? parameter = some expected ∧
      HasType language free bound middle expected := by
  rcases before with _ | ⟨first, before⟩
  · simp only [List.nil_append] at arguments
    cases arguments with
    | cons _ found middleTyped rest =>
        cases rest
        exact ⟨rfl, rfl, _, found, middleTyped⟩
  · simp only [List.cons_append] at arguments
    cases arguments with
    | cons _ _ _ rest => cases before <;> simp only [List.nil_append, List.cons_append] at rest <;> cases rest

/-- The argument at a hole of an application with two parameters is its first or its second. -/
theorem two_arguments {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}
    {before after : List Pattern} {middle : Pattern} {first second : TermParam}
    (arguments : ArgumentsHaveTypes language free bound (before ++ middle :: after) [first, second]) :
    (before = [] ∧ (∃ last, after = [last]) ∧ ∃ expected, parameterType? first = some expected ∧
        HasType language free bound middle expected) ∨
      ((∃ head, before = [head]) ∧ after = [] ∧ ∃ expected, parameterType? second = some expected ∧
        HasType language free bound middle expected) := by
  rcases before with _ | ⟨head, _ | ⟨head', before⟩⟩
  · simp only [List.nil_append] at arguments
    cases arguments with
    | cons _ found middleTyped rest =>
        cases rest with
        | cons _ _ _ rest' =>
            cases rest'
            exact .inl ⟨rfl, ⟨_, rfl⟩, _, found, middleTyped⟩
  · simp only [List.cons_append, List.nil_append] at arguments
    cases arguments with
    | cons _ _ _ rest =>
        cases rest with
        | cons _ found middleTyped rest' =>
            cases rest'
            exact .inr ⟨⟨head, rfl⟩, rfl, _, found, middleTyped⟩
  · simp only [List.cons_append] at arguments
    cases arguments with
    | cons _ _ _ rest =>
        cases rest with
        | cons _ _ _ rest' =>
            cases before <;> simp only [List.nil_append, List.cons_append] at rest' <;> cases rest'

/-! ## Where a law applies -/

/-- The sorts of constants, argument lists and names. -/
def callSort (sort : String) : Bool := sort == "Const" || sort == "Args" || sort == "Name"

/-- A parameter of one of those sorts. -/
def callParameter (parameter : TermParam) : Bool :=
  match parameterType? parameter with
  | some (.base sort) => callSort sort
  | _ => false

/-- **Constants and argument lists are built from constants, argument lists and names.** -/
theorem callRules :
    (ccsRecCalc.terms.all fun rule => !callSort rule.category || rule.params.all callParameter) = true := by
  decide

/-- **The source of a law, if it has a sort, is a process.** -/
theorem source_proc {source target : Pattern} (generator : BlockGenerator ccsRecCalc ccsBlock source target)
    {free : FreeTypeContext} {bound : List TypeExpr} {sort : String}
    (typed : HasType ccsRecCalc free bound source (.base sort)) : sort = "Proc" :=
  substitute_source_sort (block := ccsBlock) Pattern.bvar generator
    (by rwa [Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute_id])

/-- **Below a constant, an argument list or a name there are only constants, argument lists and names.** -/
theorem callPart_hole {free : FreeTypeContext} : ∀ (context : OneHoleContext) {bound : List TypeExpr}
    {inside : Pattern} {sort : String}, callSort sort = true →
    HasType ccsRecCalc free bound (context.fill inside) (.base sort) → isObjectPattern (context.fill inside) = true →
    ∃ bound' sort', callSort sort' = true ∧ HasType ccsRecCalc free bound' inside (.base sort')
  | .hole, bound, _, sort, isCall, typed, _ => ⟨bound, sort, isCall, typed⟩
  | .apply _ _ inner _, _, _, _, isCall, typed, object => by
      simp only [OneHoleContext.fill] at typed object
      obtain ⟨rule, member, -, -, typeIs, arguments⟩ := hasType_apply_inversion typed
      obtain ⟨beforeParameters, parameter, afterParameters, expected, parametersEq, -, -, -, parameterType,
          middleTyped, -⟩ := ArgumentsHaveTypes.append_cons_split arguments
      simp only [TypeExpr.base.injEq] at typeIs
      subst typeIs
      have allCall := List.all_eq_true.mp callRules rule member
      rw [isCall, Bool.not_true, Bool.false_or, List.all_eq_true] at allCall
      have parameterCall := allCall parameter (by rw [parametersEq]; simp)
      unfold callParameter at parameterCall
      rw [parameterType] at parameterCall
      match expected, parameterCall, middleTyped with
      | .base _, parameterCall, middleTyped =>
          exact callPart_hole inner parameterCall middleTyped (isObject_apply_member object)
  | .lambda _ _, _, _, _, _, typed, _ => by cases typed
  | .multiLambda _ _ _, _, _, _, _, typed, _ => by cases typed
  | .substBody _ _, _, _, _, _, _, object => by simp [OneHoleContext.fill, isObjectPattern] at object
  | .substReplacement _ _, _, _, _, _, _, object => by simp [OneHoleContext.fill, isObjectPattern] at object
  | .collection _ _ _ _ _, _, _, _, isCall, typed, _ => by
      simp only [OneHoleContext.fill] at typed
      obtain ⟨-, rfl, -⟩ := ccsRecBlockLanguage.bag_members typed
      exact absurd isCall (by decide)

/-- No law applies inside a constant, an argument list or a name. -/
theorem no_law_in_callPart {source target : Pattern} (generator : BlockGenerator ccsRecCalc ccsBlock source target)
    {free : FreeTypeContext} (context : OneHoleContext) {bound : List TypeExpr} {sort : String}
    (isCall : callSort sort = true) (typed : HasType ccsRecCalc free bound (context.fill source) (.base sort))
    (object : isObjectPattern (context.fill source) = true) : False := by
  obtain ⟨_, sort', isCall', sourceTyped⟩ := callPart_hole context isCall typed object
  rw [source_proc generator sourceTyped] at isCall'
  exact absurd isCall' (by decide)

/-- **A law below a guard is in its continuation.** -/
theorem guard_hole {free : FreeTypeContext} {source target : Pattern}
    (generator : BlockGenerator ccsRecCalc ccsBlock source target) :
    ∀ (context : OneHoleContext) {bound : List TypeExpr},
      HasType ccsRecCalc free bound (context.fill source) (.base "Guard") → isObjectPattern (context.fill source) = true →
      ∃ inner, (∃ name, context = .apply "CAct" [name] inner []) ∨ (∃ name, context = .apply "CCoAct" [name] inner []) ∨
        context = .apply "CTau" [] inner []
  | .hole, _, typed, _ => absurd (source_proc generator typed) (by decide)
  | .apply label before inner after, _, typed, object => by
      simp only [OneHoleContext.fill] at typed object
      have middleObject := isObject_apply_member object
      obtain ⟨rule, member, labelIs, -, typeIs, arguments⟩ := hasType_apply_inversion typed
      simp only [ccsRecCalc, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [ccsCalc, callRule, constZeroRule, constSuccRule, argumentsNilRule, argumentsConsRule] at typeIs
      · obtain rfl : label = "CAct" := by simpa [ccsCalc] using labelIs
        rcases two_arguments arguments with ⟨-, -, expected, found, middleTyped⟩ | ⟨⟨name, rfl⟩, rfl, -⟩
        · simp only [parameterType?, Option.some.injEq] at found
          subst found
          exact (no_law_in_callPart generator inner (by decide) middleTyped middleObject).elim
        · exact ⟨inner, .inl ⟨name, rfl⟩⟩
      · obtain rfl : label = "CCoAct" := by simpa [ccsCalc] using labelIs
        rcases two_arguments arguments with ⟨-, -, expected, found, middleTyped⟩ | ⟨⟨name, rfl⟩, rfl, -⟩
        · simp only [parameterType?, Option.some.injEq] at found
          subst found
          exact (no_law_in_callPart generator inner (by decide) middleTyped middleObject).elim
        · exact ⟨inner, .inr (.inl ⟨name, rfl⟩)⟩
      · obtain rfl : label = "CTau" := by simpa [ccsCalc] using labelIs
        obtain ⟨rfl, rfl, -⟩ := one_argument arguments
        exact ⟨inner, .inr (.inr rfl)⟩
  | .lambda _ _, _, typed, _ => by cases typed
  | .multiLambda _ _ _, _, typed, _ => by cases typed
  | .substBody _ _, _, _, object => by simp [OneHoleContext.fill, isObjectPattern] at object
  | .substReplacement _ _, _, _, object => by simp [OneHoleContext.fill, isObjectPattern] at object
  | .collection _ _ _ _ _, _, typed, _ => by
      simp only [OneHoleContext.fill] at typed
      obtain ⟨-, sortIs, -⟩ := ccsRecBlockLanguage.bag_members typed
      exact absurd sortIs (by decide)

/-- **A law between summands is a reordering**: a law whose source and target have the type of the argument of a
named multiset reorders a bag. -/
theorem generator_summands {free : FreeTypeContext} {bound : List TypeExpr} (baseContext : BaseContext free bound)
    {source target : Pattern} (generator : BlockGenerator ccsRecCalc ccsBlock source target) {elementSort : String}
    (other : elementSort ≠ "Proc")
    (carrier : ∃ rule ∈ ccsRecCalc.terms, ∃ parameter ∈ rule.params,
      CollectionTypeOccurs .hashBag (.base elementSort) parameter.typeExpr)
    (sourceTyped : HasType ccsRecCalc free bound source (.collection .hashBag (.base elementSort)))
    (targetTyped : HasType ccsRecCalc free bound target (.collection .hashBag (.base elementSort)))
    (targetObject : isObjectPattern target = true) :
    ∃ guards guards', source = .collection .hashBag guards none ∧ target = .collection .hashBag guards' none ∧
      guards.Perm guards' := by
  have structural : Structural ccsBlock (fun pattern => pattern) := ⟨fun _ _ _ => by simp, rfl⟩
  have derived : DerivedInstance ccsRecCalc source target :=
    generator_at_multiset (block := ccsBlock) structural (fun _ arguments => ⟨arguments, rfl⟩) baseContext generator
      ⟨elementSort, other, rfl, carrier⟩ sourceTyped targetTyped targetObject
  have membersTyped : ∀ {elements : List Pattern},
      HasType ccsRecCalc free bound (.collection .hashBag elements none) (.collection .hashBag (.base elementSort)) →
      ∀ element ∈ elements, HasType ccsRecCalc free bound element (.base elementSort) := by
    intro elements typed element inside
    rcases hasType_collection_inversion typed with ⟨elementType, typeIs, elementsTyped⟩ | ⟨_, _, _, _, _, typeIs, _⟩
    · simp only [TypeExpr.collection.injEq, true_and] at typeIs
      subst typeIs
      exact elementsHaveType_iff.mp elementsTyped element inside
    · cases typeIs
  cases derived with
  | bagPerm _ _ permutation => exact ⟨_, _, rfl, rfl, permutation⟩
  | setPerm declaration kindTyped _ => exact absurd kindTyped (ccsRecBlockLanguage.no_set_rule declaration)
  | setDedup declaration kindTyped => exact absurd kindTyped (ccsRecBlockLanguage.no_set_rule declaration)
  | @flatten _ _ _ pre inner post algebraRule _ _ =>
      obtain ⟨rfl, -⟩ := ccsRecBlockLanguage.algebra_shape algebraRule
      have innerTyped := membersTyped sourceTyped (.collection .hashBag inner none) (by simp)
      exact absurd (ccsRecBlockLanguage.bag_members innerTyped).2.1 other
  | @singleton _ _ _ element algebraRule _ _ =>
      obtain ⟨rfl, -⟩ := ccsRecBlockLanguage.algebra_shape algebraRule
      obtain ⟨kind', elements, rest, rfl⟩ := collection_of_typed baseContext targetTyped targetObject
      have elementTyped := membersTyped sourceTyped _ (List.mem_singleton_self _)
      exact absurd (ccsRecBlockLanguage.bag_members elementTyped).2.1 other
  | @unitElim _ _ _ unit pre post algebraRule declaredUnit _ =>
      obtain ⟨rfl, unitIs⟩ := ccsRecBlockLanguage.algebra_shape algebraRule
      rw [declaredUnit, Option.some.injEq] at unitIs
      subst unitIs
      have unitTyped := membersTyped sourceTyped (.apply ccsBlock.unit []) (by simp)
      obtain ⟨unitRule, unitMember, labelIs, -, typeIs, -⟩ := hasType_apply_inversion unitTyped
      simp only [TypeExpr.base.injEq] at typeIs
      exact absurd (typeIs.trans (ccsRecBlockLanguage.unitShape unitRule unitMember labelIs.symm)) other
  | @emptyUnit _ _ _ unit algebraRule declaredUnit _ =>
      obtain ⟨-, unitIs⟩ := ccsRecBlockLanguage.algebra_shape algebraRule
      rw [declaredUnit, Option.some.injEq] at unitIs
      subst unitIs
      exact (apply_not_collection targetTyped).elim

/-- **The positions where a law applies in a process**: the process itself, a member of a parallel bag, the body of
a restriction, the summands of a sum, or the continuation of a guard. -/
inductive LawPosition : OneHoleContext → Prop where
  | root : LawPosition .hole
  | member (before after : List Pattern) {inner : OneHoleContext} (position : LawPosition inner) :
      LawPosition (.collection .hashBag before inner after none)
  | restriction (binder : Option String) {inner : OneHoleContext} (position : LawPosition inner) :
      LawPosition (.apply "CNu" [] (.lambda binder inner) [])
  | summands : LawPosition (.apply "CSum" [] .hole [])
  | act (before after : List Pattern) (name : Pattern) (inner : OneHoleContext) :
      LawPosition (.apply "CSum" [] (.collection .hashBag before (.apply "CAct" [name] inner []) after none) [])
  | coact (before after : List Pattern) (name : Pattern) (inner : OneHoleContext) :
      LawPosition (.apply "CSum" [] (.collection .hashBag before (.apply "CCoAct" [name] inner []) after none) [])
  | silent (before after : List Pattern) (inner : OneHoleContext) :
      LawPosition (.apply "CSum" [] (.collection .hashBag before (.apply "CTau" [] inner []) after none) [])

/-- An application or a collection has no abstraction type. -/
theorem source_not_arrow {source target : Pattern} (generator : BlockGenerator ccsRecCalc ccsBlock source target)
    {free : FreeTypeContext} {bound : List TypeExpr} {domain codomain : TypeExpr}
    (typed : HasType ccsRecCalc free bound source (.arrow domain codomain)) : False := by
  rcases generator_source_head generator with ⟨constructor, arguments, rfl⟩ | ⟨kind, elements, rest, rfl⟩
  · obtain ⟨_, _, _, _, typeIs, _⟩ := hasType_apply_inversion typed
    cases typeIs
  · rcases hasType_collection_inversion typed with ⟨_, typeIs, _⟩ | ⟨_, _, _, _, _, typeIs, _⟩ <;> cases typeIs

/-- **A law applies only at a law position** of a typed object process. -/
theorem lawPosition {free : FreeTypeContext} {source target : Pattern}
    (generator : BlockGenerator ccsRecCalc ccsBlock source target) :
    ∀ (context : OneHoleContext) {bound : List TypeExpr}, BaseContext free bound →
      HasType ccsRecCalc free bound (context.fill source) (.base "Proc") → isObjectPattern (context.fill source) = true →
      LawPosition context
  | .hole, _, _, _, _ => .root
  | .collection kind before inner after rest, bound, baseContext, typed, object => by
      simp only [OneHoleContext.fill] at typed object
      obtain ⟨rfl, -, members⟩ := ccsRecBlockLanguage.bag_members typed
      cases bag_tail_none object
      exact .member before after (lawPosition generator inner baseContext
        (elementsHaveType_iff.mp members _ (by simp)) (isObject_collection_member object))
  | .apply label before inner after, bound, baseContext, typed, object => by
      simp only [OneHoleContext.fill] at typed object
      have middleObject := isObject_apply_member object
      obtain ⟨rule, member, labelIs, notBare, typeIs, arguments⟩ := hasType_apply_inversion typed
      simp only [ccsRecCalc, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [ccsCalc, callRule, constZeroRule, constSuccRule, argumentsNilRule, argumentsConsRule] at typeIs
      · -- inaction has no argument
        cases before <;> simp only [List.nil_append, List.cons_append] at arguments <;> cases arguments
      · -- the parallel bag is a bare collection
        exact (notBare ⟨_, _, _, rfl⟩).elim
      · -- a sum: its summands, or the continuation of a guard
        obtain rfl : label = "CSum" := by simpa [ccsCalc] using labelIs
        obtain ⟨rfl, rfl, expected, found, middleTyped⟩ := one_argument arguments
        simp only [parameterType?, Option.some.injEq] at found
        subst found
        match inner, middleTyped, middleObject with
        | .hole, _, _ => exact .summands
        | .collection kind pre guard post rest, middleTyped, middleObject =>
            simp only [OneHoleContext.fill] at middleTyped middleObject
            cases bag_tail_none middleObject
            rcases hasType_collection_inversion middleTyped with ⟨elementType, typeIs, elementsTyped⟩ |
              ⟨_, _, _, _, _, typeIs, _⟩
            · simp only [TypeExpr.bag, TypeExpr.collection.injEq] at typeIs
              obtain ⟨rfl, rfl⟩ := typeIs
              obtain ⟨inner', shape⟩ := guard_hole generator guard
                (elementsHaveType_iff.mp elementsTyped _ (by simp)) (isObject_collection_member middleObject)
              rcases shape with ⟨name, rfl⟩ | ⟨name, rfl⟩ | rfl
              · exact .act pre post name inner'
              · exact .coact pre post name inner'
              · exact .silent pre post inner'
            · cases typeIs
        | .apply _ _ _ _, middleTyped, _ => exact (apply_not_collection middleTyped).elim
        | .lambda _ _, middleTyped, _ => cases middleTyped
        | .multiLambda _ _ _, middleTyped, _ => cases middleTyped
        | .substBody _ _, _, middleObject => simp [OneHoleContext.fill, isObjectPattern] at middleObject
        | .substReplacement _ _, _, middleObject => simp [OneHoleContext.fill, isObjectPattern] at middleObject
      · -- a restriction: its body
        obtain rfl : label = "CNu" := by simpa [ccsCalc] using labelIs
        obtain ⟨rfl, rfl, expected, found, middleTyped⟩ := one_argument arguments
        simp only [parameterType?, Option.some.injEq] at found
        subst found
        match inner, middleTyped, middleObject with
        | .hole, middleTyped, _ => exact (source_not_arrow generator middleTyped).elim
        | .lambda binder inner', middleTyped, middleObject =>
            simp only [OneHoleContext.fill] at middleTyped middleObject
            cases middleTyped with
            | lambda bodyTyped =>
                exact .restriction binder (lawPosition generator inner' (baseContext.cons "Name") bodyTyped
                  (by simpa [isObjectPattern] using middleObject))
        | .apply _ _ _ _, middleTyped, _ =>
            obtain ⟨_, _, _, _, typeIs, _⟩ := hasType_apply_inversion middleTyped
            cases typeIs
        | .collection _ _ _ _ _, middleTyped, _ =>
            rcases hasType_collection_inversion middleTyped with ⟨_, typeIs, _⟩ | ⟨_, _, _, _, _, typeIs, _⟩ <;>
              cases typeIs
        | .multiLambda _ _ _, middleTyped, _ => cases middleTyped
        | .substBody _ _, _, middleObject => simp [OneHoleContext.fill, isObjectPattern] at middleObject
        | .substReplacement _ _, _, middleObject => simp [OneHoleContext.fill, isObjectPattern] at middleObject
      · -- a call: its constant and its arguments hold no process
        rcases two_arguments arguments with ⟨-, -, expected, found, middleTyped⟩ | ⟨-, -, expected, found, middleTyped⟩
        · simp only [parameterType?, Option.some.injEq] at found
          subst found
          exact (no_law_in_callPart generator inner (by decide) middleTyped middleObject).elim
        · simp only [parameterType?, Option.some.injEq] at found
          subst found
          exact (no_law_in_callPart generator inner (by decide) middleTyped middleObject).elim
  | .lambda _ _, _, _, typed, _ => by cases typed
  | .multiLambda _ _ _, _, _, typed, _ => by cases typed
  | .substBody _ _, _, _, _, object => by simp [OneHoleContext.fill, isObjectPattern] at object
  | .substReplacement _ _, _, _, _, object => by simp [OneHoleContext.fill, isObjectPattern] at object

/-! ## Matching closed under the positions -/

/-- **Under a restriction**, matching bodies give matching restrictions. -/
theorem matched_restrict {first second : Pattern} (matched : Matched definitions first second)
    (binder binder' : Option String) :
    Matched definitions (.apply "CNu" [.lambda binder first]) (.apply "CNu" [.lambda binder' second]) := by
  intro action target step
  obtain ⟨inner, innerTarget, innerStep, seen, rfl⟩ := lstep_restriction_inv step
  obtain ⟨innerTarget', step', same⟩ := matched innerStep
  exact ⟨_, .res binder' step' seen, equationEquiv_fill (.apply "CNu" [] (.lambda none .hole) []) same⟩

/-- **A transition of a sum** performs one of its summands. -/
theorem lstep_sum_inv {guards : List Pattern} {action : Action} {target : Pattern}
    (step : LStep definitions (.apply "CSum" [.collection .hashBag guards none]) action target) :
    ∃ k, ∃ hk : k < guards.length, guardAction guards[k] = some (action, target) := by
  generalize sourceIs : Pattern.apply "CSum" [.collection .hashBag guards none] = source at step
  cases step with
  | offer offered k hk performs =>
      subst sourceIs
      simp only [offers, Option.some.injEq] at offered
      subst offered
      exact ⟨k, hk, performs⟩
  | par => cases sourceIs
  | sync => cases sourceIs
  | res => simp at sourceIs

/-- **Reordering the summands** keeps the transitions, to the same targets. -/
theorem matched_sumPerm {guards guards' : List Pattern} (permutation : guards.Perm guards') :
    Matched definitions (.apply "CSum" [.collection .hashBag guards none])
      (.apply "CSum" [.collection .hashBag guards' none]) := by
  intro action target step
  obtain ⟨k, hk, performs⟩ := lstep_sum_inv step
  obtain ⟨k', hk', same⟩ := List.getElem_of_mem (permutation.mem_iff.mp (List.getElem_mem hk))
  exact ⟨target, .offer rfl k' hk' (by rw [same]; exact performs), .refl _⟩

/-- A guard performing what another performs, to an equivalent continuation. -/
def GuardMatched (guard guard' : Pattern) : Prop :=
  ∀ ⦃action : Action⦄ ⦃continuation : Pattern⦄, guardAction guard = some (action, continuation) →
    ∃ continuation', guardAction guard' = some (action, continuation') ∧
      EquationEquiv (engineBasePremises RelationEnv.empty) ccsRecCalc continuation continuation'

/-- The first summand replaced by one performing what it performs. -/
theorem matched_sumFront {rest : List Pattern} {guard guard' : Pattern} (same : GuardMatched guard guard') :
    Matched definitions (.apply "CSum" [.collection .hashBag (guard :: rest) none])
      (.apply "CSum" [.collection .hashBag (guard' :: rest) none]) := by
  intro action target step
  obtain ⟨k, hk, performs⟩ := lstep_sum_inv step
  cases k with
  | zero =>
      obtain ⟨continuation', performs', related⟩ := same performs
      exact ⟨continuation', .offer (guards := guard' :: rest) rfl 0 (by simp) performs', related⟩
  | succ k =>
      exact ⟨target, .offer (guards := guard' :: rest) rfl (k + 1) (by simpa using hk) (by simpa using performs),
        .refl _⟩

/-- **A summand replaced by one performing what it performs**, to equivalent continuations, keeps the
transitions. -/
theorem matched_sumGuard {before after : List Pattern} {guard guard' : Pattern} (same : GuardMatched guard guard') :
    Matched definitions (.apply "CSum" [.collection .hashBag (before ++ guard :: after) none])
      (.apply "CSum" [.collection .hashBag (before ++ guard' :: after) none]) :=
  (matched_sumPerm List.perm_middle).trans ((matched_sumFront same).trans (matched_sumPerm List.perm_middle.symm))

/-- **A member of a bag replaced by an equivalent one matching it** keeps the transitions. -/
theorem matched_member (admitted : admits definitions = true) {free : FreeTypeContext} {bound : List TypeExpr}
    {element element' : Pattern} {others : List Pattern}
    (typed : HasType ccsRecCalc free bound (.collection .hashBag (element :: others) none) (.base "Proc"))
    (object : isObjectPattern (.collection .hashBag (element :: others) none) = true)
    (typed' : HasType ccsRecCalc free bound element' (.base "Proc")) (object' : isObjectPattern element' = true)
    (forward : Matched definitions element element')
    (same : EquationEquiv (engineBasePremises RelationEnv.empty) ccsRecCalc element element') :
    Matched definitions (.collection .hashBag (element :: others) none)
      (.collection .hashBag (element' :: others) none) := by
  have members := members_of_bag (block := ccsBlock) typed
  have othersMembers : Members ccsRecCalc ccsBlock free bound others :=
    fun member inside => members member (List.mem_cons_of_mem _ inside)
  have replaced : ∀ (front back : List Pattern) {old new : Pattern},
      EquationEquiv (engineBasePremises RelationEnv.empty) ccsRecCalc old new →
      EquationEquiv (engineBasePremises RelationEnv.empty) ccsRecCalc (.collection .hashBag (front ++ old :: back) none)
        (.collection .hashBag (front ++ new :: back) none) :=
    fun front back _ _ related => equationEquiv_fill (.collection .hashBag front .hole back none) related
  have permuted : ∀ {list list' : List Pattern}, list.Perm list' →
      HasType ccsRecCalc free bound (.collection .hashBag list none) (.base "Proc") →
      EquationEquiv (engineBasePremises RelationEnv.empty) ccsRecCalc (.collection .hashBag list none)
        (.collection .hashBag list' none) :=
    fun perm listTyped => bag_result_equivalent perm listTyped
  have consMembers : ∀ {head : Pattern} {list : List Pattern}, HasType ccsRecCalc free bound head (.base "Proc") →
      Members ccsRecCalc ccsBlock free bound list → Members ccsRecCalc ccsBlock free bound (head :: list) :=
    fun headTyped listMembers other inside =>
      (List.mem_cons.mp inside).elim (fun same => same ▸ headTyped) (listMembers other)
  have bagOf : ∀ {list : List Pattern}, Members ccsRecCalc ccsBlock free bound list →
      HasType ccsRecCalc free bound (.collection .hashBag list none) (.base "Proc") :=
    fun listMembers => bag_typed (block := ccsBlock) (rest := none) listMembers
  intro action target step
  obtain ⟨targetTyped, -⟩ := step.typed admitted typed object
  obtain ⟨result, move, rfl⟩ := bagMove_of_step step
  have targetMembers := members_of_bag (block := ccsBlock) targetTyped
  rcases move.result_cases with ⟨member, rest, moved, perm, memberStep, rfl⟩ |
    ⟨first, second, rest, moved, moved', name, perm, firstStep, secondStep, rfl, rfl⟩
  · by_cases isElement : member = element
    · subst isElement
      have restPerm : others.Perm rest := perm.cons_inv
      obtain ⟨moved₁, step₁, sameMoved⟩ := forward memberStep
      obtain ⟨result', step', resultPerm⟩ := step_of_bagMove (definitions := definitions)
        (.one (List.Perm.refl (element' :: others)) step₁) none
      refine ⟨_, step', ?_⟩
      have moved₁Typed := (step₁.typed admitted typed' object').1
      have restMembers : Members ccsRecCalc ccsBlock free bound rest :=
        fun other inside => targetMembers other (List.mem_cons_of_mem _ inside)
      exact .trans _ _ _ (replaced [] rest sameMoved) (.trans _ _ _
        (permuted (restPerm.symm.cons moved₁) (bagOf (consMembers moved₁Typed restMembers)))
        (permuted resultPerm.symm (bagOf (consMembers moved₁Typed othersMembers))))
    · obtain ⟨rest', restPerm, othersPerm⟩ := perm_cons_cons_of_ne perm isElement
      have newPerm : (element' :: others).Perm (member :: element' :: rest') :=
        (othersPerm.cons element').trans (List.Perm.swap _ _ _)
      obtain ⟨result', step', resultPerm⟩ := step_of_bagMove (.one newPerm memberStep) none
      refine ⟨_, step', ?_⟩
      have movedTyped := targetMembers _ List.mem_cons_self
      have rest'Members : Members ccsRecCalc ccsBlock free bound rest' :=
        fun other inside => othersMembers other (othersPerm.mem_iff.mpr (List.mem_cons_of_mem _ inside))
      exact .trans _ _ _ (permuted (restPerm.cons moved) targetTyped) (.trans _ _ _ (replaced [moved] rest' same)
        (permuted resultPerm.symm (bagOf (consMembers movedTyped (consMembers typed' rest'Members)))))
  · by_cases firstIs : first = element
    · subst firstIs
      have othersPerm : others.Perm (second :: rest) := perm.cons_inv
      obtain ⟨moved₁, step₁, sameMoved⟩ := forward firstStep
      obtain ⟨result', step', resultPerm⟩ := step_of_bagMove (.two (othersPerm.cons element') step₁ secondStep) none
      refine ⟨_, step', ?_⟩
      have moved₁Typed := (step₁.typed admitted typed' object').1
      have tailMembers : Members ccsRecCalc ccsBlock free bound (moved' :: rest) :=
        fun other inside => targetMembers other (List.mem_cons_of_mem _ inside)
      exact .trans _ _ _ (replaced [] (moved' :: rest) sameMoved)
        (permuted resultPerm.symm (bagOf (consMembers moved₁Typed tailMembers)))
    · by_cases secondIs : second = element
      · subst secondIs
        have othersPerm : others.Perm (first :: rest) := (perm.trans (List.Perm.swap _ _ _)).cons_inv
        obtain ⟨moved₂, step₂, sameMoved⟩ := forward secondStep
        have newPerm : (element' :: others).Perm (first :: element' :: rest) :=
          (othersPerm.cons element').trans (List.Perm.swap _ _ _)
        obtain ⟨result', step', resultPerm⟩ := step_of_bagMove (.two newPerm firstStep step₂) none
        refine ⟨_, step', ?_⟩
        have moved₂Typed := (step₂.typed admitted typed' object').1
        have movedTyped := targetMembers _ List.mem_cons_self
        have restMembers : Members ccsRecCalc ccsBlock free bound rest :=
          fun other inside => targetMembers other (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ inside))
        exact .trans _ _ _ (replaced [moved] rest sameMoved)
          (permuted resultPerm.symm (bagOf (consMembers movedTyped (consMembers moved₂Typed restMembers))))
      · obtain ⟨rest₁, restPerm₁, othersPerm₁⟩ := perm_cons_cons_of_ne perm firstIs
        obtain ⟨rest₂, restPerm₂, restPerm₁'⟩ := perm_cons_cons_of_ne restPerm₁.symm secondIs
        have othersPerm : others.Perm (first :: second :: rest₂) := othersPerm₁.trans (restPerm₁'.cons first)
        have newPerm : (element' :: others).Perm (first :: second :: element' :: rest₂) := by
          refine (othersPerm.cons element').trans ?_
          perm_ac
        obtain ⟨result', step', resultPerm⟩ := step_of_bagMove (.two newPerm firstStep secondStep) none
        refine ⟨_, step', ?_⟩
        have movedTyped := targetMembers _ List.mem_cons_self
        have moved'Typed := targetMembers _ (List.mem_cons_of_mem _ List.mem_cons_self)
        have rest₂Members : Members ccsRecCalc ccsBlock free bound rest₂ := fun other inside =>
          othersMembers other (othersPerm.mem_iff.mpr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ inside)))
        exact .trans _ _ _ (permuted ((restPerm₂.cons moved').cons moved) targetTyped)
          (.trans _ _ _ (replaced [moved, moved'] rest₂ same) (permuted resultPerm.symm
            (bagOf (consMembers movedTyped (consMembers moved'Typed (consMembers typed' rest₂Members))))))

/-! ## Each law at the root -/

/-- A bag of no member has no transition. -/
theorem emptyBag_no_step {action : Action} {target : Pattern} :
    ¬ LStep definitions (.collection .hashBag [] none) action target := by
  intro step
  obtain ⟨result, move, -⟩ := bagMove_of_step step
  cases move with
  | one perm => exact absurd perm.length_eq (by simp)
  | two perm => exact absurd perm.length_eq (by simp)

/-- **Each law matches transitions where it applies at the root**, both ways, between typed object processes. -/
theorem generator_matched (admitted : admits definitions = true) {free : FreeTypeContext} {bound : List TypeExpr}
    {source target : Pattern} (generator : BlockGenerator ccsRecCalc ccsBlock source target)
    (sourceTyped : HasType ccsRecCalc free bound source (.base "Proc"))
    (targetTyped : HasType ccsRecCalc free bound target (.base "Proc"))
    (sourceObject : isObjectPattern source = true) (targetObject : isObjectPattern target = true) :
    Matched definitions source target ∧ Matched definitions target source := by
  have restrictedNil : ∀ {binder : Option String} action target,
      ¬ LStep definitions (.apply "CNu" [.lambda binder (.apply "CNil" [])]) action target :=
    fun _ _ => restriction_no_step (fun _ _ => nil_no_step)
  cases generator with
  | nil binder => exact ⟨matched_still restrictedNil, matched_still fun _ _ => nil_no_step⟩
  | nilReverse => exact ⟨matched_still fun _ _ => nil_no_step, matched_still restrictedNil⟩
  | extrusion members selected binder body inside chosen =>
      have membersTyped := members_of_bag (block := ccsBlock) sourceTyped
      have objects := bag_objects sourceObject
      have selectedTyped := membersTyped _ (List.getElem_mem inside)
      have selectedObject := objects _ (List.getElem_mem inside)
      rw [chosen] at selectedTyped selectedObject
      cases restriction_binder (block := ccsBlock) selectedTyped
      rw [isObject_restriction] at selectedObject
      have perm : members.Perm (.apply "CNu" [.lambda none body] :: members.eraseIdx selected) := by
        have reordered := perm_getElem_eraseIdx members selected inside
        rwa [chosen] at reordered
      have inOthers : ∀ element ∈ members.eraseIdx selected, element ∈ members :=
        fun element member => perm.mem_iff.mpr (List.mem_cons_of_mem _ member)
      have frontTyped := typed_of_members sourceTyped fun element member => perm.mem_iff.mpr member
      have frontObject : isObjectPattern (.collection .hashBag
          (.apply "CNu" [.lambda none body] :: members.eraseIdx selected) none) = true :=
        isObject_bag.mpr fun element member => objects element (perm.mem_iff.mpr member)
      obtain ⟨out, back⟩ := matched_extrusion admitted (definitions := definitions)
        (restriction_body (block := ccsBlock) selectedTyped) selectedObject
        (fun element member => membersTyped element (inOthers element member))
        (fun element member => objects element (inOthers element member))
      exact ⟨(matched_bagPerm admitted perm sourceTyped sourceObject).trans out,
        back.trans (matched_bagPerm admitted perm.symm frontTyped frontObject)⟩
  | extrusionReverse binder members selected originals inside othersEq =>
      cases restriction_binder (block := ccsBlock) sourceTyped
      have bodyTyped := restriction_body (block := ccsBlock) sourceTyped
      have bodyObject : isObjectPattern (.collection .hashBag members none) = true := by
        rw [isObject_restriction] at sourceObject; exact sourceObject
      have membersTyped := members_of_bag (block := ccsBlock) bodyTyped
      have objects := bag_objects bodyObject
      have perm : members.Perm (members[selected] :: originals.map (liftBVars 0 1)) := by
        have reordered := perm_getElem_eraseIdx members selected inside
        rwa [othersEq] at reordered
      have targetMembers := members_of_bag (block := ccsBlock) targetTyped
      have targetObjects := bag_objects targetObject
      have frontTyped := typed_of_members bodyTyped fun element member => perm.mem_iff.mpr member
      have frontObject : isObjectPattern
          (.collection .hashBag (members[selected] :: originals.map (liftBVars 0 1)) none) = true :=
        isObject_bag.mpr fun element member => objects element (perm.mem_iff.mpr member)
      obtain ⟨out, back⟩ := matched_extrusion admitted (definitions := definitions)
        (membersTyped _ (List.getElem_mem inside)) (objects _ (List.getElem_mem inside))
        (fun element member => targetMembers element (List.mem_cons_of_mem _ member))
        (fun element member => targetObjects element (List.mem_cons_of_mem _ member))
      exact ⟨(matched_restrict (matched_bagPerm admitted perm bodyTyped bodyObject) none none).trans back,
        out.trans (matched_restrict (matched_bagPerm admitted perm.symm frontTyped frontObject) none none)⟩
  | exchange outerBinder innerBinder body => exact matched_exchange admitted sourceTyped sourceObject
  | emptyUnit label listed =>
      simp at listed
      subst listed
      exact ⟨matched_still fun _ _ => emptySum_no_step, matched_still restrictedNil⟩
  | emptyUnitReverse label listed binder =>
      simp at listed
      subst listed
      exact ⟨matched_still restrictedNil, matched_still fun _ _ => emptySum_no_step⟩
  | derived derivedInstance =>
      cases derivedInstance with
      | bagPerm _ _ permutation =>
          exact ⟨matched_bagPerm admitted permutation sourceTyped sourceObject,
            matched_bagPerm admitted permutation.symm targetTyped targetObject⟩
      | setPerm declaration kindTyped _ => exact absurd kindTyped (ccsRecBlockLanguage.no_set_rule declaration)
      | setDedup declaration kindTyped => exact absurd kindTyped (ccsRecBlockLanguage.no_set_rule declaration)
      | @flatten _ _ _ pre inner post algebraRule _ _ =>
          obtain ⟨rfl, -⟩ := ccsRecBlockLanguage.algebra_shape algebraRule
          have front : (pre ++ .collection .hashBag inner none :: post).Perm
              (.collection .hashBag inner none :: (pre ++ post)) := List.perm_middle
          have flat : (inner ++ (pre ++ post)).Perm (pre ++ inner ++ post) := by perm_ac
          have frontTyped := typed_of_members sourceTyped fun element member => front.mem_iff.mpr member
          have frontObject : isObjectPattern
              (.collection .hashBag (.collection .hashBag inner none :: (pre ++ post)) none) = true :=
            isObject_bag.mpr fun element member => bag_objects sourceObject element (front.mem_iff.mpr member)
          have flatTyped := typed_of_members targetTyped fun element member => flat.mem_iff.mp member
          have flatObject : isObjectPattern (.collection .hashBag (inner ++ (pre ++ post)) none) = true :=
            isObject_bag.mpr fun element member => bag_objects targetObject element (flat.mem_iff.mp member)
          obtain ⟨out, back⟩ := matched_flatten admitted (definitions := definitions) frontTyped frontObject
          exact ⟨(matched_bagPerm admitted front sourceTyped sourceObject).trans
              (out.trans (matched_bagPerm admitted flat flatTyped flatObject)),
            (matched_bagPerm admitted flat.symm targetTyped targetObject).trans
              (back.trans (matched_bagPerm admitted front.symm frontTyped frontObject))⟩
      | @singleton _ _ _ element algebraRule _ _ =>
          obtain ⟨rfl, -⟩ := ccsRecBlockLanguage.algebra_shape algebraRule
          exact matched_singleton admitted targetTyped targetObject
      | @unitElim _ _ _ unit pre post algebraRule declaredUnit _ =>
          obtain ⟨rfl, unitIs⟩ := ccsRecBlockLanguage.algebra_shape algebraRule
          rw [declaredUnit, Option.some.injEq] at unitIs
          subst unitIs
          exact matched_unitElim admitted sourceTyped sourceObject
      | @emptyUnit _ _ _ unit algebraRule declaredUnit _ =>
          obtain ⟨rfl, unitIs⟩ := ccsRecBlockLanguage.algebra_shape algebraRule
          rw [declaredUnit, Option.some.injEq] at unitIs
          subst unitIs
          exact ⟨matched_still fun _ _ => emptyBag_no_step, matched_still fun _ _ => nil_no_step⟩

/-! ## A law in context -/

/-- A prefix with equivalent continuations performs what the other performs. -/
theorem guardMatched_prefix {label : String} (isPrefix : label = "CAct" ∨ label = "CCoAct") {name first second : Pattern}
    (related : EquationEquiv (engineBasePremises RelationEnv.empty) ccsRecCalc first second) :
    GuardMatched (.apply label [name, first]) (.apply label [name, second]) := by
  intro action continuation performs
  rcases isPrefix with rfl | rfl <;>
  · simp only [guardAction, Option.some.injEq, Prod.mk.injEq] at performs
    obtain ⟨rfl, rfl⟩ := performs
    exact ⟨second, rfl, related⟩

/-- A silent prefix with an equivalent continuation performs what the other performs. -/
theorem guardMatched_tau {first second : Pattern}
    (related : EquationEquiv (engineBasePremises RelationEnv.empty) ccsRecCalc first second) :
    GuardMatched (.apply "CTau" [first]) (.apply "CTau" [second]) := by
  intro action continuation performs
  simp only [guardAction, Option.some.injEq, Prod.mk.injEq] at performs
  obtain ⟨rfl, rfl⟩ := performs
  exact ⟨second, rfl, related⟩

/-- **A law applied at a law position of a typed object process matches transitions**, both ways. -/
theorem matched_at (admitted : admits definitions = true) {free : FreeTypeContext} {source target : Pattern}
    (generator : EquationGenerator (engineBasePremises RelationEnv.empty) ccsRecCalc source target)
    {context : OneHoleContext} (position : LawPosition context) :
    ∀ {bound : List TypeExpr}, BaseContext free bound →
      HasType ccsRecCalc free bound (context.fill source) (.base "Proc") →
      HasType ccsRecCalc free bound (context.fill target) (.base "Proc") →
      isObjectPattern (context.fill source) = true → isObjectPattern (context.fill target) = true →
      Matched definitions (context.fill source) (context.fill target) ∧
        Matched definitions (context.fill target) (context.fill source) := by
  have shape := generator_shape (block := ccsBlock) generator
  have related : ∀ (inner : OneHoleContext), EquationEquiv (engineBasePremises RelationEnv.empty) ccsRecCalc
      (inner.fill source) (inner.fill target) := fun inner => .rel _ _ (.inContext inner generator)
  induction position with
  | root =>
      intro bound _ sourceTyped targetTyped sourceObject targetObject
      exact generator_matched admitted shape sourceTyped targetTyped sourceObject targetObject
  | @member before after inner _ recurse =>
      intro bound baseContext sourceTyped targetTyped sourceObject targetObject
      simp only [OneHoleContext.fill] at sourceTyped targetTyped sourceObject targetObject ⊢
      have middle : ∀ (element : Pattern), (before ++ element :: after).Perm (element :: (before ++ after)) :=
        fun _ => List.perm_middle
      have memberTyped := members_of_bag (block := ccsBlock) sourceTyped (inner.fill source) (by simp)
      have memberTyped' := members_of_bag (block := ccsBlock) targetTyped (inner.fill target) (by simp)
      have memberObject := isObject_collection_member sourceObject
      have memberObject' := isObject_collection_member targetObject
      obtain ⟨forward, backward⟩ := recurse baseContext memberTyped memberTyped' memberObject memberObject'
      have frontTyped := typed_of_members sourceTyped fun element member => (middle _).mem_iff.mpr member
      have frontTyped' := typed_of_members targetTyped fun element member => (middle _).mem_iff.mpr member
      have frontObject : isObjectPattern (.collection .hashBag (inner.fill source :: (before ++ after)) none) = true :=
        isObject_bag.mpr fun element member => bag_objects sourceObject element ((middle _).mem_iff.mpr member)
      have frontObject' : isObjectPattern (.collection .hashBag (inner.fill target :: (before ++ after)) none) = true :=
        isObject_bag.mpr fun element member => bag_objects targetObject element ((middle _).mem_iff.mpr member)
      exact ⟨(matched_bagPerm admitted (middle _) sourceTyped sourceObject).trans
          ((matched_member admitted frontTyped frontObject memberTyped' memberObject' forward (related inner)).trans
            (matched_bagPerm admitted (middle _).symm frontTyped' frontObject')),
        (matched_bagPerm admitted (middle _) targetTyped targetObject).trans
          ((matched_member admitted frontTyped' frontObject' memberTyped memberObject backward
            (.symm _ _ (related inner))).trans (matched_bagPerm admitted (middle _).symm frontTyped frontObject))⟩
  | @restriction binder inner _ recurse =>
      intro bound baseContext sourceTyped targetTyped sourceObject targetObject
      simp only [OneHoleContext.fill, List.nil_append] at sourceTyped targetTyped sourceObject targetObject ⊢
      rw [isObject_restriction] at sourceObject targetObject
      obtain ⟨forward, backward⟩ := recurse (baseContext.cons "Name") (restriction_body (block := ccsBlock) sourceTyped)
        (restriction_body (block := ccsBlock) targetTyped) sourceObject targetObject
      exact ⟨matched_restrict forward binder binder, matched_restrict backward binder binder⟩
  | summands =>
      intro bound baseContext sourceTyped targetTyped sourceObject targetObject
      simp only [OneHoleContext.fill, List.nil_append] at sourceTyped targetTyped sourceObject targetObject ⊢
      obtain ⟨rule, member, labelIs, -, -, parameterName, elementSort, argument, params, other, argumentsIs,
        argumentTyped⟩ := multiset_argument (block := ccsBlock) sourceTyped (by simp)
      obtain ⟨rule', member', labelIs', -, -, parameterName', elementSort', argument', params', -, argumentsIs',
        argumentTyped'⟩ := multiset_argument (block := ccsBlock) targetTyped (by simp)
      obtain rfl := ccsRecBlockLanguage.rule_eq_of_label member member' (labelIs.trans labelIs'.symm)
      rw [params] at params'
      simp only [List.cons.injEq, TermParam.simple.injEq, TypeExpr.collection.injEq, TypeExpr.base.injEq, and_true,
        true_and] at params'
      obtain ⟨-, rfl⟩ := params'
      simp only [List.cons.injEq, and_true] at argumentsIs argumentsIs'
      subst argumentsIs argumentsIs'
      have targetObject' : isObjectPattern target = true :=
        isObject_apply_member (before := []) (after := []) targetObject
      obtain ⟨guards, guards', rfl, rfl, permutation⟩ := generator_summands baseContext shape other
        ⟨rule, member, .simple parameterName (.collection .hashBag (.base elementSort)),
          by rw [params]; exact List.mem_singleton_self _, .here⟩ argumentTyped argumentTyped' targetObject'
      exact ⟨matched_sumPerm permutation, matched_sumPerm permutation.symm⟩
  | act before after name inner =>
      intro bound _ _ _ _ _
      simp only [OneHoleContext.fill, List.nil_append, List.cons_append]
      exact ⟨matched_sumGuard (guardMatched_prefix (.inl rfl) (related inner)),
        matched_sumGuard (guardMatched_prefix (.inl rfl) (.symm _ _ (related inner)))⟩
  | coact before after name inner =>
      intro bound _ _ _ _ _
      simp only [OneHoleContext.fill, List.nil_append, List.cons_append]
      exact ⟨matched_sumGuard (guardMatched_prefix (.inr rfl) (related inner)),
        matched_sumGuard (guardMatched_prefix (.inr rfl) (.symm _ _ (related inner)))⟩
  | silent before after inner =>
      intro bound _ _ _ _ _
      simp only [OneHoleContext.fill, List.nil_append]
      exact ⟨matched_sumGuard (guardMatched_tau (related inner)),
        matched_sumGuard (guardMatched_tau (.symm _ _ (related inner)))⟩

/-! ## Chains of laws -/

/-- **A chain of laws through processes matches transitions**, both ways, from an object. -/
theorem matched_of_procEquiv (admitted : admits definitions = true) {free : FreeTypeContext} {bound : List TypeExpr}
    (baseContext : BaseContext free bound) {first second : Pattern}
    (equivalent : ProcEquiv ccsRecCalc ccsBlock free bound first second) :
    isObjectPattern first = true → Matched definitions first second ∧ Matched definitions second first := by
  induction equivalent with
  | rel source target step =>
      intro sourceObject
      have targetObject : isObjectPattern target = true := by
        rw [← step_isObject (block := ccsBlock) step.step]; exact sourceObject
      obtain ⟨stepped, sourceTyped, targetTyped⟩ := step
      cases stepped with
      | inContext context generator =>
          exact matched_at admitted generator
            (lawPosition (generator_shape (block := ccsBlock) generator) context baseContext sourceTyped sourceObject)
            baseContext sourceTyped targetTyped sourceObject targetObject
  | refl => intro _; exact ⟨.refl _, .refl _⟩
  | symm _ _ chain recurse =>
      intro object
      obtain ⟨forward, backward⟩ := recurse (by
        rw [equationEquiv_isObject (block := ccsBlock) (SortedEquiv.toEquationEquiv chain)]; exact object)
      exact ⟨backward, forward⟩
  | trans _ _ _ left _ leftRecurse rightRecurse =>
      intro object
      obtain ⟨forward, backward⟩ := leftRecurse object
      obtain ⟨forward', backward'⟩ := rightRecurse (by
        rw [← equationEquiv_isObject (block := ccsBlock) (SortedEquiv.toEquationEquiv left)]; exact object)
      exact ⟨forward.trans forward', backward'.trans backward⟩

/-! ## Strong bisimilarity -/

/-- **A strong bisimulation**: related processes match each other's transitions, to related targets. -/
def Bisimulation (definitions : List Definition) (relation : Pattern → Pattern → Prop) : Prop :=
  ∀ ⦃first second : Pattern⦄, relation first second →
    (∀ ⦃action : Action⦄ ⦃target : Pattern⦄, LStep definitions first action target →
      ∃ target', LStep definitions second action target' ∧ relation target target') ∧
    (∀ ⦃action : Action⦄ ⦃target' : Pattern⦄, LStep definitions second action target' →
      ∃ target, LStep definitions first action target ∧ relation target target')

/-- **Strong bisimilarity**: related by a strong bisimulation. -/
def Bisimilar (definitions : List Definition) (first second : Pattern) : Prop :=
  ∃ relation, Bisimulation definitions relation ∧ relation first second

/-- Typed object processes with one canonical form. -/
def SameCanon (free : FreeTypeContext) (bound : List TypeExpr) (first second : Pattern) : Prop :=
  HasType ccsRecCalc free bound first (.base "Proc") ∧ HasType ccsRecCalc free bound second (.base "Proc") ∧
    isObjectPattern first = true ∧ isObjectPattern second = true ∧ canon ccsBlock first = canon ccsBlock second

/-- **The static theory is a strong bisimulation**: typed object processes with one canonical form match each
other's transitions, to targets with one canonical form. -/
theorem sameCanon_bisimulation (admitted : admits definitions = true) {free : FreeTypeContext} {bound : List TypeExpr}
    (baseContext : BaseContext free bound) : Bisimulation definitions (SameCanon free bound) := by
  intro first second ⟨firstTyped, secondTyped, firstObject, secondObject, same⟩
  have chain : ProcEquiv ccsRecCalc ccsBlock free bound first second := by
    have toFirst := (canon_sound (block := ccsBlock) baseContext firstTyped).2
    have toSecond := (canon_sound (block := ccsBlock) baseContext secondTyped).2
    rw [same] at toFirst
    exact .trans _ _ _ toFirst (.symm _ _ toSecond)
  obtain ⟨forward, backward⟩ := matched_of_procEquiv admitted baseContext chain firstObject
  constructor
  · intro action target step
    obtain ⟨target', step', equivalent⟩ := forward step
    obtain ⟨targetTyped, targetObject⟩ := step.typed admitted firstTyped firstObject
    obtain ⟨targetTyped', targetObject'⟩ := step'.typed admitted secondTyped secondObject
    exact ⟨target', step', targetTyped, targetTyped', targetObject, targetObject',
      canon_complete (block := ccsBlock) targetObject equivalent⟩
  · intro action target' step'
    obtain ⟨target, step, equivalent⟩ := backward step'
    obtain ⟨targetTyped', targetObject'⟩ := step'.typed admitted secondTyped secondObject
    obtain ⟨targetTyped, targetObject⟩ := step.typed admitted firstTyped firstObject
    exact ⟨target, step, targetTyped, targetTyped', targetObject, targetObject',
      (canon_complete (block := ccsBlock) targetObject' equivalent).symm⟩

/-- **Equivalent typed object processes are strongly bisimilar**: the static theory is contained in strong
bisimilarity. -/
theorem bisimilar_of_equivalent (admitted : admits definitions = true) {free : FreeTypeContext} {bound : List TypeExpr}
    (baseContext : BaseContext free bound) {first second : Pattern}
    (firstTyped : HasType ccsRecCalc free bound first (.base "Proc"))
    (secondTyped : HasType ccsRecCalc free bound second (.base "Proc"))
    (firstObject : isObjectPattern first = true)
    (equivalent : EquationEquiv (engineBasePremises RelationEnv.empty) ccsRecCalc first second) :
    Bisimilar definitions first second := by
  have secondObject : isObjectPattern second = true := by
    rw [← equationEquiv_isObject (block := ccsBlock) equivalent]; exact firstObject
  exact ⟨SameCanon free bound, sameCanon_bisimulation admitted baseContext,
    firstTyped, secondTyped, firstObject, secondObject, canon_complete (block := ccsBlock) firstObject equivalent⟩

end Mettapedia.Languages.ProcessCalculi.CCS.Recursive
