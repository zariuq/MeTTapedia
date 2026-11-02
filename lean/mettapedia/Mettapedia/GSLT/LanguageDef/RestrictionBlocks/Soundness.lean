import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Signature
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Sorted
import Mettapedia.OSLF.MeTTaIL.ContextSubstitution
import Mettapedia.OSLF.MeTTaIL.ScopedMatchingInversion
import Mettapedia.OSLF.MeTTaIL.ScopedEquationExecution
import Mettapedia.GSLT.LanguageDef.EquationSemantics
import Mettapedia.GSLT.LanguageDef.ContextSubstitution
import Mettapedia.GSLT.LanguageDef.TypedSupportSubstitution
import Mettapedia.OSLF.MeTTaIL.CanonicalRenaming

/-!
# Restriction blocks are sound

Over any calculus with restriction (`BlockLanguage`), its declared laws read as equivalences of its static theory:
restriction of inaction, exchange and extrusion, the garbage law `(νx) Q = Q` when `Q` does not use `x`, blocks side
by side, dropping unused restrictions and reordering the block's restrictions. Hence a process is its block
(`decompose_sound`), and every term of every sort is related to its canonical form, of the same sort, by a chain of laws through terms of that
sort (`canon_sound`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)
open Prenex
open Mettapedia.OSLF.MeTTaIL.PatternLexOrder (serList)

variable {language : LanguageDef} {block : Block}

/-! ## Soundness tools -/

open Mettapedia.OSLF.MeTTaIL.ContextSubstitution (substitute lift lift_lift substituteList_eq_map)
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVarsList_eq_map)

/-- **Shifting the context variables is lifting.** -/
theorem substitute_shift (shift : Nat) (pattern : Pattern) :
    ∀ cutoff, substitute (lift cutoff fun index => .bvar (shift + index)) pattern =
      liftBVars cutoff shift pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      intro cutoff
      by_cases below : index < cutoff
      · have notAbove : ¬ index ≥ cutoff := by omega
        simp [substitute, lift, liftBVars, below, notAbove]
      · have above : index ≥ cutoff := by omega
        simp only [substitute, lift, below, if_false, liftBVars, above, if_true, Nat.zero_le,
          Pattern.bvar.injEq]
        omega
  | hfvar name => intro cutoff; rfl
  | happly constructor arguments inductionHypothesis =>
      intro cutoff
      simp only [substitute, substituteList_eq_map, liftBVars, liftBVarsList_eq_map, Pattern.apply.injEq, true_and]
      exact List.map_congr_left fun argument member => inductionHypothesis argument member cutoff
  | hlambda binder body inductionHypothesis =>
      intro cutoff
      simp only [substitute, liftBVars, lift_lift, Pattern.lambda.injEq, true_and]
      rw [Nat.add_comm cutoff 1]
      simpa [Nat.add_comm] using inductionHypothesis (cutoff + 1)
  | hmultiLambda arity binders body inductionHypothesis =>
      intro cutoff
      simp only [substitute, liftBVars, lift_lift, Pattern.multiLambda.injEq, true_and]
      simpa [Nat.add_comm] using inductionHypothesis (cutoff + arity)
  | hsubst body replacement bodyHypothesis replacementHypothesis =>
      intro cutoff
      simp only [substitute, liftBVars, lift_lift, Pattern.subst.injEq]
      exact ⟨by simpa [Nat.add_comm] using bodyHypothesis (cutoff + 1), replacementHypothesis cutoff⟩
  | hcollection kind elements rest inductionHypothesis =>
      intro cutoff
      simp only [substitute, substituteList_eq_map, liftBVars, liftBVarsList_eq_map, Pattern.collection.injEq,
        true_and, and_true]
      exact List.map_congr_left fun element member => inductionHypothesis element member cutoff

open Mettapedia.OSLF.MeTTaIL.RuleBinding (ContextualValue recoverValue? instantiateValue? recoveryAssignment
  occurrenceAssignment variableSpine?)

theorem recovery_one (ambient : Nat) : recoveryAssignment 1 1 ambient [0] = Pattern.bvar := by
  funext index
  by_cases inside : index < 1
  · have zero : index = 0 := by omega
    simp [recoveryAssignment, zero]
  · have recovered : 1 + (index - 1) = index := by omega
    simp [recoveryAssignment, inside, recovered]

theorem occurrence_one : occurrenceAssignment 1 1 [.bvar 0] = Pattern.bvar := by
  funext index
  by_cases inside : index < 1
  · have zero : index = 0 := by omega
    simp [occurrenceAssignment, zero]
  · have recovered : 1 + (index - 1) = index := by omega
    simp [occurrenceAssignment, inside, recovered]

theorem recovery_zero (ambient : Nat) : recoveryAssignment 0 0 ambient [] = Pattern.bvar := by
  funext index
  simp [recoveryAssignment]

theorem occurrence_zero : occurrenceAssignment 0 0 [] = Pattern.bvar := by
  funext index
  simp [occurrenceAssignment]

theorem occurrence_shift : occurrenceAssignment 0 1 [] = fun index => Pattern.bvar (1 + index) := by
  funext index
  simp [occurrenceAssignment]

/-- A body under one binder that may use it is recovered as it is. -/
theorem recoverValue?_one {dependency : TypeExpr} {ambient : Nat} {body : Pattern}
    (wellScoped : body.isWellScopedAt (1 + ambient) = true) :
    recoverValue? [dependency] ambient 1 [.bvar 0] body = some ⟨[dependency], ambient, body⟩ := by
  simp [recoverValue?, wellScoped, variableSpine?, recovery_one, Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute_id,
    instantiateValue?, occurrence_one, Pattern.isWellScopedAt]

/-- The value recovered under one binder reads back as the body. -/
theorem instantiateValue?_one {dependency : TypeExpr} {ambient : Nat} {body : Pattern}
    (wellScoped : body.isWellScopedAt (1 + ambient) = true) :
    instantiateValue? ⟨[dependency], ambient, body⟩ ambient 1 [.bvar 0] = some body := by
  simp [instantiateValue?, wellScoped, occurrence_one, Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute_id,
    Pattern.isWellScopedAt]

/-- A closed component is recovered at the root as it is. -/
theorem recoverValue?_zero {ambient : Nat} {body : Pattern} (wellScoped : body.isWellScopedAt ambient = true) :
    recoverValue? [] ambient 0 [] body = some ⟨[], ambient, body⟩ := by
  simp [recoverValue?, wellScoped, variableSpine?, recovery_zero,
    Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute_id, instantiateValue?, occurrence_zero]

/-- **A closed component read under one more binder is lifted.** -/
theorem instantiateValue?_shift {ambient : Nat} {body : Pattern} (wellScoped : body.isWellScopedAt ambient = true) :
    instantiateValue? ⟨[], ambient, body⟩ ambient 1 [] = some (liftBVars 0 1 body) := by
  have lifted : (liftBVars 0 1 body).isWellScopedAt (1 + ambient) = true := by
    have := Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_isWellScopedAt (cutoff := 0) (shift := 1)
      (ambient := ambient) (pattern := body) (by simpa using wellScoped)
    simpa [Nat.add_comm] using this
  have shifted := substitute_shift 1 body 0
  rw [Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift_zero] at shifted
  simp [instantiateValue?, wellScoped, occurrence_shift, shifted, lifted]

open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.RuleBinding (arguments? dependencies? occurrenceDeclared sitePattern? occurrenceAt?)
open Mettapedia.OSLF.MeTTaIL.ScopedEquationExecution (Orientation orientedRule applyEquationAt mem_applyEquationAt_iff)

/-- **Extrusion, read through its declaration**: a restriction in a bag moves out over the other members, which do
not use it and are read one binder deeper. -/
theorem extrusion_instance {ambient : Nat} {body : Pattern} {others : List Pattern}
    (bodyScoped : body.isWellScopedAt (1 + ambient) = true)
    (othersScoped : (Pattern.collection .hashBag others none).isWellScopedAt ambient = true) :
    .apply block.restrict [.lambda none (.collection .hashBag (body :: others.map (liftBVars 0 1)) none)] ∈
      applyEquationAt language ambient (scopeExtrusionOf block) .forward
        (.collection .hashBag (.apply block.restrict [.lambda none body] :: others) none) := by
  have liftedScoped : (Pattern.collection .hashBag (others.map (liftBVars 0 1)) none).isWellScopedAt (1 + ambient) =
      true := by
    have lifted := Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_isWellScopedAt (cutoff := 0) (shift := 1)
      (ambient := ambient) (pattern := .collection .hashBag others none) (by simpa using othersScoped)
    simpa [liftBVars, liftBVarsList_eq_map, Nat.add_comm] using lifted
  have othersList : Pattern.isWellScopedListAt ambient others = true := by
    simpa [Pattern.isWellScopedAt] using othersScoped
  have liftedList : Pattern.isWellScopedListAt (1 + ambient) (others.map (liftBVars 0 1)) = true := by
    simpa [Pattern.isWellScopedAt] using liftedScoped
  have bodyScoped' : body.isWellScopedAt (ambient + 1) = true := by rwa [Nat.add_comm]
  have liftedList' : Pattern.isWellScopedListAt (ambient + 1) (others.map (liftBVars 0 1)) = true := by
    rwa [Nat.add_comm]
  rw [mem_applyEquationAt_iff]
  refine ⟨rfl, ?_, ?_, _, [("rest", ⟨[], ambient, .collection .hashBag others none⟩),
    ("P", ⟨[.base block.name], ambient, body⟩)], rfl, rfl, ?_, ?_⟩
  · simp [Pattern.isWellScopedAt, Pattern.isWellScopedListAt, bodyScoped', othersList]
  · simp [Pattern.isWellScopedAt, Pattern.isWellScopedListAt, bodyScoped', liftedList']
  · simp only [matchRuleAt, matchRuleWithAt]
    refine mem_matchAtWith_bag.mpr ⟨_, rfl, mem_matchBagAtWith_cons.mpr
      ⟨.apply block.restrict [.lambda none body], 0, by simp [List.zipIdx], [("P", ⟨[.base block.name], ambient, body⟩)],
        ?_, ?_⟩⟩
    · refine mem_matchAtWith_apply.mpr ⟨_, rfl, mem_matchArgsAtWith_cons.mpr
        ⟨_, [], _, rfl, mem_matchAtWith_lambda.mpr ⟨none, body, rfl, mem_matchAtWith_fvar.mpr ?_⟩,
          mem_matchArgsAtWith_nil.mpr ⟨rfl, rfl⟩⟩⟩
      simp [captureWith?_literal, capture?, orientedRule, scopeExtrusionOf, dependencies?, arguments?,
        occurrenceDeclared, sitePattern?, occurrenceAt?, recoverValue?_one bodyScoped, assign, lookup]
    · refine mem_matchBagAtWith_rest.mpr ?_
      simp [captureRestWith?_literal, captureRest?, capture?, orientedRule, scopeExtrusionOf, dependencies?,
        arguments?, occurrenceDeclared, sitePattern?, occurrenceAt?, recoverValue?_zero othersScoped, assign,
        lookup]
  · simp [reduct?, instantiateAt?, instantiateWith?, instantiateArgsWith?, orientedRule, scopeExtrusionOf,
      arguments?, dependencies?, occurrenceDeclared, sitePattern?, occurrenceAt?, lookup,
      instantiateValue?_one bodyScoped, instantiateValue?_shift othersScoped, liftBVars, liftBVarsList_eq_map]

/-- The empty multiset's law, read forward, at any ambient scope. -/
theorem emptyUnit_instance {label : String} {ambient : Nat} :
    .apply block.restrict [.lambda none (.apply block.unit [])] ∈
      applyEquationAt language ambient (emptyUnitOf block label) .forward
        (.apply label [.collection .hashBag [] none]) := by
  rw [mem_applyEquationAt_iff]
  refine ⟨rfl, by simp [Pattern.isWellScopedAt, Pattern.isWellScopedListAt],
    by simp [Pattern.isWellScopedAt, Pattern.isWellScopedListAt], _, [], rfl, rfl, ?_, ?_⟩
  · simp only [matchRuleAt, matchRuleWithAt]
    refine mem_matchAtWith_apply.mpr ⟨_, rfl, mem_matchArgsAtWith_cons.mpr
      ⟨_, [], _, rfl, mem_matchAtWith_bag.mpr ⟨[], rfl, ?_⟩, mem_matchArgsAtWith_nil.mpr ⟨rfl, rfl⟩⟩⟩
    simp [matchBagAtWith, orientedRule, emptyUnitOf]
  · simp [reduct?, instantiateAt?, instantiateWith?, instantiateArgsWith?, orientedRule, emptyUnitOf]

/-- The two innermost bound variables exchanged. -/
def swapInner (index : Nat) : Nat := if index = 0 then 1 else if index = 1 then 0 else index

theorem recovery_two (ambient : Nat) : recoveryAssignment 2 2 ambient [0, 1] = Pattern.bvar := by
  funext index
  by_cases inside : index < 2
  · rcases (by omega : index = 0 ∨ index = 1) with rfl | rfl <;> simp [recoveryAssignment]
  · have recovered : 2 + (index - 2) = index := by omega
    simp [recoveryAssignment, inside, recovered]

theorem occurrence_two : occurrenceAssignment 2 2 [.bvar 0, .bvar 1] = Pattern.bvar := by
  funext index
  by_cases inside : index < 2
  · rcases (by omega : index = 0 ∨ index = 1) with rfl | rfl <;> simp [occurrenceAssignment]
  · have recovered : 2 + (index - 2) = index := by omega
    simp [occurrenceAssignment, inside, recovered]

theorem occurrence_swap :
    occurrenceAssignment 2 2 [.bvar 1, .bvar 0] = fun index => Pattern.bvar (swapInner index) := by
  funext index
  by_cases inside : index < 2
  · rcases (by omega : index = 0 ∨ index = 1) with rfl | rfl <;> simp [occurrenceAssignment, swapInner]
  · have recovered : 2 + (index - 2) = index := by omega
    have notZero : index ≠ 0 := by omega
    have notOne : index ≠ 1 := by omega
    simp [occurrenceAssignment, inside, recovered, swapInner, notZero, notOne]

/-- A body under two binders is recovered as it is. -/
theorem recoverValue?_two {first second : TypeExpr} {ambient : Nat} {body : Pattern}
    (wellScoped : body.isWellScopedAt (2 + ambient) = true) :
    recoverValue? [first, second] ambient 2 [.bvar 0, .bvar 1] body = some ⟨[first, second], ambient, body⟩ := by
  have inside : 1 < 2 + ambient := by omega
  simp [recoverValue?, wellScoped, variableSpine?, recovery_two,
    Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute_id, instantiateValue?, occurrence_two,
    Pattern.isWellScopedAt, inside]

/-- **Exchange, read through its declaration**: two restrictions trade places, and the body's two innermost bound
names are exchanged. -/
theorem exchange_instance {ambient : Nat} {body : Pattern}
    (wellScoped : body.isWellScopedAt (2 + ambient) = true)
    (swappedScoped : (rename swapInner body).isWellScopedAt (2 + ambient) = true) :
    .apply block.restrict [.lambda none (.apply block.restrict [.lambda none (rename swapInner body)])] ∈
      applyEquationAt language ambient (restrictionExchangeOf block) .forward
        (.apply block.restrict [.lambda none (.apply block.restrict [.lambda none body])]) := by
  have bodyScoped' : body.isWellScopedAt (ambient + 1 + 1) = true := by
    rw [show ambient + 1 + 1 = 2 + ambient by omega]; exact wellScoped
  have swappedScoped' : (rename swapInner body).isWellScopedAt (ambient + 1 + 1) = true := by
    rw [show ambient + 1 + 1 = 2 + ambient by omega]; exact swappedScoped
  rw [mem_applyEquationAt_iff]
  refine ⟨rfl, by simp [Pattern.isWellScopedAt, Pattern.isWellScopedListAt, bodyScoped'],
    by simp [Pattern.isWellScopedAt, Pattern.isWellScopedListAt, swappedScoped'], _,
    [("P", ⟨[.base block.name, .base block.name], ambient, body⟩)], rfl, rfl, ?_, ?_⟩
  · simp only [matchRuleAt, matchRuleWithAt]
    refine mem_matchAtWith_apply.mpr ⟨_, rfl, mem_matchArgsAtWith_cons.mpr ⟨_, [], _, rfl,
      mem_matchAtWith_lambda.mpr ⟨none, _, rfl, mem_matchAtWith_apply.mpr ⟨_, rfl, mem_matchArgsAtWith_cons.mpr
        ⟨_, [], _, rfl, mem_matchAtWith_lambda.mpr ⟨none, body, rfl, mem_matchAtWith_fvar.mpr ?_⟩,
          mem_matchArgsAtWith_nil.mpr ⟨rfl, rfl⟩⟩⟩⟩, mem_matchArgsAtWith_nil.mpr ⟨rfl, rfl⟩⟩⟩
    simp [captureWith?_literal, capture?, orientedRule, restrictionExchangeOf, dependencies?, arguments?,
      occurrenceDeclared, sitePattern?, occurrenceAt?, recoverValue?_two wellScoped, assign, lookup]
  · have swappedSubstitute : Pattern.isWellScopedAt (2 + ambient)
        (substitute (fun index => Pattern.bvar (swapInner index)) body) = true := swappedScoped
    have deep : ¬ 2 + ambient ≤ 1 := by omega
    simp [reduct?, instantiateAt?, instantiateWith?, instantiateArgsWith?, orientedRule, restrictionExchangeOf,
      arguments?, dependencies?, occurrenceDeclared, sitePattern?, occurrenceAt?, lookup, instantiateValue?,
      wellScoped, occurrence_swap, rename, swappedSubstitute, deep, Pattern.isWellScopedAt]

/-! ## Typing -/

variable [laws : BlockSignature language block]

open Mettapedia.OSLF.MeTTaIL.ContextualStep (BasePremiseEvaluator PremisesAt)
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (engineBasePremises)
open Mettapedia.OSLF.MeTTaIL.DerivedContexts (OneHoleContext)
open Mettapedia.GSLT.LanguageDef.WellSorted (HasType FreeTypeContext)
open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationEquiv EquationInstanceAt DerivedInstance
  declaredInstanceAt_of_applyEquationAt readsRaw readsRaw_of_none)
open Mettapedia.GSLT.LanguageDef.BagNormalForm (elementsHaveType_iff)

/-- **Chains of laws through processes**, in a context. -/
abbrev ProcEquiv (language : LanguageDef) (block : Block) (free : FreeTypeContext) (bound : List TypeExpr) :
    Pattern → Pattern → Prop :=
  SortedEquiv language free bound (.base block.proc)

/-- Processes of the process sort in a context. -/
def Members (language : LanguageDef) (block : Block) (free : FreeTypeContext) (bound : List TypeExpr)
    (elements : List Pattern) : Prop :=
  ∀ element ∈ elements, HasType language free bound element (.base block.proc)

omit laws in
theorem Members.cons {free : FreeTypeContext} {bound : List TypeExpr} {element : Pattern} {elements : List Pattern}
    (head : HasType language free bound element (.base block.proc)) (tail : Members language block free bound elements) :
    Members language block free bound (element :: elements) := by
  intro other member
  rcases List.mem_cons.mp member with rfl | member
  · exact head
  · exact tail other member

omit laws in
theorem Members.nil {free : FreeTypeContext} {bound : List TypeExpr} : Members language block free bound [] :=
  fun _ member => by simp at member

omit laws in
theorem Members.append {free : FreeTypeContext} {bound : List TypeExpr} {first second : List Pattern}
    (left : Members language block free bound first) (right : Members language block free bound second) :
    Members language block free bound (first ++ second) := by
  intro element member
  rcases List.mem_append.mp member with member | member
  · exact left element member
  · exact right element member

omit laws in
theorem Members.tail {free : FreeTypeContext} {bound : List TypeExpr} {element : Pattern} {elements : List Pattern}
    (members : Members language block free bound (element :: elements)) : Members language block free bound elements :=
  fun other member => members other (List.mem_cons_of_mem _ member)

theorem bag_typed {free : FreeTypeContext} {bound : List TypeExpr} {elements : List Pattern} {rest : Option String}
    (members : Members language block free bound elements) :
    HasType language free bound (.collection .hashBag elements rest) (.base block.proc) :=
  laws.bag_typed (elementsHaveType_iff.mpr members)

theorem body_typed {free : FreeTypeContext} {bound : List TypeExpr} {elements : List Pattern}
    (members : Members language block free bound elements) :
    HasType language free bound (Prenex.body block elements) (.base block.proc) := by
  match elements, members with
  | [], _ => exact laws.unit_typed
  | [element], members => exact members element (List.mem_singleton_self _)
  | _ :: _ :: _, members => exact bag_typed members

/-- A restriction of a process of the process sort is one. -/
theorem restrict_typed {free : FreeTypeContext} {bound : List TypeExpr} {body : Pattern}
    (typed : HasType language free (.base block.name :: bound) body (.base block.proc)) :
    HasType language free bound (.apply block.restrict [.lambda none body]) (.base block.proc) :=
  laws.restrict_typed typed

omit laws in
theorem replicate_succ_append (count : Nat) (sort : TypeExpr) (bound : List TypeExpr) :
    List.replicate (count + 1) sort ++ bound = List.replicate count sort ++ (sort :: bound) := by
  simp [List.replicate_succ', List.append_assoc]

theorem restricts_typed {free : FreeTypeContext} :
    ∀ (count : Nat) {bound : List TypeExpr} {body : Pattern},
      HasType language free (List.replicate count (TypeExpr.base block.name) ++ bound) body (.base block.proc) →
      HasType language free bound (Prenex.restricts block count body) (.base block.proc)
  | 0, _, _, typed => by simpa [Prenex.restricts] using typed
  | count + 1, bound, body, typed => by
      apply restrict_typed
      apply restricts_typed count
      rwa [replicate_succ_append] at typed

omit laws in
/-- Typing survives inserting binders below a prefix, when the indices are lifted. -/
theorem lift_typed {free : FreeTypeContext} {inner inserted outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (typed : HasType language free (inner ++ outer) pattern type) :
    HasType language free (inner ++ inserted ++ outer) (liftBVars inner.length inserted.length pattern) type :=
  Mettapedia.GSLT.LanguageDef.WellSorted.HasType.liftBVars_insert typed

omit laws in
/-- Members read under more binders from the outside. -/
theorem Members.lift {free : FreeTypeContext} {bound : List TypeExpr} (inserted : List TypeExpr) {elements : List Pattern}
    (members : Members language block free bound elements) :
    Members language block free (inserted ++ bound) (elements.map (liftBVars 0 inserted.length)) := by
  intro element member
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
  simpa using lift_typed (inner := []) (inserted := inserted) (outer := bound) (members original originalMember)

/-- Members are scoped by their context. -/
theorem Members.scoped {free : FreeTypeContext} {bound : List TypeExpr} {elements : List Pattern}
    (members : Members language block free bound elements) :
    (Pattern.collection .hashBag elements none).isWellScopedAt bound.length = true :=
  Mettapedia.GSLT.LanguageDef.WellSorted.HasType.isWellScopedAt (bag_typed members)

/-- **A bag context of processes carries chains through processes.** -/
theorem bag_fill {free : FreeTypeContext} {bound : List TypeExpr} {before after : List Pattern} {rest : Option String}
    (beforeMembers : Members language block free bound before) (afterMembers : Members language block free bound after)
    {first second : Pattern} (equivalent : ProcEquiv language block free bound first second) :
    ProcEquiv language block free bound (.collection .hashBag (before ++ first :: after) rest)
      (.collection .hashBag (before ++ second :: after) rest) :=
  SortedEquiv.fill (.collection .hashBag before .hole after rest)
    (fun _ typed => bag_typed (beforeMembers.append (Members.cons typed afterMembers))) equivalent

/-- **A restriction carries chains through processes under its name.** -/
theorem restrict_fill {free : FreeTypeContext} {bound : List TypeExpr} {first second : Pattern}
    (equivalent : ProcEquiv language block free (.base block.name :: bound) first second) :
    ProcEquiv language block free bound (.apply block.restrict [.lambda none first])
      (.apply block.restrict [.lambda none second]) :=
  SortedEquiv.fill (.apply block.restrict [] (.lambda none .hole) []) (fun _ typed => restrict_typed typed)
    equivalent

/-! ## The laws as equivalences -/

/-- `(νx) 0 = 0`. -/
theorem restriction_nil_equivalent {free : FreeTypeContext} {bound : List TypeExpr} :
    ProcEquiv language block free bound (.apply block.restrict [.lambda none (.apply block.unit [])])
      (.apply block.unit []) :=
  SortedEquiv.ofInstance ⟨0, .forward (initialBindings := []) (finalBindings := []) laws.nil_mem
    (readsRaw_of_none rfl) (by simp [restrictionNilOf, Mettapedia.OSLF.MeTTaIL.Match.matchPattern,
      Mettapedia.OSLF.MeTTaIL.Match.matchArgs, Mettapedia.OSLF.MeTTaIL.Match.mergeBindings]) (.nil _)
    (by simp [restrictionNilOf, Mettapedia.OSLF.MeTTaIL.Match.applyBindings])⟩
    (restrict_typed laws.unit_typed) laws.unit_typed

/-- `m{} = 0`, for a named multiset whose empty instance is the unit: its law, then `(νx) 0 = 0`. -/
theorem empty_unit_equivalent {label : String} (listed : label ∈ block.emptyUnits) {free : FreeTypeContext}
    {bound : List TypeExpr} (typed : HasType language free bound (.apply label [.collection .hashBag [] none])
      (.base block.proc)) :
    ProcEquiv language block free bound (.apply label [.collection .hashBag [] none]) (.apply block.unit []) :=
  .trans _ _ _ (SortedEquiv.ofInstance ⟨0, .declared (orientation := .forward) (ambient := bound.length)
    (laws.emptyUnit_mem listed) rfl (declaredInstanceAt_of_applyEquationAt emptyUnit_instance)⟩
    typed (restrict_typed laws.unit_typed)) restriction_nil_equivalent

/-- **Extrusion as an equivalence**: a restriction in a bag of processes moves out over the other members. -/
theorem extrusion_equivalent {free : FreeTypeContext} {bound : List TypeExpr} {body : Pattern} {others : List Pattern}
    (bodyTyped : HasType language free (.base block.name :: bound) body (.base block.proc))
    (othersTyped : Members language block free bound others) :
    ProcEquiv language block free bound (.collection .hashBag (.apply block.restrict [.lambda none body] :: others) none)
      (.apply block.restrict [.lambda none (.collection .hashBag (body :: others.map (liftBVars 0 1)) none)]) := by
  have bodyScoped : body.isWellScopedAt (1 + bound.length) = true := by
    simpa [Nat.add_comm] using Mettapedia.GSLT.LanguageDef.WellSorted.HasType.isWellScopedAt bodyTyped
  refine SortedEquiv.ofInstance ⟨0, .declared (orientation := .forward) (ambient := bound.length)
    laws.extrusion_mem rfl
    (declaredInstanceAt_of_applyEquationAt (extrusion_instance bodyScoped othersTyped.scoped))⟩
    (bag_typed (Members.cons (restrict_typed bodyTyped) othersTyped)) ?_
  exact restrict_typed (bag_typed (Members.cons bodyTyped (by simpa using othersTyped.lift [.base block.name])))

/-- Lifting twice from the outside is lifting once by the sum. -/
theorem liftBVars_zero_add (first second : Nat) (pattern : Pattern) :
    liftBVars 0 first (liftBVars 0 second pattern) = liftBVars 0 (first + second) pattern := by
  have outer := substitute_shift first (liftBVars 0 second pattern) 0
  have inner := substitute_shift second pattern 0
  have total := substitute_shift (first + second) pattern 0
  simp only [Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift_zero] at outer inner total
  rw [← outer, ← inner, Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute_comp, ← total]
  congr 1
  funext index
  show Pattern.bvar (first + (second + index)) = Pattern.bvar (first + second + index)
  rw [Nat.add_assoc]

/-- A block of restrictions is scoped where its body is, with the restrictions added. -/
theorem restricts_isWellScopedAt : ∀ (count depth : Nat) (pattern : Pattern),
    (Prenex.restricts block count pattern).isWellScopedAt depth = pattern.isWellScopedAt (depth + count)
  | 0, _, _ => rfl
  | count + 1, depth, pattern => by
      simp only [Prenex.restricts, Pattern.isWellScopedAt, Pattern.isWellScopedListAt, Bool.and_true]
      rw [restricts_isWellScopedAt count (depth + 1) pattern]
      congr 1
      omega

/-- **Several restrictions leave a bag at once**: the other members, which use none of them, are read under all of
them. -/
theorem extrusions_equivalent {free : FreeTypeContext} :
    ∀ (count : Nat) {bound : List TypeExpr} {body : Pattern} {others : List Pattern},
      HasType language free (List.replicate count (TypeExpr.base block.name) ++ bound) body (.base block.proc) →
      Members language block free bound others →
      ProcEquiv language block free bound (.collection .hashBag (Prenex.restricts block count body :: others) none)
        (Prenex.restricts block count (.collection .hashBag (body :: others.map (liftBVars 0 count)) none))
  | 0, _, body, others, _, _ => by
      simp only [Prenex.restricts]
      rw [show others.map (liftBVars 0 0) = others from by
        conv_rhs => rw [← List.map_id others]
        exact List.map_congr_left fun other _ => Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero other 0]
      exact .refl _
  | count + 1, bound, body, others, bodyTyped, othersTyped => by
      rw [replicate_succ_append] at bodyTyped
      have first := extrusion_equivalent (restricts_typed count bodyTyped) othersTyped
      have rest := extrusions_equivalent count bodyTyped (by simpa using othersTyped.lift [.base block.name])
      have inside := restrict_fill rest
      simp only [List.map_map, Function.comp_def, liftBVars_zero_add] at inside
      exact .trans _ _ _ first inside

/-! ## Garbage -/

/-- Inaction beside a process in a two-member bag is the process. -/
theorem nil_bag_equivalent {free : FreeTypeContext} {bound : List TypeExpr} {process : Pattern}
    (typed : HasType language free bound process (.base block.proc)) :
    ProcEquiv language block free bound (.collection .hashBag [.apply block.unit [], process] none) process :=
  .trans _ _ _ (SortedEquiv.ofDerived (laws.unitElim (pre := []) (post := [process])
      (bag_typed (Members.cons laws.unit_typed (Members.cons typed Members.nil))))
      (bag_typed (Members.cons laws.unit_typed (Members.cons typed Members.nil)))
      (bag_typed (Members.cons typed Members.nil)))
    (SortedEquiv.ofDerived (laws.singleton typed) (bag_typed (Members.cons typed Members.nil)) typed)

/-- **A restriction its body does not use is garbage**: `(νx) Q = Q` when `Q` does not mention `x`. Through
inaction: `(νx) Q = (νx){0 | Q} = {(νx)0 | Q} = {0 | Q} = Q`. -/
theorem garbage_equivalent {free : FreeTypeContext} {bound : List TypeExpr} {process : Pattern}
    (typed : HasType language free bound process (.base block.proc)) :
    ProcEquiv language block free bound (.apply block.restrict [.lambda none (liftBVars 0 1 process)]) process := by
  have lifted : HasType language free (.base block.name :: bound) (liftBVars 0 1 process) (.base block.proc) := by
    simpa using lift_typed (inner := []) (inserted := [.base block.name]) (outer := bound) typed
  have padded := restrict_fill (.symm _ _ (nil_bag_equivalent lifted))
  have extruded := extrusion_equivalent (body := .apply block.unit []) (others := [process]) laws.unit_typed
    (Members.cons typed Members.nil)
  have emptied := bag_fill (before := []) (after := [process]) (rest := none) Members.nil
    (Members.cons typed Members.nil) restriction_nil_equivalent
  simp only [List.map_cons, List.map_nil, List.nil_append] at extruded emptied
  exact .trans _ _ _ padded (.trans _ _ _ (.symm _ _ extruded) (.trans _ _ _ emptied (nil_bag_equivalent typed)))

/-! ## Bags and bodies -/

/-- **A bag is its body**: the empty bag is inaction, and a singleton is its member. -/
theorem bag_body_equivalent {free : FreeTypeContext} {bound : List TypeExpr} {elements : List Pattern}
    (members : Members language block free bound elements) :
    ProcEquiv language block free bound (.collection .hashBag elements none) (Prenex.body block elements) := by
  match elements, members with
  | [], members => exact SortedEquiv.ofDerived laws.emptyUnit (bag_typed members) laws.unit_typed
  | [element], members =>
      exact SortedEquiv.ofDerived (laws.singleton (members element (List.mem_singleton_self _))) (bag_typed members)
        (members element (List.mem_singleton_self _))
  | _ :: _ :: _, _ => exact .refl _

/-- Two bags side by side are one bag. -/
theorem bag_pair_equivalent {free : FreeTypeContext} {bound : List TypeExpr} {first second : List Pattern}
    (firstMembers : Members language block free bound first) (secondMembers : Members language block free bound second) :
    ProcEquiv language block free bound
      (.collection .hashBag [.collection .hashBag first none, .collection .hashBag second none] none)
      (.collection .hashBag (first ++ second) none) := by
  have outer : Members language block free bound [.collection .hashBag first none, .collection .hashBag second none] :=
    Members.cons (bag_typed firstMembers) (Members.cons (bag_typed secondMembers) Members.nil)
  have middle : Members language block free bound (first ++ [.collection .hashBag second none]) :=
    firstMembers.append (Members.cons (bag_typed secondMembers) Members.nil)
  have firstStep := laws.flatten (pre := []) (inner := first) (post := [.collection .hashBag second none])
    (bag_typed outer)
  have secondStep := laws.flatten (pre := first) (inner := second) (post := []) (bag_typed middle)
  simp only [List.nil_append, List.append_nil] at firstStep secondStep
  exact .trans _ _ _ (SortedEquiv.ofDerived firstStep (bag_typed outer) (bag_typed middle))
    (SortedEquiv.ofDerived secondStep (bag_typed middle) (bag_typed (firstMembers.append secondMembers)))

/-- **Two bodies side by side are one body.** -/
theorem body_pair_equivalent {free : FreeTypeContext} {bound : List TypeExpr} {first second : List Pattern}
    (firstMembers : Members language block free bound first) (secondMembers : Members language block free bound second) :
    ProcEquiv language block free bound
      (.collection .hashBag [Prenex.body block first, Prenex.body block second] none)
      (Prenex.body block (first ++ second)) := by
  have toBags := bag_fill (before := []) (after := [Prenex.body block second]) (rest := none) Members.nil
    (Members.cons (body_typed secondMembers) Members.nil) (.symm _ _ (bag_body_equivalent firstMembers))
  have toBags' := bag_fill (before := [.collection .hashBag first none]) (after := []) (rest := none)
    (Members.cons (bag_typed firstMembers) Members.nil) Members.nil (.symm _ _ (bag_body_equivalent secondMembers))
  simp only [List.nil_append, List.cons_append] at toBags toBags'
  exact .trans _ _ _ toBags (.trans _ _ _ toBags'
    (.trans _ _ _ (bag_pair_equivalent firstMembers secondMembers)
      (bag_body_equivalent (firstMembers.append secondMembers))))

/-! ## Blocks -/

/-- **A block of restrictions carries chains through processes.** -/
theorem restricts_congr {free : FreeTypeContext} :
    ∀ (count : Nat) {bound : List TypeExpr} {first second : Pattern},
      ProcEquiv language block free (List.replicate count (TypeExpr.base block.name) ++ bound) first second →
      ProcEquiv language block free bound (Prenex.restricts block count first) (Prenex.restricts block count second)
  | 0, _, _, _, related => by simpa [Prenex.restricts] using related
  | count + 1, bound, _, _, related => by
      rw [replicate_succ_append] at related
      exact restrict_fill (restricts_congr count related)

theorem restricts_add : ∀ (first second : Nat) (body : Pattern),
    Prenex.restricts block first (Prenex.restricts block second body) = Prenex.restricts block (first + second) body
  | 0, _, _ => by simp [Prenex.restricts]
  | first + 1, second, body => by
      rw [show first + 1 + second = (first + second) + 1 by omega]
      simp only [Prenex.restricts]
      rw [restricts_add first second body]

/-- Lifting reaches through a block, past its restrictions. -/
theorem liftBVars_restricts : ∀ (count cutoff shift : Nat) (body : Pattern),
    liftBVars cutoff shift (Prenex.restricts block count body) =
      Prenex.restricts block count (liftBVars (cutoff + count) shift body)
  | 0, _, _, _ => rfl
  | count + 1, cutoff, shift, body => by
      simp only [Prenex.restricts, liftBVars, liftBVarsList_eq_map, List.map_cons, List.map_nil]
      rw [liftBVars_restricts count (cutoff + 1) shift body]
      rw [show cutoff + 1 + count = cutoff + (count + 1) by omega]

/-- Lifting the body of a bag lifts its members. -/
theorem liftBVars_body (cutoff shift : Nat) (elements : List Pattern) :
    liftBVars cutoff shift (Prenex.body block elements) =
      Prenex.body block (elements.map (liftBVars cutoff shift)) := by
  match elements with
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: _ => simp [Prenex.body, liftBVars, liftBVarsList_eq_map]

/-- A two-member bag in either order. -/
theorem bag_swap_equivalent {free : FreeTypeContext} {bound : List TypeExpr} {first second : Pattern}
    (firstTyped : HasType language free bound first (.base block.proc))
    (secondTyped : HasType language free bound second (.base block.proc)) :
    ProcEquiv language block free bound (.collection .hashBag [first, second] none)
      (.collection .hashBag [second, first] none) :=
  SortedEquiv.ofDerived (DerivedInstance.bagPerm_of_sorted
    ⟨free, bound, bag_typed (Members.cons firstTyped (Members.cons secondTyped Members.nil))⟩
      (List.Perm.swap second first []))
    (bag_typed (Members.cons firstTyped (Members.cons secondTyped Members.nil)))
    (bag_typed (Members.cons secondTyped (Members.cons firstTyped Members.nil)))

/-- **Two blocks side by side are one block**, the first one's restrictions outermost. -/
theorem par_equivalent {free : FreeTypeContext} {bound : List TypeExpr} {first second : Prenex}
    (firstMembers : Members language block free (List.replicate first.count (TypeExpr.base block.name) ++ bound)
      first.components)
    (secondMembers : Members language block free (List.replicate second.count (TypeExpr.base block.name) ++ bound)
      second.components) :
    ProcEquiv language block free bound
      (.collection .hashBag [(first.toPattern block), (second.toPattern block)] none)
      ((first.par second).toPattern block) := by
  obtain ⟨outer, firstComponents⟩ := first
  obtain ⟨inner, secondComponents⟩ := second
  simp only at firstMembers secondMembers
  have firstBody := body_typed firstMembers
  have secondBody := body_typed secondMembers
  have secondBlock := restricts_typed inner secondBody
  -- the first block's restrictions leave the bag
  have stepOuter := extrusions_equivalent outer (body := Prenex.body block firstComponents)
    (others := [Prenex.restricts block inner (Prenex.body block secondComponents)]) firstBody
    (Members.cons secondBlock Members.nil)
  simp only [List.map_cons, List.map_nil, liftBVars_restricts, Nat.zero_add] at stepOuter
  -- inside them, the second block's restrictions leave the bag too
  have liftedSecond' : HasType language free
      (List.replicate inner (TypeExpr.base block.name) ++ (List.replicate outer (TypeExpr.base block.name) ++ bound))
      (liftBVars inner outer (Prenex.body block secondComponents)) (.base block.proc) := by
    have lifted := lift_typed (inner := List.replicate inner (TypeExpr.base block.name))
      (inserted := List.replicate outer (TypeExpr.base block.name)) (outer := bound) secondBody
    simp only [List.length_replicate] at lifted
    rw [← List.append_assoc]
    exact lifted
  have liftedSecondBlock : HasType language free (List.replicate outer (TypeExpr.base block.name) ++ bound)
      (Prenex.restricts block inner (liftBVars inner outer (Prenex.body block secondComponents))) (.base block.proc) :=
    restricts_typed inner liftedSecond'
  have swapOuter := restricts_congr outer (bag_swap_equivalent firstBody liftedSecondBlock)
  have stepInner := restricts_congr outer
    (extrusions_equivalent inner (bound := List.replicate outer (TypeExpr.base block.name) ++ bound)
      (others := [Prenex.body block firstComponents]) liftedSecond' (Members.cons firstBody Members.nil))
  simp only [List.map_cons, List.map_nil] at stepInner
  -- the members in order, and one body
  have liftedFirst : HasType language free
      (List.replicate inner (TypeExpr.base block.name) ++ (List.replicate outer (TypeExpr.base block.name) ++ bound))
      (liftBVars 0 inner (Prenex.body block firstComponents)) (.base block.proc) := by
    simpa using lift_typed (inner := []) (inserted := List.replicate inner (TypeExpr.base block.name))
      (outer := List.replicate outer (TypeExpr.base block.name) ++ bound) firstBody
  have swapInnerBag := restricts_congr outer (restricts_congr inner (bag_swap_equivalent liftedSecond' liftedFirst))
  have firstLiftedMembers : Members language block free
      (List.replicate inner (TypeExpr.base block.name) ++ (List.replicate outer (TypeExpr.base block.name) ++ bound))
      (firstComponents.map (liftBVars 0 inner)) := by
    simpa using firstMembers.lift (List.replicate inner (TypeExpr.base block.name))
  have secondLiftedMembers : Members language block free
      (List.replicate inner (TypeExpr.base block.name) ++ (List.replicate outer (TypeExpr.base block.name) ++ bound))
      (secondComponents.map (liftBVars inner outer)) := by
    intro element member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    have lifted := lift_typed (inner := List.replicate inner (TypeExpr.base block.name))
      (inserted := List.replicate outer (TypeExpr.base block.name)) (outer := bound) (secondMembers original originalMember)
    simp only [List.length_replicate] at lifted
    rw [← List.append_assoc]
    exact lifted
  have joined := restricts_congr outer
    (restricts_congr inner (body_pair_equivalent firstLiftedMembers secondLiftedMembers))
  simp only [liftBVars_body] at stepOuter swapOuter stepInner swapInnerBag joined
  have total : ((Prenex.par ⟨outer, firstComponents⟩ ⟨inner, secondComponents⟩).toPattern block) =
      Prenex.restricts block outer (Prenex.restricts block inner (Prenex.body block
        (firstComponents.map (liftBVars 0 inner) ++ secondComponents.map (liftBVars inner outer)))) := by
    simp [Prenex.par, Prenex.toPattern, restricts_add]
  rw [total]
  show ProcEquiv _ _ _ _ (.collection .hashBag [Prenex.restricts block outer (Prenex.body block firstComponents),
    Prenex.restricts block inner (Prenex.body block secondComponents)] none) _
  exact .trans _ _ _ stepOuter (.trans _ _ _ swapOuter (.trans _ _ _ stepInner
    (.trans _ _ _ swapInnerBag joined)))

omit laws in
/-- Blocks side by side are typed where their parts are. -/
theorem par_members {free : FreeTypeContext} {bound : List TypeExpr} {first second : Prenex}
    (firstMembers : Members language block free (List.replicate first.count (TypeExpr.base block.name) ++ bound) first.components)
    (secondMembers : Members language block free (List.replicate second.count (TypeExpr.base block.name) ++ bound) second.components) :
    Members language block free (List.replicate (first.par second).count (TypeExpr.base block.name) ++ bound) (first.par second).components := by
  intro element member
  simp only [Prenex.par, List.mem_append, List.mem_map] at member
  have total : List.replicate (first.count + second.count) (TypeExpr.base block.name) =
      List.replicate second.count (TypeExpr.base block.name) ++ List.replicate first.count (TypeExpr.base block.name) := by
    rw [List.replicate_append_replicate, Nat.add_comm]
  rw [Prenex.par_count, total]
  rcases member with ⟨original, originalMember, rfl⟩ | ⟨original, originalMember, rfl⟩
  · have lifted := lift_typed (inner := []) (inserted := List.replicate second.count (TypeExpr.base block.name))
      (outer := List.replicate first.count (TypeExpr.base block.name) ++ bound) (firstMembers original originalMember)
    simp only [List.nil_append, List.length_nil, List.length_replicate] at lifted
    rw [List.append_assoc]
    exact lifted
  · have lifted := lift_typed (inner := List.replicate second.count (TypeExpr.base block.name))
      (inserted := List.replicate first.count (TypeExpr.base block.name)) (outer := bound) (secondMembers original originalMember)
    simp only [List.length_replicate] at lifted
    exact lifted

/-! ## Dropping unused restrictions -/

open Mettapedia.OSLF.MeTTaIL.CanonicalBags (FreeIn freeIn_bvar freeIn_apply freeIn_lambda freeIn_multiLambda
  freeIn_subst freeIn_collection substitute_eq_of_free_fixed)
open Mettapedia.GSLT.LanguageDef.WellSorted (UsesOuterBound HasType.substituteBoundOnSupport)

theorem mentionsList_eq_any (index : Nat) : ∀ (patterns : List Pattern),
    mentionsList index patterns = patterns.any (mentions index)
  | [] => rfl
  | pattern :: patterns => by simp [mentionsList, mentionsList_eq_any index patterns]

/-- The check reads occurrence. -/
theorem mentions_iff (pattern : Pattern) : ∀ index, mentions index pattern = true ↔ FreeIn index pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar other =>
      intro index
      simp only [mentions, beq_iff_eq, freeIn_bvar]
      exact eq_comm
  | hfvar name =>
      intro index
      simp only [mentions, Bool.false_eq_true, false_iff]
      rintro ⟨⟩
  | happly label arguments recurse =>
      intro index
      simp only [mentions, mentionsList_eq_any, List.any_eq_true, freeIn_apply]
      exact exists_congr fun argument => and_congr_right fun member => recurse argument member index
  | hlambda binder body recurse =>
      intro index
      simp only [mentions, freeIn_lambda]
      exact recurse (index + 1)
  | hmultiLambda arity binders body recurse =>
      intro index
      simp only [mentions, freeIn_multiLambda]
      exact recurse (index + arity)
  | hsubst body replacement bodyRecurse replacementRecurse =>
      intro index
      simp only [mentions, Bool.or_eq_true, freeIn_subst, bodyRecurse, replacementRecurse]
  | hcollection kind elements rest recurse =>
      intro index
      simp only [mentions, mentionsList_eq_any, List.any_eq_true, freeIn_collection]
      exact exists_congr fun element => and_congr_right fun member => recurse element member index

theorem freeIn_of_uses {pattern : Pattern} {index : Nat} (used : UsesOuterBound pattern index) :
    FreeIn index pattern := by
  induction used with
  | bvar index => exact .bvar index
  | apply member _ recurse => exact .apply member recurse
  | lambda _ recurse => exact .lambda recurse
  | multiLambda _ recurse => exact .multiLambda recurse
  | substBody _ recurse => exact .substBody recurse
  | substReplacement _ recurse => exact .substReplacement recurse
  | collection member _ recurse => exact .element member recurse

/-- **Strengthening**: a pattern that does not use a bound variable is typed without it, once the variable is
dropped. -/
theorem drop_typed {free : FreeTypeContext} {inner outer : List TypeExpr} {removed type : TypeExpr}
    {pattern : Pattern} (typed : HasType language free (inner ++ removed :: outer) pattern type)
    (unused : ¬ FreeIn inner.length pattern) :
    HasType language free (inner ++ outer) (rename (dropIndex inner.length) pattern) type := by
  refine HasType.substituteBoundOnSupport typed (fun index => .bvar (dropIndex inner.length index)) ?_
  intro index indexType used lookup
  have different : index ≠ inner.length := fun equal => unused (equal ▸ freeIn_of_uses used)
  apply Mettapedia.GSLT.LanguageDef.WellSorted.HasType.bvar
  unfold dropIndex
  split_ifs with below
  · rw [List.getElem?_append_left below] at lookup ⊢
    exact lookup
  · rw [List.getElem?_append_right (by omega)] at lookup
    rw [List.getElem?_append_right (by omega)]
    obtain ⟨offset, offsetIs⟩ : ∃ offset, index - inner.length = offset + 1 := ⟨index - inner.length - 1, by omega⟩
    rw [offsetIs, List.getElem?_cons_succ] at lookup
    rw [show index - 1 - inner.length = offset by omega]
    exact lookup

/-- Dropping an unused variable and lifting it back changes nothing. -/
theorem lift_drop {pattern : Pattern} {cutoff : Nat} (unused : ¬ FreeIn cutoff pattern) :
    liftBVars cutoff 1 (rename (dropIndex cutoff) pattern) = pattern := by
  rw [← substitute_shift 1 _ cutoff, rename, Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute_comp]
  apply substitute_eq_of_free_fixed
  intro index freeIndex
  have different : index ≠ cutoff := fun equal => unused (equal ▸ freeIndex)
  simp only [substitute, lift, dropIndex]
  by_cases below : index < cutoff
  · simp [below]
  · have above : ¬ index - 1 < cutoff := by omega
    simp only [below, above, if_false, liftBVars]
    rw [if_pos (Nat.zero_le _)]
    congr 1
    omega

/-- **Closing a restriction is sound**: the kept restrictions type the components, and the restriction over the
block is equivalent to the closed block. -/
theorem close_sound {free : FreeTypeContext} {bound : List TypeExpr} {form : Prenex}
    (members : Members language block free (List.replicate form.count (TypeExpr.base block.name) ++ (.base block.name :: bound)) form.components) :
    Members language block free (List.replicate form.close.count (TypeExpr.base block.name) ++ bound) form.close.components ∧
      ProcEquiv language block free bound (.apply block.restrict [.lambda none (form.toPattern block)])
        (form.close.toPattern block) := by
  obtain ⟨count, components⟩ := form
  simp only [Prenex.close]
  split_ifs with used
  · exact ⟨by simpa [Prenex.restrict, List.replicate_succ', List.append_assoc] using members, .refl _⟩
  · simp only at members used ⊢
    have unused : ∀ component ∈ components, ¬ FreeIn count component := by
      intro component member free
      exact used (List.any_eq_true.mpr ⟨component, member, (mentions_iff component count).mpr free⟩)
    have droppedMembers : Members language block free (List.replicate count (TypeExpr.base block.name) ++ bound)
        (components.map (rename (dropIndex count))) := by
      intro element member
      obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
      have dropped := drop_typed (inner := List.replicate count (TypeExpr.base block.name)) (outer := bound)
        (members original originalMember) (by simpa using unused original originalMember)
      simpa using dropped
    refine ⟨droppedMembers, ?_⟩
    have back : (components.map (rename (dropIndex count))).map (liftBVars count 1) = components := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id components]
      exact List.map_congr_left fun component member => lift_drop (unused component member)
    have restored : (Prenex.toPattern block) ⟨count, components⟩ =
        liftBVars 0 1 ((Prenex.toPattern block) ⟨count, components.map (rename (dropIndex count))⟩) := by
      simp only [Prenex.toPattern, liftBVars_restricts, Nat.zero_add, liftBVars_body, back]
    rw [restored]
    exact garbage_equivalent (restricts_typed count (body_typed droppedMembers))

/-! ## A process is its block -/


open Mettapedia.GSLT.LanguageDef.BagNormalForm (bag_typing)

/-- A restriction of the process sort binds without a display name. -/
theorem restriction_binder {free : FreeTypeContext} {bound : List TypeExpr} {binder : Option String}
    {body : Pattern} {type : TypeExpr} (typed : HasType language free bound (.apply block.restrict [.lambda binder body]) type) :
    binder = none :=
  (laws.restriction_typed typed).2.2

open Mettapedia.GSLT.LanguageDef.WellSorted (hasType_apply_inversion parameterType? UsesBareCollection
  hasType_collection_inversion CollectionTypeOccurs)

/-- **A term of another sort than processes is its own block**: it is neither the unit, nor a restriction, nor a
bag, nor an empty multiset. -/
theorem decompose_other {free : FreeTypeContext} {bound : List TypeExpr} {term : Pattern} {sort : String}
    (typed : HasType language free bound term (.base sort)) (other : sort ≠ block.proc) :
    decompose block term = Prenex.atom term := by
  apply decompose_atom
  · rintro rfl
    obtain ⟨rule, member, labelIs, -, typeIs, -⟩ := hasType_apply_inversion typed
    simp only [TypeExpr.base.injEq] at typeIs
    exact other (typeIs.trans (laws.unitShape rule member labelIs.symm))
  · rintro binder body rfl
    obtain ⟨-, typeIs, -⟩ := laws.restriction_typed typed
    exact other (by simpa using typeIs)
  · rintro elements rfl
    exact other (laws.bag_members typed).2.1
  · rintro label argument rfl listed
    obtain ⟨rule, member, labelIs, -, typeIs, -⟩ := hasType_apply_inversion typed
    simp only [TypeExpr.base.injEq] at typeIs
    exact other (typeIs.trans ((laws.emptyUnitShape label listed).2 rule member labelIs.symm))

omit laws in
/-- Members that are their own blocks are a block of no restriction. -/
theorem decomposeList_atoms : ∀ {elements : List Pattern}, (∀ element ∈ elements, decompose block element =
    Prenex.atom element) → decomposeList block elements = ⟨0, elements⟩
  | [], _ => rfl
  | element :: elements, atoms => by
      rw [decomposeList, atoms element List.mem_cons_self,
        decomposeList_atoms (fun other member => atoms other (List.mem_cons_of_mem _ member))]
      simp [Prenex.par, Prenex.atom, map_liftBVars_zero']
  where
    map_liftBVars_zero' (cutoff : Nat) (patterns : List Pattern) : patterns.map (liftBVars cutoff 0) = patterns := by
      conv_rhs => rw [← List.map_id patterns]
      exact List.map_congr_left fun pattern _ => Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero pattern cutoff

/-- **The argument of a named multiset**: a typed application of a named multiset has one argument, a collection
type over a sort other than processes. -/
theorem multiset_argument {free : FreeTypeContext} {bound : List TypeExpr} {label : String}
    {arguments : List Pattern} {type : TypeExpr} (typed : HasType language free bound (.apply label arguments) type)
    (listed : label ∈ block.multisets) :
    ∃ rule ∈ language.terms, rule.label = label ∧ ¬ UsesBareCollection rule ∧ type = .base rule.category ∧
      ∃ parameterName elementSort argument,
        rule.params = [.simple parameterName (.collection .hashBag (.base elementSort))] ∧ elementSort ≠ block.proc ∧
        arguments = [argument] ∧ HasType language free bound argument (.collection .hashBag (.base elementSort)) := by
  obtain ⟨rule, member, labelIs, notBare, typeIs, argumentsTyped⟩ := hasType_apply_inversion typed
  obtain ⟨-, -, parameterName, elementSort, params, other⟩ := laws.multisetShape rule member (labelIs ▸ listed)
  rw [params] at argumentsTyped
  cases argumentsTyped with
  | cons _ argumentType argumentTyped restTyped =>
      cases restTyped
      simp only [parameterType?, Option.some.injEq] at argumentType
      subst argumentType
      exact ⟨rule, member, labelIs.symm, notBare, typeIs, parameterName, elementSort, _, params, other, rfl,
        argumentTyped⟩

/-- **An empty multiset is an empty closed bag**, when it reads as inaction. -/
theorem empty_multiset_shape {free : FreeTypeContext} {bound : List TypeExpr} {label : String} {argument : Pattern}
    (typed : HasType language free bound (.apply label [argument]) (.base block.proc))
    (listed : label ∈ block.emptyUnits) (empty : decompose block argument = Prenex.nil) :
    argument = .collection .hashBag [] none := by
  obtain ⟨-, -, -, -, -, parameterName, elementSort, argument', -, other, argumentsIs, argumentTyped⟩ :=
    multiset_argument typed (laws.emptyUnitShape label listed).1
  simp only [List.cons.injEq, and_true] at argumentsIs
  subst argumentsIs
  cases argument with
  | collection kind elements rest =>
      rcases hasType_collection_inversion argumentTyped with ⟨elementType, typeIs, elementsTyped⟩ |
        ⟨rule, -, -, -, -, typeIs, -⟩
      · simp only [TypeExpr.collection.injEq] at typeIs
        obtain ⟨rfl, rfl⟩ := typeIs
        have atoms : ∀ element ∈ elements, decompose block element = Prenex.atom element := fun element member =>
          decompose_other (elementsHaveType_iff.mp elementsTyped element member) other
        cases rest with
        | some name => simp [decompose, Prenex.atom, Prenex.nil] at empty
        | none =>
            rw [decompose_bag, decomposeList_atoms atoms] at empty
            simp only [Prenex.nil, Prenex.mk.injEq, true_and] at empty
            rw [empty]
      · cases typeIs
  | apply constructor arguments =>
      obtain ⟨_, _, _, _, typeIs, _⟩ := hasType_apply_inversion argumentTyped
      cases typeIs
  | lambda binder body => cases argumentTyped
  | multiLambda arity binders body => cases argumentTyped
  | bvar index => simp [decompose, Prenex.atom, Prenex.nil] at empty
  | fvar name => simp [decompose, Prenex.atom, Prenex.nil] at empty
  | subst body replacement => simp [decompose, Prenex.atom, Prenex.nil] at empty

mutual
  /-- **A process is its block**: the components are processes under the block's restrictions, and reading the
  block back gives an equivalent process. -/
  theorem decompose_sound {free : FreeTypeContext} {bound : List TypeExpr} {process : Pattern}
      (typed : HasType language free bound process (.base block.proc)) :
      Members language block free (List.replicate (decompose block process).count (TypeExpr.base block.name) ++ bound) (decompose block process).components ∧
        ProcEquiv language block free bound process ((decompose block process).toPattern block) := by
    by_cases isNil : process = .apply block.unit []
    · subst isNil
      refine ⟨by simp [decompose, Members], ?_⟩
      rw [decompose_unit]
      exact .refl _
    by_cases isRestriction : ∃ binder body, process = .apply block.restrict [.lambda binder body]
    · obtain ⟨binder, body, rfl⟩ := isRestriction
      obtain rfl := restriction_binder typed
      obtain ⟨members, equivalent⟩ := decompose_sound (laws.restriction_typed typed).1
      rw [decompose_restrict]
      have shifted : Members language block free (List.replicate (decompose block body).count (TypeExpr.base block.name) ++ (.base block.name :: bound))
          (decompose block body).components := members
      obtain ⟨closedMembers, closed⟩ := close_sound shifted
      exact ⟨closedMembers, .trans _ _ _ (restrict_fill equivalent) closed⟩
    by_cases isBag : ∃ elements, process = .collection .hashBag elements none
    · obtain ⟨elements, rfl⟩ := isBag
      have elementsTyped : Members language block free bound elements :=
        elementsHaveType_iff.mp (laws.bag_members typed).2.2
      rw [decompose_bag]
      exact decomposeList_sound elementsTyped
    have atomic : Members language block free (List.replicate (Prenex.atom process).count (TypeExpr.base block.name) ++
        bound) (Prenex.atom process).components ∧
        ProcEquiv language block free bound process ((Prenex.atom process).toPattern block) := by
      refine ⟨?_, .refl _⟩
      intro element member
      simp only [Prenex.atom, List.mem_singleton] at member
      subst member
      simpa [Prenex.atom] using typed
    by_cases isEmptyCandidate : ∃ label argument, process = .apply label [argument] ∧ label ∈ block.emptyUnits
    · obtain ⟨label, argument, rfl, listed⟩ := isEmptyCandidate
      have notRestriction := fun binder body equal => isRestriction ⟨binder, body, equal⟩
      by_cases empty : decompose block argument = Prenex.nil
      · rw [decompose_multiset notRestriction, if_pos ⟨listed, empty⟩]
        obtain rfl := empty_multiset_shape typed listed empty
        refine ⟨by simp [Members], ?_⟩
        simpa [Prenex.toPattern, Prenex.restricts, Prenex.body] using empty_unit_equivalent listed typed
      · rw [decompose_multiset_atom notRestriction (fun both => empty both.2)]
        exact atomic
    rw [decompose_atom isNil (fun binder body equal => isRestriction ⟨binder, body, equal⟩)
      (fun elements equal => isBag ⟨elements, equal⟩)
      (fun label argument equal listed => isEmptyCandidate ⟨label, argument, equal, listed⟩)]
    exact atomic
  termination_by sizeOf process
  decreasing_by all_goals sizeOf_pattern_dec

  /-- **A bag is the blocks of its members side by side.** -/
  theorem decomposeList_sound {free : FreeTypeContext} {bound : List TypeExpr} {elements : List Pattern}
      (typed : Members language block free bound elements) :
      Members language block free (List.replicate (decomposeList block elements).count (TypeExpr.base block.name) ++ bound)
          (decomposeList block elements).components ∧
        ProcEquiv language block free bound (.collection .hashBag elements none)
          ((decomposeList block elements).toPattern block) := by
    match elements, typed with
    | [], typed =>
        refine ⟨by simp [decomposeList, Members], ?_⟩
        simpa [decomposeList, Prenex.toPattern, Prenex.restricts] using bag_body_equivalent typed
    | element :: elements, typed =>
        have elementTyped := typed element List.mem_cons_self
        have restTyped : Members language block free bound elements := fun other member => typed other (List.mem_cons_of_mem _ member)
        obtain ⟨firstMembers, firstEquivalent⟩ := decompose_sound elementTyped
        obtain ⟨secondMembers, secondEquivalent⟩ := decomposeList_sound restTyped
        rw [decomposeList]
        refine ⟨par_members firstMembers secondMembers, ?_⟩
        have outer : Members language block free bound [element, .collection .hashBag elements none] :=
          Members.cons elementTyped (Members.cons (bag_typed restTyped) Members.nil)
        have flat := laws.flatten
          (pre := [element]) (inner := elements) (post := []) (bag_typed outer)
        simp only [List.append_nil, List.cons_append, List.nil_append] at flat
        have firstTyped := (SortedEquiv.typed_iff firstEquivalent).mp elementTyped
        have left := bag_fill (before := []) (after := [.collection .hashBag elements none]) (rest := none) Members.nil
          (Members.cons (bag_typed restTyped) Members.nil) firstEquivalent
        have right := bag_fill (before := [((decompose block element).toPattern block)]) (after := []) (rest := none)
          (Members.cons firstTyped Members.nil) Members.nil secondEquivalent
        simp only [List.nil_append, List.cons_append] at left right
        exact .trans _ _ _ (.symm _ _ (SortedEquiv.ofDerived flat (bag_typed outer) (bag_typed typed)))
          (.trans _ _ _ left (.trans _ _ _ right (par_equivalent firstMembers secondMembers)))
  termination_by sizeOf elements
  decreasing_by all_goals sizeOf_pattern_dec
end

/-! ## Reordering restrictions -/

open Mettapedia.OSLF.MeTTaIL.CanonicalBags (indexRenaming lift_renaming liftIndex)

theorem rename_comp (first second : Nat → Nat) (pattern : Pattern) :
    rename first (rename second pattern) = rename (first ∘ second) pattern := by
  rw [rename, rename, Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute_comp]
  rfl

theorem rename_id (pattern : Pattern) : rename id pattern = pattern :=
  Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute_id pattern

theorem liftIndex_succ (count : Nat) (relabel : Nat → Nat) :
    liftIndex count (liftIndex 1 relabel) = liftIndex (count + 1) relabel := by
  funext index
  simp only [liftIndex, Nat.sub_sub]
  split_ifs <;> omega

/-- A renaming reaches through a block, past its restrictions. -/
theorem rename_restricts : ∀ (count : Nat) (relabel : Nat → Nat) (body : Pattern),
    rename relabel (Prenex.restricts block count body) = Prenex.restricts block count (rename (liftIndex count relabel) body)
  | 0, relabel, body => by
      have same : liftIndex 0 relabel = relabel := by
        funext index
        simp [liftIndex]
      rw [same]
      rfl
  | count + 1, relabel, body => by
      have step : rename relabel (Prenex.restricts block (count + 1) body) =
          .apply block.restrict [.lambda none (rename (liftIndex 1 relabel) (Prenex.restricts block count body))] := by
        show substitute (indexRenaming relabel) _ = _
        simp only [Prenex.restricts, substitute, substituteList_eq_map, List.map_cons, List.map_nil, lift_renaming]
        rfl
      rw [step, rename_restricts count (liftIndex 1 relabel) body, liftIndex_succ]
      rfl

/-- Renaming the body of a bag renames its members. -/
theorem rename_body (relabel : Nat → Nat) (elements : List Pattern) :
    rename relabel (Prenex.body block elements) = Prenex.body block (elements.map (rename relabel)) := by
  match elements with
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: _ => simp [Prenex.body, rename, substitute, substituteList_eq_map]

/-- Exchange the bound variables `position` and `position + 1`. -/
def swapAt (position index : Nat) : Nat :=
  if index = position then position + 1 else if index = position + 1 then position else index

theorem liftIndex_swapInner (position : Nat) : liftIndex position swapInner = swapAt position := by
  funext index
  simp only [liftIndex, swapInner, swapAt]
  split_ifs <;> omega

/-- **A renaming that keeps the sort of every variable keeps the typing.** -/
theorem rename_typed {free : FreeTypeContext} {source target : List TypeExpr} {pattern : Pattern}
    {type : TypeExpr} {relabel : Nat → Nat} (typed : HasType language free source pattern type)
    (sorts : ∀ index sort, source[index]? = some sort → target[relabel index]? = some sort) :
    HasType language free target (rename relabel pattern) type :=
  HasType.substituteBoundOnSupport typed (fun index => .bvar (relabel index))
    (fun index sort _ lookup => Mettapedia.GSLT.LanguageDef.WellSorted.HasType.bvar (sorts index sort lookup))

/-- Exchanging two restrictions of a block keeps every variable's sort. -/
theorem swapAt_sorts {count position : Nat} (inside : position + 1 < count) (bound : List TypeExpr) :
    ∀ index sort, (List.replicate count (TypeExpr.base block.name) ++ bound)[index]? = some sort →
      (List.replicate count (TypeExpr.base block.name) ++ bound)[swapAt position index]? = some sort := by
  intro index sort lookup
  by_cases small : index < count
  · have swappedSmall : swapAt position index < count := by
      unfold swapAt
      split_ifs <;> omega
    rw [List.getElem?_append_left (by simpa using small), List.getElem?_replicate] at lookup
    rw [List.getElem?_append_left (by simpa using swappedSmall), List.getElem?_replicate]
    simp_all
  · have same : swapAt position index = index := by
      unfold swapAt
      split_ifs <;> omega
    rw [same]
    exact lookup

omit laws in
theorem swapped_members {free : FreeTypeContext} {bound : List TypeExpr} {count position : Nat}
    {components : List Pattern} (inside : position + 1 < count)
    (members : Members language block free (List.replicate count (TypeExpr.base block.name) ++ bound) components) :
    Members language block free (List.replicate count (TypeExpr.base block.name) ++ bound) (components.map (rename (swapAt position))) := by
  intro element member
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
  exact rename_typed (members original originalMember) (swapAt_sorts inside bound)

/-- **Exchange as an equivalence**: two restrictions trade places, and the body's two innermost bound names are
exchanged. -/
theorem exchange_equivalent {free : FreeTypeContext} {bound : List TypeExpr} {body : Pattern}
    (typed : HasType language free (.base block.name :: .base block.name :: bound) body (.base block.proc)) :
    ProcEquiv language block free bound (.apply block.restrict [.lambda none (.apply block.restrict [.lambda none body])])
      (.apply block.restrict [.lambda none (.apply block.restrict [.lambda none (rename swapInner body)])]) := by
  have swappedTyped : HasType language free (.base block.name :: .base block.name :: bound) (rename swapInner body)
      (.base block.proc) :=
    rename_typed typed fun index sort lookup => by
      rcases index with _ | _ | index <;> simp_all [swapInner]
  have wellScoped : body.isWellScopedAt (2 + bound.length) = true := by
    have := Mettapedia.GSLT.LanguageDef.WellSorted.HasType.isWellScopedAt typed
    simp only [List.length_cons] at this
    rwa [show 2 + bound.length = bound.length + 1 + 1 by omega]
  have swappedScoped : (rename swapInner body).isWellScopedAt (2 + bound.length) = true := by
    have := Mettapedia.GSLT.LanguageDef.WellSorted.HasType.isWellScopedAt swappedTyped
    simp only [List.length_cons] at this
    rwa [show 2 + bound.length = bound.length + 1 + 1 by omega]
  exact SortedEquiv.ofInstance ⟨0, .declared (orientation := .forward) (ambient := bound.length)
    laws.exchange_mem rfl
    (declaredInstanceAt_of_applyEquationAt (exchange_instance wellScoped swappedScoped))⟩
    (restrict_typed (restrict_typed typed)) (restrict_typed (restrict_typed swappedTyped))

omit laws in
theorem replicate_split {count position : Nat} (inside : position + 1 < count) (sort : TypeExpr)
    (bound : List TypeExpr) :
    List.replicate count sort ++ bound =
      List.replicate position sort ++ (sort :: sort :: (List.replicate (count - position - 2) sort ++ bound)) := by
  obtain ⟨rest, rfl⟩ : ∃ rest, count = position + 2 + rest := ⟨count - position - 2, by omega⟩
  rw [show position + 2 + rest - position - 2 = rest by omega]
  simp [List.replicate_add, List.append_assoc]

/-- **Two neighbouring restrictions of a block in either order.** -/
theorem block_exchange_equivalent {free : FreeTypeContext} {bound : List TypeExpr} {count position : Nat}
    {components : List Pattern} (inside : position + 1 < count)
    (members : Members language block free (List.replicate count (TypeExpr.base block.name) ++ bound) components) :
    ProcEquiv language block free bound ((Prenex.toPattern block) ⟨count, components⟩)
      ((Prenex.toPattern block) ⟨count, components.map (rename (swapAt position))⟩) := by
  have swapped : rename swapInner (Prenex.restricts block position (Prenex.body block components)) =
      Prenex.restricts block position (Prenex.body block (components.map (rename (swapAt position)))) := by
    rw [rename_restricts, liftIndex_swapInner, rename_body]
  have bodyTyped := body_typed members
  rw [replicate_split inside] at bodyTyped
  have exchanged := exchange_equivalent (restricts_typed position bodyTyped)
  rw [swapped] at exchanged
  have whole := restricts_congr (count - position - 2) (bound := bound) exchanged
  have split : ∀ body : Pattern, Prenex.restricts block count body =
      Prenex.restricts block (count - position - 2) (Prenex.restricts block 2 (Prenex.restricts block position body)) := by
    intro body
    rw [restricts_add, restricts_add, show count - position - 2 + 2 + position = count by omega]
  simp only [Prenex.toPattern]
  rw [split, split]
  exact whole

/-! ### Orders reached by exchanging neighbours -/

/-- Exchange the members at `position` and `position + 1`. -/
def swapAdjacent {α : Type} : Nat → List α → List α
  | 0, first :: second :: rest => second :: first :: rest
  | position + 1, first :: rest => first :: swapAdjacent position rest
  | _, list => list

/-- One list reaches another by exchanging neighbours. -/
def Reorders {α : Type} : List α → List α → Prop :=
  Relation.ReflTransGen fun list next => ∃ position, position + 1 < list.length ∧ next = swapAdjacent position list

theorem swapAdjacent_length {α : Type} : ∀ (position : Nat) (list : List α),
    (swapAdjacent position list).length = list.length
  | 0, _ :: _ :: _ => rfl
  | 0, [] => rfl
  | 0, [_] => rfl
  | _ + 1, [] => rfl
  | position + 1, _ :: rest => by simp [swapAdjacent, swapAdjacent_length position rest]

theorem Reorders.length {α : Type} {list next : List α} (reorders : Reorders list next) :
    next.length = list.length := by
  induction reorders with
  | refl => rfl
  | tail _ step recurse =>
      obtain ⟨position, _, rfl⟩ := step
      rw [swapAdjacent_length, recurse]

theorem Reorders.cons {α : Type} (head : α) {list next : List α} (reorders : Reorders list next) :
    Reorders (head :: list) (head :: next) := by
  induction reorders with
  | refl => exact .refl
  | tail _ step recurse =>
      obtain ⟨position, inside, rfl⟩ := step
      exact .tail recurse ⟨position + 1, by simpa using inside, rfl⟩

theorem insertions_reorders {α : Type} (element : α) : ∀ (list : List α), ∀ next ∈ insertions element list,
    Reorders (element :: list) next
  | [], next, member => by
      simp only [insertions, List.mem_singleton] at member
      rw [member]
      exact .refl
  | first :: rest, next, member => by
      simp only [insertions, List.mem_cons, List.mem_map] at member
      rcases member with rfl | ⟨inserted, insertedMember, rfl⟩
      · exact .refl
      · exact .head ⟨0, by simp, rfl⟩ ((insertions_reorders element rest inserted insertedMember).cons first)

/-- **Every order is reached by exchanging neighbours.** -/
theorem orders_reorders {α : Type} : ∀ (list : List α), ∀ order ∈ orders list, Reorders list order
  | [], order, member => by
      simp only [orders, List.mem_singleton] at member
      rw [member]
      exact .refl
  | first :: rest, order, member => by
      simp only [orders, List.mem_flatMap] at member
      obtain ⟨middle, middleMember, inserted⟩ := member
      exact ((orders_reorders rest middle middleMember).cons first).trans
        (insertions_reorders first middle order inserted)

theorem swapAt_succ (position index : Nat) : swapAt (position + 1) (index + 1) = swapAt position index + 1 := by
  simp only [swapAt]
  split_ifs <;> omega

theorem swapAdjacent_getElem? {α : Type} : ∀ (position : Nat) (list : List α), position + 1 < list.length →
    ∀ index, (swapAdjacent position list)[index]? = list[swapAt position index]?
  | 0, first :: second :: rest, _, index => by
      match index with
      | 0 => rfl
      | 1 => rfl
      | index + 2 =>
          rw [show swapAt 0 (index + 2) = index + 2 by simp [swapAt]]
          rfl
  | position + 1, first :: rest, inside, index => by
      match index with
      | 0 =>
          rw [show swapAt (position + 1) 0 = 0 by simp [swapAt]]
          rfl
      | index + 1 =>
          rw [swapAt_succ]
          simp only [swapAdjacent, List.getElem?_cons_succ]
          exact swapAdjacent_getElem? position rest (by simpa using inside) index
  | 0, [], inside, _ => absurd inside (by simp)
  | 0, [_], inside, _ => absurd inside (by simp)
  | _ + 1, [], inside, _ => absurd inside (by simp)

theorem permute_swapAdjacent {count position : Nat} {order : List Nat} (length : order.length = count)
    (inside : position + 1 < count) :
    Prenex.permute count (swapAdjacent position order) = Prenex.permute count order ∘ swapAt position := by
  funext index
  simp only [Prenex.permute, Function.comp]
  by_cases small : index < count
  · have swappedSmall : swapAt position index < count := by
      unfold swapAt
      split_ifs <;> omega
    rw [if_pos small, if_pos swappedSmall, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      swapAdjacent_getElem? position order (by omega) index]
    rw [List.getElem?_eq_getElem (by omega)]
    rfl
  · have same : swapAt position index = index := by
      unfold swapAt
      split_ifs <;> omega
    rw [if_neg small, same, if_neg small]

theorem permute_range (count : Nat) : Prenex.permute count (List.range count) = id := by
  funext index
  simp only [Prenex.permute, id]
  split_ifs with small
  · rw [List.getD_eq_getElem?_getD, List.getElem?_range small]
    rfl
  · rfl

/-- **Reordering a block's restrictions is sound**, for every order reached by exchanging neighbours. -/
theorem block_reorder_equivalent {free : FreeTypeContext} {bound : List TypeExpr} {count : Nat} {order : List Nat}
    (reorders : Reorders (List.range count) order) :
    ∀ {components : List Pattern}, Members language block free (List.replicate count (TypeExpr.base block.name) ++ bound) components →
      Members language block free (List.replicate count (TypeExpr.base block.name) ++ bound)
          (components.map (rename (Prenex.permute count order))) ∧
        ProcEquiv language block free bound ((Prenex.toPattern block) ⟨count, components⟩)
          ((Prenex.toPattern block) ⟨count, components.map (rename (Prenex.permute count order))⟩) := by
  induction reorders with
  | refl =>
      intro components members
      rw [permute_range]
      have same : components.map (rename id) = components := by
        conv_rhs => rw [← List.map_id components]
        exact List.map_congr_left fun component _ => rename_id component
      rw [same]
      exact ⟨members, .refl _⟩
  | @tail middle next reached step recurse =>
      intro components members
      obtain ⟨position, inside, rfl⟩ := step
      have length : middle.length = count := by simpa using Reorders.length reached
      rw [length] at inside
      rw [permute_swapAdjacent length inside]
      have split : components.map (rename (Prenex.permute count middle ∘ swapAt position)) =
          (components.map (rename (swapAt position))).map (rename (Prenex.permute count middle)) := by
        rw [List.map_map]
        exact List.map_congr_left fun component _ => (rename_comp _ _ component).symm
      rw [split]
      obtain ⟨movedMembers, moved⟩ := recurse (swapped_members inside members)
      exact ⟨movedMembers, .trans _ _ _ (block_exchange_equivalent inside members) moved⟩

/-! ## The canonical form is sound -/

open Mettapedia.GSLT.LanguageDef.WellSorted (hasType_apply_inversion parameterType? UsesBareCollection
  ArgumentsHaveTypes MatchesParameterRepresentation ElementsHaveType)
open Mettapedia.GSLT.LanguageDef.BagNormalForm (argumentsHaveTypes_join)

/-- Equivalent members make equivalent bags. -/
theorem collection_congr {free : FreeTypeContext} {bound : List TypeExpr} (rest : Option String)
    {first second : List Pattern} (firstMembers : Members language block free bound first)
    (related : List.Forall₂ (ProcEquiv language block free bound) first second) :
    ∀ pre, Members language block free bound pre →
      ProcEquiv language block free bound (.collection .hashBag (pre ++ first) rest)
        (.collection .hashBag (pre ++ second) rest) := by
  revert firstMembers
  induction related with
  | nil => intro _ pre _; exact .refl _
  | @cons head head' tail tail' here _ recurse =>
      intro firstMembers pre preMembers
      have filled := bag_fill (rest := rest) preMembers firstMembers.tail here
      have head'Typed := (SortedEquiv.typed_iff here).mp (firstMembers head List.mem_cons_self)
      have later := recurse firstMembers.tail (pre ++ [head']) (preMembers.append (Members.cons head'Typed Members.nil))
      simp only [List.append_assoc, List.singleton_append] at later
      exact .trans _ _ _ filled later

/-- Equivalent members make equivalent bodies. -/
theorem body_congr {free : FreeTypeContext} {bound : List TypeExpr} {first second : List Pattern}
    (firstMembers : Members language block free bound first)
    (related : List.Forall₂ (ProcEquiv language block free bound) first second) :
    ProcEquiv language block free bound (Prenex.body block first) (Prenex.body block second) := by
  cases related with
  | nil => exact .refl _
  | cons here tail =>
      cases tail with
      | nil => exact here
      | cons here' tail' =>
          exact collection_congr none firstMembers (.cons here (.cons here' tail')) [] Members.nil

/-- **A body in any order of its members.** -/
theorem body_perm_equivalent {free : FreeTypeContext} {bound : List TypeExpr} {first second : List Pattern}
    (members : Members language block free bound first) (permutation : first.Perm second) :
    ProcEquiv language block free bound (Prenex.body block first) (Prenex.body block second) := by
  have secondMembers : Members language block free bound second :=
    fun element member => members element (permutation.symm.subset member)
  exact .trans _ _ _ (.symm _ _ (bag_body_equivalent members))
    (.trans _ _ _ (SortedEquiv.ofDerived
      (DerivedInstance.bagPerm_of_sorted ⟨free, bound, bag_typed members⟩ permutation)
      (bag_typed members) (bag_typed secondMembers))
      (bag_body_equivalent secondMembers))

theorem least_mem : ∀ {candidates : List (List Pattern)}, candidates ≠ [] → least candidates ∈ candidates
  | first :: rest, _ => by
      unfold least
      suffices chosen : ∀ (pending : List (List Pattern)) (best : List Pattern), best ∈ first :: rest →
          pending ⊆ first :: rest →
          pending.foldl (fun best next => if serList next < serList best then next else best)
            best ∈ first :: rest from
        chosen rest first List.mem_cons_self (List.subset_cons_self _ _)
      intro pending
      induction pending with
      | nil => intro best bestMember _; exact bestMember
      | cons next more recurse =>
          intro best bestMember within
          simp only [List.foldl_cons]
          apply recurse
          · split_ifs
            · exact within List.mem_cons_self
            · exact bestMember
          · exact fun other member => within (List.mem_cons_of_mem _ member)

theorem insertions_ne_nil {α : Type} (element : α) : ∀ list, insertions element list ≠ []
  | [] => by simp [insertions]
  | _ :: _ => by simp [insertions]

theorem orders_ne_nil {α : Type} : ∀ (list : List α), orders list ≠ []
  | [] => by simp [orders]
  | first :: rest => by
      intro empty
      obtain ⟨order, member⟩ := List.exists_mem_of_ne_nil _ (orders_ne_nil rest)
      exact insertions_ne_nil first order (List.flatMap_eq_nil_iff.mp empty order member)

/-- A parameter of a base type takes any argument. -/
theorem representation_of_base {parameter : TermParam} {argument : Pattern} {sort : String}
    (typeIs : parameterType? parameter = some (.base sort)) : MatchesParameterRepresentation parameter argument := by
  cases parameter with
  | simple => trivial
  | abstractionNamed binder name type =>
      cases type <;> simp [parameterType?] at typeIs
  | multiAbstractionNamed binders name type =>
      cases type with
      | arrow domain codomain => cases domain <;> simp [parameterType?] at typeIs
      | _ => simp [parameterType?] at typeIs

/-- The representation of an abstraction does not read its body. -/
theorem representation_lambda {parameter : TermParam} {binder : Option String} {first second : Pattern}
    (representation : MatchesParameterRepresentation parameter (.lambda binder first)) :
    MatchesParameterRepresentation parameter (.lambda binder second) := by
  cases parameter <;> cases binder <;> simp_all [MatchesParameterRepresentation]

include laws in
/-- **A constructor application with canonical parts in its arguments**, given a sound canonical form of the terms
of every sort: the arguments are read left to right, each put back in place, the application keeping its sort. -/
theorem arguments_sound {free : FreeTypeContext} {bound : List TypeExpr} {canonical : Pattern → Pattern}
    (sound : ∀ {bound : List TypeExpr}, BaseContext free bound → ∀ {term : Pattern} {sort : String},
      HasType language free bound term (.base sort) →
      HasType language free bound (canonical term) (.base sort) ∧
        SortedEquiv language free bound (.base sort) term (canonical term))
    (context : BaseContext free bound)
    {rule : GrammarRule} (member : rule ∈ language.terms) (notBare : ¬ UsesBareCollection rule)
    (notMultiset : rule.label ∉ block.multisets) :
    ∀ (arguments : List Pattern) {before : List Pattern} {beforeParameters parameters : List TermParam},
      beforeParameters ++ parameters = rule.params →
      ArgumentsHaveTypes language free bound before beforeParameters →
      ArgumentsHaveTypes language free bound arguments parameters →
      ArgumentsHaveTypes language free bound (arguments.map (canonArgument canonical)) parameters ∧
        SortedEquiv language free bound (.base rule.category) (.apply rule.label (before ++ arguments))
          (.apply rule.label (before ++ arguments.map (canonArgument canonical))) := by
  intro arguments
  induction arguments with
  | nil =>
      intro before beforeParameters parameters _ _ typed
      cases typed
      exact ⟨.nil, .refl _⟩
  | cons argument arguments recurse =>
      intro before beforeParameters parameters split beforeTyped typed
      cases typed with
      | @cons _ _ _ parameter parameters expected representation typeIs argumentTyped restTyped =>
        have shape := laws.params rule member notBare notMultiset parameter (by rw [← split]; simp)
        have rebuild : ∀ middle, MatchesParameterRepresentation parameter middle →
            HasType language free bound middle expected →
            HasType language free bound (.apply rule.label (before ++ middle :: arguments)) (.base rule.category) := by
          intro middle middleRepresentation middleTyped
          have all := argumentsHaveTypes_join middleRepresentation typeIs middleTyped restTyped beforeTyped
          rw [split] at all
          exact Mettapedia.GSLT.LanguageDef.WellSorted.HasType.constructor member notBare all
        have here : HasType language free bound (canonArgument canonical argument) expected ∧
            MatchesParameterRepresentation parameter (canonArgument canonical argument) ∧
            SortedEquiv language free bound (.base rule.category) (.apply rule.label (before ++ argument :: arguments))
              (.apply rule.label (before ++ canonArgument canonical argument :: arguments)) := by
          cases argument with
          | bvar index => exact ⟨argumentTyped, representation, .refl _⟩
          | fvar name => exact ⟨argumentTyped, representation, .refl _⟩
          | subst body replacement => exact ⟨argumentTyped, representation, .refl _⟩
          | lambda binder body =>
              rcases shape with ⟨sort, base⟩ | ⟨domain, sort, abstraction⟩
              · rw [typeIs, Option.some.injEq] at base
                subst base
                cases argumentTyped
              · rw [typeIs, Option.some.injEq] at abstraction
                subst abstraction
                cases argumentTyped with
                | lambda bodyTyped =>
                    obtain ⟨canonTyped, chain⟩ := sound (context.cons domain) bodyTyped
                    exact ⟨.lambda canonTyped, representation_lambda representation,
                      SortedEquiv.fill (.apply rule.label before (.lambda binder .hole) arguments)
                        (fun _ fillingTyped => rebuild _ (representation_lambda representation) (.lambda fillingTyped))
                        chain⟩
          | apply constructor inner =>
              rcases shape with ⟨sort, base⟩ | ⟨domain, sort, abstraction⟩
              · rw [typeIs, Option.some.injEq] at base
                subst base
                obtain ⟨canonTyped, chain⟩ := sound context argumentTyped
                exact ⟨canonTyped, representation_of_base typeIs,
                  SortedEquiv.fill (.apply rule.label before .hole arguments)
                    (fun _ fillingTyped => rebuild _ (representation_of_base typeIs) fillingTyped) chain⟩
              · rw [typeIs, Option.some.injEq] at abstraction
                subst abstraction
                cases argumentTyped
          | multiLambda arity binders body =>
              rcases shape with ⟨sort, base⟩ | ⟨domain, sort, abstraction⟩
              · rw [typeIs, Option.some.injEq] at base
                subst base
                cases argumentTyped
              · rw [typeIs, Option.some.injEq] at abstraction
                subst abstraction
                cases argumentTyped
          | collection kind elements rest =>
              rcases shape with ⟨sort, base⟩ | ⟨domain, sort, abstraction⟩
              · rw [typeIs, Option.some.injEq] at base
                subst base
                obtain ⟨canonTyped, chain⟩ := sound context argumentTyped
                exact ⟨canonTyped, representation_of_base typeIs,
                  SortedEquiv.fill (.apply rule.label before .hole arguments)
                    (fun _ fillingTyped => rebuild _ (representation_of_base typeIs) fillingTyped) chain⟩
              · rw [typeIs, Option.some.injEq] at abstraction
                subst abstraction
                rcases Mettapedia.GSLT.LanguageDef.WellSorted.hasType_collection_inversion argumentTyped with
                  ⟨_, typeIs', _⟩ | ⟨_, _, _, _, _, typeIs', _⟩ <;> cases typeIs'
        obtain ⟨hereTyped, hereRepresentation, hereChain⟩ := here
        obtain ⟨restCanon, restChain⟩ := recurse (before := before ++ [canonArgument canonical argument])
          (beforeParameters := beforeParameters ++ [parameter]) (by rw [List.append_assoc]; exact split)
          (argumentsHaveTypes_join hereRepresentation typeIs hereTyped .nil beforeTyped) restTyped
        refine ⟨.cons hereRepresentation typeIs hereTyped restCanon, ?_⟩
        simp only [List.append_assoc, List.singleton_append] at restChain
        simp only [List.map_cons]
        exact .trans _ _ _ hereChain restChain

omit laws in
/-- **Related members make related collections**, over any element type. -/
theorem elements_congr {free : FreeTypeContext} {bound : List TypeExpr} (rest : Option String) {elementType : TypeExpr}
    {first second : List Pattern} (firstTyped : ∀ element ∈ first, HasType language free bound element elementType)
    (related : List.Forall₂ (SortedEquiv language free bound elementType) first second) :
    ∀ pre, (∀ element ∈ pre, HasType language free bound element elementType) →
      SortedEquiv language free bound (.collection .hashBag elementType) (.collection .hashBag (pre ++ first) rest)
        (.collection .hashBag (pre ++ second) rest) := by
  revert firstTyped
  induction related with
  | nil => intro _ pre _; exact .refl _
  | @cons head head' tail tail' here _ recurse =>
      intro firstTyped pre preTyped
      have tailTyped : ∀ element ∈ tail, HasType language free bound element elementType := fun element member =>
        firstTyped element (List.mem_cons_of_mem _ member)
      have filled := SortedEquiv.fill (holeSort := elementType) (.collection .hashBag pre .hole tail rest)
        (fun filling fillingTyped => by
          show HasType language free bound (.collection .hashBag (pre ++ filling :: tail) rest)
            (.collection .hashBag elementType)
          refine .collection (elementsHaveType_iff.mpr ?_)
          intro element member
          simp only [List.mem_append, List.mem_cons] at member
          rcases member with inPre | rfl | inTail
          · exact preTyped element inPre
          · exact fillingTyped
          · exact tailTyped element inTail) here
      simp only [OneHoleContext.fill] at filled
      have head'Typed := (SortedEquiv.typed_iff here).mp (firstTyped head List.mem_cons_self)
      have later := recurse tailTyped (pre ++ [head']) (fun element member => by
        rcases List.mem_append.mp member with inPre | single
        · exact preTyped element inPre
        · rw [List.mem_singleton.mp single]; exact head'Typed)
      simp only [List.append_assoc, List.singleton_append] at later
      exact .trans _ _ _ filled later

omit laws in
/-- The canonical form of a term that is its own block is that of its parts. -/
theorem canonWith_atom (fuel : Nat) {term : Pattern} (isAtom : decompose block term = Prenex.atom term) :
    canonWith block (fuel + 1) term = canonComponentWith block fuel term := by
  have identity : Prenex.permute 0 [] = id := permute_range 0
  simp [canonWith, isAtom, Prenex.atom, orders, identity, rename_id, sortComponents, least, Prenex.toPattern,
    Prenex.restricts, Prenex.body]

mutual
  /-- **The canonical form is sound**: a term of a sort is related to its canonical form, which has the same sort,
  by a chain of laws through terms of that sort. -/
  theorem canonWith_sound {free : FreeTypeContext} :
      ∀ (fuel : Nat) {bound : List TypeExpr}, BaseContext free bound → ∀ {process : Pattern} {sort : String},
        HasType language free bound process (.base sort) →
        HasType language free bound (canonWith block fuel process) (.base sort) ∧
          SortedEquiv language free bound (.base sort) process (canonWith block fuel process)
    | 0, _, _, _, _, typed => ⟨typed, .refl _⟩
    | fuel + 1, bound, context, process, sort, typed => by
        by_cases isProc : sort = block.proc
        swap
        · rw [canonWith_atom fuel (decompose_other typed isProc)]
          exact canonComponentWith_sound fuel context typed
        subst isProc
        obtain ⟨decomposedMembers, decomposed⟩ := decompose_sound typed
        simp only [canonWith]
        generalize decompose block process = form at decomposedMembers decomposed ⊢
        obtain ⟨count, components⟩ := form
        simp only at decomposedMembers ⊢
        have nonempty : ((orders (List.range count)).map fun order => sortComponents (components.map
            fun component => canonComponentWith block fuel (rename (Prenex.permute count order) component))) ≠ [] := by
          simpa using orders_ne_nil (List.range count)
        obtain ⟨order, orderMember, chosen⟩ := List.mem_map.mp (least_mem nonempty)
        rw [← chosen]
        obtain ⟨renamedMembers, renamed⟩ :=
          block_reorder_equivalent (orders_reorders _ order orderMember) decomposedMembers
        generalize renamedIs : components.map (rename (Prenex.permute count order)) = renamedList
          at renamedMembers renamed
        have mapped : components.map (fun component =>
            canonComponentWith block fuel (rename (Prenex.permute count order) component)) =
            renamedList.map (canonComponentWith block fuel) := by
          rw [← renamedIs, List.map_map]
          rfl
        rw [mapped]
        have parts : ∀ component ∈ renamedList,
            HasType language free (List.replicate count (.base block.name) ++ bound)
                (canonComponentWith block fuel component) (.base block.proc) ∧
              ProcEquiv language block free (List.replicate count (.base block.name) ++ bound) component
                (canonComponentWith block fuel component) :=
          fun component member => canonComponentWith_sound fuel (context.replicate count block.name)
            (renamedMembers component member)
        have canonMembers : Members language block free (List.replicate count (.base block.name) ++ bound)
            (renamedList.map (canonComponentWith block fuel)) := by
          intro element member
          obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
          exact (parts original originalMember).1
        have related : List.Forall₂ (ProcEquiv language block free (List.replicate count (.base block.name) ++ bound))
            renamedList (renamedList.map (canonComponentWith block fuel)) := by
          rw [List.forall₂_map_right_iff]
          exact List.forall₂_same.mpr fun component member => (parts component member).2
        have sortedPerm : (renamedList.map (canonComponentWith block fuel)).Perm
            (sortComponents (renamedList.map (canonComponentWith block fuel))) := (List.perm_insertionSort _ _).symm
        have sortedMembers : Members language block free (List.replicate count (.base block.name) ++ bound)
            (sortComponents (renamedList.map (canonComponentWith block fuel))) :=
          fun element member => canonMembers element (sortedPerm.symm.subset member)
        refine ⟨restricts_typed count (body_typed sortedMembers), ?_⟩
        exact .trans _ _ _ decomposed (.trans _ _ _ renamed
          (.trans _ _ _ (restricts_congr count (body_congr renamedMembers related))
            (restricts_congr count (body_perm_equivalent canonMembers sortedPerm))))

  /-- A component is related to the component with canonical parts. -/
  theorem canonComponentWith_sound {free : FreeTypeContext} :
      ∀ (fuel : Nat) {bound : List TypeExpr}, BaseContext free bound → ∀ {component : Pattern} {sort : String},
        HasType language free bound component (.base sort) →
        HasType language free bound (canonComponentWith block fuel component) (.base sort) ∧
          SortedEquiv language free bound (.base sort) component (canonComponentWith block fuel component)
    | 0, _, _, _, _, typed => ⟨typed, .refl _⟩
    | fuel + 1, bound, context, component, sort, typed => by
        cases component with
        | bvar index => exact ⟨typed, .refl _⟩
        | fvar name => exact ⟨typed, .refl _⟩
        | subst body replacement => exact ⟨typed, .refl _⟩
        | lambda binder body => cases typed
        | multiLambda arity binders body => cases typed
        | apply constructor arguments =>
            by_cases isMultiset : constructor ∈ block.multisets
            · obtain ⟨rule, member, labelIs, notBare, typeIs, parameterName, elementSort, argument, params, other,
                rfl, argumentTyped⟩ := multiset_argument typed isMultiset
              have carrier : ∃ rule ∈ language.terms, ∃ parameter ∈ rule.params,
                  CollectionTypeOccurs .hashBag (.base elementSort) parameter.typeExpr :=
                ⟨rule, member, _, by rw [params]; exact List.mem_singleton_self _, .here⟩
              obtain ⟨canonTyped, chain⟩ := canonMultisetWith_sound fuel context other carrier argumentTyped
              simp only [canonComponentWith, if_pos isMultiset, List.map_cons, List.map_nil]
              have rebuild : ∀ filling, HasType language free bound filling (.collection .hashBag (.base elementSort)) →
                  HasType language free bound (OneHoleContext.fill (.apply constructor [] .hole []) filling)
                    (.base sort) := by
                intro filling fillingTyped
                have built := Mettapedia.GSLT.LanguageDef.WellSorted.HasType.constructor (arguments := [filling])
                  member notBare (by rw [params]; exact .cons trivial rfl fillingTyped .nil)
                rw [labelIs, ← typeIs] at built
                simpa [OneHoleContext.fill] using built
              have filled := SortedEquiv.fill (.apply constructor [] .hole []) rebuild chain
              simp only [OneHoleContext.fill, List.nil_append] at filled
              exact ⟨by simpa [OneHoleContext.fill] using rebuild _ canonTyped, filled⟩
            · obtain ⟨rule, member, labelIs, notBare, typeIs, argumentsTyped⟩ := hasType_apply_inversion typed
              obtain ⟨canonArguments, chain⟩ := arguments_sound (block := block)
                (fun context' => canonWith_sound fuel context') context member
                notBare (by rw [← labelIs]; exact isMultiset) arguments (before := []) (beforeParameters := []) rfl .nil
                argumentsTyped
              have rebuilt := Mettapedia.GSLT.LanguageDef.WellSorted.HasType.constructor member notBare canonArguments
              simp only [List.nil_append] at chain
              rw [← labelIs, ← typeIs] at rebuilt chain
              simp only [canonComponentWith, if_neg isMultiset]
              exact ⟨rebuilt, chain⟩
        | collection kind elements rest =>
            rcases Mettapedia.GSLT.LanguageDef.WellSorted.hasType_collection_inversion typed with
              ⟨_, typeIs, _⟩ | ⟨rule, _, _, member, shape, typeIs, elementsTyped⟩
            · cases typeIs
            · obtain ⟨rfl, rfl, category⟩ := laws.bare_shape member shape
              have elementMembers : Members language block free bound elements :=
                fun element member => elementsHaveType_iff.mp elementsTyped element member
              have parts : ∀ element ∈ elements,
                  HasType language free bound (canonWith block fuel element) (.base block.proc) ∧
                    ProcEquiv language block free bound element (canonWith block fuel element) :=
                fun element member => canonWith_sound fuel context (elementMembers element member)
              have canonTyped : ElementsHaveType language free bound (elements.map (canonWith block fuel))
                  (.base block.proc) := by
                refine elementsHaveType_iff.mpr ?_
                intro element member
                obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
                exact (parts original originalMember).1
              have related : List.Forall₂ (ProcEquiv language block free bound) elements
                  (elements.map (canonWith block fuel)) := by
                rw [List.forall₂_map_right_iff]
                exact List.forall₂_same.mpr fun element member => (parts element member).2
              have rebuilt := Mettapedia.GSLT.LanguageDef.WellSorted.HasType.collectionConstructor (rest := rest)
                member shape canonTyped
              have chain := collection_congr rest elementMembers related [] Members.nil
              simp only [List.nil_append] at chain
              rw [category] at rebuilt typeIs
              rw [typeIs]
              exact ⟨rebuilt, chain⟩

  /-- **The canonical argument of a named multiset is sound**: a bag of terms of another sort than processes is
  related to its canonical multiset, the same members with canonical parts, sorted. -/
  theorem canonMultisetWith_sound {free : FreeTypeContext} :
      ∀ (fuel : Nat) {bound : List TypeExpr}, BaseContext free bound → ∀ {argument : Pattern} {sort : String},
        sort ≠ block.proc →
        (∃ rule ∈ language.terms, ∃ parameter ∈ rule.params,
          CollectionTypeOccurs .hashBag (.base sort) parameter.typeExpr) →
        HasType language free bound argument (.collection .hashBag (.base sort)) →
        HasType language free bound (canonMultisetWith block fuel argument) (.collection .hashBag (.base sort)) ∧
          SortedEquiv language free bound (.collection .hashBag (.base sort)) argument
            (canonMultisetWith block fuel argument)
    | 0, _, _, _, _, _, _, typed => ⟨typed, .refl _⟩
    | fuel + 1, bound, context, argument, sort, other, carrier, typed => by
        cases argument with
        | bvar index =>
            cases typed with
            | bvar lookup =>
                obtain ⟨sort', isBase⟩ := context.bound _ (List.mem_of_getElem? lookup)
                cases isBase
        | fvar name =>
            cases typed with
            | fvar lookup =>
                obtain ⟨sort', isBase⟩ := context.free name _ lookup
                cases isBase
        | apply constructor arguments =>
            obtain ⟨_, _, _, _, typeIs, _⟩ := hasType_apply_inversion typed
            cases typeIs
        | lambda binder body => cases typed
        | multiLambda arity binders body => cases typed
        | subst body replacement => exact ⟨typed, .refl _⟩
        | collection kind elements rest =>
            rcases Mettapedia.GSLT.LanguageDef.WellSorted.hasType_collection_inversion typed with
              ⟨elementType, typeIs, elementsTyped⟩ | ⟨rule, -, -, -, -, typeIs, -⟩
            swap
            · cases typeIs
            simp only [TypeExpr.collection.injEq] at typeIs
            obtain ⟨rfl, rfl⟩ := typeIs
            have membersTyped : ∀ element ∈ elements, HasType language free bound element (.base sort) :=
              fun element member => elementsHaveType_iff.mp elementsTyped element member
            cases rest with
            | some name =>
                have parts : ∀ element ∈ elements,
                    HasType language free bound (canonWith block fuel element) (.base sort) ∧
                      SortedEquiv language free bound (.base sort) element (canonWith block fuel element) :=
                  fun element member => canonWith_sound fuel context (membersTyped element member)
                have related : List.Forall₂ (SortedEquiv language free bound (.base sort)) elements
                    (elements.map (canonWith block fuel)) := by
                  rw [List.forall₂_map_right_iff]
                  exact List.forall₂_same.mpr fun element member => (parts element member).2
                have chain := elements_congr (some name) membersTyped related [] (by simp)
                simp only [List.nil_append] at chain
                refine ⟨.collection (elementsHaveType_iff.mpr fun element member => ?_), chain⟩
                obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
                exact (parts original originalMember).1
            | none =>
                have atoms : ∀ element ∈ elements, decompose block element = Prenex.atom element :=
                  fun element member => decompose_other (membersTyped element member) other
                have identity : Prenex.permute 0 [] = id := permute_range 0
                have unfolded : canonMultisetWith block (fuel + 1) (.collection .hashBag elements none) =
                    .collection .hashBag (sortComponents (elements.map (canonComponentWith block fuel))) none := by
                  simp only [canonMultisetWith, decompose_bag, decomposeList_atoms atoms, List.range_zero, orders,
                    List.map_cons, List.map_nil, identity, rename_id, least, List.foldl_nil, multisetOf, if_pos]
                rw [unfolded]
                have parts : ∀ element ∈ elements,
                    HasType language free bound (canonComponentWith block fuel element) (.base sort) ∧
                      SortedEquiv language free bound (.base sort) element (canonComponentWith block fuel element) :=
                  fun element member => canonComponentWith_sound fuel context (membersTyped element member)
                have related : List.Forall₂ (SortedEquiv language free bound (.base sort)) elements
                    (elements.map (canonComponentWith block fuel)) := by
                  rw [List.forall₂_map_right_iff]
                  exact List.forall₂_same.mpr fun element member => (parts element member).2
                have canonTyped : ∀ element ∈ elements.map (canonComponentWith block fuel),
                    HasType language free bound element (.base sort) := by
                  intro element member
                  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
                  exact (parts original originalMember).1
                have chain := elements_congr none membersTyped related [] (by simp)
                simp only [List.nil_append] at chain
                have sortedPerm : (elements.map (canonComponentWith block fuel)).Perm
                    (sortComponents (elements.map (canonComponentWith block fuel))) :=
                  (List.perm_insertionSort _ _).symm
                have sortedTyped : HasType language free bound
                    (.collection .hashBag (sortComponents (elements.map (canonComponentWith block fuel))) none)
                    (.collection .hashBag (.base sort)) :=
                  .collection (elementsHaveType_iff.mpr fun element member =>
                    canonTyped element (sortedPerm.symm.subset member))
                have mappedTyped : HasType language free bound
                    (.collection .hashBag (elements.map (canonComponentWith block fuel)) none)
                    (.collection .hashBag (.base sort)) := .collection (elementsHaveType_iff.mpr canonTyped)
                obtain ⟨rule, member, parameter, parameterMember, occurs⟩ := carrier
                have reordered := SortedEquiv.ofDerived
                  (DerivedInstance.bagPerm member ⟨parameter, parameterMember, .base sort, occurs, free, bound,
                    mappedTyped⟩ sortedPerm) mappedTyped sortedTyped
                exact ⟨sortedTyped, .trans _ _ _ chain reordered⟩
end

/-- **The canonical form is sound**: every term of a sort is related to its canonical form by a chain of laws
through terms of that sort. -/
theorem canon_sound {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound)
    {process : Pattern} {sort : String} (typed : HasType language free bound process (.base sort)) :
    HasType language free bound (canon block process) (.base sort) ∧
      SortedEquiv language free bound (.base sort) process (canon block process) :=
  canonWith_sound _ context typed

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
