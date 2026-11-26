import Mettapedia.OSLF.MeTTaIL.EngineCoded.Premises

/-!
# The executable rule engine computed on codes

`rewriteAt base language fuel term` lists the reducts of a term justified within a
contextual depth. A premise that asks the step itself reduces a source built from
the bindings of the earlier premises, so the reducts at depth `fuel + 1` are a
dialogue with depth `fuel`: in round `r` every rule instance still running asks
for the reducts of its `r`-th premise's source, and the answers extend its
bindings (`processRound`). After as many rounds as the longest premise list, the
instances are the complete premise derivations, and their reducts are the
reducts of the term (`rewriteAt_succ_eq`). With a base evaluator computable on
codes, the engine is computable on codes (`rewriteAt_computable`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.EngineCoded

open Mettapedia.Computability
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical (matchPatternForRule)
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution (applyBindingsForRule)
open Mettapedia.OSLF.MeTTaIL.PatternCode
open CodeComputable

/-! ## One premise -/

/-- The source and target of a premise that asks the step itself. -/
def recursiveOf : Premise → Option (Pattern × Pattern)
  | .congruence source target => some (source, target)
  | .scopedStep step => if step.binders.isEmpty then some (step.source, step.target) else none
  | _ => none

/-- A premise answered without the step. -/
def directOf (base : BasePremiseEvaluator) (language : LanguageDef) (premise : Premise) (bindings : Bindings) :
    List Bindings :=
  match premise with
  | .congruence _ _ => []
  | .scopedStep _ => []
  | other => base language bindings other

/-- Bindings extended by the reducts of a premise's source that match its target. -/
def extendBy (bindings : Bindings) (target : Pattern) (candidates : List Pattern) : List Bindings :=
  candidates.flatMap fun candidate => (matchPattern target candidate).filterMap (mergeBindings bindings)

theorem premiseStepUsing_eq (base : BasePremiseEvaluator) (language : LanguageDef)
    (recursive : Pattern → List Pattern) (bindings : Bindings) (premise : Premise) :
    premiseStepUsing base language recursive bindings premise =
      Option.casesOn (motive := fun _ => List Bindings) (recursiveOf premise)
        (directOf base language premise bindings)
        fun step => extendBy bindings step.2 (recursive (Match.applyBindings bindings step.1)) := by
  cases premise with
  | scopedStep step =>
      by_cases empty : step.binders.isEmpty
      · simp [premiseStepUsing, recursiveOf, extendBy, empty]
      · simp [premiseStepUsing, recursiveOf, directOf, empty]
  | congruence source target => simp [premiseStepUsing, recursiveOf, extendBy]
  | _ => rfl

theorem premisesUsing_append (base : BasePremiseEvaluator) (language : LanguageDef)
    (recursive : Pattern → List Pattern) : ∀ (first second : List Premise) (bindings : Bindings),
      premisesUsing base language recursive (first ++ second) bindings =
        (premisesUsing base language recursive first bindings).flatMap
          (premisesUsing base language recursive second)
  | [], second, bindings => by simp [premisesUsing]
  | premise :: first, second, bindings => by
      simp only [List.cons_append, premisesUsing, List.flatMap_assoc]
      congr 1
      funext middle
      exact premisesUsing_append base language recursive first second middle

theorem premisesUsing_single (base : BasePremiseEvaluator) (language : LanguageDef)
    (recursive : Pattern → List Pattern) (premise : Premise) (bindings : Bindings) :
    premisesUsing base language recursive [premise] bindings =
      premiseStepUsing base language recursive bindings premise := by
  simp [premisesUsing]

/-! ## The rules and premises of a language, by position -/

/-- A rule without premises that never fires, for positions beyond the rules. -/
def noRule : RewriteRule := { name := "", typeContext := [], premises := [], left := .bvar 0, right := .bvar 0 }

/-- A premise for positions beyond a rule's premises. -/
def noPremise : Premise := .relationQuery "" []

/-- The rule at a position. -/
def ruleAt (language : LanguageDef) (index : ℕ) : RewriteRule := language.rewrites.getD index noRule

/-- The premise of a rule at a position. -/
def premiseAt (language : LanguageDef) (index round : ℕ) : Premise :=
  (ruleAt language index).premises.getD round noPremise

/-- How many premises the rule at a position has. -/
def countAt (language : LanguageDef) (index : ℕ) : ℕ := (ruleAt language index).premises.length

theorem countAt_computable (language : LanguageDef) : CodeComputable (countAt language) :=
  (list_getD 0 (const (language.rewrites.map fun rule => rule.premises.length)) id).of_eq fun index => by
    simp only [countAt, ruleAt, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases language.rewrites[index]? <;> rfl

theorem recAt_computable (language : LanguageDef) :
    CodeComputable fun input : ℕ × ℕ => recursiveOf (premiseAt language input.1 input.2) :=
  (list_getD none (list_getD [] (const (language.rewrites.map fun rule => rule.premises.map recursiveOf)) fst)
    snd).of_eq fun input => by
      simp only [premiseAt, ruleAt, List.getD_eq_getElem?_getD, List.getElem?_map]
      cases language.rewrites[input.1]? with
      | none => rfl
      | some rule =>
          simp only [Option.map_some, Option.getD_some, List.getElem?_map]
          cases rule.premises[input.2]? <;> rfl

theorem directAt_computable (base : BasePremiseEvaluator) (language : LanguageDef)
    (hBase : ∀ premise, CodeComputable fun bindings : Bindings => base language bindings premise) :
    CodeComputable fun input : ℕ × ℕ × Bindings =>
      directOf base language (premiseAt language input.1 input.2.1) input.2.2 := by
  have direct : ∀ premise, CodeComputable (directOf base language premise) := by
    intro premise
    cases premise with
    | congruence => exact (const []).of_eq fun _ => rfl
    | scopedStep => exact (const []).of_eq fun _ => rfl
    | freshness condition => exact hBase _
    | relationQuery relation arguments => exact hBase _
    | forAll collection parameter body => exact hBase _
  have perRule : ∀ rule : RewriteRule, CodeComputable fun input : ℕ × Bindings =>
      directOf base language (rule.premises.getD input.1 noPremise) input.2 := by
    intro rule
    refine (tableOr_computable (direct noPremise) (rule.premises.map (directOf base language))
      (fun f member => ?_)).of_eq fun input => ?_
    · obtain ⟨premise, _, rfl⟩ := List.mem_map.mp member
      exact direct premise
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
      cases rule.premises[input.1]? <;> rfl
  refine (tableOr_computable (perRule noRule) (language.rewrites.map fun rule input =>
    directOf base language (rule.premises.getD input.1 noPremise) input.2) (fun f member => ?_)).of_eq
    fun input => ?_
  · obtain ⟨rule, _, rfl⟩ := List.mem_map.mp member
    exact perRule rule
  · simp only [premiseAt, ruleAt, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases language.rewrites[input.1]? <;> rfl

theorem matchAt_computable (language : LanguageDef) :
    CodeComputable fun input : ℕ × Pattern => matchPatternForRule language (ruleAt language input.1) input.2 := by
  refine (tableOr_computable (matchPatternForRule_computable language noRule)
    (language.rewrites.map fun rule term => matchPatternForRule language rule term) (fun f member => ?_)).of_eq
    fun input => ?_
  · obtain ⟨rule, _, rfl⟩ := List.mem_map.mp member
    exact matchPatternForRule_computable language rule
  · simp only [ruleAt, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases language.rewrites[input.1]? <;> rfl

theorem reductAt_computable (language : LanguageDef) :
    CodeComputable fun input : ℕ × Bindings => applyBindingsForRule language (ruleAt language input.1) input.2 := by
  refine (tableOr_computable (applyBindingsForRule_computable language noRule)
    (language.rewrites.map fun rule bindings => applyBindingsForRule language rule bindings)
    (fun f member => ?_)).of_eq fun input => ?_
  · obtain ⟨rule, _, rfl⟩ := List.mem_map.mp member
    exact applyBindingsForRule_computable language rule
  · simp only [ruleAt, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases language.rewrites[input.1]? <;> rfl

/-! ## One depth as rounds of questions -/

/-- The rule instances that match a term: the position of each rule with the bindings of its left side. -/
def matchesOf (language : LanguageDef) (term : Pattern) : List (ℕ × Bindings) :=
  (List.range language.rewrites.length).flatMap fun index =>
    (matchPatternForRule language (ruleAt language index) term).map fun bindings => (index, bindings)

/-- What a rule instance asks in a round: the source of its premise there, with its bindings applied, when that
premise asks the step itself. Any other premise asks a placeholder whose answer is not used. -/
def questionOf (language : LanguageDef) (round : ℕ) (item : ℕ × Bindings) : Pattern :=
  Option.casesOn (motive := fun _ => Pattern) (recursiveOf (premiseAt language item.1 round)) (.bvar 0)
    fun step => Match.applyBindings item.2 step.1

/-- A rule instance passes its premise of a round, given the answer to its question; an instance whose premises
are all passed stays as it is. -/
def passOf (base : BasePremiseEvaluator) (language : LanguageDef) (round : ℕ) (item : ℕ × Bindings)
    (answer : List Pattern) : List (ℕ × Bindings) :=
  if round < countAt language item.1 then
    (Option.casesOn (motive := fun _ => List Bindings) (recursiveOf (premiseAt language item.1 round))
      (directOf base language (premiseAt language item.1 round) item.2)
      fun step => extendBy item.2 step.2 answer).map fun bindings => (item.1, bindings)
  else [item]

/-- One round: every rule instance passes its premise with the answer to its own question. -/
def advance (base : BasePremiseEvaluator) (language : LanguageDef) (round : ℕ) (items : List (ℕ × Bindings))
    (answers : List (List Pattern)) : List (ℕ × Bindings) :=
  (List.zipWith (passOf base language round) items answers).flatten

/-- The rule instances after the rounds answered so far. -/
def instancesAfter (base : BasePremiseEvaluator) (language : LanguageDef) (term : Pattern)
    (answers : List (List (List Pattern))) : List (ℕ × Bindings) :=
  (answers.foldl (fun progress round => (progress.1 + 1, advance base language progress.1 progress.2 round))
    (0, matchesOf language term)).2

/-- The questions of the next round. -/
def askOf (base : BasePremiseEvaluator) (language : LanguageDef) (term : Pattern)
    (answers : List (List (List Pattern))) : List Pattern :=
  (instancesAfter base language term answers).map (questionOf language answers.length)

/-- The reducts of the rule instances after the last round. -/
def finishOf (base : BasePremiseEvaluator) (language : LanguageDef) (term : Pattern)
    (answers : List (List (List Pattern))) : List Pattern :=
  (instancesAfter base language term answers).map fun item =>
    applyBindingsForRule language (ruleAt language item.1) item.2

/-- The length of the longest premise list of a language. -/
def roundsOf (language : LanguageDef) : ℕ := (language.rewrites.map fun rule => rule.premises.length).foldr max 0

theorem le_foldr_max : ∀ (values : List ℕ) (value : ℕ), value ∈ values → value ≤ values.foldr max 0
  | [], _, member => absurd member List.not_mem_nil
  | first :: rest, value, member => by
      rcases List.mem_cons.mp member with same | later
      · rw [same, List.foldr_cons]; exact le_max_left _ _
      · rw [List.foldr_cons]; exact le_trans (le_foldr_max rest value later) (le_max_right _ _)

theorem countAt_le_roundsOf (language : LanguageDef) (index : ℕ) : countAt language index ≤ roundsOf language := by
  unfold countAt ruleAt roundsOf
  rw [List.getD_eq_getElem?_getD]
  cases found : language.rewrites[index]? with
  | none => exact Nat.zero_le _
  | some rule =>
      exact le_foldr_max _ _ (List.mem_map.mpr ⟨rule, List.mem_of_getElem? found, rfl⟩)

theorem foldl_counts {σ τ : Type} (f : ℕ → σ → τ → σ) : ∀ (items : List τ) (start : ℕ) (state : σ),
    (items.foldl (fun progress item => (progress.1 + 1, f progress.1 progress.2 item)) (start, state)).1 =
      start + items.length
  | [], start, state => by simp
  | item :: items, start, state => by
      have later := foldl_counts f items (start + 1) (f start state item)
      simp only [List.foldl_cons, List.length_cons]
      rw [later]
      omega

theorem instancesAfter_append (base : BasePremiseEvaluator) (language : LanguageDef) (term : Pattern)
    (answers : List (List (List Pattern))) (round : List (List Pattern)) :
    instancesAfter base language term (answers ++ [round]) =
      advance base language answers.length (instancesAfter base language term answers) round := by
  unfold instancesAfter
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  dsimp only
  rw [foldl_counts (advance base language), Nat.zero_add]

theorem conversation_eq {α β : Type} (ask : ℕ → α → List (List β) → List α)
    (finish : ℕ → α → List (List β) → β) (value : α → β) (k : ℕ) (argument : α) :
    ∀ (r : ℕ) (answers : List (List β)), conversation ask finish value k argument r answers =
      finish k argument ((fun answers => answers ++ [(ask k argument answers).map value])^[r] answers)
  | 0, _ => rfl
  | r + 1, answers => by
      rw [Function.iterate_succ_apply, ← conversation_eq ask finish value k argument r]
      rfl

theorem iterate_length {β : Type} (grow : List β → List β) (grows : ∀ answers, (grow answers).length =
    answers.length + 1) : ∀ (r : ℕ) (answers : List β), (grow^[r] answers).length = answers.length + r
  | 0, _ => rfl
  | r + 1, answers => by
      rw [Function.iterate_succ_apply, iterate_length grow grows r, grows]
      omega

/-- A rule instance, asked its question, passes its premise of the round as the premise list does. -/
theorem passOf_question (base : BasePremiseEvaluator) (language : LanguageDef) (recursive : Pattern → List Pattern)
    (round : ℕ) (item : ℕ × Bindings) :
    passOf base language round item (recursive (questionOf language round item)) =
      (premisesUsing base language recursive ((ruleAt language item.1).premises[round]?.toList) item.2).map
        fun bindings => (item.1, bindings) := by
  unfold passOf countAt
  by_cases within : round < (ruleAt language item.1).premises.length
  · rw [if_pos within, List.getElem?_eq_getElem within, Option.toList_some, premisesUsing_single,
      premiseStepUsing_eq]
    have same : premiseAt language item.1 round = (ruleAt language item.1).premises[round] := by
      unfold premiseAt
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem within, Option.getD_some]
    unfold questionOf
    rw [same]
    cases recursiveOf (ruleAt language item.1).premises[round] <;> rfl
  · rw [if_neg within, List.getElem?_eq_none (Nat.le_of_not_lt within), Option.toList_none]
    simp [premisesUsing]

/-- **After `r` rounds, the rule instances are the derivations of the first `r` premises of each rule.** -/
theorem instancesAfter_rounds (base : BasePremiseEvaluator) (language : LanguageDef) (k : ℕ) (term : Pattern) :
    ∀ r : ℕ, instancesAfter base language term
        ((fun answers => answers ++ [(askOf base language term answers).map (rewriteAt base language k)])^[r] []) =
      (matchesOf language term).flatMap fun item =>
        (premisesUsing base language (rewriteAt base language k) ((ruleAt language item.1).premises.take r)
          item.2).map fun bindings => (item.1, bindings)
  | 0 => by simp [instancesAfter, premisesUsing]
  | r + 1 => by
      have counted := iterate_length (fun answers => answers ++
        [(askOf base language term answers).map (rewriteAt base language k)]) (fun _ => by simp) r []
      rw [List.length_nil, Nat.zero_add] at counted
      rw [Function.iterate_succ_apply', instancesAfter_append, counted, askOf, counted,
        instancesAfter_rounds base language k term r]
      unfold advance
      rw [List.map_map, List.zipWith_map_right, List.zipWith_self, ← List.flatMap_def, List.flatMap_assoc]
      congr 1
      funext item
      rw [List.take_add_one, premisesUsing_append, List.map_flatMap, List.flatMap_map]
      congr 1
      funext bindings
      exact passOf_question base language (rewriteAt base language k) r (item.1, bindings)

/-- **One more depth is a dialogue with the depth before**: as many rounds as the longest premise list. -/
theorem rewriteAt_succ_eq (base : BasePremiseEvaluator) (language : LanguageDef) (k : ℕ) (term : Pattern) :
    rewriteAt base language (k + 1) term =
      conversation (fun _ term answers => askOf base language term answers)
        (fun _ term answers => finishOf base language term answers) (rewriteAt base language k) k term
        (roundsOf language) [] := by
  rw [conversation_eq]
  unfold finishOf
  rw [instancesAfter_rounds base language k term (roundsOf language)]
  unfold matchesOf
  rw [rewriteAt, ← map_getD_range language.rewrites noRule, List.flatMap_map, List.length_map,
    List.length_range, List.flatMap_assoc, List.map_flatMap]
  congr 1
  funext index
  show applyRuleUsing base language (rewriteAt base language k) (ruleAt language index) term = _
  unfold applyRuleUsing
  rw [List.flatMap_map, List.map_flatMap]
  congr 1
  funext bindings
  dsimp only
  rw [List.take_of_length_le (countAt_le_roundsOf language index), List.map_map]
  rfl

/-! ## Computability -/

theorem matchesOf_computable (language : LanguageDef) : CodeComputable (matchesOf language) := by
  have image : CodeComputable₂ fun (term : Pattern) (index : ℕ) =>
      (matchPatternForRule language (ruleAt language index) term).map fun bindings => (index, bindings) :=
    list_map ((matchAt_computable language).comp (pair snd fst)) (pair (snd.comp fst) snd)
  exact (list_flatMap (list_range (const language.rewrites.length)) image).of_eq fun _ => rfl

theorem questionOf_computable (language : LanguageDef) :
    CodeComputable fun input : ℕ × (ℕ × Bindings) => questionOf language input.1 input.2 := by
  have recursive : CodeComputable fun input : ℕ × (ℕ × Bindings) =>
      recursiveOf (premiseAt language input.2.1 input.1) :=
    (recAt_computable language).comp (pair (fst.comp snd) fst)
  have source : CodeComputable₂ fun (input : ℕ × (ℕ × Bindings)) (step : Pattern × Pattern) =>
      Match.applyBindings input.2.2 step.1 :=
    applyBindings_computable.comp (pair (snd.comp (snd.comp fst)) (fst.comp snd))
  exact (option_casesOn recursive (const (Pattern.bvar 0)) source).of_eq fun _ => rfl

theorem extendBy_computable :
    CodeComputable fun input : (Bindings × Pattern) × List Pattern => extendBy input.1.1 input.1.2 input.2 := by
  have matched : CodeComputable₂ fun (input : (Bindings × Pattern) × List Pattern) (candidate : Pattern) =>
      matchPattern input.1.2 candidate :=
    matchPattern_computable.comp (pair (snd.comp (fst.comp fst)) snd)
  have merged : CodeComputable₂ fun (y : ((Bindings × Pattern) × List Pattern) × Pattern) (found : Bindings) =>
      mergeBindings y.1.1.1 found :=
    mergeBindings_computable.comp (pair (fst.comp (fst.comp (fst.comp fst))) snd)
  exact (list_flatMap snd (list_filterMap matched merged)).of_eq fun _ => rfl

theorem passOf_computable (base : BasePremiseEvaluator) (language : LanguageDef)
    (hBase : ∀ premise, CodeComputable fun bindings : Bindings => base language bindings premise) :
    CodeComputable fun input : ℕ × (ℕ × Bindings) × List Pattern =>
      passOf base language input.1 input.2.1 input.2.2 := by
  have recursive : CodeComputable fun input : ℕ × (ℕ × Bindings) × List Pattern =>
      recursiveOf (premiseAt language input.2.1.1 input.1) :=
    (recAt_computable language).comp (pair (fst.comp (fst.comp snd)) fst)
  have direct : CodeComputable fun input : ℕ × (ℕ × Bindings) × List Pattern =>
      directOf base language (premiseAt language input.2.1.1 input.1) input.2.1.2 :=
    (directAt_computable base language hBase).comp (pair (fst.comp (fst.comp snd)) (pair fst (snd.comp (fst.comp snd))))
  have extended : CodeComputable₂ fun (input : ℕ × (ℕ × Bindings) × List Pattern) (step : Pattern × Pattern) =>
      extendBy input.2.1.2 step.2 input.2.2 :=
    extendBy_computable.comp (pair (pair (snd.comp (fst.comp (snd.comp fst))) (snd.comp snd)) (snd.comp (snd.comp fst)))
  have passed : CodeComputable fun input : ℕ × (ℕ × Bindings) × List Pattern =>
      (Option.casesOn (motive := fun _ => List Bindings) (recursiveOf (premiseAt language input.2.1.1 input.1))
        (directOf base language (premiseAt language input.2.1.1 input.1) input.2.1.2)
        fun step => extendBy input.2.1.2 step.2 input.2.2).map fun bindings => (input.2.1.1, bindings) :=
    list_map (option_casesOn recursive direct extended) (pair (fst.comp (fst.comp (snd.comp fst))) snd)
  refine (CodeComputable.ite (nat_lt fst ((countAt_computable language).comp (fst.comp (fst.comp snd)))) passed
    (list_cons (fst.comp snd) (const []))).of_eq fun input => ?_
  unfold passOf
  by_cases within : input.1 < countAt language input.2.1.1 <;> simp [within]

theorem advance_computable (base : BasePremiseEvaluator) (language : LanguageDef)
    (hBase : ∀ premise, CodeComputable fun bindings : Bindings => base language bindings premise) :
    CodeComputable fun input : ℕ × List (ℕ × Bindings) × List (List Pattern) =>
      advance base language input.1 input.2.1 input.2.2 := by
  have passed : CodeComputable fun y : (ℕ × List (ℕ × Bindings) × List (List Pattern)) × (ℕ × Bindings) ×
      List Pattern => passOf base language y.1.1 y.2.1 y.2.2 :=
    (passOf_computable base language hBase).comp (pair (fst.comp fst) snd)
  exact (list_flatten (list_zipWith (0, []) [] (fst.comp snd) (snd.comp snd) passed)).of_eq fun _ => rfl

theorem instancesAfter_computable (base : BasePremiseEvaluator) (language : LanguageDef)
    (hBase : ∀ premise, CodeComputable fun bindings : Bindings => base language bindings premise) :
    CodeComputable fun input : Pattern × List (List (List Pattern)) =>
      instancesAfter base language input.1 input.2 := by
  have stepped : CodeComputable fun y : (Pattern × List (List (List Pattern))) × (ℕ × List (ℕ × Bindings)) ×
      List (List Pattern) => (y.2.1.1 + 1, advance base language y.2.1.1 y.2.1.2 y.2.2) :=
    pair (nat_add (fst.comp (fst.comp snd)) (const 1))
      ((advance_computable base language hBase).comp (pair (fst.comp (fst.comp snd))
        (pair (snd.comp (fst.comp snd)) (snd.comp snd))))
  exact (snd.comp (list_foldl snd (pair (const 0) ((matchesOf_computable language).comp fst)) stepped)).of_eq
    fun _ => rfl

theorem askOf_computable (base : BasePremiseEvaluator) (language : LanguageDef)
    (hBase : ∀ premise, CodeComputable fun bindings : Bindings => base language bindings premise) :
    CodeComputable fun input : Pattern × List (List (List Pattern)) => askOf base language input.1 input.2 :=
  (list_map (instancesAfter_computable base language hBase)
    ((questionOf_computable language).comp (pair (list_length (snd.comp fst)) snd))).of_eq fun _ => rfl

theorem finishOf_computable (base : BasePremiseEvaluator) (language : LanguageDef)
    (hBase : ∀ premise, CodeComputable fun bindings : Bindings => base language bindings premise) :
    CodeComputable fun input : Pattern × List (List (List Pattern)) => finishOf base language input.1 input.2 :=
  (list_map (instancesAfter_computable base language hBase) ((reductAt_computable language).comp snd)).of_eq
    fun _ => rfl

/-- **The rule engine is computable on codes** in the depth and the term, when its base premises are. -/
theorem rewriteAt_computable (base : BasePremiseEvaluator) (language : LanguageDef)
    (hBase : ∀ premise, CodeComputable fun bindings : Bindings => base language bindings premise) :
    CodeComputable₂ (rewriteAt base language) :=
  rounds (base := fun _ => []) (count := fun _ _ => roundsOf language)
    (ask := fun _ term answers => askOf base language term answers)
    (finish := fun _ term answers => finishOf base language term answers)
    (fun _ => rfl) (rewriteAt_succ_eq base language) (const []) (const _)
    ((askOf_computable base language hBase).comp snd) ((finishOf_computable base language hBase).comp snd)

/-- **The executable rule engine with a relation environment computable on codes is computable on codes.** -/
theorem reductsUsing_computable (relEnv : RelationEnv) (relations : CodeComputable₂ relEnv.tuples)
    (language : LanguageDef) : CodeComputable₂ (reductsUsing relEnv language) :=
  rewriteAt_computable (engineBasePremises relEnv) language (basePremise_computable relEnv relations language)

end Mettapedia.OSLF.MeTTaIL.EngineCoded

#print axioms Mettapedia.OSLF.MeTTaIL.EngineCoded.reductsUsing_computable
