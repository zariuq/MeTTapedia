import Mettapedia.OSLF.MeTTaIL.EngineCoded.ReferencePremises
import Mettapedia.OSLF.MeTTaIL.EngineCoded.Rewriting
import Mettapedia.Computability.CodedRelations

/-!
# The reference relation computed on codes

`stepsAt fuel source` lists the reference steps of a term with their witnesses, every derivation at
most `fuel` rule layers deep. One more layer is a dialogue with the layer below: in round `r` every
rule instance still running asks what the `r`-th premise of its rule asks the step (`questionsOf`),
all the questions of the round are answered together, and every instance reads its answers from the
round's table (`advanceItems`). After as many rounds as the longest premise list, the instances are
the complete premise derivations (`itemsAfter_rounds`, `stepsAt_succ_eq`).

So the reference executor is computable on codes when the relation environment is
(`stepsAt_computable`), and **the reference relation of every language is recursively enumerable on
codes** when its relation environment is computable on codes (`referenceStep_enumerable`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.EngineCoded

open Mettapedia.Computability
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical (matchPatternForRule)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.OSLF.MeTTaIL.PatternCode
open CodeComputable

/-! ## Questions of a fixed premise -/

theorem questionsOf_computable (sites : Pattern) :
    ∀ premise : Premise, CodeComputable fun bindings : Bindings => questionsOf sites bindings premise
  | .freshness _ => (const []).of_eq fun _ => rfl
  | .relationQuery _ _ => (const []).of_eq fun _ => rfl
  | .congruence source target =>
      (list_cons (applyBindingsScoped_computable.comp (pair (pair (const sites) (pair id (const _))) (const source)))
        (const [])).of_eq fun _ => rfl
  | .scopedStep step =>
      (list_cons (applyBindingsScoped_computable.comp (pair (pair (const sites) (pair id (const _)))
        (const step.source))) (const [])).of_eq fun _ => rfl
  | .forAll collection parameter body => by
      have inner := questionsOf_computable sites body
      have each : CodeComputable₂ fun (bindings : Bindings) (elements : List Pattern) =>
          elements.flatMap fun element => questionsOf sites (bindParameter bindings parameter element) body :=
        list_flatMap snd (inner.comp ((bindParameter_computable parameter).comp (pair (fst.comp fst) snd)))
      refine (option_casesOn (collectionElements_computable.comp (lookup_computable.comp (pair id (const collection))))
        (const []) each).of_eq fun bindings => ?_
      simp only [questionsOf]
      cases collectionElements (bindings.lookup collection) <;> rfl

/-! ## Rules and premises by position -/

variable (relEnv : RelationEnv) (language : LanguageDef)

/-- Where the rule at a position binds its metavariables. -/
def sitesAt (index : ℕ) : Pattern := captureSites (ruleAt language index)

theorem questionsAt_computable :
    CodeComputable fun input : ℕ × ℕ × Bindings =>
      questionsOf (sitesAt language input.1) input.2.2 (premiseAt language input.1 input.2.1) := by
  have perRule : ∀ rule : RewriteRule, CodeComputable fun input : ℕ × Bindings =>
      questionsOf (captureSites rule) input.2 (rule.premises.getD input.1 noPremise) := by
    intro rule
    refine (tableOr_computable (questionsOf_computable (captureSites rule) noPremise)
      (rule.premises.map fun premise bindings => questionsOf (captureSites rule) bindings premise)
      (fun f member => ?_)).of_eq fun input => ?_
    · obtain ⟨premise, _, rfl⟩ := List.mem_map.mp member
      exact questionsOf_computable (captureSites rule) premise
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
      cases rule.premises[input.1]? <;> rfl
  refine (tableOr_computable (perRule noRule) (language.rewrites.map fun rule (input : ℕ × Bindings) =>
    questionsOf (captureSites rule) input.2 (rule.premises.getD input.1 noPremise)) (fun f member => ?_)).of_eq
    fun input => ?_
  · obtain ⟨rule, _, rfl⟩ := List.mem_map.mp member
    exact perRule rule
  · simp only [sitesAt, premiseAt, ruleAt, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases language.rewrites[input.1]? <;> rfl

theorem premiseTableAt_computable (relations : CodeComputable₂ relEnv.tuples) :
    CodeComputable fun input : ℕ × ℕ × Table × Bindings =>
      premiseAtUsing relEnv language (lookupTable input.2.2.1) (sitesAt language input.1) input.2.2.2
        (premiseAt language input.1 input.2.1) := by
  have perRule : ∀ rule : RewriteRule, CodeComputable fun input : ℕ × Table × Bindings =>
      premiseAtUsing relEnv language (lookupTable input.2.1) (captureSites rule) input.2.2
        (rule.premises.getD input.1 noPremise) := by
    intro rule
    refine (tableOr_computable (premiseAtTable_computable relEnv language relations (captureSites rule) noPremise)
      (rule.premises.map fun premise (input : Table × Bindings) =>
        premiseAtUsing relEnv language (lookupTable input.1) (captureSites rule) input.2 premise)
      (fun f member => ?_)).of_eq fun input => ?_
    · obtain ⟨premise, _, rfl⟩ := List.mem_map.mp member
      exact premiseAtTable_computable relEnv language relations (captureSites rule) premise
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
      cases rule.premises[input.1]? <;> rfl
  refine (tableOr_computable (perRule noRule) (language.rewrites.map fun rule (input : ℕ × Table × Bindings) =>
    premiseAtUsing relEnv language (lookupTable input.2.1) (captureSites rule) input.2.2
      (rule.premises.getD input.1 noPremise)) (fun f member => ?_)).of_eq fun input => ?_
  · obtain ⟨rule, _, rfl⟩ := List.mem_map.mp member
    exact perRule rule
  · simp only [sitesAt, premiseAt, ruleAt, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases language.rewrites[input.1]? <;> rfl

theorem rightAt_computable :
    CodeComputable fun input : ℕ × Bindings =>
      applyBindingsScoped (sitesAt language input.1) input.2 0 (ruleAt language input.1).right := by
  have perRule : ∀ rule : RewriteRule, CodeComputable fun bindings : Bindings =>
      applyBindingsScoped (captureSites rule) bindings 0 rule.right := fun rule =>
    applyBindingsScoped_computable.comp (pair (pair (const _) (pair id (const 0))) (const _))
  refine (tableOr_computable (perRule noRule) (language.rewrites.map fun rule bindings =>
    applyBindingsScoped (captureSites rule) bindings 0 rule.right) (fun f member => ?_)).of_eq fun input => ?_
  · obtain ⟨rule, _, rfl⟩ := List.mem_map.mp member
    exact perRule rule
  · simp only [sitesAt, ruleAt, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases language.rewrites[input.1]? <;> rfl

/-! ## One layer as rounds of questions -/

/-- A rule instance under way: the rule's position, the bindings from matching its left side, the
bindings so far, and the witnesses of its premises so far. -/
abbrev Item := ℕ × Bindings × Bindings × List Witness

/-- The rule instances that match a term. -/
def startOf (source : Pattern) : List Item :=
  (List.range language.rewrites.length).flatMap fun index =>
    (matchPatternForRule language (ruleAt language index) source).map fun initial => (index, initial, initial, [])

/-- What the instances ask in a round. -/
def roundQuestions (round : ℕ) (items : List Item) : List Pattern :=
  items.flatMap fun item => questionsOf (sitesAt language item.1) item.2.2.1 (premiseAt language item.1 round)

/-- An instance passes its premise of a round, reading its answers from the round's table. -/
def passItem (round : ℕ) (table : Table) (item : Item) : List Item :=
  if round < countAt language item.1 then
    (premiseAtUsing relEnv language (lookupTable table) (sitesAt language item.1) item.2.2.1
      (premiseAt language item.1 round)).map fun entry => (item.1, item.2.1, entry.2, item.2.2.2 ++ [entry.1])
  else [item]

/-- One round: the questions of every instance are answered together, and every instance passes its
premise against the round's table. -/
def advanceItems (round : ℕ) (items : List Item) (answers : List (List (Witness × Pattern))) : List Item :=
  items.flatMap (passItem relEnv language round ((roundQuestions language round items).zip answers))

/-- The rule instances after the rounds answered so far. -/
def itemsAfter (source : Pattern) (answers : List (List (List (Witness × Pattern)))) : List Item :=
  (answers.foldl (fun progress round => (progress.1 + 1, advanceItems relEnv language progress.1 progress.2 round))
    (0, startOf language source)).2

/-- The questions of the next round. -/
def askItems (source : Pattern) (answers : List (List (List (Witness × Pattern)))) : List Pattern :=
  roundQuestions language answers.length (itemsAfter relEnv language source answers)

/-- The steps of the rule instances after the last round. -/
def finishItems (source : Pattern) (answers : List (List (List (Witness × Pattern)))) : List (Witness × Pattern) :=
  (itemsAfter relEnv language source answers).map fun item =>
    (.rule item.1 item.2.1 item.2.2.2, applyBindingsScoped (sitesAt language item.1) item.2.2.1 0
      (ruleAt language item.1).right)

theorem itemsAfter_append (source : Pattern) (answers : List (List (List (Witness × Pattern))))
    (round : List (List (Witness × Pattern))) :
    itemsAfter relEnv language source (answers ++ [round]) =
      advanceItems relEnv language answers.length (itemsAfter relEnv language source answers) round := by
  unfold itemsAfter
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  dsimp only
  rw [foldl_counts (advanceItems relEnv language), Nat.zero_add]

theorem premisesAtUsing_append (recursive : Pattern → List (Witness × Pattern)) (sites : Pattern) :
    ∀ (first second : List Premise) (bindings : Bindings),
      premisesAtUsing relEnv language recursive sites bindings (first ++ second) =
        (premisesAtUsing relEnv language recursive sites bindings first).flatMap fun entry =>
          (premisesAtUsing relEnv language recursive sites entry.2 second).map fun rest => (entry.1 ++ rest.1, rest.2)
  | [], second, bindings => by simp [premisesAtUsing]
  | premise :: first, second, bindings => by
      simp only [List.cons_append, premisesAtUsing, List.flatMap_assoc, List.flatMap_map]
      congr 1
      funext entry
      rw [premisesAtUsing_append recursive sites first second entry.2, List.map_flatMap]
      congr 1
      funext middle
      simp [Function.comp_def]

theorem flatMap_singleton_eq_map {α β : Type} (f : α → β) :
    ∀ items : List α, (items.flatMap fun item => [f item]) = items.map f
  | [] => rfl
  | item :: items => by rw [List.flatMap_cons, List.map_cons, flatMap_singleton_eq_map f items]; rfl

theorem premisesAtUsing_single (recursive : Pattern → List (Witness × Pattern)) (sites : Pattern)
    (bindings : Bindings) (premise : Premise) :
    premisesAtUsing relEnv language recursive sites bindings [premise] =
      (premiseAtUsing relEnv language recursive sites bindings premise).map fun entry => ([entry.1], entry.2) := by
  simp only [premisesAtUsing, List.map_cons, List.map_nil]
  exact flatMap_singleton_eq_map _ _

/-- An instance passes its premise with the stepper itself, as the premise list does. -/
theorem passItem_eq (k : ℕ) (round : ℕ) (item : Item) :
    (if round < countAt language item.1 then
      (premiseAtUsing relEnv language (stepsAt relEnv language k) (sitesAt language item.1) item.2.2.1
        (premiseAt language item.1 round)).map fun entry => (item.1, item.2.1, entry.2, item.2.2.2 ++ [entry.1])
    else [item]) =
      (premisesAtUsing relEnv language (stepsAt relEnv language k) (sitesAt language item.1) item.2.2.1
        ((ruleAt language item.1).premises[round]?.toList)).map fun rest =>
          (item.1, item.2.1, rest.2, item.2.2.2 ++ rest.1) := by
  unfold countAt
  by_cases within : round < (ruleAt language item.1).premises.length
  · rw [if_pos within, List.getElem?_eq_getElem within, Option.toList_some]
    have same : premiseAt language item.1 round = (ruleAt language item.1).premises[round] := by
      unfold premiseAt
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem within, Option.getD_some]
    rw [same, premisesAtUsing_single, List.map_map]
    rfl
  · rw [if_neg within, List.getElem?_eq_none (Nat.le_of_not_lt within), Option.toList_none]
    simp [premisesAtUsing]

/-- An instance reading its answers from a table that agrees with the stepper on its questions passes its
premise as the premise list does. -/
theorem passItem_table (k r : ℕ) (table : Table) (item : Item)
    (agree : ∀ question ∈ questionsOf (sitesAt language item.1) item.2.2.1 (premiseAt language item.1 r),
      lookupTable table question = stepsAt relEnv language k question) :
    passItem relEnv language r table item =
      (premisesAtUsing relEnv language (stepsAt relEnv language k) (sitesAt language item.1) item.2.2.1
        ((ruleAt language item.1).premises[r]?.toList)).map fun rest =>
          (item.1, item.2.1, rest.2, item.2.2.2 ++ rest.1) := by
  unfold passItem
  rw [premiseAtUsing_congr relEnv language _ _ _ agree]
  exact passItem_eq relEnv language k r item

/-- **After `r` rounds, the instances are the derivations of the first `r` premises of each rule.** -/
theorem itemsAfter_rounds (k : ℕ) (source : Pattern) :
    ∀ r : ℕ, itemsAfter relEnv language source
        ((fun answers => answers ++ [(askItems relEnv language source answers).map (stepsAt relEnv language k)])^[r]
          []) =
      (startOf language source).flatMap fun item =>
        (premisesAtUsing relEnv language (stepsAt relEnv language k) (sitesAt language item.1) item.2.2.1
          ((ruleAt language item.1).premises.take r)).map fun entry => (item.1, item.2.1, entry.2, item.2.2.2 ++ entry.1)
  | 0 => by simp [itemsAfter, premisesAtUsing]
  | r + 1 => by
      have counted := iterate_length (fun answers => answers ++
        [(askItems relEnv language source answers).map (stepsAt relEnv language k)]) (fun _ => by simp) r []
      rw [List.length_nil, Nat.zero_add] at counted
      rw [Function.iterate_succ_apply', itemsAfter_append, counted, askItems, counted,
        itemsAfter_rounds k source r]
      unfold advanceItems
      rw [List.flatMap_assoc]
      refine List.flatMap_congr fun item started => ?_
      rw [List.flatMap_map, List.take_add_one, premisesAtUsing_append, List.map_flatMap]
      refine List.flatMap_congr fun entry derived => ?_
      have asked : ∀ question ∈ questionsOf (sitesAt language item.1) entry.2 (premiseAt language item.1 r),
          lookupTable ((roundQuestions language r ((startOf language source).flatMap fun item =>
            (premisesAtUsing relEnv language (stepsAt relEnv language k) (sitesAt language item.1) item.2.2.1
              ((ruleAt language item.1).premises.take r)).map fun entry =>
                (item.1, item.2.1, entry.2, item.2.2.2 ++ entry.1))).zip
            ((roundQuestions language r ((startOf language source).flatMap fun item =>
              (premisesAtUsing relEnv language (stepsAt relEnv language k) (sitesAt language item.1) item.2.2.1
                ((ruleAt language item.1).premises.take r)).map fun entry =>
                  (item.1, item.2.1, entry.2, item.2.2.2 ++ entry.1))).map (stepsAt relEnv language k)))
            question = stepsAt relEnv language k question := by
        intro question member
        refine lookupTable_zip _ _ ?_
        unfold roundQuestions
        refine List.mem_flatMap.mpr ⟨(item.1, item.2.1, entry.2, item.2.2.2 ++ entry.1),
          List.mem_flatMap.mpr ⟨item, started, List.mem_map.mpr ⟨entry, derived, rfl⟩⟩, member⟩
      rw [passItem_table relEnv language k r _ (item.1, item.2.1, entry.2, item.2.2.2 ++ entry.1) asked,
        List.map_map]
      congr 1
      funext rest
      simp [List.append_assoc]

/-- **One more layer is a dialogue with the layer below**: as many rounds as the longest premise list. -/
theorem stepsAt_succ_eq (k : ℕ) (source : Pattern) :
    stepsAt relEnv language (k + 1) source =
      conversation (fun _ source answers => askItems relEnv language source answers)
        (fun _ source answers => finishItems relEnv language source answers) (stepsAt relEnv language k) k source
        (roundsOf language) [] := by
  rw [conversation_eq]
  unfold finishItems
  rw [itemsAfter_rounds relEnv language k source (roundsOf language)]
  unfold startOf
  rw [stepsAt, List.flatMap_assoc, List.map_flatMap]
  refine List.flatMap_congr fun index inRange => ?_
  have within : index < language.rewrites.length := List.mem_range.mp inRange
  have found : language.rewrites[index]? = some (ruleAt language index) := by
    rw [List.getElem?_eq_getElem within]
    unfold ruleAt
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem within, Option.getD_some]
  rw [found]
  dsimp only
  rw [List.flatMap_map, List.map_flatMap]
  congr 1
  funext initial
  rw [List.take_of_length_le (countAt_le_roundsOf language index), List.map_map]
  rfl

/-! ## Computability -/

theorem startOf_computable : CodeComputable (startOf language) := by
  have image : CodeComputable₂ fun (source : Pattern) (index : ℕ) =>
      (matchPatternForRule language (ruleAt language index) source).map fun initial =>
        ((index, initial, initial, []) : Item) :=
    list_map ((matchAt_computable language).comp (pair snd fst))
      (pair (snd.comp fst) (pair snd (pair snd (const []))))
  exact (list_flatMap (list_range (const language.rewrites.length)) image).of_eq fun _ => rfl

theorem roundQuestions_computable :
    CodeComputable fun input : ℕ × List Item => roundQuestions language input.1 input.2 :=
  (list_flatMap snd ((questionsAt_computable language).comp (pair (fst.comp snd)
    (pair (fst.comp fst) (fst.comp (snd.comp (snd.comp snd))))))).of_eq fun _ => rfl

theorem passItem_computable (relations : CodeComputable₂ relEnv.tuples) :
    CodeComputable fun input : ℕ × Table × Item => passItem relEnv language input.1 input.2.1 input.2.2 := by
  have evaluated : CodeComputable fun input : ℕ × Table × Item =>
      premiseAtUsing relEnv language (lookupTable input.2.1) (sitesAt language input.2.2.1) input.2.2.2.2.1
        (premiseAt language input.2.2.1 input.1) :=
    (premiseTableAt_computable relEnv language relations).comp (pair (fst.comp (snd.comp snd))
      (pair fst (pair (fst.comp snd) (fst.comp (snd.comp (snd.comp (snd.comp snd)))))))
  have extended : CodeComputable₂ fun (input : ℕ × Table × Item) (entry : Witness × Bindings) =>
      ((input.2.2.1, input.2.2.2.1, entry.2, input.2.2.2.2.2 ++ [entry.1]) : Item) :=
    pair (fst.comp (snd.comp (snd.comp fst))) (pair (fst.comp (snd.comp (snd.comp (snd.comp fst))))
      (pair (snd.comp snd) (list_append (snd.comp (snd.comp (snd.comp (snd.comp (snd.comp fst)))))
        (list_cons (fst.comp snd) (const [])))))
  refine (CodeComputable.ite (nat_lt fst ((countAt_computable language).comp (fst.comp (snd.comp snd))))
    (list_map evaluated extended) (list_cons (snd.comp snd) (const []))).of_eq fun input => ?_
  unfold passItem
  by_cases within : input.1 < countAt language input.2.2.1 <;> simp [within]

theorem advanceItems_computable (relations : CodeComputable₂ relEnv.tuples) :
    CodeComputable fun input : ℕ × List Item × List (List (Witness × Pattern)) =>
      advanceItems relEnv language input.1 input.2.1 input.2.2 := by
  have table : CodeComputable fun input : ℕ × List Item × List (List (Witness × Pattern)) =>
      (roundQuestions language input.1 input.2.1).zip input.2.2 :=
    (list_zipWith (combine := fun _ (question : Pattern) (answer : List (Witness × Pattern)) => (question, answer))
      (Pattern.bvar 0) [] ((roundQuestions_computable language).comp (pair fst (fst.comp snd))) (snd.comp snd)
      (pair (fst.comp snd) (snd.comp snd))).of_eq fun _ => rfl
  exact (list_flatMap (fst.comp snd) ((passItem_computable relEnv language relations).comp
    (pair (fst.comp fst) (pair (table.comp fst) snd)))).of_eq fun _ => rfl

theorem itemsAfter_computable (relations : CodeComputable₂ relEnv.tuples) :
    CodeComputable fun input : Pattern × List (List (List (Witness × Pattern))) =>
      itemsAfter relEnv language input.1 input.2 := by
  have stepped : CodeComputable fun y : (Pattern × List (List (List (Witness × Pattern)))) × (ℕ × List Item) ×
      List (List (Witness × Pattern)) => (y.2.1.1 + 1, advanceItems relEnv language y.2.1.1 y.2.1.2 y.2.2) :=
    pair (nat_add (fst.comp (fst.comp snd)) (const 1))
      ((advanceItems_computable relEnv language relations).comp (pair (fst.comp (fst.comp snd))
        (pair (snd.comp (fst.comp snd)) (snd.comp snd))))
  exact (snd.comp (list_foldl snd (pair (const 0) ((startOf_computable language).comp fst)) stepped)).of_eq
    fun _ => rfl

theorem finishImage_computable :
    CodeComputable₂ fun (_ : ℕ × Pattern × List (List (List (Witness × Pattern)))) (item : Item) =>
      ((Witness.rule item.1 item.2.1 item.2.2.2 : Witness),
        applyBindingsScoped (sitesAt language item.1) item.2.2.1 0 (ruleAt language item.1).right) :=
  pair (rule_computable.comp (pair (fst.comp snd) (pair (fst.comp (snd.comp snd))
    (snd.comp (snd.comp (snd.comp snd))))))
    ((rightAt_computable language).comp (pair (fst.comp snd) (fst.comp (snd.comp (snd.comp snd)))))

/-- **The reference executor is computable on codes** in the depth and the term, when the relation
environment is. -/
theorem stepsAt_computable (relations : CodeComputable₂ relEnv.tuples) :
    CodeComputable₂ (stepsAt relEnv language) :=
  rounds (base := fun _ => []) (count := fun _ _ => roundsOf language)
    (ask := fun _ source answers => askItems relEnv language source answers)
    (finish := fun _ source answers => finishItems relEnv language source answers)
    (fun _ => rfl) (stepsAt_succ_eq relEnv language) (const []) (const _)
    ((roundQuestions_computable language).comp (pair (list_length (snd.comp snd))
      ((itemsAfter_computable relEnv language relations).comp snd)))
    ((list_map ((itemsAfter_computable relEnv language relations).comp snd) (finishImage_computable language)).of_eq
      fun _ => rfl)

/-- **The reference relation is recursively enumerable on codes** when its relation environment is
computable on codes. -/
theorem referenceStep_enumerable (relations : CodeComputable₂ relEnv.tuples) :
    EnumerableOnCodes (ReferenceStep.Step relEnv language) :=
  enumerableOnCodes_of_bounded patternCode_injective'
    (listing := fun fuel source => (stepsAt relEnv language fuel source).map Prod.snd)
    (list_map (stepsAt_computable relEnv language relations) (snd.comp snd)) fun source target => by
      rw [step_iff_exists_mem_stepsAt]
      simp only [List.mem_map, Prod.exists, exists_eq_right]

end Mettapedia.OSLF.MeTTaIL.EngineCoded

#print axioms Mettapedia.OSLF.MeTTaIL.EngineCoded.referenceStep_enumerable
