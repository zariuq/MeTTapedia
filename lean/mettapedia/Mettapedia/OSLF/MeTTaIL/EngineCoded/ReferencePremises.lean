import Mettapedia.OSLF.MeTTaIL.EngineCoded.Premises
import Mettapedia.OSLF.MeTTaIL.ReferenceStepExecution

/-!
# Premises of the reference relation computed on codes

Witnesses are coded (`Coded Witness`). A premise of the reference relation asks the step itself
about finitely many terms, all determined by the bindings it extends (`questionsOf`): a step premise
asks about its instantiated source, and a quantified premise asks what its body asks at each element of
the collection. A premise evaluated against any stepper that agrees with another on these questions
gives the same result (`premiseAtUsing_congr`).

A table of answers is read as a stepper (`lookupTable`). For a fixed premise, evaluating it against a
table is computable on codes in the table and the bindings (`premiseAtTable_computable`), when the
relation environment is computable on codes.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.EngineCoded

open Mettapedia.Computability
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.OSLF.MeTTaIL.PatternCode
open Mettapedia.OSLF.MeTTaIL.PatternCode.CodeComputable'
open CodeComputable

/-! ## Coding witnesses -/

mutual
/-- The code of a witness. -/
def witnessCode : Witness → ℕ
  | .base result => Nat.pair 0 (code result)
  | .premiseStep step candidate matched result =>
      Nat.pair 1 (Nat.pair (witnessCode step) (Nat.pair (code candidate) (Nat.pair (code matched) (code result))))
  | .rule index initial premises => Nat.pair 2 (Nat.pair index (Nat.pair (code initial) (witnessListCode premises)))
  | .forAll bodies => Nat.pair 3 (witnessListCode bodies)

/-- The code of a list of witnesses. -/
def witnessListCode : List Witness → ℕ
  | [] => 0
  | witness :: rest => Nat.pair (witnessCode witness) (witnessListCode rest) + 1
end

instance : Coded Witness := ⟨witnessCode⟩

theorem witnessListCode_eq : ∀ witnesses : List Witness, witnessListCode witnesses = code witnesses
  | [] => rfl
  | witness :: rest => by
      rw [witnessListCode, witnessListCode_eq rest, code_list (witness :: rest), code_list rest, List.map_cons,
        Encodable.encode_list_cons]
      rfl

/-- A constructor whose code tags the code of its arguments is computable on codes. -/
theorem tagged {α : Type} [Coded α] {f : α → Witness} (tag : ℕ) (same : ∀ a, code (f a) = Nat.pair tag (code a)) :
    CodeComputable f :=
  ⟨fun n => Nat.pair tag n, Primrec₂.natPair.to_comp.comp (Computable.const tag) Computable.id,
    fun a => (same a).symm⟩

theorem base_computable : CodeComputable Witness.base := tagged 0 fun _ => rfl

theorem premiseStep_computable :
    CodeComputable fun input : Witness × Pattern × Bindings × Bindings =>
      Witness.premiseStep input.1 input.2.1 input.2.2.1 input.2.2.2 :=
  tagged 1 fun _ => rfl

theorem rule_computable :
    CodeComputable fun input : ℕ × Bindings × List Witness => Witness.rule input.1 input.2.1 input.2.2 :=
  tagged 2 fun input => by
    show Nat.pair 2 (Nat.pair input.1 (Nat.pair (code input.2.1) (witnessListCode input.2.2))) = _
    rw [witnessListCode_eq]
    rfl

theorem forAll_computable : CodeComputable Witness.forAll :=
  tagged 3 fun bodies => by
    show Nat.pair 3 (witnessListCode bodies) = _
    rw [witnessListCode_eq]

/-! ## Collections and parameters -/

/-- The elements of a closed collection. -/
def collectionElements : Option Pattern → Option (List Pattern)
  | some (.collection _ elements none) => some elements
  | _ => none

theorem collectionElements_computable : CodeComputable collectionElements := by
  have onValue : CodeComputable₂ fun (_ : Option Pattern) (value : Pattern) =>
      @Pattern.casesOn (fun _ => Option (List Pattern)) value (fun _ => none) (fun _ => none) (fun _ _ => none)
        (fun _ _ => none) (fun _ _ _ => none) (fun _ _ => none)
        (fun _ elements rest => Option.casesOn (motive := fun _ => Option (List Pattern)) rest (some elements)
          fun _ => none) :=
    (casesOn (pattern := fun input : Option Pattern × Pattern => input.2) snd (const none) (const none)
      (const none) (const none) (const none) (const none)
      (optionString_casesOn (snd.comp (snd.comp snd)) (option_some (fst.comp (snd.comp snd))) (const none))).of_eq
      fun _ => rfl
  refine (option_casesOn id (const none) onValue).of_eq fun option => ?_
  rcases option with _ | ⟨_ | _ | _ | _ | _ | _ | ⟨_, _, _ | _⟩⟩ <;> rfl

theorem bindParameter_computable (parameter : String) :
    CodeComputable fun input : Bindings × Pattern => bindParameter input.1 parameter input.2 := by
  have kept : CodeComputable fun input : Bindings × Pattern => input.1.filter (·.1 != parameter) :=
    list_filter fst (CodeComputable.not (stringBEq.comp (pair (fst.comp snd) (const parameter))))
  exact (list_cons (pair (const parameter) snd) kept).of_eq fun _ => rfl

/-! ## The questions of a premise -/

/-- **What a premise asks the step**: the instantiated source of a step premise, and what a quantified
premise's body asks at each element of the collection. -/
def questionsOf (sites : Pattern) : Bindings → Premise → List Pattern
  | bindings, .forAll collection parameter body =>
      match collectionElements (bindings.lookup collection) with
      | none => []
      | some elements => elements.flatMap fun element =>
          questionsOf sites (bindParameter bindings parameter element) body
  | bindings, .congruence source target =>
      [applyBindingsScoped sites bindings (stepDepth sites (.congruence source target)) source]
  | bindings, .scopedStep step =>
      [applyBindingsScoped sites bindings (stepDepth sites (.scopedStep step)) step.source]
  | _, .freshness _ => []
  | _, .relationQuery _ _ => []

/-- A step premise, against a stepper. -/
def stepPremiseAt (recursive : Pattern → List (Witness × Pattern)) (sites : Pattern) (depth : ℕ)
    (source target : Pattern) (bindings : Bindings) : List (Witness × Bindings) :=
  (recursive (applyBindingsScoped sites bindings depth source)).flatMap fun entry =>
    (matchPattern target entry.2).filterMap fun matched =>
      (mergeBindings bindings matched).map fun result => (.premiseStep entry.1 entry.2 matched result, result)

variable (relEnv : RelationEnv) (language : LanguageDef)

theorem premiseAtUsing_congruence (recursive : Pattern → List (Witness × Pattern)) (sites : Pattern)
    (bindings : Bindings) (source target : Pattern) :
    premiseAtUsing relEnv language recursive sites bindings (.congruence source target) =
      stepPremiseAt recursive sites (stepDepth sites (.congruence source target)) source target bindings := by
  simp [premiseAtUsing, isBase, stepEndpoints, stepPremiseAt]

theorem premiseAtUsing_scopedStep (recursive : Pattern → List (Witness × Pattern)) (sites : Pattern)
    (bindings : Bindings) (step : ScopedStepPremise) :
    premiseAtUsing relEnv language recursive sites bindings (.scopedStep step) =
      stepPremiseAt recursive sites (stepDepth sites (.scopedStep step)) step.source step.target bindings := by
  simp [premiseAtUsing, isBase, stepEndpoints, stepPremiseAt]

theorem premiseAtUsing_base (recursive : Pattern → List (Witness × Pattern)) (sites : Pattern)
    (bindings : Bindings) {premise : Premise} (base : isBase premise = true) :
    premiseAtUsing relEnv language recursive sites bindings premise =
      (premiseStepWithEnv relEnv language bindings premise).map fun result => (.base result, result) := by
  cases premise <;> simp_all [premiseAtUsing, isBase]

theorem premiseAtUsing_forAll (recursive : Pattern → List (Witness × Pattern)) (sites : Pattern)
    (bindings : Bindings) (collection parameter : String) (body : Premise) :
    premiseAtUsing relEnv language recursive sites bindings (.forAll collection parameter body) =
      Option.casesOn (motive := fun _ => List (Witness × Bindings)) (collectionElements (bindings.lookup collection))
        [] fun elements =>
          (elements.foldr (fun element rest =>
              (premiseAtUsing relEnv language recursive sites (bindParameter bindings parameter element) body).flatMap
                fun entry => rest.map (entry.1 :: ·)) [[]]).map fun bodies => (.forAll bodies, bindings) := by
  rw [premiseAtUsing.eq_1]
  rcases bindings.lookup collection with _ | ⟨_ | _ | _ | _ | _ | _ | ⟨_, _, _ | _⟩⟩ <;> rfl

theorem foldr_congr_mem {α β γ : Type} (combine : β → γ → γ) (start : γ) {f g : α → β} :
    ∀ items : List α, (∀ item ∈ items, f item = g item) →
      items.foldr (fun item rest => combine (f item) rest) start = items.foldr (fun item rest => combine (g item) rest) start
  | [], _ => rfl
  | item :: items, same => by
      rw [List.foldr_cons, List.foldr_cons, same item List.mem_cons_self,
        foldr_congr_mem combine start items fun other member => same other (List.mem_cons_of_mem _ member)]

/-- **A premise depends on its stepper only through its questions.** -/
theorem premiseAtUsing_congr (sites : Pattern) {recursive other : Pattern → List (Witness × Pattern)} :
    ∀ (premise : Premise) (bindings : Bindings),
      (∀ question ∈ questionsOf sites bindings premise, recursive question = other question) →
        premiseAtUsing relEnv language recursive sites bindings premise =
          premiseAtUsing relEnv language other sites bindings premise
  | .freshness condition, bindings, _ => by
      rw [premiseAtUsing_base relEnv language recursive sites bindings (premise := .freshness condition) rfl,
        premiseAtUsing_base relEnv language other sites bindings (premise := .freshness condition) rfl]
  | .relationQuery relation arguments, bindings, _ => by
      rw [premiseAtUsing_base relEnv language recursive sites bindings
          (premise := .relationQuery relation arguments) rfl,
        premiseAtUsing_base relEnv language other sites bindings (premise := .relationQuery relation arguments) rfl]
  | .congruence source target, bindings, agree => by
      rw [premiseAtUsing_congruence, premiseAtUsing_congruence]
      unfold stepPremiseAt
      rw [agree _ (List.mem_singleton_self _)]
  | .scopedStep step, bindings, agree => by
      rw [premiseAtUsing_scopedStep, premiseAtUsing_scopedStep]
      unfold stepPremiseAt
      rw [agree _ (List.mem_singleton_self _)]
  | .forAll collection parameter body, bindings, agree => by
      rw [premiseAtUsing_forAll, premiseAtUsing_forAll]
      cases found : collectionElements (bindings.lookup collection) with
      | none => rfl
      | some elements =>
          dsimp only
          congr 1
          refine foldr_congr_mem (fun (choices : List (Witness × Bindings)) rest =>
            choices.flatMap fun entry => rest.map (entry.1 :: ·)) [[]] elements fun element member => ?_
          refine premiseAtUsing_congr sites body _ fun question asked => agree question ?_
          simp only [questionsOf, found, List.mem_flatMap]
          exact ⟨element, member, asked⟩

/-! ## Tables of answers -/

/-- Answers listed for terms. -/
abbrev Table := List (Pattern × List (Witness × Pattern))

/-- **A table read as a stepper**: the answers listed for a term, or none. -/
def lookupTable (table : Table) (term : Pattern) : List (Witness × Pattern) :=
  ((table.find? fun entry => entry.1 == term).map Prod.snd).getD []

theorem lookupTable_computable : CodeComputable₂ lookupTable :=
  (option_getD (option_map (list_find? fst (patternBEq.comp (pair (fst.comp snd) (snd.comp fst))))
    (snd.comp snd)) (const [])).of_eq fun _ => rfl

/-- A table listing a stepper's answers for some terms reads as the stepper at those terms. -/
theorem lookupTable_zip (recursive : Pattern → List (Witness × Pattern)) (questions : List Pattern)
    {question : Pattern} (asked : question ∈ questions) :
    lookupTable (questions.zip (questions.map recursive)) question = recursive question := by
  unfold lookupTable
  cases found : (questions.zip (questions.map recursive)).find? fun entry => entry.1 == question with
  | none =>
      exfalso
      have absent := List.find?_eq_none.mp found (question, recursive question)
        (List.mem_iff_getElem.mpr (by
          obtain ⟨index, bound, same⟩ := List.mem_iff_getElem.mp asked
          exact ⟨index, by simpa using bound, by simp [same]⟩))
      simp at absent
  | some entry =>
      have keyed := List.find?_some found
      have member := List.mem_of_find?_eq_some found
      obtain ⟨index, bound, same⟩ := List.mem_iff_getElem.mp member
      have key : entry.1 = question := by simpa using keyed
      simp only [Option.map_some, Option.getD_some]
      rw [← same, ← key, ← same]
      simp

/-! ## Premises against a table -/

theorem stepPremiseAt_computable (sites : Pattern) (depth : ℕ) (source target : Pattern) :
    CodeComputable fun input : Table × Bindings => stepPremiseAt (lookupTable input.1) sites depth source target input.2 := by
  have question : CodeComputable fun input : Table × Bindings => applyBindingsScoped sites input.2 depth source :=
    applyBindingsScoped_computable.comp (pair (pair (const sites) (pair snd (const depth))) (const source))
  have answers : CodeComputable fun input : Table × Bindings =>
      lookupTable input.1 (applyBindingsScoped sites input.2 depth source) :=
    lookupTable_computable.comp (pair fst question)
  have witnessed : CodeComputable fun w : (((Table × Bindings) × (Witness × Pattern)) × Bindings) × Bindings =>
      ((Witness.premiseStep w.1.1.2.1 w.1.1.2.2 w.1.2 w.2 : Witness), w.2) :=
    pair (premiseStep_computable.comp (pair (fst.comp (snd.comp (fst.comp fst)))
      (pair (snd.comp (snd.comp (fst.comp fst))) (pair (snd.comp fst) snd)))) snd
  have merged : CodeComputable₂ fun (z : ((Table × Bindings) × (Witness × Pattern))) (matched : Bindings) =>
      (mergeBindings z.1.2 matched).map fun result => ((Witness.premiseStep z.2.1 z.2.2 matched result : Witness), result) :=
    option_map (mergeBindings_computable.comp (pair (snd.comp (fst.comp fst)) snd)) witnessed
  have each : CodeComputable₂ fun (input : Table × Bindings) (entry : Witness × Pattern) =>
      (matchPattern target entry.2).filterMap fun matched =>
        (mergeBindings input.2 matched).map fun result => ((Witness.premiseStep entry.1 entry.2 matched result : Witness), result) :=
    list_filterMap (matchPattern_computable.comp (pair (const target) (snd.comp snd))) merged
  exact (list_flatMap answers each).of_eq fun _ => rfl

theorem tagBase_computable : CodeComputable₂ fun (_ : Table × Bindings) (result : Bindings) =>
    ((Witness.base result : Witness), result) :=
  pair (base_computable.comp snd) snd

/-- **A fixed premise against a table is computable on codes** in the table and the bindings. -/
theorem premiseAtTable_computable (relations : CodeComputable₂ relEnv.tuples) (sites : Pattern) :
    ∀ premise : Premise, CodeComputable fun input : Table × Bindings =>
      premiseAtUsing relEnv language (lookupTable input.1) sites input.2 premise
  | .freshness condition => by
      refine (list_map ((freshness_computable relEnv language condition).comp snd) tagBase_computable).of_eq
        fun input => ?_
      rw [premiseAtUsing_base relEnv language _ sites input.2 (premise := .freshness condition) rfl]
  | .relationQuery relation arguments => by
      refine (list_map ((relationQueryStep_computable relEnv relations language relation arguments).comp snd)
        tagBase_computable).of_eq fun input => ?_
      rw [premiseAtUsing_base relEnv language _ sites input.2 (premise := .relationQuery relation arguments) rfl]
      rfl
  | .congruence source target =>
      (stepPremiseAt_computable sites _ source target).of_eq fun input =>
        (premiseAtUsing_congruence relEnv language _ sites input.2 source target).symm
  | .scopedStep step =>
      (stepPremiseAt_computable sites _ step.source step.target).of_eq fun input =>
        (premiseAtUsing_scopedStep relEnv language _ sites input.2 step).symm
  | .forAll collection parameter body => by
      have inner := premiseAtTable_computable relations sites body
      have elementsOf : CodeComputable fun input : Table × Bindings =>
          collectionElements (input.2.lookup collection) :=
        collectionElements_computable.comp (lookup_computable.comp (pair snd (const collection)))
      have bodyAt : CodeComputable fun x : ((Table × Bindings) × List Pattern) × Pattern × List (List Witness) =>
          premiseAtUsing relEnv language (lookupTable x.1.1.1) sites (bindParameter x.1.1.2 parameter x.2.1) body :=
        inner.comp (pair (fst.comp (fst.comp fst)) ((bindParameter_computable parameter).comp
          (pair (snd.comp (fst.comp fst)) (fst.comp snd))))
      have extend : CodeComputable₂ fun (x : ((Table × Bindings) × List Pattern) × Pattern × List (List Witness))
          (entry : Witness × Bindings) => x.2.2.map (entry.1 :: ·) :=
        list_map (snd.comp (snd.comp fst)) (list_cons (fst.comp (snd.comp fst)) snd)
      have folded : CodeComputable₂ fun (input : Table × Bindings) (elements : List Pattern) =>
          (elements.foldr (fun element rest =>
              (premiseAtUsing relEnv language (lookupTable input.1) sites (bindParameter input.2 parameter element)
                body).flatMap fun entry => rest.map (entry.1 :: ·)) [[]]).map
            fun bodies => ((Witness.forAll bodies : Witness), input.2) :=
        list_map (list_foldr snd (const [[]]) (list_flatMap bodyAt extend))
          (pair (forAll_computable.comp snd) (snd.comp (fst.comp fst)))
      refine (option_casesOn elementsOf (const []) folded).of_eq fun input => ?_
      rw [premiseAtUsing_forAll]

end Mettapedia.OSLF.MeTTaIL.EngineCoded

#print axioms Mettapedia.OSLF.MeTTaIL.EngineCoded.premiseAtTable_computable
#print axioms Mettapedia.OSLF.MeTTaIL.EngineCoded.premiseAtUsing_congr
