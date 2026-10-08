import Mettapedia.OSLF.MeTTaIL.UnaryNumeralMatching
import Mettapedia.GSLT.LanguageDef.ScopePolicies.CoreLanguageDef

/-!
# The language definition and the evaluator agree on straight-line programs

The fragment (`Straight`): a sequence of `let`s of symbols into slots, ending
in a slot or a symbol, every slot new where it is bound.  It is read on both
sides.

* **As a term of the evaluator** (`Straight.toTm`), in the identity model: the
  slots are binder identities, a `let` is a plain `let`.
* **As a pattern of the language definition** (`Straight.toPattern`): a slot is
  the free variable that an injective naming gives it, a symbol the numeral of
  its code; a store is a list of bindings (`storePattern`).

## The agreement

`straight_agreement`: from a store that binds none of the program's slots,

* the evaluator, at every discipline, path and sufficient fuel, returns one
  result: the program's last atom, with the store extended by the program's
  bindings;
* the definition reduces the configuration of that store and the program to
  the configuration of the extended store and the last atom, and that
  configuration has no step.

The steps of the definition on this fragment are characterized exactly
(`letFresh_step_iff`): a `let` of a symbol into a named slot steps if and only
if the store does not mention the slot, and then to one configuration.

## What is not shown

The statement is about the reduction that the definition generates on patterns
(`ContextualStep.Step`).  It is not a statement about `lexicalFreshTheory`:
the terms of a presented theory are closed, and a slot is a free variable
(`slot_not_presented_term`).  Outside the fragment the definition has no rule:
when the store already binds the slot the evaluator refines and the definition
does not step (`refinement_not_covered`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ScopePolicies

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline
open Mettapedia.GSLT.LanguageDef.TemplateScope
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.Substitution (freeVars isFresh checkFreshness)
open LexicalFreshCore

/-! ## The steps of the definition on a `let` of a symbol -/

/-- The bindings that the rule's left side takes from a `let` of a symbol. -/
def letBindings (name : String) (code : ℕ) (store body : Pattern) : Bindings :=
  [("k", .fvar name), ("b", body), ("s", numeral code), ("st", store)]

theorem match_letFresh (name : String) (code : ℕ) (store body : Pattern) :
    matchPatternForRule lexicalFreshCore letFresh
        (cfg store (letT (.fvar name) (symT (numeral code)) body)) =
      [letBindings name code store body] := by
  rw [matchPatternForRule_eq_syntactic]
  simp [letFresh, letBindings, cfg, letT, symT, matchPattern, matchArgs, mergeBindings]

theorem letFresh_aligned : ruleDepthAligned letFresh = true := by decide

theorem apply_letFresh (name : String) (code : ℕ) (store body : Pattern) :
    applyBindingsForRule lexicalFreshCore letFresh (letBindings name code store body) =
      cfg (bind (.fvar name) (symT (numeral code)) store) body := by
  rw [applyBindingsForRule, applyBindingsForRuleUsing_empty,
    applyRuleBindings_eq_applyBindings _ _ letFresh_aligned]
  simp [letFresh, letBindings, cfg, LexicalFreshCore.bind, symT, applyBindings]

/-- The first freshness premise holds: a symbol mentions no slot. -/
theorem valuePremise (name : String) (code : ℕ) (store body : Pattern) :
    letBindings name code store body ∈
      engineBasePremises RelationEnv.empty lexicalFreshCore (letBindings name code store body)
        (.freshness { varName := "k", term := symT (.fvar "s") }) := by
  show letBindings name code store body ∈
    (if checkFreshness
        ⟨name, applyBindings (letBindings name code store body) (symT (.fvar "s"))⟩ = true
      then [letBindings name code store body] else [])
  have fresh : checkFreshness
      ⟨name, applyBindings (letBindings name code store body) (symT (.fvar "s"))⟩ = true := by
    simp [checkFreshness, isFresh, letBindings, symT, applyBindings, freeVars, numeral]
  rw [if_pos fresh]
  exact List.mem_singleton.mpr rfl

/-- The second freshness premise is that the store does not mention the
slot. -/
theorem storePremise_iff (name : String) (code : ℕ) (store body : Pattern)
    (result : Bindings) :
    result ∈ engineBasePremises RelationEnv.empty lexicalFreshCore
        (letBindings name code store body)
        (.freshness { varName := "k", term := .fvar "st" }) ↔
      isFresh name store = true ∧ result = letBindings name code store body := by
  show result ∈
    (if checkFreshness
        ⟨name, applyBindings (letBindings name code store body) (.fvar "st")⟩ = true
      then [letBindings name code store body] else []) ↔ _
  have term : applyBindings (letBindings name code store body) (.fvar "st") = store := by
    simp [letBindings, applyBindings]
  rw [term]
  by_cases fresh : isFresh name store = true
  · have check : checkFreshness ⟨name, store⟩ = true := fresh
    rw [if_pos check]
    simp [fresh]
  · have check : ¬ checkFreshness ⟨name, store⟩ = true := fresh
    rw [if_neg check]
    simp [fresh]

/-- **The rule fires on a slot that the store does not mention.** -/
theorem letFresh_step (name : String) (code : ℕ) (store body : Pattern)
    (fresh : isFresh name store = true) :
    Step (engineBasePremises RelationEnv.empty) lexicalFreshCore
      (cfg store (letT (.fvar name) (symT (numeral code)) body))
      (cfg (bind (.fvar name) (symT (numeral code)) store) body) := by
  refine ⟨1, StepAt.rule (rule := letFresh)
    (initialBindings := letBindings name code store body)
    (finalBindings := letBindings name code store body) ?_ ?_ ?_ ?_⟩
  · simp [lexicalFreshCore]
  · rw [match_letFresh]
    exact List.mem_singleton.mpr rfl
  · exact .cons (.freshness (valuePremise name code store body))
      (.cons (.freshness ((storePremise_iff name code store body _).mpr ⟨fresh, rfl⟩)) (.nil _))
  · exact apply_letFresh name code store body

/-- **And only so**: a step of a `let` of a symbol into a named slot needs the
store not to mention the slot, and goes to the store extended by the
binding. -/
theorem letFresh_step_inv {name : String} {code : ℕ} {store body target : Pattern}
    (step : Step (engineBasePremises RelationEnv.empty) lexicalFreshCore
      (cfg store (letT (.fvar name) (symT (numeral code)) body)) target) :
    isFresh name store = true ∧
      target = cfg (bind (.fvar name) (symT (numeral code)) store) body := by
  obtain ⟨fuel, step⟩ := step
  cases step with
  | @rule fuel source target rule initial final member matched premises applied =>
      have isRule : rule = letFresh := by simpa [lexicalFreshCore] using member
      subst isRule
      rw [match_letFresh] at matched
      have isInitial := List.mem_singleton.mp matched
      subst isInitial
      have premiseList : letFresh.premises =
          [.freshness { varName := "k", term := symT (.fvar "s") },
            .freshness { varName := "k", term := .fvar "st" }] := rfl
      rw [premiseList] at premises
      cases premises with
      | cons first rest =>
          cases first with
          | freshness firstMember =>
              have firstStep : _ ∈ premiseStepWithEnv RelationEnv.empty lexicalFreshCore
                  (letBindings name code store body)
                  (.freshness ⟨"k", symT (.fvar "s")⟩) := firstMember
              have middleSame := premiseStepWithEnv_freshness_mem firstStep
              subst middleSame
              cases rest with
              | cons second last =>
                  cases last
                  cases second with
                  | freshness secondMember =>
                      obtain ⟨fresh, same⟩ :=
                        (storePremise_iff name code store body _).mp secondMember
                      subst same
                      exact ⟨fresh, by rw [← applied, apply_letFresh]⟩

/-- **The steps of the definition on a `let` of a symbol into a named
slot.** -/
theorem letFresh_step_iff (name : String) (code : ℕ) (store body target : Pattern) :
    Step (engineBasePremises RelationEnv.empty) lexicalFreshCore
        (cfg store (letT (.fvar name) (symT (numeral code)) body)) target ↔
      isFresh name store = true ∧
        target = cfg (bind (.fvar name) (symT (numeral code)) store) body :=
  ⟨letFresh_step_inv, fun ⟨fresh, same⟩ => same ▸ letFresh_step name code store body fresh⟩

/-- A configuration whose term is a symbol has no step. -/
theorem symbol_normal (code : ℕ) (store target : Pattern) :
    ¬ Step (engineBasePremises RelationEnv.empty) lexicalFreshCore
      (cfg store (symT (numeral code))) target := by
  apply not_step_of_matchPatternForRule_eq_nil
  intro rule member
  have isRule : rule = letFresh := by simpa [lexicalFreshCore] using member
  subst isRule
  rw [matchPatternForRule_eq_syntactic]
  simp [letFresh, cfg, letT, symT, matchPattern, matchArgs]

/-- A configuration whose term is a slot has no step. -/
theorem slot_normal (name : String) (store target : Pattern) :
    ¬ Step (engineBasePremises RelationEnv.empty) lexicalFreshCore
      (cfg store (.fvar name)) target := by
  apply not_step_of_matchPatternForRule_eq_nil
  intro rule member
  have isRule : rule = letFresh := by simpa [lexicalFreshCore] using member
  subst isRule
  rw [matchPatternForRule_eq_syntactic]
  simp [letFresh, cfg, letT, symT, matchPattern, matchArgs]

/-! ## The fragment -/

universe u v

/-- **Straight-line programs**: `let`s of symbols into slots, ending in a slot
or a symbol. -/
inductive Straight (S : Type u) (X : Type v) where
  | sym (s : S)
  | slot (k : SlotId X)
  | bind (k : SlotId X) (s : S) (rest : Straight S X)

variable {S : Type u} {X : Type v}

namespace Straight

/-- The program, as a term of the evaluator in the identity model. -/
def toTm : Straight S X → Tm S (BId X)
  | .sym s => .sym s
  | .slot k => iVar k
  | .bind k s rest => .letP (iVar k) (.sym s) rest.toTm

/-- The program, as a pattern of the language definition. -/
def toPattern (enc : SlotId X → String) (code : S → ℕ) : Straight S X → Pattern
  | .sym s => symT (numeral (code s))
  | .slot k => .fvar (enc k)
  | .bind k s rest => letT (.fvar (enc k)) (symT (numeral (code s))) (rest.toPattern enc code)

/-- The last atom of the program. -/
def final : Straight S X → Straight S X
  | .bind _ _ rest => rest.final
  | atom => atom

/-- The number of `let`s. -/
def length : Straight S X → ℕ
  | .bind _ _ rest => rest.length + 1
  | _ => 0

/-- The store after the program: its bindings in front, the last first. -/
def extend : Straight S X → List (SlotId X × S) → List (SlotId X × S)
  | .bind k s rest, store => rest.extend ((k, s) :: store)
  | _, store => store

/-- Every slot is new where the program binds it. -/
def Fresh : Straight S X → List (SlotId X × S) → Prop
  | .bind k s rest, store => k ∉ store.map Prod.fst ∧ rest.Fresh ((k, s) :: store)
  | _, _ => True

end Straight

/-- A store, as a pattern of the language definition. -/
def storePattern (enc : SlotId X → String) (code : S → ℕ) : List (SlotId X × S) → Pattern
  | [] => emptyStore
  | (k, s) :: rest =>
      bind (.fvar (enc k)) (symT (numeral (code s))) (storePattern enc code rest)

/-- The slots that a store pattern mentions are the slots it binds. -/
theorem freeVars_storePattern (enc : SlotId X → String) (code : S → ℕ) :
    ∀ store : List (SlotId X × S),
      freeVars (storePattern enc code store) = store.map fun entry => enc entry.1
  | [] => by simp [storePattern, emptyStore, freeVars]
  | (k, s) :: rest => by
      simp [storePattern, LexicalFreshCore.bind, symT, numeral, freeVars,
        freeVars_storePattern enc code rest]

/-- Under an injective naming, a slot is fresh for a store pattern exactly when
the store does not bind it. -/
theorem isFresh_storePattern {enc : SlotId X → String} (injective : Function.Injective enc)
    (code : S → ℕ) (k : SlotId X) (store : List (SlotId X × S)) :
    isFresh (enc k) (storePattern enc code store) = true ↔ k ∉ store.map Prod.fst := by
  simp only [isFresh, freeVars_storePattern, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not, List.mem_map, not_exists, not_and]
  constructor
  · intro apart entry member same
    exact apart entry member (congrArg enc same)
  · intro apart entry member same
    exact apart entry member (injective same)

variable [DecidableEq X]

/-- A store, as a store of the evaluator. -/
def storeOf : List (SlotId X × S) → GStore S (BId X)
  | [] => Store.empty
  | (k, s) :: rest => fun name => if name = .src (.slot k) then some (.sym s) else storeOf rest name

theorem storeOf_unbound : ∀ (store : List (SlotId X × S)) (k : SlotId X),
    k ∉ store.map Prod.fst → storeOf store (.src (.slot k)) = none
  | [], _, _ => rfl
  | (k', s) :: rest, k, apart => by
      simp only [List.map_cons, List.mem_cons, not_or] at apart
      have differ : (Nm.src (BId.slot k) : Nm (BId X)) ≠ .src (.slot k') := by
        intro same
        injection same with same
        injection same with same
        exact apart.1 same
      simp only [storeOf, if_neg differ]
      exact storeOf_unbound rest k apart.2

/-! ## The agreement -/

/-- **The evaluator on a straight-line program**: one result, the last atom,
with the store extended by the program's bindings. -/
theorem run_straight [DecidableEq S] (d : Disc) (prog : S → Option (Tm S (BId X))) (n : ℕ) :
    ∀ (program : Straight S X) (store : List (SlotId X × S)) (π : Path),
      program.Fresh store →
        run d prog (n + 1 + program.length) π (storeOf store) program.toTm =
          some [(program.final.toTm, storeOf (program.extend store))]
  | .sym _, _, _, _ => rfl
  | .slot _, _, _, _ => rfl
  | .bind k s rest, store, π, fresh => by
      have fuel : n + 1 + (Straight.bind k s rest).length = (n + rest.length) + 2 := by
        simp only [Straight.length]
        omega
      have fuel' : n + rest.length + 1 = n + 1 + rest.length := by omega
      rw [fuel]
      show run d prog (n + rest.length + 2) π (storeOf store)
        (.letP (.var (.src (.slot k))) (.sym s) rest.toTm) = _
      rw [run_let_symbol d prog (n + rest.length) π (storeOf store) (.src (.slot k)) s rest.toTm
        (storeOf_unbound store k fresh.1), fuel']
      exact run_straight d prog n rest ((k, s) :: store) (π ++ [1]) fresh.2

omit [DecidableEq X] in
/-- **The definition on a straight-line program**: it reduces to the
configuration of the extended store and the last atom. -/
theorem steps_straight {enc : SlotId X → String} (injective : Function.Injective enc)
    (code : S → ℕ) :
    ∀ (program : Straight S X) (store : List (SlotId X × S)), program.Fresh store →
      Relation.ReflTransGen (Step (engineBasePremises RelationEnv.empty) lexicalFreshCore)
        (cfg (storePattern enc code store) (program.toPattern enc code))
        (cfg (storePattern enc code (program.extend store)) (program.final.toPattern enc code))
  | .sym _, _, _ => .refl
  | .slot _, _, _ => .refl
  | .bind k s rest, store, fresh =>
      Relation.ReflTransGen.head
        (letFresh_step (enc k) (code s) (storePattern enc code store) (rest.toPattern enc code)
          ((isFresh_storePattern injective code k store).mpr fresh.1))
        (steps_straight injective code rest ((k, s) :: store) fresh.2)

omit [DecidableEq X] in
/-- The last atom is a slot or a symbol. -/
theorem Straight.final_atom : ∀ program : Straight S X,
    (∃ s, program.final = .sym s) ∨ ∃ k, program.final = .slot k
  | .sym s => Or.inl ⟨s, rfl⟩
  | .slot k => Or.inr ⟨k, rfl⟩
  | .bind _ _ rest => rest.final_atom

omit [DecidableEq X] in
/-- The configuration reached has no step. -/
theorem final_normal (enc : SlotId X → String) (code : S → ℕ) (program : Straight S X)
    (store target : Pattern) :
    ¬ Step (engineBasePremises RelationEnv.empty) lexicalFreshCore
      (cfg store (program.final.toPattern enc code)) target := by
  rcases program.final_atom with ⟨s, isSym⟩ | ⟨k, isSlot⟩
  · rw [isSym]
    exact symbol_normal (code s) store target
  · rw [isSlot]
    exact slot_normal (enc k) store target

/-- **Agreement on straight-line programs.**  From a store that binds none of
the program's slots, the evaluator returns the last atom with the extended
store, and the definition reduces the configuration to that of the extended
store and the last atom, where it stops. -/
theorem straight_agreement [DecidableEq S] {enc : SlotId X → String}
    (injective : Function.Injective enc) (code : S → ℕ) (program : Straight S X)
    (store : List (SlotId X × S)) (fresh : program.Fresh store) (d : Disc)
    (prog : S → Option (Tm S (BId X))) (n : ℕ) (π : Path) :
    run d prog (n + 1 + program.length) π (storeOf store) program.toTm =
        some [(program.final.toTm, storeOf (program.extend store))] ∧
      Relation.ReflTransGen (Step (engineBasePremises RelationEnv.empty) lexicalFreshCore)
        (cfg (storePattern enc code store) (program.toPattern enc code))
        (cfg (storePattern enc code (program.extend store))
          (program.final.toPattern enc code)) ∧
      ∀ target, ¬ Step (engineBasePremises RelationEnv.empty) lexicalFreshCore
        (cfg (storePattern enc code (program.extend store))
          (program.final.toPattern enc code)) target :=
  ⟨run_straight d prog n program store π fresh, steps_straight injective code program store fresh,
    fun target => final_normal enc code program _ target⟩

/-! ## What is not covered -/

/-- **Refinement is outside the definition.**  When the store binds the slot
to the same symbol, the evaluator runs the body from the same store, and the
definition has no step. -/
theorem refinement_not_covered [DecidableEq S] {enc : SlotId X → String}
    (injective : Function.Injective enc) (code : S → ℕ) (k : SlotId X) (s : S)
    (rest : Straight S X) (store : List (SlotId X × S)) (d : Disc)
    (prog : S → Option (Tm S (BId X))) (n : ℕ) (π : Path) :
    run d prog (n + 2) π (storeOf ((k, s) :: store)) (Straight.bind k s rest).toTm =
        run d prog (n + 1) (π ++ [1]) (storeOf ((k, s) :: store)) rest.toTm ∧
      ∀ target, ¬ Step (engineBasePremises RelationEnv.empty) lexicalFreshCore
        (cfg (storePattern enc code ((k, s) :: store))
          ((Straight.bind k s rest).toPattern enc code)) target := by
  refine ⟨run_let_same d prog n π _ (.src (.slot k)) s rest.toTm (by simp [storeOf]), ?_⟩
  intro target step
  have fresh := (letFresh_step_inv step).1
  exact (isFresh_storePattern injective code k ((k, s) :: store)).mp fresh (by simp)

/-- **A slot is not a term of the presented theory**: its terms are typed with
no free variable. -/
theorem slot_not_presented_term (name : String) (interface : Contexts.Interface)
    (term : Contexts.Term lexicalFreshCore interface) : term.1 ≠ .fvar name := by
  intro same
  have typed := term.2.1
  rw [same] at typed
  cases typed with
  | fvar found => cases found

#print axioms letFresh_step_iff
#print axioms run_straight
#print axioms steps_straight
#print axioms straight_agreement
#print axioms refinement_not_covered
#print axioms slot_not_presented_term

end Mettapedia.GSLT.LanguageDef.ScopePolicies
