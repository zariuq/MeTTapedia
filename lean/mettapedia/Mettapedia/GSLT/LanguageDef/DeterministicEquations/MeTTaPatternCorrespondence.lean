import Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.NaturalData
import Mettapedia.Languages.MeTTa.HE.SimpleMatch

/-!
# The emitted MeTTa patterns and their bindings

The actual emitter allocates a distinct target variable for every source
pattern occurrence. These laws connect those patterns to HE's existing
one-way control-form matcher. Equation-query matching, ordered control
evaluation and native execution remain separate boundaries.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Bindings simpleMatch)

def freshName (index : Nat) : String := "nik" ++ toString index

theorem freshName_injective : Function.Injective freshName := by
  intro first second same
  have digits : first.repr = second.repr := by
    simpa [freshName] using same
  have recovered := congrArg String.toNat? digits
  simpa only [Nat.toNat?_repr, Option.some.injEq] using recovered

/-- The caller's bindings do not occupy the emitter's remaining names. -/
def FreshFrom (first : Nat) (bindings : Bindings) : Prop :=
  ∀ index, first ≤ index → bindings.lookup (freshName index) = none

theorem FreshFrom.empty (first : Nat) : FreshFrom first Bindings.empty := by
  intro index _
  rfl

theorem FreshFrom.mono {first later : Nat} {bindings : Bindings}
    (fresh : FreshFrom first bindings) (after : first ≤ later) :
    FreshFrom later bindings := fun index bound => fresh index (after.trans bound)

theorem FreshFrom.assign {first : Nat} {bindings : Bindings}
    (fresh : FreshFrom first bindings) (value : Atom) :
    FreshFrom (first + 1) (bindings.assign (freshName first) value) := by
  intro index bound
  have distinct : freshName index ≠ freshName first := by
    intro same
    have := freshName_injective same
    omega
  have absent := fresh first (by omega)
  have laterAbsent := fresh index (by omega)
  have assigned : bindings.assign (freshName first) value =
      { bindings with assignments := bindings.assignments ++ [(freshName first, value)] } := by
    simp only [Bindings.assign, Bindings.isBound, absent, Option.isSome_none,
      Bool.false_eq_true, if_false]
  rw [assigned]
  change List.lookup (freshName index) (bindings.assignments ++ [(freshName first, value)]) = none
  change List.lookup (freshName index) bindings.assignments = none at laterAbsent
  rw [List.lookup_append, laterAbsent]
  simp [distinct]

/-- Target bindings corresponding to the source match's ordered occurrences. -/
def extendMatch (first : Nat) (environment : Env) (bindings : Bindings) : Bindings :=
  match environment with
  | [] => bindings
  | (_, value) :: rest =>
      extendMatch (first + 1) rest
        (bindings.assign (freshName first) (MeTTaData.encode value))

theorem extendMatch_append (first : Nat) (left right : Env) (bindings : Bindings) :
    extendMatch first (left ++ right) bindings =
      extendMatch (first + left.length) right (extendMatch first left bindings) := by
  induction left generalizing first bindings with
  | nil => rfl
  | cons pair rest ih =>
      simp only [List.cons_append, extendMatch, List.length_cons]
      rw [ih]
      congr 1
      omega

theorem extendMatch_fresh {first : Nat} (environment : Env) {bindings : Bindings}
    (fresh : FreshFrom first bindings) :
    FreshFrom (first + environment.length) (extendMatch first environment bindings) := by
  induction environment generalizing first bindings with
  | nil => simpa [extendMatch] using fresh
  | cons pair rest ih =>
      have next := ih (fresh.assign (MeTTaData.encode pair.2))
      simpa [extendMatch, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using next

@[simp] theorem fresh_run (first : Nat) :
    fresh first = (.var (freshName first), first + 1) := rfl

@[simp] theorem pattern_variable (name : String) (first : Nat) :
    pattern (.var name) first =
      ((.var (freshName first), [(name, .var (freshName first))]), first + 1) := rfl

@[simp] theorem patterns_nil (first : Nat) :
    patterns [] first = ((.symbol "nik:Nil", []), first) := rfl

@[simp] theorem pattern_symbol (name : String) (first : Nat) :
    pattern (.sym name) first = ((MeTTaData.encode (.sym name), []), first) := rfl

@[simp] theorem pattern_literal (spelling : String) (first : Nat) :
    pattern (.lit spelling) first = ((MeTTaData.encode (.lit spelling), []), first) := rfl

theorem pattern_expression (items : List Term) (first : Nat) :
    pattern (.expr items) first =
      ((call "nik:Expr" [(patterns items first).1.1], (patterns items first).1.2),
        (patterns items first).2) := rfl

theorem pattern_list (items : List Term) (first : Nat) :
    pattern (.list items) first =
      ((call "nik:List" [(patterns items first).1.1], (patterns items first).1.2),
        (patterns items first).2) := rfl

theorem patterns_cons (head : Term) (rest : List Term) (first : Nat) :
    patterns (head :: rest) first =
      let emittedHead := pattern head first
      let emittedTail := patterns rest emittedHead.2
      ((call "nik:Cons" [emittedHead.1.1, emittedTail.1.1],
          emittedHead.1.2 ++ emittedTail.1.2), emittedTail.2) := rfl

mutual

theorem pattern_end_of_match (source value : Term) (environment : Env)
    (matched : matchTerm source value = some environment) (first : Nat) :
    (pattern source first).2 = first + environment.length := by
  cases source <;> cases value <;>
    simp only [matchTerm] at matched
  all_goals first
    | contradiction
    | (split at matched <;> first | contradiction | (cases matched; rfl))
    | (cases matched; rfl)
    | (simpa only [pattern_expression, pattern_list] using
        patterns_end_of_match _ _ environment matched first)
termination_by sizeOf source

theorem patterns_end_of_match (source values : List Term) (environment : Env)
    (matched : matchTerms source values = some environment) (first : Nat) :
    (patterns source first).2 = first + environment.length := by
  cases source with
  | nil => cases values <;> simp_all [matchTerms, patterns_nil]
  | cons head rest =>
      cases values with
      | nil => simp [matchTerms] at matched
      | cons value tail =>
          cases headMatch : matchTerm head value with
          | none => simp [matchTerms, headMatch] at matched
          | some headEnvironment =>
              cases tailMatch : matchTerms rest tail with
              | none => simp [matchTerms, headMatch, tailMatch] at matched
              | some tailEnvironment =>
                  have same : headEnvironment ++ tailEnvironment = environment := by
                    simpa [matchTerms, headMatch, tailMatch] using matched
                  rw [patterns_cons]
                  simp only
                  rw [patterns_end_of_match rest tail tailEnvironment tailMatch,
                    pattern_end_of_match head value headEnvironment headMatch, ← same,
                    List.length_append, Nat.add_assoc]
termination_by sizeOf source

end

private theorem simpleMatch_node_one (tag : String) (left right : Atom)
    (bindings : Bindings) (fuel : Nat) :
    simpleMatch (call tag [left]) (call tag [right]) bindings (fuel + 2) =
      simpleMatch left right bindings (fuel + 1) := by
  simp only [call, simpleMatch, List.length_cons, List.length_nil, bne_self_eq_false,
    Bool.false_eq_true, if_false, simpleMatch.simpleMatchList, beq_self_eq_true, if_true]
  cases simpleMatch left right bindings (fuel + 1) <;> rfl

private theorem simpleMatch_node_two (tag : String) (leftHead leftTail rightHead rightTail : Atom)
    (bindings : Bindings) (fuel : Nat) :
    simpleMatch (call tag [leftHead, leftTail]) (call tag [rightHead, rightTail])
        bindings (fuel + 2) =
      (simpleMatch leftHead rightHead bindings (fuel + 1)).bind
        (fun next => simpleMatch leftTail rightTail next (fuel + 1)) := by
  simp only [call, simpleMatch, List.length_cons, List.length_nil, bne_self_eq_false,
    Bool.false_eq_true, if_false, simpleMatch.simpleMatchList, beq_self_eq_true, if_true]
  cases simpleMatch leftHead rightHead bindings (fuel + 1) with
  | none => rfl
  | some next =>
      change (match simpleMatch leftTail rightTail next (fuel + 1) with
        | some result => some result | none => none) =
          simpleMatch leftTail rightTail next (fuel + 1)
      cases simpleMatch leftTail rightTail next (fuel + 1) <;> rfl

mutual

/-- At sufficient fuel, emitted patterns preserve successes and refusals, with
the exact target bindings. Source variables remain encoded data on the right. -/
theorem pattern_matches (source value : Term) (first fuel : Nat) (bindings : Bindings)
    (enough : sizeOf source + 2 ≤ fuel) (fresh : FreshFrom first bindings) :
    simpleMatch (pattern source first).1.1 (MeTTaData.encode value) bindings fuel =
      (matchTerm source value).map (fun environment => extendMatch first environment bindings) := by
  cases fuel with
  | zero => omega
  | succ fuel =>
      cases source with
      | var name =>
          simp [simpleMatch, fresh first (by omega), matchTerm, extendMatch]
      | sym name =>
          cases fuel with
          | zero => simp at enough
          | succ fuel =>
              cases value <;>
                simp [pattern_symbol, MeTTaData.encode, simpleMatch, simpleMatch.simpleMatchList,
                  matchTerm, extendMatch]
              split <;> symm <;> assumption
      | lit spelling =>
          cases fuel with
          | zero => simp at enough
          | succ fuel =>
              cases value <;>
                simp [pattern_literal, MeTTaData.encode, simpleMatch, simpleMatch.simpleMatchList,
                  matchTerm, extendMatch]
              split <;> symm <;> assumption
      | expr items =>
          cases fuel with
          | zero => simp at enough
          | succ fuel =>
              cases value with
              | expr values =>
                  rw [pattern_expression]
                  change simpleMatch (call "nik:Expr" [(patterns items first).1.1])
                    (call "nik:Expr" [MeTTaData.encodeItems values]) bindings (fuel + 2) = _
                  rw [simpleMatch_node_one]
                  exact patterns_match items values first (fuel + 1) bindings (by simp at enough; omega) fresh
              | sym | lit | var | list =>
                  simp [pattern_expression, MeTTaData.encode, call, simpleMatch,
                    simpleMatch.simpleMatchList, matchTerm]
      | list items =>
          cases fuel with
          | zero => simp at enough
          | succ fuel =>
              cases value with
              | list values =>
                  rw [pattern_list]
                  change simpleMatch (call "nik:List" [(patterns items first).1.1])
                    (call "nik:List" [MeTTaData.encodeItems values]) bindings (fuel + 2) = _
                  rw [simpleMatch_node_one]
                  exact patterns_match items values first (fuel + 1) bindings (by simp at enough; omega) fresh
              | sym | lit | var | expr =>
                  simp [pattern_list, MeTTaData.encode, call, simpleMatch,
                    simpleMatch.simpleMatchList, matchTerm]
termination_by sizeOf source

theorem patterns_match (source values : List Term) (first fuel : Nat) (bindings : Bindings)
    (enough : sizeOf source + 2 ≤ fuel) (fresh : FreshFrom first bindings) :
    simpleMatch (patterns source first).1.1 (MeTTaData.encodeItems values) bindings fuel =
      (matchTerms source values).map (fun environment => extendMatch first environment bindings) := by
  cases fuel with
  | zero => omega
  | succ fuel =>
      cases source with
      | nil =>
          cases values <;> simp [MeTTaData.encodeItems, simpleMatch, matchTerms, extendMatch]
      | cons head rest =>
          cases values with
          | nil => simp [patterns_cons, call, MeTTaData.encodeItems, simpleMatch, matchTerms]
          | cons value tail =>
              cases fuel with
              | zero => simp at enough
              | succ fuel =>
                  rw [patterns_cons]
                  change simpleMatch
                    (call "nik:Cons" [(pattern head first).1.1,
                      (patterns rest (pattern head first).2).1.1])
                    (call "nik:Cons" [MeTTaData.encode value, MeTTaData.encodeItems tail])
                    bindings (fuel + 2) = _
                  rw [simpleMatch_node_two,
                    pattern_matches head value first (fuel + 1) bindings (by simp at enough; omega) fresh]
                  cases headMatched : matchTerm head value with
                  | none => simp [headMatched, matchTerms]
                  | some environment =>
                      simp only [Option.map_some, Option.bind_some]
                      rw [pattern_end_of_match head value environment headMatched first,
                        patterns_match rest tail (first + environment.length) (fuel + 1)
                          (extendMatch first environment bindings) (by simp at enough; omega)
                          (extendMatch_fresh environment fresh)]
                      cases tailMatched : matchTerms rest tail <;>
                        simp [matchTerms, headMatched, tailMatched, extendMatch_append]
termination_by sizeOf source

end

theorem pattern_success_iff (source value : Term) (first fuel : Nat)
    (bindings result : Bindings) (enough : sizeOf source + 2 ≤ fuel)
    (fresh : FreshFrom first bindings) :
    simpleMatch (pattern source first).1.1 (MeTTaData.encode value) bindings fuel = some result ↔
      ∃ environment, matchTerm source value = some environment ∧
        extendMatch first environment bindings = result := by
  rw [pattern_matches source value first fuel bindings enough fresh]
  exact Option.map_eq_some_iff

/-- This refusal is independent of fuel once the structural bound is met. -/
theorem pattern_refusal_iff (source value : Term) (first fuel : Nat)
    (bindings : Bindings) (enough : sizeOf source + 2 ≤ fuel)
    (fresh : FreshFrom first bindings) :
    simpleMatch (pattern source first).1.1 (MeTTaData.encode value) bindings fuel = none ↔
      matchTerm source value = none := by
  rw [pattern_matches source value first fuel bindings enough fresh]
  exact Option.map_eq_none_iff

theorem patterns_refusal_iff (source values : List Term) (first fuel : Nat)
    (bindings : Bindings) (enough : sizeOf source + 2 ≤ fuel)
    (fresh : FreshFrom first bindings) :
    simpleMatch (patterns source first).1.1 (MeTTaData.encodeItems values) bindings fuel = none ↔
      matchTerms source values = none := by
  rw [patterns_match source values first fuel bindings enough fresh]
  exact Option.map_eq_none_iff

end Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit
