import Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaPatternCorrespondence
import Mettapedia.Languages.MeTTa.HE.BindingComposition

/-!
# Reading the bindings produced by emitted patterns

The emitter's name table and the target bindings refer to the same ordered
source occurrences. Reading a source variable through that actual table gives
its encoded source value, including the source environment's first-occurrence
lookup convention. This is a lookup law; evaluation of generated bodies is a
separate obligation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Bindings)

/-- The sequential target names belonging to a successful source match. -/
def namesForMatch (first : Nat) (environment : Env) : Names :=
  environment.mapIdx (fun index entry =>
    (entry.1, .var (freshName (first + index))))

@[simp] theorem namesForMatch_nil (first : Nat) : namesForMatch first [] = [] := rfl

theorem namesForMatch_cons (first : Nat) (entry : String × Term) (rest : Env) :
    namesForMatch first (entry :: rest) =
      (entry.1, .var (freshName first)) :: namesForMatch (first + 1) rest := by
  simp [namesForMatch, List.mapIdx_cons, Nat.add_left_comm, Nat.add_comm]

theorem namesForMatch_append (first : Nat) (left right : Env) :
    namesForMatch first (left ++ right) =
      namesForMatch first left ++ namesForMatch (first + left.length) right := by
  simp [namesForMatch, List.mapIdx_append, Nat.add_left_comm, Nat.add_comm]

mutual

theorem pattern_names_of_match (source value : Term) (environment : Env)
    (matched : matchTerm source value = some environment) (first : Nat) :
    (pattern source first).1.2 = namesForMatch first environment := by
  cases source <;> cases value <;> simp only [matchTerm] at matched
  all_goals first
    | contradiction
    | (split at matched <;> first | contradiction | (cases matched; rfl))
    | (cases matched; rfl)
    | (simpa only [pattern_expression, pattern_list] using
        patterns_names_of_match _ _ environment matched first)
termination_by sizeOf source

theorem patterns_names_of_match (source values : List Term) (environment : Env)
    (matched : matchTerms source values = some environment) (first : Nat) :
    (patterns source first).1.2 = namesForMatch first environment := by
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
                  rw [pattern_names_of_match head value headEnvironment headMatch,
                    patterns_names_of_match rest tail tailEnvironment tailMatch,
                    pattern_end_of_match head value headEnvironment headMatch,
                    ← same, namesForMatch_append]
termination_by sizeOf source

end

/-- Existing target bindings survive matching fresh occurrences. -/
theorem extendMatch_extends (environment : Env) {first : Nat} {bindings : Bindings}
    (fresh : FreshFrom first bindings) :
    bindings.Extends (extendMatch first environment bindings) := by
  induction environment generalizing first bindings with
  | nil => exact Bindings.extends_refl bindings
  | cons entry rest ih =>
      exact Bindings.extends_trans
        (Mettapedia.Languages.MeTTa.HE.extends_assign_of_lookup_none bindings
          (freshName first) (MeTTaData.encode entry.2) (fresh first (by omega)))
        (ih (fresh.assign (MeTTaData.encode entry.2)))

theorem extendMatch_lookup_index (environment : Env) {first : Nat} {bindings : Bindings}
    (fresh : FreshFrom first bindings) (index : Nat) (inside : index < environment.length) :
    (extendMatch first environment bindings).lookup (freshName (first + index)) =
      some (MeTTaData.encode environment[index].2) := by
  induction environment generalizing first bindings index with
  | nil => simp at inside
  | cons entry rest ih =>
      cases index with
      | zero =>
          simp only [extendMatch, Nat.add_zero, List.getElem_cons_zero]
          apply extendMatch_extends rest (fresh.assign (MeTTaData.encode entry.2))
          exact Mettapedia.Languages.MeTTa.HE.lookup_assign_of_lookup_none bindings
            (freshName first) (MeTTaData.encode entry.2) (fresh first (by omega))
      | succ index =>
          have bound : index < rest.length := by simpa using inside
          have next := ih (fresh.assign (MeTTaData.encode entry.2)) index bound
          simpa [extendMatch, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using next

/-- Read the first emitted occurrence of a source name through target bindings. -/
def lookupRenamed (names : Names) (bindings : Bindings) (name : String) : Option Atom :=
  (names.find? (fun entry => entry.1 == name)).bind fun entry =>
    match entry.2 with
    | .var target => bindings.lookup target
    | _ => none

private theorem lookupRenamed_namesForMatch (environment : Env) (first : Nat)
    (bindings : Bindings)
    (aligned : ∀ (index : Nat) (inside : index < environment.length),
      bindings.lookup (freshName (first + index)) =
        some (MeTTaData.encode environment[index].2)) (name : String) :
    lookupRenamed (namesForMatch first environment) bindings name =
      (environment.lookup name).map MeTTaData.encode := by
  induction environment generalizing first with
  | nil => rfl
  | cons entry rest ih =>
      rw [namesForMatch_cons]
      have head := aligned 0 (by simp)
      have tail : ∀ (index : Nat) (inside : index < rest.length),
          bindings.lookup (freshName (first + 1 + index)) =
            some (MeTTaData.encode rest[index].2) := by
        intro index inside
        have next := aligned (index + 1) (by simpa using inside)
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using next
      by_cases same : entry.1 = name
      · simpa [lookupRenamed, Env.lookup, same] using head
      · simpa [lookupRenamed, Env.lookup, same] using ih (first + 1) tail

/-- Exact variable lookup using the actual emitted name table. -/
theorem pattern_binding_lookup (source value : Term) (environment : Env)
    (matched : matchTerm source value = some environment) (first : Nat)
    (bindings : Bindings) (fresh : FreshFrom first bindings) (name : String) :
    lookupRenamed (pattern source first).1.2 (extendMatch first environment bindings) name =
      (environment.lookup name).map MeTTaData.encode := by
  rw [pattern_names_of_match source value environment matched first]
  exact lookupRenamed_namesForMatch environment first _
    (extendMatch_lookup_index environment fresh) name

theorem patterns_binding_lookup (source values : List Term) (environment : Env)
    (matched : matchTerms source values = some environment) (first : Nat)
    (bindings : Bindings) (fresh : FreshFrom first bindings) (name : String) :
    lookupRenamed (patterns source first).1.2 (extendMatch first environment bindings) name =
      (environment.lookup name).map MeTTaData.encode := by
  rw [patterns_names_of_match source values environment matched first]
  exact lookupRenamed_namesForMatch environment first _
    (extendMatch_lookup_index environment fresh) name

end Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit
