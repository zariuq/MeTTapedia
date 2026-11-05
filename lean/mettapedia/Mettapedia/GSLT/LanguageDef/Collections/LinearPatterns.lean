import Mettapedia.GSLT.LanguageDef.Collections.ElementPatterns

/-!
# Exact regular erasure of linear sequence patterns

Element and sequence variables have separate namespaces. When each variable
occurs at most once, matching the erased regular expression is equivalent to
the existing finite matcher returning a partial assignment. This statement
works even over an empty alphabet. The total-assignment corollary explicitly
requires a nonempty alphabet because total assignments also cover unused
element variables.
-/

set_option autoImplicit false

open scoped Computability

namespace Mettapedia.GSLT.LanguageDef.Collections.LinearPatterns

open Mettapedia.Computability.RegularLanguages
open Mettapedia.Algebra.Collections.SequencePatterns
open ElementPatterns (erase listMatch listMatch_iff mem_any_star)

universe u v w
variable {A : Type u} {E : Type v} {X : Type w}

def elemVars : List (Item A E X) → List E
  | [] => []
  | .elem name :: rest => name :: elemVars rest
  | _ :: rest => elemVars rest

def seqVars : List (Item A E X) → List X
  | [] => []
  | .seq name :: rest => name :: seqVars rest
  | _ :: rest => seqVars rest

/-- Each variable used by the pattern occurs once in its own namespace. -/
def Linear (pattern : List (Item A E X)) : Prop := (elemVars pattern).Nodup ∧ (seqVars pattern).Nodup

instance [DecidableEq E] [DecidableEq X] (pattern : List (Item A E X)) : Decidable (Linear pattern) := by
  unfold Linear
  infer_instance

/-- The variables still to be visited have no incoming captures. -/
def Unbound (pattern : List (Item A E X)) (bindings : Partial A E X) : Prop :=
  (∀ name ∈ elemVars pattern, bindings.elem name = none) ∧
    (∀ name ∈ seqVars pattern, bindings.seq name = none)

theorem empty_unbound (pattern : List (Item A E X)) : Unbound pattern Partial.empty :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

variable [DecidableEq A] [DecidableEq E] [DecidableEq X]

/-- Successful finite matching implies erased-language membership without
assuming that a total assignment of every element-variable name exists. -/
theorem matchFrom_mem_erase :
    ∀ (pattern : List (Item A E X)) (subject : List A) (before after : Partial A E X),
      after ∈ matchFrom pattern subject before → subject ∈ language (erase pattern)
  | [], [], _, _, _ => by simp [erase]
  | [], _ :: _, _, _, found => by simp [matchFrom] at found
  | .lit _ :: _, [], _, _, found => by simp [matchFrom] at found
  | .lit a :: pattern, b :: rest, before, after, found => by
      simp only [matchFrom] at found
      split_ifs at found with same
      · subst b
        rw [erase, language_mul, Language.mem_mul]
        exact ⟨[a], Set.mem_singleton _, rest, matchFrom_mem_erase pattern rest before after found, rfl⟩
      · simp at found
  | .elem _ :: _, [], _, _, found => by simp [matchFrom] at found
  | .elem name :: pattern, a :: rest, before, after, found => by
      have tail : rest ∈ language (erase pattern) := by
        simp only [matchFrom] at found
        split at found
        · split_ifs at found
          · exact matchFrom_mem_erase pattern rest before after found
          · simp at found
        · exact matchFrom_mem_erase pattern rest (before.setElem name a) after found
      rw [erase, language_mul, Language.mem_mul]
      exact ⟨[a], ⟨a, rfl⟩, rest, tail, rfl⟩
  | .seq name :: pattern, subject, before, after, found => by
      simp only [matchFrom] at found
      split at found
      · rename_i leading bound
        split_ifs at found with isPrefix
        · have tail := matchFrom_mem_erase pattern (subject.drop leading.length) before after found
          rw [erase, language_mul, Language.mem_mul, language_star]
          refine ⟨leading, mem_any_star leading, subject.drop leading.length, tail, ?_⟩
          obtain ⟨suffix, rfl⟩ := isPrefix
          simp
        · simp at found
      · obtain ⟨length, _bounded, found⟩ := List.mem_flatMap.mp found
        rw [erase, language_mul, Language.mem_mul, language_star]
        exact ⟨subject.take length, mem_any_star _, subject.drop length,
          matchFrom_mem_erase pattern _ (before.setSeq name (subject.take length)) after found,
          List.take_append_drop length subject⟩

/-- Regular splits construct actual partial matcher answers. Linearity makes
each newly captured name irrelevant to the remaining unbound suffix. -/
theorem mem_erase_matchFrom :
    ∀ (pattern : List (Item A E X)) (subject : List A) (before : Partial A E X),
      Linear pattern → Unbound pattern before → subject ∈ language (erase pattern) →
        ∃ after, after ∈ matchFrom pattern subject before
  | [], subject, before, _linear, _unbound, member => by
      have empty : subject = [] := by simpa [erase] using member
      subst subject
      exact ⟨before, by simp [matchFrom]⟩
  | .lit a :: pattern, subject, before, linear, unbound, member => by
      rw [erase, language_mul, Language.mem_mul] at member
      obtain ⟨leading, leadingMember, suffix, suffixMember, same⟩ := member
      have leadingEq : leading = [a] := leadingMember
      subst leading
      subst subject
      obtain ⟨after, found⟩ := mem_erase_matchFrom pattern suffix before linear unbound suffixMember
      exact ⟨after, by simpa [matchFrom] using found⟩
  | .elem name :: pattern, subject, before, linear, unbound, member => by
      rw [erase, language_mul, Language.mem_mul] at member
      obtain ⟨leading, ⟨a, leadingEq⟩, suffix, suffixMember, same⟩ := member
      subst leading
      subst subject
      have distinct := List.nodup_cons.mp linear.1
      have restLinear : Linear pattern := ⟨distinct.2, linear.2⟩
      have fresh : before.elem name = none := unbound.1 name List.mem_cons_self
      have restUnbound : Unbound pattern (before.setElem name a) := by
        constructor
        · intro other present
          have apart : other ≠ name := by rintro rfl; exact distinct.1 present
          simpa [Partial.setElem, Function.update_of_ne apart] using unbound.1 other (List.mem_cons_of_mem _ present)
        · intro other present
          exact unbound.2 other present
      obtain ⟨after, found⟩ := mem_erase_matchFrom pattern suffix (before.setElem name a) restLinear restUnbound suffixMember
      exact ⟨after, by simpa [matchFrom, fresh] using found⟩
  | .seq name :: pattern, subject, before, linear, unbound, member => by
      rw [erase, language_mul, Language.mem_mul] at member
      obtain ⟨leading, _leadingMember, suffix, suffixMember, same⟩ := member
      subst subject
      have distinct := List.nodup_cons.mp linear.2
      have restLinear : Linear pattern := ⟨linear.1, distinct.2⟩
      have fresh : before.seq name = none := unbound.2 name List.mem_cons_self
      have restUnbound : Unbound pattern (before.setSeq name leading) := by
        constructor
        · intro other present
          exact unbound.1 other present
        · intro other present
          have apart : other ≠ name := by rintro rfl; exact distinct.1 present
          simpa [Partial.setSeq, Function.update_of_ne apart] using unbound.2 other (List.mem_cons_of_mem _ present)
      obtain ⟨after, found⟩ := mem_erase_matchFrom pattern suffix (before.setSeq name leading) restLinear restUnbound suffixMember
      refine ⟨after, ?_⟩
      simp only [matchFrom, fresh]
      apply List.mem_flatMap.mpr
      refine ⟨leading.length, ?_, ?_⟩
      · simp only [List.mem_range, List.length_append]
        omega
      · simpa only [List.drop_left, List.take_left] using found

theorem listMatch_iff_exists_match (pattern : List (Item A E X)) (linear : Linear pattern) (subject : List A) :
    listMatch (erase pattern) subject = true ↔ ∃ bindings, bindings ∈ matchFrom pattern subject Partial.empty := by
  rw [listMatch_iff]
  exact ⟨mem_erase_matchFrom pattern subject Partial.empty linear (empty_unbound pattern),
    fun ⟨bindings, found⟩ => matchFrom_mem_erase pattern subject Partial.empty bindings found⟩

theorem listMatch_iff_matchFrom_ne_nil (pattern : List (Item A E X)) (linear : Linear pattern) (subject : List A) :
    listMatch (erase pattern) subject = true ↔ matchFrom pattern subject Partial.empty ≠ [] := by
  rw [listMatch_iff_exists_match pattern linear subject]
  constructor
  · rintro ⟨bindings, found⟩ empty
    rw [empty] at found
    cases found
  · exact List.exists_mem_of_ne_nil _

/-- Total assignments also cover unused names, so their existence needs an
inhabitant of the element alphabet. The matcher equivalence above does not. -/
theorem listMatch_iff_total_instance [Nonempty A] (pattern : List (Item A E X))
    (linear : Linear pattern) (subject : List A) :
    listMatch (erase pattern) subject = true ↔ ∃ assignment : Assignment A E X, instantiate assignment pattern = subject := by
  classical
  constructor
  · intro accepted
    obtain ⟨bindings, found⟩ := (listMatch_iff_exists_match pattern linear subject).mp accepted
    let fallback : A := Classical.choice (inferInstance : Nonempty A)
    let assignment : Assignment A E X :=
      ⟨fun name => (bindings.elem name).getD fallback, fun name => (bindings.seq name).getD []⟩
    have agrees : Agrees bindings assignment := by
      constructor
      · intro name value bound
        simp [assignment, bound]
      · intro name value bound
        simp [assignment, bound]
    exact ⟨assignment, (matchFrom_sound pattern subject Partial.empty bindings found).2 assignment agrees⟩
  · rintro ⟨assignment, rfl⟩
    exact (listMatch_iff _ _).mpr (ElementPatterns.instantiate_mem_erase assignment pattern)

namespace Controls

def mixed : List (Item Nat Nat Nat) := [.seq 0, .elem 0, .lit 3, .seq 1]

theorem separate_namespaces_are_linear : Linear mixed := by decide

theorem actual_mixed_captures :
    (matchFrom mixed [7, 8, 3, 9] Partial.empty).map
      (fun bindings => (bindings.seq 0, bindings.elem 0, bindings.seq 1)) =
      [(some [7], some 8, some [9])] := by decide

theorem repeated_sequence_rejects_erasure_converse :
    ¬ Linear ([.seq 0, .seq 0] : List (Item Nat Nat Nat)) ∧
      listMatch (erase ([.seq 0, .seq 0] : List (Item Nat Nat Nat))) [1, 2] = true ∧
      matchFrom [.seq 0, .seq 0] [1, 2] (Partial.empty : Partial Nat Nat Nat) = [] := by
  obtain ⟨rejected, accepted⟩ := ElementPatterns.Controls.repeated_variable_not_regular_reading
  exact ⟨by decide, (listMatch_iff _ _).mpr accepted, rejected⟩

/-- Even with unused element-variable names, an empty alphabet still admits
the empty sequence capture. There is no corresponding total assignment. -/
theorem empty_alphabet_partial_match :
    listMatch (erase ([.seq 0] : List (Item Empty Unit Nat))) [] = true ∧
      matchFrom [.seq 0] [] (Partial.empty : Partial Empty Unit Nat) ≠ [] := by
  constructor
  · decide
  · decide

theorem empty_alphabet_has_no_total_assignment : ¬ Nonempty (Assignment Empty Unit Nat) := by
  rintro ⟨assignment⟩
  exact Empty.elim (assignment.elem ())

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.LinearPatterns

#print axioms Mettapedia.GSLT.LanguageDef.Collections.LinearPatterns.listMatch_iff_matchFrom_ne_nil
#print axioms Mettapedia.GSLT.LanguageDef.Collections.LinearPatterns.listMatch_iff_total_instance
