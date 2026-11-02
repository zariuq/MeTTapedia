import Mettapedia.GSLT.LanguageDef.ScopedABTApplication

/-!
# Partial application while retaining the captured context

A contextual object may have explicit parameters before an already captured
ambient context. Supplying a prefix of its parameters retains the remaining
parameters and the ambient variables. Arguments are not evaluated here.
They are syntax, substituted simultaneously with capture avoided.

This supplies an ordinary-programming operation in addition to complete
context substitution. It imposes no requirement that programmers explicitly
declare proof-rule dependency bounds.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.SignatureIndexedABT.ScopedApplication

variable {Head : Type}

def prefixEnvironment (arity : ℕ) (arguments : List (Term Head)) (i : ℕ) : Term Head :=
  if i < arguments.length then
    Term.renameMany (fun j => arity - arguments.length + j) (argumentAt arguments i)
  else if i < arity then .idx (i - arguments.length)
  else .idx (arity - arguments.length + (i - arity))

def applyPrefix (arity : ℕ) (arguments : List (Term Head)) (body : Term Head) : Term Head :=
  Term.substituteMany (prefixEnvironment arity arguments) body

theorem prefixEnvironment_outer (arity : ℕ) (arguments : List (Term Head))
    (count : arguments.length ≤ arity) (i : ℕ) :
    prefixEnvironment arity arguments (arity + i) = .idx (arity - arguments.length + i) := by
  have afterArguments : ¬arity + i < arguments.length := by omega
  have afterParameters : ¬arity + i < arity := by omega
  simp [prefixEnvironment, afterArguments, afterParameters]

theorem substitute_prefix_weaken (arity : ℕ) (arguments : List (Term Head))
    (count : arguments.length ≤ arity) (term : Term Head) :
    Term.substituteMany (prefixEnvironment arity arguments)
        (Term.renameMany (fun i => arity + i) term) =
      Term.renameMany (fun i => arity - arguments.length + i) term := by
  rw [Term.substituteMany_rename]
  have environment : (fun i => prefixEnvironment arity arguments (arity + i)) =
      (fun i => .idx (arity - arguments.length + i)) :=
    funext (prefixEnvironment_outer arity arguments count)
  rw [environment, Term.substituteMany_renaming]

theorem applyPrefix_supported {arity ambient : ℕ} (arguments : List (Term Head))
    (count : arguments.length ≤ arity)
    (argumentsScoped : ∀ arg ∈ arguments, Term.supportedAt ambient arg = true)
    (body : Term Head) (bodyScoped : Term.supportedAt (arity + ambient) body = true) :
    Term.supportedAt (arity - arguments.length + ambient) (applyPrefix arity arguments body) = true := by
  apply Term.substituteMany_supported (source := arity + ambient) _ body bodyScoped
  intro i inside
  unfold prefixEnvironment
  split
  · rename_i argumentIndex
    have argumentScoped : Term.supportedAt ambient (argumentAt arguments i) = true := by
      have selected : argumentAt arguments i = arguments[i] := by
        simp [argumentAt, List.getElem?_eq_getElem argumentIndex]
      rw [selected]
      exact argumentsScoped arguments[i] (List.getElem_mem argumentIndex)
    exact Term.renameMany_supported (by intro j available; omega) _ argumentScoped
  · split
    · simp only [Term.supportedAt, decide_eq_true_eq]
      omega
    · simp only [Term.supportedAt, decide_eq_true_eq]
      omega

theorem applyPrefix_empty (arity : ℕ) (body : Term Head) : applyPrefix arity [] body = body := by
  unfold applyPrefix
  have environment : prefixEnvironment arity ([] : List (Term Head)) = Term.idx := by
    funext i
    by_cases inside : i < arity <;> simp [prefixEnvironment, inside]
    omega
  rw [environment, Term.substituteMany_ids]

theorem argumentAt_append_left (first second : List (Term Head)) {i : ℕ}
    (inside : i < first.length) : argumentAt (first ++ second) i = argumentAt first i := by
  simp [argumentAt, List.getElem?_append, inside]

theorem argumentAt_append_right (first second : List (Term Head)) {i : ℕ}
    (afterFirst : first.length ≤ i) (inside : i < first.length + second.length) :
    argumentAt (first ++ second) i = argumentAt second (i - first.length) := by
  have outside : ¬i < first.length := by omega
  have secondIndex : i - first.length < second.length := by omega
  simp [argumentAt, List.getElem?_append, outside, List.getElem?_eq_getElem secondIndex]

theorem prefixEnvironment_comp (arity : ℕ) (first second : List (Term Head))
    (count : first.length + second.length ≤ arity) (i : ℕ) :
    Term.substituteMany (prefixEnvironment (arity - first.length) second)
        (prefixEnvironment arity first i) =
      prefixEnvironment arity (first ++ second) i := by
  have secondFits : second.length ≤ arity - first.length := by omega
  by_cases inFirst : i < first.length
  · have inCombined : i < (first ++ second).length := by simp only [List.length_append]; omega
    simp only [prefixEnvironment, inFirst, inCombined, ↓reduceIte]
    rw [substitute_prefix_weaken _ _ secondFits]
    rw [argumentAt_append_left first second inFirst]
    simp [Nat.sub_sub]
  · have afterFirst : first.length ≤ i := by omega
    by_cases inCombined : i < (first ++ second).length
    · have beforeArity : i < arity := by simp only [List.length_append] at inCombined; omega
      have inSecond : i - first.length < second.length := by
        simp only [List.length_append] at inCombined; omega
      simp only [prefixEnvironment, inFirst, beforeArity, inCombined, ↓reduceIte,
        Term.substituteMany_idx, inSecond]
      rw [argumentAt_append_right first second afterFirst (by simpa using inCombined)]
      simp [Nat.sub_sub]
    · have afterCombined : first.length + second.length ≤ i := by
        simp only [List.length_append] at inCombined; omega
      have outsideCombined : ¬i < first.length + second.length := by omega
      by_cases beforeArity : i < arity
      · have afterSecond : ¬i - first.length < second.length := by omega
        have beforeRemaining : i - first.length < arity - first.length := by omega
        simp [prefixEnvironment, inFirst, outsideCombined, beforeArity,
          Term.substituteMany_idx, afterSecond, beforeRemaining, Nat.sub_sub]
      · have afterArguments : ¬arity - first.length + (i - arity) < second.length := by omega
        have afterRemaining : ¬arity - first.length + (i - arity) < arity - first.length := by omega
        simp [prefixEnvironment, inFirst, outsideCombined, beforeArity,
          Term.substituteMany_idx, afterArguments, afterRemaining, Nat.sub_sub]

/-- Supplying arguments in stages gives exactly the same syntax as supplying
their concatenation. Captured ambient variables retain their meaning. -/
theorem applyPrefix_append (arity : ℕ) (first second : List (Term Head))
    (count : first.length + second.length ≤ arity) (body : Term Head) :
    applyPrefix (arity - first.length) second (applyPrefix arity first body) =
      applyPrefix arity (first ++ second) body := by
  unfold applyPrefix
  rw [Term.substituteMany_comp]
  congr 1
  exact funext (prefixEnvironment_comp arity first second count)

namespace PrefixControls

local instance : DecidableEq (Term ℕ) := fun a b =>
  decidable_of_iff (SingleSort.encode a = SingleSort.encode b)
    ⟨fun same => SingleSort.encode_injective same, congrArg SingleSort.encode⟩

def pair (a b : Term ℕ) : Term ℕ := .node 2 (.cons 0 a (.cons 0 b .nil))

theorem ordinary_partial_application_retains_its_argument :
    applyPrefix 2 [.node 7 .nil] (pair (.idx 0) (.idx 1)) = pair (.node 7 .nil) (.idx 0) := by decide

theorem partial_application_preserves_captured_ambient_variable :
    applyPrefix 2 [.idx 0] (pair (.idx 0) (.idx 2)) = pair (.idx 1) (.idx 1) := by decide

theorem completing_partial_application_avoids_capture :
    applyPrefix 1 [.node 8 .nil]
        (applyPrefix 2 [.idx 0] (pair (.idx 0) (.idx 1))) =
      pair (.idx 0) (.node 8 .nil) := by decide

end PrefixControls
end Mettapedia.GSLT.LanguageDef.SignatureIndexedABT.ScopedApplication
