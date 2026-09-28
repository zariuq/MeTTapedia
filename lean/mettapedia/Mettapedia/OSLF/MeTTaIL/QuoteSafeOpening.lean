import Mettapedia.OSLF.MeTTaIL.ScopedPattern
import Mettapedia.OSLF.MeTTaIL.Substitution

/-!
# Opening a binder across a sealed quotation boundary

Opening a binder with a closed replacement preserves the quote-aware scope
judgment.  The quotation case is substantive: its body is checked at depth
zero, so the outer binder does not occur there and opening leaves it alone.
The proof covers every constructor of the shared raw pattern syntax.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.ScopedPattern

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution

/-- Removing one binder by opening with a closed replacement preserves
quote-aware scope, including under nested binders, explicit substitutions,
and collection elements. -/
theorem binderSafeAt_openBVar (quoteConstructor : String) (replacement : Pattern)
    (replacementSafe : binderSafeAt quoteConstructor 0 replacement = true) :
    ∀ (pattern : Pattern) (index : Nat),
      binderSafeAt quoteConstructor (index + 1) pattern = true →
      binderSafeAt quoteConstructor index
        (openBVar index replacement pattern) = true := by
  intro pattern
  induction pattern using Pattern.inductionOn with
  | hbvar boundIndex =>
      intro index safe
      by_cases hit : boundIndex = index
      · subst boundIndex
        simp only [openBVar, beq_self_eq_true, if_true]
        exact binderSafeAt_mono quoteConstructor replacementSafe
          (Nat.zero_le index)
      · have below : boundIndex < index := by
          have within : boundIndex < index + 1 := by
            simpa only [binderSafeAt, decide_eq_true_eq] using safe
          omega
        simp [openBVar, binderSafeAt, hit, below]
  | hfvar name =>
      intro index safe
      simp [openBVar, binderSafeAt]
  | happly constructor arguments ih =>
      intro index safe
      cases arguments with
      | nil =>
          simp [openBVar, binderSafeAt, binderSafeListAt]
      | cons first rest =>
          cases rest with
          | nil =>
              by_cases quoted : constructor = quoteConstructor
              · subst constructor
                have firstSafe : binderSafeAt quoteConstructor 0 first = true := by
                  simpa only [binderSafeAt, beq_self_eq_true, if_true] using safe
                have firstScope : first.isWellScopedAt 0 = true :=
                  isWellScopedAt_of_binderSafeAt quoteConstructor firstSafe
                have unchanged : openBVar index replacement first = first := by
                  apply openBVar_lc_at
                  rw [← isWellScopedAt_eq_lc_at]
                  exact isWellScopedAt_mono firstScope (Nat.zero_le index)
                simpa [openBVar, binderSafeAt, unchanged] using firstSafe
              · have firstSafe :
                    binderSafeAt quoteConstructor (index + 1) first = true := by
                  simpa [binderSafeAt, quoted, binderSafeListAt] using safe
                have opened := ih first (by simp) index firstSafe
                simpa [openBVar, binderSafeAt, quoted, binderSafeListAt]
                  using opened
          | cons second more =>
              have listSafe :
                  binderSafeListAt quoteConstructor (index + 1)
                    (first :: second :: more) = true := by
                simpa [binderSafeAt] using safe
              have each :=
                (binderSafeListAt_eq_true_iff quoteConstructor
                  (index + 1) (first :: second :: more)).mp listSafe
              have openedEach : ∀ part ∈ first :: second :: more,
                  binderSafeAt quoteConstructor index
                    (openBVar index replacement part) = true := by
                intro part member
                exact ih part member index (each part member)
              simp only [openBVar]
              change binderSafeListAt quoteConstructor index
                ((first :: second :: more).map
                  (openBVar index replacement)) = true
              rw [binderSafeListAt_eq_true_iff]
              intro part member
              obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
              exact openedEach original originalMember
  | hlambda name body ih =>
      intro index safe
      simpa [openBVar, binderSafeAt, Nat.add_assoc] using
        ih (index + 1) (by simpa [binderSafeAt, Nat.add_assoc] using safe)
  | hmultiLambda arity names body ih =>
      intro index safe
      have bodySafe :
          binderSafeAt quoteConstructor ((index + arity) + 1) body = true := by
        simpa [binderSafeAt, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using safe
      simpa [openBVar, binderSafeAt] using ih (index + arity) bodySafe
  | hsubst body substituted ihBody ihSubstituted =>
      intro index safe
      simp only [binderSafeAt, Bool.and_eq_true] at safe
      simp only [openBVar, binderSafeAt, Bool.and_eq_true]
      exact ⟨ihBody (index + 1)
          (by simpa [Nat.add_assoc] using safe.1),
        ihSubstituted index safe.2⟩
  | hcollection kind elements rest ih =>
      intro index safe
      have each :=
        (binderSafeListAt_eq_true_iff quoteConstructor
          (index + 1) elements).mp safe
      simp only [openBVar, binderSafeAt]
      rw [binderSafeListAt_eq_true_iff]
      intro part member
      obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
      exact ih original originalMember index (each original originalMember)

/-- Binder-eliminating substitution preserves literal quote scope when the
replacement is itself safe in the ambient context. The depth counts binders
between the eliminated variable and the current subterm. -/
theorem binderSafeAt_instantiateBVarAt (quoteConstructor : String)
    (replacement : Pattern) (ambient : Nat)
    (replacementSafe : binderSafeAt quoteConstructor ambient replacement = true) :
    ∀ (pattern : Pattern) (depth : Nat),
      binderSafeAt quoteConstructor (ambient + depth + 1) pattern = true →
      binderSafeAt quoteConstructor (ambient + depth)
        (instantiateBVarAt depth replacement pattern) = true := by
  intro pattern
  induction pattern using Pattern.inductionOn with
  | hbvar boundIndex =>
      intro depth safe
      have within : boundIndex < ambient + depth + 1 := by
        simpa only [binderSafeAt, decide_eq_true_eq] using safe
      by_cases below : boundIndex < depth
      · simp only [instantiateBVarAt, if_pos below, binderSafeAt,
          decide_eq_true_eq]
        omega
      · by_cases hit : boundIndex = depth
        · subst boundIndex
          simp only [instantiateBVarAt, Nat.lt_irrefl, if_false, if_true]
          exact binderSafeAt_liftBVars quoteConstructor replacementSafe
            (Nat.zero_le ambient)
        · have high : depth < boundIndex := by omega
          have reduced : boundIndex - 1 < ambient + depth := by omega
          simp [instantiateBVarAt, binderSafeAt, below, hit, reduced]
  | hfvar _ =>
      intro depth safe
      simp [instantiateBVarAt, binderSafeAt]
  | happly constructor arguments ih =>
      intro depth safe
      cases arguments with
      | nil =>
          simp [instantiateBVarAt, binderSafeAt, binderSafeListAt]
      | cons first rest =>
          cases rest with
          | nil =>
              by_cases quoted : constructor = quoteConstructor
              · subst constructor
                have firstSafe : binderSafeAt quoteConstructor 0 first = true := by
                  simpa only [binderSafeAt, beq_self_eq_true, if_true] using safe
                have firstScope : first.isWellScopedAt 0 = true :=
                  isWellScopedAt_of_binderSafeAt quoteConstructor firstSafe
                have unchanged : instantiateBVarAt depth replacement first = first :=
                  instantiateBVarAt_eq_self_of_isWellScopedAt
                    (isWellScopedAt_mono firstScope (Nat.zero_le depth))
                simpa [instantiateBVarAt, binderSafeAt, unchanged] using firstSafe
              · have firstSafe :
                    binderSafeAt quoteConstructor (ambient + depth + 1) first = true := by
                  simpa [binderSafeAt, quoted, binderSafeListAt] using safe
                have opened := ih first (by simp) depth firstSafe
                simpa [instantiateBVarAt, binderSafeAt, quoted, binderSafeListAt]
                  using opened
          | cons second more =>
              have listSafe :
                  binderSafeListAt quoteConstructor (ambient + depth + 1)
                    (first :: second :: more) = true := by
                simpa [binderSafeAt] using safe
              have each :=
                (binderSafeListAt_eq_true_iff quoteConstructor
                  (ambient + depth + 1) (first :: second :: more)).mp listSafe
              have openedEach : ∀ part ∈ first :: second :: more,
                  binderSafeAt quoteConstructor (ambient + depth)
                    (instantiateBVarAt depth replacement part) = true := by
                intro part member
                exact ih part member depth (each part member)
              simp only [instantiateBVarAt]
              change binderSafeListAt quoteConstructor (ambient + depth)
                ((first :: second :: more).map
                  (instantiateBVarAt depth replacement)) = true
              rw [binderSafeListAt_eq_true_iff]
              intro part member
              obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
              exact openedEach original originalMember
  | hlambda _ body ih =>
      intro depth safe
      simpa [instantiateBVarAt, binderSafeAt, Nat.add_assoc] using
        ih (depth + 1) (by simpa [binderSafeAt, Nat.add_assoc] using safe)
  | hmultiLambda arity _ body ih =>
      intro depth safe
      have bodySafe : binderSafeAt quoteConstructor
          (ambient + (depth + arity) + 1) body = true := by
        simpa [binderSafeAt, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using safe
      simpa [instantiateBVarAt, binderSafeAt, Nat.add_assoc] using
        ih (depth + arity) bodySafe
  | hsubst body nested ihBody ihNested =>
      intro depth safe
      simp only [binderSafeAt, Bool.and_eq_true] at safe
      simp only [instantiateBVarAt, binderSafeAt, Bool.and_eq_true]
      exact ⟨ihBody (depth + 1)
          (by simpa [Nat.add_assoc] using safe.1),
        ihNested depth safe.2⟩
  | hcollection _ elements _ ih =>
      intro depth safe
      have each :=
        (binderSafeListAt_eq_true_iff quoteConstructor
          (ambient + depth + 1) elements).mp safe
      simp only [instantiateBVarAt, binderSafeAt]
      rw [binderSafeListAt_eq_true_iff]
      intro part member
      obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
      exact ih original originalMember depth (each original originalMember)

/-- The ambient-context specialization of literal-safe binder elimination. -/
theorem binderSafeAt_instantiateBVar (quoteConstructor : String)
    (replacement : Pattern) (ambient : Nat)
    (replacementSafe : binderSafeAt quoteConstructor ambient replacement = true)
    (body : Pattern)
    (bodySafe : binderSafeAt quoteConstructor (ambient + 1) body = true) :
    binderSafeAt quoteConstructor ambient
      (instantiateBVar replacement body) = true := by
  simpa [instantiateBVar, Nat.add_zero] using
    binderSafeAt_instantiateBVarAt quoteConstructor replacement ambient
      replacementSafe body 0 (by simpa [Nat.add_zero] using bodySafe)

/-- Opening a name under a nested binder remains safe when the supplied
quoted process is closed. -/
theorem nested_quote_safe_opening :
    binderSafeAt "NQuote" 0
      (openBVar 0 (.apply "NQuote" [.apply "PZero" []])
        (.lambda none (.bvar 1))) = true := by
  exact binderSafeAt_openBVar "NQuote"
    (.apply "NQuote" [.apply "PZero" []]) (by decide +kernel)
    (.lambda none (.bvar 1)) 0 (by decide +kernel)

/-- Closedness of the replacement is necessary: raw opening with a free
bound index can leave the resulting process outside the closed carrier. -/
theorem open_replacement_breaks_closedness :
    binderSafeAt "NQuote" 1 (.bvar 0) = true ∧
    binderSafeAt "NQuote" 0 (.bvar 0) = false ∧
    binderSafeAt "NQuote" 0
      (openBVar 0 (.bvar 0) (.bvar 0)) = false := by
  decide +kernel

/-- Ordinary local scope does not seal a quotation from an outer binder. -/
theorem ordinary_scope_allows_quote_escape :
    (Pattern.apply "NQuote" [.bvar 0]).isWellScopedAt 1 = true ∧
    binderSafeAt "NQuote" 1 (.apply "NQuote" [.bvar 0]) = false := by
  decide +kernel

#print axioms binderSafeAt_openBVar
#print axioms nested_quote_safe_opening
#print axioms open_replacement_breaks_closedness
#print axioms ordinary_scope_allows_quote_escape

end Mettapedia.OSLF.MeTTaIL.ScopedPattern
