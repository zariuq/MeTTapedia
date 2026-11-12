import Mettapedia.Machines.Cursor.KeyFrontRanges

/-!
# Complete ground-front candidate selection

Substitution expands variable tokens and preserves every rigid token,
including expression boundaries. A genuine structural-term encoding must
commute with this expansion. The theorem below permits independent query and
stored-row substitutions. Any shorter rigid front remains sound, so a bounded
index may truncate a front rather than impose a limit on source terms.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.KeyFrontCompleteness

open KeyFrontRanges

def expand (environment : Nat → Key) (row : Key) : Key :=
  row.flatMap fun token => if kind token = 1 then environment (ofLex token).2 else [token]

theorem expand_append (environment : Nat → Key) (left right : Key) :
    expand environment (left ++ right) = expand environment left ++ expand environment right := by
  simp [expand]

theorem expand_rigid (environment : Nat → Key) (row : Key)
    (noVariable : ∀ token ∈ row, kind token ≠ 1) : expand environment row = row := by
  induction row with
  | nil => rfl
  | cons token rest ih =>
      have first := noVariable token (by simp)
      have later := ih (fun other member => noVariable other (by simp [member]))
      change (if kind token = 1 then environment (ofLex token).2 else [token]) ++
        expand environment rest = token :: rest
      rw [if_neg first, later]
      rfl

theorem front_expands_prefix (environment : Nat → Key) (row : Key) :
    front row <+: expand environment row := by
  induction row with
  | nil => exact List.prefix_refl _
  | cons token rest ih =>
      by_cases isVariable : kind token = 1
      · simp [front, isVariable]
      · obtain ⟨tail, equal⟩ := ih
        refine ⟨tail, ?_⟩
        simpa [front, expand, isVariable] using congrArg (token :: ·) equal

theorem front_decompose (row : Key) :
    front row = row ∨ ∃ name rest, row = front row ++ varToken name :: rest := by
  induction row with
  | nil => exact Or.inl rfl
  | cons token rest ih =>
      by_cases isVariable : kind token = 1
      · right
        refine ⟨(ofLex token).2, rest, ?_⟩
        have tokenEq : token = varToken (ofLex token).2 :=
          congrArg toLex (Prod.ext isVariable rfl)
        rw [front, if_pos isVariable]
        exact congrArg (· :: rest) tokenEq
      · rcases ih with whole | ⟨name, later, decomposed⟩
        · left; simp [front, isVariable, whole]
        · right
          refine ⟨name, later, ?_⟩
          simpa only [front, isVariable, ↓reduceIte, List.cons_append] using
            congrArg (token :: ·) decomposed

theorem prefix_cancel (stem left right : Key) :
    stem ++ left <+: stem ++ right ↔ left <+: right := by
  constructor
  · rintro ⟨tail, equal⟩
    refine ⟨tail, ?_⟩
    apply List.append_cancel_left (as := stem)
    simpa only [List.append_assoc] using equal
  · rintro ⟨tail, equal⟩
    exact ⟨tail, by simp [List.append_assoc, equal]⟩

/-- A variable's expansion starts at a term node, never at an expression's
closing delimiter. Variables may remain variables; groundness is not required. -/
def Proper (environment : Nat → Key) : Prop :=
  ∀ name, ∃ token rest, environment name = token :: rest ∧ 0 < kind token

def Candidate (stem row : Key) : Prop :=
  stem <+: row ∨ ∃ before token after,
    stem = before ++ token :: after ∧ 1 < kind token ∧ Band before row

/-- A full or truncated query front cannot lose a row with a common
substitution instance. Variable bands are candidates, not already answers. -/
theorem common_instance_candidate
    (queryEnvironment rowEnvironment : Nat → Key) (query row stem : Key)
    (proper : Proper rowEnvironment) (boundedFront : stem <+: front query)
    (same : expand queryEnvironment query = expand rowEnvironment row) :
    Candidate stem row := by
  have selected := boundedFront.trans (front_expands_prefix queryEnvironment query)
  rw [same] at selected
  rcases front_decompose row with closed | ⟨name, suffix, rowEq⟩
  · left
    have unchanged : expand rowEnvironment row = row := by
      apply expand_rigid
      simpa only [closed] using front_rigid row
    simpa only [unchanged] using selected
  · have noVariables := front_rigid row
    have unchanged := expand_rigid rowEnvironment (front row) noVariables
    have expanded : expand rowEnvironment row =
        front row ++ rowEnvironment name ++ expand rowEnvironment suffix := by
      conv => lhs; rw [rowEq]
      rw [expand_append, unchanged]
      change front row ++ (rowEnvironment name ++ expand rowEnvironment suffix) = _
      exact List.append_assoc _ _ _ |>.symm
    rw [expanded] at selected
    have commonStem : front row <+:
        front row ++ rowEnvironment name ++ expand rowEnvironment suffix :=
      ⟨rowEnvironment name ++ expand rowEnvironment suffix, (List.append_assoc _ _ _).symm⟩
    have relation : stem <+: front row ∨ front row <+: stem :=
      List.prefix_or_prefix_of_prefix selected commonStem
    rcases relation with before | after
    · left
      exact before.trans (front_prefix row)
    · obtain ⟨remaining, equation⟩ := after
      cases remaining with
      | nil =>
          left
          have stemEq : stem = front row := by simpa only [List.append_nil] using equation.symm
          simpa only [stemEq] using front_prefix row
      | cons token later =>
          obtain ⟨first, rest, envEq, positive⟩ := proper name
          have nextPrefix : token :: later <+:
              first :: (rest ++ expand rowEnvironment suffix) := by
            apply (prefix_cancel (front row) _ _).mp
            simpa only [equation, envEq, List.append_assoc, List.cons_append] using selected
          obtain ⟨tail, tailEq⟩ := nextPrefix
          have tokenEq : token = first := by
            have heads := congrArg List.head? tailEq
            simpa using heads
          have belongs : token ∈ stem := by
            rw [← equation]
            simp
          have rigidToken := front_rigid query token (boundedFront.subset belongs)
          have ground : 1 < kind token := by rw [tokenEq] at rigidToken ⊢; omega
          right
          exact ⟨front row, token, later, equation.symm, ground, name, suffix, rowEq⟩

/-- Any truncation of an already justified front is safe. This law does not
make the index's maximum front length a language restriction. -/
theorem truncated_candidate
    (queryEnvironment rowEnvironment : Nat → Key) (query row : Key) (limit : Nat)
    (proper : Proper rowEnvironment)
    (same : expand queryEnvironment query = expand rowEnvironment row) :
    Candidate ((front query).take limit) row :=
  common_instance_candidate queryEnvironment rowEnvironment query row _ proper
    (List.take_prefix limit (front query)) same

end Mettapedia.Machines.Cursor.KeyFrontCompleteness
