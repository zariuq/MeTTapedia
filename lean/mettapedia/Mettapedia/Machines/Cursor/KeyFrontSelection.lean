import Mettapedia.Machines.Cursor.KeyFrontTerms

/-!
# Executable front pruning and the independent matching observation

The selector inspects the rigid prefix and stops at the first stored
variable. It does not decide unification or multiplicity. The source matching
relation is independently defined by a common substitution instance; pruning
then preserves its exact occurrence list, not merely the result set.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.KeyFrontSelection

open KeyFrontRanges KeyFrontCompleteness KeyFrontTerms
open TermPathPosting (Term subst)

def possible : Key → Key → Bool
  | [], _ => true
  | _ :: _, [] => false
  | token :: later, rowToken :: rowRest =>
      if kind rowToken = 1 then decide (1 < kind token)
      else if rowToken = token then possible later rowRest else false

theorem prefix_expansion_selected (environment : Nat → Key) (stem row : Key)
    (proper : Proper environment) (rigidStem : ∀ token ∈ stem, kind token ≠ 1)
    (prefixInImage : stem <+: expand environment row) : possible stem row = true := by
  induction stem generalizing row with
  | nil => rfl
  | cons token later ih =>
      cases row with
      | nil => simp [expand] at prefixInImage
      | cons rowToken rowRest =>
          have rigidToken := rigidStem token (by simp)
          by_cases rowVariable : kind rowToken = 1
          · obtain ⟨first, rest, envEq, positive⟩ := proper (ofLex rowToken).2
            have image : expand environment (rowToken :: rowRest) =
                first :: (rest ++ expand environment rowRest) := by
              simp only [expand, List.flatMap_cons, rowVariable, ↓reduceIte, envEq, List.cons_append]
            rw [image] at prefixInImage
            obtain ⟨tail, tailEq⟩ := prefixInImage
            have same : token = first := by
              have heads := congrArg List.head? tailEq
              simpa using heads
            have node : 1 < kind token := by rw [same] at rigidToken ⊢; omega
            simp [possible, rowVariable, node]
          · have image : expand environment (rowToken :: rowRest) =
                rowToken :: expand environment rowRest := by
              simp only [expand, List.flatMap_cons, rowVariable, ↓reduceIte, List.singleton_append]
            rw [image] at prefixInImage
            obtain ⟨tail, tailEq⟩ := prefixInImage
            have same : token = rowToken := by
              have heads := congrArg List.head? tailEq
              simpa using heads
            have remaining : later <+: expand environment rowRest :=
              ⟨tail, List.cons.inj (by simpa only [List.cons_append, same] using tailEq) |>.2⟩
            have selected := ih rowRest (fun item member => rigidStem item (by simp [member])) remaining
            simp [possible, rowVariable, same, selected]

theorem unifier_selected (queryEnvironment rowEnvironment : Nat → Term)
    (query row : Term) (stem : Key) (admittedFront : stem <+: front (encode query))
    (common : subst queryEnvironment query = subst rowEnvironment row) :
    possible stem (encode row) = true := by
  apply prefix_expansion_selected (fun name => encode (rowEnvironment name)) stem (encode row)
    (substitution_proper rowEnvironment)
  · intro token member
    exact front_rigid (encode query) token (admittedFront.subset member)
  · have prefixInImage := admittedFront.trans
      (front_expands_prefix (fun name => encode (queryEnvironment name)) (encode query))
    rw [← encode_subst, common, encode_subst] at prefixInImage
    exact prefixInImage

def Matches (query row : Term) : Prop :=
  ∃ queryEnvironment rowEnvironment,
    subst queryEnvironment query = subst rowEnvironment row

noncomputable def source (query : Term) (rows : List (Nat × Term)) : List (Nat × Term) := by
  classical
  exact rows.filter (fun row => decide (Matches query row.2))

noncomputable def indexed (query : Term) (stem : Key) (rows : List (Nat × Term)) :
    List (Nat × Term) :=
  source query (rows.filter (fun row => possible stem (encode row.2)))

/-- Matching remains the original independent relation after pruning. Row
IDs, duplicate payload occurrences, and source order are unchanged. -/
theorem indexed_exact (query : Term) (stem : Key) (rows : List (Nat × Term))
    (admittedFront : stem <+: front (encode query)) : indexed query stem rows = source query rows := by
  classical
  simp only [indexed, source, List.filter_filter]
  apply List.filter_congr
  intro row _
  by_cases hasMatch : Matches query row.2
  · obtain ⟨queryEnvironment, rowEnvironment, equal⟩ := hasMatch
    have selected := unifier_selected queryEnvironment rowEnvironment query row.2 stem admittedFront equal
    simp [selected, Matches, show ∃ queryEnvironment rowEnvironment,
      subst queryEnvironment query = subst rowEnvironment row.2 from ⟨_, _, equal⟩]
  · simp [hasMatch]

end Mettapedia.Machines.Cursor.KeyFrontSelection
