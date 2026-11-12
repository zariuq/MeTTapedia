import Mettapedia.Machines.Cursor.KeyFrontCompleteness
import Mettapedia.Machines.Cursor.TermPathPosting

/-!
# Ordinary structural terms inhabit the front-range interface

The existing structural unification terms are encoded with explicit closing
delimiters. Empty expressions have their own rigid token. Substituting a term
commutes with token expansion, so the common-instance candidate theorem is
earned for structural terms rather than assumed of a native matcher.

Rigid scalar ranks here are natural labels. A dialect adapter must separately
preserve its admitted scalar order and stop fronts at non-identity equality.
This does not verify the C term-universe encoding or alpha-normalization.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.KeyFrontTerms

open KeyFrontRanges KeyFrontCompleteness
open TermPathPosting (Term subst)

def encode : Term → Key
  | .key value => [rigid (value + 1)]
  | .var name => [varToken name]
  | .node [] => [rigid 0]
  | .node (first :: later) => compound ::
      (encode first ++ later.flatMap encode ++ [close])

theorem encoding_nonempty (term : Term) : ∃ first rest,
    encode term = first :: rest ∧ 0 < kind first := by
  cases term with
  | key value => exact ⟨rigid (value + 1), [], by simp [encode], by simp [kind, rigid]⟩
  | var name => exact ⟨varToken name, [], by simp [encode], by simp [kind, varToken]⟩
  | node children =>
      cases children with
      | nil => exact ⟨rigid 0, [], by simp [encode], by simp [kind, rigid]⟩
      | cons first later => exact ⟨compound,
          encode first ++ later.flatMap encode ++ [close], by simp [encode], by simp [kind, compound]⟩

theorem substitution_proper (environment : Nat → Term) :
    Proper (fun name => encode (environment name)) := fun name => encoding_nonempty (environment name)

theorem encode_subst (environment : Nat → Term) (term : Term) :
    encode (subst environment term) =
      expand (fun name => encode (environment name)) (encode term) := by
  cases term with
  | key value => simp [subst, encode, expand, rigid, kind]
  | var name => simp [subst, encode, expand, varToken, kind]
  | node children =>
      have ih : ∀ child ∈ children,
          encode (subst environment child) =
            expand (fun name => encode (environment name)) (encode child) := by
        intro child member
        exact encode_subst environment child
      cases children with
      | nil => simp [subst, encode, expand, rigid, kind]
      | cons first later =>
          have firstIH := ih first (by simp)
          have tailIH : (later.map (subst environment)).flatMap encode =
              expand (fun name => encode (environment name)) (later.flatMap encode) := by
            have tailProof : ∀ tail : List Term, (∀ child ∈ tail, child ∈ first :: later) →
                (tail.map (subst environment)).flatMap encode =
                  expand (fun name => encode (environment name)) (tail.flatMap encode) := by
              intro tail
              induction tail with
              | nil => intro _; rfl
              | cons child tail tailIH =>
                intro included
                have childIH := ih child (included child (by simp))
                simp only [List.map_cons, List.flatMap_cons, childIH, expand_append]
                exact congrArg (_ ++ ·) (tailIH (fun item member => included item (by simp [member])))
            exact tailProof later (fun child member => by simp [member])
          simp only [subst, List.map_cons, encode, firstIH, tailIH]
          simp [expand, compound, close, kind]
termination_by sizeOf term
decreasing_by
  exact (List.sizeOf_lt_of_mem member).trans (by simp)

theorem unifier_not_refuted (queryEnvironment rowEnvironment : Nat → Term)
    (query row : Term) (stem : Key)
    (boundedFront : stem <+: front (encode query))
    (common : subst queryEnvironment query = subst rowEnvironment row) :
    Candidate stem (encode row) := by
  apply common_instance_candidate
    (fun name => encode (queryEnvironment name)) (fun name => encode (rowEnvironment name))
    (encode query) (encode row) stem (substitution_proper rowEnvironment) boundedFront
  rw [← encode_subst, ← encode_subst, common]

end Mettapedia.Machines.Cursor.KeyFrontTerms
