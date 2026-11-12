import Mettapedia.Machines.Cursor.KeyFrontSelection

/-!
# Scalar categories and structural terms in a front-index profile

The supplied scalar encoding may use numbers, strings and other rigid
categories. Empty and nonempty expressions retain their distinct marker
roles. Candidate completeness needs rigid kinds above the variable kind;
order-faithful native marshalling is a separate adapter obligation.

Scalar ranks need not be injective for this refutation interface: collisions
may retain extra candidates, while the original matcher still decides answers.
Likewise, changing variable-token payloads preserves fronts and selection,
but does not license collapsing distinct variables in the source matcher.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.KeyFrontScalarProfile

open KeyFrontRanges KeyFrontCompleteness
open TermPathPosting (Term subst)

structure Profile where
  leaf : Nat → Token
  emptyNode : Token
  compoundNode : Token
  leaf_rigid : ∀ value, 1 < kind (leaf value)
  empty_rigid : 1 < kind emptyNode
  compound_rigid : 1 < kind compoundNode

/-- Constructor order is separate from the conditions sufficient for safe
candidate pruning, so those conditions do not impose one language's order. -/
def ConstructorOrdered (profile : Profile) : Prop :=
  profile.emptyNode < profile.compoundNode ∧
    ∀ value, profile.leaf value < profile.compoundNode

@[simp] theorem leaf_not_variable (profile : Profile) (value : Nat) :
    kind (profile.leaf value) ≠ 1 := by have := profile.leaf_rigid value; omega

@[simp] theorem empty_not_variable (profile : Profile) :
    kind profile.emptyNode ≠ 1 := by have := profile.empty_rigid; omega

@[simp] theorem compound_not_variable (profile : Profile) :
    kind profile.compoundNode ≠ 1 := by have := profile.compound_rigid; omega

@[simp] theorem close_not_variable : kind close ≠ 1 := by decide

def encode (profile : Profile) : Term → Key
  | .key value => [profile.leaf value]
  | .var name => [varToken name]
  | .node [] => [profile.emptyNode]
  | .node (first :: later) => profile.compoundNode ::
      (encode profile first ++ later.flatMap (encode profile) ++ [close])

theorem encoding_nonempty (profile : Profile) (term : Term) : ∃ first rest,
    encode profile term = first :: rest ∧ 0 < kind first := by
  cases term with
  | key value => exact ⟨profile.leaf value, [], by simp [encode], by have := profile.leaf_rigid value; omega⟩
  | var name => exact ⟨varToken name, [], by simp [encode], by simp [kind, varToken]⟩
  | node children =>
      cases children with
      | nil => exact ⟨profile.emptyNode, [], by simp [encode], by have := profile.empty_rigid; omega⟩
      | cons first later =>
          exact ⟨profile.compoundNode, encode profile first ++ later.flatMap (encode profile) ++ [close],
            by simp [encode], by have := profile.compound_rigid; omega⟩

theorem substitution_proper (profile : Profile) (environment : Nat → Term) :
    Proper (fun name => encode profile (environment name)) :=
  fun name => encoding_nonempty profile (environment name)

theorem encode_subst (profile : Profile) (environment : Nat → Term) (term : Term) :
    encode profile (subst environment term) =
      expand (fun name => encode profile (environment name)) (encode profile term) := by
  cases term with
  | key value => simp [subst, encode, expand]
  | var name => simp [subst, encode, expand, varToken, kind]
  | node children =>
      have ih : ∀ child ∈ children,
          encode profile (subst environment child) =
            expand (fun name => encode profile (environment name)) (encode profile child) := by
        intro child member
        exact encode_subst profile environment child
      cases children with
      | nil => simp [subst, encode, expand]
      | cons first later =>
          have firstIH := ih first (by simp)
          have tailIH : (later.map (subst environment)).flatMap (encode profile) =
              expand (fun name => encode profile (environment name)) (later.flatMap (encode profile)) := by
            have tailProof : ∀ tail : List Term, (∀ child ∈ tail, child ∈ first :: later) →
                (tail.map (subst environment)).flatMap (encode profile) =
                  expand (fun name => encode profile (environment name)) (tail.flatMap (encode profile)) := by
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
          simp [expand]
termination_by sizeOf term
decreasing_by
  exact (List.sizeOf_lt_of_mem member).trans (by simp)

theorem unifier_not_refuted (profile : Profile) (queryEnvironment rowEnvironment : Nat → Term)
    (query row : Term) (stem : Key)
    (boundedFront : stem <+: front (encode profile query))
    (common : subst queryEnvironment query = subst rowEnvironment row) :
    Candidate stem (encode profile row) := by
  apply common_instance_candidate
    (fun name => encode profile (queryEnvironment name)) (fun name => encode profile (rowEnvironment name))
    (encode profile query) (encode profile row) stem (substitution_proper profile rowEnvironment) boundedFront
  rw [← encode_subst, ← encode_subst, common]

theorem unifier_selected (profile : Profile) (queryEnvironment rowEnvironment : Nat → Term)
    (query row : Term) (stem : Key)
    (boundedFront : stem <+: front (encode profile query))
    (common : subst queryEnvironment query = subst rowEnvironment row) :
    KeyFrontSelection.possible stem (encode profile row) = true := by
  apply KeyFrontSelection.prefix_expansion_selected
    (fun name => encode profile (rowEnvironment name)) stem (encode profile row)
    (substitution_proper profile rowEnvironment)
  · intro token member
    exact front_rigid (encode profile query) token (boundedFront.subset member)
  · have prefixed := boundedFront.trans
      (front_expands_prefix (fun name => encode profile (queryEnvironment name)) (encode profile query))
    rw [← encode_subst, common, encode_subst] at prefixed
    exact prefixed

noncomputable def indexed (profile : Profile) (query : Term) (stem : Key)
    (rows : List (Nat × Term)) : List (Nat × Term) :=
  KeyFrontSelection.source query
    (rows.filter (fun row => KeyFrontSelection.possible stem (encode profile row.2)))

/-- Even colliding scalar ranks preserve the original matcher's ordered
occurrences. Only the prefilter sees the profile; source terms are unchanged. -/
theorem indexed_exact (profile : Profile) (query : Term) (stem : Key)
    (rows : List (Nat × Term)) (boundedFront : stem <+: front (encode profile query)) :
    indexed profile query stem rows = KeyFrontSelection.source query rows := by
  classical
  simp only [indexed, KeyFrontSelection.source, List.filter_filter]
  apply List.filter_congr
  intro row _
  by_cases matched : KeyFrontSelection.Matches query row.2
  · obtain ⟨queryEnvironment, rowEnvironment, equal⟩ := matched
    have selected := unifier_selected profile queryEnvironment rowEnvironment
      query row.2 stem boundedFront equal
    simp [selected, KeyFrontSelection.Matches,
      show ∃ queryEnvironment rowEnvironment,
        subst queryEnvironment query = subst rowEnvironment row.2 from ⟨_, _, equal⟩]
  · simp [matched]

/-- Category membership is an admitted adapter property, not a requirement
that every source scalar already have a finite order rank. -/
def CScalarCategories (category : Nat → Nat) : Prop :=
  ∀ value, category value = 2 ∨ category value = 3 ∨ category value = 5

def cStyle (category rank : Nat → Nat) (admitted : CScalarCategories category) : Profile where
  leaf value := toLex (category value, rank value)
  emptyNode := toLex (4, 0)
  compoundNode := toLex (6, 0)
  leaf_rigid value := by
    have classified := admitted value
    change 1 < category value
    rcases classified with number | string | other <;> omega
  empty_rigid := by decide
  compound_rigid := by decide

theorem cStyle_constructor_ordered (category rank : Nat → Nat)
    (admitted : CScalarCategories category) : ConstructorOrdered (cStyle category rank admitted) := by
  constructor
  · apply (Prod.Lex.lt_iff).mpr
    left
    change (4 : Nat) < 6
    decide
  · intro value
    apply (Prod.Lex.lt_iff).mpr
    left
    change category value < 6
    have classified := admitted value
    rcases classified with number | string | other <;> omega

def renameToken (rename : Nat → Nat) (token : Token) : Token :=
  if kind token = 1 then varToken (rename (ofLex token).2) else token

def renameVariables (rename : Nat → Nat) (row : Key) : Key := row.map (renameToken rename)

theorem renamed_kind (rename : Nat → Nat) (token : Token) :
    kind (renameToken rename token) = kind token := by
  by_cases isVariable : kind token = 1
  · rw [renameToken, if_pos isVariable]
    change (1 : Nat) = kind token
    exact isVariable.symm
  · rw [renameToken, if_neg isVariable]

/-- Variable payload ranks are absent from the ground front. Renaming need
not be injective for this indexing-only observation. -/
theorem front_renamed (rename : Nat → Nat) (row : Key) :
    front (renameVariables rename row) = front row := by
  induction row with
  | nil => rfl
  | cons first later ih =>
      change front (renameToken rename first :: renameVariables rename later) = front (first :: later)
      by_cases isVariable : kind first = 1
      · simp only [front, renamed_kind, isVariable, ↓reduceIte]
      · have unchanged : renameToken rename first = first := by simp [renameToken, isVariable]
        simp only [unchanged, front, isVariable, ↓reduceIte]
        exact congrArg (first :: ·) ih

theorem possible_renamed (rename : Nat → Nat) (stem row : Key) :
    KeyFrontSelection.possible stem (renameVariables rename row) =
      KeyFrontSelection.possible stem row := by
  induction stem generalizing row with
  | nil => rfl
  | cons first later ih =>
      cases row with
      | nil => rfl
      | cons rowHead rowTail =>
          change KeyFrontSelection.possible (first :: later)
            (renameToken rename rowHead :: renameVariables rename rowTail) = _
          by_cases isVariable : kind rowHead = 1
          · simp only [KeyFrontSelection.possible, renamed_kind, isVariable, ↓reduceIte]
          · have unchanged : renameToken rename rowHead = rowHead := by simp [renameToken, isVariable]
            simp only [unchanged, KeyFrontSelection.possible, isVariable, ↓reduceIte]
            by_cases same : rowHead = first
            · simpa only [same, ↓reduceIte] using ih rowTail
            · simp [same]

theorem selection_renamed (queryRename rowRename : Nat → Nat) (query row : Key) :
    KeyFrontSelection.possible (front (renameVariables queryRename query))
        (renameVariables rowRename row) = KeyFrontSelection.possible (front query) row := by
  rw [front_renamed, possible_renamed]

def colliding : Profile := cStyle (fun _ => 5) (fun _ => 0) (fun _ => Or.inr (Or.inr rfl))

example : encode colliding (.key 10) = encode colliding (.key 20) := by
  simp [encode, colliding, cStyle]

/-- Scalar collisions can be extra candidates; the original structural
matcher still distinguishes them. -/
example (left right : Nat → Term) : subst left (.key 10) ≠ subst right (.key 20) := by
  simp [subst]

example : KeyFrontSelection.possible (front (encode colliding (.key 10)))
    (encode colliding (.key 20)) = true := by
  simp [encode, colliding, cStyle, KeyFrontSelection.possible, front, kind]

example : front (encode colliding (.node [.key 10, .var 4, .key 20])) =
    [toLex (6, 0), toLex (5, 0)] := by
  simp [encode, colliding, cStyle, front, kind, varToken]

example : encode colliding (.node []) = [toLex (4, 0)] := by
  simp [encode, colliding, cStyle]

example : renameVariables (fun _ => 0) [varToken 1, varToken 2] =
    [varToken 0, varToken 0] := rfl

/-- Source-variable collapse changes matching even though token-front
selection is insensitive to those payloads. -/
example : ∃ environment : Nat → Term,
    subst environment (.node [.var 0, .var 1]) = .node [.key 3, .key 4] := by
  refine ⟨fun name => if name = 0 then .key 3 else .key 4, ?_⟩
  simp [subst]

example : ¬ ∃ environment : Nat → Term,
    subst environment (.node [.var 0, .var 0]) = .node [.key 3, .key 4] := by
  rintro ⟨environment, equal⟩
  have both : environment 0 = .key 3 ∧ environment 0 = .key 4 := by
    simpa only [subst, List.map_cons, List.map_nil, Term.node.injEq, List.cons.injEq,
      List.nil_eq, and_true] using equal
  have impossible := both.1.symm.trans both.2
  cases impossible

end Mettapedia.Machines.Cursor.KeyFrontScalarProfile
