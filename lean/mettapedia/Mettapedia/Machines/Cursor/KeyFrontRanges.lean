import Mathlib.Data.List.Lex
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic

/-!
# Ordered ground-front ranges

The geometry of a rigid stem and its first-varToken bands is independent
of a tree or array index. Keys retain closing delimiters: a preorder list of
node labels alone does not determine the expression boundaries. Tokens order
closing delimiters before variables, and variables before rigid nodes.

The token model is an index interface, not the C term-universe encoding.
Native numeric equality and private values must stop a rigid front when its
identity/order interpretation is unavailable. Candidate ranges are a sound
overapproximation; the original matcher still decides an answer.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.KeyFrontRanges

abbrev Token := Nat ×ₗ Nat
abbrev Key := List Token

def close : Token := toLex (0, 0)
def varToken (name : Nat) : Token := toLex (1, name)
def rigid (value : Nat) : Token := toLex (2, value)
def compound : Token := toLex (3, 0)
def kind (token : Token) : Nat := (ofLex token).1

theorem cons_le (a b : Token) (left right : Key) :
    a :: left ≤ b :: right ↔ a < b ∨ a = b ∧ left ≤ right := by
  simp only [le_iff_lt_or_eq]
  change (List.Lex (· < ·) (a :: left) (b :: right) ∨ a :: left = b :: right) ↔ _
  rw [List.cons_lex_cons_iff]
  simp only [List.cons.injEq]
  change (a < b ∨ a = b ∧ List.Lex (· < ·) left right) ∨ a = b ∧ left = right ↔ _
  tauto

/-- A stem class is convex in lexicographic key order. It can therefore
be obtained by one lower and one upper search in any faithful sorted index. -/
theorem prefix_convex (stem left middle right : Key)
    (leftPrefix : stem <+: left) (rightPrefix : stem <+: right)
    (lower : left ≤ middle) (upper : middle ≤ right) : stem <+: middle := by
  induction stem generalizing left middle right with
  | nil => simp
  | cons first stem ih =>
      obtain ⟨leftRest, rfl⟩ := leftPrefix
      obtain ⟨rightRest, rfl⟩ := rightPrefix
      cases middle with
      | nil => exact False.elim ((not_le_of_gt
          (show ([] : Key) < first :: (stem ++ leftRest) from List.Lex.nil)) lower)
      | cons next rest =>
          have lo := (cons_le _ _ _ _).mp lower
          have hi := (cons_le _ _ _ _).mp upper
          have same : next = first := by
            rcases lo with less | ⟨same, _⟩
            · rcases hi with less' | ⟨same, _⟩
              · exact False.elim (lt_asymm less less')
              · exact same
            · exact same.symm
          subst next
          have lowerRest : stem ++ leftRest ≤ rest :=
            ((cons_le _ _ _ _).mp lower).resolve_left (lt_irrefl _) |>.2
          have upperRest : rest ≤ stem ++ rightRest :=
            ((cons_le _ _ _ _).mp upper).resolve_left (lt_irrefl _) |>.2
          obtain ⟨tail, equal⟩ := ih _ _ _ ⟨leftRest, rfl⟩ ⟨rightRest, rfl⟩
            lowerRest upperRest
          exact ⟨tail, by simp [equal]⟩

theorem append_le_cancel (stem left right : Key) :
    stem ++ left ≤ stem ++ right ↔ left ≤ right := by
  induction stem with
  | nil => rfl
  | cons first stem ih =>
      change first :: (stem ++ left) ≤ first :: (stem ++ right) ↔ _
      rw [cons_le]
      simpa using ih

/-- A varToken band fixes the rigid stem, then permits every varToken name.
The varToken at its boundary is the first one when the stem is rigid. -/
def Band (stem row : Key) : Prop :=
  ∃ name suffix, row = stem ++ varToken name :: suffix

theorem band_convex (stem left middle right : Key)
    (leftBand : Band stem left) (rightBand : Band stem right)
    (lower : left ≤ middle) (upper : middle ≤ right) : Band stem middle := by
  obtain ⟨leftName, leftRest, rfl⟩ := leftBand
  obtain ⟨rightName, rightRest, rfl⟩ := rightBand
  have between := prefix_convex stem _ middle _
    ⟨varToken leftName :: leftRest, rfl⟩ ⟨varToken rightName :: rightRest, rfl⟩ lower upper
  obtain ⟨middleRest, rfl⟩ := between
  have lo := (append_le_cancel stem _ _).mp lower
  have hi := (append_le_cancel stem _ _).mp upper
  cases middleRest with
  | nil => exact False.elim ((not_le_of_gt
      (show ([] : Key) < varToken leftName :: leftRest from List.Lex.nil)) lo)
  | cons token rest =>
      have lowerToken : varToken leftName ≤ token := by
        rcases (cons_le _ _ _ _).mp lo with less | ⟨same, _⟩
        · exact less.le
        · exact le_of_eq same
      have upperToken : token ≤ varToken rightName := by
        rcases (cons_le _ _ _ _).mp hi with less | ⟨same, _⟩
        · exact less.le
        · exact le_of_eq same
      have lowerKind := Prod.Lex.monotone_fst _ _ lowerToken
      have upperKind := Prod.Lex.monotone_fst _ _ upperToken
      have sameKind : kind token = 1 := by
        have equality := le_antisymm upperKind lowerKind
        simpa [kind, varToken] using equality
      refine ⟨(ofLex token).2, rest, ?_⟩
      have sameToken : token = varToken (ofLex token).2 := by
        exact congrArg toLex (Prod.ext sameKind rfl)
      rw [sameToken]
      rfl

theorem variable_before_rigid (name : Nat) (token : Token) (ground : 1 < kind token) :
    varToken name < token := by
  exact (Prod.Lex.lt_iff).mpr (Or.inl ground)

/-- Earlier varToken bands precede later bands, or the full rigid stem,
because their first difference is a varToken versus a rigid node. -/
theorem band_before_extension (stem : Key) (token : Token)
    (ground : 1 < kind token) (leftName : Nat) (leftRest rightRest : Key) :
    stem ++ varToken leftName :: leftRest < stem ++ token :: rightRest := by
  apply List.append_left_lt
  exact List.Lex.rel (variable_before_rigid leftName token ground)

def front : Key → Key
  | [] => []
  | token :: rest => if kind token = 1 then [] else token :: front rest

theorem front_prefix (row : Key) : front row <+: row := by
  induction row with
  | nil => exact List.prefix_refl _
  | cons token rest ih =>
      by_cases isVariable : kind token = 1
      · simp [front, isVariable]
      · obtain ⟨tail, equal⟩ := ih
        exact ⟨tail, by simp [front, isVariable, equal]⟩

theorem front_rigid (row : Key) : ∀ token ∈ front row, kind token ≠ 1 := by
  induction row with
  | nil => simp [front]
  | cons first rest ih =>
      by_cases isVariable : kind first = 1
      · simp [front, isVariable]
      · simp only [front, isVariable, ↓reduceIte, List.mem_cons]
        intro token member
        rcases member with equal | member
        · simpa [equal] using isVariable
        · exact ih token member

/-- Metadata counts rows, including duplicate occurrences, by their actual
first-varToken boundary. The all-rigid rows do not populate any band. -/
def firstVariable (row : Key) : Option Nat :=
  if front row = row then none else some (front row).length

def countBand (rows : List Key) (position : Nat) : Nat :=
  (rows.filter (fun row => firstVariable row = some position)).length

theorem countBand_nonzero_iff (rows : List Key) (position : Nat) :
    countBand rows position ≠ 0 ↔ ∃ row ∈ rows, firstVariable row = some position := by
  simp [countBand, List.filter_eq_nil_iff]

end Mettapedia.Machines.Cursor.KeyFrontRanges
