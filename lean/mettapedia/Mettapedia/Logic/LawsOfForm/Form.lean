/-!
# Laws of Form: faithful finite syntax and the Primary Arithmetic

A form is a finite juxtaposition of crosses; each cross encloses a form
(G. Spencer-Brown, *Laws of Form*).  The void is the empty juxtaposition and the
mark is a single cross enclosing the void.  Juxtaposition is list append.
Spencer-Brown's notation is two-dimensional, so juxtaposition is commutative
implicitly; a linear presentation must say so explicitly.  Here commutativity
is a *quotient*: `Form.Equiv` is permutation equivalence lifted hereditarily
through crosses.  Nothing is identified with `Bool`; the Boolean value of a
form is a separately defined observation `Form.marked`, and the Primary
Arithmetic is a normalization function whose correctness is stated against
that observation.

The Metamath development `lof.mm` (naipmoro, *Laws of Form in Metamath*)
represents forms as token strings and relies on Metamath's empty substitution
to stand for the void; here the void is the empty list and no substitution
mechanism is involved.  Spencer-Brown forms modulo commutative juxtaposition
are hereditarily finite multisets (Sifnaios, *Weak essentially undecidable
theories of hereditarily finite multisets*); Lean cannot nest an inductive
type through `Multiset`, so lists with a hereditary permutation quotient are
the faithful route.
-/

namespace Mettapedia.Logic.LawsOfForm

/-- A cross encloses a form; a form is a finite list of crosses. -/
inductive Cross where
  | cross (contents : List Cross)

/-- A form: a finite juxtaposition of crosses. -/
abbrev Form := List Cross

/-- The void. -/
def void : Form := []

/-- The mark: one cross enclosing the void. -/
def mark : Form := [.cross []]

theorem mark_ne_void : mark ≠ void :=
  List.cons_ne_nil _ _

/-- Whether a form is the void.  Used by normalization instead of decidable
equality, which Lean does not derive for nested inductive types. -/
def Form.isVoid : List Cross → Bool
  | [] => true
  | _ :: _ => false

@[simp] theorem isVoid_nil : Form.isVoid [] = true := rfl
@[simp] theorem isVoid_cons (c : Cross) (cs : List Cross) : Form.isVoid (c :: cs) = false := rfl
theorem isVoid_mark : Form.isVoid mark = false := rfl

/-! ## The value observation: marked or unmarked -/

mutual
  /-- A cross is marked exactly when its contents are unmarked. -/
  def Cross.marked : Cross → Bool
    | .cross contents => !(Form.markedList contents)
  /-- A juxtaposition is marked exactly when some component is marked. -/
  def Form.markedList : List Cross → Bool
    | [] => false
    | c :: cs => c.marked || Form.markedList cs
end

@[simp] theorem markedList_nil : Form.markedList [] = false := rfl
@[simp] theorem markedList_cons (c : Cross) (cs : List Cross) :
    Form.markedList (c :: cs) = (c.marked || Form.markedList cs) := rfl
@[simp] theorem cross_marked (contents : List Cross) :
    (Cross.cross contents).marked = !(Form.markedList contents) := rfl

theorem markedList_void : Form.markedList void = false := rfl
theorem markedList_mark : Form.markedList mark = true := rfl

theorem markedList_append (a b : List Cross) :
    Form.markedList (a ++ b) = (Form.markedList a || Form.markedList b) := by
  induction a with
  | nil => simp
  | cons c cs ih => simp [ih, Bool.or_assoc]

/-! ## Hereditary permutation equivalence: commutativity as a quotient -/

mutual
  /-- Crosses are equivalent when their contents are. -/
  inductive Cross.Equiv : Cross → Cross → Prop
    | cross {a b : List Cross} : Form.Equiv a b → Cross.Equiv (.cross a) (.cross b)
  /-- Forms are equivalent when they are permutations of pairwise equivalent
  crosses. -/
  inductive Form.Equiv : List Cross → List Cross → Prop
    | nil : Form.Equiv [] []
    | cons {x y : Cross} {xs ys : List Cross} :
        Cross.Equiv x y → Form.Equiv xs ys → Form.Equiv (x :: xs) (y :: ys)
    | swap {x y : Cross} {xs : List Cross} : Form.Equiv (x :: y :: xs) (y :: x :: xs)
    | trans {a b c : List Cross} : Form.Equiv a b → Form.Equiv b c → Form.Equiv a c
end

mutual
  theorem Cross.Equiv.refl : ∀ c : Cross, Cross.Equiv c c
    | .cross contents => .cross (Form.Equiv.refl contents)
  theorem Form.Equiv.refl : ∀ f : List Cross, Form.Equiv f f
    | [] => .nil
    | c :: cs => .cons (Cross.Equiv.refl c) (Form.Equiv.refl cs)
end

mutual
  theorem Cross.Equiv.symm : ∀ {a b : Cross}, Cross.Equiv a b → Cross.Equiv b a
    | _, _, .cross h => .cross (Form.Equiv.symm h)
  theorem Form.Equiv.symm : ∀ {a b : List Cross}, Form.Equiv a b → Form.Equiv b a
    | _, _, .nil => .nil
    | _, _, .cons hx hxs => .cons (Cross.Equiv.symm hx) (Form.Equiv.symm hxs)
    | _, _, .swap => .swap
    | _, _, .trans h₁ h₂ => .trans (Form.Equiv.symm h₂) (Form.Equiv.symm h₁)
end

/-- `Form.Equiv` is an equivalence relation. -/
theorem Form.Equiv.equivalence : Equivalence Form.Equiv :=
  ⟨Form.Equiv.refl, Form.Equiv.symm, Form.Equiv.trans⟩

/-! The value observation respects the commutativity quotient. -/
mutual
  theorem Cross.Equiv.marked_eq : ∀ {a b : Cross}, Cross.Equiv a b → a.marked = b.marked
    | _, _, .cross h => by
        simp only [cross_marked]
        rw [Form.Equiv.markedList_eq h]
  theorem Form.Equiv.markedList_eq :
      ∀ {a b : List Cross}, Form.Equiv a b → Form.markedList a = Form.markedList b
    | _, _, .nil => rfl
    | _, _, .cons hx hxs => by
        simp only [markedList_cons]
        rw [Cross.Equiv.marked_eq hx, Form.Equiv.markedList_eq hxs]
    | _, _, .swap => by
        simp only [markedList_cons]
        rw [Bool.or_left_comm]
    | _, _, .trans h₁ h₂ =>
        (Form.Equiv.markedList_eq h₁).trans (Form.Equiv.markedList_eq h₂)
end

/-! ### Commutativity canaries -/

/-- Positive: juxtaposition order is invisible to the quotient. -/
theorem juxtaposition_commutes :
    Form.Equiv [.cross [], .cross [.cross []]] [.cross [.cross []], .cross []] :=
  .swap

/-- Negative: nesting is not juxtaposition.  `⟨⟨ ⟩⟩` and `⟨ ⟩⟨ ⟩` differ, and
their values witness it. -/
theorem nesting_is_not_juxtaposition :
    ¬ Form.Equiv [.cross [.cross []]] [.cross [], .cross []] := by
  intro h
  have := Form.Equiv.markedList_eq h
  simp at this

/-! ## The Primary Arithmetic: calling and crossing, and normalization -/

/-- Calling (I1) is value-preserving: a repeated cross juxtaposed with itself has
the value of one. -/
theorem calling_value_preserving (c : List Cross) :
    Form.markedList [.cross c, .cross c] = Form.markedList [.cross c] := by
  simp

/-- Crossing (I2) is value-preserving: a cross enclosing the mark has the value of
the void. -/
theorem crossing_value_preserving :
    Form.markedList [.cross [.cross []]] = Form.markedList void := rfl

mutual
  /-- Normalize a cross: evaluate its contents, then cross. -/
  def Cross.normalize : Cross → Form
    | .cross contents => if Form.isVoid (Form.normalizeList contents) then mark else []
  /-- Normalize a juxtaposition: a marked component makes the whole the mark. -/
  def Form.normalizeList : List Cross → Form
    | [] => []
    | c :: cs => if Form.isVoid c.normalize then Form.normalizeList cs else mark
end

@[simp] theorem normalizeList_nil : Form.normalizeList [] = [] := rfl
@[simp] theorem normalizeList_cons (c : Cross) (cs : List Cross) :
    Form.normalizeList (c :: cs) =
      if Form.isVoid c.normalize then Form.normalizeList cs else mark := rfl
@[simp] theorem cross_normalize (contents : List Cross) :
    (Cross.cross contents).normalize =
      if Form.isVoid (Form.normalizeList contents) then mark else [] := rfl

/-! Every closed form normalizes to the void or the mark. -/
mutual
  theorem Cross.normalize_void_or_mark : ∀ c : Cross, c.normalize = [] ∨ c.normalize = mark
    | .cross contents => by
        rw [cross_normalize]
        cases Form.isVoid (Form.normalizeList contents)
        · exact Or.inl rfl
        · exact Or.inr rfl
  theorem Form.normalizeList_void_or_mark :
      ∀ f : List Cross, Form.normalizeList f = [] ∨ Form.normalizeList f = mark
    | [] => Or.inl rfl
    | c :: cs => by
        rw [normalizeList_cons]
        cases Form.isVoid c.normalize
        · exact Or.inr rfl
        · exact Form.normalizeList_void_or_mark cs
end

/-! Normalization preserves the value observation. -/
mutual
  theorem Cross.normalize_marked : ∀ c : Cross, Form.markedList c.normalize = c.marked
    | .cross contents => by
        have ih := Form.normalizeList_marked contents
        rcases Form.normalizeList_void_or_mark contents with h | h
        · rw [cross_normalize, cross_marked, h]
          rw [h, markedList_nil] at ih
          simp [markedList_mark, ← ih]
        · rw [cross_normalize, cross_marked, h]
          rw [h, markedList_mark] at ih
          simp [isVoid_mark, ← ih]
  theorem Form.normalizeList_marked :
      ∀ f : List Cross, Form.markedList (Form.normalizeList f) = Form.markedList f
    | [] => rfl
    | c :: cs => by
        have ihc := Cross.normalize_marked c
        have ihs := Form.normalizeList_marked cs
        rcases Cross.normalize_void_or_mark c with h | h
        · rw [normalizeList_cons, markedList_cons, h]
          rw [h, markedList_nil] at ihc
          simp [ihs, ← ihc]
        · rw [normalizeList_cons, markedList_cons, h]
          rw [h, markedList_mark] at ihc
          simp [isVoid_mark, markedList_mark, ← ihc]
end

/-- Uniqueness: the normal form is determined by the value.  Normalization is
the unique arithmetic representative of the value class. -/
theorem normalizeList_eq_of_marked (f : List Cross) :
    Form.normalizeList f = if Form.markedList f then mark else [] := by
  have h := Form.normalizeList_marked f
  rcases Form.normalizeList_void_or_mark f with h₀ | h₁
  · rw [h₀]
    rw [h₀, markedList_nil] at h
    simp [← h]
  · rw [h₁]
    rw [h₁, markedList_mark] at h
    simp [← h]

/-! ### Arithmetic canaries -/

/-- Positive: the mark juxtaposed with itself normalizes to the mark. -/
theorem calling_normalizes : Form.normalizeList [.cross [], .cross []] = mark := rfl

/-- Positive: a cross enclosing the mark normalizes to the void. -/
theorem crossing_normalizes : Form.normalizeList [.cross [.cross []]] = [] := rfl

/-- Negative: `⟨⟨ ⟩⟩` is unmarked; it is not the mark. -/
theorem double_cross_unmarked : Form.markedList [.cross [.cross []]] = false := rfl

/-- Negative: the two normal forms are distinct, so normalization is not
constant. -/
theorem normal_forms_distinct :
    Form.normalizeList [.cross []] ≠ Form.normalizeList [.cross [.cross []]] := by
  rw [crossing_normalizes]
  show mark ≠ []
  exact List.cons_ne_nil _ _

#print axioms Form.Equiv.equivalence
#print axioms Form.Equiv.markedList_eq
#print axioms nesting_is_not_juxtaposition
#print axioms Form.normalizeList_marked
#print axioms normalizeList_eq_of_marked

end Mettapedia.Logic.LawsOfForm
