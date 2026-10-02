import Mathlib.Computability.MyhillNerode

/-!
# Left derivatives of formal languages

A derivative removes a specified initial letter from each word of a language:
it is Mathlib's left quotient by a one-letter word. The equations for sums,
products and Kleene star are proved directly from Mathlib's set-of-words
semantics and its nonempty-factor description of Kleene star. They do not
presuppose a regex matcher or its derivative algorithm.
-/

open scoped Computability

namespace Mettapedia.Computability.RegularLanguages

variable {α : Type*}

/-- The words obtained by removing the initial letter `a` from words of `L`:
the left quotient of `L` by the one-letter word. -/
def leftDerivative (a : α) (L : Language α) : Language α :=
  L.leftQuotient [a]

theorem leftDerivative_eq_leftQuotient (a : α) (L : Language α) :
    leftDerivative a L = L.leftQuotient [a] :=
  rfl

@[simp]
theorem mem_leftDerivative (a : α) (L : Language α) (w : List α) :
    w ∈ leftDerivative a L ↔ a :: w ∈ L :=
  Iff.rfl

/-- The left quotient by a word removes its letters one at a time. -/
theorem leftQuotient_cons (a : α) (word : List α) (L : Language α) :
    L.leftQuotient (a :: word) = (leftDerivative a L).leftQuotient word :=
  Language.leftQuotient_append L [a] word

@[simp]
theorem leftDerivative_zero (a : α) : leftDerivative a (0 : Language α) = 0 := by
  ext w
  simp

@[simp]
theorem leftDerivative_one (a : α) : leftDerivative a (1 : Language α) = 0 := by
  ext w
  simp

/-- Removing the first letter from a singleton word gives its singleton tail. -/
@[simp]
theorem leftDerivative_singleton_cons (a : α) (w : List α) :
    leftDerivative a ({a :: w} : Language α) = {w} := by
  ext v
  change (a :: v = a :: w) ↔ v = w
  simp

/-- A different initial letter cannot match a singleton word. -/
theorem leftDerivative_singleton_cons_of_ne {a b : α} (h : a ≠ b) (w : List α) :
    leftDerivative a ({b :: w} : Language α) = 0 := by
  ext v
  change (a :: v = b :: w) ↔ v ∈ (0 : Language α)
  simp [h]

/-- A one-letter language accepts the derivative precisely at its own letter. -/
theorem leftDerivative_singleton [DecidableEq α] (a b : α) :
    leftDerivative a ({[b]} : Language α) = if a = b then 1 else 0 := by
  by_cases h : a = b
  · subst b
    rw [if_pos rfl]
    exact leftDerivative_singleton_cons a []
  · simpa [h] using leftDerivative_singleton_cons_of_ne h []

/-- The derivative of a one-letter character class depends only on whether
the consumed letter belongs to the class. -/
theorem mem_leftDerivative_letters (a : α) (P : α → Prop) (w : List α) :
    w ∈ leftDerivative a ({v | ∃ b, P b ∧ v = [b]} : Language α) ↔
      P a ∧ w = [] := by
  change (∃ b, P b ∧ a :: w = [b]) ↔ P a ∧ w = []
  simp only [List.cons.injEq]
  constructor
  · rintro ⟨b, hb, rfl, rfl⟩
    exact ⟨hb, rfl⟩
  · rintro ⟨ha, rfl⟩
    exact ⟨a, ha, rfl, rfl⟩

theorem leftDerivative_letters (a : α) (P : α → Prop) [Decidable (P a)] :
    leftDerivative a ({v | ∃ b, P b ∧ v = [b]} : Language α) =
      if P a then 1 else 0 := by
  ext w
  rw [mem_leftDerivative_letters]
  by_cases h : P a <;> simp [h]

@[simp]
theorem leftDerivative_add (a : α) (L M : Language α) :
    leftDerivative a (L + M) = leftDerivative a L + leftDerivative a M := by
  ext w
  simp only [mem_leftDerivative, Language.mem_add]

/-- Concatenation can consume the initial letter in the first factor, or in the
second factor when the first factor accepts the empty word. -/
theorem mem_leftDerivative_mul (a : α) (L M : Language α) (w : List α) :
    w ∈ leftDerivative a (L * M) ↔
      w ∈ leftDerivative a L * M ∨ ([] ∈ L ∧ w ∈ leftDerivative a M) := by
  constructor
  · intro h
    obtain ⟨u, hu, v, hv, huv⟩ := Language.mem_mul.mp h
    cases u with
    | nil =>
        right
        simp only [List.nil_append] at huv
        subst v
        exact ⟨hu, hv⟩
    | cons b u =>
        left
        simp only [List.cons_append, List.cons.injEq] at huv
        obtain ⟨rfl, huv⟩ := huv
        exact Language.mem_mul.mpr ⟨u, hu, v, hv, huv⟩
  · rintro (h | ⟨hL, hM⟩)
    · obtain ⟨u, hu, v, hv, rfl⟩ := Language.mem_mul.mp h
      exact Language.mem_mul.mpr ⟨a :: u, hu, v, hv, rfl⟩
    · exact Language.mem_mul.mpr ⟨[], hL, a :: w, hM, rfl⟩

/-- The language equation for concatenation, with an explicit nullability guard. -/
theorem leftDerivative_mul (a : α) (L M : Language α) [Decidable ([] ∈ L)] :
    leftDerivative a (L * M) =
      leftDerivative a L * M + if [] ∈ L then leftDerivative a M else 0 := by
  ext w
  rw [mem_leftDerivative_mul, Language.mem_add]
  by_cases h : [] ∈ L <;> simp [h]

/-- A nonempty starred word starts with a nonempty word of the base language.
Discarding empty factors makes this equation valid even for nullable `L`. -/
theorem leftDerivative_kstar (a : α) (L : Language α) :
    leftDerivative a L∗ = leftDerivative a L * L∗ := by
  ext w
  constructor
  · intro h
    obtain ⟨parts, hparts, hall⟩ := Language.mem_kstar_iff_exists_nonempty.mp h
    cases parts with
    | nil => simp at hparts
    | cons first rest =>
        have hfirst := hall first (by simp)
        cases first with
        | nil => exact False.elim (hfirst.2 rfl)
        | cons b u =>
            simp only [List.flatten_cons, List.cons_append, List.cons.injEq] at hparts
            obtain ⟨rfl, hw⟩ := hparts
            have hrest : rest.flatten ∈ L∗ :=
              Language.join_mem_kstar (fun v hv => (hall v (by simp [hv])).1)
            exact Language.mem_mul.mpr ⟨u, hfirst.1, rest.flatten, hrest, hw.symm⟩
  · intro h
    obtain ⟨u, hu, v, hv, rfl⟩ := Language.mem_mul.mp h
    obtain ⟨parts, rfl, hall⟩ := Language.mem_kstar.mp hv
    apply Language.mem_kstar.mpr
    refine ⟨(a :: u) :: parts, rfl, ?_⟩
    exact List.forall_mem_cons.mpr ⟨hu, hall⟩

/-- A language equation remains valid after consuming a letter. -/
theorem leftDerivative_congr (a : α) {L M : Language α}
    (h : ∀ w, w ∈ L ↔ w ∈ M) : leftDerivative a L = leftDerivative a M :=
  congrArg (leftDerivative a) (Language.ext h)

/-- Consuming a letter preserves language inclusion. -/
theorem leftDerivative_mono (a : α) {L M : Language α} (h : L ≤ M) :
    leftDerivative a L ≤ leftDerivative a M :=
  fun _ hw => h hw

namespace Controls

/-- The empty-word alternative allows a concatenation to consume its second
factor directly. -/
theorem nullable_concat_consumes_second :
    [] ∈ leftDerivative true
      ((1 + ({[false]} : Language Bool)) * ({[true]} : Language Bool)) := by
  rw [mem_leftDerivative_mul]
  right
  exact ⟨Or.inl Language.nil_mem_one, rfl⟩

/-- Empty factors in a star do not prevent a nonempty factor from matching. -/
theorem nullable_kstar_consumes :
    [] ∈ leftDerivative true ((1 + ({[true]} : Language Bool))∗) := by
  rw [leftDerivative_kstar, leftDerivative_add, leftDerivative_one]
  rw [leftDerivative_singleton_cons, zero_add]
  exact Language.mem_mul.mpr ⟨[], rfl, [], Language.nil_mem_kstar _, rfl⟩

/-- The empty-word alternative still cannot manufacture an unmatched letter. -/
theorem nullable_kstar_rejects_other_letter :
    [] ∉ leftDerivative false ((1 + ({[true]} : Language Bool))∗) := by
  rw [leftDerivative_kstar, leftDerivative_add, leftDerivative_one]
  rw [leftDerivative_singleton_cons_of_ne Bool.false_ne_true, zero_add, zero_mul]
  exact Language.notMem_zero _

end Controls

end Mettapedia.Computability.RegularLanguages
