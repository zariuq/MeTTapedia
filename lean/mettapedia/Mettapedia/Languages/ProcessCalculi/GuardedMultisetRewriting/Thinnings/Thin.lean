import Mathlib.Tactic

/-!
# Thinnings

A **thinning** says how a smaller scope sits inside a larger one, keeping the order of the
variables: an order-preserving embedding (McBride, "Everybody's Got To Be Somewhere", 2018). Here a
scope is a number of variables, counted from the innermost one, and a thinning is a bit vector read
from the innermost variable outward: bit `i` says whether variable `i` of the larger scope is kept.

Example: `[true, false, true]` embeds a scope of two variables into a scope of three, skipping the
middle one. Its variable `0` stays `0`, its variable `1` becomes `2` (`sel`).

Past its end a thinning keeps every variable, so `[]` is the identity of every scope, and the
action on variables `sel` is total. A thinning from `m` variables into `n` is **exact** when it has
`n` bits of which `m` are kept; the laws below hold for all bit lists, and exact thinnings compose
to exact thinnings (`length_comp`, `ones_comp`).

* **Composition** `comp θ φ` is "first `θ`, then `φ`": `sel (comp θ φ) = sel φ ∘ sel θ`
  (`sel_comp`). It is associative with identity `[]` (`comp_assoc`, `comp_nil_left`,
  `comp_nil_right`); on exact thinnings `replicate n true` is the identity of `n`
  (`comp_idn_left`, `comp_idn_right`). Order is kept: `sel` is strictly increasing (`sel_lt_sel`).
* **Under binders**: `keepN d θ` keeps `d` new innermost variables; `dropN k θ` skips `k`.
* **A thinning is its kept positions**: `bit θ i` says whether position `i` is kept; the kept
  positions are exactly the `sel θ j` with `j < ones θ` (`bit_sel`, `exists_sel_of_bit`), and two
  thinnings with the same kept positions act alike on their kept variables (`sel_eq_of_bits`).
* **Trimmed** thinnings end in a kept bit (or are empty). They are the canonical form of a
  reference: two trimmed thinnings with the same kept positions are equal (`trimmed_ext`). `cut m θ`
  keeps `θ` up to its `m`-th kept bit, which trims it (`trimmed_cut`).
* **Union** `bor` (bitwise or) is the coproduct of two subscopes in the slice over a scope: the
  least subscope containing both. **Pullback** `pull U φ` re-reads a subscope `φ ⊆ U` as a subscope
  of `U` (`sel_pull`). With `front`/`back`, which split a field's thinning into its bound and its
  outer variables, these give the edge of the smart constructor (`sel_edge`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings

/-- A thinning, as a bit vector read from the innermost variable outward: bit `i` says whether
variable `i` of the larger scope is kept. Past its end a thinning keeps every variable. -/
abbrev Thin := List Bool

namespace Thin

/-! ## The action on variables -/

/-- `sel θ j`: the variable of the larger scope that variable `j` of the smaller scope becomes,
that is, the position of the `j`-th kept bit. -/
def sel : Thin → ℕ → ℕ
  | [], j => j
  | true :: _, 0 => 0
  | true :: θ, j + 1 => sel θ j + 1
  | false :: θ, j => sel θ j + 1

@[simp] theorem sel_nil (j : ℕ) : sel [] j = j := by simp [sel]
@[simp] theorem sel_true_zero (θ : Thin) : sel (true :: θ) 0 = 0 := by simp [sel]
@[simp] theorem sel_true_succ (θ : Thin) (j : ℕ) : sel (true :: θ) (j + 1) = sel θ j + 1 := by
  simp [sel]
@[simp] theorem sel_false (θ : Thin) (j : ℕ) : sel (false :: θ) j = sel θ j + 1 := by simp [sel]

/-- The number of kept variables: the size of the smaller scope. -/
def ones : Thin → ℕ
  | [] => 0
  | true :: θ => ones θ + 1
  | false :: θ => ones θ

@[simp] theorem ones_nil : ones [] = 0 := rfl
@[simp] theorem ones_true (θ : Thin) : ones (true :: θ) = ones θ + 1 := rfl
@[simp] theorem ones_false (θ : Thin) : ones (false :: θ) = ones θ := rfl

theorem ones_append (α β : Thin) : ones (α ++ β) = ones α + ones β := by
  induction α with
  | nil => simp
  | cons b α ih =>
      cases b with
      | false => simp [ih]
      | true => simp [ih]; omega

theorem ones_le_length (θ : Thin) : ones θ ≤ θ.length := by
  induction θ with
  | nil => simp
  | cons b θ ih => cases b <;> simp <;> omega

/-- **Order is kept**: `sel θ` is strictly increasing. -/
theorem sel_lt_sel (θ : Thin) {j k : ℕ} (lt : j < k) : sel θ j < sel θ k := by
  induction θ generalizing j k with
  | nil => simpa using lt
  | cons b θ ih =>
      cases b with
      | false => simpa using ih lt
      | true =>
          cases j with
          | zero =>
              obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
              simp
          | succ j =>
              obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
              simpa using ih (by omega : j < k')

theorem sel_le_sel (θ : Thin) {j k : ℕ} (le : j ≤ k) : sel θ j ≤ sel θ k := by
  rcases Nat.eq_or_lt_of_le le with rfl | lt
  · exact le_refl _
  · exact (sel_lt_sel θ lt).le

theorem sel_injective (θ : Thin) : Function.Injective (sel θ) := by
  intro j k h
  rcases lt_trichotomy j k with lt | eq | gt
  · exact absurd h (sel_lt_sel θ lt).ne
  · exact eq
  · exact absurd h (sel_lt_sel θ gt).ne'

theorem le_sel (θ : Thin) (j : ℕ) : j ≤ sel θ j := by
  induction θ generalizing j with
  | nil => simp
  | cons b θ ih =>
      cases b with
      | false => have := ih j; simp; omega
      | true =>
          cases j with
          | zero => simp
          | succ j => have := ih j; simp; omega

/-! ## Composition and the category laws -/

/-- **Composition**, first `θ` then `φ`: `θ` embeds the smallest scope into the middle one, `φ`
the middle one into the largest. -/
def comp : Thin → Thin → Thin
  | θ, [] => θ
  | θ, false :: φ => false :: comp θ φ
  | [], true :: φ => true :: comp [] φ
  | b :: θ, true :: φ => b :: comp θ φ

@[simp] theorem comp_nil_right (θ : Thin) : comp θ [] = θ := by cases θ <;> simp [comp]
@[simp] theorem comp_false (θ φ : Thin) : comp θ (false :: φ) = false :: comp θ φ := by
  cases θ <;> simp [comp]
@[simp] theorem comp_nil_true (φ : Thin) : comp [] (true :: φ) = true :: comp [] φ := by
  simp [comp]
@[simp] theorem comp_cons_true (b : Bool) (θ φ : Thin) : comp (b :: θ) (true :: φ) = b :: comp θ φ := by
  simp [comp]

/-- `[]` is a left identity. -/
@[simp] theorem comp_nil_left (φ : Thin) : comp [] φ = φ := by
  induction φ with
  | nil => rfl
  | cons b φ ih => cases b <;> simp [ih]

/-- **Composition acts by composing the actions**: `sel (comp θ φ) = sel φ ∘ sel θ`. -/
theorem sel_comp (θ φ : Thin) (j : ℕ) : sel (comp θ φ) j = sel φ (sel θ j) := by
  induction φ generalizing θ j with
  | nil => simp
  | cons b φ ih =>
      cases b with
      | false => simp [ih]
      | true =>
          cases θ with
          | nil =>
              cases j with
              | zero => simp
              | succ j => simp
          | cons c θ =>
              cases c with
              | false => simp [ih]
              | true =>
                  cases j with
                  | zero => simp
                  | succ j => simp [ih]

/-- **Composition is associative.** -/
theorem comp_assoc (θ φ ψ : Thin) : comp (comp θ φ) ψ = comp θ (comp φ ψ) := by
  induction ψ generalizing θ φ with
  | nil => simp
  | cons b ψ ih =>
      cases b with
      | false => simp [ih]
      | true =>
          cases φ with
          | nil => simp
          | cons c φ =>
              cases c with
              | false => simp [ih]
              | true =>
                  cases θ with
                  | nil => simp
                  | cons a θ => simp [ih]

/-- The identity thinning of a scope of `n` variables, as an exact thinning. -/
def idn (n : ℕ) : Thin := List.replicate n true

/-- `idn` is a left identity of exact thinnings. -/
theorem comp_idn_left (φ : Thin) : comp (idn (ones φ)) φ = φ := by
  induction φ with
  | nil => simp [idn]
  | cons b φ ih =>
      cases b with
      | false => simp [ih]
      | true => simpa [idn, List.replicate_succ] using ih

/-- `idn` is a right identity of exact thinnings. -/
theorem comp_idn_right (θ : Thin) : comp θ (idn θ.length) = θ := by
  induction θ with
  | nil => simp [idn]
  | cons b θ ih => simpa [idn, List.replicate_succ] using ih

/-- **Exact thinnings compose to exact thinnings**: the length of a composite is that of the second. -/
theorem length_comp {θ φ : Thin} (exact : ones φ = θ.length) : (comp θ φ).length = φ.length := by
  induction φ generalizing θ with
  | nil => simp at exact; simp [List.length_eq_zero_iff.mp exact.symm]
  | cons b φ ih =>
      cases b with
      | false => simpa using ih exact
      | true =>
          cases θ with
          | nil => simp at exact
          | cons a θ => simpa using ih (by simpa using exact)

/-- The kept variables of a composite are those of the first. -/
theorem ones_comp {θ φ : Thin} (exact : ones φ = θ.length) : ones (comp θ φ) = ones θ := by
  induction φ generalizing θ with
  | nil => simp
  | cons b φ ih =>
      cases b with
      | false => simpa using ih exact
      | true =>
          cases θ with
          | nil => simp at exact
          | cons a θ => cases a <;> simp [ih (by simpa using exact)]

/-! ## Under binders -/

/-- `keepN d θ`: `θ` under `d` new innermost variables, which it keeps. -/
def keepN (d : ℕ) (θ : Thin) : Thin := List.replicate d true ++ θ

/-- `dropN k θ`: `θ` after `k` new innermost variables, which it skips. -/
def dropN (k : ℕ) (θ : Thin) : Thin := List.replicate k false ++ θ

theorem sel_keepN (d : ℕ) (θ : Thin) (j : ℕ) :
    sel (keepN d θ) j = if j < d then j else d + sel θ (j - d) := by
  induction d generalizing j with
  | zero => simp [keepN]
  | succ d ih =>
      cases j with
      | zero => simp [keepN, List.replicate_succ]
      | succ j =>
          have := ih j
          simp only [keepN] at this
          simp only [keepN, List.replicate_succ, List.cons_append, sel_true_succ, this]
          split_ifs <;> first | omega | (congr 1; omega) | skip
          rw [show j + 1 - (d + 1) = j - d by omega]; omega

theorem sel_keepN_lt {d : ℕ} (θ : Thin) {j : ℕ} (lt : j < d) : sel (keepN d θ) j = j := by
  rw [sel_keepN, if_pos lt]

theorem sel_keepN_add (d : ℕ) (θ : Thin) (j : ℕ) : sel (keepN d θ) (d + j) = d + sel θ j := by
  rw [sel_keepN, if_neg (by omega), Nat.add_sub_cancel_left]

theorem sel_dropN (k : ℕ) (θ : Thin) (j : ℕ) : sel (dropN k θ) j = k + sel θ j := by
  induction k with
  | zero => simp [dropN]
  | succ k ih => simp only [dropN, List.replicate_succ, List.cons_append, sel_false] at ih ⊢; omega

@[simp] theorem ones_keepN (d : ℕ) (θ : Thin) : ones (keepN d θ) = d + ones θ := by
  induction d with
  | zero => simp [keepN]
  | succ d ih => simp only [keepN, List.replicate_succ, List.cons_append, ones_true] at ih ⊢; omega

@[simp] theorem ones_dropN (k : ℕ) (θ : Thin) : ones (dropN k θ) = ones θ := by
  induction k with
  | zero => simp [dropN]
  | succ k ih => simpa [dropN, List.replicate_succ] using ih

@[simp] theorem length_keepN (d : ℕ) (θ : Thin) : (keepN d θ).length = d + θ.length := by
  simp [keepN]

@[simp] theorem length_dropN (k : ℕ) (θ : Thin) : (dropN k θ).length = k + θ.length := by
  simp [dropN]

/-- Composition commutes with going under binders. -/
theorem comp_keepN (d : ℕ) (θ φ : Thin) : comp (keepN d θ) (keepN d φ) = keepN d (comp θ φ) := by
  induction d with
  | zero => simp [keepN]
  | succ d ih => simpa [keepN, List.replicate_succ] using ih

theorem keepN_add (a b : ℕ) (θ : Thin) : keepN a (keepN b θ) = keepN (a + b) θ := by
  unfold keepN
  rw [← List.append_assoc, List.replicate_append_replicate]

/-! ## Kept positions -/

/-- `bit θ i`: whether position `i` of the larger scope is kept, reading `false` past the end. -/
def bit : Thin → ℕ → Bool
  | [], _ => false
  | b :: _, 0 => b
  | _ :: θ, i + 1 => bit θ i

@[simp] theorem bit_nil (i : ℕ) : bit [] i = false := by simp [bit]
@[simp] theorem bit_zero (b : Bool) (θ : Thin) : bit (b :: θ) 0 = b := by simp [bit]
@[simp] theorem bit_succ (b : Bool) (θ : Thin) (i : ℕ) : bit (b :: θ) (i + 1) = bit θ i := by
  simp [bit]

theorem bit_of_length_le {θ : Thin} {i : ℕ} (h : θ.length ≤ i) : bit θ i = false := by
  induction θ generalizing i with
  | nil => simp
  | cons b θ ih =>
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by simp at h; omega⟩
      simpa using ih (by simp at h; omega)

theorem bit_append (α β : Thin) (i : ℕ) :
    bit (α ++ β) i = if i < α.length then bit α i else bit β (i - α.length) := by
  induction α generalizing i with
  | nil => simp
  | cons b α ih =>
      cases i with
      | zero => simp
      | succ i =>
          simp only [List.cons_append, bit_succ, ih, List.length_cons]
          split_ifs <;> first | rfl | omega | (congr 1; omega)

/-- **The kept variables land on kept positions**, inside the vector. -/
theorem bit_sel {θ : Thin} {j : ℕ} (lt : j < ones θ) : bit θ (sel θ j) = true ∧ sel θ j < θ.length := by
  induction θ generalizing j with
  | nil => simp at lt
  | cons b θ ih =>
      cases b with
      | false => have := ih (by simpa using lt); simpa using this
      | true =>
          cases j with
          | zero => simp
          | succ j => have := ih (by simp at lt; omega); simpa using this

/-- **Every kept position is reached by a kept variable.** -/
theorem exists_sel_of_bit {θ : Thin} {i : ℕ} (h : bit θ i = true) : ∃ j < ones θ, sel θ j = i := by
  induction θ generalizing i with
  | nil => simp at h
  | cons b θ ih =>
      cases i with
      | zero =>
          simp at h; subst h
          exact ⟨0, by simp, by simp⟩
      | succ i =>
          obtain ⟨j, lt, e⟩ := ih (by simpa using h)
          cases b with
          | false => exact ⟨j, by simpa using lt, by simp [e]⟩
          | true => exact ⟨j + 1, by simp; omega, by simp [e]⟩

theorem bit_iff_exists_sel (θ : Thin) (i : ℕ) : bit θ i = true ↔ ∃ j < ones θ, sel θ j = i := by
  constructor
  · exact exists_sel_of_bit
  · rintro ⟨j, lt, rfl⟩; exact (bit_sel lt).1

/-- Two thinnings with the same kept positions keep the same number of variables. -/
theorem ones_eq_of_bits {θ θ' : Thin} (same : ∀ i, bit θ i = bit θ' i) : ones θ = ones θ' := by
  induction θ generalizing θ' with
  | nil =>
      induction θ' with
      | nil => rfl
      | cons b θ' ih =>
          have h0 := same 0
          simp at h0; subst h0
          simpa using ih (fun i => by simpa using same (i + 1))
  | cons b θ ih =>
      cases θ' with
      | nil =>
          have h0 := same 0
          simp at h0; subst h0
          simpa using ih (θ' := []) (fun i => by simpa using same (i + 1))
      | cons b' θ' =>
          have h0 := same 0
          simp at h0; subst h0
          have := ih (θ' := θ') (fun i => by simpa using same (i + 1))
          cases b <;> simp [this]

/-- **Two thinnings with the same kept positions act alike on their kept variables.** -/
theorem sel_eq_of_bits {θ θ' : Thin} (same : ∀ i, bit θ i = bit θ' i) {j : ℕ} (lt : j < ones θ) :
    sel θ j = sel θ' j := by
  induction θ generalizing θ' j with
  | nil => simp at lt
  | cons b θ ih =>
      cases θ' with
      | nil =>
          have := (bit_sel lt).1
          rw [same] at this; simp at this
      | cons b' θ' =>
          have h0 := same 0
          simp at h0; subst h0
          have rest : ∀ i, bit θ i = bit θ' i := fun i => by simpa using same (i + 1)
          cases b with
          | false => simp [ih rest (by simpa using lt)]
          | true =>
              cases j with
              | zero => simp
              | succ j => simp [ih rest (by simp at lt; omega)]

/-- Two thinnings of one length with the same kept positions are equal. -/
theorem eq_of_bits_of_length {θ θ' : Thin} (len : θ.length = θ'.length)
    (same : ∀ i, bit θ i = bit θ' i) : θ = θ' := by
  induction θ generalizing θ' with
  | nil => simp at len; exact (List.length_eq_zero_iff.mp len.symm).symm
  | cons b θ ih =>
      cases θ' with
      | nil => simp at len
      | cons b' θ' =>
          have h0 := same 0
          simp at h0; subst h0
          rw [ih (by simpa using len) (fun i => by simpa using same (i + 1))]

/-! ## Trimmed thinnings: the canonical form of a reference -/

/-- A thinning is **trimmed** when it is empty or ends in a kept bit. -/
def trimmed : Thin → Bool
  | [] => true
  | [b] => b
  | _ :: b :: θ => trimmed (b :: θ)

@[simp] theorem trimmed_nil : trimmed [] = true := rfl
@[simp] theorem trimmed_single (b : Bool) : trimmed [b] = b := rfl
@[simp] theorem trimmed_cons_cons (a b : Bool) (θ : Thin) :
    trimmed (a :: b :: θ) = trimmed (b :: θ) := rfl

theorem trimmed_tail {a : Bool} {θ : Thin} (h : trimmed (a :: θ) = true) : trimmed θ = true := by
  cases θ with
  | nil => rfl
  | cons b θ => simpa using h

theorem trimmed_cons {a : Bool} {θ : Thin} (h : trimmed θ = true) (ne : θ ≠ []) :
    trimmed (a :: θ) = true := by
  cases θ with
  | nil => exact absurd rfl ne
  | cons b θ => simpa using h

/-- A nonempty trimmed thinning keeps something. -/
theorem exists_bit_of_trimmed {θ : Thin} (h : trimmed θ = true) (ne : θ ≠ []) :
    ∃ i, bit θ i = true := by
  induction θ with
  | nil => exact absurd rfl ne
  | cons a θ ih =>
      cases θ with
      | nil => exact ⟨0, by simpa using h⟩
      | cons b θ =>
          obtain ⟨i, hi⟩ := ih (trimmed_tail h) (by simp)
          exact ⟨i + 1, by simpa using hi⟩

/-- **A trimmed thinning is its kept positions**: two trimmed thinnings that keep the same
positions are equal. -/
theorem trimmed_ext {θ θ' : Thin} (h : trimmed θ = true) (h' : trimmed θ' = true)
    (same : ∀ i, bit θ i = bit θ' i) : θ = θ' := by
  induction θ generalizing θ' with
  | nil =>
      cases θ' with
      | nil => rfl
      | cons b θ' =>
          obtain ⟨i, hi⟩ := exists_bit_of_trimmed h' (by simp)
          rw [← same] at hi; simp at hi
  | cons a θ ih =>
      cases θ' with
      | nil =>
          obtain ⟨i, hi⟩ := exists_bit_of_trimmed h (by simp)
          rw [same] at hi; simp at hi
      | cons a' θ' =>
          have h0 := same 0
          simp at h0; subst h0
          rw [ih (trimmed_tail h) (trimmed_tail h') (fun i => by simpa using same (i + 1))]

/-- `cut m θ`: `θ` up to and including its `m`-th kept bit. -/
def cut : ℕ → Thin → Thin
  | 0, _ => []
  | _ + 1, [] => []
  | m + 1, true :: θ => true :: cut m θ
  | m + 1, false :: θ => false :: cut (m + 1) θ

@[simp] theorem cut_zero (θ : Thin) : cut 0 θ = [] := by cases θ <;> simp [cut]
@[simp] theorem cut_succ_nil (m : ℕ) : cut (m + 1) [] = [] := by simp [cut]
@[simp] theorem cut_succ_true (m : ℕ) (θ : Thin) : cut (m + 1) (true :: θ) = true :: cut m θ := by
  simp [cut]
@[simp] theorem cut_succ_false (m : ℕ) (θ : Thin) :
    cut (m + 1) (false :: θ) = false :: cut (m + 1) θ := by simp [cut]

/-- Cutting after the `m`-th kept bit does not change the first `m` kept variables. -/
theorem sel_cut {m : ℕ} (θ : Thin) {j : ℕ} (lt : j < m) : sel (cut m θ) j = sel θ j := by
  induction θ generalizing m j with
  | nil => obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩; simp
  | cons b θ ih =>
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      cases b with
      | false => simp [ih lt]
      | true =>
          cases j with
          | zero => simp
          | succ j => simp [ih (by omega : j < m')]

theorem ones_cut {m : ℕ} {θ : Thin} (le : m ≤ ones θ) : ones (cut m θ) = m := by
  induction θ generalizing m with
  | nil => simp at le; subst le; simp
  | cons b θ ih =>
      cases m with
      | zero => simp
      | succ m =>
          cases b with
          | false => simpa using ih (by simpa using le)
          | true => simpa using ih (by simp at le; omega)

theorem trimmed_cut {m : ℕ} {θ : Thin} (le : m ≤ ones θ) : trimmed (cut m θ) = true := by
  induction θ generalizing m with
  | nil => simp at le; subst le; simp
  | cons b θ ih =>
      cases m with
      | zero => simp
      | succ m =>
          cases b with
          | false =>
              simp only [cut_succ_false]
              have le' : m + 1 ≤ ones θ := by simpa using le
              refine trimmed_cons (ih le') ?_
              intro e
              have := ones_cut le'
              rw [e] at this; simp at this
          | true =>
              simp only [cut_succ_true]
              cases m with
              | zero => simp
              | succ m =>
                  have le' : m + 1 ≤ ones θ := by simp at le; omega
                  refine trimmed_cons (ih le') ?_
                  intro e
                  have := ones_cut le'
                  rw [e] at this; simp at this

/-- Cutting after the last kept bit keeps every kept position. -/
theorem bit_cut_ones (θ : Thin) (i : ℕ) : bit (cut (ones θ) θ) i = bit θ i := by
  induction θ generalizing i with
  | nil => simp
  | cons b θ ih =>
      cases b with
      | true =>
          cases i with
          | zero => simp
          | succ i => simp [ih]
      | false =>
          rw [ones_false]
          cases h : ones θ with
          | zero =>
              have allFalse : ∀ k, bit θ k = false := by
                intro k
                cases hk : bit θ k
                · rfl
                · obtain ⟨j, lt, _⟩ := exists_sel_of_bit hk
                  omega
              cases i with
              | zero => simp
              | succ i => simp [allFalse]
          | succ m =>
              cases i with
              | zero => simp
              | succ i =>
                  have := ih i
                  rw [h] at this
                  simp [this]

/-- A trimmed thinning is not changed by cutting after its last kept bit. -/
theorem cut_ones_of_trimmed {θ : Thin} (h : trimmed θ = true) : cut (ones θ) θ = θ :=
  trimmed_ext (trimmed_cut (le_refl _)) h (bit_cut_ones θ)

/-! ## Splitting a field's thinning: bound and outer variables -/

/-- `front d θ`: the first `d` bits of `θ`, read `false` past its end: which of `d` bound
variables are kept. -/
def front : ℕ → Thin → Thin
  | 0, _ => []
  | d + 1, θ => θ.headD false :: front d θ.tail

/-- `back d θ`: the bits after the first `d`: which outer variables are kept. -/
def back (d : ℕ) (θ : Thin) : Thin := θ.drop d

@[simp] theorem length_front (d : ℕ) (θ : Thin) : (front d θ).length = d := by
  induction d generalizing θ with
  | zero => simp [front]
  | succ d ih => simp [front, ih]

theorem front_nil_ones (d : ℕ) : ones (front d []) = 0 := by
  induction d with
  | zero => simp [front]
  | succ d ih => simpa [front] using ih

theorem bit_front (d : ℕ) (θ : Thin) (i : ℕ) : bit (front d θ) i = if i < d then bit θ i else false := by
  induction d generalizing θ i with
  | zero => simp [front]
  | succ d ih =>
      cases θ with
      | nil =>
          cases i with
          | zero => simp [front]
          | succ i => simp [front, ih]
      | cons b θ =>
          cases i with
          | zero => simp [front]
          | succ i => simp [front, ih]

theorem bit_back (d : ℕ) (θ : Thin) (i : ℕ) : bit (back d θ) i = bit θ (d + i) := by
  induction d generalizing θ with
  | zero => simp [back]
  | succ d ih =>
      cases θ with
      | nil => simp [back]
      | cons b θ =>
          have := ih θ
          simp only [back] at this
          simp only [back, List.drop_succ_cons, this]
          rw [show d + 1 + i = (d + i) + 1 by omega, bit_succ]

theorem ones_front_back (d : ℕ) (θ : Thin) : ones (front d θ) + ones (back d θ) = ones θ := by
  induction d generalizing θ with
  | zero => simp [front, back]
  | succ d ih =>
      cases θ with
      | nil => simp [back, front_nil_ones]
      | cons b θ =>
          have := ih θ
          simp only [back] at this
          cases b with
          | false => simpa [front, back] using this
          | true => simp [front, back, ← this]; omega

/-- The kept variables of the front are those of `θ`. -/
theorem sel_front {d : ℕ} {θ : Thin} {j : ℕ} (lt : j < ones (front d θ)) :
    sel (front d θ) j = sel θ j := by
  induction d generalizing θ j with
  | zero => simp [front] at lt
  | succ d ih =>
      cases θ with
      | nil => simp [front, front_nil_ones] at lt
      | cons b θ =>
          cases b with
          | false => simp [front] at lt ⊢; exact ih lt
          | true =>
              cases j with
              | zero => simp [front]
              | succ j => simp [front] at lt ⊢; exact ih (by omega)

/-- Past the front, the kept variables of `θ` are those of the back, `d` positions further out. -/
theorem sel_back {d : ℕ} {θ : Thin} {j : ℕ} (ge : ones (front d θ) ≤ j) (lt : j < ones θ) :
    sel θ j = d + sel (back d θ) (j - ones (front d θ)) := by
  induction d generalizing θ j with
  | zero => simp [front, back]
  | succ d ih =>
      cases θ with
      | nil => simp at lt
      | cons b θ =>
          cases b with
          | false =>
              simp [front] at ge ⊢
              rw [ih ge (by simpa using lt)]
              simp [back]; omega
          | true =>
              simp [front] at ge
              obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
              simp only [sel_true_succ]
              rw [ih (by omega) (by simp at lt; omega)]
              simp only [back, List.drop_succ_cons, front, List.headD_cons, List.tail_cons, ones_true]
              rw [show j' + 1 - (ones (front d θ) + 1) = j' - ones (front d θ) by omega]
              omega

/-- Composing with an append: the first part acts first. -/
theorem sel_append (α β : Thin) (j : ℕ) :
    sel (α ++ β) j = if j < ones α then sel α j else α.length + sel β (j - ones α) := by
  induction α generalizing j with
  | nil => simp
  | cons b α ih =>
      cases b with
      | false =>
          simp only [List.cons_append, sel_false, ih, ones_false, List.length_cons]
          split_ifs <;> omega
      | true =>
          cases j with
          | zero => simp
          | succ j =>
              simp only [List.cons_append, sel_true_succ, ih, ones_true, List.length_cons]
              split_ifs <;> first | omega | (rw [show j + 1 - (ones α + 1) = j - ones α by omega]; omega)

/-! ## Union and pullback: covering a scope -/

/-- **Union** of two subscopes (bitwise or): the least subscope containing both. -/
def bor : Thin → Thin → Thin
  | [], φ => φ
  | θ, [] => θ
  | a :: θ, b :: φ => (a || b) :: bor θ φ

@[simp] theorem bor_nil_left (φ : Thin) : bor [] φ = φ := by simp [bor]
@[simp] theorem bor_nil_right (θ : Thin) : bor θ [] = θ := by cases θ <;> simp [bor]
@[simp] theorem bor_cons (a b : Bool) (θ φ : Thin) : bor (a :: θ) (b :: φ) = (a || b) :: bor θ φ := by
  simp [bor]

theorem bit_bor (θ φ : Thin) (i : ℕ) : bit (bor θ φ) i = (bit θ i || bit φ i) := by
  induction θ generalizing φ i with
  | nil => simp
  | cons a θ ih =>
      cases φ with
      | nil => simp
      | cons b φ =>
          cases i with
          | zero => simp
          | succ i => simp [ih]

theorem length_bor (θ φ : Thin) : (bor θ φ).length = max θ.length φ.length := by
  induction θ generalizing φ with
  | nil => simp
  | cons a θ ih =>
      cases φ with
      | nil => simp
      | cons b φ => simp [ih, Nat.succ_max_succ]

theorem trimmed_bor {θ φ : Thin} (h : trimmed θ = true) (h' : trimmed φ = true) :
    trimmed (bor θ φ) = true := by
  induction θ generalizing φ with
  | nil => simpa using h'
  | cons a θ ih =>
      cases φ with
      | nil => simpa using h
      | cons b φ =>
          simp only [bor_cons]
          cases θ with
          | nil =>
              cases φ with
              | nil => simp at h; simp [h]
              | cons c φ => simpa using h'
          | cons c θ =>
              cases φ with
              | nil =>
                  have := trimmed_tail h
                  simp only [bor_nil_right]; simpa using this
              | cons e φ =>
                  have := ih (trimmed_tail h) (trimmed_tail h')
                  simpa using this

/-- The union of a list of subscopes. -/
def bors (l : List Thin) : Thin := l.foldr bor []

theorem bit_bors (l : List Thin) (i : ℕ) : bit (bors l) i = true ↔ ∃ θ ∈ l, bit θ i = true := by
  induction l with
  | nil => simp [bors]
  | cons θ l ih =>
      simp only [bors, List.foldr_cons] at ih ⊢
      rw [bit_bor, Bool.or_eq_true, ih]
      simp

theorem trimmed_bors {l : List Thin} (h : ∀ θ ∈ l, trimmed θ = true) : trimmed (bors l) = true := by
  induction l with
  | nil => simp [bors]
  | cons θ l ih =>
      simp only [bors, List.foldr_cons] at ih ⊢
      exact trimmed_bor (h θ (by simp)) (ih fun θ' m => h θ' (by simp [m]))

/-- **Pullback**: `pull U φ` reads the subscope `φ ⊆ U` as a subscope of `U`, one bit per kept
variable of `U`. -/
def pull : Thin → Thin → Thin
  | [], _ => []
  | true :: U, φ => φ.headD false :: pull U φ.tail
  | false :: U, φ => pull U φ.tail

@[simp] theorem pull_nil (φ : Thin) : pull [] φ = [] := by simp [pull]
@[simp] theorem pull_true (U φ : Thin) : pull (true :: U) φ = φ.headD false :: pull U φ.tail := by
  simp [pull]
@[simp] theorem pull_false (U φ : Thin) : pull (false :: U) φ = pull U φ.tail := by simp [pull]

@[simp] theorem length_pull (U φ : Thin) : (pull U φ).length = ones U := by
  induction U generalizing φ with
  | nil => simp
  | cons b U ih => cases b <;> simp [ih]

/-- `φ` is a subscope of `U`: everything `φ` keeps, `U` keeps. -/
def Sub (φ U : Thin) : Prop := ∀ i, bit φ i = true → bit U i = true

theorem bit_pull {U : Thin} (φ : Thin) {j : ℕ} (lt : j < ones U) : bit (pull U φ) j = bit φ (sel U j) := by
  induction U generalizing φ j with
  | nil => simp at lt
  | cons b U ih =>
      cases b with
      | false =>
          simp only [pull_false, sel_false]
          rw [ih φ.tail (by simpa using lt)]
          cases φ <;> simp
      | true =>
          cases j with
          | zero => cases φ <;> simp
          | succ j =>
              simp only [pull_true, bit_succ, sel_true_succ]
              rw [ih φ.tail (by simp at lt; omega)]
              cases φ <;> simp

theorem ones_pull {U φ : Thin} (sub : Sub φ U) : ones (pull U φ) = ones φ := by
  induction U generalizing φ with
  | nil =>
      have : ∀ i, bit φ i = false := fun i => by
        cases h : bit φ i
        · rfl
        · have := sub i h; simp at this
      have : ones φ = 0 := by
        cases h : ones φ with
        | zero => rfl
        | succ m =>
            have := (bit_sel (θ := φ) (j := 0) (by omega)).1
            rw [‹∀ i, bit φ i = false›] at this; cases this
      simp [this]
  | cons b U ih =>
      cases φ with
      | nil =>
          cases b with
          | false => simpa using ih (φ := []) (fun i h => by simp at h)
          | true => simpa using ih (φ := []) (fun i h => by simp at h)
      | cons c φ =>
          have sub' : Sub φ U := fun i h => by simpa using sub (i + 1) (by simpa using h)
          cases b with
          | false =>
              have c0 : c = false := by
                cases c
                · rfl
                · have := sub 0 (by simp); simp at this
              subst c0
              simpa using ih sub'
          | true => cases c <;> simp [ih sub']

/-- **The pullback composes back**: reading `φ ⊆ U` through `U` gives `φ` again. -/
theorem sel_pull {U φ : Thin} (sub : Sub φ U) {j : ℕ} (lt : j < ones φ) :
    sel U (sel (pull U φ) j) = sel φ j := by
  induction U generalizing φ j with
  | nil =>
      have := (bit_sel lt).1
      have := sub _ this; simp at this
  | cons b U ih =>
      cases φ with
      | nil => simp at lt
      | cons c φ =>
          have sub' : Sub φ U := fun i h => by simpa using sub (i + 1) (by simpa using h)
          cases b with
          | false =>
              have c0 : c = false := by
                cases c
                · rfl
                · have := sub 0 (by simp); simp at this
              subst c0
              simp [ih sub' (by simpa using lt)]
          | true =>
              cases c with
              | false => simp [ih sub' (by simpa using lt)]
              | true =>
                  cases j with
                  | zero => simp
                  | succ j => simp [ih sub' (by simp at lt; omega)]

/-! ## The edge of the smart constructor -/

/-- **The edge of a field**: for a field under `d` binders whose child is kept by `θ` (in the
field's scope), and the node's subscope `U` containing the child's outer variables, the edge
thinning is `θ`'s bound bits followed by its outer bits read in `U`. -/
def edge (d : ℕ) (U θ : Thin) : Thin := front d θ ++ pull U (back d θ)

@[simp] theorem length_edge (d : ℕ) (U θ : Thin) : (edge d U θ).length = d + ones U := by
  simp [edge]

theorem ones_edge {d : ℕ} {U θ : Thin} (sub : Sub (back d θ) U) : ones (edge d U θ) = ones θ := by
  rw [edge, ones_append, ones_pull sub, ones_front_back]

theorem back_edge (d : ℕ) (U θ : Thin) : back d (edge d U θ) = pull U (back d θ) := by
  simp [edge, back, List.drop_left' (length_front d θ)]

/-- **The edge, put back under the node's thinning, is the field's thinning** on the child's
kept variables. -/
theorem sel_edge {d : ℕ} {U θ : Thin} (sub : Sub (back d θ) U) {j : ℕ} (lt : j < ones θ) :
    sel (keepN d U) (sel (edge d U θ) j) = sel θ j := by
  unfold edge
  rw [sel_append, length_front]
  by_cases small : j < ones (front d θ)
  · rw [if_pos small]
    have below := (bit_sel small).2
    rw [length_front] at below
    rw [sel_keepN_lt U below, sel_front small]
  · rw [if_neg small, sel_keepN_add, sel_pull sub (by have := ones_front_back d θ; omega)]
    exact (sel_back (d := d) (by omega) lt).symm

/-! ## Erasing a position -/

/-- `erase d θ`: `θ` without position `d` (opening variable `d` removes it from the scope). -/
def erase : ℕ → Thin → Thin
  | _, [] => []
  | 0, _ :: θ => θ
  | d + 1, b :: θ => b :: erase d θ

@[simp] theorem erase_nil (d : ℕ) : erase d [] = [] := by cases d <;> simp [erase]
@[simp] theorem erase_zero (b : Bool) (θ : Thin) : erase 0 (b :: θ) = θ := by simp [erase]
@[simp] theorem erase_succ (d : ℕ) (b : Bool) (θ : Thin) : erase (d + 1) (b :: θ) = b :: erase d θ := by
  simp [erase]

theorem ones_erase {d : ℕ} {θ : Thin} (unused : bit θ d = false) : ones (erase d θ) = ones θ := by
  induction θ generalizing d with
  | nil => simp
  | cons b θ ih =>
      cases d with
      | zero => simp at unused; subst unused; simp
      | succ d => cases b <;> simp [ih (by simpa using unused)]

/-- Erasing an unused position: the kept variables move down past it. -/
theorem sel_erase {d : ℕ} {θ : Thin} (unused : bit θ d = false) {j : ℕ} (lt : j < ones θ) :
    sel θ j = (if sel (erase d θ) j < d then sel (erase d θ) j else sel (erase d θ) j + 1) := by
  induction θ generalizing d j with
  | nil => simp at lt
  | cons b θ ih =>
      cases d with
      | zero =>
          simp at unused; subst unused
          simp
      | succ d =>
          cases b with
          | false =>
              simp only [erase_succ, sel_false]
              rw [ih (by simpa using unused) (by simpa using lt)]
              split_ifs <;> omega
          | true =>
              cases j with
              | zero => simp
              | succ j =>
                  simp only [erase_succ, sel_true_succ]
                  rw [ih (by simpa using unused) (by simp at lt; omega)]
                  split_ifs <;> omega

theorem trimmed_erase {d : ℕ} {θ : Thin} (h : trimmed θ = true) (unused : bit θ d = false) :
    trimmed (erase d θ) = true := by
  induction θ generalizing d with
  | nil => simp
  | cons b θ ih =>
      cases d with
      | zero =>
          simp at unused; subst unused
          cases θ with
          | nil => simp at h
          | cons c θ => simpa using trimmed_tail h
      | succ d =>
          simp only [erase_succ]
          cases θ with
          | nil => simpa using h
          | cons c θ =>
              refine trimmed_cons (ih (trimmed_tail h) (by simpa using unused)) ?_
              cases d with
              | zero =>
                  intro e
                  simp at e; subst e
                  simp at unused; subst unused
                  simp at h
              | succ d => simp

/-! ## Examples -/

namespace Controls

/-- Positive: `[true, false, true]` sends variable `1` to `2`, skipping the middle variable. -/
theorem sel_example : sel [true, false, true] 1 = 2 := by decide

/-- Positive: McBride's composite (written innermost first): keeping the first and third of
three, then the first, third and fifth of five, keeps the first and fifth of five. -/
theorem comp_example :
    comp [true, false, true] [true, false, true, false, true] = [true, false, false, false, true] := by
  decide

/-- Negative: composition is not commutative. -/
theorem comp_not_comm : comp [false] [true, false] ≠ comp [true, false] [false] := by decide

/-- Positive: the union of `{0}` and `{2}` is `{0, 2}`; reading `{2}` in it gives its second
variable. -/
theorem bor_pull_example :
    bor [true] [false, false, true] = [true, false, true] ∧
      pull [true, false, true] [false, false, true] = [false, true] := by decide

/-- Negative: `[true, false]` is not trimmed; its trimmed form is `[true]`. -/
theorem trim_example : trimmed [true, false] = false ∧ cut 1 [true, false] = [true] := by decide

end Controls

end Thin

end Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
