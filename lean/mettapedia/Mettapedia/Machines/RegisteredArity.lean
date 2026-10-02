import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bitwise

/-!
# Applications of a function name, by arity

SWI-PeTTa records, for each function name, the arities at which it is
defined (`arity/2`): for a name its prelude registers, the arities of the
predicates of that name when the prelude loads; for a name the program
defines, the arities of its equations.  An application of a function name
to `n` arguments is a call when `n` is one of them, a partial application
when some recorded arity exceeds `n` or none is recorded, and an
over-application otherwise (`reference`).  A name that is neither
registered nor defined is data.

The runtime asks each of its sources of arities (the program's equations,
the registered names, the foreign boundary) four questions about a name and
a count: is the name known, is the count one of its arities, is some arity
larger, is some arity smaller (`answer`).  It combines the sources' answers
by disjunction (`Answer.or`) and reads the application from the combination
(`classify`).

* `classify_answer`: reading one source's answer is the reference's reading
  of its arities.
* `answer_append`: the disjunction of two sources' answers is the answer of
  the union of their arities.
* `classify_or`: so the runtime's reading over two sources is the
  reference's reading of the union of their arities.
* `answer_mask`: a source that keeps its arities as the set bits of a
  number answers by testing bits: the count's own bit, any bit above it,
  any bit below it.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RegisteredArity

/-- How an application of a name to some arguments is read. -/
inductive Kind
  | data
  | call
  | partialApp
  | overapplied
  deriving DecidableEq, Repr

/-- The reference's reading of an application to `n` arguments of a name,
registered or not, whose recorded arities are `arities`.  A name with a
recorded arity is always registered: defining it registers it. -/
def reference (registered : Bool) (arities : List ℕ) (n : ℕ) : Kind :=
  if registered = false ∧ arities = [] then .data
  else if n ∈ arities then .call
  else if (∃ a ∈ arities, n < a) ∨ arities = [] then .partialApp
  else .overapplied

/-- A source's answers about a name and a count. -/
structure Answer where
  known : Bool
  exact : Bool
  larger : Bool
  smaller : Bool
  deriving DecidableEq, Repr

/-- Two sources' answers, combined. -/
def Answer.or (x y : Answer) : Answer :=
  ⟨x.known || y.known, x.exact || y.exact, x.larger || y.larger,
    x.smaller || y.smaller⟩

/-- What a source whose recorded arities are `arities` answers about `n`. -/
def answer (registered : Bool) (arities : List ℕ) (n : ℕ) : Answer :=
  ⟨registered || decide (arities ≠ []), decide (n ∈ arities),
    decide (∃ a ∈ arities, n < a), decide (∃ a ∈ arities, a < n)⟩

/-- The runtime's reading from an answer. -/
def classify (x : Answer) : Kind :=
  if x.known = false then .data
  else if x.exact then .call
  else if x.larger then .partialApp
  else if x.smaller then .overapplied
  else .partialApp

/-- A count that is none of the arities, below none and above none, is
beside an empty list. -/
theorem eq_nil_of_none {arities : List ℕ} {n : ℕ}
    (hexact : n ∉ arities) (hlarger : ¬ ∃ a ∈ arities, n < a)
    (hsmaller : ¬ ∃ a ∈ arities, a < n) : arities = [] := by
  cases arities with
  | nil => rfl
  | cons a rest =>
      exfalso
      rcases lt_trichotomy a n with h | h | h
      · exact hsmaller ⟨a, List.mem_cons_self, h⟩
      · exact hexact (h ▸ List.mem_cons_self)
      · exact hlarger ⟨a, List.mem_cons_self, h⟩

/-- Reading one source's answer is the reference's reading. -/
theorem classify_answer (registered : Bool) (arities : List ℕ) (n : ℕ) :
    classify (answer registered arities n) = reference registered arities n := by
  by_cases hknown : registered = false ∧ arities = []
  · obtain ⟨hr, ha⟩ := hknown
    subst hr ha
    simp [classify, answer, reference]
  · have hk : (registered || decide (arities ≠ [])) = true := by
      cases registered <;> cases arities <;> simp_all
    by_cases hexact : n ∈ arities
    · simp [classify, answer, reference, hexact, hknown]
    · by_cases hlarger : ∃ a ∈ arities, n < a
      · simp only [classify, answer, reference, hk, hknown, hexact, hlarger]
        simp
      · by_cases hsmaller : ∃ a ∈ arities, a < n
        · have hne : arities ≠ [] := by
            rintro rfl
            obtain ⟨a, ha, -⟩ := hsmaller
            cases ha
          simp only [classify, answer, reference, hk, hexact, hlarger,
            hsmaller, hne]
          simp
        · have hnil := eq_nil_of_none hexact hlarger hsmaller
          subst hnil
          cases registered <;> simp_all [classify, answer, reference]

/-- The disjunction of two sources' answers is the answer of the union of
their arities. -/
theorem answer_append (r₁ r₂ : Bool) (a₁ a₂ : List ℕ) (n : ℕ) :
    (answer r₁ a₁ n).or (answer r₂ a₂ n) = answer (r₁ || r₂) (a₁ ++ a₂) n := by
  simp only [Answer.or, answer, List.mem_append]
  congr 1
  · cases r₁ <;> cases r₂ <;> cases a₁ <;> cases a₂ <;> simp
  · simp [Bool.decide_or]
  · simp [List.mem_append, or_and_right, exists_or, Bool.decide_or]
  · simp [List.mem_append, or_and_right, exists_or, Bool.decide_or]

/-- The runtime's reading over two sources is the reference's reading of the
union of their arities. -/
theorem classify_or (r₁ r₂ : Bool) (a₁ a₂ : List ℕ) (n : ℕ) :
    classify ((answer r₁ a₁ n).or (answer r₂ a₂ n)) =
      reference (r₁ || r₂) (a₁ ++ a₂) n := by
  rw [answer_append, classify_answer]

/-- The arities kept as the set bits of `mask`, below `width`. -/
def bits (width mask : ℕ) : List ℕ :=
  (List.range width).filter (fun a => mask.testBit a)

/-- Below its width, an arity is kept exactly when its bit is set. -/
theorem mem_bits {width mask : ℕ} (hmask : mask < 2 ^ width) (a : ℕ) :
    a ∈ bits width mask ↔ mask.testBit a = true := by
  simp only [bits, List.mem_filter, List.mem_range]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  by_contra hge
  have hlt : mask < 2 ^ a :=
    lt_of_lt_of_le hmask (Nat.pow_le_pow_right (by decide) (not_lt.mp hge))
  rw [Nat.testBit_lt_two_pow hlt] at h
  cases h

/-- A number is nonzero exactly when one of its bits is set. -/
theorem ne_zero_iff_testBit (x : ℕ) : x ≠ 0 ↔ ∃ a, x.testBit a = true := by
  refine ⟨Nat.exists_testBit_of_ne_zero, ?_⟩
  rintro ⟨a, ha⟩ rfl
  simp at ha

/-- Some kept arity lies above `n` exactly when the mask shifted past `n` is
nonzero. -/
theorem larger_iff {width mask : ℕ} (hmask : mask < 2 ^ width) (n : ℕ) :
    (∃ a ∈ bits width mask, n < a) ↔ mask >>> (n + 1) ≠ 0 := by
  rw [ne_zero_iff_testBit]
  simp only [Nat.testBit_shiftRight]
  constructor
  · rintro ⟨a, ha, hlt⟩
    refine ⟨a - (n + 1), ?_⟩
    rw [Nat.add_sub_cancel' hlt]
    exact (mem_bits hmask a).mp ha
  · rintro ⟨i, hi⟩
    exact ⟨n + 1 + i, (mem_bits hmask _).mpr hi, by omega⟩

/-- Some kept arity lies below `n` exactly when the mask's bits below `n` are
not all clear. -/
theorem smaller_iff {width mask : ℕ} (hmask : mask < 2 ^ width) (n : ℕ) :
    (∃ a ∈ bits width mask, a < n) ↔ mask % 2 ^ n ≠ 0 := by
  rw [ne_zero_iff_testBit]
  simp only [Nat.testBit_mod_two_pow, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨a, ha, hlt⟩
    exact ⟨a, hlt, (mem_bits hmask a).mp ha⟩
  · rintro ⟨a, hlt, ha⟩
    exact ⟨a, (mem_bits hmask a).mpr ha, hlt⟩

/-- A mask's bits, below its width, answer by testing bits: whether any is
set, the count's own bit, whether any above it is set, whether any below
it is set. -/
theorem answer_mask (registered : Bool) (width mask n : ℕ)
    (hmask : mask < 2 ^ width) :
    answer registered (bits width mask) n =
      ⟨registered || decide (mask ≠ 0), mask.testBit n,
        decide (mask >>> (n + 1) ≠ 0), decide (mask % 2 ^ n ≠ 0)⟩ := by
  have hnil : bits width mask ≠ [] ↔ mask ≠ 0 := by
    rw [ne_zero_iff_testBit]
    constructor
    · intro h
      obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ h
      exact ⟨a, (mem_bits hmask a).mp ha⟩
    · rintro ⟨a, ha⟩
      exact List.ne_nil_of_mem ((mem_bits hmask a).mpr ha)
  simp only [answer, Answer.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [hnil]
  · cases h : mask.testBit n
    · have : n ∉ bits width mask := fun hn => by
        rw [(mem_bits hmask n).mp hn] at h
        cases h
      simp [this]
    · simp [(mem_bits hmask n).mpr h]
  · simp only [larger_iff hmask]
  · simp only [smaller_iff hmask]

namespace Controls

/-- `max`: the prelude's arity 2 and a program's equation of arity 1. -/
theorem max_program_equation :
    classify ((answer true [2] 1).or (answer true [1] 1)) = .call := by decide

/-- `max` with one argument and no equation of arity 1 is partial. -/
theorem max_one_argument : reference true [2] 1 = .partialApp := by decide

/-- `max` with three arguments is over-applied. -/
theorem max_three_arguments : reference true [2] 3 = .overapplied := by decide

/-- `sqrt` is registered with no arity: every application is partial. -/
theorem sqrt_any : reference true [] 1 = .partialApp := by decide

/-- An unregistered, undefined name is data. -/
theorem unknown_name : reference false [] 1 = .data := by decide

end Controls

end Mettapedia.Machines.RegisteredArity
