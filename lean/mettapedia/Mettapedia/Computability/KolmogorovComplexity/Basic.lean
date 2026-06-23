import Mathlib.Data.Nat.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.List.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecCode
import Mathlib.Algebra.Order.Ring.GeomSum
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Kolmogorov Complexity - Basic Definitions

This file defines plain Kolmogorov complexity `C[U](x)` for (partial) algorithms
`U : BinString →. BinString`, and constructs a universal algorithm using mathlib's
`Nat.Partrec.Code.eval`.

We use binary strings (`List Bool`) to match the Solomonoff development.
-/

namespace KolmogorovComplexity

open scoped Classical

/-- Binary strings are lists of booleans. -/
abbrev BinString := List Bool

/-- A (partial) algorithm mapping programs to outputs. -/
abbrev Algorithm := BinString →. BinString

/-! ## Plain Kolmogorov Complexity `C[U](x)` -/

/-- The set of program lengths that produce output `x` under algorithm `U`. -/
def lengthsFor (U : Algorithm) (x : BinString) : Set ℕ :=
  {n | ∃ p : BinString, x ∈ U p ∧ p.length = n}

/-- Plain Kolmogorov complexity with respect to algorithm `U`:
`C[U](x) := min{|p| : x ∈ U(p)}`.

If `x` is not in the range of `U`, the infimum is `0` by convention. -/
noncomputable def plainComplexity (U : Algorithm) (x : BinString) : ℕ :=
  sInf (lengthsFor U x)

notation "C[" U "](" x ")" => plainComplexity U x

/-- The set of programs that produce output `x` under algorithm `U`. -/
def programsFor (U : Algorithm) (x : BinString) : Set BinString :=
  {p | x ∈ U p}

theorem complexity_nonneg (U : Algorithm) (x : BinString) : 0 ≤ C[U](x) :=
  Nat.zero_le _

/-- If `x ∈ U(p)`, then `C[U](x) ≤ |p|`. -/
theorem complexity_le_of_program (U : Algorithm) (x : BinString) (p : BinString)
    (h : x ∈ U p) : C[U](x) ≤ p.length := by
  unfold plainComplexity
  exact Nat.sInf_le ⟨p, h, rfl⟩

/-- If `x` is produced by some program, then there is a shortest program of length `C[U](x)`. -/
theorem exists_program_of_complexity (U : Algorithm) (x : BinString)
    (hx : ∃ p : BinString, x ∈ U p) :
    ∃ p : BinString, x ∈ U p ∧ p.length = C[U](x) := by
  classical
  have hnonempty : (lengthsFor U x).Nonempty := by
    rcases hx with ⟨p, hp⟩
    exact ⟨p.length, ⟨p, hp, rfl⟩⟩
  have hm : C[U](x) ∈ lengthsFor U x := by
    simpa [plainComplexity] using Nat.sInf_mem hnonempty
  rcases hm with ⟨p, hp, hp_len⟩
  exact ⟨p, hp, hp_len⟩

/-- The identity algorithm. -/
def identityAlgorithm : Algorithm :=
  fun p => Part.some p

theorem identityAlgorithm_partrec : Partrec identityAlgorithm :=
  (Computable.id).partrec

/-- For the identity algorithm, `C(x) = |x|`. -/
theorem complexity_identity (x : BinString) : C[identityAlgorithm](x) = x.length := by
  unfold plainComplexity lengthsFor identityAlgorithm
  have :
      {n | ∃ p : BinString, x ∈ (Part.some p : Part BinString) ∧ p.length = n} = {x.length} := by
    ext n
    constructor
    · rintro ⟨p, hp, hp_len⟩
      have hx : x = p := (Part.mem_some_iff).1 hp
      have : x.length = n := by simpa [hx] using hp_len
      exact Set.mem_singleton_iff.2 this.symm
    · intro hn
      rcases Set.mem_singleton_iff.1 hn with rfl
      refine ⟨x, ?_, rfl⟩
      simp
  rw [this]
  simp [csInf_singleton]

/-! ## Universal Algorithms (via prefix coding of an index) -/

/-- `U` is universal if it can simulate any partial recursive algorithm `V` by prefixing a fixed
codeword to the program. -/
def IsUniversal (U : Algorithm) : Prop :=
  ∀ V : Algorithm, Partrec V → ∃ code : BinString, ∀ p x : BinString, x ∈ V p → x ∈ U (code ++ p)

/-- If `U` is universal and `x` is in the range of `V`, then `C[U](x) ≤ C[V](x) + O(1)`. -/
theorem universal_complexity_le_of_code (U V : Algorithm) (code : BinString)
    (hcode : ∀ p x : BinString, x ∈ V p → x ∈ U (code ++ p)) (x : BinString)
    (hx : ∃ p : BinString, x ∈ V p) :
    C[U](x) ≤ C[V](x) + code.length := by
  classical
  rcases exists_program_of_complexity V x hx with ⟨p, hp_out, hp_len⟩
  have hxU : x ∈ U (code ++ p) := hcode p x hp_out
  have hlen : C[U](x) ≤ (code ++ p).length :=
    complexity_le_of_program U x (code ++ p) hxU
  calc
    C[U](x) ≤ (code ++ p).length := hlen
    _ = code.length + p.length := by simp [List.length_append]
    _ = code.length + C[V](x) := by simp [hp_len]
    _ = C[V](x) + code.length := by simp [Nat.add_comm]

theorem universal_complexity_le (U V : Algorithm) (hU : IsUniversal U) (hV : Partrec V)
    (x : BinString) (hx : ∃ p : BinString, x ∈ V p) :
    ∃ c : ℕ, C[U](x) ≤ C[V](x) + c := by
  classical
  obtain ⟨code, hcode⟩ := hU V hV
  refine ⟨code.length, universal_complexity_le_of_code U V code hcode x hx⟩

/-- Invariance theorem (for universal, partial recursive algorithms). -/
theorem invariance_theorem (U V : Algorithm) (hU : IsUniversal U) (hUrec : Partrec U)
    (hV : IsUniversal V) (hVrec : Partrec V) :
    (∃ c : ℕ, ∀ x, C[U](x) ≤ C[V](x) + c) ∧
    (∃ c : ℕ, ∀ x, C[V](x) ≤ C[U](x) + c) := by
  constructor
  · obtain ⟨code, hcode⟩ := hU V hVrec
    refine ⟨code.length, ?_⟩
    intro x
    have hx : ∃ p : BinString, x ∈ V p := by
      obtain ⟨c', hc'⟩ := hV identityAlgorithm identityAlgorithm_partrec
      refine ⟨c' ++ x, ?_⟩
      have : x ∈ identityAlgorithm x := by simp [identityAlgorithm]
      exact hc' x x this
    exact universal_complexity_le_of_code U V code hcode x hx
  · obtain ⟨code, hcode⟩ := hV U hUrec
    refine ⟨code.length, ?_⟩
    intro x
    have hx : ∃ p : BinString, x ∈ U p := by
      obtain ⟨c', hc'⟩ := hU identityAlgorithm identityAlgorithm_partrec
      refine ⟨c' ++ x, ?_⟩
      have : x ∈ identityAlgorithm x := by simp [identityAlgorithm]
      exact hc' x x this
    exact universal_complexity_le_of_code V U code hcode x hx

/-! ## A concrete universal algorithm from `Nat.Partrec.Code.eval` -/

/-- Unary prefix code: `n` times `true` followed by a delimiter `false`. -/
def machinePrefix : ℕ → BinString
  | 0 => [false]
  | n + 1 => true :: machinePrefix n

/-- Decode a unary prefix code, returning the index and the remaining program. -/
def decodeMachinePrefix : BinString → Option (ℕ × BinString)
  | [] => none
  | false :: rest => some (0, rest)
  | true :: rest => do
    let ⟨n, tail⟩ ← decodeMachinePrefix rest
    pure (n + 1, tail)

theorem decodeMachinePrefix_machinePrefix (n : ℕ) (p : BinString) :
    decodeMachinePrefix (machinePrefix n ++ p) = some (n, p) := by
  induction n with
  | zero =>
    simp [machinePrefix, decodeMachinePrefix]
  | succ n ih =>
    simp [machinePrefix, decodeMachinePrefix, ih]

/-- The universal algorithm: interpret the unary prefix as a `Nat.Partrec.Code` index and run it. -/
noncomputable def universalAlgorithm : Algorithm :=
  fun prog =>
    match decodeMachinePrefix prog with
    | none => Part.none
    | some (n, p) =>
      (Nat.Partrec.Code.eval (Nat.Partrec.Code.ofNatCode n) (Encodable.encode p)).bind fun out =>
        Part.ofOption (Encodable.decode (α := BinString) out)

theorem universalAlgorithm_is_universal : IsUniversal universalAlgorithm := by
  classical
  intro V hV
  -- Unfold `Partrec V` to a `Nat.Partrec` statement so we can extract a code.
  unfold Partrec at hV
  obtain ⟨c, hc⟩ := (Nat.Partrec.Code.exists_code).1 hV
  refine ⟨machinePrefix (Nat.Partrec.Code.encodeCode c), ?_⟩
  intro p x hx
  have hparse :
      decodeMachinePrefix (machinePrefix (Nat.Partrec.Code.encodeCode c) ++ p) =
        some (Nat.Partrec.Code.encodeCode c, p) :=
    decodeMachinePrefix_machinePrefix _ _
  have hcode : Nat.Partrec.Code.ofNatCode (Nat.Partrec.Code.encodeCode c) = c := by
    simpa [Nat.Partrec.Code.encodeCode_eq, Nat.Partrec.Code.ofNatCode_eq] using
      (Denumerable.ofNat_encode (α := Nat.Partrec.Code) c)
  have hc_apply :
      Nat.Partrec.Code.eval c (Encodable.encode p) = (V p).map Encodable.encode := by
    have hc' := congrArg (fun f => f (Encodable.encode p)) hc
    -- Reduce the unfolded `Partrec` definition using `decode (encode p) = some p`.
    simpa using hc'
  have hx_enc : Encodable.encode x ∈ Nat.Partrec.Code.eval c (Encodable.encode p) := by
    simpa [hc_apply] using (Part.mem_map Encodable.encode hx)
  have hx_dec : x ∈ Part.ofOption (Encodable.decode (α := BinString) (Encodable.encode x)) := by
    simp
  have hxU :
      x ∈ (Nat.Partrec.Code.eval c (Encodable.encode p)).bind
            (fun out => Part.ofOption (Encodable.decode (α := BinString) out)) :=
    Part.mem_bind hx_enc hx_dec
  simpa [universalAlgorithm, hparse, hcode] using hxU

theorem exists_optimal_algorithm : ∃ U : Algorithm, IsUniversal U :=
  ⟨universalAlgorithm, universalAlgorithm_is_universal⟩

/-! ## Kolmogorov complexity `K(x)` -/

/-- Fix a universal algorithm and define `K(x) := C[U](x)`. -/
noncomputable def kolmogorovComplexity : BinString → ℕ :=
  plainComplexity (Classical.choose exists_optimal_algorithm)

notation "K(" x ")" => kolmogorovComplexity x

theorem universal_is_universal : IsUniversal (Classical.choose exists_optimal_algorithm) :=
  Classical.choose_spec exists_optimal_algorithm

theorem kolmogorov_le_length_plus_const : ∃ c : ℕ, ∀ x : BinString, K(x) ≤ x.length + c := by
  classical
  let U := Classical.choose exists_optimal_algorithm
  have hU : IsUniversal U := universal_is_universal
  obtain ⟨code, hcode⟩ := hU identityAlgorithm identityAlgorithm_partrec
  refine ⟨code.length, ?_⟩
  intro x
  have hx : x ∈ identityAlgorithm x := by simp [identityAlgorithm]
  have hxU : x ∈ U (code ++ x) := hcode x x hx
  have hlen : K(x) ≤ (code ++ x).length :=
    complexity_le_of_program U x (code ++ x) hxU
  simpa [kolmogorovComplexity, List.length_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hlen

/-- Most strings are incompressible: there exists a length-`n` string with `K(x) ≥ n - k`. -/
theorem most_strings_incompressible (n k : ℕ) (hk : 0 < k) :
    ∃ x : BinString, x.length = n ∧ K(x) ≥ n - k := by
  classical
  let m : ℕ := n - k
  by_cases hm0 : m = 0
  · refine ⟨List.replicate n false, by simp, ?_⟩
    simp [m, hm0]
  · have hm_pos : 0 < m := Nat.pos_of_ne_zero hm0
    have hm_lt_n : m < n := by
      have hn_pos : 0 < n := by
        by_contra hn0
        have hn0' : n = 0 := Nat.eq_zero_of_not_pos hn0
        subst hn0'
        have hm_pos' := hm_pos
        simp [m] at hm_pos'
      have : n - k < n := tsub_lt_self hn_pos hk
      simpa [m] using this
    let Strings : Type := List.Vector Bool n
    let Programs : Type := Σ l : Fin m, List.Vector Bool l.1
    have card_strings : Fintype.card Strings = 2 ^ n := by
      simp [Strings, card_vector]
    have card_programs_lt_pow : Fintype.card Programs < 2 ^ m := by
      have hcard : Fintype.card Programs = ∑ l : Fin m, (2 : ℕ) ^ (l : ℕ) := by
        simp [Programs, Fintype.card_sigma, card_vector]
      have hsum_range : (∑ t ∈ Finset.range m, (2 : ℕ) ^ t) < (2 : ℕ) ^ m := by
        refine Nat.geomSum_lt (m := 2) (n := m) (s := Finset.range m) (by decide) ?_
        intro t ht
        exact (Finset.mem_range.1 ht)
      have hsum_fin : (∑ l : Fin m, (2 : ℕ) ^ (l : ℕ)) < (2 : ℕ) ^ m := by
        simpa [Fin.sum_univ_eq_sum_range] using hsum_range
      exact hcard ▸ hsum_fin
    have card_programs_lt : Fintype.card Programs < Fintype.card Strings := by
      have pow_lt : (2 : ℕ) ^ m < (2 : ℕ) ^ n :=
        (Nat.pow_lt_pow_iff_right (by decide : 1 < (2 : ℕ))).2 hm_lt_n
      have : Fintype.card Programs < (2 : ℕ) ^ n := card_programs_lt_pow.trans pow_lt
      simpa [card_strings] using this
    let U := Classical.choose exists_optimal_algorithm
    have hU : IsUniversal U := Classical.choose_spec exists_optimal_algorithm
    obtain ⟨code, hcode⟩ := hU identityAlgorithm identityAlgorithm_partrec
    have U_total : ∀ x : BinString, ∃ p : BinString, x ∈ U p := by
      intro x
      refine ⟨code ++ x, ?_⟩
      have : x ∈ identityAlgorithm x := by simp [identityAlgorithm]
      exact hcode x x this
    have : ∃ x : Strings, m ≤ K(x.1) := by
      by_contra hAll
      have hAll' : ∀ x : Strings, K(x.1) < m := by
        intro x
        by_contra hx
        exact hAll ⟨x, le_of_not_gt hx⟩
      -- Choose a shortest program (of length `K(x)`) for each length-`n` string.
      let shortest : BinString → BinString := fun x =>
        Classical.choose (exists_program_of_complexity U x (U_total x))
      have shortest_spec (x : BinString) :
          x ∈ U (shortest x) ∧ (shortest x).length = K(x) := by
        simpa [shortest, kolmogorovComplexity] using
          (Classical.choose_spec (exists_program_of_complexity U x (U_total x)))
      let f : Strings → Programs := fun s =>
        let x := s.1
        have hxlt : K(x) < m := hAll' s
        have hp_len : (shortest x).length = K(x) := (shortest_spec x).2
        have hp_lt : (shortest x).length < m := by simpa [hp_len] using hxlt
        ⟨⟨(shortest x).length, hp_lt⟩, ⟨shortest x, rfl⟩⟩
      have finj : Function.Injective f := by
        intro s₁ s₂ h
        have hp :
            shortest s₁.1 = shortest s₂.1 :=
          congrArg (fun q : Programs => q.2.1) h
        have hx₁ : s₁.1 ∈ U (shortest s₁.1) := (shortest_spec s₁.1).1
        have hx₂ : s₂.1 ∈ U (shortest s₂.1) := (shortest_spec s₂.1).1
        have hxs : s₁.1 = s₂.1 := by
          exact Part.mem_unique hx₁ (by simpa [hp] using hx₂)
        exact Subtype.ext hxs
      have card_le : Fintype.card Strings ≤ Fintype.card Programs :=
        Fintype.card_le_of_injective f finj
      exact (not_lt_of_ge card_le) card_programs_lt
    rcases this with ⟨x, hx⟩
    refine ⟨x.1, x.2, ?_⟩
    simpa [m] using hx

end KolmogorovComplexity
