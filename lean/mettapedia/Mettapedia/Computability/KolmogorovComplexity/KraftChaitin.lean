import Mettapedia.Computability.KolmogorovComplexity.ConditionalChainRule

/-!
# Effective Kraft–Chaitin allocation

This file gives an *executable* online allocator for prefix codes together
with its correctness proof: the canonical left-packed frontier allocator.

The allocator state keeps a list `frontier` of free prefixes whose lengths
are strictly decreasing.  To satisfy a request for a codeword of length
`n`, it selects the first free prefix `p` with `p.length ≤ n` and allocates
`p ++ replicate (n - p.length) false`; the one-branches
`p ++ replicate k false ++ [true]` for `k < n - p.length` are retained in
the frontier, deepest first.

Development:

* `siblingsOf`: the retained one-branches, with exact lengths, pairwise
  prefix-incomparability (also against the allocated zero-extension), and
  the common-denominator Nat capacity identity
  `2^(L - |p|) = 2^(L - n) + Σ siblings`, i.e. no `Real` anywhere.
* `StateInv`: the online invariant — pairwise prefix-freeness of the
  allocated codewords and of the frontier, cross-incomparability, strictly
  decreasing frontier lengths, length bounds, and exact capacity
  conservation against an explicit total `capTotal`.
* `allocStep_preserves`: one successful allocation step preserves the
  invariant for any request `n ≤ L`.
* `allocStep_success`: if the Kraft ledger has room for the next request
  (`Σ alloc + 2^(L-n) ≤ capTotal`), allocation cannot fail.  The strict
  geometric bound behind it is `sorted_gt_cap_sum_le`: a strictly
  decreasing list of lengths inside `(n, L]` contributes strictly less
  than `2^(L-n)`.

The allocator is plain structural recursion on lists, hence executable;
worked examples at the end check the trace by kernel evaluation, including
failure cases once the Kraft budget is violated.
-/

namespace KolmogorovComplexity

namespace KraftChaitin

/-- Two strings are prefix-incomparable. -/
def Incomp (a b : BinString) : Prop := ¬ (a <+: b) ∧ ¬ (b <+: a)

theorem Incomp.symm {a b : BinString} (h : Incomp a b) : Incomp b a := ⟨h.2, h.1⟩

/-- Incomparability extends to any extension of the right operand. -/
theorem Incomp.of_prefix_right {a p c : BinString} (h : Incomp a p) (hpc : p <+: c) :
    Incomp a c := by
  constructor
  · intro hac
    rcases prefixes_comparable hac hpc with hap | hpa
    · exact h.1 hap
    · exact h.2 hpa
  · intro hca
    exact h.2 (hpc.trans hca)

/-- Incomparability extends to any extension of the left operand. -/
theorem Incomp.of_prefix_left {p b c : BinString} (h : Incomp p b) (hpc : p <+: c) :
    Incomp c b :=
  ((Incomp.symm h).of_prefix_right hpc).symm

/-- The length of a retained sibling marker path. -/
theorem length_marker (p : BinString) (j : Nat) :
    (p ++ List.replicate j false ++ [true]).length = p.length + j + 1 := by
  simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil]

/-- The length of a zeros-extended prefix. -/
theorem length_zeros (p : BinString) (d : Nat) :
    (p ++ List.replicate d false).length = p.length + d := by
  simp only [List.length_append, List.length_replicate]

/-- Pointwise lookup along a prefix. -/
theorem IsPrefix.getElem?_of_prefix {a b : BinString} (h : a <+: b) (i : Nat)
    (hi : i < a.length) : b[i]? = a[i]? := by
  obtain ⟨t, rfl⟩ := h
  rw [List.getElem?_append_left hi]

/-- The marker bit of a retained sibling `p ++ replicate j false ++ [true]`
at position `p.length + j`. -/
theorem getElem?_marker_true (p : BinString) (j : Nat) :
    (p ++ List.replicate j false ++ [true])[p.length + j]? = some true := by
  have hlen := length_zeros p j
  rw [List.getElem?_append_right (by rw [hlen]), hlen, Nat.sub_self]
  rfl

/-- Along a zero path, every interior position reads `false`. -/
theorem getElem?_zeros (p : BinString) (d j : Nat) (hjd : j < d) :
    (p ++ List.replicate d false)[p.length + j]? = some false := by
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_replicate]
  simp [hjd]

/-- A retained sibling and the allocated zero-extension are
prefix-incomparable. -/
theorem incomp_marker_zeros {p : BinString} {j d : Nat} (hjd : j < d) :
    Incomp (p ++ List.replicate j false ++ [true]) (p ++ List.replicate d false) := by
  constructor
  · intro h
    have h1 := IsPrefix.getElem?_of_prefix h (p.length + j)
      (by rw [length_marker]; omega)
    rw [getElem?_zeros p d j hjd, getElem?_marker_true p j] at h1
    exact Bool.noConfusion (Option.some.inj h1)
  · intro h
    have h1 := IsPrefix.getElem?_of_prefix h (p.length + j) (by rw [length_zeros]; omega)
    rw [getElem?_marker_true p j, getElem?_zeros p d j hjd] at h1
    exact Bool.noConfusion (Option.some.inj h1)

/-- The marker of the shallower sibling sits inside the zero strip of the
deeper one: two distinct retained siblings are prefix-incomparable. -/
theorem incomp_markers {p : BinString} {j k : Nat} (hjk : j < k) :
    Incomp (p ++ List.replicate j false ++ [true])
      (p ++ List.replicate k false ++ [true]) := by
  constructor
  · intro h
    have h1 := IsPrefix.getElem?_of_prefix h (p.length + j) (by rw [length_marker]; omega)
    have h2 : (p ++ List.replicate k false ++ [true])[p.length + j]? = some false := by
      have hlen := length_zeros p k
      rw [List.getElem?_append_left (by rw [hlen]; omega), getElem?_zeros p k j hjk]
    rw [h2, getElem?_marker_true p j] at h1
    exact Bool.noConfusion (Option.some.inj h1)
  · intro h
    have h1 := IsPrefix.getElem?_of_prefix h (p.length + k) (by rw [length_marker]; omega)
    have h2 : (p ++ List.replicate j false ++ [true])[p.length + k]? = none :=
      List.getElem?_eq_none (by rw [length_marker]; omega)
    rw [h2, getElem?_marker_true p k] at h1
    simp at h1

/-- The retained one-branches of `p` along a zero path of depth `d`,
ordered deepest to shallowest; the element with `j` zeros has length
`p.length + j + 1`. -/
def siblingsOf (p : BinString) : Nat → List BinString
  | 0 => []
  | d + 1 => (p ++ List.replicate d false ++ [true]) :: siblingsOf p d

theorem siblingsOf_mem {p q : BinString} {d : Nat} :
    q ∈ siblingsOf p d ↔ ∃ j, j < d ∧ q = p ++ List.replicate j false ++ [true] := by
  induction d with
  | zero => simp [siblingsOf]
  | succ d ih =>
      simp only [siblingsOf, List.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨j, hjd, rfl⟩)
        · exact ⟨d, Nat.lt_succ_self d, rfl⟩
        · exact ⟨j, by omega, rfl⟩
      · rintro ⟨j, hjd, rfl⟩
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hjd) with hjlt | rfl
        · exact Or.inr ⟨j, hjlt, rfl⟩
        · exact Or.inl rfl

theorem siblingsOf_length_le {p q : BinString} {d : Nat} (hq : q ∈ siblingsOf p d) :
    q.length ≤ p.length + d := by
  rcases siblingsOf_mem.mp hq with ⟨j, hjd, rfl⟩
  rw [length_marker]
  omega

theorem siblingsOf_extends {p q : BinString} {d : Nat} (hq : q ∈ siblingsOf p d) :
    p <+: q := by
  rcases siblingsOf_mem.mp hq with ⟨j, _hjd, rfl⟩
  exact ⟨List.replicate j false ++ [true], (List.append_assoc _ _ _).symm⟩

theorem siblingsOf_pairwise (p : BinString) (d : Nat) :
    (siblingsOf p d).Pairwise Incomp := by
  induction d with
  | zero => simp [siblingsOf]
  | succ d ih =>
      simp only [siblingsOf, List.pairwise_cons]
      refine ⟨?_, ih⟩
      intro q hq
      rcases siblingsOf_mem.mp hq with ⟨j, hjd, rfl⟩
      exact (incomp_markers hjd).symm

/-- Frontier decreasingness is expressed as a pairwise length comparison. -/
def FrontierSorted (fr : List BinString) : Prop :=
  fr.Pairwise fun a b => a.length > b.length

theorem siblingsOf_sorted (p : BinString) (d : Nat) :
    FrontierSorted (siblingsOf p d) := by
  induction d with
  | zero => simp [siblingsOf, FrontierSorted]
  | succ d ih =>
      simp only [siblingsOf, FrontierSorted, List.pairwise_cons]
      refine ⟨?_, ih⟩
      intro q hq
      rcases siblingsOf_mem.mp hq with ⟨j, hjd, rfl⟩
      simp only [length_marker, gt_iff_lt]
      omega

/-- Doubling a power of two.  Local helper for the capacity ledger. -/
theorem two_pow_add_self (m : Nat) : 2 ^ m + 2 ^ m = 2 ^ (m + 1) := by
  rw [pow_succ]; ring

/-- Exact capacity conservation of one split: the retained siblings carry
precisely the capacity lost between the free prefix and the codeword. -/
theorem siblingsOf_cap_sum (p : BinString) (d L : Nat) (hd : p.length + d ≤ L) :
    ((siblingsOf p d).map fun q => 2 ^ (L - q.length)).sum =
      2 ^ (L - p.length) - 2 ^ (L - p.length - d) := by
  induction d with
  | zero => simp [siblingsOf]
  | succ d ih =>
      have hd' : p.length + d ≤ L := by omega
      have hfl : siblingsOf p (d + 1) =
          (p ++ List.replicate d false ++ [true]) :: siblingsOf p d := rfl
      rw [hfl, List.map_cons, List.sum_cons]
      have e0 := ih hd'
      rw [length_marker]
      have e4 : L - (p.length + d + 1) = L - p.length - (d + 1) := by omega
      have e2 : 2 ^ (L - p.length - (d + 1)) + 2 ^ (L - p.length - (d + 1)) =
          2 ^ (L - p.length - d) := by
        have h : L - p.length - (d + 1) + 1 = L - p.length - d := by omega
        rw [two_pow_add_self, h]
      have e5 : 2 ^ (L - p.length - d) ≤ 2 ^ (L - p.length) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      rw [e4]
      rw [e0]
      set X := 2 ^ (L - List.length p - (d + 1)) with _hX
      set Y := 2 ^ (L - List.length p - d) with _hY
      set Z := 2 ^ (L - List.length p) with _hZ
      clear_value X Y Z
      omega

/-- One allocation step: find the first free prefix short enough, extend it
along zeros to length `n`, and retain the one-branches. -/
def allocStep : List BinString → Nat → Option (BinString × List BinString)
  | [], _ => none
  | p :: rest, n =>
      if p.length ≤ n then
        some (p ++ List.replicate (n - p.length) false, siblingsOf p (n - p.length) ++ rest)
      else
        (allocStep rest n).map fun r => (r.1, p :: r.2)

theorem allocStep_eq_none_of_forall {fr : List BinString} {n : Nat}
    (h : ∀ q ∈ fr, ¬ q.length ≤ n) : allocStep fr n = none := by
  induction fr with
  | nil => rfl
  | cons p rest ih =>
      have hp : ¬ p.length ≤ n := h p List.mem_cons_self
      simp [allocStep, hp, ih (fun q hq => h q (List.mem_cons_of_mem _ hq))]

theorem allocStep_none_forall {fr : List BinString} {n : Nat}
    (h : allocStep fr n = none) : ∀ q ∈ fr, ¬ q.length ≤ n := by
  induction fr with
  | nil => simp
  | cons p rest ih =>
      intro q hq
      by_cases hp : p.length ≤ n
      · simp [allocStep, hp] at h
      · have hrest : allocStep rest n = none := by
          cases hstep : allocStep rest n with
          | none => rfl
          | some r => simp [allocStep, hp, hstep] at h
        rcases List.mem_cons.mp hq with rfl | hq'
        · exact hp
        · exact ih hrest q hq'

/-- Every element of the post-step frontier was already free, or extends a
previously free prefix as a retained sibling of length at most `n`. -/
theorem allocStep_mem_extends {fr : List BinString} {n : Nat} {c : BinString}
    {fr' : List BinString} (h : allocStep fr n = some (c, fr')) {q : BinString}
    (hq : q ∈ fr') :
    q ∈ fr ∨ ∃ p₀ ∈ fr, p₀ <+: q ∧ q.length ≤ n := by
  induction fr generalizing c fr' with
  | nil => simp [allocStep] at h
  | cons p rest ih =>
      by_cases hp : p.length ≤ n
      · simp only [allocStep, if_pos hp, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_hc, hfr'⟩ := h
        subst hfr'
        rcases List.mem_append.mp hq with hq | hq
        · exact Or.inr ⟨p, List.mem_cons_self, siblingsOf_extends hq,
            (siblingsOf_length_le hq).trans (by omega)⟩
        · exact Or.inl (List.mem_cons_of_mem _ hq)
      · simp only [allocStep, if_neg hp] at h
        rcases hmap : allocStep rest n with _ | ⟨c₀, fr₀⟩
        · rw [hmap] at h; simp at h
        · rw [hmap] at h
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨_hc, hfr'⟩ := h
          subst hfr'
          rcases List.mem_cons.mp hq with rfl | hq
          · exact Or.inl List.mem_cons_self
          · rcases ih hmap hq with hqr | ⟨p₀, hp₀, hpre, hlen⟩
            · exact Or.inl (List.mem_cons_of_mem _ hqr)
            · exact Or.inr ⟨p₀, List.mem_cons_of_mem _ hp₀, hpre, hlen⟩

/-- The allocated codeword extends the split prefix and has exactly length
`n`. -/
theorem allocStep_code_extends {fr : List BinString} {n : Nat} {c : BinString}
    {fr' : List BinString} (h : allocStep fr n = some (c, fr')) :
    ∃ p₀ ∈ fr, p₀ <+: c ∧ c.length = n := by
  induction fr generalizing c fr' with
  | nil => simp [allocStep] at h
  | cons p rest ih =>
      by_cases hp : p.length ≤ n
      · simp only [allocStep, if_pos hp, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hc, _hfr'⟩ := h
        subst hc
        exact ⟨p, List.mem_cons_self,
          ⟨List.replicate (n - p.length) false, rfl⟩, by rw [length_zeros]; omega⟩
      · simp only [allocStep, if_neg hp] at h
        rcases hmap : allocStep rest n with _ | ⟨c₀, fr₀⟩
        · rw [hmap] at h; simp at h
        · rw [hmap] at h
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hc, _hfr'⟩ := h
          subst hc
          rcases ih hmap with ⟨p₀, hp₀, hpre, hlen⟩
          exact ⟨p₀, List.mem_cons_of_mem _ hp₀, hpre, hlen⟩

/-- The allocator with its codeword ledger. -/
structure State where
  allocated : List BinString
  frontier : List BinString

/-- The online Kraft–Chaitin invariant, relative to a common denominator
level `L` and an explicit total capacity `capTotal`. -/
structure StateInv (L : Nat) (s : State) (capTotal : Nat) : Prop where
  allocated_lengths : ∀ a ∈ s.allocated, a.length ≤ L
  frontier_lengths : ∀ p ∈ s.frontier, p.length ≤ L
  allocated_pf : s.allocated.Pairwise Incomp
  frontier_pf : s.frontier.Pairwise Incomp
  cross : ∀ a ∈ s.allocated, ∀ p ∈ s.frontier, Incomp a p
  frontier_sorted : FrontierSorted s.frontier
  conservation : ((s.frontier.map fun q => 2 ^ (L - q.length)).sum +
    (s.allocated.map fun a => 2 ^ (L - a.length)).sum) = capTotal

/-- The empty allocator at level `L`. -/
theorem stateInv_initial (L : Nat) : StateInv L ⟨[], [[]]⟩ (2 ^ L) where
  allocated_lengths := by simp
  frontier_lengths := by simp
  allocated_pf := by simp
  frontier_pf := by simp
  cross := by simp
  frontier_sorted := by simp [FrontierSorted]
  conservation := by simp

/-- The invariant restricted to a tail of the frontier, with the consumed
capacity removed from the total. -/
theorem StateInv.of_cons {L capTotal : Nat} {alloc : List BinString}
    {p : BinString} {rest : List BinString}
    (h : StateInv L ⟨alloc, p :: rest⟩ capTotal) :
    StateInv L ⟨alloc, rest⟩ (capTotal - 2 ^ (L - p.length)) := by
  obtain ⟨halen, hflen, hpfA, hpfF, hcr, hsr, hcons⟩ := h
  have hsr' : FrontierSorted (p :: rest) := hsr
  simp only [FrontierSorted] at hsr'
  rw [List.pairwise_cons] at hsr'
  have hpfF' : (p :: rest).Pairwise Incomp := hpfF
  rw [List.pairwise_cons] at hpfF'
  have hcons' : (((p :: rest).map fun q => 2 ^ (L - q.length)).sum +
      (alloc.map fun a => 2 ^ (L - a.length)).sum) = capTotal := hcons
  simp only [List.map_cons, List.sum_cons] at hcons'
  refine ⟨halen, fun q hq => hflen q (List.mem_cons_of_mem _ hq), hpfA, hpfF'.2,
    fun a ha q hq => hcr a ha q (List.mem_cons_of_mem _ hq), hsr'.2, ?_⟩
  show ((rest.map fun q => 2 ^ (L - q.length)).sum +
    (alloc.map fun a => 2 ^ (L - a.length)).sum) = capTotal - 2 ^ (L - p.length)
  omega

/-- One successful allocation step preserves the invariant. -/
theorem allocStep_preserves {L n : Nat} (hL : n ≤ L) :
    ∀ (fr : List BinString) (alloc : List BinString) (c : BinString)
      (fr' : List BinString) (capTotal : Nat),
      StateInv L ⟨alloc, fr⟩ capTotal → allocStep fr n = some (c, fr') →
      StateInv L ⟨c :: alloc, fr'⟩ capTotal := by
  intro fr
  induction fr with
  | nil =>
      intro alloc c fr' capTotal _ h
      simp [allocStep] at h
  | cons p rest ih =>
      intro alloc c fr' capTotal hstate hstep
      by_cases hp : p.length ≤ n
      · -- split `p` itself
        simp only [allocStep, if_pos hp, Option.some.injEq, Prod.mk.injEq] at hstep
        obtain ⟨hc, hfr'⟩ := hstep
        subst hc; subst hfr'
        have hrest := hstate.of_cons
        have hcd : (p ++ List.replicate (n - p.length) false).length = n := by
          rw [length_zeros]; omega
        have hppc : p <+: p ++ List.replicate (n - p.length) false :=
          ⟨List.replicate (n - p.length) false, rfl⟩
        have hpw : (p :: rest).Pairwise Incomp := hstate.frontier_pf
        rw [List.pairwise_cons] at hpw
        have hsr : FrontierSorted (p :: rest) := hstate.frontier_sorted
        simp only [FrontierSorted] at hsr
        rw [List.pairwise_cons] at hsr
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro a ha
          rcases List.mem_cons.mp ha with rfl | ha
          · rw [hcd]; exact hL
          · exact hstate.allocated_lengths a ha
        · intro q hq
          rcases List.mem_append.mp hq with hq | hq
          · have hle := siblingsOf_length_le hq
            omega
          · exact hrest.frontier_lengths q hq
        · rw [List.pairwise_cons]
          refine ⟨?_, hstate.allocated_pf⟩
          intro a ha
          have hcross : Incomp a p := hstate.cross a ha p List.mem_cons_self
          exact (hcross.of_prefix_right hppc).symm
        · rw [List.pairwise_append]
          refine ⟨siblingsOf_pairwise _ _, hrest.frontier_pf, ?_⟩
          intro s hs q hq
          exact (hpw.1 q hq).of_prefix_left (siblingsOf_extends hs)
        · intro a ha q hq
          rcases List.mem_cons.mp ha with rfl | ha
          · rcases List.mem_append.mp hq with hq | hq
            · rcases siblingsOf_mem.mp hq with ⟨j, hjd, rfl⟩
              exact (incomp_marker_zeros hjd).symm
            · exact (hpw.1 q hq).of_prefix_left hppc
          · rcases List.mem_append.mp hq with hq | hq
            · exact (hstate.cross a ha p List.mem_cons_self).of_prefix_right
                (siblingsOf_extends hq)
            · exact hrest.cross a ha q hq
        · rw [FrontierSorted, List.pairwise_append]
          refine ⟨siblingsOf_sorted _ _, hrest.frontier_sorted, ?_⟩
          intro s hs q hq
          have hps : p.length < s.length := by
            rcases siblingsOf_mem.mp hs with ⟨j, _hjd, rfl⟩
            simp only [length_marker]
            omega
          have hqs := hsr.1 q hq
          omega
        · have hcons' : (((p :: rest).map fun q => 2 ^ (L - q.length)).sum +
              (alloc.map fun a => 2 ^ (L - a.length)).sum) = capTotal :=
            hstate.conservation
          simp only [List.map_cons, List.sum_cons] at hcons'
          show (((siblingsOf p (n - p.length) ++ rest).map fun q =>
                2 ^ (L - q.length)).sum +
              (((p ++ List.replicate (n - p.length) false) :: alloc).map fun a =>
                2 ^ (L - a.length)).sum) = capTotal
          simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons]
          rw [siblingsOf_cap_sum p (n - p.length) L (by omega), hcd]
          have e2 : 2 ^ (L - n) ≤ 2 ^ (L - p.length) :=
            Nat.pow_le_pow_right (by omega) (by omega)
          have e3 : L - p.length - (n - p.length) = L - n := by omega
          rw [e3]
          omega
      · -- recurse past `p`
        simp only [allocStep, if_neg hp] at hstep
        rcases hmap : allocStep rest n with _ | ⟨c₀, fr₀⟩
        · rw [hmap] at hstep; simp at hstep
        · rw [hmap] at hstep
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hstep
          obtain ⟨hc, hfr'⟩ := hstep
          subst c; subst fr'
          have hrest_inv := hstate.of_cons
          have hnew := ih alloc c₀ fr₀ (capTotal - 2 ^ (L - p.length)) hrest_inv hmap
          have hpc : n < p.length := by omega
          have hpw : (p :: rest).Pairwise Incomp := hstate.frontier_pf
          rw [List.pairwise_cons] at hpw
          have hsr : FrontierSorted (p :: rest) := hstate.frontier_sorted
          simp only [FrontierSorted] at hsr
          rw [List.pairwise_cons] at hsr
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · exact hnew.allocated_lengths
          · intro q hq
            rcases List.mem_cons.mp hq with hqp | hq
            · subst q
              exact hstate.frontier_lengths p List.mem_cons_self
            · exact hnew.frontier_lengths q hq
          · exact hnew.allocated_pf
          · rw [List.pairwise_cons]
            refine ⟨?_, hnew.frontier_pf⟩
            intro q hq
            rcases allocStep_mem_extends hmap hq with hqr | ⟨p₀, hp₀, hpre, _hlen⟩
            · exact hpw.1 q hqr
            · exact (hpw.1 p₀ hp₀).of_prefix_right hpre
          · intro a ha q hq
            rcases List.mem_cons.mp ha with hac | ha
            · subst a
              rcases List.mem_cons.mp hq with hqp | hq
              · subst q
                obtain ⟨p₀, hp₀, hpre, _⟩ := allocStep_code_extends hmap
                exact ((hpw.1 p₀ hp₀).of_prefix_right hpre).symm
              · exact hnew.cross c₀ List.mem_cons_self q hq
            · rcases List.mem_cons.mp hq with hqp | hq
              · subst q
                exact hstate.cross a ha p List.mem_cons_self
              · exact hnew.cross a (List.mem_cons_of_mem _ ha) q hq
          · rw [FrontierSorted, List.pairwise_cons]
            refine ⟨?_, hnew.frontier_sorted⟩
            intro q hq
            rcases allocStep_mem_extends hmap hq with hqr | ⟨_p₀, _hp₀, _hpre, hlen⟩
            · have hqs := hsr.1 q hqr
              omega
            · omega
          · have h2 : ((fr₀.map fun q => 2 ^ (L - q.length)).sum +
                ((c₀ :: alloc).map fun a => 2 ^ (L - a.length)).sum) =
                capTotal - 2 ^ (L - p.length) := hnew.conservation
            simp only [List.map_cons, List.sum_cons] at h2
            have hcon0 : (((p :: rest).map fun q => 2 ^ (L - q.length)).sum +
                (alloc.map fun a => 2 ^ (L - a.length)).sum) = capTotal :=
              hstate.conservation
            simp only [List.map_cons, List.sum_cons] at hcon0
            show (((p :: fr₀).map fun q => 2 ^ (L - q.length)).sum +
              ((c₀ :: alloc).map fun a => 2 ^ (L - a.length)).sum) = capTotal
            simp only [List.map_cons, List.sum_cons]
            omega

/-- A frontier encountered in a failed allocation state: all lengths exceed
`n`, and the strict geometric bound keeps the remaining capacity strictly
below `2^(L-n)` even accounting for the maximal element's own weight. -/
theorem sorted_gt_cap_sum_le {L n : Nat} (ls : List BinString)
    (hsorted : FrontierSorted ls)
    (hle : ∀ l ∈ ls, l.length ≤ L) (hgt : ∀ l ∈ ls, n < l.length) (hne : ls ≠ []) :
    (ls.map fun l => 2 ^ (L - l.length)).sum +
      2 ^ (L - (ls.head hne).length) ≤ 2 ^ (L - n) := by
  induction ls with
  | nil => exact absurd rfl hne
  | cons l rest ih =>
      cases rest with
      | nil =>
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
            List.head_cons, Nat.add_zero]
          have hnl : n < l.length := hgt l List.mem_cons_self
          have hlL : l.length ≤ L := hle l List.mem_cons_self
          have mono : 2 ^ (L - l.length + 1) ≤ 2 ^ (L - n) :=
            Nat.pow_le_pow_right (by omega) (by omega)
          rw [two_pow_add_self]
          omega
      | cons h₁ t =>
          have hsorted' : (l :: h₁ :: t).Pairwise fun a b => a.length > b.length := hsorted
          rw [List.pairwise_cons] at hsorted'
          obtain ⟨hsgt, hst⟩ := hsorted'
          have hih := ih hst
            (fun x hx => hle x (List.mem_cons_of_mem _ hx))
            (fun x hx => hgt x (List.mem_cons_of_mem _ hx)) (by simp)
          have hlh : h₁.length < l.length := hsgt h₁ List.mem_cons_self
          have hlL : l.length ≤ L := hle l List.mem_cons_self
          simp only [List.map_cons, List.sum_cons, List.head_cons]
          simp only [List.map_cons, List.sum_cons, List.head_cons] at hih
          have hdd : 2 ^ (L - l.length) + 2 ^ (L - l.length) ≤ 2 ^ (L - h₁.length) := by
            have mono : 2 ^ (L - l.length + 1) ≤ 2 ^ (L - h₁.length) :=
              Nat.pow_le_pow_right (by omega) (by omega)
            rw [two_pow_add_self]
            exact mono
          omega

/-- If the Kraft ledger has room for the next request — allocated mass plus
the request's mass stays within the total capacity — allocation cannot
fail. -/
theorem allocStep_success {L n capTotal : Nat} (_hL : n ≤ L)
    {alloc fr : List BinString}
    (hstate : StateInv L ⟨alloc, fr⟩ capTotal)
    (hbudget : (alloc.map fun a => 2 ^ (L - a.length)).sum +
      2 ^ (L - n) ≤ capTotal) :
    ∃ c fr', allocStep fr n = some (c, fr') := by
  cases hstep : allocStep fr n with
  | some r => exact ⟨r.1, r.2, by rw [Prod.eta r]⟩
  | none =>
      exfalso
      obtain ⟨h₁, h₂, -, -, -, h₆, hcons⟩ := hstate
      have hcons' : ((fr.map fun q => 2 ^ (L - q.length)).sum +
          (alloc.map fun a => 2 ^ (L - a.length)).sum) = capTotal := hcons
      have hgt := allocStep_none_forall hstep
      have hpow : 0 < 2 ^ (L - n) := by positivity
      rcases fr with _ | ⟨hd, tl⟩
      · simp only [List.map_nil, List.sum_nil, Nat.zero_add] at hcons'
        omega
      · have hgt' : ∀ q ∈ hd :: tl, n < q.length := by
          intro q hq
          have hnb := hgt q hq
          omega
        have hgeo := sorted_gt_cap_sum_le (hd :: tl) h₆ h₂ hgt' (by simp)
        simp only [List.head_cons, List.map_cons, List.sum_cons] at hgeo
        simp only [List.map_cons, List.sum_cons] at hcons'
        have hps : 0 < 2 ^ (L - hd.length) := by positivity
        omega

section Examples

/-- Request 3 against the initial frontier: allocate `000`, retain
`001, 01, 1`. -/
example : allocStep [[]] 3 =
    some ([false, false, false],
      [[false, false, true], [false, true], [true]]) := by decide

/-- Second request 3: allocate `001`. -/
example : allocStep [[false, false, true], [false, true], [true]] 3 =
    some ([false, false, true], [[false, true], [true]]) := by decide

/-- Third request 3: allocate `010`, retain `011`. -/
example : allocStep [[false, true], [true]] 3 =
    some ([false, true, false], [[false, true, true], [true]]) := by decide

/-- Fourth request 3: allocate `011`; only `1` remains. -/
example : allocStep [[false, true, true], [true]] 3 =
    some ([false, true, true], [[true]]) := by decide

/-- A later request 1 still succeeds: allocate `1`. -/
example : allocStep [[true]] 1 = some ([true], []) := by decide

/-- Negative example: once the budget is exhausted (frontier empty),
any further request fails. -/
example : allocStep [] 5 = none := rfl

/-- Negative example: a length-`0` request against frontier `[[true]]`
fails; the two requests `0, 0` would exceed the Kraft budget, so the
second one is correctly refused. -/
example : allocStep [[true]] 0 = none := by decide

end Examples

#print axioms siblingsOf_cap_sum
#print axioms allocStep_preserves
#print axioms sorted_gt_cap_sum_le
#print axioms allocStep_success

end KraftChaitin

end KolmogorovComplexity
