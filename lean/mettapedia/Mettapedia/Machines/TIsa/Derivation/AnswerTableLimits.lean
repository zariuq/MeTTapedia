import Mettapedia.Machines.TIsa.Derivation.AnswerTable
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Set.Card

/-!
# Finite completion and infinite derivations

Finite derivation families have an exact eventual multiplicity.
An infinite derivation family has no finite final count. This does
not obstruct a set table: on finitely many keys, presence stabilizes
after at most one productive round per key. A cycle without a base
answer contributes no finite proof.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.Derivation.AnswerTable

variable {n : ℕ}

theorem derivesAt_succ (program : List (Clause n)) (depth : ℕ)
    {key : Fin n} {proof : Proof} (has : DerivesAt program depth key proof) :
    DerivesAt program (depth + 1) key proof := by
  induction depth generalizing key proof with
  | zero => cases has
  | succ depth ih =>
    cases proof with
    | node tag children =>
      obtain ⟨i, position, head, derivations⟩ := has
      exact ⟨i, position, head, derivations.imp (fun _ _ witness => ih witness)⟩

theorem derivesAt_mono (program : List (Clause n)) {less more : ℕ} (grows : less ≤ more)
    {key : Fin n} {proof : Proof} (has : DerivesAt program less key proof) :
    DerivesAt program more key proof := by
  induction grows with
  | refl => exact has
  | step _ ih => exact derivesAt_succ program _ ih

theorem enumerate_mono (program : List (Clause n)) {less more : ℕ} (grows : less ≤ more)
    (key : Fin n) : enumerate program less key ⊆ enumerate program more key :=
  fun {_} prior => (mem_enumerate_iff _ _ _ _).mpr
    (derivesAt_mono program grows ((mem_enumerate_iff _ _ _ _).mp prior))

theorem counts_mono (program : List (Clause n)) {less more : ℕ} (grows : less ≤ more)
    (key : Fin n) : (counts program less)[key.val]'key.isLt ≤ (counts program more)[key.val]'key.isLt := by
  classical
  have subset : (enumerate program less key).toFinset ⊆ (enumerate program more key).toFinset := by
    intro proof member
    exact List.mem_toFinset.mpr (enumerate_mono program grows key (List.mem_toFinset.mp member))
  simpa only [counts_exact, List.toFinset_card_of_nodup (enumerate_distinct program less key),
    List.toFinset_card_of_nodup (enumerate_distinct program more key)] using Finset.card_le_card subset

abbrev AnswerWitness (program : List (Clause n)) (key : Fin n) := { proof : Proof // Derives program key proof }

private theorem common_depth {I : Type*} [Fintype I] {program : List (Clause n)} {key : Fin n}
    (sample : I → AnswerWitness program key) :
    ∃ depth, ∀ i, DerivesAt program depth key (sample i).val := by
  classical
  choose limit justified using fun i => (sample i).property
  refine ⟨Finset.univ.sup limit, fun i => ?_⟩
  exact derivesAt_mono program (Finset.le_sup (f := limit) (Finset.mem_univ i)) (justified i)

theorem finite_derivations_eventual_count (program : List (Clause n)) (key : Fin n)
    [Finite (AnswerWitness program key)] :
    ∃ cutoff, ∀ depth ≥ cutoff, (counts program depth)[key.val]'key.isLt = Nat.card (AnswerWitness program key) := by
  classical
  let _ := Fintype.ofFinite (AnswerWitness program key)
  obtain ⟨cutoff, covers⟩ := common_depth (id : AnswerWitness program key → AnswerWitness program key)
  refine ⟨cutoff, fun depth later => ?_⟩
  let storage := (enumerate program depth key).toFinset
  have all : (storage : Set Proof) = {p | Derives program key p} := by
    ext p
    change p ∈ storage ↔ Derives program key p
    constructor
    · intro member
      exact ⟨depth, (mem_enumerate_iff _ _ _ _).mp (List.mem_toFinset.mp member)⟩
    · intro derivation
      exact List.mem_toFinset.mpr ((mem_enumerate_iff _ _ _ _).mpr
        (derivesAt_mono program later (covers ⟨p, derivation⟩)))
  calc
    (counts program depth)[key.val]'key.isLt = storage.card := by
      rw [counts_exact, List.toFinset_card_of_nodup (enumerate_distinct program depth key)]
    _ = Nat.card (↥(storage : Set Proof)) := by
      rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
    _ = Nat.card (AnswerWitness program key) := by rw [all]; rfl

theorem infinite_derivations_unbounded (program : List (Clause n)) (key : Fin n)
    [Infinite (AnswerWitness program key)] (bound : ℕ) :
    ∃ depth, bound < (counts program depth)[key.val]'key.isLt := by
  classical
  let sample (i : Fin (bound + 1)) : AnswerWitness program key :=
    Infinite.natEmbedding (AnswerWitness program key) i.val
  obtain ⟨depth, covers⟩ := common_depth sample
  let f (i : Fin (bound + 1)) : Proof := (sample i).val
  have faithful : Function.Injective f := fun _ _ same =>
    Fin.ext ((Infinite.natEmbedding (AnswerWitness program key)).injective (Subtype.ext same))
  have below : Finset.univ.image f ⊆ (enumerate program depth key).toFinset := by
    intro p listed
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp listed
    exact List.mem_toFinset.mpr ((mem_enumerate_iff _ _ _ _).mpr (covers i))
  have size := Finset.card_le_card below
  rw [Finset.card_image_of_injective _ faithful, Finset.card_univ, Fintype.card_fin,
    List.toFinset_card_of_nodup (enumerate_distinct program depth key)] at size
  exact ⟨depth, by rw [counts_exact]; omega⟩

theorem infinite_iff_unbounded (program : List (Clause n)) (key : Fin n) :
    Infinite (AnswerWitness program key) ↔
      ∀ bound, ∃ depth, bound < (counts program depth)[key.val]'key.isLt := by
  constructor
  · intro infinite
    let _ := infinite
    exact infinite_derivations_unbounded program key
  · intro unbounded
    apply not_finite_iff_infinite.mp
    intro finite
    let _ := finite
    obtain ⟨cutoff, same⟩ := finite_derivations_eventual_count program key
    obtain ⟨depth, large⟩ := unbounded (Nat.card (AnswerWitness program key))
    have grows := counts_mono program (Nat.le_max_left depth cutoff) key
    rw [same _ (Nat.le_max_right depth cutoff)] at grows
    omega

theorem presence_mono (program : List (Clause n)) {low high : ℕ} (grows : low ≤ high) :
    presence program low ⊆ presence program high := by
  intro key found
  obtain ⟨proof, derives⟩ := (presence_exact _ _ _).mp found
  exact (presence_exact _ _ _).mpr ⟨proof, derivesAt_mono program grows derives⟩

private theorem presence_succ_congr (program : List (Clause n)) {a b : ℕ}
    (same : presence program a = presence program b) :
    presence program (a + 1) = presence program (b + 1) := by
  simp only [presence, same]

theorem presence_stays (program : List (Clause n)) {cutoff : ℕ}
    (stationary : presence program cutoff = presence program (cutoff + 1))
    (depth : ℕ) (later : cutoff ≤ depth) : presence program depth = presence program cutoff := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le later
  clear later
  induction extra with
  | zero => rfl
  | succ extra ih =>
    rw [Nat.add_succ]
    exact (presence_succ_congr program ih).trans stationary.symm

theorem presence_saturates (program : List (Clause n)) :
    presence program n = presence program (n + 1) := by
  by_contra notYet
  have grows (depth : ℕ) (within : depth ≤ n) : presence program depth ≠ presence program (depth + 1) := by
    intro same
    exact notYet ((presence_stays program same n within).trans
      (presence_stays program same (n + 1) (within.trans (Nat.le_succ _))).symm)
  have size : ∀ depth ≤ n + 1, depth ≤ (presence program depth).card := by
    intro depth
    induction depth with
    | zero => intro _; exact Nat.zero_le _
    | succ depth ih =>
      intro within
      have enough := ih (by omega)
      have more := Finset.card_lt_card (lt_of_le_of_ne
        (presence_mono program (Nat.le_succ depth)) (grows depth (by omega)))
      change (presence program depth).card < (presence program (depth + 1)).card at more
      change depth + 1 ≤ (presence program (depth + 1)).card
      omega
  have atLimit := size (n + 1) (Nat.le_refl _)
  have cap : (presence program (n + 1)).card ≤ n := by
    simpa using (presence program (n + 1)).card_le_univ
  omega

/-- The set table gives a completed presence answer, even when the
underlying proof multiplicity is infinite. -/
theorem presence_complete (program : List (Clause n)) (key : Fin n) :
    key ∈ presence program n ↔ ∃ proof, Derives program key proof := by
  constructor
  · intro present
    obtain ⟨proof, derives⟩ := (presence_exact _ _ _).mp present
    exact ⟨proof, n, derives⟩
  · rintro ⟨proof, depth, derives⟩
    have found := (presence_exact _ _ _).mpr ⟨proof, derives⟩
    rcases Nat.le_total depth n with sooner | later
    · exact presence_mono program sooner found
    · exact presence_stays program (presence_saturates program) depth later ▸ found

/-! ## Examples -/

private def seeded : List (Clause 1) := [⟨0, []⟩, ⟨0, [0]⟩]
private def unseeded : List (Clause 1) := [⟨0, [0]⟩]

theorem productive_cycle_counts (depth : ℕ) : (counts seeded depth)[0] = depth := by
  have once (prev : Fin 1 → ℕ) : countRound seeded prev 0 = 1 + prev 0 := by
    simp [countRound, eligible, seeded, List.finRange_succ]
  induction depth with
  | zero => rfl
  | succ depth ih =>
    change countRound seeded (fun q => (counts seeded depth)[q.val]'q.isLt) (0 : Fin 1) = depth + 1
    rw [once]
    change 1 + (counts seeded depth)[0] = depth + 1
    rw [ih]
    omega

theorem productive_cycle_has_infinite_derivations : Infinite (AnswerWitness seeded 0) :=
  (infinite_iff_unbounded seeded 0).mpr
    (fun bound => ⟨bound + 1, (productive_cycle_counts (bound + 1)).symm ▸ Nat.lt_succ_self bound⟩)

theorem productive_cycle_has_presence : 0 ∈ presence seeded 1 := by decide +kernel

theorem bare_cycle_has_no_derivation : ¬ ∃ proof, Derives unseeded 0 proof := by
  rw [← presence_complete]
  decide +kernel

private def doubled : List (Clause 2) := [⟨0, []⟩, ⟨0, []⟩, ⟨1, [0, 0]⟩]

theorem two_equal_clauses_used_twice_give_four_proofs :
    (counts doubled 2)[1] = 4 ∧ 1 ∈ presence doubled 2 := by decide +kernel

end Mettapedia.Machines.TIsa.Derivation.AnswerTable
