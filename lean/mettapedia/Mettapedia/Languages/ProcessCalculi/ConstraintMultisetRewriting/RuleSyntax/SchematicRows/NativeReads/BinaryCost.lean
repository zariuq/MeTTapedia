import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.BinaryCut

/-!
# Logarithmic descriptor probes for the actual binary recurrence

These receipts count calls to the descriptor predicate, not machine
instructions, allocation or source-language fuel. The recurrence follows
the same branches and midpoint as `BinaryCut.search`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.BinaryCost

def probes (before : Nat → Bool) : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | fuel + 1, low, high =>
      if low < high then
        let middle := low + (high - low) / 2
        if before middle then 1 + probes before fuel (middle + 1) high
        else 1 + probes before fuel low middle
      else 0

theorem empty_interval (before : Nat → Bool) (fuel low high : Nat) (empty : high ≤ low) :
    probes before fuel low high = 0 := by
  cases fuel <;> simp [probes, Nat.not_lt_of_ge empty]

theorem power_bound (before : Nat → Bool) (depth : Nat) (fuel low high : Nat)
    (small : high - low < 2 ^ depth) : probes before fuel low high ≤ depth := by
  induction depth generalizing fuel low high with
  | zero =>
      simp only [pow_zero] at small
      exact le_of_eq (empty_interval before fuel low high (by omega))
  | succ depth ih =>
      cases fuel with
      | zero => simp [probes]
      | succ fuel =>
          by_cases active : low < high
          · let middle := low + (high - low) / 2
            have lower : middle - low < 2 ^ depth := by
              simp only [pow_succ] at small
              dsimp [middle]
              omega
            have upper : high - (middle + 1) < 2 ^ depth := by
              simp only [pow_succ] at small
              dsimp [middle]
              omega
            have left := ih fuel low middle lower
            have right := ih fuel (middle + 1) high upper
            simp only [probes, if_pos active]
            change (if before middle = true then 1 + probes before fuel (middle + 1) high
              else 1 + probes before fuel low middle) ≤ depth + 1
            split <;> omega
          · rw [empty_interval before (fuel + 1) low high (by omega)]
            omega

#print axioms power_bound

theorem logarithmic_bound (before : Nat → Bool) (fuel low high : Nat) :
    probes before fuel low high ≤ Nat.log2 (high - low) + 1 :=
  power_bound before (Nat.log2 (high - low) + 1) fuel low high Nat.lt_log2_self

#print axioms logarithmic_bound

section Keys

/-- Seek the first key at least as large as the query and certify equality.
The slot is an occurrence index, so successful lookups identify equations
even when several equations have equal output values. -/
def lookup (key : Nat → Nat) (size needle : Nat) : Option Nat :=
  let slot := BinaryCut.cut (fun i => decide (key i < needle)) size
  if slot < size ∧ key slot = needle then some slot else none

theorem lookup_some_iff (key : Nat → Nat) (size needle slot : Nat)
    (sorted : StrictMonoOn key (Set.Iio size)) :
    lookup key size needle = some slot ↔ slot < size ∧ key slot = needle := by
  let before : Nat → Bool := fun i => decide (key i < needle)
  let cut := BinaryCut.cut before size
  have closed : BinaryCut.Prefix before size := by
    intro i j order bound yes
    exact decide_eq_true ((sorted.monotoneOn (lt_of_le_of_lt order bound) bound order).trans_lt
      (of_decide_eq_true yes))
  change (if cut < size ∧ key cut = needle then some cut else none) = some slot ↔ _
  constructor
  · by_cases ok : cut < size ∧ key cut = needle
    · rw [if_pos ok]
      intro found
      have same := Option.some.inj found
      rw [← same]
      exact ok
    · rw [if_neg ok]
      intro impossible
      cases impossible
  · rintro ⟨inside, hit⟩
    have result : cut = slot := by
      rcases lt_trichotomy cut slot with earlier | same | later
      · have inCut := lt_trans earlier inside
        have smaller := sorted inCut inside earlier
        rw [hit] at smaller
        have impossible := (BinaryCut.before_iff before size closed cut inCut).mp (decide_eq_true smaller)
        exact (lt_irrefl _ impossible).elim
      · exact same
      · have smaller := (BinaryCut.before_iff before size closed slot inside).mpr later
        exact (Nat.ne_of_lt (of_decide_eq_true smaller) hit).elim
    rw [result, if_pos ⟨inside, hit⟩]

theorem lookup_none_iff (key : Nat → Nat) (size needle : Nat)
    (sorted : StrictMonoOn key (Set.Iio size)) :
    lookup key size needle = none ↔ ∀ slot < size, key slot ≠ needle := by
  constructor
  · intro miss slot inside hit
    rw [(lookup_some_iff key size needle slot sorted).mpr ⟨inside, hit⟩] at miss
    cases miss
  · intro notMem
    cases result : lookup key size needle with
    | none => rfl
    | some slot =>
      obtain ⟨inside, hit⟩ := (lookup_some_iff key size needle slot sorted).mp result
      exact (notMem slot inside hit).elim

/-- A decoder of Boolean comparison transcripts must distinguish every stored
occurrence plus none queries. Keeping the original payload at a leaf cannot merge
two different requested occurrence identities. -/
theorem lookup_transcript_bound (key : Nat → Nat) (size cap missing : Nat)
    (sorted : StrictMonoOn key (Set.Iio size))
    (notMem : ∀ i < size, key i ≠ missing)
    (transcript : Nat → Fin cap → Bool) (decode : (Fin cap → Bool) → Option Nat)
    (correct : ∀ k, decode (transcript k) = lookup key size k) :
    size + 1 ≤ 2 ^ cap := by
  classical
  let encode : Option (Fin size) → (Fin cap → Bool) :=
    fun choice => transcript (choice.elim missing (fun i => key i))
  have read : ∀ choice, decode (encode choice) = (choice : Option (Fin size)).map Fin.val := by
    intro choice
    cases choice with
    | none => exact (correct missing).trans ((lookup_none_iff key size missing sorted).mpr notMem)
    | some slot =>
      exact (correct (key slot)).trans ((lookup_some_iff key size (key slot) slot sorted).mpr ⟨slot.isLt, rfl⟩)
  have injective : Function.Injective encode := by
    intro a b same
    have observed := (read a).symm.trans ((congrArg decode same).trans (read b))
    cases a <;> cases b <;> simp_all [Fin.val_inj]
  simpa using Fintype.card_le_of_injective encode injective

/-- One final equality check certifies the slot obtained by the binary loop. -/
theorem lookup_comparison_upper (key : Nat → Nat) (size needle : Nat) :
    probes (fun i => decide (key i < needle)) size 0 size + 1 ≤ Nat.log2 size + 2 := by
  have bound := logarithmic_bound (fun i => decide (key i < needle)) size 0 size
  simp only [Nat.sub_zero] at bound
  omega

/-- The installed lookup is within one Boolean key comparison of the
best possible worst-case transcript length. -/
theorem lookup_within_one (key : Nat → Nat) (size cap missing needle : Nat)
    (nonempty : size ≠ 0) (sorted : StrictMonoOn key (Set.Iio size))
    (notMem : ∀ i < size, key i ≠ missing)
    (transcript : Nat → Fin cap → Bool) (decode : (Fin cap → Bool) → Option Nat)
    (correct : ∀ k, decode (transcript k) = lookup key size k) :
    probes (fun i => decide (key i < needle)) size 0 size + 1 ≤ cap + 1 := by
  have lower := lookup_transcript_bound key size cap missing sorted notMem transcript decode correct
  have depth := (Nat.log2_lt nonempty).mpr (by omega : size < 2 ^ cap)
  have upper := lookup_comparison_upper key size needle
  omega

#print axioms lookup_some_iff
#print axioms lookup_transcript_bound
#print axioms lookup_comparison_upper
#print axioms lookup_within_one

end Keys

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.BinaryCost
