/-!
# When does a promotion gate mean something? Independent evidence and its count

A memory that promotes a note into a trusted tier once "enough sources"
support it is only as sound as its notion of source. Two classical results
fix the semantics.

* **Sybil identities (Douceur 2002).** If one principal can mint identities,
  any gate that counts identities can be passed by that principal alone.
  Counting distinct *principals*, whose identities cannot be minted, is what
  makes a quorum mean independent support.
* **Evidence-based confidence (NARS; PLN, Goertzel et al. 2008).** Confidence
  in a judgement from `n` independent pieces of evidence is `c(n) = n/(n+K)`,
  where `K` is the evidential horizon. A target confidence `p/q` then
  *derives* the quorum, `n ≥ pK/(q−p)`, instead of fixing it by hand.

Recent agent-memory work reports that trust filters which score the content
let confidently worded poisoned entries through. A gate that reads a
confidence the writer supplies is no boundary at all.

Results:
* One principal with `k` sessions passes a session-counting gate of `k`
  (`sybil_passes_session_gate`). Against a principal-counting gate of at
  least 2 it never passes, however many sessions it has
  (`one_principal_never_passes`).
* Further reports from a principal already counted do not raise the count
  (`repeat_principal_does_not_count`).
* Confidence grows with independent evidence (`confidence_monotone`), and
  reaching `p/q` is exactly `pK ≤ (q−p)·n` (`reaches_iff`). With `K = 2`, a
  target of 1/2 needs two principals and 2/3 needs four (`worked_quorums`).
* A gate on writer-supplied confidence passes a single principal's entry
  (`self_reported_confidence_is_no_boundary`).

Outside the model: authenticating principals, which is the real work, and
the reliability of each principal, where weighted evidence would replace
counts.
-/

namespace Mettapedia.CognitiveArchitecture.Memory.GateEvidence

/-- The distinct elements of a list. -/
def distinct : List Nat → List Nat
  | [] => []
  | x :: xs => if x ∈ distinct xs then distinct xs else x :: distinct xs

theorem mem_distinct {l : List Nat} {y : Nat} : y ∈ distinct l ↔ y ∈ l := by
  induction l with
  | nil => simp [distinct]
  | cons x xs ih =>
    by_cases hx : x ∈ distinct xs
    · simp only [distinct, hx, if_true, ih, List.mem_cons]
      constructor
      · exact Or.inr
      · rintro (rfl | h)
        · exact ih.mp hx
        · exact h
    · simp [distinct, hx, ih]

theorem distinct_length_le_one {l : List Nat} {a : Nat} (h : ∀ x ∈ l, x = a) :
    (distinct l).length ≤ 1 := by
  induction l with
  | nil => simp [distinct]
  | cons x xs ih =>
    have hxs : ∀ y ∈ xs, y = a := fun y hy => h y (by simp [hy])
    have hx : x = a := h x (by simp)
    by_cases hmem : x ∈ distinct xs
    · simp only [distinct, hmem, if_true]
      exact ih hxs
    · simp only [distinct, hmem, if_false, List.length_cons]
      have empty : distinct xs = [] := by
        cases hd : distinct xs with
        | nil => rfl
        | cons y ys =>
          have hy : y ∈ xs := mem_distinct.mp (by simp [hd])
          have : y = x := (hxs y hy).trans hx.symm
          exact absurd (by simp [hd, this]) hmem
      simp [empty]

theorem distinct_of_nodup {l : List Nat} (h : l.Nodup) : distinct l = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.nodup_cons] at h
    simp [distinct, ih h.2, h.1]

/-- A gate that counts distinct sessions. -/
def sessionGate (k : Nat) (sessions : List Nat) : Bool :=
  decide (k ≤ (distinct sessions).length)

/-- A gate that counts distinct principals, through each session's owner. -/
def principalGate (owner : Nat → Nat) (k : Nat) (sessions : List Nat) : Bool :=
  decide (k ≤ (distinct (sessions.map owner)).length)

/-- One principal minting `k` sessions passes a session-counting gate of `k`. -/
theorem sybil_passes_session_gate (k : Nat) :
    sessionGate k (List.range k) = true := by
  simp [sessionGate, distinct_of_nodup List.nodup_range, List.length_range]

/-- Against a principal-counting gate of at least two, one principal never
passes, however many sessions it has. -/
theorem one_principal_never_passes (owner : Nat → Nat) (k a : Nat) (hk : 2 ≤ k)
    (sessions : List Nat) (mine : ∀ s ∈ sessions, owner s = a) :
    principalGate owner k sessions = false := by
  have all : ∀ x ∈ sessions.map owner, x = a := by
    intro x hx
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
    exact mine s hs
  have := distinct_length_le_one all
  simp [principalGate]
  omega

/-- A further report from a principal already counted does not raise the
count. -/
theorem repeat_principal_does_not_count (owner : Nat → Nat) (sessions : List Nat)
    (s : Nat) (counted : owner s ∈ sessions.map owner) :
    distinct ((s :: sessions).map owner) = distinct (sessions.map owner) := by
  have : owner s ∈ distinct (sessions.map owner) := mem_distinct.mpr counted
  simp [distinct, this]

/-! ## Confidence from independent evidence

`c(n) = n/(n+K)` is compared by cross-multiplication, so `c(n) ≥ p/q` is
`p·(n+K) ≤ q·n`. -/

def reaches (K p q n : Nat) : Prop := p * (n + K) ≤ q * n

/-- More independent evidence never lowers confidence:
`n/(n+K) ≤ n'/(n'+K)` whenever `n ≤ n'`. -/
theorem confidence_monotone (K n n' : Nat) (h : n ≤ n') :
    n * (n' + K) ≤ n' * (n + K) := by
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_comm n n']
  exact Nat.add_le_add_left (Nat.mul_le_mul_right K h) _

/-- The quorum a target confidence derives: `c(n) ≥ p/q` iff `pK ≤ (q−p)·n`. -/
theorem reaches_iff (K p q n : Nat) (hpq : p ≤ q) :
    reaches K p q n ↔ p * K ≤ (q - p) * n := by
  have hle : p * n ≤ q * n := Nat.mul_le_mul_right n hpq
  rw [reaches, Nat.mul_add, Nat.sub_mul]
  generalize p * n = a at hle ⊢
  generalize q * n = b at hle ⊢
  generalize p * K = c
  omega

/-- With horizon `K = 2`: confidence 1/2 needs two principals (one is not
enough), and 2/3 needs four (three are not enough). -/
theorem worked_quorums :
    reaches 2 1 2 2 ∧ ¬ reaches 2 1 2 1 ∧ reaches 2 2 3 4 ∧ ¬ reaches 2 2 3 3 := by
  simp [reaches]

/-! ## Self-reported confidence -/

structure Entry where
  principal : Nat
  confidence : Nat
  deriving DecidableEq, Repr

/-- A gate on the confidence the writer itself supplies. -/
def confidenceGate (threshold : Nat) (e : Entry) : Bool := decide (threshold ≤ e.confidence)

/-- Any single principal passes it by writing a high enough confidence. -/
theorem self_reported_confidence_is_no_boundary (threshold principal : Nat) :
    confidenceGate threshold ⟨principal, threshold⟩ = true := by
  simp [confidenceGate]

#print axioms mem_distinct
#print axioms distinct_length_le_one
#print axioms sybil_passes_session_gate
#print axioms one_principal_never_passes
#print axioms repeat_principal_does_not_count
#print axioms confidence_monotone
#print axioms reaches_iff
#print axioms worked_quorums
#print axioms self_reported_confidence_is_no_boundary

end Mettapedia.CognitiveArchitecture.Memory.GateEvidence
