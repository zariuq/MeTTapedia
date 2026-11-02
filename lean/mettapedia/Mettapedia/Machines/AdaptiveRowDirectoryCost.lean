import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-!
Cost of a dense prefix with an ordered sparse overflow directory. Rows use
the relation's shared numbering. The requested descriptor bytes are twelve
per direct slot and forty per sparse row; payload and allocator metadata are
separate. A fixed cut changes cost by at most forty on one row birth/death.

The maintenance algorithm switches to an optimal allowed cut only when its
current cost exceeds twice the optimum. Checking again within B/160 row
events gives a factor-three bound against every allowed cut. Allocation
failure does not establish that maintenance invariant: the retained prefix
must remain charged. This is a model for the proposed directory, not native
implementation correspondence or a bound on whole-runtime RSS.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.AdaptiveRowDirectoryCost

abbrev Rows := Finset Nat

def outside (rows : Rows) (cut : Nat) : Rows := rows.filter (cut ≤ ·)

def bytes (rows : Rows) (cut : Nat) : Nat :=
  12 * cut + 40 * (outside rows cut).card

inductive Event where
  | insert (key : Nat)
  | erase (key : Nat)

def Event.apply (event : Event) (rows : Rows) : Rows :=
  match event with
  | .insert key => Insert.insert key rows
  | .erase key => rows.erase key

theorem event_cost (event : Event) (rows : Rows) (cut : Nat) :
    bytes (event.apply rows) cut ≤ bytes rows cut + 40 ∧
    bytes rows cut ≤ bytes (event.apply rows) cut + 40 := by
  cases event with
  | insert key =>
      have hsub : outside (insert key rows) cut ⊆ insert key (outside rows cut) := by
        intro n hn
        simp only [outside, Finset.mem_filter, Finset.mem_insert] at hn ⊢
        rcases hn with ⟨h | h, hc⟩
        · exact Or.inl h
        · exact Or.inr ⟨h, hc⟩
      have hback : outside rows cut ⊆ outside (insert key rows) cut := by
        intro n hn
        simp only [outside, Finset.mem_filter, Finset.mem_insert] at hn ⊢
        exact ⟨Or.inr hn.1, hn.2⟩
      have hle := (Finset.card_le_card hsub).trans
        (Finset.card_insert_le key (outside rows cut))
      have hge := Finset.card_le_card hback
      simp only [Event.apply, bytes]
      omega
  | erase key =>
      have hsub : outside (rows.erase key) cut ⊆ outside rows cut := by
        intro n hn
        simp only [outside, Finset.mem_filter, Finset.mem_erase] at hn ⊢
        exact ⟨hn.1.2, hn.2⟩
      have hback : outside rows cut ⊆ insert key (outside (rows.erase key) cut) := by
        intro n hn
        simp only [outside, Finset.mem_filter, Finset.mem_insert, Finset.mem_erase] at hn ⊢
        by_cases h : n = key
        · exact Or.inl h
        · exact Or.inr ⟨⟨h, hn.1⟩, hn.2⟩
      have hle := Finset.card_le_card hsub
      have hge := (Finset.card_le_card hback).trans
        (Finset.card_insert_le key (outside (rows.erase key) cut))
      simp only [Event.apply, bytes]
      omega

def run : List Event → Rows → Rows
  | [], rows => rows
  | event :: rest, rows => run rest (event.apply rows)

theorem trace_cost (events : List Event) (rows : Rows) (cut : Nat) :
    bytes (run events rows) cut ≤ bytes rows cut + 40 * events.length ∧
    bytes rows cut ≤ bytes (run events rows) cut + 40 * events.length := by
  induction events generalizing rows with
  | nil => simp [run]
  | cons event rest ih =>
      have step := event_cost event rows cut
      have tail := ih (event.apply rows)
      simp only [run, List.length_cons]
      omega

def Optimal (rows : Rows) (cuts : Finset Nat) (best : Nat) : Prop :=
  best ∈ cuts ∧ ∀ cut ∈ cuts, bytes rows best ≤ bytes rows cut

theorem optimal_exists (rows : Rows) (cuts : Finset Nat) (nonempty : cuts.Nonempty) :
    ∃ best, Optimal rows cuts best := by
  obtain ⟨best, member, minimum⟩ := Finset.exists_min_image cuts (bytes rows) nonempty
  exact ⟨best, member, minimum⟩

def maintain (rows : Rows) (current best : Nat) : Nat :=
  if 2 * bytes rows best < bytes rows current then best else current

theorem maintenance_bound (rows : Rows) (current best : Nat) :
    bytes rows (maintain rows current best) ≤ 2 * bytes rows best := by
  unfold maintain
  split_ifs <;> omega

theorem scheduled_bound (rows : Rows) (cuts : Finset Nat) (current best : Nat)
    (events : List Event) (optimal : Optimal rows cuts best)
    (interval : 160 * events.length ≤ bytes rows best) :
    ∀ cut ∈ cuts,
      bytes (run events rows) (maintain rows current best) ≤
        3 * bytes (run events rows) cut := by
  intro cut member
  have maintained := maintenance_bound rows current best
  have current_change := (trace_cost events rows (maintain rows current best)).1
  have competitor_change := (trace_cost events rows cut).2
  have before := optimal.2 cut member
  omega

theorem sparse_cost (rows : Rows) : bytes rows 0 = 40 * rows.card := by
  simp [bytes, outside]

theorem dense_cost (rows : Rows) (cut : Nat) (inside : ∀ n ∈ rows, n < cut) :
    bytes rows cut = 12 * cut := by
  have empty : outside rows cut = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro n hn
    simp only [outside, Finset.mem_filter] at hn
    exact (Nat.not_lt_of_ge hn.2) (inside n hn.1)
  simp [bytes, empty]

theorem dense_span_negative :
    bytes {0, 1000000} 1048576 > 100000 * bytes {0, 1000000} 0 := by
  norm_num [bytes, outside]
  omega

#print axioms event_cost
#print axioms trace_cost
#print axioms scheduled_bound
#print axioms dense_span_negative

end Mettapedia.Machines.AdaptiveRowDirectoryCost
