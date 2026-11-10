import Mettapedia.Machines.CMemory.Borrowing

/-!
# Parametric footprints

A whole-span permission uses one abstract unit. Substituting the caller's
actual byte extent scales that root, while ordinary object roots use weight
one. Zero-length views are included. This is a geometric interpretation, not
an assertion that a symbolic input contains one byte. Numeric native accesses
must not treat the abstract unit as a concrete C extent.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CMemory.Borrowing

def Region.scale (weight : Nat → Nat) (r : Region) : Region :=
  ⟨r.root, r.first * weight r.root, r.count * weight r.root⟩

theorem Region.scale_contains (weight : Nat → Nat) {a b : Region} (h : a.Contains b) :
    (a.scale weight).Contains (b.scale weight) := by
  obtain ⟨same, first, finish⟩ := h
  refine ⟨same, ?_, ?_⟩
  · simpa [Region.scale, same] using Nat.mul_le_mul_right (weight b.root) first
  · simpa [Region.scale, Region.finish, ← Nat.add_mul, same] using
      Nat.mul_le_mul_right (weight b.root) finish

theorem Region.scale_disjoint (weight : Nat → Nat) {a b : Region} (h : a.Disjoint b) :
    (a.scale weight).Disjoint (b.scale weight) := by
  by_cases different : a.root ≠ b.root
  · exact Or.inl different
  have same : a.root = b.root := Classical.not_not.mp different
  rcases h with different | before | after
  · exact False.elim (different same)
  · right; left
    simpa [Region.scale, Region.finish, ← Nat.add_mul, same] using
      Nat.mul_le_mul_right (weight b.root) before
  · right; right
    simpa [Region.scale, Region.finish, ← Nat.add_mul, same] using
      Nat.mul_le_mul_right (weight b.root) after

def Loan.scale (weight : Nat → Nat) (l : Loan) : Loan :=
  { l with region := l.region.scale weight }

theorem ordered_scale (weight : Nat → Nat) {loans : List Loan} (ordered : Ordered loans) :
    Ordered (loans.map (Loan.scale weight)) := by
  intro l present parent ancestor
  obtain ⟨before, member, rfl⟩ := List.mem_map.mp present
  exact ordered before member parent ancestor

theorem access_scale (weight : Nat → Nat) {loans : List Loan} {id : Nat} {r : Region}
    {writing : Bool} (access : Access loans id r writing) :
    Access (loans.map (Loan.scale weight)) id (r.scale weight) writing := by
  obtain ⟨l, member, identity, inside, mode, others⟩ := access
  refine ⟨Loan.scale weight l, List.mem_map.mpr ⟨l, member, rfl⟩, identity,
    Region.scale_contains weight inside, mode, ?_⟩
  intro other present different overlap
  obtain ⟨before, memberBefore, rfl⟩ := List.mem_map.mp present
  apply others before memberBefore different
  intro apart
  exact overlap (Region.scale_disjoint weight apart)

theorem whole_extent (weight : Nat → Nat) (root : Nat) :
    (Region.mk root 0 1).scale weight = ⟨root, 0, weight root⟩ := by
  simp [Region.scale]

theorem preserve_concrete {weight : Nat → Nat} {r : Region} (concrete : weight r.root = 1) :
    r.scale weight = r := by cases r; simp_all [Region.scale]

namespace ScalingControls

def writer : Loan := ⟨0, ⟨7, 0, 1⟩, .exclusive, []⟩
def child : Loan := ⟨1, ⟨7, 0, 1⟩, .shared, [0]⟩

theorem whole_is_not_one_byte : (Loan.scale (fun _ => 4096) writer).region.count = 4096 := by decide
theorem empty_view_retains_identity : (Loan.scale (fun _ => 0) writer).region = ⟨7, 0, 0⟩ := by decide
theorem child_access : Access [writer, child] 1 ⟨7, 0, 1⟩ false := by decide
theorem parent_suspended : ¬ Access [writer, child] 0 ⟨7, 0, 1⟩ true := by decide
theorem arbitrary_child_extent (n : Nat) :
    Access ([writer, child].map (Loan.scale (fun _ => n))) 1 ⟨7, 0, n⟩ false := by
  simpa [Region.scale] using access_scale (fun _ => n) child_access

end ScalingControls
end Mettapedia.Machines.CMemory.Borrowing
