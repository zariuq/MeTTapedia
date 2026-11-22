import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RegionObservations

/-!
# Taking a region's whole fiber: one rule for "replace it if there is one, insert it otherwise"

An **upsert** into a region takes every occurrence that the region's fiber holds in the world it fires in, keeps
nothing, and makes one occurrence inside the region (`upsert`). Whatever the fiber held (nothing, one occurrence or
several), afterwards it holds exactly the made occurrence (`upsert_fiber`), and nothing outside the region changes
(`upsert_outside`). On an empty fiber the upsert is an insertion that takes nothing (`upsert_eq_insert`); on a fiber of
one occurrence it replaces that occurrence (`upsert_eq_replace`). So one rule covers the two cases that a fixed number of
takes splits into a rule that takes and a rule that asks for absence.

The fiber is read in the world the commit fires in. Two upserts into one region whose fibers were both read before
either fired, applied one after the other, leave both made occurrences in the fiber (`stale_upserts_double`). The
second read after the first fired leaves one (`sequential_upserts_single`). Reading the fiber exactly is what orders
two upserts into one region. An upsert into a region leaves the fiber of a disjoint region as it was
(`upsert_keeps_disjoint_fiber`), so upserts into disjoint regions commute (`upserts_commute_of_disjoint`).

An add that replaced what its region held would not be a make: two such adds into one region, applied in the two
orders, end with different occurrences (`Controls.overwriting_adds_depend_on_order`), while makes of fresh
occurrences commute (`makes_commute`). Replacing is a take and a make.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RegionUpserts

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe uO uT

variable {O : Type uO} {T : Type uT} [DecidableEq O]

/-- **An upsert into a region**: take every occurrence the region's fiber holds in `world`, keep nothing, and make
the occurrence `made`. -/
def upsert (label : O → T) (world : Finset O) (region : T → Bool) (made : O) : Commit O T :=
  ⟨regionOf label world region, ∅, {made}, []⟩

/-- **After an upsert the fiber holds exactly the made occurrence**, whatever it held before. -/
theorem upsert_fiber {label : O → T} {world : Finset O} {region : T → Bool} {made : O}
    (inside : region (label made) = true) :
    regionOf label (fire world (upsert label world region made)) region = {made} := by
  ext o
  simp only [regionOf, fire, upsert, Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff,
    Finset.mem_singleton]
  constructor
  · rintro ⟨(⟨inWorld, notTaken⟩ | rfl), inRegion⟩
    · exact absurd ⟨inWorld, inRegion⟩ notTaken
    · rfl
  · rintro rfl
    exact ⟨Or.inr rfl, inside⟩

/-- **Nothing outside the region changes.** -/
theorem upsert_outside {label : O → T} {world : Finset O} {region : T → Bool} {made : O}
    (inside : region (label made) = true) {o : O} (outside : region (label o) = false) :
    o ∈ fire world (upsert label world region made) ↔ o ∈ world := by
  simp only [fire, upsert, regionOf, Finset.mem_union, Finset.mem_sdiff, Finset.mem_filter,
    Finset.mem_singleton]
  constructor
  · rintro (⟨inWorld, _⟩ | rfl)
    · exact inWorld
    · simp [inside] at outside
  · intro inWorld
    exact Or.inl ⟨inWorld, fun held => by simp [outside] at held⟩

omit [DecidableEq O] in
/-- **On an empty fiber an upsert is an insertion**: it takes nothing. -/
theorem upsert_eq_insert {label : O → T} {world : Finset O} {region : T → Bool} {made : O}
    (empty : regionOf label world region = ∅) :
    upsert label world region made = ⟨∅, ∅, {made}, []⟩ := by
  simp only [upsert, empty]

omit [DecidableEq O] in
/-- **On a fiber of one occurrence an upsert replaces it.** -/
theorem upsert_eq_replace {label : O → T} {world : Finset O} {region : T → Bool} {made old : O}
    (single : regionOf label world region = {old}) :
    upsert label world region made = ⟨{old}, ∅, {made}, []⟩ := by
  simp only [upsert, single]

omit [DecidableEq O] in
/-- **An upsert depends on its world only through the region's fiber.** -/
theorem upsert_congr {label : O → T} {world world' : Finset O} {region : T → Bool} {made : O}
    (same : regionOf label world region = regionOf label world' region) :
    upsert label world region made = upsert label world' region made := by
  simp only [upsert, same]

/-- **Two upserts read before either fired both stay**: the second, whose fiber was read in the world before the
first fired, does not take the first's occurrence, so the fiber ends with both. -/
theorem stale_upserts_double {label : O → T} {world : Finset O} {region : T → Bool} {made₁ made₂ : O}
    (inside₁ : region (label made₁) = true) (inside₂ : region (label made₂) = true)
    (fresh₁ : made₁ ∉ world) :
    regionOf label (fire (fire world (upsert label world region made₁)) (upsert label world region made₂))
      region = {made₁, made₂} := by
  have first := upsert_fiber (label := label) (world := world) (region := region) inside₁
  generalize fire world (upsert label world region made₁) = after at first ⊢
  ext o
  have firstAt := Finset.ext_iff.mp first o
  simp only [regionOf, Finset.mem_filter, Finset.mem_singleton] at firstAt
  simp only [regionOf, fire, upsert, Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff,
    Finset.mem_singleton, Finset.mem_insert]
  constructor
  · rintro ⟨(⟨inAfter, _⟩ | rfl), inRegion⟩
    · exact Or.inl (firstAt.mp ⟨inAfter, inRegion⟩)
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨Or.inl ⟨(firstAt.mpr rfl).1, fun held => fresh₁ held.1⟩, inside₁⟩
    · exact ⟨Or.inr rfl, inside₂⟩

/-- **The second read after the first fired leaves one occurrence.** -/
theorem sequential_upserts_single {label : O → T} {world : Finset O} {region : T → Bool} {made₁ made₂ : O}
    (inside₂ : region (label made₂) = true) :
    regionOf label (fire (fire world (upsert label world region made₁))
        (upsert label (fire world (upsert label world region made₁)) region made₂)) region = {made₂} :=
  upsert_fiber inside₂

/-- **An upsert leaves the fiber of a disjoint region as it was.** -/
theorem upsert_keeps_disjoint_fiber {label : O → T} {world : Finset O} {region other : T → Bool} {made : O}
    (inside : region (label made) = true) (disjoint : ∀ t, region t = true → other t = false) :
    regionOf label (fire world (upsert label world region made)) other = regionOf label world other := by
  apply regionOf_fire_of_no_write
  intro o member
  simp only [upsert, Finset.mem_union, Finset.mem_singleton, regionOf, Finset.mem_filter] at member
  rcases member with ⟨_, inRegion⟩ | rfl
  · exact disjoint _ inRegion
  · exact disjoint _ inside

/-- **Upserts into disjoint regions commute**, each reading its fiber in the world it fires in. -/
theorem upserts_commute_of_disjoint {label : O → T} {world : Finset O} {region₁ region₂ : T → Bool}
    {made₁ made₂ : O} (inside₁ : region₁ (label made₁) = true) (inside₂ : region₂ (label made₂) = true)
    (disjoint : ∀ t, region₁ t = true → region₂ t = false) :
    fire (fire world (upsert label world region₁ made₁))
        (upsert label (fire world (upsert label world region₁ made₁)) region₂ made₂) =
      fire (fire world (upsert label world region₂ made₂))
        (upsert label (fire world (upsert label world region₂ made₂)) region₁ made₁) := by
  have disjoint' : ∀ t, region₂ t = true → region₁ t = false := by
    intro t inTwo
    cases inOne : region₁ t
    · rfl
    · simp [disjoint t inOne] at inTwo
  rw [upsert_congr (upsert_keeps_disjoint_fiber inside₁ disjoint),
    upsert_congr (upsert_keeps_disjoint_fiber inside₂ disjoint')]
  have notIn₂ : made₁ ∉ regionOf label world region₂ := by
    simp only [regionOf, Finset.mem_filter, not_and]
    intro _ inTwo
    simp [disjoint _ inside₁] at inTwo
  have notIn₁ : made₂ ∉ regionOf label world region₁ := by
    simp only [regionOf, Finset.mem_filter, not_and]
    intro _ inOne
    simp [disjoint' _ inside₂] at inOne
  ext o
  simp only [fire, upsert, Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton]
  constructor
  · rintro (⟨(⟨inWorld, not₁⟩ | rfl), not₂⟩ | rfl)
    · exact Or.inl ⟨Or.inl ⟨inWorld, not₂⟩, not₁⟩
    · exact Or.inr rfl
    · exact Or.inl ⟨Or.inr rfl, notIn₁⟩
  · rintro (⟨(⟨inWorld, not₂⟩ | rfl), not₁⟩ | rfl)
    · exact Or.inl ⟨Or.inl ⟨inWorld, not₁⟩, not₂⟩
    · exact Or.inr rfl
    · exact Or.inl ⟨Or.inr rfl, notIn₂⟩

/-- **Makes of fresh occurrences commute.** -/
theorem makes_commute (world : Finset O) (made₁ made₂ : O) :
    fire (fire world (⟨∅, ∅, {made₁}, []⟩ : Commit O T)) (⟨∅, ∅, {made₂}, []⟩ : Commit O T) =
      fire (fire world (⟨∅, ∅, {made₂}, []⟩ : Commit O T)) (⟨∅, ∅, {made₁}, []⟩ : Commit O T) := by
  ext o
  simp only [fire, Finset.mem_union, Finset.mem_sdiff, Finset.notMem_empty, not_false_eq_true,
    and_true, Finset.mem_singleton]
  tauto

namespace Controls

/-- **An add that replaced what its region held would depend on order.** Replacing the one occurrence of `{0}` by
`1` and then by `2` ends with `{2}`; the other order ends with `{1}`. -/
theorem overwriting_adds_depend_on_order :
    fire (fire {0} (upsert (fun _ : ℕ => true) {0} id 1))
        (upsert (fun _ : ℕ => true) (fire {0} (upsert (fun _ : ℕ => true) {0} id 1)) id 2) ≠
      fire (fire {0} (upsert (fun _ : ℕ => true) {0} id 2))
        (upsert (fun _ : ℕ => true) (fire {0} (upsert (fun _ : ℕ => true) {0} id 2)) id 1) := by
  decide

end Controls

#print axioms upsert_fiber
#print axioms upsert_outside
#print axioms upsert_eq_insert
#print axioms upsert_eq_replace
#print axioms upsert_congr
#print axioms stale_upserts_double
#print axioms sequential_upserts_single
#print axioms upsert_keeps_disjoint_fiber
#print axioms upserts_commute_of_disjoint
#print axioms makes_commute
#print axioms Controls.overwriting_adds_depend_on_order

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RegionUpserts
