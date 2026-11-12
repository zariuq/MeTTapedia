import Mettapedia.Languages.MeTTa.PeTTa.OutputPlanCompiler

/-!
# Private procedure names preserve source interfaces without collisions

All finite source spellings remain legal. Reservation chooses new target
names outside the supplied support, preserves interface order and does not
reuse an earlier target. This is compile-time freshness, not runtime
revalidation of each call.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.OutputPlan

theorem reserve_support_grows (used : Finset String) (interfaces : List (String × Nat)) :
    used ⊆ (reserveNames used interfaces).1 := by
  induction interfaces generalizing used with
  | nil => exact Finset.Subset.refl _
  | cons interface rest ih =>
      rcases interface with ⟨source,arity⟩
      exact Finset.Subset.trans (Finset.subset_insert _ _) (ih _)

theorem reserved_targets_live (used : Finset String) (interfaces : List (String × Nat)) :
    ∀ signature ∈ (reserveNames used interfaces).2,
      signature.target ∈ (reserveNames used interfaces).1 := by
  induction interfaces generalizing used with
  | nil => intro signature present; cases present
  | cons interface rest ih =>
      rcases interface with ⟨source,arity⟩
      intro signature present
      rcases List.mem_cons.mp present with rfl | later
      · exact reserve_support_grows _ rest (Finset.mem_insert_self _ _)
      · exact ih _ signature later

theorem reserved_targets_fresh (used : Finset String) (interfaces : List (String × Nat)) :
    ∀ signature ∈ (reserveNames used interfaces).2, signature.target ∉ used := by
  induction interfaces generalizing used with
  | nil => intro signature present; cases present
  | cons interface rest ih =>
      rcases interface with ⟨source,arity⟩
      intro signature present
      rcases List.mem_cons.mp present with rfl | later
      · exact Mettapedia.FreshString.fresh_not_mem used
      · intro old
        exact ih _ signature later (Finset.mem_insert_of_mem old)

theorem reserved_targets_distinct (used : Finset String) (interfaces : List (String × Nat)) :
    ((reserveNames used interfaces).2.map Signature.target).Nodup := by
  induction interfaces generalizing used with
  | nil => exact List.nodup_nil
  | cons interface rest ih =>
      rcases interface with ⟨source,arity⟩
      apply List.nodup_cons.mpr
      refine ⟨?_,ih _⟩
      intro repeated
      obtain ⟨signature,present,same⟩ := List.mem_map.mp repeated
      exact reserved_targets_fresh _ rest signature present
        (same ▸ Finset.mem_insert_self _ _)

theorem reserved_interfaces_exact (used : Finset String) (interfaces : List (String × Nat)) :
    (reserveNames used interfaces).2.map (fun signature => (signature.source,signature.arity)) = interfaces := by
  induction interfaces generalizing used with
  | nil => rfl
  | cons interface rest ih =>
      rcases interface with ⟨source,arity⟩
      simpa only [reserveNames,List.map_cons,List.cons.injEq,true_and] using ih _

end Mettapedia.Languages.MeTTa.PeTTa.OutputPlan
