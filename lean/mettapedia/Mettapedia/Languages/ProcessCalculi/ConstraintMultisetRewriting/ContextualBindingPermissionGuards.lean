import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingPermissions

/-!
# Binding footprints of contextual absence and count observations

A guard depends on its query and the captures of every watched row. Schema
locals remain per-use existential witnesses; captured variables in those
schemas are part of the caller dependency footprint. In particular, a closed
query does not eliminate dependencies hidden in an open shared row.

The world and row inventory are held fixed in these information-locality
laws. Physical removal, publication or replacement of watched occurrences
has a separate footprint condition.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingPermissionGuards

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualBindingPermissions ContextualGuardMatching

variable {S : Signature} {Local V W : Type} {O : Type*}
  (locals : Local → MetaArity S) {declarations : V → MetaArity S}
  {future : W → MetaArity S} {Γ : Ctx S} {sort : S.Srt}

def capturedNames : List (Local ⊕ V) → List V
  | [] => []
  | .inl _ :: rest => capturedNames rest
  | .inr name :: rest => name :: capturedNames rest

theorem mem_capturedNames (names : List (Local ⊕ V)) (name : V) :
    name ∈ capturedNames names ↔ Sum.inr name ∈ names := by
  induction names with
  | nil => simp [capturedNames]
  | cons head rest ih => cases head <;> simp [capturedNames, ih]

def rowNames : ContextualStoredRows.Row locals declarations Γ sort → List V
  | .shared value => support value
  | .schema body => capturedNames (support body)

theorem matches_congr (first second : Assignment declarations future)
    (pattern : Term (signature S future) Γ sort)
    (row : ContextualStoredRows.Row locals declarations Γ sort)
    (agree : ∀ name ∈ rowNames locals row, first name = second name) :
    Matches locals first pattern row ↔ Matches locals second pattern row := by
  cases row with
  | shared value =>
      change (pattern = instantiate first value) ↔ (pattern = instantiate second value)
      rw [instantiate_congr first second value agree]
  | schema body =>
      have bodySame (extension : Extension future)
          (localBodies : Assignment locals extension.declarations) :
          instantiate (instanceAssignment locals localBodies extension.assignment first) body =
            instantiate (instanceAssignment locals localBodies extension.assignment second) body := by
        apply instantiate_congr
        intro name member
        cases name with
        | inl localName => rfl
        | inr captured =>
            exact congrArg (instantiate extension.assignment)
              (agree captured ((mem_capturedNames (support body) captured).mpr member))
      constructor
      · rintro ⟨extension, localBodies, matched⟩
        exact ⟨extension, localBodies, (bodySame extension localBodies).symm.trans matched⟩
      · rintro ⟨extension, localBodies, matched⟩
        exact ⟨extension, localBodies, (bodySame extension localBodies).trans matched⟩

noncomputable def guardNames (rows : O → ContextualStoredRows.Row locals declarations Γ sort)
    (world : Finset O) : Check (Term (signature S declarations) Γ sort) → List V
  | .equal left right => support left ++ support right
  | .absent pattern | .count pattern _ =>
      support pattern ++ world.toList.flatMap (fun occurrence => rowNames locals (rows occurrence))

theorem region_congr (first second : Assignment declarations future)
    (rows : O → ContextualStoredRows.Row locals declarations Γ sort) (world : Finset O)
    (pattern : Term (signature S declarations) Γ sort)
    (queryAgree : ∀ name ∈ support pattern, first name = second name)
    (rowAgree : ∀ occurrence ∈ world, ∀ name ∈ rowNames locals (rows occurrence),
      first name = second name) :
    ContextualGuardSemantics.region locals first rows world pattern =
      ContextualGuardSemantics.region locals second rows world pattern := by
  classical
  have querySame := instantiate_congr first second pattern queryAgree
  ext occurrence
  simp only [ContextualGuardSemantics.mem_region]
  by_cases present : occurrence ∈ world
  · simp only [present, true_and, querySame]
    exact matches_congr locals first second _ (rows occurrence) (rowAgree occurrence present)
  · simp [present]

theorem holds_congr (first second : Assignment declarations future)
    (rows : O → ContextualStoredRows.Row locals declarations Γ sort) (world : Finset O)
    (check : Check (Term (signature S declarations) Γ sort))
    (agree : ∀ name ∈ guardNames locals rows world check, first name = second name) :
    ContextualGuardSemantics.Holds locals first rows world check ↔
      ContextualGuardSemantics.Holds locals second rows world check := by
  classical
  cases check with
  | equal left right =>
      exact equation_congr first second (left, right) agree
  | absent pattern =>
      rw [ContextualGuardSemantics.absent_iff_empty, ContextualGuardSemantics.absent_iff_empty]
      rw [region_congr locals first second rows world pattern
        (fun name member => agree name (List.mem_append_left _ member)) (by
          intro occurrence present name member
          exact agree name (List.mem_append_right _ (List.mem_flatMap.mpr
            ⟨occurrence, Finset.mem_toList.mpr present, member⟩)))]
  | count pattern number =>
      change (ContextualGuardSemantics.region locals first rows world pattern).card = number ↔
        (ContextualGuardSemantics.region locals second rows world pattern).card = number
      rw [region_congr locals first second rows world pattern
        (fun name member => agree name (List.mem_append_left _ member)) (by
          intro occurrence present name member
          exact agree name (List.mem_append_right _ (List.mem_flatMap.mpr
            ⟨occurrence, Finset.mem_toList.mpr present, member⟩)))]

/-- Generator observations record this finite capture footprint without
forgetting the different object contexts and sorts of the names. -/
noncomputable def guardObservations (rows : O → ContextualStoredRows.Row locals declarations Γ sort)
    (world : Finset O) (check : Check (Term (signature S declarations) Γ sort)) :
    List (Observation S declarations) :=
  (guardNames locals rows world check).map fun name => observe (generator declarations name)

theorem guard_name_is_observation_root
    (rows : O → ContextualStoredRows.Row locals declarations Γ sort) (world : Finset O)
    (check : Check (Term (signature S declarations) Γ sort)) (caller : List (Observation S declarations))
    {name : V} (member : name ∈ guardNames locals rows world check) :
    name ∈ observationRoots (caller ++ guardObservations locals rows world check) := by
  refine ⟨observe (generator declarations name), ?_, ?_⟩
  · exact List.mem_append_right _ (List.mem_map.mpr ⟨name, member, rfl⟩)
  · exact (support_generator name).symm ▸ List.mem_singleton_self name

/-- The source Ask is preserved in both directions, in every future family.
The permission checks the complete query-and-row dependency footprint. -/
theorem permitted_ask_iff (granted : Set V)
    (old added : EquationStore (Term (signature S declarations) Γ sort))
    (rows : O → ContextualStoredRows.Row locals declarations Γ sort) (world : Finset O)
    (check : Check (Term (signature S declarations) Γ sort)) (caller : List (Observation S declarations))
    (permission : Permitted granted old added (caller ++ guardObservations locals rows world check))
    (consistent : (ContextualFamilies.action declarations Γ sort).Consistent (old ++ added)) :
    ContextualGuardSemantics.Ask locals (old ++ added) rows world check ↔
      ContextualGuardSemantics.Ask locals old rows world check := by
  constructor
  · intro asked Future future candidate candidateModel
    obtain ⟨extended, model, agree⟩ := extend_joint_component
      (protectedComponent old (caller ++ guardObservations locals rows world check)) old added
      (dependencyClosure_closed old _) permission.avoids consistent candidate candidateModel
    have same := holds_congr locals extended candidate rows world check (fun name member =>
      agree name (DependencyClosure.root (guard_name_is_observation_root locals rows world check caller member)))
    exact same.mp (asked Future future extended model)
  · exact fun asked => ContextualGuardSemantics.Ask.append locals asked added

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingPermissionGuards
