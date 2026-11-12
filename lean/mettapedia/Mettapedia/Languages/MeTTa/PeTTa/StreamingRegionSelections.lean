import Mettapedia.Languages.MeTTa.PeTTa.StreamingRegions
import Mettapedia.Data.List.FirstSelectionInvariant

/-!
# Exact marker selection and collection association

First-demand cuts reach the marker named by the saved frame. Updating an
answer bank retains that marker's identity, original bindings and exact
caller. Untouched older jobs keep their links to later markers.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Streaming.Regions

open List.FirstSelection (After Change)

def selectFirst (key : Nat) : Boundary → Bool
  | .first found => found == key
  | _ => false

def selectHandler (key : Nat) : Boundary → Bool
  | .handler found => found == key
  | _ => false

theorem after_markers {selected : Job → Bool} {pick : Boundary → Bool}
    (compatible : ∀ job, selected job = (boundary job).any pick)
    {older remaining : List Job} (found : After selected older remaining) :
    After pick (markers older) (markers remaining) := by
  induction found with
  | @here first rest yes =>
      cases kind : boundary first with
      | none => simp only [compatible,kind,Option.any_none,Bool.false_eq_true] at yes
      | some scope =>
          have chosen : pick scope = true := by simpa only [compatible,kind,Option.any_some] using yes
          simpa only [markers,List.filterMap_cons,kind] using
            (After.here chosen : After pick (scope :: markers rest) (markers rest))
  | @skip first rest remaining missed found ih =>
      cases kind : boundary first with
      | none => simpa only [markers,List.filterMap_cons,kind] using ih
      | some scope =>
          have no : pick scope = false := by simpa only [compatible,kind,Option.any_some] using missed
          simpa only [markers,List.filterMap_cons,kind] using After.skip no ih

theorem selected_after_ordered (limit : Nat) (before : List Boundary) (chosen : Boundary)
    (after : List Boundary) (good : ordered limit (before ++ chosen :: after))
    (pick : Boundary → Bool) (yes : pick chosen = true)
    (only : ∀ scope, pick scope = true → scope.key = chosen.key) :
    After pick (before ++ chosen :: after) after := by
  apply After.of_append _ yes
  intro scope present
  cases choice : pick scope with
  | false => rfl
  | true => exact False.elim (ordered_before_key_ne limit before chosen after good scope present (only scope choice))

theorem first_cut {limit key : Nat} {older remaining : List Job} {caller : List Frame}
    (good : ordered limit (markers older))
    (fits : framesFit (markers older) (.first key :: caller))
    (found : After (firstMarker key) older remaining) : framesFit (markers remaining) caller := by
  obtain ⟨before,after,shape,nested⟩ := fits
  have selected : After (selectFirst key) (markers older) after := by
    rw [shape]
    apply selected_after_ordered limit before (.first key) after (by rw [← shape]; exact good) _
      (by simp [selectFirst])
    intro scope yes
    cases scope <;> simp_all [selectFirst,Boundary.key]
  have actual := after_markers (selected := firstMarker key) (pick := selectFirst key)
    (by intro job; cases job <;> rfl) found
  have same := selected.unique actual
  rw [← same]
  exact nested

theorem handler_cut {limit key : Nat} {older remaining : List Job} {caller : List Frame}
    (good : ordered limit (markers older))
    (fits : framesFit (markers older) (.handler key :: caller))
    (found : After (handlerMarker key) older remaining) : framesFit (markers remaining) caller := by
  obtain ⟨before,after,shape,nested⟩ := fits
  have selected : After (selectHandler key) (markers older) after := by
    rw [shape]
    apply selected_after_ordered limit before (.handler key) after (by rw [← shape]; exact good) _
      (by simp [selectHandler])
    intro scope yes
    cases scope <;> simp_all [selectHandler,Boundary.key]
  have actual := after_markers (selected := handlerMarker key) (pick := selectHandler key)
    (by intro job; cases job <;> rfl) found
  have same := selected.unique actual
  rw [← same]
  exact nested

theorem selected_suffix_valid {limit : Nat} {selected : Job → Bool} {older remaining : List Job}
    (good : valid limit older) (found : After selected older remaining) : valid limit remaining := by
  obtain ⟨before,chosen,shape,yes,earlier⟩ := found.prefix
  apply valid_suffix limit (before ++ [chosen]) remaining
  simpa only [List.append_assoc,List.singleton_append] using shape ▸ good

theorem collection_change_exact (key : Nat) (answer : Unifying.Answer) (first next : Job)
    (changed : collectionChange key answer first = some next) :
    ∃ bindings caller bank,
      first = .collect key bindings caller bank ∧
      next = .collect key bindings caller (bank ++ [answer]) := by
  cases first with
  | execute task | handler found | first found => simp only [collectionChange] at changed; cases changed
  | collect found bindings caller bank =>
      simp only [collectionChange] at changed
      split at changed
      next yes =>
        have same : found = key := by simpa only [beq_iff_eq] using yes
        subst found
        cases changed
        exact ⟨bindings,caller,bank,rfl,rfl⟩
      next no => cases changed

theorem collection_change_shape (key : Nat) (answer : Unifying.Answer) (first next : Job)
    (changed : collectionChange key answer first = some next) :
    boundary next = boundary first ∧ ∀ scopes, jobFits scopes next ↔ jobFits scopes first := by
  obtain ⟨bindings,caller,bank,rfl,rfl⟩ := collection_change_exact key answer first next changed
  exact ⟨rfl,fun _ => Iff.rfl⟩

theorem collection_markers {key : Nat} {answer : Unifying.Answer} {older changed : List Job}
    (recorded : Change (collectionChange key answer) older changed) : markers changed = markers older := by
  induction recorded with
  | here replaced =>
      simp only [markers,List.filterMap_cons,(collection_change_shape _ _ _ _ replaced).1]
  | skip missed recorded ih =>
      unfold markers at ih ⊢
      simp only [List.filterMap_cons]
      rw [ih]

theorem collection_linked {key : Nat} {answer : Unifying.Answer} {older changed : List Job}
    (recorded : Change (collectionChange key answer) older changed) (good : linked older) : linked changed := by
  induction recorded with
  | here replaced => exact ⟨((collection_change_shape _ _ _ _ replaced).2 _).mpr good.1,good.2⟩
  | skip missed recorded ih =>
      exact ⟨by rw [collection_markers recorded]; exact good.1,ih good.2⟩

theorem collection_valid {limit key : Nat} {answer : Unifying.Answer} {older changed : List Job}
    (recorded : Change (collectionChange key answer) older changed) (good : valid limit older) : valid limit changed :=
  ⟨by rw [collection_markers recorded]; exact good.1,collection_linked recorded good.2⟩

theorem collection_record_split {key : Nat} {answer : Unifying.Answer} {older changed : List Job}
    (recorded : Change (collectionChange key answer) older changed) :
    ∃ before bindings caller bank after,
      older = before ++ .collect key bindings caller bank :: after ∧
      changed = before ++ .collect key bindings caller (bank ++ [answer]) :: after ∧
      ∀ job ∈ before, collectionChange key answer job = none := by
  obtain ⟨before,first,next,after,original,result,replaced,earlier⟩ := recorded.prefix
  obtain ⟨bindings,caller,bank,rfl,rfl⟩ := collection_change_exact _ _ first next replaced
  exact ⟨before,bindings,caller,bank,after,original,result,earlier⟩

theorem marker_mem_of_job {job : Job} {scope : Boundary} {agenda : List Job}
    (present : job ∈ agenda) (kind : boundary job = some scope) : scope ∈ markers agenda :=
  List.mem_filterMap.mpr ⟨job,present,kind⟩

theorem collection_associated {limit key : Nat} {answer : Unifying.Answer}
    {older changed : List Job} {caller : List Frame}
    (good : ordered limit (markers older))
    (fits : framesFit (markers older) (.collection key :: caller))
    (recorded : Change (collectionChange key answer) older changed) :
    ∃ before bindings bank after,
      older = before ++ .collect key bindings caller bank :: after ∧
      changed = before ++ .collect key bindings caller (bank ++ [answer]) :: after ∧
      ∀ job ∈ before, collectionChange key answer job = none := by
  obtain ⟨left,right,shape,nested⟩ := fits
  have expected : Boundary.collection key caller ∈ markers older := by
    rw [shape]
    exact List.mem_append_right _ List.mem_cons_self
  obtain ⟨before,bindings,saved,bank,after,original,result,earlier⟩ := collection_record_split recorded
  have actual : Boundary.collection key saved ∈ markers older := by
    apply marker_mem_of_job (job := .collect key bindings saved bank) _ rfl
    rw [original]
    exact List.mem_append_right _ List.mem_cons_self
  have identical := ordered_key_unique good actual expected rfl
  have sameCaller : saved = caller := (Boundary.collection.inj identical).2
  subst saved
  exact ⟨before,bindings,bank,after,original,result,earlier⟩

theorem collection_resolves {key : Nat} {answer : Unifying.Answer} {older : List Job} {caller : List Frame}
    (fits : framesFit (markers older) (.collection key :: caller)) :
    ∃ changed, Change (collectionChange key answer) older changed := by
  obtain ⟨before,after,shape,nested⟩ := fits
  have present : Boundary.collection key caller ∈ markers older := by
    rw [shape]
    exact List.mem_append_right _ List.mem_cons_self
  obtain ⟨job,inOlder,kind⟩ := List.mem_filterMap.mp present
  cases job with
  | execute task | handler found | first found => cases kind
  | collect found bindings saved bank =>
      simp only [boundary,Option.some.injEq,Boundary.collection.injEq] at kind
      obtain ⟨rfl,rfl⟩ := kind
      exact Change.exists_of_mem (next := .collect found bindings saved (bank ++ [answer])) inOlder
        (by simp only [collectionChange,beq_self_eq_true,↓reduceIte])

theorem first_resolves {key : Nat} {older : List Job} {caller : List Frame}
    (fits : framesFit (markers older) (.first key :: caller)) :
    ∃ remaining, After (firstMarker key) older remaining := by
  obtain ⟨before,after,shape,nested⟩ := fits
  have present : Boundary.first key ∈ markers older := by
    rw [shape]
    exact List.mem_append_right _ List.mem_cons_self
  obtain ⟨job,inOlder,kind⟩ := List.mem_filterMap.mp present
  cases job with
  | execute task | handler found | collect found bindings saved bank => cases kind
  | first found =>
      simp only [boundary,Option.some.injEq,Boundary.first.injEq] at kind
      subst found
      exact After.exists_of_mem inOlder (by simp [firstMarker])

theorem handles_marker {key : Nat} {scopes : List Boundary} {frames : List Frame}
    (handler : Handles frames key) (fits : framesFit scopes frames) : .handler key ∈ scopes := by
  induction handler with
  | here key caller =>
      obtain ⟨before,after,shape,nested⟩ := fits
      rw [shape]
      exact List.mem_append_right _ List.mem_cons_self
  | source handler ih | collection handler ih | first handler ih => exact ih (frames_tail fits)

theorem handler_resolves {key : Nat} {older : List Job} {frames : List Frame}
    (handler : Handles frames key) (fits : framesFit (markers older) frames) :
    ∃ remaining, After (handlerMarker key) older remaining := by
  obtain ⟨job,inOlder,kind⟩ := List.mem_filterMap.mp (handles_marker handler fits)
  cases job with
  | execute task | first found | collect found bindings saved bank => cases kind
  | handler found =>
      simp only [boundary,Option.some.injEq,Boundary.handler.injEq] at kind
      subst found
      exact After.exists_of_mem inOlder (by simp [handlerMarker])

end Mettapedia.Languages.MeTTa.PeTTa.Streaming.Regions
