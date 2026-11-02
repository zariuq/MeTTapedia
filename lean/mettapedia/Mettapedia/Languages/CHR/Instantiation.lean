import Mettapedia.Languages.CHR.Syntax

/-! Instantiation is total on terms whose variables are supplied by the
source environment. These source laws do not mention the compiler or runner.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.CHR

theorem lookup_cons (name query : Nat) (value : Value) (rest : Environment) :
    lookup ((name, value) :: rest) query = if name == query then some value else lookup rest query := by
  by_cases same : name = query
  · subst query
    simp [lookup]
  · have different : (name == query) = false := beq_eq_false_iff_ne.mpr same
    simp [lookup, different]

theorem lookup_member (environment : Environment) (name : Nat) (value : Value)
    (found : lookup environment name = some value) : (name, value) ∈ environment := by
  unfold lookup at found
  cases selected : environment.find? (fun entry => entry.1 == name) with
  | none => simp [selected] at found
  | some entry =>
    have member := List.mem_of_find?_eq_some selected
    have named := List.find?_some selected
    simp only [beq_iff_eq] at named
    simp only [selected, Option.map_some, Option.some.injEq] at found
    cases entry with
    | mk actualName actualValue =>
      dsimp only at named found member
      subst actualName
      subst actualValue
      exact member

private theorem traverse_exists {α β : Type} (operation : α → Option β) (inputs : List α)
    (available : ∀ input ∈ inputs, ∃ value, operation input = some value) :
    ∃ values, inputs.mapM operation = some values := by
  induction inputs with
  | nil => exact ⟨[], rfl⟩
  | cons first rest ih =>
    obtain ⟨value, firstRead⟩ := available first List.mem_cons_self
    obtain ⟨values, restRead⟩ := ih (fun input member => available input (List.mem_cons_of_mem first member))
    exact ⟨value :: values, by simp [List.mapM_cons, firstRead, restRead]⟩

theorem Term.instantiate_exists (environment : Environment) (source : Term)
    (available : ∀ index ∈ source.variables, ∃ value, lookup environment index = some value) :
    ∃ value, source.instantiate environment = some value := by
  cases source with
  | value datum => exact ⟨datum, by rw [Term.instantiate]⟩
  | var index => simpa only [Term.instantiate] using available index (by simp [Term.variables])
  | tuple fields =>
    have children : ∀ field ∈ fields, ∃ value, field.instantiate environment = some value := by
      intro field member
      apply Term.instantiate_exists environment field
      intro index occurrence
      apply available index
      rw [Term.variables]
      exact List.mem_flatMap.mpr ⟨field, member, occurrence⟩
    obtain ⟨values, read⟩ := traverse_exists (Term.instantiate environment) fields children
    refine ⟨.tuple values, ?_⟩
    rw [Term.instantiate, read]
    rfl
termination_by sizeOf source

theorem Head.instantiate_exists (environment : Environment) (source : Head)
    (available : ∀ index ∈ source.variables, ∃ value, lookup environment index = some value) :
    ∃ value, source.instantiate environment = some value := by
  have children : ∀ field ∈ source.arguments, ∃ value, field.instantiate environment = some value := by
    intro field member
    apply Term.instantiate_exists environment field
    intro index occurrence
    exact available index (List.mem_flatMap.mpr ⟨field, member, occurrence⟩)
  obtain ⟨values, read⟩ := traverse_exists (Term.instantiate environment) source.arguments children
  exact ⟨⟨source.name, values⟩, by simp [Head.instantiate, read]⟩

#print axioms Term.instantiate_exists
#print axioms Head.instantiate_exists

end Mettapedia.Languages.CHR
