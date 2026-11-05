import Mettapedia.Languages.CHR.Syntax
import Mettapedia.Data.List.OptionMapM

/-! Instantiation is total on terms whose variables are supplied by the
source environment. These source laws do not mention the compiler or runner.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.CHR

open Mettapedia.Data.List (option_mapM_exists option_mapM_input)

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
    obtain ⟨values, read⟩ := option_mapM_exists (Term.instantiate environment) fields children
    refine ⟨.tuple values, ?_⟩
    rw [Term.instantiate, read]
    rfl
termination_by sizeOf source

theorem Term.instantiate_variables (environment : Environment) (source : Term)
    {value : Value} (read : source.instantiate environment = some value) :
    ∀ index ∈ source.variables, ∃ supplied, lookup environment index = some supplied := by
  cases source with
  | value datum => simp [Term.variables]
  | var index =>
      intro queried member
      have same : queried = index := by simpa only [Term.variables, List.mem_singleton] using member
      subst queried
      exact ⟨value, by simpa only [Term.instantiate] using read⟩
  | tuple fields =>
      cases children : fields.mapM (Term.instantiate environment) with
      | none => simp [Term.instantiate, children] at read
      | some values =>
          intro index member
          rw [Term.variables] at member
          obtain ⟨field, present, occurs⟩ := List.mem_flatMap.mp member
          obtain ⟨child, childRead⟩ := option_mapM_input (Term.instantiate environment) fields children field present
          exact Term.instantiate_variables environment field childRead index occurs
termination_by sizeOf source

theorem Term.instantiate_exists_iff (environment : Environment) (source : Term) :
    (∃ value, source.instantiate environment = some value) ↔
      ∀ index ∈ source.variables, ∃ supplied, lookup environment index = some supplied :=
  ⟨fun ⟨_, read⟩ => source.instantiate_variables environment read,
   source.instantiate_exists environment⟩

theorem Head.instantiate_exists (environment : Environment) (source : Head)
    (available : ∀ index ∈ source.variables, ∃ value, lookup environment index = some value) :
    ∃ value, source.instantiate environment = some value := by
  have children : ∀ field ∈ source.arguments, ∃ value, field.instantiate environment = some value := by
    intro field member
    apply Term.instantiate_exists environment field
    intro index occurrence
    exact available index (List.mem_flatMap.mpr ⟨field, member, occurrence⟩)
  obtain ⟨values, read⟩ := option_mapM_exists (Term.instantiate environment) source.arguments children
  exact ⟨⟨source.name, values⟩, by simp [Head.instantiate, read]⟩

theorem Head.instantiate_variables (environment : Environment) (source : Head)
    {value : Constraint} (read : source.instantiate environment = some value) :
    ∀ index ∈ source.variables, ∃ supplied, lookup environment index = some supplied := by
  unfold Head.instantiate at read
  change ((source.arguments.mapM (Term.instantiate environment)).bind fun fields =>
    some (Constraint.mk source.name fields)) = some value at read
  simp only [Option.bind_eq_some_iff, Option.some.injEq] at read
  obtain ⟨values, children, _⟩ := read
  intro index member
  change index ∈ source.arguments.flatMap Term.variables at member
  obtain ⟨field, present, occurs⟩ := List.mem_flatMap.mp member
  obtain ⟨child, childRead⟩ := option_mapM_input (Term.instantiate environment) source.arguments children field present
  exact field.instantiate_variables environment childRead index occurs

theorem Head.instantiate_exists_iff (environment : Environment) (source : Head) :
    (∃ value, source.instantiate environment = some value) ↔
      ∀ index ∈ source.variables, ∃ supplied, lookup environment index = some supplied :=
  ⟨fun ⟨_, read⟩ => source.instantiate_variables environment read,
   source.instantiate_exists environment⟩

#print axioms Term.instantiate_exists
#print axioms Head.instantiate_exists
#print axioms Term.instantiate_variables
#print axioms Head.instantiate_variables

end Mettapedia.Languages.CHR
