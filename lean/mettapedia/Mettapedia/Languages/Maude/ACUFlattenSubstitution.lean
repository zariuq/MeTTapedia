import Mettapedia.Languages.Maude.ACUFold

/-! Substitution through the physical ACU presentation. A variable can
denote a whole bag. Flattening splices its components, while the declared
ground identity remains the same term under substitution. These lemmas use
the source signature and do not change the raw term codec or admission.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Maude.ACUOperation

variable {theory : Theory} {context : VariableContext}

theorem unit_ground (operation : ACUOperation theory context) (checked : theory.signature.check = true) :
    operation.unit.variables = [] := by
  simp only [Signature.check, Bool.and_eq_true, List.all_eq_true] at checked
  have formed := checked.2 operation.declaration operation.declared
  rw [operation.identity] at formed
  simp only [Bool.and_eq_true] at formed
  exact List.isEmpty_iff.mp formed.2.1.1

theorem unit_not_merge (operation : ACUOperation theory context) (checked : theory.signature.check = true)
    (left right : Term) : operation.unit ≠ operation.merge left right := by
  simp only [Signature.check, Bool.and_eq_true, List.all_eq_true] at checked
  have formed := checked.2 operation.declaration operation.declared
  rw [operation.identity] at formed
  simp only [Bool.and_eq_true] at formed
  have root := formed.2.2
  cases unitShape : operation.unit with
  | var name => simp only [unitShape, Bool.false_eq_true] at root
  | app label arguments =>
    have different : label ≠ operation.declaration.id := by simpa only [unitShape, bne_iff_ne] using root
    intro same
    exact different (Term.app.inj same).1

theorem flatten_unit (operation : ACUOperation theory context) : operation.flatten operation.unit = [] := by
  rw [flatten.eq_def, if_pos rfl]

theorem flatten_merge (operation : ACUOperation theory context) (checked : theory.signature.check = true)
    (left right : Term) : operation.flatten (operation.merge left right) =
      operation.flatten left ++ operation.flatten right := by
  have different : operation.merge left right ≠ operation.unit := Ne.symm (operation.unit_not_merge checked left right)
  rw [flatten.eq_def, if_neg different]
  simp only [merge, if_true]

theorem flatten_decompose (operation : ACUOperation theory context) (term : Term) :
    term = operation.unit ∨ (∃ left right, term = operation.merge left right) ∨ operation.flatten term = [term] := by
  by_cases unit : term = operation.unit
  · exact .inl unit
  · cases term with
    | var name => exact .inr (.inr (by rw [flatten.eq_def, if_neg unit]))
    | app label arguments =>
      cases arguments with
      | nil => exact .inr (.inr (by rw [flatten.eq_def, if_neg unit]))
      | cons first rest =>
        cases rest with
        | nil => exact .inr (.inr (by rw [flatten.eq_def, if_neg unit]))
        | cons second tail =>
          cases tail with
          | cons third rest => exact .inr (.inr (by rw [flatten.eq_def, if_neg unit]))
          | nil =>
            by_cases selected : label = operation.declaration.id
            · exact .inr (.inl ⟨first, second, by subst label; rfl⟩)
            · exact .inr (.inr (by rw [flatten.eq_def, if_neg unit]; exact if_neg selected))

theorem flatten_stable (operation : ACUOperation theory context) (checked : theory.signature.check = true)
    (term : Term) : ∀ part ∈ operation.flatten term, operation.flatten part = [part] := by
  rcases operation.flatten_decompose term with unit | ⟨left, right, rfl⟩ | singleton
  · rw [unit, operation.flatten_unit]
    intro part impossible
    cases impossible
  · rw [operation.flatten_merge checked]
    intro part member
    rcases List.mem_append.mp member with first | second
    · exact operation.flatten_stable checked left part first
    · exact operation.flatten_stable checked right part second
  · intro part member
    rw [singleton] at member
    cases List.mem_singleton.mp member
    exact singleton
termination_by sizeOf term
decreasing_by
  all_goals
    subst_vars
    simp only [merge]
    simp_wf
    omega

theorem flatten_fold (operation : ACUOperation theory context) (checked : theory.signature.check = true)
    (parts : List Term) (stable : ∀ part ∈ parts, operation.flatten part = [part]) :
    operation.flatten (operation.fold parts) = parts := by
  induction parts with
  | nil => exact operation.flatten_unit
  | cons first rest ih =>
    rw [fold, operation.flatten_merge checked, stable first List.mem_cons_self,
      ih (fun part member => stable part (List.mem_cons_of_mem first member))]
    rfl

theorem flatten_substitute (operation : ACUOperation theory context) (checked : theory.signature.check = true)
    (assignment : Valuation) (term : Term) :
    operation.flatten (term.substitute assignment) =
      (operation.flatten term).flatMap (fun part => operation.flatten (part.substitute assignment)) := by
  rcases operation.flatten_decompose term with unit | ⟨left, right, rfl⟩ | singleton
  · rw [unit, Term.substitute_ground assignment operation.unit (operation.unit_ground checked), operation.flatten_unit]
    rfl
  · have substituted : (operation.merge left right).substitute assignment =
        operation.merge (left.substitute assignment) (right.substitute assignment) := by
      simp only [merge, Term.substitute, List.map_cons, List.map_nil]
    rw [substituted, operation.flatten_merge checked, operation.flatten_merge checked,
      List.flatMap_append, operation.flatten_substitute checked assignment left,
      operation.flatten_substitute checked assignment right]
  · rw [singleton, List.flatMap_singleton]
termination_by sizeOf term
decreasing_by
  all_goals
    subst_vars
    simp only [merge]
    simp_wf
    omega

#print axioms unit_ground
#print axioms flatten_stable
#print axioms flatten_substitute

end Mettapedia.Languages.Maude.ACUOperation
