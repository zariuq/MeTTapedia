import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ObservationModuloControls

/-!
# Pointwise and uniform equivalence as local and global sections

Over a set `U` of solutions of the knowledge, the renamings **matching** one configuration to another
(`matching`) fix the escaped identities, keep every label up to each solution in `U`, and carry the
present occurrences. Fewer solutions admit more renamings (`matching_restrict`), so this is a
presheaf on the sets of solutions. Its value at a set is one renaming for all of it, not a family.

* **Pointwise equivalence is non-empty stalks** (`pointwiseEquivalent_iff_stalks`): the same
  solutions, the escaped identities present together, and at every single solution some matching
  renaming.
* **Equivalence modulo the knowledge is a global section** (`moduloEquivalent_iff_global`): the same
  solutions and one renaming matching at all of them.
* **A principal answer is an initial solution**: every solution factors through it, so the stalk at
  it restricts into the global sections (`global_of_principal`). This is why the two equivalences
  coincide there (`Observation.moduloEquivalent_iff_pointwise`).
* **Without one, values need not have a common element** (`NonPrincipal.local_sections_do_not_glue`):
  at R55's two incomparable solutions, `straight` matches at the first and `crossed` at the second,
  and no renaming matches at both. Restriction here is inclusion and the value at the empty set is
  every carrying renaming, so `straight` and `crossed` are not compatible on the empty overlap: this
  is not a failure to glue compatible sections. The gap is the order of quantifiers: uniform
  equivalence is a non-empty limit (one renaming for all solutions), pointwise equivalence is a
  non-empty value at every solution. It is a local-versus-global gauge gap over the solutions, not
  contextuality in the sense of overlapping measurement contexts.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Observation

open AnnotatedRuns
open GuardFreeProcessOrders (SameUpTo)

universe uT uS uO

variable {T : Type uT} {S : Type uS} {O : Type uO}

section Sections

variable (A : SubstitutionAction T S) (label : O → T) (E : Finset O) (C D : Configuration T O)

/-- **The solutions of a configuration's knowledge.** -/
def solutions : Set S := {σ | A.Models σ C.equations}

/-- **The renamings matching `C` to `D` over a set `U` of solutions**: they fix `E`, keep every label
up to each solution in `U`, and carry the present occurrences of `C` to those of `D`. -/
def matching (U : Set S) : Set (O ≃ O) :=
  {π | (∀ o ∈ E, π o = o) ∧ (∀ σ ∈ U, ∀ o, A.Solves σ (label (π o), label o)) ∧
    C.present.map π.toEmbedding = D.present}

variable {A label E C D}

/-- **Restriction**: a renaming matching over a set of solutions matches over every subset. -/
theorem matching_restrict {U V : Set S} (sub : U ⊆ V) : matching A label E C D V ⊆ matching A label E C D U :=
  fun _ ⟨fixes, keeps, onto⟩ => ⟨fixes, fun σ inU => keeps σ (sub inU), onto⟩

theorem mem_matching_singleton {σ : S} {π : O ≃ O} :
    π ∈ matching A label E C D {σ} ↔
      RenamingUpTo (solutionSetoid A σ) label E π ∧ C.present.map π.toEmbedding = D.present := by
  constructor
  · rintro ⟨fixes, keeps, onto⟩
    exact ⟨⟨fun o => keeps σ rfl o, fixes⟩, onto⟩
  · rintro ⟨k, onto⟩
    exact ⟨k.fixes, fun τ same o => by rw [Set.mem_singleton_iff.mp same]; exact k.keeps o, onto⟩

/-- **Pointwise equivalence is non-empty stalks.** -/
theorem pointwiseEquivalent_iff_stalks :
    PointwiseEquivalent A label E C D ↔
      A.Equivalent C.equations D.equations ∧ (∀ o ∈ E, o ∈ C.present ↔ o ∈ D.present) ∧
        ∀ σ ∈ solutions A C, (matching A label E C D {σ}).Nonempty := by
  refine and_congr_right fun _ => and_congr_right fun _ => forall_congr' fun σ => imp_congr_right fun _ => ?_
  constructor
  · rintro ⟨π, k, onto⟩
    exact ⟨π, mem_matching_singleton.mpr ⟨k, onto⟩⟩
  · rintro ⟨π, member⟩
    exact ⟨π, mem_matching_singleton.mp member⟩

/-- **Equivalence modulo the knowledge is a global section.** -/
theorem moduloEquivalent_iff_global :
    ModuloEquivalent A label E C D ↔
      A.Equivalent C.equations D.equations ∧ (matching A label E C D (solutions A C)).Nonempty := by
  constructor
  · rintro ⟨π, k, same⟩
    exact ⟨same.1, π, k.fixes, fun σ solved o => k.keeps o σ solved, same.2⟩
  · rintro ⟨equivalent, π, fixes, keeps, onto⟩
    exact ⟨π, ⟨fun o σ solved => keeps σ solved o, fixes⟩, equivalent, onto⟩

/-- **A principal answer is an initial solution**: a renaming matching at it matches at every
solution, so its stalk restricts into the global sections. -/
theorem global_of_principal {answer : S} (principal : A.Principal C.equations answer)
    (stalk : (matching A label E C D {answer}).Nonempty) :
    (matching A label E C D (solutions A C)).Nonempty := by
  obtain ⟨π, member⟩ := stalk
  obtain ⟨k, onto⟩ := mem_matching_singleton.mp member
  have entailed := k.weaken (solution_le_entailedSetoid principal)
  exact ⟨π, k.fixes, fun σ solved o => entailed.keeps o σ solved, onto⟩

end Sections

namespace NonPrincipal

theorem solutions_left : solutions action left = {Choice.first, Choice.second} := by
  ext σ
  simp only [solutions, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  cases σ with
  | identity =>
      exact ⟨fun solved => absurd solved not_identity, fun same => by cases same <;> contradiction⟩
  | first => exact ⟨fun _ => Or.inl rfl, fun _ => first_solves⟩
  | second => exact ⟨fun _ => Or.inr rfl, fun _ => second_solves⟩

/-- **Values at each solution without a common element.** `straight` matches at the first solution
and `crossed` at the second; the two solutions cover the solution set, yet no renaming matches at
both, so the matching set over all solutions is empty. (`straight` and `crossed` are different
renamings, so they are not compatible sections; the point is the empty limit, not a gluing failure.) -/
theorem local_sections_do_not_glue :
    straight ∈ matching action label ∅ left right {Choice.first} ∧
      crossed ∈ matching action label ∅ left right {Choice.second} ∧
      solutions action left = {Choice.first} ∪ {Choice.second} ∧
      ({Choice.first} ∩ {Choice.second} : Set Choice) = ∅ ∧
      matching action label ∅ left right (solutions action left) = ∅ := by
  refine ⟨mem_matching_singleton.mpr ⟨keeps_of_rows straight_outside ?_, by decide⟩,
    mem_matching_singleton.mpr ⟨keeps_of_rows crossed_outside ?_, by decide⟩, ?_, ?_, ?_⟩
  · intro o member
    simp only [Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl | rfl | rfl <;> rfl
  · intro o member
    simp only [Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl | rfl | rfl <;> rfl
  · rw [solutions_left]
    rfl
  · ext σ
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false, not_and]
    rintro rfl
    exact fun same => absurd same (by decide)
  · refine Set.eq_empty_iff_forall_notMem.mpr fun π member => not_modulo ?_
    exact (moduloEquivalent_iff_global (E := ∅)).mpr ⟨fun _ => Iff.rfl, π, member⟩

end NonPrincipal

#print axioms matching_restrict
#print axioms pointwiseEquivalent_iff_stalks
#print axioms moduloEquivalent_iff_global
#print axioms global_of_principal
#print axioms NonPrincipal.solutions_left
#print axioms NonPrincipal.local_sections_do_not_glue

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Observation
