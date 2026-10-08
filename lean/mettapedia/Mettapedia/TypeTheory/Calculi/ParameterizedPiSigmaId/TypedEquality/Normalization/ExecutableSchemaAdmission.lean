import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ExecutableSchemaSelection
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.ConstructorSystemDevelopment

/-!
# Executable equation admission and root completeness

Supported left sides and right-variable coverage are properties of authored
entries. Under these precise conditions the source-ordered root procedure
finds a contraction exactly when the independent instance relation has one.
The selected target need not be every target of that relation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality.Normalization.ExecutableSchemaSelection

open AlgebraicSchema ExecutableSchemaMatching

variable {Head : Type} [DecidableEq Head]

def GoodEntry (entry : Entry Head) : Prop :=
  supported entry.2.1 = true ∧
    ∀ index, 0 < variableMultiplicity index entry.2.2 →
      0 < variableMultiplicity index entry.2.1

def Admitted (table : SchemaTable Head) : Prop :=
  ∀ entry ∈ table, GoodEntry entry

omit [DecidableEq Head] in
theorem admitted_cons {entry : Entry Head} {table : SchemaTable Head} :
    Admitted (entry :: table) ↔ GoodEntry entry ∧ Admitted table := by
  constructor
  · intro admitted
    exact ⟨admitted entry List.mem_cons_self,
      fun member listed => admitted member (List.mem_cons_of_mem _ listed)⟩
  · rintro ⟨good, admitted⟩ member listed
    rcases List.mem_cons.mp listed with rfl | listed
    · exact good
    · exact admitted member listed

theorem Outcome.target?_prepend {table : SchemaTable Head} {ambient : Nat}
    {source : Tm Head ambient} (entry : Entry Head) (outcome : Outcome table source) :
    (outcome.prepend entry).target? = outcome.target? := by
  cases outcome <;> rfl

/-- Reconstructed slots agree with an arbitrary instance on every right-side
occurrence, including occurrences under binders. -/
theorem target_eq_instance {slots ambient : Nat} {left right : Tm Head slots}
    {assignment : Assignment Head slots ambient} {substitution : Sub Head slots ambient}
    (covered : ∀ index, 0 < variableMultiplicity index right →
      0 < variableMultiplicity index left)
    (matched : run left (Presentation.subst substitution left) (fun _ => none) = some assignment)
    (realized : Realizes assignment substitution) :
    Presentation.subst (materialize assignment) right = Presentation.subst substitution right := by
  apply ConstructorSystem.subst_congr_occurring
  intro index occurs
  obtain ⟨value, bound⟩ := run_assigned left matched index (covered index occurs)
  exact (materialize_realizes assignment index value bound).trans
    (realized index value bound).symm

theorem first_has_target_iff_instances {table : SchemaTable Head} (admitted : Admitted table)
    {ambient : Nat} (source : Tm Head ambient) :
    (first table source).target?.isSome = true ↔
      ∃ entry ∈ table, ∃ substitution : Sub Head entry.1 ambient,
        Presentation.subst substitution entry.2.1 = source := by
  induction table with
  | nil => simp only [first, Outcome.target?, Option.isSome_none, Bool.false_eq_true,
      List.not_mem_nil, exists_false, false_and]
  | cons entry table ih =>
      obtain ⟨good, tailAdmitted⟩ := admitted_cons.mp admitted
      simp only [first]
      split
      next matched =>
          have noInstance : ¬ ∃ substitution : Sub Head entry.1 ambient,
              Presentation.subst substitution entry.2.1 = source := by
            rintro ⟨substitution, same⟩
            obtain ⟨updated, computed, _⟩ := run_complete entry.2.1 good.1 substitution
              (assignment := fun _ => none) (fun _ _ impossible => by cases impossible)
            rw [same, matched] at computed
            cases computed
          rw [Outcome.target?_prepend, ih tailAdmitted]
          constructor
          · rintro ⟨member, listed, substitution, same⟩
            exact ⟨member, List.mem_cons_of_mem _ listed, substitution, same⟩
          · rintro ⟨member, listed, substitution, same⟩
            rcases List.mem_cons.mp listed with rfl | listed
            · exact False.elim (noInstance ⟨substitution, same⟩)
            · exact ⟨member, listed, substitution, same⟩
      next assignment matched =>
          have assigned := rightAssigned_of_covered good.2 matched
          have instanceOf := (run_sound entry.2.1 matched).2 _ (materialize_realizes assignment)
          simp only [dif_pos assigned, Outcome.target?, Option.isSome_some,
            true_iff]
          exact ⟨entry, List.mem_cons_self, materialize assignment, instanceOf⟩

/-- The independently authored instance relation has a root step exactly when
the admitted executable table finds a target. This is existence reflection,
not reflection of every target under a priority policy. -/
theorem first_has_target_iff_step {table : SchemaTable Head} (admitted : Admitted table)
    {ambient : Nat} (source : Tm Head ambient) :
    (first table source).target?.isSome = true ↔
      ∃ target, (SchemaFamily.computation table.family).step source target := by
  rw [first_has_target_iff_instances admitted]
  constructor
  · rintro ⟨entry, listed, substitution, same⟩
    refine ⟨Presentation.subst substitution entry.2.2, ?_⟩
    rw [← same]
    exact SchemaTable.step_of_mem table listed substitution
  · rintro ⟨target, step⟩
    cases step with
    | instantiate listed substitution => exact ⟨_, listed, substitution, rfl⟩

end TypedEquality.Normalization.ExecutableSchemaSelection
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
