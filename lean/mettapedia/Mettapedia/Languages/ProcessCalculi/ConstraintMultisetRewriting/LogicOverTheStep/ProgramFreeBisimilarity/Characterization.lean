import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.ProgramFreeBisimilarity.Probes

/-!
# Bisimilarity of the program-free step is equivalence modulo the knowledge

For every substitution action and every labelling of occurrence identities, on configurations
whose knowledge is consistent:

* **The probe step** (guards and takes only): bisimilar exactly when equivalent modulo the
  knowledge, with no hypothesis at all (`probeBisimilar_iff`). One direction is the probes
  (`moduloEquivalent_of_probeBisimilar`); the other is the tree's counterpart argument, which needs
  no fresh identities because a probe makes nothing (`probeBisimilar_of_moduloEquivalent`).
* **The program-free step** (`Semantic.ruleOffers`): bisimilarity implies equivalence modulo the
  knowledge with no hypothesis (`moduloEquivalent_of_bisimilar`); with a fresh supply of identities
  for every label the two coincide (`ruleOffers_bisimilar_iff`), and so for every restriction of the
  step to rule forms that keeps the guards and the takes (`formOffers_bisimilar_iff`). With a fresh
  supply the probe step and the program-free step have the same bisimilarity
  (`probeBisimilar_iff_ruleBisimilar`): tells, reads, makes, absence and count checks and queries
  tell apart nothing more. Without one, a make can see that a term has run out of fresh identities
  (`ProgramFreeControls.freshSupply_needed`).
* **All configurations** (`ruleOffers_bisimilar_iff_or`): inconsistent configurations admit no
  firing, so they are all bisimilar to each other and to no consistent one; equivalence modulo the
  knowledge keeps their number of rows. No firing reaches them (`consistent_of_moves`).
* **Escaped identities**: bisimilarity sees no identity, so the right side is the relation with no
  escaped identity; any set of escaped identities gives a finer relation (`exists_moduloEquivalent_iff`).

## The raw step

The raw step also offers firings whose query regions read labels syntactically. Under rule labels
its moves are those of the program-free step (`moves_raw_iff`), so it has the same bisimilarity
(`rawBisimilar_iff`), and equivalence modulo the knowledge is contained in it as well
(`rawBisimilar_iff_moduloEquivalent`).

## What the congruence theorem says

`Semantic.ruleBisimilar_tensor` states that bisimilarity of the program-free step is preserved by
composing with a store disjoint from both sides. Its static form is already in the tree:
`Observation.ModuloEquivalent.tensor_disjoint`, equivalence modulo the knowledge preserved by a
disjoint store (a renaming supported on the two configurations fixes the store). With the
characterization the two theorems state one fact: the congruence follows from the static form
(`ruleBisimilar_tensor_of_static`), the static form on consistent composites follows from the
congruence (`moduloEquivalent_tensor_of_bisimilar`), and their conclusions coincide there
(`tensor_bisimilar_iff_moduloEquivalent`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.ProgramFreeBisimilarity

open AnnotatedRuns
open Semantic (ruleOffers rawOffers FreshSupply isSemantic_rename)
open Observation (ModuloEquivalent entailedSetoid moduloEquivalent_iff)

universe uT uS uO

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
  {A : SubstitutionAction T S} {label : O → T} {C D : Configuration T O}

/-! ## The probe step -/

/-- **Equivalence modulo the knowledge is a bisimulation of the probe step**, for every set of
escaped identities, with no fresh supply: a probe makes nothing, so each admitted probe has a
renamed counterpart. -/
theorem probeBisimilar_of_moduloEquivalent {E : Finset O} (h : ModuloEquivalent A label E C D) :
    Race.Bisimilar A label (probeOffers A) C D := by
  have counterpart : ∀ {X Y : Configuration T O}, ModuloEquivalent A label E X Y →
      ∀ (ρ : RuleInstance T) (X' : Configuration T O), Race.Moves A label (probeOffers A) X ρ X' →
        ∃ Y', Race.Moves A label (probeOffers A) Y ρ Y' ∧ ModuloEquivalent A label E X' Y' := by
    rintro X Y related ρ X' ⟨f, ⟨form, rfl, reads⟩, valid, rfl⟩
    have none : f.selection.made = [] := by
      have outputs := valid.firing.outputs
      rw [form.produce_nil] at outputs
      exact List.map_eq_nil_iff.mp outputs
    obtain ⟨π, valid', results⟩ := related.semantic_counterpart valid reads
      fun o member => absurd member (none ▸ List.not_mem_nil)
    exact ⟨_, ⟨f.rename π, ⟨form, rfl, isSemantic_rename π reads⟩, valid', rfl⟩, results⟩
  refine ⟨ModuloEquivalent A label E, ⟨?_, ?_, fun _ _ _ atom => atom.elim⟩, h⟩
  · intro X Y related ρ X' moved
    exact counterpart related ρ X' moved
  · intro X Y related ρ Y' moved
    obtain ⟨X', moved', related'⟩ := counterpart related.symm ρ Y' moved
    exact ⟨X', moved', related'.symm⟩

/-- **Bisimilar configurations of the probe step are equivalent modulo the knowledge**, for every
substitution action, when the first has consistent knowledge. -/
theorem moduloEquivalent_of_probeBisimilar (h : Race.Bisimilar A label (probeOffers A) C D)
    (consistent : A.Consistent C.equations) : ModuloEquivalent A label ∅ C D := by
  have same := equivalent_of_bisimilar h consistent
  have consistentD := (consistent_iff_of_bisimilar h).mp consistent
  have setoids : entailedSetoid A C.equations = entailedSetoid A D.equations :=
    Observation.entailedSetoid_congr same
  refine (moduloEquivalent_iff A label ∅ C D).mpr
    ⟨same, fun o member => absurd member (Finset.notMem_empty o), le_antisymm ?_ ?_⟩
  · exact bag_le_of_bisimilar h consistent _ (le_of_eq setoids.symm)
  · exact bag_le_of_bisimilar (bisimilar_symm h) consistentD _ le_rfl

/-- **On the probe step, bisimilarity is equivalence modulo the knowledge**: no hypothesis on the
action, on the labels or on the supply of identities. -/
theorem probeBisimilar_iff (consistent : A.Consistent C.equations) :
    Race.Bisimilar A label (probeOffers A) C D ↔ ∃ E, ModuloEquivalent A label E C D :=
  ⟨fun h => ⟨∅, moduloEquivalent_of_probeBisimilar h consistent⟩,
    fun ⟨_, h⟩ => probeBisimilar_of_moduloEquivalent h⟩

omit [DecidableEq O] in
/-- **The escaped identities that bisimilarity can afford are none**: equivalence relative to some
escaped identities is equivalence relative to none. -/
theorem exists_moduloEquivalent_iff :
    (∃ E, ModuloEquivalent A label E C D) ↔ ModuloEquivalent A label ∅ C D :=
  ⟨fun ⟨_, h⟩ => h.mono (Finset.empty_subset _), fun h => ⟨∅, h⟩⟩

/-! ## The program-free step -/

/-- **Bisimilar configurations of the program-free step are equivalent modulo the knowledge**, for
every substitution action, when the first has consistent knowledge. No fresh supply is needed. -/
theorem moduloEquivalent_of_bisimilar (h : Race.Bisimilar A label (ruleOffers A) C D)
    (consistent : A.Consistent C.equations) : ModuloEquivalent A label ∅ C D :=
  moduloEquivalent_of_probeBisimilar (bisimilar_formOffers h) consistent

/-- **Bisimilarity of the program-free step is equivalence modulo the knowledge**, for every
substitution action, on consistent configurations, given a fresh supply of identities. -/
theorem ruleOffers_bisimilar_iff (supply : FreshSupply label) (consistent : A.Consistent C.equations) :
    Race.Bisimilar A label (ruleOffers A) C D ↔ ∃ E, ModuloEquivalent A label E C D :=
  ⟨fun h => ⟨∅, moduloEquivalent_of_bisimilar h consistent⟩,
    fun ⟨_, h⟩ => h.semantic_bisimilar supply⟩

/-- **Every restriction of the step that keeps the guards and the takes** has the same bisimilarity,
given a fresh supply. -/
theorem formOffers_bisimilar_iff (supply : FreshSupply label) {forms : RuleInstance T → Prop}
    (probes : ∀ ρ, ProbeForm ρ → forms ρ) (consistent : A.Consistent C.equations) :
    Race.Bisimilar A label (formOffers A forms) C D ↔ ∃ E, ModuloEquivalent A label E C D :=
  ⟨fun h => ⟨∅, moduloEquivalent_of_probeBisimilar (bisimilar_formOffers_mono probes h) consistent⟩,
    fun ⟨_, h⟩ => bisimilar_formOffers (h.semantic_bisimilar supply)⟩

/-- **All configurations**: bisimilar exactly when equivalent modulo the knowledge, or both
inconsistent. -/
theorem ruleOffers_bisimilar_iff_or (supply : FreshSupply label) (C D : Configuration T O) :
    Race.Bisimilar A label (ruleOffers A) C D ↔
      (∃ E, ModuloEquivalent A label E C D) ∨
        (¬ A.Consistent C.equations ∧ ¬ A.Consistent D.equations) := by
  constructor
  · intro h
    by_cases consistent : A.Consistent C.equations
    · exact Or.inl ⟨∅, moduloEquivalent_of_bisimilar h consistent⟩
    · exact Or.inr ⟨consistent, fun consistentD =>
        consistent ((consistent_iff_of_bisimilar (bisimilar_formOffers h)).mpr consistentD)⟩
  · rintro (⟨E, h⟩ | ⟨inconsistentC, inconsistentD⟩)
    · exact h.semantic_bisimilar supply
    · exact Race.bisimilar_of_halted (fun _ _ => Semantic.no_moves_of_inconsistent inconsistentC)
        (fun _ _ => Semantic.no_moves_of_inconsistent inconsistentD)

/-- **The probe step and the program-free step have the same bisimilarity**, given a fresh supply:
the other rule forms tell apart nothing more. -/
theorem probeBisimilar_iff_ruleBisimilar (supply : FreshSupply label) (C D : Configuration T O) :
    Race.Bisimilar A label (probeOffers A) C D ↔ Race.Bisimilar A label (ruleOffers A) C D := by
  constructor
  · intro h
    by_cases consistent : A.Consistent C.equations
    · exact (moduloEquivalent_of_probeBisimilar h consistent).semantic_bisimilar supply
    · have inconsistentD : ¬ A.Consistent D.equations := fun consistentD =>
        consistent ((consistent_iff_of_bisimilar h).mpr consistentD)
      exact Race.bisimilar_of_halted (fun _ _ => Semantic.no_moves_of_inconsistent consistent)
        (fun _ _ => Semantic.no_moves_of_inconsistent inconsistentD)
  · exact bisimilar_formOffers

/-! ## The raw step -/

/-- **The raw step has the bisimilarity of the program-free step.** -/
theorem rawBisimilar_iff :
    Race.Bisimilar A label (rawOffers (S := S)) C D ↔ Race.Bisimilar A label (ruleOffers A) C D :=
  bisimilar_congr_moves fun _ _ _ => moves_raw_iff

/-- **Equivalence modulo the knowledge is bisimilarity of the raw step too**, given a fresh supply. -/
theorem rawBisimilar_iff_moduloEquivalent (supply : FreshSupply label)
    (consistent : A.Consistent C.equations) :
    Race.Bisimilar A label (rawOffers (S := S)) C D ↔ ∃ E, ModuloEquivalent A label E C D :=
  rawBisimilar_iff.trans (ruleOffers_bisimilar_iff supply consistent)

/-! ## What the congruence theorem says -/

/-- **The congruence theorem from the static side**: with a fresh supply, the conclusion of
`Semantic.ruleBisimilar_tensor` follows from the characterization and the tree's static congruence
`Observation.ModuloEquivalent.tensor_disjoint` (through `ModuloEquivalent.tensor_bisimilar`). -/
theorem ruleBisimilar_tensor_of_static (supply : FreshSupply label)
    (h : Race.Bisimilar A label (ruleOffers A) C D) (F : Configuration T O)
    (apartC : Disjoint C.present F.present) (apartD : Disjoint D.present F.present) :
    Race.Bisimilar A label (ruleOffers A) (AnnotatedRuns.tensor C F) (AnnotatedRuns.tensor D F) := by
  rcases (ruleOffers_bisimilar_iff_or supply C D).mp h with ⟨E, equivalent⟩ |
      ⟨inconsistentC, inconsistentD⟩
  · exact equivalent.tensor_bisimilar supply F apartC apartD
  · have stuck : ∀ {X : Configuration T O}, ¬ A.Consistent X.equations →
        ¬ A.Consistent (AnnotatedRuns.tensor X F).equations := by
      rintro X inconsistent ⟨σ, solved⟩
      exact inconsistent ⟨σ, ((A.models_append _ _ _).mp solved).1⟩
    exact Race.bisimilar_of_halted
      (fun _ _ => Semantic.no_moves_of_inconsistent (stuck inconsistentC))
      (fun _ _ => Semantic.no_moves_of_inconsistent (stuck inconsistentD))

/-- **Composites of bisimilar configurations are equivalent modulo the knowledge**: the content of
`Semantic.ruleBisimilar_tensor` on consistent composites, read on the static side. -/
theorem moduloEquivalent_tensor_of_bisimilar (h : Race.Bisimilar A label (ruleOffers A) C D)
    (F : Configuration T O) (apartC : Disjoint C.present F.present)
    (apartD : Disjoint D.present F.present)
    (consistent : A.Consistent (AnnotatedRuns.tensor C F).equations) :
    ModuloEquivalent A label ∅ (AnnotatedRuns.tensor C F) (AnnotatedRuns.tensor D F) :=
  moduloEquivalent_of_bisimilar (Semantic.ruleBisimilar_tensor h F apartC apartD) consistent

/-- **The two congruence theorems state one fact**: on a consistent composite and with a fresh
supply, the conclusion of `Semantic.ruleBisimilar_tensor` is the conclusion of
`Observation.ModuloEquivalent.tensor_disjoint` with no escaped identity. -/
theorem tensor_bisimilar_iff_moduloEquivalent (supply : FreshSupply label) (F : Configuration T O)
    (consistent : A.Consistent (AnnotatedRuns.tensor C F).equations) :
    Race.Bisimilar A label (ruleOffers A) (AnnotatedRuns.tensor C F) (AnnotatedRuns.tensor D F) ↔
      ModuloEquivalent A label ∅ (AnnotatedRuns.tensor C F) (AnnotatedRuns.tensor D F) :=
  (ruleOffers_bisimilar_iff supply consistent).trans exists_moduloEquivalent_iff

#print axioms probeBisimilar_of_moduloEquivalent
#print axioms moduloEquivalent_of_probeBisimilar
#print axioms probeBisimilar_iff
#print axioms exists_moduloEquivalent_iff
#print axioms moduloEquivalent_of_bisimilar
#print axioms ruleOffers_bisimilar_iff
#print axioms formOffers_bisimilar_iff
#print axioms ruleOffers_bisimilar_iff_or
#print axioms probeBisimilar_iff_ruleBisimilar
#print axioms rawBisimilar_iff
#print axioms rawBisimilar_iff_moduloEquivalent
#print axioms ruleBisimilar_tensor_of_static
#print axioms moduloEquivalent_tensor_of_bisimilar
#print axioms tensor_bisimilar_iff_moduloEquivalent

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.ProgramFreeBisimilarity
