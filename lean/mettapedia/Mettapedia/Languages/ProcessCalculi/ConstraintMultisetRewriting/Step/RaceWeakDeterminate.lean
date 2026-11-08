import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RaceWeak

/-!
# The weak determinate fragment: internal firings are inert

The race-free, independent fragment of `RaceDeterminate` (`Fragment`: ground firings, one label per
firing, distinct offered firings statically independent), with some of its labels marked internal.

* **It is τ-confluent** (`Fragment.confluent`), in the sense of `Weak.Confluent`, on configurations
  with reflexive knowledge. An internal firing and any other admitted firing are either the same
  firing, and then the other label is internal too, or they commute: each stays admitted after the
  other, and the two composite results have the same occurrences and reflexive knowledge, hence are
  bisimilar (`bisimilar_of_reflexive`).
* **Its internal firings are inert** (`Fragment.inert`): an internal firing relates weakly
  bisimilar configurations. This is Groote and Sellink's confluence theorem read in the step.
* **It is weakly determinate** (`Fragment.weaklyDeterminate`): weak successors under one label are
  weakly bisimilar. Strong determinacy (`Fragment.determinate`) passes to weak determinacy through
  τ-confluence (`Weak.weaklyDeterminate`).
* **On it, weak bisimilarity is weak trace equivalence**
  (`Fragment.weakBisimilar_iff_weakTraceEquivalent`): Milner's weak determinacy theorem.

The controls are in `RaceWeakControls`: a program of the fragment whose internal firing relates
weakly bisimilar configurations that are not bisimilar (`Inert.inert_control`), and the private-token
race pair, which leaves the fragment because its internal firings race (`Private.not_fragment`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race

open AnnotatedRuns (Firing StaticIndependent)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)

universe uT uS uO uL

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O] {L : Type uL}

instance isEmpty_system_atom (A : SubstitutionAction T S) (label : O → T)
    (offers : L → Firing T S O → Prop) : IsEmpty (system A label offers).Atom :=
  inferInstanceAs (IsEmpty PEmpty)

variable {A : SubstitutionAction T S} {label : O → T} {offers : L → Firing T S O → Prop}

omit [DecidableEq O] in
/-- A reflexive store is solved by every substitution. -/
theorem models_of_reflexive {store : EquationStore T} (refl : Reflexive store) (σ : S) :
    A.Models σ store := fun e member => by
  show A.E (A.apply σ e.1) (A.apply σ e.2)
  rw [refl e member]
  exact A.equivalence.refl _

/-- **Configurations with reflexive knowledge and the same occurrences are bisimilar.** -/
theorem bisimilar_of_reflexive {C D : Configuration T O} (reflC : Reflexive C.equations)
    (reflD : Reflexive D.equations) (present : C.present = D.present) :
    Bisimilar A label offers C D :=
  bisimilar_of_sameUpTo A label offers ⟨fun σ => ⟨fun _ => models_of_reflexive reflD σ,
    fun _ => models_of_reflexive reflC σ⟩, present⟩

variable (internal : L → Prop)

/-- **The fragment is τ-confluent** on configurations with reflexive knowledge. -/
theorem Fragment.confluent (fragment : Fragment label offers) :
    Weak.Confluent (system A label offers) internal (fun C => Reflexive C.equations) where
  equiv_closed := fun _ _ good same => (same : _ = _) ▸ good
  closed := fun C D ℓ refl moved => by
    obtain ⟨f, offered, _, rfl⟩ := (fragment.moves_iff refl).mp moved
    exact (fragment.ground _ _ offered).reflexive_result refl
  observes := fun _ _ _ _ atom => atom.elim
  diamond := by
    intro x x₁ x₂ τ ℓ refl inner m₁ m₂
    obtain ⟨f₁, o₁, e₁, rfl⟩ := (fragment.moves_iff refl).mp m₁
    obtain ⟨f₂, o₂, e₂, rfl⟩ := (fragment.moves_iff refl).mp m₂
    by_cases same : f₁ = f₂
    · subst same
      obtain rfl := fragment.oneLabel τ ℓ f₁ o₁ o₂
      exact .inl ⟨inner, (system A label offers).bisimilar_refl _⟩
    · have r₁ := (fragment.ground _ _ o₁).reflexive_result (C := x) refl
      have r₂ := (fragment.ground _ _ o₂).reflexive_result (C := x) refl
      have t₂₁ := fragment.trace A.identity o₂ o₁ (Ne.symm same)
      have t₁₂ := fragment.trace A.identity o₁ o₂ same
      have after₁ : Enabled label (fire x.present (f₁.selection.commit (T := T)))
          (f₂.selection.commit (T := T)) :=
        (MeTTaCalculus.OccurrenceCommits.enabled_fire_iff e₂ e₁).mpr
          ⟨fun clash => t₂₁.1.1 clash, t₂₁.1.2.2⟩
      have after₂ : Enabled label (fire x.present (f₂.selection.commit (T := T)))
          (f₁.selection.commit (T := T)) :=
        (MeTTaCalculus.OccurrenceCommits.enabled_fire_iff e₁ e₂).mpr
          ⟨fun clash => t₁₂.1.1 clash, t₁₂.1.2.2⟩
      refine .inr ⟨f₂.result label (f₁.result label x), f₁.result label (f₂.result label x),
        (fragment.moves_iff r₁).mpr ⟨f₂, o₂, after₁, rfl⟩,
        ⟨τ, inner, (fragment.moves_iff r₂).mpr ⟨f₁, o₁, after₂, rfl⟩⟩, ?_⟩
      exact bisimilar_of_reflexive ((fragment.ground _ _ o₂).reflexive_result r₁)
        ((fragment.ground _ _ o₁).reflexive_result r₂) (MeTTaCalculus.OccurrenceCommits.fire_comm e₁ e₂)

variable {internal}

/-- **Internal firings of the fragment are inert**: an internal firing relates weakly bisimilar
configurations. -/
theorem Fragment.inert (fragment : Fragment label offers) {C D : Configuration T O}
    (refl : Reflexive C.equations) {τ : L} (inner : internal τ) (moved : Moves A label offers C τ D) :
    WeakBisimilar A label offers internal C D :=
  Weak.inert (fragment.confluent internal) refl ⟨τ, inner, moved⟩

/-- **The fragment is weakly determinate**: weak successors under one label are weakly bisimilar. -/
theorem Fragment.weaklyDeterminate (fragment : Fragment label offers) :
    Weak.Determinate (Weak.weak (system A label offers) internal) (fun C => Reflexive C.equations) :=
  Weak.weaklyDeterminate (fragment.confluent internal) fragment.determinate

/-- **On the fragment, weak bisimilarity is weak trace equivalence.** -/
theorem Fragment.weakBisimilar_iff_weakTraceEquivalent (fragment : Fragment label offers)
    {C D : Configuration T O} (reflC : Reflexive C.equations) (reflD : Reflexive D.equations) :
    WeakBisimilar A label offers internal C D ↔ WeakTraceEquivalent A label offers internal C D :=
  Weak.confluent_bisimilar_iff_traceEquivalent (fragment.confluent internal) fragment.determinate
    reflC reflD

#print axioms models_of_reflexive
#print axioms bisimilar_of_reflexive
#print axioms Fragment.confluent
#print axioms Fragment.inert
#print axioms Fragment.weaklyDeterminate
#print axioms Fragment.weakBisimilar_iff_weakTraceEquivalent

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race
