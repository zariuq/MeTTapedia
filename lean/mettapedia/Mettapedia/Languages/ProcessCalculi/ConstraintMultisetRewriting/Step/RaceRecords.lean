import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RaceCommit
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ObservationModulo

/-!
# Records and histories

The escape that records choices (`AnnotatedRuns.choiceEscape`) records, for each firing, the sets its
predicate queries sighted and the occurrences it took, as held references. The causal past of a
history move (`RaceSteps.past`) is read off which earlier firings are not independent of the new one;
on pure firings this is provenance: the new firing takes what an earlier one made
(`staticIndependent_iff_provenance`).

* **Where records carry the history.** A record holds what each firing took, in order, so it carries
  the take half of provenance; for firings without predicate queries it is exactly the references of
  the taken occurrences (`RaceCommit.choiceEscape_records`). Equivalence relative to the record and the escape
  isomorphisms of `Observer*` act on this.
* **Where they do not** (`records_blind_to_causality`): the record does not hold what a firing made.
  Two runs with the same record can have different causal orders: taking `a` and then `b`, where `b`
  was present, is independent; taking `a` while making `b`, and then taking `b`, is causal. Their
  records are equal, their histories are not.
* **What closes the gap** (`provenance_record_determines_past`): for pure firings, recording the made
  occurrences as well determines direct dependence, so a record of takes and makes carries the causal
  order that history-preserving bisimulation compares.

## Identities

Bisimilarity labelled by rules does not see occurrence identities: a label-keeping renaming relates
bisimilar configurations (`bisimilar_rename`). Equivalence modulo the knowledge relative to escaped
identities (`Observation.ModuloEquivalent`) does see them, so it is strictly finer
(`moduloEquivalent_strictly_finer`): holding `true` and holding `false`, with `true` escaped.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race

open AnnotatedRuns (Firing StaticIndependent)
open Observation (Record)

universe uT uS uO

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

/-- **Records of takes and makes determine direct dependence on pure firings.** Two pairs of pure
firings with the same taken and made occurrences, taking different occurrences and making different
identities, are independent together. -/
theorem provenance_record_determines_past [Nonempty S] (label : O → T) {e f e' f' : Firing T S O}
    (pe : Pure e) (pf : Pure f) (pe' : Pure e') (pf' : Pure f')
    (takes : Disjoint e.selection.taken.toFinset f.selection.taken.toFinset)
    (makes : Disjoint e.selection.made.toFinset f.selection.made.toFinset)
    (sameTaken : e.selection.taken = e'.selection.taken ∧ f.selection.taken = f'.selection.taken)
    (sameMade : e.selection.made = e'.selection.made ∧ f.selection.made = f'.selection.made) :
    StaticIndependent label e f ↔ StaticIndependent label e' f' := by
  rw [staticIndependent_iff_provenance label pe pf takes makes,
    staticIndependent_iff_provenance label pe' pf'
      (by rw [← sameTaken.1, ← sameTaken.2]; exact takes)
      (by rw [← sameMade.1, ← sameMade.2]; exact makes),
    ← sameTaken.1, ← sameTaken.2, ← sameMade.1, ← sameMade.2]

namespace RecordControls

/-- Occurrences `a` and `b`. -/
inductive Site
  | a | b
  deriving DecidableEq

variable (τ : T)

def label : Site → T := fun _ => τ

/-- The ground firing that takes `taken` and makes `made`. -/
def firing (taken made : List Site) : Firing T S Site :=
  ⟨⟨taken.map (label τ), [], [], [], made.map (label τ)⟩, [], ⟨taken, [], made⟩⟩

/-- Take `a`. -/
def takeA : Firing T S Site := firing τ [.a] []
/-- Take `a` and make `b`. -/
def takeAmakeB : Firing T S Site := firing τ [.a] [.b]
/-- Take `b`. -/
def takeB : Firing T S Site := firing τ [.b] []

theorem pure_firing (taken made : List Site) : Pure (firing (S := S) τ taken made) := ⟨rfl, rfl, rfl⟩

/-- **Records do not carry causality.** The runs `takeA, takeB` and `takeAmakeB, takeB` leave the
same records, and the second firing has an empty causal past in the first run and the first firing
in its causal past in the second. -/
theorem records_blind_to_causality (A : SubstitutionAction T S) {C D : Configuration T Site} :
    ((AnnotatedRuns.choiceEscape A (label τ)).records (s := C) (takeA (S := S) τ) ++
        (AnnotatedRuns.choiceEscape A (label τ)).records (s := C) (takeB (S := S) τ) =
      (AnnotatedRuns.choiceEscape A (label τ)).records (s := D) (takeAmakeB (S := S) τ) ++
        (AnnotatedRuns.choiceEscape A (label τ)).records (s := D) (takeB (S := S) τ)) ∧
      past (label τ) [(takeA (S := S) τ, (∅ : Finset ℕ))] (takeB τ) = ∅ ∧
      0 ∈ past (label τ) [(takeAmakeB (S := S) τ, (∅ : Finset ℕ))] (takeB τ) := by
  have : Nonempty S := ⟨A.identity⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [choiceEscape_records A (label τ) rfl, choiceEscape_records A (label τ) rfl, choiceEscape_records A (label τ) rfl,
      choiceEscape_records A (label τ) rfl]
    rfl
  · have independent : StaticIndependent (label τ) (takeA (S := S) τ) (takeB τ) :=
      (staticIndependent_iff_provenance (label τ) (e := takeA τ) (f := takeB τ) (pure_firing τ _ _)
        (pure_firing τ _ _) (of_decide_eq_true rfl) (of_decide_eq_true rfl)).mpr
        ⟨of_decide_eq_true rfl, of_decide_eq_true rfl⟩
    have wf : WF [(takeA (S := S) τ, (∅ : Finset ℕ))] := wf_concat (h := []) wf_nil (Finset.empty_subset _)
    have fresh : ∀ i e, 0 ≤ i → [(takeA (S := S) τ, (∅ : Finset ℕ))][i]? = some e →
        StaticIndependent (label τ) e.1 (takeB τ) := by
      intro i e _ get
      rcases getElem?_concat_eq_some (h := []) get with ⟨lt, _⟩ | ⟨_, rfl⟩
      · simp at lt
      · exact independent
    have sub := past_subset_of_independent wf fresh
    rw [Finset.range_zero] at sub
    exact Finset.subset_empty.mp sub
  · have dependent : ¬ StaticIndependent (label τ) (takeAmakeB (S := S) τ) (takeB τ) := fun h =>
      absurd ((staticIndependent_iff_provenance (label τ) (e := takeAmakeB τ) (f := takeB τ)
        (pure_firing τ _ _) (pure_firing τ _ _) (of_decide_eq_true rfl)
        (of_decide_eq_true rfl)).mp h).1 (of_decide_eq_false rfl)
    exact directPast_subset_past _ _ (mem_directPast.mpr ⟨by simp, _, rfl, dependent⟩)

end RecordControls

/-! ## Rule labels do not see identities; the observer's equivalence does -/

section Identities

open AnnotatedRuns (renameConfiguration)

omit [DecidableEq O] in
theorem rename_symm_rename (π : O ≃ O) (C : Configuration T O) :
    renameConfiguration π.symm (renameConfiguration π C) = C := by
  obtain ⟨equations, present⟩ := C
  show (⟨equations, (present.map π.toEmbedding).map π.symm.toEmbedding⟩ : Configuration T O) =
    ⟨equations, present⟩
  congr 1
  ext o
  simp [Finset.mem_map_equiv]

/-- **Bisimilarity labelled by rules is blind to identities**: for the program that offers every
firing under its rule, a label-keeping renaming of occurrences relates bisimilar configurations. -/
theorem bisimilar_rename (A : SubstitutionAction T S) (label : O → T) {π : O ≃ O}
    (keeps : ∀ o, label (π o) = label o) (C : Configuration T O) :
    Bisimilar A label (fun r (f : Firing T S O) => f.rule = r) C (renameConfiguration π C) := by
  have keepsSymm : ∀ o, label (π.symm o) = label o := fun o => by
    have := keeps (π.symm o)
    rw [Equiv.apply_symm_apply] at this
    exact this.symm
  refine ⟨fun X Y => Y = renameConfiguration π X, ⟨?_, ?_, ?_⟩, rfl⟩
  · rintro X Y rfl r X' ⟨f, rfl, valid, rfl⟩
    exact ⟨_, ⟨f.rename π, rfl, (AnnotatedRuns.Firing.valid_rename A keeps f X).mpr valid, rfl⟩,
      AnnotatedRuns.Firing.result_rename keeps f X⟩
  · rintro X Y rfl r Y' ⟨g, rfl, valid, rfl⟩
    have back : (g.rename π.symm).Valid A label X := by
      have := (AnnotatedRuns.Firing.valid_rename A keepsSymm g (renameConfiguration π X)).mpr valid
      exact (congrArg (fun D => (g.rename π.symm).Valid A label D) (rename_symm_rename π X)).mp this
    refine ⟨_, ⟨g.rename π.symm, rfl, back, rfl⟩, ?_⟩
    have h1 : (g.rename π.symm).result label X =
        renameConfiguration π.symm (g.result label (renameConfiguration π X)) :=
      (congrArg (fun D => (g.rename π.symm).result label D) (rename_symm_rename π X)).symm.trans
        (AnnotatedRuns.Firing.result_rename keepsSymm g (renameConfiguration π X))
    have h2 : renameConfiguration π (renameConfiguration π.symm (g.result label (renameConfiguration π X))) =
        g.result label (renameConfiguration π X) :=
      rename_symm_rename π.symm (g.result label (renameConfiguration π X))
    exact h2.symm.trans (congrArg (renameConfiguration π) h1.symm)
  · intro _ _ _ atom
    exact atom.elim

/-- **Equivalence relative to the record is strictly finer than bisimilarity labelled by rules.**
With the identity `true` escaped, the configurations holding `true` and holding `false`, under one
label, are bisimilar for the program of all firings labelled by rules, and not equivalent modulo
the knowledge relative to `{true}`. -/
theorem moduloEquivalent_strictly_finer (A : SubstitutionAction T S) (τ : T) :
    Bisimilar A (fun _ : Bool => τ) (fun r (f : Firing T S Bool) => f.rule = r)
        ⟨[], {true}⟩ ⟨[], {false}⟩ ∧
      ¬ Observation.ModuloEquivalent A (fun _ : Bool => τ) {true} ⟨[], {true}⟩ ⟨[], {false}⟩ := by
  refine ⟨?_, ?_⟩
  · have := bisimilar_rename A (fun _ : Bool => τ) (π := Equiv.swap true false) (fun _ => rfl)
      (⟨[], {true}⟩ : Configuration T Bool)
    rw [show (⟨[], {false}⟩ : Configuration T Bool) =
        renameConfiguration (Equiv.swap true false) ⟨[], {true}⟩ from by simp [renameConfiguration]]
    exact this
  · rintro ⟨π, renamed, same⟩
    have fixed : π true = true := renamed.fixes true (Finset.mem_singleton_self _)
    have present := same.2
    change ({true} : Finset Bool).map π.toEmbedding = {false} at present
    rw [Finset.map_singleton, Equiv.coe_toEmbedding, fixed] at present
    exact absurd present (by decide)

end Identities

#print axioms provenance_record_determines_past
#print axioms RecordControls.records_blind_to_causality
#print axioms bisimilar_rename
#print axioms moduloEquivalent_strictly_finer

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race
