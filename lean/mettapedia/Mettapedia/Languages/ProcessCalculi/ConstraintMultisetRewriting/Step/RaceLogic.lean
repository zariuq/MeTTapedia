import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RaceSteps
import Mathlib.Data.Set.Finite.List

/-!
# Step and history logics: image-finiteness and Hennessy–Milner

## Image-finiteness per label

* **Steps** (`stepSystem_imageFiniteModulo`): when each label offers finitely many firings, each step
  label has finitely many successors. A step labelled by the multiset `M` fires a word of exactly
  `card M` firings, each offered under a label of `M`, so its successors are the ends of finitely many
  words. This needs no hypothesis on what the firings write: the multiset label already bounds the
  word.
* **Histories** (`histSystem_imageFiniteModulo`): a history move fires one offered firing, so each
  history label has finitely many successors.

## Hennessy–Milner

From image-finiteness, by the tree's adequacy theorem
`HennessyMilner.System.logicallyEquivalent_iff_bisimilar`:

* **step bisimilarity is agreement on every formula of the step logic**, whose modalities are
  labelled by multisets of labels (`stepBisimilar_iff_sat`);
* **history-preserving bisimilarity is agreement on every formula of the history logic**, whose
  modalities are labelled by a label and a causal past, at the empty histories
  (`hpBisimilar_iff_sat`).

## Finite branching (`stepMoves_finite`)

Per-label image-finiteness lets infinitely many step labels be enabled at once. A firing that writes
nothing (takes nothing and makes nothing) is statically independent of itself, so it can repeat
without bound in one step: one configuration then has a step under every multiset `{ℓ, …, ℓ}`
(`RaceLogicControls`). When every offered firing of a finite alphabet takes or makes something, no
firing is independent of itself (`AnnotatedRuns.independent_self_iff`), the firings of a step are
distinct, and the steps at a configuration are finitely many.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race

open AnnotatedRuns (Firing follow StaticIndependent)
open Mettapedia.GSLT.HennessyMilner (Formula System)

universe uT uS uO uL

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O] {L : Type uL}

/-- Lists of bounded length over a finite set are finitely many. -/
theorem finite_words {α : Type*} {pool : Set α} (finite : pool.Finite) (n : ℕ) :
    {w : List α | w.length ≤ n ∧ ∀ x ∈ w, x ∈ pool}.Finite := by
  have : Finite pool := finite.to_subtype
  refine ((List.finite_length_le pool n).image (List.map Subtype.val)).subset ?_
  rintro w ⟨length, members⟩
  refine ⟨w.attach.map fun x => (⟨x.1, members x.1 x.2⟩ : pool), by simp [length], ?_⟩
  rw [List.map_map]
  exact List.attach_map_subtype_val w

variable (A : SubstitutionAction T S) (label : O → T) (offers : L → Firing T S O → Prop)

/-- Satisfaction in the step logic: modalities labelled by multisets of labels. -/
def StepSat (φ : Formula PEmpty.{1} (Multiset L)) (C : Configuration T O) : Prop :=
  (stepSystem A label offers).sat φ C

/-- Satisfaction in the history logic: modalities labelled by a label and a causal past. -/
def HistSat (φ : Formula PEmpty.{1} (L × Finset ℕ)) (x : Configuration T O × History T S O) : Prop :=
  (histSystem A label offers).sat φ x

/-- **Steps are image-finite** when each label offers finitely many firings. -/
theorem stepSystem_imageFiniteModulo (finite : ∀ ℓ, {f | offers ℓ f}.Finite) :
    (stepSystem A label offers).ImageFiniteModulo := by
  rintro (M : Multiset L) (C : Configuration T O)
  let pool : Set (L × Firing T S O) := {x | x.1 ∈ M ∧ offers x.1 x.2}
  have poolFinite : pool.Finite := by
    refine ((M.toList.finite_toSet).biUnion fun ℓ _ =>
      (Set.finite_singleton ℓ).prod (finite ℓ)).subset ?_
    rintro ⟨ℓ, f⟩ ⟨member, offered⟩
    exact Set.mem_biUnion (x := ℓ) (Multiset.mem_toList.mpr member) ⟨rfl, offered⟩
  refine ⟨(fun w : List (L × Firing T S O) => follow label C (w.map Prod.snd)) ''
    {w : List (L × Firing T S O) | w.length ≤ Multiset.card M ∧ ∀ x ∈ w, x ∈ pool},
    (finite_words poolFinite _).image _, ?_⟩
  rintro D ⟨w, _, offered, _, _, labels, rfl⟩
  refine ⟨_, ⟨w, ⟨?_, fun x member => ⟨?_, offered x member⟩⟩, rfl⟩, rfl⟩
  · rw [labels, Multiset.coe_card, List.length_map]
  · rw [labels, Multiset.mem_coe]
    exact List.mem_map_of_mem member

/-- **Histories are image-finite** when each label offers finitely many firings. -/
theorem histSystem_imageFiniteModulo (finite : ∀ ℓ, {f | offers ℓ f}.Finite) :
    (histSystem A label offers).ImageFiniteModulo := by
  intro lab x
  refine ⟨(fun f => (f.result label x.1, x.2 ++ [(f, lab.2)])) '' {f | offers lab.1 f},
    (finite lab.1).image _, ?_⟩
  rintro y ⟨f, offered, _, _, rfl⟩
  exact ⟨_, ⟨f, offered, rfl⟩, rfl⟩

/-- **Hennessy–Milner for steps**: when each label offers finitely many firings, two configurations
are step bisimilar exactly when they satisfy the same formulas of the step logic. -/
theorem stepBisimilar_iff_sat (finite : ∀ ℓ, {f | offers ℓ f}.Finite) (C D : Configuration T O) :
    StepBisimilar A label offers C D ↔
      ∀ φ : Formula PEmpty.{1} (Multiset L), (StepSat A label offers φ C ↔ StepSat A label offers φ D) :=
  ((stepSystem A label offers).logicallyEquivalent_iff_bisimilar
    (stepSystem_imageFiniteModulo A label offers finite) C D).symm

/-- **Hennessy–Milner for histories**: when each label offers finitely many firings, two
configurations are history-preserving bisimilar exactly when their empty histories satisfy the same
formulas of the history logic. -/
theorem hpBisimilar_iff_sat (finite : ∀ ℓ, {f | offers ℓ f}.Finite) (C D : Configuration T O) :
    HPBisimilar A label offers C D ↔
      ∀ φ : Formula PEmpty.{1} (L × Finset ℕ),
        (HistSat A label offers φ (C, []) ↔ HistSat A label offers φ (D, [])) :=
  ((histSystem A label offers).logicallyEquivalent_iff_bisimilar
    (histSystem_imageFiniteModulo A label offers finite) (C, []) (D, [])).symm

/-- **Finite branching**: for a finite named alphabet whose firings all take or make something, the
steps at a configuration are finitely many. -/
theorem stepMoves_finite (alphabet : List (L × Firing T S O))
    (writes : ∀ x ∈ alphabet, x.2.selection.taken ≠ [] ∨ x.2.selection.made ≠ [])
    (C : Configuration T O) :
    {p : Multiset L × Configuration T O |
      StepMoves A label (fun ℓ f => (ℓ, f) ∈ alphabet) C p.1 p.2}.Finite := by
  refine ((finite_words alphabet.finite_toSet alphabet.length).image fun w =>
    ((↑(w.map Prod.fst) : Multiset L), follow label C (w.map Prod.snd))).subset ?_
  rintro ⟨M, D⟩ ⟨w, _, offered, pairwise, _, rfl, rfl⟩
  have distinct : (w.map Prod.snd).Nodup := by
    refine pairwise.imp_of_mem fun {f g} member _ independent same => ?_
    subst same
    obtain ⟨x, inWord, rfl⟩ := List.mem_map.mp member
    obtain ⟨taken, made⟩ :=
      (AnnotatedRuns.independent_self_iff label A.identity x.2).mp independent.2.2
    rcases writes x (offered x inWord) with nonempty | nonempty
    · exact nonempty taken
    · exact nonempty made
  exact ⟨w, ⟨(distinct.of_map _).length_le_of_subset fun x member => offered x member,
    fun x member => offered x member⟩, rfl⟩

#print axioms finite_words
#print axioms stepSystem_imageFiniteModulo
#print axioms histSystem_imageFiniteModulo
#print axioms stepBisimilar_iff_sat
#print axioms hpBisimilar_iff_sat
#print axioms stepMoves_finite

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race
