import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SemanticControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RaceExperiments
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsTensor

/-!
# Congruence under disjoint parallel composition

The parallel composition of two configurations conjoins their knowledge and unites their present
occurrences (`AnnotatedRuns.tensor`).

## Equivalence is a congruence for a disjoint context

* **Renamings extend by the identity** (`RenamingUpTo.union_disjoint`): a renaming up to an
  equivalence of labels that carries `P` to `Q` can be replaced by one that also fixes a set `R`
  disjoint from both and carries `P ∪ R` to `Q ∪ R`.
* **Equivalence modulo the knowledge** (`ModuloEquivalent.tensor_disjoint`) and **pointwise equivalence**
  (`PointwiseEquivalent.tensor_disjoint`): if `C` and `D` are equivalent relative to `E`, then `C ⊗ F` and
  `D ⊗ F` are equivalent relative to `E` together with the context's occurrences, for every
  configuration `F` whose occurrences are disjoint from those of `C` and of `D`.
* **What "compatible knowledge" needs: nothing.** The theorems ask nothing of `F`'s knowledge. The
  knowledge of the composite is the conjunction, which only coarsens the entailed equality of labels;
  when the conjunction is inconsistent at one side it is inconsistent at the other, since `C` and
  `D` have the same solutions. Only disjointness of occurrences is needed (`overlap_control`): an
  occurrence of the context present at one side collapses with it, and multiplicity is observable.
* **Bisimilarity of the ordinary step follows** (`ModuloEquivalent.tensor_bisimilar`), and so does
  bisimilarity of every program whose firings name only identities of `E`
  (`ModuloEquivalent.tensor_program_bisimilar`).
* **Clients** (`Client.respects_tensor`): a client of `C` and `D` and the context's own processes,
  which hold the context's occurrences, observe the same at the two composites.

## Closed bisimilarity of a program is not a congruence

`closed_not_congruence`: the triggered race pair's continuations `{k}` and `{kb}` are bisimilar for
their program and stop being so in parallel with the trigger of `C`, a disjoint context without
knowledge (`Race.Triggered.not_congruence`, read through `tensor_single`). The program names `k`:
the two continuations are equivalent modulo the knowledge relative to no identity and not relative
to `k` (`program_holds_names`). A program is a client of the names it fires on; relative to those
names, equivalence is a congruence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Observation

open AnnotatedRuns
open GuardFreeProcessOrders (SameUpTo)
open Semantic

universe uT uS uO uL

variable {T : Type uT} {S : Type uS} {O : Type uO}

/-- **A renaming extends by the identity on a disjoint set**: a renaming up to `r` that carries `P`
to `Q` can be replaced by one that fixes every identity of `R`, disjoint from `P` and `Q`, and
carries `P ∪ R` to `Q ∪ R`. -/
theorem RenamingUpTo.union_disjoint [DecidableEq O] {r : Setoid T} {label : O → T} {E : Finset O}
    {π : O ≃ O} {P Q R : Finset O} (k : RenamingUpTo r label E π) (onto : P.map π.toEmbedding = Q)
    (apartP : Disjoint P R) (apartQ : Disjoint Q R) :
    ∃ ρ : O ≃ O, RenamingUpTo r label (E ∪ R) ρ ∧ (P ∪ R).map ρ.toEmbedding = Q ∪ R := by
  obtain ⟨escaped, bags⟩ := (exists_renamingUpTo_iff r label E P Q).mp ⟨π, k, onto⟩
  obtain ⟨ρ, kρ, ontoρ, support⟩ := exists_supported_renamingUpTo r label E escaped bags
  have fixesR : ∀ o ∈ R, ρ o = o := fun o inR =>
    support o (Finset.disjoint_right.mp apartP inR) (Finset.disjoint_right.mp apartQ inR)
  refine ⟨ρ, ⟨kρ.keeps, fun o member => ?_⟩, ?_⟩
  · rcases Finset.mem_union.mp member with inE | inR
    · exact kρ.fixes o inE
    · exact fixesR o inR
  · rw [Finset.map_union, ontoρ, finset_map_eq_self ρ fixesR]

section Congruence

variable {A : SubstitutionAction T S} {label : O → T} {E : Finset O}

/-- **Equivalence modulo the knowledge is a congruence for a disjoint context.** -/
theorem ModuloEquivalent.tensor_disjoint [DecidableEq O] {C D : Configuration T O}
    (h : ModuloEquivalent A label E C D) (F : Configuration T O)
    (apartC : Disjoint C.present F.present) (apartD : Disjoint D.present F.present) :
    ModuloEquivalent A label (E ∪ F.present) (AnnotatedRuns.tensor C F) (AnnotatedRuns.tensor D F) := by
  obtain ⟨π, k, same⟩ := h
  obtain ⟨ρ, kρ, onto⟩ := k.union_disjoint same.2 apartC apartD
  refine ⟨ρ, kρ.weaken (entailedSetoid_mono (A.append_refines C.equations F.equations)), ?_, onto⟩
  intro σ
  show A.Models σ (C.equations ++ F.equations) ↔ A.Models σ (D.equations ++ F.equations)
  rw [A.models_append, A.models_append]
  exact and_congr (same.1 σ) Iff.rfl

/-- **Pointwise equivalence is a congruence for a disjoint context.** -/
theorem PointwiseEquivalent.tensor_disjoint [DecidableEq O] {C D : Configuration T O}
    (h : PointwiseEquivalent A label E C D) (F : Configuration T O)
    (apartC : Disjoint C.present F.present) (apartD : Disjoint D.present F.present) :
    PointwiseEquivalent A label (E ∪ F.present) (AnnotatedRuns.tensor C F) (AnnotatedRuns.tensor D F) := by
  obtain ⟨equivalent, escaped, each⟩ := h
  refine ⟨fun σ => ?_, fun o member => ?_, fun σ solved => ?_⟩
  · show A.Models σ (C.equations ++ F.equations) ↔ A.Models σ (D.equations ++ F.equations)
    rw [A.models_append, A.models_append]
    exact and_congr (equivalent σ) Iff.rfl
  · show o ∈ C.present ∪ F.present ↔ o ∈ D.present ∪ F.present
    rw [Finset.mem_union, Finset.mem_union]
    rcases Finset.mem_union.mp member with inE | inF
    · exact or_congr (escaped o inE) Iff.rfl
    · exact ⟨fun _ => Or.inr inF, fun _ => Or.inr inF⟩
  · have solvedC : A.Models σ C.equations := ((A.models_append σ _ _).mp solved).1
    obtain ⟨π, k, onto⟩ := each σ solvedC
    exact k.union_disjoint onto apartC apartD

/-- **Composites of equivalent configurations are bisimilar for the ordinary step**, given a fresh
supply of every label. -/
theorem ModuloEquivalent.tensor_bisimilar [DecidableEq O] (supply : FreshSupply label)
    {C D : Configuration T O} (h : ModuloEquivalent A label E C D) (F : Configuration T O)
    (apartC : Disjoint C.present F.present) (apartD : Disjoint D.present F.present) :
    Race.Bisimilar A label (ruleOffers A) (AnnotatedRuns.tensor C F) (AnnotatedRuns.tensor D F) :=
  (h.tensor_disjoint F apartC apartD).semantic_bisimilar supply

/-- **Composites are bisimilar for every program whose firings are semantic and name only identities
of `E`.** -/
theorem ModuloEquivalent.tensor_program_bisimilar [DecidableEq O] {L : Type uL}
    {offers : L → Firing T S O → Prop}
    (named : ∀ ℓ f, offers ℓ f → f.names ⊆ E ∧ IsSemantic A f) {C D : Configuration T O}
    (h : ModuloEquivalent A label E C D) (F : Configuration T O)
    (apartC : Disjoint C.present F.present) (apartD : Disjoint D.present F.present) :
    Race.Bisimilar A label offers (AnnotatedRuns.tensor C F) (AnnotatedRuns.tensor D F) :=
  (h.tensor_disjoint F apartC apartD).program_bisimilar fun ℓ f offered =>
    ⟨(named ℓ f offered).1.trans Finset.subset_union_left, (named ℓ f offered).2⟩

/-- **Clients respect composition with a disjoint context**: every probe naming only the client's
identities and the context's occurrences observes the same at the two composites. -/
theorem Client.respects_tensor [DecidableEq O] (c : Client O) {C D : Configuration T O}
    (h : ModuloEquivalent A label c.escaped C D) (F : Configuration T O)
    (apartC : Disjoint C.present F.present) (apartD : Disjoint D.present F.present)
    {p : ModuloProbe A O} (permitted : p.names ⊆ c.escaped ∪ F.present) :
    p.Observes label (AnnotatedRuns.tensor C F) ↔ p.Observes label (AnnotatedRuns.tensor D F) :=
  (h.tensor_disjoint F apartC apartD).observes permitted

end Congruence

/-- Adding one occurrence is composition with that occurrence. -/
theorem tensor_single [DecidableEq O] (C : Configuration T O) (o : O) :
    AnnotatedRuns.tensor C ⟨[], {o}⟩ = Race.addAtom C o := by
  show (⟨C.equations ++ [], C.present ∪ {o}⟩ : Configuration T O) = ⟨C.equations, insert o C.present⟩
  rw [List.append_nil, Finset.insert_eq, Finset.union_comm]

/-! ## Controls -/

namespace CongruenceControls

open ModuloControls (Tm c2 c2_equivalent)
open ConstraintMultisetRewriting.Controls (A)

/-- **The context must be disjoint from both sides**: the row `21` composed with C2 is present at
one side already, and the composites hold two rows against one. -/
theorem overlap_control :
    ModuloEquivalent A ModuloControls.label ∅ (c2 20) (c2 21) ∧
      Disjoint (c2 20).present ({21} : Finset ℕ) ∧
      ¬ ModuloEquivalent A ModuloControls.label ∅ (AnnotatedRuns.tensor (c2 20) ⟨[], {21}⟩) (AnnotatedRuns.tensor (c2 21) ⟨[], {21}⟩) := by
  refine ⟨c2_equivalent, by decide, fun h => ?_⟩
  have counts := h.card_eq
  exact absurd counts (by decide)

/-- **Closed bisimilarity of a program is not a congruence for a disjoint context.** -/
theorem closed_not_congruence {T : Type uT} {S : Type uS} (A : SubstitutionAction T S) (τ : T) :
    Race.Bisimilar A (Race.Triggered.label τ) (Race.Triggered.offers τ) Race.Triggered.X Race.Triggered.Y ∧
      Disjoint (Race.Triggered.X (T := T)).present {Race.Triggered.Site.tc} ∧
      Disjoint (Race.Triggered.Y (T := T)).present {Race.Triggered.Site.tc} ∧
      ¬ Race.Bisimilar A (Race.Triggered.label τ) (Race.Triggered.offers τ)
        (AnnotatedRuns.tensor Race.Triggered.X ⟨[], {Race.Triggered.Site.tc}⟩)
        (AnnotatedRuns.tensor Race.Triggered.Y ⟨[], {Race.Triggered.Site.tc}⟩) := by
  refine ⟨(Race.Triggered.not_congruence τ A).1, by simp [Race.Triggered.X],
    by simp [Race.Triggered.Y], ?_⟩
  rw [tensor_single, tensor_single]
  exact (Race.Triggered.not_congruence τ A).2

/-- **The program holds the names it fires on**: the continuations `{k}` and `{kb}` are equivalent
modulo the knowledge relative to no identity, and not relative to `k`. -/
theorem program_holds_names {T : Type uT} {S : Type uS} (A : SubstitutionAction T S) (τ : T) :
    ModuloEquivalent A (Race.Triggered.label τ) ∅ Race.Triggered.X Race.Triggered.Y ∧
      ¬ ModuloEquivalent A (Race.Triggered.label τ) {Race.Triggered.Site.k} Race.Triggered.X
        Race.Triggered.Y := by
  refine ⟨(moduloEquivalent_iff A _ ∅ _ _).mpr ⟨fun _ => Iff.rfl, fun o member =>
    absurd member (Finset.notMem_empty o), ?_⟩, fun h => ?_⟩
  · show ({Race.Triggered.Site.k} : Finset Race.Triggered.Site).val.map
        (fun o => Quotient.mk (entailedSetoid A ([] : EquationStore T)) (Race.Triggered.label τ o)) =
      ({Race.Triggered.Site.kb} : Finset Race.Triggered.Site).val.map
        (fun o => Quotient.mk (entailedSetoid A ([] : EquationStore T)) (Race.Triggered.label τ o))
    rw [Finset.singleton_val, Finset.singleton_val, Multiset.map_singleton, Multiset.map_singleton]
    rfl
  · have moved := (h.escaped_iff (Finset.mem_singleton_self Race.Triggered.Site.k)).mp
      (Finset.mem_singleton_self _)
    simp [Race.Triggered.Y] at moved

end CongruenceControls

#print axioms RenamingUpTo.union_disjoint
#print axioms ModuloEquivalent.tensor_disjoint
#print axioms PointwiseEquivalent.tensor_disjoint
#print axioms ModuloEquivalent.tensor_bisimilar
#print axioms ModuloEquivalent.tensor_program_bisimilar
#print axioms Client.respects_tensor
#print axioms tensor_single
#print axioms CongruenceControls.overlap_control
#print axioms CongruenceControls.closed_not_congruence
#print axioms CongruenceControls.program_holds_names

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Observation
