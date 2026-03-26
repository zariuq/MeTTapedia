import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mettapedia.Logic.MarkovLogicCountableProjectiveExtension

/-!
# Countable Boolean Projective Limits

This module proves the generic nat-indexed extension theorem needed by the
infinite-MLN lane.

Given a projective family of probability measures on the Boolean prefixes
`Π i : Iic n, Bool`, we recover one-step conditional kernels using
`condDistrib`, build the corresponding `trajMeasure`, and prove that its prefix
marginals are exactly the original family.

This is the council-backed high-confidence route to the first honest global
measure theorem: prove the generic countable Boolean extension layer first, then
instantiate it for the MLN limit-family.
-/

namespace Mettapedia.Logic.MarkovLogicCountableProjectiveLimit

open MeasureTheory
open ProbabilityTheory
open Preorder

/-- Boolean-valued coordinates over `ℕ`, restricted to the prefix `Iic n`. -/
abbrev PrefixBool (n : ℕ) := ∀ _ : Finset.Iic n, Bool

/-- The final coordinate of a prefix of length `n + 1`. -/
def lastCoord (n : ℕ) : PrefixBool (n + 1) → Bool :=
  fun x => x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩

/-- The prefix/last-coordinate decomposition map on length `n + 1` Boolean
prefixes. -/
def nextPairMap (n : ℕ) : PrefixBool (n + 1) → PrefixBool n × Bool :=
  fun x => (frestrictLe₂ (π := fun _ : ℕ => Bool) (Nat.le_succ n) x, lastCoord n x)

/-- Reassemble a prefix of length `n + 1` from a prefix of length `n` and the
next Boolean coordinate. -/
noncomputable def succAssemble (n : ℕ) : PrefixBool n × Bool → PrefixBool (n + 1) :=
  fun x =>
    (MeasurableEquiv.IicProdIoc (X := fun _ : ℕ => Bool) (Nat.le_succ n))
      (x.1, (MeasurableEquiv.piSingleton (X := fun _ : ℕ => Bool) n) x.2)

@[simp]
theorem succAssemble_apply_le (n : ℕ) (x : PrefixBool n × Bool)
    {i : Finset.Iic (n + 1)} (hi : i.1 ≤ n) :
    succAssemble n x i = x.1 ⟨i.1, Finset.mem_Iic.2 hi⟩ := by
  unfold succAssemble
  simp [MeasurableEquiv.IicProdIoc, hi]

@[simp]
theorem succAssemble_apply_last (n : ℕ) (x : PrefixBool n × Bool) :
    succAssemble n x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩ = x.2 := by
  unfold succAssemble
  simp [MeasurableEquiv.IicProdIoc, MeasurableEquiv.piSingleton]

@[simp]
theorem succAssemble_nextPairMap (n : ℕ) :
    succAssemble n ∘ nextPairMap n = id := by
  ext x i
  by_cases hi : i.1 ≤ n
  · simpa [nextPairMap, lastCoord] using
      (succAssemble_apply_le n (x := nextPairMap n x) hi)
  · have hi_eq : i = ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩ := by
      apply Subtype.ext
      have hi_lt : n < i.1 := Nat.lt_of_not_ge hi
      exact le_antisymm (Finset.mem_Iic.1 i.2) (Nat.succ_le_of_lt hi_lt)
    subst hi_eq
    calc
      succAssemble n (nextPairMap n x) ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩ = (nextPairMap n x).2 :=
        succAssemble_apply_last n (x := nextPairMap n x)
      _ = x ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩ := rfl

@[simp]
theorem succAssemble_worldPair (n : ℕ) :
    succAssemble n ∘ (fun x : ℕ → Bool => (frestrictLe n x, x (n + 1))) =
      frestrictLe (π := fun _ : ℕ => Bool) (n + 1) := by
  ext x i
  by_cases hi : i.1 ≤ n
  · simpa using (succAssemble_apply_le n (x := (frestrictLe n x, x (n + 1))) hi)
  · have hi_eq : i = ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩ := by
      apply Subtype.ext
      have hi_lt : n < i.1 := Nat.lt_of_not_ge hi
      exact le_antisymm (Finset.mem_Iic.1 i.2) (Nat.succ_le_of_lt hi_lt)
    subst hi_eq
    exact succAssemble_apply_last n (x := (frestrictLe n x, x (n + 1)))

section PrefixFamily

variable (μ : (n : ℕ) → Measure (PrefixBool n))
variable [∀ n, IsProbabilityMeasure (μ n)]

/-- The initial one-coordinate Boolean measure extracted from the first prefix
measure `μ 0`. -/
noncomputable def initialBoolMeasure : Measure Bool :=
  (μ 0).map (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => Bool))

instance initialBoolMeasure_isProbabilityMeasure :
    IsProbabilityMeasure (initialBoolMeasure μ) := by
  unfold initialBoolMeasure
  exact Measure.isProbabilityMeasure_map
    (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => Bool)).measurable.aemeasurable

/-- Recover the one-step kernel from the `n + 1` prefix law by conditioning the
last coordinate on the first `n + 1` coordinates. -/
noncomputable def nextKernel (n : ℕ) : ProbabilityTheory.Kernel (PrefixBool n) Bool :=
  ProbabilityTheory.condDistrib
    (lastCoord n)
    (frestrictLe₂ (π := fun _ : ℕ => Bool) (Nat.le_succ n))
    (μ (n + 1))

theorem measurable_lastCoord (n : ℕ) : Measurable (lastCoord n) := by
  unfold lastCoord
  exact measurable_pi_apply _

instance nextKernel_isMarkovKernel (n : ℕ) :
    ProbabilityTheory.IsMarkovKernel (nextKernel (μ := μ) n) := by
  unfold nextKernel
  infer_instance

/-- The global measure on `ℕ → Bool` generated from the recovered initial law
and one-step kernels. -/
noncomputable def natProjectiveLimit : Measure (ℕ → Bool) :=
  ProbabilityTheory.Kernel.trajMeasure (X := fun _ : ℕ => Bool)
    (initialBoolMeasure μ) (nextKernel (μ := μ))

variable {μ}

theorem nextKernel_compProd_eq_map
    (hμ :
      ∀ a b : ℕ, ∀ hab : a ≤ b,
        (μ b).map (frestrictLe₂ (π := fun _ : ℕ => Bool) hab) = μ a)
    (n : ℕ) :
    ((μ n).compProd (nextKernel (μ := μ) n)) =
      (μ (n + 1)).map (nextPairMap n) := by
  have hcond :
      ((μ (n + 1)).map (frestrictLe₂ (π := fun _ : ℕ => Bool) (Nat.le_succ n))).compProd
          (ProbabilityTheory.condDistrib
            (lastCoord n)
            (frestrictLe₂ (π := fun _ : ℕ => Bool) (Nat.le_succ n))
            (μ (n + 1))) =
        (μ (n + 1)).map (nextPairMap n) := by
    simpa [nextPairMap] using
      (ProbabilityTheory.compProd_map_condDistrib
      (μ := μ (n + 1))
      (X := frestrictLe₂ (π := fun _ : ℕ => Bool) (Nat.le_succ n))
      (Y := lastCoord n)
      ((measurable_lastCoord n).aemeasurable))
  rw [hμ n (n + 1) (Nat.le_succ n)] at hcond
  simpa [nextKernel] using hcond

theorem natProjectiveLimit_prefix_zero :
    (natProjectiveLimit (μ := μ)).map (frestrictLe (π := fun _ : ℕ => Bool) 0) = μ 0 := by
  unfold natProjectiveLimit ProbabilityTheory.Kernel.trajMeasure initialBoolMeasure
  rw [Measure.map_comp _ _ (by fun_prop)]
  rw [ProbabilityTheory.Kernel.traj_map_frestrictLe (X := fun _ : ℕ => Bool)]
  rw [ProbabilityTheory.Kernel.partialTraj_self, Measure.id_comp]
  rw [Measure.map_map]
  · ext s hs
    rw [Measure.map_apply (by fun_prop) hs]
    congr 1
    ext f
    have hf : uniqueElim (f default) = f := by
      ext i
      simpa using congrArg f (Subsingleton.elim default i)
    simp [hf]
  · fun_prop
  · fun_prop

theorem natProjectiveLimit_prefix
    (hμ :
      ∀ a b : ℕ, ∀ hab : a ≤ b,
        (μ b).map (frestrictLe₂ (π := fun _ : ℕ => Bool) hab) = μ a) :
    ∀ n, (natProjectiveLimit (μ := μ)).map (frestrictLe (π := fun _ : ℕ => Bool) n) = μ n
  | 0 => natProjectiveLimit_prefix_zero (μ := μ)
  | n + 1 => by
      have ih :
          (natProjectiveLimit (μ := μ)).map (frestrictLe (π := fun _ : ℕ => Bool) n) = μ n :=
        natProjectiveLimit_prefix hμ n
      have htraj :=
        ProbabilityTheory.Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
          (X := fun _ : ℕ => Bool)
          (μ₀ := initialBoolMeasure μ) (κ := nextKernel (μ := μ)) (a := n)
      have hpair :
          (natProjectiveLimit (μ := μ)).map (fun x : ℕ → Bool => (frestrictLe n x, x (n + 1))) =
            (μ (n + 1)).map (nextPairMap n) := by
        calc
          (natProjectiveLimit (μ := μ)).map (fun x : ℕ → Bool => (frestrictLe n x, x (n + 1)))
            = ((natProjectiveLimit (μ := μ)).map (frestrictLe (π := fun _ : ℕ => Bool) n)).compProd
                (nextKernel (μ := μ) n) := htraj.symm
          _ = (μ n).compProd (nextKernel (μ := μ) n) := by rw [ih]
          _ = (μ (n + 1)).map (nextPairMap n) := nextKernel_compProd_eq_map hμ n
      have hassembled := congrArg (fun ν => ν.map (succAssemble n)) hpair
      change
        Measure.map (succAssemble n)
            (Measure.map (fun x : ℕ → Bool => (frestrictLe n x, x (n + 1)))
              (natProjectiveLimit (μ := μ))) =
          Measure.map (succAssemble n) (Measure.map (nextPairMap n) (μ (n + 1))) at hassembled
      rw [Measure.map_map, Measure.map_map] at hassembled
      · simpa [succAssemble_worldPair, succAssemble_nextPairMap] using hassembled
      · fun_prop
      · fun_prop
      · fun_prop
      · fun_prop

/-- The trajectory-built global measure is the projective limit of the prefix
family `μ`. -/
theorem natProjectiveLimit_isProjectiveLimit
    (hμ :
      ∀ a b : ℕ, ∀ hab : a ≤ b,
        (μ b).map (frestrictLe₂ (π := fun _ : ℕ => Bool) hab) = μ a) :
    MeasureTheory.IsProjectiveLimit
      (ι := ℕ) (α := fun _ : ℕ => Bool)
      (natProjectiveLimit (μ := μ)) (MeasureTheory.inducedFamily (X := fun _ : ℕ => Bool) (μ := μ)) := by
  refine
    (MeasureTheory.isProjectiveLimit_nat_iff
      (μ := MeasureTheory.inducedFamily (X := fun _ : ℕ => Bool) (μ := μ))
      (hμ := MeasureTheory.isProjectiveMeasureFamily_inducedFamily
        (X := fun _ : ℕ => Bool) (μ := μ) hμ)
      (ν := natProjectiveLimit (μ := μ))).2 ?_
  intro n
  simpa [MeasureTheory.inducedFamily_Iic] using natProjectiveLimit_prefix (μ := μ) hμ n

end PrefixFamily

section CountableTransport

open Mettapedia.Logic.MarkovLogicCountableProjectiveExtension
open Mettapedia.Logic.MarkovLogicInfiniteSpecification

variable {Atom : Type*}

/-- Bool-valued coordinates over an arbitrary atom type. -/
abbrev BoolCoord (Atom : Type*) (_ : Atom) := Bool

/-- The global measure on `Atom → Bool` obtained by transporting the nat-indexed
projective limit along an enumeration `ℕ ≃ Atom`. -/
noncomputable def countableProjectiveLimit
    (e : ℕ ≃ Atom)
    (P : ∀ I : Finset Atom, Measure (∀ i : I, BoolCoord Atom i))
    [∀ I, IsProbabilityMeasure (P I)] :
    Measure (InfiniteWorld Atom) :=
  transportMeasure e (natProjectiveLimit (μ := prefixFamily e P))

/-- The transported global measure has the prescribed finite-dimensional
marginals. -/
theorem countableProjectiveLimit_marginal
    (e : ℕ ≃ Atom)
    (P : ∀ I : Finset Atom, Measure (∀ i : I, BoolCoord Atom i))
    [∀ I, IsProbabilityMeasure (P I)]
    (hP : MeasureTheory.IsProjectiveMeasureFamily P)
    (I : Finset Atom) :
    (countableProjectiveLimit e P).map I.restrict = P I := by
  classical
  let J : Finset ℕ := I.preimage e.toEmbedding e.injective.injOn
  let N : ℕ := J.sup id
  let K : Finset Atom := (Finset.Iic N).map e.toEmbedding
  have hsub : J ⊆ Finset.Iic N := by
    simpa [N] using (J.subset_Iic_sup_id : J ⊆ Finset.Iic (J.sup id))
  have hIK : I ⊆ K := by
    intro a ha
    refine Finset.mem_map.mpr ?_
    refine ⟨e.symm a, ?_, by simp⟩
    have hmem : e.symm a ∈ J := by
      simpa [J] using ha
    exact Finset.mem_Iic.mpr (Finset.le_sup (f := id) hmem)
  have hrestrict :
      I.restrict ∘ ⇑(MeasurableEquiv.piCongrLeft (fun _ : Atom => Bool) e) =
        ⇑(MeasurableEquiv.piCongrLeft (fun i : I => Bool)
          (e.restrictPreimageFinset I)) ∘ J.restrict := by
    simpa [J] using
      (Finset.restrict_comp_piCongrLeft (π := fun _ : Atom => Bool) I e)
  have hcomp :
      ⇑(MeasurableEquiv.piCongrLeft (fun i : I => Bool)
          (e.restrictPreimageFinset I)) ∘
          Finset.restrict₂ (π := fun _ : ℕ => Bool) hsub ∘
            ⇑((MeasurableEquiv.piCongrLeft (fun i : K => Bool)
              (prefixEquiv e N)).symm) =
        Finset.restrict₂ (π := fun _ : Atom => Bool) hIK := by
    ext x b
    let eJ : J ≃ I := e.restrictPreimageFinset I
    let j : J := eJ.symm b
    let iN : Finset.Iic N := ⟨j.1, hsub j.2⟩
    have hb : eJ j = b := by
      simp [eJ, j]
    rw [show b = eJ j by simpa using hb.symm]
    have houter :
        (MeasurableEquiv.piCongrLeft (fun i : I => Bool) eJ)
            ((fun i : J =>
                Finset.restrict₂ (π := fun _ : ℕ => Bool) hsub
                  ((MeasurableEquiv.piCongrLeft (fun i : K => Bool)
                    (prefixEquiv e N)).symm x) i)) (eJ j)
          =
        (Finset.restrict₂ (π := fun _ : ℕ => Bool) hsub
          ((MeasurableEquiv.piCongrLeft (fun i : K => Bool)
            (prefixEquiv e N)).symm x)) j := by
      simpa using
        (MeasurableEquiv.piCongrLeft_apply_apply
          (β := fun i : I => Bool)
          (e := eJ)
          (x := fun i : J =>
            Finset.restrict₂ (π := fun _ : ℕ => Bool) hsub
              ((MeasurableEquiv.piCongrLeft (fun i : K => Bool)
                (prefixEquiv e N)).symm x) i)
          (i := j))
    have houter' :
        (⇑(MeasurableEquiv.piCongrLeft (fun i : I => Bool)
            (e.restrictPreimageFinset I)) ∘
              Finset.restrict₂ (π := fun _ : ℕ => Bool) hsub ∘
                ⇑((MeasurableEquiv.piCongrLeft (fun i : K => Bool)
                  (prefixEquiv e N)).symm)) x (eJ j)
          =
        (Finset.restrict₂ (π := fun _ : ℕ => Bool) hsub
          ((MeasurableEquiv.piCongrLeft (fun i : K => Bool)
            (prefixEquiv e N)).symm x)) j := by
      simpa [Function.comp, eJ] using houter
    rw [houter']
    change
      ((MeasurableEquiv.piCongrLeft (fun i : K => Bool)
        (prefixEquiv e N)).symm x) iN =
        x ⟨(eJ j).1, hIK (eJ j).2⟩
    have hprefix : prefixEquiv e N iN = ⟨(eJ j).1, hIK (eJ j).2⟩ := by
      apply Subtype.ext
      change e j.1 = (eJ j).1
      rfl
    calc
      ((MeasurableEquiv.piCongrLeft (fun i : K => Bool)
        (prefixEquiv e N)).symm x) iN = x (prefixEquiv e N iN) := by
          exact
            (Equiv.piCongrLeft_symm_apply
              (P := fun i : K => Bool)
              (e := prefixEquiv e N) (g := x) (a := iN))
      _ = x ⟨(eJ j).1, hIK (eJ j).2⟩ := by rw [hprefix]
  calc
    (countableProjectiveLimit e P).map I.restrict
        =
      Measure.map
        (I.restrict ∘ ⇑(MeasurableEquiv.piCongrLeft (fun _ : Atom => Bool) e))
        (natProjectiveLimit (μ := prefixFamily e P)) := by
          unfold countableProjectiveLimit transportMeasure
          rw [Measure.map_map]
          · exact Finset.measurable_restrict I
          · exact (MeasurableEquiv.piCongrLeft (fun _ : Atom => Bool) e).measurable
    _ =
      Measure.map
        (⇑(MeasurableEquiv.piCongrLeft (fun i : I => Bool)
          (e.restrictPreimageFinset I)) ∘ J.restrict)
        (natProjectiveLimit (μ := prefixFamily e P)) := by
          simpa [Function.comp, J] using
            congrArg
              (fun f =>
                Measure.map f (natProjectiveLimit (μ := prefixFamily e P)))
              hrestrict
    _ =
      ((natProjectiveLimit (μ := prefixFamily e P)).map J.restrict).map
        (MeasurableEquiv.piCongrLeft (fun i : I => Bool)
          (e.restrictPreimageFinset I)) := by
          rw [← Measure.map_map]
          · exact
              (MeasurableEquiv.piCongrLeft (fun i : I => Bool)
                (e.restrictPreimageFinset I)).measurable
          · exact Finset.measurable_restrict J
    _ =
      (MeasureTheory.inducedFamily (X := fun _ : ℕ => Bool)
        (μ := prefixFamily e P) J).map
          (MeasurableEquiv.piCongrLeft (fun i : I => Bool)
            (e.restrictPreimageFinset I)) := by
              rw [(natProjectiveLimit_isProjectiveLimit
                (μ := prefixFamily e P)
                (hμ := fun a b hab => prefixFamily_projective e P hP hab)) J]
    _ = (P K).map (Finset.restrict₂ (π := fun _ : Atom => Bool) hIK) := by
      rw [MeasureTheory.inducedFamily, prefixFamily]
      rw [Measure.map_map, Measure.map_map]
      · simpa [Function.comp] using
          congrArg (fun f => Measure.map f (P K)) hcomp
      · fun_prop
      · fun_prop
      · fun_prop
      · fun_prop
    _ = P I := by
      symm
      exact hP K I hIK

/-- The transported countable projective limit is a projective limit of the
original family over the atom index type. -/
theorem countableProjectiveLimit_isProjectiveLimit
    (e : ℕ ≃ Atom)
    (P : ∀ I : Finset Atom, Measure (∀ i : I, BoolCoord Atom i))
    [∀ I, IsProbabilityMeasure (P I)]
    (hP : MeasureTheory.IsProjectiveMeasureFamily P) :
    MeasureTheory.IsProjectiveLimit (countableProjectiveLimit e P) P := by
  intro I
  exact countableProjectiveLimit_marginal e P hP I

end CountableTransport

end Mettapedia.Logic.MarkovLogicCountableProjectiveLimit
