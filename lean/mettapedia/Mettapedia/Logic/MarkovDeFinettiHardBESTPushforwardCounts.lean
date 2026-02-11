import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

noncomputable section

namespace Mettapedia.Logic

open scoped Classical BigOperators

namespace MarkovDeFinettiHardBEST

/-! ## Finite cardinality normalizations for pushforward terms -/

lemma sum_if_eq_const
    {Ω Γ : Type*} [Fintype Ω] [DecidableEq Γ]
    (lift : Ω → Γ) (γ : Γ) (c : ℝ) :
    (∑ f : Ω, if lift f = γ then c else 0) =
      (Fintype.card {f : Ω // lift f = γ} : ℝ) * c := by
  classical
  calc
    (∑ f : Ω, if lift f = γ then c else 0)
        = ((Finset.univ.filter (fun f : Ω => lift f = γ)).card : ℝ) * c := by
            rw [← Finset.sum_filter]
            simp [Finset.sum_const, nsmul_eq_mul]
    _ = (Finset.univ.filter (fun f : Ω => lift f = γ)).card * c := by simp
    _ = (Fintype.card {f : Ω // lift f = γ} : ℝ) * c := by
          simp [Fintype.card_subtype]

lemma sum_if_eq_and_pred_const
    {Ω Γ : Type*} [Fintype Ω] [DecidableEq Γ]
    (lift : Ω → Γ) (γ : Γ) (P : Ω → Prop) [DecidablePred P] (c : ℝ) :
    (∑ f : Ω, if lift f = γ ∧ P f then c else 0) =
      (Fintype.card {f : Ω // lift f = γ ∧ P f} : ℝ) * c := by
  classical
  calc
    (∑ f : Ω, if lift f = γ ∧ P f then c else 0)
        = ((Finset.univ.filter (fun f : Ω => lift f = γ ∧ P f)).card : ℝ) * c := by
            rw [← Finset.sum_filter]
            simp [Finset.sum_const, nsmul_eq_mul]
    _ = (Finset.univ.filter (fun f : Ω => lift f = γ ∧ P f)).card * c := by simp
    _ = (Fintype.card {f : Ω // lift f = γ ∧ P f} : ℝ) * c := by
          simp [Fintype.card_subtype]

lemma mu0_push_eq_card
    {m R : ℕ} {Γ : Type*} [DecidableEq Γ]
    (lift : (Fin m → Fin R) → Γ) (γ : Γ) :
    (∑ f : Fin m → Fin R,
      if lift f = γ then (1 : ℝ) / (R : ℝ) ^ m else 0) =
      (Fintype.card {f : Fin m → Fin R // lift f = γ} : ℝ) /
        ((R : ℝ) ^ m) := by
  calc
    (∑ f : Fin m → Fin R,
      if lift f = γ then (1 : ℝ) / (R : ℝ) ^ m else 0) =
      (Fintype.card {f : Fin m → Fin R // lift f = γ} : ℝ) *
        ((1 : ℝ) / (R : ℝ) ^ m) := by
          simpa using
            (sum_if_eq_const (Ω := Fin m → Fin R) (Γ := Γ) lift γ
              ((1 : ℝ) / (R : ℝ) ^ m))
    _ =
      (Fintype.card {f : Fin m → Fin R // lift f = γ} : ℝ) /
        ((R : ℝ) ^ m) := by
          simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]

lemma muinj_push_eq_card_scaled
    {m R : ℕ} {Γ : Type*} [DecidableEq Γ]
    (lift : (Fin m → Fin R) → Γ) (γ : Γ) :
    (∑ f : Fin m → Fin R,
      if lift f = γ then
        (if Function.Injective f then
          (1 : ℝ) / (R : ℝ) ^ m /
            (∑ g : Fin m → Fin R,
              if Function.Injective g then (1 : ℝ) / (R : ℝ) ^ m else 0)
        else 0)
      else 0) =
      (Fintype.card {f : Fin m → Fin R // lift f = γ ∧ Function.Injective f} : ℝ) *
        ((1 : ℝ) / (R : ℝ) ^ m /
          (∑ g : Fin m → Fin R,
            if Function.Injective g then (1 : ℝ) / (R : ℝ) ^ m else 0)) := by
  classical
  let c : ℝ :=
    (1 : ℝ) / (R : ℝ) ^ m /
      (∑ g : Fin m → Fin R,
        if Function.Injective g then (1 : ℝ) / (R : ℝ) ^ m else 0)
  have hpoint :
      ∀ f : Fin m → Fin R,
        (if lift f = γ then (if Function.Injective f then c else 0) else 0) =
          (if lift f = γ ∧ Function.Injective f then c else 0) := by
    intro f
    by_cases h1 : lift f = γ <;> by_cases h2 : Function.Injective f <;> simp [h1, h2]
  calc
    (∑ f : Fin m → Fin R,
      if lift f = γ then
        (if Function.Injective f then
          (1 : ℝ) / (R : ℝ) ^ m /
            (∑ g : Fin m → Fin R,
              if Function.Injective g then (1 : ℝ) / (R : ℝ) ^ m else 0)
        else 0)
      else 0)
        = ∑ f : Fin m → Fin R,
          (if lift f = γ then (if Function.Injective f then c else 0) else 0) := by
            simp [c]
    _ = ∑ f : Fin m → Fin R,
          (if lift f = γ ∧ Function.Injective f then c else 0) := by
            refine Finset.sum_congr rfl ?_
            intro f hf
            exact hpoint f
    _ = (Fintype.card {f : Fin m → Fin R // lift f = γ ∧ Function.Injective f} : ℝ) * c := by
          simpa using
            (sum_if_eq_and_pred_const
              (Ω := Fin m → Fin R) (Γ := Γ) lift γ
              (fun f => Function.Injective f) c)
    _ = (Fintype.card {f : Fin m → Fin R // lift f = γ ∧ Function.Injective f} : ℝ) *
          ((1 : ℝ) / (R : ℝ) ^ m /
            (∑ g : Fin m → Fin R,
              if Function.Injective g then (1 : ℝ) / (R : ℝ) ^ m else 0)) := by
          simp [c]

lemma inj_norm_sum_eq_card_scaled
    {m R : ℕ} :
    (∑ g : Fin m → Fin R,
      if Function.Injective g then (1 : ℝ) / (R : ℝ) ^ m else 0) =
      (Fintype.card {g : Fin m → Fin R // Function.Injective g} : ℝ) *
        ((1 : ℝ) / (R : ℝ) ^ m) := by
  calc
    (∑ g : Fin m → Fin R,
      if Function.Injective g then (1 : ℝ) / (R : ℝ) ^ m else 0) =
      ((Finset.univ.filter (fun g : Fin m → Fin R => Function.Injective g)).card : ℝ) *
        ((1 : ℝ) / (R : ℝ) ^ m) := by
          rw [← Finset.sum_filter]
          simp [Finset.sum_const, nsmul_eq_mul]
    _ =
      (Fintype.card {g : Fin m → Fin R // Function.Injective g} : ℝ) *
        ((1 : ℝ) / (R : ℝ) ^ m) := by
          simp [Fintype.card_subtype]

lemma exists_map_with_fiber_card
    {Γ Ω : Type*} [Fintype Γ] [DecidableEq Γ] [Fintype Ω]
    (A : Γ → Nat)
    (hA : (∑ γ : Γ, A γ) = Fintype.card Ω) :
    ∃ f : Ω → Γ, ∀ γ : Γ, Fintype.card {ω : Ω // f ω = γ} = A γ := by
  classical
  let T := Σ γ : Γ, Fin (A γ)
  have hcard : Fintype.card Ω = Fintype.card T := by
    calc
      Fintype.card Ω = ∑ γ : Γ, A γ := by simpa using hA.symm
      _ = Fintype.card T := by simp [T]
  let e : Ω ≃ T := Fintype.equivOfCardEq hcard
  refine ⟨fun ω => (e ω).1, ?_⟩
  intro γ
  have hcongr :
      Fintype.card {ω : Ω // (e ω).1 = γ} =
        Fintype.card {t : T // t.1 = γ} := by
    let g : {ω : Ω // (e ω).1 = γ} → {t : T // t.1 = γ} :=
      fun ω => ⟨e ω.1, by simpa using ω.2⟩
    have hg_bij : Function.Bijective g := by
      constructor
      · intro ω₁ ω₂ hω
        ext
        exact e.injective (Subtype.ext_iff.mp hω)
      · intro t
        refine ⟨⟨e.symm t.1, by simpa using t.2⟩, ?_⟩
        apply Subtype.ext
        simp [g]
    exact Fintype.card_congr (Equiv.ofBijective g hg_bij)
  calc
    Fintype.card {ω : Ω // (fun ω => (e ω).1) ω = γ}
      = Fintype.card {ω : Ω // (e ω).1 = γ} := by simp
    _ = Fintype.card {t : T // t.1 = γ} := hcongr
    _ = Fintype.card (Fin (A γ)) := by
          refine Fintype.card_congr ?_
          refine
            { toFun := fun t =>
                Fin.cast (by simpa [T] using congrArg A t.2) t.1.2
              invFun := fun i => ⟨⟨γ, i⟩, rfl⟩
              left_inv := ?_
              right_inv := ?_ }
          · intro t
            rcases t with ⟨⟨γ', i⟩, ht⟩
            subst ht
            simp
          · intro i
            simp
    _ = A γ := by simp

lemma exists_lift_with_pred_counts
    {Γ Ω : Type*} [Fintype Γ] [DecidableEq Γ] [Fintype Ω]
    (I : Ω → Prop) [DecidablePred I]
    (A B : Γ → Nat)
    (hA : (∑ γ : Γ, A γ) = Fintype.card Ω)
    (hB : (∑ γ : Γ, B γ) = Fintype.card {ω : Ω // I ω})
    (hBA : ∀ γ, B γ ≤ A γ) :
    ∃ lift : Ω → Γ,
      (∀ γ : Γ, Fintype.card {ω : Ω // lift ω = γ} = A γ) ∧
      (∀ γ : Γ, Fintype.card {ω : Ω // lift ω = γ ∧ I ω} = B γ) := by
  classical
  let C : Γ → Nat := fun γ => A γ - B γ
  have hsumAB :
      (∑ γ : Γ, A γ) = (∑ γ : Γ, B γ) + (∑ γ : Γ, C γ) := by
    calc
      (∑ γ : Γ, A γ) = ∑ γ : Γ, (B γ + C γ) := by
        refine Finset.sum_congr rfl ?_
        intro γ hγ
        simp [C, Nat.add_sub_of_le (hBA γ)]
      _ = (∑ γ : Γ, B γ) + (∑ γ : Γ, C γ) := by
          simp [Finset.sum_add_distrib]
  have hC : (∑ γ : Γ, C γ) = Fintype.card {ω : Ω // ¬ I ω} := by
    have hcardSplit :
        Fintype.card Ω = Fintype.card {ω : Ω // I ω} + (∑ γ : Γ, C γ) := by
      calc
        Fintype.card Ω = ∑ γ : Γ, A γ := by simpa using hA.symm
        _ = (∑ γ : Γ, B γ) + (∑ γ : Γ, C γ) := hsumAB
        _ = Fintype.card {ω : Ω // I ω} + (∑ γ : Γ, C γ) := by simpa [hB]
    have hcompl :
        Fintype.card {ω : Ω // ¬ I ω} =
          Fintype.card Ω - Fintype.card {ω : Ω // I ω} := by
      simpa using (Fintype.card_subtype_compl I)
    omega
  obtain ⟨fInj, hfInj⟩ :=
    exists_map_with_fiber_card (Γ := Γ) (Ω := {ω : Ω // I ω}) B hB
  obtain ⟨fNon, hfNon⟩ :=
    exists_map_with_fiber_card (Γ := Γ) (Ω := {ω : Ω // ¬ I ω}) C hC
  refine ⟨(fun ω => if hω : I ω then fInj ⟨ω, hω⟩ else fNon ⟨ω, hω⟩), ?_⟩
  refine ⟨?_, ?_⟩
  · intro γ
    let lift : Ω → Γ := fun ω => if hω : I ω then fInj ⟨ω, hω⟩ else fNon ⟨ω, hω⟩
    have hsplit :
        Fintype.card {ω : Ω // lift ω = γ} =
          Fintype.card {ω : Ω // lift ω = γ ∧ I ω} +
            Fintype.card {ω : Ω // lift ω = γ ∧ ¬ I ω} := by
      let eSplit :
          {ω : Ω // lift ω = γ} ≃
            ({ω : Ω // lift ω = γ ∧ I ω} ⊕ {ω : Ω // lift ω = γ ∧ ¬ I ω}) :=
        { toFun := fun ω =>
            if hω : I ω.1 then
              Sum.inl ⟨ω.1, ⟨ω.2, hω⟩⟩
            else
              Sum.inr ⟨ω.1, ⟨ω.2, hω⟩⟩
          invFun := fun s =>
            match s with
            | Sum.inl ωI => ⟨ωI.1, ωI.2.1⟩
            | Sum.inr ωN => ⟨ωN.1, ωN.2.1⟩
          left_inv := by
            intro ω
            by_cases hω : I ω.1
            · simp [hω]
            · simp [hω]
          right_inv := by
            intro s
            cases s with
            | inl ωI =>
                simp [ωI.2.2]
            | inr ωN =>
                simp [ωN.2.2] }
      calc
        Fintype.card {ω : Ω // lift ω = γ}
            = Fintype.card ({ω : Ω // lift ω = γ ∧ I ω} ⊕
                {ω : Ω // lift ω = γ ∧ ¬ I ω}) := by
                  exact Fintype.card_congr eSplit
        _ = Fintype.card {ω : Ω // lift ω = γ ∧ I ω} +
              Fintype.card {ω : Ω // lift ω = γ ∧ ¬ I ω} := by
                simp [Fintype.card_sum]
    have hInjCard :
        Fintype.card {ω : Ω // lift ω = γ ∧ I ω} = B γ := by
      let e :
          {ω : Ω // lift ω = γ ∧ I ω} ≃
            {u : {ω : Ω // I ω} // fInj u = γ} :=
        { toFun := fun ω =>
            ⟨⟨ω.1, ω.2.2⟩, by
              simpa [lift, ω.2.2] using ω.2.1⟩
          invFun := fun u =>
            ⟨u.1.1, by
              refine ⟨?_, u.1.2⟩
              simpa [lift, u.1.2] using u.2⟩
          left_inv := by
            intro ω
            ext
            rfl
          right_inv := by
            intro u
            ext
            rfl }
      calc
        Fintype.card {ω : Ω // lift ω = γ ∧ I ω}
            = Fintype.card {u : {ω : Ω // I ω} // fInj u = γ} := by
                exact Fintype.card_congr e
        _ = B γ := hfInj γ
    have hNonCard :
        Fintype.card {ω : Ω // lift ω = γ ∧ ¬ I ω} = C γ := by
      let e :
          {ω : Ω // lift ω = γ ∧ ¬ I ω} ≃
            {u : {ω : Ω // ¬ I ω} // fNon u = γ} :=
        { toFun := fun ω =>
            ⟨⟨ω.1, ω.2.2⟩, by
              simpa [lift, ω.2.2] using ω.2.1⟩
          invFun := fun u =>
            ⟨u.1.1, by
              refine ⟨?_, u.1.2⟩
              simpa [lift, u.1.2] using u.2⟩
          left_inv := by
            intro ω
            ext
            rfl
          right_inv := by
            intro u
            ext
            rfl }
      calc
        Fintype.card {ω : Ω // lift ω = γ ∧ ¬ I ω}
            = Fintype.card {u : {ω : Ω // ¬ I ω} // fNon u = γ} := by
                exact Fintype.card_congr e
        _ = C γ := hfNon γ
    calc
      Fintype.card {ω : Ω // lift ω = γ}
          = Fintype.card {ω : Ω // lift ω = γ ∧ I ω} +
              Fintype.card {ω : Ω // lift ω = γ ∧ ¬ I ω} := hsplit
      _ = B γ + C γ := by rw [hInjCard, hNonCard]
      _ = A γ := by simp [C, Nat.add_sub_of_le (hBA γ)]
  · intro γ
    let lift : Ω → Γ := fun ω => if hω : I ω then fInj ⟨ω, hω⟩ else fNon ⟨ω, hω⟩
    let e :
        {ω : Ω // lift ω = γ ∧ I ω} ≃
          {u : {ω : Ω // I ω} // fInj u = γ} :=
      { toFun := fun ω =>
          ⟨⟨ω.1, ω.2.2⟩, by
            simpa [lift, ω.2.2] using ω.2.1⟩
        invFun := fun u =>
          ⟨u.1.1, by
            refine ⟨?_, u.1.2⟩
            simpa [lift, u.1.2] using u.2⟩
        left_inv := by
          intro ω
          ext
          rfl
        right_inv := by
          intro u
          ext
          rfl }
    calc
      Fintype.card {ω : Ω // lift ω = γ ∧ I ω}
          = Fintype.card {u : {ω : Ω // I ω} // fInj u = γ} := by
              exact Fintype.card_congr e
      _ = B γ := hfInj γ

lemma sum_fiber_counts_eq_card
    {Γ Ω : Type*} [Fintype Γ] [Fintype Ω] [DecidableEq Γ]
    (lift : Ω → Γ) :
    (∑ γ : Γ, Fintype.card {ω : Ω // lift ω = γ}) = Fintype.card Ω := by
  classical
  let T := Σ γ : Γ, {ω : Ω // lift ω = γ}
  have hcardT : Fintype.card T = ∑ γ : Γ, Fintype.card {ω : Ω // lift ω = γ} := by
    simp [T]
  let e : T ≃ Ω :=
    { toFun := fun t => t.2.1
      invFun := fun ω => ⟨lift ω, ⟨ω, rfl⟩⟩
      left_inv := by
        intro t
        rcases t with ⟨γ, ω, hω⟩
        subst hω
        rfl
      right_inv := by
        intro ω
        rfl }
  calc
    (∑ γ : Γ, Fintype.card {ω : Ω // lift ω = γ}) = Fintype.card T := by
      symm
      exact hcardT
    _ = Fintype.card Ω := Fintype.card_congr e

lemma sum_inj_fiber_counts_eq_card
    {Γ Ω : Type*} [Fintype Γ] [Fintype Ω] [DecidableEq Γ]
    (I : Ω → Prop) [DecidablePred I]
    (lift : Ω → Γ) :
    (∑ γ : Γ, Fintype.card {ω : Ω // lift ω = γ ∧ I ω})
      = Fintype.card {ω : Ω // I ω} := by
  classical
  let T := Σ γ : Γ, {ω : Ω // lift ω = γ ∧ I ω}
  have hcardT : Fintype.card T = ∑ γ : Γ, Fintype.card {ω : Ω // lift ω = γ ∧ I ω} := by
    simp [T]
  let e : T ≃ {ω : Ω // I ω} :=
    { toFun := fun t => ⟨t.2.1, t.2.2.2⟩
      invFun := fun ω => ⟨lift ω.1, ⟨ω.1, ⟨rfl, ω.2⟩⟩⟩
      left_inv := by
        intro t
        rcases t with ⟨γ, ω, hω, hI⟩
        subst hω
        rfl
      right_inv := by
        intro ω
        rfl }
  calc
    (∑ γ : Γ, Fintype.card {ω : Ω // lift ω = γ ∧ I ω}) = Fintype.card T := by
      symm
      exact hcardT
    _ = Fintype.card {ω : Ω // I ω} := Fintype.card_congr e

lemma inj_fiber_count_le_fiber_count
    {Γ Ω : Type*} [Fintype Γ] [Fintype Ω] [DecidableEq Γ]
    (I : Ω → Prop) [DecidablePred I]
    (lift : Ω → Γ) (γ : Γ) :
    Fintype.card {ω : Ω // lift ω = γ ∧ I ω}
      ≤ Fintype.card {ω : Ω // lift ω = γ} := by
  exact Fintype.card_subtype_mono
    (fun ω : Ω => lift ω = γ ∧ I ω)
    (fun ω : Ω => lift ω = γ)
    (fun ω hω => hω.1)

lemma counts_from_lift_with_pred
    {Γ Ω : Type*} [Fintype Γ] [Fintype Ω] [DecidableEq Γ]
    (I : Ω → Prop) [DecidablePred I]
    (lift : Ω → Γ) :
    let A : Γ → Nat := fun γ => Fintype.card {ω : Ω // lift ω = γ}
    let B : Γ → Nat := fun γ => Fintype.card {ω : Ω // lift ω = γ ∧ I ω}
    (∑ γ : Γ, A γ) = Fintype.card Ω ∧
    (∑ γ : Γ, B γ) = Fintype.card {ω : Ω // I ω} ∧
    (∀ γ : Γ, B γ ≤ A γ) := by
  intro A B
  refine ⟨?_, ?_, ?_⟩
  · simpa [A] using
      (sum_fiber_counts_eq_card (Γ := Γ) (Ω := Ω) lift)
  · simpa [B] using
      (sum_inj_fiber_counts_eq_card
        (Γ := Γ) (Ω := Ω) (I := I) lift)
  · intro γ
    simpa [A, B] using
      (inj_fiber_count_le_fiber_count
        (Γ := Γ) (Ω := Ω) (I := I) lift γ)

lemma exists_pushforward_repr_of_counts
    {m R : ℕ} {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    (classTerm : Γ → ℝ)
    (A B : Γ → Nat)
    (hA : (∑ γ : Γ, A γ) = Fintype.card (Fin m → Fin R))
    (hB : (∑ γ : Γ, B γ) = Fintype.card {f : Fin m → Fin R // Function.Injective f})
    (hBA : ∀ γ : Γ, B γ ≤ A γ)
    (cInj : ℝ)
    (hcInj :
      (1 : ℝ) / (R : ℝ) ^ m /
        (∑ g : Fin m → Fin R,
          if Function.Injective g then (1 : ℝ) / (R : ℝ) ^ m else 0) = cInj)
    (hreprAB : ∀ γ : Γ,
      classTerm γ =
        abs (((A γ : ℝ) / (R : ℝ) ^ m) - ((B γ : ℝ) * cInj))) :
    let Ω := Fin m → Fin R
    let μ0 : Ω → ℝ := fun _ => (1 : ℝ) / (R : ℝ) ^ m
    let μinj : Ω → ℝ := fun f =>
      if Function.Injective f then
        (1 : ℝ) / (R : ℝ) ^ m /
          (∑ g : Ω, if Function.Injective g then
            (1 : ℝ) / (R : ℝ) ^ m else 0)
      else 0
    ∃ lift : Ω → Γ,
      ∀ γ : Γ,
        classTerm γ =
          abs ((∑ f : Ω, if lift f = γ then μ0 f else 0) -
            (∑ f : Ω, if lift f = γ then μinj f else 0)) := by
  classical
  intro Ω μ0 μinj
  rcases exists_lift_with_pred_counts
      (Γ := Γ) (Ω := Ω) (I := Function.Injective)
      (A := A) (B := B) hA hB hBA with ⟨lift, hliftA, hliftB⟩
  refine ⟨lift, ?_⟩
  intro γ
  have hsum0 :
      (∑ f : Ω, if lift f = γ then μ0 f else 0) =
        (A γ : ℝ) / (R : ℝ) ^ m := by
    calc
      (∑ f : Ω, if lift f = γ then μ0 f else 0)
          = (Fintype.card {f : Ω // lift f = γ} : ℝ) /
              (R : ℝ) ^ m := by
                simpa [μ0] using
                  (mu0_push_eq_card
                    (m := m)
                    (R := R)
                    (Γ := Γ)
                    (lift := lift)
                    (γ := γ))
      _ = (A γ : ℝ) / (R : ℝ) ^ m := by
            simp [hliftA γ]
  have hsumInj :
      (∑ f : Ω, if lift f = γ then μinj f else 0) =
        (B γ : ℝ) * cInj := by
    calc
      (∑ f : Ω, if lift f = γ then μinj f else 0)
          = (Fintype.card {f : Ω // lift f = γ ∧ Function.Injective f} : ℝ) *
              ((1 : ℝ) / (R : ℝ) ^ m /
                (∑ g : Fin m → Fin R,
                  if Function.Injective g then (1 : ℝ) / (R : ℝ) ^ m else 0)) := by
                simpa [μinj] using
                  (muinj_push_eq_card_scaled
                    (m := m)
                    (R := R)
                    (Γ := Γ)
                    (lift := lift)
                    (γ := γ))
      _ = (B γ : ℝ) *
            ((1 : ℝ) / (R : ℝ) ^ m /
              (∑ g : Fin m → Fin R,
                if Function.Injective g then (1 : ℝ) / (R : ℝ) ^ m else 0)) := by
            simp [hliftB γ]
      _ = (B γ : ℝ) * cInj := by
            rw [hcInj]
  calc
    classTerm γ =
      abs (((A γ : ℝ) / (R : ℝ) ^ m) - ((B γ : ℝ) * cInj)) := hreprAB γ
    _ =
      abs ((∑ f : Ω, if lift f = γ then μ0 f else 0) -
        (∑ f : Ω, if lift f = γ then μinj f else 0)) := by
          rw [hsum0, hsumInj]

lemma exists_wr_push_counts
    {m R : ℕ} {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    (hΓ : Nonempty Γ) :
    let Ω := Fin m → Fin R
    let μ0 : Ω → ℝ := fun _ => (1 : ℝ) / (R : ℝ) ^ m
    ∃ lift : Ω → Γ, ∃ A : Γ → Nat,
      (∑ γ : Γ, A γ) = Fintype.card Ω ∧
      (∀ γ : Γ,
        (∑ f : Ω, if lift f = γ then μ0 f else 0) =
          (A γ : ℝ) / (R : ℝ) ^ m) := by
  classical
  intro Ω μ0
  let γ0 : Γ := Classical.choice hΓ
  let lift : Ω → Γ := fun _ => γ0
  let A : Γ → Nat := fun γ => Fintype.card {f : Ω // lift f = γ}
  refine ⟨lift, A, ?_, ?_⟩
  · simpa [A] using
      (sum_fiber_counts_eq_card (Γ := Γ) (Ω := Ω) lift)
  · intro γ
    calc
      (∑ f : Ω, if lift f = γ then μ0 f else 0) =
          (Fintype.card {f : Ω // lift f = γ} : ℝ) / (R : ℝ) ^ m := by
            simpa [μ0] using
              (mu0_push_eq_card
                (m := m) (R := R) (Γ := Γ)
                (lift := lift) (γ := γ))
      _ = (A γ : ℝ) / (R : ℝ) ^ m := by
            simp [A]

lemma wr_class_counts_of_lift
    {m R : ℕ} {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    (lift : (Fin m → Fin R) → Γ) :
    let Ω := Fin m → Fin R
    let A : Γ → Nat := fun γ => Fintype.card {f : Ω // lift f = γ}
    (∑ γ : Γ, A γ) = Fintype.card Ω := by
  intro Ω A
  simpa [A] using
    (sum_fiber_counts_eq_card (Γ := Γ) (Ω := Ω) lift)

lemma wor_class_counts_of_lift
    {m R : ℕ} {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    (lift : (Fin m → Fin R) → Γ) :
    let Ω := Fin m → Fin R
    let B : Γ → Nat := fun γ =>
      Fintype.card {f : Ω // lift f = γ ∧ Function.Injective f}
    (∑ γ : Γ, B γ) = Fintype.card {f : Ω // Function.Injective f} := by
  intro Ω B
  simpa [B] using
    (sum_inj_fiber_counts_eq_card
      (Γ := Γ) (Ω := Ω) (I := Function.Injective) lift)

lemma wor_le_wr_class_counts_of_lift
    {m R : ℕ} {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    (lift : (Fin m → Fin R) → Γ) :
    let Ω := Fin m → Fin R
    let A : Γ → Nat := fun γ => Fintype.card {f : Ω // lift f = γ}
    let B : Γ → Nat := fun γ =>
      Fintype.card {f : Ω // lift f = γ ∧ Function.Injective f}
    (∀ γ : Γ, B γ ≤ A γ) := by
  intro Ω A B γ
  simpa [A, B] using
    (inj_fiber_count_le_fiber_count
      (Γ := Γ) (Ω := Ω) (I := Function.Injective) lift γ)

lemma wor_push_counts_of_lift
    {m R : ℕ} {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    (lift : (Fin m → Fin R) → Γ) :
    let Ω := Fin m → Fin R
    let μinj : Ω → ℝ := fun f =>
      if Function.Injective f then
        (1 : ℝ) / (R : ℝ) ^ m /
          (∑ g : Ω, if Function.Injective g then
            (1 : ℝ) / (R : ℝ) ^ m else 0)
      else 0
    let cInj : ℝ :=
      (1 : ℝ) / (R : ℝ) ^ m /
        (∑ g : Ω, if Function.Injective g then
          (1 : ℝ) / (R : ℝ) ^ m else 0)
    let B : Γ → Nat := fun γ =>
      Fintype.card {f : Ω // lift f = γ ∧ Function.Injective f}
    (∑ γ : Γ, B γ) = Fintype.card {f : Ω // Function.Injective f} ∧
      (∀ γ : Γ,
        (∑ f : Ω, if lift f = γ then μinj f else 0) = (B γ : ℝ) * cInj) := by
  intro Ω μinj cInj B
  refine ⟨?_, ?_⟩
  · simpa [B] using
      (sum_inj_fiber_counts_eq_card
        (Γ := Γ) (Ω := Ω) (I := Function.Injective) lift)
  · intro γ
    simpa [Ω, μinj, cInj, B] using
      (muinj_push_eq_card_scaled
        (m := m)
        (R := R)
        (Γ := Γ)
        (lift := lift)
        (γ := γ))


end MarkovDeFinettiHardBEST

end Mettapedia.Logic
