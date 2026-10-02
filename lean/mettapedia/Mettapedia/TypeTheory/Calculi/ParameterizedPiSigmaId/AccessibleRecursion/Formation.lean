import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion.Package

/-!
# Formation of the recursor and of its unfolding

Under the laws of the package, the declared type of the recursor is a type of a
universe above the motives (`recType_typed`), so the recursor is a typed constant
of the extended package, and every full application to typed arguments has the
motive at the point as its type (`rec_apply`). The declared type of the
propositional unfolding is formed as well (`unfoldType_typed`), and its full
applications prove the identity between the recursor and one step of its
unfolding (`unfold_apply`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion

open Presentation Presentation.TypedEquality Presentation.TypedEquality.Impredicative
open TelescopeAbstraction (closeType applyClosed)

variable {Head : Type}


namespace Signature

variable (S : Signature Head)

theorem consSub_two_eta {n : Nat} (σ : Sub Head 2 n) :
    consSub (σ 0) (consSub (σ 1) (fun i => Fin.elim0 i)) = σ := by
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  refine Fin.cases rfl (fun k => Fin.elim0 k) j

/-- The step type over the variables `P = var 1`, `R = var 0` is the step type. -/
theorem stepTypeOf_vars : S.stepTypeOf (.var 1) (.var 0) = S.stepType := by
  have e : consSub (.var 0 : Tm Head 2) (consSub (.var 1) (fun i => Fin.elim0 i)) = ids :=
    consSub_two_eta (σ := ids)
  simp only [stepTypeOf, e, subst_ids]

theorem rename_stepTypeOf {n m : Nat} (ρ : Ren n m) (P R : Tm Head n) :
    rename ρ (S.stepTypeOf P R) = S.stepTypeOf (rename ρ P) (rename ρ R) := by
  simp only [stepTypeOf, rename_subst]
  congr 1
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  refine Fin.cases rfl (fun k => Fin.elim0 k) j

theorem subst_stepTypeOf {n m : Nat} (σ : Sub Head n m) (P R : Tm Head n) :
    subst σ (S.stepTypeOf P R) = S.stepTypeOf (subst σ P) (subst σ R) := by
  simp only [stepTypeOf, subst_comp]
  congr 1
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  refine Fin.cases rfl (fun k => Fin.elim0 k) j

/-- The step type, written with weakenings: `Π x. (Π y. holds (R y x) → P y) → P x`. -/
theorem stepTypeOf_eq {n : Nat} (P R : Tm Head n) :
    S.stepTypeOf P R =
      .pi (liftClosed S.carrier)
        (.pi (.pi (liftClosed S.carrier)
            (.pi (S.codes.holdsOf (CodeNames.relOf (rename wk (rename wk R)) (.var 0) (.var 1)))
              (.app (rename wk (rename wk (rename wk P))) (.var 1))))
          (.app (rename wk (rename wk P)) (.var 1))) := by
  simp only [stepTypeOf, stepType, Presentation.subst, subst_liftClosed, Codes.holdsOf,
    CodeNames.relOf]
  rfl

end Signature

namespace Signature.Universes

variable {S : Signature Head} {B : Rules Head} (U : S.Universes B)
include U

theorem motiveType_typed {n : Nat} {Γ : Ctx Head n} {t : Head}
    (hmt : ∀ {k : Nat} {Δ : Ctx Head k}, Typed (S.toCodeNames.rules B) Δ (.head S.motive) (.head t))
    (toTop : ∀ {k : Nat} {Δ : Ctx Head k} {X : Tm Head k},
      Typed (S.toCodeNames.rules B) Δ X (.head S.motive) →
        Typed (S.toCodeNames.rules B) Δ X (.head t))
    (piTop : ∀ {k : Nat} {Δ : Ctx Head k} {X : Tm Head k} {Y : Tm Head (k + 1)},
      Typed (S.toCodeNames.rules B) Δ X (.head t) →
        Typed (S.toCodeNames.rules B) (.snoc Δ X) Y (.head t) →
        Typed (S.toCodeNames.rules B) Δ (.pi X Y) (.head t)) :
    Typed (S.toCodeNames.rules B) Γ S.motiveType (.head t) :=
  piTop (toTop (U.toMotive U.codes.carrier_typed')) hmt

/-- The step type is a type of motives, in the context `P R`. -/
theorem stepType_typed :
    Typed (S.toCodeNames.rules B) (.snoc (.snoc .nil S.motiveType) (S.relType S.carrier)) S.stepType
      (.head S.motive) := by
  have LC := U.codes
  let Θ2 : Ctx Head 2 := .snoc (.snoc .nil S.motiveType) (S.relType S.carrier)
  let Θx : Ctx Head 3 := .snoc Θ2 (liftClosed S.carrier)
  let Θy : Ctx Head 4 := .snoc Θx (liftClosed S.carrier)
  let rel : Tm Head 4 := S.codes.holdsOf (CodeNames.relOf (.var 2) (.var 0) (.var 1))
  let Z : Tm Head 3 := .pi (liftClosed S.carrier) (.pi rel (.app (.var 4) (.var 1)))
  have hP1 : Typed (S.toCodeNames.rules B) (.snoc .nil S.motiveType) (.var 0) S.motiveType := by
    simpa only [Signature.rename_motiveType] using
      CodeNames.Laws.var_zero (C := S.toCodeNames) (B := B) (Γ := .nil) (X := S.motiveType)
  have hP2 : Typed (S.toCodeNames.rules B) Θ2 (.var 1) S.motiveType := by
    have h := hP1.weaken (extension := S.relType S.carrier)
    simp only [Signature.rename_motiveType] at h
    exact h
  have hR2 : Typed (S.toCodeNames.rules B) Θ2 (.var 0) (S.relType S.carrier) := by
    simpa only [CodeNames.rename_relType] using
      CodeNames.Laws.var_zero (C := S.toCodeNames) (B := B) (Γ := .snoc .nil S.motiveType)
        (X := S.relType S.carrier)
  have hPx : Typed (S.toCodeNames.rules B) Θx (.var 2) S.motiveType := by
    have h := hP2.weaken (extension := liftClosed S.carrier)
    simp only [Signature.rename_motiveType] at h
    exact h
  have hRx := CodeNames.Laws.weaken_rel (E := liftClosed S.carrier) hR2
  have hxx : Typed (S.toCodeNames.rules B) Θx (.var 0) (liftClosed S.carrier) := CodeNames.Laws.var_carrier
  have hPy : Typed (S.toCodeNames.rules B) Θy (.var 3) S.motiveType := by
    have h := hPx.weaken (extension := liftClosed S.carrier)
    simp only [Signature.rename_motiveType] at h
    exact h
  have hRy := CodeNames.Laws.weaken_rel (E := liftClosed S.carrier) hRx
  have hxy := CodeNames.Laws.weaken_point (E := liftClosed S.carrier) hxx
  have hyy : Typed (S.toCodeNames.rules B) Θy (.var 0) (liftClosed S.carrier) := CodeNames.Laws.var_carrier
  simp only [Presentation.rename, wk, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at hRx hRy hxy
  have hRel : Typed (S.toCodeNames.rules B) Θy rel (.head S.codes.proofs) :=
    LC.holdsOf_typed (CodeNames.Laws.relOf_typed hRy hyy hxy)
  have hPr : Typed (S.toCodeNames.rules B) (.snoc Θy rel) (.var 4) S.motiveType := by
    have h := hPy.weaken (extension := rel)
    simp only [Signature.rename_motiveType] at h
    exact h
  have hyr : Typed (S.toCodeNames.rules B) (.snoc Θy rel) (.var 1) (liftClosed S.carrier) := by
    have h := hyy.weaken (extension := rel)
    simp only [rename_liftClosed] at h
    exact h
  have hZ : Typed (S.toCodeNames.rules B) Θx Z (.head S.motive) :=
    U.piMotive (U.toMotive LC.carrier_typed')
      (U.piMotive (U.toMotive hRel) (Signature.motiveApp_typed hPr hyr))
  have hPz : Typed (S.toCodeNames.rules B) (.snoc Θx Z) (.var 3) S.motiveType := by
    have h := hPx.weaken (extension := Z)
    simp only [Signature.rename_motiveType] at h
    exact h
  have hxz : Typed (S.toCodeNames.rules B) (.snoc Θx Z) (.var 1) (liftClosed S.carrier) := by
    have h := hxx.weaken (extension := Z)
    simp only [rename_liftClosed] at h
    exact h
  exact U.piMotive (U.toMotive LC.carrier_typed')
    (U.piMotive hZ (Signature.motiveApp_typed hPz hxz))

omit U in
/-- The variables of the recursor's telescope, at their types. -/
theorem telescope_vars :
    Typed (S.toCodeNames.rules B) S.recTelescope (.var 4) S.motiveType ∧
    Typed (S.toCodeNames.rules B) S.recTelescope (.var 3) (S.relType S.carrier) ∧
    Typed (S.toCodeNames.rules B) S.recTelescope (.var 2) (S.stepTypeOf (.var 4) (.var 3)) ∧
    Typed (S.toCodeNames.rules B) S.recTelescope (.var 1) (liftClosed S.carrier) ∧
    Typed (S.toCodeNames.rules B) S.recTelescope (.var 0) (S.codes.holdsOf (S.acc (.var 3) (.var 1))) := by
  have hP1 : Typed (S.toCodeNames.rules B) (.snoc .nil S.motiveType) (.var 0) S.motiveType := by
    have h := CodeNames.Laws.var_zero (C := S.toCodeNames) (B := B) (Γ := .nil)
      (X := S.motiveType)
    simp only [Signature.rename_motiveType] at h
    exact h
  have hR2 : Typed (S.toCodeNames.rules B) (.snoc (.snoc .nil S.motiveType) (S.relType S.carrier)) (.var 0)
      (S.relType S.carrier) := by
    have h := CodeNames.Laws.var_zero (C := S.toCodeNames) (B := B)
      (Γ := .snoc .nil S.motiveType) (X := S.relType S.carrier)
    simp only [CodeNames.rename_relType] at h
    exact h
  have hF3 := CodeNames.Laws.var_zero (C := S.toCodeNames) (B := B)
    (Γ := .snoc (.snoc .nil S.motiveType) (S.relType S.carrier)) (X := S.stepType)
  have ha4 := CodeNames.Laws.var_carrier (C := S.toCodeNames) (B := B) (A := S.carrier)
    (Γ := .snoc (.snoc (.snoc .nil S.motiveType) (S.relType S.carrier)) S.stepType)
  have hq5 := CodeNames.Laws.var_zero (C := S.toCodeNames) (B := B)
    (Γ := .snoc (.snoc (.snoc (.snoc .nil S.motiveType) (S.relType S.carrier)) S.stepType)
      (liftClosed S.carrier))
    (X := S.codes.holdsOf (S.acc (.var 2) (.var 0)))
  refine ⟨?_, ?_, ?_, ?_, hq5⟩
  · have h := (((hP1.weaken (extension := S.relType S.carrier)).weaken
      (extension := S.stepType)).weaken (extension := liftClosed S.carrier)).weaken
      (extension := S.codes.holdsOf (S.acc (.var 2) (.var 0)))
    simp only [Signature.rename_motiveType] at h
    exact h
  · have h := ((hR2.weaken (extension := S.stepType)).weaken
      (extension := liftClosed S.carrier)).weaken
      (extension := S.codes.holdsOf (S.acc (.var 2) (.var 0)))
    simp only [CodeNames.rename_relType] at h
    exact h
  · have h := (hF3.weaken (extension := liftClosed S.carrier)).weaken
      (extension := S.codes.holdsOf (S.acc (.var 2) (.var 0)))
    have e : rename wk (rename wk (rename wk S.stepType)) = S.stepTypeOf (.var 4) (.var 3) := by
      rw [← Signature.stepTypeOf_vars]
      simp only [Signature.rename_stepTypeOf, Presentation.rename]
      rfl
    rw [e] at h
    exact h
  · have h := ha4.weaken (extension := S.codes.holdsOf (S.acc (.var 2) (.var 0)))
    simp only [rename_liftClosed] at h
    exact h

/-- A body over the recursor's telescope, typed in a universe above the motives,
closes to a closed type of that universe. -/
theorem telescope_close {t : Head} (hmt : ∀ {k : Nat} {Δ : Ctx Head k},
      Typed (S.toCodeNames.rules B) Δ (.head S.motive) (.head t))
    (toTop : ∀ {k : Nat} {Δ : Ctx Head k} {X : Tm Head k},
      Typed (S.toCodeNames.rules B) Δ X (.head S.motive) → Typed (S.toCodeNames.rules B) Δ X (.head t))
    (piTop : ∀ {k : Nat} {Δ : Ctx Head k} {X : Tm Head k} {Y : Tm Head (k + 1)},
      Typed (S.toCodeNames.rules B) Δ X (.head t) → Typed (S.toCodeNames.rules B) (.snoc Δ X) Y (.head t) →
        Typed (S.toCodeNames.rules B) Δ (.pi X Y) (.head t))
    {body : Tm Head 5} (hbody : Typed (S.toCodeNames.rules B) S.recTelescope body (.head t)) :
    Typed (S.toCodeNames.rules B) .nil (closeType S.recTelescope body) (.head t) := by
  have LC := U.codes
  have hR4 : Typed (S.toCodeNames.rules B) (.snoc (.snoc (.snoc (.snoc .nil S.motiveType) (S.relType S.carrier))
      S.stepType) (liftClosed S.carrier)) (.var 2) (S.relType S.carrier) := by
    have hR2 := CodeNames.Laws.var_zero (C := S.toCodeNames) (B := B)
      (Γ := .snoc .nil S.motiveType) (X := S.relType S.carrier)
    have h := (hR2.weaken (extension := S.stepType)).weaken (extension := liftClosed S.carrier)
    simp only [CodeNames.rename_relType] at h
    exact h
  have ha4 := CodeNames.Laws.var_carrier (C := S.toCodeNames) (B := B) (A := S.carrier)
    (Γ := .snoc (.snoc (.snoc .nil S.motiveType) (S.relType S.carrier)) S.stepType)
  have f4 := piTop (toTop (U.toMotive (LC.holdsOf_typed (LC.acc_typed hR4 ha4)))) hbody
  have f3 := piTop (toTop (U.toMotive LC.carrier_typed')) f4
  have f2 := piTop (toTop U.stepType_typed) f3
  have f1 := piTop (toTop (U.toMotive LC.relType_typed)) f2
  exact piTop (U.motiveType_typed hmt toTop piTop) f1

/-- **The recursor's declared type is formed**, in a universe above the motives. -/
theorem recType_typed : ∃ t, (S.toCodeNames.rules B).isUniverse t ∧ Typed (S.toCodeNames.rules B) .nil S.recType (.head t) := by
  obtain ⟨t, ht, hmt, toTop, piTop⟩ := U.top_facts
  obtain ⟨hP, -, -, ha, -⟩ := telescope_vars
  exact ⟨t, ht, U.telescope_close hmt toTop piTop
    (toTop (Signature.motiveApp_typed hP ha))⟩

/-- The recursor is a typed constant of the extended package. -/
theorem recursor_typed (declared : (S.toCodeNames.rules B).constantType S.recursor = some S.recType) {n : Nat} {Γ : Ctx Head n} :
    Typed (S.toCodeNames.rules B) Γ (.const S.recursor) (liftClosed S.recType) := by
  obtain ⟨t, ht, hT⟩ := U.recType_typed
  exact .const declared hT ht

omit U in
/-- A typed substitution of the recursor's telescope. -/
theorem recTelescope_substMor {n : Nat} {Γ : Ctx Head n} {P R F a q : Tm Head n}
    (hP : Typed (S.toCodeNames.rules B) Γ P S.motiveType) (hR : Typed (S.toCodeNames.rules B) Γ R (S.relType S.carrier))
    (hF : Typed (S.toCodeNames.rules B) Γ F (S.stepTypeOf P R)) (ha : Typed (S.toCodeNames.rules B) Γ a (liftClosed S.carrier))
    (hq : Typed (S.toCodeNames.rules B) Γ q (S.codes.holdsOf (S.acc R a))) :
    SubstMor (S.toCodeNames.rules B) S.recTelescope Γ
      (consSub q (consSub a (consSub F (consSub R (consSub P (fun i => Fin.elim0 i)))))) := by
  refine Normalization.SubstMor.cons (Normalization.SubstMor.cons (Normalization.SubstMor.cons
    (Normalization.SubstMor.cons (Normalization.SubstMor.cons (fun i => Fin.elim0 i) ?_) ?_)
    hF) ?_) hq
  · simpa only [Signature.subst_motiveType] using hP
  · simpa only [CodeNames.subst_relType] using hR
  · simpa only [subst_liftClosed] using ha

omit U in
theorem recSpine_eq_applyClosed {n : Nat} (P R F a q : Tm Head n) :
    applyClosed S.recTelescope
        (consSub q (consSub a (consSub F (consSub R (consSub P (fun i => Fin.elim0 i))))))
        (.const S.recursor) = S.recSpine P R F a q := rfl

/-- **The recursor applied**: `rec P R F a q : P a`. -/
theorem rec_apply (declared : (S.toCodeNames.rules B).constantType S.recursor = some S.recType) {n : Nat} {Γ : Ctx Head n} {P R F a q : Tm Head n}
    (hP : Typed (S.toCodeNames.rules B) Γ P S.motiveType) (hR : Typed (S.toCodeNames.rules B) Γ R (S.relType S.carrier))
    (hF : Typed (S.toCodeNames.rules B) Γ F (S.stepTypeOf P R)) (ha : Typed (S.toCodeNames.rules B) Γ a (liftClosed S.carrier))
    (hq : Typed (S.toCodeNames.rules B) Γ q (S.codes.holdsOf (S.acc R a))) :
    Typed (S.toCodeNames.rules B) Γ (S.recSpine P R F a q) (.app P a) := by
  have h := Normalization.Typed.telescope_apply (recTelescope_substMor hP hR hF ha hq)
    (U.recursor_typed declared (Γ := Γ))
  exact h

/-- **One step of the unfolding is typed**:
`F a (λ y r. rec P R F y (inv R a q y r)) : P a`. -/
theorem unfolding_typed (declared : (S.toCodeNames.rules B).constantType S.recursor = some S.recType) {n : Nat} {Γ : Ctx Head n} {P R F a q : Tm Head n}
    (hP : Typed (S.toCodeNames.rules B) Γ P S.motiveType) (hR : Typed (S.toCodeNames.rules B) Γ R (S.relType S.carrier))
    (hF : Typed (S.toCodeNames.rules B) Γ F (S.stepTypeOf P R)) (ha : Typed (S.toCodeNames.rules B) Γ a (liftClosed S.carrier))
    (hq : Typed (S.toCodeNames.rules B) Γ q (S.codes.holdsOf (S.acc R a))) :
    Typed (S.toCodeNames.rules B) Γ (S.unfolding P R F a q) (.app P a) := by
  have LC := U.codes
  -- `F a : (Π y. holds (R y a) → P y) → P a`
  have hF' := hF
  rw [Signature.stepTypeOf_eq] at hF'
  have hFa := Derivable.appElim hF' ha
  simp only [inst0, Presentation.subst, subst_liftClosed, subst_liftSub_wk, subst_subst0_rename_wk,
    liftSub_zero, liftSub_one] at hFa
  -- the context `y r` of the recursive call
  let relY : Tm Head (n + 1) :=
    S.codes.holdsOf (CodeNames.relOf (rename wk R) (.var 0) (rename wk a))
  let Γy : Ctx Head (n + 1) := .snoc Γ (liftClosed S.carrier)
  let Γr : Ctx Head (n + 2) := .snoc Γy relY
  have wk2 : ∀ {t T : Tm Head n}, Typed (S.toCodeNames.rules B) Γ t T →
      Typed (S.toCodeNames.rules B) Γr (rename wk (rename wk t)) (rename wk (rename wk T)) :=
    fun h => (h.weaken (extension := liftClosed S.carrier)).weaken (extension := relY)
  have hP2 : Typed (S.toCodeNames.rules B) Γr (rename wk (rename wk P)) S.motiveType := by
    have h := wk2 hP
    simp only [Signature.rename_motiveType] at h
    exact h
  have hR2 : Typed (S.toCodeNames.rules B) Γr (rename wk (rename wk R)) (S.relType S.carrier) := by
    have h := wk2 hR
    simp only [CodeNames.rename_relType] at h
    exact h
  have hF2 : Typed (S.toCodeNames.rules B) Γr (rename wk (rename wk F))
      (S.stepTypeOf (rename wk (rename wk P)) (rename wk (rename wk R))) := by
    have h := wk2 hF
    simp only [Signature.rename_stepTypeOf] at h
    exact h
  have ha2 : Typed (S.toCodeNames.rules B) Γr (rename wk (rename wk a)) (liftClosed S.carrier) := by
    have h := wk2 ha
    simp only [rename_liftClosed] at h
    exact h
  have hq2 : Typed (S.toCodeNames.rules B) Γr (rename wk (rename wk q))
      (S.codes.holdsOf (S.acc (rename wk (rename wk R)) (rename wk (rename wk a)))) := by
    have h := wk2 hq
    simp only [Presentation.rename, CodeNames.rename_acc] at h
    exact h
  have hy : Typed (S.toCodeNames.rules B) Γr (.var 1) (liftClosed S.carrier) := by
    have h := (CodeNames.Laws.var_carrier (C := S.toCodeNames) (B := B)
      (A := S.carrier) (Γ := Γ)).weaken (extension := relY)
    simp only [rename_liftClosed] at h
    exact h
  have hr : Typed (S.toCodeNames.rules B) Γr (.var 0)
      (S.codes.holdsOf (CodeNames.relOf (rename wk (rename wk R)) (.var 1)
        (rename wk (rename wk a)))) := by
    exact CodeNames.Laws.var_zero (C := S.toCodeNames) (B := B) (Γ := Γy) (X := relY)
  -- `inv R a q y r : holds (acc R y)` and the recursive call
  have hinv := LC.inv_apply hR2 ha2 hq2
  have hinvY := LC.accBelow_elim hR2 ha2 hinv hy
  have hinvYR := LC.impElim (CodeNames.Laws.relOf_typed hR2 hy ha2) (LC.acc_typed hR2 hy) hinvY hr
  have call := U.rec_apply declared hP2 hR2 hF2 hy hinvYR
  -- the two abstractions, at the type of `F a`'s argument
  have hRel : Typed (S.toCodeNames.rules B) Γy relY (.head S.codes.proofs) := by
    have hR1 : Typed (S.toCodeNames.rules B) Γy (rename wk R) (S.relType S.carrier) :=
      CodeNames.Laws.weaken_rel (E := liftClosed S.carrier) hR
    have ha1 : Typed (S.toCodeNames.rules B) Γy (rename wk a) (liftClosed S.carrier) :=
      CodeNames.Laws.weaken_point (E := liftClosed S.carrier) ha
    exact LC.holdsOf_typed (CodeNames.Laws.relOf_typed hR1 CodeNames.Laws.var_carrier ha1)
  have hPy : Typed (S.toCodeNames.rules B) Γr (.app (rename wk (rename wk P)) (.var 1)) (.head S.motive) :=
    Signature.motiveApp_typed hP2 hy
  have hP1 : Typed (S.toCodeNames.rules B) Γy (rename wk P) S.motiveType := by
    have h := hP.weaken (extension := liftClosed S.carrier)
    simp only [Signature.rename_motiveType] at h
    exact h
  have formedInner : Typed (S.toCodeNames.rules B) Γy (.pi relY (.app (rename wk (rename wk P)) (.var 1)))
      (.head S.motive) := U.piMotive (U.toMotive hRel) hPy
  have formedOuter : Typed (S.toCodeNames.rules B) Γ (.pi (liftClosed S.carrier)
      (.pi relY (.app (rename wk (rename wk P)) (.var 1)))) (.head S.motive) :=
    U.piMotive (U.toMotive LC.carrier_typed') formedInner
  have lam2 := Derivable.lamIntro formedOuter U.motive_universe
    (Derivable.lamIntro formedInner U.motive_universe call)
  have result := Derivable.appElim hFa lam2
  simp only [inst0, Presentation.subst, subst_subst0_rename_wk] at result
  exact result

/-- **The unfolding's declared type is formed.** -/
theorem unfoldType_typed (declared : (S.toCodeNames.rules B).constantType S.recursor = some S.recType) :
    ∃ t, (S.toCodeNames.rules B).isUniverse t ∧ Typed (S.toCodeNames.rules B) .nil S.unfoldType (.head t) := by
  obtain ⟨t, ht, hmt, toTop, piTop⟩ := U.top_facts
  obtain ⟨hP, hR, hF, ha, hq⟩ := telescope_vars
  refine ⟨t, ht, U.telescope_close hmt toTop piTop (toTop ?_)⟩
  exact .idForm (Signature.motiveApp_typed hP ha) U.motive_universe
    (U.rec_apply declared hP hR hF ha hq) (U.unfolding_typed declared hP hR hF ha hq)

/-- The unfolding is a typed constant of the extended package. -/
theorem unfold_typed (declared : (S.toCodeNames.rules B).constantType S.recursor = some S.recType) (declaredU : (S.toCodeNames.rules B).constantType S.unfold = some S.unfoldType) {n : Nat} {Γ : Ctx Head n} :
    Typed (S.toCodeNames.rules B) Γ (.const S.unfold) (liftClosed S.unfoldType) := by
  obtain ⟨t, ht, hT⟩ := U.unfoldType_typed declared
  exact .const declaredU hT ht

/-- **The propositional unfolding applied**:
`unfold P R F a q : Id (P a) (rec P R F a q) (F a (λ y r. rec P R F y (inv R a q y r)))`. -/
theorem unfold_apply (declared : (S.toCodeNames.rules B).constantType S.recursor = some S.recType) (declaredU : (S.toCodeNames.rules B).constantType S.unfold = some S.unfoldType) {n : Nat} {Γ : Ctx Head n} {P R F a q : Tm Head n}
    (hP : Typed (S.toCodeNames.rules B) Γ P S.motiveType) (hR : Typed (S.toCodeNames.rules B) Γ R (S.relType S.carrier))
    (hF : Typed (S.toCodeNames.rules B) Γ F (S.stepTypeOf P R)) (ha : Typed (S.toCodeNames.rules B) Γ a (liftClosed S.carrier))
    (hq : Typed (S.toCodeNames.rules B) Γ q (S.codes.holdsOf (S.acc R a))) :
    Typed (S.toCodeNames.rules B) Γ (S.unfoldSpine P R F a q)
      (.id (.app P a) (S.recSpine P R F a q) (S.unfolding P R F a q)) := by
  have h := Normalization.Typed.telescope_apply (recTelescope_substMor hP hR hF ha hq)
    (U.unfold_typed declared declaredU (Γ := Γ))
  exact h

end Signature.Universes

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion
