import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion.Formation

/-!
# The unguarded recursor

The unguarded package drops the guard: the recursor and its unfolding take no
accessibility proof,

`rec : Π P R F a. P a`,
`unfold : Π P R F a. Id (P a) (rec P R F a) (F a (λ y r. rec P R F y))`.

Its declared types are formed (`recTypeU_typed`, `unfoldTypeU_typed`) and its
full applications are typed (`recU_apply`, `unfoldU_apply`). The Curry
derivation over it is in `Curry`.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion

open Presentation Presentation.TypedEquality Presentation.TypedEquality.Impredicative
open TelescopeAbstraction (closeType applyClosed)

variable {Head : Type}

namespace Signature

variable (S : Signature Head)

/-- The telescope `P R F a` of the unguarded recursor. -/
def recTelescopeU : Ctx Head 4 :=
  .snoc (.snoc (.snoc (.snoc .nil S.motiveType) (S.relType S.carrier)) S.stepType)
    (liftClosed S.carrier)

/-- The declared type of the unguarded recursor: `Π P R F a. P a`. -/
def recTypeU : Tm Head 0 := closeType S.recTelescopeU (.app (.var 3) (.var 0))

/-- `rec P R F a`. -/
def recSpineU {n : Nat} (P R F a : Tm Head n) : Tm Head n :=
  .app (.app (.app (.app (.const S.recursor) P) R) F) a

/-- `unfold P R F a`. -/
def unfoldSpineU {n : Nat} (P R F a : Tm Head n) : Tm Head n :=
  .app (.app (.app (.app (.const S.unfold) P) R) F) a

/-- The unguarded unfolding `F a (λ y r. rec P R F y)`. -/
def unfoldingU {n : Nat} (P R F a : Tm Head n) : Tm Head n :=
  .app (.app F a) (.lam (.lam
    (S.recSpineU (rename wk (rename wk P)) (rename wk (rename wk R)) (rename wk (rename wk F))
      (.var 1))))

/-- The declared type of the unguarded unfolding. -/
def unfoldTypeU : Tm Head 0 :=
  closeType S.recTelescopeU
    (.id (.app (.var 3) (.var 0)) (S.recSpineU (.var 3) (.var 2) (.var 1) (.var 0))
      (S.unfoldingU (.var 3) (.var 2) (.var 1) (.var 0)))

/-- The base package with the unguarded recursor and its unfolding declared. -/
def unguardedBase : Rules Head :=
  { S.base with
    constantType := fun c =>
      if c = S.recursor then some S.recTypeU
      else if c = S.unfold then some S.unfoldTypeU
      else S.base.constantType c }

/-- The base package with the unguarded recursor declared. -/
def unguardedRecBase : Rules Head :=
  { S.base with
    constantType := fun c => if c = S.recursor then some S.recTypeU else S.base.constantType c }

/-- The unguarded package: the base with the unguarded constants, and the codes. -/
abbrev unguardedRules : Rules Head := S.codes.extend S.unguardedBase

/-- The base with the unguarded recursor, and the codes. -/
abbrev unguardedRecRules : Rules Head := S.codes.extend S.unguardedRecBase

theorem Laws.base_unguardedRecBase {S : Signature Head} (L : S.Laws) :
    Extends S.base S.unguardedRecBase where
  headTyping := rfl
  isUniverse := rfl
  join := rfl
  cumulative := rfl
  headEq := rfl
  computation := rfl
  constantType := fun {c} {T} declared => by
    by_cases hr : c = S.recursor
    · subst hr
      rw [L.recursor_fresh.2] at declared
      cases declared
    · simpa [unguardedRecBase, hr] using declared

theorem Laws.unguardedRecBase_unguardedBase {S : Signature Head} (L : S.Laws) :
    Extends S.unguardedRecBase S.unguardedBase where
  headTyping := rfl
  isUniverse := rfl
  join := rfl
  cumulative := rfl
  headEq := rfl
  computation := rfl
  constantType := fun {c} {T} declared => by
    by_cases hr : c = S.recursor
    · subst hr
      simpa [unguardedRecBase, unguardedBase] using declared
    · by_cases hu : c = S.unfold
      · subst hu
        simp [unguardedRecBase, Ne.symm L.recursor_ne_unfold, L.unfold_fresh.2] at declared
      · simpa [unguardedRecBase, unguardedBase, hr, hu] using declared

theorem Laws.base_unguardedBase {S : Signature Head} (L : S.Laws) :
    Extends S.base S.unguardedBase :=
  L.base_unguardedRecBase.trans L.unguardedRecBase_unguardedBase

theorem unguardedRecRules_constantType_recursor {S : Signature Head} (L : S.Laws) :
    S.unguardedRecRules.constantType S.recursor = some S.recTypeU := by
  simp [Codes.extend, unguardedRecBase, L.recursor_fresh.1, Option.orElse]

theorem unguardedRules_constantType_recursor {S : Signature Head} (L : S.Laws) :
    S.unguardedRules.constantType S.recursor = some S.recTypeU := by
  simp [Codes.extend, unguardedBase, L.recursor_fresh.1, Option.orElse]

theorem unguardedRules_constantType_unfold {S : Signature Head} (L : S.Laws) :
    S.unguardedRules.constantType S.unfold = some S.unfoldTypeU := by
  simp [Codes.extend, unguardedBase, L.unfold_fresh.1, Option.orElse, Ne.symm L.recursor_ne_unfold]

end Signature

namespace Signature.Universes

variable {S : Signature Head} {B : Rules Head} (U : S.Universes B)
include U

omit U in
/-- The variables of the unguarded telescope, at their types. -/
theorem telescopeU_vars :
    Typed (S.toCodeNames.rules B) S.recTelescopeU (.var 3) S.motiveType ∧
    Typed (S.toCodeNames.rules B) S.recTelescopeU (.var 2) (S.relType S.carrier) ∧
    Typed (S.toCodeNames.rules B) S.recTelescopeU (.var 1) (S.stepTypeOf (.var 3) (.var 2)) ∧
    Typed (S.toCodeNames.rules B) S.recTelescopeU (.var 0) (liftClosed S.carrier) := by
  have hP1 : Typed (S.toCodeNames.rules B) (.snoc .nil S.motiveType) (.var 0) S.motiveType := by
    have h := CodeNames.Laws.var_zero (C := S.toCodeNames) (B := B) (Γ := .nil)
      (X := S.motiveType)
    simp only [Signature.rename_motiveType] at h
    exact h
  have hR2 : Typed (S.toCodeNames.rules B) (.snoc (.snoc .nil S.motiveType) (S.relType S.carrier))
      (.var 0) (S.relType S.carrier) := by
    have h := CodeNames.Laws.var_zero (C := S.toCodeNames) (B := B)
      (Γ := .snoc .nil S.motiveType) (X := S.relType S.carrier)
    simp only [CodeNames.rename_relType] at h
    exact h
  have hF3 := CodeNames.Laws.var_zero (C := S.toCodeNames) (B := B)
    (Γ := .snoc (.snoc .nil S.motiveType) (S.relType S.carrier)) (X := S.stepType)
  have ha4 := CodeNames.Laws.var_carrier (C := S.toCodeNames) (B := B) (A := S.carrier)
    (Γ := .snoc (.snoc (.snoc .nil S.motiveType) (S.relType S.carrier)) S.stepType)
  refine ⟨?_, ?_, ?_, ha4⟩
  · have h := ((hP1.weaken (extension := S.relType S.carrier)).weaken
      (extension := S.stepType)).weaken (extension := liftClosed S.carrier)
    simp only [Signature.rename_motiveType] at h
    exact h
  · have h := (hR2.weaken (extension := S.stepType)).weaken (extension := liftClosed S.carrier)
    simp only [CodeNames.rename_relType] at h
    exact h
  · have h := hF3.weaken (extension := liftClosed S.carrier)
    have e : rename wk (rename wk S.stepType) = S.stepTypeOf (.var 3) (.var 2) := by
      rw [← Signature.stepTypeOf_vars]
      simp only [Signature.rename_stepTypeOf, Presentation.rename]
      rfl
    rw [e] at h
    exact h

/-- A body over the unguarded telescope, typed in a universe above the motives,
closes to a closed type of that universe. -/
theorem telescopeU_close {t : Head} (hmt : ∀ {k : Nat} {Δ : Ctx Head k},
      Typed (S.toCodeNames.rules B) Δ (.head S.motive) (.head t))
    (toTop : ∀ {k : Nat} {Δ : Ctx Head k} {X : Tm Head k},
      Typed (S.toCodeNames.rules B) Δ X (.head S.motive) →
        Typed (S.toCodeNames.rules B) Δ X (.head t))
    (piTop : ∀ {k : Nat} {Δ : Ctx Head k} {X : Tm Head k} {Y : Tm Head (k + 1)},
      Typed (S.toCodeNames.rules B) Δ X (.head t) →
        Typed (S.toCodeNames.rules B) (.snoc Δ X) Y (.head t) →
        Typed (S.toCodeNames.rules B) Δ (.pi X Y) (.head t))
    {body : Tm Head 4} (hbody : Typed (S.toCodeNames.rules B) S.recTelescopeU body (.head t)) :
    Typed (S.toCodeNames.rules B) .nil (closeType S.recTelescopeU body) (.head t) := by
  have LC := U.codes
  have f3 := piTop (toTop (U.toMotive LC.carrier_typed')) hbody
  have f2 := piTop (toTop U.stepType_typed) f3
  have f1 := piTop (toTop (U.toMotive LC.relType_typed)) f2
  exact piTop (U.motiveType_typed hmt toTop piTop) f1

/-- **The unguarded recursor's declared type is formed.** -/
theorem recTypeU_typed :
    ∃ t, (S.toCodeNames.rules B).isUniverse t ∧
      Typed (S.toCodeNames.rules B) .nil S.recTypeU (.head t) := by
  obtain ⟨t, ht, hmt, toTop, piTop⟩ := U.top_facts
  obtain ⟨hP, -, -, ha⟩ := telescopeU_vars (S := S) (B := B)
  exact ⟨t, ht, U.telescopeU_close hmt toTop piTop (toTop (Signature.motiveApp_typed hP ha))⟩

omit U in
theorem recTelescopeU_substMor {n : Nat} {Γ : Ctx Head n} {P R F a : Tm Head n}
    (hP : Typed (S.toCodeNames.rules B) Γ P S.motiveType)
    (hR : Typed (S.toCodeNames.rules B) Γ R (S.relType S.carrier))
    (hF : Typed (S.toCodeNames.rules B) Γ F (S.stepTypeOf P R))
    (ha : Typed (S.toCodeNames.rules B) Γ a (liftClosed S.carrier)) :
    SubstMor (S.toCodeNames.rules B) S.recTelescopeU Γ
      (consSub a (consSub F (consSub R (consSub P (fun i => Fin.elim0 i))))) := by
  refine Normalization.SubstMor.cons (Normalization.SubstMor.cons (Normalization.SubstMor.cons
    (Normalization.SubstMor.cons (fun i => Fin.elim0 i) ?_) ?_) hF) ?_
  · simpa only [Signature.subst_motiveType] using hP
  · simpa only [CodeNames.subst_relType] using hR
  · simpa only [subst_liftClosed] using ha

/-- **The unguarded recursor applied**: `rec P R F a : P a`. -/
theorem recU_apply (declared : (S.toCodeNames.rules B).constantType S.recursor = some S.recTypeU)
    {n : Nat} {Γ : Ctx Head n} {P R F a : Tm Head n}
    (hP : Typed (S.toCodeNames.rules B) Γ P S.motiveType)
    (hR : Typed (S.toCodeNames.rules B) Γ R (S.relType S.carrier))
    (hF : Typed (S.toCodeNames.rules B) Γ F (S.stepTypeOf P R))
    (ha : Typed (S.toCodeNames.rules B) Γ a (liftClosed S.carrier)) :
    Typed (S.toCodeNames.rules B) Γ (S.recSpineU P R F a) (.app P a) := by
  obtain ⟨t, ht, hT⟩ := U.recTypeU_typed
  have hc : Typed (S.toCodeNames.rules B) Γ (.const S.recursor) (liftClosed S.recTypeU) :=
    .const declared hT ht
  exact Normalization.Typed.telescope_apply (recTelescopeU_substMor hP hR hF ha) hc

/-- **One step of the unguarded unfolding is typed**:
`F a (λ y r. rec P R F y) : P a`. -/
theorem unfoldingU_typed
    (declared : (S.toCodeNames.rules B).constantType S.recursor = some S.recTypeU)
    {n : Nat} {Γ : Ctx Head n} {P R F a : Tm Head n}
    (hP : Typed (S.toCodeNames.rules B) Γ P S.motiveType)
    (hR : Typed (S.toCodeNames.rules B) Γ R (S.relType S.carrier))
    (hF : Typed (S.toCodeNames.rules B) Γ F (S.stepTypeOf P R))
    (ha : Typed (S.toCodeNames.rules B) Γ a (liftClosed S.carrier)) :
    Typed (S.toCodeNames.rules B) Γ (S.unfoldingU P R F a) (.app P a) := by
  have LC := U.codes
  have hF' := hF
  rw [Signature.stepTypeOf_eq] at hF'
  have hFa := Derivable.appElim hF' ha
  simp only [inst0, Presentation.subst, subst_liftClosed, subst_liftSub_wk, subst_subst0_rename_wk,
    liftSub_zero, liftSub_one] at hFa
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
  have hy : Typed (S.toCodeNames.rules B) Γr (.var 1) (liftClosed S.carrier) := by
    have h := (CodeNames.Laws.var_carrier (C := S.toCodeNames) (B := B)
      (A := S.carrier) (Γ := Γ)).weaken (extension := relY)
    simp only [rename_liftClosed] at h
    exact h
  have call := U.recU_apply declared hP2 hR2 hF2 hy
  have hRel : Typed (S.toCodeNames.rules B) Γy relY (.head S.codes.proofs) := by
    have hR1 : Typed (S.toCodeNames.rules B) Γy (rename wk R) (S.relType S.carrier) :=
      CodeNames.Laws.weaken_rel (E := liftClosed S.carrier) hR
    have ha1 : Typed (S.toCodeNames.rules B) Γy (rename wk a) (liftClosed S.carrier) :=
      CodeNames.Laws.weaken_point (E := liftClosed S.carrier) ha
    exact LC.holdsOf_typed (CodeNames.Laws.relOf_typed hR1 CodeNames.Laws.var_carrier ha1)
  have hPy : Typed (S.toCodeNames.rules B) Γr (.app (rename wk (rename wk P)) (.var 1))
      (.head S.motive) := Signature.motiveApp_typed hP2 hy
  have formedInner : Typed (S.toCodeNames.rules B) Γy
      (.pi relY (.app (rename wk (rename wk P)) (.var 1))) (.head S.motive) :=
    U.piMotive (U.toMotive hRel) hPy
  have formedOuter : Typed (S.toCodeNames.rules B) Γ (.pi (liftClosed S.carrier)
      (.pi relY (.app (rename wk (rename wk P)) (.var 1)))) (.head S.motive) :=
    U.piMotive (U.toMotive LC.carrier_typed') formedInner
  have lam2 := Derivable.lamIntro formedOuter U.motive_universe
    (Derivable.lamIntro formedInner U.motive_universe call)
  have result := Derivable.appElim hFa lam2
  simp only [inst0, Presentation.subst, subst_subst0_rename_wk] at result
  exact result

/-- **The unguarded unfolding's declared type is formed.** -/
theorem unfoldTypeU_typed
    (declared : (S.toCodeNames.rules B).constantType S.recursor = some S.recTypeU) :
    ∃ t, (S.toCodeNames.rules B).isUniverse t ∧
      Typed (S.toCodeNames.rules B) .nil S.unfoldTypeU (.head t) := by
  obtain ⟨t, ht, hmt, toTop, piTop⟩ := U.top_facts
  obtain ⟨hP, hR, hF, ha⟩ := telescopeU_vars (S := S) (B := B)
  refine ⟨t, ht, U.telescopeU_close hmt toTop piTop (toTop ?_)⟩
  exact .idForm (Signature.motiveApp_typed hP ha) U.motive_universe
    (U.recU_apply declared hP hR hF ha) (U.unfoldingU_typed declared hP hR hF ha)

/-- **The unguarded unfolding applied**:
`unfold P R F a : Id (P a) (rec P R F a) (F a (λ y r. rec P R F y))`. -/
theorem unfoldU_apply
    (declared : (S.toCodeNames.rules B).constantType S.recursor = some S.recTypeU)
    (declaredU : (S.toCodeNames.rules B).constantType S.unfold = some S.unfoldTypeU)
    {n : Nat} {Γ : Ctx Head n} {P R F a : Tm Head n}
    (hP : Typed (S.toCodeNames.rules B) Γ P S.motiveType)
    (hR : Typed (S.toCodeNames.rules B) Γ R (S.relType S.carrier))
    (hF : Typed (S.toCodeNames.rules B) Γ F (S.stepTypeOf P R))
    (ha : Typed (S.toCodeNames.rules B) Γ a (liftClosed S.carrier)) :
    Typed (S.toCodeNames.rules B) Γ (S.unfoldSpineU P R F a)
      (.id (.app P a) (S.recSpineU P R F a) (S.unfoldingU P R F a)) := by
  obtain ⟨t, ht, hT⟩ := U.unfoldTypeU_typed declared
  have hc : Typed (S.toCodeNames.rules B) Γ (.const S.unfold) (liftClosed S.unfoldTypeU) :=
    .const declaredU hT ht
  exact Normalization.Typed.telescope_apply (recTelescopeU_substMor hP hR hF ha) hc

end Signature.Universes

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion
