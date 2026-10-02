import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion.Codes
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Constants

/-!
# Introduction and inversion of the accessibility code

Both are closed terms of the package, with no new constant and no new rule:

* `intro := λ R a h X s. s a (λ y r. h y r X s)`, of type
  `Π R a. holds (accBelow R a) → holds (acc R a)`;
* `inv := λ R a q. q (λ z. accBelow R z) (λ x i y r. intro R y (i y r))`, of type
  `Π R a. holds (acc R a) → holds (accBelow R a)`.

The inversion instantiates the impredicative quantifier of `acc R a` at the
predicate `λ z. accBelow R z`, which is progressive by the introduction rule.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion

open Presentation Presentation.TypedEquality Presentation.TypedEquality.Impredicative
open TelescopeAbstraction (closeType applyClosed)

variable {Head : Type}

namespace CodeNames

variable (C : CodeNames Head) (A : Tm Head 0)

/-- `λ R a h X s. s a (λ y r. h y r X s)`. -/
def introTerm : Tm Head 0 :=
  .lam (.lam (.lam (.lam (.lam (.app (.app (.var 0) (.var 3)) (.lam (.lam
    (.app (.app (.app (.app (.var 4) (.var 1)) (.var 0)) (.var 3)) (.var 2)))))))))

/-- The telescope `R : A → A → prop, a : A`. -/
def pointTelescope : Ctx Head 2 := .snoc (.snoc .nil (C.relType A)) (liftClosed A)

/-- The telescope `R, a, h : holds (accBelow R a)`. -/
def introTelescope : Ctx Head 3 :=
  .snoc (C.pointTelescope A) (C.codes.holdsOf (C.accBelow (.var 1) (.var 0)))

/-- The type of the introduction: `Π R a. holds (accBelow R a) → holds (acc R a)`. -/
def introType : Tm Head 0 :=
  closeType (C.introTelescope A) (C.codes.holdsOf (C.acc (.var 2) (.var 1)))

/-- `λ R a q. q (λ z. accBelow R z) (λ x i y r. intro R y (i y r))`. -/
def invTerm : Tm Head 0 :=
  .lam (.lam (.lam (.app (.app (.var 0) (.lam (C.accBelow (.var 3) (.var 0))))
    (.lam (.lam (.lam (.lam
      (.app (.app (.app (liftClosed (introTerm (Head := Head))) (.var 6)) (.var 1))
        (.app (.app (.var 2) (.var 1)) (.var 0))))))))))

/-- The telescope `R, a, q : holds (acc R a)`. -/
def invTelescope : Ctx Head 3 :=
  .snoc (C.pointTelescope A) (C.codes.holdsOf (C.acc (.var 1) (.var 0)))

/-- The type of the inversion: `Π R a. holds (acc R a) → holds (accBelow R a)`. -/
def invType : Tm Head 0 :=
  closeType (C.invTelescope A) (C.codes.holdsOf (C.accBelow (.var 2) (.var 1)))

end CodeNames

@[simp] theorem subst_subst0_rename_wk {n : Nat} (y t : Tm Head n) :
    subst (subst0 y) (rename wk t) = t :=
  inst0_rename_wk y t

namespace CodeNames.Laws

variable {C : CodeNames Head} {B : Rules Head} {A : Tm Head 0} (L : C.Laws B A)
include L

/-! ## Introduction and elimination of each builder -/

/-- Equal codes decode to equal types. -/
theorem equal_holdsOf {n : Nat} {Γ : Ctx Head n} {c c' : Tm Head n}
    (h : Equal (C.rules B) Γ c c' C.codes.propT) :
    Equal (C.rules B) Γ (C.codes.holdsOf c) (C.codes.holdsOf c') C.U :=
  .appCong (.refl L.holds_typed) h

/-- β under the decoder: `holds ((λ z. P) y) ≡ holds P[y]`. -/
theorem equal_holds_beta {n : Nat} {Γ : Ctx Head n} {T y : Tm Head n} {P : Tm Head (n + 1)}
    (hT : Typed (C.rules B) Γ T C.U) (hP : Typed (C.rules B) (.snoc Γ T) P C.codes.propT)
    (hy : Typed (C.rules B) Γ y T) :
    Equal (C.rules B) Γ (C.codes.holdsOf (.app (.lam P) y)) (C.codes.holdsOf (inst0 y P)) C.U :=
  L.equal_holdsOf (Derivable.betaPi (L.pi_typed hT L.prop_typed) L.proofs_universe hP hy)

theorem below_elim {n : Nat} {Γ : Ctx Head n} {R X x i y : Tm Head n}
    (hR : Typed (C.rules B) Γ R (C.relType A)) (hX : Typed (C.rules B) Γ X (C.predType A))
    (hx : Typed (C.rules B) Γ x (liftClosed A))
    (hi : Typed (C.rules B) Γ i (C.codes.holdsOf (C.below R X x)))
    (hy : Typed (C.rules B) Γ y (liftClosed A)) :
    Typed (C.rules B) Γ (.app i y)
      (C.codes.holdsOf (C.codes.impOf (CodeNames.relOf R y x) (.app X y))) := by
  have hR' : Typed (C.rules B) (.snoc Γ (liftClosed A)) (rename wk R) (C.relType A) := by
    simpa only [CodeNames.rename_relType] using hR.weaken (extension := liftClosed A)
  have hX' : Typed (C.rules B) (.snoc Γ (liftClosed A)) (rename wk X) (C.predType A) := by
    simpa only [CodeNames.rename_predType] using hX.weaken (extension := liftClosed A)
  have hx' : Typed (C.rules B) (.snoc Γ (liftClosed A)) (rename wk x) (liftClosed A) := by
    simpa only [rename_liftClosed] using hx.weaken (extension := liftClosed A)
  have h := L.pointElim (L.impOf_typed (relOf_typed hR' var_carrier hx')
    (predOf_typed hX' var_carrier)) hi hy
  simpa [inst0, Codes.impOf, Presentation.subst] using h

theorem below_intro {n : Nat} {Γ : Ctx Head n} {R X x : Tm Head n} {b : Tm Head (n + 1)}
    (hR : Typed (C.rules B) Γ R (C.relType A)) (hX : Typed (C.rules B) Γ X (C.predType A))
    (hx : Typed (C.rules B) Γ x (liftClosed A))
    (hb : Typed (C.rules B) (.snoc Γ (liftClosed A)) b
      (C.codes.holdsOf (C.codes.impOf (CodeNames.relOf (rename wk R) (.var 0) (rename wk x))
        (.app (rename wk X) (.var 0))))) :
    Typed (C.rules B) Γ (.lam b) (C.codes.holdsOf (C.below R X x)) := by
  have hR' : Typed (C.rules B) (.snoc Γ (liftClosed A)) (rename wk R) (C.relType A) := by
    simpa only [CodeNames.rename_relType] using hR.weaken (extension := liftClosed A)
  have hX' : Typed (C.rules B) (.snoc Γ (liftClosed A)) (rename wk X) (C.predType A) := by
    simpa only [CodeNames.rename_predType] using hX.weaken (extension := liftClosed A)
  have hx' : Typed (C.rules B) (.snoc Γ (liftClosed A)) (rename wk x) (liftClosed A) := by
    simpa only [rename_liftClosed] using hx.weaken (extension := liftClosed A)
  exact L.pointIntro (L.impOf_typed (relOf_typed hR' var_carrier hx')
    (predOf_typed hX' var_carrier)) hb

omit L in
/-- Weakening facts for the three parameters of the builders. -/
theorem weaken_rel {n : Nat} {Γ : Ctx Head n} {R E : Tm Head n}
    (hR : Typed (C.rules B) Γ R (C.relType A)) :
    Typed (C.rules B) (.snoc Γ E) (rename wk R) (C.relType A) := by
  simpa only [CodeNames.rename_relType] using hR.weaken (extension := E)

omit L in
theorem weaken_pred {n : Nat} {Γ : Ctx Head n} {X E : Tm Head n}
    (hX : Typed (C.rules B) Γ X (C.predType A)) :
    Typed (C.rules B) (.snoc Γ E) (rename wk X) (C.predType A) := by
  simpa only [CodeNames.rename_predType] using hX.weaken (extension := E)

omit L in
theorem weaken_point {n : Nat} {Γ : Ctx Head n} {x E : Tm Head n}
    (hx : Typed (C.rules B) Γ x (liftClosed A)) :
    Typed (C.rules B) (.snoc Γ E) (rename wk x) (liftClosed A) := by
  simpa only [rename_liftClosed] using hx.weaken (extension := E)

theorem progressive_elim {n : Nat} {Γ : Ctx Head n} {R X s x : Tm Head n}
    (hR : Typed (C.rules B) Γ R (C.relType A)) (hX : Typed (C.rules B) Γ X (C.predType A))
    (hs : Typed (C.rules B) Γ s (C.codes.holdsOf (C.progressive R X)))
    (hx : Typed (C.rules B) Γ x (liftClosed A)) :
    Typed (C.rules B) Γ (.app s x)
      (C.codes.holdsOf (C.codes.impOf (C.below R X x) (.app X x))) := by
  have hR' := weaken_rel (E := liftClosed A) hR
  have hX' := weaken_pred (E := liftClosed A) hX
  have h := L.pointElim (L.impOf_typed (L.below_typed hR' hX' var_carrier)
    (predOf_typed hX' var_carrier)) hs hx
  simpa [inst0, Codes.impOf, Presentation.subst] using h

theorem progressive_intro {n : Nat} {Γ : Ctx Head n} {R X : Tm Head n} {b : Tm Head (n + 1)}
    (hR : Typed (C.rules B) Γ R (C.relType A)) (hX : Typed (C.rules B) Γ X (C.predType A))
    (hb : Typed (C.rules B) (.snoc Γ (liftClosed A)) b
      (C.codes.holdsOf (C.codes.impOf (C.below (rename wk R) (rename wk X) (.var 0))
        (.app (rename wk X) (.var 0))))) :
    Typed (C.rules B) Γ (.lam b) (C.codes.holdsOf (C.progressive R X)) := by
  have hR' := weaken_rel (E := liftClosed A) hR
  have hX' := weaken_pred (E := liftClosed A) hX
  exact L.pointIntro (L.impOf_typed (L.below_typed hR' hX' var_carrier)
    (predOf_typed hX' var_carrier)) hb

theorem acc_elim {n : Nat} {Γ : Ctx Head n} {R a q X : Tm Head n}
    (hR : Typed (C.rules B) Γ R (C.relType A)) (ha : Typed (C.rules B) Γ a (liftClosed A))
    (hq : Typed (C.rules B) Γ q (C.codes.holdsOf (C.acc R a)))
    (hX : Typed (C.rules B) Γ X (C.predType A)) :
    Typed (C.rules B) Γ (.app q X)
      (C.codes.holdsOf (C.codes.impOf (C.progressive R X) (.app X a))) := by
  have hR' := weaken_rel (E := C.predType A) hR
  have ha' := weaken_point (E := C.predType A) ha
  have h := L.predicateElim (L.impOf_typed (L.progressive_typed hR' var_predicate)
    (predOf_typed var_predicate ha')) hq hX
  simpa [inst0, Codes.impOf, Presentation.subst] using h

theorem acc_intro {n : Nat} {Γ : Ctx Head n} {R a : Tm Head n} {b : Tm Head (n + 1)}
    (hR : Typed (C.rules B) Γ R (C.relType A)) (ha : Typed (C.rules B) Γ a (liftClosed A))
    (hb : Typed (C.rules B) (.snoc Γ (C.predType A)) b
      (C.codes.holdsOf (C.codes.impOf (C.progressive (rename wk R) (.var 0))
        (.app (.var 0) (rename wk a))))) :
    Typed (C.rules B) Γ (.lam b) (C.codes.holdsOf (C.acc R a)) := by
  have hR' := weaken_rel (E := C.predType A) hR
  have ha' := weaken_point (E := C.predType A) ha
  exact L.predicateIntro (L.impOf_typed (L.progressive_typed hR' var_predicate)
    (predOf_typed var_predicate ha')) hb

theorem accBelow_elim {n : Nat} {Γ : Ctx Head n} {R a h y : Tm Head n}
    (hR : Typed (C.rules B) Γ R (C.relType A)) (ha : Typed (C.rules B) Γ a (liftClosed A))
    (hh : Typed (C.rules B) Γ h (C.codes.holdsOf (C.accBelow R a)))
    (hy : Typed (C.rules B) Γ y (liftClosed A)) :
    Typed (C.rules B) Γ (.app h y)
      (C.codes.holdsOf (C.codes.impOf (CodeNames.relOf R y a) (C.acc R y))) := by
  have hR' := weaken_rel (E := liftClosed A) hR
  have ha' := weaken_point (E := liftClosed A) ha
  have h := L.pointElim (L.impOf_typed (relOf_typed hR' var_carrier ha')
    (L.acc_typed hR' var_carrier)) hh hy
  simpa [inst0, Codes.impOf, Presentation.subst] using h

theorem accBelow_intro {n : Nat} {Γ : Ctx Head n} {R a : Tm Head n} {b : Tm Head (n + 1)}
    (hR : Typed (C.rules B) Γ R (C.relType A)) (ha : Typed (C.rules B) Γ a (liftClosed A))
    (hb : Typed (C.rules B) (.snoc Γ (liftClosed A)) b
      (C.codes.holdsOf (C.codes.impOf (CodeNames.relOf (rename wk R) (.var 0) (rename wk a))
        (C.acc (rename wk R) (.var 0))))) :
    Typed (C.rules B) Γ (.lam b) (C.codes.holdsOf (C.accBelow R a)) := by
  have hR' := weaken_rel (E := liftClosed A) hR
  have ha' := weaken_point (E := liftClosed A) ha
  exact L.pointIntro (L.impOf_typed (relOf_typed hR' var_carrier ha')
    (L.acc_typed hR' var_carrier)) hb

/-! ## Variables of explicit contexts -/

omit L in
theorem var_weaken {n : Nat} {Γ : Ctx Head n} {E t T : Tm Head n}
    (h : Typed (C.rules B) Γ t T) : Typed (C.rules B) (.snoc Γ E) (rename wk t) (rename wk T) :=
  h.weaken

/-! ## The introduction rule -/

/-- **Introduction.** `λ R a h X s. s a (λ y r. h y r X s)` has type
`Π R a. holds (accBelow R a) → holds (acc R a)`. -/
theorem intro_typed :
    Typed (C.rules B) .nil (CodeNames.introTerm (Head := Head)) (C.introType A) := by
  -- the contexts, innermost last: R a h X s y r
  let Γ1 : Ctx Head 1 := .snoc .nil (C.relType A)
  let Γ2 : Ctx Head 2 := .snoc Γ1 (liftClosed A)
  let Γ3 : Ctx Head 3 := .snoc Γ2 (C.codes.holdsOf (C.accBelow (.var 1) (.var 0)))
  let Γ4 : Ctx Head 4 := .snoc Γ3 (C.predType A)
  let Γ5 : Ctx Head 5 := .snoc Γ4 (C.codes.holdsOf (C.progressive (.var 3) (.var 0)))
  let Γ6 : Ctx Head 6 := .snoc Γ5 (liftClosed A)
  have hR1 : Typed (C.rules B) Γ1 (.var 0) (C.relType A) := by
    simpa only [CodeNames.rename_relType] using
      var_zero (C := C) (B := B) (Γ := .nil) (X := C.relType A)
  have hR2 := weaken_rel (E := liftClosed A) hR1
  have ha2 : Typed (C.rules B) Γ2 (.var 0) (liftClosed A) := var_carrier
  have hR3 := weaken_rel (E := C.codes.holdsOf (C.accBelow (.var 1) (.var 0))) hR2
  have ha3 := weaken_point (E := C.codes.holdsOf (C.accBelow (.var 1) (.var 0))) ha2
  have hh3 := var_zero (C := C) (B := B) (Γ := Γ2)
    (X := C.codes.holdsOf (C.accBelow (.var 1) (.var 0)))
  have hR4 := weaken_rel (E := C.predType A) hR3
  have ha4 := weaken_point (E := C.predType A) ha3
  have hh4 := var_weaken (E := C.predType A) hh3
  have hX4 : Typed (C.rules B) Γ4 (.var 0) (C.predType A) := var_predicate
  have hR5 := weaken_rel (E := C.codes.holdsOf (C.progressive (.var 3) (.var 0))) hR4
  have ha5 := weaken_point (E := C.codes.holdsOf (C.progressive (.var 3) (.var 0))) ha4
  have hh5 := var_weaken (E := C.codes.holdsOf (C.progressive (.var 3) (.var 0))) hh4
  have hX5 := weaken_pred (E := C.codes.holdsOf (C.progressive (.var 3) (.var 0))) hX4
  have hs5 := var_zero (C := C) (B := B) (Γ := Γ4)
    (X := C.codes.holdsOf (C.progressive (.var 3) (.var 0)))
  have hR6 := weaken_rel (E := liftClosed A) hR5
  have ha6 := weaken_point (E := liftClosed A) ha5
  have hh6 := var_weaken (E := liftClosed A) hh5
  have hX6 := weaken_pred (E := liftClosed A) hX5
  have hs6 := var_weaken (E := liftClosed A) hs5
  have hy6 : Typed (C.rules B) Γ6 (.var 0) (liftClosed A) := var_carrier
  have hR7 := weaken_rel (E := C.codes.holdsOf (CodeNames.relOf (.var 5) (.var 0) (.var 4))) hR6
  have ha7 := weaken_point (E := C.codes.holdsOf (CodeNames.relOf (.var 5) (.var 0) (.var 4))) ha6
  have hh7 := var_weaken (E := C.codes.holdsOf (CodeNames.relOf (.var 5) (.var 0) (.var 4))) hh6
  have hX7 := weaken_pred (E := C.codes.holdsOf (CodeNames.relOf (.var 5) (.var 0) (.var 4))) hX6
  have hs7 := var_weaken (E := C.codes.holdsOf (CodeNames.relOf (.var 5) (.var 0) (.var 4))) hs6
  have hy7 := weaken_point (E := C.codes.holdsOf (CodeNames.relOf (.var 5) (.var 0) (.var 4))) hy6
  have hr7 := var_zero (C := C) (B := B) (Γ := Γ6)
    (X := C.codes.holdsOf (CodeNames.relOf (.var 5) (.var 0) (.var 4)))
  simp only [Presentation.rename, wk, Fin.reduceSucc, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, CodeNames.rename_accBelow, CodeNames.rename_progressive] at hR2 hR3 ha3 hh3 hR4 ha4 hh4 hR5 ha5 hh5 hX5 hs5 hR6 ha6 hh6 hX6 hs6 hR7 ha7 hh7 hX7 hs7 hy7 hr7
  -- `h y r X s : holds (X y)`
  have t1 := L.accBelow_elim hR7 ha7 hh7 hy7
  have t2 := L.impElim (relOf_typed hR7 hy7 ha7) (L.acc_typed hR7 hy7) t1 hr7
  have t3 := L.acc_elim hR7 hy7 t2 hX7
  have t4 := L.impElim (L.progressive_typed hR7 hX7) (predOf_typed hX7 hy7) t3 hs7
  -- `λ y r. h y r X s : holds (below R X a)`, at depth five
  have below5 := L.below_intro hR5 hX5 ha5
    (L.impIntro (relOf_typed hR6 hy6 ha6) (predOf_typed hX6 hy6) t4)
  -- `s a (λ y r. …) : holds (X a)`
  have u1 := L.progressive_elim hR5 hX5 hs5 ha5
  have u2 := L.impElim (L.below_typed hR5 hX5 ha5) (predOf_typed hX5 ha5) u1 below5
  -- `λ X s. … : holds (acc R a)`, at depth three
  have acc3 := L.acc_intro hR3 ha3
    (L.impIntro (L.progressive_typed hR4 hX4) (predOf_typed hX4 ha4) u2)
  -- the three outer abstractions
  have formed3 : Typed (C.rules B) Γ2
      (.pi (C.codes.holdsOf (C.accBelow (.var 1) (.var 0)))
        (C.codes.holdsOf (C.acc (.var 2) (.var 1)))) C.U :=
    L.pi_typed (L.holdsOf_typed (L.accBelow_typed hR2 ha2))
      (L.holdsOf_typed (L.acc_typed hR3 ha3))
  have formed2 : Typed (C.rules B) Γ1
      (.pi (liftClosed A) (.pi (C.codes.holdsOf (C.accBelow (.var 1) (.var 0)))
        (C.codes.holdsOf (C.acc (.var 2) (.var 1))))) C.U :=
    L.pi_typed L.carrier_typed' formed3
  have formed1 : Typed (C.rules B) .nil (C.introType A) C.U :=
    L.pi_typed L.relType_typed formed2
  exact .lamIntro formed1 L.proofs_universe (.lamIntro formed2 L.proofs_universe
    (.lamIntro formed3 L.proofs_universe acc3))

/-- The predicate `λ z. accBelow R z` over the carrier. -/
theorem accBelowPredicate_typed {n : Nat} {Γ : Ctx Head n} {R : Tm Head n}
    (hR : Typed (C.rules B) Γ R (C.relType A)) :
    Typed (C.rules B) Γ (.lam (C.accBelow (rename wk R) (.var 0))) (C.predType A) :=
  .lamIntro L.predType_typed L.proofs_universe
    (L.accBelow_typed (weaken_rel (E := liftClosed A) hR) var_carrier)

omit L in
/-- A substitution of the point telescope and one proof. -/
theorem pointProof_substMor {n : Nat} {Γ : Ctx Head n} {R a p : Tm Head n}
    {E : Tm Head 2} (hR : Typed (C.rules B) Γ R (C.relType A))
    (ha : Typed (C.rules B) Γ a (liftClosed A))
    (hp : Typed (C.rules B) Γ p (subst (consSub a (consSub R (fun i => Fin.elim0 i))) E)) :
    SubstMor (C.rules B) (.snoc (C.pointTelescope A) E) Γ
      (consSub p (consSub a (consSub R (fun i => Fin.elim0 i)))) := by
  refine Normalization.SubstMor.cons (Normalization.SubstMor.cons
    (Normalization.SubstMor.cons (fun i => Fin.elim0 i) ?_) ?_) hp
  · simpa only [CodeNames.subst_relType] using hR
  · simpa only [subst_liftClosed] using ha

/-- The introduction applied: from `h : holds (accBelow R a)`, `intro R a h : holds (acc R a)`. -/
theorem intro_apply {n : Nat} {Γ : Ctx Head n} {R a h : Tm Head n}
    (hR : Typed (C.rules B) Γ R (C.relType A)) (ha : Typed (C.rules B) Γ a (liftClosed A))
    (hh : Typed (C.rules B) Γ h (C.codes.holdsOf (C.accBelow R a))) :
    Typed (C.rules B) Γ (.app (.app (.app (liftClosed (CodeNames.introTerm (Head := Head))) R) a) h)
      (C.codes.holdsOf (C.acc R a)) := by
  have h := Normalization.Typed.telescope_apply (pointProof_substMor hR ha (E := C.codes.holdsOf (C.accBelow (.var 1) (.var 0)))
    hh) (Normalization.Typed.liftClosed (Δ := Γ) L.intro_typed)
  exact h

/-! ## The inversion rule -/

/-- **Inversion.** `λ R a q. q (λ z. accBelow R z) (λ x i y r. intro R y (i y r))` has type
`Π R a. holds (acc R a) → holds (accBelow R a)`. -/
theorem inv_typed :
    Typed (C.rules B) .nil (C.invTerm (Head := Head)) (C.invType A) := by
  let X3 : Tm Head 3 := .lam (C.accBelow (.var 3) (.var 0))
  let X4 : Tm Head 4 := .lam (C.accBelow (.var 4) (.var 0))
  let Γ1 : Ctx Head 1 := .snoc .nil (C.relType A)
  let Γ2 : Ctx Head 2 := .snoc Γ1 (liftClosed A)
  let Γ3 : Ctx Head 3 := .snoc Γ2 (C.codes.holdsOf (C.acc (.var 1) (.var 0)))
  let Γ4 : Ctx Head 4 := .snoc Γ3 (liftClosed A)
  let Γ5 : Ctx Head 5 := .snoc Γ4 (C.codes.holdsOf (C.below (.var 3) X4 (.var 0)))
  let Γ6 : Ctx Head 6 := .snoc Γ5 (liftClosed A)
  have hR1 : Typed (C.rules B) Γ1 (.var 0) (C.relType A) := by
    simpa only [CodeNames.rename_relType] using
      var_zero (C := C) (B := B) (Γ := .nil) (X := C.relType A)
  have hR2 := weaken_rel (E := liftClosed A) hR1
  have ha2 : Typed (C.rules B) Γ2 (.var 0) (liftClosed A) := var_carrier
  have hR3 := weaken_rel (E := C.codes.holdsOf (C.acc (.var 1) (.var 0))) hR2
  have ha3 := weaken_point (E := C.codes.holdsOf (C.acc (.var 1) (.var 0))) ha2
  have hq3 := var_zero (C := C) (B := B) (Γ := Γ2) (X := C.codes.holdsOf (C.acc (.var 1) (.var 0)))
  have hR4 := weaken_rel (E := liftClosed A) hR3
  have hx4 : Typed (C.rules B) Γ4 (.var 0) (liftClosed A) := var_carrier
  have hR5 := weaken_rel (E := C.codes.holdsOf (C.below (.var 3) X4 (.var 0))) hR4
  have hx5 := weaken_point (E := C.codes.holdsOf (C.below (.var 3) X4 (.var 0))) hx4
  have hi5 := var_zero (C := C) (B := B) (Γ := Γ4) (X := C.codes.holdsOf (C.below (.var 3) X4 (.var 0)))
  have hR6 := weaken_rel (E := liftClosed A) hR5
  have hx6 := weaken_point (E := liftClosed A) hx5
  have hi6 := var_weaken (E := liftClosed A) hi5
  have hy6 : Typed (C.rules B) Γ6 (.var 0) (liftClosed A) := var_carrier
  have hR7 := weaken_rel (E := C.codes.holdsOf (CodeNames.relOf (.var 5) (.var 0) (.var 2))) hR6
  have hx7 := weaken_point (E := C.codes.holdsOf (CodeNames.relOf (.var 5) (.var 0) (.var 2))) hx6
  have hi7 := var_weaken (E := C.codes.holdsOf (CodeNames.relOf (.var 5) (.var 0) (.var 2))) hi6
  have hy7 := weaken_point (E := C.codes.holdsOf (CodeNames.relOf (.var 5) (.var 0) (.var 2))) hy6
  have hr7 := var_zero (C := C) (B := B) (Γ := Γ6)
    (X := C.codes.holdsOf (CodeNames.relOf (.var 5) (.var 0) (.var 2)))
  simp only [Presentation.rename, wk, Fin.reduceSucc, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, CodeNames.rename_accBelow, CodeNames.rename_acc, CodeNames.rename_below, liftRen, Fin.cases_zero, X4] at hR2 hR3 ha3 hq3 hR4 hR5 hx5 hi5 hR6 hx6 hi6 hR7 hx7 hi7 hy7 hr7
  -- the predicate at depth seven, and `i y r : holds (accBelow R y)`
  have hX7 := L.accBelowPredicate_typed hR7
  simp only [Presentation.rename, wk, Fin.reduceSucc] at hX7
  have w1 := L.below_elim hR7 hX7 hx7 hi7 hy7
  have w2 := L.impElim (relOf_typed hR7 hy7 hx7) (predOf_typed hX7 hy7) w1 hr7
  have w3 := Derivable.conv w2 (L.equal_holds_beta L.carrier_typed'
    (L.accBelow_typed (weaken_rel (E := liftClosed A) hR7) var_carrier) hy7) L.proofs_universe
  simp only [inst0, CodeNames.subst_accBelow, Presentation.subst, subst0, Fin.cases_zero] at w3
  -- `intro R y (i y r) : holds (acc R y)`
  have body := L.intro_apply hR7 hy7 w3
  -- `λ y r. … : holds (accBelow R x)`, converted to `holds (X x)`
  have accBelow5 := L.accBelow_intro hR5 hx5
    (L.impIntro (relOf_typed hR6 hy6 hx6) (L.acc_typed hR6 hy6) body)
  have hX5 := L.accBelowPredicate_typed hR5
  have step5 := Derivable.conv accBelow5 (.symm (L.equal_holds_beta L.carrier_typed'
    (L.accBelow_typed (weaken_rel (E := liftClosed A) hR5) var_carrier) hx5)) L.proofs_universe
  simp only [Presentation.rename, wk, Fin.reduceSucc] at step5 hX5
  -- `λ x i y r. … : holds (progressive R X)`
  have hX4 := L.accBelowPredicate_typed hR4
  simp only [Presentation.rename, wk, Fin.reduceSucc] at hX4
  have prog3 := L.progressive_intro hR3 (L.accBelowPredicate_typed hR3)
    (L.impIntro (L.below_typed hR4 hX4 hx4) (predOf_typed hX4 hx4) step5)
  -- `q X (λ x i y r. …) : holds (X a)`, converted to `holds (accBelow R a)`
  have v1 := L.acc_elim hR3 ha3 hq3 (L.accBelowPredicate_typed hR3)
  have v2 := L.impElim (L.progressive_typed hR3 (L.accBelowPredicate_typed hR3))
    (predOf_typed (L.accBelowPredicate_typed hR3) ha3) v1 prog3
  have v3 := Derivable.conv v2 (L.equal_holds_beta L.carrier_typed'
    (L.accBelow_typed (weaken_rel (E := liftClosed A) hR3) var_carrier) ha3) L.proofs_universe
  simp only [inst0, CodeNames.subst_accBelow, Presentation.subst, subst0, Fin.cases_zero] at v3
  -- the three outer abstractions
  have formed3 : Typed (C.rules B) Γ2
      (.pi (C.codes.holdsOf (C.acc (.var 1) (.var 0)))
        (C.codes.holdsOf (C.accBelow (.var 2) (.var 1)))) C.U :=
    L.pi_typed (L.holdsOf_typed (L.acc_typed hR2 ha2))
      (L.holdsOf_typed (L.accBelow_typed hR3 ha3))
  have formed2 : Typed (C.rules B) Γ1
      (.pi (liftClosed A) (.pi (C.codes.holdsOf (C.acc (.var 1) (.var 0)))
        (C.codes.holdsOf (C.accBelow (.var 2) (.var 1))))) C.U :=
    L.pi_typed L.carrier_typed' formed3
  have formed1 : Typed (C.rules B) .nil (C.invType A) C.U :=
    L.pi_typed L.relType_typed formed2
  exact .lamIntro formed1 L.proofs_universe (.lamIntro formed2 L.proofs_universe
    (.lamIntro formed3 L.proofs_universe v3))

/-- The inversion applied: from `q : holds (acc R a)`, `inv R a q : holds (accBelow R a)`. -/
theorem inv_apply {n : Nat} {Γ : Ctx Head n} {R a q : Tm Head n}
    (hR : Typed (C.rules B) Γ R (C.relType A)) (ha : Typed (C.rules B) Γ a (liftClosed A))
    (hq : Typed (C.rules B) Γ q (C.codes.holdsOf (C.acc R a))) :
    Typed (C.rules B) Γ (.app (.app (.app (liftClosed (C.invTerm (Head := Head))) R) a) q)
      (C.codes.holdsOf (C.accBelow R a)) := by
  have h := Normalization.Typed.telescope_apply (pointProof_substMor hR ha (E := C.codes.holdsOf (C.acc (.var 1) (.var 0)))
    hq) (Normalization.Typed.liftClosed (Δ := Γ) L.inv_typed)
  exact h

end CodeNames.Laws

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion
