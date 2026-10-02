import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion.Formation
import Mettapedia.Order.AccessibilityCode
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.Fundamental
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.CodeConstants
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.Binders

/-!
# The accessibility package in the consistency model

The consistency model reads a code by its truth value, with Girard's clause for
the quantifiers: a quantifier ranges over all meanings at its carrier. Read
there, the accessibility code is the second-order encoding of accessibility,
`Mettapedia.Order.AccCode` (`truth_acc`), which is Lean's `Acc`
(`Mettapedia.Order.accCode_iff_acc`).

A model that computes the recursor by its unfolding makes the recursor a valid
term of its declared type: related arguments give related results, by
induction on the accessibility of the meaning of the point (`recursor_valid`).
The model's reduction unfolds the recursor at every accessibility proof; the
package does not. The propositional unfolding is then valid as well
(`unfold_valid`), and a base package sound for the model stays sound once the
two constants are declared (`sound_rules`). So the extended package derives no
closed proof of a false code (`consistent`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion

open Presentation Presentation.TypedEquality Presentation.TypedEquality.Impredicative
open Presentation.TypedEquality.Impredicative.Consistency
open Presentation.TypedEquality.Normalization (WhRed WhStep inst0_rename_subst_liftSub tailSub)
open TelescopeAbstraction (closeType applyClosed)
open UniverseLevel (LevelOrder)
open Mettapedia.Order (AccCode accCode_of_acc acc_of_accCode)

variable {Head L : Type} [LevelOrder L]

/-! ## The carrier in the model -/

/-- The model reads the carrier as a generic carrier `Ac`, with the quantifier
instances over `Ac` and over its predicates, and the package's implication is
the model's. -/
structure CarrierRead (C : CodeNames Head) (M : Model Head L) (A : Tm Head 0)
    (Ac : Carrier .gen) : Prop where
  term : A = Ac.term M
  interpretable : Ac.Interpretable M
  point : M.allCarrier C.point = some ⟨.gen, Ac⟩
  predicate : M.allCarrier C.predicate = some ⟨.gen, .arr Ac .prop⟩
  imp : C.codes.imp = M.imp

variable {M : Model Head L} {C : CodeNames Head} {A : Tm Head 0} {Ac : Carrier .gen}

/-- A body under an abstraction, read at a fresh generic of each meaning. -/
theorem Read.lam_fresh {n : Nat} {ξ : World M.reading n} {body : Tm Head (n + 1)}
    {B : Carrier .gen} {A' : Carrier .gen} {φ : A'.V M.reading → B.V M.reading}
    (read : ∀ v : A'.V M.reading, Read M.reading (ξ.snoc ⟨A', v⟩) body B (φ v)) :
    Read M.reading ξ (.lam body) (.arr A' B) φ := by
  have h := Read.lam_gen (σ := ids) (body := body) (φ := φ) (ξ := ξ) (fun v => by
    rw [liftSub_ids, subst_ids]
    exact read v)
  rwa [subst_ids] at h

/-- A generic of a predicate applied to a point with a meaning. -/
theorem truth_generic_app {n : Nat} {ξ : World M.reading n} {i : Fin n} {a : Tm Head n}
    {ψ : Ac.V M.reading → Prop} (gen : ξ i = ⟨.arr Ac .prop, ψ⟩) {v : Ac.V M.reading}
    (readA : Read M.reading ξ a Ac v) : Truth M.reading ξ (.app (.var i) a) (ψ v) := by
  refine Truth.generic (i := i) (args := [a]) .refl ?_
  rw [gen]
  exact .arg readA .done

/-- **The meaning of the accessibility code** is the second-order encoding of
accessibility, for the meaning `φ` of the relation and `v` of the point. -/
theorem truth_acc (read : CarrierRead C M A Ac) {n : Nat} {ξ : World M.reading n}
    {R a : Tm Head n} {φ : Ac.V M.reading → Ac.V M.reading → Prop} {v : Ac.V M.reading}
    (readR : Read M.reading ξ R (.arr Ac (.arr Ac .prop)) φ)
    (readA : Read M.reading ξ a Ac v) :
    Truth M.reading ξ (C.acc R a) (AccCode φ v) := by
  unfold AccCode
  have imp : ∀ {m : Nat} (p q : Tm Head m),
      C.codes.impOf p q = .app (.app (.const M.imp) p) q := fun p q => by
    rw [Codes.impOf, read.imp]
  refine Truth.all read.predicate .refl (Read.lam_fresh fun ψ => .prop ?_)
  let ξ₁ := ξ.snoc ⟨.arr Ac .prop, ψ⟩
  have readR₁ : Read M.reading ξ₁ (rename wk R) (.arr Ac (.arr Ac .prop)) φ := readR.rename (Morph.wk ξ _)
  have readA₁ : Read M.reading ξ₁ (rename wk a) Ac v := readA.rename (Morph.wk ξ _)
  rw [imp]
  refine Truth.imp .refl ?_ (truth_generic_app rfl readA₁)
  -- the progressive premise
  refine Truth.all read.point .refl (Read.lam_fresh fun x => .prop ?_)
  let ξ₂ := ξ₁.snoc ⟨Ac, x⟩
  have readR₂ : Read M.reading ξ₂ (rename wk (rename wk R)) (.arr Ac (.arr Ac .prop)) φ := readR₁.rename (Morph.wk ξ₁ _)
  have readX₂ : Read M.reading ξ₂ (.var 0) Ac x := Read.generic' ξ₂ rfl
  rw [imp]
  refine Truth.imp .refl ?_ (truth_generic_app rfl readX₂)
  -- the premise below `x`
  refine Truth.all read.point .refl (Read.lam_fresh fun y => .prop ?_)
  let ξ₃ := ξ₂.snoc ⟨Ac, y⟩
  have readR₃ : Read M.reading ξ₃ (rename wk (rename wk (rename wk R))) (.arr Ac (.arr Ac .prop)) φ :=
    readR₂.rename (Morph.wk ξ₂ _)
  have readY₃ : Read M.reading ξ₃ (.var 0) Ac y := Read.generic' ξ₃ rfl
  have readX₃ : Read M.reading ξ₃ (.var 1) Ac x := readX₂.rename (Morph.wk ξ₂ _)
  rw [imp]
  have readRy : Read M.reading ξ₃ (.app (rename wk (rename wk (rename wk R))) (.var 0))
      (.arr Ac .prop) (φ y) := Read.app (A := Ac) (B := .arr Ac .prop) readR₃ readY₃
  have readRyx : Read M.reading ξ₃ (CodeNames.relOf (rename wk (rename wk (rename wk R)))
      (.var 0) (.var 1)) .prop (φ y x) := Read.app (A := Ac) (B := .prop) readRy readX₃
  exact Truth.imp .refl readRyx.prop_inv (truth_generic_app rfl readY₃)

/-! ## Denotations the recursor meets -/

section Denotations

variable (laws : M.Laws) (read : CarrierRead C M A Ac)
include laws read

/-- The carrier denotes the relation of a common meaning. -/
theorem den_carrier {n : Nat} {ξ : World M.reading n} {R : Rel Head n}
    (den : Den M ξ (liftClosed A) R) : R = Ac.rel M.reading ξ := by
  obtain ⟨l, interp⟩ := den
  rw [read.term] at interp
  exact InterpAt.deterministic laws interp (Carrier.interp_rel laws l read.interpretable ξ)

/-- Terms related at the carrier have one meaning. -/
theorem carrier_meaning {n : Nat} {ξ : World M.reading n} {R : Rel Head n}
    (den : Den M ξ (liftClosed A) R) {a a' : Tm Head n} (h : R a a') :
    ∃ v, Read M.reading ξ a Ac v ∧ Read M.reading ξ a' Ac v := by
  rw [den_carrier laws read den] at h
  exact h

end Denotations

/-- The type of relations is the carrier of relations, read as a type. -/
theorem relType_eq (codesProp : C.codes.prop = M.prop) (read : CarrierRead C M A Ac) {n : Nat} :
    (C.relType A : Tm Head n) = liftClosed ((Carrier.arr Ac (.arr Ac .prop)).term M) := by
  simp only [CodeNames.relType, Carrier.term, liftClosed, Presentation.rename, rename_comp,
    Codes.propT, codesProp, read.term]
  congr 2
  exact congrArg (fun ρ => rename ρ (Carrier.term M Ac)) (funext fun i => i.elim0)

/-- Terms related at the type of relations have one meaning. -/
theorem relation_meaning (laws : M.Laws) (codesProp : C.codes.prop = M.prop)
    (read : CarrierRead C M A Ac) {n : Nat} {ξ : World M.reading n} {R : Rel Head n}
    (den : Den M ξ (C.relType A) R) {r r' : Tm Head n} (h : R r r') :
    ∃ φ, Read M.reading ξ r (.arr Ac (.arr Ac .prop)) φ ∧
      Read M.reading ξ r' (.arr Ac (.arr Ac .prop)) φ := by
  obtain ⟨l, interp⟩ := den
  rw [relType_eq codesProp read] at interp
  have hA : (Carrier.arr Ac (.arr Ac .prop)).Interpretable M :=
    .arr read.interpretable (.arr read.interpretable .prop)
  rw [InterpAt.deterministic laws interp (Carrier.interp_rel laws l hA ξ)] at h
  exact h

/-- `holds c` of a code with a truth value relates every pair or none, as the
truth value says. -/
theorem den_holds (laws : M.Laws) (codesHolds : C.codes.holds = M.holds) {n : Nat}
    {ξ : World M.reading n} {c : Tm Head n} {X : Prop} (truth : Truth M.reading ξ c X)
    {R : Rel Head n} (den : Den M ξ (C.codes.holdsOf c) R) : R = fun _ _ => X := by
  obtain ⟨l, interp⟩ := den
  rw [Codes.holdsOf, codesHolds] at interp
  obtain ⟨e, -⟩ := InterpAt.holds_inv laws interp
  rw [e]
  funext _ _
  exact propext (Truth.holds_iff laws.reading truth)

/-- `holds c` is denoted when `c` has a truth value. -/
theorem den_holds_exists (laws : M.Laws) (codesHolds : C.codes.holds = M.holds) {n : Nat}
    {ξ : World M.reading n} {c : Tm Head n} {X : Prop} (truth : Truth M.reading ξ c X) :
    Den M ξ (C.codes.holdsOf c) (fun _ _ => X) := by
  refine ⟨LevelOrder.bot, ?_⟩
  rw [Codes.holdsOf, codesHolds]
  exact Interp.holds_of_truth laws .refl truth

/-- Abstractions are related at a dependent function type under related
substitutions when their bodies are related at every world reached by a
morphism, under the substitutions renamed and extended by related arguments. -/
theorem Den.pi_lam_at (laws : M.Laws) {n : Nat} {D : Tm Head n} {body body' B : Tm Head (n + 1)}
    {m : Nat} {ξ : World M.reading m} {σ σ' : Sub Head n m}
    (bodies : ∀ {k : Nat} {ξ' : World M.reading k} {ρ : Ren m k}, Morph ξ ξ' ρ →
      ∀ {a b : Tm Head k} {RA : Rel Head k},
        Den M ξ' (subst (fun i => rename ρ (σ i)) D) RA → RA a b →
        ∀ {R : Rel Head k}, Den M ξ' (subst (consSub a fun i => rename ρ (σ i)) B) R →
          R (subst (consSub a fun i => rename ρ (σ i)) body)
            (subst (consSub b fun i => rename ρ (σ' i)) body'))
    {R : Rel Head m} (den : Den M ξ (subst σ (.pi D B)) R) :
    R (subst σ (.lam body)) (subst σ' (.lam body')) := by
  obtain ⟨l, interp⟩ := den
  obtain ⟨P, rfl, domInterp, codInterp, -⟩ := InterpAt.pi_inv laws interp
  refine PiRel.rel_lam codInterp ?_
  intro k ξ' ρ w a b ha hab
  have domI := domInterp w
  have codI := codInterp w ha
  rw [rename_subst] at domI
  rw [inst0_rename_subst_liftSub] at codI
  rw [inst0_rename_subst_liftSub, inst0_rename_subst_liftSub]
  exact bodies w ⟨l, domI⟩ hab ⟨l, codI⟩

/-! ## The recursor in a model that computes it -/

/-- A model for the recursor: lawful, reading the codes and the carrier, and
computing the recursor by its unfolding at every argument, whatever the
accessibility proof. -/
structure ComputesRecursor (S : Signature Head) (M : Model Head L) (Ac : Carrier .gen) : Prop where
  laws : M.Laws
  codes : CodesRead M S.codes
  carrier : CarrierRead S.toCodeNames M S.carrier Ac
  step : ∀ {m : Nat} (P R F a q : Tm Head m),
    M.rules.computation.step (S.recSpine P R F a q) (S.unfolding P R F a q)

namespace Signature

variable (S : Signature Head)

/-- The recursive call `rec P R F y (inv R a q y r)` under the binders `y r`. -/
def callBody : Tm Head 7 :=
  S.recSpine (.var 6) (.var 5) (.var 4) (.var 1) (S.invSpine (.var 5) (.var 3) (.var 2) (.var 1) (.var 0))

/-- `holds (R y a)` under the binder `y`. -/
def callPremise : Tm Head 6 := S.codes.holdsOf (CodeNames.relOf (.var 4) (.var 0) (.var 2))

/-- `Π y. holds (R y a) → P y`, over the recursor's telescope. -/
def callType : Tm Head 5 :=
  .pi (liftClosed S.carrier) (.pi S.callPremise (.app (.var 6) (.var 1)))

theorem subst_invSpine {n m : Nat} (σ : Sub Head n m) (R a q y r : Tm Head n) :
    subst σ (S.invSpine R a q y r) =
      S.invSpine (subst σ R) (subst σ a) (subst σ q) (subst σ y) (subst σ r) := by
  simp only [invSpine, Presentation.subst, subst_liftClosed]

theorem subst_recSpine {n m : Nat} (σ : Sub Head n m) (P R F a q : Tm Head n) :
    subst σ (S.recSpine P R F a q) =
      S.recSpine (subst σ P) (subst σ R) (subst σ F) (subst σ a) (subst σ q) := by
  simp only [recSpine, Presentation.subst]

/-- The unfolding is the step function applied to the point and to the abstraction
of the recursive call. -/
theorem unfolding_eq_subst {m : Nat} (σ : Sub Head 5 m) :
    S.unfolding (σ 4) (σ 3) (σ 2) (σ 1) (σ 0) =
      .app (.app (σ 2) (σ 1)) (subst σ (.lam (.lam S.callBody))) := by
  simp only [unfolding, callBody, Presentation.subst, subst_recSpine, subst_invSpine]
  rfl

end Signature

variable {S : Signature Head}

/-- The recursor's claim at a meaning `v` of the point: under related
substitutions of its telescope whose relation means `φ` and whose point means
`v`, the recursor's applications are related at the motive. -/
def RecClaim (S : Signature Head) (M : Model Head L) (Ac : Carrier .gen)
    (φ : Ac.V M.reading → Ac.V M.reading → Prop) (v : Ac.V M.reading) : Prop :=
  ∀ {m : Nat} {ξ : World M.reading m} {σ σ' : Sub Head 5 m},
    EqSubst M S.recTelescope ξ σ σ' →
    Read M.reading ξ (σ 3) (.arr Ac (.arr Ac .prop)) φ → Read M.reading ξ (σ 1) Ac v →
    ∀ {Rel : Rel Head m}, Den M ξ (.app (σ 4) (σ 1)) Rel →
      Rel (S.recSpine (σ 4) (σ 3) (σ 2) (σ 1) (σ 0))
        (S.recSpine (σ' 4) (σ' 3) (σ' 2) (σ' 1) (σ' 0))

/-- **One step of the unfolding is related** at an accessible point, once the
recursor's claim holds below it. -/
theorem unfolding_rel_of (H : ComputesRecursor S M Ac)
    {φ : Ac.V M.reading → Ac.V M.reading → Prop} {v : Ac.V M.reading}
    (hacc : ∀ y, φ y v → Acc φ y) (ih : ∀ y, φ y v → RecClaim S M Ac φ y)
    {m : Nat} {ξ : World M.reading m} {σ σ' : Sub Head 5 m}
    (e : EqSubst M S.recTelescope ξ σ σ')
    (readR : Read M.reading ξ (σ 3) (.arr Ac (.arr Ac .prop)) φ)
    (readA : Read M.reading ξ (σ 1) Ac v) {Rel : Rel Head m}
    (den : Den M ξ (.app (σ 4) (σ 1)) Rel) :
    Rel (S.unfolding (σ 4) (σ 3) (σ 2) (σ 1) (σ 0))
      (S.unfolding (σ' 4) (σ' 3) (σ' 2) (σ' 1) (σ' 0)) := by
  have laws := H.laws
  have read := H.carrier
  rw [S.unfolding_eq_subst σ, S.unfolding_eq_subst σ']
  -- the step function and the point
  obtain ⟨RF, denF, hF⟩ := e.lookup 2
  obtain ⟨Ra, dena, ha⟩ := e.lookup 1
  have eF : subst σ (Ctx.lookup S.recTelescope 2) = S.stepTypeOf (σ 4) (σ 3) := by
    show subst σ (rename wk (rename wk (rename wk S.stepType))) = _
    simp only [subst_rename, Signature.stepTypeOf]
    congr 1
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases rfl (fun k => Fin.elim0 k) j
  rw [eF, Signature.stepTypeOf_eq] at denF
  have ea : subst σ (Ctx.lookup S.recTelescope 1) = liftClosed S.carrier := by
    show subst σ (rename wk (rename wk (liftClosed S.carrier))) = _
    simp only [rename_liftClosed, subst_liftClosed]
  rw [ea] at dena
  obtain ⟨v', readA₁, readA₁'⟩ := carrier_meaning laws read dena ha
  obtain rfl := Read.deterministic laws.reading readA₁ readA
  obtain ⟨RB, denB, hB⟩ := Den.pi_app_exists laws denF hF
    (fun {RA} denA => by
      rw [den_carrier laws read denA]
      exact ⟨v', readA₁, readA₁'⟩)
  -- the abstraction of the recursive call, at the type of the step's argument
  have eB : inst0 (σ 1) (.pi
      (.pi (liftClosed S.carrier)
        (.pi (S.codes.holdsOf (CodeNames.relOf (rename wk (rename wk (σ 3))) (.var 0) (.var 1)))
          (.app (rename wk (rename wk (rename wk (σ 4)))) (.var 1))))
      (.app (rename wk (rename wk (σ 4))) (.var 1))) =
      .pi (subst σ S.callType) (.app (rename wk (σ 4)) (rename wk (σ 1))) := by
    simp only [inst0, Presentation.subst, subst_liftClosed, subst_liftSub_wk,
      subst_subst0_rename_wk, liftSub_zero, liftSub_one, Signature.callType,
      Signature.callPremise, Codes.holdsOf, CodeNames.relOf]
    rfl
  rw [eB] at denB
  refine Den.pi_app laws denB hB ?_ (by
    show Den M ξ (inst0 _ (.app (rename wk (σ 4)) (rename wk (σ 1)))) Rel
    simpa only [inst0, Presentation.subst, subst_subst0_rename_wk] using den)
  intro RA denLam
  refine Den.pi_lam_at laws ?_ denLam
  -- the first binder: a point `y` related at the carrier
  intro k₁ ξ₁ ρ₁ w₁ y y' RY denY hy R₁ den₁
  have denY' : Den M ξ₁ (liftClosed S.carrier) RY := by
    simpa only [subst_liftClosed] using denY
  obtain ⟨vy, readY, readY'⟩ := carrier_meaning laws read denY' hy
  refine Den.pi_lam_at laws ?_ den₁
  -- the second binder: a proof `r` that `y` is below the point
  intro k₂ ξ₂ ρ₂ w₂ r r' RR denR hr R₂ den₂
  -- the meanings at the innermost world
  have readR₂ := (readR.rename w₁).rename w₂
  have readA₂ := (readA.rename w₁).rename w₂
  have readY₂ := readY.rename w₂
  have readY₂' := readY'.rename w₂
  have readRy : Read M.reading ξ₂ (.app (rename ρ₂ (rename ρ₁ (σ 3))) (rename ρ₂ y))
      (.arr Ac .prop) (φ vy) := Read.app (A := Ac) (B := .arr Ac .prop) readR₂ readY₂
  have readRya : Read M.reading ξ₂
      (CodeNames.relOf (rename ρ₂ (rename ρ₁ (σ 3))) (rename ρ₂ y) (rename ρ₂ (rename ρ₁ (σ 1))))
      .prop (φ vy v') := Read.app (A := Ac) (B := .prop) readRy readA₂
  have hφ : φ vy v' := by
    have e := den_holds laws (C := S.toCodeNames) (H.codes.holds) readRya.prop_inv
      (c := CodeNames.relOf (rename ρ₂ (rename ρ₁ (σ 3))) (rename ρ₂ y) (rename ρ₂ (rename ρ₁ (σ 1))))
      (R := RR) denR
    rw [e] at hr
    exact hr
  -- the telescope of the recursive call
  let σR : Sub Head 5 k₂ := fun i => rename ρ₂ (rename ρ₁ (σ i))
  let σR' : Sub Head 5 k₂ := fun i => rename ρ₂ (rename ρ₁ (σ' i))
  have eR : EqSubst M S.recTelescope ξ₂ σR σR' := (e.rename laws w₁).rename laws w₂
  have e3 := eR.1.1
  have truthQ := truth_acc read readR₂ readY₂
  have denQ := den_holds_exists laws (C := S.toCodeNames) (H.codes.holds) truthQ
  have hQ : AccCode φ vy := accCode_of_acc (hacc vy hφ)
  let inv : Tm Head k₂ := S.invSpine (rename ρ₂ (rename ρ₁ (σ 3))) (rename ρ₂ (rename ρ₁ (σ 1)))
    (rename ρ₂ (rename ρ₁ (σ 0))) (rename ρ₂ y) r
  let inv' : Tm Head k₂ := S.invSpine (rename ρ₂ (rename ρ₁ (σ' 3))) (rename ρ₂ (rename ρ₁ (σ' 1)))
    (rename ρ₂ (rename ρ₁ (σ' 0))) (rename ρ₂ y') r'
  have denCarrier : Den M ξ₂ (subst (tailSub (tailSub σR)) (liftClosed S.carrier))
      (Ac.rel M.reading ξ₂) := by
    refine ⟨LevelOrder.bot, ?_⟩
    rw [subst_liftClosed, read.term]
    exact Carrier.interp_rel laws LevelOrder.bot read.interpretable ξ₂
  have eY := EqSubst.cons (A := liftClosed S.carrier) (R := Ac.rel M.reading ξ₂) e3 denCarrier
    (a := rename ρ₂ y) (a' := rename ρ₂ y') ⟨vy, readY₂, readY₂'⟩
  have eτ : EqSubst M S.recTelescope ξ₂
      (consSub inv (consSub (rename ρ₂ y) (tailSub (tailSub σR))))
      (consSub inv' (consSub (rename ρ₂ y') (tailSub (tailSub σR')))) :=
    EqSubst.cons (A := S.codes.holdsOf (S.acc (.var 2) (.var 0)))
      (R := fun _ _ => AccCode φ vy)
      eY denQ hQ
  exact ih vy hφ eτ readR₂ readY₂ (Rel := R₂) den₂

/-- **The recursor in a model that computes it.** At every accessible meaning
`v` of the point, related arguments of the recursor's telescope give related
results. The accessibility proof is never inspected. -/
theorem rec_rel (H : ComputesRecursor S M Ac) {φ : Ac.V M.reading → Ac.V M.reading → Prop}
    (v : Ac.V M.reading) (acc : Acc φ v) : RecClaim S M Ac φ v := by
  induction acc with
  | intro v hacc ih =>
  intro m ξ σ σ' e readR readA Rel den
  exact Den.expandLeft den (.single (WhStep.root (H.step _ _ _ _ _)))
    (Den.expandRight den (.single (WhStep.root (H.step _ _ _ _ _)))
      (unfolding_rel_of H hacc ih e readR readA den))

/-- A root step of the model's own computation preserves meaning. -/
theorem rootSemantic_of_modelStep {n : Nat} {l r : Tm Head n}
    (step : M.rules.computation.step l r) : RootSemantic M l r := by
  intro Γ T validL validR
  refine ⟨validL, validR, fun {_ _ σ _} e {_} den => ?_⟩
  obtain ⟨_, relR⟩ := validR
  exact Den.expandLeft den
    (Relation.ReflTransGen.single (WhStep.root (M.rules.computation.substitute σ step))) (relR e den)

/-! ## Validity of the two constants -/

/-- Related arguments of the recursor's telescope give a meaning of the
relation, a meaning of the point, and the accessibility of that meaning. -/
theorem telescope_meanings (H : ComputesRecursor S M Ac) {m : Nat} {ξ : World M.reading m}
    {σ σ' : Sub Head 5 m} (e : EqSubst M S.recTelescope ξ σ σ') :
    ∃ (φ : Ac.V M.reading → Ac.V M.reading → Prop) (v : Ac.V M.reading),
      Read M.reading ξ (σ 3) (.arr Ac (.arr Ac .prop)) φ ∧ Read M.reading ξ (σ 1) Ac v ∧
        Acc φ v := by
  obtain ⟨RR, denR, hR⟩ := e.lookup 3
  obtain ⟨Ra, dena, ha⟩ := e.lookup 1
  obtain ⟨Rq, denq, hq⟩ := e.lookup 0
  have eR : subst σ (Ctx.lookup S.recTelescope 3) = S.relType S.carrier := by
    show subst σ (rename wk (rename wk (rename wk (rename wk (S.relType S.carrier))))) = _
    simp only [CodeNames.rename_relType, CodeNames.subst_relType]
  have ea : subst σ (Ctx.lookup S.recTelescope 1) = liftClosed S.carrier := by
    show subst σ (rename wk (rename wk (liftClosed S.carrier))) = _
    simp only [rename_liftClosed, subst_liftClosed]
  rw [eR] at denR
  rw [ea] at dena
  obtain ⟨φ, readR, -⟩ := relation_meaning H.laws H.codes.prop H.carrier denR hR
  obtain ⟨v, readA, -⟩ := carrier_meaning H.laws H.carrier dena ha
  have truth := truth_acc H.carrier readR readA
  have denq' : Den M ξ (S.codes.holdsOf (S.acc (σ 3) (σ 1))) Rq := denq
  rw [den_holds H.laws H.codes.holds truth denq'] at hq
  exact ⟨φ, v, readR, readA, acc_of_accCode hq⟩

/-- **The recursor is valid** in a model that computes it, when the base
package with codes is sound for the model. -/
theorem recursor_valid (H : ComputesRecursor S M Ac) (U : S.Universes S.base)
    (sound : Sound S.baseRules M) : ValidTm M .nil (.const S.recursor) S.recType := by
  obtain ⟨t, ht, typed⟩ := U.recType_typed
  obtain ⟨validT, partsT, -⟩ := Derivable.valid sound typed trivial
  have validType : ValidTy M .nil S.recType := validT.validTy (sound.isUniverse ht)
  obtain ⟨-, validC, -⟩ := ValidTy.close_parts S.recTelescope validType partsT
  refine ValidTm.close H.laws S.recTelescope validType partsT ⟨validC, ?_⟩
  intro m ξ σ σ' e Rel den
  obtain ⟨φ, v, readR, readA, acc⟩ := telescope_meanings H e
  exact rec_rel H v acc e readR readA den

/-- A package sound for the model stays sound once a constant valid at its
declared type is declared. -/
theorem sound_declare {R R' : Rules Head} (sound : Sound R M) (ext : Extends R R')
    (fresh : ∀ {c : DeclName} {T : Tm Head 0}, R'.constantType c = some T →
      R.constantType c = some T ∨ ValidTm M .nil (.const c) T) : Sound R' M where
  laws := sound.laws
  headTyping := fun h => sound.headTyping (by rw [← ext.headTyping]; exact h)
  isUniverse := fun h => sound.isUniverse (by rw [← ext.isUniverse]; exact h)
  join := fun h => sound.join (by rw [← ext.join]; exact h)
  cumulative := fun h => sound.cumulative (by rw [← ext.cumulative]; exact h)
  headEq := fun h => sound.headEq (by rw [← ext.headEq]; exact h)
  root := fun step => sound.root (by rw [← ext.computation]; exact step)
  constants := fun declared => (fresh declared).elim sound.constants id

/-- The base package with codes and the recursor is sound for a model that
computes the recursor. -/
theorem sound_recRules (H : ComputesRecursor S M Ac) (L : S.Laws)
    (sound : Sound S.baseRules M) : Sound S.recRules M :=
  sound_declare sound (L.base_recBase.codes S.codes) fun {c} {T} declared => by
    by_cases hr : c = S.recursor
    · subst hr
      rw [Signature.recRules_constantType_recursor L] at declared
      cases declared
      exact .inr (recursor_valid H L.universes sound)
    · left
      simpa [Codes.extend, Signature.recBase, hr] using declared

/-- **The propositional unfolding is valid** in a model that computes the
recursor: the model's reduction takes the recursor's application to its
unfolding, and the unfolding is related to itself at the motive. -/
theorem unfold_valid (H : ComputesRecursor S M Ac) (L : S.Laws) (sound : Sound S.baseRules M) :
    ValidTm M .nil (.const S.unfold) S.unfoldType := by
  have soundRec := sound_recRules H L sound
  have U := L.universes.mono L.base_recBase
  obtain ⟨t, ht, typed⟩ := U.unfoldType_typed (Signature.recRules_constantType_recursor L)
  obtain ⟨validT, partsT, -⟩ := Derivable.valid soundRec typed trivial
  have validType : ValidTy M .nil S.unfoldType := validT.validTy (soundRec.isUniverse ht)
  obtain ⟨ctx, validC, -⟩ := ValidTy.close_parts S.recTelescope validType partsT
  refine ValidTm.close H.laws S.recTelescope validType partsT ⟨validC, ?_⟩
  intro m ξ σ σ' e Rel den
  obtain ⟨l, interp⟩ := den
  have interp' : InterpAt M l ξ (.id (.app (σ 4) (σ 1))
      (S.recSpine (σ 4) (σ 3) (σ 2) (σ 1) (σ 0)) (S.unfolding (σ 4) (σ 3) (σ 2) (σ 1) (σ 0)))
      Rel := interp
  obtain ⟨RA, rfl, interpA, -, -⟩ := InterpAt.id_inv H.laws interp'
  obtain ⟨φ, v, readR, readA, acc⟩ := telescope_meanings H e
  have eσ : EqSubst M S.recTelescope ξ σ σ := EqSubst.refl_left H.laws ctx.valid e
  have hU := unfolding_rel_of H (fun y h => acc.inv h) (fun y h => rec_rel H y (acc.inv h)) eσ
    readR readA ⟨l, interpA⟩
  exact Den.expandLeft ⟨l, interpA⟩ (.single (WhStep.root (H.step _ _ _ _ _))) hU

/-- **The extended package is sound** for a model that computes the recursor,
when the base package with codes is. -/
theorem sound_rules (H : ComputesRecursor S M Ac) (L : S.Laws) (sound : Sound S.baseRules M) :
    Sound S.rules M :=
  sound_declare (sound_recRules H L sound) (L.recBase_accBase.codes S.codes)
    fun {c} {T} declared => by
      by_cases hu : c = S.unfold
      · subst hu
        rw [Signature.rules_constantType_unfold L] at declared
        cases declared
        exact .inr (unfold_valid H L sound)
      · left
        simpa [Codes.extend, Signature.accBase, Signature.recBase, hu] using declared

/-- **Consistency of the extended package.** In a model that computes the
recursor and for which the base package with codes is sound, no closed term of
the extended package proves a closed code whose truth value is false. -/
theorem consistent (H : ComputesRecursor S M Ac) (L : S.Laws) (sound : Sound S.baseRules M)
    {c : Tm Head 0} {P : Prop} (truth : Truth M.reading World.closed c P) (false_ : ¬ P)
    (t : Tm Head 0) : ¬ Typed S.rules .nil t (S.codes.holdsOf c) := by
  rw [Codes.holdsOf, H.codes.holds]
  exact no_closed_proof (sound_rules H L sound) truth false_ t

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion
