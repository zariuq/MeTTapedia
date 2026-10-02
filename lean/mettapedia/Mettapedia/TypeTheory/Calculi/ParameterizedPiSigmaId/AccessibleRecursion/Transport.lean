import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion.Formation

/-!
# Transport along an identity, in every package with the identity eliminator

A package `R` has the based identity eliminator `J` with carriers in a universe
`u` and motives in a universe `v` when `J` is declared at `elimType u v`, its
declared type is formed, and the universe of motives has a type above `u`
(`Eliminator`). For every such package:

* `J` applied to typed arguments has the motive at the endpoint and the path as
  its type (`Eliminator.j_apply`);
* transport of a proof of `B x` along a path `p : Id A x y`, through the motive
  `λ y p. B y`, is a proof of `B y` (`Eliminator.transport_typed`).

None of this depends on the recursor, so it holds in the guarded package, in the
unguarded one and in the strong variant alike: an eliminator persists into every
package that extends the package (`Eliminator.mono`) or contains it with more
root steps (`Eliminator.ofSub`).

**The positive transport control.** In the guarded package, over the recursor's
telescope `P R F a q`, a predicate `Q : P a → prop` and a proof
`h : holds (Q (rec P R F a q))`, transport of `h` along the propositional
unfolding `unfold P R F a q` proves the goal about the unfolded call,
`holds (Q (F a (λ y r. rec P R F y (inv R a q y r))))`
(`Signature.transport_goal`). The unfolding is the path of the transport, so the
equation is used: the proof term is `J (P a) (rec …) (λ y p. holds (Q y)) h
(F a …) (unfold P R F a q)`.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion

open Presentation Presentation.TypedEquality Presentation.TypedEquality.Impredicative
open Presentation.TypedEquality.Normalization (elimType elimTelescope elimBody)

variable {Head : Type}

/-! ## Terms -/

/-- The identity eliminator applied: `J A x M d y p`. -/
def jSpine (J : DeclName) {n : Nat} (A x M d y p : Tm Head n) : Tm Head n :=
  .app (.app (.app (.app (.app (.app (.const J) A) x) M) d) y) p

/-- The motive `λ y p. B y` of a transport in a family `B` over `y`; the path
is not used. -/
def transportMotive {n : Nat} (B : Tm Head (n + 1)) : Tm Head n :=
  .lam (.lam (rename wk B))

/-- Transport of `d : B x` along `p : Id A x y`: `J A x (λ y p. B y) d y p`. -/
def transport (J : DeclName) {n : Nat} (A x y p : Tm Head n) (B : Tm Head (n + 1))
    (d : Tm Head n) : Tm Head n :=
  jSpine J A x (transportMotive B) d y p

@[simp] theorem rename_jSpine (J : DeclName) {n m : Nat} (ρ : Ren n m) (A x M d y p : Tm Head n) :
    rename ρ (jSpine J A x M d y p) =
      jSpine J (rename ρ A) (rename ρ x) (rename ρ M) (rename ρ d) (rename ρ y) (rename ρ p) :=
  rfl

@[simp] theorem subst_jSpine (J : DeclName) {n m : Nat} (σ : Sub Head n m) (A x M d y p : Tm Head n) :
    subst σ (jSpine J A x M d y p) =
      jSpine J (subst σ A) (subst σ x) (subst σ M) (subst σ d) (subst σ y) (subst σ p) :=
  rfl

/-- The type of a transport motive over `A` and `x`: `Π (y : A). Id A x y → U_v`. -/
def motiveIdType {n : Nat} (A x : Tm Head n) (v : Head) : Tm Head n :=
  .pi A (.pi (.id (rename wk A) (rename wk x) (.var 0)) (.head v))

/-- `M x (refl x)` and `M y p` of a transport motive are the family at the
endpoints: the motive ignores the path. -/
theorem inst0_subst_transportBody {n : Nat} (B : Tm Head (n + 1)) (y p : Tm Head n) :
    inst0 p (subst (liftSub (subst0 y)) (rename wk B)) = inst0 y B := by
  rw [subst_liftSub_wk, inst0_rename_wk]
  rfl

/-- The path type over `y`, opened at an endpoint. -/
theorem inst0_id_wk {n : Nat} (A x y : Tm Head n) :
    inst0 y (.id (rename wk A) (rename wk x) (.var 0)) = .id A x y := by
  simp only [inst0, Presentation.subst, subst_subst0_rename_wk]
  rfl

/-! ## Two β-steps -/

/-- Two β-steps at a function of two arguments `λ y p. B`. -/
theorem beta_two {R : Rules Head} {n : Nat} {Γ : Ctx Head n} {A y p : Tm Head n}
    {C : Tm Head (n + 1)} {B : Tm Head (n + 2)} {u w : Head} (hw : R.isUniverse w)
    (hPi : Typed R Γ (.pi A (.pi C (.head u))) (.head w))
    (hInner : Typed R (.snoc Γ A) (.pi C (.head u)) (.head w))
    (hB : Typed R (.snoc (.snoc Γ A) C) B (.head u))
    (hy : Typed R Γ y A) (hp : Typed R Γ p (inst0 y C)) :
    Equal R Γ (.app (.app (.lam (.lam B)) y) p)
      (inst0 p (subst (liftSub (subst0 y)) B)) (.head u) := by
  have e1 := Derivable.betaPi hPi hw (.lamIntro hInner hw hB) hy
  have e2 := Derivable.appCong e1 (.refl hp)
  have single := SubstMor.single hy
  have formed := hInner.substitute single
  have body := hB.substitute (single.lift C)
  have e3 := Derivable.betaPi formed hw body hp
  exact .trans e2 e3

/-! ## Packages with the identity eliminator -/

/-- The identity eliminator `J`, with carriers in `u` and motives in `v`,
declared in a package `R` at a formed type; `u` and `v` are universes and the
universe of motives has a type `w` into which functions from `u` to `w` fall. -/
structure Eliminator (R : Rules Head) (J : DeclName) (u v : Head) : Prop where
  declared : R.constantType J = some (elimType u v)
  formed : ∃ w, R.isUniverse w ∧ Typed R .nil (elimType u v) (.head w)
  carrier_universe : R.isUniverse u
  motive_universe : R.isUniverse v
  above : ∃ w, R.isUniverse w ∧ R.headTyping v w ∧ ∃ w', R.join u w w' ∧ R.cumulative w' w

namespace Eliminator

variable {R : Rules Head} {J : DeclName} {u v : Head} (E : Eliminator R J u v)
include E

theorem j_typed {n : Nat} {Γ : Ctx Head n} :
    Typed R Γ (.const J) (liftClosed (elimType u v)) := by
  obtain ⟨w, hw, typed⟩ := E.formed
  exact .const E.declared typed hw

/-- The type of transport motives is formed, in the type of the universe of
motives. -/
theorem motiveIdType_formed {n : Nat} {Γ : Ctx Head n} {A x : Tm Head n}
    (hA : Typed R Γ A (.head u)) (hx : Typed R Γ x A) :
    ∃ w, R.isUniverse w ∧
      Typed R (.snoc Γ A) (.pi (.id (rename wk A) (rename wk x) (.var 0)) (.head v)) (.head w) ∧
      Typed R Γ (motiveIdType A x v) (.head w) := by
  obtain ⟨w, hw, hv, w', hj, hc⟩ := E.above
  have hA' : Typed R (.snoc Γ A) (rename wk A) (.head u) := hA.weaken
  have hx' : Typed R (.snoc Γ A) (rename wk x) (rename wk A) := hx.weaken
  have hy : Typed R (.snoc Γ A) (.var 0) (rename wk A) := by
    simpa only [Ctx.lookup_snoc_zero] using Derivable.var (R := R) (Γ := .snoc Γ A) 0
  have hId : Typed R (.snoc Γ A) (.id (rename wk A) (rename wk x) (.var 0)) (.head u) :=
    .idForm hA' E.carrier_universe hx' hy
  have hHead : Typed R (.snoc (.snoc Γ A) (.id (rename wk A) (rename wk x) (.var 0)))
      (.head v) (.head w) := .headType hv
  have inner := Derivable.cumul (.piForm hId E.carrier_universe hHead hw hj) hc
  exact ⟨w, hw, inner, Derivable.cumul (.piForm hA E.carrier_universe inner hw hj) hc⟩

/-- **`J` applied**: `J A x M d y p : M y p`. -/
theorem j_apply {n : Nat} {Γ : Ctx Head n} {A x M d y p : Tm Head n}
    (hA : Typed R Γ A (.head u)) (hx : Typed R Γ x A)
    (hM : Typed R Γ M (motiveIdType A x v))
    (hd : Typed R Γ d (.app (.app M x) (.refl x)))
    (hy : Typed R Γ y A) (hp : Typed R Γ p (.id A x y)) :
    Typed R Γ (jSpine J A x M d y p) (.app (.app M y) p) := by
  have σ : SubstMor R (elimTelescope u v) Γ
      (consSub p (consSub y (consSub d (consSub M (consSub x (consSub A
        (fun i => Fin.elim0 i))))))) :=
    Normalization.SubstMor.cons (Normalization.SubstMor.cons (Normalization.SubstMor.cons
      (Normalization.SubstMor.cons (Normalization.SubstMor.cons (Normalization.SubstMor.cons
        (fun i => Fin.elim0 i) hA) hx) hM) hd) hy) hp
  exact Normalization.Typed.telescope_apply σ E.j_typed

/-- **Transport.** From `d : B x` and `p : Id A x y`, the transport of `d` along
`p` is a proof of `B y`. -/
theorem transport_typed {n : Nat} {Γ : Ctx Head n} {A x y p d : Tm Head n} {B : Tm Head (n + 1)}
    (hA : Typed R Γ A (.head u)) (hx : Typed R Γ x A) (hy : Typed R Γ y A)
    (hp : Typed R Γ p (.id A x y)) (hB : Typed R (.snoc Γ A) B (.head v))
    (hd : Typed R Γ d (inst0 x B)) :
    Typed R Γ (transport J A x y p B d) (inst0 y B) := by
  obtain ⟨w, hw, hInner, hPi⟩ := E.motiveIdType_formed hA hx
  have hBody : Typed R (.snoc (.snoc Γ A) (.id (rename wk A) (rename wk x) (.var 0)))
      (rename wk B) (.head v) := hB.weaken
  have hM : Typed R Γ (transportMotive B) (motiveIdType A x v) :=
    .lamIntro hPi hw (.lamIntro hInner hw hBody)
  have hrefl : Typed R Γ (.refl x) (inst0 x (.id (rename wk A) (rename wk x) (.var 0))) := by
    rw [inst0_id_wk]
    exact .reflIntro hx
  have eD := beta_two hw hPi hInner hBody hx hrefl
  rw [inst0_subst_transportBody] at eD
  have hd' : Typed R Γ d (.app (.app (transportMotive B) x) (.refl x)) :=
    .conv hd (.symm eD) E.motive_universe
  have hp' : Typed R Γ p (inst0 y (.id (rename wk A) (rename wk x) (.var 0))) := by
    rw [inst0_id_wk]
    exact hp
  have eR := beta_two hw hPi hInner hBody hy hp'
  rw [inst0_subst_transportBody] at eR
  exact .conv (E.j_apply hA hx hM hd' hy hp) eR E.motive_universe

end Eliminator

/-- An eliminator of a package is an eliminator of every package extending it. -/
theorem Eliminator.mono {R R' : Rules Head} {J : DeclName} {u v : Head}
    (E : Eliminator R J u v) (ext : Extends R R') : Eliminator R' J u v where
  declared := ext.constantType E.declared
  formed := by
    obtain ⟨w, hw, typed⟩ := E.formed
    exact ⟨w, by rw [ext.isUniverse]; exact hw, ext.derivable typed⟩
  carrier_universe := by rw [ext.isUniverse]; exact E.carrier_universe
  motive_universe := by rw [ext.isUniverse]; exact E.motive_universe
  above := by rw [ext.isUniverse, ext.headTyping, ext.join, ext.cumulative]; exact E.above

/-- An eliminator of a package is an eliminator of every package containing it,
such as the strong variant, which adds root steps. -/
theorem Eliminator.ofSub {R R' : Rules Head} {J : DeclName} {u v : Head}
    (E : Eliminator R J u v) (sub : Normalization.RulesSub R R') : Eliminator R' J u v where
  declared := sub.constantType E.declared
  formed := by
    obtain ⟨w, hw, typed⟩ := E.formed
    exact ⟨w, sub.isUniverse hw, Normalization.Derivable.mono sub typed⟩
  carrier_universe := sub.isUniverse E.carrier_universe
  motive_universe := sub.isUniverse E.motive_universe
  above := by
    obtain ⟨w, hw, hv, w', hj, hc⟩ := E.above
    exact ⟨w, sub.isUniverse hw, sub.headTyping hv, w', sub.join hj, sub.cumulative hc⟩

/-! ## The positive transport control -/

namespace Signature

variable (S : Signature Head)

/-- The predicate `Q : P a → prop`, over the recursor's telescope. -/
def predicateType : Tm Head 5 := .pi (.app (.var 4) (.var 1)) S.codes.propT

/-- `holds (Q (rec P R F a q))`, over the telescope and `Q`. -/
def hypothesisType : Tm Head 6 :=
  S.codes.holdsOf (.app (.var 0) (S.recSpine (.var 5) (.var 4) (.var 3) (.var 2) (.var 1)))

/-- The context of the transport control: `P R F a q`, the predicate `Q`, and
`h : holds (Q (rec P R F a q))`. -/
def transportContext : Ctx Head 7 :=
  .snoc (.snoc S.recTelescope S.predicateType) S.hypothesisType

/-- The recursive call of the control, `rec P R F a q`, in its context. -/
def controlCall : Tm Head 7 := S.recSpine (.var 6) (.var 5) (.var 4) (.var 3) (.var 2)

/-- The unfolded call of the control, `F a (λ y r. rec P R F y (inv R a q y r))`. -/
def controlUnfolding : Tm Head 7 := S.unfolding (.var 6) (.var 5) (.var 4) (.var 3) (.var 2)

/-- The goal about the unfolded call: `holds (Q (F a (λ y r. …)))`. -/
def transportGoal : Tm Head 7 := S.codes.holdsOf (.app (.var 1) S.controlUnfolding)

/-- The family `y ↦ holds (Q y)` over `P a`. -/
def goalFamily : Tm Head 8 := S.codes.holdsOf (.app (.var 2) (.var 0))

/-- **The proof of the goal**: transport of `h` along `unfold P R F a q`. -/
def transportProof (J : DeclName) : Tm Head 7 :=
  transport J (.app (.var 6) (.var 3)) S.controlCall S.controlUnfolding
    (S.unfoldSpine (.var 6) (.var 5) (.var 4) (.var 3) (.var 2)) S.goalFamily (.var 0)

/-- The variables of the transport context, at their types. -/
theorem transportContext_vars {B : Rules Head} :
    Typed (S.toCodeNames.rules B) S.transportContext (.var 6) S.motiveType ∧
    Typed (S.toCodeNames.rules B) S.transportContext (.var 5) (S.relType S.carrier) ∧
    Typed (S.toCodeNames.rules B) S.transportContext (.var 4) (S.stepTypeOf (.var 6) (.var 5)) ∧
    Typed (S.toCodeNames.rules B) S.transportContext (.var 3) (liftClosed S.carrier) ∧
    Typed (S.toCodeNames.rules B) S.transportContext (.var 2)
      (S.codes.holdsOf (S.acc (.var 5) (.var 3))) ∧
    Typed (S.toCodeNames.rules B) S.transportContext (.var 1)
      (.pi (.app (.var 6) (.var 3)) S.codes.propT) ∧
    Typed (S.toCodeNames.rules B) S.transportContext (.var 0)
      (S.codes.holdsOf (.app (.var 1) S.controlCall)) := by
  obtain ⟨hP, hR, hF, ha, hq⟩ := Universes.telescope_vars (S := S) (B := B)
  have wk2 : ∀ {t T : Tm Head 5}, Typed (S.toCodeNames.rules B) S.recTelescope t T →
      Typed (S.toCodeNames.rules B) S.transportContext (rename wk (rename wk t))
        (rename wk (rename wk T)) :=
    fun h => (h.weaken (extension := S.predicateType)).weaken (extension := S.hypothesisType)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Signature.rename_motiveType, Presentation.rename, wk, Fin.reduceSucc] using wk2 hP
  · simpa only [CodeNames.rename_relType, Presentation.rename, wk, Fin.reduceSucc] using wk2 hR
  · simpa only [Signature.rename_stepTypeOf, Presentation.rename, wk, Fin.reduceSucc] using wk2 hF
  · simpa only [rename_liftClosed, Presentation.rename, wk, Fin.reduceSucc] using wk2 ha
  · simpa only [Presentation.rename, CodeNames.rename_acc, wk, Fin.reduceSucc] using wk2 hq
  · have h := (CodeNames.Laws.var_zero (C := S.toCodeNames) (B := B) (Γ := S.recTelescope)
      (X := S.predicateType)).weaken (extension := S.hypothesisType)
    simp only [predicateType, Presentation.rename, wk, Fin.reduceSucc, Fin.succ_zero_eq_one] at h
    exact h
  · have h := CodeNames.Laws.var_zero (C := S.toCodeNames) (B := B)
      (Γ := .snoc S.recTelescope S.predicateType) (X := S.hypothesisType)
    simp only [hypothesisType, recSpine, Presentation.rename, wk, Fin.reduceSucc,
      Fin.succ_zero_eq_one] at h
    exact h

/-- **Transport along the unfolding establishes the goal about the unfolded
call.** In the guarded package with the identity eliminator at the universe of
motives, `J (P a) (rec P R F a q) (λ y p. holds (Q y)) h (F a …) (unfold P R F a q)`
proves `holds (Q (F a (λ y r. rec P R F y (inv R a q y r))))` from
`h : holds (Q (rec P R F a q))`. -/
theorem transport_goal (L : S.Laws) {J : DeclName}
    (E : Eliminator S.rules J S.motive S.codes.proofs) :
    Typed S.rules S.transportContext (S.transportProof J) S.transportGoal := by
  have U : S.Universes S.accBase := L.universes.mono L.base_accBase
  have LC := U.codes
  obtain ⟨hP, hR, hF, ha, hq, hQ, hh⟩ := S.transportContext_vars (B := S.accBase)
  have declared := Signature.rules_constantType_recursor L
  have declaredU := Signature.rules_constantType_unfold L
  have hA : Typed S.rules S.transportContext (.app (.var 6) (.var 3)) (.head S.motive) :=
    Signature.motiveApp_typed hP ha
  have hx := U.rec_apply declared hP hR hF ha hq
  have hy := U.unfolding_typed declared hP hR hF ha hq
  have hp := U.unfold_apply declared declaredU hP hR hF ha hq
  have hB : Typed S.rules (.snoc S.transportContext (.app (.var 6) (.var 3))) S.goalFamily
      (.head S.codes.proofs) := by
    have hQ' := hQ.weaken (extension := .app (.var 6) (.var 3))
    have hv : Typed S.rules (.snoc S.transportContext (.app (.var 6) (.var 3))) (.var 0)
        (rename wk (.app (.var 6) (.var 3))) :=
      CodeNames.Laws.var_zero (C := S.toCodeNames) (B := S.accBase)
    have happ := Derivable.appElim hQ' hv
    exact LC.holdsOf_typed (by
      simpa only [Presentation.rename, inst0, Presentation.subst, wk, Fin.reduceSucc,
        Fin.succ_one_eq_two] using happ)
  have hd : Typed S.rules S.transportContext (.var 0) (inst0 S.controlCall S.goalFamily) := hh
  exact E.transport_typed hA hx hy hp hB hd

end Signature

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion
