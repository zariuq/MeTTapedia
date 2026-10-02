import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ConsistencyModel
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.Functions
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.Pairs
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.Comparison
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.Telescopes

/-!
# Identity elimination and the iterator in the consistency model

In the consistency model of the executable package, identity elimination and
the iterator are valid terms of their declared types, when those types are
valid with valid parts.

Identity elimination computes to its method on every path. In the model an
identity type relates terms only when its endpoints are related, so the motive
at the base point and reflexivity and the motive at the endpoint and a path are
related types of the motive's universe: both have the denotation of the
method's type.

The iterator computes by recursion on the numeral of its count. At zero it
returns the pair of its value and evidence, whose projections are related. At
a successor it applies the step once and continues with the projections of the
computed pair, which the relatedness of the step relates.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.Impredicative.Consistency
open TelescopeAbstraction (applyClosed)
open CertifiedTransforms (stepOver shared sharedBody step_application_type subst_stepOver)
open Package (jName iterName jType iterType iterApp iterPartial iterSucTelescope)

namespace CodeModel

/-! ## Denotations of type formers -/

section Formers

variable {M : Model Tower.Head ℕ} (laws : M.Laws)
include laws

/-- A motive of identity elimination, applied to the base point and reflexivity
and to a point related to it and any path, gives types with one
interpretation at the level of the motive's universe. -/
private theorem motive_same {n : Nat} {ξ : World M.reading n} {A x y f p : Tower.Tm n} {u : Tower.Head}
    (hu : M.rules.isUniverse u) {RF : Rel Tower.Head n} (denF : Den M ξ (motiveType A x u) RF)
    (hf : RF f f) (hxy : ∀ {RA : Rel Tower.Head n}, Den M ξ A RA → RA x y) :
    ∃ R, InterpAt M (M.levels.level u) ξ (.app (.app f x) (.refl x)) R ∧
      InterpAt M (M.levels.level u) ξ (.app (.app f y) p) R := by
  obtain ⟨R₁, den₁, h₁⟩ := Den.pi_app_exists laws denF hf hxy
  rw [inst0_motiveCod] at den₁
  obtain ⟨R₂, den₂, h₂⟩ := Den.pi_app_exists laws den₁ h₁ (fun denI => Den.id_diag laws denI _ _)
  rw [Den.sort_inv laws hu den₂] at h₂
  exact universeAt.den h₂

end Formers

/-! ## Identity elimination -/

/-- Identity elimination is a valid term of its declared type. -/
theorem valid_j (v : Nat → Nat) (validType : ValidTy (model v) .nil jType)
    (partsType : Structured (model v) .nil jType) :
    ValidTm (model v) .nil (.const jName) jType := by
  have laws := model_laws v
  rw [jType_eq] at validType partsType ⊢
  obtain ⟨_, validC, _⟩ := ValidTy.close_parts
    (elimTelescope (LevelTower.Head.sort Tower.zero) (LevelTower.Head.sort Tower.zero)) (C := elimBody) validType partsType
  refine ValidTm.close laws (elimTelescope (LevelTower.Head.sort Tower.zero) (LevelTower.Head.sort Tower.zero)) (C := elimBody)
    (f := .const jName) validType partsType ⟨validC, ?_⟩
  intro m ξ σ σ' e R den
  -- the full application computes to the method
  have red : ∀ τ : Sub Tower.Head 6 m, WhRed (model v).rules (model v).roles
      (Presentation.subst τ (applyClosed (elimTelescope (LevelTower.Head.sort Tower.zero) (LevelTower.Head.sort Tower.zero)) ids
        (liftClosed (.const jName)))) (τ 2) := fun τ =>
    .single (.root (model_step (modelListed 3 (by decide))
      ⟨τ 5, τ 4, τ 3, τ 2, τ 1, τ 0, rfl, rfl⟩))
  refine Den.expandLeft den (red σ) (Den.expandRight den (red σ') ?_)
  obtain ⟨⟨⟨⟨⟨⟨_, _, _, _⟩, _, _, _⟩, RP, denP, hP⟩, Rd, dend, hd⟩, _, _, _⟩, Rp, denp, hp⟩ := e
  change Den (model v) ξ (motiveType (σ 5) (σ 4) (.sort Tower.zero)) RP at denP
  change RP (σ 3) (σ' 3) at hP
  change Den (model v) ξ (.app (.app (σ 3) (σ 4)) (.refl (σ 4))) Rd at dend
  change Rd (σ 2) (σ' 2) at hd
  change Den (model v) ξ (.id (σ 5) (σ 4) (σ 1)) Rp at denp
  change Den (model v) ξ (.app (.app (σ 3) (σ 1)) (σ 0)) R at den
  obtain ⟨R', motiveBase, motiveEnd⟩ := motive_same laws (LevelTower.IsUniverse.sort Tower.zero) denP
    (Den.refl_left laws denP hP) (fun denA => Den.id_endpoints laws denp hp denA) (p := σ 0)
  rw [Den.deterministic laws den ⟨_, motiveEnd⟩]
  rw [Den.deterministic laws dend ⟨_, motiveBase⟩] at hd
  exact hd

/-! ## The iterator -/

/-- Reducing the count of an application of the iterator. -/
theorem iter_scrutinee (v : Nat → Nat) {n : Nat} (A P s x e : Tower.Tm n) {c c' : Tower.Tm n}
    (red : WhRed (model v).rules (model v).roles c c') :
    WhRed (model v).rules (model v).roles (iterApp c A P s x e) (iterApp c' A P s x e) := by
  induction red with
  | refl => exact .refl
  | tail _ step ih =>
      exact ih.tail (WhStep.scrutinee_single (c := iterName) (arity := 6) (before := [])
        (after := [A, P, s, x, e]) modelRoles_iter rfl step)

/-- The iterator at zero returns its value and evidence. -/
theorem iter_zero_step (v : Nat → Nat) {n : Nat} (A P s x e : Tower.Tm n) :
    WhStep (model v).rules (model v).roles (iterApp (.const zeroN) A P s x e) (.pair x e) := by
  have rule : equations.family
      (iterApp SetProfile.zeroNative (.var 4) (.var 3) (.var 2) (.var 1) (.var 0) : Tower.Tm 5)
      (.pair (.var 1) (.var 0)) :=
    equation_listed 12 (by decide) rfl
  exact .root (model_step_of_rules
    (equation_sound rule (consSub e (consSub x (consSub s (consSub P (consSub A Fin.elim0)))))))

/-- The iterator at a successor uses the step once and continues. -/
theorem iter_suc_step (v : Nat → Nat) {n : Nat} (a A P s x e : Tower.Tm n) :
    WhStep (model v).rules (model v).roles (iterApp (.app (.const sucN) a) A P s x e)
      (shared s (iterPartial a A P s) x e) := by
  have rule : equations.family
      (iterApp (SetProfile.sucNative (.var 5)) (.var 4) (.var 3) (.var 2) (.var 1) (.var 0) :
        Tower.Tm 6)
      (shared (.var 2) (iterPartial (.var 5) (.var 4) (.var 3) (.var 2)) (.var 1) (.var 0)) :=
    equation_listed 13 (by decide) rfl
  exact .root (model_step_of_rules (equation_sound rule
    (consSub e (consSub x (consSub s (consSub P (consSub A (consSub a Fin.elim0))))))))

/-- One shared use of a step reads both projections of the computed pair. -/
theorem shared_beta_step (v : Nat → Nat) {n : Nat} (k s x e : Tower.Tm n) :
    WhStep (model v).rules (model v).roles (shared s k x e)
      (.app (.app k (.fst (.app (.app s x) e))) (.snd (.app (.app s x) e))) := by
  have step := WhStep.beta (R := (model v).rules) (roles := (model v).roles) (sharedBody k)
    (.app (.app s x) e)
  have body : Presentation.inst0 (.app (.app s x) e) (sharedBody k) =
      .app (.app k (.fst (.app (.app s x) e))) (.snd (.app (.app s x) e)) := by
    show Tm.app (Tm.app (Presentation.inst0 (.app (.app s x) e) (Presentation.rename wk k))
      (.fst (.app (.app s x) e))) (.snd (.app (.app s x) e)) = _
    rw [inst0_rename_wk]
  rw [body] at step
  exact step

/-- A family applied to the newest variable, instantiated at a point. -/
private theorem inst0_family {n : Nat} (x P : Tower.Tm n) :
    Presentation.inst0 x (.app (Presentation.rename wk P) (.var 0)) = .app P x := by
  show Tm.app (Presentation.inst0 x (Presentation.rename wk P)) x = _
  rw [inst0_rename_wk]

/-- The iterator at counts with one numeral, related values and related
evidence gives related pairs. -/
theorem iter_related (v : Nat → Nat) {m : Nat} {ξ : World (model v).reading m} {A P s A' P' s' : Tower.Tm m}
    {R RS : Rel Tower.Head m}
    (den : Den (model v) ξ (.sigma A (.app (Presentation.rename wk P) (.var 0))) R)
    (denS : Den (model v) ξ (stepOver A (.app (Presentation.rename wk P) (.var 0))) RS)
    (hs : RS s s') (k : Nat) :
    ∀ {c c' x x' e e' : Tower.Tm m},
      NumVal (model v).toSetting c k → NumVal (model v).toSetting c' k →
      (∀ {RA : Rel Tower.Head m}, Den (model v) ξ A RA → RA x x') →
      (∀ {RE : Rel Tower.Head m}, Den (model v) ξ (.app P x) RE → RE e e') →
      R (iterApp c A P s x e) (iterApp c' A' P' s' x' e') := by
  have laws := model_laws v
  induction k with
  | zero =>
      intro c c' x x' e e' hc hc' hx he
      cases hc with
      | zero red =>
          cases hc' with
          | zero red' =>
              refine Den.expandLeft den
                (Relation.ReflTransGen.tail (iter_scrutinee v A P s x e red)
                  (iter_zero_step v A P s x e))
                (Den.expandRight den
                  (Relation.ReflTransGen.tail (iter_scrutinee v A' P' s' x' e' red')
                    (iter_zero_step v A' P' s' x' e')) ?_)
              exact Den.sigma_pair laws den hx
                (fun denB => he (by rwa [inst0_family] at denB))
  | succ k ih =>
      intro c c' x x' e e' hc hc' hx he
      cases hc with
      | @suc _ a _ red ha =>
          cases hc' with
          | @suc _ a' _ red' ha' =>
              -- the step at the value and its evidence
              obtain ⟨R₁, den₁, h₁⟩ := Den.pi_app_exists laws denS hs hx
              rw [step_application_type] at den₁
              obtain ⟨R₂, den₂, h₂⟩ := Den.pi_app_exists laws den₁ h₁
                (fun denE => he (by rwa [inst0_family] at denE))
              rw [inst0_rename_wk] at den₂
              rw [← Den.deterministic laws den den₂] at h₂
              refine Den.expandLeft den
                (Relation.ReflTransGen.tail
                  (Relation.ReflTransGen.tail (iter_scrutinee v A P s x e red)
                    (iter_suc_step v a A P s x e))
                  (shared_beta_step v (iterPartial a A P s) s x e))
                (Den.expandRight den
                  (Relation.ReflTransGen.tail
                    (Relation.ReflTransGen.tail (iter_scrutinee v A' P' s' x' e' red')
                      (iter_suc_step v a' A' P' s' x' e'))
                    (shared_beta_step v (iterPartial a' A' P' s') s' x' e')) ?_)
              exact ih ha ha' (fun denA => Den.sigma_fst laws den h₂ denA)
                (fun denE => Den.sigma_snd laws den h₂ (by rwa [inst0_family]))

/-- The iterator is a valid term of its declared type. -/
theorem valid_iter (v : Nat → Nat) (validType : ValidTy (model v) .nil iterType)
    (partsType : Structured (model v) .nil iterType) :
    ValidTm (model v) .nil (.const iterName) iterType := by
  have laws := model_laws v
  obtain ⟨_, validC, _⟩ := ValidTy.close_parts iterSucTelescope (C := iterResult)
    validType partsType
  refine ValidTm.close laws iterSucTelescope (C := iterResult) (f := .const iterName)
    validType partsType ⟨validC, ?_⟩
  intro m ξ σ σ' e R den
  obtain ⟨⟨⟨⟨⟨⟨_, RN, denN, hN⟩, _, _, _⟩, _, _, _⟩, RS, denS, hS⟩, RX, denX, hX⟩, RE, denE, hE⟩ :=
    e
  obtain rfl := Den.num_inv laws denN
  obtain ⟨k, hk, hk'⟩ := hN
  change Den (model v) ξ (Presentation.subst (tailSub (tailSub (tailSub σ)))
    (stepOver (.var 1) (.app (.var 1) (.var 0)))) RS at denS
  rw [subst_stepOver] at denS
  change Den (model v) ξ (stepOver (σ 4) (.app (Presentation.rename wk (σ 3)) (.var 0))) RS
    at denS
  change RS (σ 2) (σ' 2) at hS
  change Den (model v) ξ (σ 4) RX at denX
  change RX (σ 1) (σ' 1) at hX
  change Den (model v) ξ (.app (σ 3) (σ 1)) RE at denE
  change Den (model v) ξ (.sigma (σ 4) (.app (Presentation.rename wk (σ 3)) (.var 0))) R at den
  change NumVal (model v).toSetting (σ 5) k at hk
  change NumVal (model v).toSetting (σ' 5) k at hk'
  show R (iterApp (σ 5) (σ 4) (σ 3) (σ 2) (σ 1) (σ 0))
    (iterApp (σ' 5) (σ' 4) (σ' 3) (σ' 2) (σ' 1) (σ' 0))
  exact iter_related v den denS hS k hk hk'
    (fun denA => by rw [Den.deterministic laws denA denX]; exact hX)
    (fun denA => by rw [Den.deterministic laws denA denE]; exact hE)

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
