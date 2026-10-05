import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ConvArithmetic

/-!
# The iterator in the conversion model

The iterator `iter n A P step x e` computes by recursion on its count, on the
value side and on the realizer side alike: at `zero` it pairs its value with
its evidence, and at `suc m` it makes one shared use of the step, then iterates
`m` times from the projections of the computed pair. It is a valid term of its
declared type (`valid_iter`):

* **Values**, by induction on the common shape of two related counts: at zero
  the pairs of the values and the evidence are related, at a successor the step
  relates the computed pairs and so their projections, and at the daimon both
  applications are daimonic (`iter_related`).
* **Realizers**, by induction on the shape of the count, read from the count's
  realizers: realizers reaching neutral terms make both applications reach
  neutral spines; reaching `zero`, both compute to pairs of the realizers of
  the value and of the evidence; reaching `suc`, both compute, through the
  shared use of the step, to the iterator at the predecessors' realizers and at
  the projections of the step's realizers applied to the realizers, which
  realize the projections of the computed pair. These reductions are typed by
  the typings of their two sides: the count's reduction by congruence
  (`iter_scrutinee_red`), the computation at zero (`iter_zero_red`), and at a
  successor the shared use of the step and its contraction, typed in the
  iterator's telescope and then instantiated (`iter_suc_red`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization hiding World
open Presentation.TypedEquality.Impredicative
open Presentation.TypedEquality.Impredicative.Conversion
open Presentation.TypedEquality.Impredicative.Consistency (World Morph)
open Presentation.TypedEquality.Impredicative.Realizability (HasShape Daimonic)
open StrongNormalization (NumShape)
open CertifiedTransforms (stepOver shared sharedBody step_application_type subst_stepOver)
open SetProfile (zeroNative sucNative)
open Package (U0 numT iterName iterType iterApp iterPartial stepFamily)

namespace CodeModel
namespace ConvRules

/-! ## The iterator on the realizer side -/

/-- The iterator at its declared type in the executable package. -/
theorem rules_iter_typed {n : Nat} {Γ : Tower.Ctx n} :
    Typed rules Γ (.const iterName) (liftClosed iterType) := by
  have declared : rules.constantType iterName = some iterType := by decide
  exact .const declared (Derivable.mono (stage_sub_rules _)
    (iterType_typed (names := [numN]) (List.mem_cons_self ..))) (LevelTower.IsUniverse.sort _)

/-- The telescope of the iterator: the count, the carrier, the family, the step,
the value and its evidence. -/
abbrev iterTele : Tower.Ctx 6 := iterSucTelescopeAt (.sort Tower.zero) (.sort Tower.zero)

/-- The substitution of the iterator's telescope by a count, a carrier, a
family, a step, a value and its evidence. -/
def iterArgs {n : Nat} (q A P s u w : Tower.Tm n) : Sub Tower.Head 6 n :=
  consSub w (consSub u (consSub s (consSub P (consSub A (consSub q fun i => Fin.elim0 i)))))

/-- The iterator at zero pairs its value and evidence, in the executable
package. -/
theorem rules_iter_zero {n : Nat} (A P s x e : Tower.Tm n) :
    rules.computation.step (iterApp zeroNative A P s x e) (.pair x e) :=
  equation_sound (equation_listed 12 (by decide) rfl)
    (consSub e (consSub x (consSub s (consSub P (consSub A Fin.elim0)))))

/-- The iterator at a successor makes one shared use of its step, in the
executable package. -/
theorem rules_iter_suc {n : Nat} (a A P s x e : Tower.Tm n) :
    rules.computation.step (iterApp (sucNative a) A P s x e) (shared s (iterPartial a A P s) x e) :=
  equation_sound (equation_listed 13 (by decide) rfl)
    (consSub e (consSub x (consSub s (consSub P (consSub A (consSub a Fin.elim0))))))

/-- The body of one shared use of a step, instantiated at the computed pair:
the iterator at both projections. -/
theorem inst0_sharedIter {n : Nat} (c A P s N : Tower.Tm n) :
    Presentation.inst0 N (sharedBody (iterPartial c A P s)) =
      iterApp c A P s (.fst N) (.snd N) := by
  show Tm.app (Tm.app (Presentation.inst0 N (Presentation.rename wk (iterPartial c A P s)))
    (.fst N)) (.snd N) = _
  rw [inst0_rename_wk]
  rfl

/-- The family applied to the newest variable, instantiated at a point. -/
theorem inst0_familyApp {n : Nat} (x P : Tower.Tm n) :
    Presentation.inst0 x (.app (Presentation.rename wk P) (.var 0)) = .app P x := by
  show Tm.app (Presentation.inst0 x (Presentation.rename wk P)) x = _
  rw [inst0_rename_wk]

section Reductions

variable {T : RealizerSide Tower.Head ℕ} (ext : OverRules T)
include ext

/-- Reducing the count of an application of the iterator on the realizer side. -/
theorem iter_scrutinee {n : Nat} (A P s x e : Tower.Tm n) {c c' : Tower.Tm n}
    (red : WhRed T.R T.roles c c') :
    WhRed T.R T.roles (iterApp c A P s x e) (iterApp c' A P s x e) :=
  WhRed.scrutinee (before := []) (after := [A, P, s, x, e]) ext.roles_iter rfl red

/-- The full applications of the iterator to a typed substitution of its
telescope. -/
theorem iterApp_typed {n : Nat} {Δ : Tower.Ctx n} {q A P s u w : Tower.Tm n}
    (typed : SubstMor T.R iterTele Δ (iterArgs q A P s u w)) :
    Typed T.R Δ (iterApp q A P s u w) (.sigma A (.app (Presentation.rename wk P) (.var 0))) :=
  Typed.telescope_apply (Θ := iterTele) (X := iterResult) (σ := iterArgs q A P s u w) typed
    (ext.typed rules_iter_typed)

/-- **Reducing the count of a full application of the iterator**, typed. -/
theorem iter_scrutinee_red {n : Nat} {Δ : Tower.Ctx n} {q q' A P s u w : Tower.Tm n}
    (typed : SubstMor T.R iterTele Δ (iterArgs q A P s u w))
    (typed' : SubstMor T.R iterTele Δ (iterArgs q' A P s u w))
    (red : RedTm T.R T.roles Δ q q' numT) :
    RedTm T.R T.roles Δ (iterApp q A P s u w) (iterApp q' A P s u w)
      (.sigma A (.app (Presentation.rename wk P) (.var 0))) := by
  refine ⟨iter_scrutinee ext A P s u w red.red, iterApp_typed ext typed, iterApp_typed ext typed',
    Equal.telescope_apply (Θ := iterTele) (X := iterResult) (σ := iterArgs q A P s u w)
      (τ := iterArgs q' A P s u w) (fun i => ?_) (ext.typed rules_iter_typed)⟩
  refine Fin.cases (.refl (typed 0)) (fun i₁ => Fin.cases (.refl (typed 1))
    (fun i₂ => Fin.cases (.refl (typed 2)) (fun i₃ => Fin.cases (.refl (typed 3))
      (fun i₄ => Fin.cases (.refl (typed 4)) (fun i₅ => Fin.cases red.equal
        (fun o => o.elim0) i₅) i₄) i₃) i₂) i₁) i

/-- **The iterator at zero reduces, typed, to the pair of its value and its
evidence.** -/
theorem iter_zero_red {n : Nat} {Δ : Tower.Ctx n} {A P s u w : Tower.Tm n}
    (typed : SubstMor T.R iterTele Δ (iterArgs zeroNative A P s u w))
    (resultType : IsType T.R Δ (.sigma A (.app (Presentation.rename wk P) (.var 0)))) :
    RedTm T.R T.roles Δ (iterApp zeroNative A P s u w) (.pair u w)
      (.sigma A (.app (Presentation.rename wk P) (.var 0))) := by
  obtain ⟨v, hv, tResult⟩ := resultType
  have tw : Typed T.R Δ w
      (Presentation.inst0 u (.app (Presentation.rename wk P) (.var 0))) := by
    rw [inst0_familyApp]
    exact typed 0
  exact RedTm.root (ext.step (rules_iter_zero A P s u w)) (iterApp_typed ext typed)
    (.pairIntro tResult hv (typed 1) tw)

/-- **The iterator at a successor reduces, typed, to the iteration from the
projections of one shared use of the step**, in the iterator's telescope. -/
theorem iterSuc_red_telescope :
    RedTm T.R T.roles iterTele
      (iterApp (sucNative (.var 5)) (.var 4) (.var 3) (.var 2) (.var 1) (.var 0))
      (iterApp (.var 5) (.var 4) (.var 3) (.var 2) (.fst (.app (.app (.var 2) (.var 1)) (.var 0)))
        (.snd (.app (.app (.var 2) (.var 1)) (.var 0))))
      iterResult := by
  have iterT : Typed T.R iterTele (.const iterName) (liftClosed iterType) :=
    ext.typed rules_iter_typed
  have sucT : Typed T.R iterTele (sucNative (.var 5)) numT := .appElim ext.suc_typed (.var 5)
  -- The iterator at the successor, and its partial application at the predecessor.
  have source : Typed T.R iterTele
      (iterApp (sucNative (.var 5)) (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)) iterResult :=
    Derivable.appElim (Derivable.appElim (Derivable.appElim (Derivable.appElim
      (Derivable.appElim (Derivable.appElim iterT sucT) (.var 4)) (.var 3)) (.var 2))
      (.var 1)) (.var 0)
  have continuation : Typed T.R iterTele (iterPartial (.var 5) (.var 4) (.var 3) (.var 2))
      (stepOver (.var 4) (.app (.var 4) (.var 0))) :=
    Derivable.appElim (Derivable.appElim (Derivable.appElim (Derivable.appElim iterT (.var 5))
      (.var 4)) (.var 3)) (.var 2)
  -- The package computed by the step, and the shared use of it.
  have sigmaTyped : Typed T.R iterTele (.sigma (.var 4) (.app (.var 4) (.var 0)))
      (.head (.sort Tower.zero)) :=
    ext.typed (Derivable.mono (stage_sub_rules (allowedIn [])) (sigmaT (.var 4)
      (.appElim (B := U0) (.var 4) (.var 0))))
  have package : Typed T.R iterTele (.app (.app (.var 2) (.var 1)) (.var 0))
      (.sigma (.var 4) (.app (.var 4) (.var 0))) :=
    stepAppT (.var 2) (.var 1) (.var 0)
  have packVar : Typed T.R (.snoc iterTele (.sigma (.var 4) (.app (.var 4) (.var 0))))
      (.var 0) (.sigma (.var 5) (.app (.var 5) (.var 0))) := .var 0
  have body : Typed T.R (.snoc iterTele (.sigma (.var 4) (.app (.var 4) (.var 0))))
      (sharedBody (iterPartial (.var 5) (.var 4) (.var 3) (.var 2)))
      (Presentation.rename wk (.sigma (.var 4) (.app (.var 4) (.var 0)))) :=
    Derivable.appElim (Derivable.appElim
      (continuation.weaken (extension := .sigma (.var 4) (.app (.var 4) (.var 0))))
      (Derivable.fstElim packVar)) (Derivable.sndElim packVar)
  have sharedTyped : Typed T.R iterTele
      (shared (.var 2) (iterPartial (.var 5) (.var 4) (.var 3) (.var 2)) (.var 1) (.var 0))
      iterResult :=
    sharedT (A := .var 4) (P := .app (.var 4) (.var 0)) sigmaTyped (ext.isUniverse_zero)
      (ext.sub.join (.sorts _ _)) (ext.sub.cumulative (fun valuation => by simp [LevelExpr.eval]))
      (.var 2) (.var 1) (.var 0) body
  -- The iteration from the projections.
  have target : Typed T.R iterTele
      (iterApp (.var 5) (.var 4) (.var 3) (.var 2) (.fst (.app (.app (.var 2) (.var 1)) (.var 0)))
        (.snd (.app (.app (.var 2) (.var 1)) (.var 0)))) iterResult :=
    Derivable.appElim (Derivable.appElim continuation (Derivable.fstElim package))
      (Derivable.sndElim package)
  have arrowTyped : Typed T.R iterTele
      (.pi (.sigma (.var 4) (.app (.var 4) (.var 0)))
        (Presentation.rename wk (.sigma (.var 4) (.app (.var 4) (.var 0)))))
      (.head (.sort Tower.zero)) :=
    ext.typed (Derivable.mono (stage_sub_rules (allowedIn [])) (piT
      (sigmaT (.var 4) (.appElim (B := U0) (.var 4) (.var 0)))
      (sigmaT (.var 5) (.appElim (B := U0) (.var 5) (.var 0)))))
  have beta := RedTm.beta (roles := T.roles) arrowTyped ext.isUniverse_zero body package
  rw [inst0_sharedIter, inst0_rename_wk] at beta
  exact (RedTm.root (ext.step (rules_iter_suc _ _ _ _ _ _)) source sharedTyped).trans beta

/-- **The iterator at a successor reduces, typed, to the iteration from the
projections of one shared use of the step.** -/
theorem iter_suc_red {n : Nat} {Δ : Tower.Ctx n} {k A P s u w : Tower.Tm n}
    (typed : SubstMor T.R iterTele Δ (iterArgs k A P s u w)) :
    RedTm T.R T.roles Δ (iterApp (sucNative k) A P s u w)
      (iterApp k A P s (.fst (.app (.app s u) w)) (.snd (.app (.app s u) w)))
      (.sigma A (.app (Presentation.rename wk P) (.var 0))) :=
  (iterSuc_red_telescope ext).subst typed

end Reductions

section Model

variable (X : TExtension) (v : Nat → Nat) {T : RealizerSide Tower.Head ℕ}

/-! ## Values -/

section Values

variable {m : Nat} {ξ : World (nmodel X v T).reading m} {A : Tower.Tm m}
  {B : Tower.Tm (m + 1)} {R RS : NPack (nmodel X v T) m}

/-- A step related to another, applied to related values and related evidence,
gives related pairs. -/
theorem iterStep_related {s s' x x' e e' : Tower.Tm m}
    (den : DenN (nmodel X v T) ξ (.sigma A B) R)
    (denS : DenN (nmodel X v T) ξ (stepOver A B) RS) (hs : RS.rel s s')
    (hx : ∀ {RA : NPack (nmodel X v T) m}, DenN (nmodel X v T) ξ A RA →
      RA.rel x x')
    (he : ∀ {RB : NPack (nmodel X v T) m},
      DenN (nmodel X v T) ξ (Presentation.inst0 x B) RB → RB.rel e e') :
    R.rel (.app (.app s x) e) (.app (.app s' x') e') := by
  have vlaws := (nmodel_laws X v T).value
  obtain ⟨R₁, den₁, h₁⟩ := ValueSide.DenS.pi_app_exists vlaws denS hs hx
  rw [step_application_type] at den₁
  obtain ⟨R₂, den₂, h₂⟩ := ValueSide.DenS.pi_app_exists vlaws den₁ h₁ he
  rw [inst0_rename_wk] at den₂
  rw [ValueSide.DenS.deterministic vlaws den den₂]
  exact h₂

/-- **The iterator's values.** Iterators with related steps over a dependent
pair type, at counts of one shape, related values and related evidence, give
related pairs, whatever carrier and family they carry along. -/
theorem iter_related {s s' K F K' F' : Tower.Tm m}
    (den : DenN (nmodel X v T) ξ (.sigma A B) R)
    (denS : DenN (nmodel X v T) ξ (stepOver A B) RS) (hs : RS.rel s s')
    (sh : NumShape) :
    ∀ {c c' x x' e e' : Tower.Tm m}, X.VShape v c sh → X.VShape v c' sh →
      (∀ {RA : NPack (nmodel X v T) m}, DenN (nmodel X v T) ξ A RA →
        RA.rel x x') →
      (∀ {RB : NPack (nmodel X v T) m},
        DenN (nmodel X v T) ξ (Presentation.inst0 x B) RB → RB.rel e e') →
      R.rel (iterApp c K F s x e) (iterApp c' K' F' s' x' e') := by
  have vlaws := (nmodel_laws X v T).value
  have expansive := ValueSide.DenS.expansive vlaws den
  induction sh with
  | zero =>
      intro c c' x x' e e' hc hc' hx he
      cases hc with
      | zero red =>
          cases hc' with
          | zero red' =>
              refine expansive.left
                (Relation.ReflTransGen.tail (X.iter_scrutinee v K F s x e red)
                  (X.iter_zero_step v K F s x e))
                (expansive.right
                  (Relation.ReflTransGen.tail (X.iter_scrutinee v K' F' s' x' e' red')
                    (X.iter_zero_step v K' F' s' x' e')) ?_)
              exact ValueSide.DenS.sigma_pair vlaws den hx he
  | suc sh ih =>
      intro c c' x x' e e' hc hc' hx he
      cases hc with
      | @suc _ a _ red ha =>
          cases hc' with
          | @suc _ a' _ red' ha' =>
              have hp := iterStep_related X v den denS hs hx he
              refine expansive.left
                (Relation.ReflTransGen.tail
                  (Relation.ReflTransGen.tail (X.iter_scrutinee v K F s x e red)
                    (X.iter_suc_step v a K F s x e))
                  (X.shared_beta_step v (iterPartial a K F s) s x e))
                (expansive.right
                  (Relation.ReflTransGen.tail
                    (Relation.ReflTransGen.tail (X.iter_scrutinee v K' F' s' x' e' red')
                      (X.iter_suc_step v a' K' F' s' x' e'))
                    (X.shared_beta_step v (iterPartial a' K' F' s') s' x' e')) ?_)
              exact ih ha ha' (ValueSide.DenS.sigma_fst vlaws den hp)
                (ValueSide.DenS.sigma_snd vlaws den hp)
  | star =>
      intro c c' x x' e e' hc hc' _ _
      cases hc with
      | star red daimonic =>
          cases hc' with
          | star red' daimonic' =>
              refine expansive.left (X.iter_scrutinee v K F s x e red)
                (expansive.right (X.iter_scrutinee v K' F' s' x' e' red') ?_)
              have role : (nmodel X v T).roles iterName =
                  .computes 6 (.split 0 .constructor fun _ => .leaf) := X.extends_.iter
              exact ValueSide.DenS.daimonic_related vlaws den
                (Daimonic.stuck (before := []) (after := [K, F, s, x, e]) role rfl daimonic)
                (Daimonic.stuck (before := []) (after := [K', F', s', x', e']) role rfl
                  daimonic')

end Values

section Validity

variable (ext : OverRules T)
include ext

/-! ## Validity -/

/-- **The iterator is valid** in the conversion model. -/
theorem valid_iter : ValidTmN (nmodel X v T) .nil (.const iterName) iterType := by
  have laws := nmodel_laws X v T
  have vlaws := laws.value
  obtain ⟨validT, partsT, _⟩ := Derivable.validTN (numStage_typedSoundN X v ext)
    (iterType_typed (names := [numN]) (List.mem_cons_self ..)) trivial
  have validType : ValidTyN (nmodel X v T) .nil iterType :=
    validT.validTy (LevelTower.IsUniverse.sort _) (ext.isUniverse_sort _)
  obtain ⟨ctx, validResult, _⟩ := ValidTyN.close_parts iterTele (C := iterResult) validType partsT
  have typedIter : Typed T.R .nil (.const iterName) iterType := by
    have h := ext.typed (rules_iter_typed (Γ := .nil))
    rwa [TelescopeAbstraction.liftClosed_zero] at h
  refine ValidTmN.close laws iterTele (C := iterResult) (f := .const iterName) validType partsT
    typedIter
    (fun args short => .inr (.inr ⟨iterName, args, 6, .inr ⟨_, ext.roles_iter⟩, short, rfl⟩))
    ⟨validResult, fun {m r ξ σ σ' Δ ς ς'} e {R} den => ?_⟩
  -- Realizer-side facts.
  have formed := e.formed
  have typed := e.substMor
  have typed' := EqSubstN.substMor_right laws ctx.valid e
  obtain ⟨-, -, -, typesResult⟩ := validResult e
  obtain ⟨-, -, -, typesStep⟩ := (ctx.lookup 2).1 e
  have e₀ := e
  obtain ⟨⟨⟨⟨⟨⟨-, RN, denN, hN, rN⟩, RT, -, -, rT⟩, RF, -, -, rF⟩,
    RS, denS, hS, rS⟩, RX, denX, hX, rX⟩, RE, denE, hE, rE⟩ := e₀
  -- The count.
  change DenN (nmodel X v T) ξ numT RN at denN
  change RN.rel (σ 5) (σ' 5) at hN
  change (RN.real (σ 5)).rel Δ numT (ς 5) (ς' 5) at rN
  -- The carrier and the family.
  change (RT.real (σ 4)).rel Δ U0 (ς 4) (ς' 4) at rT
  change (RF.real (σ 3)).rel Δ (.pi (ς 4) U0) (ς 3) (ς' 3) at rF
  -- The step.
  have denS' : DenN (nmodel X v T) ξ
      (stepOver (σ 4) (.app (Presentation.rename wk (σ 3)) (.var 0))) RS := by
    change DenN (nmodel X v T) ξ (Presentation.subst (tailSub (tailSub (tailSub σ)))
      (stepOver (.var 1) (.app (.var 1) (.var 0)))) RS at denS
    rw [subst_stepOver] at denS
    exact denS
  change RS.rel (σ 2) (σ' 2) at hS
  have rS' : (RS.real (σ 2)).rel Δ (stepOver (ς 4) (.app (Presentation.rename wk (ς 3)) (.var 0)))
      (ς 2) (ς' 2) := by
    have h := rS
    change (RS.real (σ 2)).rel Δ (Presentation.subst (tailSub (tailSub (tailSub ς)))
      (stepOver (.var 1) (.app (.var 1) (.var 0)))) (ς 2) (ς' 2) at h
    rw [subst_stepOver] at h
    exact h
  have typeStep : IsType T.R Δ (stepOver (ς 4) (.app (Presentation.rename wk (ς 3)) (.var 0))) := by
    have h := typesStep.left
    change IsType T.R Δ (Presentation.subst (tailSub (tailSub (tailSub ς)))
      (stepOver (.var 1) (.app (.var 1) (.var 0)))) at h
    rw [subst_stepOver] at h
    exact h
  -- The value and its evidence.
  change DenN (nmodel X v T) ξ (σ 4) RX at denX
  change RX.rel (σ 1) (σ' 1) at hX
  change (RX.real (σ 1)).rel Δ (ς 4) (ς 1) (ς' 1) at rX
  change DenN (nmodel X v T) ξ (.app (σ 3) (σ 1)) RE at denE
  rw [← inst0_familyApp] at denE
  change RE.rel (σ 0) (σ' 0) at hE
  change (RE.real (σ 0)).rel Δ (.app (ς 3) (ς 1)) (ς 0) (ς' 0) at rE
  change DenN (nmodel X v T) ξ
    (.sigma (σ 4) (.app (Presentation.rename wk (σ 3)) (.var 0))) R at den
  show R.rel (iterApp (σ 5) (σ 4) (σ 3) (σ 2) (σ 1) (σ 0))
      (iterApp (σ' 5) (σ' 4) (σ' 3) (σ' 2) (σ' 1) (σ' 0)) ∧
    (R.real (iterApp (σ 5) (σ 4) (σ 3) (σ 2) (σ 1) (σ 0))).rel Δ
      (.sigma (ς 4) (.app (Presentation.rename wk (ς 3)) (.var 0)))
      (iterApp (ς 5) (ς 4) (ς 3) (ς 2) (ς 1) (ς 0))
      (iterApp (ς' 5) (ς' 4) (ς' 3) (ς' 2) (ς' 1) (ς' 0))
  rw [num_den X v denN] at hN
  obtain ⟨sh, hc, hc'⟩ := ValueSide.numIndPack_rel.mp hN
  have hS' := ValueSide.DenS.refl_left vlaws denS' hS
  refine ⟨iter_related X v den denS' hS sh hc hc'
    (fun d => by rw [ValueSide.DenS.deterministic vlaws d denX]; exact hX)
    (fun d => by rw [ValueSide.DenS.deterministic vlaws d denE]; exact hE), ?_⟩
  -- Equal instances of the carrier and the family, and the two result types.
  have eA : Equal T.R Δ (ς 4) (ς' 4) U0 := ECand.equal _ rT
  have eF : Equal T.R Δ (ς 3) (ς' 3) (.pi (ς 4) U0) := ECand.equal _ rF
  have resultEq : TypeEq T.R Δ (.sigma (ς 4) (.app (Presentation.rename wk (ς 3)) (.var 0)))
      (.sigma (ς' 4) (.app (Presentation.rename wk (ς' 3)) (.var 0))) := typesResult.typeEq
  have typeResult : IsType T.R Δ (.sigma (ς 4) (.app (Presentation.rename wk (ς 3)) (.var 0))) :=
    typesResult.left
  have carrierEq : TypeEq T.R Δ (ς 4) (ς' 4) := ⟨_, ext.isUniverse_zero, eA⟩
  have typeResult' : IsType T.R Δ
      (.sigma (ς' 4) (.app (Presentation.rename wk (ς' 3)) (.var 0))) := typesResult.right
  -- Typed substitutions of the iterator's telescope on both sides.
  have mor : ∀ {q u w : Tower.Tm r}, Typed T.R Δ q numT → Typed T.R Δ u (ς 4) →
      Typed T.R Δ w (.app (ς 3) u) →
      SubstMor T.R iterTele Δ (iterArgs q (ς 4) (ς 3) (ς 2) u w) := fun {q u w} tq tu tw =>
    SubstMor.cons (SubstMor.cons (SubstMor.cons (SubstMor.cons (SubstMor.cons
      (SubstMor.cons (fun i => Fin.elim0 i) tq) (typed 4)) (typed 3)) (typed 2)) tu) tw
  have mor' : ∀ {q u w : Tower.Tm r}, Typed T.R Δ q numT → Typed T.R Δ u (ς' 4) →
      Typed T.R Δ w (.app (ς' 3) u) →
      SubstMor T.R iterTele Δ (iterArgs q (ς' 4) (ς' 3) (ς' 2) u w) := fun {q u w} tq tu tw =>
    SubstMor.cons (SubstMor.cons (SubstMor.cons (SubstMor.cons (SubstMor.cons
      (SubstMor.cons (fun i => Fin.elim0 i) tq) (typed' 4)) (typed' 3)) (typed' 2)) tu) tw
  -- The realizer claim, by induction on the count's shape.
  have claim : ∀ (sh : NumShape) {c₀ x₀ e₀ : Tower.Tm m}, X.VShape v c₀ sh →
      ∀ {q q' u u' w w' : Tower.Tm r},
        NumShapeRel T numN zeroN sucN sh Δ numT q q' →
        (∀ {RA : NPack (nmodel X v T) m}, DenN (nmodel X v T) ξ (σ 4) RA →
          RA.Val x₀ ∧ (RA.real x₀).rel Δ (ς 4) u u') →
        (∀ {RB : NPack (nmodel X v T) m}, DenN (nmodel X v T) ξ
            (Presentation.inst0 x₀ (.app (Presentation.rename wk (σ 3)) (.var 0))) RB →
          RB.Val e₀ ∧ (RB.real e₀).rel Δ (.app (ς 3) u) w w') →
        (R.real (iterApp c₀ (σ 4) (σ 3) (σ 2) x₀ e₀)).rel Δ
          (.sigma (ς 4) (.app (Presentation.rename wk (ς 3)) (.var 0)))
          (iterApp q (ς 4) (ς 3) (ς 2) u w) (iterApp q' (ς' 4) (ς' 3) (ς' 2) u' w') := by
    -- The realizers of the value and of its evidence are typed on both sides.
    have typings : ∀ {x₀ e₀ : Tower.Tm m} {u u' w w' : Tower.Tm r},
        (∀ {RA : NPack (nmodel X v T) m}, DenN (nmodel X v T) ξ (σ 4) RA →
          RA.Val x₀ ∧ (RA.real x₀).rel Δ (ς 4) u u') →
        (∀ {RB : NPack (nmodel X v T) m}, DenN (nmodel X v T) ξ
            (Presentation.inst0 x₀ (.app (Presentation.rename wk (σ 3)) (.var 0))) RB →
          RB.Val e₀ ∧ (RB.real e₀).rel Δ (.app (ς 3) u) w w') →
        (Typed T.R Δ u (ς 4) ∧ Typed T.R Δ u' (ς' 4)) ∧
          (Typed T.R Δ w (.app (ς 3) u) ∧ Typed T.R Δ w' (.app (ς' 3) u')) := by
      intro x₀ e₀ u u' w w' hx he
      obtain ⟨l, Q, -, interprets⟩ := ValueSide.DenS.sigma_inv vlaws den
      obtain ⟨vx, ru⟩ := hx ⟨l, interprets.dom_id⟩
      obtain ⟨-, rw⟩ := he ⟨l, interprets.cod_id vx⟩
      obtain ⟨tu, tu'⟩ := ECand.typed _ ru
      obtain ⟨tw, tw'⟩ := ECand.typed _ rw
      have familyEq : TypeEq T.R Δ (.app (ς 3) u) (.app (ς' 3) u') :=
        ⟨_, ext.isUniverse_zero, .appCong (B := U0) eF (ECand.equal _ ru)⟩
      exact ⟨⟨tu, Typed.convType tu' carrierEq⟩, ⟨tw, Typed.convType tw' familyEq⟩⟩
    -- Counts reaching neutral terms: both applications reach neutral spines.
    have neutralCase : ∀ {c₀ x₀ e₀ : Tower.Tm m} {q q' u u' w w' : Tower.Tm r},
        NeRel T Δ numT q q' →
        (∀ {RA : NPack (nmodel X v T) m}, DenN (nmodel X v T) ξ (σ 4) RA →
          RA.Val x₀ ∧ (RA.real x₀).rel Δ (ς 4) u u') →
        (∀ {RB : NPack (nmodel X v T) m}, DenN (nmodel X v T) ξ
            (Presentation.inst0 x₀ (.app (Presentation.rename wk (σ 3)) (.var 0))) RB →
          RB.Val e₀ ∧ (RB.real e₀).rel Δ (.app (ς 3) u) w w') →
        (R.real (iterApp c₀ (σ 4) (σ 3) (σ 2) x₀ e₀)).rel Δ
          (.sigma (ς 4) (.app (Presentation.rename wk (ς 3)) (.var 0)))
          (iterApp q (ς 4) (ς 3) (ς 2) u w) (iterApp q' (ς' 4) (ς' 3) (ς' 2) u' w') := by
      intro c₀ x₀ e₀ q q' u u' w w' ne hx he
      obtain ⟨⟨tu, tu'⟩, ⟨tw, tw'⟩⟩ := typings hx he
      obtain ⟨n₀, n₀', r₀, r₀', nw, nw', cv⟩ := ne
      have redN := iter_scrutinee_red ext (mor r₀.source tu tw) (mor r₀.target tu tw) r₀
      have redN' := (iter_scrutinee_red ext (mor' r₀'.source tu' tw') (mor' r₀'.target tu' tw')
        r₀').conv resultEq.symm
      obtain ⟨l, Q, -, interprets⟩ := ValueSide.DenS.sigma_inv vlaws den
      obtain ⟨vx, ru₀⟩ := hx ⟨l, interprets.dom_id⟩
      have rw := (he ⟨l, interprets.cod_id vx⟩).2
      have conv : ∀ i, T.E.convTm Δ (iterArgs n₀ (ς 4) (ς 3) (ς 2) u w i)
          (iterArgs n₀' (ς' 4) (ς' 3) (ς' 2) u' w' i)
          (Presentation.subst (iterArgs n₀ (ς 4) (ς 3) (ς 2) u w) (Ctx.lookup iterTele i)) := by
        intro i
        refine Fin.cases ?_ (fun i₁ => Fin.cases ?_ (fun i₂ => Fin.cases ?_ (fun i₃ =>
          Fin.cases ?_ (fun i₄ => Fin.cases ?_ (fun i₅ => Fin.cases ?_
            (fun o => o.elim0) i₅) i₄) i₃) i₂) i₁) i
        · exact ECand.escape _ rw
        · exact ECand.escape _ ru₀
        · exact ECand.escape _ rS
        · exact ECand.escape _ rF
        · exact ECand.escape _ rT
        · exact T.laws.convTm_of_convNe (.inl nw) (.inl nw') cv
      have spineConv := convNe_telescope_apply (S := T.toSetting) T.laws
        (Θ := iterTele) (X := iterResult) conv (T.laws.convNe_const iterName (ext.typed rules_iter_typed))
      change T.E.convNe Δ (iterApp n₀ (ς 4) (ς 3) (ς 2) u w)
        (iterApp n₀' (ς' 4) (ς' 3) (ς' 2) u' w')
        (.sigma (ς 4) (.app (Presentation.rename wk (ς 3)) (.var 0))) at spineConv
      exact ECand.expand _ redN redN' (ECand.neutral _
        (Neutral.stuck_single (before := []) (after := [ς 4, ς 3, ς 2, u, w]) ext.roles_iter rfl nw)
        (Neutral.stuck_single (before := []) (after := [ς' 4, ς' 3, ς' 2, u', w']) ext.roles_iter rfl
          nw')
        redN.target redN'.target spineConv)
    intro sh
    induction sh with
    | zero =>
        intro c₀ x₀ e₀ hc₀ q q' u u' w w' hq hx he
        rcases hq with ne | ⟨-, r₀, r₀', -⟩
        · exact neutralCase ne hx he
        cases hc₀ with
        | zero red =>
            obtain ⟨⟨tu, tu'⟩, ⟨tw, tw'⟩⟩ := typings hx he
            have hpair : R.rel (.pair x₀ e₀) (.pair x₀ e₀) :=
              ValueSide.DenS.sigma_pair vlaws den (fun d => (hx d).1) (fun d => (he d).1)
            rw [ValueSide.DenS.real_eq_of_rel vlaws den ((ValueSide.DenS.expansive vlaws den).left
              (Relation.ReflTransGen.tail (X.iter_scrutinee v (σ 4) (σ 3) (σ 2) x₀ e₀ red)
                (X.iter_zero_step v (σ 4) (σ 3) (σ 2) x₀ e₀)) hpair)]
            have red₀ :=
              (iter_scrutinee_red ext (mor r₀.source tu tw) (mor r₀.target tu tw) r₀).trans
              (iter_zero_red ext (mor r₀.target tu tw) typeResult)
            have red₀' := ((iter_scrutinee_red ext (mor' r₀'.source tu' tw')
              (mor' r₀'.target tu' tw') r₀').trans
              (iter_zero_red ext (mor' r₀'.target tu' tw') typeResult')).conv resultEq.symm
            refine ECand.expand _ red₀ red₀' (DenN.sigma_pair_real laws den formed typeResult
              (fun d => hx d) (fun d => ?_))
            obtain ⟨ve, re⟩ := he d
            rw [inst0_familyApp]
            exact ⟨ve, re⟩
    | suc sh ih =>
        intro c₀ x₀ e₀ hc₀ q q' u u' w w' hq hx he
        rcases hq with ne | ⟨-, k, k', r₀, r₀', -, hk⟩
        · exact neutralCase ne hx he
        cases hc₀ with
        | @suc _ c _ red hc =>
            obtain ⟨⟨tu, tu'⟩, ⟨tw, tw'⟩⟩ := typings hx he
            -- One use of the step on the value side: the computed pair and its
            -- projections.
            have hp := iterStep_related X v den denS' hS' (fun d => (hx d).1)
              (fun d => (he d).1)
            -- The step's realizers applied to the realizers of the value and the
            -- evidence realize the computed pair.
            obtain ⟨R₁, den₁, h₁⟩ := ValueSide.DenS.pi_app_exists vlaws denS' hS'
              (fun d => (hx d).1)
            have real₁ := DenN.pi_app_real laws denS' formed (RedTy.refl typeStep) rS'
              (fun d => hx d) den₁
            rw [step_application_type] at den₁ real₁
            obtain ⟨R₂, den₂, -⟩ :=
              ValueSide.DenS.pi_app_exists vlaws den₁ h₁ (fun d => (he d).1)
            obtain ⟨-, typeCod⟩ := IsType.pi_parts typeStep
            obtain ⟨uu, hu, tCod⟩ := typeCod
            have typeCod' : IsType T.R Δ (.pi (.app (ς 3) u)
                (Presentation.rename wk (.sigma (ς 4)
                  (.app (Presentation.rename wk (ς 3)) (.var 0))))) := by
              have h := Typed.instantiate tCod tu
              rw [step_application_type, inst0_familyApp] at h
              exact ⟨uu, hu, h⟩
            rw [inst0_familyApp] at real₁
            have real₂ := DenN.pi_app_real laws den₁ formed (RedTy.refl typeCod') real₁
              (fun d => he d) den₂
            rw [inst0_rename_wk] at den₂ real₂
            obtain rfl := ValueSide.DenS.deterministic vlaws den den₂
            -- The projections of the computed pair on both sides.
            obtain ⟨realFst, realSnd⟩ := DenN.sigma_proj_real laws den
              (ValueSide.DenS.refl_left vlaws den hp) formed (RedTy.refl typeResult) real₂
            -- The iteration from the projections, by induction.
            have call := ih hc hk
              (fun d => ⟨ValueSide.DenS.sigma_fst vlaws den hp d |> ValueSide.DenS.refl_left vlaws d,
                realFst d⟩)
              (fun d => ⟨ValueSide.DenS.sigma_snd vlaws den hp d |> ValueSide.DenS.refl_left vlaws d,
                by have h := realSnd d; rw [inst0_familyApp] at h; exact h⟩)
            -- The iterator's value is the value of the iteration from the projections.
            have hrec : R.rel
                (iterApp c (σ 4) (σ 3) (σ 2) (.fst (.app (.app (σ 2) x₀) e₀))
                  (.snd (.app (.app (σ 2) x₀) e₀)))
                (iterApp c (σ 4) (σ 3) (σ 2) (.fst (.app (.app (σ 2) x₀) e₀))
                  (.snd (.app (.app (σ 2) x₀) e₀))) :=
              iter_related X v den denS' hS' sh hc hc
                (ValueSide.DenS.sigma_fst vlaws den hp) (ValueSide.DenS.sigma_snd vlaws den hp)
            rw [ValueSide.DenS.real_eq_of_rel vlaws den ((ValueSide.DenS.expansive vlaws den).left
              (Relation.ReflTransGen.tail
                (Relation.ReflTransGen.tail (X.iter_scrutinee v (σ 4) (σ 3) (σ 2) x₀ e₀ red)
                  (X.iter_suc_step v c (σ 4) (σ 3) (σ 2) x₀ e₀))
                (X.shared_beta_step v (iterPartial c (σ 4) (σ 3) (σ 2)) (σ 2) x₀ e₀)) hrec)]
            -- Both realizer applications compute to the iteration from the projections.
            have hkReal := (num_real X v ext ⟨0, num_interp X v 0 ξ⟩ hc Δ numT k k').mpr hk
            obtain ⟨tk, tk'⟩ := ECand.typed _ hkReal
            have red₁ :=
              (iter_scrutinee_red ext (mor r₀.source tu tw) (mor r₀.target tu tw) r₀).trans
              (iter_suc_red ext (mor tk tu tw))
            have red₁' := ((iter_scrutinee_red ext (mor' r₀'.source tu' tw')
              (mor' r₀'.target tu' tw') r₀').trans
              (iter_suc_red ext (mor' tk' tu' tw'))).conv resultEq.symm
            exact ECand.expand _ red₁ red₁' call
    | star =>
        intro c₀ x₀ e₀ _ q q' u u' w w' hq hx he
        exact neutralCase hq hx he
  exact claim sh hc ((num_real X v ext denN hc Δ numT _ _).mp rN)
    (fun d => by
      rw [ValueSide.DenS.deterministic vlaws d denX]
      exact ⟨ValueSide.DenS.refl_left vlaws denX hX, rX⟩)
    (fun d => by
      rw [ValueSide.DenS.deterministic vlaws d denE]
      exact ⟨ValueSide.DenS.refl_left vlaws denE hE, rE⟩)

end Validity

end Model

end ConvRules
end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
