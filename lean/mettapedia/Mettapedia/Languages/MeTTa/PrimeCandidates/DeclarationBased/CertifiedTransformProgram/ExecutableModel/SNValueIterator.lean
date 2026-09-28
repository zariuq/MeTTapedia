import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.SNValueSteps
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectSteps
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.StrongNormalization.Spines
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.LevelTypings

/-!
# The iterator in the transport value model

On the skeleton-free value side of the transport value model the iterator is a
valid term of `Π (n : num) (A : k) (P : A → l) (step : Π x : A. P x → Σ y : A. P y)
(x : A) (e : P x). Σ A P` for every carrier universe `k` and family universe
`l`, when that type is valid with valid parts (`vmodel_valid_iter_at`); its
declared type is the instance at the lowest universe (`vmodel_valid_iter`).

The iterator computes by recursion on its count: at `zero` it pairs its value
with its evidence, and at `suc m` it makes one shared use of the step, then
iterates `m` times from the projections of the computed pair. At a daimonic
count it is stuck on the daimon. It never inspects its carrier and family
arguments, so the recursion is stated for a step between the values of any
dependent pair type `Σ A B`, whatever terms the iterator carries along.

* Values. At counts of one shape, related values and related evidence, the
  iterator gives related pairs, by induction on the shape. At zero these are
  the pairs of the values and the evidence; at a successor the step relates the
  computed pairs, and so their projections; at the daimon both applications
  are daimonic, and every type relates daimonic terms.
* Realizers. By induction on the shape of a realizer of the count, the iterator
  applied to realizers realizes the iterator applied to the values. Its root
  reducts are, at `zero`, a pair of reducts of the realizers of the value and
  the evidence, and at `suc m` a β-redex whose contractum is the iterator at
  `m` applied to the projections of the step's realizer applied to the
  realizers; a realizer of the daimon's shape reduces to no numeral. On the
  value side the iterator computes by the same recursion, so its value has the
  realizers of the value it computes to.

Related values are valid, since each relation is a partial equivalence, so no
premise about the universe of the pair type is needed, nor about the universes
of the carrier and the family: large families are the same argument.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.StrongNormalization
open Presentation.TypedEquality.Impredicative
open Presentation.TypedEquality.Impredicative.Consistency (World)
open Presentation.TypedEquality.Impredicative.Realizability (Daimonic)
open CertifiedTransforms (stepOver shared sharedBody step_application_type subst_stepOver)
open Package (numT iterName iterType iterApp iterPartial)

namespace CodeModel

variable (v : Nat → Nat)

/-! ## Spines of the iterator on the realizer side -/

/-- The iterator computes with six arguments, its count first. -/
private theorem objectRoles_iterator :
    objectRoles iterName = .computes 6 (.split 0 .constructor fun _ => .leaf) :=
  objectRoles_of_roles roles_iter nofun

/-- A property of six elements holds of every element of their list. -/
private theorem forall_mem_six {α : Type} {p : α → Prop} {a₀ a₁ a₂ a₃ a₄ a₅ : α}
    (h₀ : p a₀) (h₁ : p a₁) (h₂ : p a₂) (h₃ : p a₃) (h₄ : p a₄) (h₅ : p a₅) :
    ∀ a ∈ [a₀, a₁, a₂, a₃, a₄, a₅], p a := by
  intro a ha
  rcases ha with _ | ⟨_, ha⟩
  · exact h₀
  rcases ha with _ | ⟨_, ha⟩
  · exact h₁
  rcases ha with _ | ⟨_, ha⟩
  · exact h₂
  rcases ha with _ | ⟨_, ha⟩
  · exact h₃
  rcases ha with _ | ⟨_, ha⟩
  · exact h₄
  rcases ha with _ | ⟨_, ha⟩
  · exact h₅
  cases ha

/-- The iterator applied to six strongly normalizing terms lies in a Kripke
candidate when, after any reductions of the arguments, the candidate contains
its root reducts: at `zero` the pair of the value and the evidence, and at a
successor one shared use of the step. -/
private theorem iterSpine_mem (X : KCand objectRules objectRoles) {r : Nat}
    {c A P s u w : Tower.Tm r} (sc : SN objectRules c) (sA : SN objectRules A)
    (sP : SN objectRules P) (ss : SN objectRules s) (su : SN objectRules u)
    (sw : SN objectRules w)
    (zero : ∀ {u' w' : Tower.Tm r}, ReducesStar objectRules c (.const zeroN) →
      ReducesStar objectRules u u' → ReducesStar objectRules w w' → X.mem (.pair u' w'))
    (suc : ∀ {k A' P' s' u' w' : Tower.Tm r},
      ReducesStar objectRules c (.app (.const sucN) k) → ReducesStar objectRules A A' →
      ReducesStar objectRules P P' → ReducesStar objectRules s s' →
      ReducesStar objectRules u u' → ReducesStar objectRules w w' →
      X.mem (shared s' (iterPartial k A' P' s') u' w')) :
    X.mem (iterApp c A P s u w) := by
  refine KCand.computingSpine_mem objectShape X objectRoles_iterator
    (args := [c, A, P, s, u, w]) rfl (forall_mem_six sc sA sP ss su sw)
    fun args' steps r step => ?_
  obtain ⟨c', A', P', s', u', w', rfl, hc, hA, hP, hs, hu, hw⟩ := ArgsStep.star_six steps
  rcases objectStep_iter step with ⟨rfl, rfl⟩ | ⟨k, rfl, rfl⟩
  · exact zero hc hu hw
  · exact suc hc hA hP hs hu hw

/-- The body of one shared use of a step, instantiated at the computed pair:
the iterator at both projections. -/
private theorem inst0_sharedBody {n : Nat} (c A P s N : Tower.Tm n) :
    Presentation.inst0 N (sharedBody (iterPartial c A P s)) =
      iterApp c A P s (.fst N) (.snd N) := by
  show Tm.app (Tm.app (Presentation.inst0 N (Presentation.rename wk (iterPartial c A P s)))
    (.fst N)) (.snd N) = _
  rw [inst0_rename_wk]
  rfl

section Recursion

variable {m : Nat} {ξ : World (vmodel v).reading m} {A : Tower.Tm m} {B : Tower.Tm (m + 1)}
  {R RS : ValueSide.Pack (vmodel v).value m}

/-! ## One use of the step -/

/-- A step related to another, applied to related values and related evidence,
gives related pairs. -/
private theorem step_related {s s' x x' e e' : Tower.Tm m}
    (den : ValueSide.DenS (vmodel v).value ξ (.sigma A B) R)
    (denS : ValueSide.DenS (vmodel v).value ξ (stepOver A B) RS) (hs : RS.rel s s')
    (hx : ∀ {RA : ValueSide.Pack (vmodel v).value m}, ValueSide.DenS (vmodel v).value ξ A RA →
      RA.rel x x')
    (he : ∀ {RB : ValueSide.Pack (vmodel v).value m},
      ValueSide.DenS (vmodel v).value ξ (Presentation.inst0 x B) RB → RB.rel e e') :
    R.rel (.app (.app s x) e) (.app (.app s' x') e') := by
  have laws := vmodel_laws v
  obtain ⟨R₁, den₁, h₁⟩ := ModelS.DenS.pi_app_exists laws denS hs hx
  rw [step_application_type] at den₁
  obtain ⟨R₂, den₂, h₂⟩ := ModelS.DenS.pi_app_exists laws den₁ h₁ he
  rw [inst0_rename_wk] at den₂
  rw [ValueSide.DenS.deterministic (vmodel_valueLaws v) den den₂]
  exact h₂

/-- A realizer of a step applied to realizers of a value and of its evidence
realizes the computed pair. -/
private theorem step_real {s x e : Tower.Tm m} {r : Nat} {t u w : Tower.Tm r}
    (den : ValueSide.DenS (vmodel v).value ξ (.sigma A B) R)
    (denS : ValueSide.DenS (vmodel v).value ξ (stepOver A B) RS) (hs : RS.rel s s)
    (ht : (RS.real s).mem t)
    (hx : ∀ {RA : ValueSide.Pack (vmodel v).value m}, ValueSide.DenS (vmodel v).value ξ A RA →
      RA.rel x x ∧ (RA.real x).mem u)
    (he : ∀ {RB : ValueSide.Pack (vmodel v).value m},
      ValueSide.DenS (vmodel v).value ξ (Presentation.inst0 x B) RB →
        RB.rel e e ∧ (RB.real e).mem w) :
    (R.real (.app (.app s x) e)).mem (.app (.app t u) w) := by
  have laws := vmodel_laws v
  obtain ⟨R₁, den₁, h₁⟩ := ModelS.DenS.pi_app_exists laws denS hs (fun d => (hx d).1)
  have real₁ := ModelS.DenS.pi_app_real laws denS ht (fun d => (hx d).1) (fun d => (hx d).2)
    den₁
  rw [step_application_type] at den₁
  obtain ⟨R₂, den₂, -⟩ := ModelS.DenS.pi_app_exists laws den₁ h₁ (fun d => (he d).1)
  have real₂ := ModelS.DenS.pi_app_real laws den₁ real₁ (fun d => (he d).1) (fun d => (he d).2)
    den₂
  rw [inst0_rename_wk] at den₂
  rw [ValueSide.DenS.deterministic (vmodel_valueLaws v) den den₂]
  exact real₂

/-! ## The iterator on values and on realizers -/

/-- Iterators with related steps over a dependent pair type, at counts of one
shape, related values and related evidence, give related pairs, whatever
carrier and family they carry along. -/
theorem viter_related {s s' T F T' F' : Tower.Tm m}
    (den : ValueSide.DenS (vmodel v).value ξ (.sigma A B) R)
    (denS : ValueSide.DenS (vmodel v).value ξ (stepOver A B) RS) (hs : RS.rel s s')
    (sh : NumShape) :
    ∀ {c c' x x' e e' : Tower.Tm m}, VShape v c sh → VShape v c' sh →
      (∀ {RA : ValueSide.Pack (vmodel v).value m}, ValueSide.DenS (vmodel v).value ξ A RA →
        RA.rel x x') →
      (∀ {RB : ValueSide.Pack (vmodel v).value m},
        ValueSide.DenS (vmodel v).value ξ (Presentation.inst0 x B) RB → RB.rel e e') →
      R.rel (iterApp c T F s x e) (iterApp c' T' F' s' x' e') := by
  have laws := vmodel_laws v
  have expansive := ValueSide.DenS.expansive (vmodel_valueLaws v) den
  induction sh with
  | zero =>
      intro c c' x x' e e' hc hc' hx he
      cases hc with
      | zero red =>
          cases hc' with
          | zero red' =>
              refine expansive.left
                (Relation.ReflTransGen.tail (viter_scrutinee v T F s x e red)
                  (viter_zero_step v T F s x e))
                (expansive.right
                  (Relation.ReflTransGen.tail (viter_scrutinee v T' F' s' x' e' red')
                    (viter_zero_step v T' F' s' x' e')) ?_)
              exact ModelS.DenS.sigma_pair laws den hx he
  | suc sh ih =>
      intro c c' x x' e e' hc hc' hx he
      cases hc with
      | @suc _ a _ red ha =>
          cases hc' with
          | @suc _ a' _ red' ha' =>
              have hp := step_related v den denS hs hx he
              refine expansive.left
                (Relation.ReflTransGen.tail
                  (Relation.ReflTransGen.tail (viter_scrutinee v T F s x e red)
                    (viter_suc_step v a T F s x e))
                  (vshared_beta_step v (iterPartial a T F s) s x e))
                (expansive.right
                  (Relation.ReflTransGen.tail
                    (Relation.ReflTransGen.tail (viter_scrutinee v T' F' s' x' e' red')
                      (viter_suc_step v a' T' F' s' x' e'))
                    (vshared_beta_step v (iterPartial a' T' F' s') s' x' e')) ?_)
              exact ih ha ha' (ModelS.DenS.sigma_fst laws den hp)
                (ModelS.DenS.sigma_snd laws den hp)
  | star =>
      intro c c' x x' e e' hc hc' _ _
      cases hc with
      | star red daimonic =>
          cases hc' with
          | star red' daimonic' =>
              refine expansive.left (viter_scrutinee v T F s x e red)
                (expansive.right (viter_scrutinee v T' F' s' x' e' red') ?_)
              have role : (vmodel v).roles iterName =
                  .computes 6 (.split 0 .constructor fun _ => .leaf) := tmodelRoles_iter
              exact ValueSide.DenS.daimonic_related (vmodel_valueLaws v) den
                (Daimonic.stuck (before := []) (after := [T, F, s, x, e]) role rfl daimonic)
                (Daimonic.stuck (before := []) (after := [T', F', s', x', e']) role rfl
                  daimonic')

/-- An iterator over a dependent pair type, applied to realizers of its count,
step, value and evidence and to strongly normalizing carrier and family,
realizes the iterator applied to the count, the step, the value and the
evidence. -/
theorem viter_real {s T F : Tower.Tm m}
    (den : ValueSide.DenS (vmodel v).value ξ (.sigma A B) R)
    (denS : ValueSide.DenS (vmodel v).value ξ (stepOver A B) RS) (hs : RS.rel s s)
    (sh : NumShape) :
    ∀ {c x e : Tower.Tm m} {r : Nat} {c' T' F' s' u w : Tower.Tm r},
      VShape v c sh → (VNumReal sh).mem c' →
      SN objectRules T' → SN objectRules F' → (RS.real s).mem s' →
      (∀ {RA : ValueSide.Pack (vmodel v).value m}, ValueSide.DenS (vmodel v).value ξ A RA →
        RA.rel x x ∧ (RA.real x).mem u) →
      (∀ {RB : ValueSide.Pack (vmodel v).value m},
        ValueSide.DenS (vmodel v).value ξ (Presentation.inst0 x B) RB →
          RB.rel e e ∧ (RB.real e).mem w) →
      (R.real (iterApp c T F s x e)).mem (iterApp c' T' F' s' u w) := by
  have laws := vmodel_laws v
  have vlaws := vmodel_valueLaws v
  have expansive := ValueSide.DenS.expansive vlaws den
  -- Realizers of values of the domain and of the codomain are strongly normalizing.
  have realSN : ∀ {x e : Tower.Tm m} {r : Nat} {u w : Tower.Tm r},
      (∀ {RA : ValueSide.Pack (vmodel v).value m}, ValueSide.DenS (vmodel v).value ξ A RA →
        RA.rel x x ∧ (RA.real x).mem u) →
      (∀ {RB : ValueSide.Pack (vmodel v).value m},
        ValueSide.DenS (vmodel v).value ξ (Presentation.inst0 x B) RB →
          RB.rel e e ∧ (RB.real e).mem w) →
      SN objectRules u ∧ SN objectRules w := by
    intro x e r u w hx he
    obtain ⟨l, Q, -, interprets⟩ := ValueSide.DenS.sigma_inv vlaws den
    have domI : ValueSide.DenS (vmodel v).value ξ A (Q.dom (Consistency.Morph.id ξ)) :=
      ⟨l, interprets.dom_id⟩
    have vx := (hx domI).1
    exact ⟨KCand.sn _ (hx domI).2, KCand.sn _ (he ⟨l, interprets.cod_id vx⟩).2⟩
  induction sh with
  | zero =>
      intro c x e r c' T' F' s' u w hc hc' sT sF hs' hx he
      obtain ⟨su, sw⟩ := realSN hx he
      refine iterSpine_mem _ (KCand.sn _ hc') sT sF (KCand.sn _ hs') su sw
        (fun {u'' w''} _ hu'' hw'' => ?_) (fun hc'' _ _ _ _ _ => ?_)
      · cases hc with
        | zero red =>
            have hpair : R.rel (.pair x e) (.pair x e) :=
              ModelS.DenS.sigma_pair laws den (fun d => (hx d).1) (fun d => (he d).1)
            rw [ValueSide.DenS.real_eq_of_rel vlaws den (expansive.left
              (Relation.ReflTransGen.tail (viter_scrutinee v T F s x e red)
                (viter_zero_step v T F s x e)) hpair)]
            exact ModelS.DenS.sigma_pair_real laws den
              (fun d => ⟨(hx d).1, KCand.reducts _ (hx d).2 hu''⟩)
              (fun d => ⟨(he d).1, KCand.reducts _ (he d).2 hw''⟩)
      · obtain ⟨_, ⟨⟩, _⟩ := NumReal.shape_of_suc objectReflects objectNumerals hc' hc''
  | suc sh ih =>
      intro c x e r c' T' F' s' u w hc hc' sT sF hs' hx he
      obtain ⟨su, sw⟩ := realSN hx he
      refine iterSpine_mem _ (KCand.sn _ hc') sT sF (KCand.sn _ hs') su sw
        (fun hc'' _ _ => nomatch NumReal.shape_of_zero objectReflects objectNumerals hc' hc'')
        (fun {k T'' F'' s'' u'' w''} hc'' hT'' hF'' hs'' hu'' hw'' => ?_)
      obtain ⟨_, same, hk⟩ := NumReal.shape_of_suc objectReflects objectNumerals hc' hc''
      cases same
      cases hc with
      | @suc _ a _ red ha =>
          -- One use of the step, on the value side and on the realizer side.
          have hp := step_related v den denS hs (fun d => (hx d).1) (fun d => (he d).1)
          have hN := step_real v den denS hs (KCand.reducts _ hs' hs'')
            (fun d => ⟨(hx d).1, KCand.reducts _ (hx d).2 hu''⟩)
            (fun d => ⟨(he d).1, KCand.reducts _ (he d).2 hw''⟩)
          -- The iteration from the projections of the computed pair.
          have call := ih ha hk (sT.reducts hT'') (sF.reducts hF'') (KCand.reducts _ hs' hs'')
            (fun d => ⟨ModelS.DenS.sigma_fst laws den hp d,
              ModelS.DenS.sigma_fst_real laws den hp hN d⟩)
            (fun d => ⟨ModelS.DenS.sigma_snd laws den hp d,
              ModelS.DenS.sigma_snd_real laws den hp hN d⟩)
          have hrec : R.rel
              (iterApp a T F s (.fst (.app (.app s x) e)) (.snd (.app (.app s x) e)))
              (iterApp a T F s (.fst (.app (.app s x) e)) (.snd (.app (.app s x) e))) :=
            viter_related v den denS hs sh ha ha (ModelS.DenS.sigma_fst laws den hp)
              (ModelS.DenS.sigma_snd laws den hp)
          rw [ValueSide.DenS.real_eq_of_rel vlaws den (expansive.left
            (Relation.ReflTransGen.tail
              (Relation.ReflTransGen.tail (viter_scrutinee v T F s x e red)
                (viter_suc_step v a T F s x e))
              (vshared_beta_step v (iterPartial a T F s) s x e)) hrec)]
          rw [← inst0_sharedBody k T'' F'' s''] at call
          exact KCand.beta objectShape _ (SN.of_subst (subst0 _) (KCand.sn _ call))
            (KCand.sn _ hN) call
  | star =>
      intro c x e r c' T' F' s' u w _ hc' sT sF hs' hx he
      obtain ⟨su, sw⟩ := realSN hx he
      refine iterSpine_mem _ (KCand.sn _ hc') sT sF (KCand.sn _ hs') su sw
        (fun hc'' _ _ => nomatch NumReal.shape_of_zero objectReflects objectNumerals hc' hc'')
        (fun hc'' _ _ _ _ _ => ?_)
      obtain ⟨_, ⟨⟩, _⟩ := NumReal.shape_of_suc objectReflects objectNumerals hc' hc''

end Recursion

/-! ## Validity -/

/-- The family of the iterator applied to the newest variable, instantiated at
a point. -/
private theorem inst0_family {n : Nat} (x P : Tower.Tm n) :
    Presentation.inst0 x (.app (Presentation.rename wk P) (.var 0)) = .app P x := by
  show Tm.app (Presentation.inst0 x (Presentation.rename wk P)) x = _
  rw [inst0_rename_wk]

/-- **The iterator is valid at large families** in the transport value model: a
valid term of its type with its carrier in any universe `k` and its family into
any universe `l`, when that type is valid with valid parts. -/
theorem vmodel_valid_iter_at (k l : Tower.Head)
    (validType : ModelS.ValidTyS (vmodel v) .nil (iterTypeAt k l))
    (partsType : ModelS.StructuredS (vmodel v) .nil (iterTypeAt k l)) :
    ModelS.ValidTmS (vmodel v) .nil (.const iterName) (iterTypeAt k l) := by
  have laws := vmodel_laws v
  have vlaws := vmodel_valueLaws v
  obtain ⟨-, validResult, -⟩ := ModelS.ValidTyS.close_parts (iterSucTelescopeAt k l)
    (C := iterResult) validType partsType
  refine ModelS.ValidTmS.close laws (iterSucTelescopeAt k l) (C := iterResult)
    (f := .const iterName) validType partsType ⟨validResult, fun {m r ξ σ σ' ς} e {R} den => ?_⟩
  obtain ⟨⟨⟨⟨⟨⟨-, RN, denN, hN, hNr⟩, RT, -, -, hTr⟩, RF, -, -, hFr⟩,
    RS, denS, hS, hSr⟩, RX, denX, hX, hXr⟩, RE, denE, hE, hEr⟩ := e
  -- The count: a common shape, and a realizer of that shape.
  change ValueSide.DenS (vmodel v).value ξ numT RN at denN
  change RN.rel (σ 5) (σ' 5) at hN
  change (RN.real (σ 5)).mem (ς 5) at hNr
  obtain ⟨sh, hc, hc'⟩ := vnum_shape v denN hN
  have hNr' := (vnum_real v hc denN).mp hNr
  -- The carrier and the family.
  change (RT.real (σ 4)).mem (ς 4) at hTr
  change (RF.real (σ 3)).mem (ς 3) at hFr
  -- The step.
  change ValueSide.DenS (vmodel v).value ξ (Presentation.subst (tailSub (tailSub (tailSub σ)))
    (stepOver (.var 1) (.app (.var 1) (.var 0)))) RS at denS
  rw [subst_stepOver] at denS
  change ValueSide.DenS (vmodel v).value ξ
    (stepOver (σ 4) (.app (Presentation.rename wk (σ 3)) (.var 0))) RS at denS
  change RS.rel (σ 2) (σ' 2) at hS
  change (RS.real (σ 2)).mem (ς 2) at hSr
  -- The value and its evidence.
  change ValueSide.DenS (vmodel v).value ξ (σ 4) RX at denX
  change RX.rel (σ 1) (σ' 1) at hX
  change (RX.real (σ 1)).mem (ς 1) at hXr
  change ValueSide.DenS (vmodel v).value ξ (.app (σ 3) (σ 1)) RE at denE
  rw [← inst0_family] at denE
  change RE.rel (σ 0) (σ' 0) at hE
  change (RE.real (σ 0)).mem (ς 0) at hEr
  change ValueSide.DenS (vmodel v).value ξ
    (.sigma (σ 4) (.app (Presentation.rename wk (σ 3)) (.var 0))) R at den
  show R.rel (iterApp (σ 5) (σ 4) (σ 3) (σ 2) (σ 1) (σ 0))
      (iterApp (σ' 5) (σ' 4) (σ' 3) (σ' 2) (σ' 1) (σ' 0)) ∧
    (R.real (iterApp (σ 5) (σ 4) (σ 3) (σ 2) (σ 1) (σ 0))).mem
      (iterApp (ς 5) (ς 4) (ς 3) (ς 2) (ς 1) (ς 0))
  refine ⟨viter_related v den denS hS sh hc hc'
    (fun d => by rw [ValueSide.DenS.deterministic vlaws d denX]; exact hX)
    (fun d => by rw [ValueSide.DenS.deterministic vlaws d denE]; exact hE), ?_⟩
  exact viter_real v den denS (ValueSide.DenS.refl_left vlaws denS hS) sh hc hNr'
    (KCand.sn _ hTr) (KCand.sn _ hFr) hSr
    (fun d => by
      rw [ValueSide.DenS.deterministic vlaws d denX]
      exact ⟨ValueSide.DenS.refl_left vlaws denX hX, hXr⟩)
    (fun d => by
      rw [ValueSide.DenS.deterministic vlaws d denE]
      exact ⟨ValueSide.DenS.refl_left vlaws denE hE, hEr⟩)

/-- **The iterator is a valid term of its declared type** in the transport value
model, when that type is valid with valid parts: the instance of
`vmodel_valid_iter_at` at the lowest universe. -/
theorem vmodel_valid_iter (validType : ModelS.ValidTyS (vmodel v) .nil iterType)
    (partsType : ModelS.StructuredS (vmodel v) .nil iterType) :
    ModelS.ValidTmS (vmodel v) .nil (.const iterName) iterType :=
  vmodel_valid_iter_at v (.sort Tower.zero) (.sort Tower.zero) validType partsType

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
