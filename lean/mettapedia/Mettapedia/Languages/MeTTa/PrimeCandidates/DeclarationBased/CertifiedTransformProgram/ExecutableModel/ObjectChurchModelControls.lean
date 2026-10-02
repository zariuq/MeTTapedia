import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectChurchJRelation

/-!
# Controls for the object reading

**Positive: closed computations.**

* `add 1 1` denotes `2` (`add_one_one`), by the soundness of a closed derivation of
  `add 1 1 ≡ 2 : num` from the two equations of addition.
* `J num 0 (λ y p. num) 0 0 (refl 0)` denotes `0` (`j_closed`), by the soundness of the
  closed derivation of the eliminator's rule at that spine.
* `num-rec (λ _. num) 0 (λ v r. suc r) 2` denotes `2` (`numRec_two`).
* `iterCert 1 num (λ _. num) (λ x e. (suc x, e)) 0 0` denotes `(1, 0)` (`iter_one`).
* The decoding of the quantified code `all@prop (λ p. p)` is the dependent function type
  over the universe of codes whose value at a code is its decoding (`holds_allProp_id`).

**Negative: a wrong reading of one constant violates the validity of root steps.** Reading
`add` as the Church constant of its second argument (`wrongAddReading`) keeps every constant
an element of its declared type (`wrongAdd_constants`), but at the closed instance
`add 1 0 ⟶ 1` of the zero equation every hypothesis of the root condition holds and the
two sides denote `0` and `1` (`wrongAdd_roots_fail`); so the reading is not valid
(`wrongAdd_not_valid`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.Annotated
open Presentation.TypedEquality.Impredicative.Domain
open Presentation.TypedEquality.Impredicative.Domain.Ideal (projT TypeGenerated principal univIdeal
  codesIdeal natI zeroI groundI cpi csigma clam instPi SpineTyped natRec succI)
open TelescopeAbstraction (applyClosed)
open Package (jName numRecName iterName)

namespace CodeModel
namespace ModelControls

/-! ## Numerals -/

/-- One. -/
def oneI : Ideal := succI zeroI

/-- Two. -/
def twoI : Ideal := succI oneI

theorem oneI_nat : projT natI oneI = oneI := Ideal.projT_natI_succI Ideal.projT_natI_zeroI

theorem twoI_nat : projT natI twoI = twoI := Ideal.projT_natI_succI oneI_nat

theorem app_suc (ν : Ideal) :
    Ideal.app (objectChurchReading.const sucN) ν = succI (projT natI ν) := by
  rw [objectChurchReading_suc]
  exact app_sucConst objectChurchReading numNames objectChurchReading_num ν

theorem cinterp_one {n : Nat} (ρ : Env n) :
    cinterp objectChurchReading (csuc czero : CTm Tower.Head n) ρ = oneI := by
  show Ideal.app (objectChurchReading.const sucN) (objectChurchReading.const zeroN) = oneI
  rw [objectChurchReading_zero, app_suc, Ideal.projT_natI_zeroI]
  rfl

theorem cinterp_two {n : Nat} (ρ : Env n) :
    cinterp objectChurchReading (csuc (csuc czero) : CTm Tower.Head n) ρ = twoI := by
  show Ideal.app (objectChurchReading.const sucN) (cinterp objectChurchReading (csuc czero) ρ) =
    twoI
  rw [cinterp_one, app_suc, oneI_nat]
  rfl

/-! ## Positive: addition -/

/-- `add 1 1 ≡ 2 : num`, by the successor and the zero equation of addition. -/
theorem add_one_one_derivable :
    CEqual objectChurch .nil (cadd (csuc czero) (csuc czero)) (csuc (csuc czero)) cnum := by
  have one : CTyped objectChurch .nil (csuc czero) cnum := csuc_typed czero_typed
  have e₁ : CEqual objectChurch .nil (cadd (csuc czero) (csuc czero))
      (csuc (cadd (csuc czero) czero)) cnum :=
    .rootAdmitted (caddSuc_step _ _) (caddSuc_admits one czero_typed) (cadd_typed one one)
      (csuc_typed (cadd_typed one czero_typed))
  have e₂ : CEqual objectChurch .nil (cadd (csuc czero) czero) (csuc czero) cnum :=
    .rootAdmitted (caddZero_step _) (caddZero_admits one) (cadd_typed one czero_typed) one
  have e₃ : CEqual objectChurch .nil (csuc (cadd (csuc czero) czero)) (csuc (csuc czero)) cnum :=
    CDerivable.appCong (B := cnum) (.refl csucConst_typed) e₂
  exact .trans e₁ e₃

/-- **Positive**: `add 1 1` denotes `2`. -/
theorem add_one_one : Ideal.appSpine (objectChurchReading.const addN) [oneI, oneI] = twoI := by
  have h := CEqual.sound objectChurchReading_valid add_one_one_derivable (ρ := Env.nil) trivial
  change Ideal.appSpine (objectChurchReading.const addN)
    [cinterp objectChurchReading (csuc czero : CTm Tower.Head 0) Env.nil,
      cinterp objectChurchReading (csuc czero : CTm Tower.Head 0) Env.nil] =
    cinterp objectChurchReading (csuc (csuc czero) : CTm Tower.Head 0) Env.nil at h
  rwa [cinterp_one, cinterp_two] at h

/-! ## Positive: the identity eliminator -/

/-- The motive `λ (y : num). λ (p : Id num 0 y). num`, annotated. -/
abbrev cNatMotive : CTm Tower.Head 0 := .lam cnum (.lam (.id cnum czero (.var 0)) cnum)

/-- The spine `J num 0 (λ y p. num) 0 0 (refl 0)`. -/
abbrev cJClosed : CTm Tower.Head 0 :=
  CTm.appSpine (.const jName) [cnum, czero, cNatMotive, czero, czero, .refl czero]

/-- `J num 0 (λ y p. num) 0 0 (refl 0) ≡ 0`, by the eliminator's rule. -/
theorem j_closed_derivable :
    CEqual objectChurch .nil cJClosed czero (.app (.app cNatMotive czero) (.refl czero)) := by
  have formedB : CTyped objectChurch (.snoc .nil cnum) (.id cnum czero (.var 0)) cU0 :=
    cidT cnum_typed czero_typed (.var 0)
  have formed₂ : CTyped objectChurch (.snoc .nil cnum) (.pi (.id cnum czero (.var 0)) cU0) cU1 :=
    cpiT (craise formedB) cU0_typed
  have formed : CTyped objectChurch .nil (.pi cnum (.pi (.id cnum czero (.var 0)) cU0)) cU1 :=
    cpiT (craise cnum_typed) formed₂
  have bodyM : CTyped objectChurch (.snoc (.snoc .nil cnum) (.id cnum czero (.var 0))) cnum cU0 :=
    cnum_typed
  have tM : CTyped objectChurch .nil cNatMotive (.pi cnum (.pi (.id cnum czero (.var 0)) cU0)) :=
    .lamIntro cnum_typed (.sort _) formed (.sort _)
      (.lamIntro formedB (.sort _) formed₂ (.sort _) bodyM)
  have tRefl : CTyped objectChurch .nil (.refl czero) (.id cnum czero czero) :=
    .reflIntro czero_typed
  have td : CTyped objectChurch .nil czero (.app (.app cNatMotive czero) (.refl czero)) :=
    .conv czero_typed (.symm (cbetaTwo formed formed₂ (craise formedB) bodyM czero_typed tRefl))
      (.sort Tower.zero)
  have tJ := cjSpine6_typed (jArgs_mor cnum_typed czero_typed tM td czero_typed tRefl) tRefl
  have mor : CSubstMor objectChurch cJTele .nil (CTm.consSub czero (CTm.consSub czero
      (CTm.consSub czero (CTm.consSub cNatMotive (CTm.consSub czero
        (CTm.consSub cnum Fin.elim0)))))) := fun i => by
    refine Fin.cases ?_ (fun i => ?_) i
    · exact czero_typed
    refine Fin.cases ?_ (fun i => ?_) i
    · exact czero_typed
    refine Fin.cases ?_ (fun i => ?_) i
    · exact td
    refine Fin.cases ?_ (fun i => ?_) i
    · exact tM
    refine Fin.cases ?_ (fun i => ?_) i
    · exact czero_typed
    refine Fin.cases ?_ (fun i => ?_) i
    · exact cnum_typed
    exact i.elim0
  exact .rootAdmitted (objectChurch_jStep (CTm.consSub czero (CTm.consSub czero (CTm.consSub czero
      (CTm.consSub cNatMotive (CTm.consSub czero (CTm.consSub cnum Fin.elim0)))))))
    (objectChurch_jAdmits mor (.refl czero_typed) (.refl czero_typed)) tJ td

/-- **Positive**: `J num 0 (λ y p. num) 0 0 (refl 0)` denotes `0`. -/
theorem j_closed :
    Ideal.appSpine (objectChurchReading.const jName)
      [natI, zeroI, cinterp objectChurchReading cNatMotive Env.nil, zeroI, zeroI,
        Ideal.refl zeroI] =
      zeroI := by
  have h := CEqual.sound objectChurchReading_valid j_closed_derivable (ρ := Env.nil) trivial
  change Ideal.appSpine (objectChurchReading.const jName)
    [objectChurchReading.const numN, objectChurchReading.const zeroN,
      cinterp objectChurchReading cNatMotive Env.nil, objectChurchReading.const zeroN,
      objectChurchReading.const zeroN, Ideal.refl (objectChurchReading.const zeroN)] =
    objectChurchReading.const zeroN at h
  rwa [objectChurchReading_num, objectChurchReading_zero] at h

/-! ## Positive: the decoding of a quantified code -/

/-- **Positive**: the decoding of `all@prop (λ p. p)` is the dependent function type over the
universe of codes whose value at a code is its decoding. -/
theorem holds_allProp_id :
    Ideal.app (objectChurchReading.const holdsN)
      (Ideal.app (objectChurchReading.const allPropN) (clam codesIdeal fun p => p)) =
      cpi codesIdeal fun x => projT codesIdeal x := by
  rw [objectChurchReading_holds, show allPropN = SetProfile.allName .prop from rfl,
    objectChurchReading_all, Ideal.decode_allConst (typeGenerated_simpleI .prop)]
  exact Ideal.cpi_ext fun y hy => by
    rw [Ideal.app_clam Ideal.Cont.id, Ideal.app_holdsConst_eq]
    show projT codesIdeal (projT codesIdeal y) = projT codesIdeal y
    rw [Ideal.projT_projT]

/-! ## Positive: numeral recursion -/

theorem numNames_num : objectChurchReading.const numNames.num = natI := objectChurchReading_num

/-- The motive `λ _. num`. -/
def constMotive : Ideal :=
  projT (cinterp objectChurchReading (.pi cnum cU0) Env.nil) (Ideal.lam fun _ => natI)

theorem app_constMotive (v : Ideal) : Ideal.app constMotive v = natI := by
  rw [constMotive, app_projT_cinterp_pi, Ideal.app_lam_const]
  exact Ideal.projT_univ_eq_self_iff.2 Ideal.typeGenerated_natI

/-- The method `λ v r. suc r`. -/
def sucMethod : Ideal :=
  projT (cinterp objectChurchReading (nrStepTypeC numNames)
      (Env.cons zeroI (Env.cons constMotive Env.nil)))
    (Ideal.lam fun _ => Ideal.lam fun R => succI (principal R))

theorem app_app_sucMethod (v r : Ideal) :
    Ideal.app (Ideal.app sucMethod v) r = succI (projT natI r) := by
  unfold sucMethod nrStepTypeC
  rw [app_projT_cinterp_pi, app_projT_cinterp_pi]
  show projT (Ideal.app constMotive (Ideal.app (objectChurchReading.const sucN)
      (projT (objectChurchReading.const numN) v)))
      (Ideal.app (Ideal.app (Ideal.lam fun _ => Ideal.lam fun R => succI (principal R))
        (projT (objectChurchReading.const numN) v))
        (projT (Ideal.app constMotive (projT (objectChurchReading.const numN) v)) r)) = _
  rw [app_constMotive, app_constMotive, Ideal.app_lam_const,
    Ideal.app_lam_principal Ideal.cont_succI]
  exact Ideal.projT_natI_succI (Ideal.projT_projT _ _)

theorem numRec_spine {x : Ideal} (hx : projT natI x = x) :
    SpineTyped (nrTypeI objectChurchReading numNames) [constMotive, zeroI, sucMethod, x] :=
  (spineTyped_cinterp_pi objectChurchReading _ _ _ _ _).2 ⟨Ideal.projT_projT _ _,
    (spineTyped_cinterp_pi objectChurchReading _ _ _ _ _).2 ⟨by
        show projT (Ideal.app constMotive (objectChurchReading.const zeroN)) zeroI = zeroI
        rw [app_constMotive, Ideal.projT_natI_zeroI],
      (spineTyped_cinterp_pi objectChurchReading _ _ _ _ _).2 ⟨Ideal.projT_projT _ _,
        (spineTyped_cinterp_pi objectChurchReading _ _ _ _ _).2 ⟨by
            show projT (objectChurchReading.const numN) x = x
            rw [objectChurchReading_num, hx], trivial⟩⟩⟩⟩

theorem numRec_prefix :
    SpineTyped (nrTypeI objectChurchReading numNames) [constMotive, zeroI, sucMethod] :=
  ((Ideal.spineTyped_append (args := [constMotive, zeroI, sucMethod]) (args' := [zeroI])).1
    (numRec_spine Ideal.projT_natI_zeroI)).1

theorem numRec_zero :
    Ideal.appSpine (nrConst objectChurchReading numNames) [constMotive, zeroI, sucMethod, zeroI] =
      zeroI := by
  refine nrConst_iotaZero ⟨rfl, numRec_spine Ideal.projT_natI_zeroI⟩ ?_
  rw [instPi_nr numRec_prefix, numNames_num, Ideal.projT_natI_zeroI, app_constMotive,
    Ideal.projT_natI_zeroI]

/-- The successor rule at `λ _. num`, `0` and `λ v r. suc r`. -/
theorem numRec_succ {ν r : Ideal} (hν : projT natI ν = ν)
    (hrec :
      Ideal.appSpine (nrConst objectChurchReading numNames) [constMotive, zeroI, sucMethod, ν] = r)
    (hr : projT natI r = r) :
    Ideal.appSpine (nrConst objectChurchReading numNames)
        [constMotive, zeroI, sucMethod, succI ν] =
      succI r := by
  have hsuc : Ideal.app (sucConst objectChurchReading numNames) ν = succI ν := by
    rw [app_sucConst objectChurchReading numNames objectChurchReading_num, hν]
  have spine : SpineTyped (nrTypeI objectChurchReading numNames)
      [constMotive, zeroI, sucMethod, Ideal.app (sucConst objectChurchReading numNames) ν] := by
    rw [hsuc]
    exact numRec_spine (Ideal.projT_natI_succI hν)
  have e : Ideal.app (Ideal.app sucMethod ν) (Ideal.appSpine (nrConst objectChurchReading numNames)
      [constMotive, zeroI, sucMethod, ν]) = succI r := by
    rw [hrec, app_app_sucMethod, hr]
  have right : projT (instPi (nrTypeI objectChurchReading numNames)
      [constMotive, zeroI, sucMethod, Ideal.app (sucConst objectChurchReading numNames) ν])
      (Ideal.app (Ideal.app sucMethod ν) (Ideal.appSpine (nrConst objectChurchReading numNames)
        [constMotive, zeroI, sucMethod, ν])) =
      Ideal.app (Ideal.app sucMethod ν) (Ideal.appSpine (nrConst objectChurchReading numNames)
        [constMotive, zeroI, sucMethod, ν]) := by
    rw [e, instPi_nr numRec_prefix, numNames_num, hsuc, Ideal.projT_natI_succI hν,
      app_constMotive, Ideal.projT_natI_succI hr]
  have key := nrConst_iotaSucc objectChurchReading_num ⟨rfl, spine⟩ right
  rw [hsuc, e] at key
  exact key

/-- **Positive**: `num-rec (λ _. num) 0 (λ v r. suc r) 2` denotes `2`. -/
theorem numRec_two :
    Ideal.appSpine (objectChurchReading.const numRecName) [constMotive, zeroI, sucMethod, twoI] =
      twoI := by
  rw [objectChurchReading_numRec]
  exact numRec_succ oneI_nat (numRec_succ Ideal.projT_natI_zeroI numRec_zero Ideal.projT_natI_zeroI)
    oneI_nat

/-! ## Positive: the iterator -/

/-- The step `λ x e. (suc x, e)` over the numbers and the family `λ _. num`. -/
def sucPairStep : Ideal :=
  projT (cinterp objectChurchReading cStep (Env.cons constMotive (Env.cons natI Env.nil)))
    (Ideal.lam fun X => Ideal.lam fun E => Ideal.pair (succI (principal X)) (principal E))

theorem cont_constMotive : Ideal.Cont fun y => Ideal.app constMotive y :=
  Ideal.cont₂_app.right constMotive

/-- The pairs of a number with its evidence under `λ _. num`. -/
abbrev natPairs : Ideal := csigma natI fun y => Ideal.app constMotive y

theorem natPair_typed {a b : Ideal} (ha : projT natI a = a) (hb : projT natI b = b) :
    projT natPairs (Ideal.pair a b) = Ideal.pair a b :=
  Ideal.semTyped_pair cont_constMotive ha (by rw [app_constMotive]; exact hb)

theorem app_app_sucPairStep (x e : Ideal) :
    Ideal.app (Ideal.app sucPairStep x) e =
      projT natPairs (Ideal.pair (succI (projT natI x)) (projT natI e)) := by
  have hX : Ideal.Cont fun X => Ideal.lam fun E => Ideal.pair (succI X) (principal E) :=
    Ideal.cont_lam_param fun E => (Ideal.cont₂_pair.left (principal E)).comp Ideal.cont_succI
  have hE (z : Ideal) : Ideal.Cont fun E => Ideal.pair z E := Ideal.cont₂_pair.right z
  unfold sucPairStep cStep
  rw [app_projT_cinterp_pi, app_projT_cinterp_pi]
  show projT (csigma natI fun y => Ideal.app constMotive y)
      (Ideal.app (Ideal.app (Ideal.lam fun X => Ideal.lam fun E =>
        Ideal.pair (succI (principal X)) (principal E)) (projT natI x))
        (projT (Ideal.app constMotive (projT natI x)) e)) = _
  rw [Ideal.app_lam_principal hX, Ideal.app_lam_principal (hE _), app_constMotive]

/-- The spine facts of the iterator's parameters after its count, at the numbers, the
family `λ _. num`, the step `λ x e. (suc x, e)`, and numbers `x` and `e`. -/
theorem iter_tail_spine {x e : Ideal} (hx : projT natI x = x) (he : projT natI e = e) :
    SpineTyped (cinterp objectChurchReading iterTail Env.nil)
      [natI, constMotive, sucPairStep, x, e] := by
  show SpineTyped (cinterp objectChurchReading (.pi cU0 (.pi (.pi (.var 0) cU0) (.pi cStep
    (.pi (.var 2) (.pi (.app (.var 2) (.var 0)) iterCod))))) Env.nil) _
  refine (spineTyped_cinterp_pi objectChurchReading _ _ _ _ _).2 ⟨?_, ?_⟩
  · exact Ideal.projT_univ_eq_self_iff.2 Ideal.typeGenerated_natI
  refine (spineTyped_cinterp_pi objectChurchReading _ _ _ _ _).2 ⟨?_, ?_⟩
  · show projT (cpi natI fun _ => univIdeal) constMotive = constMotive
    unfold constMotive
    rw [show cinterp objectChurchReading (.pi cnum cU0 : CTm Tower.Head 0) Env.nil =
      cpi natI fun _ => univIdeal from by
        show (cpi (objectChurchReading.const numN) fun _ => univIdeal) = _
        rw [objectChurchReading_num]]
    exact Ideal.projT_projT _ _
  refine (spineTyped_cinterp_pi objectChurchReading _ _ _ _ _).2 ⟨Ideal.projT_projT _ _, ?_⟩
  refine (spineTyped_cinterp_pi objectChurchReading _ _ _ _ _).2 ⟨hx, ?_⟩
  refine (spineTyped_cinterp_pi objectChurchReading _ _ _ _ _).2 ⟨?_, trivial⟩
  show projT (Ideal.app constMotive x) e = e
  rw [app_constMotive, he]

/-- The iterator's type at a count, instantiated at these parameters, is the pairs of a
number with its evidence. -/
theorem iterTail_instPi {x e : Ideal} (hx : projT natI x = x) (he : projT natI e = e) :
    instPi (cinterp objectChurchReading iterTail Env.nil) [natI, constMotive, sucPairStep, x, e] =
      natPairs := by
  have spine := iter_tail_spine hx he
  show instPi (cinterp objectChurchReading (.pi cU0 (.pi (.pi (.var 0) cU0) (.pi cStep
    (.pi (.var 2) (.pi (.app (.var 2) (.var 0)) iterCod))))) Env.nil) _ = _
  obtain ⟨h1, s1⟩ := (spineTyped_cinterp_pi objectChurchReading _ _ _ _ _).1 spine
  obtain ⟨h2, s2⟩ := (spineTyped_cinterp_pi objectChurchReading _ _ _ _ _).1 s1
  obtain ⟨h3, s3⟩ := (spineTyped_cinterp_pi objectChurchReading _ _ _ _ _).1 s2
  obtain ⟨h4, s4⟩ := (spineTyped_cinterp_pi objectChurchReading _ _ _ _ _).1 s3
  obtain ⟨h5, -⟩ := (spineTyped_cinterp_pi objectChurchReading _ _ _ _ _).1 s4
  rw [instPi_cinterp_pi_of objectChurchReading _ h1, instPi_cinterp_pi_of objectChurchReading _ h2,
    instPi_cinterp_pi_of objectChurchReading _ h3, instPi_cinterp_pi_of objectChurchReading _ h4,
    instPi_cinterp_pi_of objectChurchReading [] h5]
  rfl

/-- **Positive**: `iterCert 1 num (λ _. num) (λ x e. (suc x, e)) 0 0` denotes `(1, 0)`. -/
theorem iter_one :
    Ideal.appSpine (objectChurchReading.const iterName)
      [oneI, natI, constMotive, sucPairStep, zeroI, zeroI] = Ideal.pair oneI zeroI := by
  have tail := iter_tail_spine Ideal.projT_natI_zeroI Ideal.projT_natI_zeroI
  have spine : SpineTyped (cinterp objectChurchReading (liftTm Package.iterType) Env.nil)
      ([oneI] ++ [natI, constMotive, sucPairStep, zeroI, zeroI]) := by
    refine Ideal.spineTyped_append.2 ⟨?_, ?_⟩
    · rw [iterType_eq]
      exact (spineTyped_cinterp_pi objectChurchReading cnum _ Env.nil oneI []).2
        ⟨by rw [cinterp_cnum]; exact oneI_nat, trivial⟩
    · rw [instPi_iterType]
      exact tail
  have hstep : Ideal.app (Ideal.app sucPairStep zeroI) zeroI = Ideal.pair oneI zeroI := by
    rw [app_app_sucPairStep, Ideal.projT_natI_zeroI]
    exact natPair_typed oneI_nat Ideal.projT_natI_zeroI
  have spine5 := iter_tail_spine oneI_nat Ideal.projT_natI_zeroI
  have hzero : Ideal.app (Ideal.app (Ideal.appSpine
      (projT (cinterp objectChurchReading iterTail Env.nil) (iterZero objectChurchReading))
      [natI, constMotive, sucPairStep]) oneI) zeroI = Ideal.pair oneI zeroI := by
    change Ideal.appSpine
      (projT (cinterp objectChurchReading iterTail Env.nil) (iterZero objectChurchReading))
      [natI, constMotive, sucPairStep, oneI, zeroI] = _
    rw [Ideal.appSpine_churchConst _ (churchTele_cinterp objectChurchReading iterTail Env.nil)
      (by show 5 ≤ 5; omega) spine5, iterTail_instPi oneI_nat Ideal.projT_natI_zeroI,
      iterZero_apply spine5]
    exact natPair_typed oneI_nat Ideal.projT_natI_zeroI
  have hF : Ideal.Cont fun pk => Ideal.app (Ideal.app (Ideal.appSpine (projT
      (cinterp objectChurchReading iterTail Env.nil) (iterZero objectChurchReading))
      [natI, constMotive, sucPairStep]) (Ideal.fst pk)) (Ideal.snd pk) :=
    Ideal.cont₂_app.comp ((Ideal.cont₂_app.right _).comp Ideal.cont_fst) Ideal.cont_snd
  rw [objectChurchReading_iter]
  refine Ideal.churchConst_root (churchTele_cinterp objectChurchReading _ Env.nil)
    (by show 6 ≤ 6; omega) spine ?_ ?_
  · change Ideal.appSpine (Ideal.app (iterRaw objectChurchReading) (succI zeroI))
      [natI, constMotive, sucPairStep, zeroI, zeroI] = _
    rw [app_iterRaw, Ideal.natRec_succI (cont₂_constStep _),
      Ideal.natRec_zeroI (cont₂_constStep _)]
    change Ideal.appSpine (iterSucc objectChurchReading)
      [iterZero objectChurchReading, natI, constMotive, sucPairStep, zeroI, zeroI] = _
    rw [iterSucc_apply tail, hstep, Ideal.app_clam hF,
      natPair_typed oneI_nat Ideal.projT_natI_zeroI, Ideal.fst_pair, Ideal.snd_pair, hzero]
  · rw [show [oneI, natI, constMotive, sucPairStep, zeroI, zeroI] =
      [oneI] ++ [natI, constMotive, sucPairStep, zeroI, zeroI] from rfl, Ideal.instPi_append,
      instPi_iterType, iterTail_instPi Ideal.projT_natI_zeroI Ideal.projT_natI_zeroI]
    exact natPair_typed oneI_nat Ideal.projT_natI_zeroI

/-! ## Negative: a wrong reading of addition -/

/-- The function returning its second argument. -/
def secondRaw : Ideal := Ideal.lam fun _ => Ideal.lam fun M => principal M

/-- **A wrong reading**: `add` read as the Church constant of its second argument, every other
constant as in the object reading. -/
def wrongAddReading : Reading Tower.Head :=
  ⟨objectHead, fun c => if c = addN then
    projT (cinterp objectChurchReading (liftTm addType) Env.nil) secondRaw
    else objectChurchReading.const c⟩

theorem wrongAdd_add :
    wrongAddReading.const addN =
      projT (cinterp objectChurchReading (liftTm addType) Env.nil) secondRaw := by
  show (if addN = addN then projT (cinterp objectChurchReading (liftTm addType) Env.nil) secondRaw
    else objectChurchReading.const addN) = _
  exact if_pos rfl

theorem wrongAdd_other {c : DeclName} (h : c ≠ addN) :
    wrongAddReading.const c = objectChurchReading.const c := by
  show (if c = addN then projT (cinterp objectChurchReading (liftTm addType) Env.nil) secondRaw
    else objectChurchReading.const c) = _
  exact if_neg h

/-- The wrong reading interprets every term without addition as the object reading does. -/
theorem wrongAdd_cinterp {n : Nat} (t : CTm Tower.Head n) (h : addN ∉ termConsts t) :
    cinterp wrongAddReading t = cinterp objectChurchReading t :=
  cinterp_congr (Rd := wrongAddReading) (Rd' := objectChurchReading) rfl t fun _ hc =>
    wrongAdd_other fun e => h (e ▸ hc)

/-- No declared type mentions addition. -/
theorem addN_not_mem_declType (tag : ObjConst) : addN ∉ termConsts tag.declType := by
  intro h
  have hs := stagedBelow_declType tag addN h
  cases tag with
  | all type =>
      rcases termConsts_typeAt (.arr (.arr type .prop) .prop) (n := 0) h with e | e | e <;>
        exact absurd e (by decide)
  | eq type =>
      rcases termConsts_typeAt (.arr type (.arr type .prop)) (n := 0) h with e | e | e <;>
        exact absurd e (by decide)
  | num => exact absurd hs (by decide)
  | set => exact absurd hs (by decide)
  | prop => exact absurd hs (by decide)
  | other => exact absurd hs (by decide)
  | zero => exact absurd hs (by decide)
  | suc => exact absurd hs (by decide)
  | add => exact absurd hs (by decide)
  | power => exact absurd hs (by decide)
  | j => exact absurd hs (by decide)
  | keep => exact absurd hs (by decide)
  | transport => exact absurd hs (by decide)
  | compose => exact absurd hs (by decide)
  | holds => exact absurd hs (by decide)
  | imp => exact absurd hs (by decide)
  | pow => exact absurd h (by decide)
  | numRec => exact absurd h (by decide)
  | iter => exact absurd h (by decide)
  | eqAt => exact absurd h (by decide)
  | sucMove => exact absurd h (by decide)
  | returnIter => exact absurd h (by decide)
  | sucStep => exact absurd h (by decide)

/-- **The wrong reading keeps every constant an element of its declared type.** -/
theorem wrongAdd_constants {c : DeclName} {D : CTm Tower.Head 0}
    (declared : objectChurch.constantType c = some D) :
    projT (cinterp wrongAddReading D Env.nil) (wrongAddReading.const c) =
      wrongAddReading.const c := by
  have hD := declType_of_declared declared
  rw [wrongAdd_cinterp D (hD ▸ addN_not_mem_declType _)]
  by_cases hc : c = addN
  · subst hc
    rw [wrongAdd_add, hD, show (objConst addN).declType = liftTm addType from rfl]
    exact Ideal.projT_projT _ _
  · rw [wrongAdd_other hc]
    exact objectChurchReading_constants declared

/-- The declared types of the constants of the instance. -/
theorem declared_of {c : DeclName} {D : CTm Tower.Head 0} (tag : ObjConst) (htag : objConst c = tag)
    (declared : objectChurch.constantType c = some D) : D = tag.declType := by
  rw [declType_of_declared declared, htag]

theorem spineFacts_const {c : DeclName} (tag : ObjConst) (htag : objConst c = tag) {n : Nat}
    {ρ : Env n} :
    SpineFacts wrongAddReading objectChurch (.const c)
      (cinterp objectChurchReading tag.declType Env.nil) ρ :=
  fun D declared => by
    rw [declared_of tag htag declared, wrongAdd_cinterp _ (addN_not_mem_declType tag)]

theorem wrong_sucConst : wrongAddReading.const sucN = sucConst objectChurchReading numNames := by
  rw [wrongAdd_other (by decide), objectChurchReading_suc]

theorem sucType_eq :
    cinterp objectChurchReading (liftTm (.pi Package.numT Package.numT) : CTm Tower.Head 0)
      Env.nil = cpi natI fun _ => natI := by
  show (cpi (objectChurchReading.const numN) fun _ => objectChurchReading.const numN) = _
  rw [objectChurchReading_num]

theorem sucTypeC_eq :
    cinterp objectChurchReading (sucTypeC numNames) Env.nil = cpi natI fun _ => natI :=
  sucType_eq

theorem addType_eq : cinterp objectChurchReading (liftTm addType : CTm Tower.Head 0) Env.nil =
    cpi natI fun _ => cpi natI fun _ => natI := by
  show (cpi (objectChurchReading.const numN) fun _ => cpi (objectChurchReading.const numN) fun _ =>
    objectChurchReading.const numN) = _
  rw [objectChurchReading_num]

/-- The spine facts of `1` at the numbers, in the wrong reading. -/
theorem spineFacts_one :
    SpineFacts wrongAddReading objectChurch (csuc czero : CTm Tower.Head 0) natI Env.nil := by
  refine ⟨natI, fun _ => natI, Ideal.Cont.const _, rfl, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · show projT (cpi natI fun _ => natI) (wrongAddReading.const sucN) = wrongAddReading.const sucN
    rw [wrong_sucConst, sucConst, sucTypeC_eq]
    exact Ideal.projT_projT _ _
  · have h := spineFacts_const (c := sucN) .suc (by decide) (ρ := Env.nil)
    rwa [show ObjConst.suc.declType = liftTm (.pi Package.numT Package.numT) from rfl,
      sucType_eq] at h
  · show projT natI (wrongAddReading.const zeroN) = wrongAddReading.const zeroN
    rw [wrongAdd_other (by decide), objectChurchReading_zero]
    exact Ideal.projT_natI_zeroI
  · have h := spineFacts_const (c := zeroN) .zero (by decide) (ρ := Env.nil)
    rwa [show ObjConst.zero.declType = cnum from rfl, cinterp_cnum] at h

theorem wrong_one : cinterp wrongAddReading (csuc czero : CTm Tower.Head 0) Env.nil = oneI := by
  rw [wrongAdd_cinterp _ (by decide)]
  exact cinterp_one Env.nil

theorem wrong_add_apply {a b : Ideal} (ha : projT natI a = a) (hb : projT natI b = b) :
    Ideal.appSpine (wrongAddReading.const addN) [a, b] = b := by
  have spine : SpineTyped (cpi natI fun _ => cpi natI fun _ => natI) [a, b] :=
    ⟨by rw [Ideal.dom_cpi]; exact ha, by
      rw [Ideal.dom_cpi, Ideal.fam_cpi (Ideal.Cont.const _)]
      exact ⟨by rw [Ideal.dom_cpi]; exact hb, trivial⟩⟩
  have hT : Ideal.ChurchTele 2 (cpi natI fun _ => cpi natI fun _ => natI) := by
    have h := churchTele_cinterp objectChurchReading (liftTm addType) Env.nil
    rwa [addType_eq] at h
  rw [wrongAdd_add, addType_eq]
  refine Ideal.churchConst_root hT (Nat.le_refl _) spine ?_ ?_
  · show Ideal.app (Ideal.app (Ideal.lam fun _ => Ideal.lam fun M => principal M) a) b = b
    rw [Ideal.app_lam_const, Ideal.app_lam_principal Ideal.Cont.id]
  · show projT (instPi (Ideal.fam .pi (cpi natI fun _ => cpi natI fun _ => natI)
      (projT (Ideal.dom .pi (cpi natI fun _ => cpi natI fun _ => natI)) a)) [b]) b = b
    rw [Ideal.dom_cpi, Ideal.fam_cpi (Ideal.Cont.const _)]
    show projT (Ideal.fam .pi (cpi natI fun _ => natI)
      (projT (Ideal.dom .pi (cpi natI fun _ => natI)) b)) b = b
    rw [Ideal.dom_cpi, Ideal.fam_cpi (Ideal.Cont.const _)]
    exact hb

/-- **Negative**: the wrong reading of addition violates the validity of root steps. At the
closed instance `add 1 0 ⟶ 1` of the zero equation, the type is the numbers, both sides are
elements of it with their spine facts there, and the two sides denote `0` and `1`. -/
theorem wrongAdd_roots_fail :
    ¬ (∀ {n : Nat} {l r : CTm Tower.Head n} {τ : Ideal} {ρ : Env n},
      objectChurch.computation.step l r → TypeGenerated τ →
      projT τ (cinterp wrongAddReading l ρ) = cinterp wrongAddReading l ρ →
      SpineFacts wrongAddReading objectChurch l τ ρ →
      projT τ (cinterp wrongAddReading r ρ) = cinterp wrongAddReading r ρ →
      SpineFacts wrongAddReading objectChurch r τ ρ →
      cinterp wrongAddReading l ρ = cinterp wrongAddReading r ρ) := by
  intro roots
  have hl :
      cinterp wrongAddReading (cadd (csuc czero) czero : CTm Tower.Head 0) Env.nil = zeroI := by
    show Ideal.appSpine (wrongAddReading.const addN)
      [cinterp wrongAddReading (csuc czero : CTm Tower.Head 0) Env.nil,
        wrongAddReading.const zeroN] = zeroI
    rw [wrong_one, wrongAdd_other (c := zeroN) (by decide), objectChurchReading_zero]
    exact wrong_add_apply oneI_nat Ideal.projT_natI_zeroI
  have hadd : projT (cpi natI fun _ => cpi natI fun _ => natI) (wrongAddReading.const addN) =
      wrongAddReading.const addN := by
    rw [wrongAdd_add, addType_eq]
    exact Ideal.projT_projT _ _
  have sl : SpineFacts wrongAddReading objectChurch (cadd (csuc czero) czero : CTm Tower.Head 0)
      natI Env.nil := by
    refine ⟨natI, fun _ => natI, Ideal.Cont.const _, rfl, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · show projT (cpi natI fun _ => natI) (Ideal.app (wrongAddReading.const addN)
        (cinterp wrongAddReading (csuc czero : CTm Tower.Head 0) Env.nil)) =
        Ideal.app (wrongAddReading.const addN)
          (cinterp wrongAddReading (csuc czero : CTm Tower.Head 0) Env.nil)
      rw [wrong_one]
      exact Ideal.semTyped_app (G := fun _ => cpi natI fun _ => natI) (Ideal.Cont.const _) hadd
        oneI_nat
    · refine ⟨natI, fun _ => cpi natI fun _ => natI, Ideal.Cont.const _, rfl, ⟨hadd, ?_⟩,
        ⟨?_, spineFacts_one⟩⟩
      · have h := spineFacts_const (c := addN) .add (by decide) (ρ := Env.nil)
        rwa [show ObjConst.add.declType = liftTm addType from rfl, addType_eq] at h
      · rw [wrong_one]
        exact oneI_nat
    · show projT natI (wrongAddReading.const zeroN) = wrongAddReading.const zeroN
      rw [wrongAdd_other (by decide), objectChurchReading_zero]
      exact Ideal.projT_natI_zeroI
    · have h := spineFacts_const (c := zeroN) .zero (by decide) (ρ := Env.nil)
      rwa [show ObjConst.zero.declType = cnum from rfl, cinterp_cnum] at h
  have h := roots (caddZero_step (csuc czero)) Ideal.typeGenerated_natI
    (by rw [hl]; exact Ideal.projT_natI_zeroI) sl (by rw [wrong_one]; exact oneI_nat) spineFacts_one
  rw [hl, wrong_one] at h
  exact Ideal.succI_not_mem_tag (by decide) zeroI (h ▸ Ideal.zeroI_mem_zero)

/-- **Negative**: the wrong reading of addition is not valid. -/
theorem wrongAdd_not_valid : ¬ ReadingValid wrongAddReading objectChurch :=
  fun valid => wrongAdd_roots_fail valid.roots

end ModelControls
end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
