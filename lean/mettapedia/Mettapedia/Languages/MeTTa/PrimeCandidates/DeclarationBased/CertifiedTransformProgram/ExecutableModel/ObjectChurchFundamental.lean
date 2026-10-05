import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectChurchConstants
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.LogicalRelationFundamental

/-!
# The fundamental lemma at the object package, stage by stage

Every statement here is about a package containing the object package (`ObjectExtension`),
the object package itself among them. The fundamental lemma within adequate constants of the
object package is `ObjectExtension.valid_within`.

**Stage 0: the numbers.** `num`, `zero` and `suc` are adequate (`constAdequateAt_num`,
`constAdequateAt_zero`, `constAdequateAt_suc`). **Addition** is adequate
(`constAdequateAt_add`): by recursion on the approximants of its numeral recursion, at
numbers related as far as its second argument observes, `add m q` is related to
`add m' q'` (`add_claim`), along the zero and successor equations and the congruence at
its second argument.

**Stage 1: `eqAt`** is adequate (`constAdequateAt_eqAt`): its right side
`Id num (add zero n) n` is typed within `num`, `zero`, `suc` and `add`
(`ceqAtRhs_typed_within`), so the fundamental lemma makes it valid.

**The identity eliminator** is adequate (`constAdequateAt_j`): its spine at the variables
of its telescope is adequate by the eliminator's case (`Adequate.objectJ_head`).

**Stage 2: the successor move** is adequate, with no hypothesis
(`constAdequateAt_sucMove'`): its right side is typed within `num`, `zero`, `suc`, `add`,
`J` and `eqAt` (`csucMoveRhs_typed_within`), so the fundamental lemma makes the typing valid
(`csucMoveRhs_valid`), which is the one hypothesis of `constAdequateAt_sucMove`.
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
open Presentation.TypedEquality.Impredicative.Domain.Ideal
  (projT TypedAt principal natRecApprox natRec natI)
open TelescopeAbstraction (applyClosed)
open FormationSensitiveHOLInterface (typeAt)
open Package (jName eqAtName sucMoveName)
open Mettapedia.Logic

namespace CodeModel

variable (X : ObjectExtension)

/-- The constants of a list are adequate when each is. -/
theorem consts_allowedIn {R' : Rules Tower.Head} {P : ChurchRules R'} {K : RigidTypes P}
    {Rd : Reading Tower.Head} {H : HeadReduction P K} {names : List DeclName}
    (h : ∀ c ∈ names, ConstAdequateAt Rd H c) :
    ∀ {c : DeclName}, allowedIn names c = true → ConstAdequateAt Rd H c :=
  fun hc => h _ (of_decide_eq_true hc)

/-! ## Stage 0: the numbers -/

section Numbers

/-- **`num` is adequate**: the numbers are an adequate type of `U₀`. -/
theorem constAdequateAt_num : ConstAdequateAt X.reading X.head numN :=
  ConstAdequateAt.of_adequate
    (X.sub.constantType (objectChurch_declared (c := numN) (T := Package.U0) (by decide) rfl))
    ((adequateType_typeAt X (.base .num) (.nil : CCtx Tower.Head 0)).adequate X.levels
      X.soundnessFacts (X.sort Tower.zero))

/-- **`zero` is adequate.** -/
theorem constAdequateAt_zero : ConstAdequateAt X.reading X.head zeroN :=
  ConstAdequateAt.of_adequate
    (X.sub.constantType (objectChurch_declared (c := zeroN) (T := Package.numT) (by decide) rfl))
    (adequate_czero X)

/-- The relation of a variable of type `num`, at every token of the projection of its value
onto the numbers. -/
theorem SubstRel.numVar {n m : Nat} {Γ : CCtx Tower.Head n} {ρ : Env n}
    {Δ : CCtx Tower.Head m} {σ σ' : CSub Tower.Head n m} {i : Fin n} (hi : Γ.lookup i = cnum)
    (hσ : SubstRel X.reading X.head Γ ρ Δ σ σ') :
    ∀ y, (projT natI (ρ i)).Mem y → RT X.head Δ true y cnum (σ i) (σ' i) := by
  intro y hy
  obtain ⟨v, hv, hvT, e⟩ := Ideal.projT_eq_iSup.1 hy
  refine RT.closed' e fun t ht => ?_
  have h := (hσ.2 i).2.2 t (hv t ht) (by rw [hi, X.cinterp_cnum]; exact hvT t ht)
  rwa [hi] at h

/-- **The successor at an adequate number is adequate**: a token of a successor is its tag
or a predecessor token of a token of the projection of its argument onto the numbers, at
which the arguments are related. -/
theorem adequate_sucVar :
    Adequate X.reading X.head (.snoc .nil cnum) (csuc (.var 0)) cnum := by
  intro ρ fits m Δ σ σ' formed hσ s hs _
  change (Ideal.app (X.reading.const sucN) (ρ 0)).Mem s at hs
  rw [X.reading_const (by decide), objectChurchReading_suc, app_sucConst objectChurchReading numNames
    objectChurchReading_num] at hs
  have h0 := SubstRel.numVar X (i := 0) rfl hσ
  have e0 : CEqual X.church Δ (σ 0) (σ' 0) cnum := hσ.1.2 0
  obtain ⟨t0, t0'⟩ := CEqual.typed X.levels e0 formed
  have red : SuccRed X.head Δ cnum (csuc (σ 0)) (csuc (σ' 0)) (σ 0) (σ' 0) :=
    ⟨CRedTy.refl ⟨_, X.sort _, X.lift cnum_typed⟩,
      CRedTm.refl (.appElim (B := cnum) (X.lift csucConst_typed) t0),
      CRedTm.refl (.appElim (B := cnum) (X.lift csucConst_typed) t0'), e0⟩
  obtain ⟨v, hv, e⟩ := hs
  refine RT.closed' e fun t ht => ?_
  rcases hv t ht with rfl | ⟨r, rfl, hr⟩
  · exact RT.tm_succTag_iff.2 ⟨_, _, red⟩
  · exact RT.tm_argSucc_iff.2 (.inr ⟨_, _, red, fun _ h => absurd h List.not_mem_nil,
      fun _ => h0 r hr⟩)

/-- **`suc` is adequate**, from its spine at a variable. -/
theorem constAdequateAt_suc : ConstAdequateAt X.reading X.head sucN :=
  ConstAdequateAt.of_spine (Θ := .snoc .nil cnum) (T := cnum) X.levels X.soundnessFacts
    (X.sub.constantType
      (objectChurch_declared (c := sucN) (T := .pi Package.numT Package.numT) (by decide) rfl))
    (X.lift (csuc_typed (.var 0))) (adequate_sucVar X)

end Numbers

/-! ## Stage 0: addition -/

section Addition

/-- The successor step of the numeral recursion of addition. -/
abbrev addRecStep : Ideal → Ideal → Ideal :=
  fun _ r => Ideal.app (sucConst objectChurchReading numNames) r

/-- **The denotation of a sum**: the numeral recursion of addition on the projection of the
second summand onto the numbers, from the projection of the first, projected onto the
numbers. -/
theorem cinterp_cadd {n : Nat} (x y : CTm Tower.Head n) (ρ : Env n) :
    cinterp X.reading (cadd x y) ρ =
      projT natI (natRec (projT natI (cinterp X.reading x ρ)) addRecStep
        (projT natI (cinterp X.reading y ρ))) := by
  change Ideal.app (Ideal.app (X.reading.const addN) _) _ = _
  rw [X.reading_const (by decide), objectChurchReading_add]
  change Ideal.app (Ideal.app (projT (Ideal.cpi natI fun _ => Ideal.cpi natI fun _ => natI)
    (addRaw (sucConst objectChurchReading numNames))) _) _ = _
  rw [Ideal.app_projT_cpi (Ideal.Cont.const _)]
  change Ideal.app (projT (Ideal.cpi natI fun _ => natI) _) _ = _
  rw [Ideal.app_projT_cpi (Ideal.Cont.const _)]
  change projT natI (Ideal.appSpine (addRaw (sucConst objectChurchReading numNames)) [_, _]) = _
  rw [appSpine_addRaw]

variable {m : Nat} {Δ : CCtx Tower.Head m}

/-- The typed reduction of a sum whose second summand reduces to zero, to the first. -/
theorem CRedTm.addZero {M Q : CTm Tower.Head m} (tM : CTyped X.church Δ M cnum)
    (hQ : CRedTm X.head Δ Q czero cnum) :
    CRedTm X.head Δ (cadd M Q) M cnum := by
  refine ⟨(Relation.ReflTransGen.lift (fun q => cadd M q) (fun _ _ s => X.head_add s)
    _ _ hQ.1).tail (X.head.root (X.within.step (caddZero_step M))), ?_⟩
  exact .trans (.appCong (A := cnum) (B := cnum)
    (.refl (.appElim (B := .pi cnum cnum) (X.lift caddConst_typed) tM)) hQ.2)
    (.rootAdmitted (X.within.step (caddZero_step M)) (caddZero_admits tM X.within)
      (X.cadd_typed tM (X.lift czero_typed)) tM)

/-- The typed reduction of a sum whose second summand reduces to a successor. -/
theorem CRedTm.addSuc {M Q q : CTm Tower.Head m} (tM : CTyped X.church Δ M cnum)
    (tq : CTyped X.church Δ q cnum) (hQ : CRedTm X.head Δ Q (csuc q) cnum) :
    CRedTm X.head Δ (cadd M Q) (csuc (cadd M q)) cnum := by
  refine ⟨(Relation.ReflTransGen.lift (fun q => cadd M q) (fun _ _ s => X.head_add s)
    _ _ hQ.1).tail (X.head.root (X.within.step (caddSuc_step M q))), ?_⟩
  exact .trans (.appCong (A := cnum) (B := cnum)
    (.refl (.appElim (B := .pi cnum cnum) (X.lift caddConst_typed) tM)) hQ.2)
    (.rootAdmitted (X.within.step (caddSuc_step M q)) (caddSuc_admits tM tq X.within)
      (X.cadd_typed tM (X.csuc_typed tq)) (X.csuc_typed (X.cadd_typed tM tq)))

/-- **Addition, by recursion on the approximants of its numeral recursion.** Let the first
summands be related as far as the zero case observes. For second summands related as far
as a numeral observes, the sums are related as far as every token of the `k`-th
approximant of the recursion at the numeral observes: at zero both sums reduce to the
first summands, and at a successor to successors of the sums at the predecessors, related
by the recursion at `k`. -/
theorem add_claim (formed : CCtxFormed X.church Δ) {z : Ideal} {M M' : CTm Tower.Head m}
    (eM : CEqual X.church Δ M M' cnum)
    (hz : ∀ y, z.Mem y → RT X.head Δ true y cnum M M') :
    ∀ (k : Nat) (ν : Ideal) (Q Q' : CTm Tower.Head m), CEqual X.church Δ Q Q' cnum →
      (∀ x, ν.Mem x → RT X.head Δ true x cnum Q Q') →
      ∀ y, (natRecApprox z addRecStep k ν).Mem y →
        RT X.head Δ true y cnum (cadd M Q) (cadd M' Q')
  | 0, _, _, _, _, _, _, hy => RT.of_vacuous hy
  | k + 1, ν, Q, Q', eQ, hν, y, hy => by
      obtain ⟨tM, tM'⟩ := CEqual.typed X.levels eM formed
      obtain ⟨v, hv, e⟩ := hy
      refine RT.closed' e fun t ht => ?_
      rcases hv t ht with ⟨w, hw, et⟩ | ⟨w, hw, et⟩
      · -- zero: both sums reduce to the first summands
        refine RT.closed' et fun r hr => ?_
        obtain ⟨hz0, hrz⟩ := hw r hr
        obtain ⟨-, hQ0, hQ'0⟩ := RT.tm_zero_iff.1 (hν _ hz0)
        exact RT.expand X.levels formed (CRedTm.addZero X tM hQ0)
          (CRedTm.addZero X tM' (hQ'0.convType ⟨_, X.sort Tower.zero, .refl (X.lift cnum_typed)⟩))
          (hz r hrz)
      · -- successor: both sums reduce to successors of the sums at the predecessors
        refine RT.closed' et fun r hr => ?_
        obtain ⟨hs0, hr'⟩ := hw r hr
        obtain ⟨q, q', hT, hQs, hQ's, eq⟩ := RT.tm_succTag_iff.1 (hν _ hs0)
        obtain ⟨tq, tq'⟩ := CEqual.typed X.levels eq formed
        -- the predecessors, related as far as the predecessor observes
        have hpred : ∀ x, (Ideal.predI ν).Mem x →
            RT X.head Δ true x cnum q q' := by
          intro x hx
          obtain ⟨u, hu, ex⟩ := hx
          refine RT.closed' ex fun s hs => ?_
          obtain ⟨C, hC⟩ := hu s hs
          rcases RT.tm_argSucc_iff.1 (hν _ hC) with hvac | ⟨q₁, q₁', hsucc, -, hrel⟩
          · exact RT.of_vacuous (vacuous_arg hvac)
          obtain ⟨rfl, rfl⟩ := SuccRed.align ⟨hT, hQs, hQ's, eq⟩ hsucc
          exact hrel rfl
        have ih := add_claim formed eM hz k (Ideal.predI ν) q q' eq hpred
        -- the value of the step: a successor of the approximant at the predecessor
        have hr'' :
            (Ideal.succI (projT natI (natRecApprox z addRecStep k (Ideal.predI ν)))).Mem r := by
          have h := hr'
          change (Ideal.app (sucConst objectChurchReading numNames) _).Mem r at h
          rwa [app_sucConst objectChurchReading numNames objectChurchReading_num] at h
        have eSum : CEqual X.church Δ (cadd M q) (cadd M' q') cnum :=
          .appCong (A := cnum) (B := cnum)
            (.appCong (A := cnum) (B := .pi cnum cnum) (.refl (X.lift caddConst_typed)) eM) eq
        have red : SuccRed X.head Δ cnum (csuc (cadd M q)) (csuc (cadd M' q'))
            (cadd M q) (cadd M' q') :=
          ⟨CRedTy.refl ⟨_, X.sort Tower.zero, X.lift cnum_typed⟩,
            CRedTm.refl (X.csuc_typed (X.cadd_typed tM tq)),
            CRedTm.refl (X.csuc_typed (X.cadd_typed tM' tq')), eSum⟩
        have hsum : RT X.head Δ true r cnum (csuc (cadd M q)) (csuc (cadd M' q')) := by
          obtain ⟨u, hu, er⟩ := hr''
          refine RT.closed' er fun s hs => ?_
          rcases hu s hs with rfl | ⟨p, rfl, hp⟩
          · exact RT.tm_succTag_iff.2 ⟨_, _, red⟩
          · refine RT.tm_argSucc_iff.2 (.inr ⟨_, _, red, fun _ h => absurd h List.not_mem_nil,
              fun _ => ?_⟩)
            obtain ⟨u', hu', -, ep⟩ := Ideal.projT_eq_iSup.1 hp
            exact RT.closed' ep fun p' hp' => ih p' (hu' p' hp')
        exact RT.expand X.levels formed (CRedTm.addSuc X tM tq hQs)
          (CRedTm.addSuc X tM' tq' (hQ's.convType ⟨_, X.sort Tower.zero, .refl (X.lift cnum_typed)⟩))
          hsum

/-- **The sum of two variables of type `num` is adequate** (`add_claim`). -/
theorem adequate_addVars :
    Adequate X.reading X.head (.snoc (.snoc .nil cnum) cnum) (cadd (.var 1) (.var 0)) cnum := by
  intro ρ fits m Δ σ σ' formed hσ s hs _
  rw [cinterp_cadd X] at hs
  obtain ⟨v, hv, -, e⟩ := Ideal.projT_eq_iSup.1 hs
  refine RT.closed' e fun t ht => ?_
  obtain ⟨k, hk⟩ := (Ideal.mem_natRec (cont₂_constStep _)).1 (hv t ht)
  exact add_claim X formed (hσ.1.2 1) (SubstRel.numVar X (i := 1) rfl hσ) k _ (σ 0) (σ' 0)
    (hσ.1.2 0) (SubstRel.numVar X (i := 0) rfl hσ) t hk

/-- **Addition is adequate**, from its spine at two variables. -/
theorem constAdequateAt_add : ConstAdequateAt X.reading X.head addN :=
  ConstAdequateAt.of_spine (Θ := .snoc (.snoc .nil cnum) cnum) (T := cnum) X.levels
    X.soundnessFacts (X.sub.constantType (objectChurch_declared (c := addN) (T := addType)
      (by decide) rfl))
    (X.lift (cadd_typed (.var 1) (.var 0))) (adequate_addVars X)

end Addition

/-! ## Typings within allowed constants -/

section Within

variable {A : DeclName → Bool} {n : Nat} {Γ : CCtx Tower.Head n}

theorem cU0_typed_within : CTyped (objectChurch.restrict A) Γ cU0 cU1 :=
  .headType (.sort Tower.zero)

/-- A type of `U₀` is a type of `U₁`. -/
theorem craise_within {T : CTm Tower.Head n} (typed : CTyped (objectChurch.restrict A) Γ T cU0) :
    CTyped (objectChurch.restrict A) Γ T cU1 :=
  CDerivable.cumul typed (fun valuation => by simp [LevelExpr.eval, LevelTower.zero])

theorem cpiT_within {D : CTm Tower.Head n} {B : CTm Tower.Head (n + 1)} {l : LevelExpr Nat}
    (domain : CTyped (objectChurch.restrict A) Γ D (CU l))
    (codomain : CTyped (objectChurch.restrict A) (.snoc Γ D) B (CU l)) :
    CTyped (objectChurch.restrict A) Γ (.pi D B) (CU l) :=
  CDerivable.cumul (.piForm domain (.sort l) codomain (.sort l) (.sorts l l))
    (fun valuation => by simp [LevelExpr.eval])

theorem cidT_within {C a b : CTm Tower.Head n} {l : LevelExpr Nat}
    (carrier : CTyped (objectChurch.restrict A) Γ C (CU l))
    (left : CTyped (objectChurch.restrict A) Γ a C)
    (right : CTyped (objectChurch.restrict A) Γ b C) :
    CTyped (objectChurch.restrict A) Γ (.id C a b) (CU l) :=
  .idForm carrier (.sort l) left right

/-- An allowed declared constant at its annotated declared type. -/
theorem cconst_within {c : DeclName} (T : Tm Tower.Head 0) {l : LevelExpr Nat} (hA : A c = true)
    (declared : objectRules.constantType c = some T) (lf : lamFree T = true)
    (typed : CTyped (objectChurch.restrict A) .nil (liftTm T) (CU l)) :
    CTyped (objectChurch.restrict A) Γ (.const c) (liftTm T).liftClosed :=
  .const (by rw [ChurchRules.restrict_constantType hA]; exact objectChurch_declared declared lf)
    typed (.sort l)

theorem cnum_typed_within (hn : A numN = true) : CTyped (objectChurch.restrict A) Γ cnum cU0 :=
  cconst_within (c := numN) Package.U0 (l := .succ Tower.zero) hn (by decide) (by decide)
    cU0_typed_within

theorem czero_typed_within (h0 : A zeroN = true) (hn : A numN = true) :
    CTyped (objectChurch.restrict A) Γ czero cnum :=
  cconst_within (c := zeroN) Package.numT (l := Tower.zero) h0 (by decide) (by decide)
    (cnum_typed_within hn)

theorem csuc_typed_within (hs : A sucN = true) (hn : A numN = true) {a : CTm Tower.Head n}
    (ta : CTyped (objectChurch.restrict A) Γ a cnum) :
    CTyped (objectChurch.restrict A) Γ (csuc a) cnum :=
  .appElim (B := cnum) (cconst_within (c := sucN) (.pi Package.numT Package.numT)
    (l := Tower.zero) hs (by decide) (by decide)
    (cpiT_within (cnum_typed_within hn) (cnum_typed_within hn))) ta

theorem cadd_typed_within (ha : A addN = true) (hn : A numN = true) {a b : CTm Tower.Head n}
    (ta : CTyped (objectChurch.restrict A) Γ a cnum)
    (tb : CTyped (objectChurch.restrict A) Γ b cnum) :
    CTyped (objectChurch.restrict A) Γ (cadd a b) cnum :=
  .appElim (B := cnum) (.appElim (B := .pi cnum cnum) (cconst_within (c := addN) addType
    (l := Tower.zero) ha (by decide) (by decide) (cpiT_within (cnum_typed_within hn)
      (cpiT_within (cnum_typed_within hn) (cnum_typed_within hn)))) ta) tb

theorem ceqAt_typed_within (he : A eqAtName = true) (hn : A numN = true) {a : CTm Tower.Head n}
    (ta : CTyped (objectChurch.restrict A) Γ a cnum) :
    CTyped (objectChurch.restrict A) Γ (ceqAt a) cU0 :=
  .appElim (B := cU0) (cconst_within Package.eqAtType (l := .succ Tower.zero) he (by decide)
    (by decide) (cpiT_within (craise_within (cnum_typed_within hn)) cU0_typed_within)) ta

/-- The annotated type of the identity eliminator, formed with no constant. -/
theorem cjType_formed_within :
    CTyped (objectChurch.restrict A) .nil (liftTm Package.jType) cU1 := by
  show CTyped (objectChurch.restrict A) .nil
    (.pi cU0 (.pi (.var 0)
      (.pi (.pi (.var 1) (.pi (.id (.var 2) (.var 1) (.var 0)) cU0))
        (.pi (.app (.app (.var 0) (.var 1)) (.refl (.var 1)))
          (.pi (.var 3) (.pi (.id (.var 4) (.var 3) (.var 0))
            (.app (.app (.var 3) (.var 1)) (.var 0)))))))) cU1
  let Γ₁ : CCtx Tower.Head 1 := .snoc .nil cU0
  let Γ₂ : CCtx Tower.Head 2 := .snoc Γ₁ (.var 0)
  have tMotiveInner : CTyped (objectChurch.restrict A) (.snoc Γ₂ (.var 1))
      (.pi (.id (.var 2) (.var 1) (.var 0)) cU0) cU1 :=
    cpiT_within (craise_within (cidT_within (.var 2) (.var 1) (.var 0))) cU0_typed_within
  have tMotive : CTyped (objectChurch.restrict A) Γ₂
      (.pi (.var 1) (.pi (.id (.var 2) (.var 1) (.var 0)) cU0)) cU1 :=
    cpiT_within (craise_within (.var 1)) tMotiveInner
  let Γ₃ : CCtx Tower.Head 3 := .snoc Γ₂ (.pi (.var 1) (.pi (.id (.var 2) (.var 1) (.var 0)) cU0))
  have tMx := CDerivable.appElim (P := objectChurch.restrict A) (Γ := Γ₃) (.var 0) (.var 1)
  have tRefl : CTyped (objectChurch.restrict A) Γ₃ (.refl (.var 1))
      (.id (.var 2) (.var 1) (.var 1)) :=
    .reflIntro (.var 1)
  have tCase : CTyped (objectChurch.restrict A) Γ₃ (.app (.app (.var 0) (.var 1)) (.refl (.var 1)))
      cU0 :=
    .appElim (B := cU0) tMx tRefl
  let Γ₄ : CCtx Tower.Head 4 := .snoc Γ₃ (.app (.app (.var 0) (.var 1)) (.refl (.var 1)))
  let Γ₅ : CCtx Tower.Head 5 := .snoc Γ₄ (.var 3)
  let Γ₆ : CCtx Tower.Head 6 := .snoc Γ₅ (.id (.var 4) (.var 3) (.var 0))
  have tPy := CDerivable.appElim (P := objectChurch.restrict A) (Γ := Γ₆) (.var 3) (.var 1)
  have tResult : CTyped (objectChurch.restrict A) Γ₆ (.app (.app (.var 3) (.var 1)) (.var 0)) cU0 :=
    .appElim (B := cU0) tPy (.var 0)
  have tPath : CTyped (objectChurch.restrict A) Γ₅
      (.pi (.id (.var 4) (.var 3) (.var 0)) (.app (.app (.var 3) (.var 1)) (.var 0))) cU1 :=
    cpiT_within (craise_within (cidT_within (.var 4) (.var 3) (.var 0))) (craise_within tResult)
  exact cpiT_within cU0_typed_within (cpiT_within (craise_within (.var 0)) (cpiT_within tMotive
    (cpiT_within (craise_within tCase) (cpiT_within (craise_within (.var 3)) tPath))))

theorem cj_typed_within (hj : A jName = true) :
    CTyped (objectChurch.restrict A) Γ (.const jName) (liftTm Package.jType).liftClosed :=
  cconst_within Package.jType hj (by decide) (by decide) cjType_formed_within

/-- Two β-steps of an annotated family of types. -/
theorem cbetaTwo_within {A' : CTm Tower.Head n} {B : CTm Tower.Head (n + 1)}
    {M : CTm Tower.Head (n + 2)} {a b : CTm Tower.Head n} {l : LevelExpr Nat}
    (formed : CTyped (objectChurch.restrict A) Γ (.pi A' (.pi B cU0)) (CU l))
    (formed₂ : CTyped (objectChurch.restrict A) (.snoc Γ A') (.pi B cU0) (CU l))
    (formedB : CTyped (objectChurch.restrict A) (.snoc Γ A') B (CU l))
    (body : CTyped (objectChurch.restrict A) (.snoc (.snoc Γ A') B) M cU0)
    (ta : CTyped (objectChurch.restrict A) Γ a A')
    (tb : CTyped (objectChurch.restrict A) Γ b (CTm.inst0 a B)) :
    CEqual (objectChurch.restrict A) Γ (.app (.app (.lam A' (.lam B M)) a) b)
      (CTm.inst0 b (M.subst (CTm.liftSub (CTm.subst0 a)))) cU0 := by
  have lamM : CTyped (objectChurch.restrict A) (.snoc Γ A') (.lam B M) (.pi B cU0) :=
    .lamIntro formedB (.sort l) formed₂ (.sort l) body
  have e₁ := CDerivable.betaPi formed (.sort l) lamM ta
  have e₂ : CEqual (objectChurch.restrict A) Γ (.app (.app (.lam A' (.lam B M)) a) b)
      (.app (CTm.inst0 a (.lam B M)) b) (CTm.inst0 b cU0) :=
    CDerivable.appCong (A := CTm.inst0 a B) (B := cU0) e₁ (.refl tb)
  have formedInst : CTyped (objectChurch.restrict A) Γ (.pi (CTm.inst0 a B) cU0) (CU l) :=
    CTyped.instantiate formed₂ ta
  have bodyInst : CTyped (objectChurch.restrict A) (.snoc Γ (CTm.inst0 a B))
      (M.subst (CTm.liftSub (CTm.subst0 a))) cU0 :=
    CTyped.substitute body (CSubstMor.lift (CSubstMor.single ta) B)
  have e₃ := CDerivable.betaPi formedInst (.sort l) bodyInst tb
  exact .trans e₂ e₃

end Within

/-! ## Stage 1: `eqAt` -/

section EqAt

/-- The constants of the right side of `eqAt`: `num`, `zero`, `suc` and `add`. -/
abbrev eqAtAllowed : DeclName → Bool := allowedIn [numN, zeroN, sucN, addN]

/-- The constants of the stage of `eqAt` are adequate. -/
theorem eqAtAllowed_adequate :
    ∀ {c : DeclName}, eqAtAllowed c = true → ConstAdequateAt X.reading X.head c :=
  consts_allowedIn fun c hc => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact constAdequateAt_num X
    · exact constAdequateAt_zero X
    · exact constAdequateAt_suc X
    · exact constAdequateAt_add X

/-- **The right side of `eqAt` is typed within its constants**:
`n : num ⊢ Id num (add zero n) n : U₀`. -/
theorem ceqAtRhs_typed_within :
    CTyped (objectChurch.restrict eqAtAllowed) (.snoc .nil cnum)
      (.id cnum (cadd czero (.var 0)) (.var 0)) cU0 :=
  cidT_within (cnum_typed_within rfl)
    (cadd_typed_within rfl rfl (czero_typed_within rfl rfl) (.var 0)) (.var 0)

/-- `eqAt` is declared at `num → U₀`. -/
theorem eqAt_declared :
    objectChurch.constantType eqAtName = some (pisCtx (.snoc .nil cnum) cU0) :=
  objectChurch_declared (T := Package.eqAtType) (by decide) (by decide)

/-- `eqAt` denotes the abstraction of its right side, projected onto its declared type. -/
theorem objectChurchReading_eqAt :
    objectChurchReading.const eqAtName =
      defConst objectChurchReading (.snoc .nil cnum) cU0
        (.id cnum (cadd czero (.var 0)) (.var 0)) := by
  have h := objectChurchReading_def (f := eqAtName) (tag := .eqAt) (by decide)
    (Θ := eqAtTele) (rhs := eqAtRhs) (T := cU0) (by decide) rfl
  have e : defRhs eqAtName eqAtTele eqAtRhs = (.id cnum (cadd czero (.var 0)) (.var 0) :
      CTm Tower.Head 1) := by
    decide
  rw [h, e]
  rfl

/-- `eqAt` is read in every extension as in the object package. -/
theorem ObjectExtension.reading_eqAt :
    X.reading.const eqAtName =
      defConst X.reading (.snoc .nil cnum) cU0 (.id cnum (cadd czero (.var 0)) (.var 0)) := by
  rw [X.reading_const (by decide), objectChurchReading_eqAt,
    X.defConst_eq _ _ _ (by decide) (by decide)]

/-- **The applications of `eqAt` reduce to its right side**, by its root step, at `U₀`. -/
theorem eqAt_teleReduces {K : RigidTypes X.church} (H : HeadReduction X.church K)
    {m : Nat} {Δ : CCtx Tower.Head m} :
    TeleReduces H Δ (CCtx.toTele (.snoc .nil cnum)) cU0 (.id cnum (cadd czero (.var 0)) (.var 0))
      (.const eqAtName) fun i => .var (Fin.elim0 i) := by
  intro N tN
  exact ⟨.single (H.root (X.within.step (ceqAt_step N))),
    .rootAdmitted (X.within.step (ceqAt_step N)) (ceqAt_admits tN X.within)
      (.appElim (B := cU0) (X.lift (ceqAtConst_typed)) tN)
      (X.cidT (X.lift cnum_typed) (X.cadd_typed (X.lift czero_typed) tN) tN)⟩

/-- **`eqAt` is adequate**: its right side's typing within `num`, `zero`, `suc` and `add` is
valid by the fundamental lemma. -/
theorem constAdequateAt_eqAt : ConstAdequateAt X.reading X.head eqAtName :=
  ConstAdequateAt.ofDefinition X.levels X.soundnessFacts (X.sub.constantType eqAt_declared)
    X.reading_eqAt
    (X.valid_within (eqAtAllowed_adequate X) ceqAtRhs_typed_within
      (.snoc .nil ⟨_, X.sort _, X.lift cnum_typed⟩)).1
    fun _ => eqAt_teleReduces X X.head

end EqAt

/-! ## The identity eliminator -/

section Eliminator

/-- The eliminator's spine at the variables of its telescope, at the motive's value at the
endpoint and the path. -/
theorem cjVars_typed :
    CTyped objectChurch cJTypeTele
      (CTm.appSpine (.const jName) [.var 5, .var 4, .var 3, .var 2, .var 1, .var 0])
      (.app (.app (.var 3) (.var 1)) (.var 0)) :=
  CDerivable.appElim cjSpine_typed (.var 0)

/-- The hypotheses of the eliminator's case at the variables of its telescope: each
variable is typed and adequate at its type. -/
theorem jCase_vars :
    JCase X X.head cJTypeTele (.var 5) (.var 4) (.var 3) (.var 2) (.var 1) (.var 0) :=
  ⟨.var 5, .var 4, .var 3, .var 2, .var 1, .var 0, (CStatement.Valid.var 3).1,
    (CStatement.Valid.var 2).1, (CStatement.Valid.var 0).1, (CStatement.Valid.var 5).1⟩

/-- **The identity eliminator is adequate**: its spine at the variables of its telescope is
adequate by the eliminator's case of the fundamental lemma (`Adequate.objectJ`), its path
congruence that of the extension's reduction (`ObjectExtension.head_jPath`). -/
theorem constAdequateAt_j : ConstAdequateAt X.reading X.head jName :=
  ConstAdequateAt.of_spine (Θ := cJTypeTele) (T := .app (.app (.var 3) (.var 1)) (.var 0))
    X.levels X.soundnessFacts
    (X.sub.constantType (objectChurch_declared (c := jName) (T := Package.jType) (by decide) rfl))
    (X.lift cjVars_typed) (Adequate.objectJ X.levels (fun s => X.head_jPath s) (jCase_vars X))

end Eliminator

/-! ## Stage 2: the successor move -/

section SucMove

/-- The constants of the right side of `sucMove`: `num`, `zero`, `suc`, `add`, `J` and
`eqAt`. -/
abbrev sucMoveAllowed : DeclName → Bool := allowedIn [numN, zeroN, sucN, addN, jName, eqAtName]

/-- The constants of the stage of `sucMove` are adequate. -/
theorem sucMoveAllowed_adequate :
    ∀ {c : DeclName}, sucMoveAllowed c = true → ConstAdequateAt X.reading X.head c :=
  consts_allowedIn fun c hc => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    · exact constAdequateAt_num X
    · exact constAdequateAt_zero X
    · exact constAdequateAt_suc X
    · exact constAdequateAt_add X
    · exact constAdequateAt_j X
    · exact constAdequateAt_eqAt X

/-- **The right side of `sucMove` is typed within its constants**, at its codomain
`eqAt (suc n)`: the typing of its template, whose conversions are β, the equation of `eqAt`
and the successor equation of addition. -/
theorem csucMoveRhs_typed_within :
    CTyped (objectChurch.restrict sucMoveAllowed) cEqAtTele cSucMoveRhs cSucMoveCod := by
  show CTyped (objectChurch.restrict sucMoveAllowed) cEqAtTele
    (.app (.app (.app (.app (.app (.app (.const jName) cnum) (cadd czero (.var 1))) cSucMotive)
      (.refl (csuc (cadd czero (.var 1))))) (.var 1)) (.var 0))
    (ceqAt (csuc (.var 1)))
  have tnum : ∀ {n : Nat} {Γ : CCtx Tower.Head n},
      CTyped (objectChurch.restrict sucMoveAllowed) Γ cnum cU0 := cnum_typed_within rfl
  have tzero : ∀ {n : Nat} {Γ : CCtx Tower.Head n},
      CTyped (objectChurch.restrict sucMoveAllowed) Γ czero cnum := czero_typed_within rfl rfl
  have point : CTyped (objectChurch.restrict sucMoveAllowed) cEqAtTele (cadd czero (.var 1)) cnum :=
    cadd_typed_within rfl rfl tzero (.var 1)
  -- the motive, typed at the eliminator's motive type
  have formedB : CTyped (objectChurch.restrict sucMoveAllowed) (.snoc cEqAtTele cnum)
      (.id cnum (cadd czero (.var 2)) (.var 0)) cU0 :=
    cidT_within tnum (cadd_typed_within rfl rfl tzero (.var 2)) (.var 0)
  have formed₂ : CTyped (objectChurch.restrict sucMoveAllowed) (.snoc cEqAtTele cnum)
      (.pi (.id cnum (cadd czero (.var 2)) (.var 0)) cU0) cU1 :=
    cpiT_within (craise_within formedB) cU0_typed_within
  have formed : CTyped (objectChurch.restrict sucMoveAllowed) cEqAtTele
      (.pi cnum (.pi (.id cnum (cadd czero (.var 2)) (.var 0)) cU0)) cU1 :=
    cpiT_within (craise_within tnum) formed₂
  have bodyM : CTyped (objectChurch.restrict sucMoveAllowed)
      (.snoc (.snoc cEqAtTele cnum) (.id cnum (cadd czero (.var 2)) (.var 0)))
      (.id cnum (csuc (cadd czero (.var 3))) (csuc (.var 1))) cU0 :=
    cidT_within tnum (csuc_typed_within rfl rfl (cadd_typed_within rfl rfl tzero (.var 3)))
      (csuc_typed_within rfl rfl (.var 1))
  have motiveTyped : CTyped (objectChurch.restrict sucMoveAllowed) cEqAtTele cSucMotive
      (.pi cnum (.pi (.id cnum (cadd czero (.var 2)) (.var 0)) cU0)) :=
    .lamIntro tnum (.sort _) formed (.sort _) (.lamIntro formedB (.sort _) formed₂ (.sort _) bodyM)
  -- the reflexivity case, retyped by β
  have reflCase : CTyped (objectChurch.restrict sucMoveAllowed) cEqAtTele
      (.refl (csuc (cadd czero (.var 1))))
      (.app (.app cSucMotive (cadd czero (.var 1))) (.refl (cadd czero (.var 1)))) :=
    .conv (.reflIntro (csuc_typed_within rfl rfl point))
      (.symm (cbetaTwo_within formed formed₂ (craise_within formedB) bodyM point
        (.reflIntro point)))
      (.sort Tower.zero)
  -- the evidence, retyped by the equation of `eqAt`
  have eAt : CEqual (objectChurch.restrict sucMoveAllowed) cEqAtTele (ceqAt (.var 1))
      (.id cnum (cadd czero (.var 1)) (.var 1)) cU0 :=
    .rootAdmitted (ceqAt_step _) (ceqAt_admits (.var 1)) (ceqAt_typed_within rfl rfl (.var 1))
      (cidT_within tnum point (.var 1))
  have path : CTyped (objectChurch.restrict sucMoveAllowed) cEqAtTele (.var 0)
      (.id cnum (cadd czero (.var 1)) (.var 1)) :=
    .conv (.var 0) eAt (.sort Tower.zero)
  -- the eliminator
  have j0 : CTyped (objectChurch.restrict sucMoveAllowed) cEqAtTele (.const jName) cJType :=
    cj_typed_within rfl
  have j1 := CDerivable.appElim j0 tnum
  have j2 := CDerivable.appElim j1 point
  have j3 := CDerivable.appElim j2 motiveTyped
  have j4 := CDerivable.appElim j3 reflCase
  have j5 := CDerivable.appElim j4 (CDerivable.var 1)
  have j6 := CDerivable.appElim j5 path
  -- the motive at the endpoint is `eqAt (suc n)`: β, `eqAt`, `add`
  have βend := cbetaTwo_within formed formed₂ (craise_within formedB) bodyM (CDerivable.var 1) path
  have eqAtSuc : CEqual (objectChurch.restrict sucMoveAllowed) cEqAtTele (ceqAt (csuc (.var 1)))
      (.id cnum (cadd czero (csuc (.var 1))) (csuc (.var 1))) cU0 :=
    .rootAdmitted (ceqAt_step _) (ceqAt_admits (csuc_typed_within rfl rfl (.var 1)))
      (ceqAt_typed_within rfl rfl (csuc_typed_within rfl rfl (.var 1)))
      (cidT_within tnum (cadd_typed_within rfl rfl tzero (csuc_typed_within rfl rfl (.var 1)))
        (csuc_typed_within rfl rfl (.var 1)))
  have addSuc : CEqual (objectChurch.restrict sucMoveAllowed) cEqAtTele
      (cadd czero (csuc (.var 1))) (csuc (cadd czero (.var 1))) cnum :=
    .rootAdmitted (caddSuc_step _ _) (caddSuc_admits tzero (.var 1))
      (cadd_typed_within rfl rfl tzero (csuc_typed_within rfl rfl (.var 1)))
      (csuc_typed_within rfl rfl point)
  have idEq : CEqual (objectChurch.restrict sucMoveAllowed) cEqAtTele
      (.id cnum (cadd czero (csuc (.var 1))) (csuc (.var 1)))
      (.id cnum (csuc (cadd czero (.var 1))) (csuc (.var 1))) cU0 :=
    .idCong (.refl tnum) (.sort _) addSuc (.refl (csuc_typed_within rfl rfl (.var 1)))
  exact .conv j6 (.trans βend (.symm (.trans eqAtSuc idEq))) (.sort Tower.zero)

/-- The telescope `n : num, e : eqAt n` is formed. -/
theorem cEqAtTele_formed : CCtxFormed objectChurch cEqAtTele :=
  .snoc (.snoc .nil ⟨_, .sort _, cnum_typed⟩) ⟨_, .sort _, ceqAt_typed (.var 0)⟩

/-- **The typing of the right side of `sucMove` at its codomain is valid**, by the fundamental
lemma within `num`, `zero`, `suc`, `add`, `J` and `eqAt`. -/
theorem csucMoveRhs_valid :
    (CStatement.typing cEqAtTele cSucMoveRhs cSucMoveCod).Valid X.reading X.head :=
  X.valid_within (sucMoveAllowed_adequate X) csucMoveRhs_typed_within (X.liftFormed cEqAtTele_formed)

/-- **The successor move is adequate**, with no hypothesis: the one hypothesis of
`constAdequateAt_sucMove` is `csucMoveRhs_valid`. -/
theorem constAdequateAt_sucMove' : ConstAdequateAt X.reading X.head sucMoveName :=
  constAdequateAt_sucMove X (csucMoveRhs_valid X)

end SucMove

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
