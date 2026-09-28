import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.AlgorithmSoundness
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.WrittenDomains

/-!
# Written domains under computation

Every step on terms with written domains preserves annotated typing and is a
typed equality between the erasures, so a written domain never changes what a
term computes to. The contractions invert an annotated λ at a dependent
function type, which needs injectivity of dependent function types from the
facts about weak-head forms of types: a written domain is equal to the domain
of every dependent function type its λ is typed at, and two λs typed at one
type have equal written domains.

Equality of written terms is equality of their erasures, between terms typed
at a common type.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L]

/-! ## Conversion of types and of the last context entry -/

section Conversion

variable {R : Rules Head}

theorem ATyped.convTypeEq {n : Nat} {Γ : Ctx Head n} {t : ATm Head n} {A B : Tm Head n}
    (typing : ATyped R Γ t A) (equal : TypeEq R Γ A B) : ATyped R Γ t B := by
  obtain ⟨u, hu, e⟩ := equal
  exact .conv typing e hu

theorem ASubstMor.ctxConv {n : Nat} {Γ : Ctx Head n} {A A' : Tm Head n}
    (equal : TypeEq R Γ A' A) : ASubstMor R (.snoc Γ A) (.snoc Γ A') ATm.ids := by
  intro i
  rw [ATm.eraseSub_ids]
  refine Fin.cases ?_ (fun j => ?_) i
  · show ATyped R (.snoc Γ A') (.var 0) (Presentation.subst ids (Presentation.rename wk A))
    rw [subst_ids]
    exact ATyped.convTypeEq (.var 0) (equal.rename (CtxRen.wk Γ A'))
  · show ATyped R (.snoc Γ A') (.var j.succ)
      (Presentation.subst ids (Presentation.rename wk (Ctx.lookup Γ j)))
    rw [subst_ids]
    exact .var j.succ

/-- Changing the last context entry to an equal type. -/
theorem ATyped.ctxConv {n : Nat} {Γ : Ctx Head n} {A A' : Tm Head n} {t : ATm Head (n + 1)}
    {T : Tm Head (n + 1)} (typing : ATyped R (.snoc Γ A) t T) (equal : TypeEq R Γ A A') :
    ATyped R (.snoc Γ A') t T := by
  simpa using typing.substitute (ASubstMor.ctxConv equal.symm)

end Conversion

variable {S : Setting Head L}

/-! ## Inversion, from the facts about weak-head forms -/

section Inversion

variable (facts : FormFacts S.R S.roles)
include facts

/-- A λ with no written domain, typed at a dependent function type, has its
body typed at the codomain over the domain. -/
theorem ATyped.lamBare_inv {n : Nat} {Γ : Ctx Head n} {A : Tm Head n}
    {body : ATm Head (n + 1)} {B : Tm Head (n + 1)}
    (typing : ATyped S.R Γ (.lamBare body) (.pi A B)) (formed : CtxFormed S.R Γ) :
    ATyped S.R (.snoc Γ A) body B := by
  obtain ⟨A', B', u, tPi, hu, tb, le⟩ := typing.generation
  obtain ⟨eA, leB⟩ := TypeLe.pi_parts facts le
    (Typed.isType typing.erase formed) formed
  exact ATyped.ctxConv (.sub tb leB) eA

/-- A λ with a written domain, typed at a dependent function type: the written
domain is a type equal to the domain, and the body is typed at the codomain
over the domain. -/
theorem ATyped.lamTyped_inv {n : Nat} {Γ : Ctx Head n} {W : ATm Head n} {A : Tm Head n}
    {body : ATm Head (n + 1)} {B : Tm Head (n + 1)}
    (typing : ATyped S.R Γ (.lamTyped W body) (.pi A B)) (formed : CtxFormed S.R Γ) :
    (∃ v, S.R.isUniverse v ∧ ATyped S.R Γ W (.head v)) ∧ TypeEq S.R Γ W.erase A ∧
      ATyped S.R (.snoc Γ A) body B := by
  obtain ⟨A', B', u, v, tW, hv, agree, tPi, hu, tb, le⟩ := typing.generation
  obtain ⟨eA, leB⟩ := TypeLe.pi_parts facts le
    (Typed.isType typing.erase formed) formed
  exact ⟨⟨v, hv, tW⟩, TypeEq.trans S.levels ⟨v, hv, agree⟩ eA, ATyped.ctxConv (.sub tb leB) eA⟩

/-- Two λs with written domains typed at one type have equal written
domains. -/
theorem ATyped.writtenDomains_agree {n : Nat} {Γ : Ctx Head n} {W W' : ATm Head n}
    {body body' : ATm Head (n + 1)} {T : Tm Head n} (formed : CtxFormed S.R Γ)
    (first : ATyped S.R Γ (.lamTyped W body) T) (second : ATyped S.R Γ (.lamTyped W' body') T) :
    TypeEq S.R Γ W.erase W'.erase := by
  obtain ⟨A, B, u, v, _, hv, agree, tPi, hu, _, le⟩ := first.generation
  obtain ⟨A', B', u', v', _, hv', agree', tPi', hu', _, le'⟩ := second.generation
  have typeT := Typed.isType first.erase formed
  obtain ⟨A₁, B₁, eT, eA₁, _⟩ := Below.pi_source facts (TypeLe.toBelow le typeT) formed
    (IsType.refl ⟨u, hu, tPi⟩)
  obtain ⟨A₂, B₂, eT', eA₂, _⟩ := Below.pi_source facts (TypeLe.toBelow le' typeT) formed
    (IsType.refl ⟨u', hu', tPi'⟩)
  obtain ⟨e₁₂, _⟩ := TypeEq.pi_injective facts (TypeEq.trans S.levels eT.symm eT') formed
  have eA : TypeEq S.R Γ A A' :=
    TypeEq.trans S.levels (TypeEq.trans S.levels eA₁ e₁₂) eA₂.symm
  exact TypeEq.trans S.levels (TypeEq.trans S.levels ⟨v, hv, agree⟩ eA) (TypeEq.symm ⟨v', hv', agree'⟩)

/-- The outer shape a former fixes: a type in weak-head normal form equal to a
type with that former has the same outer constructor. -/
def Former.sameShape {n : Nat} {A : Tm Head n} : Former S A → Tm Head n → Prop
  | .head _, B => ∃ h, B = .head h
  | .pi _ _, B => ∃ d c, B = .pi d c
  | .sigma _ _, B => ∃ d c, B = .sigma d c
  | .id _ _ _, B => ∃ T l r, B = .id T l r
  | .inductiveType T _ _, B => B = .const T

/-- A type in weak-head normal form equal to a type with a former has the
outer shape of that former. Only one of the two types needs a former. -/
theorem TypeEq.shape_of_whnf {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n} (fA : Former S A)
    (normalB : Whnf S.R S.roles B) (equal : TypeEq S.R Γ A B) (formed : CtxFormed S.R Γ) :
    fA.sameShape B := by
  obtain ⟨B', red, formB⟩ := facts.typeForm (TypeEq.isType equal formed).2 formed
  obtain rfl := WhRed.eq_of_whnf normalB red.red
  cases fA with
  | head h =>
      obtain ⟨h', e, _⟩ := (facts.forms equal formed (.inl ⟨_, rfl⟩) formB).head_left
      exact ⟨h', e⟩
  | pi A₁ B₁ =>
      obtain ⟨d, c, e, _⟩ := (facts.forms equal formed (.inr (.inl ⟨_, _, rfl⟩)) formB).pi_left
      exact ⟨d, c, e⟩
  | sigma A₁ B₁ =>
      obtain ⟨d, c, e, _⟩ :=
        (facts.forms equal formed (.inr (.inr (.inl ⟨_, _, rfl⟩))) formB).sigma_left
      exact ⟨d, c, e⟩
  | id A₁ a₁ b₁ =>
      obtain ⟨T, l, rr, e, _⟩ :=
        (facts.forms equal formed (.inr (.inr (.inr (.inl ⟨_, _, _, rfl⟩)))) formB).id_left
      exact ⟨T, l, rr, e⟩
  | inductiveType T ctors role =>
      exact (facts.forms equal formed (.inr (.inr (.inr (.inr (.inr ⟨T, ctors, role, rfl⟩)))))
        formB).inductive_left role

/-- A pair typed at a dependent pair type has its components typed. -/
theorem ATyped.pair_inv {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {a b : ATm Head n}
    {B : Tm Head (n + 1)} (typing : ATyped S.R Γ (.pair a b) (.sigma A B))
    (formed : CtxFormed S.R Γ) :
    ATyped S.R Γ a A ∧ ATyped S.R Γ b (inst0 a.erase B) := by
  obtain ⟨A', B', u, tSigma, hu, ta, tb, le⟩ := typing.generation
  obtain ⟨leA, leB⟩ := TypeLe.sigma_parts facts le
    (Typed.isType typing.erase formed) formed
  exact ⟨.sub ta leA, .sub tb (Derivable.substitutes leB (SubstMor.single ta.erase))⟩

/-- A λ whose written domain computes to a type former that the domain it is
checked at, in weak-head normal form, does not have, is not typed there: the
written domain would have to equal that domain. -/
theorem ATyped.lamTyped_domain_mismatch (roots : RootPreserving S.R) {n : Nat}
    {Γ : Ctx Head n} {W : ATm Head n} {W' A : Tm Head n} {body : ATm Head (n + 1)}
    {B : Tm Head (n + 1)} (formed : CtxFormed S.R Γ) (red : WhRed S.R S.roles W.erase W')
    (fW : Former S W') (normalA : Whnf S.R S.roles A) (differ : ¬ fW.sameShape A) :
    ¬ ATyped S.R Γ (.lamTyped W body) (.pi A B) := by
  intro typing
  obtain ⟨⟨v, hv, tW⟩, agree, _⟩ := ATyped.lamTyped_inv facts typing formed
  have toWhnf := (WhRed.preserve facts roots formed red tW.erase).2
  have equal : TypeEq S.R Γ W' A :=
    TypeEq.trans S.levels (TypeEq.symm ⟨v, hv, toWhnf⟩) agree
  exact differ (TypeEq.shape_of_whnf facts fW normalA equal formed)

/-- The same when the domain checked at has the former and the written domain,
computed to weak-head normal form, does not have its shape. -/
theorem ATyped.lamTyped_domain_mismatch' (roots : RootPreserving S.R) {n : Nat}
    {Γ : Ctx Head n} {W : ATm Head n} {W' A : Tm Head n} {body : ATm Head (n + 1)}
    {B : Tm Head (n + 1)} (formed : CtxFormed S.R Γ) (red : WhRed S.R S.roles W.erase W')
    (normalW : Whnf S.R S.roles W') (fA : Former S A) (differ : ¬ fA.sameShape W') :
    ¬ ATyped S.R Γ (.lamTyped W body) (.pi A B) := by
  intro typing
  obtain ⟨⟨v, hv, tW⟩, agree, _⟩ := ATyped.lamTyped_inv facts typing formed
  have toWhnf := (WhRed.preserve facts roots formed red tW.erase).2
  have equal : TypeEq S.R Γ A W' :=
    TypeEq.symm (TypeEq.trans S.levels (TypeEq.symm ⟨v, hv, toWhnf⟩) agree)
  exact differ (TypeEq.shape_of_whnf facts fA normalW equal formed)

/-- A λ is not typed at a dependent function type when its written domain and
the domain checked at compute to heads that are not the same head. -/
theorem ATyped.lamTyped_head_mismatch (roots : RootPreserving S.R) {n : Nat}
    {Γ : Ctx Head n} {W : ATm Head n} {A : Tm Head n} {body : ATm Head (n + 1)}
    {B : Tm Head (n + 1)} {h h' : Head} (formed : CtxFormed S.R Γ)
    (redW : WhRed S.R S.roles W.erase (.head h)) (redA : WhRed S.R S.roles A (.head h'))
    (differ : ¬ HeadSame S.R h h') :
    ¬ ATyped S.R Γ (.lamTyped W body) (.pi A B) := by
  intro typing
  obtain ⟨⟨v, hv, tW⟩, ⟨w, hw, agree⟩, _⟩ := ATyped.lamTyped_inv facts typing formed
  have tA := (Equal.typed agree formed).2
  have toW := (WhRed.preserve facts roots formed redW tW.erase).2
  have toA := (WhRed.preserve facts roots formed redA tA).2
  have equal : TypeEq S.R Γ (.head h) (.head h') :=
    TypeEq.trans S.levels
      (TypeEq.trans S.levels (TypeEq.symm ⟨v, hv, toW⟩) ⟨w, hw, agree⟩) ⟨w, hw, toA⟩
  exact differ (TypeEq.head_injective facts equal formed)

end Inversion

/-! ## The contractions -/

section Contractions

variable (facts : FormFacts S.R S.roles)
include facts

theorem ATyped.betaBare_preserve {n : Nat} {Γ : Ctx Head n} {a : ATm Head n}
    {body : ATm Head (n + 1)} {T : Tm Head n} (formed : CtxFormed S.R Γ)
    (typing : ATyped S.R Γ (.app (.lamBare body) a) T) :
    ATyped S.R Γ (ATm.inst0 a body) T := by
  obtain ⟨A, B, tf, ta, le⟩ := typing.generation
  exact (ATyped.instantiate (ATyped.lamBare_inv facts tf formed) ta).subsume le

theorem ATyped.betaTyped_preserve {n : Nat} {Γ : Ctx Head n} {W a : ATm Head n}
    {body : ATm Head (n + 1)} {T : Tm Head n} (formed : CtxFormed S.R Γ)
    (typing : ATyped S.R Γ (.app (.lamTyped W body) a) T) :
    ATyped S.R Γ (ATm.inst0 a body) T := by
  obtain ⟨A, B, tf, ta, le⟩ := typing.generation
  exact (ATyped.instantiate (ATyped.lamTyped_inv facts tf formed).2.2 ta).subsume le

theorem ATyped.fstPair_preserve {n : Nat} {Γ : Ctx Head n} {a b : ATm Head n}
    {T : Tm Head n} (formed : CtxFormed S.R Γ) (typing : ATyped S.R Γ (.fst (.pair a b)) T) :
    ATyped S.R Γ a T := by
  obtain ⟨A, B, tp, le⟩ := typing.generation
  exact (ATyped.pair_inv facts tp formed).1.subsume le

theorem ATyped.sndPair_preserve {n : Nat} {Γ : Ctx Head n} {a b : ATm Head n}
    {T : Tm Head n} (formed : CtxFormed S.R Γ) (typing : ATyped S.R Γ (.snd (.pair a b)) T) :
    ATyped S.R Γ b T := by
  obtain ⟨A, B, tp, le⟩ := typing.generation
  obtain ⟨ta, tb⟩ := ATyped.pair_inv facts tp formed
  obtain ⟨w, hw, tSigma⟩ := Typed.isType tp.erase formed
  obtain ⟨_, v, hv, family⟩ := IsType.sigma_parts ⟨w, hw, tSigma⟩
  have change : TypeEq S.R Γ (inst0 a.erase B) (inst0 (.fst (.pair a.erase b.erase)) B) :=
    TypeEq.of_instantiateEq family hv ta.erase (.symm (.betaFst tSigma hw ta.erase tb.erase))
  exact (ATyped.convTypeEq tb change).subsume le

end Contractions

/-! ## Steps -/

section Steps

variable (facts : FormFacts S.R S.roles)
include facts

/-- Steps on written terms preserve annotated typing, and each is a typed
equality between the erasures. -/
theorem ATm.Step.preserve (roots : RootPreserving S.R) (heads : HeadPreserving S.R) {n : Nat}
    {t t' : ATm Head n} (step : ATm.Step S.R.computation S.R.headEq t t') :
    ∀ {Γ : Ctx Head n}, CtxFormed S.R Γ → ∀ {T : Tm Head n}, ATyped S.R Γ t T →
      ATyped S.R Γ t' T ∧ Equal S.R Γ t.erase t'.erase T := by
  induction step with
  | betaBare body a =>
      intro Γ formed T typing
      refine ⟨ATyped.betaBare_preserve facts formed typing, ?_⟩
      rw [ATm.erase_inst0]
      exact (Typed.beta_preserve facts formed typing.erase).2
  | betaTyped W body a =>
      intro Γ formed T typing
      refine ⟨ATyped.betaTyped_preserve facts formed typing, ?_⟩
      rw [ATm.erase_inst0]
      exact (Typed.beta_preserve facts formed typing.erase).2
  | fstPair a b =>
      intro Γ formed T typing
      exact ⟨ATyped.fstPair_preserve facts formed typing,
        (Typed.fstPair_preserve facts formed typing.erase).2⟩
  | sndPair a b =>
      intro Γ formed T typing
      exact ⟨ATyped.sndPair_preserve facts formed typing,
        (Typed.sndPair_preserve facts formed typing.erase).2⟩
  | head same =>
      intro Γ formed T typing
      have typing' := heads same typing.erase
      exact ⟨ATyped.ofTyped typing', .headEq same typing.erase typing'⟩
  | root computes =>
      intro Γ formed T typing
      have typing' := roots formed computes typing.erase
      refine ⟨ATyped.ofTyped typing', ?_⟩
      rw [ATm.erase_ofTm]
      exact .root computes typing.erase typing'
  | congPiDom _ ih =>
      intro Γ formed T typing
      obtain ⟨u, v, w, tA, hu, tB, hv, join, le⟩ := typing.generation
      obtain ⟨tA', e⟩ := ih formed tA
      have tB' := ATyped.ctxConv tB ⟨u, hu, e⟩
      exact ⟨ATyped.subsume (.piForm tA' hu tB' hv join) le,
        Equal.subsume (.piCong e hu (.refl tB.erase) hv join) le⟩
  | congPiCod _ ih =>
      intro Γ formed T typing
      obtain ⟨u, v, w, tA, hu, tB, hv, join, le⟩ := typing.generation
      obtain ⟨tB', e⟩ := ih (.snoc formed ⟨u, hu, tA.erase⟩) tB
      exact ⟨ATyped.subsume (.piForm tA hu tB' hv join) le,
        Equal.subsume (.piCong (.refl tA.erase) hu e hv join) le⟩
  | congSigmaDom _ ih =>
      intro Γ formed T typing
      obtain ⟨u, v, w, tA, hu, tB, hv, join, le⟩ := typing.generation
      obtain ⟨tA', e⟩ := ih formed tA
      have tB' := ATyped.ctxConv tB ⟨u, hu, e⟩
      exact ⟨ATyped.subsume (.sigmaForm tA' hu tB' hv join) le,
        Equal.subsume (.sigmaCong e hu (.refl tB.erase) hv join) le⟩
  | congSigmaCod _ ih =>
      intro Γ formed T typing
      obtain ⟨u, v, w, tA, hu, tB, hv, join, le⟩ := typing.generation
      obtain ⟨tB', e⟩ := ih (.snoc formed ⟨u, hu, tA.erase⟩) tB
      exact ⟨ATyped.subsume (.sigmaForm tA hu tB' hv join) le,
        Equal.subsume (.sigmaCong (.refl tA.erase) hu e hv join) le⟩
  | congIdTy _ ih =>
      intro Γ formed T typing
      obtain ⟨u, tA, hu, ta, tb, le⟩ := typing.generation
      obtain ⟨tA', e⟩ := ih formed tA
      have equal : TypeEq S.R Γ _ _ := ⟨u, hu, e⟩
      exact ⟨ATyped.subsume
          (.idForm tA' hu (ATyped.convTypeEq ta equal) (ATyped.convTypeEq tb equal)) le,
        Equal.subsume (.idCong e hu (.refl ta.erase) (.refl tb.erase)) le⟩
  | congIdLeft _ ih =>
      intro Γ formed T typing
      obtain ⟨u, tA, hu, ta, tb, le⟩ := typing.generation
      obtain ⟨ta', e⟩ := ih formed ta
      exact ⟨ATyped.subsume (.idForm tA hu ta' tb) le,
        Equal.subsume (.idCong (.refl tA.erase) hu e (.refl tb.erase)) le⟩
  | congIdRight _ ih =>
      intro Γ formed T typing
      obtain ⟨u, tA, hu, ta, tb, le⟩ := typing.generation
      obtain ⟨tb', e⟩ := ih formed tb
      exact ⟨ATyped.subsume (.idForm tA hu ta tb') le,
        Equal.subsume (.idCong (.refl tA.erase) hu (.refl ta.erase) e) le⟩
  | congLamBare _ ih =>
      intro Γ formed T typing
      obtain ⟨A, B, u, tPi, hu, tb, le⟩ := typing.generation
      obtain ⟨⟨u', hu', tA⟩, _⟩ := IsType.pi_parts ⟨u, hu, tPi⟩
      obtain ⟨tb', e⟩ := ih (.snoc formed ⟨u', hu', tA⟩) tb
      exact ⟨ATyped.subsume (.lamBare tPi hu tb') le, Equal.subsume (.lamCong tPi hu e) le⟩
  | congLamDomain _ ih =>
      intro Γ formed T typing
      obtain ⟨A, B, u, v, tW, hv, agree, tPi, hu, tb, le⟩ := typing.generation
      obtain ⟨tW', e⟩ := ih formed tW
      exact ⟨ATyped.subsume (.lamTyped tW' hv (.trans (.symm e) agree) tPi hu tb) le,
        .refl typing.erase⟩
  | congLamTyped _ ih =>
      intro Γ formed T typing
      obtain ⟨A, B, u, v, tW, hv, agree, tPi, hu, tb, le⟩ := typing.generation
      obtain ⟨⟨u', hu', tA⟩, _⟩ := IsType.pi_parts ⟨u, hu, tPi⟩
      obtain ⟨tb', e⟩ := ih (.snoc formed ⟨u', hu', tA⟩) tb
      exact ⟨ATyped.subsume (.lamTyped tW hv agree tPi hu tb') le,
        Equal.subsume (.lamCong tPi hu e) le⟩
  | congAppFun _ ih =>
      intro Γ formed T typing
      obtain ⟨A, B, tf, ta, le⟩ := typing.generation
      obtain ⟨tf', e⟩ := ih formed tf
      exact ⟨ATyped.subsume (.appElim tf' ta) le,
        Equal.subsume (.appCong e (.refl ta.erase)) le⟩
  | congAppArg _ ih =>
      intro Γ formed T typing
      obtain ⟨A, B, tf, ta, le⟩ := typing.generation
      obtain ⟨ta', e⟩ := ih formed ta
      obtain ⟨w, hw, tPi⟩ := Typed.isType tf.erase formed
      obtain ⟨_, v, hv, family⟩ := IsType.pi_parts ⟨w, hw, tPi⟩
      have change := TypeEq.symm (TypeEq.of_instantiateEq family hv ta.erase e)
      exact ⟨ATyped.subsume (ATyped.convTypeEq (.appElim tf ta') change) le,
        Equal.subsume (.appCong (.refl tf.erase) e) le⟩
  | congPairFst _ ih =>
      intro Γ formed T typing
      obtain ⟨A, B, u, tSigma, hu, ta, tb, le⟩ := typing.generation
      obtain ⟨ta', e⟩ := ih formed ta
      obtain ⟨_, v, hv, family⟩ := IsType.sigma_parts ⟨u, hu, tSigma⟩
      have change := TypeEq.of_instantiateEq family hv ta.erase e
      exact ⟨ATyped.subsume (.pairIntro tSigma hu ta' (ATyped.convTypeEq tb change)) le,
        Equal.subsume (.pairCong tSigma hu e (.refl tb.erase)) le⟩
  | congPairSnd _ ih =>
      intro Γ formed T typing
      obtain ⟨A, B, u, tSigma, hu, ta, tb, le⟩ := typing.generation
      obtain ⟨tb', e⟩ := ih formed tb
      exact ⟨ATyped.subsume (.pairIntro tSigma hu ta tb') le,
        Equal.subsume (.pairCong tSigma hu (.refl ta.erase) e) le⟩
  | congFst _ ih =>
      intro Γ formed T typing
      obtain ⟨A, B, tp, le⟩ := typing.generation
      obtain ⟨tp', e⟩ := ih formed tp
      exact ⟨ATyped.subsume (.fstElim tp') le, Equal.subsume (.fstCong e) le⟩
  | congSnd _ ih =>
      intro Γ formed T typing
      obtain ⟨A, B, tp, le⟩ := typing.generation
      obtain ⟨tp', e⟩ := ih formed tp
      obtain ⟨w, hw, tSigma⟩ := Typed.isType tp.erase formed
      obtain ⟨_, v, hv, family⟩ := IsType.sigma_parts ⟨w, hw, tSigma⟩
      have change :=
        TypeEq.symm (TypeEq.of_instantiateEq family hv (.fstElim tp.erase) (.fstCong e))
      exact ⟨ATyped.subsume (ATyped.convTypeEq (.sndElim tp') change) le,
        Equal.subsume (.sndCong e) le⟩
  | congRefl _ ih =>
      intro Γ formed T typing
      obtain ⟨A, ta, le⟩ := typing.generation
      obtain ⟨ta', e⟩ := ih formed ta
      obtain ⟨u, hu, tA⟩ := Typed.isType ta.erase formed
      have change : TypeEq S.R Γ (.id A _ _) (.id A _ _) :=
        ⟨u, hu, .idCong (.refl tA) hu (.symm e) (.symm e)⟩
      exact ⟨ATyped.subsume (ATyped.convTypeEq (.reflIntro ta') change) le,
        Equal.subsume (.reflCong e) le⟩

/-- Finitely many steps on written terms preserve annotated typing and are a
typed equality between the erasures. -/
theorem ATm.Steps.preserve (roots : RootPreserving S.R) (heads : HeadPreserving S.R) {n : Nat}
    {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {t t' : ATm Head n} {T : Tm Head n}
    (steps : ATm.Steps S.R.computation S.R.headEq t t') (typing : ATyped S.R Γ t T) :
    ATyped S.R Γ t' T ∧ Equal S.R Γ t.erase t'.erase T := by
  induction steps with
  | refl => exact ⟨typing, .refl typing.erase⟩
  | tail _ step ih =>
      obtain ⟨typing', e⟩ := ih
      obtain ⟨typing'', e'⟩ := ATm.Step.preserve facts roots heads step formed typing'
      exact ⟨typing'', .trans e e'⟩

/-- A written term is equal to what it computes to, at every type it has. -/
theorem AEqual.of_steps (roots : RootPreserving S.R) (heads : HeadPreserving S.R) {n : Nat}
    {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {t t' : ATm Head n} {T : Tm Head n}
    (steps : ATm.Steps S.R.computation S.R.headEq t t') (typing : ATyped S.R Γ t T) :
    AEqual S.R Γ t t' T := by
  obtain ⟨typing', e⟩ := ATm.Steps.preserve facts roots heads formed steps typing
  exact ⟨typing, typing', e⟩

end Steps

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
