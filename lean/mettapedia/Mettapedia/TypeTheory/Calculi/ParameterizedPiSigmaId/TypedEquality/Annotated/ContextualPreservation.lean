import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.RootPreservation

/-!
# Every step of a typed annotated term is an equality at its type

`CStepCore` is one step of annotated terms at any position: β for functions, the two
projections of pairs, head equality and the declared root steps, under every former and
inside the domain of an abstraction. `Inversion` and `FormFactsTransfer` treat the steps at
the head of a term. This file treats every position.

* **One step** (`CStepCore.equal`): a step of a term typed in a formed context is an
  equality at the term's type. So the reduct is typed at that type (`CStepCore.typed`).
* **Reduction** (`CReduces`, the steps taken any number of times): the same
  (`CReduces.equal`, `CReduces.typed`).

No termination is used and none follows: the statements hold along every reduction of a
package, finite pieces of a reduction that never stops included.

Three properties of the package are hypotheses, because they are admission obligations and
not consequences of the rules:

* the type formers are injective and distinct (`CFormerFacts`), which the contractions need
  to invert the typing of an abstraction and of a pair;
* a declared root step of a typed term is an equality (`CRootAdmitted`);
* head equality preserves typing (`CHeadPreserving`).

Positive example: in every package with the three properties, the β-redex of the identity
at a typed argument is equal to its argument at the argument's type
(`identity_apply_equal`). Negative example: without the typing of the redex the statement
has no content, and a redex whose argument is not typed at the abstraction's domain is not
typed at all in a package with injective type formers, although it takes a step
(`CTyped.beta_argument`: a typed β-redex has its argument typed at the annotated domain).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Annotated

open Normalization (LevelModel)
open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {R : Rules Head}

/-- **Head equality preserves typing**: a head typed at a type, replaced by an equal head,
is typed at that type. -/
def CHeadPreserving (P : ChurchRules R) : Prop :=
  ∀ {n : Nat} {Γ : CCtx Head n} {h h' : Head} {A : CTm Head n}, R.headEq h h' →
    CTyped P Γ (.head h) A → CTyped P Γ (.head h') A

/-- **Reduction of annotated terms**: the steps of a package at any position, taken any
number of times. -/
abbrev CReduces (P : ChurchRules R) {n : Nat} (t u : CTm Head n) : Prop :=
  Relation.ReflTransGen (CStepCore P.computation R.headEq) t u

section Steps

variable {P : ChurchRules R} (facts : CFormerFacts P) (levels : LevelModel R L)
  (admitted : CRootAdmitted P) (heads : CHeadPreserving P)

include facts levels in
/-- A typed β-redex has its argument typed at the domain written on the abstraction. -/
theorem CTyped.beta_argument {n : Nat} {Γ : CCtx Head n} {D a T : CTm Head n}
    {body : CTm Head (n + 1)} (formed : CCtxFormed P Γ)
    (typing : CTyped P Γ (.app (.lam D body) a) T) : CTyped P Γ a D := by
  obtain ⟨A, B, tf, ta, _⟩ := typing.generation
  obtain ⟨E, u, w, _, _, tPi, hu, tb, leF⟩ := tf.generation
  have below := CTypeLe.toBelow leF (CTyped.isType levels tf formed)
  obtain ⟨eD, _⟩ := CBelow.pi_parts facts levels below formed
  exact CTyped.convType ta eD.symm

include facts levels admitted heads in
/-- **A step of a typed term is an equality at its type**, at every position of the term,
in a formed context. -/
theorem CStepCore.equal {n : Nat} {t u : CTm Head n}
    (step : CStepCore P.computation R.headEq t u) :
    ∀ {Γ : CCtx Head n}, CCtxFormed P Γ → ∀ {T : CTm Head n}, CTyped P Γ t T →
      CEqual P Γ t u T := by
  induction step with
  | betaPi A body a => exact fun formed _ typing => CTyped.beta_equal facts levels formed typing
  | betaSigmaFst a b =>
      exact fun formed _ typing => CTyped.fstPair_equal facts levels formed typing
  | betaSigmaSnd a b =>
      exact fun formed _ typing => CTyped.sndPair_equal facts levels formed typing
  | head same => exact fun _ _ typing => .headEq same typing (heads same typing)
  | root s => exact fun formed _ typing => admitted formed s typing
  | congPiDom _ ih =>
      intro Γ formed T typing
      obtain ⟨u, v, w, tA, hu, tB, hv, join, le⟩ := typing.generation
      exact CEqual.subsume (.piCong (ih formed tA) hu (.refl tB) hv join) le
  | congPiCod _ ih =>
      intro Γ formed T typing
      obtain ⟨u, v, w, tA, hu, tB, hv, join, le⟩ := typing.generation
      exact CEqual.subsume
        (.piCong (.refl tA) hu (ih (.snoc formed ⟨u, hu, tA⟩) tB) hv join) le
  | congSigmaDom _ ih =>
      intro Γ formed T typing
      obtain ⟨u, v, w, tA, hu, tB, hv, join, le⟩ := typing.generation
      exact CEqual.subsume (.sigmaCong (ih formed tA) hu (.refl tB) hv join) le
  | congSigmaCod _ ih =>
      intro Γ formed T typing
      obtain ⟨u, v, w, tA, hu, tB, hv, join, le⟩ := typing.generation
      exact CEqual.subsume
        (.sigmaCong (.refl tA) hu (ih (.snoc formed ⟨u, hu, tA⟩) tB) hv join) le
  | congIdTy _ ih =>
      intro Γ formed T typing
      obtain ⟨u, tA, hu, ta, tb, le⟩ := typing.generation
      exact CEqual.subsume (.idCong (ih formed tA) hu (.refl ta) (.refl tb)) le
  | congIdLeft _ ih =>
      intro Γ formed T typing
      obtain ⟨u, tA, hu, ta, tb, le⟩ := typing.generation
      exact CEqual.subsume (.idCong (.refl tA) hu (ih formed ta) (.refl tb)) le
  | congIdRight _ ih =>
      intro Γ formed T typing
      obtain ⟨u, tA, hu, ta, tb, le⟩ := typing.generation
      exact CEqual.subsume (.idCong (.refl tA) hu (.refl ta) (ih formed tb)) le
  | congLamDom _ ih =>
      intro Γ formed T typing
      obtain ⟨B, u, w, tA, hw, tPi, hu, tb, le⟩ := typing.generation
      exact CEqual.subsume (.lamCong (ih formed tA) hw tPi hu (.refl tb)) le
  | congLam _ ih =>
      intro Γ formed T typing
      obtain ⟨B, u, w, tA, hw, tPi, hu, tb, le⟩ := typing.generation
      exact CEqual.subsume
        (.lamCong (.refl tA) hw tPi hu (ih (.snoc formed ⟨w, hw, tA⟩) tb)) le
  | congAppFun _ ih =>
      intro Γ formed T typing
      obtain ⟨A, B, tf, ta, le⟩ := typing.generation
      exact CEqual.subsume (.appCong (ih formed tf) (.refl ta)) le
  | congAppArg _ ih =>
      intro Γ formed T typing
      obtain ⟨A, B, tf, ta, le⟩ := typing.generation
      exact CEqual.subsume (.appCong (.refl tf) (ih formed ta)) le
  | congPairFst _ ih =>
      intro Γ formed T typing
      obtain ⟨A, B, u, tS, hu, ta, tb, le⟩ := typing.generation
      exact CEqual.subsume (.pairCong tS hu (ih formed ta) (.refl tb)) le
  | congPairSnd _ ih =>
      intro Γ formed T typing
      obtain ⟨A, B, u, tS, hu, ta, tb, le⟩ := typing.generation
      exact CEqual.subsume (.pairCong tS hu (.refl ta) (ih formed tb)) le
  | congFst _ ih =>
      intro Γ formed T typing
      obtain ⟨A, B, tp, le⟩ := typing.generation
      exact CEqual.subsume (.fstCong (ih formed tp)) le
  | congSnd _ ih =>
      intro Γ formed T typing
      obtain ⟨A, B, tp, le⟩ := typing.generation
      exact CEqual.subsume (.sndCong (ih formed tp)) le
  | congRefl _ ih =>
      intro Γ formed T typing
      obtain ⟨A, ta, le⟩ := typing.generation
      exact CEqual.subsume (.reflCong (ih formed ta)) le

include facts levels admitted heads in
/-- **Subject reduction**: the reduct of a typed term is typed at the term's type. -/
theorem CStepCore.typed {n : Nat} {Γ : CCtx Head n} {t u T : CTm Head n}
    (formed : CCtxFormed P Γ) (step : CStepCore P.computation R.headEq t u)
    (typing : CTyped P Γ t T) : CTyped P Γ u T :=
  (CEqual.typed levels (CStepCore.equal facts levels admitted heads step formed typing)
    formed).2

include facts levels admitted heads in
/-- **Reduction of a typed term is an equality at its type**, whether or not it has reached
a term with no step. -/
theorem CReduces.equal {n : Nat} {Γ : CCtx Head n} {t u T : CTm Head n}
    (formed : CCtxFormed P Γ) (reduces : CReduces P t u) (typing : CTyped P Γ t T) :
    CEqual P Γ t u T := by
  induction reduces with
  | refl => exact .refl typing
  | tail _ step ih =>
      exact .trans ih (CStepCore.equal facts levels admitted heads step formed
        (CEqual.typed levels ih formed).2)

include facts levels admitted heads in
/-- Every term a typed term reduces to is typed at the term's type. -/
theorem CReduces.typed {n : Nat} {Γ : CCtx Head n} {t u T : CTm Head n}
    (formed : CCtxFormed P Γ) (reduces : CReduces P t u) (typing : CTyped P Γ t T) :
    CTyped P Γ u T :=
  (CEqual.typed levels (CReduces.equal facts levels admitted heads formed reduces typing)
    formed).2

include facts levels admitted heads in
/-- **Two reducts of one typed term are equal at its type.** No confluence is used: the two
are equal to the term they come from. -/
theorem CReduces.join_equal {n : Nat} {Γ : CCtx Head n} {t u v T : CTm Head n}
    (formed : CCtxFormed P Γ) (first : CReduces P t u) (second : CReduces P t v)
    (typing : CTyped P Γ t T) : CEqual P Γ u v T :=
  .trans (.symm (CReduces.equal facts levels admitted heads formed first typing))
    (CReduces.equal facts levels admitted heads formed second typing)

include facts levels in
/-- Positive example: the identity applied to a typed term is equal to the term, at its
type. -/
theorem identity_apply_equal {n : Nat} {Γ : CCtx Head n} {A a T : CTm Head n}
    (formed : CCtxFormed P Γ) (typing : CTyped P Γ (.app (.lam A (.var 0)) a) T) :
    CEqual P Γ (.app (.lam A (.var 0)) a) a T :=
  CTyped.beta_equal facts levels formed typing

end Steps

end Annotated
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
