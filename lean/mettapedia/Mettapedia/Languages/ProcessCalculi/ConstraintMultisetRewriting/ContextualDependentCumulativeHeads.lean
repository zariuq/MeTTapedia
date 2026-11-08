import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCumulativeNarrowing
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Synthesis

/-!
# Normal forms equal up to heads are equal; narrowing reflects equality

Two results on η-long β-normal forms, and the reflection they give.

* **The type a neutral spine's head assigns is principal** (`spine_principal`): every type of the spine lies above
  it. By generation, with the inversion of subtyping at Π and Σ types.
* **A normal form is equal to every term that is the same up to heads** (`equal_of_same`), at its type. Heads related
  by the package's head equality are equal at every type of the first (`HeadPreserving`); every other position is a
  congruence. The universe at which a normal type is compared is the one it is typed at: for a neutral type, the
  spine's principal type lies below that universe.
* **Narrowing reflects equality** (`equal_of_narrows`): two terms typed in `Γ` that are equal in a narrowing `Δ` are
  equal in `Γ`. Their normal forms in `Γ` stay normal in `Δ`, agree there up to heads, and so are equal in `Γ`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentCumulative

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open ContextualDependentEtaLong

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-! ## Principal types of neutral spines -/

section Principal

variable (facts : FormFacts S.R S.roles)
include facts

/-- **The type a neutral spine's head assigns lies below every type of the spine.** -/
theorem spine_principal : ∀ {n : Nat} (t : Tm Head n) {Γ : Ctx Head n} {U T : Tm Head n},
    CtxFormed S.R Γ → Long S.R S.roles (.spine Γ t U) → Typed S.R Γ t T → Below S.R Γ U T := by
  intro n t
  induction t with
  | var i =>
      intro Γ U T formed long typed
      cases long with
      | var _ e =>
          have generation : TypeLe S.R Γ (Ctx.lookup Γ i) T := Typed.generation typed
          exact .subTrans e.below (TypeLe.toBelow generation (Typed.isType typed formed))
  | const c =>
      intro Γ U T formed long typed
      cases long with
      | const _ declared _ e =>
          have generation : GenerationAt S.R Γ (.const c) T := Typed.generation typed
          obtain ⟨type, u, declared', _, _, le⟩ := generation
          rw [declared] at declared'
          cases declared'
          exact .subTrans e.below (TypeLe.toBelow le (Typed.isType typed formed))
  | app f a ihf _ =>
      intro Γ U T formed long typed
      cases long with
      | app lf eF la eU =>
          have generation : GenerationAt S.R Γ (.app f a) T := Typed.generation typed
          obtain ⟨A', B', tf, _, le⟩ := generation
          obtain ⟨A₀, B₀, eF₀, _, leB⟩ :=
            Below.pi_inv facts (ihf formed lf tf) formed (IsType.refl (Typed.isType tf formed))
          obtain ⟨eA, eB⟩ := TypeEq.pi_injective facts (TypeEq.trans S.levels eF.symm eF₀) formed
          have leB' := Derivable.subTrans eB.below (Below.ctxConv leB eA.symm)
          have instantiated := TypeLe.instantiate (TypeLe.of_below leB') (Long.sound la)
          exact .subTrans eU.below (TypeLe.toBelow (TypeLe.trans instantiated le) (Typed.isType typed formed))
  | fst p ih =>
      intro Γ U T formed long typed
      cases long with
      | fst lp eP eU =>
          have generation : GenerationAt S.R Γ (.fst p) T := Typed.generation typed
          obtain ⟨A', B', tp, le⟩ := generation
          obtain ⟨A₀, B₀, eP₀, leA, _⟩ :=
            Below.sigma_inv facts (ih formed lp tp) formed (IsType.refl (Typed.isType tp formed))
          obtain ⟨eA, _⟩ := TypeEq.sigma_injective facts (TypeEq.trans S.levels eP.symm eP₀) formed
          exact .subTrans eU.below
            (.subTrans eA.below (.subTrans leA (TypeLe.toBelow le (Typed.isType typed formed))))
  | snd p ih =>
      intro Γ U T formed long typed
      cases long with
      | snd lp eP eU =>
          have generation : GenerationAt S.R Γ (.snd p) T := Typed.generation typed
          obtain ⟨A', B', tp, le⟩ := generation
          obtain ⟨A₀, B₀, eP₀, _, leB⟩ :=
            Below.sigma_inv facts (ih formed lp tp) formed (IsType.refl (Typed.isType tp formed))
          obtain ⟨eA, eB⟩ := TypeEq.sigma_injective facts (TypeEq.trans S.levels eP.symm eP₀) formed
          have leB' := Derivable.subTrans eB.below (Below.ctxConv leB eA.symm)
          have first : Typed S.R Γ (.fst p) _ := .fstElim (Typed.convType (Long.sound lp) eP)
          have instantiated := TypeLe.instantiate (TypeLe.of_below leB') first
          exact .subTrans eU.below (TypeLe.toBelow (TypeLe.trans instantiated le) (Typed.isType typed formed))
  | head _ =>
      intro Γ U T _ long _
      cases long
  | pi _ _ _ _ =>
      intro Γ U T _ long _
      cases long
  | sigma _ _ _ _ =>
      intro Γ U T _ long _
      cases long
  | id _ _ _ _ _ _ =>
      intro Γ U T _ long _
      cases long
  | lam _ _ =>
      intro Γ U T _ long _
      cases long
  | pair _ _ _ _ =>
      intro Γ U T _ long _
      cases long
  | refl _ _ =>
      intro Γ U T _ long _
      cases long

end Principal

/-! ## Equality up to heads -/

/-- What a normal form gives against a term that is the same up to heads: a normal type is equal to it at every
universe it is typed at, a normal term at its type, a neutral spine at the type its head assigns. -/
def SameEqualAt (S : Setting Head L) : LongStatement Head → Prop
  | .type Γ V => CtxFormed S.R Γ → ∀ {W}, SameUpToHeads S.R V W → ∀ {u}, S.R.isUniverse u →
      Typed S.R Γ V (.head u) → Equal S.R Γ V W (.head u)
  | .term Γ v T => CtxFormed S.R Γ → ∀ {w}, SameUpToHeads S.R v w → Equal S.R Γ v w T
  | .spine Γ t U => CtxFormed S.R Γ → ∀ {w}, SameUpToHeads S.R t w → Equal S.R Γ t w U

section Same

variable (facts : FormFacts S.R S.roles) (heads : HeadPreserving S.R)
include facts heads

/-- **η-long normal forms are equal to the terms that are the same up to heads.** -/
theorem Long.sameEqual {st : LongStatement Head} (long : Long S.R S.roles st) : SameEqualAt S st := by
  induction long with
  | head _ =>
      intro formed W same u hu typed
      cases same with
      | head hs =>
          rcases hs with rfl | e
          · exact .refl typed
          · exact .headEq e typed (heads e typed)
  | pi lA _ _ ihA ihB =>
      intro formed W same u hu typed
      cases same with
      | pi sA sB =>
          have generation : GenerationAt S.R _ (.pi _ _) (.head u) := Typed.generation typed
          obtain ⟨u₁, u₂, w, tA, hu₁, tB, hu₂, join, le⟩ := generation
          exact Equal.subsume (.piCong (ihA formed sA hu₁ tA) hu₁ (ihB (formed.snoc lA.isType) sB hu₂ tB) hu₂ join)
            le
  | sigma lA _ _ ihA ihB =>
      intro formed W same u hu typed
      cases same with
      | sigma sA sB =>
          have generation : GenerationAt S.R _ (.sigma _ _) (.head u) := Typed.generation typed
          obtain ⟨u₁, u₂, w, tA, hu₁, tB, hu₂, join, le⟩ := generation
          exact Equal.subsume
            (.sigmaCong (ihA formed sA hu₁ tA) hu₁ (ihB (formed.snoc lA.isType) sB hu₂ tB) hu₂ join) le
  | id _ _ _ _ ihA ihx ihy =>
      intro formed W same u hu typed
      cases same with
      | id sA sx sy =>
          have generation : GenerationAt S.R _ (.id _ _ _) (.head u) := Typed.generation typed
          obtain ⟨u₁, tA, hu₁, _, _, le⟩ := generation
          exact Equal.subsume (.idCong (ihA formed sA hu₁ tA) hu₁ (ihx formed sx) (ihy formed sy)) le
  | neutralType ls _ _ ih =>
      intro formed W same u hu typed
      exact .subEq (ih formed same) (spine_principal facts _ formed ls typed)
  | univ hu e typed _ ih =>
      intro formed w same
      exact Equal.convType (ih formed same hu (Typed.convType typed e)) e.symm
  | lam e isA _ _ ih =>
      intro formed w same
      cases same with
      | lam sb =>
          obtain ⟨u, hu, tPi⟩ := (TypeEq.isType e formed).2
          exact Equal.convType (.lamCong tPi hu (ih (formed.snoc isA) sb)) e.symm
  | pair e _ _ _ iha ihb =>
      intro formed w same
      cases same with
      | pair sa sb =>
          obtain ⟨u, hu, tSigma⟩ := (TypeEq.isType e formed).2
          exact Equal.convType (.pairCong tSigma hu (iha formed sa) (ihb formed sb)) e.symm
  | refl e typed _ ih =>
      intro formed w same
      cases same with
      | refl sz =>
          have generation : GenerationAt S.R _ (.refl _) _ := Typed.generation typed
          obtain ⟨A', _, le⟩ := generation
          have eId := TypeLe.id_eq facts le (Typed.isType typed formed) formed
          obtain ⟨eA, _, _⟩ := TypeEq.id_injective facts (TypeEq.trans S.levels eId e) formed
          exact Equal.convType (.reflCong (Equal.convType (ih formed sz) eA.symm)) eId
  | neutral _ le _ _ ih =>
      intro formed w same
      exact .subEq (ih formed same) le
  | var i e =>
      intro formed w same
      cases same
      exact .refl (Typed.convType (Derivable.var i) e.symm)
  | const _ _ typed e =>
      intro formed w same
      cases same
      exact .refl (Typed.convType typed e.symm)
  | app _ eF _ eU ihf iha =>
      intro formed w same
      cases same with
      | app sf sa => exact Equal.convType (.appCong (Equal.convType (ihf formed sf) eF) (iha formed sa)) eU.symm
  | fst _ eP eU ih =>
      intro formed w same
      cases same with
      | fst sp => exact Equal.convType (.fstCong (Equal.convType (ih formed sp) eP)) eU.symm
  | snd _ eP eU ih =>
      intro formed w same
      cases same with
      | snd sp => exact Equal.convType (.sndCong (Equal.convType (ih formed sp) eP)) eU.symm

/-- **A normal term is equal, at its type, to every term that is the same up to heads.** -/
theorem equal_of_same {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {v w A : Tm Head n}
    (long : Long S.R S.roles (.term Γ v A)) (same : SameUpToHeads S.R v w) : Equal S.R Γ v w A :=
  Long.sameEqual facts heads long formed same

end Same

/-! ## Narrowing reflects equality -/

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
include facts roots heads algebra rigid complete

/-- **Narrowing reflects equality**: two terms typed in `Γ` and equal in a narrowing `Δ` are equal in `Γ`. -/
theorem equal_of_narrows {n : Nat} {Γ Δ : Ctx Head n} (narrows : CtxNarrows S.R Γ Δ) (formedΓ : CtxFormed S.R Γ)
    (formedΔ : CtxFormed S.R Δ) {s t A : Tm Head n} (ts : Typed S.R Γ s A) (tt : Typed S.R Γ t A)
    (equal : Equal S.R Δ s t A) : Equal S.R Γ s t A := by
  obtain ⟨v, first⟩ := long_exists facts roots heads algebra rigid complete formedΓ ts
  obtain ⟨w, second⟩ := long_exists facts roots heads algebra rigid complete formedΓ tt
  have same := same_of_narrows facts roots heads algebra complete narrows formedΓ formedΔ first second equal
  exact .trans first.2 (.trans (equal_of_same facts heads formedΓ first.1 same) (.symm second.2))

end ContextualDependentCumulative
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
