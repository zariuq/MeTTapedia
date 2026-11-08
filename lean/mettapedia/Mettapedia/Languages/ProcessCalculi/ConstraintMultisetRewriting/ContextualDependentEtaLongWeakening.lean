import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaLongExistence

/-!
# η-long normal forms under renaming and weakening

A renaming of a formed context into a formed context keeps η-long β-normal forms: a normal type,
a normal term at a type and a neutral spine stay so after renaming, at the renamed type
(`Long.rename`). Weakening past one declaration is the instance at `wk` (`Long.weaken`).

The only case with content is the `Base` condition of a neutral term: the renamed type must not be
equal to any Π or Σ type of the target context, including those that mention variables outside the
image of the renaming. The weak-head form of the type is read in the source context instead
(`FormFacts.typeForm`), renamed, and compared with the Π or Σ type by matching weak-head forms
(`FormFacts.forms`); renaming does not change the outermost former, so the source type is equal to a
Π or Σ type too (`Base.rename`). No injectivity of the renaming is needed, and no root step is
reflected.

With uniqueness (R88), the normal form of a renamed term is the renamed normal form, up to heads
(`normalForm_rename_unique`, `long_type_rename_unique`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentEtaLong

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-! ## The `Base` condition under renaming -/

/-- **A type that is not a Π or Σ type stays so under renaming** into a formed context. -/
theorem Base.rename (facts : FormFacts S.R S.roles) {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m}
    {ρ : Ren n m} {T : Tm Head n} (base : Base S.R Γ T) (isT : IsType S.R Γ T)
    (formedΓ : CtxFormed S.R Γ) (formedΔ : CtxFormed S.R Δ) (compatible : CtxRen Γ Δ ρ) :
    Base S.R Δ (Presentation.rename ρ T) := by
  obtain ⟨T', red, form⟩ := facts.typeForm isT formedΓ
  have renamed : TypeEq S.R Δ (Presentation.rename ρ T) (Presentation.rename ρ T') :=
    red.typeEq.rename compatible
  have form' := form.rename ρ
  constructor
  · intro A B equal
    have back : TypeEq S.R Δ (.pi A B) (Presentation.rename ρ T') :=
      TypeEq.trans S.levels equal.symm renamed
    obtain ⟨A₂, B₂, same, _, _⟩ := (facts.forms back formedΔ (.inr (.inl ⟨_, _, rfl⟩)) form').pi_left
    cases T' with
    | pi C D => exact base.1 C D red.typeEq
    | var _ | const _ | head _ | sigma _ _ | id _ _ _ | lam _ | app _ _ | pair _ _ | fst _ | snd _ | refl _ =>
        simp only [Presentation.rename, reduceCtorEq] at same
  · intro A B equal
    have back : TypeEq S.R Δ (.sigma A B) (Presentation.rename ρ T') :=
      TypeEq.trans S.levels equal.symm renamed
    obtain ⟨A₂, B₂, same, _, _⟩ :=
      (facts.forms back formedΔ (.inr (.inr (.inl ⟨_, _, rfl⟩))) form').sigma_left
    cases T' with
    | sigma C D => exact base.2 C D red.typeEq
    | var _ | const _ | head _ | pi _ _ | id _ _ _ | lam _ | app _ _ | pair _ _ | fst _ | snd _ | refl _ =>
        simp only [Presentation.rename, reduceCtorEq] at same

/-! ## Normal forms under renaming -/

/-- What a normal form gives along a renaming between formed contexts. -/
def RenamesAt (S : Setting Head L) : LongStatement Head → Prop
  | .type Γ V => ∀ {m : Nat} {Δ : Ctx Head m} {ρ : Ren _ m}, CtxRen Γ Δ ρ → CtxFormed S.R Γ →
      CtxFormed S.R Δ → Long S.R S.roles (.type Δ (Presentation.rename ρ V))
  | .term Γ v T => ∀ {m : Nat} {Δ : Ctx Head m} {ρ : Ren _ m}, CtxRen Γ Δ ρ → CtxFormed S.R Γ →
      CtxFormed S.R Δ → Long S.R S.roles (.term Δ (Presentation.rename ρ v) (Presentation.rename ρ T))
  | .spine Γ t U => ∀ {m : Nat} {Δ : Ctx Head m} {ρ : Ren _ m}, CtxRen Γ Δ ρ → CtxFormed S.R Γ →
      CtxFormed S.R Δ → Long S.R S.roles (.spine Δ (Presentation.rename ρ t) (Presentation.rename ρ U))

/-- **η-long normal forms are kept by renamings** between formed contexts. -/
theorem Long.rename (facts : FormFacts S.R S.roles) {st : LongStatement Head}
    (long : Long S.R S.roles st) : RenamesAt S st := by
  induction long with
  | head isType =>
      intro m Δ ρ compatible _ _
      exact .head (isType.rename compatible)
  | pi lA _ isType ihA ihB =>
      intro m Δ ρ compatible formedΓ formedΔ
      exact .pi (ihA compatible formedΓ formedΔ)
        (ihB (compatible.snoc _) (formedΓ.snoc lA.isType) (formedΔ.snoc (lA.isType.rename compatible)))
        (isType.rename compatible)
  | sigma lA _ isType ihA ihB =>
      intro m Δ ρ compatible formedΓ formedΔ
      exact .sigma (ihA compatible formedΓ formedΔ)
        (ihB (compatible.snoc _) (formedΓ.snoc lA.isType) (formedΔ.snoc (lA.isType.rename compatible)))
        (isType.rename compatible)
  | id _ _ _ isType ihA ihx ihy =>
      intro m Δ ρ compatible formedΓ formedΔ
      exact .id (ihA compatible formedΓ formedΔ) (ihx compatible formedΓ formedΔ)
        (ihy compatible formedΓ formedΔ) (isType.rename compatible)
  | neutralType _ hu le ih =>
      intro m Δ ρ compatible formedΓ formedΔ
      exact .neutralType (ih compatible formedΓ formedΔ) hu (Derivable.renames le compatible)
  | univ hu e typed _ ih =>
      intro m Δ ρ compatible formedΓ formedΔ
      exact .univ hu (e.rename compatible) (typed.rename compatible) (ih compatible formedΓ formedΔ)
  | lam e isA typed _ ih =>
      intro m Δ ρ compatible formedΓ formedΔ
      exact .lam (e.rename compatible) (isA.rename compatible) (typed.rename compatible)
        (ih (compatible.snoc _) (formedΓ.snoc isA) (formedΔ.snoc (isA.rename compatible)))
  | pair e typed _ _ iha ihb =>
      intro m Δ ρ compatible formedΓ formedΔ
      have lb := ihb compatible formedΓ formedΔ
      rw [rename_inst0] at lb
      exact .pair (e.rename compatible) (typed.rename compatible) (iha compatible formedΓ formedΔ) lb
  | refl e typed _ ih =>
      intro m Δ ρ compatible formedΓ formedΔ
      exact .refl (e.rename compatible) (typed.rename compatible) (ih compatible formedΓ formedΔ)
  | neutral _ le typed base ih =>
      intro m Δ ρ compatible formedΓ formedΔ
      exact .neutral (ih compatible formedΓ formedΔ) (Derivable.renames le compatible) (typed.rename compatible)
        (base.rename facts (Typed.isType typed formedΓ) formedΓ formedΔ compatible)
  | var i e =>
      intro m Δ ρ compatible _ _
      have e' := e.rename compatible
      rw [← compatible i] at e'
      exact .var (ρ i) e'
  | const role declared typed e =>
      intro m Δ ρ compatible _ _
      have typed' := typed.rename compatible
      have e' := e.rename compatible
      rw [rename_liftClosed] at typed' e'
      exact .const role declared typed' e'
  | app _ eF _ eU ihf iha =>
      intro m Δ ρ compatible formedΓ formedΔ
      have eU' := eU.rename compatible
      rw [rename_inst0] at eU'
      exact .app (ihf compatible formedΓ formedΔ) (eF.rename compatible) (iha compatible formedΓ formedΔ) eU'
  | fst _ eP eU ih =>
      intro m Δ ρ compatible formedΓ formedΔ
      exact .fst (ih compatible formedΓ formedΔ) (eP.rename compatible) (eU.rename compatible)
  | snd _ eP eU ih =>
      intro m Δ ρ compatible formedΓ formedΔ
      have eU' := eU.rename compatible
      rw [rename_inst0] at eU'
      exact .snd (ih compatible formedΓ formedΔ) (eP.rename compatible) eU'

section Instances

variable (facts : FormFacts S.R S.roles)
include facts

theorem Long.type_rename {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {ρ : Ren n m} {V : Tm Head n}
    (long : Long S.R S.roles (.type Γ V)) (compatible : CtxRen Γ Δ ρ) (formedΓ : CtxFormed S.R Γ)
    (formedΔ : CtxFormed S.R Δ) : Long S.R S.roles (.type Δ (Presentation.rename ρ V)) :=
  long.rename facts compatible formedΓ formedΔ

theorem Long.term_rename {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {ρ : Ren n m} {v T : Tm Head n}
    (long : Long S.R S.roles (.term Γ v T)) (compatible : CtxRen Γ Δ ρ) (formedΓ : CtxFormed S.R Γ)
    (formedΔ : CtxFormed S.R Δ) :
    Long S.R S.roles (.term Δ (Presentation.rename ρ v) (Presentation.rename ρ T)) :=
  long.rename facts compatible formedΓ formedΔ

/-- **Weakening keeps normal types.** -/
theorem Long.type_weaken {n : Nat} {Γ : Ctx Head n} {V B : Tm Head n} (long : Long S.R S.roles (.type Γ V))
    (formed : CtxFormed S.R Γ) (isB : IsType S.R Γ B) :
    Long S.R S.roles (.type (.snoc Γ B) (Presentation.rename wk V)) :=
  long.type_rename facts (CtxRen.wk Γ B) formed (formed.snoc isB)

/-- **Weakening keeps normal terms**, at the weakened type. -/
theorem Long.term_weaken {n : Nat} {Γ : Ctx Head n} {v A B : Tm Head n} (long : Long S.R S.roles (.term Γ v A))
    (formed : CtxFormed S.R Γ) (isB : IsType S.R Γ B) :
    Long S.R S.roles (.term (.snoc Γ B) (Presentation.rename wk v) (Presentation.rename wk A)) :=
  long.term_rename facts (CtxRen.wk Γ B) formed (formed.snoc isB)

/-- **Normal forms are kept by renamings.** -/
theorem NormalForm.rename {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {ρ : Ren n m} {t v A : Tm Head n}
    (normal : NormalForm S.R S.roles Γ t v A) (compatible : CtxRen Γ Δ ρ) (formedΓ : CtxFormed S.R Γ)
    (formedΔ : CtxFormed S.R Δ) :
    NormalForm S.R S.roles Δ (Presentation.rename ρ t) (Presentation.rename ρ v) (Presentation.rename ρ A) :=
  ⟨normal.1.term_rename facts compatible formedΓ formedΔ, normal.2.rename compatible⟩

/-- **Normal forms commute with weakening.** -/
theorem NormalForm.weaken {n : Nat} {Γ : Ctx Head n} {t v A B : Tm Head n}
    (normal : NormalForm S.R S.roles Γ t v A) (formed : CtxFormed S.R Γ) (isB : IsType S.R Γ B) :
    NormalForm S.R S.roles (.snoc Γ B) (Presentation.rename wk t) (Presentation.rename wk v)
      (Presentation.rename wk A) :=
  normal.rename facts (CtxRen.wk Γ B) formed (formed.snoc isB)

variable (roots : RootPreserving S.R) (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R)
  (complete : AlgorithmicComplete S.R S.roles)
include roots heads algebra complete

/-- **The normal form of a renamed term is the renamed normal form**, up to heads. -/
theorem normalForm_rename_unique {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {ρ : Ren n m}
    {t v A : Tm Head n} {w : Tm Head m} (normal : NormalForm S.R S.roles Γ t v A)
    (renamed : NormalForm S.R S.roles Δ (Presentation.rename ρ t) w (Presentation.rename ρ A))
    (compatible : CtxRen Γ Δ ρ) (formedΓ : CtxFormed S.R Γ) (formedΔ : CtxFormed S.R Δ) :
    SameUpToHeads S.R w (Presentation.rename ρ v) := by
  have there := normal.rename facts compatible formedΓ formedΔ
  exact long_unique facts roots heads algebra complete formedΔ renamed.1 there.1
    (.trans (.symm renamed.2) there.2)

/-- **The normal type of a renamed type is the renamed normal type**, up to heads. -/
theorem long_type_rename_unique {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {ρ : Ren n m}
    {V N : Tm Head n} {W : Tm Head m} (lN : Long S.R S.roles (.type Γ N)) (VN : TypeEq S.R Γ V N)
    (lW : Long S.R S.roles (.type Δ W)) (VW : TypeEq S.R Δ (Presentation.rename ρ V) W)
    (compatible : CtxRen Γ Δ ρ) (formedΓ : CtxFormed S.R Γ) (formedΔ : CtxFormed S.R Δ) :
    SameUpToHeads S.R W (Presentation.rename ρ N) :=
  long_type_unique facts roots heads algebra complete formedΔ lW (lN.type_rename facts compatible formedΓ formedΔ)
    (TypeEq.trans S.levels VW.symm (VN.rename compatible))

end Instances

end ContextualDependentEtaLong
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
