import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaLongReflection
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaLongWeakening

/-!
# Narrowing universe declarations

The cumulative row of the census, `λ x. F x ≐ λ x. N` with `x : U0` where `F` declares `U1`, is read by comparing the
equation's local telescope with `F`'s binders up to cumulativity. Its exactness rests on comparing judgments in two
contexts that differ only at universe declarations.

`Δ` **narrows** `Γ` (`CtxNarrows`) when the two telescopes agree except at universe declarations, where `Δ` declares a
universe below `Γ`'s. Then:

* the identity is a typed substitution from `Γ` to `Δ` (`CtxNarrows.substMor`), so every typing, equality, type
  equality and subtyping of `Γ` holds in `Δ` (`typed_narrow`, `equal_narrow`, `typeEq_narrow`, `below_narrow`);
* a type that is not a Π or Σ type in `Γ` is not one in `Δ` (`Base.narrow`), by weak-head forms read in `Γ`;
* **every η-long β-normal form of `Γ` is one of `Δ`** (`Long.narrow`, `NormalForm.narrow`). A neutral spine headed by a
  narrowed declaration is a bare variable at a universe, since a universe is neither a Π nor a Σ type; its smaller
  universe still lies below every type the spine was used at;
* **narrowing reflects equality up to heads** (`same_of_narrows`): the normal forms in `Γ` of two terms equal in `Δ`
  agree up to heads. Equality itself is reflected in `ContextualDependentCumulativeHeads` (`equal_of_narrows`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentCumulative

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open ContextualDependentEtaLong

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-! ## Narrowed contexts -/

/-- **`Δ` narrows `Γ`**: the same telescope, except at universe declarations, where `Δ` declares a universe below
`Γ`'s. -/
inductive CtxNarrows (R : Rules Head) : {n : Nat} → Ctx Head n → Ctx Head n → Prop where
  | nil : CtxNarrows R .nil .nil
  | same {n : Nat} {Γ Δ : Ctx Head n} (A : Tm Head n) : CtxNarrows R Γ Δ → CtxNarrows R (.snoc Γ A) (.snoc Δ A)
  | lower {n : Nat} {Γ Δ : Ctx Head n} {u v : Head} :
      CtxNarrows R Γ Δ → R.cumulative v u → CtxNarrows R (.snoc Γ (.head u)) (.snoc Δ (.head v))

section Contexts

variable {R : Rules Head}

/-- Every declaration of `Δ` is the one of `Γ`, or a universe below `Γ`'s. -/
theorem CtxNarrows.lookup {n : Nat} {Γ Δ : Ctx Head n} (narrows : CtxNarrows R Γ Δ) :
    ∀ i, Ctx.lookup Δ i = Ctx.lookup Γ i ∨
      ∃ u v, Ctx.lookup Γ i = .head u ∧ Ctx.lookup Δ i = .head v ∧ R.cumulative v u := by
  induction narrows with
  | nil => intro i; exact i.elim0
  | same A _ ih =>
      intro i
      refine Fin.cases (.inl rfl) (fun j => ?_) i
      rw [Ctx.lookup_snoc_succ, Ctx.lookup_snoc_succ]
      rcases ih j with same | ⟨u, v, eΓ, eΔ, c⟩
      · exact .inl (by rw [same])
      · exact .inr ⟨u, v, by rw [eΓ]; rfl, by rw [eΔ]; rfl, c⟩
  | lower _ c ih =>
      intro i
      refine Fin.cases (.inr ⟨_, _, rfl, rfl, c⟩) (fun j => ?_) i
      rw [Ctx.lookup_snoc_succ, Ctx.lookup_snoc_succ]
      rcases ih j with same | ⟨u, v, eΓ, eΔ, c'⟩
      · exact .inl (by rw [same])
      · exact .inr ⟨u, v, by rw [eΓ]; rfl, by rw [eΔ]; rfl, c'⟩

/-- **The identity is a typed substitution from `Γ` to a narrowing `Δ`.** -/
theorem CtxNarrows.substMor {n : Nat} {Γ Δ : Ctx Head n} (narrows : CtxNarrows R Γ Δ) : SubstMor R Γ Δ ids := by
  intro i
  rw [subst_ids]
  rcases narrows.lookup i with same | ⟨u, v, eΓ, eΔ, c⟩
  · rw [← same]
    exact Derivable.var i
  · have typing := Derivable.var (R := R) (Γ := Δ) i
    rw [eΔ] at typing
    rw [eΓ]
    exact Derivable.cumul typing c

variable {n : Nat} {Γ Δ : Ctx Head n} (narrows : CtxNarrows R Γ Δ)
include narrows

theorem typed_narrow {t A : Tm Head n} (typing : Typed R Γ t A) : Typed R Δ t A := by
  simpa only [subst_ids] using Typed.substitute typing narrows.substMor

theorem equal_narrow {a b A : Tm Head n} (equality : Equal R Γ a b A) : Equal R Δ a b A := by
  simpa only [subst_ids] using Equal.substitute equality narrows.substMor

theorem typeEq_narrow {A B : Tm Head n} (equal : TypeEq R Γ A B) : TypeEq R Δ A B := by
  obtain ⟨u, hu, e⟩ := equal
  exact ⟨u, hu, equal_narrow narrows e⟩

theorem isType_narrow {A : Tm Head n} (formed : IsType R Γ A) : IsType R Δ A := by
  obtain ⟨u, hu, t⟩ := formed
  exact ⟨u, hu, typed_narrow narrows t⟩

theorem below_narrow {A B : Tm Head n} (le : Below R Γ A B) : Below R Δ A B := by
  have moved : Below R Δ (subst ids A) (subst ids B) := Derivable.substitutes le narrows.substMor
  simpa only [subst_ids] using moved

end Contexts

/-- Equal types are below each other. -/
theorem below_of_typeEq {R : Rules Head} {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n} (equal : TypeEq R Γ A B) :
    Below R Γ A B := by
  obtain ⟨u, hu, e⟩ := equal
  exact .subEqual e hu

/-! ## Normal forms under narrowing -/

/-- **A type that is not a Π or Σ type stays so under narrowing** into a formed context. -/
theorem Base.narrow (facts : FormFacts S.R S.roles) {n : Nat} {Γ Δ : Ctx Head n} {T : Tm Head n}
    (base : Base S.R Γ T) (isT : IsType S.R Γ T) (formedΓ : CtxFormed S.R Γ) (formedΔ : CtxFormed S.R Δ)
    (narrows : CtxNarrows S.R Γ Δ) : Base S.R Δ T := by
  obtain ⟨T', red, form⟩ := facts.typeForm isT formedΓ
  have narrowed : TypeEq S.R Δ T T' := typeEq_narrow narrows red.typeEq
  constructor
  · intro A B equal
    have back : TypeEq S.R Δ (.pi A B) T' := TypeEq.trans S.levels equal.symm narrowed
    obtain ⟨A₂, B₂, same, _, _⟩ := (facts.forms back formedΔ (.inr (.inl ⟨_, _, rfl⟩)) form).pi_left
    subst same
    exact base.1 A₂ B₂ red.typeEq
  · intro A B equal
    have back : TypeEq S.R Δ (.sigma A B) T' := TypeEq.trans S.levels equal.symm narrowed
    obtain ⟨A₂, B₂, same, _, _⟩ := (facts.forms back formedΔ (.inr (.inr (.inl ⟨_, _, rfl⟩))) form).sigma_left
    subst same
    exact base.2 A₂ B₂ red.typeEq

/-- What a normal form gives along a narrowing between formed contexts. A neutral spine keeps its type, or it is
headed by a narrowed declaration at a universe and takes the smaller universe. -/
def NarrowsAt (S : Setting Head L) : LongStatement Head → Prop
  | .type Γ V => ∀ {Δ}, CtxNarrows S.R Γ Δ → CtxFormed S.R Γ → CtxFormed S.R Δ → Long S.R S.roles (.type Δ V)
  | .term Γ v T => ∀ {Δ}, CtxNarrows S.R Γ Δ → CtxFormed S.R Γ → CtxFormed S.R Δ → Long S.R S.roles (.term Δ v T)
  | .spine Γ t U => ∀ {Δ}, CtxNarrows S.R Γ Δ → CtxFormed S.R Γ → CtxFormed S.R Δ →
      Long S.R S.roles (.spine Δ t U) ∨
        ∃ u v, TypeEq S.R Γ U (.head u) ∧ S.R.cumulative v u ∧ Long S.R S.roles (.spine Δ t (.head v))

/-- The smaller universe of a narrowed declaration lies below every type its spine was used at. -/
theorem below_of_narrowed {n : Nat} {Γ Δ : Ctx Head n} (narrows : CtxNarrows S.R Γ Δ) {U T : Tm Head n} {u v : Head}
    (e : TypeEq S.R Γ U (.head u)) (c : S.R.cumulative v u) (le : Below S.R Γ U T) : Below S.R Δ (.head v) T :=
  .subTrans (.subUniv c) (.subTrans (below_of_typeEq (typeEq_narrow narrows e.symm)) (below_narrow narrows le))

/-- **η-long normal forms are kept by narrowing** between formed contexts. -/
theorem Long.narrow (facts : FormFacts S.R S.roles) {st : LongStatement Head} (long : Long S.R S.roles st) :
    NarrowsAt S st := by
  induction long with
  | head isType =>
      intro Δ narrows _ _
      exact .head (isType_narrow narrows isType)
  | pi lA _ isType ihA ihB =>
      intro Δ narrows formedΓ formedΔ
      exact .pi (ihA narrows formedΓ formedΔ)
        (ihB (narrows.same _) (formedΓ.snoc lA.isType) (formedΔ.snoc (isType_narrow narrows lA.isType)))
        (isType_narrow narrows isType)
  | sigma lA _ isType ihA ihB =>
      intro Δ narrows formedΓ formedΔ
      exact .sigma (ihA narrows formedΓ formedΔ)
        (ihB (narrows.same _) (formedΓ.snoc lA.isType) (formedΔ.snoc (isType_narrow narrows lA.isType)))
        (isType_narrow narrows isType)
  | id _ _ _ isType ihA ihx ihy =>
      intro Δ narrows formedΓ formedΔ
      exact .id (ihA narrows formedΓ formedΔ) (ihx narrows formedΓ formedΔ) (ihy narrows formedΓ formedΔ)
        (isType_narrow narrows isType)
  | neutralType _ hu le ih =>
      intro Δ narrows formedΓ formedΔ
      rcases ih narrows formedΓ formedΔ with kept | ⟨u, v, e, c, narrowed⟩
      · exact .neutralType kept hu (below_narrow narrows le)
      · exact .neutralType narrowed hu (below_of_narrowed narrows e c le)
  | univ hu e typed _ ih =>
      intro Δ narrows formedΓ formedΔ
      exact .univ hu (typeEq_narrow narrows e) (typed_narrow narrows typed) (ih narrows formedΓ formedΔ)
  | lam e isA typed _ ih =>
      intro Δ narrows formedΓ formedΔ
      exact .lam (typeEq_narrow narrows e) (isType_narrow narrows isA) (typed_narrow narrows typed)
        (ih (narrows.same _) (formedΓ.snoc isA) (formedΔ.snoc (isType_narrow narrows isA)))
  | pair e typed _ _ iha ihb =>
      intro Δ narrows formedΓ formedΔ
      exact .pair (typeEq_narrow narrows e) (typed_narrow narrows typed) (iha narrows formedΓ formedΔ)
        (ihb narrows formedΓ formedΔ)
  | refl e typed _ ih =>
      intro Δ narrows formedΓ formedΔ
      exact .refl (typeEq_narrow narrows e) (typed_narrow narrows typed) (ih narrows formedΓ formedΔ)
  | neutral _ le typed base ih =>
      intro Δ narrows formedΓ formedΔ
      have base' := Base.narrow facts base (Typed.isType typed formedΓ) formedΓ formedΔ narrows
      rcases ih narrows formedΓ formedΔ with kept | ⟨u, v, e, c, narrowed⟩
      · exact .neutral kept (below_narrow narrows le) (typed_narrow narrows typed) base'
      · exact .neutral narrowed (below_of_narrowed narrows e c le) (typed_narrow narrows typed) base'
  | var i e =>
      intro Δ narrows _ formedΔ
      rcases narrows.lookup i with same | ⟨u, v, eΓ, eΔ, c⟩
      · refine .inl (.var i ?_)
        rw [same]
        exact typeEq_narrow narrows e
      · have isV : IsType S.R Δ (.head v) := eΔ ▸ formedΔ.lookup i
        refine .inr ⟨u, v, eΓ ▸ e, c, .var i ?_⟩
        rw [eΔ]
        exact isV.refl
  | const role declared typed e =>
      intro Δ narrows _ _
      exact .inl (.const role declared (typed_narrow narrows typed) (typeEq_narrow narrows e))
  | app _ eF _ eU ihf iha =>
      intro Δ narrows formedΓ formedΔ
      rcases ihf narrows formedΓ formedΔ with kept | ⟨u, v, e, c, narrowed⟩
      · exact .inl (.app kept (typeEq_narrow narrows eF) (iha narrows formedΓ formedΔ) (typeEq_narrow narrows eU))
      · exact absurd (TypeEq.trans S.levels eF.symm e) (TypeEq.pi_ne_head facts formedΓ)
  | fst _ eP eU ih =>
      intro Δ narrows formedΓ formedΔ
      rcases ih narrows formedΓ formedΔ with kept | ⟨u, v, e, c, narrowed⟩
      · exact .inl (.fst kept (typeEq_narrow narrows eP) (typeEq_narrow narrows eU))
      · exact absurd (TypeEq.trans S.levels eP.symm e) (TypeEq.sigma_ne_head facts formedΓ)
  | snd _ eP eU ih =>
      intro Δ narrows formedΓ formedΔ
      rcases ih narrows formedΓ formedΔ with kept | ⟨u, v, e, c, narrowed⟩
      · exact .inl (.snd kept (typeEq_narrow narrows eP) (typeEq_narrow narrows eU))
      · exact absurd (TypeEq.trans S.levels eP.symm e) (TypeEq.sigma_ne_head facts formedΓ)

section Instances

variable (facts : FormFacts S.R S.roles)
include facts

theorem Long.term_narrow {n : Nat} {Γ Δ : Ctx Head n} {v T : Tm Head n} (long : Long S.R S.roles (.term Γ v T))
    (narrows : CtxNarrows S.R Γ Δ) (formedΓ : CtxFormed S.R Γ) (formedΔ : CtxFormed S.R Δ) :
    Long S.R S.roles (.term Δ v T) :=
  Long.narrow facts long narrows formedΓ formedΔ

theorem Long.type_narrow {n : Nat} {Γ Δ : Ctx Head n} {V : Tm Head n} (long : Long S.R S.roles (.type Γ V))
    (narrows : CtxNarrows S.R Γ Δ) (formedΓ : CtxFormed S.R Γ) (formedΔ : CtxFormed S.R Δ) :
    Long S.R S.roles (.type Δ V) :=
  Long.narrow facts long narrows formedΓ formedΔ

/-- **Normal forms are kept by narrowing.** -/
theorem NormalForm.narrow {n : Nat} {Γ Δ : Ctx Head n} {t v A : Tm Head n}
    (normal : NormalForm S.R S.roles Γ t v A) (narrows : CtxNarrows S.R Γ Δ) (formedΓ : CtxFormed S.R Γ)
    (formedΔ : CtxFormed S.R Δ) : NormalForm S.R S.roles Δ t v A :=
  ⟨Long.term_narrow facts normal.1 narrows formedΓ formedΔ, equal_narrow narrows normal.2⟩

end Instances

/-! ## Reflection of equality -/

section Reflection

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (complete : AlgorithmicComplete S.R S.roles)

include facts roots heads algebra complete in
/-- **Narrowing reflects equality, up to heads**: the normal forms in `Γ` of two terms equal in a narrowing `Δ`
agree up to heads. -/
theorem same_of_narrows {n : Nat} {Γ Δ : Ctx Head n} (narrows : CtxNarrows S.R Γ Δ) (formedΓ : CtxFormed S.R Γ)
    (formedΔ : CtxFormed S.R Δ) {s t v w A : Tm Head n} (first : NormalForm S.R S.roles Γ s v A)
    (second : NormalForm S.R S.roles Γ t w A) (equal : Equal S.R Δ s t A) : SameUpToHeads S.R v w :=
  normalForms_same_of_equal facts roots heads algebra complete formedΔ equal
    (NormalForm.narrow facts first narrows formedΓ formedΔ) (NormalForm.narrow facts second narrows formedΓ formedΔ)

end Reflection

end ContextualDependentCumulative
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
