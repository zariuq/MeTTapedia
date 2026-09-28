import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.StrongNormalization.Candidates
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.RecursionComputation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.ConstantExpansion

/-!
# Theorems published by name

A theorem published by name is a closed definition `name : T := body` added to a
package (`Rules.withTheorem`): the constant is declared at `T`, and its δ-rule
`name ⟶ body` is a root computation.

* **Typing** (`withTheorem_typed`): when `name` is fresh, `T` is a type at a
  universe and `body : T`, the constant is a term of `T` in the extended
  package, and it is equal to its body there (`withTheorem_equal_body`). The
  extended package contains the original one (`withTheorem_sub`).
  Without the formation of `T` the typing and the equation fail: a package with
  an inhabited type that is formed at no universe is a counterexample
  (`withTheorem_typed_needs_formation`, `withTheorem_equal_body_needs_formation`);
  the declaration rule of the judgment requires the declared type to be formed.
* **Unfolding** (`Derivable.unfoldTheorem`): when `name` occurs neither in `T`,
  in `body`, nor in the declared types of the package, and the package's root
  computation is stable under replacing `name` by `body`, every derivation of
  the extended package unfolds, by that replacement, to a derivation of the
  original package.
* **Strong normalization** (`SN.of_unfoldTheorem`): a term whose unfolding is
  strongly normalizing in the original package is strongly normalizing in the
  extended package. A δ-step leaves the unfolding unchanged and removes one
  occurrence of `name`; every other step of the extended package is a step of
  the unfolding.
* **Carrying the metatheory over**: an undeclared name occurs in no typed term
  (`Derivable.avoids`), so for a fresh name, a formed statement and a typed
  body, strong normalization of the package carries over to the extension
  (`withTheorem_sn`), and so does the emptiness of a closed type without the
  name (`withTheorem_uninhabited`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality

open Normalization StrongNormalization
open ConstantExpansion (expand constantNames constantNames_liftClosed)

variable {Head : Type}

/-! ## The package with a published theorem -/

/-- The δ-rule of a closed definition: the constant steps to its body. -/
def deltaComputation (name : DeclName) (body : Tm Head 0) : RootComputation Head where
  step := fun l r => l = .const name ∧ r = liftClosed body
  rename := by
    rintro n m ρ l r ⟨rfl, rfl⟩
    exact ⟨rfl, rename_liftClosed ρ body⟩
  substitute := by
    rintro n m σ l r ⟨rfl, rfl⟩
    exact ⟨rfl, subst_liftClosed σ body⟩

/-- The package with the theorem `name : T := body` published by name. -/
def _root_.Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Rules.withTheorem
    (R : Rules Head) (name : DeclName) (T body : Tm Head 0) : Rules Head :=
  { R with
    constantType := fun c => if c = name then some T else R.constantType c
    computation := RootComputation.union R.computation (deltaComputation name body) }

section Published

variable {R : Rules Head} {name : DeclName} {T body : Tm Head 0}

theorem withTheorem_constantType_self : (R.withTheorem name T body).constantType name = some T := by
  simp [Rules.withTheorem]

theorem withTheorem_constantType_of_ne {c : DeclName} (distinct : c ≠ name) :
    (R.withTheorem name T body).constantType c = R.constantType c := by
  simp [Rules.withTheorem, distinct]

/-- The δ-step of a published theorem. -/
theorem withTheorem_delta {n : Nat} :
    (R.withTheorem name T body).computation.step (.const name : Tm Head n) (liftClosed body) :=
  .inr ⟨rfl, rfl⟩

/-- A package is contained in its extension by a fresh theorem. -/
theorem withTheorem_sub (fresh : R.constantType name = none) :
    RulesSub R (R.withTheorem name T body) where
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  constantType := by
    intro c A declared
    by_cases same : c = name
    · subst same
      rw [fresh] at declared
      cases declared
    · rw [withTheorem_constantType_of_ne same]
      exact declared
  computation := fun step => .inl step

/-- A package is contained in its extension by a theorem that keeps the declared
type of its name. -/
theorem withTheorem_sub_of_declared (declared : R.constantType name = some T) :
    RulesSub R (R.withTheorem name T body) where
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  constantType := by
    intro c A declaredC
    by_cases same : c = name
    · subst same
      rw [withTheorem_constantType_self]
      rw [declared] at declaredC
      exact declaredC
    · rw [withTheorem_constantType_of_ne same]
      exact declaredC
  computation := fun step => .inl step

/-- **Typing of a published theorem**, in every context. -/
theorem withTheorem_typed_in (fresh : R.constantType name = none) (formed : IsType R .nil T)
    {n : Nat} (Γ : Ctx Head n) :
    Typed (R.withTheorem name T body) Γ (.const name) (liftClosed T) := by
  obtain ⟨u, hu, typedT⟩ := formed
  exact .const withTheorem_constantType_self (Normalization.Derivable.mono (withTheorem_sub fresh) typedT) hu

/-- **Typing of a published theorem.** The name of a fresh theorem whose
statement is a type is a closed term of its statement. -/
theorem withTheorem_typed (fresh : R.constantType name = none) (formed : IsType R .nil T) :
    Typed (R.withTheorem name T body) .nil (.const name) T := by
  have h := withTheorem_typed_in (body := body) fresh formed .nil
  rwa [TelescopeAbstraction.liftClosed_zero] at h

/-- **A published theorem is equal to its body.** -/
theorem withTheorem_equal_body (fresh : R.constantType name = none) (formed : IsType R .nil T)
    (typed : Typed R .nil body T) :
    Equal (R.withTheorem name T body) .nil (.const name) body T := by
  have step : (R.withTheorem name T body).computation.step (.const name : Tm Head 0) body := by
    have h := withTheorem_delta (R := R) (name := name) (T := T) (body := body) (n := 0)
    rwa [TelescopeAbstraction.liftClosed_zero] at h
  exact .root step (withTheorem_typed fresh formed) (Normalization.Derivable.mono (withTheorem_sub fresh) typed)

end Published

/-! ## An undeclared name occurs in no typed term -/

/-- **An undeclared name occurs in no typed term**: the declaration rule is the
only rule that introduces a constant. -/
theorem Derivable.avoids {R : Rules Head} {name : DeclName} (fresh : R.constantType name = none)
    {st : Statement Head} (derivation : Derivable R st) :
    match st with
    | .typing _ t _ => name ∉ constantNames t
    | _ => True := by
  induction derivation with
  | headType _ => exact List.not_mem_nil
  | var _ => exact List.not_mem_nil
  | const declared _ _ _ =>
      intro mem
      rw [constantNames, List.mem_singleton] at mem
      subst mem
      rw [fresh] at declared
      cases declared
  | piForm _ _ _ _ _ ihA ihB => exact List.not_mem_append ihA ihB
  | sigmaForm _ _ _ _ _ ihA ihB => exact List.not_mem_append ihA ihB
  | lamIntro _ _ _ _ ihBody => exact ihBody
  | appElim _ _ ihF ihA => exact List.not_mem_append ihF ihA
  | pairIntro _ _ _ _ _ ihA ihB => exact List.not_mem_append ihA ihB
  | fstElim _ ih => exact ih
  | sndElim _ ih => exact ih
  | idForm _ _ _ _ ihA iha ihb => exact List.not_mem_append (List.not_mem_append ihA iha) ihb
  | reflIntro _ ih => exact ih
  | sub _ _ ih _ => exact ih
  | conv _ _ _ ih _ => exact ih
  | _ => trivial

theorem Typed.avoids {R : Rules Head} {name : DeclName} (fresh : R.constantType name = none)
    {n : Nat} {Γ : Ctx Head n} {t A : Tm Head n} (typed : Typed R Γ t A) :
    name ∉ constantNames t :=
  Derivable.avoids fresh typed

/-! ## The formation of the statement is needed -/

/-- A package in which one head inhabits itself and no head is a universe: the
type `h` is inhabited but formed at no universe. -/
def unformedRules (h : Head) : Rules Head where
  headTyping := fun a b => a = h ∧ b = h
  isUniverse := fun _ => False
  join := fun _ _ _ => False
  cumulative := fun _ _ => False
  headEq := fun _ _ => False

/-- In a package without universes no constant is ever typed, and no side of a
derivable equality is a constant. -/
theorem unformed_no_const {R : Rules Head} (noUniverse : ∀ u, ¬ R.isUniverse u)
    {st : Statement Head} (derivation : Derivable R st) :
    match st with
    | .typing _ t _ => ∀ c, t ≠ .const c
    | .equality _ a b _ => (∀ c, a ≠ .const c) ∧ ∀ c, b ≠ .const c
    | _ => True := by
  induction derivation with
  | const _ _ hu => exact absurd hu (noUniverse _)
  | piForm _ hu => exact absurd hu (noUniverse _)
  | sigmaForm _ hu => exact absurd hu (noUniverse _)
  | lamIntro _ hu => exact absurd hu (noUniverse _)
  | pairIntro _ hu => exact absurd hu (noUniverse _)
  | idForm _ hu => exact absurd hu (noUniverse _)
  | conv _ _ hu => exact absurd hu (noUniverse _)
  | sub _ _ ih _ => exact ih
  | headType => intro c h; cases h
  | var => intro c h; cases h
  | appElim => intro c h; cases h
  | fstElim => intro c h; cases h
  | sndElim => intro c h; cases h
  | reflIntro => intro c h; cases h
  | refl _ ih => exact ⟨ih, ih⟩
  | symm _ ih => exact ⟨ih.2, ih.1⟩
  | trans _ _ ih₁ ih₂ => exact ⟨ih₁.1, ih₂.2⟩
  | convEq _ _ hu => exact absurd hu (noUniverse _)
  | subEq _ _ ih _ => exact ih
  | headEq => exact ⟨fun _ => nofun, fun _ => nofun⟩
  | piCong _ hu => exact absurd hu (noUniverse _)
  | sigmaCong _ hu => exact absurd hu (noUniverse _)
  | idCong _ hu => exact absurd hu (noUniverse _)
  | lamCong _ hu => exact absurd hu (noUniverse _)
  | appCong => exact ⟨fun _ => nofun, fun _ => nofun⟩
  | pairCong _ hu => exact absurd hu (noUniverse _)
  | fstCong => exact ⟨fun _ => nofun, fun _ => nofun⟩
  | sndCong => exact ⟨fun _ => nofun, fun _ => nofun⟩
  | reflCong => exact ⟨fun _ => nofun, fun _ => nofun⟩
  | betaPi _ hu => exact absurd hu (noUniverse _)
  | betaFst _ hu => exact absurd hu (noUniverse _)
  | betaSnd _ hu => exact absurd hu (noUniverse _)
  | root _ _ _ ihL ihR => exact ⟨ihL, ihR⟩
  | etaPi _ _ _ ihF ihG _ => exact ⟨ihF, ihG⟩
  | etaSigma _ _ _ _ ihP ihQ _ _ => exact ⟨ihP, ihQ⟩
  | _ => trivial

/-- **The design's typing law without formation is false.** Over any heads, in a
package with an inhabited type formed at no universe, a fresh theorem proved at
that type is not a term of it. The law holds with the formation premise
(`withTheorem_typed`). -/
theorem withTheorem_typed_needs_formation (h : Head) :
    ∃ (R : Rules Head) (name : DeclName) (T body : Tm Head 0),
      R.constantType name = none ∧ Typed R .nil body T ∧
        ¬ Typed (R.withTheorem name T body) .nil (.const name) T := by
  refine ⟨unformedRules h, .anonymous, .head h, .head h, rfl, .headType ⟨rfl, rfl⟩, fun typed => ?_⟩
  exact unformed_no_const (R := (unformedRules h).withTheorem .anonymous _ _)
    (fun _ impossible => impossible) typed .anonymous rfl

/-- **The design's equation law without formation is false**, in the same
package: the published name is not equal to its body there. The law holds with
the formation premise (`withTheorem_equal_body`). -/
theorem withTheorem_equal_body_needs_formation (h : Head) :
    ∃ (R : Rules Head) (name : DeclName) (T body : Tm Head 0),
      R.constantType name = none ∧ Typed R .nil body T ∧
        ¬ Equal (R.withTheorem name T body) .nil (.const name) body T := by
  refine ⟨unformedRules h, .anonymous, .head h, .head h, rfl, .headType ⟨rfl, rfl⟩, fun equal => ?_⟩
  exact (unformed_no_const (R := (unformedRules h).withTheorem .anonymous _ _)
    (fun _ impossible => impossible) equal).1 .anonymous rfl

/-! ## Unfolding a published theorem -/

section Unfolding

variable (name : DeclName) (body : Tm Head 0)

/-- The bodies that replace the published constant by its body. -/
def unfoldBodies : ConstantExpansion.Bodies Head := fun c => if c = name then body else .const c

/-- The unfolding of a term: the published constant replaced by its body. -/
def unfoldTm {n : Nat} (t : Tm Head n) : Tm Head n := expand (unfoldBodies name body) t

/-- The unfolding of a context. -/
def Ctx.unfold : {n : Nat} → Ctx Head n → Ctx Head n
  | _, .nil => .nil
  | _, .snoc Γ A => .snoc (Ctx.unfold Γ) (unfoldTm name body A)

/-- The unfolding of a statement. -/
def Statement.unfold : Statement Head → Statement Head
  | .typing Γ t A => .typing (Ctx.unfold name body Γ) (unfoldTm name body t) (unfoldTm name body A)
  | .equality Γ a b A =>
      .equality (Ctx.unfold name body Γ) (unfoldTm name body a) (unfoldTm name body b)
        (unfoldTm name body A)
  | .sub Γ A B => .sub (Ctx.unfold name body Γ) (unfoldTm name body A) (unfoldTm name body B)

variable {name body}

section Equations

variable {n : Nat}

@[simp] theorem unfoldTm_var (i : Fin n) : unfoldTm name body (.var i : Tm Head n) = .var i := rfl
@[simp] theorem unfoldTm_head (h : Head) : unfoldTm name body (.head h : Tm Head n) = .head h := rfl
@[simp] theorem unfoldTm_pi (A : Tm Head n) (B : Tm Head (n + 1)) :
    unfoldTm name body (.pi A B) = .pi (unfoldTm name body A) (unfoldTm name body B) := rfl
@[simp] theorem unfoldTm_sigma (A : Tm Head n) (B : Tm Head (n + 1)) :
    unfoldTm name body (.sigma A B) = .sigma (unfoldTm name body A) (unfoldTm name body B) := rfl
@[simp] theorem unfoldTm_id (A a b : Tm Head n) :
    unfoldTm name body (.id A a b) = .id (unfoldTm name body A) (unfoldTm name body a)
      (unfoldTm name body b) := rfl
@[simp] theorem unfoldTm_lam (b : Tm Head (n + 1)) :
    unfoldTm name body (.lam b) = .lam (unfoldTm name body b) := rfl
@[simp] theorem unfoldTm_app (f a : Tm Head n) :
    unfoldTm name body (.app f a) = .app (unfoldTm name body f) (unfoldTm name body a) := rfl
@[simp] theorem unfoldTm_pair (a b : Tm Head n) :
    unfoldTm name body (.pair a b) = .pair (unfoldTm name body a) (unfoldTm name body b) := rfl
@[simp] theorem unfoldTm_fst (p : Tm Head n) :
    unfoldTm name body (.fst p) = .fst (unfoldTm name body p) := rfl
@[simp] theorem unfoldTm_snd (p : Tm Head n) :
    unfoldTm name body (.snd p) = .snd (unfoldTm name body p) := rfl
@[simp] theorem unfoldTm_refl (a : Tm Head n) :
    unfoldTm name body (.refl a) = .refl (unfoldTm name body a) := rfl

@[simp] theorem unfoldTm_rename {m : Nat} (ρ : Ren n m) (t : Tm Head n) :
    unfoldTm name body (Presentation.rename ρ t) = Presentation.rename ρ (unfoldTm name body t) :=
  ConstantExpansion.expand_rename _ ρ t

@[simp] theorem unfoldTm_liftClosed (t : Tm Head 0) :
    unfoldTm name body (liftClosed t : Tm Head n) = liftClosed (unfoldTm name body t) :=
  ConstantExpansion.expand_liftClosed _ t

@[simp] theorem unfoldTm_inst0 (a : Tm Head n) (b : Tm Head (n + 1)) :
    unfoldTm name body (inst0 a b) = inst0 (unfoldTm name body a) (unfoldTm name body b) :=
  ConstantExpansion.expand_inst0 _ a b

theorem unfoldTm_const_self : unfoldTm name body (.const name : Tm Head n) = liftClosed body := by
  simp [unfoldTm, unfoldBodies, expand]

theorem unfoldTm_const_of_ne {c : DeclName} (distinct : c ≠ name) :
    unfoldTm name body (.const c : Tm Head n) = .const c := by
  simp only [unfoldTm, expand, unfoldBodies, if_neg distinct]
  rfl

/-- A term in which the published name does not occur is its own unfolding. -/
theorem unfoldTm_eq_self {t : Tm Head n} (absent : name ∉ constantNames t) :
    unfoldTm name body t = t := by
  rw [unfoldTm, ConstantExpansion.expand_eq_of_agreement (unfoldBodies name body) (fun c => .const c) t
    fun c mem => by
      have distinct : c ≠ name := fun same => absent (same ▸ mem)
      simp [unfoldBodies, distinct]]
  exact ConstantExpansion.expand_identity t

end Equations

theorem Ctx.lookup_unfold : ∀ {n : Nat} (Γ : Ctx Head n) (i : Fin n),
    Ctx.lookup (Ctx.unfold name body Γ) i = unfoldTm name body (Ctx.lookup Γ i)
  | _, .nil, i => Fin.elim0 i
  | _, .snoc Γ A, i => by
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Ctx.unfold, Ctx.lookup_snoc_zero, unfoldTm_rename]
      · simp only [Ctx.unfold, Ctx.lookup_snoc_succ, Ctx.lookup_unfold Γ j, unfoldTm_rename]

/-- **Unfolding.** When the published name occurs neither in the statement, in
the body, nor in the declared types of the package, and the root computation
of the package is stable under unfolding, every derivation of the extended
package unfolds to a derivation of the package. -/
theorem Derivable.unfoldTheorem {R : Rules Head} {T : Tm Head 0}
    (typed : Typed R .nil body T) (bodyFree : name ∉ constantNames body)
    (typeFree : name ∉ constantNames T)
    (declaredFree : ∀ {c : DeclName} {A : Tm Head 0}, R.constantType c = some A →
      name ∉ constantNames A)
    (stable : ∀ {n : Nat} {l r : Tm Head n}, R.computation.step l r →
      R.computation.step (unfoldTm name body l) (unfoldTm name body r))
    {st : Statement Head} (derivation : Derivable (R.withTheorem name T body) st) :
    Derivable R (st.unfold name body) := by
  induction derivation with
  | headType typing => exact .headType typing
  | @var n Γ i =>
      simp only [Statement.unfold]
      rw [← Ctx.lookup_unfold]
      exact .var i
  | @const n Γ c A u declared _ hu ihType =>
      simp only [Statement.unfold, unfoldTm_liftClosed]
      by_cases same : c = name
      · subst same
        rw [withTheorem_constantType_self, Option.some.injEq] at declared
        subst declared
        rw [unfoldTm_const_self, unfoldTm_eq_self typeFree]
        exact typed.rename (fun i => Fin.elim0 i)
      · rw [withTheorem_constantType_of_ne same] at declared
        rw [unfoldTm_const_of_ne same, unfoldTm_eq_self (declaredFree declared)]
        simp only [Statement.unfold, Ctx.unfold, unfoldTm_head,
          unfoldTm_eq_self (declaredFree declared)] at ihType
        exact .const declared ihType hu
  | piForm _ hu _ hv join ihA ihB =>
      simp only [Statement.unfold, Ctx.unfold, unfoldTm_pi, unfoldTm_head] at ihA ihB ⊢
      exact .piForm ihA hu ihB hv join
  | sigmaForm _ hu _ hv join ihA ihB =>
      simp only [Statement.unfold, Ctx.unfold, unfoldTm_sigma, unfoldTm_head] at ihA ihB ⊢
      exact .sigmaForm ihA hu ihB hv join
  | lamIntro _ hu _ ihPi ihBody =>
      simp only [Statement.unfold, Ctx.unfold, unfoldTm_pi, unfoldTm_lam, unfoldTm_head] at ihPi ihBody ⊢
      exact .lamIntro ihPi hu ihBody
  | appElim _ _ ihF ihA =>
      simp only [Statement.unfold, unfoldTm_pi, unfoldTm_app, unfoldTm_inst0] at ihF ihA ⊢
      exact .appElim ihF ihA
  | pairIntro _ hu _ _ ihS ihA ihB =>
      simp only [Statement.unfold, unfoldTm_sigma, unfoldTm_pair, unfoldTm_head,
        unfoldTm_inst0] at ihS ihA ihB ⊢
      exact .pairIntro ihS hu ihA ihB
  | fstElim _ ih =>
      simp only [Statement.unfold, unfoldTm_sigma, unfoldTm_fst] at ih ⊢
      exact .fstElim ih
  | sndElim _ ih =>
      simp only [Statement.unfold, unfoldTm_sigma, unfoldTm_snd, unfoldTm_fst, unfoldTm_inst0] at ih ⊢
      exact .sndElim ih
  | idForm _ hu _ _ ihA iha ihb =>
      simp only [Statement.unfold, unfoldTm_id, unfoldTm_head] at ihA iha ihb ⊢
      exact .idForm ihA hu iha ihb
  | reflIntro _ ih =>
      simp only [Statement.unfold, unfoldTm_id, unfoldTm_refl] at ih ⊢
      exact .reflIntro ih
  | sub _ _ ihT ihLe =>
      simp only [Statement.unfold] at ihT ihLe ⊢
      exact .sub ihT ihLe
  | conv _ _ hu ihT ihE =>
      simp only [Statement.unfold, unfoldTm_head] at ihT ihE ⊢
      exact .conv ihT ihE hu
  | refl _ ih =>
      simp only [Statement.unfold] at ih ⊢
      exact .refl ih
  | symm _ ih =>
      simp only [Statement.unfold] at ih ⊢
      exact .symm ih
  | trans _ _ ih₁ ih₂ =>
      simp only [Statement.unfold] at ih₁ ih₂ ⊢
      exact .trans ih₁ ih₂
  | convEq _ _ hu ih ihT =>
      simp only [Statement.unfold, unfoldTm_head] at ih ihT ⊢
      exact .convEq ih ihT hu
  | subEq _ _ ihE ihLe =>
      simp only [Statement.unfold] at ihE ihLe ⊢
      exact .subEq ihE ihLe
  | headEq same _ _ ih ih' =>
      simp only [Statement.unfold, unfoldTm_head] at ih ih' ⊢
      exact .headEq same ih ih'
  | piCong _ hu _ hv join ihA ihB =>
      simp only [Statement.unfold, Ctx.unfold, unfoldTm_pi, unfoldTm_head] at ihA ihB ⊢
      exact .piCong ihA hu ihB hv join
  | sigmaCong _ hu _ hv join ihA ihB =>
      simp only [Statement.unfold, Ctx.unfold, unfoldTm_sigma, unfoldTm_head] at ihA ihB ⊢
      exact .sigmaCong ihA hu ihB hv join
  | idCong _ hu _ _ ihA iha ihb =>
      simp only [Statement.unfold, unfoldTm_id, unfoldTm_head] at ihA iha ihb ⊢
      exact .idCong ihA hu iha ihb
  | lamCong _ hu _ ihPi ihBody =>
      simp only [Statement.unfold, Ctx.unfold, unfoldTm_pi, unfoldTm_lam, unfoldTm_head] at ihPi ihBody ⊢
      exact .lamCong ihPi hu ihBody
  | appCong _ _ ihF ihA =>
      simp only [Statement.unfold, unfoldTm_pi, unfoldTm_app, unfoldTm_inst0] at ihF ihA ⊢
      exact .appCong ihF ihA
  | pairCong _ hu _ _ ihS ihA ihB =>
      simp only [Statement.unfold, unfoldTm_sigma, unfoldTm_pair, unfoldTm_head,
        unfoldTm_inst0] at ihS ihA ihB ⊢
      exact .pairCong ihS hu ihA ihB
  | fstCong _ ih =>
      simp only [Statement.unfold, unfoldTm_sigma, unfoldTm_fst] at ih ⊢
      exact .fstCong ih
  | sndCong _ ih =>
      simp only [Statement.unfold, unfoldTm_sigma, unfoldTm_snd, unfoldTm_fst, unfoldTm_inst0] at ih ⊢
      exact .sndCong ih
  | reflCong _ ih =>
      simp only [Statement.unfold, unfoldTm_id, unfoldTm_refl] at ih ⊢
      exact .reflCong ih
  | betaPi _ hu _ _ ihPi ihBody ihA =>
      simp only [Statement.unfold, Ctx.unfold, unfoldTm_pi, unfoldTm_app, unfoldTm_lam, unfoldTm_head,
        unfoldTm_inst0] at ihPi ihBody ihA ⊢
      exact .betaPi ihPi hu ihBody ihA
  | betaFst _ hu _ _ ihS ihA ihB =>
      simp only [Statement.unfold, unfoldTm_sigma, unfoldTm_fst, unfoldTm_pair, unfoldTm_head,
        unfoldTm_inst0] at ihS ihA ihB ⊢
      exact .betaFst ihS hu ihA ihB
  | betaSnd _ hu _ _ ihS ihA ihB =>
      simp only [Statement.unfold, unfoldTm_sigma, unfoldTm_snd, unfoldTm_pair, unfoldTm_head,
        unfoldTm_inst0] at ihS ihA ihB ⊢
      exact .betaSnd ihS hu ihA ihB
  | root step _ _ ihL ihR =>
      simp only [Statement.unfold] at ihL ihR ⊢
      rcases step with step | ⟨rfl, rfl⟩
      · exact .root (stable step) ihL ihR
      · rw [unfoldTm_liftClosed, unfoldTm_eq_self bodyFree] at ihR ⊢
        rw [unfoldTm_const_self]
        exact .refl ihR
  | etaPi _ _ _ ihF ihG ihApps =>
      simp only [Statement.unfold, Ctx.unfold, unfoldTm_pi, unfoldTm_app, unfoldTm_var,
        unfoldTm_rename] at ihF ihG ihApps ⊢
      exact .etaPi ihF ihG ihApps
  | etaSigma _ _ _ _ ihP ihQ ihFst ihSnd =>
      simp only [Statement.unfold, unfoldTm_sigma, unfoldTm_fst, unfoldTm_snd,
        unfoldTm_inst0] at ihP ihQ ihFst ihSnd ⊢
      exact .etaSigma ihP ihQ ihFst ihSnd
  | subEqual _ hu ih =>
      simp only [Statement.unfold, unfoldTm_head] at ih ⊢
      exact .subEqual ih hu
  | subUniv c => exact .subUniv c
  | subPi _ hu _ hu' _ hw _ ihPi ihPi' ihA ihB =>
      simp only [Statement.unfold, Ctx.unfold, unfoldTm_pi, unfoldTm_head] at ihPi ihPi' ihA ihB ⊢
      exact .subPi ihPi hu ihPi' hu' ihA hw ihB
  | subSigma _ hu _ hu' _ _ ihS ihS' ihA ihB =>
      simp only [Statement.unfold, Ctx.unfold, unfoldTm_sigma, unfoldTm_head] at ihS ihS' ihA ihB ⊢
      exact .subSigma ihS hu ihS' hu' ihA ihB
  | subTrans _ _ ih₁ ih₂ =>
      simp only [Statement.unfold] at ih₁ ih₂ ⊢
      exact .subTrans ih₁ ih₂

/-- The unfolding of a formed context of the extended package is formed. -/
theorem CtxFormed.unfoldTheorem {R : Rules Head} {T : Tm Head 0}
    (typed : Typed R .nil body T) (bodyFree : name ∉ constantNames body)
    (typeFree : name ∉ constantNames T)
    (declaredFree : ∀ {c : DeclName} {A : Tm Head 0}, R.constantType c = some A →
      name ∉ constantNames A)
    (stable : ∀ {n : Nat} {l r : Tm Head n}, R.computation.step l r →
      R.computation.step (unfoldTm name body l) (unfoldTm name body r))
    {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed (R.withTheorem name T body) Γ) :
    CtxFormed R (Ctx.unfold name body Γ) := by
  induction formed with
  | nil => exact .nil
  | snoc _ isType ih =>
      obtain ⟨u, hu, typedA⟩ := isType
      exact .snoc ih ⟨u, hu, Derivable.unfoldTheorem typed bodyFree typeFree declaredFree stable typedA⟩

/-! ## Strong normalization -/

/-- The number of occurrences of the published name. -/
abbrev occurrences {n : Nat} (t : Tm Head n) : Nat := (constantNames t).count name

/-- A step of the extended package is a step of the unfolding, or a δ-step that
leaves the unfolding unchanged and removes one occurrence of the name. -/
theorem StrongNormalization.Reduces.unfoldTheorem {R : Rules Head} {T : Tm Head 0}
    (bodyFree : name ∉ constantNames body)
    (stable : ∀ {n : Nat} {l r : Tm Head n}, R.computation.step l r →
      R.computation.step (unfoldTm name body l) (unfoldTm name body r))
    {n : Nat} {t u : Tm Head n} (step : StrongNormalization.Reduces (R.withTheorem name T body) t u) :
    StrongNormalization.Reduces R (unfoldTm name body t) (unfoldTm name body u) ∨
      (unfoldTm name body t = unfoldTm name body u ∧ occurrences (name := name) u < occurrences (name := name) t) := by
  induction step with
  | betaPi b a =>
      left
      simp only [unfoldTm_app, unfoldTm_lam, unfoldTm_inst0]
      exact .betaPi _ _
  | betaSigmaFst a b => left; exact .betaSigmaFst _ _
  | betaSigmaSnd a b => left; exact .betaSigmaSnd _ _
  | head equality => exact equality.elim
  | root step =>
      rcases step with step | ⟨rfl, rfl⟩
      · exact .inl (.root (stable step))
      · right
        refine ⟨?_, ?_⟩
        · rw [unfoldTm_const_self, unfoldTm_liftClosed, unfoldTm_eq_self bodyFree]
        · simp only [occurrences, constantNames_liftClosed, constantNames, List.count_singleton_self,
            List.count_eq_zero_of_not_mem bodyFree]
          exact Nat.zero_lt_one
  | congPiDom _ ih =>
      rcases ih with h | ⟨same, fewer⟩
      · exact .inl (.congPiDom h)
      · refine .inr ⟨by simp only [unfoldTm_pi, same], ?_⟩
        simp only [occurrences, constantNames, List.count_append] at fewer ⊢
        omega
  | congPiCod _ ih =>
      rcases ih with h | ⟨same, fewer⟩
      · exact .inl (.congPiCod h)
      · refine .inr ⟨by simp only [unfoldTm_pi, same], ?_⟩
        simp only [occurrences, constantNames, List.count_append] at fewer ⊢
        omega
  | congSigmaDom _ ih =>
      rcases ih with h | ⟨same, fewer⟩
      · exact .inl (.congSigmaDom h)
      · refine .inr ⟨by simp only [unfoldTm_sigma, same], ?_⟩
        simp only [occurrences, constantNames, List.count_append] at fewer ⊢
        omega
  | congSigmaCod _ ih =>
      rcases ih with h | ⟨same, fewer⟩
      · exact .inl (.congSigmaCod h)
      · refine .inr ⟨by simp only [unfoldTm_sigma, same], ?_⟩
        simp only [occurrences, constantNames, List.count_append] at fewer ⊢
        omega
  | congIdTy _ ih =>
      rcases ih with h | ⟨same, fewer⟩
      · exact .inl (.congIdTy h)
      · refine .inr ⟨by simp only [unfoldTm_id, same], ?_⟩
        simp only [occurrences, constantNames, List.count_append] at fewer ⊢
        omega
  | congIdLeft _ ih =>
      rcases ih with h | ⟨same, fewer⟩
      · exact .inl (.congIdLeft h)
      · refine .inr ⟨by simp only [unfoldTm_id, same], ?_⟩
        simp only [occurrences, constantNames, List.count_append] at fewer ⊢
        omega
  | congIdRight _ ih =>
      rcases ih with h | ⟨same, fewer⟩
      · exact .inl (.congIdRight h)
      · refine .inr ⟨by simp only [unfoldTm_id, same], ?_⟩
        simp only [occurrences, constantNames, List.count_append] at fewer ⊢
        omega
  | congLam _ ih =>
      rcases ih with h | ⟨same, fewer⟩
      · exact .inl (.congLam h)
      · refine .inr ⟨by simp only [unfoldTm_lam, same], ?_⟩
        simpa only [occurrences, constantNames] using fewer
  | congAppFun _ ih =>
      rcases ih with h | ⟨same, fewer⟩
      · exact .inl (.congAppFun h)
      · refine .inr ⟨by simp only [unfoldTm_app, same], ?_⟩
        simp only [occurrences, constantNames, List.count_append] at fewer ⊢
        omega
  | congAppArg _ ih =>
      rcases ih with h | ⟨same, fewer⟩
      · exact .inl (.congAppArg h)
      · refine .inr ⟨by simp only [unfoldTm_app, same], ?_⟩
        simp only [occurrences, constantNames, List.count_append] at fewer ⊢
        omega
  | congPairFst _ ih =>
      rcases ih with h | ⟨same, fewer⟩
      · exact .inl (.congPairFst h)
      · refine .inr ⟨by simp only [unfoldTm_pair, same], ?_⟩
        simp only [occurrences, constantNames, List.count_append] at fewer ⊢
        omega
  | congPairSnd _ ih =>
      rcases ih with h | ⟨same, fewer⟩
      · exact .inl (.congPairSnd h)
      · refine .inr ⟨by simp only [unfoldTm_pair, same], ?_⟩
        simp only [occurrences, constantNames, List.count_append] at fewer ⊢
        omega
  | congFst _ ih =>
      rcases ih with h | ⟨same, fewer⟩
      · exact .inl (.congFst h)
      · refine .inr ⟨by simp only [unfoldTm_fst, same], ?_⟩
        simpa only [occurrences, constantNames] using fewer
  | congSnd _ ih =>
      rcases ih with h | ⟨same, fewer⟩
      · exact .inl (.congSnd h)
      · refine .inr ⟨by simp only [unfoldTm_snd, same], ?_⟩
        simpa only [occurrences, constantNames] using fewer
  | congRefl _ ih =>
      rcases ih with h | ⟨same, fewer⟩
      · exact .inl (.congRefl h)
      · refine .inr ⟨by simp only [unfoldTm_refl, same], ?_⟩
        simpa only [occurrences, constantNames] using fewer

/-- **Strong normalization through unfolding.** A term whose unfolding is
strongly normalizing in the package is strongly normalizing in the package
extended by the published theorem. -/
theorem StrongNormalization.SN.of_unfoldTheorem {R : Rules Head} {T : Tm Head 0}
    (bodyFree : name ∉ constantNames body)
    (stable : ∀ {n : Nat} {l r : Tm Head n}, R.computation.step l r →
      R.computation.step (unfoldTm name body l) (unfoldTm name body r))
    {n : Nat} {t : Tm Head n} (sn : SN R (unfoldTm name body t)) :
    SN (R.withTheorem name T body) t := by
  suffices key : ∀ s : Tm Head n, SN R s → ∀ (k : Nat) (t : Tm Head n),
      occurrences (name := name) t ≤ k → unfoldTm name body t = s → SN (R.withTheorem name T body) t from
    key _ sn _ t (Nat.le_refl _) rfl
  intro s hs
  induction hs with
  | intro s _ ihAcc =>
      intro k
      induction k using Nat.strongRecOn with
      | _ k ihCount =>
          intro t hk ht
          refine SN.intro fun u step => ?_
          rcases StrongNormalization.Reduces.unfoldTheorem bodyFree stable step with reduces | ⟨same, fewer⟩
          · exact ihAcc _ (ht ▸ reduces) _ u (Nat.le_refl _) rfl
          · exact ihCount (occurrences (name := name) u) (by omega) u (Nat.le_refl _) (same ▸ ht)

/-! ## The metatheory of the package carries over -/

/-- **Strong normalization carries over.** When the package normalizes every
term typed in a formed context, so does its extension by a fresh theorem whose
statement is a type and whose body is typed, provided the declared types of the
package avoid the name and its computation is stable under unfolding. -/
theorem withTheorem_sn {R : Rules Head} {T : Tm Head 0}
    (sn : ∀ {n : Nat} {Γ : Ctx Head n} {t A : Tm Head n}, CtxFormed R Γ → Typed R Γ t A →
      SN R t ∧ SN R A)
    (fresh : R.constantType name = none) (formed : IsType R .nil T) (typed : Typed R .nil body T)
    (declaredFree : ∀ {c : DeclName} {A : Tm Head 0}, R.constantType c = some A →
      name ∉ constantNames A)
    (stable : ∀ {n : Nat} {l r : Tm Head n}, R.computation.step l r →
      R.computation.step (unfoldTm name body l) (unfoldTm name body r))
    {n : Nat} {Γ : Ctx Head n} {t A : Tm Head n} (formedΓ : CtxFormed (R.withTheorem name T body) Γ)
    (typedT : Typed (R.withTheorem name T body) Γ t A) :
    SN (R.withTheorem name T body) t ∧ SN (R.withTheorem name T body) A := by
  have bodyFree := typed.avoids fresh
  obtain ⟨_, _, typedType⟩ := formed
  have typeFree := typedType.avoids fresh
  obtain ⟨snT, snA⟩ := sn (CtxFormed.unfoldTheorem typed bodyFree typeFree declaredFree stable formedΓ)
    (Derivable.unfoldTheorem typed bodyFree typeFree declaredFree stable typedT)
  exact ⟨SN.of_unfoldTheorem bodyFree stable snT, SN.of_unfoldTheorem bodyFree stable snA⟩

/-- **Uninhabited closed types stay uninhabited.** A closed type of the package
that has no closed term, and in which the name does not occur, has no closed
term in the extension by a fresh theorem whose statement is a type and whose
body is typed, under the same conditions on the package. -/
theorem withTheorem_uninhabited {R : Rules Head} {T : Tm Head 0}
    (fresh : R.constantType name = none) (formed : IsType R .nil T) (typed : Typed R .nil body T)
    (declaredFree : ∀ {c : DeclName} {A : Tm Head 0}, R.constantType c = some A →
      name ∉ constantNames A)
    (stable : ∀ {n : Nat} {l r : Tm Head n}, R.computation.step l r →
      R.computation.step (unfoldTm name body l) (unfoldTm name body r))
    {P : Tm Head 0} (propFree : name ∉ constantNames P) (empty : ∀ t : Tm Head 0, ¬ Typed R .nil t P)
    (t : Tm Head 0) : ¬ Typed (R.withTheorem name T body) .nil t P := by
  intro typedT
  obtain ⟨_, _, typedType⟩ := formed
  have unfolded := Derivable.unfoldTheorem typed (typed.avoids fresh) (typedType.avoids fresh)
    declaredFree stable typedT
  simp only [Statement.unfold, Ctx.unfold, unfoldTm_eq_self propFree] at unfolded
  exact empty _ unfolded

end Unfolding

end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
