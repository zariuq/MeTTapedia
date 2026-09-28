import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.StrongNormalization.Renaming

/-!
# Kripke candidates

A Kripke candidate is a candidate in every scope, closed under renaming: for
each scope a set of strongly normalizing terms, closed under reduction and
under renaming into any other scope, that contains every inert term all of
whose reducts it contains. A Kripke candidate therefore contains every
variable, and a member can be weakened and applied to a fresh variable.

The strongly normalizing terms form a Kripke candidate, and Kripke candidates
are closed under

* intersections over any index, which interpret impredicative quantification;
* the Kripke function space: terms whose application, after any renaming, to
  a member of the domain is a member of the codomain;
* its dependent version over an indexed family of domains and codomains;
* pairs: terms whose projections are members of the two components.

A Kripke candidate contains every normal inert term, and contains a β-redex or
a projection of a pair when it contains the contractum and the discarded parts
are strongly normalizing. Two Kripke candidates with the same members are
equal.

The constructions assume that root steps occur at spines of computing
constants of exact arity, so that applications and projections of inert terms
have no root redex, and that the root computation reflects renaming, so that
the reducts of a renamed term are renamed reducts.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace StrongNormalization

open Normalization

variable {Head : Type} {R : Rules Head} {roles : Roles Head}

/-! ## Inert and normal terms under renaming -/

/-- A renaming of an inert term is inert. -/
theorem Inert.rename {n m : Nat} {t : Tm Head n} (inert : Inert roles t) (ρ : Ren n m) :
    Inert roles (Presentation.rename ρ t) := by
  obtain ⟨notLam, notPair, notRefl, notCtor, notPartial⟩ := inert
  refine ⟨fun b h => ?_, fun a b h => ?_, fun a h => ?_, fun k arity args role h => ?_,
    fun c arity scrutinee args role short h => ?_⟩
  · obtain ⟨b', rfl, -⟩ := rename_eq_lam h
    exact notLam b' rfl
  · obtain ⟨a', b', rfl, -, -⟩ := rename_eq_pair h
    exact notPair a' b' rfl
  · obtain ⟨a', rfl, -⟩ := rename_eq_refl h
    exact notRefl a' rfl
  · obtain ⟨args', rfl, -⟩ := rename_eq_constSpine h
    exact notCtor k arity args' role rfl
  · obtain ⟨args', rfl, rfl⟩ := rename_eq_constSpine h
    rw [List.length_map] at short
    exact notPartial c arity scrutinee args' role short rfl

/-- A variable takes no step when root steps occur at constant spines. -/
theorem var_normal (spine : SpineHeaded R) {n : Nat} (i : Fin n) (u : Tm Head n) :
    ¬ Reduces R (.var i) u := by
  intro step
  cases step with
  | root r => exact not_root_of_not_spine spine (not_spine_of (by simp) (by simp)) r

/-! ## Kripke candidates -/

/-- A Kripke candidate: in every scope a set of strongly normalizing terms,
closed under reduction and under renaming, containing every inert term whose
reducts it contains. -/
structure KCand (R : Rules Head) (roles : Roles Head) where
  /-- The members, in every scope. -/
  mem : {m : Nat} → Tm Head m → Prop
  /-- Membership is stable under renaming into any scope. -/
  rename : ∀ {m m' : Nat} (ρ : Ren m m') {t : Tm Head m}, mem t →
    mem (Presentation.rename ρ t)
  /-- Members are strongly normalizing. -/
  sn : ∀ {m : Nat} {t : Tm Head m}, mem t → SN R t
  /-- Members reduce to members. -/
  reduct : ∀ {m : Nat} {t u : Tm Head m}, mem t → Reduces R t u → mem u
  /-- An inert term is a member when all of its reducts are. -/
  inert : ∀ {m : Nat} {t : Tm Head m}, Inert roles t → (∀ u, Reduces R t u → mem u) →
    mem t

namespace KCand

/-- Kripke candidates with the same members in every scope are equal. -/
theorem ext {X Y : KCand R roles} (same : ∀ {m : Nat} (t : Tm Head m), X.mem t ↔ Y.mem t) :
    X = Y := by
  cases X with
  | mk memX _ _ _ _ =>
      cases Y with
      | mk memY _ _ _ _ =>
          have equal : @memX = @memY := by
            funext m t
            exact propext (same t)
          subst equal
          rfl

/-- The members of a Kripke candidate in one scope form a candidate. -/
def toCandidate (X : KCand R roles) (n : Nat) : Candidate R roles n where
  mem := X.mem
  sn := X.sn
  reduct := X.reduct
  inert := X.inert

theorem reducts (X : KCand R roles) {n : Nat} {t u : Tm Head n} (h : X.mem t)
    (steps : ReducesStar R t u) : X.mem u :=
  (X.toCandidate n).reducts h steps

/-- Every Kripke candidate contains the normal inert terms. -/
theorem normal (X : KCand R roles) {n : Nat} {t : Tm Head n} (inert : Inert roles t)
    (normal : ∀ u, ¬ Reduces R t u) : X.mem t :=
  (X.toCandidate n).normal inert normal

/-- A variable is in every Kripke candidate. -/
theorem var_mem (spine : SpineHeaded R) (X : KCand R roles) {n : Nat} (i : Fin n) :
    X.mem (.var i : Tm Head n) :=
  X.normal (Inert.var i) (var_normal spine i)

/-- A head is in every Kripke candidate. -/
theorem head_mem (shape : RootShape R roles) (X : KCand R roles) {n : Nat} (h : Head) :
    X.mem (.head h : Tm Head n) :=
  X.normal (Inert.head h) (head_normal shape h)

section Intersections

variable (reflects : RootReflectsRename R.computation)

/-- The strongly normalizing terms. -/
def sn' : KCand R roles where
  mem := SN R
  rename := fun {_ _} ρ {_} h => SN.rename reflects ρ h
  sn := id
  reduct := fun h step => h.reduct step
  inert := fun _ h => SN.intro h

theorem mem_sn' {n : Nat} {t : Tm Head n} : (sn' (roles := roles) reflects).mem t ↔ SN R t :=
  Iff.rfl

/-- The strongly normalizing terms in every Kripke candidate of a family, over
any index: impredicative quantification. -/
def inter {I : Sort _} (F : I → KCand R roles) : KCand R roles where
  mem := fun t => SN R t ∧ ∀ i, (F i).mem t
  rename := fun {_ _} ρ {_} h => ⟨SN.rename reflects ρ h.1, fun i => (F i).rename ρ (h.2 i)⟩
  sn := fun h => h.1
  reduct := fun h step => ⟨h.1.reduct step, fun i => (F i).reduct (h.2 i) step⟩
  inert := fun hi h =>
    ⟨SN.intro fun u step => (h u step).1, fun i => (F i).inert hi fun u step => (h u step).2 i⟩

theorem mem_inter {I : Sort _} (F : I → KCand R roles) {n : Nat} {t : Tm Head n} :
    (inter reflects F).mem t ↔ SN R t ∧ ∀ i, (F i).mem t :=
  Iff.rfl

end Intersections

section Functions

variable (shape : RootShape R roles) (reflects : RootReflectsRename R.computation)
include shape reflects

/-- An inert term all of whose reducts, applied after any renaming to members
of `X`, land in `Y`, does so itself. -/
theorem app_inert (X Y : KCand R roles) {n : Nat} {t : Tm Head n} (hi : Inert roles t)
    (hreducts : ∀ t', Reduces R t t' → ∀ {m : Nat} (ρ : Ren n m) (a : Tm Head m),
      X.mem a → Y.mem (.app (Presentation.rename ρ t') a))
    {m : Nat} (ρ : Ren n m) (a : Tm Head m) (ha : X.mem a) :
    Y.mem (.app (Presentation.rename ρ t) a) := by
  have key : ∀ a, SN R a → X.mem a → Y.mem (.app (Presentation.rename ρ t) a) := by
    intro a sa
    induction sa with
    | intro a _ ih =>
        intro ha
        refine Y.inert (hi.rename ρ).app fun v step => ?_
        rcases Inert.app_reduct shape (hi.rename ρ) step with ⟨f', s, rfl⟩ | ⟨a', s, rfl⟩
        · obtain ⟨t', s', rfl⟩ := Reduces.rename_inv reflects s
          exact hreducts t' s' ρ a ha
        · exact ih a' s (X.reduct ha s)
  exact key a (X.sn ha) ha

/-- The Kripke function space: terms whose application, after any renaming, to
a member of `X` is a member of `Y`. -/
def arrow (X Y : KCand R roles) : KCand R roles where
  mem := fun {n} t => ∀ {m : Nat} (ρ : Ren n m) (a : Tm Head m), X.mem a →
    Y.mem (.app (Presentation.rename ρ t) a)
  rename := by
    intro n n' ρ t h m ρ' a ha
    rw [rename_comp]
    exact h (fun i => ρ' (ρ i)) a ha
  sn := by
    intro n t h
    have app := Y.sn (h wk (.var 0) (X.var_mem (RootShape.spineHeaded shape) 0))
    exact SN.of_rename wk (SN.app_left app)
  reduct := by
    intro n t u h step m ρ a ha
    exact Y.reduct (h ρ a ha) (.congAppFun (StepCore.renameTerms step ρ))
  inert := by
    intro n t hi h
    exact app_inert shape reflects X Y hi h

theorem mem_arrow (X Y : KCand R roles) {n : Nat} {t : Tm Head n} :
    (arrow shape reflects X Y).mem t ↔ ∀ {m : Nat} (ρ : Ren n m) (a : Tm Head m), X.mem a →
      Y.mem (.app (Presentation.rename ρ t) a) :=
  Iff.rfl

/-- The Kripke dependent function space over an inhabited family: terms whose
application, after any renaming, to a member of `dom i` is a member of
`cod i`, for every index `i`. -/
def pi {I : Sort _} (point : I) (dom cod : I → KCand R roles) : KCand R roles where
  mem := fun {n} t => ∀ (i : I) {m : Nat} (ρ : Ren n m) (a : Tm Head m), (dom i).mem a →
    (cod i).mem (.app (Presentation.rename ρ t) a)
  rename := by
    intro n n' ρ t h i m ρ' a ha
    rw [rename_comp]
    exact h i (fun j => ρ' (ρ j)) a ha
  sn := by
    intro n t h
    have var := (dom point).var_mem (RootShape.spineHeaded shape) (0 : Fin (n + 1))
    have app := (cod point).sn (h point wk (.var 0) var)
    exact SN.of_rename wk (SN.app_left app)
  reduct := by
    intro n t u h step i m ρ a ha
    exact (cod i).reduct (h i ρ a ha) (.congAppFun (StepCore.renameTerms step ρ))
  inert := by
    intro n t hi h i
    exact app_inert shape reflects (dom i) (cod i) hi fun t' s => h t' s i

theorem mem_pi {I : Sort _} (point : I) (dom cod : I → KCand R roles) {n : Nat}
    {t : Tm Head n} :
    (pi shape reflects point dom cod).mem t ↔
      ∀ (i : I) {m : Nat} (ρ : Ren n m) (a : Tm Head m), (dom i).mem a →
        (cod i).mem (.app (Presentation.rename ρ t) a) :=
  Iff.rfl

/-- The function space is the dependent function space over a family with
one index. -/
theorem arrow_eq_pi (X Y : KCand R roles) :
    arrow shape reflects X Y = pi shape reflects () (fun _ => X) (fun _ => Y) :=
  ext fun _ => ⟨fun h _ => h, fun h => h ()⟩

end Functions

section Pairs

variable (shape : RootShape R roles)
include shape

/-- Pairs: terms whose first projection is a member of `first` and whose
second projection is a member of `second`. -/
def sigma (first second : KCand R roles) : KCand R roles where
  mem := fun t => first.mem (.fst t) ∧ second.mem (.snd t)
  rename := fun {_ _} ρ {_} h => ⟨first.rename ρ h.1, second.rename ρ h.2⟩
  sn := fun h => SN.fst_arg (first.sn h.1)
  reduct := fun h step => ⟨first.reduct h.1 (.congFst step), second.reduct h.2 (.congSnd step)⟩
  inert := fun hi h =>
    ⟨first.inert Inert.fst fun v step => by
        obtain ⟨p', s, rfl⟩ := Inert.fst_reduct shape hi step
        exact (h p' s).1,
      second.inert Inert.snd fun v step => by
        obtain ⟨p', s, rfl⟩ := Inert.snd_reduct shape hi step
        exact (h p' s).2⟩

theorem mem_sigma (first second : KCand R roles) {n : Nat} {t : Tm Head n} :
    (sigma shape first second).mem t ↔ first.mem (.fst t) ∧ second.mem (.snd t) :=
  Iff.rfl

/-- β-expansion: an applied abstraction is in a Kripke candidate when its
contractum is, its argument is strongly normalizing, and so is its body. -/
theorem beta (X : KCand R roles) {n : Nat} {body : Tm Head (n + 1)} {a : Tm Head n}
    (sb : SN R body) (sa : SN R a) (contractum : X.mem (inst0 a body)) :
    X.mem (.app (.lam body) a) :=
  (X.toCandidate n).beta shape sb sa contractum

/-- A first projection of a pair is in a Kripke candidate when the first
component is and the second component is strongly normalizing. -/
theorem fst_pair (X : KCand R roles) {n : Nat} {a b : Tm Head n} (sb : SN R b)
    (ha : X.mem a) : X.mem (.fst (.pair a b)) :=
  (X.toCandidate n).fst_pair shape sb ha

/-- A second projection of a pair is in a Kripke candidate when the second
component is and the first component is strongly normalizing. -/
theorem snd_pair (X : KCand R roles) {n : Nat} {a b : Tm Head n} (sa : SN R a)
    (hb : X.mem b) : X.mem (.snd (.pair a b)) :=
  (X.toCandidate n).snd_pair shape sa hb

end Pairs

end KCand

end StrongNormalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
