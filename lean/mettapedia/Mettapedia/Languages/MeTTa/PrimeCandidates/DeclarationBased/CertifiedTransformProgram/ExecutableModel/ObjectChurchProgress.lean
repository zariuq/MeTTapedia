import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectFormFactsBridge
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.StrongNormalization.Spines
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.Progress

/-!
# Progress for the annotated types of the object package

**Progress** (`objectChurch_typeProgress`): a type of a universe, over a formed annotated
context of the object package, takes an annotated weak-head step, or its erasure is in
weak-head form. This is the property the transfer of the facts about weak-head forms from
the annotation to the package itself needs (`objectRules_formFacts_of`), besides lifting.

The proof is the generic progress theorem, instantiated at this package
(`objectProgressFacts`, `objectChurch_progress`): a typed term takes a weak-head step or is a
weak-head normal form of one of the shapes `WhnfShape` lists: a type former, an abstraction, a
pair, reflexivity, a term with a neutral erasure, the type of numbers, a constructor spine, or
a computing constant applied to fewer arguments than its arity (each takes no step,
`WhnfShape.no_step`). The induction on the size of the term is the generic one. What this
package supplies, one constant at a time, is the declared type of each constructor and each
computing constant, a root step at each canonical scrutinee, and the no-confusion of the
numbers and the codes with each other and with the type formers.
* **Canonical forms** (`canonical_at`). A weak-head normal form typed at the numbers is zero
  or a successor, at the codes an implication, a quantifier or an equation code, at an
  identity type reflexivity, at a dependent pair type a pair, at a dependent function type an
  abstraction or a partial spine, and at a universe a type in weak-head form, each up to a
  neutral term. The shapes are read off **principal types** (`PrincipalType`): a constant
  spine's declared type, instantiated along the spine, is below each of its types
  (`principal_spine`); and the kinds of types in weak-head form are told apart by the
  no-confusion of the annotated facts (`below_kind_false`).
* **Root steps at canonical forms** exist for every declared computation: they are root steps
  of the package at the erasure, and root steps lift to the annotation
  (`objectChurch_lift`).

With lifting of types and of equations of types to the annotation, the facts about the
weak-head forms of the package's own types follow (`objectRules_formFacts_given_lifting`),
and so does the completeness of its conversion algorithm
(`objectRules_algorithmicComplete_given_lifting`).
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
open TelescopeAbstraction (applyClosed)
open Package (jName numRecName eqAtName sucMoveName keepName transportName composeName
  iterName returnIterName sucStepName)

namespace CodeModel

namespace Progress

/-! ## Spines and sizes -/

section Spines

variable {Head : Type}

/-- A spine at arguments in two parts. -/
theorem appSpine_append {n : Nat} : ∀ (as bs : List (CTm Head n)) (f : CTm Head n),
    CTm.appSpine f (as ++ bs) = CTm.appSpine (CTm.appSpine f as) bs
  | [], _, _ => rfl
  | a :: as, bs, f => appSpine_append as bs (.app f a)

/-- A spine extended by one argument. -/
theorem appSpine_snoc {n : Nat} (as : List (CTm Head n)) (f a : CTm Head n) :
    CTm.appSpine f (as ++ [a]) = .app (CTm.appSpine f as) a :=
  appSpine_append as [a] f

/-- A spine at arguments around one of them. -/
theorem appSpine_around {n : Nat} (before after : List (CTm Head n)) (f x : CTm Head n) :
    CTm.appSpine f (before ++ x :: after) = CTm.appSpine (.app (CTm.appSpine f before) x) after :=
  appSpine_append before (x :: after) f

/-- A list longer than `k` splits at position `k`. -/
theorem split_at {α : Type} : ∀ (k : Nat) (as : List α), k < as.length →
    ∃ before x after, as = before ++ x :: after ∧ before.length = k
  | 0, a :: as, _ => ⟨[], a, as, rfl, rfl⟩
  | k + 1, a :: as, h => by
      obtain ⟨before, x, after, rfl, length⟩ := split_at k as (Nat.lt_of_succ_lt_succ h)
      exact ⟨a :: before, x, after, rfl, congrArg (· + 1) length⟩

variable {R : Rules Head} {P : ChurchRules R}

/-- A typed spine has a typed function. -/
theorem typed_appSpine_fun {n : Nat} {Γ : CCtx Head n} :
    ∀ (as : List (CTm Head n)) {f T : CTm Head n}, CTyped P Γ (CTm.appSpine f as) T →
      ∃ S, CTyped P Γ f S
  | [], _, T, typing => ⟨T, typing⟩
  | a :: as, f, _, typing => by
      obtain ⟨S, tS⟩ := typed_appSpine_fun as (f := .app f a) typing
      obtain ⟨A, B, tf, _, _⟩ := tS.generation
      exact ⟨_, tf⟩

end Spines

/-! ## Leading dependent function types -/

section Binders

variable {Head : Type}

/-- `afterBinders test k X`: the term `X` has `k` leading dependent function binders, and
what follows them passes `test`. -/
def afterBinders (test : ∀ {m : Nat}, CTm Head m → Bool) :
    Nat → {n : Nat} → CTm Head n → Bool
  | 0, _, X => test X
  | k + 1, _, .pi _ B => afterBinders test k B
  | _ + 1, _, _ => false

/-- A dependent function type. -/
def isPiTest : ∀ {m : Nat}, CTm Head m → Bool
  | _, .pi _ _ => true
  | _, _ => false

/-- The constant `c`. -/
def isConstTest (c : DeclName) : ∀ {m : Nat}, CTm Head m → Bool
  | _, .const c' => decide (c' = c)
  | _, _ => false

/-- An identity type. -/
def isIdTest : ∀ {m : Nat}, CTm Head m → Bool
  | _, .id _ _ _ => true
  | _, _ => false

/-- A dependent function type whose domain passes `test`. -/
def domainTest (test : ∀ {m : Nat}, CTm Head m → Bool) : ∀ {m : Nat}, CTm Head m → Bool
  | _, .pi A _ => test A
  | _, _ => false

/-- A test kept by renaming and by substitution. -/
structure StableTest (test : ∀ {m : Nat}, CTm Head m → Bool) : Prop where
  rename : ∀ {m m' : Nat} (ρ : Ren m m') (X : CTm Head m), test X = true →
    test (X.rename ρ) = true
  subst : ∀ {m m' : Nat} (σ : CSub Head m m') (X : CTm Head m), test X = true →
    test (X.subst σ) = true

theorem afterBinders_succ {test : ∀ {m : Nat}, CTm Head m → Bool} {k n : Nat} {X : CTm Head n}
    (h : afterBinders test (k + 1) X = true) :
    ∃ A B, X = .pi A B ∧ afterBinders test k B = true := by
  cases X with
  | pi A B => exact ⟨A, B, rfl, h⟩
  | var => exact absurd h Bool.false_ne_true
  | const => exact absurd h Bool.false_ne_true
  | head => exact absurd h Bool.false_ne_true
  | sigma => exact absurd h Bool.false_ne_true
  | id => exact absurd h Bool.false_ne_true
  | lam => exact absurd h Bool.false_ne_true
  | app => exact absurd h Bool.false_ne_true
  | pair => exact absurd h Bool.false_ne_true
  | fst => exact absurd h Bool.false_ne_true
  | snd => exact absurd h Bool.false_ne_true
  | refl => exact absurd h Bool.false_ne_true

theorem isPiTest_inv {m : Nat} {X : CTm Head m} (h : isPiTest X = true) : ∃ A B, X = .pi A B := by
  cases X with
  | pi A B => exact ⟨A, B, rfl⟩
  | var => exact absurd h Bool.false_ne_true
  | const => exact absurd h Bool.false_ne_true
  | head => exact absurd h Bool.false_ne_true
  | sigma => exact absurd h Bool.false_ne_true
  | id => exact absurd h Bool.false_ne_true
  | lam => exact absurd h Bool.false_ne_true
  | app => exact absurd h Bool.false_ne_true
  | pair => exact absurd h Bool.false_ne_true
  | fst => exact absurd h Bool.false_ne_true
  | snd => exact absurd h Bool.false_ne_true
  | refl => exact absurd h Bool.false_ne_true

theorem isConstTest_inv {c : DeclName} {m : Nat} {X : CTm Head m} (h : isConstTest c X = true) :
    X = .const c := by
  cases X with
  | const c' => exact congrArg CTm.const (of_decide_eq_true h)
  | var => exact absurd h Bool.false_ne_true
  | pi => exact absurd h Bool.false_ne_true
  | head => exact absurd h Bool.false_ne_true
  | sigma => exact absurd h Bool.false_ne_true
  | id => exact absurd h Bool.false_ne_true
  | lam => exact absurd h Bool.false_ne_true
  | app => exact absurd h Bool.false_ne_true
  | pair => exact absurd h Bool.false_ne_true
  | fst => exact absurd h Bool.false_ne_true
  | snd => exact absurd h Bool.false_ne_true
  | refl => exact absurd h Bool.false_ne_true

theorem isIdTest_inv {m : Nat} {X : CTm Head m} (h : isIdTest X = true) :
    ∃ A a b, X = .id A a b := by
  cases X with
  | id A a b => exact ⟨A, a, b, rfl⟩
  | var => exact absurd h Bool.false_ne_true
  | pi => exact absurd h Bool.false_ne_true
  | head => exact absurd h Bool.false_ne_true
  | sigma => exact absurd h Bool.false_ne_true
  | const => exact absurd h Bool.false_ne_true
  | lam => exact absurd h Bool.false_ne_true
  | app => exact absurd h Bool.false_ne_true
  | pair => exact absurd h Bool.false_ne_true
  | fst => exact absurd h Bool.false_ne_true
  | snd => exact absurd h Bool.false_ne_true
  | refl => exact absurd h Bool.false_ne_true

theorem domainTest_inv {test : ∀ {m : Nat}, CTm Head m → Bool} {m : Nat} {X : CTm Head m}
    (h : domainTest test X = true) : ∃ A B, X = .pi A B ∧ test A = true := by
  cases X with
  | pi A B => exact ⟨A, B, rfl, h⟩
  | var => exact absurd h Bool.false_ne_true
  | const => exact absurd h Bool.false_ne_true
  | head => exact absurd h Bool.false_ne_true
  | sigma => exact absurd h Bool.false_ne_true
  | id => exact absurd h Bool.false_ne_true
  | lam => exact absurd h Bool.false_ne_true
  | app => exact absurd h Bool.false_ne_true
  | pair => exact absurd h Bool.false_ne_true
  | fst => exact absurd h Bool.false_ne_true
  | snd => exact absurd h Bool.false_ne_true
  | refl => exact absurd h Bool.false_ne_true

theorem isPiTest_stable : StableTest (Head := Head) isPiTest where
  rename ρ X h := by
    obtain ⟨A, B, rfl⟩ := isPiTest_inv h
    rfl
  subst σ X h := by
    obtain ⟨A, B, rfl⟩ := isPiTest_inv h
    rfl

theorem isConstTest_stable (c : DeclName) : StableTest (Head := Head) (isConstTest c) where
  rename ρ X h := by
    obtain rfl := isConstTest_inv h
    exact h
  subst σ X h := by
    obtain rfl := isConstTest_inv h
    exact h

theorem isIdTest_stable : StableTest (Head := Head) isIdTest where
  rename ρ X h := by
    obtain ⟨A, a, b, rfl⟩ := isIdTest_inv h
    rfl
  subst σ X h := by
    obtain ⟨A, a, b, rfl⟩ := isIdTest_inv h
    rfl

theorem domainTest_stable {test : ∀ {m : Nat}, CTm Head m → Bool} (stable : StableTest test) :
    StableTest (domainTest test) where
  rename ρ X h := by
    obtain ⟨A, B, rfl, hA⟩ := domainTest_inv h
    exact stable.rename ρ A hA
  subst σ X h := by
    obtain ⟨A, B, rfl, hA⟩ := domainTest_inv h
    exact stable.subst σ A hA

theorem afterBinders_rename {test : ∀ {m : Nat}, CTm Head m → Bool} (stable : StableTest test) :
    ∀ (k : Nat) {n m : Nat} (ρ : Ren n m) (X : CTm Head n), afterBinders test k X = true →
      afterBinders test k (X.rename ρ) = true
  | 0, _, _, ρ, X, h => stable.rename ρ X h
  | k + 1, _, _, ρ, X, h => by
      obtain ⟨A, B, rfl, hB⟩ := afterBinders_succ h
      exact afterBinders_rename stable k (liftRen ρ) B hB

theorem afterBinders_subst {test : ∀ {m : Nat}, CTm Head m → Bool} (stable : StableTest test) :
    ∀ (k : Nat) {n m : Nat} (σ : CSub Head n m) (X : CTm Head n),
      afterBinders test k X = true → afterBinders test k (X.subst σ) = true
  | 0, _, _, σ, X, h => stable.subst σ X h
  | k + 1, _, _, σ, X, h => by
      obtain ⟨A, B, rfl, hB⟩ := afterBinders_succ h
      exact afterBinders_subst stable k (CTm.liftSub σ) B hB

/-- A closed term's test, in every context. -/
theorem afterBinders_liftClosed {test : ∀ {m : Nat}, CTm Head m → Bool}
    (stable : StableTest test) {k : Nat} {D : CTm Head 0} (h : afterBinders test k D = true)
    {n : Nat} :
    afterBinders test k (D.liftClosed : CTm Head n) = true :=
  afterBinders_rename stable k Fin.elim0 D h

/-- Fewer leading dependent function binders. -/
theorem afterBinders_isPi_le : ∀ {j k : Nat}, j ≤ k → ∀ {n : Nat} {X : CTm Head n},
    afterBinders isPiTest k X = true → afterBinders isPiTest j X = true
  | 0, 0, _, _, _, h => h
  | 0, _ + 1, _, _, _, h => by
      obtain ⟨A, B, rfl, _⟩ := afterBinders_succ h
      rfl
  | _ + 1, 0, le, _, _, _ => absurd le (Nat.not_succ_le_zero _)
  | j + 1, k + 1, le, _, _, h => by
      obtain ⟨A, B, rfl, hB⟩ := afterBinders_succ h
      exact afterBinders_isPi_le (Nat.le_of_succ_le_succ le) hB

end Binders

/-! ## Principal types -/

section Principal

variable {Head L : Type} [LevelOrder L] {R : Rules Head} {P : ChurchRules R}

/-- **A principal type** of `f`: a type below every type of `f`. -/
def PrincipalType (P : ChurchRules R) {n : Nat} (Γ : CCtx Head n) (f X : CTm Head n) : Prop :=
  ∀ {T : CTm Head n}, CTyped P Γ f T → CBelow P Γ X T

/-- A constant's declared type is principal. -/
theorem principal_const (levels : LevelModel R L) {n : Nat} {Γ : CCtx Head n}
    (formed : CCtxFormed P Γ) {c : DeclName} {D : CTm Head 0}
    (declared : P.constantType c = some D) : PrincipalType P Γ (.const c) D.liftClosed := by
  intro T typing
  obtain ⟨type, u, d, _, _, le⟩ := typing.generation
  obtain rfl : D = type := Option.some.inj (declared.symm.trans d)
  exact CTypeLe.toBelow le (CTyped.isType levels typing formed)

variable (facts : CFormerFacts P) (levels : LevelModel R L)
include facts levels

/-- The codomain of a principal dependent function type, at the argument, is principal for
the application, and the argument is typed at the domain. -/
theorem principal_app {n : Nat} {Γ : CCtx Head n} (formed : CCtxFormed P Γ)
    {f A a : CTm Head n} {B : CTm Head (n + 1)} (principal : PrincipalType P Γ f (.pi A B)) :
    PrincipalType P Γ (.app f a) (CTm.inst0 a B) ∧
      ∀ {T : CTm Head n}, CTyped P Γ (.app f a) T → CTyped P Γ a A := by
  have key : ∀ {T : CTm Head n}, CTyped P Γ (.app f a) T →
      CTyped P Γ a A ∧ CBelow P Γ (CTm.inst0 a B) T := by
    intro T typing
    obtain ⟨A₁, B₁, tf, ta, le⟩ := typing.generation
    obtain ⟨eA, leB⟩ := CBelow.pi_parts facts levels (principal tf) formed
    have ta' : CTyped P Γ a A := CTyped.convType ta eA.symm
    exact ⟨ta', .subTrans (CBelow.instantiate leB ta')
      (CTypeLe.toBelow le (CTyped.isType levels typing formed))⟩
  exact ⟨fun typing => (key typing).2, fun typing => (key typing).1⟩

/-- **Principal types along a spine**: instantiating the leading binders of a principal type
at the arguments of a spine gives a principal type of the spine, which keeps every stable
test of what follows the binders. -/
theorem principal_spine {n : Nat} {Γ : CCtx Head n} (formed : CCtxFormed P Γ)
    {test : ∀ {m : Nat}, CTm Head m → Bool} (stable : StableTest test) :
    ∀ (as : List (CTm Head n)) {f X : CTm Head n} {k : Nat}, PrincipalType P Γ f X →
      afterBinders test (k + as.length) X = true →
        ∃ X', PrincipalType P Γ (CTm.appSpine f as) X' ∧ afterBinders test k X' = true
  | [], _, X, _, principal, h => ⟨X, principal, h⟩
  | a :: as, _, _, k, principal, h => by
      obtain ⟨A, B, rfl, hB⟩ := afterBinders_succ (k := k + as.length) h
      exact principal_spine formed stable as (principal_app facts levels formed principal).1
        (afterBinders_subst stable _ (CTm.subst0 a) B hB)

/-- The argument of a spine at a position whose binder's domain passes a stable test is typed
at a type passing the test. -/
theorem argument_typed {n : Nat} {Γ : CCtx Head n} (formed : CCtxFormed P Γ)
    {test : ∀ {m : Nat}, CTm Head m → Bool} (stable : StableTest test) {f X : CTm Head n}
    (principal : PrincipalType P Γ f X) {before after : List (CTm Head n)} {x T : CTm Head n}
    (h : afterBinders (domainTest test) before.length X = true)
    (typing : CTyped P Γ (CTm.appSpine f (before ++ x :: after)) T) :
    ∃ A, test A = true ∧ CTyped P Γ x A := by
  rw [appSpine_around] at typing
  obtain ⟨S, tS⟩ := typed_appSpine_fun after typing
  obtain ⟨X', principal', hX'⟩ := principal_spine facts levels formed (domainTest_stable stable)
    before (k := 0) principal (by rw [Nat.zero_add]; exact h)
  obtain ⟨A, B, rfl, hA⟩ := domainTest_inv hX'
  exact ⟨A, hA, (principal_app facts levels formed principal').2 tS⟩

end Principal

/-! ## Kinds of types in weak-head form, and their no-confusion -/

section Kinds

variable {n : Nat} {Γ : CCtx Tower.Head n}

/-- The kinds of types in weak-head form that canonical forms tell apart: universes,
dependent function types, dependent pair types, identity types, the numbers and the codes. -/
inductive TypeKind where
  | univ
  | pi
  | sigma
  | ident
  | num
  | prop
  deriving DecidableEq

/-- `X` is a type of the kind. -/
def TypeKind.Has {m : Nat} : TypeKind → CTm Tower.Head m → Prop
  | .univ, X => ∃ w, objectRules.isUniverse w ∧ X = .head w
  | .pi, X => ∃ A B, X = .pi A B
  | .sigma, X => ∃ A B, X = .sigma A B
  | .ident, X => ∃ A a b, X = .id A a b
  | .num, X => X = .const numN
  | .prop, X => X = .const propN

/-- The kinds whose types are type formers. -/
inductive TypeKind.IsFormer : TypeKind → Prop
  | univ : TypeKind.IsFormer .univ
  | pi : TypeKind.IsFormer .pi
  | sigma : TypeKind.IsFormer .sigma
  | ident : TypeKind.IsFormer .ident

/-- The former a term is headed by, if any. -/
def formerTag {m : Nat} : CTm Tower.Head m → Nat
  | .head _ => 0
  | .pi _ _ => 1
  | .sigma _ _ => 2
  | .id _ _ _ => 3
  | _ => 4

/-- The former of a kind. -/
def TypeKind.tag : TypeKind → Nat
  | .univ => 0
  | .pi => 1
  | .sigma => 2
  | .ident => 3
  | .num => 4
  | .prop => 5

theorem TypeKind.Has.cformer {k : TypeKind} (former : k.IsFormer) {m : Nat}
    {X : CTm Tower.Head m} (has : k.Has X) : CFormer X := by
  cases k with
  | univ =>
      obtain ⟨w, _, rfl⟩ := has
      exact .head w
  | pi =>
      obtain ⟨A, B, rfl⟩ := has
      exact .pi A B
  | sigma =>
      obtain ⟨A, B, rfl⟩ := has
      exact .sigma A B
  | ident =>
      obtain ⟨A, a, b, rfl⟩ := has
      exact .id A a b
  | num => exact nomatch former
  | prop => exact nomatch former

theorem TypeKind.Has.formerTag {k : TypeKind} (former : k.IsFormer) {m : Nat}
    {X : CTm Tower.Head m} (has : k.Has X) : Progress.formerTag X = k.tag := by
  cases k with
  | univ =>
      obtain ⟨w, _, rfl⟩ := has
      rfl
  | pi =>
      obtain ⟨A, B, rfl⟩ := has
      rfl
  | sigma =>
      obtain ⟨A, B, rfl⟩ := has
      rfl
  | ident =>
      obtain ⟨A, a, b, rfl⟩ := has
      rfl
  | num => exact nomatch former
  | prop => exact nomatch former

theorem TypeKind.tag_injective {k k' : TypeKind} (same : k.tag = k'.tag) : k = k' := by
  cases k <;> cases k' <;> first | rfl | exact absurd same (by decide)

/-- Matching formers have one former. -/
theorem CFormersMatch.formerTag {m : Nat} {Δ : CCtx Tower.Head m} {X Y : CTm Tower.Head m}
    (matching : CFormersMatch objectChurch Δ X Y) :
    Progress.formerTag X = Progress.formerTag Y := by
  rcases matching with ⟨_, _, rfl, rfl, _⟩ | ⟨_, _, _, _, rfl, rfl, _⟩ |
    ⟨_, _, _, _, rfl, rfl, _⟩ | ⟨_, _, _, _, _, _, rfl, rfl, _⟩ <;> rfl

/-- The numbers are a type in weak-head form: the type constant of an inductive type. -/
theorem typeForm_num {m : Nat} :
    IsTypeForm objectRoles (CTm.const numN : CTm Tower.Head m).erase :=
  .inr (.inr (.inr (.inr (.inr ⟨numN, ctors, objectRoles_num, rfl⟩))))

/-- The codes are a neutral type: a rigid constant. -/
theorem neutral_prop {m : Nat} :
    Neutral objectRoles (CTm.const propN : CTm Tower.Head m).erase :=
  Neutral.rigid (c := propN) [] objectRoles_propRigid

/-- The codes are a type in weak-head form. -/
theorem typeForm_prop {m : Nat} :
    IsTypeForm objectRoles (CTm.const propN : CTm Tower.Head m).erase :=
  .inr (.inr (.inr (.inr (.inl neutral_prop))))

/-- **No type former is equal to a type constant in weak-head form.** -/
theorem former_ne_const (formed : CCtxFormed objectChurch Γ) {X : CTm Tower.Head n}
    (former : CFormer X) {c : DeclName}
    (form : IsTypeForm objectRoles (CTm.const c : CTm Tower.Head n).erase)
    (equal : CTypeEq objectChurch Γ X (.const c)) : False := by
  have matching := (objectFormFacts.forms equal formed former.typeForm form).formers_left former
  exact nomatch matching.right

/-- **The numbers are not the codes.** -/
theorem num_ne_prop (formed : CCtxFormed objectChurch Γ)
    (equal : CTypeEq objectChurch Γ (.const numN) (.const propN)) : False := by
  rcases objectFormFacts.forms equal formed typeForm_num typeForm_prop with
    matching | ⟨T, cs, _, e₁, e₂⟩ | ⟨neutral, _⟩
  · rcases matching with ⟨_, _, e, _⟩ | ⟨_, _, _, _, e, _⟩ | ⟨_, _, _, _, e, _⟩ |
      ⟨_, _, _, _, _, _, e, _⟩ <;> cases e
  · exact absurd (CTm.const.inj (e₁.trans e₂.symm)) (by decide)
  · exact neutral.ne_inductive objectRoles_num rfl

/-- **Types of distinct kinds are not equal.** -/
theorem kind_distinct (formed : CCtxFormed objectChurch Γ) {k k' : TypeKind}
    {X Y : CTm Tower.Head n} (hX : k.Has X) (hY : k'.Has Y) (distinct : k ≠ k')
    (equal : CTypeEq objectChurch Γ X Y) : False := by
  have cases_of : ∀ j : TypeKind, j.IsFormer ∨ j = .num ∨ j = .prop := by
    intro j
    cases j
    · exact .inl .univ
    · exact .inl .pi
    · exact .inl .sigma
    · exact .inl .ident
    · exact .inr (.inl rfl)
    · exact .inr (.inr rfl)
  rcases cases_of k with fk | rfl | rfl <;> rcases cases_of k' with fk' | rfl | rfl
  · have tags := CFormersMatch.formerTag
      (objectFormerFacts.forms equal formed (hX.cformer fk) (hY.cformer fk'))
    rw [hX.formerTag fk, hY.formerTag fk'] at tags
    exact distinct (TypeKind.tag_injective tags)
  · obtain rfl : Y = .const numN := hY
    exact former_ne_const formed (hX.cformer fk) typeForm_num equal
  · obtain rfl : Y = .const propN := hY
    exact former_ne_const formed (hX.cformer fk) typeForm_prop equal
  · obtain rfl : X = .const numN := hX
    exact former_ne_const formed (hY.cformer fk') typeForm_num equal.symm
  · exact distinct rfl
  · obtain rfl : X = .const numN := hX
    obtain rfl : Y = .const propN := hY
    exact num_ne_prop formed equal
  · obtain rfl : X = .const propN := hX
    exact former_ne_const formed (hY.cformer fk') typeForm_prop equal.symm
  · obtain rfl : X = .const propN := hX
    obtain rfl : Y = .const numN := hY
    exact num_ne_prop formed equal.symm
  · exact distinct rfl

/-- A type constant in weak-head form is usable only at types equal to it. -/
theorem below_const {X T : CTm Tower.Head n} (le : CBelow objectChurch Γ X T)
    (formed : CCtxFormed objectChurch Γ) {c : DeclName}
    (form : ∀ {m : Nat}, IsTypeForm objectRoles (CTm.const c : CTm Tower.Head m).erase)
    (eX : CTypeEq objectChurch Γ X (.const c)) : CTypeEq objectChurch Γ T (.const c) := by
  refine CBelow.induction (motive := fun m Δ X T => CCtxFormed objectChurch Δ →
      CTypeEq objectChurch Δ X (.const c) → CTypeEq objectChurch Δ T (.const c))
    ?equal ?univ ?pi ?sigma ?trans le formed eX
  case equal =>
    intro m Δ X T u e hu _ eX
    exact CTypeEq.trans ConvRules.objectLevels (CTypeEq.symm ⟨u, hu, e⟩) eX
  case univ =>
    intro m Δ u v _ formed eX
    exact (former_ne_const formed (.head u) form eX).elim
  case pi =>
    intro m Δ A A' B B' _ _ _ _ _ _ _ _ _ _ _ formed eX
    exact (former_ne_const formed (.pi A B) form eX).elim
  case sigma =>
    intro m Δ A A' B B' _ _ _ _ _ _ _ _ _ _ formed eX
    exact (former_ne_const formed (.sigma A B) form eX).elim
  case trans =>
    intro m Δ X Y T _ _ ih₁ ih₂ formed eX
    exact ih₂ formed (ih₁ formed eX)

/-- **A type of a kind is usable only at types equal to one of that kind.** -/
theorem below_kind (formed : CCtxFormed objectChurch Γ) {X T : CTm Tower.Head n}
    (le : CBelow objectChurch Γ X T) {k : TypeKind} (hX : k.Has X) :
    ∃ Y, k.Has Y ∧ CTypeEq objectChurch Γ T Y := by
  have typeX : CIsType objectChurch Γ X := (CBelow.isTypes ConvRules.objectLevels le formed).1
  cases k with
  | univ =>
      obtain ⟨w, hw, rfl⟩ := hX
      obtain ⟨v, hv, e, _⟩ := CBelow.universe_cumulative objectFormerFacts
        ConvRules.objectLevels (ConvRules.realRules_algebra objectTExt) le formed hw
        (CIsType.refl typeX)
      exact ⟨.head v, ⟨v, hv, rfl⟩, e⟩
  | pi =>
      obtain ⟨A, B, rfl⟩ := hX
      obtain ⟨A', B', e, _, _⟩ := CBelow.pi_source objectFormerFacts ConvRules.objectLevels le
        formed (CIsType.refl typeX)
      exact ⟨.pi A' B', ⟨A', B', rfl⟩, e⟩
  | sigma =>
      obtain ⟨A, B, rfl⟩ := hX
      obtain ⟨A', B', e, _, _⟩ := CBelow.sigma_source objectFormerFacts ConvRules.objectLevels
        le formed (CIsType.refl typeX)
      exact ⟨.sigma A' B', ⟨A', B', rfl⟩, e⟩
  | ident =>
      obtain ⟨A, a, b, rfl⟩ := hX
      exact ⟨.id A a b, ⟨A, a, b, rfl⟩,
        CBelow.id_eq objectFormerFacts ConvRules.objectLevels le formed (CIsType.refl typeX)⟩
  | num =>
      obtain rfl : X = .const numN := hX
      exact ⟨.const numN, rfl, below_const le formed typeForm_num (CIsType.refl typeX)⟩
  | prop =>
      obtain rfl : X = .const propN := hX
      exact ⟨.const propN, rfl, below_const le formed typeForm_prop (CIsType.refl typeX)⟩

/-- **A type of one kind is usable at no type of another kind.** -/
theorem below_kind_false (formed : CCtxFormed objectChurch Γ) {X T : CTm Tower.Head n}
    (le : CBelow objectChurch Γ X T) {k k' : TypeKind} (hX : k.Has X) (hT : k'.Has T)
    (distinct : k ≠ k') : False := by
  obtain ⟨Y, hY, e⟩ := below_kind formed le hX
  exact kind_distinct formed hT hY (Ne.symm distinct) e

end Kinds

/-! ## The roles and declared types of the object package, constant by constant -/

section Roles

/-- The constructors of the executable package are zero and the successor. -/
theorem roles_constructor_cases {c : DeclName} {arity : Nat} (role : roles c = .constructor arity) :
    (c = zeroN ∧ arity = 0) ∨ (c = sucN ∧ arity = 1) := by
  by_cases mem : c ∈ nonrigidNames
  · simp only [nonrigidNames, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    · rw [roles_num] at role; cases role
    · rw [roles_zero] at role; cases role; exact .inl ⟨rfl, rfl⟩
    · rw [roles_suc] at role; cases role; exact .inr ⟨rfl, rfl⟩
    · rw [roles_numRec] at role; cases role
    · rw [roles_add] at role; cases role
    · rw [roles_pow] at role; cases role
    · rw [roles_j] at role; cases role
    · rw [roles_eqAt] at role; cases role
    · rw [roles_sucMove] at role; cases role
    · rw [roles_keep] at role; cases role
    · rw [roles_transport] at role; cases role
    · rw [roles_compose] at role; cases role
    · rw [roles_iter] at role; cases role
    · rw [roles_returnIter] at role; cases role
    · rw [roles_sucStep] at role; cases role
  · rw [roles_of_not_mem mem] at role; cases role

/-- The computing constants of the executable package. -/
theorem roles_computes_cases {c : DeclName} {arity : Nat} {inspect : InspectTree}
    (role : roles c = .computes arity inspect) :
    c = numRecName ∨ c = addN ∨ c = powN ∨ c = jName ∨ c = eqAtName ∨ c = sucMoveName ∨
      c = keepName ∨ c = transportName ∨ c = composeName ∨ c = iterName ∨
        c = returnIterName ∨ c = sucStepName := by
  by_cases mem : c ∈ nonrigidNames
  · simp only [nonrigidNames, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl | h
    · rw [roles_num] at role; cases role
    · rw [roles_zero] at role; cases role
    · rw [roles_suc] at role; cases role
    · exact h
  · rw [roles_of_not_mem mem] at role; cases role

/-- **The constructors of the object package**: zero, the successor, implication, and every
quantifier and equation code. -/
theorem objectRoles_constructor_cases {k : DeclName} {arity : Nat}
    (role : objectRoles k = .constructor arity) :
    (k = zeroN ∧ arity = 0) ∨ (k = sucN ∧ arity = 1) ∨ (k = impN ∧ arity = 2) ∨
      (∃ type, k = SetProfile.allName type ∧ arity = 1) ∨
        (∃ type, k = SetProfile.eqName type ∧ arity = 2) := by
  by_cases hh : k = holdsN
  · subst hh; rw [objectRoles_holds] at role; cases role
  by_cases hi : k = impN
  · subst hi; rw [objectRoles_imp] at role; cases role
    exact .inr (.inr (.inl ⟨rfl, rfl⟩))
  cases ha : SetProfile.allInstance? k with
  | some type =>
      rw [objectRoles_all ha] at role; cases role
      exact .inr (.inr (.inr (.inl ⟨type, SetProfile.allInstance?_eq_some ha, rfl⟩)))
  | none =>
      cases he : SetProfile.eqInstance? k with
      | some type =>
          rw [objectRoles_eq he] at role; cases role
          exact .inr (.inr (.inr (.inr ⟨type, SetProfile.eqInstance?_eq_some he, rfl⟩)))
      | none =>
          rw [objectRoles_of hh hi ha he] at role
          rcases roles_constructor_cases role with h | h
          · exact .inl h
          · exact .inr (.inl h)

/-- **The computing constants of the object package**: the decoder, and those of the
executable package. -/
theorem objectRoles_computes_cases {c : DeclName} {arity : Nat} {inspect : InspectTree}
    (role : objectRoles c = .computes arity inspect) :
    c = holdsN ∨ roles c = .computes arity inspect := by
  by_cases hh : c = holdsN
  · exact .inl hh
  by_cases hi : c = impN
  · subst hi; rw [objectRoles_imp] at role; cases role
  cases ha : SetProfile.allInstance? c with
  | some type => rw [objectRoles_all ha] at role; cases role
  | none =>
      cases he : SetProfile.eqInstance? c with
      | some type => rw [objectRoles_eq he] at role; cases role
      | none => exact .inr ((objectRoles_of hh hi ha he).symm.trans role)

theorem objectRoles_numRec :
    objectRoles numRecName = .computes 4 (.split 3 .constructor fun _ => .leaf) :=
  objectRoles_of_roles roles_numRec nofun
theorem objectRoles_add : objectRoles addN = .computes 2 (.split 1 .constructor fun _ => .leaf) :=
  objectRoles_of_roles roles_add nofun
theorem objectRoles_pow : objectRoles powN = .computes 2 (.split 0 .constructor fun _ => .leaf) :=
  objectRoles_of_roles roles_pow nofun
theorem objectRoles_j : objectRoles jName = .computes 6 (.split 5 .constructor fun _ => .leaf) :=
  objectRoles_of_roles roles_j nofun
theorem objectRoles_iter :
    objectRoles iterName = .computes 6 (.split 0 .constructor fun _ => .leaf) :=
  objectRoles_of_roles roles_iter nofun

end Roles

section Declarations

/-- The declared type of the numbers. -/
theorem declared_num : objectChurch.constantType numN = some (liftTm (Package.U0 : Tower.Tm 0)) :=
  objectChurch_declared (by decide) (by decide)

theorem declared_holds : objectChurch.constantType holdsN = some (liftTm programCodes.holdsType) :=
  objectChurch_declared (by decide) (by decide)
theorem declared_numRec :
    objectChurch.constantType numRecName = some (liftTm Package.numRecType) :=
  objectChurch_declared (by decide) (by decide)
theorem declared_add : objectChurch.constantType addN = some (liftTm addType) :=
  objectChurch_declared (by decide) (by decide)
theorem declared_pow : objectChurch.constantType powN = some (liftTm powType) :=
  objectChurch_declared (by decide) (by decide)
theorem declared_j : objectChurch.constantType jName = some (liftTm Package.jType) :=
  objectChurch_declared (by decide) (by decide)
theorem declared_eqAt : objectChurch.constantType eqAtName = some (liftTm Package.eqAtType) :=
  objectChurch_declared (by decide) (by decide)
theorem declared_sucMove :
    objectChurch.constantType sucMoveName = some (liftTm Package.sucMoveType) :=
  objectChurch_declared (by decide) (by decide)
theorem declared_keep : objectChurch.constantType keepName = some (liftTm Package.keepType) :=
  objectChurch_declared (by decide) (by decide)
theorem declared_transport :
    objectChurch.constantType transportName = some (liftTm Package.transportType) :=
  objectChurch_declared (by decide) (by decide)
theorem declared_compose :
    objectChurch.constantType composeName = some (liftTm Package.composeType) :=
  objectChurch_declared (by decide) (by decide)
theorem declared_iter : objectChurch.constantType iterName = some (liftTm Package.iterType) :=
  objectChurch_declared (by decide) (by decide)
theorem declared_returnIter :
    objectChurch.constantType returnIterName = some (liftTm Package.returnIterType) :=
  objectChurch_declared (by decide) (by decide)
theorem declared_sucStep :
    objectChurch.constantType sucStepName = some (liftTm Package.sucStepType) :=
  objectChurch_declared (by decide) (by decide)

/-- **The declared types of the computing constants have at least their arity of leading
dependent function binders.** -/
theorem computes_declared {c : DeclName} {arity : Nat} {inspect : InspectTree}
    (role : objectRoles c = .computes arity inspect) :
    0 < arity ∧ ∃ D, objectChurch.constantType c = some D ∧
      afterBinders isPiTest (arity - 1) D = true := by
  rcases objectRoles_computes_cases role with rfl | hr
  · rw [objectRoles_holds] at role; cases role
    exact ⟨by decide, _, declared_holds, by decide⟩
  · rcases roles_computes_cases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    · rw [roles_numRec] at hr; cases hr
      exact ⟨by decide, _, declared_numRec, by decide⟩
    · rw [roles_add] at hr; cases hr
      exact ⟨by decide, _, declared_add, by decide⟩
    · rw [roles_pow] at hr; cases hr
      exact ⟨by decide, _, declared_pow, by decide⟩
    · rw [roles_j] at hr; cases hr
      exact ⟨by decide, _, declared_j, by decide⟩
    · rw [roles_eqAt] at hr; cases hr
      exact ⟨by decide, _, declared_eqAt, by decide⟩
    · rw [roles_sucMove] at hr; cases hr
      exact ⟨by decide, _, declared_sucMove, by decide⟩
    · rw [roles_keep] at hr; cases hr
      exact ⟨by decide, _, declared_keep, by decide⟩
    · rw [roles_transport] at hr; cases hr
      exact ⟨by decide, _, declared_transport, by decide⟩
    · rw [roles_compose] at hr; cases hr
      exact ⟨by decide, _, declared_compose, by decide⟩
    · rw [roles_iter] at hr; cases hr
      exact ⟨by decide, _, declared_iter, by decide⟩
    · rw [roles_returnIter] at hr; cases hr
      exact ⟨by decide, _, declared_returnIter, by decide⟩
    · rw [roles_sucStep] at hr; cases hr
      exact ⟨by decide, _, declared_sucStep, by decide⟩

end Declarations

/-! ## Root steps at canonical forms -/

section Steps

variable {n : Nat}

/-- A root step of the package at the erasure of an annotated term is the erasure of an
annotated root step of the term. -/
theorem root_of_erase {l : CTm Tower.Head n} {r₀ : Tower.Tm n}
    (step : objectRules.computation.step l.erase r₀) :
    ∃ r, objectChurch.computation.step l r := by
  obtain ⟨r, s, _⟩ := objectChurch_lift step
  exact ⟨r, s⟩

/-- A root step of one of the executable package's declared computations is a root step of
the object package. -/
theorem objectRules_step_of_mem {entry : DeclName × RootComputation Tower.Head}
    (mem : entry ∈ computations) {l r : Tower.Tm n} (step : entry.2.step l r) :
    objectRules.computation.step l r :=
  Or.inl (RootComputation.step_unionAll (List.mem_filter.mpr ⟨mem, rfl⟩) step)

/-- **A definition by one equation unfolds at every list of arguments of its arity.** -/
theorem definition_step {f : DeclName} {k : Nat} {Θ : Tower.Ctx k} {rhs : Tower.Tm k}
    (mem : (f, definitionComputation f Θ rhs) ∈ computations) {args : List (CTm Tower.Head n)}
    (length : args.length = k) :
    ∃ r, objectChurch.computation.step (CTm.appSpine (.const f) args) r := by
  obtain ⟨σ, hσ⟩ := StrongNormalization.telescopeArgs_surjective Θ (args.map CTm.erase)
    (by rw [List.length_map]; exact length)
  refine root_of_erase (r₀ := Presentation.subst σ rhs)
    (objectRules_step_of_mem (entry := (f, definitionComputation f Θ rhs)) mem ⟨σ, ?_, rfl⟩)
  rw [CTm.erase_appSpine, hσ, applyClosed_eq_appSpine]
  rfl

/-- **A definition by structural recursion computes at a constructor form of its scrutinee.** -/
theorem recursion_step {f : DeclName} {e : (i : Nat) → Tower.Tm i} {s d : Nat}
    {body : (k : DeclName) → (fields : List CtorField) →
      Tower.Tm (s + fields.length + d + (recPositions fields).length)}
    (mem : (f, recursionComputation f ctors e s d body) ∈ computations)
    {before after : List (CTm Tower.Head n)} (hb : before.length = s) (ha : after.length = d)
    {k : DeclName} {fields : List CtorField} (ctor : (k, fields) ∈ ctors)
    {as : List (CTm Tower.Head n)} (has : as.length = fields.length) :
    ∃ r, objectChurch.computation.step
      (CTm.appSpine (.const f) (before ++ CTm.appSpine (.const k) as :: after)) r := by
  have length : (before.map CTm.erase ++ appSpine (.const k) (as.map CTm.erase) ::
      after.map CTm.erase).length = s + 1 + d := by
    rw [List.length_append, List.length_cons, List.length_map, List.length_map, hb, ha]
    exact (Nat.add_right_comm s 1 d).symm
  obtain ⟨σ, hσ⟩ :=
    StrongNormalization.telescopeArgs_surjective (ofEntries e (s + 1 + d)) _ length
  have split := applyClosed_split e d σ (.const f)
  rw [applyClosed_eq_appSpine, ← hσ] at split
  obtain ⟨_, hargs⟩ := appSpine_const_injective split
  obtain ⟨_, hx, _⟩ := appendCons_inj hargs (by rw [List.length_map, telescopeArgs_length, hb])
  have replaced : replaceScrut s (appSpine (.const k) (as.map CTm.erase)) d σ = σ := by
    rw [hx]
    exact replaceScrut_self d σ
  refine root_of_erase (objectRules_step_of_mem
    (entry := (f, recursionComputation f ctors e s d body)) mem
    ⟨k, fields, σ, as.map CTm.erase, ctor, by rw [List.length_map]; exact has, ?_, rfl⟩)
  rw [replaced, applyClosed_eq_appSpine, ← hσ, CTm.erase_appSpine, List.map_append,
    List.map_cons, CTm.erase_appSpine]
  rfl

theorem zero_mem_ctors : (zeroN, ([] : List CtorField)) ∈ ctors := .head _
theorem suc_mem_ctors : (sucN, [(.recursive : CtorField)]) ∈ ctors := .tail _ (.head _)

/-- The recursor computes at zero and at a successor. -/
theorem numRec_step_zero (P z s : CTm Tower.Head n) :
    ∃ r, objectChurch.computation.step
      (CTm.appSpine (.const numRecName) [P, z, s, .const zeroN]) r :=
  root_of_erase (objectRules_step_of_mem (entry := (numRecName, iotaComputation numRecName ctors))
    (.head _)
    ⟨P.erase, [z.erase, s.erase], 0, zeroN, [], [], z.erase, rfl, rfl, rfl, rfl, rfl, rfl⟩)

theorem numRec_step_suc (P z s a : CTm Tower.Head n) :
    ∃ r, objectChurch.computation.step
      (CTm.appSpine (.const numRecName) [P, z, s, .app (.const sucN) a]) r :=
  root_of_erase (objectRules_step_of_mem (entry := (numRecName, iotaComputation numRecName ctors))
    (.head _) ⟨P.erase, [z.erase, s.erase], 1, sucN, [.recursive], [a.erase], s.erase, rfl, rfl,
      rfl, rfl, rfl, rfl⟩)

/-- The identity eliminator computes at reflexivity. -/
theorem j_step (A x M d y a : CTm Tower.Head n) :
    ∃ r, objectChurch.computation.step (CTm.appSpine (.const jName) [A, x, M, d, y, .refl a]) r :=
  root_of_erase (objectRules_step_of_mem (entry := (jName, eliminatorComputation jName))
    (.tail _ (.tail _ (.tail _ (.head _))))
    ⟨A.erase, x.erase, M.erase, d.erase, y.erase, a.erase, rfl, rfl⟩)

/-- The decoder computes at an implication, a quantifier code and an equation code. -/
theorem holds_step_imp (p q : CTm Tower.Head n) :
    ∃ r, objectChurch.computation.step (.app (.const holdsN) (.app (.app (.const impN) p) q)) r :=
  root_of_erase (Or.inr (DecoderStep.imp (D := programCodes.decoders) p.erase q.erase))

theorem holds_step_all (type : Mettapedia.Logic.HOL.Ty SetProfile.SetBase) (f : CTm Tower.Head n) :
    ∃ r, objectChurch.computation.step
      (.app (.const holdsN) (.app (.const (SetProfile.allName type)) f)) r := by
  have carrier :
      programCodes.decoders.allCarrier (SetProfile.allName type) = some (typeTerm type) := by
    change (SetProfile.allInstance? (SetProfile.allName type)).map typeTerm = some (typeTerm type)
    rw [SetProfile.allInstance?_allName]
    rfl
  exact root_of_erase (Or.inr (DecoderStep.all carrier f.erase))

theorem holds_step_eq (type : Mettapedia.Logic.HOL.Ty SetProfile.SetBase) (y z : CTm Tower.Head n) :
    ∃ r, objectChurch.computation.step
      (.app (.const holdsN) (.app (.app (.const (SetProfile.eqName type)) y) z)) r := by
  have carrier :
      programCodes.decoders.eqCarrier (SetProfile.eqName type) = some (typeTerm type) := by
    change (if true = true then (SetProfile.eqInstance? (SetProfile.eqName type)).map typeTerm
      else none) = some (typeTerm type)
    rw [if_pos rfl, SetProfile.eqInstance?_eqName]
    rfl
  exact root_of_erase (Or.inr (DecoderStep.eq carrier y.erase z.erase))

/-- Addition, the iterated power set and the iterator compute at zero and at a successor. -/
theorem add_step_zero (m : CTm Tower.Head n) :
    ∃ r, objectChurch.computation.step (CTm.appSpine (.const addN) [m, .const zeroN]) r :=
  recursion_step (f := addN) (e := addEntries) (s := 1) (d := 0) (body := addBody)
    (.tail _ (.head _)) (before := [m]) (after := []) rfl rfl zero_mem_ctors (as := []) rfl

theorem add_step_suc (m a : CTm Tower.Head n) :
    ∃ r, objectChurch.computation.step (CTm.appSpine (.const addN) [m, .app (.const sucN) a]) r :=
  recursion_step (f := addN) (e := addEntries) (s := 1) (d := 0) (body := addBody)
    (.tail _ (.head _)) (before := [m]) (after := []) rfl rfl suc_mem_ctors (as := [a]) rfl

theorem pow_step_zero (X : CTm Tower.Head n) :
    ∃ r, objectChurch.computation.step (CTm.appSpine (.const powN) [.const zeroN, X]) r :=
  recursion_step (f := powN) (e := powEntries) (s := 0) (d := 1) (body := powBody)
    (.tail _ (.tail _ (.head _))) (before := []) (after := [X]) rfl rfl zero_mem_ctors
    (as := []) rfl

theorem pow_step_suc (a X : CTm Tower.Head n) :
    ∃ r, objectChurch.computation.step (CTm.appSpine (.const powN) [.app (.const sucN) a, X]) r :=
  recursion_step (f := powN) (e := powEntries) (s := 0) (d := 1) (body := powBody)
    (.tail _ (.tail _ (.head _))) (before := []) (after := [X]) rfl rfl suc_mem_ctors
    (as := [a]) rfl

/-- The iterator's computation is declared. -/
theorem iter_mem :
    (iterName, recursionComputation iterName ctors iterEntries 0 5 iterBody) ∈ computations :=
  .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _
    (.head _)))))))))

theorem iter_step_zero (A P st x e : CTm Tower.Head n) :
    ∃ r, objectChurch.computation.step
      (CTm.appSpine (.const iterName) [.const zeroN, A, P, st, x, e]) r :=
  recursion_step (f := iterName) (e := iterEntries) (s := 0) (d := 5) (body := iterBody) iter_mem
    (before := []) (after := [A, P, st, x, e]) rfl rfl zero_mem_ctors (as := []) rfl

theorem iter_step_suc (a A P st x e : CTm Tower.Head n) :
    ∃ r, objectChurch.computation.step
      (CTm.appSpine (.const iterName) [.app (.const sucN) a, A, P, st, x, e]) r :=
  recursion_step (f := iterName) (e := iterEntries) (s := 0) (d := 5) (body := iterBody) iter_mem
    (before := []) (after := [A, P, st, x, e]) rfl rfl suc_mem_ctors (as := [a]) rfl

/-- **Every computing constant without an inspected argument unfolds at its arity**: the
definitions by one equation. -/
theorem leaf_step {c : DeclName} {arity : Nat} (role : objectRoles c = .computes arity .leaf)
    {args : List (CTm Tower.Head n)} (length : args.length = arity) :
    ∃ r, objectChurch.computation.step (CTm.appSpine (.const c) args) r := by
  rcases objectRoles_computes_cases role with rfl | hr
  · rw [objectRoles_holds] at role; cases role
  · rcases roles_computes_cases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    · rw [roles_numRec] at hr; cases hr
    · rw [roles_add] at hr; cases hr
    · rw [roles_pow] at hr; cases hr
    · rw [roles_j] at hr; cases hr
    · rw [roles_eqAt] at hr; cases hr
      exact definition_step (f := eqAtName) (Θ := eqAtTele) (rhs := eqAtRhs)
        (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) length
    · rw [roles_sucMove] at hr; cases hr
      exact definition_step (f := sucMoveName) (Θ := Package.eqAtTelescope) (rhs := sucMoveRhs)
        (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) length
    · rw [roles_keep] at hr; cases hr
      exact definition_step (f := keepName) (Θ := keepTele) (rhs := keepRhs)
        (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))) length
    · rw [roles_transport] at hr; cases hr
      exact definition_step (f := transportName) (Θ := Package.transportTelescope)
        (rhs := transportRhs)
        (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))) length
    · rw [roles_compose] at hr; cases hr
      exact definition_step (f := composeName) (Θ := Package.composeTelescope) (rhs := composeRhs)
        (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))
        length
    · rw [roles_iter] at hr; cases hr
    · rw [roles_returnIter] at hr; cases hr
      exact definition_step (f := returnIterName) (Θ := returnIterTele) (rhs := returnIterRhs)
        (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _
          (.head _))))))))))) length
    · rw [roles_sucStep] at hr; cases hr
      exact definition_step (f := sucStepName) (Θ := Package.eqAtTelescope) (rhs := sucStepRhs)
        (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _
          (.tail _ (.head _)))))))))))) length

end Steps

/-! ## Weak-head normal forms and their types -/

section Shapes

/-- **The weak-head normal forms of typed terms**, by shape: a type former, an abstraction, a
pair, reflexivity, a term with a neutral erasure, the type of numbers, a constructor spine,
or a computing constant applied to fewer arguments than its arity. -/
inductive WhnfShape : {n : Nat} → CTm Tower.Head n → Prop
  | former {n : Nat} {t : CTm Tower.Head n} : CFormer t → WhnfShape t
  | lam {n : Nat} (A : CTm Tower.Head n) (b : CTm Tower.Head (n + 1)) : WhnfShape (.lam A b)
  | pair {n : Nat} (a b : CTm Tower.Head n) : WhnfShape (.pair a b)
  | refl {n : Nat} (a : CTm Tower.Head n) : WhnfShape (.refl a)
  | neutral {n : Nat} {t : CTm Tower.Head n} : Neutral objectRoles t.erase → WhnfShape t
  | numbers {n : Nat} : WhnfShape (.const numN : CTm Tower.Head n)
  | constructorSpine {n : Nat} {k : DeclName} {arity : Nat} (args : List (CTm Tower.Head n)) :
      objectRoles k = .constructor arity → WhnfShape (CTm.appSpine (.const k) args)
  | partialSpine {n : Nat} {c : DeclName} {arity : Nat} {inspect : InspectTree}
      (args : List (CTm Tower.Head n)) : objectRoles c = .computes arity inspect →
      args.length < arity → WhnfShape (CTm.appSpine (.const c) args)

/-- **A weak-head normal form takes no step**: its erasure is a weak-head normal form of the
package. -/
theorem WhnfShape.whnf {n : Nat} {x : CTm Tower.Head n} (shape : WhnfShape x) :
    Whnf objectRules objectRoles x.erase := by
  cases shape with
  | former former =>
      cases former with
      | head h => exact head_whnf objectShape h
      | pi A B => exact pi_whnf objectShape A.erase B.erase
      | sigma A B => exact sigma_whnf objectShape A.erase B.erase
      | id A a b => exact id_whnf objectShape A.erase a.erase b.erase
  | lam A b => exact lam_whnf objectShape b.erase
  | pair a b => exact pair_whnf objectShape a.erase b.erase
  | refl a => exact refl_whnf objectShape a.erase
  | neutral neutral => exact neutral.whnf objectShape
  | numbers => exact inductive_whnf objectShape objectRoles_num
  | constructorSpine args role =>
      rw [CTm.erase_appSpine]
      exact constSpine_whnf objectShape (fun _ _ h => nomatch role.symm.trans h) _
  | partialSpine args role short =>
      rw [CTm.erase_appSpine]
      exact partialSpine_whnf objectShape role (by rw [List.length_map]; exact short)

/-- A weak-head normal form takes no annotated weak-head step. -/
theorem WhnfShape.no_step {n : Nat} {x : CTm Tower.Head n} (shape : WhnfShape x)
    (x' : CTm Tower.Head n) : ¬ CWhStepR objectChurch objectRoles x x' :=
  CWhStepR.not_of_whnf shape.whnf x'

/-- The weak-head normal forms other than neutral terms that a type of each kind has. -/
def TypeKind.Fits {m : Nat} : TypeKind → CTm Tower.Head m → Prop
  | .univ, x => CFormer x ∨ x = .const numN
  | .pi, x => (∃ A b, x = .lam A b) ∨
      (∃ k arity args, objectRoles k = .constructor arity ∧ args.length < arity ∧
        x = CTm.appSpine (.const k) args) ∨
      (∃ c arity inspect args, objectRoles c = .computes arity inspect ∧ args.length < arity ∧
        x = CTm.appSpine (.const c) args)
  | .sigma, x => ∃ a b, x = .pair a b
  | .ident, x => ∃ a, x = .refl a
  | .num, x => x = .const zeroN ∨ ∃ a, x = .app (.const sucN) a
  | .prop, x => (∃ p q, x = .app (.app (.const impN) p) q) ∨
      (∃ type f, x = .app (.const (SetProfile.allName type)) f) ∨
      (∃ type y z, x = .app (.app (.const (SetProfile.eqName type)) y) z)

theorem list_one {α : Type} : ∀ {l : List α}, l.length = 1 → ∃ a, l = [a]
  | [a], _ => ⟨a, rfl⟩

theorem list_two {α : Type} : ∀ {l : List α}, l.length = 2 → ∃ a b, l = [a, b]
  | [a, b], _ => ⟨a, b, rfl⟩

theorem list_three {α : Type} : ∀ {l : List α}, l.length = 3 → ∃ a b c, l = [a, b, c]
  | [a, b, c], _ => ⟨a, b, c, rfl⟩

theorem list_four {α : Type} : ∀ {l : List α}, l.length = 4 → ∃ a b c d, l = [a, b, c, d]
  | [a, b, c, d], _ => ⟨a, b, c, d, rfl⟩

theorem list_five {α : Type} :
    ∀ {l : List α}, l.length = 5 → ∃ a b c d e, l = [a, b, c, d, e]
  | [a, b, c, d, e], _ => ⟨a, b, c, d, e, rfl⟩

theorem list_six {α : Type} :
    ∀ {l : List α}, l.length = 6 → ∃ a b c d e f, l = [a, b, c, d, e, f]
  | [a, b, c, d, e, f], _ => ⟨a, b, c, d, e, f, rfl⟩

variable {n : Nat} {Γ : CCtx Tower.Head n}

/-- **The types of a constant spine whose declared type is `arity` dependent function binders
before a type constant**: a shorter spine is typed only at types a dependent function type is
below, a full one only at types the constant is below, and a longer one not at all. -/
theorem ctorSpine_typed (formed : CCtxFormed objectChurch Γ) {c : DeclName} {D : CTm Tower.Head 0}
    (declared : objectChurch.constantType c = some D) {arity : Nat} {kind : TypeKind} {C : DeclName}
    (hC : ∀ {m : Nat}, kind.Has (CTm.const C : CTm Tower.Head m)) (notPi : kind ≠ .pi)
    (result : afterBinders (isConstTest C) arity D = true)
    (pis : ∀ j, j < arity → afterBinders isPiTest j D = true)
    {args : List (CTm Tower.Head n)} {T : CTm Tower.Head n}
    (typing : CTyped objectChurch Γ (CTm.appSpine (.const c) args) T) :
    (args.length < arity ∧ ∃ A B, CBelow objectChurch Γ (.pi A B) T) ∨
      (args.length = arity ∧ CBelow objectChurch Γ (.const C) T) := by
  have principal : PrincipalType objectChurch Γ (.const c) D.liftClosed :=
    principal_const ConvRules.objectLevels formed declared
  rcases Nat.lt_trichotomy args.length arity with short | same | long
  · obtain ⟨X, pX, hX⟩ := principal_spine objectFormerFacts ConvRules.objectLevels formed
      isPiTest_stable args (k := 0) principal
      (by rw [Nat.zero_add]; exact afterBinders_liftClosed isPiTest_stable (pis _ short))
    obtain ⟨A, B, rfl⟩ := isPiTest_inv hX
    exact .inl ⟨short, A, B, pX typing⟩
  · obtain ⟨X, pX, hX⟩ := principal_spine objectFormerFacts ConvRules.objectLevels formed
      (isConstTest_stable C) args (k := 0) principal
      (by rw [Nat.zero_add, same]; exact afterBinders_liftClosed (isConstTest_stable C) result)
    obtain rfl := isConstTest_inv hX
    exact .inr ⟨same, pX typing⟩
  · exfalso
    obtain ⟨before, x, after, rfl, length⟩ := split_at arity args long
    rw [appSpine_around] at typing
    obtain ⟨S, tS⟩ := typed_appSpine_fun after typing
    obtain ⟨A₁, B₁, tf, _, _⟩ := tS.generation
    obtain ⟨X, pX, hX⟩ := principal_spine objectFormerFacts ConvRules.objectLevels formed
      (isConstTest_stable C) before (k := 0) principal
      (by rw [Nat.zero_add, length]; exact afterBinders_liftClosed (isConstTest_stable C) result)
    obtain rfl := isConstTest_inv hX
    exact below_kind_false formed (pX tf) hC (k' := .pi) ⟨A₁, B₁, rfl⟩ notPi

/-- A computing constant applied to fewer arguments than its arity is typed only at types a
dependent function type is below. -/
theorem partialSpine_typed (formed : CCtxFormed objectChurch Γ) {c : DeclName} {arity : Nat}
    {inspect : InspectTree} (role : objectRoles c = .computes arity inspect)
    {args : List (CTm Tower.Head n)} (short : args.length < arity) {T : CTm Tower.Head n}
    (typing : CTyped objectChurch Γ (CTm.appSpine (.const c) args) T) :
    ∃ A B, CBelow objectChurch Γ (.pi A B) T := by
  obtain ⟨_, D, declared, pis⟩ := computes_declared role
  obtain ⟨X, pX, hX⟩ := principal_spine objectFormerFacts ConvRules.objectLevels formed
    isPiTest_stable args (k := 0) (principal_const ConvRules.objectLevels formed declared)
    (by
      rw [Nat.zero_add]
      exact afterBinders_liftClosed isPiTest_stable
        (afterBinders_isPi_le (Nat.le_sub_one_of_lt short) pis))
  obtain ⟨A, B, rfl⟩ := isPiTest_inv hX
  exact ⟨A, B, pX typing⟩

/-- The declared types of the constructors. -/
theorem declared_zero :
    objectChurch.constantType zeroN = some (liftTm (Package.numT : Tower.Tm 0)) :=
  objectChurch_declared (by decide) (by decide)
theorem declared_suc :
    objectChurch.constantType sucN = some (liftTm (.pi Package.numT Package.numT : Tower.Tm 0)) :=
  objectChurch_declared (by decide) (by decide)
theorem declared_imp : objectChurch.constantType impN = some (liftTm programCodes.impType) :=
  objectChurch_declared (by decide) (by decide)

/-- **The types of weak-head normal forms**: a weak-head normal form typed at `T` has a neutral
erasure, or a type of some kind below `T` of which it is a weak-head normal form. -/
theorem whnfShape_typed (formed : CCtxFormed objectChurch Γ) {x T : CTm Tower.Head n}
    (shape : WhnfShape x) (typing : CTyped objectChurch Γ x T) :
    Neutral objectRoles x.erase ∨
      ∃ (k : TypeKind) (X : CTm Tower.Head n),
        k.Has X ∧ CBelow objectChurch Γ X T ∧ k.Fits x := by
  have typeT := CTyped.isType ConvRules.objectLevels typing formed
  cases shape with
  | former former =>
      cases former with
      | head h =>
          obtain ⟨u, ht, le⟩ := typing.generation
          exact .inr ⟨.univ, .head u, ⟨u, ConvRules.objectLevels.ground_typing ht, rfl⟩,
            CTypeLe.toBelow le typeT, .inl (.head h)⟩
      | pi A B =>
          obtain ⟨_, _, w, _, _, _, _, join, le⟩ := typing.generation
          exact .inr ⟨.univ, .head w, ⟨w, (ConvRules.objectLevels.join_level join).1, rfl⟩,
            CTypeLe.toBelow le typeT, .inl (.pi A B)⟩
      | sigma A B =>
          obtain ⟨_, _, w, _, _, _, _, join, le⟩ := typing.generation
          exact .inr ⟨.univ, .head w, ⟨w, (ConvRules.objectLevels.join_level join).1, rfl⟩,
            CTypeLe.toBelow le typeT, .inl (.sigma A B)⟩
      | id A a b =>
          obtain ⟨u, _, hu, _, _, le⟩ := typing.generation
          exact .inr ⟨.univ, .head u, ⟨u, hu, rfl⟩, CTypeLe.toBelow le typeT,
            .inl (.id A a b)⟩
  | lam A b =>
      obtain ⟨B, _, _, _, _, _, _, _, le⟩ := typing.generation
      exact .inr ⟨.pi, .pi A B, ⟨A, B, rfl⟩, CTypeLe.toBelow le typeT, .inl ⟨A, b, rfl⟩⟩
  | pair a b =>
      obtain ⟨A, B, _, _, _, _, _, le⟩ := typing.generation
      exact .inr ⟨.sigma, .sigma A B, ⟨A, B, rfl⟩, CTypeLe.toBelow le typeT,
        ⟨a, b, rfl⟩⟩
  | refl a =>
      obtain ⟨A, _, le⟩ := typing.generation
      exact .inr ⟨.ident, .id A a a, ⟨A, a, a, rfl⟩, CTypeLe.toBelow le typeT, ⟨a, rfl⟩⟩
  | neutral neutral => exact .inl neutral
  | numbers =>
      exact .inr ⟨.univ, _, ⟨.sort Tower.zero, .sort _, rfl⟩,
        principal_const ConvRules.objectLevels formed declared_num typing, .inr rfl⟩
  | constructorSpine args role =>
      rcases objectRoles_constructor_cases role with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨type, rfl, rfl⟩ | ⟨type, rfl, rfl⟩
      · rcases ctorSpine_typed formed declared_zero (arity := 0) (kind := .num) rfl (by decide)
          (by decide)
          (fun j h => absurd h (Nat.not_lt_zero j)) typing with ⟨short, _⟩ | ⟨length, le⟩
        · exact absurd short (Nat.not_lt_zero _)
        · obtain rfl : args = [] := List.eq_nil_of_length_eq_zero length
          exact .inr ⟨.num, _, rfl, le, .inl rfl⟩
      · rcases ctorSpine_typed formed declared_suc (arity := 1) (kind := .num) rfl (by decide)
          (by decide) (fun j h => afterBinders_isPi_le (k := 0) (Nat.le_of_lt_succ h) (by decide))
          typing with
          ⟨short, A, B, le⟩ | ⟨length, le⟩
        · exact .inr ⟨.pi, .pi A B, ⟨A, B, rfl⟩, le,
            .inr (.inl ⟨_, _, args, role, short, rfl⟩)⟩
        · obtain ⟨a, rfl⟩ := list_one length
          exact .inr ⟨.num, _, rfl, le, .inr ⟨a, rfl⟩⟩
      · rcases ctorSpine_typed formed declared_imp (arity := 2) (kind := .prop) rfl (by decide)
          (by decide) (fun j h => afterBinders_isPi_le (k := 1) (Nat.le_of_lt_succ h) (by decide))
          typing with
          ⟨short, A, B, le⟩ | ⟨length, le⟩
        · exact .inr ⟨.pi, .pi A B, ⟨A, B, rfl⟩, le,
            .inr (.inl ⟨_, _, args, role, short, rfl⟩)⟩
        · obtain ⟨p, q, rfl⟩ := list_two length
          exact .inr ⟨.prop, _, rfl, le, .inl ⟨p, q, rfl⟩⟩
      · rcases ctorSpine_typed formed (objectDecls_allName type) (arity := 1) (kind := .prop) rfl
          (by decide) rfl (fun j h => afterBinders_isPi_le (k := 0) (Nat.le_of_lt_succ h) rfl)
          typing with
          ⟨short, A, B, le⟩ | ⟨length, le⟩
        · exact .inr ⟨.pi, .pi A B, ⟨A, B, rfl⟩, le,
            .inr (.inl ⟨_, _, args, role, short, rfl⟩)⟩
        · obtain ⟨f, rfl⟩ := list_one length
          exact .inr ⟨.prop, _, rfl, le, .inr (.inl ⟨type, f, rfl⟩)⟩
      · rcases ctorSpine_typed formed (objectDecls_eqName type) (arity := 2) (kind := .prop) rfl
          (by decide) rfl (fun j h => afterBinders_isPi_le (k := 1) (Nat.le_of_lt_succ h) rfl)
          typing with
          ⟨short, A, B, le⟩ | ⟨length, le⟩
        · exact .inr ⟨.pi, .pi A B, ⟨A, B, rfl⟩, le,
            .inr (.inl ⟨_, _, args, role, short, rfl⟩)⟩
        · obtain ⟨y, z, rfl⟩ := list_two length
          exact .inr ⟨.prop, _, rfl, le, .inr (.inr ⟨type, y, z, rfl⟩)⟩
  | partialSpine args role short =>
      obtain ⟨A, B, le⟩ := partialSpine_typed formed role short typing
      exact .inr ⟨.pi, .pi A B, ⟨A, B, rfl⟩, le,
        .inr (.inr ⟨_, _, _, args, role, short, rfl⟩)⟩

/-- **Canonical forms**: a weak-head normal form typed at a type of some kind has a neutral
erasure or is a weak-head normal form of that kind. -/
theorem canonical_at (formed : CCtxFormed objectChurch Γ) {x T : CTm Tower.Head n}
    (shape : WhnfShape x) (typing : CTyped objectChurch Γ x T) {kind : TypeKind}
    (hT : kind.Has T) : Neutral objectRoles x.erase ∨ kind.Fits x := by
  rcases whnfShape_typed formed shape typing with neutral | ⟨k, X, hX, le, fits⟩
  · exact .inl neutral
  · by_cases same : k = kind
    · subst same
      exact .inr fits
    · exact (below_kind_false formed le hX hT same).elim

/-- A constant is a weak-head normal form. -/
theorem whnfShape_const (c : DeclName) : WhnfShape (CTm.const c : CTm Tower.Head n) := by
  cases h : objectRoles c with
  | rigid => exact .neutral (Neutral.rigid (c := c) [] h)
  | «inductive» cs =>
      obtain ⟨rfl, -⟩ := objectRoles_inductive h
      exact .numbers
  | constructor arity => exact .constructorSpine (k := c) [] h
  | computes arity inspect => exact .partialSpine (c := c) [] h (computes_declared h).1

end Shapes

/-! ## The object package as an instance of progress -/

section Instance

namespace G

export Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.TypedEquality.Annotated.Progress
  (afterBinders isPiTest isConstTest isIdTest domainTest afterBinders_isPi_le
    ProgressFacts ScrutineeDecl ScrutineeCanonical FitsConst RelevantConst WhnfShape
    typeProgress progress)

end G

theorem head_tail {α : Type} {a b : α} {as bs : List α} (h : a :: as = b :: bs) :
    a = b ∧ as = bs := by
  injection h with ha hb
  exact ⟨ha, hb⟩

section Canonical

variable {n : Nat}

/-- A canonical form of the numbers is zero or a successor. -/
theorem fits_num {x : CTm Tower.Head n} (fits : G.FitsConst objectChurch objectRoles numN x) :
    x = .const zeroN ∨ ∃ a, x = .app (.const sucN) a := by
  obtain ⟨_, _, args, _, role, length, rfl, declared, result⟩ := fits
  rcases objectRoles_constructor_cases role with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨type, rfl, rfl⟩ | ⟨type, rfl, rfl⟩
  · have := declared_zero.symm.trans declared
    cases this
    obtain rfl := List.eq_nil_of_length_eq_zero length
    exact .inl rfl
  · have := declared_suc.symm.trans declared
    cases this
    obtain ⟨a, rfl⟩ := list_one length
    exact .inr ⟨a, rfl⟩
  · have := declared_imp.symm.trans declared
    cases this
    cases result
  · have := (objectDecls_allName type).symm.trans declared
    cases this
    cases result
  · have := (objectDecls_eqName type).symm.trans declared
    cases this
    cases result

/-- A canonical form of the codes is an implication, a quantifier or an equation. -/
theorem fits_prop {x : CTm Tower.Head n} (fits : G.FitsConst objectChurch objectRoles propN x) :
    (∃ p q, x = .app (.app (.const impN) p) q) ∨
      (∃ type f, x = .app (.const (SetProfile.allName type)) f) ∨
        (∃ type y z, x = .app (.app (.const (SetProfile.eqName type)) y) z) := by
  obtain ⟨_, _, _, _, role, length, rfl, declared, result⟩ := fits
  rcases objectRoles_constructor_cases role with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨type, rfl, rfl⟩ | ⟨type, rfl, rfl⟩
  · have := declared_zero.symm.trans declared
    cases this
    cases result
  · have := declared_suc.symm.trans declared
    cases this
    cases result
  · have := declared_imp.symm.trans declared
    cases this
    obtain ⟨p, q, rfl⟩ := list_two length
    exact .inl ⟨p, q, rfl⟩
  · have := (objectDecls_allName type).symm.trans declared
    cases this
    obtain ⟨f, rfl⟩ := list_one length
    exact .inr (.inl ⟨type, f, rfl⟩)
  · have := (objectDecls_eqName type).symm.trans declared
    cases this
    obtain ⟨y, z, rfl⟩ := list_two length
    exact .inr (.inr ⟨type, y, z, rfl⟩)

theorem holds_covered (args : List (CTm Tower.Head n)) (length : args.length = 1)
    (canonical : G.ScrutineeCanonical objectChurch objectRoles
      (.split 0 .constructor fun _ => .leaf) (liftTm programCodes.holdsType) args) :
    ∃ r, objectChurch.computation.step (CTm.appSpine (.const holdsN) args) r := by
  obtain ⟨code, rfl⟩ := list_one length
  obtain ⟨before, x, _, hargs, hlen, scrut⟩ := canonical
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  obtain ⟨rfl, _⟩ := head_tail hargs
  rcases scrut with ⟨C, hdom, fits⟩ | ⟨hid, _⟩
  · obtain rfl := of_decide_eq_true hdom
    rcases fits_prop fits with ⟨p, q, rfl⟩ | ⟨type, f, rfl⟩ | ⟨type, y, z, rfl⟩
    · exact holds_step_imp p q
    · exact holds_step_all type f
    · exact holds_step_eq type y z
  · cases hid

theorem numRec_covered (args : List (CTm Tower.Head n)) (length : args.length = 4)
    (canonical : G.ScrutineeCanonical objectChurch objectRoles
      (.split 3 .constructor fun _ => .leaf) (liftTm Package.numRecType) args) :
    ∃ r, objectChurch.computation.step (CTm.appSpine (.const numRecName) args) r := by
  obtain ⟨P, z, s, q, rfl⟩ := list_four length
  obtain ⟨before, x, after, hargs, hlen, scrut⟩ := canonical
  obtain ⟨b1, b2, b3, rfl⟩ := list_three hlen
  have split : [P, z, s, q] = b1 :: b2 :: b3 :: x :: after := by
    simpa [List.cons_append, List.nil_append] using hargs
  cases split
  rcases scrut with ⟨C, hdom, fits⟩ | ⟨hid, _⟩
  · obtain rfl := of_decide_eq_true hdom
    rcases fits_num fits with rfl | ⟨a, rfl⟩
    · exact numRec_step_zero P z s
    · exact numRec_step_suc P z s a
  · cases hid

theorem add_covered (args : List (CTm Tower.Head n)) (length : args.length = 2)
    (canonical : G.ScrutineeCanonical objectChurch objectRoles
      (.split 1 .constructor fun _ => .leaf) (liftTm addType) args) :
    ∃ r, objectChurch.computation.step (CTm.appSpine (.const addN) args) r := by
  obtain ⟨m, q, rfl⟩ := list_two length
  obtain ⟨before, x, _, hargs, hlen, scrut⟩ := canonical
  obtain ⟨_, rfl⟩ := list_one hlen
  obtain ⟨rfl, h⟩ := head_tail hargs
  obtain ⟨rfl, _⟩ := head_tail h
  rcases scrut with ⟨C, hdom, fits⟩ | ⟨hid, _⟩
  · obtain rfl := of_decide_eq_true hdom
    rcases fits_num fits with rfl | ⟨a, rfl⟩
    · exact add_step_zero m
    · exact add_step_suc m a
  · cases hid

theorem pow_covered (args : List (CTm Tower.Head n)) (length : args.length = 2)
    (canonical : G.ScrutineeCanonical objectChurch objectRoles
      (.split 0 .constructor fun _ => .leaf) (liftTm powType) args) :
    ∃ r, objectChurch.computation.step (CTm.appSpine (.const powN) args) r := by
  obtain ⟨q, X, rfl⟩ := list_two length
  obtain ⟨before, x, _, hargs, hlen, scrut⟩ := canonical
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  obtain ⟨rfl, _⟩ := head_tail hargs
  rcases scrut with ⟨C, hdom, fits⟩ | ⟨hid, _⟩
  · obtain rfl := of_decide_eq_true hdom
    rcases fits_num fits with rfl | ⟨a, rfl⟩
    · exact pow_step_zero X
    · exact pow_step_suc a X
  · cases hid

theorem j_covered (args : List (CTm Tower.Head n)) (length : args.length = 6)
    (canonical : G.ScrutineeCanonical objectChurch objectRoles
      (.split 5 .constructor fun _ => .leaf) (liftTm Package.jType) args) :
    ∃ r, objectChurch.computation.step (CTm.appSpine (.const jName) args) r := by
  obtain ⟨A, x₀, M, d, y, p, rfl⟩ := list_six length
  obtain ⟨before, x, after, hargs, hlen, scrut⟩ := canonical
  obtain ⟨b1, b2, b3, b4, b5, rfl⟩ := list_five hlen
  have split : [A, x₀, M, d, y, p] = b1 :: b2 :: b3 :: b4 :: b5 :: x :: after := by
    simpa [List.cons_append, List.nil_append] using hargs
  cases split
  rcases scrut with ⟨_, hdom, _⟩ | ⟨_, ⟨w, rfl⟩⟩
  · cases hdom
  · exact j_step A x₀ M d y w

theorem iter_covered (args : List (CTm Tower.Head n)) (length : args.length = 6)
    (canonical : G.ScrutineeCanonical objectChurch objectRoles
      (.split 0 .constructor fun _ => .leaf) (liftTm Package.iterType) args) :
    ∃ r, objectChurch.computation.step (CTm.appSpine (.const iterName) args) r := by
  obtain ⟨q, A, P, st, v, e, rfl⟩ := list_six length
  obtain ⟨before, x, _, hargs, hlen, scrut⟩ := canonical
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  obtain ⟨rfl, _⟩ := head_tail hargs
  rcases scrut with ⟨C, hdom, fits⟩ | ⟨hid, _⟩
  · obtain rfl := of_decide_eq_true hdom
    rcases fits_num fits with rfl | ⟨a, rfl⟩
    · exact iter_step_zero A P st v e
    · exact iter_step_suc a A P st v e
  · cases hid

end Canonical

theorem object_constructorShape {k : DeclName} {arity : Nat}
    (role : objectRoles k = .constructor arity) :
    ∃ (D : CTm Tower.Head 0) (C : DeclName), objectChurch.constantType k = some D ∧
      G.afterBinders (G.isConstTest C) arity D = true ∧
      ∀ j, j < arity → G.afterBinders G.isPiTest j D = true := by
  rcases objectRoles_constructor_cases role with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨type, rfl, rfl⟩ | ⟨type, rfl, rfl⟩
  · exact ⟨_, numN, declared_zero, by decide, fun j h => absurd h (Nat.not_lt_zero j)⟩
  · exact ⟨_, numN, declared_suc, by decide,
      fun j h => G.afterBinders_isPi_le (Nat.le_of_lt_succ h) (by decide)⟩
  · exact ⟨_, propN, declared_imp, by decide,
      fun j h => G.afterBinders_isPi_le (Nat.le_sub_one_of_lt h) (by decide)⟩
  · exact ⟨_, propN, objectDecls_allName type, rfl,
      fun j h => G.afterBinders_isPi_le (Nat.le_of_lt_succ h) rfl⟩
  · exact ⟨_, propN, objectDecls_eqName type, rfl,
      fun j h => G.afterBinders_isPi_le (Nat.le_sub_one_of_lt h) rfl⟩

theorem object_declaredComputing {c : DeclName} {arity : Nat} {inspect : InspectTree}
    (role : objectRoles c = .computes arity inspect) :
    ∃ D, objectChurch.constantType c = some D ∧
      (∀ j, j < arity → G.afterBinders G.isPiTest j D = true) ∧
      G.ScrutineeDecl arity inspect D := by
  rcases objectRoles_computes_cases role with rfl | hr
  · rw [objectRoles_holds] at role
    cases role
    exact ⟨_, declared_holds,
      fun j h => G.afterBinders_isPi_le (Nat.le_of_lt_succ h) (by decide),
      Annotated.Progress.ScrutineeDecl.const 0 propN rfl (by decide) (by decide)⟩
  · rcases roles_computes_cases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    · rw [roles_numRec] at hr
      cases hr
      exact ⟨_, declared_numRec,
        fun j h => G.afterBinders_isPi_le (Nat.le_sub_one_of_lt h) (by decide),
        Annotated.Progress.ScrutineeDecl.const 3 numN rfl (by decide) (by decide)⟩
    · rw [roles_add] at hr
      cases hr
      exact ⟨_, declared_add,
        fun j h => G.afterBinders_isPi_le (Nat.le_sub_one_of_lt h) (by decide),
        Annotated.Progress.ScrutineeDecl.const 1 numN rfl (by decide) (by decide)⟩
    · rw [roles_pow] at hr
      cases hr
      exact ⟨_, declared_pow,
        fun j h => G.afterBinders_isPi_le (Nat.le_sub_one_of_lt h) (by decide),
        Annotated.Progress.ScrutineeDecl.const 0 numN rfl (by decide) (by decide)⟩
    · rw [roles_j] at hr
      cases hr
      exact ⟨_, declared_j,
        fun j h => G.afterBinders_isPi_le (Nat.le_sub_one_of_lt h) (by decide),
        Annotated.Progress.ScrutineeDecl.ident 5 rfl (by decide) rfl⟩
    · rw [roles_eqAt] at hr
      cases hr
      exact ⟨_, declared_eqAt,
        fun j h => G.afterBinders_isPi_le (Nat.le_of_lt_succ h) (by decide),
        Annotated.Progress.ScrutineeDecl.leaf rfl⟩
    · rw [roles_sucMove] at hr
      cases hr
      exact ⟨_, declared_sucMove,
        fun j h => G.afterBinders_isPi_le (Nat.le_sub_one_of_lt h) (by decide),
        Annotated.Progress.ScrutineeDecl.leaf rfl⟩
    · rw [roles_keep] at hr
      cases hr
      exact ⟨_, declared_keep,
        fun j h => G.afterBinders_isPi_le (Nat.le_sub_one_of_lt h) (by decide),
        Annotated.Progress.ScrutineeDecl.leaf rfl⟩
    · rw [roles_transport] at hr
      cases hr
      exact ⟨_, declared_transport,
        fun j h => G.afterBinders_isPi_le (Nat.le_sub_one_of_lt h) (by decide),
        Annotated.Progress.ScrutineeDecl.leaf rfl⟩
    · rw [roles_compose] at hr
      cases hr
      exact ⟨_, declared_compose,
        fun j h => G.afterBinders_isPi_le (Nat.le_sub_one_of_lt h) (by decide),
        Annotated.Progress.ScrutineeDecl.leaf rfl⟩
    · rw [roles_iter] at hr
      cases hr
      exact ⟨_, declared_iter,
        fun j h => G.afterBinders_isPi_le (Nat.le_sub_one_of_lt h) (by decide),
        Annotated.Progress.ScrutineeDecl.const 0 numN rfl (by decide) (by decide)⟩
    · rw [roles_returnIter] at hr
      cases hr
      exact ⟨_, declared_returnIter,
        fun j h => G.afterBinders_isPi_le (Nat.le_of_lt_succ h) (by decide),
        Annotated.Progress.ScrutineeDecl.leaf rfl⟩
    · rw [roles_sucStep] at hr
      cases hr
      exact ⟨_, declared_sucStep,
        fun j h => G.afterBinders_isPi_le (Nat.le_sub_one_of_lt h) (by decide),
        Annotated.Progress.ScrutineeDecl.leaf rfl⟩

theorem object_rootCoverage {c : DeclName} {arity : Nat} {inspect : InspectTree}
    {D : CTm Tower.Head 0} (role : objectRoles c = .computes arity inspect)
    (declared : objectChurch.constantType c = some D) {n : Nat}
    (args : List (CTm Tower.Head n)) (length : args.length = arity)
    (canonical : G.ScrutineeCanonical objectChurch objectRoles inspect D args) :
    ∃ r, objectChurch.computation.step (CTm.appSpine (.const c) args) r := by
  rcases objectRoles_computes_cases role with rfl | hr
  · rw [objectRoles_holds] at role
    cases role
    have := declared_holds.symm.trans declared
    cases this
    exact holds_covered args length canonical
  · rcases roles_computes_cases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    · rw [roles_numRec] at hr
      cases hr
      have := declared_numRec.symm.trans declared
      cases this
      exact numRec_covered args length canonical
    · rw [roles_add] at hr
      cases hr
      have := declared_add.symm.trans declared
      cases this
      exact add_covered args length canonical
    · rw [roles_pow] at hr
      cases hr
      have := declared_pow.symm.trans declared
      cases this
      exact pow_covered args length canonical
    · rw [roles_j] at hr
      cases hr
      have := declared_j.symm.trans declared
      cases this
      exact j_covered args length canonical
    · rw [roles_eqAt] at hr
      cases hr
      exact leaf_step (objectRoles_of_roles roles_eqAt nofun) length
    · rw [roles_sucMove] at hr
      cases hr
      exact leaf_step (objectRoles_of_roles roles_sucMove nofun) length
    · rw [roles_keep] at hr
      cases hr
      exact leaf_step (objectRoles_of_roles roles_keep nofun) length
    · rw [roles_transport] at hr
      cases hr
      exact leaf_step (objectRoles_of_roles roles_transport nofun) length
    · rw [roles_compose] at hr
      cases hr
      exact leaf_step (objectRoles_of_roles roles_compose nofun) length
    · rw [roles_iter] at hr
      cases hr
      have := declared_iter.symm.trans declared
      cases this
      exact iter_covered args length canonical
    · rw [roles_returnIter] at hr
      cases hr
      exact leaf_step (objectRoles_of_roles roles_returnIter nofun) length
    · rw [roles_sucStep] at hr
      cases hr
      exact leaf_step (objectRoles_of_roles roles_sucStep nofun) length

/-- The numbers and the codes are the only type constants an inspection or a constructor
names. -/
theorem relevant_num_or_prop {C : DeclName}
    (rel : G.RelevantConst objectChurch objectRoles C) : C = numN ∨ C = propN := by
  rcases rel with ⟨_, role⟩ | ⟨_, _, _, role, declared, result⟩ |
    ⟨_, _, _, _, role, declared, domain⟩
  · obtain ⟨rfl, _⟩ := objectRoles_inductive role
    exact .inl rfl
  · rcases objectRoles_constructor_cases role with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨type, rfl, rfl⟩ | ⟨type, rfl, rfl⟩
    · have := declared_zero.symm.trans declared
      cases this
      have hC := of_decide_eq_true result
      exact .inl hC.symm
    · have := declared_suc.symm.trans declared
      cases this
      have hC := of_decide_eq_true result
      exact .inl hC.symm
    · have := declared_imp.symm.trans declared
      cases this
      have hC := of_decide_eq_true result
      exact .inr hC.symm
    · have := (objectDecls_allName type).symm.trans declared
      cases this
      have hC := of_decide_eq_true result
      exact .inr hC.symm
    · have := (objectDecls_eqName type).symm.trans declared
      cases this
      have hC := of_decide_eq_true result
      exact .inr hC.symm
  · rcases objectRoles_computes_cases role with rfl | hr
    · rw [objectRoles_holds] at role
      cases role
      have := declared_holds.symm.trans declared
      cases this
      have hC := of_decide_eq_true domain
      exact .inr hC.symm
    · rcases roles_computes_cases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl
      · rw [roles_numRec] at hr
        cases hr
        have := declared_numRec.symm.trans declared
        cases this
        have hC := of_decide_eq_true domain
        exact .inl hC.symm
      · rw [roles_add] at hr
        cases hr
        have := declared_add.symm.trans declared
        cases this
        have hC := of_decide_eq_true domain
        exact .inl hC.symm
      · rw [roles_pow] at hr
        cases hr
        have := declared_pow.symm.trans declared
        cases this
        have hC := of_decide_eq_true domain
        exact .inl hC.symm
      · rw [roles_j] at hr
        cases hr
        have := declared_j.symm.trans declared
        cases this
        cases domain
      · rw [roles_eqAt] at hr
        cases hr
      · rw [roles_sucMove] at hr
        cases hr
      · rw [roles_keep] at hr
        cases hr
      · rw [roles_transport] at hr
        cases hr
      · rw [roles_compose] at hr
        cases hr
      · rw [roles_iter] at hr
        cases hr
        have := declared_iter.symm.trans declared
        cases this
        have hC := of_decide_eq_true domain
        exact .inl hC.symm
      · rw [roles_returnIter] at hr
        cases hr
      · rw [roles_sucStep] at hr
        cases hr

theorem inductive_declared {T : DeclName} {ctors : List (DeclName × List CtorField)}
    (role : objectRoles T = .inductive ctors) :
    ∃ u, objectRules.isUniverse u ∧ objectChurch.constantType T = some (.head u) := by
  obtain ⟨rfl, rfl⟩ := objectRoles_inductive role
  exact ⟨.sort Tower.zero, .sort _, declared_num⟩

/-- **The obligations of progress for the object package.** Each field is a fact about one
constant, one role or the type formers. -/
theorem objectProgressFacts : G.ProgressFacts objectChurch objectRoles where
  formers := objectFormerFacts
  constructorShape := object_constructorShape
  declaredComputing := object_declaredComputing
  rootCoverage := object_rootCoverage
  inductiveDeclared := inductive_declared
  formerNeConst := by
    intro C rel n Γ X formed former equal
    rcases relevant_num_or_prop rel with rfl | rfl
    · exact former_ne_const (n := n) (Γ := Γ) (X := X) formed former (c := numN) typeForm_num equal
    · exact former_ne_const (n := n) (Γ := Γ) (X := X) formed former (c := propN) typeForm_prop equal
  constDistinct := by
    intro C C' rel rel' distinct n Γ formed equal
    rcases relevant_num_or_prop rel with rfl | rfl <;>
      rcases relevant_num_or_prop rel' with rfl | rfl
    · exact distinct rfl
    · exact num_ne_prop (n := n) (Γ := Γ) formed equal
    · exact num_ne_prop (n := n) (Γ := Γ) formed equal.symm
    · exact distinct rfl

/-- A generic weak-head normal form is one of the shapes of this package. -/
theorem whnfShape_of_generic {n : Nat} {t : CTm Tower.Head n}
    (shape : G.WhnfShape objectRoles t) : WhnfShape t := by
  cases shape with
  | former former => exact .former former
  | lam A b => exact .lam A b
  | pair a b => exact .pair a b
  | refl a => exact .refl a
  | neutral neutral => exact .neutral neutral
  | inductiveConst role =>
      obtain ⟨rfl, _⟩ := objectRoles_inductive role
      exact .numbers
  | constructorSpine args role => exact .constructorSpine args role
  | partialSpine args role short => exact .partialSpine args role short

end Instance

/-! ## Progress -/

section ProgressTheorem

variable {n : Nat} {Γ : CCtx Tower.Head n}

/-- `t` takes an annotated weak-head step or is a weak-head normal form. -/
def Progresses (t : CTm Tower.Head n) : Prop :=
  (∃ t', CWhStepR objectChurch objectRoles t t') ∨ WhnfShape t

/-- **Progress**: a typed annotated term of the object package, over a formed context, takes
an annotated weak-head step or is a weak-head normal form. -/
theorem objectChurch_progress {t T : CTm Tower.Head n} (formed : CCtxFormed objectChurch Γ)
    (typing : CTyped objectChurch Γ t T) : Progresses t := by
  rcases G.progress objectProgressFacts ConvRules.objectLevels
      (ConvRules.realRules_algebra objectTExt) formed typing with step | shape
  · exact .inl step
  · exact .inr (whnfShape_of_generic shape)

end ProgressTheorem


end Progress

open Progress in
/-- **Progress for annotated types**: a type of a universe, over a formed annotated context of
the object package, takes an annotated weak-head step, or its erasure is in weak-head form. -/
theorem objectChurch_typeProgress {n : Nat} {Γ : CCtx Tower.Head n} {A : CTm Tower.Head n}
    {u : Tower.Head} (formed : CCtxFormed objectChurch Γ) (hu : objectRules.isUniverse u)
    (typing : CTyped objectChurch Γ A (.head u)) :
    (∃ A', CWhStepR objectChurch objectRoles A A') ∨ IsTypeForm objectRoles A.erase :=
  Progress.G.typeProgress Progress.objectProgressFacts ConvRules.objectLevels
    (ConvRules.realRules_algebra objectTExt) formed hu typing

/-- **The facts about the weak-head forms of the object package's types**, given that its types
and equations of types lift to the annotation: the annotated types progress
(`objectChurch_typeProgress`). -/
theorem objectRules_formFacts_given_lifting
    (liftType : ∀ {n : Nat} {Γ : Tower.Ctx n} {A : Tower.Tm n}, CtxFormed objectRules Γ →
      IsType objectRules Γ A → ∃ (Γ' : CCtx Tower.Head n) (A' : CTm Tower.Head n),
        CCtxFormed objectChurch Γ' ∧ Γ'.erase = Γ ∧ A'.erase = A ∧
          CIsType objectChurch Γ' A')
    (liftTypeEq : ∀ {n : Nat} {Γ : Tower.Ctx n} {A B : Tower.Tm n}, CtxFormed objectRules Γ →
      TypeEq objectRules Γ A B → ∃ (Γ' : CCtx Tower.Head n) (A' B' : CTm Tower.Head n),
        CCtxFormed objectChurch Γ' ∧ Γ'.erase = Γ ∧ A'.erase = A ∧ B'.erase = B ∧
          CTypeEq objectChurch Γ' A' B') :
    FormFacts objectRules objectRoles :=
  objectRules_formFacts_of liftType liftTypeEq objectChurch_typeProgress

/-- **The object package's conversion algorithm is complete**, given that its types and
equations of types lift to the annotation. -/
theorem objectRules_algorithmicComplete_given_lifting
    (liftType : ∀ {n : Nat} {Γ : Tower.Ctx n} {A : Tower.Tm n}, CtxFormed objectRules Γ →
      IsType objectRules Γ A → ∃ (Γ' : CCtx Tower.Head n) (A' : CTm Tower.Head n),
        CCtxFormed objectChurch Γ' ∧ Γ'.erase = Γ ∧ A'.erase = A ∧
          CIsType objectChurch Γ' A')
    (liftTypeEq : ∀ {n : Nat} {Γ : Tower.Ctx n} {A B : Tower.Tm n}, CtxFormed objectRules Γ →
      TypeEq objectRules Γ A B → ∃ (Γ' : CCtx Tower.Head n) (A' B' : CTm Tower.Head n),
        CCtxFormed objectChurch Γ' ∧ Γ'.erase = Γ ∧ A'.erase = A ∧ B'.erase = B ∧
          CTypeEq objectChurch Γ' A' B') :
    AlgorithmicComplete objectRules objectRoles :=
  objectRules_algorithmicComplete_of liftType liftTypeEq objectChurch_typeProgress

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
