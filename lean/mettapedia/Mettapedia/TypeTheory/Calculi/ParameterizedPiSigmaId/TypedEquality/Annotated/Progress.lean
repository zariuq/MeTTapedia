import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.FormFacts
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.HeadSteps

/-!
# Progress for annotated types

**Progress** (`typeProgress`): an annotated type of a universe, over a formed context, takes one
annotated weak-head step or erases to a weak-head normal form of a type. The argument is any
annotation `P` of any rule package, with any roles for its constants. What the package
contributes is collected in `ProgressFacts`: local facts about one constant, one role or one
type former, never the progress statement itself.

* **Declared type of a computing constant** (`declaredComputing`). Its declared type has one
  leading dependent function binder for every argument. A constant that inspects an argument
  inspects one constructor form, and the binder at that position has a recognized domain: a
  type constant, or an identity type.
* **Root steps at canonical scrutinees** (`rootCoverage`). A computing constant applied to its
  arity takes a declared root step when it inspects nothing, and when its inspected argument is
  a canonical form of that domain. The step relation used here contracts one such inspection,
  so a deeper inspection skeleton is not a way of discharging the obligation.
* **Canonical forms** (`constructorShape`, `Fits`). A constructor's declared type is its arity
  of dependent function binders followed by a type constant. A full spine of that constructor is
  a canonical form of the constant; a shorter spine is a canonical form of a dependent function
  type, as is an abstraction and a computing constant applied to fewer arguments than its arity.
  A weak-head normal form typed at an identity type is reflexivity or neutral, and one typed at
  a dependent pair type is a pair or neutral.
* **No-confusion through subtyping** (`formerNeConst`, `constDistinct`, together with the
  existing `CFormerFacts`). A type former is equal to no relevant type constant, two distinct
  relevant type constants are not equal, and the subtyping rules send a type only to types of
  the same kind (`below_kind`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Annotated
namespace Progress

open UniverseLevel (LevelOrder)
open Normalization (Roles Role Neutral IsTypeForm InspectTree Inspection Field LevelModel)

variable {Head : Type}

/-! ## Spines and sizes -/

/-- The number of formers of an annotated term. -/
def ctmSize {n : Nat} : CTm Head n → Nat
  | .var _ => 1
  | .const _ => 1
  | .head _ => 1
  | .pi A B => ctmSize A + ctmSize B + 1
  | .sigma A B => ctmSize A + ctmSize B + 1
  | .id A a b => ctmSize A + ctmSize a + ctmSize b + 1
  | .lam A b => ctmSize A + ctmSize b + 1
  | .app f a => ctmSize f + ctmSize a + 1
  | .pair a b => ctmSize a + ctmSize b + 1
  | .fst p => ctmSize p + 1
  | .snd p => ctmSize p + 1
  | .refl a => ctmSize a + 1

theorem appSpine_append {n : Nat} : ∀ (as bs : List (CTm Head n)) (f : CTm Head n),
    CTm.appSpine f (as ++ bs) = CTm.appSpine (CTm.appSpine f as) bs
  | [], _, _ => rfl
  | a :: as, bs, f => appSpine_append as bs (.app f a)

theorem appSpine_snoc {n : Nat} (as : List (CTm Head n)) (f a : CTm Head n) :
    CTm.appSpine f (as ++ [a]) = .app (CTm.appSpine f as) a :=
  appSpine_append as [a] f

theorem appSpine_around {n : Nat} (before after : List (CTm Head n)) (f x : CTm Head n) :
    CTm.appSpine f (before ++ x :: after) = CTm.appSpine (.app (CTm.appSpine f before) x) after :=
  appSpine_append before (x :: after) f

theorem ctmSize_le_appSpine {n : Nat} : ∀ (as : List (CTm Head n)) (f : CTm Head n),
    ctmSize f ≤ ctmSize (CTm.appSpine f as)
  | [], _ => Nat.le_refl _
  | a :: as, f => Nat.le_trans (Nat.le_succ_of_le (Nat.le_add_right (ctmSize f) (ctmSize a)))
      (ctmSize_le_appSpine as (.app f a))

theorem ctmSize_lt_appSpine {n : Nat} :
    ∀ (as : List (CTm Head n)) (f x : CTm Head n), x ∈ as →
      ctmSize x < ctmSize (CTm.appSpine f as)
  | a :: as, f, x, mem => by
      cases mem with
      | head =>
          have here : ctmSize a < ctmSize (CTm.app f a) :=
            Nat.lt_succ_of_le (Nat.le_add_left (ctmSize a) (ctmSize f))
          exact Nat.lt_of_lt_of_le here (ctmSize_le_appSpine as (.app f a))
      | tail _ mem => exact ctmSize_lt_appSpine as (.app f a) x mem

/-- A list longer than `k` splits at position `k`. -/
theorem split_at {α : Type} : ∀ (k : Nat) (as : List α), k < as.length →
    ∃ before x after, as = before ++ x :: after ∧ before.length = k
  | 0, a :: as, _ => ⟨[], a, as, rfl, rfl⟩
  | k + 1, a :: as, h => by
      obtain ⟨before, x, after, rfl, length⟩ := split_at k as (Nat.lt_of_succ_lt_succ h)
      exact ⟨a :: before, x, after, rfl, congrArg (· + 1) length⟩

variable {R : Rules Head} {P : ChurchRules R}

theorem typed_appSpine_fun {n : Nat} {Γ : CCtx Head n} :
    ∀ (as : List (CTm Head n)) {f T : CTm Head n}, CTyped P Γ (CTm.appSpine f as) T →
      ∃ S, CTyped P Γ f S
  | [], _, T, typing => ⟨T, typing⟩
  | a :: as, f, _, typing => by
      obtain ⟨S, tS⟩ := typed_appSpine_fun as (f := .app f a) typing
      obtain ⟨A, B, tf, _, _⟩ := tS.generation
      exact ⟨_, tf⟩

/-! ## Leading dependent function types -/

/-- `afterBinders test k X`: the term `X` has `k` leading dependent function binders, and
what follows them passes `test`. -/
def afterBinders (test : ∀ {m : Nat}, CTm Head m → Bool) : Nat → {n : Nat} → CTm Head n → Bool
  | 0, _, X => test X
  | k + 1, _, .pi _ B => afterBinders test k B
  | _ + 1, _, _ => false

def isPiTest : ∀ {m : Nat}, CTm Head m → Bool
  | _, .pi _ _ => true
  | _, _ => false

def isConstTest (c : DeclName) : ∀ {m : Nat}, CTm Head m → Bool
  | _, .const c' => decide (c' = c)
  | _, _ => false

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
  | _ => exact absurd h Bool.false_ne_true

theorem isPiTest_inv {m : Nat} {X : CTm Head m} (h : isPiTest X = true) : ∃ A B, X = .pi A B := by
  cases X with
  | pi A B => exact ⟨A, B, rfl⟩
  | _ => exact absurd h Bool.false_ne_true

theorem isConstTest_inv {c : DeclName} {m : Nat} {X : CTm Head m} (h : isConstTest c X = true) :
    X = .const c := by
  cases X with
  | const c' => exact congrArg CTm.const (of_decide_eq_true h)
  | _ => exact absurd h Bool.false_ne_true

theorem isIdTest_inv {m : Nat} {X : CTm Head m} (h : isIdTest X = true) :
    ∃ A a b, X = .id A a b := by
  cases X with
  | id A a b => exact ⟨A, a, b, rfl⟩
  | _ => exact absurd h Bool.false_ne_true

theorem domainTest_inv {test : ∀ {m : Nat}, CTm Head m → Bool} {m : Nat} {X : CTm Head m}
    (h : domainTest test X = true) : ∃ A B, X = .pi A B ∧ test A = true := by
  cases X with
  | pi A B => exact ⟨A, B, rfl, h⟩
  | _ => exact absurd h Bool.false_ne_true

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
    {n : Nat} : afterBinders test k (D.liftClosed : CTm Head n) = true :=
  afterBinders_rename stable k Fin.elim0 D h

/-- Fewer leading dependent function binders. -/
theorem afterBinders_isPi_le : ∀ {j k : Nat}, j ≤ k → ∀ {n : Nat} {X : CTm Head n},
    afterBinders isPiTest k X = true → afterBinders isPiTest j X = true
  | 0, 0, _, _, _, h => h
  | 0, _ + 1, _, _, _, h => by
      obtain ⟨_, _, rfl, _⟩ := afterBinders_succ h
      rfl
  | _ + 1, 0, le, _, _, _ => absurd le (Nat.not_succ_le_zero _)
  | j + 1, k + 1, le, _, _, h => by
      obtain ⟨_, B, rfl, hB⟩ := afterBinders_succ h
      exact afterBinders_isPi_le (Nat.le_of_succ_le_succ le) hB

/-! ## Principal types -/

variable {L : Type} [LevelOrder L]

/-- **A principal type** of `f`: a type below every type of `f`. -/
def PrincipalType (P : ChurchRules R) {n : Nat} (Γ : CCtx Head n) (f X : CTm Head n) : Prop :=
  ∀ {T : CTm Head n}, CTyped P Γ f T → CBelow P Γ X T

theorem principal_const (levels : LevelModel R L) {n : Nat} {Γ : CCtx Head n}
    (formed : CCtxFormed P Γ) {c : DeclName} {D : CTm Head 0}
    (declared : P.constantType c = some D) : PrincipalType P Γ (.const c) D.liftClosed := by
  intro T typing
  obtain ⟨type, _, d, _, _, le⟩ := typing.generation
  obtain rfl : D = type := Option.some.inj (declared.symm.trans d)
  exact CTypeLe.toBelow le (CTyped.isType levels typing formed)

variable (facts : CFormerFacts P) (levels : LevelModel R L)
include facts levels

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
      obtain ⟨_, B, rfl, hB⟩ := afterBinders_succ (k := k + as.length) h
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

omit facts levels

/-! ## The obligations -/

variable {roles : Roles Head}

/-- A type constant that a canonical form or an inspection actually mentions: the type
constant of an inductive type, the result of a constructor, or the domain of a computing
constant's inspected argument. -/
def RelevantConst (P : ChurchRules R) (roles : Roles Head) (C : DeclName) : Prop :=
  (∃ ctors, roles C = .inductive ctors) ∨
    (∃ (k : DeclName) (arity : Nat) (D : CTm Head 0), roles k = .constructor arity ∧
      P.constantType k = some D ∧ afterBinders (isConstTest C) arity D = true) ∨
    (∃ (c : DeclName) (arity : Nat) (D : CTm Head 0) (pos : Nat),
      roles c = .computes arity (.split pos .constructor fun _ => .leaf) ∧
      P.constantType c = some D ∧
      afterBinders (domainTest (isConstTest C)) pos D = true)

/-- **A canonical form of a type constant**: a constructor applied to exactly its arity,
whose declared type ends at that constant. -/
def FitsConst (P : ChurchRules R) (roles : Roles Head) (C : DeclName) {n : Nat}
    (x : CTm Head n) : Prop :=
  ∃ (k : DeclName) (arity : Nat) (args : List (CTm Head n)) (D : CTm Head 0),
    roles k = .constructor arity ∧ args.length = arity ∧
      x = CTm.appSpine (.const k) args ∧ P.constantType k = some D ∧
      afterBinders (isConstTest C) arity D = true

/-- **A canonical scrutinee** of a computing constant: nothing, when the constant inspects
nothing; a canonical form of the declared domain, when the constant inspects one argument. -/
def ScrutineeCanonical (P : ChurchRules R) (roles : Roles Head) (inspect : InspectTree)
    (D : CTm Head 0) {n : Nat} (args : List (CTm Head n)) : Prop :=
  match inspect with
  | .leaf => True
  | .split pos .constructor _ =>
      ∃ before x after, args = before ++ x :: after ∧ before.length = pos ∧
        ((∃ C, afterBinders (domainTest (isConstTest C)) pos D = true ∧
            FitsConst P roles C x) ∨
          (afterBinders (domainTest isIdTest) pos D = true ∧ ∃ a, x = .refl a))
  | .split _ .headForm _ => False

/-- How a computing constant's declared type presents the argument it inspects. A single
constructor inspection may end immediately. A deeper skeleton is not a scrutinee of the
annotated step relation. -/
inductive ScrutineeDecl (arity : Nat) (inspect : InspectTree) (D : CTm Head 0) : Prop where
  | leaf : inspect = .leaf → ScrutineeDecl arity inspect D
  | const (pos : Nat) (C : DeclName) : inspect = .split pos .constructor (fun _ => .leaf) →
      pos < arity → afterBinders (domainTest (isConstTest C)) pos D = true →
      ScrutineeDecl arity inspect D
  | ident (pos : Nat) : inspect = .split pos .constructor (fun _ => .leaf) →
      pos < arity → afterBinders (domainTest isIdTest) pos D = true →
      ScrutineeDecl arity inspect D

/-- **The facts progress needs.** Each field is a fact about one constant, one role or the
type formers. None of them is the progress statement. -/
structure ProgressFacts (P : ChurchRules R) (roles : Roles Head) : Prop where
  /-- Injectivity and no-confusion of the type formers. -/
  formers : CFormerFacts P
  /-- A constructor's declared type is its arity of dependent function binders followed by
  the type constant it returns. -/
  constructorShape : ∀ {k : DeclName} {arity : Nat}, roles k = .constructor arity →
    ∃ (D : CTm Head 0) (C : DeclName), P.constantType k = some D ∧
      afterBinders (isConstTest C) arity D = true ∧
      ∀ j, j < arity → afterBinders isPiTest j D = true
  /-- A computing constant's declared type has one dependent function binder per argument,
  and the binder of an inspected argument has a type-constant or identity domain. -/
  declaredComputing : ∀ {c : DeclName} {arity : Nat} {inspect : InspectTree},
    roles c = .computes arity inspect →
    ∃ (D : CTm Head 0), P.constantType c = some D ∧
      (∀ j, j < arity → afterBinders isPiTest j D = true) ∧
      ScrutineeDecl arity inspect D
  /-- A computing constant takes a root step at every canonical scrutinee of its arity. -/
  rootCoverage : ∀ {c : DeclName} {arity : Nat} {inspect : InspectTree} {D : CTm Head 0},
    roles c = .computes arity inspect → P.constantType c = some D →
    ∀ {n : Nat} (args : List (CTm Head n)), args.length = arity →
      ScrutineeCanonical P roles inspect D args →
      ∃ r, P.computation.step (CTm.appSpine (.const c) args) r
  /-- The type constant of an inductive type is declared at a universe. -/
  inductiveDeclared : ∀ {T : DeclName} {ctors : List (DeclName × List (Field Head))},
    roles T = .inductive ctors → ∃ u, R.isUniverse u ∧ P.constantType T = some (.head u)
  /-- A type former is equal to no relevant type constant. -/
  formerNeConst : ∀ {C : DeclName}, RelevantConst P roles C →
    ∀ {n : Nat} {Γ : CCtx Head n} {X : CTm Head n}, CCtxFormed P Γ → CFormer X →
      ¬ CTypeEq P Γ X (.const C)
  /-- Two distinct relevant type constants are not equal. -/
  constDistinct : ∀ {C C' : DeclName}, RelevantConst P roles C → RelevantConst P roles C' →
    C ≠ C' → ∀ {n : Nat} {Γ : CCtx Head n}, CCtxFormed P Γ →
      ¬ CTypeEq P Γ (.const C) (.const C')

theorem relevant_of_result {k : DeclName} {arity : Nat} {D : CTm Head 0} {C : DeclName}
    (role : roles k = .constructor arity) (declared : P.constantType k = some D)
    (result : afterBinders (isConstTest C) arity D = true) : RelevantConst P roles C :=
  .inr (.inl ⟨k, arity, D, role, declared, result⟩)

theorem relevant_of_domain {c : DeclName} {arity : Nat} {D : CTm Head 0} {pos : Nat}
    {C : DeclName}
    (role : roles c = .computes arity (.split pos .constructor fun _ => .leaf))
    (declared : P.constantType c = some D)
    (domain : afterBinders (domainTest (isConstTest C)) pos D = true) : RelevantConst P roles C :=
  .inr (.inr ⟨c, arity, D, pos, role, declared, domain⟩)

theorem relevant_of_inductive {T : DeclName} {ctors : List (DeclName × List (Field Head))}
    (role : roles T = .inductive ctors) : RelevantConst P roles T :=
  .inl ⟨ctors, role⟩

/-- No constant of an all-rigid role assignment is relevant, so the constant obligations hold
vacuously. -/
theorem not_relevant_of_rigid {C : DeclName} (rigid : ∀ name, roles name = .rigid)
    (rel : RelevantConst P roles C) : False := by
  rcases rel with ⟨_, role⟩ | ⟨_, _, _, role, _⟩ | ⟨_, _, _, _, role, _⟩
  · rw [rigid C] at role
    cases role
  · rw [rigid _] at role
    cases role
  · rw [rigid _] at role
    cases role

/-- **Progress for a package whose constants are all rigid**, from the type formers alone.
There is no constructor, no computing constant and no inductive type, so the constant
obligations hold vacuously. -/
theorem ProgressFacts.ofRigid (formers : CFormerFacts P) (rigid : ∀ name, roles name = .rigid) :
    ProgressFacts P roles where
  formers := formers
  constructorShape := fun role => by
    rw [rigid _] at role
    cases role
  declaredComputing := fun role => by
    rw [rigid _] at role
    cases role
  rootCoverage := fun role => by
    rw [rigid _] at role
    cases role
  inductiveDeclared := fun role => by
    rw [rigid _] at role
    cases role
  formerNeConst := fun rel => (not_relevant_of_rigid rigid rel).elim
  constDistinct := fun rel => (not_relevant_of_rigid rigid rel).elim

/-! ## Kinds of types in weak-head form -/

/-- The kinds canonical forms tell apart: the four type formers, and one type constant. -/
inductive SortKey where
  | univ
  | pi
  | sigma
  | ident
  | const (name : DeclName)
  deriving DecidableEq

/-- The kinds whose types are type formers. -/
inductive SortKey.Calc : SortKey → Prop where
  | univ : SortKey.Calc .univ
  | pi : SortKey.Calc .pi
  | sigma : SortKey.Calc .sigma
  | ident : SortKey.Calc .ident

def SortKey.tag : SortKey → Nat
  | .univ => 0
  | .pi => 1
  | .sigma => 2
  | .ident => 3
  | .const _ => 4

def formerTag {m : Nat} : CTm Head m → Nat
  | .head _ => 0
  | .pi _ _ => 1
  | .sigma _ _ => 2
  | .id _ _ _ => 3
  | _ => 4

/-- `X` is a type of the kind. -/
def SortKey.Has (R : Rules Head) {m : Nat} : SortKey → CTm Head m → Prop
  | .univ, X => ∃ w, R.isUniverse w ∧ X = .head w
  | .pi, X => ∃ A B, X = .pi A B
  | .sigma, X => ∃ A B, X = .sigma A B
  | .ident, X => ∃ A a b, X = .id A a b
  | .const C, X => X = .const C

/-- A weak-head normal form of the kind, other than a neutral term. -/
def SortKey.Fits (P : ChurchRules R) (roles : Roles Head) {m : Nat} :
    SortKey → CTm Head m → Prop
  | .univ, x => CFormer x ∨ ∃ T ctors, roles T = .inductive ctors ∧ x = .const T
  | .pi, x => (∃ A b, x = .lam A b) ∨
      (∃ k arity args, roles k = .constructor arity ∧ args.length < arity ∧
        x = CTm.appSpine (.const k) args) ∨
      (∃ c arity inspect args, roles c = .computes arity inspect ∧ args.length < arity ∧
        x = CTm.appSpine (.const c) args)
  | .sigma, x => ∃ a b, x = .pair a b
  | .ident, x => ∃ a, x = .refl a
  | .const C, x => FitsConst P roles C x

theorem SortKey.Has.cformer {k : SortKey} (kCalc : k.Calc) {m : Nat} {X : CTm Head m}
    (has : k.Has R X) : CFormer X := by
  cases kCalc with
  | univ =>
      obtain ⟨_, _, rfl⟩ := has
      exact .head _
  | pi =>
      obtain ⟨_, _, rfl⟩ := has
      exact .pi _ _
  | sigma =>
      obtain ⟨_, _, rfl⟩ := has
      exact .sigma _ _
  | ident =>
      obtain ⟨_, _, _, rfl⟩ := has
      exact .id _ _ _

theorem SortKey.Has.tag_eq {k : SortKey} (kCalc : k.Calc) {m : Nat} {X : CTm Head m}
    (has : k.Has R X) : formerTag X = k.tag := by
  cases kCalc with
  | univ =>
      obtain ⟨_, _, rfl⟩ := has
      rfl
  | pi =>
      obtain ⟨_, _, rfl⟩ := has
      rfl
  | sigma =>
      obtain ⟨_, _, rfl⟩ := has
      rfl
  | ident =>
      obtain ⟨_, _, _, rfl⟩ := has
      rfl

theorem CFormersMatch.tag_eq {P : ChurchRules R} {m : Nat} {Δ : CCtx Head m} {X Y : CTm Head m}
    (matching : CFormersMatch P Δ X Y) : formerTag X = formerTag Y := by
  rcases matching with ⟨_, _, rfl, rfl, _⟩ | ⟨_, _, _, _, rfl, rfl, _⟩ |
    ⟨_, _, _, _, rfl, rfl, _⟩ | ⟨_, _, _, _, _, _, rfl, rfl, _⟩ <;> rfl

theorem SortKey.tag_inj {k k' : SortKey} (kCalc : k.Calc) (kCalc' : k'.Calc) (same : k.tag = k'.tag) :
    k = k' := by
  cases kCalc <;> cases kCalc' <;> first | rfl | exact absurd same (by decide)

/-- A relevant type constant is usable only at types equal to it. -/
theorem below_const (pack : ProgressFacts P roles) (levels : LevelModel R L)
    {n : Nat} {Γ : CCtx Head n} {X T : CTm Head n} {C : DeclName}
    (le : CBelow P Γ X T) (formed : CCtxFormed P Γ) (rel : RelevantConst P roles C)
    (eX : CTypeEq P Γ X (.const C)) : CTypeEq P Γ T (.const C) := by
  refine CBelow.induction (motive := fun m Δ X T => CCtxFormed P Δ →
      CTypeEq P Δ X (.const C) → CTypeEq P Δ T (.const C))
    ?equal ?univ ?pi ?sigma ?trans le formed eX
  case equal =>
    intro m Δ X T u e hu _ eX
    exact CTypeEq.trans levels (CTypeEq.symm ⟨u, hu, e⟩) eX
  case univ =>
    intro m Δ u v _ formed eX
    exact (pack.formerNeConst rel formed (.head u) eX).elim
  case pi =>
    intro m Δ A A' B B' _ _ _ _ _ _ _ _ _ _ _ formed eX
    exact (pack.formerNeConst rel formed (.pi A B) eX).elim
  case sigma =>
    intro m Δ A A' B B' _ _ _ _ _ _ _ _ _ _ formed eX
    exact (pack.formerNeConst rel formed (.sigma A B) eX).elim
  case trans =>
    intro m Δ X Y T _ _ ih₁ ih₂ formed eX
    exact ih₂ formed (ih₁ formed eX)

theorem calc_distinct (pack : ProgressFacts P roles)
    {n : Nat} {Γ : CCtx Head n} {k k' : SortKey} {X Y : CTm Head n}
    (calcK : k.Calc) (calcK' : k'.Calc) (formed : CCtxFormed P Γ) (hX : k.Has R X) (hY : k'.Has R Y)
    (distinct : k ≠ k') (equal : CTypeEq P Γ X Y) : False := by
  have tags := CFormersMatch.tag_eq
    (pack.formers.forms equal formed (hX.cformer calcK) (hY.cformer calcK'))
  rw [hX.tag_eq calcK, hY.tag_eq calcK'] at tags
  exact distinct (SortKey.tag_inj calcK calcK' tags)

/-- **A type of one kind is equal to no type of another kind.** -/
theorem kind_distinct (pack : ProgressFacts P roles)
    {n : Nat} {Γ : CCtx Head n} {k k' : SortKey} {X Y : CTm Head n}
    (formed : CCtxFormed P Γ) (hX : k.Has R X) (hY : k'.Has R Y) (distinct : k ≠ k')
    (equal : CTypeEq P Γ X Y)
    (relX : ∀ C, k = .const C → RelevantConst P roles C)
    (relY : ∀ C, k' = .const C → RelevantConst P roles C) : False := by
  cases k with
  | const C =>
      have relC := relX C rfl
      obtain rfl : X = .const C := hX
      cases k' with
      | const C' =>
          have relC' := relY C' rfl
          obtain rfl : Y = .const C' := hY
          by_cases same : C = C'
          · exact distinct (congrArg SortKey.const same)
          · exact pack.constDistinct relC relC' same formed equal
      | univ =>
          obtain ⟨_, _, rfl⟩ := hY
          exact pack.formerNeConst relC formed (.head _) equal.symm
      | pi =>
          obtain ⟨_, _, rfl⟩ := hY
          exact pack.formerNeConst relC formed (.pi _ _) equal.symm
      | sigma =>
          obtain ⟨_, _, rfl⟩ := hY
          exact pack.formerNeConst relC formed (.sigma _ _) equal.symm
      | ident =>
          obtain ⟨_, _, _, rfl⟩ := hY
          exact pack.formerNeConst relC formed (.id _ _ _) equal.symm
  | univ =>
      cases k' with
      | const C =>
          obtain rfl : Y = .const C := hY
          exact pack.formerNeConst (relY C rfl) formed (hX.cformer .univ) equal
      | univ => exact calc_distinct pack .univ .univ formed hX hY distinct equal
      | pi => exact calc_distinct pack .univ .pi formed hX hY distinct equal
      | sigma => exact calc_distinct pack .univ .sigma formed hX hY distinct equal
      | ident => exact calc_distinct pack .univ .ident formed hX hY distinct equal
  | pi =>
      cases k' with
      | const C =>
          obtain rfl : Y = .const C := hY
          exact pack.formerNeConst (relY C rfl) formed (hX.cformer .pi) equal
      | univ => exact calc_distinct pack .pi .univ formed hX hY distinct equal
      | pi => exact calc_distinct pack .pi .pi formed hX hY distinct equal
      | sigma => exact calc_distinct pack .pi .sigma formed hX hY distinct equal
      | ident => exact calc_distinct pack .pi .ident formed hX hY distinct equal
  | sigma =>
      cases k' with
      | const C =>
          obtain rfl : Y = .const C := hY
          exact pack.formerNeConst (relY C rfl) formed (hX.cformer .sigma) equal
      | univ => exact calc_distinct pack .sigma .univ formed hX hY distinct equal
      | pi => exact calc_distinct pack .sigma .pi formed hX hY distinct equal
      | sigma => exact calc_distinct pack .sigma .sigma formed hX hY distinct equal
      | ident => exact calc_distinct pack .sigma .ident formed hX hY distinct equal
  | ident =>
      cases k' with
      | const C =>
          obtain rfl : Y = .const C := hY
          exact pack.formerNeConst (relY C rfl) formed (hX.cformer .ident) equal
      | univ => exact calc_distinct pack .ident .univ formed hX hY distinct equal
      | pi => exact calc_distinct pack .ident .pi formed hX hY distinct equal
      | sigma => exact calc_distinct pack .ident .sigma formed hX hY distinct equal
      | ident => exact calc_distinct pack .ident .ident formed hX hY distinct equal

/-- **A type of a kind is usable only at types equal to one of that kind.** -/
theorem below_kind (pack : ProgressFacts P roles) (levels : LevelModel R L)
    (algebra : Normalization.CumulativeAlgebra R)
    {n : Nat} {Γ : CCtx Head n} {X T : CTm Head n} (le : CBelow P Γ X T)
    (formed : CCtxFormed P Γ) {k : SortKey} (hX : k.Has R X)
    (rel : ∀ C, k = .const C → RelevantConst P roles C) :
    ∃ Y, k.Has R Y ∧ CTypeEq P Γ T Y := by
  have typeX : CIsType P Γ X := (CBelow.isTypes levels le formed).1
  cases k with
  | univ =>
      obtain ⟨w, hw, rfl⟩ := hX
      obtain ⟨v, hv, e, _⟩ := CBelow.universe_cumulative pack.formers levels algebra le formed hw
        (CIsType.refl typeX)
      exact ⟨.head v, ⟨v, hv, rfl⟩, e⟩
  | pi =>
      obtain ⟨A, B, rfl⟩ := hX
      obtain ⟨A', B', e, _, _⟩ := CBelow.pi_source pack.formers levels le formed
        (CIsType.refl typeX)
      exact ⟨.pi A' B', ⟨A', B', rfl⟩, e⟩
  | sigma =>
      obtain ⟨A, B, rfl⟩ := hX
      obtain ⟨A', B', e, _, _⟩ := CBelow.sigma_source pack.formers levels le formed
        (CIsType.refl typeX)
      exact ⟨.sigma A' B', ⟨A', B', rfl⟩, e⟩
  | ident =>
      obtain ⟨A, a, b, rfl⟩ := hX
      exact ⟨.id A a b, ⟨A, a, b, rfl⟩,
        CBelow.id_eq pack.formers levels le formed (CIsType.refl typeX)⟩
  | const C =>
      obtain rfl : X = .const C := hX
      exact ⟨.const C, rfl, below_const pack levels le formed (rel C rfl) (CIsType.refl typeX)⟩

/-- **A type of one kind is usable at no type of another kind.** -/
theorem below_kind_false (pack : ProgressFacts P roles) (levels : LevelModel R L)
    (algebra : Normalization.CumulativeAlgebra R)
    {n : Nat} {Γ : CCtx Head n} {X T : CTm Head n} (formed : CCtxFormed P Γ)
    (le : CBelow P Γ X T) {k k' : SortKey} (hX : k.Has R X) (hT : k'.Has R T)
    (distinct : k ≠ k')
    (relX : ∀ C, k = .const C → RelevantConst P roles C)
    (relT : ∀ C, k' = .const C → RelevantConst P roles C) : False := by
  obtain ⟨Y, hY, e⟩ := below_kind pack levels algebra le formed hX relX
  exact kind_distinct pack formed hT hY (Ne.symm distinct) e relT relX

/-- The argument at a position whose declared domain is the constant `C` is typed at `C`. -/
theorem argument_const (pack : ProgressFacts P roles) (levels : LevelModel R L)
    {n : Nat} {Γ : CCtx Head n} (formed : CCtxFormed P Γ) {c : DeclName}
    {D : CTm Head 0} (declared : P.constantType c = some D) {C : DeclName}
    {before after : List (CTm Head n)} {x T : CTm Head n}
    (h : afterBinders (domainTest (isConstTest C)) before.length D = true)
    (typing : CTyped P Γ (CTm.appSpine (.const c) (before ++ x :: after)) T) :
    CTyped P Γ x (.const C) := by
  obtain ⟨A, hA, tx⟩ := argument_typed pack.formers levels formed (isConstTest_stable C)
    (principal_const levels formed declared)
    (afterBinders_liftClosed (domainTest_stable (isConstTest_stable C)) h) typing
  obtain rfl := isConstTest_inv hA
  exact tx

/-- **The types of a constant spine whose declared type ends at a type constant**: a shorter
spine is typed only below a dependent function type, and a full one only below that constant.
A longer spine is typed at nothing. -/
theorem ctorSpine_typed (pack : ProgressFacts P roles) (levels : LevelModel R L)
    (algebra : Normalization.CumulativeAlgebra R)
    {n : Nat} {Γ : CCtx Head n} (formed : CCtxFormed P Γ) {c : DeclName}
    {D : CTm Head 0} (declared : P.constantType c = some D) {arity : Nat} {C : DeclName}
    (result : afterBinders (isConstTest C) arity D = true)
    (pis : ∀ j, j < arity → afterBinders isPiTest j D = true)
    (rel : RelevantConst P roles C) {args : List (CTm Head n)} {T : CTm Head n}
    (typing : CTyped P Γ (CTm.appSpine (.const c) args) T) :
    (args.length < arity ∧ ∃ A B, CBelow P Γ (.pi A B) T) ∨
      (args.length = arity ∧ CBelow P Γ (.const C) T) := by
  have principal : PrincipalType P Γ (.const c) D.liftClosed :=
    principal_const levels formed declared
  rcases Nat.lt_trichotomy args.length arity with short | same | long
  · obtain ⟨X, pX, hX⟩ := principal_spine pack.formers levels formed isPiTest_stable args (k := 0)
      principal (by rw [Nat.zero_add]; exact afterBinders_liftClosed isPiTest_stable (pis _ short))
    obtain ⟨A, B, rfl⟩ := isPiTest_inv hX
    exact .inl ⟨short, A, B, pX typing⟩
  · obtain ⟨X, pX, hX⟩ := principal_spine pack.formers levels formed (isConstTest_stable C) args
      (k := 0) principal
      (by rw [Nat.zero_add, same]; exact afterBinders_liftClosed (isConstTest_stable C) result)
    obtain rfl := isConstTest_inv hX
    exact .inr ⟨same, pX typing⟩
  · exfalso
    obtain ⟨before, x, after, rfl, length⟩ := split_at arity args long
    rw [appSpine_around] at typing
    obtain ⟨S, tS⟩ := typed_appSpine_fun after typing
    obtain ⟨A₁, B₁, tf, _, _⟩ := tS.generation
    obtain ⟨X, pX, hX⟩ := principal_spine pack.formers levels formed (isConstTest_stable C) before
      (k := 0) principal
      (by rw [Nat.zero_add, length]; exact afterBinders_liftClosed (isConstTest_stable C) result)
    obtain rfl := isConstTest_inv hX
    exact below_kind_false pack levels algebra formed (pX tf) (k := .const C) rfl (k' := .pi)
      ⟨A₁, B₁, rfl⟩ (by intro h; cases h) (fun C' h => by cases h; exact rel)
      (fun C' h => by cases h)

/-- A computing constant applied to fewer arguments than its arity is typed only below a
dependent function type. -/
theorem partial_typed (pack : ProgressFacts P roles) (levels : LevelModel R L)
    {n : Nat} {Γ : CCtx Head n} (formed : CCtxFormed P Γ) {c : DeclName}
    {arity : Nat} {inspect : InspectTree} (role : roles c = .computes arity inspect)
    {args : List (CTm Head n)} (short : args.length < arity) {T : CTm Head n}
    (typing : CTyped P Γ (CTm.appSpine (.const c) args) T) :
    ∃ A B, CBelow P Γ (.pi A B) T := by
  obtain ⟨D, declared, pis, _⟩ := pack.declaredComputing role
  obtain ⟨X, pX, hX⟩ := principal_spine pack.formers levels formed isPiTest_stable args (k := 0)
    (principal_const levels formed declared)
    (by rw [Nat.zero_add]; exact afterBinders_liftClosed isPiTest_stable (pis _ short))
  obtain ⟨A, B, rfl⟩ := isPiTest_inv hX
  exact ⟨A, B, pX typing⟩

/-! ## Weak-head normal forms -/

/-- **The weak-head normal forms of typed terms**, by shape: a type former, an abstraction, a
pair, reflexivity, a term with a neutral erasure, the type constant of an inductive type, a
constructor spine, or a computing constant applied to fewer arguments than its arity. -/
inductive WhnfShape (roles : Roles Head) : {n : Nat} → CTm Head n → Prop where
  | former {n : Nat} {t : CTm Head n} : CFormer t → WhnfShape roles t
  | lam {n : Nat} (A : CTm Head n) (b : CTm Head (n + 1)) : WhnfShape roles (.lam A b)
  | pair {n : Nat} (a b : CTm Head n) : WhnfShape roles (.pair a b)
  | refl {n : Nat} (a : CTm Head n) : WhnfShape roles (.refl a)
  | neutral {n : Nat} {t : CTm Head n} : Neutral roles t.erase → WhnfShape roles t
  | inductiveConst {n : Nat} {T : DeclName} {ctors : List (DeclName × List (Field Head))} :
      roles T = .inductive ctors → WhnfShape roles (.const T)
  | constructorSpine {n : Nat} {k : DeclName} {arity : Nat} (args : List (CTm Head n)) :
      roles k = .constructor arity → WhnfShape roles (CTm.appSpine (.const k) args)
  | partialSpine {n : Nat} {c : DeclName} {arity : Nat} {inspect : InspectTree}
      (args : List (CTm Head n)) : roles c = .computes arity inspect →
      args.length < arity → WhnfShape roles (CTm.appSpine (.const c) args)

/-- What a weak-head normal form contributes to canonical forms: a neutral erasure, or a kind,
a type of that kind below the term's type, a canonical form of the kind, and the relevance of
a type constant when the kind is one. -/
def Classified (P : ChurchRules R) (roles : Roles Head) {n : Nat} (Γ : CCtx Head n)
    (x T : CTm Head n) : Prop :=
  Neutral roles x.erase ∨ ∃ (k : SortKey) (X : CTm Head n), k.Has R X ∧ CBelow P Γ X T ∧
    k.Fits P roles x ∧ ∀ C, k = .const C → RelevantConst P roles C

theorem neutral_typeForm {n : Nat} {t : Tm Head n} (neutral : Neutral roles t) :
    IsTypeForm roles t :=
  .inr (.inr (.inr (.inr (.inl neutral))))

theorem inductive_typeForm {n : Nat} {T : DeclName} {ctors : List (DeclName × List (Field Head))}
    (role : roles T = .inductive ctors) : IsTypeForm roles (.const T : Tm Head n) :=
  .inr (.inr (.inr (.inr (.inr ⟨T, ctors, role, rfl⟩))))

/-- **The types of weak-head normal forms.** -/
theorem whnf_classified (pack : ProgressFacts P roles) (levels : LevelModel R L)
    (algebra : Normalization.CumulativeAlgebra R)
    {n : Nat} {Γ : CCtx Head n} (formed : CCtxFormed P Γ)
    {x T : CTm Head n} (shape : WhnfShape roles x) (typing : CTyped P Γ x T) :
    Classified P roles Γ x T := by
  have typeT := CTyped.isType levels typing formed
  cases shape with
  | former former =>
      cases former with
      | head h =>
          obtain ⟨u, ht, le⟩ := typing.generation
          exact .inr ⟨.univ, .head u, ⟨u, levels.ground_typing ht, rfl⟩, CTypeLe.toBelow le typeT,
            .inl (.head h), fun _ h => by cases h⟩
      | pi A B =>
          obtain ⟨_, _, w, _, _, _, _, join, le⟩ := typing.generation
          exact .inr ⟨.univ, .head w, ⟨w, (levels.join_level join).1, rfl⟩,
            CTypeLe.toBelow le typeT, .inl (.pi A B), fun _ h => by cases h⟩
      | sigma A B =>
          obtain ⟨_, _, w, _, _, _, _, join, le⟩ := typing.generation
          exact .inr ⟨.univ, .head w, ⟨w, (levels.join_level join).1, rfl⟩,
            CTypeLe.toBelow le typeT, .inl (.sigma A B), fun _ h => by cases h⟩
      | id A a b =>
          obtain ⟨u, _, hu, _, _, le⟩ := typing.generation
          exact .inr ⟨.univ, .head u, ⟨u, hu, rfl⟩, CTypeLe.toBelow le typeT,
            .inl (.id A a b), fun _ h => by cases h⟩
  | lam A b =>
      obtain ⟨B, _, _, _, _, _, _, _, le⟩ := typing.generation
      exact .inr ⟨.pi, .pi A B, ⟨A, B, rfl⟩, CTypeLe.toBelow le typeT, .inl ⟨A, b, rfl⟩,
        fun _ h => by cases h⟩
  | pair a b =>
      obtain ⟨A, B, _, _, _, _, _, le⟩ := typing.generation
      exact .inr ⟨.sigma, .sigma A B, ⟨A, B, rfl⟩, CTypeLe.toBelow le typeT, ⟨a, b, rfl⟩,
        fun _ h => by cases h⟩
  | refl a =>
      obtain ⟨A, _, le⟩ := typing.generation
      exact .inr ⟨.ident, .id A a a, ⟨A, a, a, rfl⟩, CTypeLe.toBelow le typeT, ⟨a, rfl⟩,
        fun _ h => by cases h⟩
  | neutral neutral => exact .inl neutral
  | inductiveConst role =>
      obtain ⟨u, hu, declared⟩ := pack.inductiveDeclared role
      exact .inr ⟨.univ, .head u, ⟨u, hu, rfl⟩,
        principal_const levels formed declared typing, .inr ⟨_, _, role, rfl⟩,
        fun _ h => by cases h⟩
  | constructorSpine args role =>
      obtain ⟨D, C, declared, result, pis⟩ := pack.constructorShape role
      have rel := relevant_of_result role declared result
      rcases ctorSpine_typed pack levels algebra formed declared result pis rel typing with
        ⟨short, A, B, le⟩ | ⟨hlen, le⟩
      · exact .inr ⟨.pi, .pi A B, ⟨A, B, rfl⟩, le,
          .inr (.inl ⟨_, _, args, role, short, rfl⟩), fun _ h => by cases h⟩
      · exact .inr ⟨.const C, .const C, rfl, le,
          ⟨_, _, args, D, role, hlen, rfl, declared, result⟩, fun _ h => by cases h; exact rel⟩
  | partialSpine args role short =>
      obtain ⟨A, B, le⟩ := partial_typed pack levels formed role short typing
      exact .inr ⟨.pi, .pi A B, ⟨A, B, rfl⟩, le,
        .inr (.inr ⟨_, _, _, args, role, short, rfl⟩), fun _ h => by cases h⟩

/-- **Canonical forms**: a weak-head normal form typed at a type of some kind has a neutral
erasure or is a weak-head normal form of that kind. -/
theorem canonical_at (pack : ProgressFacts P roles) (levels : LevelModel R L)
    (algebra : Normalization.CumulativeAlgebra R)
    {n : Nat} {Γ : CCtx Head n} (formed : CCtxFormed P Γ) {x T : CTm Head n}
    (shape : WhnfShape roles x) (typing : CTyped P Γ x T) {k : SortKey} (hT : k.Has R T)
    (relT : ∀ C, k = .const C → RelevantConst P roles C) :
    Neutral roles x.erase ∨ k.Fits P roles x := by
  rcases whnf_classified pack levels algebra formed shape typing with neutral | ⟨k', X, hX, le, fits, relX⟩
  · exact .inl neutral
  · by_cases same : k' = k
    · subst same
      exact .inr fits
    · exact (below_kind_false pack levels algebra formed le hX hT same relX relT).elim

/-! ## Progress -/

variable {n : Nat}

/-- `t` takes an annotated weak-head step or is a weak-head normal form. -/
def Progresses (P : ChurchRules R) (roles : Roles Head) (t : CTm Head n) : Prop :=
  (∃ t', CWhStepR P roles t t') ∨ WhnfShape roles t

/-- **A computing constant that inspects one argument, applied to exactly its arity**: it steps
at the argument when that steps, is stuck on it when it is neutral, and takes a root step when
the argument is a canonical form of its type. -/
theorem exact_split (pack : ProgressFacts P roles) (levels : LevelModel R L)
    (algebra : Normalization.CumulativeAlgebra R)
    {Γ : CCtx Head n} (formed : CCtxFormed P Γ) {c : DeclName} {arity : Nat}
    {before after : List (CTm Head n)} {x : CTm Head n}
    (role : roles c = .computes arity (.split before.length .constructor fun _ => .leaf))
    (length : before.length + 1 + after.length = arity) {k : SortKey} {S : CTm Head n}
    (hS : k.Has R S) (relS : ∀ C, k = .const C → RelevantConst P roles C)
    (tx : CTyped P Γ x S) (progress : Progresses P roles x)
    (fire : k.Fits P roles x →
      ∃ r, P.computation.step (CTm.appSpine (.const c) (before ++ x :: after)) r) :
    Progresses P roles (CTm.appSpine (.const c) (before ++ x :: after)) := by
  rcases progress with ⟨x', step⟩ | shape
  · exact .inl ⟨_, .scrutinee role length step⟩
  · rcases canonical_at pack levels algebra formed shape tx hS relS with neutral | fits
    · refine .inr (.neutral ?_)
      rw [CTm.erase_appSpine, List.map_append, List.map_cons]
      exact Neutral.stuck_single (before := before.map CTm.erase)
        (by rw [List.length_map]; exact role)
        (by rw [List.length_map, List.length_map]; exact length) neutral
    · obtain ⟨r, step⟩ := fire fits
      exact .inl ⟨r, .root step⟩

/-- **Progress at a computing constant applied to exactly its arity**, from the declared type,
the canonical forms of the inspected domain and a root step at each of them. -/
theorem exact_spine (pack : ProgressFacts P roles) (levels : LevelModel R L)
    (algebra : Normalization.CumulativeAlgebra R)
    {Γ : CCtx Head n} (formed : CCtxFormed P Γ) {c : DeclName} {arity : Nat}
    {inspect : InspectTree} (role : roles c = .computes arity inspect)
    {args : List (CTm Head n)} (length : args.length = arity) {T : CTm Head n}
    (typing : CTyped P Γ (CTm.appSpine (.const c) args) T)
    (ih : ∀ x ∈ args, ∀ {S : CTm Head n}, CTyped P Γ x S → Progresses P roles x) :
    Progresses P roles (CTm.appSpine (.const c) args) := by
  obtain ⟨D, declared, _, shape⟩ := pack.declaredComputing role
  cases shape with
  | leaf hleaf =>
      subst hleaf
      obtain ⟨r, step⟩ := pack.rootCoverage role declared args length True.intro
      exact .inl ⟨r, .root step⟩
  | const pos C hsplit hpos hdom =>
      subst hsplit
      obtain ⟨before, x, after, rfl, hlen⟩ := split_at pos args (by omega)
      have hdom' : afterBinders (domainTest (isConstTest C)) before.length D = true := by
        rw [hlen]; exact hdom
      have tx := argument_const pack levels formed declared hdom' typing
      have rel : RelevantConst P roles C := relevant_of_domain role declared hdom
      refine exact_split pack levels algebra formed (before := before) (after := after)
        (by rw [hlen]; exact role)
        (by rw [← length, List.length_append, List.length_cons]; omega) (k := .const C) rfl
        (fun _ h => by cases h; exact rel) tx
        (ih x (List.mem_append_right before (List.Mem.head after)) tx) ?_
      intro fits
      exact pack.rootCoverage role declared (before ++ x :: after) length
        ⟨before, x, after, rfl, hlen, .inl ⟨C, hdom, fits⟩⟩
  | ident pos hsplit hpos hdom =>
      subst hsplit
      obtain ⟨before, x, after, rfl, hlen⟩ := split_at pos args (by omega)
      have hdom' : afterBinders (domainTest isIdTest) before.length D = true := by
        rw [hlen]; exact hdom
      obtain ⟨A, hA, tx⟩ := argument_typed pack.formers levels formed isIdTest_stable
        (principal_const levels formed declared)
        (before := before) (after := after)
        (afterBinders_liftClosed (domainTest_stable isIdTest_stable) hdom') typing
      obtain ⟨B, a, b, rfl⟩ := isIdTest_inv hA
      refine exact_split pack levels algebra formed (before := before) (after := after)
        (by rw [hlen]; exact role)
        (by rw [← length, List.length_append, List.length_cons]; omega) (k := .ident)
        ⟨B, a, b, rfl⟩
        (fun _ h => by cases h) tx
        (ih x (List.mem_append_right before (List.Mem.head after)) tx) ?_
      intro fits
      exact pack.rootCoverage role declared (before ++ x :: after) length
        ⟨before, x, after, rfl, hlen, .inr ⟨hdom, fits⟩⟩

/-- Progress for typed terms smaller than a bound, by induction on the bound. -/
theorem progress_lt (pack : ProgressFacts P roles) (levels : LevelModel R L)
    (algebra : Normalization.CumulativeAlgebra R) :
    ∀ (N : Nat) {n : Nat} (t : CTm Head n), ctmSize t < N →
    ∀ {Γ : CCtx Head n} {T : CTm Head n}, CCtxFormed P Γ → CTyped P Γ t T → Progresses P roles t
  | 0, _, _, small, _, _, _, _ => absurd small (Nat.not_lt_zero _)
  | N + 1, n, t, small, Γ, T, formed, typing => by
      cases t with
      | var i => exact .inr (.neutral (.var i))
      | const c =>
          cases h : roles c with
          | rigid => exact .inr (.neutral (Neutral.rigid (c := c) [] h))
          | «inductive» _ => exact .inr (.inductiveConst (n := n) h)
          | constructor arity => exact .inr (.constructorSpine (k := c) [] h)
          | computes arity inspect =>
              cases arity with
              | zero =>
                  exact exact_spine pack levels algebra formed h (args := []) rfl typing
                    (fun _ mem _ _ => nomatch mem)
              | succ _ =>
                  exact .inr (.partialSpine (c := c) [] h (Nat.succ_pos _))
      | head h => exact .inr (.former (.head h))
      | pi A B => exact .inr (.former (.pi A B))
      | sigma A B => exact .inr (.former (.sigma A B))
      | id A a b => exact .inr (.former (.id A a b))
      | lam A b => exact .inr (.lam A b)
      | pair a b => exact .inr (.pair a b)
      | refl a => exact .inr (.refl a)
      | fst p =>
          obtain ⟨A, B, tp, _⟩ := typing.generation
          rcases progress_lt pack levels algebra N p (Nat.lt_of_succ_lt_succ small) formed tp with
            ⟨p', step⟩ | shape
          · exact .inl ⟨_, .fst step⟩
          · rcases canonical_at pack levels algebra formed shape tp (k := .sigma) ⟨A, B, rfl⟩
              (fun _ h => by cases h) with neutral | ⟨a, b, rfl⟩
            · exact .inr (.neutral (.fst neutral))
            · exact .inl ⟨_, .fstPair a b⟩
      | snd p =>
          obtain ⟨A, B, tp, _⟩ := typing.generation
          rcases progress_lt pack levels algebra N p (Nat.lt_of_succ_lt_succ small) formed tp with
            ⟨p', step⟩ | shape
          · exact .inl ⟨_, .snd step⟩
          · rcases canonical_at pack levels algebra formed shape tp (k := .sigma) ⟨A, B, rfl⟩
              (fun _ h => by cases h) with neutral | ⟨a, b, rfl⟩
            · exact .inr (.neutral (.snd neutral))
            · exact .inl ⟨_, .sndPair a b⟩
      | app f a =>
          have sizes : ctmSize f + ctmSize a + 1 < N + 1 := small
          obtain ⟨A, B, tf, _, _⟩ := typing.generation
          rcases progress_lt pack levels algebra N f (by omega) formed tf with ⟨f', step⟩ | shape
          · exact .inl ⟨_, .appFun step⟩
          · rcases canonical_at pack levels algebra formed shape tf (k := .pi) ⟨A, B, rfl⟩
              (fun _ h => by cases h) with neutral | fits
            · exact .inr (.neutral (.app neutral))
            · rcases fits with ⟨D, b, rfl⟩ | ⟨k, arity, args, role, _, rfl⟩ |
                ⟨c, arity, inspect, args, role, short, rfl⟩
              · exact .inl ⟨_, .beta D b a⟩
              · rw [← appSpine_snoc]
                exact .inr (.constructorSpine (args ++ [a]) role)
              · rw [← appSpine_snoc]
                rw [← appSpine_snoc] at typing
                rcases Nat.lt_or_ge (args.length + 1) arity with short' | long
                · exact .inr (.partialSpine (args ++ [a]) role
                    (by rw [List.length_append]; exact short'))
                · have length : (args ++ [a]).length = arity := by
                    rw [List.length_append]
                    exact Nat.le_antisymm short long
                  refine exact_spine pack levels algebra formed role length typing ?_
                  intro x mem S tx
                  have smaller : ctmSize x < ctmSize (CTm.appSpine (.const c) args) + ctmSize a + 1 := by
                    have within := ctmSize_lt_appSpine (args ++ [a]) (.const c) x mem
                    rwa [appSpine_snoc] at within
                  exact progress_lt pack levels algebra N x (by omega) formed tx

/-- **Progress**: a typed annotated term, over a formed context, takes an annotated weak-head
step or is a weak-head normal form. -/
theorem progress (pack : ProgressFacts P roles) (levels : LevelModel R L)
    (algebra : Normalization.CumulativeAlgebra R)
    {Γ : CCtx Head n} {t T : CTm Head n} (formed : CCtxFormed P Γ)
    (typing : CTyped P Γ t T) : Progresses P roles t :=
  progress_lt pack levels algebra (ctmSize t + 1) t (Nat.lt_succ_self _) formed typing

/-- **Progress for annotated types**: a type of a universe, over a formed context, takes an
annotated weak-head step, or its erasure is in weak-head form. -/
theorem typeProgress (pack : ProgressFacts P roles) (levels : LevelModel R L)
    (algebra : Normalization.CumulativeAlgebra R)
    {Γ : CCtx Head n} {A : CTm Head n} {u : Head} (formed : CCtxFormed P Γ)
    (hu : R.isUniverse u) (typing : CTyped P Γ A (.head u)) :
    (∃ A', CWhStepR P roles A A') ∨ IsTypeForm roles A.erase := by
  rcases progress pack levels algebra formed typing with step | shape
  · exact .inl step
  · rcases canonical_at pack levels algebra formed shape typing (k := .univ) ⟨u, hu, rfl⟩
      (fun _ h => by cases h) with neutral | fits
    · exact .inr (neutral_typeForm neutral)
    · rcases fits with former | ⟨T, ctors, role, rfl⟩
      · exact .inr former.typeForm
      · exact .inr (inductive_typeForm role)

end Progress
end Annotated
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
