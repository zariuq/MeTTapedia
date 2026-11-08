import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramBindersStrategyControls

/-!
# Leftmost-innermost reduction under binders, with `Atom` positions

**Declarations.** Following Prime's `Atom`/`Proc` ruling, a head's signature declares, per
parameter, whether the parameter is `atom` (data, never evaluated) or `proc` (run). The declaration
is data on the heads (`Declarations`), not a marker on terms. A position is **frozen** when it lies
inside an argument whose head declares that parameter `atom` (`Frozen`); undeclared parameters are
run.

**The reference** (`LeftmostAt`, `LeftmostInnermost`) is defined from R100's innermost condition
and a leftmost order on positions (`LeftOf`): an evaluated position where some equation matches,
with no evaluated match strictly inside (`InnerNormalA`; with no declarations it is R100's
`InnerNormal`, `innerNormalA_iff`), and no such position to its left.

**The strategy** (`Selects`) is a syntax-directed search, defined independently of the reference:
into the function first; into the argument only when the function is normal and the argument is not
`atom`; under a binder with the program raised along it; and the root only when nothing evaluated
inside matches.

- `selects_leftmost`, `leftmost_selects`: the strategy selects exactly the reference's redex.
- `selects_unique`: **the next redex is unique**.
- `decompose`: every term is normal at its evaluated positions, or has a selected redex.
- `step_iff`: firing at the selected redex is exactly one leftmost-innermost reduction.
- `leftmost_innermost_of_none`: with no declarations, a leftmost-innermost reduction is one of R100's
  innermost reductions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders.Leftmost

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open LambdaContextualRung (sig Srt Op Context appT lamT)
open Strategy (MatchesAt InnerNormal Innermost comp depth)
open Nested (raiseAt raisedSchema grammar)
open Controls (appT_inj lamT_inj)

/-! ## Declarations and frozen positions -/

/-- A parameter's declared kind: an `atom` parameter is data and is not evaluated; a `proc`
parameter is run. -/
inductive Kind where
  | atom
  | proc
  deriving DecidableEq

/-- **Declarations**: each head's parameter kinds, in order. A parameter past the list is undeclared,
and undeclared parameters are run. -/
abbrev Declarations (H : Type) : Type := H → List Kind

/-- No parameter is declared. -/
def noDeclarations (H : Type) : Declarations H := fun _ => []

/-- The heads seen under one more binder: the bound variable is no head. -/
def liftAmb {H : Type} {Δ : Ctx sig} (amb : Var Δ .term → Option H) : Var (.term :: Δ) .term → Option H
  | .zero => none
  | .succ v => amb v

/-- `function` applies the head `h` to `k` arguments. -/
inductive Spine {H : Type} {Δ : Ctx sig} (amb : Var Δ .term → Option H) : Term sig Δ .term → H → ℕ → Prop
  | head (v : Var Δ .term) (h : H) (named : amb v = some h) : Spine amb (.var v) h 0
  | arg (function argument : Term sig Δ .term) (h : H) (k : ℕ) (spine : Spine amb function h k) :
      Spine amb (appT function argument) h (k + 1)

/-- The argument after `function` is declared `atom` by its head. -/
def AtomArg {H : Type} (decl : Declarations H) {Δ : Ctx sig} (amb : Var Δ .term → Option H)
    (function : Term sig Δ .term) : Prop :=
  ∃ h k, Spine amb function h k ∧ (decl h)[k]? = some .atom

/-- **A frozen position** lies inside an argument declared `atom`. -/
inductive Frozen {H : Type} (decl : Declarations H) :
    {Γ Δ : Ctx sig} → (Var Γ .term → Option H) → Context Γ Δ → Prop
  | atom {Γ Δ : Ctx sig} {amb : Var Γ .term → Option H} (function : Term sig Γ .term) (inner : Context Γ Δ)
      (declared : AtomArg decl amb function) : Frozen decl amb (.appRight function inner)
  | right {Γ Δ : Ctx sig} {amb : Var Γ .term → Option H} (function : Term sig Γ .term) (inner : Context Γ Δ)
      (frozen : Frozen decl amb inner) : Frozen decl amb (.appRight function inner)
  | left {Γ Δ : Ctx sig} {amb : Var Γ .term → Option H} (inner : Context Γ Δ) (argument : Term sig Γ .term)
      (frozen : Frozen decl amb inner) : Frozen decl amb (.appLeft inner argument)
  | lam {Γ Δ : Ctx sig} {amb : Var Γ .term → Option H} (inner : Context (.term :: Γ) Δ)
      (frozen : Frozen decl (liftAmb amb) inner) : Frozen decl amb (.underLam inner)

section Frozen

variable {H : Type} {decl : Declarations H}

theorem not_frozen_hole {Γ : Ctx sig} {amb : Var Γ .term → Option H} :
    ¬ Frozen decl amb (Context.hole : Context Γ Γ) := fun frozen => by cases frozen

theorem frozen_left_iff {Γ Δ : Ctx sig} {amb : Var Γ .term → Option H} {inner : Context Γ Δ}
    {argument : Term sig Γ .term} : Frozen decl amb (.appLeft inner argument) ↔ Frozen decl amb inner :=
  ⟨fun frozen => by cases frozen with | left _ _ frozen => exact frozen, fun frozen => .left _ _ frozen⟩

theorem frozen_right_iff {Γ Δ : Ctx sig} {amb : Var Γ .term → Option H} {function : Term sig Γ .term}
    {inner : Context Γ Δ} :
    Frozen decl amb (.appRight function inner) ↔ AtomArg decl amb function ∨ Frozen decl amb inner := by
  constructor
  · intro frozen
    cases frozen with
    | atom _ _ declared => exact .inl declared
    | right _ _ frozen => exact .inr frozen
  · rintro (declared | frozen)
    · exact .atom _ _ declared
    · exact .right _ _ frozen

theorem frozen_lam_iff {Γ Δ : Ctx sig} {amb : Var Γ .term → Option H} {inner : Context (.term :: Γ) Δ} :
    Frozen decl amb (.underLam inner) ↔ Frozen decl (liftAmb amb) inner :=
  ⟨fun frozen => by cases frozen with | lam _ frozen => exact frozen, fun frozen => .lam _ frozen⟩

/-- With no declarations, no position is frozen. -/
theorem not_frozen_none {Γ Δ : Ctx sig} {amb : Var Γ .term → Option H} (context : Context Γ Δ) :
    ¬ Frozen (noDeclarations H) amb context := by
  intro frozen
  induction frozen with
  | atom _ _ declared =>
      obtain ⟨h, k, -, atom⟩ := declared
      simp [noDeclarations] at atom
  | right _ _ _ ih => exact ih
  | left _ _ _ ih => exact ih
  | lam _ _ ih => exact ih

end Frozen

/-! ## The leftmost order on positions -/

/-- **`first` lies left of `second`**: where the two positions part, at an application, `first` goes
into the function and `second` into the argument. -/
inductive LeftOf : {Γ Δ Θ : Ctx sig} → Context Γ Δ → Context Γ Θ → Prop
  | split {Γ Δ Θ : Ctx sig} (first : Context Γ Δ) (second : Context Γ Θ) (argument function : Term sig Γ .term) :
      LeftOf (.appLeft first argument) (.appRight function second)
  | left {Γ Δ Θ : Ctx sig} (first : Context Γ Δ) (second : Context Γ Θ) (argument argument' : Term sig Γ .term)
      (below : LeftOf first second) : LeftOf (.appLeft first argument) (.appLeft second argument')
  | right {Γ Δ Θ : Ctx sig} (first : Context Γ Δ) (second : Context Γ Θ) (function function' : Term sig Γ .term)
      (below : LeftOf first second) : LeftOf (.appRight function first) (.appRight function' second)
  | lam {Γ Δ Θ : Ctx sig} (first : Context (.term :: Γ) Δ) (second : Context (.term :: Γ) Θ)
      (below : LeftOf first second) : LeftOf (.underLam first) (.underLam second)

theorem not_leftOf_hole {Γ Θ : Ctx sig} (other : Context Γ Θ) : ¬ LeftOf other (Context.hole : Context Γ Γ) :=
  fun left => by cases left

theorem leftOf_left_iff {Γ Δ Θ : Ctx sig} {first : Context Γ Δ} {second : Context Γ Θ}
    {argument argument' : Term sig Γ .term} :
    LeftOf (.appLeft first argument) (.appLeft second argument') ↔ LeftOf first second :=
  ⟨fun left => by cases left with | left _ _ _ _ below => exact below, fun below => .left _ _ _ _ below⟩

theorem leftOf_right_iff {Γ Δ Θ : Ctx sig} {first : Context Γ Δ} {second : Context Γ Θ}
    {function function' : Term sig Γ .term} :
    LeftOf (.appRight function first) (.appRight function' second) ↔ LeftOf first second :=
  ⟨fun left => by cases left with | right _ _ _ _ below => exact below, fun below => .right _ _ _ _ below⟩

theorem leftOf_lam_iff {Γ Δ Θ : Ctx sig} {first : Context (.term :: Γ) Δ} {second : Context (.term :: Γ) Θ} :
    LeftOf (.underLam first) (.underLam second) ↔ LeftOf first second :=
  ⟨fun left => by cases left with | lam _ _ below => exact below, fun below => .lam _ _ below⟩

theorem not_leftOf_right_left {Γ Δ Θ : Ctx sig} {first : Context Γ Δ} {second : Context Γ Θ}
    {function argument : Term sig Γ .term} : ¬ LeftOf (.appRight function first) (.appLeft second argument) :=
  fun left => by cases left

/-! ## The reference: innermost at evaluated positions, and leftmost -/

section Reference

variable {H : Type} (decl : Declarations H) {ι : Type}

/-- No equation matches at an evaluated position strictly inside the redex: R100's `InnerNormal`,
with frozen positions left out. -/
def InnerNormalA {Γ : Ctx sig} (program : ι → Equation sig Γ .term) (amb : Var Γ .term → Option H)
    {Δ : Ctx sig} (context : Context Γ Δ) (inner : Term sig Δ .term) : Prop :=
  ∀ {Θ : Ctx sig} (below : Context Δ Θ) (term : Term sig Θ .term), 0 < depth below → inner = below.plug term →
    ¬ Frozen decl amb (comp context below) → ¬ MatchesAt program (comp context below) term

/-- An innermost redex at an evaluated position. -/
def InnermostAt {Γ : Ctx sig} (program : ι → Equation sig Γ .term) (amb : Var Γ .term → Option H)
    {Δ : Ctx sig} (context : Context Γ Δ) (inner : Term sig Δ .term) : Prop :=
  ¬ Frozen decl amb context ∧ MatchesAt program context inner ∧ InnerNormalA decl program amb context inner

/-- **The leftmost innermost redex** of `term`: an innermost redex at an evaluated position, with no
other one to its left. -/
def LeftmostAt {Γ : Ctx sig} (program : ι → Equation sig Γ .term) (amb : Var Γ .term → Option H)
    (term : Term sig Γ .term) {Δ : Ctx sig} (context : Context Γ Δ) (inner : Term sig Δ .term) : Prop :=
  term = context.plug inner ∧ InnermostAt decl program amb context inner ∧
    ∀ {Θ : Ctx sig} (other : Context Γ Θ) (otherInner : Term sig Θ .term), term = other.plug otherInner →
      InnermostAt decl program amb other otherInner → ¬ LeftOf other context

/-- No equation matches at any evaluated position of `term`. -/
def NormalA {Γ : Ctx sig} (program : ι → Equation sig Γ .term) (amb : Var Γ .term → Option H)
    (term : Term sig Γ .term) : Prop :=
  ∀ {Θ : Ctx sig} (below : Context Γ Θ) (inner : Term sig Θ .term), term = below.plug inner →
    ¬ Frozen decl amb below → ¬ MatchesAt program below inner

/-- With no declarations, the innermost condition is R100's. -/
theorem innerNormalA_iff {Γ : Ctx sig} (program : ι → Equation sig Γ .term) {amb : Var Γ .term → Option H}
    {Δ : Ctx sig} (context : Context Γ Δ) (inner : Term sig Δ .term) :
    InnerNormalA (noDeclarations H) program amb context inner ↔ InnerNormal program context inner :=
  ⟨fun normal _ below term positive same => normal below term positive same (not_frozen_none _),
    fun normal _ below term positive same _ => normal below term positive same⟩

end Reference

/-! ## The strategy: a syntax-directed search -/

section Strategy

variable {H : Type} (decl : Declarations H) {ι : Type}

/-- **The leftmost-innermost search.** Into the function first; into the argument only when the
function is normal and the argument is not `atom`; under a binder with the program raised along
it; the root only when no evaluated position strictly inside matches. -/
inductive Selects : {Γ : Ctx sig} → (ι → Equation sig Γ .term) → (Var Γ .term → Option H) →
    Term sig Γ .term → {Δ : Ctx sig} → Context Γ Δ → Term sig Δ .term → Prop
  | root {Γ : Ctx sig} {program : ι → Equation sig Γ .term} {amb : Var Γ .term → Option H}
      (term : Term sig Γ .term) (matched : MatchesAt program .hole term)
      (inside : ∀ {Θ : Ctx sig} (below : Context Γ Θ) (inner : Term sig Θ .term), 0 < depth below →
        term = below.plug inner → ¬ Frozen decl amb below → ¬ MatchesAt program below inner) :
      Selects program amb term .hole term
  | left {Γ : Ctx sig} {program : ι → Equation sig Γ .term} {amb : Var Γ .term → Option H}
      (function argument : Term sig Γ .term) {Δ : Ctx sig} (context : Context Γ Δ) (inner : Term sig Δ .term)
      (inFunction : Selects program amb function context inner) :
      Selects program amb (appT function argument) (.appLeft context argument) inner
  | right {Γ : Ctx sig} {program : ι → Equation sig Γ .term} {amb : Var Γ .term → Option H}
      (function argument : Term sig Γ .term) {Δ : Ctx sig} (context : Context Γ Δ) (inner : Term sig Δ .term)
      (normal : NormalA decl program amb function) (evaluated : ¬ AtomArg decl amb function)
      (inArgument : Selects program amb argument context inner) :
      Selects program amb (appT function argument) (.appRight function context) inner
  | lam {Γ : Ctx sig} {program : ι → Equation sig Γ .term} {amb : Var Γ .term → Option H}
      (body : Term sig (.term :: Γ) .term) {Δ : Ctx sig} (context : Context (.term :: Γ) Δ) (inner : Term sig Δ .term)
      (inBody : Selects (fun index => raiseOne Srt.term (program index)) (liftAmb amb) body context inner) :
      Selects program amb (lamT body) (.underLam context) inner

end Strategy

/-! ## Moving positions through one constructor -/

section Moves

variable {H : Type} {decl : Declarations H} {ι : Type}

theorem innerNormalA_left_iff {Γ : Ctx sig} {program : ι → Equation sig Γ .term} {amb : Var Γ .term → Option H}
    {Δ : Ctx sig} {context : Context Γ Δ} {argument : Term sig Γ .term} {inner : Term sig Δ .term} :
    InnerNormalA decl program amb (.appLeft context argument) inner ↔ InnerNormalA decl program amb context inner := by
  constructor
  · intro normal Θ below term positive same live
    exact normal below term positive same (fun frozen => live (frozen_left_iff.mp frozen))
  · intro normal Θ below term positive same live
    exact normal below term positive same (fun frozen => live (frozen_left_iff.mpr frozen))

theorem innerNormalA_right_iff {Γ : Ctx sig} {program : ι → Equation sig Γ .term} {amb : Var Γ .term → Option H}
    {Δ : Ctx sig} {function : Term sig Γ .term} (evaluated : ¬ AtomArg decl amb function) {context : Context Γ Δ}
    {inner : Term sig Δ .term} :
    InnerNormalA decl program amb (.appRight function context) inner ↔ InnerNormalA decl program amb context inner := by
  constructor
  · intro normal Θ below term positive same live
    exact normal below term positive same (fun frozen => live ((frozen_right_iff.mp frozen).resolve_left evaluated))
  · intro normal Θ below term positive same live
    exact normal below term positive same (fun frozen => live (frozen_right_iff.mpr (.inr frozen)))

theorem innerNormalA_lam_iff {Γ : Ctx sig} {program : ι → Equation sig Γ .term} {amb : Var Γ .term → Option H}
    {Δ : Ctx sig} {context : Context (.term :: Γ) Δ} {inner : Term sig Δ .term} :
    InnerNormalA decl program amb (.underLam context) inner ↔
      InnerNormalA decl (fun index => raiseOne Srt.term (program index)) (liftAmb amb) context inner := by
  constructor
  · intro normal Θ below term positive same live
    exact normal below term positive same (fun frozen => live (frozen_lam_iff.mp frozen))
  · intro normal Θ below term positive same live
    exact normal below term positive same (fun frozen => live (frozen_lam_iff.mpr frozen))

theorem innermostAt_left_iff {Γ : Ctx sig} {program : ι → Equation sig Γ .term} {amb : Var Γ .term → Option H}
    {Δ : Ctx sig} {context : Context Γ Δ} {argument : Term sig Γ .term} {inner : Term sig Δ .term} :
    InnermostAt decl program amb (.appLeft context argument) inner ↔ InnermostAt decl program amb context inner := by
  unfold InnermostAt
  rw [frozen_left_iff, innerNormalA_left_iff]
  rfl

theorem innermostAt_right_iff {Γ : Ctx sig} {program : ι → Equation sig Γ .term} {amb : Var Γ .term → Option H}
    {Δ : Ctx sig} {function : Term sig Γ .term} (evaluated : ¬ AtomArg decl amb function) {context : Context Γ Δ}
    {inner : Term sig Δ .term} :
    InnermostAt decl program amb (.appRight function context) inner ↔ InnermostAt decl program amb context inner := by
  unfold InnermostAt
  rw [frozen_right_iff, innerNormalA_right_iff evaluated]
  simp only [evaluated, false_or]
  rfl

theorem innermostAt_lam_iff {Γ : Ctx sig} {program : ι → Equation sig Γ .term} {amb : Var Γ .term → Option H}
    {Δ : Ctx sig} {context : Context (.term :: Γ) Δ} {inner : Term sig Δ .term} :
    InnermostAt decl program amb (.underLam context) inner ↔
      InnermostAt decl (fun index => raiseOne Srt.term (program index)) (liftAmb amb) context inner := by
  unfold InnermostAt
  rw [frozen_lam_iff, innerNormalA_lam_iff]
  rfl

/-- A redex strictly inside refutes the root's innermost condition. -/
theorem not_innerNormalA_hole {Γ : Ctx sig} {program : ι → Equation sig Γ .term} {amb : Var Γ .term → Option H}
    {term : Term sig Γ .term} {Δ : Ctx sig} {context : Context Γ Δ} {inner : Term sig Δ .term}
    (positive : 0 < depth context) (same : term = context.plug inner) (live : ¬ Frozen decl amb context)
    (matched : MatchesAt program context inner) : ¬ InnerNormalA decl program amb .hole term :=
  fun normal => normal context inner positive same live matched

/-- Every term is a variable, an application or an abstraction. -/
theorem term_cases {Δ : Ctx sig} (term : Term sig Δ .term) :
    (∃ v, term = .var v) ∨ (∃ function argument, term = appT function argument) ∨ ∃ body, term = lamT body := by
  rcases term with v | ⟨o, args⟩
  · exact .inl ⟨v, rfl⟩
  · cases o with
    | app =>
        rcases args with _ | ⟨function, rest⟩
        rcases rest with _ | ⟨argument, rest⟩
        rcases rest with _ | _
        exact .inr (.inl ⟨function, argument, rfl⟩)
    | lam =>
        rcases args with _ | ⟨body, rest⟩
        rcases rest with _ | _
        exact .inr (.inr ⟨body, rfl⟩)

theorem size_app_left {Δ : Ctx sig} (function argument : Term sig Δ .term) :
    termSize function < termSize (appT function argument) := by
  simp only [appT, termSize, argsSize]
  omega

theorem size_app_right {Δ : Ctx sig} (function argument : Term sig Δ .term) :
    termSize argument < termSize (appT function argument) := by
  simp only [appT, termSize, argsSize]
  omega

theorem size_lam {Δ : Ctx sig} (body : Term sig (.term :: Δ) .term) : termSize body < termSize (lamT body) := by
  simp only [lamT, termSize, argsSize]
  omega

theorem size_plug_le : ∀ {Δ Θ : Ctx sig} (below : Context Δ Θ) (term : Term sig Θ .term),
    termSize term ≤ termSize (below.plug term)
  | _, _, .hole, _ => le_rfl
  | _, _, .appLeft inner _, term => (size_plug_le inner term).trans (size_app_left _ _).le
  | _, _, .appRight _ inner, term => (size_plug_le inner term).trans (size_app_right _ _).le
  | _, _, .underLam inner, term => (size_plug_le inner term).trans (size_lam _).le

theorem size_plug_lt : ∀ {Δ Θ : Ctx sig} (below : Context Δ Θ) (term : Term sig Θ .term), 0 < depth below →
    termSize term < termSize (below.plug term)
  | _, _, .hole, _, positive => absurd positive (by simp [depth])
  | _, _, .appLeft inner _, term, _ => lt_of_le_of_lt (size_plug_le inner term) (size_app_left _ _)
  | _, _, .appRight _ inner, term, _ => lt_of_le_of_lt (size_plug_le inner term) (size_app_right _ _)
  | _, _, .underLam inner, term, _ => lt_of_le_of_lt (size_plug_le inner term) (size_lam _)

/-- A variable has only the root as a position. -/
theorem var_positions {Γ Θ : Ctx sig} {v : Var Γ .term} (below : Context Γ Θ) (inner : Term sig Θ .term)
    (same : (Term.var v : Term sig Γ .term) = below.plug inner) : depth below = 0 := by
  cases below with
  | hole => rfl
  | appLeft _ _ => cases same
  | appRight _ _ => cases same
  | underLam _ => cases same

end Moves

/-! ## The strategy selects the reference's redex -/

section Adequacy

variable {H : Type} {decl : Declarations H} {ι : Type}

/-- **The strategy selects the leftmost innermost redex.** -/
theorem selects_leftmost {Γ : Ctx sig} {program : ι → Equation sig Γ .term} {amb : Var Γ .term → Option H}
    {term : Term sig Γ .term} {Δ : Ctx sig} {context : Context Γ Δ} {inner : Term sig Δ .term}
    (selects : Selects decl program amb term context inner) : LeftmostAt decl program amb term context inner := by
  induction selects with
  | root term matched inside =>
      exact ⟨rfl, ⟨not_frozen_hole, matched, fun below v positive same live => inside below v positive same live⟩,
        fun other _ _ _ => not_leftOf_hole other⟩
  | left function argument context inner _ ih =>
      obtain ⟨same, innermost, leftmost⟩ := ih
      subst same
      refine ⟨rfl, innermostAt_left_iff.mpr innermost, fun other otherInner same' otherInnermost => ?_⟩
      cases other with
      | hole =>
          exact False.elim (not_innerNormalA_hole (context := .appLeft context argument)
            (by simp [depth]) same'.symm (fun frozen => innermost.1 (frozen_left_iff.mp frozen)) innermost.2.1
            otherInnermost.2.2)
      | appLeft other argument' =>
          obtain ⟨isFunction, -⟩ := appT_inj same'
          rw [leftOf_left_iff]
          exact leftmost other otherInner isFunction (innermostAt_left_iff.mp otherInnermost)
      | appRight _ _ => exact not_leftOf_right_left
      | underLam _ => cases same'
  | right function argument context inner normal evaluated _ ih =>
      obtain ⟨same, innermost, leftmost⟩ := ih
      subst same
      refine ⟨rfl, (innermostAt_right_iff evaluated).mpr innermost, fun other otherInner same' otherInnermost => ?_⟩
      cases other with
      | hole =>
          exact False.elim (not_innerNormalA_hole (context := .appRight function context)
            (by simp [depth]) same'.symm
            (fun frozen => innermost.1 ((frozen_right_iff.mp frozen).resolve_left evaluated)) innermost.2.1
            otherInnermost.2.2)
      | appLeft other argument' =>
          obtain ⟨isFunction, -⟩ := appT_inj same'
          exact absurd otherInnermost.2.1 (normal other otherInner isFunction
            (fun frozen => otherInnermost.1 (frozen_left_iff.mpr frozen)))
      | appRight function' other =>
          obtain ⟨isFunction, isArgument⟩ := appT_inj same'
          subst isFunction
          rw [leftOf_right_iff]
          exact leftmost other otherInner isArgument ((innermostAt_right_iff evaluated).mp otherInnermost)
      | underLam _ => cases same'
  | lam body context inner _ ih =>
      obtain ⟨same, innermost, leftmost⟩ := ih
      subst same
      refine ⟨rfl, innermostAt_lam_iff.mpr innermost, fun other otherInner same' otherInnermost => ?_⟩
      cases other with
      | hole =>
          exact False.elim (not_innerNormalA_hole (context := .underLam context)
            (by simp [depth]) same'.symm (fun frozen => innermost.1 (frozen_lam_iff.mp frozen)) innermost.2.1
            otherInnermost.2.2)
      | appLeft _ _ => cases same'
      | appRight _ _ => cases same'
      | underLam other =>
          rw [leftOf_lam_iff]
          exact leftmost other otherInner (lamT_inj same') (innermostAt_lam_iff.mp otherInnermost)

/-- **A redex has an innermost redex below it.** -/
theorem exists_innermost {Γ : Ctx sig} {program : ι → Equation sig Γ .term} {amb : Var Γ .term → Option H} :
    ∀ (size : ℕ) {Δ : Ctx sig} (context : Context Γ Δ) (inner : Term sig Δ .term), termSize inner = size →
      ¬ Frozen decl amb context → MatchesAt program context inner →
        ∃ (Θ : Ctx sig) (below : Context Δ Θ) (deeper : Term sig Θ .term), inner = below.plug deeper ∧
          InnermostAt decl program amb (comp context below) deeper := by
  intro size
  induction size using Nat.strong_induction_on with
  | _ size ih =>
      intro Δ context inner sized live matched
      by_cases normal : InnerNormalA decl program amb context inner
      · exact ⟨Δ, .hole, inner, rfl, by
          rw [StrategyControls.comp_hole]
          exact ⟨live, matched, normal⟩⟩
      · simp only [InnerNormalA, not_forall, not_not] at normal
        obtain ⟨Θ, below, term, positive, same, live', matched'⟩ := normal
        have smaller : termSize term < size := by
          rw [← sized, same]
          exact size_plug_lt below term positive
        obtain ⟨Ξ, below', deeper, same', innermost⟩ :=
          ih _ smaller (comp context below) term rfl live' matched'
        refine ⟨Ξ, comp below below', deeper, by rw [same, same', Strategy.plug_comp], ?_⟩
        rw [← StrategyControls.comp_assoc]
        exact innermost

/-- **The reference's redex is the strategy's.** -/
theorem leftmost_selects {Γ Δ : Ctx sig} (context : Context Γ Δ) :
    ∀ {program : ι → Equation sig Γ .term} {amb : Var Γ .term → Option H} {term : Term sig Γ .term}
      {inner : Term sig Δ .term}, LeftmostAt decl program amb term context inner →
        Selects decl program amb term context inner := by
  induction context with
  | hole =>
      intro program amb term inner leftmost
      obtain ⟨same, ⟨_, matched, normal⟩, _⟩ := leftmost
      change term = inner at same
      subst same
      exact .root term matched fun below v positive same' live => normal below v positive same' live
  | appLeft context argument ih =>
      intro program amb term inner leftmost
      obtain ⟨same, innermost, leftmost⟩ := leftmost
      change term = appT (context.plug inner) argument at same
      subst same
      refine .left _ _ _ _ (ih ⟨rfl, innermostAt_left_iff.mp innermost, fun other otherInner same' otherInnermost => ?_⟩)
      have left := leftmost (.appLeft other argument) otherInner (by rw [same']; rfl)
        (innermostAt_left_iff.mpr otherInnermost)
      rwa [leftOf_left_iff] at left
  | appRight function context ih =>
      intro program amb term inner leftmost
      obtain ⟨same, innermost, leftmost⟩ := leftmost
      change term = appT function (context.plug inner) at same
      subst same
      have evaluated : ¬ AtomArg decl amb function := fun declared =>
        innermost.1 (frozen_right_iff.mpr (.inl declared))
      have normal : NormalA decl program amb function := by
        intro Θ below v same' live matched
        obtain ⟨Ξ, below', deeper, same'', innermost'⟩ := exists_innermost _ below v rfl live matched
        have left := leftmost (.appLeft (comp below below') (context.plug inner)) deeper
          (by
            rw [same', same'']
            exact congrArg (fun x => appT x (context.plug inner)) (Strategy.plug_comp below below' deeper).symm)
          (innermostAt_left_iff.mpr innermost')
        exact left (.split _ _ _ _)
      refine .right _ _ _ _ normal evaluated
        (ih ⟨rfl, (innermostAt_right_iff evaluated).mp innermost, fun other otherInner same' otherInnermost => ?_⟩)
      have left := leftmost (.appRight function other) otherInner (by rw [same']; rfl)
        ((innermostAt_right_iff evaluated).mpr otherInnermost)
      rwa [leftOf_right_iff] at left
  | underLam context ih =>
      intro program amb term inner leftmost
      obtain ⟨same, innermost, leftmost⟩ := leftmost
      change term = lamT (context.plug inner) at same
      subst same
      refine .lam _ _ _ (ih ⟨rfl, innermostAt_lam_iff.mp innermost, fun other otherInner same' otherInnermost => ?_⟩)
      have left := leftmost (.underLam other) otherInner (by rw [same']; rfl)
        (innermostAt_lam_iff.mpr otherInnermost)
      rwa [leftOf_lam_iff] at left

/-- **The strategy is the reference**, at every position. -/
theorem selects_iff {Γ : Ctx sig} {program : ι → Equation sig Γ .term} {amb : Var Γ .term → Option H}
    {term : Term sig Γ .term} {Δ : Ctx sig} {context : Context Γ Δ} {inner : Term sig Δ .term} :
    Selects decl program amb term context inner ↔ LeftmostAt decl program amb term context inner :=
  ⟨selects_leftmost, leftmost_selects context⟩

theorem selects_redex {Γ : Ctx sig} {program : ι → Equation sig Γ .term} {amb : Var Γ .term → Option H}
    {term : Term sig Γ .term} {Δ : Ctx sig} {context : Context Γ Δ} {inner : Term sig Δ .term}
    (selects : Selects decl program amb term context inner) :
    term = context.plug inner ∧ ¬ Frozen decl amb context ∧ MatchesAt program context inner := by
  obtain ⟨same, ⟨live, matched, -⟩, -⟩ := selects_leftmost selects
  exact ⟨same, live, matched⟩

/-- A selection strictly inside refutes the root's condition. -/
theorem inside_refutes {Γ : Ctx sig} {program : ι → Equation sig Γ .term} {amb : Var Γ .term → Option H}
    {term : Term sig Γ .term}
    (inside : ∀ {Θ : Ctx sig} (below : Context Γ Θ) (inner : Term sig Θ .term), 0 < depth below →
      term = below.plug inner → ¬ Frozen decl amb below → ¬ MatchesAt program below inner)
    {Δ : Ctx sig} {context : Context Γ Δ} {inner : Term sig Δ .term} (positive : 0 < depth context)
    (selects : Selects decl program amb term context inner) : False := by
  obtain ⟨same, live, matched⟩ := selects_redex selects
  exact inside context inner positive same live matched

/-- **The leftmost innermost redex is unique.** -/
theorem leftmost_unique {Γ Δ₁ : Ctx sig} (first : Context Γ Δ₁) :
    ∀ {program : ι → Equation sig Γ .term} {amb : Var Γ .term → Option H} {term : Term sig Γ .term}
      {inner₁ : Term sig Δ₁ .term} {Δ₂ : Ctx sig} {second : Context Γ Δ₂} {inner₂ : Term sig Δ₂ .term},
      LeftmostAt decl program amb term first inner₁ → LeftmostAt decl program amb term second inner₂ →
        (⟨Δ₁, first, inner₁⟩ : Σ Δ : Ctx sig, Context Γ Δ × Term sig Δ .term) = ⟨Δ₂, second, inner₂⟩ := by
  induction first with
  | hole =>
      intro program amb term inner₁ Δ₂ second inner₂ one two
      obtain ⟨same₁, ⟨-, -, normal₁⟩, -⟩ := one
      obtain ⟨same₂, ⟨live₂, matched₂, -⟩, -⟩ := two
      change term = inner₁ at same₁
      subst same₁
      cases second with
      | hole =>
          change term = inner₂ at same₂
          subst same₂
          rfl
      | appLeft second argument =>
          exact (normal₁ (.appLeft second argument) inner₂ (by simp [depth]) same₂ live₂ matched₂).elim
      | appRight function second =>
          exact (normal₁ (.appRight function second) inner₂ (by simp [depth]) same₂ live₂ matched₂).elim
      | underLam second =>
          exact (normal₁ (.underLam second) inner₂ (by simp [depth]) same₂ live₂ matched₂).elim
  | appLeft first argument ih =>
      intro program amb term inner₁ Δ₂ second inner₂ one two
      obtain ⟨same₁, innermost₁, leftmost₁⟩ := one
      obtain ⟨same₂, innermost₂, leftmost₂⟩ := two
      change term = appT (first.plug inner₁) argument at same₁
      subst same₁
      cases second with
      | hole =>
          exact (not_innerNormalA_hole (context := .appLeft first argument) (by simp [depth]) same₂.symm
            innermost₁.1 innermost₁.2.1 innermost₂.2.2).elim
      | appLeft second argument' =>
          obtain ⟨isFunction, isArgument⟩ := appT_inj same₂
          subst isArgument
          have same := ih ⟨rfl, innermostAt_left_iff.mp innermost₁, fun other otherInner same' otherInnermost => by
              have left := leftmost₁ (.appLeft other argument) otherInner (by rw [same']; rfl)
                (innermostAt_left_iff.mpr otherInnermost)
              rwa [leftOf_left_iff] at left⟩
            ⟨isFunction, innermostAt_left_iff.mp innermost₂, fun other otherInner same' otherInnermost => by
              have left := leftmost₂ (.appLeft other argument) otherInner (by rw [same']; rfl)
                (innermostAt_left_iff.mpr otherInnermost)
              rwa [leftOf_left_iff] at left⟩
          cases same
          rfl
      | appRight function second =>
          exact (leftmost₂ (.appLeft first argument) inner₁ rfl innermost₁ (.split _ _ _ _)).elim
      | underLam _ => cases same₂
  | appRight function first ih =>
      intro program amb term inner₁ Δ₂ second inner₂ one two
      obtain ⟨same₁, innermost₁, leftmost₁⟩ := one
      obtain ⟨same₂, innermost₂, leftmost₂⟩ := two
      change term = appT function (first.plug inner₁) at same₁
      subst same₁
      have evaluated : ¬ AtomArg decl amb function := fun declared =>
        innermost₁.1 (frozen_right_iff.mpr (.inl declared))
      cases second with
      | hole =>
          exact (not_innerNormalA_hole (context := .appRight function first) (by simp [depth]) same₂.symm
            innermost₁.1 innermost₁.2.1 innermost₂.2.2).elim
      | appLeft second argument =>
          exact (leftmost₁ (.appLeft second argument) inner₂ same₂ innermost₂ (.split _ _ _ _)).elim
      | appRight function' second =>
          obtain ⟨isFunction, isArgument⟩ := appT_inj same₂
          subst isFunction
          have same := ih ⟨rfl, (innermostAt_right_iff evaluated).mp innermost₁,
              fun other otherInner same' otherInnermost => by
                have left := leftmost₁ (.appRight function other) otherInner (by rw [same']; rfl)
                  ((innermostAt_right_iff evaluated).mpr otherInnermost)
                rwa [leftOf_right_iff] at left⟩
            ⟨isArgument, (innermostAt_right_iff evaluated).mp innermost₂, fun other otherInner same' otherInnermost => by
              have left := leftmost₂ (.appRight function other) otherInner (by rw [same']; rfl)
                ((innermostAt_right_iff evaluated).mpr otherInnermost)
              rwa [leftOf_right_iff] at left⟩
          cases same
          rfl
      | underLam _ => cases same₂
  | underLam first ih =>
      intro program amb term inner₁ Δ₂ second inner₂ one two
      obtain ⟨same₁, innermost₁, leftmost₁⟩ := one
      obtain ⟨same₂, innermost₂, leftmost₂⟩ := two
      change term = lamT (first.plug inner₁) at same₁
      subst same₁
      cases second with
      | hole =>
          exact (not_innerNormalA_hole (context := .underLam first) (by simp [depth]) same₂.symm
            innermost₁.1 innermost₁.2.1 innermost₂.2.2).elim
      | appLeft _ _ => cases same₂
      | appRight _ _ => cases same₂
      | underLam second =>
          have isBody := lamT_inj same₂
          have same := ih ⟨rfl, innermostAt_lam_iff.mp innermost₁, fun other otherInner same' otherInnermost => by
              have left := leftmost₁ (.underLam other) otherInner (by rw [same']; rfl)
                (innermostAt_lam_iff.mpr otherInnermost)
              rwa [leftOf_lam_iff] at left⟩
            ⟨isBody, innermostAt_lam_iff.mp innermost₂, fun other otherInner same' otherInnermost => by
              have left := leftmost₂ (.underLam other) otherInner (by rw [same']; rfl)
                (innermostAt_lam_iff.mpr otherInnermost)
              rwa [leftOf_lam_iff] at left⟩
          cases same
          rfl

/-- **The next redex is unique.** -/
theorem selects_unique {Γ : Ctx sig} {program : ι → Equation sig Γ .term} {amb : Var Γ .term → Option H}
    {term : Term sig Γ .term} {Δ₁ Δ₂ : Ctx sig} {first : Context Γ Δ₁} {second : Context Γ Δ₂}
    {inner₁ : Term sig Δ₁ .term} {inner₂ : Term sig Δ₂ .term}
    (one : Selects decl program amb term first inner₁) (two : Selects decl program amb term second inner₂) :
    (⟨Δ₁, first, inner₁⟩ : Σ Δ : Ctx sig, Context Γ Δ × Term sig Δ .term) = ⟨Δ₂, second, inner₂⟩ :=
  leftmost_unique first (selects_leftmost one) (selects_leftmost two)

/-- The root is the redex when nothing evaluated strictly inside matches. -/
theorem matched_root {Γ : Ctx sig} {program : ι → Equation sig Γ .term} {amb : Var Γ .term → Option H}
    {term : Term sig Γ .term} (notNormal : ¬ NormalA decl program amb term)
    (inside : ∀ {Θ : Ctx sig} (below : Context Γ Θ) (inner : Term sig Θ .term), 0 < depth below →
      term = below.plug inner → ¬ Frozen decl amb below → ¬ MatchesAt program below inner) :
    MatchesAt program .hole term := by
  by_contra root
  apply notNormal
  intro Θ below inner same live
  cases below with
  | hole =>
      change term = inner at same
      subst same
      exact root
  | appLeft below' argument => exact inside _ inner (by simp [depth]) same live
  | appRight function below' => exact inside _ inner (by simp [depth]) same live
  | underLam below' => exact inside _ inner (by simp [depth]) same live

/-- **Decomposition**: every term is normal at its evaluated positions, or has a selected redex. -/
theorem decompose : ∀ (size : ℕ) {Γ : Ctx sig} (program : ι → Equation sig Γ .term)
    (amb : Var Γ .term → Option H) (term : Term sig Γ .term), termSize term = size →
      NormalA decl program amb term ∨
        ∃ (Δ : Ctx sig) (context : Context Γ Δ) (inner : Term sig Δ .term), Selects decl program amb term context inner := by
  intro size
  induction size using Nat.strong_induction_on with
  | _ size ih =>
      intro Γ program amb term sized
      by_cases normal : NormalA decl program amb term
      · exact .inl normal
      right
      rcases term_cases term with ⟨v, rfl⟩ | ⟨function, argument, rfl⟩ | ⟨body, rfl⟩
      · have inside : ∀ {Θ : Ctx sig} (below : Context Γ Θ) (inner : Term sig Θ .term), 0 < depth below →
            (Term.var v : Term sig Γ .term) = below.plug inner → ¬ Frozen decl amb below →
              ¬ MatchesAt program below inner := fun below inner positive same _ =>
          absurd (var_positions below inner same) (Nat.pos_iff_ne_zero.mp positive)
        exact ⟨Γ, .hole, .var v, .root _ (matched_root normal inside) inside⟩
      · rcases ih _ (sized ▸ size_app_left function argument) program amb function rfl with
          normalF | ⟨Δ, context, inner, inFunction⟩
        · by_cases go : ¬ AtomArg decl amb function ∧ ¬ NormalA decl program amb argument
          · rcases ih _ (sized ▸ size_app_right function argument) program amb argument rfl with
              normalArg | ⟨Δ, context, inner, inArgument⟩
            · exact (go.2 normalArg).elim
            · exact ⟨Δ, .appRight function context, inner, .right _ _ _ _ normalF go.1 inArgument⟩
          · have inside : ∀ {Θ : Ctx sig} (below : Context Γ Θ) (inner : Term sig Θ .term), 0 < depth below →
                appT function argument = below.plug inner → ¬ Frozen decl amb below →
                  ¬ MatchesAt program below inner := by
              intro Θ below inner positive same live
              cases below with
              | hole => simp [depth] at positive
              | appLeft below' argument' =>
                  obtain ⟨isFunction, -⟩ := appT_inj same
                  exact normalF below' inner isFunction fun frozen => live (frozen_left_iff.mpr frozen)
              | appRight function' below' =>
                  obtain ⟨isFunction, isArgument⟩ := appT_inj same
                  subst isFunction
                  by_cases declared : AtomArg decl amb function
                  · exact absurd (Frozen.atom _ _ declared) live
                  · have normalArg : NormalA decl program amb argument := by
                      by_contra notNormal
                      exact go ⟨declared, notNormal⟩
                    exact normalArg below' inner isArgument fun frozen => live (Frozen.right _ _ frozen)
              | underLam _ => cases same
            exact ⟨Γ, .hole, appT function argument, .root _ (matched_root normal inside) inside⟩
        · exact ⟨Δ, .appLeft context argument, inner, .left _ _ _ _ inFunction⟩
      · rcases ih _ (sized ▸ size_lam body) (fun index => raiseOne Srt.term (program index)) (liftAmb amb) body rfl with
          normalB | ⟨Δ, context, inner, inBody⟩
        · have inside : ∀ {Θ : Ctx sig} (below : Context Γ Θ) (inner : Term sig Θ .term), 0 < depth below →
              lamT body = below.plug inner → ¬ Frozen decl amb below → ¬ MatchesAt program below inner := by
            intro Θ below inner positive same live
            cases below with
            | hole => simp [depth] at positive
            | appLeft _ _ => cases same
            | appRight _ _ => cases same
            | underLam below' =>
                exact normalB below' inner (lamT_inj same) fun frozen => live (frozen_lam_iff.mpr frozen)
          exact ⟨Γ, .hole, lamT body, .root _ (matched_root normal inside) inside⟩
        · exact ⟨Δ, .underLam context, inner, .lam _ _ _ inBody⟩

/-! ## The selected position, read off its context -/

variable (decl) in
/-- **A clear position**: at every application where the position goes into the argument, the
function is normal at its evaluated positions. -/
inductive LeftClear : {Γ : Ctx sig} → (ι → Equation sig Γ .term) → (Var Γ .term → Option H) →
    {Δ : Ctx sig} → Context Γ Δ → Prop
  | hole {Γ : Ctx sig} {program : ι → Equation sig Γ .term} {amb : Var Γ .term → Option H} :
      LeftClear program amb (.hole : Context Γ Γ)
  | left {Γ : Ctx sig} {program : ι → Equation sig Γ .term} {amb : Var Γ .term → Option H} {Δ : Ctx sig}
      (context : Context Γ Δ) (argument : Term sig Γ .term) (clear : LeftClear program amb context) :
      LeftClear program amb (.appLeft context argument)
  | right {Γ : Ctx sig} {program : ι → Equation sig Γ .term} {amb : Var Γ .term → Option H} {Δ : Ctx sig}
      (function : Term sig Γ .term) (context : Context Γ Δ) (normal : NormalA decl program amb function)
      (clear : LeftClear program amb context) : LeftClear program amb (.appRight function context)
  | lam {Γ : Ctx sig} {program : ι → Equation sig Γ .term} {amb : Var Γ .term → Option H} {Δ : Ctx sig}
      (context : Context (.term :: Γ) Δ)
      (clear : LeftClear (fun index => raiseOne Srt.term (program index)) (liftAmb amb) context) :
      LeftClear program amb (.underLam context)

theorem clear_of_selects {Γ : Ctx sig} {program : ι → Equation sig Γ .term} {amb : Var Γ .term → Option H}
    {term : Term sig Γ .term} {Δ : Ctx sig} {context : Context Γ Δ} {inner : Term sig Δ .term}
    (selects : Selects decl program amb term context inner) : LeftClear decl program amb context := by
  induction selects with
  | root => exact .hole
  | left _ argument context _ _ ih => exact .left context argument ih
  | right function _ context _ normal _ _ ih => exact .right function context normal ih
  | lam _ context _ _ ih => exact .lam context ih

theorem LeftClear.of_left {Γ Δ : Ctx sig} {program : ι → Equation sig Γ .term} {amb : Var Γ .term → Option H}
    {context : Context Γ Δ} {argument : Term sig Γ .term}
    (clear : LeftClear decl program amb (.appLeft context argument)) : LeftClear decl program amb context := by
  cases clear
  assumption

theorem LeftClear.of_right {Γ Δ : Ctx sig} {program : ι → Equation sig Γ .term} {amb : Var Γ .term → Option H}
    {function : Term sig Γ .term} {context : Context Γ Δ}
    (clear : LeftClear decl program amb (.appRight function context)) :
    NormalA decl program amb function ∧ LeftClear decl program amb context := by
  cases clear
  exact ⟨‹_›, ‹_›⟩

theorem LeftClear.of_lam {Γ Δ : Ctx sig} {program : ι → Equation sig Γ .term} {amb : Var Γ .term → Option H}
    {context : Context (.term :: Γ) Δ} (clear : LeftClear decl program amb (.underLam context)) :
    LeftClear decl (fun index => raiseOne Srt.term (program index)) (liftAmb amb) context := by
  cases clear
  assumption

theorem selects_of_clear {Γ Δ : Ctx sig} (context : Context Γ Δ) :
    ∀ {program : ι → Equation sig Γ .term} {amb : Var Γ .term → Option H} {inner : Term sig Δ .term},
      LeftClear decl program amb context → InnermostAt decl program amb context inner →
        Selects decl program amb (context.plug inner) context inner := by
  induction context with
  | hole =>
      intro program amb inner _ innermost
      exact .root _ innermost.2.1 fun below v positive same live => innermost.2.2 below v positive same live
  | appLeft context argument ih =>
      intro program amb inner clear innermost
      exact .left _ _ _ _ (ih clear.of_left (innermostAt_left_iff.mp innermost))
  | appRight function context ih =>
      intro program amb inner clear innermost
      have evaluated : ¬ AtomArg decl amb function := fun declared =>
        innermost.1 (frozen_right_iff.mpr (.inl declared))
      exact .right _ _ _ _ clear.of_right.1 evaluated (ih clear.of_right.2 ((innermostAt_right_iff evaluated).mp innermost))
  | underLam context ih =>
      intro program amb inner clear innermost
      exact .lam _ _ _ (ih clear.of_lam (innermostAt_lam_iff.mp innermost))

/-- **The leftmost innermost redex is the innermost redex at a clear position.** -/
theorem leftmost_iff_clear {Γ : Ctx sig} {program : ι → Equation sig Γ .term} {amb : Var Γ .term → Option H}
    {term : Term sig Γ .term} {Δ : Ctx sig} {context : Context Γ Δ} {inner : Term sig Δ .term} :
    LeftmostAt decl program amb term context inner ↔
      term = context.plug inner ∧ LeftClear decl program amb context ∧ InnermostAt decl program amb context inner := by
  constructor
  · intro leftmost
    exact ⟨leftmost.1, clear_of_selects (leftmost_selects context leftmost), leftmost.2.1⟩
  · rintro ⟨rfl, clear, innermost⟩
    exact selects_leftmost (selects_of_clear context clear innermost)

end Adequacy

/-! ## Leftmost-innermost reduction -/

section Reduction

variable {Γ : Ctx sig} {ι : Type}

/-- **Leftmost-innermost reduction under binders**, `atom` positions left alone (the reference): one
equation, raised along the position's binders, answers at the leftmost innermost redex. -/
def LeftmostInnermost (decl : Declarations (Var Γ .term)) (program : ι → Equation sig Γ .term)
    (call answer : Term sig Γ .term) : Prop :=
  ∃ (Δ : Ctx sig) (context : Context Γ Δ) (index : ι) (inner result : Term sig Δ .term),
    LeftmostAt decl program some call context inner ∧ answer = context.plug result ∧
      Answers (raiseAt context (program index)) inner result

/-- **The strategy's step**: fire at the selected redex. -/
def StrategyStep (decl : Declarations (Var Γ .term)) (program : ι → Equation sig Γ .term)
    (call answer : Term sig Γ .term) : Prop :=
  ∃ (Δ : Ctx sig) (context : Context Γ Δ) (index : ι) (inner result : Term sig Δ .term),
    Selects decl program some call context inner ∧ answer = context.plug result ∧
      Answers (raiseAt context (program index)) inner result

/-- **Adequacy both ways.** -/
theorem step_iff (decl : Declarations (Var Γ .term)) (program : ι → Equation sig Γ .term)
    (call answer : Term sig Γ .term) :
    StrategyStep decl program call answer ↔ LeftmostInnermost decl program call answer := by
  constructor
  · rintro ⟨Δ, context, index, inner, result, selects, isAnswer, answered⟩
    exact ⟨Δ, context, index, inner, result, selects_leftmost selects, isAnswer, answered⟩
  · rintro ⟨Δ, context, index, inner, result, leftmost, isAnswer, answered⟩
    exact ⟨Δ, context, index, inner, result, leftmost_selects context leftmost, isAnswer, answered⟩

/-- **Every step fires at the same position**: two steps of the strategy select the same redex. -/
theorem step_position_unique {decl : Declarations (Var Γ .term)} {program : ι → Equation sig Γ .term}
    {call : Term sig Γ .term} {Δ₁ Δ₂ : Ctx sig} {first : Context Γ Δ₁} {second : Context Γ Δ₂}
    {inner₁ : Term sig Δ₁ .term} {inner₂ : Term sig Δ₂ .term}
    (one : Selects decl program some call first inner₁) (two : Selects decl program some call second inner₂) :
    (⟨Δ₁, first, inner₁⟩ : Σ Δ : Ctx sig, Context Γ Δ × Term sig Δ .term) = ⟨Δ₂, second, inner₂⟩ :=
  selects_unique one two

/-- Leftmost-innermost reduction is reduction in λ contexts (R98). -/
theorem leftmost_reduces {decl : Declarations (Var Γ .term)} {program : ι → Equation sig Γ .term}
    {call answer : Term sig Γ .term} (step : LeftmostInnermost decl program call answer) :
    CRewrites grammar (raisedSchema program) call answer := by
  obtain ⟨Δ, context, index, inner, result, ⟨isCall, -, -⟩, isAnswer, answered⟩ := step
  exact ⟨Δ, context, index, inner, result, isCall, isAnswer, answered⟩

/-- **With no declarations, it is one of R100's innermost reductions.** -/
theorem leftmost_innermost_of_none {program : ι → Equation sig Γ .term} {call answer : Term sig Γ .term}
    (step : LeftmostInnermost (noDeclarations (Var Γ .term)) program call answer) :
    Innermost program call answer := by
  obtain ⟨Δ, context, index, inner, result, ⟨isCall, ⟨-, -, normal⟩, -⟩, isAnswer, answered⟩ := step
  exact ⟨Δ, context, index, inner, result, isCall, isAnswer, answered, (innerNormalA_iff program context inner).mp normal⟩

end Reduction

#print axioms frozen_right_iff
#print axioms not_frozen_none
#print axioms innerNormalA_iff
#print axioms selects_leftmost
#print axioms exists_innermost
#print axioms leftmost_selects
#print axioms selects_iff
#print axioms selects_unique
#print axioms decompose
#print axioms clear_of_selects
#print axioms selects_of_clear
#print axioms leftmost_iff_clear
#print axioms step_iff
#print axioms step_position_unique
#print axioms leftmost_reduces
#print axioms leftmost_innermost_of_none

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders.Leftmost
