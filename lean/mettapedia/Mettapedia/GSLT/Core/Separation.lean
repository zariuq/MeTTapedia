import Mettapedia.GSLT.Core.NonFactorization

/-!
# Separating contexts, and when two notions may share a spelling

A recurring design question is whether two notions may be given one symbol.
The question is usually argued from taste.  It has an answer.

Two expressions may share a spelling exactly when **no context tells them
apart**.  If some context does, then giving them one symbol asserts that
observable behaviour is a function of the spelling — and the separating
context is a non-trivial fibre of that function, so the assertion is false.
Overload safety is therefore an instance of the factorization criterion in
`Core.NonFactorization`, not a separate discipline.

There is a second, genuinely different safety condition, and conflating the
two is what makes these arguments circular.  Notions that never occupy the
same syntactic position are never confused, because no context accepts both;
that is a fact about the grammar, and no observation is involved.  Both are
stated here so a design can say which one it is claiming.

* **Same position** — safe iff observationally indistinguishable.
* **Different positions** — safe iff no context accepts both.

Nothing here mentions any particular language.
-/

namespace Mettapedia.GSLT.Core.Separation

open Mettapedia.GSLT.Core.NonFactorization

/-- A language presented by what its contexts observe.  The observation may
be a denotation, a normal form, an acceptance verdict — anything the design
treats as visible. -/
structure ObservationSystem where
  /-- Expressions of the language. -/
  Expr : Type
  /-- One-hole contexts. -/
  Ctx : Type
  /-- What a context can report. -/
  Obs : Type
  /-- Fill a context's hole. -/
  plug : Ctx → Expr → Expr
  /-- Observe a complete expression. -/
  observe : Expr → Obs

namespace ObservationSystem

variable (system : ObservationSystem)

/-- The **behaviour** of an expression: what every context observes of it.
This is the invariant that a shared spelling would have to determine. -/
def behavior (expression : system.Expr) : system.Ctx → system.Obs :=
  fun context => system.observe (system.plug context expression)

/-- One context tells two expressions apart. -/
def Separates (context : system.Ctx) (left right : system.Expr) : Prop :=
  system.observe (system.plug context left) ≠
    system.observe (system.plug context right)

/-- Some context tells them apart.  Such a pair must not share a spelling. -/
def Separable (left right : system.Expr) : Prop :=
  ∃ context, system.Separates context left right

/-- No context tells them apart.  Such a pair may share a spelling. -/
def Indistinguishable (left right : system.Expr) : Prop :=
  ∀ context, system.observe (system.plug context left) =
    system.observe (system.plug context right)

variable {system}

theorem not_separable_iff_indistinguishable {left right : system.Expr} :
    ¬ system.Separable left right ↔ system.Indistinguishable left right := by
  constructor
  · intro notSeparable context
    by_contra differ
    exact notSeparable ⟨context, differ⟩
  · rintro indistinguishable ⟨context, differ⟩
    exact differ (indistinguishable context)

/-- Separability is exactly difference of behaviour. -/
theorem separable_iff_behavior_ne {left right : system.Expr} :
    system.Separable left right ↔ system.behavior left ≠ system.behavior right := by
  constructor
  · rintro ⟨context, differ⟩ equalBehavior
    exact differ (congrFun equalBehavior context)
  · intro differentBehavior
    by_contra notSeparable
    exact differentBehavior
      (funext (not_separable_iff_indistinguishable.mp notSeparable))

/-- **The overload criterion.**  A separating context is a non-trivial fibre
of any spelling that identifies the pair. -/
def separableFiber {left right : system.Expr} (separable : system.Separable left right)
    {Symbol : Type} (spell : system.Expr → Symbol)
    (shared : spell left = spell right) :
    NonTrivialFiber spell system.behavior where
  left := left
  right := right
  sameShadow := shared
  differentValue := separable_iff_behavior_ne.mp separable

/-- **Overloading a separable pair is unsound.**  Giving two separable
expressions one symbol asserts that behaviour is recoverable from the
symbol; it is not. -/
theorem not_factors_of_separable {left right : system.Expr}
    (separable : system.Separable left right) {Symbol : Type}
    (spell : system.Expr → Symbol) (shared : spell left = spell right) :
    ¬ Factors spell system.behavior :=
  (separableFiber separable spell shared).not_factors

/-- **Compositional observation collapses the criterion.**  When observation
is determined by the observation of the hole's filler, equal observation
already implies indistinguishability — so for such a system the overload test
reduces to comparing the two expressions directly. -/
theorem indistinguishable_of_compositional {left right : system.Expr}
    (compositional : ∀ context {a b : system.Expr},
      system.observe a = system.observe b →
        system.observe (system.plug context a) = system.observe (system.plug context b))
    (agree : system.observe left = system.observe right) :
    system.Indistinguishable left right :=
  fun context => compositional context agree

end ObservationSystem

/-! ## Different positions

The second condition.  When no context accepts both notions there is nothing
to separate, and a shared name is harmless however different the notions
are — an empty *space*, an empty *type*, and an empty *production* may all
be called empty.  This is a grammatical fact and is independent of what any
of them mean. -/

/-- A language whose contexts may reject expressions of the wrong sort. -/
structure SortedObservationSystem where
  /-- Expressions of every sort. -/
  Expr : Type
  /-- One-hole contexts. -/
  Ctx : Type
  /-- What a context can report. -/
  Obs : Type
  /-- Fill a hole, or reject the filler. -/
  plug? : Ctx → Expr → Option Expr
  /-- Observe a complete expression. -/
  observe : Expr → Obs

namespace SortedObservationSystem

variable (system : SortedObservationSystem)

/-- A context admits an expression when it accepts it in its hole. -/
def Accepts (context : system.Ctx) (expression : system.Expr) : Prop :=
  (system.plug? context expression).isSome

/-- A context separates only when it accepts both and reports differently. -/
def Separates (context : system.Ctx) (left right : system.Expr) : Prop :=
  ∃ filledLeft filledRight,
    system.plug? context left = some filledLeft ∧
      system.plug? context right = some filledRight ∧
      system.observe filledLeft ≠ system.observe filledRight

variable {system}

/-- **Sort disjointness is safety.**  If no context accepts both, then no
context separates them, and the shared name cannot cause a confusion — there
is no position at which the two readings compete. -/
theorem not_separates_of_no_common_context {left right : system.Expr}
    (noCommonContext :
      ∀ context, ¬ (system.Accepts context left ∧ system.Accepts context right))
    (context : system.Ctx) : ¬ system.Separates context left right := by
  rintro ⟨filledLeft, filledRight, leftAccepted, rightAccepted, _⟩
  exact noCommonContext context
    ⟨by simp [Accepts, leftAccepted], by simp [Accepts, rightAccepted]⟩

end SortedObservationSystem

end Mettapedia.GSLT.Core.Separation
