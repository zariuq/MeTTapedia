import Mettapedia.GSLT.Core.NonFactorization
import Mettapedia.GSLT.Core.PolicyFamilyOperationClosure
import Mettapedia.GSLT.Logic.EliminatorObservers
import Mettapedia.Cybernetics.DistinctionCalculus.PreservationGrade

/-!
# Update squares: exact, approximate and improving

A scope change is read as a map `view : X → Y` from a detailed scope to a
coarser one.  The change **supports** an update `f : X → X` when the square

```text
      f
  X ────▶ X
  │        │
 view     view
  ▼        ▼
  Y ────▶ Y
      f'
```

closes for some abstract update `f'`.  This is factorization of
`view ∘ f` through `view` (`Mettapedia.GSLT.Core.NonFactorization.Factors`), so
the whole factorization API applies.

**Exact squares.**
* Supported updates contain the identity and compose (`SquareCloses.comp`);
  they form a submonoid of `Function.End X` (`supportedUpdates`), closed under
  iteration (`Supports.iterate`).
* For a quotient view, support is exactly preservation of the equivalence
  (`supports_mk_iff`), constructively.
* **Two states identified now that need different actions later** refute
  support (`not_supports_of_split`).  The refresh canary of the policy-family
  development is an instance (`refresh_not_supported`).
* For observer stages, the update given by plugging a context is supported
  exactly when the context preserves the stage's equivalence
  (`supports_stageClass_iff`).  With the conservativity criterion for
  observer extensions, **adding contexts to an observer class is conservative
  exactly when each added context is a supported update of the old view**
  (`conservative_iff_supported`).  Instance: the eliminator view supports
  application to `tt`, while the data-eliminator view, which identifies the
  identity on booleans with negation, does not
  (`Eliminators.eliminators_support_applyTrue`,
  `Eliminators.dataEliminators_not_support_applyTrue`).

**Nondeterministic updates.**  A view supports a step relation when an
abstract relation simulates it forth and back (`RelSupports`), exactly when
its kernel is a bisimulation for the steps (`relSupports_iff`); no abstract
update function is chosen.  Exact support of a function gives support of its
graph (`Supports.relSupports`).  The stage view of an observer class supports
the reductions of every admissible context
(`relSupports_stageClass_of_admissible`).  Control: the eliminator view,
which observes by evaluation, identifies `(λx. x) tt` with `tt` and so does
not support root β-reduction (`Eliminators.eliminators_not_relSupports_rootBeta`).

**Approximate squares.**  With a distance `dist : Y → Y → D` valued in an
ordered additive monoid, a square commutes up to `ε` when
`dist (view (f x)) (f' (view x)) ≤ ε` (`ApproxSquare`).
* Squares compose, with error `δ + ω ε` when the second abstract update has
  modulus `ω` (`ApproxSquare.comp`); errors add along nonexpansive abstract
  updates (`ApproxSquare.comp_nonexpansive`), so `n` steps cost at most
  `n • ε` (`ApproxSquare.iterate`).
* With the d-calculus tolerances, a second abstract update that expands
  distances by at most `δ` adds `δ` (`ApproxSquare.comp_tolerance`).
* Controls over `ℕ`: the additive bound is attained (`Succ.error_iterate`);
  "within `ε`" is not closed under composition (`Succ.not_within_one`); an
  abstract update that doubles distances makes one unit of error per step
  grow to `2 ^ n - 1` (`Doubling.error_iterate`), beyond the additive bound
  (`Doubling.exceeds_additive`).

**Optimisation promises.**  Three contracts, over an answer readout and a
cost model:
* exact preservation of a readout (`PreservesExactly`);
* **improvement**: the same answers with cost no larger (`Improves`), a lax
  square in the preorder of costed answers (`improves_iff_laxSquare`);
* approximation within `ε` under a stated distance (`Approximates`).
Exact preservation of answers and cost implies improvement
(`PreservesExactly.improves`); improvement implies exact preservation of
answers only (`Improves.preservesAnswers`); each composes
(`Improves.comp`, `Approximates.comp`), and lax squares compose along
monotone abstract updates (`LaxSquare.comp`).  Controls on arithmetic
expressions: constant folding is an improvement
(`Folding.fold_improves`) that does not preserve cost exactly
(`Folding.fold_not_preserves_cost`); dropping a trailing increment
approximates within `1` (`Folding.dropIncrement_approximates`) and changes the
answer of `x₀ + 1`, so it is not an improvement
(`Folding.dropIncrement_not_improves`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Scope

open Mettapedia.GSLT.Core.NonFactorization

universe uX uX' uX'' uY uY' uY'' uD uA uC

/-! ## Exact squares -/

section Exact

variable {X : Type uX} {X' : Type uX'} {X'' : Type uX''}
  {Y : Type uY} {Y' : Type uY'} {Y'' : Type uY''}

/-- **The update square closes**: some abstract update `f'` satisfies
`f' (view x) = view' (f x)` for every `x`. -/
def SquareCloses (view : X → Y) (view' : X' → Y') (f : X → X') : Prop :=
  Factors view fun x => view' (f x)

/-- **A scope change supports an update** when its square closes. -/
abbrev Supports (view : X → Y) (f : X → X) : Prop :=
  SquareCloses view view f

theorem squareCloses_iff (view : X → Y) (view' : X' → Y') (f : X → X') :
    SquareCloses view view' f ↔ ∃ f' : Y → Y', ∀ x, view' (f x) = f' (view x) :=
  ⟨fun ⟨f', commutes⟩ => ⟨f', fun x => (commutes x).symm⟩,
    fun ⟨f', commutes⟩ => ⟨f', fun x => (commutes x).symm⟩⟩

/-- The identity update is supported. -/
theorem supports_id (view : X → Y) : Supports view id :=
  ⟨id, fun _ => rfl⟩

/-- **Supported updates compose.** -/
theorem SquareCloses.comp {view : X → Y} {view' : X' → Y'} {view'' : X'' → Y''}
    {f : X → X'} {g : X' → X''} (first : SquareCloses view view' f)
    (second : SquareCloses view' view'' g) : SquareCloses view view'' (g ∘ f) := by
  obtain ⟨f', commutes⟩ := first
  obtain ⟨g', commutes'⟩ := second
  exact ⟨fun y => g' (f' y), fun x => by
    change g' (f' (view x)) = view'' (g (f x))
    rw [commutes x, commutes' (f x)]⟩

/-- Supported updates are closed under iteration. -/
theorem Supports.iterate {view : X → Y} {f : X → X} (supported : Supports view f) :
    ∀ n : ℕ, Supports view f^[n]
  | 0 => supports_id view
  | n + 1 => by
    rw [Function.iterate_succ]
    exact supported.comp (Supports.iterate supported n)

/-- **The supported updates form a submonoid of the endomorphisms.** -/
def supportedUpdates (view : X → Y) : Submonoid (Function.End X) where
  carrier := {f | Supports view f}
  one_mem' := supports_id view
  mul_mem' := fun {f g} supportedF supportedG =>
    SquareCloses.comp (f := g) (g := f) supportedG supportedF

/-- **Support needs constancy on fibres**: the abstract update must send
states the view identifies to states the view identifies. -/
theorem SquareCloses.constant {view : X → Y} {view' : X' → Y'} {f : X → X'}
    (closes : SquareCloses view view' f) {x y : X} (same : view x = view y) :
    view' (f x) = view' (f y) :=
  Factors.constantOnFibers closes x y same

/-- **Two states identified now that need different views later** refute
support of the update. -/
theorem not_supports_of_split {view : X → Y} {f : X → X} {x y : X}
    (same : view x = view y) (split : view (f x) ≠ view (f y)) : ¬ Supports view f :=
  fun supported => split (supported.constant same)

/-- **For a quotient view, support is preservation of the equivalence**,
constructively in both directions. -/
theorem supports_mk_iff (E : Setoid X) (f : X → X) :
    Supports (Quotient.mk E) f ↔ ∀ ⦃x y : X⦄, E x y → E (f x) (f y) := by
  constructor
  · intro supported x y related
    exact Quotient.exact (supported.constant (Quotient.sound related))
  · intro preserves
    exact ⟨Quotient.map f preserves, fun _ => rfl⟩

/-- For a view that reaches every abstract state, support is constancy of
the updated view on fibres.  The converse direction assigns abstract updates
through a chosen section of the view, so it uses `Classical.choice`
(through `Function.surjInv`). -/
theorem squareCloses_iff_constant {view : X → Y} (surjective : Function.Surjective view)
    (view' : X' → Y') (f : X → X') :
    SquareCloses view view' f ↔ ∀ x y, view x = view y → view' (f x) = view' (f y) :=
  factors_iff_constantOnFibers surjective _

end Exact

/-! ### The refresh canary: current sufficiency is not update stability -/

section Refresh

open Mettapedia.GSLT.Core.PolicyFamily.OperationClosureCanary

/-- **Control.**  Recomputing a cached emptiness answer is not supported by
the view that keeps only the current answer: counts `0` and `1` share the
current answer and are separated after the refresh. -/
theorem refresh_not_supported : ¬ Supports currentAnswer.toObservationClass refresh :=
  refresh_does_not_descend_to_current_answer

end Refresh

/-! ### Observer stages: supported contexts are conservative extensions -/

section Stages

open Mettapedia.GSLT
open Mettapedia.GSLT.MinimalEnablingContext
open Mettapedia.GSLT.AdmissibleContextCongruence
open Mettapedia.GSLT.AdmissibleContextCongruence.AdmissibleClass

universe uS uContext uRule uAtom

variable {S : GSLT.{uS}} {rules : ContextualRules.{uContext, uRule} S}
  (observations : ContextualRules.Observations.{uAtom} S)

/-- **Plugging a context is a supported update of an observer stage exactly
when the context preserves the stage's equivalence.** -/
theorem supports_stageClass_iff (D : AdmissibleClass rules) (context : rules.Context) :
    Supports (stageClass observations D) (rules.plug context) ↔
      Preserves context (D.RelEquiv observations) := by
  constructor
  · intro supported left right related
    exact (stageClass_eq_iff observations D _ _).mp
      (supported.constant ((stageClass_eq_iff observations D _ _).mpr related))
  · intro preserved
    exact ⟨Quotient.map (rules.plug context) fun _ _ related => preserved related,
      fun _ => rfl⟩

/-- Every admissible context of a class is a supported update of its stage:
the congruence of relative equivalence, read as an update square. -/
theorem supports_stageClass_of_admissible (D : AdmissibleClass rules)
    {context : rules.Context} (admissible : D.Admissible context) :
    Supports (stageClass observations D) (rules.plug context) :=
  (supports_stageClass_iff observations D context).mpr fun _ _ related =>
    D.relEquiv_closedUnder observations admissible related

/-- **Adding contexts to an observer class is conservative exactly when every
added context is a supported update of the old view.** -/
theorem conservative_iff_supported (A : AdmissibleClass rules) (added : Set rules.Context) :
    (∀ left right, (A ⊔ generatedBy added).RelEquiv observations left right ↔
        A.RelEquiv observations left right) ↔
      ∀ context ∈ added, Supports (stageClass observations A) (rules.plug context) := by
  rw [relEquiv_sup_generatedBy_iff observations A added]
  exact forall₂_congr fun context _ => (supports_stageClass_iff observations A context).symm

end Stages

/-! ### Instance: eliminator observers and application -/

namespace Eliminators

open Mettapedia.GSLT.EliminatorObservers
open Mettapedia.GSLT.AdmissibleContextCongruence
open Mettapedia.GSLT.AdmissibleContextCongruence.AdmissibleClass
open Mettapedia.TypeTheory.Calculi.BooleanSTLC

/-- The context applying a boolean function to `tt`. -/
def applyTrue : Context :=
  Context.single (Stack.cons (Frame.apply (B := .bool) Tm.tt) Stack.nil :
    Stack (.arr .bool .bool) .bool)

theorem applyTrue_admissible : eliminators.Admissible applyTrue :=
  Context.all_single (.cons (.apply Tm.tt) .nil)

/-- **Positive.**  The eliminator view supports application to `tt`. -/
theorem eliminators_support_applyTrue :
    Supports (stageClass observations eliminators) (rules.plug applyTrue) :=
  supports_stageClass_of_admissible observations eliminators applyTrue_admissible

theorem plug_applyTrue (t : Closed (.arr .bool .bool)) :
    rules.plug applyTrue ⟨_, t⟩ = ⟨.bool, Tm.app t Tm.tt⟩ :=
  Context.plug_single _ t

/-- Booleans computing `true` and `false` are separated by every observer
class, through the identity context. -/
theorem not_relEquiv_true_false (K : AdmissibleClass rules) {t u : Closed .bool}
    (valueT : t.value = true) (valueU : u.value = false) :
    ¬ K.RelEquiv observations ⟨.bool, t⟩ ⟨.bool, u⟩ := by
  intro related
  have agree := (relEquiv_iff K _ _).mp related Context.identity K.identity_mem .isTrue
  change t.value = true ↔ u.value = true at agree
  rw [valueU] at agree
  exact Bool.false_ne_true (agree.mp valueT)

/-- **Control: identified now, different later.**  The data-eliminator view
identifies the identity on booleans with negation, and applying both to `tt`
separates them, so this view does not support application to `tt`. -/
theorem dataEliminators_not_support_applyTrue :
    ¬ Supports (stageClass observations dataEliminators) (rules.plug applyTrue) := by
  apply not_supports_of_split
    (x := ⟨_, Examples.idBool⟩) (y := ⟨_, Examples.notBool⟩)
  · exact (stageClass_eq_iff observations dataEliminators _ _).mpr too_few_observers.1
  · rw [plug_applyTrue, plug_applyTrue]
    intro same
    exact not_relEquiv_true_false dataEliminators rfl rfl
      ((stageClass_eq_iff observations dataEliminators _ _).mp same)

/-- Hence adjoining application to `tt` to the data eliminators is not
conservative. -/
theorem applyTrue_not_conservative :
    ¬ ∀ left right, (dataEliminators ⊔ generatedBy {applyTrue}).RelEquiv observations
        left right ↔ dataEliminators.RelEquiv observations left right := fun conservative =>
  dataEliminators_not_support_applyTrue
    ((conservative_iff_supported observations dataEliminators {applyTrue}).mp conservative
      applyTrue rfl)

end Eliminators

/-! ## Nondeterministic updates -/

section Relational

variable {X : Type uX} {Y : Type uY}

/-- **A view supports a nondeterministic update** when some abstract relation
simulates every detailed step (forth) and every abstract step out of the view
of a state is the view of a step of that state (back).  The abstract
relation is a relation, so no abstract update function has to be chosen. -/
def RelSupports (view : X → Y) (step : X → X → Prop) : Prop :=
  ∃ step' : Y → Y → Prop, (∀ x x', step x x' → step' (view x) (view x')) ∧
    ∀ x y', step' (view x) y' → ∃ x', step x x' ∧ view x' = y'

/-- The kernel of the view is a bisimulation for the steps. -/
def KernelBisimulation (view : X → Y) (step : X → X → Prop) : Prop :=
  ∀ ⦃x₀ x : X⦄, view x₀ = view x → ∀ ⦃x₀' : X⦄, step x₀ x₀' →
    ∃ x', step x x' ∧ view x' = view x₀'

/-- **A view supports a nondeterministic update exactly when its kernel is a
bisimulation for it**; the abstract relation can then be taken to be the
image of the steps. -/
theorem relSupports_iff (view : X → Y) (step : X → X → Prop) :
    RelSupports view step ↔ KernelBisimulation view step := by
  constructor
  · rintro ⟨step', forth, back⟩ x₀ x same x₀' moved
    have abstract := forth x₀ x₀' moved
    rw [same] at abstract
    exact back x (view x₀') abstract
  · intro bisimulation
    refine ⟨fun y y' => ∃ x x', view x = y ∧ view x' = y' ∧ step x x',
      fun x x' moved => ⟨x, x', rfl, rfl, moved⟩, ?_⟩
    rintro x y' ⟨x₀, x₀', same, rfl, moved⟩
    exact bisimulation same moved

/-- For a deterministic update, exact support gives support of its graph. -/
theorem Supports.relSupports {view : X → Y} {f : X → X} (supported : Supports view f) :
    RelSupports view fun x x' => x' = f x := by
  rw [relSupports_iff]
  rintro x₀ x same x₀' rfl
  exact ⟨f x, rfl, (supported.constant same).symm⟩

end Relational

section RelationalStages

open Mettapedia.GSLT
open Mettapedia.GSLT.MinimalEnablingContext
open Mettapedia.GSLT.AdmissibleContextCongruence
open Mettapedia.GSLT.AdmissibleContextCongruence.AdmissibleClass

universe uS uContext uRule uAtom

variable {S : GSLT.{uS}} {rules : ContextualRules.{uContext, uRule} S}
  (observations : ContextualRules.Observations.{uAtom} S)

/-- **Every admissible interaction is a supported nondeterministic update of
the observer stage**: the stage view of a class supports the reductions of
every context of the class, because its equivalence is a bisimulation of the
saturated system. -/
theorem relSupports_stageClass_of_admissible (D : AdmissibleClass rules)
    {context : rules.Context} (admissible : D.Admissible context) :
    RelSupports (stageClass observations D) fun t t' => S.Step (rules.plug context t) t' := by
  rw [relSupports_iff]
  intro x₀ x same x₀' moved
  obtain ⟨x', moved', related⟩ := bisimilar_forward
    ((stageClass_eq_iff observations D _ _).mp same) ⟨context, admissible⟩ moved
  exact ⟨x', moved', (stageClass_eq_iff observations D _ _).mpr
    (D.relEquiv_symm observations related)⟩

end RelationalStages

namespace Eliminators

open Mettapedia.GSLT.EliminatorObservers
open Mettapedia.GSLT.AdmissibleContextCongruence
open Mettapedia.GSLT.AdmissibleContextCongruence.AdmissibleClass
open Mettapedia.TypeTheory.Calculi.BooleanSTLC

/-- **Control: observation by evaluation forgets steps.**  The eliminator view
identifies `(λx. x) tt` with `tt`; the first takes a root β-step and the
second takes none, so this view does not support root β-reduction as a
nondeterministic update. -/
theorem eliminators_not_relSupports_rootBeta :
    ¬ RelSupports (stageClass observations eliminators) RootBeta := by
  intro supported
  have bisimulation := (relSupports_iff (stageClass observations eliminators) RootBeta).mp
    supported
  have same : stageClass observations eliminators ⟨.bool, .app Examples.idBool .tt⟩ =
      stageClass observations eliminators ⟨.bool, .tt⟩ :=
    (stageClass_eq_iff observations eliminators _ _).mpr
      ((relEquiv_eliminators_iff _ _).mpr betaEliminators_separates_redex.1)
  obtain ⟨_, moved, _⟩ := bisimulation same (RootBeta.beta (.var .zero) .tt)
  exact no_step_tt _ moved

end Eliminators

/-! ## Approximate squares -/

section Approximate

variable {X : Type uX} {X' : Type uX'} {X'' : Type uX''}
  {Y : Type uY} {Y' : Type uY'} {Y'' : Type uY''} {D : Type uD}

/-- **The square commutes up to `ε`** for the distance `dist` on the target
view. -/
def ApproxSquare [LE D] (dist : Y' → Y' → D) (view : X → Y) (view' : X' → Y') (f : X → X')
    (f' : Y → Y') (ε : D) : Prop :=
  ∀ x, dist (view' (f x)) (f' (view x)) ≤ ε

/-- An exact square commutes up to `0`. -/
theorem ApproxSquare.of_exact [Zero D] [Preorder D] {dist : Y' → Y' → D}
    (dist_self : ∀ y, dist y y = 0)
    {view : X → Y} {view' : X' → Y'} {f : X → X'} {f' : Y → Y'}
    (exact : ∀ x, view' (f x) = f' (view x)) : ApproxSquare dist view view' f f' 0 := by
  intro x
  rw [exact x, dist_self]

/-- A square within `ε` is within any larger bound. -/
theorem ApproxSquare.mono [Preorder D] {dist : Y' → Y' → D} {view : X → Y} {view' : X' → Y'}
    {f : X → X'} {f' : Y → Y'} {ε δ : D} (square : ApproxSquare dist view view' f f' ε)
    (le : ε ≤ δ) : ApproxSquare dist view view' f f' δ :=
  fun x => (square x).trans le

/-- **Approximate squares compose.**  The error of the composite is the error
of the second square plus the first error passed through the modulus `ω` of
the second abstract update. -/
theorem ApproxSquare.comp [AddCommMonoid D] [PartialOrder D] [IsOrderedAddMonoid D]
    {dist' : Y' → Y' → D} {dist'' : Y'' → Y'' → D}
    (triangle : ∀ a b c, dist'' a c ≤ dist'' a b + dist'' b c)
    {view : X → Y} {view' : X' → Y'} {view'' : X'' → Y''}
    {f : X → X'} {g : X' → X''} {f' : Y → Y'} {g' : Y' → Y''} {ε δ : D}
    {ω : D → D} (ω_mono : Monotone ω)
    (modulus : ∀ a b, dist'' (g' a) (g' b) ≤ ω (dist' a b))
    (first : ApproxSquare dist' view view' f f' ε)
    (second : ApproxSquare dist'' view' view'' g g' δ) :
    ApproxSquare dist'' view view'' (g ∘ f) (g' ∘ f') (δ + ω ε) := by
  intro x
  calc dist'' (view'' (g (f x))) (g' (f' (view x)))
      ≤ dist'' (view'' (g (f x))) (g' (view' (f x))) +
          dist'' (g' (view' (f x))) (g' (f' (view x))) := triangle _ _ _
    _ ≤ δ + ω ε := add_le_add (second (f x)) ((modulus _ _).trans (ω_mono (first x)))

/-- **Errors add along nonexpansive abstract updates.** -/
theorem ApproxSquare.comp_nonexpansive [AddCommMonoid D] [PartialOrder D]
    [IsOrderedAddMonoid D] {dist' : Y' → Y' → D} {dist'' : Y'' → Y'' → D}
    (triangle : ∀ a b c, dist'' a c ≤ dist'' a b + dist'' b c)
    {view : X → Y} {view' : X' → Y'} {view'' : X'' → Y''}
    {f : X → X'} {g : X' → X''} {f' : Y → Y'} {g' : Y' → Y''} {ε δ : D}
    (nonexpansive : ∀ a b, dist'' (g' a) (g' b) ≤ dist' a b)
    (first : ApproxSquare dist' view view' f f' ε)
    (second : ApproxSquare dist'' view' view'' g g' δ) :
    ApproxSquare dist'' view view'' (g ∘ f) (g' ∘ f') (δ + ε) :=
  ApproxSquare.comp triangle (ω := id) monotone_id nonexpansive first second

/-- Iterates of a nonexpansive map are nonexpansive. -/
theorem iterate_nonexpansive [Preorder D] {dist : Y → Y → D} {f' : Y → Y}
    (nonexpansive : ∀ a b, dist (f' a) (f' b) ≤ dist a b) :
    ∀ (n : ℕ) (a b : Y), dist (f'^[n] a) (f'^[n] b) ≤ dist a b
  | 0, _, _ => le_rfl
  | n + 1, a, b => by
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact (iterate_nonexpansive nonexpansive n (f' a) (f' b)).trans (nonexpansive a b)

/-- **`n` steps along a nonexpansive abstract update err by at most
`n • ε`.** -/
theorem ApproxSquare.iterate [AddCommMonoid D] [PartialOrder D] [IsOrderedAddMonoid D]
    {dist : Y → Y → D} (dist_self : ∀ y, dist y y = 0)
    (triangle : ∀ a b c, dist a c ≤ dist a b + dist b c) {view : X → Y} {f : X → X}
    {f' : Y → Y} {ε : D} (nonexpansive : ∀ a b, dist (f' a) (f' b) ≤ dist a b)
    (square : ApproxSquare dist view view f f' ε) :
    ∀ n : ℕ, ApproxSquare dist view view f^[n] f'^[n] (n • ε)
  | 0 => by
    rw [zero_smul]
    exact ApproxSquare.of_exact dist_self fun _ => rfl
  | n + 1 => by
    have composite := ApproxSquare.comp_nonexpansive triangle
      (iterate_nonexpansive nonexpansive n) square
      (ApproxSquare.iterate dist_self triangle nonexpansive square n)
    rw [Function.iterate_succ, Function.iterate_succ, succ_nsmul]
    exact composite

end Approximate

/-! ### The d-calculus tolerances -/

section Tolerance

open Mettapedia.Cybernetics.DistinctionCalculus

variable {X : Type uX} {X' : Type uX'} {X'' : Type uX''}
  {Y : Type uY} {Y' : Type uY'} {Y'' : Type uY''}

/-- **With graded observers, expansion adds.**  If the second abstract update
expands tolerance distances by at most `δ` (one-sided preservation grade
`1 − δ`), the composite square errs by at most the two errors plus `δ`. -/
theorem ApproxSquare.comp_tolerance {a : Tolerance Y'} {b : Tolerance Y''} (metric : b.Metric)
    {view : X → Y} {view' : X' → Y'} {view'' : X'' → Y''}
    {f : X → X'} {g : X' → X''} {f' : Y → Y'} {g' : Y' → Y''} {ε ε' δ : ℚ}
    (expands : Tolerance.ExpandsAtMost a b g' δ)
    (first : ApproxSquare a.distance view view' f f' ε)
    (second : ApproxSquare b.distance view' view'' g g' ε') :
    ApproxSquare b.distance view view'' (g ∘ f) (g' ∘ f') (ε' + (ε + δ)) :=
  ApproxSquare.comp metric (ω := fun t => t + δ) (fun _ _ le => add_le_add le (le_refl δ))
    expands first second

end Tolerance

/-! ### Controls over the natural numbers -/

/-- The distance of natural numbers. -/
def natDist (a b : ℕ) : ℕ :=
  (a - b) + (b - a)

theorem natDist_self (a : ℕ) : natDist a a = 0 := by
  unfold natDist
  omega

theorem natDist_triangle (a b c : ℕ) : natDist a c ≤ natDist a b + natDist b c := by
  unfold natDist
  omega

namespace Succ

/-- The detailed step adds one; the abstract step does nothing. -/
def step (x : ℕ) : ℕ :=
  x + 1

theorem square : ApproxSquare natDist id id step id 1 := by
  intro x
  change natDist (x + 1) x ≤ 1
  unfold natDist
  omega

theorem step_iterate (n x : ℕ) : step^[n] x = x + n := by
  induction n generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih]
    unfold step
    omega

/-- **The additive bound is attained**: after `n` steps the error is `n`. -/
theorem error_iterate (n x : ℕ) : natDist (step^[n] x) (id^[n] x) = n := by
  rw [step_iterate, Function.iterate_id]
  unfold natDist
  change x + n - x + (x - (x + n)) = n
  omega

/-- **"Within `ε`" is not closed under composition**: each step is within
`1`, two steps are not. -/
theorem not_within_one : ¬ ApproxSquare natDist id id (step ∘ step) (id ∘ id) 1 := by
  intro within
  have bound := within 0
  change natDist 2 0 ≤ 1 at bound
  unfold natDist at bound
  omega

end Succ

namespace Doubling

/-- The detailed step doubles and adds one; the abstract step only doubles. -/
def step (x : ℕ) : ℕ :=
  2 * x + 1

/-- The abstract step. -/
def abstract (y : ℕ) : ℕ :=
  2 * y

theorem square : ApproxSquare natDist id id step abstract 1 := by
  intro x
  change natDist (2 * x + 1) (2 * x) ≤ 1
  unfold natDist
  omega

/-- The abstract step is not nonexpansive: it doubles distances. -/
theorem abstract_doubles (a b : ℕ) : natDist (abstract a) (abstract b) = 2 * natDist a b := by
  unfold natDist abstract
  omega

theorem step_iterate_zero (n : ℕ) : step^[n] 0 = 2 ^ n - 1 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, pow_succ]
    have positive : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    unfold step
    omega

theorem abstract_iterate_zero (n : ℕ) : abstract^[n] 0 = 0 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    rfl

/-- **Error growth**: one unit of error per step becomes `2 ^ n - 1` after `n`
steps. -/
theorem error_iterate (n : ℕ) : natDist (step^[n] 0) (abstract^[n] 0) = 2 ^ n - 1 := by
  rw [step_iterate_zero, abstract_iterate_zero]
  unfold natDist
  omega

/-- **Beyond the additive bound**: after two steps the error exceeds `2 • 1`. -/
theorem exceeds_additive :
    ¬ ApproxSquare natDist id id step^[2] abstract^[2] (2 • 1) := by
  intro within
  have bound := within 0
  change natDist (step^[2] 0) (abstract^[2] 0) ≤ 2 • 1 at bound
  rw [error_iterate] at bound
  change 3 ≤ 2 at bound
  omega

end Doubling

/-! ## Optimisation promises -/

section Promises

variable {X : Type uX} {A : Type uA} {C : Type uC}

/-- **Exact preservation** of a readout by an optimisation. -/
def PreservesExactly (readout : X → A) (opt : X → X) : Prop :=
  ∀ x, readout (opt x) = readout x

/-- **Improvement**: the same answers, with cost no larger. -/
def Improves [Preorder C] (answer : X → A) (cost : X → C) (opt : X → X) : Prop :=
  ∀ x, answer (opt x) = answer x ∧ cost (opt x) ≤ cost x

/-- **Approximation** within `ε` under a stated distance on answers. -/
def Approximates {D : Type uD} [LE D] (dist : A → A → D) (answer : X → A) (ε : D)
    (opt : X → X) : Prop :=
  ∀ x, dist (answer (opt x)) (answer x) ≤ ε

/-- Exact preservation of answers and cost implies improvement. -/
theorem PreservesExactly.improves [Preorder C] {answer : X → A} {cost : X → C} {opt : X → X}
    (answers : PreservesExactly answer opt) (costs : PreservesExactly cost opt) :
    Improves answer cost opt :=
  fun x => ⟨answers x, (costs x).le⟩

/-- Improvement preserves answers exactly. -/
theorem Improves.preservesAnswers [Preorder C] {answer : X → A} {cost : X → C} {opt : X → X}
    (improves : Improves answer cost opt) : PreservesExactly answer opt :=
  fun x => (improves x).1

/-- Improvements compose. -/
theorem Improves.comp [Preorder C] {answer : X → A} {cost : X → C} {first second : X → X}
    (improvesFirst : Improves answer cost first) (improvesSecond : Improves answer cost second) :
    Improves answer cost (second ∘ first) := fun x =>
  ⟨((improvesSecond (first x)).1).trans (improvesFirst x).1,
    ((improvesSecond (first x)).2).trans (improvesFirst x).2⟩

/-- Exact preservation of answers is approximation within `0`. -/
theorem PreservesExactly.approximates {D : Type uD} [AddCommMonoid D] [PartialOrder D]
    {dist : A → A → D} (dist_self : ∀ a, dist a a = 0) {answer : X → A} {opt : X → X}
    (exact : PreservesExactly answer opt) : Approximates dist answer 0 opt := by
  intro x
  rw [exact x, dist_self]

/-- **Approximations compose, with added bounds.** -/
theorem Approximates.comp {D : Type uD} [AddCommMonoid D] [PartialOrder D]
    [IsOrderedAddMonoid D] {dist : A → A → D}
    (triangle : ∀ a b c, dist a c ≤ dist a b + dist b c)
    {answer : X → A} {first second : X → X} {ε δ : D}
    (approxFirst : Approximates dist answer ε first)
    (approxSecond : Approximates dist answer δ second) :
    Approximates dist answer (δ + ε) (second ∘ first) := fun x =>
  (triangle _ _ _).trans (add_le_add (approxSecond (first x)) (approxFirst x))

/-- A **lax square**: detailed-then-view is at most view-then-abstract. -/
def LaxSquare {Y : Type uY} {Y' : Type uY'} {X' : Type uX'} [LE Y'] (view : X → Y)
    (view' : X' → Y') (f : X → X') (f' : Y → Y') : Prop :=
  ∀ x, view' (f x) ≤ f' (view x)

/-- **Lax squares compose along monotone abstract updates.** -/
theorem LaxSquare.comp {Y : Type uY} {Y' : Type uY'} {Y'' : Type uY''} {X' : Type uX'}
    {X'' : Type uX''} [Preorder Y''] [Preorder Y'] {view : X → Y} {view' : X' → Y'}
    {view'' : X'' → Y''} {f : X → X'} {g : X' → X''} {f' : Y → Y'} {g' : Y' → Y''}
    (monotone : Monotone g') (first : LaxSquare view view' f f')
    (second : LaxSquare view' view'' g g') : LaxSquare view view'' (g ∘ f) (g' ∘ f') :=
  fun x => (second (f x)).trans (monotone (first x))

/-- An answer with its cost, ordered by: the same answer and no larger cost. -/
structure Costed (A : Type uA) (C : Type uC) where
  /-- The answer. -/
  answer : A
  /-- The cost of computing it. -/
  cost : C

instance [Preorder C] : Preorder (Costed A C) where
  le first second := first.answer = second.answer ∧ first.cost ≤ second.cost
  le_refl _ := ⟨rfl, le_rfl⟩
  le_trans _ _ _ first second := ⟨first.1.trans second.1, first.2.trans second.2⟩

/-- **Improvement is a lax square** in the preorder of costed answers, with
the identity as abstract update. -/
theorem improves_iff_laxSquare [Preorder C] (answer : X → A) (cost : X → C) (opt : X → X) :
    Improves answer cost opt ↔
      LaxSquare (fun x => (⟨answer x, cost x⟩ : Costed A C))
        (fun x => (⟨answer x, cost x⟩ : Costed A C)) opt id :=
  Iff.rfl

end Promises

/-! ### Controls: constant folding and a dropped increment -/

namespace Folding

/-- Arithmetic expressions over variables. -/
inductive Expr where
  | lit (n : ℕ)
  | var (index : ℕ)
  | add (left right : Expr)
  deriving DecidableEq

namespace Expr

/-- The value of an expression in an environment. -/
def value (env : ℕ → ℕ) : Expr → ℕ
  | lit n => n
  | var index => env index
  | add left right => left.value env + right.value env

/-- **The cost model**: the evaluator performs one addition per `add` node. -/
def cost : Expr → ℕ
  | lit _ => 0
  | var _ => 0
  | add left right => left.cost + right.cost + 1

/-- Add two folded expressions, folding when both are literals. -/
def addFolded : Expr → Expr → Expr
  | lit a, lit b => lit (a + b)
  | left, right => add left right

/-- **Constant folding**, bottom-up. -/
def fold : Expr → Expr
  | lit n => lit n
  | var index => var index
  | add left right => addFolded left.fold right.fold

theorem value_addFolded (env : ℕ → ℕ) (left right : Expr) :
    (addFolded left right).value env = left.value env + right.value env := by
  cases left <;> cases right <;> rfl

theorem cost_addFolded_le (left right : Expr) :
    (addFolded left right).cost ≤ left.cost + right.cost + 1 := by
  cases left <;> cases right <;> simp only [addFolded, cost] <;> omega

theorem value_fold (env : ℕ → ℕ) (e : Expr) : e.fold.value env = e.value env := by
  induction e with
  | lit n => rfl
  | var index => rfl
  | add left right ihLeft ihRight =>
    change (addFolded left.fold right.fold).value env = _
    rw [value_addFolded, ihLeft, ihRight]
    rfl

theorem cost_fold_le (e : Expr) : e.fold.cost ≤ e.cost := by
  induction e with
  | lit n => exact le_rfl
  | var index => exact le_rfl
  | add left right ihLeft ihRight =>
    change (addFolded left.fold right.fold).cost ≤ left.cost + right.cost + 1
    have := cost_addFolded_le left.fold right.fold
    omega

/-- Drop a trailing `+ 1` at the root. -/
def dropIncrement : Expr → Expr
  | add left (lit 1) => left
  | e => e

end Expr

open Expr

/-- **Constant folding is an improvement**: the same value in every
environment, with no more additions. -/
theorem fold_improves : Improves (fun e : Expr => fun env => e.value env) cost fold :=
  fun e => ⟨funext fun env => value_fold env e, cost_fold_le e⟩

/-- **But it does not preserve cost exactly**: `1 + 2` costs one addition,
its folding costs none.  Requiring exact equality of the cost observer would
forbid this optimisation. -/
theorem fold_not_preserves_cost : ¬ PreservesExactly cost fold := by
  intro exact
  have same := exact (add (lit 1) (lit 2))
  change (0 : ℕ) = 1 at same
  omega

/-- Folding leaves an addition with a variable unchanged. -/
theorem fold_keeps_variable_sum : fold (add (var 0) (lit 2)) = add (var 0) (lit 2) :=
  rfl

/-- **Dropping a trailing increment approximates within `1`.** -/
theorem dropIncrement_approximates (env : ℕ → ℕ) :
    Approximates natDist (fun e : Expr => e.value env) 1 dropIncrement := by
  intro e
  change natDist (e.dropIncrement.value env) (e.value env) ≤ 1
  have unchanged : ∀ a : ℕ, natDist a a ≤ 1 := fun a => by
    rw [natDist_self]
    exact Nat.zero_le 1
  match e with
  | lit n => exact unchanged _
  | var index => exact unchanged _
  | add left (lit 1) =>
    change natDist (left.value env) (left.value env + 1) ≤ 1
    unfold natDist
    omega
  | add left (lit 0) => exact unchanged _
  | add left (lit (n + 2)) => exact unchanged _
  | add left (var index) => exact unchanged _
  | add left (add left' right') => exact unchanged _

/-- **Approximation is not improvement**: dropping the increment changes the
answer of `x₀ + 1`. -/
theorem dropIncrement_not_improves :
    ¬ Improves (fun e : Expr => fun env => e.value env) cost dropIncrement := by
  intro improves
  have same := congrFun (improves (add (var 0) (lit 1))).1 fun _ => 0
  change (0 : ℕ) = 0 + 1 at same
  omega

end Folding

end Mettapedia.GSLT.Scope
