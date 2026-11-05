import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsRounds
import Mettapedia.GSLT.Causality.TraceCostValuation
import Mettapedia.GSLT.Core.SpendLiftInterchange
import Mettapedia.Algebra.WorkSpan

/-!
# Annotations of runs: functors out of the run category, and how they weave

## The base

The arrows of `OccurrenceHistory.OccurrenceCat P` are the runs of a presentation: finite paths
of occurrences, each a site with its evidence. For the candidate step the sites are firings,
which carry their occurrence identities (`AnnotatedRuns.presentation`). Parallel composition
appears as commuting squares: a tile system names the squares whose two routes are one
concurrent step, and `EventConcurrency.TraceCat` is the run category modulo those squares.
Two tile systems exist for the candidate step: the static one of
`AnnotatedRuns.siteIndependence` and the contextual one of `AnnotatedRuns.concurrency`.

## The finest tracing and its universal properties

* **The free run category** (`ofGrade`, `account_ext`): an account of runs in any monoid is
  determined by its values on single firings, and every assignment of values to firings
  extends to one. The occurrence path is therefore the finest tracing: every annotation that
  is a functor reads it.
* **The trace quotient** (`account_factors_iff`, `traced_unique`): an account factors through
  the traces of a tile system exactly when it agrees on the two routes of every tile, and then
  uniquely. Traces are the finest tracing that respects the interchange squares.
* **In the erasure lattice** (`trace_le_iff`): the trace erasure is the least erasure of
  histories that identifies the routes of every tile.

## Weaving

The product of two accounts is an account (`RunAccount.prod`); it factors through traces
exactly when both factors do (`prod_factors_iff`). On the decorated theories the history and
cost decorations of the candidate step weave in either order into one decoration over the
product monoid (`history_cost_interchange`, from `SpendLiftInterchange`), because neither reads
the other's accumulator.

## Which annotations respect the interchange squares

* **Strictly:** site accounts into commutative monoids, such as cost, grades in a commutative
  semiring and the bag of firings (`siteAccount_factors_static`,
  `AnnotatedRuns.siteValuation_descends`).
* **Exactly when the swapped grades commute:** site accounts into any monoid
  (`AnnotatedRuns.siteValuation_descends_iff`).
* **Laxly:** the work/span receipt of a round: every order has the same sequential receipt,
  and the parallel receipt lies below it with equal work (`round_receipts`).
* **Not at all:** the ordered word of firings (`Controls.history_not_traced`) and a cost that
  reads the space it fires in (`Controls.space_cost_not_traced`).
-/

set_option autoImplicit false

open CategoryTheory

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

open Mettapedia.Effects (RunAccount)
open Mettapedia.GSLT (GSLT)
open Mettapedia.GSLT.Core.InteractionEvent (InteractionPresentation)
open Mettapedia.GSLT.Causality.OccurrenceHistory (Occurrence OccurrencePath OccurrenceCat
  OccurrenceValuation)
open Mettapedia.GSLT.Causality.EventConcurrency (TileSystem TraceEq Trace TraceCat)
open Mettapedia.GSLT.Causality.TraceCostValuation (traceFunctor)

/-! ## Universal properties of the run category and of its traces -/

section Universal

universe uSite uEvent uTile w w'

variable {theory : GSLT} {P : InteractionPresentation.{uSite, uEvent} theory}
  {M : Type w} [Monoid M]

/-- The run of one occurrence. -/
def single {s t : theory.Term} (o : Occurrence P s t) : OccurrencePath P s t :=
  .cons o (.refl t)

/-- A grade of occurrences in a monoid, read as an additive valuation. -/
def gradeValuation (grade : ∀ {s t : theory.Term}, Occurrence P s t → M) :
    OccurrenceValuation P (Additive M) where
  grade o := Additive.ofMul (grade o)

/-- **Every grade of occurrences extends to an account of runs.** -/
def ofGrade (grade : ∀ {s t : theory.Term}, Occurrence P s t → M) :
    RunAccount (OccurrenceCat P) M where
  of path := Additive.toMul ((gradeValuation grade).onPath path)
  of_id _ := rfl
  of_comp first second :=
    congrArg Additive.toMul ((gradeValuation grade).onPath_append first second)

theorem ofGrade_single (grade : ∀ {s t : theory.Term}, Occurrence P s t → M)
    {s t : theory.Term} (o : Occurrence P s t) : (ofGrade grade).of (single o) = grade o := by
  change Additive.toMul (Additive.ofMul (grade o) + 0) = grade o
  simp

/-- **Accounts of runs are determined by single occurrences**: the run category is free. -/
theorem account_ext {first second : RunAccount (OccurrenceCat P) M}
    (same : ∀ {s t : theory.Term} (o : Occurrence P s t), first.of (single o) = second.of (single o)) :
    first = second := by
  have paths : ∀ {s t : theory.Term} (p : OccurrencePath P s t), first.of p = second.of p := by
    intro s t p
    induction p with
    | refl t => exact (first.of_id t).trans (second.of_id t).symm
    | cons o rest ih =>
        calc first.of (OccurrencePath.cons o rest) = first.of (single o) * first.of rest :=
              first.of_comp (single o) rest
          _ = second.of (single o) * second.of rest := by rw [same o, ih]
          _ = second.of (OccurrencePath.cons o rest) := (second.of_comp (single o) rest).symm
  exact RunAccount.ext (by funext s t p; exact paths p)

/-- A cast of the end of a run does not change its account. -/
theorem of_cast (account : RunAccount (OccurrenceCat P) M) {s t t' : theory.Term} (same : t = t')
    (p : OccurrencePath P s t) :
    account.of (same ▸ p : OccurrencePath P s t') = account.of p := by
  subst same
  rfl

/-- The second route of an independence tile is its swapped path, cast to the common end. -/
theorem of_pathSwap' {indep : Mettapedia.GSLT.Causality.OccurrenceHistory.SiteIndependence P}
    {s : theory.Term} (account : RunAccount (OccurrenceCat P) M)
    (tile : Mettapedia.GSLT.Causality.OccurrenceHistory.IndependenceTile P indep s) :
    account.of tile.pathSwap' = account.of tile.pathSwap := by
  unfold Mettapedia.GSLT.Causality.OccurrenceHistory.IndependenceTile.pathSwap'
  rw [of_cast]

variable (T : TileSystem.{uSite, uEvent, uTile} P)

/-- An account that agrees on the two routes of every tile is constant on traces. -/
theorem of_traceEq (account : RunAccount (OccurrenceCat P) M)
    (tiles : ∀ {s : theory.Term} (tile : T.Tile s),
      account.of (T.route tile) = account.of (T.swapped tile))
    {s t : theory.Term} {p q : OccurrencePath P s t} (related : TraceEq T p q) :
    account.of p = account.of q := by
  induction related with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ first second => exact first.trans second
  | tile tile => exact tiles tile
  | cong_left pre _ ih =>
      exact (account.of_comp pre _).trans ((congrArg _ ih).trans (account.of_comp pre _).symm)
  | cong_right post _ ih =>
      exact (account.of_comp _ post).trans
        ((congrArg (· * account.of post) ih).trans (account.of_comp _ post).symm)

/-- **The universal property of traces.** An account of runs factors through the traces of a
tile system exactly when it agrees on the two routes of every tile. -/
theorem account_factors_iff (account : RunAccount (OccurrenceCat P) M) :
    (∃ traced : RunAccount (TraceCat T) M, traced.comap (traceFunctor T) = account) ↔
      ∀ {s : theory.Term} (tile : T.Tile s),
        account.of (T.route tile) = account.of (T.swapped tile) := by
  constructor
  · rintro ⟨traced, rfl⟩ s tile
    change traced.of (Trace.mk (T.route tile)) = traced.of (Trace.mk (T.swapped tile))
    rw [Trace.mk_sound (.tile tile)]
  · intro tiles
    refine ⟨⟨fun trace => Quotient.liftOn trace account.of
      (fun _ _ related => of_traceEq T account tiles related), ?_, ?_⟩, ?_⟩
    · intro state
      exact account.of_id state
    · intro source middle target first second
      refine Quotient.inductionOn first fun p => ?_
      refine Quotient.inductionOn second fun q => ?_
      exact account.of_comp p q
    · exact RunAccount.ext (by funext s t p; rfl)

/-- **The factorization through traces is unique.** -/
theorem traced_unique {first second : RunAccount (TraceCat T) M}
    (same : first.comap (traceFunctor T) = second.comap (traceFunctor T)) : first = second := by
  apply RunAccount.ext
  funext s t trace
  refine Quotient.inductionOn trace fun p => ?_
  exact congrArg (fun account : RunAccount (OccurrenceCat P) M => account.of p) same

/-- **Weaving.** The product of two accounts factors through traces exactly when both do. -/
theorem prod_factors_iff {N : Type w} [Monoid N] (first : RunAccount (OccurrenceCat P) M)
    (second : RunAccount (OccurrenceCat P) N) :
    (∀ {s : theory.Term} (tile : T.Tile s),
        (first.prod second).of (T.route tile) = (first.prod second).of (T.swapped tile)) ↔
      (∀ {s : theory.Term} (tile : T.Tile s),
          first.of (T.route tile) = first.of (T.swapped tile)) ∧
        ∀ {s : theory.Term} (tile : T.Tile s),
          second.of (T.route tile) = second.of (T.swapped tile) :=
  ⟨fun both => ⟨fun tile => congrArg Prod.fst (both tile), fun tile => congrArg Prod.snd (both tile)⟩,
    fun both {_} tile => Prod.ext (both.1 tile) (both.2 tile)⟩

/-- **The trace erasure is the least erasure of histories that respects the tiles.** -/
theorem trace_le_iff (erasure : Mettapedia.GSLT.Causality.HistoryMonad.Erasure P) :
    Mettapedia.GSLT.Causality.HistoryMonad.Erasure.trace T ≤ erasure ↔
      ∀ {s : theory.Term} (tile : T.Tile s), erasure.rel (T.route tile) (T.swapped tile) := by
  constructor
  · intro below s tile
    exact (Mettapedia.GSLT.Causality.HistoryMonad.Erasure.le_iff.mp below).apply _ _ (.tile tile)
  · intro tiles
    refine Mettapedia.GSLT.Causality.HistoryMonad.Erasure.le_iff.mpr ⟨fun p q related => ?_⟩
    induction related with
    | refl p => exact erasure.equivalence.refl p
    | symm _ ih => exact erasure.equivalence.symm ih
    | trans _ _ first second => exact erasure.equivalence.trans first second
    | tile tile => exact tiles tile
    | cong_left pre _ ih => exact erasure.append (erasure.equivalence.refl pre) ih
    | cong_right post _ ih => exact erasure.append ih (erasure.equivalence.refl post)

end Universal

/-! ## The annotations of the candidate step -/

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

section Annotations

variable (A : SubstitutionAction T S) (label : O → T)

/-- The run category of the candidate step. -/
abbrev Runs := OccurrenceCat (presentation A label)

/-- The static traces: runs modulo the swaps of `siteIndependence`. -/
abbrev StaticTraces :=
  TraceCat (Mettapedia.GSLT.Causality.EventConcurrency.siteTiles (siteIndependence A label))

/-- The contextual traces: runs modulo the rounds of two of `concurrency`. -/
abbrev ContextualTraces := TraceCat (concurrency A label).tiles

/-- **The history annotation**: the ordered word of firings. -/
def historyAccount : RunAccount (Runs A label) (FreeMonoid (Firing T S O)) :=
  ofGrade fun o => FreeMonoid.of o.site

/-- **A site annotation**: each firing charged by itself, in a monoid. Cost, grades and counts
are site annotations. -/
def siteAccount {M : Type*} [Monoid M] (grade : Firing T S O → M) : RunAccount (Runs A label) M :=
  ofGrade fun o => grade o.site

/-- **Site annotations into a commutative monoid respect the static interchange squares.** -/
theorem siteAccount_factors_static {M : Type*} [CommMonoid M] (grade : Firing T S O → M) :
    ∃ traced : RunAccount (StaticTraces A label) M,
      traced.comap (traceFunctor _) = siteAccount A label grade := by
  refine (account_factors_iff _ _).mpr ?_
  intro s tile
  change (siteAccount A label grade).of tile.path = (siteAccount A label grade).of tile.pathSwap'
  unfold Mettapedia.GSLT.Causality.OccurrenceHistory.IndependenceTile.pathSwap'
  rw [of_cast]
  change grade tile.first.site * (grade tile.second.site * 1) =
    grade tile.altFirst.site * (grade tile.altSecond.site * 1)
  rw [tile.sameFirst, tile.sameSecond, mul_one, mul_one, mul_comm]

/-- **Site annotations into a commutative monoid respect the contextual interchange squares.** -/
theorem siteAccount_factors_contextual {M : Type*} [CommMonoid M] (grade : Firing T S O → M) :
    ∃ traced : RunAccount (ContextualTraces A label) M,
      traced.comap (traceFunctor _) = siteAccount A label grade := by
  refine (account_factors_iff _ _).mpr ?_
  intro s pair
  change (siteAccount A label grade).of (pair.route (concurrency A label)) =
    (siteAccount A label grade).of (pair.swapped (concurrency A label))
  unfold Mettapedia.GSLT.Causality.EventConcurrency.Concurrency.Pair.swapped
  rw [of_cast]
  change grade pair.first.site * (grade pair.second.site * 1) =
    grade pair.second.site * (grade pair.first.site * 1)
  rw [mul_one, mul_one, mul_comm]

end Annotations

/-! ## Parallel receipts are lax -/

section Receipts

variable (A : SubstitutionAction T S) (label : O → T)

theorem parallelAll_le_sequentialAll : ∀ branches : List Mettapedia.Algebra.WorkSpan,
    Mettapedia.Algebra.WorkSpan.parallelAll branches ≤
      Mettapedia.Algebra.WorkSpan.sequentialAll branches
  | [] => le_refl _
  | head :: tail =>
      le_trans (Mettapedia.Algebra.WorkSpan.parallel_le_sequential head _)
        (Mettapedia.Algebra.WorkSpan.sequential_mono (le_refl head)
          (parallelAll_le_sequentialAll tail))

theorem sequentialAll_perm {first second : List Mettapedia.Algebra.WorkSpan}
    (perm : first.Perm second) :
    Mettapedia.Algebra.WorkSpan.sequentialAll first =
      Mettapedia.Algebra.WorkSpan.sequentialAll second :=
  Mettapedia.Algebra.WorkSpan.ext
    (by rw [Mettapedia.Algebra.WorkSpan.sequentialAll_work,
      Mettapedia.Algebra.WorkSpan.sequentialAll_work, (perm.map _).sum_eq])
    (by rw [Mettapedia.Algebra.WorkSpan.sequentialAll_span,
      Mettapedia.Algebra.WorkSpan.sequentialAll_span, (perm.map _).sum_eq])

/-- **Parallel receipts are lax.** Every order of a round runs, all orders have the same
sequential receipt, and the parallel receipt of the round lies below it with equal work. -/
theorem round_receipts (receipt : Firing T S O → Mettapedia.Algebra.WorkSpan)
    {C : Configuration T O} {round order : List (Firing T S O)}
    (isRound : Round A label C round) (perm : order.Perm round) :
    Executable A label C order ∧
      Mettapedia.Algebra.WorkSpan.sequentialAll (order.map receipt) =
        Mettapedia.Algebra.WorkSpan.sequentialAll (round.map receipt) ∧
      Mettapedia.Algebra.WorkSpan.parallelAll (round.map receipt) ≤
        Mettapedia.Algebra.WorkSpan.sequentialAll (order.map receipt) ∧
      (Mettapedia.Algebra.WorkSpan.parallelAll (round.map receipt)).work =
        (Mettapedia.Algebra.WorkSpan.sequentialAll (order.map receipt)).work := by
  have sameOrder := sequentialAll_perm (perm.map receipt)
  refine ⟨isRound.executable_perm A label perm, sameOrder, ?_, ?_⟩
  · rw [sameOrder]
    exact parallelAll_le_sequentialAll _
  · rw [Mettapedia.Algebra.WorkSpan.parallelAll_work,
      Mettapedia.Algebra.WorkSpan.sequentialAll_work]
    exact (((perm.map receipt).map Mettapedia.Algebra.WorkSpan.work).sum_eq).symm

end Receipts

/-! ## Weaving decorations of the class theory -/

section Decorations

variable (A : SubstitutionAction T S) (label : O → T)

/-- **The cost decoration**: each step of the class theory is graded by the cost of its
firing. -/
def costGrading {M : Type*} (cost : Firing T S O → M) : (theory A label).StepSpend M where
  graded x y m := ∃ f, (eventLabels A label).labelled x y f ∧ m = cost f
  sound := fun ⟨_, labelled, _⟩ => (eventLabels A label).sound labelled
  resp_left := by
    rintro x x' y m same ⟨f, labelled, rfl⟩
    exact ⟨y, ⟨f, (same : x = x') ▸ labelled, rfl⟩, rfl⟩
  resp_right := by
    rintro x y y' m ⟨f, labelled, rfl⟩ same
    exact ⟨f, (same : y = y') ▸ labelled, rfl⟩

/-- **History and cost weave in either order.** Recording cost and then history has exactly the
steps of recording history and then cost, and both are one decoration by the product monoid:
neither decoration reads the other's accumulator (`GSLT.StepSpend.over`). -/
theorem history_cost_interchange {M : Type*} [Monoid M] (cost : Firing T S O → M)
    {x y : (theory A label).Term} {c c' : M} {w w' : FreeMonoid (Firing T S O)} :
    (((theory A label).spendLift (costGrading A label cost)).spendLift
        ((eventLabels A label).grading.over (costGrading A label cost))).Step ((x, c), w) ((y, c'), w') ↔
      (((theory A label).spendLift (eventLabels A label).grading).spendLift
        ((costGrading A label cost).over (eventLabels A label).grading)).Step ((x, w), c) ((y, w'), c') :=
  GSLT.spendLift_interchange_step_iff (costGrading A label cost) (eventLabels A label).grading

/-- The woven decoration is one lift by the paired grading. -/
theorem history_cost_product {M : Type*} [Monoid M] (cost : Firing T S O → M)
    {source target : ((theory A label).Term × M) × FreeMonoid (Firing T S O)} :
    (((theory A label).spendLift (costGrading A label cost)).spendLift
        ((eventLabels A label).grading.over (costGrading A label cost))).Step source target ↔
      ((theory A label).spendLift ((costGrading A label cost).prod (eventLabels A label).grading)).Step
        (source.1.1, (source.1.2, source.2)) (target.1.1, (target.1.2, target.2)) :=
  GSLT.spendLift_over_step_iff_prod (costGrading A label cost) (eventLabels A label).grading

end Decorations

/-! ## Annotations that read the space -/

section Space

variable (A : SubstitutionAction T S) (label : O → T)

omit [DecidableEq O] in
/-- The present occurrences of a class. -/
def presentOf : ConfigurationClass A O → Finset O :=
  Quotient.lift Configuration.present fun _ _ same => same.2

/-- **A cost that reads the space**: each firing charged by the size of the space it fires in,
as a scan over every present occurrence would be. -/
def spaceAccount : RunAccount (Runs A label) (Multiplicative ℕ) :=
  ofGrade fun {s _} _ => Multiplicative.ofAdd (presentOf A s).card

end Space

/-! ## Controls -/

namespace AnnotationControls

open Mettapedia.Logic.LP
open ConstraintMultisetRewriting.Controls (signature A)
open AnnotatedRuns.Controls (label Run taker reader start taker_valid reader_valid
  taker_reader_independent)

theorem taker_ne_reader : taker ≠ reader := by
  intro same
  have taken := congrArg (fun f : Run => f.selection.taken) same
  simp [taker, reader] at taken

theorem taker_reader_mazurkiewicz : MazurkiewiczIndependent label taker reader :=
  ⟨taker_ne_reader, taker_reader_independent⟩

/-- The tile of the taker and the reader at the start. -/
abbrev swapTile := tile A label taker_reader_mazurkiewicz taker_valid reader_valid

/-- **Negative control: the ordered history is not a property of the trace.** The two routes
of one tile record the two words. -/
theorem history_not_traced :
    (historyAccount A label).of swapTile.path ≠ (historyAccount A label).of swapTile.pathSwap' := by
  intro same
  have words := congrArg FreeMonoid.toList
    (same.trans (of_pathSwap' (historyAccount A label) swapTile))
  change [taker, reader] = [reader, taker] at words
  simp only [List.cons.injEq] at words
  exact taker_ne_reader words.1

theorem history_has_no_static_factorization :
    ¬ ∃ traced : RunAccount (StaticTraces A label) (FreeMonoid Run),
      traced.comap (traceFunctor _) = historyAccount A label := fun factors =>
  history_not_traced ((account_factors_iff _ _).mp factors swapTile)

/-- **Negative control: a cost that reads the space is not a property of the trace.** The
taker keeps the space at two occurrences and the reader grows it to three, so the two routes
of one tile cost four and five. -/
theorem space_cost_not_traced :
    (spaceAccount A label).of swapTile.path = Multiplicative.ofAdd 4 ∧
      (spaceAccount A label).of swapTile.pathSwap' = Multiplicative.ofAdd 5 := by
  exact ⟨by decide, (of_pathSwap' (spaceAccount A label) swapTile).trans (by decide)⟩

/-- **Positive control: counting firings is a property of the trace.** -/
theorem count_traced :
    (siteAccount A label fun _ => Multiplicative.ofAdd (1 : ℕ)).of swapTile.path =
      (siteAccount A label fun _ => Multiplicative.ofAdd (1 : ℕ)).of swapTile.pathSwap' := by
  obtain ⟨traced, restricts⟩ :=
    siteAccount_factors_static A label fun _ : Run => Multiplicative.ofAdd (1 : ℕ)
  rw [← restricts]
  exact congrArg traced.of (Trace.mk_sound (.tile (T := Mettapedia.GSLT.Causality.EventConcurrency.siteTiles
    (siteIndependence A label)) swapTile))

/-- **Positive control: a round of two unit firings.** Both orders have receipt `(2, 2)`; the
round in parallel has receipt `(2, 1)`. -/
theorem unit_round_receipts :
    Mettapedia.Algebra.WorkSpan.sequentialAll ([reader, taker].map fun _ => ⟨1, 1⟩) = ⟨2, 2⟩ ∧
      Mettapedia.Algebra.WorkSpan.parallelAll ([taker, reader].map fun _ => ⟨1, 1⟩) = ⟨2, 1⟩ ∧
      Executable A label start [reader, taker] := by
  refine ⟨rfl, rfl, ?_⟩
  exact (round_receipts A label (fun _ => ⟨1, 1⟩) RoundControls.taker_reader_round
    (List.Perm.swap taker reader [])).1

end AnnotationControls


#print axioms ofGrade_single
#print axioms account_ext
#print axioms of_traceEq
#print axioms account_factors_iff
#print axioms traced_unique
#print axioms prod_factors_iff
#print axioms trace_le_iff
#print axioms siteAccount_factors_static
#print axioms siteAccount_factors_contextual
#print axioms round_receipts
#print axioms history_cost_interchange
#print axioms history_cost_product
#print axioms AnnotationControls.history_not_traced
#print axioms AnnotationControls.history_has_no_static_factorization
#print axioms AnnotationControls.space_cost_not_traced
#print axioms AnnotationControls.count_traced
#print axioms AnnotationControls.unit_round_receipts

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
