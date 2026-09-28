import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.MorphismProperty.IsInvertedBy
import Mathlib.CategoryTheory.Skeletal
import Mettapedia.TypeTheory.LocallyThinWhiskeredCellBicategory
import Mettapedia.TypeTheory.ObserverErasure
import Mettapedia.TypeTheory.OperationalIntensionalExtensionalModes

/-!
# A work observer on a runtime comparison: sharing a list's storage or copying it

The runtime takes the tail of a list in two ways.  The first builds the tail as
a new expression and copies the remaining children.  The second shares the
parent's storage and advances an offset, in constant time.  Both return the
same list; they differ in work.

This is an example in the operational mode: the one-cells are programs run
with their work, and the two-cells are directed comparisons between them.  An
observer either reads a program into the extensional mode, as the result
observer does, or keeps operational data, as the work observer does.

**The comparison.**  Programs over the two operations are the one-cells of a
one-object bicategory whose structural two-cells are equalities
(`Programs`).  One authored generator, `share : copy ⇒ suffix`, is closed
under vertical composition and whiskering in the locally thin extension of
`LocallyThinWhiskeredCellBicategory` (`Runtime`).  Every generated cell keeps
the result and does not increase the work (`cell_improves`, read by the cell
algebra `improvementAlgebra`).  So no cell runs from `suffix` back to `copy`,
and the comparison `copy ⇒ suffix` is directed and not invertible
(`comparison_not_isIso`).

The model compares results and work.  The runtime shares storage only when
the storage outlives the tail (`Machines.Cursor.TailSummary.shared_storage_outlives`);
that side condition is not modelled here.

**Observers.**  An observer is a functor out of the category of
implementations and comparisons.  The erasure of comparisons `E` is the
extensional readout (`routeQuotient`) of that category read as a route type; it
identifies compared implementations.  For an observer valued in a thin
skeletal category, `E` is admissible (a readout `Ō` with `Ō ∘ E = O`,
`NonFactorization.Factors`) exactly when the observer inverts every comparison
(`factors_erase_iff_isInvertedBy`).  The erasure is compatible with
composition: the readout of a composite is the composite of the readouts
(`erase_comp`).

* The result observer, into the discrete category of result functions, inverts
  every comparison (`resultObserver_inverts`), so `E` is admissible for it
  (`result_factors`).  It is a route-preserving map into the discrete embedding
  of its results (`resultRoute`), and its readout `Ō` is that map lifted
  through the route quotient (`resultReadout`, `resultReadout_erase`).
* The work observer, into work functions ordered by decreasing work, does not
  invert the comparison (`workObserver_not_inverts`), so no readout `Ō` gives
  `Ō ∘ E = O` (`work_not_factors`, with the fibre witness `workFiber`).
  Copying costs more than sharing on every list of at least two elements
  (`copy_work_gt`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ListSuffixCostComparison

open CategoryTheory CategoryTheory.Bicategory
open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.TypeTheory.LocallyThinCellReflection
open Mettapedia.TypeTheory.LocallyThinWhiskeredCellBicategory
open Mettapedia.TypeTheory.OperationalIntensionalExtensionalModes

universe u v w x

/-! ## Observers of implementations and comparisons -/

section Contract

variable (H : Type u) [Category.{v} H]

/-- Implementations and their comparisons as an intensional route type: a route
from one implementation to another is a comparison between them. -/
def comparisonRoutes : RouteType.{u} where
  carrier := H
  Route first second := Nonempty (first ⟶ second)
  route_refl first := ⟨𝟙 first⟩

/-- The erasure of comparisons: the extensional readout of the route type.  It
identifies implementations joined by comparisons. -/
def erase (implementation : H) : (routeQuotient.obj (comparisonRoutes H)).carrier :=
  Quot.mk _ implementation

variable {H}

/-- Compared implementations have one readout. -/
theorem erase_eq_of_hom {first second : H} (comparison : first ⟶ second) :
    erase H first = erase H second :=
  Quot.sound ⟨comparison⟩

variable (H) in
/-- Every comparison, as a morphism property.  (It is the top property, written
without the lattice of morphism properties, whose Boolean structure on `Prop` is
classical.) -/
def everyComparison : MorphismProperty H := fun _ _ _ => True

variable {C : Type w} [Category.{x} C]

/-- **The observer contract.**  For an observer valued in a thin skeletal
category, the erasure of comparisons is admissible (some readout `Ō` gives
`Ō ∘ E = O`) exactly when the observer inverts every comparison. -/
theorem factors_erase_iff_isInvertedBy [Quiver.IsThin C] (skeletal : Skeletal C)
    (observer : H ⥤ C) :
    Factors (erase H) observer.obj ↔ (everyComparison H).IsInvertedBy observer := by
  constructor
  · rintro ⟨readout, readsOut⟩ first second comparison -
    have same : observer.obj first = observer.obj second := by
      rw [← readsOut first, ← readsOut second, erase_eq_of_hom comparison]
    exact ⟨⟨eqToHom same.symm, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
  · intro inverts
    refine ⟨Quot.lift observer.obj ?_, fun _ => rfl⟩
    rintro first second ⟨comparison⟩
    obtain ⟨inverse, forward, backward⟩ := (inverts comparison trivial).out
    exact skeletal ⟨⟨observer.map comparison, inverse, forward, backward⟩⟩

/-- A discrete category is skeletal. -/
theorem discrete_skeletal (α : Type w) : Skeletal (Discrete α) :=
  fun _ _ ⟨iso⟩ => Discrete.ext (Discrete.eq_of_hom iso.hom)

/-- A partial order is skeletal as a category. -/
theorem partialOrder_skeletal (α : Type w) [PartialOrder α] : Skeletal α :=
  fun _ _ ⟨iso⟩ => le_antisymm (leOfHom iso.hom) (leOfHom iso.inv)

end Contract

/-! ## Composition

In a bicategory, whiskering sends comparisons to comparisons, so horizontal
composition descends to the readouts of the hom categories: the erasure is
compatible with composition. -/

section Composition

variable {B : Type u} [Bicategory.{w, v} B]

/-- The composite of two readouts: the readout of a composite of
representatives. -/
def composeReadouts {a b c : B}
    (first : (routeQuotient.obj (comparisonRoutes (a ⟶ b))).carrier)
    (second : (routeQuotient.obj (comparisonRoutes (b ⟶ c))).carrier) :
    (routeQuotient.obj (comparisonRoutes (a ⟶ c))).carrier :=
  Quot.lift
    (fun earlier => Quot.lift (fun later => erase (a ⟶ c) (earlier ≫ later))
      (fun _ _ ⟨cell⟩ => erase_eq_of_hom (earlier ◁ cell)) second)
    (fun _ _ ⟨cell⟩ => by
      induction second using Quot.ind with
      | mk later => exact erase_eq_of_hom (cell ▷ later))
    first

/-- **The erasure is compatible with composition**: the readout of a composite
is the composite of the readouts. -/
theorem erase_comp {a b c : B} (first : a ⟶ b) (second : b ⟶ c) :
    erase (a ⟶ c) (first ≫ second) =
      composeReadouts (erase (a ⟶ b) first) (erase (b ⟶ c) second) :=
  rfl

end Composition

/-! ## The runtime: list tails by copying and by sharing -/

section Runtime

/-- A view of a list's children: the storage and the offset of the first child
still present. -/
structure ListView (Item : Type) where
  storage : List Item
  offset : Nat

variable {Item : Type}

/-- The list a view denotes: its children from the offset on. -/
def ListView.toList (view : ListView Item) : List Item :=
  view.storage.drop view.offset

/-- The runtime's two ways of taking the tail of a list. -/
inductive Op
  /-- Build the tail as a new expression, copying the remaining children. -/
  | copy
  /-- Share the parent's storage and advance the offset. -/
  | suffix
  deriving DecidableEq

/-- One operation on a view: the resulting view and its work.  Copying costs one
unit per child copied and one for the new expression; sharing costs one unit. -/
def step : Op → ListView Item → ListView Item × Nat
  | .copy, view => (⟨view.toList.tail, 0⟩, view.toList.tail.length + 1)
  | .suffix, view => (⟨view.storage, view.offset + 1⟩, 1)

/-- Both operations return the tail of the list the view denotes. -/
theorem toList_step (op : Op) (view : ListView Item) :
    (step op view).1.toList = view.toList.tail := by
  cases op
  · rfl
  · exact List.tail_drop.symm

/-- The work of an operation, read from the list the view denotes. -/
def work : Op → List Item → Nat
  | .copy, list => list.tail.length + 1
  | .suffix, _ => 1

theorem work_step (op : Op) (view : ListView Item) :
    (step op view).2 = work op view.toList := by
  cases op <;> rfl

/-- Run a word of operations.  The word `later ++ earlier` runs `earlier` first,
as composition in a one-object category does. -/
def runList : List Op → ListView Item → ListView Item × Nat
  | [], view => (view, 0)
  | op :: rest, view =>
      ((step op (runList rest view).1).1,
        (runList rest view).2 + (step op (runList rest view).1).2)

/-- Run a program. -/
def run (program : FreeMonoid Op) (view : ListView Item) : ListView Item × Nat :=
  runList (FreeMonoid.toList program) view

theorem runList_append (later earlier : List Op) (view : ListView Item) :
    runList (later ++ earlier) view =
      ((runList later (runList earlier view).1).1,
        (runList earlier view).2 + (runList later (runList earlier view).1).2) := by
  induction later with
  | nil => rfl
  | cons op rest ih =>
      show runList (op :: (rest ++ earlier)) view = _
      simp only [runList, ih, Nat.add_assoc]

/-- A composite runs its first factor, then its second, and adds their work. -/
theorem run_mul (later earlier : FreeMonoid Op) (view : ListView Item) :
    run (later * earlier) view =
      ((run later (run earlier view).1).1,
        (run earlier view).2 + (run later (run earlier view).1).2) :=
  runList_append (FreeMonoid.toList later) (FreeMonoid.toList earlier) view

/-- Programs read only the list a view denotes: views of one list give one
result and one work. -/
theorem runList_congr (program : List Op) {view view' : ListView Item}
    (same : view.toList = view'.toList) :
    (runList program view).1.toList = (runList program view').1.toList ∧
      (runList program view).2 = (runList program view').2 := by
  induction program with
  | nil => exact ⟨same, rfl⟩
  | cons op rest ih =>
      obtain ⟨sameList, sameWork⟩ := ih
      exact ⟨by simp only [runList, toList_step, sameList],
        by simp only [runList, work_step, sameList, sameWork]⟩

/-- `second` returns the list `first` returns, with at most its work, from
every view. -/
def Improves (first second : ListView Item → ListView Item × Nat) : Prop :=
  ∀ view, (second view).1.toList = (first view).1.toList ∧ (second view).2 ≤ (first view).2

theorem Improves.refl (implementation : ListView Item → ListView Item × Nat) :
    Improves implementation implementation :=
  fun _ => ⟨rfl, Nat.le_refl _⟩

theorem Improves.trans {first second third : ListView Item → ListView Item × Nat}
    (earlier : Improves first second) (later : Improves second third) :
    Improves first third :=
  fun view => ⟨(later view).1.trans (earlier view).1, Nat.le_trans (later view).2 (earlier view).2⟩

/-- An improvement survives running a common program before it. -/
theorem Improves.precomp {first second : FreeMonoid Op} (prior : FreeMonoid Op)
    (better : Improves (Item := Item) (run first) (run second)) :
    Improves (Item := Item) (run (first * prior)) (run (second * prior)) := by
  intro view
  rw [run_mul, run_mul]
  obtain ⟨sameList, less⟩ := better (run prior view).1
  exact ⟨sameList, Nat.add_le_add_left less _⟩

/-- An improvement survives running a common program after it. -/
theorem Improves.postcomp {first second : FreeMonoid Op} (later : FreeMonoid Op)
    (better : Improves (Item := Item) (run first) (run second)) :
    Improves (Item := Item) (run (later * first)) (run (later * second)) := by
  intro view
  obtain ⟨sameList, less⟩ := better view
  obtain ⟨sameLater, sameWork⟩ := runList_congr (FreeMonoid.toList later) sameList
  rw [run_mul, run_mul]
  exact ⟨sameLater, Nat.add_le_add less (Nat.le_of_eq sameWork)⟩

/-- Sharing improves on copying: one result, and work one against one per child
copied plus one. -/
theorem share_improves :
    Improves (Item := Item) (run (FreeMonoid.of Op.copy)) (run (FreeMonoid.of Op.suffix)) := by
  intro view
  refine ⟨?_, ?_⟩
  · show (step Op.suffix view).1.toList = (step Op.copy view).1.toList
    rw [toList_step, toList_step]
  · show 0 + (step Op.suffix view).2 ≤ 0 + (step Op.copy view).2
    rw [work_step, work_step]
    simp only [work]
    omega

/-- Copying costs more than sharing on every list of at least two elements. -/
theorem copy_work_gt (view : ListView Item) (long : 2 ≤ view.toList.length) :
    (run (FreeMonoid.of Op.suffix) view).2 < (run (FreeMonoid.of Op.copy) view).2 := by
  show 0 + (step Op.suffix view).2 < 0 + (step Op.copy view).2
  rw [work_step, work_step]
  simp only [work, List.length_tail]
  omega

end Runtime

/-! ## The runtime bicategory and its comparison -/

/-- Programs over the two operations: the free monoid on them as a one-object
category, made a bicategory whose structural two-cells are equalities. -/
abbrev Programs : Type := LocallyDiscrete (SingleObj (FreeMonoid Op))

/-- The program a one-cell runs. -/
def program {source target : Programs} (path : source ⟶ target) : FreeMonoid Op :=
  path.as

/-- The one object: a machine state holding a list view. -/
def machineState : Programs := ⟨SingleObj.star _⟩

/-- The copying tail. -/
def copyPath : machineState ⟶ machineState := ⟨FreeMonoid.of Op.copy⟩

/-- The sharing tail. -/
def suffixPath : machineState ⟶ machineState := ⟨FreeMonoid.of Op.suffix⟩

/-- The authored comparison: sharing storage replaces copying. -/
inductive Optimization : {source target : Programs} →
    (source ⟶ target) → (source ⟶ target) → Type where
  | share : Optimization copyPath suffixPath

/-- The runtime bicategory: programs, with the comparisons generated by the
optimization under vertical composition and whiskering, locally thin. -/
abbrev Runtime : Type := Extension Programs Optimization

/-- The machine, as an object of the runtime bicategory. -/
def machine : Runtime := ⟨machineState⟩

/-- Copying, as a one-cell of the runtime bicategory. -/
def copy : machine ⟶ machine := ⟨copyPath⟩

/-- Sharing, as a one-cell of the runtime bicategory. -/
def suffix : machine ⟶ machine := ⟨suffixPath⟩

/-- **The comparison** `copy ⇒ suffix`. -/
def comparison : copy ⟶ suffix :=
  ofAuthored (B := Programs) Optimization.share

variable (Item : Type)

/-- The cell algebra reading every raw generated cell as an improvement between
the programs of its boundary. -/
def improvementAlgebra :
    FreeWhiskeredCell.Algebra (oneCellBase Programs) (ExtendedGenerator Optimization)
      (fun {_ _} first second =>
        PLift (Improves (Item := Item) (run (program first)) (run (program second)))) where
  onRefl _ := ⟨Improves.refl _⟩
  onGenerator := by
    intro source target first second generator
    cases generator with
    | structural structural =>
        cases LocallyDiscrete.eq_of_hom structural
        exact ⟨Improves.refl _⟩
    | authored authored =>
        cases authored
        exact ⟨share_improves⟩
  onVertical := fun earlier later => ⟨earlier.down.trans later.down⟩
  onWhiskerLeft := @fun _source _middle _target prior _first _second cell =>
    ⟨cell.down.precomp (program prior)⟩
  onWhiskerRight := @fun _source _middle _target _first _second suffix cell =>
    ⟨cell.down.postcomp (program suffix)⟩

variable {Item}

/-- **Every comparison of the runtime keeps the result and does not increase
the work.** -/
theorem cell_improves {source target : Runtime} {first second : source ⟶ target}
    (cell : first ⟶ second) :
    Improves (Item := Item) (run (program first.as)) (run (program second.as)) := by
  obtain ⟨raw, rfl⟩ := reflect_surjective cell
  exact ((improvementAlgebra Item).fold raw).down

/-- No comparison runs from sharing back to copying. -/
instance suffix_to_copy_isEmpty : IsEmpty (suffix ⟶ copy) :=
  ⟨fun cell => by
    have less := (cell_improves (Item := Unit) cell ⟨[(), ()], 0⟩).2
    exact absurd less (Nat.not_le.2 (copy_work_gt _ (by decide)))⟩

/-- **The comparison is directed**: it has no inverse. -/
theorem comparison_not_isIso : ¬ IsIso comparison := fun ⟨⟨inverse, _, _⟩⟩ =>
  IsEmpty.false inverse

/-! ## The result and work observers -/

variable (Item)

/-- The result observer: the list each view's program returns. -/
def resultObserver : (machine ⟶ machine) ⥤ Discrete (ListView Item → List Item) where
  obj implementation := ⟨fun view => (run (program implementation.as) view).1.toList⟩
  map cell := ⟨⟨funext fun view => ((cell_improves cell) view).1.symm⟩⟩
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The work observer: the work on each view, ordered so that an arrow points
toward less work. -/
def workObserver : (machine ⟶ machine) ⥤ (ListView Item → Nat)ᵒᵈ where
  obj implementation := OrderDual.toDual fun view => (run (program implementation.as) view).2
  map cell := homOfLE fun view => ((cell_improves cell) view).2
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- **The result observer inverts every comparison.** -/
theorem resultObserver_inverts :
    (everyComparison (machine ⟶ machine)).IsInvertedBy (resultObserver Item) :=
  fun _ _ cell _ =>
    ⟨⟨⟨⟨((resultObserver Item).map cell).down.down.symm⟩⟩,
      Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩

/-- In particular it inverts the comparison `copy ⇒ suffix`. -/
theorem resultObserver_inverts_comparison : IsIso ((resultObserver Item).map comparison) :=
  resultObserver_inverts Item comparison trivial

/-- **The work observer does not invert the comparison.** -/
theorem workObserver_not_inverts [Nonempty Item] :
    ¬ IsIso ((workObserver Item).map comparison) := by
  rintro ⟨⟨inverse, -, -⟩⟩
  obtain ⟨item⟩ := ‹Nonempty Item›
  have less : (run (program copy.as) (⟨[item, item], 0⟩ : ListView Item)).2 ≤
      (run (program suffix.as) (⟨[item, item], 0⟩ : ListView Item)).2 :=
    leOfHom inverse ⟨[item, item], 0⟩
  exact absurd less (Nat.not_le.2 (copy_work_gt _ (by simp [ListView.toList])))

/-- **The erasure of comparisons is admissible for the result observer.** -/
theorem result_factors : Factors (erase (machine ⟶ machine)) (resultObserver Item).obj :=
  (factors_erase_iff_isInvertedBy (discrete_skeletal _) (resultObserver Item)).2
    (resultObserver_inverts Item)

/-- **It is not admissible for the work observer**: no readout `Ō` gives
`Ō ∘ E = O`. -/
theorem work_not_factors [Nonempty Item] :
    ¬ Factors (erase (machine ⟶ machine)) (workObserver Item).obj := fun factors =>
  workObserver_not_inverts Item
    ((factors_erase_iff_isInvertedBy (partialOrder_skeletal _) (workObserver Item)).1 factors
      comparison trivial)

/-- The fibre witness: `copy` and `suffix` have one readout and different work. -/
def workFiber [Nonempty Item] :
    NonTrivialFiber (erase (machine ⟶ machine))
      (fun implementation (view : ListView Item) => (run (program implementation.as) view).2) where
  left := copy
  right := suffix
  sameShadow := erase_eq_of_hom comparison
  differentValue := fun same => by
    obtain ⟨item⟩ := ‹Nonempty Item›
    have equal := congrFun same ⟨[item, item], 0⟩
    exact absurd equal (Nat.ne_of_gt (copy_work_gt _ (by simp [ListView.toList])))

/-- The result observer as a route-preserving map into the discrete embedding of
result functions. -/
def resultRoute :
    comparisonRoutes (machine ⟶ machine) ⟶ discreteOn.obj ⟨ListView Item → List Item⟩ where
  toFun implementation view := (run (program implementation.as) view).1.toList
  map_route := fun ⟨cell⟩ => funext fun view => ((cell_improves cell) view).1.symm

/-- The readout `Ō` of the result observer: `resultRoute` lifted through the
route quotient.  On every readout it agrees with the transpose of `resultRoute`
along the extensional readout adjunction `extensionalReadout`. -/
def resultReadout :
    routeQuotient.obj (comparisonRoutes (machine ⟶ machine)) ⟶ ⟨ListView Item → List Item⟩ :=
  ⟨Quot.lift (resultRoute Item).toFun fun _ _ route => (resultRoute Item).map_route route⟩

/-- `Ō ∘ E` is the result observer. -/
theorem resultReadout_erase (implementation : machine ⟶ machine) :
    (resultReadout Item).toFun (erase _ implementation) =
      fun view => (run (program implementation.as) view).1.toList :=
  rfl

end Mettapedia.TypeTheory.ListSuffixCostComparison
