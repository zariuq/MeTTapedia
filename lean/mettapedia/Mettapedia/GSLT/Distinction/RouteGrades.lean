import Mettapedia.Cybernetics.DistinctionCalculus.PreservationGrade
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.CategoryTheory.Category.Basic

/-!
# Preservation grades along routes

A GSLT-ML route between two spaces is a relation, not necessarily a function: it
may be partial or branching (`GSLT.LanguageDef.GSLTIL.Syntax.RouteMaps`, whose
composite routes relate exactly the relational composites, `RoutesCompose`).
When each space carries a distinction-calculus observer, a route has a
**preservation grade** in Łukasiewicz form, extending the grades of maps in
`Cybernetics.DistinctionCalculus.PreservationGrade` (Hyperseed in the
d-Calculus, HS16.02–HS16.04) from maps to relations.

* **Defects** (`ExpandsAtMost`, `DistortsAtMost`): a route adds at most `δ` to
  any distance between related points, or changes it by at most `δ`.  On the
  graph of a map they are the existing preservation grades
  (`expandsAtMost_graph_iff`, `distortsAtMost_graph_iff`).
* **Graded functoriality**: defects add along relational composites
  (`ExpandsAtMost.comp`, `DistortsAtMost.comp`) and vanish on identities.  Over
  the reals the least defect (`defect`) is subadditive (`defect_comp_le`), so
  the grade `1 − defect` composes in the Łukasiewicz quantale
  (`grade_comp`): `grade (r ; s) ≥ grade r + grade s − 1`.
* **Witnesses** (`not_expandsAtMost_iff`): a route fails a defect exactly when
  some related pair has a distinction it invents beyond the defect.
* **A category of routes** (`GradedRepresentation`): when the objects of a
  category carry observers and its morphisms routes, functorially, the best
  grade between objects (`bestGrade`) obeys the Łukasiewicz triangle law
  (`bestGrade_triangle`) and is `1` on each object, so the symmetrised best grade
  is a distinction-calculus tolerance on the objects that satisfies the metric
  law (`optionTolerance_metric`): the graph of options, observed through its
  routes, is itself an observer.
-/

set_option autoImplicit false

open CategoryTheory

namespace Mettapedia.GSLT.Distinction.RouteGrades

open Mettapedia.Cybernetics.DistinctionCalculus

universe u v w

/-- A route from one carrier to another: a relation, possibly partial or
branching. -/
def Route (X : Type u) (Y : Type v) : Type (max u v) := X → Y → Prop

namespace Route

variable {X : Type u} {Y : Type v} {Z : Type w}

/-- The identity route. -/
def identity (X : Type u) : Route X X := fun source target => source = target

/-- The relational composite of two routes. -/
def comp (first : Route X Y) (second : Route Y Z) : Route X Z :=
  fun source target => ∃ middle, first source middle ∧ second middle target

/-- The graph of a map. -/
def graph (map : X → Y) : Route X Y := fun source target => map source = target

theorem identity_comp (route : Route X Y) : (identity X).comp route = route := by
  funext source target
  apply propext
  constructor
  · rintro ⟨middle, rfl, related⟩
    exact related
  · intro related
    exact ⟨source, rfl, related⟩

theorem comp_identity (route : Route X Y) : route.comp (identity Y) = route := by
  funext source target
  apply propext
  constructor
  · rintro ⟨middle, related, rfl⟩
    exact related
  · intro related
    exact ⟨target, related, rfl⟩

theorem graph_comp (first : X → Y) (second : Y → Z) :
    (graph first).comp (graph second) = graph (second ∘ first) := by
  funext source target
  apply propext
  constructor
  · rintro ⟨middle, rfl, rfl⟩
    rfl
  · intro related
    exact ⟨first source, rfl, related⟩

end Route

/-! ## Defects of a route -/

section Defects

variable {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  {X : Type u} {Y : Type v} {Z : Type w}

/-- **One-sided preservation at grade `1 − δ`**: the route adds at most `δ` to
the distance of any two related pairs. -/
def ExpandsAtMost (a : Tolerance X R) (b : Tolerance Y R) (route : Route X Y) (δ : R) : Prop :=
  ∀ ⦃source source' target target'⦄, route source target → route source' target' →
    b.distance target target' ≤ a.distance source source' + δ

/-- **Two-sided preservation at grade `1 − δ`**: the route changes the distance
of any two related pairs by at most `δ`. -/
def DistortsAtMost (a : Tolerance X R) (b : Tolerance Y R) (route : Route X Y) (δ : R) : Prop :=
  ∀ ⦃source source' target target'⦄, route source target → route source' target' →
    |b.distance target target' - a.distance source source'| ≤ δ

variable {a : Tolerance X R} {b : Tolerance Y R} {c : Tolerance Z R}

theorem expandsAtMost_identity (a : Tolerance X R) : ExpandsAtMost a a (Route.identity X) 0 := by
  rintro _ _ _ _ rfl rfl
  rw [add_zero]

theorem distortsAtMost_identity (a : Tolerance X R) :
    DistortsAtMost a a (Route.identity X) 0 := by
  rintro _ _ _ _ rfl rfl
  rw [sub_self, abs_zero]

/-- **Defects add along composite routes.** -/
theorem ExpandsAtMost.comp {first : Route X Y} {second : Route Y Z} {δ δ' : R}
    (firstBound : ExpandsAtMost a b first δ) (secondBound : ExpandsAtMost b c second δ') :
    ExpandsAtMost a c (first.comp second) (δ + δ') := by
  rintro source source' target target' ⟨middle, sourceMiddle, middleTarget⟩
    ⟨middle', sourceMiddle', middleTarget'⟩
  have firstStep := firstBound sourceMiddle sourceMiddle'
  have secondStep := secondBound middleTarget middleTarget'
  linarith

theorem DistortsAtMost.comp {first : Route X Y} {second : Route Y Z} {δ δ' : R}
    (firstBound : DistortsAtMost a b first δ) (secondBound : DistortsAtMost b c second δ') :
    DistortsAtMost a c (first.comp second) (δ + δ') := by
  rintro source source' target target' ⟨middle, sourceMiddle, middleTarget⟩
    ⟨middle', sourceMiddle', middleTarget'⟩
  have firstStep := firstBound sourceMiddle sourceMiddle'
  have secondStep := secondBound middleTarget middleTarget'
  calc |c.distance target target' - a.distance source source'|
      ≤ |c.distance target target' - b.distance middle middle'| +
          |b.distance middle middle' - a.distance source source'| := abs_sub_le _ _ _
    _ ≤ δ' + δ := add_le_add secondStep firstStep
    _ = δ + δ' := add_comm δ' δ

theorem DistortsAtMost.expandsAtMost {route : Route X Y} {δ : R}
    (bound : DistortsAtMost a b route δ) : ExpandsAtMost a b route δ := by
  intro source source' target target' related related'
  have := (abs_le.mp (bound related related')).2
  linarith

theorem ExpandsAtMost.mono {route : Route X Y} {δ δ' : R} (bound : ExpandsAtMost a b route δ)
    (le : δ ≤ δ') : ExpandsAtMost a b route δ' := by
  intro source source' target target' related related'
  have := bound related related'
  linarith

/-- **A failed defect has a witness**: a related pair at which the route
invents a distinction beyond the defect. -/
theorem not_expandsAtMost_iff {route : Route X Y} {δ : R} :
    ¬ ExpandsAtMost a b route δ ↔
      ∃ source source' target target', route source target ∧ route source' target' ∧
        a.distance source source' + δ < b.distance target target' := by
  constructor
  · intro failed
    by_contra none
    apply failed
    intro source source' target target' related related'
    by_contra exceeds
    exact none ⟨source, source', target, target', related, related', lt_of_not_ge exceeds⟩
  · rintro ⟨source, source', target, target', related, related', exceeds⟩ bound
    exact absurd (bound related related') (not_le.mpr exceeds)

end Defects

/-! ## The dictionary with maps -/

section Graphs

variable {X : Type u} {Y : Type v}

/-- On the graph of a map, the one-sided defect of a route is the one-sided
preservation grade of the distinction calculus. -/
theorem expandsAtMost_graph_iff (a : Tolerance X) (b : Tolerance Y) (map : X → Y) (δ : ℚ) :
    ExpandsAtMost a b (Route.graph map) δ ↔ Tolerance.ExpandsAtMost a b map δ := by
  constructor
  · intro bound source source'
    exact bound (rfl : map source = map source) (rfl : map source' = map source')
  · rintro bound source source' _ _ rfl rfl
    exact bound source source'

/-- On the graph of a map, the two-sided defect of a route is the two-sided
preservation grade of the distinction calculus. -/
theorem distortsAtMost_graph_iff (a : Tolerance X) (b : Tolerance Y) (map : X → Y) (δ : ℚ) :
    DistortsAtMost a b (Route.graph map) δ ↔ Tolerance.DistortsAtMost a b map δ := by
  constructor
  · intro bound source source'
    exact bound (rfl : map source = map source) (rfl : map source' = map source')
  · rintro bound source source' _ _ rfl rfl
    exact bound source source'

end Graphs

/-! ## Least defects and grades over the reals -/

section Real

variable {X : Type u} {Y : Type v} {Z : Type w}
  (a : Tolerance X ℝ) (b : Tolerance Y ℝ) (c : Tolerance Z ℝ)

/-- The distance increments of a route. -/
def gaps (route : Route X Y) : Set ℝ :=
  {gap | ∃ source source' target target', route source target ∧ route source' target' ∧
    gap = b.distance target target' - a.distance source source'}

/-- **The least one-sided defect** of a route (zero when it relates nothing). -/
noncomputable def defect (route : Route X Y) : ℝ := sSup (insert 0 (gaps a b route))

theorem gap_le_one (route : Route X Y) {gap : ℝ} (member : gap ∈ insert 0 (gaps a b route)) :
    gap ≤ 1 := by
  rcases member with rfl | ⟨source, source', target, target', -, -, rfl⟩
  · exact zero_le_one
  · linarith [b.distance_bounded target target', a.distance_nonnegative source source']

theorem bddAbove_gaps (route : Route X Y) : BddAbove (insert 0 (gaps a b route)) :=
  ⟨1, fun _ member => gap_le_one a b route member⟩

theorem defect_nonneg (route : Route X Y) : 0 ≤ defect a b route :=
  le_csSup (bddAbove_gaps a b route) (Set.mem_insert 0 _)

theorem defect_le_one (route : Route X Y) : defect a b route ≤ 1 :=
  csSup_le (Set.insert_nonempty _ _) fun _ member => gap_le_one a b route member

/-- A route expands distances by at most its least defect. -/
theorem expandsAtMost_defect (route : Route X Y) : ExpandsAtMost a b route (defect a b route) := by
  intro source source' target target' related related'
  have : b.distance target target' - a.distance source source' ≤ defect a b route :=
    le_csSup (bddAbove_gaps a b route)
      (Set.mem_insert_of_mem _ ⟨source, source', target, target', related, related', rfl⟩)
  linarith

theorem defect_le_of_expandsAtMost {route : Route X Y} {δ : ℝ}
    (bound : ExpandsAtMost a b route δ) (nonneg : 0 ≤ δ) : defect a b route ≤ δ := by
  apply csSup_le (Set.insert_nonempty _ _)
  rintro _ (rfl | ⟨source, source', target, target', related, related', rfl⟩)
  · exact nonneg
  · have := bound related related'
    linarith

/-- The least defect is the least nonnegative defect a route satisfies. -/
theorem defect_le_iff {route : Route X Y} {δ : ℝ} (nonneg : 0 ≤ δ) :
    defect a b route ≤ δ ↔ ExpandsAtMost a b route δ :=
  ⟨fun le => (expandsAtMost_defect a b route).mono le,
    fun bound => defect_le_of_expandsAtMost a b bound nonneg⟩

theorem defect_identity : defect a a (Route.identity X) = 0 :=
  le_antisymm (defect_le_of_expandsAtMost a a (expandsAtMost_identity a) le_rfl)
    (defect_nonneg a a _)

/-- **Least defects are subadditive along composite routes.** -/
theorem defect_comp_le (first : Route X Y) (second : Route Y Z) :
    defect a c (first.comp second) ≤ defect a b first + defect b c second :=
  defect_le_of_expandsAtMost a c
    ((expandsAtMost_defect a b first).comp (expandsAtMost_defect b c second))
    (add_nonneg (defect_nonneg a b first) (defect_nonneg b c second))

/-- The **preservation grade** of a route, in Łukasiewicz form. -/
noncomputable def grade (route : Route X Y) : ℝ := 1 - defect a b route

theorem grade_nonneg (route : Route X Y) : 0 ≤ grade a b route := by
  unfold grade
  linarith [defect_le_one a b route]

theorem grade_le_one (route : Route X Y) : grade a b route ≤ 1 := by
  unfold grade
  linarith [defect_nonneg a b route]

theorem grade_identity : grade a a (Route.identity X) = 1 := by
  rw [grade, defect_identity, sub_zero]

/-- **Graded functoriality**: grades compose in the Łukasiewicz quantale. -/
theorem grade_comp (first : Route X Y) (second : Route Y Z) :
    grade a b first + grade b c second - 1 ≤ grade a c (first.comp second) := by
  unfold grade
  linarith [defect_comp_le a b c first second]

end Real

/-! ## Graded representations of a category of routes -/

/-- A **graded representation** of a category: each object carries an observed
carrier, each morphism a route, functorially. -/
structure GradedRepresentation (C : Type u) [Category.{v} C] where
  /-- The carrier of an object. -/
  Carrier : C → Type w
  /-- Its observer. -/
  observer : ∀ object, Tolerance (Carrier object) ℝ
  /-- The route of a morphism. -/
  route : ∀ {source target : C}, (source ⟶ target) → Route (Carrier source) (Carrier target)
  route_id : ∀ object, route (𝟙 object) = Route.identity (Carrier object)
  route_comp : ∀ {first second third : C} (earlier : first ⟶ second) (later : second ⟶ third),
    route (earlier ≫ later) = (route earlier).comp (route later)

namespace GradedRepresentation

variable {C : Type u} [Category.{v} C] (F : GradedRepresentation.{u, v, w} C)

/-- The grade of a morphism. -/
noncomputable def grade {source target : C} (morphism : source ⟶ target) : ℝ :=
  RouteGrades.grade (F.observer source) (F.observer target) (F.route morphism)

theorem grade_id (object : C) : F.grade (𝟙 object) = 1 := by
  unfold grade
  rw [F.route_id]
  exact grade_identity _

/-- **Grades compose along routes.** -/
theorem grade_comp {first second third : C} (earlier : first ⟶ second)
    (later : second ⟶ third) :
    F.grade earlier + F.grade later - 1 ≤ F.grade (earlier ≫ later) := by
  unfold grade
  rw [F.route_comp]
  exact RouteGrades.grade_comp _ _ _ _ _

theorem grade_le_one {source target : C} (morphism : source ⟶ target) : F.grade morphism ≤ 1 :=
  RouteGrades.grade_le_one _ _ _

/-- The best grade from one object to another; `0` when no route exists. -/
noncomputable def bestGrade (source target : C) : ℝ :=
  sSup (insert 0 (Set.range fun morphism : source ⟶ target => F.grade morphism))

theorem member_le_one {source target : C} {value : ℝ}
    (member : value ∈ insert 0 (Set.range fun morphism : source ⟶ target => F.grade morphism)) :
    value ≤ 1 := by
  rcases member with rfl | ⟨morphism, rfl⟩
  · exact zero_le_one
  · exact F.grade_le_one morphism

theorem bddAbove_grades (source target : C) :
    BddAbove (insert 0 (Set.range fun morphism : source ⟶ target => F.grade morphism)) :=
  ⟨1, fun _ member => F.member_le_one member⟩

theorem bestGrade_nonneg (source target : C) : 0 ≤ F.bestGrade source target :=
  le_csSup (F.bddAbove_grades source target) (Set.mem_insert 0 _)

theorem bestGrade_le_one (source target : C) : F.bestGrade source target ≤ 1 :=
  csSup_le (Set.insert_nonempty _ _) fun _ member => F.member_le_one member

theorem grade_le_bestGrade {source target : C} (morphism : source ⟶ target) :
    F.grade morphism ≤ F.bestGrade source target :=
  le_csSup (F.bddAbove_grades source target) (Set.mem_insert_of_mem _ ⟨morphism, rfl⟩)

theorem bestGrade_self (object : C) : F.bestGrade object object = 1 :=
  le_antisymm (F.bestGrade_le_one object object)
    ((F.grade_id object).symm.le.trans (F.grade_le_bestGrade (𝟙 object)))

/-- **The Łukasiewicz triangle law for best grades.** -/
theorem bestGrade_triangle (first second third : C) :
    F.bestGrade first second + F.bestGrade second third - 1 ≤ F.bestGrade first third := by
  have pointwise : ∀ u ∈ insert 0 (Set.range fun morphism : first ⟶ second => F.grade morphism),
      ∀ w ∈ insert 0 (Set.range fun morphism : second ⟶ third => F.grade morphism),
        u + w - 1 ≤ F.bestGrade first third := by
    intro u uMember w wMember
    have uLe := F.member_le_one uMember
    have wLe := F.member_le_one wMember
    have nonneg := F.bestGrade_nonneg first third
    rcases uMember with rfl | ⟨earlier, rfl⟩
    · linarith
    rcases wMember with rfl | ⟨later, rfl⟩
    · linarith
    exact (F.grade_comp earlier later).trans (F.grade_le_bestGrade _)
  have inner : ∀ w ∈ insert 0 (Set.range fun morphism : second ⟶ third => F.grade morphism),
      F.bestGrade first second + w - 1 ≤ F.bestGrade first third := by
    intro w wMember
    have : F.bestGrade first second ≤ F.bestGrade first third + 1 - w :=
      csSup_le (Set.insert_nonempty _ _) fun u uMember => by
        have := pointwise u uMember w wMember
        linarith
    linarith
  have : F.bestGrade second third ≤ F.bestGrade first third + 1 - F.bestGrade first second :=
    csSup_le (Set.insert_nonempty _ _) fun w wMember => by
      have := inner w wMember
      linarith
  linarith

/-- **The option tolerance**: two objects are as similar as the worse of their
best grades in the two directions. -/
noncomputable def optionTolerance : Tolerance C ℝ where
  similarity first second := min (F.bestGrade first second) (F.bestGrade second first)
  nonnegative first second := le_min (F.bestGrade_nonneg _ _) (F.bestGrade_nonneg _ _)
  bounded first second := (min_le_left _ _).trans (F.bestGrade_le_one _ _)
  reflexive object := by rw [F.bestGrade_self, min_self]
  symmetric first second := min_comm _ _

/-- **The graph of options, observed through its routes, satisfies the metric
law.** -/
theorem optionTolerance_metric : F.optionTolerance.Metric := by
  intro first second third
  unfold Tolerance.distance
  change 1 - min (F.bestGrade first third) (F.bestGrade third first) ≤
    1 - min (F.bestGrade first second) (F.bestGrade second first) +
      (1 - min (F.bestGrade second third) (F.bestGrade third second))
  have forward := F.bestGrade_triangle first second third
  have backward := F.bestGrade_triangle third second first
  have firstLeft := min_le_left (F.bestGrade first second) (F.bestGrade second first)
  have firstRight := min_le_right (F.bestGrade first second) (F.bestGrade second first)
  have secondLeft := min_le_left (F.bestGrade second third) (F.bestGrade third second)
  have secondRight := min_le_right (F.bestGrade second third) (F.bestGrade third second)
  have both : min (F.bestGrade first second) (F.bestGrade second first) +
      min (F.bestGrade second third) (F.bestGrade third second) - 1 ≤
        min (F.bestGrade first third) (F.bestGrade third first) :=
    le_min (by linarith) (by linarith)
  linarith

end GradedRepresentation

end Mettapedia.GSLT.Distinction.RouteGrades
