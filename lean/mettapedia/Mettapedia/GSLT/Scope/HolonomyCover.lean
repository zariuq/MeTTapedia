import Mettapedia.GSLT.Scope.Holonomy
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Subgroup.Lattice

/-!
# Disparity, individuation and identification

Views over an index graph glue into one global view exactly when every closed
walk transports every value to itself (`nonempty_gluing_iff`).  This module
names what blocks gluing, builds the structure on which the same views glue
without losing any value, and shows that every resolution over the same index
graph must instead identify values.

**Disparity: non-trivial holonomy.**  A disparity at an index is a closed walk
there together with a value of the view that the walk moves (`DisparityAt`);
the disparity register collects the disparities at every index (`Disparity`).
A disparity is a failure of the 1-cocycle condition, and in the language of
sheaf-theoretic contextuality an obstruction to a global section: views that
translate exactly along every edge and still cannot be integrated as they
stand.  Detecting one involves no goal; it is a property of the views alone.
* A disparity forbids gluing on any index graph (`Disparity.not_gluing`), and
  trivial holonomy leaves the register empty
  (`TrivialHolonomy.isEmpty_disparity`).
* For views with decidable equality, the register is empty exactly when
  holonomy is trivial (`isEmpty_disparity_iff`), so on a connected index graph
  exactly when the views glue (`isEmpty_disparity_iff_nonempty_gluing`).
  Without decidable equality an empty register gives only that no closed walk
  can move a value, the double negation of trivial holonomy
  (`isEmpty_disparityAt_iff_not_not`); decidable equality is where a classical
  step would otherwise enter.
* Disparities travel along walks by conjugation (`DisparityAt.push`), so on a
  connected index graph the register is inhabited exactly when it is inhabited
  at the root (`nonempty_disparity_iff_root`), and holonomy is trivial exactly
  when it is trivial at the root (`trivialHolonomy_iff_at`).

**Individuation: the holonomy cover.**  The cover at a root has as vertices an
index together with a class of walks from the root to that index, two walks
being identified when they transport alike (`Fibre`, `CoverVertex`).  Its
edges are the lifts of the edges of the index graph, and its views and
translations are those of the index below (`cover`).  It is the covering of
the index graph associated with the kernel of the holonomy representation.
* Unique walk lifting: projection is a bijection from the walks of the cover
  leaving a vertex onto the walks of the index graph leaving the index below
  it (`walkLiftEquiv`, `existsUnique_lift`).
* The projection is a covering of graphs: it is bijective on the edges leaving
  and on the edges entering every vertex (`outStarEquiv`, `inStarEquiv`).
* The cover is connected from the lift of the root (`coverConnect`) and has
  trivial holonomy (`cover_trivialHolonomy`), so it glues, by the gluing
  theorem for trivial holonomy (`coverGluing`).
* The fibre over the root is the holonomy at the root, the transports of the
  closed walks there (`fibreRootEquiv`); it is in bijection with the holonomy
  group of permutations (`holonomyGroup`, `Fibre.toHolonomyGroup_bijective`),
  closed under identity, composition and inverses (`transportEquiv_nil`,
  `transportEquiv_append`, `transportEquiv_reverse`).
  So the cover has one sheet exactly when holonomy is trivial
  (`subsingleton_fibre_iff`, `holonomyGroup_eq_bot_iff`,
  `oneSheeted_iff_trivialHolonomy`).
* Conservativity.  The views and translations of the cover are those of the
  index graph (`cover_view`, `cover_translate`), every edge lifts at every
  vertex above its source (`outStarEquiv`), and transport along a lift is
  transport along the walk (`Fibre.transport_liftWalk`).  The glued view reads the value at the
  lift of a walk by transport back along that walk, a bijection, so no two
  values of a view are identified (`coverGluing_chart_mk`,
  `coverGluing_chart_symm_mk`, `coverGluing_chart_symm_injective`).  Every
  value of the view at the root is a global section (`coverSectionsEquiv`),
  and so is every value of every view at the lift of a walk reaching it
  (`exists_coverSection`).

**Identification: the orbit quotient.**  Dividing every view by the orbits of
its holonomy (`holonomyOrbit`) keeps the index graph.  The translations
descend (`quotientTranslate`), and the quotient has trivial holonomy
(`orbitQuotient_trivialHolonomy`), so it glues on a connected index graph
(`orbitGluing`), with the orbits at the root as its global sections
(`orbitSectionsEquiv`).
* The quotient map at an index is injective exactly when holonomy is trivial
  there (`injective_orbit_mk_iff`), and, for decidable equality, exactly when
  there is no disparity there (`injective_orbit_mk_iff_isEmpty`).
* It is universal and minimal.  A map into views over the same index graph
  that commutes with the translations, where the new views have trivial
  holonomy, is constant on holonomy orbits (`map_transport_eq`) and factors
  through the orbit quotient (`orbitLift`).  A compatible family of
  equivalence relations whose quotient has trivial holonomy, or glues,
  contains every holonomy orbit (`holonomyOrbit_le`,
  `holonomyOrbit_le_of_gluing`): the orbit quotient is the finest compatible
  quotient that glues.
* So identification prunes at every disparity, identifying two distinct
  values there (`not_injective_of_disparityAt`, `identifies_of_disparityAt`),
  while the cover glues and keeps every value of the root as a global section
  (`individuation_and_identification`).  A commuting map carries global
  sections to global sections (`Sections.mapViews`), so identification never
  loses a section the views already had.

**Controls.**
* The twisted three-cycle, whose holonomy is negation: a disparity
  (`Twisted.disparity`); the cover has two sheets over the root
  (`Twisted.fibreEquivBool`), glues (`Twisted.cover_glues`), and has both
  booleans as global sections (`Twisted.coverSectionsBool`), although the
  cycle itself has none;
  identification collapses every view to one point
  (`Twisted.orbit_subsingleton`).
* The three-cycle of three points twisted by a swap: a disparity
  (`Swap.disparity`); the cover has two sheets (`Swap.fibreEquivBool`) and
  all three points as global sections (`Swap.coverSectionsFin`), whereas
  every global section of the swapped cycle takes the fixed point at the
  root (`Swap.section_at_root`); the orbit quotient keeps the fixed point
  apart from the swapped pair
  (`Swap.orbit_zero_ne_one`, `Swap.orbit_one_eq_two`, `Swap.orbitsEquivBool`)
  and keeps the section through the fixed point (`Swap.orbitSection`).
  Identifying everything also glues but merges the fixed point with the pair
  (`Swap.total_identifies_fixed_point`), so the orbit quotient is strictly
  finer.
* The untwisted path: no disparity, one sheet, and injective quotient maps
  (`Twisted.path_no_disparity`, `Twisted.path_one_sheet`,
  `Twisted.path_orbit_injective`).
* Connectivity is needed: two indices without edges, carrying a two-point and
  a one-point view, have an empty register and no gluing
  (`Apart.empty_register_without_gluing`), and the cover from one index
  misses the view at the other (`Apart.fibre_empty`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Scope

universe uI uE uV uW

namespace ViewSystem

variable {Index : Type uI} {S : ViewSystem.{uI, uE, uV} Index}

/-! ## Transport as an equivalence; conjugation -/

variable (S) in
/-- Transport along a walk, as an equivalence. -/
def transportEquiv {i j : Index} (walk : S.Walk i j) : S.View i ≃ S.View j where
  toFun := S.transport walk
  invFun := S.transport walk.reverse
  left_inv := transport_reverse walk
  right_inv := transport_reverse_right walk

/-- Carry a closed walk at `i` to `j`: back along the walk, around the closed walk, and forth
again. -/
def Walk.conjugate {i j : Index} (walk : S.Walk i j) (loop : S.Walk i i) : S.Walk j j :=
  walk.reverse.append (loop.append walk)

theorem transport_conjugate {i j : Index} (walk : S.Walk i j) (loop : S.Walk i i)
    (value : S.View j) :
    S.transport (walk.conjugate loop) value =
      S.transport walk (S.transport loop (S.transport walk.reverse value)) := by
  rw [Walk.conjugate, transport_append, transport_append]

/-! ## The disparity register -/

variable (S) in
/-- Holonomy is **trivial at an index** when every closed walk there transports every value of
the view to itself. -/
def TrivialHolonomyAt (i : Index) : Prop :=
  ∀ (loop : S.Walk i i) (value : S.View i), S.transport loop value = value

variable (S) in
/-- **A disparity** at an index: a closed walk there and a value of the view that the walk
moves. -/
structure DisparityAt (i : Index) where
  /-- The closed walk. -/
  loop : S.Walk i i
  /-- The value it moves. -/
  value : S.View i
  /-- The walk moves the value. -/
  moved : S.transport loop value ≠ value

variable (S) in
/-- **The disparity register**: the disparities at every index. -/
def Disparity : Type (max uI uE uV) :=
  Σ i : Index, S.DisparityAt i

/-- Trivial holonomy at an index leaves no disparity there. -/
theorem TrivialHolonomyAt.isEmpty {i : Index} (trivial : S.TrivialHolonomyAt i) :
    IsEmpty (S.DisparityAt i) :=
  ⟨fun disparity => disparity.moved (trivial disparity.loop disparity.value)⟩

/-- With decidable equality, no disparity at an index means trivial holonomy there. -/
theorem trivialHolonomyAt_of_isEmpty {i : Index} [DecidableEq (S.View i)]
    (empty : IsEmpty (S.DisparityAt i)) : S.TrivialHolonomyAt i :=
  fun loop value => Decidable.byContradiction fun moved => empty.false ⟨loop, value, moved⟩

/-- **In general, no disparity at an index is the double negation of trivial holonomy there.** -/
theorem isEmpty_disparityAt_iff_not_not {i : Index} :
    IsEmpty (S.DisparityAt i) ↔
      ∀ (loop : S.Walk i i) (value : S.View i), ¬¬ S.transport loop value = value :=
  ⟨fun empty loop value moved => empty.false ⟨loop, value, moved⟩,
    fun stable => ⟨fun disparity => stable disparity.loop disparity.value disparity.moved⟩⟩

/-- **No disparity at an index exactly when holonomy is trivial there**, for decidable
equality. -/
theorem isEmpty_disparityAt_iff {i : Index} [DecidableEq (S.View i)] :
    IsEmpty (S.DisparityAt i) ↔ S.TrivialHolonomyAt i :=
  ⟨trivialHolonomyAt_of_isEmpty, TrivialHolonomyAt.isEmpty⟩

theorem trivialHolonomy_iff_forall_at : S.TrivialHolonomy ↔ ∀ i, S.TrivialHolonomyAt i := by
  constructor
  · intro trivial i loop value
    exact trivial loop value
  · intro trivial i loop value
    exact trivial i loop value

theorem isEmpty_disparity_iff_forall : IsEmpty S.Disparity ↔ ∀ i, IsEmpty (S.DisparityAt i) :=
  ⟨fun empty i => ⟨fun disparity => empty.false ⟨i, disparity⟩⟩,
    fun empty => ⟨fun disparity => (empty disparity.1).false disparity.2⟩⟩

/-- **Trivial holonomy leaves the register empty**, for all views. -/
theorem TrivialHolonomy.isEmpty_disparity (trivial : S.TrivialHolonomy) : IsEmpty S.Disparity :=
  ⟨fun disparity => disparity.2.moved (trivial disparity.2.loop disparity.2.value)⟩

/-- **The register is empty exactly when holonomy is trivial**, for views with decidable
equality. -/
theorem isEmpty_disparity_iff [∀ i, DecidableEq (S.View i)] :
    IsEmpty S.Disparity ↔ S.TrivialHolonomy := by
  rw [isEmpty_disparity_iff_forall, trivialHolonomy_iff_forall_at]
  exact forall_congr' fun _ => isEmpty_disparityAt_iff

/-- **On a connected index graph the register is empty exactly when the views glue**, for views
with decidable equality. -/
theorem isEmpty_disparity_iff_nonempty_gluing [∀ i, DecidableEq (S.View i)] {root : Index}
    (connect : ∀ j : Index, Trunc (S.Walk root j)) : IsEmpty S.Disparity ↔ Nonempty S.Gluing :=
  isEmpty_disparity_iff.trans (nonempty_gluing_iff connect).symm

/-- **A disparity forbids gluing**, on any index graph. -/
theorem Disparity.not_gluing (disparity : S.Disparity) : ¬ Nonempty S.Gluing :=
  fun ⟨gluing⟩ => disparity.2.moved (gluing.trivialHolonomy disparity.2.loop disparity.2.value)

/-- **Disparities travel along walks**: conjugating the closed walk carries the moved value
along. -/
def DisparityAt.push {i j : Index} (walk : S.Walk i j) (disparity : S.DisparityAt i) :
    S.DisparityAt j where
  loop := walk.conjugate disparity.loop
  value := S.transport walk disparity.value
  moved := fun fixed => disparity.moved <| by
    rw [transport_conjugate, transport_reverse] at fixed
    have back := congrArg (S.transport walk.reverse) fixed
    rwa [transport_reverse, transport_reverse] at back

/-- On a connected index graph, a disparity anywhere gives a disparity at the root. -/
def Disparity.toRoot {root : Index} (connect : ∀ j : Index, Trunc (S.Walk root j))
    (disparity : S.Disparity) : Trunc (S.DisparityAt root) :=
  Trunc.map (fun walk => disparity.2.push walk.reverse) (connect disparity.1)

/-- **On a connected index graph the register is inhabited exactly when it is inhabited at the
root.** -/
theorem nonempty_disparity_iff_root {root : Index} (connect : ∀ j : Index, Trunc (S.Walk root j)) :
    Nonempty S.Disparity ↔ Nonempty (S.DisparityAt root) :=
  ⟨fun ⟨disparity⟩ => Trunc.induction_on (disparity.toRoot connect) fun found => ⟨found⟩,
    fun ⟨disparity⟩ => ⟨⟨root, disparity⟩⟩⟩

/-- **On a connected index graph holonomy is trivial exactly when it is trivial at the root.** -/
theorem trivialHolonomy_iff_at {root : Index} (connect : ∀ j : Index, Trunc (S.Walk root j)) :
    S.TrivialHolonomy ↔ S.TrivialHolonomyAt root := by
  constructor
  · intro trivial loop value
    exact trivial loop value
  · intro atRoot i loop value
    induction connect i using Trunc.induction_on with
    | h walk =>
      have fixed := atRoot (walk.reverse.conjugate loop) (S.transport walk.reverse value)
      rw [transport_conjugate, transport_reverse] at fixed
      have back := congrArg (S.transport walk.reverse.reverse) fixed
      rwa [transport_reverse, transport_reverse] at back

/-! ## Individuation: the holonomy cover -/

variable (S) in
/-- Two walks from the root to `j` **transport alike** when they agree on every value. -/
def sameTransport (root j : Index) : Setoid (S.Walk root j) where
  r first second := ∀ value, S.transport first value = S.transport second value
  iseqv :=
    ⟨fun _ _ => rfl, fun same value => (same value).symm,
      fun first second value => (first value).trans (second value)⟩

variable (S) in
/-- **The fibre of the holonomy cover over `j`**: the walks from the root to `j`, two of them
identified when they transport alike. -/
abbrev Fibre (root j : Index) : Type (max uI uE) :=
  Quotient (S.sameTransport root j)

variable {root : Index}

/-- Induction on a fibre: it suffices to treat the class of a walk. -/
@[elab_as_elim]
theorem Fibre.ind {j : Index} {motive : S.Fibre root j → Prop}
    (mk : ∀ walk : S.Walk root j, motive (Quotient.mk _ walk)) (c : S.Fibre root j) : motive c :=
  Quotient.ind mk c

theorem Fibre.mk_eq_mk_iff {j : Index} {first second : S.Walk root j} :
    Quotient.mk (S.sameTransport root j) first = Quotient.mk _ second ↔
      ∀ value, S.transport first value = S.transport second value :=
  ⟨fun same => Quotient.exact same, fun same => Quotient.sound same⟩

/-- Extend a class of walks by one edge, crossed forward. -/
def Fibre.stepForward {i j : Index} (c : S.Fibre root i) (edge : S.Edge i j) : S.Fibre root j :=
  Quotient.lift
    (fun walk => Quotient.mk (S.sameTransport root j) (walk.append (.forward edge (.nil j))))
    (fun first second same => Fibre.mk_eq_mk_iff.mpr fun value => by
      rw [transport_append, transport_append, same value]) c

/-- Extend a class of walks by one edge, crossed backward. -/
def Fibre.stepBackward {i j : Index} (c : S.Fibre root j) (edge : S.Edge i j) : S.Fibre root i :=
  Quotient.lift
    (fun walk => Quotient.mk (S.sameTransport root i) (walk.append (.backward edge (.nil i))))
    (fun first second same => Fibre.mk_eq_mk_iff.mpr fun value => by
      rw [transport_append, transport_append, same value]) c

theorem Fibre.stepForward_stepBackward {i j : Index} (c : S.Fibre root j) (edge : S.Edge i j) :
    (c.stepBackward edge).stepForward edge = c := by
  induction c using Fibre.ind with
  | mk walk =>
    refine Fibre.mk_eq_mk_iff.mpr fun value => ?_
    rw [transport_append, transport_append]
    exact Equiv.apply_symm_apply _ _

theorem Fibre.stepBackward_stepForward {i j : Index} (c : S.Fibre root i) (edge : S.Edge i j) :
    (c.stepForward edge).stepBackward edge = c := by
  induction c using Fibre.ind with
  | mk walk =>
    refine Fibre.mk_eq_mk_iff.mpr fun value => ?_
    rw [transport_append, transport_append]
    exact Equiv.symm_apply_apply _ _

/-- Extend a class of walks along a walk. -/
def Fibre.extend : {i j : Index} → S.Fibre root i → S.Walk i j → S.Fibre root j
  | _, _, c, .nil _ => c
  | _, _, c, .forward edge rest => Fibre.extend (c.stepForward edge) rest
  | _, _, c, .backward edge rest => Fibre.extend (c.stepBackward edge) rest

theorem Fibre.extend_mk {i j : Index} (walk : S.Walk root i) (later : S.Walk i j) :
    Fibre.extend (Quotient.mk (S.sameTransport root i) walk) later =
      Quotient.mk (S.sameTransport root j) (walk.append later) := by
  induction later with
  | nil =>
    exact Fibre.mk_eq_mk_iff.mpr fun value => (transport_append walk (.nil _) value).symm
  | forward edge rest ih =>
    refine (ih (walk.append (.forward edge (.nil _)))).trans
      (Fibre.mk_eq_mk_iff.mpr fun value => ?_)
    rw [transport_append, transport_append, transport_append]
    rfl
  | backward edge rest ih =>
    refine (ih (walk.append (.backward edge (.nil _)))).trans
      (Fibre.mk_eq_mk_iff.mpr fun value => ?_)
    rw [transport_append, transport_append, transport_append]
    rfl

variable (S root) in
/-- The vertices of the holonomy cover: an index, with a class of walks from the root to it. -/
abbrev CoverVertex : Type (max uI uE) :=
  Σ j : Index, S.Fibre root j

variable (S root) in
/-- **The holonomy cover** of `S` at `root`.  A vertex is an index with a class of walks from
the root to it; an edge is an edge of the index graph, leaving a vertex and reaching the class
extended by that edge.  The view at a vertex and the translation along an edge are those of
the index and the edge below. -/
def cover : ViewSystem.{max uI uE, uE, uV} (S.CoverVertex root) where
  View vertex := S.View vertex.1
  Edge source target :=
    {edge : S.Edge source.1 target.1 // source.2.stepForward edge = target.2}
  translate edge := S.translate edge.1

variable (S root) in
/-- The class of the empty walk at the root. -/
abbrev rootClass : S.Fibre root root :=
  Quotient.mk _ (.nil root)

variable (S root) in
/-- **The lift of the root.** -/
abbrev rootLift : S.CoverVertex root :=
  ⟨root, S.rootClass root⟩

/-- **The projection** of a walk of the cover to the index graph. -/
def Walk.project : {x y : S.CoverVertex root} → (S.cover root).Walk x y → S.Walk x.1 y.1
  | _, _, .nil _ => .nil _
  | _, _, .forward edge rest => .forward edge.1 (Walk.project rest)
  | _, _, .backward edge rest => .backward edge.1 (Walk.project rest)

/-- **The lift of a walk** from a vertex of the cover above its source. -/
def Fibre.liftWalk : {i j : Index} → (c : S.Fibre root i) → (walk : S.Walk i j) →
    (S.cover root).Walk ⟨i, c⟩ ⟨j, c.extend walk⟩
  | _, _, _, .nil _ => .nil _
  | _, _, c, .forward edge rest =>
    .forward (j := ⟨_, c.stepForward edge⟩) ⟨edge, rfl⟩ (Fibre.liftWalk (c.stepForward edge) rest)
  | _, _, c, .backward edge rest =>
    .backward (j := ⟨_, c.stepBackward edge⟩) ⟨edge, c.stepForward_stepBackward edge⟩
      (Fibre.liftWalk (c.stepBackward edge) rest)

/-- The lift of a walk projects to the walk. -/
theorem Fibre.project_liftWalk {i j : Index} (c : S.Fibre root i) (walk : S.Walk i j) :
    (c.liftWalk walk).project = walk := by
  induction walk with
  | nil => rfl
  | forward edge rest ih => exact congrArg (Walk.forward edge) (ih _)
  | backward edge rest ih => exact congrArg (Walk.backward edge) (ih _)

/-- Transport in the cover is transport along the projection. -/
theorem transport_cover {x y : S.CoverVertex root} (walk : (S.cover root).Walk x y)
    (value : S.View x.1) :
    (S.cover root).transport walk value = S.transport walk.project value := by
  induction walk with
  | nil => rfl
  | forward edge rest ih => exact ih _
  | backward edge rest ih => exact ih _

/-- **Transport along a lift is transport along the walk.** -/
theorem Fibre.transport_liftWalk {i j : Index} (c : S.Fibre root i) (walk : S.Walk i j)
    (value : S.View i) :
    (S.cover root).transport (c.liftWalk walk) value = S.transport walk value := by
  rw [transport_cover, c.project_liftWalk]

/-- A walk of the cover ends at the class of its source extended by its projection. -/
theorem Walk.extend_project {x y : S.CoverVertex root} (walk : (S.cover root).Walk x y) :
    x.2.extend walk.project = y.2 := by
  induction walk with
  | nil => rfl
  | @forward i j k edge rest ih =>
    exact (congrArg (fun c => Fibre.extend c rest.project) edge.2).trans ih
  | @backward i j k edge rest ih =>
    obtain ⟨e, h⟩ := edge
    have back : i.2.stepBackward e = j.2 := by
      rw [← h]
      exact j.2.stepBackward_stepForward e
    exact (congrArg (fun c => Fibre.extend c rest.project) back).trans ih

/-- A walk of the cover is the lift of its projection. -/
theorem Walk.liftWalk_project {x y : S.CoverVertex root} (walk : (S.cover root).Walk x y) :
    (⟨⟨y.1, x.2.extend walk.project⟩, x.2.liftWalk walk.project⟩ :
      Σ z : S.CoverVertex root, (S.cover root).Walk x z) = ⟨y, walk⟩ := by
  induction walk with
  | nil => rfl
  | @forward i j k edge rest ih =>
    obtain ⟨j₁, d⟩ := j
    obtain ⟨e, h⟩ := edge
    change S.Edge i.1 j₁ at e
    change i.2.stepForward e = d at h
    subst h
    exact congrArg
      (fun p : Σ z : S.CoverVertex root, (S.cover root).Walk ⟨j₁, i.2.stepForward e⟩ z =>
        (⟨p.1, .forward ⟨e, rfl⟩ p.2⟩ : Σ z : S.CoverVertex root, (S.cover root).Walk i z)) ih
  | @backward i j k edge rest ih =>
    obtain ⟨j₁, d⟩ := j
    obtain ⟨e, h⟩ := edge
    change S.Edge j₁ i.1 at e
    change d.stepForward e = i.2 at h
    have back : i.2.stepBackward e = d := by
      rw [← h]
      exact d.stepBackward_stepForward e
    subst back
    exact congrArg
      (fun p : Σ z : S.CoverVertex root, (S.cover root).Walk ⟨j₁, i.2.stepBackward e⟩ z =>
        (⟨p.1, .backward ⟨e, h⟩ p.2⟩ : Σ z : S.CoverVertex root, (S.cover root).Walk i z)) ih

/-- **Unique walk lifting.**  Projection is a bijection from the walks of the cover leaving a
vertex onto the walks of the index graph leaving the index below it; the inverse is lifting. -/
def walkLiftEquiv (x : S.CoverVertex root) :
    (Σ y : S.CoverVertex root, (S.cover root).Walk x y) ≃ Σ j : Index, S.Walk x.1 j where
  toFun p := ⟨p.1.1, p.2.project⟩
  invFun p := ⟨⟨p.1, x.2.extend p.2⟩, x.2.liftWalk p.2⟩
  left_inv p := Walk.liftWalk_project p.2
  right_inv p := congrArg (Sigma.mk p.1) (x.2.project_liftWalk p.2)

/-- **Unique walk lifting, pointwise**: every walk of the index graph from the index below a
vertex has exactly one lift from that vertex. -/
theorem existsUnique_lift (x : S.CoverVertex root) {j : Index} (walk : S.Walk x.1 j) :
    ∃! lift : Σ y : S.CoverVertex root, (S.cover root).Walk x y,
      walkLiftEquiv x lift = ⟨j, walk⟩ :=
  ⟨(walkLiftEquiv x).symm ⟨j, walk⟩, (walkLiftEquiv x).apply_symm_apply _,
    fun lift projects => ((walkLiftEquiv x).symm_apply_apply lift).symm.trans
      (congrArg (walkLiftEquiv x).symm projects)⟩

/-- **The projection is a covering of graphs**: on the edges leaving a vertex it is a
bijection onto the edges leaving the index below. -/
def outStarEquiv (x : S.CoverVertex root) :
    (Σ y : S.CoverVertex root, (S.cover root).Edge x y) ≃ Σ j : Index, S.Edge x.1 j where
  toFun p := ⟨p.1.1, p.2.1⟩
  invFun p := ⟨⟨p.1, x.2.stepForward p.2⟩, ⟨p.2, rfl⟩⟩
  left_inv := by
    rintro ⟨⟨j, d⟩, edge, h⟩
    change S.Edge x.1 j at edge
    change x.2.stepForward edge = d at h
    subst h
    rfl
  right_inv _ := rfl

/-- **The projection is a covering of graphs**: on the edges entering a vertex it is a
bijection onto the edges entering the index below. -/
def inStarEquiv (x : S.CoverVertex root) :
    (Σ y : S.CoverVertex root, (S.cover root).Edge y x) ≃ Σ i : Index, S.Edge i x.1 where
  toFun p := ⟨p.1.1, p.2.1⟩
  invFun p := ⟨⟨p.1, x.2.stepBackward p.2⟩, ⟨p.2, x.2.stepForward_stepBackward p.2⟩⟩
  left_inv := by
    rintro ⟨⟨i, c⟩, edge, h⟩
    change S.Edge i x.1 at edge
    change c.stepForward edge = x.2 at h
    have back : x.2.stepBackward edge = c := by
      rw [← h]
      exact c.stepBackward_stepForward edge
    subst back
    rfl
  right_inv _ := rfl

/-- The class of the empty walk, extended along a walk, is the class of that walk. -/
theorem extend_rootClass {j : Index} (walk : S.Walk root j) :
    (S.rootClass root).extend walk = Quotient.mk _ walk :=
  Fibre.extend_mk (.nil root) walk

/-- **The cover is connected** from the lift of the root: every vertex is reached by a merely
given walk, the lift of a walk of its class. -/
def coverConnect : ∀ x : S.CoverVertex root, Trunc ((S.cover root).Walk (S.rootLift root) x)
  | ⟨j, c⟩ =>
    Quotient.recOnSubsingleton
      (motive := fun c => Trunc ((S.cover root).Walk (S.rootLift root) ⟨j, c⟩)) c
      fun walk => Trunc.mk (extend_rootClass walk ▸ (S.rootClass root).liftWalk walk)

/-- A closed walk whose lift from a class closes up has trivial transport. -/
theorem Fibre.transport_eq_of_extend_eq {i : Index} (c : S.Fibre root i) (loop : S.Walk i i)
    (closed : c.extend loop = c) (value : S.View i) : S.transport loop value = value := by
  induction c using Fibre.ind with
  | mk walk =>
    rw [Fibre.extend_mk, Fibre.mk_eq_mk_iff] at closed
    have fixed := closed (S.transport walk.reverse value)
    rwa [transport_append, transport_reverse_right] at fixed

/-- **The holonomy cover has trivial holonomy.** -/
theorem cover_trivialHolonomy : (S.cover root).TrivialHolonomy := by
  intro x loop value
  exact (transport_cover loop value).trans
    (x.2.transport_eq_of_extend_eq loop.project loop.extend_project value)

variable (S root) in
/-- **The cover glues**, by the gluing theorem for trivial holonomy on a connected index
graph. -/
def coverGluing : (S.cover root).Gluing :=
  gluingOfTrivialHolonomy cover_trivialHolonomy coverConnect

theorem cover_glues : Nonempty (S.cover root).Gluing :=
  ⟨S.coverGluing root⟩

variable (S root) in
/-- **Individuation keeps every value**: the global sections of the cover are the values of the
view at the root. -/
def coverSectionsEquiv : (S.cover root).Sections ≃ S.View root :=
  sectionsEquivOfTrivialHolonomy cover_trivialHolonomy coverConnect

/-- The chart of the cover's gluing at the lift of the root is the identity. -/
theorem coverGluing_chart_rootLift (value : S.View root) :
    (S.coverGluing root).chart (S.rootLift root) value = value := by
  change liftTransport ((trivialHolonomy_iff_pathIndependent _).mp cover_trivialHolonomy)
    (coverConnect (S.rootLift root)) value = value
  induction coverConnect (S.rootLift root) using Trunc.induction_on with
  | h walk => exact cover_trivialHolonomy walk value

/-- **The glued view at the lift of a walk** is transport along that walk. -/
theorem coverGluing_chart_mk {j : Index} (walk : S.Walk root j) (value : S.View root) :
    (S.coverGluing root).chart ⟨j, Quotient.mk _ walk⟩ value = S.transport walk value := by
  have lifted := (S.coverGluing root).transport_chart ((S.rootClass root).liftWalk walk) value
  have moved := congrArg (β := S.View j)
    (fun c : S.Fibre root j => (S.coverGluing root).chart ⟨j, c⟩ value) (extend_rootClass walk)
  exact moved.symm.trans (lifted.symm.trans (((S.rootClass root).transport_liftWalk walk _).trans
    (congrArg (S.transport walk) (coverGluing_chart_rootLift value))))

/-- **Reading a value into the glued view** at the lift of a walk is transport back along the
walk. -/
theorem coverGluing_chart_symm_mk {j : Index} (walk : S.Walk root j) (value : S.View j) :
    ((S.coverGluing root).chart ⟨j, Quotient.mk _ walk⟩).symm value =
      S.transport walk.reverse value := by
  apply ((S.coverGluing root).chart ⟨j, Quotient.mk _ walk⟩).injective
  exact (Equiv.apply_symm_apply _ _).trans ((transport_reverse_right walk value).symm.trans
    (coverGluing_chart_mk walk _).symm)

/-- **Individuation identifies no values**: reading the view at any vertex into the glued view
is injective. -/
theorem coverGluing_chart_symm_injective (x : S.CoverVertex root) :
    Function.Injective ((S.coverGluing root).chart x).symm :=
  ((S.coverGluing root).chart x).symm.injective

/-- **The views of the cover are the views of `S`**: the view at a vertex is the view at the
index below. -/
theorem cover_view (x : S.CoverVertex root) : (S.cover root).View x = S.View x.1 :=
  rfl

/-- **The translations of the cover are the translations of `S`.** -/
theorem cover_translate {x y : S.CoverVertex root} (edge : (S.cover root).Edge x y) :
    (S.cover root).translate edge = S.translate edge.1 :=
  rfl

/-- On a connected index graph, every index has a vertex of the cover above it. -/
def liftIndex (connect : ∀ j : Index, Trunc (S.Walk root j)) (j : Index) :
    Trunc {x : S.CoverVertex root // x.1 = j} :=
  Trunc.map (fun walk => ⟨⟨j, Quotient.mk _ walk⟩, rfl⟩) (connect j)

/-- **Individuation prunes nothing**: every value of the view at an index reached by a walk is
the value, at the lift of that walk, of a global section of the cover. -/
theorem exists_coverSection {j : Index} (walk : S.Walk root j) (value : S.View j) :
    ∃ family : (S.cover root).Sections, family.1 ⟨j, Quotient.mk _ walk⟩ = value :=
  ⟨⟨fun x => (S.coverGluing root).chart x (S.transport walk.reverse value),
      fun edge => (S.coverGluing root).compatible edge _⟩,
    (coverGluing_chart_mk walk _).trans (transport_reverse_right walk value)⟩

/-! ### The fibre over the root is the holonomy -/

variable (S) in
/-- **The holonomy at an index**: the transports of the closed walks there, each with a merely
given closed walk that realises it. -/
def Holonomy (i : Index) : Type (max uI uE uV) :=
  Σ f : S.View i → S.View i, Trunc {loop : S.Walk i i // S.transport loop = f}

theorem Holonomy.ext {i : Index} :
    ∀ {first second : S.Holonomy i}, first.1 = second.1 → first = second
  | ⟨f, first⟩, ⟨_, second⟩, rfl => congrArg (Sigma.mk f) (Subsingleton.elim first second)

/-- **The fibre over the root is the holonomy at the root**: a class of closed walks is its
transport. -/
def fibreRootEquiv : S.Fibre root root ≃ S.Holonomy root where
  toFun := Quotient.lift
    (fun loop => (⟨S.transport loop, Trunc.mk ⟨loop, rfl⟩⟩ : S.Holonomy root))
    fun _ _ same => Holonomy.ext (funext same)
  invFun realised := Trunc.lift (fun loop => Quotient.mk (S.sameTransport root root) loop.1)
    (fun first second => Fibre.mk_eq_mk_iff.mpr fun value =>
      (congrFun first.2 value).trans (congrFun second.2 value).symm) realised.2
  left_inv c := by
    induction c using Fibre.ind with
    | mk loop => rfl
  right_inv := by
    rintro ⟨f, realised⟩
    induction realised using Trunc.induction_on with
    | h loop => exact Holonomy.ext loop.2

/-- Transport along the empty walk is the identity. -/
theorem transportEquiv_nil (i : Index) : S.transportEquiv (.nil i) = Equiv.refl (S.View i) :=
  Equiv.ext fun _ => rfl

/-- Transport along a concatenation is the composite of the transports. -/
theorem transportEquiv_append {i j k : Index} (first : S.Walk i j) (second : S.Walk j k) :
    S.transportEquiv (first.append second) =
      (S.transportEquiv first).trans (S.transportEquiv second) :=
  Equiv.ext (transport_append first second)

/-- Transport back along a walk is the inverse of the transport. -/
theorem transportEquiv_reverse {i j : Index} (walk : S.Walk i j) :
    S.transportEquiv walk.reverse = (S.transportEquiv walk).symm :=
  Equiv.ext fun _ => rfl

variable (S) in
/-- **The holonomy group** at an index: the permutations of the view there that are transports
of closed walks.  Closure under identity, composition and inverses is `transportEquiv_nil`,
`transportEquiv_append` and `transportEquiv_reverse`.  The packaging as a subgroup uses the
library's group of permutations, whose instance depends on classical choice; the equivalence of
the fibre over the root with the transports of closed walks (`fibreRootEquiv`) does not. -/
def holonomyGroup (i : Index) : Subgroup (Equiv.Perm (S.View i)) where
  carrier := {σ | ∃ loop : S.Walk i i, S.transportEquiv loop = σ}
  mul_mem' := by
    rintro _ _ ⟨first, rfl⟩ ⟨second, rfl⟩
    exact ⟨second.append first, transportEquiv_append second first⟩
  one_mem' := ⟨.nil i, transportEquiv_nil i⟩
  inv_mem' := by
    rintro _ ⟨loop, rfl⟩
    exact ⟨loop.reverse, transportEquiv_reverse loop⟩

/-- The element of the holonomy group of a class of closed walks at the root. -/
def Fibre.toHolonomyGroup (c : S.Fibre root root) : S.holonomyGroup root :=
  Quotient.lift (fun loop => (⟨S.transportEquiv loop, loop, rfl⟩ : S.holonomyGroup root))
    (fun _ _ same => Subtype.ext (Equiv.ext same)) c

/-- **The fibre over the root is in bijection with the holonomy group.** -/
theorem Fibre.toHolonomyGroup_bijective :
    Function.Bijective (Fibre.toHolonomyGroup (S := S) (root := root)) := by
  constructor
  · intro first second same
    induction first using Fibre.ind with
    | mk first =>
      induction second using Fibre.ind with
      | mk second =>
        exact Fibre.mk_eq_mk_iff.mpr fun value =>
          congrArg (fun σ : S.holonomyGroup root => (σ : Equiv.Perm (S.View root)) value) same
  · rintro ⟨σ, loop, rfl⟩
    exact ⟨Quotient.mk _ loop, rfl⟩

/-- **The holonomy group is trivial exactly when holonomy is trivial there.** -/
theorem holonomyGroup_eq_bot_iff {i : Index} : S.holonomyGroup i = ⊥ ↔ S.TrivialHolonomyAt i := by
  rw [Subgroup.eq_bot_iff_forall]
  constructor
  · intro trivial loop value
    exact congrArg (fun σ : Equiv.Perm (S.View i) => σ value) (trivial _ ⟨loop, rfl⟩)
  · rintro trivial _ ⟨loop, rfl⟩
    exact Equiv.ext (trivial loop)

/-- **One sheet exactly when holonomy is trivial at the root**: every fibre has at most one
point. -/
theorem subsingleton_fibre_iff :
    (∀ j, Subsingleton (S.Fibre root j)) ↔ S.TrivialHolonomyAt root := by
  constructor
  · intro single loop value
    exact Fibre.mk_eq_mk_iff.mp
      (@Subsingleton.elim _ (single root) (Quotient.mk _ loop) (S.rootClass root)) value
  · intro trivial j
    constructor
    intro first second
    induction first using Fibre.ind with
    | mk first =>
      induction second using Fibre.ind with
      | mk second =>
        refine Fibre.mk_eq_mk_iff.mpr fun value => ?_
        have fixed := trivial (first.append second.reverse) value
        rw [transport_append] at fixed
        have back := congrArg (S.transport second) fixed
        rwa [transport_reverse_right] at back

/-- **On a connected index graph the cover has one sheet exactly when holonomy is trivial.** -/
theorem oneSheeted_iff_trivialHolonomy (connect : ∀ j : Index, Trunc (S.Walk root j)) :
    (∀ j, Subsingleton (S.Fibre root j)) ↔ S.TrivialHolonomy :=
  subsingleton_fibre_iff.trans (trivialHolonomy_iff_at connect).symm

/-- **On a connected index graph the cover has one sheet exactly when the views glue.** -/
theorem oneSheeted_iff_nonempty_gluing (connect : ∀ j : Index, Trunc (S.Walk root j)) :
    (∀ j, Subsingleton (S.Fibre root j)) ↔ Nonempty S.Gluing :=
  (oneSheeted_iff_trivialHolonomy connect).trans (nonempty_gluing_iff connect).symm

/-! ## Identification: the orbit quotient -/

variable (S) in
/-- New views over the index graph of `S`, with translations along its edges. -/
abbrev withViews (View' : Index → Type uW)
    (translate' : ∀ {i j : Index}, S.Edge i j → View' i ≃ View' j) :
    ViewSystem.{uI, uE, uW} Index where
  View := View'
  Edge := S.Edge
  translate := translate'

section Views

variable {View' : Index → Type uW}
  {translate' : ∀ {i j : Index}, S.Edge i j → View' i ≃ View' j}

/-- A walk of `S`, as a walk over the same index graph with new views. -/
def Walk.toViews : {i j : Index} → S.Walk i j → (S.withViews View' translate').Walk i j
  | _, _, .nil i => .nil i
  | _, _, .forward edge rest => .forward edge (Walk.toViews rest)
  | _, _, .backward edge rest => .backward edge (Walk.toViews rest)

/-- A walk over the index graph of `S` with new views, as a walk of `S`. -/
def Walk.ofViews : {i j : Index} → (S.withViews View' translate').Walk i j → S.Walk i j
  | _, _, .nil i => .nil i
  | _, _, .forward edge rest => .forward edge (Walk.ofViews rest)
  | _, _, .backward edge rest => .backward edge (Walk.ofViews rest)

theorem Walk.toViews_ofViews {i j : Index} (walk : (S.withViews View' translate').Walk i j) :
    (Walk.ofViews walk).toViews = walk := by
  induction walk with
  | nil => rfl
  | forward edge rest ih => exact congrArg (Walk.forward edge) ih
  | backward edge rest ih => exact congrArg (Walk.backward edge) ih

variable (translate') in
/-- Maps from the views of `S` to new views **commute with the translations**. -/
def Commutes (q : ∀ i, S.View i → View' i) : Prop :=
  ∀ {i j : Index} (edge : S.Edge i j) (value : S.View i),
    q j (S.translate edge value) = translate' edge (q i value)

/-- **A commuting map carries transport to transport.** -/
theorem transport_toViews {q : ∀ i, S.View i → View' i} (commutes : Commutes translate' q)
    {i j : Index} (walk : S.Walk i j) (value : S.View i) :
    (S.withViews View' translate').transport walk.toViews (q i value) =
      q j (S.transport walk value) := by
  induction walk with
  | nil => rfl
  | @forward i j k edge rest ih =>
    change (S.withViews View' translate').transport rest.toViews (translate' edge (q i value)) =
      q k (S.transport rest (S.translate edge value))
    rw [← commutes]
    exact ih _
  | @backward i j k edge rest ih =>
    change (S.withViews View' translate').transport rest.toViews
        ((translate' edge).symm (q i value)) =
      q k (S.transport rest ((S.translate edge).symm value))
    have back : (translate' edge).symm (q i value) = q j ((S.translate edge).symm value) := by
      apply (translate' edge).injective
      rw [Equiv.apply_symm_apply, ← commutes, Equiv.apply_symm_apply]
    rw [back]
    exact ih _

/-- **A commuting map into views with trivial holonomy is constant on holonomy orbits.** -/
theorem map_transport_eq {q : ∀ i, S.View i → View' i} (commutes : Commutes translate' q)
    (trivial : (S.withViews View' translate').TrivialHolonomy) {i : Index} (loop : S.Walk i i)
    (value : S.View i) : q i (S.transport loop value) = q i value := by
  rw [← transport_toViews commutes]
  exact trivial _ _

/-- **Identification prunes at every disparity**: a commuting map into views with trivial
holonomy is not injective where there is a disparity. -/
theorem not_injective_of_disparityAt {q : ∀ i, S.View i → View' i}
    (commutes : Commutes translate' q) (trivial : (S.withViews View' translate').TrivialHolonomy)
    {i : Index} (disparity : S.DisparityAt i) : ¬ Function.Injective (q i) := fun injective =>
  disparity.moved (injective (map_transport_eq commutes trivial disparity.loop disparity.value))

/-- **A commuting map carries global sections to global sections.** -/
def Sections.mapViews {q : ∀ i, S.View i → View' i} (commutes : Commutes translate' q)
    (family : S.Sections) : (S.withViews View' translate').Sections :=
  ⟨fun i => q i (family.1 i), fun {i j} edge => by
    show translate' edge (q i (family.1 i)) = q j (family.1 j)
    rw [← commutes, family.2 edge]⟩

end Views

variable (S) in
/-- **Holonomy orbits** at an index: two values lie in one orbit when a closed walk there
transports the first to the second. -/
def holonomyOrbit (i : Index) : Setoid (S.View i) where
  r value value' := ∃ loop : S.Walk i i, S.transport loop value = value'
  iseqv :=
    ⟨fun _ => ⟨.nil i, rfl⟩,
      fun ⟨loop, moved⟩ => ⟨loop.reverse, by rw [← moved]; exact transport_reverse loop _⟩,
      fun ⟨first, moved⟩ ⟨second, moved'⟩ =>
        ⟨first.append second, by rw [transport_append, moved, moved']⟩⟩

/-- Holonomy orbits travel along walks. -/
theorem holonomyOrbit_transport {i j : Index} (walk : S.Walk i j) {value value' : S.View i}
    (orbit : S.holonomyOrbit i value value') :
    S.holonomyOrbit j (S.transport walk value) (S.transport walk value') := by
  obtain ⟨loop, rfl⟩ := orbit
  exact ⟨walk.conjugate loop, by rw [transport_conjugate, transport_reverse]⟩

variable (S) in
/-- A family of equivalence relations on the views is **compatible** when every translation
preserves and reflects it. -/
def Compatible (rel : ∀ i, Setoid (S.View i)) : Prop :=
  ∀ {i j : Index} (edge : S.Edge i j) (value value' : S.View i),
    rel i value value' ↔ rel j (S.translate edge value) (S.translate edge value')

/-- **The translations descend** to the quotients by a compatible family. -/
def quotientTranslate {rel : ∀ i, Setoid (S.View i)} (compatible : S.Compatible rel)
    {i j : Index} (edge : S.Edge i j) : Quotient (rel i) ≃ Quotient (rel j) where
  toFun := Quotient.lift (fun value => Quotient.mk (rel j) (S.translate edge value))
    fun _ _ related => Quotient.sound ((compatible edge _ _).mp related)
  invFun := Quotient.lift (fun value => Quotient.mk (rel i) ((S.translate edge).symm value))
    fun _ _ related => Quotient.sound <| (compatible edge _ _).mpr <| by
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact related
  left_inv c := Quotient.inductionOn c fun value =>
    congrArg (Quotient.mk (rel i)) ((S.translate edge).symm_apply_apply value)
  right_inv c := Quotient.inductionOn c fun value =>
    congrArg (Quotient.mk (rel j)) ((S.translate edge).apply_symm_apply value)

variable (S) in
/-- **The quotient of the views by a compatible family**, over the same index graph. -/
abbrev quotientSystem (rel : ∀ i, Setoid (S.View i)) (compatible : S.Compatible rel) :
    ViewSystem.{uI, uE, uV} Index :=
  S.withViews (fun i => Quotient (rel i)) (quotientTranslate compatible)

/-- The class maps commute with the translations. -/
theorem quotient_commutes {rel : ∀ i, Setoid (S.View i)} (compatible : S.Compatible rel) :
    Commutes (quotientTranslate compatible) fun i => Quotient.mk (rel i) :=
  fun _ _ => rfl

/-- Transport in a quotient is the class of the transport. -/
theorem quotientSystem_transport {rel : ∀ i, Setoid (S.View i)} (compatible : S.Compatible rel)
    {i j : Index} (walk : (S.quotientSystem rel compatible).Walk i j) (value : S.View i) :
    (S.quotientSystem rel compatible).transport walk (Quotient.mk (rel i) value) =
      Quotient.mk (rel j) (S.transport (Walk.ofViews walk) value) := by
  have carried := transport_toViews (quotient_commutes compatible) (Walk.ofViews walk) value
  rwa [Walk.toViews_ofViews] at carried

/-- Holonomy orbits form a compatible family. -/
theorem holonomyOrbit_compatible : S.Compatible S.holonomyOrbit := by
  intro i j edge value value'
  constructor
  · exact holonomyOrbit_transport (.forward edge (.nil j))
  · intro related
    have back := holonomyOrbit_transport (.backward edge (.nil i)) related
    change S.holonomyOrbit i ((S.translate edge).symm (S.translate edge value))
      ((S.translate edge).symm (S.translate edge value')) at back
    rwa [Equiv.symm_apply_apply, Equiv.symm_apply_apply] at back

variable (S) in
/-- **The orbit quotient**: every view divided by its holonomy orbits, over the same index
graph. -/
abbrev orbitQuotient : ViewSystem.{uI, uE, uV} Index :=
  S.quotientSystem S.holonomyOrbit holonomyOrbit_compatible

/-- **The orbit quotient has trivial holonomy.** -/
theorem orbitQuotient_trivialHolonomy : S.orbitQuotient.TrivialHolonomy := by
  intro i loop value
  refine Quotient.inductionOn value fun value => ?_
  rw [quotientSystem_transport]
  exact Quotient.sound ⟨(Walk.ofViews loop).reverse, transport_reverse _ _⟩

/-- **The orbit quotient glues** on a connected index graph. -/
def orbitGluing (connect : ∀ j : Index, Trunc (S.Walk root j)) : S.orbitQuotient.Gluing :=
  gluingOfTrivialHolonomy orbitQuotient_trivialHolonomy fun j => Trunc.map Walk.toViews (connect j)

/-- **The global sections of the orbit quotient are the orbits at the root**, on a connected
index graph. -/
def orbitSectionsEquiv (connect : ∀ j : Index, Trunc (S.Walk root j)) :
    S.orbitQuotient.Sections ≃ Quotient (S.holonomyOrbit root) :=
  sectionsEquivOfTrivialHolonomy orbitQuotient_trivialHolonomy
    fun j => Trunc.map Walk.toViews (connect j)

/-- **The quotient map at an index is injective exactly when holonomy is trivial there.** -/
theorem injective_orbit_mk_iff {i : Index} :
    Function.Injective (Quotient.mk (S.holonomyOrbit i)) ↔ S.TrivialHolonomyAt i := by
  constructor
  · intro injective loop value
    exact injective (Quotient.sound ⟨loop.reverse, transport_reverse loop value⟩)
  · intro trivial value value' same
    obtain ⟨loop, moved⟩ := Quotient.exact same
    exact (trivial loop value).symm.trans moved

/-- **The quotient map at an index is injective exactly when there is no disparity there**, for
decidable equality. -/
theorem injective_orbit_mk_iff_isEmpty {i : Index} [DecidableEq (S.View i)] :
    Function.Injective (Quotient.mk (S.holonomyOrbit i)) ↔ IsEmpty (S.DisparityAt i) :=
  injective_orbit_mk_iff.trans isEmpty_disparityAt_iff.symm

/-- **The orbit quotient is universal**: a commuting map into views with trivial holonomy over
the same index graph factors through it. -/
def orbitLift {View' : Index → Type uW}
    {translate' : ∀ {i j : Index}, S.Edge i j → View' i ≃ View' j} {q : ∀ i, S.View i → View' i}
    (commutes : Commutes translate' q) (trivial : (S.withViews View' translate').TrivialHolonomy)
    (i : Index) : Quotient (S.holonomyOrbit i) → View' i :=
  Quotient.lift (q i) fun value _ ⟨loop, moved⟩ =>
    (map_transport_eq commutes trivial loop value).symm.trans (congrArg (q i) moved)

theorem orbitLift_mk {View' : Index → Type uW}
    {translate' : ∀ {i j : Index}, S.Edge i j → View' i ≃ View' j} {q : ∀ i, S.View i → View' i}
    (commutes : Commutes translate' q) (trivial : (S.withViews View' translate').TrivialHolonomy)
    {i : Index} (value : S.View i) :
    orbitLift commutes trivial i (Quotient.mk _ value) = q i value :=
  rfl

/-- **Minimality**: a compatible family whose quotient has trivial holonomy contains every
holonomy orbit. -/
theorem holonomyOrbit_le {rel : ∀ i, Setoid (S.View i)} (compatible : S.Compatible rel)
    (trivial : (S.quotientSystem rel compatible).TrivialHolonomy) {i : Index}
    {value value' : S.View i} (orbit : S.holonomyOrbit i value value') : rel i value value' := by
  obtain ⟨loop, rfl⟩ := orbit
  exact Quotient.exact (map_transport_eq (quotient_commutes compatible) trivial loop value).symm

/-- **The orbit quotient is the finest compatible quotient that glues**: any compatible family
whose quotient glues contains every holonomy orbit. -/
theorem holonomyOrbit_le_of_gluing {rel : ∀ i, Setoid (S.View i)} (compatible : S.Compatible rel)
    (glues : Nonempty (S.quotientSystem rel compatible).Gluing) {i : Index}
    {value value' : S.View i} (orbit : S.holonomyOrbit i value value') : rel i value value' :=
  holonomyOrbit_le compatible (glues.elim fun gluing => gluing.trivialHolonomy) orbit

/-- **Identification prunes**: at a disparity, every compatible quotient that glues identifies
two distinct values. -/
theorem identifies_of_disparityAt {rel : ∀ i, Setoid (S.View i)} (compatible : S.Compatible rel)
    (glues : Nonempty (S.quotientSystem rel compatible).Gluing) {i : Index}
    (disparity : S.DisparityAt i) :
    ∃ value value' : S.View i, value ≠ value' ∧ rel i value value' :=
  ⟨disparity.value, S.transport disparity.loop disparity.value,
    fun same => disparity.moved same.symm,
    holonomyOrbit_le_of_gluing compatible glues ⟨disparity.loop, rfl⟩⟩

/-- **Individuation against identification.**  At a disparity at the root the views do not
glue; the holonomy cover glues and keeps every value of the root as a global section, while
every compatible quotient over the same index graph that glues identifies two distinct values
of the root. -/
theorem individuation_and_identification (disparity : S.DisparityAt root) :
    ¬ Nonempty S.Gluing ∧ Nonempty (S.cover root).Gluing ∧
      Nonempty ((S.cover root).Sections ≃ S.View root) ∧
      ∀ (rel : ∀ i, Setoid (S.View i)) (compatible : S.Compatible rel),
        Nonempty (S.quotientSystem rel compatible).Gluing →
          ∃ value value' : S.View root, value ≠ value' ∧ rel root value value' :=
  ⟨Disparity.not_gluing ⟨root, disparity⟩, cover_glues, ⟨S.coverSectionsEquiv root⟩,
    fun _ compatible glues => identifies_of_disparityAt compatible glues disparity⟩

end ViewSystem

/-! ## Controls -/

namespace Twisted

open ViewSystem

/-- The holonomy of the cycle is negation, on both values. -/
theorem cycle_transport (value : Bool) : twisted.transport cycle value = !value :=
  rfl

/-- Every walk of the twisted cycle transports by the identity or by negation. -/
theorem transport_cases : ∀ {i j : Vertex} (walk : twisted.Walk i j),
    (∀ value, twisted.transport walk value = value) ∨
      (∀ value, twisted.transport walk value = !value)
  | _, _, .nil _ => .inl fun _ => rfl
  | _, _, .forward edge rest => by
    rcases transport_cases rest with same | flipped
    · cases edge
      · exact .inl fun value => same value
      · exact .inl fun value => same value
      · exact .inr fun value => same (!value)
    · cases edge
      · exact .inr fun value => flipped value
      · exact .inr fun value => flipped value
      · exact .inl fun value => (flipped (!value)).trans (Bool.not_not value)
  | _, _, .backward edge rest => by
    rcases transport_cases rest with same | flipped
    · cases edge
      · exact .inl fun value => same value
      · exact .inl fun value => same value
      · exact .inr fun value => same (!value)
    · cases edge
      · exact .inr fun value => flipped value
      · exact .inr fun value => flipped value
      · exact .inl fun value => (flipped (!value)).trans (Bool.not_not value)

/-- **A disparity**: the cycle moves `true`. -/
def disparity : twisted.Disparity :=
  ⟨Vertex.a, cycle, true, fun fixed => Bool.noConfusion (holonomy_moves.symm.trans fixed)⟩

/-- Every vertex of the twisted cycle is reached from `a`. -/
def reach : ∀ j : Vertex, Trunc (twisted.Walk Vertex.a j)
  | .a => Trunc.mk (.nil _)
  | .b => Trunc.mk (.forward CycleEdge.ab (.nil _))
  | .c => Trunc.mk (.forward CycleEdge.ab (.forward CycleEdge.bc (.nil _)))

/-- **Two sheets over the root**: the fibre over `a` is the two holonomies, the identity and
negation. -/
def fibreEquivBool : twisted.Fibre Vertex.a Vertex.a ≃ Bool where
  toFun := Quotient.lift (fun loop => twisted.transport loop true) fun _ _ same => same true
  invFun flag := cond flag (Quotient.mk _ (.nil _)) (Quotient.mk _ cycle)
  left_inv c := by
    induction c using Fibre.ind with
    | mk loop =>
      rcases transport_cases loop with same | flipped
      · show cond (twisted.transport loop true) _ _ = _
        rw [same true]
        exact Fibre.mk_eq_mk_iff.mpr fun value => (same value).symm
      · show cond (twisted.transport loop true) _ _ = _
        rw [flipped true]
        exact Fibre.mk_eq_mk_iff.mpr fun value =>
          (cycle_transport value).trans (flipped value).symm
  right_inv flag := by cases flag <;> rfl

/-- **The cover keeps both values**: its global sections are the two booleans, whereas the
twisted cycle itself has no global section (`no_sections`). -/
def coverSectionsBool : (twisted.cover Vertex.a).Sections ≃ Bool :=
  twisted.coverSectionsEquiv Vertex.a

/-- A closed walk once around the cycle, at every vertex. -/
def turn : ∀ i : Vertex, twisted.Walk i i
  | .a => cycle
  | .b => .forward CycleEdge.bc (.forward CycleEdge.ca (.forward CycleEdge.ab (.nil _)))
  | .c => .forward CycleEdge.ca (.forward CycleEdge.ab (.forward CycleEdge.bc (.nil _)))

theorem transport_turn (i : Vertex) (value : Bool) : twisted.transport (turn i) value = !value := by
  cases i <;> cases value <;> rfl

/-- Any two values of any view lie in one holonomy orbit. -/
theorem orbit_all (i : Vertex) (value value' : Bool) : twisted.holonomyOrbit i value value' := by
  cases value <;> cases value'
  · exact ⟨.nil i, rfl⟩
  · exact ⟨turn i, transport_turn i false⟩
  · exact ⟨turn i, transport_turn i true⟩
  · exact ⟨.nil i, rfl⟩

/-- **Identification collapses**: every view of the orbit quotient has one point. -/
theorem orbit_subsingleton (i : Vertex) : Subsingleton (Quotient (twisted.holonomyOrbit i)) :=
  ⟨fun first second => Quotient.inductionOn₂ first second fun value value' =>
    Quotient.sound (orbit_all i value value')⟩

/-- **The cover of the twisted cycle glues**: two sheets, untwisted. -/
theorem cover_glues : Nonempty (twisted.cover Vertex.a).Gluing :=
  ViewSystem.cover_glues

/-- The orbit quotient of the twisted cycle glues. -/
theorem orbitQuotient_glues : Nonempty twisted.orbitQuotient.Gluing :=
  ⟨orbitGluing reach⟩

/-- **No disparity on the untwisted path.** -/
theorem path_no_disparity : IsEmpty path.Disparity :=
  @TrivialHolonomy.isEmpty_disparity _ path (@Gluing.trivialHolonomy _ path pathGluing)

/-- **One sheet over the untwisted path.** -/
theorem path_one_sheet (j : Vertex) : Subsingleton (path.Fibre Vertex.a j) :=
  subsingleton_fibre_iff.mpr (fun loop value => pathGluing.trivialHolonomy loop value) j

/-- **Identification is injective on the untwisted path.** -/
theorem path_orbit_injective (i : Vertex) :
    Function.Injective (Quotient.mk (path.holonomyOrbit i)) :=
  injective_orbit_mk_iff.mpr fun loop value => pathGluing.trivialHolonomy loop value

end Twisted

namespace Swap

open ViewSystem
open Twisted (Vertex CycleEdge)

/-- The holonomy of the swapped cycle is the swap. -/
theorem swappedCycle_transport (value : Fin 3) :
    swapped.transport swappedCycle value = swapOneTwo value :=
  rfl

/-- Every walk of the swapped cycle transports by the identity or by the swap. -/
theorem transport_cases : ∀ {i j : Vertex} (walk : swapped.Walk i j),
    (∀ value, swapped.transport walk value = value) ∨
      (∀ value, swapped.transport walk value = swapOneTwo value)
  | _, _, .nil _ => .inl fun _ => rfl
  | _, _, .forward edge rest => by
    rcases transport_cases rest with same | flipped
    · cases edge
      · exact .inl fun value => same value
      · exact .inl fun value => same value
      · exact .inr fun value => same (swapOneTwo value)
    · cases edge
      · exact .inr fun value => flipped value
      · exact .inr fun value => flipped value
      · exact .inl fun value => (flipped (swapOneTwo value)).trans (swapOneTwo_involutive value)
  | _, _, .backward edge rest => by
    rcases transport_cases rest with same | flipped
    · cases edge
      · exact .inl fun value => same value
      · exact .inl fun value => same value
      · exact .inr fun value => same (swapOneTwo value)
    · cases edge
      · exact .inr fun value => flipped value
      · exact .inr fun value => flipped value
      · exact .inl fun value => (flipped (swapOneTwo value)).trans (swapOneTwo_involutive value)

/-- **A disparity**: the cycle moves `1`. -/
def disparity : swapped.Disparity :=
  ⟨Vertex.a, swappedCycle, (1 : Fin 3), fun fixed =>
    absurd (show swapOneTwo 1 = 1 from fixed) (by decide)⟩

/-- Every vertex of the swapped cycle is reached from `a`. -/
def reach : ∀ j : Vertex, Trunc (swapped.Walk Vertex.a j)
  | .a => Trunc.mk (.nil _)
  | .b => Trunc.mk (.forward CycleEdge.ab (.nil _))
  | .c => Trunc.mk (.forward CycleEdge.ab (.forward CycleEdge.bc (.nil _)))

/-- Where a closed walk at `a` sends the point `1`. -/
def imageOfOne (loop : swapped.Walk Vertex.a Vertex.a) : Fin 3 :=
  swapped.transport loop (1 : Fin 3)

/-- **Two sheets over the root**: the fibre over `a` is the two holonomies, the identity and the
swap. -/
def fibreEquivBool : swapped.Fibre Vertex.a Vertex.a ≃ Bool where
  toFun := Quotient.lift (fun loop => decide (imageOfOne loop = 1))
    fun _ _ same => congrArg (fun value : Fin 3 => decide (value = 1)) (same (1 : Fin 3))
  invFun flag := cond flag (Quotient.mk _ (.nil _)) (Quotient.mk _ swappedCycle)
  left_inv c := by
    induction c using Fibre.ind with
    | mk loop =>
      rcases transport_cases loop with same | flipped
      · have image : imageOfOne loop = 1 := same (1 : Fin 3)
        show cond (decide (imageOfOne loop = 1)) _ _ = _
        rw [image]
        exact Fibre.mk_eq_mk_iff.mpr fun value => (same value).symm
      · have image : imageOfOne loop = 2 := flipped (1 : Fin 3)
        show cond (decide (imageOfOne loop = 1)) _ _ = _
        rw [image]
        exact Fibre.mk_eq_mk_iff.mpr fun value => (flipped value).symm
  right_inv flag := by cases flag <;> rfl

/-- **The cover keeps all three values** as global sections. -/
def coverSectionsFin : (swapped.cover Vertex.a).Sections ≃ Fin 3 :=
  swapped.coverSectionsEquiv Vertex.a

/-- **The swapped cycle keeps only the fixed point**: every global section takes the fixed point
at the root. -/
theorem section_at_root (family : swapped.Sections) : @Eq (Fin 3) (family.1 Vertex.a) 0 := by
  have fixed : swapOneTwo (family.1 Vertex.a) = family.1 Vertex.a :=
    family.transport swappedCycle
  have onlyZero : ∀ point : Fin 3, swapOneTwo point = point → point = 0 := by
    decide
  exact onlyZero _ fixed

/-- **The fixed point stays apart** from the swapped pair in the orbit quotient. -/
theorem orbit_zero_ne_one :
    Quotient.mk (swapped.holonomyOrbit Vertex.a) (0 : Fin 3) ≠ Quotient.mk _ (1 : Fin 3) := by
  intro same
  obtain ⟨loop, moved⟩ := Quotient.exact same
  rcases transport_cases loop with fixed | flipped
  · have collapse : (0 : Fin 3) = 1 := (fixed (0 : Fin 3)).symm.trans moved
    exact absurd collapse (by decide)
  · have collapse : swapOneTwo 0 = 1 := (flipped (0 : Fin 3)).symm.trans moved
    exact absurd collapse (by decide)

/-- **The swapped pair is one orbit.** -/
theorem orbit_one_eq_two :
    Quotient.mk (swapped.holonomyOrbit Vertex.a) (1 : Fin 3) = Quotient.mk _ (2 : Fin 3) :=
  Quotient.sound ⟨swappedCycle, rfl⟩

/-- Holonomy orbits keep the fixed point apart from the swapped pair. -/
theorem orbit_preserves_zero {value value' : Fin 3}
    (orbit : swapped.holonomyOrbit Vertex.a value value') :
    decide (value = 0) = decide (value' = 0) := by
  obtain ⟨loop, rfl⟩ := orbit
  rcases transport_cases loop with fixed | flipped
  · exact congrArg (fun image : Fin 3 => decide (image = 0)) (fixed value).symm
  · have swapFixesZero : ∀ point : Fin 3, decide (point = 0) = decide (swapOneTwo point = 0) := by
      decide
    exact (swapFixesZero value).trans
      (congrArg (fun image : Fin 3 => decide (image = 0)) (flipped value)).symm

/-- **Two orbits**: the fixed point and the swapped pair. -/
def orbitsEquivBool : Quotient (swapped.holonomyOrbit Vertex.a) ≃ Bool where
  toFun := Quotient.lift (fun value : Fin 3 => decide (value = 0))
    fun _ _ orbit => orbit_preserves_zero orbit
  invFun flag := cond flag (Quotient.mk _ (0 : Fin 3)) (Quotient.mk _ (1 : Fin 3))
  left_inv c := by
    refine Quotient.inductionOn c fun value => ?_
    rcases (show ∀ value : Fin 3, value = 0 ∨ value = 1 ∨ value = 2 by decide) value
      with rfl | rfl | rfl
    · rfl
    · rfl
    · exact orbit_one_eq_two
  right_inv flag := by cases flag <;> rfl

/-- **The section through the fixed point survives identification.** -/
def orbitSection : swapped.orbitQuotient.Sections :=
  fixedSection.mapViews (quotient_commutes holonomyOrbit_compatible)

/-- **The orbit quotient has two global sections**, one for each orbit. -/
def orbitSectionsBool : swapped.orbitQuotient.Sections ≃ Bool :=
  (orbitSectionsEquiv reach).trans orbitsEquivBool

/-- The relation that identifies every two values. -/
def total (i : Vertex) : Setoid (swapped.View i) where
  r _ _ := True
  iseqv := ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩

theorem total_compatible : swapped.Compatible total :=
  fun _ _ _ => Iff.rfl

/-- Identifying everything gives trivial holonomy. -/
theorem total_trivialHolonomy : (swapped.quotientSystem total total_compatible).TrivialHolonomy := by
  intro i loop value
  refine Quotient.inductionOn value fun value => ?_
  rw [quotientSystem_transport]
  exact Quotient.sound trivial

/-- **A coarser quotient also glues but merges the fixed point with the swapped pair**, which the
orbit quotient keeps apart: the orbit quotient is strictly finer. -/
theorem total_identifies_fixed_point :
    Nonempty (swapped.quotientSystem total total_compatible).Gluing ∧
      Quotient.mk (total Vertex.a) (0 : Fin 3) = Quotient.mk _ (1 : Fin 3) ∧
      Quotient.mk (swapped.holonomyOrbit Vertex.a) (0 : Fin 3) ≠ Quotient.mk _ (1 : Fin 3) :=
  ⟨⟨gluingOfTrivialHolonomy total_trivialHolonomy fun j => Trunc.map Walk.toViews (reach j)⟩,
    Quotient.sound trivial, orbit_zero_ne_one⟩

end Swap

namespace Apart

open ViewSystem

/-- Two indices and no edges: a two-point view at `true` and a one-point view at `false`. -/
def apart : ViewSystem.{0, 0, 0} Bool where
  View
    | true => Bool
    | false => Unit
  Edge _ _ := Empty
  translate edge := Empty.elim edge

/-- Without edges every closed walk is empty, so holonomy is trivial. -/
theorem apart_trivialHolonomy : apart.TrivialHolonomy := by
  intro i loop value
  cases loop with
  | nil => rfl
  | forward edge rest => exact Empty.elim edge
  | backward edge rest => exact Empty.elim edge

/-- The register is empty. -/
theorem no_disparity : IsEmpty apart.Disparity :=
  @TrivialHolonomy.isEmpty_disparity _ apart apart_trivialHolonomy

/-- The views do not glue: a two-point view is not equivalent to a one-point view. -/
theorem no_gluing : ¬ Nonempty apart.Gluing := by
  rintro ⟨gluing⟩
  have collapse : (true : Bool) = false :=
    ((gluing.chart true).symm.trans (gluing.chart false)).injective
      (Subsingleton.elim (α := Unit) _ _)
  exact Bool.noConfusion collapse

/-- **Connectivity is needed**: the register is empty and yet the views do not glue. -/
theorem empty_register_without_gluing : IsEmpty apart.Disparity ∧ ¬ Nonempty apart.Gluing :=
  ⟨no_disparity, no_gluing⟩

/-- **The cover from `true` misses the view at `false`**: no walk reaches it. -/
theorem fibre_empty : IsEmpty (apart.Fibre true false) := by
  constructor
  intro c
  induction c using Fibre.ind with
  | mk walk =>
    cases walk with
    | forward edge rest => exact Empty.elim edge
    | backward edge rest => exact Empty.elim edge

end Apart

end Mettapedia.GSLT.Scope
