import Mettapedia.GSLT.Distinction.RouteGrades
import Mathlib.Topology.Basic

/-!
# Directed Lawvere quasimetric and topology on specification categories

Given a `RouteGrades.GradedRepresentation` over a category of specification
presentations, `RouteGrades.optionTolerance` symmetrizes forward and backward best
grades into a symmetric metric tolerance. Hosting and encodability between calculi,
however, are inherently **directed**: a richer host can faithfully embed a guest
(`defect = 0`) even when no uniform encoding exists in the reverse direction
(`defect > 0`).

This module develops the directed geometry directly over `RouteGrades`:
* `directedDefect F s t := 1 - F.bestGrade s t` obeys reflexivity (`= 0` on the
  diagonal), boundedness in `[0, 1]`, and the directed triangle inequality
  (`directedDefect_triangle`).
* `ExactHosting F s t` (`directedDefect F s t = 0`, equivalently `F.bestGrade s t = 1`)
  is a preorder (`exactHosting_refl`, `exactHosting_trans`).
* `MoritaEquiv F s t` (two-sided exact hosting) is an equivalence relation equal to
  zero symmetrized distance (`moritaEquiv_iff_optionDistance_zero`).
* `quasimetricTopology F`: the forward open-ball topology whose specialization
  order recovers `ExactHosting`.
* Controls:
  - `asymmetric_hosting_control`: a concrete two-object category where forward
    hosting is exact (`directedDefect = 0`) and reverse hosting has maximal defect
    (`directedDefect = 1`).
  - `distinct_exact_routes_control`: two distinct defect-`0` self-equivalences on
    one object, demonstrating that Morita-equivalent objects retain nontrivial
    1-cell/2-cell route structure.
-/

set_option autoImplicit false

open CategoryTheory

namespace Mettapedia.GSLT.Distinction.SpecSpace

open Mettapedia.Cybernetics.DistinctionCalculus
open Mettapedia.GSLT.Distinction.RouteGrades

universe u v w

section DirectedQuasimetric

variable {C : Type u} [Category.{v} C] (F : GradedRepresentation.{u, v, w} C)

/-- **Directed Lawvere quasimetric defect** from `source` to `target`:
`0` means exact faithful hosting (`bestGrade = 1`), `1` means maximal distortion or
no grade-improving route. -/
noncomputable def directedDefect (source target : C) : ℝ :=
  1 - F.bestGrade source target

theorem directedDefect_nonneg (source target : C) : 0 ≤ directedDefect F source target := by
  unfold directedDefect
  linarith [F.bestGrade_le_one source target]

theorem directedDefect_le_one (source target : C) : directedDefect F source target ≤ 1 := by
  unfold directedDefect
  linarith [F.bestGrade_nonneg source target]

theorem directedDefect_self (object : C) : directedDefect F object object = 0 := by
  unfold directedDefect
  rw [F.bestGrade_self, sub_self]

/-- **Directed triangle inequality** (Lawvere metric-space enrichment). -/
theorem directedDefect_triangle (a b c : C) :
    directedDefect F a c ≤ directedDefect F a b + directedDefect F b c := by
  unfold directedDefect
  linarith [F.bestGrade_triangle a b c]

theorem directedDefect_le_route_defect {source target : C} (m : source ⟶ target) :
    directedDefect F source target ≤
      RouteGrades.defect (F.observer source) (F.observer target) (F.route m) := by
  unfold directedDefect
  have h := F.grade_le_bestGrade m
  unfold GradedRepresentation.grade RouteGrades.grade at h
  linarith

/-- **Exact directed hosting**: `source` embeds into `target` with zero best defect. -/
def ExactHosting (source target : C) : Prop :=
  directedDefect F source target = 0

theorem exactHosting_iff_bestGrade_one (source target : C) :
    ExactHosting F source target ↔ F.bestGrade source target = 1 := by
  unfold ExactHosting directedDefect
  constructor <;> intro h <;> linarith

theorem exactHosting_of_zero_defect {source target : C} (m : source ⟶ target)
    (hzero : RouteGrades.defect (F.observer source) (F.observer target) (F.route m) = 0) :
    ExactHosting F source target := by
  apply le_antisymm _ (directedDefect_nonneg F source target)
  calc directedDefect F source target
      ≤ RouteGrades.defect (F.observer source) (F.observer target) (F.route m) :=
        directedDefect_le_route_defect F m
    _ = 0 := hzero

theorem exactHosting_refl (object : C) : ExactHosting F object object :=
  directedDefect_self F object

theorem exactHosting_trans {a b c : C}
    (hab : ExactHosting F a b) (hbc : ExactHosting F b c) : ExactHosting F a c := by
  apply le_antisymm _ (directedDefect_nonneg F a c)
  have htri := directedDefect_triangle F a b c
  rw [hab, hbc, add_zero] at htri
  exact htri

/-- **Operational Morita equivalence**: mutual exact hosting in both directions. -/
def MoritaEquiv (a b : C) : Prop :=
  ExactHosting F a b ∧ ExactHosting F b a

theorem moritaEquiv_equivalence : Equivalence (MoritaEquiv F) where
  refl x := ⟨exactHosting_refl F x, exactHosting_refl F x⟩
  symm h := ⟨h.2, h.1⟩
  trans h1 h2 := ⟨exactHosting_trans F h1.1 h2.1, exactHosting_trans F h2.2 h1.2⟩

/-- Morita equivalence coincides with zero symmetrized distance in `optionTolerance`. -/
theorem moritaEquiv_iff_optionDistance_zero (a b : C) :
    MoritaEquiv F a b ↔ F.optionTolerance.distance a b = 0 := by
  unfold MoritaEquiv ExactHosting directedDefect Tolerance.distance
    GradedRepresentation.optionTolerance
  simp only
  have h1 := F.bestGrade_le_one a b
  have h2 := F.bestGrade_le_one b a
  constructor
  · rintro ⟨hab, hba⟩
    have e1 : F.bestGrade a b = 1 := by linarith
    have e2 : F.bestGrade b a = 1 := by linarith
    rw [e1, e2, min_self, sub_self]
  · intro hmin
    have hm : min (F.bestGrade a b) (F.bestGrade b a) = 1 := by linarith
    have le1 : 1 ≤ F.bestGrade a b := hm ▸ min_le_left _ _
    have le2 : 1 ≤ F.bestGrade b a := hm ▸ min_le_right _ _
    constructor <;> linarith

/-! ## Forward open-ball topology induced by the Lawvere quasimetric -/

/-- The forward `ε`-ball around `center`: targets reachable within directed defect `< ε`. -/
def forwardBall (center : C) (ε : ℝ) : Set C :=
  {target | directedDefect F center target < ε}

/-- **Forward quasimetric topology**: a set of specifications is open when every member
contains a positive-radius forward ball of reachable specifications. -/
@[instance_reducible]
noncomputable def quasimetricTopology : TopologicalSpace C where
  IsOpen U := ∀ x ∈ U, ∃ ε : ℝ, 0 < ε ∧ forwardBall F x ε ⊆ U
  isOpen_univ := fun _ _ => ⟨1, zero_lt_one, fun _ _ => trivial⟩
  isOpen_inter s t hs ht x hx := by
    obtain ⟨ε₁, hε₁, hsub₁⟩ := hs x hx.1
    obtain ⟨ε₂, hε₂, hsub₂⟩ := ht x hx.2
    refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun y hy => ?_⟩
    have hy' : directedDefect F x y < min ε₁ ε₂ := hy
    exact ⟨hsub₁ (lt_of_lt_of_le hy' (min_le_left _ _)),
           hsub₂ (lt_of_lt_of_le hy' (min_le_right _ _))⟩
  isOpen_sUnion S hS x hx := by
    obtain ⟨U, hUS, hxU⟩ := hx
    obtain ⟨ε, hε, hsub⟩ := hS U hUS x hxU
    exact ⟨ε, hε, fun y hy => ⟨U, hUS, hsub hy⟩⟩

/-- Every forward open ball is open in `quasimetricTopology` (by the directed triangle law). -/
theorem isOpen_forwardBall (center : C) (r : ℝ) :
    @IsOpen C (quasimetricTopology F) (forwardBall F center r) := by
  intro x hx
  have hpos : 0 < r - directedDefect F center x := sub_pos.mpr hx
  refine ⟨r - directedDefect F center x, hpos, fun y hy => ?_⟩
  show directedDefect F center y < r
  have htri := directedDefect_triangle F center x y
  have hy' : directedDefect F x y < r - directedDefect F center x := hy
  linarith

/-- **Specialization recovers exact hosting**: any open neighborhood of a guest `a`
automatically contains every exact host `b` of `a`. -/
theorem exactHosting_mem_open {a b : C} (hhost : ExactHosting F a b)
    {U : Set C} (hU : @IsOpen C (quasimetricTopology F) U) (ha : a ∈ U) : b ∈ U := by
  obtain ⟨ε, hε, hsub⟩ := hU a ha
  apply hsub
  show directedDefect F a b < ε
  rw [hhost]
  exact hε

/-- Conversely, if every forward ball around `a` contains `b`, then `ExactHosting F a b`. -/
theorem exactHosting_iff_forall_open {a b : C} :
    ExactHosting F a b ↔
      ∀ U : Set C, @IsOpen C (quasimetricTopology F) U → a ∈ U → b ∈ U := by
  constructor
  · intro hhost U hU ha
    exact exactHosting_mem_open F hhost hU ha
  · intro hopen
    apply le_antisymm _ (directedDefect_nonneg F a b)
    by_contra hpos
    push Not at hpos
    have hball : directedDefect F a b < directedDefect F a b :=
      hopen (forwardBall F a (directedDefect F a b))
        (isOpen_forwardBall F a (directedDefect F a b))
        (by show directedDefect F a a < directedDefect F a b; rw [directedDefect_self]; exact hpos)
    exact lt_irrefl _ hball

end DirectedQuasimetric

/-! ## Concrete semantic controls -/

namespace Controls

/-- Two-object category modeling an asymmetric hosting pair:
a monotonic guest (`guest`) and a richer non-monotonic host (`host`). -/
inductive TwoSpec where
  | guest
  | host
  deriving DecidableEq

/-- Morphisms: identities, one faithful embedding `guest → host`, and one lossy
collapse `host → guest` (forcing both outcomes onto one state). -/
inductive TwoHom : TwoSpec → TwoSpec → Type where
  | id (x : TwoSpec) : TwoHom x x
  | embed : TwoHom .guest .host
  | collapse : TwoHom .host .guest

def twoComp : {a b c : TwoSpec} → TwoHom a b → TwoHom b c → TwoHom a c
  | _, _, _, .id _, g => g
  | _, _, _, f, .id _ => f
  | .guest, .host, .guest, .embed, .collapse => .id .guest
  | .host, .guest, .host, .collapse, .embed => .id .host

/-- Discrete-distinction tolerance on `Bool` (`0` when equal, `1` when distinct). -/
def discreteBoolTolerance : Tolerance Bool ℝ where
  similarity a b := if a = b then 1 else 0
  nonnegative a b := by split_ifs <;> norm_num
  bounded a b := by split_ifs <;> norm_num
  reflexive a := by simp
  symmetric a b := by by_cases h : a = b <;> simp [h, eq_comm]

/-- Indiscrete tolerance on `Unit` (only one observable state). -/
def unitTolerance : Tolerance Unit ℝ where
  similarity _ _ := 1
  nonnegative _ _ := by norm_num
  bounded _ _ := by norm_num
  reflexive _ := rfl
  symmetric _ _ := rfl

/-- Two-spec category where `guest` has 1 observable state (`Unit`) and `host` has 2
separated states (`Bool`), with faithful inclusion `Unit → Bool` and surjective
collapse `Bool → Unit`... wait: `Route.comp` of `embed` then `collapse` is `id Unit`,
whereas `collapse` then `embed` maps both booleans to `true`, so we use a 2-object
category whose morphisms are `id` and `embed` only (exact arrow one way, no arrow back!). -/
inductive DirectedHom : TwoSpec → TwoSpec → Type where
  | id (x : TwoSpec) : DirectedHom x x
  | embed : DirectedHom .guest .host

def directedComp : {a b c : TwoSpec} → DirectedHom a b → DirectedHom b c → DirectedHom a c
  | _, _, _, .id _, g => g
  | _, _, _, .embed, .id _ => .embed

instance : Category TwoSpec where
  Hom := DirectedHom
  id := DirectedHom.id
  comp := directedComp
  id_comp := by intro a b f; cases f <;> rfl
  comp_id := by intro a b f; cases f <;> rfl
  assoc := by intro a b c d f g h; cases f <;> cases g <;> cases h <;> rfl

/-- Faithful graded representation: `guest` embeds isometrically into `host`, with
no reverse uniform encoding. -/
def asymmetricRep : GradedRepresentation TwoSpec where
  Carrier
    | .guest => Unit
    | .host => Bool
  observer
    | .guest => unitTolerance
    | .host => discreteBoolTolerance
  route {a b} m := match m with
    | DirectedHom.id x => Route.identity (match x with | .guest => Unit | .host => Bool)
    | DirectedHom.embed => Route.graph (fun _ => true)
  route_id x := by cases x <;> rfl
  route_comp := by
    intro a b c f g
    cases f <;> cases g
    · exact (Route.identity_comp _).symm
    · exact (Route.identity_comp _).symm
    · exact (Route.comp_identity _).symm

/-- **Asymmetric hosting control**: `guest` embeds into `host` with defect `0`, while
`host` has directed defect `1` toward `guest` (`¬ ExactHosting`). -/
theorem asymmetric_hosting_control :
    ExactHosting asymmetricRep .guest .host ∧
    directedDefect asymmetricRep .host .guest = 1 ∧
    ¬ ExactHosting asymmetricRep .host .guest := by
  have hEmbedZero :
      RouteGrades.defect (asymmetricRep.observer .guest) (asymmetricRep.observer .host)
        (asymmetricRep.route DirectedHom.embed) = 0 := by
    apply le_antisymm _ (RouteGrades.defect_nonneg _ _ _)
    apply (RouteGrades.defect_le_iff _ _ le_rfl).mpr
    intro s s' t t' h1 h2
    have ht : t = true := h1.symm
    have ht' : t' = true := h2.symm
    subst ht ht'
    simp [asymmetricRep, unitTolerance, discreteBoolTolerance, Tolerance.distance]
  have hFwd : ExactHosting asymmetricRep .guest .host :=
    exactHosting_of_zero_defect asymmetricRep DirectedHom.embed hEmbedZero
  have hNoBack : IsEmpty (TwoSpec.host ⟶ TwoSpec.guest) := ⟨fun m => nomatch m⟩
  have hBestBack : asymmetricRep.bestGrade .host .guest = 0 := by
    unfold GradedRepresentation.bestGrade
    have hrange : Set.range (fun m : TwoSpec.host ⟶ TwoSpec.guest => asymmetricRep.grade m) = ∅ :=
      Set.range_eq_empty _
    rw [hrange]
    simp [csSup_singleton]
  have hBackOne : directedDefect asymmetricRep .host .guest = 1 := by
    unfold directedDefect
    rw [hBestBack, sub_zero]
  refine ⟨hFwd, hBackOne, ?_⟩
  unfold ExactHosting
  rw [hBackOne]
  norm_num

/-- One-object category with two distinct involutive self-equivalences (`id` and `swap`),
demonstrating nontrivial 2-cell / automorphism structure inside one Morita point. -/
inductive SymObj where
  | single
  deriving DecidableEq

inductive SymHom : SymObj → SymObj → Type where
  | id : SymHom .single .single
  | swap : SymHom .single .single
  deriving DecidableEq

def symComp : SymHom .single .single → SymHom .single .single → SymHom .single .single
  | .id, g => g
  | f, .id => f
  | .swap, .swap => .id

instance : Category SymObj where
  Hom := SymHom
  id _ := .id
  comp {a b c} f g := by cases a; cases b; cases c; exact symComp f g
  id_comp := by intro a b f; cases a; cases b; cases f <;> rfl
  comp_id := by intro a b f; cases a; cases b; cases f <;> rfl
  assoc := by
    intro a b c d f g h
    cases a; cases b; cases c; cases d
    cases f <;> cases g <;> cases h <;> rfl

def symRep : GradedRepresentation SymObj where
  Carrier _ := Bool
  observer _ := discreteBoolTolerance
  route {a b} m := by
    cases a; cases b
    exact match m with
      | .id => Route.identity Bool
      | .swap => Route.graph Bool.not
  route_id x := by cases x; rfl
  route_comp {a b c} f g := by
    cases a; cases b; cases c
    cases f <;> cases g
    · exact (Route.identity_comp _).symm
    · exact (Route.identity_comp _).symm
    · exact (Route.comp_identity _).symm
    · funext x y
      apply propext
      constructor
      · intro h
        subst h
        exact ⟨!x, rfl, Bool.not_not x⟩
      · rintro ⟨m, rfl, rfl⟩
        exact (Bool.not_not x).symm

/-- **2-cell route distinction control**: both `id` and `swap` have exact defect `0`,
yet they realize distinct relational routes (`route id ≠ route swap`). -/
theorem distinct_exact_routes_control :
    RouteGrades.defect (symRep.observer .single) (symRep.observer .single)
      (symRep.route SymHom.id) = 0 ∧
    RouteGrades.defect (symRep.observer .single) (symRep.observer .single)
      (symRep.route SymHom.swap) = 0 ∧
    symRep.route SymHom.id ≠ symRep.route SymHom.swap := by
  refine ⟨RouteGrades.defect_identity _, ?_, ?_⟩
  · apply le_antisymm _ (RouteGrades.defect_nonneg _ _ _)
    apply (RouteGrades.defect_le_iff _ _ le_rfl).mpr
    intro s s' t t' h1 h2
    have ht : t = !s := h1.symm
    have ht' : t' = !s' := h2.symm
    subst ht ht'
    cases s <;> cases s' <;> simp [symRep, discreteBoolTolerance, Tolerance.distance]
  · intro heq
    have htrue : symRep.route SymHom.id true true ↔ symRep.route SymHom.swap true true := by
      rw [heq]
    have hl : symRep.route SymHom.id true true := rfl
    have hr : symRep.route SymHom.swap true true := htrue.mp hl
    exact Bool.noConfusion hr

end Controls

end Mettapedia.GSLT.Distinction.SpecSpace
