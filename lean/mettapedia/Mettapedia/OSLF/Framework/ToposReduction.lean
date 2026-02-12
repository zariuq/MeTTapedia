import Mettapedia.OSLF.Framework.TypeSynthesis
import Mathlib.CategoryTheory.Subfunctor.Basic

/-!
# Internal Presheaf Reduction Relation for OSLF

This module packages the premise-aware reduction relation as a subobject in a
presheaf category.

For any base category `C`, we use the constant presheaf on reduction pairs
`Pattern × Pattern`, and define a `Subfunctor` selecting exactly those pairs
that satisfy the declarative/internal one-step relation `langReducesUsing`.

This gives a concrete internal relation object in `Psh(C)` and a direct bridge
to the executable engine.
-/

namespace Mettapedia.OSLF.Framework.ToposReduction

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Framework.TypeSynthesis

universe u v

/-- A small bundled internal graph object in `Psh(C)`: vertices, edges,
source and target. -/
structure InternalReductionGraph (C : Type u) [CategoryTheory.Category.{v} C] where
  Vertex : CategoryTheory.Functor (Opposite C) (Type (max u v))
  Edge : CategoryTheory.Functor (Opposite C) (Type (max u v))
  source : Edge ⟶ Vertex
  target : Edge ⟶ Vertex

/-- Constant presheaf of patterns (vertex object). -/
def patternConstPresheaf (C : Type u) [CategoryTheory.Category.{v} C] :
    CategoryTheory.Functor (Opposite C) (Type (max u v)) where
  obj _ := ULift Pattern
  map _ := id
  map_id := by intro _; rfl
  map_comp := by intro _ _ _ _ _; rfl

/-- Constant presheaf of reduction pairs `(p, q)` over a base category. -/
def pairConstPresheaf (C : Type u) [CategoryTheory.Category.{v} C] :
    CategoryTheory.Functor (Opposite C) (Type (max u v)) where
  obj _ := ULift (Prod Pattern Pattern)
  map _ := id
  map_id := by intro _; rfl
  map_comp := by intro _ _ _ _ _; rfl

/-- Internal (presheaf) reduction relation: subfunctor of the constant
pair-presheaf selecting exactly premise-aware one-step reductions. -/
def reductionSubfunctorUsing (C : Type u) [CategoryTheory.Category.{v} C]
    (relEnv : RelationEnv) (lang : LanguageDef) :
    CategoryTheory.Subfunctor (pairConstPresheaf (C := C)) where
  obj X := { pq : (pairConstPresheaf (C := C)).obj X |
    langReducesUsing relEnv lang pq.down.1 pq.down.2 }
  map := by
    intro X Y f pq hpq
    change langReducesUsing relEnv lang
      (((pairConstPresheaf (C := C)).map f pq).down.1)
      (((pairConstPresheaf (C := C)).map f pq).down.2)
    simpa [pairConstPresheaf] using hpq

/-- Default internal reduction relation (`RelationEnv.empty`). -/
def reductionSubfunctor (C : Type u) [CategoryTheory.Category.{v} C] (lang : LanguageDef) :
    CategoryTheory.Subfunctor (pairConstPresheaf (C := C)) :=
  reductionSubfunctorUsing (C := C) RelationEnv.empty lang

/-- Source map `E ⟶ V` for the internal reduction graph:
edge `(p, q)` maps to source vertex `p`. -/
def reductionSourceUsing (C : Type u) [CategoryTheory.Category.{v} C]
    (relEnv : RelationEnv) (lang : LanguageDef) :
    (reductionSubfunctorUsing (C := C) relEnv lang).toFunctor ⟶
      patternConstPresheaf (C := C) where
  app X e := ULift.up e.1.down.1
  naturality := by
    intro X Y f
    funext e
    rfl

/-- Target map `E ⟶ V` for the internal reduction graph:
edge `(p, q)` maps to target vertex `q`. -/
def reductionTargetUsing (C : Type u) [CategoryTheory.Category.{v} C]
    (relEnv : RelationEnv) (lang : LanguageDef) :
    (reductionSubfunctorUsing (C := C) relEnv lang).toFunctor ⟶
      patternConstPresheaf (C := C) where
  app X e := ULift.up e.1.down.2
  naturality := by
    intro X Y f
    funext e
    rfl

/-- Internal reduction graph object over `Psh(C)`:
vertices are patterns, edges are premise-aware one-step reductions. -/
def reductionGraphUsing (C : Type u) [CategoryTheory.Category.{v} C]
    (relEnv : RelationEnv) (lang : LanguageDef) :
    InternalReductionGraph C where
  Vertex := patternConstPresheaf (C := C)
  Edge := (reductionSubfunctorUsing (C := C) relEnv lang).toFunctor
  source := reductionSourceUsing (C := C) relEnv lang
  target := reductionTargetUsing (C := C) relEnv lang

/-- Default-env internal reduction graph object. -/
def reductionGraph (C : Type u) [CategoryTheory.Category.{v} C]
    (lang : LanguageDef) :
    InternalReductionGraph C :=
  reductionGraphUsing (C := C) RelationEnv.empty lang

/-- Reusable OSLF reduction-graph abstraction with endpoint law packaged. -/
structure ReductionGraphObj (C : Type u) [CategoryTheory.Category.{v} C]
    (relEnv : RelationEnv) (lang : LanguageDef) where
  Edge : CategoryTheory.Functor (Opposite C) (Type (max u v))
  source : Edge ⟶ patternConstPresheaf (C := C)
  target : Edge ⟶ patternConstPresheaf (C := C)
  edge_endpoints_iff :
    ∀ {X : Opposite C} {p q : Pattern},
      (∃ e : Edge.obj X, (source.app X e).down = p ∧ (target.app X e).down = q) ↔
        langReducesUsing relEnv lang p q

/-- Membership in the internal reduction subfunctor is exactly
`langReducesUsing`. -/
theorem mem_reductionSubfunctorUsing_iff
    (C : Type u) [CategoryTheory.Category.{v} C]
    (relEnv : RelationEnv) (lang : LanguageDef)
    {X : Opposite C} {p q : Pattern} :
    ((ULift.up (p, q)) : (pairConstPresheaf (C := C)).obj X) ∈
      (reductionSubfunctorUsing (C := C) relEnv lang).obj X ↔
      langReducesUsing relEnv lang p q := by
  rfl

/-- Endpoint characterization of the internal graph edges:
there is an edge from `p` to `q` iff `langReducesUsing p q`. -/
theorem reductionGraphUsing_edge_endpoints_iff
    (C : Type u) [CategoryTheory.Category.{v} C]
    (relEnv : RelationEnv) (lang : LanguageDef)
    {X : Opposite C} {p q : Pattern} :
    (∃ e : (reductionGraphUsing (C := C) relEnv lang).Edge.obj X,
      ((reductionGraphUsing (C := C) relEnv lang).source.app X e).down = p ∧
      ((reductionGraphUsing (C := C) relEnv lang).target.app X e).down = q) ↔
      langReducesUsing relEnv lang p q := by
  constructor
  · rintro ⟨e, hs, ht⟩
    have hs' : e.1.down.1 = p := by
      simpa [reductionGraphUsing, reductionSourceUsing] using hs
    have ht' : e.1.down.2 = q := by
      simpa [reductionGraphUsing, reductionTargetUsing] using ht
    have hred : langReducesUsing relEnv lang e.1.down.1 e.1.down.2 := e.2
    simpa [hs', ht'] using hred
  · intro hred
    refine ⟨⟨ULift.up (p, q), hred⟩, ?_, ?_⟩
    · simp [reductionGraphUsing, reductionSourceUsing]
    · simp [reductionGraphUsing, reductionTargetUsing]

/-- Canonical packaged reduction graph object for a language/env pair. -/
def reductionGraphObjUsing (C : Type u) [CategoryTheory.Category.{v} C]
    (relEnv : RelationEnv) (lang : LanguageDef) :
    ReductionGraphObj C relEnv lang where
  Edge := (reductionGraphUsing (C := C) relEnv lang).Edge
  source := (reductionGraphUsing (C := C) relEnv lang).source
  target := (reductionGraphUsing (C := C) relEnv lang).target
  edge_endpoints_iff := by
    intro X p q
    simpa using
      (reductionGraphUsing_edge_endpoints_iff
        (C := C) (relEnv := relEnv) (lang := lang) (X := X) (p := p) (q := q))

/-- Default-env packaged reduction graph object. -/
def reductionGraphObj (C : Type u) [CategoryTheory.Category.{v} C]
    (lang : LanguageDef) :
    ReductionGraphObj C RelationEnv.empty lang :=
  reductionGraphObjUsing (C := C) RelationEnv.empty lang

/-- Graph-form `◇` characterization via source/target maps. -/
theorem langDiamondUsing_iff_exists_graphStep
    (C : Type u) [CategoryTheory.Category.{v} C]
    (relEnv : RelationEnv) (lang : LanguageDef)
    {X : Opposite C} (φ : Pattern → Prop) (p : Pattern) :
    langDiamondUsing relEnv lang φ p ↔
      ∃ e : (reductionGraphUsing (C := C) relEnv lang).Edge.obj X,
        ((reductionGraphUsing (C := C) relEnv lang).source.app X e).down = p ∧
        φ (((reductionGraphUsing (C := C) relEnv lang).target.app X e).down) := by
  constructor
  · intro h
    rcases (langDiamondUsing_spec relEnv lang φ p).1 h with ⟨q, hred, hφ⟩
    refine ⟨⟨ULift.up (p, q), hred⟩, ?_, ?_⟩
    · simp [reductionGraphUsing, reductionSourceUsing]
    · simpa [reductionGraphUsing, reductionTargetUsing] using hφ
  · rintro ⟨e, hs, hφ⟩
    refine (langDiamondUsing_spec relEnv lang φ p).2 ?_
    refine ⟨((reductionGraphUsing (C := C) relEnv lang).target.app X e).down, ?_, hφ⟩
    have hred : langReducesUsing relEnv lang
        (((reductionGraphUsing (C := C) relEnv lang).source.app X e).down)
        (((reductionGraphUsing (C := C) relEnv lang).target.app X e).down) := e.2
    simpa [hs] using hred

/-- Graph-form `□` characterization via incoming edges into `p`. -/
theorem langBoxUsing_iff_forall_graphIncoming
    (C : Type u) [CategoryTheory.Category.{v} C]
    (relEnv : RelationEnv) (lang : LanguageDef)
    {X : Opposite C} (φ : Pattern → Prop) (p : Pattern) :
    langBoxUsing relEnv lang φ p ↔
      ∀ e : (reductionGraphUsing (C := C) relEnv lang).Edge.obj X,
        ((reductionGraphUsing (C := C) relEnv lang).target.app X e).down = p →
        φ (((reductionGraphUsing (C := C) relEnv lang).source.app X e).down) := by
  constructor
  · intro h e ht
    have hred : langReducesUsing relEnv lang
      (((reductionGraphUsing (C := C) relEnv lang).source.app X e).down)
      (((reductionGraphUsing (C := C) relEnv lang).target.app X e).down) := e.2
    exact (langBoxUsing_spec relEnv lang φ p).1 h
      (((reductionGraphUsing (C := C) relEnv lang).source.app X e).down)
      (by simpa [ht] using hred)
  · intro h
    refine (langBoxUsing_spec relEnv lang φ p).2 ?_
    intro q hqp
    let e : (reductionGraphUsing (C := C) relEnv lang).Edge.obj X :=
      ⟨ULift.up (q, p), hqp⟩
    have ht : ((reductionGraphUsing (C := C) relEnv lang).target.app X e).down = p := by
      simp [e, reductionGraphUsing, reductionTargetUsing]
    have hs : ((reductionGraphUsing (C := C) relEnv lang).source.app X e).down = q := by
      simp [e, reductionGraphUsing, reductionSourceUsing]
    have hq' := h e ht
    simpa [hs] using hq'

/-- `◇` over `langReducesUsing` is equivalent to existence of an internal
one-step edge in the presheaf reduction subfunctor. -/
theorem langDiamondUsing_iff_exists_internalStep
    (C : Type u) [CategoryTheory.Category.{v} C]
    (relEnv : RelationEnv) (lang : LanguageDef)
    {X : Opposite C} (φ : Pattern → Prop) (p : Pattern) :
    langDiamondUsing relEnv lang φ p ↔
      ∃ q,
        (((ULift.up (p, q)) : (pairConstPresheaf (C := C)).obj X) ∈
          (reductionSubfunctorUsing (C := C) relEnv lang).obj X) ∧
        φ q := by
  constructor
  · intro h
    rcases (langDiamondUsing_spec relEnv lang φ p).1 h with ⟨q, hpq, hφq⟩
    exact ⟨q, (mem_reductionSubfunctorUsing_iff
      (C := C) (relEnv := relEnv) (lang := lang) (X := X) (p := p) (q := q)).2 hpq, hφq⟩
  · rintro ⟨q, hmem, hφq⟩
    exact (langDiamondUsing_spec relEnv lang φ p).2
      ⟨q, (mem_reductionSubfunctorUsing_iff
        (C := C) (relEnv := relEnv) (lang := lang) (X := X) (p := p) (q := q)).1 hmem, hφq⟩

/-- `□` over `langReducesUsing` is equivalent to universal quantification over
incoming internal edges in the presheaf reduction subfunctor. -/
theorem langBoxUsing_iff_forall_internalStep
    (C : Type u) [CategoryTheory.Category.{v} C]
    (relEnv : RelationEnv) (lang : LanguageDef)
    {X : Opposite C} (φ : Pattern → Prop) (p : Pattern) :
    langBoxUsing relEnv lang φ p ↔
      ∀ q,
        (((ULift.up (q, p)) : (pairConstPresheaf (C := C)).obj X) ∈
          (reductionSubfunctorUsing (C := C) relEnv lang).obj X) →
        φ q := by
  constructor
  · intro h q hmem
    exact (langBoxUsing_spec relEnv lang φ p).1 h q
      ((mem_reductionSubfunctorUsing_iff
        (C := C) (relEnv := relEnv) (lang := lang) (X := X) (p := q) (q := p)).1 hmem)
  · intro h
    refine (langBoxUsing_spec relEnv lang φ p).2 ?_
    intro q hqp
    exact h q ((mem_reductionSubfunctorUsing_iff
      (C := C) (relEnv := relEnv) (lang := lang) (X := X) (p := q) (q := p)).2 hqp)

/-- Default-env corollary of `langDiamondUsing_iff_exists_internalStep`. -/
theorem langDiamond_iff_exists_internalStep
    (C : Type u) [CategoryTheory.Category.{v} C]
    (lang : LanguageDef)
    {X : Opposite C} (φ : Pattern → Prop) (p : Pattern) :
    langDiamond lang φ p ↔
      ∃ q,
        (((ULift.up (p, q)) : (pairConstPresheaf (C := C)).obj X) ∈
          (reductionSubfunctor (C := C) lang).obj X) ∧
        φ q := by
  simpa [langDiamond, reductionSubfunctor] using
    (langDiamondUsing_iff_exists_internalStep
      (C := C) (relEnv := RelationEnv.empty) (lang := lang) (X := X) (φ := φ) (p := p))

/-- Default-env corollary of `langBoxUsing_iff_forall_internalStep`. -/
theorem langBox_iff_forall_internalStep
    (C : Type u) [CategoryTheory.Category.{v} C]
    (lang : LanguageDef)
    {X : Opposite C} (φ : Pattern → Prop) (p : Pattern) :
    langBox lang φ p ↔
      ∀ q,
        (((ULift.up (q, p)) : (pairConstPresheaf (C := C)).obj X) ∈
          (reductionSubfunctor (C := C) lang).obj X) →
        φ q := by
  simpa [langBox, reductionSubfunctor] using
    (langBoxUsing_iff_forall_internalStep
      (C := C) (relEnv := RelationEnv.empty) (lang := lang) (X := X) (φ := φ) (p := p))

/-- Default-env graph-form `◇` characterization. -/
theorem langDiamond_iff_exists_graphStep
    (C : Type u) [CategoryTheory.Category.{v} C]
    (lang : LanguageDef)
    {X : Opposite C} (φ : Pattern → Prop) (p : Pattern) :
    langDiamond lang φ p ↔
      ∃ e : (reductionGraph (C := C) lang).Edge.obj X,
        ((reductionGraph (C := C) lang).source.app X e).down = p ∧
        φ (((reductionGraph (C := C) lang).target.app X e).down) := by
  simpa [langDiamond, reductionGraph] using
    (langDiamondUsing_iff_exists_graphStep
      (C := C) (relEnv := RelationEnv.empty) (lang := lang) (X := X) (φ := φ) (p := p))

/-- Default-env graph-form `□` characterization. -/
theorem langBox_iff_forall_graphIncoming
    (C : Type u) [CategoryTheory.Category.{v} C]
    (lang : LanguageDef)
    {X : Opposite C} (φ : Pattern → Prop) (p : Pattern) :
    langBox lang φ p ↔
      ∀ e : (reductionGraph (C := C) lang).Edge.obj X,
        ((reductionGraph (C := C) lang).target.app X e).down = p →
        φ (((reductionGraph (C := C) lang).source.app X e).down) := by
  simpa [langBox, reductionGraph] using
    (langBoxUsing_iff_forall_graphIncoming
      (C := C) (relEnv := RelationEnv.empty) (lang := lang) (X := X) (φ := φ) (p := p))

/-- Executable premise-aware one-step reduction gives membership in the
internal presheaf relation. -/
theorem exec_mem_reductionSubfunctorUsing
    (C : Type u) [CategoryTheory.Category.{v} C]
    (relEnv : RelationEnv) (lang : LanguageDef)
    {X : Opposite C} {p q : Pattern}
    (hq : q ∈ rewriteWithContextWithPremisesUsing relEnv lang p) :
    ((ULift.up (p, q)) : (pairConstPresheaf (C := C)).obj X) ∈
      (reductionSubfunctorUsing (C := C) relEnv lang).obj X := by
  change langReducesUsing relEnv lang p q
  exact exec_to_langReducesUsing relEnv lang hq

/-- Membership in the internal presheaf relation yields executable
one-step reduction. -/
theorem reductionSubfunctorUsing_mem_exec
    (C : Type u) [CategoryTheory.Category.{v} C]
    (relEnv : RelationEnv) (lang : LanguageDef)
    {X : Opposite C} {p q : Pattern}
    (hmem : ((ULift.up (p, q)) : (pairConstPresheaf (C := C)).obj X) ∈
      (reductionSubfunctorUsing (C := C) relEnv lang).obj X) :
    q ∈ rewriteWithContextWithPremisesUsing relEnv lang p := by
  change langReducesUsing relEnv lang p q at hmem
  exact langReducesUsing_to_exec relEnv lang hmem

end Mettapedia.OSLF.Framework.ToposReduction
