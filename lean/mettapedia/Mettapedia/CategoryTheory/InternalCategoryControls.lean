import Mettapedia.CategoryTheory.InternalCategoryPathMaps
import Mathlib.CategoryTheory.SingleObj

/-!
# Whole composable paths, context changes and retained occurrences

Scalar context changes act on both event endpoints, including a change that
identifies all endpoint values. Independent occurrence identifiers remain in
the complete paths. The internal composition and nonidentity internal map
are exercised at supplied nonconstant sections, rather than only identities.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.InternalCategoryControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open InternalCategoryPathDiagram

abbrev Stage := SingleObj Nat
def stage : Stage := SingleObj.star Nat
abbrev Event := Nat × Nat × Nat

abbrev vertices : Stage ⥤ Type where
  obj _ := Nat
  map factor := TypeCat.ofHom (fun number => (show Nat from factor) * number)
  map_id _ := by apply ConcreteCategory.hom_ext; intro number; exact Nat.one_mul number
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro number
    exact Nat.mul_assoc second first number

abbrev events : Stage ⥤ Type where
  obj _ := Event
  map factor := TypeCat.ofHom (fun edge =>
    (edge.1, (show Nat from factor) * edge.2.1, (show Nat from factor) * edge.2.2))
  map_id _ := by
    apply ConcreteCategory.hom_ext
    intro edge
    change (edge.1, 1 * edge.2.1, 1 * edge.2.2) = edge
    simp only [Nat.one_mul]
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro edge
    change (edge.1, ((show Nat from second) * (show Nat from first)) * edge.2.1,
      ((show Nat from second) * (show Nat from first)) * edge.2.2) =
      (edge.1, (show Nat from second) * ((show Nat from first) * edge.2.1),
        (show Nat from second) * ((show Nat from first) * edge.2.2))
    simp only [Nat.mul_assoc]

def source : events ⟶ vertices where
  app _ := TypeCat.ofHom (fun edge => edge.2.1)
  naturality _ _ _ := rfl

def target : events ⟶ vertices where
  app _ := TypeCat.ofHom (fun edge => edge.2.2)
  naturality _ _ _ := rfl

def graph : InternalGraph (Stage ⥤ Type) := ⟨vertices, events, source, target⟩

def firstEvents : vertices ⟶ events where
  app _ := TypeCat.ofHom (fun number => (7, number, 2 * number))
  naturality _ _ factor := by
    apply ConcreteCategory.hom_ext
    intro number
    change (7, (show Nat from factor) * number, 2 * ((show Nat from factor) * number)) =
      (7, (show Nat from factor) * number, (show Nat from factor) * (2 * number))
    rw [Nat.mul_left_comm 2 (show Nat from factor) number]

def secondEvents : vertices ⟶ events where
  app _ := TypeCat.ofHom (fun number => (9, 2 * number, 3 * number))
  naturality _ _ factor := by
    apply ConcreteCategory.hom_ext
    intro number
    change (9, 2 * ((show Nat from factor) * number), 3 * ((show Nat from factor) * number)) =
      (9, (show Nat from factor) * (2 * number), (show Nat from factor) * (3 * number))
    rw [Nat.mul_left_comm 2 (show Nat from factor) number,
      Nat.mul_left_comm 3 (show Nat from factor) number]

def first : vertices ⟶ (category graph).edge := firstEvents ≫ edgeInclusion graph
def second : vertices ⟶ (category graph).edge := secondEvents ≫ edgeInclusion graph

theorem matching : first ≫ (category graph).target = second ≫ (category graph).source := by
  ext X number
  rfl

def composed : vertices ⟶ (category graph).edge := (category graph).compose first second matching

def origins {first : Vertex graph stage} : {last : Vertex graph stage} →
    Path graph stage first last → List Nat
  | _, .nil => []
  | _, .cons before edge => origins before ++ [edge.1.1]

def readout (path : InternalCategoryDiagram.Arrow ((diagram graph).obj stage)) : List Nat :=
  origins path.2.2

theorem origins_comp {a b c : Vertex graph stage} (first : Path graph stage a b)
    (second : Path graph stage b c) :
    origins (first.comp second) = origins first ++ origins second := by
  induction second with
  | nil => exact (List.append_nil _).symm
  | cons before edge ih =>
      exact (congrArg (fun xs => xs ++ [edge.1.1]) ih).trans (List.append_assoc _ _ _)

theorem origins_cast {a b : Vertex graph stage} (same : a = b) :
    origins (eqToHom same :
      (show (diagram graph).obj stage from a) ⟶ (show (diagram graph).obj stage from b)) = [] := by
  cases same
  rfl

theorem composition_readout
    (first second : InternalCategoryDiagram.Arrow ((diagram graph).obj stage))
    (matching : InternalCategoryDiagram.Arrow.target first = InternalCategoryDiagram.Arrow.source second) :
    readout (InternalCategoryDiagram.Arrow.compose first second matching) =
      readout first ++ readout second := by
  change origins (first.2.2.comp ((eqToHom matching).comp second.2.2)) = _
  rw [origins_comp, origins_comp, origins_cast, List.nil_append]
  rfl

theorem complete_composition_readout (number : Nat) :
    readout (composed.app stage number) = [7, 9] := by
  have computed := InternalCategoryDiagram.composeWith_apply (diagram graph)
    first second matching stage number
  exact (congrArg readout computed).trans
    (composition_readout (first.app stage number) (second.app stage number) _)

theorem complete_source_readout (number : Nat) :
    (category graph).source.app stage (composed.app stage number) = number :=
  congrArg (fun (map : vertices ⟶ (category graph).vertex) => map.app stage number)
    ((category graph).compose_source first second matching)

theorem complete_target_readout (number : Nat) :
    (category graph).target.app stage (composed.app stage number) = 3 * number :=
  congrArg (fun (map : vertices ⟶ (category graph).vertex) => map.app stage number)
    ((category graph).compose_target first second matching)

theorem same_endpoints_distinct_paths :
    edge graph stage (7, 1, 2) ≠ edge graph stage (8, 1, 2) := by
  intro same
  have read := congrArg readout same
  change ([7] : List Nat) = [8] at read
  cases read

theorem singleton_is_not_identity :
    edge graph stage (7, 1, 1) ≠
      (category graph).unit.app stage (show (category graph).vertex.obj stage from (1 : Nat)) := by
  intro same
  have read := congrArg readout same
  change ([7] : List Nat) = [] at read
  cases read

theorem no_endpoint_origin_decoder :
    ¬ ∃ decode : Nat × Nat → List Nat,
      ∀ path : InternalCategoryDiagram.Arrow ((diagram graph).obj stage),
        decode (path.1, path.2.1) = readout path := by
  rintro ⟨decode, correct⟩
  have first := correct (edge graph stage (7, 1, 2))
  have second := correct (edge graph stage (8, 1, 2))
  have same : ([7] : List Nat) = [8] := first.symm.trans second
  cases same

theorem nonmatching_edges_do_not_compose :
    InternalCategoryDiagram.Arrow.target (edge graph stage (7, 1, 2)) ≠
      InternalCategoryDiagram.Arrow.source (edge graph stage (9, 4, 5)) := by
  change (2 : Nat) ≠ 4
  decide

def doubledVertices : vertices ⟶ vertices where
  app _ := TypeCat.ofHom (fun number => 2 * number)
  naturality _ _ factor := by
    apply ConcreteCategory.hom_ext
    intro number
    exact Nat.mul_left_comm 2 (show Nat from factor) number

def doubledEvents : events ⟶ events where
  app _ := TypeCat.ofHom (fun edge => (edge.1 + 100, 2 * edge.2.1, 2 * edge.2.2))
  naturality _ _ factor := by
    apply ConcreteCategory.hom_ext
    intro edge
    change (edge.1 + 100, 2 * ((show Nat from factor) * edge.2.1),
      2 * ((show Nat from factor) * edge.2.2)) =
      (edge.1 + 100, (show Nat from factor) * (2 * edge.2.1),
        (show Nat from factor) * (2 * edge.2.2))
    rw [Nat.mul_left_comm 2 (show Nat from factor) edge.2.1,
      Nat.mul_left_comm 2 (show Nat from factor) edge.2.2]

def doubling : InternalGraph.Hom graph graph where
  vertex := doubledVertices
  edge := doubledEvents
  source := by ext X edge; rfl
  target := by ext X edge; rfl

theorem actual_nonidentity_edge_image :
    (InternalCategoryPathMaps.internalFunctor doubling).edge.app stage (edge graph stage (7, 1, 2)) =
      edge graph stage (107, 2, 4) := InternalCategoryPathMaps.edge_readout doubling stage _

theorem changed_edge_origin_readout :
    readout ((InternalCategoryPathMaps.internalFunctor doubling).edge.app stage
      (edge graph stage (7, 1, 2))) = [107] :=
  congrArg readout actual_nonidentity_edge_image

theorem zero_context_change_keeps_origins :
    (category graph).edge.map (show stage ⟶ stage from (0 : Nat)) (edge graph stage (7, 1, 2)) =
      edge graph stage (7, 0, 0) := edge_restriction graph _ _

end Mettapedia.CategoryTheory.InternalCategoryControls
