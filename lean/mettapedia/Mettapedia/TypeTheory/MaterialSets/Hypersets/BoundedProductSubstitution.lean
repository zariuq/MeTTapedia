import Mettapedia.TypeTheory.MaterialSets.Hypersets.BoundedDependentProducts

/-!
# Substitution of bounded material products

Substitution constructs a graph directly by separation of the new dependent
pair set. Its membership relation retains the new argument and the original
graph entry. Evaluation, encoding, identity and composition commute.

For material pullbacks, the new fibre consists of pairs rather than the old
arguments themselves. The Beck--Chevalley comparison uses the constructed
coordinate equivalence of these fibres, not a false equality of their freshly
encoded graphs. Every future section here is a complete function on its actual
member type; no representative or inverse is selected by choice.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.BoundedProductSubstitution

universe u

open HSet BoundedDependentProducts

/-- Substitution as an actual separated graph relation. -/
def reindexGraph {X Z : HSet.{u}} (B : Element X → HSet.{u}) (Y : HSet.{u})
    (σ : Element Z → Element X) (G : HSet.{u}) : HSet.{u} :=
  HSet.sep (fun z => ∃ (a : Element Z) (b : Element (B (σ a))),
    kpair a.1 b.1 = z ∧ kpair (σ a).1 b.1 ∈ G) (pairSet Z (fun a => B (σ a)) Y)

theorem mem_reindexGraph_iff {X Z Y G z : HSet.{u}} {B : Element X → HSet.{u}}
    (bounded : ∀ a, B a ⊆ Y) (σ : Element Z → Element X) :
    z ∈ reindexGraph B Y σ G ↔ ∃ (a : Element Z) (b : Element (B (σ a))),
      kpair a.1 b.1 = z ∧ kpair (σ a).1 b.1 ∈ G := by
  refine mem_sep.trans ⟨And.right, ?_⟩
  rintro ⟨a, b, same, entry⟩
  exact ⟨mem_pairSet_iff (fun a => bounded (σ a)) |>.mpr ⟨a, b, same⟩,
    a, b, same, entry⟩

theorem reindexGraph_eq_graph {X Z Y : HSet.{u}} {B : Element X → HSet.{u}}
    (bounded : ∀ a, B a ⊆ Y) (σ : Element Z → Element X)
    (g : Element (product X B Y)) :
    reindexGraph B Y σ g.1 = graph Y (fun a => evaluate g (σ a)) := by
  apply ext
  intro z
  rw [mem_reindexGraph_iff bounded, mem_graph_iff (fun a => bounded (σ a))]
  constructor
  · rintro ⟨a, b, same, entry⟩
    exact ⟨a, (congrArg (kpair a.1) (evaluate_value_of_entry g (σ a) b entry)).trans same⟩
  · rintro ⟨a, same⟩
    exact ⟨a, evaluate g (σ a), same, evaluate_entry g (σ a)⟩

/-- The substituted material member has a proved total single-valued graph. -/
def reindex {X Z Y : HSet.{u}} {B : Element X → HSet.{u}}
    (bounded : ∀ a, B a ⊆ Y) (σ : Element Z → Element X)
    (g : Element (product X B Y)) : Element (product Z (fun a => B (σ a)) Y) :=
  ⟨reindexGraph B Y σ g.1, (reindexGraph_eq_graph bounded σ g).symm ▸
    (BoundedDependentProducts.graphMember (fun a => bounded (σ a)) (fun a => evaluate g (σ a))).2⟩

theorem reindex_eq_graphMember {X Z Y : HSet.{u}} {B : Element X → HSet.{u}}
    (bounded : ∀ a, B a ⊆ Y) (σ : Element Z → Element X)
    (g : Element (product X B Y)) :
    reindex bounded σ g = BoundedDependentProducts.graphMember (fun a => bounded (σ a))
      (fun a => evaluate g (σ a)) := El.ext propositional (reindexGraph_eq_graph bounded σ g)

/-- Evaluation is the complete dependent substitution, with the original
fibre membership evidence retained. -/
theorem evaluate_reindex {X Z Y : HSet.{u}} {B : Element X → HSet.{u}}
    (bounded : ∀ a, B a ⊆ Y) (σ : Element Z → Element X)
    (g : Element (product X B Y)) (a : Element Z) :
    evaluate (reindex bounded σ g) a = evaluate g (σ a) := by
  rw [reindex_eq_graphMember]
  exact evaluate_beta _ _ _

theorem reindex_graphMember {X Z Y : HSet.{u}} {B : Element X → HSet.{u}}
    (bounded : ∀ a, B a ⊆ Y) (σ : Element Z → Element X) (s : Section X B) :
    reindex bounded σ (BoundedDependentProducts.graphMember bounded s) =
      BoundedDependentProducts.graphMember (fun a => bounded (σ a)) (fun a => s (σ a)) := by
  rw [reindex_eq_graphMember]
  exact congrArg (BoundedDependentProducts.graphMember (fun a => bounded (σ a)))
    (funext fun a => evaluate_beta bounded s (σ a))

theorem reindex_id {X Y : HSet.{u}} {B : Element X → HSet.{u}}
    (bounded : ∀ a, B a ⊆ Y) (g : Element (product X B Y)) :
    reindex bounded id g = g := by
  apply (productEquiv bounded).injective
  exact funext (evaluate_reindex bounded id g)

theorem reindex_comp {X Z W Y : HSet.{u}} {B : Element X → HSet.{u}}
    (bounded : ∀ a, B a ⊆ Y) (σ : Element Z → Element X) (τ : Element W → Element Z)
    (g : Element (product X B Y)) :
    reindex (fun a => bounded (σ a)) τ (reindex bounded σ g) =
      reindex bounded (fun a => σ (τ a)) g := by
  have sections : evaluate (reindex (fun a => bounded (σ a)) τ (reindex bounded σ g)) =
      evaluate (reindex bounded (fun a => σ (τ a)) g) := by
    funext a
    calc
      evaluate (reindex (fun a => bounded (σ a)) τ (reindex bounded σ g)) a =
          evaluate (reindex bounded σ g) (τ a) :=
        evaluate_reindex (X := Z) (Z := W) (Y := Y) (B := fun a => B (σ a))
          (fun a => bounded (σ a)) τ (reindex bounded σ g) a
      _ = evaluate g (σ (τ a)) := evaluate_reindex bounded σ g (τ a)
      _ = evaluate (reindex bounded (fun a => σ (τ a)) g) a :=
        (evaluate_reindex bounded (fun a => σ (τ a)) g a).symm
  exact (productEquiv (fun a => bounded (σ (τ a)))).injective sections

/-- Every actual commuting argument square induces a commuting material
graph square, even when the argument maps are noninjective. -/
theorem reindex_commuting_square {X Z W V Y : HSet.{u}} {B : Element X → HSet.{u}}
    (bounded : ∀ a, B a ⊆ Y) (σ : Element Z → Element X) (τ : Element W → Element X)
    (left : Element V → Element Z) (right : Element V → Element W)
    (commutes : ∀ a, σ (left a) = τ (right a)) (g : Element (product X B Y)) :
    (reindex (fun a => bounded (σ a)) left (reindex bounded σ g)).1 =
      (reindex (fun a => bounded (τ a)) right (reindex bounded τ g)).1 := by
  rw [reindex_comp, reindex_comp]
  change reindexGraph B Y (fun a => σ (left a)) g.1 =
    reindexGraph B Y (fun a => τ (right a)) g.1
  rw [reindexGraph_eq_graph bounded, reindexGraph_eq_graph bounded]
  apply ext
  intro z
  rw [mem_graph_iff (fun a => bounded (σ (left a))),
    mem_graph_iff (fun a => bounded (τ (right a)))]
  constructor
  · rintro ⟨a, same⟩
    exact ⟨a, (congrArg (fun x => kpair a.1 (evaluate g x).1) (commutes a)).symm.trans same⟩
  · rintro ⟨a, same⟩
    exact ⟨a, (congrArg (fun x => kpair a.1 (evaluate g x).1) (commutes a)).trans same⟩

/-- A domain equivalence acts on all dependent sections, with an explicitly
constructed inverse retaining the actual material values. -/
def sectionEquiv {X Z : HSet.{u}} (B : Element X → HSet.{u}) (e : Element Z ≃ Element X) :
    Section X B ≃ Section Z (fun a => B (e a)) where
  toFun s a := s (e a)
  invFun t a := ⟨(t (e.symm a)).1, by
    have member := (t (e.symm a)).2
    change (t (e.symm a)).1 ∈ B (e (e.symm a)) at member
    rw [e.apply_symm_apply] at member
    exact member⟩
  left_inv s := by
    funext a
    apply El.ext propositional
    change (s (e (e.symm a))).1 = (s a).1
    rw [e.apply_symm_apply]
  right_inv t := by
    funext a
    apply El.ext propositional
    change (t (e.symm (e a))).1 = (t a).1
    rw [e.symm_apply_apply]

/-- The induced material product equivalence uses the direct row decoder
and separated graph encoders in both directions. -/
def productReindexEquiv {X Z Y : HSet.{u}} {B : Element X → HSet.{u}}
    (bounded : ∀ a, B a ⊆ Y) (e : Element Z ≃ Element X) :
    Element (product X B Y) ≃ Element (product Z (fun a => B (e a)) Y) :=
  (productEquiv bounded).trans ((sectionEquiv B e).trans
    (productEquiv (fun a => bounded (e a))).symm)

theorem productReindexEquiv_reindex {X Z Y : HSet.{u}} {B : Element X → HSet.{u}}
    (bounded : ∀ a, B a ⊆ Y) (e : Element Z ≃ Element X)
    (g : Element (product X B Y)) :
    productReindexEquiv bounded e g = reindex bounded e g :=
  (reindex_eq_graphMember bounded e g).symm

theorem productReindexEquiv_evaluate {X Z Y : HSet.{u}} {B : Element X → HSet.{u}}
    (bounded : ∀ a, B a ⊆ Y) (e : Element Z ≃ Element X)
    (g : Element (product X B Y)) (a : Element Z) :
    evaluate (productReindexEquiv bounded e g) a = evaluate g (e a) :=
  evaluate_beta (fun a => bounded (e a)) (fun a => evaluate g (e a)) a

/-! ## Changing a proved material bound -/

def changeBound {X Y Z : HSet.{u}} {B : Element X → HSet.{u}}
    (first : ∀ a, B a ⊆ Y) (second : ∀ a, B a ⊆ Z)
    (g : Element (product X B Y)) : Element (product X B Z) :=
  ⟨g.1, product_bound_independent first second ▸ g.2⟩

theorem evaluate_changeBound {X Y Z : HSet.{u}} {B : Element X → HSet.{u}}
    (first : ∀ a, B a ⊆ Y) (second : ∀ a, B a ⊆ Z)
    (g : Element (product X B Y)) : evaluate (changeBound first second g) = evaluate g :=
  funext fun _ => El.ext propositional rfl

def changeBoundEquiv {X Y Z : HSet.{u}} {B : Element X → HSet.{u}}
    (first : ∀ a, B a ⊆ Y) (second : ∀ a, B a ⊆ Z) :
    Element (product X B Y) ≃ Element (product X B Z) where
  toFun := changeBound first second
  invFun := changeBound second first
  left_inv _ := El.ext propositional rfl
  right_inv _ := El.ext propositional rfl

theorem reindex_changeBound {X W Y Z : HSet.{u}} {B : Element X → HSet.{u}}
    (first : ∀ a, B a ⊆ Y) (second : ∀ a, B a ⊆ Z)
    (σ : Element W → Element X) (g : Element (product X B Y)) :
    reindex second σ (changeBound first second g) =
      changeBound (fun a => first (σ a)) (fun a => second (σ a)) (reindex first σ g) := by
  apply (productEquiv (fun a => second (σ a))).injective
  funext a
  exact (evaluate_reindex second σ _ a).trans
    ((congrArg (fun term => term (σ a)) (evaluate_changeBound first second g)).trans
      ((evaluate_reindex first σ g a).symm.trans
        (congrArg (fun term => term a) (evaluate_changeBound _ _ _)).symm))

end Mettapedia.TypeTheory.MaterialSets.Hypersets.BoundedProductSubstitution
