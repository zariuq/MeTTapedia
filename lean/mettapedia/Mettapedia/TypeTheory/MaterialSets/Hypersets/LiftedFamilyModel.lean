import Mettapedia.TypeTheory.MaterialSets.Hypersets.UniverseLift
import Mettapedia.TypeTheory.MaterialSets.Hypersets.DependentProduct
import Mettapedia.TypeTheory.MaterialSets.MembershipEvidence
import Mathlib.Logic.Small.Basic

/-!
# Constructed dependent families at a raised hyperset bound

Every section of a family of `HSet.{u}` members has an actual function graph
in `HSet.{u + 1}`. Uniform graph presentations at that bound let us collect
all these graphs using their actual section type as the index. No selected
quotient presentations, supplied small section carrier, or replacement
operator is an input.

Evaluation uses separation in the original fibre followed by union. The
raised graph identifies exactly one original member, so this construction
returns the original value without selecting a preimage of universe lifting.
The graph/section comparison proves beta and eta with those actual values.
The level increase is essential: this is not a same-level collection theorem,
a universal set, or the selection of a native foundational axiom package.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.LiftedFamilyModel

universe u

abbrev Elements (X : HSet.{u}) := El (fun x X : HSet.{u} => x ∈ X) X
abbrev Section (X : HSet.{u}) (B : Elements X → HSet.{u}) :=
  (a : Elements X) → Elements (B a)

private theorem propositionalMembership :
    PropositionalMembership (fun x X : HSet.{u} => x ∈ X) := fun _ _ => inferInstance

/-- Construct an actual raised graph from the original dependent member values. -/
def sectionGraph {X : HSet.{u}} {B : Elements X → HSet.{u}} (s : Section X B) :
    HSet.{u + 1} := HSet.imageUp (fun a => HSet.kpair a.1 (s a).1)

theorem mem_sectionGraph_iff {X : HSet.{u}} {B : Elements X → HSet.{u}}
    {s : Section X B} {z : HSet.{u + 1}} :
    z ∈ sectionGraph s ↔ ∃ a : Elements X, HSet.lift (HSet.kpair a.1 (s a).1) = z :=
  HSet.mem_imageUp_iff

/-- Lifted material graph rows identify the actual original result uniquely. -/
theorem liftedPair_mem_sectionGraph_iff {X : HSet.{u}} {B : Elements X → HSet.{u}}
    (s : Section X B) (a : Elements X) (b : HSet.{u}) :
    HSet.lift (HSet.kpair a.1 b) ∈ sectionGraph s ↔ b = (s a).1 := by
  constructor
  · intro member
    obtain ⟨a', same⟩ := mem_sectionGraph_iff.mp member
    have pairs := HSet.kpair_inj.mp (HSet.lift_injective same)
    have arguments : a' = a := El.ext propositionalMembership pairs.1
    cases arguments
    exact pairs.2.symm
  · intro same
    exact mem_sectionGraph_iff.mpr ⟨a, congrArg (fun b => HSet.lift (HSet.kpair a.1 b)) same.symm⟩

/-- All actual section graphs are collected at the raised graph bound. -/
def productUp (X : HSet.{u}) (B : Elements X → HSet.{u}) : HSet.{u + 1} :=
  HSet.range (fun s : Section X B =>
    HSet.imageUpGraph (fun a => HSet.kpair a.1 (s a).1))

theorem mem_productUp_iff {X : HSet.{u}} {B : Elements X → HSet.{u}}
    {g : HSet.{u + 1}} : g ∈ productUp X B ↔ ∃ s : Section X B, sectionGraph s = g :=
  HSet.mem_range

def graphMember {X : HSet.{u}} {B : Elements X → HSet.{u}} (s : Section X B) :
    Elements (productUp X B) :=
  ⟨sectionGraph s, mem_productUp_iff.mpr ⟨s, rfl⟩⟩

/-- Separate in the original fibre, retaining original hyperset values. -/
def row {X : HSet.{u}} {B : Elements X → HSet.{u}} (g : HSet.{u + 1}) (a : Elements X) :
    HSet.{u} := HSet.sep (fun b => HSet.lift (HSet.kpair a.1 b) ∈ g) (B a)

theorem row_sectionGraph {X : HSet.{u}} {B : Elements X → HSet.{u}}
    (s : Section X B) (a : Elements X) :
    row (B := B) (sectionGraph s) a = {(s a).1} := by
  apply HSet.ext
  intro b
  rw [row, HSet.mem_sep, liftedPair_mem_sectionGraph_iff, HSet.mem_singleton]
  exact ⟨And.right, fun same => ⟨same ▸ (s a).2, same⟩⟩

/-- A union of the separated singleton extracts the original member.
Existential section membership is used only to prove its membership. -/
def evaluate {X : HSet.{u}} {B : Elements X → HSet.{u}}
    (graph : Elements (productUp X B)) : Section X B := fun a =>
  ⟨HSet.sUnion (row (B := B) graph.1 a), by
    obtain ⟨s, same⟩ := mem_productUp_iff.mp graph.2
    rw [← same, row_sectionGraph, HSet.sUnion_singleton]
    exact (s a).2⟩

theorem evaluate_graph_value {X : HSet.{u}} {B : Elements X → HSet.{u}}
    (s : Section X B) (a : Elements X) :
    (evaluate (graphMember s) a).1 = (s a).1 := by
  change HSet.sUnion (row (B := B) (sectionGraph s) a) = _
  rw [row_sectionGraph, HSet.sUnion_singleton]

theorem evaluate_graph {X : HSet.{u}} {B : Elements X → HSet.{u}} (s : Section X B) :
    evaluate (graphMember s) = s := by
  funext a
  exact El.ext propositionalMembership (evaluate_graph_value s a)

theorem graph_evaluate {X : HSet.{u}} {B : Elements X → HSet.{u}}
    (graph : Elements (productUp X B)) : sectionGraph (evaluate graph) = graph.1 := by
  obtain ⟨s, same⟩ := mem_productUp_iff.mp graph.2
  have memberEq : graph = graphMember s := El.ext propositionalMembership same.symm
  cases memberEq
  exact congrArg sectionGraph (evaluate_graph s)

/-- The actual raised material product and the full original dependent
function space have explicit inverse operations, with no choice. -/
def productEquiv (X : HSet.{u}) (B : Elements X → HSet.{u}) :
    Elements (productUp X B) ≃ Section X B where
  toFun := evaluate
  invFun := graphMember
  left_inv graph := El.ext propositionalMembership (graph_evaluate graph)
  right_inv := evaluate_graph

theorem sectionGraph_injective {X : HSet.{u}} {B : Elements X → HSet.{u}} :
    Function.Injective (sectionGraph (X := X) (B := B)) := by
  intro first second same
  have members : graphMember first = graphMember second := El.ext propositionalMembership same
  exact (evaluate_graph first).symm.trans ((congrArg evaluate members).trans (evaluate_graph second))

/-! ## Actual dependent sums with original-value decoding -/

/-- Decode a raised value only under an original material bound, by
separation and union. This operation does not invert lifting on its carrier. -/
def boundedRead (bound : HSet.{u}) (raised : HSet.{u + 1}) : HSet.{u} :=
  HSet.sUnion (HSet.sep (fun original => HSet.lift original = raised) bound)

theorem boundedRead_lift {bound x : HSet.{u}} (member : x ∈ bound) :
    boundedRead bound (HSet.lift x) = x := by
  have separated : HSet.sep (fun original => HSet.lift original = HSet.lift x) bound = {x} := by
    apply HSet.ext
    intro y
    rw [HSet.mem_sep, HSet.mem_singleton]
    exact ⟨fun belongs => HSet.lift_injective belongs.2,
      fun same => ⟨same ▸ member, congrArg HSet.lift same⟩⟩
  exact (congrArg HSet.sUnion separated).trans (HSet.sUnion_singleton x)

def sumUp (X : HSet.{u}) (B : Elements X → HSet.{u}) : HSet.{u + 1} :=
  HSet.imageUp (fun pair : Σ' a : Elements X, Elements (B a) => HSet.kpair pair.1.1 pair.2.1)

theorem mem_sumUp_iff {X : HSet.{u}} {B : Elements X → HSet.{u}} {z : HSet.{u + 1}} :
    z ∈ sumUp X B ↔ ∃ a : Elements X, ∃ b : Elements (B a), HSet.lift (HSet.kpair a.1 b.1) = z := by
  rw [sumUp, HSet.mem_imageUp_iff]
  exact ⟨fun ⟨⟨a, b⟩, same⟩ => ⟨a, b, same⟩, fun ⟨a, b, same⟩ => ⟨⟨a, b⟩, same⟩⟩

def sumPair {X : HSet.{u}} {B : Elements X → HSet.{u}} (a : Elements X) (b : Elements (B a)) :
    Elements (sumUp X B) :=
  ⟨HSet.lift (HSet.kpair a.1 b.1), mem_sumUp_iff.mpr ⟨a, b, rfl⟩⟩

def sumFirst {X : HSet.{u}} {B : Elements X → HSet.{u}}
    (pair : Elements (sumUp X B)) : Elements X :=
  ⟨boundedRead X (HSet.fst pair.1), by
    obtain ⟨a, b, same⟩ := mem_sumUp_iff.mp pair.2
    rw [← same, HSet.lift_kpair, HSet.fst_kpair, boundedRead_lift a.2]
    exact a.2⟩

theorem sumFirst_pair_value {X : HSet.{u}} {B : Elements X → HSet.{u}}
    (a : Elements X) (b : Elements (B a)) : (sumFirst (sumPair a b)).1 = a.1 := by
  change boundedRead X (HSet.fst (HSet.lift (HSet.kpair a.1 b.1))) = a.1
  rw [HSet.lift_kpair, HSet.fst_kpair, boundedRead_lift a.2]

theorem sumFirst_pair {X : HSet.{u}} {B : Elements X → HSet.{u}}
    (a : Elements X) (b : Elements (B a)) : sumFirst (sumPair a b) = a :=
  El.ext propositionalMembership (sumFirst_pair_value a b)

def sumSecond {X : HSet.{u}} {B : Elements X → HSet.{u}}
    (pair : Elements (sumUp X B)) : Elements (B (sumFirst pair)) :=
  ⟨boundedRead (B (sumFirst pair)) (HSet.snd pair.1), by
    obtain ⟨a, b, same⟩ := mem_sumUp_iff.mp pair.2
    have pairEq : pair = sumPair a b := El.ext propositionalMembership same.symm
    cases pairEq
    rw [sumFirst_pair]
    change boundedRead (B a) (HSet.snd (HSet.lift (HSet.kpair a.1 b.1))) ∈ B a
    rw [HSet.lift_kpair, HSet.snd_kpair, boundedRead_lift b.2]
    exact b.2⟩

theorem sumSecond_pair_value {X : HSet.{u}} {B : Elements X → HSet.{u}}
    (a : Elements X) (b : Elements (B a)) : (sumSecond (sumPair a b)).1 = b.1 := by
  change boundedRead (B (sumFirst (sumPair a b)))
    (HSet.snd (HSet.lift (HSet.kpair a.1 b.1))) = b.1
  rw [sumFirst_pair, HSet.lift_kpair, HSet.snd_kpair, boundedRead_lift b.2]

private theorem elements_heq {X Y : HSet.{u}} (same : X = Y)
    (first : Elements X) (second : Elements Y) (values : first.1 = second.1) : HEq first second := by
  cases same
  exact heq_of_eq (El.ext propositionalMembership values)

theorem sumSecond_pair_heq {X : HSet.{u}} {B : Elements X → HSet.{u}}
    (a : Elements X) (b : Elements (B a)) : HEq (sumSecond (sumPair a b)) b :=
  elements_heq (congrArg B (sumFirst_pair a b)) _ _ (sumSecond_pair_value a b)

theorem sumPair_projections {X : HSet.{u}} {B : Elements X → HSet.{u}}
    (pair : Elements (sumUp X B)) : sumPair (sumFirst pair) (sumSecond pair) = pair := by
  obtain ⟨a, b, same⟩ := mem_sumUp_iff.mp pair.2
  have pairEq : pair = sumPair a b := El.ext propositionalMembership same.symm
  cases pairEq
  apply El.ext propositionalMembership
  exact congrArg HSet.lift (congrArg₂ HSet.kpair (sumFirst_pair_value a b) (sumSecond_pair_value a b))

/-- Explicit original-value projections and material pairing have both
inverse laws for the actual raised dependent sum. -/
def sumEquiv (X : HSet.{u}) (B : Elements X → HSet.{u}) :
    Elements (sumUp X B) ≃ Σ' a : Elements X, Elements (B a) where
  toFun pair := ⟨sumFirst pair, sumSecond pair⟩
  invFun pair := sumPair pair.1 pair.2
  left_inv := sumPair_projections
  right_inv pair := PSigma.ext (sumFirst_pair pair.1 pair.2) (sumSecond_pair_heq pair.1 pair.2)

/-- The raised material product's member carrier has the explicitly
constructed original section model at the lower host level. -/
theorem product_members_small (X : HSet.{u}) (B : Elements X → HSet.{u}) :
    Small.{u + 1} (Elements (productUp X B)) := Small.mk' (productEquiv X B)

theorem sum_members_small (X : HSet.{u}) (B : Elements X → HSet.{u}) :
    Small.{u + 1} (Elements (sumUp X B)) := Small.mk' (sumEquiv X B)

/-! ## Agreement with supplied same-level constructions -/

/-- The independently constructed raised graph equals the lift of the
same-level image whenever a same-level presentation is supplied. -/
theorem sectionGraph_eq_lift_image (p : HSet.Presentation.{u}) {X : HSet.{u}}
    {B : Elements X → HSet.{u}} (s : Section X B) :
    sectionGraph s = HSet.lift (HSet.image p X (fun a => HSet.kpair a.1 (s a).1)) := by
  apply HSet.ext
  intro z
  rw [mem_sectionGraph_iff, HSet.mem_lift_iff]
  constructor
  · rintro ⟨a, same⟩
    exact ⟨_, HSet.mem_image.mpr ⟨a, rfl⟩, same⟩
  · rintro ⟨original, member, raised⟩
    obtain ⟨a, same⟩ := HSet.mem_image.mp member
    exact ⟨a, (congrArg HSet.lift same).trans raised⟩

theorem sectionGraph_eq_lift_productMember (p : HSet.Presentation.{u}) {X : HSet.{u}}
    {B : Elements X → HSet.{u}} (s : Section X B) :
    sectionGraph s = HSet.lift ((HSet.piSetEquiv p X B).symm s).1 :=
  sectionGraph_eq_lift_image p s

/-- The actual raised collecting set agrees with the lifted powerset
product. The supplied presentation is used only by the compared construction. -/
theorem productUp_eq_lift_dependentProduct (p : HSet.Presentation.{u})
    (X : HSet.{u}) (B : Elements X → HSet.{u}) :
    productUp X B = HSet.lift (HSet.dependentProduct p X B) := by
  apply HSet.ext
  intro z
  rw [mem_productUp_iff, HSet.mem_lift_iff]
  constructor
  · rintro ⟨s, same⟩
    exact ⟨((HSet.piSetEquiv p X B).symm s).1, ((HSet.piSetEquiv p X B).symm s).2,
      (sectionGraph_eq_lift_productMember p s).symm.trans same⟩
  · rintro ⟨original, member, raised⟩
    let g : Elements (HSet.dependentProduct p X B) := ⟨original, member⟩
    exact ⟨HSet.piSetEquiv p X B g, (sectionGraph_eq_lift_productMember p _).trans
      ((congrArg (fun g : Elements (HSet.dependentProduct p X B) => HSet.lift g.1)
        ((HSet.piSetEquiv p X B).symm_apply_apply g)).trans raised)⟩

theorem sumUp_eq_lift_sigmaSet (p : HSet.Presentation.{u})
    (X : HSet.{u}) (B : Elements X → HSet.{u}) :
    sumUp X B = HSet.lift (sigmaSet (HSet.dependentReplacement p) HSet.union HSet.kuratowski X B) := by
  apply HSet.ext
  intro z
  rw [mem_sumUp_iff, HSet.mem_lift_iff]
  constructor
  · rintro ⟨a, b, same⟩
    exact ⟨_, HSet.mem_sigmaSet_iff.mpr ⟨a, b, rfl⟩, same⟩
  · rintro ⟨original, member, raised⟩
    obtain ⟨a, b, same⟩ := HSet.mem_sigmaSet_iff.mp member
    exact ⟨a, b, (congrArg HSet.lift same).trans raised⟩

/-! ## Substitution of actual member sections -/

/-- Reindex a material graph by evaluating its original members and
constructing the actual graph of the substituted section. -/
def pullGraph {X Y : HSet.{u}} {B : Elements X → HSet.{u}}
    (σ : Elements Y → Elements X) (graph : Elements (productUp X B)) :
    Elements (productUp Y (B ∘ σ)) := graphMember (fun a => evaluate graph (σ a))

theorem evaluate_pullGraph {X Y : HSet.{u}} {B : Elements X → HSet.{u}}
    (σ : Elements Y → Elements X) (graph : Elements (productUp X B)) :
    evaluate (pullGraph σ graph) = fun a => evaluate graph (σ a) := evaluate_graph _

theorem pullGraph_id {X : HSet.{u}} {B : Elements X → HSet.{u}}
    (graph : Elements (productUp X B)) : pullGraph id graph = graph :=
  El.ext propositionalMembership (graph_evaluate graph)

theorem pullGraph_comp {X Y Z : HSet.{u}} {B : Elements X → HSet.{u}}
    (σ : Elements Y → Elements X) (τ : Elements Z → Elements Y)
    (graph : Elements (productUp X B)) :
    pullGraph (σ ∘ τ) graph = pullGraph τ (pullGraph σ graph) := by
  apply (productEquiv Z (B ∘ (σ ∘ τ))).injective
  change evaluate (pullGraph (σ ∘ τ) graph) = evaluate (pullGraph τ (pullGraph σ graph))
  rw [evaluate_pullGraph, evaluate_pullGraph, evaluate_pullGraph]
  rfl

/-! ## Positive and negative size and family controls -/

theorem product_inhabited_iff_section (X : HSet.{u}) (B : Elements X → HSet.{u}) :
    Nonempty (Elements (productUp X B)) ↔ Nonempty (Section X B) :=
  ⟨fun ⟨g⟩ => ⟨evaluate g⟩, fun ⟨s⟩ => ⟨graphMember s⟩⟩

theorem sectionGraph_empty (B : Elements (∅ : HSet.{u}) → HSet.{u})
    (s : Section ∅ B) : sectionGraph s = ∅ := by
  apply HSet.eq_empty_iff.mpr
  intro z member
  obtain ⟨a, _⟩ := mem_sectionGraph_iff.mp member
  exact HSet.notMem_empty a.1 a.2

def emptySection (B : Elements (∅ : HSet.{u}) → HSet.{u}) : Section ∅ B :=
  fun a => (HSet.notMem_empty a.1 a.2).elim

theorem productUp_empty (B : Elements (∅ : HSet.{u}) → HSet.{u}) :
    productUp ∅ B = {∅} := by
  apply HSet.ext
  intro g
  rw [mem_productUp_iff, HSet.mem_singleton]
  exact ⟨fun ⟨s, same⟩ => same.symm.trans (sectionGraph_empty B s),
    fun same => ⟨emptySection B, (sectionGraph_empty B _).trans same.symm⟩⟩

theorem productUp_eq_empty_of_empty_fibre {X : HSet.{u}} {B : Elements X → HSet.{u}}
    (a : Elements X) (empty : B a = ∅) : productUp X B = ∅ := by
  apply HSet.eq_empty_iff.mpr
  intro g member
  obtain ⟨s, _⟩ := mem_productUp_iff.mp member
  exact HSet.notMem_empty (s a).1 (empty ▸ (s a).2)

theorem productUp_singleton_empty :
    productUp ({∅} : HSet.{u}) (fun _ => ∅) = ∅ :=
  productUp_eq_empty_of_empty_fibre ⟨∅, HSet.mem_singleton_self _⟩ rfl

def singletonSection (x y : HSet.{u}) : Section {x} (fun _ => {y}) :=
  fun _ => ⟨y, HSet.mem_singleton_self _⟩

theorem sectionGraph_singleton_singleton (x y : HSet.{u})
    (s : Section {x} (fun _ => {y})) : sectionGraph s = {HSet.lift (HSet.kpair x y)} := by
  apply HSet.ext
  intro z
  rw [mem_sectionGraph_iff, HSet.mem_singleton]
  constructor
  · rintro ⟨a, same⟩
    have input := HSet.mem_singleton.mp a.2
    have result := HSet.mem_singleton.mp (s a).2
    exact same.symm.trans (congrArg HSet.lift (congrArg₂ HSet.kpair input result))
  · intro same
    let a : Elements ({x} : HSet.{u}) := ⟨x, HSet.mem_singleton_self _⟩
    have result : (s a).1 = y := HSet.mem_singleton.mp (s a).2
    exact ⟨a, (congrArg (fun b => HSet.lift (HSet.kpair x b)) result).trans same.symm⟩

theorem productUp_singleton_singleton (x y : HSet.{u}) :
    productUp {x} (fun _ => {y}) = {{HSet.lift (HSet.kpair x y)}} := by
  apply HSet.ext
  intro g
  rw [mem_productUp_iff, HSet.mem_singleton]
  exact ⟨fun ⟨s, same⟩ => same.symm.trans (sectionGraph_singleton_singleton x y s),
    fun same => ⟨singletonSection x y, (sectionGraph_singleton_singleton x y _).trans same.symm⟩⟩

/-- A genuinely constructed raised product contains a non-well-founded
argument/result graph, without a supplied presentation or section carrier. -/
theorem productUp_quine_singleton :
    productUp {HSet.quineAtom.{u}} (fun _ => {HSet.quineAtom}) =
      {{HSet.kpair HSet.quineAtom.{u + 1} HSet.quineAtom}} := by
  rw [productUp_singleton_singleton, HSet.lift_kpair, HSet.lift_quineAtom]

theorem evaluate_quine_original (a : Elements ({HSet.quineAtom.{u}} : HSet.{u})) :
    (evaluate (graphMember (singletonSection HSet.quineAtom HSet.quineAtom)) a).1 =
      HSet.quineAtom.{u} := evaluate_graph_value _ a

def singletonMemberSection (X : HSet.{u}) : Section X (fun a => {a.1}) :=
  fun a => ⟨a.1, HSet.mem_singleton_self _⟩

theorem evaluate_dependent_singleton (X : HSet.{u}) (a : Elements X) :
    (evaluate (graphMember (singletonMemberSection X)) a).1 = a.1 := evaluate_graph_value _ a

/-- The family given by the domain's own member values has an empty fibre;
its actual raised product has no members. -/
theorem varying_member_family_product_empty :
    productUp ({∅, {∅}} : HSet.{u}) (fun a => a.1) = ∅ :=
  productUp_eq_empty_of_empty_fibre ⟨∅, HSet.mem_pair.mpr (Or.inl rfl)⟩ rfl

end Mettapedia.TypeTheory.MaterialSets.Hypersets.LiftedFamilyModel
