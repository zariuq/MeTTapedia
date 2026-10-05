import Mettapedia.TypeTheory.MaterialSets.Hypersets.DependentProduct

/-!
# Original-bound dependent products below a material codomain bound

For an arbitrary family of bare hypersets, a proved common bound on its
members suffices to construct its dependent-pair set and every function graph
by separation. Kuratowski pairs lie in the double powerset of the union of the
domain and codomain bounds. A further powerset, separated by totality and
single-valuedness, collects all actual dependent functions at the original
graph universe.

Evaluation separates a singleton row inside the original fibre and takes its
union. Existence is eliminated only into membership propositions; no graph
representative, presentation of all hypersets, or selected small section
carrier is an input. The construction uses the full proposition-valued
separation and powerset operations of `HSet`; it does not establish an
unrestricted original-bound Collection schema for unbounded bare families.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.BoundedDependentProducts

universe u

open HSet

abbrev Element (X : HSet.{u}) := El (· ∈ ·) X

abbrev Section (X : HSet.{u}) (B : Element X → HSet.{u}) :=
  ∀ a, Element (B a)

/-- The actual union of two material bounds. -/
def combinedBound (X Y : HSet.{u}) : HSet.{u} := sUnion {X, Y}

theorem mem_combinedBound {X Y z : HSet.{u}} :
    z ∈ combinedBound X Y ↔ z ∈ X ∨ z ∈ Y := by
  rw [combinedBound, mem_sUnion]
  constructor
  · rintro ⟨W, member, belongs⟩
    rcases mem_pair.mp member with rfl | rfl
    · exact Or.inl belongs
    · exact Or.inr belongs
  · rintro (belongs | belongs)
    · exact ⟨X, mem_pair.mpr (Or.inl rfl), belongs⟩
    · exact ⟨Y, mem_pair.mpr (Or.inr rfl), belongs⟩

/-- Ordered pairs are bounded without replacement or choosing graphs. -/
theorem kpair_mem_double_power {X Y x y : HSet.{u}} (hx : x ∈ X) (hy : y ∈ Y) :
    kpair x y ∈ powerset (powerset (combinedBound X Y)) := by
  apply mem_powerset.mpr
  intro W member
  apply mem_powerset.mpr
  intro z belongs
  rcases mem_kpair.mp member with rfl | rfl
  · exact mem_combinedBound.mpr (Or.inl (mem_singleton.mp belongs ▸ hx))
  · rcases mem_pair.mp belongs with rfl | rfl
    · exact mem_combinedBound.mpr (Or.inl hx)
    · exact mem_combinedBound.mpr (Or.inr hy)

/-- A constructed cartesian pair set of arbitrary bare material sets. -/
def cartesian (X Y : HSet.{u}) : HSet.{u} :=
  HSet.sep (fun z => ∃ x ∈ X, ∃ y ∈ Y, kpair x y = z)
    (powerset (powerset (combinedBound X Y)))

theorem mem_cartesian_iff {X Y z : HSet.{u}} :
    z ∈ cartesian X Y ↔ ∃ x ∈ X, ∃ y ∈ Y, kpair x y = z := by
  refine mem_sep.trans ⟨And.right, ?_⟩
  rintro ⟨x, hx, y, hy, same⟩
  exact ⟨same ▸ kpair_mem_double_power hx hy, x, hx, y, hy, same⟩

/-- The dependent pairs separated from the independently constructed
cartesian bound. A bound proof is required for its complete membership law. -/
def pairSet (X : HSet.{u}) (B : Element X → HSet.{u}) (Y : HSet.{u}) : HSet.{u} :=
  HSet.sep (fun z => ∃ (a : Element X) (b : Element (B a)), kpair a.1 b.1 = z)
    (cartesian X Y)

theorem mem_pairSet_iff {X Y z : HSet.{u}} {B : Element X → HSet.{u}}
    (bounded : ∀ a, B a ⊆ Y) :
    z ∈ pairSet X B Y ↔ ∃ (a : Element X) (b : Element (B a)), kpair a.1 b.1 = z := by
  refine mem_sep.trans ⟨And.right, ?_⟩
  rintro ⟨a, b, same⟩
  exact ⟨mem_cartesian_iff.mpr ⟨a.1, a.2, b.1, bounded a b.2, same⟩, a, b, same⟩

/-- Recover the original domain member with a derived Kuratowski projection. -/
def pairFirst {X Y : HSet.{u}} {B : Element X → HSet.{u}}
    (bounded : ∀ a, B a ⊆ Y) (pair : Element (pairSet X B Y)) : Element X :=
  ⟨fst pair.1, by
    obtain ⟨a, b, same⟩ := (mem_pairSet_iff bounded).mp pair.2
    rw [← same, fst_kpair]
    exact a.2⟩

/-- Recover the original fibre member, including its dependent index. -/
def pairSecond {X Y : HSet.{u}} {B : Element X → HSet.{u}}
    (bounded : ∀ a, B a ⊆ Y) (pair : Element (pairSet X B Y)) :
    Element (B (pairFirst bounded pair)) :=
  ⟨snd pair.1, by
    obtain ⟨a, b, same⟩ := (mem_pairSet_iff bounded).mp pair.2
    have index : pairFirst bounded pair = a := by
      apply El.ext propositional
      change fst pair.1 = a.1
      rw [← same, fst_kpair]
    rw [index, ← same, snd_kpair]
    exact b.2⟩

/-- The pair-set encoder needs only the proved material bound. -/
def pairMember {X Y : HSet.{u}} {B : Element X → HSet.{u}}
    (bounded : ∀ a, B a ⊆ Y) (a : Element X) (b : Element (B a)) :
    Element (pairSet X B Y) :=
  ⟨kpair a.1 b.1, mem_pairSet_iff bounded |>.mpr ⟨a, b, rfl⟩⟩

theorem pairFirst_pairMember {X Y : HSet.{u}} {B : Element X → HSet.{u}}
    (bounded : ∀ a, B a ⊆ Y) (a : Element X) (b : Element (B a)) :
    pairFirst bounded (pairMember bounded a b) = a :=
  El.ext propositional (fst_kpair _ _)

theorem pairSecond_pairMember_value {X Y : HSet.{u}} {B : Element X → HSet.{u}}
    (bounded : ∀ a, B a ⊆ Y) (a : Element X) (b : Element (B a)) :
    (pairSecond bounded (pairMember bounded a b)).1 = b.1 := snd_kpair _ _

theorem pairMember_pairFirst_pairSecond {X Y : HSet.{u}} {B : Element X → HSet.{u}}
    (bounded : ∀ a, B a ⊆ Y) (pair : Element (pairSet X B Y)) :
    pairMember bounded (pairFirst bounded pair) (pairSecond bounded pair) = pair := by
  apply El.ext propositional
  obtain ⟨a, b, same⟩ := (mem_pairSet_iff bounded).mp pair.2
  change kpair (fst pair.1) (snd pair.1) = pair.1
  rw [← same, fst_kpair, snd_kpair]

/-- The constructed material sum has actual dependent coordinates; no
existential pair representative is selected in either inverse. -/
def pairEquiv {X Y : HSet.{u}} {B : Element X → HSet.{u}}
    (bounded : ∀ a, B a ⊆ Y) :
    Element (pairSet X B Y) ≃ (Σ' a : Element X, Element (B a)) where
  toFun pair := ⟨pairFirst bounded pair, pairSecond bounded pair⟩
  invFun pair := pairMember bounded pair.1 pair.2
  left_inv := pairMember_pairFirst_pairSecond bounded
  right_inv _pair := psigma_el_ext propositional (fst_kpair _ _) (snd_kpair _ _)

/-- The graph of a supplied actual section, constructed by separation. -/
def graph {X : HSet.{u}} {B : Element X → HSet.{u}} (Y : HSet.{u})
    (s : Section X B) : HSet.{u} :=
  HSet.sep (fun z => ∃ a : Element X, kpair a.1 (s a).1 = z) (pairSet X B Y)

theorem mem_graph_iff {X Y z : HSet.{u}} {B : Element X → HSet.{u}}
    (bounded : ∀ a, B a ⊆ Y) (s : Section X B) :
    z ∈ graph Y s ↔ ∃ a : Element X, kpair a.1 (s a).1 = z := by
  refine mem_sep.trans ⟨And.right, ?_⟩
  rintro ⟨a, same⟩
  exact ⟨mem_pairSet_iff bounded |>.mpr ⟨a, s a, same⟩, a, same⟩

theorem graph_entry {X Y : HSet.{u}} {B : Element X → HSet.{u}}
    (bounded : ∀ a, B a ⊆ Y) (s : Section X B) (a : Element X) :
    kpair a.1 (s a).1 ∈ graph Y s := mem_graph_iff bounded s |>.mpr ⟨a, rfl⟩

theorem graph_isFunctionGraph {X Y : HSet.{u}} {B : Element X → HSet.{u}}
    (bounded : ∀ a, B a ⊆ Y) (s : Section X B) :
    IsFunctionGraph kuratowski X B (graph Y s) := by
  intro a
  refine ⟨s a, ⟨graph_entry bounded s a⟩, ?_⟩
  rintro z ⟨member⟩ first
  obtain ⟨a', rfl⟩ := (mem_graph_iff bounded s).mp member
  change fst (kpair a'.1 (s a').1) = a.1 at first
  rw [fst_kpair] at first
  obtain rfl : a' = a := El.ext propositional first
  exact snd_kpair _ _

/-- All bounded total single-valued graphs, collected by a full powerset. -/
def product (X : HSet.{u}) (B : Element X → HSet.{u}) (Y : HSet.{u}) : HSet.{u} :=
  HSet.sep (IsFunctionGraph kuratowski X B) (powerset (pairSet X B Y))

theorem mem_product_iff {X Y G : HSet.{u}} {B : Element X → HSet.{u}} :
    G ∈ product X B Y ↔ G ⊆ pairSet X B Y ∧ IsFunctionGraph kuratowski X B G := by
  rw [product, mem_sep, mem_powerset]

/-- Encode the complete section with its material graph membership proof. -/
def graphMember {X Y : HSet.{u}} {B : Element X → HSet.{u}}
    (bounded : ∀ a, B a ⊆ Y) (s : Section X B) : Element (product X B Y) :=
  ⟨graph Y s, mem_product_iff.mpr
    ⟨fun _ member => (mem_sep.mp member).1, graph_isFunctionGraph bounded s⟩⟩

/-- A row is computed within the original fibre, rather than by replacement. -/
def row {X : HSet.{u}} (B : Element X → HSet.{u}) (G : HSet.{u})
    (a : Element X) : HSet.{u} := HSet.sep (fun b => kpair a.1 b ∈ G) (B a)

theorem row_eq_singleton {X G : HSet.{u}} {B : Element X → HSet.{u}}
    (a : Element X) (b : Element (B a)) (entry : kpair a.1 b.1 ∈ G)
    (unique : ∀ z, Nonempty (z ∈ G) → fst z = a.1 → snd z = b.1) :
    row B G a = {b.1} := by
  apply ext
  intro value
  rw [row, mem_sep, mem_singleton]
  constructor
  · intro member
    exact (snd_kpair a.1 value).symm.trans
      (unique (kpair a.1 value) ⟨member.2⟩ (fst_kpair _ _))
  · intro same
    exact same ▸ ⟨b.2, entry⟩

theorem row_value_eq {X G : HSet.{u}} {B : Element X → HSet.{u}}
    (a : Element X) (b : Element (B a)) (entry : kpair a.1 b.1 ∈ G)
    (unique : ∀ z, Nonempty (z ∈ G) → fst z = a.1 → snd z = b.1) :
    sUnion (row B G a) = b.1 := by
  rw [row_eq_singleton a b entry unique, sUnion_singleton]

theorem row_value_mem {X Y : HSet.{u}} {B : Element X → HSet.{u}}
    (g : Element (product X B Y)) (a : Element X) : sUnion (row B g.1 a) ∈ B a := by
  obtain ⟨b, entry, unique⟩ := (mem_product_iff.mp g.2).2 a
  rw [row_value_eq a b (entry.elim id) unique]
  exact b.2

/-- Decode by bounded row separation and singleton union. No witness is
selected from totality, and the result retains its fibre membership. -/
def evaluate {X Y : HSet.{u}} {B : Element X → HSet.{u}}
    (g : Element (product X B Y)) : Section X B :=
  fun a => ⟨sUnion (row B g.1 a), recovery.recover ⟨row_value_mem g a⟩⟩

theorem evaluate_value_of_entry {X Y : HSet.{u}} {B : Element X → HSet.{u}}
    (g : Element (product X B Y)) (a : Element X) (b : Element (B a))
    (entry : kpair a.1 b.1 ∈ g.1) : (evaluate g a).1 = b.1 := by
  obtain ⟨b₀, entry₀, unique⟩ := (mem_product_iff.mp g.2).2 a
  exact (row_value_eq a b₀ (entry₀.elim id) unique).trans
    ((snd_kpair a.1 b.1).symm.trans
      (unique (kpair a.1 b.1) ⟨entry⟩ (fst_kpair _ _))).symm

theorem evaluate_entry {X Y : HSet.{u}} {B : Element X → HSet.{u}}
    (g : Element (product X B Y)) (a : Element X) :
    kpair a.1 (evaluate g a).1 ∈ g.1 := by
  obtain ⟨b, entry, unique⟩ := (mem_product_iff.mp g.2).2 a
  change kpair a.1 (sUnion (row B g.1 a)) ∈ g.1
  rw [row_value_eq a b (entry.elim id) unique]
  exact entry.elim id

theorem product_entry_iff {X Y : HSet.{u}} {B : Element X → HSet.{u}}
    (g : Element (product X B Y)) (a : Element X) (b : Element (B a)) :
    kpair a.1 b.1 ∈ g.1 ↔ evaluate g a = b :=
  ⟨fun entry => El.ext propositional (evaluate_value_of_entry g a b entry),
    fun same => same ▸ evaluate_entry g a⟩

theorem evaluate_beta {X Y : HSet.{u}} {B : Element X → HSet.{u}}
    (bounded : ∀ a, B a ⊆ Y) (s : Section X B) (a : Element X) :
    evaluate (graphMember bounded s) a = s a :=
  El.ext propositional (evaluate_value_of_entry _ a (s a) (graph_entry bounded s a))

/-- The whole graph is recovered, including all entries admitted by the
powerset bound. Totality alone would not exclude extraneous entries. -/
theorem graph_evaluate {X Y : HSet.{u}} {B : Element X → HSet.{u}}
    (bounded : ∀ a, B a ⊆ Y) (g : Element (product X B Y)) :
    graph Y (evaluate g) = g.1 := by
  apply ext
  intro z
  rw [mem_graph_iff bounded]
  constructor
  · rintro ⟨a, same⟩
    exact same ▸ evaluate_entry g a
  · intro member
    obtain ⟨a, b, same⟩ := (mem_pairSet_iff bounded).mp
      ((mem_product_iff.mp g.2).1 member)
    have entry : kpair a.1 b.1 ∈ g.1 := same.symm ▸ member
    exact ⟨a, (congrArg (kpair a.1) (evaluate_value_of_entry g a b entry)).trans same⟩

/-- Actual product members and complete dependent functions, with both
inverse laws constructed from material operations. -/
def productEquiv {X Y : HSet.{u}} {B : Element X → HSet.{u}}
    (bounded : ∀ a, B a ⊆ Y) : Element (product X B Y) ≃ Section X B where
  toFun := evaluate
  invFun := graphMember bounded
  left_inv g := El.ext propositional (graph_evaluate bounded g)
  right_inv s := funext (evaluate_beta bounded s)

theorem graph_injective {X Y : HSet.{u}} {B : Element X → HSet.{u}}
    (bounded : ∀ a, B a ⊆ Y) : Function.Injective (graph Y : Section X B → HSet.{u}) := by
  intro s t same
  have members : graphMember bounded s = graphMember bounded t := El.ext propositional same
  have sections := congrArg evaluate members
  exact (funext (evaluate_beta bounded s)).symm.trans
    (sections.trans (funext (evaluate_beta bounded t)))

theorem mem_product_iff_section {X Y G : HSet.{u}} {B : Element X → HSet.{u}}
    (bounded : ∀ a, B a ⊆ Y) :
    G ∈ product X B Y ↔ ∃ s : Section X B, graph Y s = G :=
  ⟨fun member => ⟨evaluate ⟨G, member⟩, graph_evaluate bounded _⟩,
    fun ⟨s, same⟩ => same ▸ (graphMember bounded s).2⟩

theorem product_inhabited_iff {X Y : HSet.{u}} {B : Element X → HSet.{u}}
    (bounded : ∀ a, B a ⊆ Y) :
    Nonempty (Element (product X B Y)) ↔ Nonempty (Section X B) :=
  ⟨fun ⟨g⟩ => ⟨productEquiv bounded g⟩,
    fun ⟨s⟩ => ⟨(productEquiv bounded).symm s⟩⟩

/-- A set collecting the fibres gives a common member bound by actual union.
This constructs the bound; it does not postulate replacement for the family. -/
theorem codomainBound_of_fibreCollection {X : HSet.{u}} {B : Element X → HSet.{u}}
    (collection : HSet.{u}) (collects : ∀ a, B a ∈ collection) :
    ∀ a, B a ⊆ sUnion collection :=
  fun a _ member => mem_sUnion.mpr ⟨B a, collects a, member⟩

/-- The product bound is independently constructed from the actual codomain
bound, not supplied as an assumed set of all section graphs. -/
theorem product_subset_triple_power {X Y : HSet.{u}} {B : Element X → HSet.{u}} :
    product X B Y ⊆ powerset (powerset (powerset (combinedBound X Y))) := by
  intro G member
  apply mem_powerset.mpr
  intro z entry
  have pairMember := (mem_product_iff.mp member).1 entry
  exact (mem_sep.mp (mem_sep.mp pairMember).1).1

/-! ## Independence of the proved bound and comparison with replacement -/

theorem pairSet_bound_independent {X Y Z : HSet.{u}} {B : Element X → HSet.{u}}
    (first : ∀ a, B a ⊆ Y) (second : ∀ a, B a ⊆ Z) :
    pairSet X B Y = pairSet X B Z :=
  ext fun _ => (mem_pairSet_iff first).trans (mem_pairSet_iff second).symm

theorem graph_bound_independent {X Y Z : HSet.{u}} {B : Element X → HSet.{u}}
    (first : ∀ a, B a ⊆ Y) (second : ∀ a, B a ⊆ Z) (s : Section X B) :
    graph Y s = graph Z s :=
  ext fun _ => (mem_graph_iff first s).trans (mem_graph_iff second s).symm

theorem product_bound_independent {X Y Z : HSet.{u}} {B : Element X → HSet.{u}}
    (first : ∀ a, B a ⊆ Y) (second : ∀ a, B a ⊆ Z) :
    product X B Y = product X B Z := by
  rw [product, product, pairSet_bound_independent first second]

theorem pairSet_eq_sigmaSet (p : Presentation.{u}) {X Y : HSet.{u}}
    {B : Element X → HSet.{u}} (bounded : ∀ a, B a ⊆ Y) :
    pairSet X B Y = sigmaSet (dependentReplacement p) union kuratowski X B :=
  ext fun _ => (mem_pairSet_iff bounded).trans mem_sigmaSet_iff.symm

theorem graph_eq_functionGraph (p : Presentation.{u}) {X Y : HSet.{u}}
    {B : Element X → HSet.{u}} (bounded : ∀ a, B a ⊆ Y) (s : Section X B) :
    graph Y s = functionGraph (dependentReplacement p) kuratowski s :=
  ext fun _ => (mem_graph_iff bounded s).trans mem_image.symm

/-- The new original-bound construction agrees with the older replacement
construction whenever a presentation is supplied for the latter. -/
theorem product_eq_dependentProduct (p : Presentation.{u}) {X Y : HSet.{u}}
    {B : Element X → HSet.{u}} (bounded : ∀ a, B a ⊆ Y) :
    product X B Y = dependentProduct p X B := by
  apply ext
  intro G
  rw [mem_product_iff, mem_dependentProduct_iff, pairSet_eq_sigmaSet p bounded]
  rfl

end Mettapedia.TypeTheory.MaterialSets.Hypersets.BoundedDependentProducts
