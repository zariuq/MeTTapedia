import Mettapedia.Logic.HOL.Embedding.ZFSetUniverseClosure

/-!
# Actual set-coded dependent products and sums

Dependent pairs are Kuratowski pairs. Dependent functions are total
single-valued graphs restricted to the declared fibres. Both are actual
ZFSet constructions inside the previously constructed closed universes.
Their decoding equivalences are proved from graph functionality and pair
injectivity, not supplied as universe-structure assumptions. A graph depends
only on the values on its domain (`graph_congr`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.Embedding.ZFSetDependentProducts

open ZFSetHenkinInterpretation ZFSetUniverseClosure

universe u

abbrev Elements (a : ZFSet.{u}) := {x : ZFSet.{u} // x ∈ a}

/-! ## Closure under the underlying set constructors -/

theorem _root_.Mettapedia.Logic.HOL.Embedding.ZFSetUniverseClosure.Closed.empty_mem
    {U a : ZFSet.{u}} (closed : Closed U) (ha : a ∈ U) :
    (∅ : ZFSet.{u}) ∈ U := closed.subset_mem ha (ZFSet.empty_subset a)

theorem _root_.Mettapedia.Logic.HOL.Embedding.ZFSetUniverseClosure.Closed.singleton_mem
    {U a : ZFSet.{u}} (closed : Closed U) (ha : a ∈ U) :
    ({a} : ZFSet.{u}) ∈ U := by
  apply closed.subset_mem (closed.power_mem ha)
  intro x hx
  rcases ZFSet.mem_singleton.mp hx with rfl
  exact ZFSet.mem_powerset.mpr (fun _ h => h)

private theorem empty_ne_power_empty : (∅ : ZFSet.{u}) ≠ ZFSet.powerset ∅ := by
  intro heq
  have member : (∅ : ZFSet.{u}) ∈ ZFSet.powerset ∅ :=
    ZFSet.mem_powerset.mpr (fun _ hx => hx)
  rw [← heq] at member
  exact ZFSet.mem_irrefl _ member

theorem _root_.Mettapedia.Logic.HOL.Embedding.ZFSetUniverseClosure.Closed.unorderedPair_mem
    {U a b : ZFSet.{u}}
    (closed : Closed U) (ha : a ∈ U) (hb : b ∈ U) : ({a, b} : ZFSet.{u}) ∈ U := by
  classical
  let domain : ZFSet.{u} := ZFSet.powerset (ZFSet.powerset ∅)
  let choose : ZFSet.{u} → ZFSet.{u} := fun x => if x = ∅ then a else b
  have hd : domain ∈ U := closed.power_mem (closed.power_mem (closed.empty_mem ha))
  have hr : replacement domain choose ∈ U := closed.replacement_mem hd choose
    (fun x _ => by dsimp [choose]; split <;> assumption)
  have pairEq : replacement domain choose = ({a, b} : ZFSet.{u}) := by
    apply ZFSet.ext
    intro z
    rw [mem_replacement, ZFSet.mem_pair]
    constructor
    · rintro ⟨x, _, rfl⟩
      dsimp [choose]
      split <;> simp
    · rintro (rfl | rfl)
      · exact ⟨∅, ZFSet.mem_powerset.mpr (ZFSet.empty_subset _), by simp [choose]⟩
      · exact ⟨ZFSet.powerset ∅, ZFSet.mem_powerset.mpr (fun _ hx => hx),
          by simp [choose, Ne.symm empty_ne_power_empty]⟩
  exact pairEq ▸ hr

theorem _root_.Mettapedia.Logic.HOL.Embedding.ZFSetUniverseClosure.Closed.pair_mem
    {U a b : ZFSet.{u}}
    (closed : Closed U) (ha : a ∈ U) (hb : b ∈ U) : ZFSet.pair a b ∈ U :=
  closed.unorderedPair_mem (closed.singleton_mem ha) (closed.unorderedPair_mem ha hb)

theorem _root_.Mettapedia.Logic.HOL.Embedding.ZFSetUniverseClosure.Closed.binaryUnion_mem
    {U a b : ZFSet.{u}}
    (closed : Closed U) (ha : a ∈ U) (hb : b ∈ U) : a ∪ b ∈ U :=
  closed.union_mem (closed.unorderedPair_mem ha hb)

theorem _root_.Mettapedia.Logic.HOL.Embedding.ZFSetUniverseClosure.Closed.product_mem
    {U a b : ZFSet.{u}}
    (closed : Closed U) (ha : a ∈ U) (hb : b ∈ U) : ZFSet.prod a b ∈ U := by
  unfold ZFSet.prod ZFSet.pairSep
  exact closed.separation_mem (closed.power_mem (closed.power_mem
    (closed.binaryUnion_mem ha hb))) _

theorem _root_.Mettapedia.Logic.HOL.Embedding.ZFSetUniverseClosure.Closed.functions_mem
    {U a b : ZFSet.{u}}
    (closed : Closed U) (ha : a ∈ U) (hb : b ∈ U) : ZFSet.funs a b ∈ U :=
  closed.separation_mem (closed.power_mem (closed.product_mem ha hb)) _

/-! ## Actual dependent set codes -/

noncomputable def familyUnion (a : ZFSet.{u}) (b : ZFSet.{u} → ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sUnion (replacement a b)

theorem mem_familyUnion {a y : ZFSet.{u}} {b : ZFSet.{u} → ZFSet.{u}} :
    y ∈ familyUnion a b ↔ ∃ x ∈ a, y ∈ b x := by
  rw [familyUnion, ZFSet.mem_sUnion]
  constructor
  · rintro ⟨z, hz, hy⟩
    obtain ⟨x, hx, rfl⟩ := mem_replacement.mp hz
    exact ⟨x, hx, hy⟩
  · rintro ⟨x, hx, hy⟩
    exact ⟨b x, mem_replacement.mpr ⟨x, hx, rfl⟩, hy⟩

noncomputable def sigmaSet (a : ZFSet.{u}) (b : ZFSet.{u} → ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.pairSep (fun x y => y ∈ b x) a (familyUnion a b)

theorem mem_sigmaSet {a z : ZFSet.{u}} {b : ZFSet.{u} → ZFSet.{u}} :
    z ∈ sigmaSet a b ↔ ∃ x ∈ a, ∃ y ∈ b x, z = ZFSet.pair x y := by
  rw [sigmaSet, ZFSet.mem_pairSep]
  constructor
  · rintro ⟨x, hx, y, _, heq, hy⟩
    exact ⟨x, hx, y, hy, heq⟩
  · rintro ⟨x, hx, y, hy, heq⟩
    exact ⟨x, hx, y, mem_familyUnion.mpr ⟨x, hx, hy⟩, heq, hy⟩

noncomputable def piSet (a : ZFSet.{u}) (b : ZFSet.{u} → ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun graph => ∀ x ∈ a, ∀ y, ZFSet.pair x y ∈ graph → y ∈ b x)
    (ZFSet.funs a (familyUnion a b))

theorem mem_piSet {a graph : ZFSet.{u}} {b : ZFSet.{u} → ZFSet.{u}} :
    graph ∈ piSet a b ↔
      ZFSet.IsFunc a (familyUnion a b) graph ∧
        ∀ x ∈ a, ∀ y, ZFSet.pair x y ∈ graph → y ∈ b x := by
  rw [piSet, ZFSet.mem_sep, ZFSet.mem_funs]

theorem _root_.Mettapedia.Logic.HOL.Embedding.ZFSetUniverseClosure.Closed.familyUnion_mem
    {U a : ZFSet.{u}} (closed : Closed U)
    (ha : a ∈ U) (b : ZFSet.{u} → ZFSet.{u}) (hb : ∀ x ∈ a, b x ∈ U) :
    familyUnion a b ∈ U :=
  closed.union_mem (closed.replacement_mem ha b hb)

theorem _root_.Mettapedia.Logic.HOL.Embedding.ZFSetUniverseClosure.Closed.sigmaSet_mem
    {U a : ZFSet.{u}} (closed : Closed U)
    (ha : a ∈ U) (b : ZFSet.{u} → ZFSet.{u}) (hb : ∀ x ∈ a, b x ∈ U) :
    sigmaSet a b ∈ U := by
  unfold sigmaSet ZFSet.pairSep
  exact closed.separation_mem (closed.power_mem (closed.power_mem
    (closed.binaryUnion_mem ha (closed.familyUnion_mem ha b hb)))) _

theorem _root_.Mettapedia.Logic.HOL.Embedding.ZFSetUniverseClosure.Closed.piSet_mem
    {U a : ZFSet.{u}} (closed : Closed U)
    (ha : a ∈ U) (b : ZFSet.{u} → ZFSet.{u}) (hb : ∀ x ∈ a, b x ∈ U) :
    piSet a b ∈ U :=
  closed.separation_mem (closed.functions_mem ha (closed.familyUnion_mem ha b hb)) _

/-! ## Graphs and their unique values -/

noncomputable def graph (a : ZFSet.{u}) (f : ZFSet.{u} → ZFSet.{u}) : ZFSet.{u} :=
  replacement a (fun x => ZFSet.pair x (f x))

theorem mem_graph {a z : ZFSet.{u}} {f : ZFSet.{u} → ZFSet.{u}} :
    z ∈ graph a f ↔ ∃ x ∈ a, ZFSet.pair x (f x) = z := mem_replacement

theorem pair_mem_graph {a x y : ZFSet.{u}} {f : ZFSet.{u} → ZFSet.{u}} :
    ZFSet.pair x y ∈ graph a f ↔ x ∈ a ∧ f x = y := by
  rw [mem_graph]
  constructor
  · rintro ⟨z, hz, heq⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.mp heq
    exact ⟨hz, rfl⟩
  · rintro ⟨hx, rfl⟩
    exact ⟨x, hx, rfl⟩

theorem graph_functional {a c : ZFSet.{u}} {f : ZFSet.{u} → ZFSet.{u}}
    (hf : ∀ x ∈ a, f x ∈ c) : ZFSet.IsFunc a c (graph a f) := by
  constructor
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := mem_graph.mp hz
    exact ZFSet.pair_mem_prod.mpr ⟨hx, hf x hx⟩
  · intro x hx
    refine ⟨f x, pair_mem_graph.mpr ⟨hx, rfl⟩, ?_⟩
    intro y hy
    exact (pair_mem_graph.mp hy).2.symm

theorem graph_mem_piSet {a : ZFSet.{u}} {b f : ZFSet.{u} → ZFSet.{u}}
    (hf : ∀ x ∈ a, f x ∈ b x) : graph a f ∈ piSet a b := by
  apply mem_piSet.mpr
  refine ⟨graph_functional (fun x hx => mem_familyUnion.mpr ⟨x, hx, hf x hx⟩), ?_⟩
  intro x hx y hy
  obtain ⟨_, rfl⟩ := pair_mem_graph.mp hy
  exact hf x hx

/-- Two maps that agree on a set have the same graph. -/
theorem graph_congr {a : ZFSet.{u}} {f g : ZFSet.{u} → ZFSet.{u}}
    (h : ∀ x, x ∈ a → f x = g x) : graph a f = graph a g := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨x, hx, rfl⟩ := mem_graph.mp hz
    exact mem_graph.mpr ⟨x, hx, by rw [h x hx]⟩
  · intro hz
    obtain ⟨x, hx, rfl⟩ := mem_graph.mp hz
    exact mem_graph.mpr ⟨x, hx, by rw [← h x hx]⟩

/-! ## Decoding sums and products, with actual inverse laws -/

noncomputable def encodePair {a : ZFSet.{u}} {b : ZFSet.{u} → ZFSet.{u}}
    (point : Σ x : Elements a, Elements (b x.1)) : Elements (sigmaSet a b) :=
  ⟨ZFSet.pair point.1.1 point.2.1,
    mem_sigmaSet.mpr ⟨point.1.1, point.1.2, point.2.1, point.2.2, rfl⟩⟩

theorem encodePair_bijective (a : ZFSet.{u}) (b : ZFSet.{u} → ZFSet.{u}) :
    Function.Bijective (encodePair (a := a) (b := b)) := by
  constructor
  · rintro ⟨x, y⟩ ⟨x', y'⟩ equal
    obtain ⟨hx, hy⟩ := ZFSet.pair_inj.mp (congrArg Subtype.val equal)
    have hx' : x = x' := Subtype.ext hx
    subst x'
    have hy' : y = y' := Subtype.ext hy
    subst y'
    rfl
  · intro point
    obtain ⟨x, hx, y, hy, equal⟩ := mem_sigmaSet.mp point.2
    refine ⟨⟨⟨x, hx⟩, ⟨y, hy⟩⟩, ?_⟩
    apply Subtype.ext
    exact equal.symm

noncomputable def sigmaEquiv (a : ZFSet.{u}) (b : ZFSet.{u} → ZFSet.{u}) :
    Elements (sigmaSet a b) ≃ (Σ x : Elements a, Elements (b x.1)) :=
  (Equiv.ofBijective encodePair (encodePair_bijective a b)).symm

/-- Only values on the declared domain enter the graph; the outside value
does not become an assumed member of any fibre. -/
noncomputable def extendFunction {a : ZFSet.{u}} {b : ZFSet.{u} → ZFSet.{u}}
    (f : (x : Elements a) → Elements (b x.1)) (x : ZFSet.{u}) : ZFSet.{u} := by
  classical
  exact if hx : x ∈ a then (f ⟨x, hx⟩).1 else ∅

theorem extendFunction_at {a : ZFSet.{u}} {b : ZFSet.{u} → ZFSet.{u}}
    (f : (x : Elements a) → Elements (b x.1)) (x : Elements a) :
    extendFunction f x.1 = (f x).1 := by
  simp only [extendFunction, dif_pos x.2]

noncomputable def encodeFunction {a : ZFSet.{u}} {b : ZFSet.{u} → ZFSet.{u}}
    (f : (x : Elements a) → Elements (b x.1)) : Elements (piSet a b) :=
  ⟨graph a (extendFunction f), graph_mem_piSet (fun x hx => by
    rw [extendFunction_at f ⟨x, hx⟩]
    exact (f ⟨x, hx⟩).2)⟩

noncomputable def graphValue {a : ZFSet.{u}} {b : ZFSet.{u} → ZFSet.{u}}
    (f : Elements (piSet a b)) (x : Elements a) : Elements (b x.1) :=
  ⟨Classical.choose ((mem_piSet.mp f.2).1.2 x.1 x.2),
    (mem_piSet.mp f.2).2 x.1 x.2 _
      (Classical.choose_spec ((mem_piSet.mp f.2).1.2 x.1 x.2)).1⟩

theorem graphValue_pair_mem {a : ZFSet.{u}} {b : ZFSet.{u} → ZFSet.{u}}
    (f : Elements (piSet a b)) (x : Elements a) :
    ZFSet.pair x.1 (graphValue f x).1 ∈ f.1 :=
  (Classical.choose_spec ((mem_piSet.mp f.2).1.2 x.1 x.2)).1

theorem graphValue_unique {a : ZFSet.{u}} {b : ZFSet.{u} → ZFSet.{u}}
    (f : Elements (piSet a b)) (x : Elements a) (y : ZFSet.{u})
    (hy : ZFSet.pair x.1 y ∈ f.1) : y = (graphValue f x).1 :=
  (Classical.choose_spec ((mem_piSet.mp f.2).1.2 x.1 x.2)).2 y hy

theorem encode_decode_function {a : ZFSet.{u}} {b : ZFSet.{u} → ZFSet.{u}}
    (f : Elements (piSet a b)) : encodeFunction (graphValue f) = f := by
  apply Subtype.ext
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨x, hx, equal⟩ := mem_graph.mp hz
    rw [← equal, extendFunction_at (graphValue f) ⟨x, hx⟩]
    exact graphValue_pair_mem f ⟨x, hx⟩
  · intro hz
    obtain ⟨x, hx, y, _, equal⟩ := ZFSet.mem_prod.mp ((mem_piSet.mp f.2).1.1 hz)
    rw [equal]
    apply pair_mem_graph.mpr
    refine ⟨hx, ?_⟩
    rw [extendFunction_at (graphValue f) ⟨x, hx⟩]
    exact (graphValue_unique f ⟨x, hx⟩ y (equal ▸ hz)).symm

theorem decode_encode_function {a : ZFSet.{u}} {b : ZFSet.{u} → ZFSet.{u}}
    (f : (x : Elements a) → Elements (b x.1)) : graphValue (encodeFunction f) = f := by
  funext x
  apply Subtype.ext
  apply (graphValue_unique (encodeFunction f) x (f x).1 _).symm
  exact pair_mem_graph.mpr ⟨x.2, extendFunction_at f x⟩

noncomputable def piEquiv (a : ZFSet.{u}) (b : ZFSet.{u} → ZFSet.{u}) :
    Elements (piSet a b) ≃ ((x : Elements a) → Elements (b x.1)) where
  toFun := graphValue
  invFun := encodeFunction
  left_inv := encode_decode_function
  right_inv := decode_encode_function

/-! ## Bounded dependence and reindexing -/

/-- Codes depend only on fibres over the declared domain. -/
theorem familyUnion_congr {a : ZFSet.{u}} {b c : ZFSet.{u} → ZFSet.{u}}
    (equal : ∀ x ∈ a, b x = c x) : familyUnion a b = familyUnion a c := by
  apply ZFSet.ext
  intro y
  simp only [mem_familyUnion]
  constructor <;> rintro ⟨x, hx, hy⟩
  · exact ⟨x, hx, (equal x hx) ▸ hy⟩
  · exact ⟨x, hx, (equal x hx).symm ▸ hy⟩

theorem sigmaSet_congr {a : ZFSet.{u}} {b c : ZFSet.{u} → ZFSet.{u}}
    (equal : ∀ x ∈ a, b x = c x) : sigmaSet a b = sigmaSet a c := by
  apply ZFSet.ext
  intro z
  simp only [mem_sigmaSet]
  constructor <;> rintro ⟨x, hx, y, hy, heq⟩
  · exact ⟨x, hx, y, (equal x hx) ▸ hy, heq⟩
  · exact ⟨x, hx, y, (equal x hx).symm ▸ hy, heq⟩

theorem piSet_congr {a : ZFSet.{u}} {b c : ZFSet.{u} → ZFSet.{u}}
    (equal : ∀ x ∈ a, b x = c x) : piSet a b = piSet a c := by
  apply ZFSet.ext
  intro f
  simp only [mem_piSet, familyUnion_congr equal]
  constructor <;> rintro ⟨functional, fibres⟩
  · exact ⟨functional, fun x hx y hy => (equal x hx) ▸ fibres x hx y hy⟩
  · exact ⟨functional, fun x hx y hy => (equal x hx).symm ▸ fibres x hx y hy⟩

theorem piSet_context_substitution {Γ Δ : Type*} (θ : Δ → Γ)
    (a : Γ → ZFSet.{u}) (b : Γ → ZFSet.{u} → ZFSet.{u}) :
    (fun γ => piSet (a γ) (b γ)) ∘ θ =
      (fun δ => piSet ((a ∘ θ) δ) (b (θ δ))) := rfl

theorem sigmaSet_context_substitution {Γ Δ : Type*} (θ : Δ → Γ)
    (a : Γ → ZFSet.{u}) (b : Γ → ZFSet.{u} → ZFSet.{u}) :
    (fun γ => sigmaSet (a γ) (b γ)) ∘ θ =
      (fun δ => sigmaSet ((a ∘ θ) δ) (b (θ δ))) := rfl

/-! ## Empty-fibre and genuinely varying-family controls -/

theorem piSet_empty_of_empty_fibre {a : ZFSet.{u}} {b : ZFSet.{u} → ZFSet.{u}}
    (x : Elements a) (emptyFibre : b x.1 = ∅) : piSet a b = ∅ := by
  apply ZFSet.ext
  intro f
  constructor
  · intro hf
    obtain ⟨y, impossible⟩ := graphValue ⟨f, hf⟩ x
    rw [emptyFibre] at impossible
    exact False.elim (ZFSet.notMem_empty _ impossible)
  · intro hf
    exact False.elim (ZFSet.notMem_empty _ hf)

namespace Controls

def two : ZFSet.{u} := ZFSet.powerset (ZFSet.powerset ∅)

theorem empty_mem_two : (∅ : ZFSet.{u}) ∈ two :=
  ZFSet.mem_powerset.mpr (ZFSet.empty_subset _)

theorem power_empty_mem_two : ZFSet.powerset (∅ : ZFSet.{u}) ∈ two :=
  ZFSet.mem_powerset.mpr (fun _ hx => hx)

noncomputable def varying (x : ZFSet.{u}) : ZFSet.{u} := by
  classical
  exact if x = ∅ then {∅} else two

theorem varying_at_empty : varying (∅ : ZFSet.{u}) = {∅} := by simp [varying]

theorem varying_at_power_empty : varying (ZFSet.powerset (∅ : ZFSet.{u})) = two := by
  simp [varying, Ne.symm empty_ne_power_empty]

theorem varying_fibres_distinct :
    varying (∅ : ZFSet.{u}) ≠ varying (ZFSet.powerset ∅) := by
  rw [varying_at_empty, varying_at_power_empty]
  intro equal
  have member := power_empty_mem_two.{u}
  rw [← equal, ZFSet.mem_singleton] at member
  exact empty_ne_power_empty member.symm

theorem empty_mem_every_varying_fibre (x : ZFSet.{u}) : (∅ : ZFSet.{u}) ∈ varying x := by
  classical
  unfold varying
  split
  · exact ZFSet.mem_singleton.mpr rfl
  · exact empty_mem_two

/-- A graph inhabits this genuinely nonconstant dependent product. -/
noncomputable def varyingFunction : Elements (piSet two.{u} varying) :=
  ⟨graph two (fun _ => ∅), graph_mem_piSet
    (fun x _ => empty_mem_every_varying_fibre x)⟩

noncomputable def missingFibre (x : ZFSet.{u}) : ZFSet.{u} := by
  classical
  exact if x = ∅ then ∅ else {∅}

theorem missing_product_empty : piSet two.{u} missingFibre = ∅ :=
  piSet_empty_of_empty_fibre ⟨∅, empty_mem_two⟩ (by simp [missingFibre])

/-- One empty fibre kills the product but not the dependent sum. -/
theorem missing_sum_inhabited : Nonempty (Elements (sigmaSet two.{u} missingFibre)) := by
  refine ⟨⟨ZFSet.pair (ZFSet.powerset ∅) ∅, mem_sigmaSet.mpr
    ⟨ZFSet.powerset ∅, power_empty_mem_two, ∅, ?_, rfl⟩⟩⟩
  simp [missingFibre, Ne.symm empty_ne_power_empty]

end Controls

#print axioms Closed.unorderedPair_mem
#print axioms Closed.piSet_mem
#print axioms Closed.sigmaSet_mem
#print axioms graph_functional
#print axioms encodePair_bijective
#print axioms sigmaEquiv
#print axioms graphValue_unique
#print axioms encode_decode_function
#print axioms decode_encode_function
#print axioms piEquiv
#print axioms piSet_congr
#print axioms sigmaSet_congr
#print axioms Controls.varying_fibres_distinct
#print axioms Controls.varyingFunction
#print axioms Controls.missing_product_empty
#print axioms Controls.missing_sum_inhabited

end Mettapedia.Logic.HOL.Embedding.ZFSetDependentProducts
