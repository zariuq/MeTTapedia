import Mettapedia.Logic.HOL.Embedding.ZFSetDependentProducts

/-!
# Actual Aczel trace-coded dependent products

The trace of a graph replaces each pair `(x,y)` by all pairs `(x,z)` with
`z ∈ y`. Application collects the second coordinates at an argument. These
are uniform set operations, including on empty sets; no test for a special
proof type is used. At a fixed declared domain, the trace and ordinary graph
representations have proved inverse maps. Untyped traces can lose the domain.

The construction follows Lee and Werner, *Proof-Irrelevant Model of CC with
Predicative Induction and Judgmental Equality*, LMCS 7(4:05), 2011,
Definition 3.2, Lemma 3.3 and Remark 3.4, https://lmcs.episciences.org/920/pdf.
This is an alternative product representation, not a soundness theorem for
an entire dependent calculus or a choice of global proof identity.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.Embedding.ZFSetTraceProducts

open ZFSetHenkinInterpretation ZFSetUniverseClosure ZFSetDependentProducts

universe u

/-- A bound containing both coordinates of every Kuratowski pair in `r`. -/
def coordinates (r : ZFSet.{u}) : ZFSet.{u} := ZFSet.sUnion (ZFSet.sUnion r)

theorem pair_coordinates {r x y : ZFSet.{u}} (h : ZFSet.pair x y ∈ r) :
    x ∈ coordinates r ∧ y ∈ coordinates r := by
  have inner : ({x, y} : ZFSet.{u}) ∈ ZFSet.sUnion r :=
    ZFSet.mem_sUnion.mpr ⟨ZFSet.pair x y, h, by simp [ZFSet.pair]⟩
  constructor
  · exact ZFSet.mem_sUnion.mpr ⟨{x, y}, inner, by simp⟩
  · exact ZFSet.mem_sUnion.mpr ⟨{x, y}, inner, by simp⟩

/-- A total, untyped trace operation on actual sets. The bounds are justified
by `pair_coordinates`; they do not restrict the trace relation. -/
noncomputable def traceLam (r : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.pairSep (fun x z => ∃ y, ZFSet.pair x y ∈ r ∧ z ∈ y)
    (coordinates r) (ZFSet.sUnion (coordinates r))

noncomputable def traceApp (r x : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ZFSet.pair x z ∈ r) (coordinates r)

theorem mem_traceApp {r x z : ZFSet.{u}} :
    z ∈ traceApp r x ↔ ZFSet.pair x z ∈ r := by
  rw [traceApp, ZFSet.mem_sep]
  exact ⟨And.right, fun h => ⟨(pair_coordinates h).2, h⟩⟩

theorem mem_traceLam {r p : ZFSet.{u}} :
    p ∈ traceLam r ↔
      ∃ x y z, ZFSet.pair x y ∈ r ∧ z ∈ y ∧ p = ZFSet.pair x z := by
  rw [traceLam, ZFSet.mem_pairSep]
  constructor
  · rintro ⟨x, _, z, _, hp, y, hxy, hzy⟩
    exact ⟨x, y, z, hxy, hzy, hp⟩
  · rintro ⟨x, y, z, hxy, hzy, hp⟩
    exact ⟨x, (pair_coordinates hxy).1, z,
      ZFSet.mem_sUnion.mpr ⟨y, (pair_coordinates hxy).2, hzy⟩,
      hp, y, hxy, hzy⟩

theorem pair_mem_traceLam {r x z : ZFSet.{u}} :
    ZFSet.pair x z ∈ traceLam r ↔ ∃ y, ZFSet.pair x y ∈ r ∧ z ∈ y := by
  rw [mem_traceLam]
  constructor
  · rintro ⟨x', y, z', hxy, hzy, equal⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.mp equal
    exact ⟨y, hxy, hzy⟩
  · rintro ⟨y, hxy, hzy⟩
    exact ⟨x, y, z, hxy, hzy, rfl⟩

/-- Tracing an actual graph is precisely the dependent union of its values. -/
theorem traceLam_graph (a : ZFSet.{u}) (f : ZFSet.{u} → ZFSet.{u}) :
    traceLam (graph a f) = sigmaSet a f := by
  apply ZFSet.ext
  intro p
  rw [mem_traceLam, mem_sigmaSet]
  constructor
  · rintro ⟨x, y, z, hxy, hzy, hp⟩
    obtain ⟨hx, rfl⟩ := pair_mem_graph.mp hxy
    exact ⟨x, hx, z, hzy, hp⟩
  · rintro ⟨x, hx, z, hz, hp⟩
    exact ⟨x, f x, z, pair_mem_graph.mpr ⟨hx, rfl⟩, hz, hp⟩

theorem traceApp_graph_beta {a x : ZFSet.{u}} (f : ZFSet.{u} → ZFSet.{u})
    (hx : x ∈ a) : traceApp (traceLam (graph a f)) x = f x := by
  apply ZFSet.ext
  intro z
  rw [mem_traceApp, pair_mem_traceLam]
  constructor
  · rintro ⟨y, hy, hz⟩
    obtain ⟨_, rfl⟩ := pair_mem_graph.mp hy
    exact hz
  · exact fun hz => ⟨f x, pair_mem_graph.mpr ⟨hx, rfl⟩, hz⟩

/-- A traced graph has no result at an input outside its domain. This is the
boundary complementary to `traceApp_graph_beta`. -/
theorem traceApp_graph_outside {a x : ZFSet.{u}} (f : ZFSet.{u} → ZFSet.{u})
    (hx : x ∉ a) : traceApp (traceLam (graph a f)) x = ∅ := by
  apply ZFSet.ext
  intro z
  rw [mem_traceApp, pair_mem_traceLam]
  constructor
  · rintro ⟨y, hy, _⟩
    exact False.elim (hx (pair_mem_graph.mp hy).1)
  · intro hz
    simp at hz

theorem traceApp_graphValue {a : ZFSet.{u}} {b : ZFSet.{u} → ZFSet.{u}}
    (f : Elements (piSet a b)) (x : Elements a) :
    traceApp (traceLam f.1) x.1 = (graphValue f x).1 := by
  apply ZFSet.ext
  intro z
  rw [mem_traceApp, pair_mem_traceLam]
  constructor
  · rintro ⟨y, hy, hz⟩
    exact (graphValue_unique f x y hy) ▸ hz
  · exact fun hz => ⟨(graphValue f x).1, graphValue_pair_mem f x, hz⟩

/-- Injectivity is typed: both graphs have the same domain. Their codomain
families may differ. No untyped domain-recovery theorem is claimed. -/
theorem traceLam_injective_fixed_domain {a : ZFSet.{u}}
    {b c : ZFSet.{u} → ZFSet.{u}}
    (f : Elements (piSet a b)) (g : Elements (piSet a c))
    (equal : traceLam f.1 = traceLam g.1) : f.1 = g.1 := by
  have values : ∀ x : Elements a, (graphValue f x).1 = (graphValue g x).1 := by
    intro x
    rw [← traceApp_graphValue f x, equal, traceApp_graphValue g x]
  apply ZFSet.ext
  intro p
  constructor
  · intro hp
    obtain ⟨x, hx, y, _, heq⟩ := ZFSet.mem_prod.mp ((mem_piSet.mp f.2).1.1 hp)
    rw [heq]
    have hy := graphValue_unique f ⟨x, hx⟩ y (heq ▸ hp)
    rw [hy, values ⟨x, hx⟩]
    exact graphValue_pair_mem g ⟨x, hx⟩
  · intro hp
    obtain ⟨x, hx, y, _, heq⟩ := ZFSet.mem_prod.mp ((mem_piSet.mp g.2).1.1 hp)
    rw [heq]
    have hy := graphValue_unique g ⟨x, hx⟩ y (heq ▸ hp)
    rw [hy, ← values ⟨x, hx⟩]
    exact graphValue_pair_mem f ⟨x, hx⟩

/-! ## An actual image set, with typed inverse maps -/

noncomputable def tracePiSet (a : ZFSet.{u}) (b : ZFSet.{u} → ZFSet.{u}) : ZFSet.{u} :=
  replacement (piSet a b) traceLam

theorem mem_tracePiSet {a t : ZFSet.{u}} {b : ZFSet.{u} → ZFSet.{u}} :
    t ∈ tracePiSet a b ↔ ∃ f ∈ piSet a b, traceLam f = t := mem_replacement

noncomputable def graphToTrace {a : ZFSet.{u}} {b : ZFSet.{u} → ZFSet.{u}}
    (f : Elements (piSet a b)) : Elements (tracePiSet a b) :=
  ⟨traceLam f.1, mem_tracePiSet.mpr ⟨f.1, f.2, rfl⟩⟩

theorem traceApp_mem {a : ZFSet.{u}} {b : ZFSet.{u} → ZFSet.{u}}
    (t : Elements (tracePiSet a b)) (x : Elements a) : traceApp t.1 x.1 ∈ b x.1 := by
  obtain ⟨f, hf, equal⟩ := mem_tracePiSet.mp t.2
  rw [← equal, traceApp_graphValue ⟨f, hf⟩ x]
  exact (graphValue ⟨f, hf⟩ x).2

noncomputable def traceValue {a : ZFSet.{u}} {b : ZFSet.{u} → ZFSet.{u}}
    (t : Elements (tracePiSet a b)) (x : Elements a) : Elements (b x.1) :=
  ⟨traceApp t.1 x.1, traceApp_mem t x⟩

noncomputable def traceToGraph {a : ZFSet.{u}} {b : ZFSet.{u} → ZFSet.{u}}
    (t : Elements (tracePiSet a b)) : Elements (piSet a b) :=
  encodeFunction (a := a) (b := b) (traceValue t)

theorem traceValue_graphToTrace {a : ZFSet.{u}} {b : ZFSet.{u} → ZFSet.{u}}
    (f : Elements (piSet a b)) : traceValue (graphToTrace f) = graphValue f := by
  funext x
  exact Subtype.ext (traceApp_graphValue f x)

theorem traceToGraph_graphToTrace {a : ZFSet.{u}} {b : ZFSet.{u} → ZFSet.{u}}
    (f : Elements (piSet a b)) : traceToGraph (graphToTrace f) = f := by
  rw [traceToGraph, traceValue_graphToTrace, encode_decode_function]

theorem graphToTrace_traceToGraph {a : ZFSet.{u}} {b : ZFSet.{u} → ZFSet.{u}}
    (t : Elements (tracePiSet a b)) : graphToTrace (traceToGraph t) = t := by
  obtain ⟨f, hf, equal⟩ := mem_tracePiSet.mp t.2
  have ht : t = graphToTrace ⟨f, hf⟩ := Subtype.ext equal.symm
  rw [ht, traceToGraph_graphToTrace]

noncomputable def graphTraceEquiv (a : ZFSet.{u}) (b : ZFSet.{u} → ZFSet.{u}) :
    Elements (piSet a b) ≃ Elements (tracePiSet a b) where
  toFun := graphToTrace
  invFun := traceToGraph
  left_inv := traceToGraph_graphToTrace
  right_inv := graphToTrace_traceToGraph

noncomputable def traceEncode {a : ZFSet.{u}} {b : ZFSet.{u} → ZFSet.{u}}
    (f : (x : Elements a) → Elements (b x.1)) : Elements (tracePiSet a b) :=
  graphToTrace (encodeFunction (a := a) (b := b) f)

theorem trace_beta {a : ZFSet.{u}} {b : ZFSet.{u} → ZFSet.{u}}
    (f : (x : Elements a) → Elements (b x.1)) : traceValue (traceEncode f) = f := by
  rw [traceEncode, traceValue_graphToTrace, decode_encode_function]

theorem trace_eta {a : ZFSet.{u}} {b : ZFSet.{u} → ZFSet.{u}}
    (t : Elements (tracePiSet a b)) : traceEncode (traceValue t) = t :=
  graphToTrace_traceToGraph t

noncomputable def tracePiEquiv (a : ZFSet.{u}) (b : ZFSet.{u} → ZFSet.{u}) :
    Elements (tracePiSet a b) ≃ ((x : Elements a) → Elements (b x.1)) where
  toFun := traceValue
  invFun := traceEncode
  left_inv := trace_eta
  right_inv := trace_beta

/-! ## Closure and dependence only on the declared fibres -/

theorem _root_.Mettapedia.Logic.HOL.Embedding.ZFSetUniverseClosure.Closed.traceLam_mem
    {U r : ZFSet.{u}} (closed : Closed U) (hr : r ∈ U) : traceLam r ∈ U := by
  have hc : coordinates r ∈ U := closed.union_mem (closed.union_mem hr)
  unfold traceLam ZFSet.pairSep
  exact closed.separation_mem (closed.power_mem (closed.power_mem
    (closed.binaryUnion_mem hc (closed.union_mem hc)))) _

theorem _root_.Mettapedia.Logic.HOL.Embedding.ZFSetUniverseClosure.Closed.traceApp_mem
    {U r : ZFSet.{u}} (closed : Closed U) (hr : r ∈ U) (x : ZFSet.{u}) :
    traceApp r x ∈ U :=
  closed.separation_mem (closed.union_mem (closed.union_mem hr)) _

theorem _root_.Mettapedia.Logic.HOL.Embedding.ZFSetUniverseClosure.Closed.tracePiSet_mem
    {U a : ZFSet.{u}} (closed : Closed U) (ha : a ∈ U)
    (b : ZFSet.{u} → ZFSet.{u}) (hb : ∀ x ∈ a, b x ∈ U) :
    tracePiSet a b ∈ U :=
  closed.replacement_mem (closed.piSet_mem ha b hb) traceLam
    (fun _ hf => closed.traceLam_mem
      (closed.transitive _ (closed.piSet_mem ha b hb) hf))

theorem tracePiSet_congr {a : ZFSet.{u}} {b c : ZFSet.{u} → ZFSet.{u}}
    (equal : ∀ x ∈ a, b x = c x) : tracePiSet a b = tracePiSet a c := by
  unfold tracePiSet
  rw [piSet_congr equal]

theorem tracePiSet_context_substitution {Γ Δ : Type*} (θ : Δ → Γ)
    (a : Γ → ZFSet.{u}) (b : Γ → ZFSet.{u} → ZFSet.{u}) :
    (fun γ => tracePiSet (a γ) (b γ)) ∘ θ =
      (fun δ => tracePiSet ((a ∘ θ) δ) (b (θ δ))) := rfl

/-- Substitution does not change the underlying trace value or its argument. -/
theorem traceApp_context_substitution {Γ Δ : Type*} (θ : Δ → Γ)
    (t x : Γ → ZFSet.{u}) :
    (fun γ => traceApp (t γ) (x γ)) ∘ θ =
      (fun δ => traceApp ((t ∘ θ) δ) ((x ∘ θ) δ)) := rfl

theorem traceLam_context_substitution {Γ Δ : Type*} (θ : Δ → Γ)
    (f : Γ → ZFSet.{u}) : (traceLam ∘ f) ∘ θ = traceLam ∘ (f ∘ θ) := rfl

/-! ## The exact subterminal product code -/

theorem traceApp_empty (x : ZFSet.{u}) : traceApp ∅ x = ∅ := by
  apply ZFSet.ext
  intro z
  rw [mem_traceApp]
  simp

theorem traceLam_empty : traceLam (∅ : ZFSet.{u}) = ∅ := by
  apply ZFSet.ext
  intro p
  rw [mem_traceLam]
  simp

theorem traceLam_graph_empty (a : ZFSet.{u}) : traceLam (graph a (fun _ => ∅)) = ∅ := by
  apply ZFSet.ext
  intro p
  rw [traceLam_graph, mem_sigmaSet]
  simp

theorem tracePiSet_subterminal {a : ZFSet.{u}} {b : ZFSet.{u} → ZFSet.{u}}
    (hb : ∀ x ∈ a, b x ⊆ ({∅} : ZFSet.{u})) :
    tracePiSet a b ⊆ ({∅} : ZFSet.{u}) := by
  intro t ht
  obtain ⟨f, hf, rfl⟩ := mem_tracePiSet.mp ht
  apply ZFSet.mem_singleton.mpr
  apply ZFSet.ext
  intro p
  constructor
  · intro hp
    obtain ⟨x, y, z, hxy, hzy, _⟩ := mem_traceLam.mp hp
    have hx : x ∈ a :=
      (ZFSet.pair_mem_prod.mp ((mem_piSet.mp hf).1.1 hxy)).1
    have hy : y ∈ b x := (mem_piSet.mp hf).2 x hx y hxy
    have he : y = ∅ := ZFSet.mem_singleton.mp (hb x hx hy)
    exact False.elim (ZFSet.notMem_empty z (he ▸ hzy))
  · exact fun hp => False.elim (ZFSet.notMem_empty p hp)

/-- Uniform trace formation itself gives the canonical truth code for a
subterminal family; the product definition contains no subterminal test. -/
theorem mem_tracePiSet_subterminal_iff {a t : ZFSet.{u}}
    {b : ZFSet.{u} → ZFSet.{u}}
    (hb : ∀ x ∈ a, b x ⊆ ({∅} : ZFSet.{u})) :
    t ∈ tracePiSet a b ↔ t = ∅ ∧ ∀ x ∈ a, (∅ : ZFSet.{u}) ∈ b x := by
  constructor
  · intro ht
    have he : t = ∅ := ZFSet.mem_singleton.mp (tracePiSet_subterminal hb ht)
    refine ⟨he, fun x hx => ?_⟩
    have hv := traceApp_mem (b := b) ⟨t, ht⟩ ⟨x, hx⟩
    change traceApp t x ∈ b x at hv
    rw [he, traceApp_empty] at hv
    exact hv
  · rintro ⟨rfl, inhabited⟩
    exact mem_tracePiSet.mpr ⟨graph a (fun _ => ∅),
      graph_mem_piSet inhabited, traceLam_graph_empty a⟩

theorem tracePiSet_eq_truth {a : ZFSet.{u}} {b : ZFSet.{u} → ZFSet.{u}}
    (hb : ∀ x ∈ a, b x ⊆ ({∅} : ZFSet.{u})) :
    tracePiSet a b =
      ZFSet.sep (fun _ => ∀ x ∈ a, (∅ : ZFSet.{u}) ∈ b x) {∅} := by
  apply ZFSet.ext
  intro t
  rw [mem_tracePiSet_subterminal_iff hb, ZFSet.mem_sep, ZFSet.mem_singleton]

/-- Lee--Werner Lemma 3.3(2), as equality of the actual product code. -/
theorem tracePiSet_eq_unit_iff {a : ZFSet.{u}} {b : ZFSet.{u} → ZFSet.{u}}
    (hb : ∀ x ∈ a, b x ⊆ ({∅} : ZFSet.{u})) :
    tracePiSet a b = ({∅} : ZFSet.{u}) ↔ ∀ x ∈ a, b x = {∅} := by
  constructor
  · intro equal x hx
    have ht : (∅ : ZFSet.{u}) ∈ tracePiSet a b := equal ▸ ZFSet.mem_singleton.mpr rfl
    have he := (mem_tracePiSet_subterminal_iff hb).mp ht
    apply ZFSet.ext
    intro z
    constructor
    · exact fun hz => hb x hx hz
    · intro hz
      obtain rfl := ZFSet.mem_singleton.mp hz
      exact he.2 x hx
  · intro equal
    apply ZFSet.ext
    intro t
    rw [mem_tracePiSet_subterminal_iff hb, ZFSet.mem_singleton]
    exact ⟨And.left, fun ht => ⟨ht, fun x hx =>
      (equal x hx).symm ▸ ZFSet.mem_singleton.mpr rfl⟩⟩

theorem tracePiSet_empty_of_empty_fibre {a : ZFSet.{u}}
    {b : ZFSet.{u} → ZFSet.{u}} (x : Elements a) (emptyFibre : b x.1 = ∅) :
    tracePiSet a b = ∅ := by
  apply ZFSet.ext
  intro t
  constructor
  · intro ht
    have hv := traceApp_mem (b := b) ⟨t, ht⟩ x
    rw [emptyFibre] at hv
    exact False.elim (ZFSet.notMem_empty _ hv)
  · exact fun ht => False.elim (ZFSet.notMem_empty _ ht)

/-! ## Controls: varying values and fibres, and loss of an untyped domain -/

namespace Controls

open ZFSetDependentProducts.Controls

noncomputable def varyingSection (x : Elements two.{u}) : Elements (varying x.1) := by
  classical
  refine ⟨x.1, ?_⟩
  by_cases hx : x.1 = ∅
  · simp only [varying, hx]
    exact ZFSet.mem_singleton.mpr rfl
  · simp only [varying, if_neg hx]
    exact x.2

noncomputable def varyingTrace : Elements (tracePiSet two.{u} varying) :=
  traceEncode (a := two) (b := varying) varyingSection

theorem varying_trace_at_empty :
    traceApp varyingTrace.{u}.1 ∅ = ∅ :=
  congrArg Subtype.val (congrFun (trace_beta varyingSection) ⟨∅, empty_mem_two⟩)

theorem varying_trace_at_power_empty :
    traceApp varyingTrace.{u}.1 (ZFSet.powerset ∅) = ZFSet.powerset ∅ :=
  congrArg Subtype.val
    (congrFun (trace_beta varyingSection) ⟨ZFSet.powerset ∅, power_empty_mem_two⟩)

theorem varying_trace_nonempty : varyingTrace.{u}.1 ≠ ∅ := by
  intro empty
  have member : (∅ : ZFSet.{u}) ∈ ZFSet.powerset ∅ :=
    ZFSet.mem_powerset.mpr (ZFSet.empty_subset _)
  rw [← varying_trace_at_power_empty, empty, traceApp_empty] at member
  exact ZFSet.notMem_empty _ member

theorem missing_trace_product_empty : tracePiSet two.{u} missingFibre = ∅ :=
  tracePiSet_empty_of_empty_fibre ⟨∅, empty_mem_two⟩ (by simp [missingFibre])

theorem distinct_domains : (∅ : ZFSet.{u}) ≠ ({∅} : ZFSet.{u}) := by
  intro equal
  have member : (∅ : ZFSet.{u}) ∈ ({∅} : ZFSet.{u}) := ZFSet.mem_singleton.mpr rfl
  rw [← equal] at member
  exact ZFSet.notMem_empty _ member

/-- The beta equation fails for a nonempty argument outside the retained
domain; the domain admission in the positive law cannot be erased. -/
theorem outside_domain_beta_fails :
    traceApp (traceLam (graph (∅ : ZFSet.{u}) (fun x => x))) {∅} ≠
      ({∅} : ZFSet.{u}) := by
  rw [traceApp_graph_outside (fun x => x) (ZFSet.notMem_empty _)]
  exact distinct_domains

/-- Equal untyped traces do not imply equal function domains. -/
theorem distinct_domains_same_trace :
    traceLam (graph (∅ : ZFSet.{u}) (fun _ => ∅)) =
      traceLam (graph ({∅} : ZFSet.{u}) (fun _ => ∅)) := by
  rw [traceLam_graph_empty, traceLam_graph_empty]

/-- The original graphs still distinguish those domains. -/
theorem distinct_domains_distinct_graphs :
    graph (∅ : ZFSet.{u}) (fun _ => ∅) ≠
      graph ({∅} : ZFSet.{u}) (fun _ => ∅) := by
  intro equal
  have member : ZFSet.pair (∅ : ZFSet.{u}) ∅ ∈ graph ({∅} : ZFSet.{u}) (fun _ => ∅) :=
    pair_mem_graph.mpr ⟨ZFSet.mem_singleton.mpr rfl, rfl⟩
  rw [← equal, pair_mem_graph] at member
  exact ZFSet.notMem_empty _ member.1

end Controls

#print axioms traceLam_graph
#print axioms traceApp_graph_beta
#print axioms traceApp_graph_outside
#print axioms traceLam_injective_fixed_domain
#print axioms graphTraceEquiv
#print axioms tracePiEquiv
#print axioms trace_beta
#print axioms trace_eta
#print axioms Closed.traceLam_mem
#print axioms Closed.tracePiSet_mem
#print axioms tracePiSet_congr
#print axioms tracePiSet_subterminal
#print axioms tracePiSet_eq_truth
#print axioms tracePiSet_eq_unit_iff
#print axioms Controls.varying_trace_at_empty
#print axioms Controls.varying_trace_at_power_empty
#print axioms Controls.outside_domain_beta_fails
#print axioms Controls.varying_trace_nonempty
#print axioms Controls.missing_trace_product_empty
#print axioms Controls.distinct_domains_same_trace
#print axioms Controls.distinct_domains_distinct_graphs

end Mettapedia.Logic.HOL.Embedding.ZFSetTraceProducts
