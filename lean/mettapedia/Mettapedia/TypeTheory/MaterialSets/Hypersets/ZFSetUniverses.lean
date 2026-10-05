import Mettapedia.TypeTheory.MaterialSets.Hypersets.Universes
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ZFSetModel
import Mettapedia.Logic.HOL.Embedding.ZFSetUniverseClosure
import Mettapedia.Logic.HOL.Embedding.ZFSetUniverseLift
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.SetTheory.ZFC.Ordinal

/-!
# Universes of the well-founded part through `ZFSet`

The equivalence `wellFoundedPartEquivZFSet` between the well-founded hypersets and `ZFSet`
carries Grothendieck universes to the closed universes of
`Logic.HOL.Embedding.ZFSetUniverseClosure` and back (`isGrothendieckUniverse_iff_closed`). A
closed `ZFSet` universe has no pairing law, yet it is closed under pairs
(`closed_pair_mem`): `{a, b}` is the image of `𝒫 𝒫 ∅` under `z ↦ if ∅ ∈ z then b else a`. That
case split is excluded middle; the intuitionistic universe laws state pairing directly.

The least universe is carried as well (`equiv_hull`). Under the explicit large-cardinal
hypothesis `CofinalInaccessibles.{u}` (cofinally many inaccessible cardinals at level `u`), the
least-universe operation of `ZFSet`, carried to the well-founded part (`univOf`,
`equiv_univOf`), satisfies the four universe laws (`isUniverseOperator_univOf`). It is therefore
the operation of every universe enclosure (`UniverseEnclosure.univOf_eq_univOf`), and every
well-founded set lies in a universe (`exists_isGrothendieckUniverse`). The hypothesis is a
parameter of each statement, never an axiom.

Without any hypothesis, Lean's universe levels supply one universe at level `u + 1`: the
carried image of `V_κ` for the inaccessible `κ = Cardinal.univ.{u}` (`smallUniverse`,
`isGrothendieckUniverse_smallUniverse`), and so the least universe containing `∅` at that level
(`leastEmptyUniverse`, `equiv_leastEmptyUniverse`).

`ZFSetUniverseClosure` defines replacement through `Classical.allZFSetDefinable` and chooses
enclosures and inaccessible cardinals with `Classical.choice`; every statement here that
mentions a closed `ZFSet` universe inherits that dependency.

Every hyperset of level `u` is one set of level `u + 1` (`code`). A picture whose nodes are
the members of a set, together with a set of edges and a point, is a triple of the lower
universe (`graphTriple`); `code x` is the set of the lifts of the triples that picture `x`.
The code is injective (`code_injective`) and `decodeHSet` reads it back (`decodeHSet_code`).
All codes form `hsetCode`, a subset of the power set of `carrierCode`
(`hsetCode_subset_powerset_carrierCode`) and a member of every closed universe that already
contains `carrierCode` (`hsetCode_mem_of_carrierCode_mem`). Membership of hypersets is the
relation `codeMem` on those codes. The code of a well-founded hyperset determines the set
(`decodeWellFounded_code`). The code of `Ω` differs from the code of every well-founded set
(`code_quineAtom_ne_ofZFSet`). The one-node loop and the two-node cycle are different graphs
(`canonicalGraph_loop_ne_twoCycle`) and one hyperset, so their codes agree
(`code_loop_eq_code_twoCycle`).

A type of level `u` is in bijection with the members of a set (`elementsEquiv`) by well-ordering
it, which uses `Classical.choice`. Choosing a graph of a hyperset uses the quotient, and so
does `decodeHSet`.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets

open HSet Mettapedia.Logic.HOL.Embedding

universe u

/-! ## Pairs in a closed `ZFSet` universe -/

section Closed

open ZFSetUniverseClosure ZFSetHenkinInterpretation

theorem closed_empty_mem {U a : ZFSet.{u}} (hU : Closed U) (ha : a ∈ U) : (∅ : ZFSet.{u}) ∈ U :=
  hU.transitive _ (hU.power_mem ha) (ZFSet.mem_powerset.mpr (ZFSet.empty_subset a))

/-- A closed `ZFSet` universe is closed under pairs. The proof separates `𝒫 𝒫 ∅` by the case
split `∅ ∈ z`, which is excluded middle. -/
theorem closed_pair_mem {U a b : ZFSet.{u}} (hU : Closed U) (ha : a ∈ U) (hb : b ∈ U) :
    ({a, b} : ZFSet.{u}) ∈ U := by
  classical
  have hP : ZFSet.powerset (ZFSet.powerset (∅ : ZFSet.{u})) ∈ U :=
    hU.power_mem (hU.power_mem (closed_empty_mem hU ha))
  let f : ZFSet.{u} → ZFSet.{u} := fun z => if (∅ : ZFSet.{u}) ∈ z then b else a
  have values : ∀ z ∈ ZFSet.powerset (ZFSet.powerset (∅ : ZFSet.{u})), f z ∈ U := by
    intro z _
    by_cases h : (∅ : ZFSet.{u}) ∈ z
    · simp only [f, if_pos h]
      exact hb
    · simp only [f, if_neg h]
      exact ha
  have same : replacement (ZFSet.powerset (ZFSet.powerset (∅ : ZFSet.{u}))) f = {a, b} := by
    ext y
    rw [mem_replacement, ZFSet.mem_insert_iff, ZFSet.mem_singleton]
    constructor
    · rintro ⟨z, _, rfl⟩
      by_cases h : (∅ : ZFSet.{u}) ∈ z
      · right
        simp [f, h]
      · left
        simp [f, h]
    · rintro (rfl | rfl)
      · refine ⟨∅, ZFSet.mem_powerset.mpr (ZFSet.empty_subset _), ?_⟩
        simp only [f, if_neg (ZFSet.notMem_empty ∅)]
      · refine ⟨{∅}, ZFSet.mem_powerset.mpr fun w hw => ?_, ?_⟩
        · rw [ZFSet.mem_singleton.mp hw]
          exact ZFSet.mem_powerset.mpr (ZFSet.empty_subset _)
        · simp only [f, if_pos (ZFSet.mem_singleton.mpr rfl)]
  rw [← same]
  exact hU.replacement_mem hP f values

end Closed

namespace WellFoundedPart

open ZFSetUniverseClosure ZFSetHenkinInterpretation

/-- The equivalence of the well-founded part with `ZFSet`. -/
local notation "toZF" => wellFoundedPartEquivZFSet

/-- Its inverse. -/
local notation "ofZF" => wellFoundedPartEquivZFSet.symm

/-! ## The operations through the equivalence -/

theorem mem_iff_equiv_mem {x X : WellFoundedPart.{u}} : Mem x X ↔ toZF x ∈ toZF X :=
  wellFoundedPartEquivZFSet_mem_iff.symm

theorem mem_equiv_iff {z : ZFSet.{u}} {X : WellFoundedPart.{u}} :
    z ∈ toZF X ↔ Mem (ofZF z) X := by
  rw [mem_iff_equiv_mem, Equiv.apply_symm_apply]

theorem subset_iff_equiv {X Y : WellFoundedPart.{u}} : Subset X Y ↔ toZF X ⊆ toZF Y := by
  constructor
  · intro h z hz
    exact mem_equiv_iff.mpr (h (mem_equiv_iff.mp hz))
  · intro h z hz
    have hwf : z.WF := X.2.mem hz
    exact mem_iff_equiv_mem.mpr (h ((mem_iff_equiv_mem (x := ⟨z, hwf⟩) (X := X)).mp hz))

theorem equiv_sUnion (X : WellFoundedPart.{u}) : toZF (sUnion X) = ZFSet.sUnion (toZF X) :=
  equiv_union X

theorem equiv_powerset (X : WellFoundedPart.{u}) :
    toZF (powerset X) = ZFSet.powerset (toZF X) := by
  apply ofZFSet_injective
  rw [ofZFSet_equiv, ofZFSet_powerset, ofZFSet_equiv]
  rfl

theorem equiv_upair (x y : WellFoundedPart.{u}) : toZF (upair x y) = {toZF x, toZF y} := by
  apply ofZFSet_injective
  rw [ofZFSet_equiv, ofZFSet_pair, ofZFSet_equiv, ofZFSet_equiv]
  rfl

/-- The image of a family below a bound, through the equivalence. -/
theorem mem_equiv_imageWithin {B X : WellFoundedPart.{u}} {F : El Mem X → WellFoundedPart.{u}}
    (bound : ∀ a, Mem (F a) B) {z : ZFSet.{u}} :
    z ∈ toZF (imageWithin B X F) ↔ ∃ a, toZF (F a) = z := by
  rw [mem_equiv_iff, mem_imageWithin bound]
  exact exists_congr fun _ => ⟨fun e => by rw [e, Equiv.apply_symm_apply],
    fun e => by rw [← e, Equiv.symm_apply_apply]⟩

/-- Inclusion of carried sets is inclusion of the sets. -/
theorem subset_symm_iff {a b : ZFSet.{u}} : Subset (ofZF a) (ofZF b) ↔ a ⊆ b := by
  rw [subset_iff_equiv, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- The union of a carried set is the carried union. -/
theorem sUnion_symm (a : ZFSet.{u}) : sUnion (ofZF a) = ofZF (ZFSet.sUnion a) := by
  rw [Equiv.eq_symm_apply, equiv_sUnion, Equiv.apply_symm_apply]

/-! ## Universes through the equivalence -/

/-- A well-founded set is a Grothendieck universe exactly when its `ZFSet` is a closed
universe. -/
theorem isGrothendieckUniverse_iff_closed (U : WellFoundedPart.{u}) :
    IsGrothendieckUniverse U ↔ Closed (toZF U) := by
  constructor
  · intro hU
    refine ⟨fun a ha y hy => ?_, fun {a} ha => ?_, fun {a} ha => ?_, fun {a} ha f hf => ?_⟩
    · have hA := mem_equiv_iff.mp ha
      have hy' : Mem (ofZF y) (ofZF a) :=
        mem_iff_equiv_mem.mpr (by rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply])
      exact mem_equiv_iff.mpr (hU.transitive hA hy')
    · have h := mem_iff_equiv_mem.mp (hU.sUnion_mem (mem_equiv_iff.mp ha))
      rwa [equiv_sUnion, Equiv.apply_symm_apply] at h
    · have h := mem_iff_equiv_mem.mp (hU.powerset_mem (mem_equiv_iff.mp ha))
      rwa [equiv_powerset, Equiv.apply_symm_apply] at h
    · let F : El Mem (ofZF a) → WellFoundedPart.{u} := fun b => ofZF (f (toZF b.1))
      have hb : ∀ b : El Mem (ofZF a), toZF b.1 ∈ a := fun b => by
        have h := mem_iff_equiv_mem.mp b.2
        rwa [Equiv.apply_symm_apply] at h
      have hF : ∀ b, Mem (F b) U := fun b => mem_equiv_iff.mp (hf _ (hb b))
      have same : toZF (imageWithin U (ofZF a) F) = replacement a f := by
        ext z
        rw [mem_equiv_imageWithin hF, mem_replacement]
        constructor
        · rintro ⟨b, rfl⟩
          exact ⟨toZF b.1, hb b, (Equiv.apply_symm_apply _ _).symm⟩
        · rintro ⟨x, hx, rfl⟩
          refine ⟨⟨ofZF x, mem_equiv_iff.mp (by rwa [Equiv.apply_symm_apply])⟩, ?_⟩
          change toZF (ofZF (f (toZF (ofZF x)))) = f x
          rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      rw [← same]
      exact mem_iff_equiv_mem.mp (hU.image_mem (mem_equiv_iff.mp ha) F hF)
  · intro hU
    refine ⟨fun X z hX hz => ?_, fun X hX => ?_, fun X hX => ?_, fun x y hx hy => ?_,
      fun X hX F hF => ?_⟩
    · have hwf : z.WF := X.2.mem hz
      exact mem_iff_equiv_mem.mpr (hU.transitive _ (mem_iff_equiv_mem.mp hX)
        ((mem_iff_equiv_mem (x := ⟨z, hwf⟩) (X := X)).mp hz))
    · rw [mem_iff_equiv_mem, equiv_sUnion]
      exact hU.union_mem (mem_iff_equiv_mem.mp hX)
    · rw [mem_iff_equiv_mem, equiv_powerset]
      exact hU.power_mem (mem_iff_equiv_mem.mp hX)
    · rw [mem_iff_equiv_mem, equiv_upair]
      exact closed_pair_mem hU (mem_iff_equiv_mem.mp hx) (mem_iff_equiv_mem.mp hy)
    · classical
      have hX' : ∀ {x : ZFSet.{u}}, x ∈ toZF X → Mem (ofZF x) X := fun h => mem_equiv_iff.mp h
      let f : ZFSet.{u} → ZFSet.{u} := fun x => if h : x ∈ toZF X then toZF (F ⟨_, hX' h⟩) else ∅
      have hf : ∀ b : El Mem X, f (toZF b.1) = toZF (F b) := fun b => by
        have hb : toZF b.1 ∈ toZF X := mem_iff_equiv_mem.mp b.2
        simp only [f, dif_pos hb]
        exact congrArg (fun c => toZF (F c)) (El.ext propositional (Equiv.symm_apply_apply _ _))
      have values : ∀ x ∈ toZF X, f x ∈ toZF U := fun x hx => by
        have e := hf ⟨ofZF x, hX' hx⟩
        rw [Equiv.apply_symm_apply] at e
        rw [e]
        exact mem_iff_equiv_mem.mp (hF _)
      have same : toZF (imageWithin U X F) = replacement (toZF X) f := by
        ext z
        rw [mem_equiv_imageWithin hF, mem_replacement]
        constructor
        · rintro ⟨b, rfl⟩
          exact ⟨toZF b.1, mem_iff_equiv_mem.mp b.2, hf b⟩
        · rintro ⟨x, hx, rfl⟩
          have e := hf ⟨ofZF x, hX' hx⟩
          rw [Equiv.apply_symm_apply] at e
          exact ⟨_, e.symm⟩
      rw [mem_iff_equiv_mem, same]
      exact hU.replacement_mem (mem_iff_equiv_mem.mp hX) f values

/-- A carried set is a Grothendieck universe exactly when the set is a closed universe. -/
theorem isGrothendieckUniverse_symm_iff {a : ZFSet.{u}} :
    IsGrothendieckUniverse (ofZF a) ↔ Closed a := by
  rw [isGrothendieckUniverse_iff_closed, Equiv.apply_symm_apply]

/-- The least universe is carried to the least closed universe. -/
theorem equiv_hull (N B : WellFoundedPart.{u}) :
    toZF (hull N B) = ZFSetUniverseClosure.hull (toZF N) (toZF B) := by
  ext z
  rw [mem_equiv_iff, ZFSetUniverseClosure.mem_hull]
  change (ofZF z).1 ∈ (hull N B).1 ↔ _
  rw [mem_hull]
  refine and_congr (mem_equiv_iff.symm) ⟨fun h V hN hV => ?_, fun h U hN hU => ?_⟩
  · have hU : IsGrothendieckUniverse (ofZF V) :=
      (isGrothendieckUniverse_iff_closed _).mpr (by rwa [Equiv.apply_symm_apply])
    have hN' : Mem N (ofZF V) := by
      rw [mem_iff_equiv_mem, Equiv.apply_symm_apply]
      exact hN
    have hz := mem_equiv_iff.mpr (h _ hN' hU)
    rwa [Equiv.apply_symm_apply] at hz
  · exact mem_equiv_iff.mp
      (h _ (mem_iff_equiv_mem.mp hN) ((isGrothendieckUniverse_iff_closed U).mp hU))

/-! ## The least-universe operation under cofinally many inaccessibles -/

/-- The least-universe operation of `ZFSet`, carried to the well-founded part. -/
noncomputable def univOf (h : CofinalInaccessibles.{u}) (N : WellFoundedPart.{u}) :
    WellFoundedPart.{u} :=
  ofZF (ZFSetUniverseClosure.univOf h (toZF N))

theorem equiv_univOf (h : CofinalInaccessibles.{u}) (N : WellFoundedPart.{u}) :
    toZF (univOf h N) = ZFSetUniverseClosure.univOf h (toZF N) :=
  Equiv.apply_symm_apply _ _

/-- The carried operation at a carried set is the carried least closed universe. -/
theorem univOf_symm (h : CofinalInaccessibles.{u}) (a : ZFSet.{u}) :
    univOf h (ofZF a) = ofZF (ZFSetUniverseClosure.univOf h a) := by
  rw [univOf, Equiv.apply_symm_apply]

/-- Under cofinally many inaccessibles, the carried operation satisfies the four universe
laws. -/
theorem isUniverseOperator_univOf (h : CofinalInaccessibles.{u}) :
    IsUniverseOperator (univOf h) where
  mem_univOf N := by
    rw [mem_iff_equiv_mem, equiv_univOf]
    exact ZFSetUniverseClosure.mem_univOf h _
  isGrothendieckUniverse N := by
    rw [isGrothendieckUniverse_iff_closed, equiv_univOf]
    exact ZFSetUniverseClosure.univOf_closed h _
  minimal N U hN hU := by
    rw [subset_iff_equiv, equiv_univOf]
    exact ZFSetUniverseClosure.univOf_minimal h (mem_iff_equiv_mem.mp hN)
      ((isGrothendieckUniverse_iff_closed U).mp hU)

/-- The universe enclosure given by cofinally many inaccessibles. -/
noncomputable def enclosure (h : CofinalInaccessibles.{u}) : UniverseEnclosure.{u} where
  enclose := univOf h
  mem_enclose := (isUniverseOperator_univOf h).mem_univOf
  isGrothendieckUniverse_enclose := (isUniverseOperator_univOf h).isGrothendieckUniverse

/-- Every universe enclosure yields the carried operation. -/
theorem UniverseEnclosure.univOf_eq_univOf (e : UniverseEnclosure.{u})
    (h : CofinalInaccessibles.{u}) : e.univOf = WellFoundedPart.univOf h :=
  e.isUniverseOperator.unique (isUniverseOperator_univOf h)

/-- Under cofinally many inaccessibles, every well-founded set lies in a universe. -/
theorem exists_isGrothendieckUniverse (h : CofinalInaccessibles.{u}) (N : WellFoundedPart.{u}) :
    ∃ U, Mem N U ∧ IsGrothendieckUniverse U :=
  ⟨univOf h N, (isUniverseOperator_univOf h).mem_univOf N,
    (isUniverseOperator_univOf h).isGrothendieckUniverse N⟩

/-! ## A universe from Lean's universe levels, without hypothesis -/

/-- The universe `V_κ` at level `u + 1`, for the inaccessible `κ = Cardinal.univ.{u}`. -/
noncomputable def smallUniverse : WellFoundedPart.{u + 1} :=
  ofZF ZFSetUniverseClosure.smallUniverse.{u}

theorem isGrothendieckUniverse_smallUniverse : IsGrothendieckUniverse smallUniverse.{u} := by
  rw [isGrothendieckUniverse_iff_closed, smallUniverse, Equiv.apply_symm_apply]
  exact smallUniverse_closed

theorem empty_mem_smallUniverse : Mem empty smallUniverse.{u} := by
  rw [mem_iff_equiv_mem, smallUniverse, Equiv.apply_symm_apply]
  have h : toZF empty.{u + 1} = ∅ := by
    apply ofZFSet_injective
    rw [ofZFSet_equiv, ofZFSet_empty]
    rfl
  rw [h]
  exact ZFSetUniverseClosure.empty_mem_smallUniverse

/-- The least universe containing `∅` at level `u + 1`, without any hypothesis. -/
noncomputable def leastEmptyUniverse : WellFoundedPart.{u + 1} :=
  hull empty smallUniverse.{u}

theorem isGrothendieckUniverse_leastEmptyUniverse :
    IsGrothendieckUniverse leastEmptyUniverse.{u} :=
  hull_isGrothendieckUniverse isGrothendieckUniverse_smallUniverse

theorem empty_mem_leastEmptyUniverse : Mem empty leastEmptyUniverse.{u} :=
  mem_hull_self empty_mem_smallUniverse

theorem equiv_leastEmptyUniverse :
    toZF leastEmptyUniverse.{u} = ZFSetUniverseClosure.leastEmptyUniverse.{u} := by
  rw [leastEmptyUniverse, equiv_hull, smallUniverse, Equiv.apply_symm_apply]
  have h : toZF empty.{u + 1} = ∅ := by
    apply ofZFSet_injective
    rw [ofZFSet_equiv, ofZFSet_empty]
    rfl
  rw [h]
  rfl

end WellFoundedPart

/-! ## Hypersets of one universe as a set of the next -/

open Mettapedia.Logic.HOL.Embedding.ZFSetUniverseLift

/-- A graph with nodes, edges and a point, packed as one set: the triple `(nodes, (edges, point))`. -/
def graphTriple (nodes edges point : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.pair nodes (ZFSet.pair edges point)

/-- The three components of a graph triple are determined by the triple. -/
theorem graphTriple_inj {n e p n' e' p' : ZFSet.{u}} :
    graphTriple n e p = graphTriple n' e' p' ↔ n = n' ∧ e = e' ∧ p = p' := by
  constructor
  · intro h
    obtain ⟨hn, hep⟩ := ZFSet.pair_inj.mp h
    obtain ⟨he, hp⟩ := ZFSet.pair_inj.mp hep
    exact ⟨hn, he, hp⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

/-- An edge of the set `edges`, read on a small copy of the members of `nodes`. -/
noncomputable def edgeRel (nodes edges : ZFSet.{u}) (a b : Shrink.{u} nodes) : Prop :=
  ZFSet.pair ((equivShrink.{u} nodes).symm a).1 ((equivShrink.{u} nodes).symm b).1 ∈ edges

/-- `g` pictures `x`: it is a graph triple, and the hyperset at its point is `x`. -/
noncomputable def Pictures (x : HSet.{u}) (g : ZFSet.{u}) : Prop :=
  ∃ (nodes edges point : ZFSet.{u}) (hp : point ∈ nodes),
    g = graphTriple nodes edges point ∧ edges ⊆ ZFSet.prod nodes nodes ∧
      decorate (edgeRel nodes edges) (equivShrink.{u} nodes ⟨point, hp⟩) = x

/-- The von Neumann code of a node, along a well-ordering of its type. -/
noncomputable def nodeCode {α : Type u} (a : α) : ZFSet.{u} :=
  Ordinal.toZFSet (Ordinal.typein WellOrderingRel a)

/-- Distinct nodes receive distinct codes. -/
theorem nodeCode_injective {α : Type u} : Function.Injective (nodeCode : α → ZFSet.{u}) :=
  fun _ _ h => Ordinal.typein_injective WellOrderingRel (Ordinal.toZFSet_injective h)

/-- The set of node codes of a type. -/
noncomputable def nodeSet (α : Type u) : ZFSet.{u} :=
  ZFSet.range (nodeCode : α → ZFSet.{u})

/-- Every node code is a member of the node set. -/
theorem nodeCode_mem {α : Type u} (a : α) : nodeCode a ∈ nodeSet α :=
  ZFSet.mem_range_self a

/-- Every type of level `u` is in bijection with the members of its node set. -/
noncomputable def elementsEquiv (α : Type u) : α ≃ {x : ZFSet.{u} // x ∈ nodeSet α} :=
  Equiv.ofBijective (fun a => ⟨nodeCode a, nodeCode_mem a⟩) ⟨
    fun _ _ h => nodeCode_injective (congrArg Subtype.val h),
    fun ⟨x, hx⟩ => by
      rw [nodeSet, ZFSet.mem_range] at hx
      obtain ⟨a, rfl⟩ := hx
      exact ⟨a, rfl⟩⟩

/-- The set of edges of a graph, as Kuratowski pairs of node codes. -/
noncomputable def edgeSet (G : AccessiblePointedGraph.{u}) : ZFSet.{u} :=
  ZFSet.pairSep
    (fun a b => ∃ x y : G.Node, nodeCode x = a ∧ nodeCode y = b ∧ G.edge x y)
    (nodeSet G.Node) (nodeSet G.Node)

/-- The edges of a graph are pairs of its node codes. -/
theorem edgeSet_subset_prod (G : AccessiblePointedGraph.{u}) :
    edgeSet G ⊆ ZFSet.prod (nodeSet G.Node) (nodeSet G.Node) := by
  intro z hz
  obtain ⟨a, ha, b, hb, rfl, _⟩ := ZFSet.mem_pairSep.mp hz
  exact ZFSet.mem_prod.mpr ⟨a, ha, b, hb, rfl⟩

/-- A pair lies in the edge set exactly when it is the code of an edge. -/
theorem mem_edgeSet_iff (G : AccessiblePointedGraph.{u}) {a b : ZFSet.{u}} :
    ZFSet.pair a b ∈ edgeSet G ↔
      ∃ x y : G.Node, nodeCode x = a ∧ nodeCode y = b ∧ G.edge x y := by
  rw [edgeSet, ZFSet.mem_pairSep]
  constructor
  · rintro ⟨a', _, b', _, heq, x, y, hx, hy, hedge⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.mp heq
    exact ⟨x, y, hx, hy, hedge⟩
  · rintro ⟨x, y, rfl, rfl, hedge⟩
    exact ⟨nodeCode x, nodeCode_mem x, nodeCode y, nodeCode_mem y, rfl, x, y, rfl, rfl, hedge⟩

/-- The small copy of a node, through the bijection with the members of the node set. -/
noncomputable def canonicalNode (G : AccessiblePointedGraph.{u}) (a : G.Node) :
    Shrink.{u} (nodeSet G.Node) :=
  equivShrink.{u} _ (elementsEquiv G.Node a)

/-- The member named by a small node code is the node's von Neumann code. -/
theorem canonicalNode_code (G : AccessiblePointedGraph.{u}) (a : G.Node) :
    ((equivShrink.{u} (nodeSet G.Node)).symm (canonicalNode G a)).1 = nodeCode a := by
  rw [canonicalNode, Equiv.symm_apply_apply]
  rfl

/-- Edges of the small copy are the edges of the graph. -/
theorem edgeRel_canonicalNode (G : AccessiblePointedGraph.{u}) (a a' : G.Node) :
    edgeRel (nodeSet G.Node) (edgeSet G) (canonicalNode G a) (canonicalNode G a') ↔
      G.edge a a' := by
  rw [edgeRel, canonicalNode_code, canonicalNode_code, mem_edgeSet_iff]
  constructor
  · rintro ⟨x, y, hx, hy, hedge⟩
    cases nodeCode_injective hx
    cases nodeCode_injective hy
    exact hedge
  · intro hedge
    exact ⟨a, a', rfl, rfl, hedge⟩

/-- The graph triple of an accessible pointed graph, on the codes of its nodes. -/
noncomputable def canonicalGraph (G : AccessiblePointedGraph.{u}) : ZFSet.{u} :=
  graphTriple (nodeSet G.Node) (edgeSet G) (nodeCode G.point)

/-- The small copy of the point is the point of the canonical triple. -/
theorem canonicalNode_point (G : AccessiblePointedGraph.{u}) :
    canonicalNode G G.point =
      equivShrink.{u} (nodeSet G.Node) ⟨nodeCode G.point, nodeCode_mem G.point⟩ := by
  rw [canonicalNode]
  rfl

/-- The canonical triple pictures the hyperset of the graph. -/
theorem canonicalGraph_pictures (G : AccessiblePointedGraph.{u}) :
    Pictures (mk G) (canonicalGraph G) := by
  refine ⟨nodeSet G.Node, edgeSet G, nodeCode G.point, nodeCode_mem G.point, rfl,
    edgeSet_subset_prod G, ?_⟩
  rw [mk_eq_decorate, ← canonicalNode_point]
  exact decorate_eq_of_bisimilar ((bisimilar_apply
    (f := canonicalNode G)
    (fun a a' hedge => (edgeRel_canonicalNode G a a').mpr hedge)
    (fun a b' hrel => by
      rw [edgeRel, canonicalNode_code] at hrel
      obtain ⟨x, y, hx, hy, hedge⟩ := (mem_edgeSet_iff G).mp hrel
      cases nodeCode_injective hx
      refine ⟨y, hedge, ?_⟩
      apply (equivShrink.{u} (nodeSet G.Node)).symm.injective
      rw [canonicalNode, Equiv.symm_apply_apply]
      apply Subtype.ext
      exact hy)
    G.point).symm)

/-- Every hyperset is pictured by a graph triple of the lower universe. -/
theorem exists_picture (x : HSet.{u}) : ∃ g : ZFSet.{u}, Pictures x g := by
  obtain ⟨G, rfl⟩ := exists_mk x
  exact ⟨canonicalGraph G, canonicalGraph_pictures G⟩

/-- Two hypersets pictured by one triple are equal. -/
theorem pictures_determines {x y : HSet.{u}} {g : ZFSet.{u}}
    (hx : Pictures x g) (hy : Pictures y g) : x = y := by
  obtain ⟨n, e, p, hp, rfl, _, hx⟩ := hx
  obtain ⟨n', e', p', hp', heq, _, hy⟩ := hy
  obtain ⟨rfl, rfl, rfl⟩ := graphTriple_inj.mp heq
  rw [← hx, ← hy]

/-- The code of a hyperset: the set of lifts of the graph triples that picture it. -/
noncomputable def code (x : HSet.{u}) : ZFSet.{u + 1} :=
  ZFSet.sep (fun y => ∃ g : ZFSet.{u}, lift g = y ∧ Pictures x g) carrierCode

/-- Every code is a subset of the carrier of lifted sets. -/
theorem code_subset_carrierCode (x : HSet.{u}) : code x ⊆ carrierCode :=
  ZFSet.sep_subset

/-- A lifted set lies in a code exactly when it is the lift of a picture. -/
theorem mem_code {x : HSet.{u}} {y : ZFSet.{u + 1}} :
    y ∈ code x ↔ ∃ g : ZFSet.{u}, lift g = y ∧ Pictures x g := by
  rw [code, ZFSet.mem_sep]
  constructor
  · exact fun ⟨_, h⟩ => h
  · rintro ⟨g, rfl, hg⟩
    exact ⟨mem_carrierCode.mpr ⟨g, rfl⟩, g, rfl, hg⟩

/-- The lift of the canonical triple lies in the code of the graph's hyperset. -/
theorem lift_canonicalGraph_mem (G : AccessiblePointedGraph.{u}) :
    lift (canonicalGraph G) ∈ code (mk G) :=
  mem_code.mpr ⟨canonicalGraph G, rfl, canonicalGraph_pictures G⟩

/-- Equal codes are codes of equal hypersets. -/
theorem code_injective : Function.Injective (code : HSet.{u} → ZFSet.{u + 1}) := by
  intro x y hxy
  obtain ⟨g, hg⟩ := exists_picture x
  have hmem : lift g ∈ code y := by
    rw [← hxy]
    exact mem_code.mpr ⟨g, rfl, hg⟩
  obtain ⟨g', hg', hy⟩ := mem_code.mp hmem
  have hgg : g' = g := lift_injective hg'
  subst hgg
  exact pictures_determines hg hy

/-- The hyperset read from a set of the next universe, or `∅` when the set is not a code. -/
noncomputable def decodeHSet (y : ZFSet.{u + 1}) : HSet.{u} :=
  @dite (HSet.{u}) (∃ x : HSet.{u}, code x = y) (Classical.propDecidable _)
    (fun h => Classical.choose h) (fun _ => ∅)

/-- Decoding a code returns the hyperset. -/
theorem decodeHSet_code (x : HSet.{u}) : decodeHSet (code x) = x := by
  have hex : ∃ z : HSet.{u}, code z = code x := ⟨x, rfl⟩
  rw [decodeHSet, dif_pos (h := Classical.propDecidable _) hex]
  exact code_injective (Classical.choose_spec hex)

/-- The set of all hyperset codes. -/
noncomputable def hsetCode : ZFSet.{u + 1} :=
  ZFSet.sep (fun y => ∃ x : HSet.{u}, code x = y) (ZFSet.powerset carrierCode)

/-- The codes are the members of `hsetCode`. -/
theorem mem_hsetCode {y : ZFSet.{u + 1}} : y ∈ hsetCode ↔ ∃ x : HSet.{u}, code x = y := by
  rw [hsetCode, ZFSet.mem_sep, ZFSet.mem_powerset]
  constructor
  · exact And.right
  · rintro ⟨x, rfl⟩
    exact ⟨code_subset_carrierCode x, x, rfl⟩

/-- Membership of hypersets, read on sets of the next universe through the decoding. -/
def codeMem (a b : ZFSet.{u + 1}) : Prop :=
  decodeHSet b ∈ decodeHSet a

/-- On codes, `codeMem` is membership of hypersets. -/
theorem codeMem_code {x y : HSet.{u}} : codeMem (code x) (code y) ↔ y ∈ x := by
  rw [codeMem, decodeHSet_code, decodeHSet_code]

/-- The set determined by the code of a well-founded hyperset. -/
noncomputable def decodeWellFounded (y : ZFSet.{u + 1}) : ZFSet.{u} :=
  toZFSet (decodeHSet y)

/-- The code of a well-founded hyperset determines the set. -/
theorem decodeWellFounded_code (a : ZFSet.{u}) :
    decodeWellFounded (code (ofZFSet a)) = a := by
  rw [decodeWellFounded, decodeHSet_code, toZFSet_ofZFSet]

/-- Every code is a subset of `carrierCode`, so `hsetCode` lies in its power set. -/
theorem hsetCode_subset_powerset_carrierCode :
    hsetCode ⊆ ZFSet.powerset carrierCode.{u} :=
  ZFSet.sep_subset

/-- A closed universe that contains `carrierCode` contains the set of all hyperset codes. -/
theorem hsetCode_mem_of_carrierCode_mem {U : ZFSet.{u + 1}}
    (hU : ZFSetUniverseClosure.Closed U) (h : carrierCode.{u} ∈ U) : hsetCode ∈ U :=
  hU.separation_mem (hU.power_mem h) _

/-- The code of `Ω` differs from the code of every well-founded set. -/
theorem code_quineAtom_ne_ofZFSet (a : ZFSet.{u}) :
    code quineAtom.{u} ≠ code (ofZFSet a) :=
  fun h => ofZFSet_ne_quineAtom a (code_injective h).symm

/-- The one-node loop and the two-node cycle have the same code. -/
theorem code_loop_eq_code_twoCycle : code (mk loop.{u}) = code (mk twoCycle.{u}) := by
  rw [mk_loop, mk_twoCycle]

/-- The node set of the one-node loop is the singleton of its point's code. -/
theorem mem_nodeSet_loop {x : ZFSet.{u}} :
    x ∈ nodeSet loop.{u}.Node ↔ x = nodeCode loop.point := by
  constructor
  · intro hx
    rw [nodeSet, ZFSet.mem_range] at hx
    obtain ⟨a, rfl⟩ := hx
    cases a
    rfl
  · rintro rfl
    exact nodeCode_mem _

/-- The two nodes of the two-node cycle have different codes. -/
theorem nodeCode_twoCycle_ne :
    nodeCode (show twoCycle.{u}.Node from ULift.up true) ≠
      nodeCode (show twoCycle.{u}.Node from ULift.up false) :=
  fun h => Bool.noConfusion (congrArg ULift.down (nodeCode_injective h))

/-- The canonical triples of the loop and of the two-node cycle are different sets. -/
theorem canonicalGraph_loop_ne_twoCycle :
    canonicalGraph loop.{u} ≠ canonicalGraph twoCycle.{u} := by
  intro h
  unfold canonicalGraph at h
  obtain ⟨hn, _, _⟩ := graphTriple_inj.mp h
  have htrue : nodeCode (show twoCycle.{u}.Node from ULift.up true) ∈ nodeSet loop.Node := by
    rw [hn]
    exact nodeCode_mem _
  have hfalse : nodeCode (show twoCycle.Node from ULift.up false) ∈ nodeSet loop.Node := by
    rw [hn]
    exact nodeCode_mem _
  rw [mem_nodeSet_loop] at htrue hfalse
  exact nodeCode_twoCycle_ne (htrue.trans hfalse.symm)

end Mettapedia.TypeTheory.MaterialSets.Hypersets
