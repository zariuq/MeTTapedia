import Mettapedia.TypeTheory.MaterialSets.Hypersets.DependentProduct
import Mettapedia.TypeTheory.MaterialSets.Hypersets.SmallMembers

/-!
# Material dependent products from small section carriers

An explicit equivalence from a `Type u` carrier to all sections of a material
family supplies a small collection of complete function graphs. Their range
is a hyperset, using the supplied presentation, dependent replacement and
Kuratowski pairing. Membership means being the graph of an actual section.
Evaluation uses graph-row separation and union; its inverse laws retain both
the section values and the complete material graphs.

The resulting set agrees extensionally with the powerset-based dependent
product. The small section equivalence is supplied independently to the range
construction. A material realization with explicit occurrence recovery also
supplies a small section model, making this size condition precise.

The distinction between function-space existence and powerset is discussed in
Aczel and Rathjen, *Notes on Constructive Set Theory* (2010), Definition 4.2.6
and Proposition 5.1.4: <https://michrathjen.github.io/book.pdf>.
All sets remain at graph-size level `u`; their member types live at `Type (u + 1)`.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.HSet

universe u

/-- All actual sections of a material family, retaining fibre membership. -/
abbrev Sections (X : HSet.{u}) (B : El (· ∈ ·) X → HSet.{u}) :=
  (a : El (· ∈ ·) X) → El (· ∈ ·) (B a)

/-- Collect function graphs directly from a supplied small section carrier. -/
def sectionProduct (p : Presentation.{u}) (X : HSet.{u})
    (B : El (· ∈ ·) X → HSet.{u}) {α : Type u} (e : α ≃ Sections X B) : HSet.{u} :=
  range fun i => p.graph (functionGraph (dependentReplacement p) kuratowski (e i))

/-- The range has precisely the material graphs of actual dependent sections. -/
theorem mem_sectionProduct_iff {p : Presentation.{u}} {X G : HSet.{u}}
    {B : El (· ∈ ·) X → HSet.{u}} {α : Type u} {e : α ≃ Sections X B} :
    G ∈ sectionProduct p X B e ↔
      ∃ s : Sections X B, functionGraph (dependentReplacement p) kuratowski s = G := by
  rw [sectionProduct, mem_range]
  constructor
  · rintro ⟨i, same⟩
    exact ⟨e i, (p.mk_graph _).symm.trans same⟩
  · rintro ⟨s, same⟩
    exact ⟨e.symm s, (p.mk_graph _).trans
      ((congrArg (functionGraph (dependentReplacement p) kuratowski)
        (e.apply_symm_apply s)).trans same)⟩

/-- Every collected graph has only valid dependent-pair entries. -/
theorem sectionProduct_graph_bound {p : Presentation.{u}} {X G : HSet.{u}}
    {B : El (· ∈ ·) X → HSet.{u}} {α : Type u} {e : α ≃ Sections X B}
    (member : G ∈ sectionProduct p X B e) :
    ∀ z ∈ G, z ∈ sigmaSet (dependentReplacement p) union kuratowski X B := by
  obtain ⟨s, rfl⟩ := mem_sectionProduct_iff.mp member
  intro z hz
  exact (functionGraph_bound (dependentReplacement p) union kuratowski s z ⟨hz⟩).elim id

/-- Every collected graph is total and single-valued in the specified fibres. -/
theorem sectionProduct_isFunctionGraph {p : Presentation.{u}} {X G : HSet.{u}}
    {B : El (· ∈ ·) X → HSet.{u}} {α : Type u} {e : α ≃ Sections X B}
    (member : G ∈ sectionProduct p X B e) : IsFunctionGraph kuratowski X B G := by
  obtain ⟨s, rfl⟩ := mem_sectionProduct_iff.mp member
  exact functionGraph_isFunctionGraph (dependentReplacement p) kuratowski propositional s

/-- Encode an actual section as its material graph in the range product. -/
def sectionGraphMember (p : Presentation.{u}) {X : HSet.{u}}
    {B : El (· ∈ ·) X → HSet.{u}} {α : Type u} (e : α ≃ Sections X B)
    (s : Sections X B) : El (· ∈ ·) (sectionProduct p X B e) :=
  ⟨functionGraph (dependentReplacement p) kuratowski s,
    mem_sectionProduct_iff.mpr ⟨s, rfl⟩⟩

theorem sectionGraphMember_entry (p : Presentation.{u}) {X : HSet.{u}}
    {B : El (· ∈ ·) X → HSet.{u}} {α : Type u} (e : α ≃ Sections X B)
    (s : Sections X B) (a : El (· ∈ ·) X) :
    kpair a.1 (s a).1 ∈ (sectionGraphMember p e s).1 :=
  (dependentReplacement p).mem_image (fun a => kpair a.1 (s a).1) a

/-- Direct graph-row evaluation of a graph in the range product. Its membership
proof uses the established graph law and propositional evidence recovery. -/
def evalSectionGraph (p : Presentation.{u}) {X : HSet.{u}}
    {B : El (· ∈ ·) X → HSet.{u}} {α : Type u} (e : α ≃ Sections X B)
    (g : El (· ∈ ·) (sectionProduct p X B e)) : Sections X B :=
  fun a => ⟨graphValue (dependentReplacement p) union kuratowski separation g.1 a.1,
    recovery.recover (nonempty_mem_graphValue (dependentReplacement p) union kuratowski
      separation recovery extensional (sectionProduct_isFunctionGraph g.2) a)⟩

/-- A known graph entry determines the complete material evaluation value. -/
theorem evalSectionGraph_value_of_entry (p : Presentation.{u}) {X : HSet.{u}}
    {B : El (· ∈ ·) X → HSet.{u}} {α : Type u} (e : α ≃ Sections X B)
    (g : El (· ∈ ·) (sectionProduct p X B e)) (a : El (· ∈ ·) X)
    (b : El (· ∈ ·) (B a)) (entry : kpair a.1 b.1 ∈ g.1) :
    (evalSectionGraph p e g a).1 = b.1 := by
  obtain ⟨b₀, entry₀, unique⟩ := sectionProduct_isFunctionGraph g.2 a
  exact (graphValue_eq_of_witness (dependentReplacement p) union kuratowski separation
    recovery extensional a b₀ entry₀ unique).trans
      ((snd_kpair _ _).symm.trans (unique _ ⟨entry⟩ (fst_kpair _ _))).symm

/-- Evaluating an encoded section preserves its actual fibre members. -/
theorem evalSectionGraph_beta (p : Presentation.{u}) {X : HSet.{u}}
    {B : El (· ∈ ·) X → HSet.{u}} {α : Type u} (e : α ≃ Sections X B)
    (s : Sections X B) (a : El (· ∈ ·) X) :
    evalSectionGraph p e (sectionGraphMember p e s) a = s a := by
  apply El.ext propositional
  exact evalSectionGraph_value_of_entry p e _ a (s a) (sectionGraphMember_entry p e s a)

/-- Re-encoding direct evaluation preserves the complete collected graph. -/
theorem functionGraph_evalSectionGraph (p : Presentation.{u}) {X : HSet.{u}}
    {B : El (· ∈ ·) X → HSet.{u}} {α : Type u} (e : α ≃ Sections X B)
    (g : El (· ∈ ·) (sectionProduct p X B e)) :
    functionGraph (dependentReplacement p) kuratowski (evalSectionGraph p e g) = g.1 := by
  obtain ⟨s, same⟩ := mem_sectionProduct_iff.mp g.2
  have memberEq : g = sectionGraphMember p e s := El.ext propositional same.symm
  rw [memberEq]
  have evaluated : evalSectionGraph p e (sectionGraphMember p e s) = s :=
    funext (evalSectionGraph_beta p e s)
  rw [evaluated]
  rfl

/-- Direct evaluation returns the actual entry of the original graph. -/
theorem evalSectionGraph_entry (p : Presentation.{u}) {X : HSet.{u}}
    {B : El (· ∈ ·) X → HSet.{u}} {α : Type u} (e : α ≃ Sections X B)
    (g : El (· ∈ ·) (sectionProduct p X B e)) (a : El (· ∈ ·) X) :
    kpair a.1 (evalSectionGraph p e g a).1 ∈ g.1 := by
  have entry := (dependentReplacement p).mem_image
    (fun a => kpair a.1 (evalSectionGraph p e g a).1) a
  change kpair a.1 (evalSectionGraph p e g a).1 ∈
    functionGraph (dependentReplacement p) kuratowski (evalSectionGraph p e g) at entry
  rw [functionGraph_evalSectionGraph p e g] at entry
  exact entry

/-- A typed row belongs to a collected graph exactly when it is its evaluation. -/
theorem sectionProduct_entry_iff (p : Presentation.{u}) {X : HSet.{u}}
    {B : El (· ∈ ·) X → HSet.{u}} {α : Type u} (e : α ≃ Sections X B)
    (g : El (· ∈ ·) (sectionProduct p X B e)) (a : El (· ∈ ·) X)
    (b : El (· ∈ ·) (B a)) :
    kpair a.1 b.1 ∈ g.1 ↔ evalSectionGraph p e g a = b := by
  constructor
  · intro entry
    exact El.ext propositional (evalSectionGraph_value_of_entry p e g a b entry)
  · intro same
    have entry := evalSectionGraph_entry p e g a
    rw [same] at entry
    exact entry

/-- Actual material members and complete dependent functions are equivalent;
both directions are constructed without selecting an existential section. -/
def sectionProductEquiv (p : Presentation.{u}) (X : HSet.{u})
    (B : El (· ∈ ·) X → HSet.{u}) {α : Type u} (e : α ≃ Sections X B) :
    El (· ∈ ·) (sectionProduct p X B e) ≃ Sections X B where
  toFun := evalSectionGraph p e
  invFun := sectionGraphMember p e
  left_inv g := El.ext propositional (functionGraph_evalSectionGraph p e g)
  right_inv s := funext (evalSectionGraph_beta p e s)

/-- Small codes are faithfully represented by their complete material graphs. -/
def sectionCodesEquiv (p : Presentation.{u}) (X : HSet.{u})
    (B : El (· ∈ ·) X → HSet.{u}) {α : Type u} (e : α ≃ Sections X B) :
    α ≃ El (· ∈ ·) (sectionProduct p X B e) :=
  e.trans (sectionProductEquiv p X B e).symm

theorem sectionCodesEquiv_value (p : Presentation.{u}) (X : HSet.{u})
    (B : El (· ∈ ·) X → HSet.{u}) {α : Type u} (e : α ≃ Sections X B) (i : α) :
    (sectionCodesEquiv p X B e i).1 =
      functionGraph (dependentReplacement p) kuratowski (e i) := rfl

/-- The direct range construction and the powerset construction contain the
same actual graphs. The range construction itself uses the supplied `e`. -/
theorem sectionProduct_eq_dependentProduct (p : Presentation.{u}) (X : HSet.{u})
    (B : El (· ∈ ·) X → HSet.{u}) {α : Type u} (e : α ≃ Sections X B) :
    sectionProduct p X B e = dependentProduct p X B := by
  apply ext
  intro G
  constructor
  · intro member
    exact mem_dependentProduct_iff.mpr
      ⟨sectionProduct_graph_bound member, sectionProduct_isFunctionGraph member⟩
  · intro member
    let g : El (· ∈ ·) (dependentProduct p X B) := ⟨G, member⟩
    exact mem_sectionProduct_iff.mpr ⟨piSetEquiv p X B g,
      functionGraph_evalGraph (dependentReplacement p) union kuratowski separation power
        recovery extensional g⟩

/-- The resulting material set is independent of the supplied enumeration. -/
theorem sectionProduct_eq_of_models (p : Presentation.{u}) (X : HSet.{u})
    (B : El (· ∈ ·) X → HSet.{u}) {α β : Type u}
    (e : α ≃ Sections X B) (f : β ≃ Sections X B) :
    sectionProduct p X B e = sectionProduct p X B f :=
  ext fun _ => mem_sectionProduct_iff.trans mem_sectionProduct_iff.symm

/-- Any material member realization, with supplied occurrence recovery, gives
a small carrier of complete sections. No powerset product is needed here. -/
def sectionModelOfMemberEquiv (p : Presentation.{u}) (X P : HSet.{u})
    (B : El (· ∈ ·) X → HSet.{u})
    (r : AccessiblePointedGraph.OccurrenceRecovery (p.graph P))
    (d : El (· ∈ ·) P ≃ Sections X B) : MemberModel p P ≃ Sections X B :=
  (memberModelEquiv p P r).trans d

theorem small_sections_of_memberEquiv (p : Presentation.{u}) (X P : HSet.{u})
    (B : El (· ∈ ·) X → HSet.{u})
    (r : AccessiblePointedGraph.OccurrenceRecovery (p.graph P))
    (d : El (· ∈ ·) P ≃ Sections X B) : Small.{u} (Sections X B) :=
  Small.mk' (sectionModelOfMemberEquiv p X P B r d).symm

/-- Inhabiting the direct material product means supplying a complete section. -/
theorem nonempty_sectionProduct_iff (p : Presentation.{u}) (X : HSet.{u})
    (B : El (· ∈ ·) X → HSet.{u}) {α : Type u} (e : α ≃ Sections X B) :
    Nonempty (El (· ∈ ·) (sectionProduct p X B e)) ↔ Nonempty (Sections X B) :=
  ⟨fun ⟨g⟩ => ⟨sectionProductEquiv p X B e g⟩,
    fun ⟨s⟩ => ⟨(sectionProductEquiv p X B e).symm s⟩⟩

theorem sectionProduct_eq_empty_iff (p : Presentation.{u}) (X : HSet.{u})
    (B : El (· ∈ ·) X → HSet.{u}) {α : Type u} (e : α ≃ Sections X B) :
    sectionProduct p X B e = ∅ ↔ ¬ Nonempty (Sections X B) := by
  constructor
  · intro empty ⟨s⟩
    have member := (sectionGraphMember p e s).2
    change functionGraph (dependentReplacement p) kuratowski s ∈ sectionProduct p X B e at member
    rw [empty] at member
    exact notMem_empty _ member
  · intro noSection
    apply eq_empty_iff.mpr
    intro G member
    obtain ⟨s, _⟩ := mem_sectionProduct_iff.mp member
    exact noSection ⟨s⟩

/-- The empty family has one section, with an explicit small carrier. -/
def emptySectionsEquiv (B : El (· ∈ ·) (∅ : HSet.{u}) → HSet.{u}) :
    PUnit.{u + 1} ≃ Sections ∅ B where
  toFun _ a := (notMem_empty a.1 a.2).elim
  invFun _ := PUnit.unit
  left_inv _ := rfl
  right_inv _ := funext fun a => (notMem_empty a.1 a.2).elim

/-- The unique graph over an empty domain is itself empty. -/
theorem functionGraph_empty_domain (p : Presentation.{u})
    (B : El (· ∈ ·) (∅ : HSet.{u}) → HSet.{u}) (s : Sections ∅ B) :
    functionGraph (dependentReplacement p) kuratowski s = ∅ := by
  apply eq_empty_iff.mpr
  intro z member
  obtain ⟨a, _⟩ := (dependentReplacement p).exists_of_mem_image member
  exact notMem_empty a.1 a.2

/-- A direct product over the empty domain consists of the empty graph. -/
theorem sectionProduct_empty_domain (p : Presentation.{u})
    (B : El (· ∈ ·) (∅ : HSet.{u}) → HSet.{u}) {α : Type u}
    (e : α ≃ Sections ∅ B) : sectionProduct p ∅ B e = {∅} := by
  apply ext
  intro G
  rw [mem_sectionProduct_iff, mem_singleton]
  constructor
  · rintro ⟨s, same⟩
    exact same.symm.trans (functionGraph_empty_domain p B s)
  · rintro rfl
    exact ⟨emptySectionsEquiv B PUnit.unit, functionGraph_empty_domain p B _⟩

/-- An empty fibre excludes sections, providing an explicit empty carrier. -/
def emptyFibreSectionsEquiv {X : HSet.{u}} {B : El (· ∈ ·) X → HSet.{u}}
    (a : El (· ∈ ·) X) (empty : B a = ∅) : PEmpty.{u + 1} ≃ Sections X B where
  toFun i := i.elim
  invFun s := (notMem_empty (s a).1 (empty ▸ (s a).2)).elim
  left_inv i := i.elim
  right_inv s := (notMem_empty (s a).1 (empty ▸ (s a).2)).elim

theorem sectionProduct_eq_empty_of_empty_fibre (p : Presentation.{u})
    {X : HSet.{u}} {B : El (· ∈ ·) X → HSet.{u}} {α : Type u}
    (e : α ≃ Sections X B) (a : El (· ∈ ·) X) (empty : B a = ∅) :
    sectionProduct p X B e = ∅ := by
  apply (sectionProduct_eq_empty_iff p X B e).mpr
  rintro ⟨s⟩
  exact notMem_empty (s a).1 (empty ▸ (s a).2)

/-- A nonempty singleton domain with empty fibres has no graphs; the section
carrier is constructed directly as `PEmpty`. -/
theorem sectionProduct_singleton_empty (p : Presentation.{u}) :
    sectionProduct p ({∅} : HSet.{u}) (fun _ => ∅)
      (emptyFibreSectionsEquiv ⟨∅, mem_singleton_self ∅⟩ rfl) = ∅ :=
  sectionProduct_eq_empty_of_empty_fibre p _ ⟨∅, mem_singleton_self ∅⟩ rfl

/-- Singleton fibres over a singleton domain have one section, even when the
two hypersets contain membership cycles. -/
def singletonSectionsEquiv (x y : HSet.{u}) :
    PUnit.{u + 1} ≃ Sections {x} (fun _ => {y}) where
  toFun _ _ := ⟨y, mem_singleton_self y⟩
  invFun _ := PUnit.unit
  left_inv _ := rfl
  right_inv s := by
    funext a
    apply El.ext propositional
    exact (mem_singleton.mp (s a).2).symm

/-- The graph of the unique singleton-family section is a singleton pair set. -/
theorem functionGraph_singleton_domain (p : Presentation.{u}) (x y : HSet.{u})
    (s : Sections {x} (fun _ => {y})) :
    functionGraph (dependentReplacement p) kuratowski s = {kpair x y} := by
  apply ext
  intro z
  constructor
  · intro member
    obtain ⟨a, same⟩ := (dependentReplacement p).exists_of_mem_image member
    have argValue : a.1 = x := mem_singleton.mp a.2
    have resultValue : (s a).1 = y := mem_singleton.mp (s a).2
    exact mem_singleton.mpr (same.symm.trans (congrArg₂ kpair argValue resultValue))
  · intro member
    obtain rfl := mem_singleton.mp member
    let a : El (· ∈ ·) ({x} : HSet.{u}) := ⟨x, mem_singleton_self x⟩
    have resultValue : (s a).1 = y := mem_singleton.mp (s a).2
    have entry := (dependentReplacement p).mem_image (fun a => kpair a.1 (s a).1) a
    have pairEq : kpair a.1 (s a).1 = kpair x y := congrArg₂ kpair rfl resultValue
    exact Eq.mp (congrArg (fun z => z ∈ functionGraph (dependentReplacement p) kuratowski s)
      pairEq) entry

/-- The direct range product is the singleton containing its sole singleton
graph, using independently supplied finite section codes. -/
theorem sectionProduct_singleton_singleton (p : Presentation.{u}) (x y : HSet.{u}) :
    sectionProduct p {x} (fun _ => {y}) (singletonSectionsEquiv x y) =
      {{kpair x y}} := by
  apply ext
  intro G
  rw [mem_sectionProduct_iff, mem_singleton]
  constructor
  · rintro ⟨s, same⟩
    exact same.symm.trans (functionGraph_singleton_domain p x y s)
  · rintro rfl
    exact ⟨singletonSectionsEquiv x y PUnit.unit,
      functionGraph_singleton_domain p x y _⟩

/-- Positive non-well-founded control: a genuine material graph on Quine
members is assembled from one explicit section code. -/
theorem sectionProduct_quine_singleton (p : Presentation.{u}) :
    sectionProduct p {quineAtom.{u}} (fun _ => {quineAtom})
      (singletonSectionsEquiv quineAtom quineAtom) = {{kpair quineAtom quineAtom}} :=
  sectionProduct_singleton_singleton p quineAtom quineAtom

theorem evalSectionGraph_quine_value (p : Presentation.{u})
    (a : El (· ∈ ·) ({quineAtom} : HSet.{u})) :
    let e := singletonSectionsEquiv quineAtom quineAtom
    (evalSectionGraph p e (sectionGraphMember p e (e PUnit.unit)) a).1 = quineAtom := by
  exact congrArg PSigma.fst (evalSectionGraph_beta p _ _ a)

end Mettapedia.TypeTheory.MaterialSets.Hypersets.HSet
