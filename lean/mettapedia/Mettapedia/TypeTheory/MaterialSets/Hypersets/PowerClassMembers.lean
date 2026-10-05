import Mettapedia.TypeTheory.MaterialSets.Hypersets.FamilyDescent
import Mettapedia.TypeTheory.MaterialSets.Hypersets.NoUniversalSet
import Mathlib.Logic.Small.Defs

/-!
# Small material-member carriers without occurrence selection

A member class is a proposition-valued subset of root occurrences, with the
property that it is one nonempty fibre of material observation. Its material
value is constructed as the union of the range of all its re-pointed graphs.
That range is a singleton. This supplies an actual decoder and inverse without
selecting an occurrence from a membership proposition.

The construction uses the full proposition-valued subset type of the small
occurrence carrier and material union. It is a construction in this hyperset
model, not a smallness theorem for exponentiation-only foundations. A bare
hyperset has small members propositionally; a uniform chosen graph carrier
for a family remains separate presentation data.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets

universe u

private def piBaseEquiv {α β : Type*} (base : α ≃ β) (family : β → Sort*) :
    (∀ a, family (base a)) ≃ (∀ b, family b) where
  toFun term b := cast (congrArg family (base.apply_symm_apply b)) (term (base.symm b))
  invFun term a := term (base a)
  left_inv term := by
    funext a
    exact eq_of_heq ((cast_heq _ _).trans (congr_arg_heq term (base.symm_apply_apply a)))
  right_inv term := by
    funext b
    exact eq_of_heq ((cast_heq _ _).trans (congr_arg_heq term (base.apply_symm_apply b)))

private theorem piBaseEquiv_apply {α β : Type*} (base : α ≃ β) (family : β → Sort*)
    (term : ∀ a, family (base a)) (a : α) :
    piBaseEquiv base family term (base a) = term a :=
  eq_of_heq ((cast_heq _ _).trans (congr_arg_heq term (base.symm_apply_apply a)))

private def sectionCongr {α β : Type*} {family : α → Sort*} {observed : β → Sort*}
    (base : α ≃ β) (fibres : ∀ a, family a ≃ observed (base a)) :
    (∀ a, family a) ≃ (∀ b, observed b) :=
  (Equiv.piCongrRight fibres).trans (piBaseEquiv base observed)

private theorem sectionCongr_apply {α β : Type*} {family : α → Sort*} {observed : β → Sort*}
    (base : α ≃ β) (fibres : ∀ a, family a ≃ observed (base a))
    (term : ∀ a, family a) (a : α) :
    sectionCongr base fibres term (base a) = fibres a (term a) :=
  piBaseEquiv_apply base observed (fun a => fibres a (term a)) a

private def sigmaBaseEquiv {α β : Type*} (base : α ≃ β) (family : β → Type*) :
    (Σ a, family (base a)) ≃ (Σ b, family b) where
  toFun value := ⟨base value.1, value.2⟩
  invFun value :=
    ⟨base.symm value.1, cast (congrArg family (base.apply_symm_apply value.1).symm) value.2⟩
  left_inv value := Sigma.ext (base.symm_apply_apply value.1) (cast_heq _ _)
  right_inv value := Sigma.ext (base.apply_symm_apply value.1) (cast_heq _ _)

private def sigmaFibreEquiv {α : Type*} {first second : α → Type*}
    (fibres : ∀ a, first a ≃ second a) : Sigma first ≃ Sigma second where
  toFun value := ⟨value.1, fibres value.1 value.2⟩
  invFun value := ⟨value.1, (fibres value.1).symm value.2⟩
  left_inv value := congrArg (Sigma.mk value.1) ((fibres value.1).symm_apply_apply value.2)
  right_inv value := congrArg (Sigma.mk value.1) ((fibres value.1).apply_symm_apply value.2)

private def sumCongr {α β : Type*} {family : α → Type*} {observed : β → Type*}
    (base : α ≃ β) (fibres : ∀ a, family a ≃ observed (base a)) :
    Sigma family ≃ Sigma observed :=
  (sigmaFibreEquiv fibres).trans (sigmaBaseEquiv base observed)

namespace AccessiblePointedGraph

/-- All occurrences of one material member, retaining no selected witness. -/
def memberFibre (G : AccessiblePointedGraph.{u}) (member : PicturedMembers G) :
    Set (Occurrence G) :=
  {occurrence | memberObservation G occurrence = member}

/-- A nonempty material-observation fibre. The carrier is at the graph's small
universe because it is a subtype of the full proposition-valued subset type. -/
def PowerMemberClass (G : AccessiblePointedGraph.{u}) : Type u :=
  {predicate : Set (Occurrence G) //
    ∃ occurrence, predicate = memberFibre G (memberObservation G occurrence)}

def classOfOccurrence (G : AccessiblePointedGraph.{u}) (occurrence : Occurrence G) :
    PowerMemberClass G :=
  ⟨memberFibre G (memberObservation G occurrence), occurrence, rfl⟩

/-- The graph-family range of every occurrence satisfying a class predicate. -/
def classRange (G : AccessiblePointedGraph.{u}) (predicate : Set (Occurrence G)) : HSet.{u} :=
  HSet.range (fun occurrence : {occurrence // occurrence ∈ predicate} =>
    G.repoint occurrence.1.1)

/-- A decoder defined on the entire subset carrier. Its restriction to genuine
nonempty member classes is the desired member value. -/
def classValue (G : AccessiblePointedGraph.{u}) (predicate : Set (Occurrence G)) : HSet.{u} :=
  HSet.sUnion (classRange G predicate)

theorem classRange_fibre (G : AccessiblePointedGraph.{u}) (occurrence : Occurrence G) :
    classRange G (memberFibre G (memberObservation G occurrence)) = {occurrence.picture} := by
  apply HSet.ext
  intro value
  constructor
  · intro member
    obtain ⟨witness, same⟩ := HSet.mem_range.mp member
    have observed : witness.1.picture = occurrence.picture :=
      congrArg Subtype.val witness.2
    exact HSet.mem_singleton.mpr (same.symm.trans observed)
  · intro member
    have same := HSet.mem_singleton.mp member
    apply HSet.mem_range.mpr
    exact ⟨⟨occurrence, rfl⟩, same.symm⟩

theorem classValue_fibre (G : AccessiblePointedGraph.{u}) (occurrence : Occurrence G) :
    classValue G (memberFibre G (memberObservation G occurrence)) = occurrence.picture := by
  rw [classValue, classRange_fibre, HSet.sUnion_singleton]

theorem classValue_mem (G : AccessiblePointedGraph.{u}) (memberClass : PowerMemberClass G) :
    classValue G memberClass.1 ∈ picture G := by
  obtain ⟨occurrence, same⟩ := memberClass.2
  rw [same, classValue_fibre]
  exact (memberObservation G occurrence).2

/-- Decode the class using material operations and retain its membership fact. -/
def classMember (G : AccessiblePointedGraph.{u}) (memberClass : PowerMemberClass G) :
    PicturedMembers G :=
  ⟨classValue G memberClass.1, classValue_mem G memberClass⟩

/-- Encode a material member by its fibre predicate. Existence of an occurrence
is used only to prove that this predicate is a genuine nonempty class. -/
def classOfMember (G : AccessiblePointedGraph.{u}) (member : PicturedMembers G) :
    PowerMemberClass G :=
  ⟨memberFibre G member, by
    obtain ⟨occurrence, same⟩ := memberObservation_surjective G member
    exact ⟨occurrence, congrArg (memberFibre G) same.symm⟩⟩

@[simp] theorem classMember_classOfOccurrence (G : AccessiblePointedGraph.{u})
    (occurrence : Occurrence G) :
    classMember G (classOfOccurrence G occurrence) = memberObservation G occurrence :=
  Subtype.ext (classValue_fibre G occurrence)

@[simp] theorem classOfMember_observation (G : AccessiblePointedGraph.{u})
    (occurrence : Occurrence G) :
    classOfMember G (memberObservation G occurrence) = classOfOccurrence G occurrence := rfl

@[simp] theorem classMember_classOfMember (G : AccessiblePointedGraph.{u})
    (member : PicturedMembers G) : classMember G (classOfMember G member) = member := by
  obtain ⟨occurrence, same⟩ := memberObservation_surjective G member
  rw [← same, classOfMember_observation, classMember_classOfOccurrence]

@[simp] theorem classOfMember_classMember (G : AccessiblePointedGraph.{u})
    (memberClass : PowerMemberClass G) : classOfMember G (classMember G memberClass) = memberClass := by
  apply Subtype.ext
  obtain ⟨occurrence, same⟩ := memberClass.2
  have memberSame : classMember G memberClass = memberObservation G occurrence := by
    apply Subtype.ext
    change classValue G memberClass.1 = occurrence.picture
    rw [same, classValue_fibre]
  change memberFibre G (classMember G memberClass) = memberClass.1
  rw [memberSame, same]

/-- Both inverse functions are actual constructions. No quotient representative
or occurrence is recovered from the input membership proposition. -/
def powerMemberEquiv (G : AccessiblePointedGraph.{u}) :
    PowerMemberClass G ≃ PicturedMembers G where
  toFun := classMember G
  invFun := classOfMember G
  left_inv := classOfMember_classMember G
  right_inv := classMember_classOfMember G

@[simp] theorem powerMemberEquiv_occurrence (G : AccessiblePointedGraph.{u})
    (occurrence : Occurrence G) :
    powerMemberEquiv G (classOfOccurrence G occurrence) = memberObservation G occurrence :=
  classMember_classOfOccurrence G occurrence

theorem classOfOccurrence_eq_iff (G : AccessiblePointedGraph.{u}) (left right : Occurrence G) :
    classOfOccurrence G left = classOfOccurrence G right ↔
      memberObservation G left = memberObservation G right := by
  constructor
  · intro same
    have members := congrArg (classMember G) same
    simpa only [classMember_classOfOccurrence] using members
  · intro same
    exact Subtype.ext (congrArg (memberFibre G) same)

theorem classOfOccurrence_surjective (G : AccessiblePointedGraph.{u}) :
    Function.Surjective (classOfOccurrence G) := by
  intro memberClass
  obtain ⟨occurrence, same⟩ := memberClass.2
  exact ⟨occurrence, Subtype.ext same.symm⟩

/-- Material membership evidence is propositional; this comparison does not
identify proof-relevant graph occurrences. -/
def powerElEquiv (G : AccessiblePointedGraph.{u}) :
    PowerMemberClass G ≃ El (· ∈ ·) (picture G) where
  toFun memberClass := ⟨classValue G memberClass.1, classValue_mem G memberClass⟩
  invFun member := classOfMember G ⟨member.1, member.2⟩
  left_inv := classOfMember_classMember G
  right_inv member := by
    have same := classMember_classOfMember G ⟨member.1, member.2⟩
    exact PSigma.ext (congrArg Subtype.val same) (proof_irrel_heq _ _)

theorem small_members_picture (G : AccessiblePointedGraph.{u}) :
    Small.{u} (El (· ∈ ·) (picture G)) :=
  Small.mk' (powerElEquiv G).symm

/-- This carrier models only members of the fixed picture, never the whole
ambient hyperset type. Russell's separated set supplies the missing value. -/
theorem classValue_not_surjective (G : AccessiblePointedGraph.{u}) :
    ¬ Function.Surjective (fun memberClass : PowerMemberClass G => classValue G memberClass.1) := by
  intro onto
  obtain ⟨memberClass, same⟩ := onto (HSet.russell (picture G))
  exact HSet.russell_notMem (picture G) (same ▸ classValue_mem G memberClass)

theorem duplicated_occurrences_one_class :
    classOfOccurrence twoChildren.{u} (twoChildrenOccurrence true) =
      classOfOccurrence twoChildren (twoChildrenOccurrence false) := by
  apply Subtype.ext
  exact congrArg (memberFibre twoChildren) twoChildren_same_member

theorem no_edge_tag_readout :
    ¬ ∃ readout : PowerMemberClass twoChildren.{u} → Bool,
      ∀ occurrence, readout (classOfOccurrence twoChildren occurrence) = edgeTag occurrence := by
  rintro ⟨readout, reflects⟩
  have same := congrArg readout duplicated_occurrences_one_class
  rw [reflects, reflects, edgeTag_twoChildrenOccurrence, edgeTag_twoChildrenOccurrence] at same
  exact Bool.noConfusion same

/-- The empty presentation has no member class; nonemptiness in the definition
is semantic and prevents an empty subset from masquerading as a member. -/
theorem empty_no_class : ¬ Nonempty (PowerMemberClass empty.{u}) := by
  rintro ⟨memberClass⟩
  have member := classValue_mem empty memberClass
  rw [picture_eq_mk, HSet.mk_empty] at member
  exact HSet.notMem_empty _ member

/-! ## Actual graph-valued dependent family carriers -/

/-- A small fibre carrier for a supplied graph-valued family. -/
abbrev PowerGraphFamily (G : AccessiblePointedGraph.{u})
    (family : PicturedMembers G → AccessiblePointedGraph.{u}) : PowerMemberClass G → Type u :=
  fun memberClass => PowerMemberClass (family (powerMemberEquiv G memberClass))

abbrev GraphSectionModel (G : AccessiblePointedGraph.{u})
    (family : PicturedMembers G → AccessiblePointedGraph.{u}) : Type u :=
  ∀ memberClass, PowerGraphFamily G family memberClass

abbrev GraphSumModel (G : AccessiblePointedGraph.{u})
    (family : PicturedMembers G → AccessiblePointedGraph.{u}) : Type u :=
  Σ memberClass, PowerGraphFamily G family memberClass

/-- The section carrier is constructed from the independent member-class
carriers. It does not assume an existing material function-graph product. -/
def graphSectionEquiv (G : AccessiblePointedGraph.{u})
    (family : PicturedMembers G → AccessiblePointedGraph.{u}) :
    GraphSectionModel G family ≃ (∀ member, PicturedMembers (family member)) :=
  sectionCongr (powerMemberEquiv G) (fun memberClass =>
    powerMemberEquiv (family (powerMemberEquiv G memberClass)))

theorem graphSectionEquiv_eval (G : AccessiblePointedGraph.{u})
    (family : PicturedMembers G → AccessiblePointedGraph.{u})
    (term : GraphSectionModel G family) (memberClass : PowerMemberClass G) :
    graphSectionEquiv G family term (powerMemberEquiv G memberClass) =
      powerMemberEquiv (family (powerMemberEquiv G memberClass)) (term memberClass) :=
  sectionCongr_apply _ _ term memberClass

def graphSumEquiv (G : AccessiblePointedGraph.{u})
    (family : PicturedMembers G → AccessiblePointedGraph.{u}) :
    GraphSumModel G family ≃ (Σ member, PicturedMembers (family member)) :=
  sumCongr (powerMemberEquiv G) (fun memberClass =>
    powerMemberEquiv (family (powerMemberEquiv G memberClass)))

theorem graphSumEquiv_mk (G : AccessiblePointedGraph.{u})
    (family : PicturedMembers G → AccessiblePointedGraph.{u})
    (memberClass : PowerMemberClass G) (value : PowerGraphFamily G family memberClass) :
    graphSumEquiv G family ⟨memberClass, value⟩ =
      ⟨powerMemberEquiv G memberClass,
        powerMemberEquiv (family (powerMemberEquiv G memberClass)) value⟩ := rfl

theorem small_graph_sections (G : AccessiblePointedGraph.{u})
    (family : PicturedMembers G → AccessiblePointedGraph.{u}) :
    Small.{u} (∀ member, PicturedMembers (family member)) :=
  Small.mk' (graphSectionEquiv G family).symm

theorem small_graph_sum (G : AccessiblePointedGraph.{u})
    (family : PicturedMembers G → AccessiblePointedGraph.{u}) :
    Small.{u} (Σ member, PicturedMembers (family member)) :=
  Small.mk' (graphSumEquiv G family).symm

theorem empty_fibre_no_section :
    ¬ Nonempty (GraphSectionModel twoChildren.{u} (fun _ => empty.{u})) := by
  rintro ⟨term⟩
  exact empty_no_class ⟨term (classOfOccurrence twoChildren (twoChildrenOccurrence true))⟩

def loopOccurrence : Occurrence HSet.loop.{u} := ⟨HSet.loop.point, trivial⟩

/-- A nonempty dependent-function client with a genuinely non-well-founded
material value, constructed entirely from concrete graphs. -/
def quineSection : GraphSectionModel twoChildren.{u} (fun _ => HSet.loop.{u}) :=
  fun _ => classOfOccurrence HSet.loop loopOccurrence

theorem quineSection_value :
    (graphSectionEquiv twoChildren.{u} (fun _ => HSet.loop.{u}) quineSection
      (memberObservation twoChildren (twoChildrenOccurrence true))).1 = HSet.quineAtom := by
  have evaluation := graphSectionEquiv_eval twoChildren (fun _ => HSet.loop) quineSection
    (classOfOccurrence twoChildren (twoChildrenOccurrence true))
  rw [powerMemberEquiv_occurrence] at evaluation
  have valueSame := congrArg Subtype.val evaluation
  simp only [quineSection, powerMemberEquiv_occurrence] at valueSame
  exact valueSame.trans (HSet.decorate_loop _)

theorem quineSection_not_wellFounded :
    ¬ (graphSectionEquiv twoChildren.{u} (fun _ => HSet.loop.{u}) quineSection
      (memberObservation twoChildren (twoChildrenOccurrence true))).1.WF :=
  fun wellFounded => HSet.not_wf_quineAtom (quineSection_value ▸ wellFounded)

end AccessiblePointedGraph

namespace HSet

open AccessiblePointedGraph

/-- An unconditional smallness proposition. The graph witness is eliminated
only into `Small`, a proposition; no global chosen graph or Shrink is produced. -/
theorem small_el_constructive (X : HSet.{u}) : Small.{u} (El (· ∈ ·) X) := by
  obtain ⟨G, same⟩ := exists_mk X
  have pictureSame : picture G = X := (picture_eq_mk G).trans same
  exact pictureSame ▸ small_members_picture G

/-- A supplied presentation makes the small carrier explicit for a whole
family. It supplies graphs, not selected member occurrences. -/
abbrev PowerMemberModel (p : Presentation.{u}) (X : HSet.{u}) : Type u :=
  PowerMemberClass (p.graph X)

def powerMemberModelEquiv (p : Presentation.{u}) (X : HSet.{u}) :
    PowerMemberModel p X ≃ El (· ∈ ·) X :=
  (powerElEquiv (p.graph X)).trans
    (Mettapedia.TypeTheory.DependentFamilySectionDescent.equalityEquiv
      (congrArg (fun Y => El (· ∈ ·) Y) ((picture_eq_mk _).trans (p.mk_graph X))))

private theorem memberEqualityEquiv_value {X Y : HSet.{u}} (same : X = Y)
    (member : El (· ∈ ·) X) :
    (Mettapedia.TypeTheory.DependentFamilySectionDescent.equalityEquiv
      (congrArg (fun Z => El (· ∈ ·) Z) same) member).1 = member.1 := by
  cases same
  rfl

/-- Presentation transport retains the actual material value decoded from the
class. Only its containing-set membership proof is transported. -/
theorem powerMemberModelEquiv_value (p : Presentation.{u}) (X : HSet.{u})
    (memberClass : PowerMemberModel p X) :
    (powerMemberModelEquiv p X memberClass).1 = classValue (p.graph X) memberClass.1 := by
  exact memberEqualityEquiv_value ((picture_eq_mk _).trans (p.mk_graph X))
    (powerElEquiv (p.graph X) memberClass)

abbrev PowerReducedFamily (p : Presentation.{u}) (X : HSet.{u})
    (family : El (· ∈ ·) X → HSet.{u}) : PowerMemberModel p X → Type u :=
  fun memberClass => PowerMemberModel p (family (powerMemberModelEquiv p X memberClass))

/-- An explicit small section carrier built from independent member classes. -/
abbrev PowerSectionModel (p : Presentation.{u}) (X : HSet.{u})
    (family : El (· ∈ ·) X → HSet.{u}) : Type u :=
  ∀ memberClass, PowerReducedFamily p X family memberClass

abbrev PowerSumModel (p : Presentation.{u}) (X : HSet.{u})
    (family : El (· ∈ ·) X → HSet.{u}) : Type u :=
  Σ memberClass, PowerReducedFamily p X family memberClass

def powerSectionEquiv (p : Presentation.{u}) (X : HSet.{u})
    (family : El (· ∈ ·) X → HSet.{u}) :
    PowerSectionModel p X family ≃ (∀ member, El (· ∈ ·) (family member)) :=
  sectionCongr (powerMemberModelEquiv p X) (fun memberClass =>
    powerMemberModelEquiv p (family (powerMemberModelEquiv p X memberClass)))

theorem powerSectionEquiv_eval (p : Presentation.{u}) (X : HSet.{u})
    (family : El (· ∈ ·) X → HSet.{u}) (term : PowerSectionModel p X family)
    (memberClass : PowerMemberModel p X) :
    powerSectionEquiv p X family term (powerMemberModelEquiv p X memberClass) =
      powerMemberModelEquiv p (family (powerMemberModelEquiv p X memberClass)) (term memberClass) :=
  sectionCongr_apply _ _ term memberClass

def powerSumEquiv (p : Presentation.{u}) (X : HSet.{u})
    (family : El (· ∈ ·) X → HSet.{u}) :
    PowerSumModel p X family ≃ (Σ member, El (· ∈ ·) (family member)) :=
  sumCongr (powerMemberModelEquiv p X) (fun memberClass =>
    powerMemberModelEquiv p (family (powerMemberModelEquiv p X memberClass)))

theorem powerSumEquiv_mk (p : Presentation.{u}) (X : HSet.{u})
    (family : El (· ∈ ·) X → HSet.{u}) (memberClass : PowerMemberModel p X)
    (value : PowerReducedFamily p X family memberClass) :
    powerSumEquiv p X family ⟨memberClass, value⟩ =
      ⟨powerMemberModelEquiv p X memberClass,
        powerMemberModelEquiv p (family (powerMemberModelEquiv p X memberClass)) value⟩ := rfl

theorem small_sections_presented (p : Presentation.{u}) (X : HSet.{u})
    (family : El (· ∈ ·) X → HSet.{u}) :
    Small.{u} (∀ member, El (· ∈ ·) (family member)) :=
  Small.mk' (powerSectionEquiv p X family).symm

theorem small_sum_presented (p : Presentation.{u}) (X : HSet.{u})
    (family : El (· ∈ ·) X → HSet.{u}) :
    Small.{u} (Σ member, El (· ∈ ·) (family member)) :=
  Small.mk' (powerSumEquiv p X family).symm

end HSet

end Mettapedia.TypeTheory.MaterialSets.Hypersets
