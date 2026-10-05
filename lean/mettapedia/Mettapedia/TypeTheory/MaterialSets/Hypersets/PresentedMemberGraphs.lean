import Mettapedia.TypeTheory.MaterialSets.Hypersets.PowerClassMembers

/-!
# Constructed graphs below a material bound

A supplied graph determines a graph for every one of its material members.
The construction uses all root occurrences picturing the member, collects
their repointed graphs, and takes union of that singleton range. It never
selects an occurrence. This is local presentation data below an actual graph,
not a section of the quotient map on arbitrary bare hypersets.

Graph constructors for separation, union and Kuratowski pairs preserve the
same graph bound and make these local presentations composable.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.AccessiblePointedGraph

universe u

/-- The two-step children of a presented set present its material union. -/
def unionGraph (G : AccessiblePointedGraph.{u}) : AccessiblePointedGraph.{u} :=
  sup fun path : {path : G.Node × G.Node // G.edge G.point path.1 ∧ G.edge path.1 path.2} =>
    G.repoint path.1.2

theorem mk_unionGraph (G : AccessiblePointedGraph.{u}) :
    HSet.mk (unionGraph G) = HSet.sUnion (HSet.mk G) := rfl

def separationGraph (G : AccessiblePointedGraph.{u}) (predicate : HSet.{u} → Prop) :
    AccessiblePointedGraph.{u} :=
  sup fun occurrence : {occurrence : Occurrence G // predicate occurrence.picture} =>
    G.repoint occurrence.1.1

theorem mk_separationGraph (G : AccessiblePointedGraph.{u}) (predicate : HSet.{u} → Prop) :
    HSet.mk (separationGraph G predicate) = HSet.sep predicate (HSet.mk G) := by
  apply HSet.ext
  intro value
  rw [HSet.mem_sep]
  constructor
  · intro member
    obtain ⟨occurrence, same⟩ := HSet.mem_range.mp member
    have observed := (memberObservation G occurrence.1).2
    change occurrence.1.picture ∈ picture G at observed
    rw [picture_eq_mk] at observed
    rw [HSet.mk_repoint] at same
    exact ⟨same ▸ observed, same ▸ occurrence.2⟩
  · rintro ⟨member, satisfies⟩
    rw [← picture_eq_mk] at member
    obtain ⟨occurrence, same⟩ := mem_picture_iff_occurrence.mp member
    exact HSet.mem_range.mpr ⟨⟨occurrence, same.symm ▸ satisfies⟩,
      (HSet.mk_repoint G occurrence.1).trans same⟩

def singletonGraph (G : AccessiblePointedGraph.{u}) : AccessiblePointedGraph.{u} :=
  sup fun _ : PUnit.{u + 1} => G

theorem mk_singletonGraph (G : AccessiblePointedGraph.{u}) :
    HSet.mk (singletonGraph G) = {HSet.mk G} := by
  apply HSet.ext
  intro value
  exact HSet.mem_range.trans
    ⟨fun ⟨_, same⟩ => HSet.mem_singleton.mpr same.symm,
      fun member => ⟨PUnit.unit, (HSet.mem_singleton.mp member).symm⟩⟩

def pairGraph (G H : AccessiblePointedGraph.{u}) : AccessiblePointedGraph.{u} :=
  sup fun flag : ULift.{u, 0} Bool => if flag.down then G else H

theorem mk_pairGraph (G H : AccessiblePointedGraph.{u}) :
    HSet.mk (pairGraph G H) = {HSet.mk G, HSet.mk H} := by
  apply HSet.ext
  intro value
  rw [HSet.mem_pair]
  constructor
  · intro member
    obtain ⟨⟨flag⟩, same⟩ := HSet.mem_range.mp member
    cases flag with
    | false => exact Or.inr same.symm
    | true => exact Or.inl same.symm
  · rintro (same | same)
    · exact HSet.mem_range.mpr ⟨⟨true⟩, same.symm⟩
    · exact HSet.mem_range.mpr ⟨⟨false⟩, same.symm⟩

def kpairGraph (G H : AccessiblePointedGraph.{u}) : AccessiblePointedGraph.{u} :=
  pairGraph (singletonGraph G) (pairGraph G H)

theorem mk_kpairGraph (G H : AccessiblePointedGraph.{u}) :
    HSet.mk (kpairGraph G H) = HSet.kpair (HSet.mk G) (HSet.mk H) := by
  rw [kpairGraph, mk_pairGraph, mk_singletonGraph, mk_pairGraph]
  rfl

/-- Every occurrence in a member's fibre is retained in the range graph. -/
def memberRangeGraph (G : AccessiblePointedGraph.{u}) (member : PicturedMembers G) :
    AccessiblePointedGraph.{u} :=
  sup fun occurrence : {occurrence : Occurrence G // occurrence ∈ memberFibre G member} =>
    G.repoint occurrence.1.1

theorem mk_memberRangeGraph (G : AccessiblePointedGraph.{u}) (member : PicturedMembers G) :
    HSet.mk (memberRangeGraph G member) = classRange G (memberFibre G member) := rfl

/-- A member is presented by union of the range of all its occurrences. -/
def memberGraph (G : AccessiblePointedGraph.{u}) (member : PicturedMembers G) :
    AccessiblePointedGraph.{u} := unionGraph (memberRangeGraph G member)

theorem mk_memberGraph (G : AccessiblePointedGraph.{u}) (member : PicturedMembers G) :
    HSet.mk (memberGraph G member) = member.1 := by
  rw [memberGraph, mk_unionGraph, mk_memberRangeGraph]
  exact congrArg Subtype.val (classMember_classOfMember G member)

/-- The constructed graph agrees in value with every witnessing occurrence,
while leaving occurrence recovery entirely separate. -/
theorem memberGraph_observation (G : AccessiblePointedGraph.{u}) (occurrence : Occurrence G) :
    HSet.mk (memberGraph G (memberObservation G occurrence)) = HSet.mk (G.repoint occurrence.1) :=
  mk_memberGraph G (memberObservation G occurrence)

theorem duplicate_memberGraphs_same_value :
    HSet.mk (memberGraph twoChildren.{u} (memberObservation twoChildren (twoChildrenOccurrence true))) =
      HSet.mk (memberGraph twoChildren (memberObservation twoChildren (twoChildrenOccurrence false))) :=
  (mk_memberGraph _ _).trans ((congrArg Subtype.val twoChildren_same_member).trans
    (mk_memberGraph _ _).symm)

/-- Local material presentation does not create an edge-sensitive readout
of the observation class. -/
theorem no_occurrence_tag_from_member_class :
    ¬ ∃ readout : PowerMemberClass twoChildren.{u} → Bool,
      ∀ occurrence, readout (classOfOccurrence twoChildren occurrence) = edgeTag occurrence :=
  no_edge_tag_readout

end Mettapedia.TypeTheory.MaterialSets.Hypersets.AccessiblePointedGraph
