import Mettapedia.SetTheory.Profiles.ProfileGraphReadoutSubstitution
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphCurrentMaterial
import Mettapedia.SetTheory.CarveOuts.WellFoundedReadout

/-!
# Current hyperset observations and the partial Foundation reading

Full future material equality has a sound current HSet observation. Its
current-picture kernel is ordinary graph bisimilarity, a weaker contract.
This operation is stage-indexed: it is not a map to a constant HSet model.

The Foundation domain requires well-founded current observations at every
future. Its ZFSet decoding preserves and reflects current membership and
equality on that domain. It does not reflect full future equality from one
current picture. Cyclic values are outside the domain, rather than mapped
to an empty value by this partial reading.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Profiles.ProfileGraphReadout

open CategoryTheory
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open ContextualGraphDiagrams ContextualRealizedGraphs

universe u
variable (D : Type u) [Category.{u} D]

def currentObservation {point : D} : Material D point → HSet.{u} :=
  Quotient.lift (fun value => HSet.mk (picture D value)) (fun _ _ ⟨proof⟩ =>
    ContextualGraphCurrentMaterial.material_equality proof)

theorem currentObservation_readout {point : D} (value : Value D point) :
    currentObservation D (readout D value) = HSet.mk (picture D value) := rfl

theorem currentObservation_kernel {point : D} (first second : Value D point) :
    currentObservation D (readout D first) = currentObservation D (readout D second) ↔
      picture D first ≈ picture D second := HSet.mk_eq_mk_iff

theorem currentObservation_member {point : D} {child parent : Material D point}
    (available : member D child parent) :
    currentObservation D child ∈ currentObservation D parent := by
  induction child using Quotient.inductionOn with
  | h child =>
    induction parent using Quotient.inductionOn with
    | h parent =>
      obtain ⟨proof⟩ := available
      exact ContextualGraphCurrentMaterial.material_membership proof

abbrev FoundationDomain (point : D) : Type (u+1) :=
  {value : Material D point //
    ∀ (target : D) (arrival : point ⟶ target),
      (currentObservation D (transport D arrival value)).WF}

theorem foundation_current_wf {point : D} (value : FoundationDomain D point) :
    (currentObservation D value.val).WF := by
  have available := value.property point (𝟙 point)
  simpa only [transport_identity] using available

def foundationTransport {first second : D} (arrival : first ⟶ second)
    (value : FoundationDomain D first) : FoundationDomain D second :=
  ⟨transport D arrival value.val, fun target later => by
    rw [← transport_composition]
    exact value.property target (arrival ≫ later)⟩

def foundationReadout {point : D} (value : FoundationDomain D point) : ZFSet.{u} :=
  HSet.toZFSet (currentObservation D value.val)

theorem foundationReadout_embedding {point : D} (value : FoundationDomain D point) :
    HSet.ofZFSet (foundationReadout D value) = currentObservation D value.val :=
  HSet.ofZFSet_toZFSet_of_wf (foundation_current_wf D value)

theorem foundationReadout_eq_iff {point : D} (first second : FoundationDomain D point) :
    foundationReadout D first = foundationReadout D second ↔
      currentObservation D first.val = currentObservation D second.val := by
  constructor
  · intro same
    exact (foundationReadout_embedding D first).symm.trans
      ((congrArg HSet.ofZFSet same).trans (foundationReadout_embedding D second))
  · exact congrArg HSet.toZFSet

theorem foundationReadout_mem_iff {point : D} (child parent : FoundationDomain D point) :
    foundationReadout D child ∈ foundationReadout D parent ↔
      currentObservation D child.val ∈ currentObservation D parent.val :=
  Mettapedia.SetTheory.CarveOuts.WellFoundedReadout.mem_iff_of_wf_left
    (foundation_current_wf D child)

theorem foundationReadout_preserves_member {point : D}
    {child parent : FoundationDomain D point} (available : member D child.val parent.val) :
    foundationReadout D child ∈ foundationReadout D parent :=
  (foundationReadout_mem_iff D child parent).mpr (currentObservation_member D available)

section Substitution

variable {D} {E : Type u} [Category.{u} E]

theorem currentObservation_reindex (change : E ⥤ D) (point : E)
    (value : Material D (change.obj point)) :
    currentObservation E (reindexMaterial change point value) = currentObservation D value := by
  induction value using Quotient.inductionOn with
  | h value => rfl

def reindexFoundation (change : E ⥤ D) (point : E)
    (value : FoundationDomain D (change.obj point)) : FoundationDomain E point :=
  ⟨reindexMaterial change point value.val, fun target arrival => by
    rw [reindexMaterial_transport, currentObservation_reindex]
    exact value.property (change.obj target) (change.map arrival)⟩

theorem foundationReadout_reindex (change : E ⥤ D) (point : E)
    (value : FoundationDomain D (change.obj point)) :
    foundationReadout E (reindexFoundation change point value) = foundationReadout D value :=
  congrArg HSet.toZFSet (currentObservation_reindex change point value.val)

end Substitution

end Mettapedia.SetTheory.Profiles.ProfileGraphReadout
