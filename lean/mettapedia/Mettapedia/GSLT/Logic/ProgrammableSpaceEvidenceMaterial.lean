import Mettapedia.GSLT.Logic.ProgrammableSpaceEvidenceBatch
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualArgumentCodings

/-!
# Faithful material readings of retained derivation trees

Constructor tags, authored rule positions and the complete ordered premise
spine are material data. The graph construction is recursive in the actual
finite derivation. Its equality kernel is literal receipt equality, including
input origins and distinct occurrences of equal rules. The separate fact
reading has the coarser conclusion kernel.

Both source carriers and graph nodes live at the stated bound `u`. Faithful
atom and origin dictionaries are explicit data; no graph presentation is
selected from an existential claim.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ProgrammableSpaceEvidence.Material

attribute [local instance] Finite.membership

open Mettapedia.TypeTheory.MaterialSets.Hypersets

universe u
variable {Atom Origin : Type u} {source : Source Atom Origin}

/-- Ordered finite graph spines, keeping repeated children. -/
def spine : List AccessiblePointedGraph.{u} → AccessiblePointedGraph.{u}
  | [] => AccessiblePointedGraph.empty
  | first :: rest => AccessiblePointedGraph.kpairGraph first (spine rest)

private theorem pair_ne_empty (first second : HSet.{u}) : HSet.kpair first second ≠ ∅ := by
  intro same
  have member : ({first} : HSet.{u}) ∈ HSet.kpair first second :=
    HSet.mem_pair.mpr (Or.inl rfl)
  rw [same] at member
  exact HSet.notMem_empty _ member

theorem spine_kernel (first second : List AccessiblePointedGraph.{u}) :
    HSet.mk (spine first) = HSet.mk (spine second) ↔
      first.map HSet.mk = second.map HSet.mk := by
  induction first generalizing second with
  | nil =>
    cases second with
    | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
    | cons head tail =>
      constructor
      · intro same
        change HSet.mk AccessiblePointedGraph.empty =
          HSet.mk (AccessiblePointedGraph.kpairGraph head (spine tail)) at same
        rw [HSet.mk_empty, AccessiblePointedGraph.mk_kpairGraph] at same
        exact (pair_ne_empty _ _ same.symm).elim
      · intro same
        cases same
  | cons head tail induction =>
    cases second with
    | nil =>
      constructor
      · intro same
        change HSet.mk (AccessiblePointedGraph.kpairGraph head (spine tail)) =
          HSet.mk AccessiblePointedGraph.empty at same
        rw [AccessiblePointedGraph.mk_kpairGraph, HSet.mk_empty] at same
        exact (pair_ne_empty _ _ same).elim
      · intro same
        cases same
    | cons other rest =>
      change HSet.mk (AccessiblePointedGraph.kpairGraph head (spine tail)) =
          HSet.mk (AccessiblePointedGraph.kpairGraph other (spine rest)) ↔ _
      rw [AccessiblePointedGraph.mk_kpairGraph, AccessiblePointedGraph.mk_kpairGraph,
        HSet.kpair_inj, List.map_cons, List.map_cons, List.cons.injEq, induction]

/-- The complete structural tree, including the authored rule position. -/
def treeGraph (origins : ArgumentCoding Origin) : {atom : Atom} →
    Derivation source atom → AccessiblePointedGraph.{u}
  | _, .input origin => AccessiblePointedGraph.kpairGraph (OutcomeLabels.chainGraph 0)
      (origins.graph origin)
  | _, .rule index premises => AccessiblePointedGraph.kpairGraph (OutcomeLabels.chainGraph 1)
      (AccessiblePointedGraph.kpairGraph (OutcomeLabels.chainGraph index.val)
        (spine (List.ofFn fun position => treeGraph origins (premises position))))

private theorem chain_reflect {first second : Nat}
    (same : HSet.mk (OutcomeLabels.chainGraph.{u} first) =
      HSet.mk (OutcomeLabels.chainGraph.{u} second)) : first = second := by
  rw [OutcomeLabels.mk_chainGraph, OutcomeLabels.mk_chainGraph] at same
  exact OutcomeLabels.chainValue_injective same

theorem treeGraph_reflect (origins : ArgumentCoding Origin) {firstAtom secondAtom : Atom}
    (first : Derivation source firstAtom) (second : Derivation source secondAtom)
    (same : HSet.mk (treeGraph origins first) = HSet.mk (treeGraph origins second)) :
    HEq first second := by
  induction first generalizing secondAtom with
  | input origin =>
    cases second with
    | input other =>
      simp only [treeGraph, AccessiblePointedGraph.mk_kpairGraph, HSet.kpair_inj] at same
      have identical := origins.injective same.2
      cases identical
      rfl
    | rule index premises =>
      simp only [treeGraph, AccessiblePointedGraph.mk_kpairGraph] at same
      have impossible := chain_reflect (HSet.kpair_inj.mp same).1
      cases impossible
  | rule index premises induction =>
    cases second with
    | input origin =>
      simp only [treeGraph, AccessiblePointedGraph.mk_kpairGraph] at same
      have impossible := chain_reflect (HSet.kpair_inj.mp same).1
      cases impossible
    | rule other children =>
      simp only [treeGraph, AccessiblePointedGraph.mk_kpairGraph] at same
      have bodies := (HSet.kpair_inj.mp same).2
      have indices : index = other := Fin.ext (chain_reflect (HSet.kpair_inj.mp bodies).1)
      cases indices
      have lists := (spine_kernel _ _).mp (HSet.kpair_inj.mp bodies).2
      have components := List.ofFn_injective (by simpa only [List.map_ofFn] using lists)
      have trees : premises = children := by
        funext position
        exact eq_of_heq (induction position (children position) (congrFun components position))
      cases trees
      rfl

/-- A receipt retains its conclusion as well as its full structural proof. -/
def receiptGraph (atoms : ArgumentCoding Atom) (origins : ArgumentCoding Origin)
    (receipt : Receipt source) : AccessiblePointedGraph.{u} :=
  AccessiblePointedGraph.kpairGraph (atoms.graph receipt.fact) (treeGraph origins receipt.2)

def reading (atoms : ArgumentCoding Atom) (origins : ArgumentCoding Origin)
    (receipt : Receipt source) : HSet.{u} := HSet.mk (receiptGraph atoms origins receipt)

theorem reading_injective (atoms : ArgumentCoding Atom) (origins : ArgumentCoding Origin) :
    Function.Injective (reading (source := source) atoms origins) := by
  rintro ⟨firstAtom, first⟩ ⟨secondAtom, second⟩ same
  change HSet.mk (AccessiblePointedGraph.kpairGraph (atoms.graph firstAtom) (treeGraph origins first)) =
    HSet.mk (AccessiblePointedGraph.kpairGraph (atoms.graph secondAtom) (treeGraph origins second)) at same
  rw [AccessiblePointedGraph.mk_kpairGraph, AccessiblePointedGraph.mk_kpairGraph] at same
  have atomsSame := atoms.injective (HSet.kpair_inj.mp same).1
  exact Sigma.ext atomsSame (treeGraph_reflect origins first second (HSet.kpair_inj.mp same).2)

@[simp] theorem reading_kernel (atoms : ArgumentCoding Atom) (origins : ArgumentCoding Origin)
    (first second : Receipt source) : reading atoms origins first = reading atoms origins second ↔
      first = second := (reading_injective atoms origins).eq_iff

def receiptCoding (atoms : ArgumentCoding Atom) (origins : ArgumentCoding Origin) :
    ArgumentCoding (Receipt source) where
  graph := receiptGraph atoms origins
  injective := reading_injective atoms origins

/-- Ordered receipt batches retain both order and repeated derivations. -/
def batchGraph (atoms : ArgumentCoding Atom) (origins : ArgumentCoding Origin)
    (batch : List (Receipt source)) : AccessiblePointedGraph.{u} :=
  (receiptCoding atoms origins).lists.graph batch

@[simp] theorem batch_kernel (atoms : ArgumentCoding Atom) (origins : ArgumentCoding Origin)
    (first second : List (Receipt source)) :
    HSet.mk (batchGraph atoms origins first) = HSet.mk (batchGraph atoms origins second) ↔
      first = second := ((receiptCoding atoms origins).lists.injective).eq_iff

/-- Erasing a receipt to its atom has exactly the declared fact kernel. -/
@[simp] theorem fact_kernel (atoms : ArgumentCoding Atom) (first second : Receipt source) :
    atoms.reading first.fact = atoms.reading second.fact ↔ first.fact = second.fact :=
  atoms.injective.eq_iff

/-- The material set of fact labels in the actual current batch. -/
def supportGraph (atoms : ArgumentCoding Atom) (batch : List (Receipt source)) :
    AccessiblePointedGraph.{u} :=
  AccessiblePointedGraph.sup fun index : ULift.{u, 0} (Fin batch.length) =>
    atoms.graph (batch.get index.down).fact

theorem mem_supportGraph (atoms : ArgumentCoding Atom) (batch : List (Receipt source))
    (value : HSet.{u}) : value ∈ HSet.mk (supportGraph atoms batch) ↔
      ∃ receipt ∈ batch, atoms.reading receipt.fact = value := by
  change value ∈ HSet.range _ ↔ _
  rw [HSet.mem_range]
  constructor
  · rintro ⟨index, same⟩
    exact ⟨batch.get index.down, List.get_mem _ _, same⟩
  · rintro ⟨receipt, present, same⟩
    obtain ⟨index, rfl⟩ := List.mem_iff_get.mp present
    exact ⟨⟨index⟩, same⟩

@[simp] theorem atom_mem_supportGraph [DecidableEq Atom] (atoms : ArgumentCoding Atom)
    (batch : List (Receipt source)) (atom : Atom) :
    atoms.reading atom ∈ HSet.mk (supportGraph atoms batch) ↔ atom ∈ batchSupport batch := by
  rw [mem_supportGraph, mem_batchSupport]
  constructor
  · rintro ⟨receipt, present, same⟩
    exact ⟨receipt, present, atoms.injective same⟩
  · rintro ⟨receipt, present, same⟩
    exact ⟨receipt, present, congrArg atoms.reading same⟩

@[simp] theorem support_kernel [DecidableEq Atom] (atoms : ArgumentCoding Atom)
    (first second : List (Receipt source)) :
    HSet.mk (supportGraph atoms first) = HSet.mk (supportGraph atoms second) ↔
      batchSupport first = batchSupport second := by
  constructor
  · intro same
    apply Finite.support_ext
    intro atom
    change atom ∈ batchSupport first ↔ atom ∈ batchSupport second
    rw [← atom_mem_supportGraph atoms first atom, ← atom_mem_supportGraph atoms second atom, same]
  · intro same
    apply HSet.ext
    intro value
    rw [mem_supportGraph, mem_supportGraph]
    constructor
    · rintro ⟨receipt, present, reading⟩
      have member := (mem_batchSupport first receipt.fact).mpr ⟨receipt, present, rfl⟩
      rw [same] at member
      obtain ⟨other, present, equal⟩ := (mem_batchSupport second receipt.fact).mp member
      exact ⟨other, present, (congrArg atoms.reading equal).trans reading⟩
    · rintro ⟨receipt, present, reading⟩
      have member := (mem_batchSupport second receipt.fact).mpr ⟨receipt, present, rfl⟩
      rw [← same] at member
      obtain ⟨other, present, equal⟩ := (mem_batchSupport first receipt.fact).mp member
      exact ⟨other, present, (congrArg atoms.reading equal).trans reading⟩

open Mettapedia.TypeTheory.DependentFamilyObserverFactorization
open Mettapedia.TypeTheory.DependentFamilySectionDescent

universe w
variable {family : Receipt source → Type w}

/-- The term criterion is unchanged when its observed fact is materially coded. -/
theorem compatible_iff_material (atoms : ArgumentCoding Atom)
    (d : FamilyFactorization Receipt.fact family) (term : ∀ receipt, family receipt) :
    Compatible d term ↔ ∀ first second,
      atoms.reading first.fact = atoms.reading second.fact →
        sectionObservation d term first = sectionObservation d term second := by
  constructor
  · intro compatible first second same
    exact compatible first second (atoms.injective same)
  · intro compatible first second same
    exact compatible first second (congrArg atoms.reading same)

theorem material_compatible_iff_descends (atoms : ArgumentCoding Atom)
    (d : FamilyFactorization Receipt.fact family) (term : ∀ receipt, family receipt) :
    (∀ first second, atoms.reading first.fact = atoms.reading second.fact →
        sectionObservation d term first = sectionObservation d term second) ↔
      ∃ observed : ∀ value, factFamily d value, pullback d observed = term :=
  (compatible_iff_material atoms d term).symm.trans (compatible_iff_descends d term)

end Mettapedia.GSLT.ProgrammableSpaceEvidence.Material
