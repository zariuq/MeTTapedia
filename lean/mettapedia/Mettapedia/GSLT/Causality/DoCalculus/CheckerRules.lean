import Mettapedia.GSLT.Causality.DoCalculus.RegimeModel
import Mettapedia.ProbabilityTheory.BayesianNetworks.FiniteDSeparation

/-!
# Rules 2 and 3 discharged by the finite checker

Rule 2 asks for separation of `Y` from `Z` given `X ∪ W` in the graph with the
arrows into `X` and out of `Z` deleted. Rule 3 asks for separation of `Y` from
`Z` given `X ∪ W` in the graph with the arrows into `X` and into `Z(W)`
deleted. `Z(W)` is computed here: a vertex of `Z` lies in it when it is not an
ancestor of any vertex of `W` after the arrows into `X` are deleted. Ancestors
exclude the vertex itself.

The checker accepts a profile only when that separation holds and both
endpoint sets are disjoint from the conditioning set. Compatibility of the
accepted profile then forces `Y` and `Z` to be disjoint. A `false` answer can
mean that the sets fall outside this supported profile. It is not, by itself,
a proof that an active trail exists.

Positivity of the conditioning mass is the remaining hypothesis. Rule 2 uses
the `do(X)` mass. The `do(X ∪ Z)` mass follows from it. Rule 3 keeps both
masses as hypotheses.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.DoCalculus

open Mettapedia.ProbabilityTheory.BayesianNetworks
open Mettapedia.ProbabilityTheory.BayesianNetworks.FiniteReachability
open Mettapedia.ProbabilityTheory.BayesianNetworks.FiniteDSeparation
open BayesianNetwork
open DirectedGraph
open DSeparation
open scoped ENNReal

variable {V : Type}
variable [Fintype V] [DecidableEq V]
variable (graph : DirectedGraph V)
variable [DecidableRel graph.edges]

instance gout_decidableRel (X Z : Finset V) :
    DecidableRel (gout graph X Z).edges := fun _ _ => by
  unfold gout gx deleteOutgoing deleteIncoming
  infer_instance

/-- `Z(W)` as a finset. Membership is the Boolean reachability test. -/
def zOfFinset (X Z W : Finset V) : Finset V :=
  Z.filter fun z => ∀ w ∈ W,
    reaches (deleteIncoming graph X) z w = false ∨ z = w

lemma zOfFinset_coe_eq_zWitness (X Z W : Finset V) :
    ((zOfFinset graph X Z W : Finset V) : Set V) = zWitness graph X Z W := by
  ext z
  constructor
  · intro hz
    have hzF : z ∈ zOfFinset graph X Z W := Finset.mem_coe.mp hz
    rw [zOfFinset, Finset.mem_filter] at hzF
    refine ⟨Finset.mem_coe.mpr hzF.1, ?_⟩
    intro w hw hanc
    have hanc' : (deleteIncoming graph X).Reachable z w ∧ z ≠ w := by
      simpa [DirectedGraph.ancestors, gx] using hanc
    have hdisj := hzF.2 w (Finset.mem_coe.mp hw)
    have hreach : reaches (deleteIncoming graph X) z w = true :=
      (reaches_eq_true_iff (deleteIncoming graph X) z w).2 hanc'.1
    rcases hdisj with hfalse | heq
    · exact Bool.false_ne_true (hfalse.symm.trans hreach)
    · exact hanc'.2 heq
  · intro hz
    apply Finset.mem_coe.mpr
    rw [zOfFinset, Finset.mem_filter]
    refine ⟨Finset.mem_coe.mp hz.1, ?_⟩
    intro w hw
    by_cases hne : z = w
    · exact Or.inr hne
    · apply Or.inl
      cases hreach : reaches (deleteIncoming graph X) z w with
      | false => rfl
      | true =>
          exact absurd ((reaches_eq_true_iff (deleteIncoming graph X) z w).1 hreach)
            (fun hpath => hz.2 w (Finset.mem_coe.mpr hw)
              (by simpa [DirectedGraph.ancestors, gx] using And.intro hpath hne))

/-- Rule 3's checked graph: arrows into `X` and into the computed `Z(W)`. -/
def rule3Graph (X Z W : Finset V) : DirectedGraph V :=
  deleteIncoming (deleteIncoming graph X) (zOfFinset graph X Z W)

instance rule3Graph_decidableRel (X Z W : Finset V) :
    DecidableRel (rule3Graph graph X Z W).edges := fun _ _ => by
  unfold rule3Graph deleteIncoming
  infer_instance

lemma rule3Graph_eq_g3 (X Z W : Finset V) :
    rule3Graph graph X Z W = g3 graph X Z W := by
  ext u v
  simp only [rule3Graph, g3, deleteIncoming, deleteIncomingSet, gx]
  have hviff : v ∈ zOfFinset graph X Z W ↔ v ∈ zWitness graph X Z W := by
    rw [← Finset.mem_coe, zOfFinset_coe_eq_zWitness]
  simp [hviff]

lemma rule3Graph_acyclic (hAcyclic : graph.IsAcyclic) (X Z W : Finset V) :
    (rule3Graph graph X Z W).IsAcyclic := by
  rw [rule3Graph_eq_g3]
  exact g3_acyclic graph hAcyclic X Z W

/-- Rule 2's checker profile: outcome, exchanged set, conditioning set. -/
def rule2Profile (outcome exchanged conditioning : Finset V) : Condition V where
  X := outcome
  Y := exchanged
  Z := conditioning

/-- Rule 3's checker profile: outcome, deleted set, conditioning set. -/
def rule3Profile (outcome deleted conditioning : Finset V) : Condition V where
  X := outcome
  Y := deleted
  Z := conditioning

variable (hAcyclic : graph.IsAcyclic)

/-- Checker acceptance is separation of `Y` from `Z` given `X ∪ W` in the
rule-2 mutilation, together with both endpoints missing `X ∪ W`. -/
theorem rule2_check_iff (hAcyclic : graph.IsAcyclic) (X Y Z W : Finset V) :
    FiniteDSeparation.check (gout graph X Z) (rule2Profile Y Z (X ∪ W)) = true ↔
      (rule2Profile Y Z (X ∪ W)).Meaning (gout graph X Z) ∧
        (rule2Profile Y Z (X ∪ W)).Supported :=
  check_eq_true_iff (gout graph X Z) (rule2Profile Y Z (X ∪ W))
    (gout_acyclic graph hAcyclic X Z)
    (fun vertex => DirectedGraph.isAcyclic_irrefl (gout graph X Z)
      (gout_acyclic graph hAcyclic X Z) vertex)

/-- Checker acceptance is separation of `Y` from `Z` given `X ∪ W` after the
arrows into `X` and into the computed `Z(W)` are deleted, together with both
endpoints missing `X ∪ W`. -/
theorem rule3_check_iff (hAcyclic : graph.IsAcyclic) (X Y Z W : Finset V) :
    FiniteDSeparation.check (rule3Graph graph X Z W)
        (rule3Profile Y Z (X ∪ W)) = true ↔
      (rule3Profile Y Z (X ∪ W)).Meaning (rule3Graph graph X Z W) ∧
        (rule3Profile Y Z (X ∪ W)).Supported :=
  check_eq_true_iff (rule3Graph graph X Z W) (rule3Profile Y Z (X ∪ W))
    (rule3Graph_acyclic graph hAcyclic X Z W)
    (fun vertex => DirectedGraph.isAcyclic_irrefl (rule3Graph graph X Z W)
      (rule3Graph_acyclic graph hAcyclic X Z W) vertex)

/-- An accepted rule-2 profile gives `Disjoint X Z`, `Disjoint W Z`, and
`Disjoint Y Z`, and the separation premise of rule 2. -/
theorem rule2_disjoint_of_check (hAcyclic : graph.IsAcyclic) {X Y Z W : Finset V}
    (hcheck : FiniteDSeparation.check (gout graph X Z)
      (rule2Profile Y Z (X ∪ W)) = true) :
    Disjoint X Z ∧ Disjoint W Z ∧ Disjoint Y Z ∧
      DSeparatedFull (gout graph X Z) (Y : Set V) (Z : Set V)
        ((X ∪ W : Finset V) : Set V) := by
  have haccepted := (rule2_check_iff graph hAcyclic X Y Z W).1 hcheck
  have hsup := haccepted.2
  have hXZ : Disjoint X Z :=
    _root_.disjoint_comm.mp
      (Finset.disjoint_of_subset_right Finset.subset_union_left hsup.2)
  have hWZ : Disjoint W Z :=
    _root_.disjoint_comm.mp
      (Finset.disjoint_of_subset_right Finset.subset_union_right hsup.2)
  have hYZ : Disjoint Y Z :=
    disjoint_X_Y_of_compatible_supported (rule2Profile Y Z (X ∪ W))
      haccepted.1.1 hsup
  exact ⟨hXZ, hWZ, hYZ, haccepted.1.2⟩

/-- An accepted rule-3 profile gives `Disjoint X Z`, `Disjoint W Z`, and
`Disjoint Y Z`, and separation from `Z` in the computed `Z(W)` mutilation. -/
theorem rule3_disjoint_of_check (hAcyclic : graph.IsAcyclic) {X Y Z W : Finset V}
    (hcheck : FiniteDSeparation.check (rule3Graph graph X Z W)
      (rule3Profile Y Z (X ∪ W)) = true) :
    Disjoint X Z ∧ Disjoint W Z ∧ Disjoint Y Z ∧
      DSeparatedFull (g3 graph X Z W) (Y : Set V) (Z : Set V)
        ((X ∪ W : Finset V) : Set V) := by
  have haccepted := (rule3_check_iff graph hAcyclic X Y Z W).1 hcheck
  have hsup := haccepted.2
  have hXZ : Disjoint X Z :=
    _root_.disjoint_comm.mp
      (Finset.disjoint_of_subset_right Finset.subset_union_left hsup.2)
  have hWZ : Disjoint W Z :=
    _root_.disjoint_comm.mp
      (Finset.disjoint_of_subset_right Finset.subset_union_right hsup.2)
  have hYZ : Disjoint Y Z :=
    disjoint_X_Y_of_compatible_supported (rule3Profile Y Z (X ∪ W))
      haccepted.1.1 hsup
  have hsep : DSeparatedFull (g3 graph X Z W) (Y : Set V) (Z : Set V)
      ((X ∪ W : Finset V) : Set V) := by
    simpa [rule3Graph_eq_g3, rule3Profile] using haccepted.1.2
  exact ⟨hXZ, hWZ, hYZ, hsep⟩

variable {β : Type} [Fintype β] [DecidableEq β] [Inhabited β] [MeasurableSpace β]
  [MeasurableSingletonClass β] [StandardBorelSpace β]

/-- Rule 2 from checker acceptance. Support supplies the disjointness.
Positivity is the `do(X)` mass of `X ∪ Z ∪ W`, and `anchor` carries the
exchanged value on `Z`. -/
theorem rule2_of_check
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    {X Y Z W : Finset V} (x z anchor : V → β)
    (hz : ∀ v ∈ Z, anchor v = z v)
    (hcheck : FiniteDSeparation.check (gout graph X Z)
      (rule2Profile Y Z (X ∪ W)) = true)
    (hpos : truncSlice graph hAcyclic cpt (doFinset X x) (X ∪ Z ∪ W) anchor ≠ 0) :
    truncSlice graph hAcyclic cpt (doFinset (X ∪ Z) (mergeAssign X x z))
        (X ∪ Y ∪ Z ∪ W) anchor /
      truncSlice graph hAcyclic cpt (doFinset (X ∪ Z) (mergeAssign X x z))
        (X ∪ Z ∪ W) anchor =
    truncSlice graph hAcyclic cpt (doFinset X x) (X ∪ Y ∪ Z ∪ W) anchor /
      truncSlice graph hAcyclic cpt (doFinset X x) (X ∪ Z ∪ W) anchor := by
  have hparts := rule2_disjoint_of_check graph hAcyclic hcheck
  exact rule2_regime (β := β) (graph := graph) (hAcyclic := hAcyclic)
    hparts.1 hparts.2.2.1 hparts.2.2.2 cpt x z anchor hz hpos

/-- Rule 3 from checker acceptance. Support supplies the disjointness.
Both denominator masses stay hypotheses: idle uses `do(X)`, and the forced
regime uses `do(X, Z)`. -/
theorem rule3_of_check
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    {X Y Z W : Finset V} (x z anchor : V → β)
    (hcheck : FiniteDSeparation.check (rule3Graph graph X Z W)
      (rule3Profile Y Z (X ∪ W)) = true)
    (hpos : truncSlice graph hAcyclic cpt (doFinset X x) (X ∪ W) anchor ≠ 0)
    (hposZ : truncSlice graph hAcyclic cpt
      (doFinset (X ∪ Z) (mergeAssign X x z)) (X ∪ W) anchor ≠ 0) :
    truncSlice graph hAcyclic cpt (doFinset (X ∪ Z) (mergeAssign X x z))
        (X ∪ Y ∪ W) anchor /
      truncSlice graph hAcyclic cpt
        (doFinset (X ∪ Z) (mergeAssign X x z)) (X ∪ W) anchor =
    truncSlice graph hAcyclic cpt (doFinset X x) (X ∪ Y ∪ W) anchor /
      truncSlice graph hAcyclic cpt (doFinset X x) (X ∪ W) anchor := by
  have hparts := rule3_disjoint_of_check graph hAcyclic hcheck
  exact rule3_regime (β := β) (graph := graph) (hAcyclic := hAcyclic)
    hparts.1 hparts.2.2.1 hparts.2.1 hparts.2.2.2 cpt x z anchor hpos hposZ

end Mettapedia.GSLT.Causality.DoCalculus
