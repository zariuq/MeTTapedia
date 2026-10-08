import Mettapedia.GSLT.Distinction.OptionGraph
import Mettapedia.SetTheory.CarveOuts.Distinctions
import Mettapedia.SetTheory.CarveOuts.HOTGCoverage
import Mettapedia.SetTheory.CarveOuts.GraphValues
import Mettapedia.SetTheory.CarveOuts.WellFoundedReadout
import Mettapedia.SetTheory.Profiles
import Mettapedia.SetTheory.AntiFoundation.Distinctions
import Mettapedia.TypeTheory.MaterialSets.Hypersets.Finality
import Mettapedia.TypeTheory.MaterialSets.Hypersets.WellFounded
import Mettapedia.TypeTheory.MaterialSets.Hypersets.AntiFoundation

/-!
# The set carve-outs, placed in the option graph

Two questions, each a chain of carve-outs read on one domain.

* **Carve-outs of the Heyting-valued top** (`heyting-carve-outs`): the top, its
  double-negation part, the two-valued points of that part, and the ground at the principal
  points. Each reading of a sentence of the forcing language is a function of the one before
  (a view arrow, cited by its `Factors` theorem), and each step forgets something on the frame
  of perspectives (a witness, cited by its `NonTrivialFiber`).
* **Carve-outs of the hyperset top** (`well-founded-carve-outs`): the hypersets, the
  well-founded bubble, and HOTG as a child of the bubble. The bubble's readout is a function
  of the hyperset and forgets the Quine atom; the bubble's laws are read inside HOTG, and do
  not decide HOTG's universe commitment.

Each record keeps a place for evidence from an external proof checker
(`Record.external`). The step from the bubble into HOTG carries Megalodon's run of the graph
decorations file: inside HOTG, well-founded graphs decorate, and in one way.

**Two checkers on one graph** (`crossChecks`). Each row of the comparison table with Lean's
hypersets names one graph, the verdict Megalodon checks inside HOTG, and the Lean verdict.
A row where they agree becomes an arrow: on the well-founded bubble, or for hyperset
membership read through graph codes, the two checkers give the same verdict. A row where they
separate becomes a witness between the well-founded bubble, whose verdict Megalodon checks,
and the hyperset top, whose verdict Lean checks. The rows are transcribed from the table; the
generator of the published graph compares every transcribed field with the table.

**Two presentations called HOTG** (`hotg-presentations`). The C profile `megalodon-hotg`
seeds separation directly, seeds no choice law, and omits function and propositional
extensionality; Megalodon's HOTG has the choice axiom and derives separation and excluded
middle from it. One witness records this. Nothing is decided about it.

External checker evidence is never kernel-checked evidence here
(`crossWitnesses_not_kernelChecked`). `graph` is a local graph of everything in this module,
and `graph_wellFormed` checks it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeOptions.CarveOuts

open Lean (Name)
open Mettapedia.GSLT.Distinction.OptionGraph

/-- The report that records the arguments. -/
def report : Document where
  key := "carveouts-heyting-top-and-wf-bubble-report-20261005"
  title := "Carve-outs, Lean side: the Heyting-valued top, the well-founded bubble, HOTG: report"
  date := "2026-10-05"

/-- A run of Megalodon on the graph decorations file, citing some of its theorems and
some declarations of its preamble. -/
def megalodon (theorems : List String) (preambleDeclarations : List String := []) :
    ExternalCheck where
  checker := "Megalodon"
  directory := "megalodon"
  command := "bin/megalodon -I ramsey36/preamble.mgs set_carveouts/hotg_graph_decorations.mg"
  file := "set_carveouts/hotg_graph_decorations.mg"
  fileSha256 := "11bce74570cff61e51c53befcd4b25cc23c6b925844b7d96e418f035a83ccbab"
  preamble := "ramsey36/preamble.mgs"
  preambleSha256 := "98d002808566ccd4ddfa22883e7a963b58fa0fb39d693a94b20bef2c196d6bc9"
  theorems := theorems
  preambleDeclarations := preambleDeclarations
  binary := "bin/megalodon"
  binarySha256 := "92ee2b327666e3b51bf249fb22dd4993b28a96acbd1a577c14a1d8ecb297381d"

/-- The documents the module's arguments cite, beside the report. -/
def megalodonReport : Document where
  key := "carveouts-megalodon-graph-decorations-report-20261005"
  title := "Carve-outs, Megalodon side: graph decorations inside HOTG, checked: report"
  date := "2026-10-05"

def lawInventory : Document where
  key := "hotg-law-inventory"
  title := "HOTG law inventory: the C profile's seeds against Megalodon's preamble"
  date := "2026-10-05"

def cProfileFile : Document where
  key := "c-profile-megalodon-hotg"
  title := "The C draft's Megalodon HOTG profile file"
  date := "2026-10-05"

def megalodonLibrary : Document where
  key := "megalodon-library-part1"
  title := "Megalodon library, part 1: the foundation's first definitions and theorems"
  date := "2026-10-05"

/-- One step of a chain of carve-outs. -/
structure Record where
  number : Nat
  question : String
  /-- The option that keeps the distinction. -/
  fine : String
  /-- The option that forgets it. -/
  coarse : String
  arrowId : String
  arrowKind : ArrowKind
  arrowGrades : List GradeClaim
  arrowSource : String
  arrowTarget : String
  arrowSummary : String
  /-- Theorems for the arrow. -/
  arrowTheorems : List Name
  witnessId : String
  /-- Theorems for the witness. -/
  witnessTheorems : List Name
  case : String
  coarseReading : String
  fineReading : String
  /-- Evidence from an external checker for the arrow; empty until it is supplied. -/
  external : List ExternalCheck := []
  /-- What the arrow preserves and what it does not. -/
  contract : Contract := {}

/-- The steps. -/
def records : List Record := [
  { number := 0, question := "heyting-carve-outs"
    fine := "heyting-top", coarse := "double-negation-part"
    arrowId := "top-to-double-negation", arrowKind := .booleanization
    arrowGrades := [.factors, .lossy]
    arrowSource := "heyting-top", arrowTarget := "double-negation-part"
    arrowSummary := "The double negation of a sentence's truth value is a function of the value."
    arrowTheorems := [``Mettapedia.SetTheory.CarveOuts.factors_top_negNeg,
      ``Mettapedia.SetTheory.CarveOuts.HeytingValued.toRegular_sSup,
      ``Mettapedia.SetTheory.CarveOuts.HeytingValued.toRegular_inf]
    witnessId := "dense-value"
    witnessTheorems := [``Mettapedia.SetTheory.CarveOuts.fiber_negNeg_top,
      ``Mettapedia.SetTheory.CarveOuts.not_factors_negNeg_top,
      ``Mettapedia.SetTheory.CarveOuts.HeytingValued.chain_m_dense,
      ``Mettapedia.SetTheory.CarveOuts.HeytingValued.chain_lem_ne_top]
    case := "The sentences with truth values (⊥, 1, ⊥) and (⊥, ⊤, ⊥) in the frame of \
      perspectives; 1 is dense in the chain [0, ∞]."
    coarseReading := "Identified: both double negations are (⊥, ⊤, ⊥)."
    fineReading := "Kept apart: 1 is not ⊤. Over the three-element chain the same gap makes \
      a bounded excluded-middle instance take a value below ⊤."
    contract := {
      entries := [
        .keeps .connectives [``Mettapedia.SetTheory.CarveOuts.HeytingValued.toRegular_inf,
          ``Mettapedia.SetTheory.CarveOuts.HeytingValued.toRegular_sSup,
          ``Mettapedia.SetTheory.CarveOuts.HeytingValued.toRegular_top]
          "meets, arbitrary joins and the top",
        .loses .distinctions [``Mettapedia.SetTheory.CarveOuts.not_factors_negNeg_top,
          ``Mettapedia.SetTheory.CarveOuts.HeytingValued.chain_m_dense]
          "truth values: a dense value is read as true",
        .unknownAt (.commitment .choice),
        .unknownAt (.commitment .collection),
        .unknownAt (.commitment .universes),
        .unknownAt (.operation .pi)] } },
  { number := 1, question := "heyting-carve-outs"
    fine := "double-negation-part", coarse := "two-valued-points"
    arrowId := "double-negation-to-points", arrowKind := .observationalQuotient
    arrowGrades := [.factors, .lossy]
    arrowSource := "double-negation-part", arrowTarget := "two-valued-points"
    arrowSummary := "The verdict of each point of the double-negation part is a function of \
      the double negation."
    arrowTheorems := [``Mettapedia.SetTheory.CarveOuts.factors_negNeg_points,
      ``Mettapedia.SetTheory.CarveOuts.HeytingValued.eval_lem_regular]
    witnessId := "gunky-pole"
    witnessTheorems := [``Mettapedia.SetTheory.CarveOuts.fiber_points_negNeg,
      ``Mettapedia.SetTheory.CarveOuts.not_factors_points_negNeg,
      ``Mettapedia.SetTheory.CarveOuts.not_holds_gunkTop,
      ``Mettapedia.SetTheory.CarveOuts.HeytingValued.cantorGunkyWitness,
      ``Mettapedia.SetTheory.CarveOuts.HeytingValued.exists_atom_of_point]
    case := "The sentences with truth values ⊥ and (⊥, ⊥, ⊤), which differ only on the regular \
      open sets of Cantor space."
    coarseReading := "Identified: no point affirms either, since a point affirming the second \
      would be a point of an atomless complete Boolean algebra."
    fineReading := "Kept apart: their double negations differ."
    contract := {
      entries := [
        .keeps (.formulas .boundedPositive)
          [``Mettapedia.SetTheory.CarveOuts.HeytingValued.Point.holds_eval_iff_of_positive]
          "positive bounded truth transfers to every point",
        .keeps .connectives [``Mettapedia.SetTheory.CarveOuts.HeytingValued.Point.holds_sup,
          ``Mettapedia.SetTheory.CarveOuts.HeytingValued.Point.holds_iSup] "joins at a point",
        .loses (.formulas .bounded)
          [``Mettapedia.SetTheory.CarveOuts.HeytingValued.free_point_ball_gap]
          "a free point fails a bounded universal",
        .loses (.formulas .firstOrder)
          [``Mettapedia.SetTheory.CarveOuts.HeytingValued.free_point_ball_gap]
          "a free point fails a bounded universal"] } },
  { number := 2, question := "heyting-carve-outs"
    fine := "two-valued-points", coarse := "principal-ground"
    arrowId := "points-to-ground", arrowKind := .equivalence
    arrowGrades := [.factors, .lossy]
    arrowSource := "two-valued-points", arrowTarget := "principal-ground"
    arrowSummary := "At an atom the ground's verdict in ZFSet is the verdict of the atom's \
      point: the principal collapse."
    arrowTheorems := [``Mettapedia.SetTheory.CarveOuts.factors_points_ground,
      ``Mettapedia.SetTheory.CarveOuts.HeytingValued.Name.le_eval_iff_zfHolds,
      ``Mettapedia.SetTheory.CarveOuts.HeytingValued.atomQuotientEquivZFSet_mem_iff]
    witnessId := "free-point"
    witnessTheorems := [``Mettapedia.SetTheory.CarveOuts.fiber_ground_points,
      ``Mettapedia.SetTheory.CarveOuts.not_factors_ground_points,
      ``Mettapedia.SetTheory.CarveOuts.chainPoint_ne_regularAtomPoint,
      ``Mettapedia.SetTheory.CarveOuts.atom_chain_eq_zero,
      ``Mettapedia.SetTheory.CarveOuts.HeytingValued.free_point_ball_gap]
    case := "The sentences with truth values (⊥, 0, ⊥) and (⊥, ⊤, ⊥), which differ only on \
      the chain [0, ∞]."
    coarseReading := "Identified: no atom lives on the chain, so every atom gives both the \
      same ZFSet verdict."
    fineReading := "Kept apart by the free point 'positive' of the chain, which is not the \
      point of any atom."
    contract := {
      entries := [
        .keeps (.formulas .atomic)
          [``Mettapedia.SetTheory.CarveOuts.HeytingValued.Name.le_mem_iff_collapseZF_mem,
          ``Mettapedia.SetTheory.CarveOuts.HeytingValued.Name.le_eq_iff_collapseZF_eq]
          "membership and equality at the atom",
        .keeps (.formulas .bounded)
          [``Mettapedia.SetTheory.CarveOuts.HeytingValued.Name.le_eval_iff_zfHolds]
          "every bounded formula at the atom",
        .loses .distinctions
          [``Mettapedia.SetTheory.CarveOuts.not_factors_ground_points]
          "outside the hypothesis: the free point of the chain is the point of no atom"]
      hypotheses := [``IsAtom] } },
  { number := 3, question := "well-founded-carve-outs"
    fine := "hyperset-top", coarse := "well-founded-bubble"
    arrowId := "hypersets-to-bubble", arrowKind := .observationalQuotient
    arrowGrades := [.factors, .lossy]
    arrowSource := "hyperset-top", arrowTarget := "well-founded-bubble"
    arrowSummary := "The total readout toZFSet retains well-founded members and loses atomic \
      membership and equality reflection on general hypersets. Its restriction to the actual \
      well-founded subcarrier preserves and reflects membership and equality."
    arrowTheorems := [``Mettapedia.SetTheory.CarveOuts.factors_hset_bubble,
      ``Mettapedia.SetTheory.CarveOuts.hsetBubble,
      ``Mettapedia.SetTheory.CarveOuts.bubble_readout_injective,
      ``Mettapedia.SetTheory.CarveOuts.views_agree_of_acc,
      ``Mettapedia.SetTheory.CarveOuts.WellFoundedReadout.readout_mem_iff,
      ``Mettapedia.SetTheory.CarveOuts.WellFoundedReadout.wfPart_mem_iff,
      ``Mettapedia.SetTheory.CarveOuts.WellFoundedReadout.wfPart_eq_iff]
    witnessId := "quine-atom"
    witnessTheorems := [``Mettapedia.SetTheory.CarveOuts.fiber_bubble_hset,
      ``Mettapedia.SetTheory.CarveOuts.not_factors_bubble_hset,
      ``Mettapedia.SetTheory.CarveOuts.not_acc_of_quine,
      ``Mettapedia.SetTheory.CarveOuts.WellFoundedReadout.quine_membership_lost,
      ``Mettapedia.SetTheory.CarveOuts.WellFoundedReadout.quine_empty_same_readout]
    case := "The Quine atom Ω = {Ω} and the empty set."
    coarseReading := "Identified: the bubble's readout of Ω is ∅."
    fineReading := "Kept apart: Ω is not ∅."
    contract := {
      entries := [
        .loses (.formulas .atomic)
          [``Mettapedia.SetTheory.CarveOuts.WellFoundedReadout.quine_membership_lost,
          ``Mettapedia.SetTheory.CarveOuts.WellFoundedReadout.not_equality_reflecting]
          "Ω belongs to itself but its readout ∅ does not; Ω and ∅ have the same readout",
        .loses (.formulas .firstOrder) [``Mettapedia.SetTheory.Profiles.hset_hasQuineAtom,
          ``Mettapedia.SetTheory.CarveOuts.not_acc_of_quine]
          "there is a Quine atom: true of hypersets, false on the bubble",
        .loses (.formulas .bounded)
          [``Mettapedia.SetTheory.CarveOuts.WellFoundedReadout.quine_membership_lost]
          "the lost atomic membership statement is already a bounded formula",
        .unknownAt (.commitment .choice),
        .unknownAt (.commitment .collection),
        .unknownAt (.commitment .universes)] } },
  { number := 4, question := "well-founded-carve-outs"
    fine := "hotg-child", coarse := "well-founded-bubble"
    arrowId := "hotg-modelled-in-zfset", arrowKind := .interpretation
    arrowGrades := [.ungraded]
    arrowSource := "hotg-child", arrowTarget := "well-founded-bubble"
    arrowSummary := "HOTG is modelled in the bubble's carrier ZFSet: its laws hold in the full higher-order model, the universe laws under cofinally many inaccessibles, and the choice law by the host's choice."
    arrowTheorems := [``Mettapedia.SetTheory.CarveOuts.HOTGCoverage.hotgLawsInZFSet,
      ``Mettapedia.SetTheory.CarveOuts.HOTGCoverage.coverage_all_proved,
      ``Mettapedia.SetTheory.CarveOuts.zfSet_bubbleLaws]
    witnessId := "hereditarily-finite"
    witnessTheorems := [``Mettapedia.SetTheory.CarveOuts.fiber_bubble_hotg,
      ``Mettapedia.SetTheory.CarveOuts.not_factors_bubble_hotg,
      ``Mettapedia.SetTheory.CarveOuts.hereditarilyFinite_bubbleLaws,
      ``Mettapedia.SetTheory.CarveOuts.no_closed_universe_in_hereditarilyFinite,
      ``Mettapedia.SetTheory.CarveOuts.vonNeumann_omega_closed]
    case := "The hereditarily finite sets V_ω and all of ZFSet."
    coarseReading := "Identified: both satisfy the bubble's seven laws."
    fineReading := "Kept apart: only ZFSet contains a closed universe holding ∅."
    external := [megalodon ["wf_graph_decorates", "wf_decoration_unique", "decoration_iff_wf",
      "no_self_member"]]
    contract := {
      entries := [
        .keeps .laws [``Mettapedia.SetTheory.CarveOuts.HOTGCoverage.hotgLawsInZFSet,
          ``Mettapedia.SetTheory.CarveOuts.HOTGCoverage.coverage_all_proved]
          "the eleven laws, choice and both extensionalities",
        .keeps (.commitment .universes)
          [``Mettapedia.SetTheory.CarveOuts.HOTGCoverage.hotgLawsInZFSet]
          "under cofinally many inaccessibles",
        .keeps (.commitment .choice)
          [``Mettapedia.SetTheory.CarveOuts.HOTGCoverage.hotgLawsInZFSet]
          "by the host's choice",
        .unknownAt (.commitment .collection)]
      hypotheses := [``Mettapedia.Logic.HOL.Embedding.ZFSetUniverseClosure.CofinalInaccessibles] } }
]

/-! ## Two checkers on one graph -/

/-- Where a row of the comparison table goes. -/
inductive CrossPlacement where
  /-- The two checkers agree: an arrow. -/
  | agreement
  /-- They separate: a witness. -/
  | separation
  /-- They agree on the well-founded part and separate on the rest: both. -/
  | both
  deriving DecidableEq, Repr

/-- One row of the comparison table: the graph, its shape and the relation as the table gives
them; the verdict Megalodon checks inside HOTG with its theorems; the Lean verdict with its
declarations, and what Lean has added since the table was written. -/
structure CrossCheck where
  id : String
  graph : String
  shape : String
  relation : String
  placement : CrossPlacement
  source : String
  target : String
  megalodonVerdict : String
  megalodonTheorems : List String
  leanVerdict : String
  leanUpdate : String := ""
  /-- The theorems behind the Lean verdict. -/
  leanDeclarations : List Name
  /-- The definitions the Lean verdict is stated with. -/
  leanDefinitions : List Name := []

/-- Every Lean declaration of a row: its definitions, then its theorems. -/
def CrossCheck.leanCited (row : CrossCheck) : List Name :=
  row.leanDefinitions ++ row.leanDeclarations

/-- The rows of the comparison table. -/
def crossChecks : List CrossCheck := [
  { id := "agree-empty-graph", graph := "empty graph", shape := "1 node, no edges, point 0 (Lean HSet.isolated; AntiFoundation.emptyEdge)"
    relation := "agree"
    placement := .agreement, source := "well-founded-bubble", target := "hotg-child"
    megalodonVerdict := "well-founded; decorates; the node goes to the empty set"
    megalodonTheorems := ["empty_graph_wf", "empty_graph_decorates", "empty_graph_decoration_empty"]
    leanVerdict := "decorates to the empty set, which is well-founded"
    leanDeclarations := [``Mettapedia.TypeTheory.MaterialSets.Hypersets.HSet.decorate_isolated,
      ``Mettapedia.TypeTheory.MaterialSets.Hypersets.HSet.wf_empty,
      ``Mettapedia.SetTheory.AntiFoundation.empty_afa,
      ``Mettapedia.SetTheory.AntiFoundation.all_agree_empty] },
  { id := "agree-ordinal-two", graph := "three-node acyclic graph", shape := "nodes 0 1 2; 1->0, 2->0, 2->1; point 2"
    relation := "agree in kind; the value {0, {0}} has no Lean instance declaration"
    placement := .agreement, source := "well-founded-bubble", target := "hotg-child"
    megalodonVerdict := "well-founded; decorates; every decoration sends 0, 1, 2 to the ordinals 0, 1, 2; the point goes to {0, {0}}"
    megalodonTheorems := ["ordTwo_wf", "ordTwo_decorates", "ordTwo_decoration_values", "ordTwo_point_decoration"]
    leanVerdict := "one decoration (general theorem), well-founded exactly when the point is accessible (general theorem); no declaration for this graph or its value"
    leanUpdate := "The value now has a declaration: the point decorates to {∅, {∅}}."
    leanDeclarations := [``Mettapedia.TypeTheory.MaterialSets.Hypersets.HSet.existsUnique_isDecoration,
      ``Mettapedia.TypeTheory.MaterialSets.Hypersets.HSet.wf_decorate_iff,
      ``Mettapedia.SetTheory.CarveOuts.decorate_ordTwo,
      ``Mettapedia.SetTheory.CarveOuts.decorate_ordTwo_two,
      ``Mettapedia.SetTheory.CarveOuts.wf_decorate_ordTwo] },
  { id := "loop-decoration", graph := "one-node loop", shape := "node 0; 0->0; point 0 (Lean HSet.loop; HSet.Finality selfLoop; AntiFoundation.loopEdge)"
    relation := "separate on decoration (none against Omega); agree that it is not well-founded; agree with foundation_loop_none"
    placement := .separation, source := "well-founded-bubble", target := "hyperset-top"
    megalodonVerdict := "no decoration, not even of the part reachable from the point; not well-founded"
    megalodonTheorems := ["loop_no_decoration", "loop_point_no_decoration", "loop_not_wf"]
    leanVerdict := "decorates to the Quine atom = {Omega}; Omega is not well-founded"
    leanDeclarations := [``Mettapedia.TypeTheory.MaterialSets.Hypersets.HSet.decorate_loop,
      ``Mettapedia.TypeTheory.MaterialSets.Hypersets.HSet.quineAtom_eq_singleton,
      ``Mettapedia.TypeTheory.MaterialSets.Hypersets.HSet.not_wf_quineAtom,
      ``Mettapedia.SetTheory.AntiFoundation.foundation_loop_none] },
  { id := "two-cycle-decoration", graph := "two-node cycle", shape := "nodes 0 1; 0->1, 1->0; point 0 (Lean HSet.twoCycle; AntiFoundation.cycleEdge)"
    relation := "separate on decoration; agree on non-accessibility"
    placement := .separation, source := "well-founded-bubble", target := "hyperset-top"
    megalodonVerdict := "no decoration, not even from the point; not well-founded"
    megalodonTheorems := ["cycle_no_decoration_inst", "cycle_point_no_decoration", "cycle_not_wf"]
    leanVerdict := "both nodes decorate to Omega; no node accessible"
    leanDeclarations := [``Mettapedia.TypeTheory.MaterialSets.Hypersets.HSet.decorate_twoCycle,
      ``Mettapedia.TypeTheory.MaterialSets.Hypersets.HSet.mk_twoCycle,
      ``Mettapedia.TypeTheory.MaterialSets.Hypersets.HSet.not_acc_twoCycle] },
  { id := "agree-loop-two-cycle", graph := "loop against two-node cycle", shape := "the two graphs above"
    relation := "agree"
    placement := .agreement, source := "hyperset-top", target := "hotg-child"
    megalodonVerdict := "bisimilar at every node of the cycle; the two cycle nodes are bisimilar; their codes are different sets"
    megalodonTheorems := ["loop_bisim_cycle", "cycle_nodes_bisim", "CycleCode_bisim_OmegaCode", "CycleCode_neq_OmegaCode"]
    leanVerdict := "bisimilar; the graphs differ"
    leanDeclarations := [``Mettapedia.TypeTheory.MaterialSets.Hypersets.HSet.loop_equiv_twoCycle,
      ``Mettapedia.TypeTheory.MaterialSets.Hypersets.HSet.loop_ne_twoCycle,
      ``Mettapedia.SetTheory.AntiFoundation.cycle_l_bisim_r] },
  { id := "scott-decoration", graph := "Scott pair", shape := "nodes 0 1; 0->0, 1->0, 1->1; point 1 (Lean AntiFoundation.scottEdge, s0 = 0, s1 = 1)"
    relation := "separate on decoration; agree on bisimilarity"
    placement := .separation, source := "well-founded-bubble", target := "hyperset-top"
    megalodonVerdict := "no decoration, not even from the point; every node bisimilar to the loop; the two nodes bisimilar"
    megalodonTheorems := ["scott_no_decoration", "scott_point_no_decoration", "scott_bisim_loop", "scott_nodes_bisim"]
    leanVerdict := "one decoration (general theorem); nodes bisimilar; on the finite anti-foundation carrier both nodes go to Omega"
    leanDeclarations := [``Mettapedia.TypeTheory.MaterialSets.Hypersets.HSet.existsUnique_isDecoration,
      ``Mettapedia.SetTheory.AntiFoundation.scott_s0_bisim_s1,
      ``Mettapedia.SetTheory.AntiFoundation.scott_total_bisim,
      ``Mettapedia.SetTheory.AntiFoundation.scott_afa] },
  { id := "finsler-decoration", graph := "Finsler triple", shape := "nodes 0 1 2; 0->1, 1->0, 1->2, 2->0, 2->1; point 0 (Lean AntiFoundation.finEdge)"
    relation := "separate on decoration; agree on bisimilarity"
    placement := .separation, source := "well-founded-bubble", target := "hyperset-top"
    megalodonVerdict := "no decoration, not even from the point; every node bisimilar to the loop; nodes 1 and 2 bisimilar"
    megalodonTheorems := ["finsler_no_decoration", "finsler_point_no_decoration", "finsler_bisim_loop", "finsler_nodes_bisim"]
    leanVerdict := "one decoration (general theorem); nodes bisimilar; on the finite anti-foundation carrier every node goes to Omega"
    leanDeclarations := [``Mettapedia.TypeTheory.MaterialSets.Hypersets.HSet.existsUnique_isDecoration,
      ``Mettapedia.SetTheory.AntiFoundation.fin_n1_bisim_n2,
      ``Mettapedia.SetTheory.AntiFoundation.fin_total_bisim,
      ``Mettapedia.SetTheory.AntiFoundation.fin_afa] },
  { id := "nest-point-decoration", graph := "nest at its point", shape := "nodes 0 1; 1->0, 1->1; point 1 (Lean AntiFoundation.nestEdge, blank = 0, point = 1)"
    relation := "separate on decoration; agree on bisimilarity; agree with foundation_nest_none"
    placement := .separation, source := "well-founded-bubble", target := "hyperset-top"
    leanUpdate := "The point's value now has a declaration: x = {∅, x}, not well-founded."
    megalodonVerdict := "no decoration, globally or from the point; the point is bisimilar neither to the blank node nor to the loop"
    megalodonTheorems := ["nest_no_decoration", "nest_point_no_decoration", "nest_point_not_bisim_blank", "nest_point_not_bisim_loop"]
    leanVerdict := "one decoration x = {empty, x} (general theorem; on the finite anti-foundation carrier: nest); point not bisimilar to blank; refused on the one-point foundation carrier"
    leanDeclarations := [``Mettapedia.TypeTheory.MaterialSets.Hypersets.HSet.existsUnique_isDecoration,
      ``Mettapedia.SetTheory.AntiFoundation.nest_afa,
      ``Mettapedia.SetTheory.AntiFoundation.nest_point_not_bisim_blank,
      ``Mettapedia.SetTheory.AntiFoundation.foundation_nest_none,
      ``Mettapedia.SetTheory.CarveOuts.decorate_nest_point,
      ``Mettapedia.SetTheory.CarveOuts.not_wf_decorate_nest_point] },
  { id := "agree-nest-blank", graph := "nest at its blank node", shape := "the nest, point 0"
    relation := "agree (in the bubble although the graph has a cycle elsewhere)"
    placement := .agreement, source := "well-founded-bubble", target := "hotg-child"
    leanUpdate := "The blank node's hyperset value now has a declaration: the empty set."
    megalodonVerdict := "the point is accessible; the part reachable from it decorates, to the empty set"
    megalodonTheorems := ["nest_blank_acc", "nest_blank_decorates", "nest_blank_decoration_empty"]
    leanVerdict := "the blank node decorates to the empty set (finite anti-foundation carrier); well-founded by the general theorem"
    leanDefinitions := [``Mettapedia.SetTheory.AntiFoundation.nestAfa]
    leanDeclarations := [``Mettapedia.SetTheory.AntiFoundation.nest_afa,
      ``Mettapedia.TypeTheory.MaterialSets.Hypersets.HSet.wf_decorate_iff,
      ``Mettapedia.SetTheory.CarveOuts.decorate_nest_blank] },
  { id := "decorations-in-general", graph := "decorations in general", shape := "any set of nodes, any edge relation"
    relation := "agree on accessible points (the well-founded bubble); separate on the rest (none against one non-well-founded decoration)"
    placement := .both, source := "well-founded-bubble", target := "hyperset-top"
    megalodonVerdict := "a pointed graph decorates exactly when its point is accessible, and then in one way; a graph decorates exactly when it is well-founded"
    megalodonTheorems := ["decoration_from_iff_acc", "pointed_decoration_unique", "decoration_iff_wf", "wf_decoration_unique", "reachable_cycle_no_decoration"]
    leanVerdict := "every graph has exactly one decoration; it is well-founded exactly when the node is accessible"
    leanDeclarations := [``Mettapedia.TypeTheory.MaterialSets.Hypersets.HSet.existsUnique_isDecoration,
      ``Mettapedia.TypeTheory.MaterialSets.Hypersets.HSet.IsDecoration.unique,
      ``Mettapedia.TypeTheory.MaterialSets.Hypersets.HSet.wf_decorate_iff] },
  { id := "agree-native-membership", graph := "native membership", shape := "the membership of the foundation"
    relation := "agree"
    placement := .agreement, source := "well-founded-bubble", target := "hotg-child"
    megalodonVerdict := "no set is a member of itself; no Quine atom, in the shape exists q, forall z, z in q <-> z = q"
    megalodonTheorems := ["no_self_member", "no_quine_atom", "no_quine_atom_via_loop", "native_no_quine_atom"]
    leanVerdict := "any membership with induction is irreflexive and has no Quine atom; the well-founded hypersets have induction"
    leanDeclarations := [``Mettapedia.SetTheory.Profiles.irreflexive_of_induction,
      ``Mettapedia.SetTheory.Profiles.noQuineAtom_of_induction,
      ``Mettapedia.SetTheory.Profiles.wellFoundedPart_memInduction] },
  { id := "agree-interpreted-membership", graph := "interpreted membership", shape := "graph codes, interpreted membership InStar, equality read as bisimilarity of codes"
    relation := "agree, with bisimilarity of codes in the place of equality of hypersets"
    placement := .agreement, source := "hyperset-top", target := "hotg-child"
    megalodonVerdict := "the loop code is a Quine atom up to bisimilarity and an interpreted member of itself; the two-node cycle code has the same interpreted members; interpreted membership respects bisimilarity on both sides"
    megalodonTheorems := ["interpreted_quine_atom", "OmegaCode_members", "OmegaCode_InStar_self", "CycleCode_members", "InStar_bisim_left", "InStar_bisim_right", "native_vs_interpreted"]
    leanVerdict := "hyperset membership has a Quine atom and refutes membership induction"
    leanDeclarations := [``Mettapedia.SetTheory.Profiles.hset_hasQuineAtom,
      ``Mettapedia.TypeTheory.MaterialSets.Hypersets.HSet.mem_quineAtom,
      ``Mettapedia.TypeTheory.MaterialSets.Hypersets.HSet.eq_singleton_self_iff,
      ``Mettapedia.SetTheory.Profiles.hset_refutes_memInduction] } ]

/-- The Lean reading of a row, with what has been added since the table. -/
def CrossCheck.leanReading (row : CrossCheck) : String :=
  if row.leanUpdate.isEmpty then row.leanVerdict else row.leanVerdict ++ ". " ++ row.leanUpdate

def crossArrowOf (row : CrossCheck) : Arrow where
  id := row.id
  source := row.source
  target := row.target
  kind := if row.source == "hyperset-top" then .interpretation else .equivalence
  grades := [.preserved]
  contract := { entries := [.keeps .verdicts row.leanDeclarations row.graph] }
  summary := "Both checkers, on " ++ row.graph ++ " (" ++ row.relation ++ "). Megalodon inside HOTG: " ++
    row.megalodonVerdict ++ ". Lean: " ++ row.leanReading ++ "."
  evidence := [.external (megalodon row.megalodonTheorems), cites row.leanCited]

def crossWitnessOf (row : CrossCheck) : Witness where
  id := row.id
  observer := "graph-decoration"
  left := row.source
  right := row.target
  case := "The " ++ row.graph ++ ": " ++ row.shape ++ "."
  leftVerdict := { reading := "Checked by Megalodon inside HOTG: " ++ row.megalodonVerdict ++ "."
                   evidence := [.external (megalodon row.megalodonTheorems)] }
  rightVerdict := { reading := "Checked by Lean on hypersets: " ++ row.leanReading ++ "."
                    evidence := [cites row.leanCited] }

def crossArrows : List Arrow :=
  (crossChecks.filter fun row => row.placement != .separation).map fun row =>
    let arrow := crossArrowOf row
    if row.placement == .both then
      { arrow with
        id := row.id ++ "-on-the-bubble"
        contract := { entries := [.keeps .verdicts row.leanDeclarations
          (row.graph ++ ", on accessible points")] } }
    else arrow

def crossWitnesses : List Witness :=
  (crossChecks.filter fun row => row.placement != .agreement).map crossWitnessOf ++
  [{ id := "native-quine-atom", observer := "quine-atom"
     left := "hotg-child", right := "hyperset-top"
     case := "A set equal to its own singleton, x = {x}, for the native membership of each."
     leftVerdict := {
       reading := "None: Megalodon checks inside HOTG that no set is its own singleton, and in \
         Lean membership induction, which holds in ZFSet, excludes one."
       evidence := [.external (megalodon ["no_quine_atom", "native_no_quine_atom"]),
         cites [``Mettapedia.SetTheory.Profiles.noQuineAtom_of_induction,
           ``Mettapedia.SetTheory.Profiles.zfSet_memInduction]] }
     rightVerdict := {
       reading := "Ω = {Ω} is a hyperset; HOTG reaches it only as a graph code under \
         interpreted membership, up to bisimilarity."
       evidence := [cites [``Mettapedia.SetTheory.Profiles.hset_hasQuineAtom,
           ``Mettapedia.TypeTheory.MaterialSets.Hypersets.HSet.mem_quineAtom],
         .external (megalodon ["native_vs_interpreted", "interpreted_quine_atom"])] } }]

/-! ## Two presentations called HOTG -/

def presentationNodes : List Node := [
  { id := "c-hotg-seeds", question := "hotg-presentations", title := "C megalodon-hotg seeds"
    summary := "The C draft's profile: the eleven laws seeded, separation among them, the \
      choice operator typed with no law, no function or propositional extensionality."
    cProfile := some "megalodon-hotg" },
  { id := "megalodon-preamble-hotg", question := "hotg-presentations",
    title := "Megalodon HOTG (preamble)"
    summary := "Megalodon's HOTG: the choice operator with its axiom, function and propositional \
      extensionality as axioms, separation and excluded middle derived from choice." }
]

def presentationWitness : Witness where
  id := "separation-and-choice"
  observer := "law-status"
  left := "c-hotg-seeds"
  right := "megalodon-preamble-hotg"
  case := "The status of separation, of the choice law, of excluded middle, and of function \
    and propositional extensionality."
  leftVerdict := {
    reading := "Separation is a seeded law; no choice law is seeded, so a curriculum that needs \
      one declares it; function and propositional extensionality are not seeded."
    evidence := [
      .argument cProfileFile.key "a choice law remains an explicit additional assumption"
        "The profile types the choice operator and leaves its law as an explicit additional \
        assumption.",
      .argument lawInventory.key "the C profile seeds separation directly and seeds no choice law"
        "Separation is a seed of the C profile, and no choice law is seeded.",
      .argument lawInventory.key "not seeded by the C profile"
        "Function and propositional extensionality are not seeded by the C profile.",
      .fixture "prime" "profiles/megalodon_hotg/scoped/curriculum_naproche"
        ["[(type-face cantor (cites (cantor-core)) (rests-on (powerLaw separationLaw)))]",
          "[EpsI]"]] }
  rightVerdict := {
    reading := "The choice axiom, function extensionality and propositional extensionality are \
      axioms of the preamble; separation is a constant defined from replacement and the choice \
      operator, its laws are library theorems, and excluded middle is derived from choice."
    evidence := [
      .external (megalodon [] ["Eps_i_ax", "func_ext", "prop_ext", "Sep", "SepI", "SepE", "xm"]),
      .argument lawInventory.key "the library defines Sep with the choice operator Eps_i"
        "Separation is not an axiom of the foundation: the library defines Sep with the choice \
        operator and if-then-else, itself defined by the choice operator.",
      .argument megalodonLibrary.key "Definition If_i : prop->set->set->set := (fun p x y => Eps_i"
        "If-then-else, used to define Sep, is defined by the choice operator.",
      .argument megalodonLibrary.key "Theorem xm : forall P:prop, P \\/ ~P."
        "Excluded middle is a theorem of the library.",
      .argument megalodonLibrary.key "exact (Eps_i_ax p1 Empty L1)"
        "Its proof applies the choice axiom to two predicates on the empty set and its power set, \
        as Diaconescu's argument does."] }

/-- The questions. -/
def questions : List Question := [
  { id := "heyting-carve-outs"
    title := "Carve-outs of the Heyting-valued top"
    summary := "Sets valued in a frame of perspectives: the constructive top, its classical \
      part by double negation, its two-valued points, and the ground at its principal points."
    facts := [.«theorem» [
      { declaration := ``Mettapedia.SetTheory.CarveOuts.HeytingValued.Name.eval_subst },
      { declaration := ``Mettapedia.SetTheory.CarveOuts.HeytingValued.boundedLEM_iff }]] },
  { id := "well-founded-carve-outs"
    title := "Carve-outs of the hyperset top"
    summary := "Hypersets, their well-founded bubble, and HOTG as a child of the bubble."
    facts := [.«theorem» [
      { declaration := ``Mettapedia.SetTheory.CarveOuts.hsetBubble },
      { declaration := ``Mettapedia.SetTheory.CarveOuts.decorate_eq_ofZFSet }]] },
  { id := "hotg-presentations"
    title := "Two presentations called HOTG"
    summary := "The C draft's megalodon-hotg profile and Megalodon's HOTG differ in which laws \
      are seeded and which are derived from choice. Nothing is decided about it." }
]

/-- The options. -/
def nodes : List Node := [
  { id := "heyting-top", question := "heyting-carve-outs", title := "The Heyting-valued top"
    summary := "Names valued in a frame; constructive, bounded excluded middle fails off the \
      Boolean frames."
    facts := [.«theorem» [
      { declaration := ``Mettapedia.SetTheory.CarveOuts.HeytingValued.chain_lem_ne_top,
        choiceFree := true }]] },
  { id := "double-negation-part", question := "heyting-carve-outs"
    title := "The double-negation part"
    summary := "Names valued in the complete Boolean algebra of regular elements; classical." },
  { id := "two-valued-points", question := "heyting-carve-outs"
    title := "Two-valued points"
    summary := "Completely prime filters of the double-negation part, one verdict each." },
  { id := "principal-ground", question := "heyting-carve-outs"
    title := "The ground at principal points"
    summary := "ZFSet, through the collapse at an atom." },
  { id := "hyperset-top", question := "well-founded-carve-outs", title := "Hypersets"
    summary := "Graphs modulo bisimilarity; every graph has one decoration." },
  { id := "well-founded-bubble", question := "well-founded-carve-outs"
    title := "The well-founded bubble"
    summary := "The accessible part of membership; ZFSet; membership induction holds." },
  { id := "hotg-child", question := "well-founded-carve-outs", title := "HOTG"
    summary := "The bubble with universes, a choice operator and higher-order quantification, \
      all declared."
    cProfile := some "megalodon-hotg" }
]

/-- The observers of the witnesses. -/
def observers : List Observer := [
  { id := "carve-out-identifies", title := "Identification by a carve-out"
    reads := "Whether the carve-out gives the two cases the same reading."
    kind := .«theorem», identifies := true },
  { id := "graph-decoration", title := "Decoration of a graph"
    reads := "Whether a pointed graph has a decoration, and which, as each checker proves it."
    kind := .external },
  { id := "law-status", title := "Status of a law"
    reads := "Whether a law is seeded, an axiom, or derived, and from what."
    kind := .external }
]

def arrowOf (record : Record) : Arrow where
  id := record.arrowId
  source := record.arrowSource
  target := record.arrowTarget
  kind := record.arrowKind
  grades := record.arrowGrades
  summary := record.arrowSummary
  evidence := cites record.arrowTheorems :: record.external.map .external
  contract := record.contract

def witnessOf (record : Record) : Witness where
  id := record.witnessId
  observer := "carve-out-identifies"
  left := record.coarse
  right := record.fine
  case := record.case
  leftVerdict := { reading := record.coarseReading, evidence := [cites record.witnessTheorems] }
  rightVerdict := { reading := record.fineReading, evidence := [cites record.witnessTheorems] }

def recordWitnesses : List Witness :=
  records.map witnessOf

def arrows : List Arrow :=
  records.map arrowOf ++ crossArrows

def witnesses : List Witness :=
  recordWitnesses ++ crossWitnesses ++ [presentationWitness]

def documents : List Document :=
  [report, megalodonReport, lawInventory, cProfileFile, megalodonLibrary]

def allNodes : List Node :=
  nodes ++ presentationNodes

/-- The observer the graph of record already has for Quine atoms, for the local graph. -/
def quineAtomObserver : Observer where
  id := "quine-atom"
  title := "A Quine atom"
  reads := "Whether some set equals its own singleton."
  kind := .«theorem»

/-- The local graph of this module. -/
def graph : Graph where
  documents := documents
  questions := questions
  nodes := allNodes
  arrows := arrows
  observers := observers ++ [quineAtomObserver]
  witnesses := witnesses

theorem graph_wellFormed : graph.wellFormed = true := by
  decide +kernel

/-- Every witness of the records rests on theorems only. -/
theorem witnesses_kernelChecked : recordWitnesses.all Witness.kernelChecked = true := by
  decide +kernel

/-- **Control**: no witness resting on the external checker counts as kernel-checked. -/
theorem crossWitnesses_not_kernelChecked :
    crossWitnesses.all (fun witness => !witness.kernelChecked) = true := by
  decide +kernel

/-- A membership theorem about the well-founded subcarrier does not license the
same preservation claim for the total readout on all hypersets. -/
def totalReadoutMembershipClaim : Arrow where
  id := "total-readout-preserves-membership"
  source := "hyperset-top"
  target := "well-founded-bubble"
  kind := .observationalQuotient
  grades := [.factors]
  summary := "Control: using a subcarrier theorem to claim preservation by the total readout."
  evidence := [cites [``Mettapedia.SetTheory.CarveOuts.WellFoundedReadout.wfPart_mem_iff]]
  contract := { entries := [
    .keeps (.formulas .atomic)
      [``Mettapedia.SetTheory.CarveOuts.WellFoundedReadout.wfPart_mem_iff] "membership"] }

/-- The Quine-atom counterexample refuses the broadened claim, even though its
citation is an actual theorem. -/
theorem totalReadoutMembershipClaim_refused :
    Graph.contractsConsistent
      { graph with arrows := graph.arrows ++ [totalReadoutMembershipClaim] } = false := by
  decide +kernel

end Mettapedia.Languages.MeTTa.PrimeOptions.CarveOuts
