import Mettapedia.SetTheory.AntiFoundation.Distinctions
import Mettapedia.SetTheory.AntiFoundation.Consumers

/-!
# The five picture axioms on one ledger

Foundation, Aczel, Scott, Finsler and Boffa, read on the finite menu of
pictures. The ledger records how many Quine atoms each carrier has, whether
membership induction survives, which equation systems have one solution, the
embeddings of the carriers, and which denotation factors through which.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Profiles

open Mettapedia.SetTheory.AntiFoundation
open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.GSLT.QuotientObservers
open Mettapedia.TypeTheory.MaterialSets.Hypersets

/-- What the five picture axioms keep, on the finite carriers. -/
structure AntiFoundationLedger : Prop where
  foundationLoopNone : ∀ d : Loop → FoundSet, ¬ IsDecoration loopEdge foundMem d
  foundationNestNone : ∀ d : Nest → FoundSet, ¬ IsDecoration nestEdge foundMem d
  foundInduction : HasMemInduction foundMem
  foundNoQuine : ¬ HasQuineAtom foundMem
  aSetStrong : StronglyExtensional (memChild aMem)
  aSetOneQuine : ∀ x : ASet, IsQuine aMem x ↔ x = ASet.omega
  sSetOneQuine : ∀ x : SSet, IsQuine sMem x ↔ x = SSet.omega
  fSetOneQuine : ∀ x : FSet, IsQuine fMem x ↔ x = FSet.omega
  aSetRefutesInduction : ¬ HasMemInduction aMem
  sSetRefutesInduction : ¬ HasMemInduction sMem
  fSetRefutesInduction : ¬ HasMemInduction fMem
  bSetRefutesInduction : ¬ HasMemInduction bMem
  bSetTwoQuines : IsQuine bMem BSet.atomA ∧ IsQuine bMem BSet.atomB ∧
    BSet.atomA ≠ BSet.atomB
  aSetAcc : ∀ x : ASet, Acc aMem x ↔ x = ASet.empty
  sSetAcc : ∀ x : SSet, Acc sMem x ↔ x = SSet.empty
  fSetAcc : ∀ x : FSet, Acc fMem x ↔ x = FSet.empty
  bSetAcc : ∀ x : BSet, Acc bMem x ↔ x = BSet.empty
  wfPart : ∀ {V : Type} (mem : V → V → Prop),
    HasMemInduction (fun a b : {x : V // Acc mem x} => mem a.1 b.1)
  afaLoop : CanonicalAxiom loopEdge (Bisimilar loopEdge loopEdge) aMem
  scottTwo : ∃ d d' : Scott → SSet, IsDecoration scottEdge sMem d ∧
    IsDecoration scottEdge sMem d' ∧ d Scott.s1 ≠ d' Scott.s1
  scottCanon : CanonicalAxiom scottEdge (fun a b : Scott => a = b) sMem
  finThree : ∃ d1 d2 d3 : Fin3 → FSet, IsDecoration finEdge fMem d1 ∧
    IsDecoration finEdge fMem d2 ∧ IsDecoration finEdge fMem d3 ∧
    d1 Fin3.n1 ≠ d2 Fin3.n1 ∧ d2 Fin3.n1 ≠ d3 Fin3.n1 ∧ d1 Fin3.n1 ≠ d3 Fin3.n1
  finCanon : CanonicalAxiom finEdge (fun a b : Fin3 => a = b) fMem
  bafaLoopNotUnique : ∃ d d' : Loop → BSet, IsDecoration loopEdge bMem d ∧
    IsDecoration loopEdge bMem d' ∧ d Loop.node ≠ d' Loop.node
  bafaLoopNotCanonical : ¬ CanonicalAxiom loopEdge (fun a b : Loop => a = b) bMem
  bafaCycleTwo : ∃ d d' : Cycle → BSet, IsDecoration cycleEdge bMem d ∧
    IsDecoration cycleEdge bMem d' ∧ d Cycle.l ≠ d' Cycle.l
  factorsBafaFafa : Factors denoteBAFA denoteFAFA
  factorsFafaSafa : Factors denoteFAFA denoteSAFA
  factorsSafaAfa : Factors denoteSAFA denoteAFA
  factorsAfaFound : Factors denoteAFA denoteFoundation
  notFactorsFoundAfa : ¬ Factors denoteFoundation denoteAFA
  notFactorsAfaSafa : ¬ Factors denoteAFA denoteSAFA
  notFactorsSafaFafa : ¬ Factors denoteSAFA denoteFAFA
  notFactorsFafaBafa : ¬ Factors denoteFAFA denoteBAFA
  afaEmbedMem : ∀ x y : ASet, aMem x y ↔ sMem (afaToSafa x) (afaToSafa y)
  afaEmbedInj : ∀ {x y : ASet}, afaToSafa x = afaToSafa y → x = y
  safaEmbedMem : ∀ x y : SSet, sMem x y ↔ fMem (safaToFafa x) (safaToFafa y)
  safaEmbedInj : ∀ {x y : SSet}, safaToFafa x = safaToFafa y → x = y
  fafaEmbedMem : ∀ x y : FSet, fMem x y ↔ bMem (fafaToBafa x) (fafaToBafa y)
  fafaEmbedInj : ∀ {x y : FSet}, fafaToBafa x = fafaToBafa y → x = y
  labelRespects : Respects LabelledBisimilar firstLabel
  labelForgetsUnlabelled : ¬ Respects (Bisimilar ustep ustep) firstLabel
  bafaForgetsLabelled : ¬ Respects LabelledBisimilar bafaProc

/-- The five picture axioms, packed. -/
theorem antiFoundationLedger : AntiFoundationLedger where
  foundationLoopNone := foundation_loop_none
  foundationNestNone := foundation_nest_none
  foundInduction := found_induction
  foundNoQuine := found_no_quine
  aSetStrong := aSet_strong
  aSetOneQuine := aSet_quine_iff
  sSetOneQuine := sSet_quine_iff
  fSetOneQuine := fSet_quine_iff
  aSetRefutesInduction := aSet_refutes_induction
  sSetRefutesInduction := sSet_refutes_induction
  fSetRefutesInduction := fSet_refutes_induction
  bSetRefutesInduction := bSet_refutes_induction
  bSetTwoQuines := bSet_two_quines
  aSetAcc := aSet_acc_iff
  sSetAcc := sSet_acc_iff
  fSetAcc := fSet_acc_iff
  bSetAcc := bSet_acc_iff
  wfPart := wf_part_induction
  afaLoop := afa_loop_canonical
  scottTwo := scott_two_solutions
  scottCanon := scott_canonical_axiom
  finThree := fin_three_solutions
  finCanon := fin_canonical_axiom
  bafaLoopNotUnique := loop_not_unique_bafa
  bafaLoopNotCanonical := bafa_loop_not_canonical
  bafaCycleTwo := bafa_cycle_two
  factorsBafaFafa := factors_bafa_fafa
  factorsFafaSafa := factors_fafa_safa
  factorsSafaAfa := factors_safa_afa
  factorsAfaFound := factors_afa_found
  notFactorsFoundAfa := not_factors_found_afa
  notFactorsAfaSafa := not_factors_afa_safa
  notFactorsSafaFafa := not_factors_safa_fafa
  notFactorsFafaBafa := not_factors_fafa_bafa
  afaEmbedMem := afaToSafa_mem
  afaEmbedInj := afaToSafa_inj
  safaEmbedMem := safaToFafa_mem
  safaEmbedInj := safaToFafa_inj
  fafaEmbedMem := fafaToBafa_mem
  fafaEmbedInj := fafaToBafa_inj
  labelRespects := label_respects_labelled
  labelForgetsUnlabelled := label_not_respects_unlabelled
  bafaForgetsLabelled := bafa_not_respects_labelled

end Mettapedia.SetTheory.Profiles
