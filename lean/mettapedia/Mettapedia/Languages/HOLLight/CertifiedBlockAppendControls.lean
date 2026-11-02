import Mettapedia.Languages.HOLLight.CertifiedBlockAppend
import Mettapedia.Languages.HOLLight.EqualityExpansion

/-! Exact cache, sharing and refusal controls for certified block append. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.CertifiedBlockAppend.Controls

open Mettapedia.Languages.OpenTheory Mettapedia.Logic.DerivationGraph
open GraphExpansion

local instance : DecidablePred emptyAxiomPolicy := fun _ => isFalse id

def first : CanonicalTerm := .free ⟨.global "first", .bool⟩
def second : CanonicalTerm := .free ⟨.global "second", .function .bool .bool⟩
def fact : Theorem := EqualityExpansion.reflexivity first
def other : Theorem := EqualityExpansion.reflexivity second
def before : ProofExecution.State := GraphExpansion.start [fact, other]
def block : ProofSystem.Certificate :=
  primitiveBlock (.inference (.trans fact fact)) fact ("duplicate-parent-append", 0)

theorem request_checked :
    (RuleRequest.inference (.trans fact fact)).check emptyAxiomPolicy = some fact := by
  change checkTrans fact fact = some fact
  simpa [EqualityExpansion.transResult, fact, EqualityExpansion.reflexivity,
    Theorem.unionResult, Theorem.emptyResult] using
    EqualityExpansion.transResult_checked fact fact first first first rfl
      (EqualityExpansion.equality_view first first rfl) (EqualityExpansion.equality_view first first rfl)

theorem block_checked : BlockChecked emptyAxiomPolicy [fact, fact] fact block :=
  primitiveBlock_checked (.inference (.trans fact fact)) fact ("duplicate-parent-append", 0) request_checked

def result : ProofExecution.State × Nat :=
  append before [0, 0] block rfl block_checked

theorem matches_original : emitBlock emptyAxiomPolicy [0, 0] block before = some result :=
  matches_replay before [0, 0] block rfl block_checked

theorem cache_exact : result.1.cache = #[fact, other, fact] := rfl
theorem root_exact : result.2 = 2 := by decide
theorem duplicate_parents : (result.1.receipts[0]?).map (·.parents) = some [0, 0] := by decide
theorem old_fact_retained : result.1.cache[1]? = some other := rfl

theorem fact_ne_other : fact ≠ other := by
  intro same
  have terms := congrArg (fun factValue : Theorem => factValue.sequent.concl.term) same
  have operands := (DBTerm.app.inj terms).2
  have fieldsSame := DBTerm.free.inj operands
  have types := congrArg (fun slotValue : SourceVar => slotValue.ty) fieldsSame
  have arities := (Ty.op.inj types).2
  cases arities

private theorem rejected_node (cache : Array Theorem) (node : ProofExecution.Receipt)
    (bad : (lookupPremises cache node.parents ≠ some node.witness.premises) ∨
      (node.witness.check emptyAxiomPolicy ≠ some node.conclusion)) :
    replayFrom (ruleWitness emptyAxiomPolicy) cache [node] = none := by
  cases step : node.replay (ruleWitness emptyAxiomPolicy) cache with
  | none => simp [replayFrom, step]
  | some next =>
      have checked := (ProofSystem.node_replay_iff emptyAxiomPolicy cache next node).mp step
      exact False.elim (bad.elim (fun wrong => wrong checked.1) (fun wrong => wrong checked.2.1))

theorem wrong_premise_refused : emitBlock emptyAxiomPolicy [1, 0] block before = none := by
  have refused := rejected_node before.cache
    ⟨fact, .inference (.trans fact fact), [1, 0], ("duplicate-parent-append", 0)⟩
    (Or.inl (by
      intro same
      have equal : [other, fact] = [fact, fact] := Option.some.inj same
      exact fact_ne_other (List.cons.inj equal).1.symm))
  change (do
    let cache ← replayFrom (ruleWitness emptyAxiomPolicy) before.cache
      [⟨fact, .inference (.trans fact fact), [1, 0], ("duplicate-parent-append", 0)⟩]
    let _ ← cache[2]?
    pure (({cache := cache, receipts := before.receipts ++
      (expandBlock [1, 0] before.cache.size block).1.toArray} : ProofExecution.State), (2 : Nat))) = none
  rw [refused]
  rfl
theorem future_premise_refused : emitBlock emptyAxiomPolicy [2, 0] block before = none := by decide
theorem missing_premises_refused : emitBlock emptyAxiomPolicy [] block before = none := by decide
theorem future_result_refused : emitBlock emptyAxiomPolicy [0, 0] (block.1, 100) before = none := by
  obtain ⟨cache, replayed, _⟩ := expandBlock_checked (cache := before.cache) (roots := [0, 0]) rfl block_checked
  have same := replayFrom_eq_materialize (ruleWitness emptyAxiomPolicy) replayed
  have replayPrefix : replayFrom (ruleWitness emptyAxiomPolicy) before.cache
      (expandBlock [0, 0] before.cache.size block).1 = some result.1.cache :=
    replayed.trans (congrArg some same)
  change (do
    let cache ← replayFrom (ruleWitness emptyAxiomPolicy) before.cache
      (expandBlock [0, 0] before.cache.size block).1
    let _ ← cache[100]?
    pure (({cache := cache, receipts := before.receipts ++
      (expandBlock [0, 0] before.cache.size block).1.toArray} : ProofExecution.State), (100 : Nat))) = none
  rw [replayPrefix]
  rfl

def forged : ProofSystem.Certificate :=
  ([⟨other, .inference (.trans fact fact), [0, 1], ("forged-append", 0)⟩], 2)

theorem forged_conclusion_refused : emitBlock emptyAxiomPolicy [0, 0] forged before = none := by
  have refused := rejected_node before.cache
    ⟨other, .inference (.trans fact fact), [0, 0], ("forged-append", 0)⟩
    (Or.inr (by
      rw [request_checked]
      intro same
      exact fact_ne_other (Option.some.inj same)))
  change (do
    let cache ← replayFrom (ruleWitness emptyAxiomPolicy) before.cache
      [⟨other, .inference (.trans fact fact), [0, 0], ("forged-append", 0)⟩]
    let _ ← cache[2]?
    pure (({cache := cache, receipts := before.receipts ++
      (expandBlock [0, 0] before.cache.size forged).1.toArray} : ProofExecution.State), (2 : Nat))) = none
  rw [refused]
  rfl

#print axioms block_checked
#print axioms matches_original
#print axioms cache_exact
#print axioms duplicate_parents
#print axioms wrong_premise_refused
#print axioms forged_conclusion_refused

end Mettapedia.Languages.HOLLight.CertifiedBlockAppend.Controls
