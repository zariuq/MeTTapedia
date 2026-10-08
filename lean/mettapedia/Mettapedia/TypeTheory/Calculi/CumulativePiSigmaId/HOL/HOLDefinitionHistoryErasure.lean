import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLDefinitionPrefix
import Mettapedia.Logic.HOL.DefinitionHistorySemantics

/-!
# Expansion of actual checked HOL/native definition prefixes

The existing native admission prefix determines its constant-expansion
history. Its constructed final model agrees with the model obtained from that
history. Expansion is therefore available for terms containing newly admitted
names as well as for embedded old terms. The retained proof translation keeps
hypothesis positions and ordered rule occurrences.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLDefinitionPrefix

open Mettapedia.Logic

universe u v w

variable {Base : Type u} {initial final : State.{u, v, w} Base}

def CheckedPrefix.history {initial final : State.{u, v, w} Base}
    (chain : CheckedPrefix initial final) :
    HOL.DefinitionHistory initial.Const final.Const :=
  match chain with
  | .nil => .nil
  | .snoc prior _ body _ => .add prior.history _ body

theorem CheckedPrefix.history_model (chain : CheckedPrefix initial final) :
    chain.history.extendModel initial.model = final.model := by
  induction chain with
  | nil => rfl
  | @snoc prior earlier name type body fresh ih =>
      change (earlier.history.extendModel initial.model).definitionExtension body =
        prior.model.definitionExtension body
      rw [ih]

theorem CheckedPrefix.history_embed (chain : CheckedPrefix initial final)
    {context : HOL.Ctx Base} {type : HOL.Ty Base}
    (term : HOL.Term initial.Const context type) :
    chain.history.embed term = chain.embed term := by
  induction chain with
  | nil => exact HOL.mapConst_id term
  | @snoc prior earlier name type body fresh ih =>
      change HOL.mapConst (fun constant => HOL.DefinedConst.old (earlier.history.embedding constant))
        term = HOL.DefinedConst.embed (earlier.embed term)
      rw [← ih]
      exact (HOL.mapConst_comp _ _ term).symm

theorem CheckedPrefix.erase_embed (chain : CheckedPrefix initial final)
    {context : HOL.Ctx Base} {type : HOL.Ty Base}
    (term : HOL.Term initial.Const context type) :
    chain.history.erase (chain.embed term) = term := by
  rw [← chain.history_embed term]
  exact chain.history.erase_embed term

/-- Newly admitted formulas receive the meaning of their actual expansion. -/
theorem CheckedPrefix.models_erasure (chain : CheckedPrefix initial final)
    (formula : HOL.ClosedFormula final.Const) :
    final.model.models formula ↔ initial.model.models (chain.history.erase formula) := by
  rw [← chain.history_model]
  exact chain.history.models_erasure initial.model formula

def CheckedPrefix.eraseProof (chain : CheckedPrefix initial final)
    {context : HOL.Ctx Base} {assumptions : List (HOL.Formula final.Const context)}
    {conclusion : HOL.Formula final.Const context}
    (proof : HOL.ProofSyntax final.Const assumptions conclusion) :
    HOL.ProofSyntax initial.Const (assumptions.map chain.history.erase)
      (chain.history.erase conclusion) := chain.history.eraseProof proof

theorem CheckedPrefix.eraseProof_rootObservation (chain : CheckedPrefix initial final)
    {context : HOL.Ctx Base} {assumptions : List (HOL.Formula final.Const context)}
    {conclusion : HOL.Formula final.Const context}
    (proof : HOL.ProofSyntax final.Const assumptions conclusion) :
    (chain.eraseProof proof).rootObservation = proof.rootObservation :=
  HOL.ProofSyntax.substConst_rootObservation chain.history.images proof

theorem CheckedPrefix.eraseProof_nodeCount (chain : CheckedPrefix initial final)
    {context : HOL.Ctx Base} {assumptions : List (HOL.Formula final.Const context)}
    {conclusion : HOL.Formula final.Const context}
    (proof : HOL.ProofSyntax final.Const assumptions conclusion) :
    (chain.eraseProof proof).nodeCount = proof.nodeCount :=
  chain.history.eraseProof_nodeCount proof

theorem CheckedPrefix.eraseProof_ruleTree (chain : CheckedPrefix initial final)
    {context : HOL.Ctx Base} {assumptions : List (HOL.Formula final.Const context)}
    {conclusion : HOL.Formula final.Const context}
    (proof : HOL.ProofSyntax final.Const assumptions conclusion) :
    HOL.ProofSyntax.ruleTree (chain.eraseProof proof).observe =
      HOL.ProofSyntax.ruleTree proof.observe :=
  chain.history.eraseProof_ruleTree proof

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLDefinitionPrefix
