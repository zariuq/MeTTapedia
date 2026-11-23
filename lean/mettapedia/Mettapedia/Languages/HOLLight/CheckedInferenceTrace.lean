import Mettapedia.Languages.HOLLight.ProofSystem
import Lean.Elab.Command

/-!
# Checked HOL Light inference traces

An inference check and a formation check depend on a request and its result.
Replaying an occurrence additionally checks the premises at its recorded
addresses in the current cache.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.CheckedInferenceTrace

open Mettapedia.Languages.OpenTheory Mettapedia.Logic
open ProofExecution (Receipt)

structure Checked (policy : AxiomPolicy) [DecidablePred policy]
    (formation : RuleRequest → Theorem → Bool)
    (before after : Array Theorem) (nodes : List Receipt) : Prop where
  replayed : DerivationGraph.replayFrom (ruleWitness policy) before nodes = some after
  formed : nodes.all (fun node => formation node.witness node.conclusion) = true

namespace Checked

variable {policy : AxiomPolicy} [DecidablePred policy]
variable {formation : RuleRequest → Theorem → Bool}

theorem nil (cache : Array Theorem) : Checked policy formation cache cache [] :=
  ⟨rfl, rfl⟩

theorem cons {before after : Array Theorem} {node : Receipt} {tail : List Receipt}
    (premises : DerivationGraph.lookupPremises before node.parents = some node.witness.premises)
    (inference : node.witness.check policy = some node.conclusion)
    (formed : formation node.witness node.conclusion = true)
    (later : Checked policy formation (before.push node.conclusion) after tail) :
    Checked policy formation before after (node :: tail) := by
  have step := (ProofSystem.node_replay_iff policy before (before.push node.conclusion) node).mpr
    ⟨premises, inference, rfl⟩
  exact ⟨by simp only [DerivationGraph.replayFrom, step]; exact later.replayed,
    by simp only [List.all_cons, formed, later.formed, Bool.and_self]⟩

end Checked

open Lean Elab Command

private structure RowProof where
  receipt : Ident
  before : Ident
  accepted : Ident
  formed : Ident

private def named (site : Syntax) (stem : Ident) (field : String) (index : Nat) : Ident :=
  mkIdentFrom site (stem.getId.appendAfter ("_" ++ field ++ toString index))

declare_syntax_cat checkedHolRow
syntax ident ident "[" num,* "]" : checkedHolRow
syntax ident ident "[" num,* "]" "checked_by" ident : checkedHolRow

/-- Check closed rows against the supplied policy and formation function.
The certificate keeps the original order, addresses, and origin. -/
syntax (name := checkedHolTrace) "checked_hol_trace " ident ident ident term:max " ["
  checkedHolRow,* "]" : command

elab_rules : command
  | `(command| checked_hol_trace $stem:ident $policy:ident $formation:ident $origin:term
      [$rows:checkedHolRow,*]) => do
      let entries := rows.getElems
      let initial := named stem stem "cache" 0
      elabCommand (← `(private def $initial : Array Theorem := #[]))
      let mut tracked : Array RowProof := #[]
      let mut saved : Std.HashMap (Lean.Name × Lean.Name) (Ident × Ident) := {}
      let mut before := initial
      for (row, index) in entries.zipIdx do
        let (fact, request, parents, supplied) ← withRef row do
            match row with
            | `(checkedHolRow| $fact:ident $request:ident [$parents:num,*]) =>
                pure (fact, request, parents.getElems, none)
            | `(checkedHolRow| $fact:ident $request:ident [$parents:num,*] checked_by $check:ident) =>
                pure (fact, request, parents.getElems, some check)
            | _ => throwUnsupportedSyntax
        let addresses : Array (TSyntax `term) := parents.map (fun n => ⟨n.raw⟩)
        let receipt := named row stem "node" index
        let after := named row stem "cache" (index + 1)
        let key := (fact.getId, request.getId)
        let previous := saved[key]?
        let (accepted, formed) ← withRef row do
          elabCommand (← `(private def $receipt : Receipt :=
            ⟨$fact, .inference $request, [$addresses,*], $origin⟩))
          elabCommand (← `(private def $after : Array Theorem := ($before).push $fact))
          match previous, supplied with
            | some proofs, none => pure proofs
            | previous, supplied => do
                let accepted := named row stem "checked" index
                let proof ← match supplied with
                  | some method => `($method)
                  | none => `(by decide +kernel)
                elabCommand (← `(private theorem $accepted :
                  ($receipt).witness.check $policy = some $fact := $proof))
                match previous with
                | some (_, formed) => pure (accepted, formed)
                | none =>
                    let formed := named row stem "formed" index
                    elabCommand (← `(private theorem $formed :
                      $formation ($receipt).witness $fact = true := by decide +kernel))
                    pure (accepted, formed)
        if previous.isNone then
          saved := saved.insert key (accepted, formed)
        tracked := tracked.push { receipt, before, accepted, formed }
        before := after
      let final := before
      let mut tail := named stem stem "suffix" entries.size
      let mut checked := named stem stem "trace" entries.size
      elabCommand (← `(private def $tail : List Receipt := []))
      elabCommand (← `(private theorem $checked : Checked $policy $formation $final $final $tail :=
        Checked.nil $final))
      for (row, index) in tracked.zipIdx.reverse do
        let data := named entries[index]! stem "suffix" index
        let proof := named entries[index]! stem "trace" index
        let ⟨receipt, entry, accepted, formed⟩ := row
        withRef entries[index]! do
          elabCommand (← `(private def $data : List Receipt := $receipt :: $tail))
          elabCommand (← `(private theorem $proof : Checked $policy $formation $entry $final $data :=
            Checked.cons rfl $accepted $formed $checked))
        tail := data
        checked := proof

end Mettapedia.Languages.HOLLight.CheckedInferenceTrace
