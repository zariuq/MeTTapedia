import Mettapedia.Logic.LP.FirstOrderConnectionSoundness
import Mettapedia.Logic.LP.FirstOrderConnectionSearch
import Mettapedia.Logic.LP.StandardizeApart

/-!
# Per-use scoped clauses in the existing first-order connection checker

The source matrix keeps its authored variables. Runtime proof objects use
the existing proof format over `ScopedVar`: root variables occupy scope zero,
and every extension checks an actual clause copy at its next activation
scope before incrementing the counter. Reductions keep the current counter
and the branch-local ancestor paths. No new term or proof syntax is required.

The clause-source replay below is the existing replay protocol with an
explicit next-copy coordinate. The constant-source profile agrees with the
fixed-variable checker; the scoped source computes each copy using the
existing `Atom.atScope` operation.
-/

namespace Mettapedia.Logic.LP

noncomputable section

variable {σ : LPSignature}

def ConnFOLit.atScope (scope : Nat) : ConnFOLit σ → ConnFOLit σ.scoped
  | .pos atom => .pos (atom.atScope scope)
  | .neg atom => .neg (atom.atScope scope)

def connFOClauseAtScope (scope : Nat) (clause : ConnFOClause σ) : ConnFOClause σ.scoped :=
  clause.map (ConnFOLit.atScope scope)

def connFOMatrixAtScope (clauses : ConnFOCNF σ) (scope : Nat) : ConnFOCNF σ.scoped :=
  clauses.map (connFOClauseAtScope scope)

variable [DecidableEq σ.vars] [DecidableEq σ.constants]
  [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]

def replayFOClauseSource (source : Nat → ConnFOCNF σ) (uFuel : Nat)
    (nextScope : Nat) (agenda : ConnFOAgenda σ) : FOProofTrace σ → Bool
  | [] => decide (agenda = [])
  | step :: steps =>
      match agenda with
      | [] => false
      | ⟨literal, path⟩ :: rest =>
          match step with
          | .step_reduce selected =>
              if selected ∈ path then
                match unifyComplementLit? uFuel literal selected with
                | some substitution => replayFOClauseSource source uFuel nextScope
                    (substitution.applyConnFOAgenda rest) steps
                | none => false
              else false
          | .step_extend clause selected =>
              if clause ∈ source nextScope ∧ selected ∈ clause then
                match unifyComplementLit? uFuel literal selected with
                | some substitution => replayFOClauseSource source uFuel (nextScope + 1)
                    (substitution.applyConnFOAgenda
                      (connectionGoals (clause.erase selected) (literal :: path) ++ rest)) steps
                | none => false
              else false

theorem replayFOClauseSource_constant (clauses : ConnFOCNF σ) (uFuel : Nat) :
    ∀ (trace : FOProofTrace σ) (agenda : ConnFOAgenda σ) (nextScope : Nat),
      replayFOClauseSource (fun _ => clauses) uFuel nextScope agenda trace =
        replayFOAgenda clauses uFuel agenda trace
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | step :: steps, ⟨literal, path⟩ :: rest, nextScope => by
      cases step with
      | step_reduce selected =>
          by_cases member : selected ∈ path
          · simp only [replayFOClauseSource, replayFOAgenda, if_pos member]
            cases unified : unifyComplementLit? uFuel literal selected with
            | none => rfl
            | some substitution => exact replayFOClauseSource_constant clauses uFuel steps _ nextScope
          · simp [replayFOClauseSource, replayFOAgenda, member]
      | step_extend clause selected =>
          by_cases member : clause ∈ clauses ∧ selected ∈ clause
          · simp only [replayFOClauseSource, replayFOAgenda, if_pos member]
            cases unified : unifyComplementLit? uFuel literal selected with
            | none => rfl
            | some substitution => exact replayFOClauseSource_constant clauses uFuel steps _ (nextScope + 1)
          · simp [replayFOClauseSource, replayFOAgenda, member]

/-- Replay a proof whose runtime clauses are checked against their exact
computed activation scope. The root is checked at scope zero. -/
def checkProofScopedFO (clauses : ConnFOCNF σ) (uFuel : Nat) (proof : FOProofObj σ.scoped) : Bool :=
  decide (proof.root ∈ connFOMatrixAtScope clauses 0) &&
    replayFOClauseSource (connFOMatrixAtScope clauses) uFuel 1
      (connectionGoals proof.root []) proof.trace

def connProveFOClauseSourceDFS (source : Nat → ConnFOCNF σ) (uFuel : Nat)
    (nextScope : Nat) (agenda : ConnFOAgenda σ) : Nat → Option (FOProofTrace σ)
  | 0 => if agenda = [] then some [] else none
  | fuel + 1 =>
      match agenda with
      | [] => some []
      | ⟨literal, path⟩ :: rest =>
          match tryReducePathFO
            (fun agenda => connProveFOClauseSourceDFS source uFuel nextScope agenda fuel)
            uFuel literal rest path path with
          | some trace => some trace
          | none => tryExtendFO
              (fun agenda => connProveFOClauseSourceDFS source uFuel (nextScope + 1) agenda fuel)
              uFuel literal rest path (source nextScope)

def connProveScopedFODFS (clauses : ConnFOCNF σ) (uFuel fuel : Nat)
    (root : ConnFOClause σ) : Option (FOProofObj σ.scoped) :=
  if root ∈ clauses then
    (connProveFOClauseSourceDFS (connFOMatrixAtScope clauses) uFuel 1
      (connectionGoals (connFOClauseAtScope 0 root) []) fuel).map
      (fun trace => ⟨fuel, connFOClauseAtScope 0 root, trace⟩)
  else none

end

end Mettapedia.Logic.LP
