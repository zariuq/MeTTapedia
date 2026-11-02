import Mettapedia.GSLT.LanguageDef.FirstOrderRules
import Mettapedia.TypeTheory.PromotionAdmission.Unification

/-! Bounded candidate production with premise-determined names. The search
uses the shared proved occurs-checked unifier, freshens each rule invocation,
and threads one substitution through ordered premises. Explicit seeds retain
the caller's theorem and substitution choices. The final checking boundary is
the actual admitted calculus. Exhaustion never establishes underivability. -/

set_option autoImplicit false
namespace Mettapedia.GSLT.LanguageDef.FirstOrderPremiseSearch

open Mettapedia.OSLF.MeTTaIL.Syntax
open FirstOrderRules InferenceChecker
open Mettapedia.TypeTheory

abbrev UTerm := PromotionAdmission.Term String Nat
abbrev Substitution := Nat → UTerm

inductive Seed where
  | node (rule : String) (arguments : List Pattern) (children : List (Option Seed))

structure Limits where
  steps : Nat
  depth : Nat
  unification : Nat

inductive Outcome where
  | candidate (article : RawProof)
  | noCandidate
  | exhausted (reason : String)
  | fault (reason : String)
  deriving Repr

structure Report where
  outcome : Outcome
  steps : Nat
  attempts : Nat
  deriving Repr

mutual
def schema (names : List (String × Nat)) : Pattern → Except String UTerm
  | .fvar name => do
      let some entry := names.find? (fun entry => entry.1 == name) |
        throw s!"undeclared rule variable: {name}"
      return .var entry.2
  | .apply head arguments => return .app head (← schemas names arguments)
  | _ => .error "outside the application-only first-order fragment"

def schemas (names : List (String × Nat)) : List Pattern → Except String (List UTerm)
  | [] => .ok []
  | first :: rest => return (← schema names first) :: (← schemas names rest)
end

mutual
def ground : UTerm → Option Pattern
  | .var _ => none
  | .app head arguments => return .apply head (← grounds arguments)

def grounds : List UTerm → Option (List Pattern)
  | [] => some []
  | first :: rest => return (← ground first) :: (← grounds rest)
end

structure Goal where
  term : UTerm
  seed : Option Seed
  slot : Nat
  depth : Nat

structure Node where
  slot : Nat
  rule : String
  arguments : List UTerm
  children : List Nat

structure Branch where
  pending : List Goal
  substitution : Substitution
  nodes : List Node
  nextVariable : Nat
  nextNode : Nat

inductive Work where
  | enter (branch : Branch)
  | alternatives (branch : Branch) (goal : Goal) (remaining : List Goal) (rules : List FORule)

private def candidates (rules : List FORule) (goal : Goal) (substitution : Substitution) :
    Except String (List FORule) := do
  match goal.seed with
  | some (.node name _ _) =>
      let some rule := rules.find? (fun rule => rule.id == name) | throw s!"unknown seeded rule: {name}"
      return [rule]
  | none =>
      match goal.term.subst substitution with
      | .var _ => throw "undetermined judgment head"
      | .app head _ => return rules.filter fun rule =>
          match rule.conclusion with
          | .apply actual _ => actual == head
          | _ => false

private def activate (allowance : Nat) (branch : Branch) (goal : Goal) (_remaining : List Goal) (rule : FORule) :
    Except String (PromotionAdmission.UnifyResult String Nat × List UTerm × List UTerm × List (Option Seed)) := do
  let names := rule.vars.zip ((List.range rule.vars.length).map (branch.nextVariable + ·))
  let conclusion ← schema names rule.conclusion
  let premises ← schemas names rule.premises
  let arguments := names.map (fun entry => (PromotionAdmission.Term.var entry.2 : UTerm))
  let mut equations := [(conclusion, goal.term)]
  let mut seeds := List.replicate premises.length none
  if let some (.node _ supplied children) := goal.seed then
    unless supplied.length = arguments.length do throw "seed argument arity"
    unless children.length = premises.length do throw "seed premise arity"
    let supplied ← schemas [] supplied
    equations := equations ++ arguments.zip supplied
    seeds := children
  let instantiated := equations.map fun pair =>
    (pair.1.subst branch.substitution, pair.2.subst branch.substitution)
  return (PromotionAdmission.unify allowance instantiated, arguments, premises, seeds)

private def assemble (nodes : List Node) (substitution : Substitution) : Nat → Nat → Option RawProof
  | 0, _ => none
  | fuel + 1, slot => do
      let node ← nodes.find? (fun node => node.slot == slot)
      let arguments ← grounds (node.arguments.map (·.subst substitution))
      let children ← node.children.mapM (assemble nodes substitution fuel)
      return .node ⟨⟨node.rule⟩, arguments⟩ children

private def loop (rules : List FORule) (unificationAllowance : Nat) (truncated : Option String) :
    Nat → List Work → Nat → Nat → Report
  | _, [], steps, attempts =>
      ⟨match truncated with | some reason => .exhausted reason | none => .noCandidate, steps, attempts⟩
  | 0, _, steps, attempts => ⟨.exhausted "steps", steps, attempts⟩
  | fuel + 1, .enter branch :: later, steps, attempts =>
      match branch.pending with
      | [] =>
          match assemble branch.nodes branch.substitution (branch.nodes.length + 1) 0 with
          | some article => ⟨.candidate article, steps + 1, attempts⟩
          | none => loop rules unificationAllowance truncated fuel later (steps + 1) attempts
      | goal :: remaining =>
          if goal.depth = 0 then
            loop rules unificationAllowance (truncated.or (some "depth")) fuel later (steps + 1) attempts
          else
          match candidates rules goal branch.substitution with
          | .error reason => ⟨.fault reason, steps + 1, attempts⟩
          | .ok choices => loop rules unificationAllowance truncated fuel
              (.alternatives branch goal remaining choices :: later) (steps + 1) attempts
  | fuel + 1, .alternatives _ _ _ [] :: later, steps, attempts =>
      loop rules unificationAllowance truncated fuel later (steps + 1) attempts
  | fuel + 1, .alternatives branch goal remaining (rule :: choices) :: later, steps, attempts =>
      let alternatives := Work.alternatives branch goal remaining choices :: later
      match activate unificationAllowance branch goal remaining rule with
      | .error reason => ⟨.fault reason, steps + 1, attempts + 1⟩
      | .ok (.outOfFuel, _, _, _) =>
          loop rules unificationAllowance (truncated.or (some "unification")) fuel alternatives (steps + 1) (attempts + 1)
      | .ok (.fail, _, _, _) => loop rules unificationAllowance truncated fuel alternatives (steps + 1) (attempts + 1)
      | .ok (.ok substitution, arguments, premises, seeds) =>
          let childSlots := (List.range premises.length).map (branch.nextNode + ·)
          let children := (premises.zip seeds).zip childSlots |>.map fun ((term, seed), slot) =>
            (⟨term, seed, slot, goal.depth - 1⟩ : Goal)
          let node : Node := ⟨goal.slot, rule.id, arguments, childSlots⟩
          let next : Branch := ⟨children ++ remaining,
            fun identifier => (branch.substitution identifier).subst substitution,
            node :: branch.nodes, branch.nextVariable + rule.vars.length,
            branch.nextNode + premises.length⟩
          loop rules unificationAllowance truncated fuel (.enter next :: alternatives) (steps + 1) (attempts + 1)

def search (rules : List FORule) (goal : Pattern) (seed : Option Seed) (limits : Limits) : Report :=
  if (rules.map FORule.id).eraseDups.length ≠ rules.length then ⟨.fault "duplicate rule identifier", 0, 0⟩ else
  if rules.any (fun rule => decide (¬rule.vars.Nodup)) then ⟨.fault "duplicate rule variable", 0, 0⟩ else
  match schema [] goal with
  | .error reason => ⟨.fault reason, 0, 0⟩
  | .ok term =>
      let initial : Branch := ⟨[⟨term, seed, 0, limits.depth⟩], PromotionAdmission.Term.var, [], 0, 1⟩
      loop rules limits.unification none limits.steps [.enter initial] 0 0

/-- The candidate producer grants no authority. This boundary checks its exact
article against the independently admitted definition and requested goal. -/
def checkedCandidate (definition : ValidatedCalculusLanguageDef) (goal : Pattern) (report : Report) :
    Option (CheckedProof definition goal) :=
  match report.outcome with
  | .candidate article => if accepted : checkRaw definition goal article = true then some ⟨article, accepted⟩ else none
  | _ => none

theorem checkedCandidate_sound (definition : ValidatedCalculusLanguageDef) (goal : Pattern)
    (report : Report) (returned : (checkedCandidate definition goal report).isSome = true) :
    Nonempty (Derivation definition goal) :=
  checkRaw_soundness ((checkedCandidate definition goal report).get returned).property

end Mettapedia.GSLT.LanguageDef.FirstOrderPremiseSearch
