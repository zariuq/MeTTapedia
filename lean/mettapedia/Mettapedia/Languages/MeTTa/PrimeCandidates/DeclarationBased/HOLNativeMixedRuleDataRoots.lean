import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeMixedRuleData
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.DeclarationAwarePatternMatching

/-!
# Executing the authored mixed computation roots

These equations evaluate the actual generic matcher and premise interpreter
for each retained root. Recursive weakening and substitution remain calls
to the same rule-data execution service.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeMixedRuleData

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open DeclarationAwarePatternCodec DeclarationAwareSubstitutionLanguage

def executeRule (recursive : Pattern → List Pattern) (rule : RewriteRule)
    (source : Pattern) : List Pattern :=
  applyRuleUsing (engineBasePremises RelationEnv.empty) language recursive rule (compute source)

macro "unfold_mixed_rule" : tactic =>
  `(tactic| simp (config := { maxSteps := 1000000 })
    [executeRule, computationRule, compute, constant, apps, nil, cons,
     listEliminate, identityEliminate, nilRel, consRel, relEliminate,
     proof, implication, universal, tmApp, tmPi, tmSigma, tmLam, tmId,
     tmPair, tmFst, tmSnd, tmRefl, tmVar, tmConst, tmHead, m, zero,
     applyRuleUsing, matchPatternForRule_eq_syntactic,
     matchPattern, matchArgs, mergeBindings, premisesUsing, premiseStepUsing,
     applyBindingsForRule, Mettapedia.OSLF.MeTTaIL.Match.applyBindings, Bindings.lookup,
     Mettapedia.OSLF.MeTTaIL.Match.applyRuleBindings,
     List.map_flatMap, ← List.map_eq_flatMap,
     DeclarationAwareSubstitutionExecution.weaken,
     DeclarationAwareSubstitutionExecution.substitute])

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

theorem execute_betaRule (recursive : Pattern → List Pattern) (body argument : Pattern) :
    executeRule recursive betaRule (tmApp (tmLam body) argument) =
      recursive (Binding.substitute zero argument body) := by
  unfold betaRule
  unfold_mixed_rule

theorem execute_firstRule (recursive : Pattern → List Pattern) (a b : Pattern) :
    executeRule recursive firstRule (tmFst (tmPair a b)) = [a] := by
  unfold firstRule
  unfold_mixed_rule

theorem execute_secondRule (recursive : Pattern → List Pattern) (a b : Pattern) :
    executeRule recursive secondRule (tmSnd (tmPair a b)) = [b] := by
  unfold secondRule
  unfold_mixed_rule

theorem execute_listNilRule (recursive : Pattern → List Pattern) (a p z s : Pattern) :
    executeRule recursive listNilRule (listEliminate a p z s (nil a)) = [z] := by
  unfold listNilRule
  unfold_mixed_rule

theorem execute_listConsRule (recursive : Pattern → List Pattern) (a p z s h t : Pattern) :
    executeRule recursive listConsRule (listEliminate a p z s (cons a h t)) =
      [apps s [h, t, listEliminate a p z s t]] := by
  unfold listConsRule
  unfold_mixed_rule

theorem execute_identityRule (recursive : Pattern → List Pattern) (a x p d : Pattern) :
    executeRule recursive identityRule (identityEliminate a x p d x (tmRefl x)) = [d] := by
  unfold identityRule
  unfold_mixed_rule

theorem execute_relNilRule (recursive : Pattern → List Pattern) (a b r p z s : Pattern) :
    executeRule recursive relNilRule
      (relEliminate a b r p z s (nil a) (nil b) (nilRel a b r)) = [z] := by
  unfold relNilRule
  unfold_mixed_rule

theorem execute_relConsRule (recursive : Pattern → List Pattern)
    (a b r p z s h k t u he te : Pattern) :
    executeRule recursive relConsRule
      (relEliminate a b r p z s (cons a h t) (cons b k u) (consRel a b r h k t u he te)) =
      [apps s [h, k, t, u, he, te, relEliminate a b r p z s t u te]] := by
  unfold relConsRule
  unfold_mixed_rule

theorem execute_implicationRule (recursive : Pattern → List Pattern) (p q : Pattern) :
    executeRule recursive implicationRule (proof (implication p q)) =
      (recursive (Binding.weaken zero (proof q))).map (tmPi (proof p)) := by
  unfold implicationRule
  unfold_mixed_rule

theorem execute_universalRule (recursive : Pattern → List Pattern) (a f : Pattern) :
    executeRule recursive universalRule (proof (universal a f)) =
      (recursive (Binding.weaken zero f)).map
        (fun lifted => tmPi a (proof (tmApp lifted (tmVar zero)))) := by
  unfold universalRule
  unfold_mixed_rule

theorem executeRule_inclusion (fuel : Nat) {rule : RewriteRule}
    (member : rule ∈ computationRules) (source : Pattern) :
    executeRule (execute fuel) rule source ⊆ execute (fuel + 1) (compute source) := by
  intro target result
  simp only [execute, rewriteAt, language, List.mem_flatMap]
  exact ⟨rule, List.mem_append_right _ member, result⟩

theorem execute_context_unary (recursive : Pattern → List Pattern)
    (name constructor : String) (a : Pattern) :
    executeRule recursive
      (contextRule name (.apply constructor [m "a"]) (m "a")
        (.apply constructor [m "next"])) (.apply constructor [a]) =
      (recursive (compute a)).map (fun next => .apply constructor [next]) := by
  unfold contextRule
  unfold_mixed_rule

theorem execute_context_binary_first (recursive : Pattern → List Pattern)
    (name constructor : String) (a b : Pattern) :
    executeRule recursive
      (contextRule name (.apply constructor [m "a", m "b"]) (m "a")
        (.apply constructor [m "next", m "b"])) (.apply constructor [a, b]) =
      (recursive (compute a)).map (fun next => .apply constructor [next, b]) := by
  unfold contextRule
  unfold_mixed_rule

theorem execute_context_binary_second (recursive : Pattern → List Pattern)
    (name constructor : String) (a b : Pattern) :
    executeRule recursive
      (contextRule name (.apply constructor [m "a", m "b"]) (m "b")
        (.apply constructor [m "a", m "next"])) (.apply constructor [a, b]) =
      (recursive (compute b)).map (fun next => .apply constructor [a, next]) := by
  unfold contextRule
  unfold_mixed_rule

theorem execute_context_ternary_first (recursive : Pattern → List Pattern)
    (name constructor : String) (a b c : Pattern) :
    executeRule recursive
      (contextRule name (.apply constructor [m "a", m "b", m "c"]) (m "a")
        (.apply constructor [m "next", m "b", m "c"])) (.apply constructor [a, b, c]) =
      (recursive (compute a)).map (fun next => .apply constructor [next, b, c]) := by
  unfold contextRule
  unfold_mixed_rule

theorem execute_context_ternary_second (recursive : Pattern → List Pattern)
    (name constructor : String) (a b c : Pattern) :
    executeRule recursive
      (contextRule name (.apply constructor [m "a", m "b", m "c"]) (m "b")
        (.apply constructor [m "a", m "next", m "c"])) (.apply constructor [a, b, c]) =
      (recursive (compute b)).map (fun next => .apply constructor [a, next, c]) := by
  unfold contextRule
  unfold_mixed_rule

theorem execute_context_ternary_third (recursive : Pattern → List Pattern)
    (name constructor : String) (a b c : Pattern) :
    executeRule recursive
      (contextRule name (.apply constructor [m "a", m "b", m "c"]) (m "c")
        (.apply constructor [m "a", m "b", m "next"])) (.apply constructor [a, b, c]) =
      (recursive (compute c)).map (fun next => .apply constructor [a, b, next]) := by
  unfold contextRule
  unfold_mixed_rule

theorem beta_service_unchanged (fuel : Nat) (index replacement body : Pattern) :
    execute fuel (Binding.substitute index replacement body) =
      Binding.execute fuel (Binding.substitute index replacement body) := by
  apply binding_service_unchanged
  simp [HasOperationHead, bindingHeads, DeclarationAwareSubstitutionExecution.substitute]

theorem weaken_service_unchanged (fuel : Nat) (index body : Pattern) :
    execute fuel (Binding.weaken index body) =
      Binding.execute fuel (Binding.weaken index body) := by
  apply binding_service_unchanged
  simp [HasOperationHead, bindingHeads, DeclarationAwareSubstitutionExecution.weaken]

#print axioms execute_relConsRule
#print axioms execute_implicationRule
#print axioms execute_universalRule
#print axioms executeRule_inclusion

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeMixedRuleData
