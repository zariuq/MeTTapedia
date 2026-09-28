import Mettapedia.Languages.Agda.Intrinsic.Rules
import Mettapedia.Languages.Agda.Intrinsic.Rendering
import Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution

/-!
# Lowering the authored operational table to contextual rule execution

This compiler reads the intrinsic schemas, rather than maintaining another
list of Agda reductions. Object binders become pattern binders; contextual
metavariable applications become declared occurrence substitutions. A unary
metavariable applied to a nonvariable argument uses explicit substitution.
The present table uses only nullary and unary contextual metavariables.

The declaration checks below validate every output rule. The complete
semantic comparison of this compiler with the intrinsic interpretation is
separate from declaration validity.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Intrinsic.Lowering

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPolynomial
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Authored

def termType : TypeExpr := .base "Term"

def metaName (i : Nat) : String := "m" ++ toString i

structure Occurrence where
  name : String
  path : List Nat
  arguments : List Pattern

structure Surface where
  pattern : Pattern
  occurrences : List Occurrence

def underPath (path : List Nat) (value : Surface) : List Occurrence :=
  value.occurrences.map fun row => { row with path := path ++ row.path }

def wrap (binders : List Srt) (value : Surface) : Surface :=
  { pattern := PatternRendering.wrapBinders binders value.pattern
    occurrences := underPath (List.replicate binders.length 0) value }

def constructor (op : Op .term) (args : List Surface) : Surface :=
  { pattern := .apply (Rendering.label op) (args.map Surface.pattern)
    occurrences := (args.mapIdx fun i value => underPath [i] value).flatten }

def metavariable? (index : Nat) (args : List Surface) : Option Surface :=
  match args with
  | [] => some ⟨.fvar (metaName index), []⟩
  | [⟨.bvar var, []⟩] =>
      some ⟨.fvar (metaName index), [⟨metaName index, [], [.bvar var]⟩]⟩
  | [arg] =>
      some ⟨.subst (.fvar (metaName index)) arg.pattern,
        ⟨metaName index, [0], [.bvar 0]⟩ :: underPath [1] arg⟩
  | _ => none

mutual
def schema? : {Γ : Ctx Authored.schema} → {s : Srt} →
    Term Authored.schema Γ s → Option Surface
  | _, _, .var var => some ⟨.bvar (varIdx var).val, []⟩
  | _, _, .op (.inl op) args => do
      let values ← arguments? args
      match op with
      | op => some (constructor op values)
  | _, _, .op (.inr (.mk index)) args => do
      let values ← arguments? args
      metavariable? index.val values

def arguments? : {arity : List (List Srt × Srt)} → {Γ : Ctx Authored.schema} →
    Args Authored.schema arity Γ → Option (List Surface)
  | _, _, .nil => some []
  | _, _, .cons (bs := binders) head tail => do
      let value ← schema? head
      let values ← arguments? tail
      some (wrap binders value :: values)
end

def atSite (site : RulePatternSite) (value : Surface) : List MetavariableOccurrence :=
  value.occurrences.map fun row => ⟨row.name, site, row.path, row.arguments⟩

def premise? {Γ : Ctx Authored.schema} (index : Nat)
    (premise : BinderLocalPremise.LocalStepPremise Authored.schema Γ) :
    Option (Premise × List MetavariableOccurrence) := do
  let source ← schema? premise.source
  let target ← schema? premise.target
  some (.scopedStep
      ⟨premise.binders.map (fun _ => termType), termType, source.pattern, target.pattern⟩,
    atSite (.premise index 0 0) source ++ atSite (.premise index 0 1) target)

private def rule? (index : Nat) (rule : Rule sig metas) : Option RewriteRule := do
  if !rule.conclusion.ctx.isEmpty then none else do
    let source ← schema? rule.conclusion.lhs
    let target ← schema? rule.conclusion.rhs
    let children ← (rule.premises.mapIdx premise?).mapM id
    let deps := metas.mapIdx fun i arity => (metaName i, arity.1.map (fun _ => termType))
    some
      { name := "agda-step-" ++ toString index
        typeContext := deps.map fun row => (row.1, termType)
        premises := children.map Prod.fst
        left := source.pattern
        right := target.pattern
        bindings := some
          { dependencies := deps
            occurrences := atSite .left source ++ atSite .right target ++
              (children.map Prod.snd).flatten } }

/-- Compilation has an explicit failure result; no rule is silently dropped. -/
def compile : Option (List RewriteRule) := (rules.mapIdx rule?).mapM id

/-- All intrinsic declarations in this table have a root conclusion. The
compiler is not an implementation of arbitrary positioned rewriting. -/
theorem authored_positions_are_roots (i : Fin rules.length) :
    (rules.get i).conclusion.position = rootPosition (rules.get i).conclusion.lhs := by
  fin_cases i <;> rfl

def compiled : List RewriteRule := compile.getD []

theorem compilation_succeeds : compile = some compiled := by rfl

theorem compilation_preserves_count : compiled.length = rules.length := by decide +kernel

theorem all_binding_declarations_admitted :
    compiled.all (fun rule =>
      match rule.bindings with
      | some spec => admittedFor rule spec
      | none => false) = true := by decide +kernel

end Mettapedia.Languages.Agda.Intrinsic.Lowering
