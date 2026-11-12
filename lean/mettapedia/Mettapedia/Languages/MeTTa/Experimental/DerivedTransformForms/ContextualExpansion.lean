import Mettapedia.Languages.MeTTa.Experimental.DerivedTransformForms.Lowering

/-!
# Evaluating contexts of the authored candidate forms

The candidate shells compile to the existing PeTTa source contexts, with their
actual continuations and exact administrative charges. Case syntax is constructed
and checked here; readiness is not assumed as a desired evaluator equivalence.
Arbitrary nesting and every remaining source-run outcome are retained.

These laws concern entering an initializer, subject or collected producer. They
do not turn a held value into a computation, define first demand by collection,
or extend the existing source model to dynamic closures or HE streaming.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Experimental.DerivedTransformForms.ContextualExpansion

open OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.MeTTa.PeTTa
open Unifying
open ContextualTransform.PeTTaContexts (atExpression)

open ContextualTransform
open Mettapedia.GSLT.LanguageDef.ModuleFormat

def rows (branches : List (Atom × Code)) : List Atom :=
  branches.map fun branch => .expression [branch.1, branch.2.toPeTTa]

def cases (branches : List (Atom × Code)) : SpaceSemantics.Cases :=
  branches.map fun branch => (branch.1, branch.2.toPeTTa)

theorem read_rows (branches : List (Atom × Code)) : Eval.readCases (rows branches) = some (cases branches) := by
  induction branches with
  | nil => rfl
  | cons branch rest ih =>
      simp only [rows, cases, List.map_cons, Eval.readCases] at *
      rw [ih]
      rfl

inductive Shell where
  | bindValue (pattern : Atom) (body : Code)
  | chainValue (name : String) (body : Code)
  | caseValue (branches : List (Atom × Code))
  | collect
  | count

def Shell.plug : Shell → Code → Code
  | .bindValue pattern body, inner => .bind pattern inner body
  | .chainValue name body, inner => .chain name inner body
  | .caseValue branches, inner => .cases inner branches
  | .collect, inner => .collect inner
  | .count, inner => .count inner

def Shell.sites : Shell → PeTTaApplicationContexts.Context
  | .bindValue pattern body => [.shell (.letValue pattern body.toPeTTa)]
  | .chainValue name body => [.shell (.letValue (.var name) body.toPeTTa)]
  | .caseValue branches => [.shell (.caseValue (rows branches))]
  | .collect => [.shell .collect]
  | .count => [.call "size-atom" [], .shell .collect]

def Shell.frames (bindings : Subst) : Shell → List Frame
  | .bindValue pattern body => [.bind pattern body.toPeTTa]
  | .chainValue name body => [.bind (.var name) body.toPeTTa]
  | .caseValue branches => [.select (cases branches)]
  | .collect => [.collect bindings]
  | .count => [.collect bindings, .argument (.function "size-atom") [] [] 0]

def Shell.cost : Shell → Nat
  | .count => 3
  | _ => 1

theorem shell_expansion (shell : Shell) (inner : Code) :
    (shell.plug inner).toPeTTa = PeTTaApplicationContexts.plug shell.sites inner.toPeTTa := by
  cases shell <;>
    simp only [Shell.plug, Shell.sites, PeTTaApplicationContexts.plug, PeTTaApplicationContexts.Site.plug,
      ContextualTransform.PeTTaContexts.Shell.plug, Code.toPeTTa, rows]

theorem shell_ready (registry : SpaceSemantics.Program) (bindings : Subst)
    (shell : Shell) (inner : Atom) :
    PeTTaApplicationContexts.compile registry bindings shell.sites inner = some (shell.frames bindings) := by
  cases shell with
  | bindValue pattern body => rfl
  | chainValue name body => rfl
  | caseValue branches =>
      simp [Shell.sites, PeTTaApplicationContexts.compile, PeTTaApplicationContexts.Site.frame?,
        ContextualTransform.PeTTaContexts.Shell.frame?, read_rows, Shell.frames]
  | collect => rfl
  | count => rfl

theorem shell_cost (shell : Shell) : PeTTaApplicationContexts.cost shell.sites = shell.cost := by
  cases shell <;> rfl

abbrev Context := List Shell

def plug : Context → Code → Code
  | [], inner => inner
  | shell :: rest, inner => shell.plug (plug rest inner)

def sites (context : Context) : PeTTaApplicationContexts.Context := context.flatMap Shell.sites

def frames (bindings : Subst) : Context → List Frame
  | [] => []
  | shell :: rest => frames bindings rest ++ shell.frames bindings

def cost (context : Context) : Nat := (context.map Shell.cost).sum

theorem plug_append (outside inside : Context) (inner : Code) :
    plug (outside ++ inside) inner = plug outside (plug inside inner) := by
  induction outside with
  | nil => rfl
  | cons shell rest ih => simp [plug, ih]

theorem frames_append (bindings : Subst) (outside inside : Context) :
    frames bindings (outside ++ inside) = frames bindings inside ++ frames bindings outside := by
  induction outside with
  | nil => simp [frames]
  | cons shell rest ih => simp [frames, ih, List.append_assoc]

theorem context_expansion (context : Context) (inner : Code) :
    (plug context inner).toPeTTa = PeTTaApplicationContexts.plug (sites context) inner.toPeTTa := by
  induction context with
  | nil => rfl
  | cons shell rest ih =>
      simp only [plug, shell_expansion, sites, List.flatMap_cons, PeTTaApplicationContexts.plug_append] at *
      rw [ih]

theorem context_ready (registry : SpaceSemantics.Program) (bindings : Subst)
    (context : Context) (inner : Atom) :
    PeTTaApplicationContexts.compile registry bindings (sites context) inner = some (frames bindings context) := by
  induction context with
  | nil => rfl
  | cons shell rest ih =>
      simpa only [sites, List.flatMap_cons, frames] using
        PeTTaApplicationContexts.compile_append registry bindings shell.sites (sites rest) inner
          (shell.frames bindings) (frames bindings rest)
          (shell_ready registry bindings shell (PeTTaApplicationContexts.plug (sites rest) inner)) ih

theorem context_cost (context : Context) : PeTTaApplicationContexts.cost (sites context) = cost context := by
  induction context with
  | nil => rfl
  | cons shell rest ih =>
      simp only [sites, List.flatMap_cons, PeTTaApplicationContexts.cost_append, shell_cost] at *
      simpa [cost] using congrArg (shell.cost + ·) ih

/-- After the proved entry cost, every source outcome is unchanged: completion,
fault and a suspended finite prefix all use the same real caller continuation. -/
theorem run_context (registry : SpaceSemantics.Program) (context : Context)
    (base : Configuration) (bindings : Subst) (inner : Code) (fuel : Nat) :
    run registry (cost context + fuel) (atExpression base bindings (plug context inner).toPeTTa) =
      run registry fuel (atExpression
        { base with frames := frames bindings context ++ base.frames } bindings inner.toPeTTa) := by
  rw [context_expansion, ← context_cost]
  exact PeTTaApplicationContexts.run_context registry (sites context) base bindings inner.toPeTTa
    (frames bindings context) (context_ready registry bindings context inner.toPeTTa) fuel

theorem outcome_iff (registry : SpaceSemantics.Program) (context : Context)
    (base : Configuration) (bindings : Subst) (inner : Code) (fuel : Nat) (result : Outcome) :
    run registry (cost context + fuel) (atExpression base bindings (plug context inner).toPeTTa) = result ↔
      run registry fuel (atExpression
        { base with frames := frames bindings context ++ base.frames } bindings inner.toPeTTa) = result := by
  rw [run_context]

/-- The grammar replay and the source contextual law meet at the decoded form.
This combines their scopes; it does not assert whole-family tcalc adequacy. -/
theorem accepted_context (surface : Presentations.Surface) (source : String)
    (packet : SourcePacket.Packet) (decoded : Code)
    (accepted : Lowering.accepted surface source packet = .ok decoded)
    (registry : SpaceSemantics.Program) (context : Context) (base : Configuration)
    (bindings : Subst) (fuel : Nat) :
    (∃ spec core, Lowering.description surface = .ok spec ∧
      SourceSyntaxIO.read? spec source packet = some core ∧
      SourceSyntaxIO.print? spec core = some source) ∧
    run registry (cost context + fuel) (atExpression base bindings (plug context decoded).toPeTTa) =
      run registry fuel (atExpression
        { base with frames := frames bindings context ++ base.frames } bindings decoded.toPeTTa) :=
  ⟨Lowering.acceptance_has_source surface source packet decoded accepted,
    run_context registry context base bindings decoded fuel⟩

theorem count_has_administrative_cost : cost [.count] = 3 := rfl

theorem zero_budget_retains_context (registry : SpaceSemantics.Program) (context : Context)
    (base : Configuration) (bindings : Subst) (inner : Code) :
    run registry 0 (atExpression base bindings (plug context inner).toPeTTa) =
      .exhausted (atExpression base bindings (plug context inner).toPeTTa) := rfl

theorem held_syntax_returns_data (registry : SpaceSemantics.Program) (base : Configuration)
    (bindings : Subst) (inner : Code) :
    step registry (atExpression base bindings (Code.value inner.toPeTTa).toPeTTa) =
      some { base with control := .returned [⟨resolve bindings inner.toPeTTa, bindings⟩] } :=
  value_remains_data registry base bindings inner.toPeTTa

end Mettapedia.Languages.MeTTa.Experimental.DerivedTransformForms.ContextualExpansion
