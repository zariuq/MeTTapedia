import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaBindingContexts

/-!
# Application arguments in PeTTa's source evaluation contexts

Strict first-argument positions compose with the existing let/case/condition/
collection/query shells. Admission reads the actual written-call and raw-argument
policies; it never classifies a held Atom argument as an evaluation position.
The compiler records the real continuation frames and administrative step count.

Argument-return laws also cover every later position, each branch's own bindings,
earlier effects and arbitrary caller frames. These use Unifying's existing source
judgments. Dynamic heads and closures require their separate source extension;
they are not treated as ordinary static calls by this adapter.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaApplicationContexts

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.MeTTa.PeTTa
open Unifying PeTTaContexts PeTTaActivation

inductive Site where
  | shell (value : Shell)
  | call (head : String) (rest : List Atom)

def Site.plug : Site → Atom → Atom
  | .shell core, inner => core.plug inner
  | .call head rest, inner => .expression (.symbol head :: inner :: rest)

def Site.cost : Site → Nat
  | .shell _ => 1
  | .call _ _ => 2

def Site.frame? (registry : SpaceSemantics.Program) (bindings : Subst) (site : Site)
    (inner : Atom) : Option Frame :=
  match site with
  | .shell core => core.frame? bindings
  | .call head rest =>
      if sourceControlForm (site.plug inner) || !callable registry head || Eval.argumentIsRaw registry head 0
      then none else some (.argument (.function head) rest [] 0)

theorem site_run (registry : SpaceSemantics.Program) (site : Site) (base : Configuration)
    (bindings : Subst) (inner : Atom) (frame : Frame)
    (ready : site.frame? registry bindings inner = some frame) (fuel : Nat) :
    run registry (site.cost + fuel) (atExpression base bindings (site.plug inner)) =
      run registry fuel (atExpression { base with frames := frame :: base.frames } bindings inner) := by
  cases site with
  | shell shell =>
      simpa [Site.cost, Site.plug, Nat.add_comm] using run_succ_of_step registry fuel _ _
        (transition_step (shell_enters registry shell base bindings inner frame ready))
  | call head rest =>
      simp only [Site.frame?] at ready
      split at ready
      · cases ready
      · rename_i admitted
        simp only [Bool.or_eq_true, Bool.not_eq_true, not_or] at admitted
        have ordinary : sourceControlForm (.expression (.symbol head :: inner :: rest)) = false := by
          simpa [Site.plug] using admitted.1.1
        have known : callable registry head = true := by simpa using admitted.1.2
        have strict : Eval.argumentIsRaw registry head 0 = false := admitted.2
        cases Option.some.inj ready
        have entered := written_call_step registry base bindings head (inner :: rest) ordinary known
        have argument : step registry
            { base with control := .arguments bindings (.function head) (inner :: rest) [] 0 } =
            some (atExpression { base with frames := .argument (.function head) rest [] 0 :: base.frames }
              bindings inner) := transition_step (.evaluated_argument rfl strict)
        change run registry (2 + fuel) _ = _
        simp only [Site.plug]
        rw [show 2 + fuel = (fuel + 1) + 1 by omega,
          run_succ_of_step registry (fuel + 1) _ _ entered,
          run_succ_of_step registry fuel _ _ argument]

abbrev Context := List Site

def plug : Context → Atom → Atom
  | [], inner => inner
  | site :: rest, inner => site.plug (plug rest inner)

def cost (context : Context) : Nat := (context.map Site.cost).sum

def compile (registry : SpaceSemantics.Program) (bindings : Subst) : Context → Atom → Option (List Frame)
  | [], _ => some []
  | site :: rest, inner => do
      let frame ← site.frame? registry bindings (plug rest inner)
      let nested ← compile registry bindings rest inner
      some (nested ++ [frame])

theorem plug_append (outside inside : Context) (inner : Atom) :
    plug (outside ++ inside) inner = plug outside (plug inside inner) := by
  induction outside with
  | nil => rfl
  | cons site rest ih => simp [plug, ih]

theorem cost_append (outside inside : Context) : cost (outside ++ inside) = cost outside + cost inside := by
  simp [cost]

theorem compile_append (registry : SpaceSemantics.Program) (bindings : Subst)
    (outside inside : Context) (inner : Atom) (outerFrames innerFrames : List Frame)
    (outerReady : compile registry bindings outside (plug inside inner) = some outerFrames)
    (innerReady : compile registry bindings inside inner = some innerFrames) :
    compile registry bindings (outside ++ inside) inner = some (innerFrames ++ outerFrames) := by
  induction outside generalizing outerFrames with
  | nil => simp [compile] at outerReady; subst outerFrames; simpa using innerReady
  | cons site rest ih =>
      cases frame : site.frame? registry bindings (plug rest (plug inside inner)) with
      | none => simp [compile, frame] at outerReady
      | some saved =>
          cases nested : compile registry bindings rest (plug inside inner) with
          | none => simp [compile, frame, nested] at outerReady
          | some fs =>
              simp [compile, frame, nested] at outerReady
              subst outerFrames
              simp [compile, plug_append, frame, ih fs nested, List.append_assoc]

/-- Exact source-run equality for arbitrary mixtures and nesting, including
finite cutoffs after entry. The shell overhead is explicit, not erased fuel. -/
theorem run_context (registry : SpaceSemantics.Program) (context : Context)
    (base : Configuration) (bindings : Subst) (inner : Atom) (frames : List Frame)
    (ready : compile registry bindings context inner = some frames) (fuel : Nat) :
    run registry (cost context + fuel) (atExpression base bindings (plug context inner)) =
      run registry fuel (atExpression { base with frames := frames ++ base.frames } bindings inner) := by
  induction context generalizing base frames with
  | nil => simp [compile] at ready; subst frames; simp [cost, plug]
  | cons site rest ih =>
      cases frame : site.frame? registry bindings (plug rest inner) with
      | none => simp [compile, frame] at ready
      | some saved =>
          cases nested : compile registry bindings rest inner with
          | none => simp [compile, frame, nested] at ready
          | some fs =>
              simp [compile, frame, nested] at ready
              subst frames
              change run registry ((site.cost + cost rest) + fuel) _ = _
              rw [Nat.add_assoc, plug, site_run registry site base bindings (plug rest inner) saved frame]
              simpa [List.append_assoc] using ih { base with frames := saved :: base.frames } fs nested

def atArgument (base : Configuration) (bindings : Subst) (target : Eval.Target)
    (inner : Atom) (pending values : List Atom) (index : Nat) : Configuration :=
  { base with control := .arguments bindings target (inner :: pending) values index }

def rawAt (registry : SpaceSemantics.Program) : Eval.Target → Nat → Bool
  | .function head, index => Eval.argumentIsRaw registry head index
  | .data, _ => false

/-- Every operand's packet keeps its own substitution when its remaining
arguments are scheduled. No shared binding substitution is substituted here. -/
theorem operand_then_arguments (registry : SpaceSemantics.Program) (before after : Configuration)
    (bindings : Subst) (target : Eval.Target) (inner : Atom) (pending values : List Atom) (index : Nat)
    (answers : List Answer) (strict : rawAt registry target index = false)
    (evaluated : Relation.ReflTransGen (Transition registry)
      (atExpression { before with frames := [] } bindings inner)
      { after with control := .returned answers, frames := [] }) :
    Relation.ReflTransGen (Transition registry)
      (atArgument before bindings target inner pending values index)
      { after with
        control := .sequence (answers.map fun answer =>
          .arguments answer.bindings target pending (values ++ [answer.value]) (index + 1)) []
        frames := before.frames } := by
  have entry : Transition registry (atArgument before bindings target inner pending values index)
      (atExpression { before with frames := .argument target pending values index :: before.frames }
        bindings inner) := .evaluated_argument rfl (by cases target <;> exact strict)
  have middle := steps_append_frames evaluated (.argument target pending values index :: before.frames)
  have reached : Relation.ReflTransGen (Transition registry)
      (atExpression { before with frames := .argument target pending values index :: before.frames } bindings inner)
      { after with control := .returned answers, frames := .argument target pending values index :: before.frames } := by
    simpa [atExpression, appendFrames] using middle
  exact (Relation.ReflTransGen.head entry reached).tail (.argument_return rfl rfl)

theorem argument_return_exact (registry : SpaceSemantics.Program) (base : Configuration)
    (answers : List Answer) (target : Eval.Target) (pending values : List Atom) (index : Nat)
    (next : Configuration) :
    Transition registry
      { base with
        control := .returned answers
        frames := .argument target pending values index :: base.frames } next ↔
      next = { base with control := .sequence (answers.map fun answer =>
        .arguments answer.bindings target pending (values ++ [answer.value]) (index + 1)) [] } := by
  rw [← step_iff_transition]
  simp only [step, Option.some.injEq, eq_comm]

/-- A held argument advances by three administrative steps and never asks
the evaluator to execute its contents. -/
theorem raw_argument_run (registry : SpaceSemantics.Program) (base : Configuration)
    (bindings : Subst) (target : Eval.Target) (inner : Atom) (pending values : List Atom) (index fuel : Nat)
    (raw : rawAt registry target index = true) :
    run registry (3 + fuel) (atArgument base bindings target inner pending values index) =
      run registry fuel
        { base with
          control := .arguments bindings target pending (values ++ [resolve bindings inner]) (index + 1)
          frames := .sequence [] [] :: base.frames } := by
  have enter := transition_step (Transition.raw_argument
    (registry := registry)
    (source := atArgument base bindings target inner pending values index) rfl
    (by cases target <;> exact raw))
  have returned := transition_step (Transition.argument_return
    (registry := registry)
    (source := { base with
      control := .returned [⟨resolve bindings inner, bindings⟩]
      frames := .argument target pending values index :: base.frames }) rfl rfl)
  have next := transition_step (Transition.sequence_enter
    (registry := registry)
    (source := { base with
      control := .sequence
        [.arguments bindings target pending (values ++ [resolve bindings inner]) (index + 1)] [] }) rfl)
  dsimp only [atArgument] at enter
  dsimp only at returned next
  simp only [List.map_cons, List.map_nil] at returned
  simp only [atArgument]
  rw [show 3 + fuel = ((fuel + 1) + 1) + 1 by omega,
    run_succ_of_step registry ((fuel + 1) + 1) _ _ enter,
    run_succ_of_step registry (fuel + 1) _ _ returned,
    run_succ_of_step registry fuel _ _ next]

/-- An empty operand's effects remain, while later argument work is skipped. -/
theorem answerless_operand (registry : SpaceSemantics.Program) (before after : Configuration)
    (bindings : Subst) (target : Eval.Target) (inner : Atom) (pending values : List Atom) (index : Nat)
    (strict : rawAt registry target index = false)
    (evaluated : Relation.ReflTransGen (Transition registry)
      (atExpression { before with frames := [] } bindings inner)
      { after with control := .returned [], frames := [] }) :
    Relation.ReflTransGen (Transition registry)
      (atArgument before bindings target inner pending values index)
      { after with control := .returned [], frames := before.frames } := by
  exact (operand_then_arguments registry before after bindings target inner pending values index []
    strict evaluated).tail (.sequence_done rfl)

end Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaApplicationContexts
