import Mettapedia.Languages.MeTTa.HE.Spec.Eval
import Mettapedia.Machines.OrderedProtocol

/-!
# Stateful HE chain contexts and ordered resumption

The independent completed source judgments thread the reached world through
operand evaluation and through every continuation occurrence. This adapter
compiles nested source-position chain contexts to saved continuation sites.
Their execution uses the shared ordered traversal, with each answer's own
binding frame. No snapshot of the mutable world is saved in a continuation.

The correspondence is for completed derivations. It neither assumes producer
termination nor supplies a streaming-prefix theorem for this big-step profile.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ContextualTransform.HEStatefulContexts

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Eval.Completed.Stateful
open Mettapedia.Machines.OrderedProtocol.Completion

variable {Context World : Type}

/-- One result occurrence resumes with its own reached frame. -/
def resumeOne (environment : WorldEnvironment Context World) (label : Context)
    (live : List Atom) (scope : List String) (caller : Option Atom)
    (boundary : Boundary) (policy : Policy) (row : Result)
    (before : World) (results : List Result) (after : World) : Prop :=
  BoundaryRel environment label before live scope caller boundary row.1 row.2
    results after (policy := policy)

/-- The source batch and the common stateful traversal have the same
derivations, including empty result blocks and duplicate input occurrences. -/
theorem batch_exact
    {environment : WorldEnvironment Context World} {label : Context}
    {live : List Atom} {scope : List String} {caller : Option Atom}
    {boundary : Boundary} {policy : Policy} {rows results : List Result}
    {before after : World} :
    BoundaryBatchRel environment label before live scope caller boundary rows results after
        (policy := policy) ↔
      OrderedStateFlatMapRel (resumeOne environment label live scope caller boundary policy)
        rows before results after := by
  constructor
  · intro source
    induction rows generalizing before results with
    | nil => cases source; exact .nil _
    | cons head tail ih =>
        cases source with
        | cons first rest => exact .cons first (ih rest)
  · intro target
    induction target with
    | nil => exact .nil
    | cons first _ ih => exact .cons first ih

theorem batch_append_exact
    {environment : WorldEnvironment Context World} {label : Context}
    {live : List Atom} {scope : List String} {caller : Option Atom}
    {boundary : Boundary} {policy : Policy} (left right : List Result)
    {results : List Result} {before after : World} :
    BoundaryBatchRel environment label before live scope caller boundary (left ++ right)
        results after (policy := policy) ↔
      ∃ middle earlier later, results = earlier ++ later ∧
        BoundaryBatchRel environment label before live scope caller boundary left earlier middle
          (policy := policy) ∧
        BoundaryBatchRel environment label middle live scope caller boundary right later after
          (policy := policy) := by
  constructor
  · intro source
    obtain ⟨middle, earlier, later, same, first, rest⟩ :=
      OrderedStateFlatMapRel.split left right (batch_exact.mp source)
    exact ⟨middle, earlier, later, same, batch_exact.mpr first, batch_exact.mpr rest⟩
  · rintro ⟨middle, earlier, later, rfl, first, rest⟩
    exact batch_exact.mpr ((batch_exact.mp first).append (batch_exact.mp rest))

def chain (source : Entry.Value) (name : String) (template : Entry.Value) : Entry.Value :=
  .expression .active [.symbol "chain", source, .var name, template]

/-- The operand finishes first; its reached world is where the first
continuation begins. Returning no answers does not rewind operand effects. -/
theorem chain_exact
    {environment : WorldEnvironment Context World} {label : Context}
    {live : List Atom} {scope : List String} {caller : Option Atom}
    {policy : Policy} {source template : Entry.Value} {name : String}
    {frame : Frame} {results : List Result} {before after : World} :
    MinimalRel environment label before live scope caller (chain source name template)
        frame results after (policy := policy) ↔
      ∃ middle selected,
        MinimalRel environment label before ((chain source name template).erase :: live) scope
          (some (chain source name template).erase) source frame selected middle
          (policy := policy) ∧
        BoundaryBatchRel environment label middle live scope caller (.chain name template)
          selected results after (policy := policy) := by
  constructor
  · intro sourceRun
    generalize shaped : chain source name template = term at sourceRun
    cases sourceRun <;> simp_all [chain, Entry.Value.erase, Minimal.embeddedInstruction]
    · subst term
      simp_all [Entry.Value.erase]
    · exact ⟨_, _, by assumption, by assumption⟩
  · rintro ⟨middle, selected, evaluated, resumed⟩
    apply MinimalRel.chain (world1 := middle) (selected := selected)
    · simpa [chain, Entry.Value.erase] using evaluated
    · exact resumed

theorem chain_empty_exact
    {environment : WorldEnvironment Context World} {label : Context}
    {live : List Atom} {scope : List String} {caller : Option Atom}
    {policy : Policy} {source template : Entry.Value} {name : String}
    {frame : Frame} {before reached : World}
    (evaluated : MinimalRel environment label before
      ((chain source name template).erase :: live) scope
      (some (chain source name template).erase) source frame [] reached (policy := policy)) :
    MinimalRel environment label before live scope caller (chain source name template)
      frame [] reached (policy := policy) :=
  chain_exact.mpr ⟨reached, [], evaluated, .nil⟩

/-- Saved control contains syntax and scope, never a private branch world. -/
structure Saved where
  live : List Atom
  caller : Option Atom
  boundary : Boundary

/-- Executing compiled continuations is an ordered effectful traversal at
each site, followed by the next outer site in the actually reached world. -/
inductive Resume (environment : WorldEnvironment Context World) (label : Context)
    (scope : List String) (policy : Policy) :
    List Saved → World → List Result → List Result → World → Prop where
  | done {world rows} : Resume environment label scope policy [] world rows rows world
  | next {site sites before middle after rows children results} :
      OrderedStateFlatMapRel
        (resumeOne environment label site.live scope site.caller site.boundary policy)
        rows before children middle →
      Resume environment label scope policy sites middle children results after →
      Resume environment label scope policy (site :: sites) before rows results after

theorem resume_append_exact
    {environment : WorldEnvironment Context World} {label : Context}
    {scope : List String} {policy : Policy} (first rest : List Saved)
    {before after : World} {rows results : List Result} :
    Resume environment label scope policy (first ++ rest) before rows results after ↔
      ∃ middle children,
        Resume environment label scope policy first before rows children middle ∧
        Resume environment label scope policy rest middle children results after := by
  induction first generalizing before rows with
  | nil =>
      constructor
      · intro run
        exact ⟨before, rows, .done, run⟩
      · rintro ⟨middle, children, start, rest⟩
        cases start
        exact rest
  | cons site sites ih =>
      constructor
      · intro run
        cases run with
        | next step tail =>
            obtain ⟨middle, children, prefixRun, restRun⟩ := ih.mp tail
            exact ⟨middle, children, .next step prefixRun, restRun⟩
      · rintro ⟨middle, children, prefixRun, restRun⟩
        cases prefixRun with
        | next step tail =>
            exact .next step (ih.mpr ⟨middle, children, tail, restRun⟩)

theorem resume_singleton_exact
    {environment : WorldEnvironment Context World} {label : Context}
    {scope : List String} {policy : Policy} {site : Saved}
    {before after : World} {rows results : List Result} :
    Resume environment label scope policy [site] before rows results after ↔
      BoundaryBatchRel environment label before site.live scope site.caller site.boundary
        rows results after (policy := policy) := by
  constructor
  · intro run
    cases run with
    | next step tail =>
        cases tail
        exact batch_exact.mpr step
  · intro run
    exact .next (batch_exact.mp run) .done

/-- A source-position chain context, outside first. -/
abbrev Contexts := List (String × Entry.Value)

def plug : Contexts → Entry.Value → Entry.Value
  | [], source => source
  | (name, template) :: rest, source => chain (plug rest source) name template

theorem plug_append (outside inside : Contexts) (source : Entry.Value) :
    plug (outside ++ inside) source = plug outside (plug inside source) := by
  induction outside with
  | nil => rfl
  | cons site rest ih => simp only [List.cons_append, plug, ih]

structure Plan where
  live : List Atom
  caller : Option Atom
  stack : List Saved

/-- Enter the nested source once, retaining the outer caller at each return
site and the enclosing source syntax for freshness and caller diagnostics. -/
def compile : Contexts → Entry.Value → List Atom → Option Atom → Plan
  | [], _, live, caller => ⟨live, caller, []⟩
  | (name, template) :: rest, source, live, caller =>
      let term := chain (plug rest source) name template
      let child := compile rest source (term.erase :: live) (some term.erase)
      { child with stack := child.stack ++ [⟨live, caller, .chain name template⟩] }

/-- Preservation and reflection for arbitrary nesting, without erasing
world changes, answer occurrences, selected frames, scope or caller origin. -/
theorem context_exact
    {environment : WorldEnvironment Context World} {label : Context}
    {scope : List String} {policy : Policy} (contexts : Contexts) (source : Entry.Value)
    (live : List Atom) (caller : Option Atom) {frame : Frame}
    {before after : World} {results : List Result} :
    MinimalRel environment label before live scope caller (plug contexts source)
        frame results after (policy := policy) ↔
      ∃ reached selected,
        MinimalRel environment label before (compile contexts source live caller).live scope
          (compile contexts source live caller).caller source frame selected reached
          (policy := policy) ∧
        Resume environment label scope policy (compile contexts source live caller).stack
          reached selected results after := by
  induction contexts generalizing live caller after results with
  | nil =>
      constructor
      · intro run
        exact ⟨after, results, run, .done⟩
      · rintro ⟨reached, selected, run, resumed⟩
        cases resumed
        exact run
  | cons site rest ih =>
      rcases site with ⟨name, template⟩
      simp only [plug, chain_exact, ih, compile]
      constructor
      · rintro ⟨middle, children, ⟨reached, selected, run, inner⟩, outer⟩
        refine ⟨reached, selected, run, ?_⟩
        exact (resume_append_exact _ _).mpr
          ⟨middle, children, inner, resume_singleton_exact.mpr outer⟩
      · rintro ⟨reached, selected, run, resumed⟩
        obtain ⟨middle, children, inner, outer⟩ :=
          (resume_append_exact _ _).mp resumed
        exact ⟨middle, children, ⟨reached, selected, run, inner⟩,
          resume_singleton_exact.mp outer⟩

end Mettapedia.Languages.MeTTa.ContextualTransform.HEStatefulContexts
