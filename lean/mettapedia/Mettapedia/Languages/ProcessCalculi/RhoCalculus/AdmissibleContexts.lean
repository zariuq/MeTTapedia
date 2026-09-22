import Mettapedia.OSLF.Framework.RedexPosition
import Mettapedia.OSLF.MeTTaIL.ContextualStep

/-!
# The admissible context class for rho, and why it excludes holes under a quote

Congruence for a context-labelled bisimilarity holds relative to a class of
contexts, and for rho that class must leave out contexts whose hole sits under
a name quotation.  The reason is reflection: communication turns on *name
equality*, not on behaviour, so two processes that behave alike still quote to
different names and a context that quotes its hole can tell them apart.

This module makes the class syntactic — a context is a position, and an
admissible one never descends into the argument of a quotation — and then
supplies the witness that the exclusion is necessary rather than cautious.

The witness is a pair of processes that are *both inert*, neither matching any
rule of the calculus, together with one quoting context in which one of them
produces a communication redex and the other does not.  No appeal to a
bisimulation is needed to see the failure: the two fillings are separated by a
rule match, which no behavioural equivalence on inert processes can predict.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.AdmissibleContexts

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.RedexPosition

/-! ## The class -/

/-- A path is quote-free when it never descends into the argument of a name
quotation.  Contexts of the admissible class are exactly the quote-free
positions; the parallel, output-payload, input-continuation and drop positions
all satisfy it, and the name position of an output does not. -/
def QuoteFreePath : Pattern → Position → Bool
  | _, [] => true
  | .apply constructor args, i :: rest =>
      if constructor = "NQuote" then false
      else
        match args[i]? with
        | some child => QuoteFreePath child rest
        | none => false
  | .lambda _ body, i :: rest =>
      match i with
      | 0 => QuoteFreePath body rest
      | _ + 1 => false
  | .multiLambda _ _ body, i :: rest =>
      match i with
      | 0 => QuoteFreePath body rest
      | _ + 1 => false
  | .collection _ elements _, i :: rest =>
      match elements[i]? with
      | some child => QuoteFreePath child rest
      | none => false
  | .subst body replacement, i :: rest =>
      match i with
      | 0 => QuoteFreePath body rest
      | 1 => QuoteFreePath replacement rest
      | _ + 2 => false
  | _, _ :: _ => false

/-- The empty context is admissible. -/
theorem quoteFreePath_nil (host : Pattern) : QuoteFreePath host [] = true := by
  cases host <;> rfl

/-- The class is closed under composition: appending a quote-free path below a
quote-free path stays quote-free. -/
theorem quoteFreePath_append :
    ∀ (host : Pattern) (outer inner : Position) (focus : Pattern),
      subtermAt host outer = some focus →
      QuoteFreePath host outer = true → QuoteFreePath focus inner = true →
      QuoteFreePath host (outer ++ inner) = true
  | host, [], inner, focus, hfocus, _, hinner => by
      have : focus = host := by simpa [subtermAt] using hfocus.symm
      subst this
      simpa using hinner
  | .apply constructor args, i :: rest, inner, focus, hfocus, houter, hinner => by
      by_cases hq : constructor = "NQuote"
      · simp [QuoteFreePath, hq] at houter
      · rcases hget : args[i]? with _ | child
        · simp [QuoteFreePath, hq, hget] at houter
        · have hrest : subtermAt child rest = some focus := by
            simpa [subtermAt, childAt, children, hget] using hfocus
          have houter' : QuoteFreePath child rest = true := by
            simpa [QuoteFreePath, hq, hget] using houter
          simp [QuoteFreePath, hq, hget,
            quoteFreePath_append child rest inner focus hrest houter' hinner]
  | .lambda nm body, i :: rest, inner, focus, hfocus, houter, hinner => by
      match i with
      | 0 =>
          have hrest : subtermAt body rest = some focus := by
            simpa [subtermAt, childAt, children] using hfocus
          have houter' : QuoteFreePath body rest = true := by
            simpa [QuoteFreePath] using houter
          simpa [QuoteFreePath] using
            quoteFreePath_append body rest inner focus hrest houter' hinner
      | _ + 1 => simp [QuoteFreePath] at houter
  | .multiLambda n nms body, i :: rest, inner, focus, hfocus, houter, hinner => by
      match i with
      | 0 =>
          have hrest : subtermAt body rest = some focus := by
            simpa [subtermAt, childAt, children] using hfocus
          have houter' : QuoteFreePath body rest = true := by
            simpa [QuoteFreePath] using houter
          simpa [QuoteFreePath] using
            quoteFreePath_append body rest inner focus hrest houter' hinner
      | _ + 1 => simp [QuoteFreePath] at houter
  | .collection ct elements restVar, i :: rest, inner, focus, hfocus, houter, hinner => by
      rcases hget : elements[i]? with _ | child
      · simp [QuoteFreePath, hget] at houter
      · have hrest : subtermAt child rest = some focus := by
          simpa [subtermAt, childAt, children, hget] using hfocus
        have houter' : QuoteFreePath child rest = true := by
          simpa [QuoteFreePath, hget] using houter
        simp [QuoteFreePath, hget,
          quoteFreePath_append child rest inner focus hrest houter' hinner]
  | .subst body replacement, i :: rest, inner, focus, hfocus, houter, hinner => by
      match i with
      | 0 =>
          have hrest : subtermAt body rest = some focus := by
            simpa [subtermAt, childAt, children] using hfocus
          have houter' : QuoteFreePath body rest = true := by
            simpa [QuoteFreePath] using houter
          simpa [QuoteFreePath] using
            quoteFreePath_append body rest inner focus hrest houter' hinner
      | 1 =>
          have hrest : subtermAt replacement rest = some focus := by
            simpa [subtermAt, childAt, children] using hfocus
          have houter' : QuoteFreePath replacement rest = true := by
            simpa [QuoteFreePath] using houter
          simpa [QuoteFreePath] using
            quoteFreePath_append replacement rest inner focus hrest houter' hinner
      | _ + 2 => simp [QuoteFreePath] at houter
  | .bvar _, _ :: _, _, _, _, houter, _ => by simp [QuoteFreePath] at houter
  | .fvar _, _ :: _, _, _, _, houter, _ => by simp [QuoteFreePath] at houter

/-! ## Parallel contexts are admissible, always

The platform's contexts are parallel remainders: a bag of processes placed
beside the hole.  That the class of item two contains them is not an assumption
about the platform but a fact about bags, and it is proved here rather than
asserted, so that the platform's congruence for *every* context is visibly a
congruence for *admissible* contexts. -/

/-- A path that only ever descends through collections: the hole sits beside
siblings, at any nesting depth. -/
def ParallelPath : Pattern → Position → Bool
  | _, [] => true
  | .collection _ elements _, i :: rest =>
      match elements[i]? with
      | some child => ParallelPath child rest
      | none => false
  | _, _ :: _ => false

/-- **One step beside siblings is admissible.**  A bag carries no quotation for
the path to descend into, so every in-range parallel position is quote-free. -/
theorem quoteFreePath_of_parallelStep (kind : CollType) (elements : List Pattern)
    (tail : Option String) {index : Nat} {child : Pattern}
    (found : elements[index]? = some child) :
    QuoteFreePath (.collection kind elements tail) [index] = true := by
  simp [QuoteFreePath, found]

/-- **And so is any depth of them.**  Nesting bags never introduces a quote, so
the whole parallel context category sits inside the admissible class. -/
theorem quoteFreePath_of_parallelPath :
    ∀ (host : Pattern) (path : Position),
      ParallelPath host path = true → QuoteFreePath host path = true
  | host, [], _ => quoteFreePath_nil host
  | .collection _ elements _, index :: rest, parallel => by
      rcases found : elements[index]? with _ | child
      · simp [ParallelPath, found] at parallel
      · have below : ParallelPath child rest = true := by
          simpa [ParallelPath, found] using parallel
        simp [QuoteFreePath, found, quoteFreePath_of_parallelPath child rest below]
  | .bvar _, _ :: _, parallel => by simp [ParallelPath] at parallel
  | .fvar _, _ :: _, parallel => by simp [ParallelPath] at parallel
  | .apply _ _, _ :: _, parallel => by simp [ParallelPath] at parallel
  | .lambda _ _, _ :: _, parallel => by simp [ParallelPath] at parallel
  | .multiLambda _ _ _, _ :: _, parallel => by simp [ParallelPath] at parallel
  | .subst _ _, _ :: _, parallel => by simp [ParallelPath] at parallel

/-- **Negative control: the containment is strict.**  Not every admissible
context is parallel -- the payload of an output is quote-free but is not a
position beside siblings -- so the previous theorem is a genuine inclusion and
not a restatement. -/
theorem parallelPath_not_all_quoteFree :
    QuoteFreePath (.apply "POutput" [.apply "A" [], .apply "PZero" []]) [1] = true ∧
      ParallelPath (.apply "POutput" [.apply "A" [], .apply "PZero" []]) [1] = false := by
  constructor <;> rfl

/-! ## The positions of the communication redex -/

/-- Nil. -/
def nil : Pattern := .apply "PZero" []

/-- The quotation of a pattern. -/
def quote (inner : Pattern) : Pattern := .apply "NQuote" [inner]

/-- The drop of a name. -/
def drop (name : Pattern) : Pattern := .apply "PDrop" [name]

/-- An output on a channel. -/
def out (channel payload : Pattern) : Pattern := .apply "POutput" [channel, payload]

/-- An input on a channel with a continuation. -/
def inp (channel continuation : Pattern) : Pattern :=
  .apply "PInput" [channel, continuation]

/-- The continuation position of the communication redex is admissible: it
never passes under a quotation. -/
theorem commContinuation_quoteFree :
    QuoteFreePath rhoCommRewrite.left [0, 1] = true := by rfl

/-- The payload position of the output is admissible too. -/
theorem commPayload_quoteFree :
    QuoteFreePath rhoCommRewrite.left [1, 1] = true := by rfl

/-- The channel position of the output is not: it is the argument of a
quotation only when the channel is written as one, and in the authored rule
the channel is a metavariable, so the position exists and is quote-free.  The
exclusion bites on a *term* whose channel is an explicit quotation, which is
the situation `quotedChannel_not_quoteFree` exhibits. -/
theorem commChannel_quoteFree :
    QuoteFreePath rhoCommRewrite.left [1, 0] = true := by rfl

/-! ## The witness that the exclusion is necessary -/

/-- A quoting context: an output whose channel is the quotation of the hole,
in parallel with an input listening on the quotation of `drop (quote nil)`. -/
def quotingContext (filling : Pattern) : Pattern :=
  .collection .hashBag
    [inp (quote (drop (quote nil))) (.lambda none nil),
     out (quote filling) nil] none

/-- The hole of the quoting context sits under a quotation, so the context is
not admissible. -/
theorem quotedChannel_not_quoteFree :
    QuoteFreePath (quotingContext nil) [1, 0, 0] = false := by rfl

/-- The hole is where we say it is. -/
theorem quotingContext_focus (filling : Pattern) :
    subtermAt (quotingContext filling) [1, 0, 0] = some filling := by rfl

/-- The first filling: the drop of a quoted nil. -/
def fillingLeft : Pattern := drop (quote nil)

/-- The second filling: nil. -/
def fillingRight : Pattern := nil

/-- Neither filling matches the communication rule on its own. -/
theorem fillings_no_comm_match :
    matchPatternForRule rhoCalc rhoCommRewrite fillingLeft = [] ∧
      matchPatternForRule rhoCalc rhoCommRewrite fillingRight = [] := by
  constructor <;> decide +kernel

/-- Nor the contextual rule: neither filling is a parallel composition. -/
theorem fillings_no_parCong_match :
    matchPatternForRule rhoCalc rhoParCongRewrite fillingLeft = [] ∧
      matchPatternForRule rhoCalc rhoParCongRewrite fillingRight = [] := by
  constructor <;> decide +kernel

/-- Both fillings are inert: no rule of the calculus matches either, so
neither takes a step.  Whatever behavioural equivalence one adopts, it cannot
separate them on their own behaviour, because they have none. -/
theorem fillingLeft_inert (base : BasePremiseEvaluator) (target : Pattern) :
    ¬ Step base rhoCalc fillingLeft target := by
  refine not_step_of_matchPatternForRule_eq_nil ?_
  intro rule hrule
  have : rule = rhoCommRewrite ∨ rule = rhoParCongRewrite := by
    simpa [rhoCalc] using hrule
  rcases this with h | h <;> subst h
  · exact fillings_no_comm_match.1
  · exact fillings_no_parCong_match.1

theorem fillingRight_inert (base : BasePremiseEvaluator) (target : Pattern) :
    ¬ Step base rhoCalc fillingRight target := by
  refine not_step_of_matchPatternForRule_eq_nil ?_
  intro rule hrule
  have : rule = rhoCommRewrite ∨ rule = rhoParCongRewrite := by
    simpa [rhoCalc] using hrule
  rcases this with h | h <;> subst h
  · exact fillings_no_comm_match.2
  · exact fillings_no_parCong_match.2

/-- **The separation.**  Placed in the quoting context, the first filling
produces a communication redex — the output's channel is then the very name
the input listens on — while the second does not.  Two processes with no
behaviour of their own are therefore distinguished by a context that quotes
its hole, which is why the admissible class must exclude such contexts, and
why excluding them is not mere caution. -/
theorem quoting_context_separates :
    matchPatternForRule rhoCalc rhoCommRewrite (quotingContext fillingLeft) ≠ [] ∧
      matchPatternForRule rhoCalc rhoCommRewrite (quotingContext fillingRight) = [] := by
  constructor
  · decide +kernel
  · decide +kernel

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.AdmissibleContexts
