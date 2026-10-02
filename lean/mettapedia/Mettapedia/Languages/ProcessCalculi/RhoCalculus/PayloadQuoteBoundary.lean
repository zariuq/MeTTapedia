import Mettapedia.Languages.ProcessCalculi.RhoCalculus.AdmissibleContexts
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction

/-!
# An output payload is a delayed quote

The rho admissible class `AdmissibleContexts.QuoteFreePath` excludes holes under
a name quotation and admits the payload position of an output.  Communication
quotes the payload, after `semanticNormalizeProc`, and substitutes the quoted
name for the receiver's bound name; a receiver that uses that name as a channel
then compares the payload's code by identity.

This module checks this at the rule level for the pair `a!(0)` and `a!(*@0)`:

* the two outputs send structurally congruent names, by the quote-drop law
  (`sent_names_congruent`);
* the payload position of the separating context is quote-free
  (`payloadPosition_quoteFree`);
* one communication step (`Reduces.comm`) moves the quoted payload into the
  channel position of an output (`payloadContext_reduces`);
* the two payloads normalise to distinct processes
  (`normalized_payloads_distinct`), so the quoted channels differ;
* after that step, the channel produced from `a!(0)` matches a listener on
  `@(a!(0))` and the one produced from `a!(*@0)` does not
  (`delayed_quote_separates`).

As in `AdmissibleContexts.quoting_context_separates`, the separation is by a
rule match; no bisimulation over the full rho calculus is constructed here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.PayloadQuote

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.RedexPosition
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.AdmissibleContexts

/-- The channel `@0`. -/
def zeroChannel : Pattern := quote nil

/-- `@0!(0)`. -/
def plainOutput : Pattern := out zeroChannel nil

/-- `@0!(*@0)`. -/
def dropOutput : Pattern := out zeroChannel (drop (quote nil))

/-- The listener: `for (_ <- @(@0!(0))) 0`. -/
def listener : Pattern := inp (quote plainOutput) (.lambda none nil)

/-- The echo: `for (x <- n) x!(0)`, with `n` the free name `n`. -/
def echoOn : Pattern := inp (.fvar "n") (.lambda none (out (.bvar 0) nil))

/-- The payload context: `n!(□) | for (x <- n) x!(0) | for (_ <- @(@0!(0))) 0`. -/
def payloadContext (filling : Pattern) : Pattern :=
  .collection .hashBag [out (.fvar "n") filling, echoOn, listener] none

/-- The configuration after the echo has received the payload. -/
def echoed (filling : Pattern) : Pattern :=
  .collection .hashBag [out (.apply "NQuote" [semanticNormalizeProc filling]) nil, listener] none

/-- The hole is where the payload is. -/
theorem payloadContext_focus (filling : Pattern) :
    subtermAt (payloadContext filling) [0, 1] = some filling := rfl

/-- **The payload position is quote-free.** -/
theorem payloadPosition_quoteFree :
    QuoteFreePath (payloadContext nil) [0, 1] = true := rfl

/-- **The two outputs send congruent names.**  `a!(*@0)` sends `@(*@0)`, which
the quote-drop law identifies with `@0`, the name `a!(0)` sends. -/
theorem sent_names_congruent :
    StructuralCongruence (.apply "NQuote" [semanticNormalizeProc (drop (quote nil))])
      (.apply "NQuote" [semanticNormalizeProc nil]) := by
  have normalized : semanticNormalizeProc (drop (quote nil)) = drop (quote nil) := by
    decide +kernel
  have normalizedNil : semanticNormalizeProc nil = nil := by
    decide +kernel
  rw [normalized, normalizedNil]
  exact StructuralCongruence.quote_drop (quote nil)

/-- **Communication moves the quoted payload into a channel position.** -/
theorem payloadContext_reduces (filling : Pattern) :
    Nonempty (Reduces (payloadContext filling) (echoed filling)) := by
  have substituted : semanticCommSubst (out (.bvar 0) nil) filling =
      out (.apply "NQuote" [semanticNormalizeProc filling]) nil := rfl
  have step := (Reduces.comm (n := .fvar "n") (q := filling) (p := out (.bvar 0) nil)
    (rest := [listener]))
  rw [substituted] at step
  exact ⟨step⟩

/-- **The two payloads normalise to distinct processes.** -/
theorem normalized_payloads_distinct :
    semanticNormalizeProc plainOutput ≠ semanticNormalizeProc dropOutput := by
  decide +kernel

/-- Neither output takes a communication step on its own. -/
theorem outputs_no_comm_match :
    matchPatternForRule rhoCalc rhoCommRewrite plainOutput = [] ∧
      matchPatternForRule rhoCalc rhoCommRewrite dropOutput = [] := by
  constructor <;> decide +kernel

/-- **The delayed quote separates them.**  After the payload is echoed, the
channel quoting `@0!(0)` matches the listener and the channel quoting
`@0!(*@0)` does not. -/
theorem delayed_quote_separates :
    matchPatternForRule rhoCalc rhoCommRewrite (echoed plainOutput) ≠ [] ∧
      matchPatternForRule rhoCalc rhoCommRewrite (echoed dropOutput) = [] := by
  constructor <;> decide +kernel

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.PayloadQuote
