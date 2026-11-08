import Mettapedia.Languages.Lean.ParserDescriptorLowering

/-!
# Progress of token-led declarative parser bodies

A token-led body must consume a nonempty literal before its category calls.
This is a conservative, executable admission condition, not a claim that
input length bounds the recursion of arbitrary parser callbacks.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Lean.ParserDescriptorProgress

open ParserDescription ParserDescriptorLowering
open Mettapedia.GSLT.Parsing.LanguageDefSyntaxCompiler
open Mettapedia.GSLT.Parsing.PresentationExprSemantics

def tokenLed : Description → Bool
  | .symbol text => !(scalars text).isEmpty
  | .binary name first _ => name == sequenceName && tokenLed first
  | .unary name body => name == groupName && tokenLed body
  | _ => false

def firstToken : Description → Option String
  | .symbol text => if (scalars text).isEmpty then none else some (String.ofList ((scalars text).map Char.ofNat))
  | .binary name first _ => if name == sequenceName then firstToken first else none
  | .unary name body => if name == groupName then firstToken body else none
  | _ => none

variable {classes : String → Nat → Prop} {presentation : Presentation} {input : List Nat}
  {expression : Expr} {start stop : Nat}

theorem recognition_monotone
    (run : RecognizesAtUsing classes presentation input expression start stop) : start ≤ stop := by
  induction run with
  | epsilon | char | classMember | literal | starZero | eof => omega
  | altLeft _ ih | altRight _ ih | node _ ih | ref _ _ _ _ ih => exact ih
  | seq _ _ ihFirst ihSecond | left _ _ ihFirst ihSecond | right _ _ ihFirst ihSecond => omega
  | starMore _ _ _ ihHead ihTail | plus _ _ _ ihHead ihTail => omega

theorem recognition_bounded
    (run : RecognizesAtUsing classes presentation input expression start stop)
    (within : start ≤ input.length) : stop ≤ input.length := by
  induction run with
  | epsilon | starZero | eof => omega
  | char lookup | classMember lookup _ =>
      obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp lookup
      omega
  | literal slice =>
      have length := congrArg List.length slice
      simp [List.extract] at length
      omega
  | altLeft _ ih | altRight _ ih | node _ ih | ref _ _ _ _ ih => exact ih within
  | seq _ _ ihFirst ihSecond | left _ _ ihFirst ihSecond | right _ _ ihFirst ihSecond =>
      exact ihSecond (ihFirst within)
  | starMore _ _ _ ihHead ihTail | plus _ _ _ ihHead ihTail => exact ihTail (ihHead within)

variable {bindings : Bindings} {descriptor : Description} {output : List CST}

theorem descriptor_monotone
    (run : Derives bindings classes presentation input descriptor start stop output) : start ≤ stop := by
  obtain ⟨_, _, ⟨target, _⟩⟩ := sound run
  exact recognition_monotone target

theorem descriptor_progress
    (run : Derives bindings classes presentation input descriptor start stop output)
    (guarded : tokenLed descriptor = true) : start < stop := by
  induction run with
  | @symbol text _ _ _ nonempty token spaces =>
      cases token with
      | literal slice =>
          have positive : (scalars text).length ≠ 0 := by
            intro zero
            have empty := List.length_eq_zero_iff.mp zero
            simp [empty] at nonempty
          have after := recognition_monotone spaces
          omega
  | category | constant | parser => simp [tokenLed] at guarded
  | sequence first second firstIH _ =>
      have before := firstIH (by simpa [tokenLed] using guarded)
      have after := descriptor_monotone second
      omega
  | group _ ih => exact ih (by simpa [tokenLed] using guarded)

theorem compiled_progress
    (compiled : lower bindings descriptor = some expression)
    (guarded : tokenLed descriptor = true)
    (run : CSTRecognizesAtUsing classes presentation input expression start stop output) : start < stop := by
  obtain ⟨source⟩ := complete compiled run
  exact descriptor_progress source guarded

/-- A completed command from this profile strictly decreases the actual
remaining-input measure. No per-command boundaries are parameters here. -/
theorem remaining_input_decreases
    (compiled : lower bindings descriptor = some expression)
    (guarded : tokenLed descriptor = true)
    (run : CSTRecognizesAtUsing classes presentation input expression start stop output)
    (within : start ≤ input.length) : input.length - stop < input.length - start := by
  have progress := compiled_progress compiled guarded run
  have bounded := recognition_bounded run.val within
  omega

end Mettapedia.Languages.Lean.ParserDescriptorProgress
