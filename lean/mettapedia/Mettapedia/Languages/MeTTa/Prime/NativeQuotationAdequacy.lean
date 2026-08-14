import Mettapedia.Languages.MeTTa.Prime.NativeTypedQuotation

/-!
# Parser and renderer adequacy for typed MeTTa quotations

The typed quotation boundary has two distinct round trips.

* `NativeCode.renderPattern` is structural.  Its general left-inverse theorem
  is `NativeCode.parseCode_renderPattern`.
* `renderPeTTa?` is textual.  It emits only the expression fragment understood
  by the production PeTTa parser and validates the candidate text against that
  parser before returning it.

This division is intentional.  The internal `Pattern` carrier also contains
binders, substitutions, and collections whose source spelling is not provided
by the current expression parser.  Such values are rejected by the textual
renderer instead of receiving an invented spelling.
-/

namespace Mettapedia.Languages.MeTTa.Prime.NativeQuotationAdequacy

open Mettapedia.Languages.MeTTa.Prime.NativeTypedQuotation
open Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation
open Mettapedia.OSLF.MeTTaIL.Syntax
open scoped Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation

abbrev RuntimePattern :=
  Mettapedia.Languages.MeTTa.Prime.NativeTypedQuotation.RuntimePattern

mutual
  /-- Candidate PeTTa text for the expression-only part of `RuntimePattern`.
  Consumers that require a parser-backed guarantee use the checked
  `renderPeTTa?` boundary below. -/
  def renderCandidate? : RuntimePattern → Option String
    | .fvar name => some ("$" ++ name)
    | .apply constructor [] => some constructor
    | .apply constructor arguments => do
        let rendered ← renderCandidates? arguments
        some ("(" ++ constructor ++ " " ++
          String.intercalate " " rendered ++ ")")
    | _ => none
  termination_by pattern => sizeOf pattern
  decreasing_by all_goals simp_wf

  def renderCandidates? : List RuntimePattern → Option (List String)
    | [] => some []
    | pattern :: patterns => do
        let rendered ← renderCandidate? pattern
        let rest ← renderCandidates? patterns
        some (rendered :: rest)
  termination_by patterns => sizeOf patterns
  decreasing_by all_goals simp_wf <;> omega
end

/-- Render a runtime pattern to PeTTa expression text when the production
parser reads the emitted text back as exactly that pattern. -/
def renderPeTTa? (pattern : RuntimePattern) : Option String :=
  match renderCandidate? pattern with
  | none => none
  | some source =>
      match parsePeTTaPattern source with
      | .error _ => none
      | .ok parsed =>
          if parsed = pattern then some source else none

/-- Every string returned by `renderPeTTa?` is accepted by the production
PeTTa parser as exactly the input pattern. -/
theorem renderPeTTa?_sound {pattern : RuntimePattern} {source : String}
    (rendered : renderPeTTa? pattern = some source) :
    parsePeTTaPattern source = .ok pattern := by
  unfold renderPeTTa? at rendered
  cases candidate : renderCandidate? pattern with
  | none => simp [candidate] at rendered
  | some candidateSource =>
      cases parsed : parsePeTTaPattern candidateSource with
      | error failure => simp [candidate, parsed] at rendered
      | ok parsedPattern =>
          by_cases same : parsedPattern = pattern
          · simp [candidate, parsed, same] at rendered
            subst source
            simpa [same] using parsed
          · simp [candidate, parsed, same] at rendered

/-- Checked PeTTa rendering of an intrinsically scoped native term. -/
def renderNativePeTTa? (code : NativeCode binders) : Option String :=
  NativeQuotationAdequacy.renderPeTTa? code.renderPattern

/-- Text accepted from the native renderer passes both production parsing and
native grammar parsing, recovering the original intrinsically scoped code. -/
theorem renderNativePeTTa?_sound {code : NativeCode binders} {source : String}
    (rendered : renderNativePeTTa? code = some source) :
    ∃ pattern,
      parsePeTTaPattern source = .ok pattern ∧
      parseCode binders pattern = .ok code := by
  refine ⟨code.renderPattern, ?_, code.parseCode_renderPattern⟩
  exact NativeQuotationAdequacy.renderPeTTa?_sound rendered

/-! ## Positive and negative controls -/

/-- One intrinsically scoped term that exercises every constructor in the
current native quotation grammar.  It is a grammar coverage value, not a
typing fixture. -/
def grammarCoverageCode : NativeCode 0 :=
  .superpose
    (.letE .u1
      (.pi (.var ⟨0, by omega⟩)
        (.sigma .u0
          (.id .u0 (.var ⟨0, by omega⟩) (.var ⟨2, by omega⟩)))))
    (.app
      (.lam .u0 (.refl (.var ⟨0, by omega⟩)))
      (.pattern
        (.apply "request"
          [.apply "ticket-7" [], .apply "payload" [.apply "datum" []]])))

/-- A well-typed dependent receipt protocol also survives the complete
AST-render and native-parse path. -/
def dependentReceiptCode : NativeCode 0 :=
  .lam .u0 (.refl (.var ⟨0, by omega⟩))

/-- The production PeTTa quotation elaborator reads the source into exactly
the structural rendering of the intrinsically scoped term. -/
theorem dependentReceiptCode_elaborated :
    (metta% petta "(native:lam native:u0 (native:refl (native:var 0)))") =
      dependentReceiptCode.renderPattern := by
  rfl

/-- Consequently the actual authored quotation is accepted by the native
grammar and recovers the intrinsically scoped term. -/
theorem dependentReceiptCode_source_to_native :
    parseCode 0
        (metta% petta "(native:lam native:u0 (native:refl (native:var 0)))") =
      .ok dependentReceiptCode := by
  rw [dependentReceiptCode_elaborated]
  exact dependentReceiptCode.parseCode_renderPattern

/-- Internal binder nodes have no spelling in the current expression parser
and are therefore rejected by the checked textual renderer. -/
def unsupportedBinderPattern : RuntimePattern :=
  .lambda none (.fvar "x")

theorem unsupportedBinderPattern_not_rendered :
    renderPeTTa? unsupportedBinderPattern = none := by
  have unsupported : renderCandidate? unsupportedBinderPattern = none := by
    unfold unsupportedBinderPattern
    rw [renderCandidate?]
    all_goals simp_all
  unfold renderPeTTa?
  rw [unsupported]

end Mettapedia.Languages.MeTTa.Prime.NativeQuotationAdequacy
