import Mettapedia.Languages.ProcessCalculi.MORK.MM2MatchingBatch

/-!
# The admitted native MM2 input and sink grammar

The MM2 resource profile accepts conjunction inputs or explicit unary BTM
factors, and explicit unary add/remove sinks. Transactional read/take/all/
absence inputs belong to another resource profile. Equality/exclusion factors
in the broader source theory are not admitted by this native grammar.

The original input presentation is retained. Only the cursor's factor list
is compared: rewriting the stored directive would change reflective reads.
Explicit source matching records witnesses in source order, whereas the
structural cursor accumulates them on a stack; the comparison exposes that
reversal.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ProgrammableSpaceMM2Grammar

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK
open MM2MatchingCursor
open Conformance.Computable

def btmAtom (pattern : Atom) : Atom :=
  .expression [.symbol "BTM", pattern]

def unaryBTM : Atom → Bool
  | .expression [.symbol "BTM", _] => true
  | _ => false

def unarySink : Atom → Bool
  | .expression [.symbol "+", _] => true
  | .expression [.symbol "-", _] => true
  | _ => false

def inputGrammar : Atom → Bool
  | .expression (.symbol "," :: _) => true
  | .expression (.symbol "I" :: factors) => factors.all unaryBTM
  | _ => false

def grammar : Atom → Bool
  | .expression [.symbol "exec", _, input, .expression (.symbol "O" :: sinks)] =>
      inputGrammar input && sinks.all unarySink
  | _ => false

theorem unaryBTM_iff (atom : Atom) :
    unaryBTM atom = true ↔ ∃ pattern, atom = btmAtom pattern := by
  unfold unaryBTM
  split
  · rename_i pattern
    exact ⟨fun _ => ⟨pattern, rfl⟩, fun _ => rfl⟩
  · rename_i other
    constructor
    · intro impossible
      cases impossible
    · rintro ⟨pattern, rfl⟩
      exact False.elim (other pattern rfl)

theorem all_unaryBTM_iff (raw : List Atom) :
    raw.all unaryBTM = true ↔ ∃ patterns : List Atom, raw = patterns.map btmAtom := by
  induction raw with
  | nil => exact ⟨fun _ => ⟨[], rfl⟩, fun _ => rfl⟩
  | cons first rest ih =>
      simp only [List.all_cons, Bool.and_eq_true, unaryBTM_iff, ih]
      constructor
      · rintro ⟨⟨pattern, rfl⟩, ⟨patterns, rfl⟩⟩
        exact ⟨pattern :: patterns, rfl⟩
      · rintro ⟨patterns, equal⟩
        cases patterns with
        | nil => cases equal
        | cons pattern patterns =>
            cases equal
            exact ⟨⟨pattern, rfl⟩, ⟨patterns, rfl⟩⟩

inductive InputSyntax : Atom → List Atom → Prop where
  | compat (patterns : List Atom) :
      InputSyntax (.expression (.symbol "," :: patterns)) patterns
  | explicit (patterns : List Atom) :
      InputSyntax (.expression (.symbol "I" :: patterns.map btmAtom)) patterns

theorem inputGrammar_iff (input : Atom) :
    inputGrammar input = true ↔ ∃ patterns, InputSyntax input patterns := by
  constructor
  · unfold inputGrammar
    split
    · rename_i patterns
      exact fun _ => ⟨patterns, .compat patterns⟩
    · rename_i raw
      intro accepted
      obtain ⟨patterns, rfl⟩ := (all_unaryBTM_iff raw).mp accepted
      exact ⟨patterns, .explicit patterns⟩
    · intro impossible
      cases impossible
  · rintro ⟨patterns, authored⟩
    cases authored with
    | compat => rfl
    | explicit =>
        exact (all_unaryBTM_iff _).mpr ⟨patterns, rfl⟩

theorem parse_btm_factors (patterns : List Atom) :
    parseSupportedSourceFactors (patterns.map btmAtom) =
      some (patterns.map SourceFactor.btm) := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns ih =>
      simp [List.map_cons, parseSupportedSourceFactors, parseSupportedSourceFactor,
        btmAtom, ih]

theorem InputSyntax.decoded {input : Atom} {patterns : List Atom}
    (authored : InputSyntax input patterns) :
    ∃ decoded, parseSupportedInput input = some decoded ∧
      factors decoded = patterns.map SourceFactor.btm := by
  cases authored with
  | compat => exact ⟨.compat ⟨patterns⟩, rfl, rfl⟩
  | explicit =>
      refine ⟨.explicit (patterns.map SourceFactor.btm), ?_, rfl⟩
      simp [parseSupportedInput, parse_btm_factors]

theorem unarySink_decodes (atom : Atom) (accepted : unarySink atom = true) :
    ∃ sink, parseSupportedSink atom = some sink := by
  unfold unarySink at accepted
  split at accepted
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · cases accepted

theorem all_unarySink_decodes (raw : List Atom)
    (accepted : raw.all unarySink = true) :
    ∃ sinks, parseSupportedSinkList raw = some sinks := by
  induction raw with
  | nil => exact ⟨[], rfl⟩
  | cons first rest ih =>
      simp only [List.all_cons, Bool.and_eq_true] at accepted
      obtain ⟨firstAccepted, restAccepted⟩ := accepted
      obtain ⟨sink, decoded⟩ := unarySink_decodes first firstAccepted
      obtain ⟨sinks, restDecoded⟩ := ih restAccepted
      exact ⟨sink :: sinks, by simp [parseSupportedSinkList, decoded, restDecoded]⟩

theorem supported_parsing_fields (location input output : Atom)
    (decodedInput : InputSpec) (decodedOutput : Template)
    (inputParsed : parseSupportedInput input = some decodedInput)
    (outputParsed : parseSupportedTemplate output = some decodedOutput) :
    ∃ directive,
      extractSupportedSourceExecFact
        (.expression [.symbol "exec", location, input, output]) = some directive ∧
      directive.atom = .expression [.symbol "exec", location, input, output] ∧
      directive.rule.input = decodedInput ∧ directive.rule.guards = [] := by
  simp [extractSupportedSourceExecFact, extractRawExecFact, decodeSupportedSourceExec,
    inputParsed, outputParsed]

/-- The independently defined broader source parser accepts every atom in
the native MM2 grammar, with only BTM matching factors and no implicit guard. -/
theorem grammar_decodes (atom : Atom) (accepted : grammar atom = true) :
    ∃ (directive : SourceExecFact) (pattern : Pattern),
      extractSupportedSourceExecFact atom = some directive ∧
      directive.atom = atom ∧
      factors directive.rule.input = pattern.atoms.map SourceFactor.btm ∧
      directive.rule.guards = [] := by
  unfold grammar at accepted
  split at accepted
  · rename_i location input sinks
    simp only [Bool.and_eq_true] at accepted
    obtain ⟨inputAccepted, sinkAccepted⟩ := accepted
    obtain ⟨patterns, authored⟩ := (inputGrammar_iff input).mp inputAccepted
    obtain ⟨decodedInput, inputParsed, factorization⟩ := authored.decoded
    obtain ⟨decodedSinks, sinksParsed⟩ := all_unarySink_decodes sinks sinkAccepted
    have outputParsed : parseSupportedTemplate (.expression (.symbol "O" :: sinks)) =
        some ⟨decodedSinks⟩ := by
      simp [parseSupportedTemplate, sinksParsed, mkTemplate]
    obtain ⟨directive, parsed, original, inputExact, guardsExact⟩ :=
      supported_parsing_fields location input (.expression (.symbol "O" :: sinks))
        decodedInput ⟨decodedSinks⟩ inputParsed outputParsed
    exact ⟨directive, ⟨patterns⟩, parsed, original,
      by simpa [inputExact] using factorization, guardsExact⟩
  · cases accepted

/-- Exact reversal of the explicit source executor's witness list. -/
theorem btm_source_rows (space : List Atom) (patterns : List Atom)
    (substitution : Subst) (previous : List Atom) :
    cmatchSourceFactors.go space (patterns.map SourceFactor.btm) substitution previous =
      (cMatchSourceFactorsMork substitution space (patterns.map SourceFactor.btm)).map
        (fun row => (row.1, row.2.reverse ++ previous)) := by
  induction patterns generalizing substitution previous with
  | nil => simp [cmatchSourceFactors.go, cMatchSourceFactorsMork]
  | cons pattern patterns ih =>
      simp only [List.map_cons, cmatchSourceFactors.go, cMatchSourceFactorsMork,
        cMatchSourceFactorMork, cmatchSourceFactor, List.map_flatMap]
      apply congrArg (fun continuation => List.flatMap continuation
        (space.filterMap fun atom => (cmatchAtom substitution pattern atom).map (·, atom)))
      funext found
      rw [ih]
      simp [List.map_map, Function.comp_def, List.reverse_cons, List.append_assoc]

def sourceRow (input : InputSpec) (row : Row) : Subst × List Atom :=
  match input with
  | .compat _ => eraseRow row
  | .explicit _ => (row.1, (row.2.map Prod.fst).reverse)

theorem sourceRow_substitution (input : InputSpec) (row : Row) :
    (sourceRow input row).1 = row.1 := by
  cases input <;> rfl

theorem btm_cursor_rows (space : List Atom) (input : InputSpec) (patterns : Pattern)
    (factorization : factors input = patterns.atoms.map SourceFactor.btm)
    (substitution : Subst) :
    (StructuralQuanta.residualRows (entries space)
      (StructuralQuanta.start space input substitution)).map (sourceRow input) =
        cMatchInputSpecMork substitution space input := by
  cases input with
  | compat pattern =>
      exact StructuralQuanta.start_rows_erase space (.compat pattern) substitution
  | explicit sourceFactors =>
      change sourceFactors = patterns.atoms.map SourceFactor.btm at factorization
      subst sourceFactors
      have original := StructuralQuanta.start_rows_erase space
        (.explicit (patterns.atoms.map SourceFactor.btm)) substitution
      have compared := congrArg
        (List.map fun row : Subst × List Atom => (row.1, row.2.reverse)) original
      rw [cmatchInputSpec, cmatchSourceFactors, btm_source_rows] at compared
      change (StructuralQuanta.residualRows (entries space)
        (StructuralQuanta.start space
          (.explicit (patterns.atoms.map SourceFactor.btm)) substitution)).map
          (fun row => (row.1, (row.2.map Prod.fst).reverse)) =
            cMatchSourceFactorsMork substitution space (patterns.atoms.map SourceFactor.btm)
      simpa [List.map_map, Function.comp_def, sourceRow, eraseRow,
        cMatchInputSpecMork] using compared

end Mettapedia.GSLT.LanguageDef.ProgrammableSpaceMM2Grammar
