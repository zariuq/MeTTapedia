import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRPrologSegmentation

/-! The canonical text of a CHR program as a stream of printed sentences: the
library directive, the declarations and the option directive, the rules and
the query. Each is a `Body` that reads as its form with or without a newline
before and after it (`program_bodies`), so any cut of the canonical text into
accepted sentences and layout reads as the program's forms
(`program_segments`). -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRPrologTermReadback

open Mettapedia.Logic.Prolog
open Mettapedia.Logic.Prolog.ReaderLexer
open Mettapedia.Languages
open Printed
open private isIdentifierContinue fullStopFollows from Mettapedia.Logic.Prolog.ReaderLexer
open CHRPrologReadback (programForms ProgramPrintable QueryPrintable RulePrintable declarations_form query_form
  library_form option_form libraryDirective optionDirective declarationsSource querySource ruleVariables)
open Mettapedia.Languages.CHR.TupleNormal (normalRule)

/-! ## A checkable reading condition -/

/-- A sufficient condition for `Lexeme.Reads` that can be evaluated. -/
def readsCheck : Lexeme → List Char → Bool
  | .quoted _, rest => rest.head? != some '\''
  | .identifier first more, rest =>
      first.isAlpha && more.all isIdentifierContinue && !(rest.head?.any isIdentifierContinue)
  | .graphic first more, rest =>
      isGraphic first && first != '.' && (first != '/' || (more ++ rest).head? != some '*') && more.all isGraphic &&
        !(rest.head?.any isGraphic)
  | .number _ _, _ => false
  | .punctuation character value, _ =>
      decide ((character, value) ∈ [('(', Punctuation.leftParen), (')', .rightParen), (',', .comma), ('|', .bar)])
  | .fullStop, rest => fullStopFollows rest
  | .layout character, rest => ReaderLexer.isLayout character && !(rest.head?.any ReaderLexer.isLayout)

theorem readsCheck_sound : ∀ (lexeme : Lexeme) (rest : List Char), readsCheck lexeme rest = true → lexeme.Reads rest
  | .quoted _, rest, check => by
    intro next found
    simp only [readsCheck, found, bne_iff_ne, ne_eq, Option.some.injEq] at check
    exact check
  | .identifier first more, rest, check => by
    simp only [readsCheck, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at check
    obtain ⟨⟨alpha, continues⟩, stops⟩ := check
    refine ⟨alpha, continues, fun next found => ?_⟩
    rw [found] at stops
    simpa using stops
  | .graphic first more, rest, check => by
    simp only [readsCheck, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true',
      List.all_eq_true] at check
    obtain ⟨⟨⟨⟨graphic, notDot⟩, notComment⟩, continues⟩, stops⟩ := check
    refine ⟨graphic, notDot, fun slash => ?_, continues, fun next found => ?_⟩
    · rcases notComment with notSlash | notStar
      · exact absurd slash notSlash
      · exact notStar
    · rw [found] at stops
      simpa using stops
  | .number _ _, _, check => by simp [readsCheck] at check
  | .punctuation character value, _, check =>
    of_decide_eq_true (p := (character, value) ∈ [('(', Punctuation.leftParen), (')', .rightParen), (',', .comma),
      ('|', .bar)]) check
  | .fullStop, rest, check => check
  | .layout character, rest, check => by
    simp only [readsCheck, Bool.and_eq_true, Bool.not_eq_true'] at check
    obtain ⟨white, stops⟩ := check
    refine ⟨white, fun next found => ?_⟩
    rw [found] at stops
    simpa using stops

def readsBeforeCheck : List Lexeme → List Char → Bool
  | [], _ => true
  | lexeme :: rest, text => readsCheck lexeme (rest.flatMap Lexeme.chars ++ text) && readsBeforeCheck rest text

theorem readsBeforeCheck_sound : ∀ (lexemes : List Lexeme) (text : List Char),
    readsBeforeCheck lexemes text = true → ReadsBefore lexemes text
  | [], text, _ => .nil text
  | lexeme :: rest, text, check => by
    simp only [readsBeforeCheck, Bool.and_eq_true] at check
    exact .cons (readsCheck_sound _ _ check.1) (readsBeforeCheck_sound rest text check.2)

/-! ## Facts about any printed sentence -/

theorem solid_of_first {body : List Lexeme} {lexeme : Lexeme} {more : List Lexeme} {first : Char} {rest : List Char}
    (shape : body = lexeme :: more) (chars : lexeme.chars = first :: rest) (white : ReaderLexer.isLayout first = false) :
    Solid (body.flatMap Lexeme.chars) :=
  ⟨first, rest ++ more.flatMap Lexeme.chars, by rw [shape, List.flatMap_cons, chars, List.cons_append], white⟩

/-- A sentence the reader reads to its end has no full stop before its own. -/
theorem clean_of_parses {body : List Lexeme} {position : Position} {result : ReaderTerm.Result}
    (parsed : ReaderTerm.parseOneWith chr chr.operators (tokensOf (body ++ [Lexeme.fullStop, newline]) position) =
      .ok result)
    (finished : result.remaining = []) :
    ∀ other, ∀ token ∈ tokensOf body other, token.kind ≠ .punctuation .fullStop := by
  obtain ⟨clean, span, shape, free⟩ := ReaderTerm.parseOneWith_sentence parsed finished
  rw [tokensOf_append, tokensOf_kind _ _ rfl, newline, tokensOf_layout, tokensOf_nil] at shape
  have same := (List.append_inj' shape rfl).1
  intro other token inside
  have kinds := tokensOf_kinds body other position
  have mapped : token.kind ∈ (tokensOf body position).map Token.kind := by
    rw [← kinds]
    exact List.mem_map_of_mem inside
  rw [same] at mapped
  obtain ⟨found, member, sameKind⟩ := List.mem_map.mp mapped
  rw [← sameKind]
  exact free found member

theorem Body.stopsFollowed {body : List Lexeme} (shape : Body body) :
    StopsFollowed (body ++ [Lexeme.fullStop, newline]) := by
  have followed := stopsFollowed_stream [body] (fun other inside => by
    rw [List.mem_singleton.mp inside]
    exact shape.noStop)
  simpa [stream] using followed

/-- A printed sentence lexes the same with or without a newline before and
after it, up to where its tokens start. -/
theorem scan_variant {body : List Lexeme} (shape : Body body) {before after : List Lexeme}
    (gapBefore : before = [] ∨ before = [newline]) (gapAfter : after = [] ∨ after = [newline]) :
    ReaderLexer.scan (String.ofList ((before ++ body ++ [Lexeme.fullStop] ++ after).flatMap Lexeme.chars)) =
      .ok (tokensOf (body ++ [Lexeme.fullStop, newline])
        (Position.initial.advanceMany (before.flatMap Lexeme.chars))) := by
  have inner : ReadsBefore (body ++ [Lexeme.fullStop] ++ after) [] := by
    rcases gapAfter with rfl | rfl
    · have whole : ReadsBefore ((body ++ [Lexeme.fullStop]) ++ [newline]) [] := by
        simpa using shape.reads
      have followed : StopsFollowed ((body ++ [Lexeme.fullStop]) ++ [newline]) := by
        simpa using shape.stopsFollowed
      simpa using ReadsBefore.cut whole followed (cut := []) (more := ['\n']) rfl
    · simpa using shape.reads
  have all : ReadsBefore (before ++ body ++ [Lexeme.fullStop] ++ after) [] := by
    rcases gapBefore with rfl | rfl
    · simpa using inner
    · obtain ⟨first, rest, opened, white⟩ := shape.opens
      have list : [newline] ++ body ++ [Lexeme.fullStop] ++ after = newline :: (body ++ [Lexeme.fullStop] ++ after) := by
        simp
      rw [list]
      refine .cons ⟨by decide, fun next found => ?_⟩ inner
      simp only [List.flatMap_append, opened, List.cons_append, List.head?_cons, Option.some.injEq] at found
      rw [← found]
      exact white
  rw [ReaderLexer.scan_lexemes _ (allRead_of all)]
  congr 1
  have shapeList : before ++ body ++ [Lexeme.fullStop] ++ after = before ++ (body ++ ([Lexeme.fullStop] ++ after)) := by
    simp [List.append_assoc]
  rw [shapeList, tokensOf_gap gapBefore]
  simp only [tokensOf_append]
  rcases gapAfter with rfl | rfl <;> simp [tokensOf, Lexeme.kind?, Lexeme.chars, newline]

/-- A printed sentence that parses to its end reads the same with or without
a newline before and after it. -/
theorem variant_reads {body : List Lexeme} (shape : Body body) {before after : List Lexeme}
    (gapBefore : before = [] ∨ before = [newline]) (gapAfter : after = [] ∨ after = [newline])
    {source : SourceSignature.Term} {bindings : List ReaderTerm.VariableBinding}
    (parses : ReaderTerm.parseOneWith chr chr.operators
      (tokensOf (body ++ [Lexeme.fullStop, newline]) (Position.initial.advanceMany (before.flatMap Lexeme.chars))) =
        .ok ⟨source, bindings, []⟩) :
    ReaderTerm.readOneWith chr chr.operators
        (String.ofList ((before ++ body ++ [Lexeme.fullStop] ++ after).flatMap Lexeme.chars)) =
      .ok ⟨source, bindings, []⟩ := by
  unfold ReaderTerm.readOneWith
  rw [scan_variant shape gapBefore gapAfter]
  simp only [bind, Except.bind, parses]
  rfl

/-! ## The sentences of a program -/

def libraryBody : List Lexeme :=
  [bare ":-", space, bare "use_module", openParen, bare "library", openParen, bare "chr", closeParen, closeParen]

def optionBody : List Lexeme :=
  [bare ":-", space, bare "chr_option", openParen, bare "optimize", comma, bare "off", closeParen]

def declarationsBody (declarations : List CHR.Declaration) : List Lexeme :=
  [bare ":-", space, bare "chr_constraint", space] ++ separated (declarations.map declarationLexemes)

def ruleBody (rule : CHR.Rule) : List Lexeme :=
  [quoted rule.name, space, bare "@", space] ++ headsLexemes rule ++ [space, bare (arrowName rule), space] ++
    rightLexemes rule

def queryBody (inputs : List CHR.Constraint) : List Lexeme :=
  [bare "?-", space] ++ separated (inputs.map constraintLexemes)

theorem bare_directive_chars : (bare ":-").chars = [':', '-'] := by decide_cbv
theorem bare_query_chars : (bare "?-").chars = ['?', '-'] := by decide_cbv

theorem fixed_body {body : List Lexeme} (readsChecked : readsBeforeCheck (body ++ [Lexeme.fullStop, newline]) [] = true)
    (cleanChecked : (tokensOf body Position.initial).all (fun token => token.kind != .punctuation .fullStop) = true)
    (shape : body = bare ":-" :: body.tail) : Body body where
  starts := ⟨bare ":-", body.tail, _, shape, directive_kind⟩
  opens := solid_of_first shape bare_directive_chars (by decide)
  reads := readsBeforeCheck_sound _ _ readsChecked
  clean := by
    intro other token inside
    have kinds := tokensOf_kinds body other Position.initial
    have mapped : token.kind ∈ (tokensOf body Position.initial).map Token.kind := by
      rw [← kinds]
      exact List.mem_map_of_mem inside
    obtain ⟨found, member, sameKind⟩ := List.mem_map.mp mapped
    rw [List.all_eq_true] at cleanChecked
    have := cleanChecked found member
    rw [← sameKind]
    simpa using this

theorem library_body : Body libraryBody := fixed_body (by decide_cbv) (by decide_cbv) rfl
theorem option_body : Body optionBody := fixed_body (by decide_cbv) (by decide_cbv) rfl

theorem declarations_parses (declarations : List CHR.Declaration) (nonempty : declarations ≠ []) (position : Position) :
    ∃ bindings, ReaderTerm.parseOneWith chr chr.operators (tokensOf (declarationsLexemes declarations) position) =
      .ok ⟨declarationsSource declarations, bindings, []⟩ := by
  obtain ⟨directiveSpan, wordSpan, itemsPosition, stopSpan, listed⟩ := declarations_tokens declarations position
  refine ⟨(readerState [] []).bindings.reverse, ?_⟩
  unfold ReaderTerm.parseOneWith
  rw [listed]
  dsimp only
  erw [declarations_expression declarations nonempty directiveSpan wordSpan stopSpan itemsPosition _
    (by simp; omega)]
  simp only [bind, Except.bind]
  rw [consume_full_stop _ stopSpan [] rfl]
  rfl

theorem query_parses (inputs : List CHR.Constraint) (nonempty : inputs ≠ []) (position : Position) :
    ∃ bindings, ReaderTerm.parseOneWith chr chr.operators (tokensOf (queryLexemes inputs) position) =
      .ok ⟨querySource inputs, bindings, []⟩ := by
  obtain ⟨querySpan, itemsPosition, stopSpan, listed⟩ := query_tokens inputs position
  refine ⟨(readerState [] []).bindings.reverse, ?_⟩
  unfold ReaderTerm.parseOneWith
  rw [listed]
  dsimp only
  erw [query_expression inputs nonempty querySpan stopSpan itemsPosition _ (by simp; omega)]
  simp only [bind, Except.bind]
  rw [consume_full_stop _ stopSpan [] rfl]
  rfl

theorem rule_body (rule : CHR.Rule) (heads : rule.kept ++ rule.removed ≠ []) : Body (ruleBody rule) where
  starts := ⟨quoted rule.name, _, _, rfl, quoted_kind rule.name⟩
  opens := solid_of_first rfl (rest := rule.name.toList.flatMap quotedChars ++ ['\'']) rfl (by decide)
  reads := rule_reads_before rule
  clean := by
    obtain ⟨bindings, parsed⟩ := rule_parses rule heads Position.initial
    exact clean_of_parses parsed rfl

theorem declarations_body (declarations : List CHR.Declaration) (nonempty : declarations ≠ []) :
    Body (declarationsBody declarations) where
  starts := ⟨bare ":-", _, _, rfl, directive_kind⟩
  opens := solid_of_first rfl bare_directive_chars (by decide)
  reads := declarations_reads_before declarations nonempty
  clean := by
    obtain ⟨bindings, parsed⟩ := declarations_parses declarations nonempty Position.initial
    exact clean_of_parses parsed rfl

theorem query_body (inputs : List CHR.Constraint) (nonempty : inputs ≠ []) : Body (queryBody inputs) where
  starts := ⟨bare "?-", _, _, rfl, query_kind⟩
  opens := solid_of_first rfl bare_query_chars (by decide)
  reads := query_reads_before inputs nonempty
  clean := by
    obtain ⟨bindings, parsed⟩ := query_parses inputs nonempty Position.initial
    exact clean_of_parses parsed rfl

/-- A printed sentence that reads as `form` with any newline before and after. -/
def VariantReads (body : List Lexeme) (form : CHRPrologLowering.Form) : Prop :=
  ∀ before after : List Lexeme, (before = [] ∨ before = [newline]) → (after = [] ∨ after = [newline]) →
    SentenceReads (String.ofList ((before ++ body ++ [Lexeme.fullStop] ++ after).flatMap Lexeme.chars)) form

theorem library_variants : VariantReads libraryBody .metadata := by
  intro before after gapBefore gapAfter
  rcases gapBefore with rfl | rfl <;> rcases gapAfter with rfl | rfl <;>
    exact fixed_sentence _ _ _ (by decide_cbv) library_form

theorem option_variants : VariantReads optionBody .metadata := by
  intro before after gapBefore gapAfter
  rcases gapBefore with rfl | rfl <;> rcases gapAfter with rfl | rfl <;>
    exact fixed_sentence _ _ _ (by decide_cbv) option_form

theorem rule_variants (rule : CHR.Rule) (printable : RulePrintable rule) :
    VariantReads (ruleBody rule) (.rule (normalRule rule)) := by
  intro before after gapBefore gapAfter
  obtain ⟨bindings, parsed⟩ := rule_parses rule printable.heads
    (Position.initial.advanceMany (before.flatMap Lexeme.chars))
  exact ⟨_, variant_reads (rule_body rule printable.heads) gapBefore gapAfter parsed, fun ordinal =>
    CHRPrologReadback.rule_form (nameIn (ruleVariables rule)) (fun _ => rfl) ordinal rule printable⟩

theorem declarations_variants (declarations : List CHR.Declaration) (nonempty : declarations ≠ []) :
    VariantReads (declarationsBody declarations) (.declarations declarations) := by
  intro before after gapBefore gapAfter
  obtain ⟨bindings, parsed⟩ := declarations_parses declarations nonempty
    (Position.initial.advanceMany (before.flatMap Lexeme.chars))
  exact ⟨_, variant_reads (declarations_body declarations nonempty) gapBefore gapAfter parsed,
    fun ordinal => declarations_form ordinal declarations nonempty⟩

theorem query_variants (inputs : List CHR.Constraint) (nonempty : inputs ≠ [])
    (printable : ∀ constraint ∈ inputs, QueryPrintable constraint) :
    VariantReads (queryBody inputs) (.query inputs) := by
  intro before after gapBefore gapAfter
  obtain ⟨bindings, parsed⟩ := query_parses inputs nonempty (Position.initial.advanceMany (before.flatMap Lexeme.chars))
  exact ⟨_, variant_reads (query_body inputs nonempty) gapBefore gapAfter parsed,
    fun ordinal => query_form ordinal inputs nonempty printable⟩

/-- The printed sentences of a program, before their full stops. -/
def programBodies (program : CHR.Program) (inputs : List CHR.Constraint) : List (List Lexeme) :=
  [libraryBody] ++
    (if program.declarations.isEmpty then [] else [declarationsBody program.declarations, optionBody]) ++
    program.rules.map ruleBody ++ (if inputs.isEmpty then [] else [queryBody inputs])

theorem program_bodies (program : CHR.Program) (inputs : List CHR.Constraint) (printable : ProgramPrintable program inputs) :
    (∀ body ∈ programBodies program inputs, Body body) ∧
      List.Forall₂ VariantReads (programBodies program inputs) (programForms program inputs) := by
  have declarations : (∀ body ∈ (if program.declarations.isEmpty then [] else
        [declarationsBody program.declarations, optionBody]), Body body) ∧
      List.Forall₂ VariantReads
        (if program.declarations.isEmpty then [] else [declarationsBody program.declarations, optionBody])
        (if program.declarations.isEmpty then [] else [.declarations program.declarations, .metadata]) := by
    by_cases empty : program.declarations.isEmpty
    · simp only [empty, if_true]
      exact ⟨fun _ inside => absurd inside List.not_mem_nil, .nil⟩
    · simp only [empty, if_false, Bool.false_eq_true]
      have nonempty : program.declarations ≠ [] := by simpa using empty
      refine ⟨fun body inside => ?_, .cons (declarations_variants _ nonempty) (.cons option_variants .nil)⟩
      rcases List.mem_cons.mp inside with rfl | inside
      · exact declarations_body _ nonempty
      · rw [List.mem_singleton.mp inside]
        exact option_body
  have rules : (∀ body ∈ program.rules.map ruleBody, Body body) ∧
      List.Forall₂ VariantReads (program.rules.map ruleBody) (program.rules.map fun rule => .rule (normalRule rule)) := by
    refine ⟨fun body inside => ?_, ?_⟩
    · obtain ⟨rule, member, rfl⟩ := List.mem_map.mp inside
      exact rule_body rule (printable.rules rule member).heads
    · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      exact List.forall₂_same.mpr fun rule inside => rule_variants rule (printable.rules rule inside)
  have query : (∀ body ∈ (if inputs.isEmpty then [] else [queryBody inputs]), Body body) ∧
      List.Forall₂ VariantReads (if inputs.isEmpty then [] else [queryBody inputs])
        (if inputs.isEmpty then [] else [.query inputs]) := by
    by_cases empty : inputs.isEmpty
    · simp only [empty, if_true]
      exact ⟨fun _ inside => absurd inside List.not_mem_nil, .nil⟩
    · simp only [empty, if_false, Bool.false_eq_true]
      have nonempty : inputs ≠ [] := by simpa using empty
      refine ⟨fun body inside => ?_, .cons (query_variants inputs nonempty printable.inputs) .nil⟩
      rw [List.mem_singleton.mp inside]
      exact query_body inputs nonempty
  refine ⟨fun body inside => ?_, ?_⟩
  · simp only [programBodies, List.mem_append, List.mem_singleton] at inside
    rcases inside with ((rfl | inside) | inside) | inside
    · exact library_body
    · exact declarations.1 body inside
    · exact rules.1 body inside
    · exact query.1 body inside
  · exact List.rel_append (List.rel_append (List.rel_append (.cons library_variants .nil) declarations.2) rules.2)
      query.2

theorem rule_body_chars (rule : CHR.Rule) :
    (ruleBody rule ++ [Lexeme.fullStop, newline]).flatMap Lexeme.chars = (CHRPrologPrinter.rule rule).toList :=
  (rule_chars rule).symm

theorem declarations_body_chars (declarations : List CHR.Declaration) :
    (declarationsBody declarations ++ [Lexeme.fullStop, newline]).flatMap Lexeme.chars =
      (declarationsText declarations).toList :=
  (declarations_chars declarations).symm

theorem query_body_chars (inputs : List CHR.Constraint) (nonempty : inputs ≠ []) :
    (queryBody inputs ++ [Lexeme.fullStop, newline]).flatMap Lexeme.chars = (queryText inputs).toList :=
  (query_chars inputs nonempty).symm

/-- The printed sentences, one after another, are the canonical text. -/
theorem program_stream_chars (program : CHR.Program) (inputs : List CHR.Constraint) :
    (stream (programBodies program inputs)).flatMap Lexeme.chars = (CHRPrologPrinter.program program inputs).toList := by
  have library : (libraryBody ++ [Lexeme.fullStop, newline]).flatMap Lexeme.chars = libraryText.toList := by
    decide_cbv
  have option : (optionBody ++ [Lexeme.fullStop, newline]).flatMap Lexeme.chars = optionText.toList := by
    decide_cbv
  have each : (programBodies program inputs).map (fun body => (body ++ [Lexeme.fullStop, newline]).flatMap Lexeme.chars) =
      (programSentences program inputs).map String.toList := by
    unfold programSentences programBodies
    simp only [List.map_append, List.map_cons, List.map_nil]
    refine congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) ?_ ?_) ?_) ?_
    · rw [library]
    · by_cases empty : program.declarations.isEmpty
      · simp [empty]
      · simp only [empty, Bool.false_eq_true, if_false, List.map_cons, List.map_nil]
        rw [declarations_body_chars, option]
    · rw [List.map_map, List.map_map]
      apply List.map_congr_left
      intro rule _
      exact rule_body_chars rule
    · by_cases empty : inputs.isEmpty
      · simp [empty]
      · have nonempty : inputs ≠ [] := by simpa using empty
        simp only [empty, Bool.false_eq_true, if_false, List.map_cons, List.map_nil]
        rw [query_body_chars inputs nonempty]
  rw [program_text, String.toList_join, stream, List.flatMap_assoc, List.flatMap_def, List.flatMap_def, each]

/-- **The canonical text segments into the program's forms.** Cut it into
pieces the reader accepts and a remainder the lexer reads as layout: the
pieces read, in order, as the forms of the program. -/
theorem program_segments (program : CHR.Program) (inputs : List CHR.Constraint)
    (printable : ProgramPrintable program inputs) (texts : List (List Char)) (tail : List Char)
    (whole : texts.flatten ++ tail = (CHRPrologPrinter.program program inputs).toList)
    (accepted : ∀ text ∈ texts, Accepted text) (quiet : Quiet tail) :
    List.Forall₂ (fun text form => SentenceReads (String.ofList text) form) texts (programForms program inputs) := by
  obtain ⟨shapes, reads⟩ := program_bodies program inputs printable
  have cut := segments (programBodies program inputs) [] texts tail (.inl rfl) shapes
    (by rw [List.nil_append, program_stream_chars]; exact whole) accepted quiet
  clear whole accepted quiet
  generalize programBodies program inputs = bodies at cut reads
  generalize programForms program inputs = forms at reads ⊢
  induction cut generalizing forms with
  | nil =>
    cases reads
    exact .nil
  | @cons text body texts bodies variant _ ih =>
    cases reads with
    | cons first rest =>
      obtain ⟨before, after, gapBefore, gapAfter, rfl⟩ := variant
      exact .cons (first before after gapBefore gapAfter) (ih _ rest)

#print axioms program_segments
#print axioms program_bodies

end Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRPrologTermReadback
