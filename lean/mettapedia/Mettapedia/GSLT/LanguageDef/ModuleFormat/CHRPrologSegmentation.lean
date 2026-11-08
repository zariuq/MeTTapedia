import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRPrologScanPrefix
import Mettapedia.Logic.Prolog.ReaderTermSentence

/-! Segmentation of printed sentences. A printed text is a stream of
sentences, each its lexemes, a full stop and a newline. Whenever the text is
cut into pieces the reader accepts as single sentences, followed by layout,
the pieces are the printed sentences, up to the newline between them
(`segments`). The reader invariant `readOneWith_sentence` and the cut-scanning
lemmas decide where each piece can end. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRPrologTermReadback

open Mettapedia.Logic.Prolog
open Mettapedia.Logic.Prolog.ReaderLexer
open private scanAux fullStopFollows from Mettapedia.Logic.Prolog.ReaderLexer
open Printed

/-! ## Cutting a lexeme stream -/

/-- Every prefix of a lexeme stream's text is some whole lexemes, then a part
of the next lexeme that is neither empty nor all of it, or nothing. -/
theorem cut_stream : ∀ (lexemes : List Lexeme) (text rest : List Char), text ++ rest = lexemes.flatMap Lexeme.chars →
    ∃ count cut, text = (lexemes.take count).flatMap Lexeme.chars ++ cut ∧
      (cut = [] ∨ ∃ lexeme more, lexemes[count]? = some lexeme ∧ lexeme.chars = cut ++ more ∧ cut ≠ [] ∧ more ≠ [])
  | [], text, rest, split => by
    have empty : text = [] := (List.append_eq_nil_iff.mp (by simpa using split)).1
    exact ⟨0, [], by simp [empty], .inl rfl⟩
  | lexeme :: lexemes, text, rest, split => by
    rw [List.flatMap_cons] at split
    rcases List.append_eq_append_iff.mp split with ⟨middle, inside, after⟩ | ⟨middle, beyond, after⟩
    · -- the text ends inside the first lexeme
      by_cases empty : middle = []
      · subst empty
        have same : text = lexeme.chars := by simpa using inside.symm
        subst same
        exact ⟨1, [], by simp, .inl rfl⟩
      · by_cases nothing : text = []
        · exact ⟨0, [], by simp [nothing], .inl rfl⟩
        · exact ⟨0, text, by simp, .inr ⟨lexeme, middle, rfl, inside, nothing, empty⟩⟩
    · -- the text covers the first lexeme
      obtain ⟨count, cut, shape, finish⟩ := cut_stream lexemes middle rest after.symm
      refine ⟨count + 1, cut, ?_, ?_⟩
      · rw [beyond, shape]
        simp [List.take_succ_cons, List.append_assoc]
      · simpa using finish

/-- A stream whose every full stop is followed by a newline. -/
def StopsFollowed (lexemes : List Lexeme) : Prop :=
  ∀ before after, lexemes = before ++ .fullStop :: after → after.head? = some newline

theorem StopsFollowed.tail {lexeme : Lexeme} {rest : List Lexeme} (followed : StopsFollowed (lexeme :: rest)) :
    StopsFollowed rest :=
  fun before after shape => followed (lexeme :: before) after (by rw [shape]; rfl)

theorem StopsFollowed.newline_after {rest : List Lexeme} (followed : StopsFollowed (.fullStop :: rest)) :
    ∃ after, rest.flatMap Lexeme.chars = '\n' :: after := by
  have next := followed [] rest rfl
  cases rest with
  | nil => cases next
  | cons first tail =>
    simp only [List.head?_cons, Option.some.injEq] at next
    subst next
    exact ⟨tail.flatMap Lexeme.chars, by simp [newline, Lexeme.chars]⟩

/-- Cutting a stream keeps every lexeme before the cut reading. -/
theorem ReadsBefore.cut : ∀ {before after : List Lexeme}, ReadsBefore (before ++ after) [] →
    StopsFollowed (before ++ after) → ∀ {cut more : List Char}, cut ++ more = after.flatMap Lexeme.chars →
      ReadsBefore before cut
  | [], _, _, _, _, _, _ => .nil _
  | lexeme :: before, after, whole, followed, cut, more, split => by
    rw [List.cons_append] at whole followed
    cases whole with
    | cons reads later =>
      refine .cons ?_ (ReadsBefore.cut later followed.tail split)
      have chars : (before ++ after).flatMap Lexeme.chars ++ [] =
          (before.flatMap Lexeme.chars ++ cut) ++ more := by
        simp [List.flatMap_append, ← split, List.append_assoc]
      rw [chars] at reads
      refine Lexeme.Reads.prefix (text := before.flatMap Lexeme.chars ++ cut) (more := more) reads fun stop => ?_
      subst stop
      obtain ⟨rest, shape⟩ := followed.newline_after
      rw [← chars, List.append_nil]
      exact ⟨rest, shape⟩

/-! ## Readings that do not depend on positions -/

theorem tokensOf_kinds : ∀ (lexemes : List Lexeme) (position other : Position),
    (tokensOf lexemes position).map Token.kind = (tokensOf lexemes other).map Token.kind
  | [], _, _ => rfl
  | lexeme :: rest, position, other => by
    simp only [tokensOf]
    cases lexeme.kind? with
    | none => exact tokensOf_kinds rest _ _
    | some kind => simp only [List.map_cons, tokensOf_kinds rest (position.advanceMany lexeme.chars)
        (other.advanceMany lexeme.chars)]

theorem fullStop_reads_newline (rest : List Char) : Lexeme.fullStop.Reads ('\n' :: rest) := by
  show fullStopFollows ('\n' :: rest) = true
  unfold fullStopFollows
  split <;> try simp_all
  rename_i shape
  rw [← shape.1]
  decide

/-! ## Sentences, streams and layout -/

/-- Text the reader accepts as one sentence: tokens without a full stop, then
one full stop. -/
def Accepted (text : List Char) : Prop :=
  ∃ clean span, ReaderLexer.scan (String.ofList text) = .ok (clean ++ [⟨.punctuation .fullStop, span⟩]) ∧
    ∀ token ∈ clean, token.kind ≠ .punctuation .fullStop

/-- Text the reference lexer reads as layout only. -/
def Quiet (text : List Char) : Prop := ReaderLexer.scan (String.ofList text) = .ok []

/-- Text that starts with a character that is not layout. -/
def Solid (text : List Char) : Prop :=
  ∃ first rest, text = first :: rest ∧ ReaderLexer.isLayout first = false

/-- The lexemes of one printed sentence before its full stop. -/
structure Body (body : List Lexeme) : Prop where
  starts : ∃ lexeme rest kind, body = lexeme :: rest ∧ lexeme.kind? = some kind
  opens : Solid (body.flatMap Lexeme.chars)
  reads : ReadsBefore (body ++ [.fullStop, newline]) []
  clean : ∀ position, ∀ token ∈ tokensOf body position, token.kind ≠ .punctuation .fullStop

/-- Printed sentences one after another. -/
def stream (bodies : List (List Lexeme)) : List Lexeme := bodies.flatMap (· ++ [.fullStop, newline])

theorem stream_cons (body : List Lexeme) (bodies : List (List Lexeme)) :
    stream (body :: bodies) = body ++ ([.fullStop, newline] ++ stream bodies) := by
  simp [stream, List.append_assoc]

theorem Body.noStop {body : List Lexeme} (shape : Body body) : Lexeme.fullStop ∉ body := by
  intro inside
  obtain ⟨before, after, rfl⟩ := List.mem_iff_append.mp inside
  have := shape.clean Position.initial
  rw [tokensOf_append, tokensOf_kind _ _ rfl] at this
  exact this _ (List.mem_append_right _ (List.mem_cons_self ..)) rfl

theorem stopsFollowed_stream : ∀ (bodies : List (List Lexeme)), (∀ body ∈ bodies, Lexeme.fullStop ∉ body) →
    StopsFollowed (stream bodies)
  | [], _ => fun before after shape => by simp [stream] at shape
  | body :: bodies, noStop => by
    intro before after shape
    have later := stopsFollowed_stream bodies (fun other inside => noStop other (List.mem_cons_of_mem _ inside))
    rw [stream_cons] at shape
    rcases List.append_eq_append_iff.mp shape with ⟨middle, front, back⟩ | ⟨middle, front, back⟩
    · -- the full stop is at or after the end of `body`
      cases middle with
      | nil =>
        simp only [List.nil_append, List.cons_append, List.cons.injEq] at back
        rw [← back.2]
        rfl
      | cons first middle =>
        simp only [List.cons_append, List.cons.injEq] at back
        obtain ⟨_, back⟩ := back
        cases middle with
        | nil =>
          simp only [List.nil_append, List.cons.injEq] at back
          exact absurd back.1 (by simp [newline])
        | cons second middle =>
          simp only [List.cons_append, List.cons.injEq] at back
          exact later middle after back.2
    · -- the full stop is inside `body`
      cases middle with
      | nil =>
        simp only [List.nil_append, List.cons_append, List.cons.injEq] at back
        rw [back.2]
        rfl
      | cons first middle =>
        simp only [List.cons_append, List.cons.injEq] at back
        rw [← back.1] at front
        exact absurd (front ▸ List.mem_append_right _ (List.mem_cons_self ..)) (noStop body (List.mem_cons_self ..))

theorem chars_length_le : ∀ (lexemes : List Lexeme), lexemes.length ≤ (lexemes.flatMap Lexeme.chars).length
  | [] => le_refl _
  | lexeme :: rest => by
    have := chars_length_le rest
    have one : 1 ≤ lexeme.chars.length := by cases lexeme <;> simp [Lexeme.chars]
    simp only [List.length_cons, List.flatMap_cons, List.length_append]
    omega

theorem two_chars {text : List Char} (long : 2 ≤ text.length) : ∃ first second rest, text = first :: second :: rest := by
  match text, long with
  | first :: second :: rest, _ => exact ⟨first, second, rest, rfl⟩

/-- A printed sentence reads before any text that starts with no layout. -/
theorem readsBefore_sentence : ∀ (body : List Lexeme), ReadsBefore (body ++ [.fullStop, newline]) [] →
    ∀ {text : List Char}, (text = [] ∨ ∃ first rest, text = first :: rest ∧ ReaderLexer.isLayout first = false) →
      ReadsBefore (body ++ [.fullStop, newline]) text
  | [], _, text, solid => by
    refine .cons (by simpa [newline, Lexeme.chars] using fullStop_reads_newline text) (.cons ?_ (.nil _))
    refine ⟨by decide, fun next found => ?_⟩
    rcases solid with rfl | ⟨first, rest, rfl, white⟩
    · cases found
    · simp only [List.flatMap_nil, List.nil_append, List.head?_cons, Option.some.injEq] at found
      rw [← found]
      exact white
  | lexeme :: body, whole, text, solid => by
    rw [List.cons_append] at whole ⊢
    cases whole with
    | cons reads later =>
    refine .cons ?_ (readsBefore_sentence body later solid)
    have long : 2 ≤ ((body ++ [Lexeme.fullStop, newline]).flatMap Lexeme.chars ++ []).length := by
      simp [List.flatMap_append, newline, Lexeme.chars]
    obtain ⟨first, second, rest, shape⟩ := two_chars long
    rw [shape] at reads
    have extended := Lexeme.Reads.extend reads text
    rw [← shape, List.append_nil] at extended
    exact extended

theorem readsBefore_stream : ∀ (bodies : List (List Lexeme)), (∀ body ∈ bodies, Body body) →
    ∀ {text : List Char}, (text = [] ∨ ∃ first rest, text = first :: rest ∧ ReaderLexer.isLayout first = false) →
      ReadsBefore (stream bodies) text
  | [], _, _, _ => .nil _
  | body :: bodies, shapes, text, solid => by
    rw [stream_cons, ← List.append_assoc]
    have later := readsBefore_stream bodies (fun other inside => shapes other (List.mem_cons_of_mem _ inside)) solid
    refine ReadsBefore.append (readsBefore_sentence body (shapes body (List.mem_cons_self ..)).reads ?_) later
    cases bodies with
    | nil => simpa [stream] using solid
    | cons next others =>
      obtain ⟨first, rest, opened, white⟩ := (shapes next (List.mem_cons_of_mem _ (List.mem_cons_self ..))).opens
      refine .inr ⟨first, rest ++ ([Lexeme.fullStop, newline] ++ stream others).flatMap Lexeme.chars ++ text, ?_, white⟩
      rw [stream_cons]
      simp [List.flatMap_append, opened, List.append_assoc]

#print axioms readsBefore_stream
#print axioms stopsFollowed_stream

/-! ## Where an accepted piece ends -/

theorem scan_ofList (text : List Char) :
    ReaderLexer.scan (String.ofList text) = scanAux text.length text Position.initial := by
  unfold ReaderLexer.scan
  simp only [String.toList_ofList]

theorem StopsFollowed.cons_newline {lexemes : List Lexeme} (followed : StopsFollowed lexemes) :
    StopsFollowed (newline :: lexemes) := by
  intro before after shape
  cases before with
  | nil => simp [newline] at shape
  | cons first before =>
    simp only [List.cons_append, List.cons.injEq] at shape
    exact followed before after shape.2

theorem ReadsBefore.middle : ∀ {before : List Lexeme} {lexeme : Lexeme} {after : List Lexeme} {text : List Char},
    ReadsBefore (before ++ lexeme :: after) text → ∃ rest, lexeme.Reads rest
  | [], _, _, _, .cons reads _ => ⟨_, reads⟩
  | _ :: before, lexeme, after, text, whole => by
    rw [List.cons_append] at whole
    cases whole with
    | cons _ later => exact ReadsBefore.middle later

theorem tokensOf_gap {gap : List Lexeme} (shape : gap = [] ∨ gap = [newline]) (rest : List Lexeme)
    (position : Position) :
    tokensOf (gap ++ rest) position = tokensOf rest (position.advanceMany (gap.flatMap Lexeme.chars)) := by
  rcases shape with rfl | rfl
  · simp [Position.advanceMany]
  · simp [newline, tokensOf_layout, Lexeme.chars]

theorem mem_before_last {α : Type} {clean front rest : List α} {last first second : α}
    (same : clean ++ [last] = front ++ first :: second :: rest) : first ∈ clean := by
  have lengths := congrArg List.length same
  simp only [List.length_append, List.length_cons, List.length_nil] at lengths
  have inClean : front.length < clean.length := by omega
  have at_ : (clean ++ [last])[front.length]? = (front ++ first :: second :: rest)[front.length]? := by
    rw [same]
  rw [List.getElem?_append_left inClean, List.getElem?_append_right (le_refl _), Nat.sub_self,
    List.getElem?_cons_zero] at at_
  exact List.mem_of_getElem? at_

theorem stream_opens : ∀ (bodies : List (List Lexeme)), (∀ body ∈ bodies, Body body) →
    (stream bodies).flatMap Lexeme.chars = [] ∨ Solid ((stream bodies).flatMap Lexeme.chars)
  | [], _ => .inl rfl
  | body :: bodies, shapes => by
    obtain ⟨first, rest, opened, white⟩ := (shapes body (List.mem_cons_self ..)).opens
    refine .inr ⟨first, rest ++ ([Lexeme.fullStop, newline] ++ stream bodies).flatMap Lexeme.chars, ?_, white⟩
    rw [stream_cons]
    simp [List.flatMap_append, opened]

theorem stream_starts : ∀ (bodies : List (List Lexeme)), (∀ body ∈ bodies, Body body) → bodies ≠ [] →
    ∃ lexeme rest kind, stream bodies = lexeme :: rest ∧ lexeme.kind? = some kind
  | [], _, empty => absurd rfl empty
  | body :: bodies, shapes, _ => by
    obtain ⟨lexeme, rest, kind, rfl, found⟩ := (shapes body (List.mem_cons_self ..)).starts
    exact ⟨lexeme, rest ++ ([Lexeme.fullStop, newline] ++ stream bodies), kind, by rw [stream_cons]; rfl, found⟩

/-- **Printed sentences segment uniquely.** Cut the text of a printed stream,
after an optional newline, into pieces the reader accepts and a remainder the
lexer reads as layout: the pieces are the printed sentences, each with at most
a newline before and after. -/
theorem segments : ∀ (bodies : List (List Lexeme)) (gap : List Lexeme) (texts : List (List Char)) (tail : List Char),
    (gap = [] ∨ gap = [newline]) → (∀ body ∈ bodies, Body body) →
    texts.flatten ++ tail = (gap ++ stream bodies).flatMap Lexeme.chars →
    (∀ text ∈ texts, Accepted text) → Quiet tail →
    List.Forall₂ (fun text body => ∃ before after, (before = [] ∨ before = [newline]) ∧
      (after = [] ∨ after = [newline]) ∧ text = (before ++ body ++ [Lexeme.fullStop] ++ after).flatMap Lexeme.chars)
      texts bodies
  | [], gap, texts, tail, gapShape, _, whole, accepted, _ => by
    cases texts with
    | nil => exact .nil
    | cons text texts =>
      exfalso
      have front : text ++ (texts.flatten ++ tail) = gap.flatMap Lexeme.chars := by
        simpa [stream, List.flatten_cons, List.append_assoc] using whole
      obtain ⟨clean, span, scanned, _⟩ := accepted text (List.mem_cons_self ..)
      have small : text = [] ∨ text = ['\n'] := by
        rcases gapShape with rfl | rfl
        · exact .inl (List.append_eq_nil_iff.mp front).1
        · simp only [newline, List.flatMap_cons, Lexeme.chars, List.flatMap_nil, List.append_nil] at front
          rcases List.append_eq_singleton_iff.mp front with ⟨empty, _⟩ | ⟨single, _⟩
          · exact .inl empty
          · exact .inr single
      rw [scan_ofList] at scanned
      rcases small with rfl | rfl
      · rw [scanAux_nil] at scanned
        simp at scanned
      · rw [List.length_singleton, scanAux_layout 0 '\n' [] _ (by decide) (by simp), scanAux_nil] at scanned
        simp at scanned
  | body :: bodies, gap, texts, tail, gapShape, shapes, whole, accepted, quiet => by
    have shape := shapes body (List.mem_cons_self ..)
    have others : ∀ other ∈ bodies, Body other := fun other inside => shapes other (List.mem_cons_of_mem body inside)
    -- facts about the whole stream
    have followed : StopsFollowed (gap ++ stream (body :: bodies)) := by
      have plain := stopsFollowed_stream (body :: bodies) (fun other inside => (shapes other inside).noStop)
      rcases gapShape with rfl | rfl
      · exact plain
      · exact plain.cons_newline
    have reads : ReadsBefore (gap ++ stream (body :: bodies)) [] := by
      have plain := readsBefore_stream (body :: bodies) shapes (text := []) (.inl rfl)
      rcases gapShape with rfl | rfl
      · exact plain
      · refine .cons ⟨by decide, fun next found => ?_⟩ plain
        obtain ⟨first, rest, opened, white⟩ := shape.opens
        rw [stream_cons] at found
        simp [List.flatMap_append, opened] at found
        rw [← found]
        exact white
    have shapeStream : gap ++ stream (body :: bodies) =
        (gap ++ body ++ [.fullStop]) ++ ([newline] ++ stream bodies) := by
      rw [stream_cons]
      simp [List.append_assoc]
    cases texts with
    | nil =>
      exfalso
      simp only [List.flatten_nil, List.nil_append] at whole
      unfold Quiet at quiet
      rw [whole, ReaderLexer.scan_lexemes _ (allRead_of reads), tokensOf_gap gapShape] at quiet
      obtain ⟨lexeme, rest, kind, opened, found⟩ := stream_starts (body :: bodies) shapes (List.cons_ne_nil _ _)
      rw [opened, tokensOf_kind _ _ found] at quiet
      cases quiet
    | cons text texts =>
      have split : text ++ (texts.flatten ++ tail) = (gap ++ stream (body :: bodies)).flatMap Lexeme.chars := by
        simpa [List.flatten_cons, List.append_assoc] using whole
      obtain ⟨count, cut, textShape, finish⟩ := cut_stream _ text _ split
      obtain ⟨clean, span, scanned, cleanFree⟩ := accepted text (List.mem_cons_self ..)
      set stream' := gap ++ stream (body :: bodies) with streamDef
      have whole' : stream' = stream'.take count ++ stream'.drop count := (List.take_append_drop _ _).symm
      obtain ⟨more, cutSplit⟩ : ∃ more, cut ++ more = (stream'.drop count).flatMap Lexeme.chars := by
        rcases finish with rfl | ⟨lexeme, more, found, chars, _, _⟩
        · exact ⟨_, rfl⟩
        · obtain ⟨inRange, same⟩ := List.getElem?_eq_some_iff.mp found
          refine ⟨more ++ (stream'.drop (count + 1)).flatMap Lexeme.chars, ?_⟩
          rw [List.drop_eq_getElem_cons inRange, same, List.flatMap_cons, chars, List.append_assoc]
      have readsSplit : ReadsBefore (stream'.take count ++ stream'.drop count) [] := by
        rw [← whole']
        exact reads
      have followedSplit : StopsFollowed (stream'.take count ++ stream'.drop count) := by
        rw [← whole']
        exact followed
      have readsTaken := ReadsBefore.cut readsSplit followedSplit cutSplit
      have chainLength := chars_length_le (stream'.take count)
      have scanStep := scanAux_before (stream'.take count)
        (((stream'.take count).flatMap Lexeme.chars).length - (stream'.take count).length + cut.length)
        Position.initial cut readsTaken
      have fuelSame : (stream'.take count).length +
          (((stream'.take count).flatMap Lexeme.chars).length - (stream'.take count).length + cut.length) =
            text.length := by
        rw [textShape, List.length_append]
        omega
      rw [scan_ofList, ← fuelSame, textShape, scanStep] at scanned
      rcases finish with rfl | ⟨lexeme, rest, found, chars, started, unfinished⟩
      · -- the piece ends between two lexemes
        rw [scanAux_nil] at scanned
        simp only [Except.map, Except.ok.injEq, List.append_nil] at scanned
        rw [List.append_nil] at textShape
        have restSplit : texts.flatten ++ tail = (stream'.drop count).flatMap Lexeme.chars := by
          have chars : stream'.flatMap Lexeme.chars =
              (stream'.take count).flatMap Lexeme.chars ++ (stream'.drop count).flatMap Lexeme.chars := by
            rw [← List.flatMap_append, List.take_append_drop]
          rw [chars, textShape] at split
          exact List.append_cancel_left split
        have accepted' : ∀ other ∈ texts, Accepted other := fun other inside =>
          accepted other (List.mem_cons_of_mem _ inside)
        rcases Nat.lt_or_ge count (gap ++ body ++ [Lexeme.fullStop]).length with small | large
        · -- before the full stop: the piece has no full stop
          exfalso
          have within : count ≤ (gap ++ body).length := by simp at small ⊢; omega
          have taken : stream'.take count = (gap ++ body).take count := by
            have shapeBody : stream' = (gap ++ body) ++ ([Lexeme.fullStop, newline] ++ stream bodies) := by
              rw [shapeStream]
              simp [List.append_assoc]
            rw [shapeBody]
            exact List.take_append_of_le_length within
          rw [taken] at scanned
          have pieces := tokensOf_append ((gap ++ body).take count) ((gap ++ body).drop count) Position.initial
          rw [List.take_append_drop, tokensOf_gap gapShape] at pieces
          have inside : (⟨.punctuation .fullStop, span⟩ : Token) ∈ tokensOf body
              (Position.initial.advanceMany (gap.flatMap Lexeme.chars)) := by
            rw [pieces, scanned]
            simp
          exact shape.clean _ _ inside rfl
        · rcases Nat.lt_or_ge (gap ++ body ++ [Lexeme.fullStop]).length count with beyond | atMost
          · -- after the full stop
            have shapeLine : stream' = (gap ++ body ++ [Lexeme.fullStop, newline]) ++ stream bodies := by
              rw [shapeStream]
              simp [List.append_assoc]
            by_cases fits : stream'.take count = gap ++ body ++ [Lexeme.fullStop, newline]
            · have dropped : stream'.drop count = stream bodies := by
                have again := List.take_append_drop count stream'
                rw [fits] at again
                exact List.append_cancel_left (again.trans shapeLine)
              rw [dropped] at restSplit
              refine .cons ⟨gap, [newline], gapShape, .inr rfl, ?_⟩
                (segments bodies [] texts tail (.inl rfl) others (by simpa using restSplit) accepted' quiet)
              rw [textShape, fits]
              simp [List.append_assoc]
            · exfalso
              have lengthLine : (gap ++ body ++ [Lexeme.fullStop, newline]).length ≤ count := by
                simp at beyond ⊢
                omega
              have taken : stream'.take count = (gap ++ body ++ [Lexeme.fullStop, newline]) ++
                  (stream bodies).take (count - (gap ++ body ++ [Lexeme.fullStop, newline]).length) := by
                rw [shapeLine, List.take_append, List.take_of_length_le lengthLine]
              cases bodies with
              | nil =>
                apply fits
                rw [taken]
                simp [stream]
              | cons next later =>
                obtain ⟨lexeme', rest', kind, opened, found'⟩ :=
                  stream_starts (next :: later) others (List.cons_ne_nil _ _)
                obtain ⟨step, stepEq⟩ : ∃ step,
                    count - (gap ++ body ++ [Lexeme.fullStop, newline]).length = step + 1 := by
                  refine ⟨count - (gap ++ body ++ [Lexeme.fullStop, newline]).length - 1, ?_⟩
                  have : (gap ++ body ++ [Lexeme.fullStop, newline]).length ≠ count := by
                    intro same
                    apply fits
                    rw [taken, ← same, Nat.sub_self, List.take_zero, List.append_nil]
                  omega
                have lineTokens : tokensOf (gap ++ body ++ [Lexeme.fullStop, newline]) Position.initial =
                    tokensOf body (Position.initial.advanceMany (gap.flatMap Lexeme.chars)) ++
                      [⟨.punctuation .fullStop,
                        ⟨(Position.initial.advanceMany (gap.flatMap Lexeme.chars)).advanceMany
                            (body.flatMap Lexeme.chars),
                          ((Position.initial.advanceMany (gap.flatMap Lexeme.chars)).advanceMany
                            (body.flatMap Lexeme.chars)).advanceMany ['.']⟩⟩] := by
                  rw [List.append_assoc, tokensOf_gap gapShape, tokensOf_append, tokensOf_kind _ _ rfl, newline,
                    tokensOf_layout, tokensOf_nil]
                  rfl
                rw [taken, stepEq, opened, List.take_succ_cons, tokensOf_append, lineTokens,
                  tokensOf_kind _ _ found'] at scanned
                simp only [List.append_assoc, List.singleton_append] at scanned
                have stuck := mem_before_last scanned.symm
                exact cleanFree _ stuck rfl
          · -- exactly after the full stop
            have equal : count = (gap ++ body ++ [Lexeme.fullStop]).length := by omega
            have taken : stream'.take count = gap ++ body ++ [Lexeme.fullStop] := by
              rw [shapeStream]
              exact List.take_left' equal.symm
            have dropped : stream'.drop count = [newline] ++ stream bodies := by
              rw [shapeStream]
              exact List.drop_left' equal.symm
            rw [dropped] at restSplit
            refine .cons ⟨gap, [], gapShape, .inl rfl, ?_⟩
              (segments bodies [newline] texts tail (.inr rfl) others restSplit accepted' quiet)
            rw [textShape, taken]
            simp
      · -- the piece ends inside a lexeme
        exfalso
        obtain ⟨inRange, same⟩ := List.getElem?_eq_some_iff.mp found
        have around : stream' = stream'.take count ++ lexeme :: stream'.drop (count + 1) := by
          rw [← same, ← List.drop_eq_getElem_cons inRange, List.take_append_drop]
        have readsAround : ReadsBefore (stream'.take count ++ lexeme :: stream'.drop (count + 1)) [] := by
          rw [← around]
          exact reads
        obtain ⟨context, readsLexeme⟩ := ReadsBefore.middle readsAround
        have cutLength := List.length_pos_of_ne_nil started
        obtain ⟨fuel, fuelEq⟩ : ∃ fuel,
            ((stream'.take count).flatMap Lexeme.chars).length - (stream'.take count).length + cut.length =
              fuel + 1 :=
          ⟨((stream'.take count).flatMap Lexeme.chars).length - (stream'.take count).length + cut.length - 1,
            by omega⟩
        rw [fuelEq] at scanned
        rcases scanAux_cut readsLexeme chars started unfinished fuel
            (Position.initial.advanceMany ((stream'.take count).flatMap Lexeme.chars)) with
          ⟨error, failed⟩ | ⟨token, single, other⟩
        · rw [failed] at scanned
          simp [Except.map] at scanned
        · rw [single] at scanned
          simp only [Except.map, Except.ok.injEq] at scanned
          have last := (List.append_inj' scanned rfl).2
          simp only [List.cons.injEq, and_true] at last
          exact other (by rw [last])

#print axioms segments
#print axioms cut_stream
#print axioms ReadsBefore.cut

end Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRPrologTermReadback
