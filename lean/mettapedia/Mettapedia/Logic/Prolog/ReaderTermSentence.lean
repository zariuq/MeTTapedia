import Mettapedia.Logic.Prolog.ReaderTerm

/-! The reader reads exactly one sentence. No term consumes a full stop, so a
text that `readOneWith` accepts lexes to tokens without a full stop followed
by one full stop (`readOneWith_sentence`). -/

set_option autoImplicit false

namespace Mettapedia.Logic.Prolog.ReaderTerm

open ReaderLexer ReaderOperator

open private parseExpressionAux parsePrefixOrPrimaryAux parsePrefixAux parsePrimaryAux parseApplicationAux
  parseArgumentsAux parseListAux parseListTailAux parseTailAux consumePunctuation failAt operatorName?
  firstEligiblePrefix from Mettapedia.Logic.Prolog.ReaderTerm

/-- `before` is `after` behind tokens none of which is a full stop. -/
def Consumed (before after : List Token) : Prop :=
  ∃ eaten, before = eaten ++ after ∧ ∀ token ∈ eaten, token.kind ≠ .punctuation .fullStop

theorem Consumed.refl (tokens : List Token) : Consumed tokens tokens :=
  ⟨[], rfl, fun _ inside => absurd inside List.not_mem_nil⟩

theorem Consumed.trans {first second third : List Token} (one : Consumed first second)
    (two : Consumed second third) : Consumed first third := by
  obtain ⟨eaten, rfl, clean⟩ := one
  obtain ⟨more, rfl, clean'⟩ := two
  refine ⟨eaten ++ more, by rw [List.append_assoc], fun token inside => ?_⟩
  rcases List.mem_append.mp inside with early | late
  · exact clean token early
  · exact clean' token late

theorem Consumed.cons {token : Token} {rest : List Token} (other : token.kind ≠ .punctuation .fullStop) :
    Consumed (token :: rest) rest :=
  ⟨[token], rfl, fun found inside => by
    rw [List.mem_singleton.mp inside]
    exact other⟩

theorem Consumed.drop {tokens : List Token}
    (other : ∀ token, tokens.head? = some token → token.kind ≠ .punctuation .fullStop) :
    Consumed tokens (tokens.drop 1) := by
  cases tokens with
  | nil => exact Consumed.refl _
  | cons token rest => exact Consumed.cons (other token rfl)

theorem failAt_ne {α : Type} {state : State} {kind : ErrorKind} {value : α} :
    (failAt state kind : Except Error α) ≠ .ok value := by
  simp [failAt]

theorem consumePunctuation_ok {punctuation : Punctuation} {state after : State}
    (consumed : consumePunctuation punctuation state = .ok after) :
    ∃ span rest, state.remaining = ⟨.punctuation punctuation, span⟩ :: rest ∧ after.remaining = rest := by
  unfold consumePunctuation at consumed
  rcases state with ⟨remaining, bindings, next⟩
  cases remaining with
  | nil => exact absurd consumed failAt_ne
  | cons token rest =>
    rcases token with ⟨kind, span⟩
    cases kind with
    | punctuation actual =>
      simp only at consumed
      by_cases same : actual = punctuation
      · subst same
        rw [if_pos rfl] at consumed
        cases consumed
        exact ⟨span, rest, rfl, rfl⟩
      · rw [if_neg same] at consumed
        exact absurd consumed failAt_ne
    | atom _ => exact absurd consumed failAt_ne
    | quotedAtom _ => exact absurd consumed failAt_ne
    | «variable» _ => exact absurd consumed failAt_ne
    | number _ => exact absurd consumed failAt_ne
    | string _ => exact absurd consumed failAt_ne
    | backQuoted _ => exact absurd consumed failAt_ne

theorem consumePunctuation_consumed {punctuation : Punctuation} {state after : State}
    (other : punctuation ≠ .fullStop) (consumed : consumePunctuation punctuation state = .ok after) :
    Consumed state.remaining after.remaining := by
  obtain ⟨span, rest, remaining, after⟩ := consumePunctuation_ok consumed
  rw [remaining, after]
  exact Consumed.cons (by simpa using other)

theorem internVariable_remaining (spelling : String) (state : State) :
    (internVariable spelling state).2.remaining = state.remaining := by
  unfold internVariable
  split
  · rfl
  · split <;> rfl

theorem operatorName_other {profile : ReaderProfile.Profile} {kind : Kind} {name : String}
    (named : operatorName? profile kind = some name) : kind ≠ .punctuation .fullStop := by
  intro same
  subst same
  simp [operatorName?] at named

/-- What the reader's functions consume at one fuel. -/
structure Stops (profile : ReaderProfile.Profile) (fuel : Nat) : Prop where
  expression : ∀ table maximum state parsed, parseExpressionAux profile fuel table maximum state = .ok parsed →
    Consumed state.remaining parsed.state.remaining
  prefixOrPrimary : ∀ table maximum state parsed,
    parsePrefixOrPrimaryAux profile fuel table maximum state = .ok parsed →
      Consumed state.remaining parsed.state.remaining
  prefixOperator : ∀ table maximum state name parsed,
    (∀ token, state.remaining.head? = some token → token.kind ≠ .punctuation .fullStop) →
    parsePrefixAux profile fuel table maximum state name = .ok parsed → Consumed state.remaining parsed.state.remaining
  primary : ∀ table state parsed, parsePrimaryAux profile fuel table state = .ok parsed →
    Consumed state.remaining parsed.state.remaining
  application : ∀ table name state parsed, parseApplicationAux profile fuel table name state = .ok parsed →
    Consumed state.remaining parsed.state.remaining
  arguments : ∀ table state result, parseArgumentsAux profile fuel table state = .ok result →
    Consumed state.remaining result.2.remaining
  list : ∀ table state parsed, parseListAux profile fuel table state = .ok parsed →
    Consumed state.remaining parsed.state.remaining
  listTail : ∀ table reversed state parsed, parseListTailAux profile fuel table reversed state = .ok parsed →
    Consumed state.remaining parsed.state.remaining
  tail : ∀ table maximum left parsed, parseTailAux profile fuel table maximum left = .ok parsed →
    Consumed left.state.remaining parsed.state.remaining

section Steps

variable {profile : ReaderProfile.Profile} {fuel : Nat}

theorem prefix_stops
    (expression : ∀ table maximum state parsed, parseExpressionAux profile fuel table maximum state = .ok parsed →
      Consumed state.remaining parsed.state.remaining)
    (table : Table) (maximum : Nat) (state : State) (name : String) (parsed : Parsed)
    (other : ∀ token, state.remaining.head? = some token → token.kind ≠ .punctuation .fullStop)
    (read : parsePrefixAux profile fuel table maximum state name = .ok parsed) :
    Consumed state.remaining parsed.state.remaining := by
  unfold parsePrefixAux at read
  cases found : firstEligiblePrefix table name maximum with
  | none =>
    simp only [found, failAt, bind, Except.bind] at read
    cases read
  | some declaration =>
    cases bounded : declaration.specifier.rightMaximum declaration.priority.value with
    | none =>
      simp only [found, bounded, failAt, bind, Except.bind, pure, Except.pure] at read
      cases read
    | some rightMaximum =>
      cases right : parseExpressionAux profile fuel table rightMaximum
          { state with remaining := state.remaining.drop 1 } with
      | error reason =>
        simp only [found, bounded, right, bind, Except.bind, pure, Except.pure] at read
        cases read
      | ok value =>
        simp only [found, bounded, right, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at read
        subst read
        exact (Consumed.drop other).trans (expression _ _ _ _ right)

theorem arguments_stops (previous : Stops profile fuel) (table : Table) (state : State)
    (result : List SourceSignature.Term × State) (read : parseArgumentsAux profile (fuel + 1) table state = .ok result) :
    Consumed state.remaining result.2.remaining := by
  unfold parseArgumentsAux at read
  cases argument : parseExpressionAux profile fuel table 999 state with
  | error reason =>
    simp only [argument, bind, Except.bind] at read
    cases read
  | ok argumentParsed =>
    simp only [argument, bind, Except.bind] at read
    have first := previous.expression _ _ _ _ argument
    split at read
    · rename_i commaSpan rest remaining
      cases more : parseArgumentsAux profile fuel table { argumentParsed.state with remaining := rest } with
      | error reason =>
        simp only [more] at read
        cases read
      | ok value =>
        rcases value with ⟨terms, after⟩
        simp only [more, pure, Except.pure, Except.ok.injEq] at read
        subst read
        rw [remaining] at first
        exact (first.trans (Consumed.cons (by simp))).trans (previous.arguments _ _ _ more)
    · simp only [pure, Except.pure, Except.ok.injEq] at read
      subst read
      exact first

theorem application_stops
    (arguments : ∀ table state result, parseArgumentsAux profile fuel table state = .ok result →
      Consumed state.remaining result.2.remaining)
    (table : Table) (name : String) (state : State) (parsed : Parsed)
    (read : parseApplicationAux profile fuel table name state = .ok parsed) :
    Consumed state.remaining parsed.state.remaining := by
  unfold parseApplicationAux at read
  split at read
  · rename_i _ rest remaining
    split at read
    · exact absurd read failAt_ne
    · simp only [Except.ok.injEq] at read
      subst read
      rw [remaining]
      exact Consumed.cons (by simp)
  · cases listed : parseArgumentsAux profile fuel table state with
    | error reason =>
      simp only [listed, bind, Except.bind] at read
      cases read
    | ok value =>
      rcases value with ⟨terms, afterArguments⟩
      simp only [listed, bind, Except.bind] at read
      cases closed : consumePunctuation .rightParen afterArguments with
      | error reason =>
        simp only [closed] at read
        cases read
      | ok after =>
        simp only [closed, pure, Except.pure, Except.ok.injEq] at read
        subst read
        exact (arguments _ _ _ listed).trans (consumePunctuation_consumed (by simp) closed)

theorem listTail_stops
    (expression : ∀ table maximum state parsed, parseExpressionAux profile fuel table maximum state = .ok parsed →
      Consumed state.remaining parsed.state.remaining)
    (listTail : ∀ table reversed state parsed, parseListTailAux profile fuel table reversed state = .ok parsed →
      Consumed state.remaining parsed.state.remaining)
    (table : Table) (reversed : List SourceSignature.Term) (state : State) (parsed : Parsed)
    (read : parseListTailAux profile (fuel + 1) table reversed state = .ok parsed) :
    Consumed state.remaining parsed.state.remaining := by
  unfold parseListTailAux at read
  split at read
  · rename_i _ rest remaining
    cases next : parseExpressionAux profile fuel table 999 { state with remaining := rest } with
    | error reason =>
      simp only [next, bind, Except.bind] at read
      cases read
    | ok value =>
      simp only [next, bind, Except.bind] at read
      rw [remaining]
      exact ((Consumed.cons (by simp)).trans (expression _ _ _ _ next)).trans (listTail _ _ _ _ read)
  · rename_i _ rest remaining
    cases tailRead : parseExpressionAux profile fuel table 999 { state with remaining := rest } with
    | error reason =>
      simp only [tailRead, bind, Except.bind] at read
      cases read
    | ok value =>
      simp only [tailRead, bind, Except.bind] at read
      cases closed : consumePunctuation .rightBracket value.state with
      | error reason =>
        simp only [closed] at read
        cases read
      | ok after =>
        simp only [closed, pure, Except.pure, Except.ok.injEq] at read
        subst read
        rw [remaining]
        exact ((Consumed.cons (by simp)).trans (expression _ _ _ _ tailRead)).trans
          (consumePunctuation_consumed (by simp) closed)
  · rename_i _ rest remaining
    simp only [Except.ok.injEq] at read
    subst read
    rw [remaining]
    exact Consumed.cons (by simp)
  · exact absurd read failAt_ne

end Steps

theorem stops_zero (profile : ReaderProfile.Profile) : Stops profile 0 := by
  have expression : ∀ table maximum state parsed, parseExpressionAux profile 0 table maximum state = .ok parsed →
      Consumed state.remaining parsed.state.remaining := by
    intro table maximum state parsed read
    unfold parseExpressionAux at read
    exact absurd read failAt_ne
  have arguments : ∀ table state result, parseArgumentsAux profile 0 table state = .ok result →
      Consumed state.remaining result.2.remaining := by
    intro table state result read
    unfold parseArgumentsAux at read
    exact absurd read failAt_ne
  refine ⟨expression, ?_, prefix_stops expression, ?_, application_stops arguments, arguments, ?_, ?_, ?_⟩
  · intro table maximum state parsed read
    unfold parsePrefixOrPrimaryAux at read
    exact absurd read failAt_ne
  · intro table state parsed read
    unfold parsePrimaryAux at read
    exact absurd read failAt_ne
  · intro table state parsed read
    unfold parseListAux at read
    exact absurd read failAt_ne
  · intro table reversed state parsed read
    unfold parseListTailAux at read
    exact absurd read failAt_ne
  · intro table maximum left parsed read
    unfold parseTailAux at read
    exact absurd read failAt_ne

theorem stops_succ {profile : ReaderProfile.Profile} {fuel : Nat} (previous : Stops profile fuel) :
    Stops profile (fuel + 1) := by
  have expression : ∀ table maximum state parsed,
      parseExpressionAux profile (fuel + 1) table maximum state = .ok parsed →
        Consumed state.remaining parsed.state.remaining := by
    intro table maximum state parsed read
    unfold parseExpressionAux at read
    cases left : parsePrefixOrPrimaryAux profile fuel table maximum state with
    | error reason =>
      simp only [left, bind, Except.bind] at read
      cases read
    | ok value =>
      simp only [left, bind, Except.bind] at read
      exact (previous.prefixOrPrimary _ _ _ _ left).trans (previous.tail _ _ _ _ read)
  have arguments : ∀ table state result, parseArgumentsAux profile (fuel + 1) table state = .ok result →
      Consumed state.remaining result.2.remaining := arguments_stops previous
  refine ⟨expression, ?_, prefix_stops expression, ?_, application_stops arguments, arguments, ?_,
    listTail_stops previous.expression previous.listTail, ?_⟩
  · -- prefix or primary
    intro table maximum state parsed read
    unfold parsePrefixOrPrimaryAux at read
    repeat' split at read
    all_goals first
      | exact absurd read failAt_ne
      | exact previous.primary _ _ _ read
      | (apply previous.prefixOperator _ _ _ _ _ _ read
         intro token same
         rw [‹state.remaining = _›] at same
         cases same
         simp)
      | (simp only [Except.ok.injEq] at read
         subst read
         rw [‹state.remaining = _›]
         exact (Consumed.cons (by simp)).trans (Consumed.cons (by simp)))
  · -- primary
    intro table state parsed read
    unfold parsePrimaryAux at read
    cases remaining : state.remaining with
    | nil =>
      rw [remaining] at read
      exact absurd read failAt_ne
    | cons token rest =>
      rw [remaining] at read
      rcases token with ⟨kind, span⟩
      cases kind with
      | «variable» spelling =>
        simp only [Except.ok.injEq] at read
        subst read
        rw [internVariable_remaining]
        exact Consumed.cons (by simp)
      | number lexeme =>
        simp only at read
        split at read
        · exact absurd read failAt_ne
        · simp only [Except.ok.injEq] at read
          subst read
          exact Consumed.cons (by simp)
      | string value =>
        simp only [Except.ok.injEq] at read
        subst read
        exact Consumed.cons (by simp)
      | backQuoted value =>
        simp only at read
        split at read
        · exact absurd read failAt_ne
        · simp only [Except.ok.injEq] at read
          subst read
          exact Consumed.cons (by simp)
      | atom name =>
        simp only at read
        split at read
        · split at read
          · exact ((Consumed.cons (by simp)).trans (Consumed.cons (by simp))).trans
              (previous.application _ _ _ _ read)
          · simp only [Except.ok.injEq] at read
            subst read
            exact Consumed.cons (by simp)
        · simp only [Except.ok.injEq] at read
          subst read
          exact Consumed.cons (by simp)
      | quotedAtom name =>
        simp only at read
        split at read
        · split at read
          · exact ((Consumed.cons (by simp)).trans (Consumed.cons (by simp))).trans
              (previous.application _ _ _ _ read)
          · simp only [Except.ok.injEq] at read
            subst read
            exact Consumed.cons (by simp)
        · simp only [Except.ok.injEq] at read
          subst read
          exact Consumed.cons (by simp)
      | punctuation value =>
        cases value with
        | leftParen =>
          simp only at read
          cases nested : parseExpressionAux profile fuel table 1200 { state with remaining := rest } with
          | error reason =>
            simp only [nested, bind, Except.bind] at read
            cases read
          | ok inner =>
            simp only [nested, bind, Except.bind] at read
            cases closed : consumePunctuation .rightParen inner.state with
            | error reason =>
              simp only [closed] at read
              cases read
            | ok after =>
              simp only [closed, pure, Except.pure, Except.ok.injEq] at read
              subst read
              exact ((Consumed.cons (by simp)).trans (previous.expression _ _ _ _ nested)).trans
                (consumePunctuation_consumed (by simp) closed)
        | leftBracket =>
          simp only at read
          exact (Consumed.cons (by simp)).trans (previous.list _ _ _ read)
        | leftBrace =>
          simp only at read
          split at read
          · simp only [Except.ok.injEq] at read
            subst read
            exact (Consumed.cons (by simp)).trans (Consumed.cons (by simp))
          · cases nested : parseExpressionAux profile fuel table 1200 { state with remaining := rest } with
            | error reason =>
              simp only [nested, bind, Except.bind] at read
              cases read
            | ok inner =>
              simp only [nested, bind, Except.bind] at read
              cases closed : consumePunctuation .rightBrace inner.state with
              | error reason =>
                simp only [closed] at read
                cases read
              | ok after =>
                simp only [closed, pure, Except.pure, Except.ok.injEq] at read
                subst read
                exact ((Consumed.cons (by simp)).trans (previous.expression _ _ _ _ nested)).trans
                  (consumePunctuation_consumed (by simp) closed)
        | rightParen => exact absurd read failAt_ne
        | rightBracket => exact absurd read failAt_ne
        | rightBrace => exact absurd read failAt_ne
        | comma => exact absurd read failAt_ne
        | bar => exact absurd read failAt_ne
        | fullStop => exact absurd read failAt_ne
  · -- list
    intro table state parsed read
    unfold parseListAux at read
    split at read
    · rename_i _ rest remaining
      simp only [Except.ok.injEq] at read
      subst read
      rw [remaining]
      exact Consumed.cons (by simp)
    · cases head : parseExpressionAux profile fuel table 999 state with
      | error reason =>
        simp only [head, bind, Except.bind] at read
        cases read
      | ok value =>
        simp only [head, bind, Except.bind] at read
        exact (previous.expression _ _ _ _ head).trans (previous.listTail _ _ _ _ read)
  · -- operator loop
    intro table maximum left parsed read
    unfold parseTailAux at read
    simp only [bind, Except.bind] at read
    repeat' split at read
    all_goals first
      | (simp only [Except.ok.injEq] at read
         subst read
         exact Consumed.refl _)
      | exact absurd read failAt_ne
      | cases read
      | (rw [‹left.state.remaining = _›]
         have named := ‹operatorName? profile _ = some _›
         have later := previous.tail _ _ _ _ read
         exact (Consumed.cons (operatorName_other named)).trans later)
      | (rw [‹left.state.remaining = _›]
         have named := ‹operatorName? profile _ = some _›
         have inner := previous.expression _ _ _ _ ‹parseExpressionAux profile fuel _ _ _ = .ok _›
         have later := previous.tail _ _ _ _ read
         exact ((Consumed.cons (operatorName_other named)).trans inner).trans later)

theorem stops (profile : ReaderProfile.Profile) : ∀ fuel, Stops profile fuel
  | 0 => stops_zero profile
  | fuel + 1 => stops_succ (stops profile fuel)

/-- A token list the reader reads to its end is tokens without a full stop,
then one full stop. -/
theorem parseOneWith_sentence {profile : ReaderProfile.Profile} {table : Table} {tokens : List Token}
    {result : Result} (parsed : parseOneWith profile table tokens = .ok result) (finished : result.remaining = []) :
    ∃ body span, tokens = body ++ [⟨.punctuation .fullStop, span⟩] ∧
      ∀ token ∈ body, token.kind ≠ .punctuation .fullStop := by
  unfold parseOneWith at parsed
  cases expression : parseExpressionAux profile (tokens.length * 4 + 8) table 1200 { remaining := tokens } with
  | error reason =>
    simp only [expression, bind, Except.bind] at parsed
    cases parsed
  | ok value =>
    simp only [expression, bind, Except.bind] at parsed
    cases stopped : consumePunctuation .fullStop value.state with
    | error reason =>
      simp only [stopped] at parsed
      cases parsed
    | ok after =>
      simp only [stopped, pure, Except.pure, Except.ok.injEq] at parsed
      subst parsed
      obtain ⟨span, rest, remaining, afterRemaining⟩ := consumePunctuation_ok stopped
      obtain ⟨eaten, split, clean⟩ := (stops profile _).expression _ _ _ _ expression
      refine ⟨eaten, span, ?_, clean⟩
      simp only at split finished
      rw [← afterRemaining, finished] at remaining
      rw [split, remaining]

/-- **One sentence.** A text the reader accepts lexes to tokens without a full
stop, followed by one full stop. -/
theorem readOneWith_sentence {profile : ReaderProfile.Profile} {table : Table} {source : String} {result : Result}
    (read : readOneWith profile table source = .ok result) :
    ∃ body span, scan source = .ok (body ++ [⟨.punctuation .fullStop, span⟩]) ∧
      ∀ token ∈ body, token.kind ≠ .punctuation .fullStop := by
  unfold readOneWith at read
  cases scanned : scan source with
  | error reason => simp [scanned] at read
  | ok tokens =>
    simp only [scanned] at read
    cases parsedOne : parseOneWith profile table tokens with
    | error reason =>
      simp only [parsedOne, bind, Except.bind] at read
      cases read
    | ok value =>
      simp only [parsedOne, bind, Except.bind] at read
      have empty : value.remaining = [] := by
        revert read
        cases value.remaining with
        | nil => intro _; rfl
        | cons token rest => intro read; simp at read
      obtain ⟨body, span, shape, clean⟩ := parseOneWith_sentence parsedOne empty
      exact ⟨body, span, by rw [shape], clean⟩

#print axioms parseOneWith_sentence
#print axioms readOneWith_sentence

end Mettapedia.Logic.Prolog.ReaderTerm
