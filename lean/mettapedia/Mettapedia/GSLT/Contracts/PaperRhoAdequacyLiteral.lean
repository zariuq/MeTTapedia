import Mettapedia.GSLT.Contracts.PaperRhoNamed

/-!
# Exact adequacy on the paper's reading

On the paper's reading (`Named.literal`) no binder reaches into a quotation,
so every quotation of a reading is closed code. This module connects that
reading to the COMM step of our calculus.

* `instantiate_literalBody`: on the reading of the body of `x(y).P`,
  `instantiate` with a closed replacement is the compiled COMM substitution
  `substituteReflective`.
* `substituteReflective_encode_eq_iff`: for a body whose quotations are closed,
  the compiled substitution is the paper's substitution spelling for spelling
  exactly when the quotations of the body are resolved and, if the body uses
  the binder, the communicated payload is in quote-drop normal form.
* `instantiate_literal_exact_iff`: the same on the paper's reading, and
  `instantiate_literal_exact` on the fiber where both readings are resolved.
* `canonicalize_instantiate_literal`: up to the equations, with no condition.
* `literal_reduction_iff_rhoStep`, `literal_transGen_iff`: the reading of a
  named process is closed, so its paper reductions are the steps of our
  calculus from the canonical form of its encoding.
* `literal_comm_steps_exactly`: on the fiber, the COMM step of our calculus from
  the plain encoding of a named redex lands on the paper's contractum.

Off the fiber, a reading keeps a spelling `@(*x)` that our substitution
resolves to `x` (`Controls.quotedDrop_not_exact`), and a payload spelled with
`@(*x)` is normalized when it is communicated
(`Controls.quotedDropPayload_not_exact`). The responsible law is quote-drop,
`@(*x) ≡N x`: our substitution applies it, while the paper's substitution only
compares names by it. A whole-name alias of a binder is not the cause, since
readings never produce one (`Named.readName_quote_no_alias`), and it is not
enough: `*@(*@0)` has no alias and still fails. On the binding-aware reading the
quotations are not closed and exactness fails even up to the equations
(`Controls.dynamicQuote_bindingAware_not_exact`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.PaperRho.LiteralAdequacy

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.ReflectiveQuoteAdmission (mentions mentionsList)
open Mettapedia.OSLF.MeTTaIL.ReflectiveCoherent (QuotesResolved QuotesResolvedList
  resolveQuotes_resolved resolveQuotes_of_resolved normalizeReflective_of_resolved
  resolveQuotes_isWellScopedAt substituteResolved_of_isWellScopedAt substituteResolved_drop)
open Mettapedia.OSLF.MeTTaIL.ReflectiveInstantiation (instantiate closed_agreement
  normalizeReflective_scoped)
open Mettapedia.OSLF.MeTTaIL.ScopedPattern (binderSafeAt binderSafeListAt
  isWellScopedAt_of_binderSafeAt isWellScopedAt_mono)
open Mettapedia.GSLT.Contracts.PaperRho.PatternBoundary
open Mettapedia.GSLT.Contracts.PaperRho.Adequacy
open Mettapedia.GSLT.Contracts.PaperRho.Named
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep (RhoStep)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalRepresentativeStep
  (rhoStepAt_comm_at CanonicalStep)

/-! ## The compiled substitution on bodies with closed quotations -/

/-- The index action of the compiled COMM substitution that passes the name
`@value`. -/
private abbrev passing (value : Pattern) : Nat → Nat → Pattern :=
  fun level index => if index = level then .apply "NQuote" [value] else .bvar index

private theorem resolveQuotes_eq_self_iff (pattern : Pattern) :
    resolveQuotes rhoReflectivePresentation pattern = pattern ↔
      QuotesResolved rhoReflectivePresentation pattern := by
  refine ⟨fun fixed => ?_, resolveQuotes_of_resolved⟩
  have resolved := resolveQuotes_resolved (declaration := rhoReflectivePresentation) pattern
  rwa [fixed] at resolved

private theorem quote_closed {code : Process} {level : Nat}
    (safe : binderSafeAt "NQuote" level (encodeName (.quote code)) = true) :
    (encodeName (.quote code)).isWellScopedAt 0 = true := by
  apply isWellScopedAt_of_binderSafeAt "NQuote" (depth := 0)
  simpa [encodeName, binderSafeAt] using safe

private theorem binderIndex_of_closed {n : Name} (closed : (encodeName n).isWellScopedAt 0 = true) :
    binderIndex n = none := by
  cases hit : binderIndex n with
  | none => rfl
  | some index =>
      have inScope := canonicalize_scoped rhoReflectivePresentation closed
      rw [(canonicalize_encodeName_eq_bvar_iff n index).mpr hit] at inScope
      simp [Pattern.isWellScopedAt] at inScope

private theorem substituteResolved_closed {value pattern : Pattern} (depth : Nat)
    (closed : pattern.isWellScopedAt 0 = true) :
    substituteResolved rhoReflectivePresentation (passing value) depth
        (resolveQuotes rhoReflectivePresentation pattern) =
      resolveQuotes rhoReflectivePresentation pattern :=
  substituteResolved_of_isWellScopedAt _ (fun _ _ below => by simp [Nat.ne_of_lt below])
    (isWellScopedAt_mono (resolveQuotes_isWellScopedAt closed) (Nat.zero_le _))

private theorem matchesBinder_resolved_closed {pattern : Pattern} (depth : Nat)
    (closed : pattern.isWellScopedAt 0 = true) :
    matchesBinder rhoReflectivePresentation depth
      (resolveQuotes rhoReflectivePresentation pattern) = false := by
  simp only [matchesBinder, decide_eq_false_iff_not, BinderHead.ofPattern_index_iff]
  intro equality
  have safe := canonicalize_scoped rhoReflectivePresentation
    (resolveQuotes_isWellScopedAt (declaration := rhoReflectivePresentation) closed)
  simp [equality, Pattern.isWellScopedAt] at safe

private theorem substituteResolved_dropPattern (value name : Pattern) (depth : Nat) :
    substituteResolved rhoReflectivePresentation (passing value) depth (.apply "PDrop" [name]) =
      if matchesBinder rhoReflectivePresentation depth name then
        receive rhoReflectivePresentation "PDrop" (passing value depth depth)
      else
        .apply "PDrop" [substituteResolved rhoReflectivePresentation (passing value) depth name] :=
  substituteResolved_drop (declaration := rhoReflectivePresentation) (by decide) _ depth name

/-- A drop of a closed name is fixed by the compiled substitution after
resolution. -/
private theorem dropPattern_closed {value name : Pattern} (depth : Nat)
    (closed : name.isWellScopedAt 0 = true) :
    substituteResolved rhoReflectivePresentation (passing value) depth
        (resolveQuotes rhoReflectivePresentation (.apply "PDrop" [name])) =
      .apply "PDrop" [resolveQuotes rhoReflectivePresentation name] := by
  have resolved : resolveQuotes rhoReflectivePresentation (.apply "PDrop" [name]) =
      .apply "PDrop" [resolveQuotes rhoReflectivePresentation name] := by
    simp [resolveQuotes, resolveQuotesList, finishResolveApply, rhoReflectivePresentation]
  rw [resolved, substituteResolved_dropPattern, matchesBinder_resolved_closed depth closed,
    substituteResolved_closed depth closed]
  rfl

private theorem receive_passing (value : Pattern) (depth : Nat) :
    receive rhoReflectivePresentation "PDrop" (passing value depth depth) = value := by
  simp [passing, receive, rhoReflectivePresentation]

private theorem quotesResolved_pair (constructor : String) (first second : Pattern) :
    QuotesResolved rhoReflectivePresentation (.apply constructor [first, second]) ↔
      QuotesResolved rhoReflectivePresentation first ∧
        QuotesResolved rhoReflectivePresentation second := by
  simp [QuotesResolved, QuotesResolvedList]

private theorem quotesResolved_lambda (binder : Option String) (body : Pattern) :
    QuotesResolved rhoReflectivePresentation (.lambda binder body) ↔
      QuotesResolved rhoReflectivePresentation body := Iff.rfl

private theorem quotesResolved_drop (name : Pattern) :
    QuotesResolved rhoReflectivePresentation (.apply "PDrop" [name]) ↔
      QuotesResolved rhoReflectivePresentation name := by
  simp [QuotesResolved, QuotesResolvedList, rhoReflectivePresentation]

private theorem split_iff {A B QA QB MA MB V : Prop} (first : A ↔ QA ∧ (MA → V))
    (second : B ↔ QB ∧ (MB → V)) : A ∧ B ↔ (QA ∧ QB) ∧ (MA ∨ MB → V) := by
  rw [first, second]
  constructor
  · rintro ⟨⟨qa, va⟩, qb, vb⟩
    exact ⟨⟨qa, qb⟩, fun used => used.elim va vb⟩
  · rintro ⟨⟨qa, qb⟩, v⟩
    exact ⟨⟨qa, fun used => v (.inl used)⟩, qb, fun used => v (.inr used)⟩

private theorem name_exact_iff {value : Pattern} {payload : Process} (depth : Nat) {level : Nat} :
    ∀ n : Name, binderSafeAt "NQuote" level (encodeName n) = true →
      (substituteResolved rhoReflectivePresentation (passing value) depth
          (resolveQuotes rhoReflectivePresentation (encodeName n)) =
        encodeName (bindName payload depth n) ↔
      QuotesResolved rhoReflectivePresentation (encodeName n) ∧
        (mentions depth (encodeName n) = true → value = encodeProcess payload))
  | .bound index, _ => by
      by_cases hit : index = depth
      · subst hit
        simp [passing, encodeName, resolveQuotes, substituteResolved, bindName, binderIndex,
          mentions, QuotesResolved]
      · simp [passing, encodeName, resolveQuotes, substituteResolved, bindName, binderIndex,
          mentions, QuotesResolved, hit]
  | .quote code, safe => by
      have closed := quote_closed safe
      rw [substituteResolved_closed depth closed, bindName,
        if_neg (by rw [binderIndex_of_closed closed]; simp), resolveQuotes_eq_self_iff,
        mentions_false_of_scoped (isWellScopedAt_mono closed (Nat.zero_le depth))]
      simp

private theorem substituteResolved_encode_eq_iff {value : Pattern} {payload : Process} :
    ∀ (body : Process) (depth level : Nat),
      binderSafeAt "NQuote" level (encodeProcess body) = true →
      (substituteResolved rhoReflectivePresentation (passing value) depth
          (resolveQuotes rhoReflectivePresentation (encodeProcess body)) =
        encodeProcess (substitute payload depth body) ↔
      QuotesResolved rhoReflectivePresentation (encodeProcess body) ∧
        (mentions depth (encodeProcess body) = true → value = encodeProcess payload))
  | .zero, depth, _, _ => by
      simp [encodeProcess, resolveQuotes, resolveQuotesList, finishResolveApply,
        substituteResolved, substitute, QuotesResolved, QuotesResolvedList, mentions, mentionsList]
  | .par a b, depth, level, safe => by
      simp only [encodeProcess, binderSafeAt, binderSafeListAt, Bool.and_true,
        Bool.and_eq_true] at safe
      have first := substituteResolved_encode_eq_iff (value := value) (payload := payload) a depth
        level safe.1
      have second := substituteResolved_encode_eq_iff (value := value) (payload := payload) b depth
        level safe.2
      simp only [encodeProcess, resolveQuotes, resolveQuotesList, substituteResolved,
        substituteResolvedList, substitute, Pattern.collection.injEq, List.cons.injEq, and_true,
        true_and, QuotesResolved, QuotesResolvedList, mentions, mentionsList, Bool.or_false,
        Bool.or_eq_true]
      exact split_iff first second
  | .send n q, depth, level, safe => by
      simp only [encodeProcess, binderSafeAt, binderSafeListAt, Bool.and_true,
        Bool.and_eq_true] at safe
      have first := name_exact_iff (value := value) (payload := payload) depth n safe.1
      have second := substituteResolved_encode_eq_iff (value := value) (payload := payload) q depth
        level safe.2
      simp only [encodeProcess, resolveQuotes, resolveQuotesList, finishResolveApply,
        substituteResolved, substituteResolvedList, substitute, Pattern.apply.injEq,
        List.cons.injEq, and_true, true_and, quotesResolved_pair, mentions, mentionsList,
        Bool.or_false, Bool.or_eq_true]
      exact split_iff first second
  | .receive n q, depth, level, safe => by
      simp only [encodeProcess, binderSafeAt, binderSafeListAt, Bool.and_true,
        Bool.and_eq_true] at safe
      have first := name_exact_iff (value := value) (payload := payload) depth n safe.1
      have second := substituteResolved_encode_eq_iff (value := value) (payload := payload) q
        (depth + 1) (level + 1) safe.2
      simp only [encodeProcess, resolveQuotes, resolveQuotesList, finishResolveApply,
        substituteResolved, substituteResolvedList, substitute, Pattern.apply.injEq,
        Pattern.lambda.injEq, List.cons.injEq, and_true, true_and, quotesResolved_pair,
        quotesResolved_lambda, mentions, mentionsList, Bool.or_false, Bool.or_eq_true]
      exact split_iff first second
  | .drop n, depth, level, safe => by
      cases n with
      | bound index =>
          by_cases hit : index = depth
          · subst hit
            simp [passing, encodeProcess, encodeName, resolveQuotes, resolveQuotesList,
              finishResolveApply, substituteResolved, substitute, binderIndex, receive,
              QuotesResolved, QuotesResolvedList, mentions, mentionsList, rhoReflectivePresentation]
          · simp [passing, encodeProcess, encodeName, resolveQuotes, resolveQuotesList,
              finishResolveApply, substituteResolved, substitute, binderIndex, QuotesResolved,
              QuotesResolvedList, mentions, mentionsList, rhoReflectivePresentation, hit]
      | quote code =>
          have closed := quote_closed (level := level) (by
            simpa [encodeProcess, binderSafeAt, binderSafeListAt] using safe)
          have kept : substitute payload depth (.drop (.quote code)) = .drop (.quote code) := by
            simp [substitute, binderIndex_of_closed closed]
          rw [kept, show encodeProcess (.drop (.quote code)) =
            .apply "PDrop" [encodeName (.quote code)] from rfl, dropPattern_closed depth closed]
          have absent := mentions_false_of_scoped
            (isWellScopedAt_mono closed (Nat.zero_le depth))
          simp only [Pattern.apply.injEq, List.cons.injEq, and_true, true_and, quotesResolved_drop,
            mentions, mentionsList, absent, Bool.or_false, Bool.false_eq_true, false_implies]
          exact resolveQuotes_eq_self_iff _

/-- **Exactness, exactly where it holds.** For a body whose quotations are
closed, the compiled COMM substitution passing `@value` is the paper's
substitution of `payload`, spelling for spelling, if and only if the quotations
of the body are resolved and, when the body uses the binder, `value` is the
encoding of `payload`. -/
theorem substituteReflective_encode_eq_iff {value : Pattern} {payload body : Process}
    {depth level : Nat} (closedQuotes : binderSafeAt "NQuote" level (encodeProcess body) = true) :
    substituteReflective rhoReflectivePresentation depth (.apply "NQuote" [value])
        (encodeProcess body) =
      encodeProcess (substitute payload depth body) ↔
    QuotesResolved rhoReflectivePresentation (encodeProcess body) ∧
      (mentions depth (encodeProcess body) = true → value = encodeProcess payload) :=
  substituteResolved_encode_eq_iff body depth level closedQuotes

/-! ## The paper's reading -/

/-- On the paper's reading of the body of `x(y).P`, `instantiate` with a closed
replacement is the compiled COMM substitution. -/
theorem instantiate_literalBody (y : NName) (body : NProc) {replacement : Pattern}
    (closed : replacement.isWellScopedAt 0 = true) :
    instantiate rhoReflectivePresentation 0 replacement (encodeProcess (literalBody y body)) =
      substituteReflective rhoReflectivePresentation 0 replacement
        (encodeProcess (literalBody y body)) :=
  closed_agreement rhoReflectivePresentation
    (readProcess_scoped false [some ⟨closedName y, false⟩] body) closed

/-- The name a COMM step passes for the paper's reading of a payload is closed. -/
theorem commName_closed (payload : NProc) :
    (Pattern.apply "NQuote" [normalizeReflective rhoReflectivePresentation
      (encodeProcess (literal payload))]).isWellScopedAt 0 = true := by
  have normalized : (normalizeReflective rhoReflectivePresentation
      (encodeProcess (literal payload))).isWellScopedAt 0 = true :=
    normalizeReflective_scoped rhoReflectivePresentation (readProcess_scoped false [] payload)
  simpa [Pattern.isWellScopedAt, Pattern.isWellScopedListAt] using normalized

/-- On the paper's reading, the quotations of the body of `x(y).P` are closed. -/
theorem literalBody_binderSafe (y : NName) (body : NProc) :
    binderSafeAt "NQuote" 1 (encodeProcess (literalBody y body)) = true :=
  readProcess_binderSafe [some ⟨closedName y, false⟩] body
    (confined_cons (confined_hidden 0) (closedName y))

/-- **Exactness on the paper's reading, exactly where it holds.** Eliminating
the binder `y` of `x(y).P` with `instantiate`, passing the payload as the COMM
step does, gives the paper's substitution `P{@Q/y}` spelling for spelling if and
only if the body's quotations are resolved and, when the body uses `y`, the
payload is in quote-drop normal form. -/
theorem instantiate_literal_exact_iff (y : NName) (body payload : NProc) :
    instantiate rhoReflectivePresentation 0
        (.apply "NQuote" [normalizeReflective rhoReflectivePresentation
          (encodeProcess (literal payload))])
        (encodeProcess (literalBody y body)) =
      encodeProcess (substitute (literal payload) 0 (literalBody y body)) ↔
    QuotesResolved rhoReflectivePresentation (encodeProcess (literalBody y body)) ∧
      (mentions 0 (encodeProcess (literalBody y body)) = true →
        normalizeReflective rhoReflectivePresentation (encodeProcess (literal payload)) =
          encodeProcess (literal payload)) := by
  rw [instantiate_literalBody y body (commName_closed payload)]
  exact substituteReflective_encode_eq_iff (literalBody_binderSafe y body)

/-- **Exactness on the resolved fiber.** When both readings are resolved, the
compiled substitution is the paper's substitution, spelling for spelling. -/
theorem instantiate_literal_exact (y : NName) (body payload : NProc)
    (bodyResolved : QuotesResolved rhoReflectivePresentation (encodeProcess (literalBody y body)))
    (payloadResolved : QuotesResolved rhoReflectivePresentation (encodeProcess (literal payload))) :
    instantiate rhoReflectivePresentation 0
        (.apply "NQuote" [normalizeReflective rhoReflectivePresentation
          (encodeProcess (literal payload))])
        (encodeProcess (literalBody y body)) =
      encodeProcess (substitute (literal payload) 0 (literalBody y body)) :=
  (instantiate_literal_exact_iff y body payload).mpr
    ⟨bodyResolved, fun _ => normalizeReflective_of_resolved payloadResolved⟩

/-- **Up to the equations, everywhere.** -/
theorem canonicalize_instantiate_literal (y : NName) (body payload : NProc) :
    canonicalize rhoReflectivePresentation
        (instantiate rhoReflectivePresentation 0
          (.apply "NQuote" [normalizeReflective rhoReflectivePresentation
            (encodeProcess (literal payload))])
          (encodeProcess (literalBody y body))) =
      canonicalForm (substitute (literal payload) 0 (literalBody y body)) := by
  rw [instantiate_literalBody y body (commName_closed payload)]
  exact canonicalize_substituteReflective_encode _ _ 0

/-! ## Steps on the paper's reading -/

mutual
  /-- The paper's reading is scoped by its binders, with closed quotations. -/
  theorem readName_literal_scoped :
      ∀ (scope : List (Option Binder)) (n : NName), Confined scope →
        ScopedName scope.length (readName false scope n)
    | scope, .quote code, confined => by
        simp only [readName]
        split
        · rename_i index found
          exact .bound (lookup_lt found)
        · rw [enterQuote_confined confined, readProcess_hidden]
          exact .literal (readProcess_literal_scoped [] code (confined_hidden 0))

  theorem readProcess_literal_scoped :
      ∀ (scope : List (Option Binder)) (p : NProc), Confined scope →
        ScopedProcess scope.length (readProcess false scope p)
    | _, .zero, _ => .zero
    | scope, .par left right, confined =>
        .par (readProcess_literal_scoped scope left confined)
          (readProcess_literal_scoped scope right confined)
    | scope, .send subject payload, confined =>
        .send (readName_literal_scoped scope subject confined)
          (readProcess_literal_scoped scope payload confined)
    | scope, .receive subject binder body, confined =>
        .receive (readName_literal_scoped scope subject confined)
          (readProcess_literal_scoped _ body (confined_cons confined (readName false [] binder)))
    | scope, .drop name, confined => .drop (readName_literal_scoped scope name confined)
end

/-- The paper's reading of a named process is closed: its names are global. -/
theorem literal_closed (p : NProc) : ScopedProcess 0 (literal p) :=
  readProcess_literal_scoped [] p (confined_hidden 0)

/-- **End to end, one step.** The paper's reductions of the reading of a named
process are the steps of our calculus from the canonical form of its encoding. -/
theorem literal_reduction_iff_rhoStep (p : NProc) (q : Process) :
    Reduction (literal p) q ↔
      ∃ r, RhoStep (canonicalForm (literal p)) r ∧
        canonicalize rhoReflectivePresentation r = canonicalForm q :=
  reduction_iff_rhoStep (literal_closed p)

/-- **End to end, many steps.** -/
theorem literal_transGen_iff (p : NProc) (q : Process) :
    Relation.TransGen Reduction (literal p) q ↔
      Relation.TransGen CanonicalStep (canonicalForm (literal p)) (canonicalForm q) :=
  transGen_reduction_iff_canonicalStep (literal_closed p)

/-- **The COMM step, exactly.** On the fiber of `instantiate_literal_exact_iff`,
our calculus steps from the plain encoding of the reading of the named redex
`x'(y).P | x!(Q)` to the encoding of the paper's contractum `P{@Q/y}`. -/
theorem literal_comm_steps_exactly {x x' y : NName} {body payload : NProc}
    (channels : NameEquivalence (closedName x) (closedName x'))
    (bodyResolved : QuotesResolved rhoReflectivePresentation (encodeProcess (literalBody y body)))
    (payloadNormal : mentions 0 (encodeProcess (literalBody y body)) = true →
      normalizeReflective rhoReflectivePresentation (encodeProcess (literal payload)) =
        encodeProcess (literal payload)) :
    RhoStep (encodeProcess (literal (.par (.receive x' y body) (.send x payload))))
      (.collection .hashBag [encodeProcess (substitute (literal payload) 0 (literalBody y body))]
        none) := by
  have exact := (instantiate_literalBody y body
    (commName_closed payload)).symm.trans
      ((instantiate_literal_exact_iff y body payload).mpr ⟨bodyResolved, payloadNormal⟩)
  have step : RhoStep _ _ := ⟨1, rhoStepAt_comm_at
    (elements := [encodeProcess (.receive (closedName x') (literalBody y body)),
      encodeProcess (.send (closedName x) (literal payload))]) (termRest := none)
    (inputIndex := 0) (outputIndex := 0) (by simp) (by simp) rfl rfl
    ((canonicalize_encodeName_eq_iff _ _).mpr channels.symm)⟩
  rw [exact] at step
  exact step

/-! ## Controls -/

namespace Controls

open Mettapedia.GSLT.Contracts.PaperRho.Named.Controls

private theorem zero_resolved :
    QuotesResolved rhoReflectivePresentation (encodeProcess (literal .zero)) := by
  simp [literal, readProcess, QuotesResolved, QuotesResolvedList, encodeProcess]

private theorem dynamicQuote_resolved :
    QuotesResolved rhoReflectivePresentation (encodeProcess (literalBody zName dynamicQuote)) := by
  rw [literalBody_dynamicQuote]
  simp [QuotesResolved, QuotesResolvedList, encodeProcess, encodeName, exposedDrop?,
    parallelLeaves, rhoReflectivePresentation]

/-- **Positive control: the example of §2.6 through the exact theorem.** The
quotation in `w[@(y[z])]` is impervious to substitution in our calculus too,
spelling for spelling. -/
theorem dynamicQuote_exact :
    instantiate rhoReflectivePresentation 0
        (.apply "NQuote" [normalizeReflective rhoReflectivePresentation
          (encodeProcess (literal .zero))])
        (encodeProcess (literalBody zName dynamicQuote)) =
      encodeProcess (literalBody zName dynamicQuote) :=
  (instantiate_literal_exact zName dynamicQuote .zero dynamicQuote_resolved zero_resolved).trans
    (congrArg encodeProcess dynamicQuote_paper)

/-- **Positive control: the §2.6 redex steps exactly.** `@0(z).w[@(y[z])] | @0!(0)`
steps in our calculus from its plain encoding to `w[@(y[z])]`. -/
theorem dynamicQuote_comm_exact :
    RhoStep (encodeProcess (literal (.par (.receive zeroName zName dynamicQuote)
        (.send zeroName .zero))))
      (.collection .hashBag [encodeProcess (literalBody zName dynamicQuote)] none) := by
  have step := literal_comm_steps_exactly (x := zeroName) (x' := zeroName) (y := zName)
    (body := dynamicQuote) (payload := .zero) (.refl _) dynamicQuote_resolved
    (fun _ => normalizeReflective_of_resolved zero_resolved)
  rwa [show substitute (literal .zero) 0 (literalBody zName dynamicQuote) =
    literalBody zName dynamicQuote from dynamicQuote_paper] at step

/-- **Negative control: the reading matters.** On the binding-aware reading of
the §2.6 body the quotation is not closed: it keeps the binder's index.
`instantiate` keeps the quotation opaque, so that index dangles, and the result
differs from the paper's even up to the equations. -/
theorem dynamicQuote_bindingAware_not_exact :
    binderSafeAt "NQuote" 1 (encodeProcess (bindingAwareBody zName dynamicQuote)) = false ∧
      instantiate rhoReflectivePresentation 0
          (.apply "NQuote" [normalizeReflective rhoReflectivePresentation
            (encodeProcess (literal .zero))])
          (encodeProcess (bindingAwareBody zName dynamicQuote)) ≠
        encodeProcess (substitute (literal .zero) 0 (literalBody zName dynamicQuote)) ∧
      canonicalize rhoReflectivePresentation
          (instantiate rhoReflectivePresentation 0
            (.apply "NQuote" [normalizeReflective rhoReflectivePresentation
              (encodeProcess (literal .zero))])
            (encodeProcess (bindingAwareBody zName dynamicQuote))) ≠
        canonicalForm (substitute (literal .zero) 0 (literalBody zName dynamicQuote)) := by
  rw [bindingAwareBody_dynamicQuote, literalBody_dynamicQuote,
    show literal .zero = .zero from rfl]
  have canonical :
      canonicalize rhoReflectivePresentation
          (instantiate rhoReflectivePresentation 0
            (.apply "NQuote" [normalizeReflective rhoReflectivePresentation (encodeProcess .zero)])
            (encodeProcess (.send (.quote .zero)
              (.drop (.quote (.send (.quote .zero) (.drop (.bound 0)))))))) ≠
        canonicalForm (substitute .zero 0
          (.send (.quote .zero) (.drop (.quote (.send (.quote .zero) (.drop zClosed)))))) := by
    decide +kernel
  exact ⟨by decide +kernel, fun same => canonical (by rw [same]), canonical⟩

/-! ### The minimal witness off the fiber -/

private theorem quotedDropKey_not_z :
    ¬ NameEquivalence (.quote (.drop (.quote .zero))) zClosed := fun same =>
  absurd ((canonicalize_encodeName_eq_iff _ _).mpr same) (by decide)

/-- `*@(*@0)`: a drop of a quotation that exposes a drop. -/
def quotedDrop : NProc := .drop (.quote (.drop zeroName))

/-- `*z`: the body runs the received payload. -/
def runsBinder : NProc := .drop zName

theorem literalBody_quotedDrop :
    literalBody zName quotedDrop = .drop (.quote (.drop (.quote .zero))) := by
  simp [literalBody, quotedDrop, readProcess, readName, lookup, enterQuote, closedName, zeroName,
    zName, quotedDropKey_not_z]

theorem literal_quotedDrop : literal quotedDrop = .drop (.quote (.drop (.quote .zero))) := by
  simp [literal, quotedDrop, readProcess, readName, lookup, enterQuote, zeroName]

theorem literalBody_runsBinder : literalBody zName runsBinder = .drop (.bound 0) := by
  simp [literalBody, runsBinder, readProcess, readName, lookup, enterQuote, closedName, zeroName,
    zName, NameEquivalence.refl]

/-- **Witness: an unresolved body.** The paper's reading of `*@(*@0)` under the
binder `z` keeps the spelling `@(*@0)`, which our substitution resolves to `@0`.
The two results differ as written and agree up to the equations. The
responsible law is quote-drop, `@(*x) ≡N x`. The body is as small as a body
off the fiber can be: with a normal payload, exactness fails only at a quotation
exposing a drop (`instantiate_literal_exact_iff`), the smallest such quotation
is `@(*@0)`, and a drop is the smallest process holding a name. -/
theorem quotedDrop_not_exact :
    instantiate rhoReflectivePresentation 0
        (.apply "NQuote" [normalizeReflective rhoReflectivePresentation
          (encodeProcess (literal .zero))])
        (encodeProcess (literalBody zName quotedDrop)) ≠
      encodeProcess (substitute (literal .zero) 0 (literalBody zName quotedDrop)) ∧
    canonicalize rhoReflectivePresentation
        (instantiate rhoReflectivePresentation 0
          (.apply "NQuote" [normalizeReflective rhoReflectivePresentation
            (encodeProcess (literal .zero))])
          (encodeProcess (literalBody zName quotedDrop))) =
      canonicalForm (substitute (literal .zero) 0 (literalBody zName quotedDrop)) := by
  refine ⟨?_, canonicalize_instantiate_literal zName quotedDrop .zero⟩
  rw [literalBody_quotedDrop, show literal .zero = .zero from rfl]
  decide +kernel

/-- The witness is off the fiber, as it must be. -/
theorem quotedDrop_not_resolved :
    ¬ QuotesResolved rhoReflectivePresentation (encodeProcess (literalBody zName quotedDrop)) :=
  fun resolved =>
    quotedDrop_not_exact.1 (instantiate_literal_exact zName quotedDrop .zero resolved zero_resolved)

/-- **Witness: an unnormalized payload.** Communicating `*@(*@0)` to `*z`, the
COMM step passes the payload in quote-drop normal form and the drop of `z` runs
`*@0`, while the paper's substitution runs the payload as written. The
responsible law is again quote-drop. -/
theorem quotedDropPayload_not_exact :
    instantiate rhoReflectivePresentation 0
        (.apply "NQuote" [normalizeReflective rhoReflectivePresentation
          (encodeProcess (literal quotedDrop))])
        (encodeProcess (literalBody zName runsBinder)) ≠
      encodeProcess (substitute (literal quotedDrop) 0 (literalBody zName runsBinder)) ∧
    canonicalize rhoReflectivePresentation
        (instantiate rhoReflectivePresentation 0
          (.apply "NQuote" [normalizeReflective rhoReflectivePresentation
            (encodeProcess (literal quotedDrop))])
          (encodeProcess (literalBody zName runsBinder))) =
      canonicalForm (substitute (literal quotedDrop) 0 (literalBody zName runsBinder)) := by
  refine ⟨?_, canonicalize_instantiate_literal zName runsBinder quotedDrop⟩
  rw [literalBody_runsBinder, literal_quotedDrop]
  decide +kernel

end Controls

#print axioms substituteReflective_encode_eq_iff
#print axioms instantiate_literalBody
#print axioms instantiate_literal_exact_iff
#print axioms instantiate_literal_exact
#print axioms canonicalize_instantiate_literal
#print axioms literal_closed
#print axioms literal_reduction_iff_rhoStep
#print axioms literal_transGen_iff
#print axioms literal_comm_steps_exactly
#print axioms Controls.dynamicQuote_exact
#print axioms Controls.dynamicQuote_comm_exact
#print axioms Controls.dynamicQuote_bindingAware_not_exact
#print axioms Controls.quotedDrop_not_exact
#print axioms Controls.quotedDrop_not_resolved
#print axioms Controls.quotedDropPayload_not_exact

end Mettapedia.GSLT.Contracts.PaperRho.LiteralAdequacy
