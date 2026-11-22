import Mettapedia.OSLF.MeTTaIL.ReflectiveInstantiation
import Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax

/-!
# Admission of quotations under a closed quote scope

A substitution policy whose binders do not reach into quotations (quote scope
`closed`) admits only quotations whose code is closed with respect to object
binders, as under the `box` of contextual modal type theory (Nanevski, Pfenning
and Pientka, 2008), whose body is typed in the empty object context. A quotation
whose payload exposes a drop denotes that name, by the quote-drop equation, and
is not code.

Admission is a judgment about substitution, separate from sorting
(`DerivedPresentationSyntax`). The reflective higher-order calculus of Meredith
and Radestock (2005) forms a name from any process and lets substitution pass a
quotation by; its grammar has no admission premise. `QuotesClosed` is therefore
a hypothesis of the theorems about substitution that need it.

* The equations never move an index (`mentions_canonicalize`) and never change
  the scope of a term (`isWellScopedAt_canonicalize`); on a resolved term,
  closed code is read modulo the equations (`closedCode_canonicalize`).
* **Invariance under the declared equations**: `quotesClosed_respects`.
* **Substitution of admitted names**: eliminating a binder by an admitted closed
  name in an admitted body gives an admitted term (`quotesClosed_instantiate`,
  `quotesClosed_substituteReflective`).
* **Sorting does not read the quote scope** (`nameWellSorted_withQuoteScope_iff`,
  `procWellSorted_withQuoteScope_iff`); admission does
  (`quoteAdmits_reads_quoteScope`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.ReflectiveQuoteAdmission

open Syntax Reflection Substitution ScopedPattern ReflectiveSubstitution ReflectiveCanonical
open ReflectiveCoherent ReflectiveInstantiation

/-! ## Mentions of a bound index -/

mutual
  /-- Whether a term refers to the bound index `level` (shifted under binders). -/
  def mentions : Nat → Pattern → Bool
    | level, .bvar index => index == level
    | _, .fvar _ => false
    | level, .apply _ arguments => mentionsList level arguments
    | level, .lambda _ body => mentions (level + 1) body
    | level, .multiLambda arity _ body => mentions (level + arity) body
    | level, .subst body value => mentions (level + 1) body || mentions level value
    | level, .collection _ elements _ => mentionsList level elements

  /-- List recursion for `mentions`. -/
  def mentionsList : Nat → List Pattern → Bool
    | _, [] => false
    | level, pattern :: patterns => mentions level pattern || mentionsList level patterns
end

theorem mentionsList_eq_false_iff (level : Nat) (patterns : List Pattern) :
    mentionsList level patterns = false ↔ ∀ pattern ∈ patterns, mentions level pattern = false := by
  induction patterns with
  | nil => simp [mentionsList]
  | cons pattern patterns ih => simp [mentionsList, ih]

section Mentions

variable {declaration : ReflectivePresentationDecl}

private theorem all_congr_of_mem {α : Type} {patterns : List α} {first second : α → Bool}
    (same : ∀ pattern ∈ patterns, first pattern = second pattern) :
    patterns.all first = patterns.all second := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns ih =>
      simp only [List.all_cons, same pattern (by simp), ih fun other member => same other (by simp [member])]

theorem mentionsList_eq_any (level : Nat) (patterns : List Pattern) :
    mentionsList level patterns = patterns.any (mentions level) := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns ih => simp [mentionsList, ih]

/-- A test that holds of the declared parallel unit, and of a parallel
composition exactly when it holds of each element, does not see bag
normalization: flattening, unit removal, sorting and collapsing. -/
theorem collapse_normalize_all (test : Pattern → Bool)
    (unit : test (.apply declaration.parallelUnitConstructor []) = true)
    (parallel : ∀ elements, test (.collection declaration.parallelCollection elements none) =
      elements.all test)
    (patterns : List Pattern) :
    test (collapseParallel declaration (normalizeParallelElements declaration patterns)) =
      patterns.all test := by
  have collapse : ∀ members : List Pattern,
      test (collapseParallel declaration members) = members.all test
    | [] => by simp [collapseParallel, unit]
    | [_] => by simp [collapseParallel]
    | _ :: _ :: _ => parallel _
  have splice : ∀ pattern, (parallelSplice declaration pattern).all test = test pattern := by
    intro pattern
    cases pattern with
    | collection kind elements rest =>
        cases rest with
        | none =>
            by_cases isParallel : kind = declaration.parallelCollection
            · subst isParallel; simp [parallelSplice, parallel]
            · simp [parallelSplice, isParallel]
        | some _ => simp [parallelSplice]
    | _ => simp [parallelSplice]
  rw [collapse, normalizeParallelElements_eq_sort_parallelContents, (sortPatterns_perm _).all_eq]
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true, parallelContents, List.mem_filter, List.mem_flatMap,
    decide_eq_true_eq]
  constructor
  · intro contents pattern member
    rw [← splice pattern, List.all_eq_true]
    intro element elementMember
    by_cases isUnit : element = .apply declaration.parallelUnitConstructor []
    · rw [isUnit]; exact unit
    · exact contents element ⟨⟨pattern, member, elementMember⟩, isUnit⟩
  · rintro each element ⟨⟨pattern, member, elementMember⟩, _⟩
    exact List.all_eq_true.mp ((splice pattern).trans (each pattern member)) element elementMember

theorem mentions_finishNormalizeReflectiveApply (level : Nat) (constructor : String)
    (arguments : List Pattern) :
    mentions level (finishNormalizeReflectiveApply declaration constructor arguments) =
      mentionsList level arguments := by
  unfold finishNormalizeReflectiveApply
  split
  · split
    · split
      · simp [mentions, mentionsList]
      · rfl
    · rfl
  · rfl

/-- **The equations never move an index.** -/
theorem mentions_canonicalize (pattern : Pattern) :
    ∀ level, mentions level (canonicalize declaration pattern) = mentions level pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro _; rfl
  | hfvar name => intro _; rfl
  | hlambda binder body ih => intro level; exact ih (level + 1)
  | hmultiLambda arity binders body ih => intro level; exact ih (level + arity)
  | hsubst body value ihBody ihValue =>
      intro level
      simp only [canonicalize, mentions, ihBody, ihValue]
  | happly constructor arguments ih =>
      intro level
      have mapped : (arguments.map (canonicalize declaration)).all (fun p => !mentions level p) =
          arguments.all (fun p => !mentions level p) := by
        rw [List.all_map]
        exact all_congr_of_mem fun pattern member => by simp [ih pattern member level]
      simp only [canonicalize, mentions_finishNormalizeReflectiveApply, canonicalizeList_eq_map,
        mentions, mentionsList_eq_any]
      apply Bool.not_inj
      simpa only [List.not_any_eq_all_not] using mapped
  | hcollection kind elements rest ih =>
      intro level
      have mapped : (elements.map (canonicalize declaration)).all (fun p => !mentions level p) =
          elements.all (fun p => !mentions level p) := by
        rw [List.all_map]
        exact all_congr_of_mem fun pattern member => by simp [ih pattern member level]
      have any : (elements.map (canonicalize declaration)).any (mentions level) =
          elements.any (mentions level) := by
        apply Bool.not_inj
        simpa only [List.not_any_eq_all_not] using mapped
      cases rest with
      | some rest =>
          simp only [canonicalize, canonicalizeList_eq_map, mentions, mentionsList_eq_any, any]
      | none =>
          by_cases isParallel : kind = declaration.parallelCollection
          · subst isParallel
            rw [canonicalize_parallel_eq]
            have collapsed := collapse_normalize_all (declaration := declaration)
              (fun p => !mentions level p) rfl
              (fun elements => by simp [mentions, mentionsList_eq_any, List.not_any_eq_all_not])
              (elements.map (canonicalize declaration))
            apply Bool.not_inj
            rw [collapsed, mapped]
            simp [mentions, mentionsList_eq_any, List.not_any_eq_all_not]
          · have notParallel : (kind == declaration.parallelCollection) = false := by
              simpa using isParallel
            simp only [canonicalize, notParallel, Bool.false_eq_true, if_false,
              canonicalizeList_eq_map, mentions, mentionsList_eq_any, any]

theorem mentions_resolveQuotes (level : Nat) (pattern : Pattern) :
    mentions level (resolveQuotes declaration pattern) = mentions level pattern := by
  rw [← mentions_canonicalize, canonicalize_resolveQuotes, mentions_canonicalize]

theorem mentions_respects (level : Nat) {left right : Pattern}
    (same : canonicalEquivalent declaration left right = true) :
    mentions level left = mentions level right := by
  rw [← mentions_canonicalize, canonicalEquivalent_eq_true_iff.mp same, mentions_canonicalize]

end Mentions

/-! ## Closed quotations

Under a closed scope no genuine quotation mentions an object binder bound
outside it, at any depth: quoted code is closed, as contextual modal type theory
types the body of `box` in the empty object context. `QuotesClosed` states this
on the resolved term; it generalizes `Sealed` from the eliminated binder to
every binder (`ReflectiveContextualQuote.sealed_of_quotesClosed`). A sorted
term need not satisfy it (`sorted_not_admitted`).

The condition respects the declared equations (`quotesClosed_respects`), and
eliminating a binder by an admitted closed name in an admitted body gives an
admitted term (`quotesClosed_instantiate`, `quotesClosed_substituteReflective`). -/

section Admission

variable {declaration : ReflectivePresentationDecl}

private theorem scopedListAt_eq_all (depth : Nat) (patterns : List Pattern) :
    Pattern.isWellScopedListAt depth patterns = patterns.all (Pattern.isWellScopedAt depth) := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns ih => simp [Pattern.isWellScopedListAt, ih]

theorem closedCodeList_eq_all (patterns : List Pattern) :
    closedCodeList declaration patterns = patterns.all (closedCode declaration) := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns ih => simp [closedCodeList, ih]

/-- A term is scoped at `depth` exactly when it mentions no index at or above it. -/
theorem isWellScopedAt_iff_not_mentions (pattern : Pattern) :
    ∀ depth, pattern.isWellScopedAt depth = true ↔ ∀ level, depth ≤ level → mentions level pattern = false := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      intro depth
      simp only [Pattern.isWellScopedAt, decide_eq_true_eq, mentions, beq_eq_false_iff_ne]
      constructor
      · intro below level above same
        omega
      · intro never
        by_contra notBelow
        exact never index (by omega) rfl
  | hfvar name => intro depth; simp [Pattern.isWellScopedAt, mentions]
  | happly constructor arguments ih =>
      intro depth
      simp only [Pattern.isWellScopedAt, mentions, scopedListAt_eq_all, mentionsList_eq_any]
      rw [List.all_eq_true]
      constructor
      · intro inScope level above
        rw [List.any_eq_false]
        intro argument member
        simp [((ih argument member depth).mp (inScope argument member)) level above]
      · intro never argument member
        apply (ih argument member depth).mpr
        intro level above
        have none := never level above
        rw [List.any_eq_false] at none
        simpa using none argument member
  | hlambda binder body ih =>
      intro depth
      simp only [Pattern.isWellScopedAt, mentions]
      rw [ih (depth + 1)]
      constructor
      · intro never level above
        exact never (level + 1) (by omega)
      · intro never level above
        have shifted := never (level - 1) (by omega)
        rwa [show level - 1 + 1 = level by omega] at shifted
  | hmultiLambda arity binders body ih =>
      intro depth
      simp only [Pattern.isWellScopedAt, mentions]
      rw [ih (depth + arity)]
      constructor
      · intro never level above
        exact never (level + arity) (by omega)
      · intro never level above
        have shifted := never (level - arity) (by omega)
        rwa [show level - arity + arity = level by omega] at shifted
  | hsubst body value ihBody ihValue =>
      intro depth
      simp only [Pattern.isWellScopedAt, mentions, Bool.and_eq_true, Bool.or_eq_false_iff]
      rw [ihBody (depth + 1), ihValue depth]
      constructor
      · rintro ⟨bodyNever, valueNever⟩ level above
        exact ⟨bodyNever (level + 1) (by omega), valueNever level above⟩
      · intro never
        refine ⟨fun level above => ?_, fun level above => (never level above).2⟩
        have shifted := (never (level - 1) (by omega)).1
        rwa [show level - 1 + 1 = level by omega] at shifted
  | hcollection kind elements rest ih =>
      intro depth
      simp only [Pattern.isWellScopedAt, mentions, scopedListAt_eq_all, mentionsList_eq_any]
      rw [List.all_eq_true]
      constructor
      · intro inScope level above
        rw [List.any_eq_false]
        intro element member
        simp [((ih element member depth).mp (inScope element member)) level above]
      · intro never element member
        apply (ih element member depth).mpr
        intro level above
        have none := never level above
        rw [List.any_eq_false] at none
        simpa using none element member

/-- The declared equations never change the scope of a term. -/
theorem isWellScopedAt_canonicalize (pattern : Pattern) (depth : Nat) :
    (canonicalize declaration pattern).isWellScopedAt depth = pattern.isWellScopedAt depth := by
  apply Bool.eq_iff_iff.mpr
  rw [isWellScopedAt_iff_not_mentions, isWellScopedAt_iff_not_mentions]
  simp only [mentions_canonicalize]

/-- On a resolved term, closed code is read modulo the declared equations. -/
theorem closedCode_canonicalize {pattern : Pattern} (resolved : QuotesResolved declaration pattern) :
    closedCode declaration (canonicalize declaration pattern) = closedCode declaration pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => rfl
  | hfvar name => rfl
  | hlambda binder body ih => simp only [canonicalize, closedCode, ih resolved]
  | hmultiLambda arity binders body ih => simp only [canonicalize, closedCode, ih resolved]
  | hsubst body value ihBody ihValue =>
      simp only [canonicalize, closedCode, ihBody resolved.1, ihValue resolved.2]
  | happly constructor arguments ih =>
      match arguments, resolved, ih with
      | [], _, _ => simp [canonicalize, canonicalizeList, finish_nil, closedCode]
      | [payload], resolved, ih =>
          rw [canonicalize_unary_of_resolved resolved]
          by_cases isQuote : constructor = declaration.quoteConstructor
          · simp only [closedCode, isQuote, if_true, isWellScopedAt_canonicalize,
              ih payload (by simp) resolved.1.1]
          · simp only [closedCode, isQuote, if_false, ih payload (by simp) resolved.1.1]
      | first :: second :: rest, resolved, ih =>
          have each := (quotesResolvedList_iff _).mp resolved.1
          have mapped : ((first :: second :: rest).map (canonicalize declaration)).all
                (closedCode declaration) = (first :: second :: rest).all (closedCode declaration) := by
            rw [List.all_map]
            exact all_congr_of_mem fun pattern member => ih pattern member (each pattern member)
          simp only [List.map_cons] at mapped
          simp only [canonicalize, canonicalizeList_eq_map, List.map_cons, finish_long, closedCode,
            closedCodeList_eq_all, mapped]
  | hcollection kind elements rest ih =>
      have each := (quotesResolvedList_iff elements).mp resolved
      have mapped : (elements.map (canonicalize declaration)).all (closedCode declaration) =
          elements.all (closedCode declaration) := by
        rw [List.all_map]
        exact all_congr_of_mem fun pattern member => ih pattern member (each pattern member)
      cases rest with
      | some rest =>
          simp only [canonicalize, canonicalizeList_eq_map, closedCode, closedCodeList_eq_all, mapped]
      | none =>
          by_cases isParallel : kind = declaration.parallelCollection
          · subst isParallel
            rw [canonicalize_parallel_eq, collapse_normalize_all (closedCode declaration)
              rfl (fun elements => closedCodeList_eq_all elements), mapped]
            exact (closedCodeList_eq_all elements).symm
          · have notParallel : (kind == declaration.parallelCollection) = false := by
              simpa using isParallel
            simp only [canonicalize, notParallel, Bool.false_eq_true, if_false,
              canonicalizeList_eq_map, closedCode, closedCodeList_eq_all, mapped]

/-- A term is admitted exactly when its canonical form has closed code. -/
theorem quotesClosed_iff_canonicalize {term : Pattern} :
    QuotesClosed declaration term ↔ closedCode declaration (canonicalize declaration term) = true := by
  unfold QuotesClosed
  rw [← closedCode_canonicalize (resolveQuotes_resolved term), canonicalize_resolveQuotes]

/-- **Quote admission respects the declared equations.** -/
theorem quotesClosed_respects {left right : Pattern}
    (same : canonicalEquivalent declaration left right = true) :
    QuotesClosed declaration left ↔ QuotesClosed declaration right := by
  rw [quotesClosed_iff_canonicalize, quotesClosed_iff_canonicalize,
    canonicalEquivalent_eq_true_iff.mp same]

/-- A quotation is equal to the quotation of its canonical payload. -/
theorem canonicalEquivalent_quote_canonicalize (payload : Pattern) :
    canonicalEquivalent declaration (.apply declaration.quoteConstructor [canonicalize declaration payload])
      (.apply declaration.quoteConstructor [payload]) = true := by
  rw [canonicalEquivalent_eq_true_iff]
  simp only [canonicalize, canonicalizeList, canonicalize_idempotent]

/-- **Quotation admission reads the payload modulo the declared equations.** -/
theorem quoteAdmits_canonicalize (payload : Pattern) :
    quoteAdmits declaration (canonicalize declaration payload) = quoteAdmits declaration payload := by
  unfold quoteAdmits
  split
  · exact Bool.eq_iff_iff.mpr (quotesClosed_respects (canonicalEquivalent_quote_canonicalize payload))
  · rfl

/-- Payloads with the same canonical form are admitted alike. -/
theorem quoteAdmits_of_canonicalize_eq {left right : Pattern}
    (same : canonicalize declaration left = canonicalize declaration right) :
    quoteAdmits declaration left = quoteAdmits declaration right := by
  rw [← quoteAdmits_canonicalize left, same, quoteAdmits_canonicalize]

/-- Closed code is the conjunction over the members of a parallel composition. -/
theorem closedCode_eq_parallelLeaves (pattern : Pattern) :
    closedCode declaration pattern = (parallelLeaves declaration pattern).all (closedCode declaration) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp [parallelLeaves, closedCode]
  | hfvar name => simp [parallelLeaves, closedCode]
  | happly constructor arguments _ =>
      cases arguments with
      | nil =>
          by_cases unit : constructor = declaration.parallelUnitConstructor
          · simp [parallelLeaves, unit, closedCode]
          · simp [parallelLeaves, unit]
      | cons first rest => simp [parallelLeaves]
  | hlambda binder body _ => simp [parallelLeaves]
  | hmultiLambda arity binders body _ => simp [parallelLeaves]
  | hsubst body value _ _ => simp [parallelLeaves]
  | hcollection kind elements rest ih =>
      cases rest with
      | some rest => simp [parallelLeaves]
      | none =>
          by_cases isParallel : kind = declaration.parallelCollection
          · simp only [parallelLeaves, isParallel, if_true, parallelLeavesList_eq_flatMap, closedCode,
              closedCodeList_eq_all, List.all_flatMap]
            exact all_congr_of_mem fun element member => ih element member
          · simp [parallelLeaves, isParallel]

/-- The name a parallel composition exposes is closed code when the composition is. -/
theorem closedCode_of_exposedDrop {pattern name : Pattern}
    (exposed : exposedDrop? declaration pattern = some name) :
    closedCode declaration pattern = true → closedCode declaration name = true := by
  intro closed
  rw [closedCode_eq_parallelLeaves] at closed
  unfold exposedDrop? at exposed
  split at exposed
  · rename_i constructor argument leaves
    by_cases dropped : constructor = declaration.dropConstructor
    · simp only [dropped, if_true, Option.some.injEq] at exposed
      subst exposed
      rw [leaves] at closed
      simp only [List.all_cons, List.all_nil, Bool.and_true] at closed
      unfold closedCode at closed
      split at closed <;> simp_all
    · simp [dropped] at exposed
  · cases exposed

/-- **Resolution keeps closed code closed.** -/
theorem closedCode_resolveQuotes {pattern : Pattern} :
    closedCode declaration pattern = true → closedCode declaration (resolveQuotes declaration pattern) = true := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro _; rfl
  | hfvar name => intro _; rfl
  | hlambda binder body ih => intro closed; exact ih closed
  | hmultiLambda arity binders body ih => intro closed; exact ih closed
  | hsubst body value ihBody ihValue =>
      intro closed
      simp only [closedCode, Bool.and_eq_true] at closed
      simp only [resolveQuotes, closedCode, ihBody closed.1, ihValue closed.2, Bool.and_self]
  | hcollection kind elements rest ih =>
      intro closed
      simp only [closedCode, closedCodeList_eq_all, List.all_eq_true] at closed
      simp only [resolveQuotes, resolveQuotesList_eq_map, closedCode, closedCodeList_eq_all, List.all_map,
        List.all_eq_true, Function.comp_apply]
      exact fun element member => ih element member (closed element member)
  | happly constructor arguments ih =>
      intro closed
      simp only [resolveQuotes, resolveQuotesList_eq_map]
      match arguments, closed, ih with
      | [], _, _ => simp [finishResolveApply, closedCode]
      | [payload], closed, ih =>
          have payloadClosed : closedCode declaration payload = true := by
            unfold closedCode at closed
            split at closed <;> simp_all
          have resolvedClosed := ih payload (by simp) payloadClosed
          simp only [List.map_cons, List.map_nil, finishResolveApply]
          by_cases isQuote : constructor = declaration.quoteConstructor
          · have inScope : payload.isWellScopedAt 0 = true := by
              simp only [closedCode, isQuote, if_true, Bool.and_eq_true] at closed
              exact closed.1
            simp only [isQuote, if_true]
            cases found : exposedDrop? declaration (resolveQuotes declaration payload) with
            | some name => exact closedCode_of_exposedDrop found resolvedClosed
            | none =>
                simp only [closedCode, if_true, resolveQuotes_isWellScopedAt inScope, resolvedClosed,
                  Bool.and_self]
          · simp only [isQuote, if_false, closedCode, resolvedClosed]
      | first :: second :: rest, closed, ih =>
          simp only [closedCode, closedCodeList_eq_all, List.all_eq_true] at closed
          simp only [List.map_cons, finishResolveApply, closedCode, closedCodeList_eq_all, List.all_eq_true,
            List.mem_cons, List.mem_map]
          rintro element (rfl | rfl | ⟨original, member, rfl⟩)
          · exact ih first (by simp) (closed first (by simp))
          · exact ih second (by simp) (closed second (by simp))
          · exact ih original (by simp [member]) (closed original (by simp [member]))

/-- Admission is the closed code of the resolved form, read at any resolved term. -/
theorem quotesClosed_of_closedCode {term : Pattern} (closed : closedCode declaration term = true) :
    QuotesClosed declaration term :=
  closedCode_resolveQuotes closed

theorem resolveQuotes_unary_of_ne {constructor : String}
    (notQuote : constructor ≠ declaration.quoteConstructor) (payload : Pattern) :
    resolveQuotes declaration (.apply constructor [payload]) =
      .apply constructor [resolveQuotes declaration payload] := by
  simp [resolveQuotes, resolveQuotesList, finishResolveApply, notQuote]

theorem closedCode_unary_of_ne {constructor : String}
    (notQuote : constructor ≠ declaration.quoteConstructor) (payload : Pattern) :
    closedCode declaration (.apply constructor [payload]) = closedCode declaration payload := by
  simp [closedCode, notQuote]

/-! ### Admission is hereditary -/

/-- With quote and drop distinct, a composition that exposes a drop of a name is
closed code exactly when the name is. -/
theorem closedCode_iff_of_exposedDrop (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor)
    {pattern name : Pattern} (exposed : exposedDrop? declaration pattern = some name) :
    closedCode declaration pattern = closedCode declaration name := by
  rw [closedCode_eq_parallelLeaves]
  unfold exposedDrop? at exposed
  split at exposed
  · rename_i constructor argument leaves
    by_cases dropped : constructor = declaration.dropConstructor
    · simp only [dropped, if_true, Option.some.injEq] at exposed
      subst exposed
      rw [leaves]
      simp [closedCode, dropped, distinct]
    · simp [dropped] at exposed
  · cases exposed

theorem quotesClosed_unary_of_ne {constructor : String}
    (notQuote : constructor ≠ declaration.quoteConstructor) (payload : Pattern) :
    QuotesClosed declaration (.apply constructor [payload]) ↔ QuotesClosed declaration payload := by
  unfold QuotesClosed
  rw [resolveQuotes_unary_of_ne notQuote, closedCode_unary_of_ne notQuote]

/-- The code of an admitted quotation is admitted. -/
theorem quotesClosed_of_quote (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor)
    {payload : Pattern} (admitted : QuotesClosed declaration (.apply declaration.quoteConstructor [payload])) :
    QuotesClosed declaration payload := by
  unfold QuotesClosed at admitted ⊢
  simp only [resolveQuotes, resolveQuotesList, finishResolveApply, if_true] at admitted
  cases found : exposedDrop? declaration (resolveQuotes declaration payload) with
  | some name =>
      rw [found] at admitted
      rw [closedCode_iff_of_exposedDrop distinct found]
      exact admitted
  | none =>
      rw [found] at admitted
      simp only [closedCode, if_true, Bool.and_eq_true] at admitted
      exact admitted.2

theorem quotesClosed_apply_long (constructor : String) (first second : Pattern) (rest : List Pattern) :
    QuotesClosed declaration (.apply constructor (first :: second :: rest)) ↔
      ∀ argument ∈ first :: second :: rest, QuotesClosed declaration argument := by
  unfold QuotesClosed
  simp only [resolveQuotes, resolveQuotesList_eq_map, List.map_cons, finishResolveApply, closedCode,
    closedCodeList_eq_all, List.all_eq_true, List.mem_cons, List.mem_map, forall_eq_or_imp,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]

theorem quotesClosed_lambda (binder : Option String) (body : Pattern) :
    QuotesClosed declaration (.lambda binder body) ↔ QuotesClosed declaration body := Iff.rfl

theorem quotesClosed_collection (kind : CollType) (elements : List Pattern) (rest : Option String) :
    QuotesClosed declaration (.collection kind elements rest) ↔
      ∀ element ∈ elements, QuotesClosed declaration element := by
  unfold QuotesClosed
  simp only [resolveQuotes, resolveQuotesList_eq_map, closedCode, closedCodeList_eq_all, List.all_map,
    List.all_eq_true, Function.comp_apply]

/-- **Substitution in a resolved term keeps resolved closed code**, when every
inserted value and every received value resolves to closed code. A genuine
quotation of the term is kept as it is. -/
theorem closedCode_resolveQuotes_substituteResolved {atIndex : Nat → Nat → Pattern}
    (values : ∀ level index, closedCode declaration (resolveQuotes declaration (atIndex level index)) = true)
    (received : ∀ level, closedCode declaration
      (resolveQuotes declaration (receive declaration declaration.dropConstructor (atIndex level level))) = true)
    {body : Pattern} (resolved : QuotesResolved declaration body) :
    closedCode declaration body = true → ∀ depth,
      closedCode declaration (resolveQuotes declaration (substituteResolved declaration atIndex depth body)) =
        true := by
  induction body using Pattern.inductionOn with
  | hbvar index => intro _ depth; exact values depth index
  | hfvar name => intro _ _; rfl
  | hlambda binder body ih =>
      intro closed depth
      simp only [substituteResolved, resolveQuotes, closedCode]
      exact ih resolved closed (depth + 1)
  | hmultiLambda arity binders body ih =>
      intro closed depth
      simp only [substituteResolved, resolveQuotes, closedCode]
      exact ih resolved closed (depth + arity)
  | hsubst body value ihBody ihValue =>
      intro closed depth
      simp only [closedCode, Bool.and_eq_true] at closed
      simp only [substituteResolved, resolveQuotes, closedCode, ihBody resolved.1 closed.1 (depth + 1),
        ihValue resolved.2 closed.2 depth, Bool.and_self]
  | hcollection kind elements rest ih =>
      intro closed depth
      have each := (quotesResolvedList_iff elements).mp resolved
      simp only [closedCode, closedCodeList_eq_all, List.all_eq_true] at closed
      simp only [substituteResolved, substituteResolvedList_eq_map, resolveQuotes, resolveQuotesList_eq_map,
        List.map_map, closedCode, closedCodeList_eq_all, List.all_map, List.all_eq_true, Function.comp_apply]
      exact fun element member => ih element member (each element member) (closed element member) depth
  | happly constructor arguments ih =>
      intro closed depth
      match arguments, resolved, closed, ih with
      | [], _, _, _ => simp [substituteResolved, resolveQuotes, resolveQuotesList, finishResolveApply, closedCode]
      | [payload], resolved, closed, ih =>
          have payloadResolved : QuotesResolved declaration payload := resolved.1.1
          by_cases isQuote : constructor = declaration.quoteConstructor
          · have genuine : exposedDrop? declaration payload = none := resolved.2 payload rfl isQuote
            simp only [substituteResolved, isQuote, if_true, resolveQuotes, resolveQuotesList,
              resolveQuotes_of_resolved payloadResolved, finishResolveApply, genuine]
            rw [← isQuote]
            simpa [resolveQuotes_of_resolved payloadResolved] using
              (show closedCode declaration (.apply constructor [payload]) = true from closed)
          · have payloadClosed : closedCode declaration payload = true := by
              simpa [closedCode, isQuote] using closed
            by_cases isDrop : constructor = declaration.dropConstructor
            · by_cases selected : matchesBinder declaration depth payload = true
              · subst isDrop
                simp only [substituteResolved, isQuote, if_false, if_true, selected]
                exact received depth
              · rw [show substituteResolved declaration atIndex depth (.apply constructor [payload]) =
                    .apply constructor [substituteResolved declaration atIndex depth payload] by
                    simp only [substituteResolved, if_neg isQuote, if_pos isDrop, if_neg selected],
                  resolveQuotes_unary_of_ne isQuote, closedCode_unary_of_ne isQuote]
                exact ih payload (by simp) payloadResolved payloadClosed depth
            · rw [show substituteResolved declaration atIndex depth (.apply constructor [payload]) =
                  .apply constructor [substituteResolved declaration atIndex depth payload] by
                  simp [substituteResolved, isQuote, isDrop],
                resolveQuotes_unary_of_ne isQuote, closedCode_unary_of_ne isQuote]
              exact ih payload (by simp) payloadResolved payloadClosed depth
      | first :: second :: rest, resolved, closed, ih =>
          have each := (quotesResolvedList_iff _).mp resolved.1
          simp only [closedCode, closedCodeList_eq_all, List.all_eq_true] at closed
          simp only [substituteResolved, substituteResolvedList_eq_map, List.map_cons, resolveQuotes,
            resolveQuotesList_eq_map, finishResolveApply, closedCode, closedCodeList_eq_all, List.all_eq_true,
            List.mem_cons, List.mem_map]
          rintro element (rfl | rfl | ⟨original, ⟨inner, member, rfl⟩, rfl⟩)
          · exact ih first (by simp) (each first (by simp)) (closed first (by simp)) depth
          · exact ih second (by simp) (each second (by simp)) (closed second (by simp)) depth
          · exact ih inner (by simp [member]) (each inner (by simp [member]))
              (closed inner (by simp [member])) depth

/-- A received closed name keeps closed code: a received quotation runs its
code, any other name stays under the drop. -/
theorem closedCode_resolveQuotes_receive (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor)
    {name : Pattern} (admitted : QuotesClosed declaration name) :
    closedCode declaration
      (resolveQuotes declaration (receive declaration declaration.dropConstructor name)) = true := by
  unfold QuotesClosed at admitted
  unfold receive
  split
  · rename_i quote process
    split
    · rename_i isQuote
      subst isQuote
      simp only [resolveQuotes, resolveQuotesList, finishResolveApply, if_true] at admitted
      cases found : exposedDrop? declaration (resolveQuotes declaration process) with
      | some exposedName =>
          rw [found] at admitted
          rw [closedCode_eq_parallelLeaves]
          unfold exposedDrop? at found
          split at found
          · rename_i constructor argument leaves
            by_cases dropped : constructor = declaration.dropConstructor
            · simp only [dropped, if_true, Option.some.injEq] at found
              subst found
              rw [leaves]
              simp [closedCode, dropped, distinct, admitted]
            · simp [dropped] at found
          · cases found
      | none =>
          rw [found] at admitted
          simp only [closedCode, if_true, Bool.and_eq_true] at admitted
          exact admitted.2
    · simp only [resolveQuotes, resolveQuotesList, finishResolveApply, distinct, if_false, closedCode]
      exact admitted
  · simp only [resolveQuotes, resolveQuotesList, finishResolveApply, distinct, if_false, closedCode]
    exact admitted

/-- **Eliminating a binder by an admitted closed name keeps admission.** -/
theorem quotesClosed_instantiate (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor)
    (depth : Nat) {replacement body : Pattern}
    (replacementClosed : replacement.isWellScopedAt 0 = true)
    (replacementAdmitted : QuotesClosed declaration replacement)
    (bodyAdmitted : QuotesClosed declaration body) :
    QuotesClosed declaration (instantiate declaration depth replacement body) := by
  unfold QuotesClosed
  have lifted : ∀ level, liftBVars 0 level replacement = replacement := fun level =>
    liftBVars_eq_self_of_isWellScopedAt replacementClosed
  apply closedCode_resolveQuotes_substituteResolved _ _ (resolveQuotes_resolved body) bodyAdmitted depth
  · intro level index
    show closedCode declaration (resolveQuotes declaration (instantiateBVarAt level replacement (.bvar index))) =
      true
    rcases Nat.lt_trichotomy index level with below | same | above
    · simp [instantiateBVarAt, below, resolveQuotes, closedCode]
    · subst same
      simp only [instantiateBVarAt, Nat.lt_irrefl, if_false, if_true, lifted]
      exact replacementAdmitted
    · simp [instantiateBVarAt, Nat.not_lt.mpr above.le, Nat.ne_of_gt above, resolveQuotes, closedCode]
  · intro level
    show closedCode declaration (resolveQuotes declaration
      (receive declaration declaration.dropConstructor (instantiateBVarAt level replacement (.bvar level)))) =
        true
    simp only [instantiateBVarAt, Nat.lt_irrefl, if_false, if_true, lifted]
    exact closedCode_resolveQuotes_receive distinct replacementAdmitted

/-- **Binder-preserving substitution of an admitted closed name keeps admission.** -/
theorem quotesClosed_substituteReflective (distinct : declaration.dropConstructor ≠ declaration.quoteConstructor)
    (depth : Nat) {replacement body : Pattern}
    (replacementAdmitted : QuotesClosed declaration replacement)
    (bodyAdmitted : QuotesClosed declaration body) :
    QuotesClosed declaration (substituteReflective declaration depth replacement body) := by
  unfold QuotesClosed substituteReflective
  apply closedCode_resolveQuotes_substituteResolved _ _ (resolveQuotes_resolved body) bodyAdmitted depth
  · intro level index
    by_cases same : index = level
    · simp only [same, if_true]; exact replacementAdmitted
    · simp only [same, if_false]; rfl
  · intro level
    simp only [if_true]
    exact closedCode_resolveQuotes_receive distinct replacementAdmitted

/-- **Quote-sealed scope gives closed code.** If every quotation's payload is
sealed at depth zero, every quotation's code is closed. -/
theorem closedCode_of_binderSafeAt {pattern : Pattern} {depth : Nat}
    (safe : binderSafeAt declaration.quoteConstructor depth pattern = true) :
    closedCode declaration pattern = true := by
  induction pattern using Pattern.inductionOn generalizing depth with
  | hbvar index => rfl
  | hfvar name => rfl
  | happly constructor arguments ih =>
      rcases arguments with _ | ⟨payload, _ | ⟨second, rest⟩⟩
      · rfl
      · by_cases quoted : constructor = declaration.quoteConstructor
        · subst quoted
          simp only [binderSafeAt, beq_self_eq_true, if_true] at safe
          simp only [closedCode, if_true, isWellScopedAt_of_binderSafeAt _ safe,
            ih payload (by simp) safe, Bool.and_self]
        · simp only [binderSafeAt, beq_iff_eq, if_neg quoted, binderSafeListAt, Bool.and_true] at safe
          simp only [closedCode, if_neg quoted]
          exact ih payload (by simp) safe
      · simp only [binderSafeAt] at safe
        rw [closedCode, closedCodeList_eq_all, List.all_eq_true]
        intro child member
        exact ih child member ((binderSafeListAt_eq_true_iff _ _ _).mp safe child member)
  | hlambda binder body ih => exact ih safe
  | hmultiLambda arity binders body ih => exact ih safe
  | hsubst body value ihBody ihValue =>
      simp only [binderSafeAt, Bool.and_eq_true] at safe
      simp only [closedCode, ihBody safe.1, ihValue safe.2, Bool.and_self]
  | hcollection kind elements rest ih =>
      simp only [binderSafeAt] at safe
      rw [closedCode, closedCodeList_eq_all, List.all_eq_true]
      intro child member
      exact ih child member ((binderSafeListAt_eq_true_iff _ _ _).mp safe child member)

/-- Quote-sealed scope gives closed quotations on the resolved term. -/
theorem quotesClosed_of_binderSafeAt {pattern : Pattern} {depth : Nat}
    (safe : binderSafeAt declaration.quoteConstructor depth pattern = true) :
    QuotesClosed declaration pattern :=
  closedCode_of_binderSafeAt (resolveQuotes_binderSafeAt declaration safe)

end Admission

/-! ### Admission of a quotation -/

section QuotationAdmission

/-- A quotation of closed, admitted code is admitted. -/
theorem quoteAdmits_of_quotesClosed (declaration : ReflectivePresentationDecl) {payload : Pattern}
    (payloadClosed : payload.isWellScopedAt 0 = true)
    (payloadAdmitted : QuotesClosed declaration payload) :
    quoteAdmits declaration payload = true := by
  unfold quoteAdmits
  split
  · unfold QuotesClosed at payloadAdmitted
    simp only [resolveQuotes, resolveQuotesList, finishResolveApply, if_true]
    cases found : exposedDrop? declaration (resolveQuotes declaration payload) with
    | some name => exact closedCode_of_exposedDrop found payloadAdmitted
    | none =>
        simp only [closedCode, if_true, resolveQuotes_isWellScopedAt payloadClosed, payloadAdmitted,
          Bool.and_self]
  · rfl

/-- A quotation of quote-sealed code is admitted, whatever the scope. -/
theorem quoteAdmits_of_binderSafeAt (declaration : ReflectivePresentationDecl) {payload : Pattern}
    (safe : binderSafeAt declaration.quoteConstructor 0 payload = true) :
    quoteAdmits declaration payload = true :=
  quoteAdmits_of_quotesClosed declaration (isWellScopedAt_of_binderSafeAt _ safe)
    (quotesClosed_of_binderSafeAt safe)

end QuotationAdmission

/-! ## Sorting does not read the quote scope

The quote scope selects a substitution policy. Two policies on one signature
sort the same terms and may admit different ones. -/

/-- The same signature under another quote scope. -/
def _root_.Mettapedia.OSLF.MeTTaIL.Syntax.ReflectiveProcessSignature.withQuoteScope
    (presentation : ReflectiveProcessSignature) (scope : QuoteScope) : ReflectiveProcessSignature :=
  { presentation with quoteScope := scope }

section Independence

open DerivedPresentationSyntax

variable {presentation : ReflectiveProcessSignature} {free : FreeSortContext}

mutual
  /-- A name keeps its sort under every quote scope. -/
  theorem _root_.Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax.NameWellSorted.toQuoteScope
      (scope : QuoteScope) {bound : List String} {name : Pattern}
      (typed : NameWellSorted presentation free bound name) :
      NameWellSorted (presentation.withQuoteScope scope) free bound name := by
    cases typed with
    | bvar lookup => exact .bvar lookup
    | fvar lookup => exact .fvar lookup
    | quote processTyped => exact .quote (processTyped.toQuoteScope scope)

  /-- A process keeps its sort under every quote scope. -/
  theorem _root_.Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax.ProcWellSorted.toQuoteScope
      (scope : QuoteScope) {bound : List String} {process : Pattern}
      (typed : ProcWellSorted presentation free bound process) :
      ProcWellSorted (presentation.withQuoteScope scope) free bound process := by
    cases typed with
    | bvar lookup => exact .bvar lookup
    | fvar lookup => exact .fvar lookup
    | unit => exact .unit
    | drop nameTyped => exact .drop (nameTyped.toQuoteScope scope)
    | output channelTyped payloadTyped =>
        exact .output (channelTyped.toQuoteScope scope) (payloadTyped.toQuoteScope scope)
    | input channelTyped bodyTyped =>
        exact .input (channelTyped.toQuoteScope scope) (bodyTyped.toQuoteScope scope)
    | parallel processesTyped => exact .parallel (processesTyped.toQuoteScope scope)

  /-- List form. -/
  theorem _root_.Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax.ProcListWellSorted.toQuoteScope
      (scope : QuoteScope) {bound : List String} {processes : List Pattern}
      (typed : ProcListWellSorted presentation free bound processes) :
      ProcListWellSorted (presentation.withQuoteScope scope) free bound processes := by
    cases typed with
    | nil => exact .nil
    | cons processTyped processesTyped =>
        exact .cons (processTyped.toQuoteScope scope) (processesTyped.toQuoteScope scope)
end

/-- **Sorting of names is independent of the quote scope.** -/
theorem nameWellSorted_withQuoteScope_iff (scope : QuoteScope) {bound : List String} {name : Pattern} :
    NameWellSorted (presentation.withQuoteScope scope) free bound name ↔
      NameWellSorted presentation free bound name :=
  ⟨fun typed => typed.toQuoteScope presentation.quoteScope, fun typed => typed.toQuoteScope scope⟩

/-- **Sorting of processes is independent of the quote scope.** -/
theorem procWellSorted_withQuoteScope_iff (scope : QuoteScope) {bound : List String} {process : Pattern} :
    ProcWellSorted (presentation.withQuoteScope scope) free bound process ↔
      ProcWellSorted presentation free bound process :=
  ⟨fun typed => typed.toQuoteScope presentation.quoteScope, fun typed => typed.toQuoteScope scope⟩

end Independence

/-! ### Controls in rho -/

section Controls

open DerivedPresentationSyntax

/-- `y!(0)`, where `y` is the enclosing binder. -/
private def openCode : Pattern := .apply "POutput" [.bvar 0, .apply "PZero" []]

/-- `*y`, where `y` is the enclosing binder. -/
private def exposedCode : Pattern := .apply "PDrop" [.bvar 0]

/-- `@(y!(0))` under the binder of `y` is a rho name, and its code is not closed. -/
theorem sorted_not_admitted :
    NameWellSorted rhoReflectivePresentation FreeSortContext.empty ["Name"]
        (.apply "NQuote" [openCode]) ∧
      ¬ QuotesClosed rhoReflectivePresentation.toReflectivePresentationDecl
        (.apply "NQuote" [openCode]) :=
  ⟨.quote (.output (.bvar rfl) .unit), by decide +kernel⟩

/-- `@(*y)` under the binder of `y` is admitted, since it denotes `y`, although
its spelling is not quote-sealed. -/
theorem admitted_not_sealed :
    NameWellSorted rhoReflectivePresentation FreeSortContext.empty ["Name"]
        (.apply "NQuote" [exposedCode]) ∧
      QuotesClosed rhoReflectivePresentation.toReflectivePresentationDecl
        (.apply "NQuote" [exposedCode]) ∧
      binderSafeAt "NQuote" 1 (.apply "NQuote" [exposedCode]) = false :=
  ⟨.quote (.drop (.bvar rfl)), by decide +kernel, by decide +kernel⟩

/-- Admission reads the quote scope: one signature, two policies. -/
theorem quoteAdmits_reads_quoteScope :
    quoteAdmits (rhoReflectivePresentation.withQuoteScope .closed).toReflectivePresentationDecl
        openCode = false ∧
      quoteAdmits (rhoReflectivePresentation.withQuoteScope (.reaching .apply)).toReflectivePresentationDecl
        openCode = true := by
  decide +kernel

/-- Why substitution asks for admission: eliminating the binder of a sorted
body that is not admitted leaves an unbound index in the quoted code; for the
admitted body the same elimination gives a closed term. -/
theorem instantiate_scope_needs_admission :
    ProcWellSorted rhoReflectivePresentation FreeSortContext.empty ["Name"]
        (.apply "PDrop" [.apply "NQuote" [openCode]]) ∧
      (instantiate rhoReflectivePresentation.toReflectivePresentationDecl 0
          (.apply "NQuote" [.apply "PZero" []])
          (.apply "PDrop" [.apply "NQuote" [openCode]])).isWellScopedAt 0 = false ∧
      (instantiate rhoReflectivePresentation.toReflectivePresentationDecl 0
          (.apply "NQuote" [.apply "PZero" []])
          (.apply "PDrop" [.apply "NQuote" [exposedCode]])).isWellScopedAt 0 = true :=
  ⟨.drop (.quote (.output (.bvar rfl) .unit)), by decide +kernel, by decide +kernel⟩

end Controls

end Mettapedia.OSLF.MeTTaIL.ReflectiveQuoteAdmission
