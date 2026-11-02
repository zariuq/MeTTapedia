import Mettapedia.Languages.VibeITP.Presentation.SimultaneousExecution
import Mettapedia.Languages.VibeITP.Presentation.SimultaneousFormation
import Mettapedia.Languages.VibeITP.Spec.DerivationV2

/-!
# Authored traversal with a retained replacement environment

The argument-list adapter preserves the original binder-index lookup, including
missing binders and word refusals. Recursive execution uses the existing shift
and substitution computations after looking up the replacement exactly once.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
namespace Mettapedia.Languages.VibeITP.Presentation.ComputationalSimultaneous

open ComputationalData ComputationalShift ComputationalSubstitution
open ComputationalInstantiation ComputationalInference
open SimultaneousFormation
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => simultaneousProgram
local notation "A" => simultaneousEquations
local notation "H" => computationalHost

private theorem option_bind_match {α β : Type} (value : Option α) (next : α → Option β) :
    value.bind next = match value with | none => none | some element => next element := by
  cases value <;> rfl

private theorem add_applies (left right : Nat) :
    Applies P H "nik:nat-add" [natural left, natural right] (natural (left + right)) :=
  .primitive (by rfl) (naturalArithmeticHost_add left right)

private theorem lt_applies (left right : Nat) :
    Applies P H "nik:nat-lt" [natural left, natural right] (boolean (decide (left < right))) :=
  .primitive (by rfl) (naturalArithmeticHost_lt left right)

private theorem app_start (table : SignatureTable) (entries : List Spec.SimultaneousInstantiation.Entry)
    (offset : Nat) (symbol : Spec.SymId) (arguments : List Spec.Term) (result : Term)
    (next : Applies P H "vibe:many-pruned"
      [boolean (Spec.hasFvar (signatureOf table) (.app symbol arguments)), encodeTable table,
        encodeEntries entries, natural offset, encodeSymbol symbol, .list (encodeTerms arguments)] result) :
    Applies P H "vibe:many-go"
      [encodeTable table, encodeEntries entries, natural offset, encode (.app symbol arguments)] result := by
  refine simultaneous_equation (equation := A[18])
    (environment := [("table", encodeTable table), ("entries", encodeEntries entries),
      ("offset", natural offset), ("symbol", encodeSymbol symbol), ("arguments", .list (encodeTerms arguments))])
    (by decide +kernel) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))) next
  refine Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) (.cons ?_ .nil))
    (instantiation_applies (by decide +kernel) (hasFvar_computes table (.app symbol arguments)))
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (Applies.constructor (by rfl) (by rfl))

private theorem head_result (table : SignatureTable) (offset : Nat) (symbol : Spec.SymId)
    (arguments : List Spec.Term) (entry : Option Spec.SimultaneousInstantiation.Entry) :
    Applies P H "vibe:many-head"
      [encodeEntryResult entry, encodeTable table, natural offset, encodeSymbol symbol, .list (encodeTerms arguments)]
      (encodeResult (match entry with
        | none => some (.app symbol arguments)
        | some replacement =>
            (Spec.shift (signatureOf table) offset replacement.arity replacement.value).bind
              (fun shifted => Spec.substBVars (signatureOf table) replacement.arity arguments shifted 0))) := by
  cases entry with
  | none => exact ⟨3, rfl⟩
  | some replacement =>
      refine simultaneous_equation (equation := A[24])
        (environment := [("target", encodeSymbol replacement.symbol), ("arity", natural replacement.arity),
          ("value", encode replacement.value), ("table", encodeTable table), ("offset", natural offset),
          ("symbol", encodeSymbol symbol), ("arguments", .list (encodeTerms arguments))])
        (by decide +kernel) (by rfl) (by rfl) ?_
      refine Evaluates.call (by simp [Special])
        (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))
        (instantiation_applies (by decide +kernel) (instValue_computes table replacement.arity arguments _))
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))
        (substitution_applies (by decide +kernel)
          (shift_computes_in_substitution table offset replacement.arity replacement.value))

private theorem children_result (table : SignatureTable) (entries : List Spec.SimultaneousInstantiation.Entry)
    (offset : Nat) (symbol : Spec.SymId) (processed : Option (List Spec.Term)) :
    Applies P H "vibe:many-children"
      [encodeTermsResult processed, encodeTable table, encodeEntries entries, natural offset, encodeSymbol symbol]
      (encodeResult (processed.bind fun arguments =>
        match Spec.SimultaneousInstantiation.lookup entries symbol with
        | none => some (.app symbol arguments)
        | some replacement =>
            (Spec.shift (signatureOf table) offset replacement.arity replacement.value).bind
              (fun shifted => Spec.substBVars (signatureOf table) replacement.arity arguments shifted 0))) := by
  cases processed with
  | none => exact ⟨1, rfl⟩
  | some arguments =>
      refine simultaneous_equation (equation := A[22])
        (environment := [("arguments", .list (encodeTerms arguments)), ("table", encodeTable table),
          ("entries", encodeEntries entries), ("offset", natural offset), ("symbol", encodeSymbol symbol)])
        (by decide +kernel) (by rfl) (by rfl) ?_
      refine Evaluates.call (by simp [Special])
        (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))
        (head_result table offset symbol arguments _)
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (lookup_computes entries symbol)

private theorem app_children (table : SignatureTable) (entries : List Spec.SimultaneousInstantiation.Entry)
    (offset : Nat) (symbol : Spec.SymId) (arguments : List Spec.Term) (processed result : Term)
    (children : Applies P H "vibe:many-args" [encodeTable table, encodeEntries entries, natural offset,
      encodeBinders (bindersOf (signatureOf table) symbol), .list (encodeTerms arguments)] processed)
    (next : Applies P H "vibe:many-children"
      [processed, encodeTable table, encodeEntries entries, natural offset, encodeSymbol symbol] result) :
    Applies P H "vibe:many-pruned" [.sym "True", encodeTable table, encodeEntries entries,
      natural offset, encodeSymbol symbol, .list (encodeTerms arguments)] result := by
  refine simultaneous_equation (equation := A[20])
    (environment := [("table", encodeTable table), ("entries", encodeEntries entries), ("offset", natural offset),
      ("symbol", encodeSymbol symbol), ("arguments", .list (encodeTerms arguments))])
    (by decide +kernel) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))) next
  refine Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons ?_ (.cons (.variable (by rfl)) .nil))))) children
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))
    (substitution_applies (by decide +kernel) (binders_computes_in_substitution table symbol))

private theorem arguments_start (table : SignatureTable) (entries : List Spec.SimultaneousInstantiation.Entry)
    (offset : Nat) (binders : List Nat) (arguments : List Spec.Term) (result : Term)
    (next : Applies P H "vibe:many-args-view" [encodeTable table, encodeEntries entries, natural offset,
      encodeBinders binders, listView (encodeTerms arguments)] result) :
    Applies P H "vibe:many-args" [encodeTable table, encodeEntries entries, natural offset,
      encodeBinders binders, .list (encodeTerms arguments)] result := by
  refine simultaneous_equation (equation := A[25])
    (environment := [("table", encodeTable table), ("entries", encodeEntries entries), ("offset", natural offset),
      ("binders", encodeBinders binders), ("arguments", .list (encodeTerms arguments))])
    (by decide +kernel) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons ?_ .nil))))) next
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (view_applies (encodeTerms arguments))

private theorem arguments_cons (table : SignatureTable) (entries : List Spec.SimultaneousInstantiation.Entry)
    (offset : Nat) (binders : List Nat) (first : Spec.Term) (rest : List Spec.Term) (result : Term)
    (next : Applies P H "vibe:many-args-binder" [encodeTable table, encodeEntries entries, natural offset,
      listView (binders.map natural), encode first, .list (encodeTerms rest)] result) :
    Applies P H "vibe:many-args-view" [encodeTable table, encodeEntries entries, natural offset,
      encodeBinders binders, listView (encodeTerms (first :: rest))] result := by
  refine simultaneous_equation (equation := A[27])
    (environment := [("table", encodeTable table), ("entries", encodeEntries entries), ("offset", natural offset),
      ("binders", encodeBinders binders), ("first", encode first), ("rest", .list (encodeTerms rest))])
    (by decide +kernel) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))) next
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (view_applies (binders.map natural))

private theorem arguments_binder (table : SignatureTable) (entries : List Spec.SimultaneousInstantiation.Entry)
    (offset : Nat) (binders : List Nat) (first : Spec.Term) (rest : List Spec.Term) (result : Term)
    (next : Applies P H "vibe:many-args-bound" [boolean (decide (offset + binders.headD 0 < Spec.wordBound)),
      encodeTable table, encodeEntries entries, natural offset, encodeBinders binders.tail,
      natural (offset + binders.headD 0), encode first, .list (encodeTerms rest)] result) :
    Applies P H "vibe:many-args-binder" [encodeTable table, encodeEntries entries, natural offset,
      listView (binders.map natural), encode first, .list (encodeTerms rest)] result := by
  cases binders with
  | nil =>
      simp only [List.headD_nil, List.tail_nil, Nat.add_zero] at next
      refine simultaneous_equation (equation := A[28])
        (environment := [("table", encodeTable table), ("entries", encodeEntries entries),
          ("offset", natural offset), ("first", encode first), ("rest", .list (encodeTerms rest))])
        (by decide +kernel) (by rfl) (by rfl) ?_
      refine Evaluates.call (by simp [Special])
        (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (show Evaluates P H _ (.list []) (.list []) from ⟨1, rfl⟩) (.cons (.variable (by rfl))
            (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))))) next
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.literal _ _ _ _) .nil)) (lt_applies offset Spec.wordBound)
  | cons bound tail =>
      simp only [List.headD_cons, List.tail_cons] at next
      refine simultaneous_equation (equation := A[29])
        (environment := [("table", encodeTable table), ("entries", encodeEntries entries), ("offset", natural offset),
          ("bound", natural bound), ("tail", encodeBinders tail), ("first", encode first),
          ("rest", .list (encodeTerms rest))]) (by decide +kernel) (by rfl) (by rfl) ?_
      have sum : Evaluates P H
          [("table", encodeTable table), ("entries", encodeEntries entries), ("offset", natural offset),
            ("bound", natural bound), ("tail", encodeBinders tail), ("first", encode first),
            ("rest", .list (encodeTerms rest))]
          (.expr [.sym "nik:nat-add", .var "offset", .var "bound"]) (natural (offset + bound)) :=
        Evaluates.call (by simp [Special])
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (add_applies offset bound)
      refine Evaluates.call (by simp [Special])
        (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) (.cons sum
            (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))))) next
      exact Evaluates.call (by simp [Special]) (.cons sum (.cons (.literal _ _ _ _) .nil))
        (lt_applies (offset + bound) Spec.wordBound)

private theorem arguments_first (table : SignatureTable) (entries : List Spec.SimultaneousInstantiation.Entry)
    (offset : Nat) (binders : List Nat) (first : Spec.Term) (rest : List Spec.Term)
    (processed : Option (List Spec.Term))
    (tail : Applies P H "vibe:many-args" [encodeTable table, encodeEntries entries, natural offset,
      encodeBinders binders, .list (encodeTerms rest)] (encodeTermsResult processed)) :
    Applies P H "vibe:many-args-first" [encodeResult (some first), encodeTable table, encodeEntries entries,
      natural offset, encodeBinders binders, .list (encodeTerms rest)]
      (encodeTermsResult (processed.map (first :: ·))) := by
  refine simultaneous_equation (equation := A[33])
    (environment := [("first", encode first), ("table", encodeTable table), ("entries", encodeEntries entries),
      ("offset", natural offset), ("binders", encodeBinders binders), ("rest", .list (encodeTerms rest))])
    (by decide +kernel) (by rfl) (by rfl) ?_
  refine Evaluates.call (values := [encode first, encodeTermsResult processed])
    (by simp [Special]) (.cons (.variable (by rfl)) (.cons ?_ .nil)) ?_
  · exact Evaluates.call (by simp [Special])
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))) tail
  · apply instantiation_applies (by decide +kernel)
    cases processed with
    | none => exact ⟨1, rfl⟩
    | some results => exact ⟨3, rfl⟩

private theorem arguments_children (table : SignatureTable) (entries : List Spec.SimultaneousInstantiation.Entry)
    (offset inside : Nat) (binders : List Nat) (first : Spec.Term) (rest : List Spec.Term)
    (headResult : Option Spec.Term) (tailResult : Option (List Spec.Term))
    (head : Applies P H "vibe:many-go" [encodeTable table, encodeEntries entries, natural inside, encode first]
      (encodeResult headResult))
    (tail : Applies P H "vibe:many-args" [encodeTable table, encodeEntries entries, natural offset,
      encodeBinders binders, .list (encodeTerms rest)] (encodeTermsResult tailResult)) :
    Applies P H "vibe:many-args-bound" [.sym "True", encodeTable table, encodeEntries entries, natural offset,
      encodeBinders binders, natural inside, encode first, .list (encodeTerms rest)]
      (encodeTermsResult (headResult.bind fun first' => tailResult.map (first' :: ·))) := by
  refine simultaneous_equation (equation := A[31])
    (environment := [("table", encodeTable table), ("entries", encodeEntries entries), ("offset", natural offset),
      ("binders", encodeBinders binders), ("inside", natural inside), ("first", encode first),
      ("rest", .list (encodeTerms rest))]) (by decide +kernel) (by rfl) (by rfl) ?_
  refine Evaluates.call (values := [encodeResult headResult, encodeTable table, encodeEntries entries,
      natural offset, encodeBinders binders, .list (encodeTerms rest)]) (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))) ?_
  · exact Evaluates.call (by simp [Special])
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))) head
  · cases headResult with
    | none => exact ⟨1, rfl⟩
    | some first' => exact arguments_first table entries offset binders first' rest tailResult tail

mutual
theorem go_computes (table : SignatureTable) (entries : List Spec.SimultaneousInstantiation.Entry)
    (offset : Nat) (term : Spec.Term) :
    Applies P H "vibe:many-go" [encodeTable table, encodeEntries entries, natural offset, encode term]
      (encodeResult (Spec.SimultaneousInstantiation.go (signatureOf table) entries offset term)) := by
  cases term with
  | bvar _ => exact ⟨3, rfl⟩
  | lit _ => exact ⟨3, rfl⟩
  | app symbol arguments =>
      apply app_start
      cases present : Spec.hasFvar (signatureOf table) (.app symbol arguments) with
      | false => simp only [Spec.SimultaneousInstantiation.go, present, if_true, boolean]; exact ⟨3, rfl⟩
      | true =>
          have computed := app_children table entries offset symbol arguments _ _
            (argumentList_computes table entries offset (bindersOf (signatureOf table) symbol) arguments)
            (children_result table entries offset symbol _)
          simp only [Spec.SimultaneousInstantiation.go, present, Bool.true_eq_false, if_false,
            args_eq_argumentList, List.drop_zero]
          cases processed : argumentList (signatureOf table) entries offset (bindersOf (signatureOf table) symbol) arguments with
          | none => simpa only [processed, option_bind_match, boolean, ↓reduceIte] using computed
          | some arguments' =>
              cases found : Spec.SimultaneousInstantiation.lookup entries symbol with
              | none => simpa only [processed, found, option_bind_match, boolean, ↓reduceIte] using computed
              | some entry =>
                  cases shifted : Spec.shift (signatureOf table) offset entry.arity entry.value <;>
                    simpa only [processed, found, shifted, option_bind_match, boolean, ↓reduceIte] using computed

theorem argumentList_computes (table : SignatureTable) (entries : List Spec.SimultaneousInstantiation.Entry)
    (offset : Nat) (binders : List Nat) (arguments : List Spec.Term) :
    Applies P H "vibe:many-args" [encodeTable table, encodeEntries entries, natural offset,
      encodeBinders binders, .list (encodeTerms arguments)]
      (encodeTermsResult (argumentList (signatureOf table) entries offset binders arguments)) := by
  cases arguments with
  | nil => exact arguments_start table entries offset binders [] _ ⟨2, rfl⟩
  | cons first rest =>
      apply arguments_start
      apply arguments_cons
      apply arguments_binder
      by_cases fits : offset + binders.headD 0 < Spec.wordBound
      · have computed := arguments_children table entries offset (offset + binders.headD 0) binders.tail first rest _ _
          (go_computes table entries (offset + binders.headD 0) first)
          (argumentList_computes table entries offset binders.tail rest)
        simp only [argumentList, boolean, fits, decide_true, if_true]
        convert computed using 2
        cases Spec.SimultaneousInstantiation.go (signatureOf table) entries (offset + binders.headD 0) first <;>
          cases argumentList (signatureOf table) entries offset binders.tail rest <;> rfl
      · simp only [argumentList, boolean, fits, decide_false, if_false]
        exact ⟨1, rfl⟩
end

private theorem entries_computes (table : SignatureTable) (entries : List Spec.SimultaneousInstantiation.Entry)
    (source : Spec.Term) :
    Applies P H "vibe:many-nonempty"
      [listView (entries.map encodeEntry), encodeEntries entries, encodeTable table, encode source]
      (encodeResult ((if entries.isEmpty then some source else
        Spec.SimultaneousInstantiation.go (signatureOf table) entries 0 source).bind
        (fun result => if Spec.depth (signatureOf table) result = 0 then some result else none))) := by
  cases entries with
  | nil =>
      refine simultaneous_equation (equation := A[37])
        (environment := [("entries", encodeEntries []), ("table", encodeTable table), ("statement", encode source)])
        (by decide +kernel) (by rfl) (by rfl) ?_
      refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) .nil))
        (instantiation_applies (by decide +kernel) (statement_result table (some source)))
      exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil)
        (Applies.constructor (by rfl) (by rfl))
  | cons first rest =>
      refine simultaneous_equation (equation := A[38])
        (environment := [("first", encodeEntry first), ("rest", encodeEntries rest),
          ("entries", encodeEntries (first :: rest)), ("table", encodeTable table), ("statement", encode source)])
        (by decide +kernel) (by rfl) (by rfl) ?_
      refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) .nil))
        (instantiation_applies (by decide +kernel)
          (statement_result table (Spec.SimultaneousInstantiation.go (signatureOf table) (first :: rest) 0 source)))
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (.literal _ _ _ _) (.cons (.variable (by rfl)) .nil)))) (go_computes table (first :: rest) 0 source)

private theorem prepared_computes (table : SignatureTable)
    (prepared : Option (List Spec.SimultaneousInstantiation.Entry)) (source : Spec.Term) :
    Applies P H "vibe:many-prepared" [encodePreparation prepared, encodeTable table, encode source]
      (encodeResult (prepared.bind fun entries =>
        (if entries.isEmpty then some source else Spec.SimultaneousInstantiation.go (signatureOf table) entries 0 source).bind
          (fun result => if Spec.depth (signatureOf table) result = 0 then some result else none))) := by
  cases prepared with
  | none => exact ⟨1, rfl⟩
  | some entries =>
      refine simultaneous_equation (equation := A[36])
        (environment := [("entries", encodeEntries entries), ("table", encodeTable table), ("statement", encode source)])
        (by decide +kernel) (by rfl) (by rfl) ?_
      refine Evaluates.call (by simp [Special])
        (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))
        (entries_computes table entries source)
      exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil)
        (view_applies (entries.map encodeEntry))

theorem statement_computes (table : SignatureTable) (replacements : List (Spec.SymId × Spec.Term))
    (source : Spec.Term) :
    Applies P H "vibe:instantiate-many" [encodeTable table, encodeReplacements replacements, encode source]
      (encodeResult (Spec.SimultaneousInstantiation.statement (signatureOf table) replacements source)) := by
  refine simultaneous_equation (equation := A[34])
    (environment := [("table", encodeTable table), ("replacements", encodeReplacements replacements),
      ("statement", encode source)]) (by decide +kernel) (by rfl) (by rfl) ?_
  refine Evaluates.call (values := [encodePreparation (Spec.SimultaneousInstantiation.prepare (signatureOf table) replacements),
      encodeTable table, encode source]) (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))) ?_
  · exact Evaluates.call (by simp [Special])
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (prepare_computes table replacements)
  · have computed := prepared_computes table
      (Spec.SimultaneousInstantiation.prepare (signatureOf table) replacements) source
    cases prepared : Spec.SimultaneousInstantiation.prepare (signatureOf table) replacements with
    | none => simpa only [Spec.SimultaneousInstantiation.statement, prepared, option_bind_match] using computed
    | some entries =>
        by_cases empty : entries.isEmpty = true
        · simpa only [Spec.SimultaneousInstantiation.statement, prepared, option_bind_match, empty, if_true] using computed
        · cases traversed : Spec.SimultaneousInstantiation.go (signatureOf table) entries 0 source <;>
            simpa only [Spec.SimultaneousInstantiation.statement, prepared, option_bind_match, empty,
              Bool.false_eq_true, if_false, traversed]
              using computed

theorem formed_computes (table : SignatureTable) (replacements : List (Spec.SymId × Spec.Term)) :
    Applies P H "vibe:many-formed" [encodeTable table, encodeReplacements replacements]
      (boolean (replacements.all fun pair => Spec.WellFormed (signatureOf table) pair.2)) := by
  induction replacements with
  | nil => exact ⟨3, rfl⟩
  | cons replacement rest ih =>
      rcases replacement with ⟨symbol, value⟩
      refine simultaneous_equation (equation := A[39])
        (environment := [("table", encodeTable table), ("replacements", encodeReplacements ((symbol, value) :: rest))])
        (by decide +kernel) (by rfl) (by rfl) ?_
      refine Evaluates.call (values := [encodeTable table,
          listView (((symbol, value) :: rest).map encodeReplacement)])
        (by simp [Special]) (.cons (.variable (by rfl)) (.cons ?_ .nil)) ?_
      · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil)
          (view_applies (((symbol, value) :: rest).map encodeReplacement))
      · refine simultaneous_equation (equation := A[41])
          (environment := [("table", encodeTable table), ("symbol", encodeSymbol symbol),
            ("value", encode value), ("rest", encodeReplacements rest)])
          (by decide +kernel) (by rfl) (by rfl) ?_
        refine Evaluates.call (values := [boolean (Spec.WellFormed (signatureOf table) value),
            encodeTable table, encodeReplacements rest]) (by simp [Special])
          (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))) ?_
        · exact Evaluates.call (by simp [Special])
            (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))
            (reuse_inference_call (by decide +kernel) (wellFormed_computes table value))
        · cases valid : Spec.WellFormed (signatureOf table) value with
          | false => simp only [List.all_cons, valid, Bool.false_and, boolean]; exact ⟨1, rfl⟩
          | true =>
              simp only [List.all_cons, valid, Bool.true_and, boolean]
              refine simultaneous_equation (equation := A[43])
                (environment := [("table", encodeTable table), ("rest", encodeReplacements rest)])
                (by decide +kernel) (by rfl) (by rfl) ?_
              exact Evaluates.call (by simp [Special])
                (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) ih

theorem theorem_computes (table : SignatureTable) (replacements : List (Spec.SymId × Spec.Term))
    (source : Spec.Term) :
    Applies P H "vibe:thm-instantiate-many" [encodeTable table, encodeReplacements replacements, encode source]
      (encodeResult (if replacements.all (fun pair => Spec.WellFormed (signatureOf table) pair.2) then
        Spec.SimultaneousInstantiation.statement (signatureOf table) replacements source else none)) := by
  refine simultaneous_equation (equation := A[44])
    (environment := [("table", encodeTable table), ("replacements", encodeReplacements replacements),
      ("statement", encode source)]) (by decide +kernel) (by rfl) (by rfl) ?_
  refine Evaluates.call (values := [boolean (replacements.all fun pair => Spec.WellFormed (signatureOf table) pair.2),
      encodeTable table, encodeReplacements replacements, encode source]) (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))) ?_
  · exact Evaluates.call (by simp [Special])
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) (formed_computes table replacements)
  · cases formed : replacements.all (fun pair => Spec.WellFormed (signatureOf table) pair.2) with
    | false => simp only [Bool.false_eq_true, if_false, boolean]; exact ⟨1, rfl⟩
    | true =>
        simp only [if_true, boolean]
        refine simultaneous_equation (equation := A[46])
          (environment := [("table", encodeTable table), ("replacements", encodeReplacements replacements),
            ("statement", encode source)]) (by decide +kernel) (by rfl) (by rfl) ?_
        exact Evaluates.call (by simp [Special])
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))
          (statement_computes table replacements source)

theorem statement_result_exact (table : SignatureTable) (replacements : List (Spec.SymId × Spec.Term))
    (source : Spec.Term) (result : Term) :
    Applies P H "vibe:instantiate-many" [encodeTable table, encodeReplacements replacements, encode source] result ↔
      result = encodeResult (Spec.SimultaneousInstantiation.statement (signatureOf table) replacements source) := by
  constructor
  · intro computed
    exact computed.deterministic (statement_computes table replacements source)
  · rintro rfl
    exact statement_computes table replacements source

theorem statement_accepts_iff (table : SignatureTable) (replacements : List (Spec.SymId × Spec.Term))
    (source result : Spec.Term) :
    Applies P H "vibe:instantiate-many" [encodeTable table, encodeReplacements replacements, encode source]
      (encodeResult (some result)) ↔
      Spec.SimultaneousInstantiation.statement (signatureOf table) replacements source = some result := by
  rw [statement_result_exact]
  exact ⟨fun same => (encodeResult_injective same).symm,
    fun same => by rw [same]⟩

theorem statement_completed_exact (table : SignatureTable) (replacements : List (Spec.SymId × Spec.Term))
    (source : Spec.Term) (fuel : Nat)
    (finished : apply P H fuel "vibe:instantiate-many"
      [encodeTable table, encodeReplacements replacements, encode source] ≠ .exhausted) :
    apply P H fuel "vibe:instantiate-many" [encodeTable table, encodeReplacements replacements, encode source] =
      .value (encodeResult (Spec.SimultaneousInstantiation.statement (signatureOf table) replacements source)) :=
  (statement_computes table replacements source).completed fuel finished

theorem theorem_accepts_iff (table : SignatureTable) (replacements : List (Spec.SymId × Spec.Term))
    (source result : Spec.Term) :
    Applies P H "vibe:thm-instantiate-many" [encodeTable table, encodeReplacements replacements, encode source]
      (encodeResult (some result)) ↔
      (∀ pair ∈ replacements, Spec.WellFormed (signatureOf table) pair.2 = true) ∧
        Spec.SimultaneousInstantiation.statement (signatureOf table) replacements source = some result := by
  constructor
  · intro computed
    have same := encodeResult_injective (computed.deterministic (theorem_computes table replacements source))
    cases formed : replacements.all (fun pair => Spec.WellFormed (signatureOf table) pair.2) with
    | false => simp [formed] at same
    | true => exact ⟨List.all_eq_true.mp formed, by simpa only [formed, if_true] using same.symm⟩
  · rintro ⟨formed, accepted⟩
    have allFormed := List.all_eq_true.mpr formed
    simpa only [allFormed, if_true, accepted] using theorem_computes table replacements source

/-- The authored operation realizes the actual simultaneous inference rule,
with a supplied source derivation and an explicit signature reading. -/
theorem theorem_derives {theory : Spec.Theory} (table : SignatureTable)
    (signature : theory.sig = signatureOf table) (replacements : List (Spec.SymId × Spec.Term))
    {source result : Spec.Term} (derived : Spec.DerivesV2 theory source)
    (computed : Applies P H "vibe:thm-instantiate-many"
      [encodeTable table, encodeReplacements replacements, encode source] (encodeResult (some result))) :
    Spec.DerivesV2 theory result := by
  obtain ⟨formed, accepted⟩ := (theorem_accepts_iff table replacements source result).mp computed
  exact .instantiateMany derived (by simpa only [signature] using formed)
    (by simpa only [signature] using accepted)

#print axioms go_computes
#print axioms argumentList_computes
#print axioms statement_computes
#print axioms theorem_computes
#print axioms theorem_derives

end Mettapedia.Languages.VibeITP.Presentation.ComputationalSimultaneous
