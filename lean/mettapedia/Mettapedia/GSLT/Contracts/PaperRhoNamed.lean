import Mettapedia.GSLT.Contracts.PaperRhoAdequacy
import Mettapedia.OSLF.MeTTaIL.ReflectiveContextualQuote

/-!
# Named binders and the dynamic quote

Meredith and Radestock (2005, §2.6) apply `{u/z}` to `w|y[z]|` and to `w[@(y[z])]`.
The first gives `w|y[u]|`; the second is unchanged, "because the body of the
process between quotes is impervious to substitution". The locally nameless
comparator `PaperRho` cannot state this, since its quotations hold closed code.
This module adds the paper's syntax with named binders and compares the freeze
view of our calculus with the paper's substitution.

## Names

A name is a quoted process (`NName.quote`), as in the 2005 grammar, which has no
production for atomic names.

* The paper's names are global. Every name is the code of a closed process, and
  name equivalence compares codes. An input `x(y).P` binds the names equivalent
  to `y`; a binder spelled `@(*w)` binds `w`. Atomic name variables cannot
  express such a binder, and freezing a binder to an atom would hide its code
  from name equivalence and from the channel test of COMM.
* So the freeze view writes a pattern, not a string: its binder parameter is a
  `Pattern` name, of which `.fvar binder` is one instance.
* A drop of the eliminated binder receives the frozen name like any substituted
  value, and receiving a quotation runs its code. The frozen name of a binder
  whose closed reading is `ŷ` is therefore `@(*ŷ)` (`frozen`): by quote-drop it
  is the name `ŷ`, and receiving it is the drop `*ŷ`. This is the paper's own
  identity `P{@(*z)/y} ≡ P{z/y}` (p. 58, `output_sugar`). With the bare spelling
  `@P`, the drop of the binder inside a quotation runs `P`
  (`Controls.dynamicQuote_bare_spelling_differs`).

## Readings

`readProcess` reads named syntax into the syntax of `PaperRho`. An occurrence of
a binder is a name equivalent to the closed reading of the binder's name, decided
by the paper's name equivalence, innermost binder first (`lookup`). Each binder
records whether it reaches into quotations.

* `literal`: no binder reaches into a quotation. This is the paper's reading, and
  its quotations are closed, as in `PaperRho`.
* `bindingAware`: every binder reaches into quotations. This is how our calculus
  represents the term.

The two encodings into our patterns are `encodeProcess ∘ literal` and
`encodeProcess ∘ bindingAware`. A reading never produces a whole-name spelling of
a binder index (`readName_quote_no_alias`).

## Results

* `canonicalize_freezeView`: for every scoped locally nameless body under any
  number of binders inside the eliminated one, the freeze view writing
  `@(*ŷ)` has the canonical form of the paper's substitution applied to the body
  whose quoted occurrences of the binder are written `@(*ŷ)` (`freezeProcess`).
* `readProcess_frozen`: the paper's reading is that frozen reading, up to the
  paper's congruence.
* `freezeView_matches_paper`: eliminating `y` of `x(y).P` with the freeze view, on
  the reading in which `y` reaches into quotations, gives the paper's
  substitution `P{@Q/y}` on the paper's reading, up to the equations.
  `freezeView_bindingAware` states the same for the binding-aware reading when no
  binder of `P` occurs inside a quotation of `P`.
* The agreement is up to the equations. On the §2.6 example it is exact
  (`Controls.dynamicQuote_freeze`). At a subject position the freeze view writes
  `@(*z)` where the paper keeps `z` (`Controls.quotedSubject_up_to_equations`).
* On the §2.6 example the apply and closure views differ from the paper
  (`Controls.dynamicQuote_apply_differs`, `Controls.dynamicQuote_closure_differs`),
  and `instantiate` leaves the binder dangling. On the lifted body all agree
  (`Controls.liftedBody_all_agree`).
* Obstruction: when an inner binder of `P` occurs inside a quotation of `P`, the
  binding-aware reading keeps it bound there, and the freeze view, which
  eliminates only the outer binder, differs from the paper even up to the
  equations (`Controls.innerBinder_obstruction`). The binding-aware reading does
  not respect the paper's α-equivalence, whose renaming never enters a quotation
  (`Controls.bindingAware_not_alpha_invariant`).
* On the paper's reading the body is sealed and every declared view is
  `instantiate`, which keeps quotations opaque (`literalBody_sealed`,
  `literalBody_views_coincide`). This agrees with `PaperRhoAdequacy`, whose
  substitution never enters a quotation. `PaperRhoAdequacyLiteral` states
  exactly when `instantiate` on this reading is the paper's substitution
  spelling for spelling, and connects the reading to the steps of our calculus.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.PaperRho.Named

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.ReflectiveContextualQuote
open Mettapedia.OSLF.MeTTaIL.ReflectiveQuoteAdmission (mentions mentionsList mentionsList_eq_false_iff)
open Mettapedia.OSLF.MeTTaIL.ReflectiveCoherent (finish_long finish_not_quote finish_quote_drop
  finish_cases canonicalize_parallel_eq
  canonicalize_substituteViewed_canonical_parallel canonicalize_substituteViewed_resolveQuotes)
open Mettapedia.GSLT.Contracts.PaperRho.PatternBoundary
open Mettapedia.GSLT.Contracts.PaperRho.Adequacy
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars_eq_self_of_isWellScopedAt)
open Mettapedia.OSLF.MeTTaIL.ScopedPattern (binderSafeAt binderSafeListAt)
open Mettapedia.OSLF.MeTTaIL.ReflectiveInstantiation (instantiate resolveQuotes_binderSafeAt)

/-! ## The paper's syntax with named binders -/

mutual
  /-- A name of the 2005 calculus: a quoted process. -/
  inductive NName where
    | quote (code : NProc)
  /-- A process of the 2005 calculus. An input binds a name. -/
  inductive NProc where
    | zero
    | par (left right : NProc)
    | send (subject : NName) (payload : NProc)
    | receive (subject binder : NName) (body : NProc)
    | drop (name : NName)
end

/-- A binder in scope: the closed reading of its name, and whether it binds
occurrences inside quotations. -/
structure Binder where
  name : Name
  reaches : Bool

open Classical in
/-- The innermost visible binder whose name is name-equivalent to `n`; `none`
marks a binder that is not visible at this position. -/
noncomputable def lookup (n : Name) : List (Option Binder) → Option Nat
  | [] => none
  | none :: scope => (lookup n scope).map Nat.succ
  | some binder :: scope =>
      if NameEquivalence n binder.name then some 0 else (lookup n scope).map Nat.succ

/-- Inside a quotation only the binders that reach into quotations are visible. -/
def enterQuote (scope : List (Option Binder)) : List (Option Binder) :=
  scope.map fun entry => entry.bind fun binder => if binder.reaches then some binder else none

mutual
  /-- Read a name. A name that is name-equivalent to a visible binder is that
  binder's index; any other name is a quotation, whose code is read with the
  binders that reach into quotations. Binders introduced on the way reach into
  quotations exactly when `reaches` holds. -/
  noncomputable def readName (reaches : Bool) (scope : List (Option Binder)) : NName → Name
    | .quote code =>
        match lookup (.quote (readProcess false [] code)) scope with
        | some index => .bound index
        | none => .quote (readProcess reaches (enterQuote scope) code)

  /-- Read a process. -/
  noncomputable def readProcess (reaches : Bool) (scope : List (Option Binder)) : NProc → Process
    | .zero => .zero
    | .par left right => .par (readProcess reaches scope left) (readProcess reaches scope right)
    | .send subject payload =>
        .send (readName reaches scope subject) (readProcess reaches scope payload)
    | .receive subject binder body =>
        .receive (readName reaches scope subject)
          (readProcess reaches (some ⟨readName false [] binder, reaches⟩ :: scope) body)
    | .drop name => .drop (readName reaches scope name)
end

/-- The closed reading of a name, its identity in the paper's global name space. -/
noncomputable def closedName (n : NName) : Name := readName false [] n

/-- **The paper's reading.** No binder reaches into a quotation: the body of a
quotation is impervious to substitution. -/
noncomputable def literal (p : NProc) : Process := readProcess false [] p

/-- **The reading of our calculus.** Every binder reaches into quotations: an
occurrence of a binder's name inside a quotation is the bound index. -/
noncomputable def bindingAware (p : NProc) : Process := readProcess true [] p

/-! ## Facts about the readings -/

theorem lookup_append (n : Name) (front back : List (Option Binder)) :
    lookup n (front ++ back) = (lookup n front).or ((lookup n back).map (· + front.length)) := by
  induction front with
  | nil => simp [lookup]
  | cons entry front ih =>
      cases entry with
      | none =>
          simp only [List.cons_append, lookup, ih, List.length_cons]
          cases lookup n front <;> cases lookup n back <;> simp [Nat.add_assoc]
      | some binder =>
          simp only [List.cons_append, lookup, List.length_cons]
          split
          · rfl
          · rw [ih]
            cases lookup n front <;> cases lookup n back <;> simp [Nat.add_assoc]

theorem lookup_none_entries (n : Name) (count : Nat) :
    lookup n (List.replicate count none) = none := by
  induction count with
  | zero => rfl
  | succ count ih => simp [List.replicate_succ, lookup, ih]

theorem lookup_spec {n : Name} : ∀ {scope : List (Option Binder)} {index : Nat},
    lookup n scope = some index →
      ∃ binder, scope[index]? = some (some binder) ∧ NameEquivalence n binder.name
  | [], _, found => by cases found
  | none :: scope, index, found => by
      simp only [lookup, Option.map_eq_some_iff] at found
      obtain ⟨inner, innerFound, rfl⟩ := found
      obtain ⟨binder, at_, same⟩ := lookup_spec innerFound
      exact ⟨binder, by simpa using at_, same⟩
  | some binder :: scope, index, found => by
      simp only [lookup] at found
      split at found
      · cases found
        exact ⟨binder, rfl, by assumption⟩
      · simp only [Option.map_eq_some_iff] at found
        obtain ⟨inner, innerFound, rfl⟩ := found
        obtain ⟨binder', at_, same⟩ := lookup_spec innerFound
        exact ⟨binder', by simpa using at_, same⟩

theorem lookup_isSome {n : Name} : ∀ {scope : List (Option Binder)} {index : Nat} {binder : Binder},
    scope[index]? = some (some binder) → NameEquivalence n binder.name → (lookup n scope).isSome
  | [], _, _, at_, _ => by cases at_
  | entry :: scope, 0, binder, at_, same => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at at_
      subst at_
      simp [lookup, same]
  | none :: scope, index + 1, binder, at_, same => by
      simp only [List.getElem?_cons_succ] at at_
      simpa [lookup] using lookup_isSome at_ same
  | some first :: scope, index + 1, binder, at_, same => by
      simp only [List.getElem?_cons_succ] at at_
      simp only [lookup]
      split
      · rfl
      · simpa using lookup_isSome at_ same

theorem lookup_lt {n : Name} {scope : List (Option Binder)} {index : Nat}
    (found : lookup n scope = some index) : index < scope.length := by
  obtain ⟨_, at_, _⟩ := lookup_spec found
  exact (List.getElem?_eq_some_iff.mp at_).1

theorem enterQuote_append (front back : List (Option Binder)) :
    enterQuote (front ++ back) = enterQuote front ++ enterQuote back := by
  simp [enterQuote]

theorem enterQuote_length (scope : List (Option Binder)) : (enterQuote scope).length = scope.length := by
  simp [enterQuote]

theorem enterQuote_none_entries (count : Nat) :
    enterQuote (List.replicate count none) = List.replicate count none := by
  simp [enterQuote]

/-- Hidden binders at the outer end of a scope change no reading. -/
theorem lookup_pad (n : Name) (scope : List (Option Binder)) (count : Nat) :
    lookup n (scope ++ List.replicate count none) = lookup n scope := by
  rw [lookup_append, lookup_none_entries]
  cases lookup n scope <;> rfl

mutual
  theorem readName_pad (reaches : Bool) (count : Nat) :
      ∀ (scope : List (Option Binder)) (n : NName),
        readName reaches (scope ++ List.replicate count none) n = readName reaches scope n
    | scope, .quote code => by
        simp only [readName, lookup_pad, enterQuote_append, enterQuote_none_entries,
          readProcess_pad reaches count (enterQuote scope) code]

  theorem readProcess_pad (reaches : Bool) (count : Nat) :
      ∀ (scope : List (Option Binder)) (p : NProc),
        readProcess reaches (scope ++ List.replicate count none) p = readProcess reaches scope p
    | _, .zero => rfl
    | scope, .par left right => by
        simp only [readProcess, readProcess_pad reaches count scope left,
          readProcess_pad reaches count scope right]
    | scope, .send subject payload => by
        simp only [readProcess, readName_pad reaches count scope subject,
          readProcess_pad reaches count scope payload]
    | scope, .receive subject binder body => by
        have inner := readProcess_pad reaches count
          (some ⟨readName false [] binder, reaches⟩ :: scope) body
        simp only [List.cons_append] at inner
        simp only [readProcess, readName_pad reaches count scope subject, inner]
    | scope, .drop name => by simp only [readProcess, readName_pad reaches count scope name]
end

theorem readProcess_hidden (reaches : Bool) (count : Nat) (p : NProc) :
    readProcess reaches (List.replicate count none) p = readProcess reaches [] p := by
  simpa using readProcess_pad reaches count [] p

theorem closedName_quote (code : NProc) :
    closedName (.quote code) = .quote (readProcess false [] code) := rfl

mutual
  /-- Readings are scoped by their scope. -/
  theorem readName_scoped (reaches : Bool) :
      ∀ (scope : List (Option Binder)) (n : NName),
        (encodeName (readName reaches scope n)).isWellScopedAt scope.length = true
    | scope, .quote code => by
        simp only [readName]
        split
        · rename_i index found
          simpa [encodeName, Pattern.isWellScopedAt] using lookup_lt found
        · have inner := readProcess_scoped reaches (enterQuote scope) code
          rw [enterQuote_length] at inner
          simpa [encodeName, Pattern.isWellScopedAt, Pattern.isWellScopedListAt] using inner

  theorem readProcess_scoped (reaches : Bool) :
      ∀ (scope : List (Option Binder)) (p : NProc),
        (encodeProcess (readProcess reaches scope p)).isWellScopedAt scope.length = true
    | _, .zero => rfl
    | scope, .par left right => by
        have l := readProcess_scoped reaches scope left
        have r := readProcess_scoped reaches scope right
        simp [readProcess, encodeProcess, Pattern.isWellScopedAt, Pattern.isWellScopedListAt, l, r]
    | scope, .send subject payload => by
        have l := readName_scoped reaches scope subject
        have r := readProcess_scoped reaches scope payload
        simp [readProcess, encodeProcess, Pattern.isWellScopedAt, Pattern.isWellScopedListAt, l, r]
    | scope, .receive subject binder body => by
        have l := readName_scoped reaches scope subject
        have r := readProcess_scoped reaches (some ⟨readName false [] binder, reaches⟩ :: scope) body
        simp only [List.length_cons] at r
        simp [readProcess, encodeProcess, Pattern.isWellScopedAt, Pattern.isWellScopedListAt, l, r]
    | scope, .drop name => by
        have l := readName_scoped reaches scope name
        simp [readProcess, encodeProcess, Pattern.isWellScopedAt, Pattern.isWellScopedListAt, l]
end

private theorem combine_empty_iff (first second : BinderView) :
    first.combine second = .empty ↔ first = .empty ∧ second = .empty := by
  cases first <;> cases second <;> simp [BinderView.combine]

private theorem combine_single_iff (first second : BinderView) (index : Nat) :
    first.combine second = .singleDrop (some index) ↔
      (first = .empty ∧ second = .singleDrop (some index)) ∨
        (first = .singleDrop (some index) ∧ second = .empty) := by
  cases first <;> cases second <;> simp [BinderView.combine]

/-- A reading with no output, input or drop at its top level is congruent to
the unit, in every reading. -/
theorem congruence_zero_of_empty (reaches reaches' : Bool) :
    ∀ (scope scope' : List (Option Binder)) (p : NProc),
      binderView (readProcess reaches scope p) = .empty →
        Congruence (readProcess reaches' scope' p) .zero
  | _, _, .zero, _ => .refl _
  | scope, scope', .par left right, empty => by
      simp only [readProcess, binderView] at empty
      obtain ⟨leftEmpty, rightEmpty⟩ := (combine_empty_iff _ _).mp empty
      exact .trans (.par (congruence_zero_of_empty reaches reaches' scope scope' left leftEmpty)
        (congruence_zero_of_empty reaches reaches' scope scope' right rightEmpty)) (.unit _)
  | _, _, .send _ _, empty | _, _, .receive _ _ _, empty | _, _, .drop _, empty => by
      simp [readProcess, binderView] at empty

private theorem enterQuote_entry {scope : List (Option Binder)} {index : Nat} {binder : Binder}
    (at_ : (enterQuote scope)[index]? = some (some binder)) :
    scope[index]? = some (some binder) ∧ binder.reaches = true := by
  simp only [enterQuote, List.getElem?_map, Option.map_eq_some_iff] at at_
  obtain ⟨entry, entryAt, bound⟩ := at_
  cases entry with
  | none => simp at bound
  | some original =>
      simp only [Option.bind_some] at bound
      split at bound
      · cases bound
        exact ⟨entryAt, by assumption⟩
      · cases bound

mutual
  /-- **A reading that is a whole-name spelling of a binder index denotes that
  binder.** -/
  theorem readName_binderIndex (reaches : Bool) :
      ∀ (scope : List (Option Binder)) (n : NName) (index : Nat),
        binderIndex (readName reaches scope n) = some index →
          ∃ binder, scope[index]? = some (some binder) ∧
            NameEquivalence (closedName n) binder.name
    | scope, .quote code, index, hit => by
        simp only [readName] at hit
        split at hit
        · rename_i found_index found
          simp only [binderIndex, Option.some.injEq] at hit
          subst hit
          exact lookup_spec found
        · simp only [binderIndex] at hit
          split at hit
          · rename_i view viewEq
            subst hit
            obtain ⟨binder, at_, same⟩ :=
              readProcess_singleDrop reaches (enterQuote scope) code index viewEq
            exact ⟨binder, (enterQuote_entry at_).1,
              .trans (.quote same) (.quote_drop binder.name)⟩
          · cases hit

  theorem readProcess_singleDrop (reaches : Bool) :
      ∀ (scope : List (Option Binder)) (p : NProc) (index : Nat),
        binderView (readProcess reaches scope p) = .singleDrop (some index) →
          ∃ binder, scope[index]? = some (some binder) ∧
            Congruence (readProcess false [] p) (.drop binder.name)
    | _, .zero, _, view => by simp [readProcess, binderView] at view
    | scope, .par left right, index, view => by
        simp only [readProcess, binderView] at view
        rcases (combine_single_iff _ _ index).mp view with ⟨leftEmpty, rightHit⟩ | ⟨leftHit, rightEmpty⟩
        · obtain ⟨binder, at_, same⟩ := readProcess_singleDrop reaches scope right index rightHit
          refine ⟨binder, at_, ?_⟩
          simp only [readProcess]
          exact .trans (.par (congruence_zero_of_empty reaches false scope [] left leftEmpty) same)
            (.trans (.swap _ _) (.unit _))
        · obtain ⟨binder, at_, same⟩ := readProcess_singleDrop reaches scope left index leftHit
          refine ⟨binder, at_, ?_⟩
          simp only [readProcess]
          exact .trans (.par same (congruence_zero_of_empty reaches false scope [] right rightEmpty))
            (.unit _)
    | _, .send _ _, _, view | _, .receive _ _ _, _, view => by simp [readProcess, binderView] at view
    | scope, .drop name, index, view => by
        simp only [readProcess, binderView, BinderView.singleDrop.injEq] at view
        obtain ⟨binder, at_, same⟩ := readName_binderIndex reaches scope name index view
        exact ⟨binder, at_, .drop same⟩
end

/-- **Readings never produce a whole-name alias**: a quotation that a reading
keeps is not a spelling of a binder index. -/
theorem readName_quote_no_alias {reaches : Bool} {scope : List (Option Binder)} {n : NName}
    {code : Process} (kept : readName reaches scope n = .quote code) (index : Nat) :
    binderIndex (.quote code) ≠ some index := by
  intro hit
  rw [← kept] at hit
  obtain ⟨binder, at_, same⟩ := readName_binderIndex reaches scope n index hit
  have found := lookup_isSome at_ same
  cases n with
  | quote original =>
      simp only [readName] at kept
      rw [closedName_quote] at found
      split at kept
      · cases kept
      · rename_i missed
        rw [missed] at found
        cases found

/-! ## Freezing the eliminated binder inside quotations, on the paper's side -/

mutual
  /-- Write the binder at `depth`, inside quotations, as the name `@(*spelling)`.
  Outside quotations (`inside = false`) a whole-name occurrence is kept. -/
  def freezeName (spelling : Name) (inside : Bool) (depth : Nat) : Name → Name
    | .bound index => if inside ∧ index = depth then .quote (.drop spelling) else .bound index
    | .quote code =>
        if binderIndex (.quote code) = some depth then
          (if inside then .quote (.drop spelling) else .quote code)
        else .quote (freezeProcess spelling true depth code)

  /-- `freezeName` on every name of a process. -/
  def freezeProcess (spelling : Name) (inside : Bool) (depth : Nat) : Process → Process
    | .zero => .zero
    | .par left right =>
        .par (freezeProcess spelling inside depth left) (freezeProcess spelling inside depth right)
    | .send subject payload =>
        .send (freezeName spelling inside depth subject) (freezeProcess spelling inside depth payload)
    | .receive subject body =>
        .receive (freezeName spelling inside depth subject)
          (freezeProcess spelling inside (depth + 1) body)
    | .drop name => .drop (freezeName spelling inside depth name)
end

/-- Relabel a binder view after freezing the binder at `depth`. -/
def relabel (depth : Nat) : BinderView → BinderView
  | .singleDrop (some index) => if index = depth then .singleDrop none else .singleDrop (some index)
  | view => view

private theorem combine_empty_right (view : BinderView) : view.combine .empty = view := by
  cases view <;> rfl

private theorem combine_of_ne_empty {first second : BinderView} (firstFull : first ≠ .empty)
    (secondFull : second ≠ .empty) : first.combine second = .other := by
  cases first <;> cases second <;> first | rfl | exact absurd rfl firstFull | exact absurd rfl secondFull

private theorem relabel_ne_empty (depth : Nat) {view : BinderView} (full : view ≠ .empty) :
    relabel depth view ≠ .empty := by
  rcases view with _ | ⟨_ | index⟩ | _
  · exact absurd rfl full
  · simp [relabel]
  · simp only [relabel]; split <;> simp
  · simp [relabel]

private theorem relabel_combine (depth : Nat) (first second : BinderView) :
    relabel depth (first.combine second) = (relabel depth first).combine (relabel depth second) := by
  by_cases firstEmpty : first = .empty
  · subst firstEmpty; rfl
  by_cases secondEmpty : second = .empty
  · subst secondEmpty
    rw [combine_empty_right, show relabel depth .empty = .empty from rfl, combine_empty_right]
  rw [combine_of_ne_empty firstEmpty secondEmpty,
    combine_of_ne_empty (relabel_ne_empty depth firstEmpty) (relabel_ne_empty depth secondEmpty)]
  rfl

mutual
  theorem binderIndex_freezeName {spelling : Name} (spellingMiss : binderIndex spelling = none)
      (depth : Nat) : ∀ n : Name,
      binderIndex (freezeName spelling true depth n) =
        if binderIndex n = some depth then none else binderIndex n
    | .bound index => by
        by_cases hit : index = depth
        · subst hit
          simp [freezeName, binderIndex, binderView, spellingMiss]
        · simp [freezeName, binderIndex, hit]
    | .quote code => by
        by_cases hit : binderIndex (.quote code) = some depth
        · rw [if_pos hit]
          have frozen : freezeName spelling true depth (.quote code) = .quote (.drop spelling) := by
            simp only [freezeName, hit, if_true]
          rw [frozen]
          simp [binderIndex, binderView, spellingMiss]
        · rw [if_neg hit]
          simp only [freezeName, if_neg hit]
          simp only [binderIndex, binderView_freezeProcess spellingMiss depth code]
          generalize viewEq : binderView code = view
          rw [binderIndex, viewEq] at hit
          rcases view with _ | ⟨_ | i⟩ | _ <;> simp_all [relabel]

  theorem binderView_freezeProcess {spelling : Name} (spellingMiss : binderIndex spelling = none)
      (depth : Nat) : ∀ code : Process,
      binderView (freezeProcess spelling true depth code) = relabel depth (binderView code)
    | .zero => rfl
    | .par left right => by
        simp only [freezeProcess, binderView, binderView_freezeProcess spellingMiss depth left,
          binderView_freezeProcess spellingMiss depth right, relabel_combine]
    | .send _ _ | .receive _ _ => rfl
    | .drop name => by
        simp only [freezeProcess, binderView, binderIndex_freezeName spellingMiss depth name]
        cases binderIndex name with
        | none => rfl
        | some index => by_cases same : index = depth <;> simp [relabel, same]
end

/-! ## The freeze view is the paper's substitution after freezing -/

/-- The quoted payload, the value of the eliminated binder. -/
def received (payload : Process) : Pattern := .apply "NQuote" [encodeProcess payload]

/-- The name the freeze view writes for the eliminated binder: `@(*spelling)`, the
encoding of `.quote (.drop spelling)`. -/
def frozen (spelling : Name) : Pattern := encodeName (.quote (.drop spelling))

section FreezeView

private theorem lowering_closed {value : Pattern} (closed : value.isWellScopedAt 0 = true)
    (level : Nat) : lowering value level level = value := by
  rw [lowering_self]
  exact liftBVars_eq_self_of_isWellScopedAt closed

private theorem canonicalize_two (constructor : String) (first second : Pattern) :
    canonicalize rhoReflectivePresentation (.apply constructor [first, second]) =
      .apply constructor [canonicalize rhoReflectivePresentation first,
        canonicalize rhoReflectivePresentation second] := by
  simp only [canonicalize, canonicalizeList, finish_long]

private theorem canonicalize_dropPattern (name : Pattern) :
    canonicalize rhoReflectivePresentation (.apply "PDrop" [name]) =
      .apply "PDrop" [canonicalize rhoReflectivePresentation name] := by
  simp only [canonicalize, canonicalizeList]
  exact finish_not_quote (by decide) _

private theorem canonicalize_quotePattern (code : Pattern) :
    canonicalize rhoReflectivePresentation (.apply "NQuote" [code]) =
      finishNormalizeReflectiveApply rhoReflectivePresentation "NQuote"
        [canonicalize rhoReflectivePresentation code] := by
  simp only [canonicalize, canonicalizeList]

private theorem finish_quote_dropPattern (name : Pattern) :
    finishNormalizeReflectiveApply rhoReflectivePresentation "NQuote" [.apply "PDrop" [name]] =
      name := by
  simp [finishNormalizeReflectiveApply, rhoReflectivePresentation]

private theorem receive_quote (code : Pattern) :
    receive rhoReflectivePresentation "PDrop" (.apply "NQuote" [code]) = code := by
  simp [receive, rhoReflectivePresentation]

private theorem canonicalize_frozen (spelling : Name) :
    canonicalize rhoReflectivePresentation (frozen spelling) =
      canonicalize rhoReflectivePresentation (encodeName spelling) := by
  change canonicalize rhoReflectivePresentation
    (.apply "NQuote" [.apply "PDrop" [encodeName spelling]]) = _
  rw [canonicalize_quotePattern, canonicalize_dropPattern, finish_quote_dropPattern]

private theorem substituteViewed_bvar (inside act : Nat → Nat → Pattern) (depth index : Nat) :
    substituteViewed rhoReflectivePresentation inside act depth (.bvar index) = act depth index := by
  simp [substituteViewed]

private theorem substituteViewed_zero (inside act : Nat → Nat → Pattern) (depth : Nat) :
    substituteViewed rhoReflectivePresentation inside act depth (.apply "PZero" []) =
      .apply "PZero" [] := by
  simp [substituteViewed]

private theorem substituteViewed_quote (inside act : Nat → Nat → Pattern) (depth : Nat)
    (code : Pattern) :
    substituteViewed rhoReflectivePresentation inside act depth (.apply "NQuote" [code]) =
      .apply "NQuote" [substituteViewed rhoReflectivePresentation inside inside depth code] := by
  simp [substituteViewed, rhoReflectivePresentation]

private theorem substituteViewed_drop (inside act : Nat → Nat → Pattern) (depth : Nat)
    (name : Pattern) :
    substituteViewed rhoReflectivePresentation inside act depth (.apply "PDrop" [name]) =
      if matchesBinder rhoReflectivePresentation depth name then
        receive rhoReflectivePresentation "PDrop" (act depth depth)
      else .apply "PDrop" [substituteViewed rhoReflectivePresentation inside act depth name] := by
  simp [substituteViewed, rhoReflectivePresentation]

private theorem substituteViewed_two (inside act : Nat → Nat → Pattern) (depth : Nat)
    (constructor : String) (first second : Pattern) :
    substituteViewed rhoReflectivePresentation inside act depth (.apply constructor [first, second]) =
      .apply constructor [substituteViewed rhoReflectivePresentation inside act depth first,
        substituteViewed rhoReflectivePresentation inside act depth second] := by
  simp [substituteViewed, substituteViewedList]

private theorem substituteViewed_lambda (inside act : Nat → Nat → Pattern) (depth : Nat)
    (body : Pattern) :
    substituteViewed rhoReflectivePresentation inside act depth (.lambda none body) =
      .lambda none (substituteViewed rhoReflectivePresentation inside act (depth + 1) body) := by
  simp [substituteViewed]

private theorem bound_below {index depth : Nat} {pattern : Pattern}
    (same : canonicalize rhoReflectivePresentation pattern = .bvar index)
    (inScope : pattern.isWellScopedAt (depth + 1) = true) : index < depth + 1 := by
  have canonicalScoped := canonicalize_scoped rhoReflectivePresentation inScope
  rw [same] at canonicalScoped
  simpa [Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.isWellScopedAt] using canonicalScoped

/-- A name that is not a whole-name spelling of a binder index: the traversal
enters its quotation, whatever the outside action. -/
private theorem canonicalize_substituteViewed_quoteName {inside act : Nat → Nat → Pattern}
    {depth : Nat} {code : Process} (miss : binderIndex (.quote code) = none) :
    canonicalize rhoReflectivePresentation
        (substituteViewed rhoReflectivePresentation inside act depth
          (canonicalize rhoReflectivePresentation (encodeName (.quote code)))) =
      finishNormalizeReflectiveApply rhoReflectivePresentation "NQuote"
        [canonicalize rhoReflectivePresentation
          (substituteViewed rhoReflectivePresentation inside inside depth (canonicalForm code))] := by
  have notBound : ∀ index,
      canonicalize rhoReflectivePresentation (encodeName (.quote code)) ≠ .bvar index :=
    fun index same => by
      rw [canonicalize_encodeName_eq_bvar_iff, miss] at same
      cases same
  rw [canonicalize_quote]
  rcases finish_cases (declaration := rhoReflectivePresentation) "NQuote" [canonicalForm code] with
    plain | ⟨name, _, single, collapsed⟩
  · rw [plain, substituteViewed_quote, canonicalize_quotePattern]
  · rw [collapsed]
    have dropShape : canonicalForm code = .apply "PDrop" [name] := (List.cons.inj single).1
    have nameIsCanonical : canonicalize rhoReflectivePresentation (encodeName (.quote code)) =
        name := by
      rw [canonicalize_quote]; exact collapsed
    rcases canonicalize_encodeName_shape (.quote code) with ⟨index, bound⟩ | ⟨inner, quoted⟩
    · exact absurd bound (notBound index)
    · rw [nameIsCanonical] at quoted
      subst quoted
      have miss' : matchesBinder rhoReflectivePresentation depth (.apply "NQuote" [inner]) = false := by
        rw [Bool.eq_false_iff]
        intro hit
        rw [← nameIsCanonical, matchesBinder_canonicalize_encodeName, miss] at hit
        cases hit
      rw [dropShape, substituteViewed_quote, substituteViewed_drop, miss', if_neg (by simp),
        substituteViewed_quote, canonicalize_dropPattern, finish_quote_dropPattern]

private theorem freezeName_hit {spelling : Name} {depth : Nat} {n : Name}
    (hit : binderIndex n = some depth) :
    freezeName spelling true depth n = .quote (.drop spelling) := by
  cases n with
  | bound index =>
      simp only [binderIndex, Option.some.injEq] at hit
      simp [freezeName, hit]
  | quote code => simp only [freezeName, hit, if_true]

private theorem freezeName_quote_miss {spelling : Name} {inside : Bool} {depth : Nat}
    {code : Process} (miss : binderIndex (.quote code) ≠ some depth) :
    freezeName spelling inside depth (.quote code) = .quote (freezeProcess spelling true depth code) := by
  simp only [freezeName, if_neg miss]

private theorem scoped_send {depth : Nat} {n : Name} {p : Process}
    (inScope : (encodeProcess (.send n p)).isWellScopedAt depth = true) :
    (encodeName n).isWellScopedAt depth = true ∧ (encodeProcess p).isWellScopedAt depth = true := by
  simpa [encodeProcess, Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.isWellScopedAt,
    Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.isWellScopedListAt] using inScope

private theorem scoped_receive {depth : Nat} {n : Name} {p : Process}
    (inScope : (encodeProcess (.receive n p)).isWellScopedAt depth = true) :
    (encodeName n).isWellScopedAt depth = true ∧
      (encodeProcess p).isWellScopedAt (depth + 1) = true := by
  simpa [encodeProcess, Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.isWellScopedAt,
    Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.isWellScopedListAt] using inScope

private theorem scoped_par {depth : Nat} {p q : Process}
    (inScope : (encodeProcess (.par p q)).isWellScopedAt depth = true) :
    (encodeProcess p).isWellScopedAt depth = true ∧ (encodeProcess q).isWellScopedAt depth = true := by
  simpa [encodeProcess, Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.isWellScopedAt,
    Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.isWellScopedListAt] using inScope

private theorem scoped_drop {depth : Nat} {n : Name}
    (inScope : (encodeProcess (.drop n)).isWellScopedAt depth = true) :
    (encodeName n).isWellScopedAt depth = true := by
  simpa [encodeProcess, Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.isWellScopedAt,
    Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.isWellScopedListAt] using inScope

private theorem scoped_quote {depth : Nat} {code : Process}
    (inScope : (encodeName (.quote code)).isWellScopedAt depth = true) :
    (encodeProcess code).isWellScopedAt depth = true := by
  simpa [encodeName, Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.isWellScopedAt,
    Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.isWellScopedListAt] using inScope

private theorem canonicalForm_par_parts (p q : Process) :
    canonicalForm (.par p q) = canonicalize rhoReflectivePresentation
      (.collection rhoReflectivePresentation.toReflectivePresentationDecl.parallelCollection
        [encodeProcess p, encodeProcess q] none) := rfl

variable {spelling : Name}

mutual
  /-- Inside a quotation, the freeze view writes `@(*spelling)` for the binder. -/
  theorem canonicalize_freezeInside_name (frozenClosed : (frozen spelling).isWellScopedAt 0 = true)
      (spellingMiss : binderIndex spelling = none) :
      ∀ (n : Name) (depth : Nat), (encodeName n).isWellScopedAt (depth + 1) = true →
        canonicalize rhoReflectivePresentation
            (substituteViewed rhoReflectivePresentation (lowering (frozen spelling))
              (lowering (frozen spelling)) depth (canonicalize rhoReflectivePresentation (encodeName n))) =
          canonicalize rhoReflectivePresentation (encodeName (freezeName spelling true depth n))
    | .bound index, depth, inScope => by
        have below : index < depth + 1 := bound_below (canonicalize_bound index) inScope
        rw [canonicalize_bound, substituteViewed_bvar]
        rcases Nat.lt_or_ge index depth with lower | upper
        · rw [lowering_of_lt lower]
          simp [freezeName, Nat.ne_of_lt lower, encodeName, canonicalize]
        · have same : index = depth := by omega
          subst same
          rw [lowering_closed frozenClosed]
          simp [freezeName, frozen]
    | .quote code, depth, inScope => by
        cases hb : binderIndex (.quote code) with
        | some index =>
            have bound := (canonicalize_encodeName_eq_bvar_iff (.quote code) index).mpr hb
            have below : index < depth + 1 := bound_below bound inScope
            rw [bound, substituteViewed_bvar]
            rcases Nat.lt_or_ge index depth with lower | upper
            · rw [lowering_of_lt lower]
              have kept := binderIndex_freezeName spellingMiss depth (.quote code)
              rw [hb, if_neg (by simp [Nat.ne_of_lt lower])] at kept
              exact ((canonicalize_encodeName_eq_bvar_iff _ index).mpr kept).symm
            · have same : index = depth := by omega
              subst same
              rw [lowering_closed frozenClosed, freezeName_hit hb]
              rfl
        | none =>
            rw [canonicalize_substituteViewed_quoteName hb,
              canonicalize_freezeInside frozenClosed spellingMiss code depth (scoped_quote inScope),
              freezeName_quote_miss (by rw [hb]; simp), canonicalize_quote]

  /-- Inside a quotation, the freeze view freezes every occurrence of the binder. -/
  theorem canonicalize_freezeInside (frozenClosed : (frozen spelling).isWellScopedAt 0 = true)
      (spellingMiss : binderIndex spelling = none) :
      ∀ (p : Process) (depth : Nat), (encodeProcess p).isWellScopedAt (depth + 1) = true →
        canonicalize rhoReflectivePresentation
            (substituteViewed rhoReflectivePresentation (lowering (frozen spelling))
              (lowering (frozen spelling)) depth (canonicalForm p)) =
          canonicalForm (freezeProcess spelling true depth p)
    | .zero, depth, _ => by
        rw [show canonicalForm .zero = _ from canonicalize_zero, substituteViewed_zero]
        simp only [freezeProcess]
        rw [show canonicalForm .zero = _ from canonicalize_zero]
        simp [canonicalize, canonicalizeList, finishNormalizeReflectiveApply,
          rhoReflectivePresentation]
    | .par a b, depth, inScope => by
        obtain ⟨aScoped, bScoped⟩ := scoped_par inScope
        rw [canonicalForm_par_parts, canonicalize_substituteViewed_canonical_parallel]
        simp only [List.map_cons, List.map_nil]
        rw [canonicalize_freezeInside frozenClosed spellingMiss a depth aScoped,
          canonicalize_freezeInside frozenClosed spellingMiss b depth bScoped]
        simp only [freezeProcess]
        exact (canonicalize_par _ _).symm
    | .send n p, depth, inScope => by
        obtain ⟨nScoped, pScoped⟩ := scoped_send inScope
        rw [show canonicalForm (.send n p) = _ from canonicalize_send n p, substituteViewed_two,
          canonicalize_two, canonicalize_freezeInside_name frozenClosed spellingMiss n depth nScoped,
          canonicalize_freezeInside frozenClosed spellingMiss p depth pScoped]
        simp only [freezeProcess]
        exact (canonicalize_send _ _).symm
    | .receive n p, depth, inScope => by
        obtain ⟨nScoped, pScoped⟩ := scoped_receive inScope
        rw [show canonicalForm (.receive n p) = _ from canonicalize_receive n p, substituteViewed_two,
          substituteViewed_lambda, canonicalize_two,
          canonicalize_freezeInside_name frozenClosed spellingMiss n depth nScoped]
        simp only [canonicalize]
        rw [canonicalize_freezeInside frozenClosed spellingMiss p (depth + 1) pScoped]
        simp only [freezeProcess]
        exact (canonicalize_receive _ _).symm
    | .drop n, depth, inScope => by
        have nScoped := scoped_drop inScope
        rw [show canonicalForm (.drop n) = _ from canonicalize_drop n, substituteViewed_drop]
        simp only [freezeProcess]
        rw [show canonicalForm (.drop _) = _ from canonicalize_drop _]
        by_cases hit : binderIndex n = some depth
        · rw [if_pos ((matchesBinder_canonicalize_encodeName depth n).mpr hit),
            lowering_closed frozenClosed, freezeName_hit hit]
          change canonicalize rhoReflectivePresentation
              (receive rhoReflectivePresentation "PDrop"
                (.apply "NQuote" [.apply "PDrop" [encodeName spelling]])) = _
          rw [receive_quote, canonicalize_dropPattern]
          exact congrArg (fun name => Pattern.apply "PDrop" [name]) (canonicalize_frozen spelling).symm
        · rw [if_neg (fun matched => hit ((matchesBinder_canonicalize_encodeName depth n).mp matched)),
            canonicalize_dropPattern,
            canonicalize_freezeInside_name frozenClosed spellingMiss n depth nScoped]
end

private theorem freezeName_miss {spelling : Name} {inside : Bool} {depth : Nat} {n : Name}
    (miss : binderIndex n ≠ some depth) :
    freezeName spelling inside depth n = freezeName spelling true depth n := by
  cases n with
  | bound index =>
      have other : index ≠ depth := fun same => miss (by rw [same]; rfl)
      simp [freezeName, other]
  | quote code => rw [freezeName_quote_miss miss, freezeName_quote_miss miss]

private theorem freezeName_outside_hit {spelling : Name} {depth : Nat} {n : Name}
    (hit : binderIndex n = some depth) : freezeName spelling false depth n = n := by
  cases n with
  | bound index => simp [freezeName]
  | quote code => simp only [freezeName, hit, if_true, Bool.false_eq_true, if_false]

private theorem binderIndex_freezeName_miss {spelling : Name} (spellingMiss : binderIndex spelling = none)
    {inside : Bool} {depth : Nat} {n : Name} (miss : binderIndex n ≠ some depth) :
    binderIndex (freezeName spelling inside depth n) = binderIndex n := by
  rw [freezeName_miss miss, binderIndex_freezeName spellingMiss depth n, if_neg miss]

private theorem bindName_miss {payload : Process} {depth : Nat} {n : Name}
    (miss : binderIndex n ≠ some depth) : bindName payload depth n = n := by
  simp only [bindName, if_neg miss]

mutual
  /-- Outside quotations, the freeze view substitutes the quoted payload. -/
  theorem canonicalize_freezeOutside_name {payload : Process}
      (frozenClosed : (frozen spelling).isWellScopedAt 0 = true)
      (receivedClosed : (received payload).isWellScopedAt 0 = true)
      (spellingMiss : binderIndex spelling = none) :
      ∀ (n : Name) (depth : Nat), (encodeName n).isWellScopedAt (depth + 1) = true →
        canonicalize rhoReflectivePresentation
            (substituteViewed rhoReflectivePresentation (lowering (frozen spelling))
              (lowering (received payload)) depth
              (canonicalize rhoReflectivePresentation (encodeName n))) =
          canonicalize rhoReflectivePresentation
            (encodeName (bindName payload depth (freezeName spelling false depth n)))
    | .bound index, depth, inScope => by
        have below : index < depth + 1 := bound_below (canonicalize_bound index) inScope
        rw [canonicalize_bound, substituteViewed_bvar]
        rcases Nat.lt_or_ge index depth with lower | upper
        · rw [lowering_of_lt lower]
          simp [freezeName, bindName, binderIndex, Nat.ne_of_lt lower, encodeName, canonicalize]
        · have same : index = depth := by omega
          subst same
          rw [lowering_closed receivedClosed]
          simp [freezeName, bindName, binderIndex, received, encodeName]
    | .quote code, depth, inScope => by
        cases hb : binderIndex (.quote code) with
        | some index =>
            have bound := (canonicalize_encodeName_eq_bvar_iff (.quote code) index).mpr hb
            have below : index < depth + 1 := bound_below bound inScope
            rw [bound, substituteViewed_bvar]
            rcases Nat.lt_or_ge index depth with lower | upper
            · rw [lowering_of_lt lower]
              have miss : binderIndex (.quote code) ≠ some depth := by
                rw [hb]; simp [Nat.ne_of_lt lower]
              have kept := binderIndex_freezeName_miss spellingMiss (inside := false) miss
              rw [bindName_miss (by rw [kept]; exact miss)]
              rw [hb] at kept
              exact ((canonicalize_encodeName_eq_bvar_iff _ index).mpr kept).symm
            · have same : index = depth := by omega
              subst same
              rw [lowering_closed receivedClosed, freezeName_outside_hit hb]
              simp [bindName, hb, received, encodeName]
        | none =>
            have miss : binderIndex (.quote code) ≠ some depth := by rw [hb]; simp
            rw [canonicalize_substituteViewed_quoteName hb,
              canonicalize_freezeInside frozenClosed spellingMiss code depth (scoped_quote inScope),
              bindName_miss (by rw [binderIndex_freezeName_miss spellingMiss miss]; exact miss),
              freezeName_quote_miss miss, canonicalize_quote]

  /-- Outside quotations, the freeze view is the paper's substitution of the
  frozen body. -/
  theorem canonicalize_freezeOutside {payload : Process}
      (frozenClosed : (frozen spelling).isWellScopedAt 0 = true)
      (receivedClosed : (received payload).isWellScopedAt 0 = true)
      (spellingMiss : binderIndex spelling = none) :
      ∀ (p : Process) (depth : Nat), (encodeProcess p).isWellScopedAt (depth + 1) = true →
        canonicalize rhoReflectivePresentation
            (substituteViewed rhoReflectivePresentation (lowering (frozen spelling))
              (lowering (received payload)) depth (canonicalForm p)) =
          canonicalForm (substitute payload depth (freezeProcess spelling false depth p))
    | .zero, depth, _ => by
        rw [show canonicalForm .zero = _ from canonicalize_zero, substituteViewed_zero]
        simp only [freezeProcess, substitute]
        rw [show canonicalForm .zero = _ from canonicalize_zero]
        simp [canonicalize, canonicalizeList, finishNormalizeReflectiveApply,
          rhoReflectivePresentation]
    | .par a b, depth, inScope => by
        obtain ⟨aScoped, bScoped⟩ := scoped_par inScope
        rw [canonicalForm_par_parts, canonicalize_substituteViewed_canonical_parallel]
        simp only [List.map_cons, List.map_nil]
        rw [canonicalize_freezeOutside frozenClosed receivedClosed spellingMiss a depth aScoped,
          canonicalize_freezeOutside frozenClosed receivedClosed spellingMiss b depth bScoped]
        simp only [freezeProcess, substitute]
        exact (canonicalize_par _ _).symm
    | .send n p, depth, inScope => by
        obtain ⟨nScoped, pScoped⟩ := scoped_send inScope
        rw [show canonicalForm (.send n p) = _ from canonicalize_send n p, substituteViewed_two,
          canonicalize_two,
          canonicalize_freezeOutside_name frozenClosed receivedClosed spellingMiss n depth nScoped,
          canonicalize_freezeOutside frozenClosed receivedClosed spellingMiss p depth pScoped]
        simp only [freezeProcess, substitute]
        exact (canonicalize_send _ _).symm
    | .receive n p, depth, inScope => by
        obtain ⟨nScoped, pScoped⟩ := scoped_receive inScope
        rw [show canonicalForm (.receive n p) = _ from canonicalize_receive n p, substituteViewed_two,
          substituteViewed_lambda, canonicalize_two,
          canonicalize_freezeOutside_name frozenClosed receivedClosed spellingMiss n depth nScoped]
        simp only [canonicalize]
        rw [canonicalize_freezeOutside frozenClosed receivedClosed spellingMiss p (depth + 1) pScoped]
        simp only [freezeProcess, substitute]
        exact (canonicalize_receive _ _).symm
    | .drop n, depth, inScope => by
        have nScoped := scoped_drop inScope
        rw [show canonicalForm (.drop n) = _ from canonicalize_drop n, substituteViewed_drop]
        simp only [freezeProcess, substitute]
        by_cases hit : binderIndex n = some depth
        · rw [if_pos ((matchesBinder_canonicalize_encodeName depth n).mpr hit),
            lowering_closed receivedClosed, freezeName_outside_hit hit, if_pos hit]
          exact congrArg (canonicalize rhoReflectivePresentation) (receive_quote _)
        · rw [if_neg (fun matched => hit ((matchesBinder_canonicalize_encodeName depth n).mp matched)),
            if_neg (by rw [binderIndex_freezeName_miss spellingMiss hit]; exact hit),
            canonicalize_dropPattern,
            canonicalize_freezeOutside_name frozenClosed receivedClosed spellingMiss n depth nScoped,
            bindName_miss (by rw [binderIndex_freezeName_miss spellingMiss hit]; exact hit),
            show canonicalForm (.drop _) = _ from canonicalize_drop _]
end

/-- **The freeze view is the paper's substitution after freezing.** The body
sits under `depth` binders inside the eliminated one, which is its index
`depth`; the indices below it are kept. For every body scoped under
the eliminated binder, closed payload and closed spelling that is not a binder
alias, the freeze view writing `@(*spelling)` has the canonical form of the
paper's substitution at `depth` applied to the body in which every occurrence
of the binder inside a quotation is written `@(*spelling)`. -/
theorem canonicalize_freezeView {payload : Process} {body : Process} (depth : Nat)
    (payloadClosed : (encodeProcess payload).isWellScopedAt 0 = true)
    (spellingClosed : (encodeName spelling).isWellScopedAt 0 = true)
    (spellingMiss : binderIndex spelling = none)
    (inScope : (encodeProcess body).isWellScopedAt (depth + 1) = true) :
    canonicalize rhoReflectivePresentation
        (freezeView rhoReflectivePresentation depth (received payload) (frozen spelling)
          (encodeProcess body)) =
      canonicalForm (substitute payload depth (freezeProcess spelling false depth body)) := by
  have frozenClosed : (frozen spelling).isWellScopedAt 0 = true := by
    simpa [frozen, encodeName, encodeProcess, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt] using spellingClosed
  have receivedClosed : (received payload).isWellScopedAt 0 = true := by
    simpa [received, Pattern.isWellScopedAt, Pattern.isWellScopedListAt] using payloadClosed
  unfold freezeView
  rw [canonicalize_substituteViewed_resolveQuotes]
  exact canonicalize_freezeOutside frozenClosed receivedClosed spellingMiss body depth inScope

end FreezeView

/-! ## The literal reading is the frozen reading -/

/-- No binder of the scope reaches into quotations. -/
def Confined (scope : List (Option Binder)) : Prop :=
  ∀ binder, some binder ∈ scope → binder.reaches = false

theorem enterQuote_confined {scope : List (Option Binder)} (confined : Confined scope) :
    enterQuote scope = List.replicate scope.length none := by
  unfold enterQuote
  induction scope with
  | nil => rfl
  | cons entry scope ih =>
      simp only [List.map_cons, List.length_cons, List.replicate_succ]
      congr 1
      · cases entry with
        | none => rfl
        | some binder => simp [confined binder (by simp)]
      · exact ih (fun binder member => confined binder (List.mem_cons_of_mem _ member))

theorem confined_hidden (count : Nat) : Confined (List.replicate count none) := by
  intro binder member
  simp at member

theorem confined_cons {scope : List (Option Binder)} (confined : Confined scope) (name : Name) :
    Confined (some ⟨name, false⟩ :: scope) := by
  intro binder member
  rcases List.mem_cons.mp member with same | rest
  · cases same; rfl
  · exact confined binder rest

private theorem lookup_last_hit {n spelling : Name} {reaches : Bool}
    (hit : NameEquivalence n spelling) : lookup n [some ⟨spelling, reaches⟩] = some 0 := by
  simp [lookup, hit]

private theorem lookup_last_miss {n spelling : Name} {reaches : Bool}
    (miss : ¬ NameEquivalence n spelling) : lookup n [some ⟨spelling, reaches⟩] = none := by
  simp [lookup, miss]

mutual
  /-- On names: the literal reading is the frozen reading, up to name equivalence. -/
  theorem readName_frozen (spelling : Name) :
      ∀ (inside : Bool) (front : List (Option Binder)), Confined front → ∀ n : NName,
        NameEquivalence
          (readName false (front ++ [if inside then none else some ⟨spelling, false⟩]) n)
          (freezeName spelling inside front.length
            (readName false (front ++ [some ⟨spelling, true⟩]) n))
    | inside, front, confined, .quote code => by
        simp only [readName, lookup_append]
        cases frontFound : lookup (.quote (readProcess false [] code)) front with
        | some index =>
            have below := lookup_lt frontFound
            simp only [Option.some_or]
            simp [freezeName, Nat.ne_of_lt below]
            exact .refl _
        | none =>
            simp only [Option.none_or]
            by_cases hit : NameEquivalence (.quote (readProcess false [] code)) spelling
            · rw [lookup_last_hit hit]
              cases inside with
              | false =>
                  simp only [Bool.false_eq_true, if_false, lookup_last_hit hit, Option.map_some]
                  simp [freezeName]
                  exact .refl _
              | true =>
                  simp only [if_true, lookup, Option.map_none, enterQuote_append,
                    enterQuote_confined confined]
                  have hidden : List.replicate front.length (none : Option Binder) ++
                      enterQuote [none] = List.replicate (front.length + 1) none := by
                    simp [enterQuote, List.replicate_succ']
                  rw [hidden, readProcess_hidden]
                  have frozenIndex : freezeName spelling true front.length
                      (.bound (0 + front.length)) = .quote (.drop spelling) := by
                    simp [freezeName]
                  simp only [Option.map_some]
                  rw [frozenIndex]
                  exact .trans hit (.symm (.quote_drop spelling))
            · rw [lookup_last_miss hit]
              have frozenSide : lookup (.quote (readProcess false [] code))
                  [if inside then none else some ⟨spelling, false⟩] = none := by
                cases inside
                · exact lookup_last_miss hit
                · rfl
              simp only [frozenSide, Option.map_none]
              have kept : readName false (front ++ [some ⟨spelling, true⟩]) (.quote code) =
                  .quote (readProcess false (enterQuote (front ++ [some ⟨spelling, true⟩])) code) := by
                simp [readName, lookup_append, frontFound, lookup_last_miss hit]
              rw [freezeName_quote_miss (readName_quote_no_alias kept front.length),
                enterQuote_append, enterQuote_append]
              have inner := readProcess_frozen spelling true (enterQuote front)
                (by rw [enterQuote_confined confined]; exact confined_hidden _) code
              rw [enterQuote_length] at inner
              have literalTail : enterQuote [if inside then none else some ⟨spelling, false⟩] =
                  [none] := by
                cases inside <;> rfl
              have frozenTail : enterQuote [some ⟨spelling, true⟩] = [some ⟨spelling, true⟩] := rfl
              rw [literalTail, frozenTail]
              exact .quote inner

  /-- On processes: the literal reading is the frozen reading, up to the paper's
  congruence. -/
  theorem readProcess_frozen (spelling : Name) :
      ∀ (inside : Bool) (front : List (Option Binder)), Confined front → ∀ p : NProc,
        Congruence
          (readProcess false (front ++ [if inside then none else some ⟨spelling, false⟩]) p)
          (freezeProcess spelling inside front.length
            (readProcess false (front ++ [some ⟨spelling, true⟩]) p))
    | _, _, _, .zero => .refl _
    | inside, front, confined, .par left right => by
        simp only [readProcess, freezeProcess]
        exact .par (readProcess_frozen spelling inside front confined left)
          (readProcess_frozen spelling inside front confined right)
    | inside, front, confined, .send subject payload => by
        simp only [readProcess, freezeProcess]
        exact .send (readName_frozen spelling inside front confined subject)
          (readProcess_frozen spelling inside front confined payload)
    | inside, front, confined, .receive subject binder body => by
        have inner := readProcess_frozen spelling inside _
          (confined_cons confined (readName false [] binder)) body
        simp only [List.cons_append, List.length_cons] at inner
        simp only [readProcess, freezeProcess]
        exact .receive (readName_frozen spelling inside front confined subject) inner
    | inside, front, confined, .drop name => by
        simp only [readProcess, freezeProcess]
        exact .drop (readName_frozen spelling inside front confined name)
end

/-- The paper's substitution respects the paper's congruence of bodies, read at
canonical forms. -/
theorem canonicalForm_substitute_congr {payload : Process} {depth : Nat} {first second : Process}
    (same : canonicalForm first = canonicalForm second) :
    canonicalForm (substitute payload depth first) = canonicalForm (substitute payload depth second) := by
  show canonicalize rhoReflectivePresentation (encodeProcess (substitute payload depth first)) =
    canonicalize rhoReflectivePresentation (encodeProcess (substitute payload depth second))
  rw [← canonicalize_substituteReflective (body := encodeProcess first)
      (received := encodeProcess payload) rfl rfl depth,
    ← canonicalize_substituteReflective (body := encodeProcess first)
      (received := encodeProcess payload) same rfl depth]

theorem closedName_miss (y : NName) : binderIndex (closedName y) = none := by
  cases y with
  | quote code =>
      cases view : binderIndex (closedName (.quote code)) with
      | none => rfl
      | some index =>
          exact absurd view (readName_quote_no_alias (closedName_quote code) index)

/-- The reading of the body of `x(y).P` in which only the eliminated binder `y`
reaches into quotations. -/
noncomputable def reachingBody (y : NName) (body : NProc) : Process :=
  readProcess false [some ⟨closedName y, true⟩] body

/-- The paper's reading of the body of `x(y).P`. -/
noncomputable def literalBody (y : NName) (body : NProc) : Process :=
  readProcess false [some ⟨closedName y, false⟩] body

/-- Our calculus's reading of the body of `x(y).P`. -/
noncomputable def bindingAwareBody (y : NName) (body : NProc) : Process :=
  readProcess true [some ⟨closedName y, true⟩] body

theorem literal_receive (x y : NName) (body : NProc) :
    literal (.receive x y body) = .receive (readName false [] x) (literalBody y body) := rfl

theorem bindingAware_receive (x y : NName) (body : NProc) :
    bindingAware (.receive x y body) = .receive (readName true [] x) (bindingAwareBody y body) := rfl

/-- **The dynamic quote, adequately.** Eliminating the binder `y` of `x(y).P`
with the freeze view, on the reading in which `y` reaches into quotations,
gives, up to the equations, the paper's substitution `P{@Q/y}` on the paper's
reading, which never enters a quotation. The freeze view writes the binder's
name as `@(*y)`. -/
theorem freezeView_matches_paper (y : NName) (body payload : NProc) :
    canonicalize rhoReflectivePresentation
        (freezeView rhoReflectivePresentation 0 (received (literal payload)) (frozen (closedName y))
          (encodeProcess (reachingBody y body))) =
      canonicalForm (substitute (literal payload) 0 (literalBody y body)) := by
  refine (canonicalize_freezeView (payload := literal payload) (spelling := closedName y)
    (body := reachingBody y body) 0 (readProcess_scoped false [] payload) (readName_scoped false [] y)
    (closedName_miss y) (readProcess_scoped false [some ⟨closedName y, true⟩] body)).trans ?_
  apply canonicalForm_substitute_congr
  have frozenBody := readProcess_frozen (closedName y) false [] (confined_hidden 0) body
  simp only [List.nil_append, List.length_nil, Bool.false_eq_true, if_false] at frozenBody
  exact ((canonicalize_encodeProcess_eq_iff _ _).mpr frozenBody).symm

/-- **The binding-aware reading.** When the binders of the body are not
mentioned inside its quotations, the binding-aware reading is the reading in
which only the eliminated binder reaches, and the freeze view on the body our
calculus reads computes the paper's substitution on the body the paper reads. -/
theorem freezeView_bindingAware (y : NName) (body payload : NProc)
    (innerConfined : bindingAwareBody y body = reachingBody y body) :
    canonicalize rhoReflectivePresentation
        (freezeView rhoReflectivePresentation 0 (received (literal payload)) (frozen (closedName y))
          (encodeProcess (bindingAwareBody y body))) =
      canonicalForm (substitute (literal payload) 0 (literalBody y body)) := by
  rw [innerConfined]
  exact freezeView_matches_paper y body payload

/-! ## On the paper's reading every view is `instantiate` -/

/-- A term scoped below a level does not mention it. -/
theorem mentions_false_of_scoped {pattern : Pattern} :
    ∀ {level : Nat}, pattern.isWellScopedAt level = true → mentions level pattern = false := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      intro level inScope
      simp only [Pattern.isWellScopedAt, decide_eq_true_eq] at inScope
      simp [mentions, Nat.ne_of_lt inScope]
  | hfvar name => intro _ _; rfl
  | hlambda binder body ih => intro level inScope; exact ih inScope
  | hmultiLambda arity binders body ih => intro level inScope; exact ih inScope
  | hsubst body value ihBody ihValue =>
      intro level inScope
      simp only [Pattern.isWellScopedAt, Bool.and_eq_true] at inScope
      simp [mentions, ihBody inScope.1, ihValue inScope.2]
  | happly constructor arguments ih =>
      intro level inScope
      have each := (Mettapedia.OSLF.MeTTaIL.ScopedPattern.isWellScopedListAt_eq_true_iff _ _).mp inScope
      simp only [mentions]
      exact (mentionsList_eq_false_iff _ _).mpr fun p m => ih p m (each p m)
  | hcollection kind elements rest ih =>
      intro level inScope
      have each := (Mettapedia.OSLF.MeTTaIL.ScopedPattern.isWellScopedListAt_eq_true_iff _ _).mp inScope
      simp only [mentions]
      exact (mentionsList_eq_false_iff _ _).mpr fun p m => ih p m (each p m)

private theorem everyQuotation_mono {first second : Nat → Pattern → Bool}
    (weaker : ∀ level payload, first level payload = true → second level payload = true)
    {pattern : Pattern} : ∀ {level : Nat},
      everyQuotation rhoReflectivePresentation first level pattern = true →
        everyQuotation rhoReflectivePresentation second level pattern = true := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro _ _; rfl
  | hfvar name => intro _ _; rfl
  | hlambda binder body ih => intro level holds; exact ih holds
  | hmultiLambda arity binders body ih => intro level holds; exact ih holds
  | hsubst body value ihBody ihValue =>
      intro level holds
      simp only [everyQuotation, Bool.and_eq_true] at holds ⊢
      exact ⟨ihBody holds.1, ihValue holds.2⟩
  | hcollection kind elements rest ih =>
      intro level holds
      have each := (everyQuotationList_iff _ _ _ _).mp holds
      exact (everyQuotationList_iff _ _ _ _).mpr fun p m => ih p m (each p m)
  | happly constructor arguments ih =>
      intro level holds
      match arguments, holds, ih with
      | [], _, _ => rfl
      | first' :: second' :: rest, holds, ih =>
          have each := (everyQuotationList_iff _ _ _ _).mp holds
          exact (everyQuotationList_iff _ _ _ _).mpr fun p m => ih p m (each p m)
      | [payload], holds, ih =>
          simp only [everyQuotation] at holds ⊢
          split at holds
          · rename_i isQuote
            rw [if_pos isQuote]
            exact weaker _ _ holds
          · rename_i isQuote
            rw [if_neg isQuote]
            exact ih payload (by simp) holds

mutual
  /-- On the paper's reading every quotation is closed. -/
  theorem readName_binderSafe :
      ∀ (scope : List (Option Binder)) (n : NName), Confined scope →
        binderSafeAt "NQuote" scope.length (encodeName (readName false scope n)) = true
    | scope, .quote code, confined => by
        simp only [readName]
        split
        · rename_i index found
          simpa [encodeName, binderSafeAt] using lookup_lt found
        · rw [enterQuote_confined confined, readProcess_hidden]
          have inner := readProcess_binderSafe [] code (confined_hidden 0)
          simpa [encodeName, binderSafeAt] using inner

  theorem readProcess_binderSafe :
      ∀ (scope : List (Option Binder)) (p : NProc), Confined scope →
        binderSafeAt "NQuote" scope.length (encodeProcess (readProcess false scope p)) = true
    | _, .zero, _ => by simp [readProcess, encodeProcess, binderSafeAt, binderSafeListAt]
    | scope, .par left right, confined => by
        have l := readProcess_binderSafe scope left confined
        have r := readProcess_binderSafe scope right confined
        simp [readProcess, encodeProcess, binderSafeAt, binderSafeListAt, l, r]
    | scope, .send subject payload, confined => by
        have l := readName_binderSafe scope subject confined
        have r := readProcess_binderSafe scope payload confined
        simp [readProcess, encodeProcess, binderSafeAt, binderSafeListAt, l, r]
    | scope, .receive subject binder body, confined => by
        have l := readName_binderSafe scope subject confined
        have r := readProcess_binderSafe _ body (confined_cons confined (readName false [] binder))
        simp only [List.length_cons] at r
        simp [readProcess, encodeProcess, binderSafeAt, binderSafeListAt, l, r]
    | scope, .drop name, confined => by
        have l := readName_binderSafe scope name confined
        simp [readProcess, encodeProcess, binderSafeAt, binderSafeListAt, l]
end

/-- **On the paper's reading the body is sealed**: no quotation mentions the
eliminated binder. -/
theorem literalBody_sealed (y : NName) (body : NProc) :
    Sealed rhoReflectivePresentation 0 (encodeProcess (literalBody y body)) := by
  have safe := readProcess_binderSafe [some ⟨closedName y, false⟩] body
    (confined_cons (confined_hidden 0) (closedName y))
  have resolved := resolveQuotes_binderSafeAt rhoReflectivePresentation safe
  have scopedQuotes := everyQuotation_scoped_of_binderSafeAt (level := 0) resolved
  exact everyQuotation_mono (fun level payload holds => by
    simp [mentions_false_of_scoped holds]) scopedQuotes

/-- **On the paper's reading all quote scopes coincide**, and each is
`instantiate`, which keeps quotations opaque as the paper's substitution does. -/
theorem literalBody_views_coincide (scope : QuoteScope) (y : NName) (body : NProc)
    (replacement : Pattern) :
    substituteUnder rhoReflectivePresentation scope 0 replacement
        (encodeProcess (literalBody y body)) =
      instantiate rhoReflectivePresentation 0 replacement (encodeProcess (literalBody y body)) :=
  substituteUnder_eq_instantiate_of_sealed scope (literalBody_sealed y body)
    (readProcess_scoped false [some ⟨closedName y, false⟩] body)

/-! ## Controls -/

namespace Controls

/-- `@0`. -/
def zeroName : NName := .quote .zero

/-- The binder `z = @(@0!(0))`. -/
def zName : NName := .quote (.send zeroName .zero)

/-- An inner binder `v = @(@0(@0).0)`. -/
def vName : NName := .quote (.receive zeroName zeroName .zero)

/-- The closed reading of `z`. -/
abbrev zClosed : Name := .quote (.send (.quote .zero) .zero)

/-- The closed reading of `v`. -/
abbrev vClosed : Name := .quote (.receive (.quote .zero) .zero)

theorem closedName_zName : closedName zName = zClosed := rfl

theorem closedName_vName : closedName vName = vClosed := rfl

private theorem not_equivalent {a b : Name}
    (different : canonicalize rhoReflectivePresentation (encodeName a) ≠
      canonicalize rhoReflectivePresentation (encodeName b)) : ¬ NameEquivalence a b :=
  fun same => different ((canonicalize_encodeName_eq_iff a b).mpr same)

private theorem zero_not_z : ¬ NameEquivalence (.quote .zero) zClosed :=
  not_equivalent (by decide)

private theorem dynamicKey_not_z :
    ¬ NameEquivalence (.quote (.send (.quote .zero) (.drop zClosed))) zClosed :=
  not_equivalent (by decide)

private theorem subjectKey_not_z : ¬ NameEquivalence (.quote (.send zClosed .zero)) zClosed :=
  not_equivalent (by decide)

private theorem v_not_z : ¬ NameEquivalence vClosed zClosed := not_equivalent (by decide)

private theorem innerKey_not_v : ¬ NameEquivalence (.quote (.send vClosed .zero)) vClosed :=
  not_equivalent (by decide)

private theorem innerKey_not_z : ¬ NameEquivalence (.quote (.send vClosed .zero)) zClosed :=
  not_equivalent (by decide)

/-! ### The example of §2.6 -/

/-- `w[@(y[z])]` with `w = y = @0` and the output sugar `x[y] = x!(*y)`: the
binder `z` occurs only inside the quotation. -/
def dynamicQuote : NProc := .send zeroName (.drop (.quote (.send zeroName (.drop zName))))

/-- `w!(y[z])`: the lifted body is not quoted, so substitution reaches `z`. -/
def liftedBody : NProc := .send zeroName (.send zeroName (.drop zName))

theorem bindingAwareBody_dynamicQuote :
    bindingAwareBody zName dynamicQuote =
      .send (.quote .zero) (.drop (.quote (.send (.quote .zero) (.drop (.bound 0))))) := by
  simp [bindingAwareBody, dynamicQuote, readProcess, readName, lookup, enterQuote,
    closedName, zeroName, zName, zero_not_z, dynamicKey_not_z, NameEquivalence.refl]

theorem reachingBody_dynamicQuote :
    reachingBody zName dynamicQuote =
      .send (.quote .zero) (.drop (.quote (.send (.quote .zero) (.drop (.bound 0))))) := by
  simp [reachingBody, dynamicQuote, readProcess, readName, lookup, enterQuote,
    closedName, zeroName, zName, zero_not_z, dynamicKey_not_z, NameEquivalence.refl]

theorem literalBody_dynamicQuote :
    literalBody zName dynamicQuote =
      .send (.quote .zero) (.drop (.quote (.send (.quote .zero) (.drop zClosed)))) := by
  simp [literalBody, dynamicQuote, readProcess, readName, lookup, enterQuote,
    closedName, zeroName, zName, zero_not_z, dynamicKey_not_z]

/-- The paper's statement: `w[@(y[z])]{u/z} = w[@(y[z])]`; the body between quotes
is impervious to substitution. -/
theorem dynamicQuote_paper :
    substitute .zero 0 (literalBody zName dynamicQuote) = literalBody zName dynamicQuote := by
  rw [literalBody_dynamicQuote]
  rfl

/-- **Positive control.** The freeze view on the reading of our calculus gives the
paper's result spelling for spelling: the drop of `z` inside the quotation
receives `@(*z)`, which is the drop `*z`. -/
theorem dynamicQuote_freeze :
    freezeView rhoReflectivePresentation 0 (received .zero) (frozen zClosed)
        (encodeProcess (bindingAwareBody zName dynamicQuote)) =
      encodeProcess (substitute .zero 0 (literalBody zName dynamicQuote)) := by
  rw [bindingAwareBody_dynamicQuote, literalBody_dynamicQuote]
  decide +kernel

/-- **Separation: the apply view.** Substitution enters the quotation and runs the
received payload at the drop of `z`. -/
theorem dynamicQuote_apply_differs :
    canonicalize rhoReflectivePresentation
        (applyView rhoReflectivePresentation 0 (received .zero)
          (encodeProcess (bindingAwareBody zName dynamicQuote))) ≠
      canonicalForm (substitute .zero 0 (literalBody zName dynamicQuote)) := by
  rw [bindingAwareBody_dynamicQuote, literalBody_dynamicQuote]
  decide +kernel

/-- **Separation: the closure view.** The quotation keeps the value as context. -/
theorem dynamicQuote_closure_differs :
    canonicalize rhoReflectivePresentation
        (closureView rhoReflectivePresentation "Ctx" 0 (received .zero)
          (encodeProcess (bindingAwareBody zName dynamicQuote))) ≠
      canonicalForm (substitute .zero 0 (literalBody zName dynamicQuote)) := by
  rw [bindingAwareBody_dynamicQuote, literalBody_dynamicQuote]
  decide +kernel

/-- **Separation: the bare spelling.** Passing the binder's quotation `@P` itself
as the frozen name runs `P` at the drop of `z` inside the quotation, because a
drop of the eliminated binder receives the name; the responsible rule is the drop
case of `substituteViewed`. The frozen name must be `@(*@P)`. -/
theorem dynamicQuote_bare_spelling_differs :
    canonicalize rhoReflectivePresentation
        (freezeView rhoReflectivePresentation 0 (received .zero) (encodeName zClosed)
          (encodeProcess (bindingAwareBody zName dynamicQuote))) ≠
      canonicalForm (substitute .zero 0 (literalBody zName dynamicQuote)) := by
  rw [bindingAwareBody_dynamicQuote, literalBody_dynamicQuote]
  decide +kernel

/-- **Separation: the opaque traversal.** `instantiate` keeps the quotation as
written and leaves the index of `z` inside it dangling. -/
theorem dynamicQuote_instantiate_dangles :
    (instantiate rhoReflectivePresentation 0 (received .zero)
      (encodeProcess (bindingAwareBody zName dynamicQuote))).isWellScopedAt 0 = false := by
  rw [bindingAwareBody_dynamicQuote]
  decide +kernel

theorem bindingAwareBody_liftedBody :
    bindingAwareBody zName liftedBody = .send (.quote .zero) (.send (.quote .zero) (.drop (.bound 0))) := by
  simp [bindingAwareBody, liftedBody, readProcess, readName, lookup, enterQuote,
    closedName, zeroName, zName, zero_not_z, NameEquivalence.refl]

theorem literalBody_liftedBody :
    literalBody zName liftedBody = .send (.quote .zero) (.send (.quote .zero) (.drop (.bound 0))) := by
  simp [literalBody, liftedBody, readProcess, readName, lookup, enterQuote,
    closedName, zeroName, zName, zero_not_z, NameEquivalence.refl]

/-- **Positive control.** `w!(y[z])`: the lifted body is outside every quotation,
so every view and `instantiate` agree with the paper, which runs the payload at
the drop of `z`. -/
theorem liftedBody_all_agree :
    [applyView rhoReflectivePresentation 0 (received .zero)
          (encodeProcess (bindingAwareBody zName liftedBody)),
        freezeView rhoReflectivePresentation 0 (received .zero) (frozen zClosed)
          (encodeProcess (bindingAwareBody zName liftedBody)),
        closureView rhoReflectivePresentation "Ctx" 0 (received .zero)
          (encodeProcess (bindingAwareBody zName liftedBody)),
        instantiate rhoReflectivePresentation 0 (received .zero)
          (encodeProcess (bindingAwareBody zName liftedBody))] =
      List.replicate 4 (encodeProcess (substitute .zero 0 (literalBody zName liftedBody))) := by
  rw [bindingAwareBody_liftedBody, literalBody_liftedBody]
  decide +kernel

/-! ### Exactness holds only up to the equations -/

/-- `*@(z!(0))`: the binder is the subject of an output inside the quotation. -/
def quotedSubject : NProc := .drop (.quote (.send zName .zero))

theorem bindingAwareBody_quotedSubject :
    bindingAwareBody zName quotedSubject = .drop (.quote (.send (.bound 0) .zero)) := by
  simp [bindingAwareBody, quotedSubject, readProcess, readName, lookup, enterQuote,
    closedName, zeroName, zName, subjectKey_not_z, NameEquivalence.refl]

theorem reachingBody_quotedSubject :
    reachingBody zName quotedSubject = .drop (.quote (.send (.bound 0) .zero)) := by
  simp [reachingBody, quotedSubject, readProcess, readName, lookup, enterQuote,
    closedName, zeroName, zName, subjectKey_not_z, NameEquivalence.refl]

theorem literalBody_quotedSubject :
    literalBody zName quotedSubject = .drop (.quote (.send zClosed .zero)) := by
  simp [literalBody, quotedSubject, readProcess, readName, lookup, enterQuote,
    closedName, zeroName, zName, subjectKey_not_z]

/-- **Exactness fails off drops.** At a subject position inside a quotation the
freeze view writes `@(*z)` where the paper keeps `z`: the two results differ
as written and agree up to the quote-drop equation. -/
theorem quotedSubject_up_to_equations :
    freezeView rhoReflectivePresentation 0 (received .zero) (frozen zClosed)
        (encodeProcess (bindingAwareBody zName quotedSubject)) ≠
      encodeProcess (substitute .zero 0 (literalBody zName quotedSubject)) ∧
    canonicalize rhoReflectivePresentation
        (freezeView rhoReflectivePresentation 0 (received .zero) (frozen zClosed)
          (encodeProcess (bindingAwareBody zName quotedSubject))) =
      canonicalForm (substitute .zero 0 (literalBody zName quotedSubject)) := by
  refine ⟨?_, ?_⟩
  · rw [bindingAwareBody_quotedSubject, literalBody_quotedSubject]
    decide +kernel
  · rw [bindingAwareBody_quotedSubject, ← reachingBody_quotedSubject]
    exact freezeView_matches_paper zName quotedSubject .zero

/-! ### The inner binders of the body -/

/-- `@0(v). *@(v!(0))`: an inner binder occurs inside a quotation. -/
def innerBinder : NProc := .receive zeroName vName (.drop (.quote (.send vName .zero)))

theorem bindingAwareBody_innerBinder :
    bindingAwareBody zName innerBinder =
      .receive (.quote .zero) (.drop (.quote (.send (.bound 0) .zero))) := by
  simp [bindingAwareBody, innerBinder, readProcess, readName, lookup, enterQuote,
    closedName, zeroName, zName, vName, zero_not_z, innerKey_not_v, innerKey_not_z,
    NameEquivalence.refl]

theorem reachingBody_innerBinder :
    reachingBody zName innerBinder = .receive (.quote .zero) (.drop (.quote (.send vClosed .zero))) := by
  simp [reachingBody, innerBinder, readProcess, readName, lookup, enterQuote,
    closedName, zeroName, zName, vName, zero_not_z, innerKey_not_v, innerKey_not_z, v_not_z]

theorem literalBody_innerBinder :
    literalBody zName innerBinder = .receive (.quote .zero) (.drop (.quote (.send vClosed .zero))) := by
  simp [literalBody, innerBinder, readProcess, readName, lookup, enterQuote,
    closedName, zeroName, zName, vName, zero_not_z, innerKey_not_v, innerKey_not_z]

/-- **Obstruction.** When an inner binder of the body occurs inside a quotation,
the binding-aware reading keeps it bound there, and the freeze view, which
eliminates only the outer binder, leaves that index in place, while the paper's
reading has the inner binder's name: the results differ even up to the
equations. The responsible rule is the binding-aware reading of the inner binder
inside the quotation; the hypothesis of `freezeView_bindingAware` fails. -/
theorem innerBinder_obstruction :
    bindingAwareBody zName innerBinder ≠ reachingBody zName innerBinder ∧
      canonicalize rhoReflectivePresentation
          (freezeView rhoReflectivePresentation 0 (received .zero) (frozen zClosed)
            (encodeProcess (bindingAwareBody zName innerBinder))) ≠
        canonicalForm (substitute .zero 0 (literalBody zName innerBinder)) := by
  refine ⟨?_, ?_⟩
  · rw [bindingAwareBody_innerBinder, reachingBody_innerBinder]
    intro same
    simp at same
  · rw [bindingAwareBody_innerBinder, literalBody_innerBinder]
    decide +kernel

/-- `@0(z). *@(v!(0))`: the α-variant of `innerBinder` in the paper, whose
renaming never enters a quotation. -/
def renamedInnerBinder : NProc := .receive zeroName zName (.drop (.quote (.send vName .zero)))

/-- **The binding-aware reading does not respect the paper's α-equivalence.** The
paper reads `@0(v). *@(v!(0))` and `@0(z). *@(v!(0))` alike, while the
binding-aware reading binds `v` inside the quotation of the first only. -/
theorem bindingAware_not_alpha_invariant :
    literal innerBinder = literal renamedInnerBinder ∧
      canonicalForm (bindingAware innerBinder) ≠ canonicalForm (bindingAware renamedInnerBinder) := by
  have literalFirst : literal innerBinder =
      .receive (.quote .zero) (.drop (.quote (.send vClosed .zero))) := by
    simp [literal, innerBinder, readProcess, readName, lookup, enterQuote, zeroName,
      vName, innerKey_not_v]
  have literalSecond : literal renamedInnerBinder =
      .receive (.quote .zero) (.drop (.quote (.send vClosed .zero))) := by
    simp [literal, renamedInnerBinder, readProcess, readName, lookup, enterQuote,
      zeroName, zName, vName, innerKey_not_z]
  have bindingFirst : bindingAware innerBinder =
      .receive (.quote .zero) (.drop (.quote (.send (.bound 0) .zero))) := by
    simp [bindingAware, innerBinder, readProcess, readName, lookup, enterQuote,
      zeroName, vName, innerKey_not_v, NameEquivalence.refl]
  have bindingSecond : bindingAware renamedInnerBinder =
      .receive (.quote .zero) (.drop (.quote (.send vClosed .zero))) := by
    simp [bindingAware, renamedInnerBinder, readProcess, readName, lookup, enterQuote,
      zeroName, zName, vName, zero_not_z, innerKey_not_z, v_not_z]
  refine ⟨literalFirst.trans literalSecond.symm, ?_⟩
  rw [bindingFirst, bindingSecond]
  decide +kernel

end Controls

#print axioms readName_quote_no_alias
#print axioms canonicalize_freezeView
#print axioms readProcess_frozen
#print axioms freezeView_matches_paper
#print axioms freezeView_bindingAware
#print axioms literalBody_sealed
#print axioms literalBody_views_coincide
#print axioms Controls.dynamicQuote_paper
#print axioms Controls.dynamicQuote_freeze
#print axioms Controls.dynamicQuote_apply_differs
#print axioms Controls.dynamicQuote_closure_differs
#print axioms Controls.dynamicQuote_bare_spelling_differs
#print axioms Controls.dynamicQuote_instantiate_dangles
#print axioms Controls.liftedBody_all_agree
#print axioms Controls.quotedSubject_up_to_equations
#print axioms Controls.innerBinder_obstruction
#print axioms Controls.bindingAware_not_alpha_invariant

end Mettapedia.GSLT.Contracts.PaperRho.Named
