import Mettapedia.Languages.MeTTa.PatternSelection

/-!
# Complete bucketed lookups for two-way matching

A space files each stored row under a key and answers a query from the rows
filed under the keys the query probes.  When stored rows may hold variables,
matching is two-way: after the row is renamed apart, its variables bind as
well as the query's, so a ground query can meet a row that is not equal to it.
A bucketed lookup is *complete* when every row some instance of which unifies
with the query is filed under a probed key (`Complete`).  Completeness is
exactly what makes skipping the other buckets a sound refutation in the sense
of `PatternSelection.Sound`, so the indexed every-match selection equals the
full scan in answers, order and multiplicity (`select_eq_of_complete`).

CeTTa's exact atom index (`exact_index_note_row`) files an exact-indexable
ground row under the row itself, any other row whose head is a symbol under
that head, and every remaining row (a variable, a value, an expression not
headed by a symbol) in one unheaded count (`file`).  A ground query reads the
bucket of its own identity, and its exact-occurrence route is taken only
when the count under its head and the unheaded count are zero
(`exact_index_head_exact`); that is, it probes the three buckets of `probe`.

* `head_subst`: substitution keeps a symbol head.
* `meets_ground_iff`: for a ground query, meeting it is being instantiated
  to it.
* `exactScheme_complete`: the scheme is complete for every ground query,
  whatever the exact-indexable predicate.
* `exact_bucket_suffices`: when the head and unheaded buckets are empty,
  every stored row that meets a ground query is that query itself; this is
  the certificate the exact-occurrence route relies on.
* `exact_only_incomplete`: probing only the query's own bucket is not
  complete; the stored row `(p $x)` meets `(p a)` and is filed elsewhere.
  `exact_only_control` decides the same loss on a concrete store.
* `open_query_needs_guard`: for an open query the scheme is not complete, so
  the route must decline every query with variables, as the C does.
* `shared_row_variables_lose_answer` and `renamed_uses_keep_answer`: two uses
  of one stored row in a conjunction must be renamed apart; with one renaming
  per row the conjunction `(, (zr ka kb) (zr (fz $c) $c))` over the row
  `(zr $y $x)` loses the answer that renamed uses keep.
* `shared_solution_renames_apart`: in general, every solution of a reading
  that shares one renaming between two uses of a row is a solution of the
  renamed-apart reading with the same answer, so sharing loses or specializes
  answers and never adds one.

Equality here is syntactic, as `subst` gives it.  The HE dialect also equates
numbers of different representations; the C declines the exact route for
such queries (`he_number_query_needs_promoted_candidates`), and that equality
is outside this model.  The key scheme is read from the C source; agreement of
the C with this model is measured by differential testing, not proved.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.BucketedLookupCompleteness

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.SubstitutionAlgebra (Subst subst vars)
open Mettapedia.Languages.MeTTa.PatternSelection (Unifiable Sound selectAll)

/-! ## Completeness of a bucketed lookup -/

/-- Some instance of the stored row unifies with the query.  Renaming the
row's variables apart from the query's is one such instance, so this is
two-way matching of a renamed-apart row. -/
def Meets (row query : Atom) : Prop :=
  ∃ τ : Subst, Unifiable (subst τ row) query

/-- A bucketed lookup files every stored row under a key and probes a list of
keys for a query.  It is complete for the served queries when every stored
row that meets a served query is filed under a probed key. -/
def Complete {Key : Type} (file : Atom → Key) (probe : Atom → List Key)
    (served : Atom → Prop) : Prop :=
  ∀ query row, served query → Meets row query → file row ∈ probe query

/-- A row the lookup does not read for the query. -/
def missed {Key : Type} [DecidableEq Key] (file : Atom → Key)
    (probe : Atom → List Key) (query row : Atom) : Bool :=
  !decide (file row ∈ probe query)

/-- A complete lookup misses only rows that cannot meet the query. -/
theorem missed_sound {Key : Type} [DecidableEq Key] {file : Atom → Key}
    {probe : Atom → List Key} {served : Atom → Prop}
    (complete : Complete file probe served) {query : Atom}
    (servedQuery : served query) {Match : Type}
    (attempt : Atom → Option Match)
    (meets : ∀ row found, attempt row = some found → Meets row query) :
    Sound attempt (missed file probe query) := by
  intro row isMissed
  cases attempted : attempt row with
  | none => rfl
  | some found =>
      have filed := complete query row servedQuery (meets row found attempted)
      simp [missed, filed] at isMissed

/-- Reading only the probed buckets selects exactly what the full scan selects,
in order and multiplicity, for every consumer whose attempt succeeds only on
rows meeting the query. -/
theorem select_eq_of_complete {Key : Type} [DecidableEq Key] {file : Atom → Key}
    {probe : Atom → List Key} {served : Atom → Prop}
    (complete : Complete file probe served) {query : Atom}
    (servedQuery : served query) {Match Answer : Type}
    (attempt : Atom → Option Match) (body : Atom → Match → List Answer)
    (meets : ∀ row found, attempt row = some found → Meets row query)
    (rows : List Atom) :
    selectAll attempt body (rows.filter (fun row => !missed file probe query row)) =
      selectAll attempt body rows :=
  PatternSelection.selectAll_filter
    (missed_sound complete servedQuery attempt meets) rows

/-! ## Ground atoms and heads -/

/-- An atom without variables. -/
def Ground (a : Atom) : Prop := vars a = []

instance (a : Atom) : Decidable (Ground a) :=
  inferInstanceAs (Decidable (vars a = []))

/-- The head symbol by which the index counts a row: the symbol itself, or the
first element of an expression when that element is a symbol. -/
def head? : Atom → Option String
  | .symbol s => some s
  | .expression (.symbol s :: _) => some s
  | _ => none

/-- Substitution keeps a symbol head. -/
theorem head_subst (σ : Subst) {a : Atom} {h : String} (headed : head? a = some h) :
    head? (subst σ a) = some h := by
  match a, headed with
  | .symbol s, headed => simpa [subst, head?] using headed
  | .expression (.symbol s :: rest), headed =>
      simpa [subst, subst.substList, head?] using headed

/-- A ground atom is its own every instance. -/
theorem subst_ground (σ : Subst) {a : Atom} (ground : Ground a) : subst σ a = a :=
  SubstitutionAlgebra.subst_of_vars_eq_nil σ a ground

/-- For a ground query, meeting it is being instantiated to it. -/
theorem meets_ground_iff {row query : Atom} (ground : Ground query) :
    Meets row query ↔ ∃ θ : Subst, subst θ row = query := by
  constructor
  · rintro ⟨τ, σ, equal⟩
    refine ⟨SubstitutionAlgebra.comp τ σ, ?_⟩
    rw [← SubstitutionAlgebra.subst_subst, equal, subst_ground σ ground]
  · rintro ⟨θ, equal⟩
    refine ⟨θ, SubstitutionAlgebra.empty, ?_⟩
    rw [SubstitutionAlgebra.subst_empty, SubstitutionAlgebra.subst_empty, equal]

/-! ## CeTTa's exact atom index -/

/-- The buckets of the exact index. -/
inductive Key where
  /-- An exact row, under its own identity. -/
  | exact (row : Atom)
  /-- Any other row whose head is a symbol, counted under that head. -/
  | headed (head : String)
  /-- Every remaining row: a variable, a value, an expression not headed by a
  symbol. -/
  | unheaded
  deriving DecidableEq

/-- Where the index files a stored row.  `exactIndexable` is the C predicate
for leaves it keys by identity; only ground rows are filed by identity. -/
def file (exactIndexable : Atom → Bool) (row : Atom) : Key :=
  if exactIndexable row = true ∧ Ground row then .exact row
  else match head? row with
    | some h => .headed h
    | none => .unheaded

/-- The buckets a ground query reads: its own identity, the count under its
head, and the unheaded count. -/
def probe (query : Atom) : List Key :=
  .exact query :: (((head? query).map Key.headed).toList ++ [.unheaded])

/-- The exact index's lookup is complete for every ground query. -/
theorem exactScheme_complete (exactIndexable : Atom → Bool) :
    Complete (file exactIndexable) probe Ground := by
  intro query row groundQuery meetsQuery
  obtain ⟨θ, equal⟩ := (meets_ground_iff groundQuery).mp meetsQuery
  unfold file
  by_cases filedExact : exactIndexable row = true ∧ Ground row
  · rw [if_pos filedExact]
    rw [subst_ground θ filedExact.2] at equal
    rw [equal]
    exact List.mem_cons_self
  · rw [if_neg filedExact]
    cases headed : head? row with
    | none => simp [probe]
    | some h =>
        have sameHead : head? query = some h := by
          rw [← equal]; exact head_subst θ headed
        simp [probe, sameHead]

/-- The certificate of the exact-occurrence route: when no stored row is filed
under the ground query's head or among the unheaded rows, every stored row that
meets the query is filed under the query's identity, and is the query. -/
theorem exact_bucket_suffices (exactIndexable : Atom → Bool) {query : Atom}
    (groundQuery : Ground query) (rows : List Atom)
    (noHeaded : ∀ row ∈ rows, ∀ h, head? query = some h →
      file exactIndexable row ≠ .headed h)
    (noUnheaded : ∀ row ∈ rows, file exactIndexable row ≠ .unheaded) :
    ∀ row ∈ rows, Meets row query →
      file exactIndexable row = .exact query ∧ row = query := by
  intro row member meetsQuery
  have filed := exactScheme_complete exactIndexable query row groundQuery meetsQuery
  simp only [probe, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at filed
  rcases filed with isExact | inHead | isUnheaded
  · refine ⟨isExact, ?_⟩
    unfold file at isExact
    by_cases filedExact : exactIndexable row = true ∧ Ground row
    · rw [if_pos filedExact] at isExact
      exact Key.exact.inj isExact
    · rw [if_neg filedExact] at isExact
      cases headOfRow : head? row <;> simp [headOfRow] at isExact
  · cases headOfQuery : head? query with
    | none => simp [headOfQuery] at inHead
    | some h =>
        simp [headOfQuery] at inHead
        exact absurd inHead (noHeaded row member h headOfQuery)
  · exact absurd isUnheaded (noUnheaded row member)

/-! ## Controls -/

/-- `(p a)`. -/
def groundQuery : Atom := .expression [.symbol "p", .symbol "a"]

/-- `(p $x)`. -/
def schematicRow : Atom := .expression [.symbol "p", .var "x"]

theorem schematicRow_meets : Meets schematicRow groundQuery :=
  ⟨SubstitutionAlgebra.empty,
    fun v => if v = "x" then some (.symbol "a") else none, by
      simp [schematicRow, groundQuery, SubstitutionAlgebra.subst_empty, subst,
        subst.substList]⟩

/-- Probing only the query's own bucket loses a schematic row's answer. -/
theorem exact_only_incomplete (exactIndexable : Atom → Bool) :
    ¬ Complete (file exactIndexable) (fun query => [Key.exact query]) Ground := by
  intro complete
  have filed := complete groundQuery schematicRow (by decide) schematicRow_meets
  simp [file, schematicRow, groundQuery, Ground, vars, vars.varsList, head?] at filed

/-- Exact-key-only probing over the store `[(p $x)]`, decided: the query
`(p a)` reads no row, while the full scheme reads the row's bucket. -/
theorem exact_only_control :
    ([schematicRow].filter (fun row =>
        decide (file (fun _ => true) row ∈ [Key.exact groundQuery]))).length = 0 ∧
    ([schematicRow].filter (fun row =>
        decide (file (fun _ => true) row ∈ probe groundQuery))).length = 1 := by
  decide

/-- `(p $y)`. -/
def openQuery : Atom := .expression [.symbol "p", .var "y"]

/-- Without the ground-query guard the scheme is not complete: the exact row
`(p a)` meets the open query `(p $y)` and is filed under its own identity. -/
theorem open_query_needs_guard (exactIndexable : Atom → Bool)
    (indexable : exactIndexable groundQuery = true) :
    ¬ Complete (file exactIndexable) probe (fun _ => True) := by
  intro complete
  have meetsOpen : Meets groundQuery openQuery :=
    ⟨SubstitutionAlgebra.empty,
      fun v => if v = "y" then some (.symbol "a") else none, by
        simp [groundQuery, openQuery, SubstitutionAlgebra.subst_empty, subst,
          subst.substList]⟩
  have filed := complete openQuery groundQuery trivial meetsOpen
  have groundRow : Ground groundQuery := by decide
  have filedExact : file exactIndexable groundQuery = Key.exact groundQuery := by
    unfold file
    rw [if_pos ⟨indexable, groundRow⟩]
  rw [filedExact] at filed
  simp [probe, openQuery, groundQuery, head?] at filed

/-! ## Two uses of one stored row -/

/-- `(zr $y $x)`, stored once. -/
def storedRow : Atom := .expression [.symbol "zr", .var "y", .var "x"]

/-- The conjunct `(zr ka kb)`. -/
def firstConjunct : Atom := .expression [.symbol "zr", .symbol "ka", .symbol "kb"]

/-- The conjunct `(zr (fz $c) $c)`. -/
def secondConjunct : Atom :=
  .expression [.symbol "zr", .expression [.symbol "fz", .var "c"], .var "c"]

/-- One renaming per stored row: both uses of the row share its variables, and
no substitution satisfies both conjuncts. -/
theorem shared_row_variables_lose_answer :
    ¬ ∃ σ : Subst, subst σ storedRow = subst σ firstConjunct ∧
      subst σ storedRow = subst σ secondConjunct := by
  rintro ⟨σ, first, second⟩
  rw [first] at second
  simp [firstConjunct, secondConjunct, subst, subst.substList] at second

/-- The row renamed apart for each use: `(zr $y1 $x1)` and `(zr $y2 $x2)`. -/
def firstUse : Atom := .expression [.symbol "zr", .var "y1", .var "x1"]

def secondUse : Atom := .expression [.symbol "zr", .var "y2", .var "x2"]

/-- Renamed apart, the two uses satisfy both conjuncts: the answer the shared
renaming loses. -/
theorem renamed_uses_keep_answer :
    ∃ σ : Subst, subst σ firstUse = subst σ firstConjunct ∧
      subst σ secondUse = subst σ secondConjunct :=
  ⟨fun v =>
      if v = "y1" then some (.symbol "ka")
      else if v = "x1" then some (.symbol "kb")
      else if v = "y2" then some (.expression [.symbol "fz", .var "c"])
      else if v = "x2" then some (.var "c")
      else none,
    by simp [firstUse, firstConjunct, subst, subst.substList],
    by simp [secondUse, secondConjunct, subst, subst.substList]⟩

/-! ## Sharing one renaming between uses only loses answers -/

/-- The renaming that sends each variable `x` to `ρ x`. -/
def renameBy (ρ : String → String) : Subst := fun x => some (.var (ρ x))

/-- A solution in which two uses of one stored row share the row's variables is
also a solution in which the two uses are renamed apart, and it gives every
template over the query's variables the same image.  Reading both uses through
one renaming can therefore lose answers or specialize them (an answer of the
shared reading is an instance of a most general renamed-apart answer), but it
never yields an answer that per-use renaming does not. -/
theorem shared_solution_renames_apart
    (ρ₁ ρ₂ : String → String)
    (injective₁ : ∀ x y, ρ₁ x = ρ₁ y → x = y)
    (injective₂ : ∀ x y, ρ₂ x = ρ₂ y → x = y)
    (disjoint : ∀ x y, ρ₁ x ≠ ρ₂ y)
    (row first second template : Atom)
    (fresh : ∀ v, (v ∈ vars first ∨ v ∈ vars second ∨ v ∈ vars template) →
      (∀ x, ρ₁ x ≠ v) ∧ (∀ x, ρ₂ x ≠ v))
    (σ : Subst) (useFirst : subst σ row = subst σ first)
    (useSecond : subst σ row = subst σ second) :
    ∃ τ : Subst,
      subst τ (subst (renameBy ρ₁) row) = subst τ first ∧
      subst τ (subst (renameBy ρ₂) row) = subst τ second ∧
      subst τ template = subst σ template := by
  classical
  let τ : Subst := fun v =>
    if h₁ : ∃ x, ρ₁ x = v then some (subst σ (.var (Classical.choose h₁)))
    else if h₂ : ∃ x, ρ₂ x = v then some (subst σ (.var (Classical.choose h₂)))
    else σ v
  have atFirst : ∀ x, subst τ (.var (ρ₁ x)) = subst σ (.var x) := by
    intro x
    have h₁ : ∃ y, ρ₁ y = ρ₁ x := ⟨x, rfl⟩
    have chosen : Classical.choose h₁ = x := injective₁ _ _ (Classical.choose_spec h₁)
    have value : τ (ρ₁ x) = some (subst σ (.var x)) := by
      simp only [τ, dif_pos h₁, chosen]
    simp only [subst, value, Option.getD_some]
  have atSecond : ∀ x, subst τ (.var (ρ₂ x)) = subst σ (.var x) := by
    intro x
    have h₁ : ¬ ∃ y, ρ₁ y = ρ₂ x := fun ⟨y, same⟩ => disjoint y x same
    have h₂ : ∃ y, ρ₂ y = ρ₂ x := ⟨x, rfl⟩
    have chosen : Classical.choose h₂ = x := injective₂ _ _ (Classical.choose_spec h₂)
    have value : τ (ρ₂ x) = some (subst σ (.var x)) := by
      simp only [τ, dif_neg h₁, dif_pos h₂, chosen]
    simp only [subst, value, Option.getD_some]
  have elsewhere : ∀ v, (∀ x, ρ₁ x ≠ v) → (∀ x, ρ₂ x ≠ v) →
      subst τ (.var v) = subst σ (.var v) := by
    intro v not₁ not₂
    have h₁ : ¬ ∃ x, ρ₁ x = v := fun ⟨x, same⟩ => not₁ x same
    have h₂ : ¬ ∃ x, ρ₂ x = v := fun ⟨x, same⟩ => not₂ x same
    have value : τ v = σ v := by simp only [τ, dif_neg h₁, dif_neg h₂]
    simp only [subst, value]
  have renamedRow : ∀ (ρ : String → String),
      (∀ x, subst τ (.var (ρ x)) = subst σ (.var x)) →
      subst τ (subst (renameBy ρ) row) = subst σ row := by
    intro ρ at_
    rw [SubstitutionAlgebra.subst_subst]
    apply (SubstitutionAlgebra.subst_eq_iff_on_vars _ _ row).mpr
    intro name _
    simpa [subst, SubstitutionAlgebra.comp, renameBy] using at_ name
  have sameOn : ∀ a : Atom, (∀ v ∈ vars a, (∀ x, ρ₁ x ≠ v) ∧ (∀ x, ρ₂ x ≠ v)) →
      subst τ a = subst σ a := by
    intro a outside
    apply (SubstitutionAlgebra.subst_eq_iff_on_vars _ _ a).mpr
    intro name member
    exact elsewhere name (outside name member).1 (outside name member).2
  refine ⟨τ, ?_, ?_, ?_⟩
  · rw [renamedRow ρ₁ atFirst, useFirst,
      sameOn first (fun v member => fresh v (Or.inl member))]
  · rw [renamedRow ρ₂ atSecond, useSecond,
      sameOn second (fun v member => fresh v (Or.inr (Or.inl member)))]
  · exact sameOn template (fun v member => fresh v (Or.inr (Or.inr member)))

end Mettapedia.Languages.MeTTa.BucketedLookupCompleteness
