import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamesOnTheStep.IssuedNamesControls

/-!
# Loading a theory that mentions only codes

A theory is a list of rule schemas written as data (`Schema`): take, read and produced patterns over
holes, and the holes that the firing's issued names fill. A schema is **code-only** when its
patterns mention no generative name of their own (`Schema.CodeOnly`); its constants and codes need
no issuing.

## Loading needs no issuing

Loading stores every schema of the theory as a term (`Schema.encode`, `loadFiring`). The stored
term of a code-only schema mentions no generative name (`Schema.encode_support`), so

* `loading_needs_no_issuing`: the issuing discipline holds for the loading firing at **every**
  ledger, the empty one included;
* `loading_admitted_iff`: at every ledger, the step with issuing admits loading a code-only theory
  exactly when the step without a ledger does: into any store, issuing never blocks it;
* `loading_keeps_invariant`: loading keeps the issuing invariant.

## A code-only theory cannot forge a generative name

* `writes_of_instance`, `codeOnly_writes`: an instance of a code-only schema writes only names held
  by its holes.
* `matched_names`: a hole that a take or read pattern matches holds only names of the store.
* `no_forgery`: hence an admitted instance whose other holes hold its issued names or issued names
  writes only issued names and its own fresh names. It passes the use check of the discipline by
  itself (`no_forgery_issues`). Holes holding codes need no issued name at all.

## Micromath as data

A theorem `thm o f x y` reads: for all `A B`, `o(A,B) = f(x(A,B), y(A,B))`. Its six rules are
written as schemas (`micromath`): `proj1`, `proj2`, `refl`, `substitute1`, `substitute2`, and
`define`, which issues the defined symbol. The projections `X` and `Y` are the codes of the numerals
`0` and `1`.

* `micromath_codeOnly`: Micromath's rule set mentions only codes.
* `micromath_substitutions_matched`: every hole of the two substitution rules is matched, so their
  firings pass the use check with no condition (`substitutions_cannot_forge`).
* `micromath_loads`: Micromath loads into the empty store at the empty ledger.
* Control `generative_projections_not_codeOnly`, `generative_projections_need_issuing`: with the
  projections as generative names, the rule set is not code-only, and loading it at the empty ledger
  is refused.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamesOnTheStep.CodeOnlyLoading

open IssuingControls

/-! ## Patterns and schemas -/

/-- A pattern: a term with holes. -/
inductive Pat where
  | lit (e : Expr)
  | hole (i : ℕ)
  | app (f a : Pat)
  deriving DecidableEq

namespace Pat

/-- Fill the holes. -/
def inst (σ : ℕ → Expr) : Pat → Expr
  | lit e => e
  | hole i => σ i
  | app f a => .app (f.inst σ) (a.inst σ)

/-- The generative names the pattern mentions on its own. -/
def literalSupport : Pat → Finset ℕ
  | lit e => e.support
  | hole _ => ∅
  | app f a => f.literalSupport ∪ a.literalSupport

/-- Its holes. -/
def holes : Pat → Finset ℕ
  | lit _ => ∅
  | hole i => {i}
  | app f a => f.holes ∪ a.holes

/-- The names of a filled pattern come from its literals or its holes. -/
theorem support_inst (σ : ℕ → Expr) : ∀ (p : Pat) {n : ℕ}, n ∈ (p.inst σ).support →
    n ∈ p.literalSupport ∨ ∃ i ∈ p.holes, n ∈ (σ i).support
  | .lit _, _, named => Or.inl named
  | .hole i, _, named => Or.inr ⟨i, Finset.mem_singleton_self i, named⟩
  | .app f a, _, named => by
      simp only [inst, Expr.support_app, Finset.mem_union] at named
      rcases named with named | named
      · rcases support_inst σ f named with own | ⟨i, member, held⟩
        · exact Or.inl (Finset.mem_union_left _ own)
        · exact Or.inr ⟨i, Finset.mem_union_left _ member, held⟩
      · rcases support_inst σ a named with own | ⟨i, member, held⟩
        · exact Or.inl (Finset.mem_union_right _ own)
        · exact Or.inr ⟨i, Finset.mem_union_right _ member, held⟩

/-- A hole's names are names of the filled pattern. -/
theorem hole_support (σ : ℕ → Expr) : ∀ (p : Pat) {i : ℕ}, i ∈ p.holes →
    ∀ {n : ℕ}, n ∈ (σ i).support → n ∈ (p.inst σ).support
  | .lit _, _, member, _, _ => by simp [holes] at member
  | .hole _, _, member, _, held => by
      simp only [holes, Finset.mem_singleton] at member
      subst member
      exact held
  | .app f a, _, member, _, held => by
      simp only [holes, Finset.mem_union] at member
      simp only [inst, Expr.support_app, Finset.mem_union]
      rcases member with member | member
      · exact Or.inl (hole_support σ f member held)
      · exact Or.inr (hole_support σ a member held)

/-- The pattern stored as a term: literals by their codes. -/
def encode : Pat → Expr
  | lit e => .app (.sym 201) (quote e)
  | hole i => .app (.sym 202) (.sym i)
  | app f a => .app (.app (.sym 203) f.encode) a.encode

@[simp] theorem support_encode : ∀ p : Pat, p.encode.support = p.literalSupport
  | .lit _ => by simp [encode, literalSupport, quote]
  | .hole _ => by simp [encode, literalSupport]
  | .app f a => by simp [encode, literalSupport, support_encode f, support_encode a]

end Pat

/-- A rule schema: take, read and produced patterns, and the holes the issued names fill. -/
structure Schema where
  take : List Pat
  read : List Pat
  produce : List Pat
  fresh : List ℕ
  deriving DecidableEq

namespace Schema

/-- The rule instance of a schema at a filling of its holes. -/
def inst (S : Schema) (σ : ℕ → Expr) : RuleInstance Expr :=
  ⟨S.take.map (Pat.inst σ), S.read.map (Pat.inst σ), [], [], S.produce.map (Pat.inst σ)⟩

def patterns (S : Schema) : List Pat := S.take ++ S.read ++ S.produce

/-- **Code-only**: the schema mentions no generative name of its own. -/
def CodeOnly (S : Schema) : Prop := ∀ p ∈ S.patterns, p.literalSupport = ∅

instance (S : Schema) : Decidable S.CodeOnly :=
  inferInstanceAs (Decidable (∀ p ∈ S.patterns, p.literalSupport = ∅))

/-- A hole is matched when a take or read pattern contains it. -/
def Matched (S : Schema) (i : ℕ) : Prop := ∃ q ∈ S.take ++ S.read, i ∈ q.holes

instance (S : Schema) (i : ℕ) : Decidable (S.Matched i) :=
  inferInstanceAs (Decidable (∃ q ∈ S.take ++ S.read, i ∈ q.holes))

def encodeList : List Pat → Expr
  | [] => .sym 204
  | p :: ps => .app (.app (.sym 205) p.encode) (encodeList ps)

/-- The schema stored as a term. -/
def encode (S : Schema) : Expr :=
  .app (.app (.app (.app (.sym 206) (encodeList S.take)) (encodeList S.read))
    (encodeList S.produce)) (encodeList (S.fresh.map Pat.hole))

theorem support_encodeList_of : ∀ (ps : List Pat), (∀ p ∈ ps, p.literalSupport = ∅) →
    (encodeList ps).support = ∅
  | [], _ => rfl
  | p :: ps, closed => by
      have rest := support_encodeList_of ps fun q member => closed q (List.mem_cons_of_mem _ member)
      simp [encodeList, closed p List.mem_cons_self, rest]

/-- **The stored term of a code-only schema mentions no generative name.** -/
theorem encode_support {S : Schema} (codeOnly : S.CodeOnly) : S.encode.support = ∅ := by
  have take := support_encodeList_of S.take fun p member => codeOnly p (by simp [patterns, member])
  have read := support_encodeList_of S.read fun p member => codeOnly p (by simp [patterns, member])
  have produce :=
    support_encodeList_of S.produce fun p member => codeOnly p (by simp [patterns, member])
  have fresh := support_encodeList_of (S.fresh.map Pat.hole) fun p member => by
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp member
    rfl
  simp [encode, take, read, produce, fresh]

end Schema

/-! ## What an instance writes -/

/-- **An instance writes only names of the schema's literals or of its holes.** -/
theorem writes_of_instance (S : Schema) (σ : ℕ → Expr)
    (queries : List (PredicateQueryAdmission.Query Expr Unit Occ)) (sel : Selection Occ) {n : ℕ}
    (written : n ∈ firingNames Expr.names (⟨S.inst σ, queries, sel⟩ : Fir)) :
    ∃ p ∈ S.patterns, n ∈ p.literalSupport ∨ ∃ i ∈ p.holes, n ∈ (σ i).support := by
  rcases mem_firingNames.mp written with ⟨t, member, named⟩ | ⟨t, member, named⟩ |
      ⟨e, member, _⟩ | ⟨t, member, named⟩
  · obtain ⟨p, inTake, rfl⟩ := List.mem_map.mp member
    exact ⟨p, by simp [Schema.patterns, inTake], p.support_inst σ (by simpa using named)⟩
  · obtain ⟨p, inRead, rfl⟩ := List.mem_map.mp member
    exact ⟨p, by simp [Schema.patterns, inRead], p.support_inst σ (by simpa using named)⟩
  · exact absurd member List.not_mem_nil
  · obtain ⟨p, inProduce, rfl⟩ := List.mem_map.mp member
    exact ⟨p, by simp [Schema.patterns, inProduce], p.support_inst σ (by simpa using named)⟩

/-- **A code-only instance writes only names held by its holes.** -/
theorem codeOnly_writes {S : Schema} (codeOnly : S.CodeOnly) (σ : ℕ → Expr)
    (queries : List (PredicateQueryAdmission.Query Expr Unit Occ)) (sel : Selection Occ) {n : ℕ}
    (written : n ∈ firingNames Expr.names (⟨S.inst σ, queries, sel⟩ : Fir)) :
    ∃ p ∈ S.patterns, ∃ i ∈ p.holes, n ∈ (σ i).support := by
  obtain ⟨p, member, own | held⟩ := writes_of_instance S σ queries sel written
  · rw [codeOnly p member] at own
    simp at own
  · exact ⟨p, member, held⟩

theorem forall₂_left {l : List Expr} {l' : List Occ}
    (h : List.Forall₂ (fun p (o : Occ) => p = o.1) l l') : ∀ q ∈ l, ∃ o ∈ l', q = o.1 := by
  induction h with
  | nil => exact fun _ member => absurd member List.not_mem_nil
  | cons head _ ih =>
      intro q member
      rcases List.mem_cons.mp member with here | later
      · exact ⟨_, List.mem_cons.mpr (Or.inl rfl), here.trans head⟩
      · obtain ⟨o, selected, same⟩ := ih q later
        exact ⟨o, List.mem_cons.mpr (Or.inr selected), same⟩

/-- **A matched hole holds only names of the store.** -/
theorem matched_names {S : Schema} {σ : ℕ → Expr} {sel : Selection Occ} {C : Conf}
    (valid : sel.Valid ground Prod.fst (S.inst σ) C) {i : ℕ} (matched : S.Matched i) {n : ℕ}
    (held : n ∈ (σ i).support) : n ∈ configurationNames Prod.fst Expr.names C := by
  obtain ⟨q, member, inHoles⟩ := matched
  have named := Pat.hole_support σ q inHoles held
  rcases List.mem_append.mp member with inTake | inRead
  · obtain ⟨o, selected, same⟩ :=
      forall₂_left (takes_match valid) (q.inst σ) (List.mem_map_of_mem inTake)
    refine mem_configurationNames.mpr (Or.inr ⟨o, taken_present valid selected, ?_⟩)
    rw [← same]
    simpa using named
  · obtain ⟨o, selected, same⟩ :=
      forall₂_left (reads_match valid) (q.inst σ) (List.mem_map_of_mem inRead)
    refine mem_configurationNames.mpr (Or.inr ⟨o, read_present valid selected, ?_⟩)
    rw [← same]
    simpa using named

/-- **A code-only theory cannot forge a generative name.** An admitted instance whose holes are
matched, or hold the names it issues, or hold issued names, writes only issued names and its own
fresh names. -/
theorem no_forgery {S : Schema} (codeOnly : S.CodeOnly) {σ : ℕ → Expr} {fresh : List ℕ}
    {L : Set ℕ} {C : Conf} {queries : List (PredicateQueryAdmission.Query Expr Unit Occ)}
    {sel : Selection Occ} (valid : sel.Valid ground Prod.fst (S.inst σ) C)
    (invariant : configurationNames Prod.fst Expr.names C ⊆ L)
    (holes : ∀ p ∈ S.patterns, ∀ i ∈ p.holes,
      S.Matched i ∨ (∃ m ∈ fresh, σ i = .name m) ∨ ∀ m ∈ (σ i).support, m ∈ L) :
    firingNames Expr.names (⟨S.inst σ, queries, sel⟩ : Fir) ⊆ L ∪ {n | n ∈ fresh} := by
  intro n written
  obtain ⟨p, member, i, inHoles, held⟩ := codeOnly_writes codeOnly σ queries sel written
  rcases holes p member i inHoles with matched | ⟨m, issued, filled⟩ | given
  · exact Set.mem_union_left _ (invariant (matched_names valid matched held))
  · rw [filled] at held
    simp only [Expr.support_name, Finset.mem_singleton] at held
    subst held
    exact Set.mem_union_right _ issued
  · exact Set.mem_union_left _ (given n held)

/-- The use check of the discipline then holds by itself. -/
theorem no_forgery_issues {S : Schema} (codeOnly : S.CodeOnly) {σ : ℕ → Expr} {fresh : List ℕ}
    {σ₀ : Conf × Set ℕ} {queries : List (PredicateQueryAdmission.Query Expr Unit Occ)}
    {sel : Selection Occ} (valid : sel.Valid ground Prod.fst (S.inst σ) σ₀.1)
    (invariant : Invariant naming σ₀)
    (holes : ∀ p ∈ S.patterns, ∀ i ∈ p.holes,
      S.Matched i ∨ (∃ m ∈ fresh, σ i = .name m) ∨ ∀ m ∈ (σ i).support, m ∈ σ₀.2) :
    naming.firing (s := σ₀.1) (⟨S.inst σ, queries, sel⟩ : Fir) ⊆ σ₀.2 ∪ {n | n ∈ fresh} :=
  no_forgery codeOnly valid invariant holes

/-! ## Loading -/

/-- Storing a theory: one occurrence for each schema. -/
def loadFiring (Θ : List Schema) (copy : ℕ) : Fir :=
  ⟨⟨[], [], [], [], Θ.map Schema.encode⟩, [], ⟨[], [], Θ.map fun S => (S.encode, copy)⟩⟩

theorem load_writes {Θ : List Schema} (codeOnly : ∀ S ∈ Θ, S.CodeOnly) (copy : ℕ) (n : ℕ) :
    n ∉ firingNames Expr.names (loadFiring Θ copy) := by
  intro written
  rcases mem_firingNames.mp written with ⟨_, member, _⟩ | ⟨_, member, _⟩ | ⟨_, member, _⟩ |
      ⟨t, member, named⟩
  · exact absurd member List.not_mem_nil
  · exact absurd member List.not_mem_nil
  · exact absurd member List.not_mem_nil
  · obtain ⟨S, inΘ, rfl⟩ := List.mem_map.mp member
    rw [Expr.mem_names, Schema.encode_support (codeOnly S inΘ)] at named
    simp at named

/-- **Loading a code-only theory needs no issuing**: the discipline holds at every ledger. -/
theorem loading_needs_no_issuing {Θ : List Schema} (codeOnly : ∀ S ∈ Θ, S.CodeOnly) (copy : ℕ)
    (C : Conf) (L : Set ℕ) : Issues naming C L (loadFiring Θ copy) [] :=
  ⟨List.nodup_nil, fun _ member => absurd member List.not_mem_nil,
    fun n written => absurd written (load_writes codeOnly copy n)⟩

/-- **Into any store, at any ledger, issuing never blocks loading a code-only theory.** -/
theorem loading_admitted_iff {Θ : List Schema} (codeOnly : ∀ S ∈ Θ, S.CodeOnly) (copy : ℕ)
    (C : Conf) (L : Set ℕ) :
    (withLedger base (Issues naming)).Admits (s := (C, L)) (loadFiring Θ copy, []) ↔
      base.Admits (s := C) (loadFiring Θ copy) :=
  ⟨fun admitted => admitted.1, fun admitted => ⟨admitted, loading_needs_no_issuing codeOnly copy C L⟩⟩

/-- Loading keeps the issuing invariant. -/
theorem loading_keeps_invariant {Θ : List Schema} (copy : ℕ) {σ₀ : Conf × Set ℕ}
    (admitted : (withLedger base (Issues naming)).Admits (s := σ₀) (loadFiring Θ copy, []))
    (invariant : Invariant naming σ₀) :
    Invariant naming ((withLedger base (Issues naming)).result (s := σ₀) _ admitted) :=
  invariant_result (issues_checksUses naming) _ admitted invariant

/-! ## Micromath as data -/

/-- `thm o f x y`: for all `A B`, `o(A,B) = f(x(A,B), y(A,B))`. -/
def thm (o f x y : Pat) : Pat := .app (.app (.app (.app (.lit (.sym 100)) o) f) x) y

/-- The projections: the codes of the numerals `0` and `1`. -/
def projX : Expr := quote (.sym 0)
def projY : Expr := quote (.sym 1)

/-- `x = X(x, y)`. -/
def proj1 : Schema := ⟨[], [], [thm (.hole 0) (.lit projX) (.hole 0) (.hole 1)], []⟩
/-- `y = Y(x, y)`. -/
def proj2 : Schema := ⟨[], [], [thm (.hole 1) (.lit projY) (.hole 0) (.hole 1)], []⟩
/-- `a = a(X, Y)`. -/
def refl : Schema := ⟨[], [], [thm (.hole 0) (.hole 0) (.lit projX) (.lit projY)], []⟩
/-- From `x = t(u,v)`, `u1 = u(a,b)`, `v1 = v(a,b)`, `x1 = x(a,b)`: `x1 = t(u1,v1)`.
Holes: `x 0, t 1, u 2, v 3, a 4, b 5, u1 6, v1 7, x1 8`. -/
def substitute1 : Schema :=
  ⟨[], [thm (.hole 0) (.hole 1) (.hole 2) (.hole 3), thm (.hole 6) (.hole 2) (.hole 4) (.hole 5),
      thm (.hole 7) (.hole 3) (.hole 4) (.hole 5), thm (.hole 8) (.hole 0) (.hole 4) (.hole 5)],
    [thm (.hole 8) (.hole 1) (.hole 6) (.hole 7)], []⟩
/-- From `x = t(u,v)`, `u1 = u(a,b)`, `v1 = v(a,b)`, `x1 = t(u1,v1)`: `x1 = x(a,b)`. -/
def substitute2 : Schema :=
  ⟨[], [thm (.hole 0) (.hole 1) (.hole 2) (.hole 3), thm (.hole 6) (.hole 2) (.hole 4) (.hole 5),
      thm (.hole 7) (.hole 3) (.hole 4) (.hole 5), thm (.hole 8) (.hole 1) (.hole 6) (.hole 7)],
    [thm (.hole 8) (.hole 0) (.hole 4) (.hole 5)], []⟩
/-- A definition: issue `o` and record `o = f(x,y)`. Holes: `f 0, x 1, y 2, o 3`. -/
def define : Schema := ⟨[], [], [thm (.hole 3) (.hole 0) (.hole 1) (.hole 2)], [3]⟩

/-- **Micromath's rule set, as data.** -/
def micromath : List Schema := [proj1, proj2, refl, substitute1, substitute2, define]

/-- **Micromath's rule set mentions only codes.** -/
theorem micromath_codeOnly : ∀ S ∈ micromath, S.CodeOnly := by decide

/-- Every hole of the two substitution rules is matched. -/
theorem micromath_substitutions_matched :
    ∀ S ∈ [substitute1, substitute2], ∀ p ∈ S.patterns, ∀ i ∈ p.holes, S.Matched i := by decide

/-- **The substitution rules cannot forge a name**: every admitted instance passes the use check
with no condition on its holes. -/
theorem substitutions_cannot_forge {S : Schema} (substitution : S ∈ [substitute1, substitute2])
    {σ : ℕ → Expr} {σ₀ : Conf × Set ℕ} {queries : List (PredicateQueryAdmission.Query Expr Unit Occ)}
    {sel : Selection Occ} (valid : sel.Valid ground Prod.fst (S.inst σ) σ₀.1)
    (invariant : Invariant naming σ₀) :
    naming.firing (s := σ₀.1) (⟨S.inst σ, queries, sel⟩ : Fir) ⊆ σ₀.2 ∪ {n | n ∈ ([] : List ℕ)} := by
  have codeOnly : S.CodeOnly := by
    rcases List.mem_cons.mp substitution with rfl | later
    · exact micromath_codeOnly _ (by simp [micromath])
    · rcases List.mem_singleton.mp later with rfl
      exact micromath_codeOnly _ (by simp [micromath])
  exact no_forgery_issues codeOnly valid invariant fun p member i inHoles =>
    Or.inl (micromath_substitutions_matched S substitution p member i inHoles)

/-- The empty store with nothing issued. -/
def emptyStore : Conf × Set ℕ := (⟨[], ∅⟩, ∅)

/-- **Micromath loads into the empty store at the empty ledger.** -/
theorem micromath_loads :
    (withLedger base (Issues naming)).Admits (s := emptyStore) (loadFiring micromath 0, []) :=
  admits_of (by decide) (by decide) rfl rfl rfl (by decide) (by decide) rfl (no_checks rfl)
    (loading_needs_no_issuing micromath_codeOnly 0 _ _)

/-! ## Control: projections as generative names -/

/-- `x = X(x, y)` with `X` the generative name `0`. -/
def proj1Generative : Schema := ⟨[], [], [thm (.hole 0) (.lit (.name 0)) (.hole 0) (.hole 1)], []⟩

theorem generative_projections_not_codeOnly : ¬ proj1Generative.CodeOnly := by decide

/-- **Control.** Loading it at the empty ledger is refused, in any store. -/
theorem generative_projections_need_issuing (C : Conf) (copy : ℕ) :
    ¬ Issues naming C ∅ (loadFiring [proj1Generative] copy) [] := by
  rintro ⟨_, _, uses⟩
  have written : 0 ∈ naming.firing (s := C) (loadFiring [proj1Generative] copy) := by
    apply mem_firingNames.mpr
    refine Or.inr (Or.inr (Or.inr ⟨proj1Generative.encode, by simp [loadFiring], ?_⟩))
    simp [Schema.encode, Schema.encodeList, proj1Generative, thm, Pat.literalSupport]
  have issued := uses written
  simp at issued

#print axioms Schema.encode_support
#print axioms codeOnly_writes
#print axioms matched_names
#print axioms no_forgery
#print axioms loading_needs_no_issuing
#print axioms loading_admitted_iff
#print axioms loading_keeps_invariant
#print axioms micromath_codeOnly
#print axioms substitutions_cannot_forge
#print axioms micromath_loads
#print axioms generative_projections_need_issuing

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamesOnTheStep.CodeOnlyLoading
