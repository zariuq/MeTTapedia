import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows.Codes

/-!
# Rules as rows: codes of rules, the stored-rule program, and the interpreter

At the one-frame action of the code algebra (`X`, with the identity extension `Ext`):

* **The fragment** (`Fragment`): rules whose terms have no `drop`. Every feature of the rule syntax is
  allowed: takes, reads, tells, equation guards, none queries and count queries, made rows and collect query
  patterns, with any number of the rule's own unknowns at any depth.
* **The code of a rule** (`ruleCode`): a closed row `code [takes, reads, makes, left and right sides of
  the tells, first and second terms of the checks, kinds of the checks, collect patterns]`, each part a
  list of quotations (`parts`, `partsAt`). The kind of a check (`Kind`: an equation, a none query, a count
  with its number) is a closed constant of the code, so the order of the checks is kept.
* **The stored-rule program** (`Stored F`): every rule `r` of `F`, with one more read: its own code
  (`stored`). A rule of `Stored F` fires only while a row holding its code is present. This is the
  specification of "the program is in the store".
* **The interpreter** (`U`): one rule per shape (`interp`), which does not depend on any object
  program. A shape gives the numbers of takes, reads, made rows, tells and collect patterns, and the
  list of check kinds, each count with its number; so one arity carries infinitely many rules, one per
  count number. Its first read is the code pattern of its shape (`codePattern`): one interpreter
  unknown per entry, and the kinds as constants. Each take, read, made row, tell side, check term and
  collect pattern of the object rule is the matching unknown dropped at the environment unknown `var 0`
  (`opened`); the interpreter's checks have the object's kinds.

What a code read gives (`decode`, `decode_kinds`, `decode_shape`): at a solution of the code read,
each entry unknown is the quotation of the object rule's term, and the shapes agree. What any object
instantiation gives (`uInst`, `nf_subst_uInst_codePattern`, `nf_subst_uInst_opened`): an interpreter
instantiation that reads the code and opens every term as the object instantiation does, with the
environment holding the object values. Conversely an interpreter instantiation determines the object
one (`objectOf`, `nf_subst_opened_objectOf`).

**Who does what** (`specialize_entry`, `specialize_reads_code`): with its code unknowns set to the
quotations of a rule's parts and its environment left an unknown, the interpreter rule reads that
rule's code, and each of its opened entries is, under the declared equality, the rule's own term with
each unknown `v` replaced by the projection `pick v (var 0)`, a stuck `drop (slot 0 v) (var 0)`
(`pick_var_zero`). So after the code read the interpreter rule is the object rule with its unknowns as
projections of one environment: the equality instantiates the code at the environment and does
nothing else, and choosing rows, takes, makes, checks and collect query are done by firing, as for every
rule.

Fresh openings exist at every state (`fresh_shift`): shifting a rule's unknowns above every unknown
the state mentions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows

open Interface (Frames)
open Expr

/-! ## The one-frame instance -/

/-- Terms at the one frame. -/
abbrev Tm : PUnit.{1} → Type := OneFrame.Terms Expr

/-- The one-frame action of the code algebra. -/
abbrev X : Frames Tm (fun _ _ : PUnit.{1} => ℕ → Expr) := OneFrame.frames action

/-- Firings move along the identity. -/
abbrev Ext : Extensions.{0, 0, 0} (fun _ _ : PUnit.{1} => ℕ → Expr) := OneFrame.ext action

/-! ## Small list facts -/

/-- The largest of a list of numbers (zero for the empty list). -/
def maxOf (l : List ℕ) : ℕ := l.foldr max 0

theorem le_maxOf : ∀ {l : List ℕ} {a : ℕ}, a ∈ l → a ≤ maxOf l
  | _ :: _, _, List.Mem.head _ => le_max_left _ _
  | _ :: _, _, List.Mem.tail _ inside => le_trans (le_maxOf inside) (le_max_right _ _)

theorem forall₂_of_index {α : Type*} {β : Type*} {R : α → β → Prop} : ∀ {l₁ : List α} {l₂ : List β},
    l₁.length = l₂.length → (∀ (i : ℕ) (h₁ : i < l₁.length) (h₂ : i < l₂.length), R l₁[i] l₂[i]) →
      List.Forall₂ R l₁ l₂
  | [], [], _, _ => .nil
  | _ :: _, _ :: _, lengths, all =>
      .cons (all 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _))
        (forall₂_of_index (Nat.succ.inj lengths) fun i h₁ h₂ =>
          all (i + 1) (Nat.succ_lt_succ h₁) (Nat.succ_lt_succ h₂))
  | [], _ :: _, lengths, _ => absurd lengths (by simp)
  | _ :: _, [], lengths, _ => absurd lengths (by simp)

theorem index_of_forall₂ {α : Type*} {β : Type*} {R : α → β → Prop} : ∀ {l₁ : List α} {l₂ : List β},
    List.Forall₂ R l₁ l₂ → ∀ (i : ℕ) (h₁ : i < l₁.length) (h₂ : i < l₂.length), R l₁[i] l₂[i]
  | _, _, .cons head _, 0, _, _ => head
  | _, _, .cons _ tail, i + 1, h₁, h₂ =>
      index_of_forall₂ tail i (Nat.lt_of_succ_lt_succ h₁) (Nat.lt_of_succ_lt_succ h₂)

theorem getD_of_lt {α : Type} (l : List α) (d : α) {i : ℕ} (inside : i < l.length) :
    l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inside]
  rfl

theorem map_range_getD {α : Type} (f : α → Expr) (l : List α) (d : α) :
    (List.range l.length).map (fun i => f (l.getD i d)) = l.map f := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp only [List.getElem_map, List.getElem_range]
    rw [getD_of_lt _ _ (by simpa using h₁)]

/-! ## Check kinds -/

/-- The right side of an equation guard (`nil` for the other checks). -/
def guardRight : Check Expr → Expr
  | .equal _ right => right
  | _ => nil

/-- **The kinds of checks**: an equation, a predicate query with its quantifier, a count with its
number. -/
inductive Kind where
  | equal
  | predicate (quantifier : Quantifier)
  | count (number : ℕ)
  deriving DecidableEq

/-- A kind as a closed constant. -/
def Kind.term : Kind → Expr
  | .equal => sym 20
  | .predicate .none => sym 21
  | .predicate .any => sym 23
  | .count n => cell (sym 22) (sym n)

theorem Kind.term_closed (k : Kind) : k.term.closed := by rcases k with _ | ⟨_ | _⟩ | _ <;> rfl

theorem Kind.quote_term (k : Kind) : quote k.term = k.term := by rcases k with _ | ⟨_ | _⟩ | _ <;> rfl

theorem Kind.term_injective : Function.Injective Kind.term := by
  intro k k' same
  rcases k with _ | ⟨_ | _⟩ | _ <;> rcases k' with _ | ⟨_ | _⟩ | _ <;> simp_all [Kind.term]

/-- The kind of a check. -/
def kindOf : Check Expr → Kind
  | .equal _ _ => .equal
  | .predicate q _ => .predicate q
  | .count _ n => .count n

/-- A check of a kind on two terms (the second is used by equations only). -/
def Kind.check : Kind → Expr → Expr → Check Expr
  | .equal, a, b => .equal a b
  | .predicate q, a, _ => .predicate q a
  | .count n, a, _ => .count a n

/-- **A check is its kind on its two terms.** -/
theorem check_rebuild (c : Check Expr) : (kindOf c).check c.pattern (guardRight c) = c := by
  cases c <;> rfl

/-! ## The fragment and the parts of a rule -/

/-- **The fragment**: rules whose terms have no `drop`. -/
structure Fragment (r : Rule Tm) : Prop where
  take : ∀ t ∈ r.body.take, Expr.dropFree t
  read : ∀ t ∈ r.body.read, Expr.dropFree t
  tell : ∀ e ∈ r.body.tell, Expr.dropFree e.1 ∧ Expr.dropFree e.2
  check : ∀ c ∈ r.body.checks, ∀ t ∈ checkTerms c, Expr.dropFree t
  produce : ∀ t ∈ r.body.produce, Expr.dropFree t
  collect : ∀ t ∈ r.collect, Expr.dropFree t

/-- **The nine parts of a rule**: takes, reads, made rows, the two sides of its tells, the two terms
of its checks, the kinds of its checks, and its collect patterns. -/
def parts (r : Rule Tm) : List (List Expr) :=
  [r.body.take, r.body.read, r.body.produce, r.body.tell.map Prod.fst, r.body.tell.map Prod.snd,
    r.body.checks.map Check.pattern, r.body.checks.map guardRight,
    r.body.checks.map fun c => (kindOf c).term, r.collect]

/-- Part `k` of a rule. -/
def partsAt (r : Rule Tm) (k : ℕ) : List Expr := (parts r).getD k []

theorem partsAt_dropFree {r : Rule Tm} (frag : Fragment r) {k : ℕ} {p : Expr}
    (inside : p ∈ partsAt r k) : p.dropFree := by
  unfold partsAt parts at inside
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | k
  · exact frag.take p inside
  · exact frag.read p inside
  · exact frag.produce p inside
  · obtain ⟨e, member, rfl⟩ := List.mem_map.mp inside
    exact (frag.tell e member).1
  · obtain ⟨e, member, rfl⟩ := List.mem_map.mp inside
    exact (frag.tell e member).2
  · obtain ⟨c, member, rfl⟩ := List.mem_map.mp inside
    refine frag.check c member _ ?_
    cases c <;> simp [checkTerms, Check.pattern]
  · obtain ⟨c, member, rfl⟩ := List.mem_map.mp inside
    cases c with
    | equal left right => exact frag.check _ member right (by simp [checkTerms])
    | predicate quantifier _ => rfl
    | count _ _ => rfl
  · obtain ⟨c, member, rfl⟩ := List.mem_map.mp inside
    rcases c with _ | ⟨_ | _, _⟩ | _ <;> rfl
  · exact frag.collect p inside
  · simp at inside

/-! ## Shapes, codes and the interpreter -/

/-- **An arity shape**: the numbers of takes, reads, made rows, tells and collect patterns, and the
kinds of the checks. -/
structure Shape where
  takes : ℕ
  reads : ℕ
  makes : ℕ
  tells : ℕ
  kinds : List Kind
  collect : ℕ
  deriving DecidableEq

/-- The length of part `k` at a shape. -/
def Shape.len (sh : Shape) : ℕ → ℕ
  | 0 => sh.takes
  | 1 => sh.reads
  | 2 => sh.makes
  | 3 => sh.tells
  | 4 => sh.tells
  | 5 => sh.kinds.length
  | 6 => sh.kinds.length
  | 7 => sh.kinds.length
  | 8 => sh.collect
  | _ => 0

/-- The shape of a rule. -/
def shapeOf (r : Rule Tm) : Shape :=
  ⟨r.body.take.length, r.body.read.length, r.body.produce.length, r.body.tell.length,
    r.body.checks.map kindOf, r.collect.length⟩

theorem len_shapeOf (r : Rule Tm) {k : ℕ} (hk : k < 9) : (shapeOf r).len k = (partsAt r k).length := by
  match k, hk with
  | 0, _ => simp [Shape.len, shapeOf, partsAt, parts]
  | 1, _ => simp [Shape.len, shapeOf, partsAt, parts]
  | 2, _ => simp [Shape.len, shapeOf, partsAt, parts]
  | 3, _ => simp [Shape.len, shapeOf, partsAt, parts]
  | 4, _ => simp [Shape.len, shapeOf, partsAt, parts]
  | 5, _ => simp [Shape.len, shapeOf, partsAt, parts]
  | 6, _ => simp [Shape.len, shapeOf, partsAt, parts]
  | 7, _ => simp [Shape.len, shapeOf, partsAt, parts]
  | 8, _ => simp [Shape.len, shapeOf, partsAt, parts]
  | _ + 9, outside => omega

/-- **The code of a rule**: the nine parts, each a list of quotations. -/
def ruleCode (r : Rule Tm) : Expr :=
  code (lst ((List.range 9).map fun k => lst ((partsAt r k).map quote)))

/-- The interpreter's unknown holding entry `i` of part `k`; `var 0` is the environment. -/
def slotVar (k i : ℕ) : ℕ := 9 * i + k + 1

/-- Column `k` of the code pattern: one interpreter unknown per entry, except the kinds, which are the
shape's constants. -/
def codeColumn (sh : Shape) (k : ℕ) : List Expr :=
  if k = 7 then sh.kinds.map Kind.term else (List.range (sh.len k)).map fun i => var (slotVar k i)

/-- **The code pattern of a shape.** -/
def codePattern (sh : Shape) : Expr := code (lst ((List.range 9).map fun k => lst (codeColumn sh k)))

/-- An entry unknown dropped at the environment unknown. -/
def opened (v : ℕ) : Expr := drop (var v) (var 0)

/-- The opened entries of part `k`. -/
def openedColumn (sh : Shape) (k : ℕ) : List Expr :=
  (List.range (sh.len k)).map fun i => opened (slotVar k i)

/-- **The interpreter rule of a shape.** -/
def interp (sh : Shape) : Rule Tm :=
  ⟨PUnit.unit, ⟨openedColumn sh 0, codePattern sh :: openedColumn sh 1,
    (openedColumn sh 3).zip (openedColumn sh 4),
    sh.kinds.mapIdx (fun i k => k.check (opened (slotVar 5 i)) (opened (slotVar 6 i))),
    openedColumn sh 2⟩, openedColumn sh 8⟩

/-- **The interpreter**: one rule per shape, count numbers included. It depends on no object program. -/
def U : Program Tm := {q | ∃ sh, q = interp sh}

/-- **A rule gated by its own code**: one more read, of the row holding its code. -/
def stored (r : Rule Tm) : Rule Tm :=
  ⟨r.locals, ⟨r.body.take, ruleCode r :: r.body.read, r.body.tell, r.body.checks, r.body.produce⟩,
    r.collect⟩

/-- **The stored-rule program**: every rule of `F`, gated by its own code. -/
def Stored (F : Set (Rule Tm)) : Program Tm := {q | ∃ r ∈ F, q = stored r}

/-- **A fragment closed under what it makes**: rules of the fragment whose made rows are data rows or
codes of rules of the set. -/
structure ClosedFragment (F : Set (Rule Tm)) : Prop where
  fragment : ∀ r ∈ F, Fragment r
  made : ∀ r ∈ F, ∀ m ∈ r.body.produce, (∃ t, m = obj t) ∨ ∃ r' ∈ F, m = ruleCode r'

/-! ## Codes are closed -/

theorem ruleCode_closed {r : Rule Tm} (frag : Fragment r) : (ruleCode r).closed := by
  unfold ruleCode code
  simp only [closed, Bool.and_eq_true]
  refine ⟨trivial, closed_lst ?_⟩
  intro a inside
  obtain ⟨k, -, rfl⟩ := List.mem_map.mp inside
  exact closed_lst fun b member => by
    obtain ⟨p, inside', rfl⟩ := List.mem_map.mp member
    exact quote_closed (partsAt_dropFree frag inside')

theorem subst_ruleCode {r : Rule Tm} (frag : Fragment r) (σ : ℕ → Expr) :
    subst σ (ruleCode r) = ruleCode r :=
  subst_of_closed σ (ruleCode_closed frag)

theorem nf_ruleCode {r : Rule Tm} (frag : Fragment r) : nf (ruleCode r) = ruleCode r :=
  nf_of_closed (ruleCode_closed frag)

/-! ## What a code read gives -/

theorem kinds_closed (sh : Shape) : ∀ a ∈ sh.kinds.map Kind.term, a.closed := by
  intro a inside
  obtain ⟨k, -, rfl⟩ := List.mem_map.mp inside
  exact Kind.term_closed k

theorem nf_subst_codeColumn (h : ℕ → Expr) (sh : Shape) (k : ℕ) :
    nf (subst h (lst (codeColumn sh k))) =
      lst (if k = 7 then sh.kinds.map Kind.term else
        (List.range (sh.len k)).map fun i => nf (h (slotVar k i))) := by
  unfold codeColumn
  by_cases seven : k = 7
  · rw [if_pos seven, if_pos seven, subst_of_closed h (closed_lst (kinds_closed sh)),
      nf_of_closed (closed_lst (kinds_closed sh))]
  · rw [if_neg seven, if_neg seven, subst_lst, nf_lst, List.map_map, List.map_map]
    rfl

theorem nf_subst_codePattern (h : ℕ → Expr) (sh : Shape) :
    nf (subst h (codePattern sh)) =
      code (lst ((List.range 9).map fun k =>
        lst (if k = 7 then sh.kinds.map Kind.term else
          (List.range (sh.len k)).map fun i => nf (h (slotVar k i))))) := by
  unfold codePattern
  rw [subst_code, nf_code, subst_lst, nf_lst, List.map_map, List.map_map]
  congr 2
  apply List.map_congr_left
  intro k _
  exact nf_subst_codeColumn h sh k

/-- **Reading a code**: when the code pattern of a shape is the code of a rule at a solution, the
shapes agree part by part, and each entry unknown is the quotation of the rule's term. -/
theorem decode {sh : Shape} {r : Rule Tm} {h : ℕ → Expr}
    (same : nf (subst h (codePattern sh)) = ruleCode r) {k : ℕ} (hk : k < 9) (hk7 : k ≠ 7) :
    ∃ lengths : sh.len k = (partsAt r k).length,
      ∀ (i : ℕ) (inside : i < sh.len k), nf (h (slotVar k i)) = quote ((partsAt r k)[i]'(lengths ▸ inside)) := by
  rw [nf_subst_codePattern, ruleCode] at same
  simp only [code, Expr.cell.injEq, true_and] at same
  have outer := List.map_inj_left.mp (lst_injective same) k (List.mem_range.mpr hk)
  simp only [if_neg hk7] at outer
  have inner := lst_injective outer
  have lengths : sh.len k = (partsAt r k).length := by
    simpa using congrArg List.length inner
  refine ⟨lengths, fun i inside => ?_⟩
  have entry := congrArg (fun l : List Expr => l[i]?) inner
  simp only [List.getElem?_map, List.getElem?_range inside, Option.map_some] at entry
  rw [List.getElem?_eq_getElem (lengths ▸ inside), Option.map_some, Option.some.injEq] at entry
  exact entry

/-- **Reading a code gives the kinds of its checks.** -/
theorem decode_kinds {sh : Shape} {r : Rule Tm} {h : ℕ → Expr}
    (same : nf (subst h (codePattern sh)) = ruleCode r) : sh.kinds = r.body.checks.map kindOf := by
  rw [nf_subst_codePattern, ruleCode] at same
  simp only [code, Expr.cell.injEq, true_and] at same
  have outer := List.map_inj_left.mp (lst_injective same) 7 (List.mem_range.mpr (by decide))
  rw [if_pos (rfl : (7 : ℕ) = 7)] at outer
  have inner := lst_injective outer
  have terms : sh.kinds.map Kind.term = (r.body.checks.map kindOf).map Kind.term := by
    rw [inner]
    simp [partsAt, parts, Kind.quote_term]
  exact (List.map_injective_iff.mpr Kind.term_injective) terms

/-- **The shape of a read code is the shape of its rule.** -/
theorem decode_shape {sh : Shape} {r : Rule Tm} {h : ℕ → Expr}
    (same : nf (subst h (codePattern sh)) = ruleCode r) : sh = shapeOf r := by
  have part := fun (k : ℕ) (hk : k < 9) (hk7 : k ≠ 7) =>
    ((decode same hk hk7).1).trans (len_shapeOf r hk).symm
  have kinds := decode_kinds same
  cases sh
  simp only [shapeOf, Shape.mk.injEq]
  exact ⟨part 0 (by decide) (by decide), part 1 (by decide) (by decide), part 2 (by decide) (by decide),
    part 3 (by decide) (by decide), kinds, part 8 (by decide) (by decide)⟩

/-- **The object instantiation of an interpreter instantiation**: the entries of its environment. -/
def objectOf (h : ℕ → Expr) : ℕ → Expr := fun w => pick w (nf (h 0))

theorem nf_subst_objectOf (h : ℕ → Expr) {p : Expr} (free : p.dropFree) :
    nf (subst (objectOf h) p) = subst (objectOf h) p := by
  rw [nf_subst_dropFree _ free]
  congr 1
  funext w
  exact nf_pick_of_nf (nf_nf (h 0)) w

/-- **An opened entry is the term instantiated by the environment.** -/
theorem nf_subst_opened_objectOf (h : ℕ → Expr) (v : ℕ) {p : Expr} (free : p.dropFree)
    (coded : nf (h v) = quote p) :
    nf (subst h (opened v)) = nf (subst (objectOf h) p) := by
  rw [nf_subst_objectOf h free]
  show inst (nf (h v)) (nf (h 0)) = _
  rw [coded, inst, if_pos (quote_closed free), fill_quote _ free]
  rfl

/-! ## The interpreter instantiation of an object instantiation -/

/-- One more than the largest unknown of a rule's parts. -/
def ruleBound (r : Rule Tm) : ℕ :=
  maxOf ((List.range 9).map fun k => maxOf ((partsAt r k).map bound))

theorem bound_le_ruleBound {r : Rule Tm} {k : ℕ} (hk : k < 9) {p : Expr} (inside : p ∈ partsAt r k) :
    bound p ≤ ruleBound r :=
  le_trans (le_maxOf (List.mem_map.mpr ⟨p, inside, rfl⟩))
    (le_maxOf (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩))

/-- **The interpreter instantiation of an object instantiation `g`**: the environment holds the values
of `g`, and each entry unknown holds the quotation of the rule's term. -/
def uInst (r : Rule Tm) (g : ℕ → Expr) : ℕ → Expr := fun v =>
  if v = 0 then envOf g (ruleBound r) else quote ((partsAt r ((v - 1) % 9)).getD ((v - 1) / 9) nil)

theorem uInst_zero (r : Rule Tm) (g : ℕ → Expr) : uInst r g 0 = envOf g (ruleBound r) := rfl

theorem uInst_slot (r : Rule Tm) (g : ℕ → Expr) {k : ℕ} (hk : k < 9) (i : ℕ) :
    uInst r g (slotVar k i) = quote ((partsAt r k).getD i nil) := by
  have nonzero : slotVar k i ≠ 0 := by unfold slotVar; omega
  have modulo : (slotVar k i - 1) % 9 = k := by unfold slotVar; omega
  have quotient : (slotVar k i - 1) / 9 = i := by unfold slotVar; omega
  rw [uInst, if_neg nonzero, modulo, quotient]

theorem nf_uInst_slot {r : Rule Tm} (frag : Fragment r) (g : ℕ → Expr) {k : ℕ} (hk : k < 9) {i : ℕ}
    (inside : i < (partsAt r k).length) :
    nf (uInst r g (slotVar k i)) = quote ((partsAt r k)[i]) := by
  rw [uInst_slot r g hk, getD_of_lt _ _ inside,
    nf_of_closed (quote_closed (partsAt_dropFree frag (List.getElem_mem inside)))]

/-- **The interpreter instantiation reads the rule's code.** -/
theorem nf_subst_uInst_codePattern {r : Rule Tm} (frag : Fragment r) (g : ℕ → Expr) :
    nf (subst (uInst r g) (codePattern (shapeOf r))) = ruleCode r := by
  rw [nf_subst_codePattern, ruleCode]
  congr 2
  apply List.map_congr_left
  intro k inside
  have hk : k < 9 := List.mem_range.mp inside
  congr 1
  by_cases seven : k = 7
  · subst seven
    rw [if_pos rfl]
    simp [shapeOf, partsAt, parts, Kind.quote_term]
  · rw [if_neg seven, len_shapeOf r hk, ← map_range_getD quote (partsAt r k) nil]
    apply List.map_congr_left
    intro i member
    rw [uInst_slot r g hk, nf_of_closed]
    have hi : i < (partsAt r k).length := List.mem_range.mp member
    rw [getD_of_lt _ _ hi]
    exact quote_closed (partsAt_dropFree frag (List.getElem_mem hi))

/-- **The interpreter instantiation opens each entry as the object instantiation opens the term.** -/
theorem nf_subst_uInst_opened {r : Rule Tm} (frag : Fragment r) (g : ℕ → Expr) {k : ℕ} (hk : k < 9)
    {i : ℕ} (inside : i < (partsAt r k).length) :
    nf (subst (uInst r g) (opened (slotVar k i))) = nf (subst g ((partsAt r k)[i])) := by
  have free := partsAt_dropFree frag (List.getElem_mem inside)
  have coded := nf_uInst_slot frag g hk inside
  show inst (nf (uInst r g (slotVar k i))) (nf (uInst r g 0)) = _
  rw [coded, inst, if_pos (quote_closed free), fill_quote _ free, uInst_zero,
    nf_subst_dropFree g free]
  apply subst_congr
  intro w below
  exact pick_nf_envOf g (lt_of_lt_of_le below (bound_le_ruleBound hk (List.getElem_mem inside)))

/-! ## The interpreter rule after its code read -/

/-- The interpreter's code unknowns set to the quotations of `r`'s parts; the environment unknown `0`
stays itself. -/
def specialize (r : Rule Tm) : ℕ → Expr := fun v => if v = 0 then var 0 else uInst r var v

/-- **An opened entry, specialized, is the rule's term with each unknown a projection of the
environment.** -/
theorem specialize_entry {r : Rule Tm} (frag : Fragment r) {k : ℕ} (hk : k < 9) {i : ℕ}
    (inside : i < (partsAt r k).length) :
    nf (subst (specialize r) (opened (slotVar k i))) =
      subst (fun v => pick v (var 0)) ((partsAt r k)[i]) := by
  have free := partsAt_dropFree frag (List.getElem_mem inside)
  have nonzero : slotVar k i ≠ 0 := by unfold slotVar; omega
  have coded : nf (specialize r (slotVar k i)) = quote ((partsAt r k)[i]) := by
    show nf (if slotVar k i = 0 then var 0 else uInst r var (slotVar k i)) = _
    rw [if_neg nonzero]
    exact nf_uInst_slot frag var hk inside
  rw [nf_subst_opened_objectOf (specialize r) (slotVar k i) free coded,
    nf_subst_objectOf (specialize r) free]
  rfl

/-- **The projections are stuck drops**: `pick v (var 0)` is `drop (slot 0 v) (var 0)`. -/
theorem pick_var_zero (v : ℕ) : pick v (var 0) = drop (slot 0 v) (var 0) := by
  cases v <;> rfl

/-- **The specialized code pattern reads the rule's code.** -/
theorem specialize_reads_code {r : Rule Tm} (frag : Fragment r) :
    nf (subst (specialize r) (codePattern (shapeOf r))) = ruleCode r := by
  have agree : ∀ k i : ℕ, nf (specialize r (slotVar k i)) = nf (uInst r var (slotVar k i)) := by
    intro k i
    have nonzero : slotVar k i ≠ 0 := by unfold slotVar; omega
    show nf (if slotVar k i = 0 then var 0 else uInst r var (slotVar k i)) = _
    rw [if_neg nonzero]
  rw [← nf_subst_uInst_codePattern frag var, nf_subst_codePattern, nf_subst_codePattern]
  simp only [agree]

/-! ## Fresh openings at every state -/

variable {O : Type*} [DecidableEq O]

/-- One more than the largest unknown a state mentions. -/
def stateBound (s : State Tm O) : ℕ :=
  max (maxOf (s.knowledge.map fun e => max (bound e.1) (bound e.2)))
    (s.present.sup fun o => bound (s.label o))

omit [DecidableEq O] in
theorem bound_le_stateBound {s : State Tm O} {t : Expr} (mentions : s.Mentions t) :
    bound t ≤ stateBound s := by
  rcases mentions with inside | inside | ⟨o, present, rfl⟩
  · obtain ⟨e, member, rfl⟩ := List.mem_map.mp inside
    exact le_trans (le_max_left _ _)
      (le_trans (le_maxOf (List.mem_map.mpr ⟨e, member, rfl⟩)) (le_max_left _ _))
  · obtain ⟨e, member, rfl⟩ := List.mem_map.mp inside
    exact le_trans (le_max_right _ _)
      (le_trans (le_maxOf (List.mem_map.mpr ⟨e, member, rfl⟩)) (le_max_left _ _))
  · exact le_trans (Finset.le_sup (f := fun o => bound (s.label o)) present) (le_max_right _ _)

/-- Shift every unknown by `N`. -/
def shift (N : ℕ) : ℕ → Expr := fun v => var (N + v)

omit [DecidableEq O] in
/-- **Shifting a rule's unknowns above the state's is a fresh opening.** -/
theorem fresh_shift {P : Program Tm} {s : State Tm O} (f : Firing O Ext P s.frame) {N : ℕ}
    (opening : f.opening = shift N) (above : stateBound s ≤ N) : f.Fresh X s := by
  intro b g h
  refine ⟨fun v => if v < N then g v else h (v - N), ?_, ?_⟩
  · intro t mentions
    show nf (subst _ (subst var t)) = nf (subst g t)
    rw [subst_var]
    congr 1
    apply subst_congr
    intro v below
    exact if_pos (lt_of_lt_of_le below (le_trans (bound_le_stateBound mentions) above))
  · intro t _
    show nf (subst _ (subst f.opening t)) = nf (subst h t)
    rw [opening, subst_subst]
    congr 1
    apply subst_congr
    intro v _
    simp [shift, subst]

#print axioms decode
#print axioms decode_kinds
#print axioms decode_shape
#print axioms nf_subst_opened_objectOf
#print axioms nf_subst_uInst_codePattern
#print axioms nf_subst_uInst_opened
#print axioms specialize_entry
#print axioms specialize_reads_code
#print axioms fresh_shift

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows
