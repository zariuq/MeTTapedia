import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows.RunTime
import Mathlib.Data.Set.Finite.List

/-!
# What one finite program can do, what no finite program can do, and self-application

**A uniform family** (`readShape_interp`, `interp_injective`, `mem_U_iff`): `interp` is an injective
computable map from shapes to rules, and a rule is in `U` exactly when it is the interpreter rule of
the shape read back from its own lengths and check kinds (`readShape`). Shapes include the count
numbers of the checks, so one arity carries infinitely many rules (`count_rules_injective`).

**A finite interpreter for each bound** (`UpTo N`, `upTo_finite`, `bisimulation_upTo`): the
interpreter rules of shapes with at most `N` entries in each part and count numbers at most `N` form a
finite program, and it is strongly bisimilar to the stored-rule program of every closed fragment whose
rules are bounded by `N` in the same way (`Bounded`). Both bounds are needed: the rules of shapes with
at most one entry in each part are infinitely many (`entriesAtMostOne_infinite`). The rules of `U` that
fire at a representing state have the shape of a rule of the fragment (`admitted_shape`).

**No finite program interprets every rule firing for firing** (`no_finite_one_firing`): for every
finite program `P` (any rules at all) there is a firing of the stored-rule program, admitted, whose
selection no admitted firing of `P` at any state has. The reason is arity: a firing takes exactly as
many rows as its rule has take patterns (`taken_le`), and a finite program has a largest take arity
(`finite_takesAtMost`); the stored rule `wide n` takes `n` rows (`wideFiring_admitted`). So one fixed
finite program interprets every object program only through several firings per object firing, or a
representation in which an object row is not a row.

**Self-application** (`interp_fragment_iff`, `U_not_fragment`): an interpreter rule is in the fragment
exactly when its shape is empty. Every other rule of `U` drops an entry at the environment, and `drop`
is the construct the fragment excludes: codes are quotations of drop-free terms. So `U` interprets the
code of its own empty-shape rule (`stored_interp_empty`) and of no other rule of `U`; and that rule is
idle: it reads a code row and takes, tells, checks, makes and sees nothing (`interp_empty_idle`). Self-
application covers only the rule that does nothing.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open LogicOverTheStep.StepSpan (Succ)
open Expr

/-! ## Firings across programs -/

section Programs

variable {O : Type*} [DecidableEq O]

/-- A firing of a smaller program, as a firing of a larger one. -/
def liftFiring {P Q : Program Tm} (sub : P ⊆ Q) {a : PUnit.{1}} (f : Firing O Ext P a) :
    Firing O Ext Q a :=
  ⟨f.rule, sub f.member, f.ext, f.opening, f.selection, f.seen⟩

/-- A firing of a larger program whose rule is in a smaller one, as a firing of the smaller. -/
def restrictFiring {P Q : Program Tm} {a : PUnit.{1}} (f : Firing O Ext Q a) (inside : f.rule ∈ P) :
    Firing O Ext P a :=
  ⟨f.rule, inside, f.ext, f.opening, f.selection, f.seen⟩

/-- **Every admitted firing of the interpreter at a representing state has the shape of a rule of the
fragment.** -/
theorem admitted_shape {F : Set (Rule Tm)} {s u : State Tm O} (rep : Represents F s u)
    (closed : ClosedFragment F) (g : Firing O Ext U u.frame) (admitted : g.Admits X u) :
    ∃ r ∈ F, g.rule = interp (shapeOf r) := by
  obtain ⟨sh, hg⟩ := interp_cases g
  rw [hg] at admitted
  obtain ⟨-, -, -, takeLength, readLength, -, -⟩ := admitted.1
  have readLength' : sh.reads + 1 = (g.selection).read.length := by
    have lengths : (codePattern sh :: openedColumn sh 1).length = g.selection.read.length := readLength
    rw [List.length_cons, length_openedColumn] at lengths
    exact lengths
  obtain ⟨c₀, rest, reads, -⟩ := exists_cons_of_length readLength'
  have present := present_of_enabled admitted.2.1
  have c₀present : c₀ ∈ s.present :=
    rep.present ▸ present c₀ (List.mem_append_right _ (reads ▸ List.mem_cons_self))
  obtain ⟨_, τ₀, solved⟩ := admitted.2.2.1
  obtain ⟨known, -, readsG, -⟩ := (models_information
    (interpFiring sh u.frame g.opening g.selection g.seen) takeLength readLength τ₀).mp solved
  have readsG' : List.Forall₂ (fun p o => nf (subst τ₀ (subst g.opening p)) = nf (subst τ₀ (u.label o)))
      (codePattern sh :: openedColumn sh 1) (c₀ :: rest) := by
    rw [← reads]
    exact readsG
  have codeRead := (List.forall₂_cons.mp readsG').1
  have isCode : ∃ c, nf (subst τ₀ (subst g.opening (codePattern sh))) = code c := by
    rw [subst_subst, nf_subst_codePattern]
    exact ⟨_, rfl⟩
  obtain ⟨r, hr, coded⟩ := coded_of_read rep c₀present known codeRead isCode
  have frag := closed.fragment r hr
  obtain ⟨σ', knownS, labels⟩ := rep.forth τ₀ known
  have codeH : nf (subst (fun v => subst τ₀ (g.opening v)) (codePattern sh)) = ruleCode r := by
    rw [← subst_subst, codeRead, labels c₀ c₀present, coded.value frag knownS]
  have shape := decode_shape codeH
  exact ⟨r, hr, by rw [hg, ← shape]; rfl⟩

end Programs

/-! ## A uniform family -/

/-- The shape a rule is read back as: its lengths and the kinds of its checks. -/
def readShape (q : Rule Tm) : Shape :=
  ⟨q.body.take.length, q.body.read.length - 1, q.body.produce.length, q.body.tell.length,
    q.body.checks.map kindOf, q.collect.length⟩

theorem kindOf_kindCheck (k : Kind) (a b : Expr) : kindOf (k.check a b) = k := by
  cases k <;> rfl

theorem map_kindOf_mapIdx (kinds : List Kind) (f g : ℕ → Expr) :
    (kinds.mapIdx fun i k => k.check (f i) (g i)).map kindOf = kinds := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp [List.getElem_mapIdx, kindOf_kindCheck]

/-- **The shape of an interpreter rule is read back from the rule.** -/
theorem readShape_interp (sh : Shape) : readShape (interp sh) = sh := by
  obtain ⟨t, r, m, l, kinds, c⟩ := sh
  simp only [readShape, interp, List.length_cons, length_openedColumn, List.length_zip, Shape.len,
    min_self, Nat.add_sub_cancel, map_kindOf_mapIdx]

theorem interp_injective : Function.Injective interp := fun sh sh' same => by
  rw [← readShape_interp sh, ← readShape_interp sh', same]

/-- **Membership in `U` is one computation and one comparison.** -/
theorem mem_U_iff (q : Rule Tm) : q ∈ U ↔ q = interp (readShape q) := by
  constructor
  · rintro ⟨sh, rfl⟩
    rw [readShape_interp]
  · intro same
    exact ⟨_, same⟩

/-- **One arity, infinitely many rules**: the rules of one take and one count check differ for every
count number. -/
theorem count_rules_injective :
    Function.Injective fun n : ℕ => interp ⟨1, 0, 0, 0, [.count n], 0⟩ := by
  intro n m same
  have shapes := interp_injective same
  simpa using shapes

/-- The interpreter rules of shapes with at most one entry in each part, count numbers unbounded. -/
def entriesAtMostOne : Program Tm :=
  {q | ∃ sh : Shape, sh.takes ≤ 1 ∧ sh.reads ≤ 1 ∧ sh.makes ≤ 1 ∧ sh.tells ≤ 1 ∧
    sh.kinds.length ≤ 1 ∧ sh.collect ≤ 1 ∧ q = interp sh}

/-- **Bounding the entries of each part does not make the interpreter finite**: the count numbers must
be bounded too, as `UpTo` does. -/
theorem entriesAtMostOne_infinite : entriesAtMostOne.Infinite :=
  Set.infinite_of_injective_forall_mem count_rules_injective fun n =>
    ⟨⟨1, 0, 0, 0, [.count n], 0⟩, le_rfl, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, le_rfl,
      Nat.zero_le _, rfl⟩

/-! ## A finite interpreter for each bound -/

/-- The number of a count (zero for the other kinds). -/
def Kind.number : Kind → ℕ
  | .count n => n
  | _ => 0

/-- A numbering of the kinds. -/
def Kind.code : Kind → ℕ
  | .equal => 0
  | .predicate .none => 1
  | .predicate .any => 2
  | .count n => n + 3

/-- **The interpreter rules of shapes with at most `N` entries in each part and count numbers at most
`N`.** -/
def UpTo (N : ℕ) : Program Tm :=
  {q | ∃ sh : Shape, sh.takes ≤ N ∧ sh.reads ≤ N ∧ sh.makes ≤ N ∧ sh.tells ≤ N ∧
    sh.kinds.length ≤ N ∧ (∀ k ∈ sh.kinds, k.number ≤ N) ∧ sh.collect ≤ N ∧ q = interp sh}

theorem upTo_sub (N : ℕ) : UpTo N ⊆ U := fun _ ⟨sh, _, _, _, _, _, _, _, same⟩ => ⟨sh, same⟩

/-- **`UpTo N` is a finite program.** -/
theorem upTo_finite (N : ℕ) : (UpTo N).Finite := by
  let decodeKind : Fin (N + 4) → Kind := fun j =>
    match j.val with
    | 0 => .equal
    | 1 => .predicate .none
    | 2 => .predicate .any
    | n + 3 => .count n
  let encodeKind : Kind → Fin (N + 4) := fun k => ⟨min (k.code) (N + 3), by omega⟩
  have roundTrip : ∀ k : Kind, k.number ≤ N → decodeKind (encodeKind k) = k := by
    intro k bound
    cases k with
    | equal => simp [decodeKind, encodeKind, Kind.code]
    | predicate q => cases q <;> simp [decodeKind, encodeKind, Kind.code]
    | count n =>
        have small : min (n + 3) (N + 3) = n + 3 := min_eq_left (by simp [Kind.number] at bound; omega)
        simp [decodeKind, encodeKind, Kind.code, small]
  let build : (Fin (N + 1) × Fin (N + 1) × Fin (N + 1) × Fin (N + 1) × Fin (N + 1)) ×
      List (Fin (N + 4)) → Rule Tm := fun x =>
    interp ⟨x.1.1, x.1.2.1, x.1.2.2.1, x.1.2.2.2.1, x.2.map decodeKind, x.1.2.2.2.2⟩
  refine ((Set.finite_univ.prod (List.finite_length_le (Fin (N + 4)) N)).image build).subset ?_
  rintro q ⟨⟨t, r, m, l, kinds, c⟩, ht, hr, hm, hl, hk, hn, hc, rfl⟩
  refine ⟨((⟨t, Nat.lt_succ_of_le ht⟩, ⟨r, Nat.lt_succ_of_le hr⟩, ⟨m, Nat.lt_succ_of_le hm⟩,
    ⟨l, Nat.lt_succ_of_le hl⟩, ⟨c, Nat.lt_succ_of_le hc⟩), kinds.map encodeKind),
    ⟨Set.mem_univ _, by simpa using hk⟩, ?_⟩
  show interp ⟨t, r, m, l, (kinds.map encodeKind).map decodeKind, c⟩ = interp ⟨t, r, m, l, kinds, c⟩
  rw [List.map_map]
  congr 2
  conv_rhs => rw [← List.map_id kinds]
  exact List.map_congr_left fun k inside => roundTrip k (hn k inside)

/-- A rule with at most `N` entries in each part, and count numbers at most `N`. -/
def Bounded (N : ℕ) (r : Rule Tm) : Prop :=
  (shapeOf r).takes ≤ N ∧ (shapeOf r).reads ≤ N ∧ (shapeOf r).makes ≤ N ∧ (shapeOf r).tells ≤ N ∧
    (shapeOf r).kinds.length ≤ N ∧ (∀ k ∈ (shapeOf r).kinds, k.number ≤ N) ∧ (shapeOf r).collect ≤ N

section Finite

variable {O : Type*} [DecidableEq O]

/-- **For every closed fragment of rules bounded by `N`, the finite interpreter `UpTo N` and the
stored-rule program are strongly bisimilar.** -/
theorem bisimulation_upTo {F : Set (Rule Tm)} (closed : ClosedFragment F) {N : ℕ}
    (bounded : ∀ r ∈ F, Bounded N r) {s u : State Tm O} (rep : Represents F s u) :
    (∀ s', StoredSucc F s s' → ∃ u', Succ (step X O Ext (UpTo N)).toStep u u' ∧ Represents F s' u') ∧
      (∀ u', Succ (step X O Ext (UpTo N)).toStep u u' → ∃ s', StoredSucc F s s' ∧
        Represents F s' u') := by
  constructor
  · rintro s' ⟨f, admitted, rfl⟩
    obtain ⟨g, admittedG, -, rep'⟩ := forward closed rep f admitted
    obtain ⟨r, hr, rule⟩ := admitted_shape rep closed g admittedG
    obtain ⟨b₁, b₂, b₃, b₄, b₅, b₆, b₇⟩ := bounded r hr
    have inside : g.rule ∈ UpTo N := ⟨shapeOf r, b₁, b₂, b₃, b₄, b₅, b₆, b₇, rule⟩
    exact ⟨g.result X u, ⟨restrictFiring g inside, admittedG, rfl⟩, rep'⟩
  · rintro u' ⟨g, admitted, rfl⟩
    obtain ⟨f, admittedF, -, rep'⟩ := backward closed rep (liftFiring (upTo_sub N) g) admitted
    exact ⟨f.result X s, ⟨f, admittedF, rfl⟩, rep'⟩

end Finite

/-! ## No finite program interprets every rule firing for firing -/

/-- A program whose rules have at most `N` take patterns. -/
def TakesAtMost (P : Program Tm) (N : ℕ) : Prop := ∀ r ∈ P, r.body.take.length ≤ N

/-- **A finite program has a largest take arity.** -/
theorem finite_takesAtMost {P : Program Tm} (finite : P.Finite) : ∃ N, TakesAtMost P N := by
  obtain ⟨N, upper⟩ := (finite.image fun r : Rule Tm => r.body.take.length).bddAbove
  exact ⟨N, fun r inside => upper ⟨r, inside, rfl⟩⟩

/-- **A firing takes exactly as many rows as its rule has take patterns.** -/
theorem taken_le {O : Type*} [DecidableEq O] {P : Program Tm} {N : ℕ} (bounded : TakesAtMost P N)
    {u : State Tm O} (g : Firing O Ext P u.frame) (admitted : g.Admits X u) :
    g.selection.taken.length ≤ N := by
  obtain ⟨-, -, -, takeLength, -⟩ := admitted.1
  exact takeLength ▸ bounded g.rule g.member

/-- A token. -/
def tokZ : Expr := sym 17

/-- **A stored rule taking `n` tokens.** -/
def wide (n : ℕ) : Rule Tm := ⟨PUnit.unit, ⟨List.replicate n (obj tokZ), [], [], [], []⟩, []⟩

theorem wide_mem (n : ℕ) : wide n ∈ Examples.DataFragment := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro t inside
    obtain ⟨-, rfl⟩ := List.mem_replicate.mp inside
    rfl
  all_goals (intro t inside; simp [wide] at inside)

/-- The labels of the store of `n` tokens and the code of `wide n`. -/
def wideLabel (n : ℕ) (o : ℕ) : Expr := if o < n then obj tokZ else ruleCode (wide n)

/-- **The store of `n` tokens and the code of `wide n`.** -/
def wideStore (n : ℕ) : State Tm ℕ := ⟨PUnit.unit, [], Finset.range (n + 1), wideLabel n⟩

/-- `wide n` taking every token and reading its code. -/
def wideFiring (n : ℕ) : Firing ℕ Ext (Stored Examples.DataFragment) (wideStore n).frame :=
  storedFiring (wide_mem n) (wideStore n).frame (shift (stateBound (wideStore n)))
    ⟨List.range n, [n], []⟩ []

/-- The selection of `wide n`: every token, then its code. -/
theorem wide_enabled (n : ℕ) :
    Enabled (fun _ : ℕ => ()) (Finset.range (n + 1))
      ((⟨List.range n, [n], []⟩ : Selection ℕ).commit (T := Unit)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro o inside
    simp only [Selection.commit, List.mem_toFinset, List.mem_range] at inside
    simp only [Finset.mem_range]
    omega
  · intro o inside
    simp only [Selection.commit, List.mem_toFinset, List.mem_singleton] at inside
    simp only [Finset.mem_range]
    omega
  · rw [Finset.disjoint_left]
    intro o taken read
    simp only [Selection.commit, List.mem_toFinset, List.mem_range, List.mem_singleton] at taken read
    omega
  · simp [Selection.commit]
  · intro query inside
    simp [Selection.commit] at inside

/-- **`wide n` fires, taking `n` rows.** -/
theorem wideFiring_admitted (n : ℕ) : (wideFiring n).Admits X (wideStore n) := by
  have takeLength : (wide n).body.take.length = (List.range n).length := by simp [wide]
  have readLength : (ruleCode (wide n) :: (wide n).body.read).length = [n].length := rfl
  refine ⟨⟨fresh_shift (wideFiring n) rfl le_rfl, List.nodup_range, List.nodup_nil, takeLength,
    readLength, rfl, rfl⟩, wide_enabled n, ⟨PUnit.unit, var, ?_⟩, ?_⟩
  · refine (models_information (wideFiring n) takeLength readLength var).mpr ⟨by simp [wideStore],
      ?_, ?_, ?_⟩
    · show List.Forall₂ (fun p o => nf (subst var (subst (shift (stateBound (wideStore n))) p)) =
          nf (subst var (wideLabel n o))) (List.replicate n (obj tokZ)) (List.range n)
      refine forall₂_of_index (by simp) fun i h₁ h₂ => ?_
      have below : i < n := by simpa using h₂
      rw [List.getElem_replicate, List.getElem_range, wideLabel, if_pos below]
      rfl
    · show List.Forall₂ (fun p o => nf (subst var (subst (shift (stateBound (wideStore n))) p)) =
          nf (subst var (wideLabel n o))) [ruleCode (wide n)] [n]
      refine List.Forall₂.cons ?_ List.Forall₂.nil
      show nf (subst var (subst _ (ruleCode (wide n)))) = nf (subst var (wideLabel n n))
      rw [wideLabel, if_neg (Nat.lt_irrefl n), subst_ruleCode (wide_mem n).1,
        subst_ruleCode (wide_mem n).1]
    · intro e inside
      simp [wideFiring, storedFiring, stored, wide] at inside
  · intro b σ _
    refine (holds_iff (wideFiring n) rfl σ).mpr ?_
    intro c inside
    simp [wideFiring, storedFiring, stored, wide] at inside

/-- **No program with a bound on take arity has an admitted firing with the selection of `wide (N+1)`.** -/
theorem no_bounded_one_firing {P : Program Tm} {N : ℕ} (bounded : TakesAtMost P N) (u : State Tm ℕ)
    (g : Firing ℕ Ext P u.frame) (admitted : g.Admits X u) :
    g.selection ≠ (wideFiring (N + 1)).selection := by
  intro same
  have le := taken_le bounded g admitted
  rw [same] at le
  simp [wideFiring, storedFiring] at le

/-- **No finite program interprets every rule firing for firing**: for every finite program there is an
admitted firing of the stored-rule program whose selection no admitted firing of the program has, at
any state. -/
theorem no_finite_one_firing {P : Program Tm} (finite : P.Finite) :
    ∃ n, (wideFiring n).Admits X (wideStore n) ∧
      ∀ (u : State Tm ℕ) (g : Firing ℕ Ext P u.frame), g.Admits X u → g.selection ≠ (wideFiring n).selection := by
  obtain ⟨N, bounded⟩ := finite_takesAtMost finite
  exact ⟨N + 1, wideFiring_admitted (N + 1), no_bounded_one_firing bounded⟩

/-- **In particular, no finite part of `U` does.** -/
theorem upTo_not_universal (N : ℕ) :
    ∃ n, (wideFiring n).Admits X (wideStore n) ∧
      ∀ (u : State Tm ℕ) (g : Firing ℕ Ext (UpTo N) u.frame), g.Admits X u →
        g.selection ≠ (wideFiring n).selection :=
  no_finite_one_firing (upTo_finite N)

/-! ## Self-application -/

/-- The shape with no entries. -/
def emptyShape : Shape := ⟨0, 0, 0, 0, [], 0⟩

theorem opened_not_dropFree (v : ℕ) : (opened v).dropFree = false := rfl

/-- **An interpreter rule is in the fragment exactly when its shape is empty**: every entry of a
non-empty shape is dropped at the environment. -/
theorem interp_fragment_iff (sh : Shape) : Fragment (interp sh) ↔ sh = emptyShape := by
  constructor
  · intro frag
    have entry : ∀ k, 0 < sh.len k → opened (slotVar k 0) ∈ openedColumn sh k := fun k positive =>
      List.mem_map.mpr ⟨0, List.mem_range.mpr positive, rfl⟩
    have zero : ∀ k, (∀ t ∈ openedColumn sh k, t.dropFree) → sh.len k = 0 := by
      intro k all
      by_contra nonzero
      have := all _ (entry k (Nat.pos_of_ne_zero nonzero))
      rw [opened_not_dropFree] at this
      exact Bool.false_ne_true this
    have takes : sh.len 0 = 0 := zero 0 frag.take
    have reads : sh.len 1 = 0 := zero 1 fun t inside => frag.read t (List.mem_cons_of_mem _ inside)
    have makes : sh.len 2 = 0 := zero 2 frag.produce
    have tells : sh.len 3 = 0 := by
      by_contra nonzero
      have positive := Nat.pos_of_ne_zero nonzero
      have pair : (opened (slotVar 3 0), opened (slotVar 4 0)) ∈
          (openedColumn sh 3).zip (openedColumn sh 4) := by
        have below : 0 < ((openedColumn sh 3).zip (openedColumn sh 4)).length := by
          simpa [length_openedColumn, Shape.len] using positive
        have member := List.getElem_mem below
        rw [List.getElem_zip, getElem_openedColumn, getElem_openedColumn] at member
        exact member
      have := (frag.tell _ pair).1
      rw [opened_not_dropFree] at this
      exact Bool.false_ne_true this
    have collect : sh.len 8 = 0 := zero 8 frag.collect
    have kinds : sh.kinds = [] := by
      cases hk : sh.kinds with
      | nil => rfl
      | cons k rest =>
          exfalso
          have member : k.check (opened (slotVar 5 0)) (opened (slotVar 6 0)) ∈ (interp sh).body.checks := by
            show _ ∈ sh.kinds.mapIdx _
            rw [hk, List.mapIdx_cons]
            exact List.mem_cons_self
          have free := frag.check _ member (opened (slotVar 5 0)) (by cases k <;> simp [Kind.check, checkTerms])
          rw [opened_not_dropFree] at free
          exact Bool.false_ne_true free
    cases sh
    simp only [Shape.len] at takes reads makes tells collect
    simp only at kinds
    simp [emptyShape, takes, reads, makes, tells, kinds, collect]
  · rintro rfl
    exact Examples.fragment_of_check (by decide)

/-- **`U` is not a program of the fragment**: its rule of shape `⟨1, 0, 0, 0, [], 0⟩` drops an entry. -/
theorem U_not_fragment : ¬ ∀ q ∈ U, Fragment q := by
  intro all
  have frag := all (interp ⟨1, 0, 0, 0, [], 0⟩) ⟨_, rfl⟩
  have := (interp_fragment_iff _).mp frag
  simp [emptyShape] at this

/-- **The one rule of `U` in the fragment does nothing**: the empty-shape rule reads a code row and
takes, tells, checks, makes and sees nothing. -/
theorem interp_empty_idle :
    (interp emptyShape).body.take = [] ∧ (interp emptyShape).body.produce = [] ∧
      (interp emptyShape).body.tell = [] ∧ (interp emptyShape).body.checks = [] ∧
      (interp emptyShape).collect = [] ∧ (interp emptyShape).body.read = [codePattern emptyShape] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **`U` interprets the code of its own empty-shape rule**: it is a rule of the data fragment, so its
stored form is a rule of the stored-rule program. -/
theorem stored_interp_empty :
    interp emptyShape ∈ Examples.DataFragment ∧
      stored (interp emptyShape) ∈ Stored Examples.DataFragment :=
  have mem : interp emptyShape ∈ Examples.DataFragment :=
    ⟨(interp_fragment_iff emptyShape).mpr rfl, fun m inside => by
      simp [interp, openedColumn, emptyShape, Shape.len] at inside⟩
  ⟨mem, ⟨_, mem, rfl⟩⟩

#print axioms admitted_shape
#print axioms readShape_interp
#print axioms interp_injective
#print axioms mem_U_iff
#print axioms count_rules_injective
#print axioms entriesAtMostOne_infinite
#print axioms interp_empty_idle
#print axioms upTo_finite
#print axioms bisimulation_upTo
#print axioms finite_takesAtMost
#print axioms taken_le
#print axioms wideFiring_admitted
#print axioms no_bounded_one_firing
#print axioms no_finite_one_firing
#print axioms upTo_not_universal
#print axioms interp_fragment_iff
#print axioms U_not_fragment
#print axioms stored_interp_empty

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows
