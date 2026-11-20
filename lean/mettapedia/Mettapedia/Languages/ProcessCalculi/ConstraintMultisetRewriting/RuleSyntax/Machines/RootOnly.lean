import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines.TermRewriting

/-!
# Rewriting inside terms is the rewriting of no finite list of range-restricted rules on one-row bags

`Machines.TermRewriting` hosts **root** rewriting: a step rewrites the whole row. This module shows that the
usual rewriting of terms, at any position, is not of that kind.

* `CtxStep`: the rewriting of `sym 0` into `sym 1` at any position of a row.
* `not_rewrites_deep`: a finite list of range-restricted rules whose take and made patterns have height at
  most `n` does not rewrite the one-row bag of `code^n (sym 0)` to that of `code^n (sym 1)`: a pattern of
  that height reaches the leaf only through an unknown, and the made row's unknowns are the taken row's.
* `contextual_not_finite`: so no finite list of range-restricted rules rewrites one-row bags as `CtxStep`,
  and (`contextual_not_root`) no finite list of schemas whose right unknowns occur on the left has
  `CtxStep` as its root rewriting.
* Control: `ctxStep_deep`, the rewrite at depth `n` is a step of `CtxStep`.

These are statements about `Rewrites`, which is the step for range-restricted positive programs
(`Machines.NoneReading`). A finite program can host rewriting at depth only by a machine that walks the
row, with many firings per rewrite; no such machine is built here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines.RootOnly

open Mettapedia.Logic.LP
open NamesOnTheStep (Expr)
open Presentation.Schematic

/-! ## Rewriting at any position -/

/-- **One rewrite of `sym 0` into `sym 1` at any position of a row.** -/
inductive CtxStep : Expr → Expr → Prop
  | root : CtxStep (.sym 0) (.sym 1)
  | code {e e' : Expr} : CtxStep e e' → CtxStep (.code e) (.code e')
  | appLeft {f f' a : Expr} : CtxStep f f' → CtxStep (.app f a) (.app f' a)
  | appRight {f a a' : Expr} : CtxStep a a' → CtxStep (.app f a) (.app f a')

/-- A row under `n` code formers. -/
def codes : ℕ → Expr → Expr
  | 0, e => e
  | n + 1, e => .code (codes n e)

/-- **Control: the rewrite at depth `n` is a step.** -/
theorem ctxStep_deep : ∀ n : ℕ, CtxStep (codes n (.sym 0)) (codes n (.sym 1))
  | 0 => .root
  | n + 1 => .code (ctxStep_deep n)

/-- The constant `sym k` occurs in a row. -/
def Mentions (k : ℕ) : Expr → Prop
  | .sym j => j = k
  | .name _ => False
  | .app f a => Mentions k f ∨ Mentions k a
  | .code e => Mentions k e

theorem mentions_codes (k j : ℕ) : ∀ n : ℕ, Mentions k (codes n (.sym j)) ↔ j = k
  | 0 => Iff.rfl
  | n + 1 => mentions_codes k j n

/-- The height of a pattern: unknowns have height `0`. -/
def height : Tm → ℕ
  | .var _ => 0
  | .const _ => 1
  | .app .app ts => max (height (ts head)) (height (ts tail)) + 1
  | .app .code ts => height (ts body) + 1

/-- **A pattern whose instance is `code^n (sym j)` is a chain of codes ending in one unknown, which the
instantiation sends to a row ending in `sym j`, or it is at least `n + 1` high.** -/
theorem chain_of_inst (θ : ℕ → Expr) (j : ℕ) : ∀ (n : ℕ) (p : Tm), inst θ p = codes n (.sym j) →
    (∃ x, unknowns p = [x] ∧ Mentions j (θ x)) ∨ n + 1 ≤ height p
  | n, .var x, same => Or.inl ⟨x, rfl, by
      show Mentions j (inst θ (.var x))
      rw [same, mentions_codes]⟩
  | 0, .const (.sym _), _ => Or.inr (le_refl _)
  | n + 1, .const (.sym _), same => by cases same
  | 0, .const (.name _), same => by cases same
  | n + 1, .const (.name _), same => by cases same
  | 0, .app .app _, same => by cases same
  | n + 1, .app .app _, same => by cases same
  | 0, .app .code _, same => by cases same
  | n + 1, .app .code ts, same => by
      have inner : inst θ (ts body) = codes n (.sym j) := Expr.code.inj same
      rcases chain_of_inst θ j n (ts body) inner with ⟨x, only, mentions⟩ | high
      · exact Or.inl ⟨x, only, mentions⟩
      · exact Or.inr (show n + 1 + 1 ≤ height (ts body) + 1 by omega)

/-- **The unknowns of a pattern whose instance is `code^n (sym 1)` are sent to rows without `sym 0`**, and a
pattern without unknowns is at least `n + 1` high. -/
theorem made_of_inst (θ : ℕ → Expr) : ∀ (n : ℕ) (q : Tm), inst θ q = codes n (.sym 1) →
    (∀ x ∈ unknowns q, ¬ Mentions 0 (θ x)) ∧ (unknowns q = [] → n + 1 ≤ height q)
  | n, .var x, same => ⟨fun y inside => by
      rw [List.mem_singleton.mp inside]
      show ¬ Mentions 0 (inst θ (.var x))
      rw [same, mentions_codes]
      omega, fun empty => by cases empty⟩
  | 0, .const (.sym _), _ => ⟨fun _ inside => absurd inside List.not_mem_nil, fun _ => le_refl _⟩
  | n + 1, .const (.sym _), same => by cases same
  | 0, .const (.name _), same => by cases same
  | n + 1, .const (.name _), same => by cases same
  | 0, .app .app _, same => by cases same
  | n + 1, .app .app _, same => by cases same
  | 0, .app .code _, same => by cases same
  | n + 1, .app .code ts, same => by
      have inner : inst θ (ts body) = codes n (.sym 1) := Expr.code.inj same
      obtain ⟨clean, high⟩ := made_of_inst θ n (ts body) inner
      exact ⟨clean, fun empty => show n + 1 + 1 ≤ height (ts body) + 1 by
        have := high empty
        omega⟩

/-! ## No finite list -/

/-- The height of a list of patterns. -/
def listHeight (l : List Tm) : ℕ := (l.map height).foldr max 0

/-- **The height of a program**: the highest of its take and made patterns. -/
def programHeight (rules : List SRule) : ℕ :=
  (rules.map fun r => max (listHeight r.body.take) (listHeight r.body.produce)).foldr max 0

theorem height_le_program {rules : List SRule} {r : SRule} (member : r ∈ rules) :
    listHeight r.body.take ≤ programHeight rules ∧ listHeight r.body.produce ≤ programHeight rules := by
  have inRule := le_foldr_max (List.mem_map_of_mem (f := fun r : SRule =>
    max (listHeight r.body.take) (listHeight r.body.produce)) member)
  exact ⟨(le_max_left _ _).trans inRule, (le_max_right _ _).trans inRule⟩

theorem height_le_list {l : List Tm} {t : Tm} (member : t ∈ l) : height t ≤ listHeight l :=
  le_foldr_max (List.mem_map_of_mem member)

/-- **A finite list of range-restricted rules does not rewrite the one-row bag of `code^n (sym 0)` to that of
`code^n (sym 1)`** when its patterns are at most `n` high. -/
theorem not_rewrites_deep (rules : List SRule) (restricted : ∀ r ∈ rules, RangeRestricted r) :
    ¬ Rewrites rules {codes (programHeight rules) (.sym 0)} {codes (programHeight rules) (.sym 1)} := by
  rintro ⟨r, member, θ, rest, split, readsIn, -, made⟩
  set n := programHeight rules
  have different : codes n (.sym 0) ≠ codes n (.sym 1) := fun same => by
    have mentioned : Mentions 0 (codes n (.sym 0)) := (mentions_codes 0 0 n).mpr rfl
    rw [same, mentions_codes] at mentioned
    omega
  match takes : r.body.take with
  | [] =>
      rw [takes] at split
      have restIs : rest = {codes n (.sym 0)} := by simpa using split
      rw [restIs] at made
      have inside : codes n (.sym 0) ∈ ({codes n (.sym 1)} : Multiset Expr) := by
        rw [made]
        exact Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton_self _))
      exact different (Multiset.mem_singleton.mp inside)
  | [p] =>
      rw [takes] at split
      obtain ⟨matched, restZero⟩ := row_of_singleton split
      have noReads : r.body.read = [] := by
        match readList : r.body.read with
        | [] => rfl
        | q :: _ =>
            have inRest := readsIn q (by rw [readList]; exact List.mem_cons_self)
            rw [restZero] at inRest
            exact absurd inRest (Multiset.notMem_zero _)
      rw [restZero, add_zero] at made
      have counted := congrArg Multiset.card made
      rw [Multiset.card_singleton, Multiset.coe_card, List.length_map] at counted
      obtain ⟨q, isQ⟩ := List.length_eq_one_iff.mp counted.symm
      rw [isQ] at made
      have madeQ : inst θ q = codes n (.sym 1) := by
        simpa using made.symm
      have pLow : height p ≤ n :=
        (height_le_list (show p ∈ r.body.take by rw [takes]; exact List.mem_cons_self)).trans
          (height_le_program member).1
      have qLow : height q ≤ n :=
        (height_le_list (show q ∈ r.body.produce by rw [isQ]; exact List.mem_cons_self)).trans
          (height_le_program member).2
      rcases chain_of_inst θ 0 n p matched with ⟨x, only, mentions⟩ | high
      · obtain ⟨clean, ground⟩ := made_of_inst θ n q madeQ
        match unknownsQ : unknowns q with
        | [] => exact absurd (ground unknownsQ) (by omega)
        | y :: _ =>
            have yIn : y ∈ unknowns q := by rw [unknownsQ]; exact List.mem_cons_self
            obtain ⟨t, inPatterns, vars⟩ := restricted r member q
              (mem_written_of_produce (by rw [isQ]; exact List.mem_cons_self)) y
              (vars_of_mem_unknowns q yIn)
            rw [takes, noReads, List.append_nil, List.mem_singleton] at inPatterns
            rw [inPatterns] at vars
            have isX : y = x := by
              have inP := mem_unknowns p vars
              rw [only, List.mem_singleton] at inP
              exact inP
            rw [isX] at yIn
            exact clean x yIn mentions
      · omega
  | _ :: _ :: _ =>
      rw [takes] at split
      have counted := congrArg Multiset.card split
      simp at counted
      omega

/-- **Rewriting inside terms is the rewriting of no finite list of range-restricted rules on one-row bags.** -/
theorem contextual_not_finite :
    ¬ ∃ rules : List SRule, (∀ r ∈ rules, RangeRestricted r) ∧
      ∀ e e', Rewrites rules {e} {e'} ↔ CtxStep e e' := by
  rintro ⟨rules, restricted, same⟩
  exact not_rewrites_deep rules restricted ((same _ _).mpr (ctxStep_deep _))

/-- **No finite list of schemas whose right unknowns occur on the left has rewriting inside terms as its root
rewriting.** -/
theorem contextual_not_root :
    ¬ ∃ schemas : List (Tm × Tm), (∀ p ∈ schemas, ∀ x ∈ unknowns p.2, x ∈ unknowns p.1) ∧
      ∀ e e', RootStep schemas e e' ↔ CtxStep e e' := by
  rintro ⟨schemas, closed, same⟩
  refine contextual_not_finite ⟨rootRules schemas, fun r member => (rootRules_fragment closed r member).2.2,
    fun e e' => ?_⟩
  rw [rewrites_rootRules_iff]
  constructor
  · rintro ⟨e'', rooted, isBag⟩
    rw [Multiset.singleton_inj.mp isBag]
    exact (same _ _).mp rooted
  · intro stepped
    exact ⟨e', (same _ _).mpr stepped, rfl⟩

#print axioms ctxStep_deep
#print axioms chain_of_inst
#print axioms made_of_inst
#print axioms not_rewrites_deep
#print axioms contextual_not_finite
#print axioms contextual_not_root

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines.RootOnly
