import Mettapedia.GSLT.Core.WeightOrderedSelection
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Vector.Defs

/-!
# Priority ordering by explicit keys

Shortlex order on lists over a well-founded alphabet is well-founded.  When
the alphabet is finite, the keys strictly below a given key inject into the
finite type of lists no longer than that key.  Least-key selection is then
fair on the same hypothesis as best-first selection: an explicit finite bucket
of generated nodes at or below the target key, and no return of a selected
bucket node.

Plain lexicographic order is not well-founded.  The lists `1`, `01`, `001`, …
descend forever, and a least-key scheduler on that chain starves a sibling
whose key is `1`.  That scheduler ranks by the reflexive lexicographic order
of the encoded keys: equal keys tie, and a strictly smaller key precedes.
The same chain ascends in shortlex order, so the shortlex scheduler emits
that sibling.

A byte encoding used by key-ordered execution puts an arity tag in `0..63`
and a symbol tag in `192..255`.  Under lexicographic order on those bytes,
`(s (s a))` precedes `(s a)`, which precedes `b`.  Deeper applications can
therefore starve an execution whose key is `b`.  This models the key order
only.  It is not a proof about MORK's code.
-/

namespace Mettapedia.GSLT.Core.PriorityKeyOrder

open Mettapedia.GSLT.Core.BranchingTemporal
open Mettapedia.GSLT.Core.WeightOrderedSelection
open Mettapedia.GSLT.Core.AgeProtectedSchedule
open Mettapedia.GSLT.Core.WeightedOccurrenceControl

/-! ## Shortlex and fixed-length lexicographic order -/

/-- Strict shortlex order: a shorter list precedes a longer one, and equal
lengths are compared lexicographically. -/
def ShortlexLt (r : α → α → Prop) (as bs : List α) : Prop :=
  as.length < bs.length ∨ as.length = bs.length ∧ List.Lex r as bs

/-- Reflexive shortlex order, used as a total rank by insertion sort. -/
def ShortlexLe (r : α → α → Prop) (as bs : List α) : Prop :=
  as = bs ∨ ShortlexLt r as bs

/-- Lexicographic order on lists of one fixed length. -/
def FixedLex (r : α → α → Prop) (n : Nat)
    (as bs : {l : List α // l.length = n}) : Prop :=
  List.Lex r as.1 bs.1

theorem list_lex_trans {r : α → α → Prop} [IsTrans α r] {as bs cs : List α}
    (hab : List.Lex r as bs) (hbc : List.Lex r bs cs) : List.Lex r as cs := by
  induction hab generalizing cs with
  | nil =>
      cases cs with
      | nil => cases hbc
      | cons _ _ => exact List.Lex.nil
  | rel hr =>
      cases hbc with
      | rel hr2 => exact List.Lex.rel (trans_of r hr hr2)
      | cons _ => exact List.Lex.rel hr
  | cons htail ih =>
      cases hbc with
      | rel hr => exact List.Lex.rel hr
      | cons htail2 => exact List.Lex.cons (ih htail2)

theorem shortlexLt_trans {r : α → α → Prop} [IsTrans α r] {as bs cs : List α}
    (hab : ShortlexLt r as bs) (hbc : ShortlexLt r bs cs) : ShortlexLt r as cs := by
  rcases hab with hab | ⟨hablen, hab⟩
  · rcases hbc with hbc | ⟨hbclen, _⟩
    · exact Or.inl (Nat.lt_trans hab hbc)
    · exact Or.inl (by simpa [hbclen] using hab)
  · rcases hbc with hbc | ⟨hbclen, hbc⟩
    · exact Or.inl (by simpa [hablen] using hbc)
    · exact Or.inr ⟨hablen.trans hbclen, list_lex_trans hab hbc⟩

theorem shortlexLe_trans {r : α → α → Prop} [IsTrans α r] {as bs cs : List α}
    (hab : ShortlexLe r as bs) (hbc : ShortlexLe r bs cs) : ShortlexLe r as cs := by
  rcases hab with rfl | hab
  · exact hbc
  rcases hbc with rfl | hbc
  · exact Or.inr hab
  · exact Or.inr (shortlexLt_trans hab hbc)

theorem fin_trichotomy {n : Nat} (a b : Fin n) : a < b ∨ a = b ∨ b < a := by
  rcases Nat.lt_trichotomy a.val b.val with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr h)

/-- Reflexive lexicographic order is total when the element order is trichotomous. -/
theorem list_lexLe_total {α : Type _} {r : α → α → Prop}
    (htri : ∀ a b, r a b ∨ a = b ∨ r b a) (as bs : List α) :
    (as = bs ∨ List.Lex r as bs) ∨ (bs = as ∨ List.Lex r bs as) := by
  induction as generalizing bs with
  | nil =>
      cases bs with
      | nil => exact Or.inl (Or.inl rfl)
      | cons _ _ => exact Or.inl (Or.inr List.Lex.nil)
  | cons a ta ih =>
      cases bs with
      | nil => exact Or.inr (Or.inr List.Lex.nil)
      | cons b tb =>
          rcases htri a b with hab | hab | hab
          · exact Or.inl (Or.inr (List.Lex.rel hab))
          · subst hab
            rcases ih tb with hle | hle
            · rcases hle with rfl | hlex
              · exact Or.inl (Or.inl rfl)
              · exact Or.inl (Or.inr (List.Lex.cons hlex))
            · rcases hle with rfl | hlex
              · exact Or.inl (Or.inl rfl)
              · exact Or.inr (Or.inr (List.Lex.cons hlex))
          · exact Or.inr (Or.inr (List.Lex.rel hab))

theorem shortlexLe_total {r : α → α → Prop} [DecidableEq α] [DecidableRel r]
    (htri : ∀ a b, r a b ∨ a = b ∨ r b a) (as bs : List α) :
    ShortlexLe r as bs ∨ ShortlexLe r bs as := by
  induction as generalizing bs with
  | nil =>
      cases bs with
      | nil => exact Or.inl (Or.inl rfl)
      | cons _ _ => exact Or.inl (Or.inr (Or.inl (by simp)))
  | cons a ta ih =>
      cases bs with
      | nil => exact Or.inr (Or.inr (Or.inl (by simp)))
      | cons b tb =>
          by_cases hlt : (a :: ta).length < (b :: tb).length
          · exact Or.inl (Or.inr (Or.inl hlt))
          · by_cases hgt : (b :: tb).length < (a :: ta).length
            · exact Or.inr (Or.inr (Or.inl hgt))
            · have heqLen : (a :: ta).length = (b :: tb).length := by omega
              have htail : ta.length = tb.length := by
                simp at heqLen
                omega
              rcases htri a b with hab | hab | hab
              · exact Or.inl (Or.inr (Or.inr ⟨heqLen, List.Lex.rel hab⟩))
              · subst hab
                rcases ih tb with hle | hle
                · rcases hle with rfl | hltTail
                  · exact Or.inl (Or.inl rfl)
                  · rcases hltTail with hlen | ⟨_, hlex⟩
                    · exact False.elim (by omega)
                    · exact Or.inl (Or.inr (Or.inr ⟨heqLen, List.Lex.cons hlex⟩))
                · rcases hle with rfl | hltTail
                  · exact Or.inl (Or.inl rfl)
                  · rcases hltTail with hlen | ⟨_, hlex⟩
                    · exact False.elim (by omega)
                    · exact Or.inr (Or.inr (Or.inr ⟨heqLen.symm, List.Lex.cons hlex⟩))
              · exact Or.inr (Or.inr (Or.inr ⟨heqLen.symm, List.Lex.rel hab⟩))

instance shortlexLeTrans {r : α → α → Prop} [IsTrans α r] :
    IsTrans (List α) (ShortlexLe r) :=
  ⟨fun _ _ _ => shortlexLe_trans⟩

instance shortlexLeTotal {n : Nat} : Std.Total (ShortlexLe (α := Fin n) (· < ·)) :=
  ⟨fun as bs => shortlexLe_total fin_trichotomy as bs⟩

instance listLexDecidable [DecidableEq α] (r : α → α → Prop) [DecidableRel r] :
    DecidableRel (List.Lex r) :=
  List.decidableLex r

instance shortlexLeDecidable [DecidableEq α] (r : α → α → Prop) [DecidableRel r] :
    DecidableRel (ShortlexLe r) := fun as bs =>
  if heq : as = bs then isTrue (Or.inl heq)
  else if hlt : as.length < bs.length then isTrue (Or.inr (Or.inl hlt))
  else if heql : as.length = bs.length then
    match List.decidableLex r as bs with
    | isTrue hlex => isTrue (Or.inr (Or.inr ⟨heql, hlex⟩))
    | isFalse hlex => isFalse (by
        intro hle
        rcases hle with h | h
        · exact heq h
        · rcases h with hlen | ⟨_, hrel⟩
          · omega
          · exact hlex hrel)
  else isFalse (by
        intro hle
        rcases hle with h | h
        · exact heq h
        · rcases h with hlen | ⟨heqlen, _⟩
          · exact hlt hlen
          · exact heql heqlen)

instance finLtTrans (n : Nat) : IsTrans (Fin n) (· < ·) :=
  ⟨fun _ _ _ => lt_trans⟩

/-! ## Well-founded shortlex -/

def splitSucc {α : Type _} {n : Nat} (p : {l : List α // l.length = n + 1}) :
    α × {l : List α // l.length = n} :=
  (p.1.head (List.ne_nil_of_length_pos (by simp [p.2])),
    ⟨p.1.tail, by
      have hlen : p.1.length = n + 1 := p.2
      have ht : p.1.tail.length = p.1.length - 1 := List.length_tail
      omega⟩)

theorem fixedLex_split {r : α → α → Prop} {n : Nat}
    {p q : {l : List α // l.length = n + 1}} (h : FixedLex r (n + 1) p q) :
    Prod.Lex r (FixedLex r n) (splitSucc p) (splitSucc q) := by
  rcases p with ⟨pl, hp⟩
  rcases q with ⟨ql, hq⟩
  cases pl with
  | nil => simp at hp
  | cons a t =>
      cases ql with
      | nil => simp at hq
      | cons b s =>
          have ht : t.length = n := by simpa using hp
          have hs : s.length = n := by simpa using hq
          suffices Prod.Lex r (FixedLex r n) (a, ⟨t, ht⟩) (b, ⟨s, hs⟩) by
            simpa [splitSucc, List.head_cons, List.tail_cons] using this
          rw [Prod.lex_def]
          cases h with
          | rel hr =>
              exact Or.inl (by simpa [splitSucc, List.head_cons] using hr)
          | cons htail =>
              exact Or.inr ⟨rfl,
                by simpa [FixedLex] using htail⟩

theorem fixedLex_wf {r : α → α → Prop} (hr : WellFounded r) (n : Nat) :
    WellFounded (FixedLex r n) := by
  induction n with
  | zero =>
      refine ⟨fun p => ?_⟩
      apply Acc.intro
      intro q h
      rcases p with ⟨pl, hp⟩
      rcases q with ⟨ql, hq⟩
      have hpl : pl = [] := List.length_eq_zero_iff.mp hp
      have hql : ql = [] := List.length_eq_zero_iff.mp hq
      subst hpl
      subst hql
      cases h
  | succ n ih =>
      have hprod : WellFounded (Prod.Lex r (FixedLex r n)) :=
        (Prod.lex ⟨r, hr⟩ ⟨FixedLex r n, ih⟩).wf
      exact Subrelation.wf (fun h => fixedLex_split h) (InvImage.wf splitSucc hprod)

/-- A list is accessible for shortlex order.  Shorter lists are reached by the
outer induction; equal length uses fixed-length lexicographic order. -/
theorem shortlex_acc {r : α → α → Prop} (hr : WellFounded r) :
    ∀ (n : Nat) (l : List α), l.length ≤ n → Acc (ShortlexLt r) l := by
  intro n
  induction n with
  | zero =>
      intro l hl
      have hl0 : l.length = 0 := Nat.le_zero.mp hl
      apply Acc.intro l
      intro q hq
      rcases hq with hlen | ⟨heq, hlex⟩
      · simp [hl0] at hlen
      · have hq0 : q = [] := List.length_eq_zero_iff.mp (heq.trans hl0)
        have hlEmpty : l = [] := List.length_eq_zero_iff.mp hl0
        subst hq0
        subst hlEmpty
        cases hlex
  | succ n ih =>
      intro l hl
      cases Nat.eq_or_lt_of_le hl with
      | inr hlt => exact ih l (Nat.le_of_lt_succ hlt)
      | inl heq =>
          suffices ∀ q : {t : List α // t.length = n + 1},
              Acc (FixedLex r (n + 1)) q → Acc (ShortlexLt r) q.1 by
            exact this ⟨l, heq⟩ ((fixedLex_wf hr (n + 1)).apply ⟨l, heq⟩)
          intro q hq
          refine Acc.rec (motive := fun node _ => Acc (ShortlexLt r) node.1) ?_ hq
          intro node _ ihf
          apply Acc.intro node.1
          intro s hs
          rcases hs with hlen | ⟨heqLen, hlex⟩
          · have hsle : s.length ≤ n := by
              have hlenNode : node.1.length = n + 1 := node.2
              omega
            exact ih s hsle
          · exact ihf ⟨s, heqLen.trans node.2⟩ hlex

/-- Shortlex order over a well-founded alphabet is well-founded. -/
theorem shortlexLt_wellFounded {r : α → α → Prop} (hr : WellFounded r) :
    WellFounded (ShortlexLt r) :=
  ⟨fun l => shortlex_acc hr l.length l (Nat.le_refl _)⟩

theorem fin_lt_wellFounded (n : Nat) : WellFounded (· < · : Fin n → Fin n → Prop) :=
  InvImage.wf (fun i : Fin n => i.val) Nat.lt_wfRel.wf

theorem shortlex_fin_wellFounded (n : Nat) :
    WellFounded (ShortlexLt (α := Fin n) (· < ·)) :=
  shortlexLt_wellFounded (fin_lt_wellFounded n)

/-! ## Finitely many shorter keys, without converting finiteness into a list -/

/-- Lists of length at most `n`, indexed by that length.  When the alphabet
has a finite enumeration, this type does too. -/
def BelowBound (α : Type _) (n : Nat) :=
  Σ k : Fin (n + 1), List.Vector α k.val

def embedBelow {α : Type _} (n : Nat) (l : List α) (h : l.length ≤ n) : BelowBound α n :=
  ⟨⟨l.length, Nat.lt_succ_of_le h⟩, ⟨l, rfl⟩⟩

theorem shortlexLt_length_le {r : α → α → Prop} {as bs : List α}
    (h : ShortlexLt r as bs) : as.length ≤ bs.length := by
  rcases h with h | ⟨h, _⟩
  · exact Nat.le_of_lt h
  · exact Nat.le_of_eq h

/-- Every key strictly below `key` in shortlex order injects into the finite
type of lists no longer than `key`. -/
theorem shortlex_below_injective {r : α → α → Prop} (key : List α) :
    Function.Injective
      (fun item : {t : List α // ShortlexLt r t key} =>
        embedBelow key.length item.1 (shortlexLt_length_le item.2)) := by
  intro x y h
  have hpayload :=
    congrArg (fun bound : BelowBound α key.length => bound.2.val) h
  apply Subtype.ext
  simpa [embedBelow] using hpayload

instance belowBoundFintype [Fintype α] (n : Nat) : Fintype (BelowBound α n) := by
  dsimp [BelowBound]
  infer_instance

/-- Least-key selection reaches a live root when every generated node whose
key is shortlex-at-most the target belongs to an explicit list, and a selected
node from that list does not return.  The list is the finite fiber data; it
is not manufactured from a finiteness proof. -/
theorem least_key_selects {Node Answer α : Type _} [DecidableEq Node]
    (key : Node → List α) (r : α → α → Prop)
    [DecidableRel (ShortlexLe r)] [IsTrans (List α) (ShortlexLe r)] [Std.Total (ShortlexLe r)]
    (system : BranchingSystem Node Answer) (roots : List Node) {target : Node}
    (hroot : target ∈ roots) (bucket : List Node)
    (bucket_complete : ∀ node, Generated system roots node →
      ShortlexLe r (key node) (key target) → node ∈ bucket)
    (noreturn : ∀ index node,
      choiceAt (fun left right => ShortlexLe r (key left) (key right)) system roots index =
          some node →
        node ∈ bucket →
        ∀ extra,
          node ∉ (run system
            (orderScheduler (fun left right => ShortlexLe r (key left) (key right)))
            (index + 1 + extra) (initial roots)).frontier) :
    ∃ fuel,
      choiceAt (fun left right => ShortlexLe r (key left) (key right))
        system roots fuel = some target := by
  let rankDec : DecidableRel (fun left right => ShortlexLe r (key left) (key right)) :=
    fun left right =>
      (inferInstance : DecidableRel (ShortlexLe r)) (key left) (key right)
  exact @least_first_selects Node Answer _
    (fun left right => ShortlexLe r (key left) (key right)) rankDec
    ⟨fun _ _ _ hab hbc => trans_of (ShortlexLe r) hab hbc⟩
    ⟨fun left right => Std.Total.total (r := ShortlexLe r) (key left) (key right)⟩
    system roots _ hroot bucket bucket_complete noreturn

/-! ## Lexicographic order is not well-founded -/

/-- `chain n` is `n` zeros followed by a one. -/
def chain (n : Nat) : List (Fin 2) := List.replicate n 0 ++ [1]

theorem chain_succ (n : Nat) : chain (n + 1) = 0 :: chain n := by
  simp [chain, List.replicate_succ]

theorem chain_lex_pred (n : Nat) : List.Lex (· < ·) (chain (n + 1)) (chain n) := by
  induction n with
  | zero =>
      rw [chain_succ, chain]
      simp
      exact List.Lex.rel (by decide : (0 : Fin 2) < 1)
  | succ n ih =>
      rw [chain_succ (n + 1), chain_succ n]
      exact List.Lex.cons ih

theorem chain_length (n : Nat) : (chain n).length = n + 1 := by
  simp [chain, List.length_append, List.length_replicate]

/-- A longer chain is strictly lexicographically smaller. -/
theorem chain_lex_add (j k : Nat) :
    List.Lex (· < ·) (chain (j + (k + 1))) (chain j) := by
  induction k with
  | zero => simpa using chain_lex_pred j
  | succ k ih =>
      have hidx : j + ((k + 1) + 1) = (j + (k + 1)) + 1 := by omega
      rw [hidx]
      exact list_lex_trans (chain_lex_pred (j + (k + 1))) ih

theorem chain_lex_of_gt {i j : Nat} (h : j < i) :
    List.Lex (· < ·) (chain i) (chain j) := by
  have hidx : i = j + ((i - j - 1) + 1) := by omega
  rw [hidx]
  exact chain_lex_add j (i - j - 1)

theorem not_chain_lex_of_le {i j : Nat} (h : i ≤ j) :
    ¬ List.Lex (· < ·) (chain i) (chain j) := by
  intro hlex
  rcases Nat.eq_or_lt_of_le h with rfl | hlt
  · exact List.lex_irrefl (fun x => lt_irrefl x) (chain i) hlex
  · exact List.lex_irrefl (fun x => lt_irrefl x) (chain i)
      (list_lex_trans hlex (chain_lex_of_gt hlt))

theorem chain_lex_iff_gt (i j : Nat) :
    List.Lex (· < ·) (chain i) (chain j) ↔ j < i := by
  constructor
  · intro hlex
    rcases Nat.lt_trichotomy j i with hlt | rfl | hgt
    · exact hlt
    · exact False.elim (List.lex_irrefl (fun x => lt_irrefl x) _ hlex)
    · exact False.elim (not_chain_lex_of_le (Nat.le_of_lt hgt) hlex)
  · exact chain_lex_of_gt

/-- The same chain ascends in shortlex order, because each successor is longer. -/
theorem chain_shortlex_ascends (n : Nat) :
    ShortlexLt (· < ·) (chain n) (chain (n + 1)) := by
  refine Or.inl ?_
  simp [chain, List.length_append, List.length_replicate]

theorem nat_succ_not_acc (n : Nat) : ¬ Acc (fun i j : Nat => i = j + 1) n := by
  intro h
  induction h with
  | intro x _ ih =>
      exact ih (x + 1) rfl

theorem nat_succ_not_wellFounded : ¬ WellFounded (fun i j : Nat => i = j + 1) :=
  fun hwf => nat_succ_not_acc 0 (hwf.apply 0)

/-- Plain lexicographic order has the infinite descent
`chain 0 > chain 1 > chain 2 > …`. -/
theorem lex_not_wellFounded :
    ¬ WellFounded (List.Lex (· < · : Fin 2 → Fin 2 → Prop)) := by
  intro hwf
  have hsub : Subrelation (fun i j : Nat => i = j + 1)
      (InvImage (List.Lex (· < ·)) chain) := by
    intro i j hij
    subst hij
    simpa [InvImage] using chain_lex_pred j
  exact nat_succ_not_wellFounded (Subrelation.wf hsub (InvImage.wf chain hwf))

/-! ## A least-lexicographic scheduler starves the short sibling -/

namespace LexDescend

inductive Work where
  | deep : Nat → Work
  | goal
deriving DecidableEq, Repr

def key : Work → List (Fin 2)
  | .deep n => chain n
  | .goal => [1]

def system : BranchingSystem Work Unit where
  emit
    | .deep _ => none
    | .goal => some ()
  successors
    | .deep n => [.deep (n + 1)]
    | .goal => []

def roots : List Work := [.deep 0, .goal]

/-- Reflexive lexicographic order of the encoded keys.  Equal keys tie, and a
strictly smaller key precedes.  Depth zero and the goal both have key `[1]`. -/
def rank (p q : Work) : Prop :=
  key p = key q ∨ List.Lex (· < ·) (key p) (key q)

instance : DecidableRel rank := fun p q =>
  inferInstanceAs (Decidable (key p = key q ∨ List.Lex (· < ·) (key p) (key q)))

instance : IsTrans Work rank := ⟨fun a b c hab hbc => by
  rcases hab with hab | hab
  · rcases hbc with hbc | hbc
    · exact Or.inl (hab.trans hbc)
    · exact Or.inr (by simpa [hab] using hbc)
  · rcases hbc with hbc | hbc
    · exact Or.inr (by simpa [hbc] using hab)
    · exact Or.inr (list_lex_trans hab hbc)⟩

instance : Std.Total rank := ⟨fun a b =>
  list_lexLe_total (r := (· < · : Fin 2 → Fin 2 → Prop)) fin_trichotomy (key a) (key b)⟩

theorem rank_goal_deep (n : Nat) : rank .goal (.deep n) ↔ n = 0 := by
  constructor
  · intro h
    rcases h with heq | hlex
    · have hlen : (key .goal).length = (key (.deep n)).length := congrArg List.length heq
      simp only [key, chain_length, List.length_singleton] at hlen
      omega
    · cases n with
      | zero =>
          simp only [key, chain, List.replicate_zero, List.nil_append] at hlex
          exact False.elim (List.lex_irrefl (fun (x : Fin 2) => lt_irrefl x) _ hlex)
      | succ n =>
          rw [key, key, chain_succ, List.cons_lex_cons_iff] at hlex
          rcases hlex with hr | ⟨heq, _⟩
          · exact absurd hr (by decide : ¬ ((1 : Fin 2) < 0))
          · exact absurd heq (by decide : (1 : Fin 2) ≠ 0)
  · intro h
    subst h
    exact Or.inl (by simp [key, chain])

theorem rank_deep_goal (n : Nat) : rank (.deep n) .goal := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · exact Or.inl (by simp [key, chain])
  · apply Or.inr
    simpa [key, chain] using chain_lex_of_gt (i := n) (j := 0) hpos

theorem rank_deep_deep (i j : Nat) : rank (.deep i) (.deep j) ↔ j ≤ i := by
  constructor
  · intro h
    rcases h with heq | hlex
    · have hlen : (key (.deep i)).length = (key (.deep j)).length :=
        congrArg List.length heq
      simp only [key, chain_length] at hlen
      omega
    · have hlt : j < i := (chain_lex_iff_gt i j).1 (by simpa [key] using hlex)
      omega
  · intro h
    rcases Nat.eq_or_lt_of_le h with rfl | hlt
    · exact Or.inl rfl
    · exact Or.inr (by simpa [key] using chain_lex_of_gt hlt)

private theorem reorder_keep {a b : Work} (hle : rank a b) :
    (orderScheduler rank).reorder [a, b] = [a, b] := by
  simp only [orderScheduler, List.insertionSort_cons, List.insertionSort_nil,
    List.orderedInsert_cons, List.orderedInsert_nil, hle]
  simp

private theorem reorder_swap {a b : Work} (hnot : ¬ rank a b) :
    (orderScheduler rank).reorder [a, b] = [b, a] := by
  simp only [orderScheduler, List.insertionSort_cons, List.insertionSort_nil,
    List.orderedInsert_cons, List.orderedInsert_nil, hnot]
  simp

theorem deep_before_goal (n : Nat) : rank (.deep (n + 1)) .goal :=
  rank_deep_goal (n + 1)

theorem goal_not_before_deep (n : Nat) : ¬ rank .goal (.deep (n + 1)) := by
  intro h
  have : n + 1 = 0 := (rank_goal_deep (n + 1)).1 h
  omega

theorem sort_goal_deep (n : Nat) :
    (orderScheduler rank).reorder [.goal, .deep (n + 1)] = [.deep (n + 1), .goal] :=
  reorder_swap (goal_not_before_deep n)

theorem sort_deep_goal (n : Nat) :
    (orderScheduler rank).reorder [.deep (n + 1), .goal] = [.deep (n + 1), .goal] :=
  reorder_keep (deep_before_goal n)

theorem step_from_zero :
    run system (orderScheduler rank) 1 (initial roots) = ⟨[], [.goal, .deep 1]⟩ := by
  have hstart : run system (orderScheduler rank) 0 (initial roots) =
      (⟨[], [.deep 0, .goal]⟩ : Snapshot Work Unit) := by
    simp [run, initial, roots]
  rw [run, hstart]
  have htie : rank (.deep 0) .goal := rank_deep_goal 0
  simp only [tick]
  rw [reorder_keep htie]
  simp [system, orderScheduler]
  rfl

theorem step_stable (n : Nat)
    (hprev : run system (orderScheduler rank) (n + 1) (initial roots) =
      ⟨[], [.goal, .deep (n + 1)]⟩) :
    run system (orderScheduler rank) (n + 1 + 1) (initial roots) =
      ⟨[], [.goal, .deep (n + 2)]⟩ := by
  rw [run, hprev]
  simp only [tick]
  rw [sort_goal_deep n]
  simp [system, orderScheduler]
  rfl

theorem open_after (fuel : Nat) :
    run system (orderScheduler rank) (fuel + 1) (initial roots) =
      ⟨[], [.goal, .deep (fuel + 1)]⟩ := by
  induction fuel with
  | zero => exact step_from_zero
  | succ fuel ih => exact step_stable fuel ih

/-- `rank` is the reflexive lexicographic order of the encoded keys. -/
theorem rank_spec (p q : Work) :
    rank p q ↔ key p = key q ∨ List.Lex (· < ·) (key p) (key q) := Iff.rfl

/-- Least-lexicographic selection never emits the goal.  `rank` is the
reflexive lexicographic order of the encoded keys (`rank_spec`), and each
selected node generates a lexicographically smaller key. -/
theorem goal_starves (fuel : Nat) :
    (⟨.goal, ()⟩ : Emission Work Unit) ∉
      (run system (orderScheduler rank) fuel (initial roots)).events := by
  cases fuel with
  | zero => simp [run, initial]
  | succ fuel =>
      rw [open_after fuel]
      simp

/-- Shortlex order on the same keys emits the goal, whose key is the short
end of the chain. -/
def shortRank : Work → Work → Prop
  | .goal, _ => True
  | .deep n, .goal => n = 0
  | .deep i, .deep j => i ≤ j

instance : DecidableRel shortRank := fun left right => by
  cases left <;> cases right <;> (simp [shortRank]; infer_instance)

instance : IsTrans Work shortRank := ⟨fun a b c hab hbc => by
  cases a <;> cases b <;> cases c <;> (simp_all [shortRank]; try omega)⟩

instance : Std.Total shortRank := ⟨fun a b => by
  cases a <;> cases b <;> (simp [shortRank]; try omega)⟩

theorem shortlex_emits_goal :
    (run system (orderScheduler shortRank) 1 (initial [.goal, .deep 1])).events =
      [⟨.goal, ()⟩] := by
  have hstart : run system (orderScheduler shortRank) 0 (initial [.goal, .deep 1]) =
      (⟨[], [.goal, .deep 1]⟩ : Snapshot Work Unit) := by
    simp [run, initial]
  have hle : shortRank .goal (.deep 1) := by simp [shortRank]
  have horder : (orderScheduler shortRank).reorder [.goal, .deep 1] = [.goal, .deep 1] := by
    simp only [orderScheduler, List.insertionSort_cons, List.insertionSort_nil,
      List.orderedInsert_cons, List.orderedInsert_nil, hle]
    simp
  rw [run, hstart]
  simp only [tick]
  rw [horder]
  simp [system]
  rfl

/-- An age lane still selects the goal that least-lexicographic order starves. -/
theorem age_lane_selects_goal :
    ∃ fuel,
      Work.goal ∈
        (PortfolioSnapshot.run system
          (withPriorityShare 1 QueueDiscipline.depthFirst).disciplines fuel
          ((withPriorityShare (Node := Work) 1 QueueDiscipline.depthFirst).initial
            (Answer := Unit) roots 0)).selections :=
  (withPriorityShare (Node := Work) 1 QueueDiscipline.depthFirst).eventually_selects_root
    system roots 0 (by simp [roots])

end LexDescend

/-! ## Two key functions, one branching system -/

namespace TwoKeys

inductive Node where
  | left
  | right
deriving DecidableEq, Repr

def system : BranchingSystem Node Unit where
  emit
    | .left => some ()
    | .right => some ()
  successors
    | _ => []

def keyAlpha : Node → List (Fin 2)
  | .left => [0]
  | .right => [1]

def keyBeta : Node → List (Fin 2)
  | .left => [1]
  | .right => [0]

def rankAlpha : Node → Node → Prop
  | .left, _ => True
  | .right, .left => False
  | .right, .right => True

def rankBeta : Node → Node → Prop
  | .right, _ => True
  | .left, .right => False
  | .left, .left => True

instance : DecidableRel rankAlpha := fun p q => by
  cases p <;> cases q <;> (simp [rankAlpha]; infer_instance)

instance : DecidableRel rankBeta := fun p q => by
  cases p <;> cases q <;> (simp [rankBeta]; infer_instance)

instance : IsTrans Node rankAlpha := ⟨fun a b c hab hbc => by
  cases a <;> cases b <;> cases c <;> simp_all [rankAlpha]⟩

instance : IsTrans Node rankBeta := ⟨fun a b c hab hbc => by
  cases a <;> cases b <;> cases c <;> simp_all [rankBeta]⟩

instance : Std.Total rankAlpha := ⟨fun a b => by
  cases a <;> cases b <;> simp [rankAlpha]⟩

instance : Std.Total rankBeta := ⟨fun a b => by
  cases a <;> cases b <;> simp [rankBeta]⟩

theorem alpha_heads :
    ((orderScheduler rankAlpha).reorder [.left, .right]).head? = some .left := by
  have hle : rankAlpha .left .right := by simp [rankAlpha]
  simp only [orderScheduler, List.insertionSort_cons, List.insertionSort_nil,
    List.orderedInsert_cons, List.orderedInsert_nil, hle]
  simp

theorem beta_heads :
    ((orderScheduler rankBeta).reorder [.left, .right]).head? = some .right := by
  have hnot : ¬ rankBeta .left .right := by simp [rankBeta]
  simp only [orderScheduler, List.insertionSort_cons, List.insertionSort_nil,
    List.orderedInsert_cons, List.orderedInsert_nil, hnot]
  simp

/-- The same frontier, ordered by two key functions, yields two different
heads.  Both results are permutations, so a key is a promise about order and
not a deletion. -/
theorem keys_select_different_heads :
    ((orderScheduler rankAlpha).reorder [.left, .right]).head? = some .left ∧
      ((orderScheduler rankBeta).reorder [.left, .right]).head? = some .right ∧
      ((orderScheduler rankAlpha).reorder [.left, .right]).Perm [.left, .right] ∧
      ((orderScheduler rankBeta).reorder [.left, .right]).Perm [.left, .right] := by
  refine ⟨alpha_heads, beta_heads, ?_, ?_⟩
  · exact (orderScheduler rankAlpha).reorder_complete _
  · exact (orderScheduler rankBeta).reorder_complete _

theorem alpha_is_key_order (p q : Node) :
    rankAlpha p q ↔ ShortlexLe (· < ·) (keyAlpha p) (keyAlpha q) := by
  cases p <;> cases q <;> simp [rankAlpha, keyAlpha, ShortlexLe, ShortlexLt, List.Lex.rel]

theorem beta_is_key_order (p q : Node) :
    rankBeta p q ↔ ShortlexLe (· < ·) (keyBeta p) (keyBeta q) := by
  cases p <;> cases q <;> simp [rankBeta, keyBeta, ShortlexLe, ShortlexLt, List.Lex.rel]

end TwoKeys

/-! ## Byte keys: arity tags before symbol tags -/

namespace ByteKey

abbrev Symbol := Fin 64

def arityByte (arity : Fin 64) : Fin 256 := ⟨arity.val, by omega⟩

def symbolByte (name : Symbol) : Fin 256 := ⟨192 + name.val, by omega⟩

theorem arity_before_symbol (arity name : Fin 64) : arityByte arity < symbolByte name := by
  simp [arityByte, symbolByte]
  omega

inductive Expr where
  | atom : Symbol → Expr
  | app : Symbol → Expr → Expr
deriving DecidableEq, Repr

/-- Tag byte, then the encoded children.  An application of one argument is
an arity tag of `1`, the operator symbol, and the argument key.  An atom is
only its symbol tag. -/
def key : Expr → List (Fin 256)
  | .atom name => [symbolByte name]
  | .app head arg => [arityByte 1, symbolByte head] ++ key arg

theorem key_app (head : Symbol) (arg : Expr) :
    key (.app head arg) = arityByte 1 :: symbolByte head :: key arg := by
  simp [key]

/-- Deeper application keys precede shallower ones, and a shallow application
precedes an atom, because an arity tag is below every symbol tag. -/
theorem deeper_before_shallower (s a b : Symbol) :
    List.Lex (· < ·) (key (.app s (.app s (.atom a)))) (key (.app s (.atom a))) ∧
      List.Lex (· < ·) (key (.app s (.atom a))) (key (.atom b)) := by
  refine ⟨?_, ?_⟩
  · rw [key_app, key_app]
    exact List.Lex.cons (List.Lex.cons (List.Lex.rel (arity_before_symbol 1 a)))
  · rw [key_app]
    exact List.Lex.rel (arity_before_symbol 1 b)

def wrapped (s a : Symbol) : Nat → Expr
  | 0 => .atom a
  | n + 1 => .app s (wrapped s a n)

theorem wrapped_descends (s a : Symbol) (n : Nat) :
    List.Lex (· < ·) (key (wrapped s a (n + 1))) (key (wrapped s a n)) := by
  induction n with
  | zero =>
      simp [wrapped, key_app]
      exact List.Lex.rel (arity_before_symbol 1 a)
  | succ n ih =>
      have hleft : key (wrapped s a ((n + 1) + 1)) =
          arityByte 1 :: symbolByte s :: key (wrapped s a (n + 1)) := by
        simp [wrapped, key_app]
      have hright : key (wrapped s a (n + 1)) =
          arityByte 1 :: symbolByte s :: key (wrapped s a n) := by
        simp [wrapped, key_app]
      rw [hleft, hright]
      exact List.Lex.cons (List.Lex.cons ih)

/-- Shortlex order reverses the descent: a deeper application is longer, so
it follows the shallower key. -/
theorem wrapped_shortlex_ascends (s a : Symbol) (n : Nat) :
    ShortlexLt (· < ·) (key (wrapped s a n)) (key (wrapped s a (n + 1))) := by
  refine Or.inl ?_
  induction n with
  | zero =>
      simp [wrapped, key, key_app]
  | succ n ih =>
      simp [wrapped, key_app, List.length_cons] at ih ⊢

theorem wrapped_key_length (s a : Symbol) (n : Nat) :
    (key (wrapped s a n)).length = 1 + 2 * n := by
  induction n with
  | zero => simp [wrapped, key]
  | succ n ih =>
      simp [wrapped, key_app, List.length_cons, ih]
      omega

/-- A deeper wrap is strictly lexicographically smaller. -/
theorem wrapped_lex_add (s a : Symbol) (j k : Nat) :
    List.Lex (· < ·) (key (wrapped s a (j + (k + 1)))) (key (wrapped s a j)) := by
  induction k with
  | zero => simpa using wrapped_descends s a j
  | succ k ih =>
      have hidx : j + ((k + 1) + 1) = (j + (k + 1)) + 1 := by omega
      rw [hidx]
      exact list_lex_trans (wrapped_descends s a (j + (k + 1))) ih

theorem wrapped_lex_of_gt (s a : Symbol) {i j : Nat} (h : j < i) :
    List.Lex (· < ·) (key (wrapped s a i)) (key (wrapped s a j)) := by
  have hidx : i = j + ((i - j - 1) + 1) := by omega
  rw [hidx]
  exact wrapped_lex_add s a j (i - j - 1)

theorem not_wrapped_lex_of_le (s a : Symbol) {i j : Nat} (h : i ≤ j) :
    ¬ List.Lex (· < ·) (key (wrapped s a i)) (key (wrapped s a j)) := by
  intro hlex
  rcases Nat.eq_or_lt_of_le h with rfl | hlt
  · exact List.lex_irrefl (fun x => lt_irrefl x) _ hlex
  · exact List.lex_irrefl (fun x => lt_irrefl x) _
      (list_lex_trans hlex (wrapped_lex_of_gt s a hlt))

theorem wrapped_lex_iff_gt (s a : Symbol) (i j : Nat) :
    List.Lex (· < ·) (key (wrapped s a i)) (key (wrapped s a j)) ↔ j < i := by
  constructor
  · intro hlex
    rcases Nat.lt_trichotomy j i with hlt | rfl | hgt
    · exact hlt
    · exact False.elim (List.lex_irrefl (fun x => lt_irrefl x) _ hlex)
    · exact False.elim (not_wrapped_lex_of_le s a (Nat.le_of_lt hgt) hlex)
  · exact wrapped_lex_of_gt s a

end ByteKey

namespace MorkStarve

open ByteKey

def s : Symbol := 0
def a : Symbol := 0
def b : Symbol := 1

inductive Work where
  | deep : Nat → Work
  | goal
deriving DecidableEq, Repr

def keyW : Work → List (Fin 256)
  | .deep n => key (wrapped s a (n + 1))
  | .goal => key (.atom b)

def system : BranchingSystem Work Unit where
  emit
    | .deep _ => none
    | .goal => some ()
  successors
    | .deep n => [.deep (n + 1)]
    | .goal => []

def roots : List Work := [.goal, .deep 0]

/-- Reflexive lexicographic order of the encoded byte keys.  A deeper
application has a smaller key, and every application precedes the atom `b`. -/
def rank (p q : Work) : Prop :=
  keyW p = keyW q ∨ List.Lex (· < ·) (keyW p) (keyW q)

instance : DecidableRel rank := fun p q =>
  inferInstanceAs (Decidable (keyW p = keyW q ∨ List.Lex (· < ·) (keyW p) (keyW q)))

instance : IsTrans Work rank := ⟨fun x y z hxy hyz => by
  rcases hxy with hxy | hxy
  · rcases hyz with hyz | hyz
    · exact Or.inl (hxy.trans hyz)
    · exact Or.inr (by simpa [hxy] using hyz)
  · rcases hyz with hyz | hyz
    · exact Or.inr (by simpa [hyz] using hxy)
    · exact Or.inr (list_lex_trans hxy hyz)⟩

instance : Std.Total rank := ⟨fun x y =>
  list_lexLe_total (r := (· < · : Fin 256 → Fin 256 → Prop)) fin_trichotomy (keyW x) (keyW y)⟩

theorem deep_key_before_goal (n : Nat) :
    List.Lex (· < ·) (keyW (.deep n)) (keyW .goal) := by
  simp [keyW, key]
  exact List.Lex.rel (arity_before_symbol 1 b)

theorem rank_deep_goal (n : Nat) : rank (.deep n) .goal :=
  Or.inr (deep_key_before_goal n)

theorem not_rank_goal_deep (n : Nat) : ¬ rank .goal (.deep n) := by
  intro h
  rcases h with heq | hlex
  · have hlen : (keyW .goal).length = (keyW (.deep n)).length := congrArg List.length heq
    simp only [keyW, key, wrapped_key_length, List.length_singleton] at hlen
    omega
  · exact List.lex_irrefl (fun x => lt_irrefl x) _
      (list_lex_trans hlex (deep_key_before_goal n))

theorem rank_deep_deep (i j : Nat) : rank (.deep i) (.deep j) ↔ j ≤ i := by
  constructor
  · intro h
    rcases h with heq | hlex
    · have hlen : (keyW (.deep i)).length = (keyW (.deep j)).length :=
        congrArg List.length heq
      simp only [keyW, wrapped_key_length] at hlen
      omega
    · have hlt : j + 1 < i + 1 :=
        (wrapped_lex_iff_gt s a (i + 1) (j + 1)).1 (by simpa [keyW] using hlex)
      omega
  · intro h
    rcases Nat.eq_or_lt_of_le h with rfl | hlt
    · exact Or.inl rfl
    · apply Or.inr
      have hlex : List.Lex (· < ·) (key (wrapped s a (i + 1))) (key (wrapped s a (j + 1))) :=
        wrapped_lex_of_gt s a (by omega : j + 1 < i + 1)
      simpa [keyW] using hlex

private theorem reorder_keep {left right : Work} (hle : rank left right) :
    (orderScheduler rank).reorder [left, right] = [left, right] := by
  simp only [orderScheduler, List.insertionSort_cons, List.insertionSort_nil,
    List.orderedInsert_cons, List.orderedInsert_nil, hle]
  simp

private theorem reorder_swap {left right : Work} (hnot : ¬ rank left right) :
    (orderScheduler rank).reorder [left, right] = [right, left] := by
  simp only [orderScheduler, List.insertionSort_cons, List.insertionSort_nil,
    List.orderedInsert_cons, List.orderedInsert_nil, hnot]
  simp

theorem step_from_zero :
    run system (orderScheduler rank) 1 (initial roots) = ⟨[], [.goal, .deep 1]⟩ := by
  have hstart : run system (orderScheduler rank) 0 (initial roots) =
      (⟨[], [.goal, .deep 0]⟩ : Snapshot Work Unit) := by
    simp [run, initial, roots]
  rw [run, hstart]
  simp only [tick]
  rw [reorder_swap (not_rank_goal_deep 0)]
  simp [system, orderScheduler]
  rfl

theorem step_stable (n : Nat)
    (hprev : run system (orderScheduler rank) (n + 1) (initial roots) =
      ⟨[], [.goal, .deep (n + 1)]⟩) :
    run system (orderScheduler rank) (n + 1 + 1) (initial roots) =
      ⟨[], [.goal, .deep (n + 2)]⟩ := by
  rw [run, hprev]
  simp only [tick]
  rw [reorder_swap (not_rank_goal_deep (n + 1))]
  simp [system, orderScheduler]
  rfl

theorem open_after (fuel : Nat) :
    run system (orderScheduler rank) (fuel + 1) (initial roots) =
      ⟨[], [.goal, .deep (fuel + 1)]⟩ := by
  induction fuel with
  | zero => exact step_from_zero
  | succ fuel ih => exact step_stable fuel ih

/-- `rank` is the reflexive lexicographic order of the encoded byte keys. -/
theorem rank_spec (p q : Work) :
    rank p q ↔ keyW p = keyW q ∨ List.Lex (· < ·) (keyW p) (keyW q) := Iff.rfl

/-- An execution keyed by the atom `b` is never emitted.  `rank` is the
reflexive lexicographic order of the encoded byte keys (`rank_spec`).  Each
selected execution generates a deeper application, and deeper keys sort first.
This is a model of that key order, not a proof about MORK's code. -/
theorem goal_starves (fuel : Nat) :
    (⟨.goal, ()⟩ : Emission Work Unit) ∉
      (run system (orderScheduler rank) fuel (initial roots)).events := by
  cases fuel with
  | zero => simp [run, initial]
  | succ fuel =>
      rw [open_after fuel]
      simp

end MorkStarve

end Mettapedia.GSLT.Core.PriorityKeyOrder
