import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SuperpositionLifting
import Mathlib.Data.List.Lex
import Mathlib.Data.DFinsupp.WellFounded

/-!
# The Knuth–Bendix ordering: a stable ordering linked to a ground simplification ordering

**Parameters** (`KBOParams`): a positive weight for every symbol (constants and function symbols), and
a total precedence given by an injective code into the natural numbers, so the signature is finite
or countable. Variables weigh `1`.

## The ground ordering

A ground term is coded by its **weighted Polish notation** (`enc`): for each subterm in prefix order,
its weight and the code of its head symbol. The code is a prefix code (`enc_append_inj`), so codes
compared lexicographically give a linear order on ground terms (`order`). It is the ground
Knuth–Bendix ordering: weight first (`gw_le_of_lt`), then the precedence of the head
(`prec_le_of_lt`), then the arguments lexicographically (`args_of_lt`).

* It is **well founded** (`wellFounded`), by induction on the weight, then on the precedence, then on
  the arguments in the lexicographic order of tuples of accessible terms (`Pi.Lex.wellFounded`).
* It is **compatible with contexts** and **contains the strict subterm relation**
  (`order_simplification`): a ground simplification ordering.

## The non-ground ordering

`Gt s t` (`s ≻ t`): every variable occurs in `s` at least as often as in `t` (`vars t ≤ vars s`), and
either `s` is heavier, or the weights are equal and the head of `s` has the greater precedence, or the
heads are one function symbol and the arguments are greater lexicographically.

* **Stability** (`Gt.subst`): from the weight identity `w(tσ) + |t|ᵥ = w(t) + Σ_{x ∈ t} w(xσ)`
  (`w_subst`), the variable condition gives `w(sσ) − w(tσ) ≥ w(s) − w(t)` (`w_subst_mono`).
* **The ground restriction** (`Gt.ground`): on ground terms `Gt` is contained in the ground ordering.
* Hence **the order link** (`gt_ground`), and a linked ordering (`grounded`), whose literal ordering is
  side dominance (`SidesBelow`): stable and linked, and contained in the Bachmair–Ganzinger multiset
  extension, though smaller than it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Superposition

open Mettapedia.Logic.LP

variable {sig : LPSignature}

/-! ## Lexicographic comparison of prefix codes -/

section Lex

theorem lex_cons_ne {a b : ℕ} {l l' : List ℕ} (ne : a ≠ b) :
    List.Lex (· < ·) (a :: l) (b :: l') ↔ a < b := by
  constructor
  · intro h
    cases h with
    | cons _ => exact absurd rfl ne
    | rel h => exact h
  · exact List.Lex.rel

theorem lex_head_le {a b : ℕ} {l l' : List ℕ} (h : List.Lex (· < ·) (a :: l) (b :: l')) : a ≤ b :=
  match h with
  | .cons _ => le_rfl
  | .rel h => h.le

theorem lex_irrefl (l : List ℕ) : ¬ List.Lex (· < ·) l l := fun h => lt_irrefl l h

theorem lex_append_left_iff : ∀ (u : List ℕ) {x y : List ℕ},
    List.Lex (· < ·) (u ++ x) (u ++ y) ↔ List.Lex (· < ·) x y
  | [], _, _ => Iff.rfl
  | _ :: u, _, _ => by
      rw [List.cons_append, List.cons_append, List.lex_cons_iff]
      exact lex_append_left_iff u

/-- **Codes neither of which is a prefix of the other compare inside**: extensions do not matter. -/
theorem lex_append_of_not_prefix : ∀ {u v : List ℕ} (r r' : List ℕ), (∀ w, u ++ w ≠ v) →
    (∀ w, v ++ w ≠ u) → (List.Lex (· < ·) (u ++ r) (v ++ r') ↔ List.Lex (· < ·) u v)
  | [], v, _, _, np, _ => absurd (List.nil_append v) (np v)
  | a :: u, [], _, _, _, np' => absurd (List.nil_append (a :: u)) (np' (a :: u))
  | a :: u, b :: v, r, r', np, np' => by
      by_cases same : a = b
      · subst same
        rw [List.cons_append, List.cons_append, List.lex_cons_iff, List.lex_cons_iff]
        exact lex_append_of_not_prefix r r' (fun w h => np w (by rw [List.cons_append, h]))
          (fun w h => np' w (by rw [List.cons_append, h]))
      · rw [List.cons_append, List.cons_append, lex_cons_ne same, lex_cons_ne same]

end Lex

/-! ## The ground Knuth–Bendix ordering -/

/-- **Knuth–Bendix parameters**: positive weights, and a total precedence given by an injective code of
the symbols. -/
structure KBOParams (sig : LPSignature) where
  weight : sig.constants ⊕ sig.functionSymbols → ℕ
  weight_pos : ∀ s, 0 < weight s
  prec : sig.constants ⊕ sig.functionSymbols → ℕ
  prec_injective : Function.Injective prec

namespace KBOParams

/-- The head symbol of a ground term. -/
def head : GroundTerm sig → sig.constants ⊕ sig.functionSymbols
  | .const c => .inl c
  | .app f _ => .inr f

variable (κ : KBOParams sig)

/-- **The weight of a ground term.** -/
def gw : GroundTerm sig → ℕ
  | .const c => κ.weight (.inl c)
  | .app f args => κ.weight (.inr f) + ∑ i, gw (args i)

/-- **The weighted Polish code**: for each subterm in prefix order, its weight and its head's code. -/
def enc : GroundTerm sig → List ℕ
  | .const c => [κ.weight (.inl c), κ.prec (.inl c)]
  | .app f args => κ.gw (.app f args) :: κ.prec (.inr f) :: (List.ofFn fun i => enc (args i)).flatten

theorem enc_eq : ∀ t : GroundTerm sig, ∃ rest, κ.enc t = κ.gw t :: κ.prec (head t) :: rest
  | .const _ => ⟨[], rfl⟩
  | .app _ _ => ⟨_, rfl⟩

theorem flatten_inj : ∀ (n : ℕ) (xs ys : Fin n → GroundTerm sig) (r r' : List ℕ),
    (∀ i (t : GroundTerm sig) (r r' : List ℕ), κ.enc (xs i) ++ r = κ.enc t ++ r' → xs i = t ∧ r = r') →
    (List.ofFn fun i => κ.enc (xs i)).flatten ++ r = (List.ofFn fun i => κ.enc (ys i)).flatten ++ r' →
      xs = ys ∧ r = r'
  | 0, _, _, r, r', _, same => ⟨funext fun i => i.elim0, by simpa using same⟩
  | n + 1, xs, ys, r, r', ih, same => by
      rw [List.ofFn_succ, List.ofFn_succ, List.flatten_cons, List.flatten_cons, List.append_assoc,
        List.append_assoc] at same
      obtain ⟨first, tail⟩ := ih 0 (ys 0) _ _ same
      obtain ⟨rest, rfl⟩ := flatten_inj n (fun i => xs i.succ) (fun i => ys i.succ) r r'
        (fun i => ih i.succ) tail
      exact ⟨funext fun i => Fin.cases first (fun j => congrFun rest j) i, rfl⟩

/-- **The weighted Polish code is a prefix code.** -/
theorem enc_append_inj (s : GroundTerm sig) : ∀ (t : GroundTerm sig) (r r' : List ℕ),
    κ.enc s ++ r = κ.enc t ++ r' → s = t ∧ r = r' := by
  induction s with
  | const c =>
      intro t r r' same
      cases t with
      | const d =>
          have h : κ.weight (.inl c) :: κ.prec (.inl c) :: r = κ.weight (.inl d) :: κ.prec (.inl d) :: r' :=
            same
          obtain rfl := Sum.inl.inj (κ.prec_injective (List.cons.inj (List.cons.inj h).2).1)
          exact ⟨rfl, (List.cons.inj (List.cons.inj h).2).2⟩
      | app g args =>
          have h : κ.weight (.inl c) :: κ.prec (.inl c) :: r =
              κ.gw (.app g args) :: κ.prec (.inr g) :: ((List.ofFn fun i => κ.enc (args i)).flatten ++ r') :=
            same
          exact absurd (κ.prec_injective (List.cons.inj (List.cons.inj h).2).1) Sum.inl_ne_inr
  | app f args ih =>
      intro t r r' same
      cases t with
      | const d =>
          have h : κ.gw (.app f args) :: κ.prec (.inr f) :: ((List.ofFn fun i => κ.enc (args i)).flatten ++ r) =
              κ.weight (.inl d) :: κ.prec (.inl d) :: r' := same
          exact absurd (κ.prec_injective (List.cons.inj (List.cons.inj h).2).1) Sum.inr_ne_inl
      | app g args' =>
          have h : κ.gw (.app f args) :: κ.prec (.inr f) :: ((List.ofFn fun i => κ.enc (args i)).flatten ++ r) =
              κ.gw (.app g args') :: κ.prec (.inr g) :: ((List.ofFn fun i => κ.enc (args' i)).flatten ++ r') :=
            same
          have fg := Sum.inr.inj (κ.prec_injective (List.cons.inj (List.cons.inj h).2).1)
          subst fg
          obtain ⟨rfl, rest⟩ := κ.flatten_inj _ args args' r r' ih (List.cons.inj (List.cons.inj h).2).2
          exact ⟨rfl, rest⟩

theorem enc_injective : Function.Injective κ.enc := fun s t same =>
  (κ.enc_append_inj s t [] [] (by rw [List.append_nil, List.append_nil, same])).1

theorem enc_not_prefix {s t : GroundTerm sig} (ne : s ≠ t) (w : List ℕ) : κ.enc s ++ w ≠ κ.enc t :=
  fun h => ne (κ.enc_append_inj s t w [] (by rw [h, List.append_nil])).1

theorem lex_enc_ne {s t : GroundTerm sig} (lt : List.Lex (· < ·) (κ.enc s) (κ.enc t)) : s ≠ t := by
  rintro rfl
  exact lex_irrefl _ lt

/-- **The first differing argument decides.** -/
theorem lex_flatten_of_index : ∀ (n : ℕ) (xs ys : Fin n → GroundTerm sig) (i : Fin n),
    (∀ j, j < i → xs j = ys j) → List.Lex (· < ·) (κ.enc (xs i)) (κ.enc (ys i)) →
      List.Lex (· < ·) (List.ofFn fun j => κ.enc (xs j)).flatten (List.ofFn fun j => κ.enc (ys j)).flatten
  | 0, _, _, i, _, _ => i.elim0
  | n + 1, xs, ys, i, before, lt => by
      rw [List.ofFn_succ, List.ofFn_succ, List.flatten_cons, List.flatten_cons]
      revert before lt
      refine Fin.cases ?_ (fun k => ?_) i
      · intro _ lt
        exact (lex_append_of_not_prefix _ _ (κ.enc_not_prefix (κ.lex_enc_ne lt))
          (κ.enc_not_prefix (κ.lex_enc_ne lt).symm)).mpr lt
      · intro before lt
        rw [before 0 (Fin.succ_pos k)]
        exact (lex_append_left_iff _).mpr (lex_flatten_of_index n (fun j => xs j.succ) (fun j => ys j.succ) k
          (fun j h => before j.succ (Fin.succ_lt_succ_iff.mpr h)) lt)

/-- **Comparing argument codes finds the first differing argument.** -/
theorem lex_flatten_inv : ∀ (n : ℕ) (xs ys : Fin n → GroundTerm sig),
    List.Lex (· < ·) (List.ofFn fun j => κ.enc (xs j)).flatten (List.ofFn fun j => κ.enc (ys j)).flatten →
      ∃ i, (∀ j, j < i → xs j = ys j) ∧ List.Lex (· < ·) (κ.enc (xs i)) (κ.enc (ys i))
  | 0, _, _, lt => by
      rw [List.ofFn_zero, List.flatten_nil] at lt
      cases lt
  | n + 1, xs, ys, lt => by
      rw [List.ofFn_succ, List.ofFn_succ, List.flatten_cons, List.flatten_cons] at lt
      by_cases same : xs 0 = ys 0
      · rw [same, lex_append_left_iff] at lt
        obtain ⟨i, before, here⟩ := lex_flatten_inv n (fun j => xs j.succ) (fun j => ys j.succ) lt
        refine ⟨i.succ, fun j => Fin.cases (fun _ => same)
          (fun k h => before k (Fin.succ_lt_succ_iff.mp h)) j, here⟩
      · exact ⟨0, fun j h => absurd h (Fin.not_lt_zero j),
          (lex_append_of_not_prefix _ _ (κ.enc_not_prefix same) (κ.enc_not_prefix (Ne.symm same))).mp lt⟩

/-- **The ground Knuth–Bendix ordering**: weighted Polish codes compared lexicographically. -/
abbrev order : LinearOrder (GroundTerm sig) := LinearOrder.lift' κ.enc κ.enc_injective

theorem lt_iff {s t : GroundTerm sig} : κ.order.lt s t ↔ List.Lex (· < ·) (κ.enc s) (κ.enc t) := Iff.rfl

theorem gw_arg_lt (f : sig.functionSymbols) (args : Fin (sig.functionArity f) → GroundTerm sig)
    (i : Fin (sig.functionArity f)) : κ.gw (args i) < κ.gw (.app f args) := by
  show κ.gw (args i) < κ.weight (.inr f) + ∑ j, κ.gw (args j)
  have one := Finset.single_le_sum (f := fun j => κ.gw (args j)) (fun j _ => Nat.zero_le _)
    (Finset.mem_univ i)
  have two := κ.weight_pos (.inr f)
  omega

/-- **Weight first.** -/
theorem gw_le_of_lt {s t : GroundTerm sig} (lt : List.Lex (· < ·) (κ.enc s) (κ.enc t)) : κ.gw s ≤ κ.gw t := by
  obtain ⟨rs, hs⟩ := κ.enc_eq s
  obtain ⟨rt, ht⟩ := κ.enc_eq t
  rw [hs, ht] at lt
  exact lex_head_le lt

/-- **Then the precedence of the head.** -/
theorem prec_le_of_lt {s t : GroundTerm sig} (lt : List.Lex (· < ·) (κ.enc s) (κ.enc t))
    (same : κ.gw s = κ.gw t) : κ.prec (head s) ≤ κ.prec (head t) := by
  obtain ⟨rs, hs⟩ := κ.enc_eq s
  obtain ⟨rt, ht⟩ := κ.enc_eq t
  rw [hs, ht, same] at lt
  exact lex_head_le (List.lex_cons_iff.mp lt)

/-- **Then the arguments, lexicographically.** -/
theorem args_of_lt {s : GroundTerm sig} {f : sig.functionSymbols}
    {bs : Fin (sig.functionArity f) → GroundTerm sig} (lt : List.Lex (· < ·) (κ.enc s) (κ.enc (.app f bs)))
    (same : κ.gw s = κ.gw (.app f bs)) (heads : head s = .inr f) :
    ∃ as : Fin (sig.functionArity f) → GroundTerm sig, s = .app f as ∧
      ∃ i, (∀ j, j < i → as j = bs j) ∧ List.Lex (· < ·) (κ.enc (as i)) (κ.enc (bs i)) := by
  cases s with
  | const c => cases heads
  | app g as =>
      have fg : g = f := Sum.inr.inj heads
      subst fg
      refine ⟨as, rfl, ?_⟩
      change List.Lex (· < ·) (_ :: _ :: (List.ofFn fun i => κ.enc (as i)).flatten)
        (_ :: _ :: (List.ofFn fun i => κ.enc (bs i)).flatten) at lt
      rw [same, List.lex_cons_iff, List.lex_cons_iff] at lt
      exact κ.lex_flatten_inv _ as bs lt

theorem acc_subtype {α : Type*} {R : α → α → Prop} (a : α) (h : Acc R a) :
    Acc (fun x y : {a // Acc R a} => R x.1 y.1) ⟨a, h⟩ := by
  induction h with
  | intro a _ ih => exact Acc.intro _ fun ⟨b, _⟩ hba => ih b hba

/-- **The ground Knuth–Bendix ordering is well founded.** -/
theorem wellFounded : WellFounded fun s t : GroundTerm sig => List.Lex (· < ·) (κ.enc s) (κ.enc t) := by
  let R : GroundTerm sig → GroundTerm sig → Prop := fun s t => List.Lex (· < ·) (κ.enc s) (κ.enc t)
  suffices main : ∀ W (t : GroundTerm sig), κ.gw t = W → Acc R t from ⟨fun t => main _ t rfl⟩
  intro W
  refine Nat.strong_induction_on W fun W ihW => ?_
  suffices byPrec : ∀ P (t : GroundTerm sig), κ.gw t = W → κ.prec (head t) = P → Acc R t from
    fun t ht => byPrec _ t ht rfl
  intro P
  refine Nat.strong_induction_on P fun P ihP => ?_
  intro t ht hp
  cases t with
  | const c =>
      refine Acc.intro _ fun s hs => ?_
      rcases (κ.gw_le_of_lt hs).lt_or_eq with lw | ew
      · exact ihW _ (ht ▸ lw) s rfl
      · rcases (κ.prec_le_of_lt hs ew).lt_or_eq with lp | ep
        · exact ihP _ (hp ▸ lp) s (ew.trans ht) rfl
        · have heads := κ.prec_injective ep
          cases s with
          | const d =>
              cases heads
              exact absurd hs (lex_irrefl _)
          | app g as => cases heads
  | app f bs =>
      let S := {u : GroundTerm sig // Acc R u}
      let R' : S → S → Prop := fun x y => R x.1 y.1
      have wfS : WellFounded R' := ⟨fun ⟨u, hu⟩ => acc_subtype u hu⟩
      have wfPi : WellFounded (Pi.Lex (· < ·) (fun {_} ↦ R') :
          (Fin (sig.functionArity f) → S) → (Fin (sig.functionArity f) → S) → Prop) :=
        Pi.Lex.wellFounded (· < ·) fun _ => wfS
      have argsAcc : ∀ as : Fin (sig.functionArity f) → GroundTerm sig, κ.gw (.app f as) = W →
          ∀ j, Acc R (as j) :=
        fun as h j => ihW _ (h ▸ κ.gw_arg_lt f as j) _ rfl
      have tuple : ∀ xs : Fin (sig.functionArity f) → S, κ.gw (.app f fun j => (xs j).1) = W →
          Acc R (.app f fun j => (xs j).1) := by
        intro xs
        induction xs using wfPi.induction with
        | h xs ihx =>
          intro hW
          refine Acc.intro _ fun s hs => ?_
          rcases (κ.gw_le_of_lt hs).lt_or_eq with lw | ew
          · exact ihW _ (hW ▸ lw) s rfl
          · by_cases same : head s = .inr f
            · obtain ⟨as, rfl, i, before, here⟩ := κ.args_of_lt hs ew same
              have asW : κ.gw (.app f as) = W := ew.trans hW
              let ys : Fin (sig.functionArity f) → S := fun j => ⟨as j, argsAcc as asW j⟩
              exact ihx ys ⟨i, fun j h => Subtype.ext (before j h), here⟩ asW
            · rcases (κ.prec_le_of_lt hs ew).lt_or_eq with lp | ep
              · exact ihP _ (hp ▸ lp) s (ew.trans hW) rfl
              · exact absurd (κ.prec_injective ep) same
      exact tuple (fun j => ⟨bs j, argsAcc bs ht j⟩) ht

theorem order_wellFounded : @WellFoundedLT (GroundTerm sig) κ.order.toLT := ⟨κ.wellFounded⟩

/-- **The ground Knuth–Bendix ordering is a ground simplification ordering.** -/
theorem order_simplification : @GroundSimplification sig κ.order := by
  let _ := κ.order
  constructor
  · intro f args i a lt
    have lex : List.Lex (· < ·) (κ.enc a) (κ.enc (args i)) := lt
    show List.Lex (· < ·) (κ.enc (.app f (Function.update args i a))) (κ.enc (.app f args))
    rcases (κ.gw_le_of_lt lex).lt_or_eq with lw | ew
    · have lighter : κ.gw (.app f (Function.update args i a)) < κ.gw (.app f args) := by
        show κ.weight (.inr f) + ∑ j, κ.gw (Function.update args i a j) < κ.weight (.inr f) + ∑ j, κ.gw (args j)
        have sums := Finset.sum_lt_sum (s := Finset.univ) (f := fun j => κ.gw (Function.update args i a j))
          (g := fun j => κ.gw (args j)) (fun j _ => by
            by_cases h : j = i
            · rw [h, Function.update_self]
              exact lw.le
            · simp only [Function.update_of_ne h, le_refl])
          ⟨i, Finset.mem_univ i, by simp only [Function.update_self]; exact lw⟩
        omega
      exact List.Lex.rel lighter
    · have weights : κ.gw (.app f (Function.update args i a)) = κ.gw (.app f args) := by
        show κ.weight (.inr f) + ∑ j, κ.gw (Function.update args i a j) = κ.weight (.inr f) + ∑ j, κ.gw (args j)
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases h : j = i
        · rw [h, Function.update_self]
          exact ew
        · rw [Function.update_of_ne h]
      show List.Lex (· < ·)
        (κ.gw (.app f (Function.update args i a)) :: κ.prec (.inr f) ::
          (List.ofFn fun j => κ.enc (Function.update args i a j)).flatten)
        (κ.gw (.app f args) :: κ.prec (.inr f) :: (List.ofFn fun j => κ.enc (args j)).flatten)
      rw [weights]
      refine List.Lex.cons (List.Lex.cons ?_)
      exact κ.lex_flatten_of_index _ _ _ i (fun j h => Function.update_of_ne (ne_of_lt h) _ _)
        (by rw [Function.update_self]; exact lex)
  · intro f args i
    show List.Lex (· < ·) (κ.enc (args i)) (κ.enc (.app f args))
    obtain ⟨r, hr⟩ := κ.enc_eq (args i)
    rw [hr]
    exact List.Lex.rel (κ.gw_arg_lt f args i)

/-! ## The non-ground Knuth–Bendix ordering -/

/-- **The variables of a term**, with multiplicity. -/
def vars : Term sig → Multiset sig.vars
  | .var v => {v}
  | .const _ => 0
  | .app _ ts => ∑ i, vars (ts i)

/-- **The weight of a term**; variables weigh `1`. -/
def w : Term sig → ℕ
  | .var _ => 1
  | .const c => κ.weight (.inl c)
  | .app f ts => κ.weight (.inr f) + ∑ i, w (ts i)

/-- The head symbol of a term that is not a variable. -/
def thead : Term sig → Option (sig.constants ⊕ sig.functionSymbols)
  | .var _ => none
  | .const c => some (.inl c)
  | .app f _ => some (.inr f)

/-- The weight of the instances of a multiset of variables. -/
def substWeight (σ : Subst sig) : Multiset sig.vars →+ ℕ where
  toFun M := (M.map fun x => κ.w (σ x)).sum
  map_zero' := by simp
  map_add' _ _ := by simp [Multiset.map_add, Multiset.sum_add]

/-- Binding a multiset of variables to the variables of their instances. -/
def bindVars (σ : Subst sig) : Multiset sig.vars →+ Multiset sig.vars where
  toFun M := M.bind fun x => vars (σ x)
  map_zero' := Multiset.zero_bind _
  map_add' _ _ := Multiset.add_bind _ _ _

theorem w_pos (t : Term sig) : 1 ≤ κ.w t := by
  cases t with
  | var _ => exact le_rfl
  | const c => exact κ.weight_pos _
  | app f ts =>
      show 1 ≤ κ.weight (.inr f) + ∑ i, κ.w (ts i)
      have := κ.weight_pos (.inr f)
      omega

/-- **The weight of an instance**: `w(tσ) + |t|ᵥ = w(t) + Σ_{x ∈ t} w(xσ)`. -/
theorem w_subst (σ : Subst sig) (t : Term sig) :
    κ.w (σ.applyTerm t) + Multiset.card (vars t) = κ.w t + κ.substWeight σ (vars t) := by
  induction t with
  | var v =>
      show κ.w (σ v) + Multiset.card ({v} : Multiset sig.vars) =
        1 + (({v} : Multiset sig.vars).map fun x => κ.w (σ x)).sum
      simp only [Multiset.card_singleton, Multiset.map_singleton, Multiset.sum_singleton]
      omega
  | const c => simp [vars, w, substWeight, Subst.applyTerm]
  | app f ts ih =>
      have total := Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => ih i)
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at total
      show κ.weight (.inr f) + ∑ i, κ.w (σ.applyTerm (ts i)) + Multiset.card (∑ i, vars (ts i)) =
        κ.weight (.inr f) + ∑ i, κ.w (ts i) + κ.substWeight σ (∑ i, vars (ts i))
      rw [Multiset.card_sum, map_sum]
      omega

theorem card_le_substWeight (σ : Subst sig) (M : Multiset sig.vars) :
    Multiset.card M ≤ κ.substWeight σ M := by
  induction M using Multiset.induction_on with
  | empty => simp
  | cons x M ih =>
      show Multiset.card (x ::ₘ M) ≤ ((x ::ₘ M).map fun y => κ.w (σ y)).sum
      rw [Multiset.card_cons, Multiset.map_cons, Multiset.sum_cons]
      have := κ.w_pos (σ x)
      have ih' : Multiset.card M ≤ (M.map fun y => κ.w (σ y)).sum := ih
      omega

/-- **The weight difference grows under substitution** when the variable condition holds. -/
theorem w_subst_mono (σ : Subst sig) {s t : Term sig} (le : vars t ≤ vars s) :
    κ.w (σ.applyTerm t) + κ.w s ≤ κ.w (σ.applyTerm s) + κ.w t := by
  obtain ⟨E, hE⟩ := Multiset.le_iff_exists_add.mp le
  have hs := κ.w_subst σ s
  have ht := κ.w_subst σ t
  have extra := κ.card_le_substWeight σ E
  rw [hE, map_add, Multiset.card_add] at hs
  omega

theorem vars_subst (σ : Subst sig) (t : Term sig) : vars (σ.applyTerm t) = bindVars σ (vars t) := by
  induction t with
  | var v =>
      show vars (σ v) = ({v} : Multiset sig.vars).bind fun x => vars (σ x)
      rw [Multiset.singleton_bind]
  | const _ => rfl
  | app f ts ih =>
      show ∑ i, vars (σ.applyTerm (ts i)) = bindVars σ (∑ i, vars (ts i))
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => ih i

theorem vars_subst_le (σ : Subst sig) {s t : Term sig} (le : vars t ≤ vars s) :
    vars (σ.applyTerm t) ≤ vars (σ.applyTerm s) := by
  rw [vars_subst σ s, vars_subst σ t]
  obtain ⟨E, hE⟩ := Multiset.le_iff_exists_add.mp le
  rw [hE, map_add]
  exact Multiset.le_add_right _ _

theorem thead_subst (σ : Subst sig) {t : Term sig} {p : sig.constants ⊕ sig.functionSymbols}
    (head : thead t = some p) : thead (σ.applyTerm t) = some p := by
  cases t with
  | var _ => cases head
  | const _ => exact head
  | app _ _ => exact head

/-- **The Knuth–Bendix ordering on terms** (`Gt s t`, `s ≻ t`). -/
inductive Gt : Term sig → Term sig → Prop
  /-- `s` is heavier. -/
  | weight {s t : Term sig} (vars_le : vars t ≤ vars s) (lt : κ.w t < κ.w s) : Gt s t
  /-- Equal weights, and the head of `s` has the greater precedence. -/
  | prec {s t : Term sig} {p q : sig.constants ⊕ sig.functionSymbols} (vars_le : vars t ≤ vars s)
      (same : κ.w t = κ.w s) (hs : thead s = some p) (ht : thead t = some q) (lt : κ.prec q < κ.prec p) :
      Gt s t
  /-- Equal weights, one head, and the arguments greater lexicographically. -/
  | lex {f : sig.functionSymbols} {ss ts : Fin (sig.functionArity f) → Term sig}
      (vars_le : vars (.app f ts) ≤ vars (.app f ss)) (same : κ.w (.app f ts) = κ.w (.app f ss))
      (i : Fin (sig.functionArity f)) (before : ∀ j, j < i → ss j = ts j) (gt : Gt (ss i) (ts i)) :
      Gt (.app f ss) (.app f ts)

/-- **The Knuth–Bendix ordering is stable under substitution.** -/
theorem Gt.subst (σ : Subst sig) {s t : Term sig} (gt : κ.Gt s t) :
    κ.Gt (σ.applyTerm s) (σ.applyTerm t) := by
  induction gt with
  | @weight s t vars_le lt =>
      have mono := κ.w_subst_mono σ vars_le
      exact .weight (vars_subst_le σ vars_le) (by omega)
  | @prec s t p q vars_le same hs ht lt =>
      have mono := κ.w_subst_mono σ vars_le
      rcases (show κ.w (σ.applyTerm t) ≤ κ.w (σ.applyTerm s) by omega).lt_or_eq with lw | ew
      · exact .weight (vars_subst_le σ vars_le) lw
      · exact .prec (vars_subst_le σ vars_le) ew (thead_subst σ hs) (thead_subst σ ht) lt
  | @lex f ss ts vars_le same i before _ ih =>
      have mono := κ.w_subst_mono σ vars_le
      rcases (show κ.w (σ.applyTerm (.app f ts)) ≤ κ.w (σ.applyTerm (.app f ss)) by omega).lt_or_eq with
        lw | ew
      · exact .weight (vars_subst_le σ vars_le) lw
      · exact .lex (ss := fun j => σ.applyTerm (ss j)) (ts := fun j => σ.applyTerm (ts j))
          (vars_subst_le σ vars_le) ew i (fun j h => by rw [before j h]) ih

theorem w_toTerm (a : GroundTerm sig) : κ.w a.toTerm = κ.gw a := by
  induction a with
  | const _ => rfl
  | app f args ih =>
      show κ.weight (.inr f) + ∑ i, κ.w (args i).toTerm = κ.weight (.inr f) + ∑ i, κ.gw (args i)
      simp only [ih]

theorem thead_toTerm (a : GroundTerm sig) : thead a.toTerm = some (head a) := by
  cases a <;> rfl

theorem toTerm_injective : Function.Injective (GroundTerm.toTerm (σ := sig)) := fun g₁ g₂ same => by
  have step := congrArg (Grounding.groundTerm fun _ => g₁) same
  exact (ground_toTerm _ g₁).symm.trans (step.trans (ground_toTerm _ g₂))

theorem toTerm_app_inv {a : GroundTerm sig} {f : sig.functionSymbols}
    {ss : Fin (sig.functionArity f) → Term sig} (same : a.toTerm = .app f ss) :
    ∃ as : Fin (sig.functionArity f) → GroundTerm sig, a = .app f as ∧ ∀ i, ss i = (as i).toTerm := by
  cases a with
  | const _ => cases same
  | app g as =>
      have inj := Term.app.inj same
      obtain ⟨rfl, hargs⟩ := inj
      have args := eq_of_heq hargs
      exact ⟨as, rfl, fun i => (congrFun args i).symm⟩

/-- **The ground restriction**: on ground terms the Knuth–Bendix ordering is contained in the ground
ordering. -/
theorem Gt.ground {s t : Term sig} (gt : κ.Gt s t) : ∀ a b : GroundTerm sig, s = a.toTerm → t = b.toTerm →
    List.Lex (· < ·) (κ.enc b) (κ.enc a) := by
  induction gt with
  | @weight s t _ lt =>
      intro a b hs ht
      subst hs ht
      rw [κ.w_toTerm, κ.w_toTerm] at lt
      obtain ⟨ra, ha⟩ := κ.enc_eq a
      obtain ⟨rb, hb⟩ := κ.enc_eq b
      rw [ha, hb]
      exact List.Lex.rel lt
  | @prec s t p q _ same hs ht lt =>
      intro a b hsa htb
      subst hsa htb
      rw [κ.w_toTerm, κ.w_toTerm] at same
      rw [thead_toTerm] at hs ht
      cases hs
      cases ht
      obtain ⟨ra, ha⟩ := κ.enc_eq a
      obtain ⟨rb, hb⟩ := κ.enc_eq b
      rw [ha, hb, same]
      exact List.Lex.cons (List.Lex.rel lt)
  | @lex f ss ts _ same i before _ ih =>
      intro a b hsa htb
      obtain ⟨as, rfl, has⟩ := toTerm_app_inv hsa.symm
      obtain ⟨bs, rfl, hbs⟩ := toTerm_app_inv htb.symm
      have weights : κ.gw (.app f bs) = κ.gw (.app f as) := by
        rw [← κ.w_toTerm, ← κ.w_toTerm, ← htb, ← hsa]
        exact same
      show List.Lex (· < ·)
        (κ.gw (.app f bs) :: κ.prec (.inr f) :: (List.ofFn fun j => κ.enc (bs j)).flatten)
        (κ.gw (.app f as) :: κ.prec (.inr f) :: (List.ofFn fun j => κ.enc (as j)).flatten)
      rw [weights]
      refine List.Lex.cons (List.Lex.cons ?_)
      refine κ.lex_flatten_of_index _ bs as i (fun j h => ?_) (ih (as i) (bs i) (has i) (hbs i))
      exact (toTerm_injective (by rw [← has j, ← hbs j, before j h])).symm

/-- **The order link**: `s ≻ t` implies `sθ > tθ` for every grounding `θ`. -/
theorem gt_ground (θ : Grounding sig) {s t : Term sig} (gt : κ.Gt s t) :
    List.Lex (· < ·) (κ.enc (θ.groundTerm t)) (κ.enc (θ.groundTerm s)) :=
  (gt.subst κ θ.toSubst).ground κ _ _ (Grounding.groundTerm_toTerm θ s).symm
    (Grounding.groundTerm_toTerm θ t).symm

/-- **The Knuth–Bendix ordering as a linked stable ordering** over the ground Knuth–Bendix ordering. -/
def grounded : @GroundedOrder sig κ.order :=
  @GroundedOrder.ofTermOrder sig κ.order κ.Gt (fun τ _ _ gt => gt.subst κ τ) (fun θ _ _ gt => κ.gt_ground θ gt)

end KBOParams

#print axioms lex_append_of_not_prefix
#print axioms KBOParams.enc_append_inj
#print axioms KBOParams.lex_flatten_of_index
#print axioms KBOParams.lex_flatten_inv
#print axioms KBOParams.args_of_lt
#print axioms KBOParams.wellFounded
#print axioms KBOParams.order_wellFounded
#print axioms KBOParams.order_simplification
#print axioms KBOParams.w_subst
#print axioms KBOParams.w_subst_mono
#print axioms KBOParams.vars_subst_le
#print axioms KBOParams.Gt.subst
#print axioms KBOParams.Gt.ground
#print axioms KBOParams.gt_ground
#print axioms KBOParams.grounded

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Superposition
