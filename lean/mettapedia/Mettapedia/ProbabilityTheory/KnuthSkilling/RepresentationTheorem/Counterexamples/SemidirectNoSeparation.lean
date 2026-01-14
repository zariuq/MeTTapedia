import Mathlib.Order.WithBot
import Mettapedia.ProbabilityTheory.KnuthSkilling.Algebra

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.RepresentationTheorem.Counterexamples

open Classical KnuthSkillingAlgebra

set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

/-!
# A countermodel attempt: a noncommutative `KnuthSkillingAlgebra` where `KSSeparation` fails

This file intentionally lives under `Mettapedia/ProbabilityTheory/KnuthSkilling/RepresentationTheorem/Counterexamples/`.

This file is a “build-a-countermodel-first” probe.

We construct a simple associative, strictly order-preserving, Archimedean monoid that is
**noncommutative**, but **fails** the `KSSeparation` typeclass.

Interpretation:
- This does **not** refute K&S Appendix A (which assumes / proves a separation property).
- It does show that the *base* axioms packaged in `KnuthSkillingAlgebra` do not, by themselves,
  force `KSSeparation`, and they do not rule out noncommutative models.
-/

/-!
## The model

Take `WithBot (PNat ×ₗ ℕ)` (a bottom element plus a lex-ordered pair `(u>0, x)`).

Define a semidirect-style operation
`(u, x) ⊕ (v, y) := (u+v, x + 2^u * y)`.

This is associative and (strictly) monotone in each argument w.r.t. lex order, but not commutative.
-/

abbrev SDBase := PNat ×ₗ ℕ
abbrev SD := WithBot SDBase

namespace SD

-- `WithBot α` is definitionally `Option α`, and there are multiple competing order instances for
-- `Option`. We pin the `WithBot` order structure explicitly for this specific `Option SDBase`
-- so lemmas like `WithBot.coe_lt_coe` apply without instance-mismatch noise.
instance (priority := 10000) : LE (Option SDBase) := WithBot.instLE
instance (priority := 10000) : LT (Option SDBase) := WithBot.instLT
instance (priority := 10000) : OrderBot (Option SDBase) := WithBot.instOrderBot
instance (priority := 10000) [Preorder SDBase] : Preorder (Option SDBase) := WithBot.instPreorder
instance (priority := 10000) [LinearOrder SDBase] : LinearOrder (Option SDBase) := WithBot.linearOrder

def baseOp (p q : SDBase) : SDBase :=
  let u : ℕ := (p.1 : ℕ)
  (p.1 + q.1, p.2 + (Nat.pow 2 u) * q.2)

def op : SD → SD → SD
  | ⊥, b => b
  | a, ⊥ => a
  | some p, some q => some (baseOp p q)

def ident : SD := (⊥ : SD)

@[simp] theorem op_bot_left (x : SD) : op ⊥ x = x := by cases x <;> rfl
@[simp] theorem op_bot_right (x : SD) : op x ⊥ = x := by cases x <;> rfl

@[simp] theorem op_some_some (p q : SDBase) : op (some p) (some q) = some (baseOp p q) := rfl

theorem baseOp_assoc (p q r : SDBase) : baseOp (baseOp p q) r = baseOp p (baseOp q r) := by
  apply Prod.ext
  · simpa [baseOp, add_assoc, add_left_comm, add_comm]  -- PNat addition
  · -- semidirect second coordinate: distribute and use `2^(u+v)=2^u*2^v`
    -- (all arithmetic is in `ℕ`)
    simp [baseOp, Nat.pow_add, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
      Nat.mul_assoc, Nat.add_mul]

theorem op_assoc : ∀ x y z : SD, op (op x y) z = op x (op y z) := by
  intro x y z
  cases x <;> cases y <;> cases z <;> simp [op, baseOp_assoc]

theorem op_ident_right : ∀ x : SD, op x ident = x := by
  intro x; simpa [ident] using op_bot_right x

theorem op_ident_left : ∀ x : SD, op ident x = x := by
  intro x; simpa [ident] using op_bot_left x

theorem strictMono_baseOp_left (q : SDBase) : StrictMono (fun p => baseOp p q) := by
  intro p₁ p₂ hp
  have hp' :
      p₁.1 < p₂.1 ∨ (p₁.1 = p₂.1 ∧ p₁.2 < p₂.2) := by
    -- Unfold the lexicographic order on `PNat ×ₗ ℕ`.
    have := (Prod.Lex.toLex_lt_toLex (x := (ofLex p₁ : PNat × ℕ)) (y := (ofLex p₂ : PNat × ℕ))).1
        (by simpa using hp)
    simpa using this
  cases hp' with
  | inl hfst =>
    -- First coordinate strictly increases, so the result strictly increases (in lex order).
    have : p₁.1 + q.1 < p₂.1 + q.1 := by exact add_lt_add_right hfst _
    refine (Prod.Lex.toLex_lt_toLex (x := (ofLex (baseOp p₁ q) : PNat × ℕ))
        (y := (ofLex (baseOp p₂ q) : PNat × ℕ))).2 ?_
    refine Or.inl ?_
    -- Avoid `simp` rewriting away the `+ q.1` term.
    change p₁.1 + q.1 < p₂.1 + q.1
    exact this
  | inr hsnd =>
    rcases hsnd with ⟨hfst_eq, hsnd_lt⟩
    have hu : (p₁.1 : ℕ) = (p₂.1 : ℕ) := congrArg (fun t : PNat => (t : ℕ)) hfst_eq
    have : p₁.2 + Nat.pow 2 (p₁.1 : ℕ) * q.2 < p₂.2 + Nat.pow 2 (p₂.1 : ℕ) * q.2 := by
      -- If the first coordinates are equal, the multiplier matches, so add preserves strictness.
      simpa [hu] using Nat.add_lt_add_right hsnd_lt (Nat.pow 2 (p₁.1 : ℕ) * q.2)
    refine (Prod.Lex.toLex_lt_toLex (x := (ofLex (baseOp p₁ q) : PNat × ℕ))
        (y := (ofLex (baseOp p₂ q) : PNat × ℕ))).2 ?_
    exact Or.inr <| by
      refine ⟨by
        change p₁.1 + q.1 = p₂.1 + q.1
        simpa [hfst_eq], ?_⟩
      simpa [baseOp] using this

theorem strictMono_baseOp_right (p : SDBase) : StrictMono (fun q => baseOp p q) := by
  intro q₁ q₂ hq
  have hq' :
      q₁.1 < q₂.1 ∨ (q₁.1 = q₂.1 ∧ q₁.2 < q₂.2) := by
    have := (Prod.Lex.toLex_lt_toLex (x := (ofLex q₁ : PNat × ℕ)) (y := (ofLex q₂ : PNat × ℕ))).1
        (by simpa using hq)
    simpa using this
  cases hq' with
  | inl hfst =>
    have : p.1 + q₁.1 < p.1 + q₂.1 := by exact add_lt_add_left hfst _
    refine (Prod.Lex.toLex_lt_toLex (x := (ofLex (baseOp p q₁) : PNat × ℕ))
        (y := (ofLex (baseOp p q₂) : PNat × ℕ))).2 ?_
    refine Or.inl ?_
    change p.1 + q₁.1 < p.1 + q₂.1
    exact this
  | inr hsnd =>
    rcases hsnd with ⟨hfst_eq, hsnd_lt⟩
    have hmul_pos : 0 < Nat.pow 2 (p.1 : ℕ) := Nat.pow_pos (n := (p.1 : ℕ)) (by decide : 0 < 2)
    have hmul : Nat.pow 2 (p.1 : ℕ) * q₁.2 < Nat.pow 2 (p.1 : ℕ) * q₂.2 :=
      Nat.mul_lt_mul_of_pos_left hsnd_lt hmul_pos
    have : p.2 + Nat.pow 2 (p.1 : ℕ) * q₁.2 < p.2 + Nat.pow 2 (p.1 : ℕ) * q₂.2 := by
      exact Nat.add_lt_add_left hmul _
    refine (Prod.Lex.toLex_lt_toLex (x := (ofLex (baseOp p q₁) : PNat × ℕ))
        (y := (ofLex (baseOp p q₂) : PNat × ℕ))).2 ?_
    exact Or.inr <| by
      refine ⟨by
        change p.1 + q₁.1 = p.1 + q₂.1
        simpa [hfst_eq], ?_⟩
      -- Avoid `simp` collapsing `p.2 + _ < p.2 + _` to `_ < _`.
      change p.2 + Nat.pow 2 (p.1 : ℕ) * q₁.2 < p.2 + Nat.pow 2 (p.1 : ℕ) * q₂.2
      exact this

theorem op_strictMono_left : ∀ y : SD, StrictMono (fun x => op x y) := by
  intro y
  cases y with
  | none =>
    -- y = ⊥, op x ⊥ = x
    have hop : (fun x : SD => op x (none : SD)) = fun x => x := by
      funext x; cases x <;> rfl
    simpa [hop] using (strictMono_id : StrictMono (fun x : SD => x))
  | some q =>
    intro x₁ x₂ hx
    cases x₁ with
    | none =>
      cases x₂ with
      | none =>
        exact (lt_irrefl _ hx).elim
      | some p =>
        -- op ⊥ q = q and op (some p) q = baseOp p q; first coordinate strictly increases.
        have hNat : (q.1 : ℕ) < ((p.1 + q.1 : PNat) : ℕ) := by
          -- coe (p.1 + q.1) = coe p.1 + coe q.1
          simpa using (Nat.lt_add_of_pos_left p.1.pos : (q.1 : ℕ) < (p.1 : ℕ) + (q.1 : ℕ))
        have hPNat : q.1 < p.1 + q.1 := (PNat.coe_lt_coe q.1 (p.1 + q.1)).1 hNat
        have hBase : q < baseOp p q := by
          refine (Prod.Lex.toLex_lt_toLex (x := (ofLex q : PNat × ℕ))
              (y := (ofLex (baseOp p q) : PNat × ℕ))).2 ?_
          exact Or.inl hPNat
        -- Lift the SDBase strict inequality to SD.
        have hLift : (some q : SD) < some (baseOp p q) :=
          (WithBot.coe_lt_coe (a := q) (b := baseOp p q)).2 hBase
        simpa [op] using hLift
    | some p₁ =>
      cases x₂ with
      | none =>
        exact (WithBot.not_lt_bot (a := (some p₁ : SD)) hx).elim
      | some p₂ =>
        have hx' : p₁ < p₂ := by
          exact (WithBot.coe_lt_coe (a := p₁) (b := p₂)).1 (by
            simpa [WithBot.some_eq_coe] using hx)
        have hBase : baseOp p₁ q < baseOp p₂ q := strictMono_baseOp_left q hx'
        have hLift : (some (baseOp p₁ q) : SD) < some (baseOp p₂ q) :=
          (WithBot.coe_lt_coe (a := baseOp p₁ q) (b := baseOp p₂ q)).2 hBase
        simpa [op] using hLift

theorem op_strictMono_right : ∀ x : SD, StrictMono (fun y => op x y) := by
  intro x
  cases x with
  | none =>
    -- x = ⊥, op ⊥ y = y
    simpa [op, ident] using (strictMono_id : StrictMono (fun y : SD => y))
  | some p =>
    intro y₁ y₂ hy
    cases y₁ with
    | none =>
      cases y₂ with
      | none =>
        exact (lt_irrefl _ hy).elim
      | some q =>
        -- op p ⊥ = p and op p (some q) = baseOp p q; first coordinate strictly increases.
        have hNat : (p.1 : ℕ) < ((p.1 + q.1 : PNat) : ℕ) := by
          simpa using (Nat.lt_add_of_pos_right q.1.pos : (p.1 : ℕ) < (p.1 : ℕ) + (q.1 : ℕ))
        have hPNat : p.1 < p.1 + q.1 := (PNat.coe_lt_coe p.1 (p.1 + q.1)).1 hNat
        have hBase : p < baseOp p q := by
          refine (Prod.Lex.toLex_lt_toLex (x := (ofLex p : PNat × ℕ))
              (y := (ofLex (baseOp p q) : PNat × ℕ))).2 ?_
          exact Or.inl hPNat
        have hLift : (some p : SD) < some (baseOp p q) :=
          (WithBot.coe_lt_coe (a := p) (b := baseOp p q)).2 hBase
        simpa [op] using hLift
    | some q₁ =>
      cases y₂ with
      | none =>
        exact (WithBot.not_lt_bot (a := (some q₁ : SD)) hy).elim
      | some q₂ =>
        have hy' : q₁ < q₂ := by
          exact (WithBot.coe_lt_coe (a := q₁) (b := q₂)).1 (by
            simpa [WithBot.some_eq_coe] using hy)
        have hBase : baseOp p q₁ < baseOp p q₂ := strictMono_baseOp_right p hy'
        have hLift : (some (baseOp p q₁) : SD) < some (baseOp p q₂) :=
          (WithBot.coe_lt_coe (a := baseOp p q₁) (b := baseOp p q₂)).2 hBase
        simpa [op] using hLift

def fst : SD → ℕ
  | ⊥ => 0
  | some p => (p.1 : ℕ)

lemma fst_op_left_some (p : SDBase) (z : SD) :
    fst (op (some p) z) = (p.1 : ℕ) + fst z := by
  cases z <;> simp [fst, op, baseOp]

lemma fst_iterate_op_left_some (p : SDBase) (n : ℕ) :
    fst (Nat.iterate (op (some p)) n (some p)) = (n + 1) * (p.1 : ℕ) := by
  induction n with
  | zero =>
    simp [fst]
  | succ n ih =>
    -- Use the application form: `f^[n+1] a = f (f^[n] a)`.
    simp [Function.iterate_succ_apply', fst_op_left_some, ih, Nat.succ_mul, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm]

lemma fst_le_of_le : ∀ {x y : SD}, x ≤ y → fst x ≤ fst y := by
  intro x y hxy
  cases x with
  | none =>
    simp [fst]  -- 0 ≤ fst y
  | some x' =>
    cases y with
    | none =>
      -- impossible: `some _ ≤ ⊥`
      exfalso
      have hxy' : (x' : SD) ≤ (⊥ : SD) := hxy
      exact (WithBot.not_coe_le_bot x') hxy'
    | some y' =>
      have hxy' : x' ≤ y' := by
        have hxy_coe : (x' : SD) ≤ (y' : SD) := hxy
        exact (WithBot.coe_le_coe (a := x') (b := y')).1 hxy_coe
      have hfst : (ofLex x').1 ≤ (ofLex y').1 := (Prod.Lex.le_iff' (x := x') (y := y')).1 hxy' |>.1
      have : (x'.1 : ℕ) ≤ (y'.1 : ℕ) := by
        -- `PNat` order is the `Nat` order on coercions.
        exact_mod_cast hfst
      simpa [fst] using this

lemma fst_le_of_lt {x y : SD} (hxy : x < y) : fst x ≤ fst y :=
  fst_le_of_le (x := x) (y := y) (le_of_lt hxy)

theorem op_archimedean (x y : SD) (hx : ident < x) :
    ∃ n : ℕ, y < Nat.iterate (op x) n x := by
  cases x with
  | none =>
    -- impossible: `ident < ⊥`
    have hx' := hx
    change (⊥ : SD) < (⊥ : SD) at hx'
    exact (lt_irrefl _ hx').elim
  | some px =>
    cases y with
    | none =>
      refine ⟨0, ?_⟩
      simpa [ident, op] using hx
    | some py =>
      refine ⟨(py.1 : ℕ), ?_⟩
      have hpx_ge : 1 ≤ (px.1 : ℕ) := Nat.succ_le_iff.mp px.1.pos
      have hfst_lt :
          (py.1 : ℕ) < fst (Nat.iterate (op (some px)) (py.1 : ℕ) (some px)) := by
        -- fst(iterate) = (n+1)*u ≥ n+1 > n
        have h1 : (py.1 : ℕ) < (py.1 : ℕ) + 1 := Nat.lt_succ_self _
        have h2 : (py.1 : ℕ) + 1 ≤ ((py.1 : ℕ) + 1) * (px.1 : ℕ) := by
          simpa [Nat.mul_comm] using Nat.mul_le_mul_left ((py.1 : ℕ) + 1) hpx_ge
        have : (py.1 : ℕ) < ((py.1 : ℕ) + 1) * (px.1 : ℕ) := lt_of_lt_of_le h1 h2
        simpa [fst_iterate_op_left_some] using this
      -- compare first coordinates in the lex order
      set t : SD := Nat.iterate (op (some px)) (py.1 : ℕ) (some px)
      cases ht : t with
      | none =>
        have : (py.1 : ℕ) < 0 := by simpa [t, ht, fst] using hfst_lt
        exact (Nat.not_lt_zero _ this).elim
      | some tz =>
        have hNat : (py.1 : ℕ) < (tz.1 : ℕ) := by simpa [t, ht, fst] using hfst_lt
        have hPNat : py.1 < tz.1 := (PNat.coe_lt_coe py.1 tz.1).1 (by simpa using hNat)
        have hBase : (py : SDBase) < tz := by
          refine (Prod.Lex.toLex_lt_toLex (x := (ofLex py : PNat × ℕ)) (y := (ofLex tz : PNat × ℕ))).2 ?_
          exact Or.inl hPNat
        -- lift to `WithBot`
        exact (WithBot.coe_lt_coe (a := py) (b := tz)).2 hBase

theorem ident_le (x : SD) : ident ≤ x := by
  simpa [ident] using (bot_le : (⊥ : SD) ≤ x)

instance : KnuthSkillingAlgebra SD where
  op := op
  ident := ident
  op_assoc := op_assoc
  op_ident_right := op_ident_right
  op_ident_left := op_ident_left
  op_strictMono_left := op_strictMono_left
  op_strictMono_right := op_strictMono_right
  ident_le := ident_le

end SD

namespace SD

-- A concrete witness that the operation is NOT commutative.
def exX : SD := ((toLex ((⟨1, Nat.one_pos⟩ : PNat), 1) : SDBase) : SD)
def exY : SD := ((toLex ((⟨2, Nat.succ_pos 1⟩ : PNat), 1) : SDBase) : SD)

theorem op_not_comm : KnuthSkillingAlgebraBase.op exX exY ≠ KnuthSkillingAlgebraBase.op exY exX := by
  -- exX ⊕ exY = (3, 1 + 2^1*1) = (3, 3)
  -- exY ⊕ exX = (3, 1 + 2^2*1) = (3, 5)
  simp [SD.exX, SD.exY, SD.op, SD.baseOp, KnuthSkillingAlgebraBase.op]
  decide

/-!
## `KSSeparation` fails in this model

Pick:
- `a = (1,1)`,
- `x = (1,2)`,
- `y = (1,3)`.

Then `x < y`, but for any `m>0` we have `iterate_op a m < iterate_op x m`, so it is impossible
to have `iterate_op x m < iterate_op a n` together with `iterate_op a n ≤ iterate_op y m`.
-/

def baseA : SD := ((toLex ((⟨1, Nat.one_pos⟩ : PNat), 1) : SDBase) : SD)
def baseX : SD := ((toLex ((⟨1, Nat.one_pos⟩ : PNat), 2) : SDBase) : SD)
def baseY : SD := ((toLex ((⟨1, Nat.one_pos⟩ : PNat), 3) : SDBase) : SD)

theorem fst_iterate_op_coe (p : SDBase) :
    ∀ n : ℕ, SD.fst (iterate_op (p : SD) n) = n * (p.1 : ℕ) := by
  intro n
  induction n with
  | zero =>
    simp [KnuthSkillingAlgebra.iterate_op, KnuthSkillingAlgebraBase.ident, SD.ident, SD.fst]
  | succ n ih =>
    -- iterate_op (n+1) = op p (iterate_op n)
    -- fst(op p z) = u + fst(z)
    have : SD.fst (KnuthSkillingAlgebraBase.op (p : SD) (iterate_op (p : SD) n)) =
        (p.1 : ℕ) + SD.fst (iterate_op (p : SD) n) := by
      -- reduce to the concrete `SD.fst_op_left_some`
      simpa [KnuthSkillingAlgebraBase.op, SD.op, SD.fst] using (SD.fst_op_left_some p (iterate_op (p : SD) n))
    -- finish the arithmetic
    -- `p1 + n*p1 = (n+1)*p1`
    have harith : (p.1 : ℕ) + n * (p.1 : ℕ) = (n + 1) * (p.1 : ℕ) := by
      calc
        (p.1 : ℕ) + n * (p.1 : ℕ) = n * (p.1 : ℕ) + (p.1 : ℕ) := by
          simpa [Nat.add_comm]
        _ = (n + 1) * (p.1 : ℕ) := by
          simpa [Nat.succ_mul] using (Nat.succ_mul n (p.1 : ℕ)).symm
    simpa [KnuthSkillingAlgebra.iterate_op, this, ih, harith]

theorem baseA_lt_baseX : baseA < baseX := by
  have hbase :
      (toLex ((⟨1, Nat.one_pos⟩ : PNat), 1) : SDBase) <
        (toLex ((⟨1, Nat.one_pos⟩ : PNat), 2) : SDBase) := by
    refine (Prod.Lex.toLex_lt_toLex (x := ((⟨1, Nat.one_pos⟩ : PNat), 1))
      (y := ((⟨1, Nat.one_pos⟩ : PNat), 2))).2 ?_
    exact Or.inr ⟨rfl, by decide⟩
  have : ((toLex ((⟨1, Nat.one_pos⟩ : PNat), 1) : SDBase) : SD) <
      ((toLex ((⟨1, Nat.one_pos⟩ : PNat), 2) : SDBase) : SD) := by
    simpa using hbase
  simpa [baseA, baseX] using this

theorem baseX_lt_baseY : baseX < baseY := by
  have hbase :
      (toLex ((⟨1, Nat.one_pos⟩ : PNat), 2) : SDBase) <
        (toLex ((⟨1, Nat.one_pos⟩ : PNat), 3) : SDBase) := by
    refine (Prod.Lex.toLex_lt_toLex (x := ((⟨1, Nat.one_pos⟩ : PNat), 2))
      (y := ((⟨1, Nat.one_pos⟩ : PNat), 3))).2 ?_
    exact Or.inr ⟨rfl, by decide⟩
  have : ((toLex ((⟨1, Nat.one_pos⟩ : PNat), 2) : SDBase) : SD) <
      ((toLex ((⟨1, Nat.one_pos⟩ : PNat), 3) : SDBase) : SD) := by
    simpa using hbase
  simpa [baseX, baseY] using this

/-- In this semidirect/lex model, `KSSeparation` would force an impossible inequality.

This is the essence of why `KSSeparation` fails here:
- choose `baseA < baseX < baseY` with the **same** lex “scale” (first coordinate),
- any sandwich `baseX^m < baseA^n ≤ baseY^m` forces `n = m` by comparing first coordinates,
- but strict monotonicity gives `baseA^m < baseX^m`, contradicting `baseX^m < baseA^m`. -/
theorem separation_contradiction (hSep : KSSeparation SD) : False := by
  have ha : (ident : SD) < baseA := by
    simpa [SD.ident] using (WithBot.bot_lt_iff_ne_bot (x := baseA)).2 (by simp [baseA])
  have hx : (ident : SD) < baseX := by
    simpa [SD.ident] using (WithBot.bot_lt_iff_ne_bot (x := baseX)).2 (by simp [baseX])
  have hy : (ident : SD) < baseY := by
    simpa [SD.ident] using (WithBot.bot_lt_iff_ne_bot (x := baseY)).2 (by simp [baseY])
  have hxy : baseX < baseY := baseX_lt_baseY
  rcases hSep.separation (a := baseA) (x := baseX) (y := baseY) ha hx hy hxy with
    ⟨n, m, hm_pos, hxm_lt, han_le⟩
  -- Extract the iterate exponents from the lex first coordinate (`fst`).
  let pA : SDBase := toLex ((1 : PNat), 1)
  let pX : SDBase := toLex ((1 : PNat), 2)
  let pY : SDBase := toLex ((1 : PNat), 3)
  have hfstA : SD.fst (iterate_op baseA n) = n := by
    have hpA : (pA.1 : ℕ) = 1 := by rfl
    have := (fst_iterate_op_coe (p := pA) n)
    simpa [baseA, pA, hpA] using this
  have hfstX : SD.fst (iterate_op baseX m) = m := by
    have hpX : (pX.1 : ℕ) = 1 := by rfl
    have := (fst_iterate_op_coe (p := pX) m)
    simpa [baseX, pX, hpX] using this
  have hfstY : SD.fst (iterate_op baseY m) = m := by
    have hpY : (pY.1 : ℕ) = 1 := by rfl
    have := (fst_iterate_op_coe (p := pY) m)
    simpa [baseY, pY, hpY] using this
  have hmn : m ≤ n := by
    have h := SD.fst_le_of_lt (x := iterate_op baseX m) (y := iterate_op baseA n) hxm_lt
    simpa [hfstX, hfstA] using h
  have hnm : n ≤ m := by
    have h := SD.fst_le_of_le (x := iterate_op baseA n) (y := iterate_op baseY m) han_le
    simpa [hfstA, hfstY] using h
  have hnm_eq : n = m := le_antisymm hnm hmn
  -- With n=m, we get x^m < a^m, contradicting monotonicity in the base element (a < x).
  have ham_lt : iterate_op baseA m < iterate_op baseX m :=
    KnuthSkillingAlgebra.iterate_op_strictMono_base m hm_pos baseA baseX baseA_lt_baseX
  have hxm_lt' : iterate_op baseX m < iterate_op baseA m := by simpa [hnm_eq] using hxm_lt
  exact lt_irrefl (iterate_op baseA m) (lt_trans ham_lt hxm_lt')

theorem not_KSSeparation : ¬ KSSeparation SD := by
  intro hSep
  exact separation_contradiction hSep

end SD

end Mettapedia.ProbabilityTheory.KnuthSkilling.RepresentationTheorem.Counterexamples
