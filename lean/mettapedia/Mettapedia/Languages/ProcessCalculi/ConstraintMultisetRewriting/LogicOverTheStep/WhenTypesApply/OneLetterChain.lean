import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.WhenTypesApply.FixpointTypes
import Mathlib.Data.Fintype.Pigeonhole

/-!
# On a one-letter chain every fixed-point formula is a finite automaton

The one-letter chain (`chain`) has the states `0, 1, 2, …`; `m + 1` steps to `m` under the letter
and nothing else steps. From `m` there is exactly one run, `m → m - 1 → … → 0`.

**Where automata enter, precisely.** A formula is read by a finite automaton (`Machine`) that walks
the chain from its end `0` upward: at each state it reads one column, which sets of the environment
hold there (`column`), and outputs one bit. A machine **computes** a formula when its output is the
formula's truth at every state, for every environment (`Computes`).

* Truth, falsity, a variable, the connectives and the two modalities are machines with no memory,
  machines side by side, and a machine remembering its last output (`Machine.const`,
  `Machine.read`, `Machine.pair`, `Machine.shift`).
* **A fixed point is a machine** (`Machine.fix`, `fix_computes_mu`, `fix_computes_nu`). The body's
  machine reads the bound variable as one more column. At each state the fixed point's bit is the
  body's output when that column is guessed false (least) or true (greatest), and the body's machine
  moves on with that bit. The bit is a fixed point because the body is monotone; it is the least (or
  greatest) one because a state's bit depends only on the states below it: a pre-fixed set that
  missed the first marked state it misses would, below it, agree with the marked set, and the body
  would force the state in.
* So **every formula whose fixed points have positive bodies is computed by a finite machine**
  (`exists_machine`). A machine reading a constant column runs through finitely many states, so
  its outputs repeat from some point on with a positive period (`output_periodic`): **every such
  formula denotes an ultimately periodic set** (`sat_periodic`).

**Control** (`squares_not_periodic`): the perfect squares are not ultimately periodic, since their
gaps grow. So no fixed-point formula with positive fixed points denotes them on the chain
(`squares_not_denoted`).

**The converse** (`periodic_denoted`): every ultimately periodic set is denoted, by one formula per
member below the threshold ("exactly `n` steps", `exactly`) and one least fixed point per residue
above it (`residue`: `μX. exactly n ∨ ⟨·⟩ᵖ X`). So **on the one-letter chain the formulas with
positive fixed points denote exactly the ultimately periodic sets** (`denoted_iff_periodic`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.WhenTypesApply.OneLetterChain

open Set
open Mettapedia.Logic.ModalMuCalculus
open Mettapedia.Logic.ModalQuantaleSemantics.Boolean (bodyOrderHom)
open Mettapedia.GSLT.LanguageDef.CertificateGSLT.MuCalculusBoundary (fixedPointsPositive)

universe w

variable {Act : Type w}

/-- **The one-letter chain**: `m + 1` steps to `m` under the letter; nothing else steps. -/
def chain (letter : Act) : LTS ℕ Act where
  trans n action m := action = letter ∧ n = m + 1

/-! ## Columns -/

/-- Whether a state lies in a set, as a bit. -/
noncomputable def bit (X : Set ℕ) (m : ℕ) : Bool := by
  classical exact decide (m ∈ X)

theorem bit_eq_true (X : Set ℕ) (m : ℕ) : bit X m = true ↔ m ∈ X := by
  unfold bit
  simp

/-- **The column of an environment at a state**: which of its sets hold the state. -/
noncomputable def column {k : ℕ} (E : Env ℕ k) (m : ℕ) : Fin k → Bool := fun index => bit (E index) m

theorem column_eq_true {k : ℕ} (E : Env ℕ k) (m : ℕ) (index : Fin k) :
    column E m index = true ↔ m ∈ E index :=
  bit_eq_true (E index) m

/-- The column of an extended environment: the new set first. -/
theorem column_extend {k : ℕ} (E : Env ℕ k) (X : Set ℕ) (m : ℕ) :
    column (E.extend X) m = Fin.cons (bit X m) (column E m) := by
  funext index
  refine Fin.cases ?_ (fun j => ?_) index
  · rw [Fin.cons_zero]
    show bit (E.extend X 0) m = bit X m
    congr 1
  · rw [Fin.cons_succ]
    show bit (E.extend X j.succ) m = bit (E j) m
    congr 1

/-! ## Machines -/

/-- **A finite automaton reading the chain from its end**: one column per state, starting at `0`;
one bit out per state. -/
structure Machine (k : ℕ) where
  State : Type
  finite : Finite State
  start : State
  next : State → (Fin k → Bool) → State
  out : State → (Fin k → Bool) → Bool

namespace Machine

variable {k : ℕ}

/-- The state after reading the first `m` columns. -/
def stateAt (M : Machine k) (input : ℕ → Fin k → Bool) : ℕ → M.State
  | 0 => M.start
  | m + 1 => M.next (M.stateAt input m) (input m)

/-- The output at `m`. -/
def output (M : Machine k) (input : ℕ → Fin k → Bool) (m : ℕ) : Bool :=
  M.out (M.stateAt input m) (input m)

/-- **A machine reads forward**: its state at `m` depends only on the columns below `m`. -/
theorem stateAt_congr (M : Machine k) {input input' : ℕ → Fin k → Bool} :
    ∀ m, (∀ j < m, input j = input' j) → M.stateAt input m = M.stateAt input' m
  | 0, _ => rfl
  | m + 1, same => by
      show M.next (M.stateAt input m) (input m) = M.next (M.stateAt input' m) (input' m)
      rw [M.stateAt_congr m (fun j lt => same j (Nat.lt_succ_of_lt lt)), same m (Nat.lt_succ_self m)]

/-- No memory, a constant output. -/
def const (b : Bool) : Machine k where
  State := Unit
  finite := inferInstance
  start := ()
  next _ _ := ()
  out _ _ := b

/-- No memory, reading one variable. -/
def read (index : Fin k) : Machine k where
  State := Unit
  finite := inferInstance
  start := ()
  next _ _ := ()
  out _ column := column index

/-- Two machines side by side, their outputs combined. -/
def pair (M N : Machine k) (combine : Bool → Bool → Bool) : Machine k where
  State := M.State × N.State
  finite := by
    have := M.finite
    have := N.finite
    infer_instance
  start := (M.start, N.start)
  next q column := (M.next q.1 column, N.next q.2 column)
  out q column := combine (M.out q.1 column) (N.out q.2 column)

theorem pair_stateAt (M N : Machine k) (combine : Bool → Bool → Bool) (input : ℕ → Fin k → Bool) :
    ∀ m, (pair M N combine).stateAt input m = (M.stateAt input m, N.stateAt input m)
  | 0 => rfl
  | m + 1 => by
      show (pair M N combine).next ((pair M N combine).stateAt input m) (input m) = _
      rw [pair_stateAt M N combine input m]
      rfl

theorem pair_output (M N : Machine k) (combine : Bool → Bool → Bool) (input : ℕ → Fin k → Bool)
    (m : ℕ) : (pair M N combine).output input m = combine (M.output input m) (N.output input m) := by
  show (pair M N combine).out ((pair M N combine).stateAt input m) (input m) = _
  rw [pair_stateAt]
  rfl

/-- A machine remembering the last output of another, with a first memory. -/
def shift (M : Machine k) (initial : Bool) (combine : Bool → Bool) : Machine k where
  State := M.State × Bool
  finite := by
    have := M.finite
    infer_instance
  start := (M.start, initial)
  next q column := (M.next q.1 column, M.out q.1 column)
  out q _ := combine q.2

theorem shift_stateAt (M : Machine k) (initial : Bool) (combine : Bool → Bool)
    (input : ℕ → Fin k → Bool) :
    ∀ m, ((shift M initial combine).stateAt input m).1 = M.stateAt input m
  | 0 => rfl
  | m + 1 => by
      show M.next ((shift M initial combine).stateAt input m).1 (input m) =
        M.next (M.stateAt input m) (input m)
      rw [shift_stateAt M initial combine input m]

theorem shift_output_zero (M : Machine k) (initial : Bool) (combine : Bool → Bool)
    (input : ℕ → Fin k → Bool) : (shift M initial combine).output input 0 = combine initial :=
  rfl

theorem shift_output_succ (M : Machine k) (initial : Bool) (combine : Bool → Bool)
    (input : ℕ → Fin k → Bool) (m : ℕ) :
    (shift M initial combine).output input (m + 1) = combine (M.output input m) := by
  show combine (M.out ((shift M initial combine).stateAt input m).1 (input m)) =
    combine (M.out (M.stateAt input m) (input m))
  rw [shift_stateAt]

/-- **A fixed point as a machine**: at each state the body's machine is run with the bound variable
guessed; that output is the fixed point's bit, and the body's machine moves on with it. The guess is
`false` for a least fixed point and `true` for a greatest one. -/
def fix (M : Machine (k + 1)) (guess : Bool) : Machine k where
  State := M.State
  finite := M.finite
  start := M.start
  next q column := M.next q (Fin.cons (M.out q (Fin.cons guess column)) column)
  out q column := M.out q (Fin.cons guess column)

end Machine

/-- A machine **computes** a formula on the chain: at every environment, its output at each state,
reading the environment's columns, is the formula's truth there. -/
def Computes (letter : Act) {k : ℕ} (φ : Formula Act k) (M : Machine k) : Prop :=
  ∀ (E : Env ℕ k) (m : ℕ), satisfies (chain letter) E φ m ↔ M.output (column E) m = true

/-! ## Fixed points -/

section Fix

variable {letter : Act} {k : ℕ} {body : Formula Act (k + 1)} {M : Machine (k + 1)}

/-- The states a fixed point's machine marks. -/
def marked (M : Machine (k + 1)) (guess : Bool) (E : Env ℕ k) : Set ℕ :=
  {i | (Machine.fix M guess).output (column E) i = true}

theorem bit_marked (M : Machine (k + 1)) (guess : Bool) (E : Env ℕ k) (i : ℕ) :
    bit (marked M guess E) i = (Machine.fix M guess).output (column E) i :=
  Bool.eq_iff_iff.mpr (bit_eq_true _ i)

/-- Run on the marked set, the body's machine passes through the fixed point's states. -/
theorem fix_stateAt (M : Machine (k + 1)) (guess : Bool) (E : Env ℕ k) :
    ∀ j, M.stateAt (column (E.extend (marked M guess E))) j =
      (Machine.fix M guess).stateAt (column E) j
  | 0 => rfl
  | j + 1 => by
      show M.next (M.stateAt (column (E.extend (marked M guess E))) j)
          (column (E.extend (marked M guess E)) j) =
        M.next ((Machine.fix M guess).stateAt (column E) j)
          (Fin.cons (M.out ((Machine.fix M guess).stateAt (column E) j) (Fin.cons guess (column E j)))
            (column E j))
      rw [fix_stateAt M guess E j, column_extend, bit_marked]
      rfl

/-- So does it on every set that agrees with the marked one below the state. -/
theorem fix_stateAt_of_agree (M : Machine (k + 1)) (guess : Bool) (E : Env ℕ k) (W : Set ℕ)
    (j : ℕ) (agree : ∀ i < j, (i ∈ W ↔ i ∈ marked M guess E)) :
    M.stateAt (column (E.extend W)) j = (Machine.fix M guess).stateAt (column E) j := by
  rw [← fix_stateAt M guess E j]
  apply M.stateAt_congr j
  intro i lt
  rw [column_extend, column_extend]
  congr 1
  exact Bool.eq_iff_iff.mpr ((bit_eq_true W i).trans ((agree i lt).trans (bit_eq_true _ i).symm))

theorem fix_body_iff (computes : Computes letter body M) (guess : Bool) (E : Env ℕ k) (W : Set ℕ)
    (j : ℕ) (agree : ∀ i < j, (i ∈ W ↔ i ∈ marked M guess E)) :
    satisfies (chain letter) (E.extend W) body j ↔
      M.out ((Machine.fix M guess).stateAt (column E) j) (Fin.cons (bit W j) (column E j)) = true := by
  rw [computes (E.extend W) j]
  unfold Machine.output
  rw [fix_stateAt_of_agree M guess E W j agree, column_extend]

/-- **A least fixed point is a machine.** -/
theorem fix_computes_mu (computes : Computes letter body M) (positive : body.isPositive = true) :
    Computes letter (.mu body) (Machine.fix M false) := by
  intro E m
  have monotone := (bodyOrderHom (chain letter) E body positive).monotone
  have closedX : ∀ t, satisfies (chain letter) (E.extend (marked M false E)) body t →
      t ∈ marked M false E := by
    intro t holds
    have forced := (fix_body_iff computes false E (marked M false E) t (fun _ _ => Iff.rfl)).mp holds
    rw [bit_marked] at forced
    show (Machine.fix M false).output (column E) t = true
    cases hb : (Machine.fix M false).output (column E) t with
    | true => rfl
    | false =>
        rw [hb] at forced
        have same : (Machine.fix M false).output (column E) t = true := forced
        rw [hb] at same
        exact absurd same Bool.false_ne_true
  have least : ∀ Y : Set ℕ, (∀ t, satisfies (chain letter) (E.extend Y) body t → t ∈ Y) →
      ∀ j, j ∈ marked M false E → j ∈ Y := by
    intro Y closedY j
    refine Nat.strong_induction_on j ?_
    intro j ih member
    by_contra outside
    have agree : ∀ i < j, (i ∈ marked M false E ∩ Y ↔ i ∈ marked M false E) :=
      fun i lt => ⟨fun inside => inside.1, fun inside => ⟨inside, ih i lt inside⟩⟩
    have notIn : bit (marked M false E ∩ Y) j = false := by
      cases hb : bit (marked M false E ∩ Y) j with
      | false => rfl
      | true => exact absurd ((bit_eq_true _ j).mp hb).2 outside
    have atW : satisfies (chain letter) (E.extend (marked M false E ∩ Y)) body j := by
      rw [fix_body_iff computes false E _ j agree, notIn]
      exact member
    have atY : satisfies (chain letter) (E.extend Y) body j := monotone Set.inter_subset_right atW
    exact outside (closedY j atY)
  constructor
  · intro holds
    exact holds _ closedX
  · intro member Y closedY
    exact least Y closedY m member

/-- **A greatest fixed point is a machine.** -/
theorem fix_computes_nu (computes : Computes letter body M) (positive : body.isPositive = true) :
    Computes letter (.nu body) (Machine.fix M true) := by
  intro E m
  have monotone := (bodyOrderHom (chain letter) E body positive).monotone
  have postX : ∀ t ∈ marked M true E, satisfies (chain letter) (E.extend (marked M true E)) body t := by
    intro t member
    have member' : (Machine.fix M true).output (column E) t = true := member
    rw [fix_body_iff computes true E (marked M true E) t (fun _ _ => Iff.rfl), bit_marked, member']
    exact member'
  have greatest : ∀ Y : Set ℕ, (∀ t ∈ Y, satisfies (chain letter) (E.extend Y) body t) →
      ∀ j, j ∈ Y → j ∈ marked M true E := by
    intro Y postY j
    refine Nat.strong_induction_on j ?_
    intro j ih member
    by_contra outside
    have agree : ∀ i < j, (i ∈ marked M true E ∪ Y ↔ i ∈ marked M true E) :=
      fun i lt => ⟨fun inside => inside.elim id (ih i lt), Or.inl⟩
    have isIn : bit (marked M true E ∪ Y) j = true := (bit_eq_true _ j).mpr (Or.inr member)
    have atW : satisfies (chain letter) (E.extend (marked M true E ∪ Y)) body j :=
      monotone Set.subset_union_right (postY j member)
    rw [fix_body_iff computes true E _ j agree, isIn] at atW
    exact outside atW
  constructor
  · rintro ⟨Y, member, postY⟩
    exact greatest Y postY m member
  · intro member
    exact ⟨marked M true E, member, postX⟩

end Fix

/-! ## Every formula with positive fixed points is a machine -/

/-- **Every formula whose fixed points have positive bodies is computed by a finite machine** on
the one-letter chain. -/
theorem exists_machine (letter : Act) :
    ∀ {k : ℕ} (φ : Formula Act k), fixedPointsPositive φ = true → ∃ M : Machine k, Computes letter φ M
  | _, .tt, _ => ⟨Machine.const true, fun _ _ => iff_of_true trivial rfl⟩
  | _, .ff, _ => ⟨Machine.const false, fun _ _ => iff_of_false id Bool.false_ne_true⟩
  | _, .var index, _ => ⟨Machine.read index, fun E m => (column_eq_true E m index).symm⟩
  | _, .neg inner, positive => by
      obtain ⟨M, computes⟩ := exists_machine letter inner positive
      refine ⟨Machine.pair M (Machine.const false) fun b _ => !b, fun E m => ?_⟩
      rw [Machine.pair_output]
      show ¬ satisfies (chain letter) E inner m ↔ _
      rw [computes E m]
      cases M.output (column E) m <;> simp
  | _, .conj first second, positive => by
      simp only [fixedPointsPositive, Bool.and_eq_true] at positive
      obtain ⟨M, hM⟩ := exists_machine letter first positive.1
      obtain ⟨N, hN⟩ := exists_machine letter second positive.2
      refine ⟨Machine.pair M N and, fun E m => ?_⟩
      rw [Machine.pair_output, Bool.and_eq_true, ← hM E m, ← hN E m]
      exact Iff.rfl
  | _, .disj first second, positive => by
      simp only [fixedPointsPositive, Bool.and_eq_true] at positive
      obtain ⟨M, hM⟩ := exists_machine letter first positive.1
      obtain ⟨N, hN⟩ := exists_machine letter second positive.2
      refine ⟨Machine.pair M N or, fun E m => ?_⟩
      rw [Machine.pair_output, Bool.or_eq_true, ← hM E m, ← hN E m]
      exact Iff.rfl
  | _, .diamond action inner, positive => by
      classical
      obtain ⟨M, computes⟩ := exists_machine letter inner positive
      refine ⟨Machine.shift M false fun b => decide (action = letter) && b, fun E m => ?_⟩
      cases m with
      | zero =>
          constructor
          · rintro ⟨next, ⟨_, impossible⟩, _⟩
            omega
          · intro h
            exact absurd h (by simp [Machine.shift_output_zero])
      | succ j =>
          simp only [Machine.shift_output_succ, Bool.and_eq_true, decide_eq_true_eq]
          rw [← computes E j]
          constructor
          · rintro ⟨next, ⟨same, step⟩, holds⟩
            obtain rfl : next = j := by omega
            exact ⟨same, holds⟩
          · rintro ⟨same, holds⟩
            exact ⟨j, ⟨same, rfl⟩, holds⟩
  | _, .box action inner, positive => by
      classical
      obtain ⟨M, computes⟩ := exists_machine letter inner positive
      refine ⟨Machine.shift M true fun b => !decide (action = letter) || b, fun E m => ?_⟩
      cases m with
      | zero =>
          refine iff_of_true ?_ (by simp [Machine.shift_output_zero])
          rintro next ⟨_, impossible⟩
          omega
      | succ j =>
          simp only [Machine.shift_output_succ, Bool.or_eq_true]
          rw [← computes E j]
          constructor
          · intro all
            by_cases same : action = letter
            · exact Or.inr (all j ⟨same, rfl⟩)
            · left
              simpa using same
          · rintro (different | holds) next ⟨same, step⟩
            · simp [same] at different
            · obtain rfl : next = j := by omega
              exact holds
  | _, .mu body, positive => by
      simp only [fixedPointsPositive, Bool.and_eq_true] at positive
      obtain ⟨M, computes⟩ := exists_machine letter body positive.2
      exact ⟨Machine.fix M false, fix_computes_mu computes positive.1⟩
  | _, .nu body, positive => by
      simp only [fixedPointsPositive, Bool.and_eq_true] at positive
      obtain ⟨M, computes⟩ := exists_machine letter body positive.2
      exact ⟨Machine.fix M true, fix_computes_nu computes positive.1⟩

/-! ## Finite machines repeat -/

/-- **Ultimately periodic**: from some point on, membership repeats with a positive period. -/
def UltimatelyPeriodic (A : Set ℕ) : Prop :=
  ∃ N p, 0 < p ∧ ∀ m, N ≤ m → (m + p ∈ A ↔ m ∈ A)

theorem stateAt_const_shift {k : ℕ} (M : Machine k) (c : Fin k → Bool) {i j : ℕ}
    (same : M.stateAt (fun _ => c) i = M.stateAt (fun _ => c) j) :
    ∀ t, M.stateAt (fun _ => c) (i + t) = M.stateAt (fun _ => c) (j + t)
  | 0 => same
  | t + 1 => by
      show M.next (M.stateAt (fun _ => c) (i + t)) c = M.next (M.stateAt (fun _ => c) (j + t)) c
      rw [stateAt_const_shift M c same t]

theorem periodic_of_eq {k : ℕ} (M : Machine k) (c : Fin k → Bool) {i j : ℕ} (lt : i < j)
    (same : M.stateAt (fun _ => c) i = M.stateAt (fun _ => c) j) :
    UltimatelyPeriodic {m | M.output (fun _ => c) m = true} := by
  refine ⟨i, j - i, Nat.sub_pos_of_lt lt, fun m large => ?_⟩
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le large
  have index : i + t + (j - i) = j + t := by omega
  show M.out (M.stateAt (fun _ => c) (i + t + (j - i))) c = true ↔
    M.out (M.stateAt (fun _ => c) (i + t)) c = true
  rw [index, ← stateAt_const_shift M c same t]

/-- **A finite machine reading a constant column has ultimately periodic output.** -/
theorem output_periodic {k : ℕ} (M : Machine k) (c : Fin k → Bool) :
    UltimatelyPeriodic {m | M.output (fun _ => c) m = true} := by
  have := M.finite
  obtain ⟨i, j, different, same⟩ := Finite.exists_ne_map_eq_of_infinite (M.stateAt fun _ => c)
  rcases Nat.lt_or_gt_of_ne different with lt | lt
  · exact periodic_of_eq M c lt same
  · exact periodic_of_eq M c lt same.symm

/-- **On the one-letter chain every formula with positive fixed points denotes an ultimately
periodic set**, its free variables read as empty. -/
theorem sat_periodic (letter : Act) {k : ℕ} (φ : Formula Act k)
    (positive : fixedPointsPositive φ = true) :
    UltimatelyPeriodic {m | satisfies (chain letter) (fun _ => ∅) φ m} := by
  obtain ⟨M, computes⟩ := exists_machine letter φ positive
  obtain ⟨N, p, period, repeats⟩ := output_periodic M (fun _ => false)
  refine ⟨N, p, period, fun m large => ?_⟩
  have columnEmpty : column (fun _ : Fin k => (∅ : Set ℕ)) = fun _ _ => false := by
    funext m index
    exact Bool.eq_false_iff.mpr fun h => (column_eq_true _ m index).mp h
  show satisfies (chain letter) (fun _ => ∅) φ (m + p) ↔ satisfies (chain letter) (fun _ => ∅) φ m
  rw [computes (fun _ => ∅) (m + p), computes (fun _ => ∅) m, columnEmpty]
  exact repeats m large

/-! ## Control: the squares -/

/-- The perfect squares. -/
def squares : Set ℕ := {m | ∃ r, m = r * r}

/-- **The squares are not ultimately periodic**: past any point, a square plus the period lies
strictly between two consecutive squares. -/
theorem squares_not_periodic : ¬ UltimatelyPeriodic squares := by
  rintro ⟨N, p, period, repeats⟩
  have large : N ≤ (N + p) * (N + p) := le_trans (Nat.le_add_right N p) (Nat.le_mul_self (N + p))
  obtain ⟨r, hr⟩ := (repeats _ large).mpr ⟨N + p, rfl⟩
  have lower : N + p < r := Nat.mul_self_lt_mul_self_iff.mp (hr ▸ Nat.lt_add_of_pos_right period)
  have upper : r < N + p + 1 := Nat.mul_self_lt_mul_self_iff.mp (by nlinarith)
  omega

/-- **No formula with positive fixed points denotes the squares on the one-letter chain.** -/
theorem squares_not_denoted (letter : Act) {k : ℕ} (φ : Formula Act k)
    (positive : fixedPointsPositive φ = true) :
    ¬ ∀ m, satisfies (chain letter) (fun _ => ∅) φ m ↔ m ∈ squares := by
  intro denotes
  obtain ⟨N, p, period, repeats⟩ := sat_periodic letter φ positive
  exact squares_not_periodic ⟨N, p, period, fun m large =>
    ((denotes (m + p)).symm.trans (repeats m large)).trans (denotes m)⟩

/-! ## The converse: every ultimately periodic set is denoted -/

section Converse

/-- `n` steps, then the formula. -/
def dias {k : ℕ} : ℕ → Formula Unit k → Formula Unit k
  | 0, φ => φ
  | n + 1, φ => .diamond () (dias n φ)

theorem satisfies_dias {k : ℕ} (ρ : Env ℕ k) (φ : Formula Unit k) :
    ∀ (n m : ℕ), satisfies (chain ()) ρ (dias n φ) m ↔ n ≤ m ∧ satisfies (chain ()) ρ φ (m - n)
  | 0, m => by simp [dias]
  | n + 1, m => by
      show (∃ m' ∈ (chain ()).successors m (), satisfies (chain ()) ρ (dias n φ) m') ↔ _
      constructor
      · rintro ⟨m', ⟨-, rfl⟩, holds⟩
        obtain ⟨le, there⟩ := (satisfies_dias ρ φ n m').mp holds
        refine ⟨by omega, ?_⟩
        have shift : m' + 1 - (n + 1) = m' - n := by omega
        rw [shift]
        exact there
      · rintro ⟨le, there⟩
        obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        refine ⟨m', ⟨rfl, rfl⟩, (satisfies_dias ρ φ n m').mpr ⟨by omega, ?_⟩⟩
        have shift : m' + 1 - (n + 1) = m' - n := by omega
        rw [← shift]
        exact there

/-- Exactly `n` steps. -/
def exactly {k : ℕ} (n : ℕ) : Formula Unit k := .conj (dias n .tt) (.neg (dias (n + 1) .tt))

theorem satisfies_exactly {k : ℕ} (ρ : Env ℕ k) (n m : ℕ) :
    satisfies (chain ()) ρ (exactly n) m ↔ m = n := by
  show (satisfies (chain ()) ρ (dias n .tt) m ∧ ¬ satisfies (chain ()) ρ (dias (n + 1) .tt) m) ↔ m = n
  rw [satisfies_dias, satisfies_dias]
  constructor
  · rintro ⟨⟨le, -⟩, notMore⟩
    by_contra different
    exact notMore ⟨by omega, trivial⟩
  · rintro rfl
    exact ⟨⟨le_rfl, trivial⟩, fun ⟨more, _⟩ => by omega⟩

/-- `μX. exactly n ∨ ⟨·⟩ᵖ X`: the states `n`, `n + p`, `n + 2p`, … -/
def residue (n p : ℕ) : Formula Unit 0 := .mu (.disj (exactly n) (dias p (.var 0)))

theorem satisfies_residue (n p m : ℕ) :
    satisfies (chain ()) (fun _ => ∅) (residue n p) m ↔ ∃ j, m = n + p * j := by
  constructor
  · intro holds
    refine holds {m | ∃ j, m = n + p * j} fun t body => ?_
    rcases body with here | there
    · exact ⟨0, by rw [(satisfies_exactly _ n t).mp here]; simp⟩
    · obtain ⟨le, ⟨j, same⟩⟩ := (satisfies_dias _ _ p t).mp there
      exact ⟨j + 1, by rw [Nat.mul_succ]; omega⟩
  · rintro ⟨j, rfl⟩ X closed
    induction j with
    | zero => exact closed _ (Or.inl ((satisfies_exactly _ n _).mpr (by simp)))
    | succ j ih =>
        apply closed
        refine Or.inr ((satisfies_dias _ _ p _).mpr ⟨by rw [Nat.mul_succ]; omega, ?_⟩)
        have back : n + p * (j + 1) - p = n + p * j := by rw [Nat.mul_succ]; omega
        rw [back]
        exact ih

/-- A finite disjunction. -/
def anyOf {k : ℕ} : List (Formula Unit k) → Formula Unit k
  | [] => .ff
  | φ :: rest => .disj φ (anyOf rest)

theorem satisfies_anyOf {k : ℕ} (ρ : Env ℕ k) (m : ℕ) :
    ∀ l : List (Formula Unit k), satisfies (chain ()) ρ (anyOf l) m ↔ ∃ φ ∈ l, satisfies (chain ()) ρ φ m
  | [] => by simp [anyOf, satisfies]
  | φ :: rest => by
      show (satisfies (chain ()) ρ φ m ∨ satisfies (chain ()) ρ (anyOf rest) m) ↔ _
      rw [satisfies_anyOf ρ m rest]
      simp

theorem dias_isPositiveIn {k : ℕ} (i : Fin k) (polarity : Bool) (φ : Formula Unit k)
    (positive : φ.isPositiveIn i polarity = true) : ∀ n, (dias n φ).isPositiveIn i polarity = true
  | 0 => positive
  | n + 1 => dias_isPositiveIn i polarity φ positive n

theorem dias_fixedPointsPositive {k : ℕ} (φ : Formula Unit k) (positive : fixedPointsPositive φ = true) :
    ∀ n, fixedPointsPositive (dias n φ) = true
  | 0 => positive
  | n + 1 => dias_fixedPointsPositive φ positive n

theorem exactly_isPositiveIn {k : ℕ} (i : Fin k) (polarity : Bool) (n : ℕ) :
    (exactly n : Formula Unit k).isPositiveIn i polarity = true := by
  show ((dias n .tt).isPositiveIn i polarity && (dias (n + 1) .tt).isPositiveIn i (!polarity)) = true
  rw [dias_isPositiveIn i polarity .tt rfl n, dias_isPositiveIn i (!polarity) .tt rfl (n + 1)]
  rfl

theorem exactly_fixedPointsPositive {k : ℕ} (n : ℕ) :
    fixedPointsPositive (exactly n : Formula Unit k) = true := by
  show (fixedPointsPositive (dias n .tt) && fixedPointsPositive (dias (n + 1) .tt)) = true
  rw [dias_fixedPointsPositive .tt rfl n, dias_fixedPointsPositive .tt rfl (n + 1)]
  rfl

theorem residue_positive (n p : ℕ) : fixedPointsPositive (residue n p) = true := by
  have exactlyPos : (exactly n : Formula Unit 1).isPositiveIn 0 true = true := exactly_isPositiveIn 0 true n
  have stepsPos : (dias p (.var 0) : Formula Unit 1).isPositiveIn 0 true = true :=
    dias_isPositiveIn 0 true (.var 0) rfl p
  have exactlyFix : fixedPointsPositive (exactly n : Formula Unit 1) = true := exactly_fixedPointsPositive n
  have stepsFix : fixedPointsPositive (dias p (.var 0) : Formula Unit 1) = true :=
    dias_fixedPointsPositive (.var 0) rfl p
  show ((exactly n : Formula Unit 1).isPositiveIn 0 true && (dias p (.var 0) : Formula Unit 1).isPositiveIn 0 true &&
    (fixedPointsPositive (exactly n : Formula Unit 1) &&
      fixedPointsPositive (dias p (.var 0) : Formula Unit 1))) = true
  rw [exactlyPos, stepsPos, exactlyFix, stepsFix]
  rfl

theorem anyOf_positive {k : ℕ} : ∀ l : List (Formula Unit k),
    (∀ φ ∈ l, fixedPointsPositive φ = true) → fixedPointsPositive (anyOf l) = true
  | [], _ => rfl
  | φ :: rest, all => by
      show (fixedPointsPositive φ && fixedPointsPositive (anyOf rest)) = true
      rw [all φ (by simp), anyOf_positive rest fun ψ member => all ψ (by simp [member])]
      rfl

/-- **Every ultimately periodic set is denoted on the one-letter chain** by a formula with positive
fixed points: the members below the threshold one by one, and above it one least fixed point per
residue. -/
theorem periodic_denoted (A : Set ℕ) (periodic : UltimatelyPeriodic A) :
    ∃ φ : Formula Unit 0, fixedPointsPositive φ = true ∧
      ∀ m, satisfies (chain ()) (fun _ => ∅) φ m ↔ m ∈ A := by
  classical
  obtain ⟨N, p, period, repeats⟩ := periodic
  have along : ∀ r j, N + r + p * j ∈ A ↔ N + r ∈ A := by
    intro r j
    induction j with
    | zero => simp
    | succ j ih => rw [Nat.mul_succ, ← Nat.add_assoc, repeats _ (by omega), ih]
  refine ⟨.disj (anyOf (((List.range N).filter fun m => decide (m ∈ A)).map exactly))
      (anyOf (((List.range p).filter fun r => decide (N + r ∈ A)).map fun r => residue (N + r) p)),
    ?_, fun m => ?_⟩
  · show (fixedPointsPositive (anyOf (((List.range N).filter fun m => decide (m ∈ A)).map exactly)) &&
      fixedPointsPositive (anyOf (((List.range p).filter fun r => decide (N + r ∈ A)).map
        fun r => residue (N + r) p))) = true
    rw [anyOf_positive _ fun φ member => by
        obtain ⟨n, -, rfl⟩ := List.mem_map.mp member
        exact exactly_fixedPointsPositive n,
      anyOf_positive _ fun φ member => by
        obtain ⟨r, -, rfl⟩ := List.mem_map.mp member
        exact residue_positive (N + r) p]
    rfl
  · refine (or_congr (satisfies_anyOf _ m _) (satisfies_anyOf _ m _)).trans ?_
    simp only [List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq]
    constructor
    · rintro (⟨_, ⟨n, ⟨_, inA⟩, rfl⟩, holds⟩ | ⟨_, ⟨r, ⟨_, inA⟩, rfl⟩, holds⟩)
      · rw [(satisfies_exactly _ n m).mp holds]
        exact inA
      · obtain ⟨j, rfl⟩ := (satisfies_residue (N + r) p m).mp holds
        exact (along r j).mpr inA
    · intro inA
      by_cases small : m < N
      · exact Or.inl ⟨_, ⟨m, ⟨small, inA⟩, rfl⟩, (satisfies_exactly _ m m).mpr rfl⟩
      · right
        have split := Nat.mod_add_div (m - N) p
        have decompose : m = N + (m - N) % p + p * ((m - N) / p) := by
          rw [Nat.add_assoc, split]
          omega
        refine ⟨_, ⟨(m - N) % p, ⟨Nat.mod_lt _ period, ?_⟩, rfl⟩,
          (satisfies_residue _ p m).mpr ⟨(m - N) / p, decompose⟩⟩
        rw [decompose, along] at inA
        exact inA

/-- **On the one-letter chain the formulas with positive fixed points denote exactly the ultimately
periodic sets.** -/
theorem denoted_iff_periodic (A : Set ℕ) :
    (∃ φ : Formula Unit 0, fixedPointsPositive φ = true ∧
        ∀ m, satisfies (chain ()) (fun _ => ∅) φ m ↔ m ∈ A) ↔ UltimatelyPeriodic A := by
  constructor
  · rintro ⟨φ, positive, denotes⟩
    obtain ⟨N, p, period, repeats⟩ := sat_periodic () φ positive
    exact ⟨N, p, period, fun m large =>
      ((denotes (m + p)).symm.trans (repeats m large)).trans (denotes m)⟩
  · exact periodic_denoted A

end Converse

#print axioms periodic_denoted
#print axioms denoted_iff_periodic
#print axioms column_extend
#print axioms fix_computes_mu
#print axioms fix_computes_nu
#print axioms exists_machine
#print axioms output_periodic
#print axioms sat_periodic
#print axioms squares_not_periodic
#print axioms squares_not_denoted

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.WhenTypesApply.OneLetterChain
