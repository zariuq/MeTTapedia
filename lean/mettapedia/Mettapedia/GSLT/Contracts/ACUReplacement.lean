import Mathlib.Data.Multiset.AddSub

/-!
# Ground replacement under a declared ACU operator

The syntax, equational presentation, and contextual rule relation come
first. The executable presentation uses a bag of operands as a key. The
extension theorem proves why matching a sub-bag (not just matching the
whole key) is necessary and sufficient for one quotient step.

This is the homogeneous ground fragment for one operator. The operands
are atoms as far as that operator is concerned, and occurrences retain
multiplicity. A list of ground rules can be enumerated without choosing
one successor or identifying the rule arrows with the equations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.ACUReplacement

universe u
variable {Atom : Type u}

inductive Term (Atom : Type u) where
  | atom (value : Atom)
  | unit
  | op (left right : Term Atom)
  deriving DecidableEq

inductive Equation : Term Atom → Term Atom → Prop where
  | refl (a : Term Atom) : Equation a a
  | symm {a b : Term Atom} : Equation a b → Equation b a
  | trans {a b c : Term Atom} : Equation a b → Equation b c → Equation a c
  | rightUnit (a : Term Atom) : Equation (.op a .unit) a
  | swap (a b : Term Atom) : Equation (.op a b) (.op b a)
  | assoc (a b c : Term Atom) : Equation (.op (.op a b) c) (.op a (.op b c))
  | op {a a' b b' : Term Atom} : Equation a a' → Equation b b' → Equation (.op a b) (.op a' b')

def equations : Setoid (Term Atom) := ⟨Equation, ⟨Equation.refl, Equation.symm, Equation.trans⟩⟩

def operands : Term Atom → Multiset Atom
  | .atom a => {a}
  | .unit => 0
  | .op a b => operands a + operands b

theorem Equation.sameOperands {a b : Term Atom} (eq : Equation a b) :
    operands a = operands b := by
  induction eq with
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ first second => exact first.trans second
  | rightUnit _ => simp [operands]
  | swap _ _ => exact Multiset.add_comm _ _
  | assoc _ _ _ => exact Multiset.add_assoc _ _ _
  | op _ _ first second => simp only [operands, first, second]

/-- This spelling is only for reification in the proofs; its order has
no semantic role. The executable reducer works on operand bags. -/
def spell : List Atom → Term Atom
  | [] => .unit
  | a :: rest => .op (.atom a) (spell rest)

theorem operands_spell (xs : List Atom) : operands (spell xs) = (xs : Multiset Atom) := by
  induction xs with
  | nil => rfl
  | cons a rest ih => simp [spell, operands, ih, Multiset.singleton_add]

private theorem spell_append (xs ys : List Atom) :
    Equation (.op (spell xs) (spell ys)) (spell (xs ++ ys)) := by
  induction xs with
  | nil => exact .trans (.swap ..) (.rightUnit _)
  | cons a rest ih => exact .trans (.assoc ..) (.op (.refl _) ih)

private theorem spell_perm {xs ys : List Atom} (p : xs.Perm ys) :
    Equation (spell xs) (spell ys) := by
  induction p with
  | nil => exact .refl _
  | cons a _ ih => exact .op (.refl (.atom a)) ih
  | swap a b rest =>
      exact .trans (.symm (.assoc ..))
        (.trans (.op (.swap ..) (.refl (spell rest))) (.assoc ..))
  | trans _ _ first second => exact first.trans second

private theorem hasSpelling (t : Term Atom) :
    ∃ xs : List Atom, Equation t (spell xs) := by
  induction t with
  | atom a => exact ⟨[a], .symm (.rightUnit (.atom a))⟩
  | unit => exact ⟨[], .refl _⟩
  | op a b ihA ihB =>
      obtain ⟨xs, sameA⟩ := ihA
      obtain ⟨ys, sameB⟩ := ihB
      exact ⟨xs ++ ys, .trans (.op sameA sameB) (spell_append xs ys)⟩

theorem equation_iff_operands {a b : Term Atom} : Equation a b ↔ operands a = operands b := by
  refine ⟨Equation.sameOperands, fun eq => ?_⟩
  obtain ⟨xs, left⟩ := hasSpelling a
  obtain ⟨ys, right⟩ := hasSpelling b
  have same : (xs : Multiset Atom) = ys := by
    rw [← operands_spell xs, ← operands_spell ys, ← left.sameOperands, ← right.sameOperands, eq]
  exact .trans left (.trans (spell_perm (Multiset.coe_eq_coe.mp same)) (.symm right))

structure Rule (Atom : Type u) where
  lhs : Term Atom
  rhs : Term Atom

/-- A root contraction in an operator context, open to changing
representatives before and after the contraction. -/
inductive Reduces (allowed : Rule Atom → Prop) : Term Atom → Term Atom → Prop where
  | atRoot {rule : Rule Atom} : allowed rule → Reduces allowed rule.lhs rule.rhs
  | left {a b : Term Atom} (kept : Term Atom) :
      Reduces allowed a b → Reduces allowed (.op a kept) (.op b kept)
  | right {a b : Term Atom} (kept : Term Atom) :
      Reduces allowed a b → Reduces allowed (.op kept a) (.op kept b)
  | equiv {a a' b b' : Term Atom} :
      Equation a a' → Reduces allowed a' b' → Equation b' b → Reduces allowed a b

/-- The operator's one-hole contexts, independently of the equation
relation. These are also useful for relating a profiled term syntax to
an ambient contextual calculus. -/
inductive Context (Atom : Type u) where
  | hole
  | left (inner : Context Atom) (kept : Term Atom)
  | right (kept : Term Atom) (inner : Context Atom)

def Context.plug (c : Context Atom) (value : Term Atom) : Term Atom :=
  match c with
  | .hole => value
  | .left inner kept => .op (inner.plug value) kept
  | .right kept inner => .op kept (inner.plug value)

theorem Reduces.plug {allowed : Rule Atom → Prop} {a b : Term Atom}
    (step : Reduces allowed a b) (context : Context Atom) :
    Reduces allowed (context.plug a) (context.plug b) := by
  induction context with
  | hole => exact step
  | left _ kept ih => exact .left kept ih
  | right kept _ ih => exact .right kept ih

/-- Equations can be moved to the endpoints of a step; the middle is
one declared rule at a single ordinary position. -/
theorem reduces_iff_context (allowed : Rule Atom → Prop) (a b : Term Atom) :
    Reduces allowed a b ↔ ∃ rule, allowed rule ∧ ∃ context : Context Atom,
      Equation a (context.plug rule.lhs) ∧ Equation (context.plug rule.rhs) b := by
  constructor
  · intro step
    induction step with
    | atRoot ok => exact ⟨_, ok, .hole, .refl _, .refl _⟩
    | left kept _ ih =>
        obtain ⟨rule, ok, context, before, after⟩ := ih
        exact ⟨rule, ok, .left context kept, .op before (.refl _), .op after (.refl _)⟩
    | right kept _ ih =>
        obtain ⟨rule, ok, context, before, after⟩ := ih
        exact ⟨rule, ok, .right kept context, .op (.refl _) before, .op (.refl _) after⟩
    | equiv before _ after ih =>
        obtain ⟨rule, ok, context, first, second⟩ := ih
        exact ⟨rule, ok, context, before.trans first, second.trans after⟩
  · rintro ⟨rule, ok, context, first, second⟩
    exact .equiv first ((Reduces.atRoot ok).plug context) second

def Extension (rule : Rule Atom) (before after : Multiset Atom) : Prop :=
  ∃ frame, before = operands rule.lhs + frame ∧ after = operands rule.rhs + frame

theorem reduces_iff_extension (allowed : Rule Atom → Prop) (a b : Term Atom) :
    Reduces allowed a b ↔
      ∃ rule, allowed rule ∧ Extension rule (operands a) (operands b) := by
  constructor
  · intro step
    induction step with
    | atRoot ok => exact ⟨_, ok, 0, by simp, by simp⟩
    | left kept _ ih =>
        obtain ⟨rule, ok, frame, first, second⟩ := ih
        exact ⟨rule, ok, frame + operands kept,
          by simp only [operands, first, Multiset.add_assoc],
          by simp only [operands, second, Multiset.add_assoc]⟩
    | right kept _ ih =>
        obtain ⟨rule, ok, frame, first, second⟩ := ih
        refine ⟨rule, ok, frame + operands kept, ?_, ?_⟩
        · simp only [operands, first, Multiset.add_comm (operands kept), Multiset.add_assoc]
        · simp only [operands, second, Multiset.add_comm (operands kept), Multiset.add_assoc]
    | equiv before _ after ih =>
        simpa only [before.sameOperands, ← after.sameOperands] using ih
  · rintro ⟨rule, ok, frame, first, second⟩
    obtain ⟨xs, xs_eq⟩ := Quotient.exists_rep frame
    change (xs : Multiset Atom) = frame at xs_eq
    refine .equiv (a' := .op rule.lhs (spell xs)) (b' := .op rule.rhs (spell xs))
      (equation_iff_operands.mpr ?_) (.left _ (.atRoot ok)) (equation_iff_operands.mpr ?_)
    · simpa only [operands, operands_spell, xs_eq] using first
    · simpa only [operands, operands_spell, xs_eq] using second.symm

/-- One admissible match of a ground rule gives one residual multiset.
The comparison rejects a shortage rather than relying on truncated
subtraction to supply missing operands. -/
def replace? [DecidableEq Atom] (rule : Rule Atom) (before : Multiset Atom) :
    Option (Multiset Atom) :=
  if operands rule.lhs ≤ before then
    some (operands rule.rhs + (before - operands rule.lhs))
  else none

theorem replace?_eq_some_iff [DecidableEq Atom] (rule : Rule Atom) (before after : Multiset Atom) :
    replace? rule before = some after ↔ Extension rule before after := by
  constructor
  · unfold replace?
    split
    · rename_i available
      intro reduced
      exact ⟨before - operands rule.lhs,
        by rw [Multiset.add_comm, Multiset.sub_add_cancel available], (Option.some.inj reduced).symm⟩
    · intro impossible
      cases impossible
  · rintro ⟨frame, rfl, rfl⟩
    rw [replace?, if_pos (Multiset.le_add_right _ _), Multiset.add_comm (operands rule.lhs) frame,
      Multiset.add_sub_cancel_right]

def successors [DecidableEq Atom] (rules : List (Rule Atom)) (before : Multiset Atom) :
    List (Multiset Atom) :=
  rules.filterMap (fun rule => replace? rule before)

theorem mem_successors_iff [DecidableEq Atom] (rules : List (Rule Atom)) (a b : Term Atom) :
    operands b ∈ successors rules (operands a) ↔ Reduces (· ∈ rules) a b := by
  rw [reduces_iff_extension]
  simp only [successors, List.mem_filterMap, replace?_eq_some_iff]

namespace Controls
private def frameInput : Term Nat := .op (.atom 0) (.op (.atom 1) (.atom 2))
private def toLeft : Rule Nat := ⟨.op (.atom 0) (.atom 1), .atom 3⟩
private def toRight : Rule Nat := ⟨toLeft.lhs, .atom 4⟩
private def needsTwo : Rule Nat := ⟨.op (.atom 0) (.atom 0), .atom 5⟩

/-- The redex crosses a bracketing boundary. Both alternatives retain
the third operand, and they have distinct result keys. -/
theorem across_grouping :
    let a : Term Nat := .op (.atom 3) (.atom 2)
    let b : Term Nat := .op (.atom 4) (.atom 2)
    Reduces (· ∈ [toLeft, toRight]) frameInput a ∧
      Reduces (· ∈ [toLeft, toRight]) frameInput b ∧ ¬ Equation a b := by
  dsimp only
  rw [← mem_successors_iff, ← mem_successors_iff, equation_iff_operands]
  decide

theorem missing_duplicate :
    ¬ Reduces (· ∈ [needsTwo]) frameInput (.op (.atom 5) (.atom 2)) := by
  rw [← mem_successors_iff]
  decide

end Controls

#print axioms equation_iff_operands
#print axioms reduces_iff_extension
#print axioms reduces_iff_context
#print axioms mem_successors_iff
#print axioms Controls.across_grouping
#print axioms Controls.missing_duplicate

end Mettapedia.GSLT.Contracts.ACUReplacement
