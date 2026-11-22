import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines.Rewriting
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Representation.Union

/-!
# Which relations on bags of rows are steps of positive programs

At the one first-order frame over rows with unknowns, a state that reads as a bag of ground rows
(`Machines.ReadsBag`) fires as the bag rewrites (`Machines.readsBag_backward`, `Machines.readsBag_forward`). So
the step of a range-restricted positive program is read as a relation on bags. This module says which relations
arise.

## Programs of any size

* **Rewriting by a set of rules** (`SetRewrites`): a rule of the set rewrites the bag. A firing uses one rule, so
  the correspondence between rewriting and the step holds for every set of rules, finite or not (`set_backward`,
  `set_forward`: the list form applied to the one rule of the firing, through `Equivalence.reprogram`); for a
  list it is `Machines.Rewrites` (`rewrites_iff_set`).
* **A frame-closed relation** (`FrameClosed`): a transition of a bag is a transition of the bag beside any
  further rows, which stay. Rewriting by any set of rules is frame-closed (`setRewrites_frame`); this is the
  locality of the step, read on bags.
* **Exactly the frame-closed relations** (`presented_iff_frameClosed`): a relation on bags of ground rows is the
  rewriting of some set of range-restricted positive rules exactly when it is frame-closed. The program is the
  set of ground rules "take `M`, make `M'`", one for each transition of the relation (`kernelProgram`).
  On `RuleSyntax.step`: every frame-closed relation is read from the step of that program, one firing for one
  transition, both ways (`frameClosed_presented`, a `Presents`), and a relation that the step of some set of
  range-restricted positive rules reads as is frame-closed (`presents_iff_frameClosed`, through
  `setRewrites_of_presents`).

## The encoding that proves too much, and the hypothesis that excludes it

The converse direction of `presented_iff_frameClosed` asks nothing of the relation but frame closure: no
finiteness and no effectiveness. So with programs of any size, far too many relations are steps of programs.

* **Control** (`oracle_presented`, `oracle_decides`): for every set `K` of rows whatever, the program with one
  ground rule "take `e`, make the answer row" for each `e ∈ K` is positive, and at the one-row state of `e` it
  has an admitted firing exactly when `e ∈ K`. One firing decides membership in an arbitrary set.
* **The hypothesis that excludes it is that the program is finite**: a finite program mentions finitely many
  constants of rows, so its rewriting is unchanged by exchanging two constants beyond them
  (`rewrites_equivariant`, in the module `Equivariance`), and for `K` the even constants no finite list of rules
  rewrites as the oracle of `K` (`oracle_evens_not_finite`, there).
* **Second controls.** Finite programs also consume boundedly: `allAtOnce_not_finite`, the frame-closed relation
  "some number of copies of `a` become as many copies of `b`, at once" is the rewriting of no finite list of
  rules, of any kind. And frame closure is needed: `wholeStore_not_presented`, the relation that rewrites the
  store `{a}` to `{b}` and no other store is the rewriting of no set of positive rules; an absence check is what
  such a relation needs (`Presentation.spawn_refused_beside`, `Presentation.Boundary`).

## What is not characterized

For finite programs the rewriting relation is the frame closure of finitely many schemas, by definition. No
property of the one-step relation short of that is proved to characterize it. Necessary conditions are proved:
frame closure, bounded consumption, invariance under exchanging constants beyond finitely many, and finitely many
successors (`successors_finite`, in the module `Effective`). A candidate for a relation with all four that is the rewriting of no
finite list, not proved here: the oracle of the even numerals in unary notation, whose set is decidable and which
mentions three constants; the reason expected is that a pattern of numerals matches a finite or a cofinite set
of them. A finite program computes that set along a run, with further rows; that is the correspondence of
`Machines`, which is about runs and not about one step.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Representation

open Mettapedia.Logic.LP
open Interface (Frames)
open NamesOnTheStep (Expr)
open Presentation.Schematic
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence (reprogram)

universe uO

/-! ## Rewriting by a set of rules -/

/-- **Rewriting of bags by a set of rules**: a rule of the set rewrites the bag. -/
def SetRewrites (P : Program (OneFrame.Terms Tm)) (bag bag' : Multiset Expr) : Prop :=
  ∃ r ∈ P, Rewrites [r] bag bag'

/-- Rewriting by a list of rules is rewriting by the set of its rules. -/
theorem rewrites_iff_set (rules : List SRule) (bag bag' : Multiset Expr) :
    Rewrites rules bag bag' ↔ SetRewrites {r | r ∈ rules} bag bag' := by
  constructor
  · rintro ⟨r, member, θ, rest, split, readsIn, equations, made⟩
    exact ⟨r, member, r, List.mem_singleton_self r, θ, rest, split, readsIn, equations, made⟩
  · rintro ⟨r, member, r', inside, θ, rest, split, readsIn, equations, made⟩
    obtain rfl := List.mem_singleton.mp inside
    exact ⟨_, member, θ, rest, split, readsIn, equations, made⟩

section Step

variable {O : Type uO} [DecidableEq O]

/-- **An admitted firing of a set of rules is one rewrite by the set**, at a state that reads as a bag, and
its result reads as the rewritten bag. -/
theorem set_backward {P : Program (OneFrame.Terms Tm)} (fragment : ∀ r ∈ P, RangeRestrictedPositive r)
    {s : SState O} {bag : Multiset Expr} (reads : ReadsBag s bag) (f : Firing O E P s.frame)
    (admitted : (step X O E P).Admits (s := s) f) :
    ∃ bag', SetRewrites P bag bag' ∧ ReadsBag ((step X O E P).result f admitted) bag' := by
  have single : ∀ r ∈ [f.rule], RangeRestrictedPositive r := fun r member => by
    rw [List.mem_singleton.mp member]
    exact fragment f.rule f.member
  obtain ⟨bag', rewrites, reads'⟩ :=
    readsBag_backward single reads (reprogram f (List.mem_singleton_self f.rule)) admitted
  exact ⟨bag', ⟨f.rule, f.member, rewrites⟩, reads'⟩

/-- **Every rewrite by a set of rules is an admitted firing**, at a state that reads as the bag, when
identities are infinitely many. -/
theorem set_forward [Infinite O] {P : Program (OneFrame.Terms Tm)}
    (fragment : ∀ r ∈ P, RangeRestrictedPositive r) {s : SState O} {bag bag' : Multiset Expr}
    (reads : ReadsBag s bag) (rewrites : SetRewrites P bag bag') :
    ∃ (f : Firing O E P s.frame) (admitted : (step X O E P).Admits (s := s) f),
      ReadsBag ((step X O E P).result f admitted) bag' := by
  obtain ⟨r, member, single⟩ := rewrites
  have fragmentR : ∀ r' ∈ [r], RangeRestrictedPositive r' := fun r' inside => by
    rw [List.mem_singleton.mp inside]
    exact fragment r member
  obtain ⟨g, admitted, reads'⟩ := readsBag_forward fragmentR reads single
  have isRule : g.rule = r := List.mem_singleton.mp (show g.rule ∈ [r] from g.member)
  have inP : g.rule ∈ P := by
    rw [isRule]
    exact member
  exact ⟨reprogram g inP, admitted, reads'⟩

/-- **The step of a program reads as a relation on bags**: at every state that reads as a bag, an admitted
firing is a transition of the relation whose result reads as its target, and every transition of the relation
is an admitted firing whose result reads as its target. -/
structure Presents (O : Type uO) [DecidableEq O] (P : Program (OneFrame.Terms Tm))
    (R : Multiset Expr → Multiset Expr → Prop) : Prop where
  backward : ∀ {s : SState O} {bag : Multiset Expr}, ReadsBag s bag →
    ∀ (f : Firing O E P s.frame) (admitted : (step X O E P).Admits (s := s) f),
      ∃ bag', R bag bag' ∧ ReadsBag ((step X O E P).result f admitted) bag'
  forward : ∀ {s : SState O} {bag bag' : Multiset Expr}, ReadsBag s bag → R bag bag' →
    ∃ (f : Firing O E P s.frame) (admitted : (step X O E P).Admits (s := s) f),
      ReadsBag ((step X O E P).result f admitted) bag'

/-- A set of range-restricted positive rules whose rewriting is a relation presents it on the step. -/
theorem presents_of_setRewrites [Infinite O] {P : Program (OneFrame.Terms Tm)}
    {R : Multiset Expr → Multiset Expr → Prop} (fragment : ∀ r ∈ P, RangeRestrictedPositive r)
    (same : ∀ M M', SetRewrites P M M' ↔ R M M') : Presents O P R where
  backward reads f admitted := by
    obtain ⟨bag', rewrites, reads'⟩ := set_backward fragment reads f admitted
    exact ⟨bag', (same _ _).mp rewrites, reads'⟩
  forward reads related := set_forward fragment reads ((same _ _).mpr related)

end Step

/-! ## Frame closure -/

/-- **A frame-closed relation on bags**: a transition of a bag is a transition of the bag beside any further
rows, which stay. -/
def FrameClosed (R : Multiset Expr → Multiset Expr → Prop) : Prop :=
  ∀ M M' N, R M M' → R (M + N) (M' + N)

/-- Rewriting by a list of rules is frame-closed. -/
theorem rewrites_frame {rules : List SRule} {M M' : Multiset Expr} (N : Multiset Expr)
    (rewrites : Rewrites rules M M') : Rewrites rules (M + N) (M' + N) := by
  obtain ⟨r, member, θ, rest, split, readsIn, equations, rfl⟩ := rewrites
  exact ⟨r, member, θ, rest + N, (add_assoc _ _ _).symm.trans (congrArg (fun bag => bag + N) split),
    fun q inside => Multiset.mem_add.mpr (Or.inl (readsIn q inside)), equations, add_assoc _ _ _⟩

/-- **Rewriting by a set of rules is frame-closed.** -/
theorem setRewrites_frame {P : Program (OneFrame.Terms Tm)} {M M' : Multiset Expr} (N : Multiset Expr)
    (rewrites : SetRewrites P M M') : SetRewrites P (M + N) (M' + N) := by
  obtain ⟨r, member, single⟩ := rewrites
  exact ⟨r, member, rewrites_frame N single⟩

/-! ## Ground rules, and the program of a relation -/

/-- **The ground rule of two lists of rows**: take the rows of the first, make the rows of the second. -/
def groundRule (taken made : List Expr) : SRule :=
  ⟨PUnit.unit, ⟨taken.map toTerm, [], [], [], made.map toTerm⟩, []⟩

/-- **A ground rule is range-restricted and positive.** -/
theorem groundRule_fragment (taken made : List Expr) : RangeRestrictedPositive (groundRule taken made) := by
  refine ⟨rfl, rfl, fun t inWritten x vars => ?_⟩
  obtain ⟨e, -, rfl⟩ : ∃ e ∈ made, toTerm e = t := by simpa [written, groundRule] using inWritten
  exact absurd vars (vars_toTerm e x)

theorem map_inst_toTerm (θ : ℕ → Expr) : ∀ l : List Expr, (l.map toTerm).map (inst θ) = l
  | [] => rfl
  | e :: l => by
      show inst θ (toTerm e) :: (l.map toTerm).map (inst θ) = e :: l
      rw [inst_toTerm, map_inst_toTerm θ l]

/-- **A ground rule rewrites a bag exactly by replacing its taken rows by its made rows**, beside a rest. -/
theorem rewrites_groundRule_iff (taken made : List Expr) (M M' : Multiset Expr) :
    Rewrites [groundRule taken made] M M' ↔
      ∃ rest : Multiset Expr, (taken : Multiset Expr) + rest = M ∧ M' = (made : Multiset Expr) + rest := by
  constructor
  · rintro ⟨r, member, θ, rest, split, -, -, made'⟩
    obtain rfl := List.mem_singleton.mp member
    exact ⟨rest,
      (congrArg (fun l : List Expr => (l : Multiset Expr) + rest) (map_inst_toTerm θ taken)).symm.trans split,
      made'.trans (congrArg (fun l : List Expr => (l : Multiset Expr) + rest) (map_inst_toTerm θ made))⟩
  · rintro ⟨rest, split, made'⟩
    exact ⟨groundRule taken made, List.mem_singleton_self _, fun _ => .sym 0, rest,
      (congrArg (fun l : List Expr => (l : Multiset Expr) + rest) (map_inst_toTerm _ taken)).trans split,
      fun q member => absurd member List.not_mem_nil, fun e member => absurd member List.not_mem_nil,
      made'.trans (congrArg (fun l : List Expr => (l : Multiset Expr) + rest) (map_inst_toTerm _ made)).symm⟩

/-- **The program of a relation on bags**: one ground rule for each of its transitions. -/
def kernelProgram (R : Multiset Expr → Multiset Expr → Prop) : Program (OneFrame.Terms Tm) :=
  {r | ∃ taken made : List Expr, R (taken : Multiset Expr) (made : Multiset Expr) ∧ r = groundRule taken made}

theorem kernelProgram_fragment (R : Multiset Expr → Multiset Expr → Prop) :
    ∀ r ∈ kernelProgram R, RangeRestrictedPositive r := by
  rintro r ⟨taken, made, -, rfl⟩
  exact groundRule_fragment taken made

/-- **The program of a frame-closed relation rewrites as the relation.** -/
theorem setRewrites_kernel_iff {R : Multiset Expr → Multiset Expr → Prop} (closed : FrameClosed R)
    (M M' : Multiset Expr) : SetRewrites (kernelProgram R) M M' ↔ R M M' := by
  constructor
  · rintro ⟨r, ⟨taken, made, related, rfl⟩, rewrites⟩
    obtain ⟨rest, rfl, rfl⟩ := (rewrites_groundRule_iff taken made M M').mp rewrites
    exact closed _ _ rest related
  · intro related
    refine ⟨groundRule M.toList M'.toList, ⟨M.toList, M'.toList, ?_, rfl⟩,
      (rewrites_groundRule_iff _ _ M M').mpr ⟨0, ?_, ?_⟩⟩
    · rw [Multiset.coe_toList, Multiset.coe_toList]
      exact related
    · rw [Multiset.coe_toList, add_zero]
    · rw [Multiset.coe_toList, add_zero]

/-! ## Exactly the frame-closed relations -/

/-- **The relations on bags of ground rows that are rewriting by a set of range-restricted positive rules are
exactly the frame-closed ones.** -/
theorem presented_iff_frameClosed (R : Multiset Expr → Multiset Expr → Prop) :
    (∃ P : Program (OneFrame.Terms Tm), (∀ r ∈ P, RangeRestrictedPositive r) ∧
        ∀ M M', SetRewrites P M M' ↔ R M M') ↔ FrameClosed R := by
  constructor
  · rintro ⟨P, -, same⟩ M M' N related
    exact (same _ _).mp (setRewrites_frame N ((same M M').mpr related))
  · intro closed
    exact ⟨kernelProgram R, kernelProgram_fragment R, setRewrites_kernel_iff closed⟩

/-- **Every frame-closed relation is read from the step of a positive program**, one firing for one
transition, both ways. -/
theorem frameClosed_presented {O : Type uO} [DecidableEq O] [Infinite O]
    {R : Multiset Expr → Multiset Expr → Prop} (closed : FrameClosed R) :
    Presents O (kernelProgram R) R :=
  presents_of_setRewrites (kernelProgram_fragment R) (setRewrites_kernel_iff closed)

/-- **What the step of a program reads as is its rewriting**: if the step of a set of range-restricted positive
rules reads as a relation, the relation is the rewriting by the set. Every bag is read from a state
(`Machines.exists_reads`), and a state with solvable knowledge reads as one bag. -/
theorem setRewrites_of_presents {P : Program (OneFrame.Terms Tm)} {R : Multiset Expr → Multiset Expr → Prop}
    (fragment : ∀ r ∈ P, RangeRestrictedPositive r) (presents : Presents ℕ P R) (M M' : Multiset Expr) :
    SetRewrites P M M' ↔ R M M' := by
  obtain ⟨s, reads⟩ := exists_reads M
  constructor
  · intro rewrites
    obtain ⟨f, admitted, reads'⟩ := set_forward fragment reads rewrites
    obtain ⟨bag', related, readsToo⟩ := presents.backward reads f admitted
    have same : bag' = M' :=
      readsAs_unique (ReadsBag.readsAs readsToo).1 (ReadsBag.readsAs readsToo).2 (ReadsBag.readsAs reads').2
    rw [← same]
    exact related
  · intro related
    obtain ⟨f, admitted, reads'⟩ := presents.forward reads related
    obtain ⟨bag', rewrites, readsToo⟩ := set_backward fragment reads f admitted
    have same : bag' = M' :=
      readsAs_unique (ReadsBag.readsAs readsToo).1 (ReadsBag.readsAs readsToo).2 (ReadsBag.readsAs reads').2
    rw [← same]
    exact rewrites

/-- **On `RuleSyntax.step`: the relations on bags that the step of some set of range-restricted positive rules
reads as are exactly the frame-closed ones.** -/
theorem presents_iff_frameClosed (R : Multiset Expr → Multiset Expr → Prop) :
    (∃ P : Program (OneFrame.Terms Tm), (∀ r ∈ P, RangeRestrictedPositive r) ∧ Presents ℕ P R) ↔
      FrameClosed R := by
  constructor
  · rintro ⟨P, fragment, presents⟩
    exact (presented_iff_frameClosed R).mp ⟨P, fragment, setRewrites_of_presents fragment presents⟩
  · intro closed
    exact ⟨kernelProgram R, kernelProgram_fragment R, frameClosed_presented closed⟩

/-! ## Control: the oracle of an arbitrary set of rows -/

/-- The answer row. -/
abbrev yes : Expr := .name 0

/-- **The oracle of a set of rows**: a row of the set becomes the answer row, beside any rest. -/
def Oracle (K : Set Expr) (M M' : Multiset Expr) : Prop :=
  ∃ e ∈ K, ∃ rest : Multiset Expr, {e} + rest = M ∧ M' = {yes} + rest

theorem oracle_frameClosed (K : Set Expr) : FrameClosed (Oracle K) := by
  rintro M M' N ⟨e, member, rest, rfl, rfl⟩
  exact ⟨e, member, rest + N, (add_assoc _ _ _).symm, add_assoc _ _ _⟩

/-- **The oracle of any set of rows is rewriting by a set of positive rules.** Nothing is asked of the set. -/
theorem oracle_presented (K : Set Expr) :
    ∃ P : Program (OneFrame.Terms Tm), (∀ r ∈ P, RangeRestrictedPositive r) ∧
      ∀ M M', SetRewrites P M M' ↔ Oracle K M M' :=
  (presented_iff_frameClosed (Oracle K)).mpr (oracle_frameClosed K)

/-- **One firing decides membership in an arbitrary set**: at the one-row state of a row, the program of the
oracle has an admitted firing exactly when the row is in the set. -/
theorem oracle_decides (K : Set Expr) (e : Expr) :
    (∃ (f : Firing ℕ E (kernelProgram (Oracle K)) (rowState e).frame)
        (admitted : (step X ℕ E (kernelProgram (Oracle K))).Admits (s := rowState e) f),
        ReadsBag ((step X ℕ E (kernelProgram (Oracle K))).result f admitted) {yes}) ↔ e ∈ K := by
  constructor
  · rintro ⟨f, admitted, -⟩
    obtain ⟨bag', rewrites, -⟩ := set_backward (kernelProgram_fragment _) (rowState_reads e) f admitted
    obtain ⟨a, member, rest, split, -⟩ := (setRewrites_kernel_iff (oracle_frameClosed K) _ _).mp rewrites
    have inside : a ∈ ({e} : Multiset Expr) := by
      rw [← split]
      exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_singleton_self a))
    rw [Multiset.mem_singleton.mp inside] at member
    exact member
  · intro member
    exact set_forward (kernelProgram_fragment _) (rowState_reads e)
      ((setRewrites_kernel_iff (oracle_frameClosed K) _ _).mpr
        ⟨e, member, 0, add_zero _, (add_zero _).symm⟩)

/-! ## A finite program consumes boundedly -/

/-- **All at once**: some positive number of copies of one row become as many copies of another, beside any
rest. -/
def AllAtOnce (a b : Expr) (M M' : Multiset Expr) : Prop :=
  ∃ (n : ℕ) (rest : Multiset Expr),
    Multiset.replicate (n + 1) a + rest = M ∧ M' = Multiset.replicate (n + 1) b + rest

theorem allAtOnce_frameClosed (a b : Expr) : FrameClosed (AllAtOnce a b) := by
  rintro M M' N ⟨n, rest, rfl, rfl⟩
  exact ⟨n, rest + N, (add_assoc _ _ _).symm, add_assoc _ _ _⟩

/-- **No finite list of rules rewrites all at once**: a rule takes as many rows as it has take patterns. -/
theorem allAtOnce_not_finite {a b : Expr} (different : a ≠ b) (rules : List SRule) :
    ¬ ∀ M M', Rewrites rules M M' ↔ AllAtOnce a b M M' := by
  intro same
  have bound : ∀ r ∈ rules, r.body.take.length ≤ (rules.map fun r => r.body.take.length).foldr max 0 :=
    fun r member => le_foldr_max (List.mem_map_of_mem (f := fun r : SRule => r.body.take.length) member)
  have related : AllAtOnce a b
      (Multiset.replicate ((rules.map fun r => r.body.take.length).foldr max 0 + 1) a)
      (Multiset.replicate ((rules.map fun r => r.body.take.length).foldr max 0 + 1) b) :=
    ⟨_, 0, add_zero _, (add_zero _).symm⟩
  obtain ⟨r, member, θ, rest, split, -, -, made⟩ := (same _ _).mpr related
  have counted := congrArg Multiset.card split
  rw [Multiset.card_add, Multiset.coe_card, List.length_map, Multiset.card_replicate] at counted
  have restPositive : 0 < Multiset.card rest := by
    have small := bound r member
    omega
  obtain ⟨x, inRest⟩ := Multiset.card_pos_iff_exists_mem.mp restPositive
  have inA : x ∈ Multiset.replicate ((rules.map fun r => r.body.take.length).foldr max 0 + 1) a := by
    rw [← split]
    exact Multiset.mem_add.mpr (Or.inr inRest)
  have inB : x ∈ Multiset.replicate ((rules.map fun r => r.body.take.length).foldr max 0 + 1) b := by
    rw [made]
    exact Multiset.mem_add.mpr (Or.inr inRest)
  exact different ((Multiset.eq_of_mem_replicate inA).symm.trans (Multiset.eq_of_mem_replicate inB))

/-! ## Frame closure is needed -/

/-- The relation that rewrites the store `{a}` to `{b}`, and no other store. -/
def WholeStore (a b : Expr) (M M' : Multiset Expr) : Prop := M = {a} ∧ M' = {b}

theorem wholeStore_not_frameClosed (a b : Expr) : ¬ FrameClosed (WholeStore a b) := by
  intro closed
  have extended := closed {a} {b} {a} ⟨rfl, rfl⟩
  have counted := congrArg Multiset.card extended.1
  rw [Multiset.card_add, Multiset.card_singleton] at counted
  omega

/-- **A relation on whole stores is rewriting by no set of positive rules.** -/
theorem wholeStore_not_presented (a b : Expr) :
    ¬ ∃ P : Program (OneFrame.Terms Tm), (∀ r ∈ P, RangeRestrictedPositive r) ∧
      ∀ M M', SetRewrites P M M' ↔ WholeStore a b M M' :=
  fun presented => wholeStore_not_frameClosed a b ((presented_iff_frameClosed _).mp presented)

#print axioms rewrites_iff_set
#print axioms set_backward
#print axioms set_forward
#print axioms setRewrites_frame
#print axioms groundRule_fragment
#print axioms presented_iff_frameClosed
#print axioms frameClosed_presented
#print axioms setRewrites_of_presents
#print axioms presents_iff_frameClosed
#print axioms oracle_presented
#print axioms oracle_decides
#print axioms allAtOnce_not_finite
#print axioms wholeStore_not_presented

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Representation
