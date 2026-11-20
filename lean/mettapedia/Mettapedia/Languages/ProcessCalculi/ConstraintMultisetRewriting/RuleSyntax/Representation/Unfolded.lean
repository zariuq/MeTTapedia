import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Representation.Equivariance

/-!
# The characterization of positive programs, unfolded; the even constants by a program given as a function

* `frameClosed_iff_own_closure`: a relation on bags is frame-closed exactly when it is the frame closure
  (`frameClosure`) of its own transitions. With `presented_iff_frameClosed` this gives `presented_iff_closure`:
  a relation is the rewriting of some set of range-restricted positive rules exactly when it is the frame
  closure of some table of pairs of bags. What `presented_iff_frameClosed` adds to that identity is the
  locality of the step read on bags (`setRewrites_frame`) and the reading on the step (`set_backward`,
  `set_forward`).
* `ground_suffices`: whatever a set of range-restricted positive rules rewrites as, a set of ground take/make
  rules (no unknown, no read, no tell, no guard) rewrites as the same relation. With programs of any size,
  unknowns, reads, tells and guards add no one-step relation.
* `presentsCorrespondence`: `Presents` is an `OperationalCorrespondence` from the relation to the step,
  related by `ReadsBag`, one transition for one firing in each direction.
* `evensProgram_rewrites`: the oracle of the even constants, which no finite list of rules rewrites as
  (`oracle_evens_not_finite`), is the rewriting of the program given by one function from the naturals to
  rules, `j ↦ (take sym (2 j), make yes)` (`evensProgram_fragment`, `evensProgram_not_finite`). So the line
  that finiteness draws is finitely many rules, not effectiveness.
* `evens_not_presented`: on the step, no finite range-restricted positive program presents the oracle of the
  even constants.
* `oracle_not_parallelClosed`: the oracle of a set holding a row other than the answer is not closed under
  putting two transitions side by side: two copies of the row do not become two answers in one transition.
  So a step that may commit two such matches in one firing does not read as the oracle. The statements about
  one firing (`Presents`, `oracle_decides`, `allAtOnce_not_finite`, and the one rewrite for one firing of
  `Machines.correspondence`) are statements about the step whose firing is one match, one candidate for the
  size of a firing (`RuleSyntax/JointFirings/` compares the candidates).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Representation.Unfolded

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis (equalityGSLT)
open LogicOverTheStep.StepSpan (Succ)
open NamesOnTheStep (Expr)
open Presentation.Schematic
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines

universe uO

/-! ## The characterization, unfolded -/

/-- **The frame closure of a table of pairs of bags.** -/
def frameClosure (T : Multiset Expr → Multiset Expr → Prop) (M M' : Multiset Expr) : Prop :=
  ∃ A B N, T A B ∧ M = A + N ∧ M' = B + N

theorem frameClosure_frameClosed (T : Multiset Expr → Multiset Expr → Prop) : FrameClosed (frameClosure T) := by
  rintro M M' N ⟨A, B, N', related, rfl, rfl⟩
  exact ⟨A, B, N' + N, related, add_assoc _ _ _, add_assoc _ _ _⟩

/-- **A relation is frame-closed exactly when it is the frame closure of its own transitions.** -/
theorem frameClosed_iff_own_closure (R : Multiset Expr → Multiset Expr → Prop) :
    FrameClosed R ↔ ∀ M M', frameClosure R M M' ↔ R M M' := by
  constructor
  · intro closed M M'
    constructor
    · rintro ⟨A, B, N, related, rfl, rfl⟩
      exact closed A B N related
    · intro related
      exact ⟨M, M', 0, related, (add_zero _).symm, (add_zero _).symm⟩
  · intro same M M' N related
    exact (same _ _).mp (frameClosure_frameClosed R M M' N ((same M M').mpr related))

/-- **What `presented_iff_frameClosed` says**: a relation on bags is the rewriting of some set of
range-restricted positive rules exactly when it is the frame closure of some table. -/
theorem presented_iff_closure (R : Multiset Expr → Multiset Expr → Prop) :
    (∃ P : Program (OneFrame.Terms Tm), (∀ r ∈ P, RangeRestrictedPositive r) ∧
        ∀ M M', SetRewrites P M M' ↔ R M M') ↔
      ∃ T : Multiset Expr → Multiset Expr → Prop, ∀ M M', frameClosure T M M' ↔ R M M' := by
  rw [presented_iff_frameClosed]
  constructor
  · intro closed
    exact ⟨R, (frameClosed_iff_own_closure R).mp closed⟩
  · rintro ⟨T, same⟩ M M' N related
    exact (same _ _).mp (frameClosure_frameClosed T M M' N ((same M M').mpr related))

/-- **Ground take/make rules suffice**: the rewriting of any set of range-restricted positive rules is the
rewriting of a set of ground rules that take rows and make rows. -/
theorem ground_suffices (P : Program (OneFrame.Terms Tm)) :
    ∃ Q : Program (OneFrame.Terms Tm), (∀ r ∈ Q, ∃ taken made : List Expr, r = groundRule taken made) ∧
      ∀ M M', SetRewrites Q M M' ↔ SetRewrites P M M' :=
  ⟨kernelProgram (SetRewrites P), fun _ ⟨taken, made, _, same⟩ => ⟨taken, made, same⟩,
    setRewrites_kernel_iff fun _ _ N rewrites => setRewrites_frame N rewrites⟩

/-! ## `Presents` is an operational correspondence -/

/-- **`Presents` is an `OperationalCorrespondence`** from the relation to the step of the program, related by
reading a state as a bag: one transition for one firing, both ways. -/
def presentsCorrespondence {O : Type uO} [DecidableEq O] {P : Program (OneFrame.Terms Tm)}
    {R : Multiset Expr → Multiset Expr → Prop} (presents : Presents O P R) :
    OperationalCorrespondence (equalityGSLT (Multiset Expr) R)
      (equalityGSLT (SState O) (Succ (step X O E P).toStep)) where
  related bag s := ReadsBag s bag
  readStep := by
    intro bag s s' reads stepped
    obtain ⟨f, admitted, rfl⟩ := stepped
    obtain ⟨bag', related, reads'⟩ := presents.backward reads f admitted
    exact Or.inr ⟨bag', related, reads'⟩
  forward := by
    intro bag bag' s reads related
    obtain ⟨f, admitted, reads'⟩ := presents.forward reads related
    exact ⟨_, (executionPath_nonempty_iff_multiStep (equalityGSLT (SState O) (Succ (step X O E P).toStep))
      _ _).mpr (.step ⟨f, admitted, rfl⟩ (.refl _)), reads'⟩

/-! ## The oracle of the even constants, by a program given as a function -/

/-- **The program `j ↦ (take sym (2 j), make yes)`**: one ground rule for each natural number. -/
def evensProgram : Program (OneFrame.Terms Tm) :=
  Set.range fun j : ℕ => groundRule [.sym (2 * j)] [yes]

/-- **The program given by that function rewrites as the oracle of the even constants.** -/
theorem evensProgram_rewrites (M M' : Multiset Expr) : SetRewrites evensProgram M M' ↔ Oracle evens M M' := by
  constructor
  · rintro ⟨r, ⟨j, rfl⟩, rewrites⟩
    obtain ⟨rest, split, made⟩ := (rewrites_groundRule_iff _ _ M M').mp rewrites
    exact ⟨.sym (2 * j), ⟨j, rfl⟩, rest, split, made⟩
  · rintro ⟨e, ⟨j, rfl⟩, rest, split, made⟩
    exact ⟨_, ⟨j, rfl⟩, (rewrites_groundRule_iff _ _ M M').mpr ⟨rest, split, made⟩⟩

/-- Every rule of that program is range-restricted and positive. -/
theorem evensProgram_fragment : ∀ r ∈ evensProgram, RangeRestrictedPositive r := by
  rintro r ⟨j, rfl⟩
  exact groundRule_fragment _ _

/-- And no finite list of rules rewrites as it (`oracle_evens_not_finite`, restated with this program). -/
theorem evensProgram_not_finite (rules : List SRule) :
    ¬ ∀ M M', Rewrites rules M M' ↔ SetRewrites evensProgram M M' := fun same =>
  oracle_evens_not_finite rules fun M M' => (same M M').trans (evensProgram_rewrites M M')

/-- **On the step: no finite range-restricted positive program presents the oracle of the even constants.** -/
theorem evens_not_presented (rules : List SRule) (fragment : ∀ r ∈ rules, RangeRestrictedPositive r) :
    ¬ Presents ℕ {r | r ∈ rules} (Oracle evens) := fun presents =>
  oracle_evens_not_finite rules fun M M' =>
    (rewrites_iff_set rules M M').trans
      (setRewrites_of_presents (fun r member => fragment r member) presents M M')

/-! ## Side by side -/

/-- **A relation closed under putting two transitions side by side.** -/
def ParallelClosed (R : Multiset Expr → Multiset Expr → Prop) : Prop :=
  ∀ A A' B B', R A A' → R B B' → R (A + B) (A' + B')

/-- **The oracle of a set holding a row other than the answer is not closed side by side**: two copies of the
row would have to become two answers in one transition, and the oracle answers one at a time. -/
theorem oracle_not_parallelClosed {K : Set Expr} {e : Expr} (member : e ∈ K) (notYes : e ≠ yes) :
    ¬ ParallelClosed (Oracle K) := by
  intro closed
  have once : Oracle K {e} {yes} := ⟨e, member, 0, add_zero _, (add_zero _).symm⟩
  obtain ⟨e', -, rest, split, made⟩ := closed _ _ _ _ once once
  have restYes : rest = {yes} := by
    have counted := congrArg Multiset.card split
    simp only [Multiset.card_add, Multiset.card_singleton] at counted
    have one : Multiset.card rest = 1 := by omega
    obtain ⟨x, isX⟩ := Multiset.card_eq_one.mp one
    rw [isX] at made
    have inside : x ∈ ({yes} + {yes} : Multiset Expr) := by
      rw [made]
      exact Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton_self x))
    simp only [Multiset.singleton_add, Multiset.mem_cons, Multiset.mem_singleton, or_self] at inside
    rw [isX, inside]
  rw [restYes] at split
  have inside : yes ∈ ({e} + {e} : Multiset Expr) := by
    rw [← split]
    exact Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton_self yes))
  simp only [Multiset.singleton_add, Multiset.mem_cons, Multiset.mem_singleton, or_self] at inside
  exact notYes inside.symm

#print axioms frameClosed_iff_own_closure
#print axioms presented_iff_closure
#print axioms ground_suffices
#print axioms presentsCorrespondence
#print axioms evensProgram_rewrites
#print axioms evensProgram_fragment
#print axioms evensProgram_not_finite
#print axioms evens_not_presented
#print axioms oracle_not_parallelClosed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Representation.Unfolded
