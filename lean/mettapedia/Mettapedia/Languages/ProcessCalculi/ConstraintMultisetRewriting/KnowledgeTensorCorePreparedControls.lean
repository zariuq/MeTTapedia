import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.KnowledgeTensorCorePreparedFirstOrder

/-!
# Control: an admission that reads the store as a list has no leafwise grade

The leafwise grade of a proof needs permission to be a property of similarity classes of proofs
(`Invariant`). The admission `readsSyntax` permits the candidate `tells` everywhere and every
other candidate only where the first equation of the store is `5 = 5`. It reads the order of the
equations, which configurations with the same solutions need not share.

The proof `tellsThenIdles` tells `5 = 5` and then idles. Beside a context that knows `9 = 9`:

* its structural grade holds (`the_structural_grade_holds`);
* its leafwise permission holds (`the_leafwise_permission_holds`): after the tell, the advanced
  placement has the store `5 = 5`, `9 = 9`;
* no placed proof is permitted (`no_placed_proof_is_permitted`): the placed run reaches the store
  `9 = 9`, `5 = 5`.

So `placed_proof_runs_iff_graded` fails for this admission (`the_graded_reading_fails`), and the
admission is not invariant (`reads_syntax_is_not_invariant`). The admission of the first-order
step is invariant (`FirstOrder.admission_invariant`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore.Controls

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open AnnotatedRuns (Firing firstOrder)
open FirstOrderNativeRuns
open KnowledgeTensorFirstOrderControls (plain one)

/-- Tells `5 = 5`; takes, reads and makes nothing. -/
def tells : Firing Nat Unit Nat := ⟨⟨[], [], [(5, 5)], [], []⟩, [], ⟨[], [], []⟩⟩

/-- Does nothing. -/
def idles : Firing Nat Unit Nat := ⟨⟨[], [], [], [], []⟩, [], ⟨[], [], []⟩⟩

/-- A context that knows `9 = 9` and holds no occurrence. -/
def knowsNine : Configuration Nat Nat := ⟨[(9, 9)], ∅⟩

/-- An admission that reads the store as a list. -/
def readsSyntax : (FirstOrder.effect plain id).Admission :=
  fun {C} f _ => f.rule.tell = [(5, 5)] ∨ C.equations.head? = some (5, 5)

theorem tells_problem_solved {C : Configuration Nat Nat} (solved : plain.Models () C.equations) :
    plain.Models () (tells.selection.problem id tells.rule C) := by
  have shape : tells.selection.problem id tells.rule C = C.equations ++ [] ++ [] ++ [(5, 5)] := rfl
  rw [shape, List.append_nil, List.append_nil]
  refine (plain.models_append () _ _).mpr ⟨solved, ?_⟩
  intro equation member
  obtain rfl := List.mem_singleton.mp member
  exact rfl

theorem idles_problem_solved {C : Configuration Nat Nat} (solved : plain.Models () C.equations) :
    plain.Models () (idles.selection.problem id idles.rule C) := by
  have shape : idles.selection.problem id idles.rule C = C.equations ++ [] ++ [] ++ [] := rfl
  rw [shape, List.append_nil, List.append_nil, List.append_nil]
  exact solved

theorem tells_prepared {C : Configuration Nat Nat} (solved : plain.Models () C.equations) :
    (FirstOrder.effect plain id).Prepares (s := C) tells := by
  refine ⟨⟨List.nodup_nil, List.nodup_nil, rfl, rfl, rfl⟩, ?_,
    (Frames.ofSubstitution_solvable_iff plain _).mpr ⟨(), tells_problem_solved solved⟩⟩
  show Enabled (fun _ : Nat => ()) C.present (tells.selection.commit (T := Unit))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [Selection.commit, tells]

theorem idles_prepared {C : Configuration Nat Nat} (solved : plain.Models () C.equations) :
    (FirstOrder.effect plain id).Prepares (s := C) idles := by
  refine ⟨⟨List.nodup_nil, List.nodup_nil, rfl, rfl, rfl⟩, ?_,
    (Frames.ofSubstitution_solvable_iff plain _).mpr ⟨(), idles_problem_solved solved⟩⟩
  show Enabled (fun _ : Nat => ()) C.present (idles.selection.commit (T := Unit))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [Selection.commit, idles]

theorem one_solved : plain.Models () one.equations := fun _ member => by cases member

theorem knows_nine_solved : plain.Models () knowsNine.equations := by
  intro equation member
  obtain rfl := List.mem_singleton.mp member
  exact rfl

theorem tells_leaf : (proofStep (FirstOrder.effect plain id)).Admits (s := one) tells :=
  ⟨tells_prepared one_solved, trivial⟩

theorem idles_leaf :
    (proofStep (FirstOrder.effect plain id)).Admits (s := tells.result id one) idles :=
  ⟨idles_prepared (tells_problem_solved one_solved), trivial⟩

/-- The proof: tell `5 = 5`, then idle. -/
def tellsThenIdles : (proofStep (FirstOrder.effect plain id)).Run one :=
  .cons tells tells_leaf (.cons idles idles_leaf (.nil _))

theorem the_structural_grade_holds :
    (FirstOrder.proofInterpretation plain id).Checks (left := one) (right := knowsNine) PUnit.unit
      tellsThenIdles := by
  refine ⟨⟨?_, tells_prepared (tensor_solved one_solved knows_nine_solved)⟩,
    ⟨?_, idles_prepared (tensor_solved (tells_problem_solved one_solved) knows_nine_solved)⟩,
    trivial⟩
  · show Disjoint ([] : List Nat).toFinset (∅ : Finset Nat)
    decide
  · show Disjoint ([] : List Nat).toFinset (∅ : Finset Nat)
    decide

theorem the_leafwise_permission_holds :
    PermittedAt readsSyntax (FirstOrder.proofInterpretation plain id) (left := one)
      (right := knowsNine) PUnit.unit tellsThenIdles :=
  ⟨⟨tells_prepared (tensor_solved one_solved knows_nine_solved), Or.inl rfl⟩,
    ⟨idles_prepared (tensor_solved (tells_problem_solved one_solved) knows_nine_solved),
      Or.inr rfl⟩, trivial⟩

theorem no_placed_proof_is_permitted :
    ¬ ∃ native : (proofStep (FirstOrder.effect plain id)).Run (AnnotatedRuns.tensor one knowsNine),
      Places (FirstOrder.proofInterpretation plain id) (left := one) (right := knowsNine)
        PUnit.unit tellsThenIdles native ∧ Permitted readsSyntax native := by
  rintro ⟨native, placed, permitted⟩
  have unfolded : Places (FirstOrder.proofInterpretation plain id) (left := one)
      (right := knowsNine) PUnit.unit (.cons tells tells_leaf (.cons idles idles_leaf (.nil _)))
      native := placed
  obtain ⟨_, moved, _, rfl, _, tail, similar⟩ :=
    Places.cons_inv (FirstOrder.proofInterpretation plain id) unfolded
  obtain ⟨_, _, _, rfl, _, _, _⟩ :=
    Places.cons_inv (FirstOrder.proofInterpretation plain id) tail
  cases moved with
  | nil => exact False.elim similar
  | cons g allowed rest =>
      obtain ⟨_, same, _⟩ := similar
      have which : idles = g := same
      subst which
      rcases permitted.2.1 with told | first
      · have none : idles.rule.tell = [((5 : Nat), (5 : Nat))] := told
        exact absurd none (by decide)
      · have head : (tells.result id (AnnotatedRuns.tensor one knowsNine)).equations.head? =
            some (5, 5) := first
        exact absurd head (by decide)

/-- **Without invariance the graded reading fails.** -/
theorem the_graded_reading_fails :
    ((FirstOrder.proofInterpretation plain id).Checks (left := one) (right := knowsNine) PUnit.unit
        tellsThenIdles ∧
      PermittedAt readsSyntax (FirstOrder.proofInterpretation plain id) (left := one)
        (right := knowsNine) PUnit.unit tellsThenIdles) ∧
      ¬ ∃ native : (proofStep (FirstOrder.effect plain id)).Run (AnnotatedRuns.tensor one knowsNine),
        Places (FirstOrder.proofInterpretation plain id) (left := one) (right := knowsNine)
          PUnit.unit tellsThenIdles native ∧ Permitted readsSyntax native :=
  ⟨⟨the_structural_grade_holds, the_leafwise_permission_holds⟩, no_placed_proof_is_permitted⟩

/-- The admission that reads the store as a list is not a property of similarity classes. -/
theorem reads_syntax_is_not_invariant :
    ¬ Invariant readsSyntax (FirstOrder.proofTransport plain id) :=
  fun invariant => no_placed_proof_is_permitted
    ((placed_proof_runs_iff_graded readsSyntax (FirstOrder.proofInterpretation plain id) invariant
      (left := one) (right := knowsNine) PUnit.unit tellsThenIdles).mpr
      ⟨the_structural_grade_holds, the_leafwise_permission_holds⟩)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore.Controls
