import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeStepBisim
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeClosingScopes

/-!
# The two composites of a clear live diamond agree up to dead names

`LiveFiring.closing` shows that the two orders of two live firings that leave each other clear reach
one joint state, carried along an injective inclusion of names, with the private family extended
twice. This module makes the joint state a native state (`jointState`) and the two inclusions
dead-name extensions (`joint_first`, `joint_second`).

* **The two composites agree up to dead names** (`composites_deadEquiv`), whatever the two solver
  returns and budgets.
* **They are bisimilar** (`composites_bisimilar`) for every program that does not see dead names,
  and satisfy the same Hennessy–Milner formulas (`composites_sat_iff`).
* **The concrete diamond of two makers** (`makers_composites_bisimilar`): the hypotheses hold.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)
open NativeResidual NativeClosing
open Mettapedia.GSLT.HennessyMilner (Formula)

namespace NativeDead

variable {S : Signature} {O : Type} [DecidableEq O] {Γ : Ctx S} {sort : S.Srt}
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] {s : NativeState S O Γ sort}

/-- **Extending the private family twice is one injective private reindexing.** -/
theorem lift_eq_reindex (G : ContextualConditionalExecution.Firing s.locals s.state)
    (H : ContextualConditionalExecution.Firing (rawTarget G).locals (rawTarget G).state)
    (ι : Assignment (jointFrame s) H.target.declarations)
    (row : ContextualConditionalRows.Row s.locals (jointFrame s) Γ sort) :
    lift G H ι row =
      ContextualConditionalPublication.reindexPrivate s.locals
        (ContextualPublication.privateFamily (ContextualPublication.privateFamily s.locals G.update.declaration)
          H.update.declaration) H.target.declarations (fun name => .inl (.inl name)) (fun _ => rfl)
        (row.map s.locals (jointFrame s) ι) := by
  unfold lift
  rw [extendPrivate_eq_reindexPrivate, extendPrivate_eq_reindexPrivate]
  exact reindexPrivate_comp s.locals (ContextualPublication.privateFamily s.locals G.update.declaration)
    H.target.declarations (ContextualPublication.privateFamily
      (ContextualPublication.privateFamily s.locals G.update.declaration) H.update.declaration)
    Sum.inl Sum.inl (fun _ => rfl) (fun _ => rfl) _

/-- Exchanging the two copies of the joint frame, name by name. -/
def swapNames : jointNames s → jointNames s
  | .inl name => .inr (.inl name)
  | .inr (.inl name) => .inl name
  | .inr (.inr name) => .inr (.inr name)

omit [DecidableEq O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem swapNames_injective : Function.Injective (swapNames (s := s)) := by
  rintro (a | a | a) (b | b | b) same <;> simp [swapNames] at same <;> simp [same]

variable {f g : LiveFiring s}

/-- **The joint state of a clear live diamond**, as a native state. -/
noncomputable def jointState (first : f.toNative.Realized) (second : g.toNative.Realized)
    (clearF : Clear f g.selection g.rule g.outputs) : NativeState S O Γ sort :=
  ⟨s.Local, s.localEquality, s.locals,
    { Names := jointNames s
      equality := by letI := s.localEquality; letI := s.state.equality; exact inferInstance
      declarations := jointFrame s
      occupied := (rawTarget (LiveFiring.residualExecution first second clearF)).state.occupied
      equations := jointEquations f g.selection g.rule
      present := (rawTarget (LiveFiring.residualExecution first second clearF)).state.present
      rows := jointRows f g.selection g.outputs }⟩

/-- The joint state's inclusion into the first composite (`g`, then `f`). -/
noncomputable def firstInclusion (first : f.toNative.Realized) (second : g.toNative.Realized)
    (clearF : Clear f g.selection g.rule g.outputs) :
    Inclusion (jointState first second clearF) (rawTarget (LiveFiring.residualExecution first second clearF)) :=
  ⟨fun name => .inl (.inl name), fun _ _ same => Sum.inl.inj (Sum.inl.inj same), fun _ => rfl,
    inclusionNames (LiveFiring.execution second) (LiveFiring.residualExecution first second clearF),
    inclusionNames_injective _ _, fun name => by rcases name with name | name | name <;> rfl⟩

theorem firstInclusion_frame (first : f.toNative.Realized) (second : g.toNative.Realized)
    (clearF : Clear f g.selection g.rule g.outputs) :
    (firstInclusion first second clearF).frame =
      inclusion (LiveFiring.execution second) (LiveFiring.residualExecution first second clearF) := by
  funext name
  rcases name with name | name | name <;> rfl

/-- The joint state's inclusion into the second composite (`f`, then `g`), with the copies exchanged. -/
noncomputable def secondInclusion (first : f.toNative.Realized) (second : g.toNative.Realized)
    (clearF : Clear f g.selection g.rule g.outputs) (clearG : Clear g f.selection f.rule f.outputs) :
    Inclusion (jointState first second clearF) (rawTarget (LiveFiring.residualExecution second first clearG)) :=
  ⟨fun name => .inl (.inl name), fun _ _ same => Sum.inl.inj (Sum.inl.inj same), fun _ => rfl,
    fun name => inclusionNames (LiveFiring.execution first) (LiveFiring.residualExecution second first clearG)
      (swapNames name),
    (inclusionNames_injective _ _).comp swapNames_injective,
    fun name => by rcases name with name | name | name <;> rfl⟩

theorem secondInclusion_frame (first : f.toNative.Realized) (second : g.toNative.Realized)
    (clearF : Clear f g.selection g.rule g.outputs) (clearG : Clear g f.selection f.rule f.outputs) :
    (secondInclusion first second clearF clearG).frame =
      Assignment.compose (inclusion (LiveFiring.execution first) (LiveFiring.residualExecution second first clearG))
        (swapCopies s) := by
  funext name
  rcases name with name | name | name
  · exact (instantiate_generator (inclusion (LiveFiring.execution first)
      (LiveFiring.residualExecution second first clearG)) (.inr (.inl name) : jointNames s)).symm
  · exact (instantiate_generator (inclusion (LiveFiring.execution first)
      (LiveFiring.residualExecution second first clearG)) (.inl name : jointNames s)).symm
  · exact (instantiate_generator (inclusion (LiveFiring.execution first)
      (LiveFiring.residualExecution second first clearG)) (.inr (.inr name) : jointNames s)).symm

/-- **The first composite is the joint state extended by dead names.** -/
noncomputable def joint_first (first : f.toNative.Realized) (second : g.toNative.Realized)
    (clearF : Clear f g.selection g.rule g.outputs) (clearG : Clear g f.selection f.rule f.outputs) :
    DeadExtension (jointState first second clearF) (rawTarget (LiveFiring.residualExecution first second clearF)) where
  toInclusion := firstInclusion first second clearF
  rows o := (((LiveFiring.closing first second clearF clearG).2.1 o).1).trans
    ((lift_eq_reindex _ _ _ _).trans (congrArg
      (fun frame : Assignment (jointFrame s) (LiveFiring.residualExecution first second clearF).target.declarations =>
        ContextualConditionalPublication.reindexPrivate s.locals
          (ContextualPublication.privateFamily
            (ContextualPublication.privateFamily s.locals (LiveFiring.execution second).update.declaration)
            (LiveFiring.residualExecution first second clearF).update.declaration)
          (LiveFiring.residualExecution first second clearF).target.declarations
          (fun name => Sum.inl (Sum.inl name)) (fun _ => rfl)
          ((jointRows f g.selection g.outputs o).map s.locals (jointFrame s) frame))
      (firstInclusion_frame first second clearF).symm))
  equations := List.Perm.of_eq (((LiveFiring.closing first second clearF clearG).2.2.1).trans
    (congrArg (fun frame => ContextualResidual.mapProblem frame (jointEquations f g.selection g.rule))
      (firstInclusion_frame first second clearF).symm))
  present := rfl
  occupied := rfl

/-- **The second composite is the joint state extended by dead names**, with the copies exchanged. -/
noncomputable def joint_second (first : f.toNative.Realized) (second : g.toNative.Realized)
    (clearF : Clear f g.selection g.rule g.outputs) (clearG : Clear g f.selection f.rule f.outputs) :
    DeadExtension (jointState first second clearF) (rawTarget (LiveFiring.residualExecution second first clearG)) where
  toInclusion := secondInclusion first second clearF clearG
  rows o := (((LiveFiring.closing first second clearF clearG).2.1 o).2).trans
    ((lift_eq_reindex _ _ _ _).trans (congrArg
      (fun frame : Assignment (jointFrame s) (LiveFiring.residualExecution second first clearG).target.declarations =>
        ContextualConditionalPublication.reindexPrivate s.locals
          (ContextualPublication.privateFamily
            (ContextualPublication.privateFamily s.locals (LiveFiring.execution first).update.declaration)
            (LiveFiring.residualExecution second first clearG).update.declaration)
          (LiveFiring.residualExecution second first clearG).target.declarations
          (fun name => Sum.inl (Sum.inl name)) (fun _ => rfl)
          ((jointRows f g.selection g.outputs o).map s.locals (jointFrame s) frame))
      (secondInclusion_frame first second clearF clearG).symm))
  equations := ((LiveFiring.closing first second clearF clearG).2.2.2).trans
    (List.Perm.of_eq (congrArg (fun frame => ContextualResidual.mapProblem frame (jointEquations f g.selection g.rule))
      (secondInclusion_frame first second clearF clearG).symm))
  present := (LiveFiring.closing first second clearF clearG).1.symm
  occupied := (LiveFiring.closing_occupied first second clearF clearG).symm

/-- **The two composites of a clear live diamond agree up to dead names**, whatever the solver
returns. -/
theorem composites_deadEquiv (first : f.toNative.Realized) (second : g.toNative.Realized)
    (clearF : Clear f g.selection g.rule g.outputs) (clearG : Clear g f.selection f.rule f.outputs) :
    DeadEquiv (native.result (LiveFiring.residual second f) (LiveFiring.after first second clearF))
      (native.result (LiveFiring.residual first g) (LiveFiring.after second first clearG)) :=
  DeadEquiv.of_span (joint_first first second clearF clearG) (joint_second first second clearF clearG)

/-- **The two composites of a clear live diamond are bisimilar** for every program that does not see
dead names. -/
theorem composites_bisimilar {L : Type} {program : L → (t : NativeState S O Γ sort) → LiveFiring t → Prop}
    (invariant : DeadInvariant program) (first : f.toNative.Realized) (second : g.toNative.Realized)
    (clearF : Clear f g.selection g.rule g.outputs) (clearG : Clear g f.selection f.rule f.outputs) :
    Race.Generic.Bisimilar native.toStep (liveOffers program)
      (native.result (LiveFiring.residual second f) (LiveFiring.after first second clearF))
      (native.result (LiveFiring.residual first g) (LiveFiring.after second first clearG)) :=
  bisimilar_of_deadEquiv invariant (composites_deadEquiv first second clearF clearG)

theorem composites_sat_iff {L : Type} {program : L → (t : NativeState S O Γ sort) → LiveFiring t → Prop}
    (invariant : DeadInvariant program) (first : f.toNative.Realized) (second : g.toNative.Realized)
    (clearF : Clear f g.selection g.rule g.outputs) (clearG : Clear g f.selection f.rule f.outputs)
    (φ : Formula PEmpty.{1} L) :
    Race.Generic.Sat native.toStep (liveOffers program) φ
        (native.result (LiveFiring.residual second f) (LiveFiring.after first second clearF)) ↔
      Race.Generic.Sat native.toStep (liveOffers program) φ
        (native.result (LiveFiring.residual first g) (LiveFiring.after second first clearG)) :=
  sat_iff_of_deadEquiv invariant (composites_deadEquiv first second clearF clearG) φ

/-- **The concrete diamond of two makers**: its composites are bisimilar for every closed program. -/
theorem makers_composites_bisimilar {L : Type}
    (program : L → ClosedFiring NativeResidualExample.tiny ℕ ([] : Ctx NativeResidualExample.tiny) () → Prop) :
    Race.Generic.Bisimilar native.toStep (liveOffers (closedOffers program))
      (native.result (LiveFiring.residual (NativeResidualExample.maker_realized 1 none) (NativeResidualExample.maker 0 none))
        (LiveFiring.after (NativeResidualExample.maker_realized 0 none) (NativeResidualExample.maker_realized 1 none)
          (NativeResidualExample.clear_makers 0 1 (by decide))))
      (native.result (LiveFiring.residual (NativeResidualExample.maker_realized 0 none) (NativeResidualExample.maker 1 none))
        (LiveFiring.after (NativeResidualExample.maker_realized 1 none) (NativeResidualExample.maker_realized 0 none)
          (NativeResidualExample.clear_makers 1 0 (by decide)))) :=
  composites_bisimilar (closedOffers_invariant program) (NativeResidualExample.maker_realized 0 none)
    (NativeResidualExample.maker_realized 1 none) (NativeResidualExample.clear_makers 0 1 (by decide))
    (NativeResidualExample.clear_makers 1 0 (by decide))

end NativeDead

#print axioms NativeDead.lift_eq_reindex
#print axioms NativeDead.joint_first
#print axioms NativeDead.joint_second
#print axioms NativeDead.composites_deadEquiv
#print axioms NativeDead.composites_bisimilar
#print axioms NativeDead.composites_sat_iff
#print axioms NativeDead.makers_composites_bisimilar

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
