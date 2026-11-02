import Mettapedia.Languages.Metamath.MM0Transfer.Identification
import Metamath.Spec.StoredStatement

/-!
# Projection and identification at the original stored-statement boundary

The original frame conversion includes floating hypotheses in its semantic
hypothesis list. The atomicity condition therefore admits those hypotheses,
rather than assuming that bound-sort hypotheses are absent. A source-valid
unique floating declaration supplies its exact type. Bound-sort essential
expression hypotheses remain an explicit source-profile boundary.

Stored-statement provability uses the owner's untrimmed context, including
its proof-local variable distinctness assumptions. The transfer below acts
on that actual context and keeps its exact hypotheses and conclusion.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM0Transfer.ParsedFrames

open _root_.Metamath
open _root_.Metamath.Spec.Equivalence
open _root_.Metamath.Spec.StoredStatement
open Mettapedia.Languages.Metamath.InferenceSemanticFiniteSupport
  (renameFormula TypePreserving)
open DistinctnessProjection Identification

/-- A direct property of the actual source frame's essential hypotheses. -/
def NoBoundEssential (boundSort : CN → Prop) (frame : Spec.Frame) : Prop :=
  ∀ expression, Spec.Hyp.essential expression ∈ frame.hyps →
    ¬ boundSort expression.typecode.c

/-- Original floating hypotheses satisfy atomicity with their actual declared
type; they need not be removed from the context. -/
theorem frame_atomic_hypotheses {boundSort : CN → Prop} {frame : Spec.Frame}
    (unique : FloatUnique frame) (essential : NoBoundEssential boundSort frame) :
    AtomicHypotheses boundSort (frameToContext frame) := by
  intro formula present bound
  obtain ⟨hypothesis, member, rfl⟩ := hyps_correspondence present
  cases hypothesis with
  | floating sort name =>
      obtain ⟨reference, lookup, sameType⟩ := findVR_of_float_typed unique member
      refine ⟨reference, ?_⟩
      simp only [hypToDeclarativeFormula, lookup]
      exact congrArg (·, [Sym.var reference]) sameType.symm
  | essential expression => exact False.elim (essential expression member bound)

theorem stored_untrim_atomic_hypotheses {boundSort : CN → Prop}
    {frame : Spec.Frame} (expression : Spec.Expr)
    (unique : FloatUnique frame) (essential : NoBoundEssential boundSort frame) :
    AtomicHypotheses boundSort (statementOfFrame frame expression).untrim.ctx :=
  frame_atomic_hypotheses unique essential

/-- A proof of the exact original stored statement can shed its caller's
regular/regular restrictions without pretending the theorem was a base axiom. -/
theorem stored_derivation_projects {boundSort : CN → Prop}
    {axioms : Statement → Prop} (profile : AxiomProfile boundSort axioms)
    {frame : Spec.Frame} {expression : Spec.Expr}
    (unique : FloatUnique frame) (essential : NoBoundEssential boundSort frame)
    (derived : (statementOfFrame frame expression).Provable axioms) :
    Provable axioms
      (projectContext boundSort (statementOfFrame frame expression).untrim.ctx)
      (statementOfFrame frame expression).fmla :=
  derivation_projects profile
    (stored_untrim_atomic_hypotheses expression unique essential) derived

/-- All valid later source partitions of the actual stored statement are
covered, including ones absent from an observed corpus's bundle table. -/
theorem stored_partition_instance {boundSort : CN → Prop}
    {axioms : Statement → Prop} (profile : AxiomProfile boundSort axioms)
    {frame : Spec.Frame} {expression : Spec.Expr}
    (unique : FloatUnique frame) (essential : NoBoundEssential boundSort frame)
    (derived : (statementOfFrame frame expression).Provable axioms)
    (identify : VR → VR) (typed : TypePreserving identify)
    (valid : Valid (projectDJ boundSort
      (statementOfFrame frame expression).untrim.ctx.dj) identify) :
    Provable axioms
      (imageContext
        (projectContext boundSort (statementOfFrame frame expression).untrim.ctx)
        identify valid)
      (renameFormula identify (statementOfFrame frame expression).fmla) :=
  derivation_identifies (stored_derivation_projects profile unique essential derived)
    identify typed valid

end Mettapedia.Languages.Metamath.MM0Transfer.ParsedFrames
