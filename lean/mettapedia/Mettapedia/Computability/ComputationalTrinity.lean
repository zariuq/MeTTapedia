import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.Functor.Const
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.Types.Basic

/-!
# The contextual computational trinity

The computational trinity compares three presentations of contextual
computation:

* programs and operational computations;
* proofs and typed terms; and
* generalized elements in spaces or categories.

Each face is represented as a presheaf.  Thus an element is already indexed by
a context, and substitution is the functorial action along a context map.

`Comparison` is the conservative notion: it asks only for a commuting triangle
of natural transformations.  It imposes no construction order: none of its
faces is declared prior, final, or derivable from the other two.  Candidate
faces may be revised as operational, logical, or spatial constraints are
transported around the triangle.  `Exact` is the stronger trinitarian claim
that the three faces are naturally isomorphic.  Keeping the two notions
separate is important for reflective or proof-relevant systems, where an
extensional observation may forget program occurrence or derivation evidence.

`FragmentwiseComputationalTrinity` adds the corresponding local design law:
substitution-stable fragments transport forward and backward without first
settling an entire language, type theory, or model.
-/

namespace Mettapedia.Computability.ComputationalTrinity

open CategoryTheory

universe u v w

/-- A context-indexed semantic face.  Contravariance makes substitution and
restriction explicit rather than an ambient meta-operation. -/
abbrev Face (Context : Type u) [Category.{v} Context] :=
  Contextᵒᵖ ⥤ Type w

/-- Three contextual presentations connected by a commuting interpretation
triangle.  No map is assumed invertible, and the structure gives no face
priority or construction order. -/
structure Comparison (Context : Type u) [Category.{v} Context] where
  program : Face.{u, v, w} Context
  logic : Face.{u, v, w} Context
  space : Face.{u, v, w} Context
  programToLogic : program ⟶ logic
  logicToSpace : logic ⟶ space
  programToSpace : program ⟶ space
  coherence : programToLogic ≫ logicToSpace = programToSpace

namespace Comparison

variable {Context : Type u} [Category.{v} Context]

/-- The two-step interpretation agrees pointwise with the direct one. -/
theorem coherence_apply (comparison : Comparison.{u, v, w} Context)
    (context : Contextᵒᵖ) (program : comparison.program.obj context) :
    comparison.logicToSpace.app context
        (comparison.programToLogic.app context program) =
      comparison.programToSpace.app context program := by
  simpa using congrArg
    (fun transformation => transformation.app context program)
    comparison.coherence

/-- Extensional observation loses program information at a context when two
distinct programs have the same direct spatial interpretation. -/
def LosesProgramInformation
    (comparison : Comparison.{u, v, w} Context) : Prop :=
  ∃ (context : Contextᵒᵖ)
      (left right : comparison.program.obj context),
    left ≠ right ∧
      comparison.programToSpace.app context left =
        comparison.programToSpace.app context right

end Comparison

/-- The exact computational trinity.  Two natural isomorphisms suffice; the
program-to-space isomorphism is their composite. -/
structure Exact (Context : Type u) [Category.{v} Context] where
  program : Face.{u, v, w} Context
  logic : Face.{u, v, w} Context
  space : Face.{u, v, w} Context
  programLogic : program ≅ logic
  logicSpace : logic ≅ space

namespace Exact

variable {Context : Type u} [Category.{v} Context]

/-- The derived exact interpretation from programs to spaces. -/
def programSpace (trinity : Exact.{u, v, w} Context) :
    trinity.program ≅ trinity.space :=
  trinity.programLogic ≪≫ trinity.logicSpace

/-- Forget invertibility while retaining the commuting comparison triangle. -/
def toComparison (trinity : Exact.{u, v, w} Context) :
    Comparison.{u, v, w} Context where
  program := trinity.program
  logic := trinity.logic
  space := trinity.space
  programToLogic := trinity.programLogic.hom
  logicToSpace := trinity.logicSpace.hom
  programToSpace := trinity.programSpace.hom
  coherence := rfl

/-- Exactness gives a pointwise bijection from programs to spaces. -/
theorem programToSpace_bijective (trinity : Exact.{u, v, w} Context)
    (context : Contextᵒᵖ) :
    Function.Bijective (trinity.programSpace.hom.app context) := by
  exact (trinity.programSpace.app context).toEquiv.bijective

/-- No exact trinity can lose program information in its spatial face. -/
theorem not_losesProgramInformation (trinity : Exact.{u, v, w} Context) :
    ¬ trinity.toComparison.LosesProgramInformation := by
  rintro ⟨context, left, right, distinct, sameObservation⟩
  exact distinct ((trinity.programToSpace_bijective context).1 sameObservation)

end Exact

/-! ## A nontrivial exact two-point model -/

namespace TwoPointExact

/-- Programs, proofs, and points remain distinct authored carriers. -/
inductive Program where
  | stop
  | run
  deriving DecidableEq

inductive Proof where
  | stopped
  | ran
  deriving DecidableEq

inductive Point where
  | zero
  | one
  deriving DecidableEq

def programProof : Program ≃ Proof where
  toFun
    | .stop => .stopped
    | .run => .ran
  invFun
    | .stopped => .stop
    | .ran => .run
  left_inv := by intro program; cases program <;> rfl
  right_inv := by intro proof; cases proof <;> rfl

def proofPoint : Proof ≃ Point where
  toFun
    | .stopped => .zero
    | .ran => .one
  invFun
    | .zero => .stopped
    | .one => .ran
  left_inv := by intro proof; cases proof <;> rfl
  right_inv := by intro point; cases point <;> rfl

abbrev Context := Discrete PUnit

def programFace : Face Context := (Functor.const Contextᵒᵖ).obj Program
def logicFace : Face Context := (Functor.const Contextᵒᵖ).obj Proof
def spaceFace : Face Context := (Functor.const Contextᵒᵖ).obj Point

/-- A concrete exact contextual trinity whose three carriers are not
definitionally identified. -/
noncomputable def model : Exact Context where
  program := programFace
  logic := logicFace
  space := spaceFace
  programLogic := (Functor.const Contextᵒᵖ).mapIso programProof.toIso
  logicSpace := (Functor.const Contextᵒᵖ).mapIso proofPoint.toIso

example : model.programLogic.hom.app (Opposite.op (Discrete.mk PUnit.unit))
    Program.run = Proof.ran := rfl

example : model.programSpace.hom.app (Opposite.op (Discrete.mk PUnit.unit))
    Program.stop = Point.zero := rfl

end TwoPointExact

/-! ## Information loss prevents exactness -/

namespace FirstBitObservation

abbrev Context := Discrete PUnit

def programFace : Face Context :=
  (Functor.const Contextᵒᵖ).obj (Bool × Bool)

def logicFace : Face Context := (Functor.const Contextᵒᵖ).obj Bool
def spaceFace : Face Context := (Functor.const Contextᵒᵖ).obj Bool

def firstBit : programFace ⟶ logicFace :=
  (Functor.const Contextᵒᵖ).map (↾(Prod.fst : Bool × Bool → Bool))

def logicObservation : logicFace ⟶ spaceFace := 𝟙 logicFace

def directObservation : programFace ⟶ spaceFace :=
  (Functor.const Contextᵒᵖ).map (↾(Prod.fst : Bool × Bool → Bool))

/-- This comparison observes only the first program bit. -/
def comparison : Comparison Context where
  program := programFace
  logic := logicFace
  space := spaceFace
  programToLogic := firstBit
  logicToSpace := logicObservation
  programToSpace := directObservation
  coherence := by
    ext context program
    rfl

/-- Distinct programs can have the same extensional observation. -/
theorem comparison_losesProgramInformation :
    comparison.LosesProgramInformation := by
  let context : Contextᵒᵖ := Opposite.op (Discrete.mk PUnit.unit)
  refine ⟨context, (false, false), (false, true), ?_, rfl⟩
  intro equality
  have secondBits := congrArg Prod.snd equality
  simp at secondBits

/-- Consequently this particular comparison is not the forgetful image of an
exact trinity with the same program-to-space interpretation. -/
theorem no_compatible_programSpace_iso :
    ¬ ∃ exactProgramSpace : programFace ≅ spaceFace,
      exactProgramSpace.hom = comparison.programToSpace := by
  rintro ⟨exactProgramSpace, agrees⟩
  let context : Contextᵒᵖ := Opposite.op (Discrete.mk PUnit.unit)
  have sameExact : exactProgramSpace.hom.app context (false, false) =
      exactProgramSpace.hom.app context (false, true) := by
    rw [agrees]
    rfl
  have pairEquality : (false, false) = (false, true) :=
    (exactProgramSpace.app context).toEquiv.injective sameExact
  have secondBits := congrArg Prod.snd pairEquality
  simp at secondBits

end FirstBitObservation

#print axioms Comparison.coherence_apply
#print axioms Exact.programToSpace_bijective
#print axioms Exact.not_losesProgramInformation
#print axioms FirstBitObservation.comparison_losesProgramInformation
#print axioms FirstBitObservation.no_compatible_programSpace_iso

end Mettapedia.Computability.ComputationalTrinity
