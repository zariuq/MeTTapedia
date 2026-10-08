import Mettapedia.TypeTheory.JudgmentPresheafEvidence
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingDependentRuntimeEvidence

/-!
# Generated native certificates through the actual name-passing compiler

A target diagram supplies local meanings for independently generated rules.
The generated interpreter, its naturality and its universal receipt readout
are constructed by the shared judgment library. They are instantiated here
at the actual compiler map and joined to supplied core-rho executions.

The certificate's judgment is fixed independently of the observer world.
This interface does not identify observer plugging with variable
substitution, or an attached certificate with a typing derivation of the
compiled lambda expression. Current-state certificates still require the
actual operational evidence action.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedEvidence

open _root_.CategoryTheory
open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational
open Mettapedia.TypeTheory
open JudgmentDerivation JudgmentEquationInitiality JudgmentPresheafEvidence
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafEvidenceTransport DisplayedPresheafEvidenceUniversal
open NamePassingDependentEvidence NamePassingDependentRuntimeEvidence
open NamePassingUnaryForward NamePassingEnvironmentEquationsNative

variable {S : Signature}

abbrev certificates (j : S.Judgment) : DisplayedFamily sourcePrograms :=
  derivationFamily sourcePrograms j

abbrev specification (models : compiledPrograms.Elements ⥤ Algebra S)
    (j : S.Judgment) : DisplayedFamily compiledPrograms := evidenceFamily models j

def generatedBody (models : compiledPrograms.Elements ⥤ Algebra S) (j : S.Judgment) :
    certificates j ⟶ reindexDisplayed compilerMap (specification models j) :=
  sourceReadout compilerMap models j

/-- The actual target readout is the unique extension of local rule
interpretation along the genuine compiler receipt adjunction. -/
def compiledReadout (models : compiledPrograms.Elements ⥤ Algebra S) (j : S.Judgment) :
    compiledFamily (certificates j) ⟶ specification models j :=
  receiptReadout compilerMap models j

theorem compiledReadout_computes (models : compiledPrograms.Elements ⥤ Algebra S)
    {j : S.Judgment} (point : sourcePrograms.Elements) (tree : Derivation S j) :
    (compiledReadout models j).app (compilerMap.mapElements.obj point)
      ((carry (certificates j)).app point tree) =
        interpret (models.obj (compilerMap.mapElements.obj point)) tree :=
  receiptReadout_computes compilerMap models point tree

theorem compiledReadout_unique (models : compiledPrograms.Elements ⥤ Algebra S)
    (j : S.Judgment)
    (candidate : compiledFamily (certificates j) ⟶ specification models j)
    (commutes : restrict compilerMap candidate = generatedBody models j) :
    candidate = compiledReadout models j :=
  receiptReadout_unique compilerMap models j candidate commutes

/-- The chosen readout also commutes with an independently supplied
natural change of the target rule models. -/
theorem compiledReadout_naturality
    {models other : compiledPrograms.Elements ⥤ Algebra S} (change : models ⟶ other)
    (j : S.Judgment) :
    compiledReadout models j ≫ Functor.whiskerRight change (evaluationFunctor j) =
      compiledReadout other j := receiptReadout_naturality compilerMap change j

abbrev GeneratedReceipt (models : compiledPrograms.Elements ⥤ Algebra S)
    {j : S.Judgment} (point : sourcePrograms.Elements) (tree : Derivation S j)
    (world : NamePassingSpine.World (scope point)) (code : RhoUnaryCode.Code 0)
    {final : RhoUnaryReadback.TargetProcess}
    (actual : ExecutionPath RhoUnaryReadback.Target
      (RhoUnaryReadback.runtimeProcess code world.available) final) :=
  Receipt (certificates j) (specification models j) (generatedBody models j)
    point tree world code actual

/-- Every supplied execution endpoint has the source path, administrative
accounts and generated certificate readout in one actual receipt. -/
theorem retain_generated_prefix (models : compiledPrograms.Elements ⥤ Algebra S)
    {j : S.Judgment} (point : sourcePrograms.Elements) (tree : Derivation S j)
    (world : NamePassingSpine.World (scope point)) (code : RhoUnaryCode.Code 0)
    (compiled : NamePassingRho.compile point.2 (references (scope point)) .zero
      world.world = some code) {final : RhoUnaryReadback.TargetProcess}
    (actual : ExecutionPath RhoUnaryReadback.Target
      (RhoUnaryReadback.runtimeProcess code world.available) final) :
    Nonempty (GeneratedReceipt models point tree world code actual) :=
  retain_prefix (certificates j) (specification models j) (generatedBody models j)
    point tree world code compiled actual

variable {models : compiledPrograms.Elements ⥤ Algebra S} {j : S.Judgment}
variable {point : sourcePrograms.Elements} {tree : Derivation S j}
variable {world : NamePassingSpine.World (scope point)} {code : RhoUnaryCode.Code 0}
variable {final : RhoUnaryReadback.TargetProcess}
variable {actual : ExecutionPath RhoUnaryReadback.Target
  (RhoUnaryReadback.runtimeProcess code world.available) final}

theorem GeneratedReceipt.interprets (receipt : GeneratedReceipt models point tree world code actual) :
    receipt.specification = interpret (models.obj (compilerMap.mapElements.obj point)) tree :=
  receipt.computed

/-- Initial rule evidence remains the supplied tree even after a
nonempty reflected source history. -/
theorem GeneratedReceipt.tree_retained (receipt : GeneratedReceipt models point tree world code actual) :
    receipt.history.2 = tree := rfl

/-- Soundness of generating equations suffices for equality of readouts.
No equality of distinct authored trees is inferred from this result. -/
theorem GeneratedReceipt.equation_readout (E : Equations S)
    (receipt : GeneratedReceipt models point tree world code actual)
    (laws : Satisfies E (models.obj (compilerMap.mapElements.obj point)))
    (other : Derivation S j) (related : Congruence E tree other) :
    receipt.specification = interpret (models.obj (compilerMap.mapElements.obj point)) other :=
  receipt.interprets.trans (interpretation_respects_congruence E _ laws related)

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedEvidence
