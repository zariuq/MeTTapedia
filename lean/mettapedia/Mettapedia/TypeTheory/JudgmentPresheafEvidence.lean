import Mettapedia.TypeTheory.JudgmentEquationInitiality
import Mettapedia.TypeTheory.DisplayedPresheafEvidenceUniversal
import Mathlib.CategoryTheory.Functor.Const

/-!
# Coherent native evidence obtained from generated judgments

A contextual family of local rule models assigns evidence carriers to each
program and sends evidence along the actual context arrows. The generated
interpreter is natural under those arrows. Dependent compiler receipts then
retain a supplied derivation, and their target readout computes its semantic
interpretation in the target model at the emitted program.

Local model operations and their natural maps are data; global soundness,
an interpreter and receipt uniqueness are proved here. This does not infer
current-state evidence from an initial certificate.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.JudgmentPresheafEvidence

open _root_.CategoryTheory
open JudgmentDerivation
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafEvidenceTransport DisplayedPresheafEvidenceUniversal

universe u
variable {S : Signature.{u}} {C : Type u} [Category.{u} C]
variable {P Q : Cᵒᵖ ⥤ Type u}

/-- Read the evidence carrier at one judgment from a local model. -/
def evaluationFunctor (j : S.Judgment) : Algebra.{u, u} S ⥤ Type u where
  obj A := A.Carrier j
  map f := TypeCat.ofHom (fun value => f.map (judgment := j) value)

def evidenceFamily (models : P.Elements ⥤ Algebra.{u, u} S)
    (j : S.Judgment) : DisplayedFamily P := models ⋙ evaluationFunctor j

/-- The source certificate is an actual proof tree at every program. -/
def derivationFamily (P : Cᵒᵖ ⥤ Type u) (j : S.Judgment) : DisplayedFamily P :=
  (Functor.const P.Elements).obj (Derivation S j)

def interpretationMap (models : P.Elements ⥤ Algebra.{u, u} S)
    (j : S.Judgment) : derivationFamily P j ⟶ evidenceFamily models j where
  app point := TypeCat.ofHom (fun d => interpret (models.obj point) d)
  naturality := by
    intro source target arrow
    ext d
    exact (interpret_naturality (models.map arrow) d).symm

/-- Generated rule interpretation gives a natural section, not just an
independent choice of evidence at every context. -/
def interpretedSection (models : P.Elements ⥤ Algebra.{u, u} S)
    {j : S.Judgment} (d : Derivation S j) : (evidenceFamily models j).sections where
  val point := interpret (models.obj point) d
  property := by
    intro source target arrow
    change (models.map arrow).map (interpret (models.obj source) d) =
      interpret (models.obj target) d
    exact interpret_naturality (models.map arrow) d

/-- The target model is evaluated at the literal emitted program and its
context, using the supplied source proof tree. -/
def sourceReadout (f : P ⟶ Q) (models : Q.Elements ⥤ Algebra.{u, u} S)
    (j : S.Judgment) : derivationFamily P j ⟶ reindexDisplayed f (evidenceFamily models j) :=
  interpretationMap (f.mapElements ⋙ models) j

def receiptReadout (f : P ⟶ Q) (models : Q.Elements ⥤ Algebra.{u, u} S)
    (j : S.Judgment) : transport f (derivationFamily P j) ⟶ evidenceFamily models j :=
  descend f (sourceReadout f models j)

theorem receiptReadout_computes (f : P ⟶ Q)
    (models : Q.Elements ⥤ Algebra.{u, u} S) {j : S.Judgment}
    (point : P.Elements) (d : Derivation S j) :
    (receiptReadout f models j).app (f.mapElements.obj point)
        ((unit f (derivationFamily P j)).app point d) =
      interpret (models.obj (f.mapElements.obj point)) d := by
  exact descend_unit f (sourceReadout f models j) point d

theorem receiptReadout_unique (f : P ⟶ Q)
    (models : Q.Elements ⥤ Algebra.{u, u} S) (j : S.Judgment)
    (candidate : transport f (derivationFamily P j) ⟶ evidenceFamily models j)
    (computes : restrict f candidate = sourceReadout f models j) :
    candidate = receiptReadout f models j :=
  descend_unique f (sourceReadout f models j) candidate computes

/-- Changing local models by genuine rule homomorphisms changes interpreted
evidence naturally at every program. -/
theorem interpretationMap_naturality {models other : P.Elements ⥤ Algebra.{u, u} S}
    (change : models ⟶ other) (j : S.Judgment) :
    interpretationMap models j ≫ Functor.whiskerRight change (evaluationFunctor j) =
      interpretationMap other j := by
  ext point d
  exact interpret_naturality (change.app point) d

theorem receiptReadout_naturality (f : P ⟶ Q)
    {models other : Q.Elements ⥤ Algebra.{u, u} S}
    (change : models ⟶ other) (j : S.Judgment) :
    receiptReadout f models j ≫ Functor.whiskerRight change (evaluationFunctor j) =
      receiptReadout f other j := by
  ext point receipt
  rcases point with ⟨world, targetProgram⟩
  rcases receipt with ⟨⟨sourceProgram, d⟩, emitted⟩
  change f.app world sourceProgram = targetProgram at emitted
  change P.obj world at sourceProgram
  subst targetProgram
  exact interpret_naturality (change.app (f.mapElements.obj ⟨world, sourceProgram⟩)) d

/-- Initiality determines a compatible local interpreter, rather than
assuming that arbitrary pointwise semantic assignments form one. -/
theorem interpretationMap_unique (models : P.Elements ⥤ Algebra.{u, u} S)
    (candidate : ∀ point : P.Elements, Hom (generated S) (models.obj point))
    (j : S.Judgment) (point : P.Elements) (d : Derivation S j) :
    (candidate point).map d = (interpretationMap models j).app point d := by
  exact congrArg (fun f : Hom (generated S) (models.obj point) => f.map d)
    (interpretation_unique (models.obj point) (candidate point))

end Mettapedia.TypeTheory.JudgmentPresheafEvidence
