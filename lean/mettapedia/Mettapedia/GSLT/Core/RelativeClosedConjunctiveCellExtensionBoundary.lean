import Mettapedia.GSLT.Core.RelativeClosedConjunctiveUniversalControls

/-!
# A noninvertible base cell need not extend with a fixed fresh proposition

Two actual finite-limit closed Boolean base interpretations differ at the
false object: its first fibre is empty and its second fibre is inhabited.
Both are extended by the same independently supplied Boolean operations.
The generated constant-abstraction arrow identifies its two complete inputs
under the first interpretation and separates them under the second one.

Consequently no complete natural transformation between those interpretations
can have the identity fresh-proposition reading. The base natural
transformation itself exists. This separates an isomorphism-based coherent
extension contract from a proposed extension of every noninvertible base cell;
it does not restrict the ambient category of ordinary natural transformations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedConjunctiveCellExtensionBoundary

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open scoped _root_.CategoryTheory.SemilatticeInf
open scoped Mettapedia.CategoryTheory.PredicateDoctrine.HeytingClosed
open Mettapedia.CategoryTheory
open RelativeClosedSyntax GeneratedCategory RelativeClosedConjunctive

abbrev firstBase := RelativeClosedWeakBaseControls.truthFunctor
abbrev lastBase := LambdaTheoryStructuredControls.topFunctor ⋙ firstBase
abbrev meaning := RelativeClosedConjunctiveControls.boolean
abbrev laws := RelativeClosedConjunctiveControls.boolean_laws

instance last_closed : MonoidalClosedFunctor lastBase :=
  CartesianClosedFunctorCoherence.closed_composition LambdaTheoryStructuredControls.topFunctor firstBase

instance last_lex : PreservesFiniteLimits lastBase :=
  comp_preservesFiniteLimits LambdaTheoryStructuredControls.topFunctor firstBase

def baseCell : firstBase ⟶ lastBase where
  app object := firstBase.map (LambdaTheoryStructuredControls.grow.app object)
  naturality {_ _} arrow :=
    (firstBase.map_comp arrow (LambdaTheoryStructuredControls.grow.app _)).symm.trans
      ((congrArg firstBase.map (LambdaTheoryStructuredControls.grow.naturality arrow)).trans
        (firstBase.map_comp (LambdaTheoryStructuredControls.grow.app _)
          (LambdaTheoryStructuredControls.topFunctor.map arrow)))

def firstModel := ModelReadout.model firstBase meaning laws
def lastModel := ModelReadout.model lastBase meaning laws

abbrev firstDiagram := firstModel.diagram
abbrev lastDiagram := lastModel.diagram

def fresh := (NativePredicates.operations (C := Bool)).proposition
def argument := baseObject (nativeSignature (C := Bool)) false
def captureRaw : RawHom fresh (exponentialObject argument fresh) :=
  RawHom.abstract (RawHom.first fresh argument)

def constantCapture (input : Type) : ULift.{0} Bool ⟶ (input ⟶[Type] ULift.{0} Bool) :=
  TypeCat.ofHom (fun value => TypeCat.ofHom (fun _ => value))

private theorem constant_capture (input : Type) :
    RelativeClosedSyntax.Interpretation.abstraction
        (CartesianMonoidalCategory.fst (ULift.{0} Bool) input) = constantCapture input := rfl

theorem first_proposition_read : firstDiagram.obj fresh = ULift.{0} Bool :=
  ModelReadout.proposition_read firstBase meaning laws

theorem last_proposition_read : lastDiagram.obj fresh = ULift.{0} Bool :=
  ModelReadout.proposition_read lastBase meaning laws

theorem first_function_read : firstDiagram.obj (exponentialObject argument fresh) =
    (firstBase.obj false ⟶[Type] ULift.{0} Bool) :=
  RelativeClosedSyntax.Interpretation.objectValue_unique firstModel.meanings firstModel.realization
    (exponentialObject argument fresh) (firstBase.obj false ⟶[Type] ULift.{0} Bool)
    (firstModel.meanings.evaluate_exponential rfl rfl)

theorem last_function_read : lastDiagram.obj (exponentialObject argument fresh) =
    (lastBase.obj false ⟶[Type] ULift.{0} Bool) :=
  RelativeClosedSyntax.Interpretation.objectValue_unique lastModel.meanings lastModel.realization
    (exponentialObject argument fresh) (lastBase.obj false ⟶[Type] ULift.{0} Bool)
    (lastModel.meanings.evaluate_exponential rfl rfl)

private theorem first_capture_heq :
    HEq (firstDiagram.map (classOf captureRaw)) (constantCapture (firstBase.obj false)) := by
  apply RelativeClosedSyntax.Interpretation.functor_map_heq firstModel.meanings firstModel.realization captureRaw
  rw [← constant_capture]
  exact firstModel.meanings.evaluate_abstraction _ rfl rfl rfl
    (firstModel.meanings.evaluate_first rfl rfl)

private theorem last_capture_heq :
    HEq (lastDiagram.map (classOf captureRaw)) (constantCapture (lastBase.obj false)) := by
  apply RelativeClosedSyntax.Interpretation.functor_map_heq lastModel.meanings lastModel.realization captureRaw
  rw [← constant_capture]
  exact lastModel.meanings.evaluate_abstraction _ rfl rfl rfl
    (lastModel.meanings.evaluate_first rfl rfl)

def firstCapture : ULift.{0} Bool ⟶ (firstBase.obj false ⟶[Type] ULift.{0} Bool) :=
  eqToHom first_proposition_read.symm ≫ firstDiagram.map (classOf captureRaw) ≫ eqToHom first_function_read

def lastCapture : ULift.{0} Bool ⟶ (lastBase.obj false ⟶[Type] ULift.{0} Bool) :=
  eqToHom last_proposition_read.symm ≫ lastDiagram.map (classOf captureRaw) ≫ eqToHom last_function_read

theorem first_capture_read : firstCapture = constantCapture (firstBase.obj false) :=
  ((conj_eqToHom_iff_heq (constantCapture (firstBase.obj false)) _
    first_proposition_read.symm first_function_read.symm).mpr first_capture_heq.symm).symm

theorem last_capture_read : lastCapture = constantCapture (lastBase.obj false) :=
  ((conj_eqToHom_iff_heq (constantCapture (lastBase.obj false)) _
    last_proposition_read.symm last_function_read.symm).mpr last_capture_heq.symm).symm

theorem first_capture_collides : firstCapture (ULift.up false) = firstCapture (ULift.up true) := by
  rw [first_capture_read]
  apply TypeCat.Hom.ext
  apply TypeCat.Fun.ext
  funext value
  exact False.elim (RelativeClosedWeakBaseControls.false_fibre_empty.false value)

theorem last_capture_separates : lastCapture (ULift.up false) ≠ lastCapture (ULift.up true) := by
  rw [last_capture_read]
  intro same
  have read := congrArg (fun function : lastBase.obj false ⟶ ULift.{0} Bool =>
    (function RelativeClosedWeakBaseControls.trueValue).down) same
  exact Bool.false_ne_true read

def propositionCell (cell : firstDiagram ⟶ lastDiagram) : ULift.{0} Bool ⟶ ULift.{0} Bool :=
  eqToHom first_proposition_read.symm ≫ cell.app fresh ≫ eqToHom last_proposition_read

def functionCell (cell : firstDiagram ⟶ lastDiagram) :
    (firstBase.obj false ⟶[Type] ULift.{0} Bool) ⟶ (lastBase.obj false ⟶[Type] ULift.{0} Bool) :=
  eqToHom first_function_read.symm ≫ cell.app (exponentialObject argument fresh) ≫ eqToHom last_function_read

private theorem cast_naturality {K : Type} [Category.{0} K] {F G : K ⥤ Type}
    {source target : K} {A B A' B' : Type}
    (sourceF : F.obj source = A) (targetF : F.obj target = B)
    (sourceG : G.obj source = A') (targetG : G.obj target = B')
    (cell : F ⟶ G) (arrow : source ⟶ target) :
    (eqToHom sourceF.symm ≫ F.map arrow ≫ eqToHom targetF) ≫
        (eqToHom targetF.symm ≫ cell.app target ≫ eqToHom targetG) =
      (eqToHom sourceF.symm ≫ cell.app source ≫ eqToHom sourceG) ≫
        (eqToHom sourceG.symm ≫ G.map arrow ≫ eqToHom targetG) := by
  subst A
  subst B
  subst A'
  subst B'
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using cell.naturality arrow

theorem complete_capture_naturality (cell : firstDiagram ⟶ lastDiagram) :
    firstCapture ≫ functionCell cell = propositionCell cell ≫ lastCapture :=
  cast_naturality first_proposition_read first_function_read last_proposition_read last_function_read
    cell (classOf captureRaw)

theorem no_complete_cell_with_fixed_fresh_proposition :
    ¬ ∃ cell : firstDiagram ⟶ lastDiagram, propositionCell cell = 𝟙 (ULift.{0} Bool) := by
  rintro ⟨cell, fixed⟩
  have natural := complete_capture_naturality cell
  rw [fixed, Category.id_comp] at natural
  have first := congrArg (fun arrow : ULift.{0} Bool ⟶ (lastBase.obj false ⟶[Type] ULift.{0} Bool) =>
    arrow (ULift.up false)) natural
  have second := congrArg (fun arrow : ULift.{0} Bool ⟶ (lastBase.obj false ⟶[Type] ULift.{0} Bool) =>
    arrow (ULift.up true)) natural
  change functionCell cell (firstCapture (ULift.up false)) = lastCapture (ULift.up false) at first
  change functionCell cell (firstCapture (ULift.up true)) = lastCapture (ULift.up true) at second
  exact last_capture_separates (first.symm.trans
    ((congrArg (functionCell cell) first_capture_collides).trans second))

theorem base_cell_is_supplied_and_cannot_have_that_extension :
    Nonempty (firstBase ⟶ lastBase) ∧
      ¬ ∃ cell : firstDiagram ⟶ lastDiagram, propositionCell cell = 𝟙 (ULift.{0} Bool) :=
  ⟨⟨baseCell⟩, no_complete_cell_with_fixed_fresh_proposition⟩

end Mettapedia.GSLT.Core.RelativeClosedConjunctiveCellExtensionBoundary
