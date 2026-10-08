import Mettapedia.Languages.LambdaCalculus.NamePassingAuthoredClassified
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingOperationalFunctor
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.AuthoredEquations
import Mettapedia.OSLF.Syntax.ContextualEquationClassEvents

/-!
# The retained compiler occurrence functor on actual equation classes

The source vertices use the independently authored two scope schemas, and
the target vertices use the independently authored seven polyadic equations.
The complete source and target occurrence objects retain their raw authored
origins. The compiler descends by its proved static comparison and acts on
actual beta/fetch/COMM events; all target substitutions preserve that action.

The induced internal functor acts on arbitrary class-composable paths,
including their genuine chosen composable-edge pullback. This is an
equation-class operational comparison, not an asserted finite-limit or
closed universal property of the free path construction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingEquationClassOperationalFunctor

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open Mettapedia.Languages.LambdaCalculus
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open NamePassingOpenInterpretation NamePassingOperationalEvents
open Mettapedia.CategoryTheory

abbrev SourceClass (Γ : Ctx NamePassing.Presentation.signature) :=
  TermQ NamePassing.AuthoredEquations.equations Γ NamePassing.Presentation.Srt.tm

abbrev TargetClass (Δ : Ctx sig) := TermQ Mettapedia.Languages.ProcessCalculi.PolyadicPi.equations Δ Srt.pr

namespace Target

abbrev Base := OperationalDiagram.Base
abbrev programs : Base ⥤ Type :=
  ContextualEquationClassEvents.termQPresheaf Mettapedia.Languages.ProcessCalculi.PolyadicPi.equations Srt.pr
abbrev events : Base ⥤ Type := OperationalDiagram.events

def quotient : OperationalDiagram.programs ⟶ programs :=
  ContextualEquationClassEvents.quotientNatural Mettapedia.Languages.ProcessCalculi.PolyadicPi.equations Srt.pr

def source : events ⟶ programs := OperationalDiagram.source ≫ quotient
def target : events ⟶ programs := OperationalDiagram.target ≫ quotient

def graph : InternalGraph (Base ⥤ Type) := ⟨programs, events, source, target⟩

def rawToClass : InternalGraph.Hom OperationalDiagram.graph graph where
  vertex := quotient
  edge := 𝟙 events
  source := by ext X event; rfl
  target := by ext X event; rfl

def internalCategory : InternalCategory (Base ⥤ Type) :=
  InternalCategoryPathDiagram.category graph

def rawInternalFunctor : InternalCategory.Hom OperationalDiagram.internalCategory internalCategory :=
  InternalCategoryPathMaps.internalFunctor rawToClass

/-- The class graph's endpoint image is the existing public COMM relation,
including structural endpoint envelopes, at every open context. -/
theorem endpoints_iff_stepModulo {Δ : Ctx sig} (first last : Proc Δ) :
    (∃ event : OperationalDiagram.Event Δ,
      (Quotient.mk _ event.source : TargetClass Δ) = Quotient.mk _ first ∧
      (Quotient.mk _ event.target : TargetClass Δ) = Quotient.mk _ last) ↔
      StepModulo first last := by
  constructor
  · rintro ⟨event, before, after⟩
    have start : StructuralEq first event.source :=
      AuthoredEquations.eqClosure_sound (Quotient.exact before.symm)
    have finish : StructuralEq event.target last :=
      AuthoredEquations.eqClosure_sound (Quotient.exact after)
    obtain ⟨redex, reduct, rawBefore, step, rawAfter⟩ := event.sound
    exact ⟨redex, reduct, .trans start rawBefore, step, .trans rawAfter finish⟩
  · intro step
    obtain ⟨event, before, after⟩ := OperationalDiagram.Event.complete step
    exact ⟨event, congrArg (Quotient.mk _) before, congrArg (Quotient.mk _) after⟩

end Target

abbrev Inputs := NamePassingOperationalFunctor.Inputs
abbrev Base := Target.Base

def compileClass {Γ : Ctx NamePassing.Presentation.signature} {Δ : Ctx sig}
    (inputs : Inputs Γ Δ) (supplied : SourceClass Γ) : TargetClass Δ :=
  Quotient.liftOn supplied
    (fun program => Quotient.mk _ (interpret program inputs.environment inputs.result))
    (by
      intro first last same
      apply Quotient.sound
      exact AuthoredEquations.structuralEq_complete
        (static_preserved (NamePassing.AuthoredEquations.eqClosure_sound same)
          inputs.environment inputs.result))

theorem compileClass_raw {Γ : Ctx NamePassing.Presentation.signature} {Δ : Ctx sig}
    (inputs : Inputs Γ Δ) (supplied : NamePassing.Presentation.Program Γ) :
    compileClass inputs (Quotient.mk _ supplied) =
      Quotient.mk _ (interpret supplied inputs.environment inputs.result) := rfl

/-- The full quotient compiler commutes with every simultaneous target substitution. -/
theorem compileClass_substitution {Γ : Ctx NamePassing.Presentation.signature} {Δ Θ : Ctx sig}
    (inputs : Inputs Γ Δ) (supplied : SourceClass Γ) (assigned : Sub sig Δ Θ) :
    compileClass (inputs.substitute assigned) supplied =
      bindQ assigned (compileClass inputs supplied) := by
  refine Quotient.inductionOn supplied ?_
  intro program
  exact congrArg (Quotient.mk _)
    (interpret_target_substitution program inputs.environment inputs.result assigned).symm

variable (Γ : Ctx NamePassing.Presentation.signature)

def programs : Base ⥤ Type where
  obj X := Inputs Γ X.unop.vars × SourceClass Γ
  map change := TypeCat.ofHom (fun supplied => (supplied.1.substitute change.unop, supplied.2))
  map_id _ := by
    apply ConcreteCategory.hom_ext
    intro supplied
    exact Prod.ext supplied.1.substitute_identity rfl
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro supplied
    exact Prod.ext (supplied.1.substitute_composition first.unop second.unop).symm rfl

abbrev events : Base ⥤ Type := NamePassingOperationalFunctor.events Γ

def source : events Γ ⟶ programs Γ where
  app _ := TypeCat.ofHom (fun supplied => (supplied.1, Quotient.mk _ supplied.2.source))
  naturality _ _ _ := rfl

def target : events Γ ⟶ programs Γ where
  app _ := TypeCat.ofHom (fun supplied => (supplied.1, Quotient.mk _ supplied.2.target))
  naturality _ _ _ := rfl

def graph : InternalGraph (Base ⥤ Type) := ⟨programs Γ, events Γ, source Γ, target Γ⟩

def compileProgram : programs Γ ⟶ Target.programs where
  app _ := TypeCat.ofHom (fun supplied => compileClass supplied.1 supplied.2)
  naturality _ _ change := by
    apply ConcreteCategory.hom_ext
    intro supplied
    exact compileClass_substitution supplied.1 supplied.2 change.unop

def compileEvent : events Γ ⟶ Target.events := NamePassingOperationalFunctor.compileEvent Γ

def graphMap : InternalGraph.Hom (graph Γ) Target.graph where
  vertex := compileProgram Γ
  edge := compileEvent Γ
  source := by
    ext X supplied
    exact congrArg (Quotient.mk _)
      (source_readout supplied.2 supplied.1.environment supplied.1.result)
  target := by
    ext X supplied
    exact congrArg (Quotient.mk _)
      (target_readout supplied.2 supplied.1.environment supplied.1.result)

def rawQuotient : NamePassingOperationalFunctor.programs Γ ⟶ programs Γ where
  app _ := TypeCat.ofHom (fun supplied => (supplied.1, Quotient.mk _ supplied.2))
  naturality _ _ _ := rfl

def rawToClass : InternalGraph.Hom (NamePassingOperationalFunctor.graph Γ) (graph Γ) where
  vertex := rawQuotient Γ
  edge := 𝟙 (events Γ)
  source := by ext X supplied; rfl
  target := by ext X supplied; rfl

theorem complete_vertex_square :
    NamePassingOperationalFunctor.compileProgram Γ ≫ Target.quotient =
      rawQuotient Γ ≫ compileProgram Γ := rfl

def internalCategory : InternalCategory (Base ⥤ Type) :=
  InternalCategoryPathDiagram.category (graph Γ)

def internalFunctor : InternalCategory.Hom (internalCategory Γ) Target.internalCategory :=
  InternalCategoryPathMaps.internalFunctor (graphMap Γ)

def rawInternalFunctor :
    InternalCategory.Hom (NamePassingOperationalFunctor.internalCategory Γ) (internalCategory Γ) :=
  InternalCategoryPathMaps.internalFunctor (rawToClass Γ)

theorem singleton_readout (X : Base) (inputs : Inputs Γ X.unop.vars) (supplied : SourceEvent Γ) :
    (internalFunctor Γ).edge.app X (InternalCategoryPathDiagram.edge (graph Γ) X (inputs, supplied)) =
      InternalCategoryPathDiagram.edge Target.graph X
        (mapEvent supplied inputs.environment inputs.result) :=
  InternalCategoryPathMaps.edge_readout (graphMap Γ) X (inputs, supplied)

theorem path_readout (X : Base)
    (supplied : InternalCategoryDiagram.Arrow ((InternalCategoryPathDiagram.diagram (graph Γ)).obj X)) :
    (internalFunctor Γ).edge.app X supplied =
      ⟨(compileProgram Γ).app X supplied.1, (compileProgram Γ).app X supplied.2.1,
        (InternalCategoryPathMaps.quiverMap (graphMap Γ) X).mapPath supplied.2.2⟩ :=
  InternalCategoryPathMaps.path_readout (graphMap Γ) X supplied

/-- The source endpoint image is the independent static-saturated active
relation, not an endpoint equality or a source-defined target observation. -/
theorem endpoints_iff_sourceModulo (first last : NamePassing.Presentation.Program Γ) :
    (∃ event : SourceEvent Γ,
      (Quotient.mk _ event.source : SourceClass Γ) = Quotient.mk _ first ∧
      (Quotient.mk _ event.target : SourceClass Γ) = Quotient.mk _ last) ↔
      NamePassing.AuthoredClassified.StepModulo first last := by
  constructor
  · rintro ⟨event, before, after⟩
    exact ⟨event.source, event.target,
      NamePassing.AuthoredEquations.eqClosure_sound (Quotient.exact before.symm),
      ⟨event.occurrence⟩,
      NamePassing.AuthoredEquations.eqClosure_sound (Quotient.exact after)⟩
  · rintro ⟨redex, reduct, before, ⟨occurrence⟩, after⟩
    let event := NamePassing.OperationalDiagram.Event.fromOccurrence occurrence
    have complete := NamePassing.OperationalDiagram.Event.total_fromOccurrence occurrence
    have firstRead := congrArg (fun total : NamePassing.OperationalDiagram.TotalOccurrence Γ => total.1) complete
    have lastRead := congrArg (fun total : NamePassing.OperationalDiagram.TotalOccurrence Γ => total.2.1) complete
    refine ⟨event, ?_, ?_⟩
    · exact (congrArg (Quotient.mk _) firstRead).trans
        (Quotient.sound (NamePassing.AuthoredEquations.staticEq_complete before.symm))
    · exact (congrArg (Quotient.mk _) lastRead).trans
        (Quotient.sound (NamePassing.AuthoredEquations.staticEq_complete after))

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingEquationClassOperationalFunctor
