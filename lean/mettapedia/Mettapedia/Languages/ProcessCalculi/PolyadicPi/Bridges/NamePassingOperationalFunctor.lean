import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingOperationalSubstitution

/-!
# The actual internal occurrence functor of the open compiler

Names, ordinary source program bodies and the public return vary together
over every target simultaneous substitution. Source vertices and occurrences
retain these supplied inputs. The independently authored target diagram uses
COMM reaction trees with structural endpoint envelopes. Full reaction
naturality, not a chosen simulation witness, earns the event graph map.

The induced internal functor preserves identities and composition on the
actual chosen pullback and maps arbitrary retained occurrence paths. This is
an operational diagram comparison; it does not assert that free path objects
are a finite-limit or closed classifying presentation of either guest theory.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingOperationalFunctor

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open Mettapedia.Languages.LambdaCalculus
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open NamePassingOpenInterpretation NamePassingOperationalEvents
open Mettapedia.CategoryTheory

structure Inputs (Γ : Ctx NamePassing.Presentation.signature) (Δ : Ctx sig) where
  environment : Environment Γ Δ
  result : Name Δ

namespace Inputs

def substitute {Γ : Ctx NamePassing.Presentation.signature} {Δ Θ : Ctx sig}
    (assigned : Sub sig Δ Θ) (inputs : Inputs Γ Δ) : Inputs Γ Θ :=
  ⟨inputs.environment.substitute assigned, bind assigned inputs.result⟩

@[ext] theorem ext {Γ : Ctx NamePassing.Presentation.signature} {Δ : Ctx sig}
    {first second : Inputs Γ Δ} (environments : first.environment = second.environment)
    (returns : first.result = second.result) : first = second := by
  cases first
  cases second
  cases environments
  cases returns
  rfl

theorem substitute_identity {Γ : Ctx NamePassing.Presentation.signature} {Δ : Ctx sig}
    (inputs : Inputs Γ Δ) : inputs.substitute (fun _ position => .var position) = inputs := by
  apply Inputs.ext
  · exact inputs.environment.substitute_identity
  · exact bind_id inputs.result

theorem substitute_composition {Γ : Ctx NamePassing.Presentation.signature} {Δ Θ Ξ : Ctx sig}
    (inputs : Inputs Γ Δ) (first : Sub sig Δ Θ) (second : Sub sig Θ Ξ) :
    (inputs.substitute first).substitute second =
      inputs.substitute (fun sort position => bind second (first sort position)) := by
  apply Inputs.ext
  · exact inputs.environment.substitute_composition first second
  · exact bind_comp first second inputs.result

end Inputs

abbrev Base := OperationalDiagram.Base

variable (Γ : Ctx NamePassing.Presentation.signature)

def programs : Base ⥤ Type where
  obj X := Inputs Γ X.unop.vars × NamePassing.Presentation.Program Γ
  map change := TypeCat.ofHom (fun supplied => (supplied.1.substitute change.unop, supplied.2))
  map_id _ := by
    apply ConcreteCategory.hom_ext
    intro supplied
    exact Prod.ext supplied.1.substitute_identity rfl
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro supplied
    exact Prod.ext (supplied.1.substitute_composition first.unop second.unop).symm rfl

def events : Base ⥤ Type where
  obj X := Inputs Γ X.unop.vars × SourceEvent Γ
  map change := TypeCat.ofHom (fun supplied => (supplied.1.substitute change.unop, supplied.2))
  map_id _ := by
    apply ConcreteCategory.hom_ext
    intro supplied
    exact Prod.ext supplied.1.substitute_identity rfl
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro supplied
    exact Prod.ext (supplied.1.substitute_composition first.unop second.unop).symm rfl

def source : events Γ ⟶ programs Γ where
  app _ := TypeCat.ofHom (fun supplied => (supplied.1, supplied.2.source))
  naturality _ _ _ := rfl

def target : events Γ ⟶ programs Γ where
  app _ := TypeCat.ofHom (fun supplied => (supplied.1, supplied.2.target))
  naturality _ _ _ := rfl

def graph : InternalGraph (Base ⥤ Type) :=
  ⟨programs Γ, events Γ, source Γ, target Γ⟩

def compileProgram : programs Γ ⟶ OperationalDiagram.programs where
  app _ := TypeCat.ofHom (fun supplied => interpret supplied.2 supplied.1.environment supplied.1.result)
  naturality _ _ change := by
    apply ConcreteCategory.hom_ext
    intro supplied
    exact (interpret_target_substitution supplied.2 supplied.1.environment supplied.1.result change.unop).symm

def compileEvent : events Γ ⟶ OperationalDiagram.events where
  app _ := TypeCat.ofHom (fun supplied => mapEvent supplied.2 supplied.1.environment supplied.1.result)
  naturality _ _ change := by
    apply ConcreteCategory.hom_ext
    intro supplied
    exact (event_substitution supplied.2 supplied.1.environment supplied.1.result change.unop).symm

/-- Both whole endpoint squares follow from the actual beta, fetch and
active-position readouts; they are not simulation admission fields. -/
def graphMap : InternalGraph.Hom (graph Γ) OperationalDiagram.graph where
  vertex := compileProgram Γ
  edge := compileEvent Γ
  source := by
    ext X supplied
    exact source_readout supplied.2 supplied.1.environment supplied.1.result
  target := by
    ext X supplied
    exact target_readout supplied.2 supplied.1.environment supplied.1.result

def internalCategory : InternalCategory (Base ⥤ Type) :=
  InternalCategoryPathDiagram.category (graph Γ)

/-- The complete internal path functor has the genuine target COMM diagram
as codomain, rather than a source-defined target observation. -/
def internalFunctor : InternalCategory.Hom (internalCategory Γ) OperationalDiagram.internalCategory :=
  InternalCategoryPathMaps.internalFunctor (graphMap Γ)

theorem singleton_readout (X : Base) (inputs : Inputs Γ X.unop.vars) (supplied : SourceEvent Γ) :
    (internalFunctor Γ).edge.app X (InternalCategoryPathDiagram.edge (graph Γ) X (inputs, supplied)) =
      InternalCategoryPathDiagram.edge OperationalDiagram.graph X
        (mapEvent supplied inputs.environment inputs.result) :=
  InternalCategoryPathMaps.edge_readout (graphMap Γ) X (inputs, supplied)

theorem path_readout (X : Base)
    (supplied : InternalCategoryDiagram.Arrow ((InternalCategoryPathDiagram.diagram (graph Γ)).obj X)) :
    (internalFunctor Γ).edge.app X supplied =
      ⟨(compileProgram Γ).app X supplied.1, (compileProgram Γ).app X supplied.2.1,
        (InternalCategoryPathMaps.quiverMap (graphMap Γ) X).mapPath supplied.2.2⟩ :=
  InternalCategoryPathMaps.path_readout (graphMap Γ) X supplied

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingOperationalFunctor
