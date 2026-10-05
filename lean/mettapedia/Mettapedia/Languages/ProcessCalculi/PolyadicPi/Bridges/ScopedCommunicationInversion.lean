import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedActiveFrontier
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.AuthoredClassified

/-!
# Actual communication inversion in one common scoped world

Every directed communication, and every equation-closed communication,
has one unary or binary redex under a finite private telescope with an exact
untouched parallel frame. The result is opening that supplied input body
with those supplied data, and retaining that same frame and telescope.

The occurrence is extracted from the real step derivation; it is not a
new transition authority. Static changes of source and target representatives
retain its class endpoints. Matching such occurrences to compiler origins
is a further image-invariant obligation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedCommunicationInversion

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.AuthoredOperationalProfile
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.AuthoredClassified
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedActiveFrontier

/-- Exact selected input/output data, independently of the surrounding
parallel composition and private restrictions. -/
inductive Communication : {Γ : Ctx sig} → Proc Γ → Proc Γ → Type where
  | unary {Γ} (channel datum : Name Γ) (body : Proc (.nm :: Γ)) :
      Communication (par (out1 channel datum) (inp1 channel body)) (inst body datum)
  | binary {Γ} (channel first second : Name Γ) (body : Proc (.nm :: .nm :: Γ)) :
      Communication (par (out2 channel first second) (inp2 channel body))
        (openPair body first second)

theorem Communication.sound {Γ : Ctx sig} {redex reduct : Proc Γ}
    (selected : Communication redex reduct) : Step redex reduct := by
  cases selected with
  | unary channel datum body => exact .comm1 channel datum body
  | binary channel first second body => exact .comm2 channel first second body

/-- A real selected communication, including the exact scopes and frame
needed to interpret both of its supplied endpoints. -/
structure Exposure {Γ : Ctx sig} (source target : Proc Γ) where
  world : Ctx sig
  scope : Scope Γ world
  redex : Proc world
  reduct : Proc world
  selected : Communication redex reduct
  frame : Proc world
  before : StructuralEq source (scope.close (par redex frame))
  after : StructuralEq (scope.close (par reduct frame)) target

theorem Exposure.sound {Γ : Ctx sig} {source target : Proc Γ}
    (occurrence : Exposure source target) : StepModulo source target :=
  ⟨_, _, occurrence.before,
    occurrence.scope.step (.parL occurrence.frame occurrence.selected.sound), occurrence.after⟩

def Exposure.changeSource {Γ : Ctx sig} {source source' target : Proc Γ}
    (equal : StructuralEq source' source) (occurrence : Exposure source target) :
    Exposure source' target :=
  { occurrence with before := .trans equal occurrence.before }

def Exposure.changeTarget {Γ : Ctx sig} {source target target' : Proc Γ}
    (occurrence : Exposure source target) (equal : StructuralEq target target') :
    Exposure source target' :=
  { occurrence with after := .trans occurrence.after equal }

/-- Extruding the entire private telescope retains the old and new frames
in their common world, without modifying either consumed component. -/
def Exposure.parLeft {Γ : Ctx sig} {source target : Proc Γ}
    (occurrence : Exposure source target) (frame : Proc Γ) :
    Exposure (par source frame) (par target frame) where
  world := occurrence.world
  scope := occurrence.scope
  redex := occurrence.redex
  reduct := occurrence.reduct
  selected := occurrence.selected
  frame := par occurrence.frame (rename occurrence.scope.inclusion frame)
  before := .trans (.par occurrence.before (.refl frame))
    (.trans (occurrence.scope.par_left _ frame)
      (occurrence.scope.congr (.parAssoc _ _ _)))
  after := .trans (occurrence.scope.congr (.symm (.parAssoc _ _ _)))
    (.trans (.symm (occurrence.scope.par_left _ frame))
      (.par occurrence.after (.refl frame)))

def Exposure.parRight {Γ : Ctx sig} {source target : Proc Γ}
    (frame : Proc Γ) (occurrence : Exposure source target) :
    Exposure (par frame source) (par frame target) :=
  ((occurrence.parLeft frame).changeSource (.parComm _ _)).changeTarget (.parComm _ _)

def Exposure.restrict {Γ : Ctx sig} {source target : Proc (.nm :: Γ)}
    (occurrence : Exposure source target) : Exposure (nu source) (nu target) where
  world := occurrence.world
  scope := .bind occurrence.scope
  redex := occurrence.redex
  reduct := occurrence.reduct
  selected := occurrence.selected
  frame := occurrence.frame
  before := .nu occurrence.before
  after := .nu occurrence.after

/-- The common world and untouched frame are calculated from all actual
communication and active-context constructors. -/
theorem directed_step_exposes {Γ : Ctx sig} {source target : Proc Γ}
    (step : Step source target) : Nonempty (Exposure source target) := by
  induction step with
  | comm1 channel datum body =>
      exact ⟨⟨_, .nil, _, _, .unary channel datum body, nil,
        .symm (.parUnit _), .parUnit _⟩⟩
  | comm2 channel first second body =>
      exact ⟨⟨_, .nil, _, _, .binary channel first second body, nil,
        .symm (.parUnit _), .parUnit _⟩⟩
  | parL frame _ ih =>
      obtain ⟨occurrence⟩ := ih
      exact ⟨occurrence.parLeft frame⟩
  | parR frame _ ih =>
      obtain ⟨occurrence⟩ := ih
      exact ⟨occurrence.parRight frame⟩
  | nu _ ih =>
      obtain ⟨occurrence⟩ := ih
      exact ⟨occurrence.restrict⟩

/-- Arbitrary static changes at either endpoint retain the actual selected
communication and its common scoped world. -/
theorem modulo_step_exposes {Γ : Ctx sig} {source target : Proc Γ}
    (step : StepModulo source target) : Nonempty (Exposure source target) := by
  obtain ⟨redex, reduct, before, firing, after⟩ := step
  obtain ⟨occurrence⟩ := directed_step_exposes firing
  exact ⟨(occurrence.changeSource before).changeTarget after⟩

theorem stepModulo_iff_exposure {Γ : Ctx sig} (source target : Proc Γ) :
    StepModulo source target ↔ Nonempty (Exposure source target) :=
  ⟨modulo_step_exposes, fun ⟨occurrence⟩ => occurrence.sound⟩

/-- The existing classified authored relation admits this concrete selected
communication readout, at its actual program sections and supplied endpoints. -/
theorem classified_step_iff_exposure {Γ : Ctx sig} (source target : Proc Γ) :
    IntrinsicScopedAuthoredClassifiedReduction.ExtendedReduction rules equations source target ↔
      Nonempty (Exposure source target) :=
  (extension_iff_stepModulo source target).trans (stepModulo_iff_exposure source target)

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedCommunicationInversion
