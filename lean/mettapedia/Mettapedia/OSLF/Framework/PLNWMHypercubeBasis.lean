import Mettapedia.OSLF.Framework.LanguageMorphism

/-!
# PLN/WM Hypercube Basis (GSLT-Oriented Prototype)

This module provides:

1. A generic hypercube basis (`AxisBundle`, one-axis steps, paths).
2. A generic language family over hypercube vertices with edge morphisms.
3. Path-level transport theorems for multi-step reductions.
4. A concrete PLN/WM axis prototype for OSLF/GSLT integration.
-/

namespace Mettapedia.OSLF.Framework.PLNWMHypercubeBasis

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.LangMorphism

universe u

/-! ## Generic Basis -/

structure AxisBundle where
  ι : Type u
  AxisVal : ι → Type u
  step : ∀ i, AxisVal i → AxisVal i → Prop

abbrev Vertex (A : AxisBundle) : Type u := ∀ i : A.ι, A.AxisVal i

structure AxisStep (A : AxisBundle) (v w : Vertex A) where
  axis : A.ι
  step_ok : A.step axis (v axis) (w axis)
  unchanged : ∀ j : A.ι, j ≠ axis → v j = w j

inductive CubePath (A : AxisBundle) : Vertex A → Vertex A → Type where
  | refl (v : Vertex A) : CubePath A v v
  | cons {v w u : Vertex A} :
      AxisStep A v w → CubePath A w u → CubePath A v u

namespace CubePath

variable {A : AxisBundle}

def trans {v w u : Vertex A} : CubePath A v w → CubePath A w u → CubePath A v u
  | .refl _, p₂ => p₂
  | .cons h t, p₂ => .cons h (trans t p₂)

end CubePath

structure LanguageFiber (A : AxisBundle) where
  lang : Vertex A → LanguageDef
  morph : ∀ {v w : Vertex A}, AxisStep A v w →
    LanguageMorphism (lang v) (lang w) Eq

variable {A : AxisBundle}

def mapAlongPath (F : LanguageFiber A) :
    {v w : Vertex A} → CubePath A v w → Pattern → Pattern
  | _, _, .refl _ => fun p => p
  | _, _, .cons h t => fun p => mapAlongPath F t ((F.morph h).mapTerm p)

theorem transport_single_forward
    (F : LanguageFiber A) {v w : Vertex A}
    (h : AxisStep A v w) {p q : Pattern}
    (hred : LangReducesStar (F.lang v) p q) :
    ∃ q', LangReducesStar (F.lang w) ((F.morph h).mapTerm p) q' ∧
      q' = (F.morph h).mapTerm q :=
  LanguageMorphism.forward_multi_eq (m := F.morph h) hred

theorem transport_single_backward
    (F : LanguageFiber A) {v w : Vertex A}
    (h : AxisStep A v w) {p : Pattern} {t : Pattern}
    (hred : LangReducesStar (F.lang w) ((F.morph h).mapTerm p) t) :
    ∃ p', LangReducesStar (F.lang v) p p' ∧ t = (F.morph h).mapTerm p' :=
  LanguageMorphism.backward_multi_eq (m := F.morph h) hred

theorem transport_path_forward
    (F : LanguageFiber A) {v w : Vertex A} (π : CubePath A v w) :
    ∀ {p q : Pattern}, LangReducesStar (F.lang v) p q →
      ∃ q', LangReducesStar (F.lang w) (mapAlongPath F π p) q' ∧
        q' = mapAlongPath F π q := by
  induction π with
  | refl v =>
      intro p q hred
      exact ⟨q, hred, rfl⟩
  | cons h t ih =>
      intro p q hred
      rcases transport_single_forward (F := F) h hred with ⟨q₁, hq₁, hq₁eq⟩
      subst hq₁eq
      simpa [mapAlongPath] using ih hq₁

theorem transport_path_backward
    (F : LanguageFiber A) {v w : Vertex A} (π : CubePath A v w) :
    ∀ {p : Pattern} {t : Pattern},
      LangReducesStar (F.lang w) (mapAlongPath F π p) t →
      ∃ p', LangReducesStar (F.lang v) p p' ∧ t = mapAlongPath F π p' := by
  induction π with
  | refl v =>
      intro p t hred
      exact ⟨t, hred, rfl⟩
  | cons h t ih =>
      intro p tFinal hred
      rcases ih hred with ⟨q, hq, hEq⟩
      rcases transport_single_backward (F := F) h hq with ⟨p', hp', hMap⟩
      refine ⟨p', hp', ?_⟩
      subst hMap
      simpa [mapAlongPath] using hEq

/-! ## PLN/WM Axis Prototype -/

inductive WMLogic where
  | boolean
  | heyting
  deriving DecidableEq, Repr, Fintype

inductive WMTruthValue where
  | point
  | bounds
  deriving DecidableEq, Repr, Fintype

inductive WMIntervalSemantics where
  | bayesNormal
  | bayesExact
  | walleyIDM
  deriving DecidableEq, Repr, Fintype

inductive WMQueryTyping where
  | untyped
  | typedSigma
  deriving DecidableEq, Repr, Fintype

inductive WMAxis where
  | logic
  | truthValue
  | interval
  | typing
  deriving DecidableEq, Repr, Fintype

def wmAxisTy : WMAxis → Type
  | .logic => WMLogic
  | .truthValue => WMTruthValue
  | .interval => WMIntervalSemantics
  | .typing => WMQueryTyping

def wmAxisStep : ∀ a, wmAxisTy a → wmAxisTy a → Prop
  | .logic, .boolean, .heyting => True
  | .truthValue, .point, .bounds => True
  | .interval, .bayesNormal, .bayesExact => True
  | .typing, .untyped, .typedSigma => True
  | _, x, y => x = y

def wmAxes : AxisBundle where
  ι := WMAxis
  AxisVal := wmAxisTy
  step := wmAxisStep

abbrev WMVertex := Vertex wmAxes

def mkWMVertex
    (logic : WMLogic)
    (tv : WMTruthValue)
    (interval : WMIntervalSemantics)
    (typing : WMQueryTyping) : WMVertex
  | .logic => logic
  | .truthValue => tv
  | .interval => interval
  | .typing => typing

def setLogic (v : WMVertex) (x : WMLogic) : WMVertex :=
  mkWMVertex x (v .truthValue) (v .interval) (v .typing)

def setTruthValue (v : WMVertex) (x : WMTruthValue) : WMVertex :=
  mkWMVertex (v .logic) x (v .interval) (v .typing)

def setInterval (v : WMVertex) (x : WMIntervalSemantics) : WMVertex :=
  mkWMVertex (v .logic) (v .truthValue) x (v .typing)

def setTyping (v : WMVertex) (x : WMQueryTyping) : WMVertex :=
  mkWMVertex (v .logic) (v .truthValue) (v .interval) x

def logicStep (v : WMVertex) (x : WMLogic)
    (h : wmAxisStep .logic (v .logic) x) :
    AxisStep wmAxes v (setLogic v x) where
  axis := .logic
  step_ok := h
  unchanged := by
    intro j hj
    cases j with
    | logic => exact (False.elim (hj rfl))
    | truthValue => rfl
    | interval => rfl
    | typing => rfl

def truthValueStep (v : WMVertex) (x : WMTruthValue)
    (h : wmAxisStep .truthValue (v .truthValue) x) :
    AxisStep wmAxes v (setTruthValue v x) where
  axis := .truthValue
  step_ok := h
  unchanged := by
    intro j hj
    cases j with
    | logic => rfl
    | truthValue => exact (False.elim (hj rfl))
    | interval => rfl
    | typing => rfl

def intervalStep (v : WMVertex) (x : WMIntervalSemantics)
    (h : wmAxisStep .interval (v .interval) x) :
    AxisStep wmAxes v (setInterval v x) where
  axis := .interval
  step_ok := h
  unchanged := by
    intro j hj
    cases j with
    | logic => rfl
    | truthValue => rfl
    | interval => exact (False.elim (hj rfl))
    | typing => rfl

def typingStep (v : WMVertex) (x : WMQueryTyping)
    (h : wmAxisStep .typing (v .typing) x) :
    AxisStep wmAxes v (setTyping v x) where
  axis := .typing
  step_ok := h
  unchanged := by
    intro j hj
    cases j with
    | logic => rfl
    | truthValue => rfl
    | interval => rfl
    | typing => exact (False.elim (hj rfl))

def wmVertexClassicalFast : WMVertex :=
  mkWMVertex .boolean .point .bayesNormal .untyped

def wmVertexGeneralExact : WMVertex :=
  setTyping
    (setInterval
      (setTruthValue (setLogic wmVertexClassicalFast .heyting) .bounds)
      .bayesExact)
    .typedSigma

def wmVertexGeneralWalley : WMVertex :=
  mkWMVertex .heyting .bounds .walleyIDM .typedSigma

def canonicalPathToGeneralExact :
    CubePath wmAxes wmVertexClassicalFast wmVertexGeneralExact :=
  CubePath.cons
    (logicStep wmVertexClassicalFast .heyting (by trivial))
    (CubePath.cons
      (truthValueStep (setLogic wmVertexClassicalFast .heyting) .bounds (by trivial))
      (CubePath.cons
        (intervalStep
          (setTruthValue (setLogic wmVertexClassicalFast .heyting) .bounds)
          .bayesExact (by trivial))
        (CubePath.cons
          (typingStep
            (setInterval
              (setTruthValue (setLogic wmVertexClassicalFast .heyting) .bounds)
              .bayesExact)
            .typedSigma (by trivial))
          (CubePath.refl _))))

abbrev WMLanguageFiber := LanguageFiber wmAxes

theorem transport_canonical_forward
    (F : WMLanguageFiber) {p q : Pattern}
    (hred : LangReducesStar (F.lang wmVertexClassicalFast) p q) :
    ∃ q', LangReducesStar (F.lang wmVertexGeneralExact)
      (mapAlongPath (A := wmAxes) F canonicalPathToGeneralExact p) q' ∧
      q' = mapAlongPath (A := wmAxes) F canonicalPathToGeneralExact q :=
  transport_path_forward (A := wmAxes) (F := F) (π := canonicalPathToGeneralExact) hred

/-! ## Executable Demo Fiber -/

/-- Identity language morphism (`Eq`-up-to) for a fixed language. -/
def idLanguageMorphism (lang : LanguageDef) : LanguageMorphism lang lang Eq where
  mapTerm := id
  forward_sim := by
    intro p q h
    exact ⟨q, LangReducesStar.single h, rfl⟩
  backward_sim := by
    intro p t h
    exact ⟨t, LangReducesStar.single h, rfl⟩

/-- Constant language family over all PLN/WM vertices (demo scaffold). -/
def constantFiber (lang : LanguageDef) : WMLanguageFiber where
  lang := fun _ => lang
  morph := fun _ => idLanguageMorphism lang

@[simp] theorem mapAlongPath_constant
    (lang : LanguageDef) {v w : WMVertex}
    (π : CubePath wmAxes v w) (p : Pattern) :
    mapAlongPath (A := wmAxes) (constantFiber lang) π p = p := by
  induction π with
  | refl _ =>
      rfl
  | cons _ t ih =>
      simpa [mapAlongPath, constantFiber, idLanguageMorphism] using ih

/-- The canonical path transport is immediately runnable on a constant fiber. -/
theorem transport_canonical_forward_constant
    (lang : LanguageDef) {p q : Pattern}
    (hred : LangReducesStar lang p q) :
    ∃ q', LangReducesStar lang p q' ∧ q' = q := by
  have h :=
    transport_canonical_forward (F := constantFiber lang) (p := p) (q := q) hred
  rcases h with ⟨q', hq', hqeq⟩
  refine ⟨q', ?_, ?_⟩
  · rw [mapAlongPath_constant lang canonicalPathToGeneralExact p] at hq'
    simpa [constantFiber] using hq'
  · simpa [mapAlongPath_constant] using hqeq

end Mettapedia.OSLF.Framework.PLNWMHypercubeBasis
