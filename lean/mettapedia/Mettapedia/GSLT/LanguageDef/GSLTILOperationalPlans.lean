import Mettapedia.GSLT.LanguageDef.GSLTILFreePath
import Mettapedia.TypeTheory.IndexedPolynomialFree

/-!
# Typed operational plans for authored GSLT-IL events

The method signature has two shapes: finish at equal endpoints, or retain one
actual authored event and ask for the remaining suffix. Its free terms are the
existing indexed polynomial terms with holes. Closed terms are equivalent to
the existing `ProgramPath`; no second path carrier or operational relation is
introduced. Filling a hole retains the prefix and reconstructs the same path.
-/

namespace Mettapedia.GSLT.LanguageDef.GSLTIL.OperationalPlans

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.GSLT.LanguageDef.GSLTIL.Syntax
open Mettapedia.GSLT.LanguageDef.GSLTIL.FreePath
open Mettapedia.OSLF.MeTTaIL.Syntax

set_option autoImplicit false

/-- The target is fixed while the source advances through authored events. -/
def methods (program : Program) : IndexedPolynomial.{0, 0, 0, 0} Pattern (fun _ => Pattern) where
  Shape target source := PLift (source = target) ⊕ Σ middle, ProgramEvent program source middle
  Position shape := match shape with
    | .inl _ => PEmpty.{1}
    | .inr _ => PUnit.{1}
  next shape position := match shape with
    | .inl _ => position.elim
    | .inr step => step.1

abbrev Plan (program : Program) (holes : Pattern → Pattern → Type) :=
  (methods program).Free holes

abbrev ClosedPlan (program : Program) := Plan program (fun _ _ => PEmpty)

def hole {program : Program} {holes : Pattern → Pattern → Type}
    {target source : Pattern} (value : holes target source) : Plan program holes target source :=
  IndexedPolynomial.Free.pure (methods program) value

def done {program : Program} {holes : Pattern → Pattern → Type} (state : Pattern) :
    Plan program holes state state :=
  IndexedPolynomial.Free.node (methods program) (.inl ⟨rfl⟩) (fun p => p.elim)

def step {program : Program} {holes : Pattern → Pattern → Type}
    {source middle target : Pattern} (event : ProgramEvent program source middle)
    (suffix : Plan program holes target middle) : Plan program holes target source :=
  IndexedPolynomial.Free.node (methods program) (.inr ⟨middle, event⟩) (fun _ => suffix)

/-- The actual path constructors interpret the method signature. -/
def pathAlgebra (program : Program) :
    (methods program).Algebra (fun target source => ProgramPath program source target) where
  act _ source input := match input with
    | ⟨.inl ⟨same⟩, _⟩ => same ▸ Route.refl source
    | ⟨.inr ⟨_, event⟩, children⟩ => .cons event (children PUnit.unit)

noncomputable def reconstruct {program : Program} {holes : Pattern → Pattern → Type}
    (interpret : ∀ target source, holes target source → ProgramPath program source target) :
    ∀ target source, Plan program holes target source → ProgramPath program source target :=
  IndexedPolynomial.Free.fold (methods program) interpret (pathAlgebra program)

@[simp] theorem reconstruct_hole {program : Program} {holes : Pattern → Pattern → Type}
    (interpret : ∀ target source, holes target source → ProgramPath program source target)
    {target source : Pattern} (value : holes target source) :
    reconstruct interpret target source (hole value) = interpret target source value := rfl

@[simp] theorem reconstruct_done {program : Program} {holes : Pattern → Pattern → Type}
    (interpret : ∀ target source, holes target source → ProgramPath program source target)
    (state : Pattern) : reconstruct interpret state state (done state) = .refl state := rfl

@[simp] theorem reconstruct_step {program : Program} {holes : Pattern → Pattern → Type}
    (interpret : ∀ target source, holes target source → ProgramPath program source target)
    {source middle target : Pattern} (event : ProgramEvent program source middle)
    (suffix : Plan program holes target middle) :
    reconstruct interpret target source (step event suffix) =
      .cons event (reconstruct interpret target middle suffix) := rfl

noncomputable def decode {program : Program} {source target : Pattern}
    (plan : ClosedPlan program target source) : ProgramPath program source target :=
  reconstruct (fun _ _ p => p.elim) target source plan

def encode {program : Program} : {source target : Pattern} →
    ProgramPath program source target → ClosedPlan program target source
  | _, _, .refl state => done state
  | _, _, .cons event suffix => step event (encode suffix)

@[simp] theorem decode_encode {program : Program} {source target : Pattern}
    (path : ProgramPath program source target) : decode (encode path) = path := by
  induction path with
  | refl => rfl
  | cons event suffix ih =>
      change Route.cons event (decode (encode suffix)) = _
      rw [ih]

@[simp] theorem encode_decode {program : Program} {source target : Pattern}
    (plan : ClosedPlan program target source) : encode (decode plan) = plan := by
  refine IndexedPolynomial.Fix.rec (motive := fun _ plan => encode (decode plan) = plan) ?_ plan
  intro source shape children ih
  cases shape with
    | inl impossible => exact impossible.elim
    | inr method =>
      cases method with
      | inl same =>
        rcases same with ⟨same⟩
        subst same
        change IndexedPolynomial.Free.node (methods program) (.inl ⟨rfl⟩) (fun p => p.elim) =
          IndexedPolynomial.Free.node (methods program) (.inl ⟨rfl⟩) children
        apply congrArg (IndexedPolynomial.Free.node (methods program) (.inl ⟨rfl⟩))
        funext p
        exact p.elim
      | inr method =>
        rcases method with ⟨middle, event⟩
        dsimp only [IndexedPolynomial.withHoles, methods] at children ih
        change IndexedPolynomial.Free.node (methods program) (.inr ⟨middle, event⟩)
            (fun _ => encode (decode (children PUnit.unit))) =
          IndexedPolynomial.Free.node (methods program) (.inr ⟨middle, event⟩) children
        apply congrArg (IndexedPolynomial.Free.node (methods program) (.inr ⟨middle, event⟩))
        funext p
        cases p
        exact ih PUnit.unit

/-- Closed method plans retain exactly the authored proof-relevant paths. -/
noncomputable def closedEquiv (program : Program) (source target : Pattern) :
    ClosedPlan program target source ≃ ProgramPath program source target where
  toFun := decode
  invFun := encode
  left_inv := encode_decode
  right_inv := decode_encode

/-- Filling holes uses the shared indexed free construction. -/
noncomputable def fill {program : Program} {holes nextHoles : Pattern → Pattern → Type}
    (replacement : ∀ target source, holes target source → Plan program nextHoles target source) :
    ∀ target source, Plan program holes target source → Plan program nextHoles target source :=
  IndexedPolynomial.Free.bind (methods program) replacement

/-- Reconstruction after filling is reconstruction of the same retained tree
with its holes interpreted by the supplied suffix plans. -/
theorem reconstruct_fill {program : Program} {holes nextHoles : Pattern → Pattern → Type}
    (replacement : ∀ target source, holes target source → Plan program nextHoles target source)
    (interpret : ∀ target source, nextHoles target source → ProgramPath program source target)
    {target source : Pattern} (plan : Plan program holes target source) :
    reconstruct interpret target source (fill replacement target source plan) =
      reconstruct (fun target source h => reconstruct interpret target source
        (replacement target source h)) target source plan :=
  IndexedPolynomial.Free.fold_bind (methods program) replacement interpret (pathAlgebra program) plan

/-- Any observation of the retained path sees that same substitution law. -/
theorem observe_reconstruct_fill {program : Program} {holes nextHoles : Pattern → Pattern → Type}
    (replacement : ∀ target source, holes target source → Plan program nextHoles target source)
    (interpret : ∀ target source, nextHoles target source → ProgramPath program source target)
    {target source : Pattern} {Observation : Type}
    (observe : ProgramPath program source target → Observation)
    (plan : Plan program holes target source) :
    observe (reconstruct interpret target source (fill replacement target source plan)) =
      observe (reconstruct (fun target source h => reconstruct interpret target source
        (replacement target source h)) target source plan) :=
  congrArg observe (reconstruct_fill replacement interpret plan)

/-- Closing holes with typed suffix paths reconstructs those same paths. -/
theorem decode_fill_encode {program : Program} {holes : Pattern → Pattern → Type}
    (solve : ∀ target source, holes target source → ProgramPath program source target)
    {target source : Pattern} (plan : Plan program holes target source) :
    decode (fill (fun target source h => encode (solve target source h)) target source plan) =
      reconstruct solve target source plan := by
  change reconstruct (fun _ _ p => p.elim) target source
    (fill (fun target source h => encode (solve target source h)) target source plan) = _
  rw [reconstruct_fill]
  have same : (fun target source h =>
      reconstruct (fun _ _ p => PEmpty.elim p) target source
        (encode (solve target source h))) = solve := by
    funext target source h
    exact decode_encode (solve target source h)
  rw [same]

/-- A partial interpretation cannot turn an unresolved suffix into a path. This
option records only reconstruction availability, not a logical refutation. -/
def partialPathAlgebra (program : Program) :
    (methods program).Algebra (fun target source => Option (ProgramPath program source target)) where
  act _ source input := match input with
    | ⟨.inl ⟨same⟩, _⟩ => some (same ▸ Route.refl source)
    | ⟨.inr ⟨_, event⟩, children⟩ => (children PUnit.unit).map (Route.cons event)

noncomputable def reconstruct? {program : Program} {holes : Pattern → Pattern → Type}
    (interpret : ∀ target source, holes target source → Option (ProgramPath program source target)) :
    ∀ target source, Plan program holes target source → Option (ProgramPath program source target) :=
  IndexedPolynomial.Free.fold (methods program) interpret (partialPathAlgebra program)

@[simp] theorem reconstruct?_hole {program : Program} {holes : Pattern → Pattern → Type}
    (interpret : ∀ target source, holes target source → Option (ProgramPath program source target))
    {target source : Pattern} (value : holes target source) :
    reconstruct? interpret target source (hole value) = interpret target source value := rfl

@[simp] theorem reconstruct?_done {program : Program} {holes : Pattern → Pattern → Type}
    (interpret : ∀ target source, holes target source → Option (ProgramPath program source target))
    (state : Pattern) : reconstruct? interpret state state (done state) = some (.refl state) := rfl

@[simp] theorem reconstruct?_step {program : Program} {holes : Pattern → Pattern → Type}
    (interpret : ∀ target source, holes target source → Option (ProgramPath program source target))
    {source middle target : Pattern} (event : ProgramEvent program source middle)
    (suffix : Plan program holes target middle) :
    reconstruct? interpret target source (step event suffix) =
      (reconstruct? interpret target middle suffix).map (Route.cons event) := rfl

/-- Occurrences are read from the actual reconstructed path. -/
def occurrences {program : Program} : {source target : Pattern} →
    ProgramPath program source target → List Pattern
  | _, _, .refl _ => []
  | _, _, .cons event suffix => event.occurrence :: occurrences suffix

/-- Actual edge receipts are summed over the same path. -/
def cost {program : Program}
    (charge : ∀ {source target}, ProgramEvent program source target → Nat) :
    {source target : Pattern} → ProgramPath program source target → Nat
  | _, _, .refl _ => 0
  | _, _, .cons event suffix => charge event + cost charge suffix

end Mettapedia.GSLT.LanguageDef.GSLTIL.OperationalPlans
