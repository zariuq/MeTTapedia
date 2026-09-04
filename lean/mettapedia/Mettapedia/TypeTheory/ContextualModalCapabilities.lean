import Mettapedia.TypeTheory.ModalCwF
import Mathlib.Logic.Equiv.Basic

/-!
# Independent formation capabilities of a modal CwF

The historical `ModalCwF` record stores four different kinds of data:

* a mode-indexed contextual core;
* dependent-product formation;
* a Tarski universe and its decoding operation; and
* modal context locking and modal type formation.

This module decomposes that record exactly.  The equivalence below is a
lossless reassociation of existing data, not a proposed type theory.  It makes
the individual formation capabilities available for separate comparison and
replacement before their laws, computation rules, or intended interpretation
are selected.

The Boolean canary supplies the negative control.  Two decompositions have
literally the same contextual core, product formation, and modal locking, but
choose different universe codes.  Hence the common contextual structure does
not determine a universe, just as beta computation does not determine
function extensionality.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualModalCapabilities

open Mettapedia.TypeTheory

/-- Contexts, substitutions, indexed types and terms, and comprehension over
a mode theory.  No dependent product, universe, modal lock, or quotation is
included. -/
structure ModeIndexedContextualCore (modes : ModeTheory) where
  Con : modes.Mode → Type 1
  Sub : {mode : modes.Mode} → Con mode → Con mode → Type
  sid : {mode : modes.Mode} → (context : Con mode) → Sub context context
  scomp : {mode : modes.Mode} → {first middle last : Con mode} →
    Sub first middle → Sub middle last → Sub first last
  Ty : {mode : modes.Mode} → Con mode → Type 1
  Tm : {mode : modes.Mode} → (context : Con mode) → Ty context → Type
  tySub : {mode : modes.Mode} → {first last : Con mode} →
    Ty last → Sub first last → Ty first
  tmSub : {mode : modes.Mode} → {first last : Con mode} →
    {type : Ty last} → Tm last type →
    (substitution : Sub first last) → Tm first (tySub type substitution)
  tySub_id : ∀ {mode : modes.Mode} {context : Con mode}
    (type : Ty context), tySub type (sid context) = type
  tySub_comp : ∀ {mode : modes.Mode} {first middle last : Con mode}
    (type : Ty last) (earlier : Sub first middle) (later : Sub middle last),
    tySub type (scomp earlier later) = tySub (tySub type later) earlier
  empty : (mode : modes.Mode) → Con mode
  ext : {mode : modes.Mode} → (context : Con mode) → Ty context → Con mode
  wk : {mode : modes.Mode} → {context : Con mode} →
    (type : Ty context) → Sub (ext context type) context
  vz : {mode : modes.Mode} → {context : Con mode} →
    (type : Ty context) → Tm (ext context type) (tySub type (wk type))
  sext : {mode : modes.Mode} → {first last : Con mode} →
    {type : Ty last} → (substitution : Sub first last) →
    Tm first (tySub type substitution) → Sub first (ext last type)

/-- Formation of dependent products over a selected contextual core.  Its
introduction, elimination, beta, eta, and extensionality principles are
separate structures. -/
structure DependentProductFormation (modes : ModeTheory)
    (core : ModeIndexedContextualCore modes) where
  pi : {mode : modes.Mode} → {context : core.Con mode} →
    (domain : core.Ty context) → core.Ty (core.ext context domain) →
      core.Ty context

/-- A Tarski universe formation and decoding operation.  Cumulativity,
closure, substitution stability, and reflection are additional properties. -/
structure TarskiUniverseFormation (modes : ModeTheory)
    (core : ModeIndexedContextualCore modes) where
  univ : {mode : modes.Mode} → (context : core.Con mode) → core.Ty context
  el : {mode : modes.Mode} → {context : core.Con mode} →
    core.Tm context (univ context) → core.Ty context

/-- Fitch-style context locking and modal type formation.  It does not assert
term quotation, modal elimination, or any coherence law. -/
structure ModalLockingFormation (modes : ModeTheory)
    (core : ModeIndexedContextualCore modes) where
  lock : {high low : modes.Mode} →
    modes.Hom high low → core.Con low → core.Con high
  boxTy : {high low : modes.Mode} → (modality : modes.Hom high low) →
    {context : core.Con low} → core.Ty (lock modality context) →
      core.Ty context

/-- The exact capability decomposition of the historical `ModalCwF` data.
The name describes that existing bundle and does not select a calculus. -/
structure ModalCwFDecomposition (modes : ModeTheory) where
  contextual : ModeIndexedContextualCore modes
  products : DependentProductFormation modes contextual
  tarski : TarskiUniverseFormation modes contextual
  locking : ModalLockingFormation modes contextual

namespace BundledModalCwF

/-- Forget product, universe, and modality formation from a `ModalCwF`. -/
def toContextualCore {modes : ModeTheory} (cwf : ModalCwF modes) :
    ModeIndexedContextualCore modes where
  Con := cwf.Con
  Sub := cwf.Sub
  sid := cwf.sid
  scomp := cwf.scomp
  Ty := cwf.Ty
  Tm := cwf.Tm
  tySub := cwf.tySub
  tmSub := cwf.tmSub
  tySub_id := cwf.tySub_id
  tySub_comp := cwf.tySub_comp
  empty := cwf.empty
  ext := cwf.ext
  wk := cwf.wk
  vz := cwf.vz
  sext := cwf.sext

/-- Extract dependent-product formation from the bundle. -/
def toDependentProductFormation {modes : ModeTheory} (cwf : ModalCwF modes) :
    DependentProductFormation modes (toContextualCore cwf) where
  pi := cwf.pi

/-- Extract the selected Tarski universe formation from the bundle. -/
def toTarskiUniverseFormation {modes : ModeTheory} (cwf : ModalCwF modes) :
    TarskiUniverseFormation modes (toContextualCore cwf) where
  univ := cwf.univ
  el := cwf.el

/-- Extract modal context locking and modal type formation from the bundle. -/
def toModalLockingFormation {modes : ModeTheory} (cwf : ModalCwF modes) :
    ModalLockingFormation modes (toContextualCore cwf) where
  lock := cwf.lock
  boxTy := cwf.boxTy

/-- Decompose all data in a `ModalCwF` without discarding anything. -/
def decompose {modes : ModeTheory} (cwf : ModalCwF modes) :
    ModalCwFDecomposition modes where
  contextual := toContextualCore cwf
  products := toDependentProductFormation cwf
  tarski := toTarskiUniverseFormation cwf
  locking := toModalLockingFormation cwf

end BundledModalCwF

namespace ModalCwFDecomposition

/-- Reassemble the historical bundle from its four independent formation
components. -/
def assemble {modes : ModeTheory} (decomposition : ModalCwFDecomposition modes) :
    ModalCwF modes where
  Con := decomposition.contextual.Con
  Sub := decomposition.contextual.Sub
  sid := decomposition.contextual.sid
  scomp := decomposition.contextual.scomp
  Ty := decomposition.contextual.Ty
  Tm := decomposition.contextual.Tm
  tySub := decomposition.contextual.tySub
  tmSub := decomposition.contextual.tmSub
  tySub_id := decomposition.contextual.tySub_id
  tySub_comp := decomposition.contextual.tySub_comp
  empty := decomposition.contextual.empty
  ext := decomposition.contextual.ext
  wk := decomposition.contextual.wk
  vz := decomposition.contextual.vz
  sext := decomposition.contextual.sext
  pi := decomposition.products.pi
  univ := decomposition.tarski.univ
  el := decomposition.tarski.el
  lock := decomposition.locking.lock
  boxTy := decomposition.locking.boxTy

/-- Product formation can be replaced without changing the contextual,
universe, or modal-locking components. -/
def replaceProducts {modes : ModeTheory}
    (decomposition : ModalCwFDecomposition modes)
    (products : DependentProductFormation modes decomposition.contextual) :
    ModalCwFDecomposition modes where
  contextual := decomposition.contextual
  products := products
  tarski := decomposition.tarski
  locking := decomposition.locking

/-- Universe formation can be replaced independently of the other three
components. -/
def replaceUniverse {modes : ModeTheory}
    (decomposition : ModalCwFDecomposition modes)
    (tarski : TarskiUniverseFormation modes decomposition.contextual) :
    ModalCwFDecomposition modes where
  contextual := decomposition.contextual
  products := decomposition.products
  tarski := tarski
  locking := decomposition.locking

/-- Modal locking can be replaced independently of the contextual, product,
and universe components. -/
def replaceLocking {modes : ModeTheory}
    (decomposition : ModalCwFDecomposition modes)
    (locking : ModalLockingFormation modes decomposition.contextual) :
    ModalCwFDecomposition modes where
  contextual := decomposition.contextual
  products := decomposition.products
  tarski := decomposition.tarski
  locking := locking

end ModalCwFDecomposition

/-- The historical bundle and the capability decomposition contain exactly
the same data. -/
def modalCwFDecompositionEquiv (modes : ModeTheory) :
    ModalCwF modes ≃ ModalCwFDecomposition modes where
  toFun := BundledModalCwF.decompose
  invFun := ModalCwFDecomposition.assemble
  left_inv := by
    intro cwf
    cases cwf
    rfl
  right_inv := by
    intro decomposition
    cases decomposition with
    | mk contextual products tarski locking =>
        cases contextual
        cases products
        cases tarski
        cases locking
        rfl

/-! ## Negative control: a contextual core does not select a universe -/

namespace UniverseChoiceCanary

/-- The terminal one-mode theory. -/
def oneMode : ModeTheory where
  Mode := Unit
  Hom := fun _ _ => Unit
  id := fun _ => ()
  comp := fun _ _ => ()
  id_comp := fun _ => rfl
  comp_id := fun _ => rfl
  comp_assoc := fun _ _ _ => rfl

/-- A tiny contextual core with two type codes and one term at every type. -/
def booleanCore : ModeIndexedContextualCore oneMode where
  Con := fun _ => ULift Unit
  Sub := fun _ _ => Unit
  sid := fun _ => ()
  scomp := fun _ _ => ()
  Ty := fun _ => ULift Bool
  Tm := fun _ _ => Unit
  tySub := fun type _ => type
  tmSub := fun _ _ => ()
  tySub_id := fun _ => rfl
  tySub_comp := fun _ _ _ => rfl
  empty := fun _ => ⟨()⟩
  ext := fun context _ => context
  wk := fun _ => ()
  vz := fun _ => ()
  sext := fun _ _ => ()

def products : DependentProductFormation oneMode booleanCore where
  pi := fun domain _ => domain

def locking : ModalLockingFormation oneMode booleanCore where
  lock := fun _ context => context
  boxTy := by
    intro high low modality context type
    exact type

def falseUniverse : TarskiUniverseFormation oneMode booleanCore where
  univ := fun _ => ⟨false⟩
  el := fun _ => ⟨false⟩

def trueUniverse : TarskiUniverseFormation oneMode booleanCore where
  univ := fun _ => ⟨true⟩
  el := fun _ => ⟨true⟩

def withFalseUniverse : ModalCwFDecomposition oneMode where
  contextual := booleanCore
  products := products
  tarski := falseUniverse
  locking := locking

def withTrueUniverse : ModalCwFDecomposition oneMode :=
  withFalseUniverse.replaceUniverse trueUniverse

theorem contextual_components_equal :
    withFalseUniverse.contextual = withTrueUniverse.contextual :=
  rfl

theorem product_components_equal :
    HEq withFalseUniverse.products withTrueUniverse.products :=
  HEq.rfl

theorem locking_components_equal :
    HEq withFalseUniverse.locking withTrueUniverse.locking :=
  HEq.rfl

/-- One fixed contextual core admits two distinct universe formations. -/
theorem universe_formations_distinct : falseUniverse ≠ trueUniverse := by
  intro equalUniverses
  have equalUniverseCodes := congrArg
    (fun tarski : TarskiUniverseFormation oneMode booleanCore =>
      (tarski.univ (mode := ()) ⟨()⟩).down)
    equalUniverses
  exact Bool.false_ne_true equalUniverseCodes

end UniverseChoiceCanary

#print axioms modalCwFDecompositionEquiv
#print axioms UniverseChoiceCanary.contextual_components_equal
#print axioms UniverseChoiceCanary.universe_formations_distinct

end Mettapedia.TypeTheory.ContextualModalCapabilities
