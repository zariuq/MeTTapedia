import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementModelCommutation
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementRenaming
import Mettapedia.TypeTheory.ContextualTypePresentationCast

/-!
# Model maps for actual scoped renamings

A model renaming retains its actual substitution and the readout of every
variable occurrence. Identity, composition, weakening and binder lifting
are derived from the CwF laws and telescope variables.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement

open _root_.CategoryTheory
open NativeLocalTypeFormers
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualSumComprehension
open Mettapedia.TypeTheory.ContextualTypeOperations

universe u v

variable {S : Symbols.{v}} {C : Type u} [Category.{u} C] {n k l : Nat}

local instance nativeTypeCategory (P : (NativeModel C).toCwf.Ctx) :
    Category (TypeOver (NativeModel C).toCwf P) :=
  TypeOver.instCategory

/- The finite variable readout is a local condition on one actual arrow. -/
structure ModelRenaming (Γ : Scope C k) (Δ : Scope C n) (mapping : Renaming n k) where
  arrow : Γ.1 ⟶ Δ.1
  readout : ∀ index, Γ.2.lookup (mapping index) = (Δ.2.lookup index).substitute arrow

namespace ModelRenaming

attribute [local irreducible] TypeOver.extensionSubstitution TypeOver.isoOfValEq

set_option backward.isDefEq.respectTransparency false in
def identity (Γ : Scope C n) : ModelRenaming Γ Γ id where
  arrow := (NativeModel C).toCwf.idS Γ.1
  readout _index := (Value.substitute_identity _).symm

set_option backward.isDefEq.respectTransparency false in
def compose {Γ : Scope C l} {Δ : Scope C k} {Θ : Scope C n}
    {first : Renaming n k} {second : Renaming k l}
    (earlier : ModelRenaming Δ Θ first) (later : ModelRenaming Γ Δ second) :
    ModelRenaming Γ Θ (second ∘ first) where
  arrow := (NativeModel C).toCwf.compS earlier.arrow later.arrow
  readout index := by
    rw [Function.comp_apply, later.readout, earlier.readout]
    exact (Value.substitute_composition _ _ _).symm

set_option backward.isDefEq.respectTransparency false in
def weaken (Γ : Scope C n) (A : (NativeModel C).toCwf.Ty Γ.1) : ModelRenaming (Γ.snoc A) Γ Fin.succ where
  arrow := (NativeModel C).toCwf.wk A
  readout _ := rfl

def restrict (Γ : Scope C n) (φ : Subfunctor Γ.1) :
    ModelRenaming (Γ.assume φ) Γ id where
  arrow := φ.ι
  readout _ := rfl

set_option backward.isDefEq.respectTransparency false in
def lift {Γ : Scope C k} {Δ : Scope C n} {mapping : Renaming n k}
    (modelMap : ModelRenaming Γ Δ mapping) (A : (NativeModel C).toCwf.Ty Δ.1) :
    ModelRenaming (Γ.snoc ((NativeModel C).toCwf.tySub A modelMap.arrow)) (Δ.snoc A) (liftRenaming mapping) where
  arrow := TypeOver.extensionSubstitution (C := (NativeModel C).toCwf) modelMap.arrow A
  readout index := by
    cases index using Fin.cases with
    | zero =>
        simp only [liftRenaming_zero, ScopeData.lookup_zero, Value.substitute]
        apply Sigma.ext
        · change (NativeModel C).toCwf.tySub ((NativeModel C).toCwf.tySub A modelMap.arrow)
            ((NativeModel C).toCwf.wk ((NativeModel C).toCwf.tySub A modelMap.arrow)) =
              (NativeModel C).toCwf.tySub ((NativeModel C).toCwf.tySub A ((NativeModel C).toCwf.wk A))
                (TypeOver.extensionSubstitution modelMap.arrow A)
          symm
          rw [← (NativeModel C).toCwf.tySub_comp, TypeOver.wk_extensionSubstitution, (NativeModel C).toCwf.tySub_comp]
        · exact (TypeOver.vz_extensionSubstitution (C := (NativeModel C).toCwf)
            modelMap.arrow A).symm
    | succ index =>
        simp only [liftRenaming_succ, ScopeData.lookup_succ, modelMap.readout,
          ← Value.substitute_composition]
        rw [TypeOver.wk_extensionSubstitution]

/- A chosen equality of display annotations changes the lifted target
context by actual transport, rather than selecting new variable meanings. -/
set_option backward.isDefEq.respectTransparency false in
def liftAlong {Γ : Scope C k} {Δ : Scope C n} {mapping : Renaming n k}
    (modelMap : ModelRenaming Γ Δ mapping) (A : (NativeModel C).toCwf.Ty Δ.1)
    (A' : (NativeModel C).toCwf.Ty Γ.1) (equal : (NativeModel C).toCwf.tySub A modelMap.arrow = A') :
    ModelRenaming (Γ.snoc A') (Δ.snoc A) (liftRenaming mapping) :=
  equal ▸ modelMap.lift A

set_option backward.isDefEq.respectTransparency false in
theorem liftAlong_arrow {Γ : Scope C k} {Δ : Scope C n} {mapping : Renaming n k}
    (modelMap : ModelRenaming Γ Δ mapping) (A : (NativeModel C).toCwf.Ty Δ.1)
    (A' : (NativeModel C).toCwf.Ty Γ.1) (equal : (NativeModel C).toCwf.tySub A modelMap.arrow = A') :
    (modelMap.liftAlong A A' equal).arrow =
      (NativeModel C).toCwf.compS (TypeOver.extensionSubstitution modelMap.arrow A)
        (ContextualTypePresentationCast.extensionCast (K := (NativeModel C).toCwf) equal.symm) := by
  cases equal
  change TypeOver.extensionSubstitution (C := (NativeModel C).toCwf) modelMap.arrow A = _
  rw [ContextualTypePresentationCast.extensionCast_refl]
  exact ((NativeModel C).toCwf.comp_id _).symm

set_option backward.isDefEq.respectTransparency false in
theorem arrow_unique {Γ : Scope C k} {Δ : Scope C n} {mapping : Renaming n k}
    (first second : ModelRenaming Γ Δ mapping) : first.arrow = second.arrow := by
  apply Δ.2.components_injective
  funext index
  exact (first.readout index).symm.trans (second.readout index)

end ModelRenaming

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
