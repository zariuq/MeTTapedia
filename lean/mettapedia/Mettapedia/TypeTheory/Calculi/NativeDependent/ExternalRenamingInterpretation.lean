import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalModelCommutation
import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalRenaming

/-!
# Model maps for actual scoped renamings

A model renaming retains its actual substitution and the readout of every
variable occurrence. Identity, composition, weakening and binder lifting
are derived from the CwF laws and telescope variables.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualSumComprehension
open Mettapedia.TypeTheory.ContextualTypeOperations

universe u c s t m

variable {S : Symbols.{u}} {C : CwfWithTerminal.{c, s, t, m}} {n k l : Nat}

/-- The finite variable readout is a local condition on one actual arrow. -/
structure ModelRenaming (Γ : Context C k) (Δ : Context C n) (mapping : Renaming n k) where
  arrow : C.toCwf.Sub Γ.1 Δ.1
  readout : ∀ index, Γ.2.lookup (mapping index) = (Δ.2.lookup index).substitute arrow

namespace ModelRenaming

def identity (Γ : Context C n) : ModelRenaming Γ Γ id where
  arrow := C.toCwf.idS Γ.1
  readout _index := (Value.substitute_identity _).symm

def compose {Γ : Context C l} {Δ : Context C k} {Θ : Context C n}
    {first : Renaming n k} {second : Renaming k l}
    (earlier : ModelRenaming Δ Θ first) (later : ModelRenaming Γ Δ second) :
    ModelRenaming Γ Θ (second ∘ first) where
  arrow := C.toCwf.compS earlier.arrow later.arrow
  readout index := by
    rw [Function.comp_apply, later.readout, earlier.readout]
    exact (Value.substitute_composition _ _ _).symm

def weaken (Γ : Context C n) (A : C.toCwf.Ty Γ.1) : ModelRenaming (Γ.snoc A) Γ Fin.succ where
  arrow := C.toCwf.wk A
  readout _ := rfl

def lift {Γ : Context C k} {Δ : Context C n} {mapping : Renaming n k}
    (modelMap : ModelRenaming Γ Δ mapping) (A : C.toCwf.Ty Δ.1) :
    ModelRenaming (Γ.snoc (C.toCwf.tySub A modelMap.arrow)) (Δ.snoc A) (liftRenaming mapping) where
  arrow := TypeOver.extensionSubstitution modelMap.arrow A
  readout index := by
    cases index using Fin.cases with
    | zero =>
        simp only [liftRenaming_zero, Telescope.variable_zero, Value.substitute]
        apply Sigma.ext
        · change C.toCwf.tySub (C.toCwf.tySub A modelMap.arrow)
            (C.toCwf.wk (C.toCwf.tySub A modelMap.arrow)) =
              C.toCwf.tySub (C.toCwf.tySub A (C.toCwf.wk A))
                (TypeOver.extensionSubstitution modelMap.arrow A)
          symm
          rw [← C.toCwf.tySub_comp, TypeOver.wk_extensionSubstitution, C.toCwf.tySub_comp]
        · exact (TypeOver.vz_extensionSubstitution modelMap.arrow A).symm
    | succ index =>
        simp only [liftRenaming_succ, Telescope.variable_succ, modelMap.readout,
          ← Value.substitute_composition]
        rw [TypeOver.wk_extensionSubstitution]

/-- A chosen equality of display annotations changes the lifted target
context by actual transport, rather than selecting new variable meanings. -/
def liftAlong {Γ : Context C k} {Δ : Context C n} {mapping : Renaming n k}
    (modelMap : ModelRenaming Γ Δ mapping) (A : C.toCwf.Ty Δ.1)
    (A' : C.toCwf.Ty Γ.1) (equal : C.toCwf.tySub A modelMap.arrow = A') :
    ModelRenaming (Γ.snoc A') (Δ.snoc A) (liftRenaming mapping) :=
  equal ▸ modelMap.lift A

theorem liftAlong_arrow {Γ : Context C k} {Δ : Context C n} {mapping : Renaming n k}
    (modelMap : ModelRenaming Γ Δ mapping) (A : C.toCwf.Ty Δ.1)
    (A' : C.toCwf.Ty Γ.1) (equal : C.toCwf.tySub A modelMap.arrow = A') :
    (modelMap.liftAlong A A' equal).arrow =
      C.toCwf.compS (TypeOver.extensionSubstitution modelMap.arrow A)
        (TypeOver.isoOfValEq (C := C.toCwf)
          (A := ⟨A'⟩) (B := ⟨C.toCwf.tySub A modelMap.arrow⟩) equal.symm).hom.substitution := by
  cases equal
  exact (C.toCwf.comp_id _).symm

theorem arrow_unique {Γ : Context C k} {Δ : Context C n} {mapping : Renaming n k}
    (first second : ModelRenaming Γ Δ mapping) : first.arrow = second.arrow := by
  apply Δ.2.components_injective
  funext index
  exact (first.readout index).symm.trans (second.readout index)

end ModelRenaming

end Mettapedia.TypeTheory.Calculi.NativeDependent.External
