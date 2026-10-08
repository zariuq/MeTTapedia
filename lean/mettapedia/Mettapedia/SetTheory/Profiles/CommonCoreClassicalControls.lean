import Mettapedia.SetTheory.Profiles.CommonCoreClassicalCollection

/-!
# Shared deductions and separating model controls

The actual pairing deduction is interpreted in both infinite carriers.
Regularity and Quine existence are independent of the shared calculus in
both directions, as witnessed by the two constructed models. These are
external metatheorems about the concrete proof type, not an internal
arithmetized consistency assertion of either object theory.

Preservation of membership by the well-founded inclusion does not make it
an elementary embedding for unbounded formulas. The Quine sentence is a
concrete counterexample to such unrestricted formula transfer.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Profiles.CommonCoreClassicalControls

open Mettapedia.TypeTheory.MaterialSets.Hypersets
open ContextualMaterialLogic (Formula)
open Mettapedia.SetTheory.CarveOuts.Sites (Tarski)
open CommonCoreClassical CommonCoreClassicalCollection

universe u

theorem actual_pairing_deduction_in_both_models :
    Tarski (fun (child parent : HSet.{u}) => child ∈ parent)
      CommonCore.containmentTheorem Fin.elim0 ∧
    Tarski (fun (child parent : ZFSet.{u}) => child ∈ parent)
      CommonCore.containmentTheorem Fin.elim0 :=
  ⟨hyperset_interpret CommonCore.containmentDerivation Fin.elim0,
    wellFounded_interpret CommonCore.containmentDerivation Fin.elim0⟩

theorem core_has_no_refutation :
    ¬ Nonempty (CommonCore.Derivation (Formula.bottom (n := 0))) := by
  rintro ⟨proof⟩
  exact hyperset_interpret.{0} proof Fin.elim0

theorem collection_extension_has_no_refutation :
    ¬ Nonempty (CommonCore.ExtensionDerivation (Formula.bottom (n := 0))) := by
  rintro ⟨proof⟩
  exact hyperset_extension.{0} proof Fin.elim0

theorem negated_foundation_not_derivable :
    ¬ Nonempty (CommonCore.Derivation (.imply CommonCore.foundationAxiom .bottom)) := by
  rintro ⟨proof⟩
  exact wellFounded_interpret.{0} proof Fin.elim0 (wellFounded_foundation Fin.elim0)

theorem negated_quine_not_derivable :
    ¬ Nonempty (CommonCore.Derivation (.imply quineSentence .bottom)) := by
  rintro ⟨proof⟩
  exact hyperset_interpret.{0} proof Fin.elim0 (hyperset_quine Fin.elim0)

theorem foundation_extension_not_derivable :
    ¬ Nonempty (CommonCore.ExtensionDerivation CommonCore.foundationAxiom) := by
  rintro ⟨proof⟩
  exact hyperset_not_foundation.{0} Fin.elim0 (hyperset_extension proof Fin.elim0)

theorem quine_extension_not_derivable :
    ¬ Nonempty (CommonCore.ExtensionDerivation quineSentence) := by
  rintro ⟨proof⟩
  exact wellFounded_no_quine.{0} Fin.elim0 (wellFounded_extension proof Fin.elim0)

theorem negated_foundation_extension_not_derivable :
    ¬ Nonempty (CommonCore.ExtensionDerivation (.imply CommonCore.foundationAxiom .bottom)) := by
  rintro ⟨proof⟩
  exact wellFounded_extension.{0} proof Fin.elim0 (wellFounded_foundation Fin.elim0)

theorem negated_quine_extension_not_derivable :
    ¬ Nonempty (CommonCore.ExtensionDerivation (.imply quineSentence .bottom)) := by
  rintro ⟨proof⟩
  exact hyperset_extension.{0} proof Fin.elim0 (hyperset_quine Fin.elim0)

theorem inclusion_preserves_membership (child parent : ZFSet.{u}) :
    HSet.ofZFSet child ∈ HSet.ofZFSet parent ↔ child ∈ parent :=
  HSet.ofZFSet_mem_ofZFSet_iff

theorem inclusion_is_not_elementary :
    ¬ (∀ (count : Nat) (body : Formula count) (environment : Fin count → ZFSet.{u}),
      Tarski (fun child parent => child ∈ parent) body environment ↔
      Tarski (fun (child parent : HSet.{u}) => child ∈ parent) body
        (fun index => HSet.ofZFSet (environment index))) := by
  intro elementary
  exact wellFounded_no_quine.{u} Fin.elim0
    ((elementary 0 quineSentence Fin.elim0).mpr (hyperset_quine _))

end Mettapedia.SetTheory.Profiles.CommonCoreClassicalControls
