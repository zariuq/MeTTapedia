import Mettapedia.OSLF.MeTTaCore.FullLanguageDef
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Framework.ConstructorCategory
import Mettapedia.OSLF.Framework.BeckChevalleyOSLF
import Mettapedia.OSLF.Formula

/-!
# MeTTa Full LanguageDef Client (OSLF)

End-to-end OSLF bridge for the first spec-facing `MeTTaCore.FullLanguageDef`
language slice.
-/

namespace Mettapedia.OSLF.Framework.MeTTaFullInstance

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.Formula

abbrev mettaFull : LanguageDef := Mettapedia.OSLF.MeTTaCore.FullLanguageDef.mettaFull
abbrev mettaFullOSLF := Mettapedia.OSLF.MeTTaCore.FullLanguageDef.mettaFullOSLF

/-- Automatic modal Galois connection for the first full MeTTa slice. -/
theorem mettaFullGalois :
    GaloisConnection (langDiamond mettaFull) (langBox mettaFull) :=
  langGalois mettaFull

/-- The `State` process sort in the constructor-category view of `mettaFull`. -/
def mettaState : LangSort mettaFull := ⟨"State", by decide⟩

/-- Concrete unary sort-crossings extracted from `mettaFull`. -/
private theorem mettaFull_unaryCrossings :
    unaryCrossings mettaFull = [("Eval", "Atom", "Instr"), ("Return", "Atom", "Instr")] := by
  native_decide

/-- No unary sort-crossing arrow can target `State` in `mettaFull`. -/
private theorem mettaFull_noArrowToState
    {d : LangSort mettaFull}
    (arr : SortArrow mettaFull d mettaState) : False := by
  have hmem : (arr.label, d.val, "State") ∈ unaryCrossings mettaFull := by
    simpa [mettaState] using arr.valid
  rw [mettaFull_unaryCrossings] at hmem
  simp at hmem

/-- Concrete path-order law for the `mettaFull` `State` sort. -/
theorem mettaFull_pathOrder
    (seed : Pattern) :
    ∀ {a b : LangSort mettaFull}
      (g : SortPath mettaFull a b) (h : SortPath mettaFull b mettaState),
        pathSem mettaFull g (pathSem mettaFull h seed) =
          pathSem mettaFull (g.comp h) seed := by
  intro a b g h
  cases h with
  | nil =>
      simp [pathSem, SortPath.comp]
  | cons h' arr =>
      exfalso
      exact mettaFull_noArrowToState arr

/-! ## End-to-End Bridge (Checker → Fiber → PathSemClosed BC+Graph) -/

/-- End-to-end MeTTaFull bridge parallel to TinyML/MeTTaMinimal. -/
theorem mettaFull_checker_sat_to_pathSemClosed_commDi_bc_graph
    {relEnv : RelationEnv}
    {I_check : AtomCheck} {I_sem : AtomSem}
    (h_atoms : ∀ a p, I_check a p = true → I_sem a p)
    {fuel : Nat} {p : Pattern} {φf : OSLFFormula}
    (hSat : checkLangUsing relEnv mettaFull I_check fuel p φf = .sat)
    (seed q : Pattern)
    (hPkg :
      Mettapedia.OSLF.Framework.CategoryBridge.CommDiPathSemLiftPkg
        mettaFull mettaState seed q)
    (hNat :
      Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality
        mettaFull mettaState seed
        (sem (langReducesUsing relEnv mettaFull) I_sem φf))
    {P B D : CategoryTheory.Functor (Opposite (ConstructorObj mettaFull)) (Type _)}
    (pi1 : P ⟶
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj
        mettaFull mettaState))
    (pi2 : P ⟶ B)
    (f :
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj
        mettaFull mettaState) ⟶ D)
    (g : B ⟶ D)
    (hpb : CategoryTheory.IsPullback pi1 pi2 f g)
    (hf : CategoryTheory.Mono f) (hpi2 : CategoryTheory.Mono pi2)
    {X : Opposite (ConstructorObj mettaFull)}
    (hArrow :
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj
        mettaFull mettaState).obj X)
    (hp : pathSem mettaFull hArrow seed = p) :
    let ψ := sem (langReducesUsing relEnv mettaFull) I_sem φf
    (langOSLF mettaFull "State").satisfies (S := "State")
      (pathSem mettaFull hArrow seed) ψ
    ∧ Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred mettaFull ψ
        (pathSem mettaFull hArrow seed)
    ∧
      ((CategoryTheory.Subobject.map pi2).obj
          ((CategoryTheory.Subobject.pullback pi1).obj
            (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred_subobject
              mettaFull mettaState seed
              (Mettapedia.OSLF.Framework.BeckChevalleyOSLF.commDi q
                (Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred mettaFull ψ))
              (Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality_commDi_pathSemClosed_of_pkg
                mettaFull mettaState seed q ψ hPkg)))
        =
      (CategoryTheory.Subobject.pullback g).obj
          ((CategoryTheory.Subobject.map f).obj
            (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred_subobject
              mettaFull mettaState seed
              (Mettapedia.OSLF.Framework.BeckChevalleyOSLF.commDi q
                (Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred mettaFull ψ))
              (Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality_commDi_pathSemClosed_of_pkg
                mettaFull mettaState seed q ψ hPkg))))
    ∧
      (langDiamondUsing relEnv mettaFull
        (Mettapedia.OSLF.Framework.BeckChevalleyOSLF.commDi q
          (Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred mettaFull ψ)) p ↔
        ∃ e : (Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
          (C := ConstructorObj mettaFull) relEnv mettaFull).Edge.obj X,
          ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
            (C := ConstructorObj mettaFull) relEnv mettaFull).source.app X e).down = p ∧
          ∃ u : Pattern,
            Mettapedia.OSLF.MeTTaIL.Substitution.commSubst u q =
              ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
                (C := ConstructorObj mettaFull) relEnv mettaFull).target.app X e).down ∧
            Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred mettaFull ψ u) := by
  let ψ : Pattern → Prop := sem (langReducesUsing relEnv mettaFull) I_sem φf
  have hSatFiber :
      (langOSLF mettaFull "State").satisfies (S := "State")
        (pathSem mettaFull hArrow seed) ψ :=
    checkLangUsing_sat_sound_sort_fiber_mem_iff
      (relEnv := relEnv) (lang := mettaFull) (procSort := "State")
      (I_check := I_check) (I_sem := I_sem)
      h_atoms hSat mettaState seed hNat hArrow hp
  have hClosedBase :
      Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred mettaFull ψ
        (pathSem mettaFull hArrow seed) :=
    Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred.base hSatFiber
  have hBCGraph :
      ((CategoryTheory.Subobject.map pi2).obj
          ((CategoryTheory.Subobject.pullback pi1).obj
            (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred_subobject
              mettaFull mettaState seed
              (Mettapedia.OSLF.Framework.BeckChevalleyOSLF.commDi q
                (Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred mettaFull ψ))
              (Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality_commDi_pathSemClosed_of_pkg
                mettaFull mettaState seed q ψ hPkg)))
        =
      (CategoryTheory.Subobject.pullback g).obj
          ((CategoryTheory.Subobject.map f).obj
            (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred_subobject
              mettaFull mettaState seed
              (Mettapedia.OSLF.Framework.BeckChevalleyOSLF.commDi q
                (Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred mettaFull ψ))
              (Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality_commDi_pathSemClosed_of_pkg
                mettaFull mettaState seed q ψ hPkg))))
      ∧
      (langDiamondUsing relEnv mettaFull
        (Mettapedia.OSLF.Framework.BeckChevalleyOSLF.commDi q
          (Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred mettaFull ψ)) p ↔
        ∃ e : (Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
          (C := ConstructorObj mettaFull) relEnv mettaFull).Edge.obj X,
          ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
            (C := ConstructorObj mettaFull) relEnv mettaFull).source.app X e).down = p ∧
          ∃ u : Pattern,
            Mettapedia.OSLF.MeTTaIL.Substitution.commSubst u q =
              ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
                (C := ConstructorObj mettaFull) relEnv mettaFull).target.app X e).down ∧
            Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred mettaFull ψ u) :=
    Mettapedia.OSLF.Framework.BeckChevalleyOSLF.representable_commDi_bc_and_graphDiamond_of_pathSemLiftPkg
      (lang := mettaFull) (s := mettaState) (seed := seed) (q := q) (φ := ψ)
      (hPkg := hPkg)
      (pi1 := pi1) (pi2 := pi2) (f := f) (g := g)
      (hpb := hpb) (hf := hf) (hpi2 := hpi2)
      (relEnv := relEnv) (X := X) (p := p)
  exact ⟨hSatFiber, hClosedBase, hBCGraph.1, hBCGraph.2⟩

/-- Public no-package wrapper using the concrete `mettaFull_pathOrder` law. -/
theorem mettaFull_checker_sat_to_pathSemClosed_commDi_bc_graph_auto
    {relEnv : RelationEnv}
    {I_check : AtomCheck} {I_sem : AtomSem}
    (h_atoms : ∀ a p, I_check a p = true → I_sem a p)
    {fuel : Nat} {p : Pattern} {φf : OSLFFormula}
    (hSat : checkLangUsing relEnv mettaFull I_check fuel p φf = .sat)
    (seed q : Pattern)
    (hNat :
      Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality
        mettaFull mettaState seed
        (sem (langReducesUsing relEnv mettaFull) I_sem φf))
    {P B D : CategoryTheory.Functor (Opposite (ConstructorObj mettaFull)) (Type _)}
    (pi1 : P ⟶
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj
        mettaFull mettaState))
    (pi2 : P ⟶ B)
    (f :
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj
        mettaFull mettaState) ⟶ D)
    (g : B ⟶ D)
    (hpb : CategoryTheory.IsPullback pi1 pi2 f g)
    (hf : CategoryTheory.Mono f) (hpi2 : CategoryTheory.Mono pi2)
    {X : Opposite (ConstructorObj mettaFull)}
    (hArrow :
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj
        mettaFull mettaState).obj X)
    (hp : pathSem mettaFull hArrow seed = p) :
    let ψ := sem (langReducesUsing relEnv mettaFull) I_sem φf
    (langOSLF mettaFull "State").satisfies (S := "State")
      (pathSem mettaFull hArrow seed) ψ
    ∧ Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred mettaFull ψ
        (pathSem mettaFull hArrow seed)
    ∧
      ((CategoryTheory.Subobject.map pi2).obj
          ((CategoryTheory.Subobject.pullback pi1).obj
            (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred_subobject
              mettaFull mettaState seed
              (Mettapedia.OSLF.Framework.BeckChevalleyOSLF.commDi q
                (Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred mettaFull ψ))
              (Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality_commDi_pathSemClosed_of_pkg
                mettaFull mettaState seed q ψ
                (Mettapedia.OSLF.Framework.CategoryBridge.commDiPathSemLiftPkg_of_pathSem_comm_subst_and_path_order
                  mettaFull mettaState seed q (mettaFull_pathOrder seed)))))
        =
      (CategoryTheory.Subobject.pullback g).obj
          ((CategoryTheory.Subobject.map f).obj
            (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred_subobject
              mettaFull mettaState seed
              (Mettapedia.OSLF.Framework.BeckChevalleyOSLF.commDi q
                (Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred mettaFull ψ))
              (Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality_commDi_pathSemClosed_of_pkg
                mettaFull mettaState seed q ψ
                (Mettapedia.OSLF.Framework.CategoryBridge.commDiPathSemLiftPkg_of_pathSem_comm_subst_and_path_order
                  mettaFull mettaState seed q (mettaFull_pathOrder seed))))))
    ∧
      (langDiamondUsing relEnv mettaFull
        (Mettapedia.OSLF.Framework.BeckChevalleyOSLF.commDi q
          (Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred mettaFull ψ)) p ↔
        ∃ e : (Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
          (C := ConstructorObj mettaFull) relEnv mettaFull).Edge.obj X,
          ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
            (C := ConstructorObj mettaFull) relEnv mettaFull).source.app X e).down = p ∧
          ∃ u : Pattern,
            Mettapedia.OSLF.MeTTaIL.Substitution.commSubst u q =
              ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
                (C := ConstructorObj mettaFull) relEnv mettaFull).target.app X e).down ∧
            Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred mettaFull ψ u) := by
  let hPkg :
      Mettapedia.OSLF.Framework.CategoryBridge.CommDiPathSemLiftPkg
        mettaFull mettaState seed q :=
    Mettapedia.OSLF.Framework.CategoryBridge.commDiPathSemLiftPkg_of_pathSem_comm_subst_and_path_order
      mettaFull mettaState seed q (mettaFull_pathOrder seed)
  exact mettaFull_checker_sat_to_pathSemClosed_commDi_bc_graph
    (relEnv := relEnv) (I_check := I_check) (I_sem := I_sem)
    h_atoms hSat seed q hPkg hNat
    (pi1 := pi1) (pi2 := pi2) (f := f) (g := g)
    (hpb := hpb) (hf := hf) (hpi2 := hpi2)
    (X := X) (hArrow := hArrow) (hp := hp)

/-- Spec-facing atom checker for MeTTaFull machine states. -/
def mettaFullSpecAtomCheck : AtomCheck
  | "isEvalState", .apply "State" [.apply "Eval" [_], _, _] => true
  | "isUnifyState", .apply "State" [.apply "Unify" [_, _], _, _] => true
  | "isChainState", .apply "State" [.apply "Chain" [_, _], _, _] => true
  | "isTypeCheckState", .apply "State" [.apply "TypeCheck" [_, _], _, _] => true
  | "isCastState", .apply "State" [.apply "Cast" [_, _], _, _] => true
  | "isGrounded1State", .apply "State" [.apply "Grounded1" [_, _], _, _] => true
  | "isGrounded2State", .apply "State" [.apply "Grounded2" [_, _, _], _, _] => true
  | "isReturnState", .apply "State" [.apply "Return" [_], _, _] => true
  | "isDoneState", .apply "State" [.apply "Done" [], _, _] => true
  | _, _ => false

/-- Semantics for MeTTaFull spec-facing atoms (classifier aligned). -/
def mettaFullSpecAtomSem : AtomSem :=
  fun a p => mettaFullSpecAtomCheck a p = true

/-- Soundness of the MeTTaFull spec atom checker by construction. -/
theorem mettaFullSpecAtomCheck_sound :
    ∀ a p, mettaFullSpecAtomCheck a p = true → mettaFullSpecAtomSem a p := by
  intro a p h
  simpa [mettaFullSpecAtomSem] using h

/-- Public API theorem for MeTTaFull spec-facing checker soundness. -/
theorem mettaFull_checkLangUsing_sat_sound_specAtoms
    {relEnv : RelationEnv}
    {fuel : Nat} {p : Pattern} {φ : OSLFFormula}
    (hSat : checkLangUsing relEnv mettaFull mettaFullSpecAtomCheck fuel p φ = .sat) :
    sem (langReducesUsing relEnv mettaFull) mettaFullSpecAtomSem φ p := by
  exact checkLangUsing_sat_sound
    (relEnv := relEnv) (lang := mettaFull)
    (I_check := mettaFullSpecAtomCheck) (I_sem := mettaFullSpecAtomSem)
    mettaFullSpecAtomCheck_sound hSat

/-- Default-environment specialization for MeTTaFull spec-facing checker soundness. -/
theorem mettaFull_checkLang_sat_sound_specAtoms
    {fuel : Nat} {p : Pattern} {φ : OSLFFormula}
    (hSat : checkLang mettaFull mettaFullSpecAtomCheck fuel p φ = .sat) :
    sem (langReduces mettaFull) mettaFullSpecAtomSem φ p := by
  simpa [checkLang, langReduces] using
    (mettaFull_checkLangUsing_sat_sound_specAtoms
      (relEnv := RelationEnv.empty) (fuel := fuel) (p := p) (φ := φ) hSat)

#check mettaFullOSLF
#check mettaFullGalois
#check mettaState
#check mettaFull_pathOrder
#check mettaFull_checker_sat_to_pathSemClosed_commDi_bc_graph
#check mettaFull_checker_sat_to_pathSemClosed_commDi_bc_graph_auto
#check mettaFullSpecAtomCheck
#check mettaFullSpecAtomSem
#check mettaFull_checkLangUsing_sat_sound_specAtoms

end Mettapedia.OSLF.Framework.MeTTaFullInstance
