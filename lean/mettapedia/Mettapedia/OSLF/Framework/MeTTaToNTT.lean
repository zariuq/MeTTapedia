import Mettapedia.OSLF.Framework.MeTTaFullInstance
import Mettapedia.OSLF.MeTTaIL.Engine
import Mettapedia.Logic.OSLFEvidenceSemantics
import Mettapedia.Logic.PLNWorldModel
import Mettapedia.CategoryTheory.NativeTypeTheory
import Mettapedia.CategoryTheory.PLNInstance

/-!
# MeTTaFull OSLF -> NTT Bridge

This module provides the direct evidence-to-NTT bridge for the MeTTaFull OSLF
instance, parallel to the GF `OSLFToNTT` composition layer.
-/

namespace Mettapedia.OSLF.Framework.MeTTaToNTT

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.MeTTaFullInstance
open Mettapedia.OSLF.Formula
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.OSLFEvidenceSemantics
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.CategoryTheory.PLNInstance
open Mettapedia.CategoryTheory.NativeTypeTheory

abbrev mettaFull : LanguageDef := Mettapedia.OSLF.Framework.MeTTaFullInstance.mettaFull

/-! ## 1. Evidence -> NativeTypeTheory -/

/-- Build a native type from a PLN object and evidence value. -/
def mettaEvidenceToNT (X : PLNObj) (e : Evidence) : NativeTypeBundle :=
  Sigma.mk X e

@[simp] theorem mettaEvidenceToNT_fst (X : PLNObj) (e : Evidence) :
    (mettaEvidenceToNT X e).1 = X := rfl

@[simp] theorem mettaEvidenceToNT_snd (X : PLNObj) (e : Evidence) :
    (mettaEvidenceToNT X e).2 = e := rfl

/-- Evidence order induces an NTT morphism. -/
def mettaEvidenceToNT_hom (X : PLNObj) (e₁ e₂ : Evidence) (h : e₁ ≤ e₂) :
    Hom (mettaEvidenceToNT X e₁) (mettaEvidenceToNT X e₂) :=
  PLift.up h

/-! ## 2. MeTTa OSLF evidence semantics -/

section WMBridge

variable {State : Type*}
variable [Mettapedia.Logic.EvidenceClass.EvidenceType State]
variable [Mettapedia.Logic.PLNWorldModel.WorldModel State Pattern]

/-- Evidence semantics for MeTTaFull formulas from a world-model state. -/
noncomputable def mettaSemE
    (relEnv : RelationEnv)
    (W : State)
    (queryOfAtom : String → Pattern → Pattern)
    (φ : OSLFFormula) (p : Pattern) : Evidence :=
  semE (langReducesUsing relEnv mettaFull) (wmEvidenceAtomSem W queryOfAtom) φ p

@[simp] theorem mettaSemE_atom
    (relEnv : RelationEnv)
    (W : State)
    (queryOfAtom : String → Pattern → Pattern)
    (a : String) (p : Pattern) :
    mettaSemE relEnv W queryOfAtom (.atom a) p =
      WorldModel.evidence W (queryOfAtom a p) := by
  simp [mettaSemE, wmEvidenceAtomSem]

/-- Revision of world states commutes with atom evidence in MeTTa semantics. -/
theorem mettaSemE_atom_revision
    (relEnv : RelationEnv)
    (W₁ W₂ : State)
    (queryOfAtom : String → Pattern → Pattern)
    (a : String) (p : Pattern) :
    mettaSemE relEnv (W₁ + W₂) queryOfAtom (.atom a) p =
      mettaSemE relEnv W₁ queryOfAtom (.atom a) p +
      mettaSemE relEnv W₂ queryOfAtom (.atom a) p := by
  simpa [mettaSemE] using
    semE_wm_atom_revision
      (W₁ := W₁) (W₂ := W₂) (queryOfAtom := queryOfAtom)
      (R := langReducesUsing relEnv mettaFull) (a := a) (p := p)

/-! ## 3. Formula -> NativeTypeTheory -/

/-- Lift MeTTa formula evidence evaluation into NativeTypeTheory. -/
noncomputable def mettaFormulaToNT
    (relEnv : RelationEnv)
    (W : State)
    (queryOfAtom : String → Pattern → Pattern)
    (φ : OSLFFormula) (p : Pattern) (X : PLNObj) : NativeTypeTheory :=
  mettaEvidenceToNT X (mettaSemE relEnv W queryOfAtom φ p)

@[simp] theorem mettaFormulaToNT_snd
    (relEnv : RelationEnv)
    (W : State)
    (queryOfAtom : String → Pattern → Pattern)
    (φ : OSLFFormula) (p : Pattern) (X : PLNObj) :
    (mettaFormulaToNT relEnv W queryOfAtom φ p X).2 =
      mettaSemE relEnv W queryOfAtom φ p := rfl

@[simp] theorem mettaFormulaToNT_atom
    (relEnv : RelationEnv)
    (W : State)
    (queryOfAtom : String → Pattern → Pattern)
    (a : String) (p : Pattern) (X : PLNObj) :
    mettaFormulaToNT relEnv W queryOfAtom (.atom a) p X =
      mettaEvidenceToNT X (WorldModel.evidence W (queryOfAtom a p)) := by
  simp [mettaFormulaToNT]

/-- Evidence monotonicity between formulas yields an NTT morphism. -/
noncomputable def mettaFormulaToNT_hom
    (relEnv : RelationEnv)
    (W : State)
    (queryOfAtom : String → Pattern → Pattern)
    (p : Pattern) (X : PLNObj) (φ ψ : OSLFFormula)
    (hle : mettaSemE relEnv W queryOfAtom φ p ≤ mettaSemE relEnv W queryOfAtom ψ p) :
    Hom (mettaFormulaToNT relEnv W queryOfAtom φ p X)
        (mettaFormulaToNT relEnv W queryOfAtom ψ p X) :=
  PLift.up hle

end WMBridge

end Mettapedia.OSLF.Framework.MeTTaToNTT
