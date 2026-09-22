import Foundation.Propositional.Tait.Calculus
import Mettapedia.GSLT.Logic.PropositionalCut
import Mettapedia.GSLT.Logic.PropositionalFormula
import Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-!
# GSLT propositional cut vs Foundation Tait cut

Foundation lives only in this Logic/Bridges module, never in GSLT/OSLF.

Two different cuts on related objects:

* Foundation Tait `Derivation.cut` *builds* a derivation: from `φ :: Δ` and
  `∼φ :: Δ` one obtains `Δ`. Length is `succ (max …)`. Cut is a constructor.
* GSLT `CutStep` *eliminates* a cut node on an untyped proof tree. Proof size
  strictly falls. Cut is a redex.

The same GSLT sits in the kernel: `propositionalGSLT` is an object of the
GSLT category. Its induced OSLF diamond is “a `CutStep` exists”. That is
not Tait cut, and it is not `SoundCut` (a named interaction site).

Erasing sequents sends a Tait derivation to a GSLT proof (when the formula
language matches). Cut-free Tait (no `cut` constructor) maps to `CutFree`
GSLT proofs. The algebraic Hauptsatz (Avigad) is existence of a cut-free
derivation; it is not this rewrite system.

GSLT `andElim` is natural-deduction elimination and has no Tait image.
Tait `or`/`wk`/`verum` are sequent structure: `or` now retracts as a
formula, but still does not become a GSLT proof constructor.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Bridges.PropositionalCutTait

open Mettapedia.GSLT.Logic.PropositionalCut
open Mettapedia.GSLT.Logic.PropositionalFormula
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open LO.Propositional

/-! ## Formulas -/

/-- GSLT formulas embed as Foundation negation-normal formulas. `not` becomes
De Morgan negation. Double-negation is collapsed on the Foundation side. -/
def formulaEmbed : Formula → NNFormula Nat
  | .atom n => .atom n
  | .not A => ∼ formulaEmbed A
  | .and A B => formulaEmbed A ⋏ formulaEmbed B
  | .or A B => formulaEmbed A ⋎ formulaEmbed B

/-- Retract the GSLT fragment. Verum and falsum have no GSLT constructor. -/
def formulaRetract : NNFormula Nat → Option Formula
  | .atom n => some (.atom n)
  | .natom n => some (.not (.atom n))
  | .and φ ψ =>
      match formulaRetract φ, formulaRetract ψ with
      | some A, some B => some (.and A B)
      | _, _ => none
  | .or φ ψ =>
      match formulaRetract φ, formulaRetract ψ with
      | some A, some B => some (.or A B)
      | _, _ => none
  | .verum => none
  | .falsum => none

theorem retract_embed_of_nnf {A : Formula} (h : IsNNF A) :
    formulaRetract (formulaEmbed A) = some A := by
  induction A with
  | atom n => rfl
  | not A ih =>
      cases A with
      | atom n => rfl
      | not _ => cases h
      | and _ _ => cases h
      | or _ _ => cases h
  | and A B ihA ihB =>
      rcases h with ⟨hA, hB⟩
      simp [formulaEmbed, formulaRetract, ihA hA, ihB hB]
  | or A B ihA ihB =>
      rcases h with ⟨hA, hB⟩
      simp [formulaEmbed, formulaRetract, ihA hA, ihB hB]

/-! ## Cut-free Tait (propositional; Foundation's named `IsCutFree` is FO) -/

def TaitCutFree {T : Theory Nat} {Γ : Sequent Nat} :
    Derivation T Γ → Prop
  | .axL _ _ => True
  | .verum _ => True
  | .or d => TaitCutFree d
  | .and dp dq => TaitCutFree dp ∧ TaitCutFree dq
  | .wk d _ => TaitCutFree d
  | .cut _ _ => False
  | .axm _ => True

theorem not_taitCutFree_cut {T : Theory Nat} {Δ : Sequent Nat}
    {φ : NNFormula Nat} (dp : T ⟹ φ :: Δ) (dn : T ⟹ ∼φ :: Δ) :
    ¬ TaitCutFree (Derivation.cut dp dn) :=
  fun h => h

/-! ## Forget sequents: Tait derivation → GSLT proof -/

def forgetSequentNamed? {T : Theory Nat} {Γ : Sequent Nat} :
    Derivation T Γ → Option Proof
  | .axL _ a => some (.id (.atom a))
  | .verum _ => none
  | .or d => forgetSequentNamed? d
  | .and dp dq =>
      match forgetSequentNamed? dp, forgetSequentNamed? dq with
      | some p, some q => some (.andIntro p q)
      | _, _ => none
  | .wk d _ => forgetSequentNamed? d
  | .cut (φ := φ) dp dn =>
      match formulaRetract φ, forgetSequentNamed? dp, forgetSequentNamed? dn with
      | some A, some p, some q => some (.cut A p q)
      | _, _, _ => none
  | .axm _ => none

theorem forget_axL {T : Theory Nat} {Δ : Sequent Nat} {a : Nat} :
    forgetSequentNamed? (T := T) (Derivation.axL Δ a) = some (.id (.atom a)) :=
  rfl

theorem forget_cut_hasCut {T : Theory Nat} {Δ : Sequent Nat} {φ : NNFormula Nat}
    (dp : T ⟹ φ :: Δ) (dn : T ⟹ ∼φ :: Δ) {p : Proof}
    (h : forgetSequentNamed? (Derivation.cut dp dn) = some p) :
    HasCut p := by
  dsimp [forgetSequentNamed?] at h
  cases hφ : formulaRetract φ with
  | none => simp [hφ] at h
  | some A =>
      cases hp : forgetSequentNamed? dp with
      | none => simp [hφ, hp] at h
      | some p' =>
          cases hq : forgetSequentNamed? dn with
          | none => simp [hφ, hp, hq] at h
          | some q' =>
              simp [hφ, hp, hq] at h
              subst h
              exact HasCut.atRoot

theorem taitCutFree_forget_cutFree {T : Theory Nat} {Γ : Sequent Nat}
    (d : Derivation T Γ) (hf : TaitCutFree d) {p : Proof}
    (h : forgetSequentNamed? d = some p) : CutFree p := by
  induction d generalizing p with
  | axL _ a =>
      simp [forgetSequentNamed?] at h
      subst h
      exact id_cutFree _
  | verum _ =>
      simp [forgetSequentNamed?] at h
  | or d ih =>
      exact ih hf h
  | and dp dq ihp ihq =>
      rcases hf with ⟨hfp, hfq⟩
      dsimp [forgetSequentNamed?] at h
      cases hp : forgetSequentNamed? dp with
      | none => simp [hp] at h
      | some p' =>
          cases hq : forgetSequentNamed? dq with
          | none => simp [hp, hq] at h
          | some q' =>
              simp [hp, hq] at h
              subst h
              intro contra
              cases contra with
              | andIntro_left hp' => exact ihp hfp hp hp'
              | andIntro_right hq' => exact ihq hfq hq hq'
  | wk d _ ih =>
      exact ih hf h
  | cut _ _ =>
      exact (hf.elim)
  | axm _ =>
      simp [forgetSequentNamed?] at h

/-- Building a Tait cut grows derivation length. Eliminating a GSLT cut
shrinks proof size. Same word, opposite direction. -/
theorem tait_cut_increases_length {T : Theory Nat} {Δ : Sequent Nat}
    {φ : NNFormula Nat} (dp : T ⟹ φ :: Δ) (dn : T ⟹ ∼φ :: Δ) :
    Derivation.length (Derivation.cut dp dn) =
      Nat.succ (max (Derivation.length dp) (Derivation.length dn)) :=
  rfl

theorem gslt_cutStep_decreases {p q : Proof} (h : CutStep p q) :
    proofSize q < proofSize p :=
  cutStep_decreases_proofSize h

/-- Identity on an atom is the Tait axiom pair `atom`/`natom`, after
forgetting the sequent. -/
theorem axL_forgets_to_id (Δ : List (NNFormula Nat)) (a : Nat) :
    forgetSequentNamed? (T := (∅ : Theory Nat)) (Derivation.axL Δ a) =
      some (.id (.atom a)) :=
  rfl

/-! ## Worked intersection: Tait cut of a weakened axiom is a GSLT redex -/

private theorem subset_axL_into_cut_left :
    ([NNFormula.atom 0, NNFormula.natom 0] :
      List (NNFormula Nat)) ⊆
      [NNFormula.atom 0, NNFormula.atom 0, NNFormula.natom 0] := by
  intro x hx
  cases hx with
  | head => exact .head _
  | tail _ hx =>
      cases hx with
      | head => exact .tail _ (.tail _ (.head _))
      | tail _ hx => cases hx

private theorem subset_axL_into_cut_right :
    ([NNFormula.atom 0, NNFormula.natom 0] :
      List (NNFormula Nat)) ⊆
      [NNFormula.natom 0, NNFormula.atom 0, NNFormula.natom 0] := by
  intro x hx
  cases hx with
  | head => exact .tail _ (.head _)
  | tail _ hx =>
      cases hx with
      | head => exact .head _
      | tail _ hx => cases hx

/-- Tait cut on `atom 0` after weakening `axL`. Length is 2; `axL` itself
has length 0. -/
def taitCutOnAtom0 :
    Derivation (∅ : Theory Nat)
      [NNFormula.atom 0, NNFormula.natom 0] :=
  Derivation.cut
    (φ := NNFormula.atom 0)
    (Derivation.wk (Derivation.axL [] 0) subset_axL_into_cut_left)
    (Derivation.wk (Derivation.axL [] 0) subset_axL_into_cut_right)

theorem taitCutOnAtom0_length :
    Derivation.length taitCutOnAtom0 = 2 :=
  rfl

theorem taitCutOnAtom0_not_cutFree :
    ¬ TaitCutFree taitCutOnAtom0 :=
  fun h => h

/-- Forgetting the sequent yields a GSLT axiom-cut: `cut A (id A) (id A)`. -/
theorem taitCutOnAtom0_forgets_to_axiom_cut :
    forgetSequentNamed? taitCutOnAtom0 =
      some (.cut (.atom 0) (.id (.atom 0)) (.id (.atom 0))) :=
  rfl

theorem taitCutOnAtom0_forgotten_hasCut {p : Proof}
    (h : forgetSequentNamed? taitCutOnAtom0 = some p) : HasCut p := by
  simp [taitCutOnAtom0_forgets_to_axiom_cut] at h
  exact h ▸ HasCut.atRoot

/-- The forgotten Tait cut is a GSLT redex: axiom-cut is renaming. -/
theorem taitCutOnAtom0_is_gslt_redex :
    CutStep
      (.cut (.atom 0) (.id (.atom 0)) (.id (.atom 0)))
      (.id (.atom 0)) :=
  CutStep.idLeft (.atom 0) (.id (.atom 0))

theorem taitCutOnAtom0_gslt_size_falls :
    proofSize (.id (.atom 0)) <
      proofSize (.cut (.atom 0) (.id (.atom 0)) (.id (.atom 0))) :=
  cutStep_decreases_proofSize taitCutOnAtom0_is_gslt_redex

/-! ## Intersection with the rest of the kernel

`propositionalGSLT` is a GSLT, so it induces the same OSLF Galois as rho
or any other theory. The diamond is “a `CutStep` exists”. That modality
is not Tait `Derivation.cut` (which grows length) and not `SoundCut`
(a named meeting site with a residual).
-/

theorem propositional_induces_galois :
    GaloisConnection (gsltDiamond propositionalGSLT) (gsltBox propositionalGSLT) :=
  gsltGalois propositionalGSLT

theorem propositional_diamond_iff_cutStep (P : Proof → Prop) (p : Proof) :
    gsltDiamond propositionalGSLT P p ↔ ∃ q, CutStep p q ∧ P q :=
  gsltDiamond_spec propositionalGSLT P p

theorem gslt_step_iff_cutStep (p q : Proof) :
    propositionalGSLT.Step p q ↔ CutStep p q :=
  Iff.rfl

#print axioms retract_embed_of_nnf
#print axioms not_taitCutFree_cut
#print axioms forget_cut_hasCut
#print axioms taitCutFree_forget_cutFree
#print axioms tait_cut_increases_length
#print axioms gslt_cutStep_decreases
#print axioms taitCutOnAtom0_forgets_to_axiom_cut
#print axioms taitCutOnAtom0_is_gslt_redex
#print axioms propositional_induces_galois
#print axioms propositional_diamond_iff_cutStep

end Mettapedia.Logic.Bridges.PropositionalCutTait
