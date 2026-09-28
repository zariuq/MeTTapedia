import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.SetHostedProfile
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.LinkedControls

/-!
# Controls for the hosted set profile

The laws of the generic carrier, at the set profile (`setSignedProfile`).

Positive controls:

* **zero-add**: with induction, reflexivity and substitution published by the
  generic carrier, the generic compiler links the zero-add proof to the term
  of the fixed-profile linking, a closed term of the object package at the
  decoding of its theorem (`zeroAdd_hosted`), strongly normalizing
  (`zeroAdd_hosted_sn`);
* **symmetry**: the proof library's expansion of symmetry at `num → num` links
  through the same laws to the fixed-profile linked term, typed at the decoding
  of its theorem (`symmetry_hosted`).

Negative controls:

* **residual list**: with substitution left unpublished, the residual list of
  zero-add is substitution alone, and the assumption constants of the link are
  exactly that list (`zeroAdd_residual`, `zeroAdd_residual_link`);
* **wrong realizer**: the realizer of reflexivity is not a closed term at the
  decoding of `∀x : num. x = suc x`, so it cannot realize that assumption
  (`reflRealization_rejected`);
* **frame**: replacing the realization of an assumption the proof uses by a
  fresh constant changes the linked term (`zeroAdd_frame_tight`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Impredicative
open Mettapedia.Logic
open ConstantExpansion (constantNames)
open SetProfile (SetBase SetConst numTy zeroAddProof zeroAddStatement zeroAddAssumptions)
open IdentityEquality.Translation (linkedZeroAdd)
open IdentityEquality.Linking (symmetryProof symmetryAssumptions symmetryStatement functions
  linkedSymmetry)
open HOLNativeGenericProofCompiler.Modulo (compileModulo linkHyps residual)
open CertifiedTransformProgram.Execution (numeral)
open Package (numT)

namespace CodeModel

/-! ## Zero-add -/

/-- The zero-add document's assumptions, published by the generic carrier. -/
def zeroAddHosted : ∀ i : Fin zeroAddAssumptions.length,
    setHostedProfile.Published (zeroAddAssumptions.get i)
  | ⟨0, _⟩ => .induction numInductive_mem
  | ⟨1, _⟩ => .reflexivity numTy
  | ⟨2, _⟩ => .substitution numTy

theorem zeroAddHosted_realization (i : Fin zeroAddAssumptions.length) :
    (zeroAddHosted i).realization = (IdentityEquality.Linking.zeroAddPublished i).realization := by
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => exact realization_substitution numTy

theorem zeroAdd_compiledHosted :
    setReading.compile zeroAddProof (fun i => Fin.elim0 i) (fun i => (zeroAddHosted i).realization) =
      some linkedZeroAdd := by
  rw [funext zeroAddHosted_realization]
  exact zeroAdd_compiledO

/-- **Zero-add, through the generic laws.** The generic compiler links the
zero-add proof against the facts of the generic carrier to the fixed-profile
linked term, a closed term of the object package at the decoding of the
signature's representation of `∀k. add zero k = k`. -/
theorem zeroAdd_hosted :
    compileModulo SetProfile.signature zeroAddProof (fun i => Fin.elim0 i)
        (fun i => (zeroAddHosted i).realization) = some linkedZeroAdd ∧
      ∃ code, FormationSensitiveHOLInterface.represent SetProfile.signature zeroAddStatement =
          some code ∧ Typed objectRules .nil linkedZeroAdd (programCodes.holdsOf code) :=
  setSignedProfile.linked_typedO zeroAdd_articles zeroAddHosted zeroAdd_compiledHosted

theorem zeroAdd_hosted_sn : StrongNormalization.SN objectRules linkedZeroAdd := by
  obtain ⟨_, _, _, typed⟩ := zeroAdd_hosted
  exact (objectRules_sn .nil typed).1

/-! ## Symmetry at `num → num` -/

/-- The assumptions of symmetry, published by the generic carrier. -/
def symmetryHosted : ∀ i : Fin (symmetryAssumptions functions).length,
    setHostedProfile.Published ((symmetryAssumptions functions).get i)
  | ⟨0, _⟩ => .reflexivity functions
  | ⟨1, _⟩ => .substitution functions

theorem symmetryHosted_realization (i : Fin (symmetryAssumptions functions).length) :
    (symmetryHosted i).realization =
      (IdentityEquality.Linking.symmetryPublished functions i).realization := by
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => exact realization_substitution functions

/-- The two conversion articles of symmetry are β-steps between read terms. -/
theorem symmetry_articles :
    setReading.ArticlesRead SetProfile.sourceEquations (symmetryProof functions) :=
  .allI (.allI (.impI (.convert (readStep (.beta _ _) rfl rfl)
    (.impE (.impE (.allE _ (.allE _ (.allE _ (.hyp _)))) (.hyp _))
      (.convert (.symm _ _ (readStep (.beta _ _) rfl rfl)) (.allE _ (.hyp _)))))))

theorem symmetry_compiledHosted :
    setReading.compile (symmetryProof functions) (fun i => Fin.elim0 i)
      (fun i => (symmetryHosted i).realization) = some linkedSymmetry := by
  rw [funext symmetryHosted_realization]
  rfl

/-- **Symmetry, through the generic laws.** The expansion of symmetry at
`num → num` links against the facts of the generic carrier to the
fixed-profile linked term, a closed term of the object package at the decoding
of `∀ f g. f = g → g = f`. -/
theorem symmetry_hosted :
    compileModulo SetProfile.signature (symmetryProof functions) (fun i => Fin.elim0 i)
        (fun i => (symmetryHosted i).realization) = some linkedSymmetry ∧
      ∃ code, FormationSensitiveHOLInterface.represent SetProfile.signature
          (symmetryStatement functions) = some code ∧
        Typed objectRules .nil linkedSymmetry (programCodes.holdsOf code) :=
  setSignedProfile.linked_typedO symmetry_articles symmetryHosted symmetry_compiledHosted

/-! ## An unpublished assumption stays in the residual list -/

/-- Zero-add with induction and reflexivity published and substitution not. -/
def zeroAddPartial : ∀ i : Fin zeroAddAssumptions.length,
    Option (setHostedProfile.Published (zeroAddAssumptions.get i))
  | ⟨0, _⟩ => some (.induction numInductive_mem)
  | ⟨1, _⟩ => some (.reflexivity numTy)
  | ⟨2, _⟩ => none

/-- **The residual list** of zero-add with substitution unpublished is
substitution alone. -/
theorem zeroAdd_residual :
    residual zeroAddProof (setSignedProfile.realizations zeroAddPartial) = [⟨2, by decide⟩] := by
  decide

/-- A property of the three assumption indices, checked at each. -/
theorem fin3_cases {P : Fin 3 → Prop} (at0 : P 0) (at1 : P 1) (at2 : P 2) : ∀ i, P i
  | ⟨0, _⟩ => at0
  | ⟨1, _⟩ => at1
  | ⟨2, _⟩ => at2

theorem assumptionNames_injective : Function.Injective SetProfile.assumptionNames :=
  fin3_cases (P := fun i => ∀ j, SetProfile.assumptionNames i = SetProfile.assumptionNames j → i = j)
    (fin3_cases (by decide) (by decide) (by decide))
    (fin3_cases (by decide) (by decide) (by decide))
    (fin3_cases (by decide) (by decide) (by decide))

theorem assumptionNames_ne_constantName {τ : HOL.Ty SetBase} (c : SetConst τ) :
    ∀ i : Fin 3, SetProfile.assumptionNames i ≠ SetProfile.constantName c := by
  cases c <;> exact fin3_cases (by decide) (by decide) (by decide)

theorem assumptionNames_ne_impName : ∀ i : Fin 3, SetProfile.assumptionNames i ≠ SetProfile.impName :=
  fin3_cases (by decide) (by decide) (by decide)

/-- The assumption names of the checker are no symbol of the signature. -/
theorem assumptionNames_not_symbol (i : Fin 3) :
    ¬ SetProfile.signature.SymbolName (SetProfile.assumptionNames i) := by
  have noAll : SetProfile.allInstance? (SetProfile.assumptionNames i) = none :=
    fin3_cases (P := fun i => SetProfile.allInstance? (SetProfile.assumptionNames i) = none)
      (by decide) (by decide) (by decide) i
  have noEq : SetProfile.eqInstance? (SetProfile.assumptionNames i) = none :=
    fin3_cases (P := fun i => SetProfile.eqInstance? (SetProfile.assumptionNames i) = none)
      (by decide) (by decide) (by decide) i
  rintro (⟨τ, c, mem⟩ | mem | ⟨τ, mem⟩ | ⟨τ, mem⟩)
  · change _ ∈ [SetProfile.constantName c] at mem
    exact assumptionNames_ne_constantName c i (List.mem_singleton.mp mem)
  · change _ ∈ [SetProfile.impName] at mem
    exact assumptionNames_ne_impName i (List.mem_singleton.mp mem)
  · change _ ∈ [SetProfile.allName τ] at mem
    rw [List.mem_singleton] at mem
    rw [mem, SetProfile.allInstance?_allName] at noAll
    cases noAll
  · change _ ∈ [SetProfile.eqName τ] at mem
    rw [List.mem_singleton] at mem
    rw [mem, SetProfile.eqInstance?_eqName] at noEq
    cases noEq

/-- The assumption names do not occur in the published realizations. -/
theorem zeroAddPartial_fresh (i j : Fin zeroAddAssumptions.length)
    (p : setSignedProfile.Published (zeroAddAssumptions.get j)) (found : zeroAddPartial j = some p) :
    SetProfile.assumptionNames i ∉ constantNames p.realization := by
  match j, p, found with
  | ⟨0, _⟩, _, rfl =>
      exact fin3_cases (P := fun i => SetProfile.assumptionNames i ∉
        constantNames IdentityEquality.Realizations.inductionRealization)
        (by decide) (by decide) (by decide) i
  | ⟨1, _⟩, _, rfl =>
      exact fin3_cases (P := fun i => SetProfile.assumptionNames i ∉
        constantNames IdentityEquality.Realizations.reflRealization)
        (by decide) (by decide) (by decide) i
  | ⟨2, _⟩, _, found => cases found

/-- **The link keeps exactly the residual list.** Linking zero-add with
substitution unpublished and the checker's assumption names for the
unpublished facts, the assumption constants of the link are the residual list,
and substitution's is among them. -/
theorem zeroAdd_residual_link :
    ∃ out : Tower.Tm 0, compileModulo SetProfile.signature zeroAddProof (fun i => Fin.elim0 i)
        (linkHyps (setSignedProfile.realizations zeroAddPartial) SetProfile.assumptionNames) =
          some out ∧
      (List.finRange zeroAddAssumptions.length).filter
          (fun i => decide (SetProfile.assumptionNames i ∈ constantNames out)) =
        residual zeroAddProof (setSignedProfile.realizations zeroAddPartial) ∧
      SetProfile.substName ∈ constantNames out := by
  obtain ⟨out, linked⟩ : ∃ out : Tower.Tm 0, compileModulo SetProfile.signature zeroAddProof
      (fun i => Fin.elim0 i)
      (linkHyps (setSignedProfile.realizations zeroAddPartial) SetProfile.assumptionNames) =
        some out := ⟨_, rfl⟩
  refine ⟨out, linked, HOLNativeGenericProofCompiler.Modulo.assumed_eq_residual SetProfile.signature
    zeroAddProof (fun i => Fin.elim0 i) _ SetProfile.assumptionNames assumptionNames_injective
    assumptionNames_not_symbol (fun _ j => Fin.elim0 j)
    (fun i j r found => by
      obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp found
      exact zeroAddPartial_fresh i j p hp)
    linked, ?_⟩
  exact (setSignedProfile.assumed_link zeroAddProof zeroAddPartial SetProfile.assumptionNames
    assumptionNames_injective assumptionNames_not_symbol zeroAddPartial_fresh linked
    ⟨2, by decide⟩).mpr ⟨rfl, rfl⟩

/-! ## A wrong-type realizer is rejected -/

/-- `∀x : num. x = suc x`, a false fact. -/
def successorFixpoint : HOL.Formula SetConst [] :=
  .all (σ := numTy) (.eq (.var .vz) (SetProfile.sucT (.var .vz)))

theorem successorFixpoint_read :
    setReading.term successorFixpoint =
      some (setReading.allOf numTy
        (.lam (setReading.eqOf numTy (.var 0) (.app (.const sucN) (.var 0))))) :=
  rfl

/-- **A wrong-type realizer is rejected.** The realizer of reflexivity is not a
closed term at the decoding of `∀x : num. x = suc x`: the typing premise of a
realized assumption fails for it. -/
theorem reflRealization_rejected :
    ¬ ∃ code, setReading.term successorFixpoint = some code ∧
      Typed setReading.rules .nil
        (HostedProfile.Published.reflexivity (P := setHostedProfile) numTy).realization
        (setReading.holdsOf code) := by
  rintro ⟨code, read, typed⟩
  rw [successorFixpoint_read, Option.some.injEq] at read
  subst read
  have successor : Typed setReading.rules (.snoc .nil (setReading.carrierAt 0 numTy))
      (.app (.const sucN) (.var 0)) (setReading.carrierAt 1 numTy) :=
    .appElim suc_typedO (setReading.var_carrier numTy)
  have body : Typed setReading.rules (.snoc .nil (setReading.carrierAt 0 numTy))
      (setReading.eqOf numTy (.var 0) (.app (.const sucN) (.var 0))) setReading.codes.propT :=
    setReading_laws.eqOf_typed (setReading.var_carrier numTy) successor
  have applied := setReading_laws.allElim body typed (zero_typedO (Γ := .nil))
  have identity : Typed objectRules .nil
      (.app (HostedProfile.Published.reflexivity (P := setHostedProfile) numTy).realization
        (.const zeroN)) (.id numT (numeral 0) (numeral 1)) :=
    .conv applied (setReading_laws.equal_holds_eq (τ := numTy) zero_typedO (numeral_typedO 1))
      (.sort _)
  exact numeral_identity_apart (j := 0) (k := 1) (by decide) _ identity

/-! ## The frame law is tight -/

/-- **The frame law is tight.** Zero-add uses substitution; replacing its
realization by a fresh constant changes the linked term. -/
theorem zeroAdd_frame_tight :
    ∃ out, compileModulo SetProfile.signature zeroAddProof (fun i => Fin.elim0 i)
        (Function.update (fun i => (zeroAddHosted i).realization) ⟨2, by decide⟩
          (.const SetProfile.substName)) = some out ∧
      out ≠ linkedZeroAdd :=
  HOLNativeGenericProofCompiler.Modulo.compileModulo_frame_tight SetProfile.signature zeroAddProof
    (fun i => Fin.elim0 i) _ zeroAdd_hosted.1 ⟨2, by decide⟩ rfl (by decide)

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
