import Mettapedia.Languages.Agda.Structural.AdministrativeRootPreservation

/-!
# Compatible native administrative certificates

Certificates compose through elimination heads and spines, application
arguments, cons tails, and both append slots. Their steps are constructors of
the existing structural compatible closure. Action congruence is a fold over
actual action histories and retains arbitrary input/output conversions.

These constructors cover the displayed positions only. They do not claim
preservation through every signature argument or through beta computation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.AdministrativeStatics.Preservation

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Mettapedia.TypeTheory
open Statics (RawTm RawTy RawContext)

structure ActionCongruence {n : Nat} (Γ : RawContext n) (A : RawTy n) (es : Spine (scope n)) (B : RawTy n) where
  tail : ∀ e first second, es = cons e first → SpineCertificate first second →
    SpineEq Γ A es (cons e second) B
  argument : ∀ u v rest, es = cons (apply u) rest → TermCertificate u v →
    SpineEq Γ A es (cons (apply v) rest) B

def Congruence : Judgment → Type
  | .spineAction Γ A es B => ActionCongruence Γ A es B
  | _ => PUnit

noncomputable def congruenceRule {j : Judgment} (shape : RuleShape j)
    (children : Evidence Derivation (premises shape))
    (ih : Evidence Congruence (premises shape)) : Congruence j := by
  cases shape with
  | prior shape =>
      have children := priorPremiseEvidence children
      have ih := priorPremiseEvidence ih
      cases shape with
      | core | elimination => exact ⟨⟩
      | nil | append =>
          exact ⟨(fun _ _ _ same => by cases same), fun _ _ _ same => by cases same⟩
      | cons Γ A B u es C =>
          simp only [SpineStatics.premises] at children ih
          refine ⟨?_, ?_⟩
          · intro e first second same certificate
            cases same
            exact Derivation.spineCons
              (Derivation.core (.reflexivity Γ u A.code)
                (consEvidence CoreDerivation (children 0) (noEvidence CoreDerivation)))
              (certificate.equality Γ (B.instantiate u).code C (children 1))
          · intro first second rest same certificate
            obtain ⟨rfl, rfl⟩ := cons_apply_injective same
            exact Derivation.spineCons (certificate.equality Γ A.code (children 0)) (Derivation.spineRefl (children 1))
      | inputConversion Γ A' A es B =>
          simp only [SpineStatics.premises] at children ih
          exact ⟨fun e first second same certificate =>
            Derivation.spineInputConversion (children 0) ((ih 1).tail e first second same certificate),
            fun u v rest same certificate =>
              Derivation.spineInputConversion (children 0) ((ih 1).argument u v rest same certificate)⟩
      | outputConversion Γ A es B B' =>
          simp only [SpineStatics.premises] at children ih
          exact ⟨fun e first second same certificate =>
            Derivation.spineOutputConversion ((ih 0).tail e first second same certificate) (children 1),
            fun u v rest same certificate =>
              Derivation.spineOutputConversion ((ih 0).argument u v rest same certificate) (children 1)⟩
  | spineRefl | spineSymm | spineTrans | spineCons | spineAppend | spineInputConversion
    | spineOutputConversion | appendEmpty | appendCons | eliminationCongruence
    | emptyElimination | nestedElimination => exact ⟨⟩

noncomputable def congruence {n : Nat} {Γ : RawContext n} {A B : RawTy n} {es : Spine (scope n)}
    (tree : Action Γ A es B) : ActionCongruence Γ A es B :=
  IndexedPolynomial.Fix.eliminate presentation.polynomial (fun _ j _ => Congruence j)
    (fun _ _ shape children ih => congruenceRule shape children ih) () _ tree

noncomputable def TermCertificate.eliminateHead {n : Nat} {f g : RawTm n}
    (certificate : TermCertificate f g) (es : Spine (scope n)) :
    TermCertificate (eliminate f es) (eliminate g es) where
  step := by
    change CompatibleDerivations.Step Root
      (.op Op.eliminate (.cons f (.cons es .nil)))
      (.op Op.eliminate (.cons g (.cons es .nil)))
    apply CompatibleDerivations.Step.congr (R := Root) Op.eliminate
    apply CompatibleDerivations.ArgsStep.head
    exact certificate.step
  equality Γ _ tree :=
    let parts := tree.eliminationParts
    Derivation.eliminationCongruence (certificate.equality Γ parts.input parts.headTyping) (Derivation.spineRefl parts.action)

noncomputable def SpineCertificate.eliminateSpine {n : Nat} {es fs : Spine (scope n)}
    (certificate : SpineCertificate es fs) (head : RawTm n) : TermCertificate (eliminate head es) (eliminate head fs) where
  step := by
    change CompatibleDerivations.Step Root
      (.op Op.eliminate (.cons head (.cons es .nil)))
      (.op Op.eliminate (.cons head (.cons fs .nil)))
    apply CompatibleDerivations.Step.congr (R := Root) Op.eliminate
    apply CompatibleDerivations.ArgsStep.tail
    apply CompatibleDerivations.ArgsStep.head
    exact certificate.step
  equality Γ A tree :=
    let parts := tree.eliminationParts
    Derivation.eliminationCongruence
      (Derivation.core (.reflexivity Γ head parts.input)
        (consEvidence CoreDerivation parts.headTyping (noEvidence CoreDerivation)))
      (certificate.equality Γ parts.input A parts.action)

noncomputable def SpineCertificate.appendFirst {n : Nat} {es fs : Spine (scope n)}
    (certificate : SpineCertificate es fs) (rest : Spine (scope n)) :
    SpineCertificate (append es rest) (append fs rest) where
  step := by
    change CompatibleDerivations.Step Root
      (.op Op.append (.cons es (.cons rest .nil)))
      (.op Op.append (.cons fs (.cons rest .nil)))
    apply CompatibleDerivations.Step.congr (R := Root) Op.append
    apply CompatibleDerivations.ArgsStep.head
    exact certificate.step
  equality Γ A _ tree :=
    let parts := tree.splitAppend
    Derivation.spineAppend (certificate.equality Γ A parts.middle parts.first) (Derivation.spineRefl parts.second)

noncomputable def SpineCertificate.appendSecond {n : Nat} {es fs : Spine (scope n)}
    (certificate : SpineCertificate es fs) (first : Spine (scope n)) :
    SpineCertificate (append first es) (append first fs) where
  step := by
    change CompatibleDerivations.Step Root
      (.op Op.append (.cons first (.cons es .nil)))
      (.op Op.append (.cons first (.cons fs .nil)))
    apply CompatibleDerivations.Step.congr (R := Root) Op.append
    apply CompatibleDerivations.ArgsStep.tail
    apply CompatibleDerivations.ArgsStep.head
    exact certificate.step
  equality Γ _ B tree :=
    let parts := tree.splitAppend
    Derivation.spineAppend (Derivation.spineRefl parts.first) (certificate.equality Γ parts.middle B parts.second)

noncomputable def SpineCertificate.consTail {n : Nat} {es fs : Spine (scope n)}
    (certificate : SpineCertificate es fs) (head : Elim (scope n)) :
    SpineCertificate (cons head es) (cons head fs) where
  step := by
    change CompatibleDerivations.Step Root
      (.op Op.cons (.cons head (.cons es .nil)))
      (.op Op.cons (.cons head (.cons fs .nil)))
    apply CompatibleDerivations.Step.congr (R := Root) Op.cons
    apply CompatibleDerivations.ArgsStep.tail
    apply CompatibleDerivations.ArgsStep.head
    exact certificate.step
  equality _ _ _ tree := (congruence tree).tail head es fs rfl certificate

noncomputable def TermCertificate.argument {n : Nat} {u v : RawTm n}
    (certificate : TermCertificate u v) (rest : Spine (scope n)) :
    SpineCertificate (cons (apply u) rest) (cons (apply v) rest) where
  step := by
    change CompatibleDerivations.Step Root
      (.op Op.cons (.cons (apply u) (.cons rest .nil)))
      (.op Op.cons (.cons (apply v) (.cons rest .nil)))
    apply CompatibleDerivations.Step.congr (R := Root) Op.cons
    apply CompatibleDerivations.ArgsStep.head
    apply CompatibleDerivations.Step.congr (R := Root) Op.apply
    apply CompatibleDerivations.ArgsStep.head
    exact certificate.step
  equality _ _ _ tree := (congruence tree).argument u v rest rfl certificate

end Mettapedia.Languages.Agda.Structural.AdministrativeStatics.Preservation
