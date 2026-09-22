import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveHOLProofListIntegration
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.FormationSensitiveHOLProofConversion
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.ConversionCoherence
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.ConversionConservativeExtension
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.ConservativeConversion

/-!
# Conversion-coherent completion of the mixed HOL/native rules

Duplicated metadata is retained with evidence of conversion in the original
joint List/identity/relator and HOL decoder package. This auxiliary proof presentation does not add runtime
rules: every completed contraction is proved convertible by the authored
rules, and every authored root is included on its exact diagonal.
-/

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace HOLNativeMixedConversionCompletion

open Presentation Presentation.Declaration NativeIndexedFamilies
open FormationSensitiveHOLProofFamily FormationSensitiveHOLUniformList

variable {n m : Nat}

abbrev AuthoredConv (left right : Tower.Tm n) : Prop :=
  Conv FormationSensitiveHOLProofListIntegration.rules.headEq left right FormationSensitiveHOLProofListIntegration.rules.computation

theorem coherent_transport {left right left' right' : Tower.Tm n}
    (coherent : AuthoredConv left right)
    (first : AuthoredConv left left') (second : AuthoredConv right right') :
    AuthoredConv left' right' :=
  .trans _ _ _ (.symm _ _ first) (.trans _ _ _ coherent second)

theorem nilApp_congr {x0 x0' : Tower.Tm n}
    (h0 : AuthoredConv x0 x0') :
    AuthoredConv (Intrinsic.nilApp x0) (Intrinsic.nilApp x0') :=
  (Conv.congApp (.refl _) h0)

theorem consApp_congr {x0 x1 x2 x0' x1' x2' : Tower.Tm n}
    (h0 : AuthoredConv x0 x0') (h1 : AuthoredConv x1 x1') (h2 : AuthoredConv x2 x2') :
    AuthoredConv (Intrinsic.consApp x0 x1 x2) (Intrinsic.consApp x0' x1' x2') :=
  (Conv.congApp (Conv.congApp (Conv.congApp (.refl _) h0) h1) h2)

theorem listElim_congr {x0 x1 x2 x3 x4 x0' x1' x2' x3' x4' : Tower.Tm n}
    (h0 : AuthoredConv x0 x0') (h1 : AuthoredConv x1 x1') (h2 : AuthoredConv x2 x2') (h3 : AuthoredConv x3 x3') (h4 : AuthoredConv x4 x4') :
    AuthoredConv (Intrinsic.eliminateApp x0 x1 x2 x3 x4) (Intrinsic.eliminateApp x0' x1' x2' x3' x4') :=
  (Conv.congApp (Conv.congApp (Conv.congApp (Conv.congApp (Conv.congApp (.refl _) h0) h1) h2) h3) h4)

theorem idElim_congr {x0 x1 x2 x3 x4 x5 x0' x1' x2' x3' x4' x5' : Tower.Tm n}
    (h0 : AuthoredConv x0 x0') (h1 : AuthoredConv x1 x1') (h2 : AuthoredConv x2 x2') (h3 : AuthoredConv x3 x3') (h4 : AuthoredConv x4 x4') (h5 : AuthoredConv x5 x5') :
    AuthoredConv (Intrinsic.identityEliminateApp x0 x1 x2 x3 x4 x5) (Intrinsic.identityEliminateApp x0' x1' x2' x3' x4' x5') :=
  (Conv.congApp (Conv.congApp (Conv.congApp (Conv.congApp (Conv.congApp (Conv.congApp (.refl _) h0) h1) h2) h3) h4) h5)

theorem nilRel_congr {x0 x1 x2 x0' x1' x2' : Tower.Tm n}
    (h0 : AuthoredConv x0 x0') (h1 : AuthoredConv x1 x1') (h2 : AuthoredConv x2 x2') :
    AuthoredConv (IntrinsicRelator.nilRelApp x0 x1 x2) (IntrinsicRelator.nilRelApp x0' x1' x2') :=
  (Conv.congApp (Conv.congApp (Conv.congApp (.refl _) h0) h1) h2)

theorem consRel_congr {x0 x1 x2 x3 x4 x5 x6 x7 x8 x0' x1' x2' x3' x4' x5' x6' x7' x8' : Tower.Tm n}
    (h0 : AuthoredConv x0 x0') (h1 : AuthoredConv x1 x1') (h2 : AuthoredConv x2 x2') (h3 : AuthoredConv x3 x3') (h4 : AuthoredConv x4 x4') (h5 : AuthoredConv x5 x5') (h6 : AuthoredConv x6 x6') (h7 : AuthoredConv x7 x7') (h8 : AuthoredConv x8 x8') :
    AuthoredConv (IntrinsicRelator.consRelApp x0 x1 x2 x3 x4 x5 x6 x7 x8) (IntrinsicRelator.consRelApp x0' x1' x2' x3' x4' x5' x6' x7' x8') :=
  (Conv.congApp (Conv.congApp (Conv.congApp (Conv.congApp (Conv.congApp (Conv.congApp (Conv.congApp (Conv.congApp (Conv.congApp (.refl _) h0) h1) h2) h3) h4) h5) h6) h7) h8)

theorem relElim_congr {x0 x1 x2 x3 x4 x5 x6 x7 x8 x0' x1' x2' x3' x4' x5' x6' x7' x8' : Tower.Tm n}
    (h0 : AuthoredConv x0 x0') (h1 : AuthoredConv x1 x1') (h2 : AuthoredConv x2 x2') (h3 : AuthoredConv x3 x3') (h4 : AuthoredConv x4 x4') (h5 : AuthoredConv x5 x5') (h6 : AuthoredConv x6 x6') (h7 : AuthoredConv x7 x7') (h8 : AuthoredConv x8 x8') :
    AuthoredConv (IntrinsicRelator.eliminateApp x0 x1 x2 x3 x4 x5 x6 x7 x8) (IntrinsicRelator.eliminateApp x0' x1' x2' x3' x4' x5' x6' x7' x8') :=
  (Conv.congApp (Conv.congApp (Conv.congApp (Conv.congApp (Conv.congApp (Conv.congApp (Conv.congApp (Conv.congApp (Conv.congApp (.refl _) h0) h1) h2) h3) h4) h5) h6) h7) h8)

theorem proof_congr {p q : Tower.Tm n} (h : AuthoredConv p q) :
    AuthoredConv (proof p) (proof q) := Conv.congApp (.refl _) h

theorem implicationFamily_congr {p q p' q' : Tower.Tm n}
    (hp : AuthoredConv p p') (hq : AuthoredConv q q') :
    AuthoredConv (implicationFamily p q) (implicationFamily p' q') :=
  Conv.congPi (proof_congr hp) ((proof_congr hq).renameTerms wk)

theorem universalFamily_congr {a f a' f' : Tower.Tm n}
    (ha : AuthoredConv a a') (hf : AuthoredConv f f') :
    AuthoredConv (universalFamily a f) (universalFamily a' f') :=
  Conv.congPi ha (proof_congr (Conv.congApp (hf.renameTerms wk) (.refl _)))

inductive Root : Tower.Tm n → Tower.Tm n → Prop where
  | listNil {a p z s innerA : Tower.Tm n} :
      AuthoredConv innerA a →
      Root (Intrinsic.eliminateApp a p z s (Intrinsic.nilApp innerA)) z
  | listCons {a p z s innerA h t : Tower.Tm n} :
      AuthoredConv innerA a →
      Root (Intrinsic.eliminateApp a p z s (Intrinsic.consApp innerA h t))
        (.app (.app (.app s h) t) (Intrinsic.eliminateApp a p z s t))
  | identity {a x p d y witness : Tower.Tm n} :
      AuthoredConv y x → AuthoredConv witness x →
      Root (Intrinsic.identityEliminateApp a x p d y (.refl witness)) d
  | relNil {a b r p z s xs ys innerA innerB innerR : Tower.Tm n} :
      AuthoredConv innerA a → AuthoredConv innerB b → AuthoredConv innerR r →
      AuthoredConv xs (Intrinsic.nilApp a) → AuthoredConv ys (Intrinsic.nilApp b) →
      Root (IntrinsicRelator.eliminateApp a b r p z s xs ys
        (IntrinsicRelator.nilRelApp innerA innerB innerR)) z
  | relCons {a b r p z s xs ys innerA innerB innerR h k t u he te : Tower.Tm n} :
      AuthoredConv innerA a → AuthoredConv innerB b → AuthoredConv innerR r →
      AuthoredConv xs (Intrinsic.consApp a h t) → AuthoredConv ys (Intrinsic.consApp b k u) →
      Root (IntrinsicRelator.eliminateApp a b r p z s xs ys
        (IntrinsicRelator.consRelApp innerA innerB innerR h k t u he te))
        (.app (.app (.app (.app (.app (.app (.app s h) k) t) u) he) te)
          (IntrinsicRelator.eliminateApp a b r p z s t u te))

  | implication (p q : Tower.Tm n) :
      Root (proof (rawImp p q)) (implicationFamily p q)
  | universal (a f : Tower.Tm n) :
      Root (proof (universalProposition a f)) (universalFamily a f)

theorem Root.rename {left right : Tower.Tm n} (root : Root left right) (rho : Ren n m) :
    Root (rename rho left) (rename rho right) := by
  cases root with
  | listNil first => exact .listNil (first.renameTerms rho)
  | listCons first => exact .listCons (first.renameTerms rho)
  | identity first second => exact .identity (first.renameTerms rho) (second.renameTerms rho)
  | relNil first second third fourth fifth =>
      exact .relNil (first.renameTerms rho) (second.renameTerms rho) (third.renameTerms rho)
        (fourth.renameTerms rho) (fifth.renameTerms rho)
  | relCons first second third fourth fifth =>
      exact .relCons (first.renameTerms rho) (second.renameTerms rho) (third.renameTerms rho)
        (fourth.renameTerms rho) (fifth.renameTerms rho)

  | implication p q =>
      simpa only [proof_rename, implicationFamily_rename, rawImp, Presentation.rename] using
        Root.implication (Presentation.rename rho p) (Presentation.rename rho q)
  | universal a f =>
      simpa only [proof_rename, universalFamily_rename, universalProposition, Presentation.rename] using
        Root.universal (Presentation.rename rho a) (Presentation.rename rho f)

theorem Root.substitute {left right : Tower.Tm n} (root : Root left right)
    (sigma : Sub Tower.Head n m) : Root (subst sigma left) (subst sigma right) := by
  cases root with
  | listNil first => exact .listNil (first.substitute sigma)
  | listCons first => exact .listCons (first.substitute sigma)
  | identity first second => exact .identity (first.substitute sigma) (second.substitute sigma)
  | relNil first second third fourth fifth =>
      exact .relNil (first.substitute sigma) (second.substitute sigma) (third.substitute sigma)
        (fourth.substitute sigma) (fifth.substitute sigma)
  | relCons first second third fourth fifth =>
      exact .relCons (first.substitute sigma) (second.substitute sigma) (third.substitute sigma)
        (fourth.substitute sigma) (fifth.substitute sigma)

  | implication p q =>
      simpa only [proof_subst, implicationFamily_subst, rawImp, subst] using
        Root.implication (subst sigma p) (subst sigma q)
  | universal a f =>
      simpa only [proof_subst, universalFamily_subst, universalProposition, subst] using
        Root.universal (subst sigma a) (subst sigma f)

def computation : RootComputation Tower.Head where
  step := Root
  rename := by intro n m rho left right root; exact root.rename rho
  substitute := by intro n m sigma left right root; exact root.substitute sigma

def rules : Rules Tower.Head :=
  { FormationSensitiveHOLProofListIntegration.rules with computation := computation }

theorem Root.sound {left right : Tower.Tm n} (root : Root left right) :
    AuthoredConv left right := by
  cases root with
  | listNil ca =>
      exact .trans _ _ _ (listElim_congr (.refl _) (.refl _) (.refl _) (.refl _) (nilApp_congr ca))
        (.rel _ _ (.root (.inherited (.declared ⟨.list (.nil _ _ _ _)⟩))))
  | listCons ca =>
      exact .trans _ _ _
        (listElim_congr (.refl _) (.refl _) (.refl _) (.refl _) (consApp_congr ca (.refl _) (.refl _)))
        (.rel _ _ (.root (.inherited (.declared ⟨.list (.cons _ _ _ _ _ _)⟩))))
  | identity cy cw =>
      exact .trans _ _ _
        (idElim_congr (.refl _) (.refl _) (.refl _) (.refl _) cy
          (Conv.mapCompatible Tm.refl (fun step => .congRefl step) cw))
        (.rel _ _ (.root (.inherited (.declared ⟨.list (.identity _ _ _ _)⟩))))
  | relNil ca cb cr cx cy =>
      exact .trans _ _ _
        (relElim_congr (.refl _) (.refl _) (.refl _) (.refl _) (.refl _) (.refl _) cx cy
          (nilRel_congr ca cb cr))
        (.rel _ _ (.root (.inherited (.declared ⟨.rel (.nil _ _ _ _ _ _)⟩))))
  | relCons ca cb cr cx cy =>
      exact .trans _ _ _
        (relElim_congr (.refl _) (.refl _) (.refl _) (.refl _) (.refl _) (.refl _) cx cy
          (consRel_congr ca cb cr (.refl _) (.refl _) (.refl _) (.refl _) (.refl _) (.refl _)))
        (.rel _ _ (.root (.inherited (.declared ⟨.rel (.cons _ _ _ _ _ _ _ _ _ _ _ _)⟩))))

  | implication p q => exact .rel _ _ (.root (.declared (.implication p q)))
  | universal a f => exact .rel _ _ (.root (.declared (.universal a f)))

theorem Root.of_iota {left right : Tower.Tm n}
    (evidence : IntrinsicRelator.CombinedIotaEvidence n left right) : Root left right := by
  cases evidence with
  | list evidence => cases evidence with
    | nil => exact .listNil (.refl _)
    | cons => exact .listCons (.refl _)
    | identity => exact .identity (.refl _) (.refl _)
  | rel evidence => cases evidence with
    | nil => exact .relNil (.refl _) (.refl _) (.refl _) (.refl _) (.refl _)
    | cons => exact .relCons (.refl _) (.refl _) (.refl _) (.refl _) (.refl _)

theorem native_opaque (name : DeclName) :
    FormationSensitiveHOLProofListIntegration.Execution.nativeInstance.signature.valueOf? name = none := by
  simp [LevelInstance.signature, Signature.valueOf_instantiateLevels,
    IntrinsicRelator.rawSignature_valueOf_none]

theorem root_inclusion {left right : Tower.Tm n}
    (root : FormationSensitiveHOLProofListIntegration.rules.computation.step left right) :
    Root left right := by
  cases root with
  | inherited native =>
      cases native with
      | inherited impossible => exact impossible.elim
      | delta lookup => rw [native_opaque] at lookup; cases lookup
      | declared evidence => obtain ⟨evidence⟩ := evidence; exact Root.of_iota evidence
  | delta lookup =>
      rw [FormationSensitiveHOLProofConversion.declarations_opaque] at lookup
      cases lookup
  | declared decoder =>
      cases decoder with
      | implication p q => exact .implication p q
      | universal a f => exact .universal a f

theorem conservative : ConversionConservativeExtension FormationSensitiveHOLProofListIntegration.rules rules where
  headEq_eq := rfl
  root_inclusion := root_inclusion
  root_sound := Root.sound

theorem conversion_iff (left right : Tower.Tm n) :
    AuthoredConv left right ↔ Conv rules.headEq left right rules.computation :=
  conservative.conversion_iff left right

#print axioms Root.rename
#print axioms Root.substitute
#print axioms Root.sound
#print axioms Root.of_iota
#print axioms conservative
#print axioms conversion_iff

end HOLNativeMixedConversionCompletion
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
