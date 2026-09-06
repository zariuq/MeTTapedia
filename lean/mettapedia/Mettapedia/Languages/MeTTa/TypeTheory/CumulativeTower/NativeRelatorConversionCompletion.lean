import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.IntrinsicNativeListRelator
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.ConversionCoherence
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.ConversionConservativeExtension

/-!
# Conversion-coherent completion of List, identity and relational elimination

Duplicated metadata is retained with evidence of conversion in the original
five-root package. This auxiliary proof presentation does not add runtime
rules: every completed contraction is proved convertible by the authored
rules, and every authored root is included on its exact diagonal.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace NativeRelatorConversionCompletion

open Presentation Presentation.Declaration NativeIndexedFamilies

variable {n m : Nat}

abbrev AuthoredConv (left right : Tower.Tm n) : Prop :=
  Conv IntrinsicRelator.rules.headEq left right IntrinsicRelator.rules.computation

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

def computation : RootComputation Tower.Head where
  step := Root
  rename := by intro n m rho left right root; exact root.rename rho
  substitute := by intro n m sigma left right root; exact root.substitute sigma

def rules : Rules Tower.Head :=
  { IntrinsicRelator.rules with computation := computation }

theorem Root.sound {left right : Tower.Tm n} (root : Root left right) :
    AuthoredConv left right := by
  cases root with
  | listNil ca =>
      exact .trans _ _ _ (listElim_congr (.refl _) (.refl _) (.refl _) (.refl _) (nilApp_congr ca))
        (.rel _ _ (.root (.declared ⟨.list (.nil _ _ _ _)⟩)))
  | listCons ca =>
      exact .trans _ _ _
        (listElim_congr (.refl _) (.refl _) (.refl _) (.refl _) (consApp_congr ca (.refl _) (.refl _)))
        (.rel _ _ (.root (.declared ⟨.list (.cons _ _ _ _ _ _)⟩)))
  | identity cy cw =>
      exact .trans _ _ _
        (idElim_congr (.refl _) (.refl _) (.refl _) (.refl _) cy
          (Conv.mapCompatible Tm.refl (fun step => .congRefl step) cw))
        (.rel _ _ (.root (.declared ⟨.list (.identity _ _ _ _)⟩)))
  | relNil ca cb cr cx cy =>
      exact .trans _ _ _
        (relElim_congr (.refl _) (.refl _) (.refl _) (.refl _) (.refl _) (.refl _) cx cy
          (nilRel_congr ca cb cr))
        (.rel _ _ (.root (.declared ⟨.rel (.nil _ _ _ _ _ _)⟩)))
  | relCons ca cb cr cx cy =>
      exact .trans _ _ _
        (relElim_congr (.refl _) (.refl _) (.refl _) (.refl _) (.refl _) (.refl _) cx cy
          (consRel_congr ca cb cr (.refl _) (.refl _) (.refl _) (.refl _) (.refl _) (.refl _)))
        (.rel _ _ (.root (.declared ⟨.rel (.cons _ _ _ _ _ _ _ _ _ _ _ _)⟩)))

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

theorem Root.target_unique {source first second : Tower.Tm n}
    (one : Root source first) (two : Root source second) : first = second := by
  cases one <;> cases two <;> rfl

theorem root_inclusion {left right : Tower.Tm n}
    (root : IntrinsicRelator.rules.computation.step left right) : Root left right := by
  cases root with
  | inherited impossible => exact impossible.elim
  | delta lookup => rw [IntrinsicRelator.rawSignature_valueOf_none] at lookup; cases lookup
  | declared evidence => obtain ⟨evidence⟩ := evidence; exact Root.of_iota evidence

def conservative : ConversionConservativeExtension IntrinsicRelator.rules rules where
  headEq_eq := rfl
  root_inclusion := root_inclusion
  root_sound := Root.sound

theorem conversion_iff (left right : Tower.Tm n) :
    AuthoredConv left right ↔ Conv rules.headEq left right rules.computation :=
  conservative.conversion_iff left right

namespace Examples

/-- The inner parameter has taken a different syntactic route to the same
outer parameter. No proof is inserted into the raw source term. -/
def mixedNil : Tower.Tm 4 :=
  Intrinsic.eliminateApp (.var 3) (.var 2) (.var 1) (.var 0)
    (Intrinsic.nilApp (.app (.lam (.var 0)) (.var 3)))

theorem mixed_nil_completed : Root mixedNil (.var 1) :=
  .listNil (.rel _ _ (.betaPi _ _))

theorem mixed_nil_convertible : AuthoredConv mixedNil (.var 1) :=
  mixed_nil_completed.sound

/-- The exact authored root matcher does not already identify the two
spellings. The completed contraction is not a replacement runtime rule. -/
theorem mixed_nil_not_authored_root {target : Tower.Tm 4} :
    ¬ IntrinsicRelator.rules.computation.step mixedNil target := by
  intro root
  cases root with
  | inherited impossible => exact impossible.elim
  | declared evidence =>
      obtain ⟨evidence⟩ := evidence
      cases evidence with
      | list evidence => cases evidence
      | rel evidence => cases evidence

theorem changed_nil_result_not_completed : ¬ Root mixedNil (.var 0) := by
  intro root
  have same := Root.target_unique mixed_nil_completed root
  cases same

end Examples

#print axioms Root.rename
#print axioms Root.substitute
#print axioms Root.sound
#print axioms Root.of_iota
#print axioms Root.target_unique
#print axioms conservative
#print axioms conversion_iff
#print axioms Examples.mixed_nil_completed
#print axioms Examples.mixed_nil_convertible
#print axioms Examples.mixed_nil_not_authored_root
#print axioms Examples.changed_nil_result_not_completed

end NativeRelatorConversionCompletion
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
