import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionCertificate
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeRelatorConversionChecking
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Conversion.NativeRelatorConversionCompletion

/-!
# Checked replay of conversion-coherent native contractions

Each completed contraction computes an authored conversion certificate by
first aligning its duplicated metadata using the supplied finite certificates,
then applying the existing exact native root. All five root shapes are covered.
This is conservative proof replay, not a new runtime contraction rule.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeCompletedRootCertificate

open Presentation StructuralConversionCode NativeIndexedFamilies
open NativeRelatorConversionCompletion

abbrev Certificate {n : Nat} (left right : Tower.Tm n) :=
  StructuralConversionCode.Certificate Tower.HeadEq NativeRelatorRootConversionCode.decode left right

variable {n : Nat}

theorem sound {left right : Tower.Tm n} (certificate : Certificate left right) :
    AuthoredConv left right := NativeRelatorConversionChecking.check_sound certificate.checked

def nilApp {x0 x0' : Tower.Tm n}
    (c0 : Certificate x0 x0') :
    Certificate (Intrinsic.nilApp x0) (Intrinsic.nilApp x0') :=
  ((Certificate.refl _).app c0)

def consApp {x0 x1 x2 x0' x1' x2' : Tower.Tm n}
    (c0 : Certificate x0 x0')
    (c1 : Certificate x1 x1')
    (c2 : Certificate x2 x2') :
    Certificate (Intrinsic.consApp x0 x1 x2) (Intrinsic.consApp x0' x1' x2') :=
  ((((Certificate.refl _).app c0).app c1).app c2)

def listElim {x0 x1 x2 x3 x4 x0' x1' x2' x3' x4' : Tower.Tm n}
    (c0 : Certificate x0 x0')
    (c1 : Certificate x1 x1')
    (c2 : Certificate x2 x2')
    (c3 : Certificate x3 x3')
    (c4 : Certificate x4 x4') :
    Certificate (Intrinsic.eliminateApp x0 x1 x2 x3 x4) (Intrinsic.eliminateApp x0' x1' x2' x3' x4') :=
  ((((((Certificate.refl _).app c0).app c1).app c2).app c3).app c4)

def idElim {x0 x1 x2 x3 x4 x5 x0' x1' x2' x3' x4' x5' : Tower.Tm n}
    (c0 : Certificate x0 x0')
    (c1 : Certificate x1 x1')
    (c2 : Certificate x2 x2')
    (c3 : Certificate x3 x3')
    (c4 : Certificate x4 x4')
    (c5 : Certificate x5 x5') :
    Certificate (Intrinsic.identityEliminateApp x0 x1 x2 x3 x4 x5) (Intrinsic.identityEliminateApp x0' x1' x2' x3' x4' x5') :=
  (((((((Certificate.refl _).app c0).app c1).app c2).app c3).app c4).app c5)

def nilRel {x0 x1 x2 x0' x1' x2' : Tower.Tm n}
    (c0 : Certificate x0 x0')
    (c1 : Certificate x1 x1')
    (c2 : Certificate x2 x2') :
    Certificate (IntrinsicRelator.nilRelApp x0 x1 x2) (IntrinsicRelator.nilRelApp x0' x1' x2') :=
  ((((Certificate.refl _).app c0).app c1).app c2)

def consRel {x0 x1 x2 x3 x4 x5 x6 x7 x8 x0' x1' x2' x3' x4' x5' x6' x7' x8' : Tower.Tm n}
    (c0 : Certificate x0 x0')
    (c1 : Certificate x1 x1')
    (c2 : Certificate x2 x2')
    (c3 : Certificate x3 x3')
    (c4 : Certificate x4 x4')
    (c5 : Certificate x5 x5')
    (c6 : Certificate x6 x6')
    (c7 : Certificate x7 x7')
    (c8 : Certificate x8 x8') :
    Certificate (IntrinsicRelator.consRelApp x0 x1 x2 x3 x4 x5 x6 x7 x8) (IntrinsicRelator.consRelApp x0' x1' x2' x3' x4' x5' x6' x7' x8') :=
  ((((((((((Certificate.refl _).app c0).app c1).app c2).app c3).app c4).app c5).app c6).app c7).app c8)

def relElim {x0 x1 x2 x3 x4 x5 x6 x7 x8 x0' x1' x2' x3' x4' x5' x6' x7' x8' : Tower.Tm n}
    (c0 : Certificate x0 x0')
    (c1 : Certificate x1 x1')
    (c2 : Certificate x2 x2')
    (c3 : Certificate x3 x3')
    (c4 : Certificate x4 x4')
    (c5 : Certificate x5 x5')
    (c6 : Certificate x6 x6')
    (c7 : Certificate x7 x7')
    (c8 : Certificate x8 x8') :
    Certificate (IntrinsicRelator.eliminateApp x0 x1 x2 x3 x4 x5 x6 x7 x8) (IntrinsicRelator.eliminateApp x0' x1' x2' x3' x4' x5' x6' x7' x8') :=
  ((((((((((Certificate.refl _).app c0).app c1).app c2).app c3).app c4).app c5).app c6).app c7).app c8)

def listNil {a p z s innerA : Tower.Tm n} (coherent : Certificate innerA a) :
    Certificate (Intrinsic.eliminateApp a p z s (Intrinsic.nilApp innerA)) z :=
  (listElim (.refl _) (.refl _) (.refl _) (.refl _) (nilApp coherent)).trans
    ⟨.single (.root (.indexed (.nil a p z s))), decide_eq_true rfl⟩

def listCons {a p z s innerA h t : Tower.Tm n} (coherent : Certificate innerA a) :
    Certificate (Intrinsic.eliminateApp a p z s (Intrinsic.consApp innerA h t))
      (.app (.app (.app s h) t) (Intrinsic.eliminateApp a p z s t)) :=
  (listElim (.refl _) (.refl _) (.refl _) (.refl _)
    (consApp coherent (.refl _) (.refl _))).trans
      ⟨.single (.root (.indexed (.cons a p z s h t))), decide_eq_true rfl⟩

def identity {a x p d y witness : Tower.Tm n}
    (point : Certificate y x) (proofPoint : Certificate witness x) :
    Certificate (Intrinsic.identityEliminateApp a x p d y (.refl witness)) d :=
  (idElim (.refl _) (.refl _) (.refl _) (.refl _) point proofPoint.reflTerm).trans
    ⟨.single (.root (.indexed (.identity a x p d))), decide_eq_true rfl⟩

def relNil {a b r p z s xs ys innerA innerB innerR : Tower.Tm n}
    (ca : Certificate innerA a) (cb : Certificate innerB b) (cr : Certificate innerR r)
    (cx : Certificate xs (Intrinsic.nilApp a)) (cy : Certificate ys (Intrinsic.nilApp b)) :
    Certificate (IntrinsicRelator.eliminateApp a b r p z s xs ys
      (IntrinsicRelator.nilRelApp innerA innerB innerR)) z :=
  (relElim (.refl _) (.refl _) (.refl _) (.refl _) (.refl _) (.refl _) cx cy
    (nilRel ca cb cr)).trans
      ⟨.single (.root (.relNil a b r p z s)), decide_eq_true rfl⟩

def relCons {a b r p z s xs ys innerA innerB innerR h k t u he te : Tower.Tm n}
    (ca : Certificate innerA a) (cb : Certificate innerB b) (cr : Certificate innerR r)
    (cx : Certificate xs (Intrinsic.consApp a h t)) (cy : Certificate ys (Intrinsic.consApp b k u)) :
    Certificate (IntrinsicRelator.eliminateApp a b r p z s xs ys
      (IntrinsicRelator.consRelApp innerA innerB innerR h k t u he te))
      (.app (.app (.app (.app (.app (.app (.app s h) k) t) u) he) te)
        (IntrinsicRelator.eliminateApp a b r p z s t u te)) :=
  (relElim (.refl _) (.refl _) (.refl _) (.refl _) (.refl _) (.refl _) cx cy
    (consRel ca cb cr (.refl _) (.refl _) (.refl _) (.refl _) (.refl _) (.refl _))).trans
      ⟨.single (.root (.relCons a b r p z s h k t u he te)), decide_eq_true rfl⟩

namespace Controls

def identityBeta (term : Tower.Tm n) : Certificate (.app (.lam (.var 0)) term) term :=
  ⟨.single (.betaPi (.var 0) term), decide_eq_true rfl⟩

def mixedNilCertificate : Certificate Examples.mixedNil (.var 1) :=
  listNil (identityBeta (.var 3))

theorem mixed_nil_rechecks :
    NativeRelatorConversionChecking.check mixedNilCertificate.code Examples.mixedNil (.var 1) = true :=
  mixedNilCertificate.checked

theorem changed_nil_result_rejected :
    NativeRelatorConversionChecking.check mixedNilCertificate.code Examples.mixedNil (.var 0) = false := by
  decide +kernel

end Controls

#print axioms listNil
#print axioms listCons
#print axioms identity
#print axioms relNil
#print axioms relCons
#print axioms Controls.mixed_nil_rechecks
#print axioms Controls.changed_nil_result_rejected

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeCompletedRootCertificate
