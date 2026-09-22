import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Conversion.NativeParallelReceipt
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Conversion.NativeConversionSubstitution

/-!
# Executable binding action on native parallel receipts

Renaming and simultaneous parallel substitution act on the selected receipt
tree. Metadata guards use the existing finite-code substitution operation;
parallel substitution develops source and target images independently. The
output remains replayable by the unchanged authored conversion checker.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeParallelReceipt

open Presentation NativeIndexedFamilies NativeCompletedRootCertificate

def renameCertificate {n m : Nat} (rho : Ren n m) {left right : Tower.Tm n}
    (certificate : Certificate left right) :
    Certificate (rename rho left) (rename rho right) :=
  ⟨NativeRelatorConversionChecking.rename rho certificate.code,
    NativeRelatorConversionChecking.check_rename rho certificate.code certificate.checked⟩

def substituteCertificate {n m : Nat} (sigma : Sub Tower.Head n m) {left right : Tower.Tm n}
    (certificate : Certificate left right) :
    Certificate (subst sigma left) (subst sigma right) :=
  ⟨NativeRelatorConversionChecking.substitute sigma certificate.code,
    NativeRelatorConversionChecking.check_substitute sigma certificate.code certificate.checked⟩

/-- Renaming retains each metadata coherence derivation and all five
native contraction shapes. -/
def renameReceipt {n m : Nat} (rho : Ren n m) {source target : Tower.Tm n} :
    Receipt source target → Receipt (rename rho source) (rename rho target)
  | .var _ => .var _
  | .const _ => .const _
  | .head _ => .head _
  | .headRel equality => .headRel equality
  | .pi domain codomain => .pi (renameReceipt rho domain) (renameReceipt (liftRen rho) codomain)
  | .sigma domain codomain =>
      .sigma (renameReceipt rho domain) (renameReceipt (liftRen rho) codomain)
  | .id carrier left right => .id (renameReceipt rho carrier) (renameReceipt rho left) (renameReceipt rho right)
  | .lam body => .lam (renameReceipt (liftRen rho) body)
  | .app function argument => .app (renameReceipt rho function) (renameReceipt rho argument)
  | .pair first second => .pair (renameReceipt rho first) (renameReceipt rho second)
  | .fst inner => .fst (renameReceipt rho inner)
  | .snd inner => .snd (renameReceipt rho inner)
  | .refl term => .refl (renameReceipt rho term)
  | .betaPi body argument => by
      simpa only [rename, rename_inst0] using
        (Receipt.betaPi (renameReceipt (liftRen rho) body) (renameReceipt rho argument))
  | .betaSigmaFst first second => .betaSigmaFst (renameReceipt rho first) (renameReceipt rho second)
  | .betaSigmaSnd first second => .betaSigmaSnd (renameReceipt rho first) (renameReceipt rho second)
  | .listNil ca a p z s =>
      .listNil (renameCertificate rho ca)
        (renameReceipt rho a) (renameReceipt rho p) (renameReceipt rho z) (renameReceipt rho s)
  | .listCons ca a p z s h t =>
      .listCons (renameCertificate rho ca)
        (renameReceipt rho a) (renameReceipt rho p) (renameReceipt rho z) (renameReceipt rho s)
        (renameReceipt rho h) (renameReceipt rho t)
  | .identity cy cw a x p d y witness =>
      .identity (renameCertificate rho cy) (renameCertificate rho cw)
        (renameReceipt rho a) (renameReceipt rho x) (renameReceipt rho p)
        (renameReceipt rho d) (renameReceipt rho y) (renameReceipt rho witness)
  | .relNil ca cb cr cx cy a b r p z s xs ys =>
      .relNil (renameCertificate rho ca) (renameCertificate rho cb) (renameCertificate rho cr)
        (renameCertificate rho cx) (renameCertificate rho cy)
        (renameReceipt rho a) (renameReceipt rho b) (renameReceipt rho r) (renameReceipt rho p)
        (renameReceipt rho z) (renameReceipt rho s) (renameReceipt rho xs) (renameReceipt rho ys)
  | .relCons ca cb cr cx cy a b r p z s xs ys h k t u he te =>
      .relCons (renameCertificate rho ca) (renameCertificate rho cb) (renameCertificate rho cr)
        (renameCertificate rho cx) (renameCertificate rho cy)
        (renameReceipt rho a) (renameReceipt rho b) (renameReceipt rho r) (renameReceipt rho p)
        (renameReceipt rho z) (renameReceipt rho s) (renameReceipt rho xs) (renameReceipt rho ys)
        (renameReceipt rho h) (renameReceipt rho k) (renameReceipt rho t) (renameReceipt rho u)
        (renameReceipt rho he) (renameReceipt rho te)

/-- The new binder remains variable zero, and every older replacement is
weakened before its parallel development is reused. -/
def liftArguments {n m : Nat} {source target : Sub Tower.Head n m}
    (arguments : ∀ i, Receipt (source i) (target i)) :
    ∀ i, Receipt (liftSub source i) (liftSub target i) := by
  intro i
  refine Fin.cases ?_ ?_ i
  · exact .var 0
  · intro prior
    exact renameReceipt wk (arguments prior)

/-- Simultaneous parallel substitution preserves all five native branches. The
authored coherence guards are transported, not recomputed or erased. -/
def substituteReceipt {n m : Nat} {sourceSub targetSub : Sub Tower.Head n m}
    (arguments : ∀ i, Receipt (sourceSub i) (targetSub i))
    {source target : Tower.Tm n} :
    Receipt source target → Receipt (subst sourceSub source) (subst targetSub target)
  | .var index => arguments index
  | .const _ => .const _
  | .head _ => .head _
  | .headRel equality => .headRel equality
  | .pi domain codomain =>
      .pi (substituteReceipt arguments domain) (substituteReceipt (liftArguments arguments) codomain)
  | .sigma domain codomain =>
      .sigma (substituteReceipt arguments domain)
        (substituteReceipt (liftArguments arguments) codomain)
  | .id carrier left right =>
      .id (substituteReceipt arguments carrier) (substituteReceipt arguments left)
        (substituteReceipt arguments right)
  | .lam body => .lam (substituteReceipt (liftArguments arguments) body)
  | .app function argument => .app (substituteReceipt arguments function) (substituteReceipt arguments argument)
  | .pair first second => .pair (substituteReceipt arguments first) (substituteReceipt arguments second)
  | .fst inner => .fst (substituteReceipt arguments inner)
  | .snd inner => .snd (substituteReceipt arguments inner)
  | .refl term => .refl (substituteReceipt arguments term)
  | .betaPi body argument => by
      simpa only [subst, subst_inst0] using
        (Receipt.betaPi (substituteReceipt (liftArguments arguments) body)
          (substituteReceipt arguments argument))
  | .betaSigmaFst first second =>
      .betaSigmaFst (substituteReceipt arguments first) (substituteReceipt arguments second)
  | .betaSigmaSnd first second =>
      .betaSigmaSnd (substituteReceipt arguments first) (substituteReceipt arguments second)
  | .listNil ca a p z s =>
      .listNil (substituteCertificate sourceSub ca)
        (substituteReceipt arguments a) (substituteReceipt arguments p)
        (substituteReceipt arguments z) (substituteReceipt arguments s)
  | .listCons ca a p z s h t =>
      .listCons (substituteCertificate sourceSub ca)
        (substituteReceipt arguments a) (substituteReceipt arguments p)
        (substituteReceipt arguments z) (substituteReceipt arguments s)
        (substituteReceipt arguments h) (substituteReceipt arguments t)
  | .identity cy cw a x p d y witness =>
      .identity (substituteCertificate sourceSub cy) (substituteCertificate sourceSub cw)
        (substituteReceipt arguments a) (substituteReceipt arguments x)
        (substituteReceipt arguments p) (substituteReceipt arguments d)
        (substituteReceipt arguments y) (substituteReceipt arguments witness)
  | .relNil ca cb cr cx cy a b r p z s xs ys =>
      .relNil (substituteCertificate sourceSub ca) (substituteCertificate sourceSub cb) (substituteCertificate sourceSub cr)
        (substituteCertificate sourceSub cx) (substituteCertificate sourceSub cy)
        (substituteReceipt arguments a) (substituteReceipt arguments b)
        (substituteReceipt arguments r) (substituteReceipt arguments p)
        (substituteReceipt arguments z) (substituteReceipt arguments s)
        (substituteReceipt arguments xs) (substituteReceipt arguments ys)
  | .relCons ca cb cr cx cy a b r p z s xs ys h k t u he te =>
      .relCons (substituteCertificate sourceSub ca) (substituteCertificate sourceSub cb) (substituteCertificate sourceSub cr)
        (substituteCertificate sourceSub cx) (substituteCertificate sourceSub cy)
        (substituteReceipt arguments a) (substituteReceipt arguments b)
        (substituteReceipt arguments r) (substituteReceipt arguments p)
        (substituteReceipt arguments z) (substituteReceipt arguments s)
        (substituteReceipt arguments xs) (substituteReceipt arguments ys)
        (substituteReceipt arguments h) (substituteReceipt arguments k)
        (substituteReceipt arguments t) (substituteReceipt arguments u)
        (substituteReceipt arguments he) (substituteReceipt arguments te)

/-- Binder instantiation develops the substituted argument and the body
together, including any completed native root beneath that binder. -/
def instantiateReceipt {n : Nat} {argument argument' : Tower.Tm n}
    {body body' : Tower.Tm (n + 1)} (argumentStep : Receipt argument argument')
    (bodyStep : Receipt body body') :
    Receipt (inst0 argument body) (inst0 argument' body') := by
  apply substituteReceipt (sourceSub := subst0 argument) (targetSub := subst0 argument') _ bodyStep
  intro i
  refine Fin.cases ?_ ?_ i
  · exact argumentStep
  · intro prior
    exact .var prior

#print axioms renameReceipt
#print axioms substituteReceipt
#print axioms instantiateReceipt

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeParallelReceipt
