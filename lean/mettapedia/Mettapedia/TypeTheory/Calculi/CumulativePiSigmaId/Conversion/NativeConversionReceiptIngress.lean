import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Conversion.NativeParallelReceiptPaths
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Conversion.NativeConversionPaths

/-!
# Checked authored conversion enters native parallel paths

Every accepted original step code computes a native parallel receipt.
Congruence positions and binder scopes are read from the supplied code;
native roots retain their original arguments and use reflexive metadata
certificates. The resulting graph prefunctor maps the existing checked
symmetric path, preserving its selected edges and orientations. Joining that
path computes two directed continuations, without searching for conversion.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeParallelReceipt

open Presentation NativeIndexedFamilies StructuralConversionCode

/-- The original authored roots embed as completed parallel contractions with
exact metadata. No root is inferred from its endpoints. -/
def rootReceipt {n : Nat} (code : NativeRelatorRootConversionCode.Code n)
    {left right : Tower.Tm n}
    (decoded : NativeRelatorRootConversionCode.decode code = some (left, right)) :
    Receipt left right := by
  cases code with
  | indexed code =>
      cases code with
      | nil a p z s =>
          cases Option.some.inj decoded
          exact .listNil (.refl _) (Receipt.reflexive a) (Receipt.reflexive p)
            (Receipt.reflexive _) (Receipt.reflexive s)
      | cons a p z s h t =>
          cases Option.some.inj decoded
          exact .listCons (.refl _) (Receipt.reflexive a) (Receipt.reflexive p)
            (Receipt.reflexive z) (Receipt.reflexive s) (Receipt.reflexive h) (Receipt.reflexive t)
      | identity a x p d =>
          cases Option.some.inj decoded
          exact .identity (.refl _) (.refl _) (Receipt.reflexive a) (Receipt.reflexive x)
            (Receipt.reflexive p) (Receipt.reflexive _) (Receipt.reflexive x) (Receipt.reflexive x)
  | relNil a b r p z s =>
      cases Option.some.inj decoded
      exact .relNil (.refl _) (.refl _) (.refl _) (.refl _) (.refl _)
        (Receipt.reflexive a) (Receipt.reflexive b) (Receipt.reflexive r)
        (Receipt.reflexive p) (Receipt.reflexive _) (Receipt.reflexive s)
        (Receipt.reflexive _) (Receipt.reflexive _)
  | relCons a b r p z s h k t u he te =>
      cases Option.some.inj decoded
      exact .relCons (.refl _) (.refl _) (.refl _) (.refl _) (.refl _)
        (Receipt.reflexive a) (Receipt.reflexive b) (Receipt.reflexive r)
        (Receipt.reflexive p) (Receipt.reflexive z) (Receipt.reflexive s)
        (Receipt.reflexive _) (Receipt.reflexive _)
        (Receipt.reflexive h) (Receipt.reflexive k) (Receipt.reflexive t) (Receipt.reflexive u)
        (Receipt.reflexive he) (Receipt.reflexive te)

private def mapReceipt {n m : Nat}
    (wrap : Tower.Tm n → Tower.Tm m)
    (preserves : {a b : Tower.Tm n} → Receipt a b → Receipt (wrap a) (wrap b))
    (endpoints : Option (Tower.Tm n × Tower.Tm n))
    (input : {a b : Tower.Tm n} → endpoints = some (a, b) → Receipt a b)
    {left right : Tower.Tm m}
    (decoded : mapEndpoints wrap endpoints = some (left, right)) :
    Receipt left right := by
  cases endpoints with
  | none => simp [mapEndpoints] at decoded
  | some endpoints =>
      obtain ⟨source, target⟩ := endpoints
      cases Option.some.inj decoded
      exact preserves (input rfl)

/-- Interpret the actual selected step, including its congruence position. -/
def stepReceipt {n : Nat} (code : NativeRelatorConversionChecking.StepCode n)
    {left right : Tower.Tm n}
    (decoded : code.decode Tower.HeadEq NativeRelatorRootConversionCode.decode = some (left, right)) :
    Receipt left right :=
  match code with
  | .betaPi body argument => by
      cases Option.some.inj decoded
      exact .betaPi (Receipt.reflexive body) (Receipt.reflexive argument)
  | .betaSigmaFst first second => by
      cases Option.some.inj decoded
      exact .betaSigmaFst (Receipt.reflexive _) (Receipt.reflexive second)
  | .betaSigmaSnd first second => by
      cases Option.some.inj decoded
      exact .betaSigmaSnd (Receipt.reflexive first) (Receipt.reflexive _)
  | .head first second => by
      simp only [StepCode.decode] at decoded
      split at decoded
      · rename_i equality
        cases Option.some.inj decoded
        exact .headRel equality
      · cases decoded
  | .root code => rootReceipt code decoded
  | .congPiDom code codomain =>
      mapReceipt (fun domain => .pi domain codomain) (fun inner => .pi inner (Receipt.reflexive codomain))
        (code.decode Tower.HeadEq NativeRelatorRootConversionCode.decode) (stepReceipt code) decoded
  | .congPiCod domain code =>
      mapReceipt (.pi domain) (fun inner => .pi (Receipt.reflexive domain) inner)
        (code.decode Tower.HeadEq NativeRelatorRootConversionCode.decode) (stepReceipt code) decoded
  | .congSigmaDom code codomain =>
      mapReceipt (fun domain => .sigma domain codomain) (fun inner => .sigma inner (Receipt.reflexive codomain))
        (code.decode Tower.HeadEq NativeRelatorRootConversionCode.decode) (stepReceipt code) decoded
  | .congSigmaCod domain code =>
      mapReceipt (.sigma domain) (fun inner => .sigma (Receipt.reflexive domain) inner)
        (code.decode Tower.HeadEq NativeRelatorRootConversionCode.decode) (stepReceipt code) decoded
  | .congIdTy code first second =>
      mapReceipt (fun carrier => .id carrier first second) (fun inner => .id inner (Receipt.reflexive first) (Receipt.reflexive second))
        (code.decode Tower.HeadEq NativeRelatorRootConversionCode.decode) (stepReceipt code) decoded
  | .congIdLeft carrier code second =>
      mapReceipt (fun first => .id carrier first second) (fun inner => .id (Receipt.reflexive carrier) inner (Receipt.reflexive second))
        (code.decode Tower.HeadEq NativeRelatorRootConversionCode.decode) (stepReceipt code) decoded
  | .congIdRight carrier first code =>
      mapReceipt (.id carrier first) (fun inner => .id (Receipt.reflexive carrier) (Receipt.reflexive first) inner)
        (code.decode Tower.HeadEq NativeRelatorRootConversionCode.decode) (stepReceipt code) decoded
  | .congLam code =>
      mapReceipt (.lam) (fun inner => .lam inner)
        (code.decode Tower.HeadEq NativeRelatorRootConversionCode.decode) (stepReceipt code) decoded
  | .congAppFun code argument =>
      mapReceipt (fun function => .app function argument) (fun inner => .app inner (Receipt.reflexive argument))
        (code.decode Tower.HeadEq NativeRelatorRootConversionCode.decode) (stepReceipt code) decoded
  | .congAppArg function code =>
      mapReceipt (.app function) (fun inner => .app (Receipt.reflexive function) inner)
        (code.decode Tower.HeadEq NativeRelatorRootConversionCode.decode) (stepReceipt code) decoded
  | .congPairFst code second =>
      mapReceipt (fun first => .pair first second) (fun inner => .pair inner (Receipt.reflexive second))
        (code.decode Tower.HeadEq NativeRelatorRootConversionCode.decode) (stepReceipt code) decoded
  | .congPairSnd first code =>
      mapReceipt (.pair first) (fun inner => .pair (Receipt.reflexive first) inner)
        (code.decode Tower.HeadEq NativeRelatorRootConversionCode.decode) (stepReceipt code) decoded
  | .congFst code =>
      mapReceipt (.fst) (fun inner => .fst inner)
        (code.decode Tower.HeadEq NativeRelatorRootConversionCode.decode) (stepReceipt code) decoded
  | .congSnd code =>
      mapReceipt (.snd) (fun inner => .snd inner)
        (code.decode Tower.HeadEq NativeRelatorRootConversionCode.decode) (stepReceipt code) decoded
  | .congRefl code =>
      mapReceipt (.refl) (fun inner => .refl inner)
        (code.decode Tower.HeadEq NativeRelatorRootConversionCode.decode) (stepReceipt code) decoded

def stepPrefunctor (n : Nat) : NativeConversionPaths.Vertex n ⥤q ReceiptGraph n where
  obj term := term
  map selected := stepReceipt selected.val selected.property

def ingressPath {n : Nat} {left right : Tower.Tm n} (path : NativeConversionPaths.Zigzag left right) :
    SymmetricPath left right :=
  (stepPrefunctor n).symmetrify.mapPath path

def certificatePath {n : Nat} {left right : Tower.Tm n}
    (certificate : NativeCompletedRootCertificate.Certificate left right) : SymmetricPath left right :=
  ingressPath (certificate.code.toZigzag Tower.HeadEq NativeRelatorRootConversionCode.decode
    (of_decide_eq_true certificate.checked))

def joinCertificate {n : Nat} {left right : Tower.Tm n}
    (certificate : NativeCompletedRootCertificate.Certificate left right) :
    Mettapedia.Logic.Relation.PathConfluence.Join (V := ReceiptGraph n) left right :=
  joinSymmetricPath (certificatePath certificate)


theorem ingressPath_length {n : Nat} {left right : Tower.Tm n}
    (path : NativeConversionPaths.Zigzag left right) :
    (ingressPath path).length = path.length :=
  Mettapedia.Logic.Relation.PathConfluence.mapPath_length (stepPrefunctor n).symmetrify path

theorem ingressPath_directions {n : Nat} {left right : Tower.Tm n}
    (path : NativeConversionPaths.Zigzag left right) :
    Mettapedia.Logic.Relation.PathConfluence.directions (V := ReceiptGraph n) (ingressPath path) =
      Mettapedia.Logic.Relation.PathConfluence.directions (V := NativeConversionPaths.Vertex n) path :=
  Mettapedia.Logic.Relation.PathConfluence.directions_map (stepPrefunctor n) path

theorem certificatePath_length {n : Nat} {left right : Tower.Tm n}
    (certificate : NativeCompletedRootCertificate.Certificate left right) :
    (certificatePath certificate).length = certificate.code.stepCount :=
  (ingressPath_length _).trans
    (Code.toZigzag_length Tower.HeadEq NativeRelatorRootConversionCode.decode certificate.code
      (of_decide_eq_true certificate.checked))

/-- The finite-code entry point accepts exactly what the original checker does. -/
def checkedJoin {n : Nat} (code : NativeRelatorConversionChecking.Code n)
    (left right : Tower.Tm n) :
    Option (Mettapedia.Logic.Relation.PathConfluence.Join (V := ReceiptGraph n) left right) :=
  if accepted : NativeRelatorConversionChecking.check code left right = true then
    some (joinCertificate ⟨code, accepted⟩)
  else none

theorem checkedJoin_domain {n : Nat} (code : NativeRelatorConversionChecking.Code n)
    (left right : Tower.Tm n) :
    (checkedJoin code left right).isSome = NativeRelatorConversionChecking.check code left right := by
  unfold checkedJoin
  split <;> simp_all

theorem joinCertificate_rechecks {n : Nat} {left right : Tower.Tm n}
    (certificate : NativeCompletedRootCertificate.Certificate left right) :
    NativeRelatorConversionChecking.check (replayPath (joinCertificate certificate).fromLeft).code
      left (joinCertificate certificate).common = true ∧
    NativeRelatorConversionChecking.check (replayPath (joinCertificate certificate).fromRight).code
      right (joinCertificate certificate).common = true :=
  ⟨(replayPath (joinCertificate certificate).fromLeft).checked,
    (replayPath (joinCertificate certificate).fromRight).checked⟩

#print axioms ingressPath_length
#print axioms ingressPath_directions
#print axioms certificatePath_length
#print axioms checkedJoin_domain
#print axioms joinCertificate_rechecks
#print axioms rootReceipt
#print axioms stepReceipt
#print axioms ingressPath
#print axioms joinCertificate

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeParallelReceipt
