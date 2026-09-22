import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionCodeCongruence

/-!
# Compositional certificates for structural conversion

An endpoint-indexed certificate retains a finite code accepted by the existing
decoder. The operations below compute codes using the existing congruence
transformers. This packages their check theorems for dependent consumers; it
does not introduce a conversion relation or infer a certificate from endpoints.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace StructuralConversionCode

variable {Head : Type} {RootCode : Nat → Type} [DecidableEq Head]

structure Certificate (headEq : Head → Head → Prop) [DecidableRel headEq]
    (decodeRoot : {n : Nat} → RootCode n → Option (Tm Head n × Tm Head n))
    {n : Nat} (left right : Tm Head n) where
  code : Code Head RootCode n
  checked : code.check headEq decodeRoot left right = true

namespace Certificate

variable {headEq : Head → Head → Prop} [DecidableRel headEq]
variable {decodeRoot : {n : Nat} → RootCode n → Option (Tm Head n × Tm Head n)}
variable {n m : Nat}

def refl (term : Tm Head n) : Certificate headEq decodeRoot term term :=
  ⟨.refl term, Code.check_refl headEq decodeRoot term⟩

def symm {a b : Tm Head n} (first : Certificate headEq decodeRoot a b) :
    Certificate headEq decodeRoot b a :=
  ⟨.symm first.code, Code.check_symm headEq decodeRoot first.checked⟩

def trans {a b c : Tm Head n} (first : Certificate headEq decodeRoot a b)
    (second : Certificate headEq decodeRoot b c) : Certificate headEq decodeRoot a c :=
  ⟨.trans first.code second.code, Code.check_trans headEq decodeRoot first.checked second.checked⟩

def single {a b : Tm Head n} (step : StepCode Head RootCode n)
    (checked : step.check headEq decodeRoot a b = true) : Certificate headEq decodeRoot a b :=
  ⟨.single step, checked⟩

def pi {a a' : Tm Head n} {b b' : Tm Head (n + 1)}
    (first : Certificate headEq decodeRoot a a') (second : Certificate headEq decodeRoot b b') :
    Certificate headEq decodeRoot (.pi a b) (.pi a' b') :=
  ⟨Code.congPi a' b first.code second.code,
    Code.check_congPi headEq decodeRoot first.checked second.checked⟩

def sigma {a a' : Tm Head n} {b b' : Tm Head (n + 1)}
    (first : Certificate headEq decodeRoot a a') (second : Certificate headEq decodeRoot b b') :
    Certificate headEq decodeRoot (.sigma a b) (.sigma a' b') :=
  ⟨Code.congSigma a' b first.code second.code,
    Code.check_congSigma headEq decodeRoot first.checked second.checked⟩

def app {a a' b b' : Tm Head n}
    (first : Certificate headEq decodeRoot a a') (second : Certificate headEq decodeRoot b b') :
    Certificate headEq decodeRoot (.app a b) (.app a' b') :=
  ⟨Code.congApp a' b first.code second.code,
    Code.check_congApp headEq decodeRoot first.checked second.checked⟩

def pair {a a' b b' : Tm Head n}
    (first : Certificate headEq decodeRoot a a') (second : Certificate headEq decodeRoot b b') :
    Certificate headEq decodeRoot (.pair a b) (.pair a' b') :=
  ⟨Code.congPair a' b first.code second.code,
    Code.check_congPair headEq decodeRoot first.checked second.checked⟩

def lam {a b : Tm Head (n + 1)} (inner : Certificate headEq decodeRoot a b) :
    Certificate headEq decodeRoot (.lam a) (.lam b) :=
  ⟨Code.congLam inner.code, Code.check_congLam headEq decodeRoot inner.checked⟩

def fst {a b : Tm Head n} (inner : Certificate headEq decodeRoot a b) :
    Certificate headEq decodeRoot (.fst a) (.fst b) :=
  ⟨Code.congFst inner.code, Code.check_congFst headEq decodeRoot inner.checked⟩

def snd {a b : Tm Head n} (inner : Certificate headEq decodeRoot a b) :
    Certificate headEq decodeRoot (.snd a) (.snd b) :=
  ⟨Code.congSnd inner.code, Code.check_congSnd headEq decodeRoot inner.checked⟩

def reflTerm {a b : Tm Head n} (inner : Certificate headEq decodeRoot a b) :
    Certificate headEq decodeRoot (.refl a) (.refl b) :=
  ⟨Code.congRefl inner.code, Code.check_congRefl headEq decodeRoot inner.checked⟩

def id {a a' b b' c c' : Tm Head n}
    (carrier : Certificate headEq decodeRoot a a')
    (left : Certificate headEq decodeRoot b b') (right : Certificate headEq decodeRoot c c') :
    Certificate headEq decodeRoot (.id a b c) (.id a' b' c') :=
  ⟨Code.congId a' b b' c carrier.code left.code right.code,
    Code.check_congId headEq decodeRoot carrier.checked left.checked right.checked⟩

/-- Transport a previously supplied equality across two other supplied
conversions, retaining all three finite codes. -/
def transport {a b a' b' : Tm Head n}
    (original : Certificate headEq decodeRoot a b)
    (left : Certificate headEq decodeRoot a a') (right : Certificate headEq decodeRoot b b') :
    Certificate headEq decodeRoot a' b' := left.symm.trans (original.trans right)

end Certificate
end StructuralConversionCode
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
