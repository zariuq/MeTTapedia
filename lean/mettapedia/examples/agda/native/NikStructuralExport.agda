{-# OPTIONS --safe --without-K #-}
module NikStructuralExport where

-- Offline syntax export for the finite-level relevant Pi fragment.
-- Inferred annotations are untrusted input to the native checker.
-- Operator codes follow the structural signature's binding-aware wire codec.

open import Agda.Builtin.Reflection
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String; primStringAppend; primShowNat)
open import Agda.Builtin.Unit using (⊤; tt)

infixr 5 _++_
_++_ = primStringAppend
infixl 1 _>>=_
_>>=_ = bindTC

pair : String → String → String
pair a b = "[" ++ a ++ "," ++ b ++ "]"

args : List String → String
args [] = "0"
args (x ∷ xs) = pair x (args xs)

operator : String → List String → String
operator tag xs = pair "1" (pair tag (args xs))

variableCode : Nat → String
variableCode n = pair "0" (primShowNat n)

sortCode : Nat → String
sortCode n = operator "11" (operator (pair "14" (primShowNat n)) [] ∷ [])

universeCode : Nat → String
universeCode n = operator "8" (sortCode n ∷ [])

appendArg : List (Arg Term) → Arg Term → List (Arg Term)
appendArg [] a = a ∷ []
appendArg (x ∷ xs) a = x ∷ appendArg xs a

outside : ∀ {a} {A : Set a} → String → Term → TC A
outside message t = typeError (strErr ("NIK structural export: " ++ message) ∷ termErr t ∷ [])

exhausted : ∀ {a} {A : Set a} → TC A
exhausted = typeError (strErr "NIK structural export: export recursion budget exhausted" ∷ [])

mutual
  exportType : Nat → Term → TC String
  exportType zero A = exhausted
  exportType (suc fuel) A = inferType A >>= reduce >>= exportAtSort fuel A

  exportAtSort : Nat → Term → Term → TC String
  exportAtSort fuel A (agda-sort (lit level)) =
    exportTerm fuel A (agda-sort (lit level)) >>= λ code →
    returnTC (operator "10" (sortCode level ∷ code ∷ []))
  exportAtSort fuel A inferred = outside "type is not in a finite Set level: " inferred

  exportTerm : Nat → Term → Term → TC String
  exportTerm zero t A = exhausted
  exportTerm (suc fuel) (var index []) A = returnTC (variableCode index)
  exportTerm (suc fuel) (var index spine@(_ ∷ _)) A =
    exportSpine fuel index [] spine >>= λ code →
    returnTC (operator "4" (variableCode index ∷ code ∷ []))
  exportTerm (suc fuel) (lam visible (abs binderName body)) A =
    reduce A >>= exportLambda fuel binderName body
  exportTerm (suc fuel) (pi domain@(arg (arg-info visible (modality relevant quantity-ω)) A) (abs binderName B)) expected =
    exportType fuel A >>= λ domainCode →
    extendContext binderName domain (exportType fuel B) >>= λ codomainCode →
    returnTC (operator "2" (domainCode ∷ codomainCode ∷ []))
  exportTerm (suc fuel) (agda-sort (lit level)) A = returnTC (universeCode level)
  exportTerm (suc fuel) t A = outside "unsupported term or modality: " t

  exportLambda : Nat → String → Term → Term → TC String
  exportLambda fuel binderName body (pi domain@(arg (arg-info visible (modality relevant quantity-ω)) A) (abs _ B)) =
    extendContext binderName domain (exportTerm fuel body B) >>= λ code →
    returnTC (operator "0" (code ∷ []))
  exportLambda fuel binderName body A = outside "lambda requires an explicit relevant Pi annotation: " A

  exportSpine : Nat → Nat → List (Arg Term) → List (Arg Term) → TC String
  exportSpine zero index prefix remaining = exhausted
  exportSpine (suc fuel) index prefix [] = returnTC (operator "20" [])
  exportSpine (suc fuel) index prefix (argument@(arg (arg-info visible (modality relevant quantity-ω)) t) ∷ remaining) =
    inferType (var index prefix) >>= reduce >>= exportArgument fuel index prefix argument remaining
  exportSpine (suc fuel) index prefix _ = outside "unsupported argument modality: " (var index prefix)

  exportArgument : Nat → Nat → List (Arg Term) → Arg Term → List (Arg Term) → Term → TC String
  exportArgument fuel index prefix argument@(arg _ t) remaining
      (pi (arg (arg-info visible (modality relevant quantity-ω)) A) _) =
    exportTerm fuel t A >>= λ termCode →
    exportSpine fuel index (appendArg prefix argument) remaining >>= λ restCode →
    returnTC (operator "21" (operator "18" (termCode ∷ []) ∷ restCode ∷ []))
  exportArgument fuel index prefix argument remaining A = outside "application requires a relevant Pi head: " A

emit : Nat → Term → Term → TC ⊤
emit fuel A t =
  exportType fuel A >>= λ typeCode →
  exportTerm fuel t A >>= λ termCode →
  debugPrint "nik.structural" 0
    (strErr ("NIK-AGDA-STRUCTURAL: {\"profile\":\"finite-set-relevant-pi-v1\",\"scope\":0,\"term\":"
      ++ termCode ++ ",\"type\":" ++ typeCode ++ "}") ∷ [])

emitClosed : Nat → Telescope → Term → Term → TC ⊤
emitClosed fuel [] A t = checkType t A >>= emit fuel A
emitClosed fuel (_ ∷ _) A t = outside "export requires a closed expression: " t

macro
  nikStructural : Nat → Term → Term → Term → TC ⊤
  nikStructural fuel A t hole = getContext >>= λ context →
    emitClosed fuel context A t >>= λ _ → unify hole (con (quote tt) [])
