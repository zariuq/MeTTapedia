import Mathlib.Algebra.Order.Quantale
import Mettapedia.Algebra.QuantaleWeakness
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.MultiStep
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.RhoOpening
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.SemanticSubstitution
import Mettapedia.Languages.MeTTa.HE.ExecutableBoundary

/-!
# Rhometta Reduction Layer

This file adds the smallest Lean semantics layer needed to talk about
Rhometta's deferred MeTTa-at-COMM behavior without forking the rho reducer.

The core design is:

- reuse the ordinary rho reduction relation as a base case
- add one explicit `rho:eval-payload` COMM rule
- quantify that rule over certified HE evaluation results
- expose reachability lemmas showing that every certified HE result induces a
  corresponding Rhometta branch

This makes branch-dropping inexpressible at the semantic rule level.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.RhometaReduction

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Reduction
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore

/-- Structural unary encoding for naturals inside rho-side inert syntax. -/
def natToPattern : Nat → Pattern
  | 0 => .apply "NatZ" []
  | n + 1 => .apply "NatS" [natToPattern n]

/-- Partial inverse of `natToPattern`. -/
def patternToNat? : Pattern → Option Nat
  | .apply "NatZ" [] => some 0
  | .apply "NatS" [p] => (patternToNat? p).map Nat.succ
  | _ => none

theorem patternToNat_natToPattern (n : Nat) :
    patternToNat? (natToPattern n) = some n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [natToPattern, patternToNat?, ih]

private theorem natToPattern_of_patternToNat?_eq_some :
    ∀ {p : Pattern} {n : Nat}, patternToNat? p = some n -> natToPattern n = p
  | .apply "NatZ" [], 0, h => by
      simp [patternToNat?] at h
      cases h
      rfl
  | .apply "NatZ" [], n + 1, h => by
      simp [patternToNat?] at h
  | .apply "NatS" [p], 0, h => by
      simp [patternToNat?] at h
  | .apply "NatS" [p], n + 1, h => by
      simp [patternToNat?] at h
      simp [natToPattern, natToPattern_of_patternToNat?_eq_some h]
  | .bvar _, n, h => by
      simp [patternToNat?] at h
  | .fvar _, n, h => by
      simp [patternToNat?] at h
  | .apply f args, n, h => by
      by_cases hNatZ : f = "NatZ"
      · subst hNatZ
        cases args with
        | nil =>
            cases n <;> simp [patternToNat?, natToPattern] at h ⊢
        | cons a as =>
            simp [patternToNat?] at h
      · by_cases hNatS : f = "NatS"
        · subst hNatS
          cases args with
          | nil =>
              simp [patternToNat?] at h
          | cons a as =>
              cases as with
              | nil =>
                  cases n with
                  | zero =>
                      simp [patternToNat?] at h
                  | succ n =>
                      simp [patternToNat?] at h
                      simp [natToPattern, natToPattern_of_patternToNat?_eq_some h]
              | cons b bs =>
                  simp [patternToNat?] at h
        · simp [patternToNat?, hNatZ, hNatS] at h
  | .lambda _ _, n, h => by
      simp [patternToNat?] at h
  | .multiLambda _ _ _, n, h => by
      simp [patternToNat?] at h
  | .subst _ _, n, h => by
      simp [patternToNat?] at h
  | .collection _ _ _, n, h => by
      simp [patternToNat?] at h

/-- Structural embedding of HE grounded values into inert rho-side syntax. -/
def groundedValueToPattern : GroundedValue → Pattern
  | .int (.ofNat n) => .apply "HEIntOfNat" [natToPattern n]
  | .int (.negSucc n) => .apply "HEIntNegSucc" [natToPattern n]
  | .string s => .apply "HEString" [.fvar s]
  | .bool true => .apply "HEBoolTrue" []
  | .bool false => .apply "HEBoolFalse" []
  | .custom ty data => .apply "HECustom" [.fvar ty, .fvar data]

/-- Structural embedding of HE atoms into inert rho-side syntax. -/
def atomToPattern : Atom → Pattern
  | .symbol s => .apply "HESymbol" [.fvar s]
  | .var v => .apply "HEVar" [.fvar v]
  | .grounded g => groundedValueToPattern g
  | .expression es => .apply "HEExpr" (es.map atomToPattern)

/-- Partial inverse of the grounded-value embedding. -/
def patternToGroundedValue? : Pattern → Option GroundedValue
  | .apply "HEIntOfNat" [p] =>
      (patternToNat? p).map (fun n => .int (.ofNat n))
  | .apply "HEIntNegSucc" [p] =>
      (patternToNat? p).map (fun n => .int (.negSucc n))
  | .apply "HEString" [.fvar s] => some (.string s)
  | .apply "HEBoolTrue" [] => some (.bool true)
  | .apply "HEBoolFalse" [] => some (.bool false)
  | .apply "HECustom" [.fvar ty, .fvar data] => some (.custom ty data)
  | _ => none

mutual

/-- Partial inverse of `atomToPattern` for the Rhometta inert embedding. -/
def patternToAtom? : Pattern → Option Atom
  | .apply "HESymbol" [.fvar s] => some (.symbol s)
  | .apply "HEVar" [.fvar v] => some (.var v)
  | p@(.apply "HEIntOfNat" _) => patternToGroundedValue? p |>.map .grounded
  | p@(.apply "HEIntNegSucc" _) => patternToGroundedValue? p |>.map .grounded
  | p@(.apply "HEString" _) => patternToGroundedValue? p |>.map .grounded
  | p@(.apply "HEBoolTrue" _) => patternToGroundedValue? p |>.map .grounded
  | p@(.apply "HEBoolFalse" _) => patternToGroundedValue? p |>.map .grounded
  | p@(.apply "HECustom" _) => patternToGroundedValue? p |>.map .grounded
  | .apply "HEExpr" ps => (patternToAtoms? ps).map .expression
  | _ => none

/-- Partial inverse on lists, aligned with `List.map atomToPattern`. -/
def patternToAtoms? : List Pattern → Option (List Atom)
  | [] => some []
  | p :: ps => do
      let a <- patternToAtom? p
      let as <- patternToAtoms? ps
      pure (a :: as)

end

theorem patternToGroundedValue_groundedValueToPattern (g : GroundedValue) :
    patternToGroundedValue? (groundedValueToPattern g) = some g := by
  cases g with
  | int i =>
      cases i using Int.rec with
      | ofNat n =>
          simp [groundedValueToPattern, patternToGroundedValue?,
            patternToNat_natToPattern]
      | negSucc n =>
          simp [groundedValueToPattern, patternToGroundedValue?,
            patternToNat_natToPattern]
  | string s =>
      simp [groundedValueToPattern, patternToGroundedValue?]
  | bool b =>
      cases b <;> simp [groundedValueToPattern, patternToGroundedValue?]
  | custom ty data =>
      simp [groundedValueToPattern, patternToGroundedValue?]

private theorem groundedValueToPattern_of_patternToGroundedValue?_eq_some :
    ∀ {p : Pattern} {g : GroundedValue},
      patternToGroundedValue? p = some g -> groundedValueToPattern g = p
  | .apply "HEIntOfNat" [p], .int (.ofNat n), h => by
      simp [patternToGroundedValue?] at h
      simp [groundedValueToPattern, natToPattern_of_patternToNat?_eq_some h]
  | .apply "HEIntOfNat" [p], .int (.negSucc n), h => by
      simp [patternToGroundedValue?] at h
  | .apply "HEIntOfNat" [p], .string s, h => by
      simp [patternToGroundedValue?] at h
  | .apply "HEIntOfNat" [p], .bool b, h => by
      cases b <;> simp [patternToGroundedValue?] at h
  | .apply "HEIntOfNat" [p], .custom ty data, h => by
      simp [patternToGroundedValue?] at h
  | .apply "HEIntNegSucc" [p], .int (.ofNat n), h => by
      simp [patternToGroundedValue?] at h
  | .apply "HEIntNegSucc" [p], .int (.negSucc n), h => by
      simp [patternToGroundedValue?] at h
      simp [groundedValueToPattern, natToPattern_of_patternToNat?_eq_some h]
  | .apply "HEIntNegSucc" [p], .string s, h => by
      simp [patternToGroundedValue?] at h
  | .apply "HEIntNegSucc" [p], .bool b, h => by
      cases b <;> simp [patternToGroundedValue?] at h
  | .apply "HEIntNegSucc" [p], .custom ty data, h => by
      simp [patternToGroundedValue?] at h
  | .apply "HEString" [.fvar s], .string t, h => by
      simp [patternToGroundedValue?, groundedValueToPattern] at h ⊢
      cases h
      rfl
  | .apply "HEString" [.fvar s], .int i, h => by
      cases i using Int.rec <;> simp [patternToGroundedValue?] at h
  | .apply "HEString" [.fvar s], .bool b, h => by
      cases b <;> simp [patternToGroundedValue?] at h
  | .apply "HEString" [.fvar s], .custom ty data, h => by
      simp [patternToGroundedValue?] at h
  | .apply "HEBoolTrue" [], .bool true, h => by
      simp [patternToGroundedValue?, groundedValueToPattern] at h ⊢
  | .apply "HEBoolTrue" [], .bool false, h => by
      simp [patternToGroundedValue?] at h
  | .apply "HEBoolTrue" [], .int i, h => by
      cases i using Int.rec <;> simp [patternToGroundedValue?] at h
  | .apply "HEBoolTrue" [], .string s, h => by
      simp [patternToGroundedValue?] at h
  | .apply "HEBoolTrue" [], .custom ty data, h => by
      simp [patternToGroundedValue?] at h
  | .apply "HEBoolFalse" [], .bool false, h => by
      simp [patternToGroundedValue?, groundedValueToPattern] at h ⊢
  | .apply "HEBoolFalse" [], .bool true, h => by
      simp [patternToGroundedValue?] at h
  | .apply "HEBoolFalse" [], .int i, h => by
      cases i using Int.rec <;> simp [patternToGroundedValue?] at h
  | .apply "HEBoolFalse" [], .string s, h => by
      simp [patternToGroundedValue?] at h
  | .apply "HEBoolFalse" [], .custom ty data, h => by
      simp [patternToGroundedValue?] at h
  | .apply "HECustom" [.fvar ty, .fvar data], .custom ty' data', h => by
      simp [patternToGroundedValue?, groundedValueToPattern] at h ⊢
      aesop
  | .apply "HECustom" [.fvar ty, .fvar data], .int i, h => by
      cases i using Int.rec <;> simp [patternToGroundedValue?] at h
  | .apply "HECustom" [.fvar ty, .fvar data], .string s, h => by
      simp [patternToGroundedValue?] at h
  | .apply "HECustom" [.fvar ty, .fvar data], .bool b, h => by
      cases b <;> simp [patternToGroundedValue?] at h
  | .bvar _, g, h => by
      simp [patternToGroundedValue?] at h
  | .fvar _, g, h => by
      simp [patternToGroundedValue?] at h
  | .apply f args, g, h => by
      by_cases hInt : f = "HEIntOfNat"
      · subst hInt
        cases args with
        | nil =>
            simp [patternToGroundedValue?] at h
        | cons head tail =>
            cases tail with
            | nil =>
                cases g with
                | int i =>
                    cases i using Int.rec with
                    | ofNat n =>
                        simp [patternToGroundedValue?] at h
                        simp [groundedValueToPattern,
                          natToPattern_of_patternToNat?_eq_some h]
                    | negSucc n =>
                        simp [patternToGroundedValue?] at h
                | string s =>
                    simp [patternToGroundedValue?] at h
                | bool b =>
                    cases b <;> simp [patternToGroundedValue?] at h
                | custom ty data =>
                    simp [patternToGroundedValue?] at h
            | cons hd tl =>
                simp [patternToGroundedValue?] at h
      · by_cases hNeg : f = "HEIntNegSucc"
        · subst hNeg
          cases args with
          | nil =>
              simp [patternToGroundedValue?] at h
          | cons head tail =>
              cases tail with
              | nil =>
                  cases g with
                  | int i =>
                      cases i using Int.rec with
                      | ofNat n =>
                          simp [patternToGroundedValue?] at h
                      | negSucc n =>
                          simp [patternToGroundedValue?] at h
                          simp [groundedValueToPattern,
                            natToPattern_of_patternToNat?_eq_some h]
                  | string s =>
                      simp [patternToGroundedValue?] at h
                  | bool b =>
                      cases b <;> simp [patternToGroundedValue?] at h
                  | custom ty data =>
                      simp [patternToGroundedValue?] at h
              | cons hd tl =>
                  simp [patternToGroundedValue?] at h
        · by_cases hStr : f = "HEString"
          · subst hStr
            cases args with
            | nil =>
                simp [patternToGroundedValue?] at h
            | cons head tail =>
                cases tail with
                | nil =>
                    cases head with
                    | fvar s =>
                        simp [patternToGroundedValue?, groundedValueToPattern] at h ⊢
                        cases h
                        rfl
                    | bvar i =>
                        simp [patternToGroundedValue?] at h
                    | apply f args =>
                        simp [patternToGroundedValue?] at h
                    | lambda nm body =>
                        simp [patternToGroundedValue?] at h
                    | multiLambda n nms body =>
                        simp [patternToGroundedValue?] at h
                    | subst body repl =>
                        simp [patternToGroundedValue?] at h
                    | collection ct elems g =>
                        simp [patternToGroundedValue?] at h
                | cons hd tl =>
                    simp [patternToGroundedValue?] at h
          · by_cases hTrue : f = "HEBoolTrue"
            · subst hTrue
              cases args with
              | nil =>
                  cases g <;> simp [patternToGroundedValue?, groundedValueToPattern] at h ⊢
                  · cases h
                    rfl
              | cons head tail =>
                  simp [patternToGroundedValue?] at h
            · by_cases hFalse : f = "HEBoolFalse"
              · subst hFalse
                cases args with
                | nil =>
                    cases g <;> simp [patternToGroundedValue?, groundedValueToPattern] at h ⊢
                    · cases h
                      rfl
                | cons head tail =>
                    simp [patternToGroundedValue?] at h
              · by_cases hCustom : f = "HECustom"
                · subst hCustom
                  cases args with
                  | nil =>
                      simp [patternToGroundedValue?] at h
                  | cons head tail =>
                      cases tail with
                      | nil =>
                          simp [patternToGroundedValue?] at h
                      | cons head₂ tail₂ =>
                          cases tail₂ with
                          | nil =>
                              cases head with
                              | fvar ty =>
                                  cases head₂ with
                                  | fvar data =>
                                      simp [patternToGroundedValue?, groundedValueToPattern] at h ⊢
                                      cases h
                                      rfl
                                  | bvar i =>
                                      simp [patternToGroundedValue?] at h
                                  | apply f args =>
                                      simp [patternToGroundedValue?] at h
                                  | lambda nm body =>
                                      simp [patternToGroundedValue?] at h
                                  | multiLambda n nms body =>
                                      simp [patternToGroundedValue?] at h
                                  | subst body repl =>
                                      simp [patternToGroundedValue?] at h
                                  | collection ct elems g =>
                                      simp [patternToGroundedValue?] at h
                              | bvar i =>
                                  cases head₂ <;> simp [patternToGroundedValue?] at h
                              | apply f args =>
                                  cases head₂ <;> simp [patternToGroundedValue?] at h
                              | lambda nm body =>
                                  cases head₂ <;> simp [patternToGroundedValue?] at h
                              | multiLambda n nms body =>
                                  cases head₂ <;> simp [patternToGroundedValue?] at h
                              | subst body repl =>
                                  cases head₂ <;> simp [patternToGroundedValue?] at h
                              | collection ct elems g =>
                                  cases head₂ <;> simp [patternToGroundedValue?] at h
                          | cons hd tl =>
                              simp [patternToGroundedValue?] at h
                · simp [patternToGroundedValue?, hInt, hNeg, hStr, hTrue, hFalse, hCustom] at h
  | .lambda _ _, g, h => by
      simp [patternToGroundedValue?] at h
  | .multiLambda _ _ _, g, h => by
      simp [patternToGroundedValue?] at h
  | .subst _ _, g, h => by
      simp [patternToGroundedValue?] at h
  | .collection _ _ _, g, h => by
      simp [patternToGroundedValue?] at h

theorem natToPattern_injective :
    Function.Injective natToPattern := by
  intro n m h
  have hnat := congrArg patternToNat? h
  simpa [patternToNat_natToPattern] using hnat

theorem groundedValueToPattern_injective :
    Function.Injective groundedValueToPattern := by
  intro g h hpat
  have hground := congrArg patternToGroundedValue? hpat
  simpa [patternToGroundedValue_groundedValueToPattern] using hground

/-- Internal deferred-payload marker used by Rhometta sends. -/
def deferredPayload (payload : Atom) : Pattern :=
  .apply "rho:eval-payload" [.apply "quote" [atomToPattern payload]]

/-- Wrapped non-rho value carried back through ordinary rho substitution. -/
def wrappedValue (value : Atom) : Pattern :=
  .apply "rho:val" [atomToPattern value]

/-- Decode one operational Rhometta result wrapper back to the carried atom. -/
def decodeWrappedValue? : Pattern → Option Atom
  | .apply "rho:val" [q] => patternToAtom? q
  | _ => none

/-- Decode a list of operational result wrappers. -/
def decodeWrappedValues? : List Pattern → Option (List Atom)
  | [] => some []
  | p :: ps => do
      let a <- decodeWrappedValue? p
      let as <- decodeWrappedValues? ps
      pure (a :: as)

mutual

private theorem patternToAtom_atomToPattern :
    ∀ a : Atom, patternToAtom? (atomToPattern a) = some a
  | .symbol s => by
      simp [atomToPattern, patternToAtom?]
  | .var v => by
      simp [atomToPattern, patternToAtom?]
  | .grounded g => by
      cases g with
      | int i =>
          cases i using Int.rec with
          | ofNat n =>
              simp [atomToPattern, groundedValueToPattern, patternToAtom?,
                patternToGroundedValue?, patternToNat_natToPattern]
          | negSucc n =>
              simp [atomToPattern, groundedValueToPattern, patternToAtom?,
                patternToGroundedValue?, patternToNat_natToPattern]
      | string s =>
          simp [atomToPattern, groundedValueToPattern, patternToAtom?,
            patternToGroundedValue?]
      | bool b =>
          cases b <;> simp [atomToPattern, groundedValueToPattern, patternToAtom?,
            patternToGroundedValue?]
      | custom ty data =>
          simp [atomToPattern, groundedValueToPattern, patternToAtom?,
            patternToGroundedValue?]
  | .expression es => by
      simpa [atomToPattern, patternToAtom?] using
        patternToAtoms_map_atomToPattern es
termination_by a => sizeOf a

private theorem patternToAtoms_map_atomToPattern :
    ∀ xs : List Atom, patternToAtoms? (xs.map atomToPattern) = some xs
  | [] => by
      simp [patternToAtoms?]
  | x :: xs => by
      simp [patternToAtoms?, patternToAtom_atomToPattern x,
        patternToAtoms_map_atomToPattern xs]
termination_by xs => sizeOf xs

end

private theorem patternToAtom?_eq_some_symbol_inv
    {p : Pattern} {s : String}
    (h : patternToAtom? p = some (.symbol s)) :
    p = .apply "HESymbol" [.fvar s] := by
  cases p with
  | bvar i =>
      simp [patternToAtom?] at h
  | fvar v =>
      simp [patternToAtom?] at h
  | apply f args =>
      unfold patternToAtom? at h
      split at h <;> simp at h
      aesop
  | lambda nm body =>
      simp [patternToAtom?] at h
  | multiLambda n nms body =>
      simp [patternToAtom?] at h
  | subst body repl =>
      simp [patternToAtom?] at h
  | collection ct elems g =>
      simp [patternToAtom?] at h

private theorem patternToAtom?_eq_some_var_inv
    {p : Pattern} {v : String}
    (h : patternToAtom? p = some (.var v)) :
    p = .apply "HEVar" [.fvar v] := by
  cases p with
  | bvar i =>
      simp [patternToAtom?] at h
  | fvar x =>
      simp [patternToAtom?] at h
  | apply f args =>
      unfold patternToAtom? at h
      split at h <;> simp at h
      aesop
  | lambda nm body =>
      simp [patternToAtom?] at h
  | multiLambda n nms body =>
      simp [patternToAtom?] at h
  | subst body repl =>
      simp [patternToAtom?] at h
  | collection ct elems g =>
      simp [patternToAtom?] at h

private theorem option_map_grounded_eq_some_inv
    {o : Option GroundedValue} {g : GroundedValue}
    (h : Option.map Atom.grounded o = some (.grounded g)) :
    o = some g := by
  cases ho : o with
  | none =>
      simp [ho] at h
  | some g' =>
      simp [ho] at h
      cases h
      rfl

private theorem patternToAtom?_eq_some_grounded_inv
    {p : Pattern} {g : GroundedValue}
    (h : patternToAtom? p = some (.grounded g)) :
    groundedValueToPattern g = p := by
  cases p with
  | bvar i =>
      simp [patternToAtom?] at h
  | fvar x =>
      simp [patternToAtom?] at h
  | apply f args =>
      unfold patternToAtom? at h
      split at h
      · cases h
      · cases h
      · case h_3 a heq =>
          have hground :
              patternToGroundedValue? (.apply "HEIntOfNat" a) = some g :=
            option_map_grounded_eq_some_inv h
          calc
            groundedValueToPattern g = .apply "HEIntOfNat" a := by
              simpa using groundedValueToPattern_of_patternToGroundedValue?_eq_some hground
            _ = .apply f args := by
              simpa using heq.symm
      · case h_4 a heq =>
          have hground :
              patternToGroundedValue? (.apply "HEIntNegSucc" a) = some g :=
            option_map_grounded_eq_some_inv h
          calc
            groundedValueToPattern g = .apply "HEIntNegSucc" a := by
              simpa using groundedValueToPattern_of_patternToGroundedValue?_eq_some hground
            _ = .apply f args := by
              simpa using heq.symm
      · case h_5 a heq =>
          have hground :
              patternToGroundedValue? (.apply "HEString" a) = some g :=
            option_map_grounded_eq_some_inv h
          calc
            groundedValueToPattern g = .apply "HEString" a := by
              simpa using groundedValueToPattern_of_patternToGroundedValue?_eq_some hground
            _ = .apply f args := by
              simpa using heq.symm
      · case h_6 a heq =>
          have hground :
              patternToGroundedValue? (.apply "HEBoolTrue" a) = some g :=
            option_map_grounded_eq_some_inv h
          calc
            groundedValueToPattern g = .apply "HEBoolTrue" a := by
              simpa using groundedValueToPattern_of_patternToGroundedValue?_eq_some hground
            _ = .apply f args := by
              simpa using heq.symm
      · case h_7 a heq =>
          have hground :
              patternToGroundedValue? (.apply "HEBoolFalse" a) = some g :=
            option_map_grounded_eq_some_inv h
          calc
            groundedValueToPattern g = .apply "HEBoolFalse" a := by
              simpa using groundedValueToPattern_of_patternToGroundedValue?_eq_some hground
            _ = .apply f args := by
              simpa using heq.symm
      · case h_8 a heq =>
          have hground :
              patternToGroundedValue? (.apply "HECustom" a) = some g :=
            option_map_grounded_eq_some_inv h
          calc
            groundedValueToPattern g = .apply "HECustom" a := by
              simpa using groundedValueToPattern_of_patternToGroundedValue?_eq_some hground
            _ = .apply f args := by
              simpa using heq.symm
      · case h_9 ps heq =>
          simp at h
      · cases h
  | lambda nm body =>
      simp [patternToAtom?] at h
  | multiLambda n nms body =>
      simp [patternToAtom?] at h
  | subst body repl =>
      simp [patternToAtom?] at h
  | collection ct elems g =>
      simp [patternToAtom?] at h

private theorem option_map_expression_eq_some_inv
    {o : Option (List Atom)} {xs : List Atom}
    (h : Option.map Atom.expression o = some (.expression xs)) :
    o = some xs := by
  cases ho : o with
  | none =>
      simp [ho] at h
  | some ys =>
      simp [ho] at h
      cases h
      rfl

private theorem patternToAtom?_eq_some_expression_inv
    {p : Pattern} {xs : List Atom}
    (h : patternToAtom? p = some (.expression xs)) :
    ∃ ps, p = .apply "HEExpr" ps ∧ patternToAtoms? ps = some xs := by
  cases p with
  | bvar i =>
      simp [patternToAtom?] at h
  | fvar x =>
      simp [patternToAtom?] at h
  | apply f args =>
      unfold patternToAtom? at h
      split at h
      · cases h
      · cases h
      · simp at h
      · simp at h
      · simp at h
      · simp at h
      · simp at h
      · simp at h
      · case h_9 ps heq =>
          have hs : patternToAtoms? ps = some xs :=
            option_map_expression_eq_some_inv h
          refine ⟨ps, ?_, hs⟩
          simpa using heq
      · cases h
  | lambda nm body =>
      simp [patternToAtom?] at h
  | multiLambda n nms body =>
      simp [patternToAtom?] at h
  | subst body repl =>
      simp [patternToAtom?] at h
  | collection ct elems g =>
      simp [patternToAtom?] at h

mutual

private theorem atomToPattern_of_patternToAtom?_eq_some
    (p : Pattern) (a : Atom) (h : patternToAtom? p = some a) :
    atomToPattern a = p := by
  match a with
  | .symbol s =>
      simpa [atomToPattern] using (patternToAtom?_eq_some_symbol_inv h).symm
  | .var v =>
      simpa [atomToPattern] using (patternToAtom?_eq_some_var_inv h).symm
  | .grounded g =>
      simpa [atomToPattern] using patternToAtom?_eq_some_grounded_inv h
  | .expression xs =>
      obtain ⟨ps, hp, hs⟩ := patternToAtom?_eq_some_expression_inv h
      subst hp
      simpa [atomToPattern] using patterns_atomToPattern_of_patternToAtoms?_eq_some ps xs hs

private theorem patterns_atomToPattern_of_patternToAtoms?_eq_some
    (ps : List Pattern) (xs : List Atom) (h : patternToAtoms? ps = some xs) :
    xs.map atomToPattern = ps := by
  match ps, xs with
  | [], [] =>
      simp [patternToAtoms?] at h
      cases h
      rfl
  | [], _ :: _ =>
      simp [patternToAtoms?] at h
  | p :: ps, [] =>
      cases hp : patternToAtom? p <;> simp [patternToAtoms?, hp] at h
      case some a =>
        cases hs : patternToAtoms? ps <;> simp [hs] at h
  | p :: ps, x :: xs =>
      cases hp : patternToAtom? p <;> simp [patternToAtoms?, hp] at h
      case some a =>
        cases hs : patternToAtoms? ps <;> simp [hs] at h
        case some ys =>
          cases h
          subst x
          subst xs
          simp [atomToPattern_of_patternToAtom?_eq_some p a hp,
            patterns_atomToPattern_of_patternToAtoms?_eq_some ps ys hs]

end

theorem atomToPattern_injective :
    Function.Injective atomToPattern := by
  intro a b h
  have hdecoded := congrArg patternToAtom? h
  simpa [patternToAtom_atomToPattern a, patternToAtom_atomToPattern b] using hdecoded

theorem wrappedValue_injective :
    Function.Injective (fun a : Atom => wrappedValue a) := by
  intro a b h
  have hargs : [atomToPattern a] = [atomToPattern b] := by
    injection h with hargs
  have hatom : atomToPattern a = atomToPattern b := List.cons.inj hargs |>.1
  exact atomToPattern_injective hatom

theorem deferredPayload_injective :
    Function.Injective (fun a : Atom => deferredPayload a) := by
  intro a b h
  have hargs :
      [Pattern.apply "quote" [atomToPattern a]] =
        [Pattern.apply "quote" [atomToPattern b]] := by
    injection h with hargs
  have hquote :
      Pattern.apply "quote" [atomToPattern a] =
      Pattern.apply "quote" [atomToPattern b] :=
    List.cons.inj hargs |>.1
  have hatomList : [atomToPattern a] = [atomToPattern b] := by
    injection hquote with hatomList
  have hatom : atomToPattern a = atomToPattern b := List.cons.inj hatomList |>.1
  exact atomToPattern_injective hatom

theorem decodeWrappedValue?_wrappedValue (value : Atom) :
    decodeWrappedValue? (wrappedValue value) = some value := by
  simp [decodeWrappedValue?, wrappedValue, patternToAtom_atomToPattern]

private theorem eq_wrappedValue_of_decodeWrappedValue_eq_some
    {p : Pattern} {value : Atom}
    (h : decodeWrappedValue? p = some value) :
    p = wrappedValue value := by
  cases p with
  | bvar i =>
      simp [decodeWrappedValue?] at h
  | fvar x =>
      simp [decodeWrappedValue?] at h
  | apply f args =>
      unfold decodeWrappedValue? at h
      split at h
      · case h_1 q heq =>
          have hatom : patternToAtom? q = some value := by
            simpa [heq] using h
          have hq : q = atomToPattern value :=
            (atomToPattern_of_patternToAtom?_eq_some q value hatom).symm
          subst hq
          simpa [wrappedValue] using heq
      · simp at h
  | lambda nm body =>
      simp [decodeWrappedValue?] at h
  | multiLambda n nms body =>
      simp [decodeWrappedValue?] at h
  | subst body repl =>
      simp [decodeWrappedValue?] at h
  | collection ct elems g =>
      simp [decodeWrappedValue?] at h

private theorem decodeWrappedValue_eq_some_iff_eq_wrappedValue
    {p : Pattern} {value : Atom} :
    decodeWrappedValue? p = some value ↔ p = wrappedValue value := by
  constructor
  · exact eq_wrappedValue_of_decodeWrappedValue_eq_some
  · intro h
    subst h
    exact decodeWrappedValue?_wrappedValue value

theorem decodeWrappedValues?_map_wrappedValue :
    ∀ xs : List Atom, decodeWrappedValues? (xs.map wrappedValue) = some xs
  | [] => by
      simp [decodeWrappedValues?]
  | x :: xs => by
      simp [decodeWrappedValues?, decodeWrappedValue?_wrappedValue,
        decodeWrappedValues?_map_wrappedValue xs]

private theorem patternToAtoms?_eq_of_pointwise
    {ps qs : List Pattern}
    (hlen : ps.length = qs.length)
    (hpoint : ∀ i (h₁ : i < ps.length) (h₂ : i < qs.length),
      patternToAtom? (ps.get ⟨i, h₁⟩) = patternToAtom? (qs.get ⟨i, h₂⟩)) :
    patternToAtoms? ps = patternToAtoms? qs := by
  induction ps generalizing qs with
  | nil =>
      cases qs with
      | nil => simp [patternToAtoms?]
      | cons q qs =>
          simp at hlen
  | cons p ps ih =>
      cases qs with
      | nil =>
          simp at hlen
      | cons q qs =>
          have hpq :
              patternToAtom? p = patternToAtom? q :=
            hpoint 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
          have hrest :
              patternToAtoms? ps = patternToAtoms? qs := by
            apply ih
            · simpa using Nat.succ.inj hlen
            · intro i h₁ h₂
              simpa using hpoint (i + 1) (Nat.succ_lt_succ h₁) (Nat.succ_lt_succ h₂)
          simp [patternToAtoms?, hpq, hrest]

theorem semanticNormalizeProc_wrappedValue (value : Atom) :
    semanticNormalizeProc (wrappedValue value) = wrappedValue value := by
  simp [wrappedValue, semanticNormalizeProc]

theorem semanticNormalizeProc_deferredPayload (payload : Atom) :
    semanticNormalizeProc (deferredPayload payload) = deferredPayload payload := by
  simp [deferredPayload, semanticNormalizeProc]

mutual

/-- Collapse the administrative SC wrappers that can surround inert Rhometta/HE
payload shells: quote-drop representatives and singleton/zero/empty parallel bags. -/
private def stripSCWrappers : Pattern → Pattern
  | .apply "NQuote" [.apply "PDrop" [n]] =>
      stripSCWrappers n
  | .apply f args =>
      .apply f (stripSCWrappersList args)
  | .lambda nm body =>
      .lambda nm (stripSCWrappers body)
  | .multiLambda n nms body =>
      .multiLambda n nms (stripSCWrappers body)
  | .subst body repl =>
      .subst (stripSCWrappers body) (stripSCWrappers repl)
  | .collection .hashBag elems none =>
      let elems' :=
        (stripSCWrappersList elems).filter (fun e => e ≠ .apply "PZero" [])
      match elems' with
      | [] => .apply "PZero" []
      | [e] => e
      | _ => .collection .hashBag elems' none
  | .collection .hashSet elems none =>
      let elems' :=
        (stripSCWrappersList elems).filter (fun e => e ≠ .apply "PZero" [])
      match elems' with
      | [] => .apply "PZero" []
      | [e] => e
      | _ => .collection .hashSet elems' none
  | .collection ct elems g =>
      .collection ct (stripSCWrappersList elems) g
  | p => p

/-- List recursion for `stripSCWrappers`. -/
private def stripSCWrappersList : List Pattern → List Pattern
  | [] => []
  | p :: ps => stripSCWrappers p :: stripSCWrappersList ps

end

private theorem stripSCWrappers_natToPattern :
    ∀ n : Nat, stripSCWrappers (natToPattern n) = natToPattern n
  | 0 => by
      simp [natToPattern, stripSCWrappers, stripSCWrappersList]
  | n + 1 => by
      simp [natToPattern, stripSCWrappers, stripSCWrappersList,
        stripSCWrappers_natToPattern n]

private theorem stripSCWrappersList_eq_map (elems : List Pattern) :
    stripSCWrappersList elems = elems.map stripSCWrappers := by
  induction elems with
  | nil =>
      rfl
  | cons p ps ih =>
      simp [stripSCWrappersList, ih]

private theorem mem_stripSCWrappersList_exists
    {ps : List Pattern} {q : Pattern}
    (h : q ∈ stripSCWrappersList ps) :
    ∃ p ∈ ps, stripSCWrappers p = q := by
  induction ps with
  | nil =>
      cases h
  | cons p ps ih =>
      simp [stripSCWrappersList] at h
      rcases h with h | h
      · subst q
        exact ⟨p, by simp, rfl⟩
      · rcases ih h with ⟨p', hp', hq⟩
        exact ⟨p', by simp [hp'], hq⟩

private theorem stripSCWrappers_hashBag_singleton (p : Pattern) :
    stripSCWrappers (.collection .hashBag [p] none) =
      stripSCWrappers p := by
  by_cases hzero : stripSCWrappers p = .apply "PZero" []
  · simp [stripSCWrappers, stripSCWrappersList, hzero]
  · simp [stripSCWrappers, stripSCWrappersList, hzero]

private theorem stripSCWrappers_hashBag_nil_left (p : Pattern) :
    stripSCWrappers (.collection .hashBag [.apply "PZero" [], p] none) =
      stripSCWrappers p := by
  by_cases hzero : stripSCWrappers p = .apply "PZero" []
  · simp [stripSCWrappers, stripSCWrappersList, hzero]
  · simp [stripSCWrappers, stripSCWrappersList, hzero]

private theorem stripSCWrappers_hashBag_nil_right (p : Pattern) :
    stripSCWrappers (.collection .hashBag [p, .apply "PZero" []] none) =
      stripSCWrappers p := by
  by_cases hzero : stripSCWrappers p = .apply "PZero" []
  · simp [stripSCWrappers, stripSCWrappersList, hzero]
  · simp [stripSCWrappers, stripSCWrappersList, hzero]

mutual

private theorem stripSCWrappers_atomToPattern :
    ∀ a : Atom, stripSCWrappers (atomToPattern a) = atomToPattern a
  | .symbol s => by
      simp [atomToPattern, stripSCWrappers, stripSCWrappersList]
  | .var v => by
      simp [atomToPattern, stripSCWrappers, stripSCWrappersList]
  | .grounded g => by
      cases g with
      | int i =>
          cases i using Int.rec with
          | ofNat n =>
              simp [atomToPattern, groundedValueToPattern,
                stripSCWrappers, stripSCWrappersList,
                stripSCWrappers_natToPattern]
          | negSucc n =>
              simp [atomToPattern, groundedValueToPattern,
                stripSCWrappers, stripSCWrappersList,
                stripSCWrappers_natToPattern]
      | string s =>
          simp [atomToPattern, groundedValueToPattern,
            stripSCWrappers, stripSCWrappersList]
      | bool b =>
          cases b <;> simp [atomToPattern, groundedValueToPattern,
            stripSCWrappers, stripSCWrappersList]
      | custom ty data =>
          simp [atomToPattern, groundedValueToPattern,
            stripSCWrappers, stripSCWrappersList]
  | .expression es => by
      simpa [atomToPattern, stripSCWrappers, stripSCWrappersList] using
        stripSCWrappersList_atomToPatterns es
termination_by a => sizeOf a

private theorem stripSCWrappersList_atomToPatterns :
    ∀ xs : List Atom,
      stripSCWrappersList (xs.map atomToPattern) = xs.map atomToPattern
  | [] => by
      simp [stripSCWrappersList]
  | x :: xs => by
      simp [stripSCWrappersList, stripSCWrappers_atomToPattern x,
        stripSCWrappersList_atomToPatterns xs]
termination_by xs => sizeOf xs

end

private theorem stripSCWrappers_deferredPayload (payload : Atom) :
    stripSCWrappers (deferredPayload payload) = deferredPayload payload := by
  simp [deferredPayload, stripSCWrappers, stripSCWrappersList,
    stripSCWrappers_atomToPattern]

private theorem stripSCWrappers_wrappedValue (value : Atom) :
    stripSCWrappers (wrappedValue value) = wrappedValue value := by
  simp [wrappedValue, stripSCWrappers, stripSCWrappersList,
    stripSCWrappers_atomToPattern]

/-- SC-aware atom decoder candidate: first collapse administrative wrappers,
then decode the inert HE embedding. -/
private def scDecodeAtom? (p : Pattern) : Option Atom :=
  patternToAtom? (stripSCWrappers p)

/-- The nonzero stripped elements of a parallel bag/set shell. -/
private def strippedNonZeroElems (elems : List Pattern) : List Pattern :=
  (stripSCWrappersList elems).filter (fun e => e ≠ .apply "PZero" [])

/-- SC-aware deferred-payload decoder candidate: collapse administrative
wrappers, then read the exact Rhometta eval marker. -/
private def scDecodeDeferredPayload? (p : Pattern) : Option Atom :=
  match stripSCWrappers p with
  | .apply "rho:eval-payload" [.apply "quote" [q]] => patternToAtom? q
  | _ => none

/-- SC-aware operational result decoder candidate: collapse administrative wrappers,
then read one `rho:val` carrier.  This is the one-result version of the eventual
operational outcome decoder. -/
def scDecodeWrappedValue? (p : Pattern) : Option Atom :=
  match stripSCWrappers p with
  | .apply "rho:val" [q] => patternToAtom? q
  | _ => none

private theorem scDecodeDeferredPayload_eq_of_stripSCWrappers_eq
    {p q : Pattern}
    (h : stripSCWrappers p = stripSCWrappers q) :
    scDecodeDeferredPayload? p = scDecodeDeferredPayload? q := by
  unfold scDecodeDeferredPayload?
  rw [h]

private theorem scDecodeWrappedValue_eq_of_stripSCWrappers_eq
    {p q : Pattern}
    (h : stripSCWrappers p = stripSCWrappers q) :
    scDecodeWrappedValue? p = scDecodeWrappedValue? q := by
  unfold scDecodeWrappedValue?
  rw [h]

private theorem strippedNonZeroElems_perm
    {elems₁ elems₂ : List Pattern} (hperm : elems₁.Perm elems₂) :
    (strippedNonZeroElems elems₁).Perm (strippedNonZeroElems elems₂) := by
  unfold strippedNonZeroElems
  simpa [stripSCWrappersList_eq_map] using
    (List.Perm.filter (p := fun e => e ≠ .apply "PZero" [])
      (hperm.map stripSCWrappers))

private theorem strippedNonZeroElems_eq_nil_iff_all_zero
    {elems : List Pattern} :
    strippedNonZeroElems elems = [] ↔
      ∀ e ∈ stripSCWrappersList elems, e = .apply "PZero" [] := by
  unfold strippedNonZeroElems
  simp

private theorem strippedNonZeroElems_eq_nil_of_pointwise_zero
    {ps qs : List Pattern}
    (hlen : ps.length = qs.length)
    (hzero : ∀ i (h₁ : i < ps.length) (h₂ : i < qs.length),
      stripSCWrappers (ps.get ⟨i, h₁⟩) = .apply "PZero" [] ↔
        stripSCWrappers (qs.get ⟨i, h₂⟩) = .apply "PZero" [])
    (hqs : strippedNonZeroElems qs = []) :
    strippedNonZeroElems ps = [] := by
  induction ps generalizing qs with
  | nil =>
      cases qs with
      | nil =>
          rfl
      | cons q qs =>
          simp at hlen
  | cons p ps ih =>
      cases qs with
      | nil =>
          simp at hlen
      | cons q qs =>
          have hpqzero :
              stripSCWrappers p = .apply "PZero" [] ↔
                stripSCWrappers q = .apply "PZero" [] :=
            hzero 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
          have hqzero : stripSCWrappers q = .apply "PZero" [] := by
            by_contra hqnonzero
            unfold strippedNonZeroElems at hqs
            simp [stripSCWrappersList, hqnonzero] at hqs
          have hpzero : stripSCWrappers p = .apply "PZero" [] :=
            hpqzero.mpr hqzero
          have hlen_tail : ps.length = qs.length := by
            simpa using Nat.succ.inj hlen
          have hzero_tail :
              ∀ i (h₁ : i < ps.length) (h₂ : i < qs.length),
                stripSCWrappers (ps.get ⟨i, h₁⟩) = .apply "PZero" [] ↔
                  stripSCWrappers (qs.get ⟨i, h₂⟩) = .apply "PZero" [] := by
            intro i h₁ h₂
            simpa using hzero (i + 1) (Nat.succ_lt_succ h₁) (Nat.succ_lt_succ h₂)
          have hqs_tail : strippedNonZeroElems qs = [] := by
            have hqs_all :
                ∀ e ∈ stripSCWrappersList qs, e = .apply "PZero" [] := by
              unfold strippedNonZeroElems at hqs
              simp [stripSCWrappersList, hqzero] at hqs
              exact hqs
            exact strippedNonZeroElems_eq_nil_iff_all_zero.mpr hqs_all
          have hps_tail : strippedNonZeroElems ps = [] :=
            ih hlen_tail hzero_tail hqs_tail
          have hps_all :
              ∀ e ∈ stripSCWrappersList ps, e = .apply "PZero" [] :=
            strippedNonZeroElems_eq_nil_iff_all_zero.mp hps_tail
          unfold strippedNonZeroElems
          simp [stripSCWrappersList, hpzero]
          exact hps_all

private theorem strippedNonZeroElems_eq_nil_iff_of_pointwise_zero
    {ps qs : List Pattern}
    (hlen : ps.length = qs.length)
    (hzero : ∀ i (h₁ : i < ps.length) (h₂ : i < qs.length),
      stripSCWrappers (ps.get ⟨i, h₁⟩) = .apply "PZero" [] ↔
        stripSCWrappers (qs.get ⟨i, h₂⟩) = .apply "PZero" []) :
    strippedNonZeroElems ps = [] ↔ strippedNonZeroElems qs = [] := by
  constructor
  · intro hps
    exact strippedNonZeroElems_eq_nil_of_pointwise_zero
      (ps := qs) (qs := ps) hlen.symm
      (fun i hq hp => (hzero i hp hq).symm) hps
  · intro hqs
    exact strippedNonZeroElems_eq_nil_of_pointwise_zero hlen hzero hqs

private theorem stripSCWrappers_hashBag_eq_zero_iff
    {elems : List Pattern} :
    stripSCWrappers (.collection .hashBag elems none) = .apply "PZero" [] ↔
      strippedNonZeroElems elems = [] := by
  unfold strippedNonZeroElems
  unfold stripSCWrappers
  cases hfilter :
      List.filter (fun e => decide (e ≠ .apply "PZero" []))
        (stripSCWrappersList elems) with
  | nil =>
      simp
  | cons e es =>
      cases es with
      | nil =>
          have hmem :
              e ∈
                List.filter (fun e => decide (e ≠ .apply "PZero" []))
                  (stripSCWrappersList elems) := by
            rw [hfilter]
            simp
          have hne : e ≠ .apply "PZero" [] := by
            exact of_decide_eq_true (List.mem_filter.mp hmem).2
          simp [hne]
      | cons e' es' =>
          simp

private theorem stripSCWrappers_hashSet_eq_zero_iff
    {elems : List Pattern} :
    stripSCWrappers (.collection .hashSet elems none) = .apply "PZero" [] ↔
      strippedNonZeroElems elems = [] := by
  unfold strippedNonZeroElems
  unfold stripSCWrappers
  cases hfilter :
      List.filter (fun e => decide (e ≠ .apply "PZero" []))
        (stripSCWrappersList elems) with
  | nil =>
      simp
  | cons e es =>
      cases es with
      | nil =>
          have hmem :
              e ∈
                List.filter (fun e => decide (e ≠ .apply "PZero" []))
                  (stripSCWrappersList elems) := by
            rw [hfilter]
            simp
          have hne : e ≠ .apply "PZero" [] := by
            exact of_decide_eq_true (List.mem_filter.mp hmem).2
          simp [hne]
      | cons e' es' =>
          simp

private theorem stripSCWrappers_hashBag_eq_zero_iff_of_pointwise
    {ps qs : List Pattern}
    (hlen : ps.length = qs.length)
    (hzero : ∀ i (h₁ : i < ps.length) (h₂ : i < qs.length),
      stripSCWrappers (ps.get ⟨i, h₁⟩) = .apply "PZero" [] ↔
        stripSCWrappers (qs.get ⟨i, h₂⟩) = .apply "PZero" []) :
    stripSCWrappers (.collection .hashBag ps none) = .apply "PZero" [] ↔
      stripSCWrappers (.collection .hashBag qs none) = .apply "PZero" [] := by
  rw [stripSCWrappers_hashBag_eq_zero_iff,
    stripSCWrappers_hashBag_eq_zero_iff]
  exact strippedNonZeroElems_eq_nil_iff_of_pointwise_zero hlen hzero

private theorem stripSCWrappers_hashSet_eq_zero_iff_of_pointwise
    {ps qs : List Pattern}
    (hlen : ps.length = qs.length)
    (hzero : ∀ i (h₁ : i < ps.length) (h₂ : i < qs.length),
      stripSCWrappers (ps.get ⟨i, h₁⟩) = .apply "PZero" [] ↔
        stripSCWrappers (qs.get ⟨i, h₂⟩) = .apply "PZero" []) :
    stripSCWrappers (.collection .hashSet ps none) = .apply "PZero" [] ↔
      stripSCWrappers (.collection .hashSet qs none) = .apply "PZero" [] := by
  rw [stripSCWrappers_hashSet_eq_zero_iff,
    stripSCWrappers_hashSet_eq_zero_iff]
  exact strippedNonZeroElems_eq_nil_iff_of_pointwise_zero hlen hzero

private theorem strippedNonZeroElems_eq_singleton_deferred_of_pointwise
    {ps qs : List Pattern} {payload : Atom}
    (hlen : ps.length = qs.length)
    (hzero : ∀ i (h₁ : i < ps.length) (h₂ : i < qs.length),
      stripSCWrappers (ps.get ⟨i, h₁⟩) = .apply "PZero" [] ↔
        stripSCWrappers (qs.get ⟨i, h₂⟩) = .apply "PZero" [])
    (hdefer : ∀ i (h₁ : i < ps.length) (h₂ : i < qs.length),
      stripSCWrappers (ps.get ⟨i, h₁⟩) = deferredPayload payload ↔
        stripSCWrappers (qs.get ⟨i, h₂⟩) = deferredPayload payload)
    (hps : strippedNonZeroElems ps = [deferredPayload payload]) :
    strippedNonZeroElems qs = [deferredPayload payload] := by
  induction ps generalizing qs with
  | nil =>
      cases qs with
      | nil =>
          unfold strippedNonZeroElems at hps
          simp [stripSCWrappersList] at hps
      | cons q qs =>
          simp at hlen
  | cons p ps ih =>
      cases qs with
      | nil =>
          simp at hlen
      | cons q qs =>
          have hpqzero :
              stripSCWrappers p = .apply "PZero" [] ↔
                stripSCWrappers q = .apply "PZero" [] :=
            hzero 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
          have hpqdefer :
              stripSCWrappers p = deferredPayload payload ↔
                stripSCWrappers q = deferredPayload payload :=
            hdefer 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
          have hlen_tail : ps.length = qs.length := by
            simpa using Nat.succ.inj hlen
          have hzero_tail :
              ∀ i (h₁ : i < ps.length) (h₂ : i < qs.length),
                stripSCWrappers (ps.get ⟨i, h₁⟩) = .apply "PZero" [] ↔
                  stripSCWrappers (qs.get ⟨i, h₂⟩) = .apply "PZero" [] := by
            intro i h₁ h₂
            simpa using hzero (i + 1) (Nat.succ_lt_succ h₁) (Nat.succ_lt_succ h₂)
          have hdefer_tail :
              ∀ i (h₁ : i < ps.length) (h₂ : i < qs.length),
                stripSCWrappers (ps.get ⟨i, h₁⟩) = deferredPayload payload ↔
                  stripSCWrappers (qs.get ⟨i, h₂⟩) = deferredPayload payload := by
            intro i h₁ h₂
            simpa using hdefer (i + 1) (Nat.succ_lt_succ h₁) (Nat.succ_lt_succ h₂)
          by_cases hpzero : stripSCWrappers p = .apply "PZero" []
          · have hqzero : stripSCWrappers q = .apply "PZero" [] :=
              hpqzero.mp hpzero
            have hps_tail : strippedNonZeroElems ps = [deferredPayload payload] := by
              simpa [strippedNonZeroElems, stripSCWrappersList, hpzero] using hps
            have hqs_tail : strippedNonZeroElems qs = [deferredPayload payload] :=
              ih hlen_tail hzero_tail hdefer_tail hps_tail
            simpa [strippedNonZeroElems, stripSCWrappersList, hqzero] using hqs_tail
          · have hpdefer : stripSCWrappers p = deferredPayload payload := by
              unfold strippedNonZeroElems at hps
              simp [stripSCWrappersList, hpzero] at hps
              exact hps.1
            have hqdefer : stripSCWrappers q = deferredPayload payload :=
              hpqdefer.mp hpdefer
            have hps_tail_nil : strippedNonZeroElems ps = [] := by
              unfold strippedNonZeroElems at hps ⊢
              simp [stripSCWrappersList, hpzero] at hps
              exact strippedNonZeroElems_eq_nil_iff_all_zero.mpr hps.2
            have hqs_tail_nil : strippedNonZeroElems qs = [] :=
              (strippedNonZeroElems_eq_nil_iff_of_pointwise_zero
                hlen_tail hzero_tail).mp hps_tail_nil
            unfold strippedNonZeroElems
            simp [stripSCWrappersList, hqdefer, deferredPayload]
            exact strippedNonZeroElems_eq_nil_iff_all_zero.mp hqs_tail_nil

private theorem strippedNonZeroElems_eq_singleton_deferred_iff_of_pointwise
    {ps qs : List Pattern} {payload : Atom}
    (hlen : ps.length = qs.length)
    (hzero : ∀ i (h₁ : i < ps.length) (h₂ : i < qs.length),
      stripSCWrappers (ps.get ⟨i, h₁⟩) = .apply "PZero" [] ↔
        stripSCWrappers (qs.get ⟨i, h₂⟩) = .apply "PZero" [])
    (hdefer : ∀ i (h₁ : i < ps.length) (h₂ : i < qs.length),
      stripSCWrappers (ps.get ⟨i, h₁⟩) = deferredPayload payload ↔
        stripSCWrappers (qs.get ⟨i, h₂⟩) = deferredPayload payload) :
    strippedNonZeroElems ps = [deferredPayload payload] ↔
      strippedNonZeroElems qs = [deferredPayload payload] := by
  constructor
  · exact strippedNonZeroElems_eq_singleton_deferred_of_pointwise
      hlen hzero hdefer
  · exact strippedNonZeroElems_eq_singleton_deferred_of_pointwise
      (ps := qs) (qs := ps) hlen.symm
      (fun i hq hp => (hzero i hp hq).symm)
      (fun i hq hp => (hdefer i hp hq).symm)

private theorem scDecodeAtom_atomToPattern (a : Atom) :
    scDecodeAtom? (atomToPattern a) = some a := by
  simp [scDecodeAtom?, stripSCWrappers_atomToPattern,
    patternToAtom_atomToPattern]

private theorem scDecodeAtom_unique
    {p : Pattern} {a b : Atom}
    (h₁ : scDecodeAtom? p = some a)
    (h₂ : scDecodeAtom? p = some b) :
    a = b := by
  have hsome : some a = some b := h₁.symm.trans h₂
  simpa using hsome

private theorem atom_eq_of_scDecodeAtom_atomToPattern
    {a b : Atom}
    (h : scDecodeAtom? (atomToPattern a) = some b) :
    b = a :=
  scDecodeAtom_unique h (scDecodeAtom_atomToPattern a)

private theorem atom_eq_of_scDecodeAtom_atomToPattern_eq
    {a b : Atom}
    (h : scDecodeAtom? (atomToPattern a) =
      scDecodeAtom? (atomToPattern b)) :
    a = b := by
  have hsome : scDecodeAtom? (atomToPattern a) = some b := by
    rw [h, scDecodeAtom_atomToPattern]
  exact (atom_eq_of_scDecodeAtom_atomToPattern hsome).symm

private theorem stripSCWrappers_eq_atomToPattern_of_scDecodeAtom_eq_some
    {p : Pattern} {a : Atom}
    (h : scDecodeAtom? p = some a) :
    stripSCWrappers p = atomToPattern a := by
  unfold scDecodeAtom? at h
  simpa using (atomToPattern_of_patternToAtom?_eq_some (stripSCWrappers p) a h).symm

private theorem scDecodeAtom_eq_some_iff_strip_eq_atomToPattern
    {p : Pattern} {a : Atom} :
    scDecodeAtom? p = some a ↔
      stripSCWrappers p = atomToPattern a := by
  constructor
  · exact stripSCWrappers_eq_atomToPattern_of_scDecodeAtom_eq_some
  · intro hstrip
    unfold scDecodeAtom?
    rw [hstrip]
    exact patternToAtom_atomToPattern a

private theorem scDecodeAtom_hashBag_of_strippedNonZeroElems
    {elems : List Pattern} {a : Atom}
    (h : strippedNonZeroElems elems = [atomToPattern a]) :
    scDecodeAtom? (.collection .hashBag elems none) = some a := by
  unfold strippedNonZeroElems at h
  have h' :
      List.filter (fun e => !decide (e = .apply "PZero" []))
        (stripSCWrappersList elems) = [atomToPattern a] := by
    simpa using h
  unfold scDecodeAtom?
  simp [stripSCWrappers]
  rw [h']
  exact patternToAtom_atomToPattern a

private theorem strippedNonZeroElems_eq_singleton_of_scDecodeAtom_hashBag
    {elems : List Pattern} {a : Atom}
    (h : scDecodeAtom? (.collection .hashBag elems none) = some a) :
    strippedNonZeroElems elems = [atomToPattern a] := by
  cases hshape : strippedNonZeroElems elems with
  | nil =>
      have hshape' :
          List.filter (fun e => decide (e ≠ .apply "PZero" []))
            (stripSCWrappersList elems) = [] := by
        simpa [strippedNonZeroElems] using hshape
      unfold scDecodeAtom? at h
      unfold stripSCWrappers at h
      rw [hshape'] at h
      simp [patternToAtom?] at h
  | cons e es =>
      cases es with
      | nil =>
          have hshape' :
              List.filter (fun e => decide (e ≠ .apply "PZero" []))
                (stripSCWrappersList elems) = [e] := by
            simpa [strippedNonZeroElems] using hshape
          unfold scDecodeAtom? at h
          unfold stripSCWrappers at h
          rw [hshape'] at h
          have he : patternToAtom? e = some a := by
            simpa using h
          have heq : atomToPattern a = e :=
            atomToPattern_of_patternToAtom?_eq_some e a he
          simp [heq] at hshape ⊢
      | cons e' es' =>
          have hshape' :
              List.filter (fun e => decide (e ≠ .apply "PZero" []))
                (stripSCWrappersList elems) = e :: e' :: es' := by
            simpa [strippedNonZeroElems] using hshape
          unfold scDecodeAtom? at h
          unfold stripSCWrappers at h
          rw [hshape'] at h
          simp [patternToAtom?] at h

private theorem scDecodeAtom_hashSet_of_strippedNonZeroElems
    {elems : List Pattern} {a : Atom}
    (h : strippedNonZeroElems elems = [atomToPattern a]) :
    scDecodeAtom? (.collection .hashSet elems none) = some a := by
  unfold strippedNonZeroElems at h
  have h' :
      List.filter (fun e => !decide (e = .apply "PZero" []))
        (stripSCWrappersList elems) = [atomToPattern a] := by
    simpa using h
  unfold scDecodeAtom?
  simp [stripSCWrappers]
  rw [h']
  exact patternToAtom_atomToPattern a

private theorem strippedNonZeroElems_eq_singleton_of_scDecodeAtom_hashSet
    {elems : List Pattern} {a : Atom}
    (h : scDecodeAtom? (.collection .hashSet elems none) = some a) :
    strippedNonZeroElems elems = [atomToPattern a] := by
  cases hshape : strippedNonZeroElems elems with
  | nil =>
      have hshape' :
          List.filter (fun e => decide (e ≠ .apply "PZero" []))
            (stripSCWrappersList elems) = [] := by
        simpa [strippedNonZeroElems] using hshape
      unfold scDecodeAtom? at h
      unfold stripSCWrappers at h
      rw [hshape'] at h
      simp [patternToAtom?] at h
  | cons e es =>
      cases es with
      | nil =>
          have hshape' :
              List.filter (fun e => decide (e ≠ .apply "PZero" []))
                (stripSCWrappersList elems) = [e] := by
            simpa [strippedNonZeroElems] using hshape
          unfold scDecodeAtom? at h
          unfold stripSCWrappers at h
          rw [hshape'] at h
          have he : patternToAtom? e = some a := by
            simpa using h
          have heq : atomToPattern a = e :=
            atomToPattern_of_patternToAtom?_eq_some e a he
          simp [heq] at hshape ⊢
      | cons e' es' =>
          have hshape' :
              List.filter (fun e => decide (e ≠ .apply "PZero" []))
                (stripSCWrappersList elems) = e :: e' :: es' := by
            simpa [strippedNonZeroElems] using hshape
          unfold scDecodeAtom? at h
          unfold stripSCWrappers at h
          rw [hshape'] at h
          simp [patternToAtom?] at h

private theorem scDecodeAtom_hashBag_eq_of_perm
    {elems₁ elems₂ : List Pattern} (hperm : elems₁.Perm elems₂) :
    scDecodeAtom? (.collection .hashBag elems₁ none) =
      scDecodeAtom? (.collection .hashBag elems₂ none) := by
  cases h₁ : scDecodeAtom? (.collection .hashBag elems₁ none) with
  | none =>
      cases h₂ : scDecodeAtom? (.collection .hashBag elems₂ none) with
      | none =>
          rfl
      | some a =>
          have hs₂ : strippedNonZeroElems elems₂ = [atomToPattern a] :=
            strippedNonZeroElems_eq_singleton_of_scDecodeAtom_hashBag h₂
          have hsperm : (strippedNonZeroElems elems₁).Perm [atomToPattern a] := by
            simpa [hs₂] using strippedNonZeroElems_perm hperm
          have hs₁ : strippedNonZeroElems elems₁ = [atomToPattern a] := by
            simp at hsperm
            exact hsperm
          have hsome :
              scDecodeAtom? (.collection .hashBag elems₁ none) = some a :=
            scDecodeAtom_hashBag_of_strippedNonZeroElems hs₁
          rw [h₁] at hsome
          cases hsome
  | some a =>
      have hs₁ : strippedNonZeroElems elems₁ = [atomToPattern a] :=
        strippedNonZeroElems_eq_singleton_of_scDecodeAtom_hashBag h₁
      cases h₂ : scDecodeAtom? (.collection .hashBag elems₂ none) with
      | none =>
          have hsperm : [atomToPattern a].Perm (strippedNonZeroElems elems₂) := by
            simpa [hs₁] using strippedNonZeroElems_perm hperm
          have hs₂ : strippedNonZeroElems elems₂ = [atomToPattern a] := by
            simp at hsperm
            symm
            exact hsperm
          have hsome :
              scDecodeAtom? (.collection .hashBag elems₂ none) = some a :=
            scDecodeAtom_hashBag_of_strippedNonZeroElems hs₂
          rw [h₂] at hsome
          cases hsome
      | some b =>
          have hs₂ : strippedNonZeroElems elems₂ = [atomToPattern b] :=
            strippedNonZeroElems_eq_singleton_of_scDecodeAtom_hashBag h₂
          have hsperm : [atomToPattern a].Perm [atomToPattern b] := by
            simpa [hs₁, hs₂] using strippedNonZeroElems_perm hperm
          simp at hsperm
          exact congrArg some (atomToPattern_injective hsperm)

private theorem scDecodeAtom_hashSet_eq_of_perm
    {elems₁ elems₂ : List Pattern} (hperm : elems₁.Perm elems₂) :
    scDecodeAtom? (.collection .hashSet elems₁ none) =
      scDecodeAtom? (.collection .hashSet elems₂ none) := by
  cases h₁ : scDecodeAtom? (.collection .hashSet elems₁ none) with
  | none =>
      cases h₂ : scDecodeAtom? (.collection .hashSet elems₂ none) with
      | none =>
          rfl
      | some a =>
          have hs₂ : strippedNonZeroElems elems₂ = [atomToPattern a] :=
            strippedNonZeroElems_eq_singleton_of_scDecodeAtom_hashSet h₂
          have hsperm : (strippedNonZeroElems elems₁).Perm [atomToPattern a] := by
            simpa [hs₂] using strippedNonZeroElems_perm hperm
          have hs₁ : strippedNonZeroElems elems₁ = [atomToPattern a] := by
            simp at hsperm
            exact hsperm
          have hsome :
              scDecodeAtom? (.collection .hashSet elems₁ none) = some a :=
            scDecodeAtom_hashSet_of_strippedNonZeroElems hs₁
          rw [h₁] at hsome
          cases hsome
  | some a =>
      have hs₁ : strippedNonZeroElems elems₁ = [atomToPattern a] :=
        strippedNonZeroElems_eq_singleton_of_scDecodeAtom_hashSet h₁
      cases h₂ : scDecodeAtom? (.collection .hashSet elems₂ none) with
      | none =>
          have hsperm : [atomToPattern a].Perm (strippedNonZeroElems elems₂) := by
            simpa [hs₁] using strippedNonZeroElems_perm hperm
          have hs₂ : strippedNonZeroElems elems₂ = [atomToPattern a] := by
            simp at hsperm
            symm
            exact hsperm
          have hsome :
              scDecodeAtom? (.collection .hashSet elems₂ none) = some a :=
            scDecodeAtom_hashSet_of_strippedNonZeroElems hs₂
          rw [h₂] at hsome
          cases hsome
      | some b =>
          have hs₂ : strippedNonZeroElems elems₂ = [atomToPattern b] :=
            strippedNonZeroElems_eq_singleton_of_scDecodeAtom_hashSet h₂
          have hsperm : [atomToPattern a].Perm [atomToPattern b] := by
            simpa [hs₁, hs₂] using strippedNonZeroElems_perm hperm
          simp at hsperm
          exact congrArg some (atomToPattern_injective hsperm)

private theorem scDecodeAtom_par_singleton (p : Pattern) :
    scDecodeAtom? (.collection .hashBag [p] none) = scDecodeAtom? p := by
  by_cases hzero : stripSCWrappers p = .apply "PZero" []
  · simp [scDecodeAtom?, stripSCWrappers, stripSCWrappersList, hzero,
      patternToAtom?]
  · simp [scDecodeAtom?, stripSCWrappers, stripSCWrappersList, hzero]

private theorem scDecodeAtom_par_nil_left (p : Pattern) :
    scDecodeAtom? (.collection .hashBag [.apply "PZero" [], p] none) =
      scDecodeAtom? p := by
  by_cases hzero : stripSCWrappers p = .apply "PZero" []
  · simp [scDecodeAtom?, stripSCWrappers, stripSCWrappersList, hzero,
      patternToAtom?]
  · simp [scDecodeAtom?, stripSCWrappers, stripSCWrappersList, hzero]

private theorem scDecodeAtom_par_nil_right (p : Pattern) :
    scDecodeAtom? (.collection .hashBag [p, .apply "PZero" []] none) =
      scDecodeAtom? p := by
  by_cases hzero : stripSCWrappers p = .apply "PZero" []
  · simp [scDecodeAtom?, stripSCWrappers, stripSCWrappersList, hzero,
      patternToAtom?]
  · simp [scDecodeAtom?, stripSCWrappers, stripSCWrappersList, hzero]

private theorem scDecodeAtom_par_comm (p q : Pattern) :
    scDecodeAtom? (.collection .hashBag [p, q] none) =
      scDecodeAtom? (.collection .hashBag [q, p] none) := by
  exact scDecodeAtom_hashBag_eq_of_perm
    (List.Perm.symm (List.Perm.swap p q []))

private theorem scDecodeAtom_par_assoc (p q r : Pattern) :
    scDecodeAtom?
      (.collection .hashBag [.collection .hashBag [p, q] none, r] none) =
    scDecodeAtom?
      (.collection .hashBag [p, .collection .hashBag [q, r] none] none) := by
  by_cases hp : stripSCWrappers p = .apply "PZero" []
  · by_cases hq : stripSCWrappers q = .apply "PZero" []
    · by_cases hr : stripSCWrappers r = .apply "PZero" []
      · simp [scDecodeAtom?, stripSCWrappers, stripSCWrappersList, hp, hq, hr]
      · simp [scDecodeAtom?, stripSCWrappers, stripSCWrappersList, hp, hq, hr]
    · by_cases hr : stripSCWrappers r = .apply "PZero" []
      · simp [scDecodeAtom?, stripSCWrappers, stripSCWrappersList, hp, hq, hr]
      · simp [scDecodeAtom?, stripSCWrappers, stripSCWrappersList, hp, hq, hr]
  · by_cases hq : stripSCWrappers q = .apply "PZero" []
    · by_cases hr : stripSCWrappers r = .apply "PZero" []
      · simp [scDecodeAtom?, stripSCWrappers, stripSCWrappersList, hp, hq, hr]
      · simp [scDecodeAtom?, stripSCWrappers, stripSCWrappersList, hp, hq, hr]
    · by_cases hr : stripSCWrappers r = .apply "PZero" []
      · simp [scDecodeAtom?, stripSCWrappers, stripSCWrappersList, hp, hq, hr]
      · simp [scDecodeAtom?, stripSCWrappers, stripSCWrappersList, hp, hq, hr,
          patternToAtom?]

private theorem scDecodeAtom_quoteDrop_general (p : Pattern) :
    scDecodeAtom? (.apply "NQuote" [.apply "PDrop" [p]]) =
      scDecodeAtom? p := by
  simp [scDecodeAtom?, stripSCWrappers]

private theorem scDecodeAtom_not_structuralCongruence_invariant :
    ∃ p q a, StructuralCongruence p q ∧
      scDecodeAtom? p = none ∧ scDecodeAtom? q = some a := by
  let a : Atom := .symbol "x"
  let p : Pattern :=
    .apply "NQuote" [.collection .hashBag [.apply "PDrop" [atomToPattern a]] none]
  let q : Pattern := atomToPattern a
  refine ⟨p, q, a, ?_, ?_, ?_⟩
  · dsimp [p, q, a]
    refine StructuralCongruence.trans
      (.apply "NQuote"
        [.collection .hashBag [.apply "PDrop" [atomToPattern (.symbol "x")]] none])
      (.apply "NQuote" [.apply "PDrop" [atomToPattern (.symbol "x")]])
      (atomToPattern (.symbol "x")) ?_ ?_
    · exact StructuralCongruence.apply_cong "NQuote"
        [.collection .hashBag [.apply "PDrop" [atomToPattern (.symbol "x")]] none]
        [.apply "PDrop" [atomToPattern (.symbol "x")]]
        (by simp)
        (by
          intro i h₁ h₂
          simp at h₁ h₂
          have hi : i = 0 := by omega
          subst hi
          simpa using
            StructuralCongruence.par_singleton
              (.apply "PDrop" [atomToPattern (.symbol "x")]))
    · exact StructuralCongruence.quote_drop (atomToPattern (.symbol "x"))
  · simp [p, a, scDecodeAtom?, stripSCWrappers, stripSCWrappersList,
      atomToPattern, patternToAtom?]
  · simp [q, a, scDecodeAtom?, stripSCWrappers, stripSCWrappersList,
      atomToPattern, patternToAtom?]

private theorem patternToAtoms?_eq_of_pointwise_scDecodeAtom
    {ps qs : List Pattern}
    (hlen : ps.length = qs.length)
    (hpoint : ∀ i (h₁ : i < ps.length) (h₂ : i < qs.length),
      scDecodeAtom? (ps.get ⟨i, h₁⟩) =
        scDecodeAtom? (qs.get ⟨i, h₂⟩)) :
    patternToAtoms? (stripSCWrappersList ps) =
      patternToAtoms? (stripSCWrappersList qs) := by
  rw [stripSCWrappersList_eq_map ps, stripSCWrappersList_eq_map qs]
  apply patternToAtoms?_eq_of_pointwise
  · simpa using hlen
  · intro i h₁ h₂
    have hp : i < ps.length := by simpa using h₁
    have hq : i < qs.length := by simpa using h₂
    simpa [scDecodeAtom?] using hpoint i hp hq

private theorem scDecodeDeferredPayload_deferredPayload (payload : Atom) :
    scDecodeDeferredPayload? (deferredPayload payload) = some payload := by
  rw [scDecodeDeferredPayload?, stripSCWrappers_deferredPayload]
  simp [deferredPayload, patternToAtom_atomToPattern]

private theorem scDecodeDeferredPayload_evalPayloadQuote (q : Pattern) :
    scDecodeDeferredPayload?
      (.apply "rho:eval-payload" [.apply "quote" [q]]) =
        scDecodeAtom? q := by
  simp [scDecodeDeferredPayload?, scDecodeAtom?, stripSCWrappers,
    stripSCWrappersList]

private theorem scDecodeDeferredPayload_evalPayloadQuote_eq_of_scDecodeAtom_eq
    {q₁ q₂ : Pattern}
    (h : scDecodeAtom? q₁ = scDecodeAtom? q₂) :
    scDecodeDeferredPayload?
        (.apply "rho:eval-payload" [.apply "quote" [q₁]]) =
      scDecodeDeferredPayload?
        (.apply "rho:eval-payload" [.apply "quote" [q₂]]) := by
  rw [scDecodeDeferredPayload_evalPayloadQuote,
    scDecodeDeferredPayload_evalPayloadQuote]
  exact h

private theorem scDecodeDeferredPayload_quoteDrop_general (p : Pattern) :
    scDecodeDeferredPayload? (.apply "NQuote" [.apply "PDrop" [p]]) =
      scDecodeDeferredPayload? p := by
  simp [scDecodeDeferredPayload?, stripSCWrappers]

private theorem scDecodeDeferredPayload_unique
    {p : Pattern} {payload₁ payload₂ : Atom}
    (h₁ : scDecodeDeferredPayload? p = some payload₁)
    (h₂ : scDecodeDeferredPayload? p = some payload₂) :
    payload₁ = payload₂ := by
  have hsome : some payload₁ = some payload₂ := h₁.symm.trans h₂
  simpa using hsome

private theorem payload_eq_of_scDecodeDeferredPayload_deferredPayload
    {payload₁ payload₂ : Atom}
    (h : scDecodeDeferredPayload? (deferredPayload payload₁) =
      some payload₂) :
    payload₂ = payload₁ :=
  scDecodeDeferredPayload_unique h
    (scDecodeDeferredPayload_deferredPayload payload₁)

private theorem payload_eq_of_scDecodeDeferredPayload_deferredPayload_eq
    {payload₁ payload₂ : Atom}
    (h :
      scDecodeDeferredPayload? (deferredPayload payload₁) =
        scDecodeDeferredPayload? (deferredPayload payload₂)) :
    payload₁ = payload₂ := by
  have hsome :
      scDecodeDeferredPayload? (deferredPayload payload₁) =
        some payload₂ := by
    rw [h, scDecodeDeferredPayload_deferredPayload]
  exact (payload_eq_of_scDecodeDeferredPayload_deferredPayload hsome).symm

private theorem stripSCWrappers_eq_deferredPayload_of_scDecodeDeferredPayload_eq_some
    {p : Pattern} {payload : Atom}
    (h : scDecodeDeferredPayload? p = some payload) :
    stripSCWrappers p = deferredPayload payload := by
  unfold scDecodeDeferredPayload? at h
  split at h
  · case h_1 q heq =>
      have hatom : patternToAtom? q = some payload := by
        simpa [heq] using h
      have hq : atomToPattern payload = q :=
        atomToPattern_of_patternToAtom?_eq_some q payload hatom
      calc
        stripSCWrappers p = .apply "rho:eval-payload" [.apply "quote" [q]] := by
          simpa using heq
        _ = .apply "rho:eval-payload" [.apply "quote" [atomToPattern payload]] := by
          simp [hq]
        _ = deferredPayload payload := by
          rfl
  · cases h

private theorem scDecodeDeferredPayload_eq_some_iff_strip_eq_deferredPayload
    {p : Pattern} {payload : Atom} :
    scDecodeDeferredPayload? p = some payload ↔
      stripSCWrappers p = deferredPayload payload := by
  constructor
  · exact stripSCWrappers_eq_deferredPayload_of_scDecodeDeferredPayload_eq_some
  · intro hstrip
    unfold scDecodeDeferredPayload?
    rw [hstrip]
    simp [deferredPayload, patternToAtom_atomToPattern]

private theorem scDecodeDeferredPayload_quoteDrop (payload : Atom) :
    scDecodeDeferredPayload?
      (.apply "NQuote" [.apply "PDrop" [deferredPayload payload]]) =
        some payload := by
  simp [scDecodeDeferredPayload?, stripSCWrappers]
  exact scDecodeDeferredPayload_deferredPayload payload

private theorem scDecodeDeferredPayload_not_structuralCongruence_invariant
    (payload : Atom) :
    ∃ p q,
      StructuralCongruence p q ∧
      scDecodeDeferredPayload? p = some payload ∧
      scDecodeDeferredPayload? q = none := by
  let p : Pattern :=
    Pattern.apply "NQuote" [Pattern.apply "PDrop" [deferredPayload payload]]
  let q : Pattern :=
    Pattern.apply "NQuote"
      [Pattern.collection .hashBag
        [Pattern.apply "PDrop" [deferredPayload payload]] none]
  refine ⟨p, q, ?_, ?_, ?_⟩
  · refine StructuralCongruence.apply_cong
      "NQuote"
      [.apply "PDrop" [deferredPayload payload]]
      [.collection .hashBag [.apply "PDrop" [deferredPayload payload]] none]
      rfl ?_
    intro i h₁ h₂
    have hi : i = 0 := by
      have hlt : i < 1 := by simpa using h₁
      simpa using hlt
    subst hi
    simpa using
      (StructuralCongruence.symm _ _
        (StructuralCongruence.par_singleton
          (.apply "PDrop" [deferredPayload payload])))
  · simpa [p] using scDecodeDeferredPayload_quoteDrop payload
  · simp [q, scDecodeDeferredPayload?, stripSCWrappers, stripSCWrappersList]

private theorem scDecodeDeferredPayload_singleton (payload : Atom) :
    scDecodeDeferredPayload?
      (.collection .hashBag [deferredPayload payload] none) =
        some payload := by
  simp [scDecodeDeferredPayload?, stripSCWrappers, stripSCWrappersList]
  simpa [deferredPayload] using scDecodeAtom_atomToPattern payload

private theorem scDecodeDeferredPayload_zero_left (payload : Atom) :
    scDecodeDeferredPayload?
      (.collection .hashBag [.apply "PZero" [], deferredPayload payload] none) =
        some payload := by
  simp [scDecodeDeferredPayload?, stripSCWrappers, stripSCWrappersList]
  simpa [deferredPayload] using scDecodeAtom_atomToPattern payload

private theorem scDecodeDeferredPayload_zero_right (payload : Atom) :
    scDecodeDeferredPayload?
      (.collection .hashBag [deferredPayload payload, .apply "PZero" []] none) =
        some payload := by
  simp [scDecodeDeferredPayload?, stripSCWrappers, stripSCWrappersList]
  simpa [deferredPayload] using scDecodeAtom_atomToPattern payload

private theorem scDecodeDeferredPayload_hashBag_of_strippedNonZeroElems
    {elems : List Pattern} {payload : Atom}
    (h : strippedNonZeroElems elems = [deferredPayload payload]) :
    scDecodeDeferredPayload? (.collection .hashBag elems none) = some payload := by
  unfold strippedNonZeroElems at h
  have h' :
      List.filter (fun e => !decide (e = .apply "PZero" []))
        (stripSCWrappersList elems) = [deferredPayload payload] := by
    simpa using h
  unfold scDecodeDeferredPayload?
  simp [stripSCWrappers]
  rw [h']
  simp [deferredPayload, patternToAtom_atomToPattern]

private theorem strippedNonZeroElems_eq_singleton_of_scDecodeDeferredPayload_hashBag
    {elems : List Pattern} {payload : Atom}
    (h : scDecodeDeferredPayload? (.collection .hashBag elems none) = some payload) :
    strippedNonZeroElems elems = [deferredPayload payload] := by
  have hstrip :
      stripSCWrappers (.collection .hashBag elems none) = deferredPayload payload :=
    stripSCWrappers_eq_deferredPayload_of_scDecodeDeferredPayload_eq_some h
  cases hshape : strippedNonZeroElems elems with
  | nil =>
      have hshape' :
          List.filter (fun e => decide (e ≠ .apply "PZero" []))
            (stripSCWrappersList elems) = [] := by
        simpa [strippedNonZeroElems] using hshape
      unfold stripSCWrappers at hstrip
      rw [hshape'] at hstrip
      have : False := by
        simp [deferredPayload] at hstrip
      exact False.elim this
  | cons e es =>
      cases es with
      | nil =>
          have hshape' :
              List.filter (fun e => decide (e ≠ .apply "PZero" []))
                (stripSCWrappersList elems) = [e] := by
            simpa [strippedNonZeroElems] using hshape
          unfold stripSCWrappers at hstrip
          rw [hshape'] at hstrip
          simp [hstrip]
      | cons e' es' =>
          have hshape' :
              List.filter (fun e => decide (e ≠ .apply "PZero" []))
                (stripSCWrappersList elems) = e :: e' :: es' := by
            simpa [strippedNonZeroElems] using hshape
          unfold stripSCWrappers at hstrip
          rw [hshape'] at hstrip
          have : False := by
            simp [deferredPayload] at hstrip
          exact False.elim this

private theorem scDecodeDeferredPayload_hashBag_eq_some_iff_of_pointwise
    {ps qs : List Pattern} {payload : Atom}
    (hlen : ps.length = qs.length)
    (hzero : ∀ i (h₁ : i < ps.length) (h₂ : i < qs.length),
      stripSCWrappers (ps.get ⟨i, h₁⟩) = .apply "PZero" [] ↔
        stripSCWrappers (qs.get ⟨i, h₂⟩) = .apply "PZero" [])
    (hdefer : ∀ i (h₁ : i < ps.length) (h₂ : i < qs.length),
      stripSCWrappers (ps.get ⟨i, h₁⟩) = deferredPayload payload ↔
        stripSCWrappers (qs.get ⟨i, h₂⟩) = deferredPayload payload) :
    scDecodeDeferredPayload? (.collection .hashBag ps none) = some payload ↔
      scDecodeDeferredPayload? (.collection .hashBag qs none) = some payload := by
  constructor
  · intro hps
    exact scDecodeDeferredPayload_hashBag_of_strippedNonZeroElems
      ((strippedNonZeroElems_eq_singleton_deferred_iff_of_pointwise
          hlen hzero hdefer).mp
        (strippedNonZeroElems_eq_singleton_of_scDecodeDeferredPayload_hashBag hps))
  · intro hqs
    exact scDecodeDeferredPayload_hashBag_of_strippedNonZeroElems
      ((strippedNonZeroElems_eq_singleton_deferred_iff_of_pointwise
          hlen hzero hdefer).mpr
        (strippedNonZeroElems_eq_singleton_of_scDecodeDeferredPayload_hashBag hqs))

private theorem scDecodeDeferredPayload_hashSet_of_strippedNonZeroElems
    {elems : List Pattern} {payload : Atom}
    (h : strippedNonZeroElems elems = [deferredPayload payload]) :
    scDecodeDeferredPayload? (.collection .hashSet elems none) = some payload := by
  unfold strippedNonZeroElems at h
  have h' :
      List.filter (fun e => !decide (e = .apply "PZero" []))
        (stripSCWrappersList elems) = [deferredPayload payload] := by
    simpa using h
  unfold scDecodeDeferredPayload?
  simp [stripSCWrappers]
  rw [h']
  simp [deferredPayload, patternToAtom_atomToPattern]

private theorem strippedNonZeroElems_eq_singleton_of_scDecodeDeferredPayload_hashSet
    {elems : List Pattern} {payload : Atom}
    (h : scDecodeDeferredPayload? (.collection .hashSet elems none) = some payload) :
    strippedNonZeroElems elems = [deferredPayload payload] := by
  have hstrip :
      stripSCWrappers (.collection .hashSet elems none) = deferredPayload payload :=
    stripSCWrappers_eq_deferredPayload_of_scDecodeDeferredPayload_eq_some h
  cases hshape : strippedNonZeroElems elems with
  | nil =>
      have hshape' :
          List.filter (fun e => decide (e ≠ .apply "PZero" []))
            (stripSCWrappersList elems) = [] := by
        simpa [strippedNonZeroElems] using hshape
      unfold stripSCWrappers at hstrip
      rw [hshape'] at hstrip
      have : False := by
        simp [deferredPayload] at hstrip
      exact False.elim this
  | cons e es =>
      cases es with
      | nil =>
          have hshape' :
              List.filter (fun e => decide (e ≠ .apply "PZero" []))
                (stripSCWrappersList elems) = [e] := by
            simpa [strippedNonZeroElems] using hshape
          unfold stripSCWrappers at hstrip
          rw [hshape'] at hstrip
          simp [hstrip]
      | cons e' es' =>
          have hshape' :
              List.filter (fun e => decide (e ≠ .apply "PZero" []))
                (stripSCWrappersList elems) = e :: e' :: es' := by
            simpa [strippedNonZeroElems] using hshape
          unfold stripSCWrappers at hstrip
          rw [hshape'] at hstrip
          have : False := by
            simp [deferredPayload] at hstrip
          exact False.elim this

private theorem scDecodeDeferredPayload_hashSet_eq_some_iff_of_pointwise
    {ps qs : List Pattern} {payload : Atom}
    (hlen : ps.length = qs.length)
    (hzero : ∀ i (h₁ : i < ps.length) (h₂ : i < qs.length),
      stripSCWrappers (ps.get ⟨i, h₁⟩) = .apply "PZero" [] ↔
        stripSCWrappers (qs.get ⟨i, h₂⟩) = .apply "PZero" [])
    (hdefer : ∀ i (h₁ : i < ps.length) (h₂ : i < qs.length),
      stripSCWrappers (ps.get ⟨i, h₁⟩) = deferredPayload payload ↔
        stripSCWrappers (qs.get ⟨i, h₂⟩) = deferredPayload payload) :
    scDecodeDeferredPayload? (.collection .hashSet ps none) = some payload ↔
      scDecodeDeferredPayload? (.collection .hashSet qs none) = some payload := by
  constructor
  · intro hps
    exact scDecodeDeferredPayload_hashSet_of_strippedNonZeroElems
      ((strippedNonZeroElems_eq_singleton_deferred_iff_of_pointwise
          hlen hzero hdefer).mp
        (strippedNonZeroElems_eq_singleton_of_scDecodeDeferredPayload_hashSet hps))
  · intro hqs
    exact scDecodeDeferredPayload_hashSet_of_strippedNonZeroElems
      ((strippedNonZeroElems_eq_singleton_deferred_iff_of_pointwise
          hlen hzero hdefer).mpr
        (strippedNonZeroElems_eq_singleton_of_scDecodeDeferredPayload_hashSet hqs))

private theorem scDecodeDeferredPayload_hashBag_eq_of_perm
    {elems₁ elems₂ : List Pattern} (hperm : elems₁.Perm elems₂) :
    scDecodeDeferredPayload? (.collection .hashBag elems₁ none) =
      scDecodeDeferredPayload? (.collection .hashBag elems₂ none) := by
  cases h₁ : scDecodeDeferredPayload? (.collection .hashBag elems₁ none) with
  | none =>
      cases h₂ : scDecodeDeferredPayload? (.collection .hashBag elems₂ none) with
      | none =>
          rfl
      | some payload =>
          have hs₂ :
              strippedNonZeroElems elems₂ = [deferredPayload payload] :=
            strippedNonZeroElems_eq_singleton_of_scDecodeDeferredPayload_hashBag h₂
          have hsperm : (strippedNonZeroElems elems₁).Perm [deferredPayload payload] := by
            simpa [hs₂] using strippedNonZeroElems_perm hperm
          have hs₁ :
              strippedNonZeroElems elems₁ = [deferredPayload payload] := by
            simp at hsperm
            exact hsperm
          have hsome :
              scDecodeDeferredPayload? (.collection .hashBag elems₁ none) = some payload :=
            scDecodeDeferredPayload_hashBag_of_strippedNonZeroElems hs₁
          rw [h₁] at hsome
          cases hsome
  | some payload =>
      have hs₁ :
          strippedNonZeroElems elems₁ = [deferredPayload payload] :=
        strippedNonZeroElems_eq_singleton_of_scDecodeDeferredPayload_hashBag h₁
      cases h₂ : scDecodeDeferredPayload? (.collection .hashBag elems₂ none) with
      | none =>
          have hsperm : [deferredPayload payload].Perm (strippedNonZeroElems elems₂) := by
            simpa [hs₁] using strippedNonZeroElems_perm hperm
          have hs₂ :
              strippedNonZeroElems elems₂ = [deferredPayload payload] := by
            simp at hsperm
            symm
            exact hsperm
          have hsome :
              scDecodeDeferredPayload? (.collection .hashBag elems₂ none) = some payload :=
            scDecodeDeferredPayload_hashBag_of_strippedNonZeroElems hs₂
          rw [h₂] at hsome
          cases hsome
      | some payload' =>
          have hs₂ :
              strippedNonZeroElems elems₂ = [deferredPayload payload'] :=
            strippedNonZeroElems_eq_singleton_of_scDecodeDeferredPayload_hashBag h₂
          have hsperm : [deferredPayload payload].Perm [deferredPayload payload'] := by
            simpa [hs₁, hs₂] using strippedNonZeroElems_perm hperm
          simp at hsperm
          exact congrArg some (deferredPayload_injective hsperm)

private theorem scDecodeDeferredPayload_hashSet_eq_of_perm
    {elems₁ elems₂ : List Pattern} (hperm : elems₁.Perm elems₂) :
    scDecodeDeferredPayload? (.collection .hashSet elems₁ none) =
      scDecodeDeferredPayload? (.collection .hashSet elems₂ none) := by
  cases h₁ : scDecodeDeferredPayload? (.collection .hashSet elems₁ none) with
  | none =>
      cases h₂ : scDecodeDeferredPayload? (.collection .hashSet elems₂ none) with
      | none =>
          rfl
      | some payload =>
          have hs₂ :
              strippedNonZeroElems elems₂ = [deferredPayload payload] :=
            strippedNonZeroElems_eq_singleton_of_scDecodeDeferredPayload_hashSet h₂
          have hsperm : (strippedNonZeroElems elems₁).Perm [deferredPayload payload] := by
            simpa [hs₂] using strippedNonZeroElems_perm hperm
          have hs₁ :
              strippedNonZeroElems elems₁ = [deferredPayload payload] := by
            simp at hsperm
            exact hsperm
          have hsome :
              scDecodeDeferredPayload? (.collection .hashSet elems₁ none) = some payload :=
            scDecodeDeferredPayload_hashSet_of_strippedNonZeroElems hs₁
          rw [h₁] at hsome
          cases hsome
  | some payload =>
      have hs₁ :
          strippedNonZeroElems elems₁ = [deferredPayload payload] :=
        strippedNonZeroElems_eq_singleton_of_scDecodeDeferredPayload_hashSet h₁
      cases h₂ : scDecodeDeferredPayload? (.collection .hashSet elems₂ none) with
      | none =>
          have hsperm : [deferredPayload payload].Perm (strippedNonZeroElems elems₂) := by
            simpa [hs₁] using strippedNonZeroElems_perm hperm
          have hs₂ :
              strippedNonZeroElems elems₂ = [deferredPayload payload] := by
            simp at hsperm
            symm
            exact hsperm
          have hsome :
              scDecodeDeferredPayload? (.collection .hashSet elems₂ none) = some payload :=
            scDecodeDeferredPayload_hashSet_of_strippedNonZeroElems hs₂
          rw [h₂] at hsome
          cases hsome
      | some payload' =>
          have hs₂ :
              strippedNonZeroElems elems₂ = [deferredPayload payload'] :=
            strippedNonZeroElems_eq_singleton_of_scDecodeDeferredPayload_hashSet h₂
          have hsperm : [deferredPayload payload].Perm [deferredPayload payload'] := by
            simpa [hs₁, hs₂] using strippedNonZeroElems_perm hperm
          simp at hsperm
          exact congrArg some (deferredPayload_injective hsperm)

private theorem scDecodeDeferredPayload_par_singleton (p : Pattern) :
    scDecodeDeferredPayload? (.collection .hashBag [p] none) =
      scDecodeDeferredPayload? p := by
  by_cases hzero : stripSCWrappers p = .apply "PZero" []
  · simp [scDecodeDeferredPayload?, stripSCWrappers, stripSCWrappersList, hzero]
  · simp [scDecodeDeferredPayload?, stripSCWrappers, stripSCWrappersList, hzero]

private theorem scDecodeDeferredPayload_par_nil_left (p : Pattern) :
    scDecodeDeferredPayload? (.collection .hashBag [.apply "PZero" [], p] none) =
      scDecodeDeferredPayload? p := by
  by_cases hzero : stripSCWrappers p = .apply "PZero" []
  · simp [scDecodeDeferredPayload?, stripSCWrappers, stripSCWrappersList, hzero]
  · simp [scDecodeDeferredPayload?, stripSCWrappers, stripSCWrappersList, hzero]

private theorem scDecodeDeferredPayload_par_nil_right (p : Pattern) :
    scDecodeDeferredPayload? (.collection .hashBag [p, .apply "PZero" []] none) =
      scDecodeDeferredPayload? p := by
  by_cases hzero : stripSCWrappers p = .apply "PZero" []
  · simp [scDecodeDeferredPayload?, stripSCWrappers, stripSCWrappersList, hzero]
  · simp [scDecodeDeferredPayload?, stripSCWrappers, stripSCWrappersList, hzero]

private theorem scDecodeDeferredPayload_par_comm (p q : Pattern) :
    scDecodeDeferredPayload? (.collection .hashBag [p, q] none) =
      scDecodeDeferredPayload? (.collection .hashBag [q, p] none) := by
  by_cases hp : stripSCWrappers p = .apply "PZero" []
  · by_cases hq : stripSCWrappers q = .apply "PZero" []
    · simp [scDecodeDeferredPayload?, stripSCWrappers, stripSCWrappersList, hp, hq]
    · simp [scDecodeDeferredPayload?, stripSCWrappers, stripSCWrappersList, hp, hq]
  · by_cases hq : stripSCWrappers q = .apply "PZero" []
    · simp [scDecodeDeferredPayload?, stripSCWrappers, stripSCWrappersList, hp, hq]
    · simp [scDecodeDeferredPayload?, stripSCWrappers, stripSCWrappersList, hp, hq]

private theorem scDecodeDeferredPayload_par_assoc (p q r : Pattern) :
    scDecodeDeferredPayload?
      (.collection .hashBag [.collection .hashBag [p, q] none, r] none) =
    scDecodeDeferredPayload?
      (.collection .hashBag [p, .collection .hashBag [q, r] none] none) := by
  by_cases hp : stripSCWrappers p = .apply "PZero" []
  · by_cases hq : stripSCWrappers q = .apply "PZero" []
    · by_cases hr : stripSCWrappers r = .apply "PZero" []
      · simp [scDecodeDeferredPayload?, stripSCWrappers, stripSCWrappersList, hp, hq, hr]
      · simp [scDecodeDeferredPayload?, stripSCWrappers, stripSCWrappersList, hp, hq, hr]
    · by_cases hr : stripSCWrappers r = .apply "PZero" []
      · simp [scDecodeDeferredPayload?, stripSCWrappers, stripSCWrappersList, hp, hq, hr]
      · simp [scDecodeDeferredPayload?, stripSCWrappers, stripSCWrappersList, hp, hq, hr]
  · by_cases hq : stripSCWrappers q = .apply "PZero" []
    · by_cases hr : stripSCWrappers r = .apply "PZero" []
      · simp [scDecodeDeferredPayload?, stripSCWrappers, stripSCWrappersList, hp, hq, hr]
      · simp [scDecodeDeferredPayload?, stripSCWrappers, stripSCWrappersList, hp, hq, hr]
    · by_cases hr : stripSCWrappers r = .apply "PZero" []
      · simp [scDecodeDeferredPayload?, stripSCWrappers, stripSCWrappersList, hp, hq, hr]
      · simp [scDecodeDeferredPayload?, stripSCWrappers, stripSCWrappersList, hp, hq, hr]

theorem scDecodeWrappedValue?_wrappedValue (value : Atom) :
    scDecodeWrappedValue? (wrappedValue value) = some value := by
  unfold scDecodeWrappedValue?
  rw [stripSCWrappers_wrappedValue]
  simp [wrappedValue, patternToAtom_atomToPattern]

private theorem scDecodeWrappedValue_unique
    {p : Pattern} {value value' : Atom}
    (h :
      scDecodeWrappedValue? p = some value)
    (h' :
      scDecodeWrappedValue? p = some value') :
    value = value' := by
  have hsome : some value = some value' := h.symm.trans h'
  simpa using hsome

private theorem value_eq_of_scDecodeWrappedValue_wrappedValue
    {value value' : Atom}
    (h : scDecodeWrappedValue? (wrappedValue value') = some value) :
    value = value' :=
  scDecodeWrappedValue_unique h (scDecodeWrappedValue?_wrappedValue value')

private theorem stripSCWrappers_eq_wrappedValue_of_scDecodeWrappedValue_eq_some
    {p : Pattern} {value : Atom}
    (h : scDecodeWrappedValue? p = some value) :
    stripSCWrappers p = wrappedValue value := by
  unfold scDecodeWrappedValue? at h
  split at h
  · case h_1 q heq =>
      have hatom : patternToAtom? q = some value := by
        simpa [heq] using h
      have hq : atomToPattern value = q :=
        atomToPattern_of_patternToAtom?_eq_some q value hatom
      calc
        stripSCWrappers p = .apply "rho:val" [q] := by
          simpa using heq
        _ = .apply "rho:val" [atomToPattern value] := by
          simp [hq]
        _ = wrappedValue value := by
          rfl
  · cases h

private theorem scDecodeWrappedValue_eq_some_iff_strip_eq_wrappedValue
    {p : Pattern} {value : Atom} :
    scDecodeWrappedValue? p = some value ↔
      stripSCWrappers p = wrappedValue value := by
  constructor
  · exact stripSCWrappers_eq_wrappedValue_of_scDecodeWrappedValue_eq_some
  · intro hstrip
    unfold scDecodeWrappedValue?
    rw [hstrip]
    simp [wrappedValue, patternToAtom_atomToPattern]

private theorem scDecodeWrappedValue_singleton (value : Atom) :
    scDecodeWrappedValue?
      (.collection .hashBag [wrappedValue value] none) =
        some value := by
  simp [scDecodeWrappedValue?, stripSCWrappers, stripSCWrappersList]
  simpa [wrappedValue] using scDecodeAtom_atomToPattern value

private theorem scDecodeWrappedValue_zero_left (value : Atom) :
    scDecodeWrappedValue?
      (.collection .hashBag [.apply "PZero" [], wrappedValue value] none) =
        some value := by
  simp [scDecodeWrappedValue?, stripSCWrappers, stripSCWrappersList]
  simpa [wrappedValue] using scDecodeAtom_atomToPattern value

private theorem scDecodeWrappedValue_zero_right (value : Atom) :
    scDecodeWrappedValue?
      (.collection .hashBag [wrappedValue value, .apply "PZero" []] none) =
        some value := by
  simp [scDecodeWrappedValue?, stripSCWrappers, stripSCWrappersList]
  simpa [wrappedValue] using scDecodeAtom_atomToPattern value

private theorem scDecodeWrappedValue_hashBag_of_strippedNonZeroElems
    {elems : List Pattern} {value : Atom}
    (h : strippedNonZeroElems elems = [wrappedValue value]) :
    scDecodeWrappedValue? (.collection .hashBag elems none) = some value := by
  unfold strippedNonZeroElems at h
  have h' :
      List.filter (fun e => !decide (e = .apply "PZero" []))
        (stripSCWrappersList elems) = [wrappedValue value] := by
    simpa using h
  unfold scDecodeWrappedValue?
  simp [stripSCWrappers]
  rw [h']
  simp [wrappedValue, patternToAtom_atomToPattern]

private theorem strippedNonZeroElems_eq_singleton_of_scDecodeWrappedValue_hashBag
    {elems : List Pattern} {value : Atom}
    (h : scDecodeWrappedValue? (.collection .hashBag elems none) = some value) :
    strippedNonZeroElems elems = [wrappedValue value] := by
  have hstrip :
      stripSCWrappers (.collection .hashBag elems none) = wrappedValue value :=
    stripSCWrappers_eq_wrappedValue_of_scDecodeWrappedValue_eq_some h
  cases hshape : strippedNonZeroElems elems with
  | nil =>
      have hshape' :
          List.filter (fun e => decide (e ≠ .apply "PZero" []))
            (stripSCWrappersList elems) = [] := by
        simpa [strippedNonZeroElems] using hshape
      unfold stripSCWrappers at hstrip
      rw [hshape'] at hstrip
      have : False := by
        simp [wrappedValue] at hstrip
      exact False.elim this
  | cons e es =>
      cases es with
      | nil =>
          have hshape' :
              List.filter (fun e => decide (e ≠ .apply "PZero" []))
                (stripSCWrappersList elems) = [e] := by
            simpa [strippedNonZeroElems] using hshape
          unfold stripSCWrappers at hstrip
          rw [hshape'] at hstrip
          simp [hstrip]
      | cons e' es' =>
          have hshape' :
              List.filter (fun e => decide (e ≠ .apply "PZero" []))
                (stripSCWrappersList elems) = e :: e' :: es' := by
            simpa [strippedNonZeroElems] using hshape
          unfold stripSCWrappers at hstrip
          rw [hshape'] at hstrip
          have : False := by
            simp [wrappedValue] at hstrip
          exact False.elim this

private theorem scDecodeWrappedValue_hashSet_of_strippedNonZeroElems
    {elems : List Pattern} {value : Atom}
    (h : strippedNonZeroElems elems = [wrappedValue value]) :
    scDecodeWrappedValue? (.collection .hashSet elems none) = some value := by
  unfold strippedNonZeroElems at h
  have h' :
      List.filter (fun e => !decide (e = .apply "PZero" []))
        (stripSCWrappersList elems) = [wrappedValue value] := by
    simpa using h
  unfold scDecodeWrappedValue?
  simp [stripSCWrappers]
  rw [h']
  simp [wrappedValue, patternToAtom_atomToPattern]

private theorem strippedNonZeroElems_eq_singleton_of_scDecodeWrappedValue_hashSet
    {elems : List Pattern} {value : Atom}
    (h : scDecodeWrappedValue? (.collection .hashSet elems none) = some value) :
    strippedNonZeroElems elems = [wrappedValue value] := by
  have hstrip :
      stripSCWrappers (.collection .hashSet elems none) = wrappedValue value :=
    stripSCWrappers_eq_wrappedValue_of_scDecodeWrappedValue_eq_some h
  cases hshape : strippedNonZeroElems elems with
  | nil =>
      have hshape' :
          List.filter (fun e => decide (e ≠ .apply "PZero" []))
            (stripSCWrappersList elems) = [] := by
        simpa [strippedNonZeroElems] using hshape
      unfold stripSCWrappers at hstrip
      rw [hshape'] at hstrip
      have : False := by
        simp [wrappedValue] at hstrip
      exact False.elim this
  | cons e es =>
      cases es with
      | nil =>
          have hshape' :
              List.filter (fun e => decide (e ≠ .apply "PZero" []))
                (stripSCWrappersList elems) = [e] := by
            simpa [strippedNonZeroElems] using hshape
          unfold stripSCWrappers at hstrip
          rw [hshape'] at hstrip
          simp [hstrip]
      | cons e' es' =>
          have hshape' :
              List.filter (fun e => decide (e ≠ .apply "PZero" []))
                (stripSCWrappersList elems) = e :: e' :: es' := by
            simpa [strippedNonZeroElems] using hshape
          unfold stripSCWrappers at hstrip
          rw [hshape'] at hstrip
          have : False := by
            simp [wrappedValue] at hstrip
          exact False.elim this

private theorem strippedNonZeroElems_eq_singleton_wrapped_of_pointwise
    {ps qs : List Pattern} {value : Atom}
    (hlen : ps.length = qs.length)
    (hzero : ∀ i (h₁ : i < ps.length) (h₂ : i < qs.length),
      stripSCWrappers (ps.get ⟨i, h₁⟩) = .apply "PZero" [] ↔
        stripSCWrappers (qs.get ⟨i, h₂⟩) = .apply "PZero" [])
    (hwrapped : ∀ i (h₁ : i < ps.length) (h₂ : i < qs.length),
      stripSCWrappers (ps.get ⟨i, h₁⟩) = wrappedValue value ↔
        stripSCWrappers (qs.get ⟨i, h₂⟩) = wrappedValue value)
    (hps : strippedNonZeroElems ps = [wrappedValue value]) :
    strippedNonZeroElems qs = [wrappedValue value] := by
  induction ps generalizing qs with
  | nil =>
      cases qs with
      | nil =>
          unfold strippedNonZeroElems at hps
          simp [stripSCWrappersList] at hps
      | cons q qs =>
          simp at hlen
  | cons p ps ih =>
      cases qs with
      | nil =>
          simp at hlen
      | cons q qs =>
          have hpqzero :
              stripSCWrappers p = .apply "PZero" [] ↔
                stripSCWrappers q = .apply "PZero" [] :=
            hzero 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
          have hpqwrapped :
              stripSCWrappers p = wrappedValue value ↔
                stripSCWrappers q = wrappedValue value :=
            hwrapped 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
          have hlen_tail : ps.length = qs.length := by
            simpa using Nat.succ.inj hlen
          have hzero_tail :
              ∀ i (h₁ : i < ps.length) (h₂ : i < qs.length),
                stripSCWrappers (ps.get ⟨i, h₁⟩) = .apply "PZero" [] ↔
                  stripSCWrappers (qs.get ⟨i, h₂⟩) = .apply "PZero" [] := by
            intro i h₁ h₂
            simpa using hzero (i + 1) (Nat.succ_lt_succ h₁) (Nat.succ_lt_succ h₂)
          have hwrapped_tail :
              ∀ i (h₁ : i < ps.length) (h₂ : i < qs.length),
                stripSCWrappers (ps.get ⟨i, h₁⟩) = wrappedValue value ↔
                  stripSCWrappers (qs.get ⟨i, h₂⟩) = wrappedValue value := by
            intro i h₁ h₂
            simpa using hwrapped (i + 1) (Nat.succ_lt_succ h₁) (Nat.succ_lt_succ h₂)
          by_cases hpzero : stripSCWrappers p = .apply "PZero" []
          · have hqzero : stripSCWrappers q = .apply "PZero" [] :=
              hpqzero.mp hpzero
            have hps_tail : strippedNonZeroElems ps = [wrappedValue value] := by
              simpa [strippedNonZeroElems, stripSCWrappersList, hpzero] using hps
            have hqs_tail : strippedNonZeroElems qs = [wrappedValue value] :=
              ih hlen_tail hzero_tail hwrapped_tail hps_tail
            simpa [strippedNonZeroElems, stripSCWrappersList, hqzero] using hqs_tail
          · have hpwrapped : stripSCWrappers p = wrappedValue value := by
              unfold strippedNonZeroElems at hps
              simp [stripSCWrappersList, hpzero] at hps
              exact hps.1
            have hqwrapped : stripSCWrappers q = wrappedValue value :=
              hpqwrapped.mp hpwrapped
            have hps_tail_nil : strippedNonZeroElems ps = [] := by
              unfold strippedNonZeroElems at hps ⊢
              simp [stripSCWrappersList, hpzero] at hps
              exact strippedNonZeroElems_eq_nil_iff_all_zero.mpr hps.2
            have hqs_tail_nil : strippedNonZeroElems qs = [] :=
              (strippedNonZeroElems_eq_nil_iff_of_pointwise_zero
                hlen_tail hzero_tail).mp hps_tail_nil
            unfold strippedNonZeroElems
            simp [stripSCWrappersList, hqwrapped, wrappedValue]
            exact strippedNonZeroElems_eq_nil_iff_all_zero.mp hqs_tail_nil

private theorem strippedNonZeroElems_eq_singleton_wrapped_iff_of_pointwise
    {ps qs : List Pattern} {value : Atom}
    (hlen : ps.length = qs.length)
    (hzero : ∀ i (h₁ : i < ps.length) (h₂ : i < qs.length),
      stripSCWrappers (ps.get ⟨i, h₁⟩) = .apply "PZero" [] ↔
        stripSCWrappers (qs.get ⟨i, h₂⟩) = .apply "PZero" [])
    (hwrapped : ∀ i (h₁ : i < ps.length) (h₂ : i < qs.length),
      stripSCWrappers (ps.get ⟨i, h₁⟩) = wrappedValue value ↔
        stripSCWrappers (qs.get ⟨i, h₂⟩) = wrappedValue value) :
    strippedNonZeroElems ps = [wrappedValue value] ↔
      strippedNonZeroElems qs = [wrappedValue value] := by
  constructor
  · exact strippedNonZeroElems_eq_singleton_wrapped_of_pointwise
      hlen hzero hwrapped
  · exact strippedNonZeroElems_eq_singleton_wrapped_of_pointwise
      (ps := qs) (qs := ps) hlen.symm
      (fun i hq hp => (hzero i hp hq).symm)
      (fun i hq hp => (hwrapped i hp hq).symm)

private theorem scDecodeWrappedValue_hashBag_eq_some_iff_of_pointwise
    {ps qs : List Pattern} {value : Atom}
    (hlen : ps.length = qs.length)
    (hzero : ∀ i (h₁ : i < ps.length) (h₂ : i < qs.length),
      stripSCWrappers (ps.get ⟨i, h₁⟩) = .apply "PZero" [] ↔
        stripSCWrappers (qs.get ⟨i, h₂⟩) = .apply "PZero" [])
    (hwrapped : ∀ i (h₁ : i < ps.length) (h₂ : i < qs.length),
      stripSCWrappers (ps.get ⟨i, h₁⟩) = wrappedValue value ↔
        stripSCWrappers (qs.get ⟨i, h₂⟩) = wrappedValue value) :
    scDecodeWrappedValue? (.collection .hashBag ps none) = some value ↔
      scDecodeWrappedValue? (.collection .hashBag qs none) = some value := by
  constructor
  · intro hps
    exact scDecodeWrappedValue_hashBag_of_strippedNonZeroElems
      ((strippedNonZeroElems_eq_singleton_wrapped_iff_of_pointwise
          hlen hzero hwrapped).mp
        (strippedNonZeroElems_eq_singleton_of_scDecodeWrappedValue_hashBag hps))
  · intro hqs
    exact scDecodeWrappedValue_hashBag_of_strippedNonZeroElems
      ((strippedNonZeroElems_eq_singleton_wrapped_iff_of_pointwise
          hlen hzero hwrapped).mpr
        (strippedNonZeroElems_eq_singleton_of_scDecodeWrappedValue_hashBag hqs))

private theorem scDecodeWrappedValue_hashSet_eq_some_iff_of_pointwise
    {ps qs : List Pattern} {value : Atom}
    (hlen : ps.length = qs.length)
    (hzero : ∀ i (h₁ : i < ps.length) (h₂ : i < qs.length),
      stripSCWrappers (ps.get ⟨i, h₁⟩) = .apply "PZero" [] ↔
        stripSCWrappers (qs.get ⟨i, h₂⟩) = .apply "PZero" [])
    (hwrapped : ∀ i (h₁ : i < ps.length) (h₂ : i < qs.length),
      stripSCWrappers (ps.get ⟨i, h₁⟩) = wrappedValue value ↔
        stripSCWrappers (qs.get ⟨i, h₂⟩) = wrappedValue value) :
    scDecodeWrappedValue? (.collection .hashSet ps none) = some value ↔
      scDecodeWrappedValue? (.collection .hashSet qs none) = some value := by
  constructor
  · intro hps
    exact scDecodeWrappedValue_hashSet_of_strippedNonZeroElems
      ((strippedNonZeroElems_eq_singleton_wrapped_iff_of_pointwise
          hlen hzero hwrapped).mp
        (strippedNonZeroElems_eq_singleton_of_scDecodeWrappedValue_hashSet hps))
  · intro hqs
    exact scDecodeWrappedValue_hashSet_of_strippedNonZeroElems
      ((strippedNonZeroElems_eq_singleton_wrapped_iff_of_pointwise
          hlen hzero hwrapped).mpr
        (strippedNonZeroElems_eq_singleton_of_scDecodeWrappedValue_hashSet hqs))

private theorem scDecodeWrappedValue_hashBag_eq_of_pointwise_wrapped
    {ps qs : List Pattern}
    (hlen : ps.length = qs.length)
    (hzero : ∀ i (h₁ : i < ps.length) (h₂ : i < qs.length),
      stripSCWrappers (ps.get ⟨i, h₁⟩) = .apply "PZero" [] ↔
        stripSCWrappers (qs.get ⟨i, h₂⟩) = .apply "PZero" [])
    (hwrapped : ∀ value i (h₁ : i < ps.length) (h₂ : i < qs.length),
      stripSCWrappers (ps.get ⟨i, h₁⟩) = wrappedValue value ↔
        stripSCWrappers (qs.get ⟨i, h₂⟩) = wrappedValue value) :
    scDecodeWrappedValue? (.collection .hashBag ps none) =
      scDecodeWrappedValue? (.collection .hashBag qs none) := by
  cases hps : scDecodeWrappedValue? (.collection .hashBag ps none) with
  | none =>
      cases hqs : scDecodeWrappedValue? (.collection .hashBag qs none) with
      | none =>
          rfl
      | some value =>
          have hsome :
              scDecodeWrappedValue? (.collection .hashBag ps none) = some value :=
            (scDecodeWrappedValue_hashBag_eq_some_iff_of_pointwise
              (value := value) hlen hzero (hwrapped value)).mpr hqs
          rw [hps] at hsome
          cases hsome
  | some value =>
      have hsome :
          scDecodeWrappedValue? (.collection .hashBag qs none) = some value :=
        (scDecodeWrappedValue_hashBag_eq_some_iff_of_pointwise
          (value := value) hlen hzero (hwrapped value)).mp hps
      rw [hsome]

private theorem scDecodeWrappedValue_hashSet_eq_of_pointwise_wrapped
    {ps qs : List Pattern}
    (hlen : ps.length = qs.length)
    (hzero : ∀ i (h₁ : i < ps.length) (h₂ : i < qs.length),
      stripSCWrappers (ps.get ⟨i, h₁⟩) = .apply "PZero" [] ↔
        stripSCWrappers (qs.get ⟨i, h₂⟩) = .apply "PZero" [])
    (hwrapped : ∀ value i (h₁ : i < ps.length) (h₂ : i < qs.length),
      stripSCWrappers (ps.get ⟨i, h₁⟩) = wrappedValue value ↔
        stripSCWrappers (qs.get ⟨i, h₂⟩) = wrappedValue value) :
    scDecodeWrappedValue? (.collection .hashSet ps none) =
      scDecodeWrappedValue? (.collection .hashSet qs none) := by
  cases hps : scDecodeWrappedValue? (.collection .hashSet ps none) with
  | none =>
      cases hqs : scDecodeWrappedValue? (.collection .hashSet qs none) with
      | none =>
          rfl
      | some value =>
          have hsome :
              scDecodeWrappedValue? (.collection .hashSet ps none) = some value :=
            (scDecodeWrappedValue_hashSet_eq_some_iff_of_pointwise
              (value := value) hlen hzero (hwrapped value)).mpr hqs
          rw [hps] at hsome
          cases hsome
  | some value =>
      have hsome :
          scDecodeWrappedValue? (.collection .hashSet qs none) = some value :=
        (scDecodeWrappedValue_hashSet_eq_some_iff_of_pointwise
          (value := value) hlen hzero (hwrapped value)).mp hps
      rw [hsome]

private theorem scDecodeWrappedValue_hashBag_eq_of_perm
    {elems₁ elems₂ : List Pattern} (hperm : elems₁.Perm elems₂) :
    scDecodeWrappedValue? (.collection .hashBag elems₁ none) =
      scDecodeWrappedValue? (.collection .hashBag elems₂ none) := by
  cases h₁ : scDecodeWrappedValue? (.collection .hashBag elems₁ none) with
  | none =>
      cases h₂ : scDecodeWrappedValue? (.collection .hashBag elems₂ none) with
      | none =>
          rfl
      | some value =>
          have hs₂ :
              strippedNonZeroElems elems₂ = [wrappedValue value] :=
            strippedNonZeroElems_eq_singleton_of_scDecodeWrappedValue_hashBag h₂
          have hsperm : (strippedNonZeroElems elems₁).Perm [wrappedValue value] := by
            simpa [hs₂] using strippedNonZeroElems_perm hperm
          have hs₁ :
              strippedNonZeroElems elems₁ = [wrappedValue value] := by
            simp at hsperm
            exact hsperm
          have hsome :
              scDecodeWrappedValue? (.collection .hashBag elems₁ none) = some value :=
            scDecodeWrappedValue_hashBag_of_strippedNonZeroElems hs₁
          rw [h₁] at hsome
          cases hsome
  | some value =>
      have hs₁ :
          strippedNonZeroElems elems₁ = [wrappedValue value] :=
        strippedNonZeroElems_eq_singleton_of_scDecodeWrappedValue_hashBag h₁
      cases h₂ : scDecodeWrappedValue? (.collection .hashBag elems₂ none) with
      | none =>
          have hsperm : [wrappedValue value].Perm (strippedNonZeroElems elems₂) := by
            simpa [hs₁] using strippedNonZeroElems_perm hperm
          have hs₂ :
              strippedNonZeroElems elems₂ = [wrappedValue value] := by
            simp at hsperm
            symm
            exact hsperm
          have hsome :
              scDecodeWrappedValue? (.collection .hashBag elems₂ none) = some value :=
            scDecodeWrappedValue_hashBag_of_strippedNonZeroElems hs₂
          rw [h₂] at hsome
          cases hsome
      | some value' =>
          have hs₂ :
              strippedNonZeroElems elems₂ = [wrappedValue value'] :=
            strippedNonZeroElems_eq_singleton_of_scDecodeWrappedValue_hashBag h₂
          have hsperm : [wrappedValue value].Perm [wrappedValue value'] := by
            simpa [hs₁, hs₂] using strippedNonZeroElems_perm hperm
          simp at hsperm
          exact congrArg some (wrappedValue_injective hsperm)

private theorem scDecodeWrappedValue_hashSet_eq_of_perm
    {elems₁ elems₂ : List Pattern} (hperm : elems₁.Perm elems₂) :
    scDecodeWrappedValue? (.collection .hashSet elems₁ none) =
      scDecodeWrappedValue? (.collection .hashSet elems₂ none) := by
  cases h₁ : scDecodeWrappedValue? (.collection .hashSet elems₁ none) with
  | none =>
      cases h₂ : scDecodeWrappedValue? (.collection .hashSet elems₂ none) with
      | none =>
          rfl
      | some value =>
          have hs₂ :
              strippedNonZeroElems elems₂ = [wrappedValue value] :=
            strippedNonZeroElems_eq_singleton_of_scDecodeWrappedValue_hashSet h₂
          have hsperm : (strippedNonZeroElems elems₁).Perm [wrappedValue value] := by
            simpa [hs₂] using strippedNonZeroElems_perm hperm
          have hs₁ :
              strippedNonZeroElems elems₁ = [wrappedValue value] := by
            simp at hsperm
            exact hsperm
          have hsome :
              scDecodeWrappedValue? (.collection .hashSet elems₁ none) = some value :=
            scDecodeWrappedValue_hashSet_of_strippedNonZeroElems hs₁
          rw [h₁] at hsome
          cases hsome
  | some value =>
      have hs₁ :
          strippedNonZeroElems elems₁ = [wrappedValue value] :=
        strippedNonZeroElems_eq_singleton_of_scDecodeWrappedValue_hashSet h₁
      cases h₂ : scDecodeWrappedValue? (.collection .hashSet elems₂ none) with
      | none =>
          have hsperm : [wrappedValue value].Perm (strippedNonZeroElems elems₂) := by
            simpa [hs₁] using strippedNonZeroElems_perm hperm
          have hs₂ :
              strippedNonZeroElems elems₂ = [wrappedValue value] := by
            simp at hsperm
            symm
            exact hsperm
          have hsome :
              scDecodeWrappedValue? (.collection .hashSet elems₂ none) = some value :=
            scDecodeWrappedValue_hashSet_of_strippedNonZeroElems hs₂
          rw [h₂] at hsome
          cases hsome
      | some value' =>
          have hs₂ :
              strippedNonZeroElems elems₂ = [wrappedValue value'] :=
            strippedNonZeroElems_eq_singleton_of_scDecodeWrappedValue_hashSet h₂
          have hsperm : [wrappedValue value].Perm [wrappedValue value'] := by
            simpa [hs₁, hs₂] using strippedNonZeroElems_perm hperm
          simp at hsperm
          exact congrArg some (wrappedValue_injective hsperm)

private theorem scDecodeWrappedValue_par_singleton (p : Pattern) :
    scDecodeWrappedValue? (.collection .hashBag [p] none) =
      scDecodeWrappedValue? p := by
  by_cases hzero : stripSCWrappers p = .apply "PZero" []
  · simp [scDecodeWrappedValue?, stripSCWrappers, stripSCWrappersList, hzero]
  · simp [scDecodeWrappedValue?, stripSCWrappers, stripSCWrappersList, hzero]

private theorem scDecodeWrappedValue_par_nil_left (p : Pattern) :
    scDecodeWrappedValue? (.collection .hashBag [.apply "PZero" [], p] none) =
      scDecodeWrappedValue? p := by
  by_cases hzero : stripSCWrappers p = .apply "PZero" []
  · simp [scDecodeWrappedValue?, stripSCWrappers, stripSCWrappersList, hzero]
  · simp [scDecodeWrappedValue?, stripSCWrappers, stripSCWrappersList, hzero]

private theorem scDecodeWrappedValue_par_nil_right (p : Pattern) :
    scDecodeWrappedValue? (.collection .hashBag [p, .apply "PZero" []] none) =
      scDecodeWrappedValue? p := by
  by_cases hzero : stripSCWrappers p = .apply "PZero" []
  · simp [scDecodeWrappedValue?, stripSCWrappers, stripSCWrappersList, hzero]
  · simp [scDecodeWrappedValue?, stripSCWrappers, stripSCWrappersList, hzero]

private theorem scDecodeWrappedValue_par_comm (p q : Pattern) :
    scDecodeWrappedValue? (.collection .hashBag [p, q] none) =
      scDecodeWrappedValue? (.collection .hashBag [q, p] none) := by
  exact scDecodeWrappedValue_hashBag_eq_of_perm
    (List.Perm.symm (List.Perm.swap p q []))

private theorem scDecodeWrappedValue_quoteDrop_general (p : Pattern) :
    scDecodeWrappedValue? (.apply "NQuote" [.apply "PDrop" [p]]) =
      scDecodeWrappedValue? p := by
  simp [scDecodeWrappedValue?, stripSCWrappers]

private theorem scDecodeWrappedValue_par_assoc (p q r : Pattern) :
    scDecodeWrappedValue?
      (.collection .hashBag [.collection .hashBag [p, q] none, r] none) =
    scDecodeWrappedValue?
      (.collection .hashBag [p, .collection .hashBag [q, r] none] none) := by
  by_cases hp : stripSCWrappers p = .apply "PZero" []
  · by_cases hq : stripSCWrappers q = .apply "PZero" []
    · by_cases hr : stripSCWrappers r = .apply "PZero" []
      · simp [scDecodeWrappedValue?, stripSCWrappers, stripSCWrappersList, hp, hq, hr]
      · simp [scDecodeWrappedValue?, stripSCWrappers, stripSCWrappersList, hp, hq, hr]
    · by_cases hr : stripSCWrappers r = .apply "PZero" []
      · simp [scDecodeWrappedValue?, stripSCWrappers, stripSCWrappersList, hp, hq, hr]
      · simp [scDecodeWrappedValue?, stripSCWrappers, stripSCWrappersList, hp, hq, hr]
  · by_cases hq : stripSCWrappers q = .apply "PZero" []
    · by_cases hr : stripSCWrappers r = .apply "PZero" []
      · simp [scDecodeWrappedValue?, stripSCWrappers, stripSCWrappersList, hp, hq, hr]
      · simp [scDecodeWrappedValue?, stripSCWrappers, stripSCWrappersList, hp, hq, hr]
    · by_cases hr : stripSCWrappers r = .apply "PZero" []
      · simp [scDecodeWrappedValue?, stripSCWrappers, stripSCWrappersList, hp, hq, hr]
      · simp [scDecodeWrappedValue?, stripSCWrappers, stripSCWrappersList, hp, hq, hr]

private theorem decodeWrappedValues?_multiset_eq_of_perm
    {ps qs : List Pattern} (hperm : ps.Perm qs) :
    (decodeWrappedValues? ps).map (fun xs => (xs : Multiset Atom)) =
      (decodeWrappedValues? qs).map (fun xs => (xs : Multiset Atom)) := by
  induction hperm with
  | nil =>
      rfl
  | @cons p ps qs hperm ih =>
      cases hp : decodeWrappedValue? p <;>
      simp [decodeWrappedValues?, hp]
      rename_i a
      cases hs : decodeWrappedValues? ps <;>
      cases hq : decodeWrappedValues? qs <;>
      simp [hs, hq] at ih ⊢
      · rename_i xs ys
        exact ih
  | @swap p q ps =>
      cases hp : decodeWrappedValue? p <;>
      cases hq : decodeWrappedValue? q <;>
      cases hs : decodeWrappedValues? ps <;>
      simp [decodeWrappedValues?, hp, hq, hs]
      · rename_i a b xs
        exact List.Perm.swap a b xs
  | @trans _ _ _ h₁ h₂ ih₁ ih₂ =>
      exact ih₁.trans ih₂

private theorem decodeWrappedValues?_length_eq
    {ps : List Pattern} {xs : List Atom}
    (h : decodeWrappedValues? ps = some xs) :
    xs.length = ps.length := by
  induction ps generalizing xs with
  | nil =>
      simp [decodeWrappedValues?] at h
      cases h
      rfl
  | cons p ps ih =>
      simp only [decodeWrappedValues?] at h
      cases hp : decodeWrappedValue? p <;> simp [hp] at h
      rename_i a
      cases hs : decodeWrappedValues? ps <;> simp [hs] at h
      rename_i ys
      subst xs
      simp [ih hs]

private theorem decodeWrappedValues?_singleton_source_length
    {ps : List Pattern} {xs : List Atom} {value : Atom}
    (hdec : decodeWrappedValues? ps = some xs)
    (hms : (xs : Multiset Atom) = ({value} : Multiset Atom)) :
    ps.length = 1 := by
  have hperm : xs.Perm [value] := by
    exact Multiset.coe_eq_coe.mp (by simpa using hms)
  have hxs : xs.length = 1 := by
    simpa using hperm.length_eq
  have hlen : xs.length = ps.length := decodeWrappedValues?_length_eq hdec
  omega

private theorem decodeWrappedValues?_singleton_source
    {ps : List Pattern} {xs : List Atom} {value : Atom}
    (hdec : decodeWrappedValues? ps = some xs)
    (hms : (xs : Multiset Atom) = ({value} : Multiset Atom)) :
    ∃ p, ps = [p] ∧ decodeWrappedValue? p = some value := by
  have hlen : ps.length = 1 :=
    decodeWrappedValues?_singleton_source_length hdec hms
  cases ps with
  | nil =>
      simp at hlen
  | cons p ps =>
      cases ps with
      | nil =>
          simp only [decodeWrappedValues?] at hdec
          cases hp : decodeWrappedValue? p <;> simp [hp] at hdec
          rename_i value'
          cases hdec
          have hvalue : value' = value := by
            have hperm : [value'].Perm [value] := by
              exact Multiset.coe_eq_coe.mp (by simpa using hms)
            simpa using hperm
          subst hvalue
          exact ⟨p, rfl, hp⟩
      | cons p' ps' =>
          simp at hlen

private theorem decodeWrappedValues?_singleton_source_eq
    {ps : List Pattern} {xs : List Atom} {value : Atom}
    (hdec : decodeWrappedValues? ps = some xs)
    (hms : (xs : Multiset Atom) = ({value} : Multiset Atom)) :
    ps = [wrappedValue value] := by
  rcases decodeWrappedValues?_singleton_source hdec hms with
    ⟨p, hps, hp⟩
  rw [hps, eq_wrappedValue_of_decodeWrappedValue_eq_some hp]

theorem ioCount_natToPattern_zero (n : Nat) :
    ioCount (natToPattern n) = 0 := by
  induction n with
  | zero =>
      simp [natToPattern, ioCount]
  | succ n ih =>
      simp [natToPattern, ioCount, ih]

mutual

private theorem ioCount_atomToPattern_zero :
    ∀ a : Atom, ioCount (atomToPattern a) = 0
  | .symbol s => by
      simp [atomToPattern, ioCount]
  | .var v => by
      simp [atomToPattern, ioCount]
  | .grounded g => by
      cases g with
      | int i =>
          cases i using Int.rec with
          | ofNat n =>
              simpa [atomToPattern, groundedValueToPattern, ioCount] using
                ioCount_natToPattern_zero n
          | negSucc n =>
              simpa [atomToPattern, groundedValueToPattern, ioCount] using
                ioCount_natToPattern_zero n
      | string s =>
          simp [atomToPattern, groundedValueToPattern, ioCount]
      | bool b =>
          cases b <;> simp [atomToPattern, groundedValueToPattern, ioCount]
      | custom ty data =>
          simp [atomToPattern, groundedValueToPattern, ioCount]
  | .expression es => by
      simpa [atomToPattern, ioCount] using
        ioCount_atomPatterns_zero es
termination_by a => sizeOf a

private theorem ioCount_atomPatterns_zero :
    ∀ xs : List Atom, (xs.map atomToPattern |>.map ioCount).sum = 0
  | [] => by
      simp
  | x :: xs => by
      simp [ioCount_atomToPattern_zero x]
      simpa [Function.comp] using ioCount_atomPatterns_zero xs
termination_by xs => sizeOf xs

end

theorem ioCount_wrappedValue_zero (value : Atom) :
    ioCount (wrappedValue value) = 0 := by
  simpa [wrappedValue, ioCount] using ioCount_atomToPattern_zero value

theorem ioCount_deferredPayload_zero (payload : Atom) :
    ioCount (deferredPayload payload) = 0 := by
  simpa [deferredPayload, ioCount] using ioCount_atomToPattern_zero payload

/-- A certified top-level HE result for a deferred Rhometta payload.

Bindings are existential here because the current Rhometta runtime surface
returns top-level atoms after the HE evaluator drops bindings at the edge. -/
def CertifiedPayloadResult
    (space : Space) (dispatch : GroundedDispatch)
    (payload value : Atom) : Prop :=
  ∃ b, EvalAtomCertified
    space dispatch payload Atom.undefinedType Bindings.empty (value, b)

private theorem certifiedPayloadResult_of_payload_eq
    {space : Space} {dispatch : GroundedDispatch}
    {payload payload' value : Atom}
    (hpayload : payload = payload')
    (hcert : CertifiedPayloadResult space dispatch payload' value) :
    CertifiedPayloadResult space dispatch payload value := by
  subst hpayload
  exact hcert

private theorem certifiedPayloadResult_of_value_eq
    {space : Space} {dispatch : GroundedDispatch}
    {payload value value' : Atom}
    (hvalue : value = value')
    (hcert : CertifiedPayloadResult space dispatch payload value') :
    CertifiedPayloadResult space dispatch payload value := by
  subst hvalue
  exact hcert

/-- Eval-at-COMM fires only on canonical shells, matching the runtime's
normalize-then-fire discipline while keeping structural-congruence wandering
available around the step itself. -/
def EvalCommCanonicalShell
    (body : Pattern) (payload : Atom) : Prop :=
  semanticNormalizeProc body = body ∧
    strictCoreCommBody body = true ∧
    semanticNormalizeProc (deferredPayload payload) = deferredPayload payload

theorem evalCommCanonicalShell_dropBody
    {payload : Atom} :
    EvalCommCanonicalShell (.apply "PDrop" [.bvar 0]) payload := by
  refine ⟨?_, ?_, semanticNormalizeProc_deferredPayload payload⟩
  · simp [semanticNormalizeProc, semanticNormalizeName]
  · simp [strictCoreCommBody, rhoProcCoreShape, rhoNameCoreShape,
      noBoundUnderQuote, noBoundUnderQuoteList]

/-- Output payloads that are structurally congruent to a deferred Rhometta
payload must not take the ordinary core COMM route. This closes SC shells such
as singleton-bag wrappers around `rho:eval-payload`. -/
def DeferredPayloadLike (q : Pattern) : Prop :=
  ∃ payload, StructuralCongruence q (deferredPayload payload)

theorem deferredPayloadLike_singleton_shell (payload : Atom) :
    DeferredPayloadLike (.collection .hashBag [deferredPayload payload] none) := by
  refine ⟨payload, ?_⟩
  simpa using StructuralCongruence.par_singleton (deferredPayload payload)

theorem deferredPayloadLike_iff_of_structuralCongruence
    {p q : Pattern} (hsc : StructuralCongruence p q) :
    DeferredPayloadLike p ↔ DeferredPayloadLike q := by
  constructor
  · rintro ⟨payload, hp⟩
    exact ⟨payload,
      StructuralCongruence.trans _ _ _
        (StructuralCongruence.symm _ _ hsc) hp⟩
  · rintro ⟨payload, hq⟩
    exact ⟨payload, StructuralCongruence.trans _ _ _ hsc hq⟩

theorem deferredPayloadLike_of_output_apply_cong
    {args₁ args₂ : List Pattern}
    (hlen : args₁.length = args₂.length)
    (hpoint : ∀ i (h₁ : i < args₁.length) (h₂ : i < args₂.length),
      StructuralCongruence (args₁.get ⟨i, h₁⟩) (args₂.get ⟨i, h₂⟩))
    {n q chan : Pattern} {payload : Atom}
    (hargs₁ : args₁ = [n, q])
    (hargs₂ : args₂ = [chan, deferredPayload payload]) :
    DeferredPayloadLike q := by
  subst hargs₁ hargs₂
  have hpayload : StructuralCongruence q (deferredPayload payload) := by
    simpa using hpoint 1 (by simp) (by simp)
  exact (deferredPayloadLike_iff_of_structuralCongruence hpayload).mpr
    ⟨payload, StructuralCongruence.refl _⟩

/-- Transport structural congruence to a fixed target. -/
private theorem structuralCongruence_to_fixed_iff
    {p q r : Pattern} (hsc : StructuralCongruence p q) :
    StructuralCongruence p r ↔ StructuralCongruence q r := by
  constructor
  · intro h
    exact StructuralCongruence.trans _ _ _
      (StructuralCongruence.symm _ _ hsc) h
  · intro h
    exact StructuralCongruence.trans _ _ _ hsc h

/-- Ordinary rho core steps that would consume an explicit Rhometta eval
payload are classified separately so `RhometaReduces.core` can exclude exactly
that route while preserving unrelated core reductions. -/
inductive CoreConsumesEvalPayload :
    {p q : Pattern} → Reduction.Reduces p q → Prop where
  | comm {n body q : Pattern} {rest : List Pattern} :
      DeferredPayloadLike q →
      CoreConsumesEvalPayload
        (Reduction.Reduces.comm
          (n := n) (q := q) (p := body) (rest := rest))
  | equiv {p p' q q' : Pattern}
      {hsc₁ : StructuralCongruence p p'}
      {hred : Reduction.Reduces p' q'}
      {hsc₂ : StructuralCongruence q' q} :
      CoreConsumesEvalPayload hred →
      CoreConsumesEvalPayload
        (Reduction.Reduces.equiv
          (p := p) (p' := p') (q := q) (q' := q')
          hsc₁ hred hsc₂)
  | par {p q : Pattern} {rest : List Pattern}
      {hred : Reduction.Reduces p q} :
      CoreConsumesEvalPayload hred →
      CoreConsumesEvalPayload
        (Reduction.Reduces.par (p := p) (q := q) (rest := rest) hred)
  | par_any {p q : Pattern} {before after : List Pattern}
      {hred : Reduction.Reduces p q} :
      CoreConsumesEvalPayload hred →
      CoreConsumesEvalPayload
        (Reduction.Reduces.par_any
          (p := p) (q := q) (before := before) (after := after) hred)
  | par_set {p q : Pattern} {rest : List Pattern}
      {hred : Reduction.Reduces p q} :
      CoreConsumesEvalPayload hred →
      CoreConsumesEvalPayload
        (Reduction.Reduces.par_set (p := p) (q := q) (rest := rest) hred)
  | par_set_any {p q : Pattern} {before after : List Pattern}
      {hred : Reduction.Reduces p q} :
      CoreConsumesEvalPayload hred →
      CoreConsumesEvalPayload
        (Reduction.Reduces.par_set_any
          (p := p) (q := q) (before := before) (after := after) hred)

theorem coreConsumesEvalPayload_singleton_shell
    {n body : Pattern} {rest : List Pattern} {payload : Atom} :
    CoreConsumesEvalPayload
      (Reduction.Reduces.comm
        (n := n)
        (q := .collection .hashBag [deferredPayload payload] none)
        (p := body)
        (rest := rest)) := by
  exact CoreConsumesEvalPayload.comm (deferredPayloadLike_singleton_shell payload)

mutual

/-- Every `POutput` anywhere in the syntax tree carries a deferred Rhometta
payload marker. This is the output-side structural invariant of the
drop-observer shell. -/
private def OutputsDeferred : Pattern → Prop
  | .bvar _ => True
  | .fvar _ => True
  | .apply "POutput" [_, q] => DeferredPayloadLike q
  | .apply "PInput" _ => True
  | .apply _ args => OutputsDeferredList args
  | .lambda _ body => OutputsDeferred body
  | .multiLambda _ _ body => OutputsDeferred body
  | .subst body repl => OutputsDeferred body ∧ OutputsDeferred repl
  | .collection _ elems _ => OutputsDeferredList elems

/-- List-level helper for `OutputsDeferred`. -/
private def OutputsDeferredList : List Pattern → Prop
  | [] => True
  | p :: ps => OutputsDeferred p ∧ OutputsDeferredList ps

end

private theorem outputsDeferredList_iff_of_pointwise
    {ps qs : List Pattern}
    (hlen : ps.length = qs.length)
    (hpoint : ∀ i (h₁ : i < ps.length) (h₂ : i < qs.length),
      OutputsDeferred (ps.get ⟨i, h₁⟩) ↔
        OutputsDeferred (qs.get ⟨i, h₂⟩)) :
    OutputsDeferredList ps ↔ OutputsDeferredList qs := by
  induction ps generalizing qs with
  | nil =>
      cases qs with
      | nil => simp [OutputsDeferredList]
      | cons q qs =>
          simp at hlen
  | cons p ps ih =>
      cases qs with
      | nil =>
          simp at hlen
      | cons q qs =>
          have hpq : OutputsDeferred p ↔ OutputsDeferred q :=
            hpoint 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
          have hrest : OutputsDeferredList ps ↔ OutputsDeferredList qs := by
            apply ih
            · simpa using Nat.succ.inj hlen
            · intro i h₁ h₂
              simpa using hpoint (i + 1) (Nat.succ_lt_succ h₁) (Nat.succ_lt_succ h₂)
          constructor <;> intro h
          · exact ⟨hpq.mp h.1, hrest.mp h.2⟩
          · exact ⟨hpq.mpr h.1, hrest.mpr h.2⟩

private theorem outputsDeferredList_iff_of_perm
    {ps qs : List Pattern} (hperm : ps.Perm qs) :
    OutputsDeferredList ps ↔ OutputsDeferredList qs := by
  induction hperm with
  | nil =>
      simp [OutputsDeferredList]
  | @cons p ps qs hperm ih =>
      simp [OutputsDeferredList, ih]
  | swap p q ps =>
      simp [OutputsDeferredList, and_left_comm]
  | trans _ _ ih₁ ih₂ =>
      exact ih₁.trans ih₂

private theorem outputsDeferredList_append_iff
    {ps qs : List Pattern} :
    OutputsDeferredList (ps ++ qs) ↔
      OutputsDeferredList ps ∧ OutputsDeferredList qs := by
  induction ps with
  | nil =>
      simp [OutputsDeferredList]
  | cons p ps ih =>
      simp [OutputsDeferredList, ih, and_assoc]

private theorem outputsDeferred_of_outputsDeferredList_middle
    {before after : List Pattern} {p : Pattern}
    (h : OutputsDeferredList (before ++ [p] ++ after)) :
    OutputsDeferred p := by
  induction before with
  | nil =>
      simpa [OutputsDeferredList] using h.1
  | cons b before ih =>
      have htail : OutputsDeferredList (before ++ [p] ++ after) := by
        simpa [OutputsDeferredList] using h.2
      exact ih htail

private theorem outputsDeferred_iff_of_structuralCongruence
    {p q : Pattern} (hsc : StructuralCongruence p q) :
    OutputsDeferred p ↔ OutputsDeferred q := by
  induction hsc with
  | alpha _ _ h =>
      subst h
      rfl
  | refl _ =>
      rfl
  | symm _ _ _ ih =>
      exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ =>
      exact ih₁.trans ih₂
  | par_singleton p =>
      simp [OutputsDeferred, OutputsDeferredList]
  | par_nil_left p =>
      simp [OutputsDeferred, OutputsDeferredList]
  | par_nil_right p =>
      simp [OutputsDeferred, OutputsDeferredList]
  | par_comm p q =>
      simp [OutputsDeferred, OutputsDeferredList, and_comm]
  | par_assoc p q r =>
      simp [OutputsDeferred, OutputsDeferredList, and_assoc, and_comm]
  | par_cong ps qs hlen _ ih =>
      simpa [OutputsDeferred] using outputsDeferredList_iff_of_pointwise hlen ih
  | par_flatten ps qs =>
      simp [OutputsDeferred, OutputsDeferredList, outputsDeferredList_append_iff]
  | par_perm ps qs hperm =>
      simpa [OutputsDeferred] using outputsDeferredList_iff_of_perm hperm
  | set_perm ps qs hperm =>
      simpa [OutputsDeferred] using outputsDeferredList_iff_of_perm hperm
  | set_cong ps qs hlen _ ih =>
      simpa [OutputsDeferred] using outputsDeferredList_iff_of_pointwise hlen ih
  | lambda_cong _ _ _ _ ih =>
      simpa [OutputsDeferred] using ih
  | apply_cong f args₁ args₂ hlen hpt ih =>
      by_cases hfout : f = "POutput"
      · subst hfout
        cases args₁ with
        | nil =>
            cases args₂ with
            | nil =>
                simp [OutputsDeferred, OutputsDeferredList]
            | cons a as =>
                simp at hlen
        | cons a as =>
            cases as with
            | nil =>
                cases args₂ with
                | nil =>
                    simp at hlen
                | cons b bs =>
                    cases bs with
                    | nil =>
                        simpa [OutputsDeferred, OutputsDeferredList] using
                          outputsDeferredList_iff_of_pointwise hlen ih
                    | cons c cs =>
                        simp at hlen
            | cons b bs =>
                cases bs with
                | nil =>
                    cases args₂ with
                    | nil =>
                        simp at hlen
                    | cons a' as' =>
                        cases as' with
                        | nil =>
                            simp at hlen
                        | cons b' bs' =>
                            cases bs' with
                            | nil =>
                                have hq : StructuralCongruence b b' := by
                                  simpa using hpt 1 (by simp) (by simp)
                                simpa [OutputsDeferred] using
                                  (deferredPayloadLike_iff_of_structuralCongruence hq)
                            | cons c' cs' =>
                                simp at hlen
                | cons c cs =>
                    cases args₂ with
                    | nil =>
                        simp at hlen
                    | cons a' as' =>
                        cases as' with
                        | nil =>
                            simp at hlen
                        | cons b' bs' =>
                            cases bs' with
                            | nil =>
                                simp at hlen
                            | cons c' cs' =>
                                simpa [OutputsDeferred] using
                                  outputsDeferredList_iff_of_pointwise hlen ih
      · by_cases hfin : f = "PInput"
        · simp [OutputsDeferred, hfin]
        · simpa [OutputsDeferred, hfout, hfin] using
            outputsDeferredList_iff_of_pointwise hlen ih
  | collection_general_cong ct ps qs g hlen _ ih =>
      simpa [OutputsDeferred] using outputsDeferredList_iff_of_pointwise hlen ih
  | multiLambda_cong _ _ _ _ _ ih =>
      simpa [OutputsDeferred] using ih
  | subst_cong _ _ _ _ _ _ ih₁ ih₂ =>
      simp [OutputsDeferred, ih₁, ih₂]
  | quote_drop n =>
      simp [OutputsDeferred, OutputsDeferredList]

mutual

/-- Every `POutput` anywhere in the syntax tree carries the specific deferred
payload marker from the target drop-observer shell. -/
private def OutputsPayload (payload : Atom) : Pattern → Prop
  | .bvar _ => True
  | .fvar _ => True
  | .apply "POutput" [_, q] => StructuralCongruence q (deferredPayload payload)
  | .apply "PInput" _ => True
  | .apply _ args => OutputsPayloadList payload args
  | .lambda _ body => OutputsPayload payload body
  | .multiLambda _ _ body => OutputsPayload payload body
  | .subst body repl => OutputsPayload payload body ∧ OutputsPayload payload repl
  | .collection _ elems _ => OutputsPayloadList payload elems

/-- List-level helper for `OutputsPayload`. -/
private def OutputsPayloadList (payload : Atom) : List Pattern → Prop
  | [] => True
  | p :: ps => OutputsPayload payload p ∧ OutputsPayloadList payload ps

end

private theorem outputsPayloadList_iff_of_pointwise
    {payload : Atom} {ps qs : List Pattern}
    (hlen : ps.length = qs.length)
    (hpoint : ∀ i (h₁ : i < ps.length) (h₂ : i < qs.length),
      OutputsPayload payload (ps.get ⟨i, h₁⟩) ↔
        OutputsPayload payload (qs.get ⟨i, h₂⟩)) :
    OutputsPayloadList payload ps ↔ OutputsPayloadList payload qs := by
  induction ps generalizing qs with
  | nil =>
      cases qs with
      | nil => simp [OutputsPayloadList]
      | cons q qs =>
          simp at hlen
  | cons p ps ih =>
      cases qs with
      | nil =>
          simp at hlen
      | cons q qs =>
          have hpq : OutputsPayload payload p ↔ OutputsPayload payload q :=
            hpoint 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
          have hrest : OutputsPayloadList payload ps ↔ OutputsPayloadList payload qs := by
            apply ih
            · simpa using Nat.succ.inj hlen
            · intro i h₁ h₂
              simpa using hpoint (i + 1) (Nat.succ_lt_succ h₁) (Nat.succ_lt_succ h₂)
          constructor <;> intro h
          · exact ⟨hpq.mp h.1, hrest.mp h.2⟩
          · exact ⟨hpq.mpr h.1, hrest.mpr h.2⟩

private theorem outputsPayloadList_iff_of_perm
    {payload : Atom} {ps qs : List Pattern} (hperm : ps.Perm qs) :
    OutputsPayloadList payload ps ↔ OutputsPayloadList payload qs := by
  induction hperm with
  | nil =>
      simp [OutputsPayloadList]
  | @cons p ps qs hperm ih =>
      simp [OutputsPayloadList, ih]
  | swap p q ps =>
      simp [OutputsPayloadList, and_left_comm]
  | trans _ _ ih₁ ih₂ =>
      exact ih₁.trans ih₂

private theorem outputsPayloadList_append_iff
    {payload : Atom} {ps qs : List Pattern} :
    OutputsPayloadList payload (ps ++ qs) ↔
      OutputsPayloadList payload ps ∧ OutputsPayloadList payload qs := by
  induction ps with
  | nil =>
      simp [OutputsPayloadList]
  | cons p ps ih =>
      simp [OutputsPayloadList, ih, and_assoc]

private theorem outputsPayload_iff_of_structuralCongruence
    {payload : Atom} {p q : Pattern} (hsc : StructuralCongruence p q) :
    OutputsPayload payload p ↔ OutputsPayload payload q := by
  induction hsc with
  | alpha _ _ h =>
      subst h
      rfl
  | refl _ =>
      rfl
  | symm _ _ _ ih =>
      exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ =>
      exact ih₁.trans ih₂
  | par_singleton p =>
      simp [OutputsPayload, OutputsPayloadList]
  | par_nil_left p =>
      simp [OutputsPayload, OutputsPayloadList]
  | par_nil_right p =>
      simp [OutputsPayload, OutputsPayloadList]
  | par_comm p q =>
      simp [OutputsPayload, OutputsPayloadList, and_comm]
  | par_assoc p q r =>
      simp [OutputsPayload, OutputsPayloadList, and_assoc, and_comm]
  | par_cong ps qs hlen _ ih =>
      simpa [OutputsPayload] using outputsPayloadList_iff_of_pointwise
        (payload := payload) hlen ih
  | par_flatten ps qs =>
      simp [OutputsPayload, OutputsPayloadList, outputsPayloadList_append_iff]
  | par_perm ps qs hperm =>
      simpa [OutputsPayload] using outputsPayloadList_iff_of_perm
        (payload := payload) hperm
  | set_perm ps qs hperm =>
      simpa [OutputsPayload] using outputsPayloadList_iff_of_perm
        (payload := payload) hperm
  | set_cong ps qs hlen _ ih =>
      simpa [OutputsPayload] using outputsPayloadList_iff_of_pointwise
        (payload := payload) hlen ih
  | lambda_cong _ _ _ _ ih =>
      simpa [OutputsPayload] using ih
  | apply_cong f args₁ args₂ hpt hlen ih =>
      by_cases hfout : f = "POutput"
      · subst hfout
        cases args₁ with
        | nil =>
            cases args₂ with
            | nil =>
                simp [OutputsPayload, OutputsPayloadList]
            | cons a as =>
                simp at hpt
        | cons a as =>
            cases as with
            | nil =>
                cases args₂ with
                | nil =>
                    simp at hpt
                | cons b bs =>
                    cases bs with
                    | nil =>
                        simpa [OutputsPayload, OutputsPayloadList] using
                          outputsPayloadList_iff_of_pointwise
                            (payload := payload) hpt ih
                    | cons c cs =>
                        simp at hpt
            | cons b bs =>
                cases bs with
                | nil =>
                    cases args₂ with
                    | nil =>
                        simp at hpt
                    | cons a' as' =>
                        cases as' with
                        | nil =>
                            simp at hpt
                        | cons b' bs' =>
                            cases bs' with
                            | nil =>
                                have hq : StructuralCongruence b b' := by
                                  simpa using hlen 1 (by simp) (by simp)
                                simpa [OutputsPayload] using
                                  (structuralCongruence_to_fixed_iff
                                    (r := deferredPayload payload) hq)
                            | cons c' cs' =>
                                simp at hpt
                | cons c cs =>
                    cases args₂ with
                    | nil =>
                        simp at hpt
                    | cons a' as' =>
                        cases as' with
                        | nil =>
                            simp at hpt
                        | cons b' bs' =>
                            cases bs' with
                            | nil =>
                                simp at hpt
                            | cons c' cs' =>
                                simpa [OutputsPayload] using
                                  outputsPayloadList_iff_of_pointwise
                                    (payload := payload) hpt ih
      · by_cases hfin : f = "PInput"
        · simp [OutputsPayload, hfin]
        · simpa [OutputsPayload, hfout, hfin] using
            outputsPayloadList_iff_of_pointwise
              (payload := payload) hpt ih
  | collection_general_cong ct ps qs g hlen _ ih =>
      simpa [OutputsPayload] using outputsPayloadList_iff_of_pointwise
        (payload := payload) hlen ih
  | multiLambda_cong _ _ _ _ _ ih =>
      simpa [OutputsPayload] using ih
  | subst_cong _ _ _ _ _ _ ih₁ ih₂ =>
      simp [OutputsPayload, ih₁, ih₂]
  | quote_drop n =>
      simp [OutputsPayload, OutputsPayloadList]

mutual

/-- `EvalFree p` means `p` contains no explicit `rho:eval-payload` marker
anywhere in its syntax tree. -/
def EvalFree : Pattern → Prop
  | .bvar _ => True
  | .fvar _ => True
  | .apply "rho:eval-payload" _ => False
  | .apply _ args => EvalFreeList args
  | .lambda _ body => EvalFree body
  | .multiLambda _ _ body => EvalFree body
  | .subst body repl => EvalFree body ∧ EvalFree repl
  | .collection _ elems _ => EvalFreeList elems

/-- List-level helper for `EvalFree`. -/
def EvalFreeList : List Pattern → Prop
  | [] => True
  | p :: ps => EvalFree p ∧ EvalFreeList ps

end

/-- Rhometta reuses rho reduction and adds one explicit eval-at-COMM rule. -/
inductive RhometaReduces
    (space : Space) (dispatch : GroundedDispatch) :
    Pattern → Pattern → Type where
  | core {p q : Pattern} :
      (hcore : Reduction.Reduces p q) →
      ¬ CoreConsumesEvalPayload hcore →
      RhometaReduces space dispatch p q
  | evalComm {n body : Pattern} {rest : List Pattern}
      {payload value : Atom} :
      EvalCommCanonicalShell body payload →
      CertifiedPayloadResult space dispatch payload value →
      RhometaReduces space dispatch
        (.collection .hashBag
          ([.apply "POutput" [n, deferredPayload payload],
            .apply "PInput" [n, .lambda none body]] ++ rest) none)
        (.collection .hashBag
          ([semanticCommSubst body (wrappedValue value)] ++ rest) none)
  | equiv {p p' q q' : Pattern} :
      StructuralCongruence p p' →
      RhometaReduces space dispatch p' q' →
      StructuralCongruence q' q →
      RhometaReduces space dispatch p q
  | par {p q : Pattern} {rest : List Pattern} :
      RhometaReduces space dispatch p q →
      RhometaReduces space dispatch
        (.collection .hashBag (p :: rest) none)
        (.collection .hashBag (q :: rest) none)
  | par_any {p q : Pattern} {before after : List Pattern} :
      RhometaReduces space dispatch p q →
      RhometaReduces space dispatch
        (.collection .hashBag (before ++ [p] ++ after) none)
        (.collection .hashBag (before ++ [q] ++ after) none)
  | par_set {p q : Pattern} {rest : List Pattern} :
      RhometaReduces space dispatch p q →
      RhometaReduces space dispatch
        (.collection .hashSet (p :: rest) none)
        (.collection .hashSet (q :: rest) none)
  | par_set_any {p q : Pattern} {before after : List Pattern} :
      RhometaReduces space dispatch p q →
      RhometaReduces space dispatch
        (.collection .hashSet (before ++ [p] ++ after) none)
        (.collection .hashSet (before ++ [q] ++ after) none)

/-- Reflexive-transitive closure of Rhometta reduction. -/
inductive RhometaReducesStar
    (space : Space) (dispatch : GroundedDispatch) :
    Pattern → Pattern → Type where
  | refl (p : Pattern) : RhometaReducesStar space dispatch p p
  | step {p q r : Pattern} :
      RhometaReduces space dispatch p q →
      RhometaReducesStar space dispatch q r →
      RhometaReducesStar space dispatch p r

/-- Rhometta may-reachability: all states reachable via zero or more
Rhometta reductions. -/
def RhometaMayReachable
    (space : Space) (dispatch : GroundedDispatch)
    (p : Pattern) : Set Pattern :=
  { q | Nonempty (RhometaReducesStar space dispatch p q) }

/-- A Rhometta term can step if it has at least one one-step Rhometta reduct. -/
def RhometaCanStep
    (space : Space) (dispatch : GroundedDispatch)
    (p : Pattern) : Prop :=
  ∃ q, Nonempty (RhometaReduces space dispatch p q)

/-- A Rhometta term is quiescent when it has no Rhometta one-step reduct. -/
def RhometaNormalForm
    (space : Space) (dispatch : GroundedDispatch)
    (p : Pattern) : Prop :=
  ¬ RhometaCanStep space dispatch p

/-- The quiescent outcome set for Rhometta's may-semantics. -/
def RhometaOutcomes
    (space : Space) (dispatch : GroundedDispatch)
    (p : Pattern) : Set Pattern :=
  { q | Nonempty (RhometaReducesStar space dispatch p q) ∧
      RhometaNormalForm space dispatch q }

/-- Single-path execution is semantically safe only when the Rhometta
quiescent outcome set is a subsingleton. -/
def RhometaSinglePathSafe
    (space : Space) (dispatch : GroundedDispatch)
    (p : Pattern) : Prop :=
  (RhometaOutcomes space dispatch p).Subsingleton

abbrev MayReachable := RhometaMayReachable

/-- Canonical two-party source process used to observe deferred payload COMM. -/
def evalSource (chan : Pattern) (payload : Atom) (body : Pattern)
    (rest : List Pattern := []) : Pattern :=
  .collection .hashBag
    ([.apply "POutput" [chan, deferredPayload payload],
      .apply "PInput" [chan, .lambda none body]] ++ rest) none

/-- Drop-observer source: after COMM the payload value is exposed as a process. -/
def evalDropSource (chan : Pattern) (payload : Atom) : Pattern :=
  evalSource chan payload (.apply "PDrop" [.bvar 0])

/-- Expected one-step residual for the drop-observer case. -/
def evalDropResidual (value : Atom) : Pattern :=
  .collection .hashBag [semanticNormalizeProc (wrappedValue value)] none

private theorem stripSCWrappers_evalDropResidual (value : Atom) :
    stripSCWrappers (evalDropResidual value) = wrappedValue value := by
  rw [evalDropResidual, semanticNormalizeProc_wrappedValue,
    stripSCWrappers_hashBag_singleton, stripSCWrappers_wrappedValue]

/-- Decode a quiescent residual bag of `rho:val` wrappers into the multiset of returned atoms. -/
def residualResultMultiset? : Pattern → Option (Multiset Atom)
  | .collection .hashBag elems none =>
      (decodeWrappedValues? elems).map fun xs => (xs : Multiset Atom)
  | _ => none

/-- Operational quiescent outcomes in the post-reification carrier: result multiset only, with
trivial delta and empty explicit-export bag. -/
def reifiedOutcomeOf? (p : Pattern) :
    Option (Multiset Atom × (Unit × Multiplicative (Multiset Empty))) :=
  (residualResultMultiset? p).map fun rs => (rs, ((), (1 : Multiplicative (Multiset Empty))))

/-- SC-aware operational result decoder: collapse administrative wrappers first, then decode
the observable result multiset.  Singleton/zero parallel shells around one `rho:val` outcome
decode to the same singleton multiset as the exact residual bag. -/
def scResidualResultMultiset? (p : Pattern) : Option (Multiset Atom) :=
  match stripSCWrappers p with
  | .collection .hashBag elems none =>
      (decodeWrappedValues? elems).map fun xs => (xs : Multiset Atom)
  | q =>
      (scDecodeWrappedValue? q).map fun value => ({value} : Multiset Atom)

private theorem scResidualResultMultiset_eq_of_stripSCWrappers_eq
    {p q : Pattern}
    (h : stripSCWrappers p = stripSCWrappers q) :
    scResidualResultMultiset? p = scResidualResultMultiset? q := by
  unfold scResidualResultMultiset?
  rw [h]

private theorem scResidualResultMultiset_hashBag_singleton_length
    {p : Pattern} {elems : List Pattern} {value : Atom}
    (hstrip : stripSCWrappers p = .collection .hashBag elems none)
    (h : scResidualResultMultiset? p = some ({value} : Multiset Atom)) :
    elems.length = 1 := by
  unfold scResidualResultMultiset? at h
  rw [hstrip] at h
  cases hdec : decodeWrappedValues? elems with
  | none =>
      simp [hdec] at h
  | some xs =>
      have hms : (xs : Multiset Atom) = ({value} : Multiset Atom) := by
        simpa [hdec] using h
      exact decodeWrappedValues?_singleton_source_length hdec hms

private theorem scResidualResultMultiset_hashBag_singleton_source
    {p : Pattern} {elems : List Pattern} {value : Atom}
    (hstrip : stripSCWrappers p = .collection .hashBag elems none)
    (h : scResidualResultMultiset? p = some ({value} : Multiset Atom)) :
    ∃ elem, elems = [elem] ∧ decodeWrappedValue? elem = some value := by
  unfold scResidualResultMultiset? at h
  rw [hstrip] at h
  cases hdec : decodeWrappedValues? elems with
  | none =>
      simp [hdec] at h
  | some xs =>
      have hms : (xs : Multiset Atom) = ({value} : Multiset Atom) := by
        simpa [hdec] using h
      exact decodeWrappedValues?_singleton_source hdec hms

private theorem scResidualResultMultiset_hashBag_singleton_source_eq
    {p : Pattern} {elems : List Pattern} {value : Atom}
    (hstrip : stripSCWrappers p = .collection .hashBag elems none)
    (h : scResidualResultMultiset? p = some ({value} : Multiset Atom)) :
    elems = [wrappedValue value] := by
  unfold scResidualResultMultiset? at h
  rw [hstrip] at h
  cases hdec : decodeWrappedValues? elems with
  | none =>
      simp [hdec] at h
  | some xs =>
      have hms : (xs : Multiset Atom) = ({value} : Multiset Atom) := by
        simpa [hdec] using h
      exact decodeWrappedValues?_singleton_source_eq hdec hms

/-- SC-aware operational quiescent outcomes in the post-reification carrier. -/
def scReifiedOutcomeOf? (p : Pattern) :
    Option (Multiset Atom × (Unit × Multiplicative (Multiset Empty))) :=
  (scResidualResultMultiset? p).map fun rs => (rs, ((), (1 : Multiplicative (Multiset Empty))))

/-- Directly decoded Rhometta outcomes: an observation appears when some
quiescent operational outcome of `p` decodes in the SC-aware post-reification
carrier.  Unlike `RhometaSCObservedOutcomes`, this does not quotient the
outcome by an additional structural-congruence representative. -/
def RhometaDecodedOutcomes
    (space : Space) (dispatch : GroundedDispatch)
    (p : Pattern) :
    Set (Multiset Atom × (Unit × Multiplicative (Multiset Empty))) :=
  {obs | ∃ q,
    q ∈ RhometaOutcomes space dispatch p ∧
    scReifiedOutcomeOf? q = some obs}

/-- SC-representative observed Rhometta outcomes.  This is the quotient-aware
carrier used by the bridge: an operational outcome contributes an observation
when some structurally congruent representative decodes in the SC-aware
post-reification carrier. -/
def RhometaSCObservedOutcomes
    (space : Space) (dispatch : GroundedDispatch)
    (p : Pattern) :
    Set (Multiset Atom × (Unit × Multiplicative (Multiset Empty))) :=
  {obs | ∃ q r,
    q ∈ RhometaOutcomes space dispatch p ∧
    StructuralCongruence q r ∧
    scReifiedOutcomeOf? r = some obs}

theorem rhometaDecodedOutcomes_subset_scObservedOutcomes
    {space : Space} {dispatch : GroundedDispatch} {p : Pattern} :
    RhometaDecodedOutcomes space dispatch p ⊆
      RhometaSCObservedOutcomes space dispatch p := by
  rintro obs ⟨q, hq, hdec⟩
  exact ⟨q, q, hq, StructuralCongruence.refl _, hdec⟩

private theorem scReifiedOutcomeOf_eq_of_stripSCWrappers_eq
    {p q : Pattern}
    (h : stripSCWrappers p = stripSCWrappers q) :
    scReifiedOutcomeOf? p = scReifiedOutcomeOf? q := by
  unfold scReifiedOutcomeOf?
  rw [scResidualResultMultiset_eq_of_stripSCWrappers_eq h]

private theorem scResidualResultMultiset_quoteDrop_general (p : Pattern) :
    scResidualResultMultiset? (.apply "NQuote" [.apply "PDrop" [p]]) =
      scResidualResultMultiset? p := by
  simp [scResidualResultMultiset?, stripSCWrappers]

private theorem scResidualResultMultiset_par_singleton (p : Pattern) :
    scResidualResultMultiset? (.collection .hashBag [p] none) =
      scResidualResultMultiset? p :=
  scResidualResultMultiset_eq_of_stripSCWrappers_eq
    (stripSCWrappers_hashBag_singleton p)

private theorem scResidualResultMultiset_par_nil_left (p : Pattern) :
    scResidualResultMultiset? (.collection .hashBag [.apply "PZero" [], p] none) =
      scResidualResultMultiset? p :=
  scResidualResultMultiset_eq_of_stripSCWrappers_eq
    (stripSCWrappers_hashBag_nil_left p)

private theorem scResidualResultMultiset_par_nil_right (p : Pattern) :
    scResidualResultMultiset? (.collection .hashBag [p, .apply "PZero" []] none) =
      scResidualResultMultiset? p :=
  scResidualResultMultiset_eq_of_stripSCWrappers_eq
    (stripSCWrappers_hashBag_nil_right p)

private theorem scResidualResultMultiset_par_comm (p q : Pattern) :
    scResidualResultMultiset? (.collection .hashBag [p, q] none) =
      scResidualResultMultiset? (.collection .hashBag [q, p] none) := by
  by_cases hp : stripSCWrappers p = .apply "PZero" []
  · by_cases hq : stripSCWrappers q = .apply "PZero" []
    · simp [scResidualResultMultiset?, stripSCWrappers, stripSCWrappersList, hp, hq]
    · simp [scResidualResultMultiset?, stripSCWrappers, stripSCWrappersList, hp, hq]
  · by_cases hq : stripSCWrappers q = .apply "PZero" []
    · simp [scResidualResultMultiset?, stripSCWrappers, stripSCWrappersList, hp, hq]
    · have hperm :
          [stripSCWrappers p, stripSCWrappers q].Perm
            [stripSCWrappers q, stripSCWrappers p] :=
        List.Perm.symm (List.Perm.swap (stripSCWrappers p) (stripSCWrappers q) [])
      simpa [scResidualResultMultiset?, stripSCWrappers, stripSCWrappersList, hp, hq]
        using decodeWrappedValues?_multiset_eq_of_perm hperm

private theorem scResidualResultMultiset_par_assoc (p q r : Pattern) :
    scResidualResultMultiset?
      (.collection .hashBag [.collection .hashBag [p, q] none, r] none) =
    scResidualResultMultiset?
      (.collection .hashBag [p, .collection .hashBag [q, r] none] none) := by
  by_cases hp : stripSCWrappers p = .apply "PZero" []
  · by_cases hq : stripSCWrappers q = .apply "PZero" []
    · by_cases hr : stripSCWrappers r = .apply "PZero" []
      · simp [scResidualResultMultiset?, stripSCWrappers, stripSCWrappersList, hp, hq, hr]
      · simp [scResidualResultMultiset?, stripSCWrappers, stripSCWrappersList, hp, hq, hr]
    · by_cases hr : stripSCWrappers r = .apply "PZero" []
      · simp [scResidualResultMultiset?, stripSCWrappers, stripSCWrappersList, hp, hq, hr]
      · simp [scResidualResultMultiset?, stripSCWrappers, stripSCWrappersList, hp, hq, hr]
  · by_cases hq : stripSCWrappers q = .apply "PZero" []
    · by_cases hr : stripSCWrappers r = .apply "PZero" []
      · simp [scResidualResultMultiset?, stripSCWrappers, stripSCWrappersList, hp, hq, hr]
      · simp [scResidualResultMultiset?, stripSCWrappers, stripSCWrappersList, hp, hq, hr]
    · by_cases hr : stripSCWrappers r = .apply "PZero" []
      · simp [scResidualResultMultiset?, stripSCWrappers, stripSCWrappersList, hp, hq, hr]
      · simp [scResidualResultMultiset?, stripSCWrappers, stripSCWrappersList,
          decodeWrappedValues?, decodeWrappedValue?, hp, hq, hr]

private theorem scReifiedOutcomeOf_quoteDrop_general (p : Pattern) :
    scReifiedOutcomeOf? (.apply "NQuote" [.apply "PDrop" [p]]) =
      scReifiedOutcomeOf? p := by
  simp [scReifiedOutcomeOf?, scResidualResultMultiset_quoteDrop_general]

private theorem scReifiedOutcomeOf_par_singleton (p : Pattern) :
    scReifiedOutcomeOf? (.collection .hashBag [p] none) =
      scReifiedOutcomeOf? p := by
  simp [scReifiedOutcomeOf?, scResidualResultMultiset_par_singleton]

private theorem scReifiedOutcomeOf_par_nil_left (p : Pattern) :
    scReifiedOutcomeOf? (.collection .hashBag [.apply "PZero" [], p] none) =
      scReifiedOutcomeOf? p := by
  simp [scReifiedOutcomeOf?, scResidualResultMultiset_par_nil_left]

private theorem scReifiedOutcomeOf_par_nil_right (p : Pattern) :
    scReifiedOutcomeOf? (.collection .hashBag [p, .apply "PZero" []] none) =
      scReifiedOutcomeOf? p := by
  simp [scReifiedOutcomeOf?, scResidualResultMultiset_par_nil_right]

private theorem scReifiedOutcomeOf_par_comm (p q : Pattern) :
    scReifiedOutcomeOf? (.collection .hashBag [p, q] none) =
      scReifiedOutcomeOf? (.collection .hashBag [q, p] none) := by
  simp [scReifiedOutcomeOf?, scResidualResultMultiset_par_comm]

private theorem scReifiedOutcomeOf_par_assoc (p q r : Pattern) :
    scReifiedOutcomeOf?
      (.collection .hashBag [.collection .hashBag [p, q] none, r] none) =
    scReifiedOutcomeOf?
      (.collection .hashBag [p, .collection .hashBag [q, r] none] none) := by
  simp [scReifiedOutcomeOf?, scResidualResultMultiset_par_assoc]

private theorem scReifiedOutcomeOf_hashBag_singleton_length
    {p : Pattern} {elems : List Pattern} {value : Atom}
    (hstrip : stripSCWrappers p = .collection .hashBag elems none)
    (h :
      scReifiedOutcomeOf? p =
        some (({value} : Multiset Atom), ((), (1 : Multiplicative (Multiset Empty))))) :
    elems.length = 1 := by
  have hrs : scResidualResultMultiset? p = some ({value} : Multiset Atom) := by
    simpa [scReifiedOutcomeOf?] using h
  exact scResidualResultMultiset_hashBag_singleton_length hstrip hrs

private theorem scReifiedOutcomeOf_hashBag_singleton_source
    {p : Pattern} {elems : List Pattern} {value : Atom}
    (hstrip : stripSCWrappers p = .collection .hashBag elems none)
    (h :
      scReifiedOutcomeOf? p =
        some (({value} : Multiset Atom), ((), (1 : Multiplicative (Multiset Empty))))) :
    ∃ elem, elems = [elem] ∧ decodeWrappedValue? elem = some value := by
  have hrs : scResidualResultMultiset? p = some ({value} : Multiset Atom) := by
    simpa [scReifiedOutcomeOf?] using h
  exact scResidualResultMultiset_hashBag_singleton_source hstrip hrs

private theorem scReifiedOutcomeOf_hashBag_singleton_source_eq
    {p : Pattern} {elems : List Pattern} {value : Atom}
    (hstrip : stripSCWrappers p = .collection .hashBag elems none)
    (h :
      scReifiedOutcomeOf? p =
        some (({value} : Multiset Atom), ((), (1 : Multiplicative (Multiset Empty))))) :
    elems = [wrappedValue value] := by
  have hrs : scResidualResultMultiset? p = some ({value} : Multiset Atom) := by
    simpa [scReifiedOutcomeOf?] using h
  exact scResidualResultMultiset_hashBag_singleton_source_eq hstrip hrs

theorem residualResultMultiset?_evalDropResidual (value : Atom) :
    residualResultMultiset? (evalDropResidual value) = some ({value} : Multiset Atom) := by
  simp [residualResultMultiset?, evalDropResidual,
    semanticNormalizeProc_wrappedValue, decodeWrappedValues?,
    decodeWrappedValue?_wrappedValue]

theorem reifiedOutcomeOf?_evalDropResidual (value : Atom) :
    reifiedOutcomeOf? (evalDropResidual value) =
      some (({value} : Multiset Atom), ((), (1 : Multiplicative (Multiset Empty)))) := by
  simp [reifiedOutcomeOf?, residualResultMultiset?_evalDropResidual]

theorem scDecodeWrappedValue?_evalDropResidual (value : Atom) :
    scDecodeWrappedValue? (evalDropResidual value) = some value := by
  simp [evalDropResidual, semanticNormalizeProc_wrappedValue,
    scDecodeWrappedValue_singleton]

theorem scResidualResultMultiset?_evalDropResidual (value : Atom) :
    scResidualResultMultiset? (evalDropResidual value) = some ({value} : Multiset Atom) := by
  have hnonzero : wrappedValue value ≠ .apply "PZero" [] := by
    simp [wrappedValue]
  have hstrip :
      stripSCWrappers (.collection .hashBag [wrappedValue value] none) =
        wrappedValue value := by
    simp [stripSCWrappers, stripSCWrappersList, stripSCWrappers_wrappedValue, hnonzero]
  unfold scResidualResultMultiset?
  simp [evalDropResidual, semanticNormalizeProc_wrappedValue]
  rw [hstrip]
  simpa [wrappedValue] using (scDecodeWrappedValue?_wrappedValue value)

theorem scReifiedOutcomeOf?_evalDropResidual (value : Atom) :
    scReifiedOutcomeOf? (evalDropResidual value) =
      some (({value} : Multiset Atom), ((), (1 : Multiplicative (Multiset Empty)))) := by
  simp [scReifiedOutcomeOf?, scResidualResultMultiset?_evalDropResidual]

theorem scReifiedOutcomeOf?_wrappedValue (value : Atom) :
    scReifiedOutcomeOf? (wrappedValue value) =
      some (({value} : Multiset Atom), ((), (1 : Multiplicative (Multiset Empty)))) := by
  have hstrip : stripSCWrappers (wrappedValue value) = wrappedValue value :=
    stripSCWrappers_wrappedValue value
  unfold scReifiedOutcomeOf? scResidualResultMultiset?
  rw [hstrip]
  change Option.map
      (fun rs : Multiset Atom =>
        (rs, ((), (1 : Multiplicative (Multiset Empty)))))
      (Option.map (fun value => ({value} : Multiset Atom))
        (scDecodeWrappedValue? (wrappedValue value))) =
    some (({value} : Multiset Atom), ((), (1 : Multiplicative (Multiset Empty))))
  rw [scDecodeWrappedValue?_wrappedValue]
  rfl

theorem scResidualResultMultiset?_wrappedValue (value : Atom) :
    scResidualResultMultiset? (wrappedValue value) =
      some ({value} : Multiset Atom) := by
  have hstrip : stripSCWrappers (wrappedValue value) = wrappedValue value :=
    stripSCWrappers_wrappedValue value
  unfold scResidualResultMultiset?
  rw [hstrip]
  change Option.map (fun value => ({value} : Multiset Atom))
      (scDecodeWrappedValue? (wrappedValue value)) =
    some ({value} : Multiset Atom)
  rw [scDecodeWrappedValue?_wrappedValue]
  rfl

theorem scResidualResultMultiset_wrappedValue_eq_evalDropResidual
    (value : Atom) :
    scResidualResultMultiset? (wrappedValue value) =
      scResidualResultMultiset? (evalDropResidual value) := by
  rw [scResidualResultMultiset?_wrappedValue,
    scResidualResultMultiset?_evalDropResidual]

theorem scReifiedOutcomeOf_wrappedValue_eq_evalDropResidual
    (value : Atom) :
    scReifiedOutcomeOf? (wrappedValue value) =
      scReifiedOutcomeOf? (evalDropResidual value) := by
  rw [scReifiedOutcomeOf?_wrappedValue,
    scReifiedOutcomeOf?_evalDropResidual]

theorem scDecodeWrappedValue?_evalDropSource
    (chan : Pattern) (payload : Atom) :
    scDecodeWrappedValue? (evalDropSource chan payload) = none := by
  simp [scDecodeWrappedValue?, evalDropSource, evalSource,
    stripSCWrappers, stripSCWrappersList, deferredPayload]

theorem scResidualResultMultiset?_evalDropSource
    (chan : Pattern) (payload : Atom) :
    scResidualResultMultiset? (evalDropSource chan payload) = none := by
  unfold scResidualResultMultiset?
  simp [evalDropSource, evalSource, stripSCWrappers, stripSCWrappersList,
    deferredPayload, decodeWrappedValues?, decodeWrappedValue?]

theorem scReifiedOutcomeOf?_evalDropSource
    (chan : Pattern) (payload : Atom) :
    scReifiedOutcomeOf? (evalDropSource chan payload) = none := by
  simp [scReifiedOutcomeOf?, scResidualResultMultiset?_evalDropSource]

private theorem outputsDeferred_evalDropSource
    (chan : Pattern) (payload : Atom) :
    OutputsDeferred (evalDropSource chan payload) := by
  unfold evalDropSource evalSource
  simp [OutputsDeferred, OutputsDeferredList]
  exact ⟨payload, StructuralCongruence.refl _⟩

private theorem outputsPayload_evalDropSource
    (chan : Pattern) (payload : Atom) :
    OutputsPayload payload (evalDropSource chan payload) := by
  unfold evalDropSource evalSource
  simp [OutputsPayload, OutputsPayloadList]
  exact StructuralCongruence.refl _

private theorem deferredPayloadLike_of_commSource_SC_evalDropSource
    {n q body chan : Pattern} {rest : List Pattern}
    {payload : Atom}
    (hsc :
      StructuralCongruence
        (.collection .hashBag
          ([.apply "POutput" [n, q],
            .apply "PInput" [n, .lambda none body]] ++ rest) none)
        (evalDropSource chan payload)) :
    DeferredPayloadLike q := by
  have hdef :
      OutputsDeferred
        (.collection .hashBag
          ([.apply "POutput" [n, q],
            .apply "PInput" [n, .lambda none body]] ++ rest) none) :=
    (outputsDeferred_iff_of_structuralCongruence hsc).mpr
      (outputsDeferred_evalDropSource chan payload)
  simpa [OutputsDeferred, OutputsDeferredList] using hdef.1

private theorem outputPayload_of_commSource_SC_evalDropSource
    {n q body chan : Pattern} {rest : List Pattern}
    {payload : Atom}
    (hsc :
      StructuralCongruence
        (.collection .hashBag
          ([.apply "POutput" [n, q],
            .apply "PInput" [n, .lambda none body]] ++ rest) none)
        (evalDropSource chan payload)) :
    StructuralCongruence q (deferredPayload payload) := by
  have hdef :
      OutputsPayload payload
        (.collection .hashBag
          ([.apply "POutput" [n, q],
            .apply "PInput" [n, .lambda none body]] ++ rest) none) :=
    (outputsPayload_iff_of_structuralCongruence hsc).mpr
      (outputsPayload_evalDropSource chan payload)
  simpa [OutputsPayload, OutputsPayloadList] using hdef.1

private theorem deferredPayload_of_evalSource_SC_evalDropSource
    {n chan body : Pattern} {rest : List Pattern}
    {payload₁ payload₂ : Atom}
    (hsc :
      StructuralCongruence
        (evalSource n payload₁ body rest)
        (evalDropSource chan payload₂)) :
    StructuralCongruence (deferredPayload payload₁) (deferredPayload payload₂) := by
  simpa [evalSource] using
    (outputPayload_of_commSource_SC_evalDropSource
      (n := n) (q := deferredPayload payload₁) (body := body)
      (chan := chan) (rest := rest) (payload := payload₂) hsc)

theorem evalDrop_subst (value : Atom) :
    semanticCommSubst (.apply "PDrop" [.bvar 0]) (wrappedValue value) =
      semanticNormalizeProc (wrappedValue value) := by
  simpa [wrappedValue] using
    semanticCommSubst_collapses_bound_drop (wrappedValue value)

theorem evalSource_eq_evalDropSource_inv
    {n chan body : Pattern} {rest : List Pattern}
    {payload₁ payload₂ : Atom}
    (h :
      evalSource n payload₁ body rest =
        evalDropSource chan payload₂) :
    n = chan ∧
      body = .apply "PDrop" [.bvar 0] ∧
      rest = [] ∧
      payload₁ = payload₂ := by
  unfold evalSource evalDropSource at h
  injection h with _ hlist _
  have hlen := congrArg List.length hlist
  simp at hlen
  have hrest : rest = [] := by
    cases rest with
    | nil =>
        rfl
    | cons x xs =>
        simp at hlen
  subst hrest
  simp at hlist
  have hn : n = chan := hlist.1.1
  have hpayloadPat : deferredPayload payload₁ = deferredPayload payload₂ := hlist.1.2
  have hbody : body = .apply "PDrop" [.bvar 0] := hlist.2.2
  have hpayload : payload₁ = payload₂ := by
    simp [deferredPayload] at hpayloadPat
    exact atomToPattern_injective hpayloadPat
  exact ⟨hn, hbody, rfl, hpayload⟩

theorem commSource_eq_evalDropSource_inv
    {n chan body q : Pattern} {rest : List Pattern}
    {payload : Atom}
    (h :
      .collection .hashBag
          ([.apply "POutput" [n, q],
            .apply "PInput" [n, .lambda none body]] ++ rest) none =
        evalDropSource chan payload) :
    n = chan ∧
      q = deferredPayload payload ∧
      body = .apply "PDrop" [.bvar 0] ∧
      rest = [] := by
  unfold evalDropSource evalSource at h
  injection h with _ hlist _
  have hlen := congrArg List.length hlist
  simp at hlen
  have hrest : rest = [] := by
    cases rest with
    | nil =>
        rfl
    | cons x xs =>
        simp at hlen
  subst hrest
  simp at hlist
  exact ⟨hlist.1.1, hlist.1.2, hlist.2.2, rfl⟩

theorem deferredPayloadLike_of_commSource_eq_evalDropSource
    {n chan body q : Pattern} {rest : List Pattern}
    {payload : Atom}
    (h :
      .collection .hashBag
          ([.apply "POutput" [n, q],
            .apply "PInput" [n, .lambda none body]] ++ rest) none =
        evalDropSource chan payload) :
    DeferredPayloadLike q := by
  rcases commSource_eq_evalDropSource_inv h with ⟨_, hq, _, _⟩
  subst hq
  exact ⟨payload, StructuralCongruence.refl _⟩

theorem evalDropSource_evalComm_residual_exact
    {space : Space} {dispatch : GroundedDispatch}
    {n chan body : Pattern} {rest : List Pattern}
    {payload₁ payload₂ value : Atom}
    (hsource : evalSource n payload₁ body rest = evalDropSource chan payload₂)
    (hcert : CertifiedPayloadResult space dispatch payload₁ value) :
    CertifiedPayloadResult space dispatch payload₂ value ∧
      .collection .hashBag
          ([semanticCommSubst body (wrappedValue value)] ++ rest) none =
        evalDropResidual value := by
  rcases evalSource_eq_evalDropSource_inv hsource with ⟨_, hbody, hrest, hpayload⟩
  subst hbody hrest hpayload
  constructor
  · exact hcert
  · simp [evalDropResidual, evalDrop_subst]

private theorem certifiedPayloadResult_of_evalSource_eq_evalDropSource
    {space : Space} {dispatch : GroundedDispatch}
    {n chan body : Pattern} {rest : List Pattern}
    {payload₁ payload₂ value : Atom}
    (hsource : evalSource n payload₁ body rest = evalDropSource chan payload₂)
    (hcert : CertifiedPayloadResult space dispatch payload₁ value) :
    CertifiedPayloadResult space dispatch payload₂ value :=
  (evalDropSource_evalComm_residual_exact
    (space := space) (dispatch := dispatch)
    (n := n) (chan := chan) (body := body) (rest := rest)
    (payload₁ := payload₁) (payload₂ := payload₂) (value := value)
    hsource hcert).1

private theorem no_evalComm_from_evalDropSource_eq_of_no_certified
    {space : Space} {dispatch : GroundedDispatch}
    {n chan body : Pattern} {rest : List Pattern}
    {payload₁ payload₂ value : Atom}
    (hsource : evalSource n payload₁ body rest = evalDropSource chan payload₂)
    (hnone : ∀ v, ¬ CertifiedPayloadResult space dispatch payload₂ v)
    (hcert : CertifiedPayloadResult space dispatch payload₁ value) :
    False := by
  exact hnone value
    (certifiedPayloadResult_of_evalSource_eq_evalDropSource
      (space := space) (dispatch := dispatch)
      (n := n) (chan := chan) (body := body) (rest := rest)
      (payload₁ := payload₁) (payload₂ := payload₂) (value := value)
      hsource hcert)

theorem list_middle_eq_pair_cases
    {α : Type} {before after : List α} {p a b : α}
    (h : before ++ [p] ++ after = [a, b]) :
    (before = [] ∧ p = a ∧ after = [b]) ∨
      (before = [a] ∧ p = b ∧ after = []) := by
  have hlen := congrArg List.length h
  simp at hlen
  cases before with
  | nil =>
      left
      simp at h
      aesop
  | cons x xs =>
      cases xs with
      | nil =>
          right
          simp at h
          aesop
      | cons y ys =>
          have : False := by
            have hlen' := congrArg List.length h
            simp at hlen'
          exact False.elim this

private def shellWidth : Pattern → Nat
  | .apply "PZero" [] => 0
  | .apply "NQuote" [p] => shellWidth p
  | .apply "PDrop" [p] => shellWidth p
  | .collection _ elems _ => (elems.map shellWidth).sum
  | _ => 1

private theorem shellWidth_atomToPattern (value : Atom) :
    shellWidth (atomToPattern value) = 1 := by
  cases value with
  | symbol s =>
      simp [atomToPattern, shellWidth]
  | var v =>
      simp [atomToPattern, shellWidth]
  | grounded g =>
      cases g with
      | int i =>
          cases i using Int.rec <;>
            simp [atomToPattern, groundedValueToPattern, shellWidth]
      | string s =>
          simp [atomToPattern, groundedValueToPattern, shellWidth]
      | bool b =>
          cases b <;>
            simp [atomToPattern, groundedValueToPattern, shellWidth]
      | custom ty data =>
          simp [atomToPattern, groundedValueToPattern, shellWidth]
  | expression es =>
      simp [atomToPattern, shellWidth]

private theorem shellWidth_wrappedValue (value : Atom) :
    shellWidth (wrappedValue value) = 1 := by
  simp [wrappedValue, shellWidth]

private theorem shellWidth_deferredPayload (payload : Atom) :
    shellWidth (deferredPayload payload) = 1 := by
  simp [deferredPayload, shellWidth]

private theorem shellWidth_list_SC
    {ps qs : List Pattern} (hlen : ps.length = qs.length)
    (hsc : ∀ i (h₁ : i < ps.length) (h₂ : i < qs.length),
      shellWidth (ps.get ⟨i, h₁⟩) = shellWidth (qs.get ⟨i, h₂⟩)) :
    (ps.map shellWidth).sum = (qs.map shellWidth).sum := by
  induction ps generalizing qs with
  | nil =>
      cases qs with
      | nil => rfl
      | cons q qs' => simp at hlen
  | cons p ps' ih =>
      cases qs with
      | nil => simp at hlen
      | cons q qs' =>
          simp only [List.map_cons, List.sum_cons]
          simp only [List.length_cons] at hlen ⊢
          have h0 : shellWidth p = shellWidth q := hsc 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
          have htl := ih (by omega) fun i h₁ h₂ =>
            hsc (i + 1) (Nat.succ_lt_succ h₁) (Nat.succ_lt_succ h₂)
          omega

private theorem shellWidth_SC {p q : Pattern}
    (hsc : StructuralCongruence p q) :
    shellWidth p = shellWidth q := by
  induction hsc with
  | alpha _ _ h =>
      subst h
      rfl
  | refl _ =>
      rfl
  | symm _ _ _ ih =>
      exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ =>
      exact ih₁.trans ih₂
  | par_singleton p =>
      simp [shellWidth, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  | par_nil_left p =>
      simp [shellWidth, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  | par_nil_right p =>
      simp [shellWidth, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  | par_comm p q =>
      simp [shellWidth, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      omega
  | par_assoc p q r =>
      simp [shellWidth, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      omega
  | par_cong ps qs hlen _ ih =>
      simp only [shellWidth]
      exact shellWidth_list_SC hlen ih
  | par_flatten ps qs =>
      simp [shellWidth, List.map_append, List.sum_append,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  | par_perm _ _ hperm =>
      simp only [shellWidth]
      exact (hperm.map shellWidth).sum_eq
  | set_perm _ _ hperm =>
      simp only [shellWidth]
      exact (hperm.map shellWidth).sum_eq
  | set_cong es₁ es₂ hlen _ ih =>
      simp only [shellWidth]
      exact shellWidth_list_SC hlen ih
  | lambda_cong _ _ _ _ =>
      simp [shellWidth]
  | apply_cong f args₁ args₂ hlen _ ih =>
      by_cases hquote : f = "NQuote"
      · subst hquote
        cases args₁ with
        | nil =>
            cases args₂ <;> simp at hlen ⊢
        | cons a as =>
            cases as with
            | nil =>
                cases args₂ with
                | nil => simp at hlen
                | cons b bs =>
                    cases bs with
                    | nil =>
                        have hab : shellWidth a = shellWidth b := by
                          simpa using ih 0 (by simp) (by simp)
                        simp [shellWidth, hab]
                    | cons b' bs' =>
                        simp at hlen
            | cons a' as' =>
                cases args₂ with
                | nil =>
                    simp at hlen
                | cons b bs =>
                    cases bs with
                    | nil =>
                        simp at hlen
                    | cons b' bs' =>
                        simp [shellWidth]
      · by_cases hdrop : f = "PDrop"
        · subst hdrop
          cases args₁ with
          | nil =>
              cases args₂ <;> simp at hlen ⊢
          | cons a as =>
              cases as with
              | nil =>
                  cases args₂ with
                  | nil => simp at hlen
                  | cons b bs =>
                      cases bs with
                      | nil =>
                          have hab : shellWidth a = shellWidth b := by
                            simpa using ih 0 (by simp) (by simp)
                          simp [shellWidth, hab]
                      | cons b' bs' =>
                          simp at hlen
              | cons a' as' =>
                  cases args₂ with
                  | nil =>
                      simp at hlen
                  | cons b bs =>
                      cases bs with
                      | nil =>
                          simp at hlen
                      | cons b' bs' =>
                          simp [shellWidth]
        · by_cases hzero : f = "PZero"
          · subst hzero
            cases args₁ with
            | nil =>
                cases args₂ with
                | nil =>
                    simp [shellWidth]
                | cons b bs =>
                    simp at hlen
            | cons a as =>
                cases args₂ with
                | nil =>
                    simp at hlen
                | cons b bs =>
                    cases bs with
                    | nil =>
                        simp [shellWidth]
                    | cons b' bs' =>
                        simp [shellWidth]
          · simp [shellWidth, hquote, hdrop, hzero]
  | collection_general_cong _ es₁ es₂ _ hlen _ ih =>
      simp only [shellWidth]
      exact shellWidth_list_SC hlen ih
  | multiLambda_cong _ _ _ _ _ =>
      simp [shellWidth]
  | subst_cong _ _ _ _ _ _ =>
      simp [shellWidth]
  | quote_drop n =>
      simp [shellWidth]

private theorem shellWidth_filter_nonzero_sum (ps : List Pattern) :
    ((ps.filter (fun e => !decide (e = .apply "PZero" []))).map shellWidth).sum =
      (ps.map shellWidth).sum := by
  induction ps with
  | nil =>
      simp
  | cons p ps ih =>
      by_cases hpzero : p = .apply "PZero" []
      · simp [hpzero, shellWidth, ih]
      · simp [hpzero, ih]

private theorem shellWidth_stripSCWrappersList_sum
    {ps : List Pattern}
    (hpoint : ∀ q ∈ ps, shellWidth (stripSCWrappers q) = shellWidth q) :
    ((stripSCWrappersList ps).map shellWidth).sum =
      (ps.map shellWidth).sum := by
  induction ps with
  | nil =>
      simp [stripSCWrappersList]
  | cons p ps ih =>
      have hp : shellWidth (stripSCWrappers p) = shellWidth p :=
        hpoint p (by simp)
      have htail :
          ((stripSCWrappersList ps).map shellWidth).sum =
            (ps.map shellWidth).sum := by
        apply ih
        intro q hq
        exact hpoint q (by simp [hq])
      simp [stripSCWrappersList, hp, htail]

private theorem shellWidth_stripSCWrappers (p : Pattern) :
    shellWidth (stripSCWrappers p) = shellWidth p := by
  refine Pattern.inductionOn
    (motive := fun p => shellWidth (stripSCWrappers p) = shellWidth p)
    p ?hbvar ?hfvar ?happly ?hlambda ?hmultiLambda ?hsubst ?hcollection
  · intro n
    simp [stripSCWrappers, shellWidth]
  · intro x
    simp [stripSCWrappers, shellWidth]
  · intro f args ih
    by_cases hquote : f = "NQuote"
    · subst hquote
      cases args with
      | nil =>
          simp [stripSCWrappers, stripSCWrappersList, shellWidth]
      | cons a rest =>
          cases rest with
          | nil =>
              cases a with
              | bvar n =>
                  simp [stripSCWrappers, stripSCWrappersList, shellWidth]
              | fvar x =>
                  simp [stripSCWrappers, stripSCWrappersList, shellWidth]
              | apply g inner =>
                  by_cases hdrop : g = "PDrop"
                  · subst hdrop
                    cases inner with
                    | nil =>
                        simp [stripSCWrappers, stripSCWrappersList, shellWidth]
                    | cons n tail =>
                        cases tail with
                        | nil =>
                            have ha := ih (.apply "PDrop" [n]) (by simp)
                            simpa [stripSCWrappers, stripSCWrappersList, shellWidth]
                              using ha
                        | cons n' tail' =>
                            simp [stripSCWrappers, stripSCWrappersList, shellWidth]
                  · have ha := ih (.apply g inner) (by simp)
                    simpa [stripSCWrappers, stripSCWrappersList, shellWidth, hdrop]
                      using ha
              | lambda nm body =>
                  simp [stripSCWrappers, stripSCWrappersList, shellWidth]
              | multiLambda n nms body =>
                  simp [stripSCWrappers, stripSCWrappersList, shellWidth]
              | subst body repl =>
                  simp [stripSCWrappers, stripSCWrappersList, shellWidth]
              | collection ct elems guard =>
                  have ha := ih (.collection ct elems guard) (by simp)
                  simpa [stripSCWrappers, stripSCWrappersList, shellWidth] using ha
          | cons b bs =>
              simp [stripSCWrappers, stripSCWrappersList, shellWidth]
    · by_cases hdrop : f = "PDrop"
      · subst hdrop
        cases args with
        | nil =>
            simp [stripSCWrappers, stripSCWrappersList, shellWidth]
        | cons a rest =>
            cases rest with
            | nil =>
                have ha := ih a (by simp)
                simpa [stripSCWrappers, stripSCWrappersList, shellWidth] using ha
            | cons b bs =>
                simp [stripSCWrappers, stripSCWrappersList, shellWidth]
      · by_cases hzero : f = "PZero"
        · subst hzero
          cases args with
          | nil =>
              simp [stripSCWrappers, stripSCWrappersList, shellWidth]
          | cons a rest =>
              simp [stripSCWrappers, stripSCWrappersList, shellWidth]
        · simp [stripSCWrappers, shellWidth, hquote, hdrop, hzero]
  · intro nm body ih
    simp [stripSCWrappers, shellWidth]
  · intro n nms body ih
    simp [stripSCWrappers, shellWidth]
  · intro body repl ihBody ihRepl
    simp [stripSCWrappers, shellWidth]
  · intro ct elems guard ih
    have hsum :
        ((stripSCWrappersList elems).map shellWidth).sum =
          (elems.map shellWidth).sum :=
      shellWidth_stripSCWrappersList_sum ih
    cases ct with
    | vec =>
        simpa [stripSCWrappers, shellWidth] using hsum
    | hashBag =>
        cases guard with
        | some g =>
            simpa [stripSCWrappers, shellWidth] using hsum
        | none =>
            have hfilter :
                (((stripSCWrappersList elems).filter
                  (fun e => !decide (e = .apply "PZero" []))).map shellWidth).sum =
                    (elems.map shellWidth).sum := by
              rw [shellWidth_filter_nonzero_sum, hsum]
            cases hshape :
                (stripSCWrappersList elems).filter
                  (fun e => !decide (e = .apply "PZero" [])) with
            | nil =>
                simpa [stripSCWrappers, shellWidth, hshape] using hfilter
            | cons e rest =>
                cases rest with
                | nil =>
                    simpa [stripSCWrappers, shellWidth, hshape] using hfilter
                | cons e' rest' =>
                    simpa [stripSCWrappers, shellWidth, hshape] using hfilter
    | hashSet =>
        cases guard with
        | some g =>
            simpa [stripSCWrappers, shellWidth] using hsum
        | none =>
            have hfilter :
                (((stripSCWrappersList elems).filter
                  (fun e => !decide (e = .apply "PZero" []))).map shellWidth).sum =
                    (elems.map shellWidth).sum := by
              rw [shellWidth_filter_nonzero_sum, hsum]
            cases hshape :
                (stripSCWrappersList elems).filter
                  (fun e => !decide (e = .apply "PZero" [])) with
            | nil =>
                simpa [stripSCWrappers, shellWidth, hshape] using hfilter
            | cons e rest =>
                cases rest with
                | nil =>
                    simpa [stripSCWrappers, shellWidth, hshape] using hfilter
                | cons e' rest' =>
                    simpa [stripSCWrappers, shellWidth, hshape] using hfilter

private structure DropShellLike
    (chan : Pattern) (payload : Atom) (p : Pattern) : Prop where
  source_sc : StructuralCongruence p (evalDropSource chan payload)
  outputs_deferred : OutputsDeferred p
  outputs_payload : OutputsPayload payload p
  shell_width : shellWidth p = 2
  io_count : ioCount p = 2 + 2 * ioCount chan

private theorem dropShellLike_evalDropSource
    (chan : Pattern) (payload : Atom) :
    DropShellLike chan payload (evalDropSource chan payload) := by
  refine ⟨StructuralCongruence.refl _,
    outputsDeferred_evalDropSource chan payload,
    outputsPayload_evalDropSource chan payload, ?_, ?_⟩
  · simp [evalDropSource, evalSource, shellWidth]
  · simp [evalDropSource, evalSource, ioCount, ioCount_deferredPayload_zero]
    omega

private theorem dropShellLike_of_source_structuralCongruence
    {chan p : Pattern} {payload : Atom}
    (hsc : StructuralCongruence p (evalDropSource chan payload)) :
    DropShellLike chan payload p := by
  refine ⟨hsc, ?_, ?_, ?_, ?_⟩
  · exact (outputsDeferred_iff_of_structuralCongruence hsc).mpr
      (outputsDeferred_evalDropSource chan payload)
  · exact (outputsPayload_iff_of_structuralCongruence hsc).mpr
      (outputsPayload_evalDropSource chan payload)
  · calc
      shellWidth p = shellWidth (evalDropSource chan payload) := shellWidth_SC hsc
      _ = 2 := by
        simp [evalDropSource, evalSource, shellWidth]
  · calc
      ioCount p = ioCount (evalDropSource chan payload) := ioCount_SC hsc
      _ = 2 + 2 * ioCount chan := by
        simp [evalDropSource, evalSource, ioCount, ioCount_deferredPayload_zero]
        omega

private theorem dropShellLike_iff_source_structuralCongruence
    {chan p : Pattern} {payload : Atom} :
    DropShellLike chan payload p ↔
      StructuralCongruence p (evalDropSource chan payload) := by
  constructor
  · exact DropShellLike.source_sc
  · exact dropShellLike_of_source_structuralCongruence

private theorem dropShellLike_of_structuralCongruence
    {chan p q : Pattern} {payload : Atom}
    (hsc : StructuralCongruence p q)
    (hshape : DropShellLike chan payload p) :
    DropShellLike chan payload q := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact StructuralCongruence.trans _ _ _
      (StructuralCongruence.symm _ _ hsc) hshape.source_sc
  · exact (outputsDeferred_iff_of_structuralCongruence hsc).mp
      hshape.outputs_deferred
  · exact (outputsPayload_iff_of_structuralCongruence hsc).mp
      hshape.outputs_payload
  · calc
      shellWidth q = shellWidth p := (shellWidth_SC hsc).symm
      _ = 2 := hshape.shell_width
  · calc
      ioCount q = ioCount p := (ioCount_SC hsc).symm
      _ = 2 + 2 * ioCount chan := hshape.io_count

private theorem dropShellLike_of_hashBag_singleton
    {chan p : Pattern} {payload : Atom}
    (hshape : DropShellLike chan payload
      (.collection .hashBag [p] none)) :
    DropShellLike chan payload p :=
  dropShellLike_of_source_structuralCongruence
    (StructuralCongruence.trans _ _ _
      (StructuralCongruence.symm _ _
        (StructuralCongruence.par_singleton p))
      hshape.source_sc)

private theorem dropShellLike_of_hashBag_nil_left
    {chan p : Pattern} {payload : Atom}
    (hshape : DropShellLike chan payload
      (.collection .hashBag [.apply "PZero" [], p] none)) :
    DropShellLike chan payload p :=
  dropShellLike_of_source_structuralCongruence
    (StructuralCongruence.trans _ _ _
      (StructuralCongruence.symm _ _
        (StructuralCongruence.par_nil_left p))
      hshape.source_sc)

private theorem dropShellLike_of_hashBag_nil_right
    {chan p : Pattern} {payload : Atom}
    (hshape : DropShellLike chan payload
      (.collection .hashBag [p, .apply "PZero" []] none)) :
    DropShellLike chan payload p :=
  dropShellLike_of_source_structuralCongruence
    (StructuralCongruence.trans _ _ _
      (StructuralCongruence.symm _ _
        (StructuralCongruence.par_nil_right p))
      hshape.source_sc)

private theorem dropShellLike_of_quoteDrop
    {chan p : Pattern} {payload : Atom}
    (hshape : DropShellLike chan payload
      (.apply "NQuote" [.apply "PDrop" [p]])) :
    DropShellLike chan payload p :=
  dropShellLike_of_source_structuralCongruence
    (StructuralCongruence.trans _ _ _
      (StructuralCongruence.symm _ _
        (StructuralCongruence.quote_drop p))
      hshape.source_sc)

private theorem dropShellLike_of_hashBag_perm
    {chan : Pattern} {payload : Atom} {elems₁ elems₂ : List Pattern}
    (hperm : elems₁.Perm elems₂)
    (hshape : DropShellLike chan payload
      (.collection .hashBag elems₁ none)) :
    DropShellLike chan payload (.collection .hashBag elems₂ none) :=
  dropShellLike_of_structuralCongruence
    (StructuralCongruence.par_perm elems₁ elems₂ hperm) hshape

private theorem dropShellLike_of_hashBag_flatten
    {chan : Pattern} {payload : Atom} {before nested : List Pattern}
    (hshape : DropShellLike chan payload
      (.collection .hashBag (before ++ [.collection .hashBag nested none]) none)) :
    DropShellLike chan payload
      (.collection .hashBag (before ++ nested) none) :=
  dropShellLike_of_structuralCongruence
    (StructuralCongruence.par_flatten before nested) hshape

private theorem dropShellLike_of_hashBag_unflatten
    {chan : Pattern} {payload : Atom} {before nested : List Pattern}
    (hshape : DropShellLike chan payload
      (.collection .hashBag (before ++ nested) none)) :
    DropShellLike chan payload
      (.collection .hashBag (before ++ [.collection .hashBag nested none]) none) :=
  dropShellLike_of_structuralCongruence
    (StructuralCongruence.symm _ _
      (StructuralCongruence.par_flatten before nested)) hshape

private theorem shellWidth_ge_two_of_reduces {p q : Pattern}
    (hred : Reduction.Reduces p q) :
    2 ≤ shellWidth p := by
  induction hred with
  | comm =>
      simp [shellWidth, List.map_cons, List.sum_cons]
      omega
  | @equiv p p' q q' hsc _ _ ih =>
      have hw : shellWidth p = shellWidth p' := shellWidth_SC hsc
      omega
  | par _ ih =>
      simp [shellWidth, List.map_cons, List.sum_cons]
      omega
  | par_any _ ih =>
      simp [shellWidth, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
      omega
  | par_set _ ih =>
      simp [shellWidth, List.map_cons, List.sum_cons]
      omega
  | par_set_any _ ih =>
      simp [shellWidth, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
      omega

private theorem output_shell_SC_irreducible
    {n payload p q : Pattern}
    (hsc : StructuralCongruence p (.apply "POutput" [n, payload]))
    (hred : Reduction.Reduces p q) : False := by
  have hw : shellWidth p = shellWidth (.apply "POutput" [n, payload]) := shellWidth_SC hsc
  have hge : 2 ≤ shellWidth p := shellWidth_ge_two_of_reduces hred
  simp [shellWidth] at hw
  omega

private theorem input_shell_SC_irreducible
    {n body p q : Pattern}
    (hsc : StructuralCongruence p (.apply "PInput" [n, .lambda none body]))
    (hred : Reduction.Reduces p q) : False := by
  have hw : shellWidth p = shellWidth (.apply "PInput" [n, .lambda none body]) := shellWidth_SC hsc
  have hge : 2 ≤ shellWidth p := shellWidth_ge_two_of_reduces hred
  simp [shellWidth] at hw
  omega

private theorem coreConsumesEvalPayload_of_outputsDeferred_shellWidth_two
    {p q : Pattern}
    (hout : OutputsDeferred p)
    (hwidth : shellWidth p = 2)
    (hred : Reduction.Reduces p q) :
    CoreConsumesEvalPayload hred := by
  revert hout hwidth
  induction hred with
  | comm =>
      intro hout hwidth
      exact CoreConsumesEvalPayload.comm (by
        simpa [OutputsDeferred, OutputsDeferredList] using hout.1)
  | @equiv p p' q q' hsc hmid hsc' ih =>
      intro hout hwidth
      have hout' : OutputsDeferred p' :=
        (outputsDeferred_iff_of_structuralCongruence hsc).mp hout
      have hwidth' : shellWidth p' = 2 := by
        calc
          shellWidth p' = shellWidth p := (shellWidth_SC hsc).symm
          _ = 2 := hwidth
      exact CoreConsumesEvalPayload.equiv (ih hout' hwidth')
  | @par pInner qInner rest hmid ih =>
      intro hout hwidth
      have hp : OutputsDeferred pInner := by
        simpa [OutputsDeferred, OutputsDeferredList] using hout.1
      have hge : 2 ≤ shellWidth pInner := shellWidth_ge_two_of_reduces hmid
      have hpwidth : shellWidth pInner = 2 := by
        simp [shellWidth, List.map_cons, List.sum_cons] at hwidth
        omega
      exact CoreConsumesEvalPayload.par (ih hp hpwidth)
  | @par_any pInner qInner before after hmid ih =>
      intro hout hwidth
      have hlist : OutputsDeferredList (before ++ [pInner] ++ after) := by
        simpa [OutputsDeferred] using hout
      have hp : OutputsDeferred pInner :=
        outputsDeferred_of_outputsDeferredList_middle hlist
      have hge : 2 ≤ shellWidth pInner := shellWidth_ge_two_of_reduces hmid
      have hpwidth : shellWidth pInner = 2 := by
        simp [shellWidth, List.map_append, List.sum_append, List.map_cons, List.sum_cons] at hwidth
        omega
      exact CoreConsumesEvalPayload.par_any (ih hp hpwidth)
  | @par_set pInner qInner rest hmid ih =>
      intro hout hwidth
      have hp : OutputsDeferred pInner := by
        simpa [OutputsDeferred, OutputsDeferredList] using hout.1
      have hge : 2 ≤ shellWidth pInner := shellWidth_ge_two_of_reduces hmid
      have hpwidth : shellWidth pInner = 2 := by
        simp [shellWidth, List.map_cons, List.sum_cons] at hwidth
        omega
      exact CoreConsumesEvalPayload.par_set (ih hp hpwidth)
  | @par_set_any pInner qInner before after hmid ih =>
      intro hout hwidth
      have hlist : OutputsDeferredList (before ++ [pInner] ++ after) := by
        simpa [OutputsDeferred] using hout
      have hp : OutputsDeferred pInner :=
        outputsDeferred_of_outputsDeferredList_middle hlist
      have hge : 2 ≤ shellWidth pInner := shellWidth_ge_two_of_reduces hmid
      have hpwidth : shellWidth pInner = 2 := by
        simp [shellWidth, List.map_append, List.sum_append, List.map_cons, List.sum_cons] at hwidth
        omega
      exact CoreConsumesEvalPayload.par_set_any (ih hp hpwidth)

private theorem coreConsumesEvalPayload_of_SC_evalDropSource
    {p q chan : Pattern} {payload : Atom}
    (hsc : StructuralCongruence p (evalDropSource chan payload))
    (hred : Reduction.Reduces p q) :
    CoreConsumesEvalPayload hred := by
  have hout : OutputsDeferred p :=
    (outputsDeferred_iff_of_structuralCongruence hsc).mpr
      (outputsDeferred_evalDropSource chan payload)
  have hwidth : shellWidth p = 2 := by
    calc
      shellWidth p = shellWidth (evalDropSource chan payload) := shellWidth_SC hsc
      _ = 2 := by
        simp [evalDropSource, evalSource, shellWidth]
  exact coreConsumesEvalPayload_of_outputsDeferred_shellWidth_two hout hwidth hred

private theorem no_rhometaCore_from_SC_evalDropSource
    {p q chan : Pattern} {payload : Atom}
    {hcore : Reduction.Reduces p q}
    (hsc : StructuralCongruence p (evalDropSource chan payload))
    (hguard : ¬ CoreConsumesEvalPayload hcore) :
    False := by
  exact hguard (coreConsumesEvalPayload_of_SC_evalDropSource hsc hcore)

private theorem shellWidth_ge_two_of_rhometaReduces
    {space : Space} {dispatch : GroundedDispatch}
    {p q : Pattern}
    (hred : RhometaReduces space dispatch p q) :
    2 ≤ shellWidth p := by
  induction hred with
  | core hcore _ =>
      exact shellWidth_ge_two_of_reduces hcore
  | @evalComm n body rest payload value hcanon hcert =>
      simp [shellWidth, List.map_cons, List.sum_cons]
      omega
  | @equiv p p' q q' hsc hmid hsc' ih =>
      have hw : shellWidth p = shellWidth p' := shellWidth_SC hsc
      omega
  | par _ ih =>
      simp [shellWidth, List.map_cons, List.sum_cons]
      omega
  | par_any _ ih =>
      simp [shellWidth, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
      omega
  | par_set _ ih =>
      simp [shellWidth, List.map_cons, List.sum_cons]
      omega
  | par_set_any _ ih =>
      simp [shellWidth, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
      omega

private theorem rhometa_output_shell_SC_irreducible
    {space : Space} {dispatch : GroundedDispatch}
    {n payload p q : Pattern}
    (hsc : StructuralCongruence p (.apply "POutput" [n, payload]))
    (hred : RhometaReduces space dispatch p q) : False := by
  have hw : shellWidth p = shellWidth (.apply "POutput" [n, payload]) := shellWidth_SC hsc
  have hge : 2 ≤ shellWidth p := shellWidth_ge_two_of_rhometaReduces hred
  simp [shellWidth] at hw
  omega

private theorem rhometa_input_shell_SC_irreducible
    {space : Space} {dispatch : GroundedDispatch}
    {n body p q : Pattern}
    (hsc : StructuralCongruence p (.apply "PInput" [n, .lambda none body]))
    (hred : RhometaReduces space dispatch p q) : False := by
  have hw : shellWidth p = shellWidth (.apply "PInput" [n, .lambda none body]) := shellWidth_SC hsc
  have hge : 2 ≤ shellWidth p := shellWidth_ge_two_of_rhometaReduces hred
  simp [shellWidth] at hw
  omega

private theorem no_rhometaReduces_par_source_eq_evalDropSource
    {space : Space} {dispatch : GroundedDispatch}
    {p q : Pattern} {rest : List Pattern}
    {chan : Pattern} {payload : Atom}
    (hstep : RhometaReduces space dispatch p q)
    (hsrc : .collection .hashBag (p :: rest) none = evalDropSource chan payload) :
    False := by
  unfold evalDropSource evalSource at hsrc
  injection hsrc with _ hlist _
  have hlen := congrArg List.length hlist
  simp at hlen
  cases rest with
  | nil =>
      simp at hlen
  | cons r rest' =>
      cases rest' with
      | nil =>
          rcases hlist with ⟨_, _, _⟩
          exact rhometa_output_shell_SC_irreducible
            (space := space) (dispatch := dispatch)
            (n := chan) (payload := deferredPayload payload)
            (p := .apply "POutput" [chan, deferredPayload payload])
            (q := q)
            (StructuralCongruence.refl _) hstep
      | cons r' rest'' =>
          simp at hlen

private theorem no_rhometaReduces_par_any_source_eq_evalDropSource
    {space : Space} {dispatch : GroundedDispatch}
    {p q : Pattern} {before after : List Pattern}
    {chan : Pattern} {payload : Atom}
    (hstep : RhometaReduces space dispatch p q)
    (hsrc :
      .collection .hashBag (before ++ [p] ++ after) none =
        evalDropSource chan payload) :
    False := by
  unfold evalDropSource evalSource at hsrc
  injection hsrc with _ hlist _
  rcases list_middle_eq_pair_cases hlist with hcase | hcase
  · rcases hcase with ⟨hbefore, hp, hafter⟩
    subst hbefore hp hafter
    exact rhometa_output_shell_SC_irreducible
      (space := space) (dispatch := dispatch)
      (n := chan) (payload := deferredPayload payload)
      (p := .apply "POutput" [chan, deferredPayload payload])
      (q := q)
      (StructuralCongruence.refl _) hstep
  · rcases hcase with ⟨hbefore, hp, hafter⟩
    subst hbefore hp hafter
    exact rhometa_input_shell_SC_irreducible
      (space := space) (dispatch := dispatch)
      (n := chan) (body := .apply "PDrop" [.bvar 0])
      (p := .apply "PInput" [chan, .lambda none (.apply "PDrop" [.bvar 0])])
      (q := q)
      (StructuralCongruence.refl _) hstep

private theorem no_rhometaReduces_par_set_source_eq_evalDropSource
    {space : Space} {dispatch : GroundedDispatch}
    {p q : Pattern} {rest : List Pattern}
    {chan : Pattern} {payload : Atom}
    (_hstep : RhometaReduces space dispatch p q)
    (hsrc : .collection .hashSet (p :: rest) none = evalDropSource chan payload) :
    False := by
  unfold evalDropSource evalSource at hsrc
  cases hsrc

private theorem no_rhometaReduces_par_set_any_source_eq_evalDropSource
    {space : Space} {dispatch : GroundedDispatch}
    {p q : Pattern} {before after : List Pattern}
    {chan : Pattern} {payload : Atom}
    (_hstep : RhometaReduces space dispatch p q)
    (hsrc :
      .collection .hashSet (before ++ [p] ++ after) none =
        evalDropSource chan payload) :
    False := by
  unfold evalDropSource evalSource at hsrc
  cases hsrc

private theorem struct_output_cong_channel {n n' q : Pattern}
    (hn : StructuralCongruence n n') :
    StructuralCongruence (.apply "POutput" [n, q]) (.apply "POutput" [n', q]) := by
  refine StructuralCongruence.apply_cong "POutput" [n, q] [n', q] rfl ?_
  intro i h₁ h₂
  have hi_lt : i < 2 := by simpa using h₁
  have hi : i = 0 ∨ i = 1 := by omega
  cases hi with
  | inl hi0 =>
      subst hi0
      simpa using hn
  | inr hi1 =>
      subst hi1
      simpa using StructuralCongruence.refl q

private theorem struct_input_cong_channel {n n' body : Pattern}
    (hn : StructuralCongruence n n') :
    StructuralCongruence
      (.apply "PInput" [n, .lambda none body])
      (.apply "PInput" [n', .lambda none body]) := by
  refine StructuralCongruence.apply_cong "PInput"
    [n, .lambda none body] [n', .lambda none body] rfl ?_
  intro i h₁ h₂
  have hi_lt : i < 2 := by simpa using h₁
  have hi : i = 0 ∨ i = 1 := by omega
  cases hi with
  | inl hi0 =>
      subst hi0
      simpa using hn
  | inr hi1 =>
      subst hi1
      simpa using StructuralCongruence.refl (.lambda none body)

private theorem par_cong_cons_cons_tail
    {a₁ a₂ b₁ b₂ : Pattern} {rest : List Pattern}
    (ha : StructuralCongruence a₁ a₂)
    (hb : StructuralCongruence b₁ b₂) :
    StructuralCongruence
      (.collection .hashBag ([a₁, b₁] ++ rest) none)
      (.collection .hashBag ([a₂, b₂] ++ rest) none) := by
  refine StructuralCongruence.par_cong _ _ rfl ?_
  intro i h₁ h₂
  cases i with
  | zero =>
      simpa using ha
  | succ i =>
      cases i with
      | zero =>
          simpa using hb
      | succ i =>
          have h₁' : i < rest.length := by simpa using h₁
          have h₂' : i < rest.length := by simpa using h₂
          simpa using StructuralCongruence.refl (rest.get ⟨i, h₁'⟩)

theorem evalSource_structCongruence_normalizedChannel
    (chan : Pattern) (payload : Atom) (body : Pattern) (rest : List Pattern := []) :
    StructuralCongruence
      (evalSource chan payload body rest)
      (evalSource (semanticNormalizeName chan) payload body rest) := by
  unfold evalSource
  refine par_cong_cons_cons_tail ?_ ?_
  · exact struct_output_cong_channel
      (StructuralCongruence.symm _ _ (semanticNormalizeName_sound_struct (n := chan)))
  · exact struct_input_cong_channel
      (StructuralCongruence.symm _ _ (semanticNormalizeName_sound_struct (n := chan)))

theorem evalDrop_certified_branch
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload value : Atom}
    (hcert : CertifiedPayloadResult space dispatch payload value) :
    Nonempty (RhometaReduces space dispatch
      (evalDropSource chan payload)
      (evalDropResidual value)) := by
  have hcanon :
      EvalCommCanonicalShell (.apply "PDrop" [.bvar 0]) payload :=
    evalCommCanonicalShell_dropBody (payload := payload)
  refine ⟨?_⟩
  simpa [evalDropSource, evalSource, evalDropResidual, evalDrop_subst] using
    (RhometaReduces.evalComm (space := space) (dispatch := dispatch)
      (n := chan) (body := .apply "PDrop" [.bvar 0]) (rest := [])
      (payload := payload) (value := value) hcanon hcert)

theorem evalComm_certified_branch
    {space : Space} {dispatch : GroundedDispatch}
    {chan body : Pattern} {rest : List Pattern}
    {payload value : Atom}
    (hcanon : EvalCommCanonicalShell body payload)
    (hcert : CertifiedPayloadResult space dispatch payload value) :
    Nonempty (RhometaReduces space dispatch
      (evalSource chan payload body rest)
      (.collection .hashBag
        ([semanticCommSubst body (wrappedValue value)] ++ rest) none)) := by
  refine ⟨?_⟩
  simpa [evalSource] using
    (RhometaReduces.evalComm (space := space) (dispatch := dispatch)
      (n := chan) (body := body) (rest := rest)
      (payload := payload) (value := value) hcanon hcert)

private theorem evalFreeList_iff_of_pointwise
    {ps qs : List Pattern}
    (hlen : ps.length = qs.length)
    (hpoint :
      ∀ i (h₁ : i < ps.length) (h₂ : i < qs.length),
        EvalFree (ps.get ⟨i, h₁⟩) ↔ EvalFree (qs.get ⟨i, h₂⟩)) :
    EvalFreeList ps ↔ EvalFreeList qs := by
  induction ps generalizing qs with
  | nil =>
      cases qs with
      | nil => simp [EvalFreeList]
      | cons q qs => simp at hlen
  | cons p ps ih =>
      cases qs with
      | nil => simp at hlen
      | cons q qs =>
          have hpq : EvalFree p ↔ EvalFree q :=
            hpoint 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
          have hrest :
              EvalFreeList ps ↔ EvalFreeList qs := by
            apply ih
            · simpa using Nat.succ.inj hlen
            · intro i h₁ h₂
              simpa using hpoint (i + 1) (Nat.succ_lt_succ h₁) (Nat.succ_lt_succ h₂)
          simp [EvalFreeList, hpq, hrest]

private theorem evalFreeList_iff_of_perm
    {ps qs : List Pattern} (hperm : ps.Perm qs) :
    EvalFreeList ps ↔ EvalFreeList qs := by
  induction hperm with
  | nil =>
      simp [EvalFreeList]
  | @cons p ps qs hperm ih =>
      simp [EvalFreeList, ih]
  | swap p q ps =>
      simp [EvalFreeList, and_left_comm]
  | trans _ _ ih₁ ih₂ =>
      exact ih₁.trans ih₂

private theorem evalFreeList_append_iff
    {ps qs : List Pattern} :
    EvalFreeList (ps ++ qs) ↔ EvalFreeList ps ∧ EvalFreeList qs := by
  induction ps with
  | nil =>
      simp [EvalFreeList]
  | cons p ps ih =>
      simp [EvalFreeList, ih, and_assoc]

private theorem evalFree_of_evalFreeList_middle
    {before after : List Pattern} {p : Pattern}
    (h : EvalFreeList (before ++ [p] ++ after)) :
    EvalFree p := by
  induction before with
  | nil =>
      simpa [EvalFreeList] using h.1
  | cons b before ih =>
      have htail : EvalFreeList (before ++ [p] ++ after) := by
        simpa [EvalFreeList] using h.2
      exact ih htail

theorem evalFree_iff_of_structuralCongruence
    {p q : Pattern} (hsc : StructuralCongruence p q) :
    EvalFree p ↔ EvalFree q := by
  induction hsc with
  | alpha p q h =>
      subst h
      rfl
  | refl p =>
      rfl
  | symm p q _ ih =>
      exact ih.symm
  | trans p q r _ _ ih₁ ih₂ =>
      exact ih₁.trans ih₂
  | par_singleton p =>
      simp [EvalFree, EvalFreeList]
  | par_nil_left p =>
      simp [EvalFree, EvalFreeList]
  | par_nil_right p =>
      simp [EvalFree, EvalFreeList]
  | par_comm p q =>
      simp [EvalFree, EvalFreeList, and_comm]
  | par_assoc p q r =>
      simp [EvalFree, EvalFreeList, and_assoc, and_comm]
  | par_cong ps qs hlen _ ih =>
      simpa [EvalFree] using evalFreeList_iff_of_pointwise hlen ih
  | par_flatten ps qs =>
      simp [EvalFree, EvalFreeList, evalFreeList_append_iff]
  | par_perm _ _ hperm =>
      simpa [EvalFree] using evalFreeList_iff_of_perm hperm
  | set_perm _ _ hperm =>
      simpa [EvalFree] using evalFreeList_iff_of_perm hperm
  | set_cong es₁ es₂ hlen _ ih =>
      simpa [EvalFree] using evalFreeList_iff_of_pointwise hlen ih
  | lambda_cong _ _ _ _ ih =>
      simpa [EvalFree] using ih
  | apply_cong f args₁ args₂ hlen _ ih =>
      by_cases hf : f = "rho:eval-payload"
      · subst hf
        simp [EvalFree]
      · simpa [EvalFree, hf] using evalFreeList_iff_of_pointwise hlen ih
  | collection_general_cong _ elems₁ elems₂ _ hlen _ ih =>
      simpa [EvalFree] using evalFreeList_iff_of_pointwise hlen ih
  | multiLambda_cong _ _ _ _ _ ih =>
      simpa [EvalFree] using ih
  | subst_cong _ _ _ _ _ _ ihBody ihRepl =>
      constructor
      · intro h
        exact ⟨ihBody.mp h.1, ihRepl.mp h.2⟩
      · intro h
        exact ⟨ihBody.mpr h.1, ihRepl.mpr h.2⟩
  | quote_drop n =>
      simp [EvalFree, EvalFreeList]

theorem not_evalFree_of_deferredPayloadLike
    {q : Pattern} (hlike : DeferredPayloadLike q) :
    ¬ EvalFree q := by
  rcases hlike with ⟨payload, hsc⟩
  intro hfree
  have htarget : EvalFree (deferredPayload payload) := by
    exact (evalFree_iff_of_structuralCongruence hsc).mp hfree
  simp [EvalFree, deferredPayload] at htarget

theorem not_evalFree_of_coreConsumesEvalPayload
    {p q : Pattern} {hred : Reduction.Reduces p q}
    (hconsume : CoreConsumesEvalPayload hred) :
    ¬ EvalFree p := by
  induction hconsume with
  | comm hlike =>
      intro hfree
      exact not_evalFree_of_deferredPayloadLike hlike
        (by simpa [EvalFree, EvalFreeList] using hfree.1.2)
  | @equiv p p' q q' hsc₁ hred hsc₂ _ ih =>
      intro hfree
      exact ih ((evalFree_iff_of_structuralCongruence hsc₁).mp hfree)
  | par _ ih =>
      intro hfree
      exact ih (by simpa [EvalFree, EvalFreeList] using hfree.1)
  | @par_any p q before after hred _ ih =>
      intro hfree
      have hlist : EvalFreeList (before ++ [p] ++ after) := by
        simpa [EvalFree] using hfree
      exact ih (evalFree_of_evalFreeList_middle hlist)
  | par_set _ ih =>
      intro hfree
      exact ih (by simpa [EvalFree, EvalFreeList] using hfree.1)
  | @par_set_any p q before after hred _ ih =>
      intro hfree
      have hlist : EvalFreeList (before ++ [p] ++ after) := by
        simpa [EvalFree] using hfree
      exact ih (evalFree_of_evalFreeList_middle hlist)

theorem rhometa_core_guard_of_evalFree
    {p q : Pattern} (hfree : EvalFree p) (hred : Reduction.Reduces p q) :
    ¬ CoreConsumesEvalPayload hred := by
  intro hconsume
  exact not_evalFree_of_coreConsumesEvalPayload hconsume hfree

theorem nonempty_reduces_of_rhometaReduces_of_evalFree
    {space : Space} {dispatch : GroundedDispatch}
    {p q : Pattern} (hfree : EvalFree p)
    (hred : RhometaReduces space dispatch p q) :
    Nonempty (Reduction.Reduces p q) := by
  induction hred with
  | core hcore _ =>
      exact ⟨hcore⟩
  | evalComm _ hcert =>
      exfalso
      simp [EvalFree, EvalFreeList, deferredPayload] at hfree
  | equiv hsc hstep hsc' ih =>
      rcases ih ((evalFree_iff_of_structuralCongruence hsc).mp hfree) with ⟨hcore⟩
      exact ⟨Reduction.Reduces.equiv hsc hcore hsc'⟩
  | par hstep ih =>
      rcases ih (by simpa [EvalFree, EvalFreeList] using hfree.1) with ⟨hcore⟩
      exact ⟨Reduction.Reduces.par hcore⟩
  | @par_any pInner qInner before after hstep ih =>
      have hlist : EvalFreeList (before ++ [pInner] ++ after) := by
        simpa [EvalFree] using hfree
      rcases ih (evalFree_of_evalFreeList_middle hlist) with ⟨hcore⟩
      exact ⟨Reduction.Reduces.par_any (before := before) (after := after) hcore⟩
  | par_set hstep ih =>
      rcases ih (by simpa [EvalFree, EvalFreeList] using hfree.1) with ⟨hcore⟩
      exact ⟨Reduction.Reduces.par_set hcore⟩
  | @par_set_any pInner qInner before after hstep ih =>
      have hlist : EvalFreeList (before ++ [pInner] ++ after) := by
        simpa [EvalFree] using hfree
      rcases ih (evalFree_of_evalFreeList_middle hlist) with ⟨hcore⟩
      exact ⟨Reduction.Reduces.par_set_any (before := before) (after := after) hcore⟩

theorem rhometaReduces_iff_reduces_of_evalFree
    {space : Space} {dispatch : GroundedDispatch}
    {p q : Pattern} (hfree : EvalFree p) :
    Nonempty (RhometaReduces space dispatch p q) ↔
      Nonempty (Reduction.Reduces p q) := by
  constructor
  · intro hred
    rcases hred with ⟨hred⟩
    exact nonempty_reduces_of_rhometaReduces_of_evalFree hfree hred
  · intro hred
    rcases hred with ⟨hred⟩
    exact ⟨RhometaReduces.core hred
      (rhometa_core_guard_of_evalFree hfree hred)⟩

theorem ioCount_pos_of_core_reduces {p q : Pattern}
    (hred : Reduction.Reduces p q) :
    0 < ioCount p := by
  induction hred with
  | comm =>
      simp [ioCount, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  | @equiv p p' q q' hsc _ _ ih =>
      have hw : ioCount p = ioCount p' := ioCount_SC hsc
      omega
  | par _ ih =>
      simp [ioCount, List.map_cons, List.sum_cons]
      omega
  | par_any _ ih =>
      simp [ioCount, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
      omega
  | par_set _ ih =>
      simp [ioCount, List.map_cons, List.sum_cons]
      omega
  | par_set_any _ ih =>
      simp [ioCount, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
      omega

theorem ioCount_pos_of_rhometa_reduces
    {space : Space} {dispatch : GroundedDispatch} {p q : Pattern}
    (hred : RhometaReduces space dispatch p q) :
    0 < ioCount p := by
  induction hred with
  | core hcore _ =>
      exact ioCount_pos_of_core_reduces hcore
  | @evalComm n body rest payload value _ hcert =>
      have hz : ioCount (deferredPayload payload) = 0 :=
        ioCount_deferredPayload_zero payload
      simp [ioCount, hz,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  | @equiv p p' q q' hsc _ _ ih =>
      have hw : ioCount p = ioCount p' := ioCount_SC hsc
      omega
  | par _ ih =>
      simp [ioCount, List.map_cons, List.sum_cons]
      omega
  | par_any _ ih =>
      simp [ioCount, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
      omega
  | par_set _ ih =>
      simp [ioCount, List.map_cons, List.sum_cons]
      omega
  | par_set_any _ ih =>
      simp [ioCount, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
      omega

theorem rhometaNormalForm_of_ioCount_zero
    {space : Space} {dispatch : GroundedDispatch} {p : Pattern}
    (hzero : ioCount p = 0) :
    RhometaNormalForm space dispatch p := by
  intro hstep
  rcases hstep with ⟨q, hq⟩
  rcases hq with ⟨hred⟩
  have hpos : 0 < ioCount p := ioCount_pos_of_rhometa_reduces hred
  omega

theorem evalDropResidual_normalForm
    {space : Space} {dispatch : GroundedDispatch} (value : Atom) :
    RhometaNormalForm space dispatch (evalDropResidual value) := by
  apply rhometaNormalForm_of_ioCount_zero
  simpa [evalDropResidual, semanticNormalizeProc_wrappedValue, ioCount] using
    ioCount_wrappedValue_zero value

theorem rhometaNormalForm_of_SC_evalDropResidual
    {space : Space} {dispatch : GroundedDispatch}
    {q : Pattern} {value : Atom}
    (hsc : StructuralCongruence q (evalDropResidual value)) :
    RhometaNormalForm space dispatch q := by
  apply rhometaNormalForm_of_ioCount_zero
  calc
    ioCount q = ioCount (evalDropResidual value) := ioCount_SC hsc
    _ = 0 := by
      simpa [evalDropResidual, semanticNormalizeProc_wrappedValue, ioCount] using
        ioCount_wrappedValue_zero value

theorem rhometaCanStep_iff_of_structuralCongruence
    {space : Space} {dispatch : GroundedDispatch}
    {p q : Pattern}
    (hsc : StructuralCongruence p q) :
    RhometaCanStep space dispatch p ↔
      RhometaCanStep space dispatch q := by
  constructor
  · rintro ⟨r, ⟨hred⟩⟩
    exact ⟨r, ⟨RhometaReduces.equiv
      (StructuralCongruence.symm _ _ hsc)
      hred
      (StructuralCongruence.refl _)⟩⟩
  · rintro ⟨r, ⟨hred⟩⟩
    exact ⟨r, ⟨RhometaReduces.equiv
      hsc
      hred
      (StructuralCongruence.refl _)⟩⟩

theorem rhometaNormalForm_iff_of_structuralCongruence
    {space : Space} {dispatch : GroundedDispatch}
    {p q : Pattern}
    (hsc : StructuralCongruence p q) :
    RhometaNormalForm space dispatch p ↔
      RhometaNormalForm space dispatch q := by
  constructor
  · intro hnf hstep
    exact hnf ((rhometaCanStep_iff_of_structuralCongruence hsc).mpr hstep)
  · intro hnf hstep
    exact hnf ((rhometaCanStep_iff_of_structuralCongruence hsc).mp hstep)

theorem rhometaReducesStar_representative_of_source_structuralCongruence
    {space : Space} {dispatch : GroundedDispatch}
    {p p' q' : Pattern}
    (hsc : StructuralCongruence p p')
    (hstar : RhometaReducesStar space dispatch p' q') :
    ∃ q,
      Nonempty (RhometaReducesStar space dispatch p q) ∧
      StructuralCongruence q q' := by
  induction hstar with
  | refl _ =>
      exact ⟨p, ⟨RhometaReducesStar.refl p⟩, hsc⟩
  | @step _ q r hstep htail =>
      exact ⟨r,
        ⟨RhometaReducesStar.step
            (RhometaReduces.equiv hsc hstep (StructuralCongruence.refl _))
            htail⟩,
        StructuralCongruence.refl _⟩

theorem rhometaOutcomes_representative_of_source_structuralCongruence
    {space : Space} {dispatch : GroundedDispatch}
    {p p' q' : Pattern}
    (hsc : StructuralCongruence p p')
    (hout : q' ∈ RhometaOutcomes space dispatch p') :
    ∃ q,
      q ∈ RhometaOutcomes space dispatch p ∧
      StructuralCongruence q q' := by
  rcases hout with ⟨hstar, hnf⟩
  rcases rhometaReducesStar_representative_of_source_structuralCongruence
      (space := space) (dispatch := dispatch) hsc hstar.some with
    ⟨q, hstar', hq⟩
  refine ⟨q, ⟨hstar', ?_⟩, hq⟩
  exact (rhometaNormalForm_iff_of_structuralCongruence hq).mpr hnf

theorem rhometaOutcomes_sc_representative_iff
    {space : Space} {dispatch : GroundedDispatch}
    {p p' q : Pattern}
    (hsc : StructuralCongruence p p') :
    (∃ r,
      r ∈ RhometaOutcomes space dispatch p ∧
      StructuralCongruence r q) ↔
    (∃ r,
      r ∈ RhometaOutcomes space dispatch p' ∧
      StructuralCongruence r q) := by
  constructor
  · rintro ⟨r, hr, hrq⟩
    rcases rhometaOutcomes_representative_of_source_structuralCongruence
        (space := space) (dispatch := dispatch)
        (p := p') (p' := p) (q' := r)
        (StructuralCongruence.symm _ _ hsc) hr with
      ⟨r', hr', hr'r⟩
    exact ⟨r', hr', StructuralCongruence.trans _ _ _ hr'r hrq⟩
  · rintro ⟨r, hr, hrq⟩
    rcases rhometaOutcomes_representative_of_source_structuralCongruence
        (space := space) (dispatch := dispatch)
        (p := p) (p' := p') (q' := r) hsc hr with
      ⟨r', hr', hr'r⟩
    exact ⟨r', hr', StructuralCongruence.trans _ _ _ hr'r hrq⟩

theorem rhometaSCObservedOutcomes_eq_of_source_structuralCongruence
    {space : Space} {dispatch : GroundedDispatch}
    {p p' : Pattern}
    (hsc : StructuralCongruence p p') :
    RhometaSCObservedOutcomes space dispatch p =
      RhometaSCObservedOutcomes space dispatch p' := by
  ext obs
  constructor
  · rintro ⟨q, r, hq, hqr, hdec⟩
    rcases rhometaOutcomes_representative_of_source_structuralCongruence
        (space := space) (dispatch := dispatch)
        (p := p') (p' := p) (q' := q)
        (StructuralCongruence.symm _ _ hsc) hq with
      ⟨q', hq', hq'q⟩
    exact ⟨q', r, hq', StructuralCongruence.trans _ _ _ hq'q hqr, hdec⟩
  · rintro ⟨q, r, hq, hqr, hdec⟩
    rcases rhometaOutcomes_representative_of_source_structuralCongruence
        (space := space) (dispatch := dispatch)
        (p := p) (p' := p') (q' := q) hsc hq with
      ⟨q', hq', hq'q⟩
    exact ⟨q', r, hq', StructuralCongruence.trans _ _ _ hq'q hqr, hdec⟩

private theorem dropShellLike_rhometaOutcomes_sc_representative_iff
    {space : Space} {dispatch : GroundedDispatch}
    {chan p q : Pattern} {payload : Atom}
    (hshape : DropShellLike chan payload p) :
    (∃ r,
      r ∈ RhometaOutcomes space dispatch p ∧
      StructuralCongruence r q) ↔
    (∃ r,
      r ∈ RhometaOutcomes space dispatch (evalDropSource chan payload) ∧
      StructuralCongruence r q) :=
  rhometaOutcomes_sc_representative_iff
    (space := space) (dispatch := dispatch) hshape.source_sc

private theorem dropShellLike_scObservedOutcomes_eq_evalDropSource
    {space : Space} {dispatch : GroundedDispatch}
    {chan p : Pattern} {payload : Atom}
    (hshape : DropShellLike chan payload p) :
    RhometaSCObservedOutcomes space dispatch p =
      RhometaSCObservedOutcomes space dispatch (evalDropSource chan payload) :=
  rhometaSCObservedOutcomes_eq_of_source_structuralCongruence
    (space := space) (dispatch := dispatch) hshape.source_sc

private theorem dropShellLike_scObservedOutcomes_mem_iff_evalDropSource
    {space : Space} {dispatch : GroundedDispatch}
    {chan p : Pattern} {payload : Atom}
    (hshape : DropShellLike chan payload p)
    {obs : Multiset Atom × (Unit × Multiplicative (Multiset Empty))} :
    obs ∈ RhometaSCObservedOutcomes space dispatch p ↔
      obs ∈
        RhometaSCObservedOutcomes space dispatch (evalDropSource chan payload) := by
  rw [dropShellLike_scObservedOutcomes_eq_evalDropSource
    (space := space) (dispatch := dispatch) hshape]

theorem rhometaReducesStar_eq_of_normalForm
    {space : Space} {dispatch : GroundedDispatch}
    {p q : Pattern}
    (hnf : RhometaNormalForm space dispatch p)
    (hstar : RhometaReducesStar space dispatch p q) :
    p = q := by
  induction hstar with
  | refl _ =>
      rfl
  | @step p q r hstep htail ih =>
      exfalso
      exact hnf ⟨q, ⟨hstep⟩⟩

theorem rhometaOutcomes_self_iff_normalForm
    {space : Space} {dispatch : GroundedDispatch}
    {p : Pattern} :
    p ∈ RhometaOutcomes space dispatch p ↔
      RhometaNormalForm space dispatch p := by
  constructor
  · intro hp
    exact hp.2
  · intro hnf
    exact ⟨⟨RhometaReducesStar.refl _⟩, hnf⟩

theorem not_mem_rhometaOutcomes_of_normalForm_ne
    {space : Space} {dispatch : GroundedDispatch}
    {p q : Pattern}
    (hnf : RhometaNormalForm space dispatch p)
    (hneq : q ≠ p) :
    q ∉ RhometaOutcomes space dispatch p := by
  intro hq
  rcases hq with ⟨hstar, _⟩
  have hpq : p = q := rhometaReducesStar_eq_of_normalForm hnf hstar.some
  exact hneq hpq.symm

theorem mem_rhometaOutcomes_iff_eq_of_normalForm
    {space : Space} {dispatch : GroundedDispatch}
    {p q : Pattern}
    (hnf : RhometaNormalForm space dispatch p) :
    q ∈ RhometaOutcomes space dispatch p ↔ q = p := by
  constructor
  · intro hq
    by_cases hpq : q = p
    · exact hpq
    · exact False.elim (not_mem_rhometaOutcomes_of_normalForm_ne
        (space := space) (dispatch := dispatch)
        (p := p) (q := q) hnf hpq hq)
  · intro hqp
    subst hqp
    simpa using (rhometaOutcomes_self_iff_normalForm
      (space := space) (dispatch := dispatch)
      (p := q)).2 hnf

theorem evalDropSource_outcomes_iff_eq_of_normalForm
    {space : Space} {dispatch : GroundedDispatch}
    {chan q : Pattern} {payload : Atom}
    (hnf : RhometaNormalForm space dispatch (evalDropSource chan payload)) :
    q ∈ RhometaOutcomes space dispatch (evalDropSource chan payload) ↔
      q = evalDropSource chan payload := by
  exact mem_rhometaOutcomes_iff_eq_of_normalForm
    (space := space) (dispatch := dispatch)
    (p := evalDropSource chan payload) (q := q) hnf

theorem rhometaOutcomes_eq_singleton_of_normalForm
    {space : Space} {dispatch : GroundedDispatch}
    {p : Pattern}
    (hnf : RhometaNormalForm space dispatch p) :
    RhometaOutcomes space dispatch p = ({p} : Set Pattern) := by
  ext q
  simp [mem_rhometaOutcomes_iff_eq_of_normalForm
    (space := space) (dispatch := dispatch)
    (p := p) (q := q) hnf]

theorem rhometaOutcomes_not_raw_structuralCongruence_invariant
    (space : Space) (dispatch : GroundedDispatch) :
    ∃ p p',
      StructuralCongruence p p' ∧
      RhometaOutcomes space dispatch p ≠
        RhometaOutcomes space dispatch p' := by
  let zero : Pattern := .apply "PZero" []
  let wrappedZero : Pattern := .collection .hashBag [zero] none
  refine ⟨wrappedZero, zero, StructuralCongruence.par_singleton zero, ?_⟩
  have hnfWrapped : RhometaNormalForm space dispatch wrappedZero := by
    apply rhometaNormalForm_of_ioCount_zero
    simp [wrappedZero, zero, ioCount]
  have hnfZero : RhometaNormalForm space dispatch zero := by
    apply rhometaNormalForm_of_ioCount_zero
    simp [zero, ioCount]
  intro hsets
  have hwrapped :
      wrappedZero ∈ RhometaOutcomes space dispatch wrappedZero := by
    rw [rhometaOutcomes_eq_singleton_of_normalForm hnfWrapped]
    simp
  have hmemOut : wrappedZero ∈ RhometaOutcomes space dispatch zero := by
    rw [← hsets]
    exact hwrapped
  have hmem : wrappedZero ∈ ({zero} : Set Pattern) := by
    rw [rhometaOutcomes_eq_singleton_of_normalForm hnfZero] at hmemOut
    exact hmemOut
  have heq : wrappedZero = zero := Set.mem_singleton_iff.mp hmem
  simp [wrappedZero, zero] at heq

theorem evalDropSource_outcomes_eq_singleton_of_normalForm
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload : Atom}
    (hnf : RhometaNormalForm space dispatch (evalDropSource chan payload)) :
    RhometaOutcomes space dispatch (evalDropSource chan payload) =
      ({evalDropSource chan payload} : Set Pattern) := by
  exact rhometaOutcomes_eq_singleton_of_normalForm
    (space := space) (dispatch := dispatch)
    (p := evalDropSource chan payload) hnf

theorem evalDropResidual_outcomes_iff_eq
    {space : Space} {dispatch : GroundedDispatch}
    {value : Atom} {q : Pattern} :
    q ∈ RhometaOutcomes space dispatch (evalDropResidual value) ↔
      q = evalDropResidual value := by
  exact mem_rhometaOutcomes_iff_eq_of_normalForm
    (space := space) (dispatch := dispatch)
    (p := evalDropResidual value) (q := q)
    (evalDropResidual_normalForm
      (space := space) (dispatch := dispatch) value)

theorem evalDropResidual_outcomes_eq_singleton
    {space : Space} {dispatch : GroundedDispatch}
    {value : Atom} :
    RhometaOutcomes space dispatch (evalDropResidual value) =
      ({evalDropResidual value} : Set Pattern) := by
  exact rhometaOutcomes_eq_singleton_of_normalForm
    (space := space) (dispatch := dispatch)
    (p := evalDropResidual value)
    (evalDropResidual_normalForm
      (space := space) (dispatch := dispatch) value)

theorem value_eq_of_evalDropResidual_outcome_decode
    {space : Space} {dispatch : GroundedDispatch}
    {q : Pattern} {value value' : Atom}
    (hout : q ∈ RhometaOutcomes space dispatch (evalDropResidual value'))
    (hdecode :
      scReifiedOutcomeOf? q =
        some (({value} : Multiset Atom), ((), (1 : Multiplicative (Multiset Empty))))) :
    value = value' := by
  have hq : q = evalDropResidual value' :=
    (evalDropResidual_outcomes_iff_eq
      (space := space) (dispatch := dispatch)
      (value := value') (q := q)).mp hout
  subst hq
  simpa [scReifiedOutcomeOf?_evalDropResidual] using hdecode.symm

theorem evalDropResidual_decodedOutcomes_eq_singleton
    {space : Space} {dispatch : GroundedDispatch}
    {value : Atom} :
    RhometaDecodedOutcomes space dispatch (evalDropResidual value) =
      {((({value} : Multiset Atom),
        ((), (1 : Multiplicative (Multiset Empty)))))} := by
  ext obs
  constructor
  · rintro ⟨q, hout, hdecode⟩
    have hq : q = evalDropResidual value :=
      (evalDropResidual_outcomes_iff_eq
        (space := space) (dispatch := dispatch)
        (value := value) (q := q)).mp hout
    subst hq
    simp [scReifiedOutcomeOf?_evalDropResidual] at hdecode
    simpa [Set.mem_singleton_iff] using hdecode.symm
  · intro hobs
    have hobs' :
        obs =
          (({value} : Multiset Atom),
            ((), (1 : Multiplicative (Multiset Empty)))) := by
      simpa using hobs
    subst hobs'
    refine ⟨evalDropResidual value, ?_,
      scReifiedOutcomeOf?_evalDropResidual value⟩
    exact ⟨⟨RhometaReducesStar.refl _⟩,
      evalDropResidual_normalForm (space := space) (dispatch := dispatch) value⟩

private theorem certifiedPayloadResult_of_evalDropResidual_outcome_decode
    {space : Space} {dispatch : GroundedDispatch}
    {payload value value' : Atom} {q : Pattern}
    (hcert : CertifiedPayloadResult space dispatch payload value')
    (hout : q ∈ RhometaOutcomes space dispatch (evalDropResidual value'))
    (hdecode :
      scReifiedOutcomeOf? q =
        some (({value} : Multiset Atom), ((), (1 : Multiplicative (Multiset Empty))))) :
    CertifiedPayloadResult space dispatch payload value := by
  exact certifiedPayloadResult_of_value_eq
    (value_eq_of_evalDropResidual_outcome_decode
      (space := space) (dispatch := dispatch)
      (q := q) (value := value) (value' := value')
      hout hdecode)
    hcert

private theorem certifiedPayloadResult_of_evalDrop_evalComm_outcome_decode
    {space : Space} {dispatch : GroundedDispatch}
    {n chan body q : Pattern} {rest : List Pattern}
    {payload₁ payload₂ value value' : Atom}
    (hsource : evalSource n payload₁ body rest = evalDropSource chan payload₂)
    (hcert : CertifiedPayloadResult space dispatch payload₁ value')
    (hout :
      q ∈ RhometaOutcomes space dispatch
        (.collection .hashBag
          ([semanticCommSubst body (wrappedValue value')] ++ rest) none))
    (hdecode :
      scReifiedOutcomeOf? q =
        some (({value} : Multiset Atom), ((), (1 : Multiplicative (Multiset Empty))))) :
    CertifiedPayloadResult space dispatch payload₂ value := by
  obtain ⟨hcert', hresidual⟩ :=
    evalDropSource_evalComm_residual_exact
      (space := space) (dispatch := dispatch)
      (n := n) (chan := chan) (body := body) (rest := rest)
      (payload₁ := payload₁) (payload₂ := payload₂)
      (value := value') hsource hcert
  rw [hresidual] at hout
  exact certifiedPayloadResult_of_evalDropResidual_outcome_decode
    (space := space) (dispatch := dispatch)
    (payload := payload₂) (value := value) (value' := value')
    (q := q) hcert' hout hdecode

private theorem certifiedPayloadResult_of_evalDrop_evalComm_decodedOutcome
    {space : Space} {dispatch : GroundedDispatch}
    {n chan body : Pattern} {rest : List Pattern}
    {payload₁ payload₂ value value' : Atom}
    (hsource : evalSource n payload₁ body rest = evalDropSource chan payload₂)
    (hcert : CertifiedPayloadResult space dispatch payload₁ value')
    (hobs :
      (({value} : Multiset Atom), ((), (1 : Multiplicative (Multiset Empty)))) ∈
        RhometaDecodedOutcomes space dispatch
          (.collection .hashBag
            ([semanticCommSubst body (wrappedValue value')] ++ rest) none)) :
    CertifiedPayloadResult space dispatch payload₂ value := by
  rcases hobs with ⟨q, hout, hdecode⟩
  exact certifiedPayloadResult_of_evalDrop_evalComm_outcome_decode
    (space := space) (dispatch := dispatch)
    (n := n) (chan := chan) (body := body) (rest := rest)
    (payload₁ := payload₁) (payload₂ := payload₂)
    (value := value) (value' := value') (q := q)
    hsource hcert hout hdecode

theorem evalDropSource_not_normalForm_of_certified
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload value : Atom}
    (hcert : CertifiedPayloadResult space dispatch payload value) :
    ¬ RhometaNormalForm space dispatch (evalDropSource chan payload) := by
  intro hnf
  exact hnf ⟨evalDropResidual value,
    evalDrop_certified_branch
      (space := space) (dispatch := dispatch)
      (payload := payload) (value := value) hcert⟩

theorem evalDropSource_normalForm_implies_no_certified
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload : Atom}
    (hnf : RhometaNormalForm space dispatch (evalDropSource chan payload)) :
    ∀ value, ¬ CertifiedPayloadResult space dispatch payload value := by
  intro value hcert
  exact evalDropSource_not_normalForm_of_certified
    (space := space) (dispatch := dispatch)
    (chan := chan) (payload := payload) (value := value) hcert hnf

theorem evalDropSource_outcome_implies_no_certified
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload : Atom} :
    evalDropSource chan payload ∈
        RhometaOutcomes space dispatch (evalDropSource chan payload) →
      ∀ value, ¬ CertifiedPayloadResult space dispatch payload value := by
  intro hout
  exact evalDropSource_normalForm_implies_no_certified
    (space := space) (dispatch := dispatch)
    (chan := chan) (payload := payload)
    ((rhometaOutcomes_self_iff_normalForm
      (space := space) (dispatch := dispatch)
      (p := evalDropSource chan payload)).mp hout)

theorem evalDropSource_not_outcome_of_certified
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload value : Atom}
    (hcert : CertifiedPayloadResult space dispatch payload value) :
    evalDropSource chan payload ∉
      RhometaOutcomes space dispatch (evalDropSource chan payload) := by
  intro hout
  exact evalDropSource_outcome_implies_no_certified
    (space := space) (dispatch := dispatch)
    (chan := chan) (payload := payload) hout value hcert

theorem evalDrop_outcome_factors_through_one_step_of_certified
    {space : Space} {dispatch : GroundedDispatch}
    {chan q : Pattern} {payload value : Atom}
    (hcert : CertifiedPayloadResult space dispatch payload value)
    (hout : q ∈ RhometaOutcomes space dispatch (evalDropSource chan payload)) :
    ∃ r,
      Nonempty (RhometaReduces space dispatch (evalDropSource chan payload) r) ∧
      q ∈ RhometaOutcomes space dispatch r := by
  rcases hout with ⟨⟨hstar⟩, hnf⟩
  cases hstar with
  | refl _ =>
      exfalso
      exact evalDropSource_not_normalForm_of_certified
        (space := space) (dispatch := dispatch)
        (chan := chan) (payload := payload) hcert hnf
  | @step _ r _ hstep htail =>
      exact ⟨r, ⟨hstep⟩, ⟨⟨htail⟩, hnf⟩⟩

theorem evalDrop_scObservedOutcome_factors_through_one_step_of_certified
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload value : Atom}
    {obs : Multiset Atom × (Unit × Multiplicative (Multiset Empty))}
    (hcert : CertifiedPayloadResult space dispatch payload value)
    (hobs :
      obs ∈ RhometaSCObservedOutcomes space dispatch
        (evalDropSource chan payload)) :
    ∃ r q s,
      Nonempty (RhometaReduces space dispatch (evalDropSource chan payload) r) ∧
      q ∈ RhometaOutcomes space dispatch r ∧
      StructuralCongruence q s ∧
      scReifiedOutcomeOf? s = some obs := by
  rcases hobs with ⟨q, s, hq, hqs, hdec⟩
  rcases evalDrop_outcome_factors_through_one_step_of_certified
      (space := space) (dispatch := dispatch)
      (chan := chan) (payload := payload) (value := value) hcert hq with
    ⟨r, hstep, hout⟩
  exact ⟨r, q, s, hstep, hout, hqs, hdec⟩

theorem evalDrop_decoded_outcome_factors_through_one_step
    {space : Space} {dispatch : GroundedDispatch}
    {chan q : Pattern} {payload value : Atom}
    (hout : q ∈ RhometaOutcomes space dispatch (evalDropSource chan payload))
    (hdecode :
      scReifiedOutcomeOf? q =
        some (({value} : Multiset Atom), ((), (1 : Multiplicative (Multiset Empty))))) :
    ∃ r,
      Nonempty (RhometaReduces space dispatch (evalDropSource chan payload) r) ∧
      q ∈ RhometaOutcomes space dispatch r := by
  rcases hout with ⟨⟨hstar⟩, hnf⟩
  cases hstar with
  | refl _ =>
      exfalso
      have hsource :
          scReifiedOutcomeOf? (evalDropSource chan payload) =
            some (({value} : Multiset Atom), ((), (1 : Multiplicative (Multiset Empty)))) := by
        simpa using hdecode
      rw [scReifiedOutcomeOf?_evalDropSource chan payload] at hsource
      cases hsource
  | @step _ r _ hstep htail =>
      refine ⟨r, ⟨hstep⟩, ?_⟩
      exact ⟨⟨htail⟩, hnf⟩

theorem evalDrop_decodedSingletonOutcome_factors_through_one_step
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload value : Atom}
    (hobs :
      (({value} : Multiset Atom), ((), (1 : Multiplicative (Multiset Empty)))) ∈
        RhometaDecodedOutcomes space dispatch (evalDropSource chan payload)) :
    ∃ r q,
      Nonempty (RhometaReduces space dispatch (evalDropSource chan payload) r) ∧
      q ∈ RhometaOutcomes space dispatch r ∧
      scReifiedOutcomeOf? q =
        some (({value} : Multiset Atom), ((), (1 : Multiplicative (Multiset Empty)))) := by
  rcases hobs with ⟨q, hout, hdecode⟩
  rcases evalDrop_decoded_outcome_factors_through_one_step
      (space := space) (dispatch := dispatch)
      (chan := chan) (payload := payload)
    (q := q) (value := value) hout hdecode with
    ⟨r, hstep, hout'⟩
  exact ⟨r, q, hstep, hout', hdecode⟩

private theorem dropShellLike_evalComm_outputPayload
    {chan n body : Pattern} {payload payload' : Atom} {rest : List Pattern}
    (hshape : DropShellLike chan payload
      (.collection .hashBag
        ([.apply "POutput" [n, deferredPayload payload'],
          .apply "PInput" [n, .lambda none body]] ++ rest) none)) :
    StructuralCongruence (deferredPayload payload') (deferredPayload payload) := by
  simpa [OutputsPayload, OutputsPayloadList] using hshape.outputs_payload.1

private theorem no_rhometaCore_from_dropShellLike
    {p q chan : Pattern} {payload : Atom}
    {hcore : Reduction.Reduces p q}
    (hshape : DropShellLike chan payload p)
    (hguard : ¬ CoreConsumesEvalPayload hcore) :
    False := by
  exact no_rhometaCore_from_SC_evalDropSource hshape.source_sc hguard

theorem evalDrop_certified_value_mayReachable
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload value : Atom}
    (hcert : CertifiedPayloadResult space dispatch payload value) :
    evalDropResidual value ∈ MayReachable space dispatch (evalDropSource chan payload) := by
  refine ⟨RhometaReducesStar.step ?_ (RhometaReducesStar.refl _)⟩
  exact (evalDrop_certified_branch
    (space := space) (dispatch := dispatch)
    (chan := chan) (payload := payload) (value := value) hcert).some

theorem evalDrop_certified_value_outcome
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload value : Atom}
    (hcert : CertifiedPayloadResult space dispatch payload value) :
    evalDropResidual value ∈
      RhometaOutcomes space dispatch (evalDropSource chan payload) := by
  exact ⟨evalDrop_certified_value_mayReachable
            (space := space) (dispatch := dispatch)
            (chan := chan) (payload := payload) (value := value) hcert,
         evalDropResidual_normalForm (space := space) (dispatch := dispatch) value⟩

theorem evalDrop_certified_value_outcome_of_structuralResidual
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload value : Atom} {q : Pattern}
    (hcert : CertifiedPayloadResult space dispatch payload value)
    (hsc : StructuralCongruence (evalDropResidual value) q) :
    q ∈ RhometaOutcomes space dispatch (evalDropSource chan payload) := by
  refine ⟨?_, ?_⟩
  · refine ⟨RhometaReducesStar.step ?_ (RhometaReducesStar.refl _)⟩
    exact RhometaReduces.equiv
      (StructuralCongruence.refl _)
      (evalDrop_certified_branch hcert).some
      hsc
  · exact (rhometaNormalForm_iff_of_structuralCongruence hsc).mp
      (evalDropResidual_normalForm (space := space) (dispatch := dispatch) value)

/-- Operational soundness seed for B7 on the exact drop shell: every certified payload result
already appears as a quiescent operational outcome whose SC-aware decoder recovers the singleton
post-reification observable. -/
theorem evalDrop_certified_value_outcome_decodes
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload value : Atom}
    (hcert : CertifiedPayloadResult space dispatch payload value) :
    ∃ q,
      q ∈ RhometaOutcomes space dispatch (evalDropSource chan payload) ∧
      scReifiedOutcomeOf? q =
        some (({value} : Multiset Atom), ((), (1 : Multiplicative (Multiset Empty)))) := by
  refine ⟨evalDropResidual value, ?_, ?_⟩
  · exact evalDrop_certified_value_outcome
      (space := space) (dispatch := dispatch)
      (chan := chan) (payload := payload) (value := value) hcert
  · exact scReifiedOutcomeOf?_evalDropResidual value

theorem evalDrop_certified_value_decodedOutcome
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload value : Atom}
    (hcert : CertifiedPayloadResult space dispatch payload value) :
    (({value} : Multiset Atom), ((), (1 : Multiplicative (Multiset Empty)))) ∈
      RhometaDecodedOutcomes space dispatch (evalDropSource chan payload) := by
  refine ⟨evalDropResidual value, ?_, ?_⟩
  · exact evalDrop_certified_value_outcome
      (space := space) (dispatch := dispatch)
      (chan := chan) (payload := payload) (value := value) hcert
  · exact scReifiedOutcomeOf?_evalDropResidual value

theorem evalDrop_certified_value_scObservedOutcome
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload value : Atom}
    (hcert : CertifiedPayloadResult space dispatch payload value) :
    (({value} : Multiset Atom), ((), (1 : Multiplicative (Multiset Empty)))) ∈
      RhometaSCObservedOutcomes space dispatch (evalDropSource chan payload) := by
  refine ⟨evalDropResidual value, evalDropResidual value, ?_, StructuralCongruence.refl _, ?_⟩
  · exact evalDrop_certified_value_outcome
      (space := space) (dispatch := dispatch)
      (chan := chan) (payload := payload) (value := value) hcert
  · exact scReifiedOutcomeOf?_evalDropResidual value

theorem evalDrop_certified_image_subset_decodedOutcomes
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload : Atom} :
    {obs | ∃ value,
        CertifiedPayloadResult space dispatch payload value ∧
        obs =
          (({value} : Multiset Atom),
            ((), (1 : Multiplicative (Multiset Empty))))} ⊆
      RhometaDecodedOutcomes space dispatch (evalDropSource chan payload) := by
  rintro obs ⟨value, hcert, rfl⟩
  exact evalDrop_certified_value_decodedOutcome
    (space := space) (dispatch := dispatch)
    (chan := chan) (payload := payload) hcert

theorem evalDrop_certified_decoded_image_eq_certified_image
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload : Atom} :
    {obs |
      obs ∈ RhometaDecodedOutcomes space dispatch (evalDropSource chan payload) ∧
      ∃ value,
        CertifiedPayloadResult space dispatch payload value ∧
        obs =
          (({value} : Multiset Atom),
            ((), (1 : Multiplicative (Multiset Empty))))} =
    {obs | ∃ value,
        CertifiedPayloadResult space dispatch payload value ∧
        obs =
          (({value} : Multiset Atom),
            ((), (1 : Multiplicative (Multiset Empty))))} := by
  ext obs
  constructor
  · intro hobs
    exact hobs.2
  · rintro ⟨value, hcert, rfl⟩
    exact ⟨evalDrop_certified_value_decodedOutcome
      (space := space) (dispatch := dispatch)
      (chan := chan) (payload := payload) hcert, value, hcert, rfl⟩

theorem evalDrop_certified_decoded_image_mem_iff
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload : Atom}
    {obs : Multiset Atom × (Unit × Multiplicative (Multiset Empty))} :
    (obs ∈ RhometaDecodedOutcomes space dispatch (evalDropSource chan payload) ∧
      ∃ value,
        CertifiedPayloadResult space dispatch payload value ∧
        obs =
          (({value} : Multiset Atom),
            ((), (1 : Multiplicative (Multiset Empty))))) ↔
    ∃ value,
      CertifiedPayloadResult space dispatch payload value ∧
      obs =
        (({value} : Multiset Atom),
          ((), (1 : Multiplicative (Multiset Empty)))) := by
  have hset := evalDrop_certified_decoded_image_eq_certified_image
    (space := space) (dispatch := dispatch)
    (chan := chan) (payload := payload)
  exact Set.ext_iff.mp hset obs

theorem scObservedOutcome_of_outcome_structural_evalDropResidual
    {space : Space} {dispatch : GroundedDispatch}
    {p q : Pattern} {value : Atom}
    (hout : q ∈ RhometaOutcomes space dispatch p)
    (hsc : StructuralCongruence q (evalDropResidual value)) :
    (({value} : Multiset Atom), ((), (1 : Multiplicative (Multiset Empty)))) ∈
      RhometaSCObservedOutcomes space dispatch p := by
  exact ⟨q, evalDropResidual value, hout, hsc,
    scReifiedOutcomeOf?_evalDropResidual value⟩

theorem scObservedOutcome_of_step_outcome_structural_evalDropResidual
    {space : Space} {dispatch : GroundedDispatch}
    {p r q : Pattern} {value : Atom}
    (hstep : RhometaReduces space dispatch p r)
    (hout : q ∈ RhometaOutcomes space dispatch r)
    (hsc : StructuralCongruence q (evalDropResidual value)) :
    (({value} : Multiset Atom), ((), (1 : Multiplicative (Multiset Empty)))) ∈
      RhometaSCObservedOutcomes space dispatch p := by
  rcases hout with ⟨hstar, hnf⟩
  exact scObservedOutcome_of_outcome_structural_evalDropResidual
    (space := space) (dispatch := dispatch)
    (p := p) (q := q) (value := value)
    ⟨⟨RhometaReducesStar.step hstep hstar.some⟩, hnf⟩ hsc

theorem evalDrop_certified_image_subset_scObservedOutcomes
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload : Atom} :
    {obs | ∃ value,
        CertifiedPayloadResult space dispatch payload value ∧
        obs =
          (({value} : Multiset Atom),
            ((), (1 : Multiplicative (Multiset Empty))))} ⊆
      RhometaSCObservedOutcomes space dispatch (evalDropSource chan payload) := by
  rintro obs ⟨value, hcert, rfl⟩
  exact evalDrop_certified_value_scObservedOutcome
    (space := space) (dispatch := dispatch)
    (chan := chan) (payload := payload) hcert

theorem evalDrop_certified_scObserved_image_eq_certified_image
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload : Atom} :
    {obs |
      obs ∈ RhometaSCObservedOutcomes space dispatch (evalDropSource chan payload) ∧
      ∃ value,
        CertifiedPayloadResult space dispatch payload value ∧
        obs =
          (({value} : Multiset Atom),
            ((), (1 : Multiplicative (Multiset Empty))))} =
    {obs | ∃ value,
        CertifiedPayloadResult space dispatch payload value ∧
        obs =
          (({value} : Multiset Atom),
            ((), (1 : Multiplicative (Multiset Empty))))} := by
  ext obs
  constructor
  · intro hobs
    exact hobs.2
  · rintro ⟨value, hcert, rfl⟩
    exact ⟨evalDrop_certified_value_scObservedOutcome
      (space := space) (dispatch := dispatch)
      (chan := chan) (payload := payload) hcert, value, hcert, rfl⟩

theorem evalDrop_certified_scObserved_image_mem_iff
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload : Atom}
    {obs : Multiset Atom × (Unit × Multiplicative (Multiset Empty))} :
    (obs ∈ RhometaSCObservedOutcomes space dispatch (evalDropSource chan payload) ∧
      ∃ value,
        CertifiedPayloadResult space dispatch payload value ∧
        obs =
          (({value} : Multiset Atom),
            ((), (1 : Multiplicative (Multiset Empty))))) ↔
    ∃ value,
      CertifiedPayloadResult space dispatch payload value ∧
      obs =
        (({value} : Multiset Atom),
          ((), (1 : Multiplicative (Multiset Empty)))) := by
  have hset := evalDrop_certified_scObserved_image_eq_certified_image
    (space := space) (dispatch := dispatch)
    (chan := chan) (payload := payload)
  exact Set.ext_iff.mp hset obs

private theorem dropShellLike_certified_value_scObservedOutcome
    {space : Space} {dispatch : GroundedDispatch}
    {chan p : Pattern} {payload value : Atom}
    (hshape : DropShellLike chan payload p)
    (hcert : CertifiedPayloadResult space dispatch payload value) :
    (({value} : Multiset Atom), ((), (1 : Multiplicative (Multiset Empty)))) ∈
      RhometaSCObservedOutcomes space dispatch p := by
  rw [dropShellLike_scObservedOutcomes_eq_evalDropSource
    (space := space) (dispatch := dispatch) hshape]
  exact evalDrop_certified_value_scObservedOutcome
    (space := space) (dispatch := dispatch)
    (chan := chan) (payload := payload) hcert

private theorem dropShellLike_certified_image_subset_scObservedOutcomes
    {space : Space} {dispatch : GroundedDispatch}
    {chan p : Pattern} {payload : Atom}
    (hshape : DropShellLike chan payload p) :
    {obs | ∃ value,
        CertifiedPayloadResult space dispatch payload value ∧
        obs =
          (({value} : Multiset Atom),
            ((), (1 : Multiplicative (Multiset Empty))))} ⊆
      RhometaSCObservedOutcomes space dispatch p := by
  rintro obs ⟨value, hcert, rfl⟩
  exact dropShellLike_certified_value_scObservedOutcome
    (space := space) (dispatch := dispatch)
    (chan := chan) hshape hcert

private theorem dropShellLike_certified_scObserved_image_eq_certified_image
    {space : Space} {dispatch : GroundedDispatch}
    {chan p : Pattern} {payload : Atom}
    (hshape : DropShellLike chan payload p) :
    {obs |
      obs ∈ RhometaSCObservedOutcomes space dispatch p ∧
      ∃ value,
        CertifiedPayloadResult space dispatch payload value ∧
        obs =
          (({value} : Multiset Atom),
            ((), (1 : Multiplicative (Multiset Empty))))} =
    {obs | ∃ value,
        CertifiedPayloadResult space dispatch payload value ∧
        obs =
          (({value} : Multiset Atom),
            ((), (1 : Multiplicative (Multiset Empty))))} := by
  rw [dropShellLike_scObservedOutcomes_eq_evalDropSource
    (space := space) (dispatch := dispatch) hshape]
  exact evalDrop_certified_scObserved_image_eq_certified_image
    (space := space) (dispatch := dispatch)
    (chan := chan) (payload := payload)

private theorem dropShellLike_certified_scObserved_image_mem_iff
    {space : Space} {dispatch : GroundedDispatch}
    {chan p : Pattern} {payload : Atom}
    (hshape : DropShellLike chan payload p)
    {obs : Multiset Atom × (Unit × Multiplicative (Multiset Empty))} :
    (obs ∈ RhometaSCObservedOutcomes space dispatch p ∧
      ∃ value,
        CertifiedPayloadResult space dispatch payload value ∧
        obs =
          (({value} : Multiset Atom),
            ((), (1 : Multiplicative (Multiset Empty))))) ↔
    ∃ value,
      CertifiedPayloadResult space dispatch payload value ∧
      obs =
        (({value} : Multiset Atom),
          ((), (1 : Multiplicative (Multiset Empty)))) := by
  have hset := dropShellLike_certified_scObserved_image_eq_certified_image
    (space := space) (dispatch := dispatch)
    (chan := chan) (payload := payload) hshape
  exact Set.ext_iff.mp hset obs

theorem evalDrop_preserves_all_certified_results
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload v₁ v₂ : Atom}
    (h₁ : CertifiedPayloadResult space dispatch payload v₁)
    (h₂ : CertifiedPayloadResult space dispatch payload v₂) :
    evalDropResidual v₁ ∈ MayReachable space dispatch (evalDropSource chan payload) ∧
    evalDropResidual v₂ ∈ MayReachable space dispatch (evalDropSource chan payload) := by
  exact ⟨evalDrop_certified_value_mayReachable
            (space := space) (dispatch := dispatch)
            (chan := chan) (payload := payload) (value := v₁) h₁,
         evalDrop_certified_value_mayReachable
            (space := space) (dispatch := dispatch)
            (chan := chan) (payload := payload) (value := v₂) h₂⟩

theorem evalDrop_preserves_all_certified_outcomes
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload v₁ v₂ : Atom}
    (h₁ : CertifiedPayloadResult space dispatch payload v₁)
    (h₂ : CertifiedPayloadResult space dispatch payload v₂) :
    evalDropResidual v₁ ∈ RhometaOutcomes space dispatch (evalDropSource chan payload) ∧
    evalDropResidual v₂ ∈ RhometaOutcomes space dispatch (evalDropSource chan payload) := by
  exact ⟨evalDrop_certified_value_outcome
            (space := space) (dispatch := dispatch)
            (chan := chan) (payload := payload) (value := v₁) h₁,
         evalDrop_certified_value_outcome
            (space := space) (dispatch := dispatch)
            (chan := chan) (payload := payload) (value := v₂) h₂⟩

theorem evalDropResidual_injective :
    Function.Injective (fun a : Atom => evalDropResidual a) := by
  intro a b h
  have hsingle :
      [semanticNormalizeProc (wrappedValue a)] =
      [semanticNormalizeProc (wrappedValue b)] := by
    injection h with hsingle
  have hnorm : semanticNormalizeProc (wrappedValue a) =
      semanticNormalizeProc (wrappedValue b) := List.cons.inj hsingle |>.1
  have hw : wrappedValue a = wrappedValue b := by
    simpa [semanticNormalizeProc_wrappedValue] using hnorm
  exact wrappedValue_injective hw

theorem scObservedSingleton_value_injective :
    Function.Injective (fun value : Atom =>
      (({value} : Multiset Atom),
        ((), (1 : Multiplicative (Multiset Empty))))) := by
  intro value₁ value₂ h
  have hms : ({value₁} : Multiset Atom) = ({value₂} : Multiset Atom) := by
    exact congrArg Prod.fst h
  have hperm : [value₁].Perm [value₂] := by
    exact Multiset.coe_eq_coe.mp hms
  simpa using hperm

private theorem scReifiedOutcomeOf_singleton_value_unique
    {p : Pattern} {value value' : Atom}
    (h :
      scReifiedOutcomeOf? p =
        some (({value} : Multiset Atom), ((), (1 : Multiplicative (Multiset Empty)))))
    (h' :
      scReifiedOutcomeOf? p =
        some (({value'} : Multiset Atom), ((), (1 : Multiplicative (Multiset Empty))))) :
    value = value' := by
  have hobs :
      (({value} : Multiset Atom), ((), (1 : Multiplicative (Multiset Empty)))) =
        (({value'} : Multiset Atom), ((), (1 : Multiplicative (Multiset Empty)))) := by
    exact Option.some.inj (h.symm.trans h')
  exact scObservedSingleton_value_injective hobs

private theorem scResidualResultMultiset_eq_singleton_of_scReifiedOutcomeOf_eq
    {p : Pattern} {value : Atom}
    (h :
      scReifiedOutcomeOf? p =
        some (({value} : Multiset Atom), ((), (1 : Multiplicative (Multiset Empty))))) :
    scResidualResultMultiset? p = some ({value} : Multiset Atom) := by
  unfold scReifiedOutcomeOf? at h
  cases hres : scResidualResultMultiset? p with
  | none =>
      simp [hres] at h
  | some rs =>
      have hobs :
          (rs, ((), (1 : Multiplicative (Multiset Empty)))) =
            (({value} : Multiset Atom),
              ((), (1 : Multiplicative (Multiset Empty)))) := by
        simpa [hres] using h
      have hrs : rs = ({value} : Multiset Atom) := congrArg Prod.fst hobs
      simp [hrs]

private theorem obs_eq_of_scResidualResultMultiset_eq_singleton
    {p : Pattern} {value : Atom}
    {obs : Multiset Atom × (Unit × Multiplicative (Multiset Empty))}
    (hres : scResidualResultMultiset? p = some ({value} : Multiset Atom))
    (hdecode : scReifiedOutcomeOf? p = some obs) :
    obs =
      (({value} : Multiset Atom),
        ((), (1 : Multiplicative (Multiset Empty)))) := by
  unfold scReifiedOutcomeOf? at hdecode
  simpa [hres] using hdecode.symm

private theorem value_eq_of_structuralResidual_decode_of_multiset_unique
    {value value' : Atom} {r : Pattern}
    (huniq : ∀ {s : Pattern} {rs : Multiset Atom},
      StructuralCongruence s (evalDropResidual value') →
      scResidualResultMultiset? s = some rs →
      rs = ({value'} : Multiset Atom))
    (hsc : StructuralCongruence r (evalDropResidual value'))
    (hdecode :
      scReifiedOutcomeOf? r =
        some (({value} : Multiset Atom),
          ((), (1 : Multiplicative (Multiset Empty))))) :
    value = value' := by
  have hres :
      scResidualResultMultiset? r = some ({value} : Multiset Atom) :=
    scResidualResultMultiset_eq_singleton_of_scReifiedOutcomeOf_eq hdecode
  have hrs : ({value} : Multiset Atom) = ({value'} : Multiset Atom) := by
    simpa [hres] using huniq hsc hres
  have hobs :
      (({value} : Multiset Atom),
          ((), (1 : Multiplicative (Multiset Empty)))) =
        (({value'} : Multiset Atom),
          ((), (1 : Multiplicative (Multiset Empty)))) := by
    simpa using congrArg
      (fun rs : Multiset Atom =>
        (rs, ((), (1 : Multiplicative (Multiset Empty))))) hrs
  exact scObservedSingleton_value_injective hobs

theorem scObservedCarrier_collapses_singleton_wrapper
    (value : Atom) :
    scReifiedOutcomeOf? (.collection .hashBag [evalDropResidual value] none) =
      scReifiedOutcomeOf? (evalDropResidual value) := by
  exact scReifiedOutcomeOf_par_singleton (evalDropResidual value)

theorem scObservedCarrier_collapses_wrappedValue
    (value : Atom) :
    scReifiedOutcomeOf? (wrappedValue value) =
      scReifiedOutcomeOf? (evalDropResidual value) :=
  scReifiedOutcomeOf_wrappedValue_eq_evalDropResidual value

theorem scObservedCarrier_recovers_evalDropResidual_value
    {value value' : Atom}
    (h :
      scReifiedOutcomeOf? (evalDropResidual value') =
        some (({value} : Multiset Atom), ((), (1 : Multiplicative (Multiset Empty))))) :
    value = value' := by
  simpa [scReifiedOutcomeOf?_evalDropResidual] using h.symm

theorem scObservedCarrier_recovers_wrappedValue_value
    {value value' : Atom}
    (h :
      scReifiedOutcomeOf? (wrappedValue value') =
        some (({value} : Multiset Atom), ((), (1 : Multiplicative (Multiset Empty))))) :
    value = value' := by
  rw [scReifiedOutcomeOf_wrappedValue_eq_evalDropResidual] at h
  exact scObservedCarrier_recovers_evalDropResidual_value h

mutual

private def WrappedValuePayload (value : Atom) : Pattern → Prop
  | .bvar _ => True
  | .fvar _ => True
  | .apply "rho:val" [q] => StructuralCongruence q (atomToPattern value)
  | .apply _ args => WrappedValuePayloadList value args
  | .lambda _ body => WrappedValuePayload value body
  | .multiLambda _ _ body => WrappedValuePayload value body
  | .subst body repl => WrappedValuePayload value body ∧ WrappedValuePayload value repl
  | .collection _ elems _ => WrappedValuePayloadList value elems

private def WrappedValuePayloadList (value : Atom) : List Pattern → Prop
  | [] => True
  | p :: ps => WrappedValuePayload value p ∧ WrappedValuePayloadList value ps

end

private theorem wrappedValuePayloadList_filter_nonzero
    {value : Atom} {ps : List Pattern}
    (hps : WrappedValuePayloadList value ps) :
    WrappedValuePayloadList value
      (ps.filter (fun e => e ≠ .apply "PZero" [])) := by
  induction ps with
  | nil =>
      simp [WrappedValuePayloadList]
  | cons p ps ih =>
      by_cases hpzero : p = .apply "PZero" []
      · simpa [hpzero, WrappedValuePayloadList] using ih hps.2
      · simpa [hpzero, WrappedValuePayloadList, hps.1] using ih hps.2

private theorem wrappedValuePayloadList_iff_of_pointwise
    {value : Atom} {ps qs : List Pattern}
    (hlen : ps.length = qs.length)
    (hpoint : ∀ i (h₁ : i < ps.length) (h₂ : i < qs.length),
      WrappedValuePayload value (ps.get ⟨i, h₁⟩) ↔
        WrappedValuePayload value (qs.get ⟨i, h₂⟩)) :
    WrappedValuePayloadList value ps ↔ WrappedValuePayloadList value qs := by
  induction ps generalizing qs with
  | nil =>
      cases qs with
      | nil => simp [WrappedValuePayloadList]
      | cons q qs =>
          simp at hlen
  | cons p ps ih =>
      cases qs with
      | nil =>
          simp at hlen
      | cons q qs =>
          have hpq : WrappedValuePayload value p ↔ WrappedValuePayload value q :=
            hpoint 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
          have hrest : WrappedValuePayloadList value ps ↔
              WrappedValuePayloadList value qs := by
            apply ih
            · simpa using Nat.succ.inj hlen
            · intro i h₁ h₂
              simpa using hpoint (i + 1) (Nat.succ_lt_succ h₁) (Nat.succ_lt_succ h₂)
          constructor <;> intro h
          · exact ⟨hpq.mp h.1, hrest.mp h.2⟩
          · exact ⟨hpq.mpr h.1, hrest.mpr h.2⟩

private theorem wrappedValuePayloadList_iff_of_perm
    {value : Atom} {ps qs : List Pattern} (hperm : ps.Perm qs) :
    WrappedValuePayloadList value ps ↔ WrappedValuePayloadList value qs := by
  induction hperm with
  | nil =>
      simp [WrappedValuePayloadList]
  | @cons p ps qs hperm ih =>
      simp [WrappedValuePayloadList, ih]
  | swap p q ps =>
      simp [WrappedValuePayloadList, and_left_comm]
  | trans _ _ ih₁ ih₂ =>
      exact ih₁.trans ih₂

private theorem wrappedValuePayloadList_append_iff
    {value : Atom} {ps qs : List Pattern} :
    WrappedValuePayloadList value (ps ++ qs) ↔
      WrappedValuePayloadList value ps ∧ WrappedValuePayloadList value qs := by
  induction ps with
  | nil =>
      simp [WrappedValuePayloadList]
  | cons p ps ih =>
      simp [WrappedValuePayloadList, ih, and_assoc]

private theorem wrappedValuePayload_iff_of_structuralCongruence
    {value : Atom} {p q : Pattern} (hsc : StructuralCongruence p q) :
    WrappedValuePayload value p ↔ WrappedValuePayload value q := by
  induction hsc with
  | alpha _ _ h =>
      subst h
      rfl
  | refl _ =>
      rfl
  | symm _ _ _ ih =>
      exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ =>
      exact ih₁.trans ih₂
  | par_singleton p =>
      simp [WrappedValuePayload, WrappedValuePayloadList]
  | par_nil_left p =>
      simp [WrappedValuePayload, WrappedValuePayloadList]
  | par_nil_right p =>
      simp [WrappedValuePayload, WrappedValuePayloadList]
  | par_comm p q =>
      simp [WrappedValuePayload, WrappedValuePayloadList, and_comm]
  | par_assoc p q r =>
      simp [WrappedValuePayload, WrappedValuePayloadList, and_assoc, and_comm]
  | par_cong ps qs hlen _ ih =>
      simpa [WrappedValuePayload] using wrappedValuePayloadList_iff_of_pointwise
        (value := value) hlen ih
  | par_flatten ps qs =>
      simp [WrappedValuePayload, WrappedValuePayloadList, wrappedValuePayloadList_append_iff]
  | par_perm ps qs hperm =>
      simpa [WrappedValuePayload] using wrappedValuePayloadList_iff_of_perm
        (value := value) hperm
  | set_perm ps qs hperm =>
      simpa [WrappedValuePayload] using wrappedValuePayloadList_iff_of_perm
        (value := value) hperm
  | set_cong ps qs hlen _ ih =>
      simpa [WrappedValuePayload] using wrappedValuePayloadList_iff_of_pointwise
        (value := value) hlen ih
  | lambda_cong _ _ _ _ ih =>
      simpa [WrappedValuePayload] using ih
  | apply_cong f args₁ args₂ hlen hpt ih =>
      by_cases hf : f = "rho:val"
      · subst hf
        cases args₁ with
        | nil =>
            cases args₂ with
            | nil =>
                simp [WrappedValuePayload, WrappedValuePayloadList]
            | cons b bs =>
                simp at hlen
        | cons a as =>
            cases as with
            | nil =>
                cases args₂ with
                | nil =>
                    simp at hlen
                | cons b bs =>
                    cases bs with
                    | nil =>
                        have hab : StructuralCongruence a b := by
                          simpa using hpt 0 (by simp) (by simp)
                        simpa [WrappedValuePayload] using
                          (structuralCongruence_to_fixed_iff
                            (r := atomToPattern value) hab)
                    | cons c cs =>
                        simp at hlen
            | cons a' as' =>
                cases args₂ with
                | nil =>
                    simp at hlen
                | cons b bs =>
                    cases bs with
                    | nil =>
                        simp at hlen
                    | cons b' bs' =>
                        simpa [WrappedValuePayload] using
                          wrappedValuePayloadList_iff_of_pointwise
                            (value := value) hlen ih
      · simpa [WrappedValuePayload, hf] using
          wrappedValuePayloadList_iff_of_pointwise
            (value := value) hlen ih
  | collection_general_cong ct ps qs g hlen _ ih =>
      simpa [WrappedValuePayload] using wrappedValuePayloadList_iff_of_pointwise
        (value := value) hlen ih
  | multiLambda_cong _ _ _ _ _ ih =>
      simpa [WrappedValuePayload] using ih
  | subst_cong _ _ _ _ _ _ ih₁ ih₂ =>
      simp [WrappedValuePayload, ih₁, ih₂]
  | quote_drop n =>
      simp [WrappedValuePayload, WrappedValuePayloadList]

private theorem wrappedValuePayload_wrappedValue (value : Atom) :
    WrappedValuePayload value (wrappedValue value) := by
  simpa [WrappedValuePayload, wrappedValue] using
    (StructuralCongruence.refl (atomToPattern value))

private theorem wrappedValuePayload_evalDropResidual (value : Atom) :
    WrappedValuePayload value (evalDropResidual value) := by
  simpa [evalDropResidual, semanticNormalizeProc_wrappedValue,
    WrappedValuePayload, WrappedValuePayloadList] using
    wrappedValuePayload_wrappedValue value

private structure DropResidualLike
    (value : Atom) (p : Pattern) : Prop where
  residual_sc : StructuralCongruence p (evalDropResidual value)

private theorem dropResidualLike_of_residual_structuralCongruence
    {value : Atom} {p : Pattern}
    (hsc : StructuralCongruence p (evalDropResidual value)) :
    DropResidualLike value p :=
  ⟨hsc⟩

private theorem dropResidualLike_iff_residual_structuralCongruence
    {value : Atom} {p : Pattern} :
    DropResidualLike value p ↔
      StructuralCongruence p (evalDropResidual value) := by
  constructor
  · exact DropResidualLike.residual_sc
  · exact dropResidualLike_of_residual_structuralCongruence

private theorem dropResidualLike_evalDropResidual (value : Atom) :
    DropResidualLike value (evalDropResidual value) :=
  ⟨StructuralCongruence.refl _⟩

private theorem dropResidualLike_wrappedValue (value : Atom) :
    DropResidualLike value (wrappedValue value) := by
  refine ⟨?_⟩
  exact StructuralCongruence.trans _ _ _
    (StructuralCongruence.symm _ _
      (StructuralCongruence.par_singleton (wrappedValue value)))
    (by
      simpa [evalDropResidual, semanticNormalizeProc_wrappedValue] using
        (StructuralCongruence.refl
          (.collection .hashBag [wrappedValue value] none)))

private theorem wrappedValuePayload_of_dropResidualLike
    {value : Atom} {p : Pattern}
    (hshape : DropResidualLike value p) :
    WrappedValuePayload value p :=
  (wrappedValuePayload_iff_of_structuralCongruence
    hshape.residual_sc).mpr
    (wrappedValuePayload_evalDropResidual value)

private theorem wrappedValuePayload_of_structuralResidual
    {value : Atom} {p : Pattern}
    (hsc : StructuralCongruence p (evalDropResidual value)) :
    WrappedValuePayload value p :=
  wrappedValuePayload_of_dropResidualLike ⟨hsc⟩

private theorem wrappedValuePayload_of_evalDropResidual_structural
    {value : Atom} {p : Pattern}
    (hsc : StructuralCongruence (evalDropResidual value) p) :
    WrappedValuePayload value p :=
  wrappedValuePayload_of_structuralResidual
    (StructuralCongruence.symm _ _ hsc)

-- B7 ROUTE: carrier faithful; avoid broad decoder/atom SC-invariance.
-- Prove residual-specific value recovery, then the singleton carrier theorem.
private theorem shellWidth_evalDropResidual (value : Atom) :
    shellWidth (evalDropResidual value) = 1 := by
  rw [evalDropResidual, semanticNormalizeProc_wrappedValue]
  simp [shellWidth, wrappedValue]

private theorem shellWidth_of_dropResidualLike
    {value : Atom} {p : Pattern}
    (hshape : DropResidualLike value p) :
    shellWidth p = 1 := by
  rw [shellWidth_SC hshape.residual_sc]
  exact shellWidth_evalDropResidual value

private theorem obs_eq_of_evalDropResidual_decode
    {value : Atom} {obs : Multiset Atom × (Unit × Multiplicative (Multiset Empty))}
    (hdecode : scReifiedOutcomeOf? (evalDropResidual value) = some obs) :
    obs =
      (({value} : Multiset Atom),
        ((), (1 : Multiplicative (Multiset Empty)))) := by
  simpa [scReifiedOutcomeOf?_evalDropResidual] using hdecode.symm

private theorem obs_eq_of_strip_evalDropResidual_decode
    {value : Atom} {p : Pattern}
    {obs : Multiset Atom × (Unit × Multiplicative (Multiset Empty))}
    (hstrip : stripSCWrappers p = evalDropResidual value)
    (hdecode : scReifiedOutcomeOf? p = some obs) :
    obs =
      (({value} : Multiset Atom),
        ((), (1 : Multiplicative (Multiset Empty)))) := by
  simpa [scReifiedOutcomeOf?, scResidualResultMultiset?, hstrip,
    evalDropResidual, semanticNormalizeProc_wrappedValue,
    decodeWrappedValues?, decodeWrappedValue?_wrappedValue] using hdecode.symm

private theorem value_eq_of_strip_evalDropResidual_decode
    {value value' : Atom} {p : Pattern}
    (hstrip : stripSCWrappers p = evalDropResidual value')
    (hdecode :
      scReifiedOutcomeOf? p =
        some (({value} : Multiset Atom),
          ((), (1 : Multiplicative (Multiset Empty))))) :
    value = value' := by
  have hobs :=
    obs_eq_of_strip_evalDropResidual_decode
      (value := value') (p := p) hstrip hdecode
  exact scObservedSingleton_value_injective hobs

private theorem obs_eq_of_wrappedValue_decode
    {value : Atom} {obs : Multiset Atom × (Unit × Multiplicative (Multiset Empty))}
    (hdecode : scReifiedOutcomeOf? (wrappedValue value) = some obs) :
    obs =
      (({value} : Multiset Atom),
        ((), (1 : Multiplicative (Multiset Empty)))) := by
  rw [scReifiedOutcomeOf_wrappedValue_eq_evalDropResidual] at hdecode
  exact obs_eq_of_evalDropResidual_decode hdecode

private theorem value_eq_of_evalDropResidual_par_singleton_decode
    {value value' : Atom} {p : Pattern}
    (hdecode :
      scReifiedOutcomeOf? (.collection .hashBag [p] none) =
        some (({value} : Multiset Atom), ((), (1 : Multiplicative (Multiset Empty)))))
    (htarget : evalDropResidual value' = p) :
    value = value' := by
  rw [scReifiedOutcomeOf_par_singleton] at hdecode
  rw [← htarget] at hdecode
  exact scObservedCarrier_recovers_evalDropResidual_value hdecode

private theorem obs_eq_of_evalDropResidual_par_singleton_decode
    {value : Atom} {obs : Multiset Atom × (Unit × Multiplicative (Multiset Empty))}
    {p : Pattern}
    (hdecode :
      scReifiedOutcomeOf? (.collection .hashBag [p] none) = some obs)
    (htarget : evalDropResidual value = p) :
    obs =
      (({value} : Multiset Atom),
        ((), (1 : Multiplicative (Multiset Empty)))) := by
  rw [scReifiedOutcomeOf_par_singleton] at hdecode
  rw [← htarget] at hdecode
  simpa [scReifiedOutcomeOf?_evalDropResidual] using hdecode.symm

private theorem value_eq_of_evalDropResidual_par_nil_left_decode
    {value value' : Atom} {p : Pattern}
    (hdecode :
      scReifiedOutcomeOf? (.collection .hashBag [.apply "PZero" [], p] none) =
        some (({value} : Multiset Atom), ((), (1 : Multiplicative (Multiset Empty)))))
    (htarget : evalDropResidual value' = p) :
    value = value' := by
  rw [scReifiedOutcomeOf_par_nil_left] at hdecode
  rw [← htarget] at hdecode
  exact scObservedCarrier_recovers_evalDropResidual_value hdecode

private theorem obs_eq_of_evalDropResidual_par_nil_left_decode
    {value : Atom} {obs : Multiset Atom × (Unit × Multiplicative (Multiset Empty))}
    {p : Pattern}
    (hdecode :
      scReifiedOutcomeOf? (.collection .hashBag [.apply "PZero" [], p] none) =
        some obs)
    (htarget : evalDropResidual value = p) :
    obs =
      (({value} : Multiset Atom),
        ((), (1 : Multiplicative (Multiset Empty)))) := by
  rw [scReifiedOutcomeOf_par_nil_left] at hdecode
  rw [← htarget] at hdecode
  simpa [scReifiedOutcomeOf?_evalDropResidual] using hdecode.symm

private theorem value_eq_of_evalDropResidual_par_nil_right_decode
    {value value' : Atom} {p : Pattern}
    (hdecode :
      scReifiedOutcomeOf? (.collection .hashBag [p, .apply "PZero" []] none) =
        some (({value} : Multiset Atom), ((), (1 : Multiplicative (Multiset Empty)))))
    (htarget : evalDropResidual value' = p) :
    value = value' := by
  rw [scReifiedOutcomeOf_par_nil_right] at hdecode
  rw [← htarget] at hdecode
  exact scObservedCarrier_recovers_evalDropResidual_value hdecode

private theorem obs_eq_of_evalDropResidual_par_nil_right_decode
    {value : Atom} {obs : Multiset Atom × (Unit × Multiplicative (Multiset Empty))}
    {p : Pattern}
    (hdecode :
      scReifiedOutcomeOf? (.collection .hashBag [p, .apply "PZero" []] none) =
        some obs)
    (htarget : evalDropResidual value = p) :
    obs =
      (({value} : Multiset Atom),
        ((), (1 : Multiplicative (Multiset Empty)))) := by
  rw [scReifiedOutcomeOf_par_nil_right] at hdecode
  rw [← htarget] at hdecode
  simpa [scReifiedOutcomeOf?_evalDropResidual] using hdecode.symm

private theorem value_eq_of_evalDropResidual_par_comm_decode
    {value value' : Atom} {p q : Pattern}
    (hdecode :
      scReifiedOutcomeOf? (.collection .hashBag [p, q] none) =
        some (({value} : Multiset Atom), ((), (1 : Multiplicative (Multiset Empty)))))
    (htarget : evalDropResidual value' = .collection .hashBag [q, p] none) :
    value = value' := by
  rw [scReifiedOutcomeOf_par_comm] at hdecode
  rw [← htarget] at hdecode
  exact scObservedCarrier_recovers_evalDropResidual_value hdecode

private theorem obs_eq_of_evalDropResidual_par_comm_decode
    {value : Atom} {obs : Multiset Atom × (Unit × Multiplicative (Multiset Empty))}
    {p q : Pattern}
    (hdecode :
      scReifiedOutcomeOf? (.collection .hashBag [p, q] none) = some obs)
    (htarget : evalDropResidual value = .collection .hashBag [q, p] none) :
    obs =
      (({value} : Multiset Atom),
        ((), (1 : Multiplicative (Multiset Empty)))) := by
  rw [scReifiedOutcomeOf_par_comm] at hdecode
  rw [← htarget] at hdecode
  simpa [scReifiedOutcomeOf?_evalDropResidual] using hdecode.symm

private theorem value_eq_of_evalDropResidual_par_assoc_decode
    {value value' : Atom} {p q r : Pattern}
    (hdecode :
      scReifiedOutcomeOf?
        (.collection .hashBag [.collection .hashBag [p, q] none, r] none) =
        some (({value} : Multiset Atom), ((), (1 : Multiplicative (Multiset Empty)))))
    (htarget :
      evalDropResidual value' =
        .collection .hashBag [p, .collection .hashBag [q, r] none] none) :
    value = value' := by
  rw [scReifiedOutcomeOf_par_assoc] at hdecode
  rw [← htarget] at hdecode
  exact scObservedCarrier_recovers_evalDropResidual_value hdecode

private theorem obs_eq_of_evalDropResidual_par_assoc_decode
    {value : Atom} {obs : Multiset Atom × (Unit × Multiplicative (Multiset Empty))}
    {p q r : Pattern}
    (hdecode :
      scReifiedOutcomeOf?
        (.collection .hashBag [.collection .hashBag [p, q] none, r] none) =
        some obs)
    (htarget :
      evalDropResidual value =
        .collection .hashBag [p, .collection .hashBag [q, r] none] none) :
    obs =
      (({value} : Multiset Atom),
        ((), (1 : Multiplicative (Multiset Empty)))) := by
  rw [scReifiedOutcomeOf_par_assoc] at hdecode
  rw [← htarget] at hdecode
  simpa [scReifiedOutcomeOf?_evalDropResidual] using hdecode.symm

private theorem value_eq_of_evalDropResidual_quoteDrop_decode
    {value value' : Atom} {p : Pattern}
    (hdecode :
      scReifiedOutcomeOf? (.apply "NQuote" [.apply "PDrop" [p]]) =
        some (({value} : Multiset Atom), ((), (1 : Multiplicative (Multiset Empty)))))
    (htarget : evalDropResidual value' = p) :
    value = value' := by
  rw [scReifiedOutcomeOf_quoteDrop_general] at hdecode
  rw [← htarget] at hdecode
  exact scObservedCarrier_recovers_evalDropResidual_value hdecode

private theorem obs_eq_of_evalDropResidual_quoteDrop_decode
    {value : Atom} {obs : Multiset Atom × (Unit × Multiplicative (Multiset Empty))}
    {p : Pattern}
    (hdecode :
      scReifiedOutcomeOf? (.apply "NQuote" [.apply "PDrop" [p]]) =
        some obs)
    (htarget : evalDropResidual value = p) :
    obs =
      (({value} : Multiset Atom),
        ((), (1 : Multiplicative (Multiset Empty)))) := by
  rw [scReifiedOutcomeOf_quoteDrop_general] at hdecode
  rw [← htarget] at hdecode
  simpa [scReifiedOutcomeOf?_evalDropResidual] using hdecode.symm

private theorem obs_eq_of_strip_wrappedValue_decode
    {value : Atom} {p : Pattern}
    {obs : Multiset Atom × (Unit × Multiplicative (Multiset Empty))}
    (hstrip : stripSCWrappers p = wrappedValue value)
    (hdecode : scReifiedOutcomeOf? p = some obs) :
    obs =
      (({value} : Multiset Atom),
        ((), (1 : Multiplicative (Multiset Empty)))) := by
  simpa [scReifiedOutcomeOf?, scResidualResultMultiset?, hstrip,
    scDecodeWrappedValue?, stripSCWrappers, stripSCWrappersList,
    stripSCWrappers_atomToPattern, wrappedValue,
    patternToAtom_atomToPattern] using hdecode.symm

private theorem value_eq_of_strip_wrappedValue_decode
    {value value' : Atom} {p : Pattern}
    (hstrip : stripSCWrappers p = wrappedValue value')
    (hdecode :
      scReifiedOutcomeOf? p =
        some (({value} : Multiset Atom),
          ((), (1 : Multiplicative (Multiset Empty))))) :
    value = value' := by
  have hobs :=
    obs_eq_of_strip_wrappedValue_decode
      (value := value') (p := p) hstrip hdecode
  exact scObservedSingleton_value_injective hobs

private theorem scResidualResultMultiset_eq_singleton_of_strip_wrappedValue
    {value : Atom} {p : Pattern} {rs : Multiset Atom}
    (hstrip : stripSCWrappers p = wrappedValue value)
    (hdecode : scResidualResultMultiset? p = some rs) :
    rs = ({value} : Multiset Atom) := by
  unfold scResidualResultMultiset? at hdecode
  rw [hstrip] at hdecode
  change (scDecodeWrappedValue? (wrappedValue value)).map
      (fun value => ({value} : Multiset Atom)) = some rs at hdecode
  simp [scDecodeWrappedValue?_wrappedValue] at hdecode
  exact hdecode.symm

private theorem obs_eq_of_strip_hashBag_singleton_wrapped_decode
    {value : Atom} {p : Pattern} {elems : List Pattern}
    {obs : Multiset Atom × (Unit × Multiplicative (Multiset Empty))}
    (hstrip : stripSCWrappers p = .collection .hashBag elems none)
    (helems : elems = [wrappedValue value])
    (hdecode : scReifiedOutcomeOf? p = some obs) :
    obs =
      (({value} : Multiset Atom),
        ((), (1 : Multiplicative (Multiset Empty)))) := by
  subst helems
  simpa [scReifiedOutcomeOf?, scResidualResultMultiset?, hstrip,
    decodeWrappedValues?, decodeWrappedValue?_wrappedValue] using hdecode.symm

private theorem value_eq_of_strip_hashBag_singleton_wrapped_decode
    {value value' : Atom} {p : Pattern} {elems : List Pattern}
    (hstrip : stripSCWrappers p = .collection .hashBag elems none)
    (helems : elems = [wrappedValue value'])
    (hdecode :
      scReifiedOutcomeOf? p =
        some (({value} : Multiset Atom),
          ((), (1 : Multiplicative (Multiset Empty))))) :
    value = value' := by
  have hobs :=
    obs_eq_of_strip_hashBag_singleton_wrapped_decode
      (value := value') (p := p) hstrip helems hdecode
  exact scObservedSingleton_value_injective hobs

private theorem dropResidualLike_of_structuralCongruence
    {value : Atom} {p q : Pattern}
    (hsc : StructuralCongruence p q)
    (hshape : DropResidualLike value p) :
    DropResidualLike value q :=
  ⟨StructuralCongruence.trans _ _ _
    (StructuralCongruence.symm _ _ hsc) hshape.residual_sc⟩

private theorem dropResidualLike_of_hashBag_singleton
    {value : Atom} {p : Pattern}
    (hshape : DropResidualLike value
      (.collection .hashBag [p] none)) :
    DropResidualLike value p :=
  dropResidualLike_of_structuralCongruence
    (StructuralCongruence.par_singleton p) hshape

private theorem dropResidualLike_of_hashBag_nil_left
    {value : Atom} {p : Pattern}
    (hshape : DropResidualLike value
      (.collection .hashBag [.apply "PZero" [], p] none)) :
    DropResidualLike value p :=
  dropResidualLike_of_structuralCongruence
    (StructuralCongruence.par_nil_left p) hshape

private theorem dropResidualLike_of_hashBag_nil_right
    {value : Atom} {p : Pattern}
    (hshape : DropResidualLike value
      (.collection .hashBag [p, .apply "PZero" []] none)) :
    DropResidualLike value p :=
  dropResidualLike_of_structuralCongruence
    (StructuralCongruence.par_nil_right p) hshape

private theorem dropResidualLike_of_quoteDrop
    {value : Atom} {p : Pattern}
    (hshape : DropResidualLike value
      (.apply "NQuote" [.apply "PDrop" [p]])) :
    DropResidualLike value p :=
  dropResidualLike_of_structuralCongruence
    (StructuralCongruence.quote_drop p) hshape

private theorem dropResidualLike_of_hashBag_perm
    {value : Atom} {elems₁ elems₂ : List Pattern}
    (hperm : elems₁.Perm elems₂)
    (hshape : DropResidualLike value
      (.collection .hashBag elems₁ none)) :
    DropResidualLike value (.collection .hashBag elems₂ none) :=
  dropResidualLike_of_structuralCongruence
    (StructuralCongruence.par_perm elems₁ elems₂ hperm) hshape

private theorem dropResidualLike_of_hashBag_flatten
    {value : Atom} {before nested : List Pattern}
    (hshape : DropResidualLike value
      (.collection .hashBag (before ++ [.collection .hashBag nested none]) none)) :
    DropResidualLike value
      (.collection .hashBag (before ++ nested) none) :=
  dropResidualLike_of_structuralCongruence
    (StructuralCongruence.par_flatten before nested) hshape

private theorem dropResidualLike_of_hashBag_unflatten
    {value : Atom} {before nested : List Pattern}
    (hshape : DropResidualLike value
      (.collection .hashBag (before ++ nested) none)) :
    DropResidualLike value
      (.collection .hashBag (before ++ [.collection .hashBag nested none]) none) :=
  dropResidualLike_of_structuralCongruence
    (StructuralCongruence.symm _ _
      (StructuralCongruence.par_flatten before nested)) hshape

private theorem dropResidualLike_normalForm
    {space : Space} {dispatch : GroundedDispatch}
    {value : Atom} {p : Pattern}
    (hshape : DropResidualLike value p) :
    RhometaNormalForm space dispatch p :=
  rhometaNormalForm_of_SC_evalDropResidual hshape.residual_sc

private theorem dropResidualLike_outcomes_iff_eq
    {space : Space} {dispatch : GroundedDispatch}
    {value : Atom} {p q : Pattern}
    (hshape : DropResidualLike value p) :
    q ∈ RhometaOutcomes space dispatch p ↔ q = p :=
  mem_rhometaOutcomes_iff_eq_of_normalForm
    (space := space) (dispatch := dispatch)
    (p := p) (q := q)
    (dropResidualLike_normalForm
      (space := space) (dispatch := dispatch) hshape)

private theorem dropResidualLike_scObservedOutcomes_eq_evalDropResidual
    {space : Space} {dispatch : GroundedDispatch}
    {value : Atom} {p : Pattern}
    (hshape : DropResidualLike value p) :
    RhometaSCObservedOutcomes space dispatch p =
      RhometaSCObservedOutcomes space dispatch (evalDropResidual value) :=
  rhometaSCObservedOutcomes_eq_of_source_structuralCongruence
    (space := space) (dispatch := dispatch) hshape.residual_sc

private theorem dropResidualLike_scObservedOutcomes_mem_iff_evalDropResidual
    {space : Space} {dispatch : GroundedDispatch}
    {value : Atom} {p : Pattern}
    (hshape : DropResidualLike value p)
    {obs : Multiset Atom × (Unit × Multiplicative (Multiset Empty))} :
    obs ∈ RhometaSCObservedOutcomes space dispatch p ↔
      obs ∈ RhometaSCObservedOutcomes space dispatch (evalDropResidual value) := by
  rw [dropResidualLike_scObservedOutcomes_eq_evalDropResidual
    (space := space) (dispatch := dispatch) hshape]

private theorem evalDropResidual_value_scObservedOutcome
    {space : Space} {dispatch : GroundedDispatch}
    (value : Atom) :
    (({value} : Multiset Atom), ((), (1 : Multiplicative (Multiset Empty)))) ∈
      RhometaSCObservedOutcomes space dispatch (evalDropResidual value) := by
  refine ⟨evalDropResidual value, evalDropResidual value, ?_,
    StructuralCongruence.refl _, scReifiedOutcomeOf?_evalDropResidual value⟩
  exact ⟨⟨RhometaReducesStar.refl _⟩,
    evalDropResidual_normalForm (space := space) (dispatch := dispatch) value⟩

private theorem dropResidualLike_value_scObservedOutcome
    {space : Space} {dispatch : GroundedDispatch}
    {value : Atom} {p : Pattern}
    (hshape : DropResidualLike value p) :
    (({value} : Multiset Atom), ((), (1 : Multiplicative (Multiset Empty)))) ∈
      RhometaSCObservedOutcomes space dispatch p := by
  rw [dropResidualLike_scObservedOutcomes_eq_evalDropResidual
    (space := space) (dispatch := dispatch) hshape]
  exact evalDropResidual_value_scObservedOutcome
    (space := space) (dispatch := dispatch) value

private theorem evalDropResidual_scObservedOutcomes_eq_singleton_of_residual_unique
    {space : Space} {dispatch : GroundedDispatch}
    {value : Atom}
    (huniq : ∀ {r : Pattern}
      {obs : Multiset Atom × (Unit × Multiplicative (Multiset Empty))},
      StructuralCongruence r (evalDropResidual value) →
      scReifiedOutcomeOf? r = some obs →
      obs =
        (({value} : Multiset Atom),
          ((), (1 : Multiplicative (Multiset Empty))))) :
    RhometaSCObservedOutcomes space dispatch (evalDropResidual value) =
      {((({value} : Multiset Atom),
        ((), (1 : Multiplicative (Multiset Empty)))))} := by
  ext obs
  constructor
  · rintro ⟨q, r, hq, hsc, hdecode⟩
    have hqeq : q = evalDropResidual value :=
      (evalDropResidual_outcomes_iff_eq
        (space := space) (dispatch := dispatch)
        (value := value) (q := q)).mp hq
    subst hqeq
    have hobs := huniq (StructuralCongruence.symm _ _ hsc) hdecode
    simpa [Set.mem_singleton_iff] using hobs
  · intro hobs
    have hobs' :
        obs =
          (({value} : Multiset Atom),
            ((), (1 : Multiplicative (Multiset Empty)))) := by
      simpa [Set.mem_singleton_iff] using hobs
    subst hobs'
    exact evalDropResidual_value_scObservedOutcome
      (space := space) (dispatch := dispatch) value

private theorem evalDropResidual_scObservedOutcomes_eq_singleton_of_multiset_unique
    {space : Space} {dispatch : GroundedDispatch}
    {value : Atom}
    (huniq : ∀ {r : Pattern} {rs : Multiset Atom},
      StructuralCongruence r (evalDropResidual value) →
      scResidualResultMultiset? r = some rs →
      rs = ({value} : Multiset Atom)) :
    RhometaSCObservedOutcomes space dispatch (evalDropResidual value) =
      {((({value} : Multiset Atom),
        ((), (1 : Multiplicative (Multiset Empty)))))} := by
  apply evalDropResidual_scObservedOutcomes_eq_singleton_of_residual_unique
  intro r obs hsc hdecode
  unfold scReifiedOutcomeOf? at hdecode
  cases hres : scResidualResultMultiset? r with
  | none =>
      simp [hres] at hdecode
  | some rs =>
      have hrs : rs = ({value} : Multiset Atom) := huniq hsc hres
      subst hrs
      simpa [hres] using hdecode.symm

theorem rhometta_scObserved_carrier_faithfulness_gate :
    Function.Injective (fun value : Atom =>
      (({value} : Multiset Atom),
        ((), (1 : Multiplicative (Multiset Empty))))) ∧
    (∀ value : Atom,
      scReifiedOutcomeOf? (.collection .hashBag [evalDropResidual value] none) =
        scReifiedOutcomeOf? (evalDropResidual value)) ∧
    (∀ value : Atom,
      scReifiedOutcomeOf? (wrappedValue value) =
        scReifiedOutcomeOf? (evalDropResidual value)) ∧
    (∀ {value value' : Atom},
      scReifiedOutcomeOf? (evalDropResidual value') =
        some (({value} : Multiset Atom), ((), (1 : Multiplicative (Multiset Empty)))) →
      value = value') ∧
    (∀ {value value' : Atom},
      scReifiedOutcomeOf? (wrappedValue value') =
        some (({value} : Multiset Atom), ((), (1 : Multiplicative (Multiset Empty)))) →
      value = value') := by
  exact ⟨scObservedSingleton_value_injective,
    scObservedCarrier_collapses_singleton_wrapper,
    scObservedCarrier_collapses_wrappedValue,
    fun h => scObservedCarrier_recovers_evalDropResidual_value h,
    fun h => scObservedCarrier_recovers_wrappedValue_value h⟩

theorem scObservedCarrier_distinguishes_evalDropResidual_values
    {value₁ value₂ : Atom}
    (hdistinct : value₁ ≠ value₂) :
    scReifiedOutcomeOf? (evalDropResidual value₁) ≠
      scReifiedOutcomeOf? (evalDropResidual value₂) := by
  intro hobs
  have hsingleton :
      (({value₁} : Multiset Atom), ((), (1 : Multiplicative (Multiset Empty)))) =
        (({value₂} : Multiset Atom), ((), (1 : Multiplicative (Multiset Empty)))) := by
    simpa [scReifiedOutcomeOf?_evalDropResidual] using hobs
  exact hdistinct (scObservedSingleton_value_injective hsingleton)

theorem evalDrop_scObservedOutcomes_distinguishes_certified_values
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload value₁ value₂ : Atom}
    (h₁ : CertifiedPayloadResult space dispatch payload value₁)
    (h₂ : CertifiedPayloadResult space dispatch payload value₂)
    (hdistinct : value₁ ≠ value₂) :
    (({value₁} : Multiset Atom), ((), (1 : Multiplicative (Multiset Empty)))) ∈
        RhometaSCObservedOutcomes space dispatch (evalDropSource chan payload) ∧
      (({value₂} : Multiset Atom), ((), (1 : Multiplicative (Multiset Empty)))) ∈
        RhometaSCObservedOutcomes space dispatch (evalDropSource chan payload) ∧
      (({value₁} : Multiset Atom), ((), (1 : Multiplicative (Multiset Empty)))) ≠
        (({value₂} : Multiset Atom), ((), (1 : Multiplicative (Multiset Empty)))) := by
  refine ⟨?_, ?_, ?_⟩
  · exact evalDrop_certified_value_scObservedOutcome
      (space := space) (dispatch := dispatch)
      (chan := chan) (payload := payload) h₁
  · exact evalDrop_certified_value_scObservedOutcome
      (space := space) (dispatch := dispatch)
      (chan := chan) (payload := payload) h₂
  · intro hobs
    exact hdistinct (scObservedSingleton_value_injective hobs)

theorem evalDrop_not_singlePathSafe_of_distinct_values
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload v₁ v₂ : Atom}
    (h₁ : CertifiedPayloadResult space dispatch payload v₁)
    (h₂ : CertifiedPayloadResult space dispatch payload v₂)
    (hdistinct : v₁ ≠ v₂) :
    ¬ RhometaSinglePathSafe space dispatch (evalDropSource chan payload) := by
  intro hsafe
  have hpair := evalDrop_preserves_all_certified_outcomes
    (space := space) (dispatch := dispatch)
    (chan := chan) (payload := payload)
    (v₁ := v₁) (v₂ := v₂) h₁ h₂
  have hres : evalDropResidual v₁ = evalDropResidual v₂ := hsafe hpair.1 hpair.2
  exact hdistinct (evalDropResidual_injective hres)

theorem outcomes_eq_of_singlePathSafe
    {space : Space} {dispatch : GroundedDispatch} {p q r : Pattern}
    (hsafe : RhometaSinglePathSafe space dispatch p)
    (hq : q ∈ RhometaOutcomes space dispatch p)
    (hr : r ∈ RhometaOutcomes space dispatch p) :
    q = r := by
  exact hsafe hq hr

theorem chosenOutcome_lossless_iff_singlePathSafe
    {space : Space} {dispatch : GroundedDispatch} {p q : Pattern}
    (hq : q ∈ RhometaOutcomes space dispatch p) :
    RhometaSinglePathSafe space dispatch p ↔
      ∀ r, r ∈ RhometaOutcomes space dispatch p → r = q := by
  constructor
  · intro hsafe r hr
    exact hsafe hr hq
  · intro hchosen r hr s hs
    rw [hchosen r hr, hchosen s hs]

/-! ## Concurrent fold — the commuting lemma for one fixed compatible matching (the ⊗ layer)

This block is the **⊗ layer** of the full rhometta semantics
(⊔ choice over compatible matchings + ⊗ parallel fold within a matching + `;` sequential closure of
rounds): it governs ONE pairwise-compatible matching fired as a single round.  It is deliberately
*not* the whole semantics — it does not model contention (choice between alternative pairings of the
same linear send/receive) nor causal chaining (a COMM enabling a later COMM); those phenomena require
the choice and sequencing layers and have operational witnesses in `Engine.lean` (race and multi-step
tests).  Treating this fold as the whole rhometta would overclaim.

Within its scope it is exact: a payload over a frozen base is a *nondeterministic producer of
`(result, local-delta)`*, where the delta lives in a commutative merge monoid `Δ` (a semilattice /
MORK union / cost quantale).  Firing an independent frontier chooses one outcome per payload and
merges the deltas commutatively, recording results as an order-independent multiset.  Because `Δ` is
a `CommMonoid`, the outcome set is invariant under firing order (`foldOutcomes_perm`) — macro-step
soundness for one round delivered as *algebra*, not a hand diamond.  Single-path safety factors as
"every payload is deterministic" (`foldOutcomes_subsingleton_of_forall`), generalizing
`chosenOutcome_lossless_iff_singlePathSafe`.  The value-only theory above is the `Δ := PUnit`
instance.  Payload non-interference is *structural* here (payload outcome sets are fixed data); an
engine step instantiates this fold only under the engine-side conditions (quiet continuations,
copy-stable results, unique matching, transactional isolation) — that instance-hood is a separate
corollary, not this lemma. -/
section ConcurrentFold

/-- A payload over the frozen base: its set of possible `(result, local-delta)` outcomes. -/
abbrev Payload (R Δ : Type*) := Set (R × Δ)

variable {R : Type*} {Δ : Type*} [CommMonoid Δ]

/-- Outcomes of firing a frontier (list of payloads): choose one `(result, delta)` per payload, merge
the deltas by the commutative product, and record the results as an order-independent multiset. -/
def foldOutcomes : List (Payload R Δ) → Set (Multiset R × Δ)
  | [] => {(0, 1)}
  | p :: F =>
      { x | ∃ r δ rs δ', (r, δ) ∈ p ∧ (rs, δ') ∈ foldOutcomes F ∧ x = (r ::ₘ rs, δ * δ') }

theorem mem_foldOutcomes_cons {p : Payload R Δ} {F : List (Payload R Δ)}
    {x : Multiset R × Δ} :
    x ∈ foldOutcomes (p :: F) ↔
      ∃ r δ rs δ', (r, δ) ∈ p ∧ (rs, δ') ∈ foldOutcomes F ∧ x = (r ::ₘ rs, δ * δ') :=
  Iff.rfl

/-- **Macro-step soundness as algebra**: the outcome set of an independent frontier is invariant under
firing order, because the merge monoid is commutative. -/
theorem foldOutcomes_perm {F₁ F₂ : List (Payload R Δ)} (h : F₁.Perm F₂) :
    foldOutcomes F₁ = foldOutcomes F₂ := by
  induction h with
  | nil => rfl
  | cons p _ ih => ext x; simp only [mem_foldOutcomes_cons, ih]
  | swap x y l =>
      ext z
      simp only [mem_foldOutcomes_cons]
      constructor
      · rintro ⟨ry, δy, RS, D, hy, hmid, rfl⟩
        obtain ⟨rx, δx, rs, δ', hx, hrs, hpair⟩ := hmid
        rw [Prod.mk.injEq] at hpair
        obtain ⟨rfl, rfl⟩ := hpair
        exact ⟨rx, δx, ry ::ₘ rs, δy * δ', hx, ⟨ry, δy, rs, δ', hy, hrs, rfl⟩, by
          simp only [Prod.mk.injEq]
          exact ⟨Multiset.cons_swap ry rx rs, mul_left_comm δy δx δ'⟩⟩
      · rintro ⟨rx, δx, RS, D, hx, hmid, rfl⟩
        obtain ⟨ry, δy, rs, δ', hy, hrs, hpair⟩ := hmid
        rw [Prod.mk.injEq] at hpair
        obtain ⟨rfl, rfl⟩ := hpair
        exact ⟨ry, δy, rx ::ₘ rs, δx * δ', hy, ⟨rx, δx, rs, δ', hx, hrs, rfl⟩, by
          simp only [Prod.mk.injEq]
          exact ⟨Multiset.cons_swap rx ry rs, mul_left_comm δx δy δ'⟩⟩
  | trans _ _ ih₁ ih₂ => rw [ih₁, ih₂]

/-- **Factorization (⟸)**: if every payload is deterministic (a subsingleton outcome set), the whole
frontier's outcome set is a subsingleton — i.e. single-path-safe.  Generalizes the crown theorem
`chosenOutcome_lossless_iff_singlePathSafe` to the delta-carrying setting. -/
theorem foldOutcomes_subsingleton_of_forall :
    ∀ {F : List (Payload R Δ)}, (∀ p ∈ F, p.Subsingleton) → (foldOutcomes F).Subsingleton
  | [], _ => by
      rintro a ha b hb
      simp only [foldOutcomes, Set.mem_singleton_iff] at ha hb
      rw [ha, hb]
  | p :: F, hsub => by
      rintro a ⟨r, δ, rs, δ', hr, hrs, rfl⟩ b ⟨r2, δ2, rs2, δ2', hr2, hrs2, rfl⟩
      have hp := hsub p (List.mem_cons.mpr (Or.inl rfl)) hr hr2
      have htail := foldOutcomes_subsingleton_of_forall
        (fun q hq => hsub q (List.mem_cons.mpr (Or.inr hq))) hrs hrs2
      rw [Prod.mk.injEq] at hp htail ⊢
      exact ⟨by rw [hp.1, htail.1], by rw [hp.2, htail.2]⟩

end ConcurrentFold

/-! ### Merged cost — the concurrent fold as a quantale-valued aggregate

When the merge monoid `Δ` also carries a complete lattice (e.g. the cost quantale `ℝ≥0∞` from
`Mettapedia.Algebra.QuantaleWeakness`), a payload's aggregate value is the join of its possible deltas,
and a frontier's merged cost is the commutative product of those aggregates.  This merged cost is
invariant under firing order (`foldCost_perm`) — the quantale shadow of `foldOutcomes_perm`. -/
section CostQuantale

variable {R : Type*} {Δ : Type*} [CommMonoid Δ] [CompleteLattice Δ]

/-- A payload's aggregate value: the join of its possible deltas. -/
noncomputable def payloadSup (p : Payload R Δ) : Δ := sSup {δ | ∃ r, (r, δ) ∈ p}

/-- A frontier's merged cost: the commutative product of the per-payload aggregates. -/
noncomputable def foldCost : List (Payload R Δ) → Δ
  | [] => 1
  | p :: F => payloadSup p * foldCost F

@[simp] theorem foldCost_nil : foldCost ([] : List (Payload R Δ)) = 1 := rfl

@[simp] theorem foldCost_cons (p : Payload R Δ) (F : List (Payload R Δ)) :
    foldCost (p :: F) = payloadSup p * foldCost F := rfl

/-- The merged cost of an independent frontier is invariant under firing order — the quantale shadow
of `foldOutcomes_perm`, by commutativity of the merge. -/
theorem foldCost_perm {F₁ F₂ : List (Payload R Δ)} (h : F₁.Perm F₂) :
    foldCost F₁ = foldCost F₂ := by
  induction h with
  | nil => rfl
  | cons p _ ih => simp only [foldCost_cons, ih]
  | swap x y l => simp only [foldCost_cons]; rw [mul_left_comm]
  | trans _ _ ih₁ ih₂ => rw [ih₁, ih₂]

end CostQuantale

/-! ### The quantale factorization — merged cost = aggregate over outcomes

When `Δ` is a quantale (the merge `*` distributes over arbitrary joins, as for the cost quantale
`ℝ≥0∞`), the recursive merged cost `foldCost` equals the join of the deltas of *all* concurrent
outcomes (`foldCost_eq_aggregate`).  So the macro step's single merged cost faithfully aggregates the
whole outcome lattice — macro-step soundness for the cost observable, delivered by quantale
distributivity. -/
section CostAggregate

variable {R : Type*} {Δ : Type*} [CommMonoid Δ] [CompleteLattice Δ] [IsQuantale Δ]

/-- The product of two joins is the join of the pairwise products (quantale distributivity). -/
theorem sSup_mul_sSup (A B : Set Δ) :
    sSup A * sSup B = ⨆ a ∈ A, ⨆ b ∈ B, a * b := by
  rw [sSup_mul_distrib]
  simp_rw [mul_sSup_distrib]

/-- **Quantale factorization**: the frontier's recursive merged cost equals the join of the merged
deltas over every concurrent outcome.  Macro-step soundness for the cost observable. -/
theorem foldCost_eq_aggregate (F : List (Payload R Δ)) :
    foldCost F = sSup (Prod.snd '' foldOutcomes F) := by
  induction F with
  | nil =>
      rw [foldCost_nil, foldOutcomes, Set.image_singleton]
      simp
  | cons p F ih =>
      rw [foldCost_cons, ih, payloadSup, sSup_mul_sSup]
      apply le_antisymm
      · refine iSup₂_le fun a ha => iSup₂_le fun b hb => le_sSup ?_
        obtain ⟨r, hr⟩ := ha
        obtain ⟨x, hxF, rfl⟩ := hb
        exact ⟨(r ::ₘ x.1, a * x.2),
          mem_foldOutcomes_cons.mpr ⟨r, a, x.1, x.2, hr, hxF, rfl⟩, rfl⟩
      · refine sSup_le fun c hc => ?_
        obtain ⟨x, hx, rfl⟩ := hc
        rw [mem_foldOutcomes_cons] at hx
        obtain ⟨r, δ, rs, δ', hr, hrs, rfl⟩ := hx
        exact le_iSup₂_of_le δ ⟨r, hr⟩ (le_iSup₂_of_le δ' ⟨(rs, δ'), hrs, rfl⟩ le_rfl)

end CostAggregate

/-! ### Result branching factors out of the merge

The other half of the factorization: the multiset of *results* reachable is the pure result fold,
independent of the delta monoid.  Together with `foldCost_eq_aggregate`, the may-set factors as
(result branching) × (merge/cost skeleton). -/
section ResultFactor

variable {R : Type*} {Δ : Type*} [CommMonoid Δ]

/-- The pure result fold: the multisets of results from choosing one result per payload. -/
def resultOutcomes : List (Set R) → Set (Multiset R)
  | [] => {0}
  | p :: F => {x | ∃ r rs, r ∈ p ∧ rs ∈ resultOutcomes F ∧ x = r ::ₘ rs}

theorem mem_resultOutcomes_cons {p : Set R} {F : List (Set R)} {x : Multiset R} :
    x ∈ resultOutcomes (p :: F) ↔
      ∃ r rs, r ∈ p ∧ rs ∈ resultOutcomes F ∧ x = r ::ₘ rs :=
  Iff.rfl

/-- The result-multiset reachable is the pure result fold, independent of the delta monoid. -/
theorem foldOutcomes_fst (F : List (Payload R Δ)) :
    Prod.fst '' foldOutcomes F = resultOutcomes (F.map (fun p => Prod.fst '' p)) := by
  induction F with
  | nil => simp [foldOutcomes, resultOutcomes]
  | cons p F ih =>
      ext z
      simp only [List.map_cons, mem_resultOutcomes_cons, Set.mem_image]
      constructor
      · rintro ⟨x, hx, rfl⟩
        rw [mem_foldOutcomes_cons] at hx
        obtain ⟨r, δ, rs, δ', hr, hrs, rfl⟩ := hx
        refine ⟨r, rs, ⟨(r, δ), hr, rfl⟩, ?_, rfl⟩
        rw [← ih]; exact ⟨(rs, δ'), hrs, rfl⟩
      · rintro ⟨r, rs, ⟨rδ, hrδ, hrr⟩, hrs, rfl⟩
        rw [← ih] at hrs
        obtain ⟨y, hy, rfl⟩ := hrs
        refine ⟨(rδ.1 ::ₘ y.1, rδ.2 * y.2), mem_foldOutcomes_cons.mpr
          ⟨rδ.1, rδ.2, y.1, y.2, hrδ, hy, rfl⟩, ?_⟩
        simp [hrr]

end ResultFactor

/-! ### Grounding: the fold fires on real rhometta merge and on the cost quantale

These witnesses confirm the abstract theory applies to concrete rhometta data: `Δ` a bag-space delta
(`Multiset Atom` merge, via `Multiplicative`) gives order-independent residual outcomes; `Δ = ℝ≥0∞`
(the project's cost quantale) gives the merged-cost factorization. -/
section Grounding

open scoped ENNReal

/-- rhometta residuals merging bag-space deltas: the concurrent fold is order-independent. -/
example {F₁ F₂ : List (Payload Pattern (Multiplicative (Multiset Atom)))} (h : F₁.Perm F₂) :
    foldOutcomes F₁ = foldOutcomes F₂ :=
  foldOutcomes_perm h

/-- rhometta cost in the `ℝ≥0∞` quantale: merged cost = join over all concurrent outcomes. -/
example (F : List (Payload Pattern ℝ≥0∞)) :
    foldCost F = sSup (Prod.snd '' foldOutcomes F) :=
  foldCost_eq_aggregate F

end Grounding

/-! ## First-class owned exports — the Ω layer (transactional outcomes)

The engine's transactional payloads do three things: produce a result, accumulate a local delta, and
let mutated resources escape only as *owned exports* (fresh-identity spaces/state cells returned as
values).  Here exports become first-class in the outcome object: a payload outcome is
`(result, delta, exports)` with exports an order-irrelevant bag.

The crucial economy: `PayloadΩ R Δ Ω` is *definitionally* the existing `Payload` over the product
merge monoid `Δ × ExportBag Ω`, so the entire ⊗-layer theory (`foldOutcomes`, `foldOutcomes_perm`,
the factorizations) applies verbatim — nothing is re-proven (`foldOutcomesΩ_perm`).  Dropping
exports along the projection monoid hom recovers the export-free theory
(`foldOutcomesΩ_proj_delta`, via the general naturality lemma `foldOutcomes_map_hom`), so the
development above is literally the shadow of this one.

`reifyΩ` is the abstract form of what the engine does with owned results: pack result and exports
together (owned results returned as values in the residual), delta separate.  It is injective
(`reifyΩ_injective`) — reification loses nothing — and commutes with firing a round
(`reifyΩ_fold_commutes`): reify-then-fold equals fold-then-reify on aggregate observables.  The
closing example shows exports are *semantically real*: two payloads with identical result/delta
projections but different owned exports are distinguished after reification — outcome objects
without exports are too coarse for transactional rhometta. -/
section OwnedExports

/-- A bag of owned exports, as a multiplicative commutative monoid (merge = bag union). -/
abbrev ExportBag (Ω : Type*) := Multiplicative (Multiset Ω)

/-- A transactional payload: a nondeterministic producer of `(result, delta, exports)` over a frozen
base.  Definitionally a `Payload` over the product merge monoid, so the concurrent-fold theory
applies verbatim. -/
abbrev PayloadΩ (R Δ Ω : Type*) := Payload R (Δ × ExportBag Ω)

variable {R Δ Ω : Type*} [CommMonoid Δ]

/-- Outcomes of firing a frontier of transactional payloads: the existing fold over the product
monoid — deltas merge in `Δ`, export bags merge by union. -/
abbrev foldOutcomesΩ (F : List (PayloadΩ R Δ Ω)) : Set (Multiset R × (Δ × ExportBag Ω)) :=
  foldOutcomes F

/-- Order-independence of the transactional round, inherited verbatim from the ⊗ layer. -/
theorem foldOutcomesΩ_perm {F₁ F₂ : List (PayloadΩ R Δ Ω)} (h : F₁.Perm F₂) :
    foldOutcomesΩ F₁ = foldOutcomesΩ F₂ :=
  foldOutcomes_perm h

/-- **Naturality**: the concurrent fold commutes with any monoid hom on the merge — mapping every
payload along `f` and folding equals folding and then mapping the merged delta. -/
theorem foldOutcomes_map_hom {Δ' : Type*} [CommMonoid Δ'] (f : Δ →* Δ') :
    ∀ F : List (Payload R Δ),
      foldOutcomes (F.map (fun p => (fun o : R × Δ => (o.1, f o.2)) '' p)) =
        (fun x : Multiset R × Δ => (x.1, f x.2)) '' foldOutcomes F
  | [] => by
      ext x
      simp [foldOutcomes, Set.image_singleton]
  | p :: F => by
      ext x
      simp only [List.map_cons, mem_foldOutcomes_cons, Set.mem_image]
      constructor
      · rintro ⟨r, δ, rs, δ', ⟨⟨a, b⟩, hab, hg⟩, hrs, rfl⟩
        rw [foldOutcomes_map_hom f F] at hrs
        obtain ⟨⟨rs₀, d₀⟩, hd₀, hg₂⟩ := hrs
        rw [Prod.mk.injEq] at hg hg₂
        obtain ⟨rfl, rfl⟩ := hg
        obtain ⟨rfl, rfl⟩ := hg₂
        exact ⟨(a ::ₘ rs₀, b * d₀), ⟨a, b, rs₀, d₀, hab, hd₀, rfl⟩, by
          simp [map_mul]⟩
      · rintro ⟨⟨RS, D⟩, hRSD, rfl⟩
        obtain ⟨r, δ, rs, δ', hr, hrs, hpair⟩ := hRSD
        rw [Prod.mk.injEq] at hpair
        obtain ⟨rfl, rfl⟩ := hpair
        refine ⟨r, f δ, rs, f δ', ⟨(r, δ), hr, rfl⟩, ?_, by simp [map_mul]⟩
        rw [foldOutcomes_map_hom f F]
        exact ⟨(rs, δ'), hrs, rfl⟩

/-- **Conservativity**: dropping exports (the projection monoid hom) recovers the export-free
theory — the Δ-only development is the image of the transactional one. -/
theorem foldOutcomesΩ_proj_delta (F : List (PayloadΩ R Δ Ω)) :
    foldOutcomes (F.map (fun p => (fun o : R × (Δ × ExportBag Ω) => (o.1, o.2.1)) '' p)) =
      (fun x : Multiset R × (Δ × ExportBag Ω) => (x.1, x.2.1)) '' foldOutcomesΩ F :=
  foldOutcomes_map_hom (MonoidHom.fst Δ (ExportBag Ω)) F

/-- Reify a transactional outcome into the residual-style shape the engine returns: result and
exports packed together (owned results as values in the residual), delta separate. -/
def reifyΩ (o : R × (Δ × ExportBag Ω)) : (R × Multiset Ω) × Δ :=
  ((o.1, (o.2.2 : ExportBag Ω).toAdd), o.2.1)

omit [CommMonoid Δ] in
/-- **Reification loses no information.** -/
theorem reifyΩ_injective : Function.Injective (reifyΩ (R := R) (Δ := Δ) (Ω := Ω)) := by
  rintro ⟨r₁, δ₁, ω₁⟩ ⟨r₂, δ₂, ω₂⟩ h
  simp only [reifyΩ, Prod.mk.injEq] at h
  obtain ⟨⟨rfl, hω⟩, rfl⟩ := h
  simp only [Prod.mk.injEq, true_and]
  exact Multiplicative.toAdd.injective hω

/-- Aggregate a reified round outcome: strip per-result export attachments into one merged bag. -/
def aggregateReified (x : Multiset (R × Multiset Ω) × Δ) : Multiset R × Δ × Multiset Ω :=
  (x.1.map Prod.fst, x.2, (x.1.map Prod.snd).sum)

/-- Reshape a transactional fold outcome to the same observable type. -/
def reshapeΩ (x : Multiset R × (Δ × ExportBag Ω)) : Multiset R × Δ × Multiset Ω :=
  (x.1, x.2.1, (x.2.2 : ExportBag Ω).toAdd)

/-- **Reification commutes with the round**: reifying every payload, firing the round, and
aggregating equals firing the transactional round and reshaping — reify-then-fold =
fold-then-reify on aggregate observables. -/
theorem reifyΩ_fold_commutes :
    ∀ F : List (PayloadΩ R Δ Ω),
      aggregateReified '' foldOutcomes (F.map (Set.image reifyΩ)) =
        reshapeΩ '' foldOutcomesΩ F
  | [] => by
      ext x
      simp [foldOutcomes, Set.image_singleton, aggregateReified, reshapeΩ]
  | p :: F => by
      ext x
      simp only [List.map_cons, Set.mem_image]
      constructor
      · rintro ⟨⟨RS, D⟩, hRSD, rfl⟩
        obtain ⟨rω, δ, rs, δ', hrω, hrs, hpair⟩ := hRSD
        rw [Prod.mk.injEq] at hpair
        obtain ⟨rfl, rfl⟩ := hpair
        obtain ⟨⟨a, b, ωm⟩, hab, hg⟩ := hrω
        have hagg : aggregateReified (rs, δ') ∈
            aggregateReified '' foldOutcomes (F.map (Set.image reifyΩ)) :=
          ⟨(rs, δ'), hrs, rfl⟩
        rw [reifyΩ_fold_commutes F] at hagg
        obtain ⟨⟨rs₀, d₀, ωs₀⟩, hmem, hsh⟩ := hagg
        refine ⟨(a ::ₘ rs₀, (b * d₀, ωm * ωs₀)),
          ⟨a, (b, ωm), rs₀, (d₀, ωs₀), hab, hmem, by simp⟩, ?_⟩
        simp only [reifyΩ] at hg
        rw [Prod.mk.injEq] at hg
        obtain ⟨hg1, rfl⟩ := hg
        simp only [reshapeΩ, aggregateReified, reshapeΩ] at hsh ⊢
        rw [Prod.mk.injEq] at hsh
        obtain ⟨h1, h2⟩ := hsh
        rw [Prod.mk.injEq] at h2
        obtain ⟨h2, h3⟩ := h2
        simp only [Multiset.map_cons, Multiset.sum_cons, ← hg1, Prod.mk.injEq]
        refine ⟨by rw [h1], by rw [h2], ?_⟩
        rw [← h3, toAdd_mul]
      · rintro ⟨⟨RS, D⟩, hRSD, rfl⟩
        obtain ⟨a, bω, rs, δω', hab, hrs, hpair⟩ := hRSD
        obtain ⟨b, ωm⟩ := bω
        obtain ⟨δ', ωs'⟩ := δω'
        rw [Prod.mk.injEq] at hpair
        obtain ⟨rfl, rfl⟩ := hpair
        have hsh : reshapeΩ (rs, (δ', ωs')) ∈ reshapeΩ '' foldOutcomesΩ F :=
          ⟨(rs, (δ', ωs')), hrs, rfl⟩
        rw [← reifyΩ_fold_commutes F] at hsh
        obtain ⟨⟨RS₀, D₀⟩, hmem, hagg⟩ := hsh
        refine ⟨((a, ωm.toAdd) ::ₘ RS₀, b * D₀),
          ⟨(a, ωm.toAdd), b, RS₀, D₀, ⟨(a, (b, ωm)), hab, rfl⟩, hmem, rfl⟩, ?_⟩
        simp only [aggregateReified, reshapeΩ] at hagg ⊢
        rw [Prod.mk.injEq] at hagg
        obtain ⟨h1, h2⟩ := hagg
        rw [Prod.mk.injEq] at h2
        obtain ⟨h2, h3⟩ := h2
        simp only [Multiset.map_cons, Multiset.sum_cons, Prod.fst_mul, Prod.snd_mul,
          toAdd_mul, Prod.mk.injEq]
        exact ⟨by rw [h1], by rw [h2], by rw [h3]⟩

/-- Positive grounding: a singleton transactional frontier yields exactly its payload's outcome,
exports included. -/
theorem foldOutcomesΩ_singleton (r₀ : R) (δ₀ : Δ × ExportBag Ω) :
    foldOutcomesΩ [({(r₀, δ₀)} : PayloadΩ R Δ Ω)] = {(({r₀} : Multiset R), δ₀)} := by
  ext x
  simp only [foldOutcomesΩ, foldOutcomes, Set.mem_singleton_iff]
  constructor
  · rintro ⟨r, δ, rs, δ', hr, hrs, rfl⟩
    rw [Prod.mk.injEq] at hr hrs
    obtain ⟨rfl, rfl⟩ := hr
    obtain ⟨rfl, rfl⟩ := hrs
    simp
  · rintro rfl
    exact ⟨r₀, δ₀, 0, 1, rfl, rfl, by simp⟩

/-- A concrete transactional round: one payload exporting an owned resource. -/
example :
    foldOutcomesΩ [({((), (2, Multiplicative.ofAdd ({true} : Multiset Bool)))} :
        PayloadΩ Unit ℕ Bool)] =
      {(({()} : Multiset Unit), (2, Multiplicative.ofAdd ({true} : Multiset Bool)))} :=
  foldOutcomesΩ_singleton _ _

/-- **Exports are semantically real** (the no-go-3 content): two payloads with identical
result/delta projections but different owned exports are distinguished after reification — outcome
objects without exports are too coarse for transactional rhometta. -/
example :
    ∃ p₁ p₂ : PayloadΩ Unit ℕ Bool,
      (fun o : Unit × (ℕ × ExportBag Bool) => (o.1, o.2.1)) '' p₁ =
        (fun o : Unit × (ℕ × ExportBag Bool) => (o.1, o.2.1)) '' p₂ ∧
      reifyΩ '' p₁ ≠ reifyΩ '' p₂ := by
  refine ⟨{((), (1, Multiplicative.ofAdd ({true} : Multiset Bool)))},
          {((), (1, Multiplicative.ofAdd ({false} : Multiset Bool)))}, ?_, ?_⟩
  · simp [Set.image_singleton]
  · simp only [Set.image_singleton, reifyΩ, ne_eq, Set.singleton_eq_singleton_iff]
    intro h
    rw [Prod.mk.injEq] at h
    have := h.1
    rw [Prod.mk.injEq] at this
    have hbag := this.2
    simp only [toAdd_ofAdd] at hbag
    exact absurd (Multiset.singleton_inj.mp hbag) (by decide)

end OwnedExports

/-! ## Operational reification helpers

The current Rhometta operational relation steps in the already reified residual domain: certified
payload evaluation returns an atom, and the COMM residual carries it as `rho:val`.  These helpers
package that live operational carrier as a transactional payload over trivial delta/empty-export
observables, so the B7 bridge can talk directly to the current relation without pretending the
richer Ω object has already been split out of the runtime surface. -/
section OperationalReification

local instance : CommMonoid Unit where
  mul _ _ := ()
  mul_assoc _ _ _ := rfl
  one := ()
  one_mul _ := rfl
  mul_one _ := rfl
  mul_comm _ _ := rfl

/-- A certified operational payload outcome, viewed in the post-reification carrier:
result atom returned, no separate delta, no explicit exports after reification. -/
def certifiedPayloadReified
    (space : Space) (dispatch : GroundedDispatch) (payload : Atom) :
    PayloadΩ Atom Unit Empty :=
  { o | ∃ value, CertifiedPayloadResult space dispatch payload value ∧
      o = (value, ((), (1 : ExportBag Empty))) }

theorem certifiedPayloadReified_mem_of_certified
    {space : Space} {dispatch : GroundedDispatch} {payload value : Atom}
    (hcert : CertifiedPayloadResult space dispatch payload value) :
    (value, ((), (1 : ExportBag Empty))) ∈
      certifiedPayloadReified space dispatch payload := by
  exact ⟨value, hcert, rfl⟩

theorem certifiedPayloadReified_nonempty_iff
    {space : Space} {dispatch : GroundedDispatch} {payload : Atom} :
    (certifiedPayloadReified space dispatch payload).Nonempty ↔
      ∃ value, CertifiedPayloadResult space dispatch payload value := by
  constructor
  · rintro ⟨o, ho⟩
    rcases ho with ⟨value, hcert, rfl⟩
    exact ⟨value, hcert⟩
  · rintro ⟨value, hcert⟩
    exact ⟨(value, ((), (1 : ExportBag Empty))), certifiedPayloadReified_mem_of_certified hcert⟩

theorem evalDrop_outcome_factors_through_one_step_of_ready
    {space : Space} {dispatch : GroundedDispatch}
    {chan q : Pattern} {payload : Atom}
    (hready : (certifiedPayloadReified space dispatch payload).Nonempty)
    (hout : q ∈ RhometaOutcomes space dispatch (evalDropSource chan payload)) :
    ∃ r,
      Nonempty (RhometaReduces space dispatch (evalDropSource chan payload) r) ∧
      q ∈ RhometaOutcomes space dispatch r := by
  rcases (certifiedPayloadReified_nonempty_iff
      (space := space) (dispatch := dispatch) (payload := payload)).mp hready with
    ⟨value, hcert⟩
  exact evalDrop_outcome_factors_through_one_step_of_certified
    (space := space) (dispatch := dispatch)
    (chan := chan) (payload := payload) (value := value) hcert hout

theorem evalDrop_scObservedOutcome_factors_through_one_step_of_ready
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload : Atom}
    {obs : Multiset Atom × (Unit × Multiplicative (Multiset Empty))}
    (hready : (certifiedPayloadReified space dispatch payload).Nonempty)
    (hobs :
      obs ∈ RhometaSCObservedOutcomes space dispatch
        (evalDropSource chan payload)) :
    ∃ r q s,
      Nonempty (RhometaReduces space dispatch (evalDropSource chan payload) r) ∧
      q ∈ RhometaOutcomes space dispatch r ∧
      StructuralCongruence q s ∧
      scReifiedOutcomeOf? s = some obs := by
  rcases hobs with ⟨q, s, hq, hqs, hdec⟩
  rcases evalDrop_outcome_factors_through_one_step_of_ready
      (space := space) (dispatch := dispatch)
      (chan := chan) (payload := payload) hready hq with
    ⟨r, hstep, hout⟩
  exact ⟨r, q, s, hstep, hout, hqs, hdec⟩

theorem certifiedPayloadReified_singleton_fold_mem_of_certified
    {space : Space} {dispatch : GroundedDispatch} {payload value : Atom}
    (hcert : CertifiedPayloadResult space dispatch payload value) :
    (({value} : Multiset Atom), ((), (1 : ExportBag Empty))) ∈
      foldOutcomesΩ [certifiedPayloadReified space dispatch payload] := by
  refine ⟨value, ((), (1 : ExportBag Empty)), 0, 1, ?_, ?_, ?_⟩
  · exact certifiedPayloadReified_mem_of_certified hcert
  · rfl
  · simp

/-- Concrete one-branch bridge seed for B7: one certified operational eval-at-COMM branch
matches one singleton abstract payload outcome in the post-reification carrier. -/
theorem evalDrop_certified_branch_matches_reified_singleton
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload value : Atom}
    (hcert : CertifiedPayloadResult space dispatch payload value) :
    Nonempty (RhometaReduces space dispatch
        (evalDropSource chan payload) (evalDropResidual value)) ∧
      reifiedOutcomeOf? (evalDropResidual value) =
        some (({value} : Multiset Atom), ((), (1 : Multiplicative (Multiset Empty)))) ∧
      (({value} : Multiset Atom), ((), (1 : ExportBag Empty))) ∈
        foldOutcomesΩ [certifiedPayloadReified space dispatch payload] := by
  exact ⟨evalDrop_certified_branch hcert,
    reifiedOutcomeOf?_evalDropResidual value,
    certifiedPayloadReified_singleton_fold_mem_of_certified hcert⟩

end OperationalReification

/-! ## Event layer — the ⊔/`;` boundary vocabulary (events, compatibility, matchings)

An `EventSkeleton` is a COMM candidate: which output occurrence and which input occurrence it
would consume (as frontier indices), and the transactional payload it would run.  `Compatible` is
the MODEL-level relation — distinct consumed occurrences and disjoint export identities.  It is
deliberately weaker than the engine's macro side conditions (quiet continuations, copy-stable
results, unique matching): in the model, payload non-interference is structural, so bare
compatibility carries the abstract theorems; the engine conditions enter only as explicit
hypotheses of the engine-facing corollary.

A matching is a pairwise-compatible selection of events fired together as one round; `MatchOf` is
ALL compatible matchings over an enabled set — including the empty and singleton ones, so the
exact one-redex reducer embeds as the finest refinement and every concrete scheduler is a
refinement of this one base.

The two no-go theorems pin the boundary the round/run layers must respect:
`contention_requires_choice` — a contended enabled set is represented by NO single fold, so a
one-round semantics must branch over matchings (additive choice ⊔); and
`chaining_not_single_round` — one-round folds only produce results offered by enabled payloads,
so an outcome enabled only by a *later* COMM needs sequential closure (`;`).  The same witnesses
are pinned operationally by the race/chaining theorems in `Engine.lean` and at runtime by the
`eval:contended-pair` / `eval:chained-two-round` bridge fixtures. -/
section EventLayer

variable {R Δ Ω : Type*}

/-- A COMM candidate: the output/input occurrences it consumes (frontier indices) and the
transactional payload fired at the rendezvous. -/
structure EventSkeleton (R Δ Ω : Type*) where
  sendIdx : ℕ
  recvIdx : ℕ
  payload : PayloadΩ R Δ Ω

/-- The owned-export identities an event's payload can produce. -/
def EventSkeleton.exports (e : EventSkeleton R Δ Ω) : Set Ω :=
  { ω | ∃ o ∈ e.payload, ω ∈ ((o.2.2 : ExportBag Ω).toAdd : Multiset Ω) }

/-- Model-level compatibility: distinct consumed occurrences (no shared linear send or receive)
and disjoint export identities.  Deliberately weaker than the engine's macro conditions — see the
section header. -/
structure Compatible (e₁ e₂ : EventSkeleton R Δ Ω) : Prop where
  send_ne : e₁.sendIdx ≠ e₂.sendIdx
  recv_ne : e₁.recvIdx ≠ e₂.recvIdx
  exports_disjoint : Disjoint e₁.exports e₂.exports

theorem Compatible.symm {e₁ e₂ : EventSkeleton R Δ Ω} (h : Compatible e₁ e₂) :
    Compatible e₂ e₁ :=
  ⟨h.send_ne.symm, h.recv_ne.symm, h.exports_disjoint.symm⟩

/-- Compatibility is irreflexive: an event would consume its own send twice. -/
theorem not_compatible_self (e : EventSkeleton R Δ Ω) : ¬Compatible e e :=
  fun h => h.send_ne rfl

/-- Contention: two events consuming the same linear send are incompatible. -/
theorem not_compatible_of_shared_send {e₁ e₂ : EventSkeleton R Δ Ω}
    (h : e₁.sendIdx = e₂.sendIdx) : ¬Compatible e₁ e₂ :=
  fun hc => hc.send_ne h

/-- A matching: a pairwise-compatible selection of events, fired together as one round.  Carried
as a list (the fold's native shape); order is irrelevant by `foldOutcomesΩ_perm`, and pairwise
compatibility forces distinctness via `not_compatible_self`. -/
def IsMatching (M : List (EventSkeleton R Δ Ω)) : Prop :=
  M.Pairwise Compatible

/-- ALL compatible matchings over an enabled set — including `[]` and singletons, so the exact
one-redex reducer embeds as the finest refinement of this one base relation. -/
def MatchOf (E : Set (EventSkeleton R Δ Ω)) : Set (List (EventSkeleton R Δ Ω)) :=
  { M | (∀ e ∈ M, e ∈ E) ∧ IsMatching M }

/-- The payloads a matching fires. -/
def matchingPayloads (M : List (EventSkeleton R Δ Ω)) : List (PayloadΩ R Δ Ω) :=
  M.map (·.payload)

@[simp] theorem nil_mem_matchOf (E : Set (EventSkeleton R Δ Ω)) : [] ∈ MatchOf E :=
  ⟨by simp, List.Pairwise.nil⟩

/-- Singletons are matchings: the exact one-redex step is a legal round. -/
theorem singleton_mem_matchOf {E : Set (EventSkeleton R Δ Ω)} {e : EventSkeleton R Δ Ω}
    (he : e ∈ E) : [e] ∈ MatchOf E :=
  ⟨by simpa using he, List.pairwise_singleton _ _⟩

/-- Sub-selections of a matching are matchings: the base is closed under sub-rounds. -/
theorem matchOf_sublist {E : Set (EventSkeleton R Δ Ω)} {M M' : List (EventSkeleton R Δ Ω)}
    (hM : M ∈ MatchOf E) (hsub : List.Sublist M' M) : M' ∈ MatchOf E :=
  ⟨fun e he => hM.1 e (hsub.subset he), hM.2.sublist hsub⟩

/-- In a contended pair (shared linear send), every matching fires at most one event. -/
theorem matchOf_length_le_one_of_shared_send {e₁ e₂ : EventSkeleton R Δ Ω}
    (hsend : e₁.sendIdx = e₂.sendIdx) :
    ∀ M ∈ MatchOf {e₁, e₂}, M.length ≤ 1 := by
  rintro M ⟨hmem, hpair⟩
  match M with
  | [] => simp
  | [_] => simp
  | a :: b :: rest =>
    exfalso
    have hcab : Compatible a b := (List.pairwise_cons.mp hpair).1 b (by simp)
    have ha := hmem a (by simp)
    have hb := hmem b (by simp)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    have hsame : a.sendIdx = b.sendIdx := by
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
        first | rfl | exact hsend | exact hsend.symm
    exact not_compatible_of_shared_send hsame hcab

variable [CommMonoid Δ]

/-- Every outcome of a frontier carries exactly one result per fired payload. -/
theorem foldOutcomes_card {F : List (Payload R Δ)} :
    ∀ x ∈ foldOutcomes F, x.1.card = F.length := by
  induction F with
  | nil =>
      rintro x hx
      simp only [foldOutcomes, Set.mem_singleton_iff] at hx
      subst hx; simp
  | cons p F ih =>
      rintro x ⟨r, δ, rs, δ', _, hrs, rfl⟩
      simp [ih (rs, δ') hrs]

/-- A frontier of nonempty payloads has a nonempty outcome set. -/
theorem foldOutcomes_nonempty {F : List (Payload R Δ)} (h : ∀ p ∈ F, p.Nonempty) :
    (foldOutcomes F).Nonempty := by
  induction F with
  | nil => exact ⟨(0, 1), rfl⟩
  | cons p F ih =>
      obtain ⟨⟨r, δ⟩, hrδ⟩ := h p (by simp)
      obtain ⟨⟨rs, δ'⟩, hrs⟩ := ih (fun q hq => h q (by simp [hq]))
      exact ⟨(r ::ₘ rs, δ * δ'), ⟨r, δ, rs, δ', hrδ, hrs, rfl⟩⟩

/-- **Provenance**: every result in a round outcome is offered by one of the fired payloads. -/
theorem foldOutcomes_results_mem {F : List (Payload R Δ)} :
    ∀ x ∈ foldOutcomes F, ∀ r ∈ x.1, ∃ p ∈ F, ∃ δ, (r, δ) ∈ p := by
  induction F with
  | nil =>
      rintro x hx r hr
      simp only [foldOutcomes, Set.mem_singleton_iff] at hx
      subst hx; simp at hr
  | cons p F ih =>
      rintro x ⟨r₀, δ₀, rs, δ', hr₀, hrs, rfl⟩ r hr
      rcases Multiset.mem_cons.mp hr with rfl | hr
      · exact ⟨p, by simp, δ₀, hr₀⟩
      · obtain ⟨q, hq, δ, hmem⟩ := ih (rs, δ') hrs r hr
        exact ⟨q, by simp [hq], δ, hmem⟩

/-- **No-go: contention requires choice (⊔).**  When two enabled events contend for the same
linear send, the raw fold over BOTH is the fold of NO legal matching: every matching of the
contended pair fires at most one event (outcomes carry ≤ 1 result), while the raw fold's outcomes
carry two.  A one-round semantics must branch over matchings — additive choice — rather than fold
the enabled set.  Operational echo: `Engine.lean` race theorem; runtime echo: the
`eval:contended-pair` bridge fixture. -/
theorem contention_requires_choice {e₁ e₂ : EventSkeleton R Δ Ω}
    (hsend : e₁.sendIdx = e₂.sendIdx)
    (h₁ : e₁.payload.Nonempty) (h₂ : e₂.payload.Nonempty) :
    ∀ M ∈ MatchOf {e₁, e₂},
      foldOutcomesΩ (matchingPayloads M) ≠ foldOutcomesΩ [e₁.payload, e₂.payload] := by
  rintro M hM heq
  have hlen : M.length ≤ 1 := matchOf_length_le_one_of_shared_send hsend M hM
  obtain ⟨x, hx⟩ : (foldOutcomesΩ [e₁.payload, e₂.payload]).Nonempty :=
    foldOutcomes_nonempty (by
      rintro p hp
      rcases List.mem_pair.mp hp with rfl | rfl
      · exact h₁
      · exact h₂)
  have hc2 : x.1.card = 2 := foldOutcomes_card x hx
  rw [← heq] at hx
  have hc1 : x.1.card = (matchingPayloads M).length := foldOutcomes_card x hx
  rw [matchingPayloads, List.length_map] at hc1
  omega

/-- **No-go: chaining requires sequence (`;`).**  A one-round fold over an enabled set only
produces results offered by the enabled payloads (provenance).  So an outcome whose result is
offered by NO initially-enabled payload — e.g. one enabled only after a first COMM exposes a new
send — is unreachable in any single round, whichever matching fires: reaching it requires
sequential closure of rounds.  Operational echo: `Engine.lean` two-step chaining theorem; runtime
echo: the `eval:chained-two-round` bridge fixture. -/
theorem chaining_not_single_round {E : Set (EventSkeleton R Δ Ω)} {target : R}
    (hno : ∀ e ∈ E, ∀ o ∈ e.payload, o.1 ≠ target) :
    ∀ M ∈ MatchOf E, ∀ x ∈ foldOutcomesΩ (matchingPayloads M), target ∉ x.1 := by
  rintro M ⟨hmem, _⟩ x hx htgt
  obtain ⟨p, hp, δ, hpδ⟩ := foldOutcomes_results_mem x hx target htgt
  obtain ⟨e, heM, rfl⟩ := List.mem_map.mp hp
  exact absurd rfl (hno e (hmem e heM) (target, δ) hpδ)

/-- Concrete contended pair: one send (occurrence 0), two receivers — no single fold represents
the round. -/
example :
    ∀ M ∈ MatchOf {(⟨0, 0, {(true, (1, 1))}⟩ : EventSkeleton Bool ℕ Empty),
                   (⟨0, 1, {(false, (1, 1))}⟩ : EventSkeleton Bool ℕ Empty)},
      foldOutcomesΩ (matchingPayloads M) ≠
        foldOutcomesΩ [{(true, (1, 1))}, {(false, (1, 1))}] :=
  contention_requires_choice rfl ⟨_, rfl⟩ ⟨_, rfl⟩

/-- Concrete chained witness: the only enabled payload offers `false`; the `true`-producing event
exists but is not yet enabled — no single round reaches `true`. -/
example :
    ∀ M ∈ MatchOf {(⟨0, 0, {(false, (1, 1))}⟩ : EventSkeleton Bool ℕ Empty)},
      ∀ x ∈ foldOutcomesΩ (matchingPayloads M), true ∉ x.1 :=
  chaining_not_single_round (by
    rintro e he o ho
    simp only [Set.mem_singleton_iff] at he
    subst he
    simp only [Set.mem_singleton_iff] at ho
    subst ho
    simp)

/-- Membership in a one-payload fold: exactly the payload's outcomes, singleton-wrapped. -/
theorem mem_foldOutcomes_singleton {p : Payload R Δ} {x : Multiset R × Δ} :
    x ∈ foldOutcomes [p] ↔ ∃ o ∈ p, x = ({o.1}, o.2) := by
  simp only [foldOutcomes, Set.mem_singleton_iff]
  constructor
  · rintro ⟨r, δ, rs, δ', hr, hrs, rfl⟩
    rw [Prod.mk.injEq] at hrs
    obtain ⟨rfl, rfl⟩ := hrs
    exact ⟨(r, δ), hr, by simp⟩
  · rintro ⟨⟨r, δ⟩, hr, rfl⟩
    exact ⟨r, δ, 0, 1, hr, rfl, by simp⟩

/-- Folds split over frontier concatenation: an outcome of `F₁ ++ F₂` is the pointwise merge of
an outcome of each part. -/
theorem mem_foldOutcomes_append {F₁ F₂ : List (Payload R Δ)} {x : Multiset R × Δ} :
    x ∈ foldOutcomes (F₁ ++ F₂) ↔
      ∃ x₁ ∈ foldOutcomes F₁, ∃ x₂ ∈ foldOutcomes F₂, x = (x₁.1 + x₂.1, x₁.2 * x₂.2) := by
  induction F₁ generalizing x with
  | nil =>
      simp only [List.nil_append, foldOutcomes, Set.mem_singleton_iff]
      constructor
      · intro hx
        exact ⟨(0, 1), rfl, x, hx, by simp⟩
      · rintro ⟨x₁, hx₁, x₂, hx₂, rfl⟩
        subst hx₁
        simpa using hx₂
  | cons p F₁ ih =>
      simp only [List.cons_append, mem_foldOutcomes_cons]
      constructor
      · rintro ⟨r, δ, rs, δ', hr, hrs, rfl⟩
        obtain ⟨x₁, hx₁, x₂, hx₂, heq⟩ := ih.mp hrs
        rw [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        exact ⟨(r ::ₘ x₁.1, δ * x₁.2), ⟨r, δ, x₁.1, x₁.2, hr, hx₁, rfl⟩, x₂, hx₂, by
          simp [mul_assoc]⟩
      · rintro ⟨x₁, ⟨r, δ, rs, δ', hr, hrs, rfl⟩, x₂, hx₂, rfl⟩
        exact ⟨r, δ, rs + x₂.1, δ' * x₂.2, hr, ih.mpr ⟨(rs, δ'), hrs, x₂, hx₂, rfl⟩, by
          simp [mul_assoc]⟩

omit [CommMonoid Δ] in
/-- Matchings are duplicate-free: pairwise compatibility is irreflexive. -/
theorem IsMatching.nodup {M : List (EventSkeleton R Δ Ω)} (h : IsMatching M) : M.Nodup := by
  induction M with
  | nil => exact List.nodup_nil
  | cons e M ih =>
      rcases List.pairwise_cons.mp h with ⟨hhead, htail⟩
      exact List.nodup_cons.mpr
        ⟨fun hmem => not_compatible_self e (hhead e hmem), ih htail⟩

/-! ### B4 — the round layer (static): choice over compatible matchings -/

/-- One-round outcomes of an enabled set: additive choice (⊔) over ALL compatible matchings, each
interpreted by the commuting ⊗-fold.  This is where contention becomes branching instead of an
impossible joint firing. -/
def roundOutcomes (E : Set (EventSkeleton R Δ Ω)) : Set (Multiset R × (Δ × ExportBag Ω)) :=
  ⋃ M ∈ MatchOf E, foldOutcomesΩ (matchingPayloads M)

/-- **The exact one-redex reducer is the finest refinement**: every single enabled event's fold
contributes to the round. -/
theorem singleton_step_embeds {E : Set (EventSkeleton R Δ Ω)} {e : EventSkeleton R Δ Ω}
    (he : e ∈ E) : foldOutcomesΩ [e.payload] ⊆ roundOutcomes E := fun _ hx =>
  Set.mem_biUnion (singleton_mem_matchOf he) hx

/-- **Collapse on an independent frontier**: when a selection of enabled events is pairwise
compatible, the full ⊗-fold over it is one of the round's branches. -/
theorem independent_unique_matching_collapses_to_fold {E : Set (EventSkeleton R Δ Ω)}
    {L : List (EventSkeleton R Δ Ω)} (hmem : ∀ e ∈ L, e ∈ E) (hpair : IsMatching L) :
    foldOutcomesΩ (matchingPayloads L) ⊆ roundOutcomes E := fun _ hx =>
  Set.mem_biUnion (⟨hmem, hpair⟩ : L ∈ MatchOf E) hx

/-- **Choice is semantically load-bearing** (corollary of the contention no-go): the round of a
contended pair never fires both events jointly — its outcomes carry at most one result — so it is
NOT the raw two-event fold, whose outcomes all carry two. -/
theorem roundOutcomes_ne_rawFold {e₁ e₂ : EventSkeleton R Δ Ω}
    (hsend : e₁.sendIdx = e₂.sendIdx)
    (h₁ : e₁.payload.Nonempty) (h₂ : e₂.payload.Nonempty) :
    roundOutcomes {e₁, e₂} ≠ foldOutcomesΩ [e₁.payload, e₂.payload] := by
  intro heq
  obtain ⟨x, hx⟩ : (foldOutcomesΩ [e₁.payload, e₂.payload]).Nonempty :=
    foldOutcomes_nonempty (by
      rintro p hp
      rcases List.mem_pair.mp hp with rfl | rfl
      · exact h₁
      · exact h₂)
  have hc2 : x.1.card = 2 := foldOutcomes_card x hx
  rw [← heq] at hx
  obtain ⟨_, ⟨M, rfl⟩, _, ⟨hM, rfl⟩, hxM⟩ := hx
  have hlen := matchOf_length_le_one_of_shared_send hsend M hM
  have hc1 : x.1.card = (matchingPayloads M).length := foldOutcomes_card x hxM
  rw [matchingPayloads, List.length_map] at hc1
  omega

end EventLayer

/-! ## Run layer — sequential closure of rounds and the two crowns

`EventSystem` is the abstract transactional machine: states expose enabled COMM candidates;
firing one event advances the state.  Its single law, `enabled_persist`, is the MODEL-structural
form of transactional non-interference: a compatible sibling survives a firing.  Payload outcome
sets are data attached to skeletons, so "copy-stable results" and "transactional payload
isolation" have no separate content at this layer — they are what makes an ENGINE step
instantiate this structure at all, and they are discharged at the operational bridge, not assumed
here.  Likewise the owned-export renaming obligation vanishes at this layer: exports are data
merged by bag union, so serializing a round needs no identity bookkeeping — fresh-identity
generation is an operational-bridge concern.

`runOutcomes` is the fuel-indexed sequential closure of rounds under a *policy* (which matchings
may fire): `singletonPol` is the exact one-redex reducer, `allPol` the free all-matchings base.

**Crown 1**, `round_granularity_independence`: the two closures reach exactly the same
configurations — bigger compatible rounds add nothing and lose nothing.  This is a statement
about the MODEL; citing it as an engine guarantee without Crown 2 is precisely the overclaim this
file is structured to prevent.

**Crown 2**, `macro_collapse_corollary`: under the explicit `QuietFrontier` hypotheses mirroring
the engine's macro side conditions — `matching` (no alternative pairing), `complete` (the macro
fires the whole frontier), `quiet_consume` (linear consumption and no new enablement: quiet
continuations) — the macro's one-shot outcome set IS the quiescent may-set of the full closure.
Each hypothesis corresponds to a C-side check in the correspondence table of the two-lane TODO
(docs/plans 2026-06-11); the conditions with no formal content here (copy-stability, payload
isolation) are exactly the engine's instance-hood obligations. -/
universe uR uΔ uΩ uS

section RunLayer

variable {R : Type uR} {Δ : Type uΔ} {Ω : Type uΩ} {S : Type uS} [CommMonoid Δ]

/-- A configuration: state plus accumulated observable (results, merged delta and exports). -/
abbrev Config (R Δ Ω S : Type*) := S × (Multiset R × (Δ × ExportBag Ω))

/-- Merge accumulated observables: results append, deltas and export bags multiply. -/
def accMul (x y : Multiset R × (Δ × ExportBag Ω)) : Multiset R × (Δ × ExportBag Ω) :=
  (x.1 + y.1, x.2 * y.2)

theorem accMul_assoc (x y z : Multiset R × (Δ × ExportBag Ω)) :
    accMul (accMul x y) z = accMul x (accMul y z) := by
  simp [accMul, add_assoc, mul_assoc]

@[simp] theorem accMul_one (x : Multiset R × (Δ × ExportBag Ω)) :
    accMul x (0, 1) = x := by
  simp [accMul]

/-- A realized payload outcome of one event. -/
abbrev EventOutcome (e : EventSkeleton R Δ Ω) := {o : R × (Δ × ExportBag Ω) // o ∈ e.payload}

/-- One concrete payload outcome choice for each event of a matching, in list order. -/
def MatchingRealization :
    List (EventSkeleton R Δ Ω) → Type (max (max uR uΔ) uΩ)
  | [] => PUnit
  | e :: M => EventOutcome e ×
      MatchingRealization M

namespace MatchingRealization

/-- The observable contributed by one realized event. -/
def singletonObs {e : EventSkeleton R Δ Ω} (o : EventOutcome e) :
    Multiset R × (Δ × ExportBag Ω) :=
  ({o.1.1}, o.1.2)

/-- Aggregate observable of a realized matching. -/
def aggregate : {M : List (EventSkeleton R Δ Ω)} →
    MatchingRealization M →
    Multiset R × (Δ × ExportBag Ω)
  | [], _ => (0, 1)
  | _ :: _, (o, ρ) => accMul (singletonObs o)
      (aggregate ρ)

/-- Concatenate realized outcomes along list append. -/
def append : {L M : List (EventSkeleton R Δ Ω)} →
    MatchingRealization L →
    MatchingRealization M →
    MatchingRealization (L ++ M)
  | [], _, _, ρ₂ => ρ₂
  | _ :: _, _, (o, ρ₁), ρ₂ => (o, append ρ₁ ρ₂)

@[simp] theorem aggregate_nil :
    aggregate (M := []) PUnit.unit = ((0 : Multiset R), (1 : Δ × ExportBag Ω)) := rfl

@[simp] theorem aggregate_singleton {e : EventSkeleton R Δ Ω}
    (o : EventOutcome e) :
    aggregate (M := [e]) (o, PUnit.unit) =
      singletonObs o := by
  simp [aggregate, singletonObs, accMul]

theorem aggregate_mem_foldOutcomesΩ :
    ∀ {M : List (EventSkeleton R Δ Ω)}
      (ρ : MatchingRealization M),
      aggregate ρ ∈ foldOutcomesΩ (matchingPayloads M)
  | [], _ => by
      simp [aggregate, matchingPayloads, foldOutcomesΩ, foldOutcomes]
  | _ :: _, (o, ρ) => by
      simp only [matchingPayloads, List.map_cons, foldOutcomesΩ]
      refine mem_foldOutcomes_cons.mpr ?_
      exact ⟨o.1.1, o.1.2,
        (aggregate ρ).1,
        (aggregate ρ).2,
        o.2, aggregate_mem_foldOutcomesΩ ρ, rfl⟩

theorem exists_of_mem_foldOutcomesΩ :
    ∀ {M : List (EventSkeleton R Δ Ω)} {x : Multiset R × (Δ × ExportBag Ω)},
      x ∈ foldOutcomesΩ (matchingPayloads M) →
      ∃ ρ : MatchingRealization M,
        aggregate ρ = x
  | [], x, hx => by
      simp only [matchingPayloads, foldOutcomesΩ] at hx
      subst hx
      exact ⟨PUnit.unit, rfl⟩
  | _ :: _, x, hx => by
      simp only [matchingPayloads, List.map_cons, foldOutcomesΩ] at hx
      rw [mem_foldOutcomes_cons] at hx
      obtain ⟨r, δω, rs, δω', ho, hrest, rfl⟩ := hx
      obtain ⟨ρ, hρ⟩ := exists_of_mem_foldOutcomesΩ hrest
      refine ⟨⟨⟨(r, δω), ho⟩, ρ⟩, ?_⟩
      simp [aggregate, singletonObs, accMul, hρ]

theorem aggregate_append :
    ∀ {L M : List (EventSkeleton R Δ Ω)}
      (ρ₁ : MatchingRealization L)
      (ρ₂ : MatchingRealization M),
      aggregate (append ρ₁ ρ₂) =
        accMul (aggregate ρ₁)
          (aggregate ρ₂)
  | [], _, _, ρ₂ => by
      simp [append, aggregate, accMul]
  | _ :: _, _, (o, ρ₁), ρ₂ => by
      simp [append, aggregate, aggregate_append ρ₁ ρ₂, accMul_assoc]

end MatchingRealization

/-- An abstract transactional event system: states expose enabled COMM candidates; firing one
event advances the state, possibly depending on WHICH payload outcome of that event was chosen.
`enabled_persist` is the model-structural form of transactional non-interference: a compatible
sibling survives a firing, for every realized outcome of the fired event. -/
structure EventSystem (R Δ Ω : Type*) (S : Type*) where
  enabled : S → Set (EventSkeleton R Δ Ω)
  fireOne :
    (s : S) → (e : EventSkeleton R Δ Ω) →
      EventOutcome e → S
  enabled_persist :
    ∀ s e x e', e ∈ enabled s → e' ∈ enabled s → Compatible e' e →
      e' ∈ enabled (fireOne s e x)

/-- Fire a realized matching's events in list order (the reference serialization). -/
def EventSystem.fireMany (sys : EventSystem R Δ Ω S) (s : S) :
    (M : List (EventSkeleton R Δ Ω)) →
    MatchingRealization M → S
  | [], _ => s
  | e :: M, (o, ρ) => sys.fireMany (sys.fireOne s e o) M ρ

omit [CommMonoid Δ] in
@[simp] theorem EventSystem.fireMany_nil (sys : EventSystem R Δ Ω S) (s : S) :
    sys.fireMany s [] PUnit.unit = s := rfl

omit [CommMonoid Δ] in
@[simp] theorem EventSystem.fireMany_cons (sys : EventSystem R Δ Ω S) (s : S)
    (e : EventSkeleton R Δ Ω)
    (o : EventOutcome e)
    (M : List (EventSkeleton R Δ Ω))
    (ρ : MatchingRealization M) :
    sys.fireMany s (e :: M) (o, ρ) = sys.fireMany (sys.fireOne s e o) M ρ := rfl

omit [CommMonoid Δ] in
@[simp] theorem EventSystem.fireMany_singleton (sys : EventSystem R Δ Ω S) (s : S)
    (e : EventSkeleton R Δ Ω)
    (o : EventOutcome e) :
    sys.fireMany s [e] (o, PUnit.unit) = sys.fireOne s e o := rfl

omit [CommMonoid Δ] in
theorem EventSystem.fireMany_append (sys : EventSystem R Δ Ω S) :
    ∀ (s : S) (L : List (EventSkeleton R Δ Ω))
      (ρL : MatchingRealization L)
      (M : List (EventSkeleton R Δ Ω))
      (ρM : MatchingRealization M),
      sys.fireMany s (L ++ M)
          (MatchingRealization.append ρL ρM) =
        sys.fireMany (sys.fireMany s L ρL) M ρM
  | s, [], _, M, ρM => rfl
  | s, _ :: _, (o, ρL), M, ρM => by
      simpa [EventSystem.fireMany, MatchingRealization.append] using
        EventSystem.fireMany_append sys (sys.fireOne s _ o) _ ρL M ρM

omit [CommMonoid Δ] in
/-- Firing one event of a matching keeps the rest a matching of the new state — the persistence
law, in the form the serialization induction consumes. -/
theorem matchOf_tail_fireOne (sys : EventSystem R Δ Ω S) {s : S} {e : EventSkeleton R Δ Ω}
    (o : EventOutcome e)
    {M : List (EventSkeleton R Δ Ω)} (h : (e :: M) ∈ MatchOf (sys.enabled s)) :
    M ∈ MatchOf (sys.enabled (sys.fireOne s e o)) := by
  obtain ⟨hmem, hpair⟩ := h
  rcases List.pairwise_cons.mp hpair with ⟨hhead, htail⟩
  refine ⟨fun a ha => ?_, htail⟩
  exact sys.enabled_persist s e o a (hmem e (by simp)) (hmem a (by simp [ha]))
    ((hhead a ha).symm)

/-- One round under a policy: fire a permitted matching of the enabled set, in list order,
accumulating the aggregate observable of one concrete per-event realization. -/
inductive RoundStep (sys : EventSystem R Δ Ω S)
    (pol : List (EventSkeleton R Δ Ω) → Prop) :
    Config R Δ Ω S → Config R Δ Ω S → Prop
  | fire {s : S} {acc : Multiset R × (Δ × ExportBag Ω)}
      {M : List (EventSkeleton R Δ Ω)}
      (hpol : pol M) (hM : M ∈ MatchOf (sys.enabled s))
      (ρ : MatchingRealization M) :
      RoundStep sys pol (s, acc)
        (sys.fireMany s M ρ,
          accMul acc (MatchingRealization.aggregate ρ))

/-- The exact policy: one event per round (the one-redex reducer). -/
def singletonPol (M : List (EventSkeleton R Δ Ω)) : Prop := M.length = 1

/-- The free policy: any compatible matching. -/
def allPol (_ : List (EventSkeleton R Δ Ω)) : Prop := True

/-- Fuel-indexed sequential closure: configurations reachable in at most `n` rounds. -/
def runOutcomes (sys : EventSystem R Δ Ω S) (pol : List (EventSkeleton R Δ Ω) → Prop) :
    ℕ → Config R Δ Ω S → Set (Config R Δ Ω S)
  | 0, c => {c}
  | n + 1, c => {c} ∪ ⋃ c' ∈ {c' | RoundStep sys pol c c'}, runOutcomes sys pol n c'

theorem self_mem_runOutcomes (sys : EventSystem R Δ Ω S) (pol) (n : ℕ)
    (c : Config R Δ Ω S) : c ∈ runOutcomes sys pol n c := by
  cases n <;> simp [runOutcomes]

theorem runOutcomes_succ_of_step (sys : EventSystem R Δ Ω S) {pol} {n : ℕ}
    {c d c' : Config R Δ Ω S} (hstep : RoundStep sys pol c d)
    (h : c' ∈ runOutcomes sys pol n d) : c' ∈ runOutcomes sys pol (n + 1) c := by
  simp only [runOutcomes, Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq]
  exact Or.inr ⟨d, hstep, h⟩

theorem runOutcomes_mono_fuel (sys : EventSystem R Δ Ω S) (pol) :
    ∀ {n : ℕ} {c c' : Config R Δ Ω S},
      c' ∈ runOutcomes sys pol n c → c' ∈ runOutcomes sys pol (n + 1) c := by
  intro n
  induction n with
  | zero =>
      intro c c' h
      rw [Set.mem_singleton_iff.mp h]
      exact self_mem_runOutcomes sys pol 1 c
  | succ n ih =>
      intro c c' h
      simp only [runOutcomes, Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq] at h
      rcases h with h | ⟨d, hd, hrest⟩
      · rw [Set.mem_singleton_iff.mp h]
        exact self_mem_runOutcomes sys pol (n + 2) c
      · exact runOutcomes_succ_of_step sys hd (ih hrest)

theorem runOutcomes_le (sys : EventSystem R Δ Ω S) (pol) {m k : ℕ} (hmk : m ≤ k) :
    ∀ {c c' : Config R Δ Ω S},
      c' ∈ runOutcomes sys pol m c → c' ∈ runOutcomes sys pol k c := by
  induction hmk with
  | refl => intro c c' h; exact h
  | step _ ih => intro c c' h; exact runOutcomes_mono_fuel sys pol (ih h)

theorem runOutcomes_trans (sys : EventSystem R Δ Ω S) (pol) :
    ∀ {n m : ℕ} {c c' c'' : Config R Δ Ω S},
      c' ∈ runOutcomes sys pol n c → c'' ∈ runOutcomes sys pol m c' →
      c'' ∈ runOutcomes sys pol (n + m) c := by
  intro n
  induction n with
  | zero =>
      intro m c c' c'' h h'
      rw [Set.mem_singleton_iff.mp h] at h'
      exact runOutcomes_le sys pol (by omega) h'
  | succ n ih =>
      intro m c c' c'' h h'
      simp only [runOutcomes, Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq] at h
      rcases h with h | ⟨d, hd, hrest⟩
      · rw [Set.mem_singleton_iff.mp h] at h'
        exact runOutcomes_le sys pol (by omega) h'
      · have heq : n + 1 + m = (n + m) + 1 := by omega
        rw [heq]
        exact runOutcomes_succ_of_step sys hd (ih hrest h')

theorem runOutcomes_mono_pol (sys : EventSystem R Δ Ω S)
    {pol₁ pol₂ : List (EventSkeleton R Δ Ω) → Prop} (hpol : ∀ M, pol₁ M → pol₂ M) :
    ∀ {n : ℕ} {c c' : Config R Δ Ω S},
      c' ∈ runOutcomes sys pol₁ n c → c' ∈ runOutcomes sys pol₂ n c := by
  intro n
  induction n with
  | zero => intro c c' h; exact h
  | succ n ih =>
      intro c c' h
      simp only [runOutcomes, Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq] at h
      rcases h with h | ⟨d, hd, hrest⟩
      · rw [Set.mem_singleton_iff.mp h]
        exact self_mem_runOutcomes sys pol₂ (n + 1) c
      · refine runOutcomes_succ_of_step sys ?_ (ih hrest)
        cases hd with
        | fire hp hM ρ => exact RoundStep.fire (hpol _ hp) hM ρ

/-- **Serialization**: a matching round decomposes into singleton rounds — same final state (the
round's own list order) and same accumulated observable, by the per-payload structure of the
⊗-fold.  Note: no export renaming is needed — exports are data merged by bag union at this layer. -/
theorem singleton_run_of_matching (sys : EventSystem R Δ Ω S) :
    ∀ (M : List (EventSkeleton R Δ Ω)) (s : S) (acc)
      (ρ : MatchingRealization M),
      M ∈ MatchOf (sys.enabled s) →
      (sys.fireMany s M ρ,
        accMul acc (MatchingRealization.aggregate ρ)) ∈
          runOutcomes sys singletonPol M.length (s, acc)
  | [], s, acc, ρ, _ => by
      cases ρ
      simpa [EventSystem.fireMany, MatchingRealization.aggregate, accMul] using
        self_mem_runOutcomes sys singletonPol 0 (s, acc)
  | e :: M, s, acc, (o, ρ), hM => by
      let ρ₁ :
          MatchingRealization [e] := (o, PUnit.unit)
      have hstep : RoundStep sys singletonPol (s, acc)
          (sys.fireMany s [e] ρ₁,
            accMul acc (MatchingRealization.aggregate ρ₁)) :=
        RoundStep.fire (by simp [singletonPol])
          (singleton_mem_matchOf (hM.1 e (by simp)))
          ρ₁
      have hrest' := singleton_run_of_matching sys M (sys.fireOne s e o)
        (accMul acc (MatchingRealization.aggregate ρ₁))
        ρ (matchOf_tail_fireOne sys o hM)
      simpa [EventSystem.fireMany, MatchingRealization.aggregate, ρ₁,
          MatchingRealization.singletonObs, accMul_assoc] using
        (runOutcomes_succ_of_step sys hstep hrest')

/-- Any free-policy round decomposes into a singleton run. -/
theorem roundStep_decomposes (sys : EventSystem R Δ Ω S) {c c' : Config R Δ Ω S}
    (h : RoundStep sys allPol c c') :
    ∃ n, c' ∈ runOutcomes sys singletonPol n c := by
  cases h with
  | fire hpol hM ρ => exact ⟨_, singleton_run_of_matching sys _ _ _ ρ hM⟩

/-- **Crown 1 — round-granularity independence (abstract).**  The all-matchings closure and the
singleton-only closure reach exactly the same configurations: bigger compatible rounds add
nothing and lose nothing.  This is a statement about the MODEL — payload non-interference is
structural here (payload outcome sets are fixed data, and `enabled_persist` is assumed) — and it
must NOT be cited as an engine guarantee on its own: the engine instantiates it only under the
macro side conditions, which is `macro_collapse_corollary` below. -/
theorem round_granularity_independence (sys : EventSystem R Δ Ω S) (c : Config R Δ Ω S) :
    {c' | ∃ n, c' ∈ runOutcomes sys allPol n c} =
    {c' | ∃ n, c' ∈ runOutcomes sys singletonPol n c} := by
  ext c'
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨n, hn⟩
    induction n generalizing c with
    | zero => exact ⟨0, hn⟩
    | succ n ih =>
        simp only [runOutcomes, Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq] at hn
        rcases hn with h | ⟨d, hd, hrest⟩
        · exact ⟨0, h⟩
        · obtain ⟨m₁, h₁⟩ := roundStep_decomposes sys hd
          obtain ⟨m₂, h₂⟩ := ih d hrest
          exact ⟨m₁ + m₂, runOutcomes_trans sys singletonPol h₁ h₂⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, runOutcomes_mono_pol sys (fun _ _ => trivial) hn⟩

/-- Quiescent corollary of Crown 1: the quiescent may-sets of the two closures agree. -/
theorem quiescent_granularity_independence (sys : EventSystem R Δ Ω S)
    (c : Config R Δ Ω S) :
    {c' | (∃ n, c' ∈ runOutcomes sys allPol n c) ∧ sys.enabled c'.1 = ∅} =
    {c' | (∃ n, c' ∈ runOutcomes sys singletonPol n c) ∧ sys.enabled c'.1 = ∅} := by
  have h := Set.ext_iff.mp (round_granularity_independence sys c)
  ext c'
  simp only [Set.mem_setOf_eq] at h ⊢
  exact ⟨fun ⟨a, b⟩ => ⟨(h c').mp a, b⟩, fun ⟨a, b⟩ => ⟨(h c').mpr a, b⟩⟩

/-- **The engine macro side conditions, as explicit model hypotheses.**  Each field corresponds
to a C-side check (correspondence table, docs/plans 2026-06-11): `matching` ↔ keywise at-most-one
pairing (no contention); `complete` ↔ the macro fires the whole frontier; `quiet_consume` ↔ quiet
continuations + linear consumption (fired events leave, nothing new is exposed, compatible
siblings persist — one equation).  Copy-stable results and transactional payload isolation have
no separate content at this layer (payload outcome sets are fixed data on skeletons); they are
the engine's instance-hood obligations, discharged at the operational bridge. -/
structure QuietFrontier (sys : EventSystem R Δ Ω S) (s : S)
    (M : List (EventSkeleton R Δ Ω)) : Prop where
  matching : M ∈ MatchOf (sys.enabled s)
  complete : ∀ e ∈ sys.enabled s, e ∈ M
  quiet_consume : ∀ (L : List (EventSkeleton R Δ Ω))
      (ρ : MatchingRealization L),
      L.Nodup → (∀ e ∈ L, e ∈ M) →
        sys.enabled (sys.fireMany s L ρ) = {e | e ∈ sys.enabled s ∧ e ∉ L}

/-- Shape invariant of singleton runs under a quiet frontier: every reachable configuration is
"some duplicate-free part `L'` of the frontier fired, with a fold outcome of `L'` accumulated". -/
theorem QuietFrontier.singleton_run_shape {sys : EventSystem R Δ Ω S} {s : S}
    {M : List (EventSkeleton R Δ Ω)} (h : QuietFrontier sys s M)
    (acc : Multiset R × (Δ × ExportBag Ω)) :
    ∀ {n : ℕ} {L : List (EventSkeleton R Δ Ω)}
      (ρ : MatchingRealization L)
      {c' : Config R Δ Ω S},
      L.Nodup → (∀ e ∈ L, e ∈ M) →
      c' ∈ runOutcomes sys singletonPol n
        (sys.fireMany s L ρ,
          accMul acc (MatchingRealization.aggregate ρ)) →
      ∃ L' : List (EventSkeleton R Δ Ω),
        ∃ ρ' : MatchingRealization L',
          L'.Nodup ∧ (∀ e ∈ L', e ∈ M) ∧
            c'.1 = sys.fireMany s L' ρ' ∧
            c'.2 = accMul acc (MatchingRealization.aggregate ρ') := by
  intro n
  induction n with
  | zero =>
      rintro L ρ c' hnd hsub hc'
      rw [Set.mem_singleton_iff.mp hc']
      exact ⟨L, ρ, hnd, hsub, rfl, rfl⟩
  | succ n ih =>
      rintro L ρ c' hnd hsub hc'
      simp only [runOutcomes, Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq] at hc'
      rcases hc' with hc' | ⟨d, hd, hrest⟩
      · rw [Set.mem_singleton_iff.mp hc']
        exact ⟨L, ρ, hnd, hsub, rfl, rfl⟩
      · cases hd with
        | @fire _ _ M₀ hpol hM ρ₀ =>
          obtain ⟨e, rfl⟩ : ∃ a, M₀ = [a] := by
            rcases M₀ with _ | ⟨a, _ | ⟨b, l⟩⟩
            · exfalso; simp only [singletonPol, List.length_nil] at hpol; omega
            · exact ⟨a, rfl⟩
            · exfalso; simp only [singletonPol, List.length_cons] at hpol; omega
          rcases ρ₀ with ⟨o, ρnil⟩
          cases ρnil
          let ρ₁ :
              MatchingRealization [e] := (o, PUnit.unit)
          have he : e ∈ sys.enabled (sys.fireMany s L ρ) := hM.1 e (by simp)
          rw [h.quiet_consume L ρ hnd hsub] at he
          have heM : e ∈ M := h.complete e he.1
          have hLe_nodup : (L ++ [e]).Nodup := by
            refine List.Nodup.append hnd (List.nodup_singleton e) ?_
            intro a haL hae
            exact he.2 ((List.mem_singleton.mp hae) ▸ haL)
          have hLe_sub : ∀ a ∈ L ++ [e], a ∈ M := by
            intro a ha
            rcases List.mem_append.mp ha with ha | ha
            · exact hsub a ha
            · rw [List.mem_singleton.mp ha]; exact heM
          let ρLe :
              MatchingRealization (L ++ [e]) :=
                MatchingRealization.append ρ ρ₁
          have hstate :
              sys.fireMany (sys.fireMany s L ρ) [e] ρ₁ =
                sys.fireMany s (L ++ [e]) ρLe := by
            simpa [ρLe, ρ₁] using
              (EventSystem.fireMany_append sys s L ρ [e] ρ₁).symm
          have hacc :
              accMul
                (accMul acc (MatchingRealization.aggregate ρ))
                (MatchingRealization.aggregate ρ₁) =
              accMul acc (MatchingRealization.aggregate ρLe) := by
            dsimp [ρLe]
            rw [MatchingRealization.aggregate_append]
            exact accMul_assoc acc (MatchingRealization.aggregate ρ)
              (MatchingRealization.aggregate ρ₁)
          have hd_eq : ((sys.fireMany (sys.fireMany s L ρ) [e] ρ₁,
              accMul
                (accMul acc (MatchingRealization.aggregate ρ))
                (MatchingRealization.aggregate ρ₁)) :
              Config R Δ Ω S) =
              (sys.fireMany s (L ++ [e]) ρLe,
                accMul acc (MatchingRealization.aggregate ρLe)) :=
            Prod.ext hstate hacc
          rw [hd_eq] at hrest
          exact ih ρLe hLe_nodup hLe_sub hrest

/-- **Crown 2 — the engine macro-collapse corollary.**  Under the explicit `QuietFrontier`
hypotheses (the engine's macro side conditions), the macro's one-shot outcome set IS the
quiescent may-set of the full all-matchings closure: macro-firing the frontier is semantically
invisible.  This — not Crown 1 alone — is the statement the engine may cite: Crown 1 supplies
the model fact, this corollary supplies the instance-hood under the named conditions. -/
theorem macro_collapse_corollary (sys : EventSystem R Δ Ω S) {s : S}
    {M : List (EventSkeleton R Δ Ω)} (h : QuietFrontier sys s M)
    (acc : Multiset R × (Δ × ExportBag Ω)) :
    {acc' | ∃ s', (∃ n, (s', acc') ∈ runOutcomes sys allPol n (s, acc)) ∧
        sys.enabled s' = ∅} =
    {acc' | ∃ x ∈ foldOutcomesΩ (matchingPayloads M), acc' = accMul acc x} := by
  ext acc'
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨s', ⟨n, hn⟩, hq⟩
    have h1 : ((s', acc') : Config R Δ Ω S) ∈
        {c' | ∃ n, c' ∈ runOutcomes sys singletonPol n (s, acc)} := by
      rw [← round_granularity_independence sys (s, acc)]
      exact ⟨n, hn⟩
    obtain ⟨m, hm⟩ := h1
    let ρ₀ : MatchingRealization ([] : List (EventSkeleton R Δ Ω)) := PUnit.unit
    have hbase : ((s, acc) : Config R Δ Ω S) =
        (sys.fireMany s [] ρ₀,
          accMul acc (MatchingRealization.aggregate ρ₀)) := by
      cases ρ₀
      simp [EventSystem.fireMany, MatchingRealization.aggregate, accMul]
    rw [hbase] at hm
    obtain ⟨L', ρ', hnd, hsub, hs', hacc'⟩ :=
      h.singleton_run_shape acc ρ₀ List.nodup_nil (by simp) hm
    have hempty : {e | e ∈ sys.enabled s ∧ e ∉ L'} = (∅ : Set (EventSkeleton R Δ Ω)) := by
      rw [← h.quiet_consume L' ρ' hnd hsub, ← hs', hq]
    have hML' : ∀ e ∈ M, e ∈ L' := by
      intro e heM
      by_contra hnot
      have : e ∈ {e | e ∈ sys.enabled s ∧ e ∉ L'} := ⟨h.matching.1 e heM, hnot⟩
      rw [hempty] at this
      exact this
    have hperm : L'.Perm M :=
      (hnd.subperm hsub).antisymm ((h.matching.2.nodup).subperm hML')
    have hfold : foldOutcomesΩ (matchingPayloads L') = foldOutcomesΩ (matchingPayloads M) :=
      foldOutcomesΩ_perm (hperm.map _)
    exact ⟨MatchingRealization.aggregate ρ',
      hfold ▸ MatchingRealization.aggregate_mem_foldOutcomesΩ (R := R) (Δ := Δ) (Ω := Ω) ρ',
      hacc'⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨ρ, rfl⟩ :=
      MatchingRealization.exists_of_mem_foldOutcomesΩ (R := R) (Δ := Δ) (Ω := Ω) hx
    refine ⟨sys.fireMany s M ρ, ⟨1, ?_⟩, ?_⟩
    · exact runOutcomes_succ_of_step sys (RoundStep.fire trivial h.matching ρ)
        (self_mem_runOutcomes sys allPol 0 _)
    · rw [h.quiet_consume M ρ h.matching.2.nodup (fun _ he => he)]
      ext e
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_not]
      exact fun hes => h.complete e hes

end RunLayer

/-! ## Concrete bridge seed: the eval-drop shell as a real EventSystem

This is not yet the full B7 operational instance.  It is the first honest concrete slice: the
live `evalDropSource` shell already exhibits the outcome-sensitive seam the repaired run layer was
built for.  We package that shell as a genuine `EventSystem`, prove it is non-vacuous, and show
its quiescent may-set collapses to the singleton fold of the certified payload outcomes.  This is
the minimal concrete bridge object that later generalization to arbitrary Rhometta frontiers must
conservatively extend. -/
section EvalDropRunBridge

local instance : CommMonoid Unit where
  mul _ _ := ()
  mul_assoc _ _ _ := rfl
  one := ()
  one_mul _ := rfl
  mul_one _ := rfl
  mul_comm _ _ := rfl

/-- The one enabled event of the drop-observer shell: one fixed send/receive pair whose payload
outcomes are exactly the certified operational results, already reified. -/
def evalDropEvent
    (space : Space) (dispatch : GroundedDispatch) (payload : Atom) :
    EventSkeleton Atom Unit Empty where
  sendIdx := 0
  recvIdx := 1
  payload := certifiedPayloadReified space dispatch payload

/-- Concrete enabled frontier for the drop-observer shell: the source exposes the one COMM
candidate exactly when its certified payload frontier is nonempty, and every other state in this
slice exposes none. -/
noncomputable def evalDropEnabled
    (space : Space) (dispatch : GroundedDispatch)
    (chan : Pattern) (payload : Atom) :
    Pattern → Set (EventSkeleton Atom Unit Empty) := fun s => by
      classical
      exact
      if hs : s = evalDropSource chan payload then
        if (certifiedPayloadReified space dispatch payload).Nonempty then
          {evalDropEvent space dispatch payload}
        else
          ∅
      else
        ∅

theorem evalDropSource_ne_evalDropResidual
    (chan : Pattern) (payload value : Atom) :
    evalDropSource chan payload ≠ evalDropResidual value := by
  intro h
  have hlen := congrArg
    (fun p =>
      match p with
      | .collection .hashBag elems none => elems.length
      | _ => 0) h
  simp [evalDropSource, evalSource, evalDropResidual] at hlen

theorem evalDropResidual_ne_evalDropSource
    (chan : Pattern) (payload value : Atom) :
    evalDropResidual value ≠ evalDropSource chan payload := by
  intro h
  exact evalDropSource_ne_evalDropResidual chan payload value h.symm

theorem evalDropEnabled_source_of_nonempty
    (space : Space) (dispatch : GroundedDispatch)
    (chan : Pattern) (payload : Atom)
    (hready : (certifiedPayloadReified space dispatch payload).Nonempty) :
    evalDropEnabled space dispatch chan payload (evalDropSource chan payload) =
      {evalDropEvent space dispatch payload} := by
  classical
  simp [evalDropEnabled, hready]

theorem evalDropEnabled_source_of_certified
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload value : Atom}
    (hcert : CertifiedPayloadResult space dispatch payload value) :
    evalDropEnabled space dispatch chan payload (evalDropSource chan payload) =
      {evalDropEvent space dispatch payload} := by
  exact evalDropEnabled_source_of_nonempty
    space dispatch chan payload
    ((certifiedPayloadReified_nonempty_iff
      (space := space) (dispatch := dispatch) (payload := payload)).2
      ⟨value, hcert⟩)

theorem evalDropEnabled_source_of_empty
    (space : Space) (dispatch : GroundedDispatch)
    (chan : Pattern) (payload : Atom)
    (hempty : ¬ (certifiedPayloadReified space dispatch payload).Nonempty) :
    evalDropEnabled space dispatch chan payload (evalDropSource chan payload) = ∅ := by
  classical
  simp [evalDropEnabled, hempty]

@[simp] theorem evalDropEnabled_residual
    (space : Space) (dispatch : GroundedDispatch)
    (chan : Pattern) (payload value : Atom) :
    evalDropEnabled space dispatch chan payload (evalDropResidual value) = ∅ := by
  simp [evalDropEnabled, evalDropResidual_ne_evalDropSource]

/-- Concrete `EventSystem` on the live drop-observer shell.  The only enabled COMM candidate is
the deferred-payload rendezvous; firing it picks one certified payload result and moves to the
corresponding residual. -/
def evalDropSystem
    (space : Space) (dispatch : GroundedDispatch)
    (chan : Pattern) (payload : Atom) :
    EventSystem Atom Unit Empty Pattern where
  enabled := evalDropEnabled space dispatch chan payload
  fireOne := fun _ _ o => evalDropResidual o.1.1
  enabled_persist := by
    intro s e x e' he he' hcompat
    by_cases hs : s = evalDropSource chan payload
    · by_cases hready : (certifiedPayloadReified space dispatch payload).Nonempty
      · simp [evalDropEnabled, hs, hready] at he he'
        subst e
        subst e'
        exact False.elim (not_compatible_self _ hcompat)
      · simp [evalDropEnabled, hs, hready] at he
    · simp [evalDropEnabled, hs] at he

theorem evalDropEvent_mem_enabled_source
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload : Atom}
    (hready : (certifiedPayloadReified space dispatch payload).Nonempty) :
    evalDropEvent space dispatch payload ∈
      (evalDropSystem space dispatch chan payload).enabled
        (evalDropSource chan payload) := by
  simp [evalDropSystem, evalDropEnabled, hready]

theorem evalDropEvent_mem_enabled_source_of_certified
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload value : Atom}
    (hcert : CertifiedPayloadResult space dispatch payload value) :
    evalDropEvent space dispatch payload ∈
      (evalDropSystem space dispatch chan payload).enabled
        (evalDropSource chan payload) := by
  exact evalDropEvent_mem_enabled_source
    ((certifiedPayloadReified_nonempty_iff
      (space := space) (dispatch := dispatch) (payload := payload)).2
      ⟨value, hcert⟩)

private theorem matchOf_empty_nil
    {R Δ Ω : Type*} {M : List (EventSkeleton R Δ Ω)}
    (hM : M ∈ MatchOf (∅ : Set (EventSkeleton R Δ Ω))) :
    M = [] := by
  cases M with
  | nil =>
      rfl
  | cons e rest =>
      exfalso
      have : e ∈ (∅ : Set (EventSkeleton R Δ Ω)) := hM.1 e (by simp)
      simp at this

private theorem evalDropSystem_roundStep_source_eq_self_of_empty
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload : Atom}
    {acc : Multiset Atom × (Unit × ExportBag Empty)}
    {d : Config Atom Unit Empty Pattern}
    (hempty : ¬ (certifiedPayloadReified space dispatch payload).Nonempty)
    (hstep :
      RoundStep (evalDropSystem space dispatch chan payload) allPol
        (evalDropSource chan payload, acc) d) :
    d = (evalDropSource chan payload, acc) := by
  cases hstep with
  | @fire s acc M hpol hM ρ =>
      have henabled :
          (evalDropSystem space dispatch chan payload).enabled
            (evalDropSource chan payload) = ∅ := by
        simp [evalDropSystem, evalDropEnabled, hempty]
      have hnil : M = [] := by
        apply matchOf_empty_nil
        simpa [henabled] using hM
      subst hnil
      cases ρ
      simp [EventSystem.fireMany, MatchingRealization.aggregate, accMul]

private theorem evalDropSystem_runOutcomes_source_eq_self_of_empty
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload : Atom}
    {acc : Multiset Atom × (Unit × ExportBag Empty)}
    (hempty : ¬ (certifiedPayloadReified space dispatch payload).Nonempty) :
    ∀ n,
      runOutcomes (evalDropSystem space dispatch chan payload) allPol n
        (evalDropSource chan payload, acc) =
      {(evalDropSource chan payload, acc)} := by
  intro n
  induction n with
  | zero =>
      simp [runOutcomes]
  | succ n ih =>
      ext d
      constructor
      · intro hd
        simp only [runOutcomes, Set.mem_union, Set.mem_singleton_iff,
          Set.mem_iUnion, Set.mem_setOf_eq] at hd
        rcases hd with hd | ⟨d', hstep, hd'⟩
        · simpa using hd
        · have hdself : d' = (evalDropSource chan payload, acc) :=
              evalDropSystem_roundStep_source_eq_self_of_empty hempty hstep
          subst hdself
          simpa [ih] using hd'
      · intro hd
        have hdself : d = (evalDropSource chan payload, acc) :=
          Set.mem_singleton_iff.mp hd
        subst hdself
        exact self_mem_runOutcomes
          (evalDropSystem space dispatch chan payload) allPol (n + 1)
          (evalDropSource chan payload, acc)

@[simp] theorem evalDropSystem_enabled_residual_empty
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload value : Atom} :
    (evalDropSystem space dispatch chan payload).enabled
      (evalDropResidual value) = ∅ := by
  simp [evalDropSystem]

/-- Non-vacuity witness for the concrete drop-shell instance: the enabled frontier is genuinely
nonempty at the source, and any certified payload result fires to a DIFFERENT state. -/
theorem evalDropSystem_nonvacuous
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload value : Atom}
    (hcert : CertifiedPayloadResult space dispatch payload value) :
    let sys := evalDropSystem space dispatch chan payload
    let e := evalDropEvent space dispatch payload
    e ∈ sys.enabled (evalDropSource chan payload) ∧
      sys.fireOne (evalDropSource chan payload) e
        ⟨(value, ((), (1 : ExportBag Empty))),
          certifiedPayloadReified_mem_of_certified hcert⟩
        ≠ evalDropSource chan payload := by
  dsimp
  constructor
  · exact evalDropEvent_mem_enabled_source_of_certified hcert
  · exact evalDropResidual_ne_evalDropSource chan payload value

/-- A concrete certified operational result yields a singleton abstract run in the drop-shell
instance.  This is the first direct bridge theorem from certified operational evidence into the
repaired `runOutcomes` layer. -/
theorem evalDropSystem_singleton_run_of_certified
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload value : Atom}
    (hcert : CertifiedPayloadResult space dispatch payload value) :
    ((evalDropResidual value,
        (({value} : Multiset Atom), ((), (1 : ExportBag Empty)))) :
      Config Atom Unit Empty Pattern) ∈
      runOutcomes (evalDropSystem space dispatch chan payload) singletonPol 1
        (evalDropSource chan payload,
          ((0 : Multiset Atom), (1 : Unit × ExportBag Empty))) := by
  let sys := evalDropSystem space dispatch chan payload
  let e : EventSkeleton Atom Unit Empty := evalDropEvent space dispatch payload
  let o : EventOutcome e :=
    ⟨(value, ((), (1 : ExportBag Empty))),
      certifiedPayloadReified_mem_of_certified hcert⟩
  have hstep :
      RoundStep sys singletonPol
        (evalDropSource chan payload,
          ((0 : Multiset Atom), (1 : Unit × ExportBag Empty)))
        (sys.fireMany (evalDropSource chan payload) [e] (o, PUnit.unit),
          accMul ((0 : Multiset Atom), (1 : Unit × ExportBag Empty))
            (MatchingRealization.aggregate (M := [e]) (o, PUnit.unit))) :=
    RoundStep.fire (by simp [singletonPol])
      (singleton_mem_matchOf (evalDropEvent_mem_enabled_source_of_certified
        (space := space) (dispatch := dispatch)
        (chan := chan) (payload := payload) hcert))
      (o, PUnit.unit)
  simpa [sys, e, o, evalDropSystem, evalDropEvent,
      EventSystem.fireMany, MatchingRealization.aggregate_singleton,
      MatchingRealization.singletonObs, accMul] using
    (runOutcomes_succ_of_step sys hstep (self_mem_runOutcomes sys singletonPol 0 _))

theorem evalDropQuietFrontier
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload : Atom}
    (hready : (certifiedPayloadReified space dispatch payload).Nonempty) :
    QuietFrontier
      (evalDropSystem space dispatch chan payload)
      (evalDropSource chan payload)
      [evalDropEvent space dispatch payload] := by
  refine ⟨?_, ?_, ?_⟩
  · exact singleton_mem_matchOf
      (evalDropEvent_mem_enabled_source
        (space := space) (dispatch := dispatch) hready)
  · intro e he
    simp [evalDropSystem, evalDropEnabled, evalDropEvent] at he
    rcases he with ⟨_, heq⟩
    simpa [evalDropEvent] using heq
  · intro L ρ hnd hsub
    have hshape : L = [] ∨ L = [evalDropEvent space dispatch payload] := by
      cases L with
      | nil =>
          exact Or.inl rfl
      | cons a rest =>
          have ha : a = evalDropEvent space dispatch payload :=
            List.mem_singleton.mp (hsub a (by simp))
          subst ha
          cases rest with
          | nil =>
              exact Or.inr rfl
          | cons b rest' =>
              have hb : b = evalDropEvent space dispatch payload :=
                List.mem_singleton.mp (hsub b (by simp))
              subst hb
              exfalso
              simp at hnd
    cases hshape with
    | inl hnil =>
        subst hnil
        cases ρ
        ext e
        simp [evalDropSystem, evalDropEnabled]
    | inr hsingle =>
        subst hsingle
        rcases ρ with ⟨o, ρnil⟩
        cases ρnil
        calc
          (evalDropSystem space dispatch chan payload).enabled
              ((evalDropSystem space dispatch chan payload).fireMany
                (evalDropSource chan payload)
                [evalDropEvent space dispatch payload]
                (o, PUnit.unit))
              = (evalDropSystem space dispatch chan payload).enabled
                  (evalDropResidual o.1.1) := by
                    simp [evalDropSystem, EventSystem.fireMany]
          _ = ∅ := evalDropSystem_enabled_residual_empty
          _ = {e |
                e ∈ (evalDropSystem space dispatch chan payload).enabled
                  (evalDropSource chan payload) ∧
                e ∉ [evalDropEvent space dispatch payload]} := by
                  ext e
                  simp [evalDropSystem, evalDropEnabled, evalDropEvent]

/-- Quiescent may-set crown for the concrete drop-shell instance: the abstract run-layer closure
already collapses to the singleton fold of the certified payload outcomes.  This is the concrete
slice the full B7 bridge must extend. -/
theorem evalDropSystem_macro_collapse
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload : Atom}
    (hready : (certifiedPayloadReified space dispatch payload).Nonempty)
    (acc : Multiset Atom × (Unit × ExportBag Empty)) :
    {acc' | ∃ s',
        (∃ n,
          (s', acc') ∈
            runOutcomes (evalDropSystem space dispatch chan payload) allPol n
              (evalDropSource chan payload, acc)) ∧
        (evalDropSystem space dispatch chan payload).enabled s' = ∅} =
    {acc' | ∃ x ∈ foldOutcomesΩ [certifiedPayloadReified space dispatch payload],
        acc' = accMul acc x} := by
  simpa [evalDropSystem, evalDropEvent] using
    (macro_collapse_corollary
      (sys := evalDropSystem space dispatch chan payload)
      (s := evalDropSource chan payload)
      (M := [evalDropEvent space dispatch payload])
      (h := evalDropQuietFrontier
        (space := space) (dispatch := dispatch)
        (chan := chan) (payload := payload) hready)
      acc)

/-- Abstract quiescent may-set membership produced from one certified operational result, via the
concrete drop-shell `EventSystem`. -/
theorem evalDropSystem_quiescent_mem_of_certified
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload value : Atom}
    (hcert : CertifiedPayloadResult space dispatch payload value) :
    (({value} : Multiset Atom), ((), (1 : ExportBag Empty))) ∈
      {acc' | ∃ s',
          (∃ n,
            (s', acc') ∈
              runOutcomes (evalDropSystem space dispatch chan payload) allPol n
                (evalDropSource chan payload,
                  ((0 : Multiset Atom), (1 : Unit × ExportBag Empty)))) ∧
          (evalDropSystem space dispatch chan payload).enabled s' = ∅} := by
  rw [evalDropSystem_macro_collapse
    (space := space) (dispatch := dispatch)
    (chan := chan) (payload := payload)
    ((certifiedPayloadReified_nonempty_iff
      (space := space) (dispatch := dispatch) (payload := payload)).2
      ⟨value, hcert⟩)
    (((0 : Multiset Atom), (1 : Unit × ExportBag Empty)))]
  refine ⟨(({value} : Multiset Atom), ((), (1 : ExportBag Empty))), ?_, ?_⟩
  · exact certifiedPayloadReified_singleton_fold_mem_of_certified hcert
  · simp [accMul]

/-- Honest empty-frontier complement for the drop-shell instance: if the certified payload set is
empty, the source configuration itself is already quiescent in the abstract run layer, with the
initial accumulator unchanged. -/
theorem evalDropSystem_quiescent_self_mem_of_empty
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload : Atom}
    (hempty : ¬ (certifiedPayloadReified space dispatch payload).Nonempty) :
    ((0 : Multiset Atom), (1 : Unit × ExportBag Empty)) ∈
      {acc' | ∃ s',
          (∃ n,
            (s', acc') ∈
              runOutcomes (evalDropSystem space dispatch chan payload) allPol n
                (evalDropSource chan payload,
                  ((0 : Multiset Atom), (1 : Unit × ExportBag Empty)))) ∧
          (evalDropSystem space dispatch chan payload).enabled s' = ∅} := by
  refine ⟨evalDropSource chan payload, ⟨0, ?_⟩, ?_⟩
  · simpa using self_mem_runOutcomes
      (evalDropSystem space dispatch chan payload) allPol 0
      (evalDropSource chan payload,
        ((0 : Multiset Atom), (1 : Unit × ExportBag Empty)))
  · simp [evalDropSystem, evalDropEnabled, hempty]

theorem evalDropSystem_quiescent_eq_self_of_empty
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload : Atom}
    (hempty : ¬ (certifiedPayloadReified space dispatch payload).Nonempty) :
    {acc' | ∃ s',
        (∃ n,
          (s', acc') ∈
            runOutcomes (evalDropSystem space dispatch chan payload) allPol n
              (evalDropSource chan payload,
                ((0 : Multiset Atom), (1 : Unit × ExportBag Empty)))) ∧
        (evalDropSystem space dispatch chan payload).enabled s' = ∅} =
    {((0 : Multiset Atom), (1 : Unit × ExportBag Empty))} := by
  ext acc'
  constructor
  · rintro ⟨s', ⟨n, hrun⟩, hq⟩
    have hsingleton :=
      evalDropSystem_runOutcomes_source_eq_self_of_empty
        (space := space) (dispatch := dispatch)
        (chan := chan) (payload := payload)
        (acc := ((0 : Multiset Atom), (1 : Unit × ExportBag Empty))) hempty n
    rw [hsingleton] at hrun
    have hpair : (s', acc') = (evalDropSource chan payload,
        ((0 : Multiset Atom), (1 : Unit × ExportBag Empty))) :=
      Set.mem_singleton_iff.mp hrun
    cases hpair
    rfl
  · intro hacc
    rw [Set.mem_singleton_iff.mp hacc]
    exact evalDropSystem_quiescent_self_mem_of_empty
      (space := space) (dispatch := dispatch)
      (chan := chan) (payload := payload) hempty

/-- Concrete completeness slice for the drop-shell abstract run layer: every quiescent abstract
observable already comes from some certified payload result. -/
theorem evalDropSystem_certified_of_quiescent_mem
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload : Atom}
    {acc' : Multiset Atom × (Unit × ExportBag Empty)}
    (hready : (certifiedPayloadReified space dispatch payload).Nonempty)
    (hmem :
      acc' ∈
        {acc' | ∃ s',
            (∃ n,
              (s', acc') ∈
                runOutcomes (evalDropSystem space dispatch chan payload) allPol n
                  (evalDropSource chan payload,
                    ((0 : Multiset Atom), (1 : Unit × ExportBag Empty)))) ∧
            (evalDropSystem space dispatch chan payload).enabled s' = ∅}) :
    ∃ value,
      CertifiedPayloadResult space dispatch payload value ∧
      acc' = (({value} : Multiset Atom), ((), (1 : ExportBag Empty))) := by
  rw [evalDropSystem_macro_collapse
    (space := space) (dispatch := dispatch)
    (chan := chan) (payload := payload)
    hready
    (((0 : Multiset Atom), (1 : Unit × ExportBag Empty)))] at hmem
  obtain ⟨x, hx, hacc⟩ := hmem
  have hx' :
      x ∈ foldOutcomesΩ (matchingPayloads
        [evalDropEvent space dispatch payload]) := by
    simpa [matchingPayloads, evalDropEvent] using hx
  obtain ⟨ρ, hρ⟩ :=
    MatchingRealization.exists_of_mem_foldOutcomesΩ
      (R := Atom) (Δ := Unit) (Ω := Empty) (M := [evalDropEvent space dispatch payload]) hx'
  rcases ρ with ⟨o, ρnil⟩
  cases ρnil
  obtain ⟨value, hcert, hoval⟩ := o.2
  refine ⟨value, hcert, ?_⟩
  have hxval : x = (({value} : Multiset Atom), ((), (1 : ExportBag Empty))) := by
    calc
      x = MatchingRealization.aggregate (M := [evalDropEvent space dispatch payload]) (o, PUnit.unit) := hρ.symm
      _ = MatchingRealization.singletonObs o := MatchingRealization.aggregate_singleton o
      _ = (({value} : Multiset Atom), ((), (1 : ExportBag Empty))) := by
        simp [MatchingRealization.singletonObs, hoval]
  calc
    acc' = accMul ((0 : Multiset Atom), (1 : Unit × ExportBag Empty)) x := hacc
    _ = x := by simp [accMul]
    _ = (({value} : Multiset Atom), ((), (1 : ExportBag Empty))) := hxval

theorem evalDrop_quiescent_run_subset_scObservedOutcomes
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload : Atom}
    (hready : (certifiedPayloadReified space dispatch payload).Nonempty) :
    {acc' | ∃ s',
        (∃ n,
          (s', acc') ∈
            runOutcomes (evalDropSystem space dispatch chan payload) allPol n
              (evalDropSource chan payload,
                ((0 : Multiset Atom), (1 : Unit × ExportBag Empty)))) ∧
        (evalDropSystem space dispatch chan payload).enabled s' = ∅} ⊆
      RhometaSCObservedOutcomes space dispatch (evalDropSource chan payload) := by
  intro acc' hmem
  obtain ⟨value, hcert, hacc⟩ :=
    evalDropSystem_certified_of_quiescent_mem
      (space := space) (dispatch := dispatch)
      (chan := chan) (payload := payload) hready hmem
  rw [hacc]
  exact evalDrop_certified_value_scObservedOutcome
    (space := space) (dispatch := dispatch)
    (chan := chan) (payload := payload) hcert

theorem evalDrop_certified_image_subset_quiescent_run
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload : Atom} :
    {acc' | ∃ value,
        CertifiedPayloadResult space dispatch payload value ∧
        acc' = (({value} : Multiset Atom), ((), (1 : ExportBag Empty)))} ⊆
    {acc' | ∃ s',
        (∃ n,
          (s', acc') ∈
            runOutcomes (evalDropSystem space dispatch chan payload) allPol n
              (evalDropSource chan payload,
                ((0 : Multiset Atom), (1 : Unit × ExportBag Empty)))) ∧
        (evalDropSystem space dispatch chan payload).enabled s' = ∅} := by
  rintro acc' ⟨value, hcert, rfl⟩
  exact evalDropSystem_quiescent_mem_of_certified
    (space := space) (dispatch := dispatch)
    (chan := chan) (payload := payload) hcert

theorem evalDrop_quiescent_run_eq_certified_decoded_image
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload : Atom}
    (hready : (certifiedPayloadReified space dispatch payload).Nonempty) :
    {acc' | ∃ s',
        (∃ n,
          (s', acc') ∈
            runOutcomes (evalDropSystem space dispatch chan payload) allPol n
              (evalDropSource chan payload,
                ((0 : Multiset Atom), (1 : Unit × ExportBag Empty)))) ∧
        (evalDropSystem space dispatch chan payload).enabled s' = ∅} =
    {obs |
      obs ∈ RhometaDecodedOutcomes space dispatch (evalDropSource chan payload) ∧
      ∃ value,
        CertifiedPayloadResult space dispatch payload value ∧
        obs =
          (({value} : Multiset Atom),
            ((), (1 : Multiplicative (Multiset Empty))))} := by
  ext obs
  constructor
  · intro hmem
    obtain ⟨value, hcert, hobs⟩ :=
      evalDropSystem_certified_of_quiescent_mem
        (space := space) (dispatch := dispatch)
        (chan := chan) (payload := payload) hready hmem
    refine ⟨?_, value, hcert, hobs⟩
    rw [hobs]
    exact evalDrop_certified_value_decodedOutcome
      (space := space) (dispatch := dispatch)
      (chan := chan) (payload := payload) hcert
  · rintro ⟨_hobs, value, hcert, hvalue⟩
    rw [hvalue]
    exact evalDropSystem_quiescent_mem_of_certified
      (space := space) (dispatch := dispatch)
      (chan := chan) (payload := payload) hcert

/-- Certified-slice drop-shell bridge over directly decoded operational
outcomes.  This is the precise `RhometaOutcomes`-based carrier that the final
witness-free converse will target after removing the explicit certified slice. -/
theorem rhometta_bridge_certified_decoded
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload : Atom}
    (hready : (certifiedPayloadReified space dispatch payload).Nonempty) :
    {acc' | ∃ s',
        (∃ n,
          (s', acc') ∈
            runOutcomes (evalDropSystem space dispatch chan payload) allPol n
              (evalDropSource chan payload,
                ((0 : Multiset Atom), (1 : Unit × ExportBag Empty)))) ∧
        (evalDropSystem space dispatch chan payload).enabled s' = ∅} =
    {obs |
      obs ∈ RhometaDecodedOutcomes space dispatch (evalDropSource chan payload) ∧
      ∃ value,
        CertifiedPayloadResult space dispatch payload value ∧
        obs =
          (({value} : Multiset Atom),
            ((), (1 : Multiplicative (Multiset Empty))))} := by
  exact evalDrop_quiescent_run_eq_certified_decoded_image
    (space := space) (dispatch := dispatch)
    (chan := chan) (payload := payload) hready

theorem evalDrop_quiescent_run_eq_certified_scObserved_image
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload : Atom}
    (hready : (certifiedPayloadReified space dispatch payload).Nonempty) :
    {acc' | ∃ s',
        (∃ n,
          (s', acc') ∈
            runOutcomes (evalDropSystem space dispatch chan payload) allPol n
              (evalDropSource chan payload,
                ((0 : Multiset Atom), (1 : Unit × ExportBag Empty)))) ∧
        (evalDropSystem space dispatch chan payload).enabled s' = ∅} =
    {obs |
      obs ∈ RhometaSCObservedOutcomes space dispatch (evalDropSource chan payload) ∧
      ∃ value,
        CertifiedPayloadResult space dispatch payload value ∧
        obs =
          (({value} : Multiset Atom),
            ((), (1 : Multiplicative (Multiset Empty))))} := by
  ext obs
  constructor
  · intro hmem
    obtain ⟨value, hcert, hobs⟩ :=
      evalDropSystem_certified_of_quiescent_mem
        (space := space) (dispatch := dispatch)
        (chan := chan) (payload := payload) hready hmem
    refine ⟨?_, value, hcert, hobs⟩
    rw [hobs]
    exact evalDrop_certified_value_scObservedOutcome
      (space := space) (dispatch := dispatch)
      (chan := chan) (payload := payload) hcert
  · rintro ⟨_hobs, value, hcert, hvalue⟩
    rw [hvalue]
    exact evalDropSystem_quiescent_mem_of_certified
      (space := space) (dispatch := dispatch)
      (chan := chan) (payload := payload) hcert

theorem evalDrop_quiescent_run_eq_certified_scObserved_branch_split
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload : Atom} :
    ((certifiedPayloadReified space dispatch payload).Nonempty →
      {acc' | ∃ s',
          (∃ n,
            (s', acc') ∈
              runOutcomes (evalDropSystem space dispatch chan payload) allPol n
                (evalDropSource chan payload,
                  ((0 : Multiset Atom), (1 : Unit × ExportBag Empty)))) ∧
          (evalDropSystem space dispatch chan payload).enabled s' = ∅} =
        {obs |
          obs ∈ RhometaSCObservedOutcomes space dispatch (evalDropSource chan payload) ∧
          ∃ value,
            CertifiedPayloadResult space dispatch payload value ∧
            obs =
              (({value} : Multiset Atom),
                ((), (1 : Multiplicative (Multiset Empty))))}) ∧
    (¬ (certifiedPayloadReified space dispatch payload).Nonempty →
      {acc' | ∃ s',
          (∃ n,
            (s', acc') ∈
              runOutcomes (evalDropSystem space dispatch chan payload) allPol n
                (evalDropSource chan payload,
                  ((0 : Multiset Atom), (1 : Unit × ExportBag Empty)))) ∧
          (evalDropSystem space dispatch chan payload).enabled s' = ∅} =
        {((0 : Multiset Atom), (1 : Unit × ExportBag Empty))}) := by
  constructor
  · intro hready
    exact evalDrop_quiescent_run_eq_certified_scObserved_image
      (space := space) (dispatch := dispatch)
      (chan := chan) (payload := payload) hready
  · intro hempty
    exact evalDropSystem_quiescent_eq_self_of_empty
      (space := space) (dispatch := dispatch)
      (chan := chan) (payload := payload) hempty

theorem evalDrop_quiescent_run_mem_iff_certified_scObserved
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload : Atom}
    (hready : (certifiedPayloadReified space dispatch payload).Nonempty)
    {obs : Multiset Atom × (Unit × ExportBag Empty)} :
    obs ∈
        {acc' | ∃ s',
            (∃ n,
              (s', acc') ∈
                runOutcomes (evalDropSystem space dispatch chan payload) allPol n
                  (evalDropSource chan payload,
                    ((0 : Multiset Atom), (1 : Unit × ExportBag Empty)))) ∧
            (evalDropSystem space dispatch chan payload).enabled s' = ∅} ↔
      obs ∈ RhometaSCObservedOutcomes space dispatch (evalDropSource chan payload) ∧
        ∃ value,
          CertifiedPayloadResult space dispatch payload value ∧
          obs =
            (({value} : Multiset Atom),
              ((), (1 : Multiplicative (Multiset Empty)))) := by
  rw [evalDrop_quiescent_run_eq_certified_scObserved_image
    (space := space) (dispatch := dispatch)
    (chan := chan) (payload := payload) hready]
  rfl

/-- Certified-slice drop-shell bridge, stated over the quotient-aware
SC-observed operational carrier.  On the ready branch, the concrete
`EventSystem` quiescent accumulators are exactly the certified singleton
observations visible through `RhometaSCObservedOutcomes`. -/
theorem rhometta_bridge_certified_scObserved
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload : Atom}
    (hready : (certifiedPayloadReified space dispatch payload).Nonempty) :
    {acc' | ∃ s',
        (∃ n,
          (s', acc') ∈
            runOutcomes (evalDropSystem space dispatch chan payload) allPol n
              (evalDropSource chan payload,
                ((0 : Multiset Atom), (1 : Unit × ExportBag Empty)))) ∧
        (evalDropSystem space dispatch chan payload).enabled s' = ∅} =
    {obs |
      obs ∈ RhometaSCObservedOutcomes space dispatch (evalDropSource chan payload) ∧
      ∃ value,
        CertifiedPayloadResult space dispatch payload value ∧
        obs =
          (({value} : Multiset Atom),
            ((), (1 : Multiplicative (Multiset Empty))))} := by
  exact evalDrop_quiescent_run_eq_certified_scObserved_image
    (space := space) (dispatch := dispatch)
    (chan := chan) (payload := payload) hready

/-- Certified-slice bridge with the SC-observed carrier conjunct collapsed:
on the ready branch, the concrete drop-system quiescent accumulators are
exactly the singleton observations generated by certified payload results. -/
theorem rhometta_bridge_certified
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload : Atom}
    (hready : (certifiedPayloadReified space dispatch payload).Nonempty) :
    {acc' | ∃ s',
        (∃ n,
          (s', acc') ∈
            runOutcomes (evalDropSystem space dispatch chan payload) allPol n
              (evalDropSource chan payload,
                ((0 : Multiset Atom), (1 : Unit × ExportBag Empty)))) ∧
        (evalDropSystem space dispatch chan payload).enabled s' = ∅} =
    {obs | ∃ value,
      CertifiedPayloadResult space dispatch payload value ∧
      obs =
        (({value} : Multiset Atom),
          ((), (1 : Multiplicative (Multiset Empty))))} := by
  calc
    {acc' | ∃ s',
        (∃ n,
          (s', acc') ∈
            runOutcomes (evalDropSystem space dispatch chan payload) allPol n
              (evalDropSource chan payload,
                ((0 : Multiset Atom), (1 : Unit × ExportBag Empty)))) ∧
        (evalDropSystem space dispatch chan payload).enabled s' = ∅}
        =
      {obs |
        obs ∈ RhometaSCObservedOutcomes space dispatch (evalDropSource chan payload) ∧
        ∃ value,
          CertifiedPayloadResult space dispatch payload value ∧
          obs =
            (({value} : Multiset Atom),
              ((), (1 : Multiplicative (Multiset Empty))))} := by
        exact rhometta_bridge_certified_scObserved
          (space := space) (dispatch := dispatch)
          (chan := chan) (payload := payload) hready
    _ =
      {obs | ∃ value,
        CertifiedPayloadResult space dispatch payload value ∧
        obs =
          (({value} : Multiset Atom),
            ((), (1 : Multiplicative (Multiset Empty))))} := by
        exact evalDrop_certified_scObserved_image_eq_certified_image
          (space := space) (dispatch := dispatch)
          (chan := chan) (payload := payload)

theorem rhometta_bridge_certified_mem_iff
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload : Atom}
    (hready : (certifiedPayloadReified space dispatch payload).Nonempty)
    {obs : Multiset Atom × (Unit × ExportBag Empty)} :
    obs ∈
        {acc' | ∃ s',
          (∃ n,
            (s', acc') ∈
              runOutcomes (evalDropSystem space dispatch chan payload) allPol n
                (evalDropSource chan payload,
                  ((0 : Multiset Atom), (1 : Unit × ExportBag Empty)))) ∧
          (evalDropSystem space dispatch chan payload).enabled s' = ∅} ↔
      ∃ value,
        CertifiedPayloadResult space dispatch payload value ∧
        obs =
          (({value} : Multiset Atom),
            ((), (1 : Multiplicative (Multiset Empty)))) := by
  rw [rhometta_bridge_certified
    (space := space) (dispatch := dispatch)
    (chan := chan) (payload := payload) hready]
  rfl

/-- Branch-split form of `rhometta_bridge_certified`: the ready branch is
the certified singleton image, while the empty frontier branch keeps the
initial accumulator unchanged. -/
theorem rhometta_bridge_certified_branch_split
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload : Atom} :
    ((certifiedPayloadReified space dispatch payload).Nonempty →
      {acc' | ∃ s',
          (∃ n,
            (s', acc') ∈
              runOutcomes (evalDropSystem space dispatch chan payload) allPol n
                (evalDropSource chan payload,
                  ((0 : Multiset Atom), (1 : Unit × ExportBag Empty)))) ∧
          (evalDropSystem space dispatch chan payload).enabled s' = ∅} =
        {obs | ∃ value,
          CertifiedPayloadResult space dispatch payload value ∧
          obs =
            (({value} : Multiset Atom),
              ((), (1 : Multiplicative (Multiset Empty))))}) ∧
    (¬ (certifiedPayloadReified space dispatch payload).Nonempty →
      {acc' | ∃ s',
          (∃ n,
            (s', acc') ∈
              runOutcomes (evalDropSystem space dispatch chan payload) allPol n
                (evalDropSource chan payload,
                  ((0 : Multiset Atom), (1 : Unit × ExportBag Empty)))) ∧
          (evalDropSystem space dispatch chan payload).enabled s' = ∅} =
        {((0 : Multiset Atom), (1 : Unit × ExportBag Empty))}) := by
  constructor
  · intro hready
    exact rhometta_bridge_certified
      (space := space) (dispatch := dispatch)
      (chan := chan) (payload := payload) hready
  · intro hempty
    exact evalDropSystem_quiescent_eq_self_of_empty
      (space := space) (dispatch := dispatch)
      (chan := chan) (payload := payload) hempty

/-- Branch-split form of `rhometta_bridge_certified_scObserved`: the ready
branch is the SC-observed certified image, and the empty frontier branch keeps
the initial accumulator unchanged. -/
theorem rhometta_bridge_certified_scObserved_branch_split
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload : Atom} :
    ((certifiedPayloadReified space dispatch payload).Nonempty →
      {acc' | ∃ s',
          (∃ n,
            (s', acc') ∈
              runOutcomes (evalDropSystem space dispatch chan payload) allPol n
                (evalDropSource chan payload,
                  ((0 : Multiset Atom), (1 : Unit × ExportBag Empty)))) ∧
          (evalDropSystem space dispatch chan payload).enabled s' = ∅} =
        {obs |
          obs ∈ RhometaSCObservedOutcomes space dispatch (evalDropSource chan payload) ∧
          ∃ value,
            CertifiedPayloadResult space dispatch payload value ∧
            obs =
              (({value} : Multiset Atom),
                ((), (1 : Multiplicative (Multiset Empty))))}) ∧
    (¬ (certifiedPayloadReified space dispatch payload).Nonempty →
      {acc' | ∃ s',
          (∃ n,
            (s', acc') ∈
              runOutcomes (evalDropSystem space dispatch chan payload) allPol n
                (evalDropSource chan payload,
                  ((0 : Multiset Atom), (1 : Unit × ExportBag Empty)))) ∧
          (evalDropSystem space dispatch chan payload).enabled s' = ∅} =
        {((0 : Multiset Atom), (1 : Unit × ExportBag Empty))}) := by
  exact evalDrop_quiescent_run_eq_certified_scObserved_branch_split
    (space := space) (dispatch := dispatch)
    (chan := chan) (payload := payload)

/-- Concrete micro-bridge for the drop-observer shell: one certified operational branch yields
the expected residual, that residual decodes to the singleton post-reification outcome, and that
same observable lies in the abstract quiescent may-set of the concrete drop-shell `EventSystem`. -/
theorem evalDrop_certified_branch_matches_quiescent_run
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload value : Atom}
    (hcert : CertifiedPayloadResult space dispatch payload value) :
    Nonempty (RhometaReduces space dispatch
        (evalDropSource chan payload) (evalDropResidual value)) ∧
      reifiedOutcomeOf? (evalDropResidual value) =
        some (({value} : Multiset Atom), ((), (1 : ExportBag Empty))) ∧
      (({value} : Multiset Atom), ((), (1 : ExportBag Empty))) ∈
        {acc' | ∃ s',
            (∃ n,
              (s', acc') ∈
                runOutcomes (evalDropSystem space dispatch chan payload) allPol n
                  (evalDropSource chan payload,
                    ((0 : Multiset Atom), (1 : Unit × ExportBag Empty)))) ∧
            (evalDropSystem space dispatch chan payload).enabled s' = ∅} := by
  exact ⟨evalDrop_certified_branch hcert,
    reifiedOutcomeOf?_evalDropResidual value,
    evalDropSystem_quiescent_mem_of_certified hcert⟩

/-- SC-aware variant of the concrete micro-bridge: the operational residual is decoded through
the wrapper-collapsing outcome map, matching the abstract singleton outcome carrier directly. -/
theorem evalDrop_certified_branch_matches_sc_quiescent_run
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload value : Atom}
    (hcert : CertifiedPayloadResult space dispatch payload value) :
    Nonempty (RhometaReduces space dispatch
        (evalDropSource chan payload) (evalDropResidual value)) ∧
      scReifiedOutcomeOf? (evalDropResidual value) =
        some (({value} : Multiset Atom), ((), (1 : Multiplicative (Multiset Empty)))) ∧
      (({value} : Multiset Atom), ((), (1 : ExportBag Empty))) ∈
        {acc' | ∃ s',
            (∃ n,
              (s', acc') ∈
                runOutcomes (evalDropSystem space dispatch chan payload) allPol n
                  (evalDropSource chan payload,
                    ((0 : Multiset Atom), (1 : Unit × ExportBag Empty)))) ∧
            (evalDropSystem space dispatch chan payload).enabled s' = ∅} := by
  exact ⟨evalDrop_certified_branch hcert,
    scReifiedOutcomeOf?_evalDropResidual value,
    evalDropSystem_quiescent_mem_of_certified hcert⟩

/-- Operational-outcome form of the same drop-shell bridge seed: a certified payload result
already yields a quiescent operational outcome whose decoded observable lies in the abstract
quiescent may-set of the concrete `EventSystem`.  This is the exact-shell stage-1 shape, but still
without the source-side SC inversion needed for arbitrary `equiv` detours. -/
theorem evalDrop_certified_outcome_matches_sc_quiescent_run
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload value : Atom}
    (hcert : CertifiedPayloadResult space dispatch payload value) :
    ∃ q,
      q ∈ RhometaOutcomes space dispatch (evalDropSource chan payload) ∧
      scReifiedOutcomeOf? q =
        some (({value} : Multiset Atom), ((), (1 : Multiplicative (Multiset Empty)))) ∧
      (({value} : Multiset Atom), ((), (1 : ExportBag Empty))) ∈
        {acc' | ∃ s',
            (∃ n,
              (s', acc') ∈
                runOutcomes (evalDropSystem space dispatch chan payload) allPol n
                  (evalDropSource chan payload,
                    ((0 : Multiset Atom), (1 : Unit × ExportBag Empty)))) ∧
            (evalDropSystem space dispatch chan payload).enabled s' = ∅} := by
  refine ⟨evalDropResidual value, ?_, ?_, ?_⟩
  · exact evalDrop_certified_value_outcome
      (space := space) (dispatch := dispatch)
      (chan := chan) (payload := payload) (value := value) hcert
  · exact scReifiedOutcomeOf?_evalDropResidual value
  · exact evalDropSystem_quiescent_mem_of_certified
      (space := space) (dispatch := dispatch)
      (chan := chan) (payload := payload) hcert

/-- The same concrete micro-bridge, lifted to `RhometaReducesStar`: one certified operational
branch already yields a quiescent abstract run outcome in the SC-aware carrier.  This is the
first stage-1-shaped bridge statement, still on the exact drop observer shell. -/
theorem evalDrop_certified_star_matches_sc_quiescent_run
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload value : Atom}
    (hcert : CertifiedPayloadResult space dispatch payload value) :
    Nonempty (RhometaReducesStar space dispatch
        (evalDropSource chan payload) (evalDropResidual value)) ∧
      scReifiedOutcomeOf? (evalDropResidual value) =
        some (({value} : Multiset Atom), ((), (1 : Multiplicative (Multiset Empty)))) ∧
      (({value} : Multiset Atom), ((), (1 : ExportBag Empty))) ∈
        {acc' | ∃ s',
            (∃ n,
              (s', acc') ∈
                runOutcomes (evalDropSystem space dispatch chan payload) allPol n
                  (evalDropSource chan payload,
                    ((0 : Multiset Atom), (1 : Unit × ExportBag Empty)))) ∧
            (evalDropSystem space dispatch chan payload).enabled s' = ∅} := by
  refine ⟨?_, scReifiedOutcomeOf?_evalDropResidual value,
    evalDropSystem_quiescent_mem_of_certified hcert⟩
  refine ⟨RhometaReducesStar.step ?_ (RhometaReducesStar.refl _)⟩
  exact (evalDrop_certified_branch hcert).some

/-- Concrete completeness micro-bridge for the drop-observer shell: every quiescent abstract run
observable arises from some certified operational branch.  This is the stage-3-shaped companion
to `evalDrop_certified_star_matches_sc_quiescent_run`. -/
theorem evalDrop_quiescent_run_matches_certified_star
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload : Atom}
    {acc' : Multiset Atom × (Unit × ExportBag Empty)}
    (hready : (certifiedPayloadReified space dispatch payload).Nonempty)
    (hmem :
      acc' ∈
        {acc' | ∃ s',
            (∃ n,
              (s', acc') ∈
                runOutcomes (evalDropSystem space dispatch chan payload) allPol n
                  (evalDropSource chan payload,
                    ((0 : Multiset Atom), (1 : Unit × ExportBag Empty)))) ∧
            (evalDropSystem space dispatch chan payload).enabled s' = ∅}) :
    ∃ value,
      CertifiedPayloadResult space dispatch payload value ∧
      Nonempty (RhometaReducesStar space dispatch
        (evalDropSource chan payload) (evalDropResidual value)) ∧
      scReifiedOutcomeOf? (evalDropResidual value) =
        some (({value} : Multiset Atom), ((), (1 : Multiplicative (Multiset Empty)))) ∧
      acc' = (({value} : Multiset Atom), ((), (1 : ExportBag Empty))) := by
  obtain ⟨value, hcert, rfl⟩ :=
    evalDropSystem_certified_of_quiescent_mem
      (space := space) (dispatch := dispatch)
      (chan := chan) (payload := payload) hready hmem
  refine ⟨value, hcert, ?_, scReifiedOutcomeOf?_evalDropResidual value, rfl⟩
  refine ⟨RhometaReducesStar.step ?_ (RhometaReducesStar.refl _)⟩
  exact (evalDrop_certified_branch hcert).some

/-- Operational-outcome form of the exact-shell completeness witness: every quiescent abstract
run observable already comes from some quiescent operational outcome whose SC-aware decoder
recovers the same singleton post-reification carrier. -/
theorem evalDrop_quiescent_run_matches_certified_outcome
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload : Atom}
    {acc' : Multiset Atom × (Unit × ExportBag Empty)}
    (hready : (certifiedPayloadReified space dispatch payload).Nonempty)
    (hmem :
      acc' ∈
        {acc' | ∃ s',
            (∃ n,
              (s', acc') ∈
                runOutcomes (evalDropSystem space dispatch chan payload) allPol n
                  (evalDropSource chan payload,
                    ((0 : Multiset Atom), (1 : Unit × ExportBag Empty)))) ∧
            (evalDropSystem space dispatch chan payload).enabled s' = ∅}) :
    ∃ q value,
      CertifiedPayloadResult space dispatch payload value ∧
      q ∈ RhometaOutcomes space dispatch (evalDropSource chan payload) ∧
      scReifiedOutcomeOf? q =
        some (({value} : Multiset Atom), ((), (1 : Multiplicative (Multiset Empty)))) ∧
      acc' = (({value} : Multiset Atom), ((), (1 : ExportBag Empty))) := by
  obtain ⟨value, hcert, hstar, hdecode, hacc⟩ :=
    evalDrop_quiescent_run_matches_certified_star
      (space := space) (dispatch := dispatch)
      (chan := chan) (payload := payload) hready hmem
  refine ⟨evalDropResidual value, value, hcert, ?_, ?_, hacc⟩
  · exact evalDrop_certified_value_outcome
      (space := space) (dispatch := dispatch)
      (chan := chan) (payload := payload) (value := value) hcert
  · exact hdecode

/-- Concrete bridge equality for the drop-observer shell: the abstract quiescent may-set is
exactly the image of certified payload results in the post-reification carrier.  This is the
smallest honest set-equality instance of the eventual B7 crown. -/
theorem evalDrop_quiescent_run_eq_certified_image
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload : Atom}
    (hready : (certifiedPayloadReified space dispatch payload).Nonempty) :
    {acc' | ∃ s',
        (∃ n,
          (s', acc') ∈
            runOutcomes (evalDropSystem space dispatch chan payload) allPol n
              (evalDropSource chan payload,
                ((0 : Multiset Atom), (1 : Unit × ExportBag Empty)))) ∧
        (evalDropSystem space dispatch chan payload).enabled s' = ∅} =
    {acc' | ∃ value,
        CertifiedPayloadResult space dispatch payload value ∧
        acc' = (({value} : Multiset Atom), ((), (1 : ExportBag Empty)))} := by
  ext acc'
  constructor
  · intro hmem
    exact evalDropSystem_certified_of_quiescent_mem
      (space := space) (dispatch := dispatch)
      (chan := chan) (payload := payload) hready hmem
  · rintro ⟨value, hcert, rfl⟩
    exact evalDropSystem_quiescent_mem_of_certified
      (space := space) (dispatch := dispatch)
      (chan := chan) (payload := payload) hcert

/-- Operational-image variant of the drop-shell bridge equality: the abstract quiescent may-set
is exactly the image of certified operational star branches together with their SC-aware decoded
observables.  This is still micro-local to the drop shell, but its right-hand side now speaks the
same `RhometaReducesStar` language as B7's target bridge. -/
theorem evalDrop_quiescent_run_eq_certified_star_image
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload : Atom}
    (hready : (certifiedPayloadReified space dispatch payload).Nonempty) :
    {acc' | ∃ s',
        (∃ n,
          (s', acc') ∈
            runOutcomes (evalDropSystem space dispatch chan payload) allPol n
              (evalDropSource chan payload,
                ((0 : Multiset Atom), (1 : Unit × ExportBag Empty)))) ∧
        (evalDropSystem space dispatch chan payload).enabled s' = ∅} =
    {acc' | ∃ value,
        CertifiedPayloadResult space dispatch payload value ∧
        Nonempty (RhometaReducesStar space dispatch
          (evalDropSource chan payload) (evalDropResidual value)) ∧
        scReifiedOutcomeOf? (evalDropResidual value) =
          some (({value} : Multiset Atom), ((), (1 : Multiplicative (Multiset Empty)))) ∧
        acc' = (({value} : Multiset Atom), ((), (1 : ExportBag Empty)))} := by
  ext acc'
  constructor
  · intro hmem
    exact evalDrop_quiescent_run_matches_certified_star
      (space := space) (dispatch := dispatch)
      (chan := chan) (payload := payload) hready hmem
  · rintro ⟨value, hcert, _hstar, _hdecode, rfl⟩
    exact evalDropSystem_quiescent_mem_of_certified
      (space := space) (dispatch := dispatch)
      (chan := chan) (payload := payload) hcert

/-- Pointwise form of `evalDrop_quiescent_run_eq_certified_star_image`: on the ready branch, one
abstract quiescent accumulator appears iff it is witnessed by some certified operational star
branch with the matching SC-aware singleton outcome.  This packages the set equality into the
membership shape the later exact-shell converse will actually consume. -/
theorem evalDrop_quiescent_run_mem_iff_certified_star
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload : Atom}
    (hready : (certifiedPayloadReified space dispatch payload).Nonempty)
    {acc' : Multiset Atom × (Unit × ExportBag Empty)} :
    acc' ∈
        {acc' | ∃ s',
            (∃ n,
              (s', acc') ∈
                runOutcomes (evalDropSystem space dispatch chan payload) allPol n
                  (evalDropSource chan payload,
                    ((0 : Multiset Atom), (1 : Unit × ExportBag Empty)))) ∧
            (evalDropSystem space dispatch chan payload).enabled s' = ∅} ↔
      ∃ value,
        CertifiedPayloadResult space dispatch payload value ∧
        Nonempty (RhometaReducesStar space dispatch
          (evalDropSource chan payload) (evalDropResidual value)) ∧
        scReifiedOutcomeOf? (evalDropResidual value) =
          some (({value} : Multiset Atom), ((), (1 : Multiplicative (Multiset Empty)))) ∧
        acc' = (({value} : Multiset Atom), ((), (1 : ExportBag Empty))) := by
  rw [evalDrop_quiescent_run_eq_certified_star_image
    (space := space) (dispatch := dispatch)
    (chan := chan) (payload := payload) hready]
  rfl

/-- Exact-shell bridge equality in operational-outcomes language: the abstract quiescent may-set
is exactly the image of certified quiescent operational outcomes together with their SC-aware
decoded observables.  This keeps the right-hand side in the `RhometaOutcomes` carrier while still
recording the certified-payload witness that the current bridge proof uses. -/
theorem evalDrop_quiescent_run_eq_certified_outcome_image
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload : Atom}
    (hready : (certifiedPayloadReified space dispatch payload).Nonempty) :
    {acc' | ∃ s',
        (∃ n,
          (s', acc') ∈
            runOutcomes (evalDropSystem space dispatch chan payload) allPol n
              (evalDropSource chan payload,
                ((0 : Multiset Atom), (1 : Unit × ExportBag Empty)))) ∧
        (evalDropSystem space dispatch chan payload).enabled s' = ∅} =
    {acc' | ∃ q value,
        CertifiedPayloadResult space dispatch payload value ∧
        q ∈ RhometaOutcomes space dispatch (evalDropSource chan payload) ∧
        scReifiedOutcomeOf? q =
          some (({value} : Multiset Atom), ((), (1 : Multiplicative (Multiset Empty)))) ∧
        acc' = (({value} : Multiset Atom), ((), (1 : ExportBag Empty)))} := by
  ext acc'
  constructor
  · intro hmem
    exact evalDrop_quiescent_run_matches_certified_outcome
      (space := space) (dispatch := dispatch)
      (chan := chan) (payload := payload) hready hmem
  · rintro ⟨q, value, hcert, _hout, _hdecode, rfl⟩
    exact evalDropSystem_quiescent_mem_of_certified
      (space := space) (dispatch := dispatch)
      (chan := chan) (payload := payload) hcert

/-- Pointwise form of `evalDrop_quiescent_run_eq_certified_outcome_image`: on the ready branch,
one abstract quiescent accumulator appears iff it is witnessed by some certified quiescent
operational outcome with the matching SC-aware singleton decoder result.  This is the exact-shell
operational surface the eventual source-side SC inversion will simplify further by removing the
explicit certified witness. -/
theorem evalDrop_quiescent_run_mem_iff_certified_outcome
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload : Atom}
    (hready : (certifiedPayloadReified space dispatch payload).Nonempty)
    {acc' : Multiset Atom × (Unit × ExportBag Empty)} :
    acc' ∈
        {acc' | ∃ s',
            (∃ n,
              (s', acc') ∈
                runOutcomes (evalDropSystem space dispatch chan payload) allPol n
                  (evalDropSource chan payload,
                    ((0 : Multiset Atom), (1 : Unit × ExportBag Empty)))) ∧
            (evalDropSystem space dispatch chan payload).enabled s' = ∅} ↔
      ∃ q value,
        CertifiedPayloadResult space dispatch payload value ∧
        q ∈ RhometaOutcomes space dispatch (evalDropSource chan payload) ∧
        scReifiedOutcomeOf? q =
          some (({value} : Multiset Atom), ((), (1 : Multiplicative (Multiset Empty)))) ∧
        acc' = (({value} : Multiset Atom), ((), (1 : ExportBag Empty))) := by
  rw [evalDrop_quiescent_run_eq_certified_outcome_image
    (space := space) (dispatch := dispatch)
    (chan := chan) (payload := payload) hready]
  rfl

/-- Branch-aware operational-star classification for the exact drop shell: once the stage-2
readiness split is expressed in `RhometaReducesStar` language, the ready branch is the certified
operational star image and the empty branch remains the unchanged initial accumulator. This keeps
the branch distinction explicit while moving one step closer to the eventual B7 bridge statement. -/
theorem evalDrop_quiescent_run_eq_certified_star_branch_split
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload : Atom} :
    ((certifiedPayloadReified space dispatch payload).Nonempty →
      {acc' | ∃ s',
          (∃ n,
            (s', acc') ∈
              runOutcomes (evalDropSystem space dispatch chan payload) allPol n
                (evalDropSource chan payload,
                  ((0 : Multiset Atom), (1 : Unit × ExportBag Empty)))) ∧
          (evalDropSystem space dispatch chan payload).enabled s' = ∅} =
        {acc' | ∃ value,
            CertifiedPayloadResult space dispatch payload value ∧
            Nonempty (RhometaReducesStar space dispatch
              (evalDropSource chan payload) (evalDropResidual value)) ∧
            scReifiedOutcomeOf? (evalDropResidual value) =
              some (({value} : Multiset Atom), ((), (1 : Multiplicative (Multiset Empty)))) ∧
            acc' = (({value} : Multiset Atom), ((), (1 : ExportBag Empty)))}) ∧
    (¬ (certifiedPayloadReified space dispatch payload).Nonempty →
      {acc' | ∃ s',
          (∃ n,
            (s', acc') ∈
              runOutcomes (evalDropSystem space dispatch chan payload) allPol n
                (evalDropSource chan payload,
                  ((0 : Multiset Atom), (1 : Unit × ExportBag Empty)))) ∧
          (evalDropSystem space dispatch chan payload).enabled s' = ∅} =
        {((0 : Multiset Atom), (1 : Unit × ExportBag Empty))}) := by
  constructor
  · intro hready
    exact evalDrop_quiescent_run_eq_certified_star_image
      (space := space) (dispatch := dispatch)
      (chan := chan) (payload := payload) hready
  · intro hready
    exact evalDropSystem_quiescent_eq_self_of_empty
      (space := space) (dispatch := dispatch)
      (chan := chan) (payload := payload) hready

/-- Branch-aware operational-outcomes classification for the exact drop shell: the ready branch is
the certified quiescent operational-outcome image, while the empty branch is still the unchanged
initial accumulator. This is the same honest split as above, now stated entirely in the
`RhometaOutcomes` carrier that the eventual operational converse will consume. -/
theorem evalDrop_quiescent_run_eq_certified_outcome_branch_split
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload : Atom} :
    ((certifiedPayloadReified space dispatch payload).Nonempty →
      {acc' | ∃ s',
          (∃ n,
            (s', acc') ∈
              runOutcomes (evalDropSystem space dispatch chan payload) allPol n
                (evalDropSource chan payload,
                  ((0 : Multiset Atom), (1 : Unit × ExportBag Empty)))) ∧
          (evalDropSystem space dispatch chan payload).enabled s' = ∅} =
        {acc' | ∃ q value,
            CertifiedPayloadResult space dispatch payload value ∧
            q ∈ RhometaOutcomes space dispatch (evalDropSource chan payload) ∧
            scReifiedOutcomeOf? q =
              some (({value} : Multiset Atom), ((), (1 : Multiplicative (Multiset Empty)))) ∧
            acc' = (({value} : Multiset Atom), ((), (1 : ExportBag Empty)))}) ∧
    (¬ (certifiedPayloadReified space dispatch payload).Nonempty →
      {acc' | ∃ s',
          (∃ n,
            (s', acc') ∈
              runOutcomes (evalDropSystem space dispatch chan payload) allPol n
                (evalDropSource chan payload,
                  ((0 : Multiset Atom), (1 : Unit × ExportBag Empty)))) ∧
          (evalDropSystem space dispatch chan payload).enabled s' = ∅} =
        {((0 : Multiset Atom), (1 : Unit × ExportBag Empty))}) := by
  constructor
  · intro hready
    exact evalDrop_quiescent_run_eq_certified_outcome_image
      (space := space) (dispatch := dispatch)
      (chan := chan) (payload := payload) hready
  · intro hready
    exact evalDropSystem_quiescent_eq_self_of_empty
      (space := space) (dispatch := dispatch)
      (chan := chan) (payload := payload) hready

/-- Branch-aware exact-shell classification: the drop observer's abstract quiescent may-set is
either the certified singleton image (when the payload frontier is realizable) or the unchanged
initial accumulator (when the frontier is empty). This packages the honest stage-2 split into one
theorem for later B7 use, without hiding the readiness branch behind a decidability assumption. -/
theorem evalDrop_quiescent_run_eq_branch_split
    {space : Space} {dispatch : GroundedDispatch}
    {chan : Pattern} {payload : Atom} :
    ((certifiedPayloadReified space dispatch payload).Nonempty →
      {acc' | ∃ s',
          (∃ n,
            (s', acc') ∈
              runOutcomes (evalDropSystem space dispatch chan payload) allPol n
                (evalDropSource chan payload,
                  ((0 : Multiset Atom), (1 : Unit × ExportBag Empty)))) ∧
          (evalDropSystem space dispatch chan payload).enabled s' = ∅} =
        {acc' | ∃ value,
            CertifiedPayloadResult space dispatch payload value ∧
            acc' = (({value} : Multiset Atom), ((), (1 : ExportBag Empty)))}) ∧
    (¬ (certifiedPayloadReified space dispatch payload).Nonempty →
      {acc' | ∃ s',
          (∃ n,
            (s', acc') ∈
              runOutcomes (evalDropSystem space dispatch chan payload) allPol n
                (evalDropSource chan payload,
                  ((0 : Multiset Atom), (1 : Unit × ExportBag Empty)))) ∧
          (evalDropSystem space dispatch chan payload).enabled s' = ∅} =
        {((0 : Multiset Atom), (1 : Unit × ExportBag Empty))}) := by
  constructor
  · intro hready
    exact evalDrop_quiescent_run_eq_certified_image
      (space := space) (dispatch := dispatch)
      (chan := chan) (payload := payload) hready
  · intro hready
    exact evalDropSystem_quiescent_eq_self_of_empty
      (space := space) (dispatch := dispatch)
      (chan := chan) (payload := payload) hready

end EvalDropRunBridge

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.RhometaReduction
