import Mettapedia.SetTheory.Profiles.CommonCore
import Mettapedia.GSLT.LanguageDef.CertificateGSLTWireFormat

/-!
# Finite source data for the existing material formulas

The encoder uses the shared symbolic wire carrier. Decoding checks every
de Bruijn index against the supplied number of free variables, and checks
the distinct bounded-quantifier grammar before accepting a Separation body.
A structural fuel bound is explicit; enough fuel reconstructs every encoded
formula, whereas exhaustion returns no interpretation. No predicate or set
law is supplied by this symbolic serialization.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Profiles.CommonCoreSyntax

open Mettapedia.TypeTheory.MaterialSets.Hypersets
open ContextualMaterialLogic (Formula)
open GraphBoundedFormulaRealization (BoundedFormula)
open Mettapedia.GSLT.LanguageDef.CertificateGSLT (WireTerm)

def formulaDepth {count : Nat} : Formula count → Nat
  | .bottom | .equal _ _ | .member _ _ => 1
  | .both left right | .either left right | .imply left right =>
      max (formulaDepth left) (formulaDepth right) + 1
  | .all body | .exist body => formulaDepth body + 1

def boundedDepth {count : Nat} : BoundedFormula count → Nat
  | .bottom | .equal _ _ | .member _ _ => 1
  | .both left right | .either left right | .imply left right =>
      max (boundedDepth left) (boundedDepth right) + 1
  | .allIn _ body | .existIn _ body => boundedDepth body + 1

def encodeFormula {count : Nat} : Formula count → WireTerm
  | .bottom => .list [.symbol "set:bottom"]
  | .equal first second => .list [.symbol "set:eq", .natural first.val, .natural second.val]
  | .member child parent => .list [.symbol "set:mem", .natural child.val, .natural parent.val]
  | .both left right => .list [.symbol "set:and", encodeFormula left, encodeFormula right]
  | .either left right => .list [.symbol "set:or", encodeFormula left, encodeFormula right]
  | .imply left right => .list [.symbol "set:imp", encodeFormula left, encodeFormula right]
  | .all body => .list [.symbol "set:all", encodeFormula body]
  | .exist body => .list [.symbol "set:exists", encodeFormula body]

def encodeBounded {count : Nat} : BoundedFormula count → WireTerm
  | .bottom => .list [.symbol "set:bottom"]
  | .equal first second => .list [.symbol "set:eq", .natural first.val, .natural second.val]
  | .member child parent => .list [.symbol "set:mem", .natural child.val, .natural parent.val]
  | .both left right => .list [.symbol "set:and", encodeBounded left, encodeBounded right]
  | .either left right => .list [.symbol "set:or", encodeBounded left, encodeBounded right]
  | .imply left right => .list [.symbol "set:imp", encodeBounded left, encodeBounded right]
  | .allIn parent body =>
      .list [.symbol "set:all-in", .natural parent.val, encodeBounded body]
  | .existIn parent body =>
      .list [.symbol "set:exists-in", .natural parent.val, encodeBounded body]

def decodeIndex (count value : Nat) : Option (Fin count) :=
  if bound : value < count then some ⟨value, bound⟩ else none

theorem decodeIndex_value {count : Nat} (index : Fin count) :
    decodeIndex count index.val = some index := by
  simp [decodeIndex, index.isLt]

def decodeFormula : Nat → (count : Nat) → WireTerm → Option (Formula count)
  | 0, _, _ => none
  | fuel+1, count, term =>
    match term with
    | .list [.symbol "set:bottom"] => some .bottom
    | .list [.symbol "set:eq", .natural first, .natural second] => do
        return .equal (← decodeIndex count first) (← decodeIndex count second)
    | .list [.symbol "set:mem", .natural child, .natural parent] => do
        return .member (← decodeIndex count child) (← decodeIndex count parent)
    | .list [.symbol "set:and", left, right] => do
        return .both (← decodeFormula fuel count left) (← decodeFormula fuel count right)
    | .list [.symbol "set:or", left, right] => do
        return .either (← decodeFormula fuel count left) (← decodeFormula fuel count right)
    | .list [.symbol "set:imp", left, right] => do
        return .imply (← decodeFormula fuel count left) (← decodeFormula fuel count right)
    | .list [.symbol "set:all", body] => .all <$> decodeFormula fuel (count+1) body
    | .list [.symbol "set:exists", body] => .exist <$> decodeFormula fuel (count+1) body
    | _ => none

def decodeBounded : Nat → (count : Nat) → WireTerm → Option (BoundedFormula count)
  | 0, _, _ => none
  | fuel+1, count, term =>
    match term with
    | .list [.symbol "set:bottom"] => some .bottom
    | .list [.symbol "set:eq", .natural first, .natural second] => do
        return .equal (← decodeIndex count first) (← decodeIndex count second)
    | .list [.symbol "set:mem", .natural child, .natural parent] => do
        return .member (← decodeIndex count child) (← decodeIndex count parent)
    | .list [.symbol "set:and", left, right] => do
        return .both (← decodeBounded fuel count left) (← decodeBounded fuel count right)
    | .list [.symbol "set:or", left, right] => do
        return .either (← decodeBounded fuel count left) (← decodeBounded fuel count right)
    | .list [.symbol "set:imp", left, right] => do
        return .imply (← decodeBounded fuel count left) (← decodeBounded fuel count right)
    | .list [.symbol "set:all-in", .natural parent, body] => do
        return .allIn (← decodeIndex count parent) (← decodeBounded fuel (count+1) body)
    | .list [.symbol "set:exists-in", .natural parent, body] => do
        return .existIn (← decodeIndex count parent) (← decodeBounded fuel (count+1) body)
    | _ => none

theorem formulaDepth_positive {count : Nat} (body : Formula count) : 0 < formulaDepth body := by
  cases body with
  | bottom => exact Nat.zero_lt_one
  | equal => exact Nat.zero_lt_one
  | member => exact Nat.zero_lt_one
  | both => exact Nat.succ_pos _
  | either => exact Nat.succ_pos _
  | imply => exact Nat.succ_pos _
  | all => exact Nat.succ_pos _
  | exist => exact Nat.succ_pos _

theorem boundedDepth_positive {count : Nat} (body : BoundedFormula count) : 0 < boundedDepth body := by
  cases body with
  | bottom => exact Nat.zero_lt_one
  | equal => exact Nat.zero_lt_one
  | member => exact Nat.zero_lt_one
  | both => exact Nat.succ_pos _
  | either => exact Nat.succ_pos _
  | imply => exact Nat.succ_pos _
  | allIn => exact Nat.succ_pos _
  | existIn => exact Nat.succ_pos _

theorem decodeFormula_encode {count : Nat} (body : Formula count)
    (fuel : Nat) (enough : formulaDepth body ≤ fuel) :
    decodeFormula fuel count (encodeFormula body) = some body := by
  induction body generalizing fuel with
  | bottom => cases fuel <;> simp_all [formulaDepth, encodeFormula, decodeFormula]
  | equal first second =>
      cases fuel <;> simp_all [formulaDepth, encodeFormula, decodeFormula, decodeIndex_value]
  | member child parent =>
      cases fuel <;> simp_all [formulaDepth, encodeFormula, decodeFormula, decodeIndex_value]
  | both left right leftIH rightIH =>
      cases fuel with
      | zero => simp [formulaDepth] at enough
      | succ fuel =>
          have leftBound : formulaDepth left ≤ fuel := by simp only [formulaDepth] at enough; omega
          have rightBound : formulaDepth right ≤ fuel := by simp only [formulaDepth] at enough; omega
          simp [encodeFormula, decodeFormula, leftIH fuel leftBound, rightIH fuel rightBound]
  | either left right leftIH rightIH =>
      cases fuel with
      | zero => simp [formulaDepth] at enough
      | succ fuel =>
          have leftBound : formulaDepth left ≤ fuel := by simp only [formulaDepth] at enough; omega
          have rightBound : formulaDepth right ≤ fuel := by simp only [formulaDepth] at enough; omega
          simp [encodeFormula, decodeFormula, leftIH fuel leftBound, rightIH fuel rightBound]
  | imply left right leftIH rightIH =>
      cases fuel with
      | zero => simp [formulaDepth] at enough
      | succ fuel =>
          have leftBound : formulaDepth left ≤ fuel := by simp only [formulaDepth] at enough; omega
          have rightBound : formulaDepth right ≤ fuel := by simp only [formulaDepth] at enough; omega
          simp [encodeFormula, decodeFormula, leftIH fuel leftBound, rightIH fuel rightBound]
  | all body induction =>
      cases fuel with
      | zero => simp [formulaDepth] at enough
      | succ fuel =>
          have bound : formulaDepth body ≤ fuel := by simp only [formulaDepth] at enough; omega
          simp [encodeFormula, decodeFormula, induction fuel bound]
  | exist body induction =>
      cases fuel with
      | zero => simp [formulaDepth] at enough
      | succ fuel =>
          have bound : formulaDepth body ≤ fuel := by simp only [formulaDepth] at enough; omega
          simp [encodeFormula, decodeFormula, induction fuel bound]

theorem decodeBounded_encode {count : Nat} (body : BoundedFormula count)
    (fuel : Nat) (enough : boundedDepth body ≤ fuel) :
    decodeBounded fuel count (encodeBounded body) = some body := by
  induction body generalizing fuel with
  | bottom => cases fuel <;> simp_all [boundedDepth, encodeBounded, decodeBounded]
  | equal first second =>
      cases fuel <;> simp_all [boundedDepth, encodeBounded, decodeBounded, decodeIndex_value]
  | member child parent =>
      cases fuel <;> simp_all [boundedDepth, encodeBounded, decodeBounded, decodeIndex_value]
  | both left right leftIH rightIH =>
      cases fuel with
      | zero => simp [boundedDepth] at enough
      | succ fuel =>
          have leftBound : boundedDepth left ≤ fuel := by simp only [boundedDepth] at enough; omega
          have rightBound : boundedDepth right ≤ fuel := by simp only [boundedDepth] at enough; omega
          simp [encodeBounded, decodeBounded, leftIH fuel leftBound, rightIH fuel rightBound]
  | either left right leftIH rightIH =>
      cases fuel with
      | zero => simp [boundedDepth] at enough
      | succ fuel =>
          have leftBound : boundedDepth left ≤ fuel := by simp only [boundedDepth] at enough; omega
          have rightBound : boundedDepth right ≤ fuel := by simp only [boundedDepth] at enough; omega
          simp [encodeBounded, decodeBounded, leftIH fuel leftBound, rightIH fuel rightBound]
  | imply left right leftIH rightIH =>
      cases fuel with
      | zero => simp [boundedDepth] at enough
      | succ fuel =>
          have leftBound : boundedDepth left ≤ fuel := by simp only [boundedDepth] at enough; omega
          have rightBound : boundedDepth right ≤ fuel := by simp only [boundedDepth] at enough; omega
          simp [encodeBounded, decodeBounded, leftIH fuel leftBound, rightIH fuel rightBound]
  | allIn parent body induction =>
      cases fuel with
      | zero => simp [boundedDepth] at enough
      | succ fuel =>
          have bound : boundedDepth body ≤ fuel := by simp only [boundedDepth] at enough; omega
          simp [encodeBounded, decodeBounded, decodeIndex_value, induction fuel bound]
  | existIn parent body induction =>
      cases fuel with
      | zero => simp [boundedDepth] at enough
      | succ fuel =>
          have bound : boundedDepth body ≤ fuel := by simp only [boundedDepth] at enough; omega
          simp [encodeBounded, decodeBounded, decodeIndex_value, induction fuel bound]

theorem encodeFormula_injective (count : Nat) : Function.Injective (@encodeFormula count) := by
  intro first second same
  let fuel := max (formulaDepth first) (formulaDepth second)
  have decoded := congrArg (decodeFormula fuel count) same
  rw [decodeFormula_encode first fuel (Nat.le_max_left _ _),
    decodeFormula_encode second fuel (Nat.le_max_right _ _)] at decoded
  exact Option.some.inj decoded

theorem encodeBounded_injective (count : Nat) : Function.Injective (@encodeBounded count) := by
  intro first second same
  let fuel := max (boundedDepth first) (boundedDepth second)
  have decoded := congrArg (decodeBounded fuel count) same
  rw [decodeBounded_encode first fuel (Nat.le_max_left _ _),
    decodeBounded_encode second fuel (Nat.le_max_right _ _)] at decoded
  exact Option.some.inj decoded

theorem unbounded_quantifier_is_not_bounded (fuel count : Nat) (body : WireTerm) :
    decodeBounded fuel count (.list [.symbol "set:all", body]) = none := by
  cases fuel <;> rfl

theorem out_of_scope_index_rejected (fuel count : Nat) :
    decodeFormula fuel count (.list [.symbol "set:eq", .natural count, .natural 0]) = none := by
  cases fuel <;> simp [decodeFormula, decodeIndex]

theorem fuel_exhaustion (count : Nat) (body : WireTerm) : decodeFormula 0 count body = none := rfl

end Mettapedia.SetTheory.Profiles.CommonCoreSyntax
