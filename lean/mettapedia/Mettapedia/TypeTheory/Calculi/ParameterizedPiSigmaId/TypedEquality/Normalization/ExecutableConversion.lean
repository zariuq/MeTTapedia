import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ExecutableReduction

/-!
# Executable type-directed conversion

The three recursive comparisons implement the independently defined
`Algorithm` relation. They consume scoped terms, a declaration package and
finite fuel; they reconstruct a derivation on acceptance. Function and pair
eta use their actual dependent codomains. Neutral application computes its
argument type from declaration or variable lookup, never from the proposed
answer. Failure is absence of a certificate, not a refutation theorem.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization
namespace ExecutableConversion

variable {Head : Type} (R : Rules Head) [DecidableEq Head]
variable [DecidableRel R.headEq] [∀ head, Decidable (R.isUniverse head)]
variable (reducer : ExecutableReduction.Reducer R)

abbrev Certificate (statement : AlgorithmStatement Head) := PLift (Algorithm R statement)

abbrev NeutralResult {n : Nat} (context : Ctx Head n) (left right : Tm Head n) :=
  (type : Tm Head n) × Certificate R (.neutral context left right type)

mutual

def compare : Nat → {n : Nat} → (context : Ctx Head n) →
    (left right type : Tm Head n) → Option (Certificate R (.compare context left right type))
  | 0, _, _, _, _, _ => none
  | fuel+1, _, context, left, right, type => do
      let normal ← reducer (fuel+1) type
      match normalShape : normal.val with
      | .pi domain body =>
          let certificate ← compare fuel (.snoc context domain)
            (.app (rename wk left) (.var 0)) (.app (rename wk right) (.var 0)) body
          return ⟨.pi (normalShape ▸ normal.property) certificate.down⟩
      | .sigma domain body =>
          let first ← compare fuel context (.fst left) (.fst right) domain
          let second ← compare fuel context (.snd left) (.snd right) (inst0 (.fst left) body)
          return ⟨.sigma (normalShape ▸ normal.property) first.down second.down⟩
      | .head value =>
          if isUniverse : R.isUniverse value then
            let certificate ← types fuel context left right
            return ⟨.sort (normalShape ▸ normal.property) isUniverse certificate.down⟩
          else compareNeutral fuel context left right type
      | .id carrier _ _ =>
          let leftNormal ← reducer (fuel+1) left
          let rightNormal ← reducer (fuel+1) right
          match leftShape : leftNormal.val, rightShape : rightNormal.val with
          | .refl first, .refl second =>
              let certificate ← compare fuel context first second carrier
              return ⟨.reflexivity (normalShape ▸ normal.property) (leftShape ▸ leftNormal.property) (rightShape ▸ rightNormal.property)
                certificate.down⟩
          | _, _ => compareNeutral fuel context left right type
      | _ => compareNeutral fuel context left right type

def compareNeutral : Nat → {n : Nat} → (context : Ctx Head n) →
    (left right type : Tm Head n) → Option (Certificate R (.compare context left right type))
  | 0, _, _, _, _, _ => none
  | fuel+1, _, context, left, right, _ => do
      let first ← reducer (fuel+1) left
      let second ← reducer (fuel+1) right
      let compared ← neutral fuel context first.val second.val
      return ⟨.neutralAt first.property second.property compared.2.down⟩

def types : Nat → {n : Nat} → (context : Ctx Head n) →
    (left right : Tm Head n) → Option (Certificate R (.types context left right))
  | 0, _, _, _, _ => none
  | fuel+1, _, context, left, right => do
      let first ← reducer (fuel+1) left
      let second ← reducer (fuel+1) right
      match firstShape : first.val, secondShape : second.val with
      | .head a, .head b =>
          if same : a = b ∨ R.headEq a b then
            return ⟨.heads (firstShape ▸ first.property) (secondShape ▸ second.property) same⟩
          else none
      | .pi domain body, .pi domain' body' =>
          let domains ← types fuel context domain domain'
          let bodies ← types fuel (.snoc context domain) body body'
          return ⟨.piTypes (firstShape ▸ first.property) (secondShape ▸ second.property) domains.down bodies.down⟩
      | .sigma domain body, .sigma domain' body' =>
          let domains ← types fuel context domain domain'
          let bodies ← types fuel (.snoc context domain) body body'
          return ⟨.sigmaTypes (firstShape ▸ first.property) (secondShape ▸ second.property) domains.down bodies.down⟩
      | .id carrier a b, .id carrier' a' b' =>
          let carriers ← types fuel context carrier carrier'
          let lefts ← compare fuel context a a' carrier
          let rights ← compare fuel context b b' carrier
          return ⟨.idTypes (firstShape ▸ first.property) (secondShape ▸ second.property) carriers.down lefts.down rights.down⟩
      | _, _ =>
          let compared ← neutral fuel context first.val second.val
          return ⟨.neutralTypes first.property second.property compared.2.down⟩

def neutral : Nat → {n : Nat} → (context : Ctx Head n) →
    (left right : Tm Head n) → Option (NeutralResult R context left right)
  | 0, _, _, _, _ => none
  | fuel+1, _, context, left, right =>
      match left, right with
      | .var first, .var second =>
          if same : first = second then
            some ⟨Ctx.lookup context first, ⟨same ▸ .var first⟩⟩
          else none
      | .const first, .const second =>
          if same : first = second then
            match known : R.constantType first with
            | some type => some ⟨liftClosed type, ⟨same ▸ .const known⟩⟩
            | none => none
          else none
      | .app function argument, .app function' argument' => do
          let compared ← neutral fuel context function function'
          let normal ← reducer (fuel+1) compared.1
          match normalShape : normal.val with
          | .pi domain body =>
              let arguments ← compare fuel context argument argument' domain
              return ⟨inst0 argument body, ⟨.app compared.2.down (normalShape ▸ normal.property) arguments.down⟩⟩
          | _ => none
      | .fst pair, .fst pair' => do
          let compared ← neutral fuel context pair pair'
          let normal ← reducer (fuel+1) compared.1
          match normalShape : normal.val with
          | .sigma domain _ => return ⟨domain, ⟨.fst compared.2.down (normalShape ▸ normal.property)⟩⟩
          | _ => none
      | .snd pair, .snd pair' => do
          let compared ← neutral fuel context pair pair'
          let normal ← reducer (fuel+1) compared.1
          match normalShape : normal.val with
          | .sigma _ body =>
              return ⟨inst0 (.fst pair) body, ⟨.snd compared.2.down (normalShape ▸ normal.property)⟩⟩
          | _ => none
      | _, _ => none

end

def accepts {n : Nat} (fuel : Nat) (context : Ctx Head n) (left right type : Tm Head n) : Bool :=
  (compare R reducer fuel context left right type).isSome

def acceptsTypes {n : Nat} (fuel : Nat) (context : Ctx Head n) (left right : Tm Head n) : Bool :=
  (types R reducer fuel context left right).isSome

theorem accepts_derivation {n : Nat} {fuel : Nat} {context : Ctx Head n}
    {left right type : Tm Head n} (accepted : accepts R reducer fuel context left right type = true) :
    Algorithm R (.compare context left right type) := by
  unfold accepts at accepted
  cases computed : compare R reducer fuel context left right type with
  | none => simp only [computed, Option.isSome_none, Bool.false_eq_true] at accepted
  | some certificate => exact certificate.down

theorem acceptsTypes_derivation {n : Nat} {fuel : Nat} {context : Ctx Head n}
    {left right : Tm Head n} (accepted : acceptsTypes R reducer fuel context left right = true) :
    Algorithm R (.types context left right) := by
  unfold acceptsTypes at accepted
  cases computed : types R reducer fuel context left right with
  | none => simp only [computed, Option.isSome_none, Bool.false_eq_true] at accepted
  | some certificate => exact certificate.down

end ExecutableConversion
end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
