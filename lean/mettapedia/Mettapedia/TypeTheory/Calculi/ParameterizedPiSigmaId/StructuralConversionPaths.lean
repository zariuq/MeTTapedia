import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionCodeCongruence
import Mettapedia.Logic.Relation.PathConfluence

/-!
# Checked conversion codes as proof-retaining paths

Each edge is the actual finite structural step code paired with its successful
endpoint decoding. A conversion code computes a path in the symmetrized graph:
symmetry reverses a path, and transitivity composes paths only at the decoded
common endpoint. Directed paths re-encode as accepted conversion certificates.

This is the input boundary for a computed Church--Rosser construction. It does
not assume a diamond for authored steps: a native application must map these
paths into its auxiliary parallel graph and supply that graph's executable
diamond separately.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace StructuralConversionCode

open Quiver

variable {Head : Type} {RootCode : Nat → Type}

/-- Vertices are existing terms. The graph instance fixes the decoder
whose endpoint check each retained edge must pass. -/
def StepGraph (_headEq : Head → Head → Prop)
    (_decodeRoot : {n : Nat} → RootCode n → Option (Tm Head n × Tm Head n)) (n : Nat) :=
  Tm Head n

variable [DecidableEq Head] (headEq : Head → Head → Prop) [DecidableRel headEq]
variable (decodeRoot : {n : Nat} → RootCode n → Option (Tm Head n × Tm Head n))

instance stepGraphDecidableEq (n : Nat) : DecidableEq (StepGraph headEq decodeRoot n) :=
  inferInstanceAs (DecidableEq (Tm Head n))

instance stepGraphQuiver (n : Nat) : Quiver (StepGraph headEq decodeRoot n) where
  Hom left right := {code : StepCode Head RootCode n //
    code.decode headEq decodeRoot = some (left, right)}

private def transport {V : Type} [Quiver V] {a b c d : V}
    (source : a = c) (target : b = d) (path : Path a b) : Path c d :=
  source ▸ target ▸ path

private theorem transport_length {V : Type} [Quiver V] {a b c d : V}
    (source : a = c) (target : b = d) (path : Path a b) :
    (transport source target path).length = path.length := by
  cases source
  cases target
  rfl

/-- Compute the path from the input code; the equality proof only excludes
malformed branches and transports the decoded endpoint indices. -/
def Code.toZigzag {n : Nat} (code : Code Head RootCode n) {left right : Tm Head n}
    (accepted : code.decode headEq decodeRoot = some (left, right)) :
    @Path (Symmetrify (StepGraph headEq decodeRoot n)) _ left right :=
  match code with
  | .single step => .cons .nil (.inl ⟨step, accepted⟩)
  | .refl term => by cases accepted; exact .nil
  | .symm code =>
      match decoded : code.decode headEq decodeRoot with
      | none => False.elim (by simp [Code.decode, decoded, reverseEndpoints] at accepted)
      | some (a, b) =>
          let equal : (b, a) = (left, right) := by
            simpa only [Code.decode, decoded, reverseEndpoints, Option.map_some,
              Option.some.injEq] using accepted
          transport (congrArg Prod.fst equal) (congrArg Prod.snd equal)
            (toZigzag code decoded).reverse
  | .trans first second =>
      match firstDecoded : first.decode headEq decodeRoot,
          secondDecoded : second.decode headEq decodeRoot with
      | some (a, b), some (c, d) =>
          if same : b = c then
            let equal : (a, d) = (left, right) := by
              simpa only [Code.decode, firstDecoded, secondDecoded, joinEndpoints, same,
                ↓reduceIte, Option.some.injEq] using accepted
            transport (congrArg Prod.fst equal) (congrArg Prod.snd equal)
              ((toZigzag first firstDecoded).comp
                (transport same.symm rfl (toZigzag second secondDecoded)))
          else False.elim (by
            simp [Code.decode, firstDecoded, secondDecoded, joinEndpoints, same] at accepted)
      | none, _ => False.elim (by simp [Code.decode, firstDecoded, joinEndpoints] at accepted)
      | some _, none => False.elim (by
          simp [Code.decode, firstDecoded, secondDecoded, joinEndpoints] at accepted)
termination_by structural code

def Code.stepCount {n : Nat} : Code Head RootCode n → Nat
  | .single _ => 1
  | .refl _ => 0
  | .symm code => code.stepCount
  | .trans first second => first.stepCount + second.stepCount

/-- Flattening forgets grouping but neither drops nor duplicates selected
step occurrences, including cancellation loops at equal endpoints. -/
theorem Code.toZigzag_length {n : Nat} (code : Code Head RootCode n) {left right : Tm Head n}
    (accepted : code.decode headEq decodeRoot = some (left, right)) :
    (code.toZigzag headEq decodeRoot accepted).length = code.stepCount := by
  induction code generalizing left right with
  | single step => rfl
  | refl term => cases accepted; rfl
  | symm code ih =>
      unfold toZigzag
      split
      · rename_i decoded
        simp [Code.decode, decoded, reverseEndpoints] at accepted
      · rename_i a b decoded
        dsimp only
        exact (transport_length _ _ _).trans
          ((Mettapedia.Logic.Relation.PathConfluence.reverse_length
            (code.toZigzag headEq decodeRoot decoded)).trans (ih decoded))
  | trans first second ihFirst ihSecond =>
      unfold toZigzag
      split
      · rename_i a b c d firstDecoded secondDecoded
        split
        · dsimp only
          refine (transport_length _ _ _).trans ((Path.length_comp _ _).trans ?_)
          exact congrArg₂ (· + ·) (ihFirst firstDecoded)
            ((transport_length _ _ _).trans (ihSecond secondDecoded))
        · rename_i different
          simp [Code.decode, firstDecoded, secondDecoded, joinEndpoints, different] at accepted
      · rename_i firstDecoded
        simp [Code.decode, firstDecoded, joinEndpoints] at accepted
      · rename_i pair firstDecoded secondDecoded
        simp [Code.decode, firstDecoded, secondDecoded, joinEndpoints] at accepted

/-- Emit a finite conversion certificate for the actual directed path. -/
def directedCode {n : Nat} {left right : StepGraph headEq decodeRoot n}
    (path : Path left right) : Code Head RootCode n := by
  induction path with
  | nil => exact .refl left
  | cons path edge ih => exact .trans ih (.single edge.val)

theorem directedCode_checked {n : Nat} {left right : StepGraph headEq decodeRoot n}
    (path : Path left right) :
    (directedCode headEq decodeRoot path).check headEq decodeRoot left right = true := by
  induction path with
  | nil => exact Code.check_refl headEq decodeRoot left
  | cons path edge ih =>
      apply Code.check_trans headEq decodeRoot ih
      exact decide_eq_true edge.property

/-- Re-encode a symmetric path, retaining the orientation of each checked
edge. The conversion tree is associated along the path, not reconstructed. -/
def zigzagCode {n : Nat} {left right : Symmetrify (StepGraph headEq decodeRoot n)}
    (path : @Path (Symmetrify (StepGraph headEq decodeRoot n)) _ left right) : Code Head RootCode n := by
  induction path with
  | nil => exact .refl left
  | cons path edge ih =>
      change Sum _ _ at edge
      cases edge with
      | inl forward => exact .trans ih (.single forward.val)
      | inr backward => exact .trans ih (.symm (.single backward.val))

theorem zigzagCode_checked {n : Nat} {left right : Symmetrify (StepGraph headEq decodeRoot n)}
    (path : @Path (Symmetrify (StepGraph headEq decodeRoot n)) _ left right) :
    (zigzagCode headEq decodeRoot path).check headEq decodeRoot left right = true := by
  induction path with
  | nil => exact Code.check_refl headEq decodeRoot left
  | cons path edge ih =>
      change Sum _ _ at edge
      cases edge with
      | inl forward => exact Code.check_trans headEq decodeRoot ih (decide_eq_true forward.property)
      | inr backward =>
          exact Code.check_trans headEq decodeRoot ih
            (Code.check_symm headEq decodeRoot (decide_eq_true backward.property))

/-- Return conversion evidence from two supplied directed paths with an
identical common endpoint. The paths are retained; no confluence is inferred. -/
def joinedCode {n : Nat} {left right : StepGraph headEq decodeRoot n}
    (joined : Mettapedia.Logic.Relation.PathConfluence.Join left right) : Code Head RootCode n :=
  .trans (directedCode headEq decodeRoot joined.fromLeft)
    (.symm (directedCode headEq decodeRoot joined.fromRight))

theorem joinedCode_checked {n : Nat} {left right : StepGraph headEq decodeRoot n}
    (joined : Mettapedia.Logic.Relation.PathConfluence.Join left right) :
    (joinedCode headEq decodeRoot joined).check headEq decodeRoot left right = true :=
  Code.check_trans headEq decodeRoot (directedCode_checked headEq decodeRoot joined.fromLeft)
    (Code.check_symm headEq decodeRoot (directedCode_checked headEq decodeRoot joined.fromRight))

#print axioms Code.toZigzag
#print axioms Code.toZigzag_length
#print axioms directedCode_checked
#print axioms zigzagCode_checked
#print axioms joinedCode_checked

end StructuralConversionCode
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
