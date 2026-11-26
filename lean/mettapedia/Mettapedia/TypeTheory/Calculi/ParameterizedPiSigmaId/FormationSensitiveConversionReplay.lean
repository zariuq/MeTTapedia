import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveElaboration

/-!
# Exact syntax comparisons in conversion replay

Term comparison observes every constructor, binding slot, declared name,
and head. Conversion replay uses it to join the actual intermediate terms.
The faster comparisons preserve the decoded endpoints and both outcomes of
the public formation-sensitive checker.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

section SyntaxEquality

variable {Head : Type} [DecidableEq Head]

/-- Structural comparison in the common ambient scope. -/
def Tm.sameSyntax : {n : Nat} → Tm Head n → Tm Head n → Bool
  | _, .var i, .var j => i.val == j.val
  | _, .const p, .const q => decide (p = q)
  | _, .head p, .head q => decide (p = q)
  | _, .pi a b, .pi c d | _, .sigma a b, .sigma c d =>
      a.sameSyntax c && b.sameSyntax d
  | _, .id a b c, .id x y z => a.sameSyntax x && b.sameSyntax y && c.sameSyntax z
  | _, .lam p, .lam q => p.sameSyntax q
  | _, .app p q, .app r s | _, .pair p q, .pair r s =>
      p.sameSyntax r && q.sameSyntax s
  | _, .fst p, .fst q | _, .snd p, .snd q | _, .refl p, .refl q => p.sameSyntax q
  | _, _, _ => false

theorem Tm.sameSyntax_iff {n : Nat} (left right : Tm Head n) :
    left.sameSyntax right = true ↔ left = right := by
  induction left with
  | var i => cases right <;> simp [sameSyntax, Fin.ext_iff]
  | const p => cases right <;> simp [sameSyntax]
  | head p => cases right <;> simp [sameSyntax]
  | pi a b ha hb | sigma a b ha hb =>
      cases right <;> simp [sameSyntax, ha, hb]
  | id a b c ha hb hc => cases right <;> simp [sameSyntax, ha, hb, hc, and_assoc]
  | lam p hp => cases right <;> simp [sameSyntax, hp]
  | app p q hp hq | pair p q hp hq =>
      cases right <;> simp [sameSyntax, hp, hq]
  | fst p hp | snd p hp | refl p hp => cases right <;> simp [sameSyntax, hp]

theorem Tm.sameSyntax_eq_decide {n : Nat} (left right : Tm Head n) :
    left.sameSyntax right = decide (left = right) := by
  rw [Bool.eq_iff_iff]
  exact (left.sameSyntax_iff right).trans decide_eq_true_iff.symm

section Controls

example : (Tm.lam (.var 0) : Tm Unit 2).sameSyntax (.lam (.var 0)) = true := by decide
example : (Tm.lam (.var 0) : Tm Unit 2).sameSyntax (.lam (.var 1)) = false := by decide
example : (Tm.fst (.var 0) : Tm Unit 2).sameSyntax (.snd (.var 0)) = false := by decide

end Controls

end SyntaxEquality

namespace StructuralConversionCode.Code

variable {Head : Type} {RootCode : Nat → Type} [DecidableEq Head]
variable (headEq : Head → Head → Prop) [DecidableRel headEq]
variable (decodeRoot : {n : Nat} → RootCode n → Option (Tm Head n × Tm Head n))

private def joinSyntax {n : Nat} :
    Option (Tm Head n × Tm Head n) → Option (Tm Head n × Tm Head n) →
      Option (Tm Head n × Tm Head n)
  | some (left, middle), some (middle', right) =>
      if middle.sameSyntax middle' then some (left, right) else none
  | _, _ => none

private theorem joinSyntax_eq {n : Nat} (left right : Option (Tm Head n × Tm Head n)) :
    joinSyntax left right = joinEndpoints left right := by
  cases left with
  | none => rfl
  | some left =>
      cases right with
      | none => rfl
      | some right =>
          rcases left with ⟨first, middle⟩
          rcases right with ⟨middle', last⟩
          simp [joinSyntax, joinEndpoints, Tm.sameSyntax_iff]

def decodeSyntax {n : Nat} : Code Head RootCode n → Option (Tm Head n × Tm Head n)
  | .single step => step.decode headEq decodeRoot
  | .refl term => some (term, term)
  | .symm code => reverseEndpoints (decodeSyntax code)
  | .trans first second =>
      joinSyntax (decodeSyntax first) (decodeSyntax second)

theorem decodeSyntax_eq {n : Nat} (code : Code Head RootCode n) :
    decodeSyntax headEq decodeRoot code = decode headEq decodeRoot code := by
  induction code <;> simp_all only [decodeSyntax, decode, joinSyntax_eq]

def checkSyntax {n : Nat} (code : Code Head RootCode n) (left right : Tm Head n) : Bool :=
  match decodeSyntax headEq decodeRoot code with
  | none => false
  | some (first, second) => first.sameSyntax left && second.sameSyntax right

theorem checkSyntax_eq {n : Nat} (code : Code Head RootCode n) (left right : Tm Head n) :
    checkSyntax headEq decodeRoot code left right = check headEq decodeRoot code left right := by
  unfold checkSyntax check
  rw [decodeSyntax_eq]
  cases decode headEq decodeRoot code with
  | none => simp
  | some pair => rcases pair with ⟨first, second⟩; simp [Tm.sameSyntax_eq_decide]

section Controls

private def withoutRoot {scope : Nat} (code : Empty) : Option (Tm Unit scope × Tm Unit scope) :=
  nomatch code

private def sameMiddle : Code Unit (fun _ => Empty) 2 :=
  .trans (.refl (.lam (.var 0))) (.refl (.lam (.var 0)))

private def differentMiddle : Code Unit (fun _ => Empty) 2 :=
  .trans (.refl (.lam (.var 0))) (.refl (.lam (.var 1)))

example : decodeSyntax (· = ·) @withoutRoot sameMiddle =
    some (.lam (.var 0), .lam (.var 0)) := by decide

example : decodeSyntax (· = ·) @withoutRoot differentMiddle = none := by decide

end Controls

end StructuralConversionCode.Code

namespace FormationSensitiveElaboration

open FormationSensitive StructuralTypingReplay

variable {Head : Type} (R : Rules Head) [DecidableEq Head]
variable [DecidableRel R.headTyping] [DecidablePred R.isUniverse]
variable [∀ u v w, Decidable (R.join u v w)] [DecidableRel R.cumulative] [DecidableRel R.headEq]
variable (decoder : StructuralConversionCode.RootDecoder R.computation)

private def syntaxConversion {n : Nat} (code : StructuralConversionCode.Code Head decoder.Code n)
    (left right : Tm Head n) : Bool :=
  StructuralConversionCode.Code.checkSyntax R.headEq (fun {m} => @decoder.decode m) code left right

def replayWithSyntaxConversions {n : Nat} (context : Ctx Head n) (term type : Tm Head n)
    (submission : Submission Head decoder.Code n) : Bool :=
  checkJudgment R (syntaxConversion R decoder) context term type submission.context submission.term

theorem replayWithSyntaxConversions_eq {n : Nat} (context : Ctx Head n) (term type : Tm Head n)
    (submission : Submission Head decoder.Code n) :
    replayWithSyntaxConversions R decoder context term type submission = replay R decoder context term type submission := by
  have conversion_eq : (fun {scope} (code : StructuralConversionCode.Code Head decoder.Code scope)
      left right =>
      syntaxConversion R decoder code left right) =
      (fun {_scope} code left right => code.check R.headEq decoder.decode left right) := by
    funext scope code left right
    exact StructuralConversionCode.Code.checkSyntax_eq R.headEq
      (fun {m} => @decoder.decode m) code left right
  simp only [replayWithSyntaxConversions, replay, conversion_eq]

end FormationSensitiveElaboration
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
