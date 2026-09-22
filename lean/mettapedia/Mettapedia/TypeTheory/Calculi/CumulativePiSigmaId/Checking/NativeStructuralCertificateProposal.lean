import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeJudgmentReplay

/-!
# Finite structural certificate proposals for native declarations

This bounded syntax traversal proposes a type and a finite replay tree using
actual declaration types and context lookups. It does not normalize or insert
conversion, and may propose an invalid argument derivation. Admission always
uses the independent complete judgment checker. In particular, failure is not
a refutation of typing, and success alone is not an admission judgment.

Its consumers construct fixed open-schema certificates and independently check
them, rather than selecting certificates from propositional existence proofs.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeJudgmentReplay.CertificateProposal

open Presentation NativeIndexedFamilies

def term : Nat → {n : Nat} → Tower.Ctx n → Tower.Tm n →
    Option (Tower.Tm n × Code n)
  | 0, _, _, _ => none
  | fuel + 1, _, context, subject => do
    match subject with
    | .head h => return ⟨.head (StructuralTypingReplay.TowerDecisions.headTarget h), .headType⟩
    | .var index => return ⟨Ctx.lookup context index, .var⟩
    | .const name =>
        let type ← IntrinsicRelator.rules.constantType name
        let (.head level, formation) ← term fuel .nil type | none
        return ⟨liftClosed type, .const level formation⟩
    | .pi A B =>
        let (.head (.sort u), domain) ← term fuel context A | none
        let (.head (.sort v), body) ← term fuel (.snoc context A) B | none
        return ⟨.head (.sort (.max u v)), .piForm (.sort u) (.sort v) domain body⟩
    | .app function argument =>
        let (.pi A B, functionCode) ← term fuel context function | none
        let (_, argumentCode) ← term fuel context argument
        return ⟨inst0 argument B, .appElim A B functionCode argumentCode⟩
    | .id A left right =>
        let (.head level, formation) ← term fuel context A | none
        let (_, leftCode) ← term fuel context left
        let (_, rightCode) ← term fuel context right
        return ⟨.head level, .idForm level formation leftCode rightCode⟩
    | .refl value =>
        let (A, valueCode) ← term fuel context value
        return ⟨.id A value value, .reflIntro A valueCode⟩
    | _ => none

def context : {n : Nat} → Tower.Ctx n → Option (ContextCode n)
  | _, .nil => some .nil
  | _, .snoc priorContext A => do
      let prior ← context priorContext
      let (.head level, formation) ← term 64 priorContext A | none
      return .snoc prior level formation

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeJudgmentReplay.CertificateProposal
