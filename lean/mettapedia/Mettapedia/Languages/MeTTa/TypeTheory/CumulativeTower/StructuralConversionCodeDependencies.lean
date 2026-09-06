import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.StructuralConversionCode

/-!
# Root-request-local reuse of structural conversion checking

A supplied code retains finitely many root-decoder requests. Each request
keeps its variable scope, including occurrences below binders. Agreement on
the complete decoder results for those requests preserves the exact decoding
and checking results, whether successful or unsuccessful.

This is a sufficient syntactic support, not a least dependency set. The head
policy, equality decisions, terms, and structural algorithms remain fixed.
No whole-environment agreement or type-formation reuse is asserted. A changed
decoder still needs independent qualification against its intended theory.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace StructuralConversionCode

variable {Head : Type} {RootCode : Nat → Type}

/-- A requested root code retains the scope in which it is decoded. -/
abbrev RootRequest (RootCode : Nat → Type) := Σ n, RootCode n

/-- All root requests retained by a structural step, including binder bodies. -/
def StepCode.rootRequests : {n : Nat} → StepCode Head RootCode n →
    List (RootRequest RootCode)
  | _, .betaPi _ _ => []
  | _, .betaSigmaFst _ _ => []
  | _, .betaSigmaSnd _ _ => []
  | _, .head _ _ => []
  | n, .root code => [⟨n, code⟩]
  | _, .congPiDom code _ => code.rootRequests
  | _, .congPiCod _ code => code.rootRequests
  | _, .congSigmaDom code _ => code.rootRequests
  | _, .congSigmaCod _ code => code.rootRequests
  | _, .congIdTy code _ _ => code.rootRequests
  | _, .congIdLeft _ code _ => code.rootRequests
  | _, .congIdRight _ _ code => code.rootRequests
  | _, .congLam code => code.rootRequests
  | _, .congAppFun code _ => code.rootRequests
  | _, .congAppArg _ code => code.rootRequests
  | _, .congPairFst code _ => code.rootRequests
  | _, .congPairSnd _ code => code.rootRequests
  | _, .congFst code => code.rootRequests
  | _, .congSnd code => code.rootRequests
  | _, .congRefl code => code.rootRequests

/-- Conversion retains every occurrence in both sides of composition. -/
def Code.rootRequests {n : Nat} : Code Head RootCode n → List (RootRequest RootCode)
  | .single step => step.rootRequests
  | .refl _ => []
  | .symm code => code.rootRequests
  | .trans first second => first.rootRequests ++ second.rootRequests

/-- Agreement includes `none` and every endpoint field, not just success tags. -/
def AgreeOn (requests : List (RootRequest RootCode))
    (first second : {n : Nat} → RootCode n → Option (Tm Head n × Tm Head n)) : Prop :=
  ∀ request ∈ requests, first request.2 = second request.2

/-- The finite manifest can itself be checked by comparing decoder results. -/
def agreeOnCheck [DecidableEq Head] (requests : List (RootRequest RootCode))
    (first second : {n : Nat} → RootCode n → Option (Tm Head n × Tm Head n)) : Bool :=
  requests.all fun request => decide (first request.2 = second request.2)

@[simp] theorem agreeOnCheck_iff [DecidableEq Head]
    (requests : List (RootRequest RootCode))
    (first second : {n : Nat} → RootCode n → Option (Tm Head n × Tm Head n)) :
    agreeOnCheck requests first second = true ↔ AgreeOn requests first second := by
  simp [agreeOnCheck, AgreeOn]

namespace StepCode

variable (headEq : Head → Head → Prop) [DecidableRel headEq]
    {first second : {n : Nat} → RootCode n → Option (Tm Head n × Tm Head n)}

/-- Locally agreeing root decoders give the same complete step-decoding result. -/
theorem decode_eq_of_agreeOn {n : Nat} (code : StepCode Head RootCode n) :
    AgreeOn code.rootRequests first second →
      decode headEq first code = decode headEq second code := by
  induction code with
  | betaPi body argument => intro _; rfl
  | betaSigmaFst left right => intro _; rfl
  | betaSigmaSnd left right => intro _; rfl
  | head left right => intro _; rfl
  | root request =>
      intro agree
      exact agree ⟨_, request⟩ (by simp [rootRequests])
  | congPiDom code codomain ih =>
      intro agree
      exact congrArg (mapEndpoints (fun domain => .pi domain codomain)) (ih agree)
  | congPiCod domain code ih =>
      intro agree
      exact congrArg (mapEndpoints (.pi domain)) (ih agree)
  | congSigmaDom code codomain ih =>
      intro agree
      exact congrArg (mapEndpoints (fun domain => .sigma domain codomain)) (ih agree)
  | congSigmaCod domain code ih =>
      intro agree
      exact congrArg (mapEndpoints (.sigma domain)) (ih agree)
  | congIdTy code left right ih =>
      intro agree
      exact congrArg (mapEndpoints (fun type => .id type left right)) (ih agree)
  | congIdLeft type code right ih =>
      intro agree
      exact congrArg (mapEndpoints (fun left => .id type left right)) (ih agree)
  | congIdRight type left code ih =>
      intro agree
      exact congrArg (mapEndpoints (.id type left)) (ih agree)
  | congLam code ih =>
      intro agree
      exact congrArg (mapEndpoints .lam) (ih agree)
  | congAppFun code argument ih =>
      intro agree
      exact congrArg (mapEndpoints (fun function => .app function argument)) (ih agree)
  | congAppArg function code ih =>
      intro agree
      exact congrArg (mapEndpoints (.app function)) (ih agree)
  | congPairFst code secondTerm ih =>
      intro agree
      exact congrArg (mapEndpoints (fun firstTerm => .pair firstTerm secondTerm)) (ih agree)
  | congPairSnd firstTerm code ih =>
      intro agree
      exact congrArg (mapEndpoints (.pair firstTerm)) (ih agree)
  | congFst code ih =>
      intro agree
      exact congrArg (mapEndpoints .fst) (ih agree)
  | congSnd code ih =>
      intro agree
      exact congrArg (mapEndpoints .snd) (ih agree)
  | congRefl code ih =>
      intro agree
      exact congrArg (mapEndpoints .refl) (ih agree)

/-- Both acceptance and rejection reuse the identical code and endpoints. -/
theorem check_eq_of_agreeOn [DecidableEq Head] {n : Nat}
    (code : StepCode Head RootCode n) (left right : Tm Head n)
    (agree : AgreeOn code.rootRequests first second) :
    check headEq first code left right = check headEq second code left right := by
  simp only [check, decode_eq_of_agreeOn headEq code agree]

end StepCode

namespace Code

variable (headEq : Head → Head → Prop) [DecidableRel headEq] [DecidableEq Head]
    {first second : {n : Nat} → RootCode n → Option (Tm Head n × Tm Head n)}

/-- The complete conversion-decoder result is local to the retained root
requests. Failed roots and failed syntactic joins are included. -/
theorem decode_eq_of_agreeOn {n : Nat} (code : Code Head RootCode n) :
    AgreeOn code.rootRequests first second →
      decode headEq first code = decode headEq second code := by
  induction code with
  | single step => exact StepCode.decode_eq_of_agreeOn headEq step
  | refl term => intro _; rfl
  | symm code ih =>
      intro agree
      exact congrArg reverseEndpoints (ih agree)
  | trans left right ihLeft ihRight =>
      intro agree
      have leftEq := ihLeft (fun request member =>
        agree request (List.mem_append.mpr (Or.inl member)))
      have rightEq := ihRight (fun request member =>
        agree request (List.mem_append.mpr (Or.inr member)))
      simp only [decode, leftEq, rightEq]

/-- Exact Boolean reuse requires no success premise: `false` is preserved
just as `true` is. This concerns conversion checking, not type formation. -/
theorem check_eq_of_agreeOn {n : Nat} (code : Code Head RootCode n)
    (left right : Tm Head n) (agree : AgreeOn code.rootRequests first second) :
    check headEq first code left right = check headEq second code left right := by
  simp only [check, decode_eq_of_agreeOn headEq code agree]

/-- A successful finite dependency check suffices for exact verdict reuse. -/
theorem check_eq_of_agreeOnCheck {n : Nat} (code : Code Head RootCode n)
    (left right : Tm Head n)
    (checked : agreeOnCheck code.rootRequests first second = true) :
    check headEq first code left right = check headEq second code left right :=
  check_eq_of_agreeOn headEq code left right ((agreeOnCheck_iff _ _ _).mp checked)

end Code

#print axioms agreeOnCheck_iff
#print axioms StepCode.decode_eq_of_agreeOn
#print axioms StepCode.check_eq_of_agreeOn
#print axioms Code.decode_eq_of_agreeOn
#print axioms Code.check_eq_of_agreeOn
#print axioms Code.check_eq_of_agreeOnCheck

end StructuralConversionCode
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
