import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation

/-!
# Executable codes for finite structural conversion

The structural code contains scoped terms, rule selections and composition.
Decoding recurses structurally on that code and uses the existing capture-avoiding
substitution at beta roots. Executable use additionally requires executable root
and head decoders; the native instances supply finite proof-free root data.
The structural algorithm does not search for reductions or normal forms.

Exactness concerns existence of an accepted finite code for conversion. It is
not a decision procedure for existence of such a code, a typing judgment, or
an identification of conversion paths with their endpoints.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace StructuralConversionCode

variable {Head : Type}

/-- Qualification of a finite declaration-root encoding against an independently
authored root relation. Only `Code` and `decode` are executable data. -/
structure RootDecoder (root : RootComputation Head) where
  Code : Nat → Type
  decode : {n : Nat} → Code n → Option (Tm Head n × Tm Head n)
  sound : ∀ {n : Nat} (code : Code n) {left right : Tm Head n},
    decode code = some (left, right) → root.step left right
  complete : ∀ {n : Nat} {left right : Tm Head n},
    root.step left right → ∃ code, decode code = some (left, right)

/-- The ordinary structural rules retain their congruence positions explicitly.
Indices ensure that a code below a binder has the extended variable scope. -/
inductive StepCode (Head : Type) (RootCode : Nat → Type) : Nat → Type where
  | betaPi {n : Nat} (body : Tm Head (n + 1)) (argument : Tm Head n) :
      StepCode Head RootCode n
  | betaSigmaFst {n : Nat} (first second : Tm Head n) : StepCode Head RootCode n
  | betaSigmaSnd {n : Nat} (first second : Tm Head n) : StepCode Head RootCode n
  | head {n : Nat} (left right : Head) : StepCode Head RootCode n
  | root {n : Nat} (code : RootCode n) : StepCode Head RootCode n
  | congPiDom {n : Nat} (code : StepCode Head RootCode n)
      (codomain : Tm Head (n + 1)) : StepCode Head RootCode n
  | congPiCod {n : Nat} (domain : Tm Head n)
      (code : StepCode Head RootCode (n + 1)) : StepCode Head RootCode n
  | congSigmaDom {n : Nat} (code : StepCode Head RootCode n)
      (codomain : Tm Head (n + 1)) : StepCode Head RootCode n
  | congSigmaCod {n : Nat} (domain : Tm Head n)
      (code : StepCode Head RootCode (n + 1)) : StepCode Head RootCode n
  | congIdTy {n : Nat} (code : StepCode Head RootCode n)
      (left right : Tm Head n) : StepCode Head RootCode n
  | congIdLeft {n : Nat} (type : Tm Head n) (code : StepCode Head RootCode n)
      (right : Tm Head n) : StepCode Head RootCode n
  | congIdRight {n : Nat} (type left : Tm Head n)
      (code : StepCode Head RootCode n) : StepCode Head RootCode n
  | congLam {n : Nat} (code : StepCode Head RootCode (n + 1)) :
      StepCode Head RootCode n
  | congAppFun {n : Nat} (code : StepCode Head RootCode n)
      (argument : Tm Head n) : StepCode Head RootCode n
  | congAppArg {n : Nat} (function : Tm Head n)
      (code : StepCode Head RootCode n) : StepCode Head RootCode n
  | congPairFst {n : Nat} (code : StepCode Head RootCode n)
      (second : Tm Head n) : StepCode Head RootCode n
  | congPairSnd {n : Nat} (first : Tm Head n)
      (code : StepCode Head RootCode n) : StepCode Head RootCode n
  | congFst {n : Nat} (code : StepCode Head RootCode n) : StepCode Head RootCode n
  | congSnd {n : Nat} (code : StepCode Head RootCode n) : StepCode Head RootCode n
  | congRefl {n : Nat} (code : StepCode Head RootCode n) : StepCode Head RootCode n

def mapEndpoints {n m : Nat} (wrap : Tm Head n → Tm Head m)
    (endpoints : Option (Tm Head n × Tm Head n)) :
    Option (Tm Head m × Tm Head m) :=
  endpoints.map fun pair => (wrap pair.1, wrap pair.2)

private theorem mapEndpoints_sound {n m : Nat}
    {sourceRelation : Tm Head n → Tm Head n → Prop}
    {targetRelation : Tm Head m → Tm Head m → Prop}
    (wrap : Tm Head n → Tm Head m)
    (preserves : ∀ {left right}, sourceRelation left right →
      targetRelation (wrap left) (wrap right))
    {endpoints : Option (Tm Head n × Tm Head n)}
    (certified : ∀ {left right}, endpoints = some (left, right) →
      sourceRelation left right)
    {left right : Tm Head m}
    (decoded : mapEndpoints wrap endpoints = some (left, right)) :
    targetRelation left right := by
  cases endpoints with
  | none => simp [mapEndpoints] at decoded
  | some pair =>
      rcases pair with ⟨source, target⟩
      simp only [mapEndpoints, Option.map_some, Option.some.injEq,
        Prod.mk.injEq] at decoded
      rcases decoded with ⟨rfl, rfl⟩
      exact preserves (certified rfl)

namespace StepCode

variable {RootCode : Nat → Type}

/-- Decode a finite selected structural step. Head equivalence is decided by
the supplied head policy, not by comparing raw head syntax. -/
def decode (headEq : Head → Head → Prop) [DecidableRel headEq]
    (decodeRoot : {n : Nat} → RootCode n → Option (Tm Head n × Tm Head n)) :
    {n : Nat} → StepCode Head RootCode n → Option (Tm Head n × Tm Head n)
  | _, .betaPi body argument => some (.app (.lam body) argument, inst0 argument body)
  | _, .betaSigmaFst first second => some (.fst (.pair first second), first)
  | _, .betaSigmaSnd first second => some (.snd (.pair first second), second)
  | _, .head left right =>
      if headEq left right then some (.head left, .head right) else none
  | _, .root code => decodeRoot code
  | _, .congPiDom code codomain =>
      mapEndpoints (fun domain => .pi domain codomain) (decode headEq decodeRoot code)
  | _, .congPiCod domain code =>
      mapEndpoints (.pi domain) (decode headEq decodeRoot code)
  | _, .congSigmaDom code codomain =>
      mapEndpoints (fun domain => .sigma domain codomain) (decode headEq decodeRoot code)
  | _, .congSigmaCod domain code =>
      mapEndpoints (.sigma domain) (decode headEq decodeRoot code)
  | _, .congIdTy code left right =>
      mapEndpoints (fun type => .id type left right) (decode headEq decodeRoot code)
  | _, .congIdLeft type code right =>
      mapEndpoints (fun left => .id type left right) (decode headEq decodeRoot code)
  | _, .congIdRight type left code =>
      mapEndpoints (.id type left) (decode headEq decodeRoot code)
  | _, .congLam code => mapEndpoints .lam (decode headEq decodeRoot code)
  | _, .congAppFun code argument =>
      mapEndpoints (fun function => .app function argument) (decode headEq decodeRoot code)
  | _, .congAppArg function code =>
      mapEndpoints (.app function) (decode headEq decodeRoot code)
  | _, .congPairFst code second =>
      mapEndpoints (fun first => .pair first second) (decode headEq decodeRoot code)
  | _, .congPairSnd first code =>
      mapEndpoints (.pair first) (decode headEq decodeRoot code)
  | _, .congFst code => mapEndpoints .fst (decode headEq decodeRoot code)
  | _, .congSnd code => mapEndpoints .snd (decode headEq decodeRoot code)
  | _, .congRefl code => mapEndpoints .refl (decode headEq decodeRoot code)

variable {root : RootComputation Head} {headEq : Head → Head → Prop}
    [DecidableRel headEq]

/-- Every decoded structural code is a step of the original authored relation. -/
theorem decode_sound (decoder : RootDecoder root) {n : Nat}
    (code : StepCode Head decoder.Code n) {left right : Tm Head n}
    (decoded : decode headEq decoder.decode code = some (left, right)) :
    StepCore root headEq left right := by
  induction code with
  | betaPi body argument =>
      simp only [decode, Option.some.injEq, Prod.mk.injEq] at decoded
      rcases decoded with ⟨rfl, rfl⟩
      exact .betaPi body argument
  | betaSigmaFst first second =>
      simp only [decode, Option.some.injEq, Prod.mk.injEq] at decoded
      rcases decoded with ⟨rfl, rfl⟩
      exact .betaSigmaFst first second
  | betaSigmaSnd first second =>
      simp only [decode, Option.some.injEq, Prod.mk.injEq] at decoded
      rcases decoded with ⟨rfl, rfl⟩
      exact .betaSigmaSnd first second
  | head first second =>
      simp only [decode] at decoded
      split at decoded
      · rename_i equality
        simp only [Option.some.injEq, Prod.mk.injEq] at decoded
        rcases decoded with ⟨rfl, rfl⟩
        exact .head equality
      · cases decoded
  | root code => exact .root (decoder.sound code decoded)
  | congPiDom code codomain ih =>
      exact mapEndpoints_sound _ (fun step => StepCore.congPiDom step) ih decoded
  | congPiCod domain code ih =>
      exact mapEndpoints_sound _ (fun step => StepCore.congPiCod step) ih decoded
  | congSigmaDom code codomain ih =>
      exact mapEndpoints_sound _ (fun step => StepCore.congSigmaDom step) ih decoded
  | congSigmaCod domain code ih =>
      exact mapEndpoints_sound _ (fun step => StepCore.congSigmaCod step) ih decoded
  | congIdTy code first second ih =>
      exact mapEndpoints_sound _ (fun step => StepCore.congIdTy step) ih decoded
  | congIdLeft type code second ih =>
      exact mapEndpoints_sound _ (fun step => StepCore.congIdLeft step) ih decoded
  | congIdRight type first code ih =>
      exact mapEndpoints_sound _ (fun step => StepCore.congIdRight step) ih decoded
  | congLam code ih =>
      exact mapEndpoints_sound _ (fun step => StepCore.congLam step) ih decoded
  | congAppFun code argument ih =>
      exact mapEndpoints_sound _ (fun step => StepCore.congAppFun step) ih decoded
  | congAppArg function code ih =>
      exact mapEndpoints_sound _ (fun step => StepCore.congAppArg step) ih decoded
  | congPairFst code second ih =>
      exact mapEndpoints_sound _ (fun step => StepCore.congPairFst step) ih decoded
  | congPairSnd first code ih =>
      exact mapEndpoints_sound _ (fun step => StepCore.congPairSnd step) ih decoded
  | congFst code ih =>
      exact mapEndpoints_sound _ (fun step => StepCore.congFst step) ih decoded
  | congSnd code ih =>
      exact mapEndpoints_sound _ (fun step => StepCore.congSnd step) ih decoded
  | congRefl code ih =>
      exact mapEndpoints_sound _ (fun step => StepCore.congRefl step) ih decoded

/-- Every original structural step is represented by a finite scoped code. -/
theorem decode_complete (decoder : RootDecoder root) {n : Nat}
    {left right : Tm Head n} (step : StepCore root headEq left right) :
    ∃ code, decode headEq decoder.decode code = some (left, right) := by
  induction step with
  | betaPi body argument => exact ⟨.betaPi body argument, rfl⟩
  | betaSigmaFst first second => exact ⟨.betaSigmaFst first second, rfl⟩
  | betaSigmaSnd first second => exact ⟨.betaSigmaSnd first second, rfl⟩
  | @head n first second equality =>
      exact ⟨.head first second, by simp [decode, equality]⟩
  | root step =>
      obtain ⟨code, decoded⟩ := decoder.complete step
      exact ⟨.root code, decoded⟩
  | @congPiDom n domain domain' codomain step ih =>
      obtain ⟨code, decoded⟩ := ih
      exact ⟨.congPiDom code codomain, by simp [decode, decoded, mapEndpoints]⟩
  | @congPiCod n domain codomain codomain' step ih =>
      obtain ⟨code, decoded⟩ := ih
      exact ⟨.congPiCod domain code, by simp [decode, decoded, mapEndpoints]⟩
  | @congSigmaDom n domain domain' codomain step ih =>
      obtain ⟨code, decoded⟩ := ih
      exact ⟨.congSigmaDom code codomain, by simp [decode, decoded, mapEndpoints]⟩
  | @congSigmaCod n domain codomain codomain' step ih =>
      obtain ⟨code, decoded⟩ := ih
      exact ⟨.congSigmaCod domain code, by simp [decode, decoded, mapEndpoints]⟩
  | @congIdTy n type type' first second step ih =>
      obtain ⟨code, decoded⟩ := ih
      exact ⟨.congIdTy code first second, by simp [decode, decoded, mapEndpoints]⟩
  | @congIdLeft n type first first' second step ih =>
      obtain ⟨code, decoded⟩ := ih
      exact ⟨.congIdLeft type code second, by simp [decode, decoded, mapEndpoints]⟩
  | @congIdRight n type first second second' step ih =>
      obtain ⟨code, decoded⟩ := ih
      exact ⟨.congIdRight type first code, by simp [decode, decoded, mapEndpoints]⟩
  | congLam step ih =>
      obtain ⟨code, decoded⟩ := ih
      exact ⟨.congLam code, by simp [decode, decoded, mapEndpoints]⟩
  | @congAppFun n function function' argument step ih =>
      obtain ⟨code, decoded⟩ := ih
      exact ⟨.congAppFun code argument, by simp [decode, decoded, mapEndpoints]⟩
  | @congAppArg n function argument argument' step ih =>
      obtain ⟨code, decoded⟩ := ih
      exact ⟨.congAppArg function code, by simp [decode, decoded, mapEndpoints]⟩
  | @congPairFst n first first' second step ih =>
      obtain ⟨code, decoded⟩ := ih
      exact ⟨.congPairFst code second, by simp [decode, decoded, mapEndpoints]⟩
  | @congPairSnd n first second second' step ih =>
      obtain ⟨code, decoded⟩ := ih
      exact ⟨.congPairSnd first code, by simp [decode, decoded, mapEndpoints]⟩
  | congFst step ih =>
      obtain ⟨code, decoded⟩ := ih
      exact ⟨.congFst code, by simp [decode, decoded, mapEndpoints]⟩
  | congSnd step ih =>
      obtain ⟨code, decoded⟩ := ih
      exact ⟨.congSnd code, by simp [decode, decoded, mapEndpoints]⟩
  | congRefl step ih =>
      obtain ⟨code, decoded⟩ := ih
      exact ⟨.congRefl code, by simp [decode, decoded, mapEndpoints]⟩

/-- Forward-step checking is kept distinct from symmetric conversion. -/
def check [DecidableEq Head]
    (headEq : Head → Head → Prop) [DecidableRel headEq]
    (decodeRoot : {n : Nat} → RootCode n → Option (Tm Head n × Tm Head n))
    {n : Nat} (code : StepCode Head RootCode n) (left right : Tm Head n) : Bool :=
  decide (decode headEq decodeRoot code = some (left, right))

theorem check_sound [DecidableEq Head] (decoder : RootDecoder root) {n : Nat}
    {code : StepCode Head decoder.Code n} {left right : Tm Head n}
    (checked : check headEq decoder.decode code left right = true) :
    StepCore root headEq left right :=
  decode_sound decoder code (of_decide_eq_true checked)

theorem step_iff_checked [DecidableEq Head] (decoder : RootDecoder root) {n : Nat}
    {left right : Tm Head n} :
    StepCore root headEq left right ↔
      ∃ code, check headEq decoder.decode code left right = true := by
  constructor
  · intro step
    obtain ⟨code, decoded⟩ := decode_complete decoder step
    exact ⟨code, by simp only [check, decoded, decide_true]⟩
  · rintro ⟨code, checked⟩
    exact check_sound decoder checked

end StepCode

/-- Finite conversion evidence retains the selected steps and composition tree. -/
inductive Code (Head : Type) (RootCode : Nat → Type) (n : Nat) : Type where
  | single (step : StepCode Head RootCode n)
  | refl (term : Tm Head n)
  | symm (code : Code Head RootCode n)
  | trans (first second : Code Head RootCode n)

def reverseEndpoints {n : Nat} (endpoints : Option (Tm Head n × Tm Head n)) :
    Option (Tm Head n × Tm Head n) :=
  endpoints.map fun pair => (pair.2, pair.1)

/-- Composition checks the actual intermediate term, including its metadata. -/
def joinEndpoints [DecidableEq Head] {n : Nat}
    (first second : Option (Tm Head n × Tm Head n)) :
    Option (Tm Head n × Tm Head n) :=
  match first, second with
  | some (left, middle), some (middle', right) =>
      if middle = middle' then some (left, right) else none
  | _, _ => none

private theorem reverseEndpoints_sound {n : Nat}
    {relation : Tm Head n → Tm Head n → Prop}
    (symmetric : ∀ {left right}, relation left right → relation right left)
    {endpoints : Option (Tm Head n × Tm Head n)}
    (certified : ∀ {left right}, endpoints = some (left, right) → relation left right)
    {left right : Tm Head n}
    (decoded : reverseEndpoints endpoints = some (left, right)) :
    relation left right := by
  cases endpoints with
  | none => simp [reverseEndpoints] at decoded
  | some pair =>
      rcases pair with ⟨source, target⟩
      simp only [reverseEndpoints, Option.map_some, Option.some.injEq,
        Prod.mk.injEq] at decoded
      rcases decoded with ⟨rfl, rfl⟩
      exact symmetric (certified rfl)

private theorem joinEndpoints_sound [DecidableEq Head] {n : Nat}
    {relation : Tm Head n → Tm Head n → Prop}
    (transitive : ∀ {left middle right}, relation left middle →
      relation middle right → relation left right)
    {first second : Option (Tm Head n × Tm Head n)}
    (firstCertified : ∀ {left right}, first = some (left, right) → relation left right)
    (secondCertified : ∀ {left right}, second = some (left, right) → relation left right)
    {left right : Tm Head n}
    (decoded : joinEndpoints first second = some (left, right)) :
    relation left right := by
  cases first with
  | none => simp [joinEndpoints] at decoded
  | some firstPair =>
      rcases firstPair with ⟨source, middle⟩
      cases second with
      | none => simp [joinEndpoints] at decoded
      | some secondPair =>
          rcases secondPair with ⟨middle', target⟩
          simp only [joinEndpoints] at decoded
          split at decoded
          · rename_i equal
            subst middle'
            simp only [Option.some.injEq, Prod.mk.injEq] at decoded
            rcases decoded with ⟨rfl, rfl⟩
            exact transitive (firstCertified rfl) (secondCertified rfl)
          · cases decoded

namespace Code

variable {RootCode : Nat → Type} [DecidableEq Head]

/-- Total verification of a supplied finite conversion code. -/
def decode (headEq : Head → Head → Prop) [DecidableRel headEq]
    (decodeRoot : {n : Nat} → RootCode n → Option (Tm Head n × Tm Head n))
    {n : Nat} : Code Head RootCode n → Option (Tm Head n × Tm Head n)
  | .single step => step.decode headEq decodeRoot
  | .refl term => some (term, term)
  | .symm code => reverseEndpoints (decode headEq decodeRoot code)
  | .trans first second =>
      joinEndpoints (decode headEq decodeRoot first) (decode headEq decodeRoot second)

/-- Test both claimed endpoints against the result of decoding. -/
def check (headEq : Head → Head → Prop) [DecidableRel headEq]
    (decodeRoot : {n : Nat} → RootCode n → Option (Tm Head n × Tm Head n))
    {n : Nat} (code : Code Head RootCode n) (left right : Tm Head n) : Bool :=
  decide (decode headEq decodeRoot code = some (left, right))

variable {root : RootComputation Head} {headEq : Head → Head → Prop}
    [DecidableRel headEq]

theorem decode_sound (decoder : RootDecoder root) {n : Nat}
    (code : Code Head decoder.Code n) {left right : Tm Head n}
    (decoded : decode headEq decoder.decode code = some (left, right)) :
    Conv headEq left right root := by
  induction code generalizing left right with
  | single step => exact .rel _ _ (step.decode_sound decoder decoded)
  | refl term =>
      simp only [decode, Option.some.injEq, Prod.mk.injEq] at decoded
      rcases decoded with ⟨rfl, rfl⟩
      exact .refl term
  | symm code ih =>
      exact reverseEndpoints_sound (fun conversion => .symm _ _ conversion) ih decoded
  | trans first second ihFirst ihSecond =>
      exact joinEndpoints_sound (fun first second => .trans _ _ _ first second)
        ihFirst ihSecond decoded

/-- All original conversions have a finite code. This existential theorem
does not supply a total algorithm for finding one or refuting its existence. -/
theorem decode_complete (decoder : RootDecoder root) {n : Nat}
    {left right : Tm Head n} (conversion : Conv headEq left right root) :
    ∃ code, decode headEq decoder.decode code = some (left, right) := by
  induction conversion with
  | rel source target step =>
      obtain ⟨code, decoded⟩ := StepCode.decode_complete decoder step
      exact ⟨.single code, decoded⟩
  | refl term => exact ⟨.refl term, rfl⟩
  | symm source target conversion ih =>
      obtain ⟨code, decoded⟩ := ih
      exact ⟨.symm code, by simp [decode, decoded, reverseEndpoints]⟩
  | trans source middle target first second ihFirst ihSecond =>
      obtain ⟨firstCode, firstDecoded⟩ := ihFirst
      obtain ⟨secondCode, secondDecoded⟩ := ihSecond
      exact ⟨.trans firstCode secondCode,
        by simp [decode, firstDecoded, secondDecoded, joinEndpoints]⟩

theorem check_sound (decoder : RootDecoder root) {n : Nat}
    {code : Code Head decoder.Code n} {left right : Tm Head n}
    (checked : check headEq decoder.decode code left right = true) :
    Conv headEq left right root :=
  decode_sound decoder code (of_decide_eq_true checked)

/-- The executable checker accepts exactly the finite evidence for the
independently authored conversion relation, on all scoped raw terms. -/
theorem conversion_iff_checked (decoder : RootDecoder root) {n : Nat}
    {left right : Tm Head n} :
    Conv headEq left right root ↔
      ∃ code, check headEq decoder.decode code left right = true := by
  constructor
  · intro conversion
    obtain ⟨code, decoded⟩ := decode_complete decoder conversion
    exact ⟨code, by simp only [check, decoded, decide_true]⟩
  · rintro ⟨code, checked⟩
    exact check_sound decoder checked

end Code

#print axioms StepCode.decode_sound
#print axioms StepCode.decode_complete
#print axioms StepCode.check_sound
#print axioms StepCode.step_iff_checked
#print axioms Code.decode_sound
#print axioms Code.decode_complete
#print axioms Code.check_sound
#print axioms Code.conversion_iff_checked

end StructuralConversionCode
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
