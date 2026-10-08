import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ExecutableChecking
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.WrittenDomains

/-!
# Executable checking that retains written lambda domains

All source constructors are examined before their annotated typing is returned.
In particular, synthesis checks a written domain as a type, and checking also
compares it with the expected function domain. The normalization-model proofs
are fixed qualification data for the selected rule package; they are erased
from execution. No typing tree is supplied with a source term.

The public boundary reconstructs context formation and source expected-type
formation. Failure of this finite-fuel procedure establishes no negative
judgment by itself.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality.Normalization.ExecutableWrittenChecking

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] (S : Setting Head L)
  [DecidableEq Head] [DecidableRel S.R.headEq]
  [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
  (headSteps : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R)
  (declared : DeclaredTypesFormed S.R)
variable (choices : ExecutableChecking.HeadChoices S.R)
  (evaluator : ExecutableReduction.Reducer S.R)

abbrev SynthResult {n : Nat} (context : Ctx Head n) (term : ATm Head n) :=
  (type : Tm Head n) × PLift (ATyped S.R context term type)

abbrev CheckResult {n : Nat} (context : Ctx Head n) (term : ATm Head n) (type : Tm Head n) :=
  PLift (ATyped S.R context term type)

abbrev FormationResult {n : Nat} (context : Ctx Head n) (term : ATm Head n) :=
  (head : Head) × PLift (S.R.isUniverse head ∧ ATyped S.R context term (.head head))

/-- Recognition of the synthesized formation level uses the computed normal
form; the model proves that its conversion preserves annotated typing. -/
def asType {n : Nat} (fuel : Nat) (context : Ctx Head n) (formed : CtxFormed S.R context)
    (term : ATm Head n) (inferred : SynthResult S context term) :
    Option (FormationResult S context term) := do
  let level ← ExecutableChecking.asUniverse S.R evaluator fuel inferred.1
  return ⟨level.val, ⟨level.property.1, ATyped.convTypeEq inferred.2.down
    (Reduces.typeEq facts roots headSteps formed level.property.2
      (Typed.isType inferred.2.down.erase formed))⟩⟩

omit [DecidableEq Head] [DecidableRel S.R.headEq]
    [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative] in
private theorem piFormation {n : Nat} {context : Ctx Head n} {domain : Tm Head n}
    {body : Tm Head (n+1)} (domainFormed : IsType S.R context domain)
    (bodyFormed : IsType S.R (.snoc context domain) body) : IsType S.R context (.pi domain body) := by
  obtain ⟨u, hu, domainTyped⟩ := domainFormed
  obtain ⟨v, hv, bodyTyped⟩ := bodyFormed
  obtain ⟨w, joined⟩ := S.levels.join_exists hu hv
  exact ⟨w, (S.levels.join_level joined).1, .piForm domainTyped hu bodyTyped hv joined⟩

omit [DecidableEq Head] [DecidableRel S.R.headEq]
    [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative] in
include facts roots headSteps algebra in
private theorem writtenLambda {n : Nat} {context : Ctx Head n} {written : ATm Head n}
    {domain : Tm Head n} {body : ATm Head (n+1)} {codomain : Tm Head (n+1)} {u : Head}
    (formed : CtxFormed S.R context) (writtenTyped : ATyped S.R context written (.head u))
    (hu : S.R.isUniverse u) (compared : Algorithm S.R (.types context written.erase domain))
    (functionFormed : IsType S.R context (.pi domain codomain))
    (bodyTyped : ATyped S.R (.snoc context domain) body codomain) :
    ATyped S.R context (.lamTyped written body) (.pi domain codomain) := by
  obtain ⟨v, hv, domainTyped⟩ := functionFormed.pi_parts.1
  obtain ⟨w, joined⟩ := S.levels.join_exists hu hv
  obtain ⟨aboveWritten, aboveDomain⟩ := S.levels.join_upper joined
  have hw := (S.levels.join_level joined).1
  have agreement := Algorithm.sound facts roots headSteps algebra compared formed hw
    (.cumul writtenTyped.erase aboveWritten) (.cumul domainTyped aboveDomain)
  obtain ⟨s, hs, functionTyped⟩ := functionFormed
  exact .lamTyped (.cumul writtenTyped aboveWritten) hw agreement functionTyped hs bodyTyped

mutual

def synth : Nat → {n : Nat} → (context : Ctx Head n) → CtxFormed S.R context →
    (term : ATm Head n) → Option (SynthResult S context term)
  | 0, _, _, _, _ => none
  | fuel+1, _, context, formed, term => match term with
      | .var index => some ⟨Ctx.lookup context index, ⟨.var index⟩⟩
      | .const name => match known : S.R.constantType name with
          | some type => some ⟨liftClosed type, ⟨by
              obtain ⟨u, hu, typed⟩ := declared known
              exact .const known typed hu⟩⟩
          | none => none
      | .head head => do
          let chosen ← choices.typing head
          return ⟨.head chosen.val, ⟨.headType chosen.property⟩⟩
      | .pi domain body => do
          let domainType ← synth fuel context formed domain
          let domainLevel ← asType S facts roots headSteps evaluator (fuel+1)
            context formed domain domainType
          let extended := CtxFormed.snoc formed
            ⟨domainLevel.1, domainLevel.2.down.1, domainLevel.2.down.2.erase⟩
          let bodyType ← synth fuel (.snoc context domain.erase) extended body
          let bodyLevel ← asType S facts roots headSteps evaluator (fuel+1)
            (.snoc context domain.erase) extended body bodyType
          let joined ← choices.join domainLevel.1 bodyLevel.1
          return ⟨.head joined.val, ⟨.piForm domainLevel.2.down.2 domainLevel.2.down.1
            bodyLevel.2.down.2 bodyLevel.2.down.1 joined.property⟩⟩
      | .sigma domain body => do
          let domainType ← synth fuel context formed domain
          let domainLevel ← asType S facts roots headSteps evaluator (fuel+1)
            context formed domain domainType
          let extended := CtxFormed.snoc formed
            ⟨domainLevel.1, domainLevel.2.down.1, domainLevel.2.down.2.erase⟩
          let bodyType ← synth fuel (.snoc context domain.erase) extended body
          let bodyLevel ← asType S facts roots headSteps evaluator (fuel+1)
            (.snoc context domain.erase) extended body bodyType
          let joined ← choices.join domainLevel.1 bodyLevel.1
          return ⟨.head joined.val, ⟨.sigmaForm domainLevel.2.down.2 domainLevel.2.down.1
            bodyLevel.2.down.2 bodyLevel.2.down.1 joined.property⟩⟩
      | .id carrier first second => do
          let carrierType ← synth fuel context formed carrier
          let carrierLevel ← asType S facts roots headSteps evaluator (fuel+1)
            context formed carrier carrierType
          let carrierFormed : IsType S.R context carrier.erase :=
            ⟨carrierLevel.1, carrierLevel.2.down.1, carrierLevel.2.down.2.erase⟩
          let firstChecked ← check fuel context formed first carrier.erase carrierFormed
          let secondChecked ← check fuel context formed second carrier.erase carrierFormed
          return ⟨.head carrierLevel.1, ⟨.idForm carrierLevel.2.down.2 carrierLevel.2.down.1
            firstChecked.down secondChecked.down⟩⟩
      | .lamTyped written body => do
          let writtenType ← synth fuel context formed written
          let writtenLevel ← asType S facts roots headSteps evaluator (fuel+1)
            context formed written writtenType
          let domainFormed : IsType S.R context written.erase :=
            ⟨writtenLevel.1, writtenLevel.2.down.1, writtenLevel.2.down.2.erase⟩
          let extended := CtxFormed.snoc formed domainFormed
          let bodyType ← synth fuel (.snoc context written.erase) extended body
          return ⟨.pi written.erase bodyType.1, ⟨by
            obtain ⟨u, hu, functionTyped⟩ := piFormation S domainFormed
              (Typed.isType bodyType.2.down.erase extended)
            exact .lamTyped writtenLevel.2.down.2 writtenLevel.2.down.1
              (.refl writtenLevel.2.down.2.erase) functionTyped hu bodyType.2.down⟩⟩
      | .lamBare _ => none
      | .app (.lamBare body) argument => do
          let argumentType ← synth fuel context formed argument
          let domainFormed := Typed.isType argumentType.2.down.erase formed
          let extended := CtxFormed.snoc formed domainFormed
          let bodyType ← synth fuel (.snoc context argumentType.1) extended body
          return ⟨inst0 argument.erase bodyType.1, ⟨by
            obtain ⟨u, hu, functionTyped⟩ := piFormation S domainFormed
              (Typed.isType bodyType.2.down.erase extended)
            exact .appElim (.lamBare functionTyped hu bodyType.2.down) argumentType.2.down⟩⟩
      | .app function argument => do
          let functionType ← synth fuel context formed function
          let normal ← evaluator (fuel+1) functionType.1
          match shape : normal.val with
          | .pi domain body =>
              let change := Reduces.typeEq facts roots headSteps formed (shape ▸ normal.property)
                (Typed.isType functionType.2.down.erase formed)
              let argumentChecked ← check fuel context formed argument domain
                (TypeEq.isType change formed).2.pi_parts.1
              return ⟨inst0 argument.erase body,
                ⟨.appElim (ATyped.convTypeEq functionType.2.down change) argumentChecked.down⟩⟩
          | _ => none
      | .fst pair => do
          let pairType ← synth fuel context formed pair
          let normal ← evaluator (fuel+1) pairType.1
          match shape : normal.val with
          | .sigma domain _ =>
              let change := Reduces.typeEq facts roots headSteps formed (shape ▸ normal.property)
                (Typed.isType pairType.2.down.erase formed)
              return ⟨domain, ⟨.fstElim (ATyped.convTypeEq pairType.2.down change)⟩⟩
          | _ => none
      | .snd pair => do
          let pairType ← synth fuel context formed pair
          let normal ← evaluator (fuel+1) pairType.1
          match shape : normal.val with
          | .sigma _ body =>
              let change := Reduces.typeEq facts roots headSteps formed (shape ▸ normal.property)
                (Typed.isType pairType.2.down.erase formed)
              return ⟨inst0 (.fst pair.erase) body,
                ⟨.sndElim (ATyped.convTypeEq pairType.2.down change)⟩⟩
          | _ => none
      | .refl subject => do
          let inferred ← synth fuel context formed subject
          return ⟨.id inferred.1 subject.erase subject.erase, ⟨.reflIntro inferred.2.down⟩⟩
      | .pair _ _ => none

def check : Nat → {n : Nat} → (context : Ctx Head n) → CtxFormed S.R context →
    (term : ATm Head n) → (type : Tm Head n) → IsType S.R context type →
    Option (CheckResult S context term type)
  | 0, _, _, _, _, _, _ => none
  | fuel+1, _, context, formed, term, type, typeFormed => match term with
      | .lamBare body => do
          let normal ← evaluator (fuel+1) type
          match shape : normal.val with
          | .pi domain codomain =>
              let change := Reduces.typeEq facts roots headSteps formed (shape ▸ normal.property) typeFormed
              let piFormed := (TypeEq.isType change formed).2
              let checked ← check fuel (.snoc context domain)
                (.snoc formed piFormed.pi_parts.1) body codomain piFormed.pi_parts.2
              return ⟨by
                obtain ⟨u, hu, functionTyped⟩ := piFormed
                exact ATyped.convTypeEq (.lamBare functionTyped hu checked.down) change.symm⟩
          | _ => none
      | .lamTyped written body => do
          let writtenType ← synth fuel context formed written
          let writtenLevel ← asType S facts roots headSteps evaluator (fuel+1)
            context formed written writtenType
          let normal ← evaluator (fuel+1) type
          match shape : normal.val with
          | .pi domain codomain =>
              let compared ← ExecutableConversion.types S.R evaluator fuel context written.erase domain
              let change := Reduces.typeEq facts roots headSteps formed (shape ▸ normal.property) typeFormed
              let piFormed := (TypeEq.isType change formed).2
              let checked ← check fuel (.snoc context domain)
                (.snoc formed piFormed.pi_parts.1) body codomain piFormed.pi_parts.2
              return ⟨ATyped.convTypeEq (writtenLambda S facts roots headSteps algebra formed
                writtenLevel.2.down.2 writtenLevel.2.down.1 compared.down piFormed checked.down)
                change.symm⟩
          | _ => none
      | .pair first second => do
          let normal ← evaluator (fuel+1) type
          match shape : normal.val with
          | .sigma domain codomain =>
              let change := Reduces.typeEq facts roots headSteps formed (shape ▸ normal.property) typeFormed
              let sigmaFormed := (TypeEq.isType change formed).2
              let firstChecked ← check fuel context formed first domain sigmaFormed.sigma_parts.1
              let secondChecked ← check fuel context formed second (inst0 first.erase codomain) (by
                obtain ⟨v, hv, typed⟩ := sigmaFormed.sigma_parts.2
                exact ⟨v, hv, typed.substitute (SubstMor.single firstChecked.down.erase)⟩)
              return ⟨by
                obtain ⟨u, hu, pairTyped⟩ := sigmaFormed
                exact ATyped.convTypeEq (.pairIntro pairTyped hu firstChecked.down secondChecked.down)
                  change.symm⟩
          | _ => none
      | .refl subject => do
          let normal ← evaluator (fuel+1) type
          match shape : normal.val with
          | .id carrier first second =>
              let change := Reduces.typeEq facts roots headSteps formed (shape ▸ normal.property) typeFormed
              let carrierFormed : IsType S.R context carrier := by
                obtain ⟨u, _, typed⟩ := (TypeEq.isType change formed).2
                obtain ⟨v, carrierTyped, hv, _, _, _⟩ := Typed.generation typed
                exact ⟨v, hv, carrierTyped⟩
              let subjectChecked ← check fuel context formed subject carrier carrierFormed
              let firstCompared ← ExecutableConversion.compare S.R evaluator fuel context subject.erase first carrier
              let secondCompared ← ExecutableConversion.compare S.R evaluator fuel context subject.erase second carrier
              return ⟨by
                obtain ⟨u, _, typed⟩ := (TypeEq.isType change formed).2
                obtain ⟨v, carrierTyped, hv, firstTyped, secondTyped, _⟩ := Typed.generation typed
                have firstEqual := Algorithm.sound facts roots headSteps algebra firstCompared.down
                  formed subjectChecked.down.erase firstTyped
                have secondEqual := Algorithm.sound facts roots headSteps algebra secondCompared.down
                  formed subjectChecked.down.erase secondTyped
                have endpoints : TypeEq S.R context (.id carrier subject.erase subject.erase)
                    (.id carrier first second) := ⟨v, hv, .idCong (.refl carrierTyped) hv firstEqual secondEqual⟩
                exact ATyped.convTypeEq (ATyped.convTypeEq (.reflIntro subjectChecked.down) endpoints)
                  change.symm⟩
          | _ => none
      | other => do
          let inferred ← synth fuel context formed other
          let below ← ExecutableChecking.below S.R evaluator fuel context inferred.1 type
          return ⟨.sub inferred.2.down (BelowAlgorithm.sound facts roots headSteps algebra
            below.down formed (Typed.isType inferred.2.down.erase formed) typeFormed)⟩

end

/-- The authored local context retains annotations in each entry. Its erasure
is the context of the interpretation, after those annotations are checked. -/
inductive SourceContext (Head : Type) : Nat → Type where
  | nil : SourceContext Head 0
  | snoc {n : Nat} : SourceContext Head n → ATm Head n → SourceContext Head (n+1)

def SourceContext.erase : {n : Nat} → SourceContext Head n → Ctx Head n
  | _, .nil => .nil
  | _, .snoc previous domain => .snoc previous.erase domain.erase

/-- Formation of the written context itself, before any domain is erased. -/
inductive SourceContext.Formed (R : Rules Head) : {n : Nat} → SourceContext Head n → Prop where
  | nil : SourceContext.Formed R .nil
  | snoc {n : Nat} {previous : SourceContext Head n} {domain : ATm Head n} {level : Head} :
      SourceContext.Formed R previous → ATyped R previous.erase domain (.head level) →
      R.isUniverse level → SourceContext.Formed R (.snoc previous domain)

omit [LevelOrder L] [DecidableEq Head] [DecidableRel S.R.headEq]
    [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative] in
theorem SourceContext.Formed.erase {R : Rules Head} {n : Nat} {context : SourceContext Head n}
    (formed : context.Formed R) : CtxFormed R context.erase := by
  induction formed with
  | nil => exact .nil
  | snoc previous domainTyped isLevel ih =>
      exact .snoc ih ⟨_, isLevel, domainTyped.erase⟩

def formSourceContext (fuel : Nat) : {n : Nat} → (context : SourceContext Head n) →
    Option (PLift (SourceContext.Formed S.R context))
  | _, .nil => some ⟨.nil⟩
  | _, .snoc previous domain => do
      let previousChecked ← formSourceContext fuel previous
      let inferred ← synth S facts roots headSteps algebra declared choices evaluator
        fuel previous.erase previousChecked.down.erase domain
      let domainLevel ← asType S facts roots headSteps evaluator fuel previous.erase
        previousChecked.down.erase domain inferred
      return ⟨.snoc previousChecked.down domainLevel.2.down.2 domainLevel.2.down.1⟩

/-- Complete source formation evidence for a dependent consumer. -/
structure SourceJudgmentCertificate (R : Rules Head) {n : Nat} (context : SourceContext Head n)
    (term type : ATm Head n) where
  contextChecked : SourceContext.Formed R context
  expectedUniverse : Head
  expectedIsUniverse : R.isUniverse expectedUniverse
  expectedChecked : ATyped R context.erase type (.head expectedUniverse)
  termChecked : ATyped R context.erase term type.erase

/-- Synthesis retains the computed type and the original source context. -/
structure SourceSynthesisCertificate (R : Rules Head) {n : Nat} (context : SourceContext Head n)
    (term : ATm Head n) where
  contextChecked : SourceContext.Formed R context
  type : Tm Head n
  termChecked : ATyped R context.erase term type

def synthesizeSource {n : Nat} (fuel : Nat) (context : SourceContext Head n)
    (term : ATm Head n) : Option (SourceSynthesisCertificate S.R context term) := do
  let formed ← formSourceContext S facts roots headSteps algebra declared choices evaluator fuel context
  let inferred ← synth S facts roots headSteps algebra declared choices evaluator
    fuel context.erase formed.down.erase term
  return ⟨formed.down, inferred.1, inferred.2.down⟩

def inferSource {n : Nat} (fuel : Nat) (context : SourceContext Head n) (term : ATm Head n) :
    Option (Tm Head n) :=
  (synthesizeSource S facts roots headSteps algebra declared choices evaluator fuel context term).map
    SourceSynthesisCertificate.type

theorem inferSource_sound {n fuel : Nat} {context : SourceContext Head n}
    {term : ATm Head n} {type : Tm Head n}
    (computed : inferSource S facts roots headSteps algebra declared choices evaluator
      fuel context term = some type) :
    SourceContext.Formed S.R context ∧ ATyped S.R context.erase term type := by
  unfold inferSource at computed
  cases outcome : synthesizeSource S facts roots headSteps algebra declared choices evaluator
      fuel context term with
  | none => simp only [outcome, Option.map_none] at computed; cases computed
  | some certificate =>
      simp only [outcome, Option.map_some, Option.some.injEq] at computed
      exact computed ▸ ⟨certificate.contextChecked, certificate.termChecked⟩

/-- The entirely authored boundary checks written context entries and the
written proposed type before checking the source term. -/
def sourceJudgment {n : Nat} (fuel : Nat) (context : SourceContext Head n)
    (term type : ATm Head n) : Option (SourceJudgmentCertificate S.R context term type) := do
  let formed ← formSourceContext S facts roots headSteps algebra declared choices evaluator fuel context
  let expected ← synth S facts roots headSteps algebra declared choices evaluator
    fuel context.erase formed.down.erase type
  let expectedLevel ← asType S facts roots headSteps evaluator fuel context.erase formed.down.erase type expected
  let termChecked ← check S facts roots headSteps algebra declared choices evaluator fuel context.erase formed.down.erase
    term type.erase ⟨expectedLevel.1, expectedLevel.2.down.1, expectedLevel.2.down.2.erase⟩
  return ⟨formed.down, expectedLevel.1, expectedLevel.2.down.1, expectedLevel.2.down.2,
    termChecked.down⟩

def acceptsSource {n : Nat} (fuel : Nat) (context : SourceContext Head n)
    (term type : ATm Head n) : Bool :=
  (sourceJudgment S facts roots headSteps algebra declared choices evaluator fuel context term type).isSome

theorem acceptsSource_sound {n fuel : Nat} {context : SourceContext Head n} {term type : ATm Head n}
    (accepted : acceptsSource S facts roots headSteps algebra declared choices evaluator
      fuel context term type = true) : ATyped S.R context.erase term type.erase := by
  unfold acceptsSource at accepted
  cases computed : sourceJudgment S facts roots headSteps algebra declared choices evaluator
      fuel context term type with
  | none => simp only [computed, Option.isSome_none, Bool.false_eq_true] at accepted
  | some certificate => exact certificate.termChecked

theorem acceptsSource_formation {n fuel : Nat} {context : SourceContext Head n}
    {term type : ATm Head n}
    (accepted : acceptsSource S facts roots headSteps algebra declared choices evaluator
      fuel context term type = true) :
    SourceContext.Formed S.R context ∧
      ∃ level, S.R.isUniverse level ∧ ATyped S.R context.erase type (.head level) := by
  unfold acceptsSource at accepted
  cases computed : sourceJudgment S facts roots headSteps algebra declared choices evaluator
      fuel context term type with
  | none => simp only [computed, Option.isSome_none, Bool.false_eq_true] at accepted
  | some certificate => exact ⟨certificate.contextChecked, certificate.expectedUniverse,
      certificate.expectedIsUniverse, certificate.expectedChecked⟩

def judgment {n : Nat} (fuel : Nat) (context : Ctx Head n) (term type : ATm Head n) :
    Option (CheckResult S context term type.erase) := do
  let contextChecked ← ExecutableChecking.formContext S.R choices evaluator fuel context
  let formed := ExecutableChecking.ContextAlgorithm.sound facts roots headSteps algebra declared
    contextChecked.down
  let expected ← synth S facts roots headSteps algebra declared choices evaluator fuel context formed type
  let expectedLevel ← asType S facts roots headSteps evaluator fuel context formed type expected
  check S facts roots headSteps algebra declared choices evaluator fuel context formed term type.erase
    ⟨expectedLevel.1, expectedLevel.2.down.1, expectedLevel.2.down.2.erase⟩

def accepts {n : Nat} (fuel : Nat) (context : Ctx Head n) (term type : ATm Head n) : Bool :=
  (judgment S facts roots headSteps algebra declared choices evaluator fuel context term type).isSome

theorem accepts_sound {n fuel : Nat} {context : Ctx Head n} {term type : ATm Head n}
    (accepted : accepts S facts roots headSteps algebra declared choices evaluator
      fuel context term type = true) : ATyped S.R context term type.erase := by
  unfold accepts at accepted
  cases computed : judgment S facts roots headSteps algebra declared choices evaluator
      fuel context term type with
  | none => simp only [computed, Option.isSome_none, Bool.false_eq_true] at accepted
  | some certificate => exact certificate.down

end TypedEquality.Normalization.ExecutableWrittenChecking
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
