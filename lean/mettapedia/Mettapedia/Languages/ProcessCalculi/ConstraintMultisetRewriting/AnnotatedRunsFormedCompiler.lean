import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsFormedTransform
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionCodeCongruence
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationCheckedTelescopePrograms

/-!
# Compiled rules, compiled runs, and the certificate a run produces

## Compiled rules and their soundness

A **compiled rule** (`CompiledRule`) is a rule schema of the candidate step together with a finite
conversion certificate. An instance (`CompiledRule.instantiate`) takes a pending computation
`evaluate left (var result)`, tells `result` the value `value`, and makes the pending computations
of `produce`, each `evaluate term (var output)`. Its **reduct** is the value with every output
replaced by the computation that makes it. **Per-rule soundness** (`CompiledRule.Sound`) is a
check by the Flower's checker: the certificate converts the denotation of `left` to the
denotation of the reduct, on the rule's schema variables. By the checker's own code substitution
it then holds for every instance.

## Compiled runs and their certificate

A **compiled step** (`CompiledStep`) is the data of one firing of a compiled rule: the rule, a
renaming of its schema variables, the occurrence it takes and the occurrences it makes. Its
firing (`CompiledStep.firing`) is a firing of the candidate step with no queries.

The run **produces its certificate** (`certify`): working back from the last firing, the
certificate of a taken computation is the instance of its rule's certificate, followed by the
congruence (`bridge`) that replaces each output's computation by the certificate of the firing
that took it. Nothing is searched for.

**Soundness for every run** (`certify_sound`): for every answer that solves the run's equations,
and every occurrence with a produced certificate, the occurrence is, under the answer, a pending
computation whose term the certificate converts to its result's value. It uses only per-rule
soundness, the checker's code substitution and congruence, and the run's own equations and made
occurrences.

## The compiler

A **callable** (`Callable`) is a program with its telescope and body. The compiler (`compile`)
reads the source term: a call of a callable through its telescope, with values as arguments,
becomes the compiled operation applied to the quoted arguments; a projection of a pair of values
becomes a pending projection. Any other head is refused. The compiled term denotes the call's
body at the arguments, and the source converts to it by the telescope's beta steps
(`compile_sound`).

The compiler covers single calls with values as arguments. Nested calls, which need fresh
result variables for intermediate computations, are outside it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsFormed

open Mettapedia.Logic.LP
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation (Tm Ctx Sub subst DeclName Rules liftClosed)
open Presentation.TelescopeAbstraction (applyClosed closeTerm)
open Presentation.StructuralConversionCode (RootDecoder Code)
open AnnotatedRuns

/-! ## Renaming of pattern variables -/

/-- A renaming of pattern variables, as a substitution. -/
def varRenaming (ρ : Nat → Nat) : Subst signature := fun v => .var (ρ v)

/-! ## Compiled rules -/

/-- **A compiled rule**: a rule schema with a conversion certificate on its schema variables
below `arity`. -/
structure CompiledRule (Head : Type) (RootCode : Nat → Type) where
  arity : Nat
  left : Pattern
  result : Nat
  value : Pattern
  produce : List (Pattern × Nat)
  certificate : Code Head RootCode arity

namespace CompiledRule

variable {Head : Type} [DecidableEq Head] {RootCode : Nat → Type}
variable (rule : CompiledRule Head RootCode)

/-- The rule instance whose schema variables are renamed by `ρ`. -/
def instantiate (ρ : Nat → Nat) : RuleInstance Pattern where
  take := [evaluate ((varRenaming ρ).applyTerm rule.left) (.var (ρ rule.result))]
  read := []
  tell := [(.var (ρ rule.result), (varRenaming ρ).applyTerm rule.value)]
  checks := []
  produce := rule.produce.map fun made => evaluate ((varRenaming ρ).applyTerm made.1) (.var (ρ made.2))

/-- Where an output variable is made. -/
def outputIndex (v : Nat) : Option Nat := rule.produce.findIdx? fun made => made.2 == v

/-- Whether a variable is an output. -/
def isOutput (v : Nat) : Bool := (rule.outputIndex v).isSome

/-- Each output stands for the computation that makes it; any other variable for itself. -/
def outputs : Subst signature := fun v =>
  match rule.outputIndex v with
  | some j => (rule.produce[j]?.map Prod.fst).getD (.var v)
  | none => .var v

/-- The told value with every output replaced by its computation. -/
def reduct : Pattern := rule.outputs.applyTerm rule.value

/-- The per-rule check: the certificate converts the denotation of the taken computation to the
denotation of the reduct, on the schema variables. -/
def soundCheck (headEq : Head → Head → Prop) [DecidableRel headEq]
    (decode : {n : Nat} → RootCode n → Option (Tm Head n × Tm Head n)) (ops : Operations Head) :
    Bool :=
  match (denote ops rule.left : Option (Tm Head rule.arity)),
      (denote ops rule.reduct : Option (Tm Head rule.arity)) with
  | some left, some reduct => rule.certificate.check headEq decode left reduct
  | _, _ => false

/-- **Per-rule soundness.** -/
def Sound (headEq : Head → Head → Prop) [DecidableRel headEq]
    (decode : {n : Nat} → RootCode n → Option (Tm Head n × Tm Head n)) (ops : Operations Head) :
    Prop :=
  rule.soundCheck headEq decode ops = true

variable {rule}

theorem Sound.spec {headEq : Head → Head → Prop} [DecidableRel headEq]
    {decode : {n : Nat} → RootCode n → Option (Tm Head n × Tm Head n)} {ops : Operations Head}
    (sound : rule.Sound headEq decode ops) :
    ∃ left reduct, (denote ops rule.left : Option (Tm Head rule.arity)) = some left ∧
      (denote ops rule.reduct : Option (Tm Head rule.arity)) = some reduct ∧
      rule.certificate.check headEq decode left reduct = true := by
  unfold Sound soundCheck at sound
  split at sound
  · rename_i left reduct denotedLeft denotedReduct
    exact ⟨left, reduct, denotedLeft, denotedReduct, sound⟩
  · cases sound

omit [DecidableEq Head] in
theorem outputs_of_index {v j : Nat} (index : rule.outputIndex v = some j) :
    ∃ term, rule.produce[j]? = some (term, v) ∧ rule.outputs v = term := by
  have found := List.findIdx?_eq_some_iff_getElem.mp index
  obtain ⟨inside, matches_, _⟩ := found
  have same : (rule.produce[j]'inside).2 = v := by simpa using matches_
  refine ⟨(rule.produce[j]'inside).1, ?_, ?_⟩
  · rw [List.getElem?_eq_getElem inside, ← same]
  · simp [outputs, index, List.getElem?_eq_getElem inside]

omit [DecidableEq Head] in
theorem outputs_of_not_output {v : Nat} (notOutput : rule.isOutput v = false) :
    rule.outputs v = .var v := by
  have none_ : rule.outputIndex v = none := by
    simpa [isOutput] using notOutput
  simp [outputs, none_]

end CompiledRule

/-! ## The bridge: congruence through a told value -/

section Bridge

variable {Head : Type} [DecidableEq Head] {RootCode : Nat → Type} (ops : Operations Head) {n : Nat}

/-- **Congruence through a told value**: at an output, the certificate of the computation that
made it; elsewhere reflexivity; through application and pairs, the checker's congruence. -/
def bridge (reductSide valueSide : Subst signature) (isOutput : Nat → Bool)
    (images : Nat → Option (Code Head RootCode n)) : Pattern → Option (Code Head RootCode n)
  | .var v => if isOutput v then images v else (denote ops (valueSide v)).map Code.refl
  | .const name => some (.refl (.const name))
  | .app .application arguments =>
      (bridge reductSide valueSide isOutput images (arguments ⟨0, by decide⟩)).bind fun f =>
        (bridge reductSide valueSide isOutput images (arguments ⟨1, by decide⟩)).bind fun a =>
          (denote ops (valueSide.applyTerm (arguments ⟨0, by decide⟩))).bind fun target =>
            (denote ops (reductSide.applyTerm (arguments ⟨1, by decide⟩))).map fun source =>
              Code.congApp target source f a
  | .app .pair arguments =>
      (bridge reductSide valueSide isOutput images (arguments ⟨0, by decide⟩)).bind fun f =>
        (bridge reductSide valueSide isOutput images (arguments ⟨1, by decide⟩)).bind fun a =>
          (denote ops (valueSide.applyTerm (arguments ⟨0, by decide⟩))).bind fun target =>
            (denote ops (reductSide.applyTerm (arguments ⟨1, by decide⟩))).map fun source =>
              Code.congPair target source f a
  | .app _ _ => none

variable (headEq : Head → Head → Prop) [DecidableRel headEq]
  (decode : {n : Nat} → RootCode n → Option (Tm Head n × Tm Head n))

/-- **The bridge is checked**: it converts the reduct side to the value side, given checked
images at the outputs and agreement elsewhere. -/
theorem bridge_checked {reductSide valueSide : Subst signature} {isOutput : Nat → Bool}
    {images : Nat → Option (Code Head RootCode n)}
    (outputImages : ∀ v code, isOutput v = true → images v = some code →
      ∃ a b, (denote ops (reductSide v) : Option (Tm Head n)) = some a ∧
        denote ops (valueSide v) = some b ∧ code.check headEq decode a b = true)
    (others : ∀ v, isOutput v = false → reductSide v = valueSide v) :
    ∀ (p : Pattern) {code : Code Head RootCode n},
      bridge ops reductSide valueSide isOutput images p = some code →
        ∃ a b, denote ops (reductSide.applyTerm p) = some a ∧
          denote ops (valueSide.applyTerm p) = some b ∧ code.check headEq decode a b = true
  | .var v, code, bridged => by
      unfold bridge at bridged
      cases output : isOutput v
      · rw [output, if_neg Bool.false_ne_true] at bridged
        cases denoted : (denote ops (valueSide v) : Option (Tm Head n)) with
        | none =>
            rw [denoted] at bridged
            cases bridged
        | some b =>
            rw [denoted, Option.map_some] at bridged
            cases bridged
            refine ⟨b, b, ?_, denoted, Code.check_refl headEq decode b⟩
            change denote ops (reductSide v) = some b
            rw [others v output]
            exact denoted
      · rw [output, if_pos rfl] at bridged
        exact outputImages v code output bridged
  | .const name, code, bridged => by
      simp only [bridge, Option.some.injEq] at bridged
      subst bridged
      exact ⟨.const name, .const name, rfl, rfl, Code.check_refl headEq decode _⟩
  | .app .application arguments, code, bridged => by
      cases hf : bridge ops reductSide valueSide isOutput images (arguments ⟨0, by decide⟩) with
      | none => simp [bridge, hf] at bridged
      | some f =>
          cases ha : bridge ops reductSide valueSide isOutput images (arguments ⟨1, by decide⟩) with
          | none => simp [bridge, hf, ha] at bridged
          | some a =>
              obtain ⟨f₁, f₂, df₁, df₂, cf⟩ := bridge_checked outputImages others _ hf
              obtain ⟨a₁, a₂, da₁, da₂, ca⟩ := bridge_checked outputImages others _ ha
              simp only [bridge, hf, ha, df₂, da₁, Option.bind_some, Option.map_some,
                Option.some.injEq] at bridged
              subst bridged
              refine ⟨.app f₁ a₁, .app f₂ a₂, ?_, ?_, Code.check_congApp headEq decode cf ca⟩
              · change (denote ops (reductSide.applyTerm (arguments ⟨0, by decide⟩))).bind
                    (fun f' => (denote ops (reductSide.applyTerm (arguments ⟨1, by decide⟩))).map
                      (Tm.app f')) = _
                rw [df₁, da₁]
                rfl
              · change (denote ops (valueSide.applyTerm (arguments ⟨0, by decide⟩))).bind
                    (fun f' => (denote ops (valueSide.applyTerm (arguments ⟨1, by decide⟩))).map
                      (Tm.app f')) = _
                rw [df₂, da₂]
                rfl
  | .app .pair arguments, code, bridged => by
      cases hf : bridge ops reductSide valueSide isOutput images (arguments ⟨0, by decide⟩) with
      | none => simp [bridge, hf] at bridged
      | some f =>
          cases ha : bridge ops reductSide valueSide isOutput images (arguments ⟨1, by decide⟩) with
          | none => simp [bridge, hf, ha] at bridged
          | some a =>
              obtain ⟨f₁, f₂, df₁, df₂, cf⟩ := bridge_checked outputImages others _ hf
              obtain ⟨a₁, a₂, da₁, da₂, ca⟩ := bridge_checked outputImages others _ ha
              simp only [bridge, hf, ha, df₂, da₁, Option.bind_some, Option.map_some,
                Option.some.injEq] at bridged
              subst bridged
              refine ⟨.pair f₁ a₁, .pair f₂ a₂, ?_, ?_, Code.check_congPair headEq decode cf ca⟩
              · change (denote ops (reductSide.applyTerm (arguments ⟨0, by decide⟩))).bind
                    (fun f' => (denote ops (reductSide.applyTerm (arguments ⟨1, by decide⟩))).map
                      (Tm.pair f')) = _
                rw [df₁, da₁]
                rfl
              · change (denote ops (valueSide.applyTerm (arguments ⟨0, by decide⟩))).bind
                    (fun f' => (denote ops (valueSide.applyTerm (arguments ⟨1, by decide⟩))).map
                      (Tm.pair f')) = _
                rw [df₂, da₂]
                rfl
  | .app .second _, code, bridged => by simp [bridge] at bridged
  | .app .evaluate _, code, bridged => by simp [bridge] at bridged
  | .app (.operation _ _) _, code, bridged => by simp [bridge] at bridged

end Bridge

/-! ## Callables -/

/-- **A program the compiler can call**: its name, telescope and body. -/
structure Callable (Head : Type) where
  name : DeclName
  arity : Nat
  telescope : Ctx Head arity
  body : Tm Head arity

/-! ## Compiled programs and compiled runs -/

section Program

variable {Head : Type} [DecidableEq Head] {R : Rules Head} [DecidableRel R.headEq]

/-- **A compiled program for a theory**: the operations' bodies, the callables, and the compiled
rules. Agreement of the callables with the operation table and per-rule soundness are fields;
each program proves them. -/
structure CompiledProgram (R : Rules Head) [DecidableRel R.headEq]
    (decoder : RootDecoder R.computation) where
  operations : Operations Head
  callables : List (Callable Head)
  rules : List (CompiledRule Head decoder.Code)
  callables_denoted : ∀ c ∈ callables, operations c.name c.arity = some c.body
  rules_sound : ∀ rule ∈ rules, rule.Sound R.headEq decoder.decode operations

variable {decoder : RootDecoder R.computation}

/-- **A compiled step**: one firing of a compiled rule, as data. -/
structure CompiledStep (program : CompiledProgram R decoder) where
  rule : CompiledRule Head decoder.Code
  member : rule ∈ program.rules
  rename : Nat → Nat
  taken : Nat
  made : List Nat

/-- The firing of a compiled step: the rule instance, no queries, one taken occurrence. -/
def CompiledStep.firing {program : CompiledProgram R decoder} (step : CompiledStep program) :
    Firing Pattern (Subst signature) Nat :=
  ⟨step.rule.instantiate step.rename, [], ⟨[step.taken], [], step.made⟩⟩

/-- The compiled start: no equations, and one occurrence. -/
def compiledStart (o : Nat) : Configuration Pattern Nat := ⟨[], {o}⟩

variable (program : CompiledProgram R decoder) (rootAction : RootAction decoder) {n : Nat}

/-- **The certificate of one firing**: its rule's certificate at the firing's instance, then the
bridge through its told value, with the later certificates at its outputs. -/
def stepCertificate (θ : Subst signature) (step : CompiledStep program)
    (later : Nat → Option (Code Head decoder.Code n)) : Option (Code Head decoder.Code n) :=
  (collect fun i : Fin step.rule.arity =>
      (denote program.operations ((θ ∘ₛ varRenaming step.rename) i.val) : Option (Tm Head n))).bind
    fun τ =>
      (bridge program.operations ((θ ∘ₛ varRenaming step.rename) ∘ₛ step.rule.outputs)
          (θ ∘ₛ varRenaming step.rename) step.rule.isOutput
          (fun v => match step.rule.outputIndex v with
            | some j => step.made[j]?.bind later
            | none => none)
          step.rule.value).map
        fun bridged => .trans (step.rule.certificate.substitute rootAction.substitute τ) bridged

/-- **The certificate a run produces** for an occurrence, read back from the last firing. -/
def certify (θ : Subst signature) :
    List (CompiledStep program) → Nat → Option (Code Head decoder.Code n)
  | [], _ => none
  | step :: rest, o =>
      if o = step.taken then stepCertificate program rootAction θ step (certify θ rest)
      else certify θ rest o

/-- **What a certificate certifies**: under the answer, the occurrence is a pending computation
whose term the certificate converts to its result's value. -/
def Certifies (θ : Subst signature) (label : Nat → Pattern) (o : Nat)
    (code : Code Head decoder.Code n) : Prop :=
  ∃ term result left right, θ.applyTerm (label o) = evaluate term result ∧
    (denote program.operations term : Option (Tm Head n)) = some left ∧
    denote program.operations result = some right ∧
    code.check R.headEq decoder.decode left right = true

variable {program rootAction}

theorem stepCertificate_sound {θ : Subst signature} {label : Nat → Pattern}
    {step : CompiledStep program} {later : Nat → Option (Code Head decoder.Code n)}
    (laterSound : ∀ o code, later o = some code → Certifies program θ label o code)
    (solved : action.Models θ (step.firing.added label))
    (made : step.made.map label = (step.rule.instantiate step.rename).produce)
    {code : Code Head decoder.Code n}
    (certified : stepCertificate program rootAction θ step later = some code) :
    Certifies program θ label step.taken code := by
  unfold stepCertificate at certified
  rw [Option.bind_eq_some_iff] at certified
  obtain ⟨τ, hτ, certified⟩ := certified
  rw [Option.map_eq_some_iff] at certified
  obtain ⟨bridged, hb, rfl⟩ := certified
  set σ := θ ∘ₛ varRenaming step.rename with σ_def
  obtain ⟨left, reduct, denotedLeft, denotedReduct, checked⟩ :=
    (program.rules_sound step.rule step.member).spec
  have images : ∀ i : Fin step.rule.arity,
      (denote program.operations (σ i.val) : Option (Tm Head n)) = some (τ i) :=
    collect_eq_some hτ
  have leftSide := denote_applyTerm program.operations σ τ images step.rule.left denotedLeft
  have reductSide := denote_applyTerm program.operations σ τ images step.rule.reduct
    denotedReduct
  have instance_ := Presentation.StructuralConversionCode.Code.check_substitute
    rootAction.substitute R.headEq decoder.decode rootAction.natural τ
    step.rule.certificate checked
  -- the bridge through the told value
  obtain ⟨a, b, da, db, bridgedChecked⟩ := bridge_checked program.operations R.headEq
    decoder.decode (reductSide := σ ∘ₛ step.rule.outputs) (valueSide := σ)
    (isOutput := step.rule.isOutput)
    (images := fun v => match step.rule.outputIndex v with
      | some j => step.made[j]?.bind later
      | none => none)
    (by
      intro v image output imaged
      cases index : step.rule.outputIndex v with
      | none => simp [CompiledRule.isOutput, index] at output
      | some j =>
          simp only [index] at imaged
          cases occurrence : step.made[j]? with
          | none => simp [occurrence] at imaged
          | some m =>
              simp only [occurrence, Option.bind_some] at imaged
              obtain ⟨term, result, l, r, labelled, dl, dr, cl⟩ := laterSound m image imaged
              obtain ⟨made_term, produced, outputImage⟩ :=
                CompiledRule.outputs_of_index index
              have madeLabel : label m = evaluate ((varRenaming step.rename).applyTerm made_term)
                  (.var (step.rename v)) := by
                have atJ := congrArg (fun list => list[j]?) made
                simp only [List.getElem?_map, occurrence, Option.map_some,
                  CompiledRule.instantiate, produced] at atJ
                exact Option.some.inj atJ
              rw [madeLabel, applyTerm_evaluate] at labelled
              obtain ⟨termSame, resultSame⟩ := evaluate_injective labelled
              refine ⟨l, r, ?_, ?_, cl⟩
              · change denote program.operations (σ.applyTerm (step.rule.outputs v)) = some l
                rw [outputImage, σ_def, Subst.applyTerm_comp, termSame]
                exact dl
              · change denote program.operations (θ.applyTerm (.var (step.rename v))) = some r
                rw [resultSame]
                exact dr)
    (by
      intro v notOutput
      change σ.applyTerm (step.rule.outputs v) = σ v
      rw [CompiledRule.outputs_of_not_output notOutput]
      rfl)
    step.rule.value hb
  rw [Subst.applyTerm_comp] at da
  change denote program.operations (σ.applyTerm step.rule.reduct) = some a at da
  rw [reductSide, Option.some.injEq] at da
  subst da
  -- the taken occurrence, under the answer
  have takeEquation := solved
    (evaluate ((varRenaming step.rename).applyTerm step.rule.left) (.var (step.rename step.rule.result)),
      label step.taken)
    (by simp [CompiledStep.firing, Firing.added, GuardFreeProcessOrders.added,
      Selection.equations, CompiledRule.instantiate])
  have tellEquation := solved
    (.var (step.rename step.rule.result), (varRenaming step.rename).applyTerm step.rule.value)
    (by simp [CompiledStep.firing, Firing.added, GuardFreeProcessOrders.added,
      Selection.equations, CompiledRule.instantiate])
  change θ.applyTerm _ = θ.applyTerm (label step.taken) at takeEquation
  change θ.applyTerm (.var _) = θ.applyTerm _ at tellEquation
  refine ⟨θ.applyTerm ((varRenaming step.rename).applyTerm step.rule.left),
    θ.applyTerm (.var (step.rename step.rule.result)), subst τ left, b, ?_, ?_, ?_,
    Presentation.StructuralConversionCode.Code.check_trans R.headEq decoder.decode
      instance_ bridgedChecked⟩
  · rw [← takeEquation, applyTerm_evaluate]
  · rw [← Subst.applyTerm_comp]
    exact leftSide
  · rw [tellEquation, ← Subst.applyTerm_comp]
    exact db

/-- **Soundness of the run's certificate, for every run of compiled steps**: under every answer
solving the run's equations, each produced certificate converts its occurrence's computation to
its result's value. -/
theorem certify_sound (θ : Subst signature) (label : Nat → Pattern) :
    ∀ (steps : List (CompiledStep program)),
      (∀ step ∈ steps, action.Models θ (step.firing.added label)) →
      (∀ step ∈ steps, step.made.map label = (step.rule.instantiate step.rename).produce) →
      ∀ o (code : Code Head decoder.Code n), certify program rootAction θ steps o = some code →
        Certifies program θ label o code
  | [], _, _, o, code, certified => by simp [certify] at certified
  | step :: rest, solves, made, o, code, certified => by
      have restSound := certify_sound θ label rest
        (fun s member => solves s (List.mem_cons_of_mem _ member))
        (fun s member => made s (List.mem_cons_of_mem _ member))
      unfold certify at certified
      split at certified
      · rename_i taken
        subst taken
        exact stepCertificate_sound restSound (solves step List.mem_cons_self)
          (made step List.mem_cons_self) certified
      · exact restSound o code certified

end Program

/-! ## The compiler -/

section Compiler

variable {Head : Type} [DecidableEq Head] {n : Nat}

/-- Peel a telescope's call: the head and the arguments, in de Bruijn order. -/
def peelCall : {k : Nat} → Ctx Head k → Tm Head n → Option (Tm Head n × Sub Head k n)
  | _, .nil, head => some (head, Fin.elim0)
  | _, .snoc prior _, .app function argument =>
      (peelCall prior function).map fun peeled => (peeled.1, Fin.cases argument peeled.2)
  | _, .snoc _ _, _ => none

omit [DecidableEq Head] in
theorem peelCall_spec : ∀ {k : Nat} (telescope : Ctx Head k) {t head : Tm Head n}
    {σ : Sub Head k n}, peelCall telescope t = some (head, σ) → t = applyClosed telescope σ head
  | _, .nil, t, head, σ, peeled => by
      simp only [peelCall, Option.some.injEq, Prod.mk.injEq] at peeled
      obtain ⟨rfl, _⟩ := peeled
      rfl
  | _, .snoc prior _, .app function argument, head, σ, peeled => by
      cases inner : peelCall prior function with
      | none => simp [peelCall, inner] at peeled
      | some peeledInner =>
          obtain ⟨head', σ'⟩ := peeledInner
          simp only [peelCall, inner, Option.map_some, Option.some.injEq, Prod.mk.injEq] at peeled
          obtain ⟨rfl, rfl⟩ := peeled
          have earlier := peelCall_spec prior inner
          simp only [applyClosed, Fin.cases_zero, Fin.cases_succ]
          rw [← earlier]
  | _, .snoc _ _, .var _, _, _, peeled => by simp [peelCall] at peeled
  | _, .snoc _ _, .const _, _, _, peeled => by simp [peelCall] at peeled
  | _, .snoc _ _, .head _, _, _, peeled => by simp [peelCall] at peeled
  | _, .snoc _ _, .pi _ _, _, _, peeled => by simp [peelCall] at peeled
  | _, .snoc _ _, .sigma _ _, _, _, peeled => by simp [peelCall] at peeled
  | _, .snoc _ _, .id _ _ _, _, _, peeled => by simp [peelCall] at peeled
  | _, .snoc _ _, .lam _, _, _, peeled => by simp [peelCall] at peeled
  | _, .snoc _ _, .pair _ _, _, _, peeled => by simp [peelCall] at peeled
  | _, .snoc _ _, .fst _, _, _, peeled => by simp [peelCall] at peeled
  | _, .snoc _ _, .snd _, _, _, peeled => by simp [peelCall] at peeled
  | _, .snoc _ _, .refl _, _, _, peeled => by simp [peelCall] at peeled

variable (canonical : DeclName → Bool)

/-- One callable's attempt: the source must be a call of its closed body through its telescope,
with values as arguments. -/
def compileWith (callable : Callable Head) (t : Tm Head n) : Option Pattern :=
  match peelCall callable.telescope t with
  | some (head, σ) =>
      if head = liftClosed (closeTerm callable.telescope callable.body) then
        (collect fun i : Fin callable.arity => quoteValue canonical (σ i.rev)).map
          (call callable.name callable.arity)
      else none
  | none => none

/-- **The compiler of one computation.** A call of a callable becomes the compiled operation on
the quoted arguments; a projection of a pair of values becomes a pending projection; any other
head is refused. -/
def compile (callables : List (Callable Head)) (t : Tm Head n) : Option Pattern :=
  match callables.findSome? (fun callable => compileWith canonical callable t) with
  | some p => some p
  | none =>
      match t with
      | .snd (.pair first second) =>
          (quoteValue canonical first).bind fun a =>
            (quoteValue canonical second).map fun b => secondP (pairP a b)
      | _ => none

variable {canonical}

theorem compileWith_spec {callable : Callable Head} {t : Tm Head n} {p : Pattern}
    (compiled : compileWith canonical callable t = some p) :
    ∃ σ : Sub Head callable.arity n,
      t = applyClosed callable.telescope σ (liftClosed (closeTerm callable.telescope callable.body)) ∧
      ∃ arguments : Fin callable.arity → Pattern,
        p = call callable.name callable.arity arguments ∧
          ∀ i, quoteValue canonical (σ i.rev) = some (arguments i) := by
  unfold compileWith at compiled
  split at compiled
  · rename_i head σ peeled
    split at compiled
    · rename_i headSame
      cases collected : collect (fun i : Fin callable.arity => quoteValue canonical (σ i.rev)) with
      | none => simp [collected] at compiled
      | some arguments =>
          simp only [collected, Option.map_some, Option.some.injEq] at compiled
          refine ⟨σ, ?_, arguments, compiled.symm, collect_eq_some collected⟩
          rw [peelCall_spec callable.telescope peeled, headSame]
    · cases compiled
  · cases compiled

/-- **The compiled term denotes the source's computation**, and the source converts to it by a
checked code: the telescope's beta steps for a call, reflexivity for a projection. -/
theorem compile_sound (ops : Operations Head) {callables : List (Callable Head)}
    (denoted : ∀ c ∈ callables, ops c.name c.arity = some c.body) {RootCode : Nat → Type}
    (headEq : Head → Head → Prop) [DecidableRel headEq]
    (decode : {n : Nat} → RootCode n → Option (Tm Head n × Tm Head n))
    {t : Tm Head n} {p : Pattern} (compiled : compile canonical callables t = some p) :
    ∃ (t' : Tm Head n) (entry : Code Head RootCode n), denote ops p = some t' ∧
      entry.check headEq decode t t' = true := by
  unfold compile at compiled
  split at compiled
  · rename_i p' foundSome
    cases compiled
    obtain ⟨callable, member, attempt⟩ := List.exists_of_findSome?_eq_some foundSome
    obtain ⟨σ, source, arguments, rfl, quoted⟩ := compileWith_spec attempt
    refine ⟨subst σ callable.body,
      Presentation.FormationCheckedTelescopePrograms.applicationCodeIn callable.telescope σ
        callable.body, ?_, ?_⟩
    · have values : collect (fun i => (denote ops (arguments i) : Option (Tm Head n))) =
          some (fun i => σ i.rev) :=
        collect_of_forall fun i => denote_quoteValue ops canonical _ (quoted i)
      change (ops callable.name callable.arity).bind (fun body =>
        (collect fun i => (denote ops (arguments i) : Option (Tm Head n))).map fun images =>
          subst (fun index => images index.rev) body) = _
      rw [denoted callable member, values]
      simp only [Option.bind_some, Option.map_some, Fin.rev_rev]
    · rw [source]
      exact Presentation.FormationCheckedTelescopePrograms.applicationCodeIn_checked headEq decode
        callable.telescope σ callable.body
  · split at compiled
    · rename_i first second _
      cases hf : quoteValue canonical first with
      | none => simp [hf] at compiled
      | some a =>
          cases hs : quoteValue canonical second with
          | none => simp [hf, hs] at compiled
          | some b =>
              simp only [hf, hs, Option.bind_some, Option.map_some, Option.some.injEq] at compiled
              subst compiled
              refine ⟨.snd (.pair first second), .refl _, ?_,
                Presentation.StructuralConversionCode.Code.check_refl headEq decode _⟩
              change ((denote ops (pairP a b)).map Tm.snd : Option (Tm Head n)) = _
              change (((denote ops a).bind fun a' => (denote ops b).map (Tm.pair a')).map Tm.snd :
                Option (Tm Head n)) = _
              rw [denote_quoteValue ops canonical first hf, denote_quoteValue ops canonical second hs]
              rfl
    · cases compiled

/-- **A compiled term mentions only the context's variables**: every substitution fixing them
fixes it. -/
theorem compile_fixed {callables : List (Callable Head)} {t : Tm Head n} {p : Pattern}
    (compiled : compile canonical callables t = some p) (θ : Subst signature)
    (fixed : ∀ i : Fin n, θ i.val = .var i.val) : θ.applyTerm p = p := by
  unfold compile at compiled
  split at compiled
  · rename_i p' foundSome
    cases compiled
    obtain ⟨callable, _, attempt⟩ := List.exists_of_findSome?_eq_some foundSome
    obtain ⟨σ, _, arguments, rfl, quoted⟩ := compileWith_spec attempt
    rw [applyTerm_call]
    congr 1
    funext i
    exact applyTerm_quoteValue canonical _ (quoted i) θ fixed
  · split at compiled
    · rename_i first second _
      cases hf : quoteValue canonical first with
      | none => simp [hf] at compiled
      | some a =>
          cases hs : quoteValue canonical second with
          | none => simp [hf, hs] at compiled
          | some b =>
              simp only [hf, hs, Option.bind_some, Option.map_some, Option.some.injEq] at compiled
              subst compiled
              rw [applyTerm_secondP, applyTerm_pairP, applyTerm_quoteValue canonical first hf θ fixed,
                applyTerm_quoteValue canonical second hs θ fixed]
    · cases compiled

end Compiler

#print axioms CompiledRule.Sound.spec
#print axioms CompiledRule.outputs_of_index
#print axioms CompiledRule.outputs_of_not_output
#print axioms bridge_checked
#print axioms stepCertificate_sound
#print axioms certify_sound
#print axioms peelCall_spec
#print axioms compileWith_spec
#print axioms compile_sound
#print axioms compile_fixed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsFormed
