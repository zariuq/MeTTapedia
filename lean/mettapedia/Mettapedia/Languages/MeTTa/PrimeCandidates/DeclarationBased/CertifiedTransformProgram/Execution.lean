import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.Package

/-!
# Runs of the certified-transform package

The draft's evaluator fires stored equations on matched arguments, contracts
beta redexes and pair projections, and eliminates identity proofs on
reflexivity.  Each of these is one computation step of the program's rules,
so a finite evaluation is a computation path `Runs`.

* The iterator at a numeral unfolds, one successor equation and one beta step
  per successor, to the pair of the value and evidence after that many uses
  of the step.  That pair has the iterator's result type.
* The calls of the authored execution program reach the values the runtime
  prints, for every numeral count and start, and both ends of each run are
  typed at the call's type.
* The represented consumer runs the translated induction step of `zero-add`.
  Each step's evidence is the compiler's output for the source step,
  specialized at the computed value and the incoming evidence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.Execution

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation Presentation.Declaration Presentation.FormationSensitive
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.AlgebraicSchema
  (SchemaTable SchemaFamily)
open SetProfile (baseName constantName numTy zeroNative sucNative addNative
  eqNumNative holdsName targetRules)
open CertifiedTransforms (stepOver shared sharedBody evidenceFamily)
open CertifiedTransformProgram.Package
open Mettapedia.Logic

/-! ## Runs -/

/-- A run: finitely many computation steps of the program, anywhere in a term. -/
abbrev Runs {n : Nat} (source target : Tower.Tm n) : Prop :=
  ConversionCoherence.StepStar R source target

section Runs

variable {n : Nat}

theorem Runs.app {function function' argument argument' : Tower.Tm n}
    (functionRuns : Runs function function') (argumentRuns : Runs argument argument') :
    Runs (.app function argument) (.app function' argument') :=
  (functionRuns.lift (fun term => Tm.app term argument)
      (fun _ _ step => StepCore.congAppFun step)).trans
    (argumentRuns.lift (fun term => Tm.app function' term)
      (fun _ _ step => StepCore.congAppArg step))

theorem Runs.pair {first first' second second' : Tower.Tm n}
    (firstRuns : Runs first first') (secondRuns : Runs second second') :
    Runs (.pair first second) (.pair first' second') :=
  (firstRuns.lift (fun term => Tm.pair term second)
      (fun _ _ step => StepCore.congPairFst step)).trans
    (secondRuns.lift (fun term => Tm.pair first' term)
      (fun _ _ step => StepCore.congPairSnd step))

theorem Runs.fst {pair pair' : Tower.Tm n} (pairRuns : Runs pair pair') :
    Runs (.fst pair) (.fst pair') :=
  pairRuns.lift (fun term => Tm.fst term) (fun _ _ step => StepCore.congFst step)

theorem Runs.snd {pair pair' : Tower.Tm n} (pairRuns : Runs pair pair') :
    Runs (.snd pair) (.snd pair') :=
  pairRuns.lift (fun term => Tm.snd term) (fun _ _ step => StepCore.congSnd step)

theorem Runs.reflexivity {term term' : Tower.Tm n} (termRuns : Runs term term') :
    Runs (.refl term) (.refl term') :=
  termRuns.lift (fun term => Tm.refl term) (fun _ _ step => StepCore.congRefl step)

theorem Runs.identity {carrier carrier' left left' right right' : Tower.Tm n}
    (carrierRuns : Runs carrier carrier') (leftRuns : Runs left left')
    (rightRuns : Runs right right') :
    Runs (.id carrier left right) (.id carrier' left' right') :=
  ((carrierRuns.lift (fun term => Tm.id term left right)
      (fun _ _ step => StepCore.congIdTy step)).trans
    (leftRuns.lift (fun term => Tm.id carrier' term right)
      (fun _ _ step => StepCore.congIdLeft step))).trans
    (rightRuns.lift (fun term => Tm.id carrier' left' term)
      (fun _ _ step => StepCore.congIdRight step))

theorem Runs.fst_pair (first second : Tower.Tm n) : Runs (.fst (.pair first second)) first :=
  .single (StepCore.betaSigmaFst first second)

theorem Runs.snd_pair (first second : Tower.Tm n) : Runs (.snd (.pair first second)) second :=
  .single (StepCore.betaSigmaSnd first second)

theorem Runs.beta (body : Tower.Tm (n + 1)) (argument : Tower.Tm n) :
    Runs (.app (.lam body) argument) (inst0 argument body) :=
  .single (StepCore.betaPi body argument)

/-- One stored equation of the package, at an instance. -/
theorem Runs.equation {arity : Nat} {left right : Tower.Tm arity}
    (listed : (⟨arity, (left, right)⟩ : Σ arity : Nat, Tower.Tm arity × Tower.Tm arity) ∈
      packageEquations)
    (substitution : Sub Tower.Head arity n) :
    Runs (subst substitution left) (subst substitution right) :=
  .single (StepCore.root (RootStep.declared
    (SchemaTable.step_of_mem packageEquations listed substitution)))

/-- One step of the profile's own computation. -/
theorem Runs.profile {left right : Tower.Tm n}
    (step : SetProfile.rules.computation.step left right) : Runs left right := by
  have mapped := profileMorphism.computation step
  simp only [Tm.mapHead_id] at mapped
  exact .single (StepCore.root mapped)

theorem Runs.conv {source target : Tower.Tm n} (runs : Runs source target) :
    Conv R.headEq source target R.computation :=
  ConversionCoherence.stepStar_implies_conv runs

end Runs

/-- The instance of an equation at its pattern values, listed first pattern first:
the kernel's `PVar p` is the value at position `p`. -/
def patternValues {arity n : Nat} (values : Fin arity → Tower.Tm n) : Sub Tower.Head arity n :=
  fun index => values (Fin.rev index)

/-! ## Numerals and addition -/

def numeral {n : Nat} : Nat → Tower.Tm n
  | 0 => zeroNative
  | count + 1 => sucNative (numeral count)

theorem numeral_typed {n : Nat} {Γ : Tower.Ctx n} : ∀ count : Nat, Typing R Γ (numeral count) numT
  | 0 => zeroNative_typed
  | count + 1 => sucNative_typed (numeral_typed count)

theorem add_zero_run {n : Nat} (value : Tower.Tm n) :
    Runs (addNative value zeroNative) value :=
  Runs.profile (RootStep.declared (SchemaTable.step_of_mem SetProfile.nativeEquations
    (List.getElem_mem (l := SetProfile.nativeEquations) (n := 0) (by decide))
    (patternValues ![value])))

theorem add_suc_run {n : Nat} (left right : Tower.Tm n) :
    Runs (addNative left (sucNative right)) (sucNative (addNative left right)) :=
  Runs.profile (RootStep.declared (SchemaTable.step_of_mem SetProfile.nativeEquations
    (List.getElem_mem (l := SetProfile.nativeEquations) (n := 1) (by decide))
    (patternValues ![left, right])))

/-- `add zero m` computes to `m` at every numeral. -/
theorem add_zero_numeral {n : Nat} : ∀ count : Nat,
    Runs (addNative zeroNative (numeral count) : Tower.Tm n) (numeral count)
  | 0 => add_zero_run zeroNative
  | count + 1 =>
      (add_suc_run zeroNative (numeral count)).trans
        (Runs.app .refl (add_zero_numeral count))

/-- Reflexivity at a numeral is evidence for `eqAt` there. -/
theorem refl_eqAt {n : Nat} {Γ : Tower.Ctx n} (count : Nat) :
    Typing R Γ (.refl (numeral count)) (eqAtApp (numeral count)) :=
  Typing.conv (Typing.reflIntro (numeral_typed count)) (eqAt_typed (numeral_typed count))
    (isUniverseAt Tower.zero)
    (.symm _ _ (.trans _ _ _ (package_step listed_eqAt (at1 (numeral count)))
      (Runs.conv (Runs.identity .refl (add_zero_numeral count) .refl))))

/-! ## The iterator at a numeral -/

/-- The value and evidence after `count` uses of `step`, as the iterator
leaves them: each use is shared once and read by both projections. -/
def iterState {n : Nat} (step : Tower.Tm n) :
    Nat → Tower.Tm n → Tower.Tm n → Tower.Tm n × Tower.Tm n
  | 0, value, evidence => (value, evidence)
  | count + 1, value, evidence =>
      iterState step count (.fst (app2 step value evidence)) (.snd (app2 step value evidence))

theorem shared_contracts {n : Nat} (step continuation value evidence : Tower.Tm n) :
    inst0 (app2 step value evidence) (sharedBody continuation) =
      app2 continuation (.fst (app2 step value evidence)) (.snd (app2 step value evidence)) := by
  change Tm.app (Tm.app (inst0 (app2 step value evidence) (rename wk continuation)) _) _ = _
  rw [inst0_rename_wk]
  rfl

/-- One successor equation of the iterator, then its shared beta step. -/
theorem iter_successor_run {n : Nat} (count carrier family step value evidence : Tower.Tm n) :
    Runs (iterApp (sucNative count) carrier family step value evidence)
      (iterApp count carrier family step (.fst (app2 step value evidence))
        (.snd (app2 step value evidence))) := by
  have unfold : Runs (iterApp (sucNative count) carrier family step value evidence)
      (shared step (iterPartial count carrier family step) value evidence) :=
    Runs.equation listed_iterSuc (patternValues ![count, carrier, family, step, value, evidence])
  have contract := Runs.beta (sharedBody (iterPartial count carrier family step))
    (app2 step value evidence)
  rw [shared_contracts] at contract
  exact unfold.trans contract

/-- The iterator at a numeral unfolds to the pair of the value and evidence
after that many steps: termination of the recursive definition on closed
counts, one successor equation and one beta step per successor. -/
theorem iter_runs {n : Nat} (carrier family step : Tower.Tm n) :
    ∀ (count : Nat) (value evidence : Tower.Tm n),
      Runs (iterApp (numeral count) carrier family step value evidence)
        (.pair (iterState step count value evidence).1 (iterState step count value evidence).2)
  | 0, value, evidence =>
      Runs.equation listed_iterZero (patternValues ![carrier, family, step, value, evidence])
  | count + 1, value, evidence =>
      (iter_successor_run (numeral count) carrier family step value evidence).trans
        (iter_runs carrier family step count _ _)

/-- Along the iteration, each value inhabits the carrier and each evidence
inhabits the family at its value, whatever the step computes. -/
theorem iterState_typed {n : Nat} {Γ : Tower.Ctx n} {carrier step : Tower.Tm n}
    {family : Tower.Tm (n + 1)} (stepTyped : Typing R Γ step (stepOver carrier family)) :
    ∀ (count : Nat) {value evidence : Tower.Tm n},
      Typing R Γ value carrier → Typing R Γ evidence (inst0 value family) →
        Typing R Γ (iterState step count value evidence).1 carrier ∧
          Typing R Γ (iterState step count value evidence).2
            (inst0 (iterState step count value evidence).1 family)
  | 0, _, _, valueTyped, evidenceTyped => ⟨valueTyped, evidenceTyped⟩
  | count + 1, _, _, valueTyped, evidenceTyped => by
      have package := CertifiedTransforms.step_application_typed stepTyped valueTyped evidenceTyped
      exact iterState_typed stepTyped count (Typing.fstElim package) (Typing.sndElim package)

/-- The result of the unfolded iterator has the iterator's result type. -/
theorem iter_result_typed {n : Nat} {Γ : Tower.Ctx n} {carrier step value evidence : Tower.Tm n}
    {family : Tower.Tm (n + 1)} {sortHead : Tower.Head}
    (sigmaFormed : Typing R Γ (.sigma carrier family) (.head sortHead))
    (isUniverse : R.isUniverse sortHead)
    (stepTyped : Typing R Γ step (stepOver carrier family))
    (valueTyped : Typing R Γ value carrier) (evidenceTyped : Typing R Γ evidence (inst0 value family))
    (count : Nat) :
    Typing R Γ (.pair (iterState step count value evidence).1 (iterState step count value evidence).2)
      (.sigma carrier family) :=
  have states := iterState_typed stepTyped count valueTyped evidenceTyped
  Typing.pairIntro sigmaFormed isUniverse states.1 states.2


/-! ## Calls through their declared telescopes

A call is typed by instantiating the declaration's generic call, typed once in
its telescope, at a typed substitution. -/

/-- The iterator's generic call, at every count. -/
theorem iterCall_typed :
    Typing R iterSucTelescope (iterApp (.var 5) (.var 4) (.var 3) (.var 2) (.var 1) (.var 0))
      (.sigma (.var 4) (.app (.var 4) (.var 0))) := by
  have i1 := Typing.appElim (iter_typed iterSucTelescope) (Typing.var 5)
  have i2 := Typing.appElim i1 (Typing.var 4)
  have i3 := Typing.appElim i2 (Typing.var 3)
  have i4 := Typing.appElim i3 (Typing.var 2)
  have i5 := Typing.appElim i4 (Typing.var 1)
  exact Typing.appElim i5 (Typing.var 0)

/-! ## The authored execution program over `eqAt`

The runtime prints `(suc zero)` and `(refl (suc zero))` for
`iterCert (suc zero) num eqAt sucStep zero (refl zero)`, and the doubled
values for `composeCert`.  The runs below reach exactly these values, for
every count and start. -/

section EqAtProgram

variable {n : Nat}

/-- The successor move at a numeral: the eliminator's point computes to the
endpoint, then identity elimination returns the reflexivity case. -/
theorem sucMove_numeral (count : Nat) :
    Runs (app2 (.const sucMoveName) (numeral count) (.refl (numeral count)) : Tower.Tm n)
      (.refl (numeral (count + 1))) := by
  have toEliminator : Runs
      (app2 (.const sucMoveName) (numeral count) (.refl (numeral count)) : Tower.Tm n)
      (jApp numT (addNative zeroNative (numeral count)) (sucMotive (numeral count))
        (.refl (sucNative (addNative zeroNative (numeral count)))) (numeral count)
        (.refl (numeral count))) :=
    Runs.equation listed_sucMove (patternValues ![numeral count, .refl (numeral count)])
  have point : Runs
      (jApp numT (addNative zeroNative (numeral count)) (sucMotive (numeral count))
        (.refl (sucNative (addNative zeroNative (numeral count)))) (numeral count)
        (.refl (numeral count)) : Tower.Tm n)
      (jApp numT (numeral count) (sucMotive (numeral count))
        (.refl (sucNative (addNative zeroNative (numeral count)))) (numeral count)
        (.refl (numeral count))) :=
    Runs.app (Runs.app (Runs.app (Runs.app (Runs.app .refl (add_zero_numeral count))
      .refl) .refl) .refl) .refl
  have iota : Runs
      (jApp numT (numeral count) (sucMotive (numeral count))
        (.refl (sucNative (addNative zeroNative (numeral count)))) (numeral count)
        (.refl (numeral count)) : Tower.Tm n)
      (.refl (sucNative (addNative zeroNative (numeral count)))) :=
    Runs.equation listed_jIota (patternValues ![numT, numeral count, sucMotive (numeral count),
      .refl (sucNative (addNative zeroNative (numeral count)))])
  exact toEliminator.trans (point.trans (iota.trans
    (Runs.reflexivity (Runs.app .refl (add_zero_numeral count)))))

theorem sucStep_numeral (count : Nat) :
    Runs (app2 (.const sucStepName) (numeral count) (.refl (numeral count)) : Tower.Tm n)
      (.pair (numeral (count + 1)) (.refl (numeral (count + 1)))) := by
  have toTransport : Runs
      (app2 (.const sucStepName) (numeral count) (.refl (numeral count)) : Tower.Tm n)
      (transportApp numT (.const eqAtName) (.const (constantName .suc)) (.const sucMoveName)
        (numeral count) (.refl (numeral count))) :=
    Runs.equation listed_sucStep (patternValues ![numeral count, .refl (numeral count)])
  have toPair : Runs
      (transportApp numT (.const eqAtName) (.const (constantName .suc)) (.const sucMoveName)
        (numeral count) (.refl (numeral count)) : Tower.Tm n)
      (.pair (sucNative (numeral count))
        (app2 (.const sucMoveName) (numeral count) (.refl (numeral count)))) :=
    Runs.equation listed_transport (patternValues ![numT, .const eqAtName,
      .const (constantName .suc), .const sucMoveName, numeral count, .refl (numeral count)])
  exact toTransport.trans (toPair.trans (Runs.pair .refl (sucMove_numeral count)))

/-- After `count` successor steps from a value computing to `start` with
reflexive evidence, the iteration state computes to `start + count` with
reflexive evidence. -/
theorem sucStep_iterState : ∀ (count start : Nat) {value evidence : Tower.Tm n},
    Runs value (numeral start) → Runs evidence (.refl (numeral start)) →
      Runs (iterState (.const sucStepName) count value evidence).1 (numeral (start + count)) ∧
      Runs (iterState (.const sucStepName) count value evidence).2
        (.refl (numeral (start + count)))
  | 0, _, _, _, valueRuns, evidenceRuns => ⟨valueRuns, evidenceRuns⟩
  | count + 1, start, value, evidence, valueRuns, evidenceRuns => by
      have applied : Runs (app2 (.const sucStepName) value evidence : Tower.Tm n)
          (.pair (numeral (start + 1)) (.refl (numeral (start + 1)))) :=
        (Runs.app (Runs.app .refl valueRuns) evidenceRuns).trans (sucStep_numeral start)
      have next := sucStep_iterState count (start + 1)
        ((Runs.fst applied).trans (Runs.fst_pair _ _))
        ((Runs.snd applied).trans (Runs.snd_pair _ _))
      rw [show start + 1 + count = start + (count + 1) by omega] at next
      exact next

/-- `iterCert m num eqAt sucStep s (refl s)` computes to `(s + m, refl (s + m))`. -/
theorem iter_eqAt_runs (count start : Nat) :
    Runs (iterApp (numeral count) numT (.const eqAtName) (.const sucStepName) (numeral start)
        (.refl (numeral start)) : Tower.Tm n)
      (.pair (numeral (start + count)) (.refl (numeral (start + count)))) := by
  have states := sucStep_iterState (n := n) count start (value := numeral start)
    (evidence := .refl (numeral start)) .refl .refl
  exact (iter_runs _ _ _ count _ _).trans (Runs.pair states.1 states.2)

/-- Both ends of that run have the call's type `Σ y : num. eqAt y`. -/
theorem iter_eqAt_typed {Γ : Tower.Ctx n} (count start : Nat) :
    Typing R Γ (iterApp (numeral count) numT (.const eqAtName) (.const sucStepName)
        (numeral start) (.refl (numeral start))) (.sigma numT (eqAtApp (.var 0))) ∧
      Typing R Γ (.pair (numeral (start + count)) (.refl (numeral (start + count))))
        (.sigma numT (eqAtApp (.var 0))) := by
  constructor
  · have morphism : FormationSensitive.CtxMor R iterSucTelescope Γ
        (patternValues ![numeral count, numT, .const eqAtName, .const sucStepName,
          numeral start, .refl (numeral start)]) := by
      intro index
      fin_cases index
      · exact refl_eqAt start
      · exact numeral_typed start
      · exact sucStep_typed Γ
      · exact eqAtConst_typed Γ
      · exact numT_typed
      · exact numeral_typed count
    exact iterCall_typed.substitute morphism
  · exact Typing.pairIntro (sigma_at numT_typed (eqAt_typed (Typing.var 0)))
      (isUniverseAt Tower.zero) (numeral_typed (start + count)) (refl_eqAt (start + count))

/-- `composeCert num eqAt sucStep sucStep s (refl s)` computes to
`(s + 2, refl (s + 2))`: the first step is shared once and read twice. -/
theorem compose_eqAt_runs (start : Nat) :
    Runs (app6 (.const composeName) numT (.const eqAtName) (.const sucStepName)
        (.const sucStepName) (numeral start) (.refl (numeral start)) : Tower.Tm n)
      (.pair (numeral (start + 2)) (.refl (numeral (start + 2)))) := by
  have unfold : Runs
      (app6 (.const composeName) numT (.const eqAtName) (.const sucStepName)
        (.const sucStepName) (numeral start) (.refl (numeral start)) : Tower.Tm n)
      (shared (.const sucStepName) (.const sucStepName) (numeral start)
        (.refl (numeral start))) :=
    Runs.equation listed_compose (patternValues ![numT, .const eqAtName, .const sucStepName,
      .const sucStepName, numeral start, .refl (numeral start)])
  have contract := Runs.beta (n := n) (sharedBody (.const sucStepName))
    (app2 (.const sucStepName) (numeral start) (.refl (numeral start)))
  rw [shared_contracts] at contract
  have first := sucStep_numeral (n := n) start
  have second := sucStep_numeral (n := n) (start + 1)
  exact unfold.trans (contract.trans
    ((Runs.app (Runs.app .refl ((Runs.fst first).trans (Runs.fst_pair _ _)))
      ((Runs.snd first).trans (Runs.snd_pair _ _))).trans second))

theorem compose_eqAt_typed {Γ : Tower.Ctx n} (start : Nat) :
    Typing R Γ (app6 (.const composeName) numT (.const eqAtName) (.const sucStepName)
        (.const sucStepName) (numeral start) (.refl (numeral start)))
        (.sigma numT (eqAtApp (.var 0))) ∧
      Typing R Γ (.pair (numeral (start + 2)) (.refl (numeral (start + 2))))
        (.sigma numT (eqAtApp (.var 0))) := by
  constructor
  · have morphism : FormationSensitive.CtxMor R composeTelescope Γ
        (patternValues ![numT, .const eqAtName, .const sucStepName, .const sucStepName,
          numeral start, .refl (numeral start)]) := by
      intro index
      fin_cases index
      · exact refl_eqAt start
      · exact numeral_typed start
      · exact sucStep_typed Γ
      · exact sucStep_typed Γ
      · exact eqAtConst_typed Γ
      · exact numT_typed
    exact (composeTyped.instance_typed morphism).1
  · exact Typing.pairIntro (sigma_at numT_typed (eqAt_typed (Typing.var 0)))
      (isUniverseAt Tower.zero) (numeral_typed (start + 2)) (refl_eqAt (start + 2))

/-- The program's `returnIter num eqAt (suc zero) sucStep zero (refl zero)`:
the stored equation returns a closure, five beta steps apply it, and the
iterator computes. -/
theorem returnIter_eqAt_runs :
    Runs (.app (.app (.app (.app (.app (.app (.const returnIterName) numT) (.const eqAtName))
        (numeral 1)) (.const sucStepName)) zeroNative) (.refl zeroNative) : Tower.Tm n)
      (.pair (numeral 1) (.refl (numeral 1))) := by
  have closure : Runs (.app (.const returnIterName) numT : Tower.Tm n)
      (.lam (.lam (.lam (.lam (.lam
        (iterApp (.var 3) numT (.var 4) (.var 2) (.var 1) (.var 0))))))) :=
    Runs.equation listed_returnIter (patternValues ![numT])
  have family : Runs
      (.app (.lam (.lam (.lam (.lam (.lam
        (iterApp (.var 3) numT (.var 4) (.var 2) (.var 1) (.var 0))))))) (.const eqAtName) :
        Tower.Tm n)
      (.lam (.lam (.lam (.lam
        (iterApp (.var 3) numT (.const eqAtName) (.var 2) (.var 1) (.var 0)))))) :=
    Runs.beta _ _
  have count : Runs
      (.app (.lam (.lam (.lam (.lam
        (iterApp (.var 3) numT (.const eqAtName) (.var 2) (.var 1) (.var 0)))))) (numeral 1) :
        Tower.Tm n)
      (.lam (.lam (.lam
        (iterApp (numeral 1) numT (.const eqAtName) (.var 2) (.var 1) (.var 0))))) :=
    Runs.beta _ _
  have step : Runs
      (.app (.lam (.lam (.lam
        (iterApp (numeral 1) numT (.const eqAtName) (.var 2) (.var 1) (.var 0)))))
        (.const sucStepName) : Tower.Tm n)
      (.lam (.lam
        (iterApp (numeral 1) numT (.const eqAtName) (.const sucStepName) (.var 1) (.var 0)))) :=
    Runs.beta _ _
  have value : Runs
      (.app (.lam (.lam
        (iterApp (numeral 1) numT (.const eqAtName) (.const sucStepName) (.var 1) (.var 0))))
        zeroNative : Tower.Tm n)
      (.lam (iterApp (numeral 1) numT (.const eqAtName) (.const sucStepName) zeroNative
        (.var 0))) :=
    Runs.beta _ _
  have evidence : Runs
      (.app (.lam (iterApp (numeral 1) numT (.const eqAtName) (.const sucStepName) zeroNative
        (.var 0))) (.refl zeroNative) : Tower.Tm n)
      (iterApp (numeral 1) numT (.const eqAtName) (.const sucStepName) zeroNative
        (.refl zeroNative)) :=
    Runs.beta _ _
  have calls : Runs
      (.app (.app (.app (.app (.app (.app (.const returnIterName) numT) (.const eqAtName))
        (numeral 1)) (.const sucStepName)) zeroNative) (.refl zeroNative) : Tower.Tm n)
      (.app (.app (.app (.app (.app (.lam (.lam (.lam (.lam (.lam
        (iterApp (.var 3) numT (.var 4) (.var 2) (.var 1) (.var 0)))))))
        (.const eqAtName)) (numeral 1)) (.const sucStepName)) zeroNative) (.refl zeroNative)) :=
    Runs.app (Runs.app (Runs.app (Runs.app (Runs.app closure .refl) .refl) .refl) .refl) .refl
  have first : Runs
      (.app (.app (.app (.app (.app (.lam (.lam (.lam (.lam (.lam
        (iterApp (.var 3) numT (.var 4) (.var 2) (.var 1) (.var 0)))))))
        (.const eqAtName)) (numeral 1)) (.const sucStepName)) zeroNative) (.refl zeroNative) :
        Tower.Tm n)
      (.app (.app (.app (.app (.lam (.lam (.lam (.lam
        (iterApp (.var 3) numT (.const eqAtName) (.var 2) (.var 1) (.var 0))))))
        (numeral 1)) (.const sucStepName)) zeroNative) (.refl zeroNative)) :=
    Runs.app (Runs.app (Runs.app (Runs.app family .refl) .refl) .refl) .refl
  have second : Runs
      (.app (.app (.app (.app (.lam (.lam (.lam (.lam
        (iterApp (.var 3) numT (.const eqAtName) (.var 2) (.var 1) (.var 0))))))
        (numeral 1)) (.const sucStepName)) zeroNative) (.refl zeroNative) : Tower.Tm n)
      (.app (.app (.app (.lam (.lam (.lam
        (iterApp (numeral 1) numT (.const eqAtName) (.var 2) (.var 1) (.var 0)))))
        (.const sucStepName)) zeroNative) (.refl zeroNative)) :=
    Runs.app (Runs.app (Runs.app count .refl) .refl) .refl
  have third : Runs
      (.app (.app (.app (.lam (.lam (.lam
        (iterApp (numeral 1) numT (.const eqAtName) (.var 2) (.var 1) (.var 0)))))
        (.const sucStepName)) zeroNative) (.refl zeroNative) : Tower.Tm n)
      (.app (.app (.lam (.lam
        (iterApp (numeral 1) numT (.const eqAtName) (.const sucStepName) (.var 1) (.var 0))))
        zeroNative) (.refl zeroNative)) :=
    Runs.app (Runs.app step .refl) .refl
  have fourth : Runs
      (.app (.app (.lam (.lam
        (iterApp (numeral 1) numT (.const eqAtName) (.const sucStepName) (.var 1) (.var 0))))
        zeroNative) (.refl zeroNative) : Tower.Tm n)
      (.app (.lam (iterApp (numeral 1) numT (.const eqAtName) (.const sucStepName) zeroNative
        (.var 0))) (.refl zeroNative)) :=
    Runs.app value .refl
  exact calls.trans (first.trans (second.trans (third.trans (fourth.trans
    (evidence.trans (iter_eqAt_runs 1 0))))))

/-- The program's `fst (sucStep (add (suc zero) zero) (refl (add (suc zero) zero)))`:
the arguments compute first, then the step. -/
theorem sucStep_computed_argument_runs :
    Runs (.fst (app2 (.const sucStepName) (addNative (numeral 1) zeroNative)
        (.refl (addNative (numeral 1) zeroNative))) : Tower.Tm n) (numeral 2) :=
  (Runs.fst ((Runs.app (Runs.app .refl (add_zero_run _)) (Runs.reflexivity (add_zero_run _))).trans
    (sucStep_numeral 1))).trans (Runs.fst_pair _ _)

/-- The call typechecks: the evidence `refl (add (suc zero) zero)` inhabits
`eqAt (add (suc zero) zero)` by computation of both sides. -/
theorem sucStep_computed_argument_typed {Γ : Tower.Ctx n} :
    Typing R Γ (app2 (.const sucStepName) (addNative (numeral 1) zeroNative)
      (.refl (addNative (numeral 1) zeroNative))) (.sigma numT (eqAtApp (.var 0))) := by
  have value : Typing R Γ (addNative (numeral 1) zeroNative) numT :=
    addNative_typed (numeral_typed 1) zeroNative_typed
  have evidence : Typing R Γ (.refl (addNative (numeral 1) zeroNative))
      (eqAtApp (addNative (numeral 1) zeroNative)) :=
    Typing.conv (Typing.reflIntro value) (eqAt_typed value) (isUniverseAt Tower.zero)
      (.trans _ _ _ (Runs.conv (Runs.identity .refl (add_zero_run _) (add_zero_run _)))
        (.symm _ _ (.trans _ _ _ (package_step listed_eqAt (at1 (addNative (numeral 1) zeroNative)))
          (Runs.conv (Runs.identity .refl
            ((Runs.app .refl (add_zero_run _)).trans (add_zero_numeral 1)) (add_zero_run _))))))
  have morphism : FormationSensitive.CtxMor R eqAtTelescope Γ
      (patternValues ![addNative (numeral 1) zeroNative, .refl (addNative (numeral 1) zeroNative)]) := by
    intro index
    fin_cases index
    · exact evidence
    · exact value
  exact (sucStepTyped.instance_typed morphism).1

/-- The program's `eqAt (add zero (suc (suc zero)))` computes to the identity
type between the computed numerals. -/
theorem eqAt_computed_runs :
    Runs (eqAtApp (addNative zeroNative (numeral 2)) : Tower.Tm n)
      (.id numT (numeral 2) (numeral 2)) :=
  (Runs.equation listed_eqAt (at1 (addNative zeroNative (numeral 2)))).trans
    (Runs.identity .refl ((Runs.app .refl (add_zero_numeral 2)).trans (add_zero_numeral 2))
      (add_zero_numeral 2))

end EqAtProgram

/-! ### A family given by a lambda

The program also calls the iterator at `(lam k (eqAt (add k zero)))`.  In the
calculus this family converts to `eqAt` pointwise, by beta and the first
equation of `add` at an open argument, so the supplied step checks at the
converted step type and the call runs to the same value.  The runtime
currently reports `BadArgType 4` for this call. -/

section LambdaFamily

variable {n : Nat}

/-- `λ k. eqAt (add k zero)`. -/
def shiftedEqAt : Tower.Tm n := .lam (eqAtApp (addNative (.var 0) zeroNative))

theorem Runs.pi {domain domain' : Tower.Tm n} {codomain codomain' : Tower.Tm (n + 1)}
    (domainRuns : Runs domain domain') (codomainRuns : Runs codomain codomain') :
    Runs (.pi domain codomain) (.pi domain' codomain') :=
  (domainRuns.lift (fun term => Tm.pi term codomain)
      (fun _ _ step => StepCore.congPiDom step)).trans
    (codomainRuns.lift (fun term => Tm.pi domain' term)
      (fun _ _ step => StepCore.congPiCod step))

theorem Runs.sigma {domain domain' : Tower.Tm n} {codomain codomain' : Tower.Tm (n + 1)}
    (domainRuns : Runs domain domain') (codomainRuns : Runs codomain codomain') :
    Runs (.sigma domain codomain) (.sigma domain' codomain') :=
  (domainRuns.lift (fun term => Tm.sigma term codomain)
      (fun _ _ step => StepCore.congSigmaDom step)).trans
    (codomainRuns.lift (fun term => Tm.sigma domain' term)
      (fun _ _ step => StepCore.congSigmaCod step))

/-- The lambda family at any argument computes to `eqAt` there. -/
theorem shiftedEqAt_runs (argument : Tower.Tm n) :
    Runs (.app shiftedEqAt argument) (eqAtApp argument) :=
  (Runs.beta _ argument).trans (Runs.app .refl (add_zero_run argument))

theorem shiftedEqAt_typed {Γ : Tower.Ctx n} : Typing R Γ shiftedEqAt (.pi numT U0) :=
  Typing.lamIntro (pi_at (raise numT_typed) U0_typed) (isUniverseAt level1)
    (eqAt_typed (addNative_typed (Typing.var 0) zeroNative_typed))

/-- The step type over the lambda family converts to the step type over `eqAt`. -/
theorem shifted_step_runs :
    Runs (stepOver numT (.app shiftedEqAt (.var 0)) : Tower.Tm n)
      (stepOver numT (eqAtApp (.var 0))) :=
  Runs.pi .refl (Runs.pi (shiftedEqAt_runs (.var 0))
    (Runs.sigma .refl (shiftedEqAt_runs (.var 0))))

theorem sucStep_shifted_typed {Γ : Tower.Ctx n} :
    Typing R Γ (.const sucStepName) (stepOver numT (.app shiftedEqAt (.var 0))) :=
  Typing.conv (sucStep_typed Γ)
    (CertifiedTransforms.stepOver_typed_cumulative numT_typed
      (Typing.appElim (B := U0) shiftedEqAt_typed (Typing.var 0))
      (isUniverseAt Tower.zero) (Tower.Join.sorts _ _) lowered_zero)
    (isUniverseAt Tower.zero) (.symm _ _ (Runs.conv shifted_step_runs))

/-- The call the runtime rejects is typed, and its run reaches the same value. -/
theorem iter_shifted_typed_runs {Γ : Tower.Ctx n} :
    Typing R Γ (iterApp (numeral 1) numT shiftedEqAt (.const sucStepName) zeroNative
        (.refl zeroNative)) (.sigma numT (.app shiftedEqAt (.var 0))) ∧
      Runs (iterApp (numeral 1) numT shiftedEqAt (.const sucStepName) zeroNative
        (.refl zeroNative) : Tower.Tm n) (.pair (numeral 1) (.refl (numeral 1))) ∧
      Typing R Γ (.pair (numeral 1) (.refl (numeral 1)))
        (.sigma numT (.app shiftedEqAt (.var 0))) := by
  have atValue : ∀ count : Nat, Typing R Γ (.refl (numeral count))
      (.app shiftedEqAt (numeral count)) := fun count =>
    Typing.conv (refl_eqAt count)
      (Typing.appElim (B := U0) shiftedEqAt_typed (numeral_typed count))
      (isUniverseAt Tower.zero) (.symm _ _ (Runs.conv (shiftedEqAt_runs (numeral count))))
  refine ⟨?_, ?_, ?_⟩
  · have morphism : FormationSensitive.CtxMor R iterSucTelescope Γ
        (patternValues ![numeral 1, numT, shiftedEqAt, .const sucStepName, numeral 0,
          .refl (numeral 0)]) := by
      intro index
      fin_cases index
      · exact atValue 0
      · exact numeral_typed 0
      · exact sucStep_shifted_typed
      · exact shiftedEqAt_typed
      · exact numT_typed
      · exact numeral_typed 1
    exact iterCall_typed.substitute morphism
  · have states := sucStep_iterState 1 0 (value := (zeroNative : Tower.Tm n))
      (evidence := .refl zeroNative) .refl .refl
    exact (iter_runs _ _ _ 1 _ _).trans (Runs.pair states.1 states.2)
  · exact Typing.pairIntro
      (sigma_at numT_typed (Typing.appElim (B := U0) shiftedEqAt_typed (Typing.var 0)))
      (isUniverseAt Tower.zero) (numeral_typed 1) (atValue 1)

end LambdaFamily

/-! ## The represented consumer

`holdsAt n` is the proof family of the source equality `add zero n = n`.  Its
step is the translated induction step of the source proof of `zero-add`, and
its base is the translated base case `refl@num zero`.  The evidence the
consumer computes at each value is the compiler's output for the source step,
specialized at that value and at the evidence it received. -/

section Represented

variable {n : Nat}

/-- The compiled induction step with its body's variables supplied: `value`
for the index, `shifted` for the index under the congruence motive's binder,
and `evidence` for the induction hypothesis. -/
def stepEvidenceAt (value : Tower.Tm n) (shifted : Tower.Tm (n + 1)) (evidence : Tower.Tm n) :
    Tower.Tm n :=
  .app (.app (.app (.app (.app (.const SetProfile.substName)
          (.lam (eqNumNative (sucNative (addNative zeroNative shifted)) (sucNative (.var 0)))))
        (addNative zeroNative value))
      value)
    evidence)
    (.app (.const SetProfile.reflName) (sucNative (addNative zeroNative value)))

/-- The translated source step, specialized at `value` and the induction
hypothesis `evidence`. -/
def stepEvidence (value evidence : Tower.Tm n) : Tower.Tm n :=
  stepEvidenceAt value (rename wk value) evidence

theorem zeroAddStepTerm_body :
    zeroAddStepTerm = .lam (.lam (stepEvidenceAt (.var 1) (.var 2) (.var 0))) :=
  rfl

/-- The step's hypotheses: the induction hypothesis, then the assumed facts. -/
def stepHypotheses (evidence : Tower.Tm n) : Fin 4 → Tower.Tm n :=
  Fin.cases evidence (fun index => .const (SetProfile.assumptionNames index))

/-- The compiler's output for the source induction step at object `value` and
induction hypothesis `evidence` is the specialized step. -/
theorem stepEvidence_compiles (value evidence : Tower.Tm n) :
    HOLNativeGenericProofCompiler.Modulo.compileModulo SetProfile.signature
      SetProfile.zeroAddStep (fun _ => value) (stepHypotheses evidence) =
      some (stepEvidence value evidence) :=
  rfl

/-- `holdsMove value evidence` runs the translated step: its stored equation,
then two beta steps, reach the specialized compilation. -/
theorem holdsMove_runs (value evidence : Tower.Tm n) :
    Runs (app2 (.const holdsMoveName) value evidence) (stepEvidence value evidence) := by
  have toStep : Runs (app2 (.const holdsMoveName) value evidence)
      (app2 (.lam (.lam (stepEvidenceAt (.var 1) (.var 2) (.var 0)))) value evidence) :=
    Runs.equation listed_holdsMove (patternValues ![value, evidence])
  have first : Runs (app2 (.lam (.lam (stepEvidenceAt (.var 1) (.var 2) (.var 0)))) value evidence)
      (.app (.lam (subst (liftSub (subst0 value)) (stepEvidenceAt (.var 1) (.var 2) (.var 0))))
        evidence) :=
    Runs.app (Runs.beta _ _) .refl
  have second := Runs.beta
    (subst (liftSub (subst0 value)) (stepEvidenceAt (.var 1) (.var 2) (.var 0))) evidence
  have contracted : inst0 evidence
      (subst (liftSub (subst0 value)) (stepEvidenceAt (.var 1) (.var 2) (.var 0))) =
      stepEvidence value evidence := by
    change stepEvidenceAt (inst0 evidence (rename wk value))
        (subst (liftSub (subst0 evidence)) (rename wk (rename wk value))) evidence = _
    rw [inst0_rename_wk, subst_liftSub_wk,
      show subst (subst0 evidence) (rename wk value) = value from inst0_rename_wk evidence value]
    rfl
  rw [contracted] at second
  exact toStep.trans (first.trans second)

theorem holdsStep_runs (value evidence : Tower.Tm n) :
    Runs (app2 (.const holdsStepName) value evidence)
      (.pair (sucNative value) (stepEvidence value evidence)) := by
  have toTransport : Runs (app2 (.const holdsStepName) value evidence)
      (transportApp numT (.const holdsAtName) (.const (constantName .suc))
        (.const holdsMoveName) value evidence) :=
    Runs.equation listed_holdsStep (patternValues ![value, evidence])
  have toPair : Runs
      (transportApp numT (.const holdsAtName) (.const (constantName .suc))
        (.const holdsMoveName) value evidence)
      (.pair (sucNative value) (app2 (.const holdsMoveName) value evidence)) :=
    Runs.equation listed_transport (patternValues ![numT, .const holdsAtName,
      .const (constantName .suc), .const holdsMoveName, value, evidence])
  exact toTransport.trans (toPair.trans (Runs.pair .refl (holdsMove_runs value evidence)))

/-- The assumed facts, at their proof families, in any context. -/
theorem assumption_typed {Γ : Tower.Ctx n} (index : Fin 3) :
    Typing R Γ (.const (SetProfile.assumptionNames index))
      (liftClosed (FormationSensitiveHOLGenericProofFamily.proof holdsName
        (SetProfile.assumptionCodes index))) := by
  have lookup : R.constantType (SetProfile.assumptionNames index) =
      some (FormationSensitiveHOLGenericProofFamily.proof holdsName
        (SetProfile.assumptionCodes index)) := by
    change combinedType targetRules packageDeclarations _ = _
    rw [combinedType, SetProfile.target_lookup index]
  exact Typing.const lookup (include_target (SetProfile.assumption_formed index))
    (isUniverseAt Tower.zero)

/-- A profile constant at its simple type, in the profile's own rules. -/
theorem sourceConstant_typed {Γ : Tower.Ctx n} {type : HOL.Ty SetProfile.SetBase}
    (symbol : SetProfile.SetConst type) :
    Typing SetProfile.signature.rules Γ (.const (constantName symbol))
      (FormationSensitiveHOLInterface.typeAt SetProfile.types n type) := by
  have closed := SetProfile.declared_typed (SetProfile.lookup_constant symbol)
  have lifted := FormationSensitiveHOLInterface.closed_typed closed Γ
  simp only [liftClosed, FormationSensitiveHOLInterface.typeAt_rename] at lifted
  exact lifted

theorem numeral_source_typed {Γ : Tower.Ctx n} :
    ∀ count : Nat, Typing SetProfile.signature.rules Γ (numeral count) numT
  | 0 => sourceConstant_typed .zero
  | count + 1 => Typing.appElim (B := numT) (sourceConstant_typed .suc) (numeral_source_typed count)

/-- The specialized step is evidence for `holdsAt` at the successor, by the
compiler's typing of the source step at the given object and hypotheses. -/
theorem stepEvidence_typed {Γ : Tower.Ctx n} {value evidence : Tower.Tm n}
    (valueTyped : Typing SetProfile.signature.rules Γ value numT)
    (evidenceTyped : Typing R Γ evidence (holdsAtApp value)) :
    Typing R Γ (stepEvidence value evidence) (holdsAtApp (sucNative value)) := by
  have valueHere : Typing R Γ value numT := include_profile valueTyped
  have premise : Typing R Γ evidence
      (FormationSensitiveHOLGenericProofFamily.proof holdsName (.app motiveCode value)) :=
    Typing.conv evidenceTyped
      (proof_typed (Typing.appElim (B := propT) motiveCode_typed valueHere))
      (isUniverseAt Tower.zero)
      (.trans _ _ _ (package_step listed_holdsAt (at1 value))
        (.symm _ _ (.rel _ _ (.congAppArg (.betaPi _ _)))))
  have objects : HOLNativeGenericProofCompiler.GenericTyping.Objects
      SetProfile.signature (gamma := [numTy]) Γ (fun _ => value) := by
    intro index
    fin_cases index
    exact valueTyped
  have hypotheses : HOLNativeGenericProofCompiler.GenericTyping.Hypotheses
      SetProfile.signature packageOperations (gamma := [numTy])
      (delta := SetProfile.stepAssumptions) Γ (fun _ => value)
      (stepHypotheses evidence) := by
    intro index
    fin_cases index
    · exact ⟨_, rfl, premise⟩
    · exact ⟨_, rfl, assumption_typed 0⟩
    · exact ⟨_, rfl, assumption_typed 1⟩
    · exact ⟨_, rfl, assumption_typed 2⟩
  obtain ⟨code, represented, typed⟩ :=
    HOLNativeGenericProofCompiler.Modulo.compileModulo_typed SetProfile.signature
      holdsName packageOperations SetProfile.realization SetProfile.zeroAddStep
      objects hypotheses (stepEvidence_compiles value evidence)
  have shape : FormationSensitiveHOLInterface.represent SetProfile.signature
      (.app SetProfile.motive (SetProfile.sucT (.var .vz)) :
        HOL.Formula SetProfile.SetConst [numTy]) =
      some (.app motiveCode (sucNative (.var 0))) :=
    rfl
  rw [shape] at represented
  cases represented
  exact Typing.conv typed (holdsAt_typed (sucNative_typed valueHere)) (isUniverseAt Tower.zero)
    (.trans _ _ _ (.rel _ _ (.congAppArg (.betaPi _ _)))
      (.symm _ _ (package_step listed_holdsAt (at1 (sucNative value)))))

/-- The translated base case `refl@num zero`. -/
def holdsBase : Tower.Tm n := .app (.const SetProfile.reflName) zeroNative

theorem holdsBase_typed {Γ : Tower.Ctx n} : Typing R Γ holdsBase (holdsAtApp zeroNative) := by
  have equality := SetProfile.declared_typed (SetProfile.lookup_eqName numTy)
  have lifted := FormationSensitiveHOLInterface.closed_typed equality
    (.snoc Γ (FormationSensitiveHOLInterface.typeAt SetProfile.types n numTy))
  simp only [liftClosed, FormationSensitiveHOLInterface.typeAt_rename] at lifted
  have proposition : Typing SetProfile.signature.rules
      (.snoc Γ (FormationSensitiveHOLInterface.typeAt SetProfile.types n numTy))
      (eqNumNative (.var 0) (.var 0))
      (FormationSensitiveHOLInterface.typeAt SetProfile.types (n + 1) .prop) :=
    Typing.appElim (B := propT) (Typing.appElim (B := .pi numT propT) lifted (Typing.var 0))
      (Typing.var 0)
  have atZero := packageOperations.universalElim
    (SetProfile.simple_formed numTy Γ) proposition (assumption_typed 1)
    (sourceConstant_typed .zero)
  exact Typing.conv atZero (holdsAt_typed zeroNative_typed) (isUniverseAt Tower.zero)
    (.symm _ _ (.trans _ _ _ (package_step listed_holdsAt (at1 zeroNative))
      (Runs.conv (Runs.app .refl (Runs.app (Runs.app .refl (add_zero_run zeroNative)) .refl)))))

/-- The evidence computed from `evidence` at `start` after `count` steps: the
specialized source step at each successive value. -/
def evidenceAfter : Nat → Nat → Tower.Tm n → Tower.Tm n
  | _, 0, evidence => evidence
  | start, count + 1, evidence =>
      evidenceAfter (start + 1) count (stepEvidence (numeral start) evidence)

theorem holds_iterState : ∀ (count start : Nat) {value evidence evidence' : Tower.Tm n},
    Runs value (numeral start) → Runs evidence evidence' →
      Runs (iterState (.const holdsStepName) count value evidence).1 (numeral (start + count)) ∧
      Runs (iterState (.const holdsStepName) count value evidence).2
        (evidenceAfter start count evidence')
  | 0, _, _, _, _, valueRuns, evidenceRuns => ⟨valueRuns, evidenceRuns⟩
  | count + 1, start, value, evidence, evidence', valueRuns, evidenceRuns => by
      have applied : Runs (app2 (.const holdsStepName) value evidence : Tower.Tm n)
          (.pair (numeral (start + 1)) (stepEvidence (numeral start) evidence')) :=
        (Runs.app (Runs.app .refl valueRuns) evidenceRuns).trans
          (holdsStep_runs (numeral start) evidence')
      have next := holds_iterState count (start + 1)
        ((Runs.fst applied).trans (Runs.fst_pair _ _))
        ((Runs.snd applied).trans (Runs.snd_pair _ _))
      rw [show start + 1 + count = start + (count + 1) by omega] at next
      exact next

theorem evidenceAfter_typed {Γ : Tower.Ctx n} : ∀ (count start : Nat) {evidence : Tower.Tm n},
    Typing R Γ evidence (holdsAtApp (numeral start)) →
      Typing R Γ (evidenceAfter start count evidence) (holdsAtApp (numeral (start + count)))
  | 0, _, _, typed => typed
  | count + 1, start, _, typed => by
      have next := evidenceAfter_typed count (start + 1)
        (stepEvidence_typed (numeral_source_typed start) typed)
      rw [show start + 1 + count = start + (count + 1) by omega] at next
      exact next

/-- The consumer at a numeral count: the iterator over `holdsAt` with the
translated step, from the translated base case, computes the value and the
source proof's evidence for it. -/
theorem holds_consumer_runs (count : Nat) :
    Runs (iterApp (numeral count) numT (.const holdsAtName) (.const holdsStepName) zeroNative
        holdsBase : Tower.Tm n)
      (.pair (numeral count) (evidenceAfter 0 count holdsBase)) := by
  have states := holds_iterState (n := n) count 0 (value := zeroNative) (evidence := holdsBase)
    (evidence' := holdsBase) .refl .refl
  rw [Nat.zero_add] at states
  exact (iter_runs _ _ _ count _ _).trans (Runs.pair states.1 states.2)

theorem holds_consumer_typed {Γ : Tower.Ctx n} (count : Nat) :
    Typing R Γ (iterApp (numeral count) numT (.const holdsAtName) (.const holdsStepName)
        zeroNative holdsBase) (.sigma numT (holdsAtApp (.var 0))) ∧
      Typing R Γ (.pair (numeral count) (evidenceAfter 0 count holdsBase))
        (.sigma numT (holdsAtApp (.var 0))) := by
  constructor
  · have morphism : FormationSensitive.CtxMor R iterSucTelescope Γ
        (patternValues ![numeral count, numT, .const holdsAtName, .const holdsStepName,
          zeroNative, holdsBase]) := by
      intro index
      fin_cases index
      · exact holdsBase_typed
      · exact zeroNative_typed
      · exact holdsStep_typed Γ
      · exact holdsAtConst_typed Γ
      · exact numT_typed
      · exact numeral_typed count
    exact iterCall_typed.substitute morphism
  · have evidence := evidenceAfter_typed (Γ := Γ) count 0 holdsBase_typed
    rw [Nat.zero_add] at evidence
    exact Typing.pairIntro (sigma_at numT_typed (holdsAt_typed (Typing.var 0)))
      (isUniverseAt Tower.zero) (numeral_typed count) evidence

/-- At an open index `n` with evidence `h : holdsAt n`, the step runs to
`(suc n, step n h)`, and that evidence is typed at `holdsAt (suc n)`: it is
the source proof's step, specialized at the neutral index. -/
theorem holds_open_index :
    Runs (app2 (.const holdsStepName) (.var 1) (.var 0) : Tower.Tm 2)
        (.pair (sucNative (.var 1)) (stepEvidence (.var 1) (.var 0))) ∧
      Typing R holdsAtTelescope (stepEvidence (.var 1) (.var 0))
        (holdsAtApp (sucNative (.var 1))) ∧
      Typing R holdsAtTelescope (.pair (sucNative (.var 1)) (stepEvidence (.var 1) (.var 0)))
        (.sigma numT (holdsAtApp (.var 0))) := by
  have evidence := stepEvidence_typed (Γ := holdsAtTelescope) (value := .var 1)
    (evidence := .var 0) (Typing.var 1) (Typing.var 0)
  refine ⟨holdsStep_runs _ _, evidence, ?_⟩
  exact Typing.pairIntro (sigma_at numT_typed (holdsAt_typed (Typing.var 0)))
    (isUniverseAt Tower.zero) (sucNative_typed (Typing.var 1)) evidence

/-- The iterator at an open count is typed at the consumer's type. -/
theorem holds_open_count :
    Typing R (.snoc .nil numT)
      (iterApp (.var 0) numT (.const holdsAtName) (.const holdsStepName) zeroNative holdsBase)
      (.sigma numT (holdsAtApp (.var 0))) := by
  have morphism : FormationSensitive.CtxMor R iterSucTelescope (.snoc .nil numT)
      (patternValues ![.var 0, numT, .const holdsAtName, .const holdsStepName, zeroNative,
        holdsBase]) := by
    intro index
    fin_cases index
    · exact holdsBase_typed
    · exact zeroNative_typed
    · exact holdsStep_typed _
    · exact holdsAtConst_typed _
    · exact numT_typed
    · exact Typing.var 0
  exact iterCall_typed.substitute morphism

end Represented

/-! ## Axiom audit -/

#print axioms iter_runs
#print axioms iterState_typed
#print axioms iter_result_typed
#print axioms iter_eqAt_runs
#print axioms iter_eqAt_typed
#print axioms compose_eqAt_runs
#print axioms compose_eqAt_typed
#print axioms returnIter_eqAt_runs
#print axioms sucStep_computed_argument_runs
#print axioms sucStep_computed_argument_typed
#print axioms eqAt_computed_runs
#print axioms iter_shifted_typed_runs
#print axioms stepEvidence_compiles
#print axioms holdsMove_runs
#print axioms stepEvidence_typed
#print axioms holdsBase_typed
#print axioms holds_consumer_runs
#print axioms holds_consumer_typed
#print axioms holds_open_index
#print axioms holds_open_count

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.Execution
