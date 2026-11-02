import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionSearch

/-!
# Checked certificates from bounded structural conversion production

Every produced candidate retains a recipe accepted by the existing decoder
at its actual input and output. The result holds for arbitrary root search:
a proposed root is used only when its decoded source matches the current term.
The normalization gate therefore returns the same produced candidate.

These are equations about the unchanged producer and checker. They establish
bounded candidate-certificate correctness, not normal-form completeness,
typed strong normalization, or independence of the result from fuel.
-/
set_option autoImplicit false
namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.StructuralConversionSearch
open StructuralConversionCode
variable {Head : Type} {RootCode : Nat → Type} [DecidableEq Head]
variable (headEq : Head → Head → Prop) [DecidableRel headEq]
variable (decodeRoot : {n : Nat} → RootCode n → Option (Tm Head n × Tm Head n))
    (searchRoot : {n : Nat} → Tm Head n → Option (RootCode n))

private def rootNext {n : Nat} (term : Tm Head n) :
    Option (Tm Head n × Code Head RootCode n) := do
  let proposed ← searchRoot term
  let (left,right) ← decodeRoot proposed
  if left = term then some (right,Code.single (.root proposed)) else none

private def next {n : Nat} (term : Tm Head n) :
    Option (Tm Head n × Code Head RootCode n) :=
  match term with
  | .app (.lam body) argument => some (inst0 argument body,Code.single (.betaPi body argument))
  | .fst (.pair first second) => some (first,Code.single (.betaSigmaFst first second))
  | .snd (.pair first second) => some (second,Code.single (.betaSigmaSnd first second))
  | term => rootNext decodeRoot searchRoot term

private theorem rootNext_checked {n : Nat} {source target : Tm Head n}
    {step : Code Head RootCode n}
    (selected : rootNext decodeRoot searchRoot source = some (target,step)) :
    step.check headEq decodeRoot source target = true := by
  cases proposed : searchRoot source with
  | none => simp [rootNext,proposed] at selected
  | some root =>
      cases decoded : decodeRoot root with
      | none => simp [rootNext,proposed,decoded] at selected
      | some endpoints =>
          rcases endpoints with ⟨left,right⟩
          by_cases same : left = source
          · subst left
            simp only [rootNext,proposed,decoded,Option.bind_eq_bind,Option.bind_some,
              ↓reduceIte,Option.some.injEq,Prod.mk.injEq] at selected
            rcases selected with ⟨rfl,rfl⟩
            simp [Code.check,Code.decode,StepCode.decode,decoded]
          · simp [rootNext,proposed,decoded,same] at selected

private theorem next_checked {n : Nat} {source target : Tm Head n}
    {step : Code Head RootCode n}
    (selected : next decodeRoot searchRoot source = some (target,step)) :
    step.check headEq decodeRoot source target = true := by
  cases source <;> try exact rootNext_checked headEq decodeRoot searchRoot selected
  case app function argument =>
    cases function <;> try exact rootNext_checked headEq decodeRoot searchRoot selected
    simp only [next,Option.some.injEq,Prod.mk.injEq] at selected
    rcases selected with ⟨rfl,rfl⟩
    simp [Code.check,Code.decode,StepCode.decode]
  case fst pair =>
    cases pair <;> try exact rootNext_checked headEq decodeRoot searchRoot selected
    simp only [next,Option.some.injEq,Prod.mk.injEq] at selected
    rcases selected with ⟨rfl,rfl⟩
    simp [Code.check,Code.decode,StepCode.decode]
  case snd pair =>
    cases pair <;> try exact rootNext_checked headEq decodeRoot searchRoot selected
    simp only [next,Option.some.injEq,Prod.mk.injEq] at selected
    rcases selected with ⟨rfl,rfl⟩
    simp [Code.check,Code.decode,StepCode.decode]

private theorem produce_finish_checked (fuel : Nat) :
    (∀ {n : Nat} (term : Tm Head n),
      (produce decodeRoot searchRoot fuel term).recipe.check headEq decodeRoot
        term (produce decodeRoot searchRoot fuel term).term = true) ∧
    (∀ {n : Nat} (source : Tm Head n) (candidate : Candidate Head RootCode n),
      candidate.recipe.check headEq decodeRoot source candidate.term = true →
      (finish decodeRoot searchRoot fuel candidate).recipe.check headEq decodeRoot
        source (finish decodeRoot searchRoot fuel candidate).term = true) := by
  induction fuel with
  | zero =>
      constructor
      · intro n term
        exact Code.check_refl headEq decodeRoot term
      · intro n source candidate checked
        exact checked
  | succ fuel ih =>
      constructor
      · intro n term
        cases term <;> simp only [produce] <;> apply ih.2
        case var index => exact Code.check_refl headEq decodeRoot _
        case head head => exact Code.check_refl headEq decodeRoot _
        case const name => exact Code.check_refl headEq decodeRoot _
        case pi domain body => exact Code.check_congPi headEq decodeRoot (ih.1 domain) (ih.1 body)
        case sigma domain body => exact Code.check_congSigma headEq decodeRoot (ih.1 domain) (ih.1 body)
        case lam body => exact Code.check_congLam headEq decodeRoot (ih.1 body)
        case app function argument => exact Code.check_congApp headEq decodeRoot (ih.1 function) (ih.1 argument)
        case pair first second => exact Code.check_congPair headEq decodeRoot (ih.1 first) (ih.1 second)
        case fst pair => exact Code.check_congFst headEq decodeRoot (ih.1 pair)
        case snd pair => exact Code.check_congSnd headEq decodeRoot (ih.1 pair)
        case refl subject => exact Code.check_congRefl headEq decodeRoot (ih.1 subject)
        case id carrier left right => exact Code.check_congId headEq decodeRoot (ih.1 carrier) (ih.1 left) (ih.1 right)
      · intro n source candidate checked
        change (match next decodeRoot searchRoot candidate.term with
          | none => candidate
          | some (term,step) =>
              let rest := produce decodeRoot searchRoot fuel term
              ⟨rest.term,.trans candidate.recipe (.trans step rest.recipe)⟩).recipe.check
            headEq decodeRoot source
            (match next decodeRoot searchRoot candidate.term with
            | none => candidate
            | some (term,step) =>
                let rest := produce decodeRoot searchRoot fuel term
                ⟨rest.term,.trans candidate.recipe (.trans step rest.recipe)⟩).term = true
        cases selected : next decodeRoot searchRoot candidate.term with
        | none => exact checked
        | some result =>
            rcases result with ⟨term,step⟩
            exact Code.check_trans headEq decodeRoot checked
              (Code.check_trans headEq decodeRoot
                (next_checked headEq decodeRoot searchRoot selected) (ih.1 term))

theorem produce_checked (fuel : Nat) {n : Nat} (term : Tm Head n) :
    (produce decodeRoot searchRoot fuel term).recipe.check headEq decodeRoot
      term (produce decodeRoot searchRoot fuel term).term = true :=
  (produce_finish_checked headEq decodeRoot searchRoot fuel).1 term

#print axioms produce_checked

variable {root : RootComputation Head}

theorem normalize_eq_some_produce (decoder : RootDecoder root)
    (findRoot : {n : Nat} → Tm Head n → Option (decoder.Code n))
    (fuel : Nat) {n : Nat} (term : Tm Head n) :
    normalize decoder findRoot (headEq := headEq) fuel term =
      some (produce decoder.decode findRoot fuel term) := by
  dsimp only [normalize]
  rw [produce_checked headEq decoder.decode findRoot fuel term]
  rfl

#print axioms normalize_eq_some_produce

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.StructuralConversionSearch
