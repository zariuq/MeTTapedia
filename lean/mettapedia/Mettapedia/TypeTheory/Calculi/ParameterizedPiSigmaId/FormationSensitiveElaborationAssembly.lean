import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveElaboration

/-!
# Composition equations for the original bounded evidence producer

Each equation assembles one original producer call from its actual smaller
calls. The returned code is unchanged. The premises describe production;
independent replay and ambient-context formation remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.FormationSensitiveElaboration

variable {Head : Type} {RootCode : Nat → Type} (R : Rules Head)
    (choices : Choices Head RootCode) [DecidableEq Head]

theorem synth_application_of (fuel : Nat) {n : Nat} (context : Ctx Head n)
    (function argument : Tm Head n) (notLambda : ∀ body, function ≠ .lam body)
    (inferred : Inferred Head RootCode n) (domain : Tm Head n) (body : Tm Head (n+1))
    (functionCode argumentCode : Code Head RootCode n)
    (prior : synth R choices fuel context function = some inferred)
    (view : choices.normalize fuel inferred.type = .pi domain body)
    (aligned : align R choices fuel context function inferred.type (.pi domain body) inferred.evidence = some functionCode)
    (checked : check R choices fuel context argument domain = some argumentCode) :
    synth R choices (fuel+1) context (.app function argument) =
      some ⟨inst0 argument body,.appElim domain body functionCode argumentCode⟩ := by
  cases function <;> try { exact False.elim (notLambda _ rfl) }
  all_goals simp only [synth,prior,Option.bind_eq_bind,Option.bind_some,view,aligned,checked,Option.pure_def]

theorem synth_lambda_application_of (fuel : Nat) {n : Nat} (context : Ctx Head n)
    (body : Tm Head (n+1)) (argument : Tm Head n)
    (argumentInferred : Inferred Head RootCode n) (bodyInferred : Inferred Head RootCode (n+1))
    (level : Head) (formation : Code Head RootCode n)
    (argumentProduced : synth R choices fuel context argument = some argumentInferred)
    (bodyProduced : synth R choices fuel (.snoc context argumentInferred.type) body = some bodyInferred)
    (formationProduced : synth R choices fuel context (.pi argumentInferred.type bodyInferred.type) =
      some ⟨.head level,formation⟩) :
    synth R choices (fuel+1) context (.app (.lam body) argument) =
      some ⟨inst0 argument bodyInferred.type,
        .appElim argumentInferred.type bodyInferred.type
          (.lamIntro level formation bodyInferred.evidence) argumentInferred.evidence⟩ := by
  simp only [synth,argumentProduced,bodyProduced,formationProduced,
    Option.bind_eq_bind,Option.bind_some,Option.pure_def]

theorem check_lambda_of (fuel : Nat) {n : Nat} (context : Ctx Head n)
    (body : Tm Head (n+1)) (expected domain : Tm Head n) (codomain : Tm Head (n+1))
    (level : Head) (formation : Code Head RootCode n) (bodyCode : Code Head RootCode (n+1))
    (result : Code Head RootCode n)
    (view : choices.normalize fuel expected = .pi domain codomain)
    (formed : synth R choices fuel context (.pi domain codomain) = some ⟨.head level,formation⟩)
    (checked : check R choices fuel (.snoc context domain) body codomain = some bodyCode)
    (aligned : align R choices fuel context (.lam body) (.pi domain codomain) expected
      (.lamIntro level formation bodyCode) = some result) :
    check R choices (fuel+1) context (.lam body) expected = some result := by
  simp only [check,view,formed,checked,aligned,Option.bind_eq_bind,Option.bind_some]

theorem check_pair_of (fuel : Nat) {n : Nat} (context : Ctx Head n)
    (first second expected domain : Tm Head n) (codomain : Tm Head (n+1))
    (level : Head) (formation firstCode secondCode result : Code Head RootCode n)
    (view : choices.normalize fuel expected = .sigma domain codomain)
    (formed : synth R choices fuel context (.sigma domain codomain) = some ⟨.head level,formation⟩)
    (firstProduced : check R choices fuel context first domain = some firstCode)
    (secondProduced : check R choices fuel context second (inst0 first codomain) = some secondCode)
    (aligned : align R choices fuel context (.pair first second) (.sigma domain codomain) expected
      (.pairIntro level formation firstCode secondCode) = some result) :
    check R choices (fuel+1) context (.pair first second) expected = some result := by
  simp only [check,view,formed,firstProduced,secondProduced,aligned,Option.bind_eq_bind,Option.bind_some]

theorem check_refl_of (fuel : Nat) {n : Nat} (context : Ctx Head n)
    (point expected carrier left right : Tm Head n) (pointCode result : Code Head RootCode n)
    (view : choices.normalize fuel expected = .id carrier left right)
    (checked : check R choices fuel context point carrier = some pointCode)
    (aligned : align R choices fuel context (.refl point) (.id carrier point point) expected
      (.reflIntro carrier pointCode) = some result) :
    check R choices (fuel+1) context (.refl point) expected = some result := by
  simp only [check,view,checked,aligned,Option.bind_eq_bind,Option.bind_some]

#print axioms synth_application_of
#print axioms synth_lambda_application_of
#print axioms check_lambda_of
#print axioms check_pair_of
#print axioms check_refl_of

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.FormationSensitiveElaboration
