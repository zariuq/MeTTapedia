import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativeConversion
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.FormationSensitiveHOLProofConversion
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AlgebraicParallelSubstitution

/-!
# Parallel development of the exact HOL proof-decoder equations

The two opaque, constant-headed decoder equations are presented by their
actual open schemas. Parallel development includes native beta, projections,
head equality and both decoder contractions. No additional equation is
installed, and the conversion observation is not used as a reflection map.

Complete development proves Church--Rosser for this exact presentation,
then Pi/Sigma component injectivity and contextual subject reduction. This
does not establish normalization, semantic consistency or compatibility
with separately added native list or identity-eliminator computation rules.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.FormationSensitiveHOLProofConfluence

open Presentation Presentation.Declaration Presentation.AlgebraicSchema
open Presentation.AlgebraicParallel Presentation.ConversionCoherence
open FormationSensitiveHOLProofFamily

def implicationLeft : Tower.Tm 2 := proof (Source.rawImp (.var 0) (.var 1))
def implicationRight : Tower.Tm 2 := implicationFamily (.var 0) (.var 1)
def universalLeft : Tower.Tm 2 := proof (universalProposition (.var 0) (.var 1))
def universalRight : Tower.Tm 2 := universalFamily (.var 0) (.var 1)

inductive Schema : SchemaFamily Tower.Head where
  | implication : Schema implicationLeft implicationRight
  | universal : Schema universalLeft universalRight

def arguments {n : Nat} (first second : Tower.Tm n) : Sub Tower.Head 2 n :=
  Fin.cases first (Fin.cases second Fin.elim0)

theorem schema_sound {arity n : Nat} {left right : Tower.Tm arity}
    (schema : Schema left right) (sigma : Sub Tower.Head arity n) :
    rules.computation.step (subst sigma left) (subst sigma right) := by
  cases schema with
  | implication =>
      have actual : rules.computation.step (proof (Source.rawImp (sigma 0) (sigma 1)))
          (implicationFamily (sigma 0) (sigma 1)) := .declared (.implication _ _)
      simpa only [implicationLeft, implicationRight, proof_subst,
        implicationFamily_subst, Source.rawImp, FormationSensitiveHOLUniformList.rawImp, subst]
        using actual
  | universal =>
      have actual : rules.computation.step (proof (universalProposition (sigma 0) (sigma 1)))
          (universalFamily (sigma 0) (sigma 1)) := .declared (.universal _ _)
      simpa only [universalLeft, universalRight, proof_subst,
        universalFamily_subst, universalProposition, subst]
        using actual

theorem schema_cover {n : Nat} {source target : Tower.Tm n}
    (step : rules.computation.step source target) :
    ∃ (arity : Nat) (left right : Tower.Tm arity) (sigma : Sub Tower.Head arity n),
      Schema left right ∧ subst sigma left = source ∧ subst sigma right = target := by
  cases step with
  | inherited impossible => cases impossible
  | delta lookup =>
      rw [FormationSensitiveHOLProofConversion.declarations_opaque] at lookup
      cases lookup
  | declared decoder =>
      cases decoder with
      | implication p q =>
          refine ⟨2, implicationLeft, implicationRight, arguments p q, .implication, rfl, ?_⟩
          simp only [implicationRight, implicationFamily_subst, subst]
          rfl
      | universal a f =>
          refine ⟨2, universalLeft, universalRight, arguments a f, .universal, rfl, ?_⟩
          simp only [universalRight, universalFamily_subst, subst]
          rfl

def schemaPresentation : SchemaPresentation rules where
  schema := Schema
  sound := schema_sound
  cover := schema_cover

abbrev Par {n : Nat} : Tower.Tm n → Tower.Tm n → Prop := schemaPresentation.Par

theorem schema_left_linear : LeftLinearFamily Schema := by
  intro arity left right schema
  cases schema <;> intro index <;>
    exact Fin.cases (by decide) (fun remaining =>
      Fin.cases (by decide) (fun impossible => Fin.elim0 impossible) remaining) index

private theorem par_const_aux {n : Nat} {source target : Tower.Tm n}
    (step : Par source target) : ∀ name, source = .const name → target = .const name := by
  cases step with
  | const name => intro other equality; exact equality
  | algebraic schema sigma tau inner =>
      cases schema <;> intro name equality <;> cases equality
  | _ => intro name equality; cases equality

theorem par_const {n : Nat} {name : DeclName} {target : Tower.Tm n}
    (step : Par (.const name) target) : target = .const name := par_const_aux step name rfl

private theorem par_lam_aux {n : Nat} {source target : Tower.Tm n}
    (step : Par source target) : ∀ body, source = .lam body →
      ∃ body', target = .lam body' ∧ Par body body' := by
  cases step with
  | lam inner => intro body equality; cases equality; exact ⟨_, rfl, inner⟩
  | algebraic schema sigma tau inner =>
      cases schema <;> intro body equality <;> cases equality
  | _ => intro body equality; cases equality

theorem par_lam {n : Nat} {body : Tower.Tm (n + 1)} {target : Tower.Tm n}
    (step : Par (.lam body) target) : ∃ body', target = .lam body' ∧ Par body body' :=
  par_lam_aux step body rfl

private theorem par_pair_aux {n : Nat} {source target : Tower.Tm n}
    (step : Par source target) : ∀ first second, source = .pair first second →
      ∃ first' second', target = .pair first' second' ∧ Par first first' ∧ Par second second' := by
  cases step with
  | pair left right => intro first second equality; cases equality; exact ⟨_, _, rfl, left, right⟩
  | algebraic schema sigma tau inner =>
      cases schema <;> intro first second equality <;> cases equality
  | _ => intro first second equality; cases equality

theorem par_pair {n : Nat} {first second target : Tower.Tm n}
    (step : Par (.pair first second) target) :
    ∃ first' second', target = .pair first' second' ∧ Par first first' ∧ Par second second' :=
  par_pair_aux step first second rfl

private theorem par_rigid_one_aux {n : Nat} {source target : Tower.Tm n}
    (step : Par source target) : ∀ name argument,
      name ≠ proofName → source = .app (.const name) argument →
      ∃ argument', target = .app (.const name) argument' ∧ Par argument argument' := by
  cases step with
  | app function argument =>
      intro name input distinct equality
      cases equality
      obtain rfl := par_const function
      exact ⟨_, rfl, argument⟩
  | algebraic schema sigma tau inner =>
      cases schema <;> intro name argument distinct equality <;>
        have heads := Tm.const.inj (Tm.app.inj equality).1 <;>
        exact False.elim (distinct heads.symm)
  | _ => intro name argument distinct equality; cases equality

theorem par_rigid_one {n : Nat} {name : DeclName} {argument target : Tower.Tm n}
    (distinct : name ≠ proofName) (step : Par (.app (.const name) argument) target) :
    ∃ argument', target = .app (.const name) argument' ∧ Par argument argument' :=
  par_rigid_one_aux step name argument distinct rfl

private theorem par_rigid_two_aux {n : Nat} {source target : Tower.Tm n}
    (step : Par source target) : ∀ name first second,
      name ≠ proofName → source = .app (.app (.const name) first) second →
      ∃ first' second', target = .app (.app (.const name) first') second' ∧
        Par first first' ∧ Par second second' := by
  cases step with
  | app function argument =>
      intro name first second distinct equality
      cases equality
      obtain ⟨first', rfl, firstStep⟩ := par_rigid_one distinct function
      exact ⟨first', _, rfl, firstStep, argument⟩
  | algebraic schema sigma tau inner =>
      cases schema <;> intro name first second distinct equality <;> cases equality
  | _ => intro name first second distinct equality; cases equality

theorem par_rigid_two {n : Nat} {name : DeclName} {first second target : Tower.Tm n}
    (distinct : name ≠ proofName) (step : Par (.app (.app (.const name) first) second) target) :
    ∃ first' second', target = .app (.app (.const name) first') second' ∧
      Par first first' ∧ Par second second' :=
  par_rigid_two_aux step name first second distinct rfl

def develop {n : Nat} : Tower.Tm n → Tower.Tm n
  | .var index => .var index
  | .const name => .const name
  | .head head => .head head
  | .pi domain codomain => .pi (develop domain) (develop codomain)
  | .sigma domain codomain => .sigma (develop domain) (develop codomain)
  | .id carrier left right => .id (develop carrier) (develop left) (develop right)
  | .lam body => .lam (develop body)
  | .app (.lam body) argument => inst0 (develop argument) (develop body)
  | .app (.const name) (.app (.app (.const operation) first) second) =>
      if name = proofName ∧ operation = `HOLUniformList.implication then
        implicationFamily (develop first) (develop second)
      else if name = proofName ∧ operation = `HOLUniformList.universal then
        universalFamily (develop first) (develop second)
      else .app (.const name) (develop (.app (.app (.const operation) first) second))
  | .app function argument => .app (develop function) (develop argument)
  | .pair first second => .pair (develop first) (develop second)
  | .fst (.pair first _) => develop first
  | .fst term => .fst (develop term)
  | .snd (.pair _ second) => develop second
  | .snd term => .snd (develop term)
  | .refl term => .refl (develop term)

theorem develop_implication {n : Nat} (p q : Tower.Tm n) :
    develop (proof (Source.rawImp p q)) = implicationFamily (develop p) (develop q) := by
  simp only [proof, Source.rawImp, FormationSensitiveHOLUniformList.rawImp, develop,
    and_self, ↓reduceIte]

theorem develop_universal {n : Nat} (a f : Tower.Tm n) :
    develop (proof (universalProposition a f)) = universalFamily (develop a) (develop f) := by
  have different : (`HOLUniformList.universal : DeclName) ≠ `HOLUniformList.implication := by decide
  simp only [proof, universalProposition, develop, different, and_false, and_self, ↓reduceIte]

theorem develop_app_plain {n : Nat} (function argument : Tower.Tm n)
    (noLambda : ∀ body, function ≠ .lam body)
    (noImplication : ¬ ∃ p q, function = .const proofName ∧ argument = Source.rawImp p q)
    (noUniversal : ¬ ∃ a f, function = .const proofName ∧ argument = universalProposition a f) :
    develop (.app function argument) = .app (develop function) (develop argument) := by
  cases function with
  | lam body => exact False.elim (noLambda body rfl)
  | const name =>
      cases argument with
      | app inner second =>
          cases inner with
          | app head first =>
              cases head with
              | const operation =>
                  have notImp : ¬ (name = proofName ∧ operation = `HOLUniformList.implication) := by
                    rintro ⟨rfl, rfl⟩
                    exact noImplication ⟨first, second, rfl, rfl⟩
                  have notAll : ¬ (name = proofName ∧ operation = `HOLUniformList.universal) := by
                    rintro ⟨rfl, rfl⟩
                    exact noUniversal ⟨first, second, rfl, rfl⟩
                  simp only [develop, if_neg notImp, if_neg notAll]
              | _ => rfl
          | _ => rfl
      | _ => rfl
  | _ => rfl

theorem develop_rigid_one {n : Nat} (name : DeclName) (argument : Tower.Tm n)
    (distinct : name ≠ proofName) :
    develop (.app (.const name) argument) = .app (.const name) (develop argument) := by
  apply develop_app_plain
  · intro body impossible
    cases impossible
  · rintro ⟨p, q, equality, _⟩
    exact distinct (Tm.const.inj equality)
  · rintro ⟨a, f, equality, _⟩
    exact distinct (Tm.const.inj equality)

theorem develop_rigid_two {n : Nat} (name : DeclName) (first second : Tower.Tm n)
    (distinct : name ≠ proofName) :
    develop (.app (.app (.const name) first) second) =
      .app (.app (.const name) (develop first)) (develop second) := by
  rw [develop_app_plain]
  · rw [develop_rigid_one name first distinct]
  · intro body impossible
    cases impossible
  · rintro ⟨p, q, impossible, _⟩
    cases impossible
  · rintro ⟨a, f, impossible, _⟩
    cases impossible

theorem par_implication {n : Nat} {p p' q q' : Tower.Tm n}
    (first : Par p p') (second : Par q q') :
    Par (proof (Source.rawImp p q)) (implicationFamily p' q') := by
  change Par (subst (arguments p q) implicationLeft) (subst (arguments p' q') implicationRight)
  exact .algebraic Schema.implication _ _ (.cons first (.cons second .nil))

theorem par_universal {n : Nat} {a a' f f' : Tower.Tm n}
    (domain : Par a a') (predicate : Par f f') :
    Par (proof (universalProposition a f)) (universalFamily a' f') := by
  change Par (subst (arguments a f) universalLeft) (subst (arguments a' f') universalRight)
  exact .algebraic Schema.universal _ _ (.cons domain (.cons predicate .nil))

/-- Recognition of the fixed decoder pattern is a finite syntax inspection;
the complete-development proof needs no choice of a logical witness. -/
private def decoderDecision {n : Nat} (operation : DeclName) (function argument : Tower.Tm n) :
    Decidable (∃ first second, function = .const proofName ∧
      argument = .app (.app (.const operation) first) second) := by
  cases function with
  | const name =>
      by_cases same : name = proofName
      · subst name
        cases argument with
        | app inner second =>
            cases inner with
            | app head first =>
                cases head with
                | const name =>
                    by_cases sameOperation : name = operation
                    · subst name
                      exact .isTrue ⟨first, second, rfl, rfl⟩
                    · exact .isFalse (by
                        rintro ⟨a, b, _, equality⟩
                        exact sameOperation (Tm.const.inj (Tm.app.inj (Tm.app.inj equality).1).1))
                | _ => exact .isFalse (by rintro ⟨a, b, _, equality⟩; cases equality)
            | _ => exact .isFalse (by rintro ⟨a, b, _, equality⟩; cases equality)
        | _ => exact .isFalse (by rintro ⟨a, b, _, equality⟩; cases equality)
      · exact .isFalse (by
          rintro ⟨a, b, equality, _⟩
          exact same (Tm.const.inj equality))
  | _ => exact .isFalse (by rintro ⟨a, b, equality, _⟩; cases equality)

/-- The decoder/congruence peak closes using the same two developed
operands. The constant-headed HOL operators cannot themselves contract. -/
theorem develop_application {n : Nat} {function function' argument argument' : Tower.Tm n}
    (functionStep : Par function function') (argumentStep : Par argument argument')
    (functionDevelop : Par function' (develop function))
    (argumentDevelop : Par argument' (develop argument)) :
    Par (.app function' argument') (develop (.app function argument)) := by
  let _ : Decidable (∃ p q, function = .const proofName ∧ argument = Source.rawImp p q) :=
    decoderDecision `HOLUniformList.implication function argument
  let _ : Decidable (∃ a f, function = .const proofName ∧ argument = universalProposition a f) :=
    decoderDecision `HOLUniformList.universal function argument
  by_cases implication : ∃ p q, function = .const proofName ∧ argument = Source.rawImp p q
  · obtain ⟨p, q, rfl, rfl⟩ := implication
    obtain rfl := par_const functionStep
    obtain ⟨p', q', rfl, _, _⟩ := par_rigid_two (by decide) argumentStep
    unfold FormationSensitiveHOLUniformList.rawImp at argumentDevelop
    rw [develop_rigid_two `HOLUniformList.implication p q (by decide)] at argumentDevelop
    obtain ⟨p'', q'', shape, first, second⟩ := par_rigid_two (by decide) argumentDevelop
    obtain ⟨functionShape, rfl⟩ := Tm.app.inj shape
    obtain ⟨_, rfl⟩ := Tm.app.inj functionShape
    change Par (proof (Source.rawImp p' q')) (develop (proof (Source.rawImp p q)))
    rw [develop_implication]
    exact par_implication first second
  by_cases universal : ∃ a f, function = .const proofName ∧ argument = universalProposition a f
  · obtain ⟨a, f, rfl, rfl⟩ := universal
    obtain rfl := par_const functionStep
    obtain ⟨a', f', rfl, _, _⟩ := par_rigid_two (by decide) argumentStep
    unfold universalProposition at argumentDevelop
    rw [develop_rigid_two `HOLUniformList.universal a f (by decide)] at argumentDevelop
    obtain ⟨a'', f'', shape, domain, predicate⟩ := par_rigid_two (by decide) argumentDevelop
    obtain ⟨functionShape, rfl⟩ := Tm.app.inj shape
    obtain ⟨_, rfl⟩ := Tm.app.inj functionShape
    change Par (proof (universalProposition a' f')) (develop (proof (universalProposition a f)))
    rw [develop_universal]
    exact par_universal domain predicate
  cases function with
  | lam body =>
      obtain ⟨body', rfl, _⟩ := par_lam functionStep
      obtain ⟨body'', shape, bodyDevelop⟩ := par_lam functionDevelop
      obtain rfl := Tm.lam.inj shape
      exact .betaPi bodyDevelop argumentDevelop
  | _ =>
      rw [develop_app_plain _ _ (fun body impossible => by cases impossible) implication universal]
      exact .app functionDevelop argumentDevelop

mutual

/-- Every parallel choice reaches the complete development of its source.
The algebraic cases use each original operand development, including the
predicate transported under the newly exposed dependent binder. -/
theorem par_develop {n : Nat} {source target : Tower.Tm n} :
    Par source target → Par target (develop source)
  | .var index => .var index
  | .const name => .const name
  | .head head => .head head
  | .headRel equality => .headRel (LevelTower.headEq_symmetric.symm _ _ equality)
  | .pi domain codomain => .pi (par_develop domain) (par_develop codomain)
  | .sigma domain codomain => .sigma (par_develop domain) (par_develop codomain)
  | .id carrier left right => .id (par_develop carrier) (par_develop left) (par_develop right)
  | .lam body => .lam (par_develop body)
  | .app function argument =>
      develop_application function argument (par_develop function) (par_develop argument)
  | .pair first second => .pair (par_develop first) (par_develop second)
  | @ParRed.fst _ _ _ _ pair pair' pairStep => by
      have pairDevelop := par_develop pairStep
      cases pair with
      | pair first second =>
          obtain ⟨first', second', rfl, _, _⟩ := par_pair pairStep
          obtain ⟨first'', second'', shape, firstDevelop, secondDevelop⟩ := par_pair pairDevelop
          obtain ⟨rfl, rfl⟩ := Tm.pair.inj shape
          exact .betaSigmaFst firstDevelop secondDevelop
      | _ => exact .fst pairDevelop
  | @ParRed.snd _ _ _ _ pair pair' pairStep => by
      have pairDevelop := par_develop pairStep
      cases pair with
      | pair first second =>
          obtain ⟨first', second', rfl, _, _⟩ := par_pair pairStep
          obtain ⟨first'', second'', shape, firstDevelop, secondDevelop⟩ := par_pair pairDevelop
          obtain ⟨rfl, rfl⟩ := Tm.pair.inj shape
          exact .betaSigmaSnd firstDevelop secondDevelop
      | _ => exact .snd pairDevelop
  | .refl term => .refl (par_develop term)
  | .betaPi body argument => par_inst0 (par_develop argument) (par_develop body)
  | .betaSigmaFst first _ => by simpa only [develop] using par_develop first
  | .betaSigmaSnd _ second => by simpa only [develop] using par_develop second
  | .algebraic schema sigma tau arguments => by
      have argumentDevelop := parSub_develop arguments
      cases schema with
      | implication =>
          change Par (implicationFamily (tau 0) (tau 1))
            (develop (proof (Source.rawImp (sigma 0) (sigma 1))))
          rw [develop_implication]
          exact .pi (.app (.const proofName) (argumentDevelop 0))
            (par_rename wk (.app (.const proofName) (argumentDevelop 1)))
      | universal =>
          change Par (universalFamily (tau 0) (tau 1))
            (develop (proof (universalProposition (sigma 0) (sigma 1))))
          rw [develop_universal]
          exact .pi (argumentDevelop 0)
            (.app (.const proofName) (.app (par_rename wk (argumentDevelop 1)) (.var 0)))

private theorem parSub_develop {arity n : Nat} {sigma tau : Sub Tower.Head arity n} :
    ParSub rules.headEq Schema sigma tau → ∀ index, Par (tau index) (develop (sigma index))
  | .nil, index => Fin.elim0 index
  | .cons head tail, index =>
      Fin.cases (par_develop head) (fun prior => parSub_develop tail prior) index

end

def completeDevelopment : CompleteDevelopment schemaPresentation where
  develop := develop
  reaches := par_develop

/-- This is Church--Rosser for the actual decoder conversion, not merely
for an observed or enlarged relation. -/
theorem churchRosser : ChurchRosser rules :=
  churchRosserOfCompleteDevelopment schemaPresentation completeDevelopment

theorem rootPiHeadNeutral : RootPiHeadNeutral rules where
  pi := by
    intro n domain codomain target step
    obtain ⟨arity, left, right, sigma, schema, shape, _⟩ := schema_cover step
    cases schema <;> cases shape
  head := by
    intro n head target step
    obtain ⟨arity, left, right, sigma, schema, shape, _⟩ := schema_cover step
    cases schema <;> cases shape

theorem piConversionBoundary : PiConversionBoundary rules :=
  piConversionBoundaryOfChurchRosser rootPiHeadNeutral churchRosser

private theorem step_sigma {n : Nat} {domain : Tower.Tm n} {codomain : Tower.Tm (n + 1)}
    {target : Tower.Tm n} (step : Step rules.headEq (.sigma domain codomain) target rules.computation) :
    ∃ domain' codomain', target = .sigma domain' codomain' ∧
      StepStar rules domain domain' ∧ StepStar rules codomain codomain' := by
  cases step with
  | root rootStep =>
      obtain ⟨arity, left, right, sigma, schema, shape, _⟩ := schema_cover rootStep
      cases schema <;> cases shape
  | congSigmaDom inner => exact ⟨_, _, rfl, .tail .refl inner, .refl⟩
  | congSigmaCod inner => exact ⟨_, _, rfl, .refl, .tail .refl inner⟩

theorem stepStar_sigma {n : Nat} {domain : Tower.Tm n} {codomain : Tower.Tm (n + 1)}
    {target : Tower.Tm n} (steps : StepStar rules (.sigma domain codomain) target) :
    ∃ domain' codomain', target = .sigma domain' codomain' ∧
      StepStar rules domain domain' ∧ StepStar rules codomain codomain' := by
  induction steps with
  | refl => exact ⟨_, _, rfl, .refl, .refl⟩
  | tail previous finalStep ih =>
      obtain ⟨middleDomain, middleCodomain, rfl, first, second⟩ := ih
      obtain ⟨lastDomain, lastCodomain, rfl, lastFirst, lastSecond⟩ := step_sigma finalStep
      exact ⟨_, _, rfl, first.trans lastFirst, second.trans lastSecond⟩

theorem sigmaConversionBoundary : SigmaConversionBoundary rules where
  components := by
    intro n domain domain' codomain codomain' conversion
    obtain ⟨common, firstPath, secondPath⟩ := churchRosser conversion
    obtain ⟨firstDomain, firstCodomain, firstShape, firstDomainPath, firstCodomainPath⟩ :=
      stepStar_sigma firstPath
    obtain ⟨secondDomain, secondCodomain, secondShape, secondDomainPath, secondCodomainPath⟩ :=
      stepStar_sigma secondPath
    obtain ⟨rfl, rfl⟩ := Tm.sigma.inj (firstShape.symm.trans secondShape)
    exact ⟨.trans _ _ _ (stepStar_implies_conv firstDomainPath)
        (.symm _ _ (stepStar_implies_conv secondDomainPath)),
      .trans _ _ _ (stepStar_implies_conv firstCodomainPath)
        (.symm _ _ (stepStar_implies_conv secondCodomainPath))⟩
  headDisjoint := FormationSensitiveHOLProofConversion.sigma_head_separated _ _ _

theorem pi_sigma_disjoint {n : Nat} (a c : Tower.Tm n) (b d : Tower.Tm (n + 1)) :
    ¬ Conv rules.headEq (.pi a b) (.sigma c d) rules.computation := by
  intro conversion
  obtain ⟨common, firstPath, secondPath⟩ := churchRosser conversion
  obtain ⟨a', b', firstShape, _, _⟩ := stepStar_pi_decomp rootPiHeadNeutral firstPath
  obtain ⟨c', d', secondShape, _, _⟩ := stepStar_sigma secondPath
  rw [firstShape] at secondShape
  cases secondShape

/-- A concrete overlapping peak: decoding the implication first and beta
reducing its first operand first both reach the same displayed family. -/
theorem beta_decoder_peak {n : Nat} (p q : Tower.Tm n) :
    let betaOperand := Tm.app (.lam (.var 0)) p
    let source := proof (Source.rawImp betaOperand q)
    Step rules.headEq source (implicationFamily betaOperand q) rules.computation ∧
    Step rules.headEq source (proof (Source.rawImp p q)) rules.computation ∧
    StepStar rules (implicationFamily betaOperand q) (implicationFamily p q) ∧
    StepStar rules (proof (Source.rawImp p q)) (implicationFamily p q) := by
  dsimp only
  have beta : Step rules.headEq (.app (.lam (.var 0)) p) p rules.computation := by
    simpa only [inst0, subst, subst0, consSub, Fin.cases_zero] using
      (Step.betaPi (headEq := rules.headEq) (root := rules.computation) (.var 0) p)
  exact ⟨.root (.declared (.implication _ _)),
    .congAppArg (.congAppFun (.congAppArg beta)),
    .tail .refl (.congPiDom (.congAppArg beta)),
    .tail .refl (.root (.declared (.implication _ _)))⟩

namespace Preservation

open FormationSensitive

theorem universes : UniverseRegularity rules := towerUniverseRegularity.includeSignature declarations

theorem proofSpine {n : Nat} (gamma : Tower.Ctx n) :
    DeclarationSpine rules gamma (.const proofName)
      (.pi (.const `HOLUniformList.prop) (sortTm Tower.zero)) := by
  have spine : DeclarationSpine rules gamma (.const proofName) (liftClosed proofType) :=
    .constant (by decide) proofType_formed (.sort (.max Tower.zero (.succ Tower.zero)))
  simpa only [proofType, liftClosed, sortTm, rename] using spine

/-- The outer decoder declaration recovers a real proposition argument and
replays the caller's actual type adjustments on any small replacement type. -/
theorem proofArgument {n : Nat} {gamma : Tower.Ctx n} {p displayed : Tower.Tm n}
    (formed : ContextFormation rules gamma) (observed : Typing rules gamma (proof p) displayed) :
    Typing rules gamma p (.const `HOLUniformList.prop) ∧
      (∀ {replacement}, Typing rules gamma replacement (sortTm Tower.zero) →
        Typing rules gamma replacement displayed) := by
  obtain ⟨typed, _, _, replay⟩ :=
    (proofSpine gamma).recoverApplication universes piConversionBoundary formed observed
  exact ⟨typed, replay⟩

theorem implicationSpine {n : Nat} (gamma : Tower.Ctx n) :
    DeclarationSpine rules gamma (.const `HOLUniformList.implication)
      (.pi (.const `HOLUniformList.prop)
        (.pi (.const `HOLUniformList.prop) (.const `HOLUniformList.prop))) := by
  have declared : Typing rules .nil
      (.pi (.const `HOLUniformList.prop)
        (.pi (.const `HOLUniformList.prop) (.const `HOLUniformList.prop))) (sortTm Tower.zero) :=
    pi_zero (proposition_formed _) (pi_zero (proposition_formed _) (proposition_formed _))
  have spine := DeclarationSpine.constant (R := rules) (Γ := gamma)
    (name := `HOLUniformList.implication) (by decide) declared (.sort Tower.zero)
  simpa only [liftClosed, rename] using spine

theorem implicationArguments {n : Nat} {gamma : Tower.Ctx n} {p q : Tower.Tm n}
    (formed : ContextFormation rules gamma)
    (observed : Typing rules gamma (Source.rawImp p q) (.const `HOLUniformList.prop)) :
    Typing rules gamma p (.const `HOLUniformList.prop) ∧
      Typing rules gamma q (.const `HOLUniformList.prop) := by
  obtain ⟨_, _, firstTyping, _, _, _⟩ := observed.appGeneration
  obtain ⟨pTyped, firstSpine, _, _⟩ :=
    (implicationSpine gamma).recoverApplication universes piConversionBoundary formed firstTyping
  have opened : DeclarationSpine rules gamma (.app (.const `HOLUniformList.implication) p)
      (.pi (.const `HOLUniformList.prop) (.const `HOLUniformList.prop)) := firstSpine
  exact ⟨pTyped, (opened.recoverApplication universes piConversionBoundary formed observed).1⟩

theorem universalSpine {n : Nat} (gamma : Tower.Ctx n) :
    DeclarationSpine rules gamma (.const `HOLUniformList.universal)
      (.pi (sortTm Tower.zero)
        (.pi (.pi (.var 0) (.const `HOLUniformList.prop)) (.const `HOLUniformList.prop))) := by
  have spine : DeclarationSpine rules gamma (.const `HOLUniformList.universal)
      (liftClosed FormationSensitiveHOLUniformList.universalType) :=
    .constant (by decide) (include_typed FormationSensitiveHOLUniformList.universal_type_formed)
      (.sort (.max (.succ Tower.zero) Tower.zero))
  simpa only [FormationSensitiveHOLUniformList.universalType, liftClosed, sortTm, rename, liftRen,
    Fin.cases_zero] using spine

theorem universalArguments {n : Nat} {gamma : Tower.Ctx n} {a f : Tower.Tm n}
    (formed : ContextFormation rules gamma)
    (observed : Typing rules gamma (universalProposition a f) (.const `HOLUniformList.prop)) :
    Typing rules gamma a (sortTm Tower.zero) ∧
      Typing rules gamma f (.pi a (.const `HOLUniformList.prop)) := by
  obtain ⟨_, _, firstTyping, _, _, _⟩ := observed.appGeneration
  obtain ⟨aTyped, firstSpine, _, _⟩ :=
    (universalSpine gamma).recoverApplication universes piConversionBoundary formed firstTyping
  have opened : DeclarationSpine rules gamma (.app (.const `HOLUniformList.universal) a)
      (.pi (.pi a (.const `HOLUniformList.prop)) (.const `HOLUniformList.prop)) := by
    simpa only [inst0, subst, liftSub, subst0, consSub, Fin.cases_zero] using firstSpine
  exact ⟨aTyped, (opened.recoverApplication universes piConversionBoundary formed observed).1⟩

/-- Each exact decoder contraction preserves any displayed type obtained
from its source, not merely the canonical universe type of the example. -/
theorem rootPreservation : RootPreservation rules := by
  intro n gamma source target displayed formed observed root
  cases root with
  | inherited impossible => cases impossible
  | delta lookup =>
      rw [FormationSensitiveHOLProofConversion.declarations_opaque] at lookup
      cases lookup
  | declared decoder =>
      cases decoder with
      | implication p q =>
          obtain ⟨proposition, replay⟩ := proofArgument formed observed
          obtain ⟨hp, hq⟩ := implicationArguments formed proposition
          exact replay (implication_formed hp hq)
      | universal a f =>
          obtain ⟨proposition, replay⟩ := proofArgument formed observed
          obtain ⟨ha, hf⟩ := universalArguments formed proposition
          exact replay (universal_formed ha hf)

/-- Full contextual subject reduction, including computations in dependent
binder types and beneath the proof decoder. -/
theorem step_preserves {n : Nat} {gamma : Tower.Ctx n} {source target displayed : Tower.Tm n}
    (judgment : Judgment rules gamma source displayed)
    (step : Step rules.headEq source target rules.computation) :
    Judgment rules gamma target displayed :=
  judgment.step_preserves universes piConversionBoundary sigmaConversionBoundary
    (towerHeadPreservation.includeSignature declarations) rootPreservation step

theorem steps_preserve {n : Nat} {gamma : Tower.Ctx n} {source target displayed : Tower.Tm n}
    (judgment : Judgment rules gamma source displayed) (steps : StepStar rules source target) :
    Judgment rules gamma target displayed :=
  judgment.steps_preserve universes piConversionBoundary sigmaConversionBoundary
    (towerHeadPreservation.includeSignature declarations) rootPreservation steps

end Preservation

#print axioms schema_sound
#print axioms schema_cover
#print axioms schema_left_linear
#print axioms par_rigid_two
#print axioms par_develop
#print axioms churchRosser
#print axioms piConversionBoundary
#print axioms sigmaConversionBoundary
#print axioms pi_sigma_disjoint
#print axioms beta_decoder_peak
#print axioms Preservation.rootPreservation
#print axioms Preservation.step_preserves
#print axioms Preservation.steps_preserve

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.FormationSensitiveHOLProofConfluence
