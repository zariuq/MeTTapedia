import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLNativeGenericProofCompilerTyping
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLNativeGenericProofCompilerSubstitution
import Mettapedia.Logic.HOL.ProofSyntaxModulo

/-!
# Compiling proofs modulo definitional conversion

A source checker that retypes a proof along definitional conversion emits no
proof term for the retyping: the native term is the same, and its type moves
by native conversion.  This module makes that step precise for the generic
HOL proof compiler.

The represented defining equations must be native root computation
(`EquationRealization`).  Under that condition every core definitional step is
one native step and every conversion article is a native conversion, so a
compiled proof retypes by `Typing.conv` at the proof family of the converted
conclusion.  The logical rules compile exactly as `compile` compiles them, on
every proof of the shared fragment and for every operation algebra.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLNativeGenericProofCompiler

open Presentation Mettapedia.Logic FormationSensitiveHOLInterface
open Presentation.FormationSensitive

universe u v

variable {Base : Type u} {Const : HOL.Ty Base → Type v}

/-- Source conversion moves along the source inclusion into every target. -/
theorem Operations.includeSourceConversion
    {signature : LogicalSignature Base Const} {proofName : DeclName}
    (operations : Operations signature proofName)
    {n : Nat} {left right : Tower.Tm n}
    (conversion : Conv signature.rules.headEq left right signature.rules.computation) :
    Conv operations.target.headEq left right operations.target.computation := by
  have mapped := conversion.mapHead (fun head => head)
    operations.sourceMorphism.headEq operations.sourceMorphism.computation
  simpa only [Tm.mapHead_id] using mapped

namespace Modulo

/-! ## Core terms are represented -/

theorem represent_isCore (signature : LogicalSignature Base Const) :
    ∀ {gamma : HOL.Ctx Base} {type : HOL.Ty Base} (term : HOL.Term Const gamma type),
      term.isCore = true → ∃ code, represent signature term = some code
  | _, _, .var _, _ => ⟨_, rfl⟩
  | _, _, .const _, _ => ⟨_, rfl⟩
  | _, _, .app function argument, core => by
      simp only [HOL.Term.isCore, Bool.and_eq_true] at core
      obtain ⟨_, functionCode⟩ := represent_isCore signature function core.1
      obtain ⟨_, argumentCode⟩ := represent_isCore signature argument core.2
      exact ⟨_, represent_app signature function argument functionCode argumentCode⟩
  | _, _, .lam body, core => by
      simp only [HOL.Term.isCore] at core
      obtain ⟨_, bodyCode⟩ := represent_isCore signature body core
      exact ⟨_, represent_lam signature body bodyCode⟩
  | _, _, .imp left right, core => by
      simp only [HOL.Term.isCore, Bool.and_eq_true] at core
      obtain ⟨_, leftCode⟩ := represent_isCore signature left core.1
      obtain ⟨_, rightCode⟩ := represent_isCore signature right core.2
      exact ⟨_, by rw [FormationSensitiveHOLInterface.represent_imp, leftCode, rightCode]; rfl⟩
  | _, _, .eq left right, core => by
      simp only [HOL.Term.isCore, Bool.and_eq_true] at core
      obtain ⟨_, leftCode⟩ := represent_isCore signature left core.1
      obtain ⟨_, rightCode⟩ := represent_isCore signature right core.2
      exact ⟨_, represent_eq signature left right leftCode rightCode⟩
  | _, _, .all body, core => by
      simp only [HOL.Term.isCore] at core
      obtain ⟨_, bodyCode⟩ := represent_isCore signature body core
      exact ⟨_, by rw [FormationSensitiveHOLInterface.represent_all, bodyCode]; rfl⟩
  | _, _, .top, core | _, _, .bot, core | _, _, .and _ _, core | _, _, .or _ _, core
  | _, _, .not _, core | _, _, .ex _, core => by simp [HOL.Term.isCore] at core

/-! ## Native substitutions from source substitutions -/

/-- The variable at a position of a source telescope. -/
def varAt : (gamma : HOL.Ctx Base) → Fin gamma.length → Σ type : HOL.Ty Base, HOL.Var gamma type
  | [], index => index.elim0
  | type :: gamma, index =>
      Fin.cases ⟨type, .vz⟩ (fun prior => ⟨(varAt gamma prior).1, .vs (varAt gamma prior).2⟩) index

theorem varAt_variableIndex :
    ∀ {gamma : HOL.Ctx Base} {type : HOL.Ty Base} (index : HOL.Var gamma type),
      varAt gamma (variableIndex index) = ⟨type, index⟩
  | _, _, .vz => rfl
  | _, _, .vs prior => by
      simp only [variableIndex, varAt, Fin.cases_succ]
      rw [varAt_variableIndex prior]

/-- Represent each image of a source substitution; the fallback is used only
at images without a representation. -/
def nativeSubstitution (signature : LogicalSignature Base Const)
    {theta gamma : HOL.Ctx Base} (substitution : HOL.Subst Const theta gamma) :
    Sub Tower.Head theta.length gamma.length :=
  fun index => (represent signature (substitution (varAt theta index).2)).getD
    (.head .legacyGround)

theorem nativeSubstitution_compatible (signature : LogicalSignature Base Const)
    {theta gamma : HOL.Ctx Base} (substitution : HOL.Subst Const theta gamma)
    (core : ∀ {type : HOL.Ty Base} (index : HOL.Var theta type),
      (substitution index).isCore = true)
    {type : HOL.Ty Base} (index : HOL.Var theta type) :
    represent signature (substitution index) =
      some (nativeSubstitution signature substitution (variableIndex index)) := by
  obtain ⟨code, represented⟩ := represent_isCore signature _ (core index)
  have atIndex : represent signature (substitution (varAt theta (variableIndex index)).2) =
      represent signature (substitution index) :=
    congrArg (fun entry : Σ type : HOL.Ty Base, HOL.Var theta type =>
      represent signature (substitution entry.2)) (varAt_variableIndex index)
  simp only [nativeSubstitution, atIndex, represented, Option.getD_some]

/-! ## Native realization of the defining equations -/

/-- Every listed equation is represented on both sides, and each substitution
instance of the represented equation is a native root step. -/
def EquationRealization (signature : LogicalSignature Base Const)
    (equations : List (HOL.DefiningEquation Const)) : Prop :=
  ∀ equation ∈ equations, ∃ left right,
    represent signature equation.left = some left ∧
    represent signature equation.right = some right ∧
    ∀ {n : Nat} (substitution : Sub Tower.Head equation.context.length n),
      signature.rules.computation.step (subst substitution left) (subst substitution right)

/-- A map carrying one relation into another carries their reflexive closures. -/
theorem reflGen_map {α β : Type*} {r : α → α → Prop} {s : β → β → Prop} (f : α → β)
    (carry : ∀ {a b : α}, r a b → s (f a) (f b)) :
    ∀ {a b : α}, Relation.ReflGen r a b → Relation.ReflGen s (f a) (f b)
  | _, _, .refl => .refl
  | _, _, .single related => .single (carry related)

/-- A core definitional step between represented terms is one native step. -/
theorem sourceStep_native (signature : LogicalSignature Base Const)
    {equations : List (HOL.DefiningEquation Const)}
    (realization : EquationRealization signature equations)
    {gamma : HOL.Ctx Base} {type : HOL.Ty Base} {left right : HOL.Term Const gamma type}
    (step : HOL.SourceStep equations left right) :
    left.isCore = true → right.isCore = true →
      ∀ {leftCode rightCode : Tower.Tm gamma.length},
        represent signature left = some leftCode →
        represent signature right = some rightCode →
        Step signature.rules.headEq leftCode rightCode signature.rules.computation := by
  induction step with
  | beta body argument =>
      intro leftCore _ leftCode rightCode leftRepresented rightRepresented
      simp only [HOL.Term.isCore, Bool.and_eq_true] at leftCore
      obtain ⟨bodyCode, bodyRepresented⟩ := represent_isCore signature body leftCore.1
      obtain ⟨argumentCode, argumentRepresented⟩ :=
        represent_isCore signature argument leftCore.2
      rw [represent_app signature _ argument (represent_lam signature body bodyRepresented)
        argumentRepresented] at leftRepresented
      rw [represent_instantiate signature argument body argumentRepresented,
        bodyRepresented] at rightRepresented
      cases leftRepresented
      cases rightRepresented
      exact Step.betaPi bodyCode argumentCode
  | delta equation listed substitution core =>
      intro _ _ leftCode rightCode leftRepresented rightRepresented
      obtain ⟨equationLeft, equationRight, hl, hr, roots⟩ := realization equation listed
      rw [represent_subst signature substitution (nativeSubstitution signature substitution)
        (nativeSubstitution_compatible signature substitution core), hl] at leftRepresented
      rw [represent_subst signature substitution (nativeSubstitution signature substitution)
        (nativeSubstitution_compatible signature substitution core), hr] at rightRepresented
      cases leftRepresented
      cases rightRepresented
      exact Step.root (roots _)
  | appFun argument _ ih =>
      intro leftCore rightCore leftCode rightCode leftRepresented rightRepresented
      simp only [HOL.Term.isCore, Bool.and_eq_true] at leftCore rightCore
      obtain ⟨functionCode, hf⟩ := represent_isCore signature _ leftCore.1
      obtain ⟨functionCode', hf'⟩ := represent_isCore signature _ rightCore.1
      obtain ⟨argumentCode, ha⟩ := represent_isCore signature argument leftCore.2
      rw [represent_app signature _ argument hf ha] at leftRepresented
      rw [represent_app signature _ argument hf' ha] at rightRepresented
      cases leftRepresented
      cases rightRepresented
      exact Step.congAppFun (ih leftCore.1 rightCore.1 hf hf')
  | appArg function _ ih =>
      intro leftCore rightCore leftCode rightCode leftRepresented rightRepresented
      simp only [HOL.Term.isCore, Bool.and_eq_true] at leftCore rightCore
      obtain ⟨functionCode, hf⟩ := represent_isCore signature function leftCore.1
      obtain ⟨argumentCode, ha⟩ := represent_isCore signature _ leftCore.2
      obtain ⟨argumentCode', ha'⟩ := represent_isCore signature _ rightCore.2
      rw [represent_app signature function _ hf ha] at leftRepresented
      rw [represent_app signature function _ hf ha'] at rightRepresented
      cases leftRepresented
      cases rightRepresented
      exact Step.congAppArg (ih leftCore.2 rightCore.2 ha ha')
  | lam _ ih =>
      intro leftCore rightCore leftCode rightCode leftRepresented rightRepresented
      simp only [HOL.Term.isCore] at leftCore rightCore
      obtain ⟨bodyCode, hb⟩ := represent_isCore signature _ leftCore
      obtain ⟨bodyCode', hb'⟩ := represent_isCore signature _ rightCore
      rw [represent_lam signature _ hb] at leftRepresented
      rw [represent_lam signature _ hb'] at rightRepresented
      cases leftRepresented
      cases rightRepresented
      exact Step.congLam (ih leftCore rightCore hb hb')
  | impLeft right _ ih =>
      intro leftCore rightCore leftCode rightCode leftRepresented rightRepresented
      simp only [HOL.Term.isCore, Bool.and_eq_true] at leftCore rightCore
      obtain ⟨code, hl⟩ := represent_isCore signature _ leftCore.1
      obtain ⟨code', hl'⟩ := represent_isCore signature _ rightCore.1
      obtain ⟨rightCode', hr⟩ := represent_isCore signature right leftCore.2
      rw [FormationSensitiveHOLInterface.represent_imp, hl, hr] at leftRepresented
      rw [FormationSensitiveHOLInterface.represent_imp, hl', hr] at rightRepresented
      cases leftRepresented
      cases rightRepresented
      exact Step.congAppFun (Step.congAppArg (ih leftCore.1 rightCore.1 hl hl'))
  | impRight left _ ih =>
      intro leftCore rightCore leftCode rightCode leftRepresented rightRepresented
      simp only [HOL.Term.isCore, Bool.and_eq_true] at leftCore rightCore
      obtain ⟨leftCode', hl⟩ := represent_isCore signature left leftCore.1
      obtain ⟨code, hr⟩ := represent_isCore signature _ leftCore.2
      obtain ⟨code', hr'⟩ := represent_isCore signature _ rightCore.2
      rw [FormationSensitiveHOLInterface.represent_imp, hl, hr] at leftRepresented
      rw [FormationSensitiveHOLInterface.represent_imp, hl, hr'] at rightRepresented
      cases leftRepresented
      cases rightRepresented
      exact Step.congAppArg (ih leftCore.2 rightCore.2 hr hr')
  | eqLeft right _ ih =>
      intro leftCore rightCore leftCode rightCode leftRepresented rightRepresented
      simp only [HOL.Term.isCore, Bool.and_eq_true] at leftCore rightCore
      obtain ⟨code, hl⟩ := represent_isCore signature _ leftCore.1
      obtain ⟨code', hl'⟩ := represent_isCore signature _ rightCore.1
      obtain ⟨rightCode', hr⟩ := represent_isCore signature right leftCore.2
      rw [represent_eq signature _ right hl hr] at leftRepresented
      rw [represent_eq signature _ right hl' hr] at rightRepresented
      cases leftRepresented
      cases rightRepresented
      exact Step.congAppFun (Step.congAppArg (ih leftCore.1 rightCore.1 hl hl'))
  | eqRight left _ ih =>
      intro leftCore rightCore leftCode rightCode leftRepresented rightRepresented
      simp only [HOL.Term.isCore, Bool.and_eq_true] at leftCore rightCore
      obtain ⟨leftCode', hl⟩ := represent_isCore signature left leftCore.1
      obtain ⟨code, hr⟩ := represent_isCore signature _ leftCore.2
      obtain ⟨code', hr'⟩ := represent_isCore signature _ rightCore.2
      rw [represent_eq signature left _ hl hr] at leftRepresented
      rw [represent_eq signature left _ hl hr'] at rightRepresented
      cases leftRepresented
      cases rightRepresented
      exact Step.congAppArg (ih leftCore.2 rightCore.2 hr hr')
  | all _ ih =>
      intro leftCore rightCore leftCode rightCode leftRepresented rightRepresented
      simp only [HOL.Term.isCore] at leftCore rightCore
      obtain ⟨bodyCode, hb⟩ := represent_isCore signature _ leftCore
      obtain ⟨bodyCode', hb'⟩ := represent_isCore signature _ rightCore
      rw [FormationSensitiveHOLInterface.represent_all, hb] at leftRepresented
      rw [FormationSensitiveHOLInterface.represent_all, hb'] at rightRepresented
      cases leftRepresented
      cases rightRepresented
      exact Step.congAppArg (Step.congLam (ih leftCore rightCore hb hb'))

/-- A conversion article between represented terms is native conversion. -/
theorem coreConversion_native (signature : LogicalSignature Base Const)
    {equations : List (HOL.DefiningEquation Const)}
    (realization : EquationRealization signature equations)
    {gamma : HOL.Ctx Base} {type : HOL.Ty Base} {left right : HOL.Term Const gamma type}
    (conversion : HOL.CoreConversion equations left right) :
    ∀ {leftCode rightCode : Tower.Tm gamma.length},
      represent signature left = some leftCode →
      represent signature right = some rightCode →
      Conv signature.rules.headEq leftCode rightCode signature.rules.computation := by
  induction conversion with
  | rel _ _ step =>
      intro leftCode rightCode hl hr
      exact .rel _ _ (sourceStep_native signature realization step.2.2 step.1 step.2.1 hl hr)
  | refl =>
      intro leftCode rightCode hl hr
      rw [hl] at hr
      cases hr
      exact .refl _
  | symm _ _ _ ih =>
      intro leftCode rightCode hl hr
      exact .symm _ _ (ih hr hl)
  | @trans first middle last firstMiddle middleLast ihFirst ihLast =>
      intro leftCode rightCode hl hr
      rcases HOL.CoreConversion.eq_or_core firstMiddle with same | ⟨_, middleCore⟩
      · subst same
        exact ihLast hl hr
      · obtain ⟨middleCode, hm⟩ := represent_isCore signature middle middleCore
        exact .trans _ _ _ (ihFirst hl hm) (ihLast hm hr)

/-! ## The compiler for proofs modulo -/

/-- The logical cases are those of `compile`; a retyping step emits no term. -/
def compileModulo (signature : LogicalSignature Base Const)
    {equations : List (HOL.DefiningEquation Const)}
    {gamma : HOL.Ctx Base} {delta : List (HOL.Formula Const gamma)}
    {phi : HOL.Formula Const gamma} (source : HOL.ProofSyntaxModulo equations delta phi)
    {n : Nat} (objects : Sub Tower.Head gamma.length n)
    (hypotheses : Fin delta.length → Tower.Tm n) : Option (Tower.Tm n) :=
  match source with
  | .hyp occurrence => some (hypotheses occurrence)
  | @HOL.ProofSyntaxModulo.impI _ _ _ gamma delta premise _ body => do
      let _ ← represent signature premise
      let nativeBody ← compileModulo signature body
        (fun i => rename wk (objects i))
        (Fin.cases (.var 0) (fun i => rename wk (hypotheses i)))
      pure (.lam nativeBody)
  | .impE function argument => do
      let nativeFunction ← compileModulo signature function objects hypotheses
      let nativeArgument ← compileModulo signature argument objects hypotheses
      pure (.app nativeFunction nativeArgument)
  | .allI body => do
      let nativeBody ← compileModulo signature body (liftSub objects)
        (fun i => rename wk (hypotheses (i.cast (by simp [HOL.weakenHyps]))))
      pure (.lam nativeBody)
  | .allE term function => do
      let nativeArgument ← represent signature term
      let nativeFunction ← compileModulo signature function objects hypotheses
      pure (.app nativeFunction (subst objects nativeArgument))
  | .convert _ proof => compileModulo signature proof objects hypotheses

/-- On the shared logical fragment the two compilers produce the same term
(or both reject), whatever operation algebra `compile` receives. -/
theorem compileModulo_ofProofSyntax? (signature : LogicalSignature Base Const)
    (proofName : DeclName) (operations : Operations signature proofName)
    {equations : List (HOL.DefiningEquation Const)}
    {gamma : HOL.Ctx Base} {delta : List (HOL.Formula Const gamma)}
    {phi : HOL.Formula Const gamma} (source : HOL.ProofSyntax Const delta phi)
    {embedded : HOL.ProofSyntaxModulo equations delta phi}
    (success : HOL.ProofSyntaxModulo.ofProofSyntax? source = some embedded)
    {n : Nat} (objects : Sub Tower.Head gamma.length n)
    (hypotheses : Fin delta.length → Tower.Tm n) :
    compileModulo signature embedded objects hypotheses =
      compile signature proofName operations source objects hypotheses := by
  induction source generalizing n with
  | hyp occurrence =>
      simp only [HOL.ProofSyntaxModulo.ofProofSyntax?, Option.some.injEq] at success
      subst embedded
      rfl
  | impI body ih =>
      simp only [HOL.ProofSyntaxModulo.ofProofSyntax?] at success
      obtain ⟨body', hb, rfl⟩ := Option.map_eq_some_iff.mp success
      simp only [compileModulo, compile, ih hb]
  | impE function argument ihFunction ihArgument =>
      cases hf : HOL.ProofSyntaxModulo.ofProofSyntax? (equations := equations) function <;>
        cases ha : HOL.ProofSyntaxModulo.ofProofSyntax? (equations := equations) argument <;>
          simp [HOL.ProofSyntaxModulo.ofProofSyntax?, hf, ha] at success
      subst embedded
      simp only [compileModulo, compile, ihFunction hf, ihArgument ha]
  | allI body ih =>
      simp only [HOL.ProofSyntaxModulo.ofProofSyntax?] at success
      obtain ⟨body', hb, rfl⟩ := Option.map_eq_some_iff.mp success
      simp only [compileModulo, compile, ih hb]
  | allE term function ih =>
      simp only [HOL.ProofSyntaxModulo.ofProofSyntax?] at success
      obtain ⟨function', hf, rfl⟩ := Option.map_eq_some_iff.mp success
      simp only [compileModulo, compile, ih hf]
  | _ => simp [HOL.ProofSyntaxModulo.ofProofSyntax?] at success

/-- Every successful compilation is typed at the proof family of the
represented conclusion, in the target of any operation algebra, whenever the
source equations are realized by native computation. -/
theorem compileModulo_typed (signature : LogicalSignature Base Const)
    (proofName : DeclName) (operations : Operations signature proofName)
    {equations : List (HOL.DefiningEquation Const)}
    (realization : EquationRealization signature equations)
    {gamma : HOL.Ctx Base} {delta : List (HOL.Formula Const gamma)}
    {phi : HOL.Formula Const gamma} (source : HOL.ProofSyntaxModulo equations delta phi)
    {n : Nat} {target : Tower.Ctx n}
    {objects : Sub Tower.Head gamma.length n}
    {hypotheses : Fin delta.length → Tower.Tm n} {native : Tower.Tm n}
    (objectTyped : GenericTyping.Objects signature target objects)
    (hypothesisTyped : GenericTyping.Hypotheses signature operations target objects hypotheses)
    (success : compileModulo signature source objects hypotheses = some native) :
    ∃ code, represent signature phi = some code ∧
      Typing operations.target target native
        (FormationSensitiveHOLGenericProofFamily.proof proofName (subst objects code)) := by
  open FormationSensitiveHOLGenericProofFamily GenericTyping in
  induction source generalizing n with
  | hyp occurrence =>
      simp only [compileModulo, Option.some.injEq] at success
      subst native
      exact hypothesisTyped occurrence
  | @impI gamma delta left right body ih =>
      cases hl : represent signature left with
      | none => simp [compileModulo, hl] at success
      | some leftCode =>
          cases hb : compileModulo signature body
              (fun i => rename wk (objects i))
              (Fin.cases (.var 0) (fun i => rename wk (hypotheses i))) with
          | none => simp [compileModulo, hl, hb] at success
          | some compiledBody =>
              simp [compileModulo, hl, hb] at success
              subst native
              obtain ⟨rightCode, hr, bodyTyped⟩ := ih
                (objectTyped.weaken signature (proof proofName (subst objects leftCode)))
                (hypothesisTyped.prepend signature hl) hb
              refine ⟨rawImp signature leftCode rightCode,
                by simp [FormationSensitiveHOLGenericProofFamily.represent_imp, hl, hr], ?_⟩
              simpa only [rawImp_subst] using
                operations.implicationIntro
                  (represented_typed signature operations hl objectTyped)
                  (represented_typed signature operations hr objectTyped)
                  (by simpa only [proof_rename, rename_subst] using bodyTyped)
  | @impE gamma delta left right function argument ihFunction ihArgument =>
      cases hf : compileModulo signature function objects hypotheses with
      | none => simp [compileModulo, hf] at success
      | some compiledFunction =>
          cases ha : compileModulo signature argument objects hypotheses with
          | none => simp [compileModulo, hf, ha] at success
          | some compiledArgument =>
              simp [compileModulo, hf, ha] at success
              subst native
              obtain ⟨functionCode, functionRepresented, functionTyped⟩ :=
                ihFunction objectTyped hypothesisTyped hf
              obtain ⟨leftCode, hl, argumentTyped⟩ :=
                ihArgument objectTyped hypothesisTyped ha
              cases hr : represent signature right with
              | none =>
                  simp [FormationSensitiveHOLGenericProofFamily.represent_imp,
                    hl, hr] at functionRepresented
              | some rightCode =>
                  have shape : functionCode = rawImp signature leftCode rightCode :=
                    represented_implication signature hl hr functionRepresented
                  subst functionCode
                  refine ⟨rightCode, rfl, ?_⟩
                  have majorTyped : Typing operations.target target compiledFunction
                      (proof proofName (rawImp signature
                        (subst objects leftCode) (subst objects rightCode))) := by
                    simpa only [rawImp_subst] using functionTyped
                  exact operations.implicationElim
                    (represented_typed signature operations hl objectTyped)
                    (represented_typed signature operations hr objectTyped)
                    majorTyped argumentTyped
  | @allI gamma delta type proposition body ih =>
      cases hb : compileModulo signature body (liftSub objects)
          (fun i => rename wk
            (hypotheses (i.cast (by simp [HOL.weakenHyps])))) with
      | none => simp [compileModulo, hb] at success
      | some compiledBody =>
          simp [compileModulo, hb] at success
          subst native
          obtain ⟨propositionCode, hp, bodyTyped⟩ := ih
            (objectTyped.lift signature type)
            (hypothesisTyped.lift signature type) hb
          refine ⟨universalProposition signature type (.lam propositionCode),
            by rw [FormationSensitiveHOLGenericProofFamily.represent_all signature, hp]; rfl, ?_⟩
          have introduced := operations.universalIntro
            (FormationSensitiveHOLInterface.typeAt_formed signature type target)
            (represented_typed signature operations hp
              (objectTyped.lift signature type)) bodyTyped
          simpa only [universalProposition_subst, Presentation.subst,
            typeAt_subst] using introduced
  | @allE gamma delta type proposition term function ih =>
      cases ht : represent signature term with
      | none => simp [compileModulo, ht] at success
      | some termCode =>
          cases hf : compileModulo signature function objects hypotheses with
          | none => simp [compileModulo, ht, hf] at success
          | some compiledFunction =>
              simp [compileModulo, ht, hf] at success
              subst native
              obtain ⟨functionCode, functionRepresented, functionTyped⟩ :=
                ih objectTyped hypothesisTyped hf
              cases hp : represent signature proposition with
              | none =>
                  simp [FormationSensitiveHOLGenericProofFamily.represent_all signature,
                    hp] at functionRepresented
              | some propositionCode =>
                  have shape : functionCode =
                      universalProposition signature type (.lam propositionCode) := by
                    simpa [FormationSensitiveHOLGenericProofFamily.represent_all signature,
                      hp, eq_comm] using functionRepresented
                  subst functionCode
                  refine ⟨inst0 termCode propositionCode,
                    by rw [FormationSensitiveHOLInterface.represent_instantiate signature
                      term proposition ht, hp]; rfl, ?_⟩
                  have majorTyped : Typing operations.target target compiledFunction
                      (proof proofName
                        (universalProposition signature type
                          (.lam (subst (liftSub objects) propositionCode)))) := by
                    simpa only [universalProposition_subst, Presentation.subst,
                      typeAt_subst] using functionTyped
                  have eliminated := operations.universalElim
                    (FormationSensitiveHOLInterface.typeAt_formed signature type target)
                    (represented_typed signature operations hp
                      (objectTyped.lift signature type))
                    majorTyped
                    (represented_typed signature operations ht objectTyped)
                  simpa only [subst_inst0] using eliminated
  | @convert gamma delta left right article inner ih =>
      simp only [compileModulo] at success
      obtain ⟨code, hl, typed⟩ := ih objectTyped hypothesisTyped success
      rcases HOL.CoreConversion.eq_or_core article with same | ⟨_, rightCore⟩
      · subst same
        exact ⟨code, hl, typed⟩
      · obtain ⟨rightCode, hr⟩ := represent_isCore signature right rightCore
        refine ⟨rightCode, hr, ?_⟩
        have conversion := (coreConversion_native signature realization article hl hr).substitute
          objects
        have moved : Conv operations.target.headEq
            (proof proofName (subst objects code)) (proof proofName (subst objects rightCode))
            operations.target.computation :=
          Conv.congApp (.refl _) (operations.includeSourceConversion conversion)
        exact Typing.conv typed
          (operations.includeProofTyping
            (proof_formed signature proofName operations.fresh
              (include_typed signature proofName
                (represented_typed signature operations hr objectTyped))))
          operations.zeroUniverse moved

/-- Compiling after a native substitution of the environment, or substituting
the compiled term: both routes agree, including rejection. -/
theorem compileModulo_substitute (signature : LogicalSignature Base Const)
    {equations : List (HOL.DefiningEquation Const)}
    {gamma : HOL.Ctx Base} {delta : List (HOL.Formula Const gamma)}
    {phi : HOL.Formula Const gamma} (source : HOL.ProofSyntaxModulo equations delta phi)
    {n m : Nat} (objects : Sub Tower.Head gamma.length n)
    (hypotheses : Fin delta.length → Tower.Tm n) (sigma : Sub Tower.Head n m) :
    compileModulo signature source (fun i => subst sigma (objects i))
        (fun i => subst sigma (hypotheses i)) =
      (compileModulo signature source objects hypotheses).map (subst sigma) := by
  induction source generalizing n m with
  | hyp occurrence => rfl
  | @impI gamma delta p q body ih =>
      have obj : (fun i => rename wk (subst sigma (objects i))) =
          (fun i => subst (liftSub sigma) (rename wk (objects i))) := by
        funext i
        simp only [subst_liftSub_wk]
      have hyp : Fin.cases (.var 0) (fun i => rename wk (subst sigma (hypotheses i))) =
          (fun i => subst (liftSub sigma)
            (Fin.cases (.var 0) (fun j => rename wk (hypotheses j)) i)) := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp [liftSub]
      simp only [compileModulo, obj, hyp]
      erw [ih (fun i => rename wk (objects i))
        (Fin.cases (.var 0) (fun i => rename wk (hypotheses i))) (liftSub sigma)]
      cases represent signature p <;>
        cases compileModulo signature body (fun i => rename wk (objects i))
          (Fin.cases (.var 0) (fun i => rename wk (hypotheses i))) <;> rfl
  | impE function argument ihf iha =>
      simp only [compileModulo, ihf, iha]
      cases compileModulo signature function objects hypotheses <;>
        cases compileModulo signature argument objects hypotheses <;> rfl
  | @allI gamma delta type phi body ih =>
      have obj : liftSub (fun i => subst sigma (objects i)) =
          (fun i => subst (liftSub sigma) (liftSub objects i)) := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp [liftSub]
      have hyp : (fun i : Fin (HOL.weakenHyps (σ := type) delta).length =>
          rename wk (subst sigma (hypotheses (i.cast (by simp [HOL.weakenHyps]))))) =
          (fun i => subst (liftSub sigma)
            (rename wk (hypotheses (i.cast (by simp [HOL.weakenHyps]))))) := by
        funext i
        simp only [subst_liftSub_wk]
      simp only [compileModulo, obj, hyp]
      erw [ih (liftSub objects)
        (fun i => rename wk (hypotheses (i.cast (by simp [HOL.weakenHyps])))) (liftSub sigma)]
      cases compileModulo signature body (liftSub objects)
        (fun i => rename wk (hypotheses (i.cast (by simp [HOL.weakenHyps])))) <;> rfl
  | allE term function ih =>
      simp only [compileModulo, ih]
      cases represent signature term with
      | none => rfl
      | some code =>
          cases compileModulo signature function objects hypotheses with
          | none => rfl
          | some native => simp [subst, subst_comp]
  | convert _ proof ih => exact ih objects hypotheses sigma

end Modulo

#print axioms Operations.includeSourceConversion
#print axioms Modulo.represent_isCore
#print axioms Modulo.sourceStep_native
#print axioms Modulo.coreConversion_native
#print axioms Modulo.compileModulo_ofProofSyntax?
#print axioms Modulo.compileModulo_typed
#print axioms Modulo.compileModulo_substitute

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLNativeGenericProofCompiler
