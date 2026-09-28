import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.Execution
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.SetProfile.Models

/-!
# A higher-order Tarski–Grothendieck consumer

The source theory assumes of each set `x` that `x` lies in its universe
`UnivOf x`, and that this universe is closed under power sets.  From these
facts and the stored equations of `pow`, the source proves, one power at a
time, that each iterated power set of `x` lies in the universe of `x`.  The
translated proof step drives the iterator over the represented family
`n ↦ Holds (In (pow n x) (UnivOf x))` at an open set `x`.  The family is a
lambda term and the step is the library's transport with the translated
proof as its move.

Hosting the source theory keeps its axioms as assumptions.  In sets with
`UnivOf x = {x}` the first fact holds and the second fails, and the step has
no proof from the first fact alone.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.HOTGConsumer

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation Presentation.Declaration Presentation.FormationSensitive
open SetProfile
open CertifiedTransforms (stepOver)
open CertifiedTransformProgram.Package
open CertifiedTransformProgram.Execution
open Mettapedia.Logic

/-! ## The source development -/

section Source

variable {Γ : HOL.Ctx SetBase}

def memberT (element set : HOL.Term SetConst Γ setTy) : HOL.Formula SetConst Γ :=
  .app (.app (.const .member) element) set

def univT (set : HOL.Term SetConst Γ setTy) : HOL.Term SetConst Γ setTy :=
  .app (.const .universeOf) set

/-- `In (pow n x) (UnivOf x)`. -/
def inUniverse (count : HOL.Term SetConst Γ numTy) (set : HOL.Term SetConst Γ setTy) :
    HOL.Formula SetConst Γ :=
  memberT (powT count set) (univT set)

end Source

/-- `∀ x. In x (UnivOf x)`. -/
def univMemAxiom : HOL.Formula SetConst [] :=
  .all (σ := setTy) (memberT (.var .vz) (univT (.var .vz)))

/-- `∀ x y. In y (UnivOf x) → In (Power y) (UnivOf x)`. -/
def univPowerAxiom : HOL.Formula SetConst [] :=
  .all (σ := setTy) (.all (σ := setTy)
    (.imp (memberT (.var .vz) (univT (.var (.vs .vz))))
      (memberT (powerT (.var .vz)) (univT (.var (.vs .vz))))))

def hotgAssumptions : List (HOL.Formula SetConst []) := [univMemAxiom, univPowerAxiom]

/-- `∀ x n. In (pow n x) (UnivOf x) → In (pow (suc n) x) (UnivOf x)`. -/
def hotgStepStatement : HOL.Formula SetConst [] :=
  .all (σ := setTy) (.all (σ := numTy)
    (.imp (inUniverse (.var .vz) (.var (.vs .vz)))
      (inUniverse (sucT (.var .vz)) (.var (.vs .vz)))))

/-- `∀ x. In (pow zero x) (UnivOf x)`. -/
def hotgBaseStatement : HOL.Formula SetConst [] :=
  .all (σ := setTy) (inUniverse zeroT (.var .vz))

/-- `In (Power (pow n x)) (UnivOf x)` is `In (pow (suc n) x) (UnivOf x)`, by the
successor equation of `pow`. -/
theorem powerArticle :
    HOL.CoreConversion sourceEquations (Γ := [numTy, setTy])
      (memberT (powerT (powT (.var .vz) (.var (.vs .vz)))) (univT (.var (.vs .vz))))
      (inUniverse (sucT (.var .vz)) (.var (.vs .vz))) :=
  .symm _ _ (coreStep (.appFun _ (.appArg _ (.delta powSucEquation (by simp [sourceEquations])
    (pairSubst (.var (.vs .vz)) (.var .vz)) (pairSubst_core rfl rfl)))) rfl rfl)

/-- `In x (UnivOf x)` is `In (pow zero x) (UnivOf x)`, by the zero equation of `pow`. -/
theorem zeroArticle :
    HOL.CoreConversion sourceEquations (Γ := [setTy])
      (memberT (.var .vz) (univT (.var .vz))) (inUniverse zeroT (.var .vz)) :=
  .symm _ _ (coreStep (.appFun _ (.appArg _ (.delta powZeroEquation (by simp [sourceEquations])
    (singleSubst (.var .vz)) (singleSubst_core rfl)))) rfl rfl)

/-- The hypotheses inside the step: the membership of `pow n x`, then the
weakened facts. -/
abbrev hotgStepHyps : List (HOL.Formula SetConst [numTy, setTy]) :=
  inUniverse (.var .vz) (.var (.vs .vz)) ::
    HOL.weakenHyps (σ := numTy) (HOL.weakenHyps (σ := setTy) hotgAssumptions)

def memberHypothesis :
    HOL.ProofSyntaxModulo sourceEquations hotgStepHyps (inUniverse (.var .vz) (.var (.vs .vz))) :=
  .hyp ⟨0, by decide⟩

def powerHypothesis :
    HOL.ProofSyntaxModulo sourceEquations hotgStepHyps (HOL.weaken (HOL.weaken univPowerAxiom)) :=
  .hyp ⟨2, by decide⟩

/-- The step: the universe's closure under power, then the equation of `pow`. -/
def hotgStepBody :
    HOL.ProofSyntaxModulo sourceEquations hotgStepHyps (inUniverse (sucT (.var .vz)) (.var (.vs .vz))) :=
  .convert powerArticle
    (.impE (.allE (powT (.var .vz) (.var (.vs .vz))) (.allE (.var (.vs .vz)) powerHypothesis))
      memberHypothesis)

def hotgStep : HOL.ProofSyntaxModulo sourceEquations hotgAssumptions hotgStepStatement :=
  .allI (.allI (.impI hotgStepBody))

def membershipHypothesis :
    HOL.ProofSyntaxModulo sourceEquations (HOL.weakenHyps (σ := setTy) hotgAssumptions)
      (HOL.weaken univMemAxiom) :=
  .hyp ⟨0, by decide⟩

def hotgBase : HOL.ProofSyntaxModulo sourceEquations hotgAssumptions hotgBaseStatement :=
  .allI (.convert zeroArticle (.allE (.var .vz) membershipHypothesis))

/-! ## Native terms and declarations -/

def univMemName : DeclName := .mkSimple "univ-mem"
def univPowerName : DeclName := .mkSimple "univ-power"

section Native

variable {n : Nat}

def memberNative (element set : Tower.Tm n) : Tower.Tm n :=
  .app (.app (.const (constantName .member)) element) set
def univNative (set : Tower.Tm n) : Tower.Tm n := .app (.const (constantName .universeOf)) set
def powNative (count set : Tower.Tm n) : Tower.Tm n :=
  .app (.app (.const (constantName .pow)) count) set
def powerNative (set : Tower.Tm n) : Tower.Tm n := .app (.const (constantName .power)) set
def inUniverseNative (count set : Tower.Tm n) : Tower.Tm n :=
  memberNative (powNative count set) (univNative set)

end Native

def univMemCode : Tower.Tm 0 :=
  .app (.const (allName setTy)) (.lam (memberNative (.var 0) (univNative (.var 0))))

def univPowerCode : Tower.Tm 0 :=
  .app (.const (allName setTy)) (.lam (.app (.const (allName setTy)) (.lam
    (.app (.app (.const impName) (memberNative (.var 0) (univNative (.var 1))))
      (memberNative (powerNative (.var 0)) (univNative (.var 1)))))))

theorem univMem_represented :
    FormationSensitiveHOLInterface.represent signature univMemAxiom = some univMemCode :=
  rfl

theorem univPower_represented :
    FormationSensitiveHOLInterface.represent signature univPowerAxiom = some univPowerCode :=
  rfl

def hotgHypotheses : Fin hotgAssumptions.length → Tower.Tm 0 :=
  ![.const univMemName, .const univPowerName]

/-- The compiled step: `λ x n h. univ-power x (pow n x) h`. -/
def hotgStepTerm : Tower.Tm 0 :=
  .lam (.lam (.lam
    (.app (.app (.app (.const univPowerName) (.var 2)) (powNative (.var 1) (.var 2))) (.var 0))))

/-- The compiled base case: `λ x. univ-mem x`. -/
def hotgBaseTerm : Tower.Tm 0 := .lam (.app (.const univMemName) (.var 0))

theorem hotgStep_compiles :
    HOLNativeGenericProofCompiler.Modulo.compileModulo signature hotgStep Fin.elim0 hotgHypotheses = some hotgStepTerm :=
  rfl

theorem hotgBase_compiles :
    HOLNativeGenericProofCompiler.Modulo.compileModulo signature hotgBase Fin.elim0 hotgHypotheses = some hotgBaseTerm :=
  rfl

/-- The assumed facts of the source theory, each at the proof family of its
proposition. -/
def hotgDeclarations : Signature Tower.Head :=
  Signature.ofList
    [(univMemName, { type := FormationSensitiveHOLGenericProofFamily.proof holdsName univMemCode }),
     (univPowerName,
       { type := FormationSensitiveHOLGenericProofFamily.proof holdsName univPowerCode })]

/-- The program with the source theory's facts: the certified-transform
package, then the two assumed facts. -/
noncomputable abbrev hotgRules : Rules Tower.Head := extendRules packageRules hotgDeclarations

noncomputable abbrev RH := hotgRules

theorem package_fresh {spelling : String}
    (notAll : spelling.toList.take 4 ≠ ['a', 'l', 'l', '@'])
    (notEq : spelling.toList.take 3 ≠ ['e', 'q', '@'])
    (notFixed : fixedEntry (.mkSimple spelling) = none)
    (notHolds : Lean.Name.mkSimple spelling ≠ holdsName)
    (notAssumed : assumptionDeclarations.typeOf? (.mkSimple spelling) = none)
    (notPackage : packageDeclarations.typeOf? (.mkSimple spelling) = none) :
    packageRules.constantType (.mkSimple spelling) = none := by
  change combinedType targetRules packageDeclarations _ = none
  rw [combinedType, target_none notAll notEq notFixed notHolds notAssumed]
  exact notPackage

theorem lookup_univMem :
    RH.constantType univMemName =
      some (FormationSensitiveHOLGenericProofFamily.proof holdsName univMemCode) :=
  combinedType_of_signature packageRules hotgDeclarations
    (package_fresh (spelling := "univ-mem") (by decide) (by decide) rfl (by decide) rfl rfl) rfl

theorem lookup_univPower :
    RH.constantType univPowerName =
      some (FormationSensitiveHOLGenericProofFamily.proof holdsName univPowerCode) :=
  combinedType_of_signature packageRules hotgDeclarations
    (package_fresh (spelling := "univ-power") (by decide) (by decide) rfl (by decide) rfl rfl) rfl

theorem packageToHotg : packageRules.Morphism hotgRules (fun head => head) :=
  includeMorphism packageRules hotgDeclarations

theorem include_hotg {n : Nat} {Γ : Tower.Ctx n} {term type : Tower.Tm n}
    (typed : Typing R Γ term type) : Typing RH Γ term type := by
  simpa only [Ctx.mapHead_id, Tm.mapHead_id] using typed.mapHead packageToHotg

theorem include_hotg_conversion {n : Nat} {left right : Tower.Tm n}
    (conversion : Conv R.headEq left right R.computation) :
    Conv RH.headEq left right RH.computation := by
  have mapped := conversion.mapHead (fun head => head) packageToHotg.headEq
    packageToHotg.computation
  simpa only [Tm.mapHead_id] using mapped

theorem proofToHotg : proofRules.Morphism hotgRules (fun head => head) := by
  have first := proofToPackage
  have second := packageToHotg
  exact {
    headTyping := fun typing => typing
    isUniverse := fun isU => isU
    join := fun joined => joined
    cumulative := fun order => order
    headEq := fun equality => equality
    constantType := by
      intro name type known
      simpa only [Tm.mapHead_id] using second.constantType (first.constantType known)
    computation := by
      intro n left right step
      simpa only [Tm.mapHead_id] using second.computation (first.computation step)
  }

/-- The logical proof operations, checked in the program with the facts. -/
noncomputable def hotgOperations : HOLNativeGenericProofCompiler.Operations signature holdsName :=
  HOLNativeGenericProofCompiler.Operations.logicalOnlyAt signature holdsName holdsName_fresh
    hotgRules proofToHotg

theorem univMem_formed :
    Typing RH .nil (FormationSensitiveHOLGenericProofFamily.proof holdsName univMemCode) U0 :=
  include_hotg (proof_typed (include_profile
    (FormationSensitiveHOLInterface.represent_typed signature univMemAxiom univMem_represented)))

theorem univPower_formed :
    Typing RH .nil (FormationSensitiveHOLGenericProofFamily.proof holdsName univPowerCode) U0 :=
  include_hotg (proof_typed (include_profile
    (FormationSensitiveHOLInterface.represent_typed signature univPowerAxiom
      univPower_represented)))

theorem hotgHypotheses_typed :
    HOLNativeGenericProofCompiler.GenericTyping.Hypotheses signature hotgOperations
      (.nil : Tower.Ctx 0) Fin.elim0 hotgHypotheses := by
  intro index
  fin_cases index
  · refine ⟨univMemCode, univMem_represented, ?_⟩
    rw [subst_elim0]
    have typed := Typing.const (Γ := .nil) lookup_univMem univMem_formed (isUniverseAt Tower.zero)
    rw [liftClosed_zero] at typed
    exact typed
  · refine ⟨univPowerCode, univPower_represented, ?_⟩
    rw [subst_elim0]
    have typed := Typing.const (Γ := .nil) lookup_univPower univPower_formed
      (isUniverseAt Tower.zero)
    rw [liftClosed_zero] at typed
    exact typed


/-! ## The translated proofs, checked -/

/-- `∀ n. In (pow n x) (UnivOf x) → In (pow (suc n) x) (UnivOf x)`, represented
under the binder of `x`. -/
noncomputable def stepBodyCode {n : Nat} : Tower.Tm (n + 1) :=
  FormationSensitiveHOLGenericProofFamily.universalProposition signature numTy
    (.lam (FormationSensitiveHOLGenericProofFamily.rawImp signature
      (inUniverseNative (.var 0) (.var 1)) (inUniverseNative (sucNative (.var 0)) (.var 1))))

theorem hotgStep_represented :
    FormationSensitiveHOLInterface.represent signature hotgStepStatement =
      some (FormationSensitiveHOLGenericProofFamily.universalProposition signature setTy
        (.lam stepBodyCode)) :=
  rfl

theorem hotgBase_represented :
    FormationSensitiveHOLInterface.represent signature hotgBaseStatement =
      some (FormationSensitiveHOLGenericProofFamily.universalProposition signature setTy
        (.lam (inUniverseNative zeroNative (.var 0)))) :=
  rfl

theorem hotgStep_typed :
    Typing RH .nil hotgStepTerm
      (FormationSensitiveHOLGenericProofFamily.proof holdsName
        (FormationSensitiveHOLGenericProofFamily.universalProposition signature setTy
          (.lam stepBodyCode))) := by
  obtain ⟨code, represented, typed⟩ :=
    HOLNativeGenericProofCompiler.Modulo.compileModulo_typed signature holdsName hotgOperations
      realization hotgStep (objects := Fin.elim0) (fun index => index.elim0)
      hotgHypotheses_typed hotgStep_compiles
  rw [hotgStep_represented] at represented
  cases represented
  rw [subst_elim0] at typed
  exact typed

theorem hotgBase_typed :
    Typing RH .nil hotgBaseTerm
      (FormationSensitiveHOLGenericProofFamily.proof holdsName
        (FormationSensitiveHOLGenericProofFamily.universalProposition signature setTy
          (.lam (inUniverseNative zeroNative (.var 0))))) := by
  obtain ⟨code, represented, typed⟩ :=
    HOLNativeGenericProofCompiler.Modulo.compileModulo_typed signature holdsName hotgOperations
      realization hotgBase (objects := Fin.elim0) (fun index => index.elim0)
      hotgHypotheses_typed hotgBase_compiles
  rw [hotgBase_represented] at represented
  cases represented
  rw [subst_elim0] at typed
  exact typed

/-! ## The consumer at an open set -/

section Consumer

abbrev setT {n : Nat} : Tower.Tm n := .const (baseName .set)

/-- The context of the open set `x`. -/
abbrev setContext : Tower.Ctx 1 := .snoc .nil setT

/-- `λ n. Holds (In (pow n x) (UnivOf x))`, with `x` the open set. -/
def family : Tower.Tm 1 :=
  .lam (FormationSensitiveHOLGenericProofFamily.proof holdsName
    (inUniverseNative (.var 0) (.var 1)))

/-- The translated step at `x`. -/
def move : Tower.Tm 1 := .app (liftClosed hotgStepTerm) (.var 0)

/-- The library's transport with the translated step as its move. -/
def step : Tower.Tm 1 :=
  app4 (.const transportName) numT family (.const (constantName .suc)) move

/-- The translated base case at `x`. -/
def base : Tower.Tm 1 := .app (liftClosed hotgBaseTerm) (.var 0)

/-- The evidence the translated step computes from `evidence` at `value`. -/
def hotgEvidence (value evidence : Tower.Tm 1) : Tower.Tm 1 :=
  .app (.app (.app (.const univPowerName) (.var 0)) (powNative value (.var 0))) evidence

theorem membership_proposition_typed :
    Typing R (.snoc setContext numT) (inUniverseNative (.var 0) (.var 1)) propT :=
  include_profile (FormationSensitiveHOLInterface.represent_typed signature
    (gamma := [numTy, setTy]) (inUniverse (.var .vz) (.var (.vs .vz))) rfl)

theorem family_typed_package : Typing R setContext family (.pi numT U0) :=
  Typing.lamIntro (pi_at (raise numT_typed) U0_typed) (isUniverseAt level1)
    (proof_typed membership_proposition_typed)

theorem family_typed : Typing RH setContext family (.pi numT U0) :=
  include_hotg family_typed_package

/-- The family at an argument computes to the proof family there. -/
theorem family_runs {n : Nat} (body : Tower.Tm (n + 1)) (argument : Tower.Tm n) :
    Runs (.app (.lam (FormationSensitiveHOLGenericProofFamily.proof holdsName body)) argument)
      (FormationSensitiveHOLGenericProofFamily.proof holdsName (inst0 argument body)) :=
  Runs.beta _ argument

/-- The move type `Π n. family n → family (suc n)`. -/
abbrev moveTypeF : Tower.Tm 1 :=
  .pi numT (.pi (.app (rename wk family) (.var 0))
    (.app (rename wk (rename wk family)) (sucNative (.var 1))))

theorem moveTypeF_formed : Typing RH setContext moveTypeF U0 := by
  have weakened := family_typed_package.weaken (extension := numT)
  have twice := weakened.weaken (extension := .app (rename wk family) (.var 0))
  exact include_hotg (pi_at numT_typed
    (pi_at (Typing.appElim (B := U0) weakened (Typing.var 0))
      (Typing.appElim (B := U0) twice (sucNative_typed (Typing.var 1)))))

/-- The decoded type of the move, with the family's beta steps. -/
theorem moveType_conversion :
    Conv RH.headEq
      (FormationSensitiveHOLGenericProofFamily.proof holdsName (inst0 (.var 0) stepBodyCode))
      moveTypeF RH.computation := by
  have decoded := hotgOperations.includeProofConversion
    (FormationSensitiveHOLGenericProofFamily.universal_lambda_conversion signature holdsName
      numTy (n := 1)
      (FormationSensitiveHOLGenericProofFamily.rawImp signature
        (inUniverseNative (.var 0) (.var 1)) (inUniverseNative (sucNative (.var 0)) (.var 1))))
  have implication := hotgOperations.includeProofConversion
    (FormationSensitiveHOLGenericProofFamily.implication_conversion signature holdsName (n := 2)
      (inUniverseNative (.var 0) (.var 1)) (inUniverseNative (sucNative (.var 0)) (.var 1)))
  have beta : Runs moveTypeF
      (.pi numT (.pi (FormationSensitiveHOLGenericProofFamily.proof holdsName
          (inUniverseNative (.var 0) (.var 1)))
        (rename wk (FormationSensitiveHOLGenericProofFamily.proof holdsName
          (inUniverseNative (sucNative (.var 0)) (.var 1)))))) :=
    Runs.pi .refl (Runs.pi (family_runs _ _) (family_runs _ _))
  exact .trans _ _ _ decoded (.trans _ _ _ (Conv.congPi (.refl _) implication)
    (.symm _ _ (include_hotg_conversion (Runs.conv beta))))

theorem move_typed : Typing RH setContext move moveTypeF := by
  have major := FormationSensitiveHOLInterface.closed_typed hotgStep_typed setContext
  have proposition : Typing signature.rules (.snoc setContext setT) stepBodyCode
      (FormationSensitiveHOLInterface.typeAt types 2 .prop) :=
    FormationSensitiveHOLInterface.represent_typed signature (gamma := [setTy, setTy])
      (.all (σ := numTy) (.imp (inUniverse (.var .vz) (.var (.vs .vz)))
        (inUniverse (sucT (.var .vz)) (.var (.vs .vz))))) rfl
  have argument : Typing signature.rules setContext (.var 0)
      (FormationSensitiveHOLInterface.typeAt types 1 setTy) :=
    Typing.var 0
  have applied := hotgOperations.universalElim (simple_formed setTy setContext) proposition
    major argument
  exact Typing.conv applied moveTypeF_formed (isUniverseAt Tower.zero) moveType_conversion

/-- The partial application of transport, typed once in its telescope. -/
abbrev transportPartialTelescope : Tower.Ctx 4 :=
  .snoc (.snoc familyTelescope (.pi (.var 1) (.var 2))) moveType

theorem transportPartial_typed :
    Typing R transportPartialTelescope
      (app4 (.const transportName) (.var 3) (.var 2) (.var 1) (.var 0))
      (stepOver (.var 3) (.app (.var 3) (.var 0))) := by
  have t1 := Typing.appElim (transport_typed transportPartialTelescope) (Typing.var 3)
  have t2 := Typing.appElim t1 (Typing.var 2)
  have t3 := Typing.appElim t2 (Typing.var 1)
  exact Typing.appElim t3 (Typing.var 0)

theorem step_typed :
    Typing RH setContext step (stepOver numT (.app (rename wk family) (.var 0))) := by
  have morphism : FormationSensitive.CtxMor RH transportPartialTelescope setContext
      (patternValues ![numT, family, .const (constantName .suc), move]) := by
    intro index
    fin_cases index
    · exact move_typed
    · exact include_hotg (constant_typed .suc)
    · exact family_typed
    · exact include_hotg numT_typed
  exact (include_hotg transportPartial_typed).substitute morphism

theorem base_typed : Typing RH setContext base (.app family zeroNative) := by
  have major := FormationSensitiveHOLInterface.closed_typed hotgBase_typed setContext
  have proposition : Typing signature.rules (.snoc setContext setT)
      (inUniverseNative zeroNative (.var 0)) (FormationSensitiveHOLInterface.typeAt types 2 .prop) :=
    FormationSensitiveHOLInterface.represent_typed signature (gamma := [setTy, setTy])
      (inUniverse zeroT (.var .vz)) rfl
  have applied := hotgOperations.universalElim (simple_formed setTy setContext) proposition
    major (Typing.var 0)
  exact Typing.conv applied (Typing.appElim (B := U0) family_typed (include_hotg zeroNative_typed))
    (isUniverseAt Tower.zero) (.symm _ _ (include_hotg_conversion (Runs.conv (family_runs _ _))))

/-- The consumer's call at a numeral count, and at the open set `x`. -/
theorem consumer_typed (count : Nat) :
    Typing RH setContext (iterApp (numeral count) numT family step zeroNative base)
      (.sigma numT (.app (rename wk family) (.var 0))) := by
  have morphism : FormationSensitive.CtxMor RH iterSucTelescope setContext
      (patternValues ![numeral count, numT, family, step, zeroNative, base]) := by
    intro index
    fin_cases index
    · exact base_typed
    · exact include_hotg zeroNative_typed
    · exact step_typed
    · exact family_typed
    · exact include_hotg numT_typed
    · exact include_hotg (numeral_typed count)
  exact (include_hotg iterCall_typed).substitute morphism

/-- Applying the move runs the translated step: three beta steps. -/
theorem move_runs (value evidence : Tower.Tm 1) :
    Runs (app2 move value evidence) (hotgEvidence value evidence) := by
  have first : Runs (app2 move value evidence)
      (.app (.app (.lam (.lam (.app (.app (.app (.const univPowerName) (.var 2))
        (powNative (.var 1) (.var 2))) (.var 0)))) value) evidence) :=
    Runs.app (Runs.app (Runs.beta _ _) .refl) .refl
  have second := Runs.app (Runs.beta (.lam (.app (.app (.app (.const univPowerName) (.var 2))
    (powNative (.var 1) (.var 2))) (.var 0))) value) (.refl (a := evidence))
  have third := Runs.beta (subst (liftSub (subst0 value))
    (.app (.app (.app (.const univPowerName) (.var 2)) (powNative (.var 1) (.var 2))) (.var 0)))
    evidence
  have contracted : inst0 evidence (subst (liftSub (subst0 value))
      (.app (.app (.app (.const univPowerName) (.var 2)) (powNative (.var 1) (.var 2)))
        (.var 0) : Tower.Tm 3)) = hotgEvidence value evidence := by
    change Tm.app (Tm.app (Tm.app (.const univPowerName) (.var 0))
        (powNative (inst0 evidence (rename wk value)) (.var 0))) evidence = _
    rw [inst0_rename_wk]
    rfl
  rw [contracted] at third
  exact first.trans (second.trans third)

/-- The consumer's step runs to the successor and the translated evidence. -/
theorem step_runs (value evidence : Tower.Tm 1) :
    Runs (app2 step value evidence) (.pair (sucNative value) (hotgEvidence value evidence)) := by
  have toPair : Runs (app2 step value evidence)
      (.pair (sucNative value) (app2 move value evidence)) :=
    Runs.equation listed_transport (patternValues ![numT, family, .const (constantName .suc), move,
      value, evidence])
  exact toPair.trans (Runs.pair .refl (move_runs value evidence))

/-- The evidence from `evidence` at `start` after `count` steps. -/
def evidenceAfter : Nat → Nat → Tower.Tm 1 → Tower.Tm 1
  | _, 0, evidence => evidence
  | start, count + 1, evidence =>
      evidenceAfter (start + 1) count (hotgEvidence (numeral start) evidence)

theorem consumer_iterState : ∀ (count start : Nat) {value evidence evidence' : Tower.Tm 1},
    Runs value (numeral start) → Runs evidence evidence' →
      Runs (iterState step count value evidence).1 (numeral (start + count)) ∧
      Runs (iterState step count value evidence).2 (evidenceAfter start count evidence')
  | 0, _, _, _, _, valueRuns, evidenceRuns => ⟨valueRuns, evidenceRuns⟩
  | count + 1, start, value, evidence, evidence', valueRuns, evidenceRuns => by
      have applied : Runs (app2 step value evidence)
          (.pair (numeral (start + 1)) (hotgEvidence (numeral start) evidence')) :=
        (Runs.app (Runs.app .refl valueRuns) evidenceRuns).trans
          (step_runs (numeral start) evidence')
      have next := consumer_iterState count (start + 1)
        ((Runs.fst applied).trans (Runs.fst_pair _ _))
        ((Runs.snd applied).trans (Runs.snd_pair _ _))
      rw [show start + 1 + count = start + (count + 1) by omega] at next
      exact next

/-- At a numeral count the consumer computes the count and the translated
evidence that `pow count x` lies in the universe of `x`. -/
theorem consumer_runs (count : Nat) :
    Runs (iterApp (numeral count) numT family step zeroNative base)
      (.pair (numeral count) (evidenceAfter 0 count base)) := by
  have states := consumer_iterState count 0 (value := zeroNative) (evidence := base)
    (evidence' := base) .refl .refl
  rw [Nat.zero_add] at states
  exact (iter_runs _ _ _ count _ _).trans (Runs.pair states.1 states.2)

/-- The translated step at `value` and `evidence` is the compiler's output for
the source step body, specialized. -/
theorem hotgEvidence_compiles (value evidence : Tower.Tm 1) :
    HOLNativeGenericProofCompiler.Modulo.compileModulo signature hotgStepBody
      ![value, .var 0] (Fin.cases evidence (fun index => .const
        (![univMemName, univPowerName] index))) =
      some (hotgEvidence value evidence) :=
  rfl

theorem hotgEvidence_typed {value evidence : Tower.Tm 1}
    (valueTyped : Typing signature.rules setContext value numT)
    (evidenceTyped : Typing RH setContext evidence (.app family value)) :
    Typing RH setContext (hotgEvidence value evidence) (.app family (sucNative value)) := by
  have valueHere : Typing R setContext value numT := include_profile valueTyped
  have premise : Typing RH setContext evidence
      (FormationSensitiveHOLGenericProofFamily.proof holdsName (inUniverseNative value (.var 0))) :=
    Typing.conv evidenceTyped
      (include_hotg (proof_typed (membership_proposition_typed.instantiate valueHere)))
      (isUniverseAt Tower.zero) (include_hotg_conversion (Runs.conv (family_runs _ _)))
  have objects : HOLNativeGenericProofCompiler.GenericTyping.Objects signature
      (gamma := [numTy, setTy]) setContext ![value, .var 0] := by
    intro index
    fin_cases index
    · exact valueTyped
    · exact Typing.var 0
  have hypotheses : HOLNativeGenericProofCompiler.GenericTyping.Hypotheses signature
      hotgOperations (gamma := [numTy, setTy]) (delta := hotgStepHyps) setContext
      ![value, .var 0]
      (Fin.cases evidence (fun index => .const (![univMemName, univPowerName] index))) := by
    intro index
    fin_cases index
    · exact ⟨_, rfl, premise⟩
    · exact ⟨_, rfl, Typing.const lookup_univMem univMem_formed (isUniverseAt Tower.zero)⟩
    · exact ⟨_, rfl, Typing.const lookup_univPower univPower_formed (isUniverseAt Tower.zero)⟩
  obtain ⟨code, represented, typed⟩ :=
    HOLNativeGenericProofCompiler.Modulo.compileModulo_typed signature holdsName hotgOperations
      realization hotgStepBody objects hypotheses (hotgEvidence_compiles value evidence)
  have shape : FormationSensitiveHOLInterface.represent signature
      (inUniverse (sucT (.var .vz)) (.var (.vs .vz)) : HOL.Formula SetConst [numTy, setTy]) =
      some (inUniverseNative (sucNative (.var 0)) (.var 1)) :=
    rfl
  rw [shape] at represented
  cases represented
  exact Typing.conv typed
    (Typing.appElim (B := U0) family_typed (include_hotg (sucNative_typed valueHere)))
    (isUniverseAt Tower.zero) (.symm _ _ (include_hotg_conversion (Runs.conv (family_runs _ _))))

theorem numeral_source_typed' : ∀ count : Nat,
    Typing signature.rules setContext (numeral count) numT :=
  fun count => numeral_source_typed count

theorem evidenceAfter_typed : ∀ (count start : Nat) {evidence : Tower.Tm 1},
    Typing RH setContext evidence (.app family (numeral start)) →
      Typing RH setContext (evidenceAfter start count evidence)
        (.app family (numeral (start + count)))
  | 0, _, _, typed => typed
  | count + 1, start, _, typed => by
      have next := evidenceAfter_typed count (start + 1)
        (hotgEvidence_typed (numeral_source_typed' start) typed)
      rw [show start + 1 + count = start + (count + 1) by omega] at next
      exact next

/-- Both ends of the consumer's run have the consumer's type: every iterated
power set of the open set `x` lies in its universe, with the translated
evidence. -/
theorem consumer_result_typed (count : Nat) :
    Typing RH setContext (.pair (numeral count) (evidenceAfter 0 count base))
      (.sigma numT (.app (rename wk family) (.var 0))) := by
  have evidence := evidenceAfter_typed count 0 base_typed
  rw [Nat.zero_add] at evidence
  have weakened := family_typed_package.weaken (extension := numT)
  exact Typing.pairIntro
    (include_hotg (sigma_at numT_typed (Typing.appElim (B := U0) weakened (Typing.var 0))))
    (isUniverseAt Tower.zero) (include_hotg (numeral_typed count)) evidence

/-- At an open index with its evidence, the step computes the successor and
the translated evidence, typed at the family there. -/
theorem open_index :
    Runs (app2 step (.var 1) (.var 0) : Tower.Tm 1) (.pair (sucNative (.var 1))
        (hotgEvidence (.var 1) (.var 0))) := by
  exact step_runs _ _

end Consumer

/-! ## Semantic controls -/

section Semantics

open SetProfile.Models

/-- Sets, with the universe of a set interpreted as its singleton. -/
noncomputable abbrev singletonUniverse : Interpretation where
  Num := ULift.{1} ℕ
  Sets := ZFSet.{0}
  zero := ⟨0⟩
  suc := fun number => ⟨number.down + 1⟩
  add := fun left right => ⟨left.down + right.down⟩
  pow := fun count set => ZFSet.powerset^[count.down] set
  member := fun element set => element ∈ set
  empty := ∅
  union := ZFSet.sUnion
  power := ZFSet.powerset
  universeOf := fun set => {set}

theorem singletonUniverse_lawful : singletonUniverse.Lawful where
  add_zero _ := rfl
  add_suc _ _ := rfl
  pow_zero _ := rfl
  pow_suc count set := Function.iterate_succ_apply' ZFSet.powerset count.down set

/-- Dropped assumption: without closure of the universe under power sets, the
membership of a set in its universe does not prove the step. -/
theorem closure_needed :
    ¬ Nonempty (HOL.ProofSyntaxModulo sourceEquations [univMemAxiom] hotgStepStatement) := by
  rintro ⟨proof⟩
  have holds := proof_sound singletonUniverse proof (equationsHold singletonUniverse_lawful) (by
    intro fact listed
    simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
    subst listed
    intro set _
    exact ZFSet.mem_singleton.mpr rfl)
  have atEmpty : ZFSet.powerset (∅ : ZFSet.{0}) ∈ ({∅} : ZFSet.{0}) :=
    holds (∅ : ZFSet.{0}) trivial ⟨0⟩ trivial (ZFSet.mem_singleton.mpr rfl)
  have same := ZFSet.mem_singleton.mp atEmpty
  have member : (∅ : ZFSet.{0}) ∈ ZFSet.powerset ∅ := ZFSet.mem_powerset.mpr (ZFSet.empty_subset _)
  rw [same] at member
  exact ZFSet.notMem_empty _ member

/-- Positive control: in the numbers with sets as a single point, both assumed
facts and the equations hold, so the source step is sound there. -/
theorem hotgStep_sound :
    (HOL.HenkinModel.denote naturals.model hotgStepStatement (emptyValuation naturals.model)).down :=
  proof_sound naturals hotgStep (equationsHold naturals_lawful) (by
    intro fact listed
    simp only [hotgAssumptions, List.mem_cons, List.not_mem_nil, or_false] at listed
    rcases listed with rfl | rfl
    · intro _ _
      trivial
    · intro _ _ _ _ _
      trivial)

end Semantics

/-! ## Axiom audit -/

#print axioms hotgStep_compiles
#print axioms hotgStep_typed
#print axioms hotgBase_typed
#print axioms move_typed
#print axioms step_typed
#print axioms base_typed
#print axioms consumer_typed
#print axioms consumer_runs
#print axioms hotgEvidence_compiles
#print axioms hotgEvidence_typed
#print axioms consumer_result_typed
#print axioms closure_needed
#print axioms hotgStep_sound

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.HOTGConsumer
