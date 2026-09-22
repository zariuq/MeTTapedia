import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLNativeGenericProofCompiler

/-!
# Typing correctness of the generic HOL proof compiler

The compiler consumes a law-bearing operation algebra.  This module proves
once, independently of any particular source signature or native proof
implementation, that every successful compilation is typed at the proof
family indexed by the represented source conclusion.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLNativeGenericProofCompiler
namespace GenericTyping

open Presentation Mettapedia.Logic
open Presentation.FormationSensitive
open FormationSensitiveHOLInterface
open FormationSensitiveHOLGenericProofFamily

universe u v

variable {Base : Type u} {Const : HOL.Ty Base → Type v}

/-- The object-variable environment is a typed substitution from the source
HOL telescope directly into the target of the operation algebra. -/
def Objects (signature : LogicalSignature Base Const)
    {gamma : HOL.Ctx Base} {n : Nat} (target : Tower.Ctx n)
    (objects : Sub Tower.Head gamma.length n) : Prop :=
  Presentation.FormationSensitive.CtxMor signature.rules
    (context signature.types gamma) target objects

/-- Every source hypothesis is represented and realized by a target proof of
that represented proposition. -/
def Hypotheses (signature : LogicalSignature Base Const)
    {proofName : DeclName} (operations : Operations signature proofName)
    {gamma : HOL.Ctx Base} {delta : List (HOL.Formula Const gamma)}
    {n : Nat} (target : Tower.Ctx n)
    (objects : Sub Tower.Head gamma.length n)
    (hypotheses : Fin delta.length → Tower.Tm n) : Prop :=
  ∀ i, ∃ code, represent signature (delta.get i) = some code ∧
    Typing operations.target target (hypotheses i)
      (proof proofName (subst objects code))

theorem represented_typed (signature : LogicalSignature Base Const)
    {proofName : DeclName} (_operations : Operations signature proofName)
    {gamma : HOL.Ctx Base} {type : HOL.Ty Base}
    {term : HOL.Term Const gamma type} {code : Tower.Tm gamma.length}
    (represented : represent signature term = some code)
    {n : Nat} {target : Tower.Ctx n}
    {objects : Sub Tower.Head gamma.length n}
    (typed : Objects signature target objects) :
    Typing signature.rules target (subst objects code)
      (typeAt signature.types n type) := by
  have sourceTyped :=
    FormationSensitiveHOLInterface.represent_typed signature term represented
  simpa only [typeAt_subst] using sourceTyped.substitute typed

theorem Objects.weaken (signature : LogicalSignature Base Const)
    {gamma : HOL.Ctx Base} {n : Nat} {target : Tower.Ctx n}
    {objects : Sub Tower.Head gamma.length n}
    (typed : Objects signature target objects) (extension : Tower.Tm n) :
    Objects signature (.snoc target extension)
      (fun i => rename wk (objects i)) := by
  intro i
  simpa only [rename_subst] using (typed i).weaken (extension := extension)

theorem Objects.lift (signature : LogicalSignature Base Const)
    {gamma : HOL.Ctx Base} {n : Nat} {target : Tower.Ctx n}
    {objects : Sub Tower.Head gamma.length n}
    (typed : Objects signature target objects) (type : HOL.Ty Base) :
    Objects signature (gamma := type :: gamma)
      (.snoc target (typeAt signature.types n type)) (liftSub objects) := by
  simpa only [Objects, context, typeAt_subst] using
    Presentation.FormationSensitive.CtxMor.lift typed
      (typeAt signature.types gamma.length type)

theorem Hypotheses.prepend (signature : LogicalSignature Base Const)
    {proofName : DeclName} {operations : Operations signature proofName}
    {gamma : HOL.Ctx Base} {delta : List (HOL.Formula Const gamma)}
    {n : Nat} {target : Tower.Ctx n}
    {objects : Sub Tower.Head gamma.length n}
    {hypotheses : Fin delta.length → Tower.Tm n}
    (typed : Hypotheses signature operations target objects hypotheses)
    {p : HOL.Formula Const gamma} {pc : Tower.Tm gamma.length}
    (represented : represent signature p = some pc) :
    Hypotheses signature operations (delta := p :: delta)
      (.snoc target (proof proofName (subst objects pc)))
      (fun i => rename wk (objects i))
      (fun i => Fin.cases (.var 0) (fun j => rename wk (hypotheses j)) i) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · refine ⟨pc, represented, ?_⟩
    simpa only [Fin.cases_zero, Ctx.lookup_snoc_zero, proof_rename,
      rename_subst] using
      (Typing.var (R := operations.target)
        (Γ := .snoc target (proof proofName (subst objects pc))) 0)
  · obtain ⟨code, success, admitted⟩ := typed j
    refine ⟨code, success, ?_⟩
    simpa only [Fin.cases_succ, proof_rename, rename_subst] using
      admitted.weaken (extension := proof proofName (subst objects pc))

theorem Hypotheses.lift (signature : LogicalSignature Base Const)
    {proofName : DeclName} {operations : Operations signature proofName}
    {gamma : HOL.Ctx Base} {delta : List (HOL.Formula Const gamma)}
    {n : Nat} {target : Tower.Ctx n}
    {objects : Sub Tower.Head gamma.length n}
    {hypotheses : Fin delta.length → Tower.Tm n}
    (typed : Hypotheses signature operations target objects hypotheses)
    (type : HOL.Ty Base) :
    Hypotheses signature operations
      (delta := HOL.weakenHyps (σ := type) delta)
      (.snoc target (typeAt signature.types n type)) (liftSub objects)
      (fun i => rename wk
        (hypotheses (i.cast (by simp [HOL.weakenHyps])))) := by
  intro i
  obtain ⟨code, success, admitted⟩ :=
    typed (i.cast (by simp [HOL.weakenHyps]))
  refine ⟨rename wk code, ?_, ?_⟩
  · have entry : (HOL.weakenHyps (σ := type) delta).get i =
        HOL.weaken (delta.get (i.cast (by simp [HOL.weakenHyps]))) := by
      have indexValid : i.val < delta.length := by
        simpa [HOL.weakenHyps] using i.isLt
      change (delta.map (HOL.weaken (σ := type)))[i.val] =
        HOL.weaken delta[i.val]
      simp only [List.getElem_map]
    rw [entry, FormationSensitiveHOLInterface.represent_weaken signature, success]
    rfl
  · simpa only [subst_liftSub_wk, ← proof_rename] using
      admitted.weaken (extension := typeAt signature.types n type)

theorem represented_equality (signature : LogicalSignature Base Const)
    {gamma : HOL.Ctx Base} {type : HOL.Ty Base}
    {left right : HOL.Term Const gamma type}
    {leftCode rightCode code : Tower.Tm gamma.length}
    (leftRepresented : represent signature left = some leftCode)
    (rightRepresented : represent signature right = some rightCode)
    (comparisonRepresented : represent signature (.eq left right) = some code) :
    code = rawEquality signature type leftCode rightCode := by
  apply Option.some.inj
  rw [← comparisonRepresented]
  simpa only [rawEquality] using
    FormationSensitiveHOLInterface.represent_eq signature left right
      leftRepresented rightRepresented

theorem represented_implication (signature : LogicalSignature Base Const)
    {gamma : HOL.Ctx Base} {left right : HOL.Formula Const gamma}
    {leftCode rightCode code : Tower.Tm gamma.length}
    (leftRepresented : represent signature left = some leftCode)
    (rightRepresented : represent signature right = some rightCode)
    (implicationRepresented : represent signature (.imp left right) = some code) :
    code = rawImp signature leftCode rightCode := by
  apply Option.some.inj
  rw [← implicationRepresented]
  simp [FormationSensitiveHOLGenericProofFamily.represent_imp,
    leftRepresented, rightRepresented, rawImp]

private theorem instantiate_shifted_body {n : Nat}
    (body : Tower.Tm (n + 1)) :
    inst0 (.var 0) (rename (liftRen wk) body) = body := by
  unfold inst0
  rw [subst_rename]
  calc
    subst (fun index => subst0 (.var 0) (liftRen wk index)) body =
        subst ids body := by
      apply subst_ext
      intro index
      refine Fin.cases ?_ (fun _ => ?_) index <;> rfl
    _ = body := subst_ids body

theorem betaConversion {signature : LogicalSignature Base Const}
    {proofName : DeclName} (operations : Operations signature proofName)
    {n : Nat} (body : Tower.Tm (n + 1)) (argument : Tower.Tm n) :
    Conv operations.target.headEq (.app (.lam body) argument)
      (inst0 argument body) operations.target.computation :=
  .rel _ _ (.betaPi body argument)

/-- A proof between lambda bodies is a pointwise proof between the lambdas.
The only adjustment is native beta conversion; no extensional principle is
used until the outer operation consumes the resulting pointwise proof. -/
theorem lambdaPointwise (signature : LogicalSignature Base Const)
    {proofName : DeclName} (operations : Operations signature proofName)
    {n : Nat} {target : Tower.Ctx n} {domain codomain : HOL.Ty Base}
    {leftBody rightBody comparison : Tower.Tm (n + 1)}
    (domainTyped : Typing signature.rules target
      (typeAt signature.types n domain) (sortTm Tower.zero))
    (applicationEqualityTyped : Typing signature.rules
      (.snoc target (typeAt signature.types n domain))
      (rawEquality signature codomain
        (.app (rename wk (.lam leftBody)) (.var 0))
        (.app (rename wk (.lam rightBody)) (.var 0)))
      (typeAt signature.types (n + 1) .prop))
    (comparisonTyped : Typing operations.target
      (.snoc target (typeAt signature.types n domain)) comparison
      (proof proofName (rawEquality signature codomain leftBody rightBody))) :
    Typing operations.target target (.lam comparison)
      (proof proofName
        (universalProposition signature domain
          (.lam (rawEquality signature codomain
            (.app (rename wk (.lam leftBody)) (.var 0))
            (.app (rename wk (.lam rightBody)) (.var 0)))))) := by
  let leftApplication : Tower.Tm (n + 1) :=
    .app (rename wk (.lam leftBody)) (.var 0)
  let rightApplication : Tower.Tm (n + 1) :=
    .app (rename wk (.lam rightBody)) (.var 0)
  have leftBeta : Conv operations.target.headEq leftApplication leftBody
      operations.target.computation := by
    simpa only [leftApplication, Presentation.rename,
      instantiate_shifted_body] using
      betaConversion operations (rename (liftRen wk) leftBody) (.var 0)
  have rightBeta : Conv operations.target.headEq rightApplication rightBody
      operations.target.computation := by
    simpa only [rightApplication, Presentation.rename,
      instantiate_shifted_body] using
      betaConversion operations (rename (liftRen wk) rightBody) (.var 0)
  have equalityConversion : Conv operations.target.headEq
      (proof proofName (rawEquality signature codomain leftBody rightBody))
      (proof proofName
        (rawEquality signature codomain leftApplication rightApplication))
      operations.target.computation := by
    simpa only [rawEquality, proof] using
      (Conv.congApp (.refl _)
        (Conv.congApp
          (Conv.congApp (.refl _) (.symm _ _ leftBeta))
          (.symm _ _ rightBeta)))
  have comparisonAtApplications : Typing operations.target
      (.snoc target (typeAt signature.types n domain)) comparison
      (proof proofName
        (rawEquality signature codomain leftApplication rightApplication)) :=
    .conv comparisonTyped
      (operations.includeProofTyping
        (proof_formed signature proofName operations.fresh
          (include_typed signature proofName applicationEqualityTyped)))
      operations.zeroUniverse equalityConversion
  simpa only [leftApplication, rightApplication] using
    operations.universalIntro domainTyped applicationEqualityTyped
      comparisonAtApplications

/-- Every successful recursive compilation is typed in the operation
algebra's target at the proof family indexed by the exact represented source
conclusion.  Constructors not implemented by `compile` are rejected before
this theorem can be invoked. -/
theorem compile_typed (signature : LogicalSignature Base Const)
    (proofName : DeclName) (operations : Operations signature proofName)
    {gamma : HOL.Ctx Base} {delta : List (HOL.Formula Const gamma)}
    {phi : HOL.Formula Const gamma} (source : HOL.ProofSyntax Const delta phi)
    {n : Nat} {target : Tower.Ctx n}
    {objects : Sub Tower.Head gamma.length n}
    {hypotheses : Fin delta.length → Tower.Tm n} {native : Tower.Tm n}
    (objectTyped : Objects signature target objects)
    (hypothesisTyped : Hypotheses signature operations target objects hypotheses)
    (success : compile signature proofName operations source objects hypotheses =
      some native) :
    ∃ code, represent signature phi = some code ∧
      Typing operations.target target native
        (proof proofName (subst objects code)) := by
  induction source generalizing n with
  | hyp occurrence =>
      simp only [compile, Option.some.injEq] at success
      subst native
      exact hypothesisTyped occurrence
  | @impI gamma delta left right body ih =>
      cases hl : represent signature left with
      | none => simp [compile, hl] at success
      | some leftCode =>
          cases hb : compile signature proofName operations body
              (fun i => rename wk (objects i))
              (Fin.cases (.var 0) (fun i => rename wk (hypotheses i))) with
          | none => simp [compile, hl, hb] at success
          | some compiledBody =>
              simp [compile, hl, hb] at success
              subst native
              obtain ⟨rightCode, hr, bodyTyped⟩ := ih
                (objectTyped.weaken signature
                  (proof proofName (subst objects leftCode)))
                (hypothesisTyped.prepend signature hl) hb
              refine ⟨rawImp signature leftCode rightCode,
                by simp [FormationSensitiveHOLGenericProofFamily.represent_imp,
                  hl, hr], ?_⟩
              simpa only [rawImp_subst] using
                operations.implicationIntro
                  (represented_typed signature operations hl objectTyped)
                  (represented_typed signature operations hr objectTyped)
                  (by simpa only [proof_rename, rename_subst] using bodyTyped)
  | @impE gamma delta left right function argument ihFunction ihArgument =>
      cases hf : compile signature proofName operations function objects hypotheses with
      | none => simp [compile, hf] at success
      | some compiledFunction =>
          cases ha : compile signature proofName operations argument objects hypotheses with
          | none => simp [compile, hf, ha] at success
          | some compiledArgument =>
              simp [compile, hf, ha] at success
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
                  have shape : functionCode =
                      rawImp signature leftCode rightCode :=
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
      cases hb : compile signature proofName operations body (liftSub objects)
          (fun i => rename wk
            (hypotheses (i.cast (by simp [HOL.weakenHyps])))) with
      | none => simp [compile, hb] at success
      | some compiledBody =>
          simp [compile, hb] at success
          subst native
          obtain ⟨propositionCode, hp, bodyTyped⟩ := ih
            (objectTyped.lift signature type)
            (hypothesisTyped.lift signature type) hb
          refine ⟨universalProposition signature type (.lam propositionCode),
            by rw [FormationSensitiveHOLGenericProofFamily.represent_all signature,
              hp]; rfl, ?_⟩
          have introduced := operations.universalIntro
            (FormationSensitiveHOLInterface.typeAt_formed signature type target)
            (represented_typed signature operations hp
              (objectTyped.lift signature type)) bodyTyped
          simpa only [universalProposition_subst, Presentation.subst,
            typeAt_subst] using introduced
  | @allE gamma delta type proposition term function ih =>
      cases ht : represent signature term with
      | none => simp [compile, ht] at success
      | some termCode =>
          cases hf : compile signature proofName operations function objects hypotheses with
          | none => simp [compile, ht, hf] at success
          | some compiledFunction =>
              simp [compile, ht, hf] at success
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
                      hp, eq_comm] using
                      functionRepresented
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
  | @eqRefl gamma delta type term =>
      cases ht : represent signature term with
      | none => simp [compile, ht] at success
      | some termCode =>
          cases emitted : (operations.raw.reflexivity : Option (Tower.Tm n)) with
          | none => simp [compile, ht, emitted] at success
          | some out =>
              simp [compile, ht, emitted] at success
              subst native
              refine ⟨rawEquality signature type termCode termCode,
                by simpa only [rawEquality] using
                  FormationSensitiveHOLInterface.represent_eq signature term term ht ht,
                ?_⟩
              simpa only [rawEquality_subst] using
                operations.reflexivity_typed emitted
                  (represented_typed signature operations ht objectTyped)
                  (represented_typed signature operations ht objectTyped)
                  (.refl _)
  | @eqSymm gamma delta type left right comparison ih =>
      cases hl : represent signature left with
      | none => simp [compile, hl] at success
      | some leftCode =>
          cases hr : represent signature right with
          | none => simp [compile, hl, hr] at success
          | some rightCode =>
              cases hc : compile signature proofName operations comparison
                  objects hypotheses with
              | none => simp [compile, hl, hr, hc] at success
              | some comparisonNative =>
                  cases emitted : operations.raw.symmetry type
                      (subst objects leftCode) comparisonNative with
                  | none => simp [compile, hl, hr, hc, emitted] at success
                  | some out =>
                      simp [compile, hl, hr, hc, emitted] at success
                      subst native
                      obtain ⟨comparisonCode, comparisonRepresented,
                        comparisonTyped⟩ := ih objectTyped hypothesisTyped hc
                      have shape := represented_equality signature hl hr
                        comparisonRepresented
                      subst comparisonCode
                      refine ⟨rawEquality signature type rightCode leftCode,
                        by simpa only [rawEquality] using
                          FormationSensitiveHOLInterface.represent_eq signature
                            right left hr hl, ?_⟩
                      simpa only [rawEquality_subst] using
                        operations.symmetry_typed emitted
                          (represented_typed signature operations hl objectTyped)
                          (represented_typed signature operations hr objectTyped)
                          (by simpa only [rawEquality_subst] using comparisonTyped)
  | @eqTrans gamma delta type left middle right first second ihFirst ihSecond =>
      cases hl : represent signature left with
      | none => simp [compile, hl] at success
      | some leftCode =>
          cases hm : represent signature middle with
          | none => simp [compile, hl, hm] at success
          | some middleCode =>
              cases hr : represent signature right with
              | none => simp [compile, hl, hm, hr] at success
              | some rightCode =>
                  cases hf : compile signature proofName operations first
                      objects hypotheses with
                  | none => simp [compile, hl, hm, hr, hf] at success
                  | some firstNative =>
                      cases hs : compile signature proofName operations second
                          objects hypotheses with
                      | none => simp [compile, hl, hm, hr, hf, hs] at success
                      | some secondNative =>
                          cases emitted : operations.raw.transitivity type
                              (subst objects leftCode) firstNative secondNative with
                          | none =>
                              simp [compile, hl, hm, hr, hf, hs, emitted] at success
                          | some out =>
                              simp [compile, hl, hm, hr, hf, hs, emitted] at success
                              subst native
                              obtain ⟨firstCode, firstRepresented, firstTyped⟩ :=
                                ihFirst objectTyped hypothesisTyped hf
                              obtain ⟨secondCode, secondRepresented, secondTyped⟩ :=
                                ihSecond objectTyped hypothesisTyped hs
                              have firstShape := represented_equality signature hl hm
                                firstRepresented
                              have secondShape := represented_equality signature hm hr
                                secondRepresented
                              subst firstCode
                              subst secondCode
                              refine ⟨rawEquality signature type leftCode rightCode,
                                by simpa only [rawEquality] using
                                  FormationSensitiveHOLInterface.represent_eq signature
                                    left right hl hr, ?_⟩
                              simpa only [rawEquality_subst] using
                                operations.transitivity_typed emitted
                                  (represented_typed signature operations hl objectTyped)
                                  (represented_typed signature operations hm objectTyped)
                                  (represented_typed signature operations hr objectTyped)
                                  (by simpa only [rawEquality_subst] using firstTyped)
                                  (by simpa only [rawEquality_subst] using secondTyped)
  | @eqPropI gamma delta left right forward backward ihForward ihBackward =>
      cases hl : represent signature left with
      | none => simp [compile, hl] at success
      | some leftCode =>
          cases hr : represent signature right with
          | none => simp [compile, hl, hr] at success
          | some rightCode =>
              cases hf : compile signature proofName operations forward
                  objects hypotheses with
              | none => simp [compile, hl, hr, hf] at success
              | some forwardNative =>
                  cases hb : compile signature proofName operations backward
                      objects hypotheses with
                  | none => simp [compile, hl, hr, hf, hb] at success
                  | some backwardNative =>
                      cases emitted : operations.raw.propositionExtensionality
                          (subst objects leftCode) (subst objects rightCode)
                          forwardNative backwardNative with
                      | none =>
                          simp [compile, hl, hr, hf, hb, emitted] at success
                      | some out =>
                          simp [compile, hl, hr, hf, hb, emitted] at success
                          subst native
                          obtain ⟨forwardCode, forwardRepresented, forwardTyped⟩ :=
                            ihForward objectTyped hypothesisTyped hf
                          obtain ⟨backwardCode, backwardRepresented,
                            backwardTyped⟩ :=
                            ihBackward objectTyped hypothesisTyped hb
                          have forwardShape := represented_implication signature
                            hl hr forwardRepresented
                          have backwardShape := represented_implication signature
                            hr hl backwardRepresented
                          subst forwardCode
                          subst backwardCode
                          refine ⟨rawEquality signature .prop leftCode rightCode,
                            by simpa only [rawEquality] using
                              FormationSensitiveHOLInterface.represent_eq signature
                                left right hl hr, ?_⟩
                          simpa only [rawEquality_subst, rawImp_subst] using
                            operations.propositionExtensionality_typed emitted
                              (represented_typed signature operations hl objectTyped)
                              (represented_typed signature operations hr objectTyped)
                              (by simpa only [rawImp_subst] using forwardTyped)
                              (by simpa only [rawImp_subst] using backwardTyped)
  | @eqPropEL gamma delta left right comparison ih =>
      cases hl : represent signature left with
      | none => simp [compile, hl] at success
      | some leftCode =>
          cases hr : represent signature right with
          | none => simp [compile, hl, hr] at success
          | some rightCode =>
              cases hc : compile signature proofName operations comparison
                  objects hypotheses with
              | none => simp [compile, hl, hr, hc] at success
              | some comparisonNative =>
                  cases emitted : operations.raw.propositionForward comparisonNative with
                  | none => simp [compile, hl, hr, hc, emitted] at success
                  | some out =>
                      simp [compile, hl, hr, hc, emitted] at success
                      subst native
                      obtain ⟨comparisonCode, comparisonRepresented,
                        comparisonTyped⟩ := ih objectTyped hypothesisTyped hc
                      have shape := represented_equality signature hl hr
                        comparisonRepresented
                      subst comparisonCode
                      refine ⟨rawImp signature leftCode rightCode,
                        by simp [FormationSensitiveHOLGenericProofFamily.represent_imp,
                          hl, hr], ?_⟩
                      simpa only [rawImp_subst] using
                        operations.propositionForward_typed emitted
                          (represented_typed signature operations hl objectTyped)
                          (represented_typed signature operations hr objectTyped)
                          (by simpa only [rawEquality_subst] using comparisonTyped)
  | @eqPropER gamma delta left right comparison ih =>
      cases hl : represent signature left with
      | none => simp [compile, hl] at success
      | some leftCode =>
          cases hr : represent signature right with
          | none => simp [compile, hl, hr] at success
          | some rightCode =>
              cases hc : compile signature proofName operations comparison
                  objects hypotheses with
              | none => simp [compile, hl, hr, hc] at success
              | some comparisonNative =>
                  cases reversed : operations.raw.symmetry .prop
                      (subst objects leftCode) comparisonNative with
                  | none => simp [compile, hl, hr, hc, reversed] at success
                  | some reversedNative =>
                      cases emitted : operations.raw.propositionForward reversedNative with
                      | none =>
                          simp [compile, hl, hr, hc, reversed, emitted] at success
                      | some out =>
                          simp [compile, hl, hr, hc, reversed, emitted] at success
                          subst native
                          obtain ⟨comparisonCode, comparisonRepresented,
                            comparisonTyped⟩ := ih objectTyped hypothesisTyped hc
                          have shape := represented_equality signature hl hr
                            comparisonRepresented
                          subst comparisonCode
                          have reversedTyped := operations.symmetry_typed reversed
                            (represented_typed signature operations hl objectTyped)
                            (represented_typed signature operations hr objectTyped)
                            (by simpa only [rawEquality_subst] using comparisonTyped)
                          refine ⟨rawImp signature rightCode leftCode,
                            by simp [FormationSensitiveHOLGenericProofFamily.represent_imp,
                              hl, hr], ?_⟩
                          simpa only [rawImp_subst] using
                            operations.propositionForward_typed emitted
                              (represented_typed signature operations hr objectTyped)
                              (represented_typed signature operations hl objectTyped)
                              reversedTyped
  | @eqApp gamma delta domain result function other argument comparison ih =>
      cases hf : represent signature function with
      | none => simp [compile, hf] at success
      | some functionCode =>
          cases ho : represent signature other with
          | none => simp [compile, hf, ho] at success
          | some otherCode =>
              cases ha : represent signature argument with
              | none => simp [compile, hf, ho, ha] at success
              | some argumentCode =>
                  cases hc : compile signature proofName operations comparison
                      objects hypotheses with
                  | none => simp [compile, hf, ho, ha, hc] at success
                  | some comparisonNative =>
                      cases emitted : operations.raw.functionCongruence result
                          (subst objects functionCode) (subst objects argumentCode)
                          comparisonNative with
                      | none =>
                          simp [compile, hf, ho, ha, hc, emitted] at success
                      | some out =>
                          simp [compile, hf, ho, ha, hc, emitted] at success
                          subst native
                          obtain ⟨comparisonCode, comparisonRepresented,
                            comparisonTyped⟩ := ih objectTyped hypothesisTyped hc
                          have shape := represented_equality signature hf ho
                            comparisonRepresented
                          subst comparisonCode
                          let resultCode := rawEquality signature result
                            (.app functionCode argumentCode)
                            (.app otherCode argumentCode)
                          refine ⟨resultCode, ?_, ?_⟩
                          · simpa only [resultCode, rawEquality] using
                              FormationSensitiveHOLInterface.represent_eq signature
                                (.app function argument) (.app other argument)
                                (FormationSensitiveHOLInterface.represent_app
                                  signature function argument hf ha)
                                (FormationSensitiveHOLInterface.represent_app
                                  signature other argument ho ha)
                          · simpa only [resultCode, rawEquality_subst,
                              Presentation.subst] using
                              operations.functionCongruence_typed emitted
                                (represented_typed signature operations hf objectTyped)
                                (represented_typed signature operations ho objectTyped)
                                (represented_typed signature operations ha objectTyped)
                                (by simpa only [rawEquality_subst] using comparisonTyped)
  | @eqAppArg gamma delta domain result function left right comparison ih =>
      cases hf : represent signature function with
      | none => simp [compile, hf] at success
      | some functionCode =>
          cases hl : represent signature left with
          | none => simp [compile, hf, hl] at success
          | some leftCode =>
              cases hr : represent signature right with
              | none => simp [compile, hf, hl, hr] at success
              | some rightCode =>
                  cases hc : compile signature proofName operations comparison
                      objects hypotheses with
                  | none => simp [compile, hf, hl, hr, hc] at success
                  | some comparisonNative =>
                      cases emitted : operations.raw.argumentCongruence result
                          (subst objects functionCode) (subst objects leftCode)
                          comparisonNative with
                      | none =>
                          simp [compile, hf, hl, hr, hc, emitted] at success
                      | some out =>
                          simp [compile, hf, hl, hr, hc, emitted] at success
                          subst native
                          obtain ⟨comparisonCode, comparisonRepresented,
                            comparisonTyped⟩ := ih objectTyped hypothesisTyped hc
                          have shape := represented_equality signature hl hr
                            comparisonRepresented
                          subst comparisonCode
                          let resultCode := rawEquality signature result
                            (.app functionCode leftCode) (.app functionCode rightCode)
                          refine ⟨resultCode, ?_, ?_⟩
                          · simpa only [resultCode, rawEquality] using
                              FormationSensitiveHOLInterface.represent_eq signature
                                (.app function left) (.app function right)
                                (FormationSensitiveHOLInterface.represent_app
                                  signature function left hf hl)
                                (FormationSensitiveHOLInterface.represent_app
                                  signature function right hf hr)
                          · simpa only [resultCode, rawEquality_subst,
                              Presentation.subst] using
                              operations.argumentCongruence_typed emitted
                                (represented_typed signature operations hf objectTyped)
                                (represented_typed signature operations hl objectTyped)
                                (represented_typed signature operations hr objectTyped)
                                (by simpa only [rawEquality_subst] using comparisonTyped)
  | @eqLam gamma delta domain codomain left right comparison ih =>
      cases hl : represent signature left with
      | none => simp [compile, hl] at success
      | some leftCode =>
          cases hr : represent signature right with
          | none => simp [compile, hl, hr] at success
          | some rightCode =>
              cases hc : compile signature proofName operations comparison
                  (liftSub objects)
                  (fun i => rename wk
                    (hypotheses (i.cast (by simp [HOL.weakenHyps])))) with
              | none => simp [compile, hl, hr, hc] at success
              | some comparisonNative =>
                  cases emitted : operations.raw.functionExtensionality
                      (typeAt signature.types n domain)
                      (typeAt signature.types n codomain)
                      (.lam (subst (liftSub objects) leftCode))
                      (.lam (subst (liftSub objects) rightCode))
                      (.lam comparisonNative) with
                  | none => simp [compile, hl, hr, hc, emitted] at success
                  | some out =>
                      simp [compile, hl, hr, hc, emitted] at success
                      subst native
                      obtain ⟨comparisonCode, comparisonRepresented,
                        comparisonTyped⟩ := ih
                        (objectTyped.lift signature domain)
                        (hypothesisTyped.lift signature domain) hc
                      have comparisonShape := represented_equality signature hl hr
                        comparisonRepresented
                      subst comparisonCode
                      have leftLambdaRepresented :
                          represent signature (.lam left) = some (.lam leftCode) := by
                        exact FormationSensitiveHOLInterface.represent_lam
                          signature left hl
                      have rightLambdaRepresented :
                          represent signature (.lam right) = some (.lam rightCode) := by
                        exact FormationSensitiveHOLInterface.represent_lam
                          signature right hr
                      let leftPoint : HOL.Term Const (domain :: gamma) codomain :=
                        .app (HOL.weaken (.lam left)) (.var .vz)
                      let rightPoint : HOL.Term Const (domain :: gamma) codomain :=
                        .app (HOL.weaken (.lam right)) (.var .vz)
                      have leftPointRepresented : represent signature leftPoint =
                          some (.app (rename wk (.lam leftCode)) (.var 0)) := by
                        apply FormationSensitiveHOLInterface.represent_app
                        · simp [FormationSensitiveHOLInterface.represent_weaken signature,
                            leftLambdaRepresented]
                        · rfl
                      have rightPointRepresented : represent signature rightPoint =
                          some (.app (rename wk (.lam rightCode)) (.var 0)) := by
                        apply FormationSensitiveHOLInterface.represent_app
                        · simp [FormationSensitiveHOLInterface.represent_weaken signature,
                            rightLambdaRepresented]
                        · rfl
                      have pointEqualityRepresented :
                          represent signature (.eq leftPoint rightPoint) =
                            some (rawEquality signature codomain
                              (.app (rename wk (.lam leftCode)) (.var 0))
                              (.app (rename wk (.lam rightCode)) (.var 0))) := by
                        simpa only [rawEquality] using
                          FormationSensitiveHOLInterface.represent_eq signature
                            leftPoint rightPoint leftPointRepresented
                              rightPointRepresented
                      have pointEqualityTypedRaw :=
                        represented_typed signature operations pointEqualityRepresented
                          (objectTyped.lift signature domain)
                      have pointEqualityTyped : Typing signature.rules
                          (.snoc target (typeAt signature.types n domain))
                          (rawEquality signature codomain
                            (.app (rename wk
                              (.lam (subst (liftSub objects) leftCode))) (.var 0))
                            (.app (rename wk
                              (.lam (subst (liftSub objects) rightCode))) (.var 0)))
                          (typeAt signature.types (n + 1) .prop) := by
                        simpa only [rawEquality_subst, Presentation.subst,
                          subst_liftSub_wk, liftSub_zero] using
                          pointEqualityTypedRaw
                      have pointwiseTyped := lambdaPointwise signature operations
                        (FormationSensitiveHOLInterface.typeAt_formed
                          signature domain target)
                        pointEqualityTyped
                        (by simpa only [rawEquality_subst] using comparisonTyped)
                      let resultCode := rawEquality signature (.arr domain codomain)
                        (.lam leftCode) (.lam rightCode)
                      refine ⟨resultCode, ?_, ?_⟩
                      · simpa only [resultCode, rawEquality] using
                          FormationSensitiveHOLInterface.represent_eq signature
                            (.lam left) (.lam right)
                            leftLambdaRepresented rightLambdaRepresented
                      · simpa only [resultCode, rawEquality_subst,
                          Presentation.subst] using
                          operations.functionExtensionality_typed emitted
                            (represented_typed signature operations
                              leftLambdaRepresented objectTyped)
                            (represented_typed signature operations
                              rightLambdaRepresented objectTyped)
                            pointwiseTyped
  | @funExt gamma delta domain codomain function other pointwise ih =>
      cases hf : represent signature function with
      | none => simp [compile, hf] at success
      | some functionCode =>
          cases ho : represent signature other with
          | none => simp [compile, hf, ho] at success
          | some otherCode =>
              cases hp : compile signature proofName operations pointwise
                  objects hypotheses with
              | none => simp [compile, hf, ho, hp] at success
              | some pointwiseNative =>
                  cases emitted : operations.raw.functionExtensionality
                      (typeAt signature.types n domain)
                      (typeAt signature.types n codomain)
                      (subst objects functionCode) (subst objects otherCode)
                      pointwiseNative with
                  | none => simp [compile, hf, ho, hp, emitted] at success
                  | some out =>
                      simp [compile, hf, ho, hp, emitted] at success
                      subst native
                      obtain ⟨pointwiseCode, pointwiseRepresented,
                        pointwiseTyped⟩ := ih objectTyped hypothesisTyped hp
                      let leftPoint : HOL.Term Const (domain :: gamma) codomain :=
                        .app (HOL.weaken function) (.var .vz)
                      let rightPoint : HOL.Term Const (domain :: gamma) codomain :=
                        .app (HOL.weaken other) (.var .vz)
                      have leftPointRepresented : represent signature leftPoint =
                          some (.app (rename wk functionCode) (.var 0)) := by
                        apply FormationSensitiveHOLInterface.represent_app
                        · simp [FormationSensitiveHOLInterface.represent_weaken signature, hf]
                        · rfl
                      have rightPointRepresented : represent signature rightPoint =
                          some (.app (rename wk otherCode) (.var 0)) := by
                        apply FormationSensitiveHOLInterface.represent_app
                        · simp [FormationSensitiveHOLInterface.represent_weaken signature, ho]
                        · rfl
                      have equalityRepresented :=
                        FormationSensitiveHOLInterface.represent_eq signature
                          leftPoint rightPoint leftPointRepresented rightPointRepresented
                      have expectedPointwise :
                          represent signature ((HOL.Term.eq leftPoint rightPoint).all) =
                            some (universalProposition signature domain
                              (.lam (rawEquality signature codomain
                                (.app (rename wk functionCode) (.var 0))
                                (.app (rename wk otherCode) (.var 0))))) := by
                        rw [FormationSensitiveHOLGenericProofFamily.represent_all signature,
                          equalityRepresented]
                        rfl
                      have pointwiseShape : pointwiseCode =
                          universalProposition signature domain
                            (.lam (rawEquality signature codomain
                              (.app (rename wk functionCode) (.var 0))
                              (.app (rename wk otherCode) (.var 0)))) := by
                        exact Option.some.inj
                          (pointwiseRepresented.symm.trans expectedPointwise)
                      subst pointwiseCode
                      have pointwiseTarget : Typing operations.target target
                          pointwiseNative
                          (proof proofName
                            (universalProposition signature domain
                              (.lam (rawEquality signature codomain
                                (.app (rename wk
                                  (subst objects functionCode)) (.var 0))
                                (.app (rename wk
                                  (subst objects otherCode)) (.var 0)))))) := by
                        simpa only [universalProposition_subst,
                          rawEquality_subst, Presentation.subst,
                          subst_liftSub_wk, liftSub_zero] using pointwiseTyped
                      let resultCode := rawEquality signature (.arr domain codomain)
                        functionCode otherCode
                      refine ⟨resultCode, ?_, ?_⟩
                      · simpa only [resultCode, rawEquality] using
                          FormationSensitiveHOLInterface.represent_eq signature
                            function other hf ho
                      · simpa only [resultCode, rawEquality_subst,
                          universalProposition_subst, Presentation.subst,
                          subst_liftSub_wk] using
                          operations.functionExtensionality_typed emitted
                            (represented_typed signature operations hf objectTyped)
                            (represented_typed signature operations ho objectTyped)
                            pointwiseTarget
  | @beta gamma delta domain codomain term body =>
      cases ht : represent signature term with
      | none => simp [compile, ht] at success
      | some termCode =>
          cases hb : represent signature body with
          | none => simp [compile, ht, hb] at success
          | some bodyCode =>
              cases emitted : (operations.raw.reflexivity : Option (Tower.Tm n)) with
              | none => simp [compile, ht, hb, emitted] at success
              | some out =>
                  simp [compile, ht, hb, emitted] at success
                  subst native
                  have sourceRepresentation :
                      represent signature (.app (.lam body) term) =
                        some (.app (.lam bodyCode) termCode) := by
                    exact FormationSensitiveHOLInterface.represent_app signature
                      (.lam body) term
                      (FormationSensitiveHOLInterface.represent_lam
                        signature body hb) ht
                  have targetRepresentation :
                      represent signature (HOL.instantiate term body) =
                        some (inst0 termCode bodyCode) := by
                    rw [FormationSensitiveHOLInterface.represent_instantiate signature
                      term body ht, hb]
                    rfl
                  let resultCode := rawEquality signature codomain
                    (.app (.lam bodyCode) termCode) (inst0 termCode bodyCode)
                  refine ⟨resultCode, ?_, ?_⟩
                  · simpa only [resultCode, rawEquality] using
                      FormationSensitiveHOLInterface.represent_eq signature
                        (.app (.lam body) term) (HOL.instantiate term body)
                        sourceRepresentation targetRepresentation
                  · have conversion := betaConversion operations
                        (subst (liftSub objects) bodyCode) (subst objects termCode)
                    have converted : Conv operations.target.headEq
                        (subst objects (.app (.lam bodyCode) termCode))
                        (subst objects (inst0 termCode bodyCode))
                        operations.target.computation := by
                      simpa only [Presentation.subst, subst_inst0] using conversion
                    simpa only [resultCode, rawEquality_subst,
                      Presentation.subst, subst_inst0] using
                      operations.reflexivity_typed emitted
                        (represented_typed signature operations
                          sourceRepresentation objectTyped)
                        (represented_typed signature operations
                          targetRepresentation objectTyped)
                        converted
  | @eta gamma delta domain codomain function =>
      cases hf : represent signature function with
      | none => simp [compile, hf] at success
      | some functionCode =>
          let functionTarget := subst objects functionCode
          let etaBody : Tower.Tm (n + 1) :=
            .app (rename wk functionTarget) (.var 0)
          let etaFunction : Tower.Tm n := .lam etaBody
          cases pointwiseEmitted :
              (operations.raw.reflexivity : Option (Tower.Tm (n + 1))) with
          | none => simp [compile, hf, pointwiseEmitted] at success
          | some pointwiseNative =>
              cases emitted : operations.raw.functionExtensionality
                  (typeAt signature.types n domain)
                  (typeAt signature.types n codomain)
                  etaFunction functionTarget (.lam pointwiseNative) with
              | none =>
                  simp [compile, hf, pointwiseEmitted, emitted,
                    etaFunction, etaBody, functionTarget] at success
              | some out =>
                  simp [compile, hf, pointwiseEmitted, emitted,
                    etaFunction, etaBody, functionTarget] at success
                  subst native
                  let etaSource : HOL.Term Const gamma (.arr domain codomain) :=
                    .lam (.app (HOL.weaken function) (.var .vz))
                  have etaRepresented : represent signature etaSource =
                      some (.lam (.app (rename wk functionCode) (.var 0))) := by
                    apply FormationSensitiveHOLInterface.represent_lam
                    apply FormationSensitiveHOLInterface.represent_app
                    · simp [FormationSensitiveHOLInterface.represent_weaken signature, hf]
                    · rfl
                  have functionTyped :=
                    represented_typed signature operations hf objectTyped
                  have etaFunctionTypedRaw :=
                    represented_typed signature operations etaRepresented objectTyped
                  have etaFunctionTyped : Typing signature.rules target etaFunction
                      (typeAt signature.types n (.arr domain codomain)) := by
                    simpa only [etaFunction, etaBody, functionTarget,
                      Presentation.subst, subst_liftSub_wk, liftSub_zero] using
                      etaFunctionTypedRaw
                  let leftPoint : HOL.Term Const (domain :: gamma) codomain :=
                    .app (HOL.weaken etaSource) (.var .vz)
                  let rightPoint : HOL.Term Const (domain :: gamma) codomain :=
                    .app (HOL.weaken function) (.var .vz)
                  have leftPointRepresented : represent signature leftPoint =
                      some (.app
                        (rename wk
                          (.lam (.app (rename wk functionCode) (.var 0))))
                        (.var 0)) := by
                    apply FormationSensitiveHOLInterface.represent_app
                    · simp [FormationSensitiveHOLInterface.represent_weaken signature,
                        etaRepresented]
                    · rfl
                  have rightPointRepresented : represent signature rightPoint =
                      some (.app (rename wk functionCode) (.var 0)) := by
                    apply FormationSensitiveHOLInterface.represent_app
                    · simp [FormationSensitiveHOLInterface.represent_weaken signature, hf]
                    · rfl
                  have leftPointTypedRaw :=
                    represented_typed signature operations leftPointRepresented
                      (objectTyped.lift signature domain)
                  have rightPointTypedRaw :=
                    represented_typed signature operations rightPointRepresented
                      (objectTyped.lift signature domain)
                  let leftApplication : Tower.Tm (n + 1) :=
                    .app (rename wk etaFunction) (.var 0)
                  let rightApplication : Tower.Tm (n + 1) :=
                    .app (rename wk functionTarget) (.var 0)
                  have leftPointTyped : Typing signature.rules
                      (.snoc target (typeAt signature.types n domain))
                      leftApplication (typeAt signature.types (n + 1) codomain) := by
                    simpa only [leftApplication, etaFunction, etaBody,
                      functionTarget, Presentation.subst, subst_liftSub_wk,
                      liftSub_zero, subst_liftClosed] using leftPointTypedRaw
                  have rightPointTyped : Typing signature.rules
                      (.snoc target (typeAt signature.types n domain))
                      rightApplication (typeAt signature.types (n + 1) codomain) := by
                    simpa only [rightApplication, functionTarget,
                      Presentation.subst, subst_liftSub_wk, liftSub_zero,
                      subst_liftClosed] using rightPointTypedRaw
                  have pointEqualityRepresented :
                      represent signature (.eq leftPoint rightPoint) =
                        some (rawEquality signature codomain
                          (.app
                            (rename wk
                              (.lam (.app (rename wk functionCode) (.var 0))))
                            (.var 0))
                          (.app (rename wk functionCode) (.var 0))) := by
                    simpa only [rawEquality] using
                      FormationSensitiveHOLInterface.represent_eq signature
                        leftPoint rightPoint leftPointRepresented rightPointRepresented
                  have pointEqualityTypedRaw :=
                    represented_typed signature operations pointEqualityRepresented
                      (objectTyped.lift signature domain)
                  have pointEqualityTyped : Typing signature.rules
                      (.snoc target (typeAt signature.types n domain))
                      (rawEquality signature codomain leftApplication rightApplication)
                      (typeAt signature.types (n + 1) .prop) := by
                    simpa only [rawEquality_subst, leftApplication,
                      rightApplication, etaFunction, etaBody, functionTarget,
                      Presentation.subst, subst_liftSub_wk, liftSub_zero,
                      subst_liftClosed] using
                      pointEqualityTypedRaw
                  have etaBeta : Conv operations.target.headEq
                      leftApplication rightApplication
                      operations.target.computation := by
                    have beta := betaConversion operations
                      (rename (liftRen wk) etaBody) (.var 0)
                    have betaAtBody : Conv operations.target.headEq
                        (.app (rename wk (.lam etaBody)) (.var 0)) etaBody
                        operations.target.computation := by
                      simpa only [Presentation.rename,
                        instantiate_shifted_body] using beta
                    simpa only [leftApplication, rightApplication,
                      etaFunction, etaBody] using betaAtBody
                  have pointwiseTyped := operations.reflexivity_typed
                    pointwiseEmitted leftPointTyped rightPointTyped etaBeta
                  have quantifiedPointwise := operations.universalIntro
                    (FormationSensitiveHOLInterface.typeAt_formed
                      signature domain target)
                    pointEqualityTyped pointwiseTyped
                  let resultCode := rawEquality signature (.arr domain codomain)
                    (.lam (.app (rename wk functionCode) (.var 0))) functionCode
                  refine ⟨resultCode, ?_, ?_⟩
                  · simpa only [resultCode, rawEquality] using
                      FormationSensitiveHOLInterface.represent_eq signature
                        etaSource function etaRepresented hf
                  · simpa only [resultCode, rawEquality_subst,
                      etaFunction, etaBody, functionTarget,
                      universalProposition_subst, Presentation.subst,
                      subst_liftSub_wk, liftSub_zero] using
                      operations.functionExtensionality_typed emitted
                        etaFunctionTyped functionTyped quantifiedPointwise
  | _ => simp [compile] at success

#print axioms compile_typed

/-- Closed compilation is the empty-environment instance of the generic
correctness theorem. -/
theorem compile_closed (signature : LogicalSignature Base Const)
    (proofName : DeclName) (operations : Operations signature proofName)
    {phi : HOL.Formula Const []} (source : HOL.ProofSyntax Const [] phi)
    {native : Tower.Tm 0}
    (success : compile signature proofName operations source
      Fin.elim0 Fin.elim0 = some native) :
    ∃ code, represent signature phi = some code ∧
      Typing operations.target .nil native (proof proofName code) := by
  have objectTyped : Objects signature (gamma := [])
      (.nil : Tower.Ctx 0) Fin.elim0 := by
    intro index
    nomatch index
  have hypothesisTyped : Hypotheses signature operations
      (gamma := []) (delta := [])
      (.nil : Tower.Ctx 0) Fin.elim0 Fin.elim0 := by
    intro index
    nomatch index
  obtain ⟨code, represented, typed⟩ :=
    compile_typed signature proofName operations source
      objectTyped hypothesisTyped success
  refine ⟨code, represented, ?_⟩
  have emptySub : (Fin.elim0 : Sub Tower.Head 0 0) = ids := by
    funext index
    exact Fin.elim0 index
  simpa only [emptySub, subst_ids] using typed

#print axioms compile_closed

end GenericTyping
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLNativeGenericProofCompiler
