import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLLeibnizNativeExtensionalProofTranslation
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.FormationSensitiveHOLExtensionalDerived

/-!
# Recursive native compilation of the extensional HOL fragment

The earlier constructive compiler deliberately rejects extensional proof
constructors.  The first extensional attachment compiles a single root whose
premises belong to that constructive fragment.  This module closes the
supported fragment under nesting: every recursive proof premise is compiled
by the same qualified compiler.

Only proposition and function extensionality are primitive declarations.
Lambda congruence is function extensionality applied to the abstraction of
the recursively compiled body proof, and eta is function extensionality
applied to pointwise reflexivity.  Unsupported logical constructors continue
to return `none`.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLLeibnizNativeRecursiveExtensionalCompiler

open Presentation Mettapedia.Logic HOL.UniformListInduction
open HOLLeibnizNativeProofTranslation
open FormationSensitiveHOLExtensionalApplications

abbrev SourceContext := HOLLeibnizNativeProofTranslation.SourceContext
abbrev Formula := HOLLeibnizNativeProofTranslation.Formula

/-- The constructive Leibniz fragment closed recursively under the four
extensional HOL proof constructors. -/
def compile {gamma : SourceContext} {delta : List (Formula gamma)}
    {phi : Formula gamma} (source : HOL.ProofSyntax Symbol delta phi)
    {n : Nat} (objects : Sub Tower.Head gamma.length n)
    (hypotheses : Fin delta.length → Tower.Tm n) : Option (Tower.Tm n) :=
  match source with
  | .hyp occurrence => some (hypotheses occurrence)
  | @HOL.ProofSyntax.impI _ _ gamma delta premise _ body => do
      let _ ← represent premise
      let nativeBody ← compile body (fun i => rename wk (objects i))
        (Fin.cases (.var 0) (fun i => rename wk (hypotheses i)))
      pure (.lam nativeBody)
  | .impE function argument => do
      let nativeFunction ← compile function objects hypotheses
      let nativeArgument ← compile argument objects hypotheses
      pure (.app nativeFunction nativeArgument)
  | .allI body => do
      let nativeBody ← compile body (liftSub objects)
        (fun i => rename wk (hypotheses (i.cast (by simp [HOL.weakenHyps]))))
      pure (.lam nativeBody)
  | .allE term function => do
      let nativeArgument ← represent term
      let nativeFunction ← compile function objects hypotheses
      pure (.app nativeFunction (subst objects nativeArgument))
  | .eqRefl term => do
      let _ ← represent term
      pure FormationSensitiveHOLLeibnizDerived.reflTerm
  | @HOL.ProofSyntax.eqSymm _ _ _ _ type x y comparison => do
      let xc ← represent x
      let _ ← represent y
      let comparisonNative ← compile comparison objects hypotheses
      pure (FormationSensitiveHOLLeibnizDerived.symmetry type
        (subst objects xc) comparisonNative)
  | @HOL.ProofSyntax.eqTrans _ _ _ _ type x y z first second => do
      let xc ← represent x
      let _ ← represent y
      let _ ← represent z
      let firstNative ← compile first objects hypotheses
      let secondNative ← compile second objects hypotheses
      pure (FormationSensitiveHOLLeibnizDerived.transitivity type
        (subst objects xc) firstNative secondNative)
  | @HOL.ProofSyntax.eqPropI _ _ _ _ p q forward backward => do
      let pc ← represent p
      let qc ← represent q
      let forwardNative ← compile forward objects hypotheses
      let backwardNative ← compile backward objects hypotheses
      pure (propositionExtensionalityApp (subst objects pc) (subst objects qc)
        forwardNative backwardNative)
  | @HOL.ProofSyntax.eqPropEL _ _ _ _ p q comparison => do
      let _ ← represent p
      let _ ← represent q
      let comparisonNative ← compile comparison objects hypotheses
      pure (FormationSensitiveHOLLeibnizDerived.propForward comparisonNative)
  | @HOL.ProofSyntax.eqPropER _ _ _ _ p q comparison => do
      let pc ← represent p
      let _ ← represent q
      let comparisonNative ← compile comparison objects hypotheses
      pure (FormationSensitiveHOLLeibnizDerived.propForward
        (FormationSensitiveHOLLeibnizDerived.symmetry .prop
          (subst objects pc) comparisonNative))
  | @HOL.ProofSyntax.eqApp _ _ _ _ _ result f g x comparison => do
      let fc ← represent f
      let _ ← represent g
      let xc ← represent x
      let comparisonNative ← compile comparison objects hypotheses
      pure (FormationSensitiveHOLLeibnizDerived.functionCongruence result
        (subst objects fc) (subst objects xc) comparisonNative)
  | @HOL.ProofSyntax.eqAppArg _ _ _ _ _ result f x y comparison => do
      let fc ← represent f
      let xc ← represent x
      let _ ← represent y
      let comparisonNative ← compile comparison objects hypotheses
      pure (FormationSensitiveHOLLeibnizDerived.congruence result
        (subst objects fc) (subst objects xc) comparisonNative)
  | @HOL.ProofSyntax.eqLam _ _ _ _ domain codomain left right comparison => do
      let leftCode ← represent left
      let rightCode ← represent right
      let comparisonNative ← compile comparison (liftSub objects)
        (fun i => rename wk (hypotheses (i.cast (by simp [HOL.weakenHyps]))))
      pure (functionExtensionalityApp
        (FormationSensitiveHOLInterface.typeAt
          FormationSensitiveHOLUniformList.types n domain)
        (FormationSensitiveHOLInterface.typeAt
          FormationSensitiveHOLUniformList.types n codomain)
        (.lam (subst (liftSub objects) leftCode))
        (.lam (subst (liftSub objects) rightCode))
        (.lam comparisonNative))
  | @HOL.ProofSyntax.funExt _ _ _ _ domain codomain function other pointwise => do
      let functionCode ← represent function
      let otherCode ← represent other
      let pointwiseNative ← compile pointwise objects hypotheses
      pure (functionExtensionalityApp
        (FormationSensitiveHOLInterface.typeAt
          FormationSensitiveHOLUniformList.types n domain)
        (FormationSensitiveHOLInterface.typeAt
          FormationSensitiveHOLUniformList.types n codomain)
        (subst objects functionCode) (subst objects otherCode) pointwiseNative)
  | .beta term body => do
      let _ ← represent term
      let _ ← represent body
      pure FormationSensitiveHOLLeibnizDerived.reflTerm
  | @HOL.ProofSyntax.eta _ _ _ _ domain codomain function => do
      let functionCode ← represent function
      let functionTarget := subst objects functionCode
      pure (functionExtensionalityApp
        (FormationSensitiveHOLInterface.typeAt
          FormationSensitiveHOLUniformList.types n domain)
        (FormationSensitiveHOLInterface.typeAt
          FormationSensitiveHOLUniformList.types n codomain)
        (.lam (.app (rename wk functionTarget) (.var 0))) functionTarget
        (.lam FormationSensitiveHOLLeibnizDerived.reflTerm))
  | _ => none

@[simp] theorem propositionExtensionalityApp_subst {n m : Nat}
    (sigma : Sub Tower.Head n m) (p q forward backward : Tower.Tm n) :
    subst sigma (propositionExtensionalityApp p q forward backward) =
      propositionExtensionalityApp (subst sigma p) (subst sigma q)
        (subst sigma forward) (subst sigma backward) := by
  rfl

@[simp] theorem functionExtensionalityApp_subst {n m : Nat}
    (sigma : Sub Tower.Head n m)
    (domain codomain function other pointwise : Tower.Tm n) :
    subst sigma
        (functionExtensionalityApp domain codomain function other pointwise) =
      functionExtensionalityApp (subst sigma domain) (subst sigma codomain)
        (subst sigma function) (subst sigma other) (subst sigma pointwise) := by
  rfl

/-- Recursive extensional compilation is natural in the native environment.
In particular, the object and proof environments are lifted explicitly under
both source binders. -/
theorem compile_substitute {gamma : SourceContext} {delta : List (Formula gamma)}
    {phi : Formula gamma} (source : HOL.ProofSyntax Symbol delta phi)
    {n m : Nat} (objects : Sub Tower.Head gamma.length n)
    (hypotheses : Fin delta.length → Tower.Tm n) (sigma : Sub Tower.Head n m) :
    compile source (fun i => subst sigma (objects i))
        (fun i => subst sigma (hypotheses i)) =
      (compile source objects hypotheses).map (subst sigma) := by
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
      simp only [compile, obj, hyp]
      erw [ih (fun i => rename wk (objects i))
        (Fin.cases (.var 0) (fun i => rename wk (hypotheses i))) (liftSub sigma)]
      cases represent p <;>
        cases compile body (fun i => rename wk (objects i))
          (Fin.cases (.var 0) (fun i => rename wk (hypotheses i))) <;> rfl
  | impE function argument ihf iha =>
      simp only [compile, ihf, iha]
      cases compile function objects hypotheses <;>
        cases compile argument objects hypotheses <;> rfl
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
      simp only [compile, obj, hyp]
      erw [ih (liftSub objects)
        (fun i => rename wk (hypotheses (i.cast (by simp [HOL.weakenHyps]))))
        (liftSub sigma)]
      cases compile body (liftSub objects)
        (fun i => rename wk (hypotheses (i.cast (by simp [HOL.weakenHyps])))) <;> rfl
  | allE term function ih =>
      simp only [compile, ih]
      cases represent term with
      | none => rfl
      | some code =>
          cases compile function objects hypotheses with
          | none => rfl
          | some native => simp [subst, subst_comp]
  | eqRefl term => simp only [compile]; cases represent term <;> rfl
  | @eqSymm gamma delta type x y comparison ih =>
      simp only [compile, ih]
      cases represent x <;> cases represent y <;>
        cases compile comparison objects hypotheses <;>
          simp [subst_comp, FormationSensitiveHOLLeibnizDerived.symmetry_subst]
  | @eqTrans gamma delta type x y z first second ihh ihk =>
      simp only [compile, ihh, ihk]
      cases represent x <;> cases represent y <;> cases represent z <;>
        cases compile first objects hypotheses <;> cases compile second objects hypotheses <;>
          simp [subst_comp, FormationSensitiveHOLLeibnizDerived.transitivity_subst]
  | @eqPropI gamma delta p q forward backward ihf ihb =>
      simp only [compile, ihf, ihb]
      cases represent p <;> cases represent q <;>
        cases compile forward objects hypotheses <;>
          cases compile backward objects hypotheses <;> simp [subst_comp]
  | @eqPropEL gamma delta p q comparison ih =>
      simp only [compile, ih]
      cases represent p <;> cases represent q <;>
        cases compile comparison objects hypotheses <;> rfl
  | @eqPropER gamma delta p q comparison ih =>
      simp only [compile, ih]
      cases represent p <;> cases represent q <;>
        cases compile comparison objects hypotheses <;>
          simp [subst_comp, FormationSensitiveHOLLeibnizDerived.symmetry_subst,
            FormationSensitiveHOLLeibnizDerived.propForward_subst]
  | @eqApp gamma delta a b f g x comparison ih =>
      simp only [compile, ih]
      cases represent f <;> cases represent g <;> cases represent x <;>
        cases compile comparison objects hypotheses <;>
          simp [subst_comp, FormationSensitiveHOLLeibnizDerived.functionCongruence_subst]
  | @eqAppArg gamma delta a b f x y comparison ih =>
      simp only [compile, ih]
      cases represent f <;> cases represent x <;> cases represent y <;>
        cases compile comparison objects hypotheses <;>
          simp [subst_comp, FormationSensitiveHOLLeibnizDerived.congruence_subst]
  | @eqLam gamma delta domain codomain left right comparison ih =>
      have obj : liftSub (fun i => subst sigma (objects i)) =
          (fun i => subst (liftSub sigma) (liftSub objects i)) := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp [liftSub]
      have hyp : (fun i : Fin (HOL.weakenHyps (σ := domain) delta).length =>
          rename wk (subst sigma (hypotheses (i.cast (by simp [HOL.weakenHyps]))))) =
          (fun i => subst (liftSub sigma)
            (rename wk (hypotheses (i.cast (by simp [HOL.weakenHyps]))))) := by
        funext i
        simp only [subst_liftSub_wk]
      simp only [compile, obj, hyp]
      erw [ih (liftSub objects)
        (fun i => rename wk (hypotheses (i.cast (by simp [HOL.weakenHyps]))))
        (liftSub sigma)]
      cases represent left <;> cases represent right <;>
        cases compile comparison (liftSub objects)
          (fun i => rename wk
            (hypotheses (i.cast (by simp [HOL.weakenHyps])))) <;>
          simp [subst, subst_comp, FormationSensitiveHOLInterface.typeAt_subst]
  | @funExt gamma delta domain codomain function other pointwise ih =>
      simp only [compile, ih]
      cases represent function <;> cases represent other <;>
        cases compile pointwise objects hypotheses <;>
          simp [FormationSensitiveHOLInterface.typeAt_subst]
  | beta term body =>
      simp only [compile]
      cases represent term <;> cases represent body <;> rfl
  | @eta gamma delta domain codomain function =>
      simp only [compile]
      cases represent function <;>
        simp [subst, subst_comp, FormationSensitiveHOLInterface.typeAt_subst]
  | _ => rfl

namespace NativeTyping

open Presentation.FormationSensitive
open FormationSensitiveHOLProofFamily (proof universalProposition)
open FormationSensitiveHOLUniformList (rawImp rawAll)

abbrev baseRules := FormationSensitiveHOLProofFamily.rules
abbrev rules := FormationSensitiveHOLExtensionalProfile.rules

/-- Object substitutions remain constructive: source objects do not acquire
proof-theoretic strength when opaque extensional proof constants are added. -/
abbrev Objects {gamma : SourceContext} {n : Nat} (target : Tower.Ctx n)
    (objects : Sub Tower.Head gamma.length n) : Prop :=
  HOLLeibnizNativeProofTranslation.NativeTyping.Objects target objects

/-- Proof hypotheses, unlike objects, live in the full extensional profile so
an extensional proof can be consumed beneath any later source rule. -/
def Hypotheses {gamma : SourceContext} {delta : List (Formula gamma)}
    {n : Nat} (target : Tower.Ctx n)
    (objects : Sub Tower.Head gamma.length n)
    (hypotheses : Fin delta.length → Tower.Tm n) : Prop :=
  ∀ i, ∃ code, represent (delta.get i) = some code ∧
    Typing rules target (hypotheses i) (proof (subst objects code))

theorem represented_typed {gamma : SourceContext} {type : HOL.Ty BaseSort}
    {term : HOL.Term Symbol gamma type} {code : Tower.Tm gamma.length}
    (represented : represent term = some code) {n : Nat}
    {target : Tower.Ctx n}
    {objects : Sub Tower.Head gamma.length n}
    (typed : Objects target objects) :
    Typing baseRules target (subst objects code)
      (FormationSensitiveHOLInterface.typeAt
        FormationSensitiveHOLUniformList.types n type) :=
  HOLLeibnizNativeProofTranslation.NativeTyping.represented_typed
    represented typed

theorem Objects.weaken {gamma : SourceContext} {n : Nat}
    {target : Tower.Ctx n}
    {objects : Sub Tower.Head gamma.length n}
    (typed : Objects target objects) (extension : Tower.Tm n) :
    Objects (.snoc target extension) (fun i => rename wk (objects i)) :=
  HOLLeibnizNativeProofTranslation.NativeTyping.Objects.weaken typed extension

theorem Objects.lift {gamma : SourceContext} {n : Nat}
    {target : Tower.Ctx n}
    {objects : Sub Tower.Head gamma.length n}
    (typed : Objects target objects) (type : HOL.Ty BaseSort) :
    Objects (gamma := type :: gamma)
      (.snoc target (FormationSensitiveHOLInterface.typeAt
        FormationSensitiveHOLUniformList.types n type))
      (liftSub objects) :=
  HOLLeibnizNativeProofTranslation.NativeTyping.Objects.lift typed type

theorem Hypotheses.prepend {gamma : SourceContext}
    {delta : List (Formula gamma)} {n : Nat} {target : Tower.Ctx n}
    {objects : Sub Tower.Head gamma.length n}
    {hypotheses : Fin delta.length → Tower.Tm n}
    (typed : Hypotheses target objects hypotheses)
    {p : Formula gamma} {pc : Tower.Tm gamma.length}
    (represented : represent p = some pc) :
    Hypotheses (delta := p :: delta)
      (.snoc target (proof (subst objects pc)))
      (fun i => rename wk (objects i))
      (Fin.cases (.var 0) (fun i => rename wk (hypotheses i))) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · refine ⟨pc, represented, ?_⟩
    simpa only [Fin.cases_zero, Ctx.lookup_snoc_zero,
      FormationSensitiveHOLProofFamily.proof_rename, rename_subst] using
      (Typing.var (R := rules)
        (Γ := .snoc target (proof (subst objects pc))) 0)
  · obtain ⟨code, success, admitted⟩ := typed j
    refine ⟨code, success, ?_⟩
    simpa only [Fin.cases_succ,
      FormationSensitiveHOLProofFamily.proof_rename, rename_subst] using
      admitted.weaken (extension := proof (subst objects pc))

theorem Hypotheses.lift {gamma : SourceContext}
    {delta : List (Formula gamma)} {n : Nat} {target : Tower.Ctx n}
    {objects : Sub Tower.Head gamma.length n}
    {hypotheses : Fin delta.length → Tower.Tm n}
    (typed : Hypotheses target objects hypotheses)
    (type : HOL.Ty BaseSort) :
    Hypotheses (delta := HOL.weakenHyps (σ := type) delta)
      (.snoc target (FormationSensitiveHOLInterface.typeAt
        FormationSensitiveHOLUniformList.types n type))
      (liftSub objects)
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
    rw [entry, represent_weaken, success]
    rfl
  · simpa only [subst_liftSub_wk,
      ← FormationSensitiveHOLProofFamily.proof_rename] using
      admitted.weaken (extension := FormationSensitiveHOLInterface.typeAt
        FormationSensitiveHOLUniformList.types n type)

theorem equality_conversion {n : Nat} (type : HOL.Ty BaseSort)
    (left right : Tower.Tm n) :
    Conv rules.headEq (proof (rawEquality type left right))
      (proof (FormationSensitiveHOLLeibnizInterface.rawLeibniz
        type left right)) rules.computation :=
  FormationSensitiveHOLExtensionalDerived.include_conversion
    (HOLLeibnizNativeProofTranslation.NativeTyping.equality_conversion
      type left right)

theorem equality_to_predicate {n : Nat} {target : Tower.Ctx n}
    {type : HOL.Ty BaseSort} {left right comparison : Tower.Tm n}
    (leftTyped : Typing baseRules target left
      (FormationSensitiveHOLInterface.typeAt
        FormationSensitiveHOLUniformList.types n type))
    (rightTyped : Typing baseRules target right
      (FormationSensitiveHOLInterface.typeAt
        FormationSensitiveHOLUniformList.types n type))
    (comparisonTyped : Typing rules target comparison
      (proof (rawEquality type left right))) :
    Typing rules target comparison
      (proof (FormationSensitiveHOLLeibnizInterface.rawLeibniz
        type left right)) :=
  .conv comparisonTyped
    (FormationSensitiveHOLExtensionalProfile.include_typed
      (FormationSensitiveHOLProofFamily.proof_formed
        (FormationSensitiveHOLLeibnizRules.rawLeibniz_typed
          leftTyped rightTyped)))
    (.sort Tower.zero) (equality_conversion type left right)

theorem equality_from_predicate {n : Nat} {target : Tower.Ctx n}
    {type : HOL.Ty BaseSort} {left right comparison : Tower.Tm n}
    (leftTyped : Typing baseRules target left
      (FormationSensitiveHOLInterface.typeAt
        FormationSensitiveHOLUniformList.types n type))
    (rightTyped : Typing baseRules target right
      (FormationSensitiveHOLInterface.typeAt
        FormationSensitiveHOLUniformList.types n type))
    (comparisonTyped : Typing rules target comparison
      (proof (FormationSensitiveHOLLeibnizInterface.rawLeibniz
        type left right))) :
    Typing rules target comparison (proof (rawEquality type left right)) :=
  .conv comparisonTyped
    (FormationSensitiveHOLExtensionalProfile.include_typed
      (FormationSensitiveHOLProofFamily.proof_formed
        (HOLLeibnizNativeProofTranslation.NativeTyping.equality_proposition
          leftTyped rightTyped)))
    (.sort Tower.zero) (.symm _ _ (equality_conversion type left right))

theorem equality_reflexivity {n : Nat} {target : Tower.Ctx n}
    {type : HOL.Ty BaseSort} {term : Tower.Tm n}
    (termTyped : Typing baseRules target term
      (FormationSensitiveHOLInterface.typeAt
        FormationSensitiveHOLUniformList.types n type)) :
    Typing rules target FormationSensitiveHOLLeibnizDerived.reflTerm
      (proof (rawEquality type term term)) :=
  FormationSensitiveHOLExtensionalProfile.include_typed
    (HOLLeibnizNativeProofTranslation.NativeTyping.equality_reflexivity
      termTyped)

theorem equality_of_conversion {n : Nat} {target : Tower.Ctx n}
    {type : HOL.Ty BaseSort} {left right : Tower.Tm n}
    (leftTyped : Typing baseRules target left
      (FormationSensitiveHOLInterface.typeAt
        FormationSensitiveHOLUniformList.types n type))
    (rightTyped : Typing baseRules target right
      (FormationSensitiveHOLInterface.typeAt
        FormationSensitiveHOLUniformList.types n type))
    (conversion : Conv rules.headEq left right rules.computation) :
    Typing rules target FormationSensitiveHOLLeibnizDerived.reflTerm
      (proof (rawEquality type left right)) :=
  .conv (equality_reflexivity leftTyped)
    (FormationSensitiveHOLExtensionalProfile.include_typed
      (FormationSensitiveHOLProofFamily.proof_formed
        (HOLLeibnizNativeProofTranslation.NativeTyping.equality_proposition
          leftTyped rightTyped)))
    (.sort Tower.zero)
    (Conv.congApp (.refl _) (Conv.congApp (.refl _) conversion))

theorem represented_equality {gamma : SourceContext}
    {type : HOL.Ty BaseSort}
    {left right : HOL.Term Symbol gamma type}
    {leftCode rightCode code : Tower.Tm gamma.length}
    (leftRepresented : represent left = some leftCode)
    (rightRepresented : represent right = some rightCode)
    (represented : represent (.eq left right) = some code)
    {n : Nat} {target : Tower.Ctx n}
    {objects : Sub Tower.Head gamma.length n} {native : Tower.Tm n}
    (typed : Typing rules target native (proof (subst objects code))) :
    Typing rules target native
      (proof (rawEquality type (subst objects leftCode)
        (subst objects rightCode))) := by
  have shape : code = rawEquality type leftCode rightCode := by
    simpa [represent_eq, leftRepresented, rightRepresented, eq_comm] using
      represented
  subst code
  simpa only [rawEquality_subst] using typed

/-- Apply the declared proposition-extensionality constant to proof terms
that may themselves have been produced by recursive extensional compilation. -/
theorem proposition_extensionality_typed {n : Nat}
    {target : Tower.Ctx n} {p q forward backward : Tower.Tm n}
    (pTyped : Typing baseRules target p
      (FormationSensitiveHOLInterface.typeAt
        FormationSensitiveHOLUniformList.types n .prop))
    (qTyped : Typing baseRules target q
      (FormationSensitiveHOLInterface.typeAt
        FormationSensitiveHOLUniformList.types n .prop))
    (forwardTyped : Typing rules target forward (proof (rawImp p q)))
    (backwardTyped : Typing rules target backward (proof (rawImp q p))) :
    Typing rules target
      (propositionExtensionalityApp p q forward backward)
      (proof (rawEquality .prop p q)) := by
  have pProfile : Typing rules target p
      (liftClosed FormationSensitiveHOLExtensionalProfile.proposition) := by
    simpa [FormationSensitiveHOLExtensionalProfile.proposition,
      FormationSensitiveHOLUniformList.types,
      FormationSensitiveHOLInterface.typeAt] using
      FormationSensitiveHOLExtensionalProfile.include_typed pTyped
  have qProfile : Typing rules target q
      (liftClosed FormationSensitiveHOLExtensionalProfile.proposition) := by
    simpa [FormationSensitiveHOLExtensionalProfile.proposition,
      FormationSensitiveHOLUniformList.types,
      FormationSensitiveHOLInterface.typeAt] using
      FormationSensitiveHOLExtensionalProfile.include_typed qTyped
  have applied :=
    FormationSensitiveHOLExtensionalApplications.propositionExtensionalityApp_typed
      pProfile qProfile forwardTyped backwardTyped
  have propositionCode :
      liftClosed FormationSensitiveHOLExtensionalProfile.proposition =
        FormationSensitiveHOLInterface.typeAt
          FormationSensitiveHOLUniformList.types n .prop := by
    rfl
  rw [propositionCode,
    FormationSensitiveHOLExtensionalProfile.rawLeibnizAt_typeAt] at applied
  exact equality_from_predicate pTyped qTyped applied

/-- One checked native function-extensionality spine.  Its pointwise premise
is expressed in the represented source proof family, then converted to the
dependent method type expected by the opaque declaration. -/
theorem function_extensionality_typed {n : Nat}
    {target : Tower.Ctx n} {domain codomain : HOL.Ty BaseSort}
    {function other pointwise : Tower.Tm n}
    (functionTyped : Typing baseRules target function
      (FormationSensitiveHOLInterface.typeAt
        FormationSensitiveHOLUniformList.types n (.arr domain codomain)))
    (otherTyped : Typing baseRules target other
      (FormationSensitiveHOLInterface.typeAt
        FormationSensitiveHOLUniformList.types n (.arr domain codomain)))
    (pointwiseTyped : Typing rules target pointwise
      (proof (rawAll domain
        (rawEquality codomain
          (.app (rename wk function) (.var 0))
          (.app (rename wk other) (.var 0)))))) :
    Typing rules target
      (functionExtensionalityApp
        (FormationSensitiveHOLInterface.typeAt
          FormationSensitiveHOLUniformList.types n domain)
        (FormationSensitiveHOLInterface.typeAt
          FormationSensitiveHOLUniformList.types n codomain)
        function other pointwise)
      (proof (rawEquality (.arr domain codomain) function other)) := by
  let domainCode := FormationSensitiveHOLInterface.typeAt
    FormationSensitiveHOLUniformList.types n domain
  let codomainCode := FormationSensitiveHOLInterface.typeAt
    FormationSensitiveHOLUniformList.types n codomain
  have domainTyped : Typing baseRules target domainCode (sortTm Tower.zero) :=
    FormationSensitiveHOLProofFamily.simple_type_formed domain target
  have codomainTyped : Typing baseRules target codomainCode
      (sortTm Tower.zero) :=
    FormationSensitiveHOLProofFamily.simple_type_formed codomain target
  have functionArrow : Typing baseRules target function
      (FormationSensitiveHOLExtensionalProfile.arrow
        domainCode codomainCode) := by
    simpa [domainCode, codomainCode,
      FormationSensitiveHOLExtensionalProfile.arrow,
      FormationSensitiveHOLInterface.typeAt] using functionTyped
  have otherArrow : Typing baseRules target other
      (FormationSensitiveHOLExtensionalProfile.arrow
        domainCode codomainCode) := by
    simpa [domainCode, codomainCode,
      FormationSensitiveHOLExtensionalProfile.arrow,
      FormationSensitiveHOLInterface.typeAt] using otherTyped
  have pointwiseTypeFormed :=
    FormationSensitiveHOLExtensionalProfile.include_typed
      (FormationSensitiveHOLExtensionalProfile.pointwiseEquality_formed
        domainTyped codomainTyped functionArrow otherArrow)
  have pointwiseProfile : Typing rules target pointwise
      (FormationSensitiveHOLExtensionalProfile.pointwiseEquality
        domainCode codomainCode function other) :=
    .conv pointwiseTyped pointwiseTypeFormed (.sort Tower.zero)
      (HOLLeibnizNativeExtensionalProofTranslation.pointwise_conversion
        domain codomain function other)
  have applied :=
    FormationSensitiveHOLExtensionalApplications.functionExtensionalityApp_typed
      (FormationSensitiveHOLExtensionalProfile.include_typed domainTyped)
      (FormationSensitiveHOLExtensionalProfile.include_typed codomainTyped)
      (FormationSensitiveHOLExtensionalProfile.include_typed functionArrow)
      (FormationSensitiveHOLExtensionalProfile.include_typed otherArrow)
      pointwiseProfile
  have functionTypeCode :
      FormationSensitiveHOLExtensionalProfile.arrow domainCode codomainCode =
        FormationSensitiveHOLInterface.typeAt
          FormationSensitiveHOLUniformList.types n
          (.arr domain codomain) := by
    simp [domainCode, codomainCode,
      FormationSensitiveHOLExtensionalProfile.arrow,
      FormationSensitiveHOLInterface.typeAt]
  rw [functionTypeCode,
    FormationSensitiveHOLExtensionalProfile.rawLeibnizAt_typeAt] at applied
  exact equality_from_predicate functionTyped otherTyped applied

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
      refine Fin.cases ?_ (fun prior => ?_) index <;> rfl
    _ = body := subst_ids body

/-- Turn a recursively compiled equality between two lambda bodies into the
pointwise method required by function extensionality.  Native beta conversion
accounts for the applications of the two abstractions; the proof term itself
is retained unchanged under the outer lambda. -/
theorem lambda_pointwise_typed {n : Nat}
    {target : Tower.Ctx n} {domain codomain : HOL.Ty BaseSort}
    {leftBody rightBody comparison : Tower.Tm (n + 1)}
    (leftFunctionTyped : Typing baseRules target (.lam leftBody)
      (FormationSensitiveHOLInterface.typeAt
        FormationSensitiveHOLUniformList.types n (.arr domain codomain)))
    (rightFunctionTyped : Typing baseRules target (.lam rightBody)
      (FormationSensitiveHOLInterface.typeAt
        FormationSensitiveHOLUniformList.types n (.arr domain codomain)))
    (comparisonTyped : Typing rules
      (.snoc target (FormationSensitiveHOLInterface.typeAt
        FormationSensitiveHOLUniformList.types n domain)) comparison
      (proof (rawEquality codomain leftBody rightBody))) :
    Typing rules target (.lam comparison)
      (proof (rawAll domain
        (rawEquality codomain
          (.app (rename wk (.lam leftBody)) (.var 0))
          (.app (rename wk (.lam rightBody)) (.var 0))))) := by
  let domainCode := FormationSensitiveHOLInterface.typeAt
    FormationSensitiveHOLUniformList.types n domain
  let leftApplication : Tower.Tm (n + 1) :=
    .app (rename wk (.lam leftBody)) (.var 0)
  let rightApplication : Tower.Tm (n + 1) :=
    .app (rename wk (.lam rightBody)) (.var 0)
  have leftApplicationTyped :=
    FormationSensitiveHOLLeibnizRules.application_typed
      (FormationSensitiveHOLLeibnizDerived.weaken_typed
        leftFunctionTyped domainCode)
      (FormationSensitiveHOLLeibnizDerived.variable_zero target domain)
  have rightApplicationTyped :=
    FormationSensitiveHOLLeibnizRules.application_typed
      (FormationSensitiveHOLLeibnizDerived.weaken_typed
        rightFunctionTyped domainCode)
      (FormationSensitiveHOLLeibnizDerived.variable_zero target domain)
  have targetProposition :=
    HOLLeibnizNativeProofTranslation.NativeTyping.equality_proposition
      leftApplicationTyped rightApplicationTyped
  have leftBeta : Conv rules.headEq leftApplication leftBody
      rules.computation := by
    simpa only [leftApplication, Presentation.rename,
      instantiate_shifted_body] using
      FormationSensitiveHOLExtensionalDerived.include_conversion
        (FormationSensitiveHOLLeibnizDerived.beta_conversion
          (rename (liftRen wk) leftBody) (.var 0))
  have rightBeta : Conv rules.headEq rightApplication rightBody
      rules.computation := by
    simpa only [rightApplication, Presentation.rename,
      instantiate_shifted_body] using
      FormationSensitiveHOLExtensionalDerived.include_conversion
        (FormationSensitiveHOLLeibnizDerived.beta_conversion
          (rename (liftRen wk) rightBody) (.var 0))
  have equalityConversion : Conv rules.headEq
      (proof (rawEquality codomain leftBody rightBody))
      (proof (rawEquality codomain leftApplication rightApplication))
      rules.computation := by
    simpa only [rawEquality, FormationSensitiveHOLProofFamily.proof] using
      (Conv.congApp (.refl _)
        (Conv.congApp
          (Conv.congApp (.refl _) (.symm _ _ leftBeta))
          (.symm _ _ rightBeta)))
  have comparisonAtApplications : Typing rules
      (.snoc target domainCode) comparison
      (proof (rawEquality codomain leftApplication rightApplication)) :=
    .conv comparisonTyped
      (FormationSensitiveHOLExtensionalProfile.include_typed
        (FormationSensitiveHOLProofFamily.proof_formed targetProposition))
      (.sort Tower.zero) equalityConversion
  have introduced := FormationSensitiveHOLExtensionalDerived.universal_intro
    (FormationSensitiveHOLProofFamily.simple_type_formed domain target)
    targetProposition comparisonAtApplications
  simpa only [domainCode, leftApplication, rightApplication, rawAll,
    FormationSensitiveHOLUniformList.universal,
    FormationSensitiveHOLProofFamily.universalProposition, liftClosed,
    Presentation.rename, FormationSensitiveHOLInterface.typeAt_rename] using
    introduced

/-- Every successful recursive compilation is typed in the opaque
extensional profile against the representation of its exact source
conclusion.  Object variables remain in the constructive profile; proof
hypotheses and recursively compiled premises inhabit the full profile. -/
theorem compile_typed {gamma : SourceContext} {delta : List (Formula gamma)}
    {phi : Formula gamma} (source : HOL.ProofSyntax Symbol delta phi)
    {n : Nat} {target : Tower.Ctx n}
    {objects : Sub Tower.Head gamma.length n}
    {hypotheses : Fin delta.length → Tower.Tm n} {native : Tower.Tm n}
    (objectTyped : Objects target objects)
    (hypothesisTyped : Hypotheses target objects hypotheses)
    (success : compile source objects hypotheses = some native) :
    ∃ code, represent phi = some code ∧
      Typing rules target native (proof (subst objects code)) := by
  induction source generalizing n with
  | hyp occurrence =>
      simp only [compile, Option.some.injEq] at success
      subst native
      exact hypothesisTyped occurrence
  | @impI gamma delta p q body ih =>
      cases hp : represent p with
      | none => simp [compile, hp] at success
      | some pc =>
          cases hb : compile body (fun i => rename wk (objects i))
              (Fin.cases (.var 0) (fun i => rename wk (hypotheses i))) with
          | none => simp [compile, hp, hb] at success
          | some b =>
              simp [compile, hp, hb] at success
              subst native
              obtain ⟨qc, hq, bodyTyped⟩ := ih
                (objectTyped.weaken (proof (subst objects pc)))
                (hypothesisTyped.prepend hp) hb
              refine ⟨rawImp pc qc, by simp [represent_imp, hp, hq], ?_⟩
              apply FormationSensitiveHOLExtensionalDerived.implication_intro
                (represented_typed hp objectTyped)
                (represented_typed hq objectTyped)
              simpa only [FormationSensitiveHOLProofFamily.proof_rename,
                rename_subst] using bodyTyped
  | @impE gamma delta p q function argument ihf iha =>
      cases hf : compile function objects hypotheses with
      | none => simp [compile, hf] at success
      | some f =>
          cases ha : compile argument objects hypotheses with
          | none => simp [compile, hf, ha] at success
          | some a =>
              simp [compile, hf, ha] at success
              subst native
              obtain ⟨fc, hfc, functionTyped⟩ :=
                ihf objectTyped hypothesisTyped hf
              obtain ⟨pc, hp, argumentTyped⟩ :=
                iha objectTyped hypothesisTyped ha
              cases hq : represent q with
              | none => simp [represent_imp, hp, hq] at hfc
              | some qc =>
                  have shape : fc = rawImp pc qc := by
                    simpa [represent_imp, hp, hq, eq_comm] using hfc
                  subst fc
                  exact ⟨qc, rfl,
                    FormationSensitiveHOLExtensionalDerived.implication_elim
                      (represented_typed hp objectTyped)
                      (represented_typed hq objectTyped)
                      functionTyped argumentTyped⟩
  | @allI gamma delta type proposition body ih =>
      cases hb : compile body (liftSub objects)
          (fun i => rename wk
            (hypotheses (i.cast (by simp [HOL.weakenHyps])))) with
      | none => simp [compile, hb] at success
      | some b =>
          simp [compile, hb] at success
          subst native
          obtain ⟨pc, hp, bodyTyped⟩ := ih
            (objectTyped.lift type) (hypothesisTyped.lift type) hb
          refine ⟨rawAll type pc, by rw [represent_all, hp]; rfl, ?_⟩
          have introduced :=
            FormationSensitiveHOLExtensionalDerived.universal_intro
              (FormationSensitiveHOLProofFamily.simple_type_formed type target)
              (represented_typed hp (objectTyped.lift type)) bodyTyped
          simpa only [rawAll, FormationSensitiveHOLUniformList.universal,
            FormationSensitiveHOLProofFamily.universalProposition, liftClosed,
            Presentation.rename, Presentation.subst,
            FormationSensitiveHOLInterface.typeAt_rename,
            FormationSensitiveHOLInterface.typeAt_subst] using introduced
  | @allE gamma delta type proposition term function ih =>
      cases ht : represent term with
      | none => simp [compile, ht] at success
      | some tc =>
          cases hf : compile function objects hypotheses with
          | none => simp [compile, ht, hf] at success
          | some f =>
              simp [compile, ht, hf] at success
              subst native
              obtain ⟨fc, hfc, functionTyped⟩ :=
                ih objectTyped hypothesisTyped hf
              cases hp : represent proposition with
              | none => simp [represent_all, hp] at hfc
              | some pc =>
                  have shape : fc = rawAll type pc := by
                    simpa [represent_all, hp, eq_comm] using hfc
                  subst fc
                  refine ⟨inst0 tc pc,
                    by rw [represent_instantiate term proposition ht, hp]; rfl,
                    ?_⟩
                  have majorTyped : Typing rules target f
                      (proof (universalProposition
                        (FormationSensitiveHOLInterface.typeAt
                          FormationSensitiveHOLUniformList.types n type)
                        (.lam (subst (liftSub objects) pc)))) := by
                    simpa only [rawAll,
                      FormationSensitiveHOLUniformList.universal,
                      universalProposition, liftClosed, Presentation.rename,
                      Presentation.subst,
                      FormationSensitiveHOLInterface.typeAt_rename,
                      FormationSensitiveHOLInterface.typeAt_subst] using
                      functionTyped
                  have eliminated :=
                    FormationSensitiveHOLExtensionalDerived.universal_elim
                      (FormationSensitiveHOLProofFamily.simple_type_formed
                        type target)
                      (represented_typed hp (objectTyped.lift type)) majorTyped
                      (represented_typed ht objectTyped)
                  simpa only [subst_inst0] using eliminated
  | @eqRefl gamma delta type term =>
      cases ht : represent term with
      | none => simp [compile, ht] at success
      | some tc =>
          simp [compile, ht] at success
          subst native
          refine ⟨rawEquality type tc tc,
            by simp [represent_eq, ht], ?_⟩
          simpa only [rawEquality_subst] using
            equality_reflexivity (represented_typed ht objectTyped)
  | @eqSymm gamma delta type left right comparison ih =>
      cases hl : represent left with
      | none => simp [compile, hl] at success
      | some leftCode =>
          cases hr : represent right with
          | none => simp [compile, hl, hr] at success
          | some rightCode =>
              cases hc : compile comparison objects hypotheses with
              | none => simp [compile, hl, hr, hc] at success
              | some comparisonNative =>
                  simp [compile, hl, hr, hc] at success
                  subst native
                  obtain ⟨code, represented, comparisonTyped⟩ :=
                    ih objectTyped hypothesisTyped hc
                  have input := represented_equality hl hr represented
                    comparisonTyped
                  refine ⟨rawEquality type rightCode leftCode,
                    by simp [represent_eq, hl, hr], ?_⟩
                  simpa only [rawEquality_subst] using
                    equality_from_predicate
                      (represented_typed hr objectTyped)
                      (represented_typed hl objectTyped)
                      (FormationSensitiveHOLExtensionalDerived.symmetry_typed
                        (represented_typed hl objectTyped)
                        (represented_typed hr objectTyped)
                        (equality_to_predicate
                          (represented_typed hl objectTyped)
                          (represented_typed hr objectTyped) input))
  | @eqTrans gamma delta type left middle right first second ihf ihs =>
      cases hl : represent left with
      | none => simp [compile, hl] at success
      | some leftCode =>
          cases hm : represent middle with
          | none => simp [compile, hl, hm] at success
          | some middleCode =>
              cases hr : represent right with
              | none => simp [compile, hl, hm, hr] at success
              | some rightCode =>
                  cases hf : compile first objects hypotheses with
                  | none => simp [compile, hl, hm, hr, hf] at success
                  | some firstNative =>
                      cases hs : compile second objects hypotheses with
                      | none => simp [compile, hl, hm, hr, hf, hs] at success
                      | some secondNative =>
                          simp [compile, hl, hm, hr, hf, hs] at success
                          subst native
                          obtain ⟨firstCode, firstRepresented, firstTyped⟩ :=
                            ihf objectTyped hypothesisTyped hf
                          obtain ⟨secondCode, secondRepresented, secondTyped⟩ :=
                            ihs objectTyped hypothesisTyped hs
                          have firstInput := represented_equality hl hm
                            firstRepresented firstTyped
                          have secondInput := represented_equality hm hr
                            secondRepresented secondTyped
                          refine ⟨rawEquality type leftCode rightCode,
                            by simp [represent_eq, hl, hr], ?_⟩
                          simpa only [rawEquality_subst] using
                            equality_from_predicate
                              (represented_typed hl objectTyped)
                              (represented_typed hr objectTyped)
                              (FormationSensitiveHOLExtensionalDerived.transitivity_typed
                                (represented_typed hl objectTyped)
                                (represented_typed hm objectTyped)
                                (represented_typed hr objectTyped)
                                (equality_to_predicate
                                  (represented_typed hl objectTyped)
                                  (represented_typed hm objectTyped) firstInput)
                                (equality_to_predicate
                                  (represented_typed hm objectTyped)
                                  (represented_typed hr objectTyped) secondInput))
  | @eqPropI gamma delta p q forward backward ihf ihb =>
      cases hp : represent p with
      | none => simp [compile, hp] at success
      | some pc =>
          cases hq : represent q with
          | none => simp [compile, hp, hq] at success
          | some qc =>
              cases hf : compile forward objects hypotheses with
              | none => simp [compile, hp, hq, hf] at success
              | some forwardNative =>
                  cases hb : compile backward objects hypotheses with
                  | none => simp [compile, hp, hq, hf, hb] at success
                  | some backwardNative =>
                      simp [compile, hp, hq, hf, hb] at success
                      subst native
                      obtain ⟨forwardCode, forwardRepresented, forwardTyped⟩ :=
                        ihf objectTyped hypothesisTyped hf
                      obtain ⟨backwardCode, backwardRepresented,
                        backwardTyped⟩ := ihb objectTyped hypothesisTyped hb
                      have forwardShape : forwardCode = rawImp pc qc := by
                        simpa [represent_imp, hp, hq, eq_comm] using
                          forwardRepresented
                      have backwardShape : backwardCode = rawImp qc pc := by
                        simpa [represent_imp, hp, hq, eq_comm] using
                          backwardRepresented
                      subst forwardCode
                      subst backwardCode
                      refine ⟨rawEquality .prop pc qc,
                        by simp [represent_eq, hp, hq], ?_⟩
                      simpa only [rawEquality_subst, rawImp, Presentation.subst]
                        using proposition_extensionality_typed
                          (represented_typed hp objectTyped)
                          (represented_typed hq objectTyped)
                          forwardTyped backwardTyped
  | @eqPropEL gamma delta p q comparison ih =>
      cases hp : represent p with
      | none => simp [compile, hp] at success
      | some pc =>
          cases hq : represent q with
          | none => simp [compile, hp, hq] at success
          | some qc =>
              cases hc : compile comparison objects hypotheses with
              | none => simp [compile, hp, hq, hc] at success
              | some comparisonNative =>
                  simp [compile, hp, hq, hc] at success
                  subst native
                  obtain ⟨code, represented, comparisonTyped⟩ :=
                    ih objectTyped hypothesisTyped hc
                  have input := represented_equality hp hq represented
                    comparisonTyped
                  refine ⟨rawImp pc qc,
                    by simp [represent_imp, hp, hq], ?_⟩
                  exact FormationSensitiveHOLExtensionalDerived.propForward_typed
                    (represented_typed hp objectTyped)
                    (represented_typed hq objectTyped)
                    (equality_to_predicate
                      (represented_typed hp objectTyped)
                      (represented_typed hq objectTyped) input)
  | @eqPropER gamma delta p q comparison ih =>
      cases hp : represent p with
      | none => simp [compile, hp] at success
      | some pc =>
          cases hq : represent q with
          | none => simp [compile, hp, hq] at success
          | some qc =>
              cases hc : compile comparison objects hypotheses with
              | none => simp [compile, hp, hq, hc] at success
              | some comparisonNative =>
                  simp [compile, hp, hq, hc] at success
                  subst native
                  obtain ⟨code, represented, comparisonTyped⟩ :=
                    ih objectTyped hypothesisTyped hc
                  have input := represented_equality hp hq represented
                    comparisonTyped
                  refine ⟨rawImp qc pc,
                    by simp [represent_imp, hp, hq], ?_⟩
                  exact FormationSensitiveHOLExtensionalDerived.propBackward_typed
                    (represented_typed hp objectTyped)
                    (represented_typed hq objectTyped)
                    (equality_to_predicate
                      (represented_typed hp objectTyped)
                      (represented_typed hq objectTyped) input)
  | @eqApp gamma delta domain result function other argument comparison ih =>
      cases hf : represent function with
      | none => simp [compile, hf] at success
      | some functionCode =>
          cases hg : represent other with
          | none => simp [compile, hf, hg] at success
          | some otherCode =>
              cases ha : represent argument with
              | none => simp [compile, hf, hg, ha] at success
              | some argumentCode =>
                  cases hc : compile comparison objects hypotheses with
                  | none => simp [compile, hf, hg, ha, hc] at success
                  | some comparisonNative =>
                      simp [compile, hf, hg, ha, hc] at success
                      subst native
                      obtain ⟨code, represented, comparisonTyped⟩ :=
                        ih objectTyped hypothesisTyped hc
                      have input := represented_equality hf hg represented
                        comparisonTyped
                      have functionApplication :=
                        FormationSensitiveHOLLeibnizRules.application_typed
                          (represented_typed hf objectTyped)
                          (represented_typed ha objectTyped)
                      have otherApplication :=
                        FormationSensitiveHOLLeibnizRules.application_typed
                          (represented_typed hg objectTyped)
                          (represented_typed ha objectTyped)
                      refine ⟨rawEquality result
                          (.app functionCode argumentCode)
                          (.app otherCode argumentCode),
                        by simp [represent_eq, represent_app, hf, hg, ha], ?_⟩
                      simpa only [rawEquality_subst, Presentation.subst] using
                        equality_from_predicate functionApplication
                          otherApplication
                          (FormationSensitiveHOLExtensionalDerived.functionCongruence_typed
                            (represented_typed hf objectTyped)
                            (represented_typed hg objectTyped)
                            (represented_typed ha objectTyped)
                            (equality_to_predicate
                              (represented_typed hf objectTyped)
                              (represented_typed hg objectTyped) input))
  | @eqAppArg gamma delta domain result function left right comparison ih =>
      cases hf : represent function with
      | none => simp [compile, hf] at success
      | some functionCode =>
          cases hl : represent left with
          | none => simp [compile, hf, hl] at success
          | some leftCode =>
              cases hr : represent right with
              | none => simp [compile, hf, hl, hr] at success
              | some rightCode =>
                  cases hc : compile comparison objects hypotheses with
                  | none => simp [compile, hf, hl, hr, hc] at success
                  | some comparisonNative =>
                      simp [compile, hf, hl, hr, hc] at success
                      subst native
                      obtain ⟨code, represented, comparisonTyped⟩ :=
                        ih objectTyped hypothesisTyped hc
                      have input := represented_equality hl hr represented
                        comparisonTyped
                      have leftApplication :=
                        FormationSensitiveHOLLeibnizRules.application_typed
                          (represented_typed hf objectTyped)
                          (represented_typed hl objectTyped)
                      have rightApplication :=
                        FormationSensitiveHOLLeibnizRules.application_typed
                          (represented_typed hf objectTyped)
                          (represented_typed hr objectTyped)
                      refine ⟨rawEquality result
                          (.app functionCode leftCode)
                          (.app functionCode rightCode),
                        by simp [represent_eq, represent_app, hf, hl, hr], ?_⟩
                      simpa only [rawEquality_subst, Presentation.subst] using
                        equality_from_predicate leftApplication rightApplication
                          (FormationSensitiveHOLExtensionalDerived.congruence_typed
                            (represented_typed hf objectTyped)
                            (represented_typed hl objectTyped)
                            (represented_typed hr objectTyped)
                            (equality_to_predicate
                              (represented_typed hl objectTyped)
                              (represented_typed hr objectTyped) input))
  | @eqLam gamma delta domain codomain left right comparison ih =>
      cases hl : represent left with
      | none => simp [compile, hl] at success
      | some leftCode =>
          cases hr : represent right with
          | none => simp [compile, hl, hr] at success
          | some rightCode =>
              cases hc : compile comparison (liftSub objects)
                  (fun i => rename wk
                    (hypotheses (i.cast (by simp [HOL.weakenHyps])))) with
              | none => simp [compile, hl, hr, hc] at success
              | some comparisonNative =>
                  simp [compile, hl, hr, hc] at success
                  subst native
                  obtain ⟨code, represented, comparisonTyped⟩ := ih
                    (objectTyped.lift domain) (hypothesisTyped.lift domain) hc
                  have comparisonAtBodies := represented_equality hl hr
                    represented comparisonTyped
                  have leftFunctionRepresented :
                      represent (.lam left) = some (.lam leftCode) := by
                    simp [represent_lam, hl]
                  have rightFunctionRepresented :
                      represent (.lam right) = some (.lam rightCode) := by
                    simp [represent_lam, hr]
                  have leftFunctionTyped :=
                    represented_typed leftFunctionRepresented objectTyped
                  have rightFunctionTyped :=
                    represented_typed rightFunctionRepresented objectTyped
                  have pointwiseTyped := lambda_pointwise_typed
                    leftFunctionTyped rightFunctionTyped comparisonAtBodies
                  refine ⟨rawEquality (.arr domain codomain)
                      (.lam leftCode) (.lam rightCode),
                    by simp [represent_eq, leftFunctionRepresented,
                      rightFunctionRepresented], ?_⟩
                  simpa only [rawEquality_subst, Presentation.subst] using
                    function_extensionality_typed leftFunctionTyped
                      rightFunctionTyped pointwiseTyped
  | @funExt gamma delta domain codomain function other pointwise ih =>
      cases hf : represent function with
      | none => simp [compile, hf] at success
      | some functionCode =>
          cases hg : represent other with
          | none => simp [compile, hf, hg] at success
          | some otherCode =>
              cases hp : compile pointwise objects hypotheses with
              | none => simp [compile, hf, hg, hp] at success
              | some pointwiseNative =>
                  simp [compile, hf, hg, hp] at success
                  subst native
                  obtain ⟨pointwiseCode, pointwiseRepresented,
                    pointwiseTyped⟩ := ih objectTyped hypothesisTyped hp
                  have pointwiseShape : pointwiseCode =
                      rawAll domain
                        (rawEquality codomain
                          (.app (rename wk functionCode) (.var 0))
                          (.app (rename wk otherCode) (.var 0))) := by
                    exact Option.some.inj
                      (pointwiseRepresented.symm.trans
                        (HOLLeibnizNativeExtensionalProofTranslation.represent_pointwiseFormula
                          hf hg))
                  subst pointwiseCode
                  have pointwiseTarget : Typing rules target pointwiseNative
                      (proof (rawAll domain
                        (rawEquality codomain
                          (.app (rename wk (subst objects functionCode)) (.var 0))
                          (.app (rename wk (subst objects otherCode)) (.var 0))))) := by
                    simpa [HOLLeibnizNativeExtensionalProofTranslation.rawAll_subst,
                      Presentation.subst, subst_liftSub_wk] using pointwiseTyped
                  refine ⟨rawEquality (.arr domain codomain)
                      functionCode otherCode,
                    by simp [represent_eq, hf, hg], ?_⟩
                  simpa only [rawEquality_subst] using
                    function_extensionality_typed
                      (represented_typed hf objectTyped)
                      (represented_typed hg objectTyped) pointwiseTarget
  | @beta gamma delta domain codomain term body =>
      cases ht : represent term with
      | none => simp [compile, ht] at success
      | some termCode =>
          cases hb : represent body with
          | none => simp [compile, ht, hb] at success
          | some bodyCode =>
              simp [compile, ht, hb] at success
              subst native
              have sourceRepresentation :
                  represent (.app (.lam body) term) =
                    some (.app (.lam bodyCode) termCode) := by
                simp [represent_app, represent_lam, ht, hb]
              have targetRepresentation :
                  represent (HOL.instantiate term body) =
                    some (inst0 termCode bodyCode) := by
                rw [represent_instantiate term body ht, hb]
                rfl
              refine ⟨rawEquality codomain
                  (.app (.lam bodyCode) termCode)
                  (inst0 termCode bodyCode),
                by simp [represent_eq, sourceRepresentation,
                  targetRepresentation], ?_⟩
              rw [rawEquality_subst]
              apply equality_of_conversion
                (represented_typed sourceRepresentation objectTyped)
                (represented_typed targetRepresentation objectTyped)
              have beta := FormationSensitiveHOLLeibnizDerived.beta_conversion
                (subst (liftSub objects) bodyCode) (subst objects termCode)
              have betaProfile :=
                FormationSensitiveHOLExtensionalDerived.include_conversion beta
              simpa only [Presentation.subst, subst_inst0] using betaProfile
  | @eta gamma delta domain codomain function =>
      cases hf : represent function with
      | none => simp [compile, hf] at success
      | some functionCode =>
          simp [compile, hf] at success
          subst native
          let functionTarget := subst objects functionCode
          let etaBody : Tower.Tm (n + 1) :=
            .app (rename wk functionTarget) (.var 0)
          let etaFunction : Tower.Tm n := .lam etaBody
          have functionTyped := represented_typed hf objectTyped
          have etaRepresented :
              represent (.lam (.app (HOL.weaken function) (.var .vz))) =
                some (.lam (.app (rename wk functionCode) (.var 0))) := by
            rw [represent_lam, represent_app, represent_weaken, hf]
            rfl
          have etaFunctionTypedRaw := represented_typed etaRepresented objectTyped
          have etaFunctionTyped : Typing baseRules target etaFunction
              (FormationSensitiveHOLInterface.typeAt
                FormationSensitiveHOLUniformList.types n
                (.arr domain codomain)) := by
            simpa only [etaFunction, etaBody, functionTarget,
              Presentation.subst, subst_liftSub_wk, liftSub_zero] using
              etaFunctionTypedRaw
          let leftApplication : Tower.Tm (n + 1) :=
            .app (rename wk etaFunction) (.var 0)
          let rightApplication : Tower.Tm (n + 1) :=
            .app (rename wk functionTarget) (.var 0)
          have leftApplicationTyped :=
            FormationSensitiveHOLLeibnizRules.application_typed
              (FormationSensitiveHOLLeibnizDerived.weaken_typed
                etaFunctionTyped
                (FormationSensitiveHOLInterface.typeAt
                  FormationSensitiveHOLUniformList.types n domain))
              (FormationSensitiveHOLLeibnizDerived.variable_zero target domain)
          have rightApplicationTyped :=
            FormationSensitiveHOLLeibnizRules.application_typed
              (FormationSensitiveHOLLeibnizDerived.weaken_typed
                functionTyped
                (FormationSensitiveHOLInterface.typeAt
                  FormationSensitiveHOLUniformList.types n domain))
              (FormationSensitiveHOLLeibnizDerived.variable_zero target domain)
          have etaBeta : Conv rules.headEq leftApplication rightApplication
              rules.computation := by
            have beta := FormationSensitiveHOLLeibnizDerived.beta_conversion
              (rename (liftRen wk) etaBody) (.var 0)
            have betaProfile :=
              FormationSensitiveHOLExtensionalDerived.include_conversion beta
            have betaAtBody : Conv rules.headEq
                (.app (rename wk (.lam etaBody)) (.var 0)) etaBody
                rules.computation := by
              simpa only [Presentation.rename, instantiate_shifted_body] using
                betaProfile
            simpa only [leftApplication, rightApplication, etaFunction,
              etaBody] using betaAtBody
          have pointwiseBody := equality_of_conversion leftApplicationTyped
            rightApplicationTyped etaBeta
          have pointwiseTypedRaw :=
            FormationSensitiveHOLExtensionalDerived.universal_intro
              (FormationSensitiveHOLProofFamily.simple_type_formed
                domain target)
              (HOLLeibnizNativeProofTranslation.NativeTyping.equality_proposition
                leftApplicationTyped rightApplicationTyped)
              pointwiseBody
          have pointwiseTyped : Typing rules target
              (.lam FormationSensitiveHOLLeibnizDerived.reflTerm)
              (proof (rawAll domain
                (rawEquality codomain leftApplication rightApplication))) := by
            simpa only [rawAll, FormationSensitiveHOLUniformList.universal,
              universalProposition, liftClosed, Presentation.rename,
              FormationSensitiveHOLInterface.typeAt_rename] using
              pointwiseTypedRaw
          refine ⟨rawEquality (.arr domain codomain)
              (.lam (.app (rename wk functionCode) (.var 0))) functionCode,
            by simp [represent_eq, etaRepresented, hf], ?_⟩
          simpa only [rawEquality_subst, etaFunction, etaBody, functionTarget,
            leftApplication, rightApplication, Presentation.subst,
            subst_liftSub_wk, liftSub_zero] using
            function_extensionality_typed etaFunctionTyped functionTyped
              pointwiseTyped
  | _ => simp [compile] at success

/-- The recursive compiler preserves the complete formation-sensitive
judgment whenever the target telescope is formed. -/
theorem compile_judgment {gamma : SourceContext}
    {delta : List (Formula gamma)} {phi : Formula gamma}
    (source : HOL.ProofSyntax Symbol delta phi)
    {n : Nat} {target : Tower.Ctx n}
    {objects : Sub Tower.Head gamma.length n}
    {hypotheses : Fin delta.length → Tower.Tm n} {native : Tower.Tm n}
    (formed : ContextFormation rules target)
    (objectTyped : Objects target objects)
    (hypothesisTyped : Hypotheses target objects hypotheses)
    (success : compile source objects hypotheses = some native) :
    ∃ code, represent phi = some code ∧
      Judgment rules target native (proof (subst objects code)) := by
  obtain ⟨code, represented, typed⟩ :=
    compile_typed source objectTyped hypothesisTyped success
  exact ⟨code, represented, formed, typed⟩

/-- Closed recursive compilation needs neither an object environment nor a
proof environment; its exact output is a closed native judgment. -/
theorem compile_closed {phi : Formula []}
    (source : HOL.ProofSyntax Symbol [] phi) {native : Tower.Tm 0}
    (success : compile source Fin.elim0 Fin.elim0 = some native) :
    ∃ code, represent phi = some code ∧
      Judgment rules .nil native (proof code) := by
  obtain ⟨code, represented, typed⟩ := compile_judgment source .nil
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) success
  refine ⟨code, represented, ?_⟩
  have emptySub : (Fin.elim0 : Sub Tower.Head 0 0) = ids := by
    funext i
    exact Fin.elim0 i
  simpa only [emptySub, subst_ids] using typed

end NativeTyping

namespace Controls

open HOLLeibnizNativeExtensionalProofTranslation.Controls

/-- A constructive parent can now contain an extensional child. -/
def symmetricFunctionExtensionality :
    HOL.ProofSyntax Symbol []
      (.eq propositionIdentityFunction propositionIdentityFunction) :=
  .eqSymm propositionIdentityFunctionExtensionality

theorem nested_function_extensionality_succeeds :
    ∃ native, compile symmetricFunctionExtensionality
      (n := 0) Fin.elim0 Fin.elim0 = some native := by
  refine ⟨_, rfl⟩

theorem nested_function_extensionality_base_rejects :
    HOLLeibnizNativeProofTranslation.compile symmetricFunctionExtensionality
      (n := 0) Fin.elim0 Fin.elim0 = none := rfl

/-- Eta is derived through the one function-extensionality declaration. -/
def identityEta : HOL.ProofSyntax Symbol []
    (.eq
      (.lam (.app (HOL.weaken propositionIdentityFunction) (.var .vz)))
      propositionIdentityFunction) :=
  .eta propositionIdentityFunction

theorem eta_succeeds :
    ∃ native, compile identityEta (n := 0) Fin.elim0 Fin.elim0 = some native := by
  refine ⟨_, rfl⟩

/-- Lambda congruence is derived by abstracting the recursively compiled body
proof and passing it to function extensionality. -/
def reflexiveLambdaCongruence : HOL.ProofSyntax Symbol []
    (.eq propositionIdentityFunction propositionIdentityFunction) :=
  .eqLam (.eqRefl (.var .vz))

theorem lambda_congruence_succeeds :
    ∃ native, compile reflexiveLambdaCongruence
      (n := 0) Fin.elim0 Fin.elim0 = some native := by
  refine ⟨_, rfl⟩

/-- The nested extensional proof is not merely executable: the exact emitted
term checks against the represented source conclusion. -/
theorem nested_function_extensionality_is_typed :
    ∃ native code,
      compile symmetricFunctionExtensionality
          (n := 0) Fin.elim0 Fin.elim0 = some native ∧
      represent
          (.eq propositionIdentityFunction propositionIdentityFunction) =
        some code ∧
      Presentation.FormationSensitive.Judgment
        FormationSensitiveHOLExtensionalProfile.rules .nil native
        (FormationSensitiveHOLProofFamily.proof code) := by
  obtain ⟨native, compiled⟩ := nested_function_extensionality_succeeds
  obtain ⟨code, represented, typed⟩ :=
    NativeTyping.compile_closed symmetricFunctionExtensionality compiled
  exact ⟨native, code, compiled, represented, typed⟩

theorem eta_is_typed :
    ∃ native code,
      compile identityEta (n := 0) Fin.elim0 Fin.elim0 = some native ∧
      represent
          (.eq
            (.lam (.app (HOL.weaken propositionIdentityFunction) (.var .vz)))
            propositionIdentityFunction) = some code ∧
      Presentation.FormationSensitive.Judgment
        FormationSensitiveHOLExtensionalProfile.rules .nil native
        (FormationSensitiveHOLProofFamily.proof code) := by
  obtain ⟨native, compiled⟩ := eta_succeeds
  obtain ⟨code, represented, typed⟩ :=
    NativeTyping.compile_closed identityEta compiled
  exact ⟨native, code, compiled, represented, typed⟩

theorem lambda_congruence_is_typed :
    ∃ native code,
      compile reflexiveLambdaCongruence
          (n := 0) Fin.elim0 Fin.elim0 = some native ∧
      represent
          (.eq propositionIdentityFunction propositionIdentityFunction) =
        some code ∧
      Presentation.FormationSensitive.Judgment
        FormationSensitiveHOLExtensionalProfile.rules .nil native
        (FormationSensitiveHOLProofFamily.proof code) := by
  obtain ⟨native, compiled⟩ := lambda_congruence_succeeds
  obtain ⟨code, represented, typed⟩ :=
    NativeTyping.compile_closed reflexiveLambdaCongruence compiled
  exact ⟨native, code, compiled, represented, typed⟩

end Controls

#print axioms Controls.nested_function_extensionality_succeeds
#print axioms Controls.nested_function_extensionality_base_rejects
#print axioms Controls.eta_succeeds
#print axioms Controls.lambda_congruence_succeeds
#print axioms NativeTyping.compile_typed
#print axioms NativeTyping.compile_judgment
#print axioms NativeTyping.compile_closed
#print axioms Controls.nested_function_extensionality_is_typed
#print axioms Controls.eta_is_typed
#print axioms Controls.lambda_congruence_is_typed
#print axioms compile_substitute

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLLeibnizNativeRecursiveExtensionalCompiler
