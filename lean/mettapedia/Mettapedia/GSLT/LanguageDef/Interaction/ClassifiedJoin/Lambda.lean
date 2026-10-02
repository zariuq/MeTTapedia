import Mettapedia.OSLF.Syntax.IntrinsicScopedLambdaClassifiedInstance
import Mettapedia.OSLF.Syntax.LambdaPatternRendering
import Mettapedia.OSLF.Syntax.VariablePosition
import Mettapedia.GSLT.LanguageDef.LambdaContinuedInteraction
import Mettapedia.GSLT.LanguageDef.BinderTypingInversion
import Mettapedia.GSLT.LanguageDef.ContinuationSignatureInversion
import Mettapedia.OSLF.MeTTaIL.MatchSpec

/-!
# The lambda iGSLT inside its classified presentation

The lambda calculus has two presentations in this development.  The
interactive one authors application, abstraction and the beta rule over raw
patterns; its terms are the closed sorted patterns and its only reduction is
a beta contraction at the root.  The classified one is intrinsically scoped
and sorted, lives over every context of variables, and has four rules: beta
and the three congruences.

The authored encoder sends an intrinsic term to its pattern.  On closed terms
it is a bijection onto the carrier of the interactive presentation.  Along
that bijection:

* a step of the interactive theory is exactly a beta contraction at the root
  of a closed term, and that contraction is the beta event of the classifier;
* the classifier has more events: a closed term reduces in the classifier
  exactly when it steps in the interactive theory or one of the three
  congruence rules applies, and abstraction congruence reaches redexes over
  open terms, which the closed carrier does not contain.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ClassifiedJoin.Lambda

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.LambdaContinuedInteraction
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.LambdaContextualRung (sig Srt appT lamT)
open Mettapedia.OSLF.Binding.LambdaScopedAuthoringComparison (encodeTerm encodeArgs wrapBinders)
open Mettapedia.OSLF.Binding.IntrinsicScopedLambdaClassifiedInstance
  (rules eqs extension_iff_step beta_classified appCongL_classified appCongR_classified
    lamCong_classified)
open Mettapedia.OSLF.Binding.IntrinsicScopedAuthoredClassifiedReduction (ExtendedReduction)
open Mettapedia.OSLF.Framework.LambdaInstance
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.Substitution (instantiateBVar liftBVars_zero)
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution

/-! ## The encoder lands in the sorted patterns -/

/-- The bound typing context of an intrinsic context: one term per variable. -/
def boundTypes (Γ : Ctx sig) : List TypeExpr := Γ.map fun _ => TypeExpr.base "Term"

theorem encode_app {Γ : Ctx sig} (function argument : Term sig Γ .term) :
    encodeTerm (appT function argument) =
      .apply "App" [encodeTerm function, encodeTerm argument] := rfl

theorem encode_lam {Γ : Ctx sig} (body : Term sig (.term :: Γ) .term) :
    encodeTerm (lamT body) = .apply "Lam" [.lambda none (encodeTerm body)] := rfl

theorem encode_var {Γ : Ctx sig} (position : Var Γ Srt.term) :
    encodeTerm (Term.var position : Term sig Γ .term) = .bvar (varIdx position).val := rfl

theorem application_notBare : ¬ UsesBareCollection (lambdaCalc.terms[0]'(by decide)) := by
  rintro ⟨_, _, _, shape⟩
  cases shape

theorem abstraction_notBare : ¬ UsesBareCollection (lambdaCalc.terms[1]'(by decide)) := by
  rintro ⟨_, _, _, shape⟩
  cases shape

/-- An encoded term is sorted by the authored signature, with one bound
variable of the term sort for each variable of its context. -/
theorem encode_hasSort : ∀ {Γ : Ctx sig} {s : Srt} (term : Term sig Γ s),
    HasSort lambdaCalc FreeTypeContext.empty (boundTypes Γ) (encodeTerm term) "Term"
  | Γ, _, .var position => by
      refine HasType.bvar ?_
      have inBounds : (varIdx position).val < (boundTypes Γ).length := by
        simp [boundTypes]
      rw [List.getElem?_eq_getElem inBounds]
      simp [boundTypes]
  | _, _, .op .app (.cons function (.cons argument .nil)) =>
      HasType.constructor (rule := lambdaCalc.terms[0]'(by decide)) (List.getElem_mem _)
        application_notBare
        (.cons trivial rfl (encode_hasSort function)
          (.cons trivial rfl (encode_hasSort argument) .nil))
  | _, _, .op .lam (.cons body .nil) =>
      HasType.constructor (rule := lambdaCalc.terms[1]'(by decide)) (List.getElem_mem _)
        abstraction_notBare
        (.cons trivial rfl (HasType.lambda (encode_hasSort body)) .nil)

/-- An encoded term has no pending substitution and no open collection. -/
theorem encode_object : ∀ {Γ : Ctx sig} {s : Srt} (term : Term sig Γ s),
    isObjectPattern (encodeTerm term) = true
  | _, _, .var _ => rfl
  | _, _, .op .app (.cons function (.cons argument .nil)) => by
      change isObjectPattern (.apply "App" [encodeTerm function, encodeTerm argument]) = true
      simp [isObjectPattern, isObjectPatternList, encode_object function,
        encode_object argument]
  | _, _, .op .lam (.cons body .nil) => by
      change isObjectPattern (.apply "Lam" [.lambda none (encodeTerm body)]) = true
      simp [isObjectPattern, isObjectPatternList, encode_object body]

/-- An encoded term names no binder. -/
theorem encode_canonical : ∀ {Γ : Ctx sig} {s : Srt} (term : Term sig Γ s),
    (encodeTerm term).hasCanonicalBinderMetadata = true
  | _, _, .var _ => rfl
  | _, _, .op .app (.cons function (.cons argument .nil)) => by
      change Pattern.hasCanonicalBinderMetadata
        (.apply "App" [encodeTerm function, encodeTerm argument]) = true
      simp [Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList,
        encode_canonical function, encode_canonical argument]
  | _, _, .op .lam (.cons body .nil) => by
      change Pattern.hasCanonicalBinderMetadata
        (.apply "Lam" [.lambda none (encodeTerm body)]) = true
      simp [Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList,
        encode_canonical body]

/-- A closed intrinsic term encodes to a term of the interactive carrier. -/
theorem encode_closed (term : Term sig [] .term) :
    ClosedTermWellSorted lambdaCalc lambdaInteractivePresentation.interactingLangSort
      (encodeTerm term) := by
  have typed : HasSort lambdaCalc FreeTypeContext.empty [] (encodeTerm term) "Term" :=
    encode_hasSort term
  have safe : ScopeSafe lambdaCalc (encodeTerm term) := typed.isWellScopedAt
  exact ⟨typed,
    ground_of_closed_sorting (sort := lambdaInteractivePresentation.interactingLangSort)
      typed (encode_object term) safe,
    encode_canonical term, encode_object term, safe⟩

/-- The closed carrier term of a closed intrinsic term. -/
def embed (term : Term sig [] .term) : lambdaInteractivePresentation.Term :=
  ⟨encodeTerm term, encode_closed term⟩

@[simp] theorem embed_pattern (term : Term sig [] .term) : (embed term).1 = encodeTerm term :=
  rfl

/-! ## The encoder is a bijection onto the closed carrier -/

/-- The encoder is injective in every context. -/
theorem encode_injective : ∀ {Γ : Ctx sig} {s : Srt} (first second : Term sig Γ s),
    encodeTerm first = encodeTerm second → first = second
  | _, _, .var first, second, same => by
      match second, same with
      | .var second, same =>
          have positions : Pattern.bvar (varIdx first).val = Pattern.bvar (varIdx second).val :=
            same
          simp only [Pattern.bvar.injEq] at positions
          rw [varIdx_injective first second (Fin.ext positions)]
      | .op .app (.cons _ (.cons _ .nil)), same =>
          have shapes : Pattern.bvar _ = Pattern.apply "App" _ := same
          cases shapes
      | .op .lam (.cons _ .nil), same =>
          have shapes : Pattern.bvar _ = Pattern.apply "Lam" _ := same
          cases shapes
  | _, _, .op .app (.cons function (.cons argument .nil)), second, same => by
      match second, same with
      | .var _, same =>
          have shapes : Pattern.apply "App" _ = Pattern.bvar _ := same
          cases shapes
      | .op .app (.cons function' (.cons argument' .nil)), same =>
          have shapes : Pattern.apply "App" [encodeTerm function, encodeTerm argument] =
              Pattern.apply "App" [encodeTerm function', encodeTerm argument'] := same
          simp only [Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at shapes
          rw [encode_injective function function' shapes.1,
            encode_injective argument argument' shapes.2]
      | .op .lam (.cons _ .nil), same =>
          have shapes : Pattern.apply "App" _ = Pattern.apply "Lam" _ := same
          simp at shapes
  | _, _, .op .lam (.cons body .nil), second, same => by
      match second, same with
      | .var _, same =>
          have shapes : Pattern.apply "Lam" _ = Pattern.bvar _ := same
          cases shapes
      | .op .app (.cons _ (.cons _ .nil)), same =>
          have shapes : Pattern.apply "Lam" _ = Pattern.apply "App" _ := same
          simp at shapes
      | .op .lam (.cons body' .nil), same =>
          have shapes : Pattern.apply "Lam" [.lambda none (encodeTerm body)] =
              Pattern.apply "Lam" [.lambda none (encodeTerm body')] := same
          simp only [Pattern.apply.injEq, List.cons.injEq, Pattern.lambda.injEq, and_true,
            true_and] at shapes
          rw [encode_injective body body' shapes]

/-- The variable at a position of a context. -/
def variableAt : (Γ : Ctx sig) → (index : Nat) → index < Γ.length → Var Γ Srt.term
  | [], _, bound => absurd bound (Nat.not_lt_zero _)
  | .term :: _, 0, _ => .zero
  | _ :: Γ, index + 1, bound => .succ (variableAt Γ index (Nat.lt_of_succ_lt_succ bound))

theorem varIdx_variableAt : ∀ (Γ : Ctx sig) (index : Nat) (bound : index < Γ.length),
    (varIdx (variableAt Γ index bound)).val = index
  | [], _, bound => absurd bound (Nat.not_lt_zero _)
  | .term :: _, 0, _ => rfl
  | _ :: Γ, index + 1, bound => by
      simp [variableAt, varIdx, varIdx_variableAt Γ index (Nat.lt_of_succ_lt_succ bound)]

/-- **Every sorted object pattern is an encoded term.**  The statement is for
open terms, since the body of an abstraction is open. -/
theorem exists_encode : ∀ (size : Nat) {Γ : Ctx sig} {pattern : Pattern},
    sizeOf pattern ≤ size →
    HasSort lambdaCalc FreeTypeContext.empty (boundTypes Γ) pattern "Term" →
    isObjectPattern pattern = true → pattern.hasCanonicalBinderMetadata = true →
      ∃ term : Term sig Γ .term, encodeTerm term = pattern
  | 0, _, pattern, bound, _, _, _ => by
      cases pattern <;> simp at bound
  | size + 1, Γ, pattern, bound, typed, object, canonical => by
      cases pattern with
      | bvar index =>
          have lookup := typed.bvar_inv
          have inBounds : index < Γ.length := by
            have := (List.getElem?_eq_some_iff.mp lookup).1
            simpa [boundTypes] using this
          exact ⟨.var (variableAt Γ index inBounds), by
            rw [encode_var, varIdx_variableAt]⟩
      | fvar label =>
          have lookup := typed.fvar_inv
          simp [FreeTypeContext.empty] at lookup
      | apply label arguments =>
          obtain ⟨rule, membership, sameLabel, -, -, argumentsTyped⟩ := typed.apply_inv
          have listed : rule ∈ [lambdaCalc.terms[0]'(by decide), lambdaCalc.terms[1]'(by decide)] :=
            membership
          simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
          rcases listed with rfl | rfl
          · obtain rfl : "App" = label := sameLabel
            cases argumentsTyped with
            | cons _ functionType functionTyped restTyped =>
                cases restTyped with
                | cons _ argumentType argumentTyped tailTyped =>
                    cases tailTyped
                    rename_i function argument
                    obtain rfl : TypeExpr.base "Term" = _ := Option.some.inj functionType
                    obtain rfl : TypeExpr.base "Term" = _ := Option.some.inj argumentType
                    simp only [isObjectPattern, isObjectPatternList, Bool.and_eq_true,
                      and_true] at object
                    simp only [Pattern.hasCanonicalBinderMetadata,
                      Pattern.hasCanonicalBinderMetadataList, Bool.and_eq_true, and_true]
                      at canonical
                    simp only [Pattern.apply.sizeOf_spec, List.cons.sizeOf_spec,
                      List.nil.sizeOf_spec] at bound
                    obtain ⟨functionTerm, functionEq⟩ :=
                      exists_encode size (by omega) functionTyped object.1 canonical.1
                    obtain ⟨argumentTerm, argumentEq⟩ :=
                      exists_encode size (by omega) argumentTyped object.2 canonical.2
                    exact ⟨appT functionTerm argumentTerm, by
                      rw [encode_app, functionEq, argumentEq]⟩
          · obtain rfl : "Lam" = label := sameLabel
            cases argumentsTyped with
            | cons representation abstractionType abstractionTyped tailTyped =>
                cases tailTyped
                rename_i abstraction
                obtain ⟨body, rfl⟩ :=
                  (matchesParameterRepresentation_abstractionNamed_iff _ _ _ _).mp
                    representation
                obtain rfl : TypeExpr.arrow (.base "Term") (.base "Term") = _ :=
                  Option.some.inj abstractionType
                obtain ⟨domain, codomain, arrow, bodyTyped⟩ := abstractionTyped.lambda_inv
                simp only [TypeExpr.arrow.injEq] at arrow
                obtain ⟨rfl, rfl⟩ := arrow
                simp only [isObjectPattern, isObjectPatternList, Bool.and_eq_true,
                  and_true] at object
                simp only [Pattern.hasCanonicalBinderMetadata,
                  Pattern.hasCanonicalBinderMetadataList, Option.isNone_none, Bool.true_and,
                  Bool.and_eq_true, and_true] at canonical
                simp only [Pattern.apply.sizeOf_spec, List.cons.sizeOf_spec,
                  List.nil.sizeOf_spec, Pattern.lambda.sizeOf_spec] at bound
                obtain ⟨bodyTerm, bodyEq⟩ :=
                  exists_encode size (Γ := .term :: Γ) (by omega) bodyTyped object canonical
                exact ⟨lamT bodyTerm, by rw [encode_lam, bodyEq]⟩
      | lambda binder body =>
          obtain ⟨_, _, arrow, -⟩ := typed.lambda_inv
          cases arrow
      | multiLambda arity binders body =>
          obtain ⟨_, _, arrow, -⟩ := typed.multiLambda_inv
          cases arrow
      | subst body replacement => simp [isObjectPattern] at object
      | collection collectionType elements rest =>
          obtain ⟨rule, membership, -, _, _, parameters, -⟩ := typed.collection_base_inv
          have listed : rule ∈ [lambdaCalc.terms[0]'(by decide), lambdaCalc.terms[1]'(by decide)] :=
            membership
          simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
          rcases listed with rfl | rfl <;> cases parameters

/-- The encoder is injective on closed terms. -/
theorem embed_injective : Function.Injective embed := fun first second same =>
  encode_injective first second (congrArg Subtype.val same)

/-- Every term of the interactive carrier is an encoded closed term. -/
theorem embed_surjective : Function.Surjective embed := by
  intro term
  obtain ⟨typed, -, canonical, object, -⟩ := term.2
  obtain ⟨preimage, encoded⟩ :=
    exists_encode (sizeOf term.1) (Γ := []) (Nat.le_refl _) typed object canonical
  exact ⟨preimage, Subtype.ext encoded⟩

/-- **Closed intrinsic terms are the terms of the interactive carrier.** -/
noncomputable def closedTerms : Term sig [] .term ≃ lambdaInteractivePresentation.Term :=
  Equiv.ofBijective embed ⟨embed_injective, embed_surjective⟩

/-- The intrinsic term of a term of the interactive carrier. -/
noncomputable def translate (term : lambdaInteractivePresentation.Term) : Term sig [] .term :=
  closedTerms.symm term

@[simp] theorem embed_translate (term : lambdaInteractivePresentation.Term) :
    embed (translate term) = term :=
  closedTerms.apply_symm_apply term

@[simp] theorem translate_embed (term : Term sig [] .term) : translate (embed term) = term :=
  closedTerms.symm_apply_apply term

theorem encode_translate (term : lambdaInteractivePresentation.Term) :
    encodeTerm (translate term) = term.1 :=
  congrArg Subtype.val (embed_translate term)

/-! ## The one rule of the interactive presentation -/

/-- The authored beta rule. -/
def betaRule : RewriteRule := lambdaCalc.rewrites[0]'(by decide)

theorem betaRule_left : betaRule.left =
    .apply "App" [.apply "Lam" [.lambda none (.fvar "body")], .fvar "arg"] := rfl

/-- What the left side of beta matches, and with which bindings. -/
theorem match_beta {source : Pattern} {bindings : Bindings}
    (matched : bindings ∈ matchPattern betaRule.left source) :
    ∃ binder body argument,
      source = .apply "App" [.apply "Lam" [.lambda binder body], argument] ∧
        bindings = [("arg", argument), ("body", body)] := by
  have relation := matchPattern_sound matched
  rw [betaRule_left] at relation
  cases relation
  rename_i arguments argumentsLength argumentsMatch
  cases argumentsMatch
  rename_i function functionBindings rest restBindings functionMatch restMatch merged
  cases restMatch
  rename_i argument argumentBindings tail tailBindings argumentMatch tailMatch mergedTail
  cases tailMatch
  cases argumentMatch
  cases functionMatch
  rename_i lamArguments lamLength lamMatch
  cases lamMatch
  rename_i abstraction abstractionBindings lamTail lamTailBindings abstractionMatch
    lamTailMatch lamMerged
  cases lamTailMatch
  cases abstractionMatch
  rename_i binder body bodyMatch
  cases bodyMatch
  simp [mergeBindings] at lamMerged mergedTail
  subst lamMerged
  subst mergedTail
  simp [mergeBindings] at merged
  subst merged
  exact ⟨_, _, _, rfl, rfl⟩

/-- The left side of beta matches every application of an abstraction. -/
theorem beta_matches (binder : Option String) (body argument : Pattern) :
    [("arg", argument), ("body", body)] ∈
      matchPattern betaRule.left
        (.apply "App" [.apply "Lam" [.lambda binder body], argument]) := by
  rw [betaRule_left]
  refine matchRel_complete (.apply (.cons (hb := [("body", body)])
    (tb := [("arg", argument)])
    (.apply (.cons (hb := [("body", body)]) (tb := []) (.lambda .fvar) .nil rfl) rfl)
    (.cons (hb := [("arg", argument)]) (tb := []) .fvar .nil rfl) ?_) rfl)
  simp [mergeBindings]

/-- The contractum of beta is binder elimination of the body at the
argument. -/
theorem apply_beta (body argument : Pattern) :
    applyBindingsForRule lambdaCalc betaRule [("arg", argument), ("body", body)] =
      instantiateBVar argument body := by
  rw [applyBindingsForRule_eq_syntactic]
  simp [applyRuleBindings, applyBindingsScoped, betaRule, lambdaCalc, captureDepth,
    captureDepthList, liftBVars_zero]

/-- **The reductions of the authored presentation.**  A pattern reduces
exactly when it is an abstraction applied to an argument, and its reduct is
the body with its binder eliminated at the argument. -/
theorem step_iff {source target : Pattern} :
    Step defaultBasePremises lambdaCalc source target ↔
      ∃ binder body argument,
        source = .apply "App" [.apply "Lam" [.lambda binder body], argument] ∧
          target = instantiateBVar argument body := by
  have noncontextual : ∀ rule, rule ∈ lambdaCalc.rewrites →
      NoncontextualPremises rule.premises := by
    intro rule membership
    obtain rfl : rule = betaRule := List.mem_singleton.mp membership
    exact .nil
  rw [show defaultBasePremises = engineBasePremises RelationEnv.empty from rfl,
    step_iff_rootStep_of_noncontextualRules noncontextual]
  constructor
  · rintro ⟨rule, membership, initial, matched, final, premises, targetEq⟩
    obtain rfl : rule = betaRule := List.mem_singleton.mp membership
    obtain rfl : final = initial := by
      simpa [betaRule, lambdaCalc, applyPremisesWithEnv] using premises
    obtain ⟨binder, body, argument, rfl, rfl⟩ := match_beta (by simpa using matched)
    exact ⟨binder, body, argument, rfl, by rw [← targetEq, apply_beta]⟩
  · rintro ⟨binder, body, argument, rfl, rfl⟩
    exact ⟨betaRule, List.mem_singleton.mpr rfl, _, by simpa using beta_matches binder body argument,
      _, by simp [betaRule, lambdaCalc, applyPremisesWithEnv], apply_beta body argument⟩

/-- With no equation, a step of the interactive theory is a reduction of the
authored presentation between its two terms. -/
theorem semantic_step_iff (source target : lambdaInteractivePresentation.Term) :
    lambdaIGSLT.toGSLT.Step source target ↔
      Step defaultBasePremises lambdaCalc source.1 target.1 := by
  have equality : ∀ left right : lambdaInteractivePresentation.Term,
      (presentedEquationSetoid defaultBasePremises lambdaInteractivePresentation).r
        left right ↔ left = right :=
    presentedEquationSetoid_iff_eq_of_no_generators defaultBasePremises
      lambdaInteractivePresentation (by rfl)
  constructor
  · rintro ⟨redex, contractum, sourceEq, primitive, targetEq⟩
    obtain rfl := (equality _ _).mp sourceEq
    obtain rfl := (equality _ _).mp targetEq
    exact primitive
  · intro primitive
    exact primitiveStep_to_presentedStep (presentation := lambdaInteractivePresentation)
      primitive

/-! ## The join -/

/-- A beta contraction at the root of a closed term. -/
def RootBeta (source target : Term sig [] .term) : Prop :=
  ∃ (body : Term sig [.term] .term) (argument : Term sig [] .term),
    source = appT (lamT body) argument ∧ target = inst body argument

/-- A term whose encoding is an abstraction applied to an argument is an
abstraction applied to an argument. -/
theorem encode_eq_redex {Γ : Ctx sig} {term : Term sig Γ .term} {binder : Option String}
    {body argument : Pattern}
    (encoded : encodeTerm term =
      .apply "App" [.apply "Lam" [.lambda binder body], argument]) :
    ∃ (bodyTerm : Term sig (.term :: Γ) .term) (argumentTerm : Term sig Γ .term),
      term = appT (lamT bodyTerm) argumentTerm ∧ encodeTerm bodyTerm = body ∧
        encodeTerm argumentTerm = argument := by
  match term, encoded with
  | .var _, encoded => simp [encodeTerm] at encoded
  | .op .lam (.cons _ .nil), encoded =>
      have shapes : Pattern.apply "Lam" _ = Pattern.apply "App" _ := encoded
      simp at shapes
  | .op .app (.cons function (.cons argumentTerm .nil)), encoded =>
      have shapes : Pattern.apply "App" [encodeTerm function, encodeTerm argumentTerm] =
          Pattern.apply "App" [.apply "Lam" [.lambda binder body], argument] := encoded
      simp only [Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at shapes
      obtain ⟨functionEq, argumentEq⟩ := shapes
      match function, functionEq with
      | .var _, functionEq => simp [encodeTerm] at functionEq
      | .op .app (.cons _ (.cons _ .nil)), functionEq =>
          have inner : Pattern.apply "App" _ = Pattern.apply "Lam" _ := functionEq
          simp at inner
      | .op .lam (.cons bodyTerm .nil), functionEq =>
          have inner : Pattern.apply "Lam" [.lambda none (encodeTerm bodyTerm)] =
              Pattern.apply "Lam" [.lambda binder body] := functionEq
          simp only [Pattern.apply.injEq, List.cons.injEq, Pattern.lambda.injEq, and_true,
            true_and] at inner
          exact ⟨bodyTerm, argumentTerm, rfl, inner.2, argumentEq⟩

/-- **The steps of the interactive theory are the root beta contractions of
closed terms.** -/
theorem step_iff_rootBeta (source target : lambdaInteractivePresentation.Term) :
    lambdaIGSLT.toGSLT.Step source target ↔ RootBeta (translate source) (translate target) := by
  rw [semantic_step_iff, step_iff]
  constructor
  · rintro ⟨binder, body, argument, sourceEq, targetEq⟩
    rw [← encode_translate source] at sourceEq
    obtain ⟨bodyTerm, argumentTerm, redex, rfl, rfl⟩ := encode_eq_redex sourceEq
    refine ⟨bodyTerm, argumentTerm, redex, ?_⟩
    apply encode_injective
    rw [encode_translate, targetEq]
    exact (LambdaPatternRendering.encode_inst bodyTerm argumentTerm).symm
  · rintro ⟨bodyTerm, argumentTerm, sourceEq, targetEq⟩
    refine ⟨none, encodeTerm bodyTerm, encodeTerm argumentTerm, ?_, ?_⟩
    · rw [← encode_translate source, sourceEq]
      rfl
    · rw [← encode_translate target, targetEq]
      exact LambdaPatternRendering.encode_inst bodyTerm argumentTerm

/-- **A step of the interactive theory is the beta event of the classifier.**
The firing of the contact-headed rule is sent to the classified beta event
on the translated terms. -/
theorem step_classified {source target : lambdaInteractivePresentation.Term}
    (step : lambdaIGSLT.toGSLT.Step source target) :
    ExtendedReduction rules eqs (translate source) (translate target) := by
  obtain ⟨body, argument, sourceEq, targetEq⟩ := (step_iff_rootBeta source target).mp step
  rw [sourceEq, targetEq]
  exact beta_classified body argument

/-- **What the classifier adds.**  A closed term has an event in the
classifier exactly when it steps in the interactive theory, or one of the
three congruence rules applies to an event of a part of it; the part of an
abstraction is open. -/
theorem classified_iff (source target : Term sig [] .term) :
    ExtendedReduction rules eqs source target ↔
      lambdaIGSLT.toGSLT.Step (embed source) (embed target) ∨
      (∃ function function' argument, source = appT function argument ∧
        target = appT function' argument ∧ ExtendedReduction rules eqs function function') ∨
      (∃ function argument argument', source = appT function argument ∧
        target = appT function argument' ∧ ExtendedReduction rules eqs argument argument') ∨
      (∃ body body' : Term sig [.term] .term, source = lamT body ∧ target = lamT body' ∧
        ExtendedReduction rules eqs body body') := by
  rw [step_iff_rootBeta, translate_embed, translate_embed]
  constructor
  · intro event
    cases (extension_iff_step source target).mp event with
    | beta body argument => exact .inl ⟨body, argument, rfl, rfl⟩
    | appCongL argument inner =>
        exact .inr (.inl ⟨_, _, argument, rfl, rfl, (extension_iff_step _ _).mpr inner⟩)
    | appCongR function inner =>
        exact .inr (.inr (.inl ⟨function, _, _, rfl, rfl, (extension_iff_step _ _).mpr inner⟩))
    | lamCong inner =>
        exact .inr (.inr (.inr ⟨_, _, rfl, rfl, (extension_iff_step _ _).mpr inner⟩))
  · rintro (⟨body, argument, rfl, rfl⟩ | ⟨function, function', argument, rfl, rfl, inner⟩ |
      ⟨function, argument, argument', rfl, rfl, inner⟩ | ⟨body, body', rfl, rfl, inner⟩)
    · exact beta_classified body argument
    · exact appCongL_classified argument inner
    · exact appCongR_classified function inner
    · exact lamCong_classified inner

/-! ## An instance and two controls -/

/-- The identity. -/
def identity : Term sig [] .term := lamT (.var .zero)

/-- The identity applied to itself steps in the interactive theory. -/
theorem identity_step :
    lambdaIGSLT.toGSLT.Step (embed (appT identity identity)) (embed identity) :=
  (step_iff_rootBeta _ _).mpr (by
    rw [translate_embed, translate_embed]
    exact ⟨.var .zero, identity, rfl, rfl⟩)

/-- The same contraction is an event of the classifier. -/
theorem identity_classified :
    ExtendedReduction rules eqs (appT identity identity) identity := by
  have event := step_classified identity_step
  rwa [translate_embed, translate_embed] at event

/-- `λx. (λy. y) x`: a redex beneath a binder. -/
def underBinder : Term sig [] .term := lamT (appT (lamT (.var .zero)) (.var .zero))

/-- **An event the interactive theory does not have: beneath a binder.**  The
classifier contracts the redex in the body by abstraction congruence; the
interactive theory has no step from this term at all. -/
theorem underBinder_classified_not_step :
    ExtendedReduction rules eqs underBinder identity ∧
      ∀ target, ¬ lambdaIGSLT.toGSLT.Step (embed underBinder) target := by
  refine ⟨lamCong_classified (beta_classified (.var .zero) (.var .zero)), ?_⟩
  intro target step
  obtain ⟨body, argument, sourceEq, -⟩ := (step_iff_rootBeta _ _).mp step
  rw [translate_embed] at sourceEq
  cases sourceEq

/-- `((λx. x) (λx. x)) (λx. x)`: a redex in function position. -/
def inFunction : Term sig [] .term := appT (appT identity identity) identity

/-- **An event the interactive theory does not have: in function position.**
The classifier contracts the function by left congruence; the interactive
theory has no step from this term, whose function is not an abstraction. -/
theorem inFunction_classified_not_step :
    ExtendedReduction rules eqs inFunction (appT identity identity) ∧
      ∀ target, ¬ lambdaIGSLT.toGSLT.Step (embed inFunction) target := by
  refine ⟨appCongL_classified identity identity_classified, ?_⟩
  intro target step
  obtain ⟨body, argument, sourceEq, -⟩ := (step_iff_rootBeta _ _).mp step
  rw [translate_embed] at sourceEq
  cases sourceEq

end Mettapedia.GSLT.LanguageDef.ClassifiedJoin.Lambda
