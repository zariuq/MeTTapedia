import Mettapedia.Languages.MM0.Upstream.Lean3Unfolding
import Mettapedia.Languages.MM0.Presentation.ConversionCorrespondence

/-!
# Curried and saturated MM0 conversion

`HistoricalConverts` adapts the four constructors of `conv'` at lines
188--201 of the pinned `mm0-lean/mm0/mm0.lean`. `SpecifiedConverts` retains
curried congruence, uses the specified fresh unfolding request, and includes
saturated transitivity explicitly supplied by `CTrans` / `VerifyConvTrans`
in `examples/mm0.mm0`, lines 288--361, at revision
`6d5f0d4fae8e2e3ae0b998bcbaa9d059cad99fad`:
https://github.com/digama0/mm0/blob/6d5f0d4fae8e2e3ae0b998bcbaa9d059cad99fad/examples/mm0.mm0

The displayed `VerifyConvUnfold` excludes capture by parameter images but
does not spell out dummy injectivity. Our unfolding clause retains the
already proved complete current C/Rust/kernel freshness profile, including
distinct dummy images. The transitivity and ordered-congruence clauses are
attributed to the example specification; full equality with its raw displayed
unfolding guard is not claimed.

This is an attributed relational adapter, not an executable checker. The
specified relation is not identified with the historical four-constructor
relation. Absence of a written transitivity constructor does not by itself
establish non-equivalence of the historical semantics.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Upstream.Lean3Conversion

open Lean3Typing Lean3Typing.Reference
open Mettapedia.GSLT.LanguageDef.DeterministicEquations (Applies computationalHost)

namespace Reference

/-- The pinned `sexpr.app'`, retaining source curried application order. -/
def applyArgs : SExpr → List SExpr → SExpr
  | function, [] => function
  | function, argument :: arguments => applyArgs (.app1 function argument) arguments

theorem applyArgs_append (function : SExpr) (first second : List SExpr) :
    applyArgs function (first ++ second) = applyArgs (applyArgs function first) second := by
  induction first generalizing function with
  | nil => rfl
  | cons argument arguments ih => exact ih _

theorem applyArgs_toKernel (function : SExpr) (arguments : List SExpr) :
    (applyArgs function arguments).toKernel =
      Kernel.Preterm.applyArgs function.toKernel (arguments.map SExpr.toKernel) := by
  induction arguments generalizing function with
  | nil => rfl
  | cons argument arguments ih => exact ih _

theorem applyArgs_ofKernel (function : Kernel.Preterm) (arguments : List Kernel.Preterm) :
    SExpr.ofKernel (Kernel.Preterm.applyArgs function arguments) =
      applyArgs (SExpr.ofKernel function) (arguments.map SExpr.ofKernel) := by
  induction arguments generalizing function with
  | nil => rfl
  | cons argument arguments ih => exact ih _

theorem typed_applyArgs_prefix {environment : Env} {context consumed remaining : Context}
    {function : SExpr} {arguments : List SExpr} {sort : Nat}
    (typed : Typed environment context function (consumed ++ remaining) sort)
    (fits : List.Forall₂ (FitsBinder environment context) arguments consumed) :
    Typed environment context (applyArgs function arguments) remaining sort := by
  induction fits generalizing function with
  | nil => exact typed
  | @cons argument binder arguments binders fits rest ih =>
      cases binder with
      | bound boundSort =>
          obtain ⟨index, rfl, lookup⟩ := fits
          exact ih (.appVar lookup typed)
      | reg argumentSort dependencies => exact ih (.appReg typed fits)

/-- A complete typed-spine decomposition, including variable expressions and
the exact consumed prefix of a term declaration. -/
theorem typed_spine (environment : Env) (context : Context) (expression : SExpr)
    (remaining : Context) (sort : Nat) :
    Typed environment context expression remaining sort ↔
      (∃ index binder, expression = .var index ∧ remaining = [] ∧
        context[index]? = some binder ∧ binder.sort = sort) ∨
      ∃ symbol formal returned body consumed arguments,
        GetTerm environment symbol formal returned body ∧
        formal = consumed ++ remaining ∧ returned.1 = sort ∧
        expression = applyArgs (.term symbol) arguments ∧
        List.Forall₂ (FitsBinder environment context) arguments consumed := by
  constructor
  · intro typed
    induction typed with
    | @var index binder lookup => exact .inl ⟨index, binder, rfl, rfl, lookup, rfl⟩
    | @term symbol formal returned body known =>
        exact .inr ⟨symbol, formal, returned, body, [], [], known, rfl, rfl, rfl, .nil⟩
    | @appVar function boundSort index result remaining lookup typed ih =>
        rcases ih with ⟨_, _, _, impossible, _⟩ | ⟨symbol, formal, returned, body, consumed,
          arguments, known, profile, resultSort, functionEq, fits⟩
        · cases impossible
        · refine .inr ⟨symbol, formal, returned, body, consumed ++ [.bound boundSort],
            arguments ++ [.var index], known, ?_, resultSort, ?_, ?_⟩
          · simpa only [List.append_assoc, List.singleton_append] using profile
          · rw [applyArgs_append]
            simpa only [applyArgs] using congrArg (fun f => SExpr.app1 f (.var index)) functionEq
          · exact List.rel_append fits (.cons ⟨index, rfl, lookup⟩ .nil)
    | @appReg function argument argumentSort result dependencies remaining typed argumentTyped ih _ =>
        rcases ih with ⟨_, _, _, impossible, _⟩ | ⟨symbol, formal, returned, body, consumed,
          arguments, known, profile, resultSort, functionEq, fits⟩
        · cases impossible
        · refine .inr ⟨symbol, formal, returned, body, consumed ++ [.reg argumentSort dependencies],
            arguments ++ [argument], known, ?_, resultSort, ?_, ?_⟩
          · simpa only [List.append_assoc, List.singleton_append] using profile
          · rw [applyArgs_append]
            simpa only [applyArgs] using congrArg (fun f => SExpr.app1 f argument) functionEq
          · exact List.rel_append fits (.cons argumentTyped .nil)
  · rintro (⟨index, binder, rfl, rfl, lookup, rfl⟩ |
      ⟨symbol, formal, returned, body, consumed, arguments, known, rfl, rfl, rfl, fits⟩)
    · exact .var lookup
    · exact typed_applyArgs_prefix (Typed.term known) fits

inductive HistoricalConverts (environment : Env) (context : Context) :
    SExpr → SExpr → Context → Nat → Prop where
  | refl {expression : SExpr} {remaining : Context} {sort : Nat} :
      Typed environment context expression remaining sort →
      HistoricalConverts environment context expression expression remaining sort
  | symm {left right : SExpr} {sort : Nat} :
      HistoricalConverts environment context left right [] sort →
      HistoricalConverts environment context right left [] sort
  | congruence {leftFunction rightFunction left right : SExpr} {binder : Binder}
      {remaining : Context} {sort : Nat} :
      FitsBinder environment context left binder → FitsBinder environment context right binder →
      HistoricalConverts environment context leftFunction rightFunction (binder :: remaining) sort →
      HistoricalConverts environment context left right [] binder.sort →
      HistoricalConverts environment context (.app1 leftFunction left) (.app1 rightFunction right) remaining sort
  | unfold {symbol : Nat} {formal : Context} {returned : DepType}
      {dummies images : List Nat} {body right : SExpr} {arguments : List SExpr} {sort : Nat} :
      GetTerm environment symbol formal returned (some (dummies, body)) →
      List.Forall₂ (FitsBinder environment context) arguments formal →
      Lean3Unfolding.Reference.dummySortImages context dummies images →
      HistoricalConverts environment context (applyArgs (.term symbol) arguments) right [] sort →
      HistoricalConverts environment context
        (Lean3Dependencies.Reference.substitute (arguments ++ images.map SExpr.var) body) right [] sort

/-- The current specified curried relation: explicit transitivity and complete
dummy freshness, retaining curried residual binders and argument order. -/
inductive SpecifiedConverts (environment : Env) (context : Context) :
    SExpr → SExpr → Context → Nat → Prop where
  | refl {expression : SExpr} {remaining : Context} {sort : Nat} :
      Typed environment context expression remaining sort →
      SpecifiedConverts environment context expression expression remaining sort
  | symm {left right : SExpr} {sort : Nat} :
      SpecifiedConverts environment context left right [] sort →
      SpecifiedConverts environment context right left [] sort
  | trans {left middle right : SExpr} {sort : Nat} :
      SpecifiedConverts environment context left middle [] sort →
      SpecifiedConverts environment context middle right [] sort →
      SpecifiedConverts environment context left right [] sort
  | congruence {leftFunction rightFunction left right : SExpr} {binder : Binder}
      {remaining : Context} {sort : Nat} :
      FitsBinder environment context left binder → FitsBinder environment context right binder →
      SpecifiedConverts environment context leftFunction rightFunction (binder :: remaining) sort →
      SpecifiedConverts environment context left right [] binder.sort →
      SpecifiedConverts environment context (.app1 leftFunction left) (.app1 rightFunction right) remaining sort
  | unfold {symbol : Nat} {arguments : List SExpr} {images : List Nat} {result right : SExpr} {sort : Nat} :
      Lean3Unfolding.Reference.specifiedUnfolds environment context symbol arguments images result →
      SpecifiedConverts environment context (applyArgs (.term symbol) arguments) right [] sort →
      SpecifiedConverts environment context result right [] sort

end Reference

private theorem args_refl {signature : Kernel.TermSignature}
    {definitions : Kernel.Definition.Signature} {context binders : Kernel.Context}
    {arguments : List Kernel.Preterm}
    (fits : List.Forall₂ (Kernel.Preterm.FitsBinder signature context) arguments binders) :
    Kernel.ConvertsArgs signature definitions context arguments arguments binders := by
  induction fits with
  | nil => exact .nil
  | cons fitted _ ih => exact .cons fitted fitted (.refl fitted.hasType) ih

private theorem args_append {signature : Kernel.TermSignature}
    {definitions : Kernel.Definition.Signature} {context first second : Kernel.Context}
    {left right leftTail rightTail : List Kernel.Preterm}
    (head : Kernel.ConvertsArgs signature definitions context left right first)
    (tail : Kernel.ConvertsArgs signature definitions context leftTail rightTail second) :
    Kernel.ConvertsArgs signature definitions context (left ++ leftTail) (right ++ rightTail)
      (first ++ second) := by
  induction first generalizing left right with
  | nil => cases head; exact tail
  | cons binder binders ih =>
      cases head with
      | cons leftFits rightFits converted rest =>
          exact .cons leftFits rightFits converted (ih rest)

/-- A partial curried derivation has one unchanged declared head, an exact
consumed argument prefix, and conversion evidence for that prefix. -/
private def SpineConverts (theory : Kernel.Theory) (context : Context)
    (left right : SExpr) (remaining : Context) (sort : Nat) : Prop :=
  (remaining = [] → Kernel.Converts theory.termSignature theory.definitionSignature
    (toContext context) left.toKernel right.toKernel sort) ∧
  (remaining ≠ [] → ∃ symbol declaration consumed leftArgs rightArgs,
    theory.termSignature symbol = some declaration ∧
    declaration.arguments = consumed ++ toContext remaining ∧ declaration.resultSort = sort ∧
    left.toKernel = Kernel.Preterm.applyArgs (.term symbol) leftArgs ∧
    right.toKernel = Kernel.Preterm.applyArgs (.term symbol) rightArgs ∧
    Kernel.ConvertsArgs theory.termSignature theory.definitionSignature
      (toContext context) leftArgs rightArgs consumed)

private theorem specified_spine {environment : Env} {theory : Kernel.Theory}
    (terms : EnvironmentRelated environment theory)
    (bodies : Lean3Unfolding.DefinitionsRelated environment theory)
    (valid : Kernel.Theory.WellFormed theory) {context remaining : Context}
    {left right : SExpr} {sort : Nat}
    (converted : Reference.SpecifiedConverts environment context left right remaining sort) :
    SpineConverts theory context left right remaining sort := by
  induction converted with
  | @refl expression remaining sort typed =>
      refine ⟨fun empty => ?_, fun nonempty => ?_⟩
      · subst remaining
        exact .refl (typed_toKernel terms typed)
      · rcases (Reference.typed_spine _ _ _ _ _).mp typed with
          ⟨_, _, _, empty, _⟩ | ⟨symbol, formal, returned, body, consumed, arguments,
            known, profile, returnedSort, same, fitted⟩
        · exact False.elim (nonempty empty)
        · subst expression
          refine ⟨symbol, termDecl formal returned, toContext consumed,
            arguments.map SExpr.toKernel, arguments.map SExpr.toKernel,
            (terms.terms _ _ _).mp ⟨body, known⟩, ?_, returnedSort, ?_, ?_,
            args_refl (Lean3Dependencies.fitsList_toKernel terms context fitted)⟩
          · simpa only [termDecl, toContext, List.map_append] using congrArg toContext profile
          · exact Reference.applyArgs_toKernel _ _
          · exact Reference.applyArgs_toKernel _ _
  | symm _ ih => exact ⟨fun _ => .symm (ih.1 rfl), fun impossible => False.elim (impossible rfl)⟩
  | trans _ _ ihFirst ihSecond =>
      exact ⟨fun _ => .trans (ihFirst.1 rfl) (ihSecond.1 rfl),
        fun impossible => False.elim (impossible rfl)⟩
  | @congruence leftFunction rightFunction left right binder remaining sort
      leftFits rightFits _ _ ihFunction ihArgument =>
      obtain ⟨symbol, declaration, consumed, leftArgs, rightArgs,
        declared, profile, returnedSort, leftEq, rightEq, children⟩ :=
        ihFunction.2 (List.cons_ne_nil _ _)
      have child : Kernel.Converts theory.termSignature theory.definitionSignature
          (toContext context) left.toKernel right.toKernel binder.toKernel.sort := by
        simpa only [Binder.sort_toKernel] using ihArgument.1 rfl
      have appended := args_append children
        (Kernel.ConvertsArgs.cons ((fitsBinder_iff terms _ _ _).mp leftFits)
          ((fitsBinder_iff terms _ _ _).mp rightFits) child .nil)
      have leftApp : (SExpr.app1 leftFunction left).toKernel =
          Kernel.Preterm.applyArgs (.term symbol) (leftArgs ++ [left.toKernel]) := by
        rw [Kernel.Preterm.applyArgs_append]
        simpa only [SExpr.toKernel, Kernel.Preterm.applyArgs] using
          congrArg (fun f => Kernel.Preterm.app f left.toKernel) leftEq
      have rightApp : (SExpr.app1 rightFunction right).toKernel =
          Kernel.Preterm.applyArgs (.term symbol) (rightArgs ++ [right.toKernel]) := by
        rw [Kernel.Preterm.applyArgs_append]
        simpa only [SExpr.toKernel, Kernel.Preterm.applyArgs] using
          congrArg (fun f => Kernel.Preterm.app f right.toKernel) rightEq
      refine ⟨fun empty => ?_, fun _ => ?_⟩
      · subst remaining
        rw [leftApp, rightApp, ← returnedSort]
        apply Kernel.Converts.congruence declared
        simpa only [profile, toContext, List.map_cons, List.map_nil, List.append_nil] using appended
      · refine ⟨symbol, declaration, consumed ++ [binder.toKernel],
          leftArgs ++ [left.toKernel], rightArgs ++ [right.toKernel],
          declared, ?_, returnedSort, leftApp, rightApp, appended⟩
        simpa only [toContext, List.map_cons, List.append_assoc, List.singleton_append] using profile
  | @unfold symbol arguments images result right sort requested _ ih =>
      have unfolded : Kernel.Definition.Unfolds theory.termSignature theory.definitionSignature
          (toContext context) symbol (arguments.map SExpr.toKernel) images result.toKernel := by
        apply (Lean3Unfolding.specified_unfolds_iff terms bodies valid _ _ _ _ _).mp
        simpa only [ofContext_toContext, List.map_map, Function.comp_def,
          SExpr.ofKernel_toKernel, List.map_id'] using requested
      cases unfolded with
      | @intro declaration body result declared stored fitted fresh substituted =>
          obtain ⟨storedDeclaration, lookup, admitted⟩ := valid.definitions _ _ stored
          have same := Option.some.inj (lookup.symm.trans declared)
          subst storedDeclaration
          have resultTyped := admitted.typed.substitute (fresh.typed_substitution fitted) substituted
          have callTyped := (Kernel.Preterm.HasType.term declared).applyArgs fitted
          have inner := ih.1 rfl
          have sortEq := (callTyped.deterministic (by
            simpa only [Reference.applyArgs_toKernel, SExpr.toKernel] using inner.typed.1)).2
          refine ⟨fun _ => ?_, fun impossible => False.elim (impossible rfl)⟩
          have unfolded : Kernel.Converts theory.termSignature theory.definitionSignature
              (toContext context)
              (Kernel.Preterm.applyArgs (.term symbol) (arguments.map SExpr.toKernel)) result.toKernel
              declaration.resultSort := .unfold declared
                (.intro declared stored fitted fresh substituted) resultTyped
          rw [sortEq] at unfolded
          exact .trans (.symm unfolded) (by
            simpa only [Reference.applyArgs_toKernel, SExpr.toKernel] using inner)

/-- Saturated curried conversion preserves the independent current judgment.
Partial functions are handled by the consumed-prefix invariant, not silently
treated as saturated terms. -/
theorem specified_toKernel {environment : Env} {theory : Kernel.Theory}
    (terms : EnvironmentRelated environment theory)
    (bodies : Lean3Unfolding.DefinitionsRelated environment theory)
    (valid : Kernel.Theory.WellFormed theory) {context : Context}
    {left right : SExpr} {sort : Nat}
    (converted : Reference.SpecifiedConverts environment context left right [] sort) :
    Kernel.Converts theory.termSignature theory.definitionSignature (toContext context)
      left.toKernel right.toKernel sort :=
  (specified_spine terms bodies valid converted).1 rfl

/-- Ordered saturated congruence reflects to one curried application step for
each declared binder. Unfolding uses the exact admitted body and supplied
dummy images. -/
theorem specified_ofKernel {environment : Env} {theory : Kernel.Theory}
    (terms : EnvironmentRelated environment theory)
    (bodies : Lean3Unfolding.DefinitionsRelated environment theory)
    (valid : Kernel.Theory.WellFormed theory) {context : Kernel.Context}
    {left right : Kernel.Preterm} {sort : Nat}
    (converted : Kernel.Converts theory.termSignature theory.definitionSignature
      context left right sort) :
    Reference.SpecifiedConverts environment (ofContext context)
      (SExpr.ofKernel left) (SExpr.ofKernel right) [] sort := by
  induction converted using Kernel.Converts.rec
      (motive_2 := fun left right binders _ =>
        ∀ (leftFunction rightFunction : SExpr) (remaining : Context) (sort : Nat),
          Reference.SpecifiedConverts environment (ofContext context) leftFunction rightFunction
            (ofContext binders ++ remaining) sort →
          Reference.SpecifiedConverts environment (ofContext context)
            (Reference.applyArgs leftFunction (left.map SExpr.ofKernel))
            (Reference.applyArgs rightFunction (right.map SExpr.ofKernel)) remaining sort) with
  | refl typed => exact .refl (by simpa only [ofContext, List.map_nil] using typed_ofKernel terms typed)
  | symm _ ih => exact .symm ih
  | trans _ _ ihFirst ihSecond => exact .trans ihFirst ihSecond
  | @congruence symbol declaration left right lookup _ ih =>
      obtain ⟨body, known⟩ := (terms.terms symbol (ofContext declaration.arguments)
        (declaration.resultSort, declaration.dependencies)).mpr (by
          simpa only [termDecl_ofKernel] using lookup)
      have head : Reference.SpecifiedConverts environment (ofContext context)
          (.term symbol) (.term symbol) (ofContext declaration.arguments ++ []) declaration.resultSort :=
        .refl (by simpa only [List.append_nil] using Reference.Typed.term known)
      simpa only [Reference.applyArgs_ofKernel, SExpr.ofKernel] using ih _ _ [] _ head
  | @unfold symbol declaration arguments images result lookup unfolded typed =>
      have requested := (Lean3Unfolding.specified_unfolds_iff terms bodies valid context
        symbol arguments images result).mpr unfolded
      have fitted : List.Forall₂ (Kernel.Preterm.FitsBinder theory.termSignature context)
          arguments declaration.arguments := by
        cases unfolded with
        | intro declared _ fitted _ _ =>
            have same := Option.some.inj (lookup.symm.trans declared)
            subst declaration
            exact fitted
      have call : Reference.Typed environment (ofContext context)
          (Reference.applyArgs (.term symbol) (arguments.map SExpr.ofKernel)) [] declaration.resultSort := by
        simpa only [Reference.applyArgs_ofKernel, SExpr.ofKernel, ofContext, List.map_nil] using
          typed_ofKernel terms ((Kernel.Preterm.HasType.term lookup).applyArgs fitted)
      simpa only [Reference.applyArgs_ofKernel, SExpr.ofKernel] using
        Reference.SpecifiedConverts.symm (Reference.SpecifiedConverts.unfold requested (.refl call))
  | nil =>
      rename_i leftFunction rightFunction remaining resultSort converted
      exact converted
  | @cons left right lefts rights binder binders leftFits rightFits _ _ ihChild ihTail =>
      rename_i leftFunction rightFunction remaining resultSort functionConverted
      have child : Reference.SpecifiedConverts environment (ofContext context)
          (SExpr.ofKernel left) (SExpr.ofKernel right) [] (Binder.ofKernel binder).sort := by
        simpa only [Binder.sort_ofKernel] using ihChild
      have stepped := Reference.SpecifiedConverts.congruence
        (fitsBinder_ofKernel terms leftFits) (fitsBinder_ofKernel terms rightFits)
        (by simpa only [ofContext, List.map_cons, List.cons_append] using functionConverted) child
      exact ihTail _ _ _ _ stepped

theorem specified_iff {environment : Env} {theory : Kernel.Theory}
    (terms : EnvironmentRelated environment theory)
    (bodies : Lean3Unfolding.DefinitionsRelated environment theory)
    (valid : Kernel.Theory.WellFormed theory) (context : Kernel.Context)
    (left right : Kernel.Preterm) (sort : Nat) :
    Reference.SpecifiedConverts environment (ofContext context)
      (SExpr.ofKernel left) (SExpr.ofKernel right) [] sort ↔
      Kernel.Converts theory.termSignature theory.definitionSignature context left right sort := by
  constructor
  · intro converted
    simpa only [toContext_ofContext, SExpr.toKernel_ofKernel] using
      specified_toKernel terms bodies valid converted
  · exact specified_ofKernel terms bodies valid

theorem checked_run_conversion_iff {theory : Kernel.Theory} {admissions : List Kernel.Admission}
    (checked : Kernel.Theory.run? {} admissions = some theory) (context : Kernel.Context)
    (left right : Kernel.Preterm) (sort : Nat) :
    Reference.SpecifiedConverts (projectRun admissions) (ofContext context)
      (SExpr.ofKernel left) (SExpr.ofKernel right) [] sort ↔
      Kernel.Converts theory.termSignature theory.definitionSignature context left right sort :=
  specified_iff (checked_run_environment_related checked)
    (Lean3Unfolding.checked_run_definitions_related checked)
    (Kernel.Theory.run_from_empty_wellFormed checked) context left right sort

/-- A particular accepted authored witness implies specified conversion. The
converse for this unindexed source judgment quantifies a supplied witness. -/
theorem checked_run_authored_conversion {theory : Kernel.Theory} {admissions : List Kernel.Admission}
    (checked : Kernel.Theory.run? {} admissions = some theory) {context : Kernel.Context}
    {witness : Kernel.ConvWitness} {left right : Kernel.Preterm} {sort : Nat}
    (accepted : Applies Presentation.ComputationalConversion.conversionProgram
      Mettapedia.GSLT.LanguageDef.DeterministicEquations.dataEqualityHost "mm0:conversion"
      [Presentation.ComputationalTyping.encodeTable theory.terms,
        Presentation.ComputationalDefinitions.encodeDefinitions theory.definitions,
        Presentation.ComputationalContext.encodeContext context,
        Presentation.ComputationalConversion.encodeWitness witness]
      (Presentation.ComputationalConversion.encodeConversion (some ⟨left, right, sort⟩))) :
    Reference.SpecifiedConverts (projectRun admissions) (ofContext context)
      (SExpr.ofKernel left) (SExpr.ofKernel right) [] sort :=
  (checked_run_conversion_iff checked _ _ _ _).mpr
    ((Presentation.ComputationalConversion.theory_conversion_accepts_iff _ _ _ _ _ _).mp accepted).derives

theorem checked_run_conversion_iff_authored {theory : Kernel.Theory} {admissions : List Kernel.Admission}
    (checked : Kernel.Theory.run? {} admissions = some theory) (context : Kernel.Context)
    (left right : Kernel.Preterm) (sort : Nat) :
    Reference.SpecifiedConverts (projectRun admissions) (ofContext context)
      (SExpr.ofKernel left) (SExpr.ofKernel right) [] sort ↔
      ∃ witness, Applies Presentation.ComputationalConversion.conversionProgram
        Mettapedia.GSLT.LanguageDef.DeterministicEquations.dataEqualityHost "mm0:conversion"
        [Presentation.ComputationalTyping.encodeTable theory.terms,
          Presentation.ComputationalDefinitions.encodeDefinitions theory.definitions,
          Presentation.ComputationalContext.encodeContext context,
          Presentation.ComputationalConversion.encodeWitness witness]
        (Presentation.ComputationalConversion.encodeConversion (some ⟨left, right, sort⟩)) := by
  rw [checked_run_conversion_iff checked]
  simpa only [Presentation.ComputationalTyping.theory_signature,
    Presentation.ComputationalDefinitions.theory_definitions] using
    Presentation.ComputationalConversion.converts_iff_authored theory.terms theory.definitions
      context left right sort

namespace Controls

open Kernel

private def history : List Admission := [
  .sort 0 {}, .sort 1 { provable := true }, .term 0 ⟨[], 1, ∅⟩,
  .term 1 ⟨[.bound 0, .regular 1 {0}], 1, ∅⟩,
  .definition 2 ⟨[], 1, ∅⟩ ⟨[], .term 0⟩]
private def theory : Theory := history.foldl (fun state declaration => declaration.insert state) {}
private def target : Kernel.Context := [.bound 0]
private def left : Preterm := .app (.app (.term 1) (.var 0)) (.term 2)
private def right : Preterm := .app (.app (.term 1) (.var 0)) (.term 0)
private def witness : ConvWitness := .congruence 1 [.refl (.var 0), .unfold 2 [] []]

theorem actual_declarations_are_checked : Theory.run? {} history = some theory := by
  apply (Theory.run_eq_some_iff _ _ _).mpr
  refine .cons (.intro ((Admission.check_iff _ _).mp ?_))
    (.cons (.intro ((Admission.check_iff _ _).mp ?_))
      (.cons (.intro ((Admission.check_iff _ _).mp ?_))
        (.cons (.intro ((Admission.check_iff _ _).mp ?_))
          (.cons (.intro ((Admission.check_iff _ _).mp ?_)) (.nil _)))))
  all_goals decide +kernel

private theorem witness_checked : ConvWitness.Checks theory.termSignature theory.definitionSignature
    target witness left right 1 := (ConvWitness.check_iff _ _ _ _ _ _ _).mp (by decide +kernel)

theorem ordered_curried_congruence_with_unfolding :
    Reference.SpecifiedConverts (projectRun history) (ofContext target)
      (SExpr.ofKernel left) (SExpr.ofKernel right) [] 1 :=
  (checked_run_conversion_iff actual_declarations_are_checked _ _ _ _).mpr witness_checked.derives

theorem partial_application_retains_its_next_binder :
    Typed (projectRun history) (ofContext target)
      (.app1 (.term 1) (.var 0)) [.reg 1 {0}] 1 := by
  apply (checked_run_typing_iff actual_declarations_are_checked target [.regular 1 {0}]
    (.app (.term 1) (.var 0)) 1).mpr
  exact (Preterm.infer_eq_some_iff _ _ _ _ _).mp (by decide +kernel)

theorem partial_spine_retains_consumed_bound_argument :
    ∃ body, GetTerm (projectRun history) 1 [.bound 0, .reg 1 {0}] (1, ∅) body ∧
      Reference.applyArgs (.term 1) [.var 0] = .app1 (.term 1) (.var 0) ∧
      List.Forall₂ (FitsBinder (projectRun history) (ofContext target)) [.var 0] [.bound 0] := by
  refine ⟨none, .term (by simp [projectRun, projectAdmission, history, ofContext, Binder.ofKernel]), rfl, ?_⟩
  exact .cons ⟨0, rfl, rfl⟩ .nil

theorem explicit_saturated_transitivity :
    Reference.SpecifiedConverts (projectRun history) (ofContext target)
      (.term 2) (.term 0) [] 1 := by
  apply (checked_run_conversion_iff actual_declarations_are_checked target (.term 2) (.term 0) 1).mpr
  apply ConvWitness.check_sound (witness := .trans (.unfold 2 [] []) (.refl (.term 0)))
  decide +kernel

theorem conversion_reflects_every_ordered_child :
    ∃ checkedWitness, Applies Presentation.ComputationalConversion.conversionProgram
      Mettapedia.GSLT.LanguageDef.DeterministicEquations.dataEqualityHost "mm0:conversion"
      [Presentation.ComputationalTyping.encodeTable theory.terms,
        Presentation.ComputationalDefinitions.encodeDefinitions theory.definitions,
        Presentation.ComputationalContext.encodeContext target,
        Presentation.ComputationalConversion.encodeWitness checkedWitness]
      (Presentation.ComputationalConversion.encodeConversion (some ⟨left, right, 1⟩)) :=
  (checked_run_conversion_iff_authored actual_declarations_are_checked _ _ _ _).mp
    ordered_curried_congruence_with_unfolding

theorem wrong_bound_operand_cannot_convert :
    ¬ Reference.SpecifiedConverts (projectRun history) (ofContext target)
      (.app1 (.app1 (.term 1) (.term 0)) (.term 0)) (SExpr.ofKernel right) [] 1 := by
  intro converted
  have typed := ((checked_run_conversion_iff actual_declarations_are_checked target
    (.app (.app (.term 1) (.term 0)) (.term 0)) right 1).mp converted).typed.1
  have computed := typed.eval
  have refused : Preterm.infer theory.termSignature target
      (.app (.app (.term 1) (.term 0)) (.term 0)) = none := by decide +kernel
  rw [refused] at computed
  contradiction

theorem reversed_argument_witness_is_refused :
    ConvWitness.conversion? theory.termSignature theory.definitionSignature target
      (.congruence 1 [.unfold 2 [] [], .refl (.var 0)]) = none := by decide +kernel

theorem mismatched_transitivity_witness_is_refused :
    ConvWitness.conversion? theory.termSignature theory.definitionSignature target
      (.trans (.unfold 2 [] []) (.refl (.term 2))) = none := by decide +kernel

theorem wrong_claimed_endpoint_is_refused :
    ¬ ConvWitness.Checks theory.termSignature theory.definitionSignature target witness left (.term 0) 1 := by
  intro bad
  have same := Option.some.inj (bad.eval.symm.trans witness_checked.eval)
  have wrong : (.term 0 : Preterm) ≠ right := by decide
  exact wrong (congrArg ConversionResult.right same)

theorem prior_theory_cannot_supply_the_definition :
    ConvWitness.conversion? ({} : Theory).termSignature ({} : Theory).definitionSignature target
      (.unfold 2 [] []) = none := by decide +kernel

end Controls

end Mettapedia.Languages.MM0.Upstream.Lean3Conversion
