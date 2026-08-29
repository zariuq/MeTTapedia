import Mettapedia.Languages.MeTTa.Pure.Intrinsic.RegularSubjectReduction

/-!
# Executable bidirectional checking for the regular Pure kernel

Synthesis and checking below consume the exact accessibility normalizer.  The
returned typing derivations are theorem-layer fields and erase; ordinary
execution supplies only a context, term, and (for checking) expected type.
-/

namespace Mettapedia.Languages.MeTTa.Pure.Intrinsic.PresentationBoundary

open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Syntax
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Context
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Renaming
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Reduction

/-- Stable, formation-directed failure classes for the intrinsic checker. -/
inductive RegularCheckError where
  | declarationConstant
  | upperSortHasNoType
  | lambdaNeedsFunctionType
  | pairNeedsPairType
  | expectedFunctionType
  | expectedPairType
  | expectedFormedType
  | typeMismatch
  deriving DecidableEq, Repr

/-- A synthesized result is either the distinguished top sort or an ordinary
formed type.  This is the executable checker's presupposition invariant. -/
inductive RegularTypeStatus (Γ : Ctx n) : PureTm n → Type where
  | top : type = .u1 → RegularTypeStatus Γ type
  | formed : RegularHasType Γ type .u1 → RegularTypeStatus Γ type

namespace RegularTypeStatus

/-- Every classified result type lies in the exact normalization domain. -/
def covered {Γ : Ctx n} {type : PureTm n} (context : RegularCtx Γ)
    (status : RegularTypeStatus Γ type) :
    regularNormalizationSpecification.Domain type := by
  cases status with
  | top equal =>
      subst type
      exact regularNormalizationSpecification.covers_u1 n
  | formed typing =>
      exact regularNormalizationSpecification.covers_subject
        ⟨context, typing⟩

/-- Normalization preserves the result-type classification. -/
def normalized {Γ : Ctx n} {type : PureTm n}
    (context : RegularCtx Γ) (status : RegularTypeStatus Γ type) :
    RegularTypeStatus Γ
      (regularNormalizationSpecification.normalize type
        (status.covered context)) := by
  cases status with
  | top equal =>
      subst type
      apply RegularTypeStatus.top
      exact (u1_redNormal n).redStar_eq
        (regularNormalizationSpecification.reduces .u1
          (RegularTypeStatus.covered context (RegularTypeStatus.top rfl)))
  | formed typing =>
      exact RegularTypeStatus.formed (typing.subject_reduction_star context
        (regularNormalizationSpecification.reduces type
          (RegularTypeStatus.covered context
            (RegularTypeStatus.formed typing))))

end RegularTypeStatus

/-- Synthesis returns a type, its regular derivation, and formation status. -/
structure RegularInferred {Γ : Ctx n} (term : PureTm n) where
  type : PureTm n
  typing : RegularHasType Γ term type
  status : RegularTypeStatus Γ type

/-- Checking returns exactly the requested regular typing judgment. -/
structure RegularChecked {Γ : Ctx n} (term expected : PureTm n) where
  accepted : Unit := ()
  typing : RegularHasType Γ term expected

/-- Exact conversion recognition through the P1 `DecidedRelation`.  The public
result is only a Boolean; the correctness theorem reconstructs proof evidence
inside the theorem layer. -/
def decideRegularConversion {Γ : Ctx n} {left right : PureTm n}
    (context : RegularCtx Γ)
    (leftStatus : RegularTypeStatus Γ left)
    (rightStatus : RegularTypeStatus Γ right) : Bool :=
  let leftTerm : RegularNormalizationTerm n :=
    ⟨left, leftStatus.covered context⟩
  let rightTerm : RegularNormalizationTerm n :=
    ⟨right, rightStatus.covered context⟩
  (regularDecidedConversion n).decide leftTerm rightTerm

theorem decideRegularConversion_correct {Γ : Ctx n}
    {left right : PureTm n} (context : RegularCtx Γ)
    (leftStatus : RegularTypeStatus Γ left)
    (rightStatus : RegularTypeStatus Γ right) :
    decideRegularConversion context leftStatus rightStatus = true ↔
      ConstantFreeConv left right := by
  exact regularDecidedConversion_correct
    ⟨left, leftStatus.covered context⟩
    ⟨right, rightStatus.covered context⟩

/-- Exact conversion accepts reflexivity without evaluating the proof-dependent
normalizer inside the kernel. -/
theorem decideRegularConversion_refl {Γ : Ctx n} {type : PureTm n}
    (context : RegularCtx Γ) (leftStatus rightStatus : RegularTypeStatus Γ type) :
    decideRegularConversion context leftStatus rightStatus = true := by
  apply (decideRegularConversion_correct context leftStatus rightStatus).2
  exact ConstantFreeConv.refl type
    (regularNormalizationSpecification.fragment type
      (leftStatus.covered context))

/-- A normalized dependent-function view carries the formation evidence needed
by every elimination rule. -/
structure RegularPiView {Γ : Ctx n} (type : PureTm n) where
  dom : PureTm n
  cod : PureTm (n + 1)
  conversion : ConstantFreeConv type (.pi dom cod)
  normal : RedNormal (.pi dom cod)
  domFormed : RegularHasType Γ dom .u1
  codFormed : RegularHasType (.snoc Γ dom) cod .u1

/-- A normalized dependent-pair view carries the same presuppositions. -/
structure RegularSigmaView {Γ : Ctx n} (type : PureTm n) where
  dom : PureTm n
  cod : PureTm (n + 1)
  conversion : ConstantFreeConv type (.sigma dom cod)
  normal : RedNormal (.sigma dom cod)
  domFormed : RegularHasType Γ dom .u1
  codFormed : RegularHasType (.snoc Γ dom) cod .u1

/-- Reduction cannot change a dependent-function head into another term
constructor. -/
theorem redStar_pi_shape {dom : PureTm n} {cod : PureTm (n + 1)}
    {target : PureTm n} (steps : RedStar (.pi dom cod) target) :
    ∃ dom' cod', target = .pi dom' cod' := by
  induction steps with
  | refl => exact ⟨dom, cod, rfl⟩
  | tail earlier finalStep ih =>
      rcases ih with ⟨dom', cod', rfl⟩
      cases finalStep with
      | congPiDom _ => exact ⟨_, _, rfl⟩
      | congPiCod _ => exact ⟨_, _, rfl⟩

/-- Reduction cannot change a dependent-pair head into another term
constructor. -/
theorem redStar_sigma_shape {dom : PureTm n} {cod : PureTm (n + 1)}
    {target : PureTm n} (steps : RedStar (.sigma dom cod) target) :
    ∃ dom' cod', target = .sigma dom' cod' := by
  induction steps with
  | refl => exact ⟨dom, cod, rfl⟩
  | tail earlier finalStep ih =>
      rcases ih with ⟨dom', cod', rfl⟩
      cases finalStep with
      | congSigmaDom _ => exact ⟨_, _, rfl⟩
      | congSigmaCod _ => exact ⟨_, _, rfl⟩

/-- Inspect the exact normal form of a classified type as a dependent function. -/
def regularPiView? {Γ : Ctx n} {type : PureTm n}
    (context : RegularCtx Γ) (status : RegularTypeStatus Γ type) :
    Option (RegularPiView (Γ := Γ) type) :=
  let covered := status.covered context
  let normal := regularNormalizationSpecification.normalize type covered
  let steps := regularNormalizationSpecification.reduces type covered
  let conversion :=
    (regularNormalizationSpecification.fragment type covered).redStar steps |>.1
  match head : normal with
  | .pi dom cod =>
      match status.normalized context with
      | .top equal =>
          False.elim (by
            have impossible : (.pi dom cod : PureTm n) = .u1 :=
              head.symm.trans equal
            cases impossible)
      | .formed typing =>
          let components := typing.pi_components_formed head
          some
            { dom := dom
              cod := cod
              conversion := head ▸ conversion
              normal := head ▸
                regularNormalizationSpecification.irreducible type covered
              domFormed := components.1
              codFormed := components.2 }
  | _ => none

/-- Inspect the exact normal form of a classified type as a dependent pair. -/
def regularSigmaView? {Γ : Ctx n} {type : PureTm n}
    (context : RegularCtx Γ) (status : RegularTypeStatus Γ type) :
    Option (RegularSigmaView (Γ := Γ) type) :=
  let covered := status.covered context
  let normal := regularNormalizationSpecification.normalize type covered
  let steps := regularNormalizationSpecification.reduces type covered
  let conversion :=
    (regularNormalizationSpecification.fragment type covered).redStar steps |>.1
  match head : normal with
  | .sigma dom cod =>
      match status.normalized context with
      | .top equal =>
          False.elim (by
            have impossible : (.sigma dom cod : PureTm n) = .u1 :=
              head.symm.trans equal
            cases impossible)
      | .formed typing =>
          let components := typing.sigma_components_formed head
          some
            { dom := dom
              cod := cod
              conversion := head ▸ conversion
              normal := head ▸
                regularNormalizationSpecification.irreducible type covered
              domFormed := components.1
              codFormed := components.2 }
  | _ => none

/-- A formed dependent-function type is always recognized after exact
normalization. -/
theorem regularPiView?_complete {Γ : Ctx n} {dom : PureTm n}
    {cod : PureTm (n + 1)} (context : RegularCtx Γ)
    (formed : RegularHasType Γ (.pi dom cod) .u1) :
    ∃ view, regularPiView? context (.formed formed) = some view := by
  unfold regularPiView?
  dsimp only [RegularTypeStatus.normalized]
  split
  · exact ⟨_, rfl⟩
  · rename_i notPi
    have steps := regularNormalizationSpecification.reduces (.pi dom cod)
      (RegularTypeStatus.covered context (.formed formed))
    rcases redStar_pi_shape steps with ⟨dom', cod', head⟩
    exact False.elim (notPi dom' cod' head)

/-- A formed dependent-pair type is always recognized after exact
normalization. -/
theorem regularSigmaView?_complete {Γ : Ctx n} {dom : PureTm n}
    {cod : PureTm (n + 1)} (context : RegularCtx Γ)
    (formed : RegularHasType Γ (.sigma dom cod) .u1) :
    ∃ view, regularSigmaView? context (.formed formed) = some view := by
  unfold regularSigmaView?
  dsimp only [RegularTypeStatus.normalized]
  split
  · exact ⟨_, rfl⟩
  · rename_i notSigma
    have steps := regularNormalizationSpecification.reduces (.sigma dom cod)
      (RegularTypeStatus.covered context (.formed formed))
    rcases redStar_sigma_shape steps with ⟨dom', cod', head⟩
    exact False.elim (notSigma dom' cod' head)

/-- Reclassify a synthesized type code as a formed type. -/
def RegularInferred.asFormedType?
    {Γ : Ctx n} {term : PureTm n} (context : RegularCtx Γ)
    (inferred : RegularInferred (Γ := Γ) term) :
    Except RegularCheckError (PLift (RegularHasType Γ term .u1)) :=
  if accepted : decideRegularConversion context inferred.status (.top rfl) = true then
    pure ⟨.conv_sort inferred.typing
      ((decideRegularConversion_correct context inferred.status (.top rfl)).1
        accepted)⟩
  else
    throw .expectedFormedType

/-- Extract the presupposition attached to a synthesized ordinary result. -/
def RegularInferred.resultFormed?
    {Γ : Ctx n} {term : PureTm n}
    (inferred : RegularInferred (Γ := Γ) term) :
    Except RegularCheckError
      (PLift (RegularHasType Γ inferred.type .u1)) :=
  match inferred.status with
  | .formed formed => pure ⟨formed⟩
  | .top _ => throw .expectedFormedType

/-- Whenever the synthesized result type is semantically formed, its runtime
classification must be the ordinary `formed` branch and extraction succeeds. -/
theorem RegularInferred.resultFormed?_complete
    {Γ : Ctx n} {term : PureTm n}
    (inferred : RegularInferred (Γ := Γ) term)
    (formed : RegularHasType Γ inferred.type .u1) :
    ∃ lifted, inferred.resultFormed? = .ok lifted := by
  cases statusEq : inferred.status with
  | formed statusFormed =>
      exact ⟨⟨statusFormed⟩, by
        simp only [RegularInferred.resultFormed?, statusEq]
        rfl⟩
  | top equal =>
      have impossible : False := by
        apply formed.subject_ne_u1
        exact equal
      exact False.elim impossible

mutual

/-- Synthesize a regular type.  Lambdas and pairs are checking forms; their
direct beta application is the one synthesis exception needed for ordinary
programs. -/
def inferRegularType : {n : Nat} → {Γ : Ctx n} →
    (context : RegularCtx Γ) → (term : PureTm n) →
    Except RegularCheckError (RegularInferred (Γ := Γ) term)
  | _, Γ, context, .var index =>
      pure
        { type := lookup Γ index
          typing := .var index
          status := .formed (context.lookup_formed index) }
  | _, _, _, .const _ => throw .declarationConstant
  | _, Γ, _, .u0 =>
      pure { type := .u1, typing := .u0_type Γ, status := .top rfl }
  | _, _, _, .u1 => throw .upperSortHasNoType
  | _, Γ, context, .pi dom cod => do
      let domInfo <- inferRegularType context dom
      let domFormed <- domInfo.asFormedType? context
      let extended : RegularCtx (.snoc Γ dom) := .snoc context domFormed.down
      let codInfo <- inferRegularType extended cod
      let codFormed <- codInfo.asFormedType? extended
      pure
        { type := .u1
          typing := .pi_form domFormed.down codFormed.down
          status := .top rfl }
  | _, Γ, context, .sigma dom cod => do
      let domInfo <- inferRegularType context dom
      let domFormed <- domInfo.asFormedType? context
      let extended : RegularCtx (.snoc Γ dom) := .snoc context domFormed.down
      let codInfo <- inferRegularType extended cod
      let codFormed <- codInfo.asFormedType? extended
      pure
        { type := .u1
          typing := .sigma_form domFormed.down codFormed.down
          status := .top rfl }
  | _, Γ, context, .id carrier left right => do
      let carrierInfo <- inferRegularType context carrier
      let carrierFormed <- carrierInfo.asFormedType? context
      let leftChecked <- checkRegularFormed context left carrier carrierFormed.down
      let rightChecked <- checkRegularFormed context right carrier carrierFormed.down
      pure
        { type := .u1
          typing := .id_form carrierFormed.down
            leftChecked.typing rightChecked.typing
          status := .top rfl }
  | _, _, _, .lam _ => throw .lambdaNeedsFunctionType
  | _, Γ, context, .app (.lam body) argument => do
      let argumentInfo <- inferRegularType context argument
      let domainFormed <- argumentInfo.resultFormed?
      let extended : RegularCtx (.snoc Γ argumentInfo.type) :=
        .snoc context domainFormed.down
      let bodyInfo <- inferRegularType extended body
      let codomainFormed <- bodyInfo.resultFormed?
      let resultFormed := codomainFormed.down.instantiate
        argumentInfo.typing context.constantFreeCtx
      pure
        { type := inst0 argument bodyInfo.type
          typing := .app_elim domainFormed.down
            (.lam_intro domainFormed.down codomainFormed.down bodyInfo.typing)
            argumentInfo.typing codomainFormed.down
          status := .formed resultFormed }
  | _, _, context, .app function argument => do
      let functionInfo <- inferRegularType context function
      match regularPiView? context functionInfo.status with
      | none => throw .expectedFunctionType
      | some view =>
          let functionTyping := RegularHasType.conv_type
            functionInfo.typing (.pi_form view.domFormed view.codFormed)
            view.conversion
          let argumentChecked <-
            checkRegularFormed context argument view.dom view.domFormed
          let resultFormed := view.codFormed.instantiate
            argumentChecked.typing context.constantFreeCtx
          pure
            { type := inst0 argument view.cod
              typing := .app_elim view.domFormed functionTyping
                argumentChecked.typing view.codFormed
              status := .formed resultFormed }
  | _, _, _, .pair _ _ => throw .pairNeedsPairType
  | _, _, context, .fst pair => do
      let pairInfo <- inferRegularType context pair
      match regularSigmaView? context pairInfo.status with
      | none => throw .expectedPairType
      | some view =>
          let pairTyping := RegularHasType.conv_type pairInfo.typing
            (.sigma_form view.domFormed view.codFormed) view.conversion
          pure
            { type := view.dom
              typing := .fst_elim view.domFormed pairTyping view.codFormed
              status := .formed view.domFormed }
  | _, _, context, .snd pair => do
      let pairInfo <- inferRegularType context pair
      match regularSigmaView? context pairInfo.status with
      | none => throw .expectedPairType
      | some view =>
          let pairTyping := RegularHasType.conv_type pairInfo.typing
            (.sigma_form view.domFormed view.codFormed) view.conversion
          let firstTyping :=
            RegularHasType.fst_elim view.domFormed pairTyping view.codFormed
          let resultFormed := view.codFormed.instantiate firstTyping
            context.constantFreeCtx
          pure
            { type := inst0 (.fst pair) view.cod
              typing := .snd_elim view.domFormed pairTyping view.codFormed
              status := .formed resultFormed }
  | _, _, context, .refl term => do
      let termInfo <- inferRegularType context term
      let carrierFormed <- termInfo.resultFormed?
      pure
        { type := .id termInfo.type term term
          typing := .refl_intro carrierFormed.down termInfo.typing
          status := .formed (.id_form carrierFormed.down
            termInfo.typing termInfo.typing) }
termination_by _ _ _ term => 2 * sizeOf term
decreasing_by
  all_goals simp_wf <;> omega

/-- Check against an already-formed ordinary type. -/
def checkRegularFormed : {n : Nat} → {Γ : Ctx n} →
    (context : RegularCtx Γ) → (term expected : PureTm n) →
    (expectedFormed : RegularHasType Γ expected .u1) →
    Except RegularCheckError (RegularChecked (Γ := Γ) term expected)
  | _, Γ, context, .lam body, expected, expectedFormed =>
      match regularPiView? context (.formed expectedFormed) with
      | none => throw .lambdaNeedsFunctionType
      | some view => do
          let extended : RegularCtx (.snoc Γ view.dom) :=
            .snoc context view.domFormed
          let bodyChecked <- checkRegularFormed extended body view.cod
            view.codFormed
          let lambdaTyping := RegularHasType.lam_intro
            view.domFormed view.codFormed bodyChecked.typing
          pure { typing :=
            (RegularHasType.conv_type lambdaTyping expectedFormed
              view.conversion.symm) }
  | _, Γ, context, .pair first second, expected, expectedFormed =>
      match regularSigmaView? context (.formed expectedFormed) with
      | none => throw .pairNeedsPairType
      | some view => do
          let firstChecked <- checkRegularFormed context first view.dom
            view.domFormed
          let secondExpected := inst0 first view.cod
          let secondExpectedFormed := view.codFormed.instantiate
            firstChecked.typing context.constantFreeCtx
          let secondChecked <- checkRegularFormed context second secondExpected
            secondExpectedFormed
          let pairTyping := RegularHasType.pair_intro view.domFormed
            firstChecked.typing secondChecked.typing view.codFormed
          pure { typing :=
            (RegularHasType.conv_type pairTyping expectedFormed
              view.conversion.symm) }
  | _, _, context, term, expected, expectedFormed => do
      let inferred <- inferRegularType context term
      if accepted : decideRegularConversion context inferred.status
          (.formed expectedFormed) = true then
        let conversion :=
          (decideRegularConversion_correct context inferred.status
            (.formed expectedFormed)).1 accepted
        pure { typing := .conv_type inferred.typing expectedFormed conversion }
      else
        throw .typeMismatch
termination_by _ _ _ term _ _ => 2 * sizeOf term + 1
decreasing_by
  all_goals simp_wf <;> omega

end

/-- Check a term against the distinguished top sort. -/
def checkRegularTop {Γ : Ctx n} (context : RegularCtx Γ) (term : PureTm n) :
    Except RegularCheckError (RegularChecked (Γ := Γ) term .u1) := do
  let inferred <- inferRegularType context term
  if accepted : decideRegularConversion context inferred.status (.top rfl) = true then
    let conversion :=
      (decideRegularConversion_correct context inferred.status (.top rfl)).1 accepted
    pure { typing := .conv_sort inferred.typing conversion }
  else
    throw .typeMismatch

/-- Public bidirectional checking: formation of an ordinary expected type is
itself synthesized before the term is checked.  `U1` uses its distinguished
sort boundary. -/
def checkRegularType {Γ : Ctx n} (context : RegularCtx Γ)
    (term expected : PureTm n) :
    Except RegularCheckError (RegularChecked (Γ := Γ) term expected) :=
  if top : expected = .u1 then
    top ▸ checkRegularTop context term
  else do
    let expectedInfo <- inferRegularType context expected
    let expectedFormed <- expectedInfo.asFormedType? context
    checkRegularFormed context term expected expectedFormed.down

/-- The certificate-free publication bit for a regular typing query. -/
def regularCheckBool {Γ : Ctx n} (context : RegularCtx Γ)
    (term expected : PureTm n) : Bool :=
  (checkRegularType context term expected).isOk

/-- Soundness of the executable publication bit.  The accepted branch yields
the requested intrinsic derivation; rejection carries no proof object. -/
theorem regularCheckBool_sound {Γ : Ctx n} (context : RegularCtx Γ)
    (term expected : PureTm n)
    (accepted : regularCheckBool context term expected = true) :
    RegularHasType Γ term expected := by
  unfold regularCheckBool at accepted
  cases computed : checkRegularType context term expected with
  | error failure =>
      rw [computed] at accepted
      change false = true at accepted
      cases accepted
  | ok checked => exact checked.typing

/-! ## Completeness infrastructure and executable witnesses -/

/-- Once synthesis has produced a type, exact conversion makes the ordinary
checking branch complete for any convertible formed expectation. -/
theorem checkRegularFormed_of_inferred {Γ : Ctx n}
    (context : RegularCtx Γ) {term expected : PureTm n}
    (expectedFormed : RegularHasType Γ expected .u1)
    (notLambda : ∀ body, term = .lam body → False)
    (notPair : ∀ first second, term = .pair first second → False)
    (inferred : RegularInferred (Γ := Γ) term)
    (computed : inferRegularType context term = .ok inferred)
    (conversion : ConstantFreeConv inferred.type expected) :
    ∃ checked,
      checkRegularFormed context term expected expectedFormed = .ok checked := by
  rw [checkRegularFormed.eq_3 _ _ _ _ _ _ notLambda notPair]
  rw [computed]
  dsimp [Bind.bind, Except.instMonad, Except.bind]
  have accepted : decideRegularConversion context inferred.status
      (.formed expectedFormed) = true :=
    (decideRegularConversion_correct context inferred.status
      (.formed expectedFormed)).2 conversion
  rw [dif_pos accepted]
  exact ⟨_, rfl⟩

/-- The intrinsic variable package is computed directly from regular context
lookup. -/
def regularVariableInfo {Γ : Ctx n} (context : RegularCtx Γ)
    (index : Fin n) : RegularInferred (Γ := Γ) (.var index) where
  type := lookup Γ index
  typing := .var index
  status := .formed (context.lookup_formed index)

theorem inferRegular_variable {Γ : Ctx n} (context : RegularCtx Γ)
    (index : Fin n) :
    inferRegularType context (.var index) =
      .ok (regularVariableInfo context index) := by
  rw [inferRegularType.eq_1]
  rfl

/-- Variables check against every convertible formed expectation. -/
theorem checkRegular_variable {Γ : Ctx n} (context : RegularCtx Γ)
    (index : Fin n) {expected : PureTm n}
    (expectedFormed : RegularHasType Γ expected .u1)
    (conversion : ConstantFreeConv (lookup Γ index) expected) :
    ∃ checked, checkRegularFormed context (.var index) expected
      expectedFormed = .ok checked :=
  checkRegularFormed_of_inferred context expectedFormed
    (by simp) (by simp) (regularVariableInfo context index)
    (inferRegular_variable context index) conversion

/-- The untyped self-application is rejected before the checker can fabricate
a type for its lambda argument. -/
theorem inferRegular_omega_rejects :
    inferRegularType RegularCtx.nil regularOmega =
      .error .lambdaNeedsFunctionType := by
  rw [show regularOmega = .app (.lam regularOmegaBody) regularDelta from rfl]
  rw [inferRegularType.eq_9]
  simp only [regularDelta, inferRegularType.eq_8]
  rfl

/-- Formation fails immediately when a dependent-function domain is the
untyped upper sort. -/
theorem inferRegular_malformed_domain_rejects :
    inferRegularType RegularCtx.nil (.pi .u1 .u0) =
      .error .upperSortHasNoType := by
  rw [inferRegularType.eq_5, inferRegularType.eq_4]
  rfl

/-- Formation also rejects an upper-sort codomain after accepting the lower
universe domain. -/
theorem inferRegular_malformed_codomain_rejects :
    inferRegularType RegularCtx.nil (.pi .u0 .u1) =
      .error .upperSortHasNoType := by
  rw [inferRegularType.eq_5, inferRegularType.eq_3]
  dsimp [Pure.pure, Bind.bind, Except.instMonad, Except.pure, Except.bind,
    RegularInferred.asFormedType?]
  rw [dif_pos (decideRegularConversion_refl RegularCtx.nil _ _)]
  dsimp [Pure.pure, Bind.bind, Except.instMonad, Except.pure, Except.bind]
  rw [inferRegularType.eq_4]
  rfl

/-- The two universe constructors are not convertible. -/
theorem regular_u1_not_conv_u0 :
    ¬ ConstantFreeConv (.u1 : PureTm n) .u0 := by
  intro conversion
  have equal : (.u1 : PureTm n) = .u0 := normalForms_eq_of_conv
    (.refl _) (.refl _) (u1_redNormal n) (u0_redNormal n)
    conversion.toConv
  cases equal

theorem decideRegularConversion_u1_u0_false {Γ : Ctx n}
    (context : RegularCtx Γ)
    (formed : RegularHasType Γ (.u0 : PureTm n) .u1) :
    decideRegularConversion context (.top rfl) (.formed formed) = false := by
  apply Bool.eq_false_of_not_eq_true
  intro accepted
  exact regular_u1_not_conv_u0
    ((decideRegularConversion_correct context (.top rfl)
      (.formed formed)).1 accepted)

/-- Negative conversion witness: `U0` synthesizes `U1`, so asking the checker
to assign it type `U0` is rejected by exact conversion. -/
theorem checkRegular_conversion_rejects :
    checkRegularType RegularCtx.nil .u0 .u0 = .error .typeMismatch := by
  unfold checkRegularType
  rw [dif_neg (by simp), inferRegularType.eq_3]
  dsimp [Pure.pure, Bind.bind, Except.instMonad, Except.pure, Except.bind,
    RegularInferred.asFormedType?]
  rw [dif_pos (decideRegularConversion_refl RegularCtx.nil _ _)]
  dsimp [Pure.pure, Bind.bind, Except.instMonad, Except.pure, Except.bind]
  rw [checkRegularFormed.eq_3 _ _ _ _ _ _ (by simp) (by simp)]
  rw [inferRegularType.eq_3]
  dsimp [Pure.pure, Bind.bind, Except.instMonad, Except.pure, Except.bind]
  rw [dif_neg (by simp [decideRegularConversion_u1_u0_false
    RegularCtx.nil (.u0_type .nil)])]
  rfl

/-- The synthesized package for the ordinary polymorphic-looking identity
type in the two-universe regular fragment. -/
def regularIdentityTypeInfo :
    RegularInferred (Γ := (.nil : Ctx 0)) (.pi .u0 .u0) where
  type := .u1
  typing := .pi_form (.u0_type .nil) (.u0_type _)
  status := .top rfl

/-- The corresponding dependent-pair type package in any regular context. -/
def regularPairTypeInfo {Γ : Ctx n} (_context : RegularCtx Γ) :
    RegularInferred (Γ := Γ) (.sigma .u0 .u0) where
  type := .u1
  typing := .sigma_form (.u0_type Γ) (.u0_type _)
  status := .top rfl

/-- Formation of the identity's dependent-function type is executable. -/
theorem inferRegular_identity_type :
    inferRegularType RegularCtx.nil (.pi .u0 .u0) =
      .ok regularIdentityTypeInfo := by
  rw [inferRegularType.eq_5, inferRegularType.eq_3]
  dsimp [Pure.pure, Bind.bind, Except.instMonad, Except.pure, Except.bind,
    RegularInferred.asFormedType?]
  rw [dif_pos (decideRegularConversion_refl RegularCtx.nil _ _)]
  dsimp [Pure.pure, Bind.bind, Except.instMonad, Except.pure, Except.bind]
  rw [inferRegularType.eq_3]
  dsimp [Pure.pure, Bind.bind, Except.instMonad, Except.pure, Except.bind,
    RegularInferred.asFormedType?]
  rw [dif_pos (decideRegularConversion_refl
    (.snoc RegularCtx.nil (.u0_type .nil)) _ _)]
  rfl

/-- Formation of the dependent-pair example is executable in every regular
context. -/
theorem inferRegular_pair_type {Γ : Ctx n} (context : RegularCtx Γ) :
    inferRegularType context (.sigma .u0 .u0) =
      .ok (regularPairTypeInfo context) := by
  rw [inferRegularType.eq_6, inferRegularType.eq_3]
  dsimp [Pure.pure, Bind.bind, Except.instMonad, Except.pure, Except.bind,
    RegularInferred.asFormedType?]
  rw [dif_pos (decideRegularConversion_refl context _ _)]
  dsimp [Pure.pure, Bind.bind, Except.instMonad, Except.pure, Except.bind]
  rw [inferRegularType.eq_3]
  dsimp [Pure.pure, Bind.bind, Except.instMonad, Except.pure, Except.bind,
    RegularInferred.asFormedType?]
  rw [dif_pos (decideRegularConversion_refl
    (.snoc context (.u0_type Γ)) _ _)]
  rfl

/-- Positive checking witness for the dependent-function introduction path. -/
theorem checkRegular_identity_formed :
    ∃ checked, checkRegularFormed RegularCtx.nil (.lam (.var 0))
      (.pi .u0 .u0) (.pi_form (.u0_type .nil) (.u0_type _)) = .ok checked := by
  let expectedFormed : RegularHasType (.nil : Ctx 0) (.pi .u0 .u0) .u1 :=
    .pi_form (.u0_type .nil) (.u0_type _)
  rcases regularPiView?_complete RegularCtx.nil expectedFormed with
    ⟨view, viewEq⟩
  rw [checkRegularFormed.eq_1, viewEq]
  dsimp only
  let extended : RegularCtx (.snoc (.nil : Ctx 0) view.dom) :=
    .snoc .nil view.domFormed
  let inferred :
      RegularInferred (Γ := .snoc (.nil : Ctx 0) view.dom) (.var 0) :=
    { type := lookup (.snoc (.nil : Ctx 0) view.dom) 0
      typing := .var 0
      status := .formed (extended.lookup_formed 0) }
  have inferredEq : inferRegularType extended (.var 0) = .ok inferred :=
    inferRegularType.eq_1 _ _ _ _
  have components := view.conversion.pi_injective
  have bodyConversion : ConstantFreeConv
      (lookup (.snoc (.nil : Ctx 0) view.dom) 0) view.cod := by
    simpa [lookup_snoc_zero] using
      (ConstantFreeConv.trans (components.1.rename wk).symm components.2)
  rcases checkRegularFormed_of_inferred extended view.codFormed
      (by simp) (by simp) inferred inferredEq bodyConversion with
    ⟨checked, checkedEq⟩
  rw [checkedEq]
  exact ⟨_, rfl⟩

/-- Positive checking witness for dependent-pair introduction.  The example
uses an actual term variable, so both components exercise conversion under a
formed context rather than succeeding vacuously. -/
theorem checkRegular_pair_formed :
    ∃ checked, checkRegularFormed regularCtx_u0
      (.pair (.var 0) (.var 0)) (.sigma .u0 .u0)
      (.sigma_form (.u0_type _) (.u0_type _)) = .ok checked := by
  let expectedFormed : RegularHasType (.snoc .nil .u0 : Ctx 1)
      (.sigma .u0 .u0) .u1 := .sigma_form (.u0_type _) (.u0_type _)
  rcases regularSigmaView?_complete regularCtx_u0 expectedFormed with
    ⟨view, viewEq⟩
  rw [checkRegularFormed.eq_2, viewEq]
  dsimp only
  have components := view.conversion.sigma_injective
  have firstConversion : ConstantFreeConv
      (lookup (.snoc .nil .u0 : Ctx 1) 0) view.dom := by
    simpa [lookup_snoc_zero, rename] using components.1
  rcases checkRegular_variable regularCtx_u0 0 view.domFormed
      firstConversion with ⟨firstChecked, firstEq⟩
  rw [firstEq]
  dsimp [Pure.pure, Bind.bind, Except.instMonad, Except.pure, Except.bind]
  have secondConversion : ConstantFreeConv
      (lookup (.snoc .nil .u0 : Ctx 1) 0) (inst0 (.var 0) view.cod) := by
    simpa [lookup_snoc_zero, rename, inst0, subst, subst0] using
      (components.2.inst0_body (ConstantFree.var (0 : Fin 1)))
  rcases checkRegular_variable regularCtx_u0 0 _ secondConversion with
    ⟨secondChecked, secondEq⟩
  rw [secondEq]
  exact ⟨_, rfl⟩

/-- Public positive witness: ordinary checking of the identity requires only
the context, term, and expected type. -/
theorem checkRegular_identity_accepts :
    (checkRegularType RegularCtx.nil (.lam (.var 0))
      (.pi .u0 .u0)).isOk = true := by
  unfold checkRegularType
  rw [dif_neg (by simp), inferRegular_identity_type]
  dsimp [regularIdentityTypeInfo, Pure.pure, Bind.bind, Except.instMonad,
    Except.pure, Except.bind, RegularInferred.asFormedType?]
  rw [dif_pos (decideRegularConversion_refl RegularCtx.nil _ _)]
  dsimp [Pure.pure, Bind.bind, Except.instMonad, Except.pure, Except.bind]
  rcases checkRegular_identity_formed with ⟨checked, checkedEq⟩
  rw [show checkRegularFormed RegularCtx.nil (.lam (.var 0))
      (.pi .u0 .u0) _ = .ok checked by simpa only using checkedEq]
  rfl

/-- Public positive witness for dependent-pair checking. -/
theorem checkRegular_pair_accepts :
    (checkRegularType regularCtx_u0 (.pair (.var 0) (.var 0))
      (.sigma .u0 .u0)).isOk = true := by
  unfold checkRegularType
  rw [dif_neg (by simp), inferRegular_pair_type regularCtx_u0]
  dsimp [regularPairTypeInfo, Pure.pure, Bind.bind, Except.instMonad,
    Except.pure, Except.bind, RegularInferred.asFormedType?]
  rw [dif_pos (decideRegularConversion_refl regularCtx_u0 _ _)]
  dsimp [Pure.pure, Bind.bind, Except.instMonad, Except.pure, Except.bind]
  rcases checkRegular_pair_formed with ⟨checked, checkedEq⟩
  rw [show checkRegularFormed regularCtx_u0 (.pair (.var 0) (.var 0))
      (.sigma .u0 .u0) _ = .ok checked by simpa only using checkedEq]
  rfl

/-- Positive synthesis witness for identity-type formation over an actual
inhabitant of the lower universe. -/
theorem inferRegular_id_accepts :
    ∃ inferred, inferRegularType regularCtx_u0
      (.id .u0 (.var 0) (.var 0)) = .ok inferred := by
  rw [inferRegularType.eq_7, inferRegularType.eq_3]
  dsimp [Pure.pure, Bind.bind, Except.instMonad, Except.pure, Except.bind,
    RegularInferred.asFormedType?]
  rw [dif_pos (decideRegularConversion_refl regularCtx_u0 _ _)]
  dsimp [Pure.pure, Bind.bind, Except.instMonad, Except.pure, Except.bind]
  have conversion : ConstantFreeConv
      (lookup (.snoc .nil .u0 : Ctx 1) 0) (.u0 : PureTm 1) := by
    simpa [lookup_snoc_zero, rename] using
      (ConstantFreeConv.refl (.u0 : PureTm 1) .u0)
  rcases checkRegular_variable regularCtx_u0 0 (.u0_type _) conversion with
    ⟨checked, checkedEq⟩
  rw [show checkRegularFormed regularCtx_u0 (.var 0) .u0 _ = .ok checked by
    simpa only using checkedEq]
  exact ⟨_, rfl⟩

/-- Positive synthesis witness for direct dependent application. -/
theorem inferRegular_application_accepts :
    ∃ inferred, inferRegularType regularCtx_u0
      (.app (.lam (.var 0)) (.var 0)) = .ok inferred := by
  rw [inferRegularType.eq_9, inferRegular_variable regularCtx_u0 0]
  dsimp [regularVariableInfo, RegularInferred.resultFormed?, Pure.pure,
    Bind.bind, Except.instMonad, Except.pure, Except.bind]
  rw [inferRegularType.eq_1]
  dsimp [RegularInferred.resultFormed?, Pure.pure, Bind.bind,
    Except.instMonad, Except.pure, Except.bind]
  exact ⟨_, rfl⟩

/-- A regular context containing one dependent pair, used to exercise both
projection eliminators. -/
def regularPairContext : Ctx 1 :=
  .snoc .nil (.sigma .u0 .u0)

def regularPairContext_formed : RegularCtx regularPairContext :=
  .snoc .nil (.sigma_form (.u0_type .nil) (.u0_type _))

/-- The newest variable in `regularPairContext` has the pair type explicitly,
which avoids hiding the projection test behind a lookup abbreviation. -/
def regularPairVariableInfo :
    RegularInferred (Γ := regularPairContext) (.var 0) where
  type := .sigma .u0 .u0
  typing := by
    simpa [regularPairContext, lookup_snoc_zero, rename] using
      (RegularHasType.var (Γ := regularPairContext) (i := (0 : Fin 1)))
  status := .formed (.sigma_form (.u0_type _) (.u0_type _))

theorem inferRegular_pair_variable :
    inferRegularType regularPairContext_formed (.var 0) =
      .ok regularPairVariableInfo := by
  rw [inferRegularType.eq_1]
  rfl

/-- Positive synthesis witness for first projection. -/
theorem inferRegular_fst_accepts :
    ∃ inferred, inferRegularType regularPairContext_formed (.fst (.var 0)) =
      .ok inferred := by
  rw [inferRegularType.eq_12, inferRegular_pair_variable]
  dsimp [Pure.pure, Bind.bind, Except.instMonad, Except.pure, Except.bind,
    regularPairVariableInfo]
  rcases regularSigmaView?_complete regularPairContext_formed
      (.sigma_form (.u0_type _) (.u0_type _)) with ⟨view, viewEq⟩
  rw [viewEq]
  exact ⟨_, rfl⟩

/-- Positive synthesis witness for dependent second projection. -/
theorem inferRegular_snd_accepts :
    ∃ inferred, inferRegularType regularPairContext_formed (.snd (.var 0)) =
      .ok inferred := by
  rw [inferRegularType.eq_13, inferRegular_pair_variable]
  dsimp [Pure.pure, Bind.bind, Except.instMonad, Except.pure, Except.bind,
    regularPairVariableInfo]
  rcases regularSigmaView?_complete regularPairContext_formed
      (.sigma_form (.u0_type _) (.u0_type _)) with ⟨view, viewEq⟩
  rw [viewEq]
  exact ⟨_, rfl⟩

/-! ## Axiom audit -/

#print axioms decideRegularConversion_correct
#print axioms redStar_pi_shape
#print axioms redStar_sigma_shape
#print axioms regularPiView?_complete
#print axioms regularSigmaView?_complete
#print axioms regularCheckBool_sound
#print axioms checkRegular_identity_accepts
#print axioms checkRegular_pair_accepts
#print axioms inferRegular_id_accepts
#print axioms inferRegular_application_accepts
#print axioms inferRegular_fst_accepts
#print axioms inferRegular_snd_accepts
#print axioms inferRegular_malformed_domain_rejects
#print axioms inferRegular_malformed_codomain_rejects
#print axioms checkRegular_conversion_rejects
#print axioms inferRegular_omega_rejects

end Mettapedia.Languages.MeTTa.Pure.Intrinsic.PresentationBoundary
