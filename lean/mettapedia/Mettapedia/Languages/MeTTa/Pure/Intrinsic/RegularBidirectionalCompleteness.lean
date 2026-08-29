import Mettapedia.Languages.MeTTa.Pure.Intrinsic.RegularBidirectional

/-!
# Independent bidirectional specification and checker completeness

This file states the regular kernel's bidirectional fragment independently of
the executable checker.  Introduction forms check against canonical heads;
elimination forms synthesize through canonical heads.  Canonicality is fixed
by the exact normalizer rather than by a syntactic-normal-form restriction.
-/

namespace Mettapedia.Languages.MeTTa.Pure.Intrinsic.PresentationBoundary

open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Syntax
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Context
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Renaming
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Reduction

/-- The executable view recovers the components selected by an independently
stated canonical view. -/
theorem regularPiView?_of_canonical {Γ : Ctx n} {type : PureTm n}
    (context : RegularCtx Γ) (formed : RegularHasType Γ type .u1)
    (canonical : RegularPiView (Γ := Γ) type) :
    ∃ view, regularPiView? context (.formed formed) = some view ∧
      view.dom = canonical.dom ∧ view.cod = canonical.cod := by
  let covered := (RegularTypeStatus.formed formed).covered context
  have normalizes : regularNormalizationSpecification.normalize type covered =
      .pi canonical.dom canonical.cod :=
    normalForms_eq_of_conv
      (regularNormalizationSpecification.reduces type covered) (.refl _)
      (regularNormalizationSpecification.irreducible type covered)
      canonical.normal canonical.conversion.toConv
  unfold regularPiView?
  dsimp only [RegularTypeStatus.normalized]
  split
  · rename_i dom cod head
    have components := PureTm.pi.inj (head.symm.trans normalizes)
    exact ⟨_, rfl, components.1, components.2⟩
  · rename_i notPi
    exact False.elim (notPi canonical.dom canonical.cod normalizes)

/-- Pair-head recovery is exact for the same reason. -/
theorem regularSigmaView?_of_canonical {Γ : Ctx n} {type : PureTm n}
    (context : RegularCtx Γ) (formed : RegularHasType Γ type .u1)
    (canonical : RegularSigmaView (Γ := Γ) type) :
    ∃ view, regularSigmaView? context (.formed formed) = some view ∧
      view.dom = canonical.dom ∧ view.cod = canonical.cod := by
  let covered := (RegularTypeStatus.formed formed).covered context
  have normalizes : regularNormalizationSpecification.normalize type covered =
      .sigma canonical.dom canonical.cod :=
    normalForms_eq_of_conv
      (regularNormalizationSpecification.reduces type covered) (.refl _)
      (regularNormalizationSpecification.irreducible type covered)
      canonical.normal canonical.conversion.toConv
  unfold regularSigmaView?
  dsimp only [RegularTypeStatus.normalized]
  split
  · rename_i dom cod head
    have components := PureTm.sigma.inj (head.symm.trans normalizes)
    exact ⟨_, rfl, components.1, components.2⟩
  · rename_i notSigma
    exact False.elim
      (notSigma canonical.dom canonical.cod normalizes)

/-- A synthesized function whose type has a canonical Pi view cannot inhabit
the distinguished top-sort branch; type presupposition therefore yields an
ordinary formed source type. -/
theorem RegularPiView.sourceFormed {Γ : Ctx n} {term type : PureTm n}
    (context : RegularCtx Γ) (view : RegularPiView (Γ := Γ) type)
    (typing : RegularHasType Γ term type) : RegularHasType Γ type .u1 := by
  rcases typing.type_presupposed context with top | formed
  · have impossible : (.u1 : PureTm n) = .pi view.dom view.cod :=
      normalForms_eq_of_conv (.refl _) (.refl _) (u1_redNormal n) view.normal
        (top ▸ view.conversion.toConv)
    cases impossible
  · exact formed

/-- The same presupposition argument applies to canonical Sigma heads. -/
theorem RegularSigmaView.sourceFormed {Γ : Ctx n} {term type : PureTm n}
    (context : RegularCtx Γ) (view : RegularSigmaView (Γ := Γ) type)
    (typing : RegularHasType Γ term type) : RegularHasType Γ type .u1 := by
  rcases typing.type_presupposed context with top | formed
  · have impossible : (.u1 : PureTm n) = .sigma view.dom view.cod :=
      normalForms_eq_of_conv (.refl _) (.refl _) (u1_redNormal n) view.normal
        (top ▸ view.conversion.toConv)
    cases impossible
  · exact formed

/-! ## Independent algorithmic judgments -/

/-- The two directions of the independently stated algorithmic judgment. -/
inductive RegularDirection where
  | synthesize
  | check

/-- Syntax-directed synthesis and checking for the declared regular fragment.
The relation mentions normalization semantics through canonical views, but it
does not mention `inferRegularType`, `checkRegularFormed`, or their results.
Using one direction-indexed family gives the mixed rules a genuine structural
induction principle. -/
inductive RegularBidirectional : RegularDirection → {n : Nat} → {Γ : Ctx n} →
    (context : RegularCtx Γ) → PureTm n → PureTm n → Prop where
  | var {n : Nat} {Γ : Ctx n} (context : RegularCtx Γ) (index : Fin n) :
      RegularBidirectional .synthesize context (.var index) (lookup Γ index)
  | u0 {n : Nat} {Γ : Ctx n} (context : RegularCtx Γ) :
      RegularBidirectional .synthesize context .u0 .u1
  | pi {n : Nat} {Γ : Ctx n} {context : RegularCtx Γ}
      {dom domUniverse : PureTm n} {cod codUniverse : PureTm (n + 1)}
      (domFormed : RegularHasType Γ dom .u1)
      (domSynth : RegularBidirectional .synthesize context dom domUniverse)
      (domSort : ConstantFreeConv domUniverse .u1)
      (codFormed : RegularHasType (.snoc Γ dom) cod .u1)
      (codSynth : RegularBidirectional .synthesize
        (.snoc context domFormed) cod codUniverse)
      (codSort : ConstantFreeConv codUniverse .u1) :
      RegularBidirectional .synthesize context (.pi dom cod) .u1
  | sigma {n : Nat} {Γ : Ctx n} {context : RegularCtx Γ}
      {dom domUniverse : PureTm n} {cod codUniverse : PureTm (n + 1)}
      (domFormed : RegularHasType Γ dom .u1)
      (domSynth : RegularBidirectional .synthesize context dom domUniverse)
      (domSort : ConstantFreeConv domUniverse .u1)
      (codFormed : RegularHasType (.snoc Γ dom) cod .u1)
      (codSynth : RegularBidirectional .synthesize
        (.snoc context domFormed) cod codUniverse)
      (codSort : ConstantFreeConv codUniverse .u1) :
      RegularBidirectional .synthesize context (.sigma dom cod) .u1
  | identity {n : Nat} {Γ : Ctx n} {context : RegularCtx Γ}
      {carrier carrierUniverse left right : PureTm n}
      (carrierFormed : RegularHasType Γ carrier .u1)
      (carrierSynth : RegularBidirectional .synthesize
        context carrier carrierUniverse)
      (carrierSort : ConstantFreeConv carrierUniverse .u1)
      (leftCheck : RegularBidirectional .check context left carrier)
      (rightCheck : RegularBidirectional .check context right carrier) :
      RegularBidirectional .synthesize context (.id carrier left right) .u1
  | betaApp {n : Nat} {Γ : Ctx n} {context : RegularCtx Γ}
      {argument : PureTm n}
      {body cod : PureTm (n + 1)} {dom : PureTm n}
      (domFormed : RegularHasType Γ dom .u1)
      (argumentSynth : RegularBidirectional .synthesize context argument dom)
      (codFormed : RegularHasType (.snoc Γ dom) cod .u1)
      (bodySynth : RegularBidirectional .synthesize
        (.snoc context domFormed) body cod) :
      RegularBidirectional .synthesize context (.app (.lam body) argument)
        (inst0 argument cod)
  | app {n : Nat} {Γ : Ctx n} {context : RegularCtx Γ}
      {function argument functionType : PureTm n}
      (notLambda : ∀ body, function ≠ .lam body)
      (functionTypeFormed : RegularHasType Γ functionType .u1)
      (functionSynth : RegularBidirectional .synthesize
        context function functionType)
      (view : RegularPiView (Γ := Γ) functionType)
      (argumentCheck : RegularBidirectional .check context argument view.dom) :
      RegularBidirectional .synthesize context (.app function argument)
        (inst0 argument view.cod)
  | fst {n : Nat} {Γ : Ctx n} {context : RegularCtx Γ}
      {pair pairType : PureTm n}
      (pairTypeFormed : RegularHasType Γ pairType .u1)
      (pairSynth : RegularBidirectional .synthesize context pair pairType)
      (view : RegularSigmaView (Γ := Γ) pairType) :
      RegularBidirectional .synthesize context (.fst pair) view.dom
  | snd {n : Nat} {Γ : Ctx n} {context : RegularCtx Γ}
      {pair pairType : PureTm n}
      (pairTypeFormed : RegularHasType Γ pairType .u1)
      (pairSynth : RegularBidirectional .synthesize context pair pairType)
      (view : RegularSigmaView (Γ := Γ) pairType) :
      RegularBidirectional .synthesize context (.snd pair)
        (inst0 (.fst pair) view.cod)
  | refl {n : Nat} {Γ : Ctx n} {context : RegularCtx Γ}
      {term carrier : PureTm n}
      (carrierFormed : RegularHasType Γ carrier .u1)
      (termSynth : RegularBidirectional .synthesize context term carrier) :
      RegularBidirectional .synthesize context (.refl term)
        (.id carrier term term)
  | lambda {n : Nat} {Γ : Ctx n} {context : RegularCtx Γ}
      {body : PureTm (n + 1)}
      {expected : PureTm n}
      (expectedFormed : RegularHasType Γ expected .u1)
      (view : RegularPiView (Γ := Γ) expected)
      (bodyCheck : RegularBidirectional .check
        (.snoc context view.domFormed)
        body view.cod) :
      RegularBidirectional .check context (.lam body) expected
  | pair {n : Nat} {Γ : Ctx n} {context : RegularCtx Γ}
      {first second expected : PureTm n}
      (expectedFormed : RegularHasType Γ expected .u1)
      (view : RegularSigmaView (Γ := Γ) expected)
      (firstCheck : RegularBidirectional .check context first view.dom)
      (secondCheck : RegularBidirectional .check context second
        (inst0 first view.cod)) :
      RegularBidirectional .check context (.pair first second) expected
  | convert {n : Nat} {Γ : Ctx n} {context : RegularCtx Γ}
      {term actual expected : PureTm n}
      (notLambda : ∀ body, term ≠ .lam body)
      (notPair : ∀ first second, term ≠ .pair first second)
      (actualSynth : RegularBidirectional .synthesize context term actual)
      (expectedFormed : RegularHasType Γ expected .u1)
      (conversion : ConstantFreeConv actual expected) :
      RegularBidirectional .check context term expected

/-- Public name for the synthesis direction. -/
abbrev RegularSynthesizes {Γ : Ctx n} (context : RegularCtx Γ)
    (term type : PureTm n) : Prop :=
  RegularBidirectional .synthesize context term type

/-- Public name for formed-type checking. -/
abbrev RegularChecksFormed {Γ : Ctx n} (context : RegularCtx Γ)
    (term expected : PureTm n) : Prop :=
  RegularBidirectional .check context term expected

/-! ## Semantic soundness of the independent judgments -/

theorem RegularBidirectional.sound
    {n : Nat} {Γ : Ctx n} {context : RegularCtx Γ}
    {direction : RegularDirection} {term type : PureTm n}
    (derivation : RegularBidirectional direction context term type) :
    RegularHasType Γ term type := by
  induction derivation with
  | var _ index => exact .var index
  | u0 _ => exact .u0_type _
  | pi domFormed _ _ codFormed _ _ _ _ => exact .pi_form domFormed codFormed
  | sigma domFormed _ _ codFormed _ _ _ _ =>
      exact .sigma_form domFormed codFormed
  | identity carrierFormed _ _ _ _ _ leftSound rightSound =>
      exact .id_form carrierFormed leftSound rightSound
  | betaApp domFormed _ codFormed _ argumentSound bodySound =>
      exact .app_elim domFormed
        (.lam_intro domFormed codFormed bodySound) argumentSound codFormed
  | app _ _ _ view _ functionSound argumentSound =>
      exact .app_elim view.domFormed
        (.conv_type functionSound
          (.pi_form view.domFormed view.codFormed) view.conversion)
        argumentSound view.codFormed
  | fst _ _ view pairSound =>
      exact .fst_elim view.domFormed
        (.conv_type pairSound
          (.sigma_form view.domFormed view.codFormed) view.conversion)
        view.codFormed
  | snd _ _ view pairSound =>
      exact .snd_elim view.domFormed
        (.conv_type pairSound
          (.sigma_form view.domFormed view.codFormed) view.conversion)
        view.codFormed
  | refl carrierFormed _ termSound =>
      exact .refl_intro carrierFormed termSound
  | lambda expectedFormed view _ bodySound =>
      exact .conv_type
        (.lam_intro view.domFormed view.codFormed bodySound)
        expectedFormed view.conversion.symm
  | pair expectedFormed view _ _ firstSound secondSound =>
      exact .conv_type
        (.pair_intro view.domFormed firstSound secondSound
          view.codFormed)
        expectedFormed view.conversion.symm
  | convert _ _ _ expectedFormed conversion actualSound =>
      exact .conv_type actualSound expectedFormed conversion

theorem RegularSynthesizes.sound
    {n : Nat} {Γ : Ctx n} {context : RegularCtx Γ}
    {term type : PureTm n}
    (derivation : RegularSynthesizes context term type) :
    RegularHasType Γ term type :=
  RegularBidirectional.sound derivation

theorem RegularChecksFormed.sound
    {n : Nat} {Γ : Ctx n} {context : RegularCtx Γ}
    {term expected : PureTm n}
    (derivation : RegularChecksFormed context term expected) :
    RegularHasType Γ term expected :=
  RegularBidirectional.sound derivation

/-! ## Computational success predicates -/

/-- Synthesis success includes exact agreement on the synthesized type, while
leaving proof fields existential and erasable. -/
def RegularSynthesisSucceeds {Γ : Ctx n} (context : RegularCtx Γ)
    (term type : PureTm n) : Prop :=
  ∃ inferred, inferRegularType context term = .ok inferred ∧
    inferred.type = type

/-- Formed checking must be insensitive to the particular proof of type
formation supplied by a caller. -/
def RegularCheckingSucceeds {Γ : Ctx n} (context : RegularCtx Γ)
    (term expected : PureTm n) : Prop :=
  ∀ expectedFormed : RegularHasType Γ expected .u1,
    ∃ checked, checkRegularFormed context term expected expectedFormed = .ok checked

/-- Synthesis of the upper sort makes `asFormedType?` succeed. -/
theorem RegularInferred.asFormedType?_complete_of_conversion
    {Γ : Ctx n} {term : PureTm n} (context : RegularCtx Γ)
    (inferred : RegularInferred (Γ := Γ) term)
    (conversion : ConstantFreeConv inferred.type .u1) :
    ∃ formed, inferred.asFormedType? context = .ok formed := by
  unfold RegularInferred.asFormedType?
  have accepted : decideRegularConversion context inferred.status (.top rfl) = true :=
    (decideRegularConversion_correct context inferred.status (.top rfl)).2
      conversion
  rw [dif_pos accepted]
  exact ⟨_, rfl⟩

/-- Literal synthesis of the upper sort is the reflexive special case. -/
theorem RegularInferred.asFormedType?_complete_of_type_eq
    {Γ : Ctx n} {term : PureTm n} (context : RegularCtx Γ)
    (inferred : RegularInferred (Γ := Γ) term)
    (typeEq : inferred.type = .u1) :
    ∃ formed, inferred.asFormedType? context = .ok formed := by
  apply inferred.asFormedType?_complete_of_conversion context
  simpa [typeEq] using
    (ConstantFreeConv.refl inferred.type
      (regularNormalizationSpecification.fragment inferred.type
        (inferred.status.covered context)))

/-- Successful formation extraction reflects the exact conversion premise
used by the independent judgment. -/
theorem RegularInferred.asFormedType?_reflects
    {Γ : Ctx n} {term : PureTm n} (context : RegularCtx Γ)
    (inferred : RegularInferred (Γ := Γ) term)
    (formed : PLift (RegularHasType Γ term .u1))
    (computed : inferred.asFormedType? context = .ok formed) :
    ConstantFreeConv inferred.type .u1 := by
  unfold RegularInferred.asFormedType? at computed
  split at computed
  · rename_i accepted
    exact (decideRegularConversion_correct context inferred.status (.top rfl)).1
      accepted
  · cases computed

/-- A semantically formed synthesized type must use the ordinary runtime
classification, never the distinguished top-sort branch. -/
theorem RegularInferred.status_eq_formed_of_type_formed
    {Γ : Ctx n} {term : PureTm n}
    (inferred : RegularInferred (Γ := Γ) term)
    (formed : RegularHasType Γ inferred.type .u1) :
    ∃ actualFormed, inferred.status = .formed actualFormed := by
  cases statusEq : inferred.status with
  | formed actualFormed => exact ⟨actualFormed, rfl⟩
  | top equal =>
      exact False.elim (formed.subject_ne_u1 equal)

/-! ## Compositional completeness lemmas -/

theorem inferRegular_pi_complete {Γ : Ctx n} (context : RegularCtx Γ)
    {dom domUniverse : PureTm n} {cod codUniverse : PureTm (n + 1)}
    (domFormed : RegularHasType Γ dom .u1)
    (domSuccess : RegularSynthesisSucceeds context dom domUniverse)
    (domSort : ConstantFreeConv domUniverse .u1)
    (codSuccess : RegularSynthesisSucceeds (.snoc context domFormed) cod codUniverse)
    (codSort : ConstantFreeConv codUniverse .u1) :
    RegularSynthesisSucceeds context (.pi dom cod) .u1 := by
  rcases domSuccess with ⟨domInfo, domComputed, domType⟩
  have domConversion : ConstantFreeConv domInfo.type .u1 := domType ▸ domSort
  rcases domInfo.asFormedType?_complete_of_conversion context domConversion with
    ⟨domain, domainComputed⟩
  rcases codSuccess with ⟨codInfo, codComputed, codType⟩
  have extendedEq : (.snoc context domain.down : RegularCtx (.snoc Γ dom)) =
      .snoc context domFormed := Subsingleton.elim _ _
  have codComputed' : inferRegularType (.snoc context domain.down) cod =
      .ok codInfo := by simpa only [extendedEq] using codComputed
  have codConversion : ConstantFreeConv codInfo.type .u1 := codType ▸ codSort
  rcases codInfo.asFormedType?_complete_of_conversion
      (.snoc context domain.down) codConversion with
    ⟨codomain, codomainComputed⟩
  unfold RegularSynthesisSucceeds
  rw [inferRegularType.eq_5, domComputed]
  dsimp only [Bind.bind, Except.bind]
  rw [domainComputed]
  dsimp only [Bind.bind, Except.bind]
  rw [codComputed']
  dsimp only [Bind.bind, Except.bind]
  rw [codomainComputed]
  exact ⟨_, rfl, rfl⟩

theorem inferRegular_sigma_complete {Γ : Ctx n} (context : RegularCtx Γ)
    {dom domUniverse : PureTm n} {cod codUniverse : PureTm (n + 1)}
    (domFormed : RegularHasType Γ dom .u1)
    (domSuccess : RegularSynthesisSucceeds context dom domUniverse)
    (domSort : ConstantFreeConv domUniverse .u1)
    (codSuccess : RegularSynthesisSucceeds (.snoc context domFormed) cod codUniverse)
    (codSort : ConstantFreeConv codUniverse .u1) :
    RegularSynthesisSucceeds context (.sigma dom cod) .u1 := by
  rcases domSuccess with ⟨domInfo, domComputed, domType⟩
  have domConversion : ConstantFreeConv domInfo.type .u1 := domType ▸ domSort
  rcases domInfo.asFormedType?_complete_of_conversion context domConversion with
    ⟨domain, domainComputed⟩
  rcases codSuccess with ⟨codInfo, codComputed, codType⟩
  have extendedEq : (.snoc context domain.down : RegularCtx (.snoc Γ dom)) =
      .snoc context domFormed := Subsingleton.elim _ _
  have codComputed' : inferRegularType (.snoc context domain.down) cod =
      .ok codInfo := by simpa only [extendedEq] using codComputed
  have codConversion : ConstantFreeConv codInfo.type .u1 := codType ▸ codSort
  rcases codInfo.asFormedType?_complete_of_conversion
      (.snoc context domain.down) codConversion with
    ⟨codomain, codomainComputed⟩
  unfold RegularSynthesisSucceeds
  rw [inferRegularType.eq_6, domComputed]
  dsimp only [Bind.bind, Except.bind]
  rw [domainComputed]
  dsimp only [Bind.bind, Except.bind]
  rw [codComputed']
  dsimp only [Bind.bind, Except.bind]
  rw [codomainComputed]
  exact ⟨_, rfl, rfl⟩

theorem inferRegular_identity_complete {Γ : Ctx n} (context : RegularCtx Γ)
    {carrier carrierUniverse left right : PureTm n}
    (carrierSuccess : RegularSynthesisSucceeds context carrier carrierUniverse)
    (carrierSort : ConstantFreeConv carrierUniverse .u1)
    (leftSuccess : RegularCheckingSucceeds context left carrier)
    (rightSuccess : RegularCheckingSucceeds context right carrier) :
    RegularSynthesisSucceeds context (.id carrier left right) .u1 := by
  rcases carrierSuccess with ⟨carrierInfo, carrierComputed, carrierType⟩
  have carrierConversion : ConstantFreeConv carrierInfo.type .u1 :=
    carrierType ▸ carrierSort
  rcases carrierInfo.asFormedType?_complete_of_conversion context
      carrierConversion with
    ⟨carrierFormed, carrierFormedComputed⟩
  rcases leftSuccess carrierFormed.down with ⟨leftChecked, leftComputed⟩
  rcases rightSuccess carrierFormed.down with ⟨rightChecked, rightComputed⟩
  unfold RegularSynthesisSucceeds
  rw [inferRegularType.eq_7, carrierComputed]
  dsimp only [Bind.bind, Except.bind]
  rw [carrierFormedComputed]
  dsimp only [Bind.bind, Except.bind]
  rw [leftComputed]
  dsimp only [Bind.bind, Except.bind]
  rw [rightComputed]
  exact ⟨_, rfl, rfl⟩

theorem inferRegular_betaApp_complete {Γ : Ctx n} (context : RegularCtx Γ)
    {argument : PureTm n} {body cod : PureTm (n + 1)} {dom : PureTm n}
    (domFormed : RegularHasType Γ dom .u1)
    (argumentSuccess : RegularSynthesisSucceeds context argument dom)
    (bodySuccess : RegularSynthesisSucceeds (.snoc context domFormed) body cod)
    (codFormed : RegularHasType (.snoc Γ dom) cod .u1) :
    RegularSynthesisSucceeds context (.app (.lam body) argument)
      (inst0 argument cod) := by
  rcases argumentSuccess with ⟨argumentInfo, argumentComputed, argumentType⟩
  subst dom
  rcases argumentInfo.status_eq_formed_of_type_formed domFormed with
    ⟨argumentFormed, argumentStatus⟩
  rcases bodySuccess with ⟨bodyInfo, bodyComputed, bodyType⟩
  subst cod
  have extendedEq : (.snoc context argumentFormed :
      RegularCtx (.snoc Γ argumentInfo.type)) =
      .snoc context domFormed := Subsingleton.elim _ _
  have bodyComputed' : inferRegularType (.snoc context argumentFormed) body =
      .ok bodyInfo := by
    simpa only [extendedEq] using bodyComputed
  rcases bodyInfo.status_eq_formed_of_type_formed codFormed with
    ⟨bodyFormed, bodyStatus⟩
  unfold RegularSynthesisSucceeds
  rw [inferRegularType.eq_9, argumentComputed]
  dsimp only [RegularInferred.resultFormed?, Bind.bind, Except.bind]
  rw [argumentStatus]
  dsimp [Pure.pure, Bind.bind, Except.instMonad, Except.pure, Except.bind]
  rw [bodyComputed']
  dsimp only [RegularInferred.resultFormed?, Bind.bind, Except.bind]
  rw [bodyStatus]
  dsimp [Pure.pure, Bind.bind, Except.instMonad, Except.pure, Except.bind]
  exact ⟨_, rfl, rfl⟩

theorem inferRegular_refl_complete {Γ : Ctx n} (context : RegularCtx Γ)
    {term carrier : PureTm n}
    (carrierFormed : RegularHasType Γ carrier .u1)
    (termSuccess : RegularSynthesisSucceeds context term carrier) :
    RegularSynthesisSucceeds context (.refl term) (.id carrier term term) := by
  rcases termSuccess with ⟨termInfo, termComputed, termType⟩
  have resultFormed : RegularHasType Γ termInfo.type .u1 := by
    exact termType ▸ carrierFormed
  rcases termInfo.status_eq_formed_of_type_formed resultFormed with
    ⟨actualFormed, statusComputed⟩
  unfold RegularSynthesisSucceeds
  rw [inferRegularType.eq_14, termComputed]
  dsimp only [RegularInferred.resultFormed?, Bind.bind, Except.bind]
  rw [statusComputed]
  dsimp [Pure.pure, Bind.bind, Except.instMonad, Except.pure, Except.bind]
  refine ⟨_, rfl, ?_⟩
  simp only [termType]

theorem inferRegular_app_complete {Γ : Ctx n} (context : RegularCtx Γ)
    {function argument functionType : PureTm n}
    (notLambda : ∀ body, function ≠ .lam body)
    (functionTypeFormed : RegularHasType Γ functionType .u1)
    (functionSuccess : RegularSynthesisSucceeds context function functionType)
    (canonical : RegularPiView (Γ := Γ) functionType)
    (argumentSuccess : RegularCheckingSucceeds context argument canonical.dom) :
    RegularSynthesisSucceeds context (.app function argument)
      (inst0 argument canonical.cod) := by
  rcases functionSuccess with
    ⟨functionInfo, functionComputed, functionTypeEq⟩
  subst functionType
  rcases functionInfo.status_eq_formed_of_type_formed functionTypeFormed with
    ⟨actualFormed, statusComputed⟩
  rcases regularPiView?_of_canonical context actualFormed canonical with
    ⟨view, viewComputed, domEq, codEq⟩
  have argumentSuccess' : RegularCheckingSucceeds context argument view.dom := by
    simpa only [domEq] using argumentSuccess
  rcases argumentSuccess' view.domFormed with
    ⟨argumentChecked, argumentComputed⟩
  unfold RegularSynthesisSucceeds
  rw [inferRegularType.eq_10 _ _ _ _ _ notLambda, functionComputed]
  dsimp [Pure.pure, Bind.bind, Except.instMonad, Except.pure, Except.bind]
  rw [statusComputed, viewComputed]
  dsimp [Pure.pure, Bind.bind, Except.instMonad, Except.pure, Except.bind]
  rw [argumentComputed]
  refine ⟨_, rfl, ?_⟩
  exact congrArg (inst0 argument) codEq

theorem inferRegular_fst_complete {Γ : Ctx n} (context : RegularCtx Γ)
    {pair pairType : PureTm n}
    (pairTypeFormed : RegularHasType Γ pairType .u1)
    (pairSuccess : RegularSynthesisSucceeds context pair pairType)
    (canonical : RegularSigmaView (Γ := Γ) pairType) :
    RegularSynthesisSucceeds context (.fst pair) canonical.dom := by
  rcases pairSuccess with ⟨pairInfo, pairComputed, pairTypeEq⟩
  subst pairType
  rcases pairInfo.status_eq_formed_of_type_formed pairTypeFormed with
    ⟨actualFormed, statusComputed⟩
  rcases regularSigmaView?_of_canonical context actualFormed canonical with
    ⟨view, viewComputed, domEq, codEq⟩
  unfold RegularSynthesisSucceeds
  rw [inferRegularType.eq_12, pairComputed]
  dsimp [Pure.pure, Bind.bind, Except.instMonad, Except.pure, Except.bind]
  rw [statusComputed, viewComputed]
  exact ⟨_, rfl, domEq⟩

theorem inferRegular_snd_complete {Γ : Ctx n} (context : RegularCtx Γ)
    {pair pairType : PureTm n}
    (pairTypeFormed : RegularHasType Γ pairType .u1)
    (pairSuccess : RegularSynthesisSucceeds context pair pairType)
    (canonical : RegularSigmaView (Γ := Γ) pairType) :
    RegularSynthesisSucceeds context (.snd pair)
      (inst0 (.fst pair) canonical.cod) := by
  rcases pairSuccess with ⟨pairInfo, pairComputed, pairTypeEq⟩
  subst pairType
  rcases pairInfo.status_eq_formed_of_type_formed pairTypeFormed with
    ⟨actualFormed, statusComputed⟩
  rcases regularSigmaView?_of_canonical context actualFormed canonical with
    ⟨view, viewComputed, domEq, codEq⟩
  unfold RegularSynthesisSucceeds
  rw [inferRegularType.eq_13, pairComputed]
  dsimp [Pure.pure, Bind.bind, Except.instMonad, Except.pure, Except.bind]
  rw [statusComputed, viewComputed]
  refine ⟨_, rfl, ?_⟩
  exact congrArg (inst0 (.fst pair)) codEq

theorem checkRegular_lambda_complete {Γ : Ctx n} (context : RegularCtx Γ)
    {body : PureTm (n + 1)} {expected : PureTm n}
    (canonical : RegularPiView (Γ := Γ) expected)
    (bodySuccess : RegularCheckingSucceeds
      (.snoc context canonical.domFormed) body canonical.cod) :
    RegularCheckingSucceeds context (.lam body) expected := by
  intro expectedFormed
  rcases regularPiView?_of_canonical context expectedFormed canonical with
    ⟨view, viewComputed, domEq, codEq⟩
  have bodySuccess' : RegularCheckingSucceeds
      (.snoc context view.domFormed) body view.cod := by
    simpa only [domEq, codEq] using bodySuccess
  rcases bodySuccess' view.codFormed with ⟨bodyChecked, bodyComputed⟩
  rw [checkRegularFormed.eq_1, viewComputed]
  dsimp [Pure.pure, Bind.bind, Except.instMonad, Except.pure, Except.bind]
  rw [bodyComputed]
  exact ⟨_, rfl⟩

theorem checkRegular_pair_complete {Γ : Ctx n} (context : RegularCtx Γ)
    {first second expected : PureTm n}
    (canonical : RegularSigmaView (Γ := Γ) expected)
    (firstSuccess : RegularCheckingSucceeds context first canonical.dom)
    (secondSuccess : RegularCheckingSucceeds context second
      (inst0 first canonical.cod)) :
    RegularCheckingSucceeds context (.pair first second) expected := by
  intro expectedFormed
  rcases regularSigmaView?_of_canonical context expectedFormed canonical with
    ⟨view, viewComputed, domEq, codEq⟩
  have firstSuccess' : RegularCheckingSucceeds context first view.dom := by
    simpa only [domEq] using firstSuccess
  have secondSuccess' : RegularCheckingSucceeds context second
      (inst0 first view.cod) := by
    simpa only [codEq] using secondSuccess
  rcases firstSuccess' view.domFormed with ⟨firstChecked, firstComputed⟩
  let secondExpectedFormed := view.codFormed.instantiate
    firstChecked.typing context.constantFreeCtx
  rcases secondSuccess' secondExpectedFormed with
    ⟨secondChecked, secondComputed⟩
  rw [checkRegularFormed.eq_2, viewComputed]
  dsimp [Pure.pure, Bind.bind, Except.instMonad, Except.pure, Except.bind]
  rw [firstComputed]
  dsimp [secondExpectedFormed, Pure.pure, Bind.bind, Except.instMonad,
    Except.pure, Except.bind]
  rw [secondComputed]
  exact ⟨_, rfl⟩

theorem checkRegular_convert_complete {Γ : Ctx n} (context : RegularCtx Γ)
    {term actual expected : PureTm n}
    (notLambda : ∀ body, term ≠ .lam body)
    (notPair : ∀ first second, term ≠ .pair first second)
    (actualSuccess : RegularSynthesisSucceeds context term actual)
    (conversion : ConstantFreeConv actual expected) :
    RegularCheckingSucceeds context term expected := by
  intro expectedFormed
  rcases actualSuccess with ⟨inferred, computed, actualType⟩
  have conversion' : ConstantFreeConv inferred.type expected := by
    exact actualType ▸ conversion
  exact checkRegularFormed_of_inferred context expectedFormed
    (fun body equal => notLambda body equal)
    (fun first second equal => notPair first second equal)
    inferred computed conversion'

/-! ## Exact completeness for the declared bidirectional fragment -/

/-- Every derivation in the independently authored judgment is accepted by
the executable checker in the corresponding direction. -/
theorem RegularBidirectional.complete
    {n : Nat} {Γ : Ctx n} {context : RegularCtx Γ}
    {direction : RegularDirection} {term type : PureTm n}
    (derivation : RegularBidirectional direction context term type) :
    match direction with
    | .synthesize => RegularSynthesisSucceeds context term type
    | .check => RegularCheckingSucceeds context term type := by
  induction derivation with
  | var context index =>
      exact ⟨regularVariableInfo context index,
        inferRegular_variable context index, rfl⟩
  | u0 context =>
      unfold RegularSynthesisSucceeds
      refine ⟨{ type := .u1, typing := .u0_type _, status := .top rfl }, ?_, rfl⟩
      rw [inferRegularType.eq_3]
      rfl
  | pi domFormed _ domSort codFormed _ codSort domComplete codComplete =>
      exact inferRegular_pi_complete _ domFormed domComplete domSort
        codComplete codSort
  | sigma domFormed _ domSort codFormed _ codSort domComplete codComplete =>
      exact inferRegular_sigma_complete _ domFormed domComplete domSort
        codComplete codSort
  | identity carrierFormed _ carrierSort _ _ carrierComplete leftComplete
      rightComplete =>
      exact inferRegular_identity_complete _ carrierComplete carrierSort
        leftComplete rightComplete
  | betaApp domFormed _ codFormed _ argumentComplete bodyComplete =>
      exact inferRegular_betaApp_complete _ domFormed argumentComplete
        bodyComplete codFormed
  | app notLambda functionTypeFormed _ view _ functionComplete
      argumentComplete =>
      exact inferRegular_app_complete _ notLambda functionTypeFormed
        functionComplete view argumentComplete
  | fst pairTypeFormed _ view pairComplete =>
      exact inferRegular_fst_complete _ pairTypeFormed pairComplete view
  | snd pairTypeFormed _ view pairComplete =>
      exact inferRegular_snd_complete _ pairTypeFormed pairComplete view
  | refl carrierFormed _ termComplete =>
      exact inferRegular_refl_complete _ carrierFormed termComplete
  | lambda expectedFormed view _ bodyComplete =>
      exact checkRegular_lambda_complete _ view bodyComplete
  | pair expectedFormed view _ _ firstComplete secondComplete =>
      exact checkRegular_pair_complete _ view firstComplete secondComplete
  | convert notLambda notPair _ expectedFormed conversion actualComplete =>
      exact checkRegular_convert_complete _ notLambda notPair actualComplete
        conversion

theorem RegularSynthesizes.complete
    {n : Nat} {Γ : Ctx n} {context : RegularCtx Γ}
    {term type : PureTm n}
    (derivation : RegularSynthesizes context term type) :
    RegularSynthesisSucceeds context term type :=
  RegularBidirectional.complete derivation

theorem RegularChecksFormed.complete
    {n : Nat} {Γ : Ctx n} {context : RegularCtx Γ}
    {term expected : PureTm n}
    (derivation : RegularChecksFormed context term expected) :
    RegularCheckingSucceeds context term expected :=
  RegularBidirectional.complete derivation

/-! ## Public typing queries -/

/-- A public query either checks against the distinguished top sort or first
synthesizes formation of an ordinary expected type.  This is independent of
the executable `checkRegularType` branching code. -/
inductive RegularPublicChecks {Γ : Ctx n} (context : RegularCtx Γ) :
    PureTm n → PureTm n → Prop where
  | top {term actual : PureTm n}
      (termSynth : RegularSynthesizes context term actual)
      (conversion : ConstantFreeConv actual .u1) :
      RegularPublicChecks context term .u1
  | formed {term expected expectedUniverse : PureTm n}
      (expectedSynth : RegularSynthesizes context expected expectedUniverse)
      (expectedSort : ConstantFreeConv expectedUniverse .u1)
      (termCheck : RegularChecksFormed context term expected) :
      RegularPublicChecks context term expected

/-- Public-query soundness lands in the intrinsic regular typing judgment. -/
theorem RegularPublicChecks.sound
    {n : Nat} {Γ : Ctx n} {context : RegularCtx Γ}
    {term expected : PureTm n}
    (derivation : RegularPublicChecks context term expected) :
    RegularHasType Γ term expected := by
  cases derivation with
  | top termSynth conversion => exact .conv_sort termSynth.sound conversion
  | formed expectedSynth expectedSort termCheck => exact termCheck.sound

theorem checkRegularTop_complete {Γ : Ctx n} (context : RegularCtx Γ)
    {term actual : PureTm n}
    (termSuccess : RegularSynthesisSucceeds context term actual)
    (conversion : ConstantFreeConv actual .u1) :
    ∃ checked, checkRegularTop context term = .ok checked := by
  rcases termSuccess with ⟨inferred, computed, actualType⟩
  have conversion' : ConstantFreeConv inferred.type .u1 :=
    actualType ▸ conversion
  unfold checkRegularTop
  rw [computed]
  dsimp [Pure.pure, Bind.bind, Except.instMonad, Except.pure, Except.bind]
  have accepted : decideRegularConversion context inferred.status (.top rfl) = true :=
    (decideRegularConversion_correct context inferred.status (.top rfl)).2
      conversion'
  rw [dif_pos accepted]
  exact ⟨_, rfl⟩

/-- Completeness reaches the actual certificate-free publication bit, not a
parallel evaluator. -/
theorem regularCheckBool_complete {Γ : Ctx n} {context : RegularCtx Γ}
    {term expected : PureTm n}
    (derivation : RegularPublicChecks context term expected) :
    regularCheckBool context term expected = true := by
  cases derivation with
  | top termSynth conversion =>
      rcases checkRegularTop_complete context termSynth.complete conversion with
        ⟨checked, computed⟩
      unfold regularCheckBool checkRegularType
      rw [dif_pos rfl, computed]
      rfl
  | formed expectedSynth expectedSort termCheck =>
      have expectedFormed := expectedSynth.sound
      have expectedTypeFormed : RegularHasType Γ expected .u1 :=
        .conv_sort expectedFormed expectedSort
      have expectedNotTop : expected ≠ .u1 := expectedTypeFormed.subject_ne_u1
      rcases expectedSynth.complete with
        ⟨expectedInfo, expectedComputed, expectedType⟩
      have expectedConversion : ConstantFreeConv expectedInfo.type .u1 :=
        expectedType ▸ expectedSort
      rcases expectedInfo.asFormedType?_complete_of_conversion context
          expectedConversion with
        ⟨formed, formedComputed⟩
      rcases termCheck.complete formed.down with ⟨checked, checkedComputed⟩
      unfold regularCheckBool checkRegularType
      rw [dif_neg expectedNotTop, expectedComputed]
      dsimp [Pure.pure, Bind.bind, Except.instMonad, Except.pure, Except.bind]
      rw [formedComputed]
      dsimp [Pure.pure, Bind.bind, Except.instMonad, Except.pure, Except.bind]
      rw [checkedComputed]
      rfl

/-! ## Boundary witnesses -/

/-- Positive public witness: the lower universe checks at the upper sort. -/
theorem regularPublic_u0_u1 :
    RegularPublicChecks RegularCtx.nil (.u0 : PureTm 0) .u1 := by
  exact .top (.u0 .nil) (ConstantFreeConv.refl .u1 .u1)

/-- Negative public witness: no query can type the upper sort itself. -/
theorem regularPublic_u1_rejected :
    ¬ RegularPublicChecks RegularCtx.nil (.u1 : PureTm 0) .u1 := by
  intro derivation
  exact no_regular_u1_term (Γ := (.nil : Ctx 0)) derivation.sound

/-! ## Reflection of successful computation -/

mutual

theorem inferRegularType_reflects {Γ : Ctx n} (context : RegularCtx Γ)
    (term : PureTm n) (inferred : RegularInferred (Γ := Γ) term)
    (computed : inferRegularType context term = .ok inferred) :
    RegularSynthesizes context term inferred.type := by
  cases term with
  | var index =>
      rw [inferRegularType.eq_1] at computed
      cases computed
      exact .var context index
  | const name =>
      rw [inferRegularType.eq_2] at computed
      cases computed
  | u0 =>
      rw [inferRegularType.eq_3] at computed
      cases computed
      exact .u0 context
  | u1 =>
      rw [inferRegularType.eq_4] at computed
      cases computed
  | pi dom cod =>
      rw [inferRegularType.eq_5] at computed
      cases domComputed : inferRegularType context dom with
      | error failure =>
          rw [domComputed] at computed
          cases computed
      | ok domInfo =>
          rw [domComputed] at computed
          dsimp [Pure.pure, Bind.bind, Except.instMonad, Except.pure,
            Except.bind] at computed
          cases domFormedComputed : domInfo.asFormedType? context with
          | error failure =>
              rw [domFormedComputed] at computed
              cases computed
          | ok domFormed =>
              rw [domFormedComputed] at computed
              dsimp [Pure.pure, Bind.bind, Except.instMonad, Except.pure,
                Except.bind] at computed
              cases codComputed : inferRegularType
                  (.snoc context domFormed.down) cod with
              | error failure =>
                  rw [codComputed] at computed
                  cases computed
              | ok codInfo =>
                  rw [codComputed] at computed
                  dsimp [Pure.pure, Bind.bind, Except.instMonad, Except.pure,
                    Except.bind] at computed
                  cases codFormedComputed : codInfo.asFormedType?
                      (.snoc context domFormed.down) with
                  | error failure =>
                      rw [codFormedComputed] at computed
                      cases computed
                  | ok codFormed =>
                      rw [codFormedComputed] at computed
                      cases computed
                      exact .pi domFormed.down
                        (inferRegularType_reflects context dom domInfo domComputed)
                        (domInfo.asFormedType?_reflects context domFormed
                          domFormedComputed)
                        codFormed.down
                        (inferRegularType_reflects
                          (.snoc context domFormed.down) cod codInfo codComputed)
                        (codInfo.asFormedType?_reflects
                          (.snoc context domFormed.down) codFormed
                          codFormedComputed)
  | sigma dom cod =>
      rw [inferRegularType.eq_6] at computed
      cases domComputed : inferRegularType context dom with
      | error failure =>
          rw [domComputed] at computed
          cases computed
      | ok domInfo =>
          rw [domComputed] at computed
          dsimp [Pure.pure, Bind.bind, Except.instMonad, Except.pure,
            Except.bind] at computed
          cases domFormedComputed : domInfo.asFormedType? context with
          | error failure =>
              rw [domFormedComputed] at computed
              cases computed
          | ok domFormed =>
              rw [domFormedComputed] at computed
              dsimp [Pure.pure, Bind.bind, Except.instMonad, Except.pure,
                Except.bind] at computed
              cases codComputed : inferRegularType
                  (.snoc context domFormed.down) cod with
              | error failure =>
                  rw [codComputed] at computed
                  cases computed
              | ok codInfo =>
                  rw [codComputed] at computed
                  dsimp [Pure.pure, Bind.bind, Except.instMonad, Except.pure,
                    Except.bind] at computed
                  cases codFormedComputed : codInfo.asFormedType?
                      (.snoc context domFormed.down) with
                  | error failure =>
                      rw [codFormedComputed] at computed
                      cases computed
                  | ok codFormed =>
                      rw [codFormedComputed] at computed
                      cases computed
                      exact .sigma domFormed.down
                        (inferRegularType_reflects context dom domInfo domComputed)
                        (domInfo.asFormedType?_reflects context domFormed
                          domFormedComputed)
                        codFormed.down
                        (inferRegularType_reflects
                          (.snoc context domFormed.down) cod codInfo codComputed)
                        (codInfo.asFormedType?_reflects
                          (.snoc context domFormed.down) codFormed
                          codFormedComputed)
  | id carrier left right =>
      rw [inferRegularType.eq_7] at computed
      cases carrierComputed : inferRegularType context carrier with
      | error failure =>
          rw [carrierComputed] at computed
          cases computed
      | ok carrierInfo =>
          rw [carrierComputed] at computed
          dsimp [Pure.pure, Bind.bind, Except.instMonad, Except.pure,
            Except.bind] at computed
          cases carrierFormedComputed : carrierInfo.asFormedType? context with
          | error failure =>
              rw [carrierFormedComputed] at computed
              cases computed
          | ok carrierFormed =>
              rw [carrierFormedComputed] at computed
              dsimp [Pure.pure, Bind.bind, Except.instMonad, Except.pure,
                Except.bind] at computed
              cases leftComputed : checkRegularFormed context left carrier
                  carrierFormed.down with
              | error failure =>
                  rw [leftComputed] at computed
                  cases computed
              | ok leftChecked =>
                  rw [leftComputed] at computed
                  dsimp [Pure.pure, Bind.bind, Except.instMonad, Except.pure,
                    Except.bind] at computed
                  cases rightComputed : checkRegularFormed context right carrier
                      carrierFormed.down with
                  | error failure =>
                      rw [rightComputed] at computed
                      cases computed
                  | ok rightChecked =>
                      rw [rightComputed] at computed
                      cases computed
                      exact .identity carrierFormed.down
                        (inferRegularType_reflects context carrier carrierInfo
                          carrierComputed)
                        (carrierInfo.asFormedType?_reflects context carrierFormed
                          carrierFormedComputed)
                        (checkRegularFormed_reflects context left carrier
                          carrierFormed.down leftChecked leftComputed)
                        (checkRegularFormed_reflects context right carrier
                          carrierFormed.down rightChecked rightComputed)
  | lam body =>
      rw [inferRegularType.eq_8] at computed
      cases computed
  | app function argument =>
      by_cases isLambda : ∃ body, function = .lam body
      · rcases isLambda with ⟨body, rfl⟩
        rw [inferRegularType.eq_9] at computed
        cases argumentComputed : inferRegularType context argument with
        | error failure =>
            rw [argumentComputed] at computed
            cases computed
        | ok argumentInfo =>
            rw [argumentComputed] at computed
            dsimp [Pure.pure, Bind.bind, Except.instMonad, Except.pure,
              Except.bind] at computed
            cases domFormedComputed : argumentInfo.resultFormed? with
            | error failure =>
                rw [domFormedComputed] at computed
                cases computed
            | ok domFormed =>
                rw [domFormedComputed] at computed
                dsimp [Pure.pure, Bind.bind, Except.instMonad, Except.pure,
                  Except.bind] at computed
                cases bodyComputed : inferRegularType
                    (.snoc context domFormed.down) body with
                | error failure =>
                    rw [bodyComputed] at computed
                    cases computed
                | ok bodyInfo =>
                    rw [bodyComputed] at computed
                    dsimp [Pure.pure, Bind.bind, Except.instMonad, Except.pure,
                      Except.bind] at computed
                    cases codFormedComputed : bodyInfo.resultFormed? with
                    | error failure =>
                        rw [codFormedComputed] at computed
                        cases computed
                    | ok codFormed =>
                        rw [codFormedComputed] at computed
                        cases computed
                        exact .betaApp domFormed.down
                          (inferRegularType_reflects context argument
                            argumentInfo argumentComputed)
                          codFormed.down
                          (inferRegularType_reflects
                            (.snoc context domFormed.down) body bodyInfo
                            bodyComputed)
      · have notLambda : ∀ body, function ≠ .lam body := by
          intro body equal
          exact isLambda ⟨body, equal⟩
        rw [inferRegularType.eq_10 _ _ _ _ _ notLambda] at computed
        cases functionComputed : inferRegularType context function with
        | error failure =>
            rw [functionComputed] at computed
            cases computed
        | ok functionInfo =>
            rw [functionComputed] at computed
            dsimp [Pure.pure, Bind.bind, Except.instMonad, Except.pure,
              Except.bind] at computed
            cases viewComputed : regularPiView? context functionInfo.status with
            | none =>
                rw [viewComputed] at computed
                cases computed
            | some view =>
                rw [viewComputed] at computed
                dsimp [Pure.pure, Bind.bind, Except.instMonad, Except.pure,
                  Except.bind] at computed
                cases argumentComputed : checkRegularFormed context argument
                    view.dom view.domFormed with
                | error failure =>
                    rw [argumentComputed] at computed
                    cases computed
                | ok argumentChecked =>
                    rw [argumentComputed] at computed
                    cases computed
                    exact .app notLambda
                      (view.sourceFormed context functionInfo.typing)
                      (inferRegularType_reflects context function functionInfo
                        functionComputed)
                      view
                      (checkRegularFormed_reflects context argument view.dom
                        view.domFormed argumentChecked argumentComputed)
  | pair first second =>
      rw [inferRegularType.eq_11] at computed
      cases computed
  | fst pair =>
      rw [inferRegularType.eq_12] at computed
      cases pairComputed : inferRegularType context pair with
      | error failure =>
          rw [pairComputed] at computed
          cases computed
      | ok pairInfo =>
          rw [pairComputed] at computed
          dsimp [Pure.pure, Bind.bind, Except.instMonad, Except.pure,
            Except.bind] at computed
          cases viewComputed : regularSigmaView? context pairInfo.status with
          | none =>
              rw [viewComputed] at computed
              cases computed
          | some view =>
              rw [viewComputed] at computed
              cases computed
              exact .fst (view.sourceFormed context pairInfo.typing)
                (inferRegularType_reflects context pair pairInfo pairComputed)
                view
  | snd pair =>
      rw [inferRegularType.eq_13] at computed
      cases pairComputed : inferRegularType context pair with
      | error failure =>
          rw [pairComputed] at computed
          cases computed
      | ok pairInfo =>
          rw [pairComputed] at computed
          dsimp [Pure.pure, Bind.bind, Except.instMonad, Except.pure,
            Except.bind] at computed
          cases viewComputed : regularSigmaView? context pairInfo.status with
          | none =>
              rw [viewComputed] at computed
              cases computed
          | some view =>
              rw [viewComputed] at computed
              cases computed
              exact .snd (view.sourceFormed context pairInfo.typing)
                (inferRegularType_reflects context pair pairInfo pairComputed)
                view
  | refl term =>
      rw [inferRegularType.eq_14] at computed
      cases termComputed : inferRegularType context term with
      | error failure =>
          rw [termComputed] at computed
          cases computed
      | ok termInfo =>
          rw [termComputed] at computed
          dsimp [Pure.pure, Bind.bind, Except.instMonad, Except.pure,
            Except.bind] at computed
          cases carrierComputed : termInfo.resultFormed? with
          | error failure =>
              rw [carrierComputed] at computed
              cases computed
          | ok carrierFormed =>
              rw [carrierComputed] at computed
              cases computed
              exact .refl carrierFormed.down
                (inferRegularType_reflects context term termInfo termComputed)
termination_by 2 * sizeOf term
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals simp_wf <;> omega

theorem checkRegularFormed_reflects {Γ : Ctx n} (context : RegularCtx Γ)
    (term expected : PureTm n)
    (expectedFormed : RegularHasType Γ expected .u1)
    (checked : RegularChecked (Γ := Γ) term expected)
    (computed : checkRegularFormed context term expected expectedFormed =
      .ok checked) : RegularChecksFormed context term expected := by
  have fallback (notLambda : ∀ body, term ≠ .lam body)
      (notPair : ∀ first second, term ≠ .pair first second) :
      RegularChecksFormed context term expected := by
    rw [checkRegularFormed.eq_3 _ _ _ _ _ _ notLambda notPair] at computed
    cases inferredComputed : inferRegularType context term with
    | error failure =>
        rw [inferredComputed] at computed
        cases computed
    | ok inferred =>
        rw [inferredComputed] at computed
        dsimp [Pure.pure, Bind.bind, Except.instMonad, Except.pure,
          Except.bind] at computed
        split at computed
        · rename_i accepted
          exact .convert notLambda notPair
            (inferRegularType_reflects context term inferred inferredComputed)
            expectedFormed
            ((decideRegularConversion_correct context inferred.status
              (.formed expectedFormed)).1 accepted)
        · cases computed
  cases term with
  | lam body =>
      rw [checkRegularFormed.eq_1] at computed
      cases viewComputed : regularPiView? context (.formed expectedFormed) with
      | none =>
          rw [viewComputed] at computed
          cases computed
      | some view =>
          rw [viewComputed] at computed
          dsimp [Pure.pure, Bind.bind, Except.instMonad, Except.pure,
            Except.bind] at computed
          cases bodyComputed : checkRegularFormed
              (.snoc context view.domFormed) body view.cod view.codFormed with
          | error failure =>
              rw [bodyComputed] at computed
              cases computed
          | ok bodyChecked =>
              rw [bodyComputed] at computed
              exact .lambda expectedFormed view
                (checkRegularFormed_reflects (.snoc context view.domFormed)
                  body view.cod view.codFormed bodyChecked bodyComputed)
  | pair first second =>
      rw [checkRegularFormed.eq_2] at computed
      cases viewComputed : regularSigmaView? context (.formed expectedFormed) with
      | none =>
          rw [viewComputed] at computed
          cases computed
      | some view =>
          rw [viewComputed] at computed
          dsimp [Pure.pure, Bind.bind, Except.instMonad, Except.pure,
            Except.bind] at computed
          cases firstComputed : checkRegularFormed context first view.dom
              view.domFormed with
          | error failure =>
              rw [firstComputed] at computed
              cases computed
          | ok firstChecked =>
              rw [firstComputed] at computed
              dsimp [Pure.pure, Bind.bind, Except.instMonad, Except.pure,
                Except.bind] at computed
              have secondFormed : RegularHasType Γ (inst0 first view.cod) .u1 := by
                simpa [inst0, subst] using view.codFormed.instantiate
                  firstChecked.typing context.constantFreeCtx
              cases secondComputed : checkRegularFormed context second
                  (inst0 first view.cod) secondFormed with
              | error failure =>
                  rw [secondComputed] at computed
                  cases computed
              | ok secondChecked =>
                  rw [secondComputed] at computed
                  exact .pair expectedFormed view
                    (checkRegularFormed_reflects context first view.dom
                      view.domFormed firstChecked firstComputed)
                    (checkRegularFormed_reflects context second
                      (inst0 first view.cod) secondFormed secondChecked
                      secondComputed)
  | var index => exact fallback (by simp) (by simp)
  | const name => exact fallback (by simp) (by simp)
  | u0 => exact fallback (by simp) (by simp)
  | u1 => exact fallback (by simp) (by simp)
  | pi dom cod => exact fallback (by simp) (by simp)
  | sigma dom cod => exact fallback (by simp) (by simp)
  | id carrier left right => exact fallback (by simp) (by simp)
  | app function argument => exact fallback (by simp) (by simp)
  | fst pair => exact fallback (by simp) (by simp)
  | snd pair => exact fallback (by simp) (by simp)
  | refl term => exact fallback (by simp) (by simp)
termination_by 2 * sizeOf term + 1
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals simp_wf <;> omega

end

/-! ## Exact public reflection and direct NIK authority -/

/-- A successful top-sort check reflects to the independent public judgment. -/
theorem checkRegularTop_reflects {Γ : Ctx n} (context : RegularCtx Γ)
    (term : PureTm n) (checked : RegularChecked (Γ := Γ) term .u1)
    (computed : checkRegularTop context term = .ok checked) :
    RegularPublicChecks context term .u1 := by
  unfold checkRegularTop at computed
  cases inferredComputed : inferRegularType context term with
  | error failure =>
      rw [inferredComputed] at computed
      cases computed
  | ok inferred =>
      rw [inferredComputed] at computed
      dsimp [Pure.pure, Bind.bind, Except.instMonad, Except.pure,
        Except.bind] at computed
      split at computed
      · rename_i accepted
        exact .top
          (inferRegularType_reflects context term inferred inferredComputed)
          ((decideRegularConversion_correct context inferred.status
            (.top rfl)).1 accepted)
      · cases computed

/-- Every successful public checker result is explained by the independent
bidirectional judgment. -/
theorem checkRegularType_reflects {Γ : Ctx n} (context : RegularCtx Γ)
    (term expected : PureTm n)
    (checked : RegularChecked (Γ := Γ) term expected)
    (computed : checkRegularType context term expected = .ok checked) :
    RegularPublicChecks context term expected := by
  by_cases top : expected = .u1
  · subst expected
    unfold checkRegularType at computed
    rw [dif_pos rfl] at computed
    exact checkRegularTop_reflects context term checked computed
  · unfold checkRegularType at computed
    rw [dif_neg top] at computed
    cases expectedComputed : inferRegularType context expected with
    | error failure =>
        rw [expectedComputed] at computed
        cases computed
    | ok expectedInfo =>
        rw [expectedComputed] at computed
        dsimp [Pure.pure, Bind.bind, Except.instMonad, Except.pure,
          Except.bind] at computed
        cases formedComputed : expectedInfo.asFormedType? context with
        | error failure =>
            rw [formedComputed] at computed
            cases computed
        | ok formed =>
            rw [formedComputed] at computed
            dsimp [Pure.pure, Bind.bind, Except.instMonad, Except.pure,
              Except.bind] at computed
            exact .formed
              (inferRegularType_reflects context expected expectedInfo
                expectedComputed)
              (expectedInfo.asFormedType?_reflects context formed
                formedComputed)
              (checkRegularFormed_reflects context term expected formed.down
                checked computed)

/-- The public Boolean reflects successful computation without retaining the
proof-bearing result package. -/
theorem regularCheckBool_reflects {Γ : Ctx n} (context : RegularCtx Γ)
    (term expected : PureTm n)
    (accepted : regularCheckBool context term expected = true) :
    RegularPublicChecks context term expected := by
  unfold regularCheckBool at accepted
  cases computed : checkRegularType context term expected with
  | error failure =>
      rw [computed] at accepted
      cases accepted
  | ok checked =>
      exact checkRegularType_reflects context term expected checked computed

/-- Exact agreement between the executable bit and the independently stated
regular bidirectional calculus. -/
theorem regularCheckBool_correct {Γ : Ctx n} (context : RegularCtx Γ)
    (term expected : PureTm n) :
    regularCheckBool context term expected = true ↔
      RegularPublicChecks context term expected := by
  constructor
  · exact regularCheckBool_reflects context term expected
  · exact regularCheckBool_complete

/-- A closed package for a regular typing query.  The context proof is part of
the trusted input description, while acceptance itself remains a direct
Boolean decision. -/
structure RegularTypingClaim where
  arity : Nat
  contextSyntax : Ctx arity
  context : RegularCtx contextSyntax
  term : PureTm arity
  expected : PureTm arity

/-- Independent meaning of a packaged regular typing query. -/
def RegularTypingClaim.Meaning (claim : RegularTypingClaim) : Prop :=
  RegularPublicChecks claim.context claim.term claim.expected

/-- The regular checker is a direct decision kernel: it recomputes conversion
and carries no certificate on the ordinary path. -/
def regularTypingDecisionKernel :
    Mettapedia.GSLT.LanguageDef.KernelAuthority.Checker.DecisionKernel
      RegularTypingClaim RegularTypingClaim.Meaning where
  decide := fun claim =>
    regularCheckBool claim.context claim.term claim.expected
  correct := fun claim =>
    regularCheckBool_correct claim.context claim.term claim.expected

/-- Positive direct-kernel witness. -/
def regularTypingPositiveClaim : RegularTypingClaim where
  arity := 0
  contextSyntax := .nil
  context := .nil
  term := .u0
  expected := .u1

theorem regularTypingDecisionKernel_accepts_positive :
    regularTypingDecisionKernel.decide regularTypingPositiveClaim = true := by
  exact regularCheckBool_complete regularPublic_u0_u1

/-- Negative direct-kernel witness. -/
def regularTypingNegativeClaim : RegularTypingClaim where
  arity := 0
  contextSyntax := .nil
  context := .nil
  term := .u1
  expected := .u1

theorem regularTypingDecisionKernel_rejects_negative :
    regularTypingDecisionKernel.decide regularTypingNegativeClaim = false := by
  apply Bool.eq_false_of_not_eq_true
  intro accepted
  exact regularPublic_u1_rejected
    ((regularTypingDecisionKernel.correct regularTypingNegativeClaim).1 accepted)

/-! ## Axiom audit -/

#print axioms RegularBidirectional.sound
#print axioms RegularBidirectional.complete
#print axioms inferRegularType_reflects
#print axioms checkRegularFormed_reflects
#print axioms regularCheckBool_correct
#print axioms regularTypingDecisionKernel
#print axioms regularTypingDecisionKernel_accepts_positive
#print axioms regularTypingDecisionKernel_rejects_negative

end Mettapedia.Languages.MeTTa.Pure.Intrinsic.PresentationBoundary
