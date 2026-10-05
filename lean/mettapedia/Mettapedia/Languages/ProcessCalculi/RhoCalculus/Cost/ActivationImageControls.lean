import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationCodeImage
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationOccurrencePathControls
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationAuthoredBorrowingBoundary
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationAuthoredWholeControls

/-!
# Controls for the image of generated syntax and for the firing of a funded redex

* The authored image of unsigned rho code (`ActivationCodeImage.AuthoredCodeImage`, seals taken
  from a function of the caller) and the image of generated syntax are different notions. An
  authored image may carry a seal of two atoms; no image of generated syntax does. An authored
  image never contains a signed pair, which is the left side of the generated rule.
* The image and raw admission (`CodeAdmitted`) differ in both directions. A raw term may be
  admitted and still not be the encoding of any image: admission allows any parallel tree, while
  the readout of a bag always ends in `nil`. A raw term whose normal form is the encoding of an
  image may be rejected by admission: an open name under a quote.
* A funded redex fires whatever the shape of the generated syntax: an unfunded contact inside a
  funded contact, at a closed nonempty channel, fires with the outer purse, although the generated
  language has no step from that syntax. A redex beside a purse whose head is another key does
  not fire (`ActivationLocatedControls.actual_wrong_key_catalogue_empty`).
* A concrete runtime firing is the generated step at its place (`FiringIsGeneratedStep`). The
  place matters: the generated rule has no step on the whole bag of contact and frame
  (`selected_R1_does_not_authorize_frame`), and none from a contact nested in a funded contact,
  which the runtime fires.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationImageControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open ActivationGenerated ActivationGenerated.SerializationAdmission

/-! ## The authored image says something different -/

/-- Every seal in an image of generated syntax is one literal authority. -/
theorem signed_image_singleton {depth : Nat} {source : Pattern}
    {process : CostProc LiteralAuthority} {signature : CostSig LiteralAuthority}
    (image : CodeImage depth source (.signed process signature)) :
    ∃ authority : Pattern, signature = {authority} := by
  generalize same : CostTerm.signed process signature = term at image
  cases image with
  | signed typed _ _ =>
    injection same with _ sealSame
    exact ⟨_, sealSame.trans typed.property.1⟩
  | zero => cases same
  | drop _ => cases same
  | collection codes =>
    subst same
    cases codes

def literalNilEncoding : SignatureNameEncoding LiteralAuthority :=
  fun _ => .apply "NQuote" [.apply "PZero" []]

def twoAtomSeal : Pattern → CostSig LiteralAuthority :=
  fun _ => {.apply "A" []} + {.apply "B" []}

def twoAtomSealedPayload : CostTerm LiteralAuthority :=
  .signed (.send (.quote .nil) .nil) ({.apply "A" []} + {.apply "B" []})

/-- Positive for the authored image, negative for the generated one: a seal of two atoms. -/
theorem authored_two_atom_seal_is_not_generated :
    ActivationCodeImage.AuthoredCodeImage literalNilEncoding twoAtomSeal FreeSortContext.empty []
        ActivationCodeImage.authoredNonemptyPayload twoAtomSealedPayload ∧
      ∀ depth source, ¬ CodeImage depth source twoAtomSealedPayload := by
  refine ⟨⟨ActivationCodeImage.authored_nonempty_payload_sorted, 12, by decide +kernel⟩, ?_⟩
  intro depth source image
  obtain ⟨authority, same⟩ := signed_image_singleton image
  have cards := congrArg Multiset.card same
  simp at cards

theorem wrapList_nil_or_par {Ground : Type} (encoding : SignatureNameEncoding Ground)
    (signatureFor : Pattern → CostSig Ground) (fuel : Nat) (sources : List Pattern)
    {wrapped : ActivationCodeImage.WrappedCode encoding (.collection .hashBag sources none)}
    (compiled : ActivationCodeImage.wrapList encoding signatureFor fuel sources = some wrapped) :
    wrapped.val = .nil ∨ ∃ head tail, wrapped.val = .par head tail := by
  cases fuel with
  | zero => simp [ActivationCodeImage.wrapList] at compiled
  | succ fuel =>
    cases sources with
    | nil =>
      simp only [ActivationCodeImage.wrapList, Option.some.injEq] at compiled
      subst compiled
      exact .inl rfl
    | cons source sources =>
      simp only [ActivationCodeImage.wrapList, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at compiled
      obtain ⟨_, _, _, _, same⟩ := compiled
      subst same
      exact .inr ⟨_, _, rfl⟩

/-- The authored compiler signs every send and every receive on its own: it never returns a
signed pair. -/
theorem wrapCode_no_signed_pair {Ground : Type} (encoding : SignatureNameEncoding Ground)
    (signatureFor : Pattern → CostSig Ground) (fuel : Nat) (source : Pattern)
    {wrapped : ActivationCodeImage.WrappedCode encoding source}
    (compiled : ActivationCodeImage.wrapCode encoding signatureFor fuel source = some wrapped)
    (first second : CostProc Ground) (signature : CostSig Ground) :
    wrapped.val ≠ .signed (.par first second) signature := by
  induction fuel, source using ActivationCodeImage.wrapCode.induct
    (motive_1 := fun _ _ => True) (motive_3 := fun _ _ => True) with
  | case1 => trivial
  | case2 => trivial
  | case3 => trivial
  | case4 => trivial
  | case5 => simp [ActivationCodeImage.wrapCode] at compiled
  | case6 =>
    simp only [ActivationCodeImage.wrapCode, Option.some.injEq] at compiled
    subst compiled
    intro same; cases same
  | case7 =>
    simp only [ActivationCodeImage.wrapCode, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at compiled
    obtain ⟨_, _, same⟩ := compiled
    subst same
    intro same; cases same
  | case8 =>
    simp only [ActivationCodeImage.wrapCode, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at compiled
    obtain ⟨_, _, _, _, same⟩ := compiled
    subst same
    intro same; cases same
  | case9 =>
    simp only [ActivationCodeImage.wrapCode, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at compiled
    obtain ⟨_, _, _, _, same⟩ := compiled
    subst same
    intro same; cases same
  | case10 fuel sources _ =>
    simp only [ActivationCodeImage.wrapCode] at compiled
    intro same
    rcases wrapList_nil_or_par encoding signatureFor _ _ compiled with nil | ⟨_, _, par⟩
    · rw [nil] at same; cases same
    · rw [par] at same; cases same
  | case11 n x notZero notDrop notOutput notInput notBag =>
    rw [ActivationCodeImage.wrapCode.eq_def] at compiled
    simp_all
  | case12 => trivial
  | case13 => trivial
  | case14 => trivial

/-- Negative: no authored image is a signed pair, the left side of the generated rule. -/
theorem authored_image_has_no_whole_redex {Ground : Type}
    {encoding : SignatureNameEncoding Ground} {signatureFor : Pattern → CostSig Ground}
    {free : FreeSortContext} {bound : List String} {source : Pattern}
    (first second : CostProc Ground) (signature : CostSig Ground) :
    ¬ ActivationCodeImage.AuthoredCodeImage encoding signatureFor free bound source
      (.signed (.par first second) signature) := by
  rintro ⟨_, fuel, compiled⟩
  obtain ⟨wrapped, compiledSome, same⟩ := Option.map_eq_some_iff.mp compiled
  exact wrapCode_no_signed_pair encoding signatureFor fuel source compiledSome first second signature same

/-! ## Raw admission and the image differ in both directions -/

def signedZero : RawCostTerm :=
  .signed .nil [literalAuthorityKey ActivationLocatedControls.unitSource]

theorem signedZero_admitted : CodeAdmitted 0 signedZero :=
  .signed .zero (.accepted ActivationLocatedControls.unitTyped ActivationLocatedControls.unit_accepted)

theorem list_image_literal_nil_or_par {depth : Nat} {sources : List Pattern}
    {term : CostTerm LiteralAuthority} (image : CodeListImage depth sources term) :
    literalEncodeTerm term = .nil ∨ ∃ head tail, literalEncodeTerm term = .par head tail := by
  cases image with
  | nil => exact .inl rfl
  | cons _ _ => exact .inr ⟨_, _, rfl⟩

/-- Admitted, but not the encoding of any image. -/
theorem admitted_par_not_image_encoding :
    CodeAdmitted 0 (.par signedZero signedZero) ∧
      ∀ depth source term, CodeImage depth source term →
        literalEncodeTerm term ≠ .par signedZero signedZero := by
  refine ⟨.par signedZero_admitted signedZero_admitted, ?_⟩
  intro depth source term image same
  cases image with
  | zero => cases same
  | drop _ => cases same
  | signed _ _ _ => cases same
  | collection codes =>
    cases codes with
    | nil => cases same
    | cons _ tail =>
      injection same with _ tailSame
      have encoded : literalEncodeTerm _ = signedZero := tailSame
      rcases list_image_literal_nil_or_par tail with nil | ⟨_, _, par⟩
      · rw [nil] at encoded; cases encoded
      · rw [par] at encoded; cases encoded

/-- The normal form of a rejected raw term is the encoding of an image: under a quote the name
`bvar 0` is open, and admission rejects it, because substitution does not look under a quote. -/
theorem image_normal_form_not_admitted :
    CodeImage 1 (.apply "$cost:wrapped-constructor:PDrop" [.bvar 0]) (.drop (.bvar 0)) ∧
      (RawCostTerm.drop (.quote (.drop (.bvar 0)))).normalize = literalEncodeTerm (.drop (.bvar 0)) ∧
      ¬ CodeAdmitted 1 (.drop (.quote (.drop (.bvar 0)))) :=
  ⟨.drop (.bvar (by decide)), by decide,
    ActivationOccurrencePathControls.receiver_open_quote_rejected⟩

/-! ## A funded redex fires whatever the shape of the generated syntax -/

open ActivationLocatedControls in
/-- An unfunded contact inside a funded contact at a closed nonempty channel fires with the
outer purse, by `ConfigImage.funded_redex_fires`; the generated language has no step from this
syntax. -/
theorem nested_contact_fires_without_generated_step :
    (∃ step,
      step ∈ runtimeCostCandidatesFromConfig
        (literalEncodeTerm (decodedBorrowedReceiver channel (.drop (.bvar 0)) payload {unitSource}
          .empty)).normalizeConfig ∧
      decodeCostName step.location = decodeCostName (literalEncodeName channel).normalize ∧
      decodeCostSig step.spend = {literalAuthorityKey unitSource} ∧
      ∃ path : CostPath 0
          (initialTraceComponents (literalEncodeTerm
            (decodedBorrowedReceiver channel (.drop (.bvar 0)) payload {unitSource} .empty)))
          1 (applyTracedStep (initialTraceComponents (literalEncodeTerm
            (decodedBorrowedReceiver channel (.drop (.bvar 0)) payload {unitSource} .empty))) step 0),
        path.depth = 1) ∧
    ∀ target, ¬ Step (.reflection rhoCIGSLT.costWholeReflectionProfile)
      (Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises
        Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty) rhoCIGSLT.costWholeLanguage
      (borrowedReceiverSource channelSource boundBodySource payloadSource unitSource emptySource)
      target := by
  have bodyImage : CodeImage 1 boundBodySource (.drop (.bvar 0)) := .drop (.bvar (by decide))
  have image := borrowed_receiver_image channel_image bodyImage payload_image unitTyped unit_accepted
    StackImage.empty
  obtain ⟨_, step, _, _, enabled, located, spent, _, path, _⟩ :=
    image.funded_redex_fires channel_image bodyImage payload_image (.whole unitTyped .empty)
      {CostTerm.purse channel .empty} (by
        simp only [decodedBorrowedReceiver, decodedReceiverSource, Funding.redex, locatedContact,
          CostTerm.components, Multiset.cons_zero]
        abel)
  exact ⟨⟨step, enabled, located, spent, path⟩,
    fun target => borrowed_receiver_no_authored_step _ _ _ _ _ _ target⟩

open ActivationAuthoredWholeControls in
/-- Positive: the firing of the receiver that returns what it receives, with a nonempty tail and
an empty purse in the frame, is the generated step at its place. -/
theorem concrete_firing_is_generated_step :
    ∃ cover : RawWholeOccurrenceCover config,
      cover.selected = [selectedPurse] ∧ cover.runtimeStep ∈ runtimeCostCandidatesFromConfig config ∧
      FiringIsGeneratedStep nilChannelLocation config cover source
        (receiverContractum ActivationLocatedControls.boundBodySource ActivationLocatedControls.zeroSource
          tailSource) := by
  obtain ⟨cover, result, frameSource, frame, _, selected, enabled, targetImage, frameImage, sourceBag,
    observed⟩ := actual_same_purse_rhs
  exact ⟨cover, selected, enabled, authored_step, frameSource, .par decoded (.par frame .nil),
    .par (locatedContact nilChannelLocation (.par result .nil) tail) (.par frame .nil),
    .collection (.cons source_image (.cons frameImage .nil)),
    .collection (.cons targetImage (.cons frameImage .nil)), sourceBag, observed⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationImageControls
