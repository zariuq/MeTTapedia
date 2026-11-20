import Mettapedia.OSLF.MeTTaIL.Complete.WrapperCoherence
import Mettapedia.OSLF.MeTTaIL.Complete.RhoQuoteDrop

/-!
# Rho modulo its declared collection algebra and the name equation

Rho's parallel composition `PPar` is a bare bag constructor with unit `PZero`; its collection algebra
declares, besides flattening and unit absorption, that a singleton composition is its process and the
empty one is `PZero`. The explorer that commits the model's canonical form explores every closed process
reachable by steps modulo the parallel laws, the two wrapper laws and `@(*n) = n`, up to all of them
(`rho_explores_wrappers`).

Rho meets every condition: `PPar` is homogeneous with its unit at the same sort, no other parameter
mentions a bag, COMM matches a bag of two explicit processes and a rest, its reduct keeps the rest and
substitutes an explicit quotation into the received body, its captures are names, processes and a bag
of processes, and no reduction context lies under a binder.

Positive example: the channels `@{}` and `@0` are one name (`emptyWrapper_identifies`); the quote-drop
model kept them apart. Negative example: a bag of two different messages is not either message
(`two_messages_separate`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Complete.RhoWrappers

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax GeneralExecutionAdmission CanonicalBags QuoteDrop RhoPresented
open Mettapedia.GSLT.LanguageDef.WellSorted Wrappers
open RhoQuoteDrop (presentation distinct typedPresentation quoteOpaque fires)

/-- **Rho types its wrapper laws**: `PPar` is homogeneous with the unit `PZero` of its sort, and no
other parameter mentions a bag. -/
theorem wrappersTyped : WrappersTyped (Normalized.laws GeneralRho.Standard.plan)
    (GeneralPlanEnvironment.environment GeneralRho.Standard.plan).language where
  homogeneous law kind found rule member name element parameters := by
    obtain ⟨rfl, _, rfl⟩ := bare_rule member parameters
    rfl
  units law kind found label unit rule member name element parameters := by
    obtain ⟨_, rfl⟩ := laws_found found
    obtain ⟨rfl, _, _⟩ := bare_rule member parameters
    simp only [Option.some.injEq] at unit
    subst unit
    exact ⟨rhoCalc.terms[0], by rw [terms_eq]; simp [rhoCalc], rfl, rfl, rfl⟩
  bareElements rule member name kind element parameters := by
    obtain ⟨_, _, rfl⟩ := bare_rule member parameters
    trivial
  parameters rule member notBare parameter parameterMember type typedParameter := by
    rcases mem_terms member with rfl | rfl | rfl | rfl | rfl | rfl
    · simp [rhoCalc] at parameterMember
    · simp only [rhoCalc, List.getElem_cons_zero, List.getElem_cons_succ, List.mem_cons, List.mem_nil_iff,
        or_false] at parameterMember
      subst parameterMember
      simp only [parameterType?, TypeExpr.name, TypeExpr.baseType, Option.some.injEq] at typedParameter
      subst typedParameter
      trivial
    · simp only [rhoCalc, List.getElem_cons_zero, List.getElem_cons_succ, List.mem_cons, List.mem_nil_iff,
        or_false] at parameterMember
      subst parameterMember
      simp only [parameterType?, TypeExpr.proc, TypeExpr.baseType, Option.some.injEq] at typedParameter
      subst typedParameter
      trivial
    · exact absurd ⟨_, _, _, rfl⟩ notBare
    · simp only [rhoCalc, List.getElem_cons_zero, List.getElem_cons_succ, List.mem_cons, List.mem_nil_iff,
        or_false] at parameterMember
      rcases parameterMember with rfl | rfl <;>
        simp only [parameterType?, TypeExpr.name, TypeExpr.proc, TypeExpr.baseType, Option.some.injEq] at typedParameter <;>
        subst typedParameter <;> trivial
    · simp only [rhoCalc, List.getElem_cons_zero, List.getElem_cons_succ, List.mem_cons, List.mem_nil_iff,
        or_false] at parameterMember
      rcases parameterMember with rfl | rfl <;>
        simp only [parameterType?, TypeExpr.name, TypeExpr.proc, TypeExpr.baseType, TypeExpr.funType,
          Option.some.injEq] at typedParameter <;>
        subst typedParameter <;> trivial

theorem lookup_mem {α β : Type} [BEq α] [LawfulBEq α] {key : α} {value : β} :
    ∀ {entries : List (α × β)}, entries.lookup key = some value → (key, value) ∈ entries
  | [], found => by simp [List.lookup] at found
  | (other, stored) :: rest, found => by
    simp only [List.lookup] at found
    split at found
    · rename_i same
      cases found
      rw [beq_iff_eq.mp same]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (lookup_mem found)

/-- **COMM fires at wrapper normal forms.** -/
theorem wrapperFires : RulesFireAtWrapper (Normalized.laws GeneralRho.Standard.plan) GeneralRho.Standard.plan
    presentation := by
  intro declaration ordinal member rule spec selected specified
  obtain ⟨rfl, rfl, rfl⟩ := rule_at member selected specified
  refine ⟨rfl, ["rest"], ?_, ?_, ?_, .inr ⟨GeneralRho.substitution_selected, ?_⟩⟩
  · rw [comm_left, laws_eq]
    decide +kernel
  · decide +kernel
  · intro name type found
    have entry := lookup_mem found
    simp only [GeneralRho.comm, rhoCommRewrite, List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff,
      or_false, Prod.mk.injEq] at entry
    rcases entry with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨fun _ => trivial, fun member => by simp at member⟩
    · exact ⟨fun _ => trivial, fun member => by simp at member⟩
    · exact ⟨fun _ => trivial, fun member => by simp at member⟩
    · exact ⟨fun notRest => absurd (by simp) notRest, fun _ => .inr ⟨.hashBag, .base "Proc", rfl, trivial⟩⟩
  · refine ⟨rfl, ?_⟩
    intro kind law found
    obtain ⟨rfl, rfl⟩ := laws_found found
    exact ⟨rfl, fun unit => (Option.some.inj unit).symm⟩

/-- **The explorer is complete for rho modulo its declared collection algebra and the name equation**:
every closed process reachable from a closed process by finitely many steps modulo the parallel laws,
`{P} = P`, `{} = 0` and `@(*n) = n` is explored from the canonical form of the process, up to all of
them. -/
theorem rho_explores_wrappers (source : Pattern) {target : Pattern}
    (reaches : (WrapperCoherence.gslt GeneralRho.Standard.plan [] (.base "Proc") presentation).MultiStep source target) :
    ∃ state, Explore.Explored (S := WrapperCoherence.search GeneralRho.Standard.plan [] (.base "Proc") presentation)
        (WrapperCoherence.commit GeneralRho.Standard.plan presentation source) state ∧
      WrapperCoherence.ModelEquiv GeneralRho.Standard.plan [] (.base "Proc") presentation state target :=
  WrapperCoherence.presented_explores_wrappers checked (noEquations [] (.base "Proc")) distinct extrusions_eq canonical
    descentAdmissible (show LawTypeOk _ _ (.base "Proc") from trivial) wrappersTyped typedPresentation quoteOpaque fires
    rfl rfl trivial wrapperFires source reaches

/-! ## Examples -/

/-- The empty process `0`. -/
def zero : Pattern := .apply "PZero" []

/-- Sending `0` on a channel. -/
def send (channel : Pattern) : Pattern := .apply "POutput" [channel, zero]

theorem bagLaw : CollectionLaws.lawFor (Normalized.laws GeneralRho.Standard.plan) .hashBag =
    some ⟨.hashBag, some "PZero"⟩ := by
  rw [laws_eq]; rfl

/-- **Positive example**: the channels `@{}` and `@0` are one name; the quote-drop model kept them
apart. -/
theorem emptyWrapper_identifies :
    WrapperCoherence.commit GeneralRho.Standard.plan presentation (send (.apply "NQuote" [.collection .hashBag [] none])) =
      WrapperCoherence.commit GeneralRho.Standard.plan presentation (send (.apply "NQuote" [zero])) :=
  ModelMove.modelCanon_eq distinct (.inr (.inr (WrapperStep.apply (label := "POutput") (before := []) (after := [zero])
    (WrapperStep.apply (label := "NQuote") (before := []) (after := []) (WrapperStep.empty bagLaw rfl)))))

/-- **Positive example**: the channel `@{*@0}` is the name `@0`: collapsing the wrapper exposes a
quote-drop pair. -/
theorem wrapper_exposes_quoteDrop :
    WrapperCoherence.commit GeneralRho.Standard.plan presentation
        (send (.apply "NQuote" [.collection .hashBag [.apply "PDrop" [.apply "NQuote" [zero]]] none])) =
      WrapperCoherence.commit GeneralRho.Standard.plan presentation (send (.apply "NQuote" [zero])) := by
  have collapse := ModelMove.modelCanon_eq (laws := Normalized.laws GeneralRho.Standard.plan) distinct
    (.inr (.inr (WrapperStep.apply (label := "POutput") (before := []) (after := [zero])
      (WrapperStep.apply (label := "NQuote") (before := []) (after := [])
        (WrapperStep.singleton (element := .apply "PDrop" [.apply "NQuote" [zero]]) bagLaw)))))
  have quoteDrop := ModelMove.modelCanon_eq (laws := Normalized.laws GeneralRho.Standard.plan) distinct
    (.inr (.inl (QuoteDropStep.apply (label := "POutput") (before := []) (after := [zero])
      (QuoteDropStep.collapse (declaration := presentation) (.apply "NQuote" [zero])))))
  exact collapse.trans quoteDrop

/-- A message's model normal form is a message. -/
theorem modelNormal_send (channel : Pattern) :
    ∃ arguments, modelNormal (Normalized.laws GeneralRho.Standard.plan) presentation (send channel) =
      .apply "POutput" arguments ∧ arguments.length = 2 := by
  refine ⟨[modelNormal (Normalized.laws GeneralRho.Standard.plan) presentation channel,
    modelNormal (Normalized.laws GeneralRho.Standard.plan) presentation zero], ?_, rfl⟩
  rw [send, modelNormal, finish_not_quote (by decide)]
  rfl

/-- **Negative example**: parallel composition is not idempotent; two copies of a message are not the
message. -/
theorem two_copies_separate :
    WrapperCoherence.commit GeneralRho.Standard.plan presentation
        (.collection .hashBag [send (.apply "NQuote" [zero]), send (.apply "NQuote" [zero])] none) ≠
      WrapperCoherence.commit GeneralRho.Standard.plan presentation (send (.apply "NQuote" [zero])) := by
  obtain ⟨arguments, normalIs, lengthIs⟩ := modelNormal_send (.apply "NQuote" [zero])
  have item : deepSplice ⟨.hashBag, some "PZero"⟩ (.apply "POutput" arguments) = [.apply "POutput" arguments] := by
    match arguments, lengthIs with
    | [_, _], _ => simp [deepSplice]
  have bag : modelNormal (Normalized.laws GeneralRho.Standard.plan) presentation
      (.collection .hashBag [send (.apply "NQuote" [zero]), send (.apply "NQuote" [zero])] none) =
      .collection .hashBag [.apply "POutput" arguments, .apply "POutput" arguments] none := by
    rw [modelNormal, bagLaw]
    simp only [List.map_cons, List.map_nil, normalIs, List.flatMap_cons, List.flatMap_nil, item, List.cons_append,
      List.nil_append, List.append_nil]
    rfl
  simp only [WrapperCoherence.commit, modelCanon, bag, normalIs, canon_collection, canon_apply]
  intro same
  cases same

end Mettapedia.OSLF.MeTTaIL.Complete.RhoWrappers
