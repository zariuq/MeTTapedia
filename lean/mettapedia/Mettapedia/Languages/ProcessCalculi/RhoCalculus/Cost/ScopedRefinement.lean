import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ScopedErasure
import Mettapedia.GSLT.Meredith.RhoExample
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT

/-!
# Scoped funded execution refines pure rho

Canonical erasure sends declarative funded configurations to the established
pure rho carrier.  Each binder-safe funded step becomes one COMM step of the
committed rho GSLT, and binder safety is preserved along declarative paths.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalTyping
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.PureBoundary
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.ScopedSemanticSubstitution
open Mettapedia.GSLT
open Mettapedia.GSLT.Meredith.RhoExample

universe u

/-- A signature interpretation lands in the closed name fiber derived from
the authored rho presentation.  This combines declaration-derived sorting
with quote-aware scope safety; either property alone is insufficient. -/
def SignatureNameEncoding.MapsToClosedRhoNames {Ground : Type u}
    (signatureName : SignatureNameEncoding Ground) : Prop :=
  ∀ signature, RhoClosedTermWellSorted rhoName (signatureName signature)

namespace SignatureNameEncoding.MapsToClosedRhoNames

/-- Closed rho-name encodings are well sorted in the empty free context. -/
theorem wellSorted {Ground : Type u}
    {signatureName : SignatureNameEncoding Ground}
    (closed : signatureName.MapsToClosedRhoNames) :
    signatureName.WellSorted FreeSortContext.empty := by
  intro signature
  exact ((rhoClosedTermWellSorted_name_iff _).mp (closed signature)).1

/-- Closed rho-name encodings cannot capture a surrounding binder. -/
theorem binderSafe {Ground : Type u}
    {signatureName : SignatureNameEncoding Ground}
    (closed : signatureName.MapsToClosedRhoNames) :
    ∀ signature,
      binderSafeAt "NQuote" 0 (signatureName signature) = true := by
  intro signature
  exact ((rhoClosedTermWellSorted_name_iff _).mp (closed signature)).2

end SignatureNameEncoding.MapsToClosedRhoNames

/-! ## Signature-encoding controls -/

/-- Positive: a constant interpretation by the closed quotation of nil lands
in the derived closed-name fiber. -/
example {Ground : Type u} :
    SignatureNameEncoding.MapsToClosedRhoNames
      (fun _ : CostSig Ground => (closedNilName.1 : Pattern)) := by
  intro _signature
  exact closedNilName.2

/-- Negative: being well sorted in a nonempty free-name context does not make
an interpretation a closed rho name.  Closing the GSLT carrier therefore
requires the stronger empty-context premise. -/
theorem exists_wellSorted_signatureEncoding_not_closed :
    ∃ (signatureName : SignatureNameEncoding Unit)
        (free : FreeSortContext),
      signatureName.WellSorted free ∧
        ¬signatureName.MapsToClosedRhoNames := by
  let free : FreeSortContext := fun name =>
    if name = "cost-authority" then some rhoReflectivePresentation.nameSort
    else none
  let signatureName : SignatureNameEncoding Unit :=
    fun _ => .fvar "cost-authority"
  refine ⟨signatureName, free, ?_, ?_⟩
  · intro _signature
    exact .fvar (by simp [free])
  · intro closed
    have typed :=
      ((rhoClosedTermWellSorted_name_iff _).mp (closed (0 : CostSig Unit))).1
    cases typed with
    | fvar lookup => simp [FreeSortContext.empty] at lookup

private theorem eraseList_procWellSorted
    {Ground : Type u} {signatureName : SignatureNameEncoding Ground}
    (signatureClosed : signatureName.MapsToClosedRhoNames) :
    ∀ (terms : List (CostTerm Ground)),
      (∀ term ∈ terms, term.BinderSafe) →
      ProcListWellSorted rhoReflectivePresentation FreeSortContext.empty []
        (terms.map (CostTerm.erase signatureName))
  | [], _ => .nil
  | term :: terms, safe => by
      exact .cons
        (by
          simpa using (safe term (by simp)).erase_wellSorted
            signatureClosed.wellSorted)
        (eraseList_procWellSorted signatureClosed terms (by
          intro candidate membership
          exact safe candidate (by simp [membership])))

private theorem eraseList_binderSafe
    {Ground : Type u} {signatureName : SignatureNameEncoding Ground}
    (signatureClosed : signatureName.MapsToClosedRhoNames) :
    ∀ (terms : List (CostTerm Ground)),
      (∀ term ∈ terms, term.BinderSafe) →
      binderSafeListAt "NQuote" 0
        (terms.map (CostTerm.erase signatureName)) = true
  | [], _ => by simp [binderSafeListAt]
  | term :: terms, safe => by
      simp [binderSafeListAt,
        (safe term (by simp)).erase_binderSafeAt signatureClosed.binderSafe,
        eraseList_binderSafe signatureClosed terms (by
          intro candidate membership
          exact safe candidate (by simp [membership]))]

/-- Canonical erasure of a binder-safe cost configuration inhabits the closed
process fiber mechanically derived from `rhoCalc`. -/
theorem CostConfig.eraseCanonical_closed
    {Ground : Type u} {signatureName : SignatureNameEncoding Ground}
    (signatureClosed : signatureName.MapsToClosedRhoNames)
    (config : CostConfig Ground) (safe : config.BinderSafe) :
    RhoClosedTermWellSorted rhoProc
      (CostConfig.eraseCanonical signatureName
        signatureClosed.wellSorted.hashSetFree config) := by
  revert safe
  refine Quotient.inductionOn config ?_
  intro terms safe
  have termsSafe : ∀ term ∈ terms, term.BinderSafe := by
    intro term membership
    exact safe term (by simpa using membership)
  have rawTyped :
      ProcWellSorted rhoReflectivePresentation FreeSortContext.empty []
        (.collection .hashBag
          (terms.map (CostTerm.erase signatureName)) none) :=
    .parallel (eraseList_procWellSorted signatureClosed terms termsSafe)
  have rawSafe :
      binderSafeAt "NQuote" 0
        (.collection .hashBag
          (terms.map (CostTerm.erase signatureName)) none) = true := by
    simpa [binderSafeAt] using
      eraseList_binderSafe signatureClosed terms termsSafe
  apply (rhoClosedTermWellSorted_process_iff _).mpr
  exact ⟨canonicalize_procWellSorted [] rawTyped,
    canonicalize_binderSafeAt _ 0 rawSafe⟩

/-- Canonical cost erasure packaged as a term of the one-root rho process
carrier. -/
def CostConfig.eraseCanonicalProcess
    {Ground : Type u} {signatureName : SignatureNameEncoding Ground}
    (signatureClosed : signatureName.MapsToClosedRhoNames)
    (config : CostConfig Ground) (safe : config.BinderSafe) : RhoProcess :=
  ⟨CostConfig.eraseCanonical signatureName
      signatureClosed.wellSorted.hashSetFree config,
    config.eraseCanonical_closed signatureClosed safe⟩

private theorem structuralParallelCongruenceTwo
    {left₁ left₂ right₁ right₂ : Pattern}
    (first : StructuralCongruence left₁ right₁)
    (second : StructuralCongruence left₂ right₂) :
    StructuralCongruence
      (.collection .hashBag [left₁, left₂] none)
      (.collection .hashBag [right₁, right₂] none) := by
  refine StructuralCongruence.par_cong [left₁, left₂] [right₁, right₂] rfl ?_
  intro index leftBound rightBound
  have indexBound : index < 2 := by simpa using leftBound
  have cases : index = 0 ∨ index = 1 := by omega
  rcases cases with rfl | rfl
  · simpa using first
  · simpa using second

/-- A pair of parallel bags flattens to concatenation. -/
private theorem parallelPair_structural_append (left right : List Pattern) :
    StructuralCongruence
      (.collection .hashBag
        [.collection .hashBag left none, .collection .hashBag right none] none)
      (.collection .hashBag (left ++ right) none) := by
  let leftBag : Pattern := .collection .hashBag left none
  let rightBag : Pattern := .collection .hashBag right none
  have swap : StructuralCongruence
      (.collection .hashBag [leftBag, rightBag] none)
      (.collection .hashBag [rightBag, leftBag] none) :=
    StructuralCongruence.par_perm _ _ (by simp [List.Perm.swap])
  have flattenLeft : StructuralCongruence
      (.collection .hashBag [rightBag, leftBag] none)
      (.collection .hashBag (rightBag :: left) none) := by
    simpa [leftBag] using StructuralCongruence.par_flatten [rightBag] left
  have moveRight : StructuralCongruence
      (.collection .hashBag (rightBag :: left) none)
      (.collection .hashBag (left ++ [rightBag]) none) :=
    StructuralCongruence.par_perm _ _ (by
      simpa using (List.perm_append_comm (l₁ := [rightBag]) (l₂ := left)))
  have flattenRight : StructuralCongruence
      (.collection .hashBag (left ++ [rightBag]) none)
      (.collection .hashBag (left ++ right) none) := by
    simpa [rightBag] using StructuralCongruence.par_flatten left right
  exact StructuralCongruence.trans _ _ _ swap
    (StructuralCongruence.trans _ _ _ flattenLeft
      (StructuralCongruence.trans _ _ _ moveRight flattenRight))

/-- Canonical configuration erasure is monoidal up to pure structural
congruence. -/
theorem CostConfig.eraseCanonical_add_structural
    {Ground : Type u} (signatureName : SignatureNameEncoding Ground)
    (signaturePure : ∀ signature, HashSetFree (signatureName signature))
    (left right : CostConfig Ground) :
    StructuralCongruence
      (CostConfig.eraseCanonical signatureName signaturePure (left + right))
      (.collection .hashBag
        [CostConfig.eraseCanonical signatureName signaturePure left,
         CostConfig.eraseCanonical signatureName signaturePure right] none) := by
  refine Quotient.inductionOn left ?_
  intro leftTerms
  refine Quotient.inductionOn right ?_
  intro rightTerms
  let leftRaw : Pattern := .collection .hashBag
    (leftTerms.map (CostTerm.erase signatureName)) none
  let rightRaw : Pattern := .collection .hashBag
    (rightTerms.map (CostTerm.erase signatureName)) none
  let combinedRaw : Pattern := .collection .hashBag
    ((leftTerms ++ rightTerms).map (CostTerm.erase signatureName)) none
  have combinedToRaw : StructuralCongruence
      (Canonical.canonicalize combinedRaw) combinedRaw :=
    StructuralCongruence.symm _ _ (Canonical.canonicalize_sound combinedRaw)
  have rawToPair : StructuralCongruence combinedRaw
      (.collection .hashBag [leftRaw, rightRaw] none) := by
    exact StructuralCongruence.symm _ _ (by
      simpa [leftRaw, rightRaw, combinedRaw, List.map_append] using
        parallelPair_structural_append
          (leftTerms.map (CostTerm.erase signatureName))
          (rightTerms.map (CostTerm.erase signatureName)))
  have pairToCanonical : StructuralCongruence
      (.collection .hashBag [leftRaw, rightRaw] none)
      (.collection .hashBag
        [Canonical.canonicalize leftRaw, Canonical.canonicalize rightRaw] none) :=
    structuralParallelCongruenceTwo
      (Canonical.canonicalize_sound leftRaw)
      (Canonical.canonicalize_sound rightRaw)
  simpa [CostConfig.eraseCanonical, combinedRaw, leftRaw, rightRaw,
    List.map_append] using
    StructuralCongruence.trans _ _ _ combinedToRaw
      (StructuralCongruence.trans _ _ _ rawToPair pairToCanonical)

/-- Singleton configurations erase to their term erasure. -/
theorem CostConfig.eraseCanonical_singleton_structural
    {Ground : Type u} (signatureName : SignatureNameEncoding Ground)
    (signaturePure : ∀ signature, HashSetFree (signatureName signature))
    (term : CostTerm Ground) :
    StructuralCongruence
      (CostConfig.eraseCanonical signatureName signaturePure (term ::ₘ 0))
      (term.erase signatureName) := by
  exact StructuralCongruence.trans _ _ _
    (StructuralCongruence.symm _ _
      (Canonical.canonicalize_sound
        (.collection .hashBag [term.erase signatureName] none)))
    (StructuralCongruence.par_singleton _)

/-- Empty configurations erase to the pure nil process. -/
theorem CostConfig.eraseCanonical_zero_structural
    {Ground : Type u} (signatureName : SignatureNameEncoding Ground)
    (signaturePure : ∀ signature, HashSetFree (signatureName signature)) :
    StructuralCongruence
      (CostConfig.eraseCanonical signatureName signaturePure 0)
      (.apply "PZero" []) := by
  exact StructuralCongruence.trans _ _ _
    (StructuralCongruence.symm _ _
      (Canonical.canonicalize_sound (.collection .hashBag [] none)))
    StructuralCongruence.par_empty

private theorem parallelZeros_structural :
    ∀ count : Nat,
      StructuralCongruence
        (.collection .hashBag (List.replicate count (.apply "PZero" [])) none)
        (.apply "PZero" [])
  | 0 => StructuralCongruence.par_empty
  | count + 1 => by
      have expand : StructuralCongruence
          (.collection .hashBag
            (.apply "PZero" [] :: List.replicate count (.apply "PZero" [])) none)
          (.collection .hashBag
            [.apply "PZero" [],
             .collection .hashBag (List.replicate count (.apply "PZero" [])) none] none) := by
        exact StructuralCongruence.symm _ _ (by
          simpa using StructuralCongruence.par_flatten [.apply "PZero" []]
            (List.replicate count (.apply "PZero" [])))
      have collapseTail := structuralParallelCongruenceTwo
        (StructuralCongruence.refl (.apply "PZero" []))
        (parallelZeros_structural count)
      simpa [List.replicate_succ] using StructuralCongruence.trans _ _ _ expand
        (StructuralCongruence.trans _ _ _ collapseTail
          (StructuralCongruence.par_nil_left (.apply "PZero" [])))

/-- Located bookkeeping purses disappear under computational erasure. -/
theorem LocatedPurse.eraseCanonical_configComponents_structural
    {Ground : Type u} (signatureName : SignatureNameEncoding Ground)
    (signaturePure : ∀ signature, HashSetFree (signatureName signature))
    (purses : Multiset (LocatedPurse Ground)) :
    StructuralCongruence
      (CostConfig.eraseCanonical signatureName signaturePure
        (LocatedPurse.configComponents purses))
      (.apply "PZero" []) := by
  refine Quotient.inductionOn purses ?_
  intro purseList
  have erasedList :
      (purseList.map LocatedPurse.toTerm).map (CostTerm.erase signatureName) =
        List.replicate purseList.length (.collection .hashBag [] none) := by
    induction purseList with
    | nil => rfl
    | cons purse rest induction =>
        simp [LocatedPurse.toTerm, induction, List.replicate_succ]
  have emptyToZero : StructuralCongruence
      (.collection .hashBag
        (List.replicate purseList.length (.collection .hashBag [] none)) none)
      (.collection .hashBag
        (List.replicate purseList.length (.apply "PZero" [])) none) := by
    refine StructuralCongruence.par_cong _ _ (by simp) ?_
    intro index leftBound rightBound
    simpa using StructuralCongruence.par_empty
  change StructuralCongruence
    (Canonical.canonicalize
      (.collection .hashBag
        ((purseList.map LocatedPurse.toTerm).map
          (CostTerm.erase signatureName)) none))
    (.apply "PZero" [])
  rw [erasedList]
  exact StructuralCongruence.trans _ _ _
    (StructuralCongruence.symm _ _ (Canonical.canonicalize_sound _))
    (StructuralCongruence.trans _ _ _ emptyToZero
      (parallelZeros_structural purseList.length))

/-- Flattening cost syntax into configuration components preserves its pure
meaning. -/
theorem CostTerm.eraseCanonical_components_structural
    {Ground : Type u} (signatureName : SignatureNameEncoding Ground)
    (signaturePure : ∀ signature, HashSetFree (signatureName signature)) :
    ∀ term : CostTerm Ground,
      StructuralCongruence
        (CostConfig.eraseCanonical signatureName signaturePure term.components)
        (term.erase signatureName)
  | .nil => by
      exact StructuralCongruence.trans _ _ _
        (CostConfig.eraseCanonical_zero_structural signatureName signaturePure)
        (StructuralCongruence.symm _ _ StructuralCongruence.par_empty)
  | .par left right => by
      exact StructuralCongruence.trans _ _ _
        (CostConfig.eraseCanonical_add_structural signatureName signaturePure
          left.components right.components)
        (structuralParallelCongruenceTwo
          (CostTerm.eraseCanonical_components_structural signatureName signaturePure left)
          (CostTerm.eraseCanonical_components_structural signatureName signaturePure right))
  | .signed process signature =>
      CostConfig.eraseCanonical_singleton_structural signatureName signaturePure _
  | .drop name =>
      CostConfig.eraseCanonical_singleton_structural signatureName signaturePure _
  | .purse surface stack =>
      CostConfig.eraseCanonical_singleton_structural signatureName signaturePure _

private theorem fundedTarget_toPureCommTarget
    {Ground : Type u} {signatureName : SignatureNameEncoding Ground}
    {free : FreeSortContext} (signatureTyped : signatureName.WellSorted free)
    (signaturePure : ∀ signature, HashSetFree (signatureName signature))
    (context : CostConfig Ground) (residual : Multiset (LocatedPurse Ground))
    {body payload : CostTerm Ground}
    (bodySafe : body.BinderSafeAt 1) (payloadSafe : payload.BinderSafe) :
    StructuralCongruence
      (CostConfig.eraseCanonical signatureName signaturePure
        (context + (body.commSubst payload).components +
          LocatedPurse.configComponents residual))
      (.collection .hashBag
        [semanticCommSubst (body.erase signatureName) (payload.erase signatureName),
         CostConfig.eraseCanonical signatureName signaturePure context] none) := by
  have outer := CostConfig.eraseCanonical_add_structural
    signatureName signaturePure
    (context + (body.commSubst payload).components)
    (LocatedPurse.configComponents residual)
  have inner := CostConfig.eraseCanonical_add_structural
    signatureName signaturePure context (body.commSubst payload).components
  have contractum := CostTerm.eraseCanonical_components_structural
    signatureName signaturePure (body.commSubst payload)
  have commute := bodySafe.erase_commSubst_structural signatureTyped payloadSafe
  have removePurses := LocatedPurse.eraseCanonical_configComponents_structural
    signatureName signaturePure residual
  have exposeInner : StructuralCongruence
      (CostConfig.eraseCanonical signatureName signaturePure
        (context + (body.commSubst payload).components))
      (.collection .hashBag
        [CostConfig.eraseCanonical signatureName signaturePure context,
         (body.commSubst payload).erase signatureName] none) :=
    StructuralCongruence.trans _ _ _ inner
      (structuralParallelCongruenceTwo (StructuralCongruence.refl _) contractum)
  have exposeAll : StructuralCongruence
      (CostConfig.eraseCanonical signatureName signaturePure
        (context + (body.commSubst payload).components +
          LocatedPurse.configComponents residual))
      (.collection .hashBag
        [.collection .hashBag
          [CostConfig.eraseCanonical signatureName signaturePure context,
           (body.commSubst payload).erase signatureName] none,
         .apply "PZero" []] none) :=
    StructuralCongruence.trans _ _ _ outer
      (structuralParallelCongruenceTwo exposeInner removePurses)
  have removeZero : StructuralCongruence
      (.collection .hashBag
        [.collection .hashBag
          [CostConfig.eraseCanonical signatureName signaturePure context,
           (body.commSubst payload).erase signatureName] none,
         .apply "PZero" []] none)
      (.collection .hashBag
        [CostConfig.eraseCanonical signatureName signaturePure context,
         (body.commSubst payload).erase signatureName] none) :=
    StructuralCongruence.par_nil_right _
  have commuteInside : StructuralCongruence
      (.collection .hashBag
        [CostConfig.eraseCanonical signatureName signaturePure context,
         (body.commSubst payload).erase signatureName] none)
      (.collection .hashBag
        [CostConfig.eraseCanonical signatureName signaturePure context,
         semanticCommSubst (body.erase signatureName) (payload.erase signatureName)] none) :=
    structuralParallelCongruenceTwo (StructuralCongruence.refl _) commute
  have reorder : StructuralCongruence
      (.collection .hashBag
        [CostConfig.eraseCanonical signatureName signaturePure context,
         semanticCommSubst (body.erase signatureName) (payload.erase signatureName)] none)
      (.collection .hashBag
        [semanticCommSubst (body.erase signatureName) (payload.erase signatureName),
         CostConfig.eraseCanonical signatureName signaturePure context] none) :=
    StructuralCongruence.par_comm _ _
  exact StructuralCongruence.trans _ _ _ exposeAll
    (StructuralCongruence.trans _ _ _ removeZero
      (StructuralCongruence.trans _ _ _ commuteInside reorder))

private theorem wholeRecvSendSource_toPureCommSource
    {Ground : Type u} (signatureName : SignatureNameEncoding Ground)
    (signaturePure : ∀ signature, HashSetFree (signatureName signature))
    (context : CostConfig Ground) (available : Multiset (LocatedPurse Ground))
    (channel : CostName Ground) (body payload : CostTerm Ground)
    (outerSig : CostSig Ground) :
    StructuralCongruence
      (CostConfig.eraseCanonical signatureName signaturePure
        (context +
          (.signed (.par (.recv channel body) (.send channel payload)) outerSig ::ₘ 0) +
          LocatedPurse.configComponents available))
      (.collection .hashBag
        [.apply "POutput" [channel.erase signatureName, payload.erase signatureName],
         .apply "PInput"
          [channel.erase signatureName, .lambda none (body.erase signatureName)],
         CostConfig.eraseCanonical signatureName signaturePure context] none) := by
  let redex : CostTerm Ground :=
    .signed (.par (.recv channel body) (.send channel payload)) outerSig
  have outer := CostConfig.eraseCanonical_add_structural signatureName signaturePure
    (context + (redex ::ₘ 0)) (LocatedPurse.configComponents available)
  have inner := CostConfig.eraseCanonical_add_structural signatureName signaturePure
    context (redex ::ₘ 0)
  have singleton := CostConfig.eraseCanonical_singleton_structural
    signatureName signaturePure redex
  have purses := LocatedPurse.eraseCanonical_configComponents_structural
    signatureName signaturePure available
  have exposeInner := StructuralCongruence.trans _ _ _ inner
    (structuralParallelCongruenceTwo (StructuralCongruence.refl _) singleton)
  have exposeAll := StructuralCongruence.trans _ _ _ outer
    (structuralParallelCongruenceTwo exposeInner purses)
  have removeZero := StructuralCongruence.par_nil_right
    (.collection .hashBag
      [CostConfig.eraseCanonical signatureName signaturePure context,
       redex.erase signatureName] none)
  have flatten : StructuralCongruence
      (.collection .hashBag
        [CostConfig.eraseCanonical signatureName signaturePure context,
         redex.erase signatureName] none)
      (.collection .hashBag
        [CostConfig.eraseCanonical signatureName signaturePure context,
         .apply "PInput"
          [channel.erase signatureName, .lambda none (body.erase signatureName)],
         .apply "POutput"
          [channel.erase signatureName, payload.erase signatureName]] none) := by
    simpa [redex, CostTerm.erase, CostProc.erase] using
      StructuralCongruence.par_flatten
        [CostConfig.eraseCanonical signatureName signaturePure context]
        [.apply "PInput"
          [channel.erase signatureName, .lambda none (body.erase signatureName)],
         .apply "POutput"
          [channel.erase signatureName, payload.erase signatureName]]
  have reorder : StructuralCongruence
      (.collection .hashBag
        [CostConfig.eraseCanonical signatureName signaturePure context,
         .apply "PInput"
          [channel.erase signatureName, .lambda none (body.erase signatureName)],
         .apply "POutput"
          [channel.erase signatureName, payload.erase signatureName]] none)
      (.collection .hashBag
        [.apply "POutput" [channel.erase signatureName, payload.erase signatureName],
         .apply "PInput"
          [channel.erase signatureName, .lambda none (body.erase signatureName)],
         CostConfig.eraseCanonical signatureName signaturePure context] none) := by
    apply StructuralCongruence.par_perm
    exact (List.Perm.swap _ _ [_]).trans
      ((List.Perm.cons _ (List.Perm.swap _ _ [])).trans
        (List.Perm.swap _ _ [_]))
  simpa [redex] using StructuralCongruence.trans _ _ _ exposeAll
    (StructuralCongruence.trans _ _ _ removeZero
      (StructuralCongruence.trans _ _ _ flatten reorder))

private theorem wholeSendRecvSource_toPureCommSource
    {Ground : Type u} (signatureName : SignatureNameEncoding Ground)
    (signaturePure : ∀ signature, HashSetFree (signatureName signature))
    (context : CostConfig Ground) (available : Multiset (LocatedPurse Ground))
    (channel : CostName Ground) (body payload : CostTerm Ground)
    (outerSig : CostSig Ground) :
    StructuralCongruence
      (CostConfig.eraseCanonical signatureName signaturePure
        (context +
          (.signed (.par (.send channel payload) (.recv channel body)) outerSig ::ₘ 0) +
          LocatedPurse.configComponents available))
      (.collection .hashBag
        [.apply "POutput" [channel.erase signatureName, payload.erase signatureName],
         .apply "PInput"
          [channel.erase signatureName, .lambda none (body.erase signatureName)],
         CostConfig.eraseCanonical signatureName signaturePure context] none) := by
  let redex : CostTerm Ground :=
    .signed (.par (.send channel payload) (.recv channel body)) outerSig
  have outer := CostConfig.eraseCanonical_add_structural signatureName signaturePure
    (context + (redex ::ₘ 0)) (LocatedPurse.configComponents available)
  have inner := CostConfig.eraseCanonical_add_structural signatureName signaturePure
    context (redex ::ₘ 0)
  have singleton := CostConfig.eraseCanonical_singleton_structural
    signatureName signaturePure redex
  have purses := LocatedPurse.eraseCanonical_configComponents_structural
    signatureName signaturePure available
  have exposeInner := StructuralCongruence.trans _ _ _ inner
    (structuralParallelCongruenceTwo (StructuralCongruence.refl _) singleton)
  have exposeAll := StructuralCongruence.trans _ _ _ outer
    (structuralParallelCongruenceTwo exposeInner purses)
  have removeZero := StructuralCongruence.par_nil_right
    (.collection .hashBag
      [CostConfig.eraseCanonical signatureName signaturePure context,
       redex.erase signatureName] none)
  have flatten : StructuralCongruence
      (.collection .hashBag
        [CostConfig.eraseCanonical signatureName signaturePure context,
         redex.erase signatureName] none)
      (.collection .hashBag
        [CostConfig.eraseCanonical signatureName signaturePure context,
         .apply "POutput"
          [channel.erase signatureName, payload.erase signatureName],
         .apply "PInput"
          [channel.erase signatureName, .lambda none (body.erase signatureName)]] none) := by
    simpa [redex, CostTerm.erase, CostProc.erase] using
      StructuralCongruence.par_flatten
        [CostConfig.eraseCanonical signatureName signaturePure context]
        [.apply "POutput"
          [channel.erase signatureName, payload.erase signatureName],
         .apply "PInput"
          [channel.erase signatureName, .lambda none (body.erase signatureName)]]
  have reorder : StructuralCongruence
      (.collection .hashBag
        [CostConfig.eraseCanonical signatureName signaturePure context,
         .apply "POutput" [channel.erase signatureName, payload.erase signatureName],
         .apply "PInput"
          [channel.erase signatureName, .lambda none (body.erase signatureName)]] none)
      (.collection .hashBag
        [.apply "POutput" [channel.erase signatureName, payload.erase signatureName],
         .apply "PInput"
          [channel.erase signatureName, .lambda none (body.erase signatureName)],
         CostConfig.eraseCanonical signatureName signaturePure context] none) := by
    apply StructuralCongruence.par_perm
    exact (List.Perm.swap _ _ [_]).trans
      (List.Perm.cons _ (List.Perm.swap _ _ []))
  simpa [redex] using StructuralCongruence.trans _ _ _ exposeAll
    (StructuralCongruence.trans _ _ _ removeZero
      (StructuralCongruence.trans _ _ _ flatten reorder))

private theorem splitSource_toPureCommSource
    {Ground : Type u} (signatureName : SignatureNameEncoding Ground)
    (signaturePure : ∀ signature, HashSetFree (signatureName signature))
    (context : CostConfig Ground) (available : Multiset (LocatedPurse Ground))
    (channel : CostName Ground) (body payload : CostTerm Ground)
    (recvSeal sendSeal : CostSig Ground) :
    StructuralCongruence
      (CostConfig.eraseCanonical signatureName signaturePure
        (context + (.signed (.recv channel body) recvSeal ::ₘ 0) +
          (.signed (.send channel payload) sendSeal ::ₘ 0) +
          LocatedPurse.configComponents available))
      (.collection .hashBag
        [.apply "POutput" [channel.erase signatureName, payload.erase signatureName],
         .apply "PInput"
          [channel.erase signatureName, .lambda none (body.erase signatureName)],
         CostConfig.eraseCanonical signatureName signaturePure context] none) := by
  let receive : CostTerm Ground := .signed (.recv channel body) recvSeal
  let send : CostTerm Ground := .signed (.send channel payload) sendSeal
  have outer := CostConfig.eraseCanonical_add_structural signatureName signaturePure
    (context + (receive ::ₘ 0) + (send ::ₘ 0))
    (LocatedPurse.configComponents available)
  have middle := CostConfig.eraseCanonical_add_structural signatureName signaturePure
    (context + (receive ::ₘ 0)) (send ::ₘ 0)
  have inner := CostConfig.eraseCanonical_add_structural signatureName signaturePure
    context (receive ::ₘ 0)
  have receiveSingleton := CostConfig.eraseCanonical_singleton_structural
    signatureName signaturePure receive
  have sendSingleton := CostConfig.eraseCanonical_singleton_structural
    signatureName signaturePure send
  have purses := LocatedPurse.eraseCanonical_configComponents_structural
    signatureName signaturePure available
  have exposeInner := StructuralCongruence.trans _ _ _ inner
    (structuralParallelCongruenceTwo
      (StructuralCongruence.refl _) receiveSingleton)
  have exposeMiddle := StructuralCongruence.trans _ _ _ middle
    (structuralParallelCongruenceTwo exposeInner sendSingleton)
  have exposeAll := StructuralCongruence.trans _ _ _ outer
    (structuralParallelCongruenceTwo exposeMiddle purses)
  have removeZero := StructuralCongruence.par_nil_right
    (.collection .hashBag
      [.collection .hashBag
        [CostConfig.eraseCanonical signatureName signaturePure context,
         receive.erase signatureName] none,
       send.erase signatureName] none)
  have wrapSend : StructuralCongruence
      (.collection .hashBag
        [.collection .hashBag
          [CostConfig.eraseCanonical signatureName signaturePure context,
           receive.erase signatureName] none,
         send.erase signatureName] none)
      (.collection .hashBag
        [.collection .hashBag
          [CostConfig.eraseCanonical signatureName signaturePure context,
           receive.erase signatureName] none,
         .collection .hashBag [send.erase signatureName] none] none) :=
    structuralParallelCongruenceTwo (StructuralCongruence.refl _)
      (StructuralCongruence.symm _ _
        (StructuralCongruence.par_singleton (send.erase signatureName)))
  have flatten : StructuralCongruence
      (.collection .hashBag
        [.collection .hashBag
          [CostConfig.eraseCanonical signatureName signaturePure context,
           receive.erase signatureName] none,
         .collection .hashBag [send.erase signatureName] none] none)
      (.collection .hashBag
        [CostConfig.eraseCanonical signatureName signaturePure context,
         receive.erase signatureName, send.erase signatureName] none) := by
    simpa using parallelPair_structural_append
      [CostConfig.eraseCanonical signatureName signaturePure context,
       receive.erase signatureName]
      [send.erase signatureName]
  have reorder : StructuralCongruence
      (.collection .hashBag
        [CostConfig.eraseCanonical signatureName signaturePure context,
         receive.erase signatureName, send.erase signatureName] none)
      (.collection .hashBag
        [send.erase signatureName, receive.erase signatureName,
         CostConfig.eraseCanonical signatureName signaturePure context] none) := by
    apply StructuralCongruence.par_perm
    exact (List.Perm.swap _ _ [_]).trans
      ((List.Perm.cons _ (List.Perm.swap _ _ [])).trans
        (List.Perm.swap _ _ [_]))
  simpa [receive, send, CostTerm.erase, CostProc.erase] using
    StructuralCongruence.trans _ _ _ exposeAll
      (StructuralCongruence.trans _ _ _ removeZero
        (StructuralCongruence.trans _ _ _ wrapSend
          (StructuralCongruence.trans _ _ _ flatten reorder)))

/-- A funded COMM whose canonical source and target expose one pure redex is
a step of the GSLT mechanically derived from `rhoCalc`. -/
private theorem fundedCommErasure_rhoLanguageDefGSLTStep
    {Ground : Type u} {signatureName : SignatureNameEncoding Ground}
    (signatureClosed : signatureName.MapsToClosedRhoNames)
    {source target context : CostConfig Ground}
    {channel : CostName Ground} {body payload : CostTerm Ground}
    (sourceSafe : source.BinderSafe) (targetSafe : target.BinderSafe)
    (contextSafe : context.BinderSafe)
    (channelSafe : channel.BinderSafeAt 0)
    (bodySafe : body.BinderSafeAt 1) (payloadSafe : payload.BinderSafe)
    (sourceCongruent :
      StructuralCongruence
        (CostConfig.eraseCanonical signatureName
          signatureClosed.wellSorted.hashSetFree source)
        (.collection .hashBag
          [.apply "POutput"
            [channel.erase signatureName, payload.erase signatureName],
           .apply "PInput"
            [channel.erase signatureName, .lambda none (body.erase signatureName)],
           CostConfig.eraseCanonical signatureName
            signatureClosed.wellSorted.hashSetFree context] none))
    (targetCongruent :
      StructuralCongruence
        (CostConfig.eraseCanonical signatureName
          signatureClosed.wellSorted.hashSetFree target)
        (.collection .hashBag
          [semanticCommSubst (body.erase signatureName)
            (payload.erase signatureName),
           CostConfig.eraseCanonical signatureName
            signatureClosed.wellSorted.hashSetFree context] none)) :
    rhoLanguageDefGSLT.Step
      (source.eraseCanonicalProcess signatureClosed sourceSafe)
      (target.eraseCanonicalProcess signatureClosed targetSafe) := by
  let contextProcess : RhoProcess :=
    context.eraseCanonicalProcess signatureClosed contextSafe
  have contextClosed :=
    (rhoClosedTermWellSorted_process_iff contextProcess.1).mp contextProcess.2
  have channelTyped :=
    channelSafe.erase_wellSorted signatureClosed.wellSorted
  have channelScoped :=
    channelSafe.erase_binderSafeAt signatureClosed.binderSafe
  have bodyTyped := bodySafe.erase_wellSorted signatureClosed.wellSorted
  have bodyScoped := bodySafe.erase_binderSafeAt signatureClosed.binderSafe
  have payloadTyped := payloadSafe.erase_wellSorted signatureClosed.wellSorted
  have payloadScoped :=
    payloadSafe.erase_binderSafeAt signatureClosed.binderSafe
  have contractumClosed := semanticCommSubst_preserves
    (by simpa using bodyTyped) bodyScoped (by simpa using payloadTyped)
      payloadScoped
  let redexPattern : Pattern :=
    .collection .hashBag
      [.apply "PInput"
        [channel.erase signatureName, .lambda none (body.erase signatureName)],
       .apply "POutput"
        [channel.erase signatureName, payload.erase signatureName],
       contextProcess.1] none
  let contractumPattern : Pattern :=
    .collection .hashBag
      [semanticCommSubst (body.erase signatureName)
        (payload.erase signatureName),
       contextProcess.1] none
  have redexTyped :
      ProcWellSorted rhoReflectivePresentation FreeSortContext.empty []
        redexPattern := by
    exact .parallel
      (.cons (.input channelTyped (by simpa using bodyTyped))
        (.cons (.output channelTyped (by simpa using payloadTyped))
          (.cons contextClosed.1 .nil)))
  have redexSafe : binderSafeAt "NQuote" 0 redexPattern = true := by
    simp [redexPattern, binderSafeAt, binderSafeListAt, channelScoped,
      bodyScoped, payloadScoped, contextClosed.2]
  have contractumTyped :
      ProcWellSorted rhoReflectivePresentation FreeSortContext.empty []
        contractumPattern := by
    exact .parallel (.cons contractumClosed.1 (.cons contextClosed.1 .nil))
  have contractumSafe :
      binderSafeAt "NQuote" 0 contractumPattern = true := by
    simp [contractumPattern, binderSafeAt, binderSafeListAt,
      contractumClosed.2, contextClosed.2]
  let redex : RhoProcess :=
    ⟨redexPattern,
      (rhoClosedTermWellSorted_process_iff redexPattern).mpr
        ⟨redexTyped, redexSafe⟩⟩
  let contractum : RhoProcess :=
    ⟨contractumPattern,
      (rhoClosedTermWellSorted_process_iff contractumPattern).mpr
        ⟨contractumTyped, contractumSafe⟩⟩
  have sourceOrder : StructuralCongruence
      (.collection .hashBag
        [.apply "POutput"
          [channel.erase signatureName, payload.erase signatureName],
         .apply "PInput"
          [channel.erase signatureName, .lambda none (body.erase signatureName)],
         contextProcess.1] none)
      redexPattern := by
    apply StructuralCongruence.par_perm
    exact List.Perm.swap _ _ [_]
  have sourceToRedex : StructuralCongruence
      (source.eraseCanonicalProcess signatureClosed sourceSafe).1 redex.1 := by
    simpa [CostConfig.eraseCanonicalProcess, redex, redexPattern,
      contextProcess] using
      StructuralCongruence.trans _ _ _ sourceCongruent sourceOrder
  have contractumToTarget : StructuralCongruence
      contractum.1
      (target.eraseCanonicalProcess signatureClosed targetSafe).1 := by
    simpa [CostConfig.eraseCanonicalProcess, contractum, contractumPattern,
      contextProcess] using StructuralCongruence.symm _ _ targetCongruent
  have baseStep : rhoRewriteSystem.Reduces redex contractum := by
    change RhoStep redex.1 contractum.1
    simpa [redex, redexPattern, contractum, contractumPattern] using
      (RhoStep.comm
        (free := FreeSortContext.empty) (bound := [])
        (channel.erase signatureName) (body.erase signatureName)
        (payload.erase signatureName) [contextProcess.1]
        (by simpa using bodyTyped) (by simpa using payloadTyped))
  exact ⟨redex, contractum,
    (rhoProcessEquations_iff_structuralCongruence _ _).mpr sourceToRedex,
    baseStep,
    (rhoProcessEquations_iff_structuralCongruence _ _).mpr
      contractumToTarget⟩

/-- Every binder-safe funded step erases to exactly one step of the GSLT
mechanically derived from the authored `rhoCalc` declaration. -/
theorem CostStep.eraseCanonical_rhoLanguageDefGSLTStep
    {Ground : Type u} {signatureName : SignatureNameEncoding Ground}
    (signatureClosed : signatureName.MapsToClosedRhoNames)
    {source target : CostConfig Ground} {channel : CostName Ground}
    {demand : CostSig Ground}
    (step : CostStep source channel demand target)
    (sourceSafe : source.BinderSafe) :
    rhoLanguageDefGSLT.Step
      (source.eraseCanonicalProcess signatureClosed sourceSafe)
      (target.eraseCanonicalProcess signatureClosed
        (step.preserves_binderSafe sourceSafe)) := by
  have targetSafe := step.preserves_binderSafe sourceSafe
  cases step with
  | @wholeRecvSend context available residual stepChannel body payload outerSig
      signatureValid cover =>
      have redexSafe :
          (CostTerm.signed
            (.par (.recv channel body) (.send channel payload)) demand).BinderSafe :=
        sourceSafe _ (by simp)
      have contextSafe : context.BinderSafe := by
        intro term membership
        exact sourceSafe term (by simp [membership])
      cases redexSafe with
      | signed processSafe =>
          cases processSafe with
          | par receiveSafe sendSafe =>
              cases receiveSafe with
              | recv channelSafe bodySafe =>
                  cases sendSafe with
                  | send sendChannelSafe payloadSafe =>
                      exact fundedCommErasure_rhoLanguageDefGSLTStep
                        signatureClosed sourceSafe targetSafe contextSafe
                        channelSafe bodySafe payloadSafe
                        (wholeRecvSendSource_toPureCommSource
                          signatureName signatureClosed.wellSorted.hashSetFree
                          context available channel body payload demand)
                        (fundedTarget_toPureCommTarget
                          signatureClosed.wellSorted
                          signatureClosed.wellSorted.hashSetFree
                          context residual bodySafe payloadSafe)
  | @wholeSendRecv context available residual stepChannel body payload outerSig
      signatureValid cover =>
      have redexSafe :
          (CostTerm.signed
            (.par (.send channel payload) (.recv channel body)) demand).BinderSafe :=
        sourceSafe _ (by simp)
      have contextSafe : context.BinderSafe := by
        intro term membership
        exact sourceSafe term (by simp [membership])
      cases redexSafe with
      | signed processSafe =>
          cases processSafe with
          | par sendSafe receiveSafe =>
              cases sendSafe with
              | send sendChannelSafe payloadSafe =>
                  cases receiveSafe with
                  | recv channelSafe bodySafe =>
                      exact fundedCommErasure_rhoLanguageDefGSLTStep
                        signatureClosed sourceSafe targetSafe contextSafe
                        channelSafe bodySafe payloadSafe
                        (wholeSendRecvSource_toPureCommSource
                          signatureName signatureClosed.wellSorted.hashSetFree
                          context available channel body payload demand)
                        (fundedTarget_toPureCommTarget
                          signatureClosed.wellSorted
                          signatureClosed.wellSorted.hashSetFree
                          context residual bodySafe payloadSafe)
  | @split context available residual stepChannel body payload recvSeal sendSeal
      recvValid sendValid cover =>
      have receiveSafe :
          (CostTerm.signed (.recv channel body) recvSeal).BinderSafe :=
        sourceSafe _ (by simp)
      have sendSafe :
          (CostTerm.signed (.send channel payload) sendSeal).BinderSafe :=
        sourceSafe _ (by simp)
      have contextSafe : context.BinderSafe := by
        intro term membership
        exact sourceSafe term (by simp [membership])
      cases receiveSafe with
      | signed receiveProcessSafe =>
          cases receiveProcessSafe with
          | recv channelSafe bodySafe =>
              cases sendSafe with
              | signed sendProcessSafe =>
                  cases sendProcessSafe with
                  | send sendChannelSafe payloadSafe =>
                      exact fundedCommErasure_rhoLanguageDefGSLTStep
                        signatureClosed sourceSafe targetSafe contextSafe
                        channelSafe bodySafe payloadSafe
                        (splitSource_toPureCommSource
                          signatureName signatureClosed.wellSorted.hashSetFree
                          context available channel body payload recvSeal sendSeal)
                        (fundedTarget_toPureCommTarget
                          signatureClosed.wellSorted
                          signatureClosed.wellSorted.hashSetFree
                          context residual bodySafe payloadSafe)

/-- Every binder-safe funded declarative step is exactly one COMM step of the
committed pure-rho GSLT after canonical cost erasure. -/
theorem CostStep.eraseCanonical_rhoGSLTStep
    {Ground : Type u} {signatureName : SignatureNameEncoding Ground}
    {free : FreeSortContext} (signatureTyped : signatureName.WellSorted free)
    {source target : CostConfig Ground} {channel : CostName Ground}
    {demand : CostSig Ground}
    (step : CostStep source channel demand target)
    (sourceSafe : source.BinderSafe) :
    rhoGSLT.Step
      (CostConfig.eraseCanonical signatureName signatureTyped.hashSetFree source)
      (CostConfig.eraseCanonical signatureName signatureTyped.hashSetFree target) := by
  let signaturePure := signatureTyped.hashSetFree
  cases step with
  | @wholeRecvSend context available residual stepChannel body payload outerSig
      signatureValid cover =>
      have redexSafe :
          (CostTerm.signed
            (.par (.recv channel body) (.send channel payload)) demand).BinderSafe :=
        sourceSafe _ (by simp)
      cases redexSafe with
      | signed processSafe =>
          cases processSafe with
          | par receiveSafe sendSafe =>
              cases receiveSafe with
              | recv receiveChannelSafe bodySafe =>
                  cases sendSafe with
                  | send sendChannelSafe payloadSafe =>
                      have sourceCongruent :=
                        wholeRecvSendSource_toPureCommSource
                          signatureName signaturePure context available channel body payload demand
                      have targetCongruent := fundedTarget_toPureCommTarget
                        signatureTyped signaturePure context residual bodySafe payloadSafe
                      exact ⟨Reduces.equiv sourceCongruent Reduces.comm
                        (StructuralCongruence.symm _ _ targetCongruent)⟩

  | @wholeSendRecv context available residual stepChannel body payload outerSig
      signatureValid cover =>
      have redexSafe :
          (CostTerm.signed
            (.par (.send channel payload) (.recv channel body)) demand).BinderSafe :=
        sourceSafe _ (by simp)
      cases redexSafe with
      | signed processSafe =>
          cases processSafe with
          | par sendSafe receiveSafe =>
              cases sendSafe with
              | send sendChannelSafe payloadSafe =>
                  cases receiveSafe with
                  | recv receiveChannelSafe bodySafe =>
                      have sourceCongruent :=
                        wholeSendRecvSource_toPureCommSource
                          signatureName signaturePure context available channel body payload demand
                      have targetCongruent := fundedTarget_toPureCommTarget
                        signatureTyped signaturePure context residual bodySafe payloadSafe
                      exact ⟨Reduces.equiv sourceCongruent Reduces.comm
                        (StructuralCongruence.symm _ _ targetCongruent)⟩

  | @split context available residual stepChannel body payload recvSeal sendSeal
      recvValid sendValid cover =>
      have receiveSafe :
          (CostTerm.signed (.recv channel body) recvSeal).BinderSafe :=
        sourceSafe _ (by simp)
      have sendSafe :
          (CostTerm.signed (.send channel payload) sendSeal).BinderSafe :=
        sourceSafe _ (by simp)
      cases receiveSafe with
      | signed receiveProcessSafe =>
          cases receiveProcessSafe with
          | recv receiveChannelSafe bodySafe =>
              cases sendSafe with
              | signed sendProcessSafe =>
                  cases sendProcessSafe with
                  | send sendChannelSafe payloadSafe =>
                      have sourceCongruent := splitSource_toPureCommSource
                        signatureName signaturePure context available channel body payload
                          recvSeal sendSeal
                      have targetCongruent := fundedTarget_toPureCommTarget
                        signatureTyped signaturePure context residual bodySafe payloadSafe
                      exact ⟨Reduces.equiv sourceCongruent Reduces.comm
                        (StructuralCongruence.symm _ _ targetCongruent)⟩

/-! ## Declarative paths and their exact demand receipts -/

/-- A composable path in the declarative funded relation.  Step labels retain
the exact channel and demanded signature for each COMM occurrence. -/
inductive CostStepPath {Ground : Type u} :
    CostConfig Ground → CostConfig Ground → Type u where
  | done (config : CostConfig Ground) : CostStepPath config config
  | fire {source middle target : CostConfig Ground}
      {channel : CostName Ground} {demand : CostSig Ground}
      (step : CostStep source channel demand middle)
      (rest : CostStepPath middle target) :
      CostStepPath source target

namespace CostStepPath

/-- Number of funded COMM occurrences in a declarative path. -/
def length {Ground : Type u} {source target : CostConfig Ground} :
    CostStepPath source target → Nat
  | .done _ => 0
  | .fire _ rest => rest.length + 1

/-- Ordered exact demands, before any lossy numerical valuation. -/
def demands {Ground : Type u} {source target : CostConfig Ground} :
    CostStepPath source target → List (CostSig Ground)
  | .done _ => []
  | @fire _ _ _ _ _ demand _ rest => demand :: rest.demands

@[simp]
theorem demands_length {Ground : Type u} {source target : CostConfig Ground}
    (path : CostStepPath source target) :
    path.demands.length = path.length := by
  induction path with
  | done => rfl
  | fire step rest induction =>
      simp [demands, length, induction, Nat.add_comm]

/-- Initialization plus step preservation computes a safety witness for the
complete target of a declarative path. -/
def preserves_binderSafe
    {Ground : Type u} {source target : CostConfig Ground}
    (path : CostStepPath source target) : source.BinderSafe → target.BinderSafe :=
  match path with
  | .done _ => fun sourceSafe => sourceSafe
  | .fire step rest => fun sourceSafe =>
      rest.preserves_binderSafe (step.preserves_binderSafe sourceSafe)

/-- A binder-safe funded path erases to a rewrite path in the committed rho
GSLT, with one pure COMM step per funded occurrence. -/
def eraseCanonical_rhoRewritePath
    {Ground : Type u} {signatureName : SignatureNameEncoding Ground}
    {free : FreeSortContext} (signatureTyped : signatureName.WellSorted free)
    {source target : CostConfig Ground}
    (path : CostStepPath source target) (sourceSafe : source.BinderSafe) :
    rhoGSLT.RewritePath
      (CostConfig.eraseCanonical signatureName signatureTyped.hashSetFree source)
      (CostConfig.eraseCanonical signatureName signatureTyped.hashSetFree target) :=
  match path with
  | .done config => .nil _
  | .fire step rest =>
      .cons (step.eraseCanonical_rhoGSLTStep signatureTyped sourceSafe)
        (rest.eraseCanonical_rhoRewritePath signatureTyped
          (step.preserves_binderSafe sourceSafe))

/-- Erasure preserves event count exactly; it does not insert administrative
or executable-Drop steps. -/
theorem eraseCanonical_rhoRewritePath_length
    {Ground : Type u} {signatureName : SignatureNameEncoding Ground}
    {free : FreeSortContext} (signatureTyped : signatureName.WellSorted free)
    {source target : CostConfig Ground}
    (path : CostStepPath source target) (sourceSafe : source.BinderSafe) :
    (path.eraseCanonical_rhoRewritePath signatureTyped sourceSafe).length =
      path.length := by
  induction path with
  | done => rfl
  | fire step rest induction =>
      simp [eraseCanonical_rhoRewritePath, GSLT.RewritePath.length,
        length, induction, Nat.add_comm]

/-- The pure rewrite-path length is also the length of the ordered exact
demand receipt. -/
theorem eraseCanonical_rhoRewritePath_length_eq_demands
    {Ground : Type u} {signatureName : SignatureNameEncoding Ground}
    {free : FreeSortContext} (signatureTyped : signatureName.WellSorted free)
    {source target : CostConfig Ground}
    (path : CostStepPath source target) (sourceSafe : source.BinderSafe) :
    (path.eraseCanonical_rhoRewritePath signatureTyped sourceSafe).length =
      path.demands.length := by
  rw [path.eraseCanonical_rhoRewritePath_length signatureTyped sourceSafe,
    path.demands_length]

/-- A binder-safe funded path has an erasure into the one-root GSLT derived
from `rhoCalc`, with exactly one derived step per funded COMM occurrence.

The final scope witness is existential because it is proof-irrelevant data
inside the closed-term subtype, not part of the operational path. -/
theorem exists_eraseCanonical_rhoLanguageDefRewritePath
    {Ground : Type u} {signatureName : SignatureNameEncoding Ground}
    (signatureClosed : signatureName.MapsToClosedRhoNames)
    {source target : CostConfig Ground}
    (path : CostStepPath source target) (sourceSafe : source.BinderSafe) :
    ∃ targetSafe : target.BinderSafe,
      ∃ purePath : rhoLanguageDefGSLT.RewritePath
        (source.eraseCanonicalProcess signatureClosed sourceSafe)
        (target.eraseCanonicalProcess signatureClosed targetSafe),
        purePath.length = path.length := by
  induction path with
  | done =>
      exact ⟨sourceSafe, .nil _, rfl⟩
  | fire step rest induction =>
      obtain ⟨targetSafe, tail, tailLength⟩ :=
        induction (step.preserves_binderSafe sourceSafe)
      refine ⟨targetSafe,
        .cons
          (step.eraseCanonical_rhoLanguageDefGSLTStep
            signatureClosed sourceSafe)
          tail, ?_⟩
      simp [GSLT.RewritePath.length, length, tailLength, Nat.add_comm]

end CostStepPath

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
