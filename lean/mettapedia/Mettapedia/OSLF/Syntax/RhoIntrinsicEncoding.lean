import Mettapedia.OSLF.Syntax.RhoCommunicationSchema
import Mettapedia.OSLF.Syntax.TermClone
import Mettapedia.OSLF.MeTTaIL.ScopedPattern
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem

/-!
# A rho term encoding and its quotation boundary

The intrinsic binary-parallel syntax has sorted binders. The canonical authored
syntax stores the same visible constructors in raw patterns and uses a hash bag
for parallel composition. This map does not yet identify the respective ACU
quotients or prove operational equivalence. Its exact quote-safety theorem
exposes the domain restriction needed for such a comparison: canonical rho
quotation seals its body against surrounding input binders.
-/

namespace Mettapedia.OSLF.Binding.RhoSchema.IntrinsicEncoding

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax

set_option autoImplicit false

/-- Render a declared list of bound sorts as nested locally nameless binders. -/
def wrapBinders (binders : List Srt) (body : Pattern) : Pattern :=
  binders.foldr (fun _ result => .lambda none result) body

mutual
/-- Render an intrinsic rho term in the canonical authored pattern syntax.
The binary parallel former becomes a two-element hash bag. -/
def encodeTerm : {Γ : Ctx sig} → {s : Srt} → Term sig Γ s → Pattern
  | _, _, .var v => .bvar (varIdx v).val
  | _, _, .op .nil _ => .apply "PZero" []
  | _, _, .op .par args => .collection .hashBag (encodeArgs args) none
  | _, _, .op .out args => .apply "POutput" (encodeArgs args)
  | _, _, .op .inp args => .apply "PInput" (encodeArgs args)
  | _, _, .op .quo args => .apply "NQuote" (encodeArgs args)
  | _, _, .op .drp args => .apply "PDrop" (encodeArgs args)

/-- Encode each argument under exactly its declared binder list. -/
def encodeArgs : {as : List (List Srt × Srt)} → {Γ : Ctx sig} →
    Args sig as Γ → List Pattern
  | _, _, .nil => []
  | _, _, .cons (bs := bs) head tail =>
      wrapBinders bs (encodeTerm head) :: encodeArgs tail
end

/-- A closed intrinsic process whose input binder is used inside a quotation. -/
def crossingQuote : Term sig [] Srt.pr :=
  .op Op.inp (.cons chan
    (.cons (.op Op.drp
      (.cons (.op Op.quo
        (.cons (.op Op.drp (.cons (.var Var.zero) .nil)) .nil)) .nil)) .nil))

theorem crossingQuote_not_canonical :
    binderSafeAt "NQuote" 0 (encodeTerm crossingQuote) = false := by
  decide +kernel

theorem communication_quote_safe :
    binderSafeAt "NQuote" 0 (encodeTerm commSource) = true := by
  decide +kernel

/-- The naive full-carrier encoding cannot land in canonical closed rho:
the canonical presentation explicitly seals quotation at its boundary. -/
theorem crossingQuote_not_closedRho :
    ¬ Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem.RhoClosedTermWellSorted
      Mettapedia.OSLF.Framework.ConstructorCategory.rhoProc
      (encodeTerm crossingQuote) := by
  intro typed
  have safe :=
    (Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem.rhoClosedTermWellSorted_process_iff
      (encodeTerm crossingQuote)).mp typed |>.2
  rw [crossingQuote_not_canonical] at safe
  cases safe

/-- The encoded closed communication source does inhabit the canonical
closed-process carrier; the quotation restriction is substantive rather than
a blanket rejection of input binders. -/
theorem communication_encoded_closedRho :
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem.RhoClosedTermWellSorted
      Mettapedia.OSLF.Framework.ConstructorCategory.rhoProc
      (encodeTerm commSource) := by
  apply (Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem.rhoClosedTermWellSorted_process_iff
    (encodeTerm commSource)).mpr
  refine ⟨?_, communication_quote_safe⟩
  change Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax.ProcWellSorted
    rhoReflectivePresentation
    Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax.FreeSortContext.empty []
    (.collection .hashBag
      [.apply "POutput" [.apply "NQuote" [.apply "PZero" []], .apply "PZero" []],
       .apply "PInput" [.apply "NQuote" [.apply "PZero" []],
         .lambda none (.apply "PDrop" [.bvar 0])]] none)
  exact .parallel (.cons (.output (.quote .unit) .unit)
    (.cons (.input (.quote .unit) (.drop (.bvar (by decide)))) .nil))

mutual
/-- Intrinsic quote safety: input binders extend scope, while quotation
starts a sealed scope. -/
def intrinsicQuoteSafe : {Γ : Ctx sig} → {s : Srt} → Nat → Term sig Γ s → Bool
  | _, _, depth, .var v => decide ((varIdx v).val < depth)
  | _, _, _, .op .quo args => intrinsicQuoteSafeArgs 0 args
  | _, _, depth, .op _ args => intrinsicQuoteSafeArgs depth args

/-- The binder-sensitive safety judgment for a vector of arguments. -/
def intrinsicQuoteSafeArgs : {as : List (List Srt × Srt)} → {Γ : Ctx sig} →
    Nat → Args sig as Γ → Bool
  | _, _, _, .nil => true
  | _, _, depth, .cons (bs := bs) head tail =>
      intrinsicQuoteSafe (depth + bs.length) head &&
        intrinsicQuoteSafeArgs depth tail
end

/-- Encoding a binder list raises the canonical scope depth by its length. -/
theorem binderSafeAt_wrapBinders (binders : List Srt) (depth : Nat)
    (body : Pattern) :
    binderSafeAt "NQuote" depth (wrapBinders binders body) =
      binderSafeAt "NQuote" (depth + binders.length) body := by
  induction binders generalizing depth with
  | nil => rfl
  | cons binder rest ih =>
      simp only [wrapBinders, List.foldr_cons, binderSafeAt, List.length_cons]
      simpa [wrapBinders, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using ih (depth + 1)

mutual
/-- The intrinsic safety judgment is exactly the canonical quote-aware
scope check after encoding. -/
theorem encodeTerm_quoteSafe : ∀ {Γ : Ctx sig} {s : Srt}
    (term : Term sig Γ s) (depth : Nat),
    binderSafeAt "NQuote" depth (encodeTerm term) =
      intrinsicQuoteSafe depth term
  | _, _, .var v, depth => rfl
  | _, _, .op .nil .nil, depth => rfl
  | _, _, .op .par (.cons left (.cons right .nil)), depth => by
      simp [encodeTerm, encodeArgs, intrinsicQuoteSafe, intrinsicQuoteSafeArgs,
        wrapBinders, binderSafeAt, binderSafeListAt,
        encodeTerm_quoteSafe left depth, encodeTerm_quoteSafe right depth]
  | _, _, .op .out (.cons name (.cons body .nil)), depth => by
      simp [encodeTerm, encodeArgs, intrinsicQuoteSafe, intrinsicQuoteSafeArgs,
        wrapBinders, binderSafeAt, binderSafeListAt,
        encodeTerm_quoteSafe name depth, encodeTerm_quoteSafe body depth]
  | _, _, .op .inp (.cons name (.cons body .nil)), depth => by
      simp [encodeTerm, encodeArgs, intrinsicQuoteSafe, intrinsicQuoteSafeArgs,
        wrapBinders, binderSafeAt, binderSafeListAt,
        encodeTerm_quoteSafe name depth, encodeTerm_quoteSafe body (depth + 1)]
  | _, _, .op .quo (.cons body .nil), depth => by
      simp [encodeTerm, encodeArgs, intrinsicQuoteSafe, intrinsicQuoteSafeArgs,
        wrapBinders, binderSafeAt,
        encodeTerm_quoteSafe body 0]
  | _, _, .op .drp (.cons name .nil), depth => by
      simp [encodeTerm, encodeArgs, intrinsicQuoteSafe, intrinsicQuoteSafeArgs,
        wrapBinders, binderSafeAt, binderSafeListAt,
        encodeTerm_quoteSafe name depth]

/-- Argument encoding obeys the same quote-safety comparison. -/
theorem encodeArgs_quoteSafe : ∀ {as : List (List Srt × Srt)}
    {Γ : Ctx sig} (args : Args sig as Γ) (depth : Nat),
    binderSafeListAt "NQuote" depth (encodeArgs args) =
      intrinsicQuoteSafeArgs depth args
  | _, _, .nil, _ => rfl
  | _, _, .cons (bs := bs) head tail, depth => by
      simp only [encodeArgs, binderSafeListAt, intrinsicQuoteSafeArgs,
        binderSafeAt_wrapBinders, encodeTerm_quoteSafe head (depth + bs.length),
        encodeArgs_quoteSafe tail depth]
end

theorem crossingQuote_intrinsically_unsafe :
    intrinsicQuoteSafe 0 crossingQuote = false := by
  rw [← encodeTerm_quoteSafe crossingQuote 0]
  exact crossingQuote_not_canonical

theorem communication_intrinsically_safe :
    intrinsicQuoteSafe 0 commSource = true := by
  rw [← encodeTerm_quoteSafe commSource 0]
  exact communication_quote_safe

/-! ### Open communication and the literal-quotation boundary -/

/-- A name in the ambient context of an open communication. -/
abbrev openCommAmbientName : Term sig [Srt.nm] Srt.nm := .var .zero

/-- The emitted process refers to that ambient name. -/
abbrev openCommPayload : Term sig [Srt.nm] Srt.pr :=
  .op Op.out (.cons openCommAmbientName (.cons (.op Op.nil .nil) .nil))

/-- The input continuation uses its freshly bound name as an output channel. -/
abbrev openCommContinuation : Term sig [Srt.nm, Srt.nm] Srt.pr :=
  .op Op.out (.cons (.var .zero) (.cons (.op Op.nil .nil) .nil))

/-- This is an instance of the general semantic COMM constructor, in an open
context rather than after closing every ambient name. -/
abbrev openCommSource : Term sig [Srt.nm] Srt.pr :=
  .op Op.par
    (.cons
      (.op Op.out (.cons openCommAmbientName (.cons openCommPayload .nil)))
      (.cons (.op Op.inp
        (.cons openCommAmbientName (.cons openCommContinuation .nil))) .nil))

abbrev openCommTarget : Term sig [Srt.nm] Srt.pr :=
  inst openCommContinuation (.op Op.quo (.cons openCommPayload .nil))

/-- Its source is admitted by the authored quote-aware scope check. -/
theorem openCommSource_quoteSafe :
    intrinsicQuoteSafe 1 openCommSource = true := by
  decide +kernel

/-- Ordinary intrinsic substitution constructs a name from the open payload.
It is a valid intrinsic term, but its rendering cannot be a *literal* sealed
quote in the current authored source syntax. -/
theorem openCommTarget_not_quoteSafe :
    intrinsicQuoteSafe 1 openCommTarget = false := by
  decide +kernel

/-- The same boundary is visible at the actual authored scope checker. -/
theorem openCommTarget_not_literal_source :
    binderSafeAt "NQuote" 1 (encodeTerm openCommTarget) = false := by
  rw [encodeTerm_quoteSafe]
  exact openCommTarget_not_quoteSafe

/-- The admitted literal-source fragment is not closed under the general
open-context COMM constructor. A semantic carrier for this operation must
retain constructed names separately from literal quotations. -/
theorem openComm_not_closed_on_literal_source :
    intrinsicQuoteSafe 1 openCommSource = true ∧
      intrinsicQuoteSafe 1 openCommTarget = false :=
  ⟨openCommSource_quoteSafe, openCommTarget_not_quoteSafe⟩

/-- Map the two intrinsic sorts to the authored declaration's sort labels. -/
def sortLabel : Srt → String
  | .nm => "Name"
  | .pr => "Proc"

/-- An intrinsic sorted context as the canonical checker's ordered context. -/
def contextLabels (Γ : Ctx sig) : List String := Γ.map sortLabel

/-- Positional encoding retains the sort at every bound-variable index. -/
theorem contextLabels_var : ∀ {Γ : Ctx sig} {s : Srt} (v : Var Γ s),
    (contextLabels Γ)[(varIdx v).val]? = some (sortLabel s)
  | _, _, .zero => rfl
  | _, _, .succ v => contextLabels_var v

/-- The actual canonical sorting judgment for an encoded intrinsic term. -/
def EncodedTermTyped {Γ : Ctx sig} {s : Srt} (t : Term sig Γ s) : Prop :=
  match s with
  | .nm => NameWellSorted rhoReflectivePresentation FreeSortContext.empty
      (contextLabels Γ) (encodeTerm t)
  | .pr => ProcWellSorted rhoReflectivePresentation FreeSortContext.empty
      (contextLabels Γ) (encodeTerm t)

/-- Recursive sorting invariant for an argument vector. -/
def EncodedArgsTyped : {as : List (List Srt × Srt)} → {Γ : Ctx sig} →
    Args sig as Γ → Prop
  | _, _, .nil => True
  | _, _, .cons head tail => EncodedTermTyped head ∧ EncodedArgsTyped tail

mutual
/-- Every intrinsic rho term is well sorted after encoding, even before the
additional quotation restriction is imposed. -/
theorem encodedTerm_typed : ∀ {Γ : Ctx sig} {s : Srt}
    (t : Term sig Γ s), EncodedTermTyped t
  | _, _, .var (s := s) v => by
      cases s with
      | nm => exact NameWellSorted.bvar (contextLabels_var v)
      | pr => exact ProcWellSorted.bvar (contextLabels_var v)
  | _, _, .op .nil .nil => by
      exact ProcWellSorted.unit
  | _, _, .op .par (.cons a (.cons b .nil)) => by
      exact ProcWellSorted.parallel
        (.cons (encodedTerm_typed a) (.cons (encodedTerm_typed b) .nil))
  | _, _, .op .out (.cons a (.cons b .nil)) => by
      exact ProcWellSorted.output (encodedTerm_typed a) (encodedTerm_typed b)
  | _, _, .op .inp (.cons a (.cons b .nil)) => by
      exact ProcWellSorted.input (encodedTerm_typed a) (encodedTerm_typed b)
  | _, _, .op .quo (.cons a .nil) => by
      exact NameWellSorted.quote (encodedTerm_typed a)
  | _, _, .op .drp (.cons a .nil) => by
      exact ProcWellSorted.drop (encodedTerm_typed a)

/-- Every argument vector satisfies the encoded sorting invariant. -/
theorem encodedArgs_typed : ∀ {as : List (List Srt × Srt)}
    {Γ : Ctx sig} (args : Args sig as Γ), EncodedArgsTyped args
  | _, _, .nil => trivial
  | _, _, .cons head tail =>
      ⟨encodedTerm_typed head, encodedArgs_typed tail⟩
end

/-- The open COMM source passes both parts of the authored admission check:
its constructor sorts are correct and its literal quotations respect scope. -/
theorem openCommSource_authored_admitted :
    ProcWellSorted rhoReflectivePresentation FreeSortContext.empty
      (contextLabels [Srt.nm]) (encodeTerm openCommSource) ∧
    binderSafeAt "NQuote" 1 (encodeTerm openCommSource) = true := by
  exact ⟨encodedTerm_typed openCommSource,
    (encodeTerm_quoteSafe openCommSource 1).trans openCommSource_quoteSafe⟩

/-- The quote-safe closed intrinsic process fragment maps into the actual
canonical closed-process carrier, carrying both sort and scope proofs. -/
def encodeClosedProcess (term : Term sig [] Srt.pr)
    (safe : intrinsicQuoteSafe 0 term = true) :
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem.RhoClosedTerm
      Mettapedia.OSLF.Framework.ConstructorCategory.rhoProc := by
  refine ⟨encodeTerm term, ?_⟩
  apply (Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem.rhoClosedTermWellSorted_process_iff
    (encodeTerm term)).mpr
  refine ⟨?_, ?_⟩
  · simpa [EncodedTermTyped, contextLabels] using encodedTerm_typed term
  · rw [encodeTerm_quoteSafe]
    exact safe

/-- The corresponding map on closed intrinsic names uses the same quote
boundary; names and processes remain distinct canonical fibres. -/
def encodeClosedName (term : Term sig [] Srt.nm)
    (safe : intrinsicQuoteSafe 0 term = true) :
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem.RhoClosedTerm
      Mettapedia.OSLF.Framework.ConstructorCategory.rhoName := by
  refine ⟨encodeTerm term, ?_⟩
  apply (Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem.rhoClosedTermWellSorted_name_iff
    (encodeTerm term)).mpr
  refine ⟨?_, ?_⟩
  · simpa [EncodedTermTyped, contextLabels] using encodedTerm_typed term
  · rw [encodeTerm_quoteSafe]
    exact safe

/-- For an intrinsically sorted closed process, quote safety is the exact
additional condition for admission to the canonical closed rho carrier. -/
theorem encoded_process_admitted_iff_quoteSafe (term : Term sig [] Srt.pr) :
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem.RhoClosedTermWellSorted
      Mettapedia.OSLF.Framework.ConstructorCategory.rhoProc (encodeTerm term) ↔
      intrinsicQuoteSafe 0 term = true := by
  constructor
  · intro admitted
    have safe :=
      (Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem.rhoClosedTermWellSorted_process_iff
        (encodeTerm term)).mp admitted |>.2
    rw [encodeTerm_quoteSafe] at safe
    exact safe
  · intro safe
    exact (encodeClosedProcess term safe).2

/-- The same exact admission criterion holds at the name sort. -/
theorem encoded_name_admitted_iff_quoteSafe (term : Term sig [] Srt.nm) :
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem.RhoClosedTermWellSorted
      Mettapedia.OSLF.Framework.ConstructorCategory.rhoName (encodeTerm term) ↔
      intrinsicQuoteSafe 0 term = true := by
  constructor
  · intro admitted
    have safe :=
      (Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem.rhoClosedTermWellSorted_name_iff
        (encodeTerm term)).mp admitted |>.2
    rw [encodeTerm_quoteSafe] at safe
    exact safe
  · intro safe
    exact (encodeClosedName term safe).2

@[simp] theorem encodeClosedProcess_pattern (term : Term sig [] Srt.pr)
    (safe : intrinsicQuoteSafe 0 term = true) :
    (encodeClosedProcess term safe).1 = encodeTerm term := rfl

@[simp] theorem encodeClosedName_pattern (term : Term sig [] Srt.nm)
    (safe : intrinsicQuoteSafe 0 term = true) :
    (encodeClosedName term safe).1 = encodeTerm term := rfl

end Mettapedia.OSLF.Binding.RhoSchema.IntrinsicEncoding
