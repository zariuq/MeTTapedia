import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedImage
import Mettapedia.OSLF.Syntax.RhoEquationEncoding

/-!
# Intrinsic source readout of the generated runtime image

The partial functions read the existing runtime trees into rho's declared
binding signature. Quotation is reified in a closed context before being
inserted into the surrounding context. Signature names and resource purses
are outside this source readout. Literal authority and authored origins remain
in the original runtime and decoder values; they are not reconstructed here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.RuntimeSourceReification

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.RhoSchema
open Mettapedia.OSLF.Binding.RhoSchema.IntrinsicEncoding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open ActivationGenerated

abbrev nameContext (depth : Nat) : Ctx sig := List.replicate depth Srt.nm

/-- Use the existing positional variable constructor at its checked sort. -/
def namePosition (depth index : Nat) (bound : index < depth) :
    Var (nameContext depth) Srt.nm := by
  let position : Fin (nameContext depth).length := ⟨index, by simpa using bound⟩
  have sort : (nameContext depth).get position = Srt.nm := by simp [nameContext]
  exact sort ▸ varOfIdx (nameContext depth) position

private theorem varIdx_cast {Γ : Ctx sig} {s t : Srt}
    (equal : s = t) (position : Var Γ s) :
    (varIdx (equal ▸ position)).val = (varIdx position).val := by
  cases equal
  rfl

theorem namePosition_index (depth index : Nat) (bound : index < depth) :
    (varIdx (namePosition depth index bound)).val = index := by
  simp only [namePosition, varIdx_cast, varIdx_varOfIdx]

/-- Insert a closed term without changing its bound-variable positions. -/
def insertClosed {sort : Srt} (depth : Nat) (term : Term sig [] sort) :
    Term sig (nameContext depth) sort :=
  rename (fun s (position : Var ([] : Ctx sig) s) => nomatch position) term

theorem encode_insertClosed {sort : Srt} (depth : Nat) (term : Term sig [] sort) :
    encodeTerm (insertClosed depth term) = encodeTerm term := by
  rw [insertClosed, encodeTerm_rename_shift _ 0 0]
  · exact Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero _ 0
  · intro _ position
    exact nomatch position

theorem insertClosed_quoteSafe {sort : Srt} (depth : Nat) (term : Term sig [] sort)
    (safe : intrinsicQuoteSafe 0 term = true) :
    intrinsicQuoteSafe 0 (insertClosed depth term) = true := by
  rw [← encodeTerm_quoteSafe, encode_insertClosed, encodeTerm_quoteSafe]
  exact safe

mutual
  /-- A runtime name is a checked position or a sealed quotation. -/
  def name? (depth : Nat) : CostName LiteralAuthority →
      Option (Term sig (nameContext depth) Srt.nm)
    | .bvar index =>
        if bound : index < depth then some (.var (namePosition depth index bound)) else none
    | .quote code => (code? 0 code).map (fun body =>
        .op Op.quo (.cons (insertClosed depth body) .nil))
    | .signature _ => none

  /-- Signed processes retain their full binder-bearing source tree. -/
  def process? (depth : Nat) : CostProc LiteralAuthority →
      Option (Term sig (nameContext depth) Srt.pr)
    | .nil => some (.op Op.nil .nil)
    | .par left right => do
        let first ← process? depth left
        let second ← process? depth right
        pure (.op Op.par (.cons first (.cons second .nil)))
    | .send channel payload => do
        let name ← name? depth channel
        let body ← code? depth payload
        pure (.op Op.out (.cons name (.cons body .nil)))
    | .recv channel continuation => do
        let name ← name? depth channel
        let body ← code? (depth + 1) continuation
        pure (.op Op.inp (.cons name (.cons (by
          simpa only [nameContext, List.replicate_succ, List.cons_append,
            List.nil_append] using body) .nil)))

  /-- Current-layer authority is retained separately, not read as source code. -/
  def code? (depth : Nat) : CostTerm LiteralAuthority →
      Option (Term sig (nameContext depth) Srt.pr)
    | .nil => some (.op Op.nil .nil)
    | .signed process _ => process? depth process
    | .par left right => do
        let first ← code? depth left
        let second ← code? depth right
        pure (.op Op.par (.cons first (.cons second .nil)))
    | .drop channel => (name? depth channel).map (fun name =>
        .op Op.drp (.cons name .nil))
    | .purse _ _ => none
end

theorem signature_name_rejected (depth : Nat) (authority : CostSig LiteralAuthority) :
    name? depth (.signature authority) = none := rfl

theorem resource_purse_rejected (depth : Nat) (location : CostName LiteralAuthority)
    (stack : CostStack LiteralAuthority) : code? depth (.purse location stack) = none := rfl

mutual
  /-- Every decoder-admitted name has a source term with the same erasure. -/
  theorem name_image_readout {depth : Nat} {source : Pattern}
      {name : CostName LiteralAuthority} (image : NameImage depth source name) :
      ∃ term, name? depth name = some term ∧ intrinsicQuoteSafe depth term = true ∧
        ∀ encoding : SignatureNameEncoding LiteralAuthority,
          StructuralCongruence (encodeTerm term) (name.erase encoding) := by
    cases image with
    | bvar bound =>
        refine ⟨.var (namePosition _ _ bound), by simp [name?, bound], ?_, ?_⟩
        · simp [intrinsicQuoteSafe, namePosition_index, bound]
        · intro encoding
          simp only [encodeTerm, namePosition_index, CostName.erase]
          exact .refl _
    | baseZeroQuote =>
        refine ⟨.op Op.quo (.cons (insertClosed _ (.op Op.nil .nil)) .nil), rfl, ?_, ?_⟩
        · simp [intrinsicQuoteSafe, intrinsicQuoteSafeArgs, insertClosed, rename,
            renameArgs]
        · intro encoding
          simp only [encodeTerm, encodeArgs, wrapBinders, List.foldr_nil,
            encode_insertClosed, CostName.erase, CostTerm.erase]
          exact applyCongruence_of_forall₂ "NQuote" (.cons (.symm _ _ .par_empty) .nil)
    | quote code =>
        obtain ⟨body, found, safe, agree⟩ := code_image_readout code
        refine ⟨.op Op.quo (.cons (insertClosed _ body) .nil), ?_, ?_, ?_⟩
        · simp [name?, found]
        · simpa [intrinsicQuoteSafe, intrinsicQuoteSafeArgs] using
            insertClosed_quoteSafe depth body safe
        · intro encoding
          simp only [encodeTerm, encodeArgs, wrapBinders, List.foldr_nil,
            encode_insertClosed, CostName.erase]
          exact applyCongruence_of_forall₂ "NQuote" (.cons (agree encoding) .nil)

  /-- Every admitted wrapped code retains its entire declared binder tree. -/
  theorem code_image_readout {depth : Nat} {source : Pattern}
      {code : CostTerm LiteralAuthority} (image : CodeImage depth source code) :
      ∃ term, code? depth code = some term ∧ intrinsicQuoteSafe depth term = true ∧
        ∀ encoding : SignatureNameEncoding LiteralAuthority,
          StructuralCongruence (encodeTerm term) (code.erase encoding) := by
    cases image with
    | zero =>
        exact ⟨.op Op.nil .nil, rfl, rfl, fun _ => .symm _ _ .par_empty⟩
    | drop name =>
        obtain ⟨channel, found, safe, agree⟩ := name_image_readout name
        refine ⟨.op Op.drp (.cons channel .nil), ?_, ?_, ?_⟩
        · simp [code?, found]
        · simpa [intrinsicQuoteSafe, intrinsicQuoteSafeArgs] using safe
        · intro encoding
          exact applyCongruence_of_forall₂ "PDrop" (.cons (agree encoding) .nil)
    | signed _ _ process => exact process_image_readout process
    | collection codes => exact code_list_image_readout codes

  /-- Input continuation readout opens precisely one name binder. -/
  theorem process_image_readout {depth : Nat} {source : Pattern}
      {process : CostProc LiteralAuthority} (image : ProcImage depth source process) :
      ∃ term, process? depth process = some term ∧ intrinsicQuoteSafe depth term = true ∧
        ∀ encoding : SignatureNameEncoding LiteralAuthority,
          StructuralCongruence (encodeTerm term) (process.erase encoding) := by
    cases image with
    | zero => exact ⟨.op Op.nil .nil, rfl, rfl, fun _ => .symm _ _ .par_empty⟩
    | send name code =>
        obtain ⟨channel, nameFound, nameSafe, nameAgree⟩ := name_image_readout name
        obtain ⟨body, codeFound, codeSafe, codeAgree⟩ := code_image_readout code
        refine ⟨.op Op.out (.cons channel (.cons body .nil)), ?_, ?_, ?_⟩
        · simp [process?, nameFound, codeFound]
        · simp [intrinsicQuoteSafe, intrinsicQuoteSafeArgs, nameSafe, codeSafe]
        · intro encoding
          exact applyCongruence_of_forall₂ "POutput"
            (.cons (nameAgree encoding) (.cons (codeAgree encoding) .nil))
    | recv name code =>
        obtain ⟨channel, nameFound, nameSafe, nameAgree⟩ := name_image_readout name
        obtain ⟨body, codeFound, codeSafe, codeAgree⟩ := code_image_readout code
        let continuation : Term sig (Srt.nm :: nameContext depth) Srt.pr := by
          simpa only [nameContext, List.replicate_succ] using body
        refine ⟨.op Op.inp (.cons channel (.cons continuation .nil)), ?_, ?_, ?_⟩
        · simp [process?, nameFound, codeFound, continuation]
        · simp [intrinsicQuoteSafe, intrinsicQuoteSafeArgs, nameSafe, continuation,
            codeSafe]
        · intro encoding
          exact applyCongruence_of_forall₂ "PInput"
            (.cons (nameAgree encoding)
              (.cons (.lambda_cong none _ _ (codeAgree encoding)) .nil))
    | pair left right =>
        obtain ⟨first, leftFound, leftSafe, leftAgree⟩ := process_image_readout left
        obtain ⟨second, rightFound, rightSafe, rightAgree⟩ := process_image_readout right
        refine ⟨.op Op.par (.cons first (.cons second .nil)), ?_, ?_, ?_⟩
        · simp [process?, leftFound, rightFound]
        · simp [intrinsicQuoteSafe, intrinsicQuoteSafeArgs, leftSafe, rightSafe]
        · intro encoding
          exact collectionCongruence_of_forall₂ .hashBag none
            (.cons (leftAgree encoding) (.cons (rightAgree encoding) .nil))

  /-- The existing ordered runtime parallel spine is read without dropping a component. -/
  theorem code_list_image_readout {depth : Nat} {sources : List Pattern}
      {code : CostTerm LiteralAuthority} (image : CodeListImage depth sources code) :
      ∃ term, code? depth code = some term ∧ intrinsicQuoteSafe depth term = true ∧
        ∀ encoding : SignatureNameEncoding LiteralAuthority,
          StructuralCongruence (encodeTerm term) (code.erase encoding) := by
    cases image with
    | nil => exact ⟨.op Op.nil .nil, rfl, rfl, fun _ => .symm _ _ .par_empty⟩
    | cons head tail =>
        obtain ⟨first, headFound, headSafe, headAgree⟩ := code_image_readout head
        obtain ⟨second, tailFound, tailSafe, tailAgree⟩ := code_list_image_readout tail
        refine ⟨.op Op.par (.cons first (.cons second .nil)), ?_, ?_, ?_⟩
        · simp [code?, headFound, tailFound]
        · simp [intrinsicQuoteSafe, intrinsicQuoteSafeArgs, headSafe, tailSafe]
        · intro encoding
          exact collectionCongruence_of_forall₂ .hashBag none
            (.cons (headAgree encoding) (.cons (tailAgree encoding) .nil))
end

/-- Successful decoding constructs an intrinsic term, rather than postulating one. -/
theorem generated_code_readout {depth : Nat} {source : Pattern}
    {code : CostTerm LiteralAuthority} (image : GeneratedCodeImage depth source code) :
    ∃ term, code? depth code = some term := by
  obtain ⟨term, found, _⟩ := code_image_readout image.structural_image
  exact ⟨term, found⟩

/-- The readout agrees with the actual independent apparatus erasure. -/
theorem code_readout_erasure {depth : Nat} {source : Pattern}
    {code : CostTerm LiteralAuthority} (image : CodeImage depth source code)
    {term : Term sig (nameContext depth) Srt.pr} (found : code? depth code = some term) :
    StructuralCongruence (encodeTerm term) (eraseGenerated source) := by
  obtain ⟨other, otherFound, _, agree⟩ := code_image_readout image
  have equal : other = term := Option.some.inj (otherFound.symm.trans found)
  subst other
  exact .trans _ _ _ (agree (fun _ => .apply "PZero" []))
    (image.erase_structural (fun _ => .apply "PZero" []))

theorem code_readout_quoteSafe {depth : Nat} {source : Pattern}
    {code : CostTerm LiteralAuthority} (image : CodeImage depth source code)
    {term : Term sig (nameContext depth) Srt.pr} (found : code? depth code = some term) :
    intrinsicQuoteSafe depth term = true := by
  obtain ⟨other, otherFound, safe, _⟩ := code_image_readout image
  have equal : other = term := Option.some.inj (otherFound.symm.trans found)
  exact equal ▸ safe

/-- Whole-program canonical observation agrees, not merely a leaf inventory. -/
theorem code_readout_canonical {depth : Nat} {source : Pattern}
    {code : CostTerm LiteralAuthority} (image : CodeImage depth source code)
    {term : Term sig (nameContext depth) Srt.pr} (found : code? depth code = some term) :
    canonicalize (encodeTerm term) = canonicalize (eraseGenerated source) := by
  have agree := code_readout_erasure image found
  exact canonicalize_eq_of_structuralCongruence agree (encodedTerm_hashSetFree term)
    ((hashSetFree_iff_of_structuralCongruence agree).mp (encodedTerm_hashSetFree term))

#print axioms name_image_readout
#print axioms code_image_readout
#print axioms code_readout_canonical
#print axioms code_readout_quoteSafe

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.RuntimeSourceReification
