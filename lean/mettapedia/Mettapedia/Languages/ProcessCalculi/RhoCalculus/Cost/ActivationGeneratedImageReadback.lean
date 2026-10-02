import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedImage
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedClosureReadout

/-!
# Actual readback of the generated decoder image

Every structural image derivation has a finite fuel bound after which the
existing parser returns exactly its cost syntax. This is readback of the
declared parser image, not completeness for all raw typed terms.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated

open Mettapedia.OSLF.MeTTaIL.Syntax

mutual
  theorem NameImage.parser_eventually {depth : Nat} {source : Pattern}
      {name : CostName LiteralAuthority} (image : NameImage depth source name) :
      ∃ bound, ∀ fuel, bound ≤ fuel → (name? fuel depth source).map Subtype.val = some name := by
    cases image with
    | bvar inScope =>
      refine ⟨1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel => rw [name_bvar_readout, if_pos inScope]
    | baseZeroQuote =>
      refine ⟨1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel => exact name_base_zero_quote_readout fuel depth
    | quote code =>
      obtain ⟨bound, readback⟩ := code.parser_eventually
      refine ⟨bound + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel =>
        rw [name_wrapped_quote_readout, readback fuel (by omega)]
        rfl

  theorem CodeImage.parser_eventually {depth : Nat} {source : Pattern}
      {term : CostTerm LiteralAuthority} (image : CodeImage depth source term) :
      ∃ bound, ∀ fuel, bound ≤ fuel → (code? fuel depth source).map Subtype.val = some term := by
    cases image with
    | zero =>
      refine ⟨1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel => exact code_zero_readout fuel depth
    | drop name =>
      obtain ⟨bound, readback⟩ := name.parser_eventually
      refine ⟨bound + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel =>
        rw [code_drop_readout, readback fuel (by omega)]
        rfl
    | signed signature accepted process =>
      obtain ⟨bound, readback⟩ := process.parser_eventually
      refine ⟨bound + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel =>
        rw [code_signed_readout, accepted, readback fuel (by omega)]
        rfl
    | collection codes =>
      obtain ⟨bound, readback⟩ := codes.parser_eventually
      refine ⟨bound + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel => rw [code_collection_readout, readback fuel (by omega)]

  theorem ProcImage.parser_eventually {depth : Nat} {source : Pattern}
      {process : CostProc LiteralAuthority} (image : ProcImage depth source process) :
      ∃ bound, ∀ fuel, bound ≤ fuel → (proc? fuel depth source).map Subtype.val = some process := by
    cases image with
    | zero =>
      refine ⟨1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel => exact proc_zero_readout fuel depth
    | send name code =>
      obtain ⟨nameBound, nameReadback⟩ := name.parser_eventually
      obtain ⟨codeBound, codeReadback⟩ := code.parser_eventually
      refine ⟨max nameBound codeBound + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel =>
        rw [proc_send_readout, nameReadback fuel (by omega), codeReadback fuel (by omega)]
        rfl
    | recv name code =>
      obtain ⟨nameBound, nameReadback⟩ := name.parser_eventually
      obtain ⟨codeBound, codeReadback⟩ := code.parser_eventually
      refine ⟨max nameBound codeBound + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel =>
        rw [proc_recv_readout, nameReadback fuel (by omega), codeReadback fuel (by omega)]
        rfl
    | pair left right =>
      obtain ⟨leftBound, leftReadback⟩ := left.parser_eventually
      obtain ⟨rightBound, rightReadback⟩ := right.parser_eventually
      refine ⟨max leftBound rightBound + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel =>
        rw [proc_pair_readout, leftReadback fuel (by omega), rightReadback fuel (by omega)]
        rfl

  theorem CodeListImage.parser_eventually {depth : Nat} {sources : List Pattern}
      {term : CostTerm LiteralAuthority} (image : CodeListImage depth sources term) :
      ∃ bound, ∀ fuel, bound ≤ fuel → (codeList? fuel depth sources).map Subtype.val = some term := by
    cases image with
    | nil =>
      refine ⟨1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel => exact codeList_nil_readout fuel depth
    | cons head tail =>
      obtain ⟨headBound, headReadback⟩ := head.parser_eventually
      obtain ⟨tailBound, tailReadback⟩ := tail.parser_eventually
      refine ⟨max headBound tailBound + 1, ?_⟩
      intro fuel enough
      cases fuel with
      | zero => omega
      | succ fuel =>
        rw [codeList_cons_readout, headReadback fuel (by omega), tailReadback fuel (by omega)]
        rfl
end

theorem name_parser_iff_image {depth : Nat} {source : Pattern} {name : CostName LiteralAuthority} :
    (∃ fuel, (name? fuel depth source).map Subtype.val = some name) ↔ NameImage depth source name := by
  constructor
  · rintro ⟨fuel, parsed⟩
    exact name_parser_image parsed
  · intro image
    obtain ⟨bound, readback⟩ := image.parser_eventually
    exact ⟨bound, readback bound (le_refl bound)⟩

theorem code_parser_iff_image {depth : Nat} {source : Pattern} {term : CostTerm LiteralAuthority} :
    (∃ fuel, (code? fuel depth source).map Subtype.val = some term) ↔ CodeImage depth source term := by
  constructor
  · rintro ⟨fuel, parsed⟩
    exact code_parser_image parsed
  · intro image
    obtain ⟨bound, readback⟩ := image.parser_eventually
    exact ⟨bound, readback bound (le_refl bound)⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated
