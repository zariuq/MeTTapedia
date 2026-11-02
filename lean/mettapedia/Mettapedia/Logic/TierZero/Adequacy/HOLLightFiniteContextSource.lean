import Mettapedia.Logic.TierZero.Adequacy.HOLLightFiniteContextData

/-!
# Finite source declarations decode to their original registered context

The existing OperatorTable/DeclarationTable witnesses cover the complete
source signature. The finite decoder recovers that exact function-valued
TheoryContext, including occupied names and provenance-sensitive symbols,
without replaying the history that built it.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightFiniteContextSource

open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.OpenTheory.SignatureFormation
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open Mettapedia.Languages.HOLLight.MeTTa
open HOLLightFiniteContextData
open HOLLightFiniteSignatureLookup

def ofTable {context : TheoryContext} (table : DeclarationTable.Table context) : ContextData :=
  ⟨context.names, table.operators.entries, table.constants⟩

private theorem signature_equal {first second : Signature}
    (operators : first.typeOperators = second.typeOperators) (constants : first.constants = second.constants) : first = second := by
  cases first
  cases second
  cases operators
  cases constants
  rfl

theorem signature_ofTable {context : TheoryContext} (table : DeclarationTable.Table context) :
    signature (ofTable table) = context.signature := by
  apply signature_equal
  · exact operator_table_exact table.operators
  · exact constant_table_exact table

theorem ofTable_wellFormed {context : TheoryContext} (table : DeclarationTable.Table context) : WellFormed (ofTable table) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro entry member
    exact context.typeNames entry.1 entry.2 (table.operators.registered entry member)
  · intro entry member
    exact context.constantNames entry.1 entry.2 (table.registered entry member)
  · intro first firstMember second secondMember sameName
    obtain ⟨left, leftArity⟩ := first
    obtain ⟨right, rightArity⟩ := second
    have leftKnown := table.operators.registered (left, leftArity) firstMember
    have rightKnown := table.operators.registered (right, rightArity) secondMember
    have same := context.uniqueTypeNames left right leftArity rightArity leftKnown rightKnown sameName
    subst right
    exact Prod.ext rfl (Option.some.inj (leftKnown.symm.trans rightKnown))
  · intro first firstMember second secondMember sameName
    obtain ⟨left, leftSchema⟩ := first
    obtain ⟨right, rightSchema⟩ := second
    have leftKnown := table.registered (left, leftSchema) firstMember
    have rightKnown := table.registered (right, rightSchema) secondMember
    have same := context.uniqueConstantNames left right leftSchema rightSchema leftKnown rightKnown sameName
    subst right
    exact Prod.ext rfl (Option.some.inj (leftKnown.symm.trans rightKnown))
  · intro entry member
    rw [signature_ofTable]
    exact context.constantTypes entry.1 entry.2 (table.registered entry member)

private theorem context_equal {first second : TheoryContext}
    (names : first.names = second.names) (signature : first.signature = second.signature) : first = second := by
  cases first
  cases second
  cases names
  cases signature
  rfl

theorem toContext_ofTable {context : TheoryContext} (table : DeclarationTable.Table context)
    (formed : WellFormed (ofTable table)) : toContext (ofTable table) formed = context :=
  context_equal rfl (signature_ofTable table)

theorem decode_ofTable {context : TheoryContext} (table : DeclarationTable.Table context) :
    decode (ofTable table) = some context := by
  unfold decode
  rw [dif_pos ((valid_iff _).mpr (ofTable_wellFormed table))]
  exact congrArg some (toContext_ofTable table _)

theorem wire_decode_ofTable {context : TheoryContext} (table : DeclarationTable.Table context) :
    (codec.get (codec.put (ofTable table))).bind decode = some context := by
  rw [codec.get_put]
  exact decode_ofTable table

theorem of_decoded_table (data : ContextData) (formed : WellFormed data) :
    ofTable (toTable data formed) = data := rfl

end Mettapedia.Logic.TierZero.Adequacy.HOLLightFiniteContextSource
