import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSelectedMeaning

/-! Local source policies can be proved on CST nodes before selecting a
parser certificate. Exact row labels and spans transport that evidence to
every family of any derivation of the tree. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceTreePolicy

open Mettapedia.GSLT.Parsing
open ParserProfileSemantics PresentationExprSemantics
open ClassAwareParserPackCorrespondence ClassAwareParserPackCertificate ClassAwarePackedForest

mutual
  def Holds (policy : String → Nat → Nat → Prop) : CST → Prop
    | .terminal _ _ _ => True
    | .node label start stop children => policy label start stop ∧ ChildrenHold policy children

  def ChildrenHold (policy : String → Nat → Nat → Prop) : List CST → Prop
    | [] => True
    | first :: rest => Holds policy first ∧ ChildrenHold policy rest
end

mutual
  theorem selects {profile : ParserProfileLayer} {plan : CompiledParserPackPlan} {input : List Nat}
      (filters : List SourceSyntax.FamilyFilter) (policy : String → Nat → Nat → Prop)
      (lexical : ∀ row ∈ plan.lexical.productions, ∀ start stop, policy row.label start stop →
        filters.all (SourceSyntax.FamilyFilter.allows row.resultSort
          ((input.drop start).take (stop - start)) (input.drop stop)) = true)
      (structural : ∀ row ∈ plan.structural, ∀ start stop, policy row.label start stop →
        filters.all (SourceSyntax.FamilyFilter.allows row.resultSort
          ((input.drop start).take (stop - start)) (input.drop stop)) = true)
      {sort : String} {start stop : Nat} {tree : CST}
      (derived : ParserPackDerivesAt profile plan input sort start stop tree)
      (holds : Holds policy tree) :
      SourcePacketSelection.selected (SourcePacketSelection.allows filters input) sort
        (Certificate.ofDerivation derived) = true :=
    match derived with
    | .lexical position valid matcher result label matched => by
      simp only [Certificate.ofDerivation, SourcePacketSelection.selected,
        SourcePacketSelection.allows, certificateFamily]
      rw [← result]
      exact lexical _ (List.get_mem _ ⟨position, valid⟩) _ _ (label ▸ holds.1)
    | .structural position valid result label body => by
      simp only [Certificate.ofDerivation, SourcePacketSelection.selected,
        SourcePacketSelection.allows, certificateFamily, Bool.and_eq_true]
      refine ⟨?_, selectsItems filters policy lexical structural body holds.2⟩
      rw [← result]
      exact structural _ (List.get_mem _ ⟨position, valid⟩) _ _ (label ▸ holds.1)
    termination_by structural derived

  theorem selectsItems {profile : ParserProfileLayer} {plan : CompiledParserPackPlan} {input : List Nat}
      (filters : List SourceSyntax.FamilyFilter) (policy : String → Nat → Nat → Prop)
      (lexical : ∀ row ∈ plan.lexical.productions, ∀ start stop, policy row.label start stop →
        filters.all (SourceSyntax.FamilyFilter.allows row.resultSort
          ((input.drop start).take (stop - start)) (input.drop stop)) = true)
      (structural : ∀ row ∈ plan.structural, ∀ start stop, policy row.label start stop →
        filters.all (SourceSyntax.FamilyFilter.allows row.resultSort
          ((input.drop start).take (stop - start)) (input.drop stop)) = true)
      {items : List PackItem} {start stop : Nat} {children : List CST}
      (derived : ParserPackItemsDeriveAt profile plan input items start stop children)
      (holds : ChildrenHold policy children) :
      SourcePacketSelection.selectedItems (SourcePacketSelection.allows filters input)
        (ItemsCertificate.ofDerivation derived) = true :=
    match derived with
    | .nil => rfl
    | .terminal _ rest => selectsItems filters policy lexical structural rest holds
    | .nonterminal head rest => by
      simp only [ItemsCertificate.ofDerivation, SourcePacketSelection.selectedItems, Bool.and_eq_true]
      exact ⟨selects filters policy lexical structural head holds.1,
        selectsItems filters policy lexical structural rest holds.2⟩
    termination_by structural derived
end

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceTreePolicy
