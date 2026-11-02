import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceTreePolicy
import Mettapedia.GSLT.LanguageDef.ModuleFormat.ScalarSyntaxPrinting

/-! Compositional invariants on retained source constructors transport to
their source trees. Applications check their root and every ordered child;
no property of the native packet producer is needed. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SourcePatternPolicy

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.Parsing
open PresentationExprSemantics LanguageDefScalarSyntax
open ScalarSyntaxCore

mutual
  def Holds (policy : String → List Pattern → Prop) : Pattern → Prop
    | .apply label children => policy label children ∧ ChildrenHold policy children
    | _ => True

  def ChildrenHold (policy : String → List Pattern → Prop) : List Pattern → Prop
    | [] => True
    | first :: rest => Holds policy first ∧ ChildrenHold policy rest
end

theorem children_iff (policy : String → List Pattern → Prop) (children : List Pattern) :
    ChildrenHold policy children ↔ ∀ child ∈ children, Holds policy child := by
  induction children with
  | nil => simp [ChildrenHold]
  | cons head tail ih => simp only [ChildrenHold, ih, List.forall_mem_cons]

mutual
  theorem reify_tree (description : Description) (patternPolicy : String → List Pattern → Prop)
      (treePolicy : String → Nat → Nat → Prop) {input : List Nat}
      (lexical : ∀ row : Fin description.profile.states.length, ∀ start stop,
        treePolicy (description.profile.states.get row).ruleLabel start stop)
      (structural : ∀ (row : Fin description.grammar.terms.length) {start stop children}
        (source : ItemsDeriveAt SourceSyntaxExport.literalScalars? description.profile description.grammar input
          (description.grammar.terms.get row) (description.grammar.terms.get row).syntaxPattern start stop children),
        patternPolicy (description.grammar.terms.get row).label (reifyItems description source) →
        treePolicy (description.grammar.terms.get row).label start stop)
      {sort : String} {start stop : Nat} {tree : CST}
      (source : DerivesAt SourceSyntaxExport.literalScalars? description.profile description.grammar input
        sort start stop tree) (holds : Holds patternPolicy (reify description source)) :
      SourceTreePolicy.Holds treePolicy tree :=
    match source with
    | .lexical row _ _ => ⟨lexical row _ _, trivial, trivial⟩
    | .structural row body => ⟨structural row body holds.1,
        reifyItems_tree description patternPolicy treePolicy lexical structural body holds.2⟩
    termination_by structural source

  theorem reifyItems_tree (description : Description) (patternPolicy : String → List Pattern → Prop)
      (treePolicy : String → Nat → Nat → Prop) {input : List Nat}
      (lexical : ∀ row : Fin description.profile.states.length, ∀ start stop,
        treePolicy (description.profile.states.get row).ruleLabel start stop)
      (structural : ∀ (row : Fin description.grammar.terms.length) {start stop children}
        (source : ItemsDeriveAt SourceSyntaxExport.literalScalars? description.profile description.grammar input
          (description.grammar.terms.get row) (description.grammar.terms.get row).syntaxPattern start stop children),
        patternPolicy (description.grammar.terms.get row).label (reifyItems description source) →
        treePolicy (description.grammar.terms.get row).label start stop)
      {row : GrammarRule} {items : List SyntaxItem} {start stop : Nat} {children : List CST}
      (source : ItemsDeriveAt SourceSyntaxExport.literalScalars? description.profile description.grammar input
        row items start stop children) (holds : ChildrenHold patternPolicy (reifyItems description source)) :
      SourceTreePolicy.ChildrenHold treePolicy children :=
    match source with
    | .nil => trivial
    | .terminal _ _ rest => reifyItems_tree description patternPolicy treePolicy lexical structural rest holds
    | .nonterminal _ head rest => ⟨reify_tree description patternPolicy treePolicy lexical structural head holds.1,
        reifyItems_tree description patternPolicy treePolicy lexical structural rest holds.2⟩
    termination_by structural source
end

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SourcePatternPolicy
