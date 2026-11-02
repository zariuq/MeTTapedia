import Mettapedia.GSLT.LanguageDef.ModuleFormat.ScalarSyntaxCST
import Mettapedia.GSLT.LanguageDef.ModuleFormat.ScalarSyntaxLeafInverse
import Mettapedia.GSLT.Parsing.LanguageDefScalarSequence

/-! Successful printing has an original source derivation and reconstructs
the exact syntax core. The theorem is generic in the authored grammar and
lexical profile; native parser coverage remains a separate obligation. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.ScalarSyntaxCore

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.Parsing
open LanguageDefScalarSyntax LanguageDefScalarPrinter PresentationExprSemantics
open ClassAwareParserPackCorrespondence

mutual
  theorem print_source (description : Description) (sort : String) (pattern : Pattern) (points : List Nat)
      (printed : printScalars? description sort pattern = some points)
      {input : List Nat} {start stop : Nat}
      (matched : ScalarSequenceMatchesAt input points start stop) :
      ∃ tree, ∃ source : DerivesAt (fun text => some (stringScalars text))
        description.profile description.grammar input sort start stop tree,
        reify description source = pattern := by
    cases pattern with
    | apply label children =>
      unfold printScalars? at printed
      rw [DeclaredConstructorPrinter.print?] at printed
      cases picked : lexicalRow? description sort with
      | some row =>
        have read : (readLeaf? description row (.apply label children)).map (· :: []) = some points := by
          simpa only [lexicalPrinter, picked, Option.map_some] using printed
        obtain ⟨point, decoded, rfl⟩ := Option.map_eq_some_iff.mp read
        have sameSort := lexicalRow?_sort picked
        subst sort
        cases matched with
        | cons lookup rest =>
          cases rest
          obtain ⟨formed, same⟩ := readLeaf?_inverse decoded
          exact ⟨_, .lexical row lookup formed, same⟩
      | none =>
        simp only [lexicalPrinter, picked, Option.map_none, Option.bind_eq_bind] at printed
        obtain ⟨row, selected, body⟩ := Option.bind_eq_some_iff.mp printed
        obtain ⟨member, labelEq, sortEq⟩ := constructor?_meaning selected
        obtain ⟨index, rowEq⟩ := List.mem_iff_get.mp member
        subst row
        subst label
        subst sort
        obtain ⟨trees, source, same⟩ := printItems_source description _ _ children points body matched
        refine ⟨_, .structural index source, ?_⟩
        simp only [reify, same]
    | _ => simp [printScalars?, DeclaredConstructorPrinter.print?] at printed
  termination_by (sizeOf pattern, 0)

  theorem printItems_source (description : Description) (rule : GrammarRule)
      (items : List SyntaxItem) (children : List Pattern) (points : List Nat)
      (printed : DeclaredConstructorPrinter.printItems? description.grammar stringScalars
        (lexicalPrinter description) rule items children = some points)
      {input : List Nat} {start stop : Nat}
      (matched : ScalarSequenceMatchesAt input points start stop) :
      ∃ trees, ∃ source : ItemsDeriveAt (fun text => some (stringScalars text))
        description.profile description.grammar input rule items start stop trees,
        reifyItems description source = children := by
    match items, children with
    | [], [] =>
      have same : ([] : List Nat) = points := by simpa only [DeclaredConstructorPrinter.printItems?, Option.some.injEq] using printed
      subst points
      cases matched
      exact ⟨[], .nil, rfl⟩
    | .terminal token :: rest, children =>
      rw [DeclaredConstructorPrinter.printItems?] at printed
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at printed
      obtain ⟨later, restPrinted, rfl⟩ := printed
      obtain ⟨middle, ⟨tokenMatched⟩, ⟨restMatched⟩⟩ := sequence_split matched
      obtain ⟨trees, source, same⟩ := printItems_source description rule rest children later restPrinted restMatched
      exact ⟨trees, .terminal rfl tokenMatched source, same⟩
    | .nonTerminal parameter :: rest, head :: tail =>
      rw [DeclaredConstructorPrinter.printItems?] at printed
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at printed
      obtain ⟨sort, lookup, first, headPrinted, later, tailPrinted, rfl⟩ := printed
      obtain ⟨middle, ⟨headMatched⟩, ⟨tailMatched⟩⟩ := sequence_split matched
      obtain ⟨tree, headSource, headSame⟩ := print_source description sort head first headPrinted headMatched
      obtain ⟨trees, tailSource, tailSame⟩ := printItems_source description rule rest tail later tailPrinted tailMatched
      refine ⟨tree :: trees, .nonterminal lookup headSource tailSource, ?_⟩
      simp only [reifyItems, headSame, tailSame]
    | [], _ :: _ => simp [DeclaredConstructorPrinter.printItems?] at printed
    | .nonTerminal _ :: _, [] => simp [DeclaredConstructorPrinter.printItems?] at printed
    | .separator _ :: _, _ => simp [DeclaredConstructorPrinter.printItems?] at printed
    | .delimiter _ _ :: _, _ => simp [DeclaredConstructorPrinter.printItems?] at printed
    | .op _ :: _, _ => simp [DeclaredConstructorPrinter.printItems?] at printed
  termination_by (sizeOf children, items.length + 1)
end

theorem printed_source_readback (description : Description) (shape : Shape description)
    (sort : String) (pattern : Pattern) (points : List Nat)
    (printed : printScalars? description sort pattern = some points) :
    ∃ tree, Nonempty (DerivesAt (fun text => some (stringScalars text))
      description.profile description.grammar points sort 0 points.length tree) ∧
      lowerCST? description sort tree = some pattern := by
  obtain ⟨tree, source, same⟩ := print_source description sort pattern points printed (sequence_self points)
  exact ⟨tree, ⟨source⟩, by rw [lowerCST_source description shape source, same]⟩

end Mettapedia.GSLT.LanguageDef.ModuleFormat.ScalarSyntaxCore
