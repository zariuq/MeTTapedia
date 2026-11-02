import Mettapedia.GSLT.LanguageDef.ModuleFormat.ScalarSyntaxFormation
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogPrinterShared
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogSourcePrinter

/-! Finite constructor views checked against the authored Datalog grammar.
The source module remains the authority for every label, result sort and
ordered parameter vector. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePrinter.Formation

open Mettapedia.OSLF.MeTTaIL.Syntax
open ScalarSyntaxCore
abbrev Formed := ScalarSyntaxCore.Formed description

theorem program {p0 p1 : Pattern}
    (h0 : Formed "DlTrivia" p0)
    (h1 : Formed "DlItems" p1) :
    Formed "DlProgram" (node "program" [p0, p1]) := by
  apply constructor_formed description ⟨0, by decide +kernel⟩ "DlProgram" "dl-src:program" [.simple "leading" (.base "DlTrivia"), .simple "items" (.base "DlItems")] [p0, p1]
  · decide +kernel
  · exact (.cons h0 (.cons h1 .nil))

theorem items_empty :
    Formed "DlItems" (node "items-empty" []) := by
  apply constructor_formed description ⟨1, by decide +kernel⟩ "DlItems" "dl-src:items-empty" [] []
  · decide +kernel
  · exact .nil

theorem items_more {p0 p1 p2 : Pattern}
    (h0 : Formed "DlItem" p0)
    (h1 : Formed "DlTrivia" p1)
    (h2 : Formed "DlItems" p2) :
    Formed "DlItems" (node "items-more" [p0, p1, p2]) := by
  apply constructor_formed description ⟨2, by decide +kernel⟩ "DlItems" "dl-src:items-more" [.simple "head" (.base "DlItem"), .simple "gap" (.base "DlTrivia"), .simple "tail" (.base "DlItems")] [p0, p1, p2]
  · decide +kernel
  · exact (.cons h0 (.cons h1 (.cons h2 .nil)))

theorem item_declaration {p0 : Pattern}
    (h0 : Formed "DlDeclaration" p0) :
    Formed "DlItem" (node "item-declaration" [p0]) := by
  apply constructor_formed description ⟨3, by decide +kernel⟩ "DlItem" "dl-src:item-declaration" [.simple "value" (.base "DlDeclaration")] [p0]
  · decide +kernel
  · exact (.cons h0 .nil)

theorem item_fact {p0 : Pattern}
    (h0 : Formed "DlFact" p0) :
    Formed "DlItem" (node "item-fact" [p0]) := by
  apply constructor_formed description ⟨4, by decide +kernel⟩ "DlItem" "dl-src:item-fact" [.simple "value" (.base "DlFact")] [p0]
  · decide +kernel
  · exact (.cons h0 .nil)

theorem item_rule {p0 : Pattern}
    (h0 : Formed "DlRule" p0) :
    Formed "DlItem" (node "item-rule" [p0]) := by
  apply constructor_formed description ⟨5, by decide +kernel⟩ "DlItem" "dl-src:item-rule" [.simple "value" (.base "DlRule")] [p0]
  · decide +kernel
  · exact (.cons h0 .nil)

theorem item_input {p0 : Pattern}
    (h0 : Formed "DlInput" p0) :
    Formed "DlItem" (node "item-input" [p0]) := by
  apply constructor_formed description ⟨6, by decide +kernel⟩ "DlItem" "dl-src:item-input" [.simple "value" (.base "DlInput")] [p0]
  · decide +kernel
  · exact (.cons h0 .nil)

theorem item_output {p0 : Pattern}
    (h0 : Formed "DlOutput" p0) :
    Formed "DlItem" (node "item-output" [p0]) := by
  apply constructor_formed description ⟨7, by decide +kernel⟩ "DlItem" "dl-src:item-output" [.simple "value" (.base "DlOutput")] [p0]
  · decide +kernel
  · exact (.cons h0 .nil)

theorem declaration {p0 p1 p2 p3 p4 : Pattern}
    (h0 : Formed "DlDirectiveSpace" p0)
    (h1 : Formed "DlRelations" p1)
    (h2 : Formed "DlTrivia" p2)
    (h3 : Formed "DlTrivia" p3)
    (h4 : Formed "DlAttributes" p4) :
    Formed "DlDeclaration" (node "declaration" [p0, p1, p2, p3, p4]) := by
  apply constructor_formed description ⟨8, by decide +kernel⟩ "DlDeclaration" "dl-src:declaration" [.simple "space" (.base "DlDirectiveSpace"), .simple "relations" (.base "DlRelations"), .simple "before" (.base "DlTrivia"), .simple "start" (.base "DlTrivia"), .simple "attributes" (.base "DlAttributes")] [p0, p1, p2, p3, p4]
  · decide +kernel
  · exact (.cons h0 (.cons h1 (.cons h2 (.cons h3 (.cons h4 .nil)))))

theorem relations_one {p0 : Pattern}
    (h0 : Formed "DlIdentifier" p0) :
    Formed "DlRelations" (node "relations-one" [p0]) := by
  apply constructor_formed description ⟨9, by decide +kernel⟩ "DlRelations" "dl-src:relations-one" [.simple "relation" (.base "DlIdentifier")] [p0]
  · decide +kernel
  · exact (.cons h0 .nil)

theorem attributes_empty :
    Formed "DlAttributes" (node "attributes-empty" []) := by
  apply constructor_formed description ⟨11, by decide +kernel⟩ "DlAttributes" "dl-src:attributes-empty" [] []
  · decide +kernel
  · exact .nil

theorem attributes_one {p0 p1 : Pattern}
    (h0 : Formed "DlAttribute" p0)
    (h1 : Formed "DlTrivia" p1) :
    Formed "DlAttributes" (node "attributes-one" [p0, p1]) := by
  apply constructor_formed description ⟨12, by decide +kernel⟩ "DlAttributes" "dl-src:attributes-one" [.simple "attr" (.base "DlAttribute"), .simple "trailing" (.base "DlTrivia")] [p0, p1]
  · decide +kernel
  · exact (.cons h0 (.cons h1 .nil))

theorem attributes_more {p0 p1 p2 p3 : Pattern}
    (h0 : Formed "DlAttribute" p0)
    (h1 : Formed "DlTrivia" p1)
    (h2 : Formed "DlTrivia" p2)
    (h3 : Formed "DlAttributes" p3) :
    Formed "DlAttributes" (node "attributes-more" [p0, p1, p2, p3]) := by
  apply constructor_formed description ⟨13, by decide +kernel⟩ "DlAttributes" "dl-src:attributes-more" [.simple "head" (.base "DlAttribute"), .simple "before" (.base "DlTrivia"), .simple "after" (.base "DlTrivia"), .simple "tail" (.base "DlAttributes")] [p0, p1, p2, p3]
  · decide +kernel
  · exact (.cons h0 (.cons h1 (.cons h2 (.cons h3 .nil))))

theorem attr {p0 p1 p2 p3 : Pattern}
    (h0 : Formed "DlIdentifier" p0)
    (h1 : Formed "DlTrivia" p1)
    (h2 : Formed "DlTrivia" p2)
    (h3 : Formed "DlPrimitiveType" p3) :
    Formed "DlAttribute" (node "attr" [p0, p1, p2, p3]) := by
  apply constructor_formed description ⟨14, by decide +kernel⟩ "DlAttribute" "dl-src:attr" [.simple "attr" (.base "DlIdentifier"), .simple "before" (.base "DlTrivia"), .simple "after" (.base "DlTrivia"), .simple "attributeType" (.base "DlPrimitiveType")] [p0, p1, p2, p3]
  · decide +kernel
  · exact (.cons h0 (.cons h1 (.cons h2 (.cons h3 .nil))))

theorem type_symbol :
    Formed "DlPrimitiveType" (node "type-symbol" []) := by
  apply constructor_formed description ⟨15, by decide +kernel⟩ "DlPrimitiveType" "dl-src:type-symbol" [] []
  · decide +kernel
  · exact .nil

theorem type_number :
    Formed "DlPrimitiveType" (node "type-number" []) := by
  apply constructor_formed description ⟨16, by decide +kernel⟩ "DlPrimitiveType" "dl-src:type-number" [] []
  · decide +kernel
  · exact .nil

theorem type_unsigned :
    Formed "DlPrimitiveType" (node "type-unsigned" []) := by
  apply constructor_formed description ⟨17, by decide +kernel⟩ "DlPrimitiveType" "dl-src:type-unsigned" [] []
  · decide +kernel
  · exact .nil

theorem input {p0 p1 : Pattern}
    (h0 : Formed "DlDirectiveSpace" p0)
    (h1 : Formed "DlQualifiedName" p1) :
    Formed "DlInput" (node "input" [p0, p1]) := by
  apply constructor_formed description ⟨19, by decide +kernel⟩ "DlInput" "dl-src:input" [.simple "space" (.base "DlDirectiveSpace"), .simple "relation" (.base "DlQualifiedName")] [p0, p1]
  · decide +kernel
  · exact (.cons h0 (.cons h1 .nil))

theorem output {p0 p1 : Pattern}
    (h0 : Formed "DlDirectiveSpace" p0)
    (h1 : Formed "DlQualifiedName" p1) :
    Formed "DlOutput" (node "output" [p0, p1]) := by
  apply constructor_formed description ⟨20, by decide +kernel⟩ "DlOutput" "dl-src:output" [.simple "space" (.base "DlDirectiveSpace"), .simple "relation" (.base "DlQualifiedName")] [p0, p1]
  · decide +kernel
  · exact (.cons h0 (.cons h1 .nil))

theorem fact {p0 p1 : Pattern}
    (h0 : Formed "DlGroundAtom" p0)
    (h1 : Formed "DlTrivia" p1) :
    Formed "DlFact" (node "fact" [p0, p1]) := by
  apply constructor_formed description ⟨21, by decide +kernel⟩ "DlFact" "dl-src:fact" [.simple "atom" (.base "DlGroundAtom"), .simple "gap" (.base "DlTrivia")] [p0, p1]
  · decide +kernel
  · exact (.cons h0 (.cons h1 .nil))

theorem rule {p0 p1 p2 p3 : Pattern}
    (h0 : Formed "DlAtom" p0)
    (h1 : Formed "DlTrivia" p1)
    (h2 : Formed "DlTrivia" p2)
    (h3 : Formed "DlBody" p3) :
    Formed "DlRule" (node "rule" [p0, p1, p2, p3]) := by
  apply constructor_formed description ⟨22, by decide +kernel⟩ "DlRule" "dl-src:rule" [.simple "head" (.base "DlAtom"), .simple "before" (.base "DlTrivia"), .simple "after" (.base "DlTrivia"), .simple "body" (.base "DlBody")] [p0, p1, p2, p3]
  · decide +kernel
  · exact (.cons h0 (.cons h1 (.cons h2 (.cons h3 .nil))))

theorem body_one {p0 p1 : Pattern}
    (h0 : Formed "DlPositiveLiteral" p0)
    (h1 : Formed "DlTrivia" p1) :
    Formed "DlBody" (node "body-one" [p0, p1]) := by
  apply constructor_formed description ⟨23, by decide +kernel⟩ "DlBody" "dl-src:body-one" [.simple "literal" (.base "DlPositiveLiteral"), .simple "trailing" (.base "DlTrivia")] [p0, p1]
  · decide +kernel
  · exact (.cons h0 (.cons h1 .nil))

theorem body_more {p0 p1 p2 p3 : Pattern}
    (h0 : Formed "DlPositiveLiteral" p0)
    (h1 : Formed "DlTrivia" p1)
    (h2 : Formed "DlTrivia" p2)
    (h3 : Formed "DlBody" p3) :
    Formed "DlBody" (node "body-more" [p0, p1, p2, p3]) := by
  apply constructor_formed description ⟨24, by decide +kernel⟩ "DlBody" "dl-src:body-more" [.simple "head" (.base "DlPositiveLiteral"), .simple "before" (.base "DlTrivia"), .simple "after" (.base "DlTrivia"), .simple "tail" (.base "DlBody")] [p0, p1, p2, p3]
  · decide +kernel
  · exact (.cons h0 (.cons h1 (.cons h2 (.cons h3 .nil))))

theorem positive_atom {p0 : Pattern}
    (h0 : Formed "DlAtom" p0) :
    Formed "DlPositiveLiteral" (node "positive-atom" [p0]) := by
  apply constructor_formed description ⟨25, by decide +kernel⟩ "DlPositiveLiteral" "dl-src:positive-atom" [.simple "atom" (.base "DlAtom")] [p0]
  · decide +kernel
  · exact (.cons h0 .nil)

theorem positive_comparison {p0 : Pattern}
    (h0 : Formed "DlComparison" p0) :
    Formed "DlPositiveLiteral" (node "positive-comparison" [p0]) := by
  apply constructor_formed description ⟨26, by decide +kernel⟩ "DlPositiveLiteral" "dl-src:positive-comparison" [.simple "constraint" (.base "DlComparison")] [p0]
  · decide +kernel
  · exact (.cons h0 .nil)

theorem comparison {p0 p1 p2 p3 p4 : Pattern}
    (h0 : Formed "DlTerm" p0)
    (h1 : Formed "DlTrivia" p1)
    (h2 : Formed "DlComparisonOperator" p2)
    (h3 : Formed "DlTrivia" p3)
    (h4 : Formed "DlTerm" p4) :
    Formed "DlComparison" (node "comparison" [p0, p1, p2, p3, p4]) := by
  apply constructor_formed description ⟨27, by decide +kernel⟩ "DlComparison" "dl-src:comparison" [.simple "left" (.base "DlTerm"), .simple "before" (.base "DlTrivia"), .simple "operator" (.base "DlComparisonOperator"), .simple "after" (.base "DlTrivia"), .simple "right" (.base "DlTerm")] [p0, p1, p2, p3, p4]
  · decide +kernel
  · exact (.cons h0 (.cons h1 (.cons h2 (.cons h3 (.cons h4 .nil)))))

theorem comparison_equal :
    Formed "DlComparisonOperator" (node "comparison-equal" []) := by
  apply constructor_formed description ⟨28, by decide +kernel⟩ "DlComparisonOperator" "dl-src:comparison-equal" [] []
  · decide +kernel
  · exact .nil

theorem comparison_different :
    Formed "DlComparisonOperator" (node "comparison-different" []) := by
  apply constructor_formed description ⟨29, by decide +kernel⟩ "DlComparisonOperator" "dl-src:comparison-different" [] []
  · decide +kernel
  · exact .nil

theorem comparison_less :
    Formed "DlComparisonOperator" (node "comparison-less" []) := by
  apply constructor_formed description ⟨30, by decide +kernel⟩ "DlComparisonOperator" "dl-src:comparison-less" [] []
  · decide +kernel
  · exact .nil

theorem comparison_less_equal :
    Formed "DlComparisonOperator" (node "comparison-less-equal" []) := by
  apply constructor_formed description ⟨31, by decide +kernel⟩ "DlComparisonOperator" "dl-src:comparison-less-equal" [] []
  · decide +kernel
  · exact .nil

theorem comparison_greater :
    Formed "DlComparisonOperator" (node "comparison-greater" []) := by
  apply constructor_formed description ⟨32, by decide +kernel⟩ "DlComparisonOperator" "dl-src:comparison-greater" [] []
  · decide +kernel
  · exact .nil

theorem comparison_greater_equal :
    Formed "DlComparisonOperator" (node "comparison-greater-equal" []) := by
  apply constructor_formed description ⟨33, by decide +kernel⟩ "DlComparisonOperator" "dl-src:comparison-greater-equal" [] []
  · decide +kernel
  · exact .nil

theorem atom {p0 p1 p2 p3 : Pattern}
    (h0 : Formed "DlQualifiedName" p0)
    (h1 : Formed "DlTrivia" p1)
    (h2 : Formed "DlTrivia" p2)
    (h3 : Formed "DlTerms" p3) :
    Formed "DlAtom" (node "atom" [p0, p1, p2, p3]) := by
  apply constructor_formed description ⟨34, by decide +kernel⟩ "DlAtom" "dl-src:atom" [.simple "relation" (.base "DlQualifiedName"), .simple "before" (.base "DlTrivia"), .simple "after" (.base "DlTrivia"), .simple "arguments" (.base "DlTerms")] [p0, p1, p2, p3]
  · decide +kernel
  · exact (.cons h0 (.cons h1 (.cons h2 (.cons h3 .nil))))

theorem ground_atom {p0 p1 p2 p3 : Pattern}
    (h0 : Formed "DlQualifiedName" p0)
    (h1 : Formed "DlTrivia" p1)
    (h2 : Formed "DlTrivia" p2)
    (h3 : Formed "DlConstants" p3) :
    Formed "DlGroundAtom" (node "ground-atom" [p0, p1, p2, p3]) := by
  apply constructor_formed description ⟨35, by decide +kernel⟩ "DlGroundAtom" "dl-src:ground-atom" [.simple "relation" (.base "DlQualifiedName"), .simple "before" (.base "DlTrivia"), .simple "after" (.base "DlTrivia"), .simple "arguments" (.base "DlConstants")] [p0, p1, p2, p3]
  · decide +kernel
  · exact (.cons h0 (.cons h1 (.cons h2 (.cons h3 .nil))))

theorem terms_empty :
    Formed "DlTerms" (node "terms-empty" []) := by
  apply constructor_formed description ⟨36, by decide +kernel⟩ "DlTerms" "dl-src:terms-empty" [] []
  · decide +kernel
  · exact .nil

theorem terms_one {p0 p1 : Pattern}
    (h0 : Formed "DlTerm" p0)
    (h1 : Formed "DlTrivia" p1) :
    Formed "DlTerms" (node "terms-one" [p0, p1]) := by
  apply constructor_formed description ⟨37, by decide +kernel⟩ "DlTerms" "dl-src:terms-one" [.simple "value" (.base "DlTerm"), .simple "trailing" (.base "DlTrivia")] [p0, p1]
  · decide +kernel
  · exact (.cons h0 (.cons h1 .nil))

theorem terms_more {p0 p1 p2 p3 : Pattern}
    (h0 : Formed "DlTerm" p0)
    (h1 : Formed "DlTrivia" p1)
    (h2 : Formed "DlTrivia" p2)
    (h3 : Formed "DlTerms" p3) :
    Formed "DlTerms" (node "terms-more" [p0, p1, p2, p3]) := by
  apply constructor_formed description ⟨38, by decide +kernel⟩ "DlTerms" "dl-src:terms-more" [.simple "head" (.base "DlTerm"), .simple "before" (.base "DlTrivia"), .simple "after" (.base "DlTrivia"), .simple "tail" (.base "DlTerms")] [p0, p1, p2, p3]
  · decide +kernel
  · exact (.cons h0 (.cons h1 (.cons h2 (.cons h3 .nil))))

theorem constants_empty :
    Formed "DlConstants" (node "constants-empty" []) := by
  apply constructor_formed description ⟨39, by decide +kernel⟩ "DlConstants" "dl-src:constants-empty" [] []
  · decide +kernel
  · exact .nil

theorem constants_one {p0 p1 : Pattern}
    (h0 : Formed "DlConstant" p0)
    (h1 : Formed "DlTrivia" p1) :
    Formed "DlConstants" (node "constants-one" [p0, p1]) := by
  apply constructor_formed description ⟨40, by decide +kernel⟩ "DlConstants" "dl-src:constants-one" [.simple "value" (.base "DlConstant"), .simple "trailing" (.base "DlTrivia")] [p0, p1]
  · decide +kernel
  · exact (.cons h0 (.cons h1 .nil))

theorem constants_more {p0 p1 p2 p3 : Pattern}
    (h0 : Formed "DlConstant" p0)
    (h1 : Formed "DlTrivia" p1)
    (h2 : Formed "DlTrivia" p2)
    (h3 : Formed "DlConstants" p3) :
    Formed "DlConstants" (node "constants-more" [p0, p1, p2, p3]) := by
  apply constructor_formed description ⟨41, by decide +kernel⟩ "DlConstants" "dl-src:constants-more" [.simple "head" (.base "DlConstant"), .simple "before" (.base "DlTrivia"), .simple "after" (.base "DlTrivia"), .simple "tail" (.base "DlConstants")] [p0, p1, p2, p3]
  · decide +kernel
  · exact (.cons h0 (.cons h1 (.cons h2 (.cons h3 .nil))))

theorem term_variable {p0 : Pattern}
    (h0 : Formed "DlIdentifier" p0) :
    Formed "DlTerm" (node "term-variable" [p0]) := by
  apply constructor_formed description ⟨42, by decide +kernel⟩ "DlTerm" "dl-src:term-variable" [.simple "varRef" (.base "DlIdentifier")] [p0]
  · decide +kernel
  · exact (.cons h0 .nil)

theorem term_anonymous :
    Formed "DlTerm" (node "term-anonymous" []) := by
  apply constructor_formed description ⟨43, by decide +kernel⟩ "DlTerm" "dl-src:term-anonymous" [] []
  · decide +kernel
  · exact .nil

theorem term_constant {p0 : Pattern}
    (h0 : Formed "DlConstant" p0) :
    Formed "DlTerm" (node "term-constant" [p0]) := by
  apply constructor_formed description ⟨44, by decide +kernel⟩ "DlTerm" "dl-src:term-constant" [.simple "constValue" (.base "DlConstant")] [p0]
  · decide +kernel
  · exact (.cons h0 .nil)

theorem constant_symbol {p0 : Pattern}
    (h0 : Formed "DlSymbol" p0) :
    Formed "DlConstant" (node "constant-symbol" [p0]) := by
  apply constructor_formed description ⟨45, by decide +kernel⟩ "DlConstant" "dl-src:constant-symbol" [.simple "value" (.base "DlSymbol")] [p0]
  · decide +kernel
  · exact (.cons h0 .nil)

theorem constant_integer {p0 : Pattern}
    (h0 : Formed "DlInteger" p0) :
    Formed "DlConstant" (node "constant-integer" [p0]) := by
  apply constructor_formed description ⟨46, by decide +kernel⟩ "DlConstant" "dl-src:constant-integer" [.simple "value" (.base "DlInteger")] [p0]
  · decide +kernel
  · exact (.cons h0 .nil)

theorem constant_unsigned {p0 : Pattern}
    (h0 : Formed "DlUnsigned" p0) :
    Formed "DlConstant" (node "constant-unsigned" [p0]) := by
  apply constructor_formed description ⟨47, by decide +kernel⟩ "DlConstant" "dl-src:constant-unsigned" [.simple "value" (.base "DlUnsigned")] [p0]
  · decide +kernel
  · exact (.cons h0 .nil)

theorem qualified_name_one {p0 : Pattern}
    (h0 : Formed "DlIdentifier" p0) :
    Formed "DlQualifiedName" (node "qualified-name-one" [p0]) := by
  apply constructor_formed description ⟨49, by decide +kernel⟩ "DlQualifiedName" "dl-src:qualified-name-one" [.simple "identifier" (.base "DlIdentifier")] [p0]
  · decide +kernel
  · exact (.cons h0 .nil)

theorem qualified_name_more {p0 p1 : Pattern}
    (h0 : Formed "DlIdentifier" p0)
    (h1 : Formed "DlQualifiedName" p1) :
    Formed "DlQualifiedName" (node "qualified-name-more" [p0, p1]) := by
  apply constructor_formed description ⟨50, by decide +kernel⟩ "DlQualifiedName" "dl-src:qualified-name-more" [.simple "head" (.base "DlIdentifier"), .simple "tail" (.base "DlQualifiedName")] [p0, p1]
  · decide +kernel
  · exact (.cons h0 (.cons h1 .nil))

theorem identifier_one {p0 : Pattern}
    (h0 : Formed "DlSingleIdentifierScalar" p0) :
    Formed "DlIdentifier" (node "identifier-one" [p0]) := by
  apply constructor_formed description ⟨51, by decide +kernel⟩ "DlIdentifier" "dl-src:identifier-one" [.simple "scalar" (.base "DlSingleIdentifierScalar")] [p0]
  · decide +kernel
  · exact (.cons h0 .nil)

theorem identifier_more {p0 p1 : Pattern}
    (h0 : Formed "DlIdentifierFirstScalar" p0)
    (h1 : Formed "DlIdentifierNonempty" p1) :
    Formed "DlIdentifier" (node "identifier-more" [p0, p1]) := by
  apply constructor_formed description ⟨52, by decide +kernel⟩ "DlIdentifier" "dl-src:identifier-more" [.simple "head" (.base "DlIdentifierFirstScalar"), .simple "tail" (.base "DlIdentifierNonempty")] [p0, p1]
  · decide +kernel
  · exact (.cons h0 (.cons h1 .nil))

theorem identifier_tail_one {p0 : Pattern}
    (h0 : Formed "DlIdentifierRestScalar" p0) :
    Formed "DlIdentifierNonempty" (node "identifier-tail-one" [p0]) := by
  apply constructor_formed description ⟨53, by decide +kernel⟩ "DlIdentifierNonempty" "dl-src:identifier-tail-one" [.simple "scalar" (.base "DlIdentifierRestScalar")] [p0]
  · decide +kernel
  · exact (.cons h0 .nil)

theorem identifier_tail_more {p0 p1 : Pattern}
    (h0 : Formed "DlIdentifierRestScalar" p0)
    (h1 : Formed "DlIdentifierNonempty" p1) :
    Formed "DlIdentifierNonempty" (node "identifier-tail-more" [p0, p1]) := by
  apply constructor_formed description ⟨54, by decide +kernel⟩ "DlIdentifierNonempty" "dl-src:identifier-tail-more" [.simple "head" (.base "DlIdentifierRestScalar"), .simple "tail" (.base "DlIdentifierNonempty")] [p0, p1]
  · decide +kernel
  · exact (.cons h0 (.cons h1 .nil))

theorem integer_decimal {p0 : Pattern}
    (h0 : Formed "DlDigits" p0) :
    Formed "DlInteger" (node "integer-decimal" [p0]) := by
  apply constructor_formed description ⟨55, by decide +kernel⟩ "DlInteger" "dl-src:integer-decimal" [.simple "digits" (.base "DlDigits")] [p0]
  · decide +kernel
  · exact (.cons h0 .nil)

theorem integer_negative {p0 : Pattern}
    (h0 : Formed "DlDigits" p0) :
    Formed "DlInteger" (node "integer-negative" [p0]) := by
  apply constructor_formed description ⟨56, by decide +kernel⟩ "DlInteger" "dl-src:integer-negative" [.simple "digits" (.base "DlDigits")] [p0]
  · decide +kernel
  · exact (.cons h0 .nil)

theorem unsigned_decimal {p0 : Pattern}
    (h0 : Formed "DlDigits" p0) :
    Formed "DlUnsigned" (node "unsigned-decimal" [p0]) := by
  apply constructor_formed description ⟨61, by decide +kernel⟩ "DlUnsigned" "dl-src:unsigned-decimal" [.simple "digits" (.base "DlDigits")] [p0]
  · decide +kernel
  · exact (.cons h0 .nil)

theorem digits_one {p0 : Pattern}
    (h0 : Formed "DlDigitScalar" p0) :
    Formed "DlDigits" (node "digits-one" [p0]) := by
  apply constructor_formed description ⟨66, by decide +kernel⟩ "DlDigits" "dl-src:digits-one" [.simple "digit" (.base "DlDigitScalar")] [p0]
  · decide +kernel
  · exact (.cons h0 .nil)

theorem digits_more {p0 p1 : Pattern}
    (h0 : Formed "DlDigitScalar" p0)
    (h1 : Formed "DlDigits" p1) :
    Formed "DlDigits" (node "digits-more" [p0, p1]) := by
  apply constructor_formed description ⟨67, by decide +kernel⟩ "DlDigits" "dl-src:digits-more" [.simple "head" (.base "DlDigitScalar"), .simple "tail" (.base "DlDigits")] [p0, p1]
  · decide +kernel
  · exact (.cons h0 (.cons h1 .nil))

theorem symbol {p0 : Pattern}
    (h0 : Formed "DlSymbolBody" p0) :
    Formed "DlSymbol" (node "symbol" [p0]) := by
  apply constructor_formed description ⟨72, by decide +kernel⟩ "DlSymbol" "dl-src:symbol" [.simple "body" (.base "DlSymbolBody")] [p0]
  · decide +kernel
  · exact (.cons h0 .nil)

theorem symbol_empty :
    Formed "DlSymbolBody" (node "symbol-empty" []) := by
  apply constructor_formed description ⟨73, by decide +kernel⟩ "DlSymbolBody" "dl-src:symbol-empty" [] []
  · decide +kernel
  · exact .nil

theorem symbol_body {p0 p1 : Pattern}
    (h0 : Formed "DlStringScalar" p0)
    (h1 : Formed "DlSymbolBody" p1) :
    Formed "DlSymbolBody" (node "symbol-body" [p0, p1]) := by
  apply constructor_formed description ⟨74, by decide +kernel⟩ "DlSymbolBody" "dl-src:symbol-body" [.simple "head" (.base "DlStringScalar"), .simple "tail" (.base "DlSymbolBody")] [p0, p1]
  · decide +kernel
  · exact (.cons h0 (.cons h1 .nil))

theorem symbol_escape {p0 p1 : Pattern}
    (h0 : Formed "DlEscape" p0)
    (h1 : Formed "DlSymbolBody" p1) :
    Formed "DlSymbolBody" (node "symbol-escape" [p0, p1]) := by
  apply constructor_formed description ⟨75, by decide +kernel⟩ "DlSymbolBody" "dl-src:symbol-escape" [.simple "head" (.base "DlEscape"), .simple "tail" (.base "DlSymbolBody")] [p0, p1]
  · decide +kernel
  · exact (.cons h0 (.cons h1 .nil))

theorem escape_quote :
    Formed "DlEscape" (node "escape-quote" []) := by
  apply constructor_formed description ⟨76, by decide +kernel⟩ "DlEscape" "dl-src:escape-quote" [] []
  · decide +kernel
  · exact .nil

theorem escape_slash :
    Formed "DlEscape" (node "escape-slash" []) := by
  apply constructor_formed description ⟨78, by decide +kernel⟩ "DlEscape" "dl-src:escape-slash" [] []
  · decide +kernel
  · exact .nil

theorem escape_bell :
    Formed "DlEscape" (node "escape-bell" []) := by
  apply constructor_formed description ⟨79, by decide +kernel⟩ "DlEscape" "dl-src:escape-bell" [] []
  · decide +kernel
  · exact .nil

theorem escape_backspace :
    Formed "DlEscape" (node "escape-backspace" []) := by
  apply constructor_formed description ⟨80, by decide +kernel⟩ "DlEscape" "dl-src:escape-backspace" [] []
  · decide +kernel
  · exact .nil

theorem escape_formfeed :
    Formed "DlEscape" (node "escape-formfeed" []) := by
  apply constructor_formed description ⟨81, by decide +kernel⟩ "DlEscape" "dl-src:escape-formfeed" [] []
  · decide +kernel
  · exact .nil

theorem escape_newline :
    Formed "DlEscape" (node "escape-newline" []) := by
  apply constructor_formed description ⟨82, by decide +kernel⟩ "DlEscape" "dl-src:escape-newline" [] []
  · decide +kernel
  · exact .nil

theorem escape_return :
    Formed "DlEscape" (node "escape-return" []) := by
  apply constructor_formed description ⟨83, by decide +kernel⟩ "DlEscape" "dl-src:escape-return" [] []
  · decide +kernel
  · exact .nil

theorem escape_tab :
    Formed "DlEscape" (node "escape-tab" []) := by
  apply constructor_formed description ⟨84, by decide +kernel⟩ "DlEscape" "dl-src:escape-tab" [] []
  · decide +kernel
  · exact .nil

theorem escape_vertical_tab :
    Formed "DlEscape" (node "escape-vertical-tab" []) := by
  apply constructor_formed description ⟨85, by decide +kernel⟩ "DlEscape" "dl-src:escape-vertical-tab" [] []
  · decide +kernel
  · exact .nil

theorem trivia_empty :
    Formed "DlTrivia" (node "trivia-empty" []) := by
  apply constructor_formed description ⟨86, by decide +kernel⟩ "DlTrivia" "dl-src:trivia-empty" [] []
  · decide +kernel
  · exact .nil

theorem trivia_space {p0 p1 : Pattern}
    (h0 : Formed "DlWhitespaceScalar" p0)
    (h1 : Formed "DlTrivia" p1) :
    Formed "DlTrivia" (node "trivia-space" [p0, p1]) := by
  apply constructor_formed description ⟨87, by decide +kernel⟩ "DlTrivia" "dl-src:trivia-space" [.simple "head" (.base "DlWhitespaceScalar"), .simple "tail" (.base "DlTrivia")] [p0, p1]
  · decide +kernel
  · exact (.cons h0 (.cons h1 .nil))

theorem directive_space {p0 p1 : Pattern}
    (h0 : Formed "DlHorizontalSpaceScalar" p0)
    (h1 : Formed "DlTrivia" p1) :
    Formed "DlDirectiveSpace" (node "directive-space" [p0, p1]) := by
  apply constructor_formed description ⟨98, by decide +kernel⟩ "DlDirectiveSpace" "dl-src:directive-space" [.simple "head" (.base "DlHorizontalSpaceScalar"), .simple "tail" (.base "DlTrivia")] [p0, p1]
  · decide +kernel
  · exact (.cons h0 (.cons h1 .nil))

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePrinter.Formation
