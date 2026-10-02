import Mettapedia.GSLT.LanguageDef.CostConstruction

/-!
# Closed key and signature syntax of the generated Cost apparatus

Exact finite keys and their monoid-valued commitments belong to the generic
Cost grammar. Decoder admission and the semantics of a specific reflective
language are separate consumers of these constructor shapes.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Cost.SignatureSyntax

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- The original unit/product subgrammar, kept distinct from commitments. -/
inductive LegacyLiteralSignatureSyntax : Pattern → Prop where
  | unit : LegacyLiteralSignatureSyntax (.apply costSignatureUnitConstructorName [])
  | product {left right} : LegacyLiteralSignatureSyntax left → LegacyLiteralSignatureSyntax right →
      LegacyLiteralSignatureSyntax (.apply costSignatureProductConstructorName [left, right])

mutual
  inductive LiteralKeySyntax : Pattern → Prop where
    | leaf : LiteralKeySyntax (.apply costKeyLeafConstructorName [])
    | branch {left right} : LiteralKeySyntax left → LiteralKeySyntax right →
        LiteralKeySyntax (.apply costKeyBranchConstructorName [left, right])

  inductive LiteralSignatureSyntax : Pattern → Prop where
    | unit : LiteralSignatureSyntax (.apply costSignatureUnitConstructorName [])
    | product {left right} : LiteralSignatureSyntax left → LiteralSignatureSyntax right →
        LiteralSignatureSyntax (.apply costSignatureProductConstructorName [left, right])
    | commit {key} : LiteralKeySyntax key →
        LiteralSignatureSyntax (.apply costSignatureCommitConstructorName [key])
end

theorem LegacyLiteralSignatureSyntax.toLiteralSignatureSyntax {source : Pattern}
    (grammar : LegacyLiteralSignatureSyntax source) : LiteralSignatureSyntax source := by
  induction grammar with
  | unit => exact .unit
  | product left right leftIH rightIH => exact .product leftIH rightIH

end Mettapedia.GSLT.LanguageDef.Cost.SignatureSyntax
