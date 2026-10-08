import Mettapedia.GSLT.Parsing.CanonicalSourceHornElaboration
import Mettapedia.GSLT.Parsing.CanonicalSourceQualification
import Mettapedia.OSLF.MeTTaIL.MeTTaPinnedSourceQuotation
import Std.Data.String.ToInt
import Lean.Meta.Eval

/-!
# Admission of the retained authored MM0 sources

The exact retained syntax is compared independently with ordinary source
constructors. The existing canonical decoder and Horn elaborator supply the
admission boundaries. File reading is a quotation boundary; source digests
do not supply semantic judgments.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

namespace Mettapedia.Languages.MM0.MeTTa.TextualAuthoredSource

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.GSLT.Parsing
open HornCertificate
open Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT
open CanonicalSourceHornElaboration
open scoped Mettapedia.OSLF.MeTTaIL.MeTTaPinnedSourceQuotation

/-! Constructor caching is confined to static authored GSLT quotation. Every
cached value below must be compared with the retained S-expression in a
kernel proof before it supplies an admission theorem. -/
meta section

open Lean Elab Term

private partial def sourceExpr (raw : SExpr) : Expr :=
  match raw with
  | .atom token => mkApp (mkConst ``SExpr.atom) (toExpr token)
  | .list items => mkApp (mkConst ``SExpr.list)
      (items.foldr (fun item tail => mkApp3 (mkConst ``List.cons [0])
        (mkConst ``SExpr) (sourceExpr item) tail)
        (mkApp (mkConst ``List.nil [0]) (mkConst ``SExpr)))

private instance : ToExpr SExpr where
  toExpr := sourceExpr
  toTypeExpr := mkConst ``SExpr

private instance : ToExpr Operator where
  toExpr operator := mkApp2 (mkConst ``Operator.mk)
    (toExpr operator.name) (toExpr operator.arity)
  toTypeExpr := mkConst ``Operator

private instance : ToExpr Rewrite where
  toExpr rewrite := mkApp3 (mkConst ``Rewrite.mk)
    (toExpr rewrite.name) (toExpr rewrite.head) (toExpr rewrite.body)
  toTypeExpr := mkConst ``Rewrite

private instance : ToExpr Source where
  toExpr source := mkApp4 (mkConst ``Source.mk) (toExpr source.name)
    (toExpr source.operators) (toExpr source.equations) (toExpr source.rewrites)
  toTypeExpr := mkConst ``Source

private def cacheSource (raw : TSyntax `term) : TermElabM Expr := do
  let expression ← elabTerm raw (some (mkConst ``SExpr))
  let decoded ← unsafe Meta.evalExpr (Option Source) (toTypeExpr (Option Source))
    (mkApp (mkConst ``decode) expression)
  let some source := decoded | throwErrorAt raw "canonical source decoder refused quotation"
  pure (toExpr source)

syntax "authored_source% " term:max : term
elab_rules : term
  | `(authored_source% $raw:term) => cacheSource raw

mutual
  private partial def termExpr : Mettapedia.GSLT.Parsing.HornCertificate.Term → Expr
    | .var index => mkApp (mkConst ``Mettapedia.GSLT.Parsing.HornCertificate.Term.var) (toExpr index)
    | .atom name => mkApp (mkConst ``Mettapedia.GSLT.Parsing.HornCertificate.Term.atom) (toExpr name)
    | .integer value => mkApp (mkConst ``Mettapedia.GSLT.Parsing.HornCertificate.Term.integer) (toExpr value)
    | .app name args => mkApp2 (mkConst ``Mettapedia.GSLT.Parsing.HornCertificate.Term.app) (toExpr name) (termsExpr args)
  private partial def termsExpr : Terms → Expr
    | .nil => mkConst ``Terms.nil
    | .cons head tail => mkApp2 (mkConst ``Terms.cons) (termExpr head) (termsExpr tail)
end
private instance : ToExpr Mettapedia.GSLT.Parsing.HornCertificate.Term where
  toExpr := termExpr
  toTypeExpr := mkConst ``Mettapedia.GSLT.Parsing.HornCertificate.Term
private instance : ToExpr Terms where
  toExpr := termsExpr
  toTypeExpr := mkConst ``Terms
private instance : ToExpr Atom where
  toExpr atom := mkApp2 (mkConst ``Atom.mk) (toExpr atom.relation) (toExpr atom.arguments)
  toTypeExpr := mkConst ``Atom
private instance : ToExpr Rule where
  toExpr rule := mkApp3 (mkConst ``Rule.mk) (toExpr rule.name) (toExpr rule.head) (toExpr rule.body)
  toTypeExpr := mkConst ``Rule
private def cacheRules (raw : TSyntax `term) : TermElabM Expr := do
  let expression ← elabTerm raw (some (toTypeExpr (List Rewrite)))
  let decoded ← unsafe Meta.evalExpr (Option (List ScopedRule)) (toTypeExpr (Option (List ScopedRule)))
    (mkApp (mkConst ``elaborateRewrites?) expression)
  let some rules := decoded | throwErrorAt raw "source rule elaborator refused quotation"
  pure (toExpr rules)
private def cacheRows (raw : TSyntax `term) : TermElabM Expr := do
  let expression ← elabTerm raw (some (toTypeExpr (List Rewrite)))
  let rows ← unsafe Meta.evalExpr (List Rewrite) (toTypeExpr (List Rewrite)) expression
  pure (toExpr rows)
syntax "authored_rows% " term:max : term
elab_rules : term
  | `(authored_rows% $raw:term) => cacheRows raw

syntax "authored_rules% " term:max : term
elab_rules : term
  | `(authored_rules% $raw:term) => cacheRules raw

end

/-- Retained source order of the authored assertion environment target. -/
private def groundCapabilitySyntax : SExpr := metta_sexpr_pinned_file% petta
      "../../../../../../../../../hyperon/cetta-mm0-metta-20261004/experiments/gslt2parse_foundation/presentations/shared/ground_relations_v1.metta"
      sha256 "cf6eae2778f3afc5db8358eba83c7d0e856f7a184bb963af315fe5822db27314"
private def groundProviderSyntax : SExpr := metta_sexpr_pinned_file% petta
      "../../../../../../../../../hyperon/cetta-mm0-metta-20261004/experiments/gslt2parse_foundation/presentations/shared/cetta_petta_ground_relations_v1.metta"
      sha256 "64c59d3cb00ee87e834ab9f0e7d3568c0e3cc6b52c5427618229f5a66d784e5b"
private def sourceFoldSyntax : SExpr := metta_sexpr_pinned_file% petta
      "../../../../../../../../../hyperon/cetta-mm0-metta-20261004/langdef/mm0/source_fold_v1.metta"
      sha256 "e0ebb182137c5b117051bf12b7b2c5247e710397ff1a1522d281d4325256da0c"
private def sortEnvironmentSyntax : SExpr := metta_sexpr_pinned_file% petta
      "../../../../../../../../../hyperon/cetta-mm0-metta-20261004/langdef/mm0/sort_environment_v1.metta"
      sha256 "3d6c33aeaae750f3fe3090048633b3301c8ed5678e72dfe7f6be76209edff4b4"
private def termEnvironmentSyntax : SExpr := metta_sexpr_pinned_file% petta
      "../../../../../../../../../hyperon/cetta-mm0-metta-20261004/langdef/mm0/term_environment_v1.metta"
      sha256 "5c2c3197f8a52fbe1623818dfa9ebb659d01da84d24ad2173762c02cc28f97bf"
private def secondaryLexerSyntax : SExpr := metta_sexpr_pinned_file% petta
      "../../../../../../../../../hyperon/cetta-mm0-metta-20261004/langdef/mm0/secondary_lexer_v1.metta"
      sha256 "a1c24d261cbb1e50e2132047a5d6990327d1c86f8e7373d5f3e5ec4493b6707e"
private def notationEnvironmentSyntax : SExpr := metta_sexpr_pinned_file% petta
      "../../../../../../../../../hyperon/cetta-mm0-metta-20261004/langdef/mm0/notation_environment_v1.metta"
      sha256 "a972ec3cfebb09ee1ad2eda1763841f696ec1f407670ce7329afe3510041fa9a"
private def dynamicPrattSyntax : SExpr := metta_sexpr_pinned_file% petta
      "../../../../../../../../../hyperon/cetta-mm0-metta-20261004/langdef/common/dynamic_pratt_v1.metta"
      sha256 "fa8004f1363009cb2f32b72b647a54a5763084557bc6b86d96ebcb2f88ff8ca1"
private def mathParserSyntax : SExpr := metta_sexpr_pinned_file% petta
      "../../../../../../../../../hyperon/cetta-mm0-metta-20261004/langdef/mm0/math_parser_v1.metta"
      sha256 "bf197e06eea1fae15ed7c7e666704f6ac46d727db464cbf87f537fb1c75fafa4"
private def expressionEnvironmentSyntax : SExpr := metta_sexpr_pinned_file% petta
      "../../../../../../../../../hyperon/cetta-mm0-metta-20261004/langdef/mm0/expression_environment_v1.metta"
      sha256 "2a72b6e18c981dc8c25c4574d9d551db08c7d7ec187e3a4de8f68cf1566ba5bd"
private def assertionEnvironmentSyntax : SExpr := metta_sexpr_pinned_file% petta
      "../../../../../../../../../hyperon/cetta-mm0-metta-20261004/langdef/mm0/assertion_environment_v1.metta"
      sha256 "760a3bd9b3f171ef220139d73872aa626409745d7b4238042d1b2e2068e25fe7"

def sourceSyntax : List SExpr := [groundCapabilitySyntax, groundProviderSyntax,
  sourceFoldSyntax, sortEnvironmentSyntax, termEnvironmentSyntax, secondaryLexerSyntax,
  notationEnvironmentSyntax, dynamicPrattSyntax, mathParserSyntax,
  expressionEnvironmentSyntax, assertionEnvironmentSyntax]

private def groundCapabilitySource : Source := authored_source% groundCapabilitySyntax
theorem groundCapability_encoded : encode groundCapabilitySource = groundCapabilitySyntax := by decide +kernel

private def groundProviderSource : Source := authored_source% groundProviderSyntax
theorem groundProvider_encoded : encode groundProviderSource = groundProviderSyntax := by decide +kernel

private def sourceFoldSource : Source := authored_source% sourceFoldSyntax
theorem sourceFold_encoded : encode sourceFoldSource = sourceFoldSyntax := by decide +kernel

private def sortEnvironmentSource : Source := authored_source% sortEnvironmentSyntax
theorem sortEnvironment_encoded : encode sortEnvironmentSource = sortEnvironmentSyntax := by decide +kernel

private def termEnvironmentSource : Source := authored_source% termEnvironmentSyntax
theorem termEnvironment_encoded : encode termEnvironmentSource = termEnvironmentSyntax := by decide +kernel

private def secondaryLexerSource : Source := authored_source% secondaryLexerSyntax
theorem secondaryLexer_encoded : encode secondaryLexerSource = secondaryLexerSyntax := by decide +kernel

private def notationEnvironmentSource : Source := authored_source% notationEnvironmentSyntax
theorem notationEnvironment_encoded : encode notationEnvironmentSource = notationEnvironmentSyntax := by decide +kernel

private def dynamicPrattSource : Source := authored_source% dynamicPrattSyntax
theorem dynamicPratt_encoded : encode dynamicPrattSource = dynamicPrattSyntax := by decide +kernel

private def mathParserSource : Source := authored_source% mathParserSyntax
theorem mathParser_encoded : encode mathParserSource = mathParserSyntax := by decide +kernel

private def expressionEnvironmentSource : Source := authored_source% expressionEnvironmentSyntax
theorem expressionEnvironment_encoded : encode expressionEnvironmentSource = expressionEnvironmentSyntax := by decide +kernel

private def assertionEnvironmentSource : Source := authored_source% assertionEnvironmentSyntax
theorem assertionEnvironment_encoded : encode assertionEnvironmentSource = assertionEnvironmentSyntax := by decide +kernel

/-- Ordinary source constructors independently compared with every retained row. -/
def sources : List Source := [groundCapabilitySource, groundProviderSource, sourceFoldSource, sortEnvironmentSource, termEnvironmentSource, secondaryLexerSource, notationEnvironmentSource, dynamicPrattSource, mathParserSource, expressionEnvironmentSource, assertionEnvironmentSource]

theorem sources_decoded : decodeList decode sourceSyntax = some sources := by
  unfold sourceSyntax sources
  rw [← groundCapability_encoded, ← groundProvider_encoded, ← sourceFold_encoded, ← sortEnvironment_encoded, ← termEnvironment_encoded, ← secondaryLexer_encoded, ← notationEnvironment_encoded, ← dynamicPratt_encoded, ← mathParser_encoded, ← expressionEnvironment_encoded, ← assertionEnvironment_encoded]
  simpa only [sources, List.map_cons, List.map_nil] using
    Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT.decodeList_map_encode
      decode encode Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT.decode_encode sources



/-! The following complete partition bounds proof reduction. It changes no
source occurrence, signature entry, variable scope, or rule multiplicity. -/

@[local simp] private theorem intToken2 : "2".toInt? = some (2 : Int) := Nat.toInt?_repr 2
@[local simp] private theorem intToken10 : "10".toInt? = some (10 : Int) := Nat.toInt?_repr 10
@[local simp] private theorem intToken32 : "32".toInt? = some (32 : Int) := Nat.toInt?_repr 32
@[local simp] private theorem intToken40 : "40".toInt? = some (40 : Int) := Nat.toInt?_repr 40
@[local simp] private theorem intToken41 : "41".toInt? = some (41 : Int) := Nat.toInt?_repr 41
@[local simp] private theorem intToken48 : "48".toInt? = some (48 : Int) := Nat.toInt?_repr 48
@[local simp] private theorem intToken49 : "49".toInt? = some (49 : Int) := Nat.toInt?_repr 49
@[local simp] private theorem intToken50 : "50".toInt? = some (50 : Int) := Nat.toInt?_repr 50
@[local simp] private theorem intToken51 : "51".toInt? = some (51 : Int) := Nat.toInt?_repr 51
@[local simp] private theorem intToken52 : "52".toInt? = some (52 : Int) := Nat.toInt?_repr 52
@[local simp] private theorem intToken53 : "53".toInt? = some (53 : Int) := Nat.toInt?_repr 53
@[local simp] private theorem intToken54 : "54".toInt? = some (54 : Int) := Nat.toInt?_repr 54
@[local simp] private theorem intToken55 : "55".toInt? = some (55 : Int) := Nat.toInt?_repr 55
@[local simp] private theorem intToken56 : "56".toInt? = some (56 : Int) := Nat.toInt?_repr 56
@[local simp] private theorem intToken57 : "57".toInt? = some (57 : Int) := Nat.toInt?_repr 57
@[local simp] private theorem intToken97 : "97".toInt? = some (97 : Int) := Nat.toInt?_repr 97
@[local simp] private theorem intToken109 : "109".toInt? = some (109 : Int) := Nat.toInt?_repr 109
@[local simp] private theorem intToken120 : "120".toInt? = some (120 : Int) := Nat.toInt?_repr 120

private theorem nodup_append_of_fresh (left right : List String)
    (leftUnique : left.Nodup) (rightUnique : right.Nodup)
    (fresh : right.all (fun name => !left.contains name) = true) :
    (left ++ right).Nodup := by
  apply List.nodup_append.mpr ⟨leftUnique, rightUnique, ?_⟩
  intro previous previousMember current currentMember same
  have missing := List.all_eq_true.mp fresh current currentMember
  have absent : current ∉ left := by simpa using missing
  exact absent (same ▸ previousMember)

private theorem source_reference_validity (sourceList : List Source) (operators : List Operator)
    (emptyEquations : sourceList.all (fun source => source.equations.isEmpty) = true)
    (supported : (compositionRewrites sourceList).all (fun row =>
      termSupported operators row.head && termsSupported operators row.body) = true) :
    sourceList.all (Source.termsValidIn operators) = true := by
  simp only [compositionRewrites, List.all_flatMap] at supported
  apply List.all_eq_true.mpr
  intro source member
  have equationsEmpty := List.nil_of_isEmpty (List.all_eq_true.mp emptyEquations source member)
  simpa only [Source.termsValidIn, equationsEmpty, List.all_nil, Bool.true_and] using
    List.all_eq_true.mp supported source member

private theorem elaborateRewrites_append (left right : List Rewrite) :
    elaborateRewrites? (left ++ right) = (do
      let first ← elaborateRewrites? left
      let second ← elaborateRewrites? right
      some (first ++ second)) := by
  simp only [elaborateRewrites?, List.mapM_append]
  rfl

private def namesPrefix (count : Nat) : List String :=
  ((compositionRewrites sources).take count).map Rewrite.name

private theorem namesPrefix0_unique : (namesPrefix 0).Nodup := by decide +kernel

private def rows0 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 0).take 10)
private theorem rows0_captured : ((compositionRewrites sources).drop 0).take 10 = rows0 := rfl
private def named0 : List ScopedRule := authored_rules% rows0
private theorem rows0_references : rows0.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows0_unique : (rows0.map Rewrite.name).Nodup := by decide +kernel
private theorem rows0_fresh : (rows0.map Rewrite.name).all
    (fun name => !(namesPrefix 0).contains name) = true := by decide +kernel
private theorem namesPrefix10_partition : namesPrefix 0 ++ rows0.map Rewrite.name = namesPrefix 10 := rfl
private theorem namesPrefix10_unique : (namesPrefix 10).Nodup := by
  rw [← namesPrefix10_partition]
  exact nodup_append_of_fresh _ _ namesPrefix0_unique rows0_unique rows0_fresh
private theorem named0_elaborated : elaborateRewrites? rows0 = some named0 := by
  simp [rows0, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows1 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 10).take 10)
private theorem rows1_captured : ((compositionRewrites sources).drop 10).take 10 = rows1 := rfl
private def named1 : List ScopedRule := authored_rules% rows1
private theorem rows1_references : rows1.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows1_unique : (rows1.map Rewrite.name).Nodup := by decide +kernel
private theorem rows1_fresh : (rows1.map Rewrite.name).all
    (fun name => !(namesPrefix 10).contains name) = true := by decide +kernel
private theorem namesPrefix20_partition : namesPrefix 10 ++ rows1.map Rewrite.name = namesPrefix 20 := rfl
private theorem namesPrefix20_unique : (namesPrefix 20).Nodup := by
  rw [← namesPrefix20_partition]
  exact nodup_append_of_fresh _ _ namesPrefix10_unique rows1_unique rows1_fresh
private theorem named1_elaborated : elaborateRewrites? rows1 = some named1 := by
  simp [rows1, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows2 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 20).take 10)
private theorem rows2_captured : ((compositionRewrites sources).drop 20).take 10 = rows2 := rfl
private def named2 : List ScopedRule := authored_rules% rows2
private theorem rows2_references : rows2.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows2_unique : (rows2.map Rewrite.name).Nodup := by decide +kernel
private theorem rows2_fresh : (rows2.map Rewrite.name).all
    (fun name => !(namesPrefix 20).contains name) = true := by decide +kernel
private theorem namesPrefix30_partition : namesPrefix 20 ++ rows2.map Rewrite.name = namesPrefix 30 := rfl
private theorem namesPrefix30_unique : (namesPrefix 30).Nodup := by
  rw [← namesPrefix30_partition]
  exact nodup_append_of_fresh _ _ namesPrefix20_unique rows2_unique rows2_fresh
private theorem named2_elaborated : elaborateRewrites? rows2 = some named2 := by
  simp [rows2, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows3 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 30).take 10)
private theorem rows3_captured : ((compositionRewrites sources).drop 30).take 10 = rows3 := rfl
private def named3 : List ScopedRule := authored_rules% rows3
private theorem rows3_references : rows3.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows3_unique : (rows3.map Rewrite.name).Nodup := by decide +kernel
private theorem rows3_fresh : (rows3.map Rewrite.name).all
    (fun name => !(namesPrefix 30).contains name) = true := by decide +kernel
private theorem namesPrefix40_partition : namesPrefix 30 ++ rows3.map Rewrite.name = namesPrefix 40 := rfl
private theorem namesPrefix40_unique : (namesPrefix 40).Nodup := by
  rw [← namesPrefix40_partition]
  exact nodup_append_of_fresh _ _ namesPrefix30_unique rows3_unique rows3_fresh
private theorem named3_elaborated : elaborateRewrites? rows3 = some named3 := by
  simp [rows3, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows4 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 40).take 10)
private theorem rows4_captured : ((compositionRewrites sources).drop 40).take 10 = rows4 := rfl
private def named4 : List ScopedRule := authored_rules% rows4
private theorem rows4_references : rows4.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows4_unique : (rows4.map Rewrite.name).Nodup := by decide +kernel
private theorem rows4_fresh : (rows4.map Rewrite.name).all
    (fun name => !(namesPrefix 40).contains name) = true := by decide +kernel
private theorem namesPrefix50_partition : namesPrefix 40 ++ rows4.map Rewrite.name = namesPrefix 50 := rfl
private theorem namesPrefix50_unique : (namesPrefix 50).Nodup := by
  rw [← namesPrefix50_partition]
  exact nodup_append_of_fresh _ _ namesPrefix40_unique rows4_unique rows4_fresh
private theorem named4_elaborated : elaborateRewrites? rows4 = some named4 := by
  simp [rows4, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows5 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 50).take 10)
private theorem rows5_captured : ((compositionRewrites sources).drop 50).take 10 = rows5 := rfl
private def named5 : List ScopedRule := authored_rules% rows5
private theorem rows5_references : rows5.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows5_unique : (rows5.map Rewrite.name).Nodup := by decide +kernel
private theorem rows5_fresh : (rows5.map Rewrite.name).all
    (fun name => !(namesPrefix 50).contains name) = true := by decide +kernel
private theorem namesPrefix60_partition : namesPrefix 50 ++ rows5.map Rewrite.name = namesPrefix 60 := rfl
private theorem namesPrefix60_unique : (namesPrefix 60).Nodup := by
  rw [← namesPrefix60_partition]
  exact nodup_append_of_fresh _ _ namesPrefix50_unique rows5_unique rows5_fresh
private theorem named5_elaborated : elaborateRewrites? rows5 = some named5 := by
  simp [rows5, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows6 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 60).take 10)
private theorem rows6_captured : ((compositionRewrites sources).drop 60).take 10 = rows6 := rfl
private def named6 : List ScopedRule := authored_rules% rows6
private theorem rows6_references : rows6.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows6_unique : (rows6.map Rewrite.name).Nodup := by decide +kernel
private theorem rows6_fresh : (rows6.map Rewrite.name).all
    (fun name => !(namesPrefix 60).contains name) = true := by decide +kernel
private theorem namesPrefix70_partition : namesPrefix 60 ++ rows6.map Rewrite.name = namesPrefix 70 := rfl
private theorem namesPrefix70_unique : (namesPrefix 70).Nodup := by
  rw [← namesPrefix70_partition]
  exact nodup_append_of_fresh _ _ namesPrefix60_unique rows6_unique rows6_fresh
private theorem named6_elaborated : elaborateRewrites? rows6 = some named6 := by
  simp [rows6, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows7 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 70).take 10)
private theorem rows7_captured : ((compositionRewrites sources).drop 70).take 10 = rows7 := rfl
private def named7 : List ScopedRule := authored_rules% rows7
private theorem rows7_references : rows7.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows7_unique : (rows7.map Rewrite.name).Nodup := by decide +kernel
private theorem rows7_fresh : (rows7.map Rewrite.name).all
    (fun name => !(namesPrefix 70).contains name) = true := by decide +kernel
private theorem namesPrefix80_partition : namesPrefix 70 ++ rows7.map Rewrite.name = namesPrefix 80 := rfl
private theorem namesPrefix80_unique : (namesPrefix 80).Nodup := by
  rw [← namesPrefix80_partition]
  exact nodup_append_of_fresh _ _ namesPrefix70_unique rows7_unique rows7_fresh
private theorem named7_elaborated : elaborateRewrites? rows7 = some named7 := by
  simp [rows7, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows8 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 80).take 10)
private theorem rows8_captured : ((compositionRewrites sources).drop 80).take 10 = rows8 := rfl
private def named8 : List ScopedRule := authored_rules% rows8
private theorem rows8_references : rows8.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows8_unique : (rows8.map Rewrite.name).Nodup := by decide +kernel
private theorem rows8_fresh : (rows8.map Rewrite.name).all
    (fun name => !(namesPrefix 80).contains name) = true := by decide +kernel
private theorem namesPrefix90_partition : namesPrefix 80 ++ rows8.map Rewrite.name = namesPrefix 90 := rfl
private theorem namesPrefix90_unique : (namesPrefix 90).Nodup := by
  rw [← namesPrefix90_partition]
  exact nodup_append_of_fresh _ _ namesPrefix80_unique rows8_unique rows8_fresh
private theorem named8_elaborated : elaborateRewrites? rows8 = some named8 := by
  simp [rows8, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows9 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 90).take 10)
private theorem rows9_captured : ((compositionRewrites sources).drop 90).take 10 = rows9 := rfl
private def named9 : List ScopedRule := authored_rules% rows9
private theorem rows9_references : rows9.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows9_unique : (rows9.map Rewrite.name).Nodup := by decide +kernel
private theorem rows9_fresh : (rows9.map Rewrite.name).all
    (fun name => !(namesPrefix 90).contains name) = true := by decide +kernel
private theorem namesPrefix100_partition : namesPrefix 90 ++ rows9.map Rewrite.name = namesPrefix 100 := rfl
private theorem namesPrefix100_unique : (namesPrefix 100).Nodup := by
  rw [← namesPrefix100_partition]
  exact nodup_append_of_fresh _ _ namesPrefix90_unique rows9_unique rows9_fresh
private theorem named9_elaborated : elaborateRewrites? rows9 = some named9 := by
  simp [rows9, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows10 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 100).take 10)
private theorem rows10_captured : ((compositionRewrites sources).drop 100).take 10 = rows10 := rfl
private def named10 : List ScopedRule := authored_rules% rows10
private theorem rows10_references : rows10.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows10_unique : (rows10.map Rewrite.name).Nodup := by decide +kernel
private theorem rows10_fresh : (rows10.map Rewrite.name).all
    (fun name => !(namesPrefix 100).contains name) = true := by decide +kernel
private theorem namesPrefix110_partition : namesPrefix 100 ++ rows10.map Rewrite.name = namesPrefix 110 := rfl
private theorem namesPrefix110_unique : (namesPrefix 110).Nodup := by
  rw [← namesPrefix110_partition]
  exact nodup_append_of_fresh _ _ namesPrefix100_unique rows10_unique rows10_fresh
private theorem named10_elaborated : elaborateRewrites? rows10 = some named10 := by
  simp [rows10, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows11 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 110).take 10)
private theorem rows11_captured : ((compositionRewrites sources).drop 110).take 10 = rows11 := rfl
private def named11 : List ScopedRule := authored_rules% rows11
private theorem rows11_references : rows11.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows11_unique : (rows11.map Rewrite.name).Nodup := by decide +kernel
private theorem rows11_fresh : (rows11.map Rewrite.name).all
    (fun name => !(namesPrefix 110).contains name) = true := by decide +kernel
private theorem namesPrefix120_partition : namesPrefix 110 ++ rows11.map Rewrite.name = namesPrefix 120 := rfl
private theorem namesPrefix120_unique : (namesPrefix 120).Nodup := by
  rw [← namesPrefix120_partition]
  exact nodup_append_of_fresh _ _ namesPrefix110_unique rows11_unique rows11_fresh
private theorem named11_elaborated : elaborateRewrites? rows11 = some named11 := by
  simp [rows11, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows12 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 120).take 10)
private theorem rows12_captured : ((compositionRewrites sources).drop 120).take 10 = rows12 := rfl
private def named12 : List ScopedRule := authored_rules% rows12
private theorem rows12_references : rows12.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows12_unique : (rows12.map Rewrite.name).Nodup := by decide +kernel
private theorem rows12_fresh : (rows12.map Rewrite.name).all
    (fun name => !(namesPrefix 120).contains name) = true := by decide +kernel
private theorem namesPrefix130_partition : namesPrefix 120 ++ rows12.map Rewrite.name = namesPrefix 130 := rfl
private theorem namesPrefix130_unique : (namesPrefix 130).Nodup := by
  rw [← namesPrefix130_partition]
  exact nodup_append_of_fresh _ _ namesPrefix120_unique rows12_unique rows12_fresh
private theorem named12_elaborated : elaborateRewrites? rows12 = some named12 := by
  simp [rows12, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows13 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 130).take 10)
private theorem rows13_captured : ((compositionRewrites sources).drop 130).take 10 = rows13 := rfl
private def named13 : List ScopedRule := authored_rules% rows13
private theorem rows13_references : rows13.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows13_unique : (rows13.map Rewrite.name).Nodup := by decide +kernel
private theorem rows13_fresh : (rows13.map Rewrite.name).all
    (fun name => !(namesPrefix 130).contains name) = true := by decide +kernel
private theorem namesPrefix140_partition : namesPrefix 130 ++ rows13.map Rewrite.name = namesPrefix 140 := rfl
private theorem namesPrefix140_unique : (namesPrefix 140).Nodup := by
  rw [← namesPrefix140_partition]
  exact nodup_append_of_fresh _ _ namesPrefix130_unique rows13_unique rows13_fresh
private theorem named13_elaborated : elaborateRewrites? rows13 = some named13 := by
  simp [rows13, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows14 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 140).take 10)
private theorem rows14_captured : ((compositionRewrites sources).drop 140).take 10 = rows14 := rfl
private def named14 : List ScopedRule := authored_rules% rows14
private theorem rows14_references : rows14.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows14_unique : (rows14.map Rewrite.name).Nodup := by decide +kernel
private theorem rows14_fresh : (rows14.map Rewrite.name).all
    (fun name => !(namesPrefix 140).contains name) = true := by decide +kernel
private theorem namesPrefix150_partition : namesPrefix 140 ++ rows14.map Rewrite.name = namesPrefix 150 := rfl
private theorem namesPrefix150_unique : (namesPrefix 150).Nodup := by
  rw [← namesPrefix150_partition]
  exact nodup_append_of_fresh _ _ namesPrefix140_unique rows14_unique rows14_fresh
private theorem named14_elaborated : elaborateRewrites? rows14 = some named14 := by
  simp [rows14, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows15 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 150).take 10)
private theorem rows15_captured : ((compositionRewrites sources).drop 150).take 10 = rows15 := rfl
private def named15 : List ScopedRule := authored_rules% rows15
private theorem rows15_references : rows15.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows15_unique : (rows15.map Rewrite.name).Nodup := by decide +kernel
private theorem rows15_fresh : (rows15.map Rewrite.name).all
    (fun name => !(namesPrefix 150).contains name) = true := by decide +kernel
private theorem namesPrefix160_partition : namesPrefix 150 ++ rows15.map Rewrite.name = namesPrefix 160 := rfl
private theorem namesPrefix160_unique : (namesPrefix 160).Nodup := by
  rw [← namesPrefix160_partition]
  exact nodup_append_of_fresh _ _ namesPrefix150_unique rows15_unique rows15_fresh
private theorem named15_elaborated : elaborateRewrites? rows15 = some named15 := by
  simp [rows15, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows16 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 160).take 10)
private theorem rows16_captured : ((compositionRewrites sources).drop 160).take 10 = rows16 := rfl
private def named16 : List ScopedRule := authored_rules% rows16
private theorem rows16_references : rows16.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows16_unique : (rows16.map Rewrite.name).Nodup := by decide +kernel
private theorem rows16_fresh : (rows16.map Rewrite.name).all
    (fun name => !(namesPrefix 160).contains name) = true := by decide +kernel
private theorem namesPrefix170_partition : namesPrefix 160 ++ rows16.map Rewrite.name = namesPrefix 170 := rfl
private theorem namesPrefix170_unique : (namesPrefix 170).Nodup := by
  rw [← namesPrefix170_partition]
  exact nodup_append_of_fresh _ _ namesPrefix160_unique rows16_unique rows16_fresh
private theorem named16_elaborated : elaborateRewrites? rows16 = some named16 := by
  simp [rows16, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows17 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 170).take 10)
private theorem rows17_captured : ((compositionRewrites sources).drop 170).take 10 = rows17 := rfl
private def named17 : List ScopedRule := authored_rules% rows17
private theorem rows17_references : rows17.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows17_unique : (rows17.map Rewrite.name).Nodup := by decide +kernel
private theorem rows17_fresh : (rows17.map Rewrite.name).all
    (fun name => !(namesPrefix 170).contains name) = true := by decide +kernel
private theorem namesPrefix180_partition : namesPrefix 170 ++ rows17.map Rewrite.name = namesPrefix 180 := rfl
private theorem namesPrefix180_unique : (namesPrefix 180).Nodup := by
  rw [← namesPrefix180_partition]
  exact nodup_append_of_fresh _ _ namesPrefix170_unique rows17_unique rows17_fresh
private theorem named17_elaborated : elaborateRewrites? rows17 = some named17 := by
  simp [rows17, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows18 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 180).take 10)
private theorem rows18_captured : ((compositionRewrites sources).drop 180).take 10 = rows18 := rfl
private def named18 : List ScopedRule := authored_rules% rows18
private theorem rows18_references : rows18.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows18_unique : (rows18.map Rewrite.name).Nodup := by decide +kernel
private theorem rows18_fresh : (rows18.map Rewrite.name).all
    (fun name => !(namesPrefix 180).contains name) = true := by decide +kernel
private theorem namesPrefix190_partition : namesPrefix 180 ++ rows18.map Rewrite.name = namesPrefix 190 := rfl
private theorem namesPrefix190_unique : (namesPrefix 190).Nodup := by
  rw [← namesPrefix190_partition]
  exact nodup_append_of_fresh _ _ namesPrefix180_unique rows18_unique rows18_fresh
private theorem named18_elaborated : elaborateRewrites? rows18 = some named18 := by
  simp [rows18, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows19 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 190).take 10)
private theorem rows19_captured : ((compositionRewrites sources).drop 190).take 10 = rows19 := rfl
private def named19 : List ScopedRule := authored_rules% rows19
private theorem rows19_references : rows19.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows19_unique : (rows19.map Rewrite.name).Nodup := by decide +kernel
private theorem rows19_fresh : (rows19.map Rewrite.name).all
    (fun name => !(namesPrefix 190).contains name) = true := by decide +kernel
private theorem namesPrefix200_partition : namesPrefix 190 ++ rows19.map Rewrite.name = namesPrefix 200 := rfl
private theorem namesPrefix200_unique : (namesPrefix 200).Nodup := by
  rw [← namesPrefix200_partition]
  exact nodup_append_of_fresh _ _ namesPrefix190_unique rows19_unique rows19_fresh
private theorem named19_elaborated : elaborateRewrites? rows19 = some named19 := by
  simp [rows19, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows20 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 200).take 10)
private theorem rows20_captured : ((compositionRewrites sources).drop 200).take 10 = rows20 := rfl
private def named20 : List ScopedRule := authored_rules% rows20
private theorem rows20_references : rows20.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows20_unique : (rows20.map Rewrite.name).Nodup := by decide +kernel
private theorem rows20_fresh : (rows20.map Rewrite.name).all
    (fun name => !(namesPrefix 200).contains name) = true := by decide +kernel
private theorem namesPrefix210_partition : namesPrefix 200 ++ rows20.map Rewrite.name = namesPrefix 210 := rfl
private theorem namesPrefix210_unique : (namesPrefix 210).Nodup := by
  rw [← namesPrefix210_partition]
  exact nodup_append_of_fresh _ _ namesPrefix200_unique rows20_unique rows20_fresh
private theorem named20_elaborated : elaborateRewrites? rows20 = some named20 := by
  simp [rows20, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows21 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 210).take 10)
private theorem rows21_captured : ((compositionRewrites sources).drop 210).take 10 = rows21 := rfl
private def named21 : List ScopedRule := authored_rules% rows21
private theorem rows21_references : rows21.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows21_unique : (rows21.map Rewrite.name).Nodup := by decide +kernel
private theorem rows21_fresh : (rows21.map Rewrite.name).all
    (fun name => !(namesPrefix 210).contains name) = true := by decide +kernel
private theorem namesPrefix220_partition : namesPrefix 210 ++ rows21.map Rewrite.name = namesPrefix 220 := rfl
private theorem namesPrefix220_unique : (namesPrefix 220).Nodup := by
  rw [← namesPrefix220_partition]
  exact nodup_append_of_fresh _ _ namesPrefix210_unique rows21_unique rows21_fresh
private theorem named21_elaborated : elaborateRewrites? rows21 = some named21 := by
  simp [rows21, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows22 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 220).take 10)
private theorem rows22_captured : ((compositionRewrites sources).drop 220).take 10 = rows22 := rfl
private def named22 : List ScopedRule := authored_rules% rows22
private theorem rows22_references : rows22.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows22_unique : (rows22.map Rewrite.name).Nodup := by decide +kernel
private theorem rows22_fresh : (rows22.map Rewrite.name).all
    (fun name => !(namesPrefix 220).contains name) = true := by decide +kernel
private theorem namesPrefix230_partition : namesPrefix 220 ++ rows22.map Rewrite.name = namesPrefix 230 := rfl
private theorem namesPrefix230_unique : (namesPrefix 230).Nodup := by
  rw [← namesPrefix230_partition]
  exact nodup_append_of_fresh _ _ namesPrefix220_unique rows22_unique rows22_fresh
private theorem named22_elaborated : elaborateRewrites? rows22 = some named22 := by
  simp [rows22, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows23 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 230).take 10)
private theorem rows23_captured : ((compositionRewrites sources).drop 230).take 10 = rows23 := rfl
private def named23 : List ScopedRule := authored_rules% rows23
private theorem rows23_references : rows23.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows23_unique : (rows23.map Rewrite.name).Nodup := by decide +kernel
private theorem rows23_fresh : (rows23.map Rewrite.name).all
    (fun name => !(namesPrefix 230).contains name) = true := by decide +kernel
private theorem namesPrefix240_partition : namesPrefix 230 ++ rows23.map Rewrite.name = namesPrefix 240 := rfl
private theorem namesPrefix240_unique : (namesPrefix 240).Nodup := by
  rw [← namesPrefix240_partition]
  exact nodup_append_of_fresh _ _ namesPrefix230_unique rows23_unique rows23_fresh
private theorem named23_elaborated : elaborateRewrites? rows23 = some named23 := by
  simp [rows23, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows24 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 240).take 10)
private theorem rows24_captured : ((compositionRewrites sources).drop 240).take 10 = rows24 := rfl
private def named24 : List ScopedRule := authored_rules% rows24
private theorem rows24_references : rows24.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows24_unique : (rows24.map Rewrite.name).Nodup := by decide +kernel
private theorem rows24_fresh : (rows24.map Rewrite.name).all
    (fun name => !(namesPrefix 240).contains name) = true := by decide +kernel
private theorem namesPrefix250_partition : namesPrefix 240 ++ rows24.map Rewrite.name = namesPrefix 250 := rfl
private theorem namesPrefix250_unique : (namesPrefix 250).Nodup := by
  rw [← namesPrefix250_partition]
  exact nodup_append_of_fresh _ _ namesPrefix240_unique rows24_unique rows24_fresh
private theorem named24_elaborated : elaborateRewrites? rows24 = some named24 := by
  simp [rows24, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows25 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 250).take 10)
private theorem rows25_captured : ((compositionRewrites sources).drop 250).take 10 = rows25 := rfl
private def named25 : List ScopedRule := authored_rules% rows25
private theorem rows25_references : rows25.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows25_unique : (rows25.map Rewrite.name).Nodup := by decide +kernel
private theorem rows25_fresh : (rows25.map Rewrite.name).all
    (fun name => !(namesPrefix 250).contains name) = true := by decide +kernel
private theorem namesPrefix260_partition : namesPrefix 250 ++ rows25.map Rewrite.name = namesPrefix 260 := rfl
private theorem namesPrefix260_unique : (namesPrefix 260).Nodup := by
  rw [← namesPrefix260_partition]
  exact nodup_append_of_fresh _ _ namesPrefix250_unique rows25_unique rows25_fresh
private theorem named25_elaborated : elaborateRewrites? rows25 = some named25 := by
  simp [rows25, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows26 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 260).take 10)
private theorem rows26_captured : ((compositionRewrites sources).drop 260).take 10 = rows26 := rfl
private def named26 : List ScopedRule := authored_rules% rows26
private theorem rows26_references : rows26.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows26_unique : (rows26.map Rewrite.name).Nodup := by decide +kernel
private theorem rows26_fresh : (rows26.map Rewrite.name).all
    (fun name => !(namesPrefix 260).contains name) = true := by decide +kernel
private theorem namesPrefix270_partition : namesPrefix 260 ++ rows26.map Rewrite.name = namesPrefix 270 := rfl
private theorem namesPrefix270_unique : (namesPrefix 270).Nodup := by
  rw [← namesPrefix270_partition]
  exact nodup_append_of_fresh _ _ namesPrefix260_unique rows26_unique rows26_fresh
private theorem named26_elaborated : elaborateRewrites? rows26 = some named26 := by
  simp [rows26, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows27 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 270).take 10)
private theorem rows27_captured : ((compositionRewrites sources).drop 270).take 10 = rows27 := rfl
private def named27 : List ScopedRule := authored_rules% rows27
private theorem rows27_references : rows27.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows27_unique : (rows27.map Rewrite.name).Nodup := by decide +kernel
private theorem rows27_fresh : (rows27.map Rewrite.name).all
    (fun name => !(namesPrefix 270).contains name) = true := by decide +kernel
private theorem namesPrefix280_partition : namesPrefix 270 ++ rows27.map Rewrite.name = namesPrefix 280 := rfl
private theorem namesPrefix280_unique : (namesPrefix 280).Nodup := by
  rw [← namesPrefix280_partition]
  exact nodup_append_of_fresh _ _ namesPrefix270_unique rows27_unique rows27_fresh
private theorem named27_elaborated : elaborateRewrites? rows27 = some named27 := by
  simp [rows27, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows28 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 280).take 10)
private theorem rows28_captured : ((compositionRewrites sources).drop 280).take 10 = rows28 := rfl
private def named28 : List ScopedRule := authored_rules% rows28
private theorem rows28_references : rows28.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows28_unique : (rows28.map Rewrite.name).Nodup := by decide +kernel
private theorem rows28_fresh : (rows28.map Rewrite.name).all
    (fun name => !(namesPrefix 280).contains name) = true := by decide +kernel
private theorem namesPrefix290_partition : namesPrefix 280 ++ rows28.map Rewrite.name = namesPrefix 290 := rfl
private theorem namesPrefix290_unique : (namesPrefix 290).Nodup := by
  rw [← namesPrefix290_partition]
  exact nodup_append_of_fresh _ _ namesPrefix280_unique rows28_unique rows28_fresh
private theorem named28_elaborated : elaborateRewrites? rows28 = some named28 := by
  simp [rows28, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows29 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 290).take 10)
private theorem rows29_captured : ((compositionRewrites sources).drop 290).take 10 = rows29 := rfl
private def named29 : List ScopedRule := authored_rules% rows29
private theorem rows29_references : rows29.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows29_unique : (rows29.map Rewrite.name).Nodup := by decide +kernel
private theorem rows29_fresh : (rows29.map Rewrite.name).all
    (fun name => !(namesPrefix 290).contains name) = true := by decide +kernel
private theorem namesPrefix300_partition : namesPrefix 290 ++ rows29.map Rewrite.name = namesPrefix 300 := rfl
private theorem namesPrefix300_unique : (namesPrefix 300).Nodup := by
  rw [← namesPrefix300_partition]
  exact nodup_append_of_fresh _ _ namesPrefix290_unique rows29_unique rows29_fresh
private theorem named29_elaborated : elaborateRewrites? rows29 = some named29 := by
  simp [rows29, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows30 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 300).take 10)
private theorem rows30_captured : ((compositionRewrites sources).drop 300).take 10 = rows30 := rfl
private def named30 : List ScopedRule := authored_rules% rows30
private theorem rows30_references : rows30.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows30_unique : (rows30.map Rewrite.name).Nodup := by decide +kernel
private theorem rows30_fresh : (rows30.map Rewrite.name).all
    (fun name => !(namesPrefix 300).contains name) = true := by decide +kernel
private theorem namesPrefix310_partition : namesPrefix 300 ++ rows30.map Rewrite.name = namesPrefix 310 := rfl
private theorem namesPrefix310_unique : (namesPrefix 310).Nodup := by
  rw [← namesPrefix310_partition]
  exact nodup_append_of_fresh _ _ namesPrefix300_unique rows30_unique rows30_fresh
private theorem named30_elaborated : elaborateRewrites? rows30 = some named30 := by
  simp [rows30, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows31 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 310).take 10)
private theorem rows31_captured : ((compositionRewrites sources).drop 310).take 10 = rows31 := rfl
private def named31 : List ScopedRule := authored_rules% rows31
private theorem rows31_references : rows31.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows31_unique : (rows31.map Rewrite.name).Nodup := by decide +kernel
private theorem rows31_fresh : (rows31.map Rewrite.name).all
    (fun name => !(namesPrefix 310).contains name) = true := by decide +kernel
private theorem namesPrefix320_partition : namesPrefix 310 ++ rows31.map Rewrite.name = namesPrefix 320 := rfl
private theorem namesPrefix320_unique : (namesPrefix 320).Nodup := by
  rw [← namesPrefix320_partition]
  exact nodup_append_of_fresh _ _ namesPrefix310_unique rows31_unique rows31_fresh
private theorem named31_elaborated : elaborateRewrites? rows31 = some named31 := by
  simp [rows31, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows32 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 320).take 10)
private theorem rows32_captured : ((compositionRewrites sources).drop 320).take 10 = rows32 := rfl
private def named32 : List ScopedRule := authored_rules% rows32
private theorem rows32_references : rows32.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows32_unique : (rows32.map Rewrite.name).Nodup := by decide +kernel
private theorem rows32_fresh : (rows32.map Rewrite.name).all
    (fun name => !(namesPrefix 320).contains name) = true := by decide +kernel
private theorem namesPrefix330_partition : namesPrefix 320 ++ rows32.map Rewrite.name = namesPrefix 330 := rfl
private theorem namesPrefix330_unique : (namesPrefix 330).Nodup := by
  rw [← namesPrefix330_partition]
  exact nodup_append_of_fresh _ _ namesPrefix320_unique rows32_unique rows32_fresh
private theorem named32_elaborated : elaborateRewrites? rows32 = some named32 := by
  simp [rows32, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows33 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 330).take 10)
private theorem rows33_captured : ((compositionRewrites sources).drop 330).take 10 = rows33 := rfl
private def named33 : List ScopedRule := authored_rules% rows33
private theorem rows33_references : rows33.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows33_unique : (rows33.map Rewrite.name).Nodup := by decide +kernel
private theorem rows33_fresh : (rows33.map Rewrite.name).all
    (fun name => !(namesPrefix 330).contains name) = true := by decide +kernel
private theorem namesPrefix340_partition : namesPrefix 330 ++ rows33.map Rewrite.name = namesPrefix 340 := rfl
private theorem namesPrefix340_unique : (namesPrefix 340).Nodup := by
  rw [← namesPrefix340_partition]
  exact nodup_append_of_fresh _ _ namesPrefix330_unique rows33_unique rows33_fresh
private theorem named33_elaborated : elaborateRewrites? rows33 = some named33 := by
  simp [rows33, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows34 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 340).take 10)
private theorem rows34_captured : ((compositionRewrites sources).drop 340).take 10 = rows34 := rfl
private def named34 : List ScopedRule := authored_rules% rows34
private theorem rows34_references : rows34.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows34_unique : (rows34.map Rewrite.name).Nodup := by decide +kernel
private theorem rows34_fresh : (rows34.map Rewrite.name).all
    (fun name => !(namesPrefix 340).contains name) = true := by decide +kernel
private theorem namesPrefix350_partition : namesPrefix 340 ++ rows34.map Rewrite.name = namesPrefix 350 := rfl
private theorem namesPrefix350_unique : (namesPrefix 350).Nodup := by
  rw [← namesPrefix350_partition]
  exact nodup_append_of_fresh _ _ namesPrefix340_unique rows34_unique rows34_fresh
private theorem named34_elaborated : elaborateRewrites? rows34 = some named34 := by
  simp [rows34, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows35 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 350).take 10)
private theorem rows35_captured : ((compositionRewrites sources).drop 350).take 10 = rows35 := rfl
private def named35 : List ScopedRule := authored_rules% rows35
private theorem rows35_references : rows35.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows35_unique : (rows35.map Rewrite.name).Nodup := by decide +kernel
private theorem rows35_fresh : (rows35.map Rewrite.name).all
    (fun name => !(namesPrefix 350).contains name) = true := by decide +kernel
private theorem namesPrefix360_partition : namesPrefix 350 ++ rows35.map Rewrite.name = namesPrefix 360 := rfl
private theorem namesPrefix360_unique : (namesPrefix 360).Nodup := by
  rw [← namesPrefix360_partition]
  exact nodup_append_of_fresh _ _ namesPrefix350_unique rows35_unique rows35_fresh
private theorem named35_elaborated : elaborateRewrites? rows35 = some named35 := by
  simp [rows35, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows36 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 360).take 10)
private theorem rows36_captured : ((compositionRewrites sources).drop 360).take 10 = rows36 := rfl
private def named36 : List ScopedRule := authored_rules% rows36
private theorem rows36_references : rows36.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows36_unique : (rows36.map Rewrite.name).Nodup := by decide +kernel
private theorem rows36_fresh : (rows36.map Rewrite.name).all
    (fun name => !(namesPrefix 360).contains name) = true := by decide +kernel
private theorem namesPrefix370_partition : namesPrefix 360 ++ rows36.map Rewrite.name = namesPrefix 370 := rfl
private theorem namesPrefix370_unique : (namesPrefix 370).Nodup := by
  rw [← namesPrefix370_partition]
  exact nodup_append_of_fresh _ _ namesPrefix360_unique rows36_unique rows36_fresh
private theorem named36_elaborated : elaborateRewrites? rows36 = some named36 := by
  simp [rows36, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows37 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 370).take 10)
private theorem rows37_captured : ((compositionRewrites sources).drop 370).take 10 = rows37 := rfl
private def named37 : List ScopedRule := authored_rules% rows37
private theorem rows37_references : rows37.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows37_unique : (rows37.map Rewrite.name).Nodup := by decide +kernel
private theorem rows37_fresh : (rows37.map Rewrite.name).all
    (fun name => !(namesPrefix 370).contains name) = true := by decide +kernel
private theorem namesPrefix380_partition : namesPrefix 370 ++ rows37.map Rewrite.name = namesPrefix 380 := rfl
private theorem namesPrefix380_unique : (namesPrefix 380).Nodup := by
  rw [← namesPrefix380_partition]
  exact nodup_append_of_fresh _ _ namesPrefix370_unique rows37_unique rows37_fresh
private theorem named37_elaborated : elaborateRewrites? rows37 = some named37 := by
  simp [rows37, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows38 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 380).take 10)
private theorem rows38_captured : ((compositionRewrites sources).drop 380).take 10 = rows38 := rfl
private def named38 : List ScopedRule := authored_rules% rows38
private theorem rows38_references : rows38.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows38_unique : (rows38.map Rewrite.name).Nodup := by decide +kernel
private theorem rows38_fresh : (rows38.map Rewrite.name).all
    (fun name => !(namesPrefix 380).contains name) = true := by decide +kernel
private theorem namesPrefix390_partition : namesPrefix 380 ++ rows38.map Rewrite.name = namesPrefix 390 := rfl
private theorem namesPrefix390_unique : (namesPrefix 390).Nodup := by
  rw [← namesPrefix390_partition]
  exact nodup_append_of_fresh _ _ namesPrefix380_unique rows38_unique rows38_fresh
private theorem named38_elaborated : elaborateRewrites? rows38 = some named38 := by
  simp [rows38, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows39 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 390).take 10)
private theorem rows39_captured : ((compositionRewrites sources).drop 390).take 10 = rows39 := rfl
private def named39 : List ScopedRule := authored_rules% rows39
private theorem rows39_references : rows39.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows39_unique : (rows39.map Rewrite.name).Nodup := by decide +kernel
private theorem rows39_fresh : (rows39.map Rewrite.name).all
    (fun name => !(namesPrefix 390).contains name) = true := by decide +kernel
private theorem namesPrefix400_partition : namesPrefix 390 ++ rows39.map Rewrite.name = namesPrefix 400 := rfl
private theorem namesPrefix400_unique : (namesPrefix 400).Nodup := by
  rw [← namesPrefix400_partition]
  exact nodup_append_of_fresh _ _ namesPrefix390_unique rows39_unique rows39_fresh
private theorem named39_elaborated : elaborateRewrites? rows39 = some named39 := by
  simp [rows39, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows40 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 400).take 10)
private theorem rows40_captured : ((compositionRewrites sources).drop 400).take 10 = rows40 := rfl
private def named40 : List ScopedRule := authored_rules% rows40
private theorem rows40_references : rows40.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows40_unique : (rows40.map Rewrite.name).Nodup := by decide +kernel
private theorem rows40_fresh : (rows40.map Rewrite.name).all
    (fun name => !(namesPrefix 400).contains name) = true := by decide +kernel
private theorem namesPrefix410_partition : namesPrefix 400 ++ rows40.map Rewrite.name = namesPrefix 410 := rfl
private theorem namesPrefix410_unique : (namesPrefix 410).Nodup := by
  rw [← namesPrefix410_partition]
  exact nodup_append_of_fresh _ _ namesPrefix400_unique rows40_unique rows40_fresh
private theorem named40_elaborated : elaborateRewrites? rows40 = some named40 := by
  simp [rows40, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows41 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 410).take 10)
private theorem rows41_captured : ((compositionRewrites sources).drop 410).take 10 = rows41 := rfl
private def named41 : List ScopedRule := authored_rules% rows41
private theorem rows41_references : rows41.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows41_unique : (rows41.map Rewrite.name).Nodup := by decide +kernel
private theorem rows41_fresh : (rows41.map Rewrite.name).all
    (fun name => !(namesPrefix 410).contains name) = true := by decide +kernel
private theorem namesPrefix420_partition : namesPrefix 410 ++ rows41.map Rewrite.name = namesPrefix 420 := rfl
private theorem namesPrefix420_unique : (namesPrefix 420).Nodup := by
  rw [← namesPrefix420_partition]
  exact nodup_append_of_fresh _ _ namesPrefix410_unique rows41_unique rows41_fresh
private theorem named41_elaborated : elaborateRewrites? rows41 = some named41 := by
  simp [rows41, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows42 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 420).take 10)
private theorem rows42_captured : ((compositionRewrites sources).drop 420).take 10 = rows42 := rfl
private def named42 : List ScopedRule := authored_rules% rows42
private theorem rows42_references : rows42.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows42_unique : (rows42.map Rewrite.name).Nodup := by decide +kernel
private theorem rows42_fresh : (rows42.map Rewrite.name).all
    (fun name => !(namesPrefix 420).contains name) = true := by decide +kernel
private theorem namesPrefix430_partition : namesPrefix 420 ++ rows42.map Rewrite.name = namesPrefix 430 := rfl
private theorem namesPrefix430_unique : (namesPrefix 430).Nodup := by
  rw [← namesPrefix430_partition]
  exact nodup_append_of_fresh _ _ namesPrefix420_unique rows42_unique rows42_fresh
private theorem named42_elaborated : elaborateRewrites? rows42 = some named42 := by
  simp [rows42, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows43 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 430).take 10)
private theorem rows43_captured : ((compositionRewrites sources).drop 430).take 10 = rows43 := rfl
private def named43 : List ScopedRule := authored_rules% rows43
private theorem rows43_references : rows43.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows43_unique : (rows43.map Rewrite.name).Nodup := by decide +kernel
private theorem rows43_fresh : (rows43.map Rewrite.name).all
    (fun name => !(namesPrefix 430).contains name) = true := by decide +kernel
private theorem namesPrefix440_partition : namesPrefix 430 ++ rows43.map Rewrite.name = namesPrefix 440 := rfl
private theorem namesPrefix440_unique : (namesPrefix 440).Nodup := by
  rw [← namesPrefix440_partition]
  exact nodup_append_of_fresh _ _ namesPrefix430_unique rows43_unique rows43_fresh
private theorem named43_elaborated : elaborateRewrites? rows43 = some named43 := by
  simp [rows43, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows44 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 440).take 10)
private theorem rows44_captured : ((compositionRewrites sources).drop 440).take 10 = rows44 := rfl
private def named44 : List ScopedRule := authored_rules% rows44
private theorem rows44_references : rows44.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows44_unique : (rows44.map Rewrite.name).Nodup := by decide +kernel
private theorem rows44_fresh : (rows44.map Rewrite.name).all
    (fun name => !(namesPrefix 440).contains name) = true := by decide +kernel
private theorem namesPrefix450_partition : namesPrefix 440 ++ rows44.map Rewrite.name = namesPrefix 450 := rfl
private theorem namesPrefix450_unique : (namesPrefix 450).Nodup := by
  rw [← namesPrefix450_partition]
  exact nodup_append_of_fresh _ _ namesPrefix440_unique rows44_unique rows44_fresh
private theorem named44_elaborated : elaborateRewrites? rows44 = some named44 := by
  simp [rows44, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows45 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 450).take 10)
private theorem rows45_captured : ((compositionRewrites sources).drop 450).take 10 = rows45 := rfl
private def named45 : List ScopedRule := authored_rules% rows45
private theorem rows45_references : rows45.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows45_unique : (rows45.map Rewrite.name).Nodup := by decide +kernel
private theorem rows45_fresh : (rows45.map Rewrite.name).all
    (fun name => !(namesPrefix 450).contains name) = true := by decide +kernel
private theorem namesPrefix460_partition : namesPrefix 450 ++ rows45.map Rewrite.name = namesPrefix 460 := rfl
private theorem namesPrefix460_unique : (namesPrefix 460).Nodup := by
  rw [← namesPrefix460_partition]
  exact nodup_append_of_fresh _ _ namesPrefix450_unique rows45_unique rows45_fresh
private theorem named45_elaborated : elaborateRewrites? rows45 = some named45 := by
  simp [rows45, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows46 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 460).take 10)
private theorem rows46_captured : ((compositionRewrites sources).drop 460).take 10 = rows46 := rfl
private def named46 : List ScopedRule := authored_rules% rows46
private theorem rows46_references : rows46.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows46_unique : (rows46.map Rewrite.name).Nodup := by decide +kernel
private theorem rows46_fresh : (rows46.map Rewrite.name).all
    (fun name => !(namesPrefix 460).contains name) = true := by decide +kernel
private theorem namesPrefix470_partition : namesPrefix 460 ++ rows46.map Rewrite.name = namesPrefix 470 := rfl
private theorem namesPrefix470_unique : (namesPrefix 470).Nodup := by
  rw [← namesPrefix470_partition]
  exact nodup_append_of_fresh _ _ namesPrefix460_unique rows46_unique rows46_fresh
private theorem named46_elaborated : elaborateRewrites? rows46 = some named46 := by
  simp [rows46, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows47 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 470).take 10)
private theorem rows47_captured : ((compositionRewrites sources).drop 470).take 10 = rows47 := rfl
private def named47 : List ScopedRule := authored_rules% rows47
private theorem rows47_references : rows47.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows47_unique : (rows47.map Rewrite.name).Nodup := by decide +kernel
private theorem rows47_fresh : (rows47.map Rewrite.name).all
    (fun name => !(namesPrefix 470).contains name) = true := by decide +kernel
private theorem namesPrefix480_partition : namesPrefix 470 ++ rows47.map Rewrite.name = namesPrefix 480 := rfl
private theorem namesPrefix480_unique : (namesPrefix 480).Nodup := by
  rw [← namesPrefix480_partition]
  exact nodup_append_of_fresh _ _ namesPrefix470_unique rows47_unique rows47_fresh
private theorem named47_elaborated : elaborateRewrites? rows47 = some named47 := by
  simp [rows47, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows48 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 480).take 10)
private theorem rows48_captured : ((compositionRewrites sources).drop 480).take 10 = rows48 := rfl
private def named48 : List ScopedRule := authored_rules% rows48
private theorem rows48_references : rows48.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows48_unique : (rows48.map Rewrite.name).Nodup := by decide +kernel
private theorem rows48_fresh : (rows48.map Rewrite.name).all
    (fun name => !(namesPrefix 480).contains name) = true := by decide +kernel
private theorem namesPrefix490_partition : namesPrefix 480 ++ rows48.map Rewrite.name = namesPrefix 490 := rfl
private theorem namesPrefix490_unique : (namesPrefix 490).Nodup := by
  rw [← namesPrefix490_partition]
  exact nodup_append_of_fresh _ _ namesPrefix480_unique rows48_unique rows48_fresh
private theorem named48_elaborated : elaborateRewrites? rows48 = some named48 := by
  simp [rows48, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows49 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 490).take 10)
private theorem rows49_captured : ((compositionRewrites sources).drop 490).take 10 = rows49 := rfl
private def named49 : List ScopedRule := authored_rules% rows49
private theorem rows49_references : rows49.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows49_unique : (rows49.map Rewrite.name).Nodup := by decide +kernel
private theorem rows49_fresh : (rows49.map Rewrite.name).all
    (fun name => !(namesPrefix 490).contains name) = true := by decide +kernel
private theorem namesPrefix500_partition : namesPrefix 490 ++ rows49.map Rewrite.name = namesPrefix 500 := rfl
private theorem namesPrefix500_unique : (namesPrefix 500).Nodup := by
  rw [← namesPrefix500_partition]
  exact nodup_append_of_fresh _ _ namesPrefix490_unique rows49_unique rows49_fresh
private theorem named49_elaborated : elaborateRewrites? rows49 = some named49 := by
  simp [rows49, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows50 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 500).take 10)
private theorem rows50_captured : ((compositionRewrites sources).drop 500).take 10 = rows50 := rfl
private def named50 : List ScopedRule := authored_rules% rows50
private theorem rows50_references : rows50.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows50_unique : (rows50.map Rewrite.name).Nodup := by decide +kernel
private theorem rows50_fresh : (rows50.map Rewrite.name).all
    (fun name => !(namesPrefix 500).contains name) = true := by decide +kernel
private theorem namesPrefix510_partition : namesPrefix 500 ++ rows50.map Rewrite.name = namesPrefix 510 := rfl
private theorem namesPrefix510_unique : (namesPrefix 510).Nodup := by
  rw [← namesPrefix510_partition]
  exact nodup_append_of_fresh _ _ namesPrefix500_unique rows50_unique rows50_fresh
private theorem named50_elaborated : elaborateRewrites? rows50 = some named50 := by
  simp [rows50, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows51 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 510).take 10)
private theorem rows51_captured : ((compositionRewrites sources).drop 510).take 10 = rows51 := rfl
private def named51 : List ScopedRule := authored_rules% rows51
private theorem rows51_references : rows51.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows51_unique : (rows51.map Rewrite.name).Nodup := by decide +kernel
private theorem rows51_fresh : (rows51.map Rewrite.name).all
    (fun name => !(namesPrefix 510).contains name) = true := by decide +kernel
private theorem namesPrefix520_partition : namesPrefix 510 ++ rows51.map Rewrite.name = namesPrefix 520 := rfl
private theorem namesPrefix520_unique : (namesPrefix 520).Nodup := by
  rw [← namesPrefix520_partition]
  exact nodup_append_of_fresh _ _ namesPrefix510_unique rows51_unique rows51_fresh
private theorem named51_elaborated : elaborateRewrites? rows51 = some named51 := by
  simp [rows51, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows52 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 520).take 10)
private theorem rows52_captured : ((compositionRewrites sources).drop 520).take 10 = rows52 := rfl
private def named52 : List ScopedRule := authored_rules% rows52
private theorem rows52_references : rows52.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows52_unique : (rows52.map Rewrite.name).Nodup := by decide +kernel
private theorem rows52_fresh : (rows52.map Rewrite.name).all
    (fun name => !(namesPrefix 520).contains name) = true := by decide +kernel
private theorem namesPrefix530_partition : namesPrefix 520 ++ rows52.map Rewrite.name = namesPrefix 530 := rfl
private theorem namesPrefix530_unique : (namesPrefix 530).Nodup := by
  rw [← namesPrefix530_partition]
  exact nodup_append_of_fresh _ _ namesPrefix520_unique rows52_unique rows52_fresh
private theorem named52_elaborated : elaborateRewrites? rows52 = some named52 := by
  simp [rows52, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows53 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 530).take 10)
private theorem rows53_captured : ((compositionRewrites sources).drop 530).take 10 = rows53 := rfl
private def named53 : List ScopedRule := authored_rules% rows53
private theorem rows53_references : rows53.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows53_unique : (rows53.map Rewrite.name).Nodup := by decide +kernel
private theorem rows53_fresh : (rows53.map Rewrite.name).all
    (fun name => !(namesPrefix 530).contains name) = true := by decide +kernel
private theorem namesPrefix540_partition : namesPrefix 530 ++ rows53.map Rewrite.name = namesPrefix 540 := rfl
private theorem namesPrefix540_unique : (namesPrefix 540).Nodup := by
  rw [← namesPrefix540_partition]
  exact nodup_append_of_fresh _ _ namesPrefix530_unique rows53_unique rows53_fresh
private theorem named53_elaborated : elaborateRewrites? rows53 = some named53 := by
  simp [rows53, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows54 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 540).take 10)
private theorem rows54_captured : ((compositionRewrites sources).drop 540).take 10 = rows54 := rfl
private def named54 : List ScopedRule := authored_rules% rows54
private theorem rows54_references : rows54.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows54_unique : (rows54.map Rewrite.name).Nodup := by decide +kernel
private theorem rows54_fresh : (rows54.map Rewrite.name).all
    (fun name => !(namesPrefix 540).contains name) = true := by decide +kernel
private theorem namesPrefix550_partition : namesPrefix 540 ++ rows54.map Rewrite.name = namesPrefix 550 := rfl
private theorem namesPrefix550_unique : (namesPrefix 550).Nodup := by
  rw [← namesPrefix550_partition]
  exact nodup_append_of_fresh _ _ namesPrefix540_unique rows54_unique rows54_fresh
private theorem named54_elaborated : elaborateRewrites? rows54 = some named54 := by
  simp [rows54, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows55 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 550).take 10)
private theorem rows55_captured : ((compositionRewrites sources).drop 550).take 10 = rows55 := rfl
private def named55 : List ScopedRule := authored_rules% rows55
private theorem rows55_references : rows55.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows55_unique : (rows55.map Rewrite.name).Nodup := by decide +kernel
private theorem rows55_fresh : (rows55.map Rewrite.name).all
    (fun name => !(namesPrefix 550).contains name) = true := by decide +kernel
private theorem namesPrefix560_partition : namesPrefix 550 ++ rows55.map Rewrite.name = namesPrefix 560 := rfl
private theorem namesPrefix560_unique : (namesPrefix 560).Nodup := by
  rw [← namesPrefix560_partition]
  exact nodup_append_of_fresh _ _ namesPrefix550_unique rows55_unique rows55_fresh
private theorem named55_elaborated : elaborateRewrites? rows55 = some named55 := by
  simp [rows55, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows56 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 560).take 10)
private theorem rows56_captured : ((compositionRewrites sources).drop 560).take 10 = rows56 := rfl
private def named56 : List ScopedRule := authored_rules% rows56
private theorem rows56_references : rows56.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows56_unique : (rows56.map Rewrite.name).Nodup := by decide +kernel
private theorem rows56_fresh : (rows56.map Rewrite.name).all
    (fun name => !(namesPrefix 560).contains name) = true := by decide +kernel
private theorem namesPrefix570_partition : namesPrefix 560 ++ rows56.map Rewrite.name = namesPrefix 570 := rfl
private theorem namesPrefix570_unique : (namesPrefix 570).Nodup := by
  rw [← namesPrefix570_partition]
  exact nodup_append_of_fresh _ _ namesPrefix560_unique rows56_unique rows56_fresh
private theorem named56_elaborated : elaborateRewrites? rows56 = some named56 := by
  simp [rows56, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows57 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 570).take 10)
private theorem rows57_captured : ((compositionRewrites sources).drop 570).take 10 = rows57 := rfl
private def named57 : List ScopedRule := authored_rules% rows57
private theorem rows57_references : rows57.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows57_unique : (rows57.map Rewrite.name).Nodup := by decide +kernel
private theorem rows57_fresh : (rows57.map Rewrite.name).all
    (fun name => !(namesPrefix 570).contains name) = true := by decide +kernel
private theorem namesPrefix580_partition : namesPrefix 570 ++ rows57.map Rewrite.name = namesPrefix 580 := rfl
private theorem namesPrefix580_unique : (namesPrefix 580).Nodup := by
  rw [← namesPrefix580_partition]
  exact nodup_append_of_fresh _ _ namesPrefix570_unique rows57_unique rows57_fresh
private theorem named57_elaborated : elaborateRewrites? rows57 = some named57 := by
  simp [rows57, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows58 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 580).take 10)
private theorem rows58_captured : ((compositionRewrites sources).drop 580).take 10 = rows58 := rfl
private def named58 : List ScopedRule := authored_rules% rows58
private theorem rows58_references : rows58.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows58_unique : (rows58.map Rewrite.name).Nodup := by decide +kernel
private theorem rows58_fresh : (rows58.map Rewrite.name).all
    (fun name => !(namesPrefix 580).contains name) = true := by decide +kernel
private theorem namesPrefix590_partition : namesPrefix 580 ++ rows58.map Rewrite.name = namesPrefix 590 := rfl
private theorem namesPrefix590_unique : (namesPrefix 590).Nodup := by
  rw [← namesPrefix590_partition]
  exact nodup_append_of_fresh _ _ namesPrefix580_unique rows58_unique rows58_fresh
private theorem named58_elaborated : elaborateRewrites? rows58 = some named58 := by
  simp [rows58, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows59 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 590).take 10)
private theorem rows59_captured : ((compositionRewrites sources).drop 590).take 10 = rows59 := rfl
private def named59 : List ScopedRule := authored_rules% rows59
private theorem rows59_references : rows59.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows59_unique : (rows59.map Rewrite.name).Nodup := by decide +kernel
private theorem rows59_fresh : (rows59.map Rewrite.name).all
    (fun name => !(namesPrefix 590).contains name) = true := by decide +kernel
private theorem namesPrefix600_partition : namesPrefix 590 ++ rows59.map Rewrite.name = namesPrefix 600 := rfl
private theorem namesPrefix600_unique : (namesPrefix 600).Nodup := by
  rw [← namesPrefix600_partition]
  exact nodup_append_of_fresh _ _ namesPrefix590_unique rows59_unique rows59_fresh
private theorem named59_elaborated : elaborateRewrites? rows59 = some named59 := by
  simp [rows59, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows60 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 600).take 10)
private theorem rows60_captured : ((compositionRewrites sources).drop 600).take 10 = rows60 := rfl
private def named60 : List ScopedRule := authored_rules% rows60
private theorem rows60_references : rows60.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows60_unique : (rows60.map Rewrite.name).Nodup := by decide +kernel
private theorem rows60_fresh : (rows60.map Rewrite.name).all
    (fun name => !(namesPrefix 600).contains name) = true := by decide +kernel
private theorem namesPrefix610_partition : namesPrefix 600 ++ rows60.map Rewrite.name = namesPrefix 610 := rfl
private theorem namesPrefix610_unique : (namesPrefix 610).Nodup := by
  rw [← namesPrefix610_partition]
  exact nodup_append_of_fresh _ _ namesPrefix600_unique rows60_unique rows60_fresh
private theorem named60_elaborated : elaborateRewrites? rows60 = some named60 := by
  simp [rows60, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows61 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 610).take 10)
private theorem rows61_captured : ((compositionRewrites sources).drop 610).take 10 = rows61 := rfl
private def named61 : List ScopedRule := authored_rules% rows61
private theorem rows61_references : rows61.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows61_unique : (rows61.map Rewrite.name).Nodup := by decide +kernel
private theorem rows61_fresh : (rows61.map Rewrite.name).all
    (fun name => !(namesPrefix 610).contains name) = true := by decide +kernel
private theorem namesPrefix620_partition : namesPrefix 610 ++ rows61.map Rewrite.name = namesPrefix 620 := rfl
private theorem namesPrefix620_unique : (namesPrefix 620).Nodup := by
  rw [← namesPrefix620_partition]
  exact nodup_append_of_fresh _ _ namesPrefix610_unique rows61_unique rows61_fresh
private theorem named61_elaborated : elaborateRewrites? rows61 = some named61 := by
  simp [rows61, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows62 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 620).take 10)
private theorem rows62_captured : ((compositionRewrites sources).drop 620).take 10 = rows62 := rfl
private def named62 : List ScopedRule := authored_rules% rows62
private theorem rows62_references : rows62.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows62_unique : (rows62.map Rewrite.name).Nodup := by decide +kernel
private theorem rows62_fresh : (rows62.map Rewrite.name).all
    (fun name => !(namesPrefix 620).contains name) = true := by decide +kernel
private theorem namesPrefix630_partition : namesPrefix 620 ++ rows62.map Rewrite.name = namesPrefix 630 := rfl
private theorem namesPrefix630_unique : (namesPrefix 630).Nodup := by
  rw [← namesPrefix630_partition]
  exact nodup_append_of_fresh _ _ namesPrefix620_unique rows62_unique rows62_fresh
private theorem named62_elaborated : elaborateRewrites? rows62 = some named62 := by
  simp [rows62, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows63 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 630).take 10)
private theorem rows63_captured : ((compositionRewrites sources).drop 630).take 10 = rows63 := rfl
private def named63 : List ScopedRule := authored_rules% rows63
private theorem rows63_references : rows63.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows63_unique : (rows63.map Rewrite.name).Nodup := by decide +kernel
private theorem rows63_fresh : (rows63.map Rewrite.name).all
    (fun name => !(namesPrefix 630).contains name) = true := by decide +kernel
private theorem namesPrefix640_partition : namesPrefix 630 ++ rows63.map Rewrite.name = namesPrefix 640 := rfl
private theorem namesPrefix640_unique : (namesPrefix 640).Nodup := by
  rw [← namesPrefix640_partition]
  exact nodup_append_of_fresh _ _ namesPrefix630_unique rows63_unique rows63_fresh
private theorem named63_elaborated : elaborateRewrites? rows63 = some named63 := by
  simp [rows63, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows64 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 640).take 10)
private theorem rows64_captured : ((compositionRewrites sources).drop 640).take 10 = rows64 := rfl
private def named64 : List ScopedRule := authored_rules% rows64
private theorem rows64_references : rows64.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows64_unique : (rows64.map Rewrite.name).Nodup := by decide +kernel
private theorem rows64_fresh : (rows64.map Rewrite.name).all
    (fun name => !(namesPrefix 640).contains name) = true := by decide +kernel
private theorem namesPrefix650_partition : namesPrefix 640 ++ rows64.map Rewrite.name = namesPrefix 650 := rfl
private theorem namesPrefix650_unique : (namesPrefix 650).Nodup := by
  rw [← namesPrefix650_partition]
  exact nodup_append_of_fresh _ _ namesPrefix640_unique rows64_unique rows64_fresh
private theorem named64_elaborated : elaborateRewrites? rows64 = some named64 := by
  simp [rows64, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows65 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 650).take 10)
private theorem rows65_captured : ((compositionRewrites sources).drop 650).take 10 = rows65 := rfl
private def named65 : List ScopedRule := authored_rules% rows65
private theorem rows65_references : rows65.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows65_unique : (rows65.map Rewrite.name).Nodup := by decide +kernel
private theorem rows65_fresh : (rows65.map Rewrite.name).all
    (fun name => !(namesPrefix 650).contains name) = true := by decide +kernel
private theorem namesPrefix660_partition : namesPrefix 650 ++ rows65.map Rewrite.name = namesPrefix 660 := rfl
private theorem namesPrefix660_unique : (namesPrefix 660).Nodup := by
  rw [← namesPrefix660_partition]
  exact nodup_append_of_fresh _ _ namesPrefix650_unique rows65_unique rows65_fresh
private theorem named65_elaborated : elaborateRewrites? rows65 = some named65 := by
  simp [rows65, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows66 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 660).take 10)
private theorem rows66_captured : ((compositionRewrites sources).drop 660).take 10 = rows66 := rfl
private def named66 : List ScopedRule := authored_rules% rows66
private theorem rows66_references : rows66.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows66_unique : (rows66.map Rewrite.name).Nodup := by decide +kernel
private theorem rows66_fresh : (rows66.map Rewrite.name).all
    (fun name => !(namesPrefix 660).contains name) = true := by decide +kernel
private theorem namesPrefix670_partition : namesPrefix 660 ++ rows66.map Rewrite.name = namesPrefix 670 := rfl
private theorem namesPrefix670_unique : (namesPrefix 670).Nodup := by
  rw [← namesPrefix670_partition]
  exact nodup_append_of_fresh _ _ namesPrefix660_unique rows66_unique rows66_fresh
private theorem named66_elaborated : elaborateRewrites? rows66 = some named66 := by
  simp [rows66, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows67 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 670).take 10)
private theorem rows67_captured : ((compositionRewrites sources).drop 670).take 10 = rows67 := rfl
private def named67 : List ScopedRule := authored_rules% rows67
private theorem rows67_references : rows67.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows67_unique : (rows67.map Rewrite.name).Nodup := by decide +kernel
private theorem rows67_fresh : (rows67.map Rewrite.name).all
    (fun name => !(namesPrefix 670).contains name) = true := by decide +kernel
private theorem namesPrefix680_partition : namesPrefix 670 ++ rows67.map Rewrite.name = namesPrefix 680 := rfl
private theorem namesPrefix680_unique : (namesPrefix 680).Nodup := by
  rw [← namesPrefix680_partition]
  exact nodup_append_of_fresh _ _ namesPrefix670_unique rows67_unique rows67_fresh
private theorem named67_elaborated : elaborateRewrites? rows67 = some named67 := by
  simp [rows67, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows68 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 680).take 10)
private theorem rows68_captured : ((compositionRewrites sources).drop 680).take 10 = rows68 := rfl
private def named68 : List ScopedRule := authored_rules% rows68
private theorem rows68_references : rows68.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows68_unique : (rows68.map Rewrite.name).Nodup := by decide +kernel
private theorem rows68_fresh : (rows68.map Rewrite.name).all
    (fun name => !(namesPrefix 680).contains name) = true := by decide +kernel
private theorem namesPrefix690_partition : namesPrefix 680 ++ rows68.map Rewrite.name = namesPrefix 690 := rfl
private theorem namesPrefix690_unique : (namesPrefix 690).Nodup := by
  rw [← namesPrefix690_partition]
  exact nodup_append_of_fresh _ _ namesPrefix680_unique rows68_unique rows68_fresh
private theorem named68_elaborated : elaborateRewrites? rows68 = some named68 := by
  simp [rows68, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows69 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 690).take 10)
private theorem rows69_captured : ((compositionRewrites sources).drop 690).take 10 = rows69 := rfl
private def named69 : List ScopedRule := authored_rules% rows69
private theorem rows69_references : rows69.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows69_unique : (rows69.map Rewrite.name).Nodup := by decide +kernel
private theorem rows69_fresh : (rows69.map Rewrite.name).all
    (fun name => !(namesPrefix 690).contains name) = true := by decide +kernel
private theorem namesPrefix700_partition : namesPrefix 690 ++ rows69.map Rewrite.name = namesPrefix 700 := rfl
private theorem namesPrefix700_unique : (namesPrefix 700).Nodup := by
  rw [← namesPrefix700_partition]
  exact nodup_append_of_fresh _ _ namesPrefix690_unique rows69_unique rows69_fresh
private theorem named69_elaborated : elaborateRewrites? rows69 = some named69 := by
  simp [rows69, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows70 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 700).take 10)
private theorem rows70_captured : ((compositionRewrites sources).drop 700).take 10 = rows70 := rfl
private def named70 : List ScopedRule := authored_rules% rows70
private theorem rows70_references : rows70.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows70_unique : (rows70.map Rewrite.name).Nodup := by decide +kernel
private theorem rows70_fresh : (rows70.map Rewrite.name).all
    (fun name => !(namesPrefix 700).contains name) = true := by decide +kernel
private theorem namesPrefix710_partition : namesPrefix 700 ++ rows70.map Rewrite.name = namesPrefix 710 := rfl
private theorem namesPrefix710_unique : (namesPrefix 710).Nodup := by
  rw [← namesPrefix710_partition]
  exact nodup_append_of_fresh _ _ namesPrefix700_unique rows70_unique rows70_fresh
private theorem named70_elaborated : elaborateRewrites? rows70 = some named70 := by
  simp [rows70, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows71 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 710).take 10)
private theorem rows71_captured : ((compositionRewrites sources).drop 710).take 10 = rows71 := rfl
private def named71 : List ScopedRule := authored_rules% rows71
private theorem rows71_references : rows71.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows71_unique : (rows71.map Rewrite.name).Nodup := by decide +kernel
private theorem rows71_fresh : (rows71.map Rewrite.name).all
    (fun name => !(namesPrefix 710).contains name) = true := by decide +kernel
private theorem namesPrefix720_partition : namesPrefix 710 ++ rows71.map Rewrite.name = namesPrefix 720 := rfl
private theorem namesPrefix720_unique : (namesPrefix 720).Nodup := by
  rw [← namesPrefix720_partition]
  exact nodup_append_of_fresh _ _ namesPrefix710_unique rows71_unique rows71_fresh
private theorem named71_elaborated : elaborateRewrites? rows71 = some named71 := by
  simp [rows71, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows72 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 720).take 10)
private theorem rows72_captured : ((compositionRewrites sources).drop 720).take 10 = rows72 := rfl
private def named72 : List ScopedRule := authored_rules% rows72
private theorem rows72_references : rows72.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows72_unique : (rows72.map Rewrite.name).Nodup := by decide +kernel
private theorem rows72_fresh : (rows72.map Rewrite.name).all
    (fun name => !(namesPrefix 720).contains name) = true := by decide +kernel
private theorem namesPrefix730_partition : namesPrefix 720 ++ rows72.map Rewrite.name = namesPrefix 730 := rfl
private theorem namesPrefix730_unique : (namesPrefix 730).Nodup := by
  rw [← namesPrefix730_partition]
  exact nodup_append_of_fresh _ _ namesPrefix720_unique rows72_unique rows72_fresh
private theorem named72_elaborated : elaborateRewrites? rows72 = some named72 := by
  simp [rows72, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private def rows73 : List Rewrite := authored_rows% (((compositionRewrites sources).drop 730).take 10)
private theorem rows73_captured : ((compositionRewrites sources).drop 730).take 10 = rows73 := rfl
private def named73 : List ScopedRule := authored_rules% rows73
private theorem rows73_references : rows73.all (fun row =>
    termSupported (compositionOperators sources) row.head && termsSupported (compositionOperators sources) row.body) = true := by decide +kernel
private theorem rows73_unique : (rows73.map Rewrite.name).Nodup := by decide +kernel
private theorem rows73_fresh : (rows73.map Rewrite.name).all
    (fun name => !(namesPrefix 730).contains name) = true := by decide +kernel
private theorem namesPrefix740_partition : namesPrefix 730 ++ rows73.map Rewrite.name = namesPrefix 740 := rfl
private theorem namesPrefix740_unique : (namesPrefix 740).Nodup := by
  rw [← namesPrefix740_partition]
  exact nodup_append_of_fresh _ _ namesPrefix730_unique rows73_unique rows73_fresh
private theorem named73_elaborated : elaborateRewrites? rows73 = some named73 := by
  simp [rows73, elaborateRewrites?, elaborateRewrite?, elaborateRewriteCandidate?,
    elaborateAtom?, elaborateAtoms?, elaborateTerm?, elaborateTerms?]
  decide +kernel

private theorem rewrites_partition : compositionRewrites sources = rows0 ++ rows1 ++ rows2 ++ rows3 ++ rows4 ++ rows5 ++ rows6 ++ rows7 ++ rows8 ++ rows9 ++ rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15 ++ rows16 ++ rows17 ++ rows18 ++ rows19 ++ rows20 ++ rows21 ++ rows22 ++ rows23 ++ rows24 ++ rows25 ++ rows26 ++ rows27 ++ rows28 ++ rows29 ++ rows30 ++ rows31 ++ rows32 ++ rows33 ++ rows34 ++ rows35 ++ rows36 ++ rows37 ++ rows38 ++ rows39 ++ rows40 ++ rows41 ++ rows42 ++ rows43 ++ rows44 ++ rows45 ++ rows46 ++ rows47 ++ rows48 ++ rows49 ++ rows50 ++ rows51 ++ rows52 ++ rows53 ++ rows54 ++ rows55 ++ rows56 ++ rows57 ++ rows58 ++ rows59 ++ rows60 ++ rows61 ++ rows62 ++ rows63 ++ rows64 ++ rows65 ++ rows66 ++ rows67 ++ rows68 ++ rows69 ++ rows70 ++ rows71 ++ rows72 ++ rows73 := rfl

/-- Every authored rule identity is retained once in its original occurrence. -/
theorem rewrite_names_unique : (compositionRewriteNames sources).Nodup :=
  namesPrefix740_unique

theorem source_names_unique : (sources.map Source.name).Nodup := by decide +kernel

theorem source_schemas_valid : sources.all Source.hasValidSchema = true := by decide +kernel

theorem source_equations_empty : sources.all (fun source => source.equations.isEmpty) = true := by decide +kernel

theorem source_references_valid : sources.all (Source.termsValidIn (compositionOperators sources)) = true := by
  apply source_reference_validity _ _ source_equations_empty
  rw [rewrites_partition]
  simp only [List.all_append, rows0_references, rows1_references, rows2_references, rows3_references, rows4_references, rows5_references, rows6_references, rows7_references, rows8_references, rows9_references, rows10_references, rows11_references, rows12_references, rows13_references, rows14_references, rows15_references, rows16_references, rows17_references, rows18_references, rows19_references, rows20_references, rows21_references, rows22_references, rows23_references, rows24_references, rows25_references, rows26_references, rows27_references, rows28_references, rows29_references, rows30_references, rows31_references, rows32_references, rows33_references, rows34_references, rows35_references, rows36_references, rows37_references, rows38_references, rows39_references, rows40_references, rows41_references, rows42_references, rows43_references, rows44_references, rows45_references, rows46_references, rows47_references, rows48_references, rows49_references, rows50_references, rows51_references, rows52_references, rows53_references, rows54_references, rows55_references, rows56_references, rows57_references, rows58_references, rows59_references, rows60_references, rows61_references, rows62_references, rows63_references, rows64_references, rows65_references, rows66_references, rows67_references, rows68_references, rows69_references, rows70_references, rows71_references, rows72_references, rows73_references, Bool.and_self]

/-- The existing closed-source guard, including all operator references. -/
theorem composition_admitted : compositionValid sources = true := by
  simp only [compositionValid, source_names_unique, rewrite_names_unique, source_schemas_valid,
    source_references_valid, decide_true, Bool.and_true]
  rfl

/-- Plain Horn constructors from the existing elaborator, checked below against
all retained source rows. This cache supplies no admission judgment by itself. -/
def namedRules : List ScopedRule := named0 ++ named1 ++ named2 ++ named3 ++ named4 ++ named5 ++ named6 ++ named7 ++ named8 ++ named9 ++ named10 ++ named11 ++ named12 ++ named13 ++ named14 ++ named15 ++ named16 ++ named17 ++ named18 ++ named19 ++ named20 ++ named21 ++ named22 ++ named23 ++ named24 ++ named25 ++ named26 ++ named27 ++ named28 ++ named29 ++ named30 ++ named31 ++ named32 ++ named33 ++ named34 ++ named35 ++ named36 ++ named37 ++ named38 ++ named39 ++ named40 ++ named41 ++ named42 ++ named43 ++ named44 ++ named45 ++ named46 ++ named47 ++ named48 ++ named49 ++ named50 ++ named51 ++ named52 ++ named53 ++ named54 ++ named55 ++ named56 ++ named57 ++ named58 ++ named59 ++ named60 ++ named61 ++ named62 ++ named63 ++ named64 ++ named65 ++ named66 ++ named67 ++ named68 ++ named69 ++ named70 ++ named71 ++ named72 ++ named73

theorem namedRules_elaborated : elaborateRewrites? (compositionRewrites sources) = some namedRules := by
  rw [rewrites_partition]
  simp only [elaborateRewrites_append, named0_elaborated, named1_elaborated, named2_elaborated, named3_elaborated, named4_elaborated, named5_elaborated, named6_elaborated, named7_elaborated, named8_elaborated, named9_elaborated, named10_elaborated, named11_elaborated, named12_elaborated, named13_elaborated, named14_elaborated, named15_elaborated, named16_elaborated, named17_elaborated, named18_elaborated, named19_elaborated, named20_elaborated, named21_elaborated, named22_elaborated, named23_elaborated, named24_elaborated, named25_elaborated, named26_elaborated, named27_elaborated, named28_elaborated, named29_elaborated, named30_elaborated, named31_elaborated, named32_elaborated, named33_elaborated, named34_elaborated, named35_elaborated, named36_elaborated, named37_elaborated, named38_elaborated, named39_elaborated, named40_elaborated, named41_elaborated, named42_elaborated, named43_elaborated, named44_elaborated, named45_elaborated, named46_elaborated, named47_elaborated, named48_elaborated, named49_elaborated, named50_elaborated, named51_elaborated, named52_elaborated, named53_elaborated, named54_elaborated, named55_elaborated, named56_elaborated, named57_elaborated, named58_elaborated, named59_elaborated, named60_elaborated, named61_elaborated, named62_elaborated, named63_elaborated, named64_elaborated, named65_elaborated, named66_elaborated, named67_elaborated, named68_elaborated, named69_elaborated, named70_elaborated, named71_elaborated, named72_elaborated, named73_elaborated]
  rfl

/-- The existing ordered Horn program; definition names and source occurrence
indices retain their complete authored ordering. -/
def program : Program := programOf namedRules

theorem program_elaborated : elaborateProgram? sources = some program := by
  simp only [elaborateProgram?, elaborateComposition?, composition_admitted,
    source_equations_empty, Bool.and_self, ↓reduceIte, namedRules_elaborated]
  rfl

theorem program_preserves_source_names : program.map Rule.name =
    (compositionRewrites sources).map Rewrite.name :=
  elaborateProgram?_preserves_names program_elaborated

theorem source_count : sources.length = 11 := rfl

theorem rule_count : (compositionRewrites sources).length = 731 := rfl

theorem program_count : program.length = 731 := by
  rw [elaborateProgram?_preserves_length program_elaborated, rule_count]

/-! Refusal controls concern the complete existing admission boundaries. -/

/-- Repeating the retained source composition collides with its actual source
identities even though the individual source data remains well formed. -/
theorem repeated_sources_refused : elaborateProgram? (sources ++ sources) = none := by
  have collision : ¬ ((sources ++ sources).map Source.name).Nodup := by decide +kernel
  have invalid : compositionValid (sources ++ sources) = false := by
    simp only [compositionValid, collision, decide_false, Bool.and_false, Bool.false_and]
  simp [elaborateProgram?, elaborateComposition?, invalid]

private def malformedProviderBody : Rewrite :=
  { groundProviderSource.rewrites[0]'(by decide +kernel) with
    body := [.atom "not-a-relation-application"] }

/-- Reading an authentic head never admits a malformed body. -/
theorem retained_provider_with_malformed_body_refused :
    elaborateRewrite? malformedProviderBody = none := by decide +kernel

/-- Native variable spelling is outside the authored first-order source
variable convention; it cannot silently acquire a Horn variable identifier. -/
theorem host_variable_refused :
    elaborateTerm? ["?name"] (.atom "$name") = none := by decide +kernel

/-- A singleton list is retained as a list and is refused where the exact
source schema requires the source name to be an atom. -/
theorem list_source_name_refused : decode (.list [.atom "gslt-presentation-v1",
    .list [.atom "GroundRelationsV1"], .list [.atom "signature"],
    .list [.atom "equations"], .list [.atom "rewrites"]]) = none := rfl

end Mettapedia.Languages.MM0.MeTTa.TextualAuthoredSource
