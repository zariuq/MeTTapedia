import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationPayloadInterpretation
import Mettapedia.GSLT.Parsing.LanguageDefScalarStructural
import Mettapedia.GSLT.Parsing.LanguageDefScalarUnicode
import Mettapedia.GSLT.Parsing.ClassAwarePackedForestSaturation

/-! # Authored transform syntax from scalar input to interpreted data

`Tcalc.Syntax` supplies all structural productions of this profile. Literal
spellings are Unicode strings; there are no additional lexical-sort rows.
Source derivations, compiled whole-input entries and replayed packed forests
are connected before any ambiguity policy selects a tree. Every admitted
source tree decodes to the actual transform carrier of its declared sort.
Canonical printing supplies such a source tree at arbitrary finite depth.
Uniqueness of all parses of that text is a further obligation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.SyntaxSource

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework
open Mettapedia.GSLT.Parsing
open ParserProfileSemantics PresentationExprSemantics LanguageDefSyntaxCompiler
open ClassAwareParserPackCorrespondence ClassAwarePackedForest ClassAwareParserPackCertificate
open LanguageDefGrammarAlgebra LanguageDefScalarPrinter
open Payloads

/-- The authored structural syntax profile. Lexical abbreviations may be
added by a separate profile with an explicit interpretation. -/
def profile (sort : String) : ParserProfileLayer :=
  ⟨"Tcalc.Syntax.scalar-v1", sort, [], []⟩

def literalScalars (token : String) : Option (List Nat) := some (stringScalars token)

def plan (sort : String) : CompiledParserPackPlan :=
  { lexical := compileLexicalPack (profile sort)
    structural := (compileStructuralProductions? literalScalars sort Payloads.rules).get (by rfl) }

theorem plan_compiled (sort : String) :
    compileParserPackPlan? literalScalars (profile sort) Payloads.rules = some (plan sort) := rfl

theorem plan_agreement (sort : String) :
    ParserPackPlanAgreement literalScalars (profile sort) Payloads.rules (plan sort) :=
  ParserPackPlanAgreement.of_compilation (plan_compiled sort)

abbrev Source (sort : String) (input : List Nat) (tree : CST) :=
  LanguageDefScalarSyntax.DerivesAt literalScalars (profile sort) dataLanguage input
    sort 0 input.length tree

abbrev Entry (sort : String) (input : List Nat) (tree : CST) :=
  ParserPackEntryDerivesAt (profile sort) (plan sort) input
    (plan sort).entryProduction.resultState input.length tree

def readParsed (sort : String) (tree : CST) : Option (Carrier sort) :=
  (LanguageDefScalarStructural.tree? tree).bind (Payloads.decode sort)

theorem source_iff_entry (sort : String) (input : List Nat) (tree : CST) :
    Nonempty (Source sort input tree) ↔ Nonempty (Entry sort input tree) :=
  (LanguageDefScalarSyntax.source_plan_iff data_compiles).trans
    (sourcePlanEntryDerivationEquiv (plan_agreement sort) tree).nonempty_congr

theorem source_iff_root (sort : String) (input : List Nat) (tree : CST) :
    Nonempty (Source sort input tree) ↔
      Nonempty (ParserPackRootDerives (profile sort) (plan sort) input tree) :=
  (LanguageDefScalarSyntax.source_plan_iff data_compiles).trans
    (sourcePlanRootDerivationEquiv (plan_agreement sort) tree).nonempty_congr

/-- The scalar input and actual decoded AST are both related to the authored
row derivation. This is an equivalence, not only a forward parser simulation. -/
theorem source_iff_tokens (sort : String) (input : List Nat) (pattern : Pattern) :
    (∃ tree, LanguageDefScalarStructural.tree? tree = some pattern ∧
      Nonempty (Source sort input tree)) ↔
    ∃ tokens, GrammarDerives.Derives dataLanguage sort tokens pattern ∧
      LanguageDefScalarStructural.spell literalScalars tokens = some input :=
  LanguageDefScalarStructural.full_source_iff_tokens rfl sort pattern

theorem source_decodes {sort : String} {input : List Nat} {tree : CST}
    (source : Source sort input tree) :
    ∃ value : Carrier sort, readParsed sort tree = some value := by
  obtain ⟨tokens, pattern, erased, derived, _⟩ :=
    LanguageDefScalarStructural.full_source_to_tokens rfl source
  obtain ⟨value, decoded⟩ := Payloads.source_decodes derived
  refine ⟨value, ?_⟩
  simp only [readParsed, erased, Option.bind_some, decoded]

theorem source_unicode {sort : String} {input : List Nat} {tree : CST}
    (source : Source sort input tree) : ∀ point ∈ input, point.isValidChar := by
  intro point member
  exact render_valid source point ((full_source source).symm ▸ member)

abbrev Packed (forest : Forest) (sort : String) (input : List Nat) (tree : CST) :=
  PackedFibre forest (profile sort) (plan sort) input sort 0 input.length tree

theorem packed_reflects_source (forest : Forest) (sort : String) (input : List Nat) (tree : CST) :
    Nonempty (Packed forest sort input tree) → Nonempty (Source sort input tree) := by
  rintro ⟨certificate, replay⟩
  exact (source_iff_root sort input tree).mpr ⟨replay.derivation⟩

/-- Global rule saturation is a sufficient completeness certificate. This
statement does not assume a root-pruned runtime forest satisfies it. -/
theorem complete_forest_iff_source (forest : Forest) (sort : String) (input : List Nat)
    (checked : ClassAwarePackedForestSaturation.validateRuleSaturation
      forest (profile sort) (plan sort) input = true) (tree : CST) :
    Nonempty (Packed forest sort input tree) ↔ Nonempty (Source sort input tree) := by
  refine ⟨packed_reflects_source forest sort input tree, ?_⟩
  intro source
  obtain ⟨derived⟩ := (source_iff_root sort input tree).mp source
  have complete := ClassAwarePackedForestSaturation.validateRuleSaturation_root_complete checked tree
  exact ⟨Certificate.ofDerivation derived, ⟨complete derived⟩,
    ClassAwareParserPackCertificate.Replays.ofDerivation derived⟩

def Selected (keep : CST → Bool) (forest : Forest) (sort : String)
    (input : List Nat) (tree : CST) : Prop :=
  Nonempty (Packed forest sort input tree) ∧ keep tree = true

theorem selected_iff_source (keep : CST → Bool) (forest : Forest) (sort : String) (input : List Nat)
    (checked : ClassAwarePackedForestSaturation.validateRuleSaturation
      forest (profile sort) (plan sort) input = true) (tree : CST) :
    Selected keep forest sort input tree ↔ Nonempty (Source sort input tree) ∧ keep tree = true :=
  and_congr (complete_forest_iff_source forest sort input checked tree) Iff.rfl

theorem selected_decodes {keep : CST → Bool} {forest : Forest} {sort : String}
    {input : List Nat} {tree : CST} (selected : Selected keep forest sort input tree) :
    ∃ value : Carrier sort, readParsed sort tree = some value := by
  obtain ⟨source⟩ := packed_reflects_source forest sort input tree selected.1
  exact source_decodes source

def printTokens (tokens : List String) : List Nat := tokens.flatMap stringScalars

theorem spell_printTokens (tokens : List String) :
    LanguageDefScalarStructural.spell literalScalars tokens = some (printTokens tokens) := by
  induction tokens with
  | nil => rfl
  | cons first rest ih =>
      simp only [LanguageDefScalarStructural.spell, literalScalars, ih]
      rfl

/-- Printing any typed route yields a real whole-input source derivation and
its interpreted data. This existence law does not select among other parses. -/
theorem printed_route_source {sort : String} (route : Payloads.Route sort) :
    ∃ tree, Nonempty (Source sort (printTokens ((syntaxAlgebra Payloads.rules).evaluate route).tokens) tree) ∧
      readParsed sort tree = some (interpret interpretation route) := by
  have derived := evaluate_source_derives data_compiles route
  obtain ⟨tree, erased, source⟩ := (source_iff_tokens sort _ _).mpr
    ⟨_, derived, spell_printTokens _⟩
  refine ⟨tree, source, ?_⟩
  simp only [readParsed, erased, Option.bind_some, decode_route]
  rfl

/-- The binding-tree printer is connected to the actual scalar source grammar. -/
theorem printed_term_source (term : Term) :
    ∃ tree, Nonempty (Source "TcTerm" (printTokens ((syntaxAlgebra Payloads.rules).evaluate (termRoute term)).tokens) tree) ∧
      readParsed "TcTerm" tree = some term := by
  obtain ⟨tree, source, decoded⟩ := printed_route_source (termRoute term)
  have interpretationEq := decode_route (termRoute term)
  rw [termRoute_tree] at interpretationEq
  change readTerm (termPattern term) = some (interpret interpretation (termRoute term)) at interpretationEq
  rw [readTerm_pattern] at interpretationEq
  exact ⟨tree, source, decoded.trans (congrArg some (Option.some.inj interpretationEq).symm)⟩

/-- An admitted full source cannot contain an invalid Unicode scalar. -/
theorem invalid_scalar_refused {sort : String} {input : List Nat} {point : Nat}
    (member : point ∈ input) (invalid : ¬point.isValidChar) :
    ¬ ∃ tree, Nonempty (Source sort input tree) := by
  rintro ⟨tree, ⟨source⟩⟩
  exact invalid (source_unicode source point member)

#print axioms source_iff_entry
#print axioms source_iff_tokens
#print axioms source_decodes
#print axioms selected_decodes
#print axioms printed_route_source
#print axioms printed_term_source
#print axioms invalid_scalar_refused

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.SyntaxSource
