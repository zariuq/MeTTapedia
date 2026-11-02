import Mettapedia.GSLT.LanguageDef.ModuleFormat.GoldCoreSyntax
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntaxViewLaws
import Mettapedia.GSLT.LanguageDef.ModuleFormat.ScalarSyntaxPrinting
import Mettapedia.GSLT.LanguageDef.ModuleSource.ComputedViews
import Mettapedia.GSLT.Parsing.GrammarArgumentLayoutLaws

/-! Closed views of the three actual source grammar/profile replies.
Each equality is kernel checked against its authored module. The shared
source-syntax construction and printer are instantiated with finite
declaration facts, without assuming any language's runtime semantics. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.GoldCoreSyntaxViews

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.Parsing ParserProfileSemantics GrammarArgumentLayout
open ScalarSyntaxCore
open scoped Mettapedia.GSLT.LanguageDef.ModuleSource.ComputedViews

private instance : DecidableEq LanguageDef := fun first second => by
  cases first
  cases second
  exact decidable_of_iff' _ (Iff.of_eq (LanguageDef.mk.injEq _ _ _ _ _ _ _ _ _ _))

def profile : ParserProfileLayer := module_profile_view% (GoldCoreSyntax.OCaml.description?.map (·.profile))
def ocamlGrammar : LanguageDef := module_language_view% (GoldCoreSyntax.OCaml.description?.map (·.grammar))
def maudeGrammar : LanguageDef := module_language_view% (GoldCoreSyntax.Maude.description?.map (·.grammar))
def erlangGrammar : LanguageDef := module_language_view% (GoldCoreSyntax.Erlang.description?.map (·.grammar))

theorem ocaml_description_exact : GoldCoreSyntax.OCaml.description? = some ⟨ocamlGrammar, profile⟩ := by
  apply SourceSyntax.description_of_views
  · change GoldCoreSyntax.OCaml.Syntax.language.toOption = some ocamlGrammar
    decide +kernel
  · apply SourceSyntax.lexicalReply_of_payload
    decide +kernel

theorem maude_description_exact : GoldCoreSyntax.Maude.description? = some ⟨maudeGrammar, profile⟩ := by
  apply SourceSyntax.description_of_views
  · change GoldCoreSyntax.Maude.Syntax.language.toOption = some maudeGrammar
    decide +kernel
  · apply SourceSyntax.lexicalReply_of_payload
    decide +kernel

theorem erlang_description_exact : GoldCoreSyntax.Erlang.description? = some ⟨erlangGrammar, profile⟩ := by
  apply SourceSyntax.description_of_views
  · change GoldCoreSyntax.Erlang.Syntax.language.toOption = some erlangGrammar
    decide +kernel
  · apply SourceSyntax.lexicalReply_of_payload
    decide +kernel

theorem ocaml_grammar_exact : GoldCoreSyntax.OCaml.description?.map (·.grammar) = some ocamlGrammar := by
  rw [ocaml_description_exact]; rfl
theorem maude_grammar_exact : GoldCoreSyntax.Maude.description?.map (·.grammar) = some maudeGrammar := by
  rw [maude_description_exact]; rfl
theorem erlang_grammar_exact : GoldCoreSyntax.Erlang.description?.map (·.grammar) = some erlangGrammar := by
  rw [erlang_description_exact]; rfl
theorem ocaml_profile_exact : GoldCoreSyntax.OCaml.description?.map (·.profile) = some profile := by
  rw [ocaml_description_exact]; rfl
theorem maude_profile_exact : GoldCoreSyntax.Maude.description?.map (·.profile) = some profile := by
  rw [maude_description_exact]; rfl
theorem erlang_profile_exact : GoldCoreSyntax.Erlang.description?.map (·.profile) = some profile := by
  rw [erlang_description_exact]; rfl

def ocaml : Description := ⟨ocamlGrammar, profile, "source-scalar:"⟩
def maude : Description := ⟨maudeGrammar, profile, "source-scalar:"⟩
def erlang : Description := ⟨erlangGrammar, profile, "source-scalar:"⟩

theorem ocaml_shape : Shape ocaml := by
  have ordered : ∀ row ∈ ocaml.grammar.terms, parameters? row row.syntaxPattern = some row.params := by decide +kernel
  refine ⟨ordered, fun row member => not_bare_of_parameters row (ordered row member), ?_, ?_, ?_, ?_, ?_⟩
  all_goals decide +kernel

theorem maude_shape : Shape maude := by
  have ordered : ∀ row ∈ maude.grammar.terms, parameters? row row.syntaxPattern = some row.params := by decide +kernel
  refine ⟨ordered, fun row member => not_bare_of_parameters row (ordered row member), ?_, ?_, ?_, ?_, ?_⟩
  all_goals decide +kernel

theorem erlang_shape : Shape erlang := by
  have ordered : ∀ row ∈ erlang.grammar.terms, parameters? row row.syntaxPattern = some row.params := by decide +kernel
  refine ⟨ordered, fun row member => not_bare_of_parameters row (ordered row member), ?_, ?_, ?_, ?_, ?_⟩
  all_goals decide +kernel

#guard (language ocaml).validate.isEmpty
#guard (language maude).validate.isEmpty
#guard (language erlang).validate.isEmpty

#print axioms ocaml_grammar_exact
#print axioms maude_grammar_exact
#print axioms erlang_grammar_exact
#print axioms ocaml_profile_exact
#print axioms maude_profile_exact
#print axioms erlang_profile_exact
#print axioms ocaml_description_exact
#print axioms maude_description_exact
#print axioms erlang_description_exact
#print axioms ocaml_shape
#print axioms maude_shape
#print axioms erlang_shape

end Mettapedia.GSLT.LanguageDef.ModuleFormat.GoldCoreSyntaxViews
