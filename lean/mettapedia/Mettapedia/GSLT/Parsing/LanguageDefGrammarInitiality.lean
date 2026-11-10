import Mettapedia.GSLT.Parsing.LanguageDefGrammarAlgebra

/-! # Unique interpretation of the authored structural constructors

Typed construction trees are free on the actual compiled production
occurrences. Once the target carrier and every constructor operation are
given, there is exactly one constructor-preserving interpretation. This is
initiality for the structural signature, before imposing extra equations or
an operational observation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.LanguageDefGrammarAlgebra

open LanguageDefSyntaxCompiler
open Mettapedia.GSLT.LanguageDef.ConstructionProvenance.ManySorted

variable {rules : List CompiledRule} (target : Interpretation rules)

abbrev Reader := (sort : String) → ConstructionTree (syntaxAlgebra rules) sort → target.Carrier sort

def mapArguments (read : Reader target) {sorts : List String} :
    ConstructionArguments (syntaxAlgebra rules) sorts → FamilyList target.Carrier sorts
  | .nil => .nil
  | .cons head tail => .cons (read _ head) (mapArguments read tail)

def PreservesConstructors (read : Reader target) : Prop :=
  ∀ {inputs output} (operation : Operation rules inputs output)
    (arguments : ConstructionArguments (syntaxAlgebra rules) inputs),
      read output (.apply operation arguments) =
        target.operation operation (mapArguments target read arguments)

mutual
  theorem reader_unique (read : Reader target) (preserves : PreservesConstructors target read)
      {sort : String} (tree : ConstructionTree (syntaxAlgebra rules) sort) :
      read sort tree = interpret target tree := by
    match tree with
    | .source impossible => exact Empty.elim impossible
    | .apply operation arguments =>
        rw [preserves operation arguments, arguments_unique read preserves arguments]
        rfl
    termination_by structural tree

  theorem arguments_unique (read : Reader target) (preserves : PreservesConstructors target read)
      {sorts : List String} (arguments : ConstructionArguments (syntaxAlgebra rules) sorts) :
      mapArguments target read arguments = interpretArguments target arguments := by
    match arguments with
    | .nil => rfl
    | .cons head tail =>
        simp only [mapArguments, interpretArguments,
          reader_unique read preserves head, arguments_unique read preserves tail]
        rfl
    termination_by structural arguments
end

theorem map_interpret {sorts : List String}
    (arguments : ConstructionArguments (syntaxAlgebra rules) sorts) :
    mapArguments target (fun _ => interpret target) arguments = interpretArguments target arguments := by
  match arguments with
  | .nil => rfl
  | .cons _ tail =>
      simp only [mapArguments, interpretArguments, map_interpret tail]
      rfl
termination_by structural arguments

theorem interpret_preserves : PreservesConstructors target (fun _ => interpret target) := by
  intro inputs output operation arguments
  simp only [interpret, map_interpret]

/-- Existence and uniqueness are relative to every declared constructor of
the actual signature; the target interpretation is not chosen by initiality. -/
theorem interpretation_exists_unique :
    ∃! read : Reader target, PreservesConstructors target read := by
  refine ⟨fun _ => interpret target, interpret_preserves target, ?_⟩
  intro other laws
  funext sort tree
  exact reader_unique target other laws tree

#print axioms interpretation_exists_unique

end Mettapedia.GSLT.Parsing.LanguageDefGrammarAlgebra
