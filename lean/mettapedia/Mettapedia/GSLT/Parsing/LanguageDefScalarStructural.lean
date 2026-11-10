import Mettapedia.GSLT.Parsing.LanguageDefScalarSequence

/-! # Structural source syntax and its token grammar

For a profile without additional lexical-sort productions, exact scalar
source derivations and the authored token grammar describe the same structural
trees. Terminal spellings are explicit parameters. CST spans remain in the
source witness; the partial projection below forgets only those spans and
rejects lexical leaves. Profiles with lexical-sort productions require their
own leaf interpretation and are not silently identified with this profile.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.LanguageDefScalarStructural

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework
open ParserProfileSemantics PresentationExprSemantics
open ClassAwareParserPackCorrespondence LanguageDefScalarSyntax LanguageDefScalarPrinter

mutual
  def tree? : CST → Option Pattern
    | .terminal _ _ _ => none
    | .node label _ _ children => Pattern.apply label <$> trees? children

  def trees? : List CST → Option (List Pattern)
    | [] => some []
    | first :: rest => do return (← tree? first) :: (← trees? rest)
end

def spell (literalScalars? : String → Option (List Nat)) : List String → Option (List Nat)
  | [] => some []
  | first :: rest => do return (← literalScalars? first) ++ (← spell literalScalars? rest)

theorem spell_append (literalScalars? : String → Option (List Nat)) (first second : List String) :
    spell literalScalars? (first ++ second) = do
      return (← spell literalScalars? first) ++ (← spell literalScalars? second) := by
  induction first with
  | nil => simp [spell]
  | cons token tokens ih =>
      simp only [List.cons_append, spell, ih]
      cases literalScalars? token <;> cases spell literalScalars? tokens <;>
        cases spell literalScalars? second <;> simp [List.append_assoc]

variable {literalScalars? : String → Option (List Nat)} {profile : ParserProfileLayer}
  {language : LanguageDef} {input : List Nat}

mutual
  /-- Forgetting spans recovers an actual derivation of the original rows;
  the recovered token spellings equal the original scalar renderer. -/
  theorem to_tokens (noLexical : profile.states = [])
      {sort : String} {start stop : Nat} {tree : CST}
      (source : DerivesAt literalScalars? profile language input sort start stop tree) :
      ∃ tokens pattern, tree? tree = some pattern ∧
        GrammarDerives.Derives language sort tokens pattern ∧
        spell literalScalars? tokens = some (render source) := by
    match source with
    | .lexical row _ _ =>
        have impossible := row.isLt
        simp only [noLexical, List.length_nil] at impossible
        exact False.elim (Nat.not_lt_zero _ impossible)
    | .structural row body =>
        obtain ⟨tokens, patterns, erased, derived, spelled⟩ := items_to_tokens noLexical body
        refine ⟨tokens, .apply (language.terms.get row).label patterns, ?_,
          .rule _ (List.get_mem _ _) _ rfl _ _ derived, spelled⟩
        simp only [tree?, erased]
        rfl
    termination_by structural source

  theorem items_to_tokens (noLexical : profile.states = [])
      {rule : GrammarRule} {items : List SyntaxItem} {start stop : Nat} {trees : List CST}
      (source : ItemsDeriveAt literalScalars? profile language input rule items start stop trees) :
      ∃ tokens patterns, trees? trees = some patterns ∧
        GrammarDerives.DerivesItems language rule items tokens patterns ∧
        spell literalScalars? tokens = some (renderItems source) := by
    match source with
    | .nil => exact ⟨[], [], rfl, .nil _, rfl⟩
    | .terminal decoded _ rest =>
        obtain ⟨tokens, patterns, erased, derived, spelled⟩ := items_to_tokens noLexical rest
        refine ⟨_ :: tokens, patterns, erased, .terminal _ _ _ _ _ derived, ?_⟩
        simp only [spell, decoded, spelled]
        rfl
    | .nonterminal lookup head rest =>
        obtain ⟨first, pattern, erasedHead, derivedHead, spelledHead⟩ := to_tokens noLexical head
        obtain ⟨tokens, patterns, erasedRest, derivedRest, spelledRest⟩ := items_to_tokens noLexical rest
        refine ⟨first ++ tokens, pattern :: patterns, ?_,
          .nonTerminal _ _ _ lookup _ _ derivedHead _ _ _ derivedRest, ?_⟩
        · simp only [trees?, erasedHead, erasedRest]
          rfl
        · rw [spell_append, spelledHead, spelledRest]
          rfl
    termination_by structural source
end

/-- A whole-input source witness yields tokens spelling precisely that input. -/
theorem full_source_to_tokens (noLexical : profile.states = [])
    {sort : String} {tree : CST}
    (source : DerivesAt literalScalars? profile language input sort 0 input.length tree) :
    ∃ tokens pattern, tree? tree = some pattern ∧
      GrammarDerives.Derives language sort tokens pattern ∧
      spell literalScalars? tokens = some input := by
  obtain ⟨tokens, pattern, erased, derived, spelled⟩ := to_tokens noLexical source
  exact ⟨tokens, pattern, erased, derived, by simpa only [full_source source] using spelled⟩

/-- Any derivation of the token grammar whose spelling occupies the given
scalar interval lifts to source syntax with exactly the same structural tree.
Extra lexical productions do not obstruct this constructive direction. -/
theorem from_tokens {sort : String} {tokens : List String} {pattern : Pattern}
    (derived : GrammarDerives.Derives language sort tokens pattern) :
    ∀ {points : List Nat} {start stop : Nat}, spell literalScalars? tokens = some points →
      ScalarSequenceMatchesAt input points start stop →
      ∃ tree, tree? tree = some pattern ∧
        Nonempty (DerivesAt literalScalars? profile language input sort start stop tree) := by
  induction derived using GrammarDerives.Derives.rec
      (motive_2 := fun rule items tokens patterns _ =>
        ∀ {points : List Nat} {start stop : Nat}, spell literalScalars? tokens = some points →
          ScalarSequenceMatchesAt input points start stop →
          ∃ trees, trees? trees = some patterns ∧
            Nonempty (ItemsDeriveAt literalScalars? profile language input
              rule items start stop trees)) with
  | rule rule member sort same tokens patterns _ ih =>
      intro points start stop spelled matched
      obtain ⟨trees, erased, ⟨source⟩⟩ := ih spelled matched
      obtain ⟨row, rowEq⟩ := List.mem_iff_get.mp member
      subst rule
      subst sort
      refine ⟨.node (language.terms.get row).label start stop trees, ?_,
        ⟨.structural row source⟩⟩
      simp only [tree?, erased]
      rfl
  | nil rule =>
      rename_i points start stop spelled matched
      have empty : points = [] := (Option.some.inj spelled).symm
      subst points
      cases matched
      exact ⟨[], rfl, ⟨.nil⟩⟩
  | terminal rule token rest tokens patterns _ ih =>
      rename_i points start stop spelled matched
      cases decoded : literalScalars? token with
      | none => simp [spell, decoded] at spelled
      | some first =>
          cases suffix : spell literalScalars? tokens with
          | none => simp [spell, decoded, suffix] at spelled
          | some second =>
              have same : first ++ second = points := by
                rw [spell, decoded, suffix] at spelled
                exact Option.some.inj spelled
              subst points
              obtain ⟨middle, ⟨left⟩, ⟨right⟩⟩ := sequence_split matched
              obtain ⟨trees, erased, ⟨source⟩⟩ := ih suffix right
              exact ⟨trees, erased, ⟨.terminal decoded left source⟩⟩
  | nonTerminal rule parameter sort lookup first pattern _ rest tokens patterns _ ihHead ihRest =>
      rename_i points start stop spelled matched
      rw [spell_append] at spelled
      cases headSpelling : spell literalScalars? first with
      | none => simp [headSpelling] at spelled
      | some leftPoints =>
          cases suffix : spell literalScalars? tokens with
          | none => simp [suffix] at spelled
          | some rightPoints =>
              have same : leftPoints ++ rightPoints = points := by
                rw [headSpelling, suffix] at spelled
                exact Option.some.inj spelled
              subst points
              obtain ⟨middle, ⟨left⟩, ⟨right⟩⟩ := sequence_split matched
              obtain ⟨head, erasedHead, ⟨sourceHead⟩⟩ := ihHead headSpelling left
              obtain ⟨trees, erasedRest, ⟨sourceRest⟩⟩ := ihRest suffix right
              refine ⟨head :: trees, ?_, ⟨.nonterminal lookup sourceHead sourceRest⟩⟩
              simp only [trees?, erasedHead, erasedRest]
              rfl

/-- Both directions retain the actual scalar input and the structural AST.
No source parser is assumed correct by definition. -/
theorem full_source_iff_tokens (noLexical : profile.states = [])
    (sort : String) (pattern : Pattern) :
    (∃ tree, tree? tree = some pattern ∧
      Nonempty (DerivesAt literalScalars? profile language input sort 0 input.length tree)) ↔
    ∃ tokens, GrammarDerives.Derives language sort tokens pattern ∧
      spell literalScalars? tokens = some input := by
  constructor
  · rintro ⟨tree, erased, ⟨source⟩⟩
    obtain ⟨tokens, result, erased', derived, spelled⟩ := full_source_to_tokens noLexical source
    have same : result = pattern := Option.some.inj (erased'.symm.trans erased)
    subst result
    exact ⟨tokens, derived, spelled⟩
  · rintro ⟨tokens, derived, spelled⟩
    exact from_tokens derived spelled (sequence_self input)

#print axioms to_tokens
#print axioms from_tokens
#print axioms full_source_iff_tokens

end Mettapedia.GSLT.Parsing.LanguageDefScalarStructural
