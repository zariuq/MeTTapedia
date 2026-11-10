import Mettapedia.OSLF.Framework.GrammarDerives
import Mathlib.Logic.Embedding.Basic

/-! # Occurrence-preserving inclusions of authored grammar rows

An inclusion names the target position of every source row and retains the
whole row, including its parameter order and syntax. It preserves derivations;
adding productions need not reflect them. Operational reflection is a separate
obligation of an interpreted language extension.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.LanguageDefGrammarEmbedding

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.GrammarDerives

structure Embedding (source target : LanguageDef) where
  index : Fin source.terms.length ↪ Fin target.terms.length
  row : ∀ i, target.terms.get (index i) = source.terms.get i

namespace Embedding

variable {source target : LanguageDef} (embedding : Embedding source target)
include embedding

theorem mem {rule : GrammarRule} (member : rule ∈ source.terms) : rule ∈ target.terms := by
  obtain ⟨index, selected⟩ := List.mem_iff_get.mp member
  have present := List.get_mem target.terms (embedding.index index)
  rw [embedding.row, selected] at present
  exact present

/-- Preserve the exact authored tree and token sequence. The explicit index
map separately records which production occurrence the embedding uses. -/
theorem derives {sort : String} {tokens : List String} {tree : Pattern}
    (sourceDerivation : Derives source sort tokens tree) : Derives target sort tokens tree := by
  induction sourceDerivation using Derives.rec
      (motive_2 := fun rule items tokens children _ =>
        DerivesItems target rule items tokens children) with
  | rule rule member sort same tokens children _ ih =>
      exact .rule rule (embedding.mem member) sort same tokens children ih
  | nil rule => exact .nil rule
  | terminal rule token items tokens children _ ih =>
      exact .terminal rule token items tokens children ih
  | nonTerminal rule name sort lookup first tree _ items tokens children _ ihHead ihRest =>
      exact .nonTerminal rule name sort lookup first tree ihHead items tokens children ihRest

theorem distinct_rows {first second : Fin source.terms.length} (different : first ≠ second) :
    embedding.index first ≠ embedding.index second :=
  fun same => different (embedding.index.injective same)

end Embedding

end Mettapedia.GSLT.Parsing.LanguageDefGrammarEmbedding
