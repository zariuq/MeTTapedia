import Mettapedia.OSLF.NativeTypes.Product.Query
import Mettapedia.OSLF.MeTTaIL.CoreReductionRows

/-!
# One core for every reading of a file

The executable reads a `.module` file in one of two ways (`readingOf`):
- as its rows are written (`directReading`), when that is a language with certified forms;
- otherwise as its core (`LanguageDef.toCore`).

Both readings have the file's core:
- the direct reading reduces the rows with named binders as the core reduction does, and keeps the others, which the
  core reduction then reduces in the same signature (`reduce_directReading`);
- the core of a core is itself (`CoreReduction.reduce_reduce`).

So whichever reading the executable answers over, its core is the file's core (`readingOf_core`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Product

open Mettapedia.OSLF.MeTTaIL Syntax CoreReduction

/-- Rows that a first mapping sends to rows with the same image under a second have the same images. -/
theorem mapM_images_eq {α β ε : Type} (first : α → Except ε α) (second : α → Except ε β)
    (same : ∀ row result, first row = .ok result → second result = second row) :
    ∀ (rows results : List α), rows.mapM first = .ok results → results.mapM second = rows.mapM second
  | [], results, mapped => by
      simp only [List.mapM_nil] at mapped
      cases mapped
      rfl
  | row :: rows, results, mapped => by
      simp only [List.mapM_cons] at mapped
      cases head : first row with
      | error problem => simp only [head, bind, Except.bind] at mapped; cases mapped
      | ok result =>
          cases tail : rows.mapM first with
          | error problem => simp only [head, tail, bind, Except.bind] at mapped; cases mapped
          | ok rest =>
              simp only [head, tail, bind, Except.bind, pure, Except.pure] at mapped
              cases mapped
              simp only [List.mapM_cons, same row result head, mapM_images_eq first second same rows rest tail]

/-- A rewrite the direct reading reads has the core of the rewrite written. -/
theorem reduceRewrite_directRow (grammar : LanguageDef) (row result : RewriteRule)
    (read : (if namesBinders row.left row.right row.premises then reduceRewrite grammar row else pure row) =
      .ok result) :
    reduceRewrite grammar result = reduceRewrite grammar row := by
  split at read
  · obtain ⟨spec, declared⟩ := Option.isSome_iff_exists.mp (reduceRewrite_declared grammar read)
    rw [reduceRewrite_of_declared grammar declared, read]
  · cases read
    rfl

/-- An equation the direct reading reads has the core of the equation written. -/
theorem reduceEquation_directRow (grammar : LanguageDef) (row result : Equation)
    (read : (if namesBinders row.left row.right row.premises then reduceEquation grammar row else pure row) =
      .ok result) :
    reduceEquation grammar result = reduceEquation grammar row := by
  split at read
  · obtain ⟨spec, declared⟩ := Option.isSome_iff_exists.mp (reduceEquation_declared grammar read)
    rw [reduceEquation_of_declared grammar declared, read]
  · cases read
    rfl

/-- The direct reading keeps the language's name, sorts and constructors, and reads its rows. -/
theorem directReading_rows {language direct : LanguageDef} (read : directReading language = .ok direct) :
    ∃ equations rewrites,
      language.equations.mapM (fun row =>
          if namesBinders row.left row.right row.premises then reduceEquation (canonicalGrammar language) row
          else pure row) = .ok equations ∧
        language.rewrites.mapM (fun row =>
          if namesBinders row.left row.right row.premises then reduceRewrite (canonicalGrammar language) row
          else pure row) = .ok rewrites ∧
        direct = withRows language equations rewrites := by
  unfold directReading at read
  dsimp only at read
  cases equated : language.equations.mapM (fun row =>
      if namesBinders row.left row.right row.premises then reduceEquation (canonicalGrammar language) row
      else pure row) with
  | error problem => rw [equated] at read; cases read
  | ok equations =>
      cases rewritten : language.rewrites.mapM (fun row =>
          if namesBinders row.left row.right row.premises then reduceRewrite (canonicalGrammar language) row
          else pure row) with
      | error problem => rw [equated, rewritten] at read; cases read
      | ok rewrites =>
          rw [equated, rewritten] at read
          cases read
          exact ⟨equations, rewrites, rfl, rfl, rfl⟩

/-- **The direct reading of a language has its core.** -/
theorem reduce_directReading {language direct : LanguageDef} (read : directReading language = .ok direct) :
    reduce direct = reduce language := by
  obtain ⟨equations, rewrites, equated, rewritten, rfl⟩ := directReading_rows read
  rw [reduce_withRows]
  have sameRewrites := mapM_images_eq _ (reduceRewrite (canonicalGrammar language))
    (reduceRewrite_directRow (canonicalGrammar language)) _ _ rewritten
  have sameEquations := mapM_images_eq _ (reduceEquation (canonicalGrammar language))
    (reduceEquation_directRow (canonicalGrammar language)) _ _ equated
  rw [sameRewrites, sameEquations]
  rfl

/-- What has a core reduces to it. -/
theorem reduce_of_toCore {language : LanguageDef} {core : CoreLanguageDef} (cored : language.toCore = .ok core) :
    reduce language = .ok core.language := by
  unfold LanguageDef.toCore at cored
  cases reduced : reduce language with
  | error problem => simp only [reduced, bind, Except.bind] at cored; cases cored
  | ok result =>
      simp only [reduced, bind, Except.bind] at cored
      split at cored
      · cases cored; rfl
      · cases cored

/-- **Every reading of a file has the file's core**: the executable answers a file over a language whose core is the
file's core. -/
theorem readingOf_core {language reading : LanguageDef} (read : readingOf (.ok language) = .ok reading) :
    reduce reading = reduce language := by
  simp only [readingOf] at read
  have ofCore : (match language.toCore with
      | .ok core => (.ok core.language : Except String LanguageDef)
      | .error problem => .error s!"the language has no core: {repr problem}") = .ok reading →
      reduce reading = reduce language := by
    intro cored
    split at cored
    · rename_i core hasCore
      cases cored
      rw [reduce_of_toCore hasCore]
      exact reduce_reduce (reduce_of_toCore hasCore)
    · cases cored
  split at read
  · rename_i direct directly
    split at read
    · cases read
      exact reduce_directReading directly
    · exact ofCore read
  · exact ofCore read

end Mettapedia.OSLF.NativeTypes.Product
