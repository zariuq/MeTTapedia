import Mettapedia.Languages.MeTTa.SpaceTheory.AtomEquations
import Mettapedia.Languages.MeTTa.SpaceTheory.NativeVocabulary

/-!
# Why native equation contexts stop at carrier boundaries

The same nullary Pattern can implement either a GroundAtom constructor
or the text in a GroundText field. It has these interpretations *at
different sorts*. Unrestricted contextual closure on the representation
does not know which one it is looking at. The Atom equation view does.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.NativeEquality

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.OSLFCore.Bridge
open Mettapedia.OSLF.MeTTaIL.Syntax (Equation LanguageDef Pattern)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (BasePremiseEvaluator)
open Mettapedia.OSLF.MeTTaIL.DerivedContexts (OneHoleContext)
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.DecidableRelations (FirstOrder)
open Mettapedia.GSLT.LanguageDef.CarrierWellSorted (checkHasType)
open Atoms (Content Preference)

section Controls

private def off : Atom := .grounded (.bool false)
private def on : Atom := .grounded (.bool true)
private def offSpelling : Atom := .symbol "ground-atom-boolean-false-v1"
private def onSpelling : Atom := .symbol "ground-atom-boolean-true-v1"
private def declaration : Atom := (Content.equation .indifferent off on []).syntax

private def palette : Presentation.PresentedSpace :=
  ⟨[declaration], { GroundData.dataLanguage with
    equations := Presentation.aliasEquations (GroundData.encode off) [GroundData.encode on] }⟩

private theorem only_boolean_generator (a b : Atom) :
    AtomEquations.Generator [declaration] a b ↔ a = off ∧ b = on := by
  constructor
  · rintro ⟨pref, second, rest, written, member⟩
    have same := List.mem_singleton.mp written
    cases pref with
    | indifferent =>
      have fields : a = off ∧ second = on ∧ rest = [] := by
        simpa [Content.syntax, Preference.symbol, declaration] using same
      exact ⟨fields.1, by simpa only [fields.2.1, fields.2.2, List.mem_singleton] using member⟩
    | rightward => simp [Content.syntax, Preference.symbol, declaration] at same
    | leftward => simp [Content.syntax, Preference.symbol, declaration] at same
  · rintro ⟨rfl, rfl⟩
    exact ⟨.indifferent, on, [], List.mem_cons_self, List.mem_cons_self⟩

theorem boolean_equation_preserved_in_an_expression (head : Atom) :
    AtomEquations.Equivalent [declaration] (.expression [head, off]) (.expression [head, on]) :=
  AtomEquations.fill_equivalent (.child [head] .hole [])
    (AtomEquations.authored ((only_boolean_generator off on).mpr ⟨rfl, rfl⟩))

theorem boolean_equation_does_not_change_a_symbol_spelling :
    ¬ AtomEquations.Equivalent [declaration] offSpelling onSpelling := by
  have separates := AtomEquations.isolated_scalar (atoms := [declaration]) offSpelling
    (fun args same => by cases same)
    (fun b eq => by rcases (only_boolean_generator _ _).mp eq with ⟨same, _⟩; cases same)
    (fun a eq => by rcases (only_boolean_generator _ _).mp eq with ⟨_, same⟩; cases same)
    onSpelling
  exact fun changed => (show offSpelling ≠ onSpelling by decide) (separates.mp changed)

/-- The raw Pattern quotient identifies two encodings of symbols even
though neither symbol is written in an equation. Restricting all raw
contexts only by typechecking the instantiated side at its position
would not suffice: both of these nullary representations also type as
GroundText. The relevant sort is the one at which the equation was
declared, not every sort that happens to accept its representation. -/
theorem raw_quotient_changes_literal_spelling (base : BasePremiseEvaluator) :
    NativeVocabulary.present .back GroundData.dataLanguage [declaration] = some palette ∧
      EquationEquiv base palette.language (GroundData.encode offSpelling) (GroundData.encode onSpelling) ∧
      checkHasType GroundData.dataLanguage (fun _ => none) [] (GroundData.encode off) (.base "GroundText") = true ∧
      checkHasType GroundData.dataLanguage (fun _ => none) [] (GroundData.encode on) (.base "GroundText") = true := by
  refine ⟨?_, ?_, by decide +kernel, by decide +kernel⟩
  · have shape : Atoms.content declaration = .equation .indifferent off on [] := rfl
    simp [NativeVocabulary.present, NativeVocabulary.parts, shape, NativeVocabulary.contribution,
      Presentation.contributionUsing, GroundData.encodeList, Presentation.assemble, palette,
      GroundData.dataLanguage]
  have offGround : FirstOrder (GroundData.encode off) := by
    rw [off, GroundData.encode]
    exact .apply (by simp)
  have onGround : FirstOrder (GroundData.encode on) := by
    rw [on, GroundData.encode]
    exact .apply (by simp)
  have equalBooleans : EquationEquiv base palette.language (GroundData.encode off) (GroundData.encode on) :=
    Presentation.aliasEquations_connect base palette.language (GroundData.encode off) [GroundData.encode on]
      offGround (by simpa using onGround) (List.Subset.refl _) (by simp) (by simp)
  let literal : OneHoleContext :=
    .apply "ground-atom-symbol-v1" [] (.apply "source-sexpr-atom-v1" [] .hole []) []
  have changed := equationEquiv_fill literal equalBooleans
  unfold literal at changed
  rw [off, on, GroundData.encode, GroundData.encode] at changed
  rw [offSpelling, onSpelling, GroundData.encode, GroundData.encode]
  exact changed

end Controls

end Mettapedia.Languages.MeTTa.SpaceTheory.NativeEquality
