import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.RowCompiler

/-!
# A literal hosted match determines an actual native schema substitution

The environment comes from the existing binder-equation matcher. Its values
need not initially be native terms. Matching a compiled left side against a
scoped native encoding proves that every used slot decodes at that scope.
One decoded environment is used for all occurrences, including repeated
variables. The extra continuation slot is never interpreted as an object
variable. Unused native slots receive an irrelevant fixed term.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.PatternReadback

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open SourceLanguage SourceLanguage.Elaboration
open RuleBuilder

def readEnvironment {slots ambient : Nat} (environment : Fin (slots + 1) → MClosed) :
    Sub Tower.Head slots ambient := fun index =>
  (decodeTm ambient (environment index.castSucc)).getD (.const .anonymous)

theorem read_encoded_slot {slots ambient : Nat} (environment : Fin (slots + 1) → MClosed)
    (index : Fin slots) (term : Tower.Tm ambient)
    (encoded : environment index.castSucc = encodeTm term) :
    readEnvironment environment index = term := by
  simp [readEnvironment, encoded]

theorem encoded_app {ambient : Nat} {left right : MClosed} {term : Tower.Tm ambient}
    (encoded : nodeC "prime-tm-app" [left, right] = encodeTm term) :
    ∃ function argument, term = .app function argument ∧
      left = encodeTm function ∧ right = encodeTm argument := by
  cases term <;> simp_all [DataEmbedding.nodeC_eq_iff]

theorem encoded_refl {ambient : Nat} {subject : MClosed} {term : Tower.Tm ambient}
    (encoded : nodeC "prime-tm-refl" [subject] = encodeTm term) :
    ∃ value, term = .refl value ∧ subject = encodeTm value := by
  cases term <;> simp_all [DataEmbedding.nodeC_eq_iff]

/-- Literal matching supplies the native substitution and its per-used-slot
readback. Neither semantic conversion nor a source reduction is assumed. -/
theorem pattern_reflects {slots : Nat} (pattern : Tower.Tm slots) :
    ∀ {ambient : Nat} (environment : Fin (slots + 1) → MClosed)
      {template : Template (slots + 1)} {term : Tower.Tm ambient},
      RowCompiler.pattern (fun index => slot index.castSucc) pattern = some template →
      materialize environment template = encodeTm term →
      subst (readEnvironment environment) pattern = term ∧
        ∀ index, 0 < AlgebraicSchema.variableMultiplicity index pattern →
          environment index.castSucc = encodeTm (readEnvironment (ambient := ambient) environment index) := by
  induction pattern with
  | var candidate =>
      intro ambient environment template term compiled matched
      cases compiled
      have encoded : environment candidate.castSucc = encodeTm term := by
        simpa only [materialize_slot] using matched
      have decoded := read_encoded_slot environment candidate term encoded
      refine ⟨decoded, ?_⟩
      intro index used
      have same : candidate = index := by
        by_contra different
        simp [AlgebraicSchema.variableMultiplicity, different] at used
      subst index
      rw [decoded]
      exact encoded
  | const name =>
      intro ambient environment template term compiled matched
      cases compiled
      have encoded : encodeTm (.const name : Tower.Tm ambient) = encodeTm term := by
        simpa only [materialize_literal, encodeTm_const] using matched
      exact ⟨encodeTm_injective encoded, fun _ used => False.elim (Nat.not_lt_zero _ used)⟩
  | head head =>
      intro ambient environment template term compiled matched
      cases compiled
      have encoded : encodeTm (.head head : Tower.Tm ambient) = encodeTm term := by
        simpa only [materialize_literal, encodeTm_head] using matched
      exact ⟨encodeTm_injective encoded, fun _ used => False.elim (Nat.not_lt_zero _ used)⟩
  | app function argument ihf iha =>
      intro ambient environment template term compiled matched
      obtain ⟨f, first, rest⟩ := Option.bind_eq_some_iff.mp compiled
      obtain ⟨a, second, last⟩ := Option.bind_eq_some_iff.mp rest
      cases last
      have encoded : nodeC "prime-tm-app" [materialize environment f, materialize environment a] =
          encodeTm term := by
        simpa only [materialize_node, List.map_cons, List.map_nil] using matched
      obtain ⟨actualFunction, actualArgument, rfl, readsFunction, readsArgument⟩ := encoded_app encoded
      obtain ⟨sameFunction, slotsFunction⟩ := ihf environment first readsFunction
      obtain ⟨sameArgument, slotsArgument⟩ := iha environment second readsArgument
      refine ⟨?_, ?_⟩
      · simp only [subst, sameFunction, sameArgument]
      · intro index used
        change 0 < AlgebraicSchema.variableMultiplicity index function +
          AlgebraicSchema.variableMultiplicity index argument at used
        by_cases left : 0 < AlgebraicSchema.variableMultiplicity index function
        · exact slotsFunction index left
        · exact slotsArgument index (by omega)
  | refl subject ih =>
      intro ambient environment template term compiled matched
      obtain ⟨value, found, last⟩ := Option.bind_eq_some_iff.mp compiled
      cases last
      have encoded : nodeC "prime-tm-refl" [materialize environment value] = encodeTm term := by
        simpa only [materialize_node, List.map_cons, List.map_nil] using matched
      obtain ⟨actual, rfl, reads⟩ := encoded_refl encoded
      obtain ⟨same, slots⟩ := ih environment found reads
      exact ⟨congrArg Tm.refl same, slots⟩
  | _ =>
      intro ambient environment template term compiled _
      cases compiled

theorem native_substitution_of_match {slots ambient : Nat} (pattern : Tower.Tm slots)
    (environment : Fin (slots + 1) → MClosed) {template : Template (slots + 1)}
    {term : Tower.Tm ambient}
    (compiled : RowCompiler.pattern (fun index => slot index.castSucc) pattern = some template)
    (matched : materialize environment template = encodeTm term) :
    ∃ substitution : Sub Tower.Head slots ambient,
      subst substitution pattern = term ∧
      ∀ index, 0 < AlgebraicSchema.variableMultiplicity index pattern →
        environment index.castSucc = encodeTm (substitution index) :=
  ⟨readEnvironment environment, pattern_reflects pattern environment compiled matched⟩

section Controls

def repeated : Tower.Tm 1 := .app (.var 0) (.var 0)
def repeatedTemplate : Template 2 := node "prime-tm-app" [slot 0, slot 0]

theorem repeated_compiles :
    RowCompiler.pattern (fun index => slot index.castSucc) repeated = some repeatedTemplate := rfl

theorem repeated_variable_cannot_take_different_terms :
    ¬ ∃ environment : Fin 2 → MClosed,
      materialize environment repeatedTemplate =
        encodeTm (.app (.const .anonymous) (.head .legacyGround) : Tower.Tm 0) := by
  rintro ⟨environment, matched⟩
  obtain ⟨substitution, native, _⟩ :=
    native_substitution_of_match repeated environment repeated_compiles matched
  have parts := Tm.app.inj native
  have impossible : (.const .anonymous : Tower.Tm 0) = .head .legacyGround :=
    parts.1.symm.trans parts.2
  cases impossible

theorem repeated_variable_matches_identical_terms (term : Tower.Tm 0) :
    materialize (fun _ : Fin 2 => encodeTm term) repeatedTemplate = encodeTm (.app term term) := by
  simp [repeatedTemplate, materialize_node]

end Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.PatternReadback

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.PatternReadback.native_substitution_of_match
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.PatternReadback.repeated_variable_cannot_take_different_terms
