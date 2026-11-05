import Mettapedia.GSLT.LanguageDef.DecidableRelations.Membership

/-!
# Composing complemented relations

**Privacy survives joins** (`private_join`). A language holding a signature's equality and disequality privately,
joined with rules that do not apply to those judgments, still holds them privately. So equality stays complemented in the
join (`equality_complemented_join`).

**The generated rules grow with the signature** (`disequalityRules_subset`). A signature's rules are among those of
any signature containing it.

**Joining the parts is not enough.** Take the rules generated for `[A]` and those generated for `[B]`, joined: they
derive neither `Equal(A, B)` nor `Unequal(A, B)`, so equality is not complemented there (`parts_not_complemented`). The rules
generated for the joined signature `[A, B]` decide it (`whole_unequal`). Complements are generated over the final
signature: composition is a join followed by a closure.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DecidableRelations

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.OSLF.MeTTaIL.MatchSpec

/-- **Two languages joined**: their sorts, constructors, equations and rewrites, the first's before the second's. -/
def join (first second : LanguageDef) : LanguageDef :=
  ⟨first.name, first.types ++ second.types, first.terms ++ second.terms, first.equations ++ second.equations,
    first.rewrites ++ second.rewrites⟩

/-- **Privacy survives joins** with rules that do not apply to equality and disequality judgments. -/
theorem private_join {first second : LanguageDef} {signature : List (String × Nat)}
    (privacy : Private first signature)
    (apart : ∀ rule ∈ second.rewrites, rule ∉ disequalityRules signature → ∀ arguments,
      matchPattern rule.left (.apply equalJudgment arguments) = [] ∧
        matchPattern rule.left (.apply unequalJudgment arguments) = []) :
    Private (join first second) signature := by
  intro rule member notGenerated arguments
  rcases List.mem_append.mp member with inFirst | inSecond
  · exact privacy rule inFirst notGenerated arguments
  · exact apart rule inSecond notGenerated arguments

/-- **Equality stays complemented in a join** that keeps it private. -/
theorem equality_complemented_join {relEnv : RelationEnv} {first second : LanguageDef} {signature : List (String × Nat)}
    (rules : ∀ rule ∈ disequalityRules signature, rule ∈ first.rewrites) (privacy : Private first signature)
    (apart : ∀ rule ∈ second.rewrites, rule ∉ disequalityRules signature → ∀ arguments,
      matchPattern rule.left (.apply equalJudgment arguments) = [] ∧
        matchPattern rule.left (.apply unequalJudgment arguments) = [])
    (names : (signature.map Prod.fst).Nodup) :
    Complemented (fun pair : Pattern × Pattern => Derives relEnv (join first second) equalJudgment [pair.1, pair.2])
      (fun pair => Derives relEnv (join first second) unequalJudgment [pair.1, pair.2])
      (fun pair => TermOf signature pair.1 ∧ TermOf signature pair.2) :=
  equality_complemented (fun rule generated => List.mem_append_left _ (rules rule generated)) (private_join privacy apart)
    names

/-- **The generated rules grow with the signature.** -/
theorem disequalityRules_subset {smaller larger : List (String × Nat)} (within : ∀ entry ∈ smaller, entry ∈ larger) :
    ∀ rule ∈ disequalityRules smaller, rule ∈ disequalityRules larger := by
  intro rule member
  rcases mem_disequalityRules member with rfl | ⟨first, firstMember, second, secondMember, different, rfl⟩ |
    ⟨constructor, constructorMember, position, inside, rfl⟩
  · exact List.mem_cons_self ..
  · simp only [disequalityRules, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_filterMap]
    exact .inr (.inl ⟨first, within _ firstMember, second, within _ secondMember, by simp [different]⟩)
  · simp only [disequalityRules, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
    exact .inr (.inr ⟨constructor, within _ constructorMember, position, inside, rfl⟩)

/-! ## Joining the parts is not enough -/

namespace Parts

/-- The rules generated for `[A]` and for `[B]`, joined. -/
def joined : LanguageDef := ⟨"Parts", [], [], [], disequalityRules [("A", 0)] ++ disequalityRules [("B", 0)]⟩

/-- The rules generated for the joined signature `[A, B]`. -/
def whole : LanguageDef := ⟨"Whole", [], [], [], disequalityRules [("A", 0), ("B", 0)]⟩

def a : Pattern := .apply "A" []
def b : Pattern := .apply "B" []

/-- The joined parts hold only the equality rule, twice. -/
theorem joined_rules : joined.rewrites = [equalRule, equalRule] := by
  simp [joined, disequalityRules]

/-- **The joined parts do not derive `Unequal(A, B)`**: no rule of theirs applies to it. -/
theorem not_unequal : ¬ Derives RelationEnv.empty joined unequalJudgment [a, b] := by
  rintro ⟨witness, step⟩
  obtain ⟨rule, member, _, _, _, matched, _⟩ := stepValid_yes_cases step
  rw [joined_rules] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at member
  subst member
  simp [equalRule, matchPattern, equalJudgment, unequalJudgment] at matched

/-- The joined parts do not derive `Equal(A, B)` either. -/
theorem not_equal : ¬ Derives RelationEnv.empty joined equalJudgment [a, b] := by
  rintro ⟨witness, step⟩
  obtain ⟨rule, member, _, _, _, matched, _⟩ := stepValid_yes_cases step
  rw [joined_rules] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at member
  subst member
  have correct := matchPattern_correct matched (by simp [equalRule, Pattern.isMatchCorrect, isMatchCorrectAux,
    isMatchCorrectListAux])
  simp only [equalRule, applyBindings, List.map_cons, List.map_nil, Pattern.apply.injEq, List.cons.injEq, true_and,
    and_true, a, b] at correct
  exact absurd (correct.1.symm.trans correct.2) (by simp)

/-- **So equality is not complemented by the joined parts**, on the joined signature's terms. -/
theorem parts_not_complemented :
    ¬ Complemented (fun pair : Pattern × Pattern => Derives RelationEnv.empty joined equalJudgment [pair.1, pair.2])
      (fun pair => Derives RelationEnv.empty joined unequalJudgment [pair.1, pair.2])
      (fun pair => TermOf [("A", 0), ("B", 0)] pair.1 ∧ TermOf [("A", 0), ("B", 0)] pair.2) := by
  intro complemented
  rcases complemented.exhaustive (a, b) ⟨.apply (by simp) (by simp), .apply (by simp) (by simp)⟩ with equal | unequal
  · exact not_equal equal
  · exact not_unequal unequal

/-- **The rules generated for the joined signature derive `Unequal(A, B)`.** -/
theorem whole_unequal : Derives RelationEnv.empty whole unequalJudgment [a, b] :=
  (derives_unequal_iff (fun _ member => member) (fun _ member notGenerated => absurd member notGenerated)
    (by decide) (.apply (by simp) (by simp)) (.apply (by simp) (by simp))).mpr (by simp)

end Parts

end Mettapedia.GSLT.LanguageDef.DecidableRelations
