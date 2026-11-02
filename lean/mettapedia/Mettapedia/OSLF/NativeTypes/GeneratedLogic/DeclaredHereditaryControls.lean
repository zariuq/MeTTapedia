import Mettapedia.OSLF.NativeTypes.GeneratedLogic.DeclaredReadingControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetDriverControls

/-!
# Controls: the hereditary reading at the front door

The membership language declared over its hereditary terms (`hereditarySets`) and asked through the front door of a
declared language (`askDeclared`), evaluated by the kernel. The set driver answers, and each answer is a theorem about
the declared reading in every relation environment (`askDeclared_sound`).

| formula | set | answer |
|---|---|---|
| some set contains it (`◆⊤`) | `0` | yes |
| some empty set contains it (`◆ empty`) | `0` | no |
| `3` contains it (`◆ is 3`) | `2` | yes |
| every set containing it is nonempty (`■ nonempty`) | `0` | yes |
| at least two members | `2` | yes |
| at least two members | `{0, 0}` | no |
| some set is empty (`∃ Set. empty`) | `2` | yes |
| some set satisfies `⊥` | `2` | no |
| an endless chain of containers (`νX. ◆X`) | `0` | yes |
| a well-founded chain of containers (`μX. ◆X`) | `0` | no |

It answers nothing where the set driver does not serve: a formula with a relation, counting containers (`≥2` steps
back), a term that is not a hereditary set, another language declared over its hereditary terms, and the membership
language at another sort.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.DeclaredReadings.HereditaryControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open SetReadings (membership hfRule pool zero one two three askHereditary)
open SetReadings.SetDriverControls (doubled)

/-- **The membership language over its hereditary terms.** -/
def hereditarySets : DeclaredLanguage := { language := membership, states := .hereditary hfRule.category }

/-! ## Answers -/

theorem zero_contained : askDeclared RelationEnv.empty hereditarySets 0 0 (.sometimeBefore .any .top) zero = some true := by
  decide +kernel

theorem zero_not_in_empty :
    askDeclared RelationEnv.empty hereditarySets 0 0 (.sometimeBefore .any (.empty .hashSet)) zero = some false := by
  decide +kernel

theorem two_in_three : askDeclared RelationEnv.empty hereditarySets 0 0 (.sometimeBefore .any (.is three)) two = some true := by
  decide +kernel

theorem zero_containers_nonempty :
    askDeclared RelationEnv.empty hereditarySets 0 0 (.alwaysBefore .any (.nonEmpty .hashSet)) zero = some true := by
  decide +kernel

theorem two_two_members : askDeclared RelationEnv.empty hereditarySets 0 0 (.atLeast 2 .forward .any .top) two = some true := by
  decide +kernel

theorem doubled_one_member :
    askDeclared RelationEnv.empty hereditarySets 0 0 (.atLeast 2 .forward .any .top) doubled = some false := by
  decide +kernel

theorem some_empty : askDeclared RelationEnv.empty hereditarySets 0 0 (.someOf (.base "Set") (.empty .hashSet)) two = some true := by
  decide +kernel

theorem none_bottom : askDeclared RelationEnv.empty hereditarySets 0 0 (.someOf (.base "Set") .bot) two = some false := by
  decide +kernel

theorem endless_containers : askDeclared RelationEnv.empty hereditarySets 0 0 (.nu (.sometimeBefore .any (.var 0))) zero = some true := by
  decide +kernel

theorem no_least_containers :
    askDeclared RelationEnv.empty hereditarySets 0 0 (.mu (.sometimeBefore .any (.var 0))) zero = some false := by
  decide +kernel

/-! ## Refusals -/

theorem relation_refused : askDeclared RelationEnv.empty hereditarySets 0 0 (.inRelation "R") zero = none := by
  decide +kernel

theorem counting_containers_refused :
    askDeclared RelationEnv.empty hereditarySets 0 0 (.atLeast 2 .backward .any .top) two = none := by
  decide +kernel

theorem atom_refused : askDeclared RelationEnv.empty hereditarySets 0 0 (.possibly .any .top) (.apply "Foo" []) = none := by
  decide +kernel

theorem other_language_refused :
    askDeclared RelationEnv.empty { language := pool, states := .hereditary "Pool" } 0 0 (.sometimeBefore .any .top) zero =
      none := by
  decide +kernel

theorem other_sort_refused :
    askDeclared RelationEnv.empty { language := membership, states := .hereditary "Other" } 0 0
      (.sometimeBefore .any .top) zero = none := by
  decide +kernel

/-! ## What the answers say, in every relation environment -/

/-- **The answer does not depend on the relation environment**: the set driver serves formulas without relations. -/
theorem askDeclared_hereditarySets (relEnv : RelationEnv) {formula : Formula 0}
    (admitted : setDriverAdmits hereditarySets hfRule.category formula = true) (term : Pattern) :
    askDeclared relEnv hereditarySets 0 0 formula term = askHereditary formula term := by
  show (if setDriverAdmits hereditarySets hfRule.category formula then askHereditary formula term else none) = _
  rw [if_pos admitted]

/-- **The hereditary reading, in any relation environment**: some set contains `0`, no empty set does, `3` contains `2`,
`2` has two members and `{0, 0}` has one, and the containers of `0` go on without end but not well-founded. -/
theorem hereditary_verdicts (relEnv : RelationEnv) :
    Holds relEnv hereditarySets (.sometimeBefore .any .top) zero ∧
      ¬ Holds relEnv hereditarySets (.sometimeBefore .any (.empty .hashSet)) zero ∧
      Holds relEnv hereditarySets (.sometimeBefore .any (.is three)) two ∧
      Holds relEnv hereditarySets (.atLeast 2 .forward .any .top) two ∧
      ¬ Holds relEnv hereditarySets (.atLeast 2 .forward .any .top) doubled ∧
      Holds relEnv hereditarySets (.nu (.sometimeBefore .any (.var 0))) zero ∧
      ¬ Holds relEnv hereditarySets (.mu (.sometimeBefore .any (.var 0))) zero := by
  have sound : ∀ {formula : Formula 0} {term : Pattern} {verdict : Bool},
      setDriverAdmits hereditarySets hfRule.category formula = true →
      askDeclared RelationEnv.empty hereditarySets 0 0 formula term = some verdict →
      (verdict = true ↔ Holds relEnv hereditarySets formula term) := fun admitted answered =>
    askDeclared_sound (fun states => by simp [hereditarySets] at states) (formsSuit_none _ _)
      ((askDeclared_hereditarySets relEnv admitted _).trans
        ((askDeclared_hereditarySets RelationEnv.empty admitted _).symm.trans answered))
  exact ⟨(sound (by decide +kernel) zero_contained).mp rfl,
    fun holds => Bool.false_ne_true ((sound (by decide +kernel) zero_not_in_empty).mpr holds),
    (sound (by decide +kernel) two_in_three).mp rfl,
    (sound (by decide +kernel) two_two_members).mp rfl,
    fun holds => Bool.false_ne_true ((sound (by decide +kernel) doubled_one_member).mpr holds),
    (sound (by decide +kernel) endless_containers).mp rfl,
    fun holds => Bool.false_ne_true ((sound (by decide +kernel) no_least_containers).mpr holds)⟩

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.DeclaredReadings.HereditaryControls
