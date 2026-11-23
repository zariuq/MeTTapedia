import Mettapedia.GSLT.LanguageDef.InferenceChecker
import Mettapedia.Logic.Derivation

/-! Selective compilation of premises of a validated rule application. A native
decision concerns source derivability at that exact judgment. Declining leaves
an ordinary ordered premise. Even if every premise is computed, the original
rule must still instantiate, check its side conditions and issue the conclusion.
The observation compared here is derivability. -/

set_option autoImplicit false
namespace Mettapedia.GSLT.LanguageDef.NativePremiseCompilation

open Mettapedia.OSLF.MeTTaIL.Syntax
open InferenceChecker

abbrev Handler := Pattern → Option Bool

def ValidFor (definition : ValidatedCalculusLanguageDef) (handler : Handler) : Prop :=
  ∀ goal answer, handler goal = some answer →
    (answer = true ↔ Nonempty (Derivation definition goal))

/-- Install a functional decision only for this head and this input tuple.
A call outside the mode remains rule-hosted. A recognized partial function
with no output refutes every proposed result at those inputs. -/
def functional (head : String) (inputs : List Pattern) (run : Unit → Option Pattern) : Handler
  | .apply name args => do
    let out ← args.getLast?
    if name = head ∧ args = inputs ++ [out] then some (decide (run () = some out)) else none
  | _ => none

theorem valid_functional {d : ValidatedCalculusLanguageDef} {head : String} {inputs : List Pattern}
    {run : Unit → Option Pattern} (exactResult : ∀ out, run () = some out ↔
      Nonempty (Derivation d (.apply head (inputs ++ [out])))) : ValidFor d (functional head inputs run) := by
  intro goal answer matched
  cases goal <;> simp only [functional] at matched
  case apply name args =>
    obtain ⟨out, _, ok⟩ := Option.bind_eq_some_iff.mp matched
    split at ok
    · rename_i yes
      obtain ⟨rfl, rfl⟩ := yes
      obtain rfl := Option.some.inj ok
      simpa using exactResult out
    · contradiction
  all_goals contradiction

/-- Keep the first qualified handler's decision. Both may decline. -/
def orElse (first second : Handler) : Handler := fun goal =>
  (first goal).orElse (fun _ => second goal)

theorem valid_orElse {d : ValidatedCalculusLanguageDef} {f g : Handler}
    (hf : ValidFor d f) (hg : ValidFor d g) : ValidFor d (orElse f g) := by
  intro goal b eqn
  cases h : f goal with
  | none => exact hg goal b (by simpa [orElse, h] using eqn)
  | some result =>
    have same : result = b := by simpa [orElse, h] using eqn
    exact same ▸ hf goal result h

def remaining (handler : Handler) (premises : List Pattern) :=
  premises.filter (fun p => (handler p).isNone)

def compile (definition : ValidatedCalculusLanguageDef) (handler : Handler)
    (call : RuleInstance) : Option (List Pattern × Pattern) :=
  match instantiateRule? definition call with
  | none => none
  | some (premises, conclusion) =>
    if premises.all (fun p => handler p != some false) then some (remaining handler premises, conclusion)
    else none

def Rule (definition : ValidatedCalculusLanguageDef) (handler : Handler)
    (premises : List Pattern) (conclusion : Pattern) : Prop :=
  ∃ call, compile definition handler call = some (premises, conclusion)

private theorem compiled_iff {d : ValidatedCalculusLanguageDef} {h : Handler}
    {ps : List Pattern} {g : Pattern} :
    Rule d h ps g ↔ ∃ call original, RuleApplication d call original g ∧
      (∀ p ∈ original, h p ≠ some false) ∧ ps = remaining h original := by
  constructor
  · rintro ⟨call, ok⟩
    unfold compile at ok
    cases hi : instantiateRule? d call with
    | none => simp [hi] at ok
    | some pair =>
      rcases pair with ⟨original, goal⟩
      simp [hi] at ok
      obtain ⟨all, rfl, rfl⟩ := ok
      exact ⟨call, original, instantiateRule?_eq_some_iff_application.mp hi, all, rfl⟩
  · rintro ⟨call, original, applies, all, rfl⟩
    have allowed : original.all (fun p => h p != some false) = true := by simpa using all
    exact ⟨call, by simp [compile, instantiateRule?_eq_some_iff_application.mpr applies, allowed]⟩

private theorem children {d : ValidatedCalculusLanguageDef} (ps : List Pattern)
    (each : ∀ p ∈ ps, Nonempty (Derivation d p)) : Nonempty (DerivationList d ps) := by
  induction ps with
  | nil => exact ⟨.nil⟩
  | cons p ps ih =>
    obtain ⟨first⟩ := each p (by simp)
    obtain ⟨rest⟩ := ih (fun q mem => each q (by simp [mem]))
    exact ⟨.cons first rest⟩

/-- Finite derivations with any mixture of specialized and ordinary premises
derive exactly the original judgments, even for recursive catalogs. -/
theorem derives_iff {d : ValidatedCalculusLanguageDef} {h : Handler}
    (licensed : ValidFor d h) (goal : Pattern) :
    Mettapedia.Logic.Derives (Rule d h) goal ↔ Nonempty (Derivation d goal) := by
  constructor
  · intro proof
    apply Mettapedia.Logic.Derives.least (fun g => Nonempty (Derivation d g)) _ proof
    intro ps g compiled known
    obtain ⟨call, original, applies, all, rfl⟩ := compiled_iff.mp compiled
    obtain ⟨subtrees⟩ := children original (d := d) (by
      intro p member
      cases answer : h p with
      | none => exact known p (by simp [remaining, member, answer])
      | some b =>
        cases b with
        | false => exact False.elim (all p member answer)
        | true => exact (licensed p true answer).mp rfl)
    exact ⟨.byRule call applies subtrees⟩
  · rintro ⟨proof⟩
    apply (Derivation.sound_of_ruleApplications (fun g =>
      Nonempty (Derivation d g) ∧ Mettapedia.Logic.Derives (Rule d h) g) _ proof).2
    intro call ps g applies ih
    obtain ⟨subtrees⟩ := children ps (fun p mem => (ih p mem).1)
    refine ⟨⟨.byRule call applies subtrees⟩, .node (remaining h ps) g
      (compiled_iff.mpr ⟨call, ps, applies, ?_, rfl⟩) ?_⟩
    · intro p mem denied
      exact Bool.noConfusion ((licensed p false denied).mpr (ih p mem).1)
    · intro p mem
      exact (ih p (List.mem_filter.mp mem).1).2

end Mettapedia.GSLT.LanguageDef.NativePremiseCompilation
