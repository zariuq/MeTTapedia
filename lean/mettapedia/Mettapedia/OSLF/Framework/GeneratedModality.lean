import Mettapedia.OSLF.Framework.RedexPosition
import Mettapedia.OSLF.MeTTaIL.ContextualStep

/-!
# The generated rely-possibly modality and its soundness

For a rewrite rule and a choice of redex position, the type-system generator
introduces one modality at the carrier of the chosen subterm:

  `⟨K_j⟩_{x⃗ :: A⃗} B`

read as a rely-possibly specification — under the rely assumptions on `x⃗`,
placing a term into `K_j[-]` takes one step to the rule's right-hand side, which
inhabits `B`.  Its four rules are formation, introduction, step and
elimination; elimination differs from the equation-generated case in supplying
the operational step rather than a full conversion.

## What carries the soundness

The step rule is only meaningful if the generator's decomposition of a
left-hand side into a context and a focus survives instantiation: a rule fires
on *instances* of its left-hand side, so `K_j[t_j]` must still be the
left-hand side after the rely parameters are given values.  That is
`subtermAt_applyBindings` together with `plug_applyBindings` below, and it is
not automatic.  Applying bindings to a `.subst` node eliminates the node, so a
path descending through one does not survive; and applying bindings to a
collection appends the expansion of its rest variable, which preserves the
indices of the authored elements but not those of anything beyond them.
`StablePath` is exactly the condition under which the decomposition commutes
with instantiation, and the rho communication redex satisfies it.
-/

namespace Mettapedia.OSLF.Framework.GeneratedModality

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.RedexPosition

/-! ## Paths that survive instantiation -/

/-- Whether a path descends only through nodes whose children keep their index
when bindings are applied: constructor arguments, binder bodies, and the
authored elements of a collection.  An explicit substitution node is excluded,
because applying bindings eliminates it. -/
def StablePath : Pattern → Position → Bool
  | _, [] => true
  | .apply _ args, i :: rest =>
      match args[i]? with
      | some c => StablePath c rest
      | none => false
  | .lambda _ body, i :: rest =>
      match i with
      | 0 => StablePath body rest
      | _ + 1 => false
  | .multiLambda _ _ body, i :: rest =>
      match i with
      | 0 => StablePath body rest
      | _ + 1 => false
  | .collection _ elements _, i :: rest =>
      match elements[i]? with
      | some c => StablePath c rest
      | none => false
  | _, _ :: _ => false

/-- An index into a list that has an entry is below its length. -/
private theorem lt_length_of_getElem? {α : Type _} {l : List α} {i : Nat} {a : α}
    (h : l[i]? = some a) : i < l.length := by
  by_contra hge
  simp [List.getElem?_eq_none (by omega : l.length ≤ i)] at h

/-- Applying bindings to a collection appends the expansion of its rest
variable, so the authored elements keep their indices. -/
private theorem applyBindings_collection_childAt (bindings : Bindings)
    (ct : CollType) (elements : List Pattern) (restVar : Option String)
    {i : Nat} {child : Pattern} (hget : elements[i]? = some child) :
    childAt (applyBindings bindings (.collection ct elements restVar)) i
      = some (applyBindings bindings child) := by
  have hlt : i < (elements.map (applyBindings bindings)).length := by
    simpa using lt_length_of_getElem? hget
  -- whatever the rest variable expands to, it is appended after the authored
  -- elements, so the index of `child` is untouched
  have key : ∀ (tail : List Pattern) (u : Option String),
      childAt (.collection ct ((elements.map (applyBindings bindings)) ++ tail) u) i
        = some (applyBindings bindings child) := by
    intro tail u
    simp only [childAt, children]
    rw [List.getElem?_append_left hlt]
    simp [List.getElem?_map, hget]
  rw [applyBindings.eq_def]
  dsimp only
  repeat' split
  all_goals exact key _ _

/-- Taking the subterm at a stable path commutes with applying bindings. -/
theorem subtermAt_applyBindings (bindings : Bindings) :
    ∀ (p : Pattern) (pos : Position) (t : Pattern),
      StablePath p pos = true → subtermAt p pos = some t →
      subtermAt (applyBindings bindings p) pos = some (applyBindings bindings t)
  | p, [], t, _, h => by
      have : t = p := by simpa [subtermAt] using h.symm
      subst this; simp [subtermAt]
  | .apply c args, i :: rest, t, hstable, h => by
      rcases hget : args[i]? with _ | child
      · simp [StablePath, hget] at hstable
      · have hrest : subtermAt child rest = some t := by
          simpa [subtermAt, childAt, children, hget] using h
        have hchild : StablePath child rest = true := by
          simpa [StablePath, hget] using hstable
        have hmap : (args.map (applyBindings bindings))[i]? =
            some (applyBindings bindings child) := by
          simp [List.getElem?_map, hget]
        simp [applyBindings, subtermAt, childAt, children, hmap,
          subtermAt_applyBindings bindings child rest t hchild hrest]
  | .lambda nm body, i :: rest, t, hstable, h => by
      match i with
      | 0 =>
          have hrest : subtermAt body rest = some t := by
            simpa [subtermAt, childAt, children] using h
          have hchild : StablePath body rest = true := by
            simpa [StablePath] using hstable
          simp [applyBindings, subtermAt, childAt, children,
            subtermAt_applyBindings bindings body rest t hchild hrest]
      | _ + 1 => simp [StablePath] at hstable
  | .multiLambda n nms body, i :: rest, t, hstable, h => by
      match i with
      | 0 =>
          have hrest : subtermAt body rest = some t := by
            simpa [subtermAt, childAt, children] using h
          have hchild : StablePath body rest = true := by
            simpa [StablePath] using hstable
          simp [applyBindings, subtermAt, childAt, children,
            subtermAt_applyBindings bindings body rest t hchild hrest]
      | _ + 1 => simp [StablePath] at hstable
  | .collection ct elements restVar, i :: rest, t, hstable, h => by
      rcases hget : elements[i]? with _ | child
      · simp [StablePath, hget] at hstable
      · have hrest : subtermAt child rest = some t := by
          simpa [subtermAt, childAt, children, hget] using h
        have hchild : StablePath child rest = true := by
          simpa [StablePath, hget] using hstable
        simp [subtermAt,
          applyBindings_collection_childAt bindings ct elements restVar hget,
          subtermAt_applyBindings bindings child rest t hchild hrest]
  | .bvar _, _ :: _, _, hstable, _ => by simp [StablePath] at hstable
  | .fvar _, _ :: _, _, hstable, _ => by simp [StablePath] at hstable
  | .subst _ _, _ :: _, _, hstable, _ => by simp [StablePath] at hstable

/-- The one-hole context law survives instantiation: an instance of the
left-hand side is still the instantiated context filled with the instantiated
focus. -/
theorem plug_applyBindings (bindings : Bindings) {p t : Pattern} {pos : Position}
    (hstable : StablePath p pos = true) (h : subtermAt p pos = some t) :
    plug (applyBindings bindings p) pos (applyBindings bindings t) =
      some (applyBindings bindings p) :=
  plug_subtermAt (subtermAt_applyBindings bindings p pos t hstable h)

/-! ## The modality -/

/-- An instantiation meets the rely assumptions when every rely parameter it
gives a value to satisfies that parameter's predicate. -/
def RelySatisfied (rule : RewriteRule) (pos : Position)
    (A : String → Pattern → Prop) (bindings : Bindings) : Prop :=
  ∀ x ∈ relyVars rule.left pos, ∀ v : Pattern,
    Bindings.lookup bindings x = some v → A x v

/-- The rule fires on this instantiation: the engine steps the instantiated
left-hand side to the target the engine actually builds from it.

The target is the scope-corrected instance, not the depth-agnostic one.  The
two agree on every rule whose metavariables sit at the same binder depth on
both sides; they differ exactly on a rule that carries a metavariable under a
binder, and there the engine builds the corrected term.  Written the other way
this predicate would be unsatisfiable for such a rule and the modality below
would be vacuously true of everything, which is a worse failure than being
false. -/
def RuleFires (base : BasePremiseEvaluator) (lang : LanguageDef)
    (rule : RewriteRule) (bindings : Bindings) : Prop :=
  Step base lang (applyBindings bindings rule.left)
    (Mettapedia.OSLF.MeTTaIL.Match.applyRuleBindings rule bindings)

/-- The generated rely-possibly modality `⟨K_j⟩_{x⃗ :: A⃗} B`, as a predicate on
terms at the carrier of the chosen subterm.

A term inhabits it when, for every instantiation of the rely parameters meeting
their assumptions on which the rule fires, placing the term into the
instantiated context yields a term that steps to some reduct inhabiting `B`.

**Why the reduct is quantified.**  Taking `B` at the rule's own right-hand side
instance makes the result obligation independent of the term: two terms whose
contexts both step there would inhabit and fail together, and the elimination
rule would be a projection out of a constant rather than a rule about its
inhabitant.  `rhsOnlyRelyPossibly_result_independent_of_term` below states that
defect as a theorem.  A possibility modality's target is existential, and at the
authored focus the reduct *is* the right-hand side instance
(`relyPossibly_step_authored`), so the display's reading is recovered exactly
where it holds and nothing is given up. -/
def RelyPossibly (base : BasePremiseEvaluator) (lang : LanguageDef)
    (rule : RewriteRule) (pos : Position)
    (A : String → Pattern → Prop) (B : Pattern → Prop) (t : Pattern) : Prop :=
  ∀ bindings : Bindings,
    RelySatisfied rule pos A bindings →
    RuleFires base lang rule bindings →
    ∃ source target : Pattern,
      plug (applyBindings bindings rule.left) pos (applyBindings bindings t)
          = some source ∧
        Step base lang source target ∧ B target

/-- **M-FORM.**  The modality depends on the rely predicates only through the
parameters the position actually has: a predicate assigned to a name that is not
a rely parameter cannot change which terms inhabit the modality.

This is an upper bound on dependence and only that.  It does not show any rely
parameter is *needed*, which is the direction that would justify "one slot per
rely parameter" against a smaller family.  The missing statement is that for each
rely parameter there are predicates agreeing off it and a term inhabiting one
modality but not the other; it is not proved here. -/
theorem relyPossibly_congr_relyVars
    {base : BasePremiseEvaluator} {lang : LanguageDef} {rule : RewriteRule}
    {pos : Position} {A A' : String → Pattern → Prop} {B : Pattern → Prop}
    {t : Pattern}
    (hA : ∀ x ∈ relyVars rule.left pos, A x = A' x) :
    RelyPossibly base lang rule pos A B t ↔
      RelyPossibly base lang rule pos A' B t := by
  have hsat : ∀ bindings, RelySatisfied rule pos A bindings ↔
      RelySatisfied rule pos A' bindings := by
    intro bindings
    constructor
    · intro h x hx v hv
      have := h x hx v hv
      rwa [hA x hx] at this
    · intro h x hx v hv
      have := h x hx v hv
      rwa [← hA x hx] at this
  constructor
  · intro h bindings hrely hfires
    exact h bindings ((hsat bindings).2 hrely) hfires
  · intro h bindings hrely hfires
    exact h bindings ((hsat bindings).1 hrely) hfires

/-- **M-INTRO.**  The chosen subterm inhabits the modality whose result
predicate holds of the right-hand side instances.  The step obligation is
discharged by the decomposition surviving instantiation, so this is where
`plug_applyBindings` does its work. -/
theorem relyPossibly_intro
    {base : BasePremiseEvaluator} {lang : LanguageDef} {rule : RewriteRule}
    {pos : Position} {A : String → Pattern → Prop} {B : Pattern → Prop}
    {t : Pattern}
    (hstable : StablePath rule.left pos = true)
    (hfocus : subtermAt rule.left pos = some t)
    (hB : ∀ bindings : Bindings,
      RelySatisfied rule pos A bindings →
      RuleFires base lang rule bindings →
      B (Mettapedia.OSLF.MeTTaIL.Match.applyRuleBindings rule bindings)) :
    RelyPossibly base lang rule pos A B t := by
  intro bindings hrely hfires
  exact ⟨applyBindings bindings rule.left,
    Mettapedia.OSLF.MeTTaIL.Match.applyRuleBindings rule bindings,
    plug_applyBindings bindings hstable hfocus, hfires,
    hB bindings hrely hfires⟩

/-- **M-STEP.**  Under rely assumptions on which the rule fires, the context
filled with the term steps to the right-hand side instance.  Unlike an
equation-generated modality this supplies the operational step, not a
conversion. -/
theorem relyPossibly_step
    {base : BasePremiseEvaluator} {lang : LanguageDef} {rule : RewriteRule}
    {pos : Position} {A : String → Pattern → Prop} {B : Pattern → Prop}
    {t : Pattern} {bindings : Bindings}
    (ht : RelyPossibly base lang rule pos A B t)
    (hrely : RelySatisfied rule pos A bindings)
    (hfires : RuleFires base lang rule bindings) :
    ∃ source target : Pattern,
      plug (applyBindings bindings rule.left) pos (applyBindings bindings t)
          = some source ∧
        Step base lang source target := by
  obtain ⟨source, target, hplug, hstep, _⟩ := ht bindings hrely hfires
  exact ⟨source, target, hplug, hstep⟩

/-- **M-STEP at the authored focus.**  Where the term is the subterm the
position selects, the reduct reached is the rule's own right-hand side
instance.  This needs no inhabitant: it is the rule firing, transported along
the decomposition, and it is the display's reading of the step rule recovered
exactly where that reading is correct. -/
theorem relyPossibly_step_authored
    {base : BasePremiseEvaluator} {lang : LanguageDef} {rule : RewriteRule}
    {pos : Position} {t : Pattern} (bindings : Bindings)
    (hstable : StablePath rule.left pos = true)
    (hfocus : subtermAt rule.left pos = some t)
    (hfires : RuleFires base lang rule bindings) :
    ∃ source : Pattern,
      plug (applyBindings bindings rule.left) pos (applyBindings bindings t)
          = some source ∧
        Step base lang source
          (Mettapedia.OSLF.MeTTaIL.Match.applyRuleBindings rule bindings) :=
  ⟨applyBindings bindings rule.left,
    plug_applyBindings bindings hstable hfocus, hfires⟩

/-- **M-ELIM.**  Under the same assumptions the right-hand side instance
inhabits the result predicate. -/
theorem relyPossibly_elim
    {base : BasePremiseEvaluator} {lang : LanguageDef} {rule : RewriteRule}
    {pos : Position} {A : String → Pattern → Prop} {B : Pattern → Prop}
    {t : Pattern} {bindings : Bindings}
    (ht : RelyPossibly base lang rule pos A B t)
    (hrely : RelySatisfied rule pos A bindings)
    (hfires : RuleFires base lang rule bindings) :
    ∃ target : Pattern, B target ∧
      ∃ source : Pattern,
        plug (applyBindings bindings rule.left) pos (applyBindings bindings t)
            = some source ∧ Step base lang source target := by
  obtain ⟨source, target, hplug, hstep, hB⟩ := ht bindings hrely hfires
  exact ⟨target, hB, source, hplug, hstep⟩

/-- The modality is monotone in its result predicate, as a comprehension over
reducts must be. -/
theorem relyPossibly_mono_result
    {base : BasePremiseEvaluator} {lang : LanguageDef} {rule : RewriteRule}
    {pos : Position} {A : String → Pattern → Prop} {B B' : Pattern → Prop}
    {t : Pattern} (weaker : ∀ q, B q → B' q)
    (ht : RelyPossibly base lang rule pos A B t) :
    RelyPossibly base lang rule pos A B' t := by
  intro bindings hrely hfires
  obtain ⟨source, target, hplug, hstep, hB⟩ := ht bindings hrely hfires
  exact ⟨source, target, hplug, hstep, weaker target hB⟩

/-- **And the result predicate is load-bearing.**  At a predicate satisfied by
no term nothing inhabits the modality, so inhabitation is not a consequence of
the position alone. -/
theorem not_relyPossibly_of_result_empty
    {base : BasePremiseEvaluator} {lang : LanguageDef} {rule : RewriteRule}
    {pos : Position} {A : String → Pattern → Prop} {B : Pattern → Prop}
    {t : Pattern} {bindings : Bindings}
    (empty : ∀ q, ¬ B q)
    (hrely : RelySatisfied rule pos A bindings)
    (hfires : RuleFires base lang rule bindings) :
    ¬ RelyPossibly base lang rule pos A B t := by
  intro ht
  obtain ⟨-, target, -, -, hB⟩ := ht bindings hrely hfires
  exact empty target hB

/-! ## The reading that was rejected, and the reason -/

/-- The reading that takes the result predicate at the rule's own right-hand
side instance. -/
def rhsOnlyRelyPossibly (base : BasePremiseEvaluator) (lang : LanguageDef)
    (rule : RewriteRule) (pos : Position)
    (A : String → Pattern → Prop) (B : Pattern → Prop) (t : Pattern) : Prop :=
  ∀ bindings : Bindings,
    RelySatisfied rule pos A bindings →
    RuleFires base lang rule bindings →
    ∃ source : Pattern,
      plug (applyBindings bindings rule.left) pos (applyBindings bindings t)
          = some source ∧
        Step base lang source
          (Mettapedia.OSLF.MeTTaIL.Match.applyRuleBindings rule bindings) ∧
        B (Mettapedia.OSLF.MeTTaIL.Match.applyRuleBindings rule bindings)

/-- **Why it is not used.**  Its result obligation does not mention the
inhabitant, so it transports unchanged to any other term whose decomposition
survives instantiation.  A modality whose elimination cannot distinguish its own
inhabitants is a conjunction of a term predicate with a constant. -/
theorem rhsOnlyRelyPossibly_result_independent_of_term
    {base : BasePremiseEvaluator} {lang : LanguageDef} {rule : RewriteRule}
    {pos : Position} {A : String → Pattern → Prop} {B : Pattern → Prop}
    {t u : Pattern}
    (ht : rhsOnlyRelyPossibly base lang rule pos A B t)
    (hu : ∀ bindings : Bindings,
      RelySatisfied rule pos A bindings →
      RuleFires base lang rule bindings →
      ∃ source : Pattern,
        plug (applyBindings bindings rule.left) pos (applyBindings bindings u)
            = some source ∧
          Step base lang source
            (Mettapedia.OSLF.MeTTaIL.Match.applyRuleBindings rule bindings)) :
    rhsOnlyRelyPossibly base lang rule pos A B u := by
  intro bindings hrely hfires
  obtain ⟨source, hplug, hstep⟩ := hu bindings hrely hfires
  obtain ⟨-, -, -, hB⟩ := ht bindings hrely hfires
  exact ⟨source, hplug, hstep, hB⟩

/-- It does imply the reading used here, so quantifying the reduct gives up
nothing the display asserts. -/
theorem relyPossibly_of_rhsOnly
    {base : BasePremiseEvaluator} {lang : LanguageDef} {rule : RewriteRule}
    {pos : Position} {A : String → Pattern → Prop} {B : Pattern → Prop}
    {t : Pattern} (ht : rhsOnlyRelyPossibly base lang rule pos A B t) :
    RelyPossibly base lang rule pos A B t := by
  intro bindings hrely hfires
  obtain ⟨source, hplug, hstep, hB⟩ := ht bindings hrely hfires
  exact ⟨source, Mettapedia.OSLF.MeTTaIL.Match.applyRuleBindings rule bindings,
    hplug, hstep, hB⟩

end Mettapedia.OSLF.Framework.GeneratedModality
