import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Spatial

/-!
# Substitutability on finite programs of the fragment

For a finite program of the positive fragment over ground rows, two configurations with trivial knowledge have
the same generated barbed types exactly when they are bisimilar (`substitutability`).

**The observation.** A *row barb* `barb t` is the generated formula "some part of the store is exactly the store
`{t}`", the spatial former of the union of stores applied to the singleton type of the store `{t}` and to `⊤`
(`sat_barb_iff`: it holds exactly when a row `t` is present). The *barbed types* (`Barbed`) are the generated
formulas built from row barbs and their negations with `⊤`, `⊥`, `∧`, `∨` and the generated possibility and
necessity over every step. The bisimilarity is strong bisimilarity of the step of the program, as a system of the
tree's Hennessy–Milner library, observing row barbs (`barbs`).

**What is the existing theorem and what is new.** `substitutability` is the tree's Hennessy–Milner theorem for the
step of a program, `ProgramAdequacy.program_adequacy` (finite programs, observations invariant under renaming, a
supply of fresh identities), transported through a translation of its formulas: each Hennessy–Milner formula has a
barbed type that holds at the store of a configuration exactly where the formula holds at the configuration
(`translate_sat`), and each barbed type is such a formula (`back_sat`). The barbed types are Hennessy–Milner
formulas written in the generated logic. What is new here is only that the observation and the modality are the
generated logic's own: a row barb is a generated formula with the meaning of a barb (`sat_barb_iff`;
`Controls.barbed_generated`), and the possibility steps are the generated possibility
(`sat_possibly_storeOf_iff`, the generated logic's form of `Possibility.generated_possibility_iff`).

**Not closed under contexts.** The bisimilarity here observes a configuration alone. The tree's theorem for token
nets, `TokenNets.saturated_iff_nativeTypes`, characterizes saturated bisimilarity against every environment of
tokens by context-labelled generated types; no such context-closed form is proved here, for nets with read arcs
or otherwise.

**How it differs from the substitutability theorem of operational semantics in logical form.** That theorem
relates barbed bisimilarity, with barbs on names and closure under contexts, to equality of all generated types. Here the barbs are rows, the bisimilarity is the
closed strong one with no context, the types are a named fragment of the generated formulas, and the programs are
finite and ground. All the generated formulas together are finer: a singleton type tells apart stores that
differ only in how many copies of a row they hold (the tree's `Equivalence.agree_iff_objectEquivalent`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic
  (Formula Env referenceStructure IsState ObjectEquivalent sat_respects_equivalent)
open NamesOnTheStep (Expr)
open NamesOnTheStep.IssuingControls (ground)
open LogicOverTheStep.ProgramAdequacy (program program_adequacy Supply Keeps renameConf)
open LogicOverTheStep.StepSpan (Succ stepSystem)
open OneFrame (bodies)

universe uO

variable {R : Reading} {rules : List (Rule Rows)} {relEnv : RelationEnv}

/-! ## Row barbs -/

/-- **A row barb**: some part of the store is exactly the store of the row. -/
def barb (t : Expr) : Formula 0 := .split .hashBag (.is (storeCode [t])) .top

/-- **A row barb holds at a store exactly when the row is present.** -/
theorem sat_barb_iff (t : Expr) (rows : List Expr) :
    (referenceStructure relEnv (presentWith R rules)).sat Env.closed (barb t) (storeCode rows) ↔ t ∈ rows := by
  refine (sat_split_iff _ _ rows).trans ?_
  constructor
  · rintro ⟨left, right, perm, named, -⟩
    obtain ⟨others, same, leftPerm⟩ := storeCode_of_objectEquivalent named.2
    obtain rfl : others = [t] := (storeCode_injective same).symm
    rw [List.perm_singleton.mp leftPerm] at perm
    exact perm.subset (List.mem_append_left _ (List.mem_singleton_self t))
  · intro member
    exact ⟨[t], rows.erase t, (List.perm_cons_erase member).symm, ⟨(isState_storeCode _).2, Relation.EqvGen.refl _⟩,
      trivial⟩

/-- **The barbed types**: row barbs and their negations, closed under `⊤`, `⊥`, `∧`, `∨` and the generated
possibility and necessity over every step. -/
inductive Barbed : Formula 0 → Prop
  | top : Barbed .top
  | bot : Barbed .bot
  | and {left right : Formula 0} : Barbed left → Barbed right → Barbed (.and left right)
  | or {left right : Formula 0} : Barbed left → Barbed right → Barbed (.or left right)
  | possibly {inner : Formula 0} : Barbed inner → Barbed (.possibly .any inner)
  | necessarily {inner : Formula 0} : Barbed inner → Barbed (.necessarily .any inner)
  | row (t : Expr) : Barbed (barb t)
  | noRow (t : Expr) : Barbed (barb t).dual

/-- The barbed types are closed under the dual. -/
theorem Barbed.dual {φ : Formula 0} (barbed : Barbed φ) : Barbed φ.dual := by
  induction barbed with
  | top => exact .bot
  | bot => exact .top
  | and _ _ left right => exact .or left right
  | or _ _ left right => exact .and left right
  | possibly _ inner => exact .necessarily inner
  | necessarily _ inner => exact .possibly inner
  | row t => exact .noRow t
  | noRow t =>
      rw [Formula.dual_dual]
      exact .row t

/-! ## The observation on the step -/

section Step

variable {O : Type uO} [DecidableEq O] (label : O → Expr)

/-- **Row barbs on configurations**: a row is present. -/
def barbs (t : Expr) (C : Configuration Expr O) : Prop := t ∈ bagOf label C

omit [DecidableEq O] in
/-- Row barbs read labels only. -/
theorem barbs_invariant (t : Expr) (π : Equiv.Perm O) (C : Configuration Expr O) (keeps : Keeps label π) :
    barbs label t (renameConf π C) ↔ barbs label t C := by
  have same : label ∘ ⇑π.toEmbedding = label := funext keeps
  simp only [barbs, bagOf, renameConf, Finset.map_val, Multiset.map_map, same]

omit [DecidableEq O] in
theorem sat_barb_storeOf (t : Expr) (C : Configuration Expr O) :
    (referenceStructure relEnv (presentWith R rules)).sat Env.closed (barb t) (storeOf label C) ↔
      barbs label t C := by
  refine (sat_barb_iff t _).trans ?_
  rw [barbs, ← coe_rows label C, Multiset.mem_coe]

/-- **The generated logic's possibility at the store of a configuration is the firing possibility**: the form
of `Possibility.generated_possibility_iff` for the generated logic of the presented language. -/
theorem sat_possibly_storeOf_iff (supply : Supply label) (positive : ∀ r ∈ rules, Positive r)
    {C : Configuration Expr O} (knowledge : Trivial C.equations) (A : Formula 0) :
    (referenceStructure relEnv (present rules)).sat Env.closed (.possibly .any A) (storeOf label C) ↔
      ∃ C', Succ (program ground label (bodies {r | r ∈ rules})) C C' ∧
        (referenceStructure relEnv (present rules)).sat Env.closed A (storeOf label C') := by
  refine (sat_possibly_iff A _).trans ?_
  constructor
  · rintro ⟨r, member, holds, rest, split, satisfied⟩
    have bag : ((consumes r : List Expr) : Multiset Expr) + (rest : Multiset Expr) = bagOf label C := by
      rw [Multiset.coe_add, ← coe_rows label C]
      exact Multiset.coe_eq_coe.mpr split
    obtain ⟨C', step, after⟩ := succ_of_bag label supply member (positive r member) holds knowledge bag
    refine ⟨C', step, (sat_respects_equivalent relEnv _ A (isState_storeCode _) (isState_storeCode _) ?_).mp
      satisfied⟩
    refine objectEquivalent_of_perm (Multiset.coe_eq_coe.mp ?_)
    rw [← Multiset.coe_add, coe_rows, after]
    rfl
  · rintro ⟨C', step, satisfied⟩
    obtain ⟨r, member, holds, rest, before, after, -⟩ := succ_bag label step
    have before' : ((standard.consumed r : List Expr) : Multiset Expr) + rest = bagOf label C := before
    have after' : bagOf label C' = ((standard.yielded r : List Expr) : Multiset Expr) + rest := after
    refine ⟨r, member, holds, rest.toList, ?_,
      (sat_respects_equivalent relEnv _ A (isState_storeCode _) (isState_storeCode _) ?_).mpr satisfied⟩
    · refine Multiset.coe_eq_coe.mp ?_
      rw [← Multiset.coe_add, Multiset.coe_toList, before', coe_rows]
    · refine objectEquivalent_of_perm (Multiset.coe_eq_coe.mp ?_)
      rw [← Multiset.coe_add, Multiset.coe_toList, coe_rows, after']

/-! ## Hennessy–Milner formulas and barbed types -/

/-- **A Hennessy–Milner formula as a barbed type**: atoms are row barbs, negation is the dual, and the diamond is
the generated possibility. -/
def translate : Mettapedia.GSLT.HennessyMilner.Formula Expr Unit → Formula 0
  | .top => .top
  | .atom t => barb t
  | .conj left right => .and (translate left) (translate right)
  | .neg inner => (translate inner).dual
  | .dia _ inner => .possibly .any (translate inner)

theorem translate_barbed : ∀ φ : Mettapedia.GSLT.HennessyMilner.Formula Expr Unit, Barbed (translate φ)
  | .top => .top
  | .atom t => .row t
  | .conj left right => .and (translate_barbed left) (translate_barbed right)
  | .neg inner => (translate_barbed inner).dual
  | .dia _ inner => .possibly (translate_barbed inner)

variable (supply : Supply label) (positive : ∀ r ∈ rules, Positive r)

include supply positive in
/-- **A formula's barbed type holds at a configuration's store exactly where the formula holds.** -/
theorem translate_sat : ∀ (φ : Mettapedia.GSLT.HennessyMilner.Formula Expr Unit) (C : Configuration Expr O),
    Trivial C.equations →
      ((referenceStructure relEnv (present rules)).sat Env.closed (translate φ) (storeOf label C) ↔
        (stepSystem (program ground label (bodies {r | r ∈ rules})) (barbs label)).sat φ C)
  | .top, _, _ => Iff.rfl
  | .atom t, C, _ => sat_barb_storeOf label t C
  | .conj left right, C, knowledge =>
      and_congr (translate_sat left C knowledge) (translate_sat right C knowledge)
  | .neg inner, C, knowledge =>
      ((referenceStructure relEnv (present rules)).sat_dual_closed (translate inner) _).trans
        (not_congr (translate_sat inner C knowledge))
  | .dia _ inner, C, knowledge => by
      refine (sat_possibly_storeOf_iff label supply positive knowledge _).trans ?_
      constructor
      · rintro ⟨C', step, holds⟩
        obtain ⟨-, -, -, -, -, -, knowledge'⟩ := succ_bag label step
        exact ⟨C', step, (translate_sat inner C' knowledge').mp holds⟩
      · rintro ⟨C', step, holds⟩
        obtain ⟨-, -, -, -, -, -, knowledge'⟩ := succ_bag label step
        exact ⟨C', step, (translate_sat inner C' knowledge').mpr holds⟩

include supply positive in
/-- **Every barbed type is a Hennessy–Milner formula** at the stores of configurations with trivial knowledge. -/
theorem back_sat {φ : Formula 0} (barbed : Barbed φ) :
    ∃ ψ : Mettapedia.GSLT.HennessyMilner.Formula Expr Unit, ∀ C : Configuration Expr O, Trivial C.equations →
      ((referenceStructure relEnv (present rules)).sat Env.closed φ (storeOf label C) ↔
        (stepSystem (program ground label (bodies {r | r ∈ rules})) (barbs label)).sat ψ C) := by
  induction barbed with
  | top => exact ⟨.top, fun _ _ => Iff.rfl⟩
  | bot => exact ⟨.neg .top, fun _ _ => ⟨False.elim, fun refuted => refuted trivial⟩⟩
  | and _ _ left right =>
      obtain ⟨ψl, hl⟩ := left
      obtain ⟨ψr, hr⟩ := right
      exact ⟨.conj ψl ψr, fun C knowledge => and_congr (hl C knowledge) (hr C knowledge)⟩
  | or _ _ left right =>
      obtain ⟨ψl, hl⟩ := left
      obtain ⟨ψr, hr⟩ := right
      refine ⟨.neg (.conj (.neg ψl) (.neg ψr)), fun C knowledge => ?_⟩
      show (_ ∨ _) ↔ ¬ (¬ _ ∧ ¬ _)
      rw [hl C knowledge, hr C knowledge]
      tauto
  | possibly _ inner =>
      obtain ⟨ψ, h⟩ := inner
      refine ⟨.dia () ψ, fun C knowledge => (sat_possibly_storeOf_iff label supply positive knowledge _).trans ?_⟩
      constructor
      · rintro ⟨C', step, holds⟩
        obtain ⟨-, -, -, -, -, -, knowledge'⟩ := succ_bag label step
        exact ⟨C', step, (h C' knowledge').mp holds⟩
      · rintro ⟨C', step, holds⟩
        obtain ⟨-, -, -, -, -, -, knowledge'⟩ := succ_bag label step
        exact ⟨C', step, (h C' knowledge').mpr holds⟩
  | @necessarily inner _ ih =>
      obtain ⟨ψ, h⟩ := ih
      refine ⟨.neg (.dia () (.neg ψ)), fun C knowledge => ?_⟩
      have dualized := (referenceStructure relEnv (present rules)).sat_dual_closed (.possibly .any inner.dual)
        (storeOf label C)
      simp only [Formula.dual, Formula.dual_dual] at dualized
      refine dualized.trans (not_congr ((sat_possibly_storeOf_iff label supply positive knowledge _).trans ?_))
      constructor
      · rintro ⟨C', step, holds⟩
        obtain ⟨-, -, -, -, -, -, knowledge'⟩ := succ_bag label step
        exact ⟨C', step, fun satisfied => ((referenceStructure relEnv (present rules)).sat_dual_closed inner _).mp
          holds ((h C' knowledge').mpr satisfied)⟩
      · rintro ⟨C', step, refuted⟩
        obtain ⟨-, -, -, -, -, -, knowledge'⟩ := succ_bag label step
        exact ⟨C', step, ((referenceStructure relEnv (present rules)).sat_dual_closed inner _).mpr
          fun holds => refuted ((h C' knowledge').mp holds)⟩
  | row t => exact ⟨.atom t, fun C _ => sat_barb_storeOf label t C⟩
  | noRow t =>
      exact ⟨.neg (.atom t), fun C _ =>
        ((referenceStructure relEnv (present rules)).sat_dual_closed (barb t) _).trans
          (not_congr (sat_barb_storeOf label t C))⟩

end Step

/-! ## The theorem -/

theorem bodies_finite (rules : List (Rule Rows)) : (bodies {r | r ∈ rules}).Finite :=
  (List.finite_toSet (rules.map fun r => (r.body : RuleInstance Expr))).subset fun _ ⟨r, member, same⟩ =>
    List.mem_map.mpr ⟨r, member, same⟩

variable {O : Type uO} [DecidableEq O] (label : O → Expr)

/-- **Substitutability**: for a finite program of the positive fragment, two configurations with trivial
knowledge have the same barbed types at their stores exactly when they are bisimilar, observing row barbs. This is
the tree's Hennessy–Milner theorem `program_adequacy` transported by `translate_sat` and `back_sat`; the
bisimilarity is not closed under contexts. -/
theorem substitutability (supply : Supply label) (positive : ∀ r ∈ rules, Positive r)
    {C D : Configuration Expr O} (knowledgeC : Trivial C.equations) (knowledgeD : Trivial D.equations) :
    (∀ φ : Formula 0, Barbed φ →
      ((referenceStructure relEnv (present rules)).sat Env.closed φ (storeOf label C) ↔
        (referenceStructure relEnv (present rules)).sat Env.closed φ (storeOf label D))) ↔
      (stepSystem (program ground label (bodies {r | r ∈ rules})) (barbs label)).Bisimilar C D := by
  rw [← program_adequacy ground label supply (bodies_finite rules) (barbs label) (barbs_invariant label) C D]
  constructor
  · intro agree ψ
    rw [← translate_sat label supply positive ψ C knowledgeC, ← translate_sat label supply positive ψ D knowledgeD]
    exact agree _ (translate_barbed ψ)
  · intro equivalent φ barbed
    obtain ⟨ψ, h⟩ := back_sat label supply positive barbed
    rw [h C knowledgeC, h D knowledgeD]
    exact equivalent ψ

#print axioms sat_barb_iff
#print axioms Barbed.dual
#print axioms barbs_invariant
#print axioms sat_possibly_storeOf_iff
#print axioms translate_sat
#print axioms back_sat
#print axioms bodies_finite
#print axioms substitutability

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation
