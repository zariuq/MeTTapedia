import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.CommOneFiring

/-!
# Runs of the manuscript's COMM steps as runs of the one-match step

The step is the one-match step of a program at the one frame of patterns, with the five choices stated in
`CommOneFiring`: a bag store, one match, guards asked after the firing's own tells (the comm rules have
none), a fixed set of rules beside the store, one store of knowledge. Here the program is `commRules`,
the comm rules of every redex shape.

A run of the manuscript's COMM steps is read on a bag of components, each component held by one identity:
one COMM takes the two components that are the inputs `for(t <- x)P` and `for(u <- x)Q` of a redex and
puts the dotted continuations in their place at two new identities (`CommOnComponents`), under the side
conditions of `comm_one_firing`. Each such step relates its redex by the manuscript's root COMM, and changes
the bag of components by replacing the two inputs with the two dotted continuations
(`CommOnComponents.manuscript`).

A state of the step **tracks** components (`Tracks`) when every present row reads, at every solution of the
knowledge, as its component; when every row's component is ground, or is the row's own label, whose
variables the state mentions nowhere else; and when the knowledge is consistent. A configuration whose rows
are labelled by components with pairwise distinct variables, apart from a consistent knowledge, tracks them
(`Tracks.of_labels`).

* `comm_tracks`: at a state that tracks its components, one COMM between two of them is one firing of the
  comm program, to a state that tracks the new components.
* `runs_track`: every run of COMM steps on components, from a state that tracks them, is a run of the step
  of the comm program, ending in a state that tracks the final components.

What is not shown: the converse (that every run of the comm program reads as a run of COMM steps), PAR,
EQUIV and REFL beyond the root COMM, and the flattening of a continuation that is a parallel composition
into its own components; both sides keep such a continuation as one component.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.Comm

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.MeTTaIL.Match (Bindings)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus (pFor par pZero nQuote applyDot SC)
open MeTTaOperationsComm (psubst psubst_none psubst_of_pvars_nil pvars patternAction PSubst dotted commRule
  commSelection GroundPrincipal storePVars applyDot_eq)
open MeTTaCalculus.Corrected (pvars_pFor)
open OneFrame (embed)
open MeTTaCalculus.OccurrenceCommits (fire)
open LogicOverTheStep.StepSpan (Succ)

/-! ## Ground continuations -/

/-- A substitution that sends every variable of a pattern to a ground pattern leaves no variable. -/
theorem pvars_psubst_eq_nil {σ : PSubst} {p : Pattern}
    (closes : ∀ x ∈ pvars p, ∃ v, σ x = some v ∧ pvars v = []) : pvars (psubst σ p) = [] := by
  revert closes
  induction p using Pattern.rec
      (motive_2 := fun ps => (∀ x ∈ MeTTaOperationsComm.pvars.pvarsList ps, ∃ v, σ x = some v ∧ pvars v = []) →
        MeTTaOperationsComm.pvars.pvarsList (MeTTaOperationsComm.psubst.psubstList σ ps) = []) with
  | bvar n => intro _; rfl
  | fvar y =>
    intro closes
    obtain ⟨v, found, closed⟩ := closes y (by simp [pvars])
    simp only [psubst, found, Option.getD_some]
    exact closed
  | apply c args ih => intro closes; exact ih closes
  | lambda nm body ih => intro closes; exact ih closes
  | multiLambda n nms body ih => intro closes; exact ih closes
  | subst body repl ihb ihr =>
    intro closes
    show pvars (psubst σ body) ++ pvars (psubst σ repl) = []
    rw [ihb fun x occurs => closes x (List.mem_append_left _ occurs), List.nil_append]
    exact ihr fun x occurs => closes x (List.mem_append_right _ occurs)
  | collection ct elems rest ih => intro closes; exact ih closes
  | nil => rfl
  | cons p ps head tail =>
    rename_i closes
    show pvars (psubst σ p) ++ MeTTaOperationsComm.pvars.pvarsList
      (MeTTaOperationsComm.psubst.psubstList σ ps) = []
    rw [head fun x occurs => closes x (List.mem_append_left _ occurs), List.nil_append]
    exact tail fun x occurs => closes x (List.mem_append_right _ occurs)

/-- **Under a ground principal unifier, a closed first-order continuation dots to a ground pattern.** -/
theorem applyDot_ground {t u : Pattern} {bs : Bindings} (gp : GroundPrincipal t u bs) (P : Pattern)
    (fo : MeTTaOperationsComm.firstOrder P = true) (closed : ∀ x ∈ pvars P, x ∈ pvars t ++ pvars u) :
    pvars (applyDot bs P) = [] := by
  rw [applyDot_eq bs P fo]
  apply pvars_psubst_eq_nil
  intro x occurs
  obtain ⟨v, found, closedV⟩ := gp.covers x (closed x occurs)
  refine ⟨nQuote v, by rw [found, Option.map_some], ?_⟩
  show pvars v ++ [] = []
  rw [List.append_nil]
  exact closedV

/-- The variables of a renamed pattern are the renamed variables. -/
theorem mem_pvars_renameBy {g : String → String} {q : Pattern} {x : String}
    (occurs : x ∈ pvars (psubst (renameBy g) q)) : ∃ y ∈ pvars q, x = g y := by
  rw [show psubst (renameBy g) q = MeTTaCalculus.Corrected.rename g q from rfl,
    MeTTaCalculus.Corrected.pvars_rename] at occurs
  obtain ⟨y, inside, rfl⟩ := List.mem_map.mp occurs
  exact ⟨y, inside, rfl⟩

/-! ## The comm program -/

variable {O : Type*}

/-- **The comm program**: the comm rules of every redex shape. -/
def commRules : Program Tm := {r | ∃ t u channel P Q, r = commSchema t u channel P Q}

/-- The COMM firing as a firing of the comm program. -/
def commFiringIn (t u channel P Q : Pattern) (ρ : PSubst) (first second made₁ made₂ : O) :
    Firing O E commRules PUnit.unit :=
  ⟨commSchema t u channel P Q, ⟨t, u, channel, P, Q, rfl⟩, PUnit.unit, ρ,
    commSelection first second made₁ made₂, []⟩

/-- Every solution of the knowledge after a firing solves the knowledge before it. -/
theorem knowledge_of_information {Prog : Program Tm} (label : O → Pattern) (C : Configuration Pattern O)
    (f : Firing O E Prog PUnit.unit) {σ : PSubst}
    (solved : patternAction.Models σ (f.information X (embed label C))) :
    patternAction.Models σ C.equations := by
  intro e member
  have equation := solved (psubst (fun _ => none) e.1, psubst (fun _ => none) e.2)
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_map_of_mem member))))
  change psubst σ (psubst (fun _ => none) e.1) = psubst σ (psubst (fun _ => none) e.2) at equation
  rw [psubst_none, psubst_none] at equation
  exact equation

/-- The variables of the knowledge after the COMM firing opened by a renaming: the knowledge's, the taken
rows' labels', and renamed variables of the rule. -/
theorem storePVars_comm (label : O → Pattern) (C : Configuration Pattern O) (t u channel P Q : Pattern)
    (g : String → String) (first second made₁ made₂ : O) {x : String}
    (member : x ∈ storePVars ((commFiring t u channel P Q (renameBy g) first second made₁ made₂).information
      X (embed label C))) :
    x ∈ storePVars C.equations ∨ x ∈ pvars (label first) ∨ x ∈ pvars (label second) ∨
      ∃ y ∈ ruleVars (commSchema t u channel P Q), x = g y := by
  have renamed : ∀ q ∈ (commSchema t u channel P Q).terms, x ∈ pvars (psubst (renameBy g) q) →
      ∃ y ∈ ruleVars (commSchema t u channel P Q), x = g y := by
    intro q term occurs
    obtain ⟨y, inside, same⟩ := mem_pvars_renameBy occurs
    exact ⟨y, List.mem_flatMap.mpr ⟨q, term, inside⟩, same⟩
  obtain ⟨e, inside, occurs⟩ := List.mem_flatMap.mp member
  have information : (commFiring t u channel P Q (renameBy g) first second made₁ made₂).information X
      (embed label C) =
      C.equations.map (fun e => (psubst (fun _ => none) e.1, psubst (fun _ => none) e.2)) ++
        [(psubst (renameBy g) (pFor t channel P), psubst (fun _ => none) (label first)),
          (psubst (renameBy g) (pFor u channel Q), psubst (fun _ => none) (label second))] ++ [] ++
        [(psubst (renameBy g) t, psubst (renameBy g) u)] := rfl
  rw [information] at inside
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at inside
  rcases inside with (⟨e', e'In, rfl⟩ | rfl | rfl) | rfl
  · dsimp only at occurs
    rw [psubst_none, psubst_none] at occurs
    exact Or.inl (List.mem_flatMap.mpr ⟨e', e'In, occurs⟩)
  · dsimp only at occurs
    rcases List.mem_append.mp occurs with inPattern | inLabel
    · exact Or.inr (Or.inr (Or.inr (renamed _ (by simp [commSchema, Rule.terms, commRule]) inPattern)))
    · rw [psubst_none] at inLabel
      exact Or.inr (Or.inl inLabel)
  · dsimp only at occurs
    rcases List.mem_append.mp occurs with inPattern | inLabel
    · exact Or.inr (Or.inr (Or.inr (renamed _ (by simp [commSchema, Rule.terms, commRule]) inPattern)))
    · rw [psubst_none] at inLabel
      exact Or.inr (Or.inr (Or.inl inLabel))
  · dsimp only at occurs
    rcases List.mem_append.mp occurs with inT | inU
    · exact Or.inr (Or.inr (Or.inr (renamed _ (by simp [commSchema, Rule.terms, commRule]) inT)))
    · exact Or.inr (Or.inr (Or.inr (renamed _ (by simp [commSchema, Rule.terms, commRule]) inU)))

section Runs

variable [DecidableEq O]

/-! ## States that track components -/

/-- **A state tracks components**: every present row reads, at every solution of the knowledge, as its
component; every row's component is ground, or is the row's own label, whose variables the state mentions
nowhere else; and the knowledge is consistent. -/
structure Tracks (label : O → Pattern) (C : Configuration Pattern O) (comp : O → Pattern) : Prop where
  reads : ∀ o ∈ C.present, ∀ σ : PSubst, patternAction.Models σ C.equations →
    psubst σ (label o) = psubst σ (comp o)
  shape : ∀ o ∈ C.present, pvars (comp o) = [] ∨
    (label o = comp o ∧ ∀ x ∈ pvars (label o), x ∉ storePVars C.equations ∧
      ∀ o' ∈ C.present, o' ≠ o → x ∉ pvars (label o'))
  consistent : patternAction.Consistent C.equations

omit [DecidableEq O] in
/-- **Rows labelled by their components** track them, when each row's variables are apart from a
consistent knowledge and from every other row. -/
theorem Tracks.of_labels (label : O → Pattern) (C : Configuration Pattern O)
    (hidden : ∀ o ∈ C.present, ∀ x ∈ pvars (label o), x ∉ storePVars C.equations ∧
      ∀ o' ∈ C.present, o' ≠ o → x ∉ pvars (label o'))
    (consistent : patternAction.Consistent C.equations) : Tracks label C label :=
  ⟨fun _ _ _ _ => rfl, fun o present => Or.inr ⟨rfl, hidden o present⟩, consistent⟩

omit [DecidableEq O] in
theorem Tracks.apart_of_mem {label : O → Pattern} {C : Configuration Pattern O} {comp : O → Pattern}
    (tracks : Tracks label C comp) {o : O} (present : o ∈ C.present) {x : String}
    (occurs : x ∈ pvars (comp o)) : x ∉ storePVars C.equations := by
  rcases tracks.shape o present with ground | ⟨same, hidden⟩
  · rw [ground] at occurs
    exact absurd occurs List.not_mem_nil
  · rw [← same] at occurs
    exact (hidden x occurs).1

/-- The components after a COMM: the dotted continuations at the made identities. -/
def afterComm (comp : O → Pattern) (made₁ made₂ : O) (left right : Pattern) : O → Pattern :=
  fun o => if o = made₁ then left else if o = made₂ then right else comp o

theorem afterComm_made₁ (comp : O → Pattern) (made₁ made₂ : O) (left right : Pattern) :
    afterComm comp made₁ made₂ left right made₁ = left := by
  show (if made₁ = made₁ then _ else _) = _
  rw [if_pos rfl]

theorem afterComm_made₂ (comp : O → Pattern) {made₁ made₂ : O} (madeDistinct : made₁ ≠ made₂)
    (left right : Pattern) : afterComm comp made₁ made₂ left right made₂ = right := by
  show (if made₂ = made₁ then _ else if made₂ = made₂ then _ else _) = _
  rw [if_neg (Ne.symm madeDistinct), if_pos rfl]

theorem afterComm_other (comp : O → Pattern) {made₁ made₂ o : O} (other₁ : o ≠ made₁) (other₂ : o ≠ made₂)
    (left right : Pattern) : afterComm comp made₁ made₂ left right o = comp o := by
  show (if o = made₁ then _ else if o = made₂ then _ else _) = _
  rw [if_neg other₁, if_neg other₂]

/-! ## One COMM keeps the components tracked -/

/-- **One COMM keeps the components tracked.** At a state that tracks its components, a COMM between two
present rows whose components are the redex's inputs, under the side conditions of `comm_one_firing`, is
one firing of the comm program, to a state whose present rows are the old ones with the inputs replaced by
the made identities, and which tracks the components with the dotted continuations at the made
identities. -/
theorem comm_tracks (label : O → Pattern) (C : Configuration Pattern O) (comp : O → Pattern)
    (tracks : Tracks label C comp) (t u channel P Q : Pattern) (bs : Bindings) (gp : GroundPrincipal t u bs)
    (foP : MeTTaOperationsComm.firstOrder P = true) (foQ : MeTTaOperationsComm.firstOrder Q = true)
    (closedP : ∀ x ∈ pvars P, x ∈ pvars t ++ pvars u) (closedQ : ∀ x ∈ pvars Q, x ∈ pvars t ++ pvars u)
    (first second made₁ made₂ : O)
    (compFirst : comp first = pFor t channel P) (compSecond : comp second = pFor u channel Q)
    (distinct : first ≠ second) (madeDistinct : made₁ ≠ made₂)
    (present₁ : first ∈ C.present) (present₂ : second ∈ C.present)
    (fresh₁ : made₁ ∉ C.present) (fresh₂ : made₂ ∉ C.present) :
    ∃ (label' : O → Pattern) (C' : Configuration Pattern O),
      Succ (RuleSyntax.step X O E commRules).toStep (embed label C) (embed label' C') ∧
        C'.present = (C.present \ {first, second}) ∪ {made₁, made₂} ∧
        Tracks label' C' (afterComm comp made₁ made₂ (applyDot bs P) (applyDot bs Q)) := by
  have readsFirst : ∀ σ : PSubst, patternAction.Models σ C.equations →
      psubst σ (label first) = psubst σ (pFor t channel P) := fun σ known =>
    (tracks.reads first present₁ σ known).trans (by rw [compFirst])
  have readsSecond : ∀ σ : PSubst, patternAction.Models σ C.equations →
      psubst σ (label second) = psubst σ (pFor u channel Q) := fun σ known =>
    (tracks.reads second present₂ σ known).trans (by rw [compSecond])
  have apart : ∀ x ∈ pvars t ++ pvars u, x ∉ storePVars C.equations := by
    intro x inside
    rcases List.mem_append.mp inside with inT | inU
    · exact tracks.apart_of_mem present₁ (by
        rw [compFirst, pvars_pFor]; exact List.mem_append_left _ (List.mem_append_left _ inT))
    · exact tracks.apart_of_mem present₂ (by
        rw [compSecond, pvars_pFor]; exact List.mem_append_left _ (List.mem_append_left _ inU))
  obtain ⟨g, injective, avoids⟩ :=
    exists_apart_renaming (embed label C) (ruleVars (commSchema t u channel P Q))
  have opensFreshly := fresh_of_renaming (embed label C)
    (commFiring t u channel P Q (renameBy g) first second made₁ made₂) g rfl injective avoids
  obtain ⟨admitted, -, readOff⟩ := comm_one_firing_reading label t u channel P Q bs gp foP foQ closedP
    closedQ C first second made₁ made₂ readsFirst readsSecond distinct madeDistinct present₁ present₂ fresh₁
    fresh₂ apart tracks.consistent opensFreshly
  have presentEq : ((commFiring t u channel P Q (renameBy g) first second made₁ made₂).result X
      (embed label C)).present = (C.present \ {first, second}) ∪ {made₁, made₂} := by
    show fire C.present ((commSelection first second made₁ made₂).commit (T := Unit)) = _
    simp [fire, Selection.commit, commSelection]
  have labelOther : ∀ o, o ≠ made₁ → o ≠ made₂ →
      ((commFiring t u channel P Q (renameBy g) first second made₁ made₂).result X
        (embed label C)).label o = label o := by
    intro o other₁ other₂
    have missing : o ∉ (commFiring t u channel P Q (renameBy g) first second made₁ made₂).selection.made := by
      simp [commFiring, commSelection, other₁, other₂]
    exact (Firing.result_label_other (X := X) (s := embed label C) _ missing).trans (psubst_none (label o))
  have groundP := applyDot_ground gp P foP closedP
  have groundQ := applyDot_ground gp Q foQ closedQ
  refine ⟨((commFiring t u channel P Q (renameBy g) first second made₁ made₂).result X (embed label C)).label,
    ⟨((commFiring t u channel P Q (renameBy g) first second made₁ made₂).result X (embed label C)).knowledge,
      ((commFiring t u channel P Q (renameBy g) first second made₁ made₂).result X (embed label C)).present⟩,
    ⟨commFiringIn t u channel P Q (renameBy g) first second made₁ made₂, admitted, rfl⟩, presentEq,
    ⟨?_, ?_, ?_⟩⟩
  · intro o member σ solved
    have known := knowledge_of_information label C _ solved
    change o ∈ ((commFiring t u channel P Q (renameBy g) first second made₁ made₂).result X
      (embed label C)).present at member
    rw [presentEq] at member
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at member
    rcases member with ⟨old, -, -⟩ | rfl | rfl
    · have other₁ := ne_of_present old fresh₁
      have other₂ := ne_of_present old fresh₂
      rw [labelOther o other₁ other₂, afterComm_other comp other₁ other₂]
      exact tracks.reads o old σ known
    · rw [afterComm_made₁, (readOff σ solved).1, psubst_of_pvars_nil σ _ groundP]
    · rw [afterComm_made₂ comp madeDistinct, (readOff σ solved).2, psubst_of_pvars_nil σ _ groundQ]
  · intro o member
    change o ∈ ((commFiring t u channel P Q (renameBy g) first second made₁ made₂).result X
      (embed label C)).present at member
    rw [presentEq] at member
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at member
    rcases member with ⟨old, notFirst, notSecond⟩ | rfl | rfl
    · have other₁ := ne_of_present old fresh₁
      have other₂ := ne_of_present old fresh₂
      rw [afterComm_other comp other₁ other₂]
      rcases tracks.shape o old with ground | ⟨same, hidden⟩
      · exact Or.inl ground
      · refine Or.inr ⟨(labelOther o other₁ other₂).trans same, fun x occurs => ⟨fun inStore => ?_,
          fun o' member' other' occurs' => ?_⟩⟩
        · rw [labelOther o other₁ other₂] at occurs
          rcases storePVars_comm label C t u channel P Q g first second made₁ made₂ inStore with
            old' | inFirst | inSecond | ⟨y, inVars, rfl⟩
          · exact (hidden x occurs).1 old'
          · exact (hidden x occurs).2 first present₁ (fun same => notFirst same.symm) inFirst
          · exact (hidden x occurs).2 second present₂ (fun same => notSecond same.symm) inSecond
          · exact avoids y inVars (label o) (Or.inr (Or.inr ⟨o, old, rfl⟩)) occurs
        · rw [labelOther o other₁ other₂] at occurs
          change o' ∈ ((commFiring t u channel P Q (renameBy g) first second made₁ made₂).result X
            (embed label C)).present at member'
          rw [presentEq] at member'
          simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton,
            not_or] at member'
          rcases member' with ⟨old', -, -⟩ | rfl | rfl
          · rw [labelOther o' (ne_of_present old' fresh₁) (ne_of_present old' fresh₂)] at occurs'
            exact (hidden x occurs).2 o' old' other' occurs'
          · rw [commFiring_label₁] at occurs'
            obtain ⟨y, inside, rfl⟩ := mem_pvars_renameBy occurs'
            exact avoids y (List.mem_flatMap.mpr ⟨_, by simp [commSchema, Rule.terms, commRule], inside⟩)
              (label o) (Or.inr (Or.inr ⟨o, old, rfl⟩)) occurs
          · rw [commFiring_label₂ label C t u channel P Q (renameBy g) first second madeDistinct] at occurs'
            obtain ⟨y, inside, rfl⟩ := mem_pvars_renameBy occurs'
            exact avoids y (List.mem_flatMap.mpr ⟨_, by simp [commSchema, Rule.terms, commRule], inside⟩)
              (label o) (Or.inr (Or.inr ⟨o, old, rfl⟩)) occurs
    · rw [afterComm_made₁]
      exact Or.inl groundP
    · rw [afterComm_made₂ comp madeDistinct]
      exact Or.inl groundQ
  · obtain ⟨_, σ, solved⟩ := ((RuleSyntax.admits_iff _).mp admitted).2.2.2.1
    exact ⟨σ, solved⟩

/-! ## Runs -/

/-- **One COMM on components**, under the side conditions of `comm_one_firing`: the two inputs of a redex,
held by two present identities, are replaced by the dotted continuations at two new identities. -/
inductive CommOnComponents : Finset O × (O → Pattern) → Finset O × (O → Pattern) → Prop
  | comm (present : Finset O) (comp : O → Pattern) (t u channel P Q : Pattern) (bs : Bindings)
      (gp : GroundPrincipal t u bs) (foP : MeTTaOperationsComm.firstOrder P = true)
      (foQ : MeTTaOperationsComm.firstOrder Q = true)
      (closedP : ∀ x ∈ pvars P, x ∈ pvars t ++ pvars u) (closedQ : ∀ x ∈ pvars Q, x ∈ pvars t ++ pvars u)
      (first second made₁ made₂ : O)
      (compFirst : comp first = pFor t channel P) (compSecond : comp second = pFor u channel Q)
      (distinct : first ≠ second) (madeDistinct : made₁ ≠ made₂)
      (present₁ : first ∈ present) (present₂ : second ∈ present)
      (fresh₁ : made₁ ∉ present) (fresh₂ : made₂ ∉ present) :
      CommOnComponents (present, comp)
        ((present \ {first, second}) ∪ {made₁, made₂},
          afterComm comp made₁ made₂ (applyDot bs P) (applyDot bs Q))

/-- **Each COMM on components is the manuscript's root COMM on its redex, and changes the bag of
components by it**: two present components are the redex's inputs, the manuscript's COMM relates the redex
to the dotted continuations, and the bag of components loses the inputs and gains the continuations. -/
theorem CommOnComponents.manuscript {before after : Finset O × (O → Pattern)}
    (step : CommOnComponents before after) :
    ∃ (first second : O) (t u channel P Q : Pattern) (bs : Bindings),
      first ∈ before.1 ∧ second ∈ before.1 ∧ first ≠ second ∧
      before.2 first = pFor t channel P ∧ before.2 second = pFor u channel Q ∧
      MeTTaCalculus.ReflectionClosure.Step GroundPrincipal SC (par (pFor t channel P) (pFor u channel Q))
        (par (applyDot bs P) (applyDot bs Q)) ∧
      after.1.val.map after.2 = before.1.val.map before.2 - {pFor t channel P, pFor u channel Q} +
        {applyDot bs P, applyDot bs Q} := by
  cases step with
  | comm present comp t u channel P Q bs gp _ _ _ _ first second made₁ made₂ compFirst compSecond distinct
      madeDistinct present₁ present₂ fresh₁ fresh₂ =>
    refine ⟨first, second, t, u, channel, P, Q, bs, present₁, present₂, distinct, compFirst, compSecond,
      .comm t u channel P Q bs gp, ?_⟩
    have fireEq : fire present ((commSelection first second made₁ made₂).commit (T := Pattern)) =
        (present \ {first, second}) ∪ {made₁, made₂} := by
      simp [fire, Selection.commit, commSelection]
    have outside : ∀ o ∈ present.val, afterComm comp made₁ made₂ (applyDot bs P) (applyDot bs Q) o = comp o :=
      fun o inside => afterComm_other comp (ne_of_present inside fresh₁) (ne_of_present inside fresh₂) _ _
    dsimp only
    rw [← fireEq, MeTTaCalculus.Corrected.mem_fire_labels _ present first second made₁ made₂ distinct
      madeDistinct present₁ present₂ fresh₁ fresh₂, Multiset.map_congr rfl outside,
      afterComm_other comp (ne_of_present present₁ fresh₁) (ne_of_present present₁ fresh₂),
      afterComm_other comp (ne_of_present present₂ fresh₁) (ne_of_present present₂ fresh₂),
      afterComm_made₁, afterComm_made₂ comp madeDistinct, compFirst, compSecond]

/-- **Runs of COMM steps are runs of the step.** Every run of COMM steps on components, from a state that
tracks the starting components, is a run of the step of the comm program, ending in a state whose present
rows hold the final components and which tracks them. -/
theorem runs_track {start finish : Finset O × (O → Pattern)}
    (run : Relation.ReflTransGen CommOnComponents start finish) (label : O → Pattern)
    (C : Configuration Pattern O) (presentEq : C.present = start.1) (tracks : Tracks label C start.2) :
    ∃ (label' : O → Pattern) (C' : Configuration Pattern O),
      Relation.ReflTransGen (Succ (RuleSyntax.step X O E commRules).toStep) (embed label C) (embed label' C') ∧
        C'.present = finish.1 ∧ Tracks label' C' finish.2 := by
  induction run with
  | refl => exact ⟨label, C, .refl, presentEq, tracks⟩
  | tail _ step ih =>
    obtain ⟨label₁, C₁, firings, present₁Eq, tracks₁⟩ := ih
    cases step with
    | comm present comp t u channel P Q bs gp foP foQ closedP closedQ first second made₁ made₂ compFirst
        compSecond distinct madeDistinct inFirst inSecond fresh₁ fresh₂ =>
      dsimp only at present₁Eq tracks₁ ⊢
      subst present₁Eq
      obtain ⟨label₂, C₂, succ, present₂Eq, tracks₂⟩ := comm_tracks label₁ C₁ comp tracks₁ t u channel P Q
        bs gp foP foQ closedP closedQ first second made₁ made₂ compFirst compSecond distinct madeDistinct
        inFirst inSecond fresh₁ fresh₂
      exact ⟨label₂, C₂, firings.tail succ, present₂Eq, tracks₂⟩

/-! ## A run of two COMM steps, the second on a made row -/

namespace TwoSteps

/-- The process `0` as a term: `(0)`. -/
def zeroTerm : Pattern := MeTTaCalculus.tProc pZero

/-- A second channel, `@((0))`. -/
def ch₁ : Pattern := nQuote zeroTerm

/-- `for((0) <- @0)for((0) <- @((0)))0`: it offers `(0)` on `@0`, then offers `(0)` on `@((0))`. -/
def relay : Pattern := pFor zeroTerm MeTTaCalculus.demoChan (pFor zeroTerm ch₁ pZero)

/-- `for(y <- @0)y`. -/
def onZero : Pattern := pFor (.fvar "y") MeTTaCalculus.demoChan (.fvar "y")

/-- `for(w <- @((0)))w`. -/
def onOne : Pattern := pFor (.fvar "w") ch₁ (.fvar "w")

/-- The components at identities `0`, `1`, `2`. -/
def comps : ℕ → Pattern := fun n => if n = 0 then relay else if n = 1 then onZero else if n = 2 then onOne else pZero

/-- The unifiers `y ↦ (0)` and `w ↦ (0)`. -/
def bindY : Bindings := [("y", zeroTerm)]
def bindW : Bindings := [("w", zeroTerm)]

theorem unify_y : MeTTaCalculus.Corrected.unify zeroTerm (.fvar "y") = some bindY := by decide +kernel
theorem unify_w : MeTTaCalculus.Corrected.unify zeroTerm (.fvar "w") = some bindW := by decide +kernel

theorem ground_y : GroundPrincipal zeroTerm (.fvar "y") bindY := by
  refine groundPrincipal_of_principal (MeTTaCalculus.Corrected.unify_principal unify_y) ?_
  intro x member
  have vars : pvars zeroTerm ++ pvars (.fvar "y") = ["y"] := by decide +kernel
  rw [vars, List.mem_singleton] at member
  subst member
  exact ⟨zeroTerm, by decide +kernel, by decide +kernel⟩

theorem ground_w : GroundPrincipal zeroTerm (.fvar "w") bindW := by
  refine groundPrincipal_of_principal (MeTTaCalculus.Corrected.unify_principal unify_w) ?_
  intro x member
  have vars : pvars zeroTerm ++ pvars (.fvar "w") = ["w"] := by decide +kernel
  rw [vars, List.mem_singleton] at member
  subst member
  exact ⟨zeroTerm, by decide +kernel, by decide +kernel⟩

/-- The components after the first COMM. -/
def comps₁ : ℕ → Pattern :=
  afterComm comps 3 4 (applyDot bindY (pFor zeroTerm ch₁ pZero)) (applyDot bindY (.fvar "y"))

/-- The first COMM: `relay` with `onZero`, making `3` and `4`. -/
theorem step₁ : CommOnComponents (({0, 1, 2} : Finset ℕ), comps) ((({0, 1, 2} : Finset ℕ) \ {0, 1}) ∪ {3, 4}, comps₁) :=
  .comm {0, 1, 2} comps zeroTerm (.fvar "y") MeTTaCalculus.demoChan (pFor zeroTerm ch₁ pZero) (.fvar "y")
    bindY ground_y (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) 0 1 3 4 rfl
    rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The second COMM: the row made at `3`, which offers `(0)` on `@((0))`, with `onOne`, making `5` and
`6`. -/
theorem step₂ : CommOnComponents ((({0, 1, 2} : Finset ℕ) \ {0, 1}) ∪ {3, 4}, comps₁)
    (((({0, 1, 2} : Finset ℕ) \ {0, 1}) ∪ {3, 4}) \ {3, 2} ∪ {5, 6},
      afterComm comps₁ 5 6 (applyDot bindW pZero) (applyDot bindW (.fvar "w"))) :=
  .comm _ comps₁ zeroTerm (.fvar "w") ch₁ pZero (.fvar "w") bindW ground_w (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) 3 2 5 6 (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **The two COMM steps are a run of the step of the comm program**: by `runs_track`, from the
configuration whose rows `0`, `1`, `2` are labelled by the three components, with no knowledge. -/
theorem two_steps :
    ∃ (label' : ℕ → Pattern) (C' : Configuration Pattern ℕ),
      Relation.ReflTransGen (Succ (RuleSyntax.step X ℕ E commRules).toStep)
        (embed comps ⟨[], {0, 1, 2}⟩) (embed label' C') ∧
      C'.present = ((({0, 1, 2} : Finset ℕ) \ {0, 1}) ∪ {3, 4}) \ {3, 2} ∪ {5, 6} ∧
      Tracks label' C' (afterComm comps₁ 5 6 (applyDot bindW pZero) (applyDot bindW (.fvar "w"))) :=
  runs_track ((Relation.ReflTransGen.single step₁).tail step₂) comps ⟨[], {0, 1, 2}⟩ rfl
    (Tracks.of_labels comps ⟨[], {0, 1, 2}⟩ (by decide +kernel)
      ⟨fun _ => none, fun _ member => absurd member List.not_mem_nil⟩)

end TwoSteps

end Runs

#print axioms pvars_psubst_eq_nil
#print axioms applyDot_ground
#print axioms storePVars_comm
#print axioms Tracks.of_labels
#print axioms comm_tracks
#print axioms CommOnComponents.manuscript
#print axioms runs_track
#print axioms TwoSteps.two_steps

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.Comm
