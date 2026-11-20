import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.FiniteHosting

/-!
# The finite program along runs with nested binding

The step is the one-match step of the three-rule `program` at the one frame of structural substitution
on patterns, with the five choices stated in `FiniteComm`: a bag store, one match, guards asked after the
firing's own tells (the rules have none), a fixed set of rules beside the store, one store of knowledge.

`FiniteHosting` proves the correspondence for parts that bind only at their own input. Here continuations
may bind again, at any depth: `for(y <- @0)for(z <- y)z` is in the fragment (`FiniteNestedControls` runs
an example through two communications).

## The fragment

A part is nested (`Nested`) when it is first-order (no explicit substitution, no collection rest), scoped
(`Scoped []`: every variable is bound by an enclosing input, no input rebinds a bound variable, and a
channel binds nothing), and its inputs bind pairwise distinct variables (`FramesApart (frames c)`). A
process is nested (`NestedProcess`) when its parallel parts are, and no two parts' inputs bind a common
variable (`FramesDisjoint`). These two are the variable convention, within a part and across parts. Every
hosted process is nested (`nestedProcess_of_hosted`), and `FiniteNestedControls` gives a nested process
that is not hosted (`nested_example`, `nested_not_hosted`).

## Representation

`NestedBy s M comp`: every present row reads, at every solution of the knowledge, as the representation
`predot` of its part; the parts are nested and no two of them bind a common variable; every variable of a
part occurs in its row's label or in the knowledge; every assignment of the parts' variables extends to a
solution of the knowledge; and the parts of the rows sum to the bag `M`. A row's label need not be its
part's representation: after a communication a made row holds an opened continuation, and the knowledge
says what it reads as.

## The correspondence (`manuscript_calculus_nested`)

The six clauses of `manuscript_calculus_by_a_finite_program`, for nested processes, with the same source
`BagComm`, the same side condition `GroundUnifiable` on the fourth clause, and the same bound on
housekeeping. Along runs: every run of the source from a represented bag is matched by a run of the step
(`runs_complete_nested`), and every run of the step from it is a run of the source when every bag the
source reaches is ground-unifiable (`runs_sound_nested`).

## Scoping and frames

* `Scoped bound p`, `frames p`: the inputs' frames are their patterns' variables, skipping patterns
  without variables.
* `vars_of_scoped`: a scoped term's variables are bound or are its own binders; `binders_not_bound`: its
  binders are not bound outside.
* `scoped_psubst`, `frames_psubst`, `binders_psubst`: substituting values without variables for the
  outermost binders keeps scoping, frames and binders.
* `nested_applyDot`: the dotted continuation of a nested input is nested.

## What is not shown

Renaming bound variables into the convention: the fragment assumes it. Across parts the convention matters
to this representation: a communication fixes the variables of its patterns (`comm_fixes`), and a state
whose knowledge fixes a variable represents no bag in which that variable occurs
(`pinned_represents_nothing`). `FiniteNestedControls` gives a process outside the convention where the
fifth clause fails.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.FiniteProgram

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.MeTTaIL.Match (Bindings)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus (pFor par pZero nQuote applyDot)
open MeTTaOperationsComm (psubst psubst_none psubst_congr psubst_of_pvars_nil pvars patternAction PSubst
  dotted commSelection GroundPrincipal storePVars applyDot_eq psubst_pFor firstOrder lookup_eq_none_of_keys)
open MeTTaCalculus.Corrected (binders bindersList binders_apply bindersFor_cons3 bindersFor_short Apart
  binders_subset_pvars mem_pvars_psubst pvars_pFor psubstList_eq_map mem_pvars_apply_of
  mem_pvars_collection_of)
open Comm (Tm X E renameBy ruleVars)
open OneFrame (embed)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open LogicOverTheStep.StepSpan (Succ)

/-! ## Scoping -/

mutual
/-- **Scoped under `bound`**: every variable is bound by an enclosing input or is in `bound`, no input
rebinds a variable already bound, and a channel binds nothing. -/
def Scoped : List String → Pattern → Prop
  | _, .bvar _ => True
  | bound, .fvar x => x ∈ bound
  | bound, .apply c args => if c = "MFor" then ScopedFor bound args else ScopedList bound args
  | bound, .lambda _ body => Scoped bound body
  | bound, .multiLambda _ _ body => Scoped bound body
  | bound, .subst body repl => Scoped bound body ∧ Scoped bound repl
  | bound, .collection _ elems _ => ScopedList bound elems
/-- Scoping of a list. -/
def ScopedList : List String → List Pattern → Prop
  | _, [] => True
  | bound, p :: ps => Scoped bound p ∧ ScopedList bound ps
/-- Scoping of an input's arguments: the pattern's variables are new, the channel binds nothing, the
continuation is scoped under the pattern's variables. -/
def ScopedFor : List String → List Pattern → Prop
  | _, [] => True
  | bound, [p] => Scoped bound p
  | bound, [p, q] => Scoped bound p ∧ Scoped bound q
  | bound, t :: x :: k :: rest => (∀ y ∈ pvars t, y ∉ bound) ∧ binders x = [] ∧ Scoped bound x ∧
      Scoped (pvars t ++ bound) k ∧ ScopedList bound rest
end

theorem scopedList_iff (bound : List String) (ps : List Pattern) :
    ScopedList bound ps ↔ ∀ p ∈ ps, Scoped bound p := by
  induction ps with
  | nil => simp [ScopedList]
  | cons p ps ih => simp [ScopedList, ih]

theorem scopedFor_short (bound : List String) (ps : List Pattern) (short : ps.length < 3) :
    ScopedFor bound ps ↔ ∀ p ∈ ps, Scoped bound p := by
  match ps, short with
  | [], _ => simp [ScopedFor]
  | [p], _ => simp [ScopedFor]
  | [p, q], _ => simp [ScopedFor]

theorem scoped_apply (bound : List String) (c : String) (args : List Pattern) :
    Scoped bound (.apply c args) ↔ if c = "MFor" then ScopedFor bound args else ∀ p ∈ args, Scoped bound p := by
  simp only [Scoped]
  split_ifs
  · exact Iff.rfl
  · exact scopedList_iff bound args

theorem scoped_pFor (bound : List String) (t x k : Pattern) :
    Scoped bound (pFor t x k) ↔ (∀ y ∈ pvars t, y ∉ bound) ∧ binders x = [] ∧ Scoped bound x ∧
      Scoped (pvars t ++ bound) k := by
  simp [pFor, Scoped, ScopedFor, ScopedList]

theorem scoped_par (bound : List String) (a b : Pattern) :
    Scoped bound (par a b) ↔ Scoped bound a ∧ Scoped bound b := by
  simp [par, MeTTaCalculus.pPar, Scoped, ScopedList]

/-- **Scoping depends only on which variables are bound.** -/
theorem scoped_congr (p : Pattern) : ∀ (bound bound' : List String), (∀ y, y ∈ bound ↔ y ∈ bound') →
    Scoped bound p → Scoped bound' p := by
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, ∀ (bound bound' : List String),
      (∀ y, y ∈ bound ↔ y ∈ bound') → Scoped bound q → Scoped bound' q) with
  | bvar n => intro _ _ _ _; trivial
  | fvar x => intro bound bound' same inside; exact (same x).mp inside
  | apply c args ih =>
      intro bound bound' same hs
      rw [scoped_apply] at hs ⊢
      split_ifs at hs ⊢ with isFor
      · match args, ih, hs with
        | t :: x :: k :: rest, ih, hs =>
            obtain ⟨fresh, noBinders, scopedX, scopedK, scopedRest⟩ := hs
            refine ⟨fun y inT inBound => fresh y inT ((same y).mpr inBound), noBinders,
              ih x (by simp) bound bound' same scopedX,
              ih k (by simp) _ _ (fun y => by simp only [List.mem_append]; rw [same y]) scopedK, ?_⟩
            rw [scopedList_iff] at scopedRest ⊢
            exact fun q member => ih q (by simp [member]) bound bound' same (scopedRest q member)
        | [], _, _ => trivial
        | [p], ih, hs =>
            rw [scopedFor_short _ _ (by simp)] at hs ⊢
            exact fun q member => ih q member bound bound' same (hs q member)
        | [p, q], ih, hs =>
            rw [scopedFor_short _ _ (by simp)] at hs ⊢
            exact fun r member => ih r member bound bound' same (hs r member)
      · exact fun q member => ih q member bound bound' same (hs q member)
  | lambda nm body ih => intro bound bound' same hs; exact ih bound bound' same hs
  | multiLambda n nms body ih => intro bound bound' same hs; exact ih bound bound' same hs
  | subst body repl ihb ihr =>
      intro bound bound' same hs
      exact ⟨ihb bound bound' same hs.1, ihr bound bound' same hs.2⟩
  | collection ct elems rest ih =>
      intro bound bound' same hs
      simp only [Scoped] at hs ⊢
      rw [scopedList_iff] at hs ⊢
      exact fun q member => ih q member bound bound' same (hs q member)
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member bound bound' same hs
      rcases List.mem_cons.mp member with rfl | later
      · exact head bound bound' same hs
      · exact tail q later bound bound' same hs

/-- **A scoped term's variables are bound outside or bound inside.** -/
theorem vars_of_scoped (p : Pattern) : ∀ bound : List String, Scoped bound p →
    ∀ y ∈ pvars p, y ∈ bound ∨ y ∈ binders p := by
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, ∀ bound : List String, Scoped bound q →
      ∀ y ∈ pvars q, y ∈ bound ∨ y ∈ binders q) with
  | bvar n => intro _ _ y inside; simp [pvars] at inside
  | fvar x =>
      intro bound hs y inside
      simp only [pvars, List.mem_singleton] at inside
      subst inside
      exact .inl hs
  | apply c args ih =>
      intro bound hs y inside
      rw [MeTTaCalculus.Corrected.pvars_apply, MeTTaCalculus.Corrected.mem_pvarsList] at inside
      obtain ⟨q, member, inQ⟩ := inside
      rw [scoped_apply] at hs
      rw [binders_apply]
      split_ifs at hs ⊢ with isFor
      · match args, ih, hs, member with
        | t :: x :: k :: rest, ih, hs, member =>
            obtain ⟨-, -, scopedX, scopedK, scopedRest⟩ := hs
            rw [bindersFor_cons3]
            simp only [List.mem_cons] at member
            rcases member with rfl | rfl | rfl | inRest
            · exact .inr (by simp [inQ])
            · rcases ih q (by simp) bound scopedX y inQ with inBound | inBinders
              · exact .inl inBound
              · exact .inr (by simp [inBinders])
            · rcases ih q (by simp) _ scopedK y inQ with inOuter | inBinders
              · rcases List.mem_append.mp inOuter with inT | inBound
                · exact .inr (by simp [inT])
                · exact .inl inBound
              · exact .inr (by simp [inBinders])
            · rw [scopedList_iff] at scopedRest
              rcases ih q (by simp [inRest]) bound (scopedRest q inRest) y inQ with inBound | inBinders
              · exact .inl inBound
              · exact .inr (by simp only [List.mem_append, List.mem_flatMap]; exact .inr ⟨q, inRest, inBinders⟩)
        | [], _, _, member => simp at member
        | [p], ih, hs, member =>
            rw [scopedFor_short _ _ (by simp)] at hs
            rw [bindersFor_short _ (by simp)]
            rcases ih q member bound (hs q member) y inQ with inBound | inBinders
            · exact .inl inBound
            · exact .inr (List.mem_flatMap.mpr ⟨q, member, inBinders⟩)
        | [p, p'], ih, hs, member =>
            rw [scopedFor_short _ _ (by simp)] at hs
            rw [bindersFor_short _ (by simp)]
            rcases ih q member bound (hs q member) y inQ with inBound | inBinders
            · exact .inl inBound
            · exact .inr (List.mem_flatMap.mpr ⟨q, member, inBinders⟩)
      · rcases ih q member bound (hs q member) y inQ with inBound | inBinders
        · exact .inl inBound
        · exact .inr (List.mem_flatMap.mpr ⟨q, member, inBinders⟩)
  | lambda nm body ih =>
      intro bound hs y inside
      simpa [binders] using ih bound hs y (by simpa [pvars] using inside)
  | multiLambda n nms body ih =>
      intro bound hs y inside
      simpa [binders] using ih bound hs y (by simpa [pvars] using inside)
  | subst body repl ihb ihr =>
      intro bound hs y inside
      simp only [pvars, List.mem_append] at inside
      simp only [binders, List.mem_append]
      rcases inside with inBody | inRepl
      · rcases ihb bound hs.1 y inBody with inBound | inBinders
        · exact .inl inBound
        · exact .inr (.inl inBinders)
      · rcases ihr bound hs.2 y inRepl with inBound | inBinders
        · exact .inl inBound
        · exact .inr (.inr inBinders)
  | collection ct elems rest ih =>
      intro bound hs y inside
      simp only [Scoped] at hs
      rw [scopedList_iff] at hs
      simp only [pvars, MeTTaCalculus.Corrected.mem_pvarsList] at inside
      obtain ⟨q, member, inQ⟩ := inside
      simp only [binders, MeTTaCalculus.Corrected.bindersList_eq_flatMap, List.mem_flatMap]
      rcases ih q member bound (hs q member) y inQ with inBound | inBinders
      · exact .inl inBound
      · exact .inr ⟨q, member, inBinders⟩
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member bound hs y inside
      rcases List.mem_cons.mp member with rfl | later
      · exact head bound hs y inside
      · exact tail q later bound hs y inside

/-- **A scoped term's binders are not bound outside.** -/
theorem binders_not_bound (p : Pattern) : ∀ bound : List String, Scoped bound p →
    ∀ y ∈ binders p, y ∉ bound := by
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, ∀ bound : List String, Scoped bound q →
      ∀ y ∈ binders q, y ∉ bound) with
  | bvar n => intro _ _ y inside; simp [binders] at inside
  | fvar x => intro _ _ y inside; simp [binders] at inside
  | apply c args ih =>
      intro bound hs y inside
      rw [scoped_apply] at hs
      rw [binders_apply] at inside
      split_ifs at hs inside with isFor
      · match args, ih, hs, inside with
        | t :: x :: k :: rest, ih, hs, inside =>
            obtain ⟨fresh, noBinders, -, scopedK, scopedRest⟩ := hs
            rw [bindersFor_cons3] at inside
            simp only [List.mem_append, List.mem_flatMap] at inside
            rcases inside with ((inT | inX) | inK) | ⟨q, inRest, inQ⟩
            · exact fresh y inT
            · rw [noBinders] at inX; exact absurd inX List.not_mem_nil
            · intro inBound
              exact ih k (by simp) _ scopedK y inK (List.mem_append_right _ inBound)
            · rw [scopedList_iff] at scopedRest
              exact ih q (by simp [inRest]) bound (scopedRest q inRest) y inQ
        | [], _, _, inside => simp [MeTTaCalculus.Corrected.bindersFor] at inside
        | [p], ih, hs, inside =>
            rw [scopedFor_short _ _ (by simp)] at hs
            rw [bindersFor_short _ (by simp)] at inside
            obtain ⟨q, member, inQ⟩ := List.mem_flatMap.mp inside
            exact ih q member bound (hs q member) y inQ
        | [p, p'], ih, hs, inside =>
            rw [scopedFor_short _ _ (by simp)] at hs
            rw [bindersFor_short _ (by simp)] at inside
            obtain ⟨q, member, inQ⟩ := List.mem_flatMap.mp inside
            exact ih q member bound (hs q member) y inQ
      · obtain ⟨q, member, inQ⟩ := List.mem_flatMap.mp inside
        exact ih q member bound (hs q member) y inQ
  | lambda nm body ih =>
      intro bound hs y inside
      exact ih bound hs y (by simpa [binders] using inside)
  | multiLambda n nms body ih =>
      intro bound hs y inside
      exact ih bound hs y (by simpa [binders] using inside)
  | subst body repl ihb ihr =>
      intro bound hs y inside
      simp only [binders, List.mem_append] at inside
      rcases inside with inBody | inRepl
      · exact ihb bound hs.1 y inBody
      · exact ihr bound hs.2 y inRepl
  | collection ct elems rest ih =>
      intro bound hs y inside
      simp only [Scoped] at hs
      rw [scopedList_iff] at hs
      simp only [binders, MeTTaCalculus.Corrected.bindersList_eq_flatMap, List.mem_flatMap] at inside
      obtain ⟨q, member, inQ⟩ := inside
      exact ih q member bound (hs q member) y inQ
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member bound hs y inside
      rcases List.mem_cons.mp member with rfl | later
      · exact head bound hs y inside
      · exact tail q later bound hs y inside

/-- A term without variables binds nothing. -/
theorem binders_of_ground {p : Pattern} (ground : pvars p = []) : binders p = [] :=
  List.eq_nil_iff_forall_not_mem.mpr fun y inside => by
    have occurs := binders_subset_pvars p y inside
    rw [ground] at occurs
    exact List.not_mem_nil occurs

/-- **A term without variables is scoped under every list.** -/
theorem scoped_of_ground (p : Pattern) : ∀ bound : List String, pvars p = [] → Scoped bound p := by
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, ∀ bound : List String, pvars q = [] →
      Scoped bound q) with
  | bvar n => intro _ _; trivial
  | fvar x => intro _ ground; simp [pvars] at ground
  | apply c args ih =>
      intro bound ground
      have each : ∀ q ∈ args, pvars q = [] := fun q member =>
        List.eq_nil_iff_forall_not_mem.mpr fun y occurs =>
          List.eq_nil_iff_forall_not_mem.mp ground y (mem_pvars_apply_of member occurs)
      rw [scoped_apply]
      split_ifs with isFor
      · match args, ih, each with
        | t :: x :: k :: rest, ih, each =>
            have groundT := each t (by simp)
            refine ⟨fun y inT => by rw [groundT] at inT; exact absurd inT List.not_mem_nil,
              binders_of_ground (each x (by simp)), ih x (by simp) bound (each x (by simp)),
              ih k (by simp) _ (each k (by simp)), ?_⟩
            rw [scopedList_iff]
            exact fun q member => ih q (by simp [member]) bound (each q (by simp [member]))
        | [], _, _ => trivial
        | [p], ih, each =>
            rw [scopedFor_short _ _ (by simp)]
            exact fun q member => ih q member bound (each q member)
        | [p, p'], ih, each =>
            rw [scopedFor_short _ _ (by simp)]
            exact fun q member => ih q member bound (each q member)
      · exact fun q member => ih q member bound (each q member)
  | lambda nm body ih => intro bound ground; exact ih bound (by simpa [pvars] using ground)
  | multiLambda n nms body ih => intro bound ground; exact ih bound (by simpa [pvars] using ground)
  | subst body repl ihb ihr =>
      intro bound ground
      have both : pvars body = [] ∧ pvars repl = [] := by simpa [pvars] using ground
      exact ⟨ihb bound both.1, ihr bound both.2⟩
  | collection ct elems rest ih =>
      intro bound ground
      simp only [Scoped]
      rw [scopedList_iff]
      exact fun q member => ih q member bound (List.eq_nil_iff_forall_not_mem.mpr fun y occurs =>
        List.eq_nil_iff_forall_not_mem.mp ground y (mem_pvars_collection_of member occurs))
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member bound ground
      rcases List.mem_cons.mp member with rfl | later
      · exact head bound ground
      · exact tail q later bound ground

/-- **Substituting values without variables keeps the binders**, when no binder is substituted. -/
theorem binders_psubst {δ : PSubst} (ground : GroundValued δ) (p : Pattern)
    (untouched : ∀ y ∈ binders p, δ y = none) : binders (psubst δ p) = binders p := by
  revert untouched
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, (∀ y ∈ binders q, δ y = none) →
      binders (psubst δ q) = binders q) with
  | bvar n => intro _; rfl
  | fvar x =>
      intro _
      show binders ((δ x).getD (.fvar x)) = binders (.fvar x)
      cases found : δ x with
      | some v => simp only [Option.getD_some]; rw [binders_of_ground (ground x v found)]; rfl
      | none => rfl
  | apply c args ih =>
      intro untouched
      have psubstApply : psubst δ (.apply c args) = .apply c (args.map (psubst δ)) := by
        simp only [psubst, psubstList_eq_map]
      rw [psubstApply, binders_apply, binders_apply]
      rw [binders_apply] at untouched
      split_ifs at untouched ⊢ with isFor
      · match args, ih, untouched with
        | t :: x :: k :: rest, ih, untouched =>
            rw [bindersFor_cons3] at untouched
            simp only [List.map_cons]
            rw [bindersFor_cons3, bindersFor_cons3]
            have tFixed : psubst δ t = t := by
              rw [psubst_congr δ (fun _ => none) t fun y occurs => untouched y (by simp [occurs]), psubst_none]
            rw [tFixed, ih x (by simp) fun y inside => untouched y (by simp [inside]),
              ih k (by simp) fun y inside => untouched y (by simp [inside]), List.flatMap_map]
            congr 1
            exact List.flatMap_congr fun q member => ih q (by simp [member]) fun y inside =>
              untouched y (by simp only [List.mem_append, List.mem_flatMap]; exact .inr ⟨q, member, inside⟩)
        | [], _, _ => rfl
        | [p], ih, untouched =>
            rw [bindersFor_short [p] (by simp)] at untouched
            simp only [List.map_cons, List.map_nil]
            rw [bindersFor_short _ (by simp), bindersFor_short [p] (by simp)]
            simp only [List.flatMap_cons, List.flatMap_nil]
            rw [ih p (by simp) fun y inside => untouched y (by simp [inside])]
        | [p, q], ih, untouched =>
            rw [bindersFor_short [p, q] (by simp)] at untouched
            simp only [List.map_cons, List.map_nil]
            rw [bindersFor_short _ (by simp), bindersFor_short [p, q] (by simp)]
            simp only [List.flatMap_cons, List.flatMap_nil]
            rw [ih p (by simp) fun y inside => untouched y (by simp [inside]),
              ih q (by simp) fun y inside => untouched y (by simp [inside])]
      · rw [List.flatMap_map]
        exact List.flatMap_congr fun q member => ih q member fun y inside =>
          untouched y (List.mem_flatMap.mpr ⟨q, member, inside⟩)
  | lambda nm body ih =>
      intro untouched
      simp only [psubst, binders]
      exact ih fun y inside => untouched y (by simpa [binders] using inside)
  | multiLambda n nms body ih =>
      intro untouched
      simp only [psubst, binders]
      exact ih fun y inside => untouched y (by simpa [binders] using inside)
  | subst body repl ihb ihr =>
      intro untouched
      simp only [psubst, binders]
      rw [ihb fun y inside => untouched y (by simp [binders, inside]),
        ihr fun y inside => untouched y (by simp [binders, inside])]
  | collection ct elems rest ih =>
      intro untouched
      simp only [psubst, binders, MeTTaCalculus.Corrected.bindersList_eq_flatMap, psubstList_eq_map,
        List.flatMap_map]
      exact List.flatMap_congr fun q member => ih q member fun y inside => untouched y (by
        simp only [binders, MeTTaCalculus.Corrected.bindersList_eq_flatMap, List.mem_flatMap]
        exact ⟨q, member, inside⟩)
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member untouched
      rcases List.mem_cons.mp member with rfl | later
      · exact head untouched
      · exact tail q later untouched

/-- **Substituting values without variables for the outermost binders keeps scoping.** The values are
put for variables of `vs`, every variable of `vs` gets one, and no other variable of the term is
substituted. -/
theorem scoped_psubst {δ : PSubst} (ground : GroundValued δ) {vs : List String}
    (covers : ∀ y ∈ vs, (δ y).isSome) (p : Pattern) : ∀ bound : List String,
    Scoped (vs ++ bound) p → (∀ y ∈ pvars p, y ∉ vs → δ y = none) → Scoped bound (psubst δ p) := by
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, ∀ bound : List String,
      Scoped (vs ++ bound) q → (∀ y ∈ pvars q, y ∉ vs → δ y = none) → Scoped bound (psubst δ q)) with
  | bvar n => intro _ _ _; trivial
  | fvar x =>
      intro bound hs outsideVs
      show Scoped bound ((δ x).getD (.fvar x))
      by_cases inVs : x ∈ vs
      · obtain ⟨v, found⟩ := Option.isSome_iff_exists.mp (covers x inVs)
        rw [found, Option.getD_some]
        exact scoped_of_ground v bound (ground x v found)
      · rw [outsideVs x (by simp [pvars]) inVs, Option.getD_none]
        have inside : x ∈ vs ++ bound := hs
        exact (List.mem_append.mp inside).resolve_left inVs
  | apply c args ih =>
      intro bound hs outsideVs
      have psubstApply : psubst δ (.apply c args) = .apply c (args.map (psubst δ)) := by
        simp only [psubst, psubstList_eq_map]
      have onlyArg : ∀ q ∈ args, ∀ y ∈ pvars q, y ∉ vs → δ y = none := fun q member y occurs =>
        outsideVs y (mem_pvars_apply_of member occurs)
      rw [psubstApply, scoped_apply]
      rw [scoped_apply] at hs
      split_ifs at hs ⊢ with isFor
      · match args, ih, hs, onlyArg with
        | t :: x :: k :: rest, ih, hs, onlyArg =>
            obtain ⟨fresh, noBinders, scopedX, scopedK, scopedRest⟩ := hs
            have tFixed : psubst δ t = t := by
              rw [psubst_congr δ (fun _ => none) t fun y occurs =>
                onlyArg t (by simp) y occurs fun inVs => fresh y occurs (List.mem_append_left _ inVs),
                psubst_none]
            simp only [List.map_cons]
            refine ⟨?_, ?_, ih x (by simp) bound scopedX (onlyArg x (by simp)), ?_, ?_⟩
            · rw [tFixed]
              exact fun y inT inBound => fresh y inT (List.mem_append_right _ inBound)
            · rw [binders_psubst ground x (by rw [noBinders]; simp)]
              exact noBinders
            · rw [tFixed]
              refine ih k (by simp) (pvars t ++ bound) ?_ (onlyArg k (by simp))
              exact scoped_congr k _ _ (fun y => by simp only [List.mem_append]; tauto) scopedK
            · rw [scopedList_iff] at scopedRest ⊢
              intro q member
              obtain ⟨r, inRest, rfl⟩ := List.mem_map.mp member
              exact ih r (by simp [inRest]) bound (scopedRest r inRest) (onlyArg r (by simp [inRest]))
        | [], _, _, _ => trivial
        | [p], ih, hs, onlyArg =>
            rw [scopedFor_short _ _ (by simp)] at hs
            rw [scopedFor_short _ _ (by simp)]
            intro q member
            obtain ⟨r, inArgs, rfl⟩ := List.mem_map.mp member
            exact ih r inArgs bound (hs r inArgs) (onlyArg r inArgs)
        | [p, p'], ih, hs, onlyArg =>
            rw [scopedFor_short _ _ (by simp)] at hs
            rw [scopedFor_short _ _ (by simp)]
            intro q member
            obtain ⟨r, inArgs, rfl⟩ := List.mem_map.mp member
            exact ih r inArgs bound (hs r inArgs) (onlyArg r inArgs)
      · intro q member
        obtain ⟨r, inArgs, rfl⟩ := List.mem_map.mp member
        exact ih r inArgs bound (hs r inArgs) (onlyArg r inArgs)
  | lambda nm body ih =>
      intro bound hs outsideVs
      exact ih bound hs fun y occurs => outsideVs y (by simpa [pvars] using occurs)
  | multiLambda n nms body ih =>
      intro bound hs outsideVs
      exact ih bound hs fun y occurs => outsideVs y (by simpa [pvars] using occurs)
  | subst body repl ihb ihr =>
      intro bound hs outsideVs
      exact ⟨ihb bound hs.1 fun y occurs => outsideVs y (by simp [pvars, occurs]),
        ihr bound hs.2 fun y occurs => outsideVs y (by simp [pvars, occurs])⟩
  | collection ct elems rest ih =>
      intro bound hs outsideVs
      simp only [Scoped] at hs
      simp only [psubst, psubstList_eq_map, Scoped]
      rw [scopedList_iff] at hs ⊢
      intro q member
      obtain ⟨r, inElems, rfl⟩ := List.mem_map.mp member
      exact ih r inElems bound (hs r inElems) fun y occurs =>
        outsideVs y (mem_pvars_collection_of inElems occurs)
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member bound hs outsideVs
      rcases List.mem_cons.mp member with rfl | later
      · exact head bound hs outsideVs
      · exact tail q later bound hs outsideVs

/-! ## Frames: the variables each input binds -/

mutual
/-- **The frames of a term**: for each input with a variable in its pattern, the pattern's variables. -/
def frames : Pattern → List (List String)
  | .bvar _ => []
  | .fvar _ => []
  | .apply c args => if c = "MFor" then framesFor args else framesList args
  | .lambda _ body => frames body
  | .multiLambda _ _ body => frames body
  | .subst body repl => frames body ++ frames repl
  | .collection _ elems _ => framesList elems
/-- Frames of a list. -/
def framesList : List Pattern → List (List String)
  | [] => []
  | p :: ps => frames p ++ framesList ps
/-- Frames of an input's arguments. -/
def framesFor : List Pattern → List (List String)
  | [] => []
  | [p] => frames p
  | [p, q] => frames p ++ frames q
  | t :: x :: k :: rest => (if pvars t = [] then [] else [pvars t]) ++ frames x ++ frames k ++ framesList rest
end

theorem framesList_eq_flatMap (ps : List Pattern) : framesList ps = ps.flatMap frames := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [framesList, ih]

theorem frames_apply (c : String) (args : List Pattern) :
    frames (.apply c args) = if c = "MFor" then framesFor args else args.flatMap frames := by
  simp [frames, framesList_eq_flatMap]

theorem framesFor_cons3 (t x k : Pattern) (rest : List Pattern) :
    framesFor (t :: x :: k :: rest) =
      (if pvars t = [] then [] else [pvars t]) ++ frames x ++ frames k ++ rest.flatMap frames := by
  simp [framesFor, framesList_eq_flatMap]

theorem framesFor_short (ps : List Pattern) (short : ps.length < 3) : framesFor ps = ps.flatMap frames := by
  match ps, short with
  | [], _ => rfl
  | [p], _ => simp [framesFor]
  | [p, q], _ => simp [framesFor]

theorem frames_pFor (t x k : Pattern) :
    frames (pFor t x k) = (if pvars t = [] then [] else [pvars t]) ++ frames x ++ frames k := by
  simp [pFor, frames_apply, framesFor_cons3]

theorem frames_par (a b : Pattern) : frames (par a b) = frames a ++ frames b := by
  simp [par, MeTTaCalculus.pPar, frames, framesList]

/-- **The binders are the frames' variables.** -/
theorem mem_binders_iff (p : Pattern) : ∀ y : String, y ∈ binders p ↔ ∃ f ∈ frames p, y ∈ f := by
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, ∀ y : String,
      y ∈ binders q ↔ ∃ f ∈ frames q, y ∈ f) with
  | bvar n => intro y; simp [binders, frames]
  | fvar x => intro y; simp [binders, frames]
  | apply c args ih =>
      intro y
      rw [binders_apply, frames_apply]
      split_ifs with isFor
      · match args, ih with
        | t :: x :: k :: rest, ih =>
            rw [bindersFor_cons3, framesFor_cons3]
            simp only [List.mem_append, List.mem_flatMap]
            rw [ih x (by simp) y, ih k (by simp) y]
            constructor
            · rintro (((inT | ⟨f, inX, inF⟩) | ⟨f, inK, inF⟩) | ⟨q, inRest, inQ⟩)
              · have notEmpty : pvars t ≠ [] := List.ne_nil_of_mem inT
                exact ⟨pvars t, by simp [notEmpty], inT⟩
              · exact ⟨f, by simp [inX], inF⟩
              · exact ⟨f, by simp [inK], inF⟩
              · obtain ⟨f, inQF, inF⟩ := (ih q (by simp [inRest]) y).mp inQ
                exact ⟨f, .inr ⟨q, inRest, inQF⟩, inF⟩
            · rintro ⟨f, member, inF⟩
              rcases member with ((inT | inX) | inK) | ⟨q, inRest, inQ⟩
              · split_ifs at inT with empty
                · exact absurd inT List.not_mem_nil
                · rw [List.mem_singleton] at inT
                  subst inT
                  exact .inl (.inl (.inl inF))
              · exact .inl (.inl (.inr ⟨f, inX, inF⟩))
              · exact .inl (.inr ⟨f, inK, inF⟩)
              · exact .inr ⟨q, inRest, (ih q (by simp [inRest]) y).mpr ⟨f, inQ, inF⟩⟩
        | [], _ => simp [MeTTaCalculus.Corrected.bindersFor, framesFor]
        | [p], ih =>
            rw [bindersFor_short _ (by simp), framesFor_short _ (by simp)]
            simp only [List.mem_flatMap]
            constructor
            · rintro ⟨q, member, inQ⟩
              obtain ⟨f, inQF, inF⟩ := (ih q member y).mp inQ
              exact ⟨f, ⟨q, member, inQF⟩, inF⟩
            · rintro ⟨f, ⟨q, member, inQF⟩, inF⟩
              exact ⟨q, member, (ih q member y).mpr ⟨f, inQF, inF⟩⟩
        | [p, p'], ih =>
            rw [bindersFor_short _ (by simp), framesFor_short _ (by simp)]
            simp only [List.mem_flatMap]
            constructor
            · rintro ⟨q, member, inQ⟩
              obtain ⟨f, inQF, inF⟩ := (ih q member y).mp inQ
              exact ⟨f, ⟨q, member, inQF⟩, inF⟩
            · rintro ⟨f, ⟨q, member, inQF⟩, inF⟩
              exact ⟨q, member, (ih q member y).mpr ⟨f, inQF, inF⟩⟩
      · simp only [List.mem_flatMap]
        constructor
        · rintro ⟨q, member, inQ⟩
          obtain ⟨f, inQF, inF⟩ := (ih q member y).mp inQ
          exact ⟨f, ⟨q, member, inQF⟩, inF⟩
        · rintro ⟨f, ⟨q, member, inQF⟩, inF⟩
          exact ⟨q, member, (ih q member y).mpr ⟨f, inQF, inF⟩⟩
  | lambda nm body ih => intro y; simpa [binders, frames] using ih y
  | multiLambda n nms body ih => intro y; simpa [binders, frames] using ih y
  | subst body repl ihb ihr =>
      intro y
      simp only [binders, frames, List.mem_append]
      rw [ihb y, ihr y]
      constructor
      · rintro (⟨f, inF, inY⟩ | ⟨f, inF, inY⟩)
        · exact ⟨f, .inl inF, inY⟩
        · exact ⟨f, .inr inF, inY⟩
      · rintro ⟨f, inF | inF, inY⟩
        · exact .inl ⟨f, inF, inY⟩
        · exact .inr ⟨f, inF, inY⟩
  | collection ct elems rest ih =>
      intro y
      simp only [binders, frames, MeTTaCalculus.Corrected.bindersList_eq_flatMap, framesList_eq_flatMap,
        List.mem_flatMap]
      constructor
      · rintro ⟨q, member, inQ⟩
        obtain ⟨f, inQF, inF⟩ := (ih q member y).mp inQ
        exact ⟨f, ⟨q, member, inQF⟩, inF⟩
      · rintro ⟨f, ⟨q, member, inQF⟩, inF⟩
        exact ⟨q, member, (ih q member y).mpr ⟨f, inQF, inF⟩⟩
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member y
      rcases List.mem_cons.mp member with rfl | later
      · exact head y
      · exact tail q later y

/-- **A term without variables has no frame.** -/
theorem frames_of_ground (p : Pattern) (ground : pvars p = []) : frames p = [] := by
  revert ground
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, pvars q = [] → frames q = []) with
  | bvar n => intro _; rfl
  | fvar x => intro ground; simp [pvars] at ground
  | apply c args ih =>
      intro ground
      have each : ∀ q ∈ args, pvars q = [] := fun q member =>
        List.eq_nil_iff_forall_not_mem.mpr fun y occurs =>
          List.eq_nil_iff_forall_not_mem.mp ground y (mem_pvars_apply_of member occurs)
      rw [frames_apply]
      split_ifs with isFor
      · match args, ih, each with
        | t :: x :: k :: rest, ih, each =>
            rw [framesFor_cons3, if_pos (each t (by simp)), ih x (by simp) (each x (by simp)),
              ih k (by simp) (each k (by simp))]
            simp only [List.nil_append, List.flatMap_eq_nil_iff]
            exact fun q member => ih q (by simp [member]) (each q (by simp [member]))
        | [], _, _ => rfl
        | [p], ih, each =>
            rw [framesFor_short _ (by simp), List.flatMap_eq_nil_iff]
            exact fun q member => ih q member (each q member)
        | [p, p'], ih, each =>
            rw [framesFor_short _ (by simp), List.flatMap_eq_nil_iff]
            exact fun q member => ih q member (each q member)
      · rw [List.flatMap_eq_nil_iff]
        exact fun q member => ih q member (each q member)
  | lambda nm body ih =>
      intro ground
      simp only [frames]
      exact ih (by simpa [pvars] using ground)
  | multiLambda n nms body ih =>
      intro ground
      simp only [frames]
      exact ih (by simpa [pvars] using ground)
  | subst body repl ihb ihr =>
      intro ground
      have both : pvars body = [] ∧ pvars repl = [] := by simpa [pvars] using ground
      simp only [frames]
      rw [ihb both.1, ihr both.2]
      rfl
  | collection ct elems rest ih =>
      intro ground
      simp only [frames, framesList_eq_flatMap, List.flatMap_eq_nil_iff]
      exact fun q member => ih q member (List.eq_nil_iff_forall_not_mem.mpr fun y occurs =>
        List.eq_nil_iff_forall_not_mem.mp ground y (mem_pvars_collection_of member occurs))
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member ground
      rcases List.mem_cons.mp member with rfl | later
      · exact head ground
      · exact tail q later ground

/-- **Substituting values without variables keeps the frames**, when no binder is substituted. -/
theorem frames_psubst {δ : PSubst} (ground : GroundValued δ) (p : Pattern)
    (untouched : ∀ y ∈ binders p, δ y = none) : frames (psubst δ p) = frames p := by
  revert untouched
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, (∀ y ∈ binders q, δ y = none) →
      frames (psubst δ q) = frames q) with
  | bvar n => intro _; rfl
  | fvar x =>
      intro _
      show frames ((δ x).getD (.fvar x)) = frames (.fvar x)
      cases found : δ x with
      | some v => simp only [Option.getD_some]; rw [frames_of_ground v (ground x v found)]; rfl
      | none => rfl
  | apply c args ih =>
      intro untouched
      have psubstApply : psubst δ (.apply c args) = .apply c (args.map (psubst δ)) := by
        simp only [psubst, psubstList_eq_map]
      rw [psubstApply, frames_apply, frames_apply]
      rw [binders_apply] at untouched
      split_ifs at untouched ⊢ with isFor
      · match args, ih, untouched with
        | t :: x :: k :: rest, ih, untouched =>
            rw [bindersFor_cons3] at untouched
            simp only [List.map_cons]
            rw [framesFor_cons3, framesFor_cons3]
            have tFixed : psubst δ t = t := by
              rw [psubst_congr δ (fun _ => none) t fun y occurs => untouched y (by simp [occurs]), psubst_none]
            rw [tFixed, ih x (by simp) fun y inside => untouched y (by simp [inside]),
              ih k (by simp) fun y inside => untouched y (by simp [inside]), List.flatMap_map]
            congr 1
            exact List.flatMap_congr fun q member => ih q (by simp [member]) fun y inside =>
              untouched y (by simp only [List.mem_append, List.mem_flatMap]; exact .inr ⟨q, member, inside⟩)
        | [], _, _ => rfl
        | [p], ih, untouched =>
            rw [bindersFor_short [p] (by simp)] at untouched
            simp only [List.map_cons, List.map_nil]
            rw [framesFor_short _ (by simp), framesFor_short [p] (by simp)]
            simp only [List.flatMap_cons, List.flatMap_nil]
            rw [ih p (by simp) fun y inside => untouched y (by simp [inside])]
        | [p, q], ih, untouched =>
            rw [bindersFor_short [p, q] (by simp)] at untouched
            simp only [List.map_cons, List.map_nil]
            rw [framesFor_short _ (by simp), framesFor_short [p, q] (by simp)]
            simp only [List.flatMap_cons, List.flatMap_nil]
            rw [ih p (by simp) fun y inside => untouched y (by simp [inside]),
              ih q (by simp) fun y inside => untouched y (by simp [inside])]
      · rw [List.flatMap_map]
        exact List.flatMap_congr fun q member => ih q member fun y inside =>
          untouched y (List.mem_flatMap.mpr ⟨q, member, inside⟩)
  | lambda nm body ih =>
      intro untouched
      simp only [psubst, frames]
      exact ih fun y inside => untouched y (by simpa [binders] using inside)
  | multiLambda n nms body ih =>
      intro untouched
      simp only [psubst, frames]
      exact ih fun y inside => untouched y (by simpa [binders] using inside)
  | subst body repl ihb ihr =>
      intro untouched
      simp only [psubst, frames]
      rw [ihb fun y inside => untouched y (by simp [binders, inside]),
        ihr fun y inside => untouched y (by simp [binders, inside])]
  | collection ct elems rest ih =>
      intro untouched
      simp only [psubst, frames, framesList_eq_flatMap, psubstList_eq_map, List.flatMap_map]
      exact List.flatMap_congr fun q member => ih q member fun y inside => untouched y (by
        simp only [binders, MeTTaCalculus.Corrected.bindersList_eq_flatMap, List.mem_flatMap]
        exact ⟨q, member, inside⟩)
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member untouched
      rcases List.mem_cons.mp member with rfl | later
      · exact head untouched
      · exact tail q later untouched

/-! ## Pre-dotting keeps every variable -/

/-- **Pre-dotting keeps every variable.** -/
theorem mem_pvars_predot_of_mem {p : Pattern} {x : String} (occurs : x ∈ pvars p) : x ∈ pvars (predot p) := by
  revert occurs
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, x ∈ pvars q → x ∈ pvars (predot q)) with
  | bvar n => exact id
  | fvar y => exact id
  | apply c args ih =>
      intro occurs
      rw [MeTTaCalculus.Corrected.pvars_apply, MeTTaCalculus.Corrected.mem_pvarsList] at occurs
      obtain ⟨q, member, inQ⟩ := occurs
      rw [predot_apply, MeTTaCalculus.Corrected.pvars_apply, MeTTaCalculus.Corrected.mem_pvarsList]
      split_ifs with isFor
      · match args, ih, member with
        | t :: y :: k :: rest, ih, member =>
            rw [predotFor_cons3]
            simp only [List.mem_cons] at member
            rcases member with rfl | rfl | rfl | inRest
            · exact ⟨q, by simp, inQ⟩
            · exact ⟨predot q, by simp, ih q (by simp) inQ⟩
            · exact ⟨dotted (pvars t) (predot q), by simp, mem_pvars_dotted.mpr (ih q (by simp) inQ)⟩
            · exact ⟨predot q, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_map_of_mem inRest))), ih q (by simp [inRest]) inQ⟩
        | [], _, member => simp at member
        | [p], ih, member =>
            rw [predotFor_short [p] (by simp)]
            exact ⟨predot q, List.mem_map_of_mem member, ih q member inQ⟩
        | [p, p'], ih, member =>
            rw [predotFor_short [p, p'] (by simp)]
            exact ⟨predot q, List.mem_map_of_mem member, ih q member inQ⟩
      · exact ⟨predot q, List.mem_map_of_mem member, ih q member inQ⟩
  | lambda nm body ih =>
      intro occurs
      simp only [predot, pvars] at occurs ⊢
      exact ih occurs
  | multiLambda n nms body ih =>
      intro occurs
      simp only [predot, pvars] at occurs ⊢
      exact ih occurs
  | subst body repl ihb ihr =>
      intro occurs
      simp only [predot, pvars, List.mem_append] at occurs ⊢
      rcases occurs with inBody | inRepl
      · exact .inl (ihb inBody)
      · exact .inr (ihr inRepl)
  | collection ct elems rest ih =>
      intro occurs
      simp only [pvars, MeTTaCalculus.Corrected.mem_pvarsList] at occurs
      obtain ⟨q, member, inQ⟩ := occurs
      simp only [predot, predotList_eq_map, pvars, MeTTaCalculus.Corrected.mem_pvarsList]
      exact ⟨predot q, List.mem_map_of_mem member, ih q member inQ⟩
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member inQ
      rcases List.mem_cons.mp member with rfl | later
      · exact head inQ
      · exact tail q later inQ

/-! ## The nested fragment -/

/-- Frames that share no variable. -/
def FramesApart (L : List (List String)) : Prop := L.Pairwise fun f g => ∀ y ∈ f, y ∉ g

/-- Two terms whose inputs bind no common variable. -/
def FramesDisjoint (c d : Pattern) : Prop := ∀ f ∈ frames c, ∀ g ∈ frames d, ∀ y ∈ f, y ∉ g

theorem FramesDisjoint.symm {c d : Pattern} (apart : FramesDisjoint c d) : FramesDisjoint d c :=
  fun g inD f inC y inG inF => apart f inC g inD y inF inG

theorem FramesDisjoint.mono {c d e : Pattern} (apart : FramesDisjoint c d)
    (sub : ∀ g ∈ frames e, g ∈ frames d) : FramesDisjoint c e :=
  fun f inC g inE y inF inG => apart f inC g (sub g inE) y inF inG

instance (L : List (List String)) : Decidable (FramesApart L) :=
  inferInstanceAs (Decidable (L.Pairwise fun f g => ∀ y ∈ f, y ∉ g))

instance (c d : Pattern) : Decidable (FramesDisjoint c d) :=
  inferInstanceAs (Decidable (∀ f ∈ frames c, ∀ g ∈ frames d, ∀ y ∈ f, y ∉ g))

/-- **A part of the nested fragment**: first-order, scoped, and its inputs bind pairwise distinct
variables. -/
def Nested (c : Pattern) : Prop := firstOrder c = true ∧ Scoped [] c ∧ FramesApart (frames c)

/-- **A process of the nested fragment**: its parallel parts are nested, and no two parts' inputs bind a
common variable. -/
structure NestedProcess (P : Pattern) : Prop where
  nested : ∀ c ∈ parts P, Nested c
  disjoint : (parts P).Pairwise FramesDisjoint

/-- A closed term's variables are its binders. -/
theorem binders_of_closed {c : Pattern} (closed : Scoped [] c) {y : String} (occurs : y ∈ pvars c) :
    y ∈ binders c :=
  (vars_of_scoped c [] closed y occurs).resolve_left List.not_mem_nil

/-- **Closed terms whose inputs bind no common variable share no variable.** -/
theorem vars_disjoint {c d : Pattern} (closedC : Scoped [] c) (closedD : Scoped [] d)
    (apart : FramesDisjoint c d) {y : String} (inC : y ∈ pvars c) : y ∉ pvars d := fun inD => by
  obtain ⟨f, inF, yF⟩ := (mem_binders_iff c y).mp (binders_of_closed closedC inC)
  obtain ⟨g, inG, yG⟩ := (mem_binders_iff d y).mp (binders_of_closed closedD inD)
  exact apart f inF g inG y yF yG

theorem pattern_frame {t x k : Pattern} {y : String} (inT : y ∈ pvars t) : pvars t ∈ frames (pFor t x k) := by
  rw [frames_pFor, if_neg (List.ne_nil_of_mem inT)]
  simp

theorem continuation_frame {t x k : Pattern} {f : List String} (member : f ∈ frames k) :
    f ∈ frames (pFor t x k) := by
  rw [frames_pFor]
  simp [member]

/-- **The facts of a nested input.** -/
theorem Nested.input {t x A : Pattern} (nested : Nested (pFor t x A)) :
    pvars x = [] ∧ Scoped (pvars t) A ∧ (∀ y ∈ pvars t, y ∉ binders A) ∧ firstOrder A = true ∧
      FramesApart (frames A) := by
  obtain ⟨fo, closed, apart⟩ := nested
  rw [scoped_pFor] at closed
  obtain ⟨-, noBinders, scopedX, scopedA⟩ := closed
  refine ⟨?_, scoped_congr A _ _ (fun y => by simp) scopedA, fun y inT inA => ?_,
    (firstOrder_pFor.mp fo).2.2, ?_⟩
  · exact List.eq_nil_iff_forall_not_mem.mpr fun y occurs => by
      rcases vars_of_scoped x [] scopedX y occurs with inBound | inBinders
      · exact List.not_mem_nil inBound
      · rw [noBinders] at inBinders
        exact List.not_mem_nil inBinders
  · exact binders_not_bound A _ scopedA y inA (List.mem_append_left _ inT)
  · have whole : FramesApart ((if pvars t = [] then [] else [pvars t]) ++ frames x ++ frames A) := by
      rw [← frames_pFor]
      exact apart
    exact List.Pairwise.sublist (List.sublist_append_right _ _) whole

/-- **The parts of a nested binary parallel composition are nested and bind no common variable.** -/
theorem Nested.parts_of_par {a b : Pattern} (nested : Nested (par a b)) :
    Nested a ∧ Nested b ∧ FramesDisjoint a b := by
  obtain ⟨fo, closed, apart⟩ := nested
  obtain ⟨foA, foB⟩ := firstOrder_par.mp fo
  rw [scoped_par] at closed
  have whole : FramesApart (frames a ++ frames b) := by
    rw [← frames_par]
    exact apart
  unfold FramesApart at whole
  rw [List.pairwise_append] at whole
  obtain ⟨apartA, apartB, cross⟩ := whole
  exact ⟨⟨foA, closed.1, apartA⟩, ⟨foB, closed.2, apartB⟩, fun f inF g inG y yF yG => cross f inF g inG y yF yG⟩

theorem predotFor_length (ps : List Pattern) : (predotFor ps).length = ps.length := by
  match ps with
  | [] => rfl
  | [p] => simp [predotFor]
  | [p, q] => simp [predotFor]
  | t :: x :: k :: rest => simp [predotFor_cons3]

/-- A closed term read as an input is an input. -/
theorem closed_input_of_instance {c : Pattern} (closed : Scoped [] c) {σ : PSubst} {a b d : Pattern}
    (same : psubst σ (predot c) = pFor a b d) : ∃ t x A, c = pFor t x A := by
  cases c with
  | fvar z => exact absurd (show z ∈ ([] : List String) from closed) List.not_mem_nil
  | apply f args =>
      rw [predot_apply] at same
      simp only [psubst, psubstList_eq_map, pFor, Pattern.apply.injEq] at same
      obtain ⟨rfl, lengths⟩ := same
      have three : args.length = 3 := by
        have counted := congrArg List.length lengths
        simpa [predotFor_length] using counted
      match args, three with
      | [t, x, A], _ => exact ⟨t, x, A, rfl⟩
  | bvar n => simp [predot, psubst, pFor] at same
  | lambda nm body => simp [predot, psubst, pFor] at same
  | multiLambda n nms body => simp [predot, psubst, pFor] at same
  | subst body repl => simp [predot, psubst, pFor] at same
  | collection ct elems rest => simp [predot, psubst, pFor] at same

/-- A closed term read as a binary parallel composition is one. -/
theorem closed_par_of_instance {c : Pattern} (closed : Scoped [] c) {σ : PSubst} {a b : Pattern}
    (same : psubst σ (predot c) = par a b) : ∃ a' b', c = par a' b' := by
  cases c with
  | fvar z => exact absurd (show z ∈ ([] : List String) from closed) List.not_mem_nil
  | collection ct elems rest =>
      simp only [predot, predotList_eq_map, psubst, psubstList_eq_map, par, MeTTaCalculus.pPar,
        Pattern.collection.injEq] at same
      obtain ⟨rfl, lengths, rfl⟩ := same
      have two : elems.length = 2 := by simpa using congrArg List.length lengths
      match elems, two with
      | [a', b'], _ => exact ⟨a', b', rfl⟩
  | bvar n => simp [predot, psubst, par, MeTTaCalculus.pPar] at same
  | apply f args =>
      rw [predot_apply] at same
      simp [psubst, par, MeTTaCalculus.pPar] at same
  | lambda nm body => simp [predot, psubst, par, MeTTaCalculus.pPar] at same
  | multiLambda n nms body => simp [predot, psubst, par, MeTTaCalculus.pPar] at same
  | subst body repl => simp [predot, psubst, par, MeTTaCalculus.pPar] at same

/-- A closed term read as `0` is `0`. -/
theorem closed_zero_of_instance {c : Pattern} (closed : Scoped [] c) {σ : PSubst}
    (same : psubst σ (predot c) = pZero) : c = pZero := by
  cases c with
  | fvar z => exact absurd (show z ∈ ([] : List String) from closed) List.not_mem_nil
  | apply f args =>
      rw [predot_apply] at same
      simp only [psubst, psubstList_eq_map, pZero, Pattern.apply.injEq] at same
      obtain ⟨rfl, empty⟩ := same
      have noArgs : args = [] := by simpa using empty
      subst noArgs
      rfl
  | bvar n => simp [predot, psubst, pZero] at same
  | lambda nm body => simp [predot, psubst, pZero] at same
  | multiLambda n nms body => simp [predot, psubst, pZero] at same
  | subst body repl => simp [predot, psubst, pZero] at same
  | collection ct elems rest => simp [predot, psubst, pZero] at same

/-! ## The dotted continuation of a nested input -/

theorem dot_groundValued {t u : Pattern} {bs : Bindings} (gp : GroundPrincipal t u bs) :
    GroundValued (fun y => (bs.lookup y).map nQuote) := by
  intro y v found
  change (bs.lookup y).map nQuote = some v at found
  obtain ⟨w, look, rfl⟩ := Option.map_eq_some_iff.mp found
  obtain ⟨w', look', closed⟩ := gp.covers y (mem_keys_of_lookup gp.keys look)
  rw [look] at look'
  obtain rfl := Option.some.inj look'
  simp [nQuote, pvars, MeTTaOperationsComm.pvars.pvarsList, closed]

/-- **The dotted continuation of a nested input is a nested part**, under a ground principal unifier with
first-order values, when the continuation is scoped under variables of the patterns and no inner input
binds a variable of either pattern. Its frames are the continuation's, and its variables are variables of
the continuation that neither pattern has. -/
theorem nested_applyDot {t u : Pattern} {bs : Bindings} (gp : GroundPrincipal t u bs)
    (values : ∀ y v, bs.lookup y = some v → firstOrder v = true) {vs : List String}
    (sub : ∀ y ∈ vs, y ∈ pvars t ++ pvars u) {A : Pattern} (fo : firstOrder A = true)
    (scopedA : Scoped vs A) (framesA : FramesApart (frames A))
    (keysOutside : ∀ y ∈ binders A, y ∉ pvars t ++ pvars u) :
    Nested (applyDot bs A) ∧ frames (applyDot bs A) = frames A ∧
      ∀ y ∈ pvars (applyDot bs A), y ∈ pvars A ∧ y ∉ pvars t ++ pvars u := by
  rw [applyDot_eq bs A fo]
  have ground := dot_groundValued gp
  have untouched : ∀ y ∈ binders A, (fun y => (bs.lookup y).map nQuote) y = Option.none := by
    intro y inside
    simp [lookup_eq_none_of_keys gp.keys (keysOutside y inside)]
  have covers : ∀ y ∈ vs, ((fun y => (bs.lookup y).map nQuote) y).isSome := by
    intro y inVs
    obtain ⟨v, found, -⟩ := gp.covers y (sub y inVs)
    simp [found]
  have outsideVs : ∀ y ∈ pvars A, y ∉ vs → (fun y => (bs.lookup y).map nQuote) y = Option.none := by
    intro y inA notVs
    rcases vars_of_scoped A vs scopedA y inA with inVs | inBinders
    · exact absurd inVs notVs
    · exact untouched y inBinders
  have framesSame := frames_psubst ground A untouched
  refine ⟨⟨firstOrder_psubst (fun y v found => ?_) A fo,
    scoped_psubst ground covers A [] (by simpa using scopedA) outsideVs, ?_⟩, framesSame, ?_⟩
  · change (bs.lookup y).map nQuote = some v at found
    obtain ⟨w, look, rfl⟩ := Option.map_eq_some_iff.mp found
    simp [nQuote, firstOrder, MeTTaOperationsComm.firstOrder.firstOrderList, values y w look]
  · rw [framesSame]
    exact framesA
  · intro y inside
    obtain ⟨w, inA, inW⟩ := (mem_pvars_psubst _ A y).mp inside
    have inW' : y ∈ pvars (((bs.lookup w).map nQuote).getD (.fvar w)) := inW
    cases look : bs.lookup w with
    | some v =>
        obtain ⟨v', look', closed⟩ := gp.covers w (mem_keys_of_lookup gp.keys look)
        rw [look] at look'
        obtain rfl := Option.some.inj look'
        rw [look] at inW'
        simp [nQuote, pvars, MeTTaOperationsComm.pvars.pvarsList, closed] at inW'
    | none =>
        rw [look] at inW'
        simp only [Option.map_none, Option.getD_none, pvars, List.mem_singleton] at inW'
        subst inW'
        refine ⟨inA, fun inKeys => ?_⟩
        obtain ⟨v, found, -⟩ := gp.covers y inKeys
        rw [look] at found
        cases found

/-! ## The hosted fragment is nested -/

/-- **A term that binds nothing is scoped under every list holding its variables.** -/
theorem scoped_of_binders_nil (p : Pattern) : ∀ bound : List String, binders p = [] →
    (∀ y ∈ pvars p, y ∈ bound) → Scoped bound p := by
  induction p using Pattern.rec (motive_2 := fun ps => ∀ q ∈ ps, ∀ bound : List String, binders q = [] →
      (∀ y ∈ pvars q, y ∈ bound) → Scoped bound q) with
  | bvar n => intro _ _ _; trivial
  | fvar x => intro bound _ inside; exact inside x (by simp [pvars])
  | apply c args ih =>
      intro bound noBinders inside
      have varsOf : ∀ q ∈ args, ∀ y ∈ pvars q, y ∈ bound := fun q member y occurs =>
        inside y (mem_pvars_apply_of member occurs)
      rw [binders_apply] at noBinders
      rw [scoped_apply]
      split_ifs at noBinders ⊢ with isFor
      · match args, ih, varsOf, noBinders with
        | t :: x :: k :: rest, ih, varsOf, noBinders =>
            rw [bindersFor_cons3] at noBinders
            simp only [List.append_eq_nil_iff, List.flatMap_eq_nil_iff] at noBinders
            obtain ⟨⟨⟨noT, noX⟩, noK⟩, noRest⟩ := noBinders
            refine ⟨fun y inT => by rw [noT] at inT; exact absurd inT List.not_mem_nil, noX,
              ih x (by simp) bound noX (varsOf x (by simp)),
              ih k (by simp) _ noK fun y occurs => List.mem_append_right _ (varsOf k (by simp) y occurs), ?_⟩
            rw [scopedList_iff]
            exact fun q member => ih q (by simp [member]) bound (noRest q member) (varsOf q (by simp [member]))
        | [], _, _, _ => trivial
        | [p], ih, varsOf, noBinders =>
            rw [bindersFor_short _ (by simp), List.flatMap_eq_nil_iff] at noBinders
            rw [scopedFor_short _ _ (by simp)]
            exact fun q member => ih q member bound (noBinders q member) (varsOf q member)
        | [p, p'], ih, varsOf, noBinders =>
            rw [bindersFor_short _ (by simp), List.flatMap_eq_nil_iff] at noBinders
            rw [scopedFor_short _ _ (by simp)]
            exact fun q member => ih q member bound (noBinders q member) (varsOf q member)
      · rw [List.flatMap_eq_nil_iff] at noBinders
        exact fun q member => ih q member bound (noBinders q member) (varsOf q member)
  | lambda nm body ih =>
      intro bound noBinders inside
      exact ih bound (by simpa [binders] using noBinders) (by simpa [pvars] using inside)
  | multiLambda n nms body ih =>
      intro bound noBinders inside
      exact ih bound (by simpa [binders] using noBinders) (by simpa [pvars] using inside)
  | subst body repl ihb ihr =>
      intro bound noBinders inside
      have both : binders body = [] ∧ binders repl = [] := by simpa [binders] using noBinders
      exact ⟨ihb bound both.1 fun y occurs => inside y (by simp [pvars, occurs]),
        ihr bound both.2 fun y occurs => inside y (by simp [pvars, occurs])⟩
  | collection ct elems rest ih =>
      intro bound noBinders inside
      simp only [Scoped]
      rw [scopedList_iff]
      have each : ∀ q ∈ elems, binders q = [] := by
        simpa [binders, MeTTaCalculus.Corrected.bindersList_eq_flatMap, List.flatMap_eq_nil_iff] using
          noBinders
      exact fun q member => ih q member bound (each q member)
        (fun y occurs => inside y (mem_pvars_collection_of member occurs))
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member bound noBinders inside
      rcases List.mem_cons.mp member with rfl | later
      · exact head bound noBinders inside
      · exact tail q later bound noBinders inside

/-- A frame's variables are variables of the term. -/
theorem mem_pvars_of_mem_frames {c : Pattern} {f : List String} (member : f ∈ frames c) {y : String}
    (inF : y ∈ f) : y ∈ pvars c :=
  binders_subset_pvars c y ((mem_binders_iff c y).mpr ⟨f, member, inF⟩)

/-- **A hosted part is nested.** -/
theorem nested_of_hosted {c : Pattern} (hosted : Hosted c) : Nested c := by
  obtain ⟨fo, ground | ⟨t, x, A, rfl, groundX, own, noBinders⟩⟩ := hosted
  · exact ⟨fo, scoped_of_ground c [] ground, by rw [frames_of_ground c ground]; exact List.Pairwise.nil⟩
  · have empty : ∀ f ∈ frames A, ∀ y ∈ f, False := fun f member y inF => by
      have inBinders := (mem_binders_iff A y).mpr ⟨f, member, inF⟩
      rw [noBinders] at inBinders
      exact List.not_mem_nil inBinders
    refine ⟨fo, (scoped_pFor [] t x A).mpr ⟨fun y _ => List.not_mem_nil, binders_of_ground groundX,
      scoped_of_ground x [] groundX, scoped_of_binders_nil A _ noBinders fun y occurs =>
        List.mem_append_left _ (own y occurs)⟩, ?_⟩
    rw [frames_pFor, frames_of_ground x groundX, List.append_nil]
    unfold FramesApart
    rw [List.pairwise_append]
    refine ⟨?_, List.pairwise_iff_forall_sublist.mpr fun sub y inA _ => empty _ (sub.subset (by simp)) y inA,
      fun _ _ g inG y _ inYG => empty g inG y inYG⟩
    split_ifs
    · exact List.Pairwise.nil
    · exact List.pairwise_singleton _ _

/-- **A hosted process is nested**: the nested fragment contains the hosted one. -/
theorem nestedProcess_of_hosted {P : Pattern} (hostedP : HostedProcess P) : NestedProcess P :=
  ⟨fun c member => nested_of_hosted (hostedP.hosted c member),
    hostedP.disjoint.imp fun {_ _} apart _ inC _ inD y inF inG =>
      apart y (mem_pvars_of_mem_frames inC inF) (mem_pvars_of_mem_frames inD inG)⟩

/-! ## States that represent a bag of nested parts -/

/-- **A state represents a bag of nested parts**, through a part for each present row: every row reads
as its part's representation at every solution of the knowledge; the parts are nested; no two parts'
inputs bind a common variable; every variable of a part occurs in its row's label or in the knowledge;
and every assignment of the parts' variables extends to a solution of the knowledge. -/
structure NestedBy (s : State Tm ℕ) (M : Multiset Pattern) (comp : ℕ → Pattern) : Prop where
  reads : ∀ o ∈ s.present, ∀ σ : PSubst, patternAction.Models σ s.knowledge →
    psubst σ (s.label o) = psubst σ (predot (comp o))
  nested : ∀ o ∈ s.present, Nested (comp o)
  apart : ∀ o ∈ s.present, ∀ o' ∈ s.present, o ≠ o' → FramesDisjoint (comp o) (comp o')
  mentioned : ∀ o ∈ s.present, ∀ y ∈ pvars (comp o), y ∈ pvars (s.label o) ∨ y ∈ storePVars s.knowledge
  free : ∀ τ : PSubst, ∃ σ : PSubst, patternAction.Models σ s.knowledge ∧
    ∀ o ∈ s.present, ∀ y ∈ pvars (comp o), (σ y).getD (.fvar y) = (τ y).getD (.fvar y)
  bag : bagOf s.present comp = M

/-- A state represents a bag of nested parts. -/
def RepresentsNested (s : State Tm ℕ) (M : Multiset Pattern) : Prop := ∃ comp, NestedBy s M comp

theorem mentions_of {s : State Tm ℕ} {o : ℕ} (present : o ∈ s.present) {y : String}
    (occurs : y ∈ pvars (s.label o) ∨ y ∈ storePVars s.knowledge) : ∃ m, s.Mentions m ∧ y ∈ pvars m := by
  rcases occurs with inLabel | inKnown
  · exact ⟨s.label o, .inr (.inr ⟨o, present, rfl⟩), inLabel⟩
  · obtain ⟨e, member, inE⟩ := List.mem_flatMap.mp inKnown
    rcases List.mem_append.mp inE with one | two
    · exact ⟨e.1, .inl (List.mem_map_of_mem member), one⟩
    · exact ⟨e.2, .inr (.inl (List.mem_map_of_mem member)), two⟩

theorem agree_of_mentioned {s : State Tm ℕ} {w g : PSubst}
    (agree : ∀ m, s.Mentions m → psubst w (psubst (fun _ => none) m) = psubst g m)
    {m : Pattern} (mentioned : s.Mentions m) {y : String} (occurs : y ∈ pvars m) :
    (w y).getD (.fvar y) = (g y).getD (.fvar y) := by
  have same := agree m mentioned
  rw [psubst_none] at same
  exact Comm.agree_of_psubst_eq same y occurs

/-- A solution of the heating firing's information that agrees with a solution of the knowledge on every
term the state mentions. -/
theorem heat_amalgamates {s : State Tm ℕ} {ρ : PSubst} {o m₁ m₂ : ℕ}
    (fresh : (heatAt ρ o m₁ m₂).Fresh X s) (present : o ∈ s.present) {σ₀ : PSubst}
    (known : patternAction.Models σ₀ s.knowledge) {a b : Pattern} (reads : psubst σ₀ (s.label o) = par a b) :
    ∃ w : PSubst, patternAction.Models w ((heatAt ρ o m₁ m₂).information X s) ∧
      ∀ m, s.Mentions m → psubst w (psubst (fun _ => none) m) = psubst σ₀ m := by
  let h : PSubst := fun v => if v = "A" then some a else if v = "B" then some b else none
  obtain ⟨w, solved, state, -⟩ := Comm.information_amalgamates_matched (Y := X) (s := s)
    (heatAt ρ o m₁ m₂) fresh (b := PUnit.unit) σ₀ h known
    (fun _ member => (List.not_mem_nil member).elim)
    (fun x member => by
      obtain rfl := List.mem_singleton.mp member
      exact present)
    (fun _ member => (List.not_mem_nil member).elim)
    (fun q member => by
      obtain rfl := List.mem_singleton.mp member
      show psubst h (par leftPart rightPart) = psubst σ₀ (s.label o)
      rw [reads]
      simp [h, leftPart, rightPart, par, MeTTaCalculus.pPar, psubst, MeTTaOperationsComm.psubst.psubstList])
    (fun _ member => (List.not_mem_nil member).elim)
  exact ⟨w, solved, state⟩

/-! ## What each admitted firing does to a represented state of nested parts -/

/-- **The parts of an admitted communication**: two inputs on one channel whose patterns some solution
unifies. -/
theorem comm_shape_nested {s : State Tm ℕ} {M : Multiset Pattern} {comp : ℕ → Pattern}
    (nestedBy : NestedBy s M comp) {ρ : PSubst} {o₁ o₂ m₁ m₂ : ℕ}
    (admitted : (commAt ρ o₁ o₂ m₁ m₂).Admits X s) (madeDistinct : m₁ ≠ m₂)
    (present₁ : o₁ ∈ s.present) (present₂ : o₂ ∈ s.present) :
    ∃ t x A u B, comp o₁ = pFor t x A ∧ comp o₂ = pFor u x B ∧ ∃ σ : PSubst, psubst σ t = psubst σ u := by
  obtain ⟨-, -, ⟨_, σ₀, solved₀⟩, -⟩ := admitted
  have solvedInfo : patternAction.Models σ₀ ((commAt ρ o₁ o₂ m₁ m₂).information X s) := solved₀
  rw [commAt_info] at solvedInfo
  have known₀ : patternAction.Models σ₀ s.knowledge := fun e member => solvedInfo e (by simp [member])
  have take₁ : psubst σ₀ (psubst ρ (pFor firstPattern channelUnknown firstBody)) = psubst σ₀ (s.label o₁) :=
    solvedInfo (psubst ρ (pFor firstPattern channelUnknown firstBody), s.label o₁) (by simp)
  have take₂ : psubst σ₀ (psubst ρ (pFor secondPattern channelUnknown secondBody)) =
      psubst σ₀ (s.label o₂) :=
    solvedInfo (psubst ρ (pFor secondPattern channelUnknown secondBody), s.label o₂) (by simp)
  rw [nestedBy.reads o₁ present₁ σ₀ known₀] at take₁
  rw [nestedBy.reads o₂ present₂ σ₀ known₀] at take₂
  simp only [psubst_pFor] at take₁ take₂
  obtain ⟨t, x, A, first⟩ := closed_input_of_instance (nestedBy.nested o₁ present₁).2.1 take₁.symm
  obtain ⟨u, x', B, second⟩ := closed_input_of_instance (nestedBy.nested o₂ present₂).2.1 take₂.symm
  have nestedFirst := nestedBy.nested o₁ present₁
  rw [first] at nestedFirst
  have nestedSecond := nestedBy.nested o₂ present₂
  rw [second] at nestedSecond
  obtain ⟨groundX, -, -, -, -⟩ := nestedFirst.input
  obtain ⟨groundX', -, -, -, -⟩ := nestedSecond.input
  have resultSolved : patternAction.Models σ₀ ((commAt ρ o₁ o₂ m₁ m₂).result X s).knowledge := solved₀
  obtain ⟨-, unify₀, channel₀, -, -⟩ := comm_reads_inputs s.label t u (predot x) (predot x')
    (dotted (pvars t) (predot A)) (dotted (pvars u) (predot B)) ⟨s.knowledge, s.present⟩ o₁ o₂ m₁ m₂
    (fun σ known => (nestedBy.reads o₁ present₁ σ known).trans (by rw [first, predot_pFor]))
    (fun σ known => (nestedBy.reads o₂ present₂ σ known).trans (by rw [second, predot_pFor]))
    madeDistinct ρ resultSolved
  rw [predot_ground x groundX, predot_ground x' groundX', psubst_of_pvars_nil σ₀ x groundX,
    psubst_of_pvars_nil σ₀ x' groundX'] at channel₀
  subst channel₀
  exact ⟨t, x, A, u, B, first, second, σ₀, unify₀⟩

/-- **What a communication firing does to a represented state of nested parts.** When the two taken rows
hold the inputs `for(t <- x)A` and `for(u <- x)B` and `bs` is a ground principal unifier of the patterns
with first-order values: the inputs satisfy the variable convention, and the result represents the parts
of the dotted continuations beside the other rows' parts. -/
theorem comm_result_nested {s : State Tm ℕ} {M : Multiset Pattern} {comp : ℕ → Pattern}
    (nestedBy : NestedBy s M comp) {ρ : PSubst} {o₁ o₂ m₁ m₂ : ℕ}
    (admitted : (commAt ρ o₁ o₂ m₁ m₂).Admits X s) (distinct : o₁ ≠ o₂) (madeDistinct : m₁ ≠ m₂)
    (present₁ : o₁ ∈ s.present) (present₂ : o₂ ∈ s.present) (fresh₁ : m₁ ∉ s.present)
    (fresh₂ : m₂ ∉ s.present) {t x A u B : Pattern} {bs : Bindings}
    (first : comp o₁ = pFor t x A) (second : comp o₂ = pFor u x B) (gp : GroundPrincipal t u bs)
    (values : ∀ y v, bs.lookup y = some v → firstOrder v = true) :
    Apart t A u B ∧ NestedBy ((commAt ρ o₁ o₂ m₁ m₂).result X s)
      ((parts (applyDot bs A) : Multiset Pattern) + (parts (applyDot bs B) : Multiset Pattern) +
        bagOf (s.present \ {o₁, o₂}) comp)
      (afterComm comp m₁ m₂ (applyDot bs A) (applyDot bs B)) := by
  classical
  obtain ⟨⟨fresh, -⟩, -, -, -⟩ := admitted
  have nestedFirst := nestedBy.nested o₁ present₁
  rw [first] at nestedFirst
  have nestedSecond := nestedBy.nested o₂ present₂
  rw [second] at nestedSecond
  obtain ⟨-, scopedA, keptA, foA, framesA⟩ := nestedFirst.input
  obtain ⟨-, scopedB, keptB, foB, framesB⟩ := nestedSecond.input
  have cross : FramesDisjoint (pFor t x A) (pFor u x B) := by
    have apart := nestedBy.apart o₁ present₁ o₂ present₂ distinct
    rwa [first, second] at apart
  have patternsApart : ∀ y ∈ pvars t, y ∉ pvars u := fun y inT inU =>
    cross (pvars t) (pattern_frame inT) (pvars u) (pattern_frame inU) y inT inU
  have bindersAApart : ∀ y ∈ binders A, y ∉ pvars u := fun y inside inU => by
    obtain ⟨f, inF, yF⟩ := (mem_binders_iff A y).mp inside
    exact cross f (continuation_frame inF) (pvars u) (pattern_frame inU) y yF inU
  have bindersBApart : ∀ y ∈ binders B, y ∉ pvars t := fun y inside inT => by
    obtain ⟨g, inG, yG⟩ := (mem_binders_iff B y).mp inside
    exact cross (pvars t) (pattern_frame inT) g (continuation_frame inG) y inT yG
  have convention : Apart t A u B := by
    refine ⟨patternsApart, fun y inT inB => ?_, fun y inU inA => ?_, keptA, keptB⟩
    · rcases vars_of_scoped B (pvars u) scopedB y inB with inU | inBinders
      · exact patternsApart y inT inU
      · exact bindersBApart y inBinders inT
    · rcases vars_of_scoped A (pvars t) scopedA y inA with inT | inBinders
      · exact patternsApart y inT inU
      · exact bindersAApart y inBinders inU
  have keysOutsideA : ∀ y ∈ binders A, y ∉ pvars t ++ pvars u := fun y inside inKeys => by
    rcases List.mem_append.mp inKeys with inT | inU
    · exact keptA y inT inside
    · exact bindersAApart y inside inU
  have keysOutsideB : ∀ y ∈ binders B, y ∉ pvars t ++ pvars u := fun y inside inKeys => by
    rcases List.mem_append.mp inKeys with inT | inU
    · exact bindersBApart y inside inT
    · exact keptB y inU inside
  obtain ⟨nestedDotA, framesDotA, varsDotA⟩ := nested_applyDot gp values (vs := pvars t)
    (fun y inside => List.mem_append_left _ inside) foA scopedA framesA keysOutsideA
  obtain ⟨nestedDotB, framesDotB, varsDotB⟩ := nested_applyDot gp values (vs := pvars u)
    (fun y inside => List.mem_append_right _ inside) foB scopedB framesB keysOutsideB
  have readsFirst : ∀ σ : PSubst, patternAction.Models σ s.knowledge →
      psubst σ (s.label o₁) = psubst σ (predot (pFor t x A)) := fun σ known =>
    (nestedBy.reads o₁ present₁ σ known).trans (by rw [first])
  have readsSecond : ∀ σ : PSubst, patternAction.Models σ s.knowledge →
      psubst σ (s.label o₂) = psubst σ (predot (pFor u x B)) := fun σ known =>
    (nestedBy.reads o₂ present₂ σ known).trans (by rw [second])
  have reads := fun (σ : PSubst)
      (solved : patternAction.Models σ ((commAt ρ o₁ o₂ m₁ m₂).result X s).knowledge) =>
    comm_reads s.label t u x A B bs gp convention foA foB ⟨s.knowledge, s.present⟩ o₁ o₂ m₁ m₂ readsFirst
      readsSecond madeDistinct ρ solved
  have comp'₁ : afterComm comp m₁ m₂ (applyDot bs A) (applyDot bs B) m₁ = applyDot bs A := by
    simp [afterComm]
  have comp'₂ : afterComm comp m₁ m₂ (applyDot bs A) (applyDot bs B) m₂ = applyDot bs B := by
    simp [afterComm, Ne.symm madeDistinct]
  have notMade : ∀ o ∈ s.present, o ≠ m₁ ∧ o ≠ m₂ := fun o member =>
    ⟨fun same => fresh₁ (same ▸ member), fun same => fresh₂ (same ▸ member)⟩
  have comp'Old : ∀ o ∈ s.present, afterComm comp m₁ m₂ (applyDot bs A) (applyDot bs B) o = comp o := by
    intro o member
    simp [afterComm, (notMade o member).1, (notMade o member).2]
  have resultPresent : ((commAt ρ o₁ o₂ m₁ m₂).result X s).present = (s.present \ {o₁, o₂}) ∪ {m₁, m₂} := by
    show fire s.present ((commSelection o₁ o₂ m₁ m₂).commit (T := Unit)) = _
    simp [fire, Selection.commit, commSelection]
  have labelOld : ∀ o, o ≠ m₁ → o ≠ m₂ → ((commAt ρ o₁ o₂ m₁ m₂).result X s).label o = s.label o := by
    intro o n₁ n₂
    exact result_label_kept s (by simp [commAt, commSelection, n₁, n₂])
  have oldOf : ∀ o ∈ s.present \ {o₁, o₂}, o ∈ s.present ∧ o ≠ o₁ ∧ o ≠ o₂ := by
    intro o member
    obtain ⟨inside, notTaken⟩ := Finset.mem_sdiff.mp member
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at notTaken
    exact ⟨inside, notTaken.1, notTaken.2⟩
  have infoEq := commAt_info s ρ o₁ o₂ m₁ m₂
  have knownGrows : ∀ y ∈ storePVars s.knowledge,
      y ∈ storePVars ((commAt ρ o₁ o₂ m₁ m₂).result X s).knowledge := by
    intro y inside
    show y ∈ storePVars ((commAt ρ o₁ o₂ m₁ m₂).information X s)
    rw [infoEq]
    obtain ⟨e, member, occurs⟩ := List.mem_flatMap.mp inside
    exact List.mem_flatMap.mpr ⟨e, by simp [member], occurs⟩
  have label₁Known : ∀ y ∈ pvars (s.label o₁),
      y ∈ storePVars ((commAt ρ o₁ o₂ m₁ m₂).result X s).knowledge := by
    intro y inside
    show y ∈ storePVars ((commAt ρ o₁ o₂ m₁ m₂).information X s)
    rw [infoEq]
    exact mem_storePVars (e := (psubst ρ (pFor firstPattern channelUnknown firstBody), s.label o₁))
      (by simp) (.inr inside)
  have label₂Known : ∀ y ∈ pvars (s.label o₂),
      y ∈ storePVars ((commAt ρ o₁ o₂ m₁ m₂).result X s).knowledge := by
    intro y inside
    show y ∈ storePVars ((commAt ρ o₁ o₂ m₁ m₂).information X s)
    rw [infoEq]
    exact mem_storePVars (e := (psubst ρ (pFor secondPattern channelUnknown secondBody), s.label o₂))
      (by simp) (.inr inside)
  have fromFirst : ∀ y ∈ pvars (applyDot bs A), y ∈ pvars (comp o₁) ∧ y ∉ pvars t ++ pvars u := by
    intro y inside
    obtain ⟨inA, notKey⟩ := varsDotA y inside
    refine ⟨?_, notKey⟩
    rw [first, pvars_pFor]
    exact List.mem_append_right _ inA
  have fromSecond : ∀ y ∈ pvars (applyDot bs B), y ∈ pvars (comp o₂) ∧ y ∉ pvars t ++ pvars u := by
    intro y inside
    obtain ⟨inB, notKey⟩ := varsDotB y inside
    refine ⟨?_, notKey⟩
    rw [second, pvars_pFor]
    exact List.mem_append_right _ inB
  have origin : ∀ o ∈ ((commAt ρ o₁ o₂ m₁ m₂).result X s).present,
      ∀ y ∈ pvars (afterComm comp m₁ m₂ (applyDot bs A) (applyDot bs B) o),
        ∃ o' ∈ s.present, y ∈ pvars (comp o') ∧ y ∉ pvars t ++ pvars u := by
    intro o member y inside
    rw [resultPresent] at member
    rcases Finset.mem_union.mp member with old | new
    · obtain ⟨oPresent, notFirst, notSecond⟩ := oldOf o old
      rw [comp'Old o oPresent] at inside
      refine ⟨o, oPresent, inside, fun inKeys => ?_⟩
      rcases List.mem_append.mp inKeys with inT | inU
      · have inComp₁ : y ∈ pvars (comp o₁) := by
          rw [first, pvars_pFor]
          exact List.mem_append_left _ (List.mem_append_left _ inT)
        exact vars_disjoint (nestedBy.nested o oPresent).2.1 (nestedBy.nested o₁ present₁).2.1
          (nestedBy.apart o oPresent o₁ present₁ notFirst) inside inComp₁
      · have inComp₂ : y ∈ pvars (comp o₂) := by
          rw [second, pvars_pFor]
          exact List.mem_append_left _ (List.mem_append_left _ inU)
        exact vars_disjoint (nestedBy.nested o oPresent).2.1 (nestedBy.nested o₂ present₂).2.1
          (nestedBy.apart o oPresent o₂ present₂ notSecond) inside inComp₂
    · simp only [Finset.mem_insert, Finset.mem_singleton] at new
      rcases new with rfl | rfl
      · rw [comp'₁] at inside
        obtain ⟨inComp, notKey⟩ := fromFirst y inside
        exact ⟨o₁, present₁, inComp, notKey⟩
      · rw [comp'₂] at inside
        obtain ⟨inComp, notKey⟩ := fromSecond y inside
        exact ⟨o₂, present₂, inComp, notKey⟩
  have aSub : ∀ g ∈ frames (applyDot bs A), g ∈ frames (comp o₁) := fun g inG => by
    rw [framesDotA] at inG
    rw [first]
    exact continuation_frame inG
  have bSub : ∀ g ∈ frames (applyDot bs B), g ∈ frames (comp o₂) := fun g inG => by
    rw [framesDotB] at inG
    rw [second]
    exact continuation_frame inG
  have dotsApart : FramesDisjoint (applyDot bs A) (applyDot bs B) :=
    (((nestedBy.apart o₁ present₁ o₂ present₂ distinct).mono bSub).symm.mono aSub).symm
  refine ⟨convention, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · -- readings
    intro o member σ solved
    rw [resultPresent] at member
    rcases Finset.mem_union.mp member with old | new
    · obtain ⟨inside, -, -⟩ := oldOf o old
      rw [labelOld o (notMade o inside).1 (notMade o inside).2, comp'Old o inside]
      exact nestedBy.reads o inside σ (reads σ solved).1
    · simp only [Finset.mem_insert, Finset.mem_singleton] at new
      rcases new with rfl | rfl
      · rw [comp'₁]
        exact (reads σ solved).2.2.1
      · rw [comp'₂]
        exact (reads σ solved).2.2.2
  · -- the parts are nested
    intro o member
    rw [resultPresent] at member
    rcases Finset.mem_union.mp member with old | new
    · obtain ⟨inside, -, -⟩ := oldOf o old
      rw [comp'Old o inside]
      exact nestedBy.nested o inside
    · simp only [Finset.mem_insert, Finset.mem_singleton] at new
      rcases new with rfl | rfl
      · rw [comp'₁]; exact nestedDotA
      · rw [comp'₂]; exact nestedDotB
  · -- no two parts' inputs bind a common variable
    intro o member o' member' different
    rw [resultPresent] at member member'
    rcases Finset.mem_union.mp member with old | new <;>
      rcases Finset.mem_union.mp member' with old' | new'
    · obtain ⟨inside, -, -⟩ := oldOf o old
      obtain ⟨inside', -, -⟩ := oldOf o' old'
      rw [comp'Old o inside, comp'Old o' inside']
      exact nestedBy.apart o inside o' inside' different
    · obtain ⟨inside, notFirst, notSecond⟩ := oldOf o old
      rw [comp'Old o inside]
      simp only [Finset.mem_insert, Finset.mem_singleton] at new'
      rcases new' with rfl | rfl
      · rw [comp'₁]; exact (nestedBy.apart o inside o₁ present₁ notFirst).mono aSub
      · rw [comp'₂]; exact (nestedBy.apart o inside o₂ present₂ notSecond).mono bSub
    · obtain ⟨inside', notFirst', notSecond'⟩ := oldOf o' old'
      rw [comp'Old o' inside']
      simp only [Finset.mem_insert, Finset.mem_singleton] at new
      rcases new with rfl | rfl
      · rw [comp'₁]; exact ((nestedBy.apart o' inside' o₁ present₁ notFirst').mono aSub).symm
      · rw [comp'₂]; exact ((nestedBy.apart o' inside' o₂ present₂ notSecond').mono bSub).symm
    · simp only [Finset.mem_insert, Finset.mem_singleton] at new new'
      rcases new with rfl | rfl <;> rcases new' with rfl | rfl
      · exact absurd rfl different
      · rw [comp'₁, comp'₂]; exact dotsApart
      · rw [comp'₂, comp'₁]; exact dotsApart.symm
      · exact absurd rfl different
  · -- every variable of a part is mentioned
    intro o member y inside
    rw [resultPresent] at member
    rcases Finset.mem_union.mp member with old | new
    · obtain ⟨oPresent, -, -⟩ := oldOf o old
      rw [comp'Old o oPresent] at inside
      rw [labelOld o (notMade o oPresent).1 (notMade o oPresent).2]
      rcases nestedBy.mentioned o oPresent y inside with inLabel | inKnown
      · exact .inl inLabel
      · exact .inr (knownGrows y inKnown)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at new
      rcases new with rfl | rfl
      · rw [comp'₁] at inside
        refine .inr ?_
        rcases nestedBy.mentioned o₁ present₁ y (fromFirst y inside).1 with inLabel | inKnown
        · exact label₁Known y inLabel
        · exact knownGrows y inKnown
      · rw [comp'₂] at inside
        refine .inr ?_
        rcases nestedBy.mentioned o₂ present₂ y (fromSecond y inside).1 with inLabel | inKnown
        · exact label₂Known y inLabel
        · exact knownGrows y inKnown
  · -- every assignment of the parts' variables extends to a solution
    intro τ
    let τ₁ : PSubst := fun y => if y ∈ pvars t ++ pvars u then bs.lookup y else τ y
    obtain ⟨σ₁, known₁, agree₁⟩ := nestedBy.free τ₁
    have onKeys : ∀ y ∈ pvars t ++ pvars u, (σ₁ y).getD (.fvar y) = (bs.lookup y).getD (.fvar y) := by
      intro y inKeys
      have inComp : ∃ o ∈ s.present, y ∈ pvars (comp o) := by
        rcases List.mem_append.mp inKeys with inT | inU
        · exact ⟨o₁, present₁, by
            rw [first, pvars_pFor]; exact List.mem_append_left _ (List.mem_append_left _ inT)⟩
        · exact ⟨o₂, present₂, by
            rw [second, pvars_pFor]; exact List.mem_append_left _ (List.mem_append_left _ inU)⟩
      obtain ⟨o, oPresent, inO⟩ := inComp
      rw [agree₁ o oPresent y inO]
      show (if y ∈ pvars t ++ pvars u then bs.lookup y else τ y).getD (.fvar y) = _
      rw [if_pos inKeys]
    have unify₁ : psubst σ₁ t = psubst σ₁ u := by
      rw [MeTTaCalculus.Corrected.psubst_getD_congr_on (τ := bs.lookup) (p := t)
          fun y inT => onKeys y (List.mem_append_left _ inT),
        MeTTaCalculus.Corrected.psubst_getD_congr_on (τ := bs.lookup) (p := u)
          fun y inU => onKeys y (List.mem_append_right _ inU)]
      exact gp.solves
    obtain ⟨w, solved, state⟩ := comm_amalgamates s.label t u (predot x)
      (dotted (pvars t) (predot A)) (dotted (pvars u) (predot B)) ⟨s.knowledge, s.present⟩ o₁ o₂ m₁ m₂
      (fun σ known => (readsFirst σ known).trans (by rw [predot_pFor]))
      (fun σ known => (readsSecond σ known).trans (by rw [predot_pFor])) present₁ present₂ known₁ unify₁
      fresh
    refine ⟨w, solved, fun o member y inside => ?_⟩
    obtain ⟨o', oPresent, inO, notKey⟩ := origin o member y inside
    obtain ⟨m, mentioned, inM⟩ := mentions_of oPresent (nestedBy.mentioned o' oPresent y inO)
    rw [agree_of_mentioned state mentioned inM, agree₁ o' oPresent y inO]
    show (if y ∈ pvars t ++ pvars u then bs.lookup y else τ y).getD (.fvar y) = _
    rw [if_neg notKey]
  · -- the bag after
    rw [resultPresent]
    unfold bagOf
    have apartSets : Disjoint (s.present \ {o₁, o₂}) ({m₁, m₂} : Finset ℕ) := by
      rw [Finset.disjoint_left]
      intro o inside made
      simp only [Finset.mem_insert, Finset.mem_singleton] at made
      rcases made with rfl | rfl
      · exact fresh₁ (Finset.mem_sdiff.mp inside).1
      · exact fresh₂ (Finset.mem_sdiff.mp inside).1
    rw [Finset.sum_union apartSets, Finset.sum_pair madeDistinct, comp'₁, comp'₂,
      Finset.sum_congr rfl fun o member => by rw [comp'Old o (Finset.mem_sdiff.mp member).1]]
    abel

/-- **What a heating firing does to a represented state of nested parts**: the bag is kept and the weight
decreases. -/
theorem heat_result_nested {s : State Tm ℕ} {M : Multiset Pattern} {comp : ℕ → Pattern}
    (nestedBy : NestedBy s M comp) {ρ : PSubst} {o m₁ m₂ : ℕ}
    (admitted : (heatAt ρ o m₁ m₂).Admits X s) (madeDistinct : m₁ ≠ m₂) (present : o ∈ s.present)
    (fresh₁ : m₁ ∉ s.present) (fresh₂ : m₂ ∉ s.present) :
    ∃ comp' : ℕ → Pattern, NestedBy ((heatAt ρ o m₁ m₂).result X s) M comp' ∧
      weightOf ((heatAt ρ o m₁ m₂).result X s).present comp' < weightOf s.present comp := by
  classical
  obtain ⟨⟨fresh, -⟩, -, ⟨_, σ₀, solved₀⟩, -⟩ := admitted
  have solvedInfo : patternAction.Models σ₀ ((heatAt ρ o m₁ m₂).information X s) := solved₀
  rw [heatAt_info] at solvedInfo
  have known₀ : patternAction.Models σ₀ s.knowledge := fun e member => solvedInfo e (by simp [member])
  have take₀ : psubst σ₀ (psubst ρ (par leftPart rightPart)) = psubst σ₀ (s.label o) :=
    solvedInfo (psubst ρ (par leftPart rightPart), s.label o) (by simp)
  rw [nestedBy.reads o present σ₀ known₀] at take₀
  simp only [MeTTaOperationsComm.psubst_par] at take₀
  obtain ⟨a, b, shape⟩ := closed_par_of_instance (nestedBy.nested o present).2.1 take₀.symm
  have nestedPar := nestedBy.nested o present
  rw [shape] at nestedPar
  obtain ⟨nestedA, nestedB, crossAB⟩ := nestedPar.parts_of_par
  let comp' : ℕ → Pattern := fun x => if x = m₁ then a else if x = m₂ then b else comp x
  have comp'₁ : comp' m₁ = a := by simp [comp']
  have comp'₂ : comp' m₂ = b := by simp [comp', Ne.symm madeDistinct]
  have notMade : ∀ x ∈ s.present, x ≠ m₁ ∧ x ≠ m₂ := fun x member =>
    ⟨fun same => fresh₁ (same ▸ member), fun same => fresh₂ (same ▸ member)⟩
  have comp'Old : ∀ x ∈ s.present, comp' x = comp x := by
    intro x member
    simp [comp', (notMade x member).1, (notMade x member).2]
  have resultPresent : ((heatAt ρ o m₁ m₂).result X s).present = (s.present \ {o}) ∪ {m₁, m₂} := by
    show fire s.present (Selection.commit (T := Unit) ⟨[o], [], [m₁, m₂]⟩) = _
    simp [fire, Selection.commit]
  have labelOld : ∀ x, x ≠ m₁ → x ≠ m₂ → ((heatAt ρ o m₁ m₂).result X s).label x = s.label x := by
    intro x n₁ n₂
    exact result_label_kept s (by simp [heatAt, n₁, n₂])
  have aSub : ∀ g ∈ frames a, g ∈ frames (comp o) := fun g inG => by
    rw [shape, frames_par]
    exact List.mem_append_left _ inG
  have bSub : ∀ g ∈ frames b, g ∈ frames (comp o) := fun g inG => by
    rw [shape, frames_par]
    exact List.mem_append_right _ inG
  have aVars : ∀ y ∈ pvars a, y ∈ pvars (comp o) := fun y inside => by
    rw [shape, MeTTaCalculus.Corrected.pvars_par]
    exact List.mem_append_left _ inside
  have bVars : ∀ y ∈ pvars b, y ∈ pvars (comp o) := fun y inside => by
    rw [shape, MeTTaCalculus.Corrected.pvars_par]
    exact List.mem_append_right _ inside
  have readsMade : ∀ σ : PSubst, patternAction.Models σ ((heatAt ρ o m₁ m₂).result X s).knowledge →
      patternAction.Models σ s.knowledge ∧ psubst σ (psubst ρ leftPart) = psubst σ (predot a) ∧
        psubst σ (psubst ρ rightPart) = psubst σ (predot b) := by
    intro σ solved
    have solvedσ : patternAction.Models σ ((heatAt ρ o m₁ m₂).information X s) := solved
    rw [heatAt_info] at solvedσ
    have knownσ : patternAction.Models σ s.knowledge := fun e member => solvedσ e (by simp [member])
    have takeσ : psubst σ (psubst ρ (par leftPart rightPart)) = psubst σ (s.label o) :=
      solvedσ (psubst ρ (par leftPart rightPart), s.label o) (by simp)
    rw [nestedBy.reads o present σ knownσ, shape, predot_par] at takeσ
    simp only [MeTTaOperationsComm.psubst_par] at takeσ
    have partsSame : psubst σ (psubst ρ leftPart) = psubst σ (predot a) ∧
        psubst σ (psubst ρ rightPart) = psubst σ (predot b) := by
      simpa [par, MeTTaCalculus.pPar] using takeσ
    exact ⟨knownσ, partsSame.1, partsSame.2⟩
  have knownGrows : ∀ y ∈ storePVars s.knowledge,
      y ∈ storePVars ((heatAt ρ o m₁ m₂).result X s).knowledge := by
    intro y inside
    show y ∈ storePVars ((heatAt ρ o m₁ m₂).information X s)
    rw [heatAt_info]
    obtain ⟨e, member, occurs⟩ := List.mem_flatMap.mp inside
    exact List.mem_flatMap.mpr ⟨e, by simp [member], occurs⟩
  have labelKnown : ∀ y ∈ pvars (s.label o), y ∈ storePVars ((heatAt ρ o m₁ m₂).result X s).knowledge := by
    intro y inside
    show y ∈ storePVars ((heatAt ρ o m₁ m₂).information X s)
    rw [heatAt_info]
    exact mem_storePVars (e := (psubst ρ (par leftPart rightPart), s.label o)) (by simp) (.inr inside)
  have origin : ∀ x ∈ ((heatAt ρ o m₁ m₂).result X s).present, ∀ y ∈ pvars (comp' x),
      ∃ x' ∈ s.present, y ∈ pvars (comp x') := by
    intro x member y inside
    rw [resultPresent] at member
    rcases Finset.mem_union.mp member with old | new
    · have xPresent := (Finset.mem_sdiff.mp old).1
      rw [comp'Old x xPresent] at inside
      exact ⟨x, xPresent, inside⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at new
      rcases new with rfl | rfl
      · rw [comp'₁] at inside
        exact ⟨o, present, aVars y inside⟩
      · rw [comp'₂] at inside
        exact ⟨o, present, bVars y inside⟩
  have apartSets : Disjoint (s.present \ {o}) ({m₁, m₂} : Finset ℕ) := by
    rw [Finset.disjoint_left]
    intro x inside made
    simp only [Finset.mem_insert, Finset.mem_singleton] at made
    rcases made with rfl | rfl
    · exact fresh₁ (Finset.mem_sdiff.mp inside).1
    · exact fresh₂ (Finset.mem_sdiff.mp inside).1
  have oldOf : ∀ x ∈ s.present \ {o}, x ∈ s.present ∧ x ≠ o := fun x member =>
    ⟨(Finset.mem_sdiff.mp member).1, fun same => (Finset.mem_sdiff.mp member).2 (by simp [same])⟩
  refine ⟨comp', ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro x member σ solved
    rw [resultPresent] at member
    rcases Finset.mem_union.mp member with old | new
    · obtain ⟨inside, -⟩ := oldOf x old
      rw [labelOld x (notMade x inside).1 (notMade x inside).2, comp'Old x inside]
      exact nestedBy.reads x inside σ (readsMade σ solved).1
    · simp only [Finset.mem_insert, Finset.mem_singleton] at new
      rcases new with rfl | rfl
      · rw [comp'₁, heatAt_label₁]
        exact (readsMade σ solved).2.1
      · rw [comp'₂, heatAt_label₂ s ρ o madeDistinct]
        exact (readsMade σ solved).2.2
  · intro x member
    rw [resultPresent] at member
    rcases Finset.mem_union.mp member with old | new
    · obtain ⟨inside, -⟩ := oldOf x old
      rw [comp'Old x inside]
      exact nestedBy.nested x inside
    · simp only [Finset.mem_insert, Finset.mem_singleton] at new
      rcases new with rfl | rfl
      · rw [comp'₁]; exact nestedA
      · rw [comp'₂]; exact nestedB
  · intro x member x' member' different
    rw [resultPresent] at member member'
    rcases Finset.mem_union.mp member with old | new <;>
      rcases Finset.mem_union.mp member' with old' | new'
    · obtain ⟨inside, -⟩ := oldOf x old
      obtain ⟨inside', -⟩ := oldOf x' old'
      rw [comp'Old x inside, comp'Old x' inside']
      exact nestedBy.apart x inside x' inside' different
    · obtain ⟨inside, notO⟩ := oldOf x old
      rw [comp'Old x inside]
      simp only [Finset.mem_insert, Finset.mem_singleton] at new'
      rcases new' with rfl | rfl
      · rw [comp'₁]; exact (nestedBy.apart x inside o present notO).mono aSub
      · rw [comp'₂]; exact (nestedBy.apart x inside o present notO).mono bSub
    · obtain ⟨inside', notO'⟩ := oldOf x' old'
      rw [comp'Old x' inside']
      simp only [Finset.mem_insert, Finset.mem_singleton] at new
      rcases new with rfl | rfl
      · rw [comp'₁]; exact ((nestedBy.apart x' inside' o present notO').mono aSub).symm
      · rw [comp'₂]; exact ((nestedBy.apart x' inside' o present notO').mono bSub).symm
    · simp only [Finset.mem_insert, Finset.mem_singleton] at new new'
      rcases new with rfl | rfl <;> rcases new' with rfl | rfl
      · exact absurd rfl different
      · rw [comp'₁, comp'₂]; exact crossAB
      · rw [comp'₂, comp'₁]; exact crossAB.symm
      · exact absurd rfl different
  · intro x member y inside
    rw [resultPresent] at member
    rcases Finset.mem_union.mp member with old | new
    · obtain ⟨xPresent, -⟩ := oldOf x old
      rw [comp'Old x xPresent] at inside
      rw [labelOld x (notMade x xPresent).1 (notMade x xPresent).2]
      rcases nestedBy.mentioned x xPresent y inside with inLabel | inKnown
      · exact .inl inLabel
      · exact .inr (knownGrows y inKnown)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at new
      have fromPar : y ∈ pvars (comp o) := by
        rcases new with rfl | rfl
        · rw [comp'₁] at inside; exact aVars y inside
        · rw [comp'₂] at inside; exact bVars y inside
      refine .inr ?_
      rcases nestedBy.mentioned o present y fromPar with inLabel | inKnown
      · exact labelKnown y inLabel
      · exact knownGrows y inKnown
  · intro τ
    obtain ⟨σ₁, known₁, agree₁⟩ := nestedBy.free τ
    have readsPar : psubst σ₁ (s.label o) = par (psubst σ₁ (predot a)) (psubst σ₁ (predot b)) := by
      rw [nestedBy.reads o present σ₁ known₁, shape, predot_par, MeTTaOperationsComm.psubst_par]
    obtain ⟨w, solved, state⟩ := heat_amalgamates fresh present known₁ readsPar
    refine ⟨w, solved, fun x member y inside => ?_⟩
    obtain ⟨x', xPresent, inX⟩ := origin x member y inside
    obtain ⟨m, mentioned, inM⟩ := mentions_of xPresent (nestedBy.mentioned x' xPresent y inX)
    rw [agree_of_mentioned state mentioned inM, agree₁ x' xPresent y inX]
  · rw [← nestedBy.bag, resultPresent]
    unfold bagOf
    rw [Finset.sum_union apartSets, Finset.sum_pair madeDistinct, comp'₁, comp'₂,
      Finset.sum_congr rfl fun x member => by rw [comp'Old x (Finset.mem_sdiff.mp member).1],
      ← Finset.sum_sdiff (Finset.singleton_subset_iff.mpr present) (s₂ := s.present), Finset.sum_singleton,
      shape, parts_par, ← Multiset.coe_add]
  · rw [resultPresent]
    unfold weightOf
    rw [Finset.sum_union apartSets, Finset.sum_pair madeDistinct, comp'₁, comp'₂,
      Finset.sum_congr rfl fun x member => by rw [comp'Old x (Finset.mem_sdiff.mp member).1],
      ← Finset.sum_sdiff (Finset.singleton_subset_iff.mpr present) (s₂ := s.present)
        (f := fun x => weight (comp x)), Finset.sum_singleton, shape, weight_par]
    omega

/-- **What a clearing firing does to a represented state of nested parts**: the bag is kept and the weight
decreases. -/
theorem clear_result_nested {s : State Tm ℕ} {M : Multiset Pattern} {comp : ℕ → Pattern}
    (nestedBy : NestedBy s M comp) {ρ : PSubst} {o : ℕ}
    (admitted : (clearAt ρ o).Admits X s) (present : o ∈ s.present) :
    NestedBy ((clearAt ρ o).result X s) M comp ∧
      weightOf ((clearAt ρ o).result X s).present comp < weightOf s.present comp := by
  classical
  obtain ⟨-, -, ⟨_, σ₀, solved₀⟩, -⟩ := admitted
  have solvedInfo : patternAction.Models σ₀ ((clearAt ρ o).information X s) := solved₀
  rw [clearAt_info] at solvedInfo
  have known₀ : patternAction.Models σ₀ s.knowledge := fun e member => solvedInfo e (by simp [member])
  have take₀ : psubst σ₀ (psubst ρ pZero) = psubst σ₀ (s.label o) :=
    solvedInfo (psubst ρ pZero, s.label o) (by simp)
  rw [nestedBy.reads o present σ₀ known₀, MeTTaOperationsComm.psubst_pZero,
    MeTTaOperationsComm.psubst_pZero] at take₀
  have shape := closed_zero_of_instance (nestedBy.nested o present).2.1 take₀.symm
  have resultPresent : ((clearAt ρ o).result X s).present = s.present \ {o} := by
    show fire s.present (Selection.commit (T := Unit) ⟨[o], [], []⟩) = _
    simp [fire, Selection.commit]
  have labelOld : ∀ x, ((clearAt ρ o).result X s).label x = s.label x := fun x =>
    result_label_kept s (by simp [clearAt])
  have knownOf : ∀ σ : PSubst, patternAction.Models σ ((clearAt ρ o).result X s).knowledge →
      patternAction.Models σ s.knowledge := by
    intro σ solved
    have solvedσ : patternAction.Models σ ((clearAt ρ o).information X s) := solved
    rw [clearAt_info] at solvedσ
    exact fun e member => solvedσ e (by simp [member])
  have knownGrows : ∀ y ∈ storePVars s.knowledge, y ∈ storePVars ((clearAt ρ o).result X s).knowledge := by
    intro y inside
    show y ∈ storePVars ((clearAt ρ o).information X s)
    rw [clearAt_info]
    obtain ⟨e, member, occurs⟩ := List.mem_flatMap.mp inside
    exact List.mem_flatMap.mpr ⟨e, by simp [member], occurs⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro x member σ solved
    rw [resultPresent] at member
    rw [labelOld x]
    exact nestedBy.reads x (Finset.mem_sdiff.mp member).1 σ (knownOf σ solved)
  · intro x member
    rw [resultPresent] at member
    exact nestedBy.nested x (Finset.mem_sdiff.mp member).1
  · intro x member x' member' different
    rw [resultPresent] at member member'
    exact nestedBy.apart x (Finset.mem_sdiff.mp member).1 x' (Finset.mem_sdiff.mp member').1 different
  · intro x member y inside
    rw [resultPresent] at member
    rw [labelOld x]
    rcases nestedBy.mentioned x (Finset.mem_sdiff.mp member).1 y inside with inLabel | inKnown
    · exact .inl inLabel
    · exact .inr (knownGrows y inKnown)
  · intro τ
    obtain ⟨σ₁, known₁, agree₁⟩ := nestedBy.free τ
    refine ⟨σ₁, ?_, fun x member y inside => ?_⟩
    · show patternAction.Models σ₁ ((clearAt ρ o).information X s)
      rw [clearAt_info]
      intro e member
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with known | rfl
      · exact known₁ e known
      · show psubst σ₁ (psubst ρ pZero) = psubst σ₁ (s.label o)
        rw [nestedBy.reads o present σ₁ known₁, shape, predot_pZero]
        rfl
    · rw [resultPresent] at member
      exact agree₁ x (Finset.mem_sdiff.mp member).1 y inside
  · rw [← nestedBy.bag, resultPresent]
    unfold bagOf
    rw [← Finset.sum_sdiff (Finset.singleton_subset_iff.mpr present) (s₂ := s.present),
      Finset.sum_singleton, shape, parts_pZero]
    simp
  · rw [resultPresent]
    unfold weightOf
    rw [← Finset.sum_sdiff (Finset.singleton_subset_iff.mpr present) (s₂ := s.present)
      (f := fun x => weight (comp x)), Finset.sum_singleton, shape, weight_pZero]
    omega

/-! ## Existence of firings at represented states of nested parts -/

/-- **Communication fires between two rows holding inputs on one channel whose patterns have a ground
principal unifier.** -/
theorem comm_exists_nested {s : State Tm ℕ} {M : Multiset Pattern} {comp : ℕ → Pattern}
    (nestedBy : NestedBy s M comp) {o₁ o₂ : ℕ} (present₁ : o₁ ∈ s.present)
    (present₂ : o₂ ∈ s.present) (distinct : o₁ ≠ o₂) {t x A u B : Pattern} {bs : Bindings}
    (first : comp o₁ = pFor t x A) (second : comp o₂ = pFor u x B) (gp : GroundPrincipal t u bs) :
    ∃ ρ m₁ m₂, (commAt ρ o₁ o₂ m₁ m₂).Admits X s ∧ m₁ ≠ m₂ ∧ m₁ ∉ s.present ∧ m₂ ∉ s.present := by
  obtain ⟨m₁, m₂, fresh₁, fresh₂, madeDistinct⟩ := two_fresh s.present
  obtain ⟨ρ, opensFreshly⟩ := exists_fresh_opening s.label ⟨s.knowledge, s.present⟩ o₁ o₂ m₁ m₂
  obtain ⟨σ₀, known, agree⟩ := nestedBy.free bs.lookup
  have unifies : psubst σ₀ t = psubst σ₀ u := by
    rw [MeTTaCalculus.Corrected.psubst_getD_congr_on (τ := bs.lookup) (p := t) fun y inT =>
        agree o₁ present₁ y (by
          rw [first, pvars_pFor]; exact List.mem_append_left _ (List.mem_append_left _ inT)),
      MeTTaCalculus.Corrected.psubst_getD_congr_on (τ := bs.lookup) (p := u) fun y inU =>
        agree o₂ present₂ y (by
          rw [second, pvars_pFor]; exact List.mem_append_left _ (List.mem_append_left _ inU))]
    exact gp.solves
  exact ⟨ρ, m₁, m₂, comm_admits s.label t u x A B ⟨s.knowledge, s.present⟩ o₁ o₂ m₁ m₂
    (fun σ known => (nestedBy.reads o₁ present₁ σ known).trans (by rw [first]))
    (fun σ known => (nestedBy.reads o₂ present₂ σ known).trans (by rw [second]))
    distinct madeDistinct present₁ present₂ fresh₁ fresh₂ known unifies opensFreshly,
    madeDistinct, fresh₁, fresh₂⟩

/-- **Heating fires at every row whose part is a binary parallel composition.** -/
theorem heat_exists_nested {s : State Tm ℕ} {M : Multiset Pattern} {comp : ℕ → Pattern}
    (nestedBy : NestedBy s M comp) {o : ℕ} (present : o ∈ s.present) {a b : Pattern}
    (shape : comp o = par a b) :
    ∃ ρ m₁ m₂, (heatAt ρ o m₁ m₂).Admits X s ∧ m₁ ≠ m₂ ∧ m₁ ∉ s.present ∧ m₂ ∉ s.present := by
  classical
  obtain ⟨g, injective, avoids⟩ := Comm.exists_apart_renaming s (ruleVars heatRule)
  obtain ⟨m₁, m₂, fresh₁, fresh₂, madeDistinct⟩ := two_fresh s.present
  have freshAt : (heatAt (renameBy g) o m₁ m₂).Fresh X s :=
    Comm.fresh_of_renaming s (heatAt (renameBy g) o m₁ m₂) g rfl injective avoids
  obtain ⟨σ₀, known, -⟩ := nestedBy.free (fun _ => none)
  have readsPar : psubst σ₀ (s.label o) = par (psubst σ₀ (predot a)) (psubst σ₀ (predot b)) := by
    rw [nestedBy.reads o present σ₀ known, shape, predot_par, MeTTaOperationsComm.psubst_par]
  obtain ⟨w, solved, -⟩ := heat_amalgamates freshAt present known readsPar
  refine ⟨renameBy g, m₁, m₂, (RuleSyntax.admits_iff _).mpr ⟨freshAt,
    ⟨by simp [heatAt], by simp [heatAt, madeDistinct], rfl, rfl, rfl, rfl⟩,
    ⟨?_, ?_, ?_, ?_, fun query member => by simp [Selection.commit] at member⟩,
    ⟨PUnit.unit, w, solved⟩, fun _ member => (List.not_mem_nil member).elim,
    fun _ member => (List.not_mem_nil member).elim⟩, madeDistinct, fresh₁, fresh₂⟩
  · intro x member
    simp only [heatAt, Selection.commit, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
      Finset.mem_singleton] at member
    subst member
    exact present
  · intro x member
    simp [heatAt, Selection.commit] at member
  · simp [heatAt, Selection.commit]
  · rw [Finset.disjoint_left]
    intro x member
    simp only [heatAt, Selection.commit, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
      Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl
    · exact fresh₁
    · exact fresh₂

/-- **Clearing fires at every row whose part is `0`.** -/
theorem clear_exists_nested {s : State Tm ℕ} {M : Multiset Pattern} {comp : ℕ → Pattern}
    (nestedBy : NestedBy s M comp) {o : ℕ} (present : o ∈ s.present) (shape : comp o = pZero) :
    ∃ ρ, (clearAt ρ o).Admits X s := by
  classical
  obtain ⟨g, injective, avoids⟩ := Comm.exists_apart_renaming s (ruleVars clearRule)
  have freshAt : (clearAt (renameBy g) o).Fresh X s :=
    Comm.fresh_of_renaming s (clearAt (renameBy g) o) g rfl injective avoids
  obtain ⟨σ₀, known, -⟩ := nestedBy.free (fun _ => none)
  have solvedInfo : patternAction.Models σ₀ ((clearAt (renameBy g) o).information X s) := by
    rw [clearAt_info]
    intro e member
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with inKnown | rfl
    · exact known e inKnown
    · show psubst σ₀ (psubst (renameBy g) pZero) = psubst σ₀ (s.label o)
      rw [nestedBy.reads o present σ₀ known, shape, predot_pZero]
      rfl
  refine ⟨renameBy g, (RuleSyntax.admits_iff _).mpr ⟨freshAt,
    ⟨by simp [clearAt], by simp [clearAt], rfl, rfl, rfl, rfl⟩,
    ⟨?_, ?_, ?_, ?_, fun query member => by simp [Selection.commit] at member⟩,
    ⟨PUnit.unit, σ₀, solvedInfo⟩, fun _ member => (List.not_mem_nil member).elim,
    fun _ member => (List.not_mem_nil member).elim⟩⟩
  · intro x member
    simp only [clearAt, Selection.commit, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
      Finset.mem_singleton] at member
    subst member
    exact present
  · intro x member
    simp [clearAt, Selection.commit] at member
  · simp [clearAt, Selection.commit]
  · simp [clearAt, Selection.commit]

/-! ## Housekeeping -/

/-- **Housekeeping keeps the represented bag and decreases the weight.** -/
theorem administration_decreases_nested {s s' : State Tm ℕ} {M : Multiset Pattern} {comp : ℕ → Pattern}
    (nestedBy : NestedBy s M comp) (fires : Administers s s') :
    ∃ comp' : ℕ → Pattern, NestedBy s' M comp' ∧ weightOf s'.present comp' < weightOf s.present comp := by
  obtain ⟨f, kind, admitted, rfl⟩ := fires
  rcases kind with isHeat | isClear
  · obtain ⟨o, m₁, m₂, same, madeDistinct, present, fresh₁, fresh₂⟩ := heat_normal f isHeat admitted
    rw [same] at admitted ⊢
    exact heat_result_nested nestedBy admitted madeDistinct present fresh₁ fresh₂
  · obtain ⟨o, same, present⟩ := clear_normal f isClear admitted
    rw [same] at admitted ⊢
    exact ⟨comp, clear_result_nested nestedBy admitted present⟩

/-- **Housekeeping is bounded** by the spine weight. -/
theorem administration_bounded_nested {s e : State Tm ℕ} {M : Multiset Pattern} {comp : ℕ → Pattern}
    {k : ℕ} (nestedBy : NestedBy s M comp) (run : AdministrativeRun k s e) : k ≤ weightOf s.present comp := by
  induction run generalizing comp with
  | refl => exact Nat.zero_le _
  | head fires _ earlier =>
      obtain ⟨comp', nestedBy', lighter⟩ := administration_decreases_nested nestedBy fires
      have bound := earlier nestedBy'
      omega

/-- **Heating reaches parts.** -/
theorem heats_to_parts_nested {s : State Tm ℕ} {M : Multiset Pattern} {comp : ℕ → Pattern}
    (nestedBy : NestedBy s M comp) :
    ∃ (s₁ : State Tm ℕ) (comp₁ : ℕ → Pattern), Relation.ReflTransGen Administers s s₁ ∧
      NestedBy s₁ M comp₁ ∧ ∀ o ∈ s₁.present, weight (comp₁ o) = 0 := by
  classical
  induction hw : weightOf s.present comp using Nat.strong_induction_on generalizing s comp with
  | _ w earlier =>
    by_cases light : ∀ o ∈ s.present, weight (comp o) = 0
    · exact ⟨s, comp, .refl, nestedBy, light⟩
    · simp only [not_forall] at light
      obtain ⟨o, present, heavy⟩ := light
      obtain ⟨s₁, fires⟩ : ∃ s₁, Administers s s₁ := by
        rcases heavy_shape heavy with zero | ⟨a, b, shape⟩
        · obtain ⟨ρ, admitted⟩ := clear_exists_nested nestedBy present zero
          exact ⟨_, clearAt ρ o, .inr rfl, admitted, rfl⟩
        · obtain ⟨ρ, m₁, m₂, admitted, -⟩ := heat_exists_nested nestedBy present shape
          exact ⟨_, heatAt ρ o m₁ m₂, .inl rfl, admitted, rfl⟩
      obtain ⟨comp', nestedBy', lighter⟩ := administration_decreases_nested nestedBy fires
      obtain ⟨s', comp'', run, nestedBy'', light'⟩ := earlier _ (hw ▸ lighter) nestedBy' rfl
      exact ⟨s', comp'', .head fires run, nestedBy'', light'⟩

/-! ## Communication -/

/-- **A communication is a source step**, at a ground-unifiable bag of nested parts. -/
theorem communication_sound_nested {s s' : State Tm ℕ} {M : Multiset Pattern} {comp : ℕ → Pattern}
    (nestedBy : NestedBy s M comp) (grounded : GroundUnifiable M) (fires : Communicates s s') :
    ∃ M', BagComm M M' ∧ RepresentsNested s' M' := by
  obtain ⟨f, isComm, admitted, rfl⟩ := fires
  obtain ⟨o₁, o₂, m₁, m₂, same, distinct, madeDistinct, present₁, present₂, fresh₁, fresh₂⟩ :=
    comm_normal f isComm admitted
  rw [same] at admitted ⊢
  obtain ⟨t, x, A, u, B, first, second, unifiable⟩ :=
    comm_shape_nested nestedBy admitted madeDistinct present₁ present₂
  have split : M = pFor t x A ::ₘ pFor u x B ::ₘ bagOf (s.present \ {o₁, o₂}) comp := by
    rw [← nestedBy.bag]
    exact bagOf_split distinct present₁ present₂ first second
  have inM₁ : pFor t x A ∈ M := by
    rw [split]
    exact Multiset.mem_cons_self _ _
  have inM₂ : pFor u x B ∈ M.erase (pFor t x A) := by
    rw [split, Multiset.erase_cons_head]
    exact Multiset.mem_cons_self _ _
  obtain ⟨bs, gp, values⟩ := grounded t x A u B inM₁ inM₂ unifiable
  obtain ⟨convention, nestedBy'⟩ := comm_result_nested nestedBy admitted distinct madeDistinct present₁
    present₂ fresh₁ fresh₂ first second gp values
  refine ⟨_, ?_, _, nestedBy'⟩
  rw [split]
  exact BagComm.comm t u x A B bs _ gp convention values

/-- **Every source step is matched**: housekeeping firings, then one communication. -/
theorem communication_complete_nested {s : State Tm ℕ} {M M' : Multiset Pattern} {comp : ℕ → Pattern}
    (nestedBy : NestedBy s M comp) (step : BagComm M M') :
    ∃ s₁ s₂ : State Tm ℕ, Relation.ReflTransGen Administers s s₁ ∧ Communicates s₁ s₂ ∧
      RepresentsNested s₂ M' := by
  classical
  obtain ⟨s₁, comp₁, run, nestedBy₁, light⟩ := heats_to_parts_nested nestedBy
  obtain ⟨t, u, x, A, B, bs, rest, gp, convention, values⟩ := step
  have heated : bagOf s₁.present comp₁ = s₁.present.val.map comp₁ := by
    unfold bagOf
    rw [Finset.sum_congr rfl fun o member => parts_coe_of_light (light o member),
      Finset.sum_eq_multiset_sum,
      show (fun o => ({comp₁ o} : Multiset Pattern)) = (fun p : Pattern => ({p} : Multiset Pattern)) ∘ comp₁
        from rfl, ← Multiset.map_map, Multiset.sum_map_singleton]
  have rows : s₁.present.val.map comp₁ = pFor t x A ::ₘ pFor u x B ::ₘ rest := by
    rw [← heated, nestedBy₁.bag]
  obtain ⟨o₁, member₁, at₁⟩ : ∃ o₁ ∈ s₁.present, comp₁ o₁ = pFor t x A := by
    have found : pFor t x A ∈ s₁.present.val.map comp₁ := by
      rw [rows]
      exact Multiset.mem_cons_self _ _
    obtain ⟨o₁, member, same⟩ := Multiset.mem_map.mp found
    exact ⟨o₁, member, same⟩
  obtain ⟨o₂, member₂, distinct, at₂⟩ : ∃ o₂ ∈ s₁.present, o₂ ≠ o₁ ∧ comp₁ o₂ = pFor u x B := by
    have split : s₁.present.val.map comp₁ = comp₁ o₁ ::ₘ (s₁.present.erase o₁).val.map comp₁ := by
      rw [← Multiset.map_cons comp₁ o₁,
        ← Finset.insert_val_of_notMem (Finset.notMem_erase o₁ s₁.present),
        Finset.insert_erase member₁]
    rw [split, at₁] at rows
    have others := Multiset.cons_inj_right _ |>.mp rows
    have found : pFor u x B ∈ (s₁.present.erase o₁).val.map comp₁ := by
      rw [others]
      exact Multiset.mem_cons_self _ _
    obtain ⟨o₂, member, same⟩ := Multiset.mem_map.mp found
    have inErase := Finset.mem_erase.mp member
    exact ⟨o₂, inErase.2, inErase.1, same⟩
  obtain ⟨ρ, m₁, m₂, admitted, madeDistinct, fresh₁, fresh₂⟩ :=
    comm_exists_nested nestedBy₁ member₁ member₂ (Ne.symm distinct) at₁ at₂ gp
  obtain ⟨-, nestedBy₂⟩ := comm_result_nested nestedBy₁ admitted (Ne.symm distinct) madeDistinct member₁
    member₂ fresh₁ fresh₂ at₁ at₂ gp values
  have restSame : bagOf (s₁.present \ {o₁, o₂}) comp₁ = rest := by
    have both : pFor t x A ::ₘ pFor u x B ::ₘ rest =
        pFor t x A ::ₘ pFor u x B ::ₘ bagOf (s₁.present \ {o₁, o₂}) comp₁ := by
      rw [← nestedBy₁.bag]
      exact bagOf_split (Ne.symm distinct) member₁ member₂ at₁ at₂
    exact ((Multiset.cons_inj_right _).mp ((Multiset.cons_inj_right _).mp both)).symm
  rw [restSame] at nestedBy₂
  exact ⟨s₁, _, run, ⟨commAt ρ o₁ o₂ m₁ m₂, rfl, admitted, rfl⟩, _, nestedBy₂⟩

/-! ## Every nested process is represented -/

/-- **The initial state of a nested process represents its parts.** -/
theorem initial_nested (P : Pattern) (nestedP : NestedProcess P) :
    NestedBy (initial (parts P)) (parts P) (fun n => (parts P).getD n pZero) := by
  refine ⟨fun _ _ _ _ => rfl, fun n member => nestedP.nested _ (getD_mem (Finset.mem_range.mp member)),
    ?_, ?_, ?_, initial_bag P⟩
  · intro i member j member' different
    have small₁ := Finset.mem_range.mp member
    have small₂ := Finset.mem_range.mp member'
    show FramesDisjoint ((parts P).getD i pZero) ((parts P).getD j pZero)
    rw [getD_eq small₁, getD_eq small₂]
    have pairwise := List.pairwise_iff_getElem.mp nestedP.disjoint
    rcases Nat.lt_or_gt_of_ne different with before | after
    · exact pairwise i j small₁ small₂ before
    · exact (pairwise j i small₂ small₁ after).symm
  · intro i member y inside
    exact .inl (mem_pvars_predot_of_mem inside)
  · intro τ
    exact ⟨τ, fun _ member => absurd member List.not_mem_nil, fun _ _ _ _ => rfl⟩

/-- **Every nested process is represented.** -/
theorem every_nested_process_represented (P : Pattern) (nestedP : NestedProcess P) :
    ∃ s, RepresentsNested s (parts P) :=
  ⟨initial (parts P), _, initial_nested P nestedP⟩

/-! ## A variable the knowledge fixes -/

theorem eq_of_mem_parts_of_not_par {p c : Pattern} (notPar : ¬ IsPar p) (member : c ∈ parts p) : c = p := by
  rw [parts_of_not_par notPar] at member
  split_ifs at member
  · exact absurd member List.not_mem_nil
  · exact List.mem_singleton.mp member

/-- **A part's variables are the process's.** -/
theorem pvars_of_mem_parts (p : Pattern) : ∀ c ∈ parts p, ∀ y ∈ pvars c, y ∈ pvars p := by
  induction p using Pattern.rec
    (motive_2 := fun ps => ∀ q ∈ ps, ∀ c ∈ parts q, ∀ y ∈ pvars c, y ∈ pvars q) with
  | collection ct elems rest ih =>
      intro c member y inC
      by_cases isPar : IsPar (.collection ct elems rest)
      · obtain ⟨a, b, same⟩ := isPar
        simp only [par, MeTTaCalculus.pPar, Pattern.collection.injEq] at same
        obtain ⟨rfl, rfl, rfl⟩ := same
        rw [show Pattern.collection .hashBag [a, b] none = par a b from rfl, parts_par] at member
        rw [show Pattern.collection .hashBag [a, b] none = par a b from rfl, MeTTaCalculus.Corrected.pvars_par]
        rcases List.mem_append.mp member with inA | inB
        · exact List.mem_append_left _ (ih a (by simp) c inA y inC)
        · exact List.mem_append_right _ (ih b (by simp) c inB y inC)
      · exact eq_of_mem_parts_of_not_par isPar member ▸ inC
  | bvar n =>
      exact fun c member y inC =>
        eq_of_mem_parts_of_not_par (by rintro ⟨a, b, same⟩; cases same) member ▸ inC
  | fvar x =>
      exact fun c member y inC =>
        eq_of_mem_parts_of_not_par (by rintro ⟨a, b, same⟩; cases same) member ▸ inC
  | apply f args ih =>
      exact fun c member y inC =>
        eq_of_mem_parts_of_not_par (by rintro ⟨a, b, same⟩; cases same) member ▸ inC
  | lambda nm body ih =>
      exact fun c member y inC =>
        eq_of_mem_parts_of_not_par (by rintro ⟨a, b, same⟩; cases same) member ▸ inC
  | multiLambda n nms body ih =>
      exact fun c member y inC =>
        eq_of_mem_parts_of_not_par (by rintro ⟨a, b, same⟩; cases same) member ▸ inC
  | subst body repl ihb ihr =>
      exact fun c member y inC =>
        eq_of_mem_parts_of_not_par (by rintro ⟨a, b, same⟩; cases same) member ▸ inC
  | nil => simp_all
  | cons p ps head tail =>
      rename_i q member c inC y inY
      rcases List.mem_cons.mp member with rfl | later
      · exact head c inC y inY
      · exact tail q later c inC y inY

/-- **A communication fixes the variables of its patterns**: when the taken rows read as inputs whose
patterns have a ground principal unifier, every solution of the knowledge after the firing gives each
variable of the two patterns its value. -/
theorem comm_fixes {s : State Tm ℕ} {ρ : PSubst} {o₁ o₂ m₁ m₂ : ℕ} {t u x₁ x₂ K₁ K₂ : Pattern}
    (reads₁ : ∀ σ : PSubst, patternAction.Models σ s.knowledge →
      psubst σ (s.label o₁) = psubst σ (pFor t x₁ K₁))
    (reads₂ : ∀ σ : PSubst, patternAction.Models σ s.knowledge →
      psubst σ (s.label o₂) = psubst σ (pFor u x₂ K₂))
    (madeDistinct : m₁ ≠ m₂) {bs : Bindings} (gp : GroundPrincipal t u bs) {σ : PSubst}
    (solved : patternAction.Models σ ((commAt ρ o₁ o₂ m₁ m₂).result X s).knowledge)
    {y : String} (inPatterns : y ∈ pvars t ++ pvars u) {value : Pattern} (found : bs.lookup y = some value) :
    (σ y).getD (.fvar y) = value :=
  gp.principal σ (comm_reads_inputs s.label t u x₁ x₂ K₁ K₂ ⟨s.knowledge, s.present⟩ o₁ o₂ m₁ m₂ reads₁
    reads₂ madeDistinct ρ solved).2.1 y inPatterns value found

/-- **A state whose knowledge fixes a variable represents no bag of nested parts in which it occurs.**
Every assignment of the parts' variables must extend to a solution of the knowledge. A communication fixes
the variables of its patterns (`comm_fixes`), so a part beside the redex that binds one of them again is
misrepresented; the variable convention across parts rules this out. -/
theorem pinned_represents_nothing {s : State Tm ℕ} {y : String} {value : Pattern}
    (pinned : ∀ σ : PSubst, patternAction.Models σ s.knowledge → (σ y).getD (.fvar y) = value)
    {M : Multiset Pattern} {c : Pattern} (member : c ∈ M) (occurs : y ∈ pvars c) :
    ¬ RepresentsNested s M := by
  rintro ⟨comp, nestedBy⟩
  rw [← nestedBy.bag] at member
  unfold bagOf at member
  obtain ⟨o, present, inParts⟩ := Multiset.mem_sum.mp member
  have inComp : y ∈ pvars (comp o) := pvars_of_mem_parts (comp o) c (Multiset.mem_coe.mp inParts) y occurs
  obtain ⟨σ₁, known₁, agree₁⟩ := nestedBy.free fun _ => some pZero
  obtain ⟨σ₂, known₂, agree₂⟩ := nestedBy.free fun _ => some (nQuote pZero)
  have toZero : pZero = value := (agree₁ o present y inComp).symm.trans (pinned σ₁ known₁)
  have toQuote : nQuote pZero = value := (agree₂ o present y inComp).symm.trans (pinned σ₂ known₂)
  exact absurd (toZero.trans toQuote.symm) (by decide +kernel)

/-! ## The theorem -/

/-- **The F1R3FLY manuscript's calculus on the one-match step by a finite program, with nested binding.**

The step is `RuleSyntax.step` of the fixed three-rule `program` at the one frame of structural
substitution on patterns. Through `RepresentsNested`, with the bag of parallel parts as the source and
`BagComm` as its COMM, for processes whose continuations may bind again at any depth:

1. every nested process is represented;
2. every transition of the step is a communication or housekeeping;
3. housekeeping keeps the represented bag;
4. at a ground-unifiable bag, a communication is a source step;
5. every source step is matched by housekeeping firings and one communication;
6. a run of `k` housekeeping firings has `k` at most the spine weight of the parts. -/
theorem manuscript_calculus_nested :
    program.Finite ∧
    (∀ P : Pattern, NestedProcess P → ∃ s, RepresentsNested s (parts P)) ∧
    (∀ s s' : State Tm ℕ,
      Succ (RuleSyntax.step X ℕ E program).toStep s s' ↔ Communicates s s' ∨ Administers s s') ∧
    (∀ {s s' : State Tm ℕ} {M : Multiset Pattern}, RepresentsNested s M → Administers s s' →
      RepresentsNested s' M) ∧
    (∀ {s s' : State Tm ℕ} {M : Multiset Pattern}, RepresentsNested s M → GroundUnifiable M →
      Communicates s s' → ∃ M', BagComm M M' ∧ RepresentsNested s' M') ∧
    (∀ {s : State Tm ℕ} {M M' : Multiset Pattern}, RepresentsNested s M → BagComm M M' →
      ∃ s₁ s₂ : State Tm ℕ, Relation.ReflTransGen Administers s s₁ ∧ Communicates s₁ s₂ ∧
        RepresentsNested s₂ M') ∧
    (∀ {s e : State Tm ℕ} {M : Multiset Pattern} {comp : ℕ → Pattern} {k : ℕ},
      NestedBy s M comp → AdministrativeRun k s e → k ≤ weightOf s.present comp) := by
  refine ⟨program_finite, every_nested_process_represented, succ_iff, ?_, ?_, ?_,
    fun nestedBy run => administration_bounded_nested nestedBy run⟩
  · intro s s' M represented fires
    obtain ⟨comp, nestedBy⟩ := represented
    obtain ⟨comp', nestedBy', -⟩ := administration_decreases_nested nestedBy fires
    exact ⟨comp', nestedBy'⟩
  · intro s s' M represented grounded fires
    obtain ⟨comp, nestedBy⟩ := represented
    exact communication_sound_nested nestedBy grounded fires
  · intro s M M' represented step
    obtain ⟨comp, nestedBy⟩ := represented
    exact communication_complete_nested nestedBy step

/-! ## Runs -/

/-- Housekeeping runs are runs of the step. -/
theorem succ_of_administers {s s' : State Tm ℕ} (run : Relation.ReflTransGen Administers s s') :
    Relation.ReflTransGen (Succ (RuleSyntax.step X ℕ E program).toStep) s s' := by
  induction run with
  | refl => exact .refl
  | tail _ administers earlier => exact earlier.tail ((succ_iff _ _).mpr (.inr administers))

/-- **Every run of the source from a represented bag is matched by a run of the step.** -/
theorem runs_complete_nested {s : State Tm ℕ} {M M' : Multiset Pattern} (represented : RepresentsNested s M)
    (run : Relation.ReflTransGen BagComm M M') :
    ∃ s', Relation.ReflTransGen (Succ (RuleSyntax.step X ℕ E program).toStep) s s' ∧
      RepresentsNested s' M' := by
  induction run with
  | refl => exact ⟨s, .refl, represented⟩
  | tail _ step earlier =>
      obtain ⟨s₁, run₁, comp₁, nestedBy₁⟩ := earlier
      obtain ⟨s₂, s₃, housekeeping, fires, represented₃⟩ := communication_complete_nested nestedBy₁ step
      exact ⟨s₃, run₁.trans ((succ_of_administers housekeeping).tail ((succ_iff s₂ s₃).mpr (.inl fires))),
        represented₃⟩

/-- **Every run of the step from a represented bag is a run of the source**, when every bag the source
reaches from it is ground-unifiable: a communication is a source step, and housekeeping keeps the bag. -/
theorem runs_sound_nested {s s' : State Tm ℕ} {M : Multiset Pattern} (represented : RepresentsNested s M)
    (grounded : ∀ M', Relation.ReflTransGen BagComm M M' → GroundUnifiable M')
    (run : Relation.ReflTransGen (Succ (RuleSyntax.step X ℕ E program).toStep) s s') :
    ∃ M', Relation.ReflTransGen BagComm M M' ∧ RepresentsNested s' M' := by
  induction run with
  | refl => exact ⟨M, .refl, represented⟩
  | tail _ step earlier =>
      obtain ⟨M₁, run₁, comp₁, nestedBy₁⟩ := earlier
      rcases (succ_iff _ _).mp step with fires | fires
      · obtain ⟨M₂, source, represented₂⟩ :=
          communication_sound_nested nestedBy₁ (grounded M₁ run₁) fires
        exact ⟨M₂, run₁.tail source, represented₂⟩
      · obtain ⟨comp₂, nestedBy₂, -⟩ := administration_decreases_nested nestedBy₁ fires
        exact ⟨M₁, run₁, comp₂, nestedBy₂⟩

#print axioms scoped_congr
#print axioms vars_of_scoped
#print axioms binders_not_bound
#print axioms scoped_of_ground
#print axioms binders_psubst
#print axioms scoped_psubst
#print axioms mem_binders_iff
#print axioms frames_of_ground
#print axioms frames_psubst
#print axioms mem_pvars_predot_of_mem
#print axioms closed_input_of_instance
#print axioms closed_par_of_instance
#print axioms closed_zero_of_instance
#print axioms nested_applyDot
#print axioms heat_amalgamates
#print axioms comm_shape_nested
#print axioms comm_result_nested
#print axioms heat_result_nested
#print axioms clear_result_nested
#print axioms comm_exists_nested
#print axioms heat_exists_nested
#print axioms clear_exists_nested
#print axioms heats_to_parts_nested
#print axioms communication_sound_nested
#print axioms communication_complete_nested
#print axioms initial_nested
#print axioms manuscript_calculus_nested
#print axioms pvars_of_mem_parts
#print axioms comm_fixes
#print axioms pinned_represents_nothing
#print axioms runs_complete_nested
#print axioms runs_sound_nested
#print axioms scoped_of_binders_nil
#print axioms nested_of_hosted
#print axioms nestedProcess_of_hosted

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.FiniteProgram
