import Mettapedia.GSLT.LanguageDef.MatchStepMachine
import Mettapedia.GSLT.LanguageDef.CertificateGSLTStepAdequacyGeneral
import Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics

/-!
# Match steps and `spaceMatch`

The pure PeTTa specification of `(match &self pat tmpl)` is
`PeTTaSpace.spaceMatch`: for each stored atom in order, one-sided matching of
`pat` against the atom (`matchPattern`, over MeTTaIL `Pattern`), and `tmpl` with
each match's bindings applied.  This module connects the match step of
`MatchStepMachine` to it.

**A data template.**  `matchSite_answers`, for any store algebra: from a query
control `(match s P T)` whose continuation returns the template `T`, the machine
with match steps delivers `T`'s instance in every store the candidate step
produces, in snapshot order and with duplicates, and has then exhausted its
frontier, after one step for the match and one per answer.

**From LP terms to MeTTaIL patterns.**  `toPattern` sends a variable to the
metavariable of its name, a constant to the nullary application of its name, and
a function symbol applied to children to the application of its name to their
translations, in order.  With injective names it is injective
(`toPattern_injective`).  `matchPattern_toPattern`, with `matchArgs_toPattern`
for argument lists: matching a translated pattern against a translated ground
term succeeds exactly when some substitution sends the pattern to the term; it
then yields exactly one binding list, which gives the pattern's variables their
values under every such substitution and binds nothing else (`BindsAs`).
`unify_ground_matchPattern`: the total unifier of a ground atom with a pattern
succeeds exactly when the translated pattern matches the translated atom, and a
template instantiated by the unifier translates to the translated template with
the match's bindings applied (`applyBindings_toPattern`).  A template variable
the pattern lacks is fixed by the unifier (`unifyTotal_relevantIdempotent`) and
left unbound by the match.  `spaceMatch_toPattern` states this for a whole
snapshot, as lists.

**The bridge** (`matchSite_spaceMatch`).  Over the substitution store, for a
snapshot of ground atoms and a data template: the run of the machine with match
steps from `(match s P T)` exhausts its frontier, and its answers, read through
their stores and translated, are `spaceMatch` of the space whose facts are the
translated snapshot and which has no rules, for `P` and `T` read through the
entry store: equal as lists, in order, with duplicates.

**What connects and what does not.**  The connection goes through the
substitution instance and `toPattern`; no instance of the generic machine over
MeTTaIL `Pattern` with `matchPattern` is built.  Covered: first-order patterns
and templates (variables, constants, applications), repeated pattern variables,
and template variables the pattern does not bind.  Not covered: stored atoms
with variables (the match step unifies two-sided where `matchPattern` matches
one-sided), templates with calls, MeTTaIL binders, explicit substitutions and
collections (bags, sets and rest variables), and the stored `(= lhs rhs)` atoms
of premise-free rules (`storedRuleAtoms`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.MatchSteps

open Mettapedia.Machines.SharedContinuation
open Mettapedia.GSLT.LanguageDef.DefunctionalizedEquationBodies
open Mettapedia.GSLT.LanguageDef.DestinationPassing
open Mettapedia.GSLT.Dynamics.ContextIndexedSwitching (repeats)

/-! ## A match site with a data template -/

section DataTemplate

variable {Term Store Rel Sp Op : Type} (L : TemplateLanguage Term) (S : StoreAlgebra Term Store Op)
variable [DecidableEq Rel] [DecidableEq Sp] [Inhabited Term]
variable (P : EqProgram L (Rel ⊕ Sp) Op) (atoms : Sp → List (Atom L))

/-- Tasks that return a template instance with no pending frame deliver it, one
per step, in order. -/
theorem repeats_rets {k : Nat} (t : L.Tmpl k) (frame : Fin k → Term) (dest : Option Term) :
    ∀ (stores : List Store) (emitted : List (Unit × Answer Term Store)),
      repeats (step (matching L S P atoms)) stores.length
          ⟨stores.map (fun σ' => ⟨(), ⟨⟨k, .ret t, frame, σ'⟩, dest⟩, []⟩), emitted⟩ =
        ⟨[], emitted ++ stores.map fun σ' => ((), (L.inst t frame, σ'))⟩
  | [], emitted => by simp [repeats]
  | σ' :: rest, emitted => by
      have first : step (matching L S P atoms)
          ⟨(⟨(), ⟨⟨k, .ret t, frame, σ'⟩, dest⟩, []⟩ : Task Unit (DestControl L (Rel ⊕ Sp) Op Store)
              (DestFrame L (Rel ⊕ Sp) Op)) ::
            rest.map (fun σ' => ⟨(), ⟨⟨k, .ret t, frame, σ'⟩, dest⟩, []⟩), emitted⟩ =
          ⟨rest.map (fun σ' => ⟨(), ⟨⟨k, .ret t, frame, σ'⟩, dest⟩, []⟩),
            emitted ++ [((), (L.inst t frame, σ'))]⟩ := rfl
      simp only [List.length_cons, repeats, List.map_cons, first]
      rw [repeats_rets t frame dest rest]
      simp

/-- **The answers of a match site with a data template.**  From a query
control `(match s P T)` whose continuation returns the template `T`, the machine
with match steps delivers, in snapshot order and with duplicates, `T`'s instance
in every store the candidate step produces, and then has exhausted its frontier:
one step for the match, one per answer. -/
theorem matchSite_answers {k : Nat} (s : Sp) (pattern template : L.Tmpl k) (frame : Fin k → Term)
    (σ : Store) :
    repeats (step (matching L S P atoms))
        (((atoms s).filterMap fun A => candidate S A (L.inst pattern frame) σ).length + 1)
        (queryStateOut L (matchSite L s pattern (.ret template)) frame σ) =
      ⟨[], ((atoms s).filterMap fun A => candidate S A (L.inst pattern frame) σ).map
        fun σ' => ((), (L.inst template frame, σ'))⟩ := by
  set keep := frameSupport L pattern (Code.ret template : Code L (Rel ⊕ Sp) Op k)
  have same : L.inst template (reconstruct (capture frame keep)) = L.inst template frame :=
    L.inst_congr template _ _ fun i member =>
      reconstruct_capture frame keep i (by simp [keep, frameSupport, Code.support, member])
  have first : step (matching L S P atoms)
      (queryStateOut L (matchSite L s pattern (.ret template)) frame σ) =
      ⟨((atoms s).filterMap fun A => candidate S A (L.inst pattern frame) σ).map
          (fun σ' => ⟨(), ⟨⟨k, .ret template, reconstruct (capture frame keep), σ'⟩, none⟩, []⟩),
        []⟩ := by
    show (⟨(((atoms s).filterMap fun A => (candidate S A (L.inst pattern frame) σ).map
        fun σ' => ((), (⟨⟨k, .ret template, reconstruct (capture frame keep), σ'⟩, none⟩ :
          DestControl L (Rel ⊕ Sp) Op Store))).map fun next => ⟨next.1, next.2, []⟩) ++ [],
        [] ++ []⟩ : State Unit (DestControl L (Rel ⊕ Sp) Op Store) (DestFrame L (Rel ⊕ Sp) Op)
          (Answer Term Store)) = _
    simp only [List.append_nil, List.map_filterMap, Option.map_map, Function.comp_def]
  rw [repeats, first, repeats_rets, same]
  simp

end DataTemplate

/-! ## LP terms as MeTTaIL patterns -/

section Translation

open Mettapedia.Logic.LP
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match

variable {σ : LPSignature} (vname : σ.vars → String) (head : σ.constants ⊕ σ.functionSymbols → String)

/-- An LP term as a MeTTaIL pattern: a variable is the metavariable of its name,
a constant the nullary application of its name, a function symbol the
application of its name to the children, in order. -/
def toPattern : Mettapedia.Logic.LP.Term σ → Pattern
  | .var x => .fvar (vname x)
  | .const c => .apply (head (.inl c)) []
  | .app f ts => .apply (head (.inr f)) (List.ofFn fun i => toPattern (ts i))

variable {vname head}

/-- With injective names, the translation is injective. -/
theorem toPattern_injective (vinj : Function.Injective vname) (hinj : Function.Injective head) :
    Function.Injective (toPattern vname head) := by
  intro t u same
  induction t generalizing u with
  | var x =>
      cases u with
      | var y => simp only [toPattern, Pattern.fvar.injEq] at same; rw [vinj same]
      | const _ => simp [toPattern] at same
      | app _ _ => simp [toPattern] at same
  | const c =>
      cases u with
      | var _ => simp [toPattern] at same
      | const d =>
          simp only [toPattern, Pattern.apply.injEq, and_true] at same
          cases hinj same
          rfl
      | app g us =>
          simp only [toPattern, Pattern.apply.injEq] at same
          exact absurd (hinj same.1) (by simp)
  | app f ts ih =>
      cases u with
      | var _ => simp [toPattern] at same
      | const _ =>
          simp only [toPattern, Pattern.apply.injEq] at same
          exact absurd (hinj same.1) (by simp)
      | app g us =>
          simp only [toPattern, Pattern.apply.injEq] at same
          obtain ⟨names, children⟩ := same
          cases hinj names
          have pointwise := List.ofFn_inj.mp children
          congr 1
          funext i
          exact ih i (congrFun pointwise i)

/-- Applying bindings to the translation of `t` is the translation of `t` under
`δ` when every variable of `t` is either bound to its value under `δ`, or unbound
and fixed by `δ`. -/
theorem applyBindings_toPattern {bs : Bindings} {δ : Subst σ} [DecidableEq σ.vars] :
    ∀ (t : Mettapedia.Logic.LP.Term σ),
      (∀ y ∈ t.freeVars, Bindings.lookup bs (vname y) = some (toPattern vname head (δ y)) ∨
        (Bindings.lookup bs (vname y) = none ∧ δ y = .var y)) →
        applyBindings bs (toPattern vname head t) = toPattern vname head (δ.applyTerm t)
  | .var x, covers => by
      simp only [toPattern, applyBindings, Subst.applyTerm_var]
      rcases covers x (Term.mem_freeVars_var.mpr rfl) with found | ⟨missing, fixed⟩
      · unfold Bindings.lookup at found
        cases hfind : bs.find? (·.1 == vname x) with
        | none => rw [hfind] at found; cases found
        | some pair =>
            rw [hfind] at found
            simpa using found
      · unfold Bindings.lookup at missing
        cases hfind : bs.find? (·.1 == vname x) with
        | none =>
            rw [fixed]
            rfl
        | some pair => rw [hfind] at missing; cases missing
  | .const c, _ => by simp [toPattern, applyBindings]
  | .app f ts, covers => by
      simp only [toPattern, applyBindings, Subst.applyTerm_app, List.map_ofFn,
        Pattern.apply.injEq, true_and]
      congr 1
      funext i
      exact applyBindings_toPattern (ts i) fun y member =>
        covers y (Term.mem_freeVars_app.mpr ⟨i, member⟩)

/-- In bindings whose every entry gives a variable's name its value under `δ`,
a name that is bound is looked up at that value. -/
theorem lookup_uniform (vinj : Function.Injective vname) {bs : Bindings} {δ : Subst σ}
    (uniform : ∀ pair ∈ bs, ∃ y, pair.1 = vname y ∧ pair.2 = toPattern vname head (δ y))
    {y : σ.vars} (present : ∃ pair ∈ bs, pair.1 = vname y) :
    Bindings.lookup bs (vname y) = some (toPattern vname head (δ y)) := by
  unfold Bindings.lookup
  cases hfind : bs.find? (·.1 == vname y) with
  | none =>
      obtain ⟨pair, member, named⟩ := present
      have := List.find?_eq_none.mp hfind pair member
      simp [named] at this
  | some pair =>
      obtain ⟨z, named, valued⟩ := uniform pair (List.mem_of_find?_eq_some hfind)
      have hit := List.find?_some hfind
      simp only [beq_iff_eq, named] at hit
      cases vinj hit
      simp [valued]

variable (vname head) in
/-- `bs` gives every variable in `vars` its value under `δ`, as a pattern, and
binds nothing else. -/
def BindsAs (vars : σ.vars → Prop) (δ : Subst σ) (bs : Bindings) : Prop :=
  (∀ y, vars y → Bindings.lookup bs (vname y) = some (toPattern vname head (δ y))) ∧
    ∀ pair ∈ bs, ∃ y, vars y ∧ pair.1 = vname y ∧ pair.2 = toPattern vname head (δ y)

theorem BindsAs.congr {vars vars' : σ.vars → Prop} {δ : Subst σ} {bs : Bindings}
    (binds : BindsAs vname head vars δ bs) (same : ∀ y, vars y ↔ vars' y) :
    BindsAs vname head vars' δ bs :=
  ⟨fun y member => binds.1 y ((same y).mpr member), fun pair member =>
    let ⟨y, inVars, named, valued⟩ := binds.2 pair member
    ⟨y, (same y).mp inVars, named, valued⟩⟩

variable [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]

omit [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
/-- **Matching a translated argument list** against the translation of ground
arguments, given the matching law for every argument: it succeeds exactly when
one substitution sends every pattern to its argument, with one binding list,
which gives the patterns' variables their values under every such
substitution. -/
theorem matchArgs_toPattern (vinj : Function.Injective vname) (hinj : Function.Injective head) :
    ∀ (n : ℕ) (ts us : Fin n → Mettapedia.Logic.LP.Term σ),
      (∀ i, ∀ a : Mettapedia.Logic.LP.Term σ, a.freeVars = ∅ →
        ((∃ δ : Subst σ, δ.applyTerm (ts i) = a) →
          ∃ bs, matchPattern (toPattern vname head (ts i)) (toPattern vname head a) = [bs] ∧
            ∀ δ : Subst σ, δ.applyTerm (ts i) = a →
              BindsAs vname head (· ∈ (ts i).freeVars) δ bs) ∧
        ((¬ ∃ δ : Subst σ, δ.applyTerm (ts i) = a) →
          matchPattern (toPattern vname head (ts i)) (toPattern vname head a) = [])) →
      (∀ i, (us i).freeVars = ∅) →
      ((∃ δ : Subst σ, ∀ i, δ.applyTerm (ts i) = us i) →
        ∃ bs, matchArgs (List.ofFn fun i => toPattern vname head (ts i))
            (List.ofFn fun i => toPattern vname head (us i)) = [bs] ∧
          ∀ δ : Subst σ, (∀ i, δ.applyTerm (ts i) = us i) →
            BindsAs vname head (fun y => ∃ i, y ∈ (ts i).freeVars) δ bs) ∧
      ((¬ ∃ δ : Subst σ, ∀ i, δ.applyTerm (ts i) = us i) →
        matchArgs (List.ofFn fun i => toPattern vname head (ts i))
          (List.ofFn fun i => toPattern vname head (us i)) = [])
  | 0, ts, us, _, _ => by
      refine ⟨fun _ => ⟨[], by simp [matchArgs], fun δ _ => ⟨?_, ?_⟩⟩, fun none => ?_⟩
      · rintro y ⟨i, -⟩
        exact i.elim0
      · intro pair member
        cases member
      · exact absurd ⟨Subst.id σ, fun i => i.elim0⟩ none
  | n + 1, ts, us, spec, ground => by
      have tail := matchArgs_toPattern vinj hinj n (fun i => ts i.succ) (fun i => us i.succ)
        (fun i => spec i.succ) (fun i => ground i.succ)
      have first := spec 0 (us 0) (ground 0)
      rw [List.ofFn_succ, List.ofFn_succ]
      simp only [matchArgs]
      by_cases joint : ∃ δ : Subst σ, ∀ i, δ.applyTerm (ts i) = us i
      · obtain ⟨δ, hδ⟩ := joint
        obtain ⟨hb, hm, hbinds⟩ := first.1 ⟨δ, hδ 0⟩
        obtain ⟨tb, tm, tbinds⟩ := tail.1 ⟨δ, fun i => hδ i.succ⟩
        have uniform : ∀ pair ∈ hb ++ tb, ∃ y, pair.1 = vname y ∧
            pair.2 = toPattern vname head (δ y) := by
          intro pair member
          rcases List.mem_append.mp member with inHead | inTail
          · obtain ⟨y, -, named, valued⟩ := (hbinds δ (hδ 0)).2 pair inHead
            exact ⟨y, named, valued⟩
          · obtain ⟨y, -, named, valued⟩ := (tbinds δ fun i => hδ i.succ).2 pair inTail
            exact ⟨y, named, valued⟩
        have agrees : ∀ l, (∀ pair ∈ l, pair ∈ hb ++ tb) →
            CertificateGSLT.bindingsAgreeWith (hb ++ tb) l := by
          intro l within pair member
          obtain ⟨y, named, valued⟩ := uniform pair (within pair member)
          rw [named, valued]
          exact lookup_uniform vinj uniform ⟨pair, within pair member, named⟩
        obtain ⟨merged, hmerge, -⟩ := CertificateGSLT.mergeBindings_some_of_agree
          (agrees hb fun pair member => List.mem_append_left _ member)
          (agrees tb fun pair member => List.mem_append_right _ member)
        refine ⟨fun _ => ⟨merged, by simp [hm, tm, hmerge], fun δ' hδ' => ⟨?_, ?_⟩⟩,
          fun none => absurd ⟨δ, hδ⟩ none⟩
        · rintro y ⟨i, member⟩
          induction i using Fin.cases with
          | zero =>
              exact CertificateGSLT.mergeBindings_lookup_left hmerge
                ((hbinds δ' (hδ' 0)).1 y member)
          | succ j =>
              have found := (tbinds δ' fun i => hδ' i.succ).1 y ⟨j, member⟩
              exact CertificateGSLT.mergeBindings_lookup_right hmerge _
                (CertificateGSLT.bindings_mem_of_lookup found)
        · intro pair member
          rcases CertificateGSLT.mergeBindings_mem_source hmerge pair member with inHead | inTail
          · obtain ⟨y, inVars, named, valued⟩ := (hbinds δ' (hδ' 0)).2 pair inHead
            exact ⟨y, ⟨0, inVars⟩, named, valued⟩
          · obtain ⟨y, ⟨j, inVars⟩, named, valued⟩ :=
              (tbinds δ' fun i => hδ' i.succ).2 pair inTail
            exact ⟨y, ⟨j.succ, inVars⟩, named, valued⟩
      · refine ⟨fun some => absurd some joint, fun _ => ?_⟩
        by_cases headMatch : ∃ δ : Subst σ, δ.applyTerm (ts 0) = us 0
        · obtain ⟨hb, hm, hbinds⟩ := first.1 headMatch
          by_cases tailMatch : ∃ δ : Subst σ, ∀ i : Fin n, δ.applyTerm (ts i.succ) = us i.succ
          · obtain ⟨tb, tm, tbinds⟩ := tail.1 tailMatch
            obtain ⟨δ₁, h₁⟩ := headMatch
            obtain ⟨δ₂, h₂⟩ := tailMatch
            have conflict : ∃ y, y ∈ (ts 0).freeVars ∧ (∃ j, y ∈ (ts (Fin.succ j)).freeVars) ∧
                δ₁ y ≠ δ₂ y := by
              by_contra noConflict
              push Not at noConflict
              refine joint ⟨fun y => if y ∈ (ts 0).freeVars then δ₁ y else δ₂ y, fun i => ?_⟩
              induction i using Fin.cases with
              | zero =>
                  rw [← h₁]
                  exact Subst.applyTerm_congr fun v member => by simp [member]
              | succ j =>
                  rw [← h₂ j]
                  refine Subst.applyTerm_congr fun v member => ?_
                  by_cases inHead : v ∈ (ts 0).freeVars
                  · simp only [inHead, ↓reduceIte]
                    exact noConflict v inHead ⟨j, member⟩
                  · simp [inHead]
            obtain ⟨y, inHead, ⟨j, inTail⟩, differ⟩ := conflict
            have rejected : mergeBindings hb tb = none := by
              cases hmerge : mergeBindings hb tb with
              | none => rfl
              | some merged =>
                  have left := CertificateGSLT.mergeBindings_lookup_left hmerge
                    ((hbinds δ₁ h₁).1 y inHead)
                  have right := CertificateGSLT.mergeBindings_lookup_right hmerge _
                    (CertificateGSLT.bindings_mem_of_lookup
                      ((tbinds δ₂ h₂).1 y ⟨j, inTail⟩))
                  rw [left, Option.some.injEq] at right
                  exact absurd (toPattern_injective vinj hinj right) differ
            simp [hm, tm, rejected]
          · simp [hm, tail.2 tailMatch]
        · simp [first.2 headMatch]

omit [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
/-- **Matching a translated pattern against a translated ground term** succeeds
exactly when some substitution sends the pattern to the term.  It then has one
binding list, which gives the pattern's variables their values under every such
substitution and binds nothing else. -/
theorem matchPattern_toPattern (vinj : Function.Injective vname) (hinj : Function.Injective head) :
    ∀ (p a : Mettapedia.Logic.LP.Term σ), a.freeVars = ∅ →
      ((∃ δ : Subst σ, δ.applyTerm p = a) →
        ∃ bs, matchPattern (toPattern vname head p) (toPattern vname head a) = [bs] ∧
          ∀ δ : Subst σ, δ.applyTerm p = a → BindsAs vname head (· ∈ p.freeVars) δ bs) ∧
      ((¬ ∃ δ : Subst σ, δ.applyTerm p = a) →
        matchPattern (toPattern vname head p) (toPattern vname head a) = [])
  | .var x, a, _ => by
      refine ⟨fun _ => ⟨[(vname x, toPattern vname head a)], by simp [toPattern, matchPattern],
        fun δ hδ => ⟨?_, ?_⟩⟩, fun none => absurd ⟨fun _ => a, rfl⟩ none⟩
      · intro y member
        rw [Term.mem_freeVars_var.mp member]
        simp only [Subst.applyTerm_var] at hδ
        simp [Bindings.lookup, hδ]
      · intro pair member
        simp only [List.mem_singleton] at member
        subst member
        simp only [Subst.applyTerm_var] at hδ
        exact ⟨x, Term.mem_freeVars_var.mpr rfl, rfl, by rw [hδ]⟩
  | .const c, a, ground => by
      cases a with
      | var v => simp [Term.freeVars] at ground
      | const d =>
          by_cases same : c = d
          · subst same
            refine ⟨fun _ => ⟨[], by simp [toPattern, matchPattern, matchArgs], fun δ _ => ⟨?_, ?_⟩⟩,
              fun none => absurd ⟨Subst.id σ, rfl⟩ none⟩
            · intro y member
              exact absurd member Term.not_mem_freeVars_const
            · intro pair member
              cases member
          · have differ : head (.inl c) ≠ head (.inl d) := fun e => same (Sum.inl_injective (hinj e))
            refine ⟨fun ⟨δ, hδ⟩ => ?_, fun _ => ?_⟩
            · simp only [Subst.applyTerm_const, Term.const.injEq] at hδ
              exact absurd hδ same
            · simp [toPattern, matchPattern, differ]
      | app g us =>
          have differ : head (.inl c) ≠ head (.inr g) := fun e => by cases hinj e
          refine ⟨fun ⟨δ, hδ⟩ => ?_, fun _ => ?_⟩
          · simp at hδ
          · simp [toPattern, matchPattern, differ]
  | .app f ts, a, ground => by
      cases a with
      | var v => simp [Term.freeVars] at ground
      | const d =>
          have differ : head (.inr f) ≠ head (.inl d) := fun e => by cases hinj e
          refine ⟨fun ⟨δ, hδ⟩ => ?_, fun _ => ?_⟩
          · simp at hδ
          · simp [toPattern, matchPattern, differ]
      | app g us =>
          by_cases same : f = g
          · subst same
            have groundArgs : ∀ i, (us i).freeVars = ∅ := fun i =>
              Finset.eq_empty_of_forall_notMem fun y member => by
                have : y ∈ (Term.app f us).freeVars := Term.mem_freeVars_app.mpr ⟨i, member⟩
                simp [ground] at this
            have args := matchArgs_toPattern vinj hinj _ ts us
              (fun i => matchPattern_toPattern vinj hinj (ts i)) groundArgs
            have unfolds : matchPattern (toPattern vname head (.app f ts))
                (toPattern vname head (.app f us)) =
                matchArgs (List.ofFn fun i => toPattern vname head (ts i))
                  (List.ofFn fun i => toPattern vname head (us i)) := by
              simp [toPattern, matchPattern]
            have unfolding : ∀ δ : Subst σ,
                δ.applyTerm (.app f ts) = .app f us ↔ ∀ i, δ.applyTerm (ts i) = us i := by
              intro δ
              simp only [Subst.applyTerm_app, Term.app.injEq, heq_eq_eq, true_and]
              exact funext_iff
            have vars : ∀ y, (∃ i, y ∈ (ts i).freeVars) ↔ y ∈ (Term.app f ts).freeVars :=
              fun y => Term.mem_freeVars_app.symm
            rw [unfolds]
            refine ⟨fun ⟨δ, hδ⟩ => ?_, fun none => ?_⟩
            · obtain ⟨bs, hm, hbinds⟩ := args.1 ⟨δ, (unfolding δ).mp hδ⟩
              exact ⟨bs, hm, fun δ' hδ' => (hbinds δ' ((unfolding δ').mp hδ')).congr vars⟩
            · exact args.2 fun ⟨δ, hδ⟩ => none ⟨δ, (unfolding δ).mpr hδ⟩
          · have differ : head (.inr f) ≠ head (.inr g) := fun e => same (Sum.inr_injective (hinj e))
            refine ⟨fun ⟨δ, hδ⟩ => ?_, fun _ => ?_⟩
            · simp only [Subst.applyTerm_app, Term.app.injEq] at hδ
              exact absurd hδ.1 same
            · simp [toPattern, matchPattern, differ]

/-- **Unifying with a ground atom is one-sided matching.**  The total unifier of
a ground atom with a pattern succeeds exactly when the translated pattern
matches the translated atom, and a template whose variables the pattern binds,
instantiated by the unifier, translates to the template with the match's
bindings applied.  The unifier fixes every variable the pattern does not
contain, and the match leaves it unbound. -/
theorem unify_ground_matchPattern (vinj : Function.Injective vname)
    (hinj : Function.Injective head) (a p t : Mettapedia.Logic.LP.Term σ) (ground : a.freeVars = ∅) :
    (unifyTotal [(a, p)]).toList.map (fun μ => toPattern vname head (μ.applyTerm t)) =
      (matchPattern (toPattern vname head p) (toPattern vname head a)).map
        fun bs => applyBindings bs (toPattern vname head t) := by
  have fixed : ∀ θ : Subst σ, θ.applyTerm a = a := fun θ =>
    Subst.applyTerm_eq_self fun v member => by simp [ground] at member
  have spec := matchPattern_toPattern vinj hinj p a ground
  cases hu : unifyTotal [(a, p)] with
  | none =>
      have none : ¬ ∃ δ : Subst σ, δ.applyTerm p = a := fun ⟨δ, hδ⟩ =>
        (unifyTotal_none_iff_not_unifiable _).mp hu ⟨δ, fun e member => by
          simp only [List.mem_singleton] at member
          subst member
          simp [fixed, hδ]⟩
      simp [spec.2 none]
  | some μ =>
      have sound := unifyTotal_sound _ μ hu (a, p) (by simp)
      have hμ : μ.applyTerm p = a := sound.symm.trans (fixed μ)
      obtain ⟨bs, hm, hbinds⟩ := spec.1 ⟨μ, hμ⟩
      have relevant := unifyTotal_relevantIdempotent _ μ hu
      rw [hm]
      simp only [Option.toList_some, List.map_cons, List.map_nil, List.cons.injEq, and_true]
      refine (applyBindings_toPattern t fun y _ => ?_).symm
      by_cases inPattern : y ∈ p.freeVars
      · exact .inl ((hbinds μ hμ).1 y inPattern)
      · refine .inr ⟨?_, relevant.fixes y (by simp [eqVars, ground, inPattern])⟩
        cases found : Bindings.lookup bs (vname y) with
        | none => rfl
        | some value =>
            obtain ⟨z, inVars, named, -⟩ :=
              (hbinds μ hμ).2 _ (CertificateGSLT.bindings_mem_of_lookup found)
            obtain rfl := vinj named
            exact absurd inVars inPattern

open Mettapedia.Languages.MeTTa.PeTTa in
/-- **Ground snapshots against `spaceMatch`.**  Unifying every ground atom with the
pattern, in snapshot order, and instantiating the template by each unifier
gives, after translation, `spaceMatch` of the space whose stored atoms are the
translated snapshot: as a list, in order, with duplicates. -/
theorem spaceMatch_toPattern (vinj : Function.Injective vname) (hinj : Function.Injective head)
    (atoms : List (Mettapedia.Logic.LP.Term σ)) (ground : ∀ a ∈ atoms, a.freeVars = ∅)
    (p t : Mettapedia.Logic.LP.Term σ) :
    atoms.flatMap (fun a =>
        (unifyTotal [(a, p)]).toList.map fun μ => toPattern vname head (μ.applyTerm t)) =
      PeTTaSpace.spaceMatch ⟨atoms.map (toPattern vname head), []⟩
        (toPattern vname head p) (toPattern vname head t) := by
  simp only [PeTTaSpace.spaceMatch, PeTTaSpace.storedAtoms, PeTTaSpace.storedRuleAtoms,
    List.filterMap_nil, List.append_nil, List.flatMap_map]
  exact List.flatMap_congr fun a member =>
    unify_ground_matchPattern vinj hinj a p t (ground a member)

end Translation

/-! ## The bridge over the substitution store -/

section Substitution

open Mettapedia.Logic.LP
open CompiledTwoSidedHeadProgram
open Mettapedia.Languages.MeTTa.PeTTa

universe r

variable {σ : LPSignature.{0, 0, r, 0}} [DecidableEq σ.vars] [DecidableEq σ.constants]
  [DecidableEq σ.functionSymbols]
variable (name : ℕ → σ.vars) {Op : Type}
  (prim : Op → List (Mettapedia.Logic.LP.Term σ) → Subst σ × ℕ → Option (Mettapedia.Logic.LP.Term σ))
  (test : Op → List (Mettapedia.Logic.LP.Term σ) → Subst σ × ℕ → Option Bool)

/-- A ground stored atom, a head pattern without slots, as a term. -/
def groundTerm (g : HeadPattern σ (Fin 0)) : Mettapedia.Logic.LP.Term σ :=
  instantiate (fun i => i.elim0) g

omit [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
theorem groundTerm_freeVars (g : HeadPattern σ (Fin 0)) : (groundTerm g).freeVars = ∅ := by
  induction g with
  | var i => exact i.elim0
  | const c => rfl
  | app f ts ih =>
      refine Finset.eq_empty_of_forall_notMem fun y member => ?_
      simp only [groundTerm, instantiate] at member
      obtain ⟨i, inChild⟩ := Term.mem_freeVars_app.mp member
      have := ih i
      simp only [groundTerm] at this
      simp [this] at inChild

/-- The candidate step on a ground atom allocates nothing and unifies the atom
with the pattern read through the store. -/
theorem candidate_ground (g : HeadPattern σ (Fin 0)) (p : Mettapedia.Logic.LP.Term σ) (θ : Subst σ)
    (n : ℕ) :
    candidate (substitutionStore name prim test) (⟨0, g⟩ : Atom (headTemplates σ)) p (θ, n) =
      (unifyTotal [(groundTerm g, θ.applyTerm p)]).map fun μ => (μ ∘ₛ θ, n) := by
  have frame : (freshVariables name n 0 : Fin 0 → Mettapedia.Logic.LP.Term σ) = fun i => i.elim0 :=
    funext fun i => i.elim0
  have fixed : θ.applyTerm (groundTerm g) = groundTerm g :=
    Subst.applyTerm_eq_self fun v member => by simp [groundTerm_freeVars] at member
  simp only [candidate, substitutionStore, frame]
  change (unifyTotal [(θ.applyTerm (groundTerm g), θ.applyTerm p)]).map _ = _
  rw [fixed]
  rfl

/-- **The bridge to `spaceMatch`.**  Over the substitution store, from a query
control `(match s P T)` whose continuation returns the data template `T`, on a
snapshot of ground atoms: the machine with match steps exhausts its frontier
after one step per answer and one for the match, and its answers, read through
their stores and translated, are `spaceMatch` of the space whose stored atoms
are the translated snapshot, for `P` and `T` read through the entry store: as a
list, in order, with duplicates. -/
theorem matchSite_spaceMatch (vname : σ.vars → String)
    (head : σ.constants ⊕ σ.functionSymbols → String) (vinj : Function.Injective vname)
    (hinj : Function.Injective head) [Inhabited (Mettapedia.Logic.LP.Term σ)] {Rel Sp : Type}
    [DecidableEq Rel] [DecidableEq Sp]
    (P : EqProgram (headTemplates σ) (Rel ⊕ Sp) Op) (atoms : Sp → List (Atom (headTemplates σ)))
    (s : Sp) (ground : List (HeadPattern σ (Fin 0)))
    (snapshot : atoms s = ground.map fun g => ⟨0, g⟩) {k : ℕ}
    (pattern template : HeadPattern σ (Fin k)) (frame : Fin k → Mettapedia.Logic.LP.Term σ)
    (θ : Subst σ) (n : ℕ) :
    ∃ m, (repeats (step (matching (headTemplates σ) (substitutionStore name prim test) P atoms)) m
          (queryStateOut (headTemplates σ) (matchSite (headTemplates σ) s pattern (.ret template))
            frame (θ, n))).frontier = [] ∧
      (repeats (step (matching (headTemplates σ) (substitutionStore name prim test) P atoms)) m
          (queryStateOut (headTemplates σ) (matchSite (headTemplates σ) s pattern (.ret template))
            frame (θ, n))).emitted.map (fun a => toPattern vname head (a.2.2.1.applyTerm a.2.1)) =
        PeTTaSpace.spaceMatch ⟨ground.map (toPattern vname head ∘ groundTerm), []⟩
          (toPattern vname head (θ.applyTerm (instantiate frame pattern)))
          (toPattern vname head (θ.applyTerm (instantiate frame template))) := by
  have run := matchSite_answers (headTemplates σ) (substitutionStore name prim test) P atoms s
    pattern template frame (θ, n)
  have translated : ground.map (toPattern vname head ∘ groundTerm) =
      (ground.map groundTerm).map (toPattern vname head) := by
    simp [List.map_map]
  refine ⟨((atoms s).filterMap fun A => candidate (substitutionStore name prim test) A
    (instantiate frame pattern) (θ, n)).length + 1, ?_, ?_⟩
  · rw [run]
  rw [run, translated,
    ← spaceMatch_toPattern vinj hinj (ground.map groundTerm)
      (fun a member => by
        obtain ⟨g, -, rfl⟩ := List.mem_map.mp member
        exact groundTerm_freeVars g) _ _]
  simp only [List.map_map, snapshot, List.flatMap_map, Function.comp_def, candidate_ground,
    List.filterMap_eq_flatMap_toList, List.map_flatMap]
  refine List.flatMap_congr fun g _ => ?_
  cases unifyTotal [(groundTerm g, θ.applyTerm (instantiate frame pattern))] with
  | none => rfl
  | some μ => simp [Subst.applyTerm_comp]

end Substitution

end Mettapedia.GSLT.LanguageDef.MatchSteps

#print axioms Mettapedia.GSLT.LanguageDef.MatchSteps.matchSite_answers
#print axioms Mettapedia.GSLT.LanguageDef.MatchSteps.matchPattern_toPattern
#print axioms Mettapedia.GSLT.LanguageDef.MatchSteps.unify_ground_matchPattern
#print axioms Mettapedia.GSLT.LanguageDef.MatchSteps.spaceMatch_toPattern
#print axioms Mettapedia.GSLT.LanguageDef.MatchSteps.matchSite_spaceMatch
