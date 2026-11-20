import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope.Hiding
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope.CompositionControls

/-!
# Hiding at first-order terms: a bisimulation, and the projection by solved forms

At the first-order action (`FirstOrder.action`), at the one frame.

## Freshness reads only the unknowns a state mentions

`fresh_iff_of_unknowns`: two states that mention the same unknowns have the same fresh openings,
because a substitution agrees with another on a term exactly when it agrees on the term's unknowns
(`agree_of_applyTerm_eq`).

## The bisimulation

`HiddenFO s s'`: `s` and `s'` hide each other (`Hides`: same rows, knowledge seen alike from the rows)
and their knowledges mention the same unknowns. Then every opening fresh at one is fresh at the other,
and **`succ_hiddenFO`**: every successor of `s` is matched by a successor of `s'` by the same firing,
and the two are again related; the relation is symmetric (`HiddenFO.symm`). So it is a bisimulation
of the step of every program, and reachable success under any barb is the same
(`reaches_iff_of_hiddenFO`).

## The projection by solved forms

For a solvable store `K` with most general unifier `θ` (`unifyTotal`) and a set `H` of unknowns that no
row mentions, `hideStore θ H K` keeps the solved equation `v = θ v` of every unknown of `K` outside `H`
and keeps each unknown of `H` only as a name (the equation `h = h`).

* `seenAlike_hide`: it is seen alike from the rows (`SeenAlike`), by idempotence and relevance of the
  solved form; `unknowns_hide`: it mentions the same unknowns.
* **`hiddenFO_hide`**: so a state and its hiding are related by the bisimulation, for every program.

What the projection cannot do: the unknowns of `H` that occur inside a kept solved equation stay as
existential witnesses (`x = f(h)` keeps `h`). Dropping every equation that mentions a hidden unknown
is unsound (`HidingControls.naive_drop_not_seen_alike`): `x = f(h)` with `h` hidden constrains `x`
to the shape `f(_)`, which the empty store does not. And the hidden store is genuinely weaker
(`HidingControls.hiding_forgets`): from `x = 5, h = x` with `h` hidden, the hidden store admits
`h = 7`. After hiding, knowledge no longer only grows.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open LogicOverTheStep.StepSpan (Succ)
open OneFrame (Terms frames ext)
open Mettapedia.Logic.LP

universe uO

section FirstOrderHiding

variable {sig : LPSignature} [DecidableEq sig.vars] {O : Type uO} [DecidableEq O]

local notation "FO" => FirstOrder.action sig

omit [DecidableEq O] in
/-- **Freshness reads only the unknowns a state mentions.** -/
theorem fresh_of_unknowns {P : Program (Terms (Term sig))} {s s' : State (Terms (Term sig)) O}
    (same : ∀ v, UnknownsOf s'.Mentions v → UnknownsOf s.Mentions v)
    {f : Firing O (ext FO) P PUnit.unit} (fresh : f.Fresh (frames FO) s) : f.Fresh (frames FO) s' := by
  intro b g h
  obtain ⟨u, onS, onRule⟩ := fresh b g h
  refine ⟨u, fun t mentioned => ?_, onRule⟩
  show Subst.applyTerm u (Subst.applyTerm (Subst.id sig) t) = Subst.applyTerm g t
  rw [Subst.applyTerm_id]
  apply Subst.applyTerm_congr
  intro v inside
  obtain ⟨t₀, mentioned₀, inside₀⟩ := same v ⟨t, mentioned, inside⟩
  have atT₀ : Subst.applyTerm u (Subst.applyTerm (Subst.id sig) t₀) = Subst.applyTerm g t₀ :=
    onS t₀ mentioned₀
  rw [Subst.applyTerm_id] at atT₀
  exact agree_of_applyTerm_eq t₀ atT₀ v inside₀

omit [DecidableEq O] in
theorem fresh_iff_of_unknowns {P : Program (Terms (Term sig))} {s s' : State (Terms (Term sig)) O}
    (same : ∀ v, UnknownsOf s.Mentions v ↔ UnknownsOf s'.Mentions v)
    (f : Firing O (ext FO) P PUnit.unit) : f.Fresh (frames FO) s ↔ f.Fresh (frames FO) s' :=
  ⟨fresh_of_unknowns fun v => (same v).mpr, fresh_of_unknowns fun v => (same v).mp⟩

/-- **The hiding relation at first-order terms**: the two states hide each other and their knowledges
mention the same unknowns. -/
structure HiddenFO (s s' : State (Terms (Term sig)) O) : Prop where
  hides : Hides FO s s'
  unknowns : ∀ v, UnknownsOf (StoreTerms s.knowledge) v ↔ UnknownsOf (StoreTerms s'.knowledge) v

omit [DecidableEq O] in
theorem HiddenFO.symm {s s' : State (Terms (Term sig)) O} (hidden : HiddenFO s s') : HiddenFO s' s :=
  ⟨hidden.hides.symm, fun v => (hidden.unknowns v).symm⟩

omit [DecidableEq O] in
theorem unknowns_mentions {s : State (Terms (Term sig)) O} (v : sig.vars) :
    UnknownsOf s.Mentions v ↔ UnknownsOf (StoreTerms s.knowledge) v ∨ UnknownsOf (Rows s) v := by
  constructor
  · rintro ⟨t, first | second | row, inside⟩
    · exact Or.inl ⟨t, Or.inl first, inside⟩
    · exact Or.inl ⟨t, Or.inr second, inside⟩
    · exact Or.inr ⟨t, row, inside⟩
  · rintro (⟨t, first | second, inside⟩ | ⟨t, row, inside⟩)
    · exact ⟨t, Or.inl first, inside⟩
    · exact ⟨t, Or.inr (Or.inl second), inside⟩
    · exact ⟨t, Or.inr (Or.inr row), inside⟩

omit [DecidableEq O] in
theorem HiddenFO.mentions {s s' : State (Terms (Term sig)) O} (hidden : HiddenFO s s') (v : sig.vars) :
    UnknownsOf s.Mentions v ↔ UnknownsOf s'.Mentions v := by
  rw [unknowns_mentions, unknowns_mentions, hidden.unknowns v,
    rows_eq hidden.hides.present hidden.hides.label]

omit [DecidableEq sig.vars] [DecidableEq O] in
theorem storeTerms_append {K L : EquationStore (Term sig)} {t : Term sig} :
    StoreTerms (K ++ L) t ↔ StoreTerms K t ∨ StoreTerms L t := by
  unfold StoreTerms
  simp only [List.map_append, List.mem_append]
  tauto

omit [DecidableEq O] in
theorem unknowns_append {K L : EquationStore (Term sig)} (v : sig.vars) :
    UnknownsOf (StoreTerms (K ++ L)) v ↔ UnknownsOf (StoreTerms K) v ∨ UnknownsOf (StoreTerms L) v := by
  constructor
  · rintro ⟨t, member, inside⟩
    rcases storeTerms_append.mp member with inK | inL
    · exact Or.inl ⟨t, inK, inside⟩
    · exact Or.inr ⟨t, inL, inside⟩
  · rintro (⟨t, inK, inside⟩ | ⟨t, inL, inside⟩)
    · exact ⟨t, storeTerms_append.mpr (Or.inl inK), inside⟩
    · exact ⟨t, storeTerms_append.mpr (Or.inr inL), inside⟩

/-- **The results of one firing at related states are related.** -/
theorem hiddenFO_result {P : Program (Terms (Term sig))} {s s' : State (Terms (Term sig)) O}
    (hidden : HiddenFO s s') {f : Firing O (ext FO) P PUnit.unit}
    (admitted : (step (frames FO) O (ext FO) P).Admits (s := s) f) :
    HiddenFO (f.result (frames FO) s) (f.result (frames FO) s') := by
  have fresh : f.Fresh (frames FO) s := admitted.1.1
  have fresh' : f.Fresh (frames FO) s' := (fresh_iff_of_unknowns hidden.mentions f).mp fresh
  refine ⟨hides_result hidden.hides fresh fresh' admitted, fun v => ?_⟩
  show UnknownsOf (StoreTerms (f.information (frames FO) s)) v ↔
    UnknownsOf (StoreTerms (f.information (frames FO) s')) v
  rw [information_eq_append, information_eq_append, unknowns_append, unknowns_append, hidden.unknowns v,
    ownInformation_congr f hidden.hides.label]

/-- **The bisimulation**: every successor of `s` is matched by a successor of `s'`, by the same
firing, and the two are again related. -/
theorem succ_hiddenFO {P : Program (Terms (Term sig))} {s s' t : State (Terms (Term sig)) O}
    (hidden : HiddenFO s s') (reached : Succ (step (frames FO) O (ext FO) P).toStep s t) :
    ∃ t', Succ (step (frames FO) O (ext FO) P).toStep s' t' ∧ HiddenFO t t' := by
  obtain ⟨f, admitted, rfl⟩ := reached
  have fresh : f.Fresh (frames FO) s := admitted.1.1
  have fresh' : f.Fresh (frames FO) s' := (fresh_iff_of_unknowns hidden.mentions f).mp fresh
  exact ⟨_, ⟨f, admits_of_hides hidden.hides fresh fresh' admitted, rfl⟩, hiddenFO_result hidden admitted⟩

theorem runs_hiddenFO {P : Program (Terms (Term sig))} {s s' t : State (Terms (Term sig)) O}
    (hidden : HiddenFO s s') (run : Relation.ReflTransGen (Succ (step (frames FO) O (ext FO) P).toStep) s t) :
    ∃ t', Relation.ReflTransGen (Succ (step (frames FO) O (ext FO) P).toStep) s' t' ∧ HiddenFO t t' := by
  induction run with
  | refl => exact ⟨s', Relation.ReflTransGen.refl, hidden⟩
  | tail _ last ih =>
      obtain ⟨u', run', related⟩ := ih
      obtain ⟨t', step', related'⟩ := succ_hiddenFO related last
      exact ⟨t', run'.tail step', related'⟩

omit [DecidableEq O] in
theorem succeeds_of_hiddenFO {barb : Term sig → Prop} {s s' : State (Terms (Term sig)) O}
    (hidden : HiddenFO s s') (succeeds : Succeeds barb s) : Succeeds barb s' := by
  obtain ⟨o, present, holds⟩ := succeeds
  refine ⟨o, hidden.hides.present ▸ present, ?_⟩
  rw [← hidden.hides.label]
  exact holds

/-- **Reachable success is the same at related states**, for every program and every barb. -/
theorem reaches_iff_of_hiddenFO {P : Program (Terms (Term sig))} {barb : Term sig → Prop}
    {s s' : State (Terms (Term sig)) O} (hidden : HiddenFO s s') :
    (∃ t, Relation.ReflTransGen (Succ (step (frames FO) O (ext FO) P).toStep) s t ∧ Succeeds barb t) ↔
      ∃ t', Relation.ReflTransGen (Succ (step (frames FO) O (ext FO) P).toStep) s' t' ∧ Succeeds barb t' := by
  constructor
  · rintro ⟨t, run, holds⟩
    obtain ⟨t', run', related⟩ := runs_hiddenFO hidden run
    exact ⟨t', run', succeeds_of_hiddenFO related holds⟩
  · rintro ⟨t', run', holds⟩
    obtain ⟨t, run, related⟩ := runs_hiddenFO hidden.symm run'
    exact ⟨t, run, succeeds_of_hiddenFO related holds⟩

/-! ## The projection by solved forms -/

variable [DecidableEq sig.constants] [DecidableEq sig.functionSymbols]

/-- **Hide the unknowns `H` from a store by its solved form `θ`**: keep the solved equation of every
unknown of the store outside `H`, and keep each unknown of `H` only as a name. -/
noncomputable def hideStore (θ : Subst sig) (H : Finset sig.vars) (K : EquationStore (Term sig)) :
    EquationStore (Term sig) :=
  ((eqVars K).filter (· ∉ H)).toList.map (fun v => (Term.var v, θ v)) ++
    ((eqVars K).filter (· ∈ H)).toList.map (fun v => (Term.var v, Term.var v))

omit [DecidableEq O] [DecidableEq sig.constants] [DecidableEq sig.functionSymbols] in
theorem mem_hideStore {θ : Subst sig} {H : Finset sig.vars} {K : EquationStore (Term sig)}
    {e : Equation (Term sig)} :
    e ∈ hideStore θ H K ↔ (∃ v ∈ eqVars K, v ∉ H ∧ e = (Term.var v, θ v)) ∨
      ∃ v ∈ eqVars K, v ∈ H ∧ e = (Term.var v, Term.var v) := by
  unfold hideStore
  simp only [List.mem_append, List.mem_map, Finset.mem_toList, Finset.mem_filter]
  constructor
  · rintro (⟨v, ⟨inK, outH⟩, rfl⟩ | ⟨v, ⟨inK, inH⟩, rfl⟩)
    · exact Or.inl ⟨v, inK, outH, rfl⟩
    · exact Or.inr ⟨v, inK, inH, rfl⟩
  · rintro (⟨v, inK, outH, rfl⟩ | ⟨v, inK, inH, rfl⟩)
    · exact Or.inl ⟨v, ⟨inK, outH⟩, rfl⟩
    · exact Or.inr ⟨v, ⟨inK, inH⟩, rfl⟩

/-- **The hidden store is seen alike from any family that avoids the hidden unknowns.** -/
theorem seenAlike_hide {K : EquationStore (Term sig)} {θ : Subst sig} (accepted : unifyTotal K = some θ)
    {H : Finset sig.vars} {F : Term sig → Prop} (avoid : ∀ v, UnknownsOf F v → v ∉ H) :
    SeenAlike FO K (hideStore θ H K) F := by
  classical
  have relevant := unifyTotal_relevantIdempotent K θ accepted
  constructor
  · intro σ solved
    have absorbs : σ.Absorbs θ :=
      Subst.absorbs_of_moreGeneral relevant.absorbs (unifyTotal_mgu K θ accepted σ solved)
    refine ⟨σ, fun e member => ?_, fun t _ => rfl⟩
    rcases mem_hideStore.mp member with ⟨v, -, -, rfl⟩ | ⟨v, -, -, rfl⟩
    · exact (absorbs v).symm
    · rfl
  · intro σ' solved'
    let σ : Subst sig := fun v => if v ∈ H then Subst.applyTerm σ' (θ v) else σ' v
    have onRange : ∀ v, ∀ w ∈ (θ v).freeVars, σ w = σ' w := by
      intro v w inside
      have unbound : θ w = Term.var w := relevant.unbound v w inside
      show (if w ∈ H then Subst.applyTerm σ' (θ w) else σ' w) = σ' w
      split_ifs
      · rw [unbound]
        rfl
      · rfl
    have absorbs : σ.Absorbs θ := by
      intro v
      rw [Subst.applyTerm_congr (onRange v)]
      by_cases hidden : v ∈ H
      · show Subst.applyTerm σ' (θ v) = if v ∈ H then Subst.applyTerm σ' (θ v) else σ' v
        rw [if_pos hidden]
      · show Subst.applyTerm σ' (θ v) = if v ∈ H then Subst.applyTerm σ' (θ v) else σ' v
        rw [if_neg hidden]
        by_cases inK : v ∈ eqVars K
        · have kept : (Term.var v, θ v) ∈ hideStore θ H K := mem_hideStore.mpr (Or.inl ⟨v, inK, hidden, rfl⟩)
          exact (solved' _ kept).symm
        · rw [relevant.fixes v inK]
          rfl
    refine ⟨σ, fun e member => ?_, fun t holds => ?_⟩
    · have unified : Subst.applyTerm θ e.1 = Subst.applyTerm θ e.2 := unifyTotal_sound K θ accepted e member
      show Subst.applyTerm σ e.1 = Subst.applyTerm σ e.2
      rw [← absorbs.applyTerm e.1, ← absorbs.applyTerm e.2, unified]
    · show Subst.applyTerm σ t = Subst.applyTerm σ' t
      apply Subst.applyTerm_congr
      intro v inside
      show (if v ∈ H then Subst.applyTerm σ' (θ v) else σ' v) = σ' v
      rw [if_neg (avoid v ⟨t, holds, inside⟩)]

omit [DecidableEq O] [DecidableEq sig.constants] [DecidableEq sig.functionSymbols] in
theorem unknowns_storeTerms_iff {K : EquationStore (Term sig)} (v : sig.vars) :
    UnknownsOf (StoreTerms K) v ↔ v ∈ eqVars K := by
  rw [mem_eqVars]
  constructor
  · rintro ⟨t, first | second, inside⟩
    · obtain ⟨e, member, rfl⟩ := List.mem_map.mp first
      exact ⟨e, member, Or.inl inside⟩
    · obtain ⟨e, member, rfl⟩ := List.mem_map.mp second
      exact ⟨e, member, Or.inr inside⟩
  · rintro ⟨e, member, inside | inside⟩
    · exact ⟨e.1, (storeTerms_of_mem member).1, inside⟩
    · exact ⟨e.2, (storeTerms_of_mem member).2, inside⟩

/-- **The hidden store mentions the same unknowns.** -/
theorem unknowns_hide {K : EquationStore (Term sig)} {θ : Subst sig} (accepted : unifyTotal K = some θ)
    (H : Finset sig.vars) (v : sig.vars) :
    UnknownsOf (StoreTerms K) v ↔ UnknownsOf (StoreTerms (hideStore θ H K)) v := by
  have relevant := unifyTotal_relevantIdempotent K θ accepted
  rw [unknowns_storeTerms_iff, unknowns_storeTerms_iff, mem_eqVars (equations := hideStore θ H K)]
  constructor
  · intro inK
    by_cases hidden : v ∈ H
    · exact ⟨(Term.var v, Term.var v), mem_hideStore.mpr (Or.inr ⟨v, inK, hidden, rfl⟩),
        Or.inl (Term.mem_freeVars_var.mpr rfl)⟩
    · exact ⟨(Term.var v, θ v), mem_hideStore.mpr (Or.inl ⟨v, inK, hidden, rfl⟩),
        Or.inl (Term.mem_freeVars_var.mpr rfl)⟩
  · rintro ⟨e, member, inside⟩
    rcases mem_hideStore.mp member with ⟨w, inK, -, rfl⟩ | ⟨w, inK, -, rfl⟩
    · rcases inside with inside | inside
      · rw [Term.mem_freeVars_var.mp inside]
        exact inK
      · exact relevant.range w inK inside
    · rcases inside with inside | inside <;> (rw [Term.mem_freeVars_var.mp inside]; exact inK)

/-- A state with its knowledge replaced. -/
def withKnowledge (s : State (Terms (Term sig)) O) (K : EquationStore (Term sig)) :
    State (Terms (Term sig)) O :=
  ⟨PUnit.unit, K, s.present, s.label⟩

omit [DecidableEq O] in
/-- **A state and its hiding are related by the bisimulation**, when no row mentions a hidden
unknown and the knowledge has the solved form `θ`. -/
theorem hiddenFO_hide {s : State (Terms (Term sig)) O} {θ : Subst sig}
    (accepted : unifyTotal s.knowledge = some θ) {H : Finset sig.vars}
    (avoid : ∀ v, UnknownsOf (Rows s) v → v ∉ H) :
    HiddenFO s (withKnowledge s (hideStore θ H s.knowledge)) :=
  ⟨⟨rfl, rfl, seenAlike_hide accepted avoid⟩, fun v => unknowns_hide accepted H v⟩

end FirstOrderHiding

#print axioms fresh_iff_of_unknowns
#print axioms hiddenFO_result
#print axioms succ_hiddenFO
#print axioms reaches_iff_of_hiddenFO
#print axioms seenAlike_hide
#print axioms unknowns_hide
#print axioms hiddenFO_hide

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope
