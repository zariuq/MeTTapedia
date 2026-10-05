import Mettapedia.GSLT.Causality.Hierarchy

/-!
# Meta-level contexts against first-class contexts: adaptive interventions

On the response-type GSLT of `Hierarchy`, an intervention is a context the
observer applies from outside: `impose` a treatment on a population or on a
drawn individual.  Here the protocol of an experiment is part of the term: a
population carries a **policy**, a function from what the drawn individual
shows before treatment (its natural treatment) to the treatment imposed.  A
policy is a first-class context computed from data the run observes.

**The meta level is the constant-policy bubble.**
* A constant policy is the external intervention (`internal_do_eq_external`),
  and the meta-level GSLT embeds as the terms with constant policies,
  commuting with interventions (`embed_impose`), step for step
  (`moves_embed`, `moves_of_embed`) and observation for observation
  (`shows_embed`).
* Its guarantee: the treatment imposed on a drawn unit does not depend on the
  unit (`constant_policy_regime_independent`).  This is what makes a
  meta-level intervention an experiment rather than a selection.

**First-class contexts reach beyond it.**  The policy "treat exactly the
naturally untreated" (`flip`) on a population of one always-affected,
naturally untreated individual and one never-affected, naturally treated one
(`twoUnits`) draws units under different regimes (`flip_regime_depends`).  No
meta-level context applied to that population behaves like it, even passively
(`adaptive_not_meta`): the adaptive run reaches the records "treated, effect"
and "untreated, no effect", and every single imposed regime misses one of
them.

**The separation is relative to the model.**  The same behaviour is the
passive behaviour of a different meta-level population, whose natural
treatments are the policy's choices (`adaptive_reencoded`).  What a
first-class context adds is the computation of the regime from the run's own
data on a given model, without rewriting the model.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.AdaptiveContexts

open Mettapedia.GSLT
open Mettapedia.GSLT.MinimalEnablingContext
open Mettapedia.GSLT.AdmissibleContextCongruence
open Mettapedia.GSLT.Causality.Hierarchy
open Mettapedia.GSLT.Causality.Hierarchy.ResponseTypes (Response Quantity)

/-- A stage of an experiment whose protocol is a policy. -/
inductive Stage where
  /-- A population, with the policy that chooses each drawn unit's regime from
  its natural treatment. -/
  | population (individuals : List (Bool × Response)) (policy : Bool → Option Bool)
  /-- A drawn unit: natural treatment, response type, imposed treatment. -/
  | individual (natural : Bool) (response : Response) (imposed : Option Bool)
  /-- The record of a finished unit: treatment received, outcome. -/
  | record (treated effect : Bool)

/-- Drawing applies the policy to the drawn unit's natural treatment; a drawn
unit responds as in `Hierarchy`. -/
inductive Moves : Stage → Stage → Prop where
  | draw {individuals : List (Bool × Response)} {policy : Bool → Option Bool} {natural : Bool}
      {response : Response} :
      (natural, response) ∈ individuals →
        Moves (.population individuals policy) (.individual natural response (policy natural))
  | respond {natural : Bool} {response : Response} {imposed : Option Bool} :
      Moves (.individual natural response imposed)
        (.record (imposed.getD natural) (response.outcome (imposed.getD natural)))

/-- **The GSLT of policy-driven experiments.** -/
abbrev adaptiveGSLT : GSLT where
  Term := Stage
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := Moves
  rewrites_resp_left := by
    intro source source' target equal step
    have same : source = source' := equal
    subst same
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    have same : target = target' := equal
    subst same
    exact step

/-- An external intervention: impose a treatment over the protocol. -/
def impose (treatment : Option Bool) : Stage → Stage
  | .population individuals policy =>
      .population individuals fun natural => treatment.or (policy natural)
  | .individual natural response imposed => .individual natural response (treatment.or imposed)
  | .record treated effect => .record treated effect

/-- The external interventions. -/
abbrev interventions : ContextualRules adaptiveGSLT where
  Context := Option Bool
  identity := none
  compose outer inner := outer.or inner
  plug := impose
  plug_identity term := by cases term <;> rfl
  plug_compose outer inner term := by
    cases outer <;> cases term <;> rfl
  plug_resp _ := by
    intro left right equal
    have same : left = right := equal
    subst same
    rfl
  Rule := Unit
  fires _ := Moves
  fires_resp_left := by
    intro _ left right target equal fires
    have same : left = right := equal
    subst same
    exact ⟨target, fires, rfl⟩
  fires_resp_right := by
    intro _ source target target' fires equal
    have same : target = target' := equal
    subst same
    exact fires
  fires_step := fun fires => fires

/-- A record shows its treatment and its effect. -/
def shows : Quantity → Stage → Prop
  | .treatment, .record treated _ => treated = true
  | .effect, .record _ effect => effect = true
  | _, .population _ _ => False
  | _, .individual _ _ _ => False

/-- The measured quantities. -/
abbrev quantities : ContextualRules.Observations adaptiveGSLT where
  Atom := Quantity
  observes := shows
  observes_resp := by
    intro _ left right equal
    have same : left = right := equal
    subst same
    exact Iff.rfl

/-! ## The meta level as a bubble -/

/-- The meta-level stages, with their imposed treatment as a constant policy. -/
def embed : ResponseTypes.Stage → Stage
  | .population individuals imposed => .population individuals fun _ => imposed
  | .individual natural response imposed => .individual natural response imposed
  | .record treated effect => .record treated effect

/-- **Internal `do` with a constant policy is external `do`.** -/
theorem internal_do_eq_external (individuals : List (Bool × Response)) (treatment : Option Bool) :
    Stage.population individuals (fun _ => treatment) =
      impose treatment (.population individuals fun _ => none) := by
  simp only [impose]
  congr 1
  funext _
  cases treatment <;> rfl

/-- **The embedding commutes with interventions.** -/
theorem embed_impose (treatment : Option Bool) (stage : ResponseTypes.Stage) :
    embed (ResponseTypes.impose treatment stage) = impose treatment (embed stage) := by
  cases stage <;> rfl

/-- The embedding preserves the observations. -/
theorem shows_embed (quantity : Quantity) (stage : ResponseTypes.Stage) :
    shows quantity (embed stage) ↔ ResponseTypes.shows quantity stage := by
  cases quantity <;> cases stage <;> exact Iff.rfl

/-- Every meta-level step is a step of its embedding. -/
theorem moves_embed {source target : ResponseTypes.Stage} (step : ResponseTypes.Moves source target) :
    Moves (embed source) (embed target) := by
  cases step with
  | draw member => exact Moves.draw member
  | respond => exact Moves.respond

/-- Every step of an embedded stage is the embedding of a meta-level step. -/
theorem moves_of_embed {source : ResponseTypes.Stage} {target : Stage}
    (step : Moves (embed source) target) :
    ∃ target', ResponseTypes.Moves source target' ∧ embed target' = target := by
  cases source with
  | population individuals imposed =>
      cases step with
      | draw member => exact ⟨_, ResponseTypes.Moves.draw member, rfl⟩
  | individual natural response imposed =>
      cases step
      exact ⟨_, ResponseTypes.Moves.respond, rfl⟩
  | record treated effect => cases step

/-- **The guarantee of the bubble**: under a constant policy every drawn unit
carries the same regime. -/
theorem constant_policy_regime_independent {individuals : List (Bool × Response)}
    {treatment : Option Bool} {natural : Bool} {response : Response} {imposed : Option Bool}
    (step : Moves (.population individuals fun _ => treatment) (.individual natural response imposed)) :
    imposed = treatment := by
  cases step
  rfl

/-! ## The adaptive policy -/

/-- "Treat exactly the naturally untreated." -/
def flip (natural : Bool) : Option Bool :=
  some (!natural)

/-- An always-affected, naturally untreated unit and a never-affected,
naturally treated one. -/
abbrev twoUnits : List (Bool × Response) :=
  [(false, .always), (true, .never)]

/-- **The policy imposes different regimes on different units.** -/
theorem flip_regime_depends :
    Moves (.population twoUnits flip) (.individual false .always (some true)) ∧
      Moves (.population twoUnits flip) (.individual true .never (some false)) :=
  ⟨Moves.draw (by simp), Moves.draw (by simp)⟩

/-- Two steps to a record. -/
def ReachesRecord (stage : Stage) (treated effect : Bool) : Prop :=
  ∃ middle, Moves stage middle ∧ Moves middle (.record treated effect)

theorem reachesRecord_population_iff (individuals : List (Bool × Response))
    (policy : Bool → Option Bool) (treated effect : Bool) :
    ReachesRecord (.population individuals policy) treated effect ↔
      ∃ unit ∈ individuals, (policy unit.1).getD unit.1 = treated ∧ unit.2.outcome treated = effect := by
  constructor
  · rintro ⟨middle, first, second⟩
    cases first with
    | @draw _ _ natural response member =>
        cases second
        exact ⟨(natural, response), member, rfl, rfl⟩
  · rintro ⟨⟨natural, response⟩, member, rfl, rfl⟩
    exact ⟨_, Moves.draw member, Moves.respond⟩

/-- Reduction-bisimilar stages reach the same records in two steps. -/
theorem reachesRecord_of_bisimilar {left right : Stage}
    (bisimilar : ReductionBisimilar quantities left right) {treated effect : Bool}
    (reaches : ReachesRecord left treated effect) : ReachesRecord right treated effect := by
  obtain ⟨relation, ⟨⟨forward, _⟩, atoms⟩, related⟩ := bisimilar
  obtain ⟨middle, first, second⟩ := reaches
  obtain ⟨middle', first', related'⟩ := forward related first
  obtain ⟨final, second', related''⟩ := forward related' second
  have treatedSame := atoms related'' .treatment
  have effectSame := atoms related'' .effect
  refine ⟨middle', first', ?_⟩
  cases first' with
  | draw member =>
      cases second'
      change (treated = true ↔ _ = true) at treatedSame
      change (effect = true ↔ _ = true) at effectSame
      rw [Bool.coe_iff_coe.mp treatedSame, Bool.coe_iff_coe.mp effectSame]
      exact Moves.respond
  | respond => cases second'

/-- The adaptive run treats the always-affected unit and shows the effect. -/
theorem adaptive_reaches_treated_effect : ReachesRecord (.population twoUnits flip) true true :=
  (reachesRecord_population_iff _ _ _ _).mpr ⟨(false, .always), by simp, rfl, rfl⟩

/-- The adaptive run leaves the never-affected unit untreated, with no effect. -/
theorem adaptive_reaches_untreated_none : ReachesRecord (.population twoUnits flip) false false :=
  (reachesRecord_population_iff _ _ _ _).mpr ⟨(true, .never), by simp, rfl, rfl⟩

/-- **Every single regime misses one of the two records.** -/
theorem constant_policy_misses (treatment : Option Bool) :
    ¬ (ReachesRecord (.population twoUnits fun _ => treatment) true true ∧
      ReachesRecord (.population twoUnits fun _ => treatment) false false) := by
  rw [reachesRecord_population_iff, reachesRecord_population_iff]
  cases treatment with
  | none => simp [Response.outcome]
  | some value => cases value <;> simp [Response.outcome]

/-- **No meta-level intervention on the model behaves like the adaptive
policy**, even at rung one: for every imposed regime, the intervened model and
the adaptive program are not reduction bisimilar. -/
theorem adaptive_not_meta (treatment : Option Bool) :
    ¬ ReductionBisimilar quantities
      (embed (ResponseTypes.impose treatment (.population twoUnits none)))
      (.population twoUnits flip) := by
  intro bisimilar
  have backward := reductionBisimilar_symm quantities bisimilar
  have intervened : embed (ResponseTypes.impose treatment (.population twoUnits none)) =
      .population twoUnits fun _ => treatment := by
    rw [embed_impose, internal_do_eq_external]
    rfl
  rw [intervened] at backward
  exact constant_policy_misses treatment
    ⟨reachesRecord_of_bisimilar backward adaptive_reaches_treated_effect,
      reachesRecord_of_bisimilar backward adaptive_reaches_untreated_none⟩

/-! ## Relative to the model -/

/-- The units the policy's choices make natural. -/
abbrev reencodedUnits : List (Bool × Response) :=
  [(true, .always), (false, .never)]

/-- The pairs matched by re-encoding the policy into natural treatments. -/
def Reencoding (left right : Stage) : Prop :=
  left = right ∨
    (left = .population twoUnits flip ∧ right = .population reencodedUnits fun _ => none) ∨
    (left = .individual false .always (some true) ∧ right = .individual true .always none) ∨
    (left = .individual true .never (some false) ∧ right = .individual false .never none)

theorem reencoding_isReductionBisimulation : IsReductionBisimulation quantities Reencoding := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro left right (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) left' step
    · exact ⟨left', step, Or.inl rfl⟩
    · have moves : Moves (.population twoUnits flip) left' := step
      cases moves with
      | draw member =>
          simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
          rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨_, Moves.draw (by simp), Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
          · exact ⟨_, Moves.draw (by simp), Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
    · have moves : Moves (.individual false .always (some true)) left' := step
      cases moves
      exact ⟨_, Moves.respond, Or.inl rfl⟩
    · have moves : Moves (.individual true .never (some false)) left' := step
      cases moves
      exact ⟨_, Moves.respond, Or.inl rfl⟩
  · rintro left right (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) right' step
    · exact ⟨right', step, Or.inl rfl⟩
    · have moves : Moves (.population reencodedUnits fun _ => none) right' := step
      cases moves with
      | draw member =>
          simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
          rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨_, Moves.draw (by simp), Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
          · exact ⟨_, Moves.draw (by simp), Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
    · have moves : Moves (.individual true .always none) right' := step
      cases moves
      exact ⟨_, Moves.respond, Or.inl rfl⟩
    · have moves : Moves (.individual false .never none) right' := step
      cases moves
      exact ⟨_, Moves.respond, Or.inl rfl⟩
  · rintro left right (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) atom <;>
      cases atom <;> exact Iff.rfl

/-- **The adaptive behaviour is a meta-level behaviour of a different model**:
the population whose natural treatments are the policy's choices. -/
theorem adaptive_reencoded :
    ReductionBisimilar quantities (.population twoUnits flip)
      (embed (.population reencodedUnits none)) :=
  ⟨Reencoding, reencoding_isReductionBisimulation, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩

end Mettapedia.GSLT.Causality.AdaptiveContexts
