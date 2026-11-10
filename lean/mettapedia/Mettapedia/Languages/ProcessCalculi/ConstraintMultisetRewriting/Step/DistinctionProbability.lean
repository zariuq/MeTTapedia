import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DistinctionObserver
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DistinctionMachine
import Mettapedia.GSLT.Distinction.Probabilistic.System

/-!
# Probability observers of transform programs

An action-indexed subdistribution is read by the existing probabilistic
distinction semantics. Sound support relates its positive-weight outcomes to
actual transform firings; complete support is a separate, optional law.
This permits policies assigning zero probability to otherwise possible moves
without identifying the policy with the full nondeterministic program.

For an encoding, preservation of all pushed-forward code masses and current
readings is exactly probabilistic bisimulation of its kernel. The statement
includes refusal mass through the mass of the whole space.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DistinctionProbability
open Interface
open Mettapedia.GSLT.Distinction.Probabilistic

universe uOb uT uH uO uS uF uL uV uQ
variable {Obj : Type uOb} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uO} [DecidableEq O] {State : Type uS}
  {Fir : State → Type uF} {L : Type uL} {V : Type uV} {Code : Type uQ}
  (P : Interface.Step X O State Fir) (offers : L → (s : State) → Fir s → Prop)
  (read : State → V) (law : L → State → SubDistribution State)

def system : ProbabilisticSystem (Race.Generic.gslt P offers) where
  Atom := V
  observes value s := read s = value
  observes_resp := by intro value s t same; cases same; rfl
  Label := L
  kernel := law
  kernel_resp := by intro label s t same predicate closed; cases same; rfl

def SoundSupport : Prop :=
  ∀ a s t, 0 < (law a s).weight t → Race.Generic.Moves P offers s a t

def CompleteSupport : Prop :=
  ∀ a s t, Race.Generic.Moves P offers s a t → 0 < (law a s).weight t

theorem support_implies_move (sound : SoundSupport P offers law) {a : L} {s t : State}
    (supported : (system P offers read law).support.act a s t) : Race.Generic.Moves P offers s a t := by
  obtain ⟨u, member, same⟩ := supported
  cases same
  exact sound a s t ((law a s).weight_pos member)

theorem support_iff_move (sound : SoundSupport P offers law) (complete : CompleteSupport P offers law)
    (a : L) (s t : State) :
    (system P offers read law).support.act a s t ↔ Race.Generic.Moves P offers s a t := by
  constructor
  · exact support_implies_move P offers read law sound
  · intro moved
    exact ⟨t, Finsupp.mem_support_iff.mpr (ne_of_gt (complete a s t moved)), rfl⟩

def PreservesMass (encode : State → Code) : Prop :=
  ∀ s t, encode s = encode t → ∀ a (event : Code → Prop),
    (law a s).mass (event ∘ encode) = (law a t).mass (event ∘ encode)

/-- Preserving total mass also preserves the missing (refusal) mass. -/
theorem refusal_mass_eq (encode : State → Code) (preserves : PreservesMass law encode)
    {s t : State} (same : encode s = encode t) (a : L) :
    1 - (law a s).mass (fun _ => True) = 1 - (law a t).mass (fun _ => True) :=
  congrArg (fun total : ℝ => 1 - total) (preserves s t same a (fun _ => True))

/-- Exact stochastic abstraction is mass preservation, not merely support matching. -/
theorem exact_iff_probabilistic_bisimulation (encode : State → Code) :
    DistinctionObserver.Reads encode read ∧ PreservesMass law encode ↔
      (system P offers read law).IsLSBisimulation (fun s t => encode s = encode t) := by
  constructor
  · rintro ⟨reads, masses⟩
    refine ⟨⟨fun _ => rfl, Eq.symm, Eq.trans⟩,
      fun same => congrArg encode same, ?_, ?_⟩
    · intro s t same value
      change read s = value ↔ read t = value
      rw [reads s t same]
    · intro s t same a event closed
      let codeEvent : Code → Prop := fun c => ∃ u, encode u = c ∧ event u
      have event_iff (u : State) : codeEvent (encode u) ↔ event u := by
        constructor
        · rintro ⟨v, equal, holds⟩
          exact (closed v u equal).mp holds
        · intro holds
          exact ⟨u, rfl, holds⟩
      change (law a s).mass event = (law a t).mass event
      calc
        (law a s).mass event = (law a s).mass (codeEvent ∘ encode) :=
          (law a s).mass_congr (fun u _ => (event_iff u).symm)
        _ = (law a t).mass (codeEvent ∘ encode) := masses s t same a codeEvent
        _ = (law a t).mass event := (law a t).mass_congr (fun u _ => event_iff u)
  · intro bisim
    refine ⟨fun s t same => (bisim.observes same (read t)).mpr rfl, ?_⟩
    intro s t same a event
    apply bisim.masses same a (event ∘ encode)
    intro x y equal
    simp only [Function.comp_apply, equal]

/-- Injective recoding retains exact mass compatibility; arbitrary merging need not. -/
theorem mass_recode {Other : Type*} (encode : State → Code) (summarize : Code → Other)
    (preserves : PreservesMass law encode)
    (reflects : Function.Injective summarize) : PreservesMass law (summarize ∘ encode) := by
  intro s t same a event
  exact preserves s t (reflects same) a (event ∘ summarize)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DistinctionProbability

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DistinctionProbability.Controls
open Mettapedia.GSLT.Distinction.Probabilistic
open DistinctionFinite

noncomputable def point {S : Type*} (s : S) : SubDistribution S where
  weight := Finsupp.single s 1
  nonneg t := by
    classical
    by_cases same : s = t <;> simp [same]
  total_le_one := by
    classical
    simp

theorem point_positive_iff {S : Type*} (s t : S) : 0 < (point s).weight t ↔ t = s := by
  classical
  by_cases same : s = t
  · subst t; simp [point]
  · simp [point, Ne.symm same]

def machine : Machine Bool Unit Bool := ⟨id, fun _ _ => [false, true]⟩
noncomputable def chooseFalse (_ : Unit) (s : Nat × Bool) : SubDistribution (Nat × Bool) :=
  point (s.1 + 1, false)

theorem chosen_policy_sound : SoundSupport machine.step.toStep Machine.offers chooseFalse := by
  intro a s t positive
  have same := (point_positive_iff (s.1 + 1, false) t).mp positive
  subst t
  exact machine.every_successor_fires s a false (by simp [machine])

/-- Zero-weight alternatives remain semantically possible in the uncommitted program. -/
theorem chosen_policy_not_complete : ¬ CompleteSupport machine.step.toStep Machine.offers chooseFalse := by
  intro complete
  have positive := complete () (0, false) (1, true)
    (machine.every_successor_fires _ _ _ (by simp [machine]))
  have impossible := (point_positive_iff (1, false) (1, true)).mp positive
  cases impossible

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DistinctionProbability.Controls
