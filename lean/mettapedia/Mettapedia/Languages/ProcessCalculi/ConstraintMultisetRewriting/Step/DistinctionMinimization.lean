import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DistinctionMachine

/-!
# The computed relation is the coarsest exact behavioural quotient

Refinement is characterized by the existing observation-preserving
bisimulation semantics. Its result is therefore an equivalence relation,
and every exact encoding refines it. This establishes optimality of the
computed finite partition; stability of a supplied partition alone would
not establish that claim.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DistinctionFinite
open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
universe uS uA uV
variable {S : Type uS} {A : Type uA} {V : Type uV}
namespace Machine
variable (M : Machine S A V)

def theory : GSLT where
  Term := S
  equations := ⟨Eq, eq_equivalence⟩
  rewrites s t := ∃ a, t ∈ M.next s a
  rewrites_resp_left := by intro s s' t same move; exact ⟨t, same ▸ move, rfl⟩
  rewrites_resp_right := by intro s t t' move same; exact same ▸ move

def system : System M.theory where
  Atom := V
  observes v s := M.read s = v
  observes_resp := by intro v s t same; cases same; rfl
  Label := A
  act a s t := t ∈ M.next s a
  act_resp_left := by intro a s s' t same move; exact ⟨t, same ▸ move, rfl⟩
  act_resp_right := by intro a s t t' move same; exact same ▸ move

variable [DecidableEq S] [Fintype A] [DecidableEq V]

omit [Fintype A] [DecidableEq V] in
theorem mem_swap_iff {r : Finset (S × S)} {s t : S} :
    (s, t) ∈ r.image Prod.swap ↔ (t, s) ∈ r := by
  constructor
  · rintro member
    obtain ⟨⟨u, v⟩, inside, same⟩ := Finset.mem_image.mp member
    cases same
    exact inside
  · intro inside
    exact Finset.mem_image.mpr ⟨(t, s), inside, rfl⟩

theorem stable_iff_bisimulation (r : Finset (S × S)) :
    M.Stable r ↔ M.system.IsBisimulation (fun s t => (s, t) ∈ r) := by
  constructor
  · intro stable
    refine ⟨?_, ?_, ?_⟩
    · intro s t related a s' move
      exact (M.stable_good stable related).2 a |>.1 s' move
    · intro s t related a t' move
      obtain ⟨s', move', related'⟩ := (M.stable_good stable related).2 a |>.2 t' move
      exact ⟨s', move', mem_swap_iff.mp related'⟩
    · intro s t related v
      change M.read s = v ↔ M.read t = v
      rw [(M.stable_good stable related).1]
  · rintro ⟨forth, back, atoms⟩
    apply Finset.Subset.antisymm (M.refine_subset _)
    intro p member
    refine Finset.mem_filter.mpr ⟨member, ?_, fun a => ⟨?_, ?_⟩⟩
    · exact (atoms member (M.read p.2)).mpr rfl
    · intro s' move
      exact forth member a move
    · intro t' move
      obtain ⟨s', move', related⟩ := back member a move
      exact ⟨s', move', mem_swap_iff.mpr related⟩

variable [Fintype S]

/-- Soundness and completeness of the computed relation for labelled behavioural identity. -/
theorem mem_behaviour_iff (s t : S) :
    (s, t) ∈ M.behaviour ↔ M.system.Bisimilar s t := by
  constructor
  · intro member
    exact ⟨_, (M.stable_iff_bisimulation _).mp M.behaviour_stable, member⟩
  · rintro ⟨R, ⟨forth, back, atoms⟩, related⟩
    classical
    let r : Finset (S × S) := Finset.univ.filter fun p => R p.1 p.2
    have mem (x y : S) : (x, y) ∈ r ↔ R x y := by simp [r]
    have stable : M.Stable r := (M.stable_iff_bisimulation r).mpr ⟨
      fun _ _ h a _ move => by
        obtain ⟨y, move', rel⟩ := forth ((mem _ _).mp h) a move
        exact ⟨y, move', (mem _ _).mpr rel⟩,
      fun _ _ h a _ move => by
        obtain ⟨x, move', rel⟩ := back ((mem _ _).mp h) a move
        exact ⟨x, move', (mem _ _).mpr rel⟩,
      fun _ _ h v => atoms ((mem _ _).mp h) v⟩
    exact M.behaviour_greatest stable ((mem _ _).mpr related)

def behaviouralSetoid : Setoid S where
  r s t := (s, t) ∈ M.behaviour
  iseqv := ⟨fun s => (M.mem_behaviour_iff s s).mpr (M.system.bisimilar_refl s),
    fun h => (M.mem_behaviour_iff _ _).mpr (M.system.bisimilar_symm ((M.mem_behaviour_iff _ _).mp h)),
    fun h k => (M.mem_behaviour_iff _ _).mpr
      (M.system.bisimilar_trans ((M.mem_behaviour_iff _ _).mp h) ((M.mem_behaviour_iff _ _).mp k))⟩

/-- Every accepted exact encoding keeps at least the distinctions of the computed partition. -/
theorem checked_refines_behaviour {Q : Type*} [DecidableEq Q] (encode : S → Q)
    (checked : M.checkEncoding encode = true) {s t : S} (same : encode s = encode t) :
    (s, t) ∈ M.behaviour :=
  M.behaviour_greatest ((M.checkEncoding_iff encode).mp checked)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, same⟩)

end Machine
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DistinctionFinite
