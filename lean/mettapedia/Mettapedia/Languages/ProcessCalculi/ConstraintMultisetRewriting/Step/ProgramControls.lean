import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramInterface

/-!
# Which resumption law: one-shot or per demand

The successor function is exact for every well formed schema, not only the core's
(`fires_iff_schemaSuccessors`), so variant rules are compared by computation.

* **The core's law** takes the demand and reads the suspended continuation: it resumes the
  continuation exactly once per demand (`Program.exactly_once_per_demand`, `Program.demand_balance`).
* **A one-shot continuation** takes both (`oneShot`). From one suspended continuation and two demands
  it resumes once in all, and one demand is never served (`oneShot_resumes_once`).
* **A resumption that reads its demand** replays it without bound (`Program.replay_unbounded`).

So the right law for a suspended continuation resumed on demand is: take the demand, read the
continuation. A one-shot continuation is the separate law "resume at most once"; a read demand has no
bound at all.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Program

open ProgramRows ProgramTranslation

/-- The successors of a configuration of rows by one schema. -/
def schemaSuccessors (r : Schema) (W : List Sx) : List (List Sx) :=
  (pick (r.take ++ r.read) W []).map fun choice => output r choice.1 choice.2

/-- **The successor function of any well formed schema is exact.** -/
theorem fires_iff_schemaSuccessors {r : Schema} (wf : r.WellFormed) (W : List Sx) (W' : Multiset Sx) :
    r.Fires (W : Multiset Sx) W' ↔ ∃ l ∈ schemaSuccessors r W, W' = (l : Multiset Sx) := by
  constructor
  · rintro ⟨θ, F, hW, rfl⟩
    have split : (W : Multiset Sx) = (((r.take ++ r.read).map (Pat.inst θ) : List Sx) : Multiset Sx) + F := by
      rw [hW, push_eq, push_eq, List.map_append, ← Multiset.coe_add, add_assoc]
    obtain ⟨σ, rest, mem, agrees, same⟩ := pick_complete _ W F [] (fun _ _ h => by cases h) split
    obtain ⟨-, bound, -⟩ := pick_sound _ W [] σ rest mem
    refine ⟨output r σ rest, List.mem_map.mpr ⟨(σ, rest), mem, rfl⟩, ?_⟩
    have readSame : r.read.map (Pat.inst σ.get) = r.read.map (Pat.inst θ) :=
      List.map_congr_left fun p hp => inst_get_of_agrees agrees p fun x hx =>
        bound x ⟨p, List.mem_append_right _ hp, hx⟩
    have makeSame : r.make.map (Pat.inst σ.get) = r.make.map (Pat.inst θ) :=
      List.map_congr_left fun q hq => inst_get_of_agrees agrees q fun x hx => by
        obtain ⟨p, hp, hx'⟩ := wf.covered q hq x hx
        exact bound x ⟨p, hp, hx'⟩
    rw [output, readSame, makeSame, push_eq, push_eq, ← same, ← Multiset.coe_add, ← Multiset.coe_add,
      add_assoc]
  · rintro ⟨l, mem, rfl⟩
    obtain ⟨⟨σ, rest⟩, pickMem, rfl⟩ := List.mem_map.mp mem
    obtain ⟨-, -, split⟩ := pick_sound _ W [] σ rest pickMem
    refine ⟨σ.get, rest, ?_, ?_⟩
    · rw [split σ (Extends.refl σ), push_eq, push_eq, List.map_append, ← Multiset.coe_add, add_assoc]
    · rw [output, push_eq, push_eq, ← Multiset.coe_add, ← Multiset.coe_add, add_assoc]

/-- **A one-shot continuation**: the resumption takes the demand and the suspended continuation. -/
def oneShot : Schema := ⟨[p2 33 (.var 0) (.var 1), p2 32 (.var 0) (.var 2)], [], [p2 30 (.var 1) (.var 2)]⟩

theorem oneShot_wellFormed : oneShot.WellFormed := ⟨by decide, by decide⟩

/-- One suspended continuation and two demands of it. -/
def twoDemands : List Sx := [demand ku (atom ka), demand ku (atom kb), susp ku nil]

theorem oneShot_first :
    schemaSuccessors oneShot twoDemands = [[ret (atom ka) nil, demand ku (atom kb)],
      [ret (atom kb) nil, demand ku (atom ka)]] := by decide

theorem oneShot_then_none :
    schemaSuccessors oneShot [ret (atom ka) nil, demand ku (atom kb)] = [] ∧
      schemaSuccessors oneShot [ret (atom kb) nil, demand ku (atom ka)] = [] := by decide

/-- **A one-shot continuation resumes once in all**: from one suspended continuation and two demands,
its first resumption serves one demand, and then it cannot fire again; the other demand is never
served. -/
theorem oneShot_resumes_once {W' : Multiset Sx} (first : oneShot.Fires (twoDemands : Multiset Sx) W') :
    (W' = ([ret (atom ka) nil, demand ku (atom kb)] : Multiset Sx) ∨
        W' = ([ret (atom kb) nil, demand ku (atom ka)] : Multiset Sx)) ∧
      ∀ W'', ¬ oneShot.Fires W' W'' := by
  obtain ⟨l, mem, rfl⟩ := (fires_iff_schemaSuccessors oneShot_wellFormed twoDemands W').mp first
  rw [oneShot_first] at mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  obtain ⟨none₁, none₂⟩ := oneShot_then_none
  have stuck : ∀ (l : List Sx), schemaSuccessors oneShot l = [] → ∀ W'', ¬ oneShot.Fires (l : Multiset Sx) W'' :=
    fun l none W'' fires => by
      obtain ⟨l', mem', -⟩ := (fires_iff_schemaSuccessors oneShot_wellFormed l W'').mp fires
      rw [none] at mem'
      cases mem'
  rcases mem with rfl | rfl
  · exact ⟨.inl rfl, stuck _ none₁⟩
  · exact ⟨.inr rfl, stuck _ none₂⟩

#print axioms fires_iff_schemaSuccessors
#print axioms oneShot_wellFormed
#print axioms oneShot_first
#print axioms oneShot_then_none
#print axioms oneShot_resumes_once

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Program
