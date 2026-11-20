import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.ArrowRuns

/-!
# Where hygiene fails on a run, the run theorem's conclusion fails

`arrow_runs_forward_of_hygienic` asks `ArrowProgram`, `ArrowComp`, unopened query names, and
`ReachableHygienic`. The query

`let x = one in (let x = two in x)` (both arrows at the site `[9]`, the empty program)

satisfies the first three (`arrowQ`, `arrowP`, `shadowQ_unopened`); it is not well formed (two binders
share a site), and the last hypothesis fails on it.

* A source run reaches an alternative that is not hygienic (`not_hygienic`), and goes on to a live
  alternative `B6` that answers `two` (`runs6`, `B6_live`).
* Every state that runs of the translated program reach from the start represents one of the six
  alternatives before the second bind (`reached_inv`), and the last of them has no firing at all
  (`B5_stuck`: the rule's bind tells `x = two` into a knowledge with `x = one`).
* So **no frontier of the configuration holding `B6` is reached by the step** (`no_frontier`): the
  conclusion of `arrow_runs_forward_of_hygienic` fails, and the hypothesis is needed for whole runs,
  not only for one bind (`hygiene_needed`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Controls.ShadowRun

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open SourceLanguage SourceLanguage.Elaboration SourceLanguage.Toolkit
open Hosting
open Classical

/-- The trivial discipline, with its type language on the nose. -/
abbrev D : Discipline MSig [] () := ⟨MTy, fun _ _ => True⟩
abbrev N := mettaNodes

def supply : ℕ → MClosed := fun _ => csym "space"
abbrev sp : MClosed → Multiset (Row mkeys [] ()) := fun _ => 0

/-- No equations. -/
def P0 : SourceLanguage.Program mkeys [] () MTy := ⟨[], fun t => .apply t⟩

abbrev x9 : MData := foD [] [9] 0
abbrev x0 : MData := foD [0] [9] 0
abbrev x10 : MData := foD [1, 0] [9] 0
def oneT : MData := sym "one"
def twoT : MData := sym "two"

abbrev k1 : Comp mkeys [] () MTy := .let_ [9] x9 (.ret twoT) (.ret x9)
/-- `let x = one in (let x = two in x)`, both arrows at the site `[9]`. -/
def shadowQ : Comp mkeys [] () MTy := .let_ [9] x9 (.ret oneT) k1

abbrev B0 : Branch mkeys [] () MTy := ⟨[], .eval (.let_ [9] x9 (.ret oneT) k1), [], []⟩
abbrev B1 : Branch mkeys [] () MTy := ⟨[], .eval (.ret oneT), [.bindTo [9] x9 k1], []⟩
abbrev B2 : Branch mkeys [] () MTy := ⟨[], .value oneT, [.bindTo [9] x9 k1], []⟩
abbrev B3 : Branch mkeys [] () MTy := ⟨[(x0, oneT)], .eval (.let_ [9] x0 (.ret twoT) (.ret x0)), [], []⟩
abbrev B4 : Branch mkeys [] () MTy := ⟨[(x0, oneT)], .eval (.ret twoT), [.bindTo [9] x0 (.ret x0)], []⟩
abbrev B5 : Branch mkeys [] () MTy := ⟨[(x0, oneT)], .value twoT, [.bindTo [9] x0 (.ret x0)], []⟩
abbrev B6 : Branch mkeys [] () MTy := ⟨[(x0, oneT), (x10, twoT)], .eval (.ret x10), [], []⟩

theorem arrowQ : ArrowComp shadowQ := ⟨trivial, trivial, trivial⟩

theorem arrowP : ArrowProgram P0 := fun _ member => by cases member

theorem shadowQ_unopened : ∀ t ∈ shadowQ.data, ∀ x ∈ support t, x.scopes = [] := by
  have hx : NamesIn [[9]] x9 := by decide
  have h1 : NamesIn [[9]] oneT := by decide
  have h2 : NamesIn [[9]] twoT := by decide
  intro t member x inside
  simp only [shadowQ, Comp.data, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact (hx x inside).1
  · exact (h1 x inside).1
  · exact (hx x inside).1
  · exact (h2 x inside).1
  · exact (hx x inside).1

/-- The query is not well formed: its two binders share a site. -/
theorem shadowQ_sites_shared : ¬ ([3] :: shadowQ.sites).Nodup := by decide

/-! ## The source run -/

def live6σ : Assignment (fam mkeys) noNames :=
  closeNames [(([0], [9], 0), csym "one"), (([1, 0], [9], 0), csym "two")] (csym "a")

theorem B3_live : Solvable B3.store :=
  ⟨Empty, noNames, live6σ, fun c member => by
    simp only [List.mem_singleton] at member
    subst member
    rfl⟩

theorem B6_live : Solvable B6.store :=
  ⟨Empty, noNames, live6σ, fun c member => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl⟩

def C5 : Config mkeys [] () MTy := ⟨⟨1, 0, sp⟩, {B5}⟩
def C6 : Config mkeys [] () MTy := ⟨⟨2, 0, sp⟩, {B6}⟩

theorem runs5 : Runs D P0 supply (Config.initial sp shadowQ) C5 := by
  refine Relation.ReflTransGen.tail (b := ⟨⟨1, 0, sp⟩, {B4}⟩) ?_ (step_one B3_live (.ret _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨1, 0, sp⟩, {B3}⟩) ?_ (step_one B3_live (.letStart _ _ _ _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨0, 0, sp⟩, {B2}⟩) ?_ (step_one live_nil (.letBind _ _ _ _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨0, 0, sp⟩, {B1}⟩) ?_ (step_one live_nil (.ret _ _ _ _ _))
  exact Relation.ReflTransGen.single (step_one live_nil (.letStart _ _ _ _ _ _ _ _))

theorem runs6 : Runs D P0 supply (Config.initial sp shadowQ) C6 :=
  runs5.tail (step_one B3_live (.letBind _ _ _ _ _ _ _ _))

/-- The alternative `B5` is not hygienic: its store binds the frame's own name. -/
theorem B5_not_private :
    ¬ FramePrivate [9] x0 (.ret x0) [(x0, oneT)] twoT ([] : List (SourceLanguage.Frame mkeys [] () MTy)) := by
  intro private'
  let σa : Assignment (fam mkeys) noNames := closeNames [] (csym "two")
  let σb : Assignment (fam mkeys) noNames := closeNames [(([0], [9], 0), csym "one")] (csym "two")
  obtain ⟨onStore, _, _⟩ := private' σa σb (by
    intro y notOwn
    rcases y with ⟨scopes, ⟨site, index, ⟨Δ, u⟩⟩⟩
    cases u
    cases Δ with
    | cons _ _ => rfl
    | nil =>
        by_cases hit : scopes = [0] ∧ site = [9] ∧ index = 0
        · obtain ⟨rfl, rfl, rfl⟩ := hit
          exact absurd ⟨rfl, .inl (by decide)⟩ notOwn
        · simp only [σa, σb, closeNames, List.lookup]
          split
          · rename_i heq
            simp only [beq_iff_eq, Prod.mk.injEq] at heq
            exact absurd heq hit
          · rfl)
  have := (onStore _ (List.mem_singleton_self _)).1
  change Rigid.includeTerm noNames (csym "two") = Rigid.includeTerm noNames (csym "one") at this
  have := Rigid.include_injective _ _ _ this
  simp [csym] at this

/-- **`ReachableHygienic` fails for this query.** -/
theorem not_hygienic : ¬ ReachableHygienic (D := D) sp shadowQ P0 supply := by
  intro hygiene
  exact B5_not_private (hygiene C5 runs5 B5 (Multiset.mem_singleton_self _) _ _ _ _ _ _ _ rfl)

/-! ## The moves before the second bind -/

section Moves

variable {w w' : World mkeys [] ()} {b : Branch mkeys [] () D.Ty} {bs : Multiset (Branch mkeys [] () D.Ty)}

theorem move_B0 (move : Move D P0 supply w b w' bs) (hb : b = B0) : w' = w ∧ ∀ b' ∈ bs, b' = B1 := by
  cases move <;> cases hb
  exact ⟨rfl, fun b' made => Multiset.mem_singleton.mp made⟩

theorem move_B1 (move : Move D P0 supply w b w' bs) (hb : b = B1) : w' = w ∧ ∀ b' ∈ bs, b' = B2 := by
  cases move <;> cases hb
  exact ⟨rfl, fun b' made => Multiset.mem_singleton.mp made⟩

theorem move_B2 (move : Move D P0 supply w b w' bs) (hb : b = B2) (zero : w.scope = 0) :
    w'.scope = 1 ∧ ∀ b' ∈ bs, b' = B3 := by
  cases move <;> cases hb
  refine ⟨by simp [World.fresh, zero], fun b' made => ?_⟩
  rw [Multiset.mem_singleton.mp made, zero]
  rfl

theorem move_B3 (move : Move D P0 supply w b w' bs) (hb : b = B3) : w' = w ∧ ∀ b' ∈ bs, b' = B4 := by
  cases move <;> cases hb
  exact ⟨rfl, fun b' made => Multiset.mem_singleton.mp made⟩

theorem move_B4 (move : Move D P0 supply w b w' bs) (hb : b = B4) : w' = w ∧ ∀ b' ∈ bs, b' = B5 := by
  cases move <;> cases hb
  exact ⟨rfl, fun b' made => Multiset.mem_singleton.mp made⟩

end Moves

/-! ## The step stops at `B5` -/

/-- **No firing at `B5`.** -/
theorem B5_stuck {s s' : HostState MSig} {n a : ℕ} (rep : Represents N P0 n B5 s a) : ¬ Fires N P0 s s' := by
  rintro ⟨⟨rule, member, ext, opening, selection, seen⟩, admitted, _⟩
  rcases (mem_translate N).mp member with control | ⟨e, eMember, _⟩
  · rcases (mem_controlRules N).mp control with rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨_, _, _, B, h, reads, _⟩ := admitted_takes_alternative N rep admitted rfl rfl rfl
        (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
      obtain ⟨t, focus⟩ := shape_ret N reads
      cases focus
    · obtain ⟨_, _, _, B, h, reads, _⟩ := admitted_takes_alternative N rep admitted rfl rfl rfl
        (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
      change branchReads N _ B (observe (instantiate h _)) at reads
      rw [instantiate_altN, instantiate_evalN, instantiate_applyN] at reads
      obtain ⟨t, _, focus, _⟩ := shape_apply N reads
      cases focus
    · obtain ⟨_, _, _, B, h, reads, _⟩ := admitted_takes_alternative N rep admitted rfl rfl rfl
        (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
      obtain ⟨c, d, focus⟩ := shape_choice N reads
      cases focus
    · obtain ⟨_, _, _, B, h, reads, _⟩ := admitted_takes_alternative N rep admitted rfl rfl rfl
        (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
      obtain ⟨c, d, focus⟩ := shape_choice N reads
      cases focus
    · obtain ⟨_, _, _, B, h, reads, _⟩ := admitted_takes_alternative N rep admitted rfl rfl rfl
        (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
      obtain ⟨_, _, _, _, focus⟩ := shape_bindStart N reads
      cases focus
    · obtain ⟨_, _, _, B, h, reads, told⟩ := admitted_takes_alternative N rep admitted rfl rfl rfl
        (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
      obtain ⟨σ, solved, matched, _⟩ := (bindValue_rule_side N (K := [(x0, oneT)]) (v := twoT) (s := [9])
        (p := x0) (k := .ret x0) (fs := []) (ps := []) _).mp ⟨h, reads, told, rfl⟩
      have bound := solved _ (List.mem_singleton_self _)
      change instantiate σ x0 = instantiate σ (sym "one") at bound
      change instantiate σ x0 = instantiate σ (sym "two") at matched
      have same := bound.symm.trans matched
      change (Term.op (Sum.inl (MOp.sym "one")) .nil : Term (signature MSig B.arity) [] ()) =
        Term.op (Sum.inl (MOp.sym "two")) .nil at same
      simp at same
  · cases eMember

/-! ## Every reached state represents one of `B0`, …, `B5` -/

def Inv (s : HostState MSig) : Prop :=
  ∃ a, Represents N P0 0 B0 s a ∨ Represents N P0 0 B1 s a ∨ Represents N P0 0 B2 s a ∨
    Represents N P0 1 B3 s a ∨ Represents N P0 1 B4 s a ∨ Represents N P0 1 B5 s a

theorem private2 : FramePrivate [9] x9 k1 [] oneT ([] : List (SourceLanguage.Frame mkeys [] () MTy)) := by
  intro W target σ σ' _
  refine ⟨?_, rfl, ?_⟩
  · intro e member
    cases member
  · intro fr member
    cases member

theorem hyg_eval {K : List (Constraint mkeys [] ())} {c : Comp mkeys [] () MTy} {fs : List (SourceLanguage.Frame mkeys [] () MTy)} :
    Hygienic (⟨K, .eval c, fs, []⟩ : Branch mkeys [] () MTy) := by
  intro K' v s p k fs' ps same
  cases same

theorem inv_step {s s' : HostState MSig} (inv : Inv s) (fires : Fires N P0 s s') : Inv s' := by
  obtain ⟨a, rep | rep | rep | rep | rep | rep⟩ := inv
  · obtain ⟨w', bs, b', a', move, child, rep', _⟩ := reflection_arrows N (D := D) (supply := supply) (w :=⟨0, 0, sp⟩)
      arrowP rep ⟨trivial, .inl ⟨_, rfl, arrowQ⟩⟩ hyg_eval fires
    obtain ⟨hw, hb⟩ := move_B0 move rfl
    rw [hb b' child, hw] at rep'
    exact ⟨a', .inr (.inl rep')⟩
  · obtain ⟨w', bs, b', a', move, child, rep', _⟩ := reflection_arrows N (D := D) (supply := supply) (w :=⟨0, 0, sp⟩)
      arrowP rep ⟨⟨⟨trivial, trivial⟩, trivial⟩, .inl ⟨_, rfl, trivial⟩⟩ hyg_eval fires
    obtain ⟨hw, hb⟩ := move_B1 move rfl
    rw [hb b' child, hw] at rep'
    exact ⟨a', .inr (.inr (.inl rep'))⟩
  · obtain ⟨w', bs, b', a', move, child, rep', _⟩ := reflection_arrows N (D := D) (supply := supply) (w :=⟨0, 0, sp⟩)
      arrowP rep ⟨⟨⟨trivial, trivial⟩, trivial⟩, .inr ⟨_, rfl⟩⟩
      (fun K v s p k fs ps same => by cases same; exact private2) fires
    obtain ⟨hw, hb⟩ := move_B2 move rfl rfl
    rw [hb b' child, hw] at rep'
    exact ⟨a', .inr (.inr (.inr (.inl rep')))⟩
  · obtain ⟨w', bs, b', a', move, child, rep', _⟩ := reflection_arrows N (D := D) (supply := supply) (w :=⟨1, 0, sp⟩)
      arrowP rep ⟨trivial, .inl ⟨_, rfl, ⟨trivial, trivial⟩⟩⟩ hyg_eval fires
    obtain ⟨hw, hb⟩ := move_B3 move rfl
    rw [hb b' child, hw] at rep'
    exact ⟨a', .inr (.inr (.inr (.inr (.inl rep'))))⟩
  · obtain ⟨w', bs, b', a', move, child, rep', _⟩ := reflection_arrows N (D := D) (supply := supply) (w :=⟨1, 0, sp⟩)
      arrowP rep ⟨⟨trivial, trivial⟩, .inl ⟨_, rfl, trivial⟩⟩ hyg_eval fires
    obtain ⟨hw, hb⟩ := move_B4 move rfl
    rw [hb b' child, hw] at rep'
    exact ⟨a', .inr (.inr (.inr (.inr (.inr rep'))))⟩
  · exact absurd fires (B5_stuck rep)

/-- **Every state reached by the step represents one of `B0`, …, `B5`.** -/
theorem reached_inv {s : HostState MSig} (run : Relation.ReflTransGen (Fires N P0) (Hosting.start N P0 shadowQ) s) :
    Inv s := by
  induction run with
  | refl => exact ⟨_, .inl (start_represents N P0 shadowQ shadowQ_unopened)⟩
  | tail _ fires ih => exact inv_step ih fires

/-! ## No reached state represents `B6` -/

abbrev BE : Interface.Frames.Frame MSig := ⟨Empty, noNames⟩

def r6 : Observation MSig BE.arity := observe (altN N (evalN N (retN N (symAt "two"))) (emptyN N))

theorem B6_reads : branchReads N B6 BE r6 :=
  ⟨live6σ, fun c member => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl, rfl⟩

/-- The two components of an alternative's row. -/
theorem split_reads {b : Branch mkeys [] () MTy} (reads : branchReads N b BE r6) :
    ∃ σ : Assignment (fam mkeys) BE.arity,
      encFocus N (instantiate σ) b.focus = evalN N (retN N (symAt "two")) ∧
      encStack N (instantiate σ) b.frames = emptyN N := by
  obtain ⟨σ, _, same⟩ := reads
  have whole := observe_injective same
  rw [encBranch, encAlt] at whole
  exact ⟨σ, vec2_inj (N.args_eq whole)⟩

theorem others_not_r6 {b : Branch mkeys [] () MTy}
    (which : b = B0 ∨ b = B1 ∨ b = B2 ∨ b = B3 ∨ b = B4 ∨ b = B5) : ¬ branchReads N b BE r6 := by
  intro reads
  obtain ⟨σ, onFocus, onStack⟩ := split_reads reads
  rcases which with rfl | rfl | rfl | rfl | rfl | rfl
  · have inner := vec1_inj (N.args_eq onFocus)
    exact absurd (N.tag_eq inner) (by decide)
  · exact absurd (N.tag_eq onStack) (by decide)
  · exact absurd (N.tag_eq onFocus) (by decide)
  · have inner := vec1_inj (N.args_eq onFocus)
    exact absurd (N.tag_eq inner) (by decide)
  · exact absurd (N.tag_eq onStack) (by decide)
  · exact absurd (N.tag_eq onFocus) (by decide)

theorem present_single {n m : ℕ} {b b' : Branch mkeys [] () MTy} {s : HostState MSig} {a a' : ℕ}
    (rep : Represents N P0 n b s a) (rep' : Represents N P0 m b' s a') : a = a' := by
  have one := rep.present
  have two := rep'.present
  rw [one] at two
  simpa [P0] using two

/-- **No state reached by the step represents `B6`**, so the configuration `C6` that the source reaches
has no frontier of reached states: the conclusion of the hygienic run theorem fails where its last
hypothesis does. -/
theorem no_frontier :
    Runs D P0 supply (Config.initial sp shadowQ) C6 ∧ ¬ ReachableHygienic (D := D) sp shadowQ P0 supply ∧
      ¬ ∃ L, ArrowFrontier (D := D) N P0 C6 L ∧
        ∀ x ∈ L, Relation.ReflTransGen (Fires N P0) (Hosting.start N P0 shadowQ) x.2.1 := by
  refine ⟨runs6, not_hygienic, ?_⟩
  rintro ⟨L, frontier, reached⟩
  have inside : B6 ∈ L.map Prod.fst := by
    rw [frontier.branches]
    exact Multiset.mem_filter.mpr ⟨Multiset.mem_singleton_self _, B6_live⟩
  obtain ⟨x, xMember, same⟩ := Multiset.mem_map.mp inside
  obtain ⟨rep6, _⟩ := frontier.represents x xMember
  rw [same] at rep6
  rcases reached_inv (reached x xMember) with ⟨a, rep | rep | rep | rep | rep | rep⟩
  all_goals
    have index := present_single rep rep6
    subst index
    have fromState := (rep6.reads BE r6).mpr B6_reads
    have toBranch := (rep.reads BE r6).mp fromState
    exact others_not_r6 (by simp) toBranch

#print axioms shadowQ_sites_shared
#print axioms runs6
#print axioms not_hygienic
#print axioms B5_stuck
#print axioms reached_inv
#print axioms no_frontier

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Controls.ShadowRun
