import Mathlib.Logic.Hydra
import Mathlib.Order.WellFounded
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Divergence.Systems

/-!
# Divergence preserved: an infinite run of the source gives an infinite run of the step

A configuration of the source is a bag of alternatives and a step moves one of them, so an infinite run
of the source need not move any one alternative for ever by its definition: `choice` makes two
alternatives and the run may move now one, now the other. It does (`arrow_alternative_diverges`),
because every move makes finitely many alternatives. The statement is proved first in the form that
needs no choice of the alternative.

* `acc_of_frontier`: **a system that is followed, one step at a time, by a frontier of states** (each
  step replaces one state of the frontier by finitely many of its successors) **terminates wherever
  every state of the frontier does**. It is the well-foundedness of the multiset extension of a
  well-founded relation (`Relation.CutExpand`, `Acc.cutExpand`).
* `arrow_source_terminates`, `source_terminates`: if the translated program has no infinite run from
  the start, the source has no infinite run from the query (the fragment with `let` for scoped programs
  and queries; the first fragment).
* `arrow_divergence_preserved`, `divergence_preserved`: **an infinite run of the source from the query
  gives an infinite run of the translated program from the start.**

With `Divergence.Systems.arrow_divergence_reflected` and `divergence_reflected`: the source diverges
from a query exactly when the translated program diverges from its start
(`arrow_diverges_iff`, `diverges_iff`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Divergence

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage

/-! ## Termination through frontiers -/

section Frontier

universe uC uS

variable {C : Type uC} {St : Type uS}

/-- An accessible element is not related to itself. -/
theorem acc_irrefl {r : St → St → Prop} {x : St} (acc : Acc r x) : ¬ r x x := by
  induction acc with
  | intro x _ ih => exact fun loop => ih x loop loop

/-- **Termination through frontiers.** `step` is followed by frontiers when every step from a system
state with frontier `M` replaces one state `x` of `M` by a bag `new` of states each related to `x` by
`r` (read `r y x` as: `y` is a successor of `x`). Then a system state whose frontier consists of
accessible states is accessible. -/
theorem acc_of_frontier {step : C → C → Prop} {r : St → St → Prop} {Inv : C → Multiset St → Prop}
    (move : ∀ {c c' : C} {M : Multiset St}, Inv c M → step c c' →
      ∃ x rest new, M = x ::ₘ rest ∧ (∀ y ∈ new, r y x) ∧ Inv c' (new + rest))
    {c : C} {M : Multiset St} (inv : Inv c M) (acc : ∀ s ∈ M, Acc r s) :
    Acc (fun c' c => step c c') c := by
  let ra : St → St → Prop := fun y x => r y x ∧ Acc r x
  have : Std.Irrefl ra := ⟨fun x loop => acc_irrefl loop.2 loop.1⟩
  have sub : Subrelation ra r := fun related => related.1
  have accM : Acc (Relation.CutExpand ra) M :=
    Relation.acc_of_singleton fun s member => (sub.accessible (acc s member)).cutExpand
  induction accM generalizing c with
  | intro M _ ih =>
      refine Acc.intro c fun c' taken => ?_
      obtain ⟨x, rest, new, split, successors, inv'⟩ := move inv taken
      have accX : Acc r x := acc x (by rw [split]; exact Multiset.mem_cons_self _ _)
      refine ih (new + rest) ⟨new, x, fun y member => ⟨successors y member, accX⟩, ?_⟩ inv' ?_
      · rw [split, ← Multiset.singleton_add, add_comm (new + rest) {x}, add_comm new rest, ← add_assoc]
      · intro s member
        rcases Multiset.mem_add.mp member with inNew | inRest
        · exact accX.inv (successors s inNew)
        · exact acc s (by rw [split]; exact Multiset.mem_cons_of_mem inRest)

end Frontier

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} (N : Nodes S Γ star) {κ : Keys S}
  {D : Discipline S Γ star} {P : SourceLanguage.Program κ Γ star D.Ty} {supply : ℕ → Term S Γ star}
  (spaces : Term S Γ star → Multiset (Row κ Γ star)) (q : Comp κ Γ star D.Ty)

/-! ## The fragment with `let` -/

/-- **If the translated program terminates from the start, the source terminates from the query**
(the fragment with `let`, scoped programs and queries). -/
theorem arrow_source_terminates
    (equations : ∀ e ∈ P.equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs)
    {qsite : κ.Site} (qScoped : q.Scoped [qsite]) (qDistinct : (qsite :: q.sites).Nodup)
    (arrowQ : ArrowComp q) (terminates : Acc (fun s' s => Fires N P s s') (start N P q)) :
    Acc (fun C' C => SourceLanguage.Step D P supply C C') (Config.initial spaces q) := by
  classical
  refine acc_of_frontier (r := fun s' s => Fires N P s s')
    (Inv := fun (C : Config κ Γ star D.Ty) (M : Multiset (HostState S)) =>
      Runs D P supply (Config.initial spaces q) C ∧
        ∃ L : Multiset (Branch κ Γ star D.Ty × HostState S × ℕ), ArrowFrontier N P C L ∧
          M = L.map fun x => x.2.1)
    ?_ (M := {start N P q}) ?_ ?_
  · rintro C C' M ⟨runs, L, frontier, rfl⟩ step
    obtain ⟨L', frontier', x, rest, new, split, rfl, fires⟩ :=
      arrowFrontier_step N (fun e member => (equations e member).2.2) frontier
        (reachableHygienic_of_scoped spaces q equations qScoped qDistinct arrowQ C runs) step
    refine ⟨x.2.1, rest.map (fun x => x.2.1), new.map (fun x => x.2.1), ?_, ?_, runs.tail step, _, frontier', ?_⟩
    · rw [split, Multiset.map_cons]
    · intro y member
      obtain ⟨z, inside, rfl⟩ := Multiset.mem_map.mp member
      exact fires z inside
    · rw [Multiset.map_add]
  · exact ⟨.refl, _, arrowFrontier_initial N spaces q arrowQ (query_unopened qScoped qDistinct arrowQ), rfl⟩
  · intro s member
    rw [Multiset.mem_singleton.mp member]
    exact terminates

/-- **Divergence is preserved** (the fragment with `let`): an infinite run of the source from a scoped
query gives an infinite run of the translated program from the start. -/
theorem arrow_divergence_preserved
    (equations : ∀ e ∈ P.equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs)
    {qsite : κ.Site} (qScoped : q.Scoped [qsite]) (qDistinct : (qsite :: q.sites).Nodup)
    (arrowQ : ArrowComp q) (run : ℕ → Config κ Γ star D.Ty) (first : run 0 = Config.initial spaces q)
    (steps : ∀ k, SourceLanguage.Step D P supply (run k) (run (k + 1))) :
    ∃ f : ℕ → HostState S, f 0 = start N P q ∧ ∀ k, Fires N P (f k) (f (k + 1)) := by
  have diverges : ¬ Acc (fun C' C => SourceLanguage.Step D P supply C C') (Config.initial spaces q) :=
    not_acc_iff_exists_descending_chain.mpr ⟨run, first, steps⟩
  exact not_acc_iff_exists_descending_chain.mp fun terminates =>
    diverges (arrow_source_terminates N spaces q equations qScoped qDistinct arrowQ terminates)

/-! ## The first fragment -/

/-- **If the translated program terminates from the start, the source terminates from the query**
(the first fragment). -/
theorem source_terminates (plainP : PlainProgram P) (plainQ : PlainComp q)
    (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = [])
    (terminates : Acc (fun s' s => Fires N P s s') (start N P q)) :
    Acc (fun C' C => SourceLanguage.Step D P supply C C') (Config.initial spaces q) := by
  classical
  refine acc_of_frontier (r := fun s' s => Fires N P s s')
    (Inv := fun (C : Config κ Γ star D.Ty) (M : Multiset (HostState S)) =>
      ∃ L : Multiset (Branch κ Γ star D.Ty × HostState S × ℕ), Frontier N P C L ∧ M = L.map fun x => x.2.1)
    ?_ (M := {start N P q}) ?_ ?_
  · rintro C C' M ⟨L, frontier, rfl⟩ step
    obtain ⟨L', frontier', x, rest, new, split, rfl, fires⟩ := frontier_step N plainP frontier step
    refine ⟨x.2.1, rest.map (fun x => x.2.1), new.map (fun x => x.2.1), ?_, ?_, _, frontier', ?_⟩
    · rw [split, Multiset.map_cons]
    · intro y member
      obtain ⟨z, inside, rfl⟩ := Multiset.mem_map.mp member
      exact fires z inside
    · rw [Multiset.map_add]
  · exact ⟨_, frontier_initial N spaces q plainQ unopened, rfl⟩
  · intro s member
    rw [Multiset.mem_singleton.mp member]
    exact terminates

/-- **Divergence is preserved** (the first fragment): an infinite run of the source from a query whose
names are unopened gives an infinite run of the translated program from the start. -/
theorem divergence_preserved (plainP : PlainProgram P) (plainQ : PlainComp q)
    (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = []) (run : ℕ → Config κ Γ star D.Ty)
    (first : run 0 = Config.initial spaces q)
    (steps : ∀ k, SourceLanguage.Step D P supply (run k) (run (k + 1))) :
    ∃ f : ℕ → HostState S, f 0 = start N P q ∧ ∀ k, Fires N P (f k) (f (k + 1)) := by
  have diverges : ¬ Acc (fun C' C => SourceLanguage.Step D P supply C C') (Config.initial spaces q) :=
    not_acc_iff_exists_descending_chain.mpr ⟨run, first, steps⟩
  exact not_acc_iff_exists_descending_chain.mp fun terminates =>
    diverges (source_terminates N spaces q plainP plainQ unopened terminates)

include N in
/-- **An infinite run of the source moves some alternative for ever**: from an infinite run of the
source from a scoped query there is an alternative, starting at the query's, that moves infinitely
often, each move to a live alternative that it makes. This is König's lemma for the source's runs; the
proof goes through the step (an infinite run of the translated program is one alternative's moves),
which is why it takes nodes. -/
theorem arrow_alternative_diverges
    (equations : ∀ e ∈ P.equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs)
    {qsite : κ.Site} (qScoped : q.Scoped [qsite]) (qDistinct : (qsite :: q.sites).Nodup)
    (arrowQ : ArrowComp q) (run : ℕ → Config κ Γ star D.Ty) (first : run 0 = Config.initial spaces q)
    (steps : ∀ k, SourceLanguage.Step D P supply (run k) (run (k + 1))) :
    ∃ moves : ℕ → World κ Γ star × Branch κ Γ star D.Ty, moves 0 = (⟨0, 0, spaces⟩, initialBranch q) ∧
      ∀ k, (alternativeSystem D P supply).Step (moves k) (moves (k + 1)) := by
  obtain ⟨f, start, fires⟩ :=
    arrow_divergence_preserved N spaces q equations qScoped qDistinct arrowQ run first steps
  exact alternative_divergence_reflected N equations
    (start_representsAlternative N spaces q qScoped qDistinct arrowQ) f start fires

/-! ## Both ways -/

/-- **The source diverges from a scoped query exactly when the translated program diverges from its
start** (the fragment with `let`). -/
theorem arrow_diverges_iff
    (equations : ∀ e ∈ P.equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs)
    {qsite : κ.Site} (qScoped : q.Scoped [qsite]) (qDistinct : (qsite :: q.sites).Nodup)
    (arrowQ : ArrowComp q) :
    (∃ run : ℕ → Config κ Γ star D.Ty, run 0 = Config.initial spaces q ∧
      ∀ k, SourceLanguage.Step D P supply (run k) (run (k + 1))) ↔
      ∃ f : ℕ → HostState S, f 0 = start N P q ∧ ∀ k, Fires N P (f k) (f (k + 1)) :=
  ⟨fun ⟨run, first, steps⟩ =>
      arrow_divergence_preserved N spaces q equations qScoped qDistinct arrowQ run first steps,
    fun ⟨f, first, fires⟩ =>
      arrow_divergence_reflected N spaces q equations qScoped qDistinct arrowQ f first fires⟩

/-- **The source diverges from a query exactly when the translated program diverges from its start**
(the first fragment, queries whose names are unopened). -/
theorem diverges_iff (plainP : PlainProgram P) (plainQ : PlainComp q)
    (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = []) :
    (∃ run : ℕ → Config κ Γ star D.Ty, run 0 = Config.initial spaces q ∧
      ∀ k, SourceLanguage.Step D P supply (run k) (run (k + 1))) ↔
      ∃ f : ℕ → HostState S, f 0 = start N P q ∧ ∀ k, Fires N P (f k) (f (k + 1)) :=
  ⟨fun ⟨run, first, steps⟩ => divergence_preserved N spaces q plainP plainQ unopened run first steps,
    fun ⟨f, first, fires⟩ => divergence_reflected N spaces q plainP plainQ unopened f first fires⟩

#print axioms arrow_alternative_diverges
#print axioms arrow_diverges_iff
#print axioms diverges_iff
#print axioms acc_of_frontier
#print axioms arrow_source_terminates
#print axioms arrow_divergence_preserved
#print axioms source_terminates
#print axioms divergence_preserved

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Divergence
