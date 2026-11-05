import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.CorrectedCongruence
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.CorrectedControls
import Mettapedia.OSLF.MeTTaIL.PatternCode

/-!
# REFL quotes the canonical representative of its reduct

Under the bag laws a reduct is determined only up to the order of its
parallel components, and REFL quotes a process. If REFL quotes whichever
representative the derivation produced, one class of reducts yields
listeners that are not equivalent, and a partner can tell them apart
(`BagControls.reflects_both`, `BagControls.listeners_differ`,
`BagControls.partner_tells_listeners_apart`): the order of a bag would be
observable through reflection.

A name is a quoted process, and names are compared modulo the structural
equivalence of the processes they quote. Here REFL quotes the canonical
representative of the reduct's class: its closed components, sorted by an
injective structural code, with their multiplicities (`canonicalBag`). Then

* the listener depends only on the class of the reduct
  (`canonicalBag_eq_of_bagEq`, `reflect_listener_canonical`), and equivalent
  reflected processes reach the same listeners (`reflect_respects_bagEq`);
* the executable step with canonical reflection is sound for the rules
  (`cstepCanon_sound_uniform`) and, on the closing fragment, complete for the
  whole relational semantics modulo the bag laws, REFL included
  (`cstepCanon_complete`);
* the two representatives of the control reach one listener
  (`canonical_reflection_one_listener`), while the representative-dependent
  reading reaches two (`representative_reflection_two_listeners`).

The canonical order is exact for ground names. A pattern that quotes a bag
with variables is compared by unification as written, and its canonical
order can change under instantiation: comparing such patterns modulo the bag
laws needs unification modulo associativity and commutativity, which has
complete sets of unifiers rather than one principal unifier. That admission
is not part of this module.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Corrected

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MeTTaOperationsComm (psubst pvars)
open Mettapedia.OSLF.MeTTaIL.PatternCode (patternCode patternCode_injective)

/-! ## The canonical representative of a class -/

/-- Order by the injective structural code. -/
def codeLe (a b : Pattern) : Prop := patternCode a ≤ patternCode b

instance : DecidableRel codeLe := fun a b => inferInstanceAs (Decidable (patternCode a ≤ patternCode b))
instance : Std.Total codeLe := ⟨fun a b => Nat.le_total (patternCode a) (patternCode b)⟩
instance : IsTrans Pattern codeLe := ⟨fun _ _ _ => Nat.le_trans⟩
instance : Std.Antisymm codeLe := ⟨fun _ _ first second => patternCode_injective (Nat.le_antisymm first second)⟩

/-- Sort by the structural code; equal patterns stay, as many as there are. -/
def codeOrder (l : List Pattern) : List Pattern := l.insertionSort codeLe

theorem codeOrder_perm (l : List Pattern) : (codeOrder l).Perm l := List.perm_insertionSort codeLe l

theorem codeOrder_eq_of_perm {l l' : List Pattern} (perm : l.Perm l') : codeOrder l = codeOrder l' :=
  List.Perm.eq_of_pairwise' (List.pairwise_insertionSort codeLe l) (List.pairwise_insertionSort codeLe l')
    ((codeOrder_perm l).trans (perm.trans (codeOrder_perm l').symm))

/-- **The canonical representative** of a process modulo the bag laws: its
closed components, sorted, with their multiplicities. -/
def canonicalBag (p : Pattern) : Pattern := pPar (codeOrder (components (close p)))

theorem components_canonicalBag (p : Pattern) :
    components (close (canonicalBag p)) = codeOrder (components (close p)) := by
  have members : ∀ c ∈ codeOrder (components (close p)), c ∈ components (close p) :=
    fun c member => (codeOrder_perm _).subset member
  have closed : (codeOrder (components (close p))).map close = codeOrder (components (close p)) := by
    conv_rhs => rw [← List.map_id (codeOrder _)]
    exact List.map_congr_left fun c member => close_of_mem_closed_components (members c member)
  have closeBag : close (canonicalBag p) = pPar ((codeOrder (components (close p))).map close) := by
    simp [canonicalBag, close, pPar, closeIn, closeList_eq_map]
  rw [closeBag, closed]
  exact components_pPar_leaves _ fun c member => leaf_of_mem_closed_components (members c member)

theorem canonicalBag_bagEq (p : Pattern) : BagEq (canonicalBag p) p := by
  unfold BagEq
  rw [components_canonicalBag]
  exact codeOrder_perm _

theorem canonicalBag_eq_of_bagEq {p q : Pattern} (same : BagEq p q) : canonicalBag p = canonicalBag q := by
  unfold canonicalBag
  rw [codeOrder_eq_of_perm same]

/-- Two processes are equal modulo the bag laws exactly when they have the
same canonical representative. -/
theorem bagEq_iff_canonicalBag_eq (p q : Pattern) : BagEq p q ↔ canonicalBag p = canonicalBag q :=
  ⟨canonicalBag_eq_of_bagEq, fun same =>
    (canonicalBag_bagEq p).symm.trans (by rw [same]; exact canonicalBag_bagEq q)⟩

/-! ## The relational semantics with canonical reflection -/

/-- The listener REFL emits for a reduct: it quotes the canonical representative. -/
def listener (x target : Pattern) : Pattern := pFor (tProc (canonicalBag target)) x pZero

/-- The manuscript's rules modulo the bag laws, with REFL quoting the
canonical representative of its reduct. -/
inductive CanonicalBagStep (admit : Admission) : Pattern → Pattern → Prop where
  | comm (t u x A B : Pattern) (bs : Bindings) (principal : Principal t u bs)
      (admitted : admit t A u B bs) :
      CanonicalBagStep admit (par (pFor t x A) (pFor u x B)) (par (applyDot bs A) (applyDot bs B))
  | parallel {source target : Pattern} (surrounding : Pattern) :
      CanonicalBagStep admit source target →
      CanonicalBagStep admit (par source surrounding) (par target surrounding)
  | congruence {source source' target' target : Pattern} :
      BagEq source source' → CanonicalBagStep admit source' target' → BagEq target' target →
      CanonicalBagStep admit source target
  | reflect (x : Pattern) {source target : Pattern} :
      CanonicalBagStep admit source target →
      CanonicalBagStep admit (pReflect x source) (listener x target)

theorem CanonicalBagStep.mono {admit admit' : Admission}
    (weaker : ∀ t A u B bs, admit t A u B bs → admit' t A u B bs) {p q : Pattern}
    (step : CanonicalBagStep admit p q) : CanonicalBagStep admit' p q := by
  induction step with
  | comm t u x A B bs principal admitted => exact .comm t u x A B bs principal (weaker _ _ _ _ _ admitted)
  | parallel surrounding _ ih => exact .parallel surrounding ih
  | congruence before _ after ih => exact .congruence before ih after
  | reflect x _ ih => exact .reflect x ih

/-- COMM at any position is a step with canonical reflection. -/
theorem BagCommStep.toCanonicalBagStep {admit : Admission} {p q : Pattern} (step : BagCommStep admit p q) :
    CanonicalBagStep admit p q := by
  induction step with
  | comm t u x A B bs principal admitted => exact .comm t u x A B bs principal admitted
  | parallel surrounding _ ih => exact .parallel surrounding ih
  | congruence before _ after ih => exact .congruence before ih after

/-- A step from two guards is a COMM, which the bag laws keep. -/
theorem guards_step_toCanonicalBagStep {admit : Admission} {source target : Pattern}
    (step : Step admit source target) :
    ∀ t x A u y B, close source = close (par (pFor t x A) (pFor u y B)) →
      CanonicalBagStep admit source target := by
  induction step with
  | comm t u x A B bs principal admitted =>
      intro _ _ _ _ _ _ _
      exact .comm t u x A B bs principal admitted
  | parallel surrounding inner _ =>
      intro t x A u y B same
      unfold close at same
      rw [closeIn_par, closeIn_par] at same
      have first : closeIn [] _ = closeIn [] (pFor t x A) := (by simpa [par, pPar] using same : _ ∧ _).1
      rw [closeIn_pFor] at first
      exact absurd first (Controls.step_source_not_guard inner _ _ _)
  | congruence before _ after ih =>
      intro t x A u y B same
      exact .congruence (.of_alphaEq before) (ih t x A u y B ((show close _ = close _ from before).symm.trans same))
        (.of_alphaEq after)
  | reflect x _ _ =>
      intro t x' A u y B same
      unfold close at same
      rw [closeIn_pReflect, closeIn_par] at same
      simp [pReflect, par, pPar] at same

/-! ## The executable step with canonical reflection -/

/-- One step of a closed process modulo the bag laws: COMM on any ordered pair
of guards among its components, and REFL on any reflected component, quoting
the canonical representative of the reduct. -/
def stepCanon (avoid : List String) : ℕ → List Pattern → List Pattern
  | 0, _ => []
  | fuel + 1, cs =>
      (picks cs).flatMap fun choice =>
        ((picks choice.2).flatMap fun second =>
            (commClosed avoid choice.1 second.1).map fun r => pPar (r :: second.2)) ++
          (match choice.1 with
           | .apply "MRef" [x, a] =>
               (stepCanon avoid fuel (components a)).map fun a' =>
                 pPar (pFor (tProc (canonicalBag a')) x pZero :: choice.2)
           | _ => [])

/-- **The corrected step modulo the bag laws, with canonical reflection.** -/
def cstepCanon (p : Pattern) : List Pattern :=
  stepCanon (pvars (close p)) (psize (close p) + 1) (components (close p))

theorem mem_stepCanon {avoid : List String} {fuel : ℕ} {cs : List Pattern} {Q : Pattern}
    (member : Q ∈ stepCanon avoid (fuel + 1) cs) :
    ∃ c₁ rest₁, (c₁, rest₁) ∈ picks cs ∧
      ((∃ c₂ rest r, (c₂, rest) ∈ picks rest₁ ∧ r ∈ commClosed avoid c₁ c₂ ∧ Q = pPar (r :: rest)) ∨
        (∃ x a a', c₁ = pReflect x a ∧ a' ∈ stepCanon avoid fuel (components a) ∧
          Q = pPar (pFor (tProc (canonicalBag a')) x pZero :: rest₁))) := by
  simp only [stepCanon, List.mem_flatMap, List.mem_append] at member
  obtain ⟨⟨c₁, rest₁⟩, inPicks, inner⟩ := member
  refine ⟨c₁, rest₁, inPicks, ?_⟩
  rcases inner with ⟨⟨c₂, rest⟩, inSecond, inComm⟩ | inRefl
  · obtain ⟨r, rIn, rfl⟩ := List.mem_map.mp inComm
    exact .inl ⟨c₂, rest, r, inSecond, rIn, rfl⟩
  · simp only at inRefl
    split at inRefl
    · rename_i x a
      obtain ⟨a', a'In, rfl⟩ := List.mem_map.mp inRefl
      exact .inr ⟨x, a, a', rfl, a'In, rfl⟩
    · cases inRefl

/-! ## Soundness modulo the bag laws -/

theorem stepCanon_sound (avoid : List String) : ∀ (fuel : ℕ) (P : Pattern), calcTerm P = true →
    (∀ z ∈ pvars (close P), z ∈ avoid) →
    ∀ Q ∈ stepCanon avoid fuel (components (close P)), CanonicalBagStep uniform P Q := by
  intro fuel
  induction fuel with
  | zero => intro P _ _ Q member; simp [stepCanon] at member
  | succ fuel ih =>
      intro P inCalc fresh Q member
      have closedComps : components (close P) = (components P).map close := components_closeIn P []
      have leafAll : ∀ c ∈ components P, components c = [c] := components_of_mem_components P
      obtain ⟨c₁, rest₁, inPicks, which⟩ := mem_stepCanon member
      have perm₁ := perm_of_mem_picks inPicks
      rw [closedComps] at perm₁
      obtain ⟨C₁, L₁, permC₁, closeC₁, permL₁⟩ := perm_map_cons_lift close perm₁
      have C₁mem : C₁ ∈ components P := permC₁.symm.subset (List.mem_cons_self ..)
      have restClosed : ∀ c ∈ rest₁, c ∈ components (close P) := fun c member =>
        (perm_of_mem_picks inPicks).symm.subset (List.mem_cons_of_mem _ member)
      rcases which with ⟨c₂, rest, r, inSecond, rIn, rfl⟩ | ⟨x, a, a', reflShape, a'In, rfl⟩
      · have perm₂ := perm_of_mem_picks inSecond
        obtain ⟨C₂, L, permC₂, closeC₂, permL⟩ := perm_map_cons_lift close (permL₁.trans perm₂)
        have C₂mem : C₂ ∈ components P :=
          permC₁.symm.subset (List.mem_cons_of_mem _ (permC₂.symm.subset (List.mem_cons_self ..)))
        have Lsub : ∀ c ∈ L, c ∈ components P := fun c member =>
          permC₁.symm.subset (List.mem_cons_of_mem _ (permC₂.symm.subset (List.mem_cons_of_mem _ member)))
        subst closeC₁ closeC₂
        cases g1 : asGuard (closeIn [] C₁) with
        | none => rw [show close C₁ = closeIn [] C₁ from rfl, commClosed_of_not_guard (.inl g1)] at rIn; cases rIn
        | some r1 =>
            cases g2 : asGuard (closeIn [] C₂) with
            | none =>
                rw [show close C₁ = closeIn [] C₁ from rfl, show close C₂ = closeIn [] C₂ from rfl,
                  commClosed_of_not_guard (.inr g2)] at rIn
                cases rIn
            | some r2 =>
                obtain ⟨t, xt, A, rfl, _⟩ := asGuard_closeIn g1
                obtain ⟨u, yu, B, rfl, _⟩ := asGuard_closeIn g2
                obtain ⟨calcT, _, calcA⟩ := calcTerm_pFor (calcTerm_of_mem_components inCalc C₁mem)
                obtain ⟨calcU, _, calcB⟩ := calcTerm_pFor (calcTerm_of_mem_components inCalc C₂mem)
                have freshPair : ∀ z ∈ pvars (close (par (pFor t xt A) (pFor u yu B))), z ∈ avoid := by
                  intro z occurs
                  unfold close at occurs
                  rw [closeIn_par, pvars_par] at occurs
                  rcases List.mem_append.mp occurs with h | h
                  · exact fresh z (pvars_close_of_mem_components C₁mem h)
                  · exact fresh z (pvars_close_of_mem_components C₂mem h)
                have sound := commClosed_sound_uniform avoid t xt A u yu B calcT calcU calcA calcB freshPair rIn
                have step₁ : CanonicalBagStep uniform (par (par (pFor t xt A) (pFor u yu B)) (pPar L))
                    (par r (pPar L)) := .parallel _ (guards_step_toCanonicalBagStep sound t xt A u yu B rfl)
                have leavesL : ∀ c ∈ L, components c = [c] := fun c member => leafAll c (Lsub c member)
                have before : BagEq P (par (par (pFor t xt A) (pFor u yu B)) (pPar L)) := by
                  rw [bagEq_iff, components_par, components_par, components_pPar_leaves L leavesL,
                    components_pFor, components_pFor]
                  exact (permC₁.trans (permC₂.cons _)).map close
                have leavesRest : ∀ c ∈ rest, components c = [c] := fun c member =>
                  leaf_of_mem_closed_components (restClosed c (perm₂.symm.subset (List.mem_cons_of_mem _ member)))
                have closedRest : rest.map close = rest := by
                  conv_rhs => rw [← List.map_id rest]
                  exact List.map_congr_left fun c member =>
                    close_of_mem_closed_components (restClosed c (perm₂.symm.subset (List.mem_cons_of_mem _ member)))
                have after : BagEq (par r (pPar L)) (pPar (r :: rest)) := by
                  rw [bagEq_iff, components_par, components_pPar_leaves L leavesL]
                  have : components (pPar (r :: rest)) = components r ++ rest := by
                    simp only [pPar, components, componentsList, componentsList_eq_flatMap]
                    rw [List.flatMap_congr (g := fun c => [c]) leavesRest, List.flatMap_singleton']
                  rw [this, List.map_append, List.map_append, closedRest]
                  exact List.Perm.append_left _ permL
                exact .congruence before step₁ after
      · subst closeC₁
        obtain ⟨X, A, rfl, rfl, rfl⟩ := closeIn_eq_pReflect reflShape
        have calcs := calcTerm_pReflect (calcTerm_of_mem_components inCalc C₁mem)
        have freshA : ∀ z ∈ pvars (close A), z ∈ avoid := by
          intro z occurs
          apply fresh z
          apply pvars_close_of_mem_components C₁mem
          unfold close at occurs ⊢
          rw [closeIn_pReflect, pvars_pReflect]
          exact List.mem_append_right _ occurs
        have inner := ih A calcs.2 freshA a' a'In
        have step₁ : CanonicalBagStep uniform (par (pReflect X A) (pPar L₁))
            (par (pFor (tProc (canonicalBag a')) X pZero) (pPar L₁)) := .parallel _ (.reflect X inner)
        have L₁sub : ∀ c ∈ L₁, c ∈ components P := fun c member =>
          permC₁.symm.subset (List.mem_cons_of_mem _ member)
        have leavesL₁ : ∀ c ∈ L₁, components c = [c] := fun c member => leafAll c (L₁sub c member)
        have reflLeaf : components (pReflect X A) = [pReflect X A] := by
          have := leafAll _ C₁mem
          exact this
        have before : BagEq P (par (pReflect X A) (pPar L₁)) := by
          rw [bagEq_iff, components_par, components_pPar_leaves L₁ leavesL₁, reflLeaf]
          exact permC₁.map close
        have leavesRest : ∀ c ∈ rest₁, components c = [c] := fun c member =>
          leaf_of_mem_closed_components (restClosed c member)
        have closedRest : rest₁.map close = rest₁ := by
          conv_rhs => rw [← List.map_id rest₁]
          exact List.map_congr_left fun c member => close_of_mem_closed_components (restClosed c member)
        have after : BagEq (par (pFor (tProc (canonicalBag a')) X pZero) (pPar L₁))
            (pPar (pFor (tProc (canonicalBag a')) (closeIn [] X) pZero :: rest₁)) := by
          rw [bagEq_iff, components_par, components_pPar_leaves L₁ leavesL₁, components_pFor]
          have : components (pPar (pFor (tProc (canonicalBag a')) (closeIn [] X) pZero :: rest₁)) =
              pFor (tProc (canonicalBag a')) (closeIn [] X) pZero :: rest₁ := by
            simp only [pPar, components, componentsList, componentsList_eq_flatMap]
            rw [List.flatMap_congr (g := fun c => [c]) leavesRest, List.flatMap_singleton', components_pFor]
            rfl
          rw [this, List.singleton_append, List.map_cons, List.map_cons, closedRest]
          have channel : close (pFor (tProc (canonicalBag a')) X pZero) = close (pFor (tProc (canonicalBag a')) (closeIn [] X) pZero) :=
            alphaEq_pFor_channel (tProc (canonicalBag a')) X pZero
          rw [channel]
          exact List.Perm.cons _ permL₁
        exact .congruence before step₁ after



theorem comm_mem_stepCanon {avoid : List String} {fuel : ℕ} {cs rest₁ rest : List Pattern}
    {c₁ c₂ r : Pattern} (first : (c₁, rest₁) ∈ picks cs) (second : (c₂, rest) ∈ picks rest₁)
    (fired : r ∈ commClosed avoid c₁ c₂) : pPar (r :: rest) ∈ stepCanon avoid (fuel + 1) cs := by
  simp only [stepCanon, List.mem_flatMap, List.mem_append]
  exact ⟨(c₁, rest₁), first, .inl ⟨(c₂, rest), second, List.mem_map_of_mem fired⟩⟩

theorem refl_mem_stepCanon {avoid : List String} {fuel : ℕ} {cs rest₁ : List Pattern} {x a a' : Pattern}
    (first : (pReflect x a, rest₁) ∈ picks cs) (inner : a' ∈ stepCanon avoid fuel (components a)) :
    pPar (pFor (tProc (canonicalBag a')) x pZero :: rest₁) ∈ stepCanon avoid (fuel + 1) cs := by
  simp only [stepCanon, List.mem_flatMap, List.mem_append]
  refine ⟨(pReflect x a, rest₁), first, .inr ?_⟩
  simp only [pReflect]
  exact List.mem_map_of_mem inner

theorem stepCanon_append {avoid : List String} {fuel : ℕ} {cs : List Pattern} (ms : List Pattern)
    (leaves : ∀ m ∈ ms, components m = [m]) {Q₁ : Pattern}
    (member : Q₁ ∈ stepCanon avoid (fuel + 1) cs) :
    ∃ Q₂ ∈ stepCanon avoid (fuel + 1) (cs ++ ms), components Q₂ = components Q₁ ++ ms := by
  have msFlat : ms.flatMap components = ms := by
    rw [List.flatMap_congr (g := fun c => [c]) leaves, List.flatMap_singleton']
  obtain ⟨c₁, rest₁, first, which⟩ := mem_stepCanon member
  rcases which with ⟨c₂, rest, r, second, fired, rfl⟩ | ⟨x, a, a', rfl, inner, rfl⟩
  · refine ⟨pPar (r :: (rest ++ ms)), comm_mem_stepCanon (mem_picks_append ms first)
      (mem_picks_append ms second) fired, ?_⟩
    rw [components_pPar_cons, components_pPar_cons, List.flatMap_append, msFlat, List.append_assoc]
  · refine ⟨pPar (pFor (tProc (canonicalBag a')) x pZero :: (rest₁ ++ ms)),
      refl_mem_stepCanon (mem_picks_append ms first) inner, ?_⟩
    rw [components_pPar_cons, components_pPar_cons, List.flatMap_append, msFlat, List.append_assoc]

/-- Reordering the components reorders the reducts' components. -/
theorem stepCanon_perm {avoid : List String} {fuel : ℕ} {cs cs' : List Pattern} (perm : cs.Perm cs')
    {Q₁ : Pattern} (member : Q₁ ∈ stepCanon avoid (fuel + 1) cs') :
    ∃ Q₂ ∈ stepCanon avoid (fuel + 1) cs, (components Q₂).Perm (components Q₁) := by
  obtain ⟨c₁, rest₁, first, which⟩ := mem_stepCanon member
  obtain ⟨rest₁', first', perm₁⟩ := mem_picks_of_perm (perm.trans (perm_of_mem_picks first))
  rcases which with ⟨c₂, rest, r, second, fired, rfl⟩ | ⟨x, a, a', rfl, inner, rfl⟩
  · obtain ⟨rest', second', perm₂⟩ := mem_picks_of_perm (perm₁.trans (perm_of_mem_picks second))
    refine ⟨pPar (r :: rest'), comm_mem_stepCanon first' second' fired, ?_⟩
    rw [components_pPar_cons, components_pPar_cons]
    exact List.Perm.append_left _ (perm₂.flatMap_right components)
  · refine ⟨pPar (pFor (tProc (canonicalBag a')) x pZero :: rest₁'), refl_mem_stepCanon first' inner, ?_⟩
    rw [components_pPar_cons, components_pPar_cons]
    exact List.Perm.append_left _ (perm₁.flatMap_right components)


/-- **Soundness with canonical reflection.** -/
theorem cstepCanon_sound_uniform {P Q : Pattern} (inCalc : calcTerm P = true) (member : Q ∈ cstepCanon P) :
    CanonicalBagStep uniform P Q :=
  stepCanon_sound (pvars (close P)) _ P inCalc (fun _ occurs => occurs) Q member

theorem cstepCanon_sound {P Q : Pattern} (inCalc : calcTerm P = true) (member : Q ∈ cstepCanon P) :
    CanonicalBagStep conventional P Q :=
  (cstepCanon_sound_uniform inCalc member).mono uniform_conventional

/-! ## Completeness with canonical reflection -/

theorem psize_pReflect (x a : Pattern) : psize (pReflect x a) = psize x + psize a + 1 := by
  simp [pReflect, psize, psizeList]

theorem components_close_pReflect (x a : Pattern) :
    components (close (pReflect x a)) = [pReflect (close x) (close a)] := by
  unfold close
  rw [closeIn_pReflect]
  simp [pReflect, components]

/-- **Completeness with canonical reflection.** Every step of the closing
fragment modulo the bag laws, REFL included, is matched up to the bag laws by
a step of the closed components, given fuel above the size of every
component. -/
theorem stepCanon_complete {P Q : Pattern} (step : CanonicalBagStep closing P Q) :
    ∀ (avoid : List String) (fuel : ℕ), (∀ c ∈ components (close P), psize c < fuel) →
      (∀ z ∈ pvars (close P), z ∈ avoid) →
      ∃ Q' ∈ stepCanon avoid fuel (components (close P)), BagEq Q' Q := by
  induction step with
  | comm t u x A B bs principal admitted =>
      intro avoid fuel bound fresh
      obtain ⟨Q₀, fired, alpha⟩ := commClosed_complete avoid t u x A B bs principal admitted fresh
      have comps : components (close (par (pFor t x A) (pFor u x B))) =
          [close (pFor t x A), close (pFor u x B)] := by
        unfold close
        rw [closeIn_par, components_par]
        exact congrArg₂ (· ++ ·) (components_close_pFor t x A) (components_close_pFor u x B)
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by
        have := bound _ (by rw [comps]; exact List.mem_cons_self ..)
        omega⟩
      refine ⟨pPar [Q₀], ?_, ?_⟩
      · rw [comps]
        exact comm_mem_stepCanon (rest₁ := [close (pFor u x B)]) (by simp [picks]) (by simp [picks]) fired
      · unfold BagEq
        have : components (close (pPar [Q₀])) = components (close Q₀) := by
          unfold close
          simp [pPar, closeIn, closeList, components, componentsList]
        rw [this, show close Q₀ = close _ from alpha]
  | parallel R _ ih =>
      rename_i source target stepS
      intro avoid fuel bound fresh
      have split : components (close (par source R)) = components (close source) ++ components (close R) := by
        unfold close; rw [closeIn_par, components_par]
      obtain ⟨Q₁, member, alpha⟩ := ih avoid fuel
        (fun c member => bound c (by rw [split]; exact List.mem_append_left _ member))
        fun z occurs => fresh z (by
          unfold close at occurs ⊢; rw [closeIn_par, pvars_par]; exact List.mem_append_left _ occurs)
      cases fuel with
      | zero => simp [stepCanon] at member
      | succ f =>
          have leavesR : ∀ m ∈ components (close R), components m = [m] := fun m member =>
            leaf_of_mem_closed_components member
          obtain ⟨Q₂, member₂, comps₂⟩ := stepCanon_append (components (close R)) leavesR member
          refine ⟨Q₂, by rw [split]; exact member₂, ?_⟩
          rw [bagEq_iff] at alpha ⊢
          have closedR : (components (close R)).map close = (components (close R)) := by
            conv_rhs => rw [← List.map_id (components (close R))]
            exact List.map_congr_left fun c member => close_of_mem_closed_components member
          rw [comps₂, components_par, List.map_append, List.map_append, closedR]
          have : components (close R) = (components R).map close := components_closeIn R []
          rw [this]
          exact List.Perm.append_right _ alpha
  | congruence before _ after ih =>
      rename_i source source' target' target stepS
      intro avoid fuel bound fresh
      have permComps : (components (close source)).Perm (components (close source')) := before
      have freshSource' : ∀ z ∈ pvars (close source'), z ∈ avoid := by
        intro z occurs
        obtain ⟨c, cIn, zIn⟩ := pvars_in_components _ z occurs
        have cInSource : c ∈ components (close source) := permComps.symm.subset cIn
        exact fresh z (pvars_of_mem_components cInSource zIn)
      obtain ⟨Q₁, member, alpha⟩ := ih avoid fuel (fun c member => bound c (permComps.symm.subset member))
        freshSource'
      cases fuel with
      | zero => simp [stepCanon] at member
      | succ f =>
          obtain ⟨Q₂, member₂, perm⟩ := stepCanon_perm permComps member
          refine ⟨Q₂, member₂, ?_⟩
          have : BagEq Q₂ Q₁ := by
            rw [bagEq_iff]; exact perm.map close
          exact this.trans (alpha.trans after)
  | reflect x _ ih =>
      rename_i source target stepS
      intro avoid fuel bound fresh
      have comps := components_close_pReflect x source
      have outer := bound _ (by rw [comps]; exact List.mem_cons_self ..)
      rw [psize_pReflect] at outer
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have innerBound : ∀ c ∈ components (close source), psize c < f := by
        intro c member
        have := psize_le_of_mem_components (close source) c member
        omega
      obtain ⟨a₁, member, alpha⟩ := ih avoid f innerBound fun z occurs => fresh z (by
        unfold close at occurs ⊢; rw [closeIn_pReflect, pvars_pReflect]; exact List.mem_append_right _ occurs)
      refine ⟨pPar [pFor (tProc (canonicalBag a₁)) (close x) pZero], ?_, ?_⟩
      · rw [comps]
        exact refl_mem_stepCanon (rest₁ := []) (by simp [picks, pReflect]) member
      · rw [canonicalBag_eq_of_bagEq alpha, bagEq_iff]
        have leaf : components (pPar [pFor (tProc (canonicalBag target)) (close x) pZero]) =
            [pFor (tProc (canonicalBag target)) (close x) pZero] := by
          simp [pPar, components, componentsList, pFor]
        rw [leaf, show listener x target = pFor (tProc (canonicalBag target)) x pZero from rfl, components_pFor]
        simp only [List.map_cons, List.map_nil]
        rw [show close (pFor (tProc (canonicalBag target)) (close x) pZero) =
          close (pFor (tProc (canonicalBag target)) x pZero) from (alphaEq_pFor_channel _ x pZero).symm]

/-- **Completeness of the step with canonical reflection** on the closing
fragment, for the whole relational semantics modulo the bag laws, REFL
included. -/
theorem cstepCanon_complete {P Q : Pattern} (step : CanonicalBagStep closing P Q) :
    ∃ Q' ∈ cstepCanon P, BagEq Q' Q :=
  stepCanon_complete step (pvars (close P)) (psize (close P) + 1)
    (fun c member => Nat.lt_succ_of_le (psize_le_of_mem_components _ c member)) fun _ occurs => occurs

/-! ## REFL respects the bag laws -/

/-- **The listener depends only on the class of the reduct.** -/
theorem reflect_listener_canonical (x : Pattern) {A₁ A₂ : Pattern} (same : BagEq A₁ A₂) :
    listener x A₁ = listener x A₂ := by
  unfold listener
  rw [canonicalBag_eq_of_bagEq same]

/-- **REFL respects the bag laws of the reflected process.** Two reflected
processes equal modulo the bag laws reach the same listener, and every
reduct equivalent to a reduct gives that same listener. -/
theorem reflect_respects_bagEq {admit : Admission} (x : Pattern) {A A' A₁ : Pattern} (same : BagEq A A')
    (step : CanonicalBagStep admit A A₁) :
    CanonicalBagStep admit (pReflect x A) (listener x A₁) ∧
      CanonicalBagStep admit (pReflect x A') (listener x A₁) ∧
      ∀ A₂, BagEq A₁ A₂ → listener x A₂ = listener x A₁ :=
  ⟨.reflect x step, .reflect x (.congruence same.symm step (BagEq.refl _)),
    fun _ equivalent => (reflect_listener_canonical x equivalent).symm⟩

/-- Multiplicity is kept: a component twice is not the component once. -/
theorem canonicalBag_keeps_multiplicity :
    canonicalBag (par BagControls.atomA BagControls.atomA) ≠ canonicalBag BagControls.atomA := by
  decide +kernel

/-! ## Controls -/

namespace ReflectionControls

open BagControls

/-- The control's two inputs in the other order. -/
def twoPartiesSwapped : Proc := par (pFor pZero demoChan atomB) (pFor pZero demoChan atomA)

def reflectedSwapped : Proc := pReflect demoChan twoPartiesSwapped

theorem reflected_bagEq : BagEq twoParties twoPartiesSwapped := BagEq.par_comm _ _

/-- The listener of the canonical reflection. -/
def canonicalListener : Proc := listener demoChan (par atomA atomB)

/-- **One class, one listener.** From either representative of the reflected
process, every listener the executable emits is the same one. COMM fires in
both orders of the two inputs, so the listener appears twice. -/
theorem canonical_reflection_one_listener :
    cstepCanon reflected = [pPar [canonicalListener], pPar [canonicalListener]] ∧
      cstepCanon reflectedSwapped = [pPar [canonicalListener], pPar [canonicalListener]] := by
  constructor <;> decide +kernel

/-- **Separating control.** The representative-dependent reading reaches two
listeners from one process, and the two are not equivalent. -/
theorem representative_reflection_two_listeners :
    BagStep conventional reflected listenerAB ∧ BagStep conventional reflected listenerBA ∧
      ¬ BagEq listenerAB listenerBA :=
  ⟨reflects_both.1, reflects_both.2, listeners_differ⟩

/-- With canonical reflection, the listeners of the two orders coincide. -/
theorem canonical_listeners_agree : listener demoChan (par atomA atomB) = listener demoChan (par atomB atomA) :=
  reflect_listener_canonical demoChan (BagEq.par_comm atomA atomB)

/-- A partner that quotes the canonical representative meets the listener. -/
def canonicalPartner : Proc := pFor (tProc (canonicalBag (par atomA atomB))) demoChan pZero

theorem canonical_partner_meets :
    cstep (par canonicalListener canonicalPartner) ≠ [] := by
  decide +kernel

/-- A partner that quotes a bag in another order does not: comparing patterns
modulo the bag laws is the separate admission of unification modulo the bag
laws. -/
theorem written_order_partner_misses :
    cstep (par canonicalListener (pFor (tProc (par atomB atomA)) demoChan pZero)) = [] := by
  decide +kernel

end ReflectionControls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Corrected
