import Mettapedia.Languages.MeTTa.HE.Types
import Mettapedia.Languages.MeTTa.HE.Matching
import Mettapedia.Languages.MeTTa.HE.DeclMatchSpec

/-!
# Declarative HE merge specification (Phase G2 scaffold)

The **declarative** spec for HE binding merge, faithful to the author's English spec
`merge_bindings` / `add_var_binding` / `add_var_equality`
(`Specs/he_metta_official_specs.md:436-492`). This is the merge analogue of `MatchRel`
(`DeclMatchSpec.lean`): the relation against which the computable `mergeBindings` /
`addVarBinding` / `addVarEquality` (`Matching.lean`) are to be proven sound + complete (the
mm-lean4 discipline).

## The recursive merge-back (the heart of the spec)
A conflict — adding `$x <- val` when `$x` already holds `prev ≠ val`, or equating two already-valued
variables — does **not overwrite**. It *unifies* the clashing values via `match_atoms` (here the proven
`MatchRel`) and **merges every resulting unifier back** (`:468-471`, `:489-491`). So the conflict
constructors recurse: `MatchRel prev val mB → MergeRel b mB out`. This unifier-keeping behavior is the
conformance point the bolstered draft flags (§9, "a merge that overwrites after checking unification is
incomplete").

## Provenance discipline (anti-circularity)
Every constructor cites an English-spec line `[:NNN]`. Anchored to the **author's text**, not to LeaTTa
or the LLM-drafted Lean. References the *proven-faithful* `MatchRel` for the conflict-unification cases.

## The keystone (witness §4)
Incompatible values cannot merge: adding `$x <- b` when `$x = a` (with `a`, `b` distinct symbols that
do not unify) has **no** valid `AddVarBindingRel` derivation — no overwrite, no spurious success. The
proof routes through the already-proven `matchRel_symSym_inv` (different symbols do not match), so the
merge spec inherits the match spec's faithfulness.
-/

namespace Mettapedia.Languages.MeTTa.HE.DeclMergeSpec

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.DeclMatchSpec
  (MatchRel matchRel_symSym_inv matchAtoms_sound matchAtoms_complete
   matchAtoms_mono mergeBindings_mono)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-! ## §1  The declarative merge relations (faithful to `:436-492`)

A 5-way mutual cluster. `AddVarBindingRel`/`AddVarEqualityRel` add one relation (with recursive
merge-back on conflict). `MergeAssignsRel`/`MergeEqsRel` fold a list of relations left-to-right.
`MergeRel` folds `right`'s assignments then equalities into `left`, exactly as `merge_bindings`. -/

mutual

/-- Add one value relation `$v <- val` to `b`. `[:452-471]` -/
inductive AddVarBindingRel : Bindings → String → Atom → Bindings → Prop where
  /-- `$v` is unbound → record the assignment. -/
  | unbound {b v val} : b.lookup v = none → AddVarBindingRel b v val (b.assign v val)
  /-- `$v` already holds exactly `val` → no change. -/
  | same {b v val} : b.lookup v = some val → AddVarBindingRel b v val b
  /-- `$v` holds a different `prev` → **unify and merge back** (no overwrite). `[:468-471]` -/
  | conflict {b v val prev mB out} :
      b.lookup v = some prev → prev ≠ val →
      MatchRel prev val mB → MergeRel b mB out → AddVarBindingRel b v val out

/-- Add one equality relation `$a = $c` to `b`. `[:472-492]` -/
inductive AddVarEqualityRel : Bindings → String → String → Bindings → Prop where
  /-- At most one side valued (or equal values) → drop `$c`'s assignment, record `$a = $c`. `[:485-486]` -/
  | recordEq {b a c} :
      (b.lookup a = none ∨ b.lookup c = none ∨ b.lookup a = b.lookup c) →
      AddVarEqualityRel b a c ((b.removeAssignment c).addEquality a c)
  /-- Both sides valued and distinct → **unify and merge back**. `[:489-491]` -/
  | conflict {b a c av cv mB out} :
      b.lookup a = some av → b.lookup c = some cv → av ≠ cv →
      MatchRel av cv mB → MergeRel b mB out → AddVarEqualityRel b a c out

/-- Fold a list of value relations into the accumulator. `[:446-448]` -/
inductive MergeAssignsRel : Bindings → List (String × Atom) → Bindings → Prop where
  | nil {acc} : MergeAssignsRel acc [] acc
  | cons {acc v val rest acc' out} :
      AddVarBindingRel acc v val acc' → MergeAssignsRel acc' rest out →
      MergeAssignsRel acc ((v, val) :: rest) out

/-- Fold a list of equality relations into the accumulator. `[:449-450]` -/
inductive MergeEqsRel : Bindings → List (String × String) → Bindings → Prop where
  | nil {acc} : MergeEqsRel acc [] acc
  | cons {acc a c rest acc' out} :
      AddVarEqualityRel acc a c acc' → MergeEqsRel acc' rest out →
      MergeEqsRel acc ((a, c) :: rest) out

/-- `merge_bindings(left, right)`: fold `right`'s assignments then equalities into `left`. `[:436-451]` -/
inductive MergeRel : Bindings → Bindings → Bindings → Prop where
  | mk {left right mid out} :
      MergeAssignsRel left right.assignments mid →
      MergeEqsRel mid right.equalities out →
      MergeRel left right out

end

/-! ## §1.5  Executable fold helpers + fuel monotonicity

The executable merge surface is a pair of left-to-right folds over lists of
relations.  We name those folds explicitly so the soundness/completeness proofs
can talk about them directly, then prove the small monotonicity/seedwise lemmas
needed to synchronize local witnesses to one common fuel. -/

/-- Pointwise inclusion on executable binding-result lists. -/
private def BSub (xs ys : List Bindings) : Prop := ∀ x ∈ xs, x ∈ ys

private theorem BSub.refl (xs : List Bindings) : BSub xs xs := fun _ h => h

private theorem flatMap_bsub {xs xs' : List Bindings}
    {f g : Bindings → List Bindings}
    (h_xs : BSub xs xs') (h_fg : ∀ a ∈ xs, BSub (f a) (g a)) :
    BSub (xs.flatMap f) (xs'.flatMap g) := by
  intro x hx
  obtain ⟨a, ha, hfa⟩ := List.mem_flatMap.mp hx
  exact List.mem_flatMap.mpr ⟨a, h_xs a ha, h_fg a ha x hfa⟩

/-- Fold `addVarBinding` over a list of assignments using one common fuel. -/
private def execAssignFold
    (acc : List Bindings) (assigns : List (String × Atom)) (fuel : Nat) :
    List Bindings :=
  assigns.foldl
    (fun acc (v, val) => acc.flatMap fun b => addVarBinding b v val fuel)
    acc

/-- Fold `addVarEquality` over a list of equalities using one common fuel. -/
private def execEqFold
    (acc : List Bindings) (eqs : List (String × String)) (fuel : Nat) :
    List Bindings :=
  eqs.foldl
    (fun acc (a, c) => acc.flatMap fun b => addVarEquality b a c fuel)
    acc

private theorem execAssignFold_flatMap_acc
    {α : Type} (assigns : List (String × Atom)) (acc : List α)
    (f : α → List Bindings) (fuel : Nat) :
    execAssignFold (acc.flatMap f) assigns fuel =
      acc.flatMap (fun a => execAssignFold (f a) assigns fuel) := by
  induction assigns generalizing acc f with
  | nil =>
      simp [execAssignFold]
  | cons p ps ih =>
      rcases p with ⟨v, val⟩
      simp only [execAssignFold, List.foldl_cons]
      rw [List.flatMap_assoc]
      exact
        ih acc
          (fun a => (f a).flatMap fun b => addVarBinding b v val fuel)

private theorem execAssignFold_seedwise
    (assigns : List (String × Atom)) (seeds : List Bindings) (fuel : Nat) :
    execAssignFold seeds assigns fuel =
      seeds.flatMap (fun b => execAssignFold [b] assigns fuel) := by
  simpa using
    (execAssignFold_flatMap_acc assigns seeds (fun b => [b]) fuel)

private theorem execEqFold_flatMap_acc
    {α : Type} (eqs : List (String × String)) (acc : List α)
    (f : α → List Bindings) (fuel : Nat) :
    execEqFold (acc.flatMap f) eqs fuel =
      acc.flatMap (fun a => execEqFold (f a) eqs fuel) := by
  induction eqs generalizing acc f with
  | nil =>
      simp [execEqFold]
  | cons p ps ih =>
      rcases p with ⟨a, c⟩
      simp only [execEqFold, List.foldl_cons]
      rw [List.flatMap_assoc]
      exact
        ih acc
          (fun seed => (f seed).flatMap fun b => addVarEquality b a c fuel)

private theorem execEqFold_seedwise
    (eqs : List (String × String)) (seeds : List Bindings) (fuel : Nat) :
    execEqFold seeds eqs fuel =
      seeds.flatMap (fun b => execEqFold [b] eqs fuel) := by
  simpa using
    (execEqFold_flatMap_acc eqs seeds (fun b => [b]) fuel)

private theorem addVarBinding_mono_step
    (b : Bindings) (v : String) (val : Atom) (fuel : Nat) :
    BSub (addVarBinding b v val fuel) (addVarBinding b v val (fuel + 1)) := by
  cases fuel with
  | zero =>
      intro out h
      simp [addVarBinding] at h
  | succ n =>
      intro out h
      cases hlookup : b.lookup v with
      | none =>
          simp [addVarBinding, hlookup] at h ⊢
          exact h
      | some prev =>
          by_cases hEq : prev = val
          · simp [addVarBinding, hlookup, hEq] at h ⊢
            exact h
          · simp [addVarBinding, hlookup, hEq] at h ⊢
            rcases h with ⟨mb, hmb, hmerge⟩
            exact ⟨mb, matchAtoms_mono prev val n 1 hmb, mergeBindings_mono b mb n 1 hmerge⟩

private theorem addVarBinding_mono
    (b : Bindings) (v : String) (val : Atom) (fuel extra : Nat) :
    BSub (addVarBinding b v val fuel) (addVarBinding b v val (fuel + extra)) := by
  induction extra with
  | zero =>
      simpa using BSub.refl (addVarBinding b v val fuel)
  | succ extra ih =>
      intro out h
      exact
        addVarBinding_mono_step b v val (fuel + extra)
          out (ih out h)

private theorem addVarEquality_mono_step
    (b : Bindings) (a c : String) (fuel : Nat) :
    BSub (addVarEquality b a c fuel) (addVarEquality b a c (fuel + 1)) := by
  cases fuel with
  | zero =>
      intro out h
      simp [addVarEquality] at h
  | succ n =>
      intro out h
      cases hA : b.lookup a <;> cases hC : b.lookup c <;>
        simp [addVarEquality, hA, hC] at h ⊢
      · exact h
      · exact h
      · exact h
      · rename_i av cv
        by_cases hEq : av = cv
        · simp [hEq] at h ⊢
          exact h
        · simp [hEq] at h ⊢
          rcases h with ⟨mb, hmb, hmerge⟩
          exact ⟨mb, matchAtoms_mono av cv n 1 hmb, mergeBindings_mono b mb n 1 hmerge⟩

private theorem addVarEquality_mono
    (b : Bindings) (a c : String) (fuel extra : Nat) :
    BSub (addVarEquality b a c fuel) (addVarEquality b a c (fuel + extra)) := by
  induction extra with
  | zero =>
      simpa using BSub.refl (addVarEquality b a c fuel)
  | succ extra ih =>
      intro out h
      exact
        addVarEquality_mono_step b a c (fuel + extra)
          out (ih out h)

private theorem execAssignFold_mono_local
    (assigns : List (String × Atom)) (fuel : Nat) :
    ∀ {acc acc' : List Bindings}, BSub acc acc' →
      BSub (execAssignFold acc assigns fuel)
        (execAssignFold acc' assigns (fuel + 1)) := by
  induction assigns with
  | nil =>
      intro acc acc' hacc
      simpa [execAssignFold] using hacc
  | cons p ps ih =>
      intro acc acc' hacc
      rcases p with ⟨v, val⟩
      simp only [execAssignFold, List.foldl_cons]
      exact ih (flatMap_bsub hacc (fun b _ => addVarBinding_mono_step b v val fuel))

private theorem execAssignFold_mono
    (acc : List Bindings) (assigns : List (String × Atom)) (fuel extra : Nat) :
    BSub (execAssignFold acc assigns fuel) (execAssignFold acc assigns (fuel + extra)) := by
  induction extra with
  | zero =>
      simpa using BSub.refl (execAssignFold acc assigns fuel)
  | succ extra ih =>
      intro out h
      have h' : out ∈ execAssignFold acc assigns (fuel + extra) := ih out h
      exact
        execAssignFold_mono_local assigns (fuel + extra) (acc := acc) (acc' := acc)
          (BSub.refl _) out h'

private theorem execEqFold_mono_local
    (eqs : List (String × String)) (fuel : Nat) :
    ∀ {acc acc' : List Bindings}, BSub acc acc' →
      BSub (execEqFold acc eqs fuel)
        (execEqFold acc' eqs (fuel + 1)) := by
  induction eqs with
  | nil =>
      intro acc acc' hacc
      simpa [execEqFold] using hacc
  | cons p ps ih =>
      intro acc acc' hacc
      rcases p with ⟨a, c⟩
      simp only [execEqFold, List.foldl_cons]
      exact ih (flatMap_bsub hacc (fun b _ => addVarEquality_mono_step b a c fuel))

private theorem execEqFold_mono
    (acc : List Bindings) (eqs : List (String × String)) (fuel extra : Nat) :
    BSub (execEqFold acc eqs fuel) (execEqFold acc eqs (fuel + extra)) := by
  induction extra with
  | zero =>
      simpa using BSub.refl (execEqFold acc eqs fuel)
  | succ extra ih =>
      intro out h
      have h' : out ∈ execEqFold acc eqs (fuel + extra) := ih out h
      exact
        execEqFold_mono_local eqs (fuel + extra) (acc := acc) (acc' := acc)
          (BSub.refl _) out h'

/-! ## §1.6  Soundness of the executable merge family

Each executable merge helper produces only declaratively valid merge steps.  We
prove this by fuel induction, with the assignment/equality folds handled by
small local inductions over the right-hand relation lists. -/

private theorem mergeSoundFamily : ∀ fuel,
    (∀ {b : Bindings} {v : String} {val : Atom} {out : Bindings},
        out ∈ addVarBinding b v val fuel → AddVarBindingRel b v val out) ∧
    (∀ {b : Bindings} {a c : String} {out : Bindings},
        out ∈ addVarEquality b a c fuel → AddVarEqualityRel b a c out) ∧
    (∀ {left right out : Bindings},
        out ∈ mergeBindings left right fuel → MergeRel left right out) := by
  intro fuel
  induction fuel with
  | zero =>
      refine ⟨?_, ?_, ?_⟩
      · intro b v val out h
        simp [addVarBinding] at h
      · intro b a c out h
        simp [addVarEquality] at h
      · intro left right out h
        simp [mergeBindings] at h
  | succ n ih =>
      obtain ⟨ihBind, ihEq, ihMerge⟩ := ih
      refine ⟨?_, ?_, ?_⟩
      · intro b v val out h
        cases hlookup : b.lookup v with
        | none =>
            simp [addVarBinding, hlookup] at h
            subst out
            exact .unbound hlookup
        | some prev =>
            by_cases hEqv : prev = val
            · simp [addVarBinding, hlookup, hEqv] at h
              subst out
              exact .same (by simpa [hEqv] using hlookup)
            · simp [addVarBinding, hlookup, hEqv] at h
              rcases h with ⟨mb, hmb, hmerge⟩
              exact .conflict hlookup hEqv (matchAtoms_sound hmb) (ihMerge hmerge)
      · intro b a c out h
        cases hA : b.lookup a with
        | none =>
            simp [addVarEquality, hA] at h
            subst out
            exact .recordEq (Or.inl hA)
        | some av =>
            cases hC : b.lookup c with
            | none =>
                simp [addVarEquality, hA, hC] at h
                subst out
                exact .recordEq (Or.inr (Or.inl hC))
            | some cv =>
                by_cases hEqv : av = cv
                · simp [addVarEquality, hA, hC, hEqv] at h
                  subst out
                  exact .recordEq (Or.inr (Or.inr (by simp [hA, hC, hEqv])))
                · simp [addVarEquality, hA, hC, hEqv] at h
                  rcases h with ⟨mb, hmb, hmerge⟩
                  exact .conflict hA hC hEqv (matchAtoms_sound hmb) (ihMerge hmerge)
      · intro left right out h
        change out ∈ execEqFold (execAssignFold [left] right.assignments n) right.equalities n at h
        have hAssignFold :
            ∀ {assigns : List (String × Atom)} {acc : List Bindings} {out : Bindings},
              out ∈ execAssignFold acc assigns n →
              ∃ seed, seed ∈ acc ∧ MergeAssignsRel seed assigns out := by
          intro assigns acc out hout
          induction assigns generalizing acc out with
          | nil =>
              exact ⟨out, by simpa [execAssignFold] using hout, .nil⟩
          | cons p ps ihPs =>
              rcases p with ⟨v, val⟩
              simp [execAssignFold, List.foldl_cons] at hout
              rcases ihPs hout with ⟨mid, hmid, hrest⟩
              rcases List.mem_flatMap.mp hmid with ⟨seed, hseed, hadd⟩
              exact ⟨seed, hseed, .cons (ihBind hadd) hrest⟩
        have hEqFold :
            ∀ {eqs : List (String × String)} {acc : List Bindings} {out : Bindings},
              out ∈ execEqFold acc eqs n →
              ∃ seed, seed ∈ acc ∧ MergeEqsRel seed eqs out := by
          intro eqs acc out hout
          induction eqs generalizing acc out with
          | nil =>
              exact ⟨out, by simpa [execEqFold] using hout, .nil⟩
          | cons p ps ihPs =>
              rcases p with ⟨a, c⟩
              simp [execEqFold, List.foldl_cons] at hout
              rcases ihPs hout with ⟨mid, hmid, hrest⟩
              rcases List.mem_flatMap.mp hmid with ⟨seed, hseed, hadd⟩
              exact ⟨seed, hseed, .cons (ihEq hadd) hrest⟩
        rcases hEqFold h with ⟨mid, hmid, hEqs⟩
        rcases hAssignFold hmid with ⟨seed, hseed, hAssigns⟩
        simp at hseed
        subst seed
        exact .mk hAssigns hEqs

/-- Soundness of the executable `addVarBinding` helper against the faithful
    declarative one-step merge relation. -/
theorem addVarBinding_sound
    {b : Bindings} {v : String} {val : Atom} {out : Bindings} {fuel : Nat}
    (h : out ∈ addVarBinding b v val fuel) :
    AddVarBindingRel b v val out :=
  (mergeSoundFamily fuel).1 h

/-- Soundness of the executable `addVarEquality` helper. -/
theorem addVarEquality_sound
    {b : Bindings} {a c : String} {out : Bindings} {fuel : Nat}
    (h : out ∈ addVarEquality b a c fuel) :
    AddVarEqualityRel b a c out :=
  (mergeSoundFamily fuel).2.1 h

/-- Soundness of the full executable `mergeBindings` surface against the
    faithful declarative merge relation. -/
theorem mergeBindings_sound
    {left right out : Bindings} {fuel : Nat}
    (h : out ∈ mergeBindings left right fuel) :
    MergeRel left right out :=
  (mergeSoundFamily fuel).2.2 h

/-! ## §1.7  Completeness of the executable merge family

Every declaratively valid merge step is realized by the executable helpers at
some finite fuel.  The recursive conflict cases use the already-proven
`matchAtoms_complete`, while the list folds are reassembled from singleton-seed
tail runs via the seedwise lemmas above. -/

private theorem flatMap_of_match_merge
    {lhs rhs : Atom} {seed mB out : Bindings} {fuelMatch fuelMerge : Nat}
    (hmatch : mB ∈ matchAtoms lhs rhs fuelMatch)
    (hmerge : out ∈ mergeBindings seed mB fuelMerge) :
    ∃ fuel,
      out ∈ (matchAtoms lhs rhs fuel).flatMap (fun mb => mergeBindings seed mb fuel) := by
  let fuel := max fuelMatch fuelMerge
  have hMatchLe : fuelMatch ≤ fuel := by
    dsimp [fuel]
    exact Nat.le_max_left _ _
  have hMergeLe : fuelMerge ≤ fuel := by
    dsimp [fuel]
    exact Nat.le_max_right _ _
  have hmatch' : mB ∈ matchAtoms lhs rhs fuel := by
    simpa [Nat.add_sub_of_le hMatchLe] using
      (matchAtoms_mono lhs rhs fuelMatch (fuel - fuelMatch) hmatch)
  have hmerge' : out ∈ mergeBindings seed mB fuel := by
    simpa [Nat.add_sub_of_le hMergeLe] using
      (mergeBindings_mono seed mB fuelMerge (fuel - fuelMerge) hmerge)
  exact ⟨fuel, List.mem_flatMap.mpr ⟨mB, hmatch', hmerge'⟩⟩

private theorem execAssignFold_cons_of_head_tail
    {v : String} {val : Atom} {rest : List (String × Atom)}
    {seed next out : Bindings} {fuelHead fuelTail : Nat}
    (hhead : next ∈ addVarBinding seed v val fuelHead)
    (htail : out ∈ execAssignFold [next] rest fuelTail) :
    ∃ fuel, out ∈ execAssignFold [seed] ((v, val) :: rest) fuel := by
  let fuel := max fuelHead fuelTail
  have hHeadLe : fuelHead ≤ fuel := by
    dsimp [fuel]
    exact Nat.le_max_left _ _
  have hTailLe : fuelTail ≤ fuel := by
    dsimp [fuel]
    exact Nat.le_max_right _ _
  have hhead' : next ∈ addVarBinding seed v val fuel := by
    simpa [Nat.add_sub_of_le hHeadLe] using
      (addVarBinding_mono seed v val fuelHead (fuel - fuelHead) next hhead)
  have htail' : out ∈ execAssignFold [next] rest fuel := by
    simpa [Nat.add_sub_of_le hTailLe] using
      (execAssignFold_mono [next] rest fuelTail (fuel - fuelTail) out htail)
  have hseeded :
      out ∈ execAssignFold (([seed]).flatMap fun b => addVarBinding b v val fuel) rest fuel := by
    rw [execAssignFold_seedwise rest (([seed]).flatMap fun b => addVarBinding b v val fuel) fuel]
    exact
      List.mem_flatMap.mpr
        ⟨next, List.mem_flatMap.mpr ⟨seed, by simp, hhead'⟩, htail'⟩
  refine ⟨fuel, ?_⟩
  simpa [execAssignFold, List.foldl_cons] using hseeded

private theorem execEqFold_cons_of_head_tail
    {a c : String} {rest : List (String × String)}
    {seed next out : Bindings} {fuelHead fuelTail : Nat}
    (hhead : next ∈ addVarEquality seed a c fuelHead)
    (htail : out ∈ execEqFold [next] rest fuelTail) :
    ∃ fuel, out ∈ execEqFold [seed] ((a, c) :: rest) fuel := by
  let fuel := max fuelHead fuelTail
  have hHeadLe : fuelHead ≤ fuel := by
    dsimp [fuel]
    exact Nat.le_max_left _ _
  have hTailLe : fuelTail ≤ fuel := by
    dsimp [fuel]
    exact Nat.le_max_right _ _
  have hhead' : next ∈ addVarEquality seed a c fuel := by
    simpa [Nat.add_sub_of_le hHeadLe] using
      (addVarEquality_mono seed a c fuelHead (fuel - fuelHead) next hhead)
  have htail' : out ∈ execEqFold [next] rest fuel := by
    simpa [Nat.add_sub_of_le hTailLe] using
      (execEqFold_mono [next] rest fuelTail (fuel - fuelTail) out htail)
  have hseeded :
      out ∈ execEqFold (([seed]).flatMap fun b => addVarEquality b a c fuel) rest fuel := by
    rw [execEqFold_seedwise rest (([seed]).flatMap fun b => addVarEquality b a c fuel) fuel]
    exact
      List.mem_flatMap.mpr
        ⟨next, List.mem_flatMap.mpr ⟨seed, by simp, hhead'⟩, htail'⟩
  refine ⟨fuel, ?_⟩
  simpa [execEqFold, List.foldl_cons] using hseeded

private structure MergeCompletePack where
  addVarBinding :
    ∀ {b : Bindings} {v : String} {val : Atom} {out : Bindings},
      AddVarBindingRel b v val out → ∃ fuel, out ∈ addVarBinding b v val fuel
  addVarEquality :
    ∀ {b : Bindings} {a c : String} {out : Bindings},
      AddVarEqualityRel b a c out → ∃ fuel, out ∈ addVarEquality b a c fuel
  mergeAssigns :
    ∀ {seed out : Bindings} {assigns : List (String × Atom)},
      MergeAssignsRel seed assigns out → ∃ fuel, out ∈ execAssignFold [seed] assigns fuel
  mergeEqs :
    ∀ {seed out : Bindings} {eqs : List (String × String)},
      MergeEqsRel seed eqs out → ∃ fuel, out ∈ execEqFold [seed] eqs fuel
  mergeRel :
    ∀ {left right out : Bindings},
      MergeRel left right out → ∃ fuel, out ∈ mergeBindings left right fuel

private theorem completePack : MergeCompletePack := by
  let m1 :
      (b : Bindings) → (v : String) → (val : Atom) → (out : Bindings) →
        AddVarBindingRel b v val out → Prop :=
    fun b v val out _ => ∃ fuel, out ∈ addVarBinding b v val fuel
  let m2 :
      (b : Bindings) → (a : String) → (c : String) → (out : Bindings) →
        AddVarEqualityRel b a c out → Prop :=
    fun b a c out _ => ∃ fuel, out ∈ addVarEquality b a c fuel
  let m3 :
      (seed : Bindings) → (assigns : List (String × Atom)) → (out : Bindings) →
        MergeAssignsRel seed assigns out → Prop :=
    fun seed assigns out _ => ∃ fuel, out ∈ execAssignFold [seed] assigns fuel
  let m4 :
      (seed : Bindings) → (eqs : List (String × String)) → (out : Bindings) →
        MergeEqsRel seed eqs out → Prop :=
    fun seed eqs out _ => ∃ fuel, out ∈ execEqFold [seed] eqs fuel
  let m5 :
      (left : Bindings) → (right : Bindings) → (out : Bindings) →
        MergeRel left right out → Prop :=
    fun left right out _ => ∃ fuel, out ∈ mergeBindings left right fuel
  let c1 :
      ∀ {b : Bindings} {v : String} {val : Atom}
        (hnone : b.lookup v = none),
        m1 b v val (b.assign v val) (.unbound hnone) := by
    intro b v val hnone
    refine ⟨1, ?_⟩
    simp [addVarBinding, hnone]
  let c2 :
      ∀ {b : Bindings} {v : String} {val : Atom}
        (hsame : b.lookup v = some val),
        m1 b v val b (.same hsame) := by
    intro b v val hsame
    refine ⟨1, ?_⟩
    simp [addVarBinding, hsame]
  let c3 :
      ∀ {b : Bindings} {v : String} {val prev : Atom} {mB out : Bindings}
        (hlookup : b.lookup v = some prev) (hneq : prev ≠ val)
        (hm : MatchRel prev val mB) (hmerge : MergeRel b mB out),
        m5 b mB out hmerge → m1 b v val out (.conflict hlookup hneq hm hmerge) := by
    intro b v val prev mB out hlookup hneq hm hmerge ihMerge
    obtain ⟨fuelMatch, hmatch⟩ := matchAtoms_complete hm
    obtain ⟨fuelMerge, hmergeMem⟩ := ihMerge
    obtain ⟨fuel, hflat⟩ := flatMap_of_match_merge hmatch hmergeMem
    refine ⟨fuel + 1, ?_⟩
    simpa [addVarBinding, hlookup, hneq] using hflat
  let c4 :
      ∀ {b : Bindings} {a c : String}
        (hcond : b.lookup a = none ∨ b.lookup c = none ∨ b.lookup a = b.lookup c),
        m2 b a c ((b.removeAssignment c).addEquality a c) (.recordEq hcond) := by
    intro b a c hcond
    refine ⟨1, ?_⟩
    rcases hcond with hA | hC | hEq
    · cases hC' : b.lookup c <;> simp [addVarEquality, hA, hC']
    · cases hA' : b.lookup a <;> simp [addVarEquality, hA', hC]
    · cases hA' : b.lookup a <;> cases hC' : b.lookup c
      · simp [addVarEquality, hA', hC']
      · simp [hA', hC'] at hEq
      · simp [hA', hC'] at hEq
      · rename_i av cv
        have havcv : av = cv := by simpa [hA', hC'] using hEq
        simp [addVarEquality, hA', hC', havcv]
  let c5 :
      ∀ {b : Bindings} {a c : String} {av cv : Atom} {mB out : Bindings}
        (hA : b.lookup a = some av) (hC : b.lookup c = some cv) (hneq : av ≠ cv)
        (hm : MatchRel av cv mB) (hmerge : MergeRel b mB out),
        m5 b mB out hmerge → m2 b a c out (.conflict hA hC hneq hm hmerge) := by
    intro b a c av cv mB out hA hC hneq hm hmerge ihMerge
    obtain ⟨fuelMatch, hmatch⟩ := matchAtoms_complete hm
    obtain ⟨fuelMerge, hmergeMem⟩ := ihMerge
    obtain ⟨fuel, hflat⟩ := flatMap_of_match_merge hmatch hmergeMem
    refine ⟨fuel + 1, ?_⟩
    simpa [addVarEquality, hA, hC, hneq] using hflat
  let c6 :
      ∀ {acc : Bindings}, m3 acc [] acc (.nil) := by
    intro acc
    refine ⟨0, ?_⟩
    simp [execAssignFold]
  let c7 :
      ∀ {acc : Bindings} {v : String} {val : Atom} {rest : List (String × Atom)} {acc' out : Bindings}
        (hHead : AddVarBindingRel acc v val acc') (hTail : MergeAssignsRel acc' rest out),
        m1 acc v val acc' hHead → m3 acc' rest out hTail →
          m3 acc ((v, val) :: rest) out (.cons hHead hTail) := by
    intro acc v val rest acc' out hHead hTail ihHead ihTail
    obtain ⟨fuelHead, hHeadMem⟩ := ihHead
    obtain ⟨fuelTail, hTailMem⟩ := ihTail
    exact execAssignFold_cons_of_head_tail hHeadMem hTailMem
  let c8 :
      ∀ {acc : Bindings}, m4 acc [] acc (.nil) := by
    intro acc
    refine ⟨0, ?_⟩
    simp [execEqFold]
  let c9 :
      ∀ {acc : Bindings} {a c : String} {rest : List (String × String)} {acc' out : Bindings}
        (hHead : AddVarEqualityRel acc a c acc') (hTail : MergeEqsRel acc' rest out),
        m2 acc a c acc' hHead → m4 acc' rest out hTail →
          m4 acc ((a, c) :: rest) out (.cons hHead hTail) := by
    intro acc a c rest acc' out hHead hTail ihHead ihTail
    obtain ⟨fuelHead, hHeadMem⟩ := ihHead
    obtain ⟨fuelTail, hTailMem⟩ := ihTail
    exact execEqFold_cons_of_head_tail hHeadMem hTailMem
  let c10 :
      ∀ {left right mid out : Bindings}
        (hAssigns : MergeAssignsRel left right.assignments mid)
        (hEqs : MergeEqsRel mid right.equalities out),
        m3 left right.assignments mid hAssigns →
          m4 mid right.equalities out hEqs →
            m5 left right out (.mk hAssigns hEqs) := by
    intro left right mid out hAssigns hEqs ihAssigns ihEqs
    obtain ⟨fuelAssigns, hAssignsMem⟩ := ihAssigns
    obtain ⟨fuelEqs, hEqsMem⟩ := ihEqs
    let fuel := max fuelAssigns fuelEqs
    have hAssignLe : fuelAssigns ≤ fuel := by
      dsimp [fuel]
      exact Nat.le_max_left _ _
    have hEqsLe : fuelEqs ≤ fuel := by
      dsimp [fuel]
      exact Nat.le_max_right _ _
    have hAssigns' : mid ∈ execAssignFold [left] right.assignments fuel := by
      simpa [Nat.add_sub_of_le hAssignLe] using
        (execAssignFold_mono [left] right.assignments fuelAssigns (fuel - fuelAssigns) _ hAssignsMem)
    have hEqs' : out ∈ execEqFold [mid] right.equalities fuel := by
      simpa [Nat.add_sub_of_le hEqsLe] using
        (execEqFold_mono [mid] right.equalities fuelEqs (fuel - fuelEqs) _ hEqsMem)
    have hseeded :
        out ∈ execEqFold (execAssignFold [left] right.assignments fuel) right.equalities fuel := by
      rw [execEqFold_seedwise right.equalities (execAssignFold [left] right.assignments fuel) fuel]
      exact List.mem_flatMap.mpr ⟨mid, hAssigns', hEqs'⟩
    refine ⟨fuel + 1, ?_⟩
    simpa [mergeBindings, execAssignFold, execEqFold] using hseeded
  refine {
    addVarBinding := ?_,
    addVarEquality := ?_,
    mergeAssigns := ?_,
    mergeEqs := ?_,
    mergeRel := ?_
  }
  · intro b v val out h
    exact
      AddVarBindingRel.rec
        (motive_1 := m1) (motive_2 := m2) (motive_3 := m3) (motive_4 := m4) (motive_5 := m5)
        c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 h
  · intro b a c out h
    exact
      AddVarEqualityRel.rec
        (motive_1 := m1) (motive_2 := m2) (motive_3 := m3) (motive_4 := m4) (motive_5 := m5)
        c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 h
  · intro seed assigns out h
    exact
      MergeAssignsRel.rec
        (motive_1 := m1) (motive_2 := m2) (motive_3 := m3) (motive_4 := m4) (motive_5 := m5)
        c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 h
  · intro seed eqs out h
    exact
      MergeEqsRel.rec
        (motive_1 := m1) (motive_2 := m2) (motive_3 := m3) (motive_4 := m4) (motive_5 := m5)
        c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 h
  · intro left right out h
    exact
      MergeRel.rec
        (motive_1 := m1) (motive_2 := m2) (motive_3 := m3) (motive_4 := m4) (motive_5 := m5)
        c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 h

/-- Completeness of the executable `addVarBinding` helper. -/
theorem addVarBinding_complete
    {b : Bindings} {v : String} {val : Atom} {out : Bindings}
    (h : AddVarBindingRel b v val out) :
    ∃ fuel, out ∈ addVarBinding b v val fuel :=
  completePack.addVarBinding h

/-- Completeness of the executable `addVarEquality` helper. -/
theorem addVarEquality_complete
    {b : Bindings} {a c : String} {out : Bindings}
    (h : AddVarEqualityRel b a c out) :
    ∃ fuel, out ∈ addVarEquality b a c fuel :=
  completePack.addVarEquality h

/-- Completeness of the full executable `mergeBindings` surface. -/
theorem mergeBindings_complete
    {left right out : Bindings}
    (h : MergeRel left right out) :
    ∃ fuel, out ∈ mergeBindings left right fuel :=
  completePack.mergeRel h

/-! ## §2  Positive witnesses — spec-compliant merges -/

/-- Merging two disjoint assignments accumulates both. -/
example : MergeRel ⟨[("x", .symbol "a")], []⟩ ⟨[("y", .symbol "b")], []⟩
    ⟨[("x", .symbol "a"), ("y", .symbol "b")], []⟩ :=
  .mk (.cons (.unbound rfl) .nil) .nil

/-- Merging an empty right binding is the identity. -/
example {b : Bindings} : MergeRel b ⟨[], []⟩ b := .mk .nil .nil

/-- Re-adding an already-present binding is a no-op (the `same` case). -/
example : MergeRel ⟨[("x", .symbol "a")], []⟩ ⟨[("x", .symbol "a")], []⟩ ⟨[("x", .symbol "a")], []⟩ :=
  .mk (.cons (.same rfl) .nil) .nil

/-! ## §3  Keystone negative — incompatible values cannot merge

Adding `$x <- b` when `$x` already holds `a` (distinct symbols that do not unify) has **no** valid
derivation: not `unbound` (it's bound), not `same` (`a ≠ b`), not `conflict` (that needs
`MatchRel (sym a) (sym b)`, impossible by `matchRel_symSym_inv`). No overwrite; no spurious success —
the merge spec inherits the match spec's faithfulness. -/

example {out : Bindings} :
    ¬ AddVarBindingRel ⟨[("x", .symbol "a")], []⟩ "x" (.symbol "b") out := by
  intro h
  cases h with
  | unbound hl => simp [Bindings.lookup] at hl
  | same hl => simp [Bindings.lookup] at hl
  | conflict hl _ hm _ =>
      simp [Bindings.lookup] at hl
      subst hl
      exact absurd (matchRel_symSym_inv hm).1 (by decide)

end Mettapedia.Languages.MeTTa.HE.DeclMergeSpec
