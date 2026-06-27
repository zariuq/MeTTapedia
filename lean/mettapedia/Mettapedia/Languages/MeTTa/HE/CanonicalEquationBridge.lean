import Mettapedia.Languages.MeTTa.HE.CanonAbsorbsFreshening
import Mettapedia.Languages.MeTTa.HE.LeaTTaBridge
import Mettapedia.Languages.MeTTa.HE.VariantQueryCorrectness
import Provenance.Util.ValueTypeString

namespace Mettapedia.Languages.MeTTa.HE.CanonicalEquationBridge

open Metta
open Mettapedia.Languages.MeTTa.OSLFCore
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.LeaTTaBridge
open Mettapedia.Languages.MeTTa.HE.CanonAbsorbsFreshening

private def counterSuffix (counter : Nat) (v : String) : String :=
  v ++ "#" ++ toString counter

private def counterMapping (counter : Nat) (vars : List String) : List (String × String) :=
  vars.map fun v => (v, counterSuffix counter v)

private theorem counterSuffix_injective (counter : Nat) :
    Function.Injective (counterSuffix counter) := by
  intro x y h
  apply String.ext
  have h' : x.toList ++ ("#" ++ toString counter).toList =
      y.toList ++ ("#" ++ toString counter).toList := by
    simpa [counterSuffix, String.toList_append, List.append_assoc] using congrArg String.toList h
  exact (List.append_left_inj (("#" ++ toString counter).toList)).mp h'

private theorem counterMapping_find?
    (counter : Nat) :
    ∀ (vars : List String) (v : String),
      (counterMapping counter vars).find? (fun p => p.1 == v) =
        (vars.find? (fun x => x == v)).map (fun x => (x, counterSuffix counter x)) := by
  intro vars v
  induction vars with
  | nil =>
      simp [counterMapping]
  | cons x xs ih =>
      by_cases hx : x = v
      · subst hx
        simp [counterMapping]
      · have hbeq : (x == v) = false := by
          simp [hx]
        simpa [counterMapping, hbeq] using ih

private theorem counterSubst_lookup
    (counter : Nat) :
    ∀ (vars : List String) (v : String),
      Metta.Subst.lookup
          (vars.map fun x => (x, Metta.Atom.var (counterSuffix counter x))) v =
        (vars.find? (fun x => x == v)).map (fun x => Metta.Atom.var (counterSuffix counter x)) := by
  intro vars v
  induction vars with
  | nil =>
      simp [Metta.Subst.lookup]
  | cons x xs ih =>
      by_cases hx : x = v
      · subst hx
        simp [Metta.Subst.lookup]
      · have hbeq : (x == v) = false := by
          simp [hx]
        have hne : v ≠ x := by
          intro h
          exact hx h.symm
        have hbeq' : (v == x) = false := by
          simp [hne]
        simpa [Metta.Subst.lookup, hbeq, hbeq'] using ih

private theorem renameVars_eq_substApply_counterMapping
    (counter : Nat) (vars : List String) :
    ∀ a : Metta.Atom,
      Metta.renameVars (counterMapping counter vars) a =
        Metta.Subst.apply
          (vars.map fun x => (x, Metta.Atom.var (counterSuffix counter x))) a := by
  refine Metta.Atom.recAux ?_ ?_ ?_ ?_
  · intro s
    simp [Metta.renameVars, Metta.Subst.apply]
  · intro v
    rw [Metta.renameVars, Metta.Subst.apply,
      counterMapping_find?, counterSubst_lookup]
    cases hfind : List.find? (fun x => x == v) vars <;> simp
  · intro g
    simp [Metta.renameVars, Metta.Subst.apply]
  · intro xs ih
    simpa [Metta.renameVars, Metta.Subst.apply] using
      congrArg Metta.Atom.expr (List.map_congr_left ih)

private theorem applyRen_counterMapping_of_mem
    (counter : Nat) :
    ∀ {vars : List String} {v : String},
      v ∈ vars →
        applyRen (counterMapping counter vars) v = counterSuffix counter v := by
  intro vars v hv
  induction vars with
  | nil =>
      cases hv
  | cons x xs ih =>
      unfold applyRen
      by_cases hx : x = v
      · subst hx
        simp [counterMapping, counterSuffix]
      · have hvxs : v ∈ xs := (List.mem_cons.mp hv).resolve_left (fun h => hx h.symm)
        have hbeq : (x == v) = false := by
          simp [hx]
        simp [counterMapping, hbeq, counterSuffix]
        simpa [counterMapping, applyRen, counterSuffix] using ih hvxs

private theorem renameVars_counterMapping_eq_renBy_of_varsSubset
    (counter : Nat) (vars : List String) (a : Metta.Atom)
    (hvars : ∀ v ∈ a.vars, v ∈ vars) :
    Metta.renameVars (counterMapping counter vars) a = renBy (counterSuffix counter) a := by
  rw [renameVars_eq_renBy]
  refine renBy_congr ?_
  intro v hv
  exact applyRen_counterMapping_of_mem counter (hvars v hv)

private theorem subst_apply_renBy_comm_of_lookup
    {s₁ s₂ : Metta.Subst} {g : String → String} :
    ∀ a : Metta.Atom,
      (∀ v ∈ a.vars,
        Metta.Subst.lookup s₂ (g v) =
          Option.map (renBy g) (Metta.Subst.lookup s₁ v)) →
      Metta.Subst.apply s₂ (renBy g a) = renBy g (Metta.Subst.apply s₁ a) := by
  intro a hlookup
  induction a with
  | sym s =>
      simp [Metta.Subst.apply, renBy]
  | gnd gnd =>
      simp [Metta.Subst.apply, renBy]
  | var v =>
      have hlook :
          Metta.Subst.lookup s₂ (g v) =
            Option.map (renBy g) (Metta.Subst.lookup s₁ v) :=
        hlookup v (by simp [Metta.Atom.vars])
      cases hs₁ : Metta.Subst.lookup s₁ v with
      | none =>
          have hs₂ : Metta.Subst.lookup s₂ (g v) = none := by
            simpa [hs₁] using hlook
          simp [Metta.Subst.apply, hs₁, hs₂]
      | some val =>
          have hs₂ : Metta.Subst.lookup s₂ (g v) = some (renBy g val) := by
            simpa [hs₁] using hlook
          simp [Metta.Subst.apply, hs₁, hs₂]
  | expr xs ih =>
      have hmap :
          xs.map (fun x => Metta.Subst.apply s₂ (renBy g x)) =
            xs.map (fun x => renBy g (Metta.Subst.apply s₁ x)) := by
        refine List.map_congr_left ?_
        intro x hx
        exact ih x hx (fun v hv => hlookup v (by
          simp only [Metta.Atom.vars, List.mem_flatten, List.mem_map]
          exact ⟨x.vars, ⟨x, hx, rfl⟩, hv⟩))
      simpa [Metta.Subst.apply, renBy] using congrArg Metta.Atom.expr hmap

private theorem canonicalizeVars_subst_apply_renBy_eq_of_lookup
    {s₁ s₂ : Metta.Subst} {g : String → String} {a : Metta.Atom}
    (hlookup : ∀ v ∈ a.vars,
      Metta.Subst.lookup s₂ (g v) =
        Option.map (renBy g) (Metta.Subst.lookup s₁ v))
    (hinj : Set.InjOn g {v | v ∈ (Metta.Subst.apply s₁ a).vars}) :
    canonicalizeVars (Metta.Subst.apply s₂ (renBy g a)) =
      canonicalizeVars (Metta.Subst.apply s₁ a) := by
  rw [subst_apply_renBy_comm_of_lookup a hlookup]
  exact canonicalizeVars_renBy_of_injOn_vars hinj

/-- LeaTTa runtime freshening is alpha-inert on the LHS: canonicalization
forgets the fresh counter suffixes entirely. -/
theorem freshenRule_alphaEq_fst
    (counter : Nat) (lhs rhs : Metta.Atom) :
    Metta.AlphaEq (Metta.Minimal.freshenRule counter lhs rhs).1 lhs := by
  unfold Metta.AlphaEq
  unfold Metta.Minimal.freshenRule
  cases hvars : lhs.vars ++ rhs.vars with
  | nil =>
      simp
  | cons v vs =>
      simp
      have hrename :
          Metta.Subst.apply
              ((v, Metta.Atom.var (counterSuffix counter v)) ::
                vs.map fun x => (x, Metta.Atom.var (counterSuffix counter x))) lhs =
            Metta.renameVars (counterMapping counter (v :: vs)) lhs := by
        simpa [counterMapping] using
          (renameVars_eq_substApply_counterMapping counter (v :: vs) lhs).symm
      have hsubset : ∀ x ∈ lhs.vars, x ∈ v :: vs := by
        intro x hx
        rw [← hvars]
        exact List.mem_append_left rhs.vars hx
      calc
        canonicalizeVars
            (Metta.Subst.apply
              ((v, Metta.Atom.var (v ++ "#" ++ counter.repr)) ::
                vs.map fun x => (x, Metta.Atom.var (x ++ "#" ++ counter.repr))) lhs)
            =
              canonicalizeVars (Metta.renameVars (counterMapping counter (v :: vs)) lhs) := by
                simpa [counterSuffix] using congrArg canonicalizeVars hrename
        _ = canonicalizeVars (renBy (counterSuffix counter) lhs) := by
              rw [renameVars_counterMapping_eq_renBy_of_varsSubset counter (v :: vs) lhs hsubset]
        _ = canonicalizeVars lhs := canonicalizeVars_renBy_of_injective (counterSuffix_injective counter) lhs

/-- LeaTTa runtime freshening is alpha-inert on the RHS as well. -/
theorem freshenRule_alphaEq_snd
    (counter : Nat) (lhs rhs : Metta.Atom) :
    Metta.AlphaEq (Metta.Minimal.freshenRule counter lhs rhs).2 rhs := by
  unfold Metta.AlphaEq
  unfold Metta.Minimal.freshenRule
  cases hvars : lhs.vars ++ rhs.vars with
  | nil =>
      simp
  | cons v vs =>
      simp
      have hrename :
          Metta.Subst.apply
              ((v, Metta.Atom.var (counterSuffix counter v)) ::
                vs.map fun x => (x, Metta.Atom.var (counterSuffix counter x))) rhs =
            Metta.renameVars (counterMapping counter (v :: vs)) rhs := by
        simpa [counterMapping] using
          (renameVars_eq_substApply_counterMapping counter (v :: vs) rhs).symm
      have hsubset : ∀ x ∈ rhs.vars, x ∈ v :: vs := by
        intro x hx
        rw [← hvars]
        exact List.mem_append_right lhs.vars hx
      calc
        canonicalizeVars
            (Metta.Subst.apply
              ((v, Metta.Atom.var (v ++ "#" ++ counter.repr)) ::
                vs.map fun x => (x, Metta.Atom.var (x ++ "#" ++ counter.repr))) rhs)
            =
              canonicalizeVars (Metta.renameVars (counterMapping counter (v :: vs)) rhs) := by
                simpa [counterSuffix] using congrArg canonicalizeVars hrename
        _ = canonicalizeVars (renBy (counterSuffix counter) rhs) := by
              rw [renameVars_counterMapping_eq_renBy_of_varsSubset counter (v :: vs) rhs hsubset]
        _ = canonicalizeVars rhs := canonicalizeVars_renBy_of_injective (counterSuffix_injective counter) rhs

private def decodeFreshName (s : String) : String × Nat :=
  let rs := s.toList.reverse
  let revDigits := rs.takeWhile (fun c => c != '#')
  let rest := rs.dropWhile (fun c => c != '#')
  (String.ofList (rest.drop 1).reverse, natStringValue (String.ofList revDigits.reverse))

private theorem digit_not_hash_of_mem_toDigits (n : Nat) :
    ∀ a ∈ (Nat.toDigits 10 n).reverse, (a != '#') = true := by
  intro a ha
  have ha' : a ∈ Nat.toDigits 10 n := List.mem_reverse.mp ha
  have hdig : a.isDigit = true :=
    Nat.isDigit_of_mem_toDigits (b := 10) (n := n) (by omega) (by omega) ha'
  have hneq : a ≠ '#' := by
    intro h
    simp [h] at hdig
  simp [hneq]

private theorem decodeFreshName_eq (v : String) (n : Nat) :
    decodeFreshName (v ++ "#" ++ toString n) = (v, n) := by
  unfold decodeFreshName
  rw [String.toList_append, String.toList_append, List.reverse_append, List.reverse_append]
  simp
  have htake :=
    List.takeWhile_append_of_pos
      (l₁ := (Nat.toDigits 10 n).reverse)
      (l₂ := '#' :: v.toList.reverse)
      (p := fun c => c != '#')
      (digit_not_hash_of_mem_toDigits n)
  have hdrop :=
    List.dropWhile_append_of_pos
      (l₁ := (Nat.toDigits 10 n).reverse)
      (l₂ := '#' :: v.toList.reverse)
      (p := fun c => c != '#')
      (digit_not_hash_of_mem_toDigits n)
  rw [htake, hdrop]
  have hnat : natStringValue (String.ofList (Nat.toDigits 10 n)) = n := by
    simpa [natStringValue, Nat.toList_repr] using natStringValue_repr n
  simp [hnat]

private theorem freshName_injective :
    Function.Injective (fun p : String × Nat => p.1 ++ "#" ++ toString p.2) := by
  intro p q h
  have hp : decodeFreshName (p.1 ++ "#" ++ toString p.2) =
      decodeFreshName (q.1 ++ "#" ++ toString q.2) := congrArg decodeFreshName h
  have hp' : decodeFreshName (p.1 ++ "#" ++ toString p.2) = p := by
    simpa using (decodeFreshName_eq p.1 p.2)
  have hq' : decodeFreshName (q.1 ++ "#" ++ toString q.2) = q := by
    simpa using (decodeFreshName_eq q.1 q.2)
  calc
    p = decodeFreshName (p.1 ++ "#" ++ toString p.2) := hp'.symm
    _ = decodeFreshName (q.1 ++ "#" ++ toString q.2) := hp
    _ = q := hq'

private def heFreshStep (st : List (String × String) × Nat) (v : String) :
    List (String × String) × Nat :=
  if st.1.any (fun p => p.1 == v) then st
  else ((v, s!"{v}#{st.2}") :: st.1, st.2 + 1)

private theorem freshMapping_eq_foldl_heFreshStep (counter : Nat) (vars : List String) :
    freshMapping counter vars = vars.foldl heFreshStep ([], counter) := by
  rfl

private theorem foldl_append_tail_invariant
    {x : String} {xs : List String} {acc : List (String × String)} {n : Nat} {xval : String}
    (hxs : x ∉ xs) (hacc : ∀ p ∈ acc, p.1 ≠ x) :
    List.foldl heFreshStep (acc ++ [(x, xval)], n) xs =
      let tail := List.foldl heFreshStep (acc, n) xs
      (tail.1 ++ [(x, xval)], tail.2) := by
  induction xs generalizing acc n with
  | nil =>
      simp
  | cons y ys ih =>
      have hyx : y ≠ x := by
        intro h
        apply hxs
        simp [h]
      have hys : x ∉ ys := by
        intro h
        exact hxs (List.mem_cons_of_mem _ h)
      simp only [List.foldl_cons, heFreshStep]
      have hsingle : ([(x, xval)] : List (String × String)).any (fun p => p.1 == y) = false := by
        simp
        intro h
        exact hyx h.symm
      have hany : ((acc ++ [(x, xval)]).any (fun p => p.1 == y)) = (acc.any (fun p => p.1 == y)) := by
        rw [List.any_append, hsingle]
        simp
      rw [hany]
      split
      · simpa using ih hys hacc
      · have hacc' : ∀ p ∈ ((y, s!"{y}#{n}") :: acc), p.1 ≠ x := by
          intro p hp
          rcases List.mem_cons.mp hp with rfl | hp
          · exact hyx
          · exact hacc p hp
        simpa [List.append_assoc] using ih hys hacc'

private theorem freshMapping_cons_of_not_mem
    {x : String} {xs : List String} (idx : Nat) (hx : x ∉ xs) :
    freshMapping idx (x :: xs) =
      let tail := freshMapping (idx + 1) xs
      (tail.1 ++ [(x, s!"{x}#{idx}")], tail.2) := by
  change List.foldl heFreshStep ([(x, s!"{x}#{idx}")], idx + 1) xs = _
  show
    List.foldl heFreshStep ([(x, s!"{x}#{idx}")], idx + 1) xs =
      let tail := List.foldl heFreshStep ([], idx + 1) xs
      (tail.1 ++ [(x, s!"{x}#{idx}")], tail.2)
  simpa [freshMapping_eq_foldl_heFreshStep]
    using
      (foldl_append_tail_invariant
        (acc := []) (n := idx + 1) (xval := s!"{x}#{idx}") hx
        (by intro p hp; cases hp))

private theorem nodup_eraseDups : (xs : List String) → xs.eraseDups.Nodup
  | [] => by
      simp
  | x :: xs => by
      rw [List.eraseDups_cons]
      refine List.Nodup.cons ?_ (nodup_eraseDups _)
      intro hx
      have : x ∈ List.filter (fun b => !b == x) xs := List.mem_eraseDups.mp hx
      simp at this
termination_by xs => xs.length
decreasing_by
  simpa using Nat.lt_succ_of_le (List.length_filter_le (fun b => !b == x) xs)

private theorem freshMapping_find?_of_not_mem_nodup
    {vars : List String} (hnd : vars.Nodup) (idx : Nat) {v : String}
    (hv : v ∉ vars) :
    List.find? (fun p => p.1 == v) (freshMapping idx vars).1 = none := by
  induction vars generalizing idx with
  | nil =>
      simp [freshMapping]
  | cons x xs ih =>
      cases hnd with
      | @cons _ _ hnotin hndxs =>
          have hxnot : x ∉ xs := by
            intro hx
            exact hnotin _ hx rfl
          have hvx : v ≠ x := by
            intro h
            subst h
            exact hv (by simp)
          have hvxs : v ∉ xs := by
            intro h
            exact hv (List.mem_cons_of_mem _ h)
          rw [freshMapping_cons_of_not_mem idx hxnot]
          rw [List.find?_append, ih hndxs (idx + 1) hvxs]
          have hxv : x ≠ v := by
            intro h
            exact hvx h.symm
          simp [hxv]

private theorem applyRen_freshMapping_of_not_mem_nodup
    {vars : List String} (hnd : vars.Nodup) (idx : Nat) {v : String}
    (hv : v ∉ vars) :
    applyRen (freshMapping idx vars).1 v = v := by
  induction vars generalizing idx with
  | nil =>
      simp [freshMapping, applyRen]
  | cons x xs ih =>
      cases hnd with
      | @cons _ _ hnotin hndxs =>
      have hxnot : x ∉ xs := by
        intro hx
        exact hnotin _ hx rfl
      have hvx : v ≠ x := by
        intro h
        subst h
        exact hv (by simp)
      have hvxs : v ∉ xs := by
        intro h
        exact hv (List.mem_cons_of_mem _ h)
      rw [freshMapping_cons_of_not_mem idx hxnot]
      unfold applyRen
      rw [List.find?_append]
      have htail : List.find? (fun p => p.1 == v) (freshMapping (idx + 1) xs).1 = none :=
        freshMapping_find?_of_not_mem_nodup hndxs (idx + 1) hvxs
      rw [htail]
      have hxv : x ≠ v := by
        intro h
        exact hvx h.symm
      simp [hxv]

private theorem freshMapping_applyRen_of_mem_nodup
    {vars : List String} (hnd : vars.Nodup) (idx : Nat) {v : String}
    (hv : v ∈ vars) :
    ∃ k, k < vars.length ∧ applyRen (freshMapping idx vars).1 v = v ++ "#" ++ toString (idx + k) := by
  induction vars generalizing idx with
  | nil =>
      cases hv
  | cons x xs ih =>
      cases hnd with
      | @cons _ _ hnotin hndxs =>
          have hxnot : x ∉ xs := by
            intro hx
            exact hnotin _ hx rfl
          rcases List.mem_cons.mp hv with rfl | hvxs
          · refine ⟨0, by simp, ?_⟩
            rw [freshMapping_cons_of_not_mem idx hxnot]
            unfold applyRen
            rw [List.find?_append]
            have hvnot : v ∉ xs := by
              simpa using hxnot
            have htail :
                List.find? (fun p => p.1 == v) (freshMapping (idx + 1) xs).1 = none :=
              freshMapping_find?_of_not_mem_nodup hndxs (idx + 1) hvnot
            rw [htail]
            simp [List.find?]
            rfl
          · rcases ih hndxs (idx + 1) hvxs with ⟨k, hk, happly⟩
            refine ⟨k + 1, by simp [hk], ?_⟩
            rw [freshMapping_cons_of_not_mem idx hxnot]
            have hvx : v ≠ x := by
              intro h
              subst h
              exact hxnot hvxs
            have hxv : x ≠ v := by
              intro h
              exact hvx h.symm
            simpa [applyRen, List.find?_append, hxv, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using happly

private theorem freshMapping_applyRen_injOn_of_nodup
    {vars : List String} (hnd : vars.Nodup) (idx : Nat) :
    Set.InjOn (applyRen (freshMapping idx vars).1) {v | v ∈ vars} := by
  intro u hu v hv huv
  rcases freshMapping_applyRen_of_mem_nodup hnd idx hu with ⟨ku, hku, hu'⟩
  rcases freshMapping_applyRen_of_mem_nodup hnd idx hv with ⟨kv, hkv, hv'⟩
  have hpairs : (u, idx + ku) = (v, idx + kv) := by
    apply freshName_injective
    simpa [hu', hv'] using huv
  have : u = v ∧ idx + ku = idx + kv := by
    simpa using hpairs
  exact this.1

private theorem collectVars_eq_toLeaTTaAtom_vars_of_depth :
    ∀ fuel (a : OSLFCore.Atom), atomDepth a + 1 ≤ fuel →
      collectVars a fuel = (toLeaTTaAtom a).vars := by
  intro fuel
  induction fuel with
  | zero =>
      intro a hdepth
      omega
  | succ fuel ih =>
      intro a hdepth
      cases a with
      | symbol s =>
          simp [collectVars, toLeaTTaAtom, Metta.Atom.vars]
      | var v =>
          simp [collectVars, toLeaTTaAtom, Metta.Atom.vars]
      | grounded g =>
          simp [collectVars, toLeaTTaAtom, Metta.Atom.vars]
      | expression es =>
          have hlist :
              ∀ es : List OSLFCore.Atom, listDepth es + 1 ≤ fuel →
                collectVars.collectVarsList es fuel =
                  ((toLeaTTaAtoms es).map Metta.Atom.vars).flatten := by
            intro es
            induction es with
            | nil =>
                intro _
                simp [collectVars.collectVarsList, toLeaTTaAtoms]
            | cons e es ihEs =>
                intro hes
                simp [collectVars.collectVarsList, toLeaTTaAtoms, listDepth] at hes ⊢
                have hhead : atomDepth e + 1 ≤ fuel := by
                  omega
                have htail : listDepth es + 1 ≤ fuel := by
                  omega
                rw [ih e hhead, ihEs htail]
          have hes : listDepth es + 1 ≤ fuel := by
            simp [atomDepth] at hdepth
            omega
          simpa [collectVars, toLeaTTaAtom, Metta.Atom.vars] using hlist es hes

theorem freshenEquation_alphaEq_fst
    (idx : Nat) (lhs rhs : OSLFCore.Atom) (fuel : Nat)
    (hdepth : atomDepth lhs + 1 ≤ fuel) :
    Metta.AlphaEq (toLeaTTaAtom (freshenEquation idx lhs rhs fuel).1) (toLeaTTaAtom lhs) := by
  unfold Metta.AlphaEq
  let vars := (collectVars lhs fuel ++ collectVars rhs fuel).eraseDups
  have hrename :=
    toLeaTTaAtom_freshenEquation_fst idx lhs rhs fuel hdepth
  have hvarsEq : collectVars lhs fuel = (toLeaTTaAtom lhs).vars :=
    collectVars_eq_toLeaTTaAtom_vars_of_depth fuel lhs hdepth
  have hsubset : ∀ v ∈ (toLeaTTaAtom lhs).vars, v ∈ vars := by
    intro v hv
    apply List.mem_eraseDups.mpr
    rw [← hvarsEq] at hv
    exact List.mem_append_left _ hv
  have hnd : vars.Nodup := nodup_eraseDups _
  have hinj :
      Set.InjOn (applyRen (freshMapping idx vars).1) {v | v ∈ (toLeaTTaAtom lhs).vars} := by
    intro u hu v hv huv
    exact freshMapping_applyRen_injOn_of_nodup hnd idx (hsubset u hu) (hsubset v hv) huv
  calc
    canonicalizeVars (toLeaTTaAtom (freshenEquation idx lhs rhs fuel).1)
        = canonicalizeVars
            (Metta.renameVars (freshMapping idx vars).1 (toLeaTTaAtom lhs)) := by
              simpa [vars] using congrArg canonicalizeVars hrename
    _ = canonicalizeVars (toLeaTTaAtom lhs) :=
          canonicalizeVars_renameVars_of_injOn_vars hinj

theorem freshenEquation_alphaEq_snd
    (idx : Nat) (lhs rhs : OSLFCore.Atom) (fuel : Nat)
    (hdepth : atomDepth rhs + 1 ≤ fuel) :
    Metta.AlphaEq (toLeaTTaAtom (freshenEquation idx lhs rhs fuel).2) (toLeaTTaAtom rhs) := by
  unfold Metta.AlphaEq
  let vars := (collectVars lhs fuel ++ collectVars rhs fuel).eraseDups
  have hrename :=
    toLeaTTaAtom_freshenEquation_snd idx lhs rhs fuel hdepth
  have hvarsEq : collectVars rhs fuel = (toLeaTTaAtom rhs).vars :=
    collectVars_eq_toLeaTTaAtom_vars_of_depth fuel rhs hdepth
  have hsubset : ∀ v ∈ (toLeaTTaAtom rhs).vars, v ∈ vars := by
    intro v hv
    apply List.mem_eraseDups.mpr
    rw [← hvarsEq] at hv
    exact List.mem_append_right _ hv
  have hnd : vars.Nodup := nodup_eraseDups _
  have hinj :
      Set.InjOn (applyRen (freshMapping idx vars).1) {v | v ∈ (toLeaTTaAtom rhs).vars} := by
    intro u hu v hv huv
    exact freshMapping_applyRen_injOn_of_nodup hnd idx (hsubset u hu) (hsubset v hv) huv
  calc
    canonicalizeVars (toLeaTTaAtom (freshenEquation idx lhs rhs fuel).2)
        = canonicalizeVars
            (Metta.renameVars (freshMapping idx vars).1 (toLeaTTaAtom rhs)) := by
              simpa [vars] using congrArg canonicalizeVars hrename
    _ = canonicalizeVars (toLeaTTaAtom rhs) :=
          canonicalizeVars_renameVars_of_injOn_vars hinj

/-- The two independent freshening conventions already agree at the canonical
surface on the translated LHS: LeaTTa's runtime `freshenRule` and HE's
`freshenEquation` may choose different concrete names, but they land in the
same alpha-class. -/
theorem freshenRule_alphaEq_freshenEquation_fst
    (counter idx : Nat) (lhs rhs : OSLFCore.Atom) (fuel : Nat)
    (hdepth : atomDepth lhs + 1 ≤ fuel) :
    Metta.AlphaEq
      (Metta.Minimal.freshenRule counter (toLeaTTaAtom lhs) (toLeaTTaAtom rhs)).1
      (toLeaTTaAtom (freshenEquation idx lhs rhs fuel).1) := by
  unfold Metta.AlphaEq
  exact
    (freshenRule_alphaEq_fst counter (toLeaTTaAtom lhs) (toLeaTTaAtom rhs)).trans
      (freshenEquation_alphaEq_fst idx lhs rhs fuel hdepth).symm

/-- RHS companion to `freshenRule_alphaEq_freshenEquation_fst`. This is the
canonical-hub form of "same rule, different freshening discipline": the emitted
runtime RHS and the HE freshened RHS agree up to alpha-renaming. -/
theorem freshenRule_alphaEq_freshenEquation_snd
    (counter idx : Nat) (lhs rhs : OSLFCore.Atom) (fuel : Nat)
    (hdepth : atomDepth rhs + 1 ≤ fuel) :
    Metta.AlphaEq
      (Metta.Minimal.freshenRule counter (toLeaTTaAtom lhs) (toLeaTTaAtom rhs)).2
      (toLeaTTaAtom (freshenEquation idx lhs rhs fuel).2) := by
  unfold Metta.AlphaEq
  exact
    (freshenRule_alphaEq_snd counter (toLeaTTaAtom lhs) (toLeaTTaAtom rhs)).trans
      (freshenEquation_alphaEq_snd idx lhs rhs fuel hdepth).symm

private theorem resolve_eq_lookup_or_none_of_noVar
    {b : Bindings} (hno : NoVarAssignmentValues b) :
    ∀ fuel v, b.resolve v fuel = match fuel with | 0 => none | _ + 1 => b.lookup v := by
  intro fuel v
  cases fuel with
  | zero =>
      rfl
  | succ fuel =>
      unfold Bindings.resolve
      cases hlookup : b.lookup v with
      | none =>
          rfl
      | some val =>
          cases val with
          | var x =>
              exact False.elim (hno hlookup)
          | symbol s =>
              rfl
          | grounded g =>
              rfl
          | expression es =>
              rfl

private theorem resolve_eq_lookup_or_none_of_keysRenamedBy_noVar
    (r : VarRenaming) {b b' : Bindings}
    (hrel : BindingsKeysRenamedBy r b b')
    (hno : NoVarAssignmentValues b) :
    ∀ fuel v,
      b'.resolve (r.rename v) fuel =
        match fuel with | 0 => none | _ + 1 => b'.lookup (r.rename v) := by
  intro fuel v
  cases fuel with
  | zero =>
      rfl
  | succ fuel =>
      unfold Bindings.resolve
      cases hlookup : b.lookup v with
      | none =>
          have hnone' : b'.lookup (r.rename v) = none := by
            have hbound := hrel.bound_iff v
            simp [hlookup] at hbound
            exact hbound
          rw [hnone']
      | some val =>
          have hlookup' : b'.lookup (r.rename v) = some val :=
            hrel.forward v val hlookup
          cases val with
          | var x =>
              exact False.elim (hno hlookup)
          | symbol s =>
              rw [hlookup']
          | grounded g =>
              rw [hlookup']
          | expression es =>
              rw [hlookup']

/-- When a pattern-key renaming leaves all matched values fixed and the original
bindings carry no variable-valued assignments, applying the renamed bindings to
the renamed atom computes the same result as renaming the original HE
application result. This is the core HE-side transport lemma behind the
restricted no-chain equation bridge: renamed matcher keys are harmless once
recursive variable chains are absent. -/
private theorem applyAtomTotal_apply_of_bindingsKeysRenamedBy_noVar
    (r : VarRenaming) {b b' : Bindings}
    (hrel : BindingsKeysRenamedBy r b b')
    (hno : NoVarAssignmentValues b)
    (hfix : ∀ {v val}, b.lookup v = some val → applyAtomTotal r val = val) :
    ∀ fuel a,
      b'.apply (applyAtomTotal r a) fuel = applyAtomTotal r (b.apply a fuel) := by
  intro fuel
  induction fuel with
  | zero =>
      intro a
      simp [Bindings.apply]
  | succ fuel ih =>
      intro a
      cases a with
      | symbol s =>
          simp [Bindings.apply, applyAtomTotal]
      | grounded g =>
          simp [Bindings.apply, applyAtomTotal]
      | expression es =>
          simp [Bindings.apply, applyAtomTotal]
          intro a ha
          exact ih a
      | var v =>
          cases fuel with
          | zero =>
              simp [Bindings.apply, Bindings.resolve, applyAtomTotal]
          | succ fuel =>
              cases hlookup : b.lookup v with
              | none =>
                  have hnone' : b'.lookup (r.rename v) = none := by
                    have hbound := hrel.bound_iff v
                    simp [hlookup] at hbound
                    exact hbound
                  simp [Bindings.apply, Bindings.resolve, applyAtomTotal, hlookup, hnone']
              | some val =>
                  have hlookup' : b'.lookup (r.rename v) = some val :=
                    hrel.forward v val hlookup
                  have hfixed : applyAtomTotal r val = val := hfix hlookup
                  cases val with
                  | var x =>
                      exact False.elim (hno hlookup)
                  | symbol s =>
                      simp [Bindings.apply, Bindings.resolve, applyAtomTotal, hlookup, hlookup', hfixed]
                  | grounded g =>
                      simp [Bindings.apply, Bindings.resolve, applyAtomTotal, hlookup, hlookup', hfixed]
                  | expression es =>
                      simp [Bindings.apply, Bindings.resolve, applyAtomTotal, hlookup, hlookup', hfixed]

private theorem toLeaTTaAtom_applyAtomTotal_eq_renBy
    (r : VarRenaming) :
    ∀ a : OSLFCore.Atom, toLeaTTaAtom (applyAtomTotal r a) = renBy r.rename (toLeaTTaAtom a)
  | .symbol _ => by simp [applyAtomTotal, toLeaTTaAtom, renBy]
  | .var _ => by simp [applyAtomTotal, toLeaTTaAtom]
  | .grounded _ => by simp [applyAtomTotal, toLeaTTaAtom, renBy]
  | .expression es =>
      by
        simp [applyAtomTotal, toLeaTTaAtom, toLeaTTaAtoms_applyAtomTotal_eq_map_renBy r es]
where
  toLeaTTaAtoms_applyAtomTotal_eq_map_renBy
      (r : VarRenaming) :
      ∀ es : List OSLFCore.Atom,
        toLeaTTaAtoms (es.map (applyAtomTotal r)) =
          (toLeaTTaAtoms es).map (renBy r.rename)
    | [] => rfl
    | e :: es => by
        simp [toLeaTTaAtoms_applyAtomTotal_eq_map_renBy r es,
          toLeaTTaAtom_applyAtomTotal_eq_renBy r e]

/-- Any injective HE variable renaming is invisible to LeaTTa's canonical
surface after translation: the renamed HE atom is alpha-equivalent to the
original one. This is the free-metavariable half of the canonical-hub story,
separate from the binder-level de Bruijn layer. -/
private theorem alphaEq_toLeaTTaAtom_applyAtomTotal_of_injective
    (r : VarRenaming) (hr : r.Injective) (a : OSLFCore.Atom) :
    Metta.AlphaEq (toLeaTTaAtom (applyAtomTotal r a)) (toLeaTTaAtom a) := by
  unfold Metta.AlphaEq
  rw [toLeaTTaAtom_applyAtomTotal_eq_renBy]
  exact canonicalizeVars_renBy_of_injective hr (toLeaTTaAtom a)

mutual

/-- Pure variable renaming is structurally depth-preserving on HE atoms. -/
private theorem atomDepth_applyAtomTotal_eq
    (r : VarRenaming) :
    ∀ a : OSLFCore.Atom, atomDepth (applyAtomTotal r a) = atomDepth a
  | .symbol _ => by simp [atomDepth, applyAtomTotal]
  | .var _ => by simp [atomDepth, applyAtomTotal]
  | .grounded _ => by simp [atomDepth, applyAtomTotal]
  | .expression es => by
      simp [atomDepth, applyAtomTotal, listDepth_applyAtomTotal_eq r es]

/-- List companion to `atomDepth_applyAtomTotal_eq`. -/
private theorem listDepth_applyAtomTotal_eq
    (r : VarRenaming) :
    ∀ es : List OSLFCore.Atom, listDepth (es.map (applyAtomTotal r)) = listDepth es
  | [] => by simp [listDepth]
  | e :: es => by
      simp [listDepth, atomDepth_applyAtomTotal_eq r e, listDepth_applyAtomTotal_eq r es]

end

/-- Packaged restricted bridge for the honest no-chain fragment: if a runtime
item already instantiates a key-renamed HE witness and the renamed matcher
values are fixed by the key renaming, then that same runtime item is already a
visible successor for the original HE witness up to α-equivalence. This keeps
the later repaired transport theorem honest: the remaining work is precisely to
construct the key-renamed runtime witness and prove the value-fix side
condition on the repaired visible-avoid surface. -/
theorem visible_successor_of_keyRenamed_instantiated_item
    {rhs : OSLFCore.Atom} {qb qb' : Bindings} {fuel : Nat} {prev : Metta.Minimal.Stack}
    {items : List Metta.Minimal.Item}
    (r : VarRenaming) (hr : r.Injective)
    (hrel : BindingsKeysRenamedBy r qb qb')
    (hno : NoVarAssignmentValues qb)
    (hno' : NoVarAssignmentValues qb')
    (hkeys' : AssignmentsNodup qb')
    (hfix : ∀ {v val}, qb.lookup v = some val → applyAtomTotal r val = val)
    (hdepthRenamed : atomDepth (applyAtomTotal r rhs) + 2 ≤ fuel)
    (hitem :
      Metta.Minimal.evalResult prev
          (Metta.instantiate (toLeaTTaMatchBindings qb') (toLeaTTaAtom (applyAtomTotal r rhs)))
          (toLeaTTaMatchBindings qb') ∈ items) :
    ∃ emitted m,
      Metta.Minimal.evalResult prev emitted m ∈ items ∧
      Metta.AlphaEq emitted (toLeaTTaAtom (qb.apply rhs fuel)) := by
  obtain ⟨emitted, m, hmem, halphaRenamed⟩ :=
    visible_successor_of_instantiated_item
      (rhs := applyAtomTotal r rhs) (qb := qb') (fuel := fuel)
      (prev := prev) (items := items)
      hno' hkeys' hdepthRenamed hitem
  have happly :
      qb'.apply (applyAtomTotal r rhs) fuel = applyAtomTotal r (qb.apply rhs fuel) :=
    applyAtomTotal_apply_of_bindingsKeysRenamedBy_noVar
      r hrel hno (a := rhs) (fuel := fuel) hfix
  have halphaApply :
      Metta.AlphaEq
        (toLeaTTaAtom (qb'.apply (applyAtomTotal r rhs) fuel))
        (toLeaTTaAtom (qb.apply rhs fuel)) := by
    rw [happly]
    exact alphaEq_toLeaTTaAtom_applyAtomTotal_of_injective r hr (qb.apply rhs fuel)
  refine ⟨emitted, m, hmem, ?_⟩
  unfold Metta.AlphaEq at halphaRenamed halphaApply ⊢
  exact halphaRenamed.trans halphaApply

/-- Same restricted bridge, but with the LeaTTa-side nodup and renamed-depth
facts discharged from an actual renamed successful match. This is the form the
next transport proof wants: once the renamed matcher witness has been built,
the remaining obligations are the semantic no-var and value-fix conditions,
not bookkeeping about duplicate keys or structural depth. -/
theorem visible_successor_of_keyRenamed_instantiated_item_of_match
    {lhs target rhs : OSLFCore.Atom}
    {qb qb' : Bindings} {fuel : Nat} {prev : Metta.Minimal.Stack}
    {items : List Metta.Minimal.Item}
    (r : VarRenaming) (hr : r.Injective)
    (hmatch' : simpleMatch (applyAtomTotal r lhs) target Bindings.empty fuel = some qb')
    (hrel : BindingsKeysRenamedBy r qb qb')
    (hno : NoVarAssignmentValues qb)
    (hno' : NoVarAssignmentValues qb')
    (hfix : ∀ {v val}, qb.lookup v = some val → applyAtomTotal r val = val)
    (hdepth : atomDepth rhs + 2 ≤ fuel)
    (hitem :
      Metta.Minimal.evalResult prev
          (Metta.instantiate (toLeaTTaMatchBindings qb') (toLeaTTaAtom (applyAtomTotal r rhs)))
          (toLeaTTaMatchBindings qb') ∈ items) :
    ∃ emitted m,
      Metta.Minimal.evalResult prev emitted m ∈ items ∧
      Metta.AlphaEq emitted (toLeaTTaAtom (qb.apply rhs fuel)) := by
  have hkeys' : AssignmentsNodup qb' :=
    simpleMatch_assignmentsNodup hmatch'
  have hdepthRenamed : atomDepth (applyAtomTotal r rhs) + 2 ≤ fuel := by
    simpa [atomDepth_applyAtomTotal_eq r rhs] using hdepth
  exact
    visible_successor_of_keyRenamed_instantiated_item
      (rhs := rhs) (qb := qb) (qb' := qb') (fuel := fuel)
      (prev := prev) (items := items)
      r hr hrel hno hno' hkeys' hfix hdepthRenamed hitem

private theorem applyAtomTotal_lookup_fixed_of_target_fixed_match
    (r : VarRenaming) (hr : r.Injective)
    {lhs target : OSLFCore.Atom} {qb : Bindings} {fuel : Nat}
    (htarget : applyAtomTotal r target = target)
    (hmatch : simpleMatch lhs target Bindings.empty fuel = some qb) :
    ∀ {v val}, qb.lookup v = some val → applyAtomTotal r val = val := by
  have hrel :=
    (simpleMatch_rename_bisim r hr fuel).1 lhs target
      Bindings.empty Bindings.empty (bindingsRenamedBy_empty r)
  have hmatchRenamed :
      simpleMatch lhs (applyAtomTotal r target) Bindings.empty fuel = some qb := by
    simpa [htarget] using hmatch
  rw [hmatch, hmatchRenamed] at hrel
  cases hrel with
  | some hrel =>
  intro v val hlookup
  have hlookup' := hrel.forward v val hlookup
  rw [hlookup] at hlookup'
  injection hlookup' with hEq
  exact hEq.symm

/-- Disjoint-name specialization of the restricted bridge: if the target atom
is literally fixed by the key renaming, then the matcher-value-fix condition is
automatic. This isolates a real sound fragment where the canonical-hub bridge
needs only the renamed witness, no-var hypotheses, and the two successful
matches. -/
theorem visible_successor_of_keyRenamed_instantiated_item_of_matches_targetFixed
    {lhs target rhs : OSLFCore.Atom}
    {qb qb' : Bindings} {fuel : Nat} {prev : Metta.Minimal.Stack}
    {items : List Metta.Minimal.Item}
    (r : VarRenaming) (hr : r.Injective)
    (htarget : applyAtomTotal r target = target)
    (hmatch : simpleMatch lhs target Bindings.empty fuel = some qb)
    (hmatch' : simpleMatch (applyAtomTotal r lhs) target Bindings.empty fuel = some qb')
    (hrel : BindingsKeysRenamedBy r qb qb')
    (hno : NoVarAssignmentValues qb)
    (hno' : NoVarAssignmentValues qb')
    (hdepth : atomDepth rhs + 2 ≤ fuel)
    (hitem :
      Metta.Minimal.evalResult prev
          (Metta.instantiate (toLeaTTaMatchBindings qb') (toLeaTTaAtom (applyAtomTotal r rhs)))
          (toLeaTTaMatchBindings qb') ∈ items) :
    ∃ emitted m,
      Metta.Minimal.evalResult prev emitted m ∈ items ∧
      Metta.AlphaEq emitted (toLeaTTaAtom (qb.apply rhs fuel)) := by
  have hfix :
      ∀ {v val}, qb.lookup v = some val → applyAtomTotal r val = val :=
    applyAtomTotal_lookup_fixed_of_target_fixed_match r hr htarget hmatch
  exact
    visible_successor_of_keyRenamed_instantiated_item_of_match
      (lhs := lhs) (target := target) (rhs := rhs)
      (qb := qb) (qb' := qb') (fuel := fuel)
      (prev := prev) (items := items)
      r hr hmatch' hrel hno hno' hfix hdepth hitem

end Mettapedia.Languages.MeTTa.HE.CanonicalEquationBridge
