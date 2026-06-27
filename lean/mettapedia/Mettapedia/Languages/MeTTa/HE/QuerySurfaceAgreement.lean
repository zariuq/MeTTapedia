import Mettapedia.Languages.MeTTa.HE.Space
import Mettapedia.Languages.MeTTa.HE.SimpleMatch
import Mettapedia.Languages.MeTTa.HE.MatcherBridge
import Mettapedia.Languages.MeTTa.HE.DeclMatchSpec
import Mettapedia.Languages.MeTTa.HE.DeclMergeSpec

/-!
# G3 staged agreement for the HE equation-query surface

This file banks the **bounded** G3 theorem after the public query surface moved
from the legacy one-way matcher to the faithful `matchAtoms`/`mergeBindings`
basis.

The headline is deliberately scoped:

- On the **ground-query fragment**, every faithful public query result has
  **no equalities**.
- For any **fixed freshened equation pair** `(lhs', rhs')`, the legacy
  one-way matcher and the repaired `matchAtoms`/`mergeBindings` surface agree
  on the ground-query fragment, up to extra matcher fuel.

This makes the exact G3/G3b boundary explicit. Equality-threading only becomes
observable once the queried atom itself still contains variables; that core
`Bindings.resolve` / `Bindings.apply` repair is deferred to G3b on purpose.
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

mutual

/-- Structural depth bound needed only for the local fuel-stability lemmas in
`QuerySurfaceAgreement`; kept local so bounded G3 does not depend on the
LeaTTa bridge layer. -/
private def atomDepth : Atom → Nat
  | .symbol _ => 0
  | .var _ => 0
  | .grounded _ => 0
  | .expression es => listDepth es + 1

private def listDepth : List Atom → Nat
  | [] => 0
  | a :: as => max (atomDepth a) (listDepth as)

end

private theorem collectVars_stable_of_depth :
    ∀ fuel fuel' (a : Atom),
      atomDepth a + 1 ≤ fuel →
      atomDepth a + 1 ≤ fuel' →
      collectVars a fuel = collectVars a fuel' := by
  intro fuel
  induction fuel with
  | zero =>
      intro fuel' a hdepth _
      omega
  | succ fuel ih =>
      intro fuel' a hdepth hdepth'
      cases fuel' with
      | zero =>
          omega
      | succ fuel' =>
          cases a with
          | symbol s =>
              simp [collectVars]
          | var v =>
              simp [collectVars]
          | grounded g =>
              simp [collectVars]
          | expression es =>
              have hlist :
                  ∀ es : List Atom, listDepth es + 1 ≤ fuel →
                    listDepth es + 1 ≤ fuel' →
                    collectVars.collectVarsList es fuel =
                      collectVars.collectVarsList es fuel' := by
                intro es
                induction es with
                | nil =>
                    intro _ _
                    simp [collectVars.collectVarsList]
                | cons e es ihEs =>
                    intro hes hes'
                    simp [collectVars.collectVarsList, listDepth] at hes hes' ⊢
                    have hhead : atomDepth e + 1 ≤ fuel := by
                      omega
                    have hhead' : atomDepth e + 1 ≤ fuel' := by
                      omega
                    have htail : listDepth es + 1 ≤ fuel := by
                      omega
                    have htail' : listDepth es + 1 ≤ fuel' := by
                      omega
                    rw [ih fuel' e hhead hhead', ihEs htail htail']
              have hes : listDepth es + 1 ≤ fuel := by
                simp [atomDepth] at hdepth
                omega
              have hes' : listDepth es + 1 ≤ fuel' := by
                simp [atomDepth] at hdepth'
                omega
              simp [collectVars, hlist es hes hes']

private theorem renameVars_stable_of_depth (mapping : List (String × String)) :
    ∀ fuel fuel' (a : Atom),
      atomDepth a + 1 ≤ fuel →
      atomDepth a + 1 ≤ fuel' →
      renameVars mapping a fuel = renameVars mapping a fuel' := by
  intro fuel
  induction fuel with
  | zero =>
      intro fuel' a hdepth _
      omega
  | succ fuel ih =>
      intro fuel' a hdepth hdepth'
      cases fuel' with
      | zero =>
          omega
      | succ fuel' =>
          cases a with
          | symbol s =>
              simp [renameVars]
          | var v =>
              simp [renameVars]
          | grounded g =>
              simp [renameVars]
          | expression es =>
              have hlist :
                  ∀ es : List Atom, listDepth es + 1 ≤ fuel →
                    listDepth es + 1 ≤ fuel' →
                    renameVars.renameVarsList mapping es fuel =
                      renameVars.renameVarsList mapping es fuel' := by
                intro es
                induction es with
                | nil =>
                    intro _ _
                    simp [renameVars.renameVarsList]
                | cons e es ihEs =>
                    intro hes hes'
                    simp [renameVars.renameVarsList, listDepth] at hes hes' ⊢
                    have hhead : atomDepth e + 1 ≤ fuel := by
                      omega
                    have hhead' : atomDepth e + 1 ≤ fuel' := by
                      omega
                    have htail : listDepth es + 1 ≤ fuel := by
                      omega
                    have htail' : listDepth es + 1 ≤ fuel' := by
                      omega
                    constructor
                    · exact ih fuel' e hhead hhead'
                    · exact ihEs htail htail'
              have hes : listDepth es + 1 ≤ fuel := by
                simp [atomDepth] at hdepth
                omega
              have hes' : listDepth es + 1 ≤ fuel' := by
                simp [atomDepth] at hdepth'
                omega
              simpa [renameVars] using congrArg Atom.expression (hlist es hes hes')

private theorem collectVars_ground_nil :
    ∀ {a : Atom}, GroundAtom a → ∀ fuel, collectVars a fuel = [] := by
  intro a hground
  induction hground with
  | symbol s =>
      intro fuel
      cases fuel <;> simp [collectVars]
  | grounded g =>
      intro fuel
      cases fuel <;> simp [collectVars]
  | @expression es hElems ih =>
      intro fuel
      cases fuel with
      | zero =>
          simp [collectVars]
      | succ n =>
          have hlist :
              ∀ es : List Atom, (∀ e ∈ es, collectVars e n = []) →
                collectVars.collectVarsList es n = [] := by
            intro es
            induction es with
            | nil =>
                intro _
                simp [collectVars.collectVarsList]
            | cons e es ihEs =>
                intro hEs
                have hhead : collectVars e n = [] := hEs e (by simp)
                have htail : ∀ e' ∈ es, collectVars e' n = [] := by
                  intro e' he'
                  exact hEs e' (by simp [he'])
                simp [collectVars.collectVarsList, hhead, ihEs htail]
          have hElemsNil : ∀ e ∈ es, collectVars e n = [] := by
            intro e he
            exact ih e he n
          simp [collectVars, hlist _ hElemsNil]

private theorem freshenEquation_stable_of_depth
    (idx : Nat) (lhs rhs : Atom) (fuel fuel' : Nat)
    (hdepthL : atomDepth lhs + 1 ≤ fuel)
    (hdepthL' : atomDepth lhs + 1 ≤ fuel')
    (hdepthR : atomDepth rhs + 1 ≤ fuel)
    (hdepthR' : atomDepth rhs + 1 ≤ fuel') :
    freshenEquation idx lhs rhs fuel = freshenEquation idx lhs rhs fuel' := by
  have hvarsL := collectVars_stable_of_depth fuel fuel' lhs hdepthL hdepthL'
  have hvarsR := collectVars_stable_of_depth fuel fuel' rhs hdepthR hdepthR'
  have hvars :
      (collectVars lhs fuel ++ collectVars rhs fuel).eraseDups =
        (collectVars lhs fuel' ++ collectVars rhs fuel').eraseDups := by
    rw [hvarsL, hvarsR]
  simp [freshenEquation, hvars,
    renameVars_stable_of_depth
      ((freshMapping idx ((collectVars lhs fuel' ++ collectVars rhs fuel').eraseDups)).1)
      fuel fuel' lhs hdepthL hdepthL',
    renameVars_stable_of_depth
      ((freshMapping idx ((collectVars lhs fuel' ++ collectVars rhs fuel').eraseDups)).1)
      fuel fuel' rhs hdepthR hdepthR']

private theorem freshenEquationAgainst_stable_of_depth
    (avoid : List String) (idx : Nat) (lhs rhs : Atom) (fuel fuel' : Nat)
    (hdepthL : atomDepth lhs + 1 ≤ fuel)
    (hdepthL' : atomDepth lhs + 1 ≤ fuel')
    (hdepthR : atomDepth rhs + 1 ≤ fuel)
    (hdepthR' : atomDepth rhs + 1 ≤ fuel') :
    freshenEquationAgainst avoid idx lhs rhs fuel =
      freshenEquationAgainst avoid idx lhs rhs fuel' := by
  have hvarsL := collectVars_stable_of_depth fuel fuel' lhs hdepthL hdepthL'
  have hvarsR := collectVars_stable_of_depth fuel fuel' rhs hdepthR hdepthR'
  have hvars :
      (collectVars lhs fuel ++ collectVars rhs fuel).eraseDups =
        (collectVars lhs fuel' ++ collectVars rhs fuel').eraseDups := by
    rw [hvarsL, hvarsR]
  simp [freshenEquationAgainst, hvars,
    renameVars_stable_of_depth
      ((freshMappingAgainst idx avoid
        ((collectVars lhs fuel' ++ collectVars rhs fuel').eraseDups)).1)
      fuel fuel' lhs hdepthL hdepthL',
    renameVars_stable_of_depth
      ((freshMappingAgainst idx avoid
        ((collectVars lhs fuel' ++ collectVars rhs fuel').eraseDups)).1)
      fuel fuel' rhs hdepthR hdepthR']

/-- The historical equation-query helper, kept here only as a proof-model for
the staged G3 comparison theorem. The live runtime surface is `queryEquations`
in `Space.lean`; this legacy helper should not be reintroduced downstream. -/
private def queryEquationsLegacyModel
    (space : Space) (atom : Atom) (fuel : Nat := 100) :
    List (Atom × Bindings) :=
  space.atoms.zipIdx.filterMap fun (eq, idx) =>
    match eq with
    | .expression [.symbol "=", lhs, rhs] =>
      let (lhs', rhs') := freshenEquation idx lhs rhs fuel
      match simpleMatch lhs' atom Bindings.empty fuel with
      | some b => some (rhs', b)
      | none => none
    | _ => none

/-- Visible-avoid legacy query helper, again only for the staged G3 theorem. -/
private def queryEquationsAgainstVisibleLegacyModel
    (space : Space) (atom : Atom) (fuel : Nat := 100) :
    List (Atom × Bindings) :=
  let avoid := (collectVars atom fuel).eraseDups
  space.atoms.zipIdx.filterMap fun (eq, idx) =>
    match eq with
    | .expression [.symbol "=", lhs, rhs] =>
      let (lhs', rhs') := freshenEquationAgainst avoid idx lhs rhs fuel
      match simpleMatch lhs' atom Bindings.empty fuel with
      | some b => some (rhs', b)
      | none => none
    | _ => none

/-- Local empty-right merge simplification used by the staged G3 witnesses. -/
private theorem mergeBindings_empty_right_local (b : Bindings) (n : Nat) :
    mergeBindings b Bindings.empty (n + 1) = [b] := by
  simp [mergeBindings, Bindings.empty]

/-- Legacy one-way query on an already-freshened equation pair. This isolates
the matcher migration from the separate fuel-sensitive freshening wrapper in
`queryEquations`. -/
private def queryFreshenedLegacyModel
    (lhs rhs atom : Atom) (fuel : Nat) : List (Atom × Bindings) :=
  match simpleMatch lhs atom Bindings.empty fuel with
  | some b => [(rhs, b)]
  | none => []

/-- Faithful query on an already-freshened equation pair. This is the repaired
`matchAtoms`/`mergeBindings` surface with the outer space scan and freshening
step factored away, so the bounded G3 theorem can focus on the matcher change
itself. -/
private def queryFreshenedFaithfulModel
    (lhs rhs atom : Atom) (fuel : Nat) : List (Atom × Bindings) :=
  (matchAtoms atom lhs fuel).flatMap fun qb =>
    (mergeBindings qb Bindings.empty fuel).filterMap fun merged =>
      if merged.hasLoop then none else some (rhs, merged)

private theorem queryFreshenedFaithful_mono
    {lhs rhs atom : Atom} {fuel extra : Nat} {out : Atom × Bindings}
    (hmem : out ∈ queryFreshenedFaithfulModel lhs rhs atom fuel) :
    out ∈ queryFreshenedFaithfulModel lhs rhs atom (fuel + extra) := by
  rcases out with ⟨outAtom, outB⟩
  rcases List.mem_flatMap.mp hmem with ⟨mb, hmb, hfilter⟩
  simp at hfilter
  rcases hfilter with ⟨hmerge, hout⟩
  refine List.mem_flatMap.mpr ?_
  refine ⟨mb, DeclMatchSpec.matchAtoms_mono atom lhs fuel extra hmb, ?_⟩
  have hmerge' : outB ∈ mergeBindings mb Bindings.empty (fuel + extra) :=
    DeclMatchSpec.mergeBindings_mono mb Bindings.empty fuel extra hmerge
  simp [hmerge', hout]

/-- `matchAtomsList` decomposes a seed accumulator into singleton-seeded runs.
This local copy keeps the bounded G3 converse independent of the larger
MatcherBridge private scaffolding. -/
private theorem matchAtomsList_seedwise_local
    (lefts rights : List Atom) (seeds : List Bindings) (fuel : Nat) :
    matchAtomsList lefts rights seeds fuel =
      seeds.flatMap (fun b => matchAtomsList lefts rights [b] fuel) := by
  induction fuel generalizing lefts rights seeds with
  | zero =>
      simp [matchAtomsList]
  | succ n ih =>
      cases lefts <;> cases rights
      · simp [matchAtomsList]
      · simp [matchAtomsList]
      · simp [matchAtomsList]
      · rename_i l ls r rs
        calc
          matchAtomsList (l :: ls) (r :: rs) seeds (n + 1)
              = matchAtomsList ls rs
                  (seeds.flatMap fun a => (matchAtoms l r n).flatMap fun b => mergeBindings a b n) n := by
                    simp [matchAtomsList]
          _ = (seeds.flatMap fun a => (matchAtoms l r n).flatMap fun b => mergeBindings a b n).flatMap
                (fun b => matchAtomsList ls rs [b] n) := by
                    rw [ih ls rs
                      (seeds.flatMap fun a => (matchAtoms l r n).flatMap fun b => mergeBindings a b n)]
          _ = seeds.flatMap
                (fun b =>
                  ((matchAtoms l r n).flatMap fun b1 => mergeBindings b b1 n).flatMap
                    (fun b2 => matchAtomsList ls rs [b2] n)) := by
                    simp [List.flatMap_assoc]
          _ = seeds.flatMap
                (fun b => matchAtomsList ls rs (List.flatMap (fun b_1 => mergeBindings b b_1 n) (matchAtoms l r n)) n) := by
                    induction seeds with
                    | nil =>
                        rfl
                    | cons b bs ihSeeds =>
                        simp [ih ls rs
                          ((matchAtoms l r n).flatMap fun b1 => mergeBindings b b1 n), ihSeeds]
          _ = seeds.flatMap (fun b => matchAtomsList (l :: ls) (r :: rs) [b] (n + 1)) := by
                    simp [matchAtomsList]

private theorem mem_matchAtomsList_seedwise_local
    {lefts rights : List Atom} {seeds : List Bindings}
    {fuel : Nat} {x : Bindings} :
    x ∈ matchAtomsList lefts rights seeds fuel ↔
      ∃ b ∈ seeds, x ∈ matchAtomsList lefts rights [b] fuel := by
  rw [matchAtomsList_seedwise_local lefts rights seeds fuel]
  simp

/-- `matchAtomsList` distributes over a `flatMap`-built accumulator. This
local copy lets the bounded G3 converse decompose seeded official list runs
without depending on MatcherBridge's private scaffolding. -/
private theorem matchAtomsList_flatMap_acc_local
    {α : Type} (lefts rights : List Atom) (acc : List α)
    (f : α → List Bindings) (fuel : Nat) :
    matchAtomsList lefts rights (acc.flatMap f) fuel =
      acc.flatMap (fun a => matchAtomsList lefts rights (f a) fuel) := by
  induction fuel generalizing lefts rights acc f with
  | zero =>
      simp [matchAtomsList]
  | succ n ih =>
      cases lefts with
      | nil =>
          cases rights with
          | nil =>
              simp [matchAtomsList]
          | cons right rights =>
              simp [matchAtomsList]
      | cons left lefts =>
          cases rights with
          | nil =>
              simp [matchAtomsList]
          | cons right rights =>
              simp only [matchAtomsList]
              rw [List.flatMap_assoc]
              simpa using
                ih lefts rights acc
                  (fun a =>
                    (f a).flatMap fun b =>
                      (matchAtoms left right n).flatMap fun mb =>
                        mergeBindings b mb n)

private theorem mem_matchAtomsList_flatMap_acc_local
    {α : Type} {lefts rights : List Atom} {acc : List α}
    {f : α → List Bindings} {fuel : Nat} {x : Bindings} :
    x ∈ matchAtomsList lefts rights (acc.flatMap f) fuel ↔
      ∃ a ∈ acc, x ∈ matchAtomsList lefts rights (f a) fuel := by
  rw [matchAtomsList_flatMap_acc_local lefts rights acc f fuel]
  simp

private theorem mergeRel_empty_right_eq
    {b out : Bindings}
    (h : DeclMergeSpec.MergeRel b Bindings.empty out) :
    out = b := by
  cases h with
  | mk hAssigns hEqs =>
      cases hAssigns with
      | nil =>
          cases hEqs with
          | nil =>
              rfl

private theorem mergeRel_single_assign_inv
    {seed out : Bindings} {v : String} {val : Atom}
    (h : DeclMergeSpec.MergeRel seed (Bindings.empty.assign v val) out) :
    DeclMergeSpec.AddVarBindingRel seed v val out := by
  cases h with
  | mk hAssigns hEqs =>
      cases hEqs with
      | nil =>
          cases hAssigns with
          | cons hHead hTail =>
              cases hTail with
              | nil =>
                  exact hHead

private theorem lookup_some_mem_assignments_local
    {xs : List (String × Atom)} {v : String} {a : Atom}
    (h : List.lookup v xs = some a) :
    (v, a) ∈ xs := by
  induction xs with
  | nil =>
      simp at h
  | cons x xs ih =>
      rcases x with ⟨k, b⟩
      by_cases hk : v == k
      · have hvk : v = k := by simpa using hk
        simp [List.lookup_cons, hk] at h
        subst hvk
        subst h
        simp
      · simp [List.lookup_cons, hk] at h
        simpa using Or.inr (ih h)

private theorem lookup_ground_local
    {b : Bindings} (hb : GroundBindings b)
    {v : String} {a : Atom} (h : b.lookup v = some a) :
    GroundAtom a := by
  exact hb.1 (v, a) (lookup_some_mem_assignments_local h)

private theorem mergeRel_ground_bindings_local
    {left right out : Bindings}
    (hleft : GroundBindings left)
    (hright : GroundBindings right)
    (h : DeclMergeSpec.MergeRel left right out) :
    GroundBindings out := by
  obtain ⟨fuel, hmem⟩ := DeclMergeSpec.mergeBindings_complete h
  rcases matcher_ground fuel with ⟨_, _, hmergeGround, _⟩
  exact hmergeGround left right out hleft hright hmem

private theorem matchAtoms_ground_ne_nil_local
    {left right : Atom} {n : Nat}
    (hleft : GroundAtom left)
    (hright : GroundAtom right)
    (hneq : left ≠ right) :
    matchAtoms left right (n + 1) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro result hmem
  obtain ⟨_, heq⟩ := matchAtoms_ground_rigid_exact hleft hright hmem
  exact hneq heq

private theorem seeded_var_head_ground_reifies_simpleMatch_exact
    {seed out : Bindings} {v : String} {target : Atom} {fuel : Nat}
    (hseed : GroundBindings seed)
    (htarget : GroundAtom target)
    (hmerge : out ∈ mergeBindings seed (Bindings.empty.assign v target) (fuel + 2)) :
    simpleMatch (.var v) target seed (fuel + 2) = some out := by
  cases hlook : seed.lookup v with
  | none =>
      have hout : out = seed.assign v target := by
        simpa [mergeBindings_single_assign_fresh hlook fuel] using hmerge
      subst hout
      simp [simpleMatch, hlook]
  | some prev =>
      have hprev : GroundAtom prev := lookup_ground_local hseed hlook
      by_cases heq : prev = target
      · have hout : out = seed := by
          simpa [mergeBindings_single_assign_same (heq.symm ▸ hlook) fuel] using hmerge
        subst hout
        simp [simpleMatch, hlook, heq]
      · have hsameFalse : ¬ (prev == target) := by
          intro hbeq
          apply heq
          simpa using hbeq
        have hmergeNil : mergeBindings seed (Bindings.empty.assign v target) (fuel + 2) = [] := by
          rw [mergeBindings_single_assign (b := seed) (v := v) (val := target) fuel]
          cases fuel with
          | zero =>
              simp [addVarBinding, hlook, hsameFalse, matchAtoms]
          | succ k =>
              have hmatchNil : matchAtoms prev target (k + 1) = [] :=
                matchAtoms_ground_ne_nil_local hprev htarget heq
              simp [addVarBinding, hlook, hsameFalse, hmatchNil]
        rw [hmergeNil] at hmerge
        simp at hmerge

private theorem addVarBindingRel_ground_reifies_simpleMatch
    {seed out : Bindings} {v : String} {val : Atom}
    (hseed : GroundBindings seed)
    (hval : GroundAtom val)
    (h : DeclMergeSpec.AddVarBindingRel seed v val out) :
    ∃ fuel, simpleMatch (.var v) val seed fuel = some out := by
  cases h with
  | unbound hnone =>
      refine ⟨1, ?_⟩
      simp [simpleMatch, hnone, Bindings.assign]
  | same hsame =>
      refine ⟨1, ?_⟩
      simp [simpleMatch, hsame]
  | @conflict _ _ _ prev mB out hlookup hneq hm hmerge =>
      have hprev : GroundAtom prev := lookup_ground_local hseed hlookup
      obtain ⟨fuelMatch, hmatch⟩ := DeclMatchSpec.matchAtoms_complete hm
      cases fuelMatch with
      | zero =>
          simp [matchAtoms] at hmatch
      | succ n =>
          have hrigid :=
            matchAtoms_ground_rigid_exact hprev hval hmatch
          rcases hrigid with ⟨_, hEq⟩
          exact False.elim (hneq hEq)

private theorem seeded_var_head_ground_reifies_simpleMatch
    {seed out : Bindings} {v : String} {target : Atom} {fuel : Nat}
    (hseed : GroundBindings seed)
    (htarget : GroundAtom target)
    (hmerge : out ∈ mergeBindings seed (Bindings.empty.assign v target) fuel) :
    ∃ fuel', simpleMatch (.var v) target seed fuel' = some out := by
  cases fuel with
  | zero =>
      simp [mergeBindings] at hmerge
  | succ fuel =>
      cases fuel with
      | zero =>
          have hnil : mergeBindings seed (Bindings.empty.assign v target) 1 = [] := by
            simp [mergeBindings, addVarBinding, Bindings.empty, Bindings.assign,
              Bindings.isBound, Bindings.lookup]
          rw [hnil] at hmerge
          simp at hmerge
      | succ n =>
          exact ⟨n + 2, seeded_var_head_ground_reifies_simpleMatch_exact hseed htarget hmerge⟩

private theorem seeded_ground_nonexpr_head_reifies_simpleMatch
    {pattern target : Atom} {seed mb out : Bindings} {fuel : Nat}
    (hseed : GroundBindings seed)
    (htarget : GroundAtom target)
    (h_nonexpr : ¬ ∃ ps, pattern = .expression ps)
    (hmb : mb ∈ matchAtoms target pattern fuel)
    (hmerge : out ∈ mergeBindings seed mb fuel) :
    ∃ fuel', simpleMatch pattern target seed fuel' = some out := by
  cases fuel with
  | zero =>
      simp [matchAtoms] at hmb
  | succ n =>
      cases pattern with
      | var v =>
          have hmbEq : mb = Bindings.empty.assign v target := by
            simpa [matchAtoms_ground_var_exact target v n htarget] using hmb
          subst hmbEq
          exact seeded_var_head_ground_reifies_simpleMatch hseed htarget hmerge
      | symbol s =>
          have hrigid :=
            matchAtoms_ground_rigid_exact htarget (GroundAtom.symbol s) hmb
          rcases hrigid with ⟨hmbEq, hEq⟩
          subst hEq
          have hmergeSound : DeclMergeSpec.MergeRel seed Bindings.empty out := by
            simpa [hmbEq] using DeclMergeSpec.mergeBindings_sound hmerge
          have hout : out = seed := mergeRel_empty_right_eq hmergeSound
          refine ⟨1, ?_⟩
          subst hout
          simp [simpleMatch]
      | grounded g =>
          have hrigid :=
            matchAtoms_ground_rigid_exact htarget (GroundAtom.grounded g) hmb
          rcases hrigid with ⟨hmbEq, hEq⟩
          subst hEq
          have hmergeSound : DeclMergeSpec.MergeRel seed Bindings.empty out := by
            simpa [hmbEq] using DeclMergeSpec.mergeBindings_sound hmerge
          have hout : out = seed := mergeRel_empty_right_eq hmergeSound
          refine ⟨1, ?_⟩
          subst hout
          simp [simpleMatch]
      | expression ps =>
          exact False.elim (h_nonexpr ⟨ps, rfl⟩)

private theorem seeded_ground_nonexpr_head_reifies_simpleMatch_exact
    {pattern target : Atom} {seed mb out : Bindings} {fuel : Nat}
    (hseed : GroundBindings seed)
    (htarget : GroundAtom target)
    (h_nonexpr : ¬ ∃ ps, pattern = .expression ps)
    (hmb : mb ∈ matchAtoms target pattern fuel)
    (hmerge : out ∈ mergeBindings seed mb fuel) :
    simpleMatch pattern target seed fuel = some out := by
  cases fuel with
  | zero =>
      simp [matchAtoms] at hmb
  | succ n =>
      cases pattern with
      | var v =>
          have hmbEq : mb = Bindings.empty.assign v target := by
            simpa [matchAtoms_ground_var_exact target v n htarget] using hmb
          subst hmbEq
          cases n with
          | zero =>
              have hnil : mergeBindings seed (Bindings.empty.assign v target) 1 = [] := by
                simp [mergeBindings, addVarBinding, Bindings.empty, Bindings.assign,
                  Bindings.isBound, Bindings.lookup]
              rw [hnil] at hmerge
              simp at hmerge
          | succ k =>
              simpa using
                seeded_var_head_ground_reifies_simpleMatch_exact
                  (fuel := k) hseed htarget hmerge
      | symbol s =>
          have hrigid :=
            matchAtoms_ground_rigid_exact htarget (GroundAtom.symbol s) hmb
          rcases hrigid with ⟨hmbEq, hEq⟩
          subst hEq
          have hmergeSound : DeclMergeSpec.MergeRel seed Bindings.empty out := by
            simpa [hmbEq] using DeclMergeSpec.mergeBindings_sound hmerge
          have hout : out = seed := mergeRel_empty_right_eq hmergeSound
          subst hout
          simp [simpleMatch]
      | grounded g =>
          have hrigid :=
            matchAtoms_ground_rigid_exact htarget (GroundAtom.grounded g) hmb
          rcases hrigid with ⟨hmbEq, hEq⟩
          subst hEq
          have hmergeSound : DeclMergeSpec.MergeRel seed Bindings.empty out := by
            simpa [hmbEq] using DeclMergeSpec.mergeBindings_sound hmerge
          have hout : out = seed := mergeRel_empty_right_eq hmergeSound
          subst hout
          simp [simpleMatch]
      | expression ps =>
          exact False.elim (h_nonexpr ⟨ps, rfl⟩)

/-- Local fuel monotonicity copy for successful `simpleMatch` / `simpleMatchList`
runs. This is the small synchronization shim the flat-expression replay uses
to bring head and tail witnesses to one common legacy fuel. -/
private theorem simpleMatch_mono_succ_local (fuel : Nat) :
    (∀ pattern target b qb,
      simpleMatch pattern target b fuel = some qb →
      simpleMatch pattern target b (fuel + 1) = some qb) ∧
    (∀ ps ts b qb,
      simpleMatch.simpleMatchList ps ts b fuel = some qb →
      simpleMatch.simpleMatchList ps ts b (fuel + 1) = some qb) := by
  induction fuel with
  | zero =>
      refine ⟨?_, ?_⟩
      · intro pattern target b qb h
        simp [simpleMatch] at h
      · intro ps ts b qb h
        cases ps <;> cases ts <;>
          simp [simpleMatch.simpleMatchList, simpleMatch] at h ⊢
        · simpa [simpleMatch.simpleMatchList] using h
  | succ n ih =>
      obtain ⟨ihAtom, ihList⟩ := ih
      have hAtomSucc :
          ∀ pattern target b qb,
            simpleMatch pattern target b (n + 1) = some qb →
            simpleMatch pattern target b (n + 2) = some qb := by
        intro pattern target b qb h
        cases pattern with
        | var v =>
            cases hlook : b.lookup v <;>
              simpa [simpleMatch, hlook] using h
        | symbol s =>
            cases target <;> simp [simpleMatch] at h
            · simp [simpleMatch] at h ⊢
              exact h
        | grounded g =>
            cases target <;> simp [simpleMatch] at h
            · simp [simpleMatch] at h ⊢
              exact h
        | expression ps =>
            cases target with
            | var v =>
                simp [simpleMatch] at h
            | symbol s =>
                simp [simpleMatch] at h
            | grounded g =>
                simp [simpleMatch] at h
            | expression ts =>
                cases hneq : (ps.length != ts.length) with
                | true =>
                    simp [simpleMatch, hneq] at h
                | false =>
                    simp [simpleMatch, hneq] at h ⊢
                    exact ihList ps ts b qb h
      have hListSucc :
          ∀ ps ts b qb,
            simpleMatch.simpleMatchList ps ts b (n + 1) = some qb →
            simpleMatch.simpleMatchList ps ts b (n + 2) = some qb := by
        intro ps
        induction ps with
        | nil =>
            intro ts b qb h
            cases ts <;> simp [simpleMatch.simpleMatchList] at h ⊢
            · simpa [simpleMatch.simpleMatchList] using h
        | cons p ps ihps =>
            intro ts b qb h
            cases ts with
            | nil =>
                simp [simpleMatch.simpleMatchList] at h
            | cons t ts =>
                unfold simpleMatch.simpleMatchList at h ⊢
                cases hhd : simpleMatch p t b (n + 1) with
                | none =>
                    simp [hhd] at h
                | some b' =>
                    simp [hhd] at h
                    have hhd' : simpleMatch p t b (n + 2) = some b' :=
                      hAtomSucc p t b b' hhd
                    have htail' : simpleMatch.simpleMatchList ps ts b' (n + 2) = some qb :=
                      ihps ts b' qb h
                    simp [hhd', htail']
      exact ⟨hAtomSucc, hListSucc⟩

private theorem simpleMatch_mono_add_local (fuel extra : Nat) :
    (∀ pattern target b qb,
      simpleMatch pattern target b fuel = some qb →
      simpleMatch pattern target b (fuel + extra) = some qb) ∧
    (∀ ps ts b qb,
      simpleMatch.simpleMatchList ps ts b fuel = some qb →
      simpleMatch.simpleMatchList ps ts b (fuel + extra) = some qb) := by
  induction extra with
  | zero =>
      refine ⟨?_, ?_⟩
      · intro pattern target b qb h
        simpa using h
      · intro ps ts b qb h
        simpa using h
  | succ extra ih =>
      obtain ⟨ihAtom, ihList⟩ := ih
      obtain ⟨hSuccAtom, hSuccList⟩ := simpleMatch_mono_succ_local (fuel + extra)
      refine ⟨?_, ?_⟩
      · intro pattern target b qb h
        exact hSuccAtom pattern target b qb (ihAtom pattern target b qb h)
      · intro ps ts b qb h
        exact hSuccList ps ts b qb (ihList ps ts b qb h)

private theorem queryFreshenedLegacy_mono
    {lhs rhs atom : Atom} {fuel extra : Nat} {out : Atom × Bindings}
    (hmem : out ∈ queryFreshenedLegacyModel lhs rhs atom fuel) :
    out ∈ queryFreshenedLegacyModel lhs rhs atom (fuel + extra) := by
  rcases out with ⟨outAtom, outB⟩
  simp [queryFreshenedLegacyModel] at hmem ⊢
  cases hsm : simpleMatch lhs atom Bindings.empty fuel with
  | none =>
      simp [hsm] at hmem
  | some qb =>
      have hout : (outAtom, outB) = (rhs, qb) := by
        simpa [hsm] using hmem
      have hsm' :
          simpleMatch lhs atom Bindings.empty (fuel + extra) = some qb :=
        (simpleMatch_mono_add_local fuel extra).1 lhs atom Bindings.empty qb hsm
      simp [hsm', hout]

private theorem matchAtomsList_ground_seeded_reifies_simpleMatchList_nonexpr :
    ∀ fuel,
      ∀ {ps ts : List Atom} {seed qb : Bindings},
        GroundBindings seed →
        (∀ t ∈ ts, GroundAtom t) →
        (∀ p ∈ ps, ¬ ∃ es, p = .expression es) →
        qb ∈ matchAtomsList ts ps [seed] fuel →
        ∃ fuel', simpleMatch.simpleMatchList ps ts seed fuel' = some qb := by
  intro fuel
  induction fuel with
  | zero =>
      intro ps ts seed qb hseed hts hps hmem
      simp [matchAtomsList] at hmem
  | succ n ih =>
      intro ps ts seed qb hseed hts hps hmem
      cases ps with
      | nil =>
          cases ts with
          | nil =>
              have hqb : qb = seed := by
                simpa [matchAtomsList] using hmem
              subst hqb
              refine ⟨1, ?_⟩
              simp [simpleMatch.simpleMatchList]
          | cons t ts =>
              simp [matchAtomsList] at hmem
      | cons p ps =>
          cases ts with
          | nil =>
              simp [matchAtomsList] at hmem
          | cons t ts =>
              have ht : GroundAtom t := hts t (by simp)
              have hseededTail :
                  qb ∈ matchAtomsList ts ps
                    ((matchAtoms t p n).flatMap fun mb => mergeBindings seed mb n) n := by
                simpa [matchAtomsList] using hmem
              obtain ⟨mb, hmb, htailAcc⟩ :=
                (mem_matchAtomsList_flatMap_acc_local
                  (lefts := ts) (rights := ps)
                  (acc := matchAtoms t p n)
                  (f := fun mb => mergeBindings seed mb n)
                  (fuel := n) (x := qb)).mp hseededTail
              obtain ⟨b', hb', htail⟩ :=
                (mem_matchAtomsList_seedwise_local
                  (lefts := ts) (rights := ps)
                  (seeds := mergeBindings seed mb n)
                  (fuel := n) (x := qb)).mp htailAcc
              have hp_nonexpr : ¬ ∃ es, p = .expression es := hps p (by simp)
              obtain ⟨fuelHead, hheadLegacy⟩ :=
                seeded_ground_nonexpr_head_reifies_simpleMatch
                  hseed ht hp_nonexpr hmb hb'
              have hmbGround : GroundBindings mb :=
                matchAtoms_ground_bindings ht hmb
              have hb'Sound :
                  DeclMergeSpec.MergeRel seed mb b' :=
                DeclMergeSpec.mergeBindings_sound hb'
              have hb'Ground : GroundBindings b' :=
                mergeRel_ground_bindings_local hseed hmbGround hb'Sound
              have hts' : ∀ u ∈ ts, GroundAtom u := by
                intro u hu
                exact hts u (by simp [hu])
              have hps' : ∀ q ∈ ps, ¬ ∃ es, q = .expression es := by
                intro q hq
                exact hps q (by simp [hq])
              have hrec :=
                ih (ps := ps) (ts := ts) (seed := b') (qb := qb)
                  hb'Ground hts' hps' htail
              rcases hrec with ⟨fuelTail, htailLegacy⟩
              let fuel' := max fuelHead fuelTail
              have hHeadLe : fuelHead ≤ fuel' := by
                dsimp [fuel']
                exact Nat.le_max_left _ _
              have hTailLe : fuelTail ≤ fuel' := by
                dsimp [fuel']
                exact Nat.le_max_right _ _
              have hheadLegacy' :
                  simpleMatch p t seed fuel' = some b' := by
                have hEq : fuelHead + (fuel' - fuelHead) = fuel' :=
                  Nat.add_sub_of_le hHeadLe
                simpa [hEq] using
                  (simpleMatch_mono_add_local fuelHead (fuel' - fuelHead)).1
                    p t seed b' hheadLegacy
              have htailLegacy' :
                  simpleMatch.simpleMatchList ps ts b' fuel' = some qb := by
                have hEq : fuelTail + (fuel' - fuelTail) = fuel' :=
                  Nat.add_sub_of_le hTailLe
                simpa [hEq] using
                  (simpleMatch_mono_add_local fuelTail (fuel' - fuelTail)).2
                    ps ts b' qb htailLegacy
              refine ⟨fuel', ?_⟩
              unfold simpleMatch.simpleMatchList
              simp [hheadLegacy', htailLegacy']

/-- Membership-aware seeded ground replay factorization: if every official
head-step whose pattern occurs in the current pattern list can be replayed into
the legacy seeded matcher, then the whole official seeded list run can be
replayed too. This is the local tool the nested-expression head replay uses to
recurse only on strict subpatterns of the current expression. -/
private theorem matchAtomsList_ground_seeded_reifies_simpleMatchList_of_head_replay_mem
    :
    ∀ fuel,
      ∀ {ps ts : List Atom} {seed qb : Bindings},
        GroundBindings seed →
        (∀ t ∈ ts, GroundAtom t) →
        (∀ {pattern target : Atom} {seed mb out : Bindings} {fuel : Nat},
          pattern ∈ ps →
          GroundBindings seed →
          GroundAtom target →
          mb ∈ matchAtoms target pattern fuel →
          out ∈ mergeBindings seed mb fuel →
          ∃ fuel', simpleMatch pattern target seed fuel' = some out) →
        qb ∈ matchAtomsList ts ps [seed] fuel →
        ∃ fuel', simpleMatch.simpleMatchList ps ts seed fuel' = some qb := by
  intro fuel
  induction fuel with
  | zero =>
      intro ps ts seed qb hseed hts hHead hmem
      simp [matchAtomsList] at hmem
  | succ n ih =>
      intro ps ts seed qb hseed hts hHead hmem
      cases ps with
      | nil =>
          cases ts with
          | nil =>
              have hqb : qb = seed := by
                simpa [matchAtomsList] using hmem
              subst hqb
              refine ⟨1, ?_⟩
              simp [simpleMatch.simpleMatchList]
          | cons t ts =>
              simp [matchAtomsList] at hmem
      | cons p ps =>
          cases ts with
          | nil =>
              simp [matchAtomsList] at hmem
          | cons t ts =>
              have ht : GroundAtom t := hts t (by simp)
              have hseededTail :
                  qb ∈ matchAtomsList ts ps
                    ((matchAtoms t p n).flatMap fun mb => mergeBindings seed mb n) n := by
                simpa [matchAtomsList] using hmem
              obtain ⟨mb, hmb, htailAcc⟩ :=
                (mem_matchAtomsList_flatMap_acc_local
                  (lefts := ts) (rights := ps)
                  (acc := matchAtoms t p n)
                  (f := fun mb => mergeBindings seed mb n)
                  (fuel := n) (x := qb)).mp hseededTail
              obtain ⟨b', hb', htail⟩ :=
                (mem_matchAtomsList_seedwise_local
                  (lefts := ts) (rights := ps)
                  (seeds := mergeBindings seed mb n)
                  (fuel := n) (x := qb)).mp htailAcc
              obtain ⟨fuelHead, hheadLegacy⟩ :=
                hHead (by simp) hseed ht hmb hb'
              have hmbGround : GroundBindings mb :=
                matchAtoms_ground_bindings ht hmb
              have hb'Sound :
                  DeclMergeSpec.MergeRel seed mb b' :=
                DeclMergeSpec.mergeBindings_sound hb'
              have hb'Ground : GroundBindings b' :=
                mergeRel_ground_bindings_local hseed hmbGround hb'Sound
              have hts' : ∀ u ∈ ts, GroundAtom u := by
                intro u hu
                exact hts u (by simp [hu])
              have hHeadTail :
                  ∀ {pattern target : Atom} {seed mb out : Bindings} {fuel : Nat},
                    pattern ∈ ps →
                    GroundBindings seed →
                    GroundAtom target →
                    mb ∈ matchAtoms target pattern fuel →
                    out ∈ mergeBindings seed mb fuel →
                    ∃ fuel', simpleMatch pattern target seed fuel' = some out := by
                intro pattern target seed' mb' out' fuel' hmem' hseed' htarget' hmb' hmerge'
                exact hHead (by simp [hmem']) hseed' htarget' hmb' hmerge'
              have hrec :=
                ih (ps := ps) (ts := ts) (seed := b') (qb := qb)
                  hb'Ground hts' hHeadTail htail
              rcases hrec with ⟨fuelTail, htailLegacy⟩
              let fuel' := max fuelHead fuelTail
              have hHeadLe : fuelHead ≤ fuel' := by
                dsimp [fuel']
                exact Nat.le_max_left _ _
              have hTailLe : fuelTail ≤ fuel' := by
                dsimp [fuel']
                exact Nat.le_max_right _ _
              have hheadLegacy' :
                  simpleMatch p t seed fuel' = some b' := by
                have hEq : fuelHead + (fuel' - fuelHead) = fuel' :=
                  Nat.add_sub_of_le hHeadLe
                simpa [hEq] using
                  (simpleMatch_mono_add_local fuelHead (fuel' - fuelHead)).1
                    p t seed b' hheadLegacy
              have htailLegacy' :
                  simpleMatch.simpleMatchList ps ts b' fuel' = some qb := by
                have hEq : fuelTail + (fuel' - fuelTail) = fuel' :=
                  Nat.add_sub_of_le hTailLe
                simpa [hEq] using
                  (simpleMatch_mono_add_local fuelTail (fuel' - fuelTail)).2
                    ps ts b' qb htailLegacy
              refine ⟨fuel', ?_⟩
              unfold simpleMatch.simpleMatchList
              simp [hheadLegacy', htailLegacy']

private theorem matchAtomsList_ground_seeded_reifies_simpleMatchList_of_head_replay_mem_exact
    :
    ∀ fuel,
      ∀ {ps ts : List Atom} {seed qb : Bindings},
        GroundBindings seed →
        (∀ t ∈ ts, GroundAtom t) →
        (∀ {pattern target : Atom} {seed mb out : Bindings} {fuel : Nat},
          pattern ∈ ps →
          GroundBindings seed →
          GroundAtom target →
          mb ∈ matchAtoms target pattern fuel →
          out ∈ mergeBindings seed mb fuel →
          simpleMatch pattern target seed fuel = some out) →
        qb ∈ matchAtomsList ts ps [seed] fuel →
        simpleMatch.simpleMatchList ps ts seed fuel = some qb := by
  intro fuel
  induction fuel with
  | zero =>
      intro ps ts seed qb hseed hts hHead hmem
      simp [matchAtomsList] at hmem
  | succ n ih =>
      intro ps ts seed qb hseed hts hHead hmem
      cases ps with
      | nil =>
          cases ts with
          | nil =>
              have hqb : qb = seed := by
                simpa [matchAtomsList] using hmem
              subst hqb
              simp [simpleMatch.simpleMatchList]
          | cons t ts =>
              simp [matchAtomsList] at hmem
      | cons p ps =>
          cases ts with
          | nil =>
              simp [matchAtomsList] at hmem
          | cons t ts =>
              have ht : GroundAtom t := hts t (by simp)
              have hseededTail :
                  qb ∈ matchAtomsList ts ps
                    ((matchAtoms t p n).flatMap fun mb => mergeBindings seed mb n) n := by
                simpa [matchAtomsList] using hmem
              obtain ⟨mb, hmb, htailAcc⟩ :=
                (mem_matchAtomsList_flatMap_acc_local
                  (lefts := ts) (rights := ps)
                  (acc := matchAtoms t p n)
                  (f := fun mb => mergeBindings seed mb n)
                  (fuel := n) (x := qb)).mp hseededTail
              obtain ⟨b', hb', htail⟩ :=
                (mem_matchAtomsList_seedwise_local
                  (lefts := ts) (rights := ps)
                  (seeds := mergeBindings seed mb n)
                  (fuel := n) (x := qb)).mp htailAcc
              have hheadExact :
                  simpleMatch p t seed n = some b' :=
                hHead (by simp) hseed ht hmb hb'
              have hmbGround : GroundBindings mb :=
                matchAtoms_ground_bindings ht hmb
              have hb'Sound :
                  DeclMergeSpec.MergeRel seed mb b' :=
                DeclMergeSpec.mergeBindings_sound hb'
              have hb'Ground : GroundBindings b' :=
                mergeRel_ground_bindings_local hseed hmbGround hb'Sound
              have hts' : ∀ u ∈ ts, GroundAtom u := by
                intro u hu
                exact hts u (by simp [hu])
              have hHeadTail :
                  ∀ {pattern target : Atom} {seed mb out : Bindings} {fuel : Nat},
                    pattern ∈ ps →
                    GroundBindings seed →
                    GroundAtom target →
                    mb ∈ matchAtoms target pattern fuel →
                    out ∈ mergeBindings seed mb fuel →
                    simpleMatch pattern target seed fuel = some out := by
                intro pattern target seed' mb' out' fuel' hmem' hseed' htarget' hmb' hmerge'
                exact hHead (by simp [hmem']) hseed' htarget' hmb' hmerge'
              have htailExact :
                  simpleMatch.simpleMatchList ps ts b' n = some qb :=
                ih hb'Ground hts' hHeadTail htail
              have hheadExact' :
                  simpleMatch p t seed (n + 1) = some b' :=
                (simpleMatch_mono_succ_local n).1 p t seed b' hheadExact
              have htailExact' :
                  simpleMatch.simpleMatchList ps ts b' (n + 1) = some qb :=
                (simpleMatch_mono_succ_local n).2 ps ts b' qb htailExact
              simp [simpleMatch.simpleMatchList, hheadExact', htailExact']

/-- Higher-order ground replay factorization: if every official head-step on a
ground target can be replayed into the legacy seeded matcher, then the whole
official seeded list run can be replayed too. This isolates the remaining G3
crux to the head replay theorem for nested expression patterns. -/
private theorem matchAtomsList_ground_seeded_reifies_simpleMatchList_of_head_replay
    (hHead :
      ∀ {pattern target : Atom} {seed mb out : Bindings} {fuel : Nat},
        GroundBindings seed →
        GroundAtom target →
        mb ∈ matchAtoms target pattern fuel →
        out ∈ mergeBindings seed mb fuel →
        ∃ fuel', simpleMatch pattern target seed fuel' = some out) :
    ∀ fuel,
      ∀ {ps ts : List Atom} {seed qb : Bindings},
        GroundBindings seed →
        (∀ t ∈ ts, GroundAtom t) →
        qb ∈ matchAtomsList ts ps [seed] fuel →
        ∃ fuel', simpleMatch.simpleMatchList ps ts seed fuel' = some qb := by
  intro fuel ps ts seed qb hseed hts hmem
  exact
    matchAtomsList_ground_seeded_reifies_simpleMatchList_of_head_replay_mem
      fuel hseed hts
      (fun {pattern target seed mb out fuel} _ hseed' htarget hmb hmerge =>
        hHead hseed' htarget hmb hmerge)
      hmem

private theorem queryFreshened_ground_faithful_reifies_legacy_nonexpr_exact
    {lhs rhs atom : Atom} {qb : Bindings} {fuel : Nat}
    (hground : GroundAtom atom)
    (h_nonexpr : ¬ ∃ ps, lhs = .expression ps)
    (hmem : (rhs, qb) ∈ queryFreshenedFaithfulModel lhs rhs atom (fuel + 1)) :
    (rhs, qb) ∈ queryFreshenedLegacyModel lhs rhs atom (fuel + 1) := by
  rcases List.mem_flatMap.mp hmem with ⟨mb, hmb, hfilter⟩
  simp at hfilter
  rcases hfilter with ⟨hmerge, hrhs⟩
  have hmergeSound :
      DeclMergeSpec.MergeRel mb Bindings.empty qb :=
    DeclMergeSpec.mergeBindings_sound hmerge
  have hqb : qb = mb := mergeRel_empty_right_eq hmergeSound
  cases lhs with
  | var v =>
      have hExact :
          matchAtoms atom (.var v) (fuel + 1) =
            [Bindings.empty.assign v atom] :=
        matchAtoms_ground_var_exact atom v fuel hground
      have hmb' : mb = Bindings.empty.assign v atom := by
        simpa [hExact] using hmb
      have hqb' : qb = Bindings.empty.assign v atom := by
        simpa [hqb] using hmb'
      subst hqb'
      simp [queryFreshenedLegacyModel, simpleMatch, Bindings.empty,
        Bindings.lookup, Bindings.assign]
  | symbol s =>
      have hrigid :=
        matchAtoms_ground_rigid_exact hground (GroundAtom.symbol s) hmb
      rcases hrigid with ⟨hmbEq, hatomEq⟩
      have hqb' : qb = Bindings.empty := by
        simpa [hqb] using hmbEq
      subst hqb'
      subst hatomEq
      simp [queryFreshenedLegacyModel, simpleMatch]
  | grounded g =>
      have hrigid :=
        matchAtoms_ground_rigid_exact hground (GroundAtom.grounded g) hmb
      rcases hrigid with ⟨hmbEq, hatomEq⟩
      have hqb' : qb = Bindings.empty := by
        simpa [hqb] using hmbEq
      subst hqb'
      subst hatomEq
      simp [queryFreshenedLegacyModel, simpleMatch]
  | expression ps =>
      exact False.elim (h_nonexpr ⟨ps, rfl⟩)

private theorem queryFreshened_ground_faithful_reifies_legacy_nonexpr
    {lhs rhs atom : Atom} {qb : Bindings} {fuel : Nat}
    (hground : GroundAtom atom)
    (h_nonexpr : ¬ ∃ ps, lhs = .expression ps)
    (hmem : (rhs, qb) ∈ queryFreshenedFaithfulModel lhs rhs atom fuel) :
    ∃ fuel', (rhs, qb) ∈ queryFreshenedLegacyModel lhs rhs atom fuel' := by
  cases fuel with
  | zero =>
      simp [queryFreshenedFaithfulModel, matchAtoms] at hmem
  | succ n =>
      exact ⟨n + 1,
        queryFreshened_ground_faithful_reifies_legacy_nonexpr_exact
          hground h_nonexpr hmem⟩

/-- On a ground queried atom, the official matcher cannot produce equality
constraints. Equalities therefore arise in the query path only once the query
atom itself still carries variables. -/
theorem matchAtoms_equalities_nil_of_ground_query
    {atom lhs : Atom} {qb : Bindings} {fuel : Nat}
    (hground : GroundAtom atom)
    (hmem : qb ∈ matchAtoms atom lhs fuel) :
    qb.equalities = [] := by
  exact (matchAtoms_ground_bindings hground hmem).2

/-- The repaired public query surface inherits the same no-equalities property
on the ground-query fragment. This is the honest staged theorem that marks
where G3 stops and G3b begins. -/
theorem queryEquations_equalities_nil_of_ground_query
    {space : Space} {atom rhs : Atom} {qb : Bindings} {fuel : Nat}
    (hground : GroundAtom atom)
    (hmem : (rhs, qb) ∈ queryEquations space atom fuel) :
    qb.equalities = [] := by
  cases fuel with
  | zero =>
      simp [queryEquations] at hmem
  | succ n =>
      simp [queryEquations] at hmem
      rcases hmem with ⟨eq, idx, _hentry, hpair⟩
      cases eq with
      | symbol s =>
          simp at hpair
      | var v =>
          simp at hpair
      | grounded g =>
          simp at hpair
      | expression es =>
          cases es with
          | nil =>
              simp at hpair
          | cons hd tl =>
              cases hd with
              | symbol s =>
                  by_cases hs : s = "="
                  · subst hs
                    cases tl with
                    | nil =>
                        simp at hpair
                    | cons lhs tl2 =>
                        cases tl2 with
                        | nil =>
                            simp at hpair
                        | cons rhs tl3 =>
                            cases tl3 with
                            | nil =>
                                rcases List.mem_flatMap.mp hpair with ⟨mb, hmb, hfilter⟩
                                simp at hfilter
                                rcases hfilter with ⟨hmerged, _⟩
                                have hcanon : mb.equalities = [] :=
                                  matchAtoms_equalities_nil_of_ground_query hground hmb
                                have hmerge : qb = mb := by
                                  simpa [mergeBindings_empty_right_local mb n] using hmerged
                                simpa [hmerge] using hcanon
                            | cons extra rest =>
                                simp at hpair
                  · simp [hs] at hpair
              | var v =>
                  simp at hpair
              | grounded g =>
                  simp at hpair
              | expression inner =>
                  simp at hpair

/-- The visible-avoid surface has the same bounded no-equality property on
ground query atoms. -/
theorem queryEquationsAgainstVisible_equalities_nil_of_ground_query
    {space : Space} {atom rhs : Atom} {qb : Bindings} {fuel : Nat}
    (hground : GroundAtom atom)
    (hmem : (rhs, qb) ∈ queryEquationsAgainstVisible space atom fuel) :
    qb.equalities = [] := by
  cases fuel with
  | zero =>
      simp [queryEquationsAgainstVisible] at hmem
  | succ n =>
      simp [queryEquationsAgainstVisible] at hmem
      rcases hmem with ⟨eq, idx, _hentry, hpair⟩
      cases eq with
      | symbol s =>
          simp at hpair
      | var v =>
          simp at hpair
      | grounded g =>
          simp at hpair
      | expression es =>
          cases es with
          | nil =>
              simp at hpair
          | cons hd tl =>
              cases hd with
              | symbol s =>
                  by_cases hs : s = "="
                  · subst hs
                    cases tl with
                    | nil =>
                        simp at hpair
                    | cons lhs tl2 =>
                        cases tl2 with
                        | nil =>
                            simp at hpair
                        | cons rhs tl3 =>
                            cases tl3 with
                            | nil =>
                                rcases List.mem_flatMap.mp hpair with ⟨mb, hmb, hfilter⟩
                                simp at hfilter
                                rcases hfilter with ⟨hmerged, _⟩
                                have hcanon : mb.equalities = [] :=
                                  matchAtoms_equalities_nil_of_ground_query hground hmb
                                have hmerge : qb = mb := by
                                  simpa [mergeBindings_empty_right_local mb n] using hmerged
                                simpa [hmerge] using hcanon
                            | cons extra rest =>
                                simp at hpair
                  · simp [hs] at hpair
              | var v =>
                  simp at hpair
              | grounded g =>
                  simp at hpair
              | expression inner =>
                  simp at hpair

/-- On a ground queried atom, the fixed-freshening faithful matcher surface
cannot produce equality constraints either. This is the matcher-only companion
to the public `queryEquations_*_equalities_nil_*` theorem above. -/
theorem queryFreshenedFaithful_equalities_nil_of_ground_query
    {lhs rhs atom : Atom} {qb : Bindings} {fuel : Nat}
    (hground : GroundAtom atom)
    (hmem : (rhs, qb) ∈ queryFreshenedFaithfulModel lhs rhs atom fuel) :
    qb.equalities = [] := by
  cases fuel with
  | zero =>
      simp [queryFreshenedFaithfulModel, matchAtoms] at hmem
  | succ n =>
      rcases List.mem_flatMap.mp hmem with ⟨mb, hmb, hfilter⟩
      simp at hfilter
      rcases hfilter with ⟨hmerged, _⟩
      have hcanon : mb.equalities = [] :=
        matchAtoms_equalities_nil_of_ground_query hground hmb
      have hmerge : qb = mb := by
        simpa [mergeBindings_empty_right_local mb n] using hmerged
      simpa [hmerge] using hcanon

/-- Expression-case inversion for the fixed-freshening faithful surface on a
ground queried atom. Any such hit must come from a ground expression scrutinee
of matching arity, and after the trivial empty-right merge the reported
bindings are exactly the underlying empty-seeded official list-matcher result.

This is the precise remaining shape of the G3 converse: the open work is now a
replay theorem from this empty-seeded official list witness into the legacy
`simpleMatchList`, not any further analysis of equalities or the outer query
scan. -/
private theorem queryFreshenedFaithful_ground_expr_inv
    {ps : List Atom} {rhs atom : Atom} {qb : Bindings} {fuel : Nat}
    (hground : GroundAtom atom)
    (hmem : (rhs, qb) ∈ queryFreshenedFaithfulModel (.expression ps) rhs atom (fuel + 1)) :
    ∃ ts mb,
      atom = .expression ts ∧
      ts.length = ps.length ∧
      mb ∈ matchAtomsList ts ps [Bindings.empty] fuel ∧
      qb = mb := by
  rcases List.mem_flatMap.mp hmem with ⟨mb, hmb, hfilter⟩
  simp at hfilter
  rcases hfilter with ⟨hmerged, _⟩
  have hmergeSound :
      DeclMergeSpec.MergeRel mb Bindings.empty qb :=
    DeclMergeSpec.mergeBindings_sound hmerged
  have hqb : qb = mb := mergeRel_empty_right_eq hmergeSound
  cases atom with
  | var v =>
      exact False.elim (GroundAtom.not_var hground)
  | symbol s =>
      simp [matchAtoms, getMetaType,
        Atom.symbolType, Atom.expressionType] at hmb
  | grounded g =>
      simp [matchAtoms, getMetaType,
        Atom.groundedType, Atom.expressionType] at hmb
  | expression ts =>
      by_cases hlen : ts.length = ps.length
      · refine ⟨ts, mb, rfl, hlen, ?_, hqb⟩
        simp [matchAtoms, getMetaType, Atom.expressionType, hlen] at hmb
        exact hmb.1
      · simp [matchAtoms, getMetaType, Atom.expressionType, hlen] at hmb

/-- Head/tail inversion of the expression-case faithful surface on a ground
queried atom. This refines `queryFreshenedFaithful_ground_expr_inv` to the
exact recursive shape the remaining G3 converse must replay:

- a ground expression scrutinee `t :: ts`
- a head official match witness for `matchAtoms t p`
- a tail official seeded run from `[mbHead]`

No equalities or outer-query bookkeeping remain here; the sole remaining work is
to replay this official head/tail chain into the legacy `simpleMatch` /
`simpleMatchList` chain. -/
private theorem queryFreshenedFaithful_ground_expr_cons_inv
    {p : Atom} {ps : List Atom} {rhs atom : Atom} {qb : Bindings} {fuel : Nat}
    (hground : GroundAtom atom)
    (hmem :
      (rhs, qb) ∈
        queryFreshenedFaithfulModel (.expression (p :: ps)) rhs atom (fuel + 2)) :
    ∃ t ts mbHead,
      atom = .expression (t :: ts) ∧
      mbHead ∈ matchAtoms t p (fuel + 1) ∧
      qb ∈ matchAtomsList ts ps [mbHead] (fuel + 1) := by
  obtain ⟨items, qb0, hatom, hlen, hlist, hqb⟩ :=
    queryFreshenedFaithful_ground_expr_inv hground hmem
  subst hatom
  subst hqb
  cases items with
  | nil =>
      simp at hlen
  | cons t ts =>
      obtain ⟨mbHead, hhead0, htail0⟩ :=
        matchAtomsList_ground_empty_cons_inv
          (t := t) (p := p) (ts := ts) (ps := ps)
          (result := qb) (fuel := fuel)
          (GroundAtom.elem hground (by simp)) hlist
      have hhead :
          mbHead ∈ matchAtoms t p (fuel + 1) :=
        DeclMatchSpec.matchAtoms_mono t p fuel 1 hhead0
      have htail :
          qb ∈ matchAtomsList ts ps [mbHead] (fuel + 1) :=
        DeclMatchSpec.matchAtomsList_mono ts ps [mbHead] fuel 1 htail0
      exact ⟨t, ts, mbHead, rfl, hhead, htail⟩

/-- Single-element expression inversion on the ground fragment. This is the
one-step case of `queryFreshenedFaithful_ground_expr_cons_inv`: the queried
atom must itself be a singleton ground expression, and the reported bindings
are exactly the official head-match witness. -/
private theorem queryFreshenedFaithful_ground_expr_single_inv
    {p : Atom} {rhs atom : Atom} {qb : Bindings} {fuel : Nat}
    (hground : GroundAtom atom)
    (hmem :
      (rhs, qb) ∈
        queryFreshenedFaithfulModel (.expression [p]) rhs atom (fuel + 2)) :
    ∃ t mbHead,
      atom = .expression [t] ∧
      mbHead ∈ matchAtoms t p (fuel + 1) ∧
      qb = mbHead := by
  obtain ⟨t, ts, mbHead, hatom, hhead, htail⟩ :=
    queryFreshenedFaithful_ground_expr_cons_inv
      (p := p) (ps := []) hground hmem
  cases ts with
  | nil =>
      have hqb : qb = mbHead := by
        simpa [matchAtomsList] using htail
      exact ⟨t, mbHead, by simpa using hatom, hhead, hqb⟩
  | cons u us =>
      simp [matchAtomsList] at htail

/-- Exact ground-fragment agreement for a fixed freshened equation pair on the
non-expression cases.  This is the already-settled portion of the G3 converse:
once `lhs` is not an expression, the faithful `matchAtoms`/`mergeBindings`
surface and the legacy one-way matcher produce exactly the same query result at
the same positive fuel on ground queried atoms. -/
theorem queryFreshened_ground_agrees_nonexpr_exact
    {lhs rhs atom : Atom} {qb : Bindings} {fuel : Nat}
    (hground : GroundAtom atom)
    (h_nonexpr : ¬ ∃ ps, lhs = .expression ps) :
    (rhs, qb) ∈ queryFreshenedFaithfulModel lhs rhs atom (fuel + 1) ↔
      (rhs, qb) ∈ queryFreshenedLegacyModel lhs rhs atom (fuel + 1) := by
  constructor
  · exact queryFreshened_ground_faithful_reifies_legacy_nonexpr_exact hground h_nonexpr
  · intro hlegacy
    simp [queryFreshenedLegacyModel] at hlegacy
    cases lhs with
    | var v =>
        cases hsm : simpleMatch (.var v) atom Bindings.empty (fuel + 1) with
        | none =>
            simp [hsm] at hlegacy
        | some qb0 =>
            have hqq0 : qb = qb0 := by
              simpa [hsm] using hlegacy
            have hq0 : qb0 = Bindings.empty.assign v atom := by
              simpa [simpleMatch, Bindings.empty, Bindings.lookup] using hsm.symm
            have hqb : qb = Bindings.empty.assign v atom := by
              simpa [hq0] using hqq0
            subst hqb
            have hExact :
                matchAtoms atom (.var v) (fuel + 1) =
                  [Bindings.empty.assign v atom] :=
              matchAtoms_ground_var_exact atom v fuel hground
            have hloop :
                (Bindings.empty.assign v atom).hasLoop = false :=
              GroundBindings.hasLoop_false
                (GroundBindings.assign GroundBindings.empty hground)
            simp [queryFreshenedFaithfulModel, hExact,
              mergeBindings_empty_right_local (Bindings.empty.assign v atom) fuel, hloop]
    | symbol s =>
        cases hsm : simpleMatch (.symbol s) atom Bindings.empty (fuel + 1) with
        | none =>
            simp [hsm] at hlegacy
        | some qb0 =>
            have hs : atom = .symbol s := by
              cases atom with
              | symbol t =>
                  simp [simpleMatch] at hsm
                  rcases hsm with ⟨hst, _⟩
                  subst hst
                  rfl
              | var v =>
                  exact False.elim (GroundAtom.not_var hground)
              | grounded g =>
                  simp [simpleMatch] at hsm
              | expression es =>
                  simp [simpleMatch] at hsm
            subst hs
            have hqb0 : qb0 = Bindings.empty := by
              simp [simpleMatch] at hsm
              simpa using hsm.symm
            have hqb : qb = Bindings.empty := by
              simpa [hsm, hqb0] using hlegacy
            subst hqb
            simp [queryFreshenedFaithfulModel, matchAtoms, getMetaType,
              Atom.symbolType, mergeBindings_empty_right_local Bindings.empty fuel,
              GroundBindings.hasLoop_false GroundBindings.empty]
    | grounded g =>
        cases hsm : simpleMatch (.grounded g) atom Bindings.empty (fuel + 1) with
        | none =>
            simp [hsm] at hlegacy
        | some qb0 =>
            have hg : atom = .grounded g := by
              cases atom with
              | grounded h =>
                  simp [simpleMatch] at hsm
                  rcases hsm with ⟨hgh, _⟩
                  subst hgh
                  rfl
              | var v =>
                  exact False.elim (GroundAtom.not_var hground)
              | symbol s =>
                  simp [simpleMatch] at hsm
              | expression es =>
                  simp [simpleMatch] at hsm
            subst hg
            have hqb0 : qb0 = Bindings.empty := by
              simp [simpleMatch] at hsm
              simpa using hsm.symm
            have hqb : qb = Bindings.empty := by
              simpa [hsm, hqb0] using hlegacy
            subst hqb
            simp [queryFreshenedFaithfulModel, matchAtoms, getMetaType,
              Atom.groundedType, mergeBindings_empty_right_local Bindings.empty fuel,
              GroundBindings.hasLoop_false GroundBindings.empty]
    | expression ps =>
        exact False.elim (h_nonexpr ⟨ps, rfl⟩)

/-- The faithful-vs-legacy converse is already exact for singleton
expression patterns whose head pattern is itself non-expression. This banks
the first expression slice and leaves the remaining G3 crux isolated to
multi-position seeded tail replay. -/
private theorem queryFreshened_ground_faithful_reifies_legacy_expr_single_nonexpr_exact
    {p rhs atom : Atom} {qb : Bindings} {fuel : Nat}
    (hground : GroundAtom atom)
    (h_nonexpr : ¬ ∃ ps, p = .expression ps)
    (hmem :
      (rhs, qb) ∈
        queryFreshenedFaithfulModel (.expression [p]) rhs atom (fuel + 2)) :
    (rhs, qb) ∈ queryFreshenedLegacyModel (.expression [p]) rhs atom (fuel + 2) := by
  obtain ⟨t, mbHead, hatom, hhead, hqb⟩ :=
    queryFreshenedFaithful_ground_expr_single_inv hground hmem
  subst hatom
  have hloop : mbHead.hasLoop = false :=
    GroundBindings.hasLoop_false (matchAtoms_ground_bindings (GroundAtom.elem hground (by simp)) hhead)
  have hfaithfulHead :
      (rhs, mbHead) ∈ queryFreshenedFaithfulModel p rhs t (fuel + 1) := by
    have hmerge :
        mbHead ∈ mergeBindings mbHead Bindings.empty (fuel + 1) := by
      rw [mergeBindings_empty_right_local mbHead fuel]
      simp
    refine List.mem_flatMap.mpr ?_
    refine ⟨mbHead, hhead, ?_⟩
    simp [hmerge, hloop]
  have hlegacyHead :
      (rhs, mbHead) ∈ queryFreshenedLegacyModel p rhs t (fuel + 1) :=
    (queryFreshened_ground_agrees_nonexpr_exact
      (lhs := p) (rhs := rhs) (atom := t) (qb := mbHead)
      (fuel := fuel) (hground := GroundAtom.elem hground (by simp))
      (h_nonexpr := h_nonexpr)).mp hfaithfulHead
  simp [queryFreshenedLegacyModel] at hlegacyHead ⊢
  cases hsm : simpleMatch p t Bindings.empty (fuel + 1) with
  | none =>
      simp [hsm] at hlegacyHead
  | some qb0 =>
      have hheadLegacy : qb0 = mbHead := by
        simp [hsm] at hlegacyHead
        exact hlegacyHead.symm
      simp [simpleMatch, simpleMatch.simpleMatchList, hsm, hqb, hheadLegacy]

/-- Faithful-to-legacy converse for the flat expression fragment on ground
queries: if every immediate pattern atom is non-expression, the official
empty-seeded list witness can be replayed all the way into the legacy
threaded matcher. This banks the entire flat-expression slice of G3, leaving
the remaining gap isolated to nested expression subpatterns. -/
private theorem queryFreshened_ground_faithful_reifies_legacy_expr_flat
    {ps : List Atom} {rhs atom : Atom} {qb : Bindings} {fuel : Nat}
    (hground : GroundAtom atom)
    (hflat : ∀ p ∈ ps, ¬ ∃ es, p = .expression es)
    (hmem :
      (rhs, qb) ∈
        queryFreshenedFaithfulModel (.expression ps) rhs atom (fuel + 1)) :
    ∃ fuel', (rhs, qb) ∈ queryFreshenedLegacyModel (.expression ps) rhs atom fuel' := by
  obtain ⟨ts, mb, hatom, hlen, hlist, hqb⟩ :=
    queryFreshenedFaithful_ground_expr_inv hground hmem
  subst hatom
  subst hqb
  have htsGround : ∀ t ∈ ts, GroundAtom t := by
    intro t ht
    exact GroundAtom.elem hground ht
  obtain ⟨fuelList, hlegacyList⟩ :=
    matchAtomsList_ground_seeded_reifies_simpleMatchList_nonexpr
      fuel GroundBindings.empty htsGround hflat hlist
  refine ⟨fuelList + 1, ?_⟩
  simp [queryFreshenedLegacyModel, simpleMatch, hlen, hlegacyList]

/-- Higher-order expression converse factorization on the ground fragment:
once a seeded ground head-step replay theorem is available for arbitrary
patterns, the whole faithful fixed-freshening expression query surface
replays into the legacy one-way matcher. This turns the remaining G3 work
into a single explicit local obligation. -/
private theorem sizeOf_mem_lt_expression_local (a : Atom) (es : List Atom) (ha : a ∈ es) :
    sizeOf a < sizeOf (Atom.expression es) := by
  rw [Atom.expression.sizeOf_spec]
  exact Nat.lt_of_lt_of_le (List.sizeOf_lt_of_mem ha) (Nat.le_add_left _ _)

/-- Nested-expression head replay on the ground fragment.  This is the actual
remaining G3 crux: an official head-step result, already merged into the
current seed, can be replayed by the legacy matcher even when the head pattern
itself is an expression. The proof recurses only on strict subpatterns. -/
private theorem seeded_ground_head_reifies_simpleMatch
    (pattern : Atom)
    {target : Atom} {seed mb out : Bindings} {fuel : Nat}
    (hseed : GroundBindings seed)
    (htarget : GroundAtom target)
    (hmb : mb ∈ matchAtoms target pattern fuel)
    (hmerge : out ∈ mergeBindings seed mb fuel) :
    ∃ fuel', simpleMatch pattern target seed fuel' = some out := by
  let go :
      (pattern : Atom) →
      ∀ {target : Atom} {seed mb out : Bindings} {fuel : Nat},
        GroundBindings seed →
        GroundAtom target →
        mb ∈ matchAtoms target pattern fuel →
        out ∈ mergeBindings seed mb fuel →
        ∃ fuel', simpleMatch pattern target seed fuel' = some out :=
    WellFounded.fix (measure (fun a : Atom => sizeOf a)).wf
      (fun pattern ih =>
        by
          intro target seed mb out fuel hseed htarget hmb hmerge
          cases pattern with
          | var v =>
              exact seeded_ground_nonexpr_head_reifies_simpleMatch
                hseed htarget (by intro h; rcases h with ⟨ps, hps⟩; cases hps) hmb hmerge
          | symbol s =>
              exact seeded_ground_nonexpr_head_reifies_simpleMatch
                hseed htarget (by intro h; rcases h with ⟨ps, hps⟩; cases hps) hmb hmerge
          | grounded g =>
              exact seeded_ground_nonexpr_head_reifies_simpleMatch
                hseed htarget (by intro h; rcases h with ⟨ps, hps⟩; cases hps) hmb hmerge
          | expression ps =>
              cases fuel with
              | zero =>
                  simp [matchAtoms] at hmb
              | succ n =>
                  cases target with
                  | var v =>
                      exact False.elim (GroundAtom.not_var htarget)
                  | symbol s =>
                      simp [matchAtoms, getMetaType, Atom.symbolType, Atom.expressionType] at hmb
                  | grounded g =>
                      simp [matchAtoms, getMetaType, Atom.groundedType, Atom.expressionType] at hmb
                  | expression ts =>
                      have htsGround : ∀ t ∈ ts, GroundAtom t := by
                        intro t ht
                        exact GroundAtom.elem htarget ht
                      have hfilter := matchAtoms_ground_expr_filter_free ts ps n htsGround
                      by_cases hlen : ts.length == ps.length
                      · have hlist : mb ∈ matchAtomsList ts ps [Bindings.empty] n := by
                          simpa [hfilter, hlen] using hmb
                        have hmbGround : GroundBindings mb :=
                          matchAtoms_ground_bindings htarget hmb
                        have hmergeSound : DeclMergeSpec.MergeRel seed mb out :=
                          DeclMergeSpec.mergeBindings_sound hmerge
                        obtain ⟨fuelMerge0, hmerge0⟩ := DeclMergeSpec.mergeBindings_complete hmergeSound
                        let fuelMerge := max fuelMerge0 2
                        have hmergeHi : out ∈ mergeBindings seed mb fuelMerge := by
                          have hEq : fuelMerge0 + (fuelMerge - fuelMerge0) = fuelMerge :=
                            Nat.add_sub_of_le (Nat.le_max_left _ _)
                          simpa [fuelMerge, hEq] using
                            DeclMatchSpec.mergeBindings_mono seed mb fuelMerge0 (fuelMerge - fuelMerge0) hmerge0
                        have hmerge2 : out ∈ mergeBindings seed mb 2 := by
                          exact mergeBindings_ground_of_ge_two
                            hseed hmbGround
                            (by
                              dsimp [fuelMerge]
                              exact Nat.le_max_right _ _)
                            hmergeHi
                        obtain ⟨fuelSeeded, hseededList⟩ :=
                          matchAtomsList_empty_factor_to_seeded_ground
                            n htsGround hseed hlist hmerge2
                        obtain ⟨fuelLegacy, hlegacyList⟩ :=
                          matchAtomsList_ground_seeded_reifies_simpleMatchList_of_head_replay_mem
                            fuelSeeded hseed htsGround
                            (fun {pattern target seed mb out fuel} hpatMem hseed' htarget' hmb' hmerge' =>
                              ih pattern (sizeOf_mem_lt_expression_local pattern ps hpatMem)
                                hseed' htarget' hmb' hmerge')
                            hseededList
                        have hlen' : ts.length = ps.length := by
                          simpa using hlen
                        have hneq : (ps.length != ts.length) = false := by
                          simp [hlen']
                        refine ⟨fuelLegacy + 1, ?_⟩
                        simp [simpleMatch, hneq, hlegacyList]
                      · simp [hfilter, hlen] at hmb)
  exact go pattern hseed htarget hmb hmerge

private theorem queryFreshened_ground_faithful_reifies_legacy_expr_of_head_replay
    (hHead :
      ∀ {pattern target : Atom} {seed mb out : Bindings} {fuel : Nat},
        GroundBindings seed →
        GroundAtom target →
        mb ∈ matchAtoms target pattern fuel →
        out ∈ mergeBindings seed mb fuel →
        ∃ fuel', simpleMatch pattern target seed fuel' = some out)
    {ps : List Atom} {rhs atom : Atom} {qb : Bindings} {fuel : Nat}
    (hground : GroundAtom atom)
    (hmem :
      (rhs, qb) ∈
        queryFreshenedFaithfulModel (.expression ps) rhs atom (fuel + 1)) :
    ∃ fuel', (rhs, qb) ∈ queryFreshenedLegacyModel (.expression ps) rhs atom fuel' := by
  obtain ⟨ts, mb, hatom, hlen, hlist, hqb⟩ :=
    queryFreshenedFaithful_ground_expr_inv hground hmem
  subst hatom
  subst hqb
  have htsGround : ∀ t ∈ ts, GroundAtom t := by
    intro t ht
    exact GroundAtom.elem hground ht
  obtain ⟨fuelList, hlegacyList⟩ :=
    matchAtomsList_ground_seeded_reifies_simpleMatchList_of_head_replay
      hHead fuel GroundBindings.empty htsGround hlist
  refine ⟨fuelList + 1, ?_⟩
  simp [queryFreshenedLegacyModel, simpleMatch, hlen, hlegacyList]

/-- Faithful-to-legacy converse on the bounded G3 ground fragment. For a fixed
already-freshened equation pair, every faithful official query result can be
replayed by the legacy one-way matcher, possibly at a larger matcher fuel. -/
private theorem queryFreshened_ground_faithful_reifies_legacy
    {lhs rhs atom : Atom} {qb : Bindings} {fuel : Nat}
    (hground : GroundAtom atom)
    (hmem : (rhs, qb) ∈ queryFreshenedFaithfulModel lhs rhs atom fuel) :
    ∃ fuel', (rhs, qb) ∈ queryFreshenedLegacyModel lhs rhs atom fuel' := by
  cases fuel with
  | zero =>
      cases lhs <;> simp [queryFreshenedFaithfulModel, matchAtoms] at hmem
  | succ n =>
      by_cases hexpr : ∃ ps, lhs = .expression ps
      · rcases hexpr with ⟨ps, rfl⟩
        exact
          queryFreshened_ground_faithful_reifies_legacy_expr_of_head_replay
            (fun {pattern target seed mb out fuel} hseed htarget hmb hmerge =>
              seeded_ground_head_reifies_simpleMatch pattern hseed htarget hmb hmerge)
            hground hmem
      · exact queryFreshened_ground_faithful_reifies_legacy_nonexpr hground hexpr hmem

/-- Staged G3 semantic agreement theorem, at the exact abstraction layer that
is currently sound: once the equation has already been freshened, the legacy
one-way matcher and the repaired faithful matcher/merge surface agree on the
ground-query fragment, possibly at a larger matcher fuel. This isolates the
matcher migration from the separate fuel-sensitive freshening wrapper in the
public `queryEquations` scans. -/
theorem queryFreshened_ground_legacy_lifts
    {lhs rhs atom : Atom} {qb : Bindings} {fuel : Nat}
    (hground : GroundAtom atom)
    (hmem : (rhs, qb) ∈ queryFreshenedLegacyModel lhs rhs atom fuel) :
    ∃ fuel', (rhs, qb) ∈ queryFreshenedFaithfulModel lhs rhs atom fuel' := by
  simp [queryFreshenedLegacyModel] at hmem
  cases hsm : simpleMatch lhs atom Bindings.empty fuel with
  | none =>
      simp [hsm] at hmem
  | some qb0 =>
      have hqb : qb = qb0 := by
        simpa [hsm] using hmem
      subst hqb
      obtain ⟨fuel', hmb, _hfuel⟩ :=
        simpleMatch_ground_matchAtoms hground hsm
      have hmerge : qb ∈ mergeBindings qb Bindings.empty fuel' := by
        cases fuel' with
        | zero =>
            omega
        | succ n =>
            simp [mergeBindings_empty_right_local qb n]
      refine ⟨fuel', ?_⟩
      cases fuel' with
      | zero =>
          omega
      | succ n =>
          refine List.mem_flatMap.mpr ?_
          refine ⟨qb, hmb, ?_⟩
          simp [hmerge,
            GroundBindings.hasLoop_false (matchAtoms_ground_bindings hground hmb)]

/-- Adequacy predicate for the bounded G3 fragment: the query fuel is large
enough to see every variable of every equation LHS/RHS in the scanned space,
so the freshening wrapper has stabilized. This is intentionally local to the
query migration proof; the stronger global stability story stays outside G3. -/
private def EquationFresheningAdequate (space : Space) (fuel : Nat) : Prop :=
  ∀ {eq : Atom} {idx : Nat} {lhs rhs : Atom},
    (eq, idx) ∈ space.atoms.zipIdx →
    eq = .expression [.symbol "=", lhs, rhs] →
      atomDepth lhs + 1 ≤ fuel ∧ atomDepth rhs + 1 ≤ fuel

/-- Public-surface staged G3 theorem, legacy-to-faithful direction:
on the ground-query fragment, once the query fuel is large enough that the
equation freshening wrapper has stabilized, every legacy `queryEquations`
result reappears on the repaired public `queryEquations` surface at some
larger fuel. This is the honest bridge from the fixed-freshening theorem back
to the live space scan. -/
theorem queryEquations_ground_legacy_lifts_adequate
    {space : Space} {atom rhs : Atom} {qb : Bindings} {fuel : Nat}
    (hground : GroundAtom atom)
    (hadequate : EquationFresheningAdequate space fuel)
    (hmem : (rhs, qb) ∈ queryEquationsLegacyModel space atom fuel) :
    ∃ fuel', (rhs, qb) ∈ queryEquations space atom fuel' := by
  simp [queryEquationsLegacyModel] at hmem
  rcases hmem with ⟨eq, idx, hentry, hpair⟩
  cases eq with
  | symbol s =>
      simp at hpair
  | var v =>
      simp at hpair
  | grounded g =>
      simp at hpair
  | expression es =>
      cases es with
      | nil =>
          simp at hpair
      | cons hd tl =>
          cases hd with
          | symbol s =>
              by_cases hs : s = "="
              · subst hs
                cases tl with
                | nil =>
                    simp at hpair
                | cons lhs tl2 =>
                    cases tl2 with
                    | nil =>
                        simp at hpair
                    | cons rawRhs tl3 =>
                        cases tl3 with
                        | nil =>
                            cases hsm : simpleMatch (freshenEquation idx lhs rawRhs fuel).1 atom Bindings.empty fuel with
                            | none =>
                                simp [hsm] at hpair
                            | some qb0 =>
                                have hpair :
                                    (freshenEquation idx lhs rawRhs fuel).2 = rhs ∧
                                      qb0 = qb := by
                                  simpa [hsm] using hpair
                                rcases hpair with ⟨hrhs, hqb⟩
                                have hlegacyFresh :
                                    ((freshenEquation idx lhs rawRhs fuel).2, qb0) ∈
                                      queryFreshenedLegacyModel
                                        (freshenEquation idx lhs rawRhs fuel).1
                                        (freshenEquation idx lhs rawRhs fuel).2
                                        atom fuel := by
                                  simp [queryFreshenedLegacyModel, hsm]
                                obtain ⟨fuelMatch, hfaithful⟩ :=
                                  queryFreshened_ground_legacy_lifts hground hlegacyFresh
                                let fuel' := max fuel fuelMatch + 1
                                have hfuelMatchLe : fuelMatch ≤ fuel' := by
                                  dsimp [fuel']
                                  omega
                                have hfaithful' :
                                    ((freshenEquation idx lhs rawRhs fuel).2, qb0) ∈
                                      queryFreshenedFaithfulModel
                                        (freshenEquation idx lhs rawRhs fuel).1
                                        (freshenEquation idx lhs rawRhs fuel).2
                                        atom fuel' := by
                                  have hmono :=
                                    queryFreshenedFaithful_mono
                                      (fuel := fuelMatch)
                                      (extra := fuel' - fuelMatch) hfaithful
                                  have hEq : fuelMatch + (fuel' - fuelMatch) = fuel' :=
                                    Nat.add_sub_of_le hfuelMatchLe
                                  simpa [hEq] using hmono
                                have hdepths :
                                    atomDepth lhs + 1 ≤ fuel ∧ atomDepth rawRhs + 1 ≤ fuel :=
                                  hadequate hentry rfl
                                rcases hdepths with ⟨hdepthL, hdepthR⟩
                                have hfuelLe : fuel ≤ fuel' := by
                                  dsimp [fuel']
                                  omega
                                have hdepthL' : atomDepth lhs + 1 ≤ fuel' := by
                                  exact le_trans hdepthL hfuelLe
                                have hdepthR' : atomDepth rawRhs + 1 ≤ fuel' := by
                                  exact le_trans hdepthR hfuelLe
                                have hstable :
                                    freshenEquation idx lhs rawRhs fuel =
                                      freshenEquation idx lhs rawRhs fuel' :=
                                  freshenEquation_stable_of_depth
                                    idx lhs rawRhs fuel fuel'
                                    hdepthL hdepthL' hdepthR hdepthR'
                                have hrhs' :
                                    (freshenEquation idx lhs rawRhs fuel').2 = rhs := by
                                  simpa [hstable] using hrhs
                                have hinner :
                                    (rhs, qb) ∈
                                      queryFreshenedFaithfulModel
                                        (freshenEquation idx lhs rawRhs fuel').1
                                        (freshenEquation idx lhs rawRhs fuel').2
                                        atom fuel' := by
                                  simpa [queryFreshenedFaithfulModel, hstable, hrhs, hrhs', hqb] using hfaithful'
                                refine ⟨fuel', ?_⟩
                                have hscan :
                                    (rhs, qb) ∈
                                      space.atoms.zipIdx.flatMap (fun (eq, idx) =>
                                        match eq with
                                        | .expression [.symbol "=", lhs, rhs] =>
                                            let (lhs', rhs') := freshenEquation idx lhs rhs fuel'
                                            (matchAtoms atom lhs' fuel').flatMap fun qb =>
                                          (mergeBindings qb Bindings.empty fuel').filterMap fun merged =>
                                                if merged.hasLoop then none else some (rhs', merged)
                                        | _ => []) := by
                                  refine List.mem_flatMap.mpr ?_
                                  refine ⟨(.expression [.symbol "=", lhs, rawRhs], idx), hentry, ?_⟩
                                  simpa [queryFreshenedFaithfulModel] using hinner
                                have hquery :
                                    queryEquations space atom (max fuel fuelMatch + 1) =
                                      space.atoms.zipIdx.flatMap (fun (eq, idx) =>
                                        match eq with
                                        | .expression [.symbol "=", lhs, rhs] =>
                                            let (lhs', rhs') :=
                                              freshenEquation idx lhs rhs (max fuel fuelMatch + 1)
                                            (matchAtoms atom lhs' (max fuel fuelMatch + 1)).flatMap fun qb =>
                                              (mergeBindings qb Bindings.empty (max fuel fuelMatch + 1)).filterMap
                                                fun merged =>
                                                  if merged.hasLoop then none else some (rhs', merged)
                                        | _ => []) := by
                                  simp [queryEquations]
                                  rfl
                                dsimp [fuel'] at hscan ⊢
                                have hfinal :
                                    (rhs, qb) ∈ queryEquations space atom (max fuel fuelMatch + 1) := by
                                  simpa [hquery] using hscan
                                exact hfinal
                        | cons extra rest =>
                            simp at hpair
              · simp [hs] at hpair
          | var v =>
              simp at hpair
          | grounded g =>
              simp at hpair
          | expression inner =>
              simp at hpair

/-- Visible-avoid companion to `queryEquations_ground_legacy_lifts_adequate`.
For ground query atoms the avoid set is definitionally empty, so the same
stabilized-freshening argument lifts legacy hits into the repaired public
`queryEquationsAgainstVisible` scan. -/
theorem queryEquationsAgainstVisible_ground_legacy_lifts_adequate
    {space : Space} {atom rhs : Atom} {qb : Bindings} {fuel : Nat}
    (hground : GroundAtom atom)
    (hadequate : EquationFresheningAdequate space fuel)
    (hmem : (rhs, qb) ∈ queryEquationsAgainstVisibleLegacyModel space atom fuel) :
    ∃ fuel', (rhs, qb) ∈ queryEquationsAgainstVisible space atom fuel' := by
  have havoidNil : (collectVars atom fuel).eraseDups = [] := by
    simp [collectVars_ground_nil hground fuel]
  simp [queryEquationsAgainstVisibleLegacyModel, havoidNil] at hmem
  rcases hmem with ⟨eq, idx, hentry, hpair⟩
  cases eq with
  | symbol s =>
      simp at hpair
  | var v =>
      simp at hpair
  | grounded g =>
      simp at hpair
  | expression es =>
      cases es with
      | nil =>
          simp at hpair
      | cons hd tl =>
          cases hd with
          | symbol s =>
              by_cases hs : s = "="
              · subst hs
                cases tl with
                | nil =>
                    simp at hpair
                | cons lhs tl2 =>
                    cases tl2 with
                    | nil =>
                        simp at hpair
                    | cons rawRhs tl3 =>
                        cases tl3 with
                        | nil =>
                            cases hsm : simpleMatch (freshenEquationAgainst [] idx lhs rawRhs fuel).1 atom Bindings.empty fuel with
                            | none =>
                                simp [hsm] at hpair
                            | some qb0 =>
                                have hpair :
                                    (freshenEquationAgainst [] idx lhs rawRhs fuel).2 = rhs ∧
                                      qb0 = qb := by
                                  simpa [hsm] using hpair
                                rcases hpair with ⟨hrhs, hqb⟩
                                have hlegacyFresh :
                                    ((freshenEquationAgainst [] idx lhs rawRhs fuel).2, qb0) ∈
                                      queryFreshenedLegacyModel
                                        (freshenEquationAgainst [] idx lhs rawRhs fuel).1
                                        (freshenEquationAgainst [] idx lhs rawRhs fuel).2
                                        atom fuel := by
                                  simp [queryFreshenedLegacyModel, hsm]
                                obtain ⟨fuelMatch, hfaithful⟩ :=
                                  queryFreshened_ground_legacy_lifts hground hlegacyFresh
                                let fuel' := max fuel fuelMatch + 1
                                have hfuelMatchLe : fuelMatch ≤ fuel' := by
                                  dsimp [fuel']
                                  omega
                                have hfaithful' :
                                    ((freshenEquationAgainst [] idx lhs rawRhs fuel).2, qb0) ∈
                                      queryFreshenedFaithfulModel
                                        (freshenEquationAgainst [] idx lhs rawRhs fuel).1
                                        (freshenEquationAgainst [] idx lhs rawRhs fuel).2
                                        atom fuel' := by
                                  have hmono :=
                                    queryFreshenedFaithful_mono
                                      (fuel := fuelMatch)
                                      (extra := fuel' - fuelMatch) hfaithful
                                  have hEq : fuelMatch + (fuel' - fuelMatch) = fuel' :=
                                    Nat.add_sub_of_le hfuelMatchLe
                                  simpa [hEq] using hmono
                                have hdepths :
                                    atomDepth lhs + 1 ≤ fuel ∧ atomDepth rawRhs + 1 ≤ fuel :=
                                  hadequate hentry rfl
                                rcases hdepths with ⟨hdepthL, hdepthR⟩
                                have hfuelLe : fuel ≤ fuel' := by
                                  dsimp [fuel']
                                  omega
                                have hdepthL' : atomDepth lhs + 1 ≤ fuel' := by
                                  exact le_trans hdepthL hfuelLe
                                have hdepthR' : atomDepth rawRhs + 1 ≤ fuel' := by
                                  exact le_trans hdepthR hfuelLe
                                have hstable :
                                    freshenEquationAgainst [] idx lhs rawRhs fuel =
                                      freshenEquationAgainst [] idx lhs rawRhs fuel' :=
                                  freshenEquationAgainst_stable_of_depth
                                    [] idx lhs rawRhs fuel fuel'
                                    hdepthL hdepthL' hdepthR hdepthR'
                                have havoidNil' : (collectVars atom fuel').eraseDups = [] := by
                                  simp [collectVars_ground_nil hground fuel']
                                have hrhs' :
                                    (freshenEquationAgainst [] idx lhs rawRhs fuel').2 = rhs := by
                                  simpa [hstable] using hrhs
                                have hinner :
                                    (rhs, qb) ∈
                                      queryFreshenedFaithfulModel
                                        (freshenEquationAgainst [] idx lhs rawRhs fuel').1
                                        (freshenEquationAgainst [] idx lhs rawRhs fuel').2
                                        atom fuel' := by
                                  simpa [queryFreshenedFaithfulModel, hstable, hrhs, hrhs', hqb] using hfaithful'
                                refine ⟨fuel', ?_⟩
                                have hscan :
                                    (rhs, qb) ∈
                                      space.atoms.zipIdx.flatMap (fun (eq, idx) =>
                                        match eq with
                                        | .expression [.symbol "=", lhs, rhs] =>
                                            let (lhs', rhs') :=
                                              freshenEquationAgainst ((collectVars atom fuel').eraseDups) idx lhs rhs fuel'
                                            (matchAtoms atom lhs' fuel').flatMap fun qb =>
                                              (mergeBindings qb Bindings.empty fuel').filterMap fun merged =>
                                                if merged.hasLoop then none else some (rhs', merged)
                                        | _ => []) := by
                                  refine List.mem_flatMap.mpr ?_
                                  refine ⟨(.expression [.symbol "=", lhs, rawRhs], idx), hentry, ?_⟩
                                  simpa [queryFreshenedFaithfulModel, havoidNil'] using hinner
                                have hquery :
                                    queryEquationsAgainstVisible space atom (max fuel fuelMatch + 1) =
                                      space.atoms.zipIdx.flatMap (fun (eq, idx) =>
                                        match eq with
                                        | .expression [.symbol "=", lhs, rhs] =>
                                            let (lhs', rhs') :=
                                              freshenEquationAgainst ((collectVars atom (max fuel fuelMatch + 1)).eraseDups)
                                                idx lhs rhs (max fuel fuelMatch + 1)
                                            (matchAtoms atom lhs' (max fuel fuelMatch + 1)).flatMap fun qb =>
                                              (mergeBindings qb Bindings.empty (max fuel fuelMatch + 1)).filterMap
                                                fun merged =>
                                                  if merged.hasLoop then none else some (rhs', merged)
                                        | _ => []) := by
                                  simp [queryEquationsAgainstVisible]
                                  rfl
                                dsimp [fuel'] at hscan havoidNil' ⊢
                                have hfinal :
                                    (rhs, qb) ∈
                                      queryEquationsAgainstVisible space atom (max fuel fuelMatch + 1) := by
                                  simpa [hquery] using hscan
                                exact hfinal
                        | cons extra rest =>
                            simp at hpair
              · simp [hs] at hpair
          | var v =>
              simp at hpair
          | grounded g =>
              simp at hpair
          | expression inner =>
              simp at hpair

/-- Public-surface staged G3 theorem, faithful-to-legacy direction:
on the ground-query fragment, every repaired public `queryEquations` hit
replays into the legacy one-way scan once the equation freshening wrapper is
stable at the queried fuel. The replay itself may use a larger matcher fuel,
so this theorem packages the faithful hit with the same adequacy hypothesis
used by the forward lift. -/
theorem queryEquations_ground_faithful_reifies_legacy
    {space : Space} {atom rhs : Atom} {qb : Bindings} {fuel : Nat}
    (hground : GroundAtom atom)
    (hadequate : EquationFresheningAdequate space fuel)
    (hmem : (rhs, qb) ∈ queryEquations space atom fuel) :
    ∃ fuel', (rhs, qb) ∈ queryEquationsLegacyModel space atom fuel' := by
  cases fuel with
  | zero =>
      simp [queryEquations] at hmem
  | succ n =>
      simp [queryEquations] at hmem
      rcases hmem with ⟨eq, idx, hentry, hinner⟩
      cases eq with
      | symbol s =>
          simp at hinner
      | var v =>
          simp at hinner
      | grounded g =>
          simp at hinner
      | expression es =>
          cases es with
          | nil =>
              simp at hinner
          | cons hd tl =>
              cases hd with
              | symbol s =>
                  by_cases hs : s = "="
                  · subst hs
                    cases tl with
                    | nil =>
                        simp at hinner
                    | cons lhs tl2 =>
                        cases tl2 with
                        | nil =>
                            simp at hinner
                        | cons rawRhs tl3 =>
                            cases tl3 with
                            | nil =>
                                have hrhs :
                                    (freshenEquation idx lhs rawRhs (n + 1)).2 = rhs := by
                                  rcases List.mem_flatMap.mp hinner with ⟨mb0, hmb0, hfilter0⟩
                                  rcases List.mem_filterMap.mp hfilter0 with ⟨merged, hmerged, hsome⟩
                                  cases hloop : merged.hasLoop with
                                  | true =>
                                      simp [hloop] at hsome
                                  | false =>
                                      rw [hloop] at hsome
                                      have hpair :
                                          ((freshenEquation idx lhs rawRhs (n + 1)).2, merged) = (rhs, qb) := by
                                        simpa using Option.some.inj hsome
                                      exact congrArg Prod.fst hpair
                                have hfresh :
                                    ((freshenEquation idx lhs rawRhs (n + 1)).2, qb) ∈
                                      queryFreshenedFaithfulModel
                                        (freshenEquation idx lhs rawRhs (n + 1)).1
                                        (freshenEquation idx lhs rawRhs (n + 1)).2
                                        atom (n + 1) := by
                                  simpa [queryFreshenedFaithfulModel, hrhs] using hinner
                                obtain ⟨fuelLegacy, hlegacyFresh0⟩ :=
                                  queryFreshened_ground_faithful_reifies_legacy
                                    (lhs := (freshenEquation idx lhs rawRhs (n + 1)).1)
                                    (rhs := (freshenEquation idx lhs rawRhs (n + 1)).2)
                                    (atom := atom) (qb := qb) (fuel := n + 1)
                                    hground hfresh
                                let fuel' := max (n + 1) fuelLegacy
                                have hFuelLegacyLe : fuelLegacy ≤ fuel' := by
                                  dsimp [fuel']
                                  exact Nat.le_max_right _ _
                                have hlegacyFresh :
                                    ((freshenEquation idx lhs rawRhs (n + 1)).2, qb) ∈
                                      queryFreshenedLegacyModel
                                        (freshenEquation idx lhs rawRhs (n + 1)).1
                                        (freshenEquation idx lhs rawRhs (n + 1)).2
                                        atom fuel' := by
                                  have hmono :=
                                    queryFreshenedLegacy_mono
                                      (fuel := fuelLegacy)
                                      (extra := fuel' - fuelLegacy)
                                      hlegacyFresh0
                                  have hEq : fuelLegacy + (fuel' - fuelLegacy) = fuel' :=
                                    Nat.add_sub_of_le hFuelLegacyLe
                                  simpa [hEq] using hmono
                                have hdepths :
                                    atomDepth lhs + 1 ≤ n + 1 ∧ atomDepth rawRhs + 1 ≤ n + 1 :=
                                  hadequate hentry rfl
                                rcases hdepths with ⟨hdepthL, hdepthR⟩
                                have hFuelLe : n + 1 ≤ fuel' := by
                                  dsimp [fuel']
                                  exact Nat.le_max_left _ _
                                have hdepthL' : atomDepth lhs + 1 ≤ fuel' := by
                                  exact le_trans hdepthL hFuelLe
                                have hdepthR' : atomDepth rawRhs + 1 ≤ fuel' := by
                                  exact le_trans hdepthR hFuelLe
                                have hstable :
                                    freshenEquation idx lhs rawRhs (n + 1) =
                                      freshenEquation idx lhs rawRhs fuel' :=
                                  freshenEquation_stable_of_depth
                                    idx lhs rawRhs (n + 1) fuel'
                                    hdepthL hdepthL' hdepthR hdepthR'
                                simp [queryFreshenedLegacyModel] at hlegacyFresh
                                cases hsm :
                                    simpleMatch
                                      (freshenEquation idx lhs rawRhs (n + 1)).1
                                      atom Bindings.empty fuel' with
                                | none =>
                                    simp [hsm] at hlegacyFresh
                                | some qb0 =>
                                    have hqb : qb = qb0 := by
                                      simpa [hsm] using hlegacyFresh
                                    have hrhs' :
                                        (freshenEquation idx lhs rawRhs fuel').2 = rhs := by
                                      simpa [hstable] using hrhs
                                    have hsm' :
                                        simpleMatch
                                          (freshenEquation idx lhs rawRhs fuel').1
                                          atom Bindings.empty fuel' = some qb0 := by
                                      simpa [hstable] using hsm
                                    refine ⟨fuel', ?_⟩
                                    refine List.mem_filterMap.mpr ?_
                                    refine ⟨(.expression [.symbol "=", lhs, rawRhs], idx), hentry, ?_⟩
                                    simp [hsm', hrhs', hqb]
                            | cons extra rest =>
                                simp at hinner
                  · simp [hs] at hinner
              | var v =>
                  simp at hinner
              | grounded g =>
                  simp at hinner
              | expression inner =>
                  simp at hinner

/-- Visible-avoid public converse companion to
`queryEquations_ground_faithful_reifies_legacy`. On the ground fragment the
avoid set is definitionally empty, so the same adequate-fuel replay turns a
faithful `queryEquationsAgainstVisible` hit into a legacy visible-avoid hit. -/
theorem queryEquationsAgainstVisible_ground_faithful_reifies_legacy
    {space : Space} {atom rhs : Atom} {qb : Bindings} {fuel : Nat}
    (hground : GroundAtom atom)
    (hadequate : EquationFresheningAdequate space fuel)
    (hmem : (rhs, qb) ∈ queryEquationsAgainstVisible space atom fuel) :
    ∃ fuel', (rhs, qb) ∈ queryEquationsAgainstVisibleLegacyModel space atom fuel' := by
  have havoidNil : (collectVars atom fuel).eraseDups = [] := by
    simp [collectVars_ground_nil hground fuel]
  cases fuel with
  | zero =>
      simp [queryEquationsAgainstVisible] at hmem
  | succ n =>
      simp [queryEquationsAgainstVisible, havoidNil] at hmem
      rcases hmem with ⟨eq, idx, hentry, hinner⟩
      cases eq with
      | symbol s =>
          simp at hinner
      | var v =>
          simp at hinner
      | grounded g =>
          simp at hinner
      | expression es =>
          cases es with
          | nil =>
              simp at hinner
          | cons hd tl =>
              cases hd with
              | symbol s =>
                  by_cases hs : s = "="
                  · subst hs
                    cases tl with
                    | nil =>
                        simp at hinner
                    | cons lhs tl2 =>
                        cases tl2 with
                        | nil =>
                            simp at hinner
                        | cons rawRhs tl3 =>
                            cases tl3 with
                            | nil =>
                                have hrhs :
                                    (freshenEquationAgainst [] idx lhs rawRhs (n + 1)).2 = rhs := by
                                  rcases List.mem_flatMap.mp hinner with ⟨mb0, hmb0, hfilter0⟩
                                  rcases List.mem_filterMap.mp hfilter0 with ⟨merged, hmerged, hsome⟩
                                  cases hloop : merged.hasLoop with
                                  | true =>
                                      simp [hloop] at hsome
                                  | false =>
                                      rw [hloop] at hsome
                                      have hpair :
                                          ((freshenEquationAgainst [] idx lhs rawRhs (n + 1)).2, merged) = (rhs, qb) := by
                                        simpa using Option.some.inj hsome
                                      exact congrArg Prod.fst hpair
                                have hfresh :
                                    ((freshenEquationAgainst [] idx lhs rawRhs (n + 1)).2, qb) ∈
                                      queryFreshenedFaithfulModel
                                        (freshenEquationAgainst [] idx lhs rawRhs (n + 1)).1
                                        (freshenEquationAgainst [] idx lhs rawRhs (n + 1)).2
                                        atom (n + 1) := by
                                  simpa [queryFreshenedFaithfulModel, hrhs] using hinner
                                obtain ⟨fuelLegacy, hlegacyFresh0⟩ :=
                                  queryFreshened_ground_faithful_reifies_legacy
                                    (lhs := (freshenEquationAgainst [] idx lhs rawRhs (n + 1)).1)
                                    (rhs := (freshenEquationAgainst [] idx lhs rawRhs (n + 1)).2)
                                    (atom := atom) (qb := qb) (fuel := n + 1)
                                    hground hfresh
                                let fuel' := max (n + 1) fuelLegacy
                                have hFuelLegacyLe : fuelLegacy ≤ fuel' := by
                                  dsimp [fuel']
                                  exact Nat.le_max_right _ _
                                have hlegacyFresh :
                                    ((freshenEquationAgainst [] idx lhs rawRhs (n + 1)).2, qb) ∈
                                      queryFreshenedLegacyModel
                                        (freshenEquationAgainst [] idx lhs rawRhs (n + 1)).1
                                        (freshenEquationAgainst [] idx lhs rawRhs (n + 1)).2
                                        atom fuel' := by
                                  have hmono :=
                                    queryFreshenedLegacy_mono
                                      (fuel := fuelLegacy)
                                      (extra := fuel' - fuelLegacy)
                                      hlegacyFresh0
                                  have hEq : fuelLegacy + (fuel' - fuelLegacy) = fuel' :=
                                    Nat.add_sub_of_le hFuelLegacyLe
                                  simpa [hEq] using hmono
                                have hdepths :
                                    atomDepth lhs + 1 ≤ n + 1 ∧ atomDepth rawRhs + 1 ≤ n + 1 :=
                                  hadequate hentry rfl
                                rcases hdepths with ⟨hdepthL, hdepthR⟩
                                have hFuelLe : n + 1 ≤ fuel' := by
                                  dsimp [fuel']
                                  exact Nat.le_max_left _ _
                                have hdepthL' : atomDepth lhs + 1 ≤ fuel' := by
                                  exact le_trans hdepthL hFuelLe
                                have hdepthR' : atomDepth rawRhs + 1 ≤ fuel' := by
                                  exact le_trans hdepthR hFuelLe
                                have hstable :
                                    freshenEquationAgainst [] idx lhs rawRhs (n + 1) =
                                      freshenEquationAgainst [] idx lhs rawRhs fuel' :=
                                  freshenEquationAgainst_stable_of_depth
                                    [] idx lhs rawRhs (n + 1) fuel'
                                    hdepthL hdepthL' hdepthR hdepthR'
                                have havoidNil' : (collectVars atom fuel').eraseDups = [] := by
                                  simp [collectVars_ground_nil hground fuel']
                                simp [queryFreshenedLegacyModel] at hlegacyFresh
                                cases hsm :
                                    simpleMatch
                                      (freshenEquationAgainst [] idx lhs rawRhs (n + 1)).1
                                      atom Bindings.empty fuel' with
                                | none =>
                                    simp [hsm] at hlegacyFresh
                                | some qb0 =>
                                    have hqb : qb = qb0 := by
                                      simpa [hsm] using hlegacyFresh
                                    have hrhs' :
                                        (freshenEquationAgainst [] idx lhs rawRhs fuel').2 = rhs := by
                                      simpa [hstable] using hrhs
                                    have hsm' :
                                        simpleMatch
                                          (freshenEquationAgainst [] idx lhs rawRhs fuel').1
                                          atom Bindings.empty fuel' = some qb0 := by
                                      simpa [hstable] using hsm
                                    refine ⟨fuel', ?_⟩
                                    refine List.mem_filterMap.mpr ?_
                                    refine ⟨(.expression [.symbol "=", lhs, rawRhs], idx), hentry, ?_⟩
                                    simp [havoidNil', hsm', hrhs', hqb]
                            | cons extra rest =>
                                simp at hinner
                  · simp [hs] at hinner
              | var v =>
                  simp at hinner
              | grounded g =>
                  simp at hinner
              | expression inner =>
                  simp at hinner

/-- Explicit two-way staged G3 agreement on the ground fragment for the public
`queryEquations` surface. The two directions live at different abstractions:
legacy hits need freshening adequacy to lift into the repaired surface, and
faithful hits use the same adequacy hypothesis to stabilize the legacy scan
around the replay fuel. -/
theorem queryEquations_ground_two_way_adequate
    {space : Space} {atom rhs : Atom} {qb : Bindings} {fuel : Nat}
    (hground : GroundAtom atom)
    (hadequate : EquationFresheningAdequate space fuel) :
    ((rhs, qb) ∈ queryEquationsLegacyModel space atom fuel →
      ∃ fuel', (rhs, qb) ∈ queryEquations space atom fuel') ∧
    ((rhs, qb) ∈ queryEquations space atom fuel →
      ∃ fuel', (rhs, qb) ∈ queryEquationsLegacyModel space atom fuel') := by
  constructor
  · intro hlegacy
    exact queryEquations_ground_legacy_lifts_adequate hground hadequate hlegacy
  · intro hfaithful
    exact queryEquations_ground_faithful_reifies_legacy hground hadequate hfaithful

/-- Visible-avoid companion to `queryEquations_ground_two_way_adequate`. -/
theorem queryEquationsAgainstVisible_ground_two_way_adequate
    {space : Space} {atom rhs : Atom} {qb : Bindings} {fuel : Nat}
    (hground : GroundAtom atom)
    (hadequate : EquationFresheningAdequate space fuel) :
    ((rhs, qb) ∈ queryEquationsAgainstVisibleLegacyModel space atom fuel →
      ∃ fuel', (rhs, qb) ∈ queryEquationsAgainstVisible space atom fuel') ∧
    ((rhs, qb) ∈ queryEquationsAgainstVisible space atom fuel →
      ∃ fuel', (rhs, qb) ∈ queryEquationsAgainstVisibleLegacyModel space atom fuel') := by
  constructor
  · intro hlegacy
    exact queryEquationsAgainstVisible_ground_legacy_lifts_adequate hground hadequate hlegacy
  · intro hfaithful
    exact queryEquationsAgainstVisible_ground_faithful_reifies_legacy hground hadequate hfaithful

end Mettapedia.Languages.MeTTa.HE
