import Mettapedia.Languages.MeTTa.HE.Certification
import Mettapedia.Languages.MeTTa.HE.SmallStepMaster
import Mettapedia.Languages.MeTTa.HE.BindingComposition

/-!
# F1: The Matcher Bridge — Leaf Layer

Relating the coarse rules' one-way pattern matcher (`simpleMatch`,
accumulator-threading) to the official `unify` instruction's matcher
(`matchAtoms`, fresh-bindings folded through `mergeBindings`) on ground
scrutinees.  This file lands the leaf commutation facts; the
fuel-monotonicity induction and the bridge proper build on them (design
note F1).

Key alignment facts (verified against the definitions, recorded here as
theorems): `Bindings.assign` appends for fresh variables (order
preserved), and `addVarBinding`'s nonlinear-variable handling (`prev ==
val → [b]`) mirrors `simpleMatch`'s lookup-equality exactly — the two
matchers agree on repeated pattern variables over ground scrutinees.
We state only what we prove.
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-- Fresh-variable `addVarBinding` is plain assignment. -/
theorem addVarBinding_fresh {b : Bindings} {v : String} {val : Atom}
    (h : b.lookup v = none) (n : Nat) :
    addVarBinding b v val (n + 1) = [b.assign v val] := by
  simp [addVarBinding, h]

/-- Bound-to-the-same-value `addVarBinding` is the identity. -/
theorem addVarBinding_same {b : Bindings} {v : String} {val : Atom}
    (h : b.lookup v = some val) (n : Nat) :
    addVarBinding b v val (n + 1) = [b] := by
  simp [addVarBinding, h]

/-- Merging a single fresh assignment: the same case split as
`simpleMatch`'s variable case (fresh → extend; bound-same → unchanged). -/
theorem mergeBindings_single_assign {b : Bindings} {v : String} {val : Atom}
    (n : Nat) :
    mergeBindings b (Bindings.empty.assign v val) (n + 2) =
      addVarBinding b v val (n + 1) := by
  simp [mergeBindings, Bindings.assign, Bindings.empty, Bindings.isBound,
    Bindings.lookup]

/-- Fresh single-assignment merge is just the expected assignment. -/
theorem mergeBindings_single_assign_fresh {b : Bindings} {v : String} {val : Atom}
    (h : b.lookup v = none) (n : Nat) :
    mergeBindings b (Bindings.empty.assign v val) (n + 2) = [b.assign v val] := by
  rw [mergeBindings_single_assign]
  exact addVarBinding_fresh h n

/-- Re-merging the same single assignment is the identity. -/
theorem mergeBindings_single_assign_same {b : Bindings} {v : String} {val : Atom}
    (h : b.lookup v = some val) (n : Nat) :
    mergeBindings b (Bindings.empty.assign v val) (n + 2) = [b] := by
  rw [mergeBindings_single_assign]
  exact addVarBinding_same h n

/-- Empty bindings merged with a single assignment reproduce that assignment
once enough fuel is available for the inner `addVarBinding`. -/
theorem mergeBindings_empty_single_assign {v : String} {val : Atom} (n : Nat) :
    mergeBindings Bindings.empty (Bindings.empty.assign v val) (n + 2) =
      [Bindings.empty.assign v val] := by
  rw [mergeBindings_single_assign]
  exact addVarBinding_fresh (by simp [Bindings.empty, Bindings.lookup]) n

/-- At fuel 1, `addVarBinding` is a deterministic single-step compatibility
check: fresh extends, same-value keeps, different-value fails. -/
theorem addVarBinding_fuel1 (b : Bindings) (v : String) (val : Atom) :
    addVarBinding b v val 1 =
      match b.lookup v with
      | none => [b.assign v val]
      | some prev => if prev == val then [b] else [] := by
  cases hlook : b.lookup v <;> simp [addVarBinding, hlook, matchAtoms]

/-- One deterministic ground-merge fold step: thread a list of candidate
bindings through one assignment, failing on incompatible rebinding. -/
private def detfoldStep (acc : List Bindings) (x : String × Atom) : List Bindings :=
  acc.flatMap fun (b : Bindings) =>
    match b.lookup x.1 with
    | none => [b.assign x.1 x.2]
    | some prev => if prev == x.2 then [b] else []

/-- Deterministic ground-merge helper: merge a list of assignments into a seed,
failing on the first incompatible rebinding. This is the algebraic view of
`mergeBindings` on the ground fragment. -/
private def mergeGroundAssignments? (b : Bindings) :
    List (String × Atom) → Option Bindings
  | [] => some b
  | (v, val) :: rest =>
      match b.lookup v with
      | none => mergeGroundAssignments? (b.assign v val) rest
      | some prev =>
          if prev == val then
            mergeGroundAssignments? b rest
          else
            none

/-- The fuel-1 `addVarBinding` fold is definitionally the deterministic
lookup/compare fold used by `mergeGroundAssignments?`. -/
private theorem fold_addVarBinding_fuel1_eq
    (acc : List Bindings) (assigns : List (String × Atom)) :
    List.foldl
      (fun acc x => acc.flatMap fun b => addVarBinding b x.1 x.2 1)
      acc assigns =
    List.foldl detfoldStep acc assigns := by
  induction assigns generalizing acc with
  | nil => rfl
  | cons pair assigns ih =>
      rcases pair with ⟨v, val⟩
      simpa [List.foldl, addVarBinding_fuel1, detfoldStep] using
        ih
          (List.flatMap
            (fun b =>
              match b.lookup v with
              | none => [b.assign v val]
              | some prev => if prev == val then [b] else [])
            acc)

/-- Once the deterministic ground-merge fold has no candidate bindings left,
it stays empty. -/
private theorem detfold_nil
    (assigns : List (String × Atom)) :
    List.foldl detfoldStep [] assigns = [] := by
  induction assigns with
  | nil => rfl
  | cons pair assigns ih =>
      rcases pair with ⟨v, val⟩
      simp [detfoldStep, ih]

/-- The deterministic ground-merge helper exactly matches the explicit
deterministic assignment fold. -/
private theorem mergeGroundAssignments_toList_eq_detfold
    (b : Bindings) (assigns : List (String × Atom)) :
    (mergeGroundAssignments? b assigns).toList =
      List.foldl detfoldStep [b] assigns := by
  induction assigns generalizing b with
  | nil => rfl
  | cons pair assigns ih =>
      rcases pair with ⟨v, val⟩
      cases hlook : b.lookup v with
      | none =>
          simp [mergeGroundAssignments?, detfoldStep, hlook]
          simpa [detfoldStep, hlook] using ih (b.assign v val)
      | some prev =>
          by_cases hsame : prev = val
          · have hbeq : (prev == val) = true := by simp [hsame]
            simp [mergeGroundAssignments?, detfoldStep, hlook, hsame]
            simpa [detfoldStep, hlook, hsame] using ih b
          · have hbeq : (prev == val) = false := by simp [hsame]
            simp [mergeGroundAssignments?, detfoldStep, hlook, hsame, hbeq, detfold_nil]

/-- Deterministic ground-merge composes over appended assignment lists. -/
private theorem mergeGroundAssignments_append
    (b : Bindings) (xs ys : List (String × Atom)) :
    mergeGroundAssignments? b (xs ++ ys) =
      match mergeGroundAssignments? b xs with
      | some b' => mergeGroundAssignments? b' ys
      | none => none := by
  induction xs generalizing b with
  | nil => rfl
  | cons pair xs ih =>
      rcases pair with ⟨v, val⟩
      cases hlook : b.lookup v with
      | none =>
          simp [mergeGroundAssignments?, hlook, ih]
      | some prev =>
          by_cases hsame : prev == val
          · simp [mergeGroundAssignments?, hlook, hsame, ih]
          · simp [mergeGroundAssignments?, hlook, hsame]

private theorem lookup_none_of_not_mem_keys
    {xs : List (String × Atom)} {v : String}
    (h : v ∉ xs.map Prod.fst) :
    List.lookup v xs = none := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      rcases x with ⟨k, a⟩
      have hk : v ≠ k := by
        intro hvk
        apply h
        simp [hvk]
      have htail : v ∉ xs.map Prod.fst := by
        intro hmem
        apply h
        simp [hmem]
      have hne : (v == k) = false := by
        simp [hk]
      simp [List.lookup_cons, hne, ih htail]

/-- On a right fragment with distinct keys, successful deterministic ground
merge is extensional: each lookup in the result comes from the right fragment
if present there, otherwise from the left seed. -/
private theorem mergeGroundAssignments_lookup_spec
    {left out : Bindings} {assigns : List (String × Atom)}
    (hkeys : (assigns.map Prod.fst).Nodup)
    (hmerge : mergeGroundAssignments? left assigns = some out) :
    ∀ x,
      out.lookup x =
        match List.lookup x assigns with
        | some a => some a
        | none => left.lookup x := by
  induction assigns generalizing left out with
  | nil =>
      intro x
      simp [mergeGroundAssignments?] at hmerge
      rcases hmerge with rfl
      rfl
  | cons pair assigns ih =>
      rcases pair with ⟨v, val⟩
      have hnotmem : v ∉ assigns.map Prod.fst := by
        simpa using (List.nodup_cons.mp hkeys).1
      have hkeys' : (assigns.map Prod.fst).Nodup := by
        simpa using (List.nodup_cons.mp hkeys).2
      cases hlook : left.lookup v with
      | none =>
          simp [mergeGroundAssignments?, hlook] at hmerge
          intro x
          by_cases hxeq : x = v
          · subst x
            have htailNone : List.lookup v assigns = none :=
              lookup_none_of_not_mem_keys hnotmem
            have hseed :
                out.lookup v =
                  match List.lookup v assigns with
                  | some a => some a
                  | none => (left.assign v val).lookup v :=
              ih hkeys' hmerge v
            rw [htailNone] at hseed
            simpa [lookup_assign_of_lookup_none left v val hlook] using hseed
          · have htail :
              out.lookup x =
                match List.lookup x assigns with
                | some a => some a
                | none => (left.assign v val).lookup x :=
              ih hkeys' hmerge x
            have hlookup :
                (left.assign v val).lookup x = left.lookup x :=
              assign_lookup_ne left v val x hxeq hlook
            have hcons : List.lookup x ((v, val) :: assigns) = List.lookup x assigns := by
              have hbeq : (x == v) = false := by simp [hxeq]
              simp [List.lookup_cons, hbeq]
            rw [hcons]
            simpa [hlookup] using htail
      | some prev =>
          by_cases hsame : prev = val
          · simp [mergeGroundAssignments?, hlook, hsame] at hmerge
            intro x
            by_cases hxeq : x = v
            · subst x
              have htailNone : List.lookup v assigns = none :=
                lookup_none_of_not_mem_keys hnotmem
              have htail :
                  out.lookup v =
                    match List.lookup v assigns with
                    | some a => some a
                    | none => left.lookup v :=
                ih hkeys' hmerge v
              rw [htailNone] at htail
              simpa [List.lookup_cons, hlook, hsame] using htail
            · have htail :
                out.lookup x =
                  match List.lookup x assigns with
                    | some a => some a
                    | none => left.lookup x :=
                ih hkeys' hmerge x
              have hcons : List.lookup x ((v, val) :: assigns) = List.lookup x assigns := by
                have hbeq : (x == v) = false := by simp [hxeq]
                simp [List.lookup_cons, hbeq]
              rw [hcons]
              exact htail
          · simp [mergeGroundAssignments?, hlook, hsame] at hmerge

/-- Package the deterministic helper at the bindings level. -/
private def mergeGround? (left right : Bindings) : Option Bindings :=
  match right.equalities with
  | [] => mergeGroundAssignments? left right.assignments
  | _ :: _ => none

/-- On canonical right-hand fragments, successful `mergeGround?` is extensional:
lookups in the result come from the right fragment when present there, and
otherwise from the left seed. -/
private theorem mergeGround_lookup_spec
    {left right out : Bindings}
    (hrightEq : right.equalities = [])
    (hkeys : (right.assignments.map Prod.fst).Nodup)
    (hmerge : mergeGround? left right = some out) :
    ∀ x,
      out.lookup x =
        match right.lookup x with
        | some a => some a
        | none => left.lookup x := by
  cases right with
  | mk assignments equalities =>
      cases hrightEq
      simpa [mergeGround?, Bindings.lookup] using
        (mergeGroundAssignments_lookup_spec (left := left) (out := out)
          (assigns := assignments) hkeys hmerge)

/-- Successful assignment-list merge is compatible on overlaps: whenever both
the left seed and the right assignment fragment bind the same variable, they
bind it to the same atom. -/
private theorem mergeGroundAssignments_overlap_agree
    {assigns : List (String × Atom)} {left out : Bindings}
    {x : String} {aL aR : Atom}
    (hkeys : (assigns.map Prod.fst).Nodup)
    (hmerge : mergeGroundAssignments? left assigns = some out)
    (hleft : left.lookup x = some aL)
    (hright : List.lookup x assigns = some aR) :
    aL = aR := by
  induction assigns generalizing left out x aL aR with
  | nil =>
      simp at hright
  | cons pair assigns ih =>
      rcases pair with ⟨v, val⟩
      have hnotmem : v ∉ assigns.map Prod.fst := by
        simpa using (List.nodup_cons.mp hkeys).1
      have hkeys' : (assigns.map Prod.fst).Nodup := by
        simpa using (List.nodup_cons.mp hkeys).2
      cases hlook : left.lookup v with
      | none =>
          have hmerge' :
              mergeGroundAssignments? (left.assign v val) assigns = some out := by
            simpa [mergeGroundAssignments?, hlook] using hmerge
          by_cases hxeq : x = v
          · subst hxeq
            have : False := by
              simp [hlook] at hleft
            exact False.elim this
          · have htail :
              List.lookup x assigns = some aR := by
                have hbeq : (x == v) = false := by simp [hxeq]
                simpa [List.lookup_cons, hbeq] using hright
            have hleft' :
                (left.assign v val).lookup x = some aL := by
              simpa [assign_lookup_ne left v val x hxeq hlook] using hleft
            exact ih hkeys' hmerge' hleft' htail
      | some prev =>
          by_cases hsame : prev = val
          · have hmerge' :
                mergeGroundAssignments? left assigns = some out := by
              simpa [mergeGroundAssignments?, hlook, hsame] using hmerge
            by_cases hxeq : x = v
            · subst hxeq
              have hhead : val = aR := by
                simp at hright
                simpa using hright
              have hprev : prev = aL := by simpa [hlook] using hleft
              rw [← hprev, hsame, hhead]
            · have htail :
                List.lookup x assigns = some aR := by
                  have hbeq : (x == v) = false := by simp [hxeq]
                  simpa [List.lookup_cons, hbeq] using hright
              exact ih hkeys' hmerge' hleft htail
          · have : False := by
              simp [mergeGroundAssignments?, hlook, hsame] at hmerge
            exact False.elim this

/-- Deterministic assignment-list merge succeeds whenever every overlap between
the seed and the assignment list already agrees on its value. This is the
existence half paired with `mergeGroundAssignments_overlap_agree`. -/
private theorem mergeGroundAssignments_exists_of_overlap_agree
    {assigns : List (String × Atom)} {left : Bindings}
    (hkeys : (assigns.map Prod.fst).Nodup)
    (hag :
      ∀ {x aL aR}, left.lookup x = some aL → List.lookup x assigns = some aR → aL = aR) :
    ∃ out, mergeGroundAssignments? left assigns = some out := by
  induction assigns generalizing left with
  | nil =>
      exact ⟨left, rfl⟩
  | cons pair assigns ih =>
      rcases pair with ⟨v, val⟩
      have hnotmem : v ∉ assigns.map Prod.fst := by
        simpa using (List.nodup_cons.mp hkeys).1
      have hkeys' : (assigns.map Prod.fst).Nodup := by
        simpa using (List.nodup_cons.mp hkeys).2
      cases hlook : left.lookup v with
      | none =>
          have hag' :
              ∀ {x aL aR},
                (left.assign v val).lookup x = some aL →
                List.lookup x assigns = some aR →
                aL = aR := by
            intro x aL aR hx htail
            by_cases hxeq : x = v
            · subst x
              have htailNone : List.lookup v assigns = none :=
                lookup_none_of_not_mem_keys hnotmem
              rw [htailNone] at htail
              cases htail
            · have hleft' : left.lookup x = some aL := by
                simpa [assign_lookup_ne left v val x hxeq hlook] using hx
              have hcons : List.lookup x ((v, val) :: assigns) = some aR := by
                have hbeq : (x == v) = false := by simp [hxeq]
                simpa [List.lookup_cons, hbeq] using htail
              exact hag hleft' hcons
          obtain ⟨out, hout⟩ := ih hkeys' hag'
          exact ⟨out, by simpa [mergeGroundAssignments?, hlook] using hout⟩
      | some prev =>
          have hsame : prev = val := by
            have hhead : List.lookup v ((v, val) :: assigns) = some val := by
              simp
            exact hag hlook hhead
          have hag' :
              ∀ {x aL aR},
                left.lookup x = some aL →
                List.lookup x assigns = some aR →
                aL = aR := by
            intro x aL aR hx htail
            have hcons : List.lookup x ((v, val) :: assigns) = some aR := by
              by_cases hxeq : x = v
              · subst x
                have : False := by
                  have htailNone : List.lookup v assigns = none :=
                    lookup_none_of_not_mem_keys hnotmem
                  rw [htailNone] at htail
                  cases htail
                exact False.elim this
              · have hbeq : (x == v) = false := by simp [hxeq]
                simpa [List.lookup_cons, hbeq] using htail
            exact hag hx hcons
          obtain ⟨out, hout⟩ := ih hkeys' hag'
          exact ⟨out, by simpa [mergeGroundAssignments?, hlook, hsame] using hout⟩

/-- Assigning a fresh key does not change which later right-hand assignments
look fresh, provided that key does not reappear later in the list. -/
private theorem filter_fresh_assign_eq
    {assigns : List (String × Atom)} {left : Bindings} {v : String} {val : Atom}
    (hlookup : left.lookup v = none)
    (hnotmem : v ∉ assigns.map Prod.fst) :
    assigns.filter (fun p => ((left.assign v val).lookup p.1).isNone) =
      assigns.filter (fun p => (left.lookup p.1).isNone) := by
  induction assigns with
  | nil => rfl
  | cons pair assigns ih =>
      rcases pair with ⟨w, a⟩
      have hwne : w ≠ v := by
        intro hwv
        subst hwv
        exact hnotmem (by simp)
      have hnotmem' : v ∉ assigns.map Prod.fst := by
        intro hv
        exact hnotmem (by simp [hv])
      have hnoneEq :
          ((left.assign v val).lookup w).isNone = (left.lookup w).isNone := by
        rw [assign_lookup_ne left v val w hwne hlookup]
      cases hfresh : (left.lookup w).isNone <;>
        simp [hnoneEq, hfresh, ih hnotmem']

/-- On a no-equalities seed, deterministic assignment-list merge under overlap
agreement produces exactly the seed assignments followed by the assignments
that were genuinely fresh at the seed, in their original right-hand order. -/
private theorem mergeGroundAssignments_eq_append_fresh_of_overlap_agree
    {assigns : List (String × Atom)} {left : Bindings}
    (hEq : left.equalities = [])
    (hkeys : (assigns.map Prod.fst).Nodup)
    (hag :
      ∀ {x aL aR}, left.lookup x = some aL → List.lookup x assigns = some aR → aL = aR) :
    mergeGroundAssignments? left assigns =
      some
        { assignments := left.assignments ++
            assigns.filter (fun p => (left.lookup p.1).isNone)
        , equalities := [] } := by
  induction assigns generalizing left with
  | nil =>
      cases left
      cases hEq
      simp [mergeGroundAssignments?]
  | cons pair assigns ih =>
      rcases pair with ⟨v, val⟩
      have hnotmem : v ∉ assigns.map Prod.fst := by
        simpa using (List.nodup_cons.mp hkeys).1
      have hkeys' : (assigns.map Prod.fst).Nodup := by
        simpa using (List.nodup_cons.mp hkeys).2
      cases hlook : left.lookup v with
      | none =>
          have hnotbound : left.isBound v = false := by
            simp [Bindings.isBound, hlook]
          have hEq' : (left.assign v val).equalities = [] := by
            simpa [Bindings.assign, hnotbound] using hEq
          have hag' :
              ∀ {x aL aR},
                (left.assign v val).lookup x = some aL →
                List.lookup x assigns = some aR →
                aL = aR := by
            intro x aL aR hx hright
            by_cases hxeq : x = v
            · subst x
              have htailNone : List.lookup v assigns = none :=
                lookup_none_of_not_mem_keys hnotmem
              rw [htailNone] at hright
              cases hright
            · have hleft' : left.lookup x = some aL := by
                simpa [assign_lookup_ne left v val x hxeq hlook] using hx
              have hcons : List.lookup x ((v, val) :: assigns) = some aR := by
                have hbeq : (x == v) = false := by simp [hxeq]
                simpa [List.lookup_cons, hbeq] using hright
              exact hag hleft' hcons
          have hfilter :
              assigns.filter (fun p => ((left.assign v val).lookup p.1).isNone) =
                assigns.filter (fun p => (left.lookup p.1).isNone) :=
            filter_fresh_assign_eq hlook hnotmem
          simp [mergeGroundAssignments?, hlook]
          rw [ih hEq' hkeys' hag', hfilter]
          simp [Bindings.assign, hnotbound, List.append_assoc]
      | some prev =>
          have hsame : prev = val := by
            have hhead : List.lookup v ((v, val) :: assigns) = some val := by
              simp
            exact hag hlook hhead
          have hag' :
              ∀ {x aL aR},
                left.lookup x = some aL →
                List.lookup x assigns = some aR →
                aL = aR := by
            intro x aL aR hx hright
            have hcons : List.lookup x ((v, val) :: assigns) = some aR := by
              by_cases hxeq : x = v
              · subst x
                have : False := by
                  have htailNone : List.lookup v assigns = none :=
                    lookup_none_of_not_mem_keys hnotmem
                  rw [htailNone] at hright
                  cases hright
                exact False.elim this
              · have hbeq : (x == v) = false := by simp [hxeq]
                simpa [List.lookup_cons, hbeq] using hright
            exact hag hx hcons
          simpa [mergeGroundAssignments?, hlook, hsame] using ih hEq hkeys' hag'

/-- Successful deterministic ground merge is compatible on overlaps:
whenever both the left seed and the right fragment bind the same variable,
they bind it to the same atom. This is the local agreement law the later
seed-composition proof needs. -/
private theorem mergeGround_overlap_agree
    {left right out : Bindings} {x : String} {aL aR : Atom}
    (hrightEq : right.equalities = [])
    (hkeys : (right.assignments.map Prod.fst).Nodup)
    (hmerge : mergeGround? left right = some out)
    (hleft : left.lookup x = some aL)
    (hright : right.lookup x = some aR) :
    aL = aR := by
  cases right with
  | mk assignments equalities =>
      cases hrightEq
      simpa [mergeGround?, Bindings.lookup] using
        (mergeGroundAssignments_overlap_agree
          (assigns := assignments) (left := left) (out := out)
          (x := x) (aL := aL) (aR := aR)
          hkeys hmerge hleft hright)

/-- The overlap-agreement criterion is also sufficient at the bindings level:
when a no-equalities right fragment with distinct keys agrees with the left
seed on every shared variable, deterministic ground merge succeeds. -/
private theorem mergeGround_exists_of_overlap_agree
    {left right : Bindings}
    (hrightEq : right.equalities = [])
    (hkeys : (right.assignments.map Prod.fst).Nodup)
    (hag :
      ∀ {x aL aR}, left.lookup x = some aL → right.lookup x = some aR → aL = aR) :
    ∃ out, mergeGround? left right = some out := by
  cases right with
  | mk assignments equalities =>
      cases hrightEq
      have hag' :
          ∀ {x aL aR},
            left.lookup x = some aL →
            List.lookup x assignments = some aR →
            aL = aR := by
        intro x aL aR hleft hright
        exact hag hleft (by simpa [Bindings.lookup] using hright)
      simpa [mergeGround?, Bindings.lookup] using
        (mergeGroundAssignments_exists_of_overlap_agree
          (assigns := assignments) (left := left) hkeys hag')

/-- A successful deterministic merge with a canonical right-hand fragment
preserves every lookup from that right fragment in the result. -/
private theorem mergeGround_extends_right_of_nodup
    {left right out : Bindings}
    (hrightEq : right.equalities = [])
    (hkeys : (right.assignments.map Prod.fst).Nodup)
    (hmerge : mergeGround? left right = some out) :
    right.Extends out := by
  intro x a hx
  have hout :=
    mergeGround_lookup_spec (left := left) (right := right) (out := out)
      hrightEq hkeys hmerge x
  rw [hx] at hout
  simpa using hout

/-- A successful deterministic merge with a canonical right-hand fragment also
preserves every lookup already present in the left seed. -/
private theorem mergeGround_extends_left_of_nodup
    {left right out : Bindings}
    (hrightEq : right.equalities = [])
    (hkeys : (right.assignments.map Prod.fst).Nodup)
    (hmerge : mergeGround? left right = some out) :
    left.Extends out := by
  intro x a hx
  by_cases hrightx : ∃ aR, right.lookup x = some aR
  · rcases hrightx with ⟨aR, hrightLook⟩
    have hagree : a = aR :=
      mergeGround_overlap_agree hrightEq hkeys hmerge hx hrightLook
    have hout :=
      mergeGround_lookup_spec (left := left) (right := right) (out := out)
        hrightEq hkeys hmerge x
    rw [hrightLook] at hout
    simpa [hagree] using hout
  · have hrightNone : right.lookup x = none := by
      cases hlook : right.lookup x with
      | none =>
          rfl
      | some aR =>
          exfalso
          exact hrightx ⟨aR, hlook⟩
    have hout :=
      mergeGround_lookup_spec (left := left) (right := right) (out := out)
        hrightEq hkeys hmerge x
    rw [hrightNone] at hout
    simpa [hx] using hout

/-- If a seed `b` merges successfully with a canonical ground fragment `mb`,
and the resulting bindings in turn merge successfully with a second canonical
ground fragment `fr`, then the middle merge `mb ⋆ fr` exists on its own. This
isolates the overlap-agreement content of seeded composition before the final
equation-level factorization law. -/
private theorem mergeGround_mid_exists_of_seeded
    {b mb c fr x : Bindings}
    (hmbEq : mb.equalities = [])
    (hmbKeys : (mb.assignments.map Prod.fst).Nodup)
    (hfrEq : fr.equalities = [])
    (hfrKeys : (fr.assignments.map Prod.fst).Nodup)
    (hc : mergeGround? b mb = some c)
    (hx : mergeGround? c fr = some x) :
    ∃ g, mergeGround? mb fr = some g := by
  have hmbc : mb.Extends c := mergeGround_extends_right_of_nodup hmbEq hmbKeys hc
  have hag :
      ∀ {v aM aF}, mb.lookup v = some aM → fr.lookup v = some aF → aM = aF := by
    intro v aM aF hmbLook hfrLook
    have hcLook : c.lookup v = some aM := hmbc v aM hmbLook
    exact mergeGround_overlap_agree hfrEq hfrKeys hx hcLook hfrLook
  exact mergeGround_exists_of_overlap_agree hfrEq hfrKeys hag

private theorem lookup_filter_some_of_nodup
    {xs : List (String × Atom)} {pred : (String × Atom) → Bool}
    {v : String} {a : Atom}
    (hkeys : (xs.map Prod.fst).Nodup)
    (h : List.lookup v (xs.filter pred) = some a) :
    List.lookup v xs = some a := by
  induction xs with
  | nil =>
      simp at h
  | cons x xs ih =>
      rcases x with ⟨k, b⟩
      have hkeys' : (xs.map Prod.fst).Nodup := by
        simpa using (List.nodup_cons.mp hkeys).2
      by_cases hk : v == k
      · have hvk : v = k := by simpa using hk
        subst k
        have hnotmem : v ∉ xs.map Prod.fst := by
          simpa using (List.nodup_cons.mp hkeys).1
        by_cases hpred : pred (v, b)
        · simp [hpred] at h
          simpa using h
        · simp [hpred] at h
          have htailNone : List.lookup v xs = none := lookup_none_of_not_mem_keys hnotmem
          have htailSome : List.lookup v xs = some a := ih hkeys' h
          rw [htailNone] at htailSome
          cases htailSome
      · by_cases hpred : pred (k, b)
        · have h' : List.lookup v (List.filter pred xs) = some a := by
            simpa [List.lookup_cons, hk, hpred] using h
          simpa [List.lookup_cons, hk] using ih hkeys' h'
        · have h' : List.lookup v (List.filter pred xs) = some a := by
            simpa [List.lookup_cons, hk, hpred] using h
          simpa [List.lookup_cons, hk] using ih hkeys' h'

private theorem keys_nodup_filter
    {xs : List (String × Atom)} {pred : (String × Atom) → Bool}
    (hkeys : (xs.map Prod.fst).Nodup) :
    ((xs.filter pred).map Prod.fst).Nodup := by
  induction xs with
  | nil =>
      simp
  | cons pair xs ih =>
      rcases pair with ⟨k, a⟩
      have hnotmem : k ∉ xs.map Prod.fst := by
        simpa using (List.nodup_cons.mp hkeys).1
      have hkeys' : (xs.map Prod.fst).Nodup := by
        simpa using (List.nodup_cons.mp hkeys).2
      by_cases hpred : pred (k, a)
      · have hnotmem' : k ∉ (xs.filter pred).map Prod.fst := by
          intro hkmem
          rcases List.mem_map.mp hkmem with ⟨p, hp, hpk⟩
          have hp' : p ∈ xs := List.mem_of_mem_filter hp
          rcases p with ⟨k', a'⟩
          simp at hpk
          subst k'
          exact hnotmem (List.mem_map.mpr ⟨(k, a'), hp', rfl⟩)
        simpa [List.filter_cons, hpred] using List.Nodup.cons hnotmem' (ih hkeys')
      · simpa [List.filter_cons, hpred] using ih hkeys'

private theorem filter_lookup_none_of_extends
    {xs : List (String × Atom)} {base ext : Bindings}
    (hext : base.Extends ext) :
    (xs.filter (fun p => (base.lookup p.1).isNone)).filter
        (fun p => (ext.lookup p.1).isNone) =
      xs.filter (fun p => (ext.lookup p.1).isNone) := by
  induction xs with
  | nil => rfl
  | cons pair xs ih =>
      rcases pair with ⟨v, a⟩
      cases hExt : (ext.lookup v).isNone with
      | false =>
          cases hBase : (base.lookup v).isNone <;>
            simp [hExt, hBase, ih]
      | true =>
          have hExtNone : ext.lookup v = none := by
            cases hlook : ext.lookup v <;> simp [hlook] at hExt ⊢
          have hBase : (base.lookup v).isNone = true := by
            cases hlook : base.lookup v with
            | none =>
                simp
            | some b =>
                have hpush : ext.lookup v = some b := hext v b hlook
                rw [hExtNone] at hpush
                cases hpush
          simp [hExt, hBase, ih]

/-- At the bindings level, deterministic ground-merge composes over
concatenated assignment fragments when both fragments have no equalities. -/
private theorem mergeGround_concat
    (left mid right : Bindings)
    (hmid : mid.equalities = []) (hright : right.equalities = []) :
    mergeGround? left { assignments := mid.assignments ++ right.assignments, equalities := [] } =
      match mergeGround? left mid with
      | some leftmid => mergeGround? leftmid right
      | none => none := by
  cases mid with
  | mk midAssignments midEqualities =>
      cases right with
      | mk rightAssignments rightEqualities =>
          cases hmid
          cases hright
          simp [mergeGround?, mergeGroundAssignments_append]

/-- On the no-equalities fragment, `mergeGround?` exactly reproduces
`mergeBindings` at fuel 2. -/
private theorem mergeGround_toList_eq_mergeBindings_two
    (left right : Bindings) (hEq : right.equalities = []) :
    (mergeGround? left right).toList = mergeBindings left right 2 := by
  cases right with
  | mk assignments equalities =>
      cases hEq
      simp [mergeGround?, mergeBindings, mergeGroundAssignments_toList_eq_detfold,
        fold_addVarBinding_fuel1_eq]

/-- At fuel 2, merging a concatenated ground/no-equalities fragment is the
same as merging the first fragment, then the second. -/
private theorem mergeBindings_two_concat
    (left mid right : Bindings)
    (hmid : mid.equalities = []) (hright : right.equalities = []) :
    mergeBindings left { assignments := mid.assignments ++ right.assignments, equalities := [] } 2 =
      (mergeBindings left mid 2).flatMap fun leftmid =>
        mergeBindings leftmid right 2 := by
  rw [← mergeGround_toList_eq_mergeBindings_two left
      { assignments := mid.assignments ++ right.assignments, equalities := [] } rfl]
  rw [mergeGround_concat left mid right hmid hright]
  rw [← mergeGround_toList_eq_mergeBindings_two left mid hmid]
  cases hmerge : mergeGround? left mid with
  | none =>
      simp
  | some leftmid =>
      simp [mergeGround_toList_eq_mergeBindings_two leftmid right hright]

/-- On the no-equalities fragment, membership in `mergeBindings ... 2` is
equivalent to the deterministic ground-merge helper returning that result. -/
private theorem mem_mergeBindings_two_iff
    {left right result : Bindings} (hEq : right.equalities = []) :
    result ∈ mergeBindings left right 2 ↔ mergeGround? left right = some result := by
  rw [← mergeGround_toList_eq_mergeBindings_two left right hEq]
  cases hmerge : mergeGround? left right with
  | none =>
      simp
  | some b =>
      simp [eq_comm]

/-- The empty bindings have no loop. -/
theorem hasLoop_empty : Bindings.empty.hasLoop = false := by
  simp [Bindings.hasLoop, Bindings.empty]

/-! ## Fuel monotonicity for the matcher family

Membership in any of the five matcher functions' results is preserved
under additional fuel (fuel only gates recursion depth; all branch
conditions are fuel-independent).  Proven as one simultaneous induction
on fuel; the list function carries accumulator-monotonicity in the same
statement (its recursion grows the accumulator). -/

/-- Pointwise list inclusion: every member of `xs` is a member of `ys`. -/
def Sub (xs ys : List Bindings) : Prop := ∀ x ∈ xs, x ∈ ys

theorem Sub.refl (xs : List Bindings) : Sub xs xs := fun _ h => h

/-- `matchAtomsList` distributes over a `flatMap`-built accumulator. This is
the structural reason seeded official matching can later be factored
seed-by-seed. -/
private theorem matchAtomsList_flatMap_acc
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

/-- Membership form of `matchAtomsList_flatMap_acc`: seeded official matching
decomposes seed-by-seed over a `flatMap`-built accumulator. -/
private theorem mem_matchAtomsList_flatMap_acc
    {α : Type} {lefts rights : List Atom} {acc : List α}
    {f : α → List Bindings} {fuel : Nat} {x : Bindings} :
    x ∈ matchAtomsList lefts rights (acc.flatMap f) fuel ↔
      ∃ a ∈ acc, x ∈ matchAtomsList lefts rights (f a) fuel := by
  rw [matchAtomsList_flatMap_acc lefts rights acc f fuel]
  simp

/-- `matchAtomsList` decomposes an accumulator into singleton-seeded runs. -/
private theorem matchAtomsList_seedwise
    (lefts rights : List Atom) (seeds : List Bindings) (fuel : Nat) :
    matchAtomsList lefts rights seeds fuel =
      seeds.flatMap (fun b => matchAtomsList lefts rights [b] fuel) := by
  simpa using
    (matchAtomsList_flatMap_acc lefts rights seeds (fun b => [b]) fuel)

/-- Membership form of `matchAtomsList_seedwise`. -/
private theorem mem_matchAtomsList_seedwise
    {lefts rights : List Atom} {seeds : List Bindings}
    {fuel : Nat} {x : Bindings} :
    x ∈ matchAtomsList lefts rights seeds fuel ↔
      ∃ b ∈ seeds, x ∈ matchAtomsList lefts rights [b] fuel := by
  rw [matchAtomsList_seedwise lefts rights seeds fuel]
  simp

theorem flatMap_sub {xs xs' : List Bindings}
    {f g : Bindings → List Bindings}
    (h_xs : Sub xs xs') (h_fg : ∀ a ∈ xs, Sub (f a) (g a)) :
    Sub (xs.flatMap f) (xs'.flatMap g) := by
  intro x hx
  obtain ⟨a, ha, hfa⟩ := List.mem_flatMap.mp hx
  exact List.mem_flatMap.mpr ⟨a, h_xs a ha, h_fg a ha x hfa⟩

private theorem foldl_flatMap_sub {α : Type} (l : List α)
    {step step' : List Bindings → α → List Bindings}
    (h_step : ∀ acc acc' a, Sub acc acc' → Sub (step acc a) (step' acc' a)) :
    ∀ {acc acc' : List Bindings}, Sub acc acc' →
      Sub (l.foldl step acc) (l.foldl step' acc') := by
  induction l with
  | nil => intro acc acc' h; simpa using h
  | cons a as ih =>
      intro acc acc' h
      simp only [List.foldl_cons]
      exact ih (h_step acc acc' a h)

/-- The simultaneous fuel-monotonicity statement. -/
theorem matcher_mono : ∀ n : Nat,
    (∀ l r, Sub (matchAtoms l r n) (matchAtoms l r (n + 1))) ∧
    (∀ ls rs acc acc', Sub acc acc' →
      Sub (matchAtomsList ls rs acc n) (matchAtomsList ls rs acc' (n + 1))) ∧
    (∀ a b, Sub (mergeBindings a b n) (mergeBindings a b (n + 1))) ∧
    (∀ b v val, Sub (addVarBinding b v val n) (addVarBinding b v val (n + 1))) ∧
    (∀ b a c, Sub (addVarEquality b a c n) (addVarEquality b a c (n + 1))) := by
  intro n
  induction n with
  | zero =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
        first
          | (intro l r x hx; simp [matchAtoms] at hx)
          | (intro ls rs acc acc' h x hx; simp [matchAtomsList] at hx)
          | (intro a b x hx; simp [mergeBindings] at hx)
          | (intro b v val x hx; simp [addVarBinding] at hx)
          | (intro b a c x hx; simp [addVarEquality] at hx)
  | succ n ih =>
      obtain ⟨ihA, ihL, ihM, ihB, ihE⟩ := ih
      have subRefl : ∀ xs : List Bindings, Sub xs xs := Sub.refl
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · -- matchAtoms: same branch taken at both fuels; recursive branch via ihL
        intro l r x hx
        simp only [matchAtoms, List.mem_filter, beq_iff_eq,
          Bool.and_eq_true] at hx ⊢
        refine ⟨?_, hx.2⟩
        have hx1 := hx.1
        -- walk the paired if-levels: identical constants close by `exact`,
        -- off-diagonals by contradiction; only the expression level
        -- (where the fuel occurs) survives
        repeat'
          first
            | exact hx1
            | exact absurd ‹_› ‹_›
            | (split at hx1 <;> split <;>
                first
                  | exact hx1
                  | exact absurd ‹_› ‹_›
                  | skip)
        -- leftover: the expression diagonal (plus one stray off-diagonal)
        all_goals
          first
            | contradiction
            | (split at hx1
               · -- expression/expression arm: the inner length-ite
                 split at hx1
                 · rename_i hlen
                   rw [if_pos hlen]
                   exact ihL _ _ _ _ (subRefl _) x hx1
                 · rename_i hlen
                   rw [if_neg hlen]
                   exact hx1
               · -- catchall arm: both sides empty
                 exact hx1)
      · -- matchAtomsList
        intro ls rs acc acc' hacc x hx
        simp only [matchAtomsList] at hx ⊢
        split at hx
        · exact hacc x hx
        · rename_i l1 ls1 r1 rs1
          exact ihL _ _ _ _
            (flatMap_sub hacc
              (fun a _ => flatMap_sub (ihA l1 r1) (fun bnd _ => ihM a bnd)))
            x hx
        · exact absurd hx (by simp)
      · -- mergeBindings
        intro a b x hx
        simp only [mergeBindings] at hx ⊢
        refine foldl_flatMap_sub b.equalities
          (fun acc acc' p h => flatMap_sub h (fun bd _ => ihE bd p.1 p.2)) ?_ x hx
        exact foldl_flatMap_sub b.assignments
          (fun acc acc' p h => flatMap_sub h (fun bd _ => ihB bd p.1 p.2))
          (subRefl [a])
      · -- addVarBinding
        intro b v val x hx
        cases hlook : b.lookup v with
        | none =>
            simp only [addVarBinding, hlook] at hx ⊢
            exact hx
        | some prev =>
            simp only [addVarBinding, hlook] at hx ⊢
            split at hx <;> rename_i heq
            · rw [if_pos heq]; exact hx
            · rw [if_neg heq]
              exact flatMap_sub (ihA _ _) (fun mb _ => ihM b mb) x hx
      · -- addVarEquality
        intro b a c x hx
        cases hA : b.lookup a with
        | none =>
            simp only [addVarEquality, hA] at hx ⊢
            exact hx
        | some av =>
            cases hC : b.lookup c with
            | none =>
                simp only [addVarEquality, hA, hC] at hx ⊢
                exact hx
            | some cv =>
                simp only [addVarEquality, hA, hC] at hx ⊢
                split at hx <;> rename_i heq
                · rw [if_pos heq]; exact hx
                · rw [if_neg heq]
                  exact flatMap_sub (ihA _ _) (fun mb _ => ihM b mb) x hx

/-- `matchAtoms` is monotone in fuel. -/
private theorem matchAtoms_mono_add
    (l r : Atom) (fuel extra : Nat) :
    Sub (matchAtoms l r fuel) (matchAtoms l r (fuel + extra)) := by
  induction extra with
  | zero =>
      simpa using Sub.refl (matchAtoms l r fuel)
  | succ extra ih =>
      have hstep := (matcher_mono (fuel + extra)).1 l r
      exact fun x hx => hstep x (ih x hx)

/-- `matchAtomsList` is monotone in fuel when the accumulator is fixed. -/
private theorem matchAtomsList_mono_add
    (ls rs : List Atom) (acc : List Bindings) (fuel extra : Nat) :
    Sub (matchAtomsList ls rs acc fuel) (matchAtomsList ls rs acc (fuel + extra)) := by
  induction extra with
  | zero =>
      simpa using Sub.refl (matchAtomsList ls rs acc fuel)
  | succ extra ih =>
      have hstep := (matcher_mono (fuel + extra)).2.1 ls rs acc acc (Sub.refl _)
      exact fun x hx => hstep x (ih x hx)

/-- `mergeBindings` is monotone in fuel. -/
private theorem mergeBindings_mono_add
    (left right : Bindings) (fuel extra : Nat) :
    Sub (mergeBindings left right fuel) (mergeBindings left right (fuel + extra)) := by
  induction extra with
  | zero =>
      simpa using Sub.refl (mergeBindings left right fuel)
  | succ extra ih =>
      have hstep := (matcher_mono (fuel + extra)).2.2.1 left right
      exact fun x hx => hstep x (ih x hx)

/-- A bridged head-step seed and a bridged tail run can be reassembled into a
single official `matchAtomsList` witness at a common larger fuel. -/
private theorem matchAtomsList_cons_of_head_tail
    {t p : Atom} {ts ps : List Atom}
    {b b' qb : Bindings} {fuelHead fuelTail : Nat}
    (hhead :
      b' ∈ (matchAtoms t p fuelHead).flatMap (fun mb => mergeBindings b mb fuelHead))
    (htail : qb ∈ matchAtomsList ts ps [b'] fuelTail) :
    ∃ fuel, qb ∈ matchAtomsList (t :: ts) (p :: ps) [b] (fuel + 1) := by
  let fuel := max fuelHead fuelTail
  have hHeadLe : fuelHead ≤ fuel := by
    dsimp [fuel]
    exact Nat.le_max_left _ _
  have hTailLe : fuelTail ≤ fuel := by
    dsimp [fuel]
    exact Nat.le_max_right _ _
  have hHeadEq : fuelHead + (fuel - fuelHead) = fuel :=
    Nat.add_sub_of_le hHeadLe
  have hTailEq : fuelTail + (fuel - fuelTail) = fuel :=
    Nat.add_sub_of_le hTailLe
  have hhead_sub :
      Sub
        ((matchAtoms t p fuelHead).flatMap fun mb => mergeBindings b mb fuelHead)
        ((matchAtoms t p fuel).flatMap fun mb => mergeBindings b mb fuel) := by
    refine flatMap_sub ?_ ?_
    · simpa [hHeadEq] using
        (matchAtoms_mono_add t p fuelHead (fuel - fuelHead))
    intro mb hmb
    simpa [hHeadEq] using
      (mergeBindings_mono_add b mb fuelHead (fuel - fuelHead))
  have hhead' :
      b' ∈ (matchAtoms t p fuel).flatMap (fun mb => mergeBindings b mb fuel) :=
    hhead_sub b' hhead
  have htail' :
      qb ∈ matchAtomsList ts ps [b'] fuel := by
    have hsub := matchAtomsList_mono_add ts ps [b'] fuelTail (fuel - fuelTail)
    simpa [hTailEq] using hsub qb htail
  have hseeded :
      qb ∈ matchAtomsList ts ps
        ((matchAtoms t p fuel).flatMap fun mb => mergeBindings b mb fuel) fuel := by
    rw [matchAtomsList_seedwise ts ps
        ((matchAtoms t p fuel).flatMap fun mb => mergeBindings b mb fuel) fuel]
    exact List.mem_flatMap.mpr ⟨b', hhead', htail'⟩
  refine ⟨fuel, ?_⟩
  simpa [matchAtomsList] using hseeded

/-- If each successful element match at a fixed `fuel` can be witnessed by an
official head-step from the same seed, then successful `simpleMatchList`
threading at that `fuel` can be witnessed by official `matchAtomsList`
threading from `[seed]`.  This packages the exact inner induction shape the
ground matcher bridge needs later. -/
private theorem simpleMatchList_ground_seeded_of_elem_bridge
    (fuel : Nat)
    (hElem :
      ∀ {p t b qb},
        GroundAtom t →
        simpleMatch p t b fuel = some qb →
          ∃ fuel',
            qb ∈ (matchAtoms t p fuel').flatMap (fun mb => mergeBindings b mb fuel')) :
    ∀ {ps ts b qb},
      (∀ t ∈ ts, GroundAtom t) →
      simpleMatch.simpleMatchList ps ts b fuel = some qb →
        ∃ fuel', qb ∈ matchAtomsList ts ps [b] fuel' := by
  intro ps
  induction ps with
  | nil =>
      intro ts b qb hground hmatch
      cases ts with
      | nil =>
          simp [simpleMatch.simpleMatchList] at hmatch
          subst hmatch
          refine ⟨1, ?_⟩
          simp [matchAtomsList]
      | cons t ts =>
          simp [simpleMatch.simpleMatchList] at hmatch
  | cons p ps ih =>
      intro ts b qb hground hmatch
      cases ts with
      | nil =>
          simp [simpleMatch.simpleMatchList] at hmatch
      | cons t ts =>
          unfold simpleMatch.simpleMatchList at hmatch
          cases hhd : simpleMatch p t b fuel with
          | none =>
              simp [hhd] at hmatch
          | some b' =>
              simp [hhd] at hmatch
              have ht : GroundAtom t := hground t (by simp)
              obtain ⟨fuelHead, hhead⟩ := hElem ht hhd
              obtain ⟨fuelTail, htail⟩ := ih
                (fun a ha => hground a (by simp [ha])) hmatch
              obtain ⟨fuel', hwhole⟩ := matchAtomsList_cons_of_head_tail hhead htail
              exact ⟨fuel' + 1, hwhole⟩

/-! ## Ground-results invariants

Matching a ground left atom produces bindings whose assignment values are
ground and whose equality list is empty — hence loop-free (`hasLoop` only
chases variable-valued assignments).  These invariants are what make the
bindings algebra of the bridge factorization tractable. -/

/-- Bindings with ground assignment values and no equalities. -/
def GroundBindings (b : Bindings) : Prop :=
  (∀ p ∈ b.assignments, GroundAtom p.2) ∧ b.equalities = []

theorem GroundBindings.empty : GroundBindings Bindings.empty :=
  ⟨by simp [Bindings.empty], rfl⟩

theorem GroundBindings.assign {b : Bindings} {v : String} {val : Atom}
    (hb : GroundBindings b) (hval : GroundAtom val) :
    GroundBindings (b.assign v val) := by
  refine ⟨?_, hb.2⟩
  intro p hp
  simp only [Bindings.assign] at hp
  split at hp
  · obtain ⟨q, hq, hpq⟩ := List.mem_map.mp hp
    split at hpq
    · exact hpq ▸ hval
    · exact hpq ▸ hb.1 q hq
  · rcases List.mem_append.mp hp with h | h
    · exact hb.1 p h
    · simp at h
      rw [h]
      exact hval

/-- Explicit key-uniqueness side invariant for bindings assignments.
This is documented in `Types.lean` and is the missing premise the
ground-merge algebra needs to speak honestly about canonical results. -/
private def Bindings.KeysNodup (b : Bindings) : Prop :=
  (b.assignments.map Prod.fst).Nodup

private theorem lookup_none_not_mem_keys
    {xs : List (String × Atom)} {v : String}
    (h : List.lookup v xs = none) :
    v ∉ xs.map Prod.fst := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rcases x with ⟨k, a⟩
      by_cases hk : v == k
      · have : False := by
          simp [List.lookup_cons, hk] at h
        exact False.elim this
      · have htail : List.lookup v xs = none := by
          simpa [List.lookup_cons, hk] using h
        have hneq : v ≠ k := by
          simpa using hk
        simp [hneq, ih htail]

private theorem Bindings.KeysNodup.empty :
    Bindings.KeysNodup Bindings.empty := by
  simp [Bindings.KeysNodup, Bindings.empty]

private theorem Bindings.KeysNodup.assign
    {b : Bindings} {v : String} {val : Atom}
    (hkeys : Bindings.KeysNodup b) :
    Bindings.KeysNodup (b.assign v val) := by
  unfold Bindings.KeysNodup at hkeys ⊢
  by_cases hbound : b.isBound v
  · have hmap :
        List.map (Prod.fst ∘ fun x => if x.1 = v then (x.1, val) else x) b.assignments =
          List.map Prod.fst b.assignments := by
      induction b.assignments with
      | nil => rfl
      | cons x xs ih =>
          rcases x with ⟨k, a⟩
          by_cases hk : k = v
          · simp [hk, ih]
          · simp [hk, ih]
    simp [Bindings.assign, hbound]
    rw [hmap]
    exact hkeys
  · have hlookup_none : b.lookup v = none := by
      unfold Bindings.isBound at hbound
      cases hlook : b.lookup v <;> simp [hlook] at hbound
      case none => exact rfl
    have hnotmem : v ∉ b.assignments.map Prod.fst :=
      lookup_none_not_mem_keys hlookup_none
    simp [Bindings.assign, hbound]
    rw [← List.concat_eq_append]
    exact List.Nodup.concat hnotmem hkeys

/-- Ground bindings together with the documented key-uniqueness discipline.
This is the honest strengthening needed for extensional merge laws. -/
private def GroundBindingsCanon (b : Bindings) : Prop :=
  GroundBindings b ∧ Bindings.KeysNodup b

private theorem GroundBindingsCanon.empty : GroundBindingsCanon Bindings.empty :=
  ⟨GroundBindings.empty, Bindings.KeysNodup.empty⟩

private theorem GroundBindingsCanon.assign {b : Bindings} {v : String} {val : Atom}
    (hb : GroundBindingsCanon b) (hval : GroundAtom val) :
    GroundBindingsCanon (b.assign v val) := by
  exact ⟨GroundBindings.assign hb.1 hval, Bindings.KeysNodup.assign hb.2⟩

/-- If a suffix assignment list has pairwise-distinct keys, is fresh with
respect to a seed, and the seed carries no equalities, then the deterministic
ground-merge helper just appends that suffix.  This is the canonical
empty-seed/seed-extension behavior the later factorization algebra relies on. -/
private theorem mergeGroundAssignments_append_fresh
    {seed : Bindings} {rest : List (String × Atom)}
    (hEq : seed.equalities = [])
    (hkeysSeed : Bindings.KeysNodup seed)
    (hkeysRest : (rest.map Prod.fst).Nodup)
    (hfresh : ∀ v, v ∈ rest.map Prod.fst → seed.lookup v = none) :
    mergeGroundAssignments? seed rest =
      some { assignments := seed.assignments ++ rest, equalities := [] } := by
  induction rest generalizing seed with
  | nil =>
      cases seed
      cases hEq
      simp [mergeGroundAssignments?]
  | cons pair rest ih =>
      rcases pair with ⟨v, val⟩
      have hlookup : seed.lookup v = none := hfresh v (by simp)
      have hnotbound : seed.isBound v = false := by
        simp [Bindings.isBound, hlookup]
      have hnotmemRest : v ∉ rest.map Prod.fst := by
        simpa using (List.nodup_cons.mp hkeysRest).1
      have hkeysRest' : (rest.map Prod.fst).Nodup := by
        simpa using (List.nodup_cons.mp hkeysRest).2
      have hEq' : (seed.assign v val).equalities = [] := by
        simpa [Bindings.assign, hnotbound] using hEq
      have hfresh' : ∀ w, w ∈ rest.map Prod.fst → (seed.assign v val).lookup w = none := by
        intro w hw
        have hwSeed : seed.lookup w = none := hfresh w (by simp [hw])
        have hwne : w ≠ v := by
          intro hwv
          subst hwv
          exact hnotmemRest hw
        simpa [hwSeed] using assign_lookup_ne seed v val w hwne hlookup
      simp [mergeGroundAssignments?, hlookup]
      simpa [Bindings.assign, hnotbound, List.append_assoc] using
        (ih hEq' (Bindings.KeysNodup.assign hkeysSeed) hkeysRest' hfresh')

/-- Canonical ground bindings merge into the empty seed without change. -/
private theorem mergeGround_empty_left_of_canon
    {b : Bindings} (hb : GroundBindingsCanon b) :
    mergeGround? Bindings.empty b = some b := by
  rcases b with ⟨assignments, equalities⟩
  have hEq : equalities = [] := hb.1.2
  cases hEq
  simp [mergeGround?, Bindings.empty]
  exact mergeGroundAssignments_append_fresh
    (seed := Bindings.empty)
    (rest := assignments)
    rfl
    Bindings.KeysNodup.empty
    hb.2
    (by
      intro v hv
      simp [Bindings.empty, Bindings.lookup])

/-- At fuel 2, canonical ground bindings merged into the empty seed reproduce
the same bindings as a singleton result. -/
private theorem mergeBindings_empty_left_two_of_canon
    {b : Bindings} (hb : GroundBindingsCanon b) :
    mergeBindings Bindings.empty b 2 = [b] := by
  rw [← mergeGround_toList_eq_mergeBindings_two Bindings.empty b hb.1.2]
  simp [mergeGround_empty_left_of_canon hb]

/-- Canonical ground bindings survive re-merging into the empty seed at any
fuel at least `2`. This packages the empty-seed self-membership fact in the
shape later head/tail reassembly lemmas want. -/
private theorem mergeBindings_empty_left_mem_of_canon
    {b : Bindings} (hb : GroundBindingsCanon b) (extra : Nat) :
    b ∈ mergeBindings Bindings.empty b (2 + extra) := by
  have hbase : b ∈ mergeBindings Bindings.empty b 2 := by
    rw [mergeBindings_empty_left_two_of_canon hb]
    simp
  have hsub := mergeBindings_mono_add Bindings.empty b 2 extra
  exact hsub b hbase

/-- Ground/canonical head reassembly into an empty-seeded official list run:
if a canonical ground head match `mb` is available and the tail runs from
`[mb]`, then the whole run can be rebuilt from the empty seed at some common
fuel. This is the exact assembly shape the singleton-seed factorization uses
after composing merges. -/
private theorem matchAtomsList_cons_of_head_tail_empty_ground
    {t p : Atom} {ts ps : List Atom}
    {mb qb : Bindings} {fuelHead fuelTail : Nat}
    (hmbCanon : GroundBindingsCanon mb)
    (hhead : mb ∈ matchAtoms t p fuelHead)
    (htail : qb ∈ matchAtomsList ts ps [mb] fuelTail) :
    ∃ fuel, qb ∈ matchAtomsList (t :: ts) (p :: ps) [Bindings.empty] (fuel + 1) := by
  let fuel := max (max fuelHead fuelTail) 2
  have hHeadLe : fuelHead ≤ fuel := by
    dsimp [fuel]
    exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have hTailLe : fuelTail ≤ fuel := by
    dsimp [fuel]
    exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  have hhead' : mb ∈ matchAtoms t p fuel := by
    have hEq : fuelHead + (fuel - fuelHead) = fuel := Nat.add_sub_of_le hHeadLe
    simpa [hEq] using
      (matchAtoms_mono_add t p fuelHead (fuel - fuelHead)) mb hhead
  have htail' : qb ∈ matchAtomsList ts ps [mb] fuel := by
    have hEq : fuelTail + (fuel - fuelTail) = fuel := Nat.add_sub_of_le hTailLe
    simpa [hEq] using
      (matchAtomsList_mono_add ts ps [mb] fuelTail (fuel - fuelTail)) qb htail
  have hFuelGe2 : 2 ≤ fuel := by
    dsimp [fuel]
    exact Nat.le_max_right _ _
  obtain ⟨extra, hExtra⟩ := Nat.exists_eq_add_of_le hFuelGe2
  have hseed : mb ∈ mergeBindings Bindings.empty mb fuel := by
    rw [hExtra]
    exact mergeBindings_empty_left_mem_of_canon hmbCanon extra
  have hheadSeed :
      mb ∈ (matchAtoms t p fuel).flatMap
        (fun mb0 => mergeBindings Bindings.empty mb0 fuel) :=
    List.mem_flatMap.mpr ⟨mb, hhead', hseed⟩
  exact matchAtomsList_cons_of_head_tail hheadSeed htail'

private theorem lookup_some_mem_assignments {xs : List (String × Atom)}
    {v : String} {a : Atom} (h : List.lookup v xs = some a) :
    (v, a) ∈ xs := by
  induction xs with
  | nil => simp at h
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

private theorem lookup_some_of_mem_assignment {xs : List (String × Atom)}
    {v : String} {a : Atom} (hmem : (v, a) ∈ xs) :
    ∃ a', List.lookup v xs = some a' := by
  induction xs with
  | nil => cases hmem
  | cons x xs ih =>
      rcases x with ⟨k, b⟩
      simp at hmem
      rcases hmem with h | h
      · rcases h with ⟨rfl, rfl⟩
        refine ⟨a, ?_⟩
        simp
      · by_cases hk : v == k
        · exact ⟨b, by simp [List.lookup_cons, hk]⟩
        · rcases ih h with ⟨a', ha'⟩
          exact ⟨a', by simp [List.lookup_cons, hk, ha']⟩

private theorem lookup_ground {b : Bindings} (hb : GroundBindings b)
    {v : String} {a : Atom} (h : b.lookup v = some a) : GroundAtom a := by
  exact hb.1 (v, a) (lookup_some_mem_assignments h)

/-- Ground bindings cannot have variable loops: every successful lookup
returns a ground atom, and ground atoms are never variables, so the first
`hasLoopFrom` step always stops. -/
theorem GroundBindings.hasLoop_false {b : Bindings} (hb : GroundBindings b) :
    b.hasLoop = false := by
  unfold Mettapedia.Languages.MeTTa.HE.Bindings.hasLoop
  rw [List.any_eq_false]
  intro p hp
  rcases p with ⟨v, val⟩
  simp
  rcases lookup_some_of_mem_assignment hp with ⟨a', hlookup⟩
  have hg : GroundAtom a' := lookup_ground hb hlookup
  cases a' with
  | var w =>
      exact (GroundAtom.not_var hg).elim
  | symbol s =>
      unfold Mettapedia.Languages.MeTTa.HE.Bindings.hasLoop.hasLoopFrom
      simp [Bindings.lookup, hlookup]
  | grounded g =>
      unfold Mettapedia.Languages.MeTTa.HE.Bindings.hasLoop.hasLoopFrom
      simp [Bindings.lookup, hlookup]
  | expression es =>
      unfold Mettapedia.Languages.MeTTa.HE.Bindings.hasLoop.hasLoopFrom
      simp [Bindings.lookup, hlookup]

private def collectVarsListAux (es : List Atom) (fuel : Nat) : List String :=
  match es with
  | [] => []
  | a :: as => collectVars a fuel ++ collectVarsListAux as fuel

private theorem collectVarsList_eq_aux (es : List Atom) (fuel : Nat) :
    collectVars.collectVarsList es fuel = collectVarsListAux es fuel := by
  induction es with
  | nil =>
      rfl
  | cons a as ih =>
      simp [collectVars.collectVarsList, collectVarsListAux, ih]

private theorem collectVars_expr_eq_aux (es : List Atom) (fuel : Nat) :
    collectVars (.expression es) (fuel + 1) = collectVarsListAux es fuel := by
  simp [collectVars, collectVarsList_eq_aux]

/-- On ground matcher bindings, `Bindings.apply` depends only on the lookups
of variables that syntactically occur in the atom being substituted.

Positive example:
- if `b₂` agrees with `b₁` on every variable in `body`, then applying either
  bindings set to `body` yields the same substituted atom.

Negative example:
- this theorem is intentionally restricted to *ground* `b₁`; without that,
  a variable in `body` could resolve through an extra indirection not
  mentioned syntactically in `body` itself. -/
private theorem apply_eq_of_lookup_eq_on_collectVars :
    ∀ fuel : Nat,
      (∀ {a : Atom} {b₁ b₂ : Bindings},
        GroundBindings b₁ →
        (∀ v, v ∈ collectVars a fuel → b₂.lookup v = b₁.lookup v) →
        b₂.apply a fuel = b₁.apply a fuel) ∧
      (∀ {es : List Atom} {b₁ b₂ : Bindings},
        GroundBindings b₁ →
        (∀ v, v ∈ collectVarsListAux es fuel → b₂.lookup v = b₁.lookup v) →
        es.map (b₂.apply · fuel) = es.map (b₁.apply · fuel)) := by
  intro fuel
  induction fuel with
  | zero =>
      refine ⟨?_, ?_⟩
      · intro a b₁ b₂ _ _
        simp [Bindings.apply]
      · intro es b₁ b₂ _ _
        induction es with
        | nil => rfl
        | cons a as ih => simp [Bindings.apply]
  | succ n ih =>
      obtain ⟨ihAtom, ihList⟩ := ih
      have hAtom :
          ∀ {a : Atom} {b₁ b₂ : Bindings},
            GroundBindings b₁ →
            (∀ v, v ∈ collectVars a (n + 1) → b₂.lookup v = b₁.lookup v) →
            b₂.apply a (n + 1) = b₁.apply a (n + 1) := by
        intro a b₁ b₂ hb hagree
        cases a with
        | symbol s =>
            simp [Bindings.apply]
        | grounded g =>
            simp [Bindings.apply]
        | var v =>
            have hlookEq : b₂.lookup v = b₁.lookup v := by
              exact hagree v (by simp [collectVars])
            cases h₁ : b₁.lookup v with
            | none =>
                have h₂ : b₂.lookup v = none := by
                  rw [h₁] at hlookEq
                  exact hlookEq
                cases n with
                | zero =>
                    simp [Bindings.apply, Bindings.resolve]
                | succ m =>
                    simp [Bindings.apply, Bindings.resolve, h₁, h₂]
            | some val =>
                have h₂ : b₂.lookup v = some val := by
                  rw [h₁] at hlookEq
                  exact hlookEq
                have hground : GroundAtom val := lookup_ground hb h₁
                cases val with
                | var w =>
                    exact (GroundAtom.not_var hground).elim
                | symbol s =>
                    cases n with
                    | zero =>
                        simp [Bindings.apply, Bindings.resolve]
                    | succ m =>
                        simp [Bindings.apply, Bindings.resolve, h₁, h₂]
                | grounded g =>
                    cases n with
                    | zero =>
                        simp [Bindings.apply, Bindings.resolve]
                    | succ m =>
                        simp [Bindings.apply, Bindings.resolve, h₁, h₂]
                | expression es =>
                    cases n with
                    | zero =>
                        simp [Bindings.apply, Bindings.resolve]
                    | succ m =>
                        simp [Bindings.apply, Bindings.resolve, h₁, h₂]
        | expression es =>
            have hvars :
                ∀ v, v ∈ collectVarsListAux es n → b₂.lookup v = b₁.lookup v := by
              intro v hv
              exact hagree v (by simpa [collectVars_expr_eq_aux es n] using hv)
            have hmap := ihList (es := es) (b₁ := b₁) (b₂ := b₂) hb hvars
            simpa [Bindings.apply] using congrArg Atom.expression hmap
      have hList :
          ∀ {es : List Atom} {b₁ b₂ : Bindings},
            GroundBindings b₁ →
            (∀ v, v ∈ collectVarsListAux es (n + 1) → b₂.lookup v = b₁.lookup v) →
            es.map (b₂.apply · (n + 1)) = es.map (b₁.apply · (n + 1)) := by
        intro es b₁ b₂ hb hagree
        induction es with
        | nil =>
            rfl
        | cons a as ihEs =>
            have hHead :
                b₂.apply a (n + 1) = b₁.apply a (n + 1) := by
              apply hAtom hb
              intro v hv
              exact hagree v (by simp [collectVarsListAux, hv])
            have hTail :
                as.map (b₂.apply · (n + 1)) = as.map (b₁.apply · (n + 1)) := by
              exact ihEs
                (fun v hv => hagree v (by simp [collectVarsListAux, hv]))
            simp [hHead, hTail]
      exact ⟨hAtom, hList⟩

private theorem apply_eq_of_lookup_eq_on_collectVars_atom
    {a : Atom} {b₁ b₂ : Bindings} {fuel : Nat}
    (hb₁ : GroundBindings b₁)
    (hagree : ∀ v, v ∈ collectVars a fuel → b₂.lookup v = b₁.lookup v) :
    b₂.apply a fuel = b₁.apply a fuel :=
  (apply_eq_of_lookup_eq_on_collectVars fuel).1 hb₁ hagree

/-- If a deterministic no-equalities merge adds only bindings on variable
names absent from a body, then substituting that body is unchanged compared
to substituting with the original ground matcher bindings alone. -/
private theorem apply_eq_of_mergeGround_irrel
    {body : Atom} {mb qb merged : Bindings} {fuel : Nat}
    (hmb : GroundBindings mb)
    (hqbEq : qb.equalities = [])
    (hqbKeys : (qb.assignments.map Prod.fst).Nodup)
    (hmerge : mergeGround? mb qb = some merged)
    (habsent : ∀ v, v ∈ collectVars body fuel → qb.lookup v = none) :
    merged.apply body fuel = mb.apply body fuel := by
  apply apply_eq_of_lookup_eq_on_collectVars_atom hmb
  intro v hv
  have hspec :=
    mergeGround_lookup_spec (left := mb) (right := qb) (out := merged)
      hqbEq hqbKeys hmerge v
  simpa [habsent v hv] using hspec

/-- Once the factorization theorem is known for singleton seeds, it lifts
immediately to arbitrary seed lists via `matchAtomsList_seedwise`. -/
private theorem matchAtomsList_lift_singleton_factor
    {lefts rights : List Atom} {fuel : Nat}
    (hsingle :
      ∀ {b x : Bindings},
        GroundBindings b →
        x ∈ matchAtomsList lefts rights [b] fuel →
          ∃ fr,
            fr ∈ matchAtomsList lefts rights [Bindings.empty] fuel ∧
            x ∈ mergeBindings b fr 2) :
    ∀ {seeds : List Bindings} {x : Bindings},
      (∀ b ∈ seeds, GroundBindings b) →
      x ∈ matchAtomsList lefts rights seeds fuel →
        ∃ b ∈ seeds, ∃ fr,
          fr ∈ matchAtomsList lefts rights [Bindings.empty] fuel ∧
          x ∈ mergeBindings b fr 2 := by
  intro seeds x hseeds hx
  obtain ⟨b, hb, hx_single⟩ := (mem_matchAtomsList_seedwise).mp hx
  obtain ⟨fr, hfr, hmerge⟩ := hsingle (hseeds b hb) hx_single
  exact ⟨b, hb, fr, hfr, hmerge⟩

/-! ## Ground-result preservation for the official matcher

When the scrutinee side of the official matcher is ground, every
successful matcher result contains only ground assignment values and no
equalities.  This is the key invariant needed to factor the official
matcher through the coarse one-way matcher on ground targets. -/

theorem matcher_ground : ∀ n : Nat,
    (∀ left right result,
      GroundAtom left →
      result ∈ matchAtoms left right n →
      GroundBindings result) ∧
    (∀ lefts rights acc result,
      (∀ p ∈ lefts, GroundAtom p) →
      (∀ b ∈ acc, GroundBindings b) →
      result ∈ matchAtomsList lefts rights acc n →
      GroundBindings result) ∧
    (∀ left right result,
      GroundBindings left →
      GroundBindings right →
      result ∈ mergeBindings left right n →
      GroundBindings result) ∧
    (∀ b v val result,
      GroundBindings b →
      GroundAtom val →
      result ∈ addVarBinding b v val n →
      GroundBindings result) := by
  intro n
  induction n with
  | zero =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro left right result hleft hmem
        simp [matchAtoms] at hmem
      · intro lefts rights acc result hlefts hacc hmem
        simp [matchAtomsList] at hmem
      · intro left right result hleft hright hmem
        simp [mergeBindings] at hmem
      · intro b v val result hb hval hmem
        simp [addVarBinding] at hmem
  | succ n ih =>
      obtain ⟨ihA, ihL, ihM, ihB⟩ := ih
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro left right result hleft hmem
        cases left with
        | var v =>
            exact (GroundAtom.not_var hleft).elim
        | symbol s =>
            cases right with
            | var v =>
                have hmem' := by
                  simpa [matchAtoms, getMetaType, Atom.symbolType] using hmem
                rcases hmem' with ⟨⟨_, rfl⟩, _⟩
                exact GroundBindings.assign GroundBindings.empty (.symbol s)
            | symbol t =>
                have hmem' := by
                  simpa [matchAtoms, getMetaType, Atom.symbolType] using hmem
                rcases hmem' with ⟨⟨_, rfl⟩, _⟩
                exact GroundBindings.empty
            | grounded g =>
                simp [matchAtoms, getMetaType, Atom.symbolType, Atom.groundedType] at hmem
            | expression es =>
                simp [matchAtoms, getMetaType, Atom.symbolType, Atom.expressionType] at hmem
        | grounded g =>
            cases right with
            | var v =>
                have hmem' := by
                  simpa [matchAtoms, getMetaType, Atom.groundedType] using hmem
                rcases hmem' with ⟨⟨_, rfl⟩, _⟩
                exact GroundBindings.assign GroundBindings.empty (.grounded g)
            | symbol s =>
                simp [matchAtoms, getMetaType, Atom.groundedType, Atom.symbolType] at hmem
            | grounded h =>
                have hmem' := by
                  simpa [matchAtoms, getMetaType, Atom.groundedType] using hmem
                rcases hmem' with ⟨⟨_, rfl⟩, _⟩
                exact GroundBindings.empty
            | expression es =>
                simp [matchAtoms, getMetaType, Atom.groundedType, Atom.expressionType] at hmem
        | expression lefts =>
            cases right with
            | var v =>
                have hmem' := by
                  simpa [matchAtoms, getMetaType, Atom.expressionType] using hmem
                rcases hmem' with ⟨⟨_, rfl⟩, _⟩
                exact GroundBindings.assign GroundBindings.empty hleft
            | symbol s =>
                simp [matchAtoms, getMetaType, Atom.expressionType, Atom.symbolType] at hmem
            | grounded g =>
                simp [matchAtoms, getMetaType, Atom.expressionType, Atom.groundedType] at hmem
            | expression rights =>
                have hchild : ∀ p ∈ lefts, GroundAtom p := by
                  intro p hp
                  exact GroundAtom.elem hleft hp
                have hmem' := by
                  simpa [matchAtoms, getMetaType, Atom.expressionType] using hmem
                rcases hmem' with ⟨⟨_, hraw⟩, _⟩
                exact ihL lefts rights [Bindings.empty] result hchild
                  (by
                    intro b hb
                    simp at hb
                    rcases hb with rfl
                    exact GroundBindings.empty)
                  hraw
      · intro lefts rights acc result hlefts hacc hmem
        cases lefts with
        | nil =>
            cases rights with
            | nil =>
                simpa [matchAtomsList] using hacc result hmem
            | cons r rs =>
                simp [matchAtomsList] at hmem
        | cons left lefts =>
            cases rights with
            | nil =>
                simp [matchAtomsList] at hmem
            | cons right rights =>
                simp only [matchAtomsList] at hmem
                have hnext : ∀ b ∈ acc.flatMap (fun a => (matchAtoms left right n).flatMap fun mb =>
                    mergeBindings a mb n), GroundBindings b := by
                  intro b hb
                  rcases List.mem_flatMap.mp hb with ⟨a, ha, hb⟩
                  rcases List.mem_flatMap.mp hb with ⟨mb, hmb, hmerge⟩
                  have hga : GroundBindings a := hacc a ha
                  have hgm : GroundBindings mb := ihA left right mb (hlefts left (by simp)) hmb
                  exact ihM a mb b hga hgm hmerge
                exact ihL lefts rights _ result
                  (by
                    intro p hp
                    exact hlefts p (by simp [hp]))
                  hnext
                  hmem
      · intro left right result hleft hright hmem
        have hassign :
            ∀ (assigns : List (String × Atom)) (acc : List Bindings) result,
              (∀ p : String × Atom, p ∈ assigns → GroundAtom p.2) →
              (∀ b ∈ acc, GroundBindings b) →
              result ∈ List.foldl
                (fun acc (v, val) => acc.flatMap fun b => addVarBinding b v val n) acc assigns →
              GroundBindings result := by
          intro assigns
          induction assigns with
          | nil =>
              intro acc result hground hacc hres
              simpa using hacc result hres
          | cons pair assigns ihAssigns =>
              rcases pair with ⟨v, val⟩
              intro acc result hground hacc hres
              simp only [List.foldl_cons] at hres
              have hval : GroundAtom val := hground (v, val) (by simp)
              have hacc' : ∀ b ∈ acc.flatMap (fun b => addVarBinding b v val n), GroundBindings b := by
                intro b hb
                rcases List.mem_flatMap.mp hb with ⟨b0, hb0, hb1⟩
                exact ihB b0 v val b (hacc b0 hb0) hval hb1
              exact ihAssigns _ _ (by
                intro p hp
                exact hground p (by simp [hp])) hacc' hres
        have heqs : right.equalities = [] := hright.2
        simp only [mergeBindings, heqs, List.foldl_nil] at hmem
        exact hassign right.assignments [left] result hright.1
          (by
            intro b hb
            simp at hb
            rcases hb with rfl
            exact hleft)
          hmem
      · intro b v val result hb hval hmem
        cases hlook : b.lookup v with
        | none =>
            simp [addVarBinding, hlook] at hmem
            rcases hmem with rfl
            exact GroundBindings.assign hb hval
        | some prev =>
            simp only [addVarBinding, hlook] at hmem
            split at hmem <;> rename_i hsame
            · simp at hmem
              rcases hmem with rfl
              exact hb
            · rcases List.mem_flatMap.mp hmem with ⟨mb, hmb, hmerge⟩
              have hprev : GroundAtom prev := lookup_ground hb hlook
              have hmb : GroundBindings mb := ihA prev val mb hprev hmb
              exact ihM b mb result hb hmb hmerge

/-- Filtering by `!hasLoop` is inert on lists of ground bindings. -/
private theorem filter_hasLoop_eq_self (xs : List Bindings)
    (hxs : ∀ b ∈ xs, GroundBindings b) :
    xs.filter (fun b => !b.hasLoop) = xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      have hb : GroundBindings b := hxs b (by simp)
      have htail : ∀ b' ∈ xs, GroundBindings b' := by
        intro b' hb'
        exact hxs b' (by simp [hb'])
      simp [GroundBindings.hasLoop_false hb, ih htail]

/-- On ground-left expression matching, the top-level `hasLoop` filter is
inert: every list result is already loop-free by `matcher_ground`. -/
theorem matchAtoms_ground_expr_filter_free
    (lefts rights : List Atom) (n : Nat)
    (hlefts : ∀ p ∈ lefts, GroundAtom p) :
    matchAtoms (.expression lefts) (.expression rights) (n + 1) =
      if lefts.length == rights.length then
        matchAtomsList lefts rights [Bindings.empty] n
      else [] := by
  have hmatchers := matcher_ground n
  rcases hmatchers with ⟨_, hList, _, _⟩
  simp [matchAtoms, getMetaType, Atom.expressionType]
  intro b hlen hb
  exact GroundBindings.hasLoop_false <|
    hList lefts rights [Bindings.empty] b hlefts
      (by
        intro b' hb'
        simp at hb'
        rcases hb' with rfl
        exact GroundBindings.empty)
      hb

/-- Ground scrutinee against a variable pattern is exact assignment, with the
top-level `hasLoop` filter inert by groundness. -/
theorem matchAtoms_ground_var_exact
    (left : Atom) (v : String) (n : Nat)
    (hleft : GroundAtom left) :
    matchAtoms left (.var v) (n + 1) = [Bindings.empty.assign v left] := by
  cases left with
  | var w =>
      exact (GroundAtom.not_var hleft).elim
  | symbol s =>
      have hloop :
          (Bindings.empty.assign v (.symbol s)).hasLoop = false :=
        GroundBindings.hasLoop_false
          (GroundBindings.assign GroundBindings.empty (.symbol s))
      simp [matchAtoms, getMetaType, Atom.symbolType, Atom.variableType, hloop]
  | grounded g =>
      have hloop :
          (Bindings.empty.assign v (.grounded g)).hasLoop = false :=
        GroundBindings.hasLoop_false
          (GroundBindings.assign GroundBindings.empty (.grounded g))
      simp [matchAtoms, getMetaType, Atom.groundedType, Atom.variableType, hloop]
  | expression es =>
      have hloop :
          (Bindings.empty.assign v (.expression es)).hasLoop = false :=
        GroundBindings.hasLoop_false
          (GroundBindings.assign GroundBindings.empty hleft)
      simp [matchAtoms, getMetaType, Atom.expressionType, Atom.variableType, hloop]

/-- On the ground fragment, any successful official atom match returns the
empty bindings and therefore witnesses actual atom equality.  The list form is
specialized to the empty seed because that is the official matcher shape used
by `matchAtoms` on expression nodes. -/
private theorem ground_matchAtoms_mem_empty_eq : ∀ n : Nat,
    (∀ left right result,
      GroundAtom left →
      GroundAtom right →
      result ∈ matchAtoms left right (n + 1) →
        result = Bindings.empty ∧ left = right) ∧
    (∀ lefts rights result,
      (∀ p ∈ lefts, GroundAtom p) →
      (∀ p ∈ rights, GroundAtom p) →
      result ∈ matchAtomsList lefts rights [Bindings.empty] (n + 1) →
        result = Bindings.empty ∧ lefts = rights) := by
  intro n
  induction n with
  | zero =>
      refine ⟨?_, ?_⟩
      · intro left right result hleft hright hmem
        cases left with
        | var v =>
            exact (GroundAtom.not_var hleft).elim
        | symbol s =>
            cases right with
            | var v =>
                exact (GroundAtom.not_var hright).elim
            | symbol t =>
                have hmem' : (s = t ∧ result = Bindings.empty) ∧ result.hasLoop = false := by
                  simpa [matchAtoms, getMetaType, Atom.symbolType] using hmem
                rcases hmem' with ⟨⟨hst, rfl⟩, _⟩
                exact ⟨rfl, by simpa using hst⟩
            | grounded g =>
                simp [matchAtoms, getMetaType, Atom.symbolType, Atom.groundedType] at hmem
            | expression es =>
                simp [matchAtoms, getMetaType, Atom.symbolType, Atom.expressionType] at hmem
        | grounded g =>
            cases right with
            | var v =>
                exact (GroundAtom.not_var hright).elim
            | symbol s =>
                simp [matchAtoms, getMetaType, Atom.groundedType, Atom.symbolType] at hmem
            | grounded h =>
                have hmem' : (g = h ∧ result = Bindings.empty) ∧ result.hasLoop = false := by
                  simpa [matchAtoms, getMetaType, Atom.groundedType] using hmem
                rcases hmem' with ⟨⟨hgh, rfl⟩, _⟩
                exact ⟨rfl, by simpa using hgh⟩
            | expression es =>
                simp [matchAtoms, getMetaType, Atom.groundedType, Atom.expressionType] at hmem
        | expression ls =>
            cases right with
            | var v =>
                exact (GroundAtom.not_var hright).elim
            | symbol s =>
                simp [matchAtoms, getMetaType, Atom.expressionType, Atom.symbolType] at hmem
            | grounded g =>
                simp [matchAtoms, getMetaType, Atom.expressionType, Atom.groundedType] at hmem
            | expression rs =>
                simp [matchAtoms, getMetaType, Atom.expressionType, matchAtomsList] at hmem
      · intro lefts rights result hlefts hrights hmem
        cases lefts with
        | nil =>
            cases rights with
            | nil =>
                simp [matchAtomsList] at hmem
                exact ⟨hmem, rfl⟩
            | cons r rs =>
                simp [matchAtomsList] at hmem
        | cons l ls =>
            cases rights with
            | nil =>
                simp [matchAtomsList] at hmem
            | cons r rs =>
                simp [matchAtomsList] at hmem
  | succ n ih =>
      obtain ⟨ihA, ihL⟩ := ih
      refine ⟨?_, ?_⟩
      · intro left right result hleft hright hmem
        cases left with
        | var v =>
            exact (GroundAtom.not_var hleft).elim
        | symbol s =>
            cases right with
            | var v =>
                exact (GroundAtom.not_var hright).elim
            | symbol t =>
                have hmem' : (s = t ∧ result = Bindings.empty) ∧ result.hasLoop = false := by
                  simpa [matchAtoms, getMetaType, Atom.symbolType] using hmem
                rcases hmem' with ⟨⟨hst, rfl⟩, _⟩
                exact ⟨rfl, by simpa using hst⟩
            | grounded g =>
                simp [matchAtoms, getMetaType, Atom.symbolType, Atom.groundedType] at hmem
            | expression es =>
                simp [matchAtoms, getMetaType, Atom.symbolType, Atom.expressionType] at hmem
        | grounded g =>
            cases right with
            | var v =>
                exact (GroundAtom.not_var hright).elim
            | symbol s =>
                simp [matchAtoms, getMetaType, Atom.groundedType, Atom.symbolType] at hmem
            | grounded h =>
                have hmem' : (g = h ∧ result = Bindings.empty) ∧ result.hasLoop = false := by
                  simpa [matchAtoms, getMetaType, Atom.groundedType] using hmem
                rcases hmem' with ⟨⟨hgh, rfl⟩, _⟩
                exact ⟨rfl, by simpa using hgh⟩
            | expression es =>
                simp [matchAtoms, getMetaType, Atom.groundedType, Atom.expressionType] at hmem
        | expression ls =>
            cases right with
            | var v =>
                exact (GroundAtom.not_var hright).elim
            | symbol s =>
                simp [matchAtoms, getMetaType, Atom.expressionType, Atom.symbolType] at hmem
            | grounded g =>
                simp [matchAtoms, getMetaType, Atom.expressionType, Atom.groundedType] at hmem
            | expression rs =>
                have hls : ∀ p ∈ ls, GroundAtom p := by
                  intro p hp
                  exact GroundAtom.elem hleft hp
                have hrs : ∀ p ∈ rs, GroundAtom p := by
                  intro p hp
                  exact GroundAtom.elem hright hp
                have hmemExpr :
                    (ls.length = rs.length ∧
                      result ∈ matchAtomsList ls rs [Bindings.empty] (n + 1)) ∧
                        result.hasLoop = false := by
                  simpa [matchAtoms, getMetaType, Atom.expressionType] using hmem
                obtain ⟨hres, hEq⟩ := ihL ls rs result hls hrs hmemExpr.1.2
                exact ⟨hres, by simp [hEq]⟩
      · intro lefts rights result hlefts hrights hmem
        cases lefts with
        | nil =>
            cases rights with
            | nil =>
                simpa [matchAtomsList] using hmem
            | cons r rs =>
                simp [matchAtomsList] at hmem
        | cons l ls =>
            cases rights with
            | nil =>
                simp [matchAtomsList] at hmem
            | cons r rs =>
                have hl : GroundAtom l := hlefts l (by simp)
                have hr : GroundAtom r := hrights r (by simp)
                have hmem' := by
                  simpa [matchAtomsList] using hmem
                obtain ⟨headRes, hhead, htail⟩ :=
                  (mem_matchAtomsList_flatMap_acc
                    (lefts := ls) (rights := rs)
                    (acc := matchAtoms l r (n + 1))
                    (f := fun mb => mergeBindings Bindings.empty mb (n + 1))
                    (fuel := n + 1) (x := result)).mp hmem'
                obtain ⟨hheadRes, hlr⟩ := ihA l r headRes hl hr hhead
                subst hheadRes
                have htail' : result ∈ matchAtomsList ls rs [Bindings.empty] (n + 1) := by
                  simpa [mergeBindings_empty_right Bindings.empty n] using htail
                obtain ⟨hres, hEqTail⟩ := ihL ls rs result
                  (fun p hp => hlefts p (by simp [hp]))
                  (fun p hp => hrights p (by simp [hp]))
                  htail'
                exact ⟨hres, by simp [hlr, hEqTail]⟩

/-- Two different ground atoms never officially match. -/
private theorem matchAtoms_ground_ne_nil
    {left right : Atom} {n : Nat}
    (hleft : GroundAtom left) (hright : GroundAtom right)
    (hneq : left ≠ right) :
    matchAtoms left right (n + 1) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro result hmem
  obtain ⟨_, heq⟩ := (ground_matchAtoms_mem_empty_eq n).1 left right result hleft hright hmem
  exact hneq heq

/-- Ground/canonical bindings stay canonical through one-way variable binding
on a ground value.  On the ground fragment, the conflicting-rebinding branch
cannot recover via deeper matching, so the only surviving outcomes are the
fresh-assign and same-value cases. -/
private theorem addVarBinding_canon
    {b result : Bindings} {v : String} {val : Atom} {fuel : Nat}
    (hb : GroundBindingsCanon b) (hval : GroundAtom val)
    (hres : result ∈ addVarBinding b v val fuel) :
    GroundBindingsCanon result := by
  cases fuel with
  | zero =>
      simp [addVarBinding] at hres
  | succ n =>
      cases hlook : b.lookup v with
      | none =>
          simp [addVarBinding, hlook] at hres
          rcases hres with rfl
          exact GroundBindingsCanon.assign hb hval
      | some prev =>
          have hprev : GroundAtom prev := lookup_ground hb.1 hlook
          by_cases hsame : prev == val
          · simp [addVarBinding, hlook, hsame] at hres
            rcases hres with rfl
            exact hb
          · have hneq : prev ≠ val := by
              intro heq
              exact hsame (by simp [heq])
            cases n with
            | zero =>
                simp [addVarBinding, hlook, hsame, matchAtoms] at hres
            | succ k =>
                have hmatchNil : matchAtoms prev val (k + 1) = [] :=
                  matchAtoms_ground_ne_nil hprev hval hneq
                simp [addVarBinding, hlook, hsame, hmatchNil] at hres

/-- Folding `addVarBinding` over a canonical accumulator and a ground
assignment list preserves canonicality. -/
private theorem fold_addVarBinding_canon
    (acc : List Bindings) (assigns : List (String × Atom)) (fuel : Nat)
    (hacc : ∀ b ∈ acc, GroundBindingsCanon b)
    (hassigns : ∀ p ∈ assigns, GroundAtom p.2) :
    ∀ b ∈ assigns.foldl
        (fun acc (v, val) => acc.flatMap fun b => addVarBinding b v val fuel) acc,
      GroundBindingsCanon b := by
  induction assigns generalizing acc with
  | nil =>
      simpa
  | cons pair assigns ih =>
      rcases pair with ⟨v, val⟩
      have hval : GroundAtom val := hassigns (v, val) (by simp)
      have hacc' :
          ∀ b ∈ acc.flatMap (fun b => addVarBinding b v val fuel),
            GroundBindingsCanon b := by
        intro b hb
        rcases List.mem_flatMap.mp hb with ⟨b0, hb0, hstep⟩
        exact addVarBinding_canon (hacc b0 hb0) hval hstep
      simp only [List.foldl_cons]
      exact ih _ hacc' (fun p hp => hassigns p (List.mem_cons_of_mem _ hp))

/-- Merging canonical ground bindings preserves canonicality.  The right side's
equalities list is empty on this fragment, so only the assignment fold matters. -/
private theorem mergeBindings_canon
    {left right result : Bindings} {fuel : Nat}
    (hleft : GroundBindingsCanon left) (hright : GroundBindingsCanon right)
    (hres : result ∈ mergeBindings left right fuel) :
    GroundBindingsCanon result := by
  cases fuel with
  | zero =>
      simp [mergeBindings] at hres
  | succ n =>
      have hafter :
          ∀ b ∈ right.assignments.foldl
              (fun acc (v, val) => acc.flatMap fun b => addVarBinding b v val n) [left],
            GroundBindingsCanon b := by
        exact fold_addVarBinding_canon [left] right.assignments n
          (by
            intro b hb
            simp at hb
            rcases hb with rfl
            exact hleft)
          hright.1.1
      simp [mergeBindings, hright.1.2] at hres
      exact hafter result hres

/-- On ground scrutinees, the official matcher and singleton-seeded official
list matcher produce canonical bindings: ground assignment values, no
equalities, and no duplicate assignment keys.  This is the exact amount of
canonicality the later factorization proof needs. -/
private theorem matcher_ground_singleton_canon : ∀ n : Nat,
    (∀ left right result,
      GroundAtom left →
      result ∈ matchAtoms left right n →
      GroundBindingsCanon result) ∧
    (∀ lefts rights b result,
      (∀ p ∈ lefts, GroundAtom p) →
      GroundBindingsCanon b →
      result ∈ matchAtomsList lefts rights [b] n →
      GroundBindingsCanon result) := by
  intro n
  induction n with
  | zero =>
      refine ⟨?_, ?_⟩
      · intro left right result hleft hmem
        simp [matchAtoms] at hmem
      · intro lefts rights b result hlefts hb hmem
        simp [matchAtomsList] at hmem
  | succ n ih =>
      obtain ⟨ihA, ihL⟩ := ih
      refine ⟨?_, ?_⟩
      · intro left right result hleft hmem
        cases left with
        | var v =>
            exact (GroundAtom.not_var hleft).elim
        | symbol s =>
            cases right with
            | var v =>
                have hmem' := by
                  simpa [matchAtoms, getMetaType, Atom.symbolType] using hmem
                rcases hmem' with ⟨⟨_, rfl⟩, _⟩
                exact GroundBindingsCanon.assign GroundBindingsCanon.empty (GroundAtom.symbol s)
            | symbol t =>
                have hmem' := by
                  simpa [matchAtoms, getMetaType, Atom.symbolType] using hmem
                rcases hmem' with ⟨⟨_, rfl⟩, _⟩
                exact GroundBindingsCanon.empty
            | grounded g =>
                simp [matchAtoms, getMetaType, Atom.symbolType, Atom.groundedType] at hmem
            | expression es =>
                simp [matchAtoms, getMetaType, Atom.symbolType, Atom.expressionType] at hmem
        | grounded g =>
            cases right with
            | var v =>
                have hmem' := by
                  simpa [matchAtoms, getMetaType, Atom.groundedType] using hmem
                rcases hmem' with ⟨⟨_, rfl⟩, _⟩
                exact GroundBindingsCanon.assign GroundBindingsCanon.empty (GroundAtom.grounded g)
            | symbol s =>
                simp [matchAtoms, getMetaType, Atom.groundedType, Atom.symbolType] at hmem
            | grounded h =>
                have hmem' := by
                  simpa [matchAtoms, getMetaType, Atom.groundedType] using hmem
                rcases hmem' with ⟨⟨_, rfl⟩, _⟩
                exact GroundBindingsCanon.empty
            | expression es =>
                simp [matchAtoms, getMetaType, Atom.groundedType, Atom.expressionType] at hmem
        | expression lefts =>
            cases right with
            | var v =>
                have hmem' := by
                  simpa [matchAtoms, getMetaType, Atom.expressionType] using hmem
                rcases hmem' with ⟨⟨_, rfl⟩, _⟩
                exact GroundBindingsCanon.assign GroundBindingsCanon.empty hleft
            | symbol s =>
                simp [matchAtoms, getMetaType, Atom.expressionType, Atom.symbolType] at hmem
            | grounded g =>
                simp [matchAtoms, getMetaType, Atom.expressionType, Atom.groundedType] at hmem
            | expression rights =>
                have hchild : ∀ p ∈ lefts, GroundAtom p := by
                  intro p hp
                  exact GroundAtom.elem hleft hp
                have hmem' := by
                  simpa [matchAtoms, getMetaType, Atom.expressionType] using hmem
                rcases hmem' with ⟨⟨_, hraw⟩, _⟩
                exact ihL lefts rights Bindings.empty result hchild GroundBindingsCanon.empty hraw
      · intro lefts rights b result hlefts hb hmem
        cases lefts with
        | nil =>
            cases rights with
            | nil =>
                simp [matchAtomsList] at hmem
                subst hmem
                exact hb
            | cons r rs =>
                simp [matchAtomsList] at hmem
        | cons l ls =>
            cases rights with
            | nil =>
                simp [matchAtomsList] at hmem
            | cons r rs =>
                have hl : GroundAtom l := hlefts l (by simp)
                have hmem' := by
                  simpa [matchAtomsList] using hmem
                obtain ⟨mb, hmb, htailAcc⟩ :=
                  (mem_matchAtomsList_flatMap_acc
                    (lefts := ls) (rights := rs)
                    (acc := matchAtoms l r n)
                    (f := fun mb => mergeBindings b mb n)
                    (fuel := n) (x := result)).mp hmem'
                obtain ⟨b', hb', htail⟩ :=
                  (mem_matchAtomsList_seedwise
                    (lefts := ls) (rights := rs)
                    (seeds := mergeBindings b mb n)
                    (fuel := n) (x := result)).mp htailAcc
                have hmbCanon : GroundBindingsCanon mb := ihA l r mb hl hmb
                have hb'Canon : GroundBindingsCanon b' := mergeBindings_canon hb hmbCanon hb'
                exact ihL ls rs b' result
                  (fun p hp => hlefts p (by simp [hp]))
                  hb'Canon
                  htail

private theorem matchAtoms_ground_canon
    {left right : Atom} {result : Bindings} {n : Nat}
    (hleft : GroundAtom left)
    (hmem : result ∈ matchAtoms left right n) :
    GroundBindingsCanon result :=
  (matcher_ground_singleton_canon n).1 left right result hleft hmem

private theorem matchAtomsList_ground_empty_canon
    {lefts rights : List Atom} {result : Bindings} {n : Nat}
    (hlefts : ∀ p ∈ lefts, GroundAtom p)
    (hmem : result ∈ matchAtomsList lefts rights [Bindings.empty] n) :
    GroundBindingsCanon result :=
  (matcher_ground_singleton_canon n).2 lefts rights Bindings.empty result
    hlefts GroundBindingsCanon.empty hmem

/-- Fuel-1 `addVarBinding` preserves an already-built prefix and installs the
new assignment at its fresh key.  This is the right-hand extension step for
deterministic ground merges. -/
private theorem addVarBinding_fuel1_extends_prefix
    {pref b result : Bindings} {v : String} {val a : Atom} {x : String}
    (hlookup_none : pref.lookup v = none)
    (hext : pref.Extends b)
    (hres : result ∈ addVarBinding b v val 1)
    (hx : (pref.assign v val).lookup x = some a) :
    result.lookup x = some a := by
  cases hlook : b.lookup v with
  | none =>
      simp [addVarBinding, hlook] at hres
      rcases hres with rfl
      by_cases hxeq : x = v
      · subst hxeq
        have hxv : a = val := by
          have := hx
          simpa [lookup_assign_of_lookup_none pref x val hlookup_none] using this.symm
        subst hxv
        exact lookup_assign_of_lookup_none b x a hlook
      · have hpref : pref.lookup x = some a := by
          simpa [assign_lookup_ne pref v val x hxeq hlookup_none] using hx
        have hb : b.lookup x = some a := hext x a hpref
        simpa [assign_lookup_ne b v val x hxeq hlook] using hb
  | some prev =>
      by_cases hsame : prev == val
      · simp [addVarBinding, hlook, hsame] at hres
        rcases hres with rfl
        by_cases hxeq : x = v
        · subst hxeq
          have hxv : a = val := by
            have := hx
            simpa [lookup_assign_of_lookup_none pref x val hlookup_none] using this.symm
          subst hxv
          simpa [hlook] using hsame
        · have hpref : pref.lookup x = some a := by
            simpa [assign_lookup_ne pref v val x hxeq hlookup_none] using hx
          exact hext x a hpref
      · simp [addVarBinding, hlook, hsame, matchAtoms] at hres

/-- Folding fuel-1 `addVarBinding` over a list of fresh assignments preserves
the whole accumulated right-hand fragment in every surviving result. -/
private theorem fold_addVarBinding_fuel1_extends_prefix
    (acc : List Bindings) (pref : Bindings) (rest : List (String × Atom))
    (hEq : pref.equalities = [])
    (hkeys : Bindings.KeysNodup pref)
    (hrestKeys : (rest.map Prod.fst).Nodup)
    (hfresh : ∀ v, v ∈ rest.map Prod.fst → pref.lookup v = none)
    (hacc : ∀ b ∈ acc, pref.Extends b) :
    ∀ result ∈ List.foldl
        (fun acc x => acc.flatMap fun b => addVarBinding b x.1 x.2 1)
        acc rest,
      ({ assignments := pref.assignments ++ rest, equalities := [] } : Bindings).Extends result := by
  induction rest generalizing acc pref with
  | nil =>
      intro result hresult
      have hpref : ({ assignments := pref.assignments, equalities := [] } : Bindings) = pref := by
        rw [← hEq]
      rw [List.append_nil, hpref]
      exact hacc result hresult
  | cons pair rest ih =>
      rcases pair with ⟨v, val⟩
      have hlookup : pref.lookup v = none := hfresh v (by simp)
      have hnotbound : pref.isBound v = false := by
        simp [Bindings.isBound, hlookup]
      have hnotmemRest : v ∉ rest.map Prod.fst := by
        simpa using (List.nodup_cons.mp hrestKeys).1
      have hkeysRest : (rest.map Prod.fst).Nodup := by
        simpa using (List.nodup_cons.mp hrestKeys).2
      have hEq' : (pref.assign v val).equalities = [] := by
        simpa [Bindings.assign, hnotbound] using hEq
      have hfresh' : ∀ w, w ∈ rest.map Prod.fst → (pref.assign v val).lookup w = none := by
        intro w hw
        have hwne : w ≠ v := by
          intro hwv
          subst hwv
          exact hnotmemRest hw
        simpa [hfresh w (by simp [hw])] using assign_lookup_ne pref v val w hwne hlookup
      have hacc' : ∀ b ∈ acc.flatMap (fun b => addVarBinding b v val 1), (pref.assign v val).Extends b := by
        intro b hb x a hx
        rcases List.mem_flatMap.mp hb with ⟨b0, hb0, hstep⟩
        exact addVarBinding_fuel1_extends_prefix hlookup (hacc b0 hb0) hstep hx
      intro result hresult
      simp only [List.foldl_cons] at hresult
      have htail :=
        ih (acc.flatMap fun b => addVarBinding b v val 1) (pref.assign v val)
          hEq' (Bindings.KeysNodup.assign hkeys) hkeysRest hfresh' hacc'
          result hresult
      simpa [Bindings.assign, hnotbound, List.append_assoc] using htail

/-- Any successful fuel-2 merge with a canonical right-hand fragment preserves
that entire fragment inside the result.  This is the honest pointwise form of
"seeded official matching still contains the official fragment". -/
private theorem mergeBindings_two_extends_right_of_canon
    {left right result : Bindings}
    (hright : GroundBindingsCanon right)
    (hres : result ∈ mergeBindings left right 2) :
    right.Extends result := by
  rcases hright with ⟨hground, hkeys⟩
  have hres' :
      result ∈ List.foldl
        (fun acc x => acc.flatMap fun b => addVarBinding b x.1 x.2 1)
        [left] right.assignments := by
    simpa [mergeBindings, hground.2] using hres
  have hfold :
      ({ assignments := [] ++ right.assignments, equalities := [] } : Bindings).Extends result := by
    exact
      (fold_addVarBinding_fuel1_extends_prefix [left] Bindings.empty right.assignments
        rfl Bindings.KeysNodup.empty hkeys
        (by
          intro v hv
          simp [Bindings.empty, Bindings.lookup])
        (by
          intro b hb
          rcases List.mem_singleton.mp hb with rfl
          intro x a hx
          simp [Bindings.empty, Bindings.lookup] at hx)
        result hres')
  have hright : ({ assignments := right.assignments, equalities := [] } : Bindings) = right := by
    rw [← hground.2]
  rw [List.nil_append, hright] at hfold
  exact hfold

/-- Any successful fuel-1 `addVarBinding` step preserves every lookup already
present in the seed bindings. -/
private theorem addVarBinding_fuel1_extends_seed
    {seed result : Bindings} {v : String} {val : Atom}
    (hres : result ∈ addVarBinding seed v val 1) :
    seed.Extends result := by
  cases hlook : seed.lookup v with
  | none =>
      simp [addVarBinding, hlook] at hres
      rcases hres with rfl
      exact extends_assign_of_lookup_none seed v val hlook
  | some prev =>
      by_cases hsame : prev == val
      · simp [addVarBinding, hlook, hsame] at hres
        rcases hres with rfl
        exact fun _ _ h => h
      · simp [addVarBinding, hlook, hsame, matchAtoms] at hres

/-- Folding fuel-1 `addVarBinding` over any assignment list preserves the
original seed through every surviving result. -/
private theorem fold_addVarBinding_fuel1_extends_seed
    (seed : Bindings) (acc : List Bindings) (assigns : List (String × Atom))
    (hacc : ∀ b ∈ acc, seed.Extends b) :
    ∀ result ∈ List.foldl
        (fun acc x => acc.flatMap fun b => addVarBinding b x.1 x.2 1)
        acc assigns,
      seed.Extends result := by
  induction assigns generalizing acc with
  | nil =>
      intro result hresult
      exact hacc result hresult
  | cons pair assigns ih =>
      rcases pair with ⟨v, val⟩
      have hacc' :
          ∀ b ∈ acc.flatMap (fun b => addVarBinding b v val 1), seed.Extends b := by
        intro b hb
        rcases List.mem_flatMap.mp hb with ⟨b0, hb0, hstep⟩
        exact Bindings.extends_trans (hacc b0 hb0) (addVarBinding_fuel1_extends_seed hstep)
      intro result hresult
      simp only [List.foldl_cons] at hresult
      exact ih _ hacc' result hresult

/-- Any successful fuel-2 merge preserves every lookup already present in the
left seed bindings on the ground/no-equalities fragment. -/
private theorem mergeBindings_two_extends_left
    {left right result : Bindings}
    (hright : GroundBindings right)
    (hres : result ∈ mergeBindings left right 2) :
    left.Extends result := by
  intro x a hx
  have hseed : left.Extends result :=
    by
      have hres' :
          result ∈ List.foldl
            (fun acc x => acc.flatMap fun b => addVarBinding b x.1 x.2 1)
            [left] right.assignments := by
        simpa [mergeBindings, hright.2] using hres
      exact fold_addVarBinding_fuel1_extends_seed left [left] right.assignments
        (by
          intro b hb
          rcases List.mem_singleton.mp hb with rfl
          exact fun _ _ h => h)
        result hres'
  exact hseed x a hx

/-- On ground seeds and ground values, positive-fuel `addVarBinding` collapses
to the deterministic fuel-1 case.  Conflicting rebinding cannot recover via a
deeper matcher call because two different ground atoms never match. -/
  private theorem addVarBinding_ground_eq_fuel1
    {b : Bindings} {v : String} {val : Atom} (fuel : Nat)
    (hb : GroundBindings b) (hval : GroundAtom val) :
    addVarBinding b v val (fuel + 1) = addVarBinding b v val 1 := by
  cases hlook : b.lookup v with
  | none =>
      simp [addVarBinding, hlook]
  | some prev =>
      have hprev : GroundAtom prev := lookup_ground hb hlook
      by_cases hsame : prev == val
      · simp [addVarBinding, hlook, hsame]
      · have hneq : prev ≠ val := by
          intro heq
          exact hsame (by simp [heq])
        cases fuel with
        | zero =>
            simp [addVarBinding, hlook, hsame]
        | succ n =>
            have hmatchNil : matchAtoms prev val (n + 1) = [] :=
              matchAtoms_ground_ne_nil hprev hval hneq
            have hlhs : addVarBinding b v val (n + 2) = [] := by
              simp [addVarBinding, hlook, hsame, hmatchNil]
            have hrhs : addVarBinding b v val 1 = [] := by
              simp [addVarBinding, hlook, hsame, matchAtoms]
            rw [hlhs, hrhs]

/-- On a ground accumulator and a ground value, one positive-fuel
`addVarBinding` step is exactly the deterministic ground-merge step. -/
private theorem flatMap_addVarBinding_ground_eq_detfold
    (acc : List Bindings) (v : String) (val : Atom) (fuel : Nat)
    (hacc : ∀ b ∈ acc, GroundBindings b) (hval : GroundAtom val) :
    acc.flatMap (fun b => addVarBinding b v val (fuel + 1)) =
      detfoldStep acc (v, val) := by
  induction acc with
  | nil => rfl
  | cons b acc ih =>
      have hb : GroundBindings b := hacc b (by simp)
      have hacc' : ∀ b' ∈ acc, GroundBindings b' := by
        intro b' hb'
        exact hacc b' (by simp [hb'])
      simp [detfoldStep, addVarBinding_ground_eq_fuel1 fuel hb hval,
        addVarBinding_fuel1, ih hacc']

/-- Deterministic ground-merge preserves the ground-bindings invariant. -/
private theorem detfoldStep_ground
    {acc : List Bindings} {v : String} {val : Atom}
    (hacc : ∀ b ∈ acc, GroundBindings b) (hval : GroundAtom val) :
    ∀ b ∈ detfoldStep acc (v, val), GroundBindings b := by
  intro b hb
  rcases List.mem_flatMap.mp hb with ⟨b0, hb0, hstep⟩
  have hb0g : GroundBindings b0 := hacc b0 hb0
  cases hlook : b0.lookup v with
  | none =>
      simp [hlook] at hstep
      rcases hstep with rfl
      exact GroundBindings.assign hb0g hval
  | some prev =>
      by_cases hsame : prev == val
      · simp [hlook, hsame] at hstep
        rcases hstep with rfl
        exact hb0g
      · simp [hlook, hsame] at hstep

/-- Folding positive-fuel `addVarBinding` over a ground accumulator and ground
assignment list collapses to the deterministic ground-merge fold. -/
private theorem fold_addVarBinding_ground_eq_detfold
    (assigns : List (String × Atom)) (acc : List Bindings) (fuel : Nat)
    (hassigns : ∀ p ∈ assigns, GroundAtom p.2)
    (hacc : ∀ b ∈ acc, GroundBindings b) :
    List.foldl
      (fun acc x => acc.flatMap fun b => addVarBinding b x.1 x.2 (fuel + 1))
      acc assigns =
    List.foldl detfoldStep acc assigns := by
  induction assigns generalizing acc with
  | nil => rfl
  | cons pair assigns ih =>
      rcases pair with ⟨v, val⟩
      have hval : GroundAtom val := hassigns (v, val) (by simp)
      have hstep :
          acc.flatMap (fun b => addVarBinding b v val (fuel + 1)) =
            detfoldStep acc (v, val) :=
        flatMap_addVarBinding_ground_eq_detfold acc v val fuel hacc hval
      have hnext : ∀ b ∈ detfoldStep acc (v, val), GroundBindings b := by
        intro b hb
        exact detfoldStep_ground hacc hval b hb
      rw [List.foldl_cons, List.foldl_cons, hstep]
      exact ih (detfoldStep acc (v, val))
        (fun p hp => hassigns p (by simp [hp]))
        hnext

/-- On the ground/no-equalities fragment, positive-fuel `mergeBindings`
collapses to the deterministic helper `mergeGround?`. -/
private theorem mergeBindings_ground_eq_mergeGround
    {left right : Bindings} (fuel : Nat)
    (hleft : GroundBindings left) (hright : GroundBindings right) :
    mergeBindings left right (fuel + 2) = (mergeGround? left right).toList := by
  rcases hright with ⟨hassigns, heqs⟩
  cases right with
  | mk assignments equalities =>
      cases heqs
      simp [mergeBindings, mergeGround?]
      rw [fold_addVarBinding_ground_eq_detfold assignments [left] fuel
        (by simpa using hassigns)
        (by
          intro b hb
          simp at hb
          rcases hb with rfl
          exact hleft)]
      simpa using (mergeGroundAssignments_toList_eq_detfold left assignments).symm

/-- Membership in a positive-fuel ground merge is equivalent to the
deterministic ground-merge helper returning that result. -/
private theorem mem_mergeBindings_ground_iff
    {left right result : Bindings} {fuel : Nat}
    (hleft : GroundBindings left) (hright : GroundBindings right) :
    result ∈ mergeBindings left right (fuel + 2) ↔
      mergeGround? left right = some result := by
  rw [mergeBindings_ground_eq_mergeGround fuel hleft hright]
  cases hmerge : mergeGround? left right with
  | none =>
      simp
  | some b =>
      simp [eq_comm]

/-- A seeded official head match on a ground scrutinee factors through the
same head binding merged at fuel 2.  This removes fuel-skew from the
head-step part of the matcher bridge; the remaining bottleneck is the
list-level singleton-seed factorization. -/
private theorem matchAtoms_ground_seed_factor
    {left x : Bindings} {scrutinee pattern : Atom} {fuel : Nat}
    (hground : GroundAtom scrutinee) (hb : GroundBindings left)
    (hx :
      x ∈ (matchAtoms scrutinee pattern fuel).flatMap
        (fun mb => mergeBindings left mb fuel)) :
    ∃ mb,
      mb ∈ matchAtoms scrutinee pattern fuel ∧
      x ∈ mergeBindings left mb 2 := by
  obtain ⟨mb, hmb, hmerge⟩ := List.mem_flatMap.mp hx
  have hmbGround : GroundBindings mb :=
    (matcher_ground fuel).1 scrutinee pattern mb hground hmb
  cases fuel with
  | zero =>
      simp [matchAtoms] at hmb
  | succ n =>
      refine ⟨mb, hmb, ?_⟩
      cases n with
      | zero =>
          have hsub := mergeBindings_mono_add left mb 1 1
          exact hsub x hmerge
      | succ k =>
          have hdet :
              mergeGround? left mb = some x :=
            (mem_mergeBindings_ground_iff (left := left) (right := mb)
              (result := x) (fuel := k) hb hmbGround).mp hmerge
          exact
            (mem_mergeBindings_ground_iff (left := left) (right := mb)
              (result := x) (fuel := 0) hb hmbGround).mpr hdet

/-- Exact inversion of an empty-seeded official cons-run on the ground
fragment: the implicit head seed produced by the empty merge is really the
head matcher result itself, so the run decomposes to a canonical head witness
and a tail run from `[mb]` at the same inner fuel. -/
private theorem matchAtomsList_empty_cons_inv_ground
    {t p : Atom} {ts ps : List Atom} {result : Bindings} {fuel : Nat}
    (ht : GroundAtom t)
    (hmem : result ∈ matchAtomsList (t :: ts) (p :: ps) [Bindings.empty] (fuel + 1)) :
    ∃ mb,
      mb ∈ matchAtoms t p fuel ∧
      result ∈ matchAtomsList ts ps [mb] fuel := by
  have hmem' : result ∈
      matchAtomsList ts ps
        ((matchAtoms t p fuel).flatMap fun mb => mergeBindings Bindings.empty mb fuel)
        fuel := by
    simpa [matchAtomsList] using hmem
  obtain ⟨mb, hmb, htailAcc⟩ :=
    (mem_matchAtomsList_flatMap_acc
      (lefts := ts) (rights := ps)
      (acc := matchAtoms t p fuel)
      (f := fun mb => mergeBindings Bindings.empty mb fuel)
      (fuel := fuel) (x := result)).mp hmem'
  obtain ⟨b', hb', htail⟩ :=
    (mem_matchAtomsList_seedwise
      (lefts := ts) (rights := ps)
      (seeds := mergeBindings Bindings.empty mb fuel)
      (fuel := fuel) (x := result)).mp htailAcc
  have hheadSeeded :
      b' ∈ (matchAtoms t p fuel).flatMap
        (fun mb => mergeBindings Bindings.empty mb fuel) :=
    List.mem_flatMap.mpr ⟨mb, hmb, hb'⟩
  obtain ⟨mb0, hmb0, hb'2⟩ :=
    matchAtoms_ground_seed_factor ht GroundBindings.empty hheadSeeded
  have hmb0Canon : GroundBindingsCanon mb0 := matchAtoms_ground_canon ht hmb0
  have hb'det :
      mergeGround? Bindings.empty mb0 = some b' := by
    exact
      (mem_mergeBindings_ground_iff
        (left := Bindings.empty) (right := mb0) (result := b')
        (fuel := 0) GroundBindings.empty hmb0Canon.1).mp hb'2
  have hb'eq : b' = mb0 := by
    rw [mergeGround_empty_left_of_canon hmb0Canon] at hb'det
    injection hb'det with hEq
    symm
    exact hEq
  exact ⟨b', by simpa [hb'eq] using hmb0, htail⟩

/-- Deterministic ground merge composes at the equation level on the canonical
ground fragment: if `c` is the result of merging `mb` into `b`, and `x` is the
result of merging `fr` into `c`, then the middle merge `mb ⋆ fr` exists as a
concrete bindings value `g`, and merging `g` into `b` reproduces `x`. -/
private theorem mergeGround_seed_compose
    {b mb c fr x : Bindings}
    (hb : GroundBindings b)
    (hmbCanon : GroundBindingsCanon mb)
    (hfrCanon : GroundBindingsCanon fr)
    (hc : mergeGround? b mb = some c)
    (hx : mergeGround? c fr = some x) :
    ∃ g,
      mergeGround? mb fr = some g ∧
      mergeGround? b g = some x := by
  let restAssigns := fr.assignments.filter (fun p => (mb.lookup p.1).isNone)
  let rest : Bindings := { assignments := restAssigns, equalities := [] }
  let g : Bindings := { assignments := mb.assignments ++ restAssigns, equalities := [] }
  have hmbExt : mb.Extends c :=
    mergeGround_extends_right_of_nodup hmbCanon.1.2 hmbCanon.2 hc
  have hmid :
      mergeGround? mb fr = some g := by
    have hag :
        ∀ {v aM aF},
          mb.lookup v = some aM →
          List.lookup v fr.assignments = some aF →
          aM = aF := by
      intro v aM aF hmbLook hfrLook
      have hcLook : c.lookup v = some aM := hmbExt v aM hmbLook
      exact mergeGround_overlap_agree hfrCanon.1.2 hfrCanon.2 hx hcLook
        (by simpa [Bindings.lookup] using hfrLook)
    simpa [mergeGround?, hfrCanon.1.2, g, restAssigns] using
      (mergeGroundAssignments_eq_append_fresh_of_overlap_agree
        (left := mb) (assigns := fr.assignments)
        hmbCanon.1.2 hfrCanon.2 hag)
  have hcmem :
      c ∈ mergeBindings b mb 2 :=
    (mem_mergeBindings_ground_iff
      (left := b) (right := mb) (result := c) (fuel := 0) hb hmbCanon.1).mpr hc
  have hcg : GroundBindings c := by
    have hmatchers := matcher_ground 2
    rcases hmatchers with ⟨_hA, _hL, hM, _hB⟩
    exact hM b mb c hb hmbCanon.1 hcmem
  have hrestMerge :
      mergeGround? c rest = some x := by
    have hrest :
        mergeGround? c rest =
          some
            { assignments := c.assignments ++
                restAssigns.filter (fun p => (c.lookup p.1).isNone)
            , equalities := [] } := by
      have hag :
          ∀ {v aL aR},
            c.lookup v = some aL →
            List.lookup v restAssigns = some aR →
            aL = aR := by
        intro v aL aR hcLook hrestLook
        have hfrLook : List.lookup v fr.assignments = some aR :=
          lookup_filter_some_of_nodup hfrCanon.2 hrestLook
        exact mergeGround_overlap_agree hfrCanon.1.2 hfrCanon.2 hx hcLook
          (by simpa [Bindings.lookup] using hfrLook)
      simpa [mergeGround?, rest, restAssigns] using
        (mergeGroundAssignments_eq_append_fresh_of_overlap_agree
          (left := c) (assigns := restAssigns)
          hcg.2 (keys_nodup_filter hfrCanon.2) hag)
    have hx' :
        x =
          { assignments := c.assignments ++
              fr.assignments.filter (fun p => (c.lookup p.1).isNone)
          , equalities := [] } := by
      have hfull :
          mergeGround? c fr =
            some
              { assignments := c.assignments ++
                  fr.assignments.filter (fun p => (c.lookup p.1).isNone)
              , equalities := [] } := by
        have hag :
            ∀ {v aL aR},
              c.lookup v = some aL →
              List.lookup v fr.assignments = some aR →
              aL = aR := by
          intro v aL aR hcLook hfrLook
          exact mergeGround_overlap_agree hfrCanon.1.2 hfrCanon.2 hx hcLook
            (by simpa [Bindings.lookup] using hfrLook)
        simpa [mergeGround?, hfrCanon.1.2] using
          (mergeGroundAssignments_eq_append_fresh_of_overlap_agree
            (left := c) (assigns := fr.assignments)
            hcg.2 hfrCanon.2 hag)
      have : some x =
          some
            { assignments := c.assignments ++
                fr.assignments.filter (fun p => (c.lookup p.1).isNone)
            , equalities := [] } := by
        rw [← hx, hfull]
      injection this
    have hfilter :
        restAssigns.filter (fun p => (c.lookup p.1).isNone) =
          fr.assignments.filter (fun p => (c.lookup p.1).isNone) := by
      simpa [restAssigns] using
        (filter_lookup_none_of_extends
          (xs := fr.assignments) (base := mb) (ext := c) hmbExt)
    rw [hrest, hx', hfilter]
  refine ⟨g, hmid, ?_⟩
  have hconcat := mergeGround_concat b mb rest hmbCanon.1.2 rfl
  simpa [g, rest, restAssigns, hc, hrestMerge] using hconcat

/-- Transport a singleton-seeded official list run across an already-factored
ground seed: if `seed` is obtained by merging canonical `delta` into `base`,
then any official run from `[seed]` factors through a run from `[delta]`,
possibly at a larger fuel, with the same final merge into `base`. -/
private theorem matchAtomsList_seed_transport_ground : ∀ fuel : Nat,
    ∀ {lefts rights base delta seed x},
      (∀ t ∈ lefts, GroundAtom t) →
      GroundBindings base →
      GroundBindingsCanon delta →
      seed ∈ mergeBindings base delta 2 →
      x ∈ matchAtomsList lefts rights [seed] fuel →
        ∃ fuel', ∃ fr,
          fr ∈ matchAtomsList lefts rights [delta] fuel' ∧
          x ∈ mergeBindings base fr 2 := by
  intro fuel
  induction fuel with
  | zero =>
      intro lefts rights base delta seed x hlefts hbase hdelta hseed hmem
      simp [matchAtomsList] at hmem
  | succ n ih =>
      intro lefts rights base delta seed x hlefts hbase hdelta hseed hmem
      have hseedGround : GroundBindings seed := by
        have hmatchers := matcher_ground 2
        rcases hmatchers with ⟨_hA, _hL, hM, _hB⟩
        exact hM base delta seed hbase hdelta.1 hseed
      cases lefts with
      | nil =>
          cases rights with
          | nil =>
              simp [matchAtomsList] at hmem
              subst hmem
              refine ⟨1, delta, ?_, hseed⟩
              simp [matchAtomsList]
          | cons r rs =>
              simp [matchAtomsList] at hmem
      | cons t ts =>
          cases rights with
          | nil =>
              simp [matchAtomsList] at hmem
          | cons p ps =>
              have ht : GroundAtom t := hlefts t (by simp)
              have htsGround : ∀ a ∈ ts, GroundAtom a := by
                intro a ha
                exact hlefts a (by simp [ha])
              have htailAcc :
                  x ∈ matchAtomsList ts ps
                    ((matchAtoms t p n).flatMap fun mb => mergeBindings seed mb n) n := by
                simpa [matchAtomsList] using hmem
              obtain ⟨c, hcAcc, htail⟩ :=
                (mem_matchAtomsList_seedwise
                  (lefts := ts) (rights := ps)
                  (seeds := (matchAtoms t p n).flatMap fun mb => mergeBindings seed mb n)
                  (fuel := n) (x := x)).mp htailAcc
              obtain ⟨mb, hmb, hcSeed2⟩ :=
                matchAtoms_ground_seed_factor ht hseedGround hcAcc
              have hmbCanon : GroundBindingsCanon mb := matchAtoms_ground_canon ht hmb
              have hseedEq :
                  mergeGround? base delta = some seed :=
                (mem_mergeBindings_ground_iff
                  (left := base) (right := delta) (result := seed)
                  (fuel := 0) hbase hdelta.1).mp hseed
              have hcSeedEq :
                  mergeGround? seed mb = some c :=
                (mem_mergeBindings_ground_iff
                  (left := seed) (right := mb) (result := c)
                  (fuel := 0) hseedGround hmbCanon.1).mp hcSeed2
              obtain ⟨g, hgEq, hcBaseEq⟩ :=
                mergeGround_seed_compose hbase hdelta hmbCanon hseedEq hcSeedEq
              have hgMem2 :
                  g ∈ mergeBindings delta mb 2 :=
                (mem_mergeBindings_ground_iff
                  (left := delta) (right := mb) (result := g)
                  (fuel := 0) hdelta.1 hmbCanon.1).mpr hgEq
              have hgCanon : GroundBindingsCanon g :=
                mergeBindings_canon hdelta hmbCanon hgMem2
              have hcBaseMem :
                  c ∈ mergeBindings base g 2 :=
                (mem_mergeBindings_ground_iff
                  (left := base) (right := g) (result := c)
                  (fuel := 0) hbase hgCanon.1).mpr hcBaseEq
              obtain ⟨fuelTail, fr, hfr, hmergeFinal⟩ :=
                ih (lefts := ts) (rights := ps)
                  (base := base) (delta := g) (seed := c) (x := x)
                  htsGround hbase hgCanon hcBaseMem htail
              let fuelHead := max n 2
              have hmb' : mb ∈ matchAtoms t p fuelHead := by
                have hEq : n + (fuelHead - n) = fuelHead := by
                  dsimp [fuelHead]
                  exact Nat.add_sub_of_le (Nat.le_max_left _ _)
                simpa [hEq, fuelHead] using
                  (matchAtoms_mono_add t p n (fuelHead - n)) mb hmb
              have hgMemHead : g ∈ mergeBindings delta mb fuelHead := by
                have hEq : 2 + (fuelHead - 2) = fuelHead := by
                  dsimp [fuelHead]
                  exact Nat.add_sub_of_le (Nat.le_max_right _ _)
                simpa [hEq, fuelHead] using
                  (mergeBindings_mono_add delta mb 2 (fuelHead - 2)) g hgMem2
              have hhead :
                  g ∈ (matchAtoms t p fuelHead).flatMap
                    (fun mb0 => mergeBindings delta mb0 fuelHead) :=
                List.mem_flatMap.mpr ⟨mb, hmb', hgMemHead⟩
              obtain ⟨fuelWhole, hwhole⟩ := matchAtomsList_cons_of_head_tail hhead hfr
              exact ⟨fuelWhole + 1, fr, by simpa using hwhole, hmergeFinal⟩

/-- Singleton-seed factorization on the ground fragment: any official list run
from `[b]` factors through an empty-seeded run at some (possibly larger) fuel,
with the same final merge back into `b` at fuel 2. -/
private theorem matchAtomsList_singleton_factor_ground
    {lefts rights : List Atom} {b x : Bindings} {fuel : Nat}
    (hlefts : ∀ t ∈ lefts, GroundAtom t)
    (hb : GroundBindings b)
    (hmem : x ∈ matchAtomsList lefts rights [b] fuel) :
    ∃ fuel', ∃ fr,
      fr ∈ matchAtomsList lefts rights [Bindings.empty] fuel' ∧
      x ∈ mergeBindings b fr 2 := by
  have hseed : b ∈ mergeBindings b Bindings.empty 2 := by
    rw [mergeBindings_empty_right b 1]
    simp
  simpa using
    (matchAtomsList_seed_transport_ground fuel
      (lefts := lefts) (rights := rights)
      (base := b) (delta := Bindings.empty) (seed := b) (x := x)
      hlefts hb GroundBindingsCanon.empty hseed hmem)

/-- Ground-seeded list bridge: if each successful element match from a ground
seed has an official witness, then successful `simpleMatchList` threading from
a ground seed also has an official seeded list witness, and recursive seeds stay
ground by `matcher_ground`. -/
private theorem simpleMatchList_ground_seeded_of_elem_bridge_ground
    (fuel : Nat)
    (hElem :
      ∀ {p t b qb},
        GroundBindings b →
        GroundAtom t →
        simpleMatch p t b fuel = some qb →
          ∃ fuel',
            qb ∈ (matchAtoms t p fuel').flatMap (fun mb => mergeBindings b mb fuel')) :
    ∀ {ps ts b qb},
      GroundBindings b →
      (∀ t ∈ ts, GroundAtom t) →
      simpleMatch.simpleMatchList ps ts b fuel = some qb →
        ∃ fuel', qb ∈ matchAtomsList ts ps [b] fuel' := by
  intro ps
  induction ps with
  | nil =>
      intro ts b qb hb hground hmatch
      cases ts with
      | nil =>
          simp [simpleMatch.simpleMatchList] at hmatch
          subst hmatch
          refine ⟨1, ?_⟩
          simp [matchAtomsList]
      | cons t ts =>
          simp [simpleMatch.simpleMatchList] at hmatch
  | cons p ps ih =>
      intro ts b qb hb hground hmatch
      cases ts with
      | nil =>
          simp [simpleMatch.simpleMatchList] at hmatch
      | cons t ts =>
          unfold simpleMatch.simpleMatchList at hmatch
          cases hhd : simpleMatch p t b fuel with
          | none =>
              simp [hhd] at hmatch
          | some b' =>
              simp [hhd] at hmatch
              have ht : GroundAtom t := hground t (by simp)
              obtain ⟨fuelHead, hhead⟩ := hElem hb ht hhd
              have hb' : GroundBindings b' := by
                rcases List.mem_flatMap.mp hhead with ⟨mb, hmb, hmerge⟩
                have hmatchers := matcher_ground fuelHead
                rcases hmatchers with ⟨hA, _hL, hM, _hB⟩
                have hmbGround : GroundBindings mb := hA t p mb ht hmb
                exact hM b mb b' hb hmbGround hmerge
              obtain ⟨fuelTail, htail⟩ := ih hb'
                (fun a ha => hground a (by simp [ha])) hmatch
              obtain ⟨fuel', hwhole⟩ := matchAtomsList_cons_of_head_tail hhead htail
              exact ⟨fuel' + 1, hwhole⟩

/-- Bridge helper: a successful one-way variable match against a ground target
is witnessed by the official matcher plus a merge of the produced singleton
binding into the seed. -/
theorem simpleMatch_ground_var_bridge
    {target : Atom} {b qb : Bindings} {v : String} {fuel : Nat}
    (hground : GroundAtom target)
    (hmatch : simpleMatch (.var v) target b fuel = some qb) :
    ∃ fuel',
      Bindings.empty.assign v target ∈ matchAtoms target (.var v) fuel' ∧
      qb ∈ mergeBindings b (Bindings.empty.assign v target) fuel' := by
  cases fuel with
  | zero =>
      simp [simpleMatch] at hmatch
  | succ n =>
      cases hlook : b.lookup v with
      | none =>
          simp [simpleMatch, hlook] at hmatch
          rcases hmatch with rfl
          refine ⟨2, ?_, ?_⟩
          · rw [matchAtoms_ground_var_exact target v 1 hground]
            simp
          · rw [mergeBindings_single_assign_fresh hlook 0]
            simp
      | some prev =>
          simp only [simpleMatch, hlook] at hmatch
          split at hmatch <;> rename_i heq
          · simp at hmatch
            rcases hmatch with rfl
            have hprev : prev = target := by simpa using heq
            refine ⟨2, ?_, ?_⟩
            · rw [matchAtoms_ground_var_exact target v 1 hground]
              simp
            · rw [mergeBindings_single_assign_same (hprev.symm ▸ hlook) 0]
              simp
          · simp at hmatch

/-- Bridge helper: a successful symbol-pattern match against a ground target
is witnessed by the official matcher's empty binding result. -/
theorem simpleMatch_ground_symbol_bridge
    {target : Atom} {b qb : Bindings} {s : String} {fuel : Nat}
    (hground : GroundAtom target)
    (hmatch : simpleMatch (.symbol s) target b fuel = some qb) :
    ∃ fuel',
      Bindings.empty ∈ matchAtoms target (.symbol s) fuel' ∧
      qb ∈ mergeBindings b Bindings.empty fuel' := by
  cases fuel with
  | zero =>
      simp [simpleMatch] at hmatch
  | succ n =>
      cases target with
      | var v =>
          exact (GroundAtom.not_var hground).elim
      | symbol t =>
          simp [simpleMatch] at hmatch
          rcases hmatch with ⟨hst, rfl⟩
          refine ⟨1, ?_, ?_⟩
          · subst hst
            simp [matchAtoms, getMetaType, Atom.symbolType, Bindings.hasLoop, Bindings.empty]
          · rw [mergeBindings_empty_right b 0]
            simp
      | grounded g =>
          simp [simpleMatch] at hmatch
      | expression es =>
          simp [simpleMatch] at hmatch

/-- Bridge helper: a successful grounded-value pattern match against a ground
target is witnessed by the official matcher's empty binding result. -/
theorem simpleMatch_ground_grounded_bridge
    {target : Atom} {b qb : Bindings} {g : GroundedValue} {fuel : Nat}
    (hground : GroundAtom target)
    (hmatch : simpleMatch (.grounded g) target b fuel = some qb) :
    ∃ fuel',
      Bindings.empty ∈ matchAtoms target (.grounded g) fuel' ∧
      qb ∈ mergeBindings b Bindings.empty fuel' := by
  cases fuel with
  | zero =>
      simp [simpleMatch] at hmatch
  | succ n =>
      cases target with
      | var v =>
          exact (GroundAtom.not_var hground).elim
      | symbol s =>
          simp [simpleMatch] at hmatch
      | grounded h =>
          simp [simpleMatch] at hmatch
          rcases hmatch with ⟨hgh, rfl⟩
          refine ⟨1, ?_, ?_⟩
          · subst hgh
            simp [matchAtoms, getMetaType, Atom.groundedType, Bindings.hasLoop, Bindings.empty]
          · rw [mergeBindings_empty_right b 0]
            simp
      | expression es =>
          simp [simpleMatch] at hmatch

/-- `simpleMatch` and `simpleMatchList` are monotone in fuel on successful
runs: once a match succeeds, one extra unit of fuel preserves the same
result.  This is the fuel-skew shim the failure bridge needs, because the
official `matchAtomsList` recursion spends one unit of fuel differently from
the coarse threaded matcher. -/
private theorem simpleMatch_mono_succ (fuel : Nat) :
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
            cases target with
            | var v =>
                simp [simpleMatch] at h
            | symbol t =>
                simp [simpleMatch] at h ⊢
                exact h
            | grounded g =>
                simp [simpleMatch] at h
            | expression es =>
                simp [simpleMatch] at h
        | grounded g =>
            cases target with
            | var v =>
                simp [simpleMatch] at h
            | symbol s =>
                simp [simpleMatch] at h
            | grounded h' =>
                simp [simpleMatch] at h ⊢
                exact h
            | expression es =>
                simp [simpleMatch] at h
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

/-- Contrapositive of `simpleMatch_mono_succ`: if a match fails at fuel
`n+1`, it already failed at fuel `n`.  This is the downward fuel step used to
line up coarse list failures with the official list matcher's inner fuel. -/
private theorem simpleMatch_none_pred (fuel : Nat) :
    (∀ pattern target b,
      simpleMatch pattern target b (fuel + 1) = none →
      simpleMatch pattern target b fuel = none) ∧
    (∀ ps ts b,
      simpleMatch.simpleMatchList ps ts b (fuel + 1) = none →
      simpleMatch.simpleMatchList ps ts b fuel = none) := by
  obtain ⟨hAtomSucc, hListSucc⟩ := simpleMatch_mono_succ fuel
  refine ⟨?_, ?_⟩
  · intro pattern target b hnone
    cases hprev : simpleMatch pattern target b fuel with
    | none =>
        rfl
    | some qb =>
        have hsucc : simpleMatch pattern target b (fuel + 1) = some qb :=
          hAtomSucc pattern target b qb hprev
        rw [hsucc] at hnone
        exact hnone
  · intro ps ts b hnone
    cases hprev : simpleMatch.simpleMatchList ps ts b fuel with
    | none =>
        rfl
    | some qb =>
        have hsucc : simpleMatch.simpleMatchList ps ts b (fuel + 1) = some qb :=
          hListSucc ps ts b qb hprev
        rw [hsucc] at hnone
        exact hnone

/-- Failure leaf: on a ground target, a conflicting seeded variable match has
no official seeded witness at the same fuel. -/
private theorem simpleMatch_ground_var_no_match
    {target : Atom} {b : Bindings} {v : String} {fuel : Nat}
    (hb : GroundBindings b)
    (hground : GroundAtom target)
    (hmatch : simpleMatch (.var v) target b fuel = none) :
    (matchAtoms target (.var v) fuel).flatMap
      (fun mb => mergeBindings b mb fuel) = [] := by
  cases fuel with
  | zero =>
      simp [matchAtoms]
  | succ n =>
      cases hlook : b.lookup v with
      | none =>
          simp [simpleMatch, hlook] at hmatch
      | some prev =>
          simp only [simpleMatch, hlook] at hmatch
          split at hmatch <;> rename_i hsame
          · simp at hmatch
          · have hprev : GroundAtom prev := lookup_ground hb hlook
            have hneq : prev ≠ target := by
              intro heq
              exact hsame (by simp [heq])
            cases n with
            | zero =>
                rw [matchAtoms_ground_var_exact target v 0 hground]
                simp [mergeBindings, addVarBinding, Bindings.empty, Bindings.assign,
                  Bindings.isBound, Bindings.lookup]
            | succ k =>
                rw [matchAtoms_ground_var_exact target v (k + 1) hground]
                have hmerge :
                    mergeBindings b (Bindings.empty.assign v target) (k + 2) = [] := by
                  rw [mergeBindings_single_assign (b := b) (v := v) (val := target) k]
                  cases k with
                  | zero =>
                      simp [addVarBinding, hlook, hsame, matchAtoms]
                  | succ m =>
                      have hmatchNil : matchAtoms prev target (m + 1) = [] :=
                        matchAtoms_ground_ne_nil hprev hground hneq
                      simp [addVarBinding, hlook, hsame, hmatchNil]
                simpa using hmerge

/-- Failure leaf: on a ground target, a symbol-pattern mismatch has no
official seeded witness at the same fuel. -/
private theorem simpleMatch_ground_symbol_no_match
    {target : Atom} {b : Bindings} {s : String} {fuel : Nat}
    (hground : GroundAtom target)
    (hmatch : simpleMatch (.symbol s) target b fuel = none) :
    (matchAtoms target (.symbol s) fuel).flatMap
      (fun mb => mergeBindings b mb fuel) = [] := by
  cases fuel with
  | zero =>
      simp [matchAtoms]
  | succ n =>
      cases target with
      | var v =>
          exact (GroundAtom.not_var hground).elim
      | symbol t =>
          simp [simpleMatch] at hmatch
          have hst : s ≠ t := by simpa using hmatch
          by_cases hts : t = s
          · exact False.elim (hst hts.symm)
          · simp [matchAtoms, getMetaType, Atom.symbolType, hts]
      | grounded g =>
          simp [matchAtoms, getMetaType, Atom.groundedType, Atom.symbolType]
      | expression es =>
          simp [matchAtoms, getMetaType, Atom.expressionType, Atom.symbolType]

/-- Failure leaf: on a ground target, a grounded-pattern mismatch has no
official seeded witness at the same fuel. -/
private theorem simpleMatch_ground_grounded_no_match
    {target : Atom} {b : Bindings} {g : GroundedValue} {fuel : Nat}
    (hground : GroundAtom target)
    (hmatch : simpleMatch (.grounded g) target b fuel = none) :
    (matchAtoms target (.grounded g) fuel).flatMap
      (fun mb => mergeBindings b mb fuel) = [] := by
  cases fuel with
  | zero =>
      simp [matchAtoms]
  | succ n =>
      cases target with
      | var v =>
          exact (GroundAtom.not_var hground).elim
      | symbol s =>
          simp [matchAtoms, getMetaType, Atom.symbolType, Atom.groundedType]
      | grounded h =>
          simp [simpleMatch] at hmatch
          have hgh : g ≠ h := by simpa using hmatch
          by_cases hhg : h = g
          · exact False.elim (hgh hhg.symm)
          · simp [matchAtoms, getMetaType, Atom.groundedType, hhg]
      | expression es =>
          simp [matchAtoms, getMetaType, Atom.expressionType, Atom.groundedType]

/-- If the seeded official list matcher on ground scrutinees factors through
the empty-seeded run plus a final seed merge, then the full ground
`simpleMatch`/`matchAtoms` bridge follows by fuel induction. This isolates the
remaining hard part to the singleton-seed factorization theorem. -/
private theorem simpleMatch_ground_official_of_factor
    (hFactor :
      ∀ {lefts rights b x fuelList},
        (∀ t ∈ lefts, GroundAtom t) →
        GroundBindings b →
        x ∈ matchAtomsList lefts rights [b] fuelList →
          ∃ fuel', ∃ fr,
            fr ∈ matchAtomsList lefts rights [Bindings.empty] fuel' ∧
            x ∈ mergeBindings b fr 2) :
    ∀ fuel : Nat,
      (∀ p t b qb,
        GroundBindings b →
        GroundAtom t →
        simpleMatch p t b fuel = some qb →
          ∃ fuel',
            qb ∈ (matchAtoms t p fuel').flatMap (fun mb => mergeBindings b mb fuel')) ∧
      (∀ ps ts b qb,
        GroundBindings b →
        (∀ t ∈ ts, GroundAtom t) →
        simpleMatch.simpleMatchList ps ts b fuel = some qb →
          ∃ fuel', qb ∈ matchAtomsList ts ps [b] fuel') := by
  intro fuel
  induction fuel with
  | zero =>
      refine ⟨?_, ?_⟩
      · intro p t b qb hb hground hmatch
        simp [simpleMatch] at hmatch
      · intro ps ts b qb hb hground hmatch
        cases ps with
        | nil =>
            cases ts with
            | nil =>
                simp [simpleMatch.simpleMatchList] at hmatch
                subst hmatch
                refine ⟨1, ?_⟩
                simp [matchAtomsList]
            | cons t ts =>
                simp [simpleMatch.simpleMatchList] at hmatch
        | cons p ps =>
            cases ts with
            | nil =>
                simp [simpleMatch.simpleMatchList] at hmatch
            | cons t ts =>
                simp [simpleMatch.simpleMatchList, simpleMatch] at hmatch
  | succ n ih =>
      obtain ⟨ihElem, ihList⟩ := ih
      have hElemSucc :
          ∀ p t b qb,
            GroundBindings b →
            GroundAtom t →
            simpleMatch p t b (n + 1) = some qb →
              ∃ fuel',
                qb ∈ (matchAtoms t p fuel').flatMap (fun mb => mergeBindings b mb fuel') := by
        intro p t b qb hb hground hmatch
        cases p with
        | var v =>
            obtain ⟨fuel', hmb, hmerge⟩ := simpleMatch_ground_var_bridge hground hmatch
            refine ⟨fuel', ?_⟩
            exact List.mem_flatMap.mpr ⟨Bindings.empty.assign v t, hmb, hmerge⟩
        | symbol s =>
            obtain ⟨fuel', hmb, hmerge⟩ := simpleMatch_ground_symbol_bridge hground hmatch
            refine ⟨fuel', ?_⟩
            exact List.mem_flatMap.mpr ⟨Bindings.empty, hmb, hmerge⟩
        | grounded g =>
            obtain ⟨fuel', hmb, hmerge⟩ := simpleMatch_ground_grounded_bridge hground hmatch
            refine ⟨fuel', ?_⟩
            exact List.mem_flatMap.mpr ⟨Bindings.empty, hmb, hmerge⟩
        | expression ps =>
            cases t with
            | var w =>
                exact (GroundAtom.not_var hground).elim
            | symbol s =>
                simp [simpleMatch] at hmatch
            | grounded g =>
                simp [simpleMatch] at hmatch
            | expression ts =>
                have hts : GroundAtom (.expression ts) := hground
                have htsGround : ∀ a ∈ ts, GroundAtom a := by
                  intro a ha
                  exact GroundAtom.elem hts ha
                cases hneq : (ps.length != ts.length) with
                | true =>
                    simp [simpleMatch, hneq] at hmatch
                | false =>
                    have hlen : ps.length = ts.length := by
                      simpa using hneq
                    simp [simpleMatch, hneq] at hmatch
                    obtain ⟨fuelSeeded, hseeded⟩ := ihList ps ts b qb hb htsGround hmatch
                    obtain ⟨fuelFact, fr, hfr, hmerge2⟩ := hFactor htsGround hb hseeded
                    let fuel0 := max fuelFact 2
                    have hFuelFactLe : fuelFact ≤ fuel0 := by
                      dsimp [fuel0]
                      exact Nat.le_max_left _ _
                    have hFuel0Ge2 : 2 ≤ fuel0 := by
                      dsimp [fuel0]
                      exact Nat.le_max_right _ _
                    have hfr' : fr ∈ matchAtomsList ts ps [Bindings.empty] fuel0 := by
                      have hsub := matchAtomsList_mono_add ts ps [Bindings.empty] fuelFact (fuel0 - fuelFact)
                      have hEq : fuelFact + (fuel0 - fuelFact) = fuel0 :=
                        Nat.add_sub_of_le hFuelFactLe
                      simpa [hEq] using hsub fr hfr
                    have hexpr : fr ∈ matchAtoms (.expression ts) (.expression ps) (fuel0 + 1) := by
                      rw [matchAtoms_ground_expr_filter_free ts ps fuel0 htsGround]
                      have hbeq : (ts.length == ps.length) = true := by
                        simp [hlen]
                      simpa [hbeq] using hfr'
                    have hmerge' : qb ∈ mergeBindings b fr (fuel0 + 1) := by
                      have hsub := mergeBindings_mono_add b fr 2 (fuel0 - 1)
                      have hEq : 2 + (fuel0 - 1) = fuel0 + 1 := by
                        omega
                      simpa [hEq] using hsub qb hmerge2
                    refine ⟨fuel0 + 1, ?_⟩
                    exact List.mem_flatMap.mpr ⟨fr, hexpr, hmerge'⟩
      have hListSucc :
          ∀ ps ts b qb,
            GroundBindings b →
            (∀ t ∈ ts, GroundAtom t) →
            simpleMatch.simpleMatchList ps ts b (n + 1) = some qb →
              ∃ fuel', qb ∈ matchAtomsList ts ps [b] fuel' := by
        have hElemSucc' :
            ∀ {p t b qb},
              GroundBindings b →
              GroundAtom t →
              simpleMatch p t b (n + 1) = some qb →
                ∃ fuel',
                  qb ∈ (matchAtoms t p fuel').flatMap (fun mb => mergeBindings b mb fuel') := by
          intro p t b qb hb hground hmatch
          exact hElemSucc p t b qb hb hground hmatch
        intro ps ts b qb hb hground hmatch
        exact simpleMatchList_ground_seeded_of_elem_bridge_ground (n + 1) hElemSucc' hb hground hmatch
      exact ⟨hElemSucc, hListSucc⟩

/-- Full success bridge for one-way `simpleMatch` on the ground fragment:
every successful coarse match is witnessed by an official matcher result
merged back into the same seed. -/
private theorem simpleMatch_ground_official
    {p t : Atom} {seed out : Bindings} {fuel : Nat}
    (hb : GroundBindings seed)
    (ht : GroundAtom t)
    (hmatch : simpleMatch p t seed fuel = some out) :
    ∃ fuel',
      out ∈ (matchAtoms t p fuel').flatMap (fun mb => mergeBindings seed mb fuel') := by
  exact
    (simpleMatch_ground_official_of_factor
      (fun {lefts rights b x fuelList} hlefts hb hmem =>
        matchAtomsList_singleton_factor_ground hlefts hb hmem) fuel).1
      p t seed out hb ht hmatch

/-- Full success bridge for `simpleMatchList` on the ground fragment:
every successful coarse threaded match has an official seeded list-matcher
witness, possibly at a larger fuel. -/
private theorem simpleMatchList_ground_official
    {ps ts : List Atom} {seed out : Bindings} {fuel : Nat}
    (hb : GroundBindings seed)
    (hts : ∀ t ∈ ts, GroundAtom t)
    (hmatch : simpleMatch.simpleMatchList ps ts seed fuel = some out) :
    ∃ fuel', out ∈ matchAtomsList ts ps [seed] fuel' := by
  exact
    (simpleMatch_ground_official_of_factor
      (fun {lefts rights b x fuelList} hlefts hb hmem =>
        matchAtomsList_singleton_factor_ground hlefts hb hmem) fuel).2
      ps ts seed out hb hts hmatch

/-- Empty-seed success bridge on the ground fragment: when a coarse one-way
match succeeds against a ground target from the empty seed, the resulting
bindings themselves appear as an official `matchAtoms` result at some fuel
at least `2`.  This packages away the empty-seed merge bookkeeping and is
the reusable matcher-facing endpoint for later sugar-rule certifications. -/
theorem simpleMatch_ground_matchAtoms
    {pattern target : Atom} {mb : Bindings} {fuel : Nat}
    (hground : GroundAtom target)
    (hmatch : simpleMatch pattern target Bindings.empty fuel = some mb) :
    ∃ fuel', mb ∈ matchAtoms target pattern fuel' ∧ 2 ≤ fuel' := by
  obtain ⟨fuel', hbridge⟩ :=
    simpleMatch_ground_official GroundBindings.empty hground hmatch
  rcases List.mem_flatMap.mp hbridge with ⟨mb0, hmb0, hmerge0⟩
  have hmbCanon : GroundBindingsCanon mb0 := matchAtoms_ground_canon hground hmb0
  let fuel0 := fuel' + 2
  have hmb0' : mb0 ∈ matchAtoms target pattern fuel0 := by
    dsimp [fuel0]
    exact (matchAtoms_mono_add target pattern fuel' 2) mb0 hmb0
  have hmerge0' : mb ∈ mergeBindings Bindings.empty mb0 fuel0 := by
    dsimp [fuel0]
    exact (mergeBindings_mono_add Bindings.empty mb0 fuel' 2) mb hmerge0
  have hmergeDet : mergeGround? Bindings.empty mb0 = some mb := by
    exact
      (mem_mergeBindings_ground_iff
        (left := Bindings.empty) (right := mb0) (result := mb) (fuel := fuel')
        GroundBindings.empty hmbCanon.1).mp hmerge0'
  have hmergeId : mergeGround? Bindings.empty mb0 = some mb0 :=
    mergeGround_empty_left_of_canon hmbCanon
  have hsame : mb = mb0 := by
    rw [hmergeId] at hmergeDet
    injection hmergeDet with hEq
    exact hEq.symm
  refine ⟨fuel0, ?_, ?_⟩
  · simpa [hsame] using hmb0'
  · dsimp [fuel0]
    omega

/-! ## First consumers of the completed matcher bridge -/

/-- On the ground fragment, a successful coarse one-way match from the empty
seed induces the official `unify_match` instruction step with the same
substituted success branch.  This is the matcher-side core theorem later
control-form certifications consume. -/
theorem minimalStep_absorbs_unify_match_ground
    {space : Space} {d : GroundedDispatch}
    {target pattern thenBranch elseBranch : Atom} {mb : Bindings} {fuel : Nat}
    (hground : GroundAtom target)
    (hmatch : simpleMatch pattern target Bindings.empty fuel = some mb) :
    MinimalStep d space
      (.expression [.symbol "unify", target, pattern, thenBranch, elseBranch])
      Bindings.empty space (mb.applyDefault thenBranch, mb) := by
  obtain ⟨fuel0, hmb, hFuel0⟩ := simpleMatch_ground_matchAtoms hground hmatch
  have hmbCanon : GroundBindingsCanon mb := matchAtoms_ground_canon hground hmb
  have hmbGround : GroundBindings mb := hmbCanon.1
  have hnoLoop : mb.hasLoop = false :=
    GroundBindings.hasLoop_false hmbGround
  have hmergeRight : mb ∈ mergeBindings mb Bindings.empty fuel0 := by
    cases fuel0 with
    | zero =>
        omega
    | succ n =>
        rw [mergeBindings_empty_right mb n]
        simp
  exact MinimalStep.unify_match space target pattern thenBranch elseBranch Bindings.empty
    mb mb fuel0 hmb hmergeRight hnoLoop

/-- Empty-seed no-match bridge on the ground fragment for the non-expression
pattern cases: if coarse one-way matching fails, the official matcher also
has no results (at the same fuel).  The expression-pattern case is excluded
here and treated separately later because it depends on the list-level
earlier-branch failure bridge. -/
private theorem simpleMatch_ground_matchAtoms_nil_nonexpr
    {pattern target : Atom} {fuel : Nat}
    (hground : GroundAtom target)
    (h_nonexpr : ¬ ∃ ps, pattern = .expression ps)
    (hmatch : simpleMatch pattern target Bindings.empty fuel = none) :
    matchAtoms target pattern fuel = [] := by
  cases fuel with
  | zero =>
      simp [matchAtoms]
  | succ n =>
      cases pattern with
      | var v =>
          simp [simpleMatch, Bindings.empty, Bindings.lookup] at hmatch
      | symbol s =>
          cases target with
          | var v =>
              exact (GroundAtom.not_var hground).elim
          | symbol t =>
              simp [simpleMatch] at hmatch
              have hst : s ≠ t := by simpa using hmatch
              have hneq : t ≠ s := by
                intro hts
                exact hst hts.symm
              simp [matchAtoms, getMetaType, Atom.symbolType, hneq]
          | grounded g =>
              simp [matchAtoms, getMetaType, Atom.symbolType, Atom.groundedType]
          | expression es =>
              simp [matchAtoms, getMetaType, Atom.symbolType, Atom.expressionType]
      | grounded g =>
          cases target with
          | var v =>
              exact (GroundAtom.not_var hground).elim
          | symbol s =>
              simp [matchAtoms, getMetaType, Atom.symbolType, Atom.groundedType]
          | grounded h =>
              simp [simpleMatch] at hmatch
              have hgh : g ≠ h := by simpa using hmatch
              have hneq : h ≠ g := by
                intro hhg
                exact hgh hhg.symm
              simp [matchAtoms, getMetaType, Atom.groundedType, hneq]
          | expression es =>
              simp [matchAtoms, getMetaType, Atom.expressionType, Atom.groundedType]
      | expression ps =>
          exact False.elim (h_nonexpr ⟨ps, rfl⟩)

/-- Empty-seed no-match bridge on the full ground fragment: if coarse one-way
matching fails, there exists some official matcher fuel witnessing failure
too.  Non-expression patterns can reuse the same fuel; expression patterns
use fuel `1`, whose inner official list matcher has zero fuel and so yields
no candidates. -/
theorem simpleMatch_ground_matchAtoms_nil
    {pattern target : Atom} {fuel : Nat}
    (hground : GroundAtom target)
    (hmatch : simpleMatch pattern target Bindings.empty fuel = none) :
    ∃ fuel', matchAtoms target pattern fuel' = [] := by
  cases pattern with
  | var v =>
      refine ⟨fuel, ?_⟩
      exact simpleMatch_ground_matchAtoms_nil_nonexpr hground
        (by intro h; rcases h with ⟨ps, hps⟩; cases hps)
        hmatch
  | symbol s =>
      refine ⟨fuel, ?_⟩
      exact simpleMatch_ground_matchAtoms_nil_nonexpr hground
        (by intro h; rcases h with ⟨ps, hps⟩; cases hps)
        hmatch
  | grounded g =>
      refine ⟨fuel, ?_⟩
      exact simpleMatch_ground_matchAtoms_nil_nonexpr hground
        (by intro h; rcases h with ⟨ps, hps⟩; cases hps)
        hmatch
  | expression ps =>
      refine ⟨1, ?_⟩
      cases target with
      | var v =>
          exact (GroundAtom.not_var hground).elim
      | symbol s =>
          simp [matchAtoms, getMetaType, Atom.symbolType, Atom.expressionType]
      | grounded g =>
          simp [matchAtoms, getMetaType, Atom.groundedType, Atom.expressionType]
      | expression ts =>
          have hinner : matchAtomsList ts ps [Bindings.empty] 0 = [] := by
            simp [matchAtomsList]
          simp [matchAtoms, getMetaType, Atom.expressionType, hinner]

/-- Ground-fragment no-match absorption for `unify`, on the non-expression
pattern cases.  When coarse one-way matching from the empty seed fails, the
official `unify` instruction takes its `unify_no_match` branch and returns
the else-branch unchanged with empty bindings.  Expression patterns are
excluded here; they need the list-level failure bridge still to come. -/
theorem minimalStep_absorbs_unify_no_match_ground_nonexpr
    {space : Space} {d : GroundedDispatch}
    {target pattern thenBranch elseBranch : Atom} {fuel : Nat}
    (hground : GroundAtom target)
    (h_nonexpr : ¬ ∃ ps, pattern = .expression ps)
    (hmatch : simpleMatch pattern target Bindings.empty fuel = none) :
    MinimalStep d space
      (.expression [.symbol "unify", target, pattern, thenBranch, elseBranch])
      Bindings.empty space (elseBranch, Bindings.empty) := by
  exact MinimalStep.unify_no_match space target pattern thenBranch elseBranch
    Bindings.empty fuel
    (simpleMatch_ground_matchAtoms_nil_nonexpr hground h_nonexpr hmatch)

/-- Ground-fragment no-match absorption for `unify`, with no pattern-shape
restriction: when coarse one-way matching from the empty seed fails, the
official `unify` instruction takes its `unify_no_match` branch at some fuel
and returns the else-branch unchanged with empty bindings. -/
theorem minimalStep_absorbs_unify_no_match_ground
    {space : Space} {d : GroundedDispatch}
    {target pattern thenBranch elseBranch : Atom} {fuel : Nat}
    (hground : GroundAtom target)
    (hmatch : simpleMatch pattern target Bindings.empty fuel = none) :
    MinimalStep d space
      (.expression [.symbol "unify", target, pattern, thenBranch, elseBranch])
      Bindings.empty space (elseBranch, Bindings.empty) := by
  obtain ⟨fuel0, hnil⟩ := simpleMatch_ground_matchAtoms_nil hground hmatch
  exact MinimalStep.unify_no_match space target pattern thenBranch elseBranch
    Bindings.empty fuel0 hnil

/-- **F3, `let` substitution half on the ground fragment.**  The verbatim
upstream rhs of `let`,
`(unify <value> <pattern> <template> Empty)`, takes an official
`unify_match` step whenever the coarse one-way matcher succeeds on a ground
value.  This is the first end-to-end consumer of the completed matcher
bridge. -/
theorem minimalStep_absorbs_let_subst_ground
    {space : Space} {d : GroundedDispatch}
    {pt value body : Atom} {mb : Bindings} {fuel : Nat}
    (hground : GroundAtom value)
    (hmatch : simpleMatch pt value Bindings.empty fuel = some mb) :
    MinimalStep d space (.expression [.symbol "unify", value, pt, body, Atom.empty])
      Bindings.empty space (mb.applyDefault body, mb) :=
  minimalStep_absorbs_unify_match_ground hground hmatch

/-- **F3, `switch-internal` first-branch hit on the ground fragment.**
The verbatim upstream `switch-internal` rhs delegates its head branch to a
`unify`; when the coarse one-way matcher succeeds on a ground scrutinee, that
`unify` takes the official `unify_match` step to the chosen branch's returned
template.  This is the success-half core that the later `HES_SwitchMinimal`
certification will compose through the surrounding recursion. -/
theorem minimalStep_absorbs_switch_internal_head_match_ground
    {space : Space} {d : GroundedDispatch}
    {scrut pt template : Atom} {tail : List Atom} {mb : Bindings} {fuel : Nat}
    (hground : GroundAtom scrut)
    (hmatch : simpleMatch pt scrut Bindings.empty fuel = some mb) :
    MinimalStep d space
      (.expression [.symbol "unify", scrut, pt,
        .expression [.symbol "return", template],
        .expression [.symbol "chain",
          .expression [.symbol "eval",
            .expression [.symbol "switch-minimal", scrut, .expression tail]],
          .var "ret",
          .expression [.symbol "return", .var "ret"]]])
      Bindings.empty space
      (mb.applyDefault (.expression [.symbol "return", template]), mb) :=
  minimalStep_absorbs_unify_match_ground hground hmatch

/-- **F3, `switch-internal` head miss on the ground/non-expression fragment.**
When the head branch's coarse one-way matcher fails from the empty seed, the
official `unify` takes its no-match branch and returns the recursive else
branch unchanged.  This is the first failure-side consumer on the exact
upstream `switch-internal` shape; the expression-pattern case is excluded
until the list-level earlier-branch failure bridge lands. -/
theorem minimalStep_absorbs_switch_internal_head_no_match_ground_nonexpr
    {space : Space} {d : GroundedDispatch}
    {scrut pt template : Atom} {tail : List Atom} {fuel : Nat}
    (hground : GroundAtom scrut)
    (h_nonexpr : ¬ ∃ ps, pt = .expression ps)
    (hmatch : simpleMatch pt scrut Bindings.empty fuel = none) :
    MinimalStep d space
      (.expression [.symbol "unify", scrut, pt,
        .expression [.symbol "return", template],
        .expression [.symbol "chain",
          .expression [.symbol "eval",
            .expression [.symbol "switch-minimal", scrut, .expression tail]],
          .var "ret",
          .expression [.symbol "return", .var "ret"]]])
      Bindings.empty space
      (.expression [.symbol "chain",
        .expression [.symbol "eval",
          .expression [.symbol "switch-minimal", scrut, .expression tail]],
        .var "ret",
        .expression [.symbol "return", .var "ret"]],
        Bindings.empty) :=
  minimalStep_absorbs_unify_no_match_ground_nonexpr hground h_nonexpr hmatch

/-- **F3, `switch-internal` head miss on the full ground fragment.**
When the head branch's coarse one-way matcher fails from the empty seed, the
official `unify` takes its no-match branch and returns the recursive else
branch unchanged.  This packages the completed empty-seed failure bridge in
the exact upstream `switch-internal` shape. -/
theorem minimalStep_absorbs_switch_internal_head_no_match_ground
    {space : Space} {d : GroundedDispatch}
    {scrut pt template : Atom} {tail : List Atom} {fuel : Nat}
    (hground : GroundAtom scrut)
    (hmatch : simpleMatch pt scrut Bindings.empty fuel = none) :
    MinimalStep d space
      (.expression [.symbol "unify", scrut, pt,
        .expression [.symbol "return", template],
        .expression [.symbol "chain",
          .expression [.symbol "eval",
            .expression [.symbol "switch-minimal", scrut, .expression tail]],
          .var "ret",
          .expression [.symbol "return", .var "ret"]]])
      Bindings.empty space
      (.expression [.symbol "chain",
        .expression [.symbol "eval",
          .expression [.symbol "switch-minimal", scrut, .expression tail]],
        .var "ret",
        .expression [.symbol "return", .var "ret"]],
        Bindings.empty) :=
  minimalStep_absorbs_unify_no_match_ground hground hmatch

/-! ## F2: Ground `unify` Realization Boundary

The matcher bridge and the `MinimalStep.unify_*` absorption theorems above pin
the official *instruction-level* behavior.  The remaining sugar-rule
certifications need one more handoff: the live HE evaluator must actually
realize those `unify` instructions at the `EvalAtom` entry point under the
active dispatch.  We state that boundary explicitly instead of folding it into
the later surface-rule theorems. -/

/-- Executable raw-branch realization needed to spend the matcher bridge inside
surface sugar proofs.

Positive example:
- a successful coarse ground match makes the evaluator stably return the
  substituted success branch for the corresponding `unify`.

Negative example:
- a failed coarse ground match makes the evaluator stably return the else
  branch unchanged for the corresponding `unify`.

This deliberately stops at the primitive operator boundary: it certifies only
the raw branch result that upstream `unify` itself returns, not any further
evaluation of that chosen branch in enclosing contexts. -/
structure UnifyGroundBranchRealization (space : Space) (d : GroundedDispatch) where
  matchStable :
    ∀ {target pattern thenBranch elseBranch mb fuel},
      GroundAtom target →
      simpleMatch pattern target Bindings.empty fuel = some mb →
      EvalAtomStablyReaches space d
        (.expression [.symbol "unify", target, pattern, thenBranch, elseBranch])
        Atom.undefinedType Bindings.empty
        (mb.applyDefault thenBranch, mb)
  noMatchStable :
    ∀ {target pattern thenBranch elseBranch fuel},
      GroundAtom target →
      simpleMatch pattern target Bindings.empty fuel = none →
      EvalAtomStablyReaches space d
        (.expression [.symbol "unify", target, pattern, thenBranch, elseBranch])
        Atom.undefinedType Bindings.empty
        (elseBranch, Bindings.empty)

/-- Seeded raw-branch realization for the equation-helper route: in addition
to the empty-seed `unify` outcomes above, some sugar wrappers need the
evaluator to realize the same official primitive `unify` behavior when the
incoming bindings are a non-empty seed supplied by an outer equation query.

Positive example:
- a seeded official `unify_match` result under query bindings still evaluates
  to the merged substituted success branch.

Negative example:
- a seeded official `unify_no_match` result still returns its else branch
  under the same incoming bindings, rather than silently resetting to empty. -/
structure UnifyGroundSeededBranchRealization (space : Space) (d : GroundedDispatch)
    extends UnifyGroundBranchRealization space d where
  matchStableSeeded :
    ∀ {seed target pattern thenBranch elseBranch mb merged fuel},
      GroundAtom target →
      mb ∈ matchAtoms target pattern fuel →
      merged ∈ mergeBindings mb seed fuel →
      merged.hasLoop = false →
      EvalAtomStablyReaches space d
        (.expression [.symbol "unify", target, pattern, thenBranch, elseBranch])
        Atom.undefinedType seed
        (merged.applyDefault thenBranch, merged)
  noMatchStableSeeded :
    ∀ {seed target pattern thenBranch elseBranch fuel},
      GroundAtom target →
      matchAtoms target pattern fuel = [] →
      EvalAtomStablyReaches space d
        (.expression [.symbol "unify", target, pattern, thenBranch, elseBranch])
        Atom.undefinedType seed
        (elseBranch, seed)

/-- Spending the realization boundary on the success branch: a successful
coarse ground match yields the public declarative `EvalAtom` judgment for the
corresponding `unify` expression. -/
theorem evalAtom_realizes_unify_match_ground
    {space : Space} {d : GroundedDispatch}
    (hReal : UnifyGroundBranchRealization space d)
    {target pattern thenBranch elseBranch : Atom} {mb : Bindings} {fuel : Nat}
    (hground : GroundAtom target)
    (hmatch : simpleMatch pattern target Bindings.empty fuel = some mb) :
    EvalAtom space d
      (.expression [.symbol "unify", target, pattern, thenBranch, elseBranch])
      Atom.undefinedType Bindings.empty
      (mb.applyDefault thenBranch, mb) :=
  evalAtomStablyReaches_to_EvalAtom space d
    (.expression [.symbol "unify", target, pattern, thenBranch, elseBranch])
    Atom.undefinedType Bindings.empty
    (mb.applyDefault thenBranch, mb)
    (hReal.matchStable hground hmatch)

/-- Spending the realization boundary on the failure branch: a failed coarse
ground match yields the public declarative `EvalAtom` judgment for the
corresponding `unify` expression's else branch. -/
theorem evalAtom_realizes_unify_no_match_ground
    {space : Space} {d : GroundedDispatch}
    (hReal : UnifyGroundBranchRealization space d)
    {target pattern thenBranch elseBranch : Atom} {fuel : Nat}
    (hground : GroundAtom target)
    (hmatch : simpleMatch pattern target Bindings.empty fuel = none) :
    EvalAtom space d
      (.expression [.symbol "unify", target, pattern, thenBranch, elseBranch])
      Atom.undefinedType Bindings.empty
      (elseBranch, Bindings.empty) :=
  evalAtomStablyReaches_to_EvalAtom space d
    (.expression [.symbol "unify", target, pattern, thenBranch, elseBranch])
    Atom.undefinedType Bindings.empty
    (elseBranch, Bindings.empty)
    (hReal.noMatchStable hground hmatch)

/-- Seeded consumer of the stronger evaluator boundary: an official ground
`unify_match` witness can be spent under any incoming seed bindings, not just
the empty seed.  This is the exact form the stdlib equation-helper wrappers
need after `queryEquations` has contributed its fresh local bindings. -/
theorem evalAtom_realizes_unify_match_ground_seeded
    {space : Space} {d : GroundedDispatch}
    (hReal : UnifyGroundSeededBranchRealization space d)
    {seed mb merged : Bindings}
    {target pattern thenBranch elseBranch : Atom} {fuel : Nat}
    (hground : GroundAtom target)
    (hmatch : mb ∈ matchAtoms target pattern fuel)
    (hmerge : merged ∈ mergeBindings mb seed fuel)
    (h_no_loop : merged.hasLoop = false) :
    EvalAtom space d
      (.expression [.symbol "unify", target, pattern, thenBranch, elseBranch])
      Atom.undefinedType seed
      (merged.applyDefault thenBranch, merged) :=
  evalAtomStablyReaches_to_EvalAtom space d
    (.expression [.symbol "unify", target, pattern, thenBranch, elseBranch])
    Atom.undefinedType seed
    (merged.applyDefault thenBranch, merged)
    (hReal.matchStableSeeded hground hmatch hmerge h_no_loop)

/-- Seeded no-match consumer of the stronger evaluator boundary: an official
ground `unify_no_match` witness can also be spent under non-empty incoming
bindings.  This is the equation-helper companion to the empty-seed theorem
above. -/
theorem evalAtom_realizes_unify_no_match_ground_seeded
    {space : Space} {d : GroundedDispatch}
    (hReal : UnifyGroundSeededBranchRealization space d)
    {seed : Bindings}
    {target pattern thenBranch elseBranch : Atom} {fuel : Nat}
    (hground : GroundAtom target)
    (hmatch : matchAtoms target pattern fuel = []) :
    EvalAtom space d
      (.expression [.symbol "unify", target, pattern, thenBranch, elseBranch])
      Atom.undefinedType seed
      (elseBranch, seed) :=
  evalAtomStablyReaches_to_EvalAtom space d
    (.expression [.symbol "unify", target, pattern, thenBranch, elseBranch])
    Atom.undefinedType seed
    (elseBranch, seed)
    (hReal.noMatchStableSeeded hground hmatch)

/-- Seeded specialization for `let`'s `unify` rhs.  This is the missing
equation-helper form of the already-landed empty-seed consumer. -/
theorem evalAtom_realizes_let_subst_ground_seeded
    {space : Space} {d : GroundedDispatch}
    (hReal : UnifyGroundSeededBranchRealization space d)
    {seed mb merged : Bindings}
    {pt value body : Atom} {fuel : Nat}
    (hground : GroundAtom value)
    (hmatch : mb ∈ matchAtoms value pt fuel)
    (hmerge : merged ∈ mergeBindings mb seed fuel)
    (h_no_loop : merged.hasLoop = false) :
    EvalAtom space d
      (.expression [.symbol "unify", value, pt, body, Atom.empty])
      Atom.undefinedType seed
      (merged.applyDefault body, merged) :=
  evalAtom_realizes_unify_match_ground_seeded hReal hground hmatch hmerge h_no_loop

/-- Realized evaluator form of the `let` substitution half on the ground
fragment.  This is the first surface-sugar consumer of the explicit `unify`
realization boundary. -/
theorem evalAtom_realizes_let_subst_ground
    {space : Space} {d : GroundedDispatch}
    (hReal : UnifyGroundBranchRealization space d)
    {pt value body : Atom} {mb : Bindings} {fuel : Nat}
    (hground : GroundAtom value)
    (hmatch : simpleMatch pt value Bindings.empty fuel = some mb) :
    EvalAtom space d
      (.expression [.symbol "unify", value, pt, body, Atom.empty])
      Atom.undefinedType Bindings.empty
      (mb.applyDefault body, mb) :=
  evalAtom_realizes_unify_match_ground hReal hground hmatch

/-- Realized evaluator form of the `switch-internal` head-hit branch on the
ground fragment.  This is the direct success-side ingredient for the later
`switch-minimal` certification. -/
theorem evalAtom_realizes_switch_internal_head_match_ground
    {space : Space} {d : GroundedDispatch}
    (hReal : UnifyGroundBranchRealization space d)
    {scrut pt template : Atom} {tail : List Atom} {mb : Bindings} {fuel : Nat}
    (hground : GroundAtom scrut)
    (hmatch : simpleMatch pt scrut Bindings.empty fuel = some mb) :
    EvalAtom space d
      (.expression [.symbol "unify", scrut, pt,
        .expression [.symbol "return", template],
        .expression [.symbol "chain",
          .expression [.symbol "eval",
            .expression [.symbol "switch-minimal", scrut, .expression tail]],
          .var "ret",
          .expression [.symbol "return", .var "ret"]]])
      Atom.undefinedType Bindings.empty
      (mb.applyDefault (.expression [.symbol "return", template]), mb) :=
  evalAtom_realizes_unify_match_ground
    hReal hground hmatch

/-- Realized evaluator form of the `switch-internal` head-miss branch on the
ground fragment.  This is the failure-side ingredient for the later
`switch-minimal` certification. -/
theorem evalAtom_realizes_switch_internal_head_no_match_ground
    {space : Space} {d : GroundedDispatch}
    (hReal : UnifyGroundBranchRealization space d)
    {scrut pt template : Atom} {tail : List Atom} {fuel : Nat}
    (hground : GroundAtom scrut)
    (hmatch : simpleMatch pt scrut Bindings.empty fuel = none) :
    EvalAtom space d
      (.expression [.symbol "unify", scrut, pt,
        .expression [.symbol "return", template],
        .expression [.symbol "chain",
          .expression [.symbol "eval",
            .expression [.symbol "switch-minimal", scrut, .expression tail]],
          .var "ret",
          .expression [.symbol "return", .var "ret"]]])
      Atom.undefinedType Bindings.empty
      (.expression [.symbol "chain",
        .expression [.symbol "eval",
          .expression [.symbol "switch-minimal", scrut, .expression tail]],
        .var "ret",
        .expression [.symbol "return", .var "ret"]],
        Bindings.empty) :=
  evalAtom_realizes_unify_no_match_ground
    hReal hground hmatch

/-! ## F3: `let` Function/Equation Shell

The matcher bridge now gives us the `unify` core.  The next honest outer layer
is the verbatim upstream `let` shell: the operator's typed function-path
interpretation, then the equation-call wrapper that invokes the `unify` rhs.

We keep this shell explicit instead of folding it into the later rule theorem:
it is the exact typed/equational boundary the final `HES_Let` certification
will spend. -/

/-- The verbatim upstream function type annotation for `unify`. -/
private def unifyFunctionType : Atom :=
  .expression [.symbol "->", Atom.atomType, Atom.atomType,
    Atom.atomType, Atom.atomType, Atom.undefinedType]

/-- Surface `unify` atom in the upstream stdlib shape. -/
private def unifyExpr (target pattern thenBranch elseBranch : Atom) : Atom :=
  .expression [.symbol "unify", target, pattern, thenBranch, elseBranch]

/-- The verbatim upstream function type annotation for `let`. -/
private def letFunctionType : Atom :=
  .expression [.symbol "->", Atom.atomType, Atom.undefinedType,
    Atom.atomType, Atom.undefinedType]

/-- Surface `let` atom in the upstream stdlib shape. -/
private def letExpr (pt value body : Atom) : Atom :=
  .expression [.symbol "let", pt, value, body]

/-- The verbatim upstream rhs for `let`: a `unify` over the evaluated value. -/
private def letUnifyRhs (pt value body : Atom) : Atom :=
  .expression [.symbol "unify", value, pt, body, Atom.empty]

/-- If the space presents `let` with exactly its stdlib function type, then
the official type-cast path evaluates the head symbol to itself at that type.

Positive example:
- `(: let (-> Atom %Undefined% Atom %Undefined%))` gives the expected head step.

Negative example:
- without the exact annotation, this theorem does not apply; the typed
  function-path shell is an explicit hypothesis boundary, not folklore. -/
private theorem evalAtom_let_head_typed
    {space : Space} {d : GroundedDispatch}
    (h_types : getAtomTypes space (.symbol "let") = [letFunctionType]) :
    EvalAtom space d (.symbol "let") letFunctionType Bindings.empty
      (.symbol "let", Bindings.empty) := by
  refine EvalAtom.type_cast _ _ _ _ 10 rfl ?_ (Or.inl rfl) ?_
  · simp [letFunctionType, getMetaType, Atom.atomType,
      Atom.symbolType, Atom.undefinedType, Atom.variableType]
  · rw [typeCast, h_types]
    have hmatch : matchAtoms letFunctionType letFunctionType 10 = [Bindings.empty] := by
      native_decide
    have hmerge : mergeBindings Bindings.empty Bindings.empty 10 = [Bindings.empty] := by
      simpa using mergeBindings_empty_right Bindings.empty 9
    have hflat :
        List.flatMap (fun mb => mergeBindings Bindings.empty mb 10)
          (matchAtoms letFunctionType letFunctionType 10) = [Bindings.empty] := by
      rw [hmatch]
      simp [hmerge]
    have hmt : matchTypes letFunctionType letFunctionType Bindings.empty 10 = [Bindings.empty] := by
      unfold matchTypes
      have hcond :
          (letFunctionType == Atom.undefinedType || letFunctionType == Atom.atomType ||
              letFunctionType == Atom.undefinedType || letFunctionType == Atom.atomType) = false := by
        native_decide
      simp [hcond, hflat]
    rw [typeCast.typeCastLoop, hmt]
    simp

/-- Seeded companion to `evalAtom_let_head_typed`: the typed `let` head
evaluates to itself under any incoming bindings thread, not just
`Bindings.empty`.  This is the head-side boundary the source-progress half
of `HES_Let` will need once value evaluation has already shifted the
bindings thread. -/
private theorem evalAtom_let_head_typed_seeded
    {space : Space} {d : GroundedDispatch} {seed : Bindings}
    (h_types : getAtomTypes space (.symbol "let") = [letFunctionType]) :
    EvalAtom space d (.symbol "let") letFunctionType seed
      (.symbol "let", seed) := by
  refine EvalAtom.type_cast _ _ _ _ 10 rfl ?_ (Or.inl rfl) ?_
  · simp [letFunctionType, getMetaType, Atom.atomType,
      Atom.symbolType, Atom.undefinedType, Atom.variableType]
  · rw [typeCast, h_types]
    have hmatch : matchAtoms letFunctionType letFunctionType 10 = [Bindings.empty] := by
      native_decide
    have hmerge : mergeBindings seed Bindings.empty 10 = [seed] := by
      simpa using mergeBindings_empty_right seed 9
    have hflat :
        List.flatMap (fun mb => mergeBindings seed mb 10)
          (matchAtoms letFunctionType letFunctionType 10) = [seed] := by
      rw [hmatch]
      simp [hmerge]
    have hmt : matchTypes letFunctionType letFunctionType seed 10 = [seed] := by
      unfold matchTypes
      have hcond :
          (letFunctionType == Atom.undefinedType || letFunctionType == Atom.atomType ||
              letFunctionType == Atom.undefinedType || letFunctionType == Atom.atomType) = false := by
        native_decide
      simp [hcond, hflat]
    rw [typeCast.typeCastLoop, hmt]
    simp

/-- Any atom can be evaluated against the expected type `Atom`, producing
itself with unchanged bindings. -/
private theorem evalAtom_atom_type
    {space : Space} {d : GroundedDispatch} (a : Atom) (b : Bindings) :
    EvalAtom space d a Atom.atomType b (a, b) := by
  by_cases h : isEmptyOrError a = true
  · exact EvalAtom.empty_or_error _ _ _ h
  · exact EvalAtom.type_pass _ _ _ (by simpa using h) (Or.inl rfl)

/-- If the space presents `unify` with exactly its stdlib function type, then
the official type-cast path evaluates the head symbol to itself at that type
under any incoming bindings thread. -/
private theorem evalAtom_unify_head_typed_seeded
    {space : Space} {d : GroundedDispatch} {seed : Bindings}
    (h_types : getAtomTypes space (.symbol "unify") = [unifyFunctionType]) :
    EvalAtom space d (.symbol "unify") unifyFunctionType seed
      (.symbol "unify", seed) := by
  refine EvalAtom.type_cast _ _ _ _ 10 rfl ?_ (Or.inl rfl) ?_
  · simp [unifyFunctionType, getMetaType, Atom.atomType,
      Atom.symbolType, Atom.undefinedType, Atom.variableType]
  · rw [typeCast, h_types]
    have hmatch : matchAtoms unifyFunctionType unifyFunctionType 10 = [Bindings.empty] := by
      native_decide
    have hmerge : mergeBindings seed Bindings.empty 10 = [seed] := by
      simpa using mergeBindings_empty_right seed 9
    have hflat :
        List.flatMap (fun mb => mergeBindings seed mb 10)
          (matchAtoms unifyFunctionType unifyFunctionType 10) = [seed] := by
      rw [hmatch]
      simp [hmerge]
    have hmt : matchTypes unifyFunctionType unifyFunctionType seed 10 = [seed] := by
      unfold matchTypes
      have hcond :
          (unifyFunctionType == Atom.undefinedType || unifyFunctionType == Atom.atomType ||
              unifyFunctionType == Atom.undefinedType || unifyFunctionType == Atom.atomType) = false := by
        native_decide
      simp [hcond, hflat]
    rw [typeCast.typeCastLoop, hmt]
    simp

/-- The four `unify` arguments officially interpret to themselves on the
Atom-typed fragment, under an arbitrary incoming bindings thread.  We keep the
bare-`Error` exclusions explicit because the typed function path filters on
error-shaped intermediate tuple shells. -/
private theorem interpretArgs_unify_self_seeded
    {space : Space} {d : GroundedDispatch}
    {target pattern thenBranch elseBranch : Atom} {seed : Bindings}
    (h_pattern_nerr : pattern ≠ Atom.symbol "Error")
    (h_then_nerr : thenBranch ≠ Atom.symbol "Error")
    (h_else_nerr : elseBranch ≠ Atom.symbol "Error") :
    InterpretArgs space d [target, pattern, thenBranch, elseBranch]
      [Atom.atomType, Atom.atomType, Atom.atomType, Atom.atomType]
      seed
      (.expression [target, pattern, thenBranch, elseBranch], seed) := by
  have h_target : EvalAtom space d target Atom.atomType seed (target, seed) :=
    evalAtom_atom_type target seed
  have h_pattern : EvalAtom space d pattern Atom.atomType seed (pattern, seed) :=
    evalAtom_atom_type pattern seed
  have h_then : EvalAtom space d thenBranch Atom.atomType seed (thenBranch, seed) :=
    evalAtom_atom_type thenBranch seed
  have h_else : EvalAtom space d elseBranch Atom.atomType seed (elseBranch, seed) :=
    evalAtom_atom_type elseBranch seed
  have h_tail_else : InterpretArgs space d [elseBranch] [Atom.atomType]
      seed (.expression [elseBranch], seed) := by
    exact InterpretArgs.cons_ok elseBranch [] Atom.atomType [] seed
      (elseBranch, seed) (Atom.unit, seed)
      h_else (Or.inr rfl) InterpretArgs.nil rfl
  have h_tail_then : InterpretArgs space d [thenBranch, elseBranch]
      [Atom.atomType, Atom.atomType] seed
      (.expression [thenBranch, elseBranch], seed) := by
    refine InterpretArgs.cons_ok thenBranch [elseBranch] Atom.atomType
      [Atom.atomType] seed
      (thenBranch, seed) (.expression [elseBranch], seed)
      h_then (Or.inr rfl) h_tail_else ?_
    exact isEmptyOrError_expr_false [] h_else_nerr
  have h_tail_pattern : InterpretArgs space d [pattern, thenBranch, elseBranch]
      [Atom.atomType, Atom.atomType, Atom.atomType] seed
      (.expression [pattern, thenBranch, elseBranch], seed) := by
    refine InterpretArgs.cons_ok pattern [thenBranch, elseBranch] Atom.atomType
      [Atom.atomType, Atom.atomType] seed
      (pattern, seed) (.expression [thenBranch, elseBranch], seed)
      h_pattern (Or.inr rfl) h_tail_then ?_
    exact isEmptyOrError_expr_false [elseBranch] h_then_nerr
  refine InterpretArgs.cons_ok target [pattern, thenBranch, elseBranch] Atom.atomType
    [Atom.atomType, Atom.atomType, Atom.atomType] seed
    (target, seed) (.expression [pattern, thenBranch, elseBranch], seed)
    h_target (Or.inr rfl) h_tail_pattern ?_
  exact isEmptyOrError_expr_false (thenBranch :: [elseBranch]) h_pattern_nerr

/-- The official typed function-path shell for the verbatim upstream `unify`
surface form on the self-evaluating Atom-typed fragment. -/
private theorem interpretFunction_unify_self_seeded
    {space : Space} {d : GroundedDispatch}
    {target pattern thenBranch elseBranch : Atom} {seed : Bindings}
    (h_types : getAtomTypes space (.symbol "unify") = [unifyFunctionType])
    (h_target_nerr : target ≠ Atom.symbol "Error")
    (h_pattern_nerr : pattern ≠ Atom.symbol "Error")
    (h_then_nerr : thenBranch ≠ Atom.symbol "Error")
    (h_else_nerr : elseBranch ≠ Atom.symbol "Error") :
    InterpretFunction space d (unifyExpr target pattern thenBranch elseBranch)
      unifyFunctionType Atom.undefinedType seed
      (unifyExpr target pattern thenBranch elseBranch, seed) := by
  have h_head : EvalAtom space d (.symbol "unify") unifyFunctionType seed
      (.symbol "unify", seed) :=
    evalAtom_unify_head_typed_seeded h_types
  have h_tail : InterpretArgs space d [target, pattern, thenBranch, elseBranch]
      [Atom.atomType, Atom.atomType, Atom.atomType, Atom.atomType]
      seed
      (.expression [target, pattern, thenBranch, elseBranch], seed) :=
    interpretArgs_unify_self_seeded
      h_pattern_nerr h_then_nerr h_else_nerr
  refine InterpretFunction.head_ok_tail_ok
    (unifyExpr target pattern thenBranch elseBranch)
    unifyFunctionType Atom.undefinedType seed
    (.symbol "unify") [target, pattern, thenBranch, elseBranch]
    [Atom.atomType, Atom.atomType, Atom.atomType, Atom.atomType]
    (.symbol "unify", seed)
    (.expression [target, pattern, thenBranch, elseBranch], seed)
    rfl rfl h_head rfl h_tail ?_
  exact isEmptyOrError_expr_false
    (pattern :: thenBranch :: [elseBranch]) h_target_nerr

/-- Outer official `unify` shell, relative to the explicit typed-function path
and a supplied official `MettaCall` witness for the raw branch result. -/
private theorem evalAtom_absorbs_unify_shell_of_interp
    {space : Space} {d : GroundedDispatch}
    {target pattern thenBranch elseBranch : Atom} {seed : Bindings}
    {interpResult final : ResultPair}
    {succs : List Bindings} {fuel : Nat}
    (h_op_type : unifyFunctionType ∈ getAtomTypes space (.symbol "unify"))
    (h_check : checkIfFunctionTypeIsApplicable
      (unifyExpr target pattern thenBranch elseBranch)
      unifyFunctionType Atom.undefinedType
      space seed fuel = .inr succs)
    (h_check_b : seed ∈ succs)
    (h_interp : InterpretFunction space d
      (unifyExpr target pattern thenBranch elseBranch)
      unifyFunctionType Atom.undefinedType seed interpResult)
    (h_call : MettaCall space d interpResult.1
      Atom.undefinedType interpResult.2 final) :
    EvalAtom space d (unifyExpr target pattern thenBranch elseBranch)
      Atom.undefinedType seed final := by
  have h_unify_nerr : (.symbol "unify") ≠ Atom.symbol "Error" := by
    simp
  by_cases h_final_err : isErrorAtom final.1 = true
  · refine EvalAtom.interpret_error _ _ _ _ ?_ ?_ rfl ?_ ?_ h_final_err
    · exact isEmptyOrError_expr_false
        (pattern :: thenBranch :: [elseBranch]) h_unify_nerr
    · simp [unifyExpr, getMetaType, Atom.undefinedType, Atom.atomType,
        Atom.expressionType, Atom.variableType]
    · intro h_unit
      simp [unifyExpr, Atom.unit] at h_unit
    · refine InterpretExpression.function_path _ _ _
        (.symbol "unify") [target, pattern, thenBranch, elseBranch]
        unifyFunctionType Atom.undefinedType seed
        interpResult final fuel
        rfl h_op_type ?_ succs h_check h_check_b rfl h_interp h_call
      rfl
  · refine EvalAtom.interpret_success _ _ _ _ ?_ ?_ rfl ?_ ?_ ?_
    · exact isEmptyOrError_expr_false
        (pattern :: thenBranch :: [elseBranch]) h_unify_nerr
    · simp [unifyExpr, getMetaType, Atom.undefinedType, Atom.atomType,
        Atom.expressionType, Atom.variableType]
    · intro h_unit
      simp [unifyExpr, Atom.unit] at h_unit
    · refine InterpretExpression.function_path _ _ _
        (.symbol "unify") [target, pattern, thenBranch, elseBranch]
        unifyFunctionType Atom.undefinedType seed
        interpResult final fuel
        rfl h_op_type ?_ succs h_check h_check_b rfl h_interp h_call
      rfl
    · simpa using h_final_err

/-- Typed official evaluator form of the primitive `unify` success branch,
under the exact stdlib `unify` annotation and the self-evaluating Atom-typed
argument shell. -/
theorem evalAtom_realizes_unify_match_ground_seeded_typed
    {space : Space} {d : GroundedDispatch}
    {seed mb merged : Bindings}
    {target pattern thenBranch elseBranch : Atom} {fuel : Nat}
    {succs : List Bindings} {fuelShell : Nat}
    (h_types : getAtomTypes space (.symbol "unify") = [unifyFunctionType])
    (h_target_nerr : target ≠ Atom.symbol "Error")
    (h_pattern_nerr : pattern ≠ Atom.symbol "Error")
    (h_then_nerr : thenBranch ≠ Atom.symbol "Error")
    (h_else_nerr : elseBranch ≠ Atom.symbol "Error")
    (h_check : checkIfFunctionTypeIsApplicable
      (unifyExpr target pattern thenBranch elseBranch)
      unifyFunctionType Atom.undefinedType
      space seed fuelShell = .inr succs)
    (h_check_b : seed ∈ succs)
    (hmatch : mb ∈ matchAtoms target pattern fuel)
    (hmerge : merged ∈ mergeBindings mb seed fuel)
    (h_no_loop : merged.hasLoop = false) :
    EvalAtom space d
      (unifyExpr target pattern thenBranch elseBranch)
      Atom.undefinedType seed
      (merged.applyDefault thenBranch, merged) := by
  have h_interp : InterpretFunction space d
      (unifyExpr target pattern thenBranch elseBranch)
      unifyFunctionType Atom.undefinedType seed
      (unifyExpr target pattern thenBranch elseBranch, seed) :=
    interpretFunction_unify_self_seeded h_types
      h_target_nerr h_pattern_nerr h_then_nerr h_else_nerr
  have h_raw :
      (merged.applyDefault thenBranch, merged) ∈
        unifySuccessResults target pattern thenBranch seed fuel := by
    refine List.mem_flatMap.mpr ?_
    refine ⟨mb, hmatch, ?_⟩
    exact List.mem_filterMap.mpr ⟨merged, hmerge, by simp [h_no_loop]⟩
  have h_call : MettaCall space d
      (unifyExpr target pattern thenBranch elseBranch)
      Atom.undefinedType seed
      (merged.applyDefault thenBranch, merged) :=
    MettaCall.unify_success_raw
      (unifyExpr target pattern thenBranch elseBranch)
      Atom.undefinedType seed
      target pattern thenBranch elseBranch
      (merged.applyDefault thenBranch, merged) fuel
      rfl (by simp [unifyExpr, isErrorAtom]) h_raw
  have h_op_type : unifyFunctionType ∈ getAtomTypes space (.symbol "unify") := by
    rw [h_types]
    simp
  exact evalAtom_absorbs_unify_shell_of_interp
    h_op_type h_check h_check_b h_interp h_call

/-- Typed official evaluator form of the primitive `unify` no-match branch,
under the exact stdlib `unify` annotation and the self-evaluating Atom-typed
argument shell. -/
theorem evalAtom_realizes_unify_no_match_ground_seeded_typed
    {space : Space} {d : GroundedDispatch}
    {seed : Bindings}
    {target pattern thenBranch elseBranch : Atom} {fuel : Nat}
    {succs : List Bindings} {fuelShell : Nat}
    (h_types : getAtomTypes space (.symbol "unify") = [unifyFunctionType])
    (h_target_nerr : target ≠ Atom.symbol "Error")
    (h_pattern_nerr : pattern ≠ Atom.symbol "Error")
    (h_then_nerr : thenBranch ≠ Atom.symbol "Error")
    (h_else_nerr : elseBranch ≠ Atom.symbol "Error")
    (h_check : checkIfFunctionTypeIsApplicable
      (unifyExpr target pattern thenBranch elseBranch)
      unifyFunctionType Atom.undefinedType
      space seed fuelShell = .inr succs)
    (h_check_b : seed ∈ succs)
    (hmatch : matchAtoms target pattern fuel = []) :
    EvalAtom space d
      (unifyExpr target pattern thenBranch elseBranch)
      Atom.undefinedType seed
      (elseBranch, seed) := by
  have h_interp : InterpretFunction space d
      (unifyExpr target pattern thenBranch elseBranch)
      unifyFunctionType Atom.undefinedType seed
      (unifyExpr target pattern thenBranch elseBranch, seed) :=
    interpretFunction_unify_self_seeded h_types
      h_target_nerr h_pattern_nerr h_then_nerr h_else_nerr
  have h_call : MettaCall space d
      (unifyExpr target pattern thenBranch elseBranch)
      Atom.undefinedType seed
      (elseBranch, seed) := by
    have h_empty : unifySuccessResults target pattern thenBranch seed fuel = [] := by
      simp [unifySuccessResults, hmatch]
    exact MettaCall.unify_no_match_raw
      (unifyExpr target pattern thenBranch elseBranch)
      Atom.undefinedType seed
      target pattern thenBranch elseBranch fuel
      rfl (by simp [unifyExpr, isErrorAtom]) h_empty
  have h_op_type : unifyFunctionType ∈ getAtomTypes space (.symbol "unify") := by
    rw [h_types]
    simp
  exact evalAtom_absorbs_unify_shell_of_interp
    h_op_type h_check h_check_b h_interp h_call

/-- Typed specialisation for `let`'s raw `unify` rhs under the exact stdlib
`unify` annotation.  This removes the abstract evaluator boundary from the
active `let` certification path while keeping the head/argument shell explicit. -/
theorem evalAtom_realizes_let_subst_ground_seeded_typed
    {space : Space} {d : GroundedDispatch}
    {seed mb merged : Bindings}
    {pt value body : Atom} {fuel : Nat}
    {succs : List Bindings} {fuelShell : Nat}
    (h_types : getAtomTypes space (.symbol "unify") = [unifyFunctionType])
    (h_value_nerr : value ≠ Atom.symbol "Error")
    (h_pt_nerr : pt ≠ Atom.symbol "Error")
    (h_body_nerr : body ≠ Atom.symbol "Error")
    (_hground : GroundAtom value)
    (h_check : checkIfFunctionTypeIsApplicable
      (unifyExpr value pt body Atom.empty)
      unifyFunctionType Atom.undefinedType
      space seed fuelShell = .inr succs)
    (h_check_b : seed ∈ succs)
    (hmatch : mb ∈ matchAtoms value pt fuel)
    (hmerge : merged ∈ mergeBindings mb seed fuel)
    (h_no_loop : merged.hasLoop = false) :
    EvalAtom space d
      (.expression [.symbol "unify", value, pt, body, Atom.empty])
      Atom.undefinedType seed
      (merged.applyDefault body, merged) := by
  have h_empty_nerr : Atom.empty ≠ Atom.symbol "Error" := by
    native_decide
  simpa [unifyExpr] using
    evalAtom_realizes_unify_match_ground_seeded_typed
      (space := space) (d := d) (seed := seed) (mb := mb) (merged := merged)
      (target := value) (pattern := pt) (thenBranch := body) (elseBranch := Atom.empty)
      (fuel := fuel) (succs := succs) (fuelShell := fuelShell)
      h_types h_value_nerr h_pt_nerr h_body_nerr h_empty_nerr
      h_check h_check_b hmatch hmerge h_no_loop

/-- The three `let` arguments officially interpret to themselves on the
fragment needed by the sugar proof: pattern/body are merely required not to be
the bare `Error` symbol, while the value uses the proven quiescent
self-evaluation theorem. -/
private theorem interpretArgs_let_self
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {pt value body : Atom}
    (h_value_nerr : value ≠ Atom.symbol "Error")
    (h_body_nerr : body ≠ Atom.symbol "Error")
    (h_value_q : SelfEvalQuiescent space d fuel value) :
    InterpretArgs space d [pt, value, body]
      [Atom.atomType, Atom.undefinedType, Atom.atomType]
      Bindings.empty
      (.expression [pt, value, body], Bindings.empty) := by
  have h_pt : EvalAtom space d pt Atom.atomType Bindings.empty
      (pt, Bindings.empty) :=
    evalAtom_atom_type pt Bindings.empty
  have h_value : EvalAtom space d value Atom.undefinedType Bindings.empty
      (value, Bindings.empty) :=
    selfEval_of_quiescent value h_value_q Bindings.empty
  have h_body : EvalAtom space d body Atom.atomType Bindings.empty
      (body, Bindings.empty) :=
    evalAtom_atom_type body Bindings.empty
  have h_tail_body : InterpretArgs space d [body] [Atom.atomType]
      Bindings.empty (.expression [body], Bindings.empty) := by
    exact InterpretArgs.cons_ok body [] Atom.atomType [] Bindings.empty
      (body, Bindings.empty) (Atom.unit, Bindings.empty)
      h_body (Or.inr rfl) InterpretArgs.nil rfl
  have h_tail_value : InterpretArgs space d [value, body]
      [Atom.undefinedType, Atom.atomType] Bindings.empty
      (.expression [value, body], Bindings.empty) := by
    refine InterpretArgs.cons_ok value [body] Atom.undefinedType
      [Atom.atomType] Bindings.empty
      (value, Bindings.empty) (.expression [body], Bindings.empty)
      h_value (Or.inr rfl) h_tail_body ?_
    exact isEmptyOrError_expr_false [] h_body_nerr
  refine InterpretArgs.cons_ok pt [value, body] Atom.atomType
    [Atom.undefinedType, Atom.atomType] Bindings.empty
    (pt, Bindings.empty) (.expression [value, body], Bindings.empty)
    h_pt (Or.inr rfl) h_tail_value ?_
  exact isEmptyOrError_expr_false [body] h_value_nerr

/-- Seeded companion to `interpretArgs_let_self`: the three `let` arguments
interpret to themselves under an arbitrary incoming bindings thread when the
value is in the quiescent self-evaluation fragment. -/
private theorem interpretArgs_let_self_seeded
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {pt value body : Atom} {seed : Bindings}
    (h_value_nerr : value ≠ Atom.symbol "Error")
    (h_body_nerr : body ≠ Atom.symbol "Error")
    (h_value_q : SelfEvalQuiescent space d fuel value) :
    InterpretArgs space d [pt, value, body]
      [Atom.atomType, Atom.undefinedType, Atom.atomType]
      seed
      (.expression [pt, value, body], seed) := by
  have h_pt : EvalAtom space d pt Atom.atomType seed (pt, seed) :=
    evalAtom_atom_type pt seed
  have h_value : EvalAtom space d value Atom.undefinedType seed
      (value, seed) :=
    selfEval_of_quiescent value h_value_q seed
  have h_body : EvalAtom space d body Atom.atomType seed
      (body, seed) :=
    evalAtom_atom_type body seed
  have h_tail_body : InterpretArgs space d [body] [Atom.atomType]
      seed (.expression [body], seed) := by
    exact InterpretArgs.cons_ok body [] Atom.atomType [] seed
      (body, seed) (Atom.unit, seed)
      h_body (Or.inr rfl) InterpretArgs.nil rfl
  have h_tail_value : InterpretArgs space d [value, body]
      [Atom.undefinedType, Atom.atomType] seed
      (.expression [value, body], seed) := by
    refine InterpretArgs.cons_ok value [body] Atom.undefinedType
      [Atom.atomType] seed
      (value, seed) (.expression [body], seed)
      h_value (Or.inr rfl) h_tail_body ?_
    exact isEmptyOrError_expr_false [] h_body_nerr
  refine InterpretArgs.cons_ok pt [value, body] Atom.atomType
    [Atom.undefinedType, Atom.atomType] seed
    (pt, seed) (.expression [value, body], seed)
    h_pt (Or.inr rfl) h_tail_value ?_
  exact isEmptyOrError_expr_false [body] h_value_nerr

/-- The official typed function-path shell for the verbatim upstream `let`
surface form on the certified fragment.  This is the outer function wrapper
that the later `HES_Let` theorem will spend before taking the equation-match
step into the `unify` rhs. -/
theorem interpretFunction_let_self
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {pt value body : Atom}
    (h_types : getAtomTypes space (.symbol "let") = [letFunctionType])
    (h_pt_nerr : pt ≠ Atom.symbol "Error")
    (h_value_nerr : value ≠ Atom.symbol "Error")
    (h_body_nerr : body ≠ Atom.symbol "Error")
    (h_value_q : SelfEvalQuiescent space d fuel value) :
    InterpretFunction space d (letExpr pt value body)
      letFunctionType Atom.undefinedType Bindings.empty
      (letExpr pt value body, Bindings.empty) := by
  have h_head : EvalAtom space d (.symbol "let") letFunctionType Bindings.empty
      (.symbol "let", Bindings.empty) :=
    evalAtom_let_head_typed h_types
  have h_tail : InterpretArgs space d [pt, value, body]
      [Atom.atomType, Atom.undefinedType, Atom.atomType]
      Bindings.empty
      (.expression [pt, value, body], Bindings.empty) :=
    interpretArgs_let_self h_value_nerr h_body_nerr h_value_q
  refine InterpretFunction.head_ok_tail_ok
    (letExpr pt value body) letFunctionType Atom.undefinedType Bindings.empty
    (.symbol "let") [pt, value, body]
    [Atom.atomType, Atom.undefinedType, Atom.atomType]
    (.symbol "let", Bindings.empty)
    (.expression [pt, value, body], Bindings.empty)
    rfl rfl h_head rfl h_tail ?_
  exact isEmptyOrError_expr_false (value :: [body]) h_pt_nerr

/-- Seeded typed function-path shell for the verbatim upstream `let` surface
form.  This is the incoming-bindings companion to `interpretFunction_let_self`
that the source-progress side of `HES_Let` will need after the value
evaluation has already produced a non-empty bindings thread. -/
theorem interpretFunction_let_self_seeded
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {pt value body : Atom} {seed : Bindings}
    (h_types : getAtomTypes space (.symbol "let") = [letFunctionType])
    (h_pt_nerr : pt ≠ Atom.symbol "Error")
    (h_value_nerr : value ≠ Atom.symbol "Error")
    (h_body_nerr : body ≠ Atom.symbol "Error")
    (h_value_q : SelfEvalQuiescent space d fuel value) :
    InterpretFunction space d (letExpr pt value body)
      letFunctionType Atom.undefinedType seed
      (letExpr pt value body, seed) := by
  have h_head : EvalAtom space d (.symbol "let") letFunctionType seed
      (.symbol "let", seed) :=
    evalAtom_let_head_typed_seeded h_types
  have h_tail : InterpretArgs space d [pt, value, body]
      [Atom.atomType, Atom.undefinedType, Atom.atomType]
      seed
      (.expression [pt, value, body], seed) :=
    interpretArgs_let_self_seeded h_value_nerr h_body_nerr h_value_q
  refine InterpretFunction.head_ok_tail_ok
    (letExpr pt value body) letFunctionType Atom.undefinedType seed
    (.symbol "let") [pt, value, body]
    [Atom.atomType, Atom.undefinedType, Atom.atomType]
    (.symbol "let", seed)
    (.expression [pt, value, body], seed)
    rfl rfl h_head rfl h_tail ?_
  exact isEmptyOrError_expr_false (value :: [body]) h_pt_nerr

/-- Source-progress companion to the quiescent `let` shell: if the bound
value has already been officially evaluated to a non-empty/non-error atom,
then the `let` function path rebuilds around that evaluated value and threads
its bindings forward into the body position. -/
private theorem interpretFunction_let_of_value_eval_ok
    {space : Space} {d : GroundedDispatch}
    {pt value body : Atom} {valueResult : ResultPair}
    (h_types : getAtomTypes space (.symbol "let") = [letFunctionType])
    (h_pt_nerr : pt ≠ Atom.symbol "Error")
    (h_value_nerr : valueResult.1 ≠ Atom.symbol "Error")
    (h_body_nerr : body ≠ Atom.symbol "Error")
    (h_value : EvalAtom space d value Atom.undefinedType Bindings.empty valueResult)
    (h_value_ok : isEmptyOrError valueResult.1 = false) :
    InterpretFunction space d (letExpr pt value body)
      letFunctionType Atom.undefinedType Bindings.empty
      (letExpr pt valueResult.1 body, valueResult.2) := by
  have h_head : EvalAtom space d (.symbol "let") letFunctionType Bindings.empty
      (.symbol "let", Bindings.empty) :=
    evalAtom_let_head_typed h_types
  have h_pt : EvalAtom space d pt Atom.atomType Bindings.empty
      (pt, Bindings.empty) :=
    evalAtom_atom_type pt Bindings.empty
  have h_body : EvalAtom space d body Atom.atomType valueResult.2
      (body, valueResult.2) :=
    evalAtom_atom_type body valueResult.2
  have h_tail_body : InterpretArgs space d [body] [Atom.atomType]
      valueResult.2 (.expression [body], valueResult.2) := by
    exact InterpretArgs.cons_ok body [] Atom.atomType [] valueResult.2
      (body, valueResult.2) (Atom.unit, valueResult.2)
      h_body (Or.inr rfl) InterpretArgs.nil rfl
  have h_tail_value : InterpretArgs space d [value, body]
      [Atom.undefinedType, Atom.atomType] Bindings.empty
      (.expression [valueResult.1, body], valueResult.2) := by
    refine InterpretArgs.cons_ok value [body] Atom.undefinedType
      [Atom.atomType] Bindings.empty
      valueResult (.expression [body], valueResult.2)
      h_value (Or.inl h_value_ok) h_tail_body ?_
    exact isEmptyOrError_expr_false [] h_body_nerr
  refine InterpretFunction.head_ok_tail_ok
    (letExpr pt value body) letFunctionType Atom.undefinedType Bindings.empty
    (.symbol "let") [pt, value, body]
    [Atom.atomType, Atom.undefinedType, Atom.atomType]
    (.symbol "let", Bindings.empty)
    (.expression [pt, valueResult.1, body], valueResult.2)
    rfl rfl h_head rfl ?_ ?_
  · refine InterpretArgs.cons_ok pt [value, body] Atom.atomType
      [Atom.undefinedType, Atom.atomType] Bindings.empty
      (pt, Bindings.empty) (.expression [valueResult.1, body], valueResult.2)
      h_pt (Or.inr rfl) h_tail_value ?_
    exact isEmptyOrError_expr_false [body] h_value_nerr
  · exact isEmptyOrError_expr_false (valueResult.1 :: [body]) h_pt_nerr

/-- Error/Empty propagation companion to the quiescent `let` shell: if the
bound value already officially evaluates to a changed Empty/Error result, the
`let` function path propagates that result immediately without touching the
body. -/
private theorem interpretFunction_let_of_value_eval_bad
    {space : Space} {d : GroundedDispatch}
    {pt value body : Atom} {valueResult : ResultPair}
    (h_types : getAtomTypes space (.symbol "let") = [letFunctionType])
    (h_value : EvalAtom space d value Atom.undefinedType Bindings.empty valueResult)
    (h_value_bad : isEmptyOrError valueResult.1 = true)
    (h_changed : valueResult.1 ≠ value) :
    InterpretFunction space d (letExpr pt value body)
      letFunctionType Atom.undefinedType Bindings.empty
      valueResult := by
  have h_head : EvalAtom space d (.symbol "let") letFunctionType Bindings.empty
      (.symbol "let", Bindings.empty) :=
    evalAtom_let_head_typed h_types
  have h_pt : EvalAtom space d pt Atom.atomType Bindings.empty
      (pt, Bindings.empty) :=
    evalAtom_atom_type pt Bindings.empty
  have h_tail_value : InterpretArgs space d [value, body]
      [Atom.undefinedType, Atom.atomType] Bindings.empty valueResult := by
    exact InterpretArgs.head_changed_error value [body]
      Atom.undefinedType [Atom.atomType] Bindings.empty valueResult
      h_value h_value_bad h_changed
  refine InterpretFunction.head_ok_tail_error
    (letExpr pt value body) letFunctionType Atom.undefinedType Bindings.empty
    (.symbol "let") [pt, value, body]
    [Atom.atomType, Atom.undefinedType, Atom.atomType]
    (.symbol "let", Bindings.empty) valueResult
    rfl rfl h_head rfl ?_ h_value_bad
  exact InterpretArgs.cons_tail_error pt [value, body]
    Atom.atomType [Atom.undefinedType, Atom.atomType]
    Bindings.empty
    (pt, Bindings.empty) valueResult
    h_pt (Or.inr rfl) h_tail_value h_value_bad

/-- Generic equation-call wrapper for the verbatim upstream `let` surface
form.  Once the typed function-path shell is in place, any official evaluation
of the matched rhs composes into an official `MettaCall` of the original
surface `let`. -/
theorem mettaCall_absorbs_let_equation
    {space : Space} {d : GroundedDispatch}
    {pt value body rhs : Atom} {qb merged : Bindings}
    {final : ResultPair} {fuel : Nat}
    (h_not_exec : d.isExecutable (.symbol "let") = false)
    (h_query : (rhs, qb) ∈ queryEquations space (letExpr pt value body) fuel)
    (h_merge : merged ∈ mergeBindings qb Bindings.empty fuel)
    (h_no_loop : merged.hasLoop = false)
    (h_eval : EvalAtom space d (merged.apply rhs fuel)
      Atom.undefinedType merged final) :
    MettaCall space d (letExpr pt value body) Atom.undefinedType
      Bindings.empty final :=
  MettaCall.equation_match _ _ _ rhs qb merged final fuel
    (by simp [letExpr, isErrorAtom])
    (by
      refine ⟨?_, ?_⟩
      · simpa [letExpr] using h_not_exec
      · simp)
    h_query h_merge h_no_loop h_eval

/-- Seeded equation-call wrapper for the verbatim upstream `let` surface
form.  Once the typed function-path shell has already threaded some incoming
bindings through the value evaluation, the same equation-match packaging
still applies at that seed. -/
theorem mettaCall_absorbs_let_equation_seeded
    {space : Space} {d : GroundedDispatch}
    {pt value body rhs : Atom} {seed qb merged : Bindings}
    {final : ResultPair} {fuel : Nat}
    (h_not_exec : d.isExecutable (.symbol "let") = false)
    (h_query : (rhs, qb) ∈ queryEquations space (letExpr pt value body) fuel)
    (h_merge : merged ∈ mergeBindings qb seed fuel)
    (h_no_loop : merged.hasLoop = false)
    (h_eval : EvalAtom space d (merged.apply rhs fuel)
      Atom.undefinedType merged final) :
    MettaCall space d (letExpr pt value body) Atom.undefinedType
      seed final :=
  MettaCall.equation_match _ _ _ rhs qb merged final fuel
    (by simp [letExpr, isErrorAtom])
    (by
      refine ⟨?_, ?_⟩
      · simpa [letExpr] using h_not_exec
      · simp)
    h_query h_merge h_no_loop h_eval

/-- Generic outer official `let` shell, parameterized by the actual
`InterpretFunction` result.  This is the right theorem boundary for the
source-progress half: once the `let` function path has been derived honestly,
the remaining official `EvalAtom` judgment is just the usual function-path +
`MettaCall` composition. -/
theorem evalAtom_absorbs_let_shell_of_interp
    {space : Space} {d : GroundedDispatch}
    {pt value body : Atom} {seed : Bindings}
    {interpResult final : ResultPair}
    {succs : List Bindings} {fuel : Nat}
    (h_op_type : letFunctionType ∈ getAtomTypes space (.symbol "let"))
    (h_check : checkIfFunctionTypeIsApplicable
      (letExpr pt value body) letFunctionType Atom.undefinedType
      space seed fuel = .inr succs)
    (h_check_b : seed ∈ succs)
    (h_interp : InterpretFunction space d (letExpr pt value body)
      letFunctionType Atom.undefinedType seed interpResult)
    (h_call : MettaCall space d interpResult.1
      Atom.undefinedType interpResult.2 final) :
    EvalAtom space d (letExpr pt value body)
      Atom.undefinedType seed final := by
  by_cases h_final_err : isErrorAtom final.1 = true
  · refine EvalAtom.interpret_error _ _ _ _ ?_ ?_ rfl ?_ ?_ h_final_err
    · exact isEmptyOrError_expr_false [pt, value, body] (by simp)
    · simp [letExpr, getMetaType, Atom.undefinedType, Atom.atomType,
        Atom.expressionType, Atom.variableType]
    · intro h_unit
      simp [letExpr, Atom.unit] at h_unit
    · refine InterpretExpression.function_path _ _ _
        (.symbol "let") [pt, value, body]
        letFunctionType Atom.undefinedType seed
        interpResult final fuel
        rfl h_op_type ?_ succs h_check h_check_b rfl h_interp h_call
      rfl
  · refine EvalAtom.interpret_success _ _ _ _ ?_ ?_ rfl ?_ ?_ ?_
    · exact isEmptyOrError_expr_false [pt, value, body] (by simp)
    · simp [letExpr, getMetaType, Atom.undefinedType, Atom.atomType,
        Atom.expressionType, Atom.variableType]
    · intro h_unit
      simp [letExpr, Atom.unit] at h_unit
    · refine InterpretExpression.function_path _ _ _
        (.symbol "let") [pt, value, body]
        letFunctionType Atom.undefinedType seed
        interpResult final fuel
        rfl h_op_type ?_ succs h_check h_check_b rfl h_interp h_call
      rfl
    · simpa using h_final_err

/-- The outer official `let` shell, relative to the explicit typed-function
path and equation-match hypotheses.  This theorem packages the exact remaining
boundary around the already-proven `unify` core: once the surface `let`
function path and its equation-call are supplied, the full official
`EvalAtom` judgment follows. -/
theorem evalAtom_absorbs_let_shell
    {space : Space} {d : GroundedDispatch}
    {pt value body : Atom} {final : ResultPair}
    {succs : List Bindings} {fuel : Nat}
    (h_op_type : letFunctionType ∈ getAtomTypes space (.symbol "let"))
    (h_check : checkIfFunctionTypeIsApplicable
      (letExpr pt value body) letFunctionType Atom.undefinedType
      space Bindings.empty fuel = .inr succs)
    (h_check_b : Bindings.empty ∈ succs)
    (h_interp : InterpretFunction space d (letExpr pt value body)
      letFunctionType Atom.undefinedType Bindings.empty
      (letExpr pt value body, Bindings.empty))
    (h_call : MettaCall space d (letExpr pt value body)
      Atom.undefinedType Bindings.empty final)
    (h_final_ok : isErrorAtom final.1 = false) :
    EvalAtom space d (letExpr pt value body)
      Atom.undefinedType Bindings.empty final := by
  refine EvalAtom.interpret_success _ _ _ _ ?_ ?_ rfl ?_ ?_ h_final_ok
  · exact isEmptyOrError_expr_false [pt, value, body] (by simp)
  · simp [letExpr, getMetaType, Atom.undefinedType, Atom.atomType,
      Atom.expressionType, Atom.variableType]
  · intro h_unit
    simp [letExpr, Atom.unit] at h_unit
  · refine InterpretExpression.function_path _ _ _
      (.symbol "let") [pt, value, body]
      letFunctionType Atom.undefinedType Bindings.empty
      (letExpr pt value body, Bindings.empty) final fuel
      rfl h_op_type ?_ succs h_check h_check_b rfl h_interp h_call
    rfl

/-- Error-side companion to `evalAtom_absorbs_let_shell`: when the outer
typed-function path and equation-call are supplied and the final result is
error-shaped, the full official `EvalAtom` judgment follows on the error
branch rather than the success branch. -/
theorem evalAtom_absorbs_let_shell_error
    {space : Space} {d : GroundedDispatch}
    {pt value body : Atom} {final : ResultPair}
    {succs : List Bindings} {fuel : Nat}
    (h_op_type : letFunctionType ∈ getAtomTypes space (.symbol "let"))
    (h_check : checkIfFunctionTypeIsApplicable
      (letExpr pt value body) letFunctionType Atom.undefinedType
      space Bindings.empty fuel = .inr succs)
    (h_check_b : Bindings.empty ∈ succs)
    (h_interp : InterpretFunction space d (letExpr pt value body)
      letFunctionType Atom.undefinedType Bindings.empty
      (letExpr pt value body, Bindings.empty))
    (h_call : MettaCall space d (letExpr pt value body)
      Atom.undefinedType Bindings.empty final)
    (h_final_err : isErrorAtom final.1 = true) :
    EvalAtom space d (letExpr pt value body)
      Atom.undefinedType Bindings.empty final := by
  refine EvalAtom.interpret_error _ _ _ _ ?_ ?_ rfl ?_ ?_ h_final_err
  · exact isEmptyOrError_expr_false [pt, value, body] (by simp)
  · simp [letExpr, getMetaType, Atom.undefinedType, Atom.atomType,
      Atom.expressionType, Atom.variableType]
  · intro h_unit
    simp [letExpr, Atom.unit] at h_unit
  · refine InterpretExpression.function_path _ _ _
      (.symbol "let") [pt, value, body]
      letFunctionType Atom.undefinedType Bindings.empty
      (letExpr pt value body, Bindings.empty) final fuel
      rfl h_op_type ?_ succs h_check h_check_b rfl h_interp h_call
    rfl

/-- Source-progress shell for `let` on the non-empty/non-error value-result
fragment.  Once the bound value has an official evaluation result and the
continuation `let` surface at that result is officially callable, the whole
original `let` expression officially evaluates to the same final result. -/
theorem evalAtom_absorbs_let_value_eval_ok
    {space : Space} {d : GroundedDispatch}
    {pt value body valueAtom : Atom} {valueBindings : Bindings}
    {final : ResultPair}
    {succs : List Bindings} {fuel : Nat}
    (h_types : getAtomTypes space (.symbol "let") = [letFunctionType])
    (h_check : checkIfFunctionTypeIsApplicable
      (letExpr pt value body) letFunctionType Atom.undefinedType
      space Bindings.empty fuel = .inr succs)
    (h_check_b : Bindings.empty ∈ succs)
    (h_pt_nerr : pt ≠ Atom.symbol "Error")
    (h_value_nerr : valueAtom ≠ Atom.symbol "Error")
    (h_body_nerr : body ≠ Atom.symbol "Error")
    (h_value : EvalAtom space d value Atom.undefinedType Bindings.empty
      (valueAtom, valueBindings))
    (h_value_ok : isEmptyOrError valueAtom = false)
    (h_call : MettaCall space d (letExpr pt valueAtom body)
      Atom.undefinedType valueBindings final) :
    EvalAtom space d (letExpr pt value body)
      Atom.undefinedType Bindings.empty final := by
  have h_interp :
      InterpretFunction space d (letExpr pt value body)
        letFunctionType Atom.undefinedType Bindings.empty
        (letExpr pt valueAtom body, valueBindings) :=
    interpretFunction_let_of_value_eval_ok
      h_types h_pt_nerr h_value_nerr h_body_nerr h_value h_value_ok
  have h_op_type : letFunctionType ∈ getAtomTypes space (.symbol "let") := by
    rw [h_types]
    simp
  exact evalAtom_absorbs_let_shell_of_interp
    h_op_type h_check h_check_b h_interp h_call

/-- Source-progress shell for `let` on the changed Empty/Error value-result
fragment.  If evaluating the bound value already produces a changed
Empty/Error result, the `let` propagates that result without touching the
body. -/
theorem evalAtom_absorbs_let_value_eval_bad
    {space : Space} {d : GroundedDispatch}
    {pt value body valueAtom : Atom} {valueBindings : Bindings}
    {final : ResultPair}
    {succs : List Bindings} {fuel : Nat}
    (h_types : getAtomTypes space (.symbol "let") = [letFunctionType])
    (h_check : checkIfFunctionTypeIsApplicable
      (letExpr pt value body) letFunctionType Atom.undefinedType
      space Bindings.empty fuel = .inr succs)
    (h_check_b : Bindings.empty ∈ succs)
    (h_value : EvalAtom space d value Atom.undefinedType Bindings.empty
      (valueAtom, valueBindings))
    (h_value_bad : isEmptyOrError valueAtom = true)
    (h_changed : valueAtom ≠ value)
    (h_call : MettaCall space d valueAtom
      Atom.undefinedType valueBindings final) :
    EvalAtom space d (letExpr pt value body)
      Atom.undefinedType Bindings.empty final := by
  have h_interp :
      InterpretFunction space d (letExpr pt value body)
        letFunctionType Atom.undefinedType Bindings.empty
        (valueAtom, valueBindings) :=
    interpretFunction_let_of_value_eval_bad
      h_types h_value h_value_bad h_changed
  have h_op_type : letFunctionType ∈ getAtomTypes space (.symbol "let") := by
    rw [h_types]
    simp
  exact evalAtom_absorbs_let_shell_of_interp
    h_op_type h_check h_check_b h_interp h_call

/-- Source-progress half of `HES_Let`, non-error fragment: if the bound value
takes a certified fragment step, any official evaluation of the successor
value can be lifted back to an official evaluation of the original `let`
provided the continuation `let` surface at the evaluated value is officially
callable. -/
theorem evalAtom_absorbs_let_source_frag_ok
    {space : Space} {d : GroundedDispatch}
    {fuel fuelShell : Nat}
    {pt value value' body : Atom} {valueResult final : ResultPair}
    {succs : List Bindings}
    (h_empty_no_eqs : ∀ f, queryEquations space Atom.empty f = [])
    (h_frag : FragStep space d fuel value value')
    (h_types : getAtomTypes space (.symbol "let") = [letFunctionType])
    (h_check : checkIfFunctionTypeIsApplicable
      (letExpr pt value body) letFunctionType Atom.undefinedType
      space Bindings.empty fuelShell = .inr succs)
    (h_check_b : Bindings.empty ∈ succs)
    (h_pt_nerr : pt ≠ Atom.symbol "Error")
    (h_value_nerr : valueResult.1 ≠ Atom.symbol "Error")
    (h_body_nerr : body ≠ Atom.symbol "Error")
    (h_eval' : EvalAtom space d value' Atom.undefinedType Bindings.empty valueResult)
    (h_value_ok : isEmptyOrError valueResult.1 = false)
    (h_call : ∀ {rb},
      EvalAtom space d value Atom.undefinedType Bindings.empty (valueResult.1, rb) →
      MettaCall space d (letExpr pt valueResult.1 body)
        Atom.undefinedType rb final) :
    ∃ rb,
      EvalAtom space d (letExpr pt value body)
        Atom.undefinedType Bindings.empty (final.1, rb) := by
  obtain ⟨rb, h_value⟩ := evalAtom_absorbs_fragStep h_empty_no_eqs h_frag h_eval'
  refine ⟨final.2, ?_⟩
  exact evalAtom_absorbs_let_value_eval_ok
    h_types h_check h_check_b h_pt_nerr h_value_nerr h_body_nerr
    h_value h_value_ok (h_call h_value)

/-- Source-progress half of `HES_Let`, changed Empty/Error fragment: if the
bound value takes a certified fragment step and the lifted official
evaluation already yields a changed Empty/Error result, the original `let`
propagates that result immediately. -/
theorem evalAtom_absorbs_let_source_frag_bad
    {space : Space} {d : GroundedDispatch}
    {fuel fuelShell : Nat}
    {pt value value' body : Atom} {valueResult final : ResultPair}
    {succs : List Bindings}
    (h_empty_no_eqs : ∀ f, queryEquations space Atom.empty f = [])
    (h_frag : FragStep space d fuel value value')
    (h_types : getAtomTypes space (.symbol "let") = [letFunctionType])
    (h_check : checkIfFunctionTypeIsApplicable
      (letExpr pt value body) letFunctionType Atom.undefinedType
      space Bindings.empty fuelShell = .inr succs)
    (h_check_b : Bindings.empty ∈ succs)
    (h_eval' : EvalAtom space d value' Atom.undefinedType Bindings.empty valueResult)
    (h_value_bad : isEmptyOrError valueResult.1 = true)
    (h_changed : valueResult.1 ≠ value)
    (h_call : ∀ {rb},
      EvalAtom space d value Atom.undefinedType Bindings.empty (valueResult.1, rb) →
      MettaCall space d valueResult.1 Atom.undefinedType rb final) :
    ∃ rb,
      EvalAtom space d (letExpr pt value body)
        Atom.undefinedType Bindings.empty (final.1, rb) := by
  obtain ⟨rb, h_value⟩ := evalAtom_absorbs_fragStep h_empty_no_eqs h_frag h_eval'
  refine ⟨final.2, ?_⟩
  exact evalAtom_absorbs_let_value_eval_bad
    h_types h_check h_check_b h_value h_value_bad h_changed (h_call h_value)

/-- Step-shaped source-progress certification theorem for `HES_Let` on the
non-error fragment.

This ties `evalAtom_absorbs_let_source_frag_ok` back to the coarse
`HESmallStep.let_source` rule, without pretending the continuation call on the
evaluated value has already been discharged automatically. -/
theorem evalAtom_absorbs_let_source_frag_rule_ok
    {space : Space} {d : GroundedDispatch}
    {fuelStep fuelShell : Nat}
    {pt value value' body valueAtom : Atom}
    {valueBindings : Bindings} {final : ResultPair}
    {succs : List Bindings}
    (_h_step : HESmallStep space d fuelStep
      (letExpr pt value body) (letExpr pt value' body))
    (h_empty_no_eqs : ∀ f, queryEquations space Atom.empty f = [])
    (h_frag : FragStep space d fuelStep value value')
    (h_types : getAtomTypes space (.symbol "let") = [letFunctionType])
    (h_check : checkIfFunctionTypeIsApplicable
      (letExpr pt value body) letFunctionType Atom.undefinedType
      space Bindings.empty fuelShell = .inr succs)
    (h_check_b : Bindings.empty ∈ succs)
    (h_pt_nerr : pt ≠ Atom.symbol "Error")
    (h_value_nerr : valueAtom ≠ Atom.symbol "Error")
    (h_body_nerr : body ≠ Atom.symbol "Error")
    (h_eval' : EvalAtom space d value' Atom.undefinedType Bindings.empty
      (valueAtom, valueBindings))
    (h_value_ok : isEmptyOrError valueAtom = false)
    (h_call : ∀ {rb},
      EvalAtom space d value Atom.undefinedType Bindings.empty (valueAtom, rb) →
      MettaCall space d (letExpr pt valueAtom body)
        Atom.undefinedType rb final) :
    ∃ rb,
      EvalAtom space d (letExpr pt value body)
        Atom.undefinedType Bindings.empty (final.1, rb) := by
  exact evalAtom_absorbs_let_source_frag_ok
    h_empty_no_eqs h_frag h_types h_check h_check_b
    h_pt_nerr h_value_nerr h_body_nerr h_eval' h_value_ok h_call

/-- Step-shaped source-progress certification theorem for `HES_Let` on the
changed Empty/Error fragment.

This ties `evalAtom_absorbs_let_source_frag_bad` back to the coarse
`HESmallStep.let_source` rule.  If the lifted value evaluation already
produces a changed Empty/Error result, the original surface `let` propagates
that result immediately. -/
theorem evalAtom_absorbs_let_source_frag_rule_bad
    {space : Space} {d : GroundedDispatch}
    {fuelStep fuelShell : Nat}
    {pt value value' body valueAtom : Atom}
    {valueBindings : Bindings} {final : ResultPair}
    {succs : List Bindings}
    (_h_step : HESmallStep space d fuelStep
      (letExpr pt value body) (letExpr pt value' body))
    (h_empty_no_eqs : ∀ f, queryEquations space Atom.empty f = [])
    (h_frag : FragStep space d fuelStep value value')
    (h_types : getAtomTypes space (.symbol "let") = [letFunctionType])
    (h_check : checkIfFunctionTypeIsApplicable
      (letExpr pt value body) letFunctionType Atom.undefinedType
      space Bindings.empty fuelShell = .inr succs)
    (h_check_b : Bindings.empty ∈ succs)
    (h_eval' : EvalAtom space d value' Atom.undefinedType Bindings.empty
      (valueAtom, valueBindings))
    (h_value_bad : isEmptyOrError valueAtom = true)
    (h_changed : valueAtom ≠ value)
    (h_call : ∀ {rb},
      EvalAtom space d value Atom.undefinedType Bindings.empty (valueAtom, rb) →
      MettaCall space d valueAtom Atom.undefinedType rb final) :
    ∃ rb,
      EvalAtom space d (letExpr pt value body)
        Atom.undefinedType Bindings.empty (final.1, rb) := by
  exact evalAtom_absorbs_let_source_frag_bad
    h_empty_no_eqs h_frag h_types h_check h_check_b
    h_eval' h_value_bad h_changed h_call

/-- Full ground-success `let` wrapper through the verbatim stdlib helper
route, with the query-side freshness assumptions made explicit.

This theorem spends:
- the typed/equational outer `let` shell,
- the seeded `unify` realization boundary, and
- the body-side non-interference lemma for query-local fresh variables.

It is the honest substitution-half certification theorem for surface `let`
on the stated fragment: the outer query bindings may be non-empty, but they
must not affect the user body's actual variables. -/
theorem evalAtom_absorbs_let_subst_ground_shell
    {space : Space} {d : GroundedDispatch}
    {pt value body rhs : Atom}
    {qb mb merged : Bindings}
    {succs succsUnify : List Bindings}
    {fuelShell fuelQuery fuelUnify fuelUnifyShell : Nat}
    (h_types : getAtomTypes space (.symbol "let") = [letFunctionType])
    (h_unify_types : getAtomTypes space (.symbol "unify") = [unifyFunctionType])
    (h_check : checkIfFunctionTypeIsApplicable
      (letExpr pt value body) letFunctionType Atom.undefinedType
      space Bindings.empty fuelShell = .inr succs)
    (h_check_b : Bindings.empty ∈ succs)
    (h_unify_check : checkIfFunctionTypeIsApplicable
      (unifyExpr value pt body Atom.empty)
      unifyFunctionType Atom.undefinedType
      space qb fuelUnifyShell = .inr succsUnify)
    (h_unify_check_b : qb ∈ succsUnify)
    (h_not_exec : d.isExecutable (.symbol "let") = false)
    (h_pt_nerr : pt ≠ Atom.symbol "Error")
    (h_value_nerr : value ≠ Atom.symbol "Error")
    (h_body_nerr : body ≠ Atom.symbol "Error")
    (h_value_q : SelfEvalQuiescent space d fuelShell value)
    (hground : GroundAtom value)
    (h_query : (rhs, qb) ∈ queryEquations space (letExpr pt value body) fuelQuery)
    (h_query_merge : qb ∈ mergeBindings qb Bindings.empty fuelQuery)
    (h_query_no_loop : qb.hasLoop = false)
    (h_rhs : qb.apply rhs fuelQuery = letUnifyRhs pt value body)
    (hqbEq : qb.equalities = [])
    (hqbKeys : (qb.assignments.map Prod.fst).Nodup)
    (hbody_irrel : ∀ v, v ∈ collectVars body 100 → qb.lookup v = none)
    (hmatch : mb ∈ matchAtoms value pt fuelUnify)
    (hmerge : merged ∈ mergeBindings mb qb fuelUnify)
    (hmerge_det : mergeGround? mb qb = some merged)
    (h_unify_no_loop : merged.hasLoop = false)
    (h_final_ok : isErrorAtom (mb.applyDefault body) = false) :
    EvalAtom space d (letExpr pt value body)
      Atom.undefinedType Bindings.empty
      (mb.applyDefault body, merged) := by
  have h_interp :
      InterpretFunction space d (letExpr pt value body)
        letFunctionType Atom.undefinedType Bindings.empty
        (letExpr pt value body, Bindings.empty) :=
    interpretFunction_let_self h_types h_pt_nerr h_value_nerr h_body_nerr h_value_q
  have hmbGround : GroundBindings mb :=
    (matchAtoms_ground_canon hground hmatch).1
  have h_body_eq : merged.applyDefault body = mb.applyDefault body := by
    exact apply_eq_of_mergeGround_irrel hmbGround hqbEq hqbKeys hmerge_det hbody_irrel
  have h_eval_rhs :
      EvalAtom space d (qb.apply rhs fuelQuery)
        Atom.undefinedType qb
        (mb.applyDefault body, merged) := by
    rw [h_rhs]
    have h_unify :
        EvalAtom space d (letUnifyRhs pt value body)
          Atom.undefinedType qb
          (merged.applyDefault body, merged) :=
      evalAtom_realizes_let_subst_ground_seeded_typed
        h_unify_types h_value_nerr h_pt_nerr h_body_nerr
        hground h_unify_check h_unify_check_b hmatch hmerge h_unify_no_loop
    simpa [letUnifyRhs, h_body_eq] using h_unify
  have h_call :
      MettaCall space d (letExpr pt value body)
        Atom.undefinedType Bindings.empty
        (mb.applyDefault body, merged) :=
    mettaCall_absorbs_let_equation h_not_exec h_query h_query_merge
      h_query_no_loop h_eval_rhs
  have h_op_type : letFunctionType ∈ getAtomTypes space (.symbol "let") := by
    rw [h_types]
    simp
  exact evalAtom_absorbs_let_shell h_op_type h_check h_check_b
    h_interp h_call h_final_ok

/-- Seeded outer official `let` shell, relative to the explicit typed-function
path and equation-match hypotheses.  This is the incoming-bindings companion
to `evalAtom_absorbs_let_shell`, keeping the shell theorem honest when the
value-evaluation side has already produced a non-empty bindings thread. -/
theorem evalAtom_absorbs_let_shell_seeded
    {space : Space} {d : GroundedDispatch}
    {pt value body : Atom} {seed : Bindings} {final : ResultPair}
    {succs : List Bindings} {fuel : Nat}
    (h_op_type : letFunctionType ∈ getAtomTypes space (.symbol "let"))
    (h_check : checkIfFunctionTypeIsApplicable
      (letExpr pt value body) letFunctionType Atom.undefinedType
      space seed fuel = .inr succs)
    (h_check_b : seed ∈ succs)
    (h_interp : InterpretFunction space d (letExpr pt value body)
      letFunctionType Atom.undefinedType seed
      (letExpr pt value body, seed))
    (h_call : MettaCall space d (letExpr pt value body)
      Atom.undefinedType seed final)
    (h_final_ok : isErrorAtom final.1 = false) :
    EvalAtom space d (letExpr pt value body)
      Atom.undefinedType seed final := by
  refine EvalAtom.interpret_success _ _ _ _ ?_ ?_ rfl ?_ ?_ h_final_ok
  · exact isEmptyOrError_expr_false [pt, value, body] (by simp)
  · simp [letExpr, getMetaType, Atom.undefinedType, Atom.atomType,
      Atom.expressionType, Atom.variableType]
  · intro h_unit
    simp [letExpr, Atom.unit] at h_unit
  · refine InterpretExpression.function_path _ _ _
      (.symbol "let") [pt, value, body]
      letFunctionType Atom.undefinedType seed
      (letExpr pt value body, seed) final fuel
      rfl h_op_type ?_ succs h_check h_check_b rfl h_interp h_call
    rfl

/-- Seeded error-side companion to `evalAtom_absorbs_let_shell_seeded`.
This keeps the outer `let` shell honest when the value-evaluation side has
already shifted the bindings thread and the eventual result is error-shaped. -/
theorem evalAtom_absorbs_let_shell_seeded_error
    {space : Space} {d : GroundedDispatch}
    {pt value body : Atom} {seed : Bindings} {final : ResultPair}
    {succs : List Bindings} {fuel : Nat}
    (h_op_type : letFunctionType ∈ getAtomTypes space (.symbol "let"))
    (h_check : checkIfFunctionTypeIsApplicable
      (letExpr pt value body) letFunctionType Atom.undefinedType
      space seed fuel = .inr succs)
    (h_check_b : seed ∈ succs)
    (h_interp : InterpretFunction space d (letExpr pt value body)
      letFunctionType Atom.undefinedType seed
      (letExpr pt value body, seed))
    (h_call : MettaCall space d (letExpr pt value body)
      Atom.undefinedType seed final)
    (h_final_err : isErrorAtom final.1 = true) :
    EvalAtom space d (letExpr pt value body)
      Atom.undefinedType seed final := by
  refine EvalAtom.interpret_error _ _ _ _ ?_ ?_ rfl ?_ ?_ h_final_err
  · exact isEmptyOrError_expr_false [pt, value, body] (by simp)
  · simp [letExpr, getMetaType, Atom.undefinedType, Atom.atomType,
      Atom.expressionType, Atom.variableType]
  · intro h_unit
    simp [letExpr, Atom.unit] at h_unit
  · refine InterpretExpression.function_path _ _ _
      (.symbol "let") [pt, value, body]
      letFunctionType Atom.undefinedType seed
      (letExpr pt value body, seed) final fuel
      rfl h_op_type ?_ succs h_check h_check_b rfl h_interp h_call
    rfl

/-- Step-shaped substitution-side certification theorem for `HES_Let` on the
ground fragment.

This is a thin wrapper over `evalAtom_absorbs_let_subst_ground_shell`: it
ties that shell theorem back to the coarse `HESmallStep.let_subst` rule,
without pretending the source-progress half of `let` is already certified.

Positive example:
- a coarse `let_subst` step with a ground quiescent value and an irrelevant
  query-local binding layer yields the official evaluation of the whole
  surface `let` to the substituted body result.

Negative example:
- if the query-local bindings can affect variables actually occurring in the
  user body, this theorem does not apply; that no-capture boundary remains
  explicit in `hbody_irrel`. -/
theorem evalAtom_absorbs_let_subst_ground_rule
    {space : Space} {d : GroundedDispatch}
    {pt value body rhs : Atom}
    {qb mb merged : Bindings}
    {succs succsUnify : List Bindings}
    {fuelStep fuelShell fuelQuery fuelUnify fuelUnifyShell : Nat}
    (_h_step : HESmallStep space d fuelStep
      (letExpr pt value body) (mb.applyDefault body))
    (h_types : getAtomTypes space (.symbol "let") = [letFunctionType])
    (h_unify_types : getAtomTypes space (.symbol "unify") = [unifyFunctionType])
    (h_check : checkIfFunctionTypeIsApplicable
      (letExpr pt value body) letFunctionType Atom.undefinedType
      space Bindings.empty fuelShell = .inr succs)
    (h_check_b : Bindings.empty ∈ succs)
    (h_unify_check : checkIfFunctionTypeIsApplicable
      (unifyExpr value pt body Atom.empty)
      unifyFunctionType Atom.undefinedType
      space qb fuelUnifyShell = .inr succsUnify)
    (h_unify_check_b : qb ∈ succsUnify)
    (h_not_exec : d.isExecutable (.symbol "let") = false)
    (h_pt_nerr : pt ≠ Atom.symbol "Error")
    (h_value_nerr : value ≠ Atom.symbol "Error")
    (h_body_nerr : body ≠ Atom.symbol "Error")
    (h_value_q : SelfEvalQuiescent space d fuelShell value)
    (hground : GroundAtom value)
    (h_query : (rhs, qb) ∈ queryEquations space (letExpr pt value body) fuelQuery)
    (h_query_merge : qb ∈ mergeBindings qb Bindings.empty fuelQuery)
    (h_query_no_loop : qb.hasLoop = false)
    (h_rhs : qb.apply rhs fuelQuery = letUnifyRhs pt value body)
    (hqbEq : qb.equalities = [])
    (hqbKeys : (qb.assignments.map Prod.fst).Nodup)
    (hbody_irrel : ∀ v, v ∈ collectVars body 100 → qb.lookup v = none)
    (hmatch : mb ∈ matchAtoms value pt fuelUnify)
    (hmerge : merged ∈ mergeBindings mb qb fuelUnify)
    (hmerge_det : mergeGround? mb qb = some merged)
    (h_unify_no_loop : merged.hasLoop = false)
    (h_final_ok : isErrorAtom (mb.applyDefault body) = false) :
    EvalAtom space d (letExpr pt value body)
      Atom.undefinedType Bindings.empty
      (mb.applyDefault body, merged) := by
  simpa [letExpr] using
    (evalAtom_absorbs_let_subst_ground_shell
      (pt := pt) (value := value) (body := body) (rhs := rhs)
      (qb := qb) (mb := mb) (merged := merged)
      (succs := succs) (succsUnify := succsUnify)
      (fuelShell := fuelShell) (fuelQuery := fuelQuery)
      (fuelUnify := fuelUnify) (fuelUnifyShell := fuelUnifyShell)
      h_types h_unify_types h_check h_check_b h_unify_check h_unify_check_b
      h_not_exec h_pt_nerr h_value_nerr h_body_nerr
      h_value_q hground h_query h_query_merge h_query_no_loop h_rhs
      hqbEq hqbKeys hbody_irrel hmatch hmerge hmerge_det
      h_unify_no_loop h_final_ok)

/-! ## F3a: Primitive `switch-minimal` Selector Core

The stdlib helper route for `switch-minimal` is still useful context, but the
coarse rule itself is really about one simpler semantic fact: scanning the raw
branch list left-to-right, skipping malformed branches, and choosing the first
well-formed branch whose pattern matches the raw scrutinee.

We record that selector directly here, in the same one-way matcher language as
`HESmallStep.switch_minimal_match`.  This keeps the eventual primitive-route
certification honest and local: the recursive selector proof should spend these
facts instead of reproving the branch scan from scratch.

The selector itself now lives in `Matching.lean` so the control-side bridge,
runtime contracts, and future primitive evaluator route can all point at the
same shared kernel rather than a private local copy. -/

/-- Positive example: if a particular well-formed branch is the first one
whose pattern matches the raw scrutinee, the coarse selector returns exactly
that branch's substituted template.

Negative example: malformed earlier branches do not block the match; they are
skipped by the selector and therefore need no "earlier failure" witness. -/
theorem selectSwitchTemplateCoarse_of_prefix_match
    {scrut pt template : Atom} {pre post : List Atom}
    {mb : Bindings} {fuel : Nat}
    (h_match : simpleMatch pt scrut Bindings.empty fuel = some mb)
    (h_earlier : ∀ branch ∈ pre, ∀ pt' template',
      branch = Atom.expression [pt', template'] →
      simpleMatch pt' scrut Bindings.empty fuel = none) :
    selectSwitchTemplateCoarse scrut
      (pre ++ Atom.expression [pt, template] :: post) fuel =
      mb.applyDefault template := by
  induction pre with
  | nil =>
      simp [selectSwitchTemplateCoarse, selectSwitchResultPair?, h_match]
  | cons head rest ih =>
      have h_rest :
          ∀ branch ∈ rest, ∀ pt' template',
            branch = Atom.expression [pt', template'] →
            simpleMatch pt' scrut Bindings.empty fuel = none := by
        intro branch hmem pt' template' hshape
        exact h_earlier branch (by simp [hmem]) pt' template' hshape
      cases h_head : head with
      | symbol s =>
          simp [selectSwitchTemplateCoarse, selectSwitchResultPair?, h_head]
          exact ih h_rest
      | var v =>
          simp [selectSwitchTemplateCoarse, selectSwitchResultPair?, h_head]
          exact ih h_rest
      | grounded g =>
          simp [selectSwitchTemplateCoarse, selectSwitchResultPair?, h_head]
          exact ih h_rest
      | expression hs =>
          cases hs with
          | nil =>
              simp [selectSwitchTemplateCoarse, selectSwitchResultPair?, h_head]
              exact ih h_rest
          | cons a hs1 =>
              cases hs1 with
              | nil =>
                  simp [selectSwitchTemplateCoarse, selectSwitchResultPair?, h_head]
                  exact ih h_rest
              | cons b hs2 =>
                  cases hs2 with
                  | nil =>
                      have h_fail : simpleMatch a scrut Bindings.empty fuel = none :=
                        h_earlier (Atom.expression [a, b]) (by
                          simp [h_head]) a b rfl
                      simp [selectSwitchTemplateCoarse, selectSwitchResultPair?, h_fail]
                      exact ih h_rest
                  | cons c hs3 =>
                      simp [selectSwitchTemplateCoarse, selectSwitchResultPair?, h_head]
                      exact ih h_rest

/-- Indexed companion to `selectSwitchTemplateCoarse_of_prefix_match`.
This is the exact first-match theorem shape that the coarse
`HESmallStep.switch_minimal_match` constructor already carries: a selected
well-formed branch at index `i`, a successful match there, and failure of all
earlier well-formed branches. -/
theorem selectSwitchTemplateCoarse_of_index_match
    {scrut : Atom} {branches : List Atom} {i : Nat}
    {pt template : Atom} {mb : Bindings} {fuel : Nat}
    (h_branch : branches[i]? = some (.expression [pt, template]))
    (h_match : simpleMatch pt scrut Bindings.empty fuel = some mb)
    (h_earlier : ∀ j < i, ∀ pt' template',
      branches[j]? = some (.expression [pt', template']) →
      simpleMatch pt' scrut Bindings.empty fuel = none) :
    selectSwitchTemplateCoarse scrut branches fuel =
      mb.applyDefault template := by
  rcases (List.getElem?_eq_some_iff.mp h_branch) with ⟨hi, hget⟩
  have hsplit :
      branches =
        List.take i branches ++ Atom.expression [pt, template] ::
          List.drop (i + 1) branches := by
    calc
      branches = List.take i branches ++ List.drop i branches := by
        symm
        exact List.take_append_drop i branches
      _ = List.take i branches ++ branches[i] :: List.drop (i + 1) branches := by
        rw [List.drop_eq_getElem_cons hi]
      _ = List.take i branches ++ Atom.expression [pt, template] ::
            List.drop (i + 1) branches := by
        rw [hget]
  have h_prefix :
      ∀ branch ∈ List.take i branches, ∀ pt' template',
        branch = Atom.expression [pt', template'] →
        simpleMatch pt' scrut Bindings.empty fuel = none := by
    intro branch hmem pt' template' hshape
    rcases (List.mem_iff_getElem.mp hmem) with ⟨j, hj, hj_eq⟩
    have htake_len : (List.take i branches).length = i := by
      rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
    have hj_lt_i : j < i := by
      simpa [htake_len] using hj
    have hj_lt_len : j < branches.length := lt_trans hj_lt_i hi
    have hj_eq_branch : branches[j] = branch := by
      have htakej :
          (List.take i branches)[j] = branches[j] :=
        List.getElem_take (xs := branches) (j := i) (i := j) (h := hj)
      exact htakej.symm.trans hj_eq
    have hj_some :
        branches[j]? = some (Atom.expression [pt', template']) := by
      simp [List.getElem?_eq_getElem hj_lt_len, hj_eq_branch, hshape]
    exact h_earlier j hj_lt_i pt' template' hj_some
  rw [hsplit]
  exact selectSwitchTemplateCoarse_of_prefix_match h_match h_prefix

/-- If every well-formed branch fails to match the raw scrutinee, the coarse
selector returns the `NotReducible` sentinel.

Positive example: a branch list of only malformed branches returns
`NotReducible`.

Negative example: as soon as some well-formed branch matches, this theorem no
longer applies and `selectSwitchTemplateCoarse_of_prefix_match` becomes the
relevant fact instead. -/
theorem selectSwitchTemplateCoarse_notReducible_of_all_fail
    {scrut : Atom} {branches : List Atom} {fuel : Nat}
    (h_all_fail : ∀ branch ∈ branches, ∀ pt template,
      branch = Atom.expression [pt, template] →
      simpleMatch pt scrut Bindings.empty fuel = none) :
    selectSwitchTemplateCoarse scrut branches fuel = Atom.notReducible := by
  induction branches with
  | nil =>
      simp [selectSwitchTemplateCoarse, selectSwitchResultPair?]
  | cons head rest ih =>
      have h_rest :
          ∀ branch ∈ rest, ∀ pt template,
            branch = Atom.expression [pt, template] →
            simpleMatch pt scrut Bindings.empty fuel = none := by
        intro branch hmem pt template hshape
        exact h_all_fail branch (by simp [hmem]) pt template hshape
      cases h_head : head with
      | symbol s =>
          simp [selectSwitchTemplateCoarse, selectSwitchResultPair?, h_head]
          exact ih h_rest
      | var v =>
          simp [selectSwitchTemplateCoarse, selectSwitchResultPair?, h_head]
          exact ih h_rest
      | grounded g =>
          simp [selectSwitchTemplateCoarse, selectSwitchResultPair?, h_head]
          exact ih h_rest
      | expression hs =>
          cases hs with
          | nil =>
              simp [selectSwitchTemplateCoarse, selectSwitchResultPair?, h_head]
              exact ih h_rest
          | cons a hs1 =>
              cases hs1 with
              | nil =>
                  simp [selectSwitchTemplateCoarse, selectSwitchResultPair?, h_head]
                  exact ih h_rest
              | cons b hs2 =>
                  cases hs2 with
                  | nil =>
                      have h_head_fail :
                          simpleMatch a scrut Bindings.empty fuel = none :=
                        h_all_fail (Atom.expression [a, b]) (by
                          simp [h_head]) a b rfl
                      simp [selectSwitchTemplateCoarse, selectSwitchResultPair?, h_head_fail]
                      exact ih h_rest
                  | cons c hs3 =>
                      simp [selectSwitchTemplateCoarse, selectSwitchResultPair?, h_head]
                      exact ih h_rest

/-- Indexed companion to `selectSwitchTemplateCoarse_notReducible_of_all_fail`.
If every indexed well-formed branch fails to match the raw scrutinee, the
coarse selector returns `NotReducible`. -/
theorem selectSwitchTemplateCoarse_notReducible_of_index_fail
    {scrut : Atom} {branches : List Atom} {fuel : Nat}
    (h_all_fail : ∀ (i : Nat) (pt template : Atom),
      branches[i]? = some (Atom.expression [pt, template]) →
      simpleMatch pt scrut Bindings.empty fuel = none) :
    selectSwitchTemplateCoarse scrut branches fuel = Atom.notReducible := by
  apply selectSwitchTemplateCoarse_notReducible_of_all_fail
  intro branch hmem pt template hshape
  rcases (List.mem_iff_getElem.mp hmem) with ⟨i, hi, hi_eq⟩
  have hi_some :
      branches[i]? = some (Atom.expression [pt, template]) := by
    simp [List.getElem?_eq_getElem hi, hi_eq, hshape]
  exact h_all_fail i pt template hi_some

/-- Positive selector-to-coarse-step bridge: the indexed witness carried by
`HESmallStep.switch_minimal_match` produces a coarse step whose result is
exactly the primitive first-match selector result.  This keeps later
`switch-minimal` packaging aligned with the primitive selector surface rather
than only the raw `mb.applyDefault template` witness. -/
theorem step_switchMinimal_to_selector_of_index_match
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {scrut : Atom} {branches : List Atom} {i : Nat}
    {pt template : Atom} {mb : Bindings}
    (h_branch : branches[i]? = some (.expression [pt, template]))
    (h_match : simpleMatch pt scrut Bindings.empty fuel = some mb)
    (h_earlier : ∀ j < i, ∀ pt' template',
      branches[j]? = some (.expression [pt', template']) →
      simpleMatch pt' scrut Bindings.empty fuel = none) :
    HESmallStep space d fuel
      (.expression [.symbol "switch-minimal", scrut, .expression branches])
      (selectSwitchTemplateCoarse scrut branches fuel) := by
  have hsel :
      selectSwitchTemplateCoarse scrut branches fuel =
        mb.applyDefault template :=
    selectSwitchTemplateCoarse_of_index_match h_branch h_match h_earlier
  rw [hsel]
  exact HESmallStep.switch_minimal_match rfl h_branch h_match h_earlier

/-- Converse selector witness on the honest non-sentinel fragment: if the
primitive first-match selector returns some atom other than `NotReducible`,
then that result really came from a well-formed matching branch, together
with the exact indexed earlier-failure witness carried by the coarse
`switch_minimal_match` rule.  The sentinel case stays explicit because a
matching template may itself literally be `NotReducible`, so equality to the
sentinel alone is not enough to recover a coarse witness. -/
theorem selectSwitchTemplateCoarse_exists_of_ne_notReducible
    {scrut : Atom} {branches : List Atom} {fuel : Nat} {result : Atom}
    (hsel : selectSwitchTemplateCoarse scrut branches fuel = result)
    (hred : result ≠ Atom.notReducible) :
    ∃ (i : Nat) (pt template : Atom) (mb : Bindings),
      branches[i]? = some (.expression [pt, template]) ∧
      simpleMatch pt scrut Bindings.empty fuel = some mb ∧
      (∀ j < i, ∀ pt' template',
        branches[j]? = some (.expression [pt', template']) →
        simpleMatch pt' scrut Bindings.empty fuel = none) ∧
      result = mb.applyDefault template := by
  induction branches generalizing result with
  | nil =>
      simp [selectSwitchTemplateCoarse, selectSwitchResultPair?] at hsel
      exact False.elim (hred hsel.symm)
  | cons head tail ih =>
      cases h_head : head with
      | symbol s =>
          have hsel_tail : selectSwitchTemplateCoarse scrut tail fuel = result := by
            simpa [selectSwitchTemplateCoarse, selectSwitchResultPair?, h_head] using hsel
          rcases ih hsel_tail hred with
            ⟨i, pt, template, mb, h_branch, h_match, h_earlier, h_result⟩
          refine ⟨i + 1, pt, template, mb, ?_, h_match, ?_, h_result⟩
          · simpa using h_branch
          · intro j hj pt' template' h_branch_j
            cases j with
            | zero =>
                simp at h_branch_j
            | succ j' =>
                have hj' : j' < i := Nat.lt_of_succ_lt_succ hj
                exact h_earlier j' hj' pt' template' (by simpa using h_branch_j)
      | var v =>
          have hsel_tail : selectSwitchTemplateCoarse scrut tail fuel = result := by
            simpa [selectSwitchTemplateCoarse, selectSwitchResultPair?, h_head] using hsel
          rcases ih hsel_tail hred with
            ⟨i, pt, template, mb, h_branch, h_match, h_earlier, h_result⟩
          refine ⟨i + 1, pt, template, mb, ?_, h_match, ?_, h_result⟩
          · simpa using h_branch
          · intro j hj pt' template' h_branch_j
            cases j with
            | zero =>
                simp at h_branch_j
            | succ j' =>
                have hj' : j' < i := Nat.lt_of_succ_lt_succ hj
                exact h_earlier j' hj' pt' template' (by simpa using h_branch_j)
      | grounded g =>
          have hsel_tail : selectSwitchTemplateCoarse scrut tail fuel = result := by
            simpa [selectSwitchTemplateCoarse, selectSwitchResultPair?, h_head] using hsel
          rcases ih hsel_tail hred with
            ⟨i, pt, template, mb, h_branch, h_match, h_earlier, h_result⟩
          refine ⟨i + 1, pt, template, mb, ?_, h_match, ?_, h_result⟩
          · simpa using h_branch
          · intro j hj pt' template' h_branch_j
            cases j with
            | zero =>
                simp at h_branch_j
            | succ j' =>
                have hj' : j' < i := Nat.lt_of_succ_lt_succ hj
                exact h_earlier j' hj' pt' template' (by simpa using h_branch_j)
      | expression hs =>
          cases hs with
          | nil =>
              have hsel_tail : selectSwitchTemplateCoarse scrut tail fuel = result := by
                simpa [selectSwitchTemplateCoarse, selectSwitchResultPair?, h_head] using hsel
              rcases ih hsel_tail hred with
                ⟨i, pt, template, mb, h_branch, h_match, h_earlier, h_result⟩
              refine ⟨i + 1, pt, template, mb, ?_, h_match, ?_, h_result⟩
              · simpa using h_branch
              · intro j hj pt' template' h_branch_j
                cases j with
                | zero =>
                    simp at h_branch_j
                | succ j' =>
                    have hj' : j' < i := Nat.lt_of_succ_lt_succ hj
                    exact h_earlier j' hj' pt' template' (by simpa using h_branch_j)
          | cons a hs1 =>
              cases hs1 with
              | nil =>
                  have hsel_tail : selectSwitchTemplateCoarse scrut tail fuel = result := by
                    simpa [selectSwitchTemplateCoarse, selectSwitchResultPair?, h_head] using hsel
                  rcases ih hsel_tail hred with
                    ⟨i, pt, template, mb, h_branch, h_match, h_earlier, h_result⟩
                  refine ⟨i + 1, pt, template, mb, ?_, h_match, ?_, h_result⟩
                  · simpa using h_branch
                  · intro j hj pt' template' h_branch_j
                    cases j with
                    | zero =>
                        simp at h_branch_j
                    | succ j' =>
                        have hj' : j' < i := Nat.lt_of_succ_lt_succ hj
                        exact h_earlier j' hj' pt' template' (by simpa using h_branch_j)
              | cons b hs2 =>
                  cases hs2 with
                  | nil =>
                      cases h_match0 : simpleMatch a scrut Bindings.empty fuel with
                      | none =>
                          have hsel_tail :
                              selectSwitchTemplateCoarse scrut tail fuel = result := by
                            simpa [selectSwitchTemplateCoarse, selectSwitchResultPair?, h_head, h_match0] using hsel
                          rcases ih hsel_tail hred with
                            ⟨i, pt, template, mb, h_branch, h_match, h_earlier, h_result⟩
                          refine ⟨i + 1, pt, template, mb, ?_, h_match, ?_, h_result⟩
                          · simpa using h_branch
                          · intro j hj pt' template' h_branch_j
                            cases j with
                            | zero =>
                                have h_pair :
                                    Atom.expression [a, b] =
                                      Atom.expression [pt', template'] := by
                                  simpa [h_head] using h_branch_j
                                cases h_pair
                                simpa using h_match0
                            | succ j' =>
                                have hj' : j' < i := Nat.lt_of_succ_lt_succ hj
                                exact h_earlier j' hj' pt' template'
                                  (by simpa using h_branch_j)
                      | some mb0 =>
                          refine ⟨0, a, b, mb0, ?_, h_match0, ?_, ?_⟩
                          · simp
                          · intro j hj
                            exact False.elim (Nat.not_lt_zero _ hj)
                          · simpa [selectSwitchTemplateCoarse, selectSwitchResultPair?, h_head, h_match0] using hsel.symm
                  | cons c hs3 =>
                      have hsel_tail : selectSwitchTemplateCoarse scrut tail fuel = result := by
                        simpa [selectSwitchTemplateCoarse, selectSwitchResultPair?, h_head] using hsel
                      rcases ih hsel_tail hred with
                        ⟨i, pt, template, mb, h_branch, h_match, h_earlier, h_result⟩
                      refine ⟨i + 1, pt, template, mb, ?_, h_match, ?_, h_result⟩
                      · simpa using h_branch
                      · intro j hj pt' template' h_branch_j
                        cases j with
                        | zero =>
                            simp at h_branch_j
                        | succ j' =>
                            have hj' : j' < i := Nat.lt_of_succ_lt_succ hj
                            exact h_earlier j' hj' pt' template' (by simpa using h_branch_j)

/-- Selector-to-coarse-step converse on the honest non-sentinel fragment.
If the primitive selector returns some atom other than `NotReducible`, then
the coarse `switch-minimal` relation really does have a visible match step to
that result. -/
theorem step_switchMinimal_of_selector_ne_notReducible
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {scrut : Atom} {branches : List Atom} {result : Atom}
    (hsel : selectSwitchTemplateCoarse scrut branches fuel = result)
    (hred : result ≠ Atom.notReducible) :
    HESmallStep space d fuel
      (.expression [.symbol "switch-minimal", scrut, .expression branches])
      result := by
  rcases selectSwitchTemplateCoarse_exists_of_ne_notReducible hsel hred with
    ⟨i, pt, template, mb, h_branch, h_match, h_earlier, h_result⟩
  rw [h_result]
  exact HESmallStep.switch_minimal_match rfl h_branch h_match h_earlier

/-! ## F3b: Direct Executable `switch-minimal` Results

The coarse selector witnesses above describe which branch should be chosen.
The executable evaluator now exposes that choice through
`switchMinimalResults`, so we record the corresponding direct membership fact
before packaging it into `MettaCall`/`EvalAtom` shells. -/

/-- Positive executable witness for the direct `switch-minimal` lane: if a
particular well-formed branch is the first one whose pattern matches the raw
scrutinee, and the surviving merged bindings are loop-free, then the
observable executable result set contains exactly that branch result (with the
stdlib `NotReducible -> Empty` post-processing). -/
theorem switchMinimalResults_mem_of_prefix_match
    {scrut pt template : Atom} {pre post : List Atom}
    {mb : Bindings} {n : Nat}
    (h_match : simpleMatch pt scrut Bindings.empty (n + 1) = some mb)
    (h_no_loop : mb.hasLoop = false)
    (h_earlier : ∀ branch ∈ pre, ∀ pt' template',
      branch = Atom.expression [pt', template'] →
      simpleMatch pt' scrut Bindings.empty (n + 1) = none) :
    ((if mb.applyDefault template == Atom.notReducible
        then Atom.empty else mb.applyDefault template), mb)
      ∈ switchMinimalResults scrut
          (pre ++ Atom.expression [pt, template] :: post)
          Bindings.empty (n + 1) := by
  induction pre with
  | nil =>
      simp [switchMinimalResults, switchMinimalRawResults, h_match,
        mergeBindings_empty_right, h_no_loop]
  | cons head rest ih =>
      have h_rest :
          ∀ branch ∈ rest, ∀ pt' template',
            branch = Atom.expression [pt', template'] →
            simpleMatch pt' scrut Bindings.empty (n + 1) = none := by
        intro branch hmem pt' template' hshape
        exact h_earlier branch (by simp [hmem]) pt' template' hshape
      cases h_head : head with
      | symbol s =>
          simpa [switchMinimalResults, switchMinimalRawResults, h_head] using
            ih h_rest
      | var v =>
          simpa [switchMinimalResults, switchMinimalRawResults, h_head] using
            ih h_rest
      | grounded g =>
          simpa [switchMinimalResults, switchMinimalRawResults, h_head] using
            ih h_rest
      | expression hs =>
          cases hs with
          | nil =>
              simpa [switchMinimalResults, switchMinimalRawResults, h_head] using
                ih h_rest
          | cons a hs =>
              cases hs with
              | nil =>
                  simpa [switchMinimalResults, switchMinimalRawResults, h_head] using
                    ih h_rest
              | cons b hs' =>
                  cases hs' with
                  | nil =>
                      have h_miss : simpleMatch a scrut Bindings.empty (n + 1) = none := by
                        exact h_earlier head (by simp) a b h_head
                      simpa [switchMinimalResults, switchMinimalRawResults, h_head, h_miss] using
                        ih h_rest
                  | cons c hs'' =>
                      simpa [switchMinimalResults, switchMinimalRawResults, h_head] using
                        ih h_rest

/-- Indexed companion to `switchMinimalResults_mem_of_prefix_match`, matching
the exact witness shape carried by `HESmallStep.switch_minimal_match`. -/
theorem switchMinimalResults_mem_of_index_match
    {scrut : Atom} {branches : List Atom} {i : Nat}
    {pt template : Atom} {mb : Bindings} {n : Nat}
    (h_branch : branches[i]? = some (.expression [pt, template]))
    (h_match : simpleMatch pt scrut Bindings.empty (n + 1) = some mb)
    (h_no_loop : mb.hasLoop = false)
    (h_earlier : ∀ j < i, ∀ pt' template',
      branches[j]? = some (.expression [pt', template']) →
      simpleMatch pt' scrut Bindings.empty (n + 1) = none) :
    ((if mb.applyDefault template == Atom.notReducible
        then Atom.empty else mb.applyDefault template), mb)
      ∈ switchMinimalResults scrut branches Bindings.empty (n + 1) := by
  rcases (List.getElem?_eq_some_iff.mp h_branch) with ⟨hi, hget⟩
  have hsplit :
      branches =
        List.take i branches ++ Atom.expression [pt, template] ::
          List.drop (i + 1) branches := by
    calc
      branches = List.take i branches ++ List.drop i branches := by
        symm
        exact List.take_append_drop i branches
      _ = List.take i branches ++ branches[i] :: List.drop (i + 1) branches := by
        rw [List.drop_eq_getElem_cons hi]
      _ = List.take i branches ++ Atom.expression [pt, template] ::
            List.drop (i + 1) branches := by
        rw [hget]
  have h_prefix :
      ∀ branch ∈ List.take i branches, ∀ pt' template',
        branch = Atom.expression [pt', template'] →
        simpleMatch pt' scrut Bindings.empty (n + 1) = none := by
    intro branch hmem pt' template' hshape
    rcases (List.mem_iff_getElem.mp hmem) with ⟨j, hj, hj_eq⟩
    have htake_len : (List.take i branches).length = i := by
      rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
    have hj_lt_i : j < i := by
      simpa [htake_len] using hj
    have hj_lt_len : j < branches.length := lt_trans hj_lt_i hi
    have hj_eq_branch : branches[j] = branch := by
      have htakej :
          (List.take i branches)[j] = branches[j] :=
        List.getElem_take (xs := branches) (j := i) (i := j) (h := hj)
      exact htakej.symm.trans hj_eq
    have hj_some :
        branches[j]? = some (Atom.expression [pt', template']) := by
      simp [List.getElem?_eq_getElem hj_lt_len, hj_eq_branch, hshape]
    exact h_earlier j hj_lt_i pt' template' hj_some
  rw [hsplit]
  exact switchMinimalResults_mem_of_prefix_match h_match h_no_loop h_prefix

/-! ## F3: `switch-minimal` / `switch-internal` Typed Function + Equation Shells

The matcher bridge and `unify` realization now give us the branch-local core
of `switch-internal`. The next honest outer layer is the typed/equational
surface shell shared by `switch-minimal` and `switch-internal`: both are
stdlib equations whose heads carry the same binary function type
`(-> Atom Expression Atom)`. We expose that shell explicitly so the later
recursive branch proof can spend real interface theorems rather than rebuild
the function/equation plumbing ad hoc. -/

/-- The shared stdlib function type for `switch-minimal` and
`switch-internal`. -/
private def switchBinaryFunctionType : Atom :=
  .expression [.symbol "->", Atom.atomType, Atom.expressionType, Atom.atomType]

/-- Surface `switch-minimal` atom in the upstream stdlib shape. -/
private def switchMinimalExpr (scrut : Atom) (branches : List Atom) : Atom :=
  .expression [.symbol "switch-minimal", scrut, .expression branches]

/-- Surface `switch-internal` atom in the upstream stdlib shape. -/
private def switchInternalExpr (scrut headBranch : Atom) (tail : List Atom) : Atom :=
  .expression [.symbol "switch-internal", scrut,
    .expression [headBranch, .expression tail]]

/-- The recursive else-branch used by the upstream `switch-internal` helper. -/
private def switchInternalElseChain (scrut : Atom) (tail : List Atom) : Atom :=
  .expression [.symbol "chain",
    .expression [.symbol "eval", switchMinimalExpr scrut tail],
    .var "ret",
    .expression [.symbol "return", .var "ret"]]

/-- The verbatim upstream `unify` core inside `switch-internal`. -/
private def switchInternalUnify
    (scrut pt template : Atom) (tail : List Atom) : Atom :=
  .expression [.symbol "unify", scrut, pt,
    .expression [.symbol "return", template],
    switchInternalElseChain scrut tail]

/-- The verbatim upstream `function` body for `switch-internal`. -/
private def switchInternalBody
    (scrut pt template : Atom) (tail : List Atom) : Atom :=
  .expression [.symbol "function", switchInternalUnify scrut pt template tail]

/-- Alpha-renamed variant of the recursive else-branch used by
`switch-internal`: the local chain binder may be any fresh variable name,
not just the unsuffixed surface spelling.  This matches the real
`queryEquations` route, which freshens all equation-local variables. -/
private def switchInternalElseChainVar
    (retVar : String) (scrut : Atom) (tail : List Atom) : Atom :=
  .expression [.symbol "chain",
    .expression [.symbol "eval", switchMinimalExpr scrut tail],
    .var retVar,
    .expression [.symbol "return", .var retVar]]

/-- Alpha-renamed variant of the upstream `unify` core inside
`switch-internal`, parameterized by the freshened local binder used in the
recursive else branch. -/
private def switchInternalUnifyVar
    (retVar : String) (scrut pt template : Atom) (tail : List Atom) : Atom :=
  .expression [.symbol "unify", scrut, pt,
    .expression [.symbol "return", template],
    switchInternalElseChainVar retVar scrut tail]

/-- Alpha-renamed variant of the verbatim upstream `function` body for
`switch-internal`, parameterized by the freshened local binder. -/
private def switchInternalBodyVar
    (retVar : String) (scrut pt template : Atom) (tail : List Atom) : Atom :=
  .expression [.symbol "function", switchInternalUnifyVar retVar scrut pt template tail]

private theorem switchInternalElseChainVar_ret
    (scrut : Atom) (tail : List Atom) :
    switchInternalElseChainVar "ret" scrut tail = switchInternalElseChain scrut tail := rfl

private theorem switchInternalUnifyVar_ret
    (scrut pt template : Atom) (tail : List Atom) :
    switchInternalUnifyVar "ret" scrut pt template tail =
      switchInternalUnify scrut pt template tail := rfl

private theorem switchInternalBodyVar_ret
    (scrut pt template : Atom) (tail : List Atom) :
    switchInternalBodyVar "ret" scrut pt template tail =
      switchInternalBody scrut pt template tail := rfl

/-- If the space presents `switch-minimal` with exactly its stdlib function
type, then the official type-cast path evaluates the head symbol to itself at
that type. -/
private theorem evalAtom_switchMinimal_head_typed
    {space : Space} {d : GroundedDispatch}
    (h_types : getAtomTypes space (.symbol "switch-minimal") = [switchBinaryFunctionType]) :
    EvalAtom space d (.symbol "switch-minimal") switchBinaryFunctionType Bindings.empty
      (.symbol "switch-minimal", Bindings.empty) := by
  refine EvalAtom.type_cast _ _ _ _ 10 rfl ?_ (Or.inl rfl) ?_
  · simp [switchBinaryFunctionType, getMetaType, Atom.atomType,
      Atom.symbolType, Atom.variableType]
  · rw [typeCast, h_types]
    native_decide

/-- If the space presents `switch-internal` with exactly its stdlib function
type, then the official type-cast path evaluates the head symbol to itself at
that type. -/
private theorem evalAtom_switchInternal_head_typed
    {space : Space} {d : GroundedDispatch}
    (h_types : getAtomTypes space (.symbol "switch-internal") = [switchBinaryFunctionType]) :
    EvalAtom space d (.symbol "switch-internal") switchBinaryFunctionType Bindings.empty
      (.symbol "switch-internal", Bindings.empty) := by
  refine EvalAtom.type_cast _ _ _ _ 10 rfl ?_ (Or.inl rfl) ?_
  · simp [switchBinaryFunctionType, getMetaType, Atom.atomType,
      Atom.symbolType, Atom.variableType]
  · rw [typeCast, h_types]
    native_decide

/-- Any non-empty, non-error-headed expression can be evaluated against the
expected type `Expression`, producing itself with unchanged bindings. -/
private theorem evalAtom_expr_type_self
    {space : Space} {d : GroundedDispatch}
    (head : Atom) (tail : List Atom) (b : Bindings)
    (h_head_nerr : head ≠ Atom.symbol "Error") :
    EvalAtom space d (.expression (head :: tail)) Atom.expressionType b
      (.expression (head :: tail), b) := by
  exact EvalAtom.type_pass _ _ _ (isEmptyOrError_expr_false tail h_head_nerr)
    (Or.inr (Or.inl rfl))

/-- Shared argument-shell lemma for the binary switch helpers:
the first argument is interpreted at type `Atom`, and the second at type
`Expression`, both self-evaluating on the certified fragment. -/
private theorem interpretArgs_switch_binary_self
    {space : Space} {d : GroundedDispatch}
    {scrut head : Atom} {tail : List Atom}
    (h_head_nerr : head ≠ Atom.symbol "Error") :
    InterpretArgs space d [scrut, .expression (head :: tail)]
      [Atom.atomType, Atom.expressionType]
      Bindings.empty
      (.expression [scrut, .expression (head :: tail)], Bindings.empty) := by
  have h_scrut : EvalAtom space d scrut Atom.atomType Bindings.empty
      (scrut, Bindings.empty) :=
    evalAtom_atom_type scrut Bindings.empty
  have h_cases : EvalAtom space d (.expression (head :: tail))
      Atom.expressionType Bindings.empty
      (.expression (head :: tail), Bindings.empty) :=
    evalAtom_expr_type_self head tail Bindings.empty h_head_nerr
  have h_tail : InterpretArgs space d [.expression (head :: tail)]
      [Atom.expressionType] Bindings.empty
      (.expression [.expression (head :: tail)], Bindings.empty) := by
    exact InterpretArgs.cons_ok (.expression (head :: tail)) [] Atom.expressionType []
      Bindings.empty
      (.expression (head :: tail), Bindings.empty)
      (Atom.unit, Bindings.empty)
      h_cases (Or.inr rfl) InterpretArgs.nil rfl
  refine InterpretArgs.cons_ok scrut [.expression (head :: tail)] Atom.atomType
    [Atom.expressionType] Bindings.empty
    (scrut, Bindings.empty) (.expression [.expression (head :: tail)], Bindings.empty)
    h_scrut (Or.inr rfl) h_tail ?_
  exact isEmptyOrError_expr_false [] (by simp)

/-- Typed function-path shell for the verbatim upstream `switch-minimal`
surface form on the fragment where the raw-cases expression is non-empty and
not error-shaped. -/
theorem interpretFunction_switchMinimal_self
    {space : Space} {d : GroundedDispatch}
    {scrut headBranch : Atom} {tail : List Atom}
    (h_types : getAtomTypes space (.symbol "switch-minimal") = [switchBinaryFunctionType])
    (h_scrut_nerr : scrut ≠ Atom.symbol "Error")
    (h_head_nerr : headBranch ≠ Atom.symbol "Error") :
    InterpretFunction space d (switchMinimalExpr scrut (headBranch :: tail))
      switchBinaryFunctionType Atom.undefinedType Bindings.empty
      (switchMinimalExpr scrut (headBranch :: tail), Bindings.empty) := by
  have h_head : EvalAtom space d (.symbol "switch-minimal")
      switchBinaryFunctionType Bindings.empty
      (.symbol "switch-minimal", Bindings.empty) :=
    evalAtom_switchMinimal_head_typed h_types
  have h_tail : InterpretArgs space d [scrut, .expression (headBranch :: tail)]
      [Atom.atomType, Atom.expressionType]
      Bindings.empty
      (.expression [scrut, .expression (headBranch :: tail)], Bindings.empty) :=
    interpretArgs_switch_binary_self h_head_nerr
  refine InterpretFunction.head_ok_tail_ok
    (switchMinimalExpr scrut (headBranch :: tail))
    switchBinaryFunctionType Atom.undefinedType Bindings.empty
    (.symbol "switch-minimal") [scrut, .expression (headBranch :: tail)]
    [Atom.atomType, Atom.expressionType]
    (.symbol "switch-minimal", Bindings.empty)
    (.expression [scrut, .expression (headBranch :: tail)], Bindings.empty)
    rfl rfl h_head rfl h_tail ?_
  exact isEmptyOrError_expr_false [.expression (headBranch :: tail)] h_scrut_nerr

/-- Typed function-path shell for the verbatim upstream `switch-internal`
surface form on the fragment where the deconsed head branch is itself not the
bare `Error` symbol.  In the intended use that head is a branch pair
expression, so this side condition is immediate. -/
theorem interpretFunction_switchInternal_self
    {space : Space} {d : GroundedDispatch}
    {scrut headBranch : Atom} {tail : List Atom}
    (h_types : getAtomTypes space (.symbol "switch-internal") = [switchBinaryFunctionType])
    (h_scrut_nerr : scrut ≠ Atom.symbol "Error")
    (h_head_nerr : headBranch ≠ Atom.symbol "Error") :
    InterpretFunction space d (switchInternalExpr scrut headBranch tail)
      switchBinaryFunctionType Atom.undefinedType Bindings.empty
      (switchInternalExpr scrut headBranch tail, Bindings.empty) := by
  have h_head : EvalAtom space d (.symbol "switch-internal")
      switchBinaryFunctionType Bindings.empty
      (.symbol "switch-internal", Bindings.empty) :=
    evalAtom_switchInternal_head_typed h_types
  have h_tail : InterpretArgs space d [scrut, .expression [headBranch, .expression tail]]
      [Atom.atomType, Atom.expressionType]
      Bindings.empty
      (.expression [scrut, .expression [headBranch, .expression tail]], Bindings.empty) :=
    interpretArgs_switch_binary_self h_head_nerr
  refine InterpretFunction.head_ok_tail_ok
    (switchInternalExpr scrut headBranch tail)
    switchBinaryFunctionType Atom.undefinedType Bindings.empty
    (.symbol "switch-internal") [scrut, .expression [headBranch, .expression tail]]
    [Atom.atomType, Atom.expressionType]
    (.symbol "switch-internal", Bindings.empty)
    (.expression [scrut, .expression [headBranch, .expression tail]], Bindings.empty)
    rfl rfl h_head rfl h_tail ?_
  exact isEmptyOrError_expr_false [.expression [headBranch, .expression tail]] h_scrut_nerr

/-- Direct `MettaCall` wrapper for the exact-shape upstream
`switch-minimal` surface form.  After the evaluator-side refactor,
`switch-minimal` no longer reaches the generic equation lane; its official
observable behavior is the dedicated `switchMinimalResults` kernel. -/
theorem mettaCall_absorbs_switchMinimal_direct
    {space : Space} {d : GroundedDispatch}
    {scrut : Atom} {branches : List Atom} {type_ : Atom}
    {final : ResultPair} {fuel : Nat}
    (h_result : final ∈ switchMinimalResults scrut branches Bindings.empty fuel) :
    MettaCall space d (switchMinimalExpr scrut branches) type_
      Bindings.empty final :=
  MettaCall.switch_minimal_result _ _ _ scrut branches final fuel
    rfl
    (by simp [switchMinimalExpr, isErrorAtom])
    h_result

/-- Generic equation-call wrapper for the verbatim upstream `switch-internal`
surface form. -/
theorem mettaCall_absorbs_switchInternal_equation
    {space : Space} {d : GroundedDispatch}
    {scrut headBranch : Atom} {tail : List Atom}
    {type_ rhs : Atom} {qb merged : Bindings}
    {final : ResultPair} {fuel : Nat}
    (h_not_exec : d.isExecutable (.symbol "switch-internal") = false)
    (h_query : (rhs, qb) ∈ queryEquations space
      (switchInternalExpr scrut headBranch tail) fuel)
    (h_merge : merged ∈ mergeBindings qb Bindings.empty fuel)
    (h_no_loop : merged.hasLoop = false)
    (h_eval : EvalAtom space d (merged.apply rhs fuel) type_ merged final) :
    MettaCall space d (switchInternalExpr scrut headBranch tail) type_
      Bindings.empty final :=
  MettaCall.equation_match _ _ _ rhs qb merged final fuel
    (by simp [switchInternalExpr, isErrorAtom])
    (by
      refine ⟨?_, ?_⟩
      · simpa [switchInternalExpr] using h_not_exec
      · simp)
    h_query h_merge h_no_loop h_eval

/-- Outer official shell for `switch-minimal`, relative to the explicit typed
function-path and equation-call hypotheses.  This isolates the remaining
recursive branch-selection content from the already-settled surface
typed/equational plumbing. -/
theorem evalAtom_absorbs_switchMinimal_shell
    {space : Space} {d : GroundedDispatch}
    {scrut headBranch : Atom} {tail : List Atom} {final : ResultPair}
    {succs : List Bindings} {fuel : Nat}
    (h_op_type : switchBinaryFunctionType ∈ getAtomTypes space (.symbol "switch-minimal"))
    (h_check : checkIfFunctionTypeIsApplicable
      (switchMinimalExpr scrut (headBranch :: tail)) switchBinaryFunctionType Atom.undefinedType
      space Bindings.empty fuel = .inr succs)
    (h_check_b : Bindings.empty ∈ succs)
    (h_interp : InterpretFunction space d (switchMinimalExpr scrut (headBranch :: tail))
      switchBinaryFunctionType Atom.undefinedType Bindings.empty
      (switchMinimalExpr scrut (headBranch :: tail), Bindings.empty))
    (h_call : MettaCall space d (switchMinimalExpr scrut (headBranch :: tail))
      Atom.atomType Bindings.empty final)
    (h_final_ok : isErrorAtom final.1 = false) :
    EvalAtom space d (switchMinimalExpr scrut (headBranch :: tail))
      Atom.undefinedType Bindings.empty final := by
  refine EvalAtom.interpret_success _ _ _ _ ?_ ?_ rfl ?_ ?_ h_final_ok
  · exact isEmptyOrError_expr_false [scrut, .expression (headBranch :: tail)] (by simp)
  · simp [switchMinimalExpr, getMetaType, Atom.undefinedType, Atom.atomType,
      Atom.expressionType, Atom.variableType]
  · intro h_unit
    simp [switchMinimalExpr, Atom.unit] at h_unit
  · refine InterpretExpression.function_path _ _ _
      (.symbol "switch-minimal") [scrut, .expression (headBranch :: tail)]
      switchBinaryFunctionType Atom.atomType Bindings.empty
      (switchMinimalExpr scrut (headBranch :: tail), Bindings.empty) final fuel
      rfl h_op_type ?_ succs h_check h_check_b ?_ h_interp h_call
    · rfl
    · native_decide

/-- Honest direct outer shell for exact-shape `switch-minimal`: once the
typed function-path checks have admitted the surface form, any executable
result already present in `switchMinimalResults` is an official `EvalAtom`
result of the whole call.  This is the dedicated executable route that
replaces the old equation-wrapper fiction. -/
theorem evalAtom_absorbs_switchMinimal_direct_shell
    {space : Space} {d : GroundedDispatch}
    {scrut headBranch : Atom} {tail : List Atom} {final : ResultPair}
    {succs : List Bindings} {fuelCheck fuelCall : Nat}
    (h_types : getAtomTypes space (.symbol "switch-minimal") = [switchBinaryFunctionType])
    (h_check : checkIfFunctionTypeIsApplicable
      (switchMinimalExpr scrut (headBranch :: tail)) switchBinaryFunctionType Atom.undefinedType
      space Bindings.empty fuelCheck = .inr succs)
    (h_check_b : Bindings.empty ∈ succs)
    (h_scrut_nerr : scrut ≠ Atom.symbol "Error")
    (h_head_nerr : headBranch ≠ Atom.symbol "Error")
    (h_result : final ∈ switchMinimalResults scrut (headBranch :: tail) Bindings.empty fuelCall)
    (h_final_ok : isErrorAtom final.1 = false) :
    EvalAtom space d (switchMinimalExpr scrut (headBranch :: tail))
      Atom.undefinedType Bindings.empty final := by
  have h_interp :
      InterpretFunction space d (switchMinimalExpr scrut (headBranch :: tail))
        switchBinaryFunctionType Atom.undefinedType Bindings.empty
        (switchMinimalExpr scrut (headBranch :: tail), Bindings.empty) :=
    interpretFunction_switchMinimal_self h_types h_scrut_nerr h_head_nerr
  have h_call :
      MettaCall space d (switchMinimalExpr scrut (headBranch :: tail))
        Atom.atomType Bindings.empty final :=
    mettaCall_absorbs_switchMinimal_direct h_result
  have h_op_type : switchBinaryFunctionType ∈ getAtomTypes space (.symbol "switch-minimal") := by
    rw [h_types]
    simp
  exact evalAtom_absorbs_switchMinimal_shell
    h_op_type h_check h_check_b h_interp h_call h_final_ok

/-- Honest direct success-side rule theorem for the non-sentinel ground
fragment of coarse `switch-minimal`: when the selected branch is the first
matching well-formed branch, its substituted template is an official direct
evaluator result of the whole `switch-minimal` call. -/
theorem evalAtom_absorbs_switchMinimal_match_ground_rule
    {space : Space} {d : GroundedDispatch}
    {scrut headBranch : Atom} {tail : List Atom}
    {i : Nat} {pt template : Atom} {mb : Bindings}
    {succs : List Bindings} {fuelStep fuelShell : Nat}
    (_h_step : HESmallStep space d fuelStep
      (switchMinimalExpr scrut (headBranch :: tail)) (mb.applyDefault template))
    (h_types : getAtomTypes space (.symbol "switch-minimal") = [switchBinaryFunctionType])
    (h_check : checkIfFunctionTypeIsApplicable
      (switchMinimalExpr scrut (headBranch :: tail))
      switchBinaryFunctionType Atom.undefinedType
      space Bindings.empty fuelShell = .inr succs)
    (h_check_b : Bindings.empty ∈ succs)
    (h_scrut_nerr : scrut ≠ Atom.symbol "Error")
    (h_head_nerr : headBranch ≠ Atom.symbol "Error")
    (hground : GroundAtom scrut)
    (h_branch : (headBranch :: tail)[i]? = some (.expression [pt, template]))
    (h_match : simpleMatch pt scrut Bindings.empty fuelStep = some mb)
    (h_earlier : ∀ j < i, ∀ pt' template',
      (headBranch :: tail)[j]? = some (.expression [pt', template']) →
      simpleMatch pt' scrut Bindings.empty fuelStep = none)
    (h_not_reducible : mb.applyDefault template ≠ Atom.notReducible)
    (h_final_ok : isErrorAtom (mb.applyDefault template) = false) :
    EvalAtom space d (switchMinimalExpr scrut (headBranch :: tail))
      Atom.undefinedType Bindings.empty
      (mb.applyDefault template, mb) := by
  cases fuelStep with
  | zero =>
      simp [simpleMatch] at h_match
  | succ n =>
      obtain ⟨fuel0, hmb, _⟩ := simpleMatch_ground_matchAtoms hground h_match
      have hmbCanon : GroundBindingsCanon mb := matchAtoms_ground_canon hground hmb
      have hnoLoop : mb.hasLoop = false :=
        GroundBindings.hasLoop_false hmbCanon.1
      have h_result :
          ((if mb.applyDefault template == Atom.notReducible
              then Atom.empty else mb.applyDefault template), mb)
            ∈ switchMinimalResults scrut (headBranch :: tail) Bindings.empty (n + 1) :=
        switchMinimalResults_mem_of_index_match h_branch h_match hnoLoop h_earlier
      have h_result' :
          (mb.applyDefault template, mb) ∈
            switchMinimalResults scrut (headBranch :: tail) Bindings.empty (n + 1) := by
        simpa [h_not_reducible] using h_result
      exact evalAtom_absorbs_switchMinimal_direct_shell
        h_types h_check h_check_b h_scrut_nerr h_head_nerr h_result' h_final_ok

/-- Outer official shell for `switch-internal`, relative to the explicit
typed function-path and equation-call hypotheses.  This isolates the
recursive head-hit/head-miss proof from the already-settled typed/equational
surface layer. -/
theorem evalAtom_absorbs_switchInternal_shell
    {space : Space} {d : GroundedDispatch}
    {scrut headBranch : Atom} {tail : List Atom} {final : ResultPair}
    {succs : List Bindings} {fuel : Nat}
    (h_op_type : switchBinaryFunctionType ∈ getAtomTypes space (.symbol "switch-internal"))
    (h_check : checkIfFunctionTypeIsApplicable
      (switchInternalExpr scrut headBranch tail) switchBinaryFunctionType
      Atom.undefinedType space Bindings.empty fuel = .inr succs)
    (h_check_b : Bindings.empty ∈ succs)
    (h_interp : InterpretFunction space d (switchInternalExpr scrut headBranch tail)
      switchBinaryFunctionType Atom.undefinedType Bindings.empty
      (switchInternalExpr scrut headBranch tail, Bindings.empty))
    (h_call : MettaCall space d (switchInternalExpr scrut headBranch tail)
      Atom.atomType Bindings.empty final)
    (h_final_ok : isErrorAtom final.1 = false) :
    EvalAtom space d (switchInternalExpr scrut headBranch tail)
      Atom.undefinedType Bindings.empty final := by
  refine EvalAtom.interpret_success _ _ _ _ ?_ ?_ rfl ?_ ?_ h_final_ok
  · exact isEmptyOrError_expr_false
      [scrut, .expression [headBranch, .expression tail]] (by simp)
  · simp [switchInternalExpr, getMetaType, Atom.undefinedType, Atom.atomType,
      Atom.expressionType, Atom.variableType]
  · intro h_unit
    simp [switchInternalExpr, Atom.unit] at h_unit
  · refine InterpretExpression.function_path _ _ _
      (.symbol "switch-internal") [scrut, .expression [headBranch, .expression tail]]
      switchBinaryFunctionType Atom.atomType Bindings.empty
      (switchInternalExpr scrut headBranch tail, Bindings.empty) final fuel
      rfl h_op_type ?_ succs h_check h_check_b ?_ h_interp h_call
    · rfl
    · native_decide

/-! ## F2b: `switch-internal` Evaluator Boundary

The `unify` realization is now explicit, but the recursive `switch-internal`
helper also depends on three other minimal control operators in the live
evaluator: `eval`, `chain`, and `function/return`.  We surface exactly that
boundary here rather than silently smuggling those behaviors into the later
branch-selection proof. -/

/-- Stable evaluator boundary for the exact minimal helpers that
`switch-internal` spends in addition to `unify`. -/
structure SwitchInternalGroundRealization (space : Space) (d : GroundedDispatch)
    extends UnifyGroundBranchRealization space d where
  evalStable :
    ∀ {atom : Atom} {r : ResultPair},
      EvalAtom space d atom Atom.undefinedType Bindings.empty r →
      EvalAtomStablyReaches space d
        (.expression [.symbol "eval", atom])
        Atom.undefinedType Bindings.empty r
  chainStable :
    ∀ {atom template : Atom} {v : String} {result : Atom} {rb : Bindings},
      EvalAtom space d atom Atom.undefinedType Bindings.empty (result, rb) →
      result ≠ Atom.empty →
      EvalAtomStablyReaches space d
        (.expression [.symbol "chain", atom, .var v, template])
        Atom.undefinedType Bindings.empty
        ((Bindings.assign rb v result).applyDefault template,
          Bindings.assign rb v result)
  functionReturnStable :
    ∀ {body ret : Atom} {rb : Bindings},
      EvalAtom space d body Atom.undefinedType Bindings.empty
        (.expression [.symbol "return", ret], rb) →
      EvalAtomStablyReaches space d
        (.expression [.symbol "function", body])
        Atom.undefinedType Bindings.empty
        (ret, rb)
  functionContinueStable :
    ∀ {body mid ret : Atom} {mb rb : Bindings},
      EvalAtom space d body Atom.undefinedType Bindings.empty (mid, mb) →
      EvalAtom space d mid Atom.undefinedType mb
        (.expression [.symbol "return", ret], rb) →
      EvalAtomStablyReaches space d
        (.expression [.symbol "function", body])
        Atom.undefinedType Bindings.empty
        (ret, rb)

/-- Seeded companion to `SwitchInternalGroundRealization`: the exact same
minimal helper boundaries, but under an arbitrary incoming bindings seed.
This is the form the stdlib equation-helper route needs after
`queryEquations` has contributed fresh local bindings before the recursive
`switch-internal` body runs. -/
structure SwitchInternalGroundSeededRealization (space : Space)
    (d : GroundedDispatch) extends UnifyGroundSeededBranchRealization space d where
  evalStableSeeded :
    ∀ {seed : Bindings} {atom : Atom} {r : ResultPair},
      EvalAtom space d atom Atom.undefinedType seed r →
      EvalAtomStablyReaches space d
        (.expression [.symbol "eval", atom])
        Atom.undefinedType seed r
  chainStableSeeded :
    ∀ {seed : Bindings} {atom template : Atom} {v : String}
      {result : Atom} {rb : Bindings},
      EvalAtom space d atom Atom.undefinedType seed (result, rb) →
      result ≠ Atom.empty →
      EvalAtomStablyReaches space d
        (.expression [.symbol "chain", atom, .var v, template])
        Atom.undefinedType seed
        ((Bindings.assign rb v result).applyDefault template,
          Bindings.assign rb v result)
  functionReturnStableSeeded :
    ∀ {seed : Bindings} {body ret : Atom} {rb : Bindings},
      EvalAtom space d body Atom.undefinedType seed
        (.expression [.symbol "return", ret], rb) →
      EvalAtomStablyReaches space d
        (.expression [.symbol "function", body])
        Atom.undefinedType seed
        (ret, rb)
  functionContinueStableSeeded :
    ∀ {seed : Bindings} {body mid ret : Atom} {mb rb : Bindings},
      EvalAtom space d body Atom.undefinedType seed (mid, mb) →
      EvalAtom space d mid Atom.undefinedType mb
        (.expression [.symbol "return", ret], rb) →
      EvalAtomStablyReaches space d
        (.expression [.symbol "function", body])
        Atom.undefinedType seed
        (ret, rb)

/-- Applying bindings to a `(return ...)` wrapper preserves the head symbol
and substitutes only inside the payload.  This makes the `function/return`
boundary spendable without pretending the inner payload saw the same fuel as a
bare `applyDefault`. -/
private theorem applyDefault_return_shape
    (b : Bindings) (payload : Atom) :
    b.applyDefault (.expression [.symbol "return", payload]) =
      .expression [.symbol "return", b.apply payload 99] := by
  rfl

/-- Honest contextual follow-through for the `function` loop: if the body
first evaluates to an intermediate atom and that atom then evaluates to a
`(return ...)`, the surrounding `function` continues from that chosen branch.
This keeps branch selection and branch continuation separate, exactly where
the runtime contract places them. -/
theorem evalAtom_realizes_function_follow
    {space : Space} {d : GroundedDispatch}
    (hReal : SwitchInternalGroundRealization space d)
    {body mid ret : Atom} {mb rb : Bindings}
    (h_body :
      EvalAtom space d body Atom.undefinedType Bindings.empty (mid, mb))
    (h_mid :
      EvalAtom space d mid Atom.undefinedType mb
        (.expression [.symbol "return", ret], rb)) :
    EvalAtom space d
      (.expression [.symbol "function", body])
      Atom.undefinedType Bindings.empty
      (ret, rb) := by
  exact evalAtomStablyReaches_to_EvalAtom space d
    (.expression [.symbol "function", body])
    Atom.undefinedType Bindings.empty
    (ret, rb)
    (hReal.functionContinueStable h_body h_mid)

/-- Seeded companion to `evalAtom_realizes_function_follow`: the `function`
loop continues from an intermediate chosen branch under arbitrary incoming
bindings, rather than only under the empty seed. -/
theorem evalAtom_realizes_function_follow_seeded
    {space : Space} {d : GroundedDispatch}
    (hReal : SwitchInternalGroundSeededRealization space d)
    {seed : Bindings} {body mid ret : Atom} {mb rb : Bindings}
    (h_body :
      EvalAtom space d body Atom.undefinedType seed (mid, mb))
    (h_mid :
      EvalAtom space d mid Atom.undefinedType mb
        (.expression [.symbol "return", ret], rb)) :
    EvalAtom space d
      (.expression [.symbol "function", body])
      Atom.undefinedType seed
      (ret, rb) := by
  exact evalAtomStablyReaches_to_EvalAtom space d
    (.expression [.symbol "function", body])
    Atom.undefinedType seed
    (ret, rb)
    (hReal.functionContinueStableSeeded h_body h_mid)

/-- Head-hit branch of the *function body* used by `switch-internal`.
This spends the explicit `function/return` boundary on top of the already
landed `unify` realization, keeping the one-step fuel skew visible in the
result atom. -/
theorem evalAtom_realizes_switch_internal_body_match_ground
    {space : Space} {d : GroundedDispatch}
    (hReal : SwitchInternalGroundRealization space d)
    {scrut pt template : Atom} {tail : List Atom} {mb : Bindings} {fuel : Nat}
    (hground : GroundAtom scrut)
    (hmatch : simpleMatch pt scrut Bindings.empty fuel = some mb) :
    EvalAtom space d
      (switchInternalBody scrut pt template tail)
      Atom.undefinedType Bindings.empty
      (mb.apply template 99, mb) := by
  have h_unify :
      EvalAtom space d
        (switchInternalUnify scrut pt template tail)
        Atom.undefinedType Bindings.empty
        (mb.applyDefault (.expression [.symbol "return", template]), mb) := by
    simpa [switchInternalUnify, switchInternalElseChain, switchMinimalExpr] using
      evalAtom_realizes_switch_internal_head_match_ground
        hReal.toUnifyGroundBranchRealization hground hmatch
  have h_unify_ret :
      EvalAtom space d
        (switchInternalUnify scrut pt template tail)
        Atom.undefinedType Bindings.empty
        (.expression [.symbol "return", mb.apply template 99], mb) := by
    simpa [applyDefault_return_shape] using h_unify
  exact evalAtomStablyReaches_to_EvalAtom space d
    (switchInternalBody scrut pt template tail)
    Atom.undefinedType Bindings.empty
    (mb.apply template 99, mb)
    (hReal.functionReturnStable h_unify_ret)

/-- Recursive else-chain core used by the head-miss branch of
`switch-internal`, parametrized by the official evaluation of the tail
`switch-minimal`.  This is the exact `chain` layer the later recursive
branch-selection proof will feed into the function shell. -/
theorem evalAtom_realizes_switch_internal_else_chain_of_tail
    {space : Space} {d : GroundedDispatch}
    (hReal : SwitchInternalGroundRealization space d)
    {scrut : Atom} {tail : List Atom}
    {ret : Atom} {rb : Bindings}
    (h_tail :
      EvalAtom space d
        (switchMinimalExpr scrut tail)
        Atom.undefinedType Bindings.empty
        (ret, rb))
    (h_ret_nonempty : ret ≠ Atom.empty) :
    EvalAtom space d
      (switchInternalElseChain scrut tail)
      Atom.undefinedType Bindings.empty
      (.expression [.symbol "return",
          (Bindings.assign rb "ret" ret).apply (.var "ret") 99],
        Bindings.assign rb "ret" ret) := by
  have h_eval_switch :
      EvalAtom space d
        (.expression [.symbol "eval", switchMinimalExpr scrut tail])
        Atom.undefinedType Bindings.empty
        (ret, rb) :=
    evalAtomStablyReaches_to_EvalAtom space d
      (.expression [.symbol "eval", switchMinimalExpr scrut tail])
      Atom.undefinedType Bindings.empty
      (ret, rb)
      (hReal.evalStable h_tail)
  have h_chain :
      EvalAtom space d
        (switchInternalElseChain scrut tail)
        Atom.undefinedType Bindings.empty
        ((Bindings.assign rb "ret" ret).applyDefault
          (.expression [.symbol "return", .var "ret"]),
          Bindings.assign rb "ret" ret) :=
    evalAtomStablyReaches_to_EvalAtom space d
      (switchInternalElseChain scrut tail)
      Atom.undefinedType Bindings.empty
      ((Bindings.assign rb "ret" ret).applyDefault
        (.expression [.symbol "return", .var "ret"]),
        Bindings.assign rb "ret" ret)
      (hReal.chainStable h_eval_switch h_ret_nonempty)
  have h_chain_ret :
      EvalAtom space d
        (switchInternalElseChain scrut tail)
        Atom.undefinedType Bindings.empty
        (.expression [.symbol "return",
            (Bindings.assign rb "ret" ret).apply (.var "ret") 99],
          Bindings.assign rb "ret" ret) := by
    simpa [applyDefault_return_shape] using h_chain
  exact h_chain_ret

/-- Head-miss branch of the *function body* used by `switch-internal`,
parametrized by the official evaluation of the tail `switch-minimal`.
This is the honest recursive miss-side companion to
`evalAtom_realizes_switch_internal_body_match_ground`: the `unify` miss does
not stop the computation, it follows its else branch through the recursive
`chain`, and then the surrounding `function` consumes the resulting
`(return ...)`. -/
theorem evalAtom_realizes_switch_internal_body_no_match_of_tail
    {space : Space} {d : GroundedDispatch}
    (hReal : SwitchInternalGroundRealization space d)
    {scrut pt template : Atom} {tail : List Atom}
    {ret : Atom} {rb : Bindings} {fuel : Nat}
    (hground : GroundAtom scrut)
    (hmatch : simpleMatch pt scrut Bindings.empty fuel = none)
    (h_tail :
      EvalAtom space d
        (switchMinimalExpr scrut tail)
        Atom.undefinedType Bindings.empty
        (ret, rb))
    (h_ret_nonempty : ret ≠ Atom.empty) :
    EvalAtom space d
      (switchInternalBody scrut pt template tail)
      Atom.undefinedType Bindings.empty
      ((Bindings.assign rb "ret" ret).apply (.var "ret") 99,
        Bindings.assign rb "ret" ret) := by
  have h_else :
      EvalAtom space d
        (switchInternalElseChain scrut tail)
        Atom.undefinedType Bindings.empty
        (.expression [.symbol "return",
            (Bindings.assign rb "ret" ret).apply (.var "ret") 99],
          Bindings.assign rb "ret" ret) := by
    exact evalAtom_realizes_switch_internal_else_chain_of_tail
      hReal h_tail h_ret_nonempty
  have h_unify_raw :
      EvalAtom space d
        (switchInternalUnify scrut pt template tail)
        Atom.undefinedType Bindings.empty
        (switchInternalElseChain scrut tail, Bindings.empty) := by
    exact evalAtom_realizes_switch_internal_head_no_match_ground
      hReal.toUnifyGroundBranchRealization hground hmatch
  exact evalAtom_realizes_function_follow hReal h_unify_raw h_else

/-- Seeded head-hit branch of the `switch-internal` function body.  This is
the equation-helper companion to
`evalAtom_realizes_switch_internal_body_match_ground`: when an outer query has
already contributed incoming bindings, the seeded `unify_match` result still
feeds the surrounding `function` body to the same returned branch payload. -/
theorem evalAtom_realizes_switch_internal_body_match_ground_seeded
    {space : Space} {d : GroundedDispatch}
    (hReal : SwitchInternalGroundSeededRealization space d)
    {seed mb merged : Bindings}
    {scrut pt template : Atom} {tail : List Atom} {fuel : Nat}
    (hground : GroundAtom scrut)
    (hmatch : mb ∈ matchAtoms scrut pt fuel)
    (hmerge : merged ∈ mergeBindings mb seed fuel)
    (h_no_loop : merged.hasLoop = false) :
    EvalAtom space d
      (switchInternalBody scrut pt template tail)
      Atom.undefinedType seed
      (merged.apply template 99, merged) := by
  have h_unify :
      EvalAtom space d
        (switchInternalUnify scrut pt template tail)
        Atom.undefinedType seed
        (merged.applyDefault (.expression [.symbol "return", template]), merged) := by
    simpa [switchInternalUnify, switchInternalElseChain] using
      evalAtom_realizes_unify_match_ground_seeded
        hReal.toUnifyGroundSeededBranchRealization
        hground hmatch hmerge h_no_loop
  have h_unify_ret :
      EvalAtom space d
        (switchInternalUnify scrut pt template tail)
        Atom.undefinedType seed
        (.expression [.symbol "return", merged.apply template 99], merged) := by
    simpa [applyDefault_return_shape] using h_unify
  exact evalAtomStablyReaches_to_EvalAtom space d
    (switchInternalBody scrut pt template tail)
    Atom.undefinedType seed
    (merged.apply template 99, merged)
    (hReal.functionReturnStableSeeded h_unify_ret)

/-- Seeded recursive else-chain core used by the head-miss branch of
`switch-internal`: if the tail `switch-minimal` already has an official
evaluation under the same incoming query bindings, the seeded `eval/chain`
helper path realizes the corresponding `(return ...)` body result. -/
theorem evalAtom_realizes_switch_internal_else_chain_of_tail_seeded
    {space : Space} {d : GroundedDispatch}
    (hReal : SwitchInternalGroundSeededRealization space d)
    {seed : Bindings} {scrut : Atom} {tail : List Atom}
    {ret : Atom} {rb : Bindings}
    (h_tail :
      EvalAtom space d
        (switchMinimalExpr scrut tail)
        Atom.undefinedType seed
        (ret, rb))
    (h_ret_nonempty : ret ≠ Atom.empty) :
    EvalAtom space d
      (switchInternalElseChain scrut tail)
      Atom.undefinedType seed
      (.expression [.symbol "return",
          (Bindings.assign rb "ret" ret).apply (.var "ret") 99],
        Bindings.assign rb "ret" ret) := by
  have h_eval_switch :
      EvalAtom space d
        (.expression [.symbol "eval", switchMinimalExpr scrut tail])
        Atom.undefinedType seed
        (ret, rb) :=
    evalAtomStablyReaches_to_EvalAtom space d
      (.expression [.symbol "eval", switchMinimalExpr scrut tail])
      Atom.undefinedType seed
      (ret, rb)
      (hReal.evalStableSeeded h_tail)
  have h_chain :
      EvalAtom space d
        (switchInternalElseChain scrut tail)
        Atom.undefinedType seed
        ((Bindings.assign rb "ret" ret).applyDefault
          (.expression [.symbol "return", .var "ret"]),
          Bindings.assign rb "ret" ret) :=
    evalAtomStablyReaches_to_EvalAtom space d
      (switchInternalElseChain scrut tail)
      Atom.undefinedType seed
      ((Bindings.assign rb "ret" ret).applyDefault
        (.expression [.symbol "return", .var "ret"]),
        Bindings.assign rb "ret" ret)
      (hReal.chainStableSeeded h_eval_switch h_ret_nonempty)
  have h_chain_ret :
      EvalAtom space d
        (switchInternalElseChain scrut tail)
        Atom.undefinedType seed
        (.expression [.symbol "return",
            (Bindings.assign rb "ret" ret).apply (.var "ret") 99],
          Bindings.assign rb "ret" ret) := by
    simpa [applyDefault_return_shape] using h_chain
  exact h_chain_ret

/-- Seeded head-miss branch of the `switch-internal` function body.  This is
the equation-helper companion to
`evalAtom_realizes_switch_internal_body_no_match_of_tail`: the seeded
`unify_no_match` branch follows its recursive else-chain under the same
incoming query bindings, then the surrounding `function` consumes the
resulting `(return ...)`. -/
theorem evalAtom_realizes_switch_internal_body_no_match_of_tail_seeded
    {space : Space} {d : GroundedDispatch}
    (hReal : SwitchInternalGroundSeededRealization space d)
    {seed : Bindings} {scrut pt template : Atom} {tail : List Atom}
    {ret : Atom} {rb : Bindings} {fuel : Nat}
    (hground : GroundAtom scrut)
    (hmatch : matchAtoms scrut pt fuel = [])
    (h_tail :
      EvalAtom space d
        (switchMinimalExpr scrut tail)
        Atom.undefinedType seed
        (ret, rb))
    (h_ret_nonempty : ret ≠ Atom.empty) :
    EvalAtom space d
      (switchInternalBody scrut pt template tail)
      Atom.undefinedType seed
      ((Bindings.assign rb "ret" ret).apply (.var "ret") 99,
        Bindings.assign rb "ret" ret) := by
  have h_else :
      EvalAtom space d
        (switchInternalElseChain scrut tail)
        Atom.undefinedType seed
        (.expression [.symbol "return",
            (Bindings.assign rb "ret" ret).apply (.var "ret") 99],
          Bindings.assign rb "ret" ret) := by
    exact evalAtom_realizes_switch_internal_else_chain_of_tail_seeded
      hReal h_tail h_ret_nonempty
  have h_unify_raw :
      EvalAtom space d
        (switchInternalUnify scrut pt template tail)
        Atom.undefinedType seed
        (switchInternalElseChain scrut tail, seed) := by
    simpa [switchInternalUnify, switchInternalElseChain] using
      evalAtom_realizes_unify_no_match_ground_seeded
        hReal.toUnifyGroundSeededBranchRealization hground hmatch
  exact evalAtom_realizes_function_follow_seeded hReal h_unify_raw h_else

/-- Alpha-renamed seeded head-hit branch of the `switch-internal` function
body.  This is the exact equation-helper form needed after
`queryEquations` freshens the local `ret` binder. -/
theorem evalAtom_realizes_switch_internal_body_match_ground_seeded_var
    {space : Space} {d : GroundedDispatch}
    (hReal : SwitchInternalGroundSeededRealization space d)
    {retVar : String} {seed mb merged : Bindings}
    {scrut pt template : Atom} {tail : List Atom} {fuel : Nat}
    (hground : GroundAtom scrut)
    (hmatch : mb ∈ matchAtoms scrut pt fuel)
    (hmerge : merged ∈ mergeBindings mb seed fuel)
    (h_no_loop : merged.hasLoop = false) :
    EvalAtom space d
      (switchInternalBodyVar retVar scrut pt template tail)
      Atom.undefinedType seed
      (merged.apply template 99, merged) := by
  have h_unify :
      EvalAtom space d
        (switchInternalUnifyVar retVar scrut pt template tail)
        Atom.undefinedType seed
        (merged.applyDefault (.expression [.symbol "return", template]), merged) := by
    simpa [switchInternalUnifyVar, switchInternalElseChainVar] using
      evalAtom_realizes_unify_match_ground_seeded
        hReal.toUnifyGroundSeededBranchRealization
        hground hmatch hmerge h_no_loop
  have h_unify_ret :
      EvalAtom space d
        (switchInternalUnifyVar retVar scrut pt template tail)
        Atom.undefinedType seed
        (.expression [.symbol "return", merged.apply template 99], merged) := by
    simpa [applyDefault_return_shape] using h_unify
  exact evalAtomStablyReaches_to_EvalAtom space d
    (switchInternalBodyVar retVar scrut pt template tail)
    Atom.undefinedType seed
    (merged.apply template 99, merged)
    (hReal.functionReturnStableSeeded h_unify_ret)

/-- Alpha-renamed seeded recursive else-chain core used by the head-miss
branch of `switch-internal`.  This is the exact equation-helper form needed
after `queryEquations` freshens the local `ret` binder. -/
theorem evalAtom_realizes_switch_internal_else_chain_of_tail_seeded_var
    {space : Space} {d : GroundedDispatch}
    (hReal : SwitchInternalGroundSeededRealization space d)
    {retVar : String} {seed : Bindings} {scrut : Atom} {tail : List Atom}
    {ret : Atom} {rb : Bindings}
    (h_tail :
      EvalAtom space d
        (switchMinimalExpr scrut tail)
        Atom.undefinedType seed
        (ret, rb))
    (h_ret_nonempty : ret ≠ Atom.empty) :
    EvalAtom space d
      (switchInternalElseChainVar retVar scrut tail)
      Atom.undefinedType seed
      (.expression [.symbol "return",
          (Bindings.assign rb retVar ret).apply (.var retVar) 99],
        Bindings.assign rb retVar ret) := by
  have h_eval_switch :
      EvalAtom space d
        (.expression [.symbol "eval", switchMinimalExpr scrut tail])
        Atom.undefinedType seed
        (ret, rb) :=
    evalAtomStablyReaches_to_EvalAtom space d
      (.expression [.symbol "eval", switchMinimalExpr scrut tail])
      Atom.undefinedType seed
      (ret, rb)
      (hReal.evalStableSeeded h_tail)
  have h_chain :
      EvalAtom space d
        (switchInternalElseChainVar retVar scrut tail)
        Atom.undefinedType seed
        ((Bindings.assign rb retVar ret).applyDefault
          (.expression [.symbol "return", .var retVar]),
          Bindings.assign rb retVar ret) :=
    evalAtomStablyReaches_to_EvalAtom space d
      (switchInternalElseChainVar retVar scrut tail)
      Atom.undefinedType seed
      ((Bindings.assign rb retVar ret).applyDefault
        (.expression [.symbol "return", .var retVar]),
        Bindings.assign rb retVar ret)
      (hReal.chainStableSeeded h_eval_switch h_ret_nonempty)
  have h_chain_ret :
      EvalAtom space d
        (switchInternalElseChainVar retVar scrut tail)
        Atom.undefinedType seed
        (.expression [.symbol "return",
            (Bindings.assign rb retVar ret).apply (.var retVar) 99],
          Bindings.assign rb retVar ret) := by
    simpa [applyDefault_return_shape] using h_chain
  exact h_chain_ret

/-- Alpha-renamed seeded head-miss branch of the `switch-internal` function
body.  This is the exact equation-helper form needed after
`queryEquations` freshens the local `ret` binder. -/
theorem evalAtom_realizes_switch_internal_body_no_match_of_tail_seeded_var
    {space : Space} {d : GroundedDispatch}
    (hReal : SwitchInternalGroundSeededRealization space d)
    {retVar : String} {seed : Bindings}
    {scrut pt template : Atom} {tail : List Atom}
    {ret : Atom} {rb : Bindings} {fuel : Nat}
    (hground : GroundAtom scrut)
    (hmatch : matchAtoms scrut pt fuel = [])
    (h_tail :
      EvalAtom space d
        (switchMinimalExpr scrut tail)
        Atom.undefinedType seed
        (ret, rb))
    (h_ret_nonempty : ret ≠ Atom.empty) :
    EvalAtom space d
      (switchInternalBodyVar retVar scrut pt template tail)
      Atom.undefinedType seed
      ((Bindings.assign rb retVar ret).apply (.var retVar) 99,
        Bindings.assign rb retVar ret) := by
  have h_else :
      EvalAtom space d
        (switchInternalElseChainVar retVar scrut tail)
        Atom.undefinedType seed
        (.expression [.symbol "return",
            (Bindings.assign rb retVar ret).apply (.var retVar) 99],
          Bindings.assign rb retVar ret) := by
    exact evalAtom_realizes_switch_internal_else_chain_of_tail_seeded_var
      hReal h_tail h_ret_nonempty
  have h_unify_raw :
      EvalAtom space d
        (switchInternalUnifyVar retVar scrut pt template tail)
        Atom.undefinedType seed
        (switchInternalElseChainVar retVar scrut tail, seed) := by
    simpa [switchInternalUnifyVar, switchInternalElseChainVar] using
      evalAtom_realizes_unify_no_match_ground_seeded
        hReal.toUnifyGroundSeededBranchRealization hground hmatch
  exact evalAtom_realizes_function_follow_seeded hReal h_unify_raw h_else

/-- Honest outer shell fact for the current evaluator route of
`switch-internal`: once the stdlib equation has been selected and freshened,
an Atom-typed equation body is returned *raw* at the shell boundary.

This is not the final `switch-internal` certification theorem we eventually
want for `switch-minimal`; it records the current evaluator behavior exactly.
The recursive body-follow-through theorems above therefore need a more direct
surface/control route than this typed equation shell, because the shell itself
stops at the applied body expression when the return type is `Atom`. -/
theorem evalAtom_absorbs_switchInternal_raw_body_shell
    {space : Space} {d : GroundedDispatch}
    {scrut headBranch rhs body : Atom} {tail : List Atom}
    {qb : Bindings}
    {succs : List Bindings}
    {fuelShell fuelQuery : Nat}
    (h_types : getAtomTypes space (.symbol "switch-internal") = [switchBinaryFunctionType])
    (h_check : checkIfFunctionTypeIsApplicable
      (switchInternalExpr scrut headBranch tail)
      switchBinaryFunctionType Atom.undefinedType
      space Bindings.empty fuelShell = .inr succs)
    (h_check_b : Bindings.empty ∈ succs)
    (h_not_exec : d.isExecutable (.symbol "switch-internal") = false)
    (h_scrut_nerr : scrut ≠ Atom.symbol "Error")
    (h_head_nerr : headBranch ≠ Atom.symbol "Error")
    (h_query : (rhs, qb) ∈ queryEquations space
      (switchInternalExpr scrut headBranch tail) fuelQuery)
    (h_query_merge : qb ∈ mergeBindings qb Bindings.empty fuelQuery)
    (h_query_no_loop : qb.hasLoop = false)
    (h_rhs : qb.apply rhs fuelQuery = body)
    (h_body_ok : isEmptyOrError body = false) :
    EvalAtom space d
      (switchInternalExpr scrut headBranch tail)
      Atom.undefinedType Bindings.empty
      (body, qb) := by
  have h_interp :
      InterpretFunction space d (switchInternalExpr scrut headBranch tail)
        switchBinaryFunctionType Atom.undefinedType Bindings.empty
        (switchInternalExpr scrut headBranch tail, Bindings.empty) :=
    interpretFunction_switchInternal_self h_types h_scrut_nerr h_head_nerr
  have h_eval_rhs :
      EvalAtom space d (qb.apply rhs fuelQuery)
        Atom.atomType qb
        (body, qb) := by
    rw [h_rhs]
    exact EvalAtom.type_pass body Atom.atomType qb h_body_ok (by left; rfl)
  have h_call :
      MettaCall space d (switchInternalExpr scrut headBranch tail)
        Atom.atomType Bindings.empty
        (body, qb) :=
    mettaCall_absorbs_switchInternal_equation
      h_not_exec h_query h_query_merge h_query_no_loop h_eval_rhs
  have h_op_type : switchBinaryFunctionType ∈ getAtomTypes space (.symbol "switch-internal") := by
    rw [h_types]
    simp
  have h_body_not_error : isErrorAtom body = false := by
    have h_ok := h_body_ok
    simp [isEmptyOrError, Bool.or_eq_false_iff] at h_ok
    exact h_ok.2
  exact evalAtom_absorbs_switchInternal_shell
    h_op_type h_check h_check_b h_interp h_call h_body_not_error

end Mettapedia.Languages.MeTTa.HE
