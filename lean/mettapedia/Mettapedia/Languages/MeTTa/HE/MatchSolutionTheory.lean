import Mettapedia.Languages.MeTTa.HE.LeaTTaBindingTransport

/-!
# HE matcher outputs present exactly their input equation

`DeclMatchSpec`/`DeclMergeSpec` characterize the executable matcher
syntactically (which derivations exist).  This file adds the extensional
account: every binding set returned by the executable `matchAtoms` presents,
through its value and equality constraints, **exactly the solution set of the
input atom equation**, and the merge/add helpers present exactly constraint
conjunction.  Representation details — relation order, equality orientation,
class chronology, the particular reconciliation route taken — are invisible at
this layer.

Main results:
* `matchAtoms_solution_iff` — executable matcher outputs present the equation.
* `mergeBindings_solution_iff` — merge presents solution intersection.
* `addVarBinding_solution_iff` / `addVarEquality_solution_iff` — the
  incremental helpers present exactly one added constraint.
* `heMatch_leaMatch_solutionTheoryEquiv` — an executable HE witness and a
  repaired-LeaTTa witness for one translated equation always have equal
  binding solution theories: the semantic half of the cross-engine congruence,
  with no comparison of binding representations.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaBridge

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-! ## Satisfaction: structural helpers -/

/-- The empty binding record constrains nothing. -/
theorem hesat_empty (μ : String → Metta.Atom) :
    HEBindingSatisfied μ Bindings.empty :=
  ⟨fun _ _ h => by simp [Bindings.empty] at h,
   fun _ _ h => by simp [Bindings.empty] at h⟩

@[simp] theorem hesat_empty_iff (μ : String → Metta.Atom) :
    HEBindingSatisfied μ Bindings.empty ↔ True :=
  iff_true_intro (hesat_empty μ)

private theorem eq_of_walk {μ : String → Metta.Atom} {b : Bindings}
    (hsat : ∀ x y, (x, y) ∈ b.equalities → μ x = μ y) :
    ∀ {x y : String},
      (EqualityClosure.edgeGraph b.equalities).Walk x y → μ x = μ y
  | _, _, .nil => rfl
  | _, _, .cons hadj tail => by
      rcases (EqualityClosure.edgeGraph_adj_iff.mp hadj).2 with hedge | hedge
      · exact (hsat _ _ hedge).trans (eq_of_walk hsat tail)
      · exact (hsat _ _ hedge).symm.trans (eq_of_walk hsat tail)

/-- A satisfying valuation is constant on every explicit equality class. -/
theorem HEBindingSatisfied.eq_of_mem_eqClass {μ : String → Metta.Atom}
    {b : Bindings} (hsat : HEBindingSatisfied μ b) {v w : String}
    (hmem : w ∈ b.eqClass v) : μ v = μ w :=
  (EqualityClosure.mem_eqClass_iff_reachable.mp hmem).elim
    fun walk => eq_of_walk hsat.2 walk

private theorem mem_of_lookup_eq_some {k : String} {a : Atom} :
    ∀ {l : List (String × Atom)}, l.lookup k = some a → (k, a) ∈ l
  | [], h => by simp [List.lookup] at h
  | (k', a') :: l, h => by
      rw [List.lookup] at h
      cases hk : (k == k') with
      | false =>
          rw [hk] at h
          exact List.mem_cons_of_mem _ (mem_of_lookup_eq_some h)
      | true =>
          rw [hk] at h
          have hkk : k = k' := eq_of_beq hk
          have haa : a' = a := Option.some.inj h
          subst hkk
          subst haa
          exact List.mem_cons_self ..

/-- A satisfying valuation sends a variable to (the solution image of) every
value carried anywhere in its equality class. -/
theorem HEBindingSatisfied.eq_applyClassSolution_of_mem_classValues
    {μ : String → Metta.Atom} {b : Bindings}
    (hsat : HEBindingSatisfied μ b) {v : String} {value : Atom}
    (hmem : value ∈ b.classValues v) :
    μ v = applyClassSolution μ (toLeaTTaAtom value) := by
  unfold Bindings.classValues at hmem
  rcases List.mem_filterMap.mp hmem with ⟨w, hw, hlookup⟩
  have hclass : w ∈ b.eqClass v :=
    EqualityClosure.mem_eqClassOrdered_iff.mp hw
  have hassign : (w, value) ∈ b.assignments :=
    mem_of_lookup_eq_some hlookup
  exact (hsat.eq_of_mem_eqClass hclass).trans (hsat.1 w value hassign)

private theorem isBound_eq_false_of_classValues_nil {b : Bindings} {v : String}
    (h : b.classValues v = []) : b.isBound v = false := by
  by_contra habs
  have hbound : b.isBound v = true := by simpa using habs
  rw [Bindings.isBound, Option.isSome_iff_exists] at hbound
  rcases hbound with ⟨a, ha⟩
  have hself : v ∈ b.eqClassOrdered v :=
    EqualityClosure.mem_eqClassOrdered_iff.mpr
      (EqualityClosure.mem_eqClass_iff_reachable.mpr .rfl)
  have hmem : a ∈ b.classValues v := by
    unfold Bindings.classValues
    exact List.mem_filterMap.mpr ⟨v, hself, ha⟩
  rw [h] at hmem
  simp at hmem

private theorem hesat_assign_of_not_isBound {b : Bindings} {v : String}
    {val : Atom} (hnb : b.isBound v = false) (μ : String → Metta.Atom) :
    HEBindingSatisfied μ (b.assign v val) ↔
      (HEBindingSatisfied μ b ∧
        μ v = applyClassSolution μ (toLeaTTaAtom val)) := by
  have hassign : b.assign v val =
      ⟨b.assignments ++ [(v, val)], b.equalities⟩ := by
    simp [Bindings.assign, hnb]
  rw [hassign]
  constructor
  · intro hsat
    exact ⟨⟨fun x value hx => hsat.1 x value (List.mem_append_left _ hx),
        hsat.2⟩,
      hsat.1 v val (List.mem_append_right _ (by simp))⟩
  · rintro ⟨hsat, hval⟩
    refine ⟨fun x value hx => ?_, hsat.2⟩
    rcases List.mem_append.mp hx with hx | hx
    · exact hsat.1 x value hx
    · simp only [List.mem_singleton, Prod.mk.injEq] at hx
      rcases hx with ⟨rfl, rfl⟩
      exact hval

private theorem hesat_addEquality {b : Bindings} {a c : String}
    (μ : String → Metta.Atom) :
    HEBindingSatisfied μ (b.addEquality a c) ↔
      (HEBindingSatisfied μ b ∧ μ a = μ c) := by
  have heq : b.addEquality a c =
      ⟨b.assignments, b.equalities ++ [(a, c)]⟩ := rfl
  rw [heq]
  constructor
  · intro hsat
    exact ⟨⟨hsat.1, fun x y hx => hsat.2 x y (List.mem_append_left _ hx)⟩,
      hsat.2 a c (List.mem_append_right _ (by simp))⟩
  · rintro ⟨hsat, hac⟩
    refine ⟨hsat.1, fun x y hx => ?_⟩
    rcases List.mem_append.mp hx with hx | hx
    · exact hsat.2 x y hx
    · simp only [List.mem_singleton, Prod.mk.injEq] at hx
      rcases hx with ⟨rfl, rfl⟩
      exact hac

/-! ## The translated equation, by constructor -/

@[simp] private theorem applyToLea_symbol (μ : String → Metta.Atom)
    (s : String) :
    applyClassSolution μ (toLeaTTaAtom (.symbol s)) = .sym s := by
  simp [toLeaTTaAtom, applyClassSolution]

@[simp] private theorem applyToLea_var (μ : String → Metta.Atom)
    (v : String) :
    applyClassSolution μ (toLeaTTaAtom (.var v)) = μ v := by
  simp [toLeaTTaAtom, applyClassSolution]

@[simp] private theorem applyToLea_grounded (μ : String → Metta.Atom)
    (g : GroundedValue) :
    applyClassSolution μ (toLeaTTaAtom (.grounded g)) =
      .gnd (toLeaTTaGround g) := by
  simp [toLeaTTaAtom, applyClassSolution]

@[simp] private theorem applyToLea_expression (μ : String → Metta.Atom)
    (es : List Atom) :
    applyClassSolution μ (toLeaTTaAtom (.expression es)) =
      .expr ((toLeaTTaAtoms es).map (applyClassSolution μ)) := by
  simp [toLeaTTaAtom, applyClassSolution]

private theorem toLeaTTaAtoms_eq_map (l : List Atom) :
    toLeaTTaAtoms l = l.map toLeaTTaAtom := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

private theorem toLeaTTaAtoms_replicate (k : Nat) (a : Atom) :
    toLeaTTaAtoms (List.replicate k a) =
      List.replicate k (toLeaTTaAtom a) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, ih]

/-- A constant list agrees with a mapped list exactly when every image is the
constant.  This is the solution reading of the class-wide reconciliation
worklists built by `addVarBinding`/`addVarEquality`. -/
private theorem replicate_eq_map_iff (μ : String → Metta.Atom) (k : Atom) :
    ∀ l : List Atom,
      (List.replicate l.length (applyClassSolution μ (toLeaTTaAtom k)) =
        List.map (applyClassSolution μ ∘ toLeaTTaAtom) l) ↔
      ∀ o ∈ l, applyClassSolution μ (toLeaTTaAtom o) =
        applyClassSolution μ (toLeaTTaAtom k)
  | [] => by simp
  | o :: l => by
      simp only [List.length_cons, List.replicate_succ, List.map_cons,
        List.cons.injEq, List.forall_mem_cons, Function.comp]
      rw [replicate_eq_map_iff μ k l]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1.symm, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1.symm, h2⟩

/-! ## Fold plumbing for `mergeBindings` -/

private theorem stepFold_solution {β : Type} {Con : β → (String → Metta.Atom) → Prop}
    {f : Bindings → β → List Bindings}
    (hstep : ∀ {bb : Bindings} {p : β} {out : Bindings}, out ∈ f bb p →
      ∀ μ : String → Metta.Atom,
        (HEBindingSatisfied μ out ↔ (HEBindingSatisfied μ bb ∧ Con p μ))) :
    ∀ (entries : List β) (init : List Bindings) (out : Bindings),
      out ∈ entries.foldl (fun acc p => acc.flatMap fun bb => f bb p) init →
      ∃ seed ∈ init, ∀ μ : String → Metta.Atom,
        (HEBindingSatisfied μ out ↔
          (HEBindingSatisfied μ seed ∧ ∀ p ∈ entries, Con p μ)) := by
  intro entries
  induction entries with
  | nil =>
      intro init out h
      exact ⟨out, by simpa using h, fun μ => by simp⟩
  | cons p entries ih =>
      intro init out h
      rw [List.foldl_cons] at h
      obtain ⟨seed1, hseed1, hiff⟩ := ih _ _ h
      obtain ⟨seed0, hseed0, hstep1⟩ := List.mem_flatMap.mp hseed1
      refine ⟨seed0, hseed0, fun μ => ?_⟩
      rw [hiff μ, hstep hstep1 μ, List.forall_mem_cons]
      tauto

/-! ## The fuel-indexed solution pack

The five executable functions recurse mutually on one strictly decreasing
fuel, so their solution characterizations are proven by one simultaneous
induction on fuel — mirroring `DeclMatchSpec.matchSoundPair`. -/

private theorem solutionPack :
    ∀ fuel : Nat,
      (∀ {l r : Atom} {b : Bindings}, b ∈ matchAtoms l r fuel →
        ∀ μ : String → Metta.Atom,
          (HEBindingSatisfied μ b ↔
            applyClassSolution μ (toLeaTTaAtom l) =
              applyClassSolution μ (toLeaTTaAtom r))) ∧
      (∀ {ls rs : List Atom} {acc : List Bindings} {out : Bindings},
        out ∈ matchAtomsList ls rs acc fuel →
        ∃ seed ∈ acc, ∀ μ : String → Metta.Atom,
          (HEBindingSatisfied μ out ↔
            (HEBindingSatisfied μ seed ∧
              (toLeaTTaAtoms ls).map (applyClassSolution μ) =
                (toLeaTTaAtoms rs).map (applyClassSolution μ)))) ∧
      (∀ {left right out : Bindings}, out ∈ mergeBindings left right fuel →
        ∀ μ : String → Metta.Atom,
          (HEBindingSatisfied μ out ↔
            (HEBindingSatisfied μ left ∧ HEBindingSatisfied μ right))) ∧
      (∀ {b : Bindings} {v : String} {val : Atom} {out : Bindings},
        out ∈ addVarBinding b v val fuel →
        ∀ μ : String → Metta.Atom,
          (HEBindingSatisfied μ out ↔
            (HEBindingSatisfied μ b ∧
              μ v = applyClassSolution μ (toLeaTTaAtom val)))) ∧
      (∀ {b : Bindings} {a c : String} {out : Bindings},
        out ∈ addVarEquality b a c fuel →
        ∀ μ : String → Metta.Atom,
          (HEBindingSatisfied μ out ↔
            (HEBindingSatisfied μ b ∧ μ a = μ c)))
  | 0 => by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro l r b h
        simp [matchAtoms] at h
      · intro ls rs acc out h
        simp [matchAtomsList] at h
      · intro left right out h
        simp [mergeBindings] at h
      · intro b v val out h
        simp [addVarBinding] at h
      · intro b a c out h
        simp [addVarEquality] at h
  | fuel + 1 => by
      obtain ⟨ihA, ihB, ihC, ihD, ihE⟩ := solutionPack fuel
      -- The merge/add layer first: it only consumes the IH at `fuel`.
      have hD : ∀ {b : Bindings} {v : String} {val : Atom} {out : Bindings},
          out ∈ addVarBinding b v val (fuel + 1) →
          ∀ μ : String → Metta.Atom,
            (HEBindingSatisfied μ out ↔
              (HEBindingSatisfied μ b ∧
                μ v = applyClassSolution μ (toLeaTTaAtom val))) := by
        intro b v val out h
        simp only [addVarBinding] at h
        split at h
        · -- fresh class: no value anywhere in the class
          next hcv =>
            simp only [List.mem_singleton] at h
            subst h
            exact hesat_assign_of_not_isBound
              (isBound_eq_false_of_classValues_nil hcv)
        · next first rest hcv =>
            split at h
            · -- consistent class values
              split at h
              · -- proposed value equals the carried value: no change
                next hbeq =>
                  simp only [List.mem_singleton] at h
                  subst h
                  have hval : first = val := eq_of_beq hbeq
                  subst hval
                  intro μ
                  constructor
                  · intro hs
                    exact ⟨hs, hs.eq_applyClassSolution_of_mem_classValues
                      (by rw [hcv]; exact List.mem_cons_self ..)⟩
                  · exact fun hs => hs.1
              · -- conflicting value: reconcile through the matcher, merge back
                next hbeq =>
                  obtain ⟨mb, hmb, hmrg⟩ := List.mem_flatMap.mp h
                  intro μ
                  rw [ihC hmrg μ, ihA hmb μ]
                  have hfirst : HEBindingSatisfied μ b →
                      μ v = applyClassSolution μ (toLeaTTaAtom first) :=
                    fun hs => hs.eq_applyClassSolution_of_mem_classValues
                      (by rw [hcv]; exact List.mem_cons_self ..)
                  constructor
                  · rintro ⟨hs, hfv⟩
                    exact ⟨hs, (hfirst hs).trans hfv⟩
                  · rintro ⟨hs, hvv⟩
                    exact ⟨hs, (hfirst hs).symm.trans hvv⟩
            · -- inconsistent class values: reconcile the whole class plus `val`
              next hcons =>
                obtain ⟨mb, hmb, hmrg⟩ := List.mem_flatMap.mp h
                obtain ⟨seed, hseed, hiffL⟩ := ihB hmb
                simp only [List.mem_singleton] at hseed
                subst hseed
                intro μ
                rw [ihC hmrg μ, hiffL μ]
                simp only [hesat_empty_iff, true_and, toLeaTTaAtoms_eq_map,
                  List.map_map, List.map_replicate, List.append_eq]
                rw [replicate_eq_map_iff μ first (rest ++ [val])]
                have hfirst : HEBindingSatisfied μ b →
                    μ v = applyClassSolution μ (toLeaTTaAtom first) :=
                  fun hs => hs.eq_applyClassSolution_of_mem_classValues
                    (by rw [hcv]; exact List.mem_cons_self ..)
                have hrest : HEBindingSatisfied μ b →
                    ∀ o ∈ rest, applyClassSolution μ (toLeaTTaAtom o) =
                      applyClassSolution μ (toLeaTTaAtom first) :=
                  fun hs o ho =>
                    (hs.eq_applyClassSolution_of_mem_classValues
                      (by rw [hcv]; exact List.mem_cons_of_mem _ ho)).symm.trans
                      (hfirst hs)
                constructor
                · rintro ⟨hs, hall⟩
                  have hval := hall val
                    (List.mem_append_right _ (by simp))
                  exact ⟨hs, (hfirst hs).trans hval.symm⟩
                · rintro ⟨hs, hvv⟩
                  refine ⟨hs, fun o ho => ?_⟩
                  rcases List.mem_append.mp ho with ho | ho
                  · exact hrest hs o ho
                  · simp only [List.mem_singleton] at ho
                    subst ho
                    exact ((hfirst hs).symm.trans hvv).symm
      have hE : ∀ {b : Bindings} {a c : String} {out : Bindings},
          out ∈ addVarEquality b a c (fuel + 1) →
          ∀ μ : String → Metta.Atom,
            (HEBindingSatisfied μ out ↔
              (HEBindingSatisfied μ b ∧ μ a = μ c)) := by
        intro b a c out h
        simp only [addVarEquality] at h
        split at h
        · -- joined class already consistent
          simp only [List.mem_singleton] at h
          subst h
          exact hesat_addEquality
        · next hcons =>
            split at h
            · -- no values at all: `valuesConsistent [] = true`, contradiction
              simp at h
            · -- exactly two conflicting values
              next first second hcv =>
                obtain ⟨mb, hmb, hmrg⟩ := List.mem_flatMap.mp h
                intro μ
                rw [ihC hmrg μ, ihA hmb μ, hesat_addEquality μ]
                have hpair : HEBindingSatisfied μ (b.addEquality a c) →
                    applyClassSolution μ (toLeaTTaAtom first) =
                      applyClassSolution μ (toLeaTTaAtom second) := by
                  intro hs
                  have h1 := hs.eq_applyClassSolution_of_mem_classValues
                    (v := a) (by rw [hcv]; exact List.mem_cons_self ..)
                  have h2 := hs.eq_applyClassSolution_of_mem_classValues
                    (v := a) (by
                      rw [hcv]
                      exact List.mem_cons_of_mem _ (List.mem_cons_self ..))
                  exact h1.symm.trans h2
                constructor
                · rintro ⟨hs, -⟩
                  exact hs
                · rintro ⟨hsb, hac⟩
                  have hs := (hesat_addEquality μ).mpr ⟨hsb, hac⟩
                  exact ⟨⟨hsb, hac⟩, hpair hs⟩
            · -- three or more conflicting values
              next first rest hnotpair hcv =>
                obtain ⟨mb, hmb, hmrg⟩ := List.mem_flatMap.mp h
                obtain ⟨seed, hseed, hiffL⟩ := ihB hmb
                simp only [List.mem_singleton] at hseed
                subst hseed
                intro μ
                rw [ihC hmrg μ, hiffL μ, hesat_addEquality μ]
                simp only [hesat_empty_iff, true_and, toLeaTTaAtoms_eq_map,
                  List.map_map, List.map_replicate]
                rw [replicate_eq_map_iff μ first rest]
                have hall : HEBindingSatisfied μ (b.addEquality a c) →
                    ∀ o ∈ rest, applyClassSolution μ (toLeaTTaAtom o) =
                      applyClassSolution μ (toLeaTTaAtom first) := by
                  intro hs o ho
                  have h1 := hs.eq_applyClassSolution_of_mem_classValues
                    (v := a) (by rw [hcv]; exact List.mem_cons_self ..)
                  have h2 := hs.eq_applyClassSolution_of_mem_classValues
                    (v := a) (by rw [hcv]; exact List.mem_cons_of_mem _ ho)
                  exact h2.symm.trans h1
                constructor
                · rintro ⟨hs, -⟩
                  exact hs
                · intro hs
                  have hsat := (hesat_addEquality μ).mpr hs
                  exact ⟨hs, hall hsat⟩
      have hC : ∀ {left right out : Bindings},
          out ∈ mergeBindings left right (fuel + 1) →
          ∀ μ : String → Metta.Atom,
            (HEBindingSatisfied μ out ↔
              (HEBindingSatisfied μ left ∧ HEBindingSatisfied μ right)) := by
        intro left right out h
        simp only [mergeBindings] at h
        obtain ⟨mid, hmid, hiffE⟩ :=
          stepFold_solution (f := fun bb p => addVarEquality bb p.1 p.2 fuel)
            (Con := fun p μ => μ p.1 = μ p.2)
            (fun hstep μ => ihE hstep μ) right.equalities _ out h
        obtain ⟨seed, hseed, hiffA⟩ :=
          stepFold_solution (f := fun bb p => addVarBinding bb p.1 p.2 fuel)
            (Con := fun p μ =>
              μ p.1 = applyClassSolution μ (toLeaTTaAtom p.2))
            (fun hstep μ => ihD hstep μ) right.assignments [left] mid hmid
        simp only [List.mem_singleton] at hseed
        subst hseed
        intro μ
        rw [hiffE μ, hiffA μ]
        constructor
        · rintro ⟨⟨hl, hassigns⟩, heqs⟩
          exact ⟨hl,
            ⟨fun x value hx => hassigns (x, value) hx,
             fun x y hx => heqs (x, y) hx⟩⟩
        · rintro ⟨hl, hr⟩
          exact ⟨⟨hl, fun p hp => hr.1 p.1 p.2 (by simpa using hp)⟩,
            fun p hp => hr.2 p.1 p.2 (by simpa using hp)⟩
      -- The matcher layer, mirroring `matchSoundPair`'s case skeleton.
      have hB : ∀ {ls rs : List Atom} {acc : List Bindings} {out : Bindings},
          out ∈ matchAtomsList ls rs acc (fuel + 1) →
          ∃ seed ∈ acc, ∀ μ : String → Metta.Atom,
            (HEBindingSatisfied μ out ↔
              (HEBindingSatisfied μ seed ∧
                (toLeaTTaAtoms ls).map (applyClassSolution μ) =
                  (toLeaTTaAtoms rs).map (applyClassSolution μ))) := by
        intro ls rs acc out h
        cases ls <;> cases rs <;> simp [matchAtomsList] at h
        case nil.nil =>
          exact ⟨out, h, fun μ => by simp⟩
        case cons.cons l ls r rs =>
          obtain ⟨seed1, hseed1, hiff⟩ := ihB h
          obtain ⟨a, ha, hseed1'⟩ := List.mem_flatMap.mp hseed1
          obtain ⟨bH, hbH, hmrg⟩ := List.mem_flatMap.mp hseed1'
          refine ⟨a, ha, fun μ => ?_⟩
          rw [hiff μ, ihC hmrg μ, ihA hbH μ]
          simp only [toLeaTTaAtoms_cons, List.map_cons, List.cons.injEq]
          tauto
      have hA : ∀ {l r : Atom} {b : Bindings}, b ∈ matchAtoms l r (fuel + 1) →
          ∀ μ : String → Metta.Atom,
            (HEBindingSatisfied μ b ↔
              applyClassSolution μ (toLeaTTaAtom l) =
                applyClassSolution μ (toLeaTTaAtom r)) := by
        intro l r b h
        cases l with
        | symbol s =>
            cases r with
            | symbol t =>
                by_cases hst : s = t
                · subst hst
                  simp [matchAtoms, getMetaType, Atom.symbolType] at h
                  have hb : b = Bindings.empty := by simpa using h.1
                  subst hb
                  simp
                · simp [matchAtoms, getMetaType, Atom.symbolType, hst] at h
            | var v =>
                simp [matchAtoms, getMetaType, Atom.symbolType,
                  Atom.variableType] at h
                have hb : b = Bindings.empty.assign v (.symbol s) := by
                  simpa using h.1
                subst hb
                intro μ
                rw [hesat_assign_of_not_isBound (by rfl) μ]
                simp [eq_comm]
            | grounded g =>
                simp [matchAtoms, getMetaType, Atom.symbolType,
                  Atom.groundedType] at h
            | expression es =>
                simp [matchAtoms, getMetaType, Atom.symbolType,
                  Atom.expressionType] at h
        | var v =>
            cases r with
            | symbol s =>
                simp [matchAtoms, getMetaType, Atom.symbolType,
                  Atom.variableType] at h
                have hb : b = Bindings.empty.assign v (.symbol s) := by
                  simpa using h.1
                subst hb
                intro μ
                rw [hesat_assign_of_not_isBound (by rfl) μ]
                simp
            | var w =>
                simp [matchAtoms, getMetaType, Atom.variableType] at h
                have hb : b = Bindings.empty.addEquality v w := by
                  simpa using h.1
                subst hb
                intro μ
                rw [hesat_addEquality μ]
                simp
            | grounded g =>
                simp [matchAtoms, getMetaType, Atom.variableType,
                  Atom.groundedType] at h
                have hb : b = Bindings.empty.assign v (.grounded g) := by
                  simpa using h.1
                subst hb
                intro μ
                rw [hesat_assign_of_not_isBound (by rfl) μ]
                simp
            | expression es =>
                simp [matchAtoms, getMetaType, Atom.variableType,
                  Atom.expressionType] at h
                have hb : b = Bindings.empty.assign v (.expression es) := by
                  simpa using h.1
                subst hb
                intro μ
                rw [hesat_assign_of_not_isBound (by rfl) μ]
                simp
        | grounded g =>
            cases r with
            | symbol s =>
                simp [matchAtoms, getMetaType, Atom.symbolType,
                  Atom.groundedType] at h
            | var v =>
                simp [matchAtoms, getMetaType, Atom.variableType,
                  Atom.groundedType] at h
                have hb : b = Bindings.empty.assign v (.grounded g) := by
                  simpa using h.1
                subst hb
                intro μ
                rw [hesat_assign_of_not_isBound (by rfl) μ]
                simp [eq_comm]
            | grounded hG =>
                by_cases hg : g = hG
                · subst hg
                  simp [matchAtoms, getMetaType, Atom.groundedType] at h
                  have hb : b = Bindings.empty := by simpa using h.1
                  subst hb
                  simp
                · simp [matchAtoms, getMetaType, Atom.groundedType, hg] at h
            | expression es =>
                simp [matchAtoms, getMetaType, Atom.expressionType,
                  Atom.groundedType] at h
        | expression ls =>
            cases r with
            | symbol s =>
                simp [matchAtoms, getMetaType, Atom.symbolType,
                  Atom.expressionType] at h
            | var v =>
                simp [matchAtoms, getMetaType, Atom.variableType,
                  Atom.expressionType] at h
                have hb : b = Bindings.empty.assign v (.expression ls) := by
                  simpa using h.1
                subst hb
                intro μ
                rw [hesat_assign_of_not_isBound (by rfl) μ]
                simp [eq_comm]
            | grounded g =>
                simp [matchAtoms, getMetaType, Atom.expressionType,
                  Atom.groundedType] at h
            | expression rs =>
                by_cases hlen : ls.length = rs.length
                · simp [matchAtoms, getMetaType, Atom.expressionType,
                    hlen] at h
                  rcases h with ⟨hList, -⟩
                  obtain ⟨seed, hseed, hiff⟩ := ihB hList
                  simp only [List.mem_singleton] at hseed
                  subst hseed
                  intro μ
                  rw [hiff μ]
                  simp [Metta.Atom.expr.injEq]
                · simp [matchAtoms, getMetaType, Atom.expressionType,
                    hlen] at h
      exact ⟨hA, hB, hC, hD, hE⟩

/-! ## Exported solution characterizations -/

/-- **Solution soundness of the executable HE matcher**: every returned
binding set presents exactly the solution set of the input equation. -/
theorem matchAtoms_solution_iff {l r : Atom} {b : Bindings} {fuel : Nat}
    (h : b ∈ matchAtoms l r fuel) (μ : String → Metta.Atom) :
    HEBindingSatisfied μ b ↔
      MettaEquationSatisfied μ (toLeaTTaAtom l, toLeaTTaAtom r) :=
  (solutionPack fuel).1 h μ

/-- Merging presents exactly solution intersection. -/
theorem mergeBindings_solution_iff {left right out : Bindings} {fuel : Nat}
    (h : out ∈ mergeBindings left right fuel) (μ : String → Metta.Atom) :
    HEBindingSatisfied μ out ↔
      (HEBindingSatisfied μ left ∧ HEBindingSatisfied μ right) :=
  (solutionPack fuel).2.2.1 h μ

/-- `addVarBinding` presents exactly one added value constraint. -/
theorem addVarBinding_solution_iff {b : Bindings} {v : String} {val : Atom}
    {out : Bindings} {fuel : Nat}
    (h : out ∈ addVarBinding b v val fuel) (μ : String → Metta.Atom) :
    HEBindingSatisfied μ out ↔
      (HEBindingSatisfied μ b ∧
        μ v = applyClassSolution μ (toLeaTTaAtom val)) :=
  (solutionPack fuel).2.2.2.1 h μ

/-- `addVarEquality` presents exactly one added equality constraint. -/
theorem addVarEquality_solution_iff {b : Bindings} {a c : String}
    {out : Bindings} {fuel : Nat}
    (h : out ∈ addVarEquality b a c fuel) (μ : String → Metta.Atom) :
    HEBindingSatisfied μ out ↔
      (HEBindingSatisfied μ b ∧ μ a = μ c) :=
  (solutionPack fuel).2.2.2.2 h μ

/-! ## The cross-engine corollary -/

/-- Any executable HE match witness and any repaired-LeaTTa match witness for
one translated equation have **equal binding solution theories**.  This is the
semantic half of the cross-engine congruence, obtained with no comparison of
binding representations — either engine may present the solution set through
any spanning tree, orientation, or reconciliation route. -/
theorem heMatch_leaMatch_solutionTheoryEquiv
    {l r : Atom} {b : Bindings} {fuel : Nat} {lb : Metta.Bindings}
    (hHE : b ∈ matchAtoms l r fuel)
    (hLea : lb ∈ Metta.matchAtoms (toLeaTTaAtom l) (toLeaTTaAtom r))
    (hlNoFloat : MettaAtomNoFloat (toLeaTTaAtom l))
    (hrNoFloat : MettaAtomNoFloat (toLeaTTaAtom r)) :
    LeaBindingSolutionTheoryEquiv b lb := by
  intro μ
  rw [matchAtoms_solution_iff hHE μ]
  exact (leaMatchAtoms_solution_iff μ hlNoFloat hrNoFloat hLea).symm

/-! ## Oracles -/

/-- POSITIVE: on the connected-class regression shape, the solution reading of
**any** matcher output identifies the two query variables — the observable the
oriented-`val` unifier-discard bug lost. -/
example {b : Bindings} {μ : String → Metta.Atom}
    (h : b ∈ matchAtoms
      (.expression [.symbol "g", .var "q1", .var "q1", .var "q2"])
      (.expression [.symbol "g", .var "p1", .var "p2", .var "p2"]) 10)
    (hsat : HEBindingSatisfied μ b) : μ "q1" = μ "q2" := by
  have heq := (matchAtoms_solution_iff h μ).mp hsat
  simp only [MettaEquationSatisfied, applyToLea_expression,
    toLeaTTaAtoms_cons, toLeaTTaAtoms_nil, List.map_cons, List.map_nil,
    applyToLea_symbol, applyToLea_var, Metta.Atom.expr.injEq,
    List.cons.injEq, and_true, true_and] at heq
  obtain ⟨h1, h2, h3⟩ := heq
  exact h2.trans h3.symm

/-- NEGATIVE: the solution reading accepts nothing beyond the equation — a
valuation disagreeing with the matched symbol is rejected. -/
example {b : Bindings}
    (h : b ∈ matchAtoms (.var "x") (.symbol "a") 10) :
    ¬ HEBindingSatisfied (fun _ => .sym "b") b := by
  intro hsat
  have heq := (matchAtoms_solution_iff h _).mp hsat
  simp [MettaEquationSatisfied] at heq

end Mettapedia.Languages.MeTTa.HE.LeaTTaBridge
