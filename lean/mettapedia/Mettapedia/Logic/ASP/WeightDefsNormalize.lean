import Mettapedia.Logic.ASP.WeightDefs

/-!
# Weight definitions and the normalization by sequential weight counters

A program with definitions (`WeightDefs`) reads as a weight program (`WeightRules`): each normal
rule `h :- pos, not neg` is the weight rule `h :- n ≤ {pos = 1, not neg = 1}` with `n` its number of
literals (`Rule.toWRule`, `Rule.toWRule_bodyHolds`), and each definition `W ↔ L ≤ {terms}` is the
weight rule `W :- L ≤ {terms}` (`WeightDef.toWRule`). This weight program
(`DefProgram.toWProgram`) is normalized by the verified sequential weight counter
(`WProgram.normalize`).

## The bridge

* `DefProgram.stable_of_toWProgram`: for well-formed definitions (distinct atoms, heading no rule),
  every stable model of the weight program is a stable model of the program with definitions.
* `DefProgram.toWProgram_of_stable`: if moreover no definition's atom lies on a cycle of positive
  dependencies (`DefProgram.Acyclic`), the converse holds. Each definition's atom in `S` is derived
  in the weight program's least model by induction along the dependencies between definition
  atoms, which are well founded: there are finitely many and none depends on itself.
* **`DefProgram.stable_iff_toWProgram`**: so under both conditions the two have the same stable
  models.

Acyclicity is needed: with `a :- W` and `W ↔ 1 ≤ {a = 1}`, `{a, W}` is a stable model of the program
with definitions, the definition giving `W` and the rule `a`, but the weight program has only the
stable model `∅` (`WeightStepControls`).

## The normalization

Composed with the normalization theorem (`WProgram.normalize_correct`), not re-proved:

* **`DefProgram.stable_iff_exists_normalize`**: `S` is a stable model of the program with
  definitions exactly when it is the original atoms of a stable model of the normalized program;
* **`DefProgram.normalize_correct`**: restriction to the original atoms maps the stable models of
  the normalized program onto those of the program with definitions, each extending to exactly one;
* `DefProgram.restrict_normalize`: the same restricted further to any set of atoms, such as the
  atoms other than the definitions'.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ASP

universe u

variable {A : Type u}

/-! ## Normal rules as weight rules -/

/-- A normal rule as a weight rule: each literal of weight `1`, the bound its number of literals. -/
def Rule.toWRule (r : Rule A) : WRule A :=
  ⟨.atom r.head, r.pos.length + r.neg.length,
    r.pos.map (fun b => ⟨.pos b, 1⟩) ++ r.neg.map fun b => ⟨.neg b, 1⟩⟩

theorem weightIn_le_length {ts : List (WTerm A)} (unit : ∀ t ∈ ts, t.weight = 1) (I N : Set A) :
    weightIn ts I N ≤ ts.length := by
  induction ts with
  | nil => exact le_rfl
  | cons t ts ih =>
    rw [weightIn_cons, List.length_cons]
    have rest := ih fun t' ht' => unit t' (List.mem_cons_of_mem _ ht')
    have head : t.value I N ≤ 1 := by
      by_cases h : t.lit.Holds I N
      · rw [WTerm.value_of_holds h, unit t List.mem_cons_self]
      · rw [WTerm.value_of_not_holds h]
        exact Nat.zero_le _
    omega

/-- Literals of weight `1` weigh at least their number exactly when all of them hold. -/
theorem length_le_weightIn_iff {ts : List (WTerm A)} (unit : ∀ t ∈ ts, t.weight = 1) (I N : Set A) :
    ts.length ≤ weightIn ts I N ↔ ∀ t ∈ ts, t.lit.Holds I N := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    have unit' : ∀ t' ∈ ts, t'.weight = 1 := fun t' ht' => unit t' (List.mem_cons_of_mem _ ht')
    rw [weightIn_cons, List.length_cons, List.forall_mem_cons, ← ih unit']
    have rest := weightIn_le_length unit' I N
    by_cases h : t.lit.Holds I N
    · rw [WTerm.value_of_holds h, unit t List.mem_cons_self]
      simp only [h, true_and]
      omega
    · rw [WTerm.value_of_not_holds h]
      simp only [h, false_and, iff_false]
      omega

/-- **A normal rule and its weight rule have the same body.** -/
theorem Rule.toWRule_bodyHolds (r : Rule A) (I N : Set A) : r.toWRule.BodyHolds I N ↔ r.Holds I N := by
  have unit : ∀ t ∈ r.toWRule.body, t.weight = 1 := by
    intro t ht
    simp only [Rule.toWRule, List.mem_append, List.mem_map] at ht
    rcases ht with ⟨b, -, rfl⟩ | ⟨b, -, rfl⟩ <;> rfl
  have bound : r.toWRule.bound = r.toWRule.body.length := by simp [Rule.toWRule]
  unfold WRule.BodyHolds
  rw [bound, length_le_weightIn_iff unit]
  simp only [Rule.toWRule, List.forall_mem_append, List.forall_mem_map, Rule.Holds]
  exact Iff.rfl

/-! ## The weight program of a program with definitions -/

namespace DefProgram

variable (Q : DefProgram A)

/-- **The weight program**: the rules as weight rules, then the definitions as weight rules. -/
def toWProgram : WProgram A := Q.rules.map Rule.toWRule ++ Q.defs.map WeightDef.toWRule

/-- The immediate consequences of the weight program: those of the rules, and the definitions'
atoms whose bodies hold. -/
theorem step_toWProgram (I N : Set A) :
    Q.toWProgram.step I N = Q.rules.step I N ∪ {a | ∃ d ∈ Q.defs, d.atom = a ∧ d.bound ≤ weightIn d.terms I N} := by
  ext a
  simp only [WProgram.step, toWProgram, List.mem_append, List.mem_map, Set.mem_union, Set.mem_ofPred_eq,
    Program.step]
  constructor
  · rintro ⟨ρ, ⟨r, hr, rfl⟩ | ⟨d, hd, rfl⟩, offers, body⟩
    · exact .inl ⟨r, hr, offers, (r.toWRule_bodyHolds _ _).mp body⟩
    · exact .inr ⟨d, hd, offers, body⟩
  · rintro (⟨r, hr, rfl, holds⟩ | ⟨d, hd, rfl, body⟩)
    · exact ⟨r.toWRule, .inl ⟨r, hr, rfl⟩, rfl, (r.toWRule_bodyHolds _ _).mpr holds⟩
    · exact ⟨d.toWRule, .inr ⟨d, hd, rfl⟩, rfl, body⟩

/-- The weight program has no constraints, so its stable models are the least fixed points. -/
theorem toWProgram_stable_iff (S : Set A) : Q.toWProgram.Stable S ↔ S = Q.toWProgram.glOp S := by
  rw [WProgram.stable_iff]
  refine ⟨fun h => h.1, fun h => ⟨h, fun ρ hρ hh => ?_⟩⟩
  rcases List.mem_append.mp hρ with hρ | hρ <;> obtain ⟨x, -, rfl⟩ := List.mem_map.mp hρ <;> cases hh

variable {Q}

/-- For well-formed definitions, a definition's atom is derived exactly by its own definition. -/
theorem defAtom_mem_step (wf : Q.WellFormed) {d : WeightDef A} (hd : d ∈ Q.defs) (I N : Set A) :
    d.atom ∈ Q.toWProgram.step I N ↔ d.bound ≤ weightIn d.terms I N := by
  rw [step_toWProgram]
  constructor
  · rintro (⟨r, hr, head, -⟩ | ⟨d', hd', same, body⟩)
    · exact absurd (head ▸ Q.atom_mem_defAtoms hd) (wf.noHead r hr)
    · rwa [List.inj_on_of_nodup_map wf.nodup hd' hd same] at body
  · exact fun body => .inr ⟨d, hd, rfl, body⟩

/-- More positive atoms make the literals weigh more. -/
theorem weightIn_le_of_pos {ts : List (WTerm A)} {I I' N : Set A}
    (h : ∀ t ∈ ts, ∀ b, t.lit = .pos b → b ∈ I → b ∈ I') : weightIn ts I N ≤ weightIn ts I' N := by
  induction ts with
  | nil => exact le_rfl
  | cons t ts ih =>
    rw [weightIn_cons, weightIn_cons]
    have head : t.value I N ≤ t.value I' N := by
      obtain ⟨l, w⟩ := t
      cases l with
      | pos b =>
        by_cases hb : b ∈ I
        · rw [WTerm.value_of_holds (t := ⟨.pos b, w⟩) (I := I) (N := N) hb,
            WTerm.value_of_holds (t := ⟨.pos b, w⟩) (I := I') (N := N) (h _ List.mem_cons_self b rfl hb)]
        · rw [WTerm.value_of_not_holds (t := ⟨.pos b, w⟩) (I := I) (N := N) hb]
          exact Nat.zero_le _
      | neg b => exact le_rfl
    have := ih fun t' ht' => h t' (List.mem_cons_of_mem _ ht')
    omega

/-- **Every stable model of the weight program is a stable model of the program with definitions.** -/
theorem stable_of_toWProgram (wf : Q.WellFormed) {S : Set A} (h : Q.toWProgram.Stable S) : Q.Stable S := by
  have hS : S = Q.toWProgram.glOp S := (Q.toWProgram_stable_iff S).mp h
  have fixed : Q.toWProgram.step S S = S := by
    have := Q.toWProgram.glOp_fixed S
    rwa [← hS] at this
  have defs : ∀ d ∈ Q.defs, d.atom ∈ S ↔ d.Holds S := fun d hd => by
    have := defAtom_mem_step wf hd S S
    rwa [fixed] at this
  refine ⟨defs, ?_⟩
  have pre : (Q.given S).step S S ⊆ S := by
    rw [step_given]
    rintro a (ha | ⟨d, -, rfl, hS'⟩)
    · rw [← fixed, step_toWProgram]
      exact .inl ha
    · exact hS'
  have below : (Q.given S).glOp S ⊆ S := OrderHom.lfp_le _ pre
  refine Set.Subset.antisymm ?_ below
  have above : Q.toWProgram.glOp S ⊆ (Q.given S).glOp S := by
    apply OrderHom.lfp_le
    intro a ha
    change a ∈ Q.toWProgram.step ((Q.given S).glOp S) S at ha
    rw [step_toWProgram] at ha
    rw [← (Q.given S).glOp_fixed S, step_given]
    rcases ha with ha | ⟨d, hd, rfl, body⟩
    · exact .inl ha
    · exact .inr ⟨d, hd, rfl, (defs d hd).mpr (body.trans (weightIn_mono_left _ _ below))⟩
  intro a ha
  rw [hS] at ha
  exact above ha

/-- **For acyclic definitions, every stable model of the program with definitions is a stable model
of the weight program.** -/
theorem toWProgram_of_stable (wf : Q.WellFormed) (acyclic : Q.Acyclic) {S : Set A} (h : Q.Stable S) :
    Q.toWProgram.Stable S := by
  obtain ⟨defs, stable⟩ := h
  have fixedS : (Q.given S).step S S = S := (Q.given S).stable_step_eq stable
  set Z := Q.toWProgram.glOp S with hZ
  have fixedZ : Q.toWProgram.step Z S = Z := Q.toWProgram.glOp_fixed S
  have ZS : Z ⊆ S := by
    apply OrderHom.lfp_le
    intro a ha
    change a ∈ Q.toWProgram.step S S at ha
    rw [step_toWProgram] at ha
    rcases ha with ha | ⟨d, hd, rfl, body⟩
    · rw [← fixedS]
      exact Q.rules_step_subset_given S S S ha
    · exact (defs d hd).mpr body
  -- An atom of `S` is in `Z` once the definition atoms it depends on are.
  have founded : ∀ b ∈ S, (∀ d ∈ Q.defs, Relation.ReflTransGen Q.PosDep d.atom b → d.atom ∈ S → d.atom ∈ Z) →
      b ∈ Z := by
    let Y : Set A := {x | x ∈ S ∧
      ((∀ d ∈ Q.defs, Relation.ReflTransGen Q.PosDep d.atom x → d.atom ∈ S → d.atom ∈ Z) → x ∈ Z)}
    have sub : (Q.given S).glOp S ⊆ Y := by
      apply OrderHom.lfp_le
      intro x hx
      change x ∈ (Q.given S).step Y S at hx
      have xS : x ∈ S := by
        rw [← fixedS]
        exact (Q.given S).step_mono (fun y hy => hy.1) le_rfl hx
      refine ⟨xS, fun H => ?_⟩
      rw [step_given] at hx
      rcases hx with ⟨r, hr, rfl, holds⟩ | ⟨d, hd, rfl, -⟩
      · have body : r.Holds Z S := ⟨fun b hb => (holds.1 b hb).2 fun d hd rtg =>
          H d hd (rtg.tail (.inl ⟨r, hr, rfl, hb⟩)), holds.2⟩
        rw [← fixedZ, step_toWProgram]
        exact .inl ⟨r, hr, rfl, body⟩
      · exact H d hd .refl xS
    intro b hb H
    have hb' : b ∈ (Q.given S).glOp S := by
      rw [← stable]
      exact hb
    exact (sub hb').2 H
  -- Every definition atom of `S` is in `Z`, by induction along the dependencies between them.
  have defsZ : ∀ d ∈ Q.defs, d.atom ∈ S → d.atom ∈ Z := by
    classical
    let R : {a // a ∈ Q.defAtoms.toFinset} → {a // a ∈ Q.defAtoms.toFinset} → Prop :=
      fun x y => Relation.TransGen Q.PosDep x.1 y.1
    have : IsTrans _ R := ⟨fun _ _ _ h₁ h₂ => Relation.TransGen.trans h₁ h₂⟩
    have : Std.Irrefl R := ⟨fun x hx => by
      obtain ⟨d, hd, hdx⟩ := List.mem_map.mp (List.mem_toFinset.mp x.2)
      exact acyclic d hd (by rw [hdx]; exact hx)⟩
    have wfR : WellFounded R := Finite.wellFounded_of_trans_of_irrefl R
    have key : ∀ x : {a // a ∈ Q.defAtoms.toFinset}, x.1 ∈ S → x.1 ∈ Z := by
      intro x
      refine wfR.induction (C := fun x => x.1 ∈ S → x.1 ∈ Z) x fun x ih => ?_
      intro hx
      obtain ⟨d, hd, hdx⟩ := List.mem_map.mp (List.mem_toFinset.mp x.2)
      rw [← hdx] at hx ⊢
      have pos : ∀ t ∈ d.terms, ∀ b, t.lit = .pos b → b ∈ S → b ∈ Z := by
        intro t ht b hb hbS
        have dep : Q.PosDep b d.atom := .inr ⟨d, hd, rfl, WeightDef.pos_of_mem_terms ht hb⟩
        refine founded b hbS fun d' hd' rtg hd'S => ?_
        have below : R ⟨d'.atom, List.mem_toFinset.mpr (Q.atom_mem_defAtoms hd')⟩ x := by
          change Relation.TransGen Q.PosDep d'.atom x.1
          rw [← hdx]
          exact Relation.TransGen.tail' rtg dep
        exact ih _ below hd'S
      have body : d.bound ≤ weightIn d.terms Z S := ((defs d hd).mp hx).trans (weightIn_le_of_pos pos)
      rw [← fixedZ]
      exact (defAtom_mem_step wf hd Z S).mpr body
    intro d hd hS
    exact key ⟨d.atom, List.mem_toFinset.mpr (Q.atom_mem_defAtoms hd)⟩ hS
  have SZ : S ⊆ Z := by
    have least : (Q.given S).glOp S ⊆ Z := by
      apply OrderHom.lfp_le
      intro a ha
      change a ∈ (Q.given S).step Z S at ha
      rw [step_given] at ha
      rcases ha with ha | ⟨d, hd, rfl, hS⟩
      · rw [← fixedZ, step_toWProgram]
        exact .inl ha
      · exact defsZ d hd hS
    intro a ha
    rw [stable] at ha
    exact least ha
  exact (Q.toWProgram_stable_iff S).mpr (Set.Subset.antisymm SZ ZS)

/-- **The program with acyclic, well-formed definitions and its weight program have the same stable
models.** -/
theorem stable_iff_toWProgram (wf : Q.WellFormed) (acyclic : Q.Acyclic) (S : Set A) :
    Q.Stable S ↔ Q.toWProgram.Stable S :=
  ⟨toWProgram_of_stable wf acyclic, stable_of_toWProgram wf⟩

/-! ## The normalization -/

/-- **The stable models of the program with definitions are the original atoms of the stable models
of its normalization.** -/
theorem stable_iff_exists_normalize (wf : Q.WellFormed) (acyclic : Q.Acyclic) (S : Set A) :
    Q.Stable S ↔ ∃ M, Q.toWProgram.normalize.Stable M ∧ Sum.inl ⁻¹' M = S :=
  (stable_iff_toWProgram wf acyclic S).trans (WProgram.stable_iff_exists_normalize S)

/-- **The normalization is correct for programs with acyclic definitions**: restriction to the original
atoms maps the stable models of the normalized program onto the stable models of the program with
definitions, and each of these extends to exactly one stable model of the normalized program. -/
theorem normalize_correct (wf : Q.WellFormed) (acyclic : Q.Acyclic) :
    (Sum.inl ⁻¹' ·) '' {M | Q.toWProgram.normalize.Stable M} = {S | Q.Stable S} ∧
      ∀ S, Q.Stable S → ∃! M, Q.toWProgram.normalize.Stable M ∧ Sum.inl ⁻¹' M = S := by
  obtain ⟨image, unique⟩ := Q.toWProgram.normalize_correct
  refine ⟨?_, fun S h => unique S ((stable_iff_toWProgram wf acyclic S).mp h)⟩
  rw [image]
  ext S
  exact (stable_iff_toWProgram wf acyclic S).symm

/-- **Restricted to any set of atoms**, the stable models of the normalized program and of the program
with definitions are the same. -/
theorem restrict_normalize (wf : Q.WellFormed) (acyclic : Q.Acyclic) (O : Set A) :
    (fun M => Sum.inl ⁻¹' M ∩ O) '' {M | Q.toWProgram.normalize.Stable M} = (· ∩ O) '' {S | Q.Stable S} := by
  rw [← (normalize_correct wf acyclic).1, Set.image_image]

end DefProgram

end Mettapedia.Logic.ASP
