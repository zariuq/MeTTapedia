import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization.Static

/-!
# Congruent states are statically equivalent, beside programs that leave a constant unused

The content direction of the characterization of `Static` (see `Static` for the outline):

* `countAt_eq_of_congruent`: the probe argument, at congruent states whose left rows a solution pins;
* `rows_of_congruent`: a renaming of identities under which every label of the left equals the label
  of its image at every solution of the left knowledge;
* `mentions_of_congruent`: the right mentions no unknown the left does not;
* `static_of_congruent`: `Cong ⟨P, s⟩ ⟨P', t⟩ → Static s t` for bounded `P`, `P'`;
* **`congruent_iff_static`** (bounded `P`) and **`static_iff`** (no rules): congruence of states is
  exactly the static equivalence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open Mettapedia.Logic.LP
open RuleSyntax.Examples (Tm X E x c fresh_of_ground)
open RuleSyntax.Controls (atoms action)
open AtOneFrame (Sys Cong Moves pat idle information_of_empty fresh_identity tellX)

/-! ## The probe argument -/

/-- **The probe argument**: at congruent states beside a program whose constants lie below `z`, when
a solution pins the rows of the left and solves the right knowledge, and the right avoids `z` and
`z + 1`, the rows that solution equates with `k` are as many at the right as at the left. -/
theorem countAt_eq_of_congruent {P P' : Program Tm} {z : ℕ}
    (boundP' : ∀ r ∈ P', ∀ t ∈ r.terms, ∀ k : ℕ, t = .const k → k < z)
    {u v : State Tm ℕ} (related : Cong ⟨P, u⟩ ⟨P', v⟩) {σ₀ : Subst atoms}
    (solvedU : X.Models (a := PUnit.unit) (b := PUnit.unit) σ₀ u.knowledge)
    (solvedV : X.Models (a := PUnit.unit) (b := PUnit.unit) σ₀ v.knowledge)
    (pinnedU : ∀ τ : Subst atoms, X.Models (a := PUnit.unit) (b := PUnit.unit) τ u.knowledge →
      ∀ o ∈ u.present, Subst.applyTerm τ (u.label o) = Subst.applyTerm σ₀ (u.label o))
    (belowU : ∀ o ∈ u.present, ∀ j : ℕ, Subst.applyTerm σ₀ (u.label o) = .const j → j < z)
    (avoidsV : Avoids z v) (avoidsV' : Avoids (z + 1) v) (k : ℕ) :
    countAt σ₀ v k = countAt σ₀ u k := by
  have relatedProbe : Cong ⟨P ∪ {probe k (countAt σ₀ u k) z}, u⟩
      ⟨P' ∪ {probe k (countAt σ₀ u k) z}, v⟩ := related.addRules {probe k (countAt σ₀ u k) z}
  have member : probe k (countAt σ₀ u k) z ∈ P ∪ {probe k (countAt σ₀ u k) z} :=
    Set.mem_union_right _ (Set.mem_singleton _)
  have admitted := probe_admitted member ⟨PUnit.unit, σ₀, solvedU⟩ pinnedU
    (fresh_identity u.present)
  obtain ⟨T', moved, relatedResults⟩ :=
    candidate_congruent.reduces relatedProbe (reduces_of_admits _ admitted)
  obtain ⟨-, h, admittedH, reached⟩ := moved
  have reached' : h.result X v = T'.state := reached
  have barbLeft := probe_barb member admitted
  have noBarbLeft := probe_no_barb (z' := z + 1) (m := u.present.sup id + 1) member pinnedU
    (fun o present same => by
      have small := belowU o present (z + 1) same
      omega)
    (by omega)
  have barbRight : MayBarb X (pat (c z)) T'.state :=
    candidate_congruent.barbs relatedResults _ barbLeft
  rcases (Set.mem_union _ _ _).mp h.member with inP' | isProbe
  · exfalso
    have avoids : ∀ z'' : ℕ, z ≤ z'' → ∀ t ∈ h.rule.terms, t ≠ .const z'' := by
      intro z'' above t inside same
      have small := boundP' h.rule inP' t inside z'' same
      omega
    have avoidZ : Avoids z (h.result X v) :=
      result_avoids h admittedH (avoids z le_rfl) avoidsV
    have avoidZ' : Avoids (z + 1) (h.result X v) :=
      result_avoids h admittedH (avoids (z + 1) (Nat.le_succ z)) avoidsV'
    rw [← reached'] at barbRight
    have swapped := mayBarb_swap avoidZ avoidZ' barbRight
    rw [reached'] at swapped
    exact noBarbLeft (candidate_congruent.barbs relatedResults.symm _ swapped)
  · exact count_of_probe h isProbe admittedH solvedV

/-! ## The rows -/

/-- **The rows are observed**: congruent states beside bounded programs, at solvable knowledge, have
present rows that a renaming of identities matches label for label at every solution. -/
theorem rows_of_congruent {P P' : Program Tm} (boundP' : Bounded P') {s t : State Tm ℕ}
    (related : Cong ⟨P, s⟩ ⟨P', t⟩) (solvable : X.Solvable (a := PUnit.unit) s.knowledge) :
    ∃ π : Equiv.Perm ℕ, s.present.map π.toEmbedding = t.present ∧
      ∀ o ∈ s.present, ∀ δ : Subst atoms,
        X.Models (a := PUnit.unit) (b := PUnit.unit) δ s.knowledge →
          Subst.applyTerm δ (s.label o) = Subst.applyTerm δ (t.label (π o)) := by
  classical
  obtain ⟨B', boundB'⟩ := boundP'
  have equivalent := equivalent_of_congruent related
  let L := mentioned s ++ mentioned t
  obtain ⟨σ₀, solvedS, constant, generic⟩ := generic_solution solvable L
  have solvedT : X.Models (a := PUnit.unit) (b := PUnit.unit) σ₀ t.knowledge :=
    (equivalent PUnit.unit σ₀).mp solvedS
  let G := pin σ₀ L
  obtain ⟨z, hz⟩ : ∃ z, z = sizeBound (L.map (Subst.applyTerm σ₀)) + B' := ⟨_, rfl⟩
  have pinG : X.Models (a := PUnit.unit) (b := PUnit.unit) σ₀ G :=
    models_pin_self fun u _ => constant u
  -- Every constant of a listed term or of its grounded value lies below `z`.
  have valueBelow : ∀ w ∈ L, ∀ j : ℕ, Subst.applyTerm σ₀ w = .const j → j < z := by
    intro w inside j same
    have small := size_le_sizeBound (List.mem_map_of_mem (f := Subst.applyTerm σ₀) inside)
    rw [same] at small
    simp only [size] at small
    omega
  have listedBelow : ∀ w ∈ L, ∀ j : ℕ, w = .const j → j < z := by
    intro w inside j same
    apply valueBelow w inside j
    rw [same]
    rfl
  have rightAvoids : ∀ z'' : ℕ, z ≤ z'' → Avoids z'' (tellState t G) := by
    intro z'' above w mentions same
    rcases mentions with inFst | inSnd | ⟨o, present, rfl⟩
    · obtain ⟨e, inside, rfl⟩ := List.mem_map.mp inFst
      rcases List.mem_append.mp inside with old | told
      · have small := listedBelow e.1 (List.mem_append_right _
          (mem_mentioned.mpr (Or.inl (List.mem_map_of_mem old)))) z'' same
        omega
      · obtain ⟨w', listed, rfl⟩ := List.mem_map.mp told
        have small := listedBelow w' listed z'' same
        omega
    · obtain ⟨e, inside, rfl⟩ := List.mem_map.mp inSnd
      rcases List.mem_append.mp inside with old | told
      · have small := listedBelow e.2 (List.mem_append_right _
          (mem_mentioned.mpr (Or.inr (Or.inl (List.mem_map_of_mem old))))) z'' same
        omega
      · obtain ⟨w', listed, rfl⟩ := List.mem_map.mp told
        have small := valueBelow w' listed z'' same
        omega
    · have small := listedBelow (t.label o) (List.mem_append_right _
        (mem_mentioned.mpr (Or.inr (Or.inr ⟨o, present, rfl⟩)))) z'' same
      omega
  have relatedG : Cong ⟨P, tellState s G⟩ ⟨P', tellState t G⟩ := related.tell fun _ => G
  have pinnedU : ∀ τ : Subst atoms, X.Models (a := PUnit.unit) (b := PUnit.unit) τ
      (tellState s G).knowledge →
      ∀ o ∈ (tellState s G).present, Subst.applyTerm τ ((tellState s G).label o) =
        Subst.applyTerm σ₀ ((tellState s G).label o) := by
    intro τ solved o present
    obtain ⟨-, pinned⟩ := (Frames.models_append _ _ _).mp solved
    exact (models_pin_iff (fun u _ => constant u) τ).mp pinned (s.label o)
      (List.mem_append_left _ (mem_mentioned.mpr (Or.inr (Or.inr ⟨o, present, rfl⟩))))
  have counts : ∀ k, countAt σ₀ t k = countAt σ₀ s k := fun k =>
    countAt_eq_of_congruent (z := z)
      (fun r member w inside j same => by
        have small := boundB' r member w inside j same
        omega)
      relatedG ((Frames.models_append _ _ _).mpr ⟨solvedS, pinG⟩)
      ((Frames.models_append _ _ _).mpr ⟨solvedT, pinG⟩) pinnedU
      (fun o present j same => valueBelow (s.label o)
        (List.mem_append_left _ (mem_mentioned.mpr (Or.inr (Or.inr ⟨o, present, rfl⟩)))) j same)
      (rightAvoids z le_rfl) (rightAvoids (z + 1) (Nat.le_succ z)) k
  -- Equal counts give equal multisets of grounded labels.
  have toCount : ∀ (w : State Tm ℕ) (j : ℕ),
      Multiset.card (Multiset.filter (fun o => Term.const j = Subst.applyTerm σ₀ (w.label o))
        w.present.val) = countAt σ₀ w j := by
    intro w j
    have same : w.present.filter (fun o => Term.const j = Subst.applyTerm σ₀ (w.label o)) =
        matchesAt X (a := PUnit.unit) (b := PUnit.unit) σ₀ w.label w.present (c j) := by
      ext o
      rw [Finset.mem_filter, mem_matchesAt]
      exact Iff.rfl
    unfold countAt
    rw [← same]
    rfl
  have multisets : s.present.val.map (fun o => Subst.applyTerm σ₀ (s.label o)) =
      t.present.val.map (fun o => Subst.applyTerm σ₀ (t.label o)) := by
    ext a
    rw [Multiset.count_map, Multiset.count_map]
    cases a with
    | var v =>
        have none : ∀ (w : State Tm ℕ), Multiset.card
            (Multiset.filter (fun o => Term.var v = Subst.applyTerm σ₀ (w.label o)) w.present.val) =
            0 := by
          intro w
          apply Multiset.card_eq_zero.mpr
          apply Multiset.filter_eq_nil.mpr
          intro o _ same
          obtain ⟨j, valued⟩ := constant (w.label o)
          rw [valued] at same
          cases same
        exact (none s).trans (none t).symm
    | const j => exact (toCount s j).trans ((counts j).symm.trans (toCount t j).symm)
    | app fn _ => exact nomatch fn
  obtain ⟨π, image, labels⟩ := exists_perm_of_map_eq (fun o => Subst.applyTerm σ₀ (s.label o))
    (fun o => Subst.applyTerm σ₀ (t.label o)) s.present t.present multisets
  refine ⟨π, image, fun o present δ solved => ?_⟩
  have imagePresent : π o ∈ t.present := by
    rw [← image]
    exact Finset.mem_map_of_mem _ present
  exact generic (s.label o)
    (List.mem_append_left _ (mem_mentioned.mpr (Or.inr (Or.inr ⟨o, present, rfl⟩))))
    (t.label (π o))
    (List.mem_append_right _ (mem_mentioned.mpr (Or.inr (Or.inr ⟨π o, imagePresent, rfl⟩))))
    (labels o present).symm δ solved

/-! ## The support -/

/-- No term is the constant one above its own numeral. -/
theorem ne_const_size (t : Term atoms) : t ≠ .const (size t) := by
  cases t with
  | var v => exact fun same => by cases same
  | const k =>
      intro same
      have values : size (Term.const k : Term atoms) = k := (Term.const.inj same).symm
      simp only [size] at values
      omega
  | app fn _ => exact nomatch fn

/-- An opened term of a rule is not an unknown the state mentions. -/
theorem opened_ne_var {P : Program Tm} {s : State Tm ℕ} (f : Firing ℕ E P s.frame)
    (fresh : f.Fresh X s) {t : Term atoms} (term : t ∈ f.rule.terms) {w : ℕ}
    (mentions : s.Mentions (.var w)) : Subst.applyTerm f.opening t ≠ .var w := by
  cases t with
  | var v =>
      obtain ⟨w', opened, unmentioned⟩ := opening_var f fresh term
      show f.opening v ≠ .var w
      rw [opened]
      intro same
      have values : w' = w := Term.var.inj same
      subst values
      exact unmentioned mentions
  | const n => exact fun same => by cases same
  | app fn _ => exact nomatch fn

/-- **The support is observed**: beside bounded programs, at solvable knowledge, every unknown the
right mentions is mentioned by the left. -/
theorem mentions_of_congruent {P P' : Program Tm} (boundP' : Bounded P') {s t : State Tm ℕ}
    (related : Cong ⟨P, s⟩ ⟨P', t⟩) (solvable : X.Solvable (a := PUnit.unit) s.knowledge) {w : ℕ}
    (mentionsT : t.Mentions (.var w)) : s.Mentions (.var w) := by
  by_contra unmentioned
  have equivalent := equivalent_of_congruent related
  obtain ⟨b, σ, solved⟩ := solvable
  cases b
  -- No row of the right is labelled `w`.
  obtain ⟨π, image, labels⟩ := rows_of_congruent boundP' related ⟨PUnit.unit, σ, solved⟩
  have noRow : ∀ o ∈ t.present, t.label o ≠ .var w := by
    intro o present same
    rw [← image] at present
    obtain ⟨o', present', rfl⟩ := Finset.mem_map.mp present
    have other : s.label o' ≠ .var w := by
      intro same'
      apply unmentioned
      rw [← same']
      exact Or.inr (Or.inr ⟨o', present', rfl⟩)
    let g : Term atoms := .const (size (Subst.applyTerm σ (s.label o')))
    have moved := labels o' present' (Function.update σ w g) (models_update unmentioned solved g)
    rw [applyTerm_update_of_ne σ g other] at moved
    have atW : Subst.applyTerm (Function.update σ w g) (t.label (π.toEmbedding o')) = g := by
      rw [same]
      exact Function.update_self w g σ
    exact ne_const_size _ (moved.trans atW)
  -- The left opens the unknown of the rule that tells `x = 5` as `w`.
  have relatedA : Cong ⟨P ∪ ({tellX} ∪ {idle}), s⟩ ⟨P' ∪ ({tellX} ∪ {idle}), t⟩ :=
    related.addRules ({tellX} ∪ {idle})
  let lf : Firing ℕ E (P ∪ ({tellX} ∪ {idle})) s.frame :=
    ⟨tellX, Or.inr (Or.inl rfl), PUnit.unit, fun _ => .var w, ⟨[], [], []⟩, []⟩
  have admittedL : lf.Admits X s := by
    refine (admits_iff lf).mpr ⟨?_, ⟨List.nodup_nil, List.nodup_nil, rfl, rfl, rfl, rfl⟩, ?_, ?_,
      fun check inside => absurd inside List.not_mem_nil,
      fun q inside => absurd inside List.not_mem_nil⟩
    · refine fresh_at lf unmentioned (fun v inside => ?_) rfl
      simp [lf, tellX, Rule.terms, x, c] at inside
      exact inside
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [lf, Selection.commit]
      · simp [lf, Selection.commit]
      · simp [lf, Selection.commit]
      · simp [lf, Selection.commit]
      · intro q inside
        simp [lf, Selection.commit] at inside
    · refine ⟨PUnit.unit, Function.update σ w (c 5), fun e inside => ?_⟩
      rcases (mem_information lf).mp inside with old | take | read | told
      · obtain ⟨e', member, rfl⟩ := List.mem_map.mp old
        have h := models_update unmentioned solved (c 5) e' member
        show Subst.applyTerm (Function.update σ w (c 5)) (Subst.applyTerm (Subst.id atoms) e'.1) =
          Subst.applyTerm (Function.update σ w (c 5)) (Subst.applyTerm (Subst.id atoms) e'.2)
        rw [Subst.applyTerm_id, Subst.applyTerm_id]
        exact h
      · obtain ⟨p, o, paired, -⟩ := (mem_matching lf).mp take
        exact absurd paired List.not_mem_nil
      · obtain ⟨p, o, paired, -⟩ := (mem_matching lf).mp read
        exact absurd paired List.not_mem_nil
      · have isTell : e = (.var w, c 5) := List.mem_singleton.mp told
        subst isTell
        exact Function.update_self w (c 5) σ
  -- The right answers with some firing `h`.
  obtain ⟨T', moved, relatedR⟩ := candidate_congruent.reduces relatedA (reduces_of_admits lf admittedL)
  obtain ⟨program, h, admittedH, reached⟩ := moved
  have reached' : h.result X t = T'.state := reached
  -- A context tells `w = 6`.
  have relatedTold := relatedR.tell fun _ => [(.var w, c 6)]
  have leftStuck : ¬ X.Solvable (a := PUnit.unit) (tellState (lf.result X s) [(.var w, c 6)]).knowledge := by
    rintro ⟨b, τ, solvedτ⟩
    cases b
    obtain ⟨known, told⟩ := (Frames.models_append _ _ _).mp solvedτ
    have tellMember : ((Term.var w : Term atoms), c 5) ∈ lf.information X s :=
      (mem_information (X := X) lf).mpr (Or.inr (Or.inr (Or.inr (by
        show ((Term.var w : Term atoms), c 5) ∈ [((Term.var w : Term atoms), c 5)]
        exact List.mem_singleton_self _))))
    have five : τ w = c 5 := known ((Term.var w : Term atoms), c 5) tellMember
    have six : τ w = c 6 := told ((Term.var w : Term atoms), c 6) (List.mem_singleton_self _)
    exact absurd (Term.const.inj (five.symm.trans six)) (by decide)
  have rightSolvable : X.Solvable (a := PUnit.unit) (tellState T'.state [(.var w, c 6)]).knowledge := by
    rw [← reached']
    obtain ⟨b, σh, solvedH⟩ := admittedH.2.2.1
    cases b
    obtain ⟨fresh, -⟩ := admittedH.1
    have enabled := admittedH.2.1
    have takenPresent : ∀ o ∈ h.selection.taken, o ∈ t.present := fun o member =>
      enabled.taken_subset (by simpa [Selection.commit] using member)
    have readPresent : ∀ o ∈ h.selection.read, o ∈ t.present := fun o member =>
      enabled.kept_subset (by simpa [Selection.commit] using member)
    have rowNe : ∀ o ∈ t.present, h.row X t o ≠ .var w := fun o present => by
      show Subst.applyTerm (Subst.id atoms) (t.label o) ≠ .var w
      rw [Subst.applyTerm_id]
      exact noRow o present
    have openedNe : ∀ q ∈ h.rule.terms, Subst.applyTerm h.opening q ≠ .var w := fun q inside =>
      opened_ne_var h fresh inside mentionsT
    refine ⟨PUnit.unit, Function.update σh w (c 6),
      (Frames.models_append _ _ _).mpr ⟨fun e inside => ?_, ?_⟩⟩
    · rcases (mem_information h).mp inside with old | take | read | told
      · -- The right knowledge: `w` is free in it, as in the left one.
        obtain ⟨e', member, rfl⟩ := List.mem_map.mp old
        have knownT : X.Models (a := PUnit.unit) (b := PUnit.unit) σh t.knowledge := by
          intro e'' member''
          have transported := solvedH _ ((mem_information h).mpr
            (Or.inl (List.mem_map_of_mem member'')))
          have transported' : Subst.applyTerm σh (Subst.applyTerm (Subst.id atoms) e''.1) =
              Subst.applyTerm σh (Subst.applyTerm (Subst.id atoms) e''.2) := transported
          rw [Subst.applyTerm_id, Subst.applyTerm_id] at transported'
          exact transported'
        have knownS := (equivalent PUnit.unit σh).mpr knownT
        have movedT := (equivalent PUnit.unit (Function.update σh w (c 6))).mp (models_update unmentioned knownS (c 6))
        have h' : Subst.applyTerm (Function.update σh w (c 6)) e'.1 = Subst.applyTerm (Function.update σh w (c 6)) e'.2 := movedT e' member
        show Subst.applyTerm (Function.update σh w (c 6)) (Subst.applyTerm (Subst.id atoms) e'.1) =
          Subst.applyTerm (Function.update σh w (c 6)) (Subst.applyTerm (Subst.id atoms) e'.2)
        rw [Subst.applyTerm_id, Subst.applyTerm_id]
        exact h'
      · obtain ⟨p, o, paired, rfl⟩ := (mem_matching h).mp take
        have original : Subst.applyTerm σh p = Subst.applyTerm σh (h.row X t o) :=
          solvedH _ inside
        obtain ⟨q, member, rfl⟩ := List.mem_map.mp (List.of_mem_zip paired).1
        have one := openedNe q (AtOneFrame.mem_terms (Or.inl member))
        have two := rowNe o (takenPresent o (List.of_mem_zip paired).2)
        show Subst.applyTerm (Function.update σh w (c 6)) (Subst.applyTerm h.opening q) = Subst.applyTerm (Function.update σh w (c 6)) (h.row X t o)
        rw [applyTerm_update_of_ne σh (c 6) one, applyTerm_update_of_ne σh (c 6) two]
        exact original
      · obtain ⟨p, o, paired, rfl⟩ := (mem_matching h).mp read
        have original : Subst.applyTerm σh p = Subst.applyTerm σh (h.row X t o) :=
          solvedH _ inside
        obtain ⟨q, member, rfl⟩ := List.mem_map.mp (List.of_mem_zip paired).1
        have one := openedNe q (AtOneFrame.mem_terms (Or.inr (Or.inl member)))
        have two := rowNe o (readPresent o (List.of_mem_zip paired).2)
        show Subst.applyTerm (Function.update σh w (c 6)) (Subst.applyTerm h.opening q) = Subst.applyTerm (Function.update σh w (c 6)) (h.row X t o)
        rw [applyTerm_update_of_ne σh (c 6) one, applyTerm_update_of_ne σh (c 6) two]
        exact original
      · have original : Subst.applyTerm σh e.1 = Subst.applyTerm σh e.2 := solvedH _ inside
        obtain ⟨e', member, rfl⟩ := List.mem_map.mp told
        have one := openedNe e'.1 (AtOneFrame.mem_terms (Or.inr (Or.inr (Or.inl
          (List.mem_map_of_mem member)))))
        have two := openedNe e'.2 (AtOneFrame.mem_terms (Or.inr (Or.inr (Or.inr (Or.inl
          (List.mem_map_of_mem member))))))
        show Subst.applyTerm (Function.update σh w (c 6)) (Subst.applyTerm h.opening e'.1) =
          Subst.applyTerm (Function.update σh w (c 6)) (Subst.applyTerm h.opening e'.2)
        rw [applyTerm_update_of_ne σh (c 6) one, applyTerm_update_of_ne σh (c 6) two]
        exact original
    · intro e inside
      have isTell : e = ((Term.var w : Term atoms), c 6) := List.mem_singleton.mp inside
      subst isTell
      exact Function.update_self w (c 6) σh
  -- The right moves by the rule that does nothing; the left cannot move.
  have rightMoves : Moves ⟨T'.program, tellState T'.state [(.var w, c 6)]⟩ := by
    rw [program]
    exact idle_moves (Set.mem_union_right _ (Set.mem_union_right _ (Set.mem_singleton _))) _
      rightSolvable
  exact stuck_of_unsolvable (S := ⟨P ∪ ({tellX} ∪ {idle}), tellState (lf.result X s)
    [(.var w, c 6)]⟩) leftStuck (relatedTold.symm.moves rightMoves)

/-! ## The characterization -/

/-- At one frame, two instantiations agree on what a state mentions exactly when they agree on the
unknowns it mentions. -/
theorem supports_iff_vars (s : State Tm ℕ) (φ ψ : Subst atoms) :
    Supports X (b := PUnit.unit) s φ ψ ↔ ∀ w, s.Mentions (.var w) → φ w = ψ w := by
  constructor
  · intro agree w mentions
    exact agree (.var w) mentions
  · intro agree t mentions
    cases t with
    | var w => exact agree w mentions
    | const _ => rfl
    | app fn _ => exact nomatch fn

/-- **Congruent states are statically equivalent**, beside any two programs that leave a constant
unused. -/
theorem static_of_congruent {P P' : Program Tm} (boundP : Bounded P) (boundP' : Bounded P')
    {s t : State Tm ℕ} (related : Cong ⟨P, s⟩ ⟨P', t⟩) : Static s t := by
  have equivalent := equivalent_of_congruent related
  by_cases solvable : X.Solvable (a := PUnit.unit) s.knowledge
  · right
    have solvableT : X.Solvable (a := PUnit.unit) t.knowledge :=
      (Frames.Equivalent.solvable_iff equivalent).mp solvable
    obtain ⟨π, image, labels⟩ := rows_of_congruent boundP' related solvable
    have mentionsIff : ∀ w, s.Mentions (.var w) ↔ t.Mentions (.var w) := fun w =>
      ⟨mentions_of_congruent boundP related.symm solvableT,
        mentions_of_congruent boundP' related solvable⟩
    obtain ⟨tf, tk, tp, tl⟩ := t
    simp only at image
    subst image
    refine ⟨π, tk, tl, ⟨equivalent, fun o inside b δ solved => ?_, fun b φ ψ => ?_⟩, rfl⟩
    · have back : π.symm o ∈ s.present := Finset.mem_map_equiv.mp inside
      have agree := labels (π.symm o) back δ solved
      rw [Equiv.apply_symm_apply] at agree
      exact agree
    · cases b
      show Supports X (renameState π s) φ ψ ↔
        Supports X (⟨(renameState π s).frame, tk, (renameState π s).present, tl⟩ : State Tm ℕ) φ ψ
      rw [supports_iff_vars, supports_iff_vars]
      have sameT : ∀ w, (⟨(renameState π s).frame, tk, (renameState π s).present, tl⟩ :
          State Tm ℕ).Mentions (.var w) ↔ (⟨tf, tk, s.present.map π.toEmbedding, tl⟩ :
          State Tm ℕ).Mentions (.var w) := fun w => Iff.rfl
      constructor
      · intro agree w mentions
        exact agree w ((mentions_renameState π s _).mpr ((mentionsIff w).mpr ((sameT w).mp mentions)))
      · intro agree w mentions
        exact agree w ((sameT w).mpr ((mentionsIff w).mp ((mentions_renameState π s _).mp mentions)))
  · left
    exact ⟨solvable, fun solvableT => solvable ((Frames.Equivalent.solvable_iff equivalent).mpr
      solvableT)⟩

/-- **The characterization of the congruence of states**: beside a program that leaves a constant
unused, two states are congruent exactly when they are statically equivalent. -/
theorem congruent_iff_static {P : Program Tm} (bounded : Bounded P) (s t : State Tm ℕ) :
    Cong ⟨P, s⟩ ⟨P, t⟩ ↔ Static s t :=
  ⟨static_of_congruent bounded bounded, congruent_of_static P⟩

/-- **With no rules, congruence is exactly the static equivalence.** -/
theorem static_iff (s t : State Tm ℕ) : Cong ⟨∅, s⟩ ⟨∅, t⟩ ↔ Static s t :=
  congruent_iff_static bounded_empty s t

#print axioms countAt_eq_of_congruent
#print axioms rows_of_congruent
#print axioms ne_const_size
#print axioms opened_ne_var
#print axioms mentions_of_congruent
#print axioms supports_iff_vars
#print axioms static_of_congruent
#print axioms congruent_iff_static
#print axioms static_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization
