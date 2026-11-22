import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Congruence
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.CheckAccepts

/-!
# States equivalent modulo the knowledge are congruent, given the same support

## Support

A firing's opening must be fresh: it must realize every instantiation of the state's frame on the
terms the state mentions together with every instantiation of the rule (`Firing.Fresh`). So what a
state mentions matters, through which instantiations agree on it (`Supports`): its **support**.

## Law 2

Two states are **equivalent modulo the knowledge** (`ModuloAt`, `Modulo`) when they have the same
frame and present rows, knowledge with the same solutions in every later frame, labels of present rows
equal at every solution of the knowledge, and the same support.

* Freshness depends on a state only through its support (`fresh_iff_of_support`).
* A result's support is the source's support along the extension together with the opened rule's
  terms that the result keeps: patterns, tells and made rows (`supports_result`).
* The same firing is admitted at both states and its results are again equivalent modulo the
  knowledge (`modulo_step`); every context preserves the relation (`modulo_apply`); may- and
  must-barbs cannot tell such states apart (`mayBarb_modulo`, `mustBarb_modulo`).
* **Law 2** (`modulo_congruent`, `modulo_congruent_mayBarb`): such states are congruent with every
  program. Instances: labels of absent identities are unobservable (`offPresent_congruent`); a row may
  be replaced by any label the knowledge equates with it, and the knowledge by any store with the same
  solutions, as long as the support stays.
* The support hypothesis is needed: at one frame, the empty knowledge and the knowledge `y = y` have
  the same solutions and are separated by a program with one fresh unknown and a context that names
  `y` (`AtOneFrame.support_separates`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)

universe uO uT uH uE uOcc uB

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

/-! ## Lists -/

theorem exists_zip_left {α : Type uT} {β : Type uOcc} :
    ∀ (l₁ : List α) (l₂ : List β), l₁.length = l₂.length → ∀ a ∈ l₁, ∃ b, (a, b) ∈ l₁.zip l₂
  | [], _, _, _, inside => by cases inside
  | _ :: _, [], lengths, _, _ => by simp at lengths
  | a' :: as, b :: bs, lengths, a, inside => by
      rcases List.mem_cons.mp inside with rfl | later
      · exact ⟨b, List.mem_cons_self⟩
      · obtain ⟨b', paired⟩ := exists_zip_left as bs (Nat.succ.inj lengths) a later
        exact ⟨b', List.mem_cons_of_mem _ paired⟩

theorem exists_zip_right {α : Type uT} {β : Type uOcc} :
    ∀ (l₁ : List α) (l₂ : List β), l₁.length = l₂.length → ∀ b ∈ l₂, ∃ a, (a, b) ∈ l₁.zip l₂
  | [], [], _, _, inside => by cases inside
  | [], _ :: _, lengths, _, _ => by simp at lengths
  | _ :: _, [], _, _, inside => by cases inside
  | a :: as, b' :: bs, lengths, b, inside => by
      rcases List.mem_cons.mp inside with rfl | later
      · exact ⟨a, List.mem_cons_self⟩
      · obtain ⟨a', paired⟩ := exists_zip_right as bs (Nat.succ.inj lengths) b later
        exact ⟨a', List.mem_cons_of_mem _ paired⟩

section Relabel

variable {O : Type uOcc} [DecidableEq O]

/-- A made identity's new label is one of the made rows. -/
theorem relabel_mem {a : Obj} (old : O → Tm a) :
    ∀ (made : List O) (rows : List (Tm a)) (o : O), made.length = rows.length → o ∈ made →
      relabel old made rows o ∈ rows
  | [], _, _, _, inside => by cases inside
  | _ :: _, [], _, lengths, _ => by simp at lengths
  | m :: rest, t :: ts, o, lengths, inside => by
      simp only [relabel]
      split_ifs with same
      · exact List.mem_cons_self
      · have later : o ∈ rest := by
          rcases List.mem_cons.mp inside with rfl | later
          · exact absurd rfl same
          · exact later
        exact List.mem_cons_of_mem _ (relabel_mem old rest ts o (Nat.succ.inj lengths) later)

/-- A made identity's new label does not depend on the old labels. -/
theorem relabel_eq_of_mem {a : Obj} (old old' : O → Tm a) :
    ∀ (made : List O) (rows : List (Tm a)) (o : O), made.length = rows.length → o ∈ made →
      relabel old made rows o = relabel old' made rows o
  | [], _, _, _, inside => by cases inside
  | _ :: _, [], _, lengths, _ => by simp at lengths
  | m :: rest, t :: ts, o, lengths, inside => by
      simp only [relabel]
      split_ifs with same
      · rfl
      · have later : o ∈ rest := by
          rcases List.mem_cons.mp inside with rfl | later
          · exact absurd rfl same
          · exact later
        exact relabel_eq_of_mem old old' rest ts o (Nat.succ.inj lengths) later

variable {X : Frames Tm Hom}

/-- Made identities agree after relabelling, whatever the old labels. -/
theorem E_relabel_of_mem {a b : Obj} (σ : Hom a b) (old old' : O → Tm a) (made : List O)
    (rows : List (Tm a)) (o : O) (lengths : made.length = rows.length) (inside : o ∈ made) :
    X.E (X.act σ (relabel old made rows o)) (X.act σ (relabel old' made rows o)) := by
  rw [relabel_eq_of_mem old old' made rows o lengths inside]
  exact (X.equivalence b).refl _

omit [DecidableEq O] in
/-- Agreement along a composite is agreement after acting twice. -/
theorem E_comp_iff {a m b : Obj} (σ : Hom m b) (w : Hom a m) (t t' : Tm a) :
    X.E (X.act (X.comp σ w) t) (X.act (X.comp σ w) t') ↔
      X.E (X.act σ (X.act w t)) (X.act σ (X.act w t')) := by
  rw [X.act_comp, X.act_comp]

omit [DecidableEq O] in
/-- A choice between a shared term and two agreeing terms agrees. -/
theorem E_ite {a b : Obj} (σ : Hom a b) (c : Prop) [Decidable c] (x y y' : Tm a)
    (agree : ¬ c → X.E (X.act σ y) (X.act σ y')) :
    X.E (X.act σ (if c then x else y)) (X.act σ (if c then x else y')) := by
  by_cases holds : c
  · rw [if_pos holds, if_pos holds]
    exact (X.equivalence b).refl _
  · rw [if_neg holds, if_neg holds]
    exact agree holds

/-- Other identities agree after relabelling when their old labels agree. -/
theorem E_relabel_of_not_mem {a b : Obj} (σ : Hom a b) (old old' : O → Tm a) (made : List O)
    (rows : List (Tm a)) (o : O) (notMade : o ∉ made)
    (agree : X.E (X.act σ (old o)) (X.act σ (old' o))) :
    X.E (X.act σ (relabel old made rows o)) (X.act σ (relabel old' made rows o)) := by
  rw [Firing.relabel_of_not_mem old made rows notMade, Firing.relabel_of_not_mem old' made rows notMade]
  exact agree

end Relabel

/-! ## Support -/

section Support

variable (X : Frames Tm Hom) {O : Type uOcc}

/-- **Two instantiations agree on what a state mentions.** -/
def Supports (s : State Tm O) {b : Obj} (φ ψ : Hom s.frame b) : Prop :=
  ∀ t, s.Mentions t → X.E (X.act φ t) (X.act ψ t)

variable {X} {E : Extensions.{uO, uH, uE} Hom}

/-- **Freshness depends on a state only through its support.** -/
theorem fresh_iff_of_support {P : Program Tm} {s : State Tm O} {K : EquationStore (Tm s.frame)}
    {W : Finset O} {ℓ : O → Tm s.frame}
    (same : ∀ (b : Obj) (φ ψ : Hom s.frame b), Supports X s φ ψ ↔ Supports X ⟨s.frame, K, W, ℓ⟩ φ ψ)
    (f : Firing O E P s.frame) : f.Fresh X s ↔ f.Fresh X ⟨s.frame, K, W, ℓ⟩ := by
  constructor
  · intro fresh b g h
    obtain ⟨u, state, rule⟩ := fresh b g h
    refine ⟨u, ?_, rule⟩
    have agree : Supports X s (X.comp u (E.weaken f.ext)) g := fun t mentioned => by
      rw [X.act_comp]
      exact state t mentioned
    intro t mentioned
    have moved := (same b _ g).mp agree t mentioned
    rw [X.act_comp] at moved
    exact moved
  · intro fresh b g h
    obtain ⟨u, state, rule⟩ := fresh b g h
    refine ⟨u, ?_, rule⟩
    have agree : Supports X (⟨s.frame, K, W, ℓ⟩ : State Tm O) (X.comp u (E.weaken f.ext)) g :=
      fun t mentioned => by
        rw [X.act_comp]
        exact state t mentioned
    intro t mentioned
    have moved := (same b _ g).mpr agree t mentioned
    rw [X.act_comp] at moved
    exact moved

variable [DecidableEq O]

/-- The opened rule's terms that a result keeps: patterns, tells and made rows. -/
def resultTerms (X : Frames Tm Hom) {P : Program Tm} {a : Obj} (f : Firing O E P a) :
    List (Tm (E.target f.ext)) :=
  (f.opened X).take ++ (f.opened X).read ++ (f.opened X).tell.map Prod.fst ++
    (f.opened X).tell.map Prod.snd ++ (f.opened X).produce

omit [DecidableEq O] in
theorem mem_matching {P : Program Tm} {s : State Tm O} (f : Firing O E P s.frame)
    {patterns : List (Tm (E.target f.ext))} {selected : List O}
    {e : Equation (Tm (E.target f.ext))} :
    e ∈ f.matching X s patterns selected ↔
      ∃ p o, (p, o) ∈ patterns.zip selected ∧ e = (p, f.row X s o) := by
  unfold Firing.matching
  rw [← List.map_uncurry_zip_eq_zipWith, List.mem_map]
  constructor
  · rintro ⟨⟨p, o⟩, inside, rfl⟩
    exact ⟨p, o, inside, rfl⟩
  · rintro ⟨p, o, inside, rfl⟩
    exact ⟨(p, o), inside, rfl⟩

omit [DecidableEq O] in
theorem mem_information {P : Program Tm} {s : State Tm O} (f : Firing O E P s.frame)
    {e : Equation (Tm (E.target f.ext))} :
    e ∈ f.information X s ↔ e ∈ X.applyStore (E.weaken f.ext) s.knowledge ∨
      e ∈ f.matching X s (f.opened X).take f.selection.taken ∨
      e ∈ f.matching X s (f.opened X).read f.selection.read ∨ e ∈ (f.opened X).tell := by
  unfold Firing.information
  simp only [List.mem_append]
  tauto

/-- **The support of a result**: the source's support along the extension, and the opened rule's
terms that the result keeps. -/
theorem supports_result {P : Program Tm} {s : State Tm O} {f : Firing O E P s.frame}
    (shapes : f.Shapes X s) (enabled : Enabled (fun _ : O => ()) s.present (f.selection.commit (T := Unit)))
    {b : Obj} (φ ψ : Hom (E.target f.ext) b) :
    Supports X (f.result X s) φ ψ ↔
      Supports X s (X.comp φ (E.weaken f.ext)) (X.comp ψ (E.weaken f.ext)) ∧
        ∀ u ∈ resultTerms X f, X.E (X.act φ u) (X.act ψ u) := by
  obtain ⟨-, -, -, takeLength, readLength, produceLength, -⟩ := id shapes
  have takeLength' : (f.opened X).take.length = f.selection.taken.length := by
    rw [← takeLength]
    exact List.length_map _
  have readLength' : (f.opened X).read.length = f.selection.read.length := by
    rw [← readLength]
    exact List.length_map _
  have produceLength' : f.selection.made.length = (f.opened X).produce.length := by
    rw [← produceLength]
    exact (List.length_map _).symm
  have takenPresent : ∀ o ∈ f.selection.taken, o ∈ s.present := fun o member =>
    enabled.taken_subset (by simpa [Selection.commit] using member)
  have readPresent : ∀ o ∈ f.selection.read, o ∈ s.present := fun o member =>
    enabled.kept_subset (by simpa [Selection.commit] using member)
  have madeAbsent : ∀ o ∈ f.selection.made, o ∉ s.present := fun o member present =>
    Finset.disjoint_left.mp enabled.fresh (by simpa [Selection.commit] using member) present
  have weaken : ∀ (t : Tm s.frame), X.E (X.act φ (X.act (E.weaken f.ext) t))
      (X.act ψ (X.act (E.weaken f.ext) t)) ↔
      X.E (X.act (X.comp φ (E.weaken f.ext)) t) (X.act (X.comp ψ (E.weaken f.ext)) t) := by
    intro t
    rw [X.act_comp, X.act_comp]
  -- A result mentions the information's sides and the labels of its present rows.
  have mentionedFst : ∀ e ∈ f.information X s, (f.result X s).Mentions e.1 :=
    fun e member => Or.inl (List.mem_map_of_mem member)
  have mentionedSnd : ∀ e ∈ f.information X s, (f.result X s).Mentions e.2 :=
    fun e member => Or.inr (Or.inl (List.mem_map_of_mem member))
  constructor
  · intro supports
    refine ⟨?_, ?_⟩
    · intro t mentioned
      rw [← weaken]
      rcases mentioned with inFst | inSnd | ⟨o, present, rfl⟩
      · obtain ⟨e, inside, rfl⟩ := List.mem_map.mp inFst
        exact supports _ (mentionedFst _ ((mem_information f).mpr
          (Or.inl (List.mem_map_of_mem inside))))
      · obtain ⟨e, inside, rfl⟩ := List.mem_map.mp inSnd
        exact supports _ (mentionedSnd _ ((mem_information f).mpr
          (Or.inl (List.mem_map_of_mem inside))))
      · by_cases taken : o ∈ f.selection.taken
        · obtain ⟨p, paired⟩ := exists_zip_right _ _ takeLength' o taken
          exact supports _ (mentionedSnd (p, f.row X s o) ((mem_information f).mpr
            (Or.inr (Or.inl ((mem_matching f).mpr ⟨p, o, paired, rfl⟩)))))
        · have survives : o ∈ fire s.present (f.selection.commit (T := Unit)) :=
            mem_fire.mpr (Or.inl ⟨present, by simpa [Selection.commit] using taken⟩)
          have notMade : o ∉ f.selection.made := fun made => madeAbsent o made present
          have label : (f.result X s).label o = f.row X s o :=
            Firing.result_label_other f notMade
          exact supports _ (Or.inr (Or.inr ⟨o, survives, label⟩))
    · intro u inside
      unfold resultTerms at inside
      simp only [List.mem_append] at inside
      rcases inside with (((take | read) | told) | told) | made
      · obtain ⟨o, paired⟩ := exists_zip_left _ _ takeLength' u take
        exact supports _ (mentionedFst (u, f.row X s o) ((mem_information f).mpr
          (Or.inr (Or.inl ((mem_matching f).mpr ⟨u, o, paired, rfl⟩)))))
      · obtain ⟨o, paired⟩ := exists_zip_left _ _ readLength' u read
        exact supports _ (mentionedFst (u, f.row X s o) ((mem_information f).mpr
          (Or.inr (Or.inr (Or.inl ((mem_matching f).mpr ⟨u, o, paired, rfl⟩))))))
      · obtain ⟨e, inside, rfl⟩ := List.mem_map.mp told
        exact supports _ (mentionedFst e ((mem_information f).mpr (Or.inr (Or.inr (Or.inr inside)))))
      · obtain ⟨e, inside, rfl⟩ := List.mem_map.mp told
        exact supports _ (mentionedSnd e ((mem_information f).mpr (Or.inr (Or.inr (Or.inr inside)))))
      · obtain ⟨m, paired⟩ := exists_zip_right _ _ produceLength' u made
        have isMade : m ∈ f.selection.made := (List.of_mem_zip paired).1
        have survives : m ∈ fire s.present (f.selection.commit (T := Unit)) :=
          mem_fire.mpr (Or.inr (by simpa [Selection.commit] using isMade))
        exact supports _ (Or.inr (Or.inr ⟨m, survives, Firing.result_label_made f shapes paired⟩))
  · rintro ⟨supports, opened⟩ t mentioned
    have keep : ∀ u ∈ resultTerms X f, X.E (X.act φ u) (X.act ψ u) := opened
    unfold resultTerms at keep
    simp only [List.mem_append] at keep
    rcases mentioned with inFst | inSnd | ⟨o, survives, rfl⟩
    · obtain ⟨e, inside, rfl⟩ := List.mem_map.mp inFst
      rcases (mem_information f).mp inside with old | take | read | told
      · obtain ⟨original, member, rfl⟩ := List.mem_map.mp old
        exact (weaken _).mpr (supports _ (Or.inl (List.mem_map_of_mem member)))
      · obtain ⟨p, o, paired, rfl⟩ := (mem_matching f).mp take
        exact keep p (Or.inl (Or.inl (Or.inl (Or.inl (List.of_mem_zip paired).1))))
      · obtain ⟨p, o, paired, rfl⟩ := (mem_matching f).mp read
        exact keep p (Or.inl (Or.inl (Or.inl (Or.inr (List.of_mem_zip paired).1))))
      · exact keep _ (Or.inl (Or.inl (Or.inr (List.mem_map_of_mem told))))
    · obtain ⟨e, inside, rfl⟩ := List.mem_map.mp inSnd
      rcases (mem_information f).mp inside with old | take | read | told
      · obtain ⟨original, member, rfl⟩ := List.mem_map.mp old
        exact (weaken _).mpr (supports _ (Or.inr (Or.inl (List.mem_map_of_mem member))))
      · obtain ⟨p, o, paired, rfl⟩ := (mem_matching f).mp take
        exact (weaken _).mpr (supports _ (Or.inr (Or.inr
          ⟨o, takenPresent o (List.of_mem_zip paired).2, rfl⟩)))
      · obtain ⟨p, o, paired, rfl⟩ := (mem_matching f).mp read
        exact (weaken _).mpr (supports _ (Or.inr (Or.inr
          ⟨o, readPresent o (List.of_mem_zip paired).2, rfl⟩)))
      · exact keep _ (Or.inl (Or.inr (List.mem_map_of_mem told)))
    · by_cases made : o ∈ f.selection.made
      · exact keep _ (Or.inr (relabel_mem (f.row X s) _ _ o produceLength' made))
      · have present : o ∈ s.present := by
          rcases mem_fire.mp survives with ⟨present, -⟩ | isMade
          · exact present
          · exact absurd (by simpa [Selection.commit] using isMade) made
        show X.E (X.act φ (relabel (f.row X s) f.selection.made (f.opened X).produce o))
          (X.act ψ (relabel (f.row X s) f.selection.made (f.opened X).produce o))
        rw [Firing.relabel_of_not_mem (f.row X s) _ _ made]
        exact (weaken _).mpr (supports _ (Or.inr (Or.inr ⟨o, present, rfl⟩)))

end Support

/-! ## Equivalence modulo the knowledge -/

section Modulo

variable (X : Frames Tm Hom) {O : Type uOcc}

/-- **Equivalent modulo the knowledge**, as a relation between a state and new knowledge and labels
at its frame, with its present rows: the same solutions, labels of present rows equal at every
solution, and the same support. -/
structure ModuloAt (s : State Tm O) (K : EquationStore (Tm s.frame)) (ℓ : O → Tm s.frame) : Prop where
  equivalent : X.Equivalent s.knowledge K
  labels : ∀ o ∈ s.present,
    X.Entails s.knowledge (fun _ σ => X.E (X.act σ (s.label o)) (X.act σ (ℓ o)))
  support : ∀ (b : Obj) (φ ψ : Hom s.frame b),
    Supports X s φ ψ ↔ Supports X ⟨s.frame, K, s.present, ℓ⟩ φ ψ

/-- **States equivalent modulo the knowledge.** -/
def Modulo (s t : State Tm O) : Prop :=
  ∃ (K : EquationStore (Tm s.frame)) (ℓ : O → Tm s.frame),
    ModuloAt X s K ℓ ∧ t = ⟨s.frame, K, s.present, ℓ⟩

variable {X}

theorem Modulo.symm {s t : State Tm O} (modulo : Modulo X s t) : Modulo X t s := by
  obtain ⟨K, ℓ, ⟨equivalent, labels, support⟩, rfl⟩ := modulo
  refine ⟨s.knowledge, s.label, ⟨fun b σ => (equivalent b σ).symm, fun o present b σ solved => ?_,
    fun b φ ψ => (support b φ ψ).symm⟩, rfl⟩
  exact (X.equivalence b).symm (labels o present b σ ((equivalent b σ).mpr solved))

theorem Modulo.refl (s : State Tm O) : Modulo X s s :=
  ⟨s.knowledge, s.label, ⟨fun _ _ => Iff.rfl, fun _ _ b _ _ => (X.equivalence b).refl _,
    fun _ _ _ => Iff.rfl⟩, rfl⟩

/-- **May-barbs cannot tell states equivalent modulo the knowledge apart.** -/
theorem mayBarb_modulo {s t : State Tm O} (modulo : Modulo X s t) (p : Pattern Tm) :
    MayBarb X p s → MayBarb X p t := by
  obtain ⟨K, ℓ, ⟨equivalent, labels, -⟩, rfl⟩ := modulo
  rintro ⟨o, present, b, σ, h, known, equated⟩
  exact ⟨o, present, b, σ, h, (equivalent b σ).mp known,
    (X.equivalence b).trans ((X.equivalence b).symm (labels o present b σ known)) equated⟩

/-- **Must-barbs cannot tell states equivalent modulo the knowledge apart.** -/
theorem mustBarb_modulo {s t : State Tm O} (modulo : Modulo X s t) (p : Pattern Tm) :
    MustBarb X p s → MustBarb X p t := by
  obtain ⟨K, ℓ, ⟨equivalent, labels, -⟩, rfl⟩ := modulo
  rintro ⟨o, present, every⟩
  refine ⟨o, present, fun b σ known => ?_⟩
  have known' := (equivalent b σ).mpr known
  obtain ⟨h, equated⟩ := every b σ known'
  exact ⟨h, (X.equivalence b).trans ((X.equivalence b).symm (labels o present b σ known')) equated⟩

end Modulo

/-! ## A firing at states equivalent modulo the knowledge -/

section Step

variable {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {E : Extensions.{uO, uH, uE} Hom}

omit [DecidableEq O] in
theorem matchesAt_congr_rows {a b : Obj} (σ : Hom a b) {row row' : O → Tm a} {W : Finset O}
    (same : ∀ o ∈ W, X.E (X.act σ (row o)) (X.act σ (row' o))) (p : Tm a) :
    matchesAt X σ row W p = matchesAt X σ row' W p := by
  ext o
  rw [mem_matchesAt, mem_matchesAt]
  constructor
  · rintro ⟨present, equated⟩
    exact ⟨present, (X.equivalence b).trans equated (same o present)⟩
  · rintro ⟨present, equated⟩
    exact ⟨present, (X.equivalence b).trans equated ((X.equivalence b).symm (same o present))⟩

omit [DecidableEq O] in
theorem checkHolds_congr_rows {a b : Obj} (σ : Hom a b) {row row' : O → Tm a} {W : Finset O}
    (same : ∀ o ∈ W, X.E (X.act σ (row o)) (X.act σ (row' o))) (c : Check (Tm a)) :
    checkHolds X σ row W c ↔ checkHolds X σ row' W c := by
  cases c with
  | equal left right => exact Iff.rfl
  | predicate quantifier pattern =>
      rw [checkHolds_predicate_iff, checkHolds_predicate_iff, matchesAt_congr_rows σ same]
  | count pattern number =>
      show (matchesAt X σ row W pattern).card = number ↔ (matchesAt X σ row' W pattern).card = number
      rw [matchesAt_congr_rows σ same]

variable {P : Program Tm}

/-- **One firing at states equivalent modulo the knowledge**: admitted at both, with results equivalent
modulo the knowledge. -/
theorem modulo_step {s : State Tm O} {K : EquationStore (Tm s.frame)} {ℓ : O → Tm s.frame}
    (modulo : ModuloAt X s K ℓ) (f : Firing O E P s.frame) (admitted : f.Admits X s) :
    f.Admits X ⟨s.frame, K, s.present, ℓ⟩ ∧
      Modulo X (f.result X s) (f.result X ⟨s.frame, K, s.present, ℓ⟩) := by
  obtain ⟨equivalent, labels, support⟩ := modulo
  obtain ⟨⟨fresh, lengths⟩, enabled, solvable, asks⟩ := admitted
  let t : State Tm O := ⟨s.frame, K, s.present, ℓ⟩
  have takenPresent : ∀ o ∈ f.selection.taken, o ∈ s.present := fun o member =>
    enabled.taken_subset (by simpa [Selection.commit] using member)
  have readPresent : ∀ o ∈ f.selection.read, o ∈ s.present := fun o member =>
    enabled.kept_subset (by simpa [Selection.commit] using member)
  -- At a solution of either information, the rows of the two states agree.
  have rowsAgree : ∀ {b : Obj} (σ : Hom (E.target f.ext) b),
      X.Models (X.comp σ (E.weaken f.ext)) s.knowledge →
      ∀ o ∈ s.present, X.E (X.act σ (f.row X s o)) (X.act σ (f.row X t o)) := by
    intro b σ known o present
    have agree : X.E (X.act (X.comp σ (E.weaken f.ext)) (s.label o))
        (X.act (X.comp σ (E.weaken f.ext)) (ℓ o)) := labels o present b _ known
    rw [X.act_comp, X.act_comp] at agree
    exact agree
  have knownOf : ∀ {b : Obj} (σ : Hom (E.target f.ext) b),
      X.Models σ (X.applyStore (E.weaken f.ext) s.knowledge) ↔
        X.Models σ (X.applyStore (E.weaken f.ext) K) := by
    intro b σ
    rw [Frames.models_applyStore, Frames.models_applyStore]
    exact equivalent b _
  have infoEquivalent : X.Equivalent (f.information X s) (f.information X t) := by
    intro b σ
    constructor
    · intro solved e member
      have knownS : X.Models σ (X.applyStore (E.weaken f.ext) s.knowledge) :=
        fun e' inside => solved e' ((mem_information f).mpr (Or.inl inside))
      have known := (Frames.models_applyStore (E.weaken f.ext) σ s.knowledge).mp knownS
      rcases (mem_information (s := t) f).mp member with old | take | read | told
      · exact (knownOf σ).mp knownS e old
      · obtain ⟨p, o, paired, rfl⟩ := (mem_matching (s := t) f).mp take
        have here : X.E (X.act σ p) (X.act σ (f.row X s o)) := solved _ ((mem_information f).mpr
          (Or.inr (Or.inl ((mem_matching f).mpr ⟨p, o, paired, rfl⟩))))
        exact (X.equivalence b).trans here
          (rowsAgree σ known o (takenPresent o (List.of_mem_zip paired).2))
      · obtain ⟨p, o, paired, rfl⟩ := (mem_matching (s := t) f).mp read
        have here : X.E (X.act σ p) (X.act σ (f.row X s o)) := solved _ ((mem_information f).mpr
          (Or.inr (Or.inr (Or.inl ((mem_matching f).mpr ⟨p, o, paired, rfl⟩)))))
        exact (X.equivalence b).trans here
          (rowsAgree σ known o (readPresent o (List.of_mem_zip paired).2))
      · exact solved e ((mem_information f).mpr (Or.inr (Or.inr (Or.inr told))))
    · intro solved e member
      have knownT : X.Models σ (X.applyStore (E.weaken f.ext) K) :=
        fun e' inside => solved e' ((mem_information (s := t) f).mpr (Or.inl inside))
      have knownS := (knownOf σ).mpr knownT
      have known := (Frames.models_applyStore (E.weaken f.ext) σ s.knowledge).mp knownS
      rcases (mem_information f).mp member with old | take | read | told
      · exact knownS e old
      · obtain ⟨p, o, paired, rfl⟩ := (mem_matching f).mp take
        have here : X.E (X.act σ p) (X.act σ (f.row X t o)) := solved _
          ((mem_information (s := t) f).mpr
            (Or.inr (Or.inl ((mem_matching (s := t) f).mpr ⟨p, o, paired, rfl⟩))))
        exact (X.equivalence b).trans here ((X.equivalence b).symm
          (rowsAgree σ known o (takenPresent o (List.of_mem_zip paired).2)))
      · obtain ⟨p, o, paired, rfl⟩ := (mem_matching f).mp read
        have here : X.E (X.act σ p) (X.act σ (f.row X t o)) := solved _
          ((mem_information (s := t) f).mpr
            (Or.inr (Or.inr (Or.inl ((mem_matching (s := t) f).mpr ⟨p, o, paired, rfl⟩)))))
        exact (X.equivalence b).trans here ((X.equivalence b).symm
          (rowsAgree σ known o (readPresent o (List.of_mem_zip paired).2)))
      · exact solved e ((mem_information (s := t) f).mpr (Or.inr (Or.inr (Or.inr told))))
  -- At every solution of the information the guard predicates agree.
  have holdsIff : ∀ {b : Obj} (σ : Hom (E.target f.ext) b), X.Models σ (f.information X s) →
      (f.Holds X s σ ↔ f.Holds X t σ) := by
    intro b σ solved
    have knownS : X.Models σ (X.applyStore (E.weaken f.ext) s.knowledge) :=
      fun e' inside => solved e' ((mem_information f).mpr (Or.inl inside))
    have known := (Frames.models_applyStore (E.weaken f.ext) σ s.knowledge).mp knownS
    have rows := rowsAgree σ known
    apply and_congr
    · exact forall₂_congr fun c _ => checkHolds_congr_rows σ rows c
    · apply forall₂_congr
      intro q _
      show matchesAt X σ (f.row X s) s.present q.1 = q.2 ↔
        matchesAt X σ (f.row X t) s.present q.1 = q.2
      rw [matchesAt_congr_rows σ rows]
  have freshT : f.Fresh X t := (fresh_iff_of_support support f).mp fresh
  have shapesT : f.Shapes X t := ⟨freshT, lengths⟩
  refine ⟨⟨shapesT, enabled, (Frames.Equivalent.solvable_iff infoEquivalent).mp solvable, ?_⟩, ?_⟩
  · intro b σ solved
    exact (holdsIff σ ((infoEquivalent b σ).mpr solved)).mp (asks b σ ((infoEquivalent b σ).mpr solved))
  · refine ⟨f.information X t, relabel (f.row X t) f.selection.made (f.opened X).produce,
      ⟨infoEquivalent, ?_, ?_⟩, rfl⟩
    · intro o survives b σ solved
      have knownS : X.Models σ (X.applyStore (E.weaken f.ext) s.knowledge) :=
        fun e' inside => solved e' ((mem_information f).mpr (Or.inl inside))
      have known := (Frames.models_applyStore (E.weaken f.ext) σ s.knowledge).mp knownS
      have produceLength : f.selection.made.length = (f.opened X).produce.length := by
        rw [← lengths.2.2.2.2.1]
        exact (List.length_map _).symm
      by_cases made : o ∈ f.selection.made
      · exact E_relabel_of_mem σ (f.row X s) (f.row X t) _ _ o produceLength made
      · have present : o ∈ s.present := by
          rcases mem_fire.mp survives with ⟨present, -⟩ | isMade
          · exact present
          · exact absurd (by simpa [Selection.commit] using isMade) made
        exact E_relabel_of_not_mem σ (f.row X s) (f.row X t) _ _ o made
          (rowsAgree σ known o present)
    · intro b φ ψ
      rw [supports_result ⟨fresh, lengths⟩ enabled φ ψ]
      exact (and_congr (support b _ _) Iff.rfl).trans
        (supports_result (s := t) (f := f) shapesT enabled φ ψ).symm

end Step

/-! ## Contexts preserve equivalence modulo the knowledge -/

section Contexts

variable {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {E : Extensions.{uO, uH, uE} Hom}

theorem supports_addRows (s : State Tm O) (ids : Finset O) (label : O → Tm s.frame)
    (apart : Disjoint ids s.present) {b : Obj} (φ ψ : Hom s.frame b) :
    Supports X (addRows s ids label) φ ψ ↔
      Supports X s φ ψ ∧ ∀ o ∈ ids, X.E (X.act φ (label o)) (X.act ψ (label o)) := by
  constructor
  · intro supports
    refine ⟨fun t mentioned => ?_, fun o inside => ?_⟩
    · rcases mentioned with inFst | inSnd | ⟨o, present, rfl⟩
      · exact supports _ (Or.inl inFst)
      · exact supports _ (Or.inr (Or.inl inSnd))
      · have notNew : o ∉ ids := fun inIds => Finset.disjoint_left.mp apart inIds present
        have label' : (addRows s ids label).label o = s.label o := by
          simp [addRows, notNew]
        exact supports _ (Or.inr (Or.inr ⟨o, Finset.mem_union_left _ present, label'⟩))
    · have label' : (addRows s ids label).label o = label o := by
        simp [addRows, inside]
      exact supports _ (Or.inr (Or.inr ⟨o, Finset.mem_union_right _ inside, label'⟩))
  · rintro ⟨old, new⟩ t mentioned
    rcases mentioned with inFst | inSnd | ⟨o, present, rfl⟩
    · exact old _ (Or.inl inFst)
    · exact old _ (Or.inr (Or.inl inSnd))
    · by_cases inIds : o ∈ ids
      · have label' : (addRows s ids label).label o = label o := by
          simp [addRows, inIds]
        rw [label']
        exact new o inIds
      · have label' : (addRows s ids label).label o = s.label o := by
          simp [addRows, inIds]
        rw [label']
        have present' : o ∈ s.present := by
          rcases Finset.mem_union.mp present with present' | inIds'
          · exact present'
          · exact absurd inIds' inIds
        exact old _ (Or.inr (Or.inr ⟨o, present', rfl⟩))

omit [DecidableEq O] in
theorem supports_tellState (s : State Tm O) (L : EquationStore (Tm s.frame)) {b : Obj}
    (φ ψ : Hom s.frame b) :
    Supports X (tellState s L) φ ψ ↔
      Supports X s φ ψ ∧ ∀ e ∈ L, X.E (X.act φ e.1) (X.act ψ e.1) ∧ X.E (X.act φ e.2) (X.act ψ e.2) := by
  constructor
  · intro supports
    refine ⟨fun t mentioned => ?_, fun e inside => ⟨?_, ?_⟩⟩
    · rcases mentioned with inFst | inSnd | rows
      · have inside : t ∈ (s.knowledge ++ L).map Prod.fst := by
          rw [List.map_append]
          exact List.mem_append_left _ inFst
        exact supports _ (Or.inl inside)
      · have inside : t ∈ (s.knowledge ++ L).map Prod.snd := by
          rw [List.map_append]
          exact List.mem_append_left _ inSnd
        exact supports _ (Or.inr (Or.inl inside))
      · exact supports _ (Or.inr (Or.inr rows))
    · exact supports _ (Or.inl (List.mem_map_of_mem (List.mem_append_right _ inside)))
    · exact supports _ (Or.inr (Or.inl (List.mem_map_of_mem (List.mem_append_right _ inside))))
  · rintro ⟨old, new⟩ t mentioned
    rcases mentioned with inFst | inSnd | rows
    · obtain ⟨e, inside, rfl⟩ := List.mem_map.mp inFst
      rcases List.mem_append.mp inside with known | told
      · exact old _ (Or.inl (List.mem_map_of_mem known))
      · exact (new e told).1
    · obtain ⟨e, inside, rfl⟩ := List.mem_map.mp inSnd
      rcases List.mem_append.mp inside with known | told
      · exact old _ (Or.inr (Or.inl (List.mem_map_of_mem known)))
      · exact (new e told).2
    · exact old _ (Or.inr (Or.inr rows))

omit [DecidableEq O] in
theorem supports_extendState (s : State Tm O) (x : E.Ext s.frame) {b : Obj}
    (φ ψ : Hom (E.target x) b) :
    Supports X (extendState X E s x) φ ψ ↔
      Supports X s (X.comp φ (E.weaken x)) (X.comp ψ (E.weaken x)) := by
  constructor
  · intro supports t mentioned
    rw [X.act_comp, X.act_comp]
    rcases mentioned with inFst | inSnd | ⟨o, present, rfl⟩
    · obtain ⟨e, inside, rfl⟩ := List.mem_map.mp inFst
      exact supports _ (Or.inl (List.mem_map_of_mem (List.mem_map_of_mem inside)))
    · obtain ⟨e, inside, rfl⟩ := List.mem_map.mp inSnd
      exact supports _ (Or.inr (Or.inl (List.mem_map_of_mem (List.mem_map_of_mem inside))))
    · exact supports _ (Or.inr (Or.inr ⟨o, present, rfl⟩))
  · intro supports t mentioned
    rcases mentioned with inFst | inSnd | ⟨o, present, rfl⟩
    · obtain ⟨e, inside, rfl⟩ := List.mem_map.mp inFst
      obtain ⟨original, member, rfl⟩ := List.mem_map.mp inside
      have agree := supports _ (Or.inl (List.mem_map_of_mem member))
      rw [X.act_comp, X.act_comp] at agree
      exact agree
    · obtain ⟨e, inside, rfl⟩ := List.mem_map.mp inSnd
      obtain ⟨original, member, rfl⟩ := List.mem_map.mp inside
      have agree := supports _ (Or.inr (Or.inl (List.mem_map_of_mem member)))
      rw [X.act_comp, X.act_comp] at agree
      exact agree
    · have agree := supports _ (Or.inr (Or.inr ⟨o, present, rfl⟩))
      rw [X.act_comp, X.act_comp] at agree
      exact agree

/-- **Every context preserves equivalence modulo the knowledge.** -/
theorem modulo_apply {s : State Tm O} {K : EquationStore (Tm s.frame)} {ℓ : O → Tm s.frame}
    (modulo : ModuloAt X s K ℓ) (c : Basic Tm O E) (P : Program Tm) (applies : c.Applies ⟨P, s⟩) :
    Modulo X (c.apply X ⟨P, s⟩).state (c.apply X ⟨P, ⟨s.frame, K, s.present, ℓ⟩⟩).state := by
  obtain ⟨equivalent, labels, support⟩ := modulo
  cases c with
  | rows ids label =>
      have apart : Disjoint ids s.present := applies
      refine ⟨K, fun o => if o ∈ ids then label s.frame o else ℓ o, ⟨equivalent, ?_, ?_⟩, rfl⟩
      · intro o present b σ known
        refine E_ite σ (o ∈ ids) (label s.frame o) (s.label o) (ℓ o) (fun inIds => ?_)
        have present' : o ∈ s.present := by
          rcases Finset.mem_union.mp present with present' | inIds'
          · exact present'
          · exact absurd inIds' inIds
        exact labels o present' b σ known
      · intro b φ ψ
        exact (supports_addRows s ids (label s.frame) apart φ ψ).trans
          ((and_congr (support b φ ψ) Iff.rfl).trans
            (supports_addRows (⟨s.frame, K, s.present, ℓ⟩ : State Tm O) ids (label s.frame) apart
              φ ψ).symm)
  | rules added => exact ⟨K, ℓ, ⟨equivalent, labels, support⟩, rfl⟩
  | tell equations =>
      refine ⟨K ++ equations s.frame, ℓ, ⟨fun b σ => ?_, fun o present b σ known => ?_, ?_⟩, rfl⟩
      · exact (Frames.models_append (X := X) σ s.knowledge (equations s.frame)).trans
          ((and_congr (equivalent b σ) Iff.rfl).trans
            (Frames.models_append (X := X) σ K (equations s.frame)).symm)
      · exact labels o present b σ (Frames.models_of_subset (fun e inside =>
          List.mem_append_left _ inside) known)
      · intro b φ ψ
        exact (supports_tellState s (equations s.frame) φ ψ).trans
          ((and_congr (support b φ ψ) Iff.rfl).trans
            (supports_tellState (⟨s.frame, K, s.present, ℓ⟩ : State Tm O) (equations s.frame)
              φ ψ).symm)
  | extend extension =>
      let x := extension s.frame
      refine ⟨X.applyStore (E.weaken x) K, fun o => X.act (E.weaken x) (ℓ o),
        ⟨fun b σ => ?_, fun o present b σ known => ?_, ?_⟩, rfl⟩
      · exact (Frames.models_applyStore (X := X) (E.weaken x) σ s.knowledge).trans
          ((equivalent b _).trans (Frames.models_applyStore (X := X) (E.weaken x) σ K).symm)
      · have known' := (Frames.models_applyStore (E.weaken x) σ s.knowledge).mp known
        have agree : X.E (X.act (X.comp σ (E.weaken x)) (s.label o))
            (X.act (X.comp σ (E.weaken x)) (ℓ o)) := labels o present b _ known'
        exact (E_comp_iff σ (E.weaken x) _ _).mp agree
      · intro b φ ψ
        exact (supports_extendState s x φ ψ).trans ((support b _ _).trans
          (supports_extendState (⟨s.frame, K, s.present, ℓ⟩ : State Tm O) x φ ψ).symm)

end Contexts

/-! ## Law 2 -/

section Law

variable {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {E : Extensions.{uO, uH, uE} Hom}
  {B : Type uB} {obs : B → State Tm O → Prop}

/-- **Law 2: states equivalent modulo the knowledge, with the same support, are congruent**, with
every program, for every barb family that cannot tell them apart. -/
theorem modulo_congruent (invariant : ∀ {s t : State Tm O}, Modulo X s t → ∀ β, obs β s → obs β t)
    (P : Program Tm) {s t : State Tm O} (modulo : Modulo X s t) :
    Congruent X O E obs ⟨P, s⟩ ⟨P, t⟩ := by
  let R : System Tm O → System Tm O → Prop := fun S T =>
    T.program = S.program ∧ Modulo X S.state T.state
  have candidate : Candidate X O E obs R := {
    symm := fun ⟨program, related⟩ => ⟨program.symm, related.symm⟩
    barbs := fun ⟨_, related⟩ β holds => invariant related β holds
    reduces := by
      rintro ⟨SP, Ss⟩ ⟨TP, Ts⟩ ⟨program, K, ℓ, related, state⟩ S' ⟨same, f, admitted, reached⟩
      simp only at program state
      subst program state
      obtain ⟨admittedT, results⟩ := modulo_step related f admitted
      refine ⟨⟨S'.program, f.result X ⟨Ss.frame, K, Ss.present, ℓ⟩⟩, ⟨same, f, admittedT, rfl⟩,
        rfl, ?_⟩
      have reached' : f.result X Ss = S'.state := reached
      rw [← reached']
      exact results
    context := by
      rintro ⟨SP, Ss⟩ ⟨TP, Ts⟩ ⟨program, K, ℓ, related, state⟩ c applies
      simp only at program state
      subst program state
      refine ⟨1, ?_, ?_⟩
      · rw [Basic.rename_one]
        cases c <;> exact applies
      · rw [Basic.rename_one]
        refine ⟨?_, modulo_apply related c TP applies⟩
        cases c <;> rfl }
  exact candidate.le_congruent ⟨rfl, modulo⟩

/-- **Law 2 for the chosen barbs.** -/
theorem modulo_congruent_mayBarb (P : Program Tm) {s t : State Tm O} (modulo : Modulo X s t) :
    Congruent X O E (MayBarb X) ⟨P, s⟩ ⟨P, t⟩ :=
  modulo_congruent (fun related p => mayBarb_modulo related p) P modulo

/-- **Labels of absent identities are unobservable.** -/
theorem offPresent_congruent (invariant : ∀ {s t : State Tm O}, Modulo X s t → ∀ β, obs β s → obs β t)
    (P : Program Tm) (s : State Tm O) (ℓ : O → Tm s.frame) (agree : ∀ o ∈ s.present, ℓ o = s.label o) :
    Congruent X O E obs ⟨P, s⟩ ⟨P, ⟨s.frame, s.knowledge, s.present, ℓ⟩⟩ := by
  refine modulo_congruent invariant P ⟨s.knowledge, ℓ, ⟨fun _ _ => Iff.rfl,
    fun o present b σ _ => ?_, fun b φ ψ => ?_⟩, rfl⟩
  · rw [agree o present]
    exact (X.equivalence b).refl _
  · constructor
    · intro supports t mentioned
      rcases mentioned with inFst | inSnd | ⟨o, present, rfl⟩
      · exact supports _ (Or.inl inFst)
      · exact supports _ (Or.inr (Or.inl inSnd))
      · exact supports _ (Or.inr (Or.inr ⟨o, present, (agree o present).symm⟩))
    · intro supports t mentioned
      rcases mentioned with inFst | inSnd | ⟨o, present, rfl⟩
      · exact supports _ (Or.inl inFst)
      · exact supports _ (Or.inr (Or.inl inSnd))
      · exact supports _ (Or.inr (Or.inr ⟨o, present, agree o present⟩))

end Law

#print axioms exists_zip_left
#print axioms exists_zip_right
#print axioms relabel_mem
#print axioms relabel_eq_of_mem
#print axioms fresh_iff_of_support
#print axioms supports_result
#print axioms Modulo.symm
#print axioms mayBarb_modulo
#print axioms mustBarb_modulo
#print axioms modulo_step
#print axioms supports_addRows
#print axioms supports_tellState
#print axioms supports_extendState
#print axioms modulo_apply
#print axioms modulo_congruent
#print axioms modulo_congruent_mayBarb
#print axioms offPresent_congruent

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence
