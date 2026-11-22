import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflSystemPhases

/-!
# Independence, diamond commutation across locations, and Mazurkiewicz trace equivalence

In the located program (`ReflLocated.located`), firings at `Root`, at sibling children, and at
nested or dead locations interleave freely. Here we prove the algebraic commutation and trace
reordering half of P2 (child-segment isolation across arbitrary runs follows in
`ReflSystemIsolation`):

* **Canonical shapes of admitted firings** (`eq_heatChildN`, `eq_coolAt`, `eq_commChildAt`): any
  admitted firing of `located` with rule `heatChild`, `cool`, or `commChild` at a child location in
  `PendingPhaseS` / `DonePhaseS` is equal to the corresponding named firing constructor with the
  unique phase token.
* **Selection & equation-store commutation** (`SelectionDisjoint`, `models_after_iff`,
  `commute_disjoint_firings`): two admitted firings with disjoint conflict sets, mutually fresh
  openings, mutual check avoidance on made rows, and a common solution of their information commute
  in a strict diamond — yielding **syntactically equal** `present` sets and `label` maps, and
  **logically equivalent** knowledge stores (`∀ σ, Models σ info₁₂ ↔ Models σ info₂₁`), so every
  solution-wise readout agrees identically.
* **Commutation across different locations** (`ActiveAtRootChild`,
  `disjoint_of_different_root_children`, `commute_different_children`): firings localized to
  `NameLaws`-apart root-child locations automatically have disjoint selections and avoid each
  other's checks.
* **Lipton reduction / Mazurkiewicz trace equivalence** (`FiringSeq`, `TraceEquiv`,
  `firingSeq_congr_knowledge`, `traceEquiv_sound`): swapping adjacent independent firings anywhere
  along a valid firing sequence produces a valid reordered firing sequence with identical `present`
  occurrences, identical `label` map, and equivalent knowledge stores.
* **Sharpness control** (`identical_reflections_serialize_open`): two distinct root reflections
  sharing the *same* child location `Child(Root, @0, 0)` are each admitted initially, yet opening
  one blocks opening the other until the child closes — proving `apart` is necessary.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflSystem

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus (pFor pZero tProc pReflect demoChan)
open MeTTaOperationsComm (psubst PSubst)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open FiniteProgram (commRule heatRule clearRule channelUnknown)
open Comm (Tm)
open OneFrame (embed)
open ReflNames (NameLaws nameAction QN QNE nameLaws_heads)
open ReflLocated (atLoc rootLoc childLoc pendingTok doneTok locL locM reflP accC atRule
  located commChild heatChild heatChild_mem heatChildN cool closeRoot closeChild openRoot openChild
  exists_mem_zip psubst_rootLoc psubst_atLoc_any psubst_pendingTok locatedFrame_name)
open ReflPacking (psubst_doneTok nameLaws_doneTok_iff coolAt cool_mem)
open ReflLocatedStep (located_cases psubst_childLoc nameLaws_pendingTok_iff nameLaws_childLoc_iff
  res resConf info_known take_reads read_reads solution_of_admitted result_label_old
  result_label_made made_label made_not_present result_row commChildAt psubst_pReflect
  nameLaws_pReflect_iff)
open ReflCorrespondence (Clean openRootAt openRoot_admitted)

/-! ## Canonical constructor forms of admitted firings -/

section CanonicalFirings

variable {O : Type*} [DecidableEq O]

private theorem list_len1 {α : Type*} {xs : List α} (h : xs.length = 1) : ∃ a, xs = [a] := by
  match xs, h with | [a], _ => exact ⟨a, rfl⟩

private theorem list_len2 {α : Type*} {xs : List α} (h : xs.length = 2) : ∃ a b, xs = [a, b] := by
  match xs, h with | [a, b], _ => exact ⟨a, b, rfl⟩

private theorem list_len3 {α : Type*} {xs : List α} (h : xs.length = 3) : ∃ a b c, xs = [a, b, c] := by
  match xs, h with | [a, b, c], _ => exact ⟨a, b, c, rfl⟩

theorem eq_heatChildN {m x p : Pattern} {label : O → Pattern} {C : Configuration Pattern O} {tk : O}
    (phase : PendingPhaseS (childLoc m x p) m label C tk)
    {g : Firing O QNE located PUnit.unit}
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g)
    (isHeat : g.rule = heatChild) {σ₀ : PSubst}
    (solved₀ : nameAction.Models σ₀ (g.information QN (embed label C)))
    (loc₀ : NameLaws (psubst σ₀ (psubst g.opening locL)) (psubst σ₀ (childLoc m x p))) :
    ∃ o m₁ m₂, g = heatChildN g.opening o tk m₁ m₂ := by
  obtain ⟨_, shapes, -⟩ := (RuleSyntax.admits_iff g).mp admitted
  obtain ⟨rule, member, ext, ρ, ⟨taken, read, made⟩, seen⟩ := g
  cases ext
  simp only at isHeat shapes solved₀ loc₀
  subst isHeat
  obtain ⟨o, rfl⟩ := list_len1 shapes.2.2.1.symm
  obtain ⟨tk', rfl⟩ := list_len1 shapes.2.2.2.1.symm
  obtain ⟨m₁, m₂, rfl⟩ := list_len2 shapes.2.2.2.2.1.symm
  have seenNil : seen = [] := List.eq_nil_of_length_eq_zero shapes.2.2.2.2.2.symm
  subst seenNil
  have zipped : (pendingTok locL locM, tk') ∈
      (heatChildN ρ o tk' m₁ m₂).rule.body.read.zip (heatChildN ρ o tk' m₁ m₂).selection.read := by
    simp [heatChildN, heatChild]
  have subMem : member = heatChild_mem := Subsingleton.elim _ _
  subst subMem
  obtain ⟨_, _, enabled, -⟩ := (RuleSyntax.admits_iff _).mp admitted
  have tk'In : tk' ∈ C.present := enabled.kept_subset (by simp [Selection.commit])
  have rRead := read_reads (heatChildN ρ o tk' m₁ m₂) solved₀ zipped
  rw [psubst_pendingTok] at rRead
  have isTk : tk' = tk := phase.unique tk' tk'In ⟨σ₀, info_known _ solved₀, _,
    rRead.symm.trans (nameLaws_pendingTok_iff.mpr ⟨loc₀, NameLaws.refl _⟩)⟩
  subst isTk
  exact ⟨o, m₁, m₂, rfl⟩

theorem eq_coolAt {m x p : Pattern} {label : O → Pattern} {C : Configuration Pattern O} {d : O}
    (phase : DonePhaseS (childLoc m x p) m label C d)
    {g : Firing O QNE located PUnit.unit}
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g)
    (isCool : g.rule = cool) {σ₀ : PSubst}
    (solved₀ : nameAction.Models σ₀ (g.information QN (embed label C)))
    (loc₀ : NameLaws (psubst σ₀ (psubst g.opening locL)) (psubst σ₀ (childLoc m x p))) :
    ∃ r d', g = coolAt g.opening d r d' := by
  obtain ⟨_, shapes, enabled, -⟩ := (RuleSyntax.admits_iff g).mp admitted
  obtain ⟨rule, member, ext, ρ, ⟨taken, read, made⟩, seen⟩ := g
  cases ext
  simp only at isCool shapes solved₀ loc₀
  subst isCool
  obtain ⟨d₀, r, rfl⟩ := list_len2 shapes.2.2.1.symm
  have readNil : read = [] := List.eq_nil_of_length_eq_zero shapes.2.2.2.1.symm
  obtain ⟨d', rfl⟩ := list_len1 shapes.2.2.2.2.1.symm
  have seenNil : seen = [] := List.eq_nil_of_length_eq_zero shapes.2.2.2.2.2.symm
  subst readNil seenNil
  have subMem : member = cool_mem := Subsingleton.elim _ _
  subst subMem
  have d₀In : d₀ ∈ C.present := enabled.taken_subset (by simp [Selection.commit])
  have zipped : (doneTok locL locM accC, d₀) ∈
      (coolAt ρ d₀ r d').rule.body.take.zip (coolAt ρ d₀ r d').selection.taken := by
    simp [coolAt, cool]
  have rTake := take_reads (coolAt ρ d₀ r d') solved₀ zipped
  rw [psubst_doneTok] at rTake
  have isD : d₀ = d := phase.unique d₀ d₀In ⟨σ₀, info_known _ solved₀, _, _,
    rTake.symm.trans (nameLaws_doneTok_iff.mpr ⟨loc₀, NameLaws.refl _, NameLaws.refl _⟩)⟩
  subst isD
  exact ⟨r, d', rfl⟩

theorem eq_commChildAt {m x p : Pattern} {label : O → Pattern} {C : Configuration Pattern O} {tk : O}
    (phase : PendingPhaseS (childLoc m x p) m label C tk)
    {g : Firing O QNE located PUnit.unit}
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g)
    (isComm : g.rule = commChild) {σ₀ : PSubst}
    (solved₀ : nameAction.Models σ₀ (g.information QN (embed label C)))
    (loc₀ : NameLaws (psubst σ₀ (psubst g.opening locL)) (psubst σ₀ (childLoc m x p))) :
    ∃ first second m₁ m₂ mTok, g = commChildAt g.opening first second tk m₁ m₂ mTok := by
  obtain ⟨_, shapes, enabled, -⟩ := (RuleSyntax.admits_iff g).mp admitted
  obtain ⟨rule, member, ext, ρ, ⟨taken, read, made⟩, seen⟩ := g
  cases ext
  simp only at isComm shapes solved₀ loc₀
  subst isComm
  obtain ⟨first, second, tk₀, rfl⟩ := list_len3 shapes.2.2.1.symm
  have readNil : read = [] := List.eq_nil_of_length_eq_zero shapes.2.2.2.1.symm
  obtain ⟨m₁, m₂, mTok, rfl⟩ := list_len3 shapes.2.2.2.2.1.symm
  have seenNil : seen = [] := List.eq_nil_of_length_eq_zero shapes.2.2.2.2.2.symm
  subst readNil seenNil
  have subMem : member = ReflLocated.commChild_mem := Subsingleton.elim _ _
  subst subMem
  have tk₀In : tk₀ ∈ C.present := enabled.taken_subset (by simp [Selection.commit])
  have zipped : (pendingTok locL locM, tk₀) ∈
      (commChildAt ρ first second tk₀ m₁ m₂ mTok).rule.body.take.zip
        (commChildAt ρ first second tk₀ m₁ m₂ mTok).selection.taken := by
    simp [commChildAt, commChild]
  have rTake := take_reads (commChildAt ρ first second tk₀ m₁ m₂ mTok) solved₀ zipped
  rw [psubst_pendingTok] at rTake
  have isTk : tk₀ = tk := phase.unique tk₀ tk₀In ⟨σ₀, info_known _ solved₀, _,
    rTake.symm.trans (nameLaws_pendingTok_iff.mpr ⟨loc₀, NameLaws.refl _⟩)⟩
  subst isTk
  exact ⟨first, second, m₁, m₂, mTok, rfl⟩

end CanonicalFirings

/-! ## Diamond commutation of independent firings at `QN` -/

section Diamond

variable {O : Type*} [DecidableEq O]

/-- Two occurrence selections have no write-write or read-write conflict and make distinct IDs. -/
structure SelectionDisjoint (s₁ s₂ : Selection O) : Prop where
  taken_taken : ∀ o ∈ s₁.taken, o ∉ s₂.taken
  taken_read : ∀ o ∈ s₁.taken, o ∉ s₂.read
  read_taken : ∀ o ∈ s₂.taken, o ∉ s₁.read
  made_made : ∀ o ∈ s₁.made, o ∉ s₂.made

omit [DecidableEq O] in
theorem SelectionDisjoint.symm {s₁ s₂ : Selection O} (h : SelectionDisjoint s₁ s₂) :
    SelectionDisjoint s₂ s₁ :=
  ⟨fun o m₂ m₁ => h.taken_taken o m₁ m₂, h.read_taken, h.taken_read,
    fun o m₂ m₁ => h.made_made o m₁ m₂⟩

theorem enabled_after_disjoint {P : Program Tm} {present : Finset O}
    {f₁ f₂ : Firing O QNE P PUnit.unit}
    (en₁ : Enabled (fun _ : O => ()) present (f₁.selection.commit (T := Unit)))
    (en₂ : Enabled (fun _ : O => ()) present (f₂.selection.commit (T := Unit)))
    (disj : SelectionDisjoint f₁.selection f₂.selection) :
    Enabled (fun _ : O => ()) (fire present (f₁.selection.commit (T := Unit)))
      (f₂.selection.commit (T := Unit)) := by
  have fresh₁ : ∀ o ∈ f₁.selection.made, o ∉ present := fun o m inP =>
    Finset.disjoint_left.mp en₁.fresh (by simpa [Selection.commit] using m) inP
  have fresh₂ : ∀ o ∈ f₂.selection.made, o ∉ present := fun o m inP =>
    Finset.disjoint_left.mp en₂.fresh (by simpa [Selection.commit] using m) inP
  refine ⟨?_, ?_, en₂.apart, ?_, fun q m => by simp [Selection.commit] at m⟩
  · intro o m
    have in₂ : o ∈ f₂.selection.taken := by simpa [Selection.commit] using m
    have inP : o ∈ present := en₂.taken_subset m
    simp only [fire, Selection.commit, Finset.mem_union, Finset.mem_sdiff, List.mem_toFinset]
    exact .inl ⟨inP, fun in₁ => disj.taken_taken o in₁ in₂⟩
  · intro o m
    have in₂ : o ∈ f₂.selection.read := by simpa [Selection.commit] using m
    have inP : o ∈ present := en₂.kept_subset m
    simp only [fire, Selection.commit, Finset.mem_union, Finset.mem_sdiff, List.mem_toFinset]
    exact .inl ⟨inP, fun in₁ => disj.taken_read o in₁ in₂⟩
  · rw [Finset.disjoint_left]
    intro o m inFire
    have m₂ : o ∈ f₂.selection.made := by simpa [Selection.commit] using m
    simp only [fire, Selection.commit, Finset.mem_union, Finset.mem_sdiff, List.mem_toFinset] at inFire
    rcases inFire with ⟨inP, _⟩ | m₁
    · exact fresh₂ o m₂ inP
    · exact disj.made_made o m₁ m₂

theorem fire_comm_of_disjoint {P : Program Tm} {present : Finset O}
    {f₁ f₂ : Firing O QNE P PUnit.unit}
    (en₁ : Enabled (fun _ : O => ()) present (f₁.selection.commit (T := Unit)))
    (en₂ : Enabled (fun _ : O => ()) present (f₂.selection.commit (T := Unit))) :
    fire (fire present (f₁.selection.commit (T := Unit))) (f₂.selection.commit (T := Unit)) =
      fire (fire present (f₂.selection.commit (T := Unit))) (f₁.selection.commit (T := Unit)) := by
  have fresh₁ : ∀ o ∈ f₁.selection.made, o ∉ present := fun o m inP =>
    Finset.disjoint_left.mp en₁.fresh (by simpa [Selection.commit] using m) inP
  have fresh₂ : ∀ o ∈ f₂.selection.made, o ∉ present := fun o m inP =>
    Finset.disjoint_left.mp en₂.fresh (by simpa [Selection.commit] using m) inP
  have madeNotTaken₁ : ∀ o ∈ f₁.selection.made, o ∉ f₂.selection.taken := fun o m inT =>
    fresh₁ o m (en₂.taken_subset (by simpa [Selection.commit] using inT))
  have madeNotTaken₂ : ∀ o ∈ f₂.selection.made, o ∉ f₁.selection.taken := fun o m inT =>
    fresh₂ o m (en₁.taken_subset (by simpa [Selection.commit] using inT))
  ext o
  simp only [fire, Selection.commit, Finset.mem_union, Finset.mem_sdiff, List.mem_toFinset]
  constructor
  · rintro (⟨⟨inP, nt₁⟩ | m₁, nt₂⟩ | m₂)
    · exact .inl ⟨.inl ⟨inP, nt₂⟩, nt₁⟩
    · exact .inr m₁
    · exact .inl ⟨.inr m₂, madeNotTaken₂ o m₂⟩
  · rintro (⟨⟨inP, nt₂⟩ | m₂, nt₁⟩ | m₁)
    · exact .inl ⟨.inl ⟨inP, nt₁⟩, nt₂⟩
    · exact .inr m₂
    · exact .inl ⟨.inr m₁, madeNotTaken₁ o m₁⟩

theorem matching_after_disjoint {label : O → Pattern} {C : Configuration Pattern O}
    {f₁ f₂ : Firing O QNE located PUnit.unit}
    (admitted₁ : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) f₁)
    (pats : List Pattern) {sel : List O} (inPresent : ∀ o ∈ sel, o ∈ C.present) :
    f₂.matching QN (embed (res label C f₁).label (resConf label C f₁)) pats sel =
      f₂.matching QN (embed label C) pats sel := by
  unfold Firing.matching
  rw [← List.map_uncurry_zip_eq_zipWith, ← List.map_uncurry_zip_eq_zipWith]
  apply List.map_congr_left
  rintro ⟨pat, o⟩ zipped
  have oIn : o ∈ C.present := inPresent o (List.of_mem_zip zipped).2
  have notMade₁ : o ∉ f₁.selection.made := fun m => made_not_present admitted₁ m oIn
  show (pat, f₂.row QN (embed (res label C f₁).label (resConf label C f₁)) o) =
    (pat, f₂.row QN (embed label C) o)
  rw [OneFrame.row_eq, OneFrame.row_eq]
  exact congrArg (Prod.mk pat) (result_label_old f₁ notMade₁)

/-- **Sequential solutions = joint solutions**: after an admitted `f₁`, `σ` solves `f₂`'s
information iff `σ` solves both `f₁`'s and `f₂`'s information at `(label, C)`. -/
theorem models_after_iff {label : O → Pattern} {C : Configuration Pattern O}
    {f₁ f₂ : Firing O QNE located PUnit.unit}
    (admitted₁ : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) f₁)
    (admitted₂ : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) f₂)
    (σ : PSubst) :
    nameAction.Models σ (f₂.information QN (embed (res label C f₁).label (resConf label C f₁))) ↔
      nameAction.Models σ (f₁.information QN (embed label C)) ∧
        nameAction.Models σ (f₂.information QN (embed label C)) := by
  obtain ⟨_, _, en₂, -⟩ := (RuleSyntax.admits_iff f₂).mp admitted₂
  have takeIn : ∀ o ∈ f₂.selection.taken, o ∈ C.present := fun o m =>
    en₂.taken_subset (by simpa [Selection.commit] using m)
  have readIn : ∀ o ∈ f₂.selection.read, o ∈ C.present := fun o m =>
    en₂.kept_subset (by simpa [Selection.commit] using m)
  have applyId : ∀ (K : EquationStore Pattern),
      QN.applyStore (a := PUnit.unit) (b := PUnit.unit) (QNE.weaken (a := PUnit.unit) PUnit.unit) K = K :=
    fun K => Interface.Frames.applyStore_id (X := QN) (a := PUnit.unit) K
  have extEq : f₂.ext = PUnit.unit := rfl
  have eqInfo₁₂ : f₂.information QN (embed (res label C f₁).label (resConf label C f₁)) =
      f₁.information QN (embed label C) ++
        f₂.matching QN (embed label C) (f₂.opened QN).take f₂.selection.taken ++
        f₂.matching QN (embed label C) (f₂.opened QN).read f₂.selection.read ++
        (f₂.opened QN).tell := by
    unfold Firing.information
    rw [extEq, applyId, matching_after_disjoint admitted₁ _ takeIn,
      matching_after_disjoint admitted₁ _ readIn]
    rfl
  have eqInfo₂ : f₂.information QN (embed label C) =
      C.equations ++
        f₂.matching QN (embed label C) (f₂.opened QN).take f₂.selection.taken ++
        f₂.matching QN (embed label C) (f₂.opened QN).read f₂.selection.read ++
        (f₂.opened QN).tell := by
    unfold Firing.information
    rw [extEq, applyId]
    rfl
  rw [eqInfo₁₂, eqInfo₂]
  constructor
  · intro solved
    have s₁ : nameAction.Models σ (f₁.information QN (embed label C)) := fun e m =>
      solved e (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ m)))
    refine ⟨s₁, fun e m => ?_⟩
    rcases List.mem_append.mp m with front | inTell
    · rcases List.mem_append.mp front with front' | inRead
      · rcases List.mem_append.mp front' with inBase | inTake
        · exact info_known f₁ s₁ e inBase
        · exact solved e (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ inTake)))
      · exact solved e (List.mem_append_left _ (List.mem_append_right _ inRead))
    · exact solved e (List.mem_append_right _ inTell)
  · rintro ⟨s₁, s₂⟩ e m
    rcases List.mem_append.mp m with front | inTell
    · rcases List.mem_append.mp front with front' | inRead
      · rcases List.mem_append.mp front' with inInfo₁ | inTake
        · exact s₁ e inInfo₁
        · exact s₂ e (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ inTake)))
      · exact s₂ e (List.mem_append_left _ (List.mem_append_right _ inRead))
    · exact s₂ e (List.mem_append_right _ inTell)

theorem label_comm_of_disjoint {label : O → Pattern} {C : Configuration Pattern O}
    {f₁ f₂ : Firing O QNE located PUnit.unit}
    (admitted₁ : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) f₁)
    (admitted₂ : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) f₂)
    (disj : SelectionDisjoint f₁.selection f₂.selection)
    (admitted₁₂ : (RuleSyntax.step QN O QNE located).Admits
      (s := embed (res label C f₁).label (resConf label C f₁)) f₂)
    (admitted₂₁ : (RuleSyntax.step QN O QNE located).Admits
      (s := embed (res label C f₂).label (resConf label C f₂)) f₁) :
    (res (res label C f₁).label (resConf label C f₁) f₂).label =
      (res (res label C f₂).label (resConf label C f₂) f₁).label := by
  obtain ⟨_, shapes₁, -⟩ := (RuleSyntax.admits_iff f₁).mp admitted₁
  obtain ⟨_, shapes₂, -⟩ := (RuleSyntax.admits_iff f₂).mp admitted₂
  funext o
  by_cases m₁ : o ∈ f₁.selection.made
  · have nm₂ : o ∉ f₂.selection.made := disj.made_made o m₁
    obtain ⟨t₁, z₁⟩ := exists_mem_zip shapes₁.2.2.2.2.1.symm m₁
    rw [result_label_old f₂ nm₂, result_label_made admitted₁ z₁, result_label_made admitted₂₁ z₁]
  · by_cases m₂ : o ∈ f₂.selection.made
    · obtain ⟨t₂, z₂⟩ := exists_mem_zip shapes₂.2.2.2.2.1.symm m₂
      rw [result_label_made admitted₁₂ z₂, result_label_old f₁ m₁, result_label_made admitted₂ z₂]
    · rw [result_label_old f₂ m₂, result_label_old f₁ m₁,
        result_label_old f₁ m₁, result_label_old f₂ m₂]

/-- No check of `f₂` matches any row made by `f₁`, at any joint solution. -/
def ChecksAvoidMade (label : O → Pattern) (C : Configuration Pattern O)
    (f₁ f₂ : Firing O QNE located PUnit.unit) : Prop :=
  ∀ c ∈ f₂.rule.body.checks, ∀ pat, c = .predicate .none pat →
    ∀ σ : PSubst, nameAction.Models σ (f₁.information QN (embed label C)) →
      nameAction.Models σ (f₂.information QN (embed label C)) →
        ∀ t ∈ f₁.rule.body.produce, ¬ NameLaws (psubst σ (psubst f₂.opening pat))
          (psubst σ (psubst f₁.opening t))

omit [DecidableEq O] in
theorem located_checks_absent {r : Rule Tm} (member : r ∈ located) {c : Check Pattern}
    (inside : c ∈ r.body.checks) : ∃ pat, c = .predicate .none pat := by
  rcases located_cases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [atRule, RuleInstance.map, commRule, heatRule, clearRule, commChild, heatChild, cool,
      closeRoot, closeChild, openRoot, openChild] at inside
  all_goals
    rcases inside with rfl | rfl | rfl <;> exact ⟨_, rfl⟩

omit [DecidableEq O] in
theorem located_collect_nil {r : Rule Tm} (member : r ∈ located) : r.collect = [] := by
  rcases located_cases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- **Diamond commutation of independent firings at `QN`**. -/
theorem commute_disjoint_firings {label : O → Pattern} {C : Configuration Pattern O}
    {f₁ f₂ : Firing O QNE located PUnit.unit}
    (admitted₁ : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) f₁)
    (admitted₂ : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) f₂)
    (disj : SelectionDisjoint f₁.selection f₂.selection)
    (fresh₁₂ : f₂.Fresh QN (embed (res label C f₁).label (resConf label C f₁)))
    (fresh₂₁ : f₁.Fresh QN (embed (res label C f₂).label (resConf label C f₂)))
    (avoid₁₂ : ChecksAvoidMade label C f₁ f₂)
    (avoid₂₁ : ChecksAvoidMade label C f₂ f₁)
    (joint : ∃ σ : PSubst, nameAction.Models σ (f₁.information QN (embed label C)) ∧
      nameAction.Models σ (f₂.information QN (embed label C))) :
    ∃ (_ : (RuleSyntax.step QN O QNE located).Admits
          (s := embed (res label C f₁).label (resConf label C f₁)) f₂)
      (_ : (RuleSyntax.step QN O QNE located).Admits
          (s := embed (res label C f₂).label (resConf label C f₂)) f₁),
      (resConf (res label C f₁).label (resConf label C f₁) f₂).present =
        (resConf (res label C f₂).label (resConf label C f₂) f₁).present ∧
      (res (res label C f₁).label (resConf label C f₁) f₂).label =
        (res (res label C f₂).label (resConf label C f₂) f₁).label ∧
      ∀ σ : PSubst,
        nameAction.Models σ (resConf (res label C f₁).label (resConf label C f₁) f₂).equations ↔
          nameAction.Models σ (resConf (res label C f₂).label (resConf label C f₂) f₁).equations := by
  have stepAdmits : ∀ {g₁ g₂ : Firing O QNE located PUnit.unit},
      (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g₁ →
      (RuleSyntax.step QN O QNE located).Admits (s := embed label C) g₂ →
      SelectionDisjoint g₁.selection g₂.selection →
      g₂.Fresh QN (embed (res label C g₁).label (resConf label C g₁)) →
      ChecksAvoidMade label C g₁ g₂ →
      (∃ σ : PSubst, nameAction.Models σ (g₁.information QN (embed label C)) ∧
        nameAction.Models σ (g₂.information QN (embed label C))) →
      (RuleSyntax.step QN O QNE located).Admits
        (s := embed (res label C g₁).label (resConf label C g₁)) g₂ := by
    intro g₁ g₂ a₁ a₂ d fr av ⟨σ₀, j₁, j₂⟩
    obtain ⟨_, sh₁, en₁, -⟩ := (RuleSyntax.admits_iff g₁).mp a₁
    obtain ⟨_, sh₂, en₂, _, ch₂, _⟩ := (RuleSyntax.admits_iff g₂).mp a₂
    have σ₀Solves : nameAction.Models σ₀
        (g₂.information QN (embed (res label C g₁).label (resConf label C g₁))) :=
      (models_after_iff a₁ a₂ σ₀).mpr ⟨j₁, j₂⟩
    refine (RuleSyntax.admits_iff g₂).mpr ⟨fr, sh₂, enabled_after_disjoint en₁ en₂ d,
      ⟨PUnit.unit, σ₀, σ₀Solves⟩, ?_, ?_⟩
    · intro c cMem _ σ solved
      obtain ⟨s₁, s₂⟩ := (models_after_iff a₁ a₂ σ).mp solved
      have cMap : c ∈ g₂.rule.body.checks.map (Check.map (psubst g₂.opening)) := cMem
      obtain ⟨c₀, c₀In, rfl⟩ := List.mem_map.mp cMap
      obtain ⟨pat, rfl⟩ := located_checks_absent g₂.member c₀In
      intro o oPres same
      rw [OneFrame.row_eq] at same
      rcases result_row (g := g₁) oPres with m₁ | ⟨old, -, -, labelOld⟩
      · obtain ⟨t₁, t₁In, lEq⟩ := made_label a₁ m₁
        rw [lEq] at same
        exact av _ c₀In pat rfl σ s₁ s₂ t₁ t₁In same
      · rw [labelOld] at same
        have oldHold := ch₂ (Check.predicate .none (psubst g₂.opening pat))
          (List.mem_map_of_mem c₀In) PUnit.unit σ s₂
        exact oldHold o old (by simpa [OneFrame.row_eq] using same)
    · intro q qMem
      have nilC : (g₂.collectOpened QN) = [] := by
        simp [Firing.collectOpened, located_collect_nil g₂.member]
      rw [nilC] at qMem
      simp at qMem
  obtain ⟨σ₀, j₁, j₂⟩ := joint
  have adm₁₂ := stepAdmits admitted₁ admitted₂ disj fresh₁₂ avoid₁₂ ⟨σ₀, j₁, j₂⟩
  have adm₂₁ := stepAdmits admitted₂ admitted₁ disj.symm fresh₂₁ avoid₂₁ ⟨σ₀, j₂, j₁⟩
  obtain ⟨_, _, en₁, -⟩ := (RuleSyntax.admits_iff f₁).mp admitted₁
  obtain ⟨_, _, en₂, -⟩ := (RuleSyntax.admits_iff f₂).mp admitted₂
  refine ⟨adm₁₂, adm₂₁, fire_comm_of_disjoint en₁ en₂,
    label_comm_of_disjoint admitted₁ admitted₂ disj adm₁₂ adm₂₁, fun σ => ?_⟩
  show nameAction.Models σ (f₂.information QN _) ↔ nameAction.Models σ (f₁.information QN _)
  rw [models_after_iff admitted₁ admitted₂ σ, models_after_iff admitted₂ admitted₁ σ]
  exact and_comm

/-! ## Commutation across different child locations & Mazurkiewicz trace equivalence -/

/-- A firing `f` is confined to a root-child footprint `l = childLoc rootLoc x p`. -/
structure ActiveAtRootChild (x p : Pattern) (label : O → Pattern) (C : Configuration Pattern O)
    (f : Firing O QNE located PUnit.unit) : Prop where
  used_loc : ∀ o ∈ f.selection.taken ++ f.selection.read,
    ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label o)) (psubst σ (atLoc (pReflect x p) rootLoc)) ∨
      (∃ q, NameLaws (psubst σ (label o)) (atLoc q (psubst σ (childLoc rootLoc x p)))) ∨
      (∃ m', NameLaws (psubst σ (label o)) (pendingTok (psubst σ (childLoc rootLoc x p)) m')) ∨
      (∃ m' c', NameLaws (psubst σ (label o)) (doneTok (psubst σ (childLoc rootLoc x p)) m' c'))
  made_loc : ∀ t ∈ f.rule.body.produce, ∀ σ : PSubst,
    nameAction.Models σ (f.information QN (embed label C)) →
      (∃ c', NameLaws (psubst σ (psubst f.opening t))
        (atLoc (pFor (tProc c') (psubst σ x) pZero) rootLoc)) ∨
      (∃ q, NameLaws (psubst σ (psubst f.opening t))
        (atLoc q (psubst σ (childLoc rootLoc x p)))) ∨
      (∃ m', NameLaws (psubst σ (psubst f.opening t))
        (pendingTok (psubst σ (childLoc rootLoc x p)) m')) ∨
      (∃ m' c', NameLaws (psubst σ (psubst f.opening t))
        (doneTok (psubst σ (childLoc rootLoc x p)) m' c'))
  check_loc : ∀ c ∈ f.rule.body.checks, ∀ pat, c = .predicate .none pat →
    ∀ σ : PSubst, nameAction.Models σ (f.information QN (embed label C)) →
      (∃ m', NameLaws (psubst σ (psubst f.opening pat))
        (pendingTok (psubst σ (childLoc rootLoc x p)) m')) ∨
      (∃ m' c', NameLaws (psubst σ (psubst f.opening pat))
        (doneTok (psubst σ (childLoc rootLoc x p)) m' c')) ∨
      (∃ y, NameLaws (psubst σ (psubst f.opening pat))
        (atLoc y (psubst σ (childLoc rootLoc x p))))

omit [DecidableEq O] in
/-- Two root-child footprints that differ modulo `NameLaws` have disjoint selections and avoid
each other's made rows. -/
theorem disjoint_of_different_root_children {x₁ p₁ x₂ p₂ : Pattern}
    {label : O → Pattern} {C : Configuration Pattern O}
    {f₁ f₂ : Firing O QNE located PUnit.unit}
    (act₁ : ActiveAtRootChild x₁ p₁ label C f₁)
    (act₂ : ActiveAtRootChild x₂ p₂ label C f₂)
    (apart : ∀ σ : PSubst, nameAction.Models σ C.equations →
      ¬ NameLaws (psubst σ (childLoc rootLoc x₁ p₁)) (psubst σ (childLoc rootLoc x₂ p₂)))
    (solvable : ∃ σ₀ : PSubst, nameAction.Models σ₀ C.equations)
    (madeDisj : ∀ o ∈ f₁.selection.made, o ∉ f₂.selection.made) :
    SelectionDisjoint f₁.selection f₂.selection ∧
      ChecksAvoidMade label C f₁ f₂ ∧ ChecksAvoidMade label C f₂ f₁ := by
  have noShared : ∀ o, o ∈ f₁.selection.taken ++ f₁.selection.read →
      o ∈ f₂.selection.taken ++ f₂.selection.read → False := by
    intro o u₁ u₂
    obtain ⟨σ, solved⟩ := solvable
    have diff := apart σ solved
    rcases act₁.used_loc o u₁ σ solved with r₁ | ⟨q₁, a₁⟩ | ⟨m₁, p₁'⟩ | ⟨m₁, c₁, d₁⟩ <;>
      rcases act₂.used_loc o u₂ σ solved with r₂ | ⟨q₂, a₂⟩ | ⟨m₂, p₂'⟩ | ⟨m₂, c₂, d₂⟩
    · have both := r₁.symm.trans r₂
      simp only [psubst_atLoc_any, psubst_pReflect, psubst_rootLoc] at both
      obtain ⟨parts, -⟩ := (locatedFrame_name.atLoc_iff _ _ _ _).mp both
      obtain ⟨chEq, pEq⟩ := nameLaws_pReflect_iff.mp parts
      apply diff
      rw [psubst_childLoc, psubst_childLoc, psubst_rootLoc]
      exact nameLaws_childLoc_iff.mpr ⟨NameLaws.refl _, chEq, pEq⟩
    · have both := r₁.symm.trans a₂
      rw [psubst_atLoc_any, psubst_rootLoc, psubst_childLoc] at both
      exact not_nameLaws_childLoc_rootLoc _ _ _ ((locatedFrame_name.atLoc_iff _ _ _ _).mp both).2.symm
    · rw [psubst_atLoc_any] at r₁
      exact absurd (nameLaws_heads (r₁.symm.trans p₂')) (by decide)
    · rw [psubst_atLoc_any] at r₁
      exact absurd (nameLaws_heads (r₁.symm.trans d₂)) (by decide)
    · have both := a₁.symm.trans r₂
      rw [psubst_atLoc_any, psubst_rootLoc, psubst_childLoc] at both
      exact not_nameLaws_childLoc_rootLoc _ _ _ ((locatedFrame_name.atLoc_iff _ _ _ _).mp both).2
    · exact diff ((locatedFrame_name.atLoc_iff _ _ _ _).mp (a₁.symm.trans a₂)).2
    · exact absurd (nameLaws_heads (a₁.symm.trans p₂')) (by decide)
    · exact absurd (nameLaws_heads (a₁.symm.trans d₂)) (by decide)
    · rw [psubst_atLoc_any] at r₂
      exact absurd (nameLaws_heads (p₁'.symm.trans r₂)) (by decide)
    · exact absurd (nameLaws_heads (p₁'.symm.trans a₂)) (by decide)
    · exact diff (nameLaws_pendingTok_iff.mp (p₁'.symm.trans p₂')).1
    · exact absurd (nameLaws_heads (p₁'.symm.trans d₂)) (by decide)
    · rw [psubst_atLoc_any] at r₂
      exact absurd (nameLaws_heads (d₁.symm.trans r₂)) (by decide)
    · exact absurd (nameLaws_heads (d₁.symm.trans a₂)) (by decide)
    · exact absurd (nameLaws_heads (d₁.symm.trans p₂')) (by decide)
    · exact diff (nameLaws_doneTok_iff.mp (d₁.symm.trans d₂)).1
  have avoidAux : ∀ {xa pa xb pb : Pattern} {fa fb : Firing O QNE located PUnit.unit},
      ActiveAtRootChild xa pa label C fa → ActiveAtRootChild xb pb label C fb →
      (∀ σ : PSubst, nameAction.Models σ C.equations →
        ¬ NameLaws (psubst σ (childLoc rootLoc xa pa)) (psubst σ (childLoc rootLoc xb pb))) →
      ChecksAvoidMade label C fa fb := by
    intro xa pa xb pb fa fb aa ab ap c cIn pat cEq σ s₁ s₂ t tIn same
    have known : nameAction.Models σ C.equations := info_known fa s₁
    have diff := ap σ known
    rcases ab.check_loc c cIn pat cEq σ s₂ with ⟨m₂, chP⟩ | ⟨m₂, c₂, chD⟩ | ⟨y₂, chA⟩ <;>
      rcases aa.made_loc t tIn σ s₁ with ⟨c₁, mL⟩ | ⟨q₁, mA⟩ | ⟨m₁, mP⟩ | ⟨m₁, c₁, mD⟩
    · exact absurd (nameLaws_heads (chP.symm.trans (same.trans mL))) (by decide)
    · exact absurd (nameLaws_heads (chP.symm.trans (same.trans mA))) (by decide)
    · exact diff (nameLaws_pendingTok_iff.mp (mP.symm.trans (same.symm.trans chP))).1
    · exact absurd (nameLaws_heads (chP.symm.trans (same.trans mD))) (by decide)
    · exact absurd (nameLaws_heads (chD.symm.trans (same.trans mL))) (by decide)
    · exact absurd (nameLaws_heads (chD.symm.trans (same.trans mA))) (by decide)
    · exact absurd (nameLaws_heads (chD.symm.trans (same.trans mP))) (by decide)
    · exact diff (nameLaws_doneTok_iff.mp (mD.symm.trans (same.symm.trans chD))).1
    · have both := mL.symm.trans (same.symm.trans chA)
      rw [psubst_childLoc] at both
      exact not_nameLaws_childLoc_rootLoc _ _ _ ((locatedFrame_name.atLoc_iff _ _ _ _).mp both).2.symm
    · exact diff ((locatedFrame_name.atLoc_iff _ _ _ _).mp (mA.symm.trans (same.symm.trans chA))).2
    · exact absurd (nameLaws_heads (chA.symm.trans (same.trans mP))) (by decide)
    · exact absurd (nameLaws_heads (chA.symm.trans (same.trans mD))) (by decide)
  refine ⟨⟨fun o t₁ t₂ => noShared o (List.mem_append_left _ t₁) (List.mem_append_left _ t₂),
    fun o t₁ r₂ => noShared o (List.mem_append_left _ t₁) (List.mem_append_right _ r₂),
    fun o t₂ r₁ => noShared o (List.mem_append_right _ r₁) (List.mem_append_left _ t₂),
    madeDisj⟩, avoidAux act₁ act₂ apart,
    avoidAux act₂ act₁ (fun σ s h => apart σ s h.symm)⟩

/-- **Firings at different root-child locations commute in a diamond**, preserving admission and
every solution-wise readout. -/
theorem commute_different_children {x₁ p₁ x₂ p₂ : Pattern}
    {label : O → Pattern} {C : Configuration Pattern O}
    {f₁ f₂ : Firing O QNE located PUnit.unit}
    (admitted₁ : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) f₁)
    (admitted₂ : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) f₂)
    (act₁ : ActiveAtRootChild x₁ p₁ label C f₁)
    (act₂ : ActiveAtRootChild x₂ p₂ label C f₂)
    (apart : ∀ σ : PSubst, nameAction.Models σ C.equations →
      ¬ NameLaws (psubst σ (childLoc rootLoc x₁ p₁)) (psubst σ (childLoc rootLoc x₂ p₂)))
    (madeDisj : ∀ o ∈ f₁.selection.made, o ∉ f₂.selection.made)
    (fresh₁₂ : f₂.Fresh QN (embed (res label C f₁).label (resConf label C f₁)))
    (fresh₂₁ : f₁.Fresh QN (embed (res label C f₂).label (resConf label C f₂)))
    (joint : ∃ σ : PSubst, nameAction.Models σ (f₁.information QN (embed label C)) ∧
      nameAction.Models σ (f₂.information QN (embed label C))) :
    ∃ (_ : (RuleSyntax.step QN O QNE located).Admits
          (s := embed (res label C f₁).label (resConf label C f₁)) f₂)
      (_ : (RuleSyntax.step QN O QNE located).Admits
          (s := embed (res label C f₂).label (resConf label C f₂)) f₁),
      (resConf (res label C f₁).label (resConf label C f₁) f₂).present =
        (resConf (res label C f₂).label (resConf label C f₂) f₁).present ∧
      (res (res label C f₁).label (resConf label C f₁) f₂).label =
        (res (res label C f₂).label (resConf label C f₂) f₁).label ∧
      ∀ σ : PSubst,
        nameAction.Models σ (resConf (res label C f₁).label (resConf label C f₁) f₂).equations ↔
          nameAction.Models σ (resConf (res label C f₂).label (resConf label C f₂) f₁).equations := by
  rcases joint with ⟨σ₀, s₁, s₂⟩
  obtain ⟨disj, av₁₂, av₂₁⟩ := disjoint_of_different_root_children act₁ act₂ apart
    ⟨σ₀, info_known f₁ s₁⟩ madeDisj
  exact commute_disjoint_firings admitted₁ admitted₂ disj fresh₁₂ fresh₂₁ av₁₂ av₂₁ ⟨σ₀, s₁, s₂⟩

/-- Explicit list-indexed run of admitted firings of `located` at `QN`. -/
inductive FiringSeq :
    (O → Pattern) → Configuration Pattern O → List (Firing O QNE located PUnit.unit) →
      (O → Pattern) → Configuration Pattern O → Prop where
  | nil (label : O → Pattern) (C : Configuration Pattern O) : FiringSeq label C [] label C
  | cons {label : O → Pattern} {C : Configuration Pattern O}
      {label' : O → Pattern} {C' : Configuration Pattern O}
      (f : Firing O QNE located PUnit.unit) (fs : List (Firing O QNE located PUnit.unit))
      (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) f)
      (rest : FiringSeq (res label C f).label (resConf label C f) fs label' C') :
      FiringSeq label C (f :: fs) label' C'

/-- **Mazurkiewicz trace equivalence / Lipton adjacent swap** on firing sequences. -/
inductive TraceEquiv :
    (O → Pattern) → Configuration Pattern O →
      List (Firing O QNE located PUnit.unit) → List (Firing O QNE located PUnit.unit) → Prop where
  | refl {label : O → Pattern} {C : Configuration Pattern O}
      {fs : List (Firing O QNE located PUnit.unit)} {label' : O → Pattern}
      {C' : Configuration Pattern O} :
      FiringSeq label C fs label' C' → TraceEquiv label C fs fs
  | swap_head {label : O → Pattern} {C : Configuration Pattern O}
      {f₁ f₂ : Firing O QNE located PUnit.unit}
      {tail : List (Firing O QNE located PUnit.unit)}
      {label' : O → Pattern} {C' : Configuration Pattern O}
      (adm₁ : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) f₁)
      (adm₂ : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) f₂)
      (disj : SelectionDisjoint f₁.selection f₂.selection)
      (fresh₁₂ : f₂.Fresh QN (embed (res label C f₁).label (resConf label C f₁)))
      (fresh₂₁ : f₁.Fresh QN (embed (res label C f₂).label (resConf label C f₂)))
      (av₁₂ : ChecksAvoidMade label C f₁ f₂) (av₂₁ : ChecksAvoidMade label C f₂ f₁)
      (joint : ∃ σ : PSubst, nameAction.Models σ (f₁.information QN (embed label C)) ∧
        nameAction.Models σ (f₂.information QN (embed label C)))
      (rest : FiringSeq (res (res label C f₁).label (resConf label C f₁) f₂).label
        (resConf (res label C f₁).label (resConf label C f₁) f₂) tail label' C') :
      TraceEquiv label C (f₁ :: f₂ :: tail) (f₂ :: f₁ :: tail)
  | step_congr {label : O → Pattern} {C : Configuration Pattern O}
      {f : Firing O QNE located PUnit.unit}
      {fs₁ fs₂ : List (Firing O QNE located PUnit.unit)}
      (adm : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) f)
      (inner : TraceEquiv (res label C f).label (resConf label C f) fs₁ fs₂) :
      TraceEquiv label C (f :: fs₁) (f :: fs₂)
  | trans {label : O → Pattern} {C : Configuration Pattern O}
      {fs₁ fs₂ fs₃ : List (Firing O QNE located PUnit.unit)} :
      TraceEquiv label C fs₁ fs₂ → TraceEquiv label C fs₂ fs₃ → TraceEquiv label C fs₁ fs₃

/-- Equivalent knowledge stores admit the exact same subsequent firing sequences when openings
remain fresh across logically equivalent stores. -/
theorem firingSeq_congr_knowledge {label : O → Pattern} {C₁ C₂ : Configuration Pattern O}
    (samePres : C₁.present = C₂.present)
    (sameEqs : ∀ σ : PSubst, nameAction.Models σ C₁.equations ↔ nameAction.Models σ C₂.equations)
    {fs : List (Firing O QNE located PUnit.unit)} {label' : O → Pattern}
    {C₁' : Configuration Pattern O} (seq : FiringSeq label C₁ fs label' C₁')
    (freshAll : ∀ {lbl : O → Pattern} {K₁ K₂ : EquationStore Pattern} {pres : Finset O}
      {g : Firing O QNE located PUnit.unit},
      (∀ σ : PSubst, nameAction.Models σ K₁ ↔ nameAction.Models σ K₂) →
      g.Fresh QN (embed lbl ⟨K₁, pres⟩) → g.Fresh QN (embed lbl ⟨K₂, pres⟩)) :
    ∃ C₂' : Configuration Pattern O, FiringSeq label C₂ fs label' C₂' ∧
      C₁'.present = C₂'.present ∧
      (∀ σ : PSubst, nameAction.Models σ C₁'.equations ↔ nameAction.Models σ C₂'.equations) := by
  induction seq generalizing C₂ with
  | nil label C₁ => exact ⟨C₂, .nil label C₂, samePres, sameEqs⟩
  | @cons lbl C₁ lbl' C₁' f rest adm₁ restSeq ih =>
      obtain ⟨fr₁, sh₁, en₁, ⟨_, σ₀, sol₀⟩, ch₁, _⟩ := (RuleSyntax.admits_iff f).mp adm₁
      have eqInfo : ∀ σ : PSubst,
          nameAction.Models σ (f.information QN (embed lbl C₁)) ↔
            nameAction.Models σ (f.information QN (embed lbl C₂)) := by
        intro σ
        rw [OneFrame.information_eq, OneFrame.information_eq]
        simp only [Selection.problem, List.mem_append, SubstitutionAction.Models]
        constructor <;> intro s e m
        · rcases m with ((b | tk) | r) | t
          · exact (sameEqs σ).mp (fun e' m' => s e' (.inl (.inl (.inl m')))) e b
          · exact s e (.inl (.inl (.inr tk)))
          · exact s e (.inl (.inr r))
          · exact s e (.inr t)
        · rcases m with ((b | tk) | r) | t
          · exact (sameEqs σ).mpr (fun e' m' => s e' (.inl (.inl (.inl m')))) e b
          · exact s e (.inl (.inl (.inr tk)))
          · exact s e (.inl (.inr r))
          · exact s e (.inr t)
      have adm₂ : (RuleSyntax.step QN O QNE located).Admits (s := embed lbl C₂) f := by
        have c₂Eq : C₂ = ⟨C₂.equations, C₁.present⟩ := by cases C₂; cases samePres; rfl
        have fr₂ : f.Fresh QN (embed lbl C₂) := by
          rw [c₂Eq]; exact freshAll sameEqs fr₁
        have en₂ : Enabled (fun _ : O => ()) (embed lbl C₂).present (f.selection.commit (T := Unit)) := by
          change Enabled _ C₂.present _; rw [← samePres]; exact en₁
        refine (RuleSyntax.admits_iff f).mpr ⟨fr₂, sh₁, en₂,
          ⟨PUnit.unit, σ₀, (eqInfo σ₀).mp sol₀⟩, ?_, ?_⟩
        · intro c cIn b σ s₂
          cases b
          have h := ch₁ c cIn PUnit.unit σ ((eqInfo σ).mpr s₂)
          change checkHolds QN σ _ C₁.present c at h
          change checkHolds QN σ _ C₂.present c
          rw [← samePres]
          simpa [OneFrame.row_eq] using h
        · intro q qIn
          have nilC : (f.collectOpened QN) = [] := by
            simp [Firing.collectOpened, located_collect_nil f.member]
          rw [nilC] at qIn
          simp at qIn
      have sameLbl : (res lbl C₁ f).label = (res lbl C₂ f).label := by
        funext o
        by_cases m : o ∈ f.selection.made
        · obtain ⟨t, z⟩ := exists_mem_zip sh₁.2.2.2.2.1.symm m
          rw [result_label_made adm₁ z, result_label_made adm₂ z]
        · rw [result_label_old f m, result_label_old f m]
      have sameNextPres : (resConf lbl C₁ f).present = (resConf lbl C₂ f).present := by
        show fire C₁.present _ = fire C₂.present _
        rw [samePres]
      obtain ⟨C₂', seq₂', pEq, kEq⟩ := ih sameNextPres eqInfo
      rw [sameLbl] at seq₂'
      exact ⟨C₂', .cons f rest adm₂ seq₂', pEq, kEq⟩

/-- **Trace-equivalent firing sequences reach identical occurrences and labels, and equivalent
knowledge stores.** -/
theorem traceEquiv_sound {label : O → Pattern} {C : Configuration Pattern O}
    {fs₁ fs₂ : List (Firing O QNE located PUnit.unit)}
    (equiv : TraceEquiv label C fs₁ fs₂)
    (freshAll : ∀ {lbl : O → Pattern} {K₁ K₂ : EquationStore Pattern} {pres : Finset O}
      {g : Firing O QNE located PUnit.unit},
      (∀ σ : PSubst, nameAction.Models σ K₁ ↔ nameAction.Models σ K₂) →
      g.Fresh QN (embed lbl ⟨K₁, pres⟩) → g.Fresh QN (embed lbl ⟨K₂, pres⟩))
    {label' : O → Pattern} {C₁' : Configuration Pattern O}
    (seq₁ : FiringSeq label C fs₁ label' C₁') :
    ∃ C₂' : Configuration Pattern O, FiringSeq label C fs₂ label' C₂' ∧
      C₁'.present = C₂'.present ∧
      (∀ σ : PSubst, nameAction.Models σ C₁'.equations ↔ nameAction.Models σ C₂'.equations) := by
  induction equiv generalizing label' C₁' with
  | refl _ => exact ⟨C₁', seq₁, rfl, fun _ => Iff.rfl⟩
  | @swap_head _ _ f₁ f₂ tail _ _ adm₁ adm₂ disj fr₁₂ fr₂₁ av₁₂ av₂₁ joint _ =>
      cases seq₁ with
      | cons _ _ _ seqTail =>
          cases seqTail with
          | cons _ _ _ tailSeq =>
              obtain ⟨_, adm₂₁, presEq, lblEq, eqsEq⟩ :=
                commute_disjoint_firings adm₁ adm₂ disj fr₁₂ fr₂₁ av₁₂ av₂₁ joint
              rw [lblEq] at tailSeq
              obtain ⟨C₂', tailSeq₂, pEq, kEq⟩ :=
                firingSeq_congr_knowledge presEq eqsEq tailSeq freshAll
              exact ⟨C₂', .cons f₂ (f₁ :: tail) adm₂ (.cons f₁ tail adm₂₁ tailSeq₂), pEq, kEq⟩
  | @step_congr _ _ f _ fs₂' adm _ ih =>
      cases seq₁ with
      | cons _ _ _ restSeq =>
          obtain ⟨C₂', restSeq₂, pEq, kEq⟩ := ih restSeq
          exact ⟨C₂', .cons f fs₂' adm restSeq₂, pEq, kEq⟩
  | trans _ _ ih₁ ih₂ =>
      obtain ⟨Cₘ, seqₘ, p₁, k₁⟩ := ih₁ seq₁
      obtain ⟨C₂', seq₂, p₂, k₂⟩ := ih₂ seqₘ
      exact ⟨C₂', seq₂, p₁.trans p₂, fun σ => (k₁ σ).trans (k₂ σ)⟩

end Diamond

/-! ## Sharpness control: identical sibling reflections serialize at `openRoot` -/

/-- Two identical root reflections `@0?(0) @ Root` at distinct occurrences `0` and `1`. -/
def twinReflRows : ℕ → Pattern
  | 0 => atLoc (pReflect demoChan pZero) rootLoc
  | 1 => atLoc (pReflect demoChan pZero) rootLoc
  | _ => pZero

def twinReflStart : Configuration Pattern ℕ := ⟨[], {0, 1}⟩

/-- **Sharpness of `apart` in `commute_different_children`**: when two distinct root reflections
(`0` and `1`) share the **same** child location `Child(Root, @0, 0)`, each `openRootAt` is admitted
at `twinReflStart`, yet once `0` opens, `1`'s `openRootAt` is **refused at every opening** because
`Pending(Child(Root, @0, 0), Root)` is now present at their shared child location. -/
theorem identical_reflections_serialize_open :
    (∃ ρ₀, (RuleSyntax.step QN ℕ QNE located).Admits (s := embed twinReflRows twinReflStart)
      (openRootAt ρ₀ 0 2 3)) ∧
    (∃ ρ₁, (RuleSyntax.step QN ℕ QNE located).Admits (s := embed twinReflRows twinReflStart)
      (openRootAt ρ₁ 1 4 5)) ∧
    ∀ ρ₀, (RuleSyntax.step QN ℕ QNE located).Admits (s := embed twinReflRows twinReflStart)
        (openRootAt ρ₀ 0 2 3) →
      ∀ ρ₁, ¬ (RuleSyntax.step QN ℕ QNE located).Admits
        (s := embed (res twinReflRows twinReflStart (openRootAt ρ₀ 0 2 3)).label
          (resConf twinReflRows twinReflStart (openRootAt ρ₀ 0 2 3)))
        (openRootAt ρ₁ 1 4 5) := by
  have clean₀ : Clean (childLoc rootLoc demoChan pZero) twinReflRows twinReflStart := by
    intro o oIn σ _
    have oCases : o = 0 ∨ o = 1 := by simpa [twinReflStart] using oIn
    refine ⟨fun m' same => ?_, fun m' c' same => ?_, fun y same => ?_⟩
    · rcases oCases with rfl | rfl <;>
        { simp only [twinReflRows, atLoc, pendingTok] at same
          exact absurd (ReflLocatedStep.head_of_reading same) (by decide) }
    · rcases oCases with rfl | rfl <;>
        { simp only [twinReflRows, atLoc, doneTok] at same
          exact absurd (ReflLocatedStep.head_of_reading same) (by decide) }
    · rcases oCases with rfl | rfl <;>
        { simp only [twinReflRows, psubst_atLoc_any, psubst_rootLoc, psubst_childLoc] at same
          exact not_nameLaws_childLoc_rootLoc _ _ _ ((locatedFrame_name.atLoc_iff _ _ _ _).mp same).2.symm }
  obtain ⟨ρ₀, fr₀⟩ := ReflCorrespondence.open_fresh_exists twinReflRows twinReflStart 0 2 3
  obtain ⟨ρ₁, fr₁⟩ := ReflCorrespondence.open_fresh_exists twinReflRows twinReflStart 1 4 5
  have adm₀ := openRoot_admitted twinReflRows twinReflStart demoChan pZero 0 2 3
    (fun σ _ => NameLaws.refl _) clean₀ (by simp [twinReflStart]) (by decide)
    ⟨by simp [twinReflStart], by simp [twinReflStart]⟩
    (σ₀ := fun _ => none) (fun _ m => absurd m List.not_mem_nil) fr₀
  have adm₁ := openRoot_admitted twinReflRows twinReflStart demoChan pZero 1 4 5
    (fun σ _ => NameLaws.refl _) clean₀ (by simp [twinReflStart]) (by decide)
    ⟨by simp [twinReflStart], by simp [twinReflStart]⟩
    (σ₀ := fun _ => none) (fun _ m => absurd m List.not_mem_nil) fr₁
  refine ⟨⟨ρ₀, adm₀⟩, ⟨ρ₁, adm₁⟩, fun ρ₀' adm₀' ρ₁' adm₁₂ => ?_⟩
  have phase₁ := openRoot_enters_pending_S twinReflRows twinReflStart demoChan pZero 0 2 3 ρ₀'
    (fun σ _ => NameLaws.refl _) clean₀ adm₀'
  obtain ⟨σ, solved⟩ := solution_of_admitted adm₁₂
  have row1Old : (res twinReflRows twinReflStart (openRootAt ρ₀' 0 2 3)).label 1 =
      twinReflRows 1 := ReflCorrespondence.open_label_old _ _ ρ₀' 0 2 3 (by decide) (by decide)
  obtain ⟨chan, proc⟩ := ReflCorrespondence.open_reading
    (res twinReflRows twinReflStart (openRootAt ρ₀' 0 2 3)).label
    (resConf twinReflRows twinReflStart (openRootAt ρ₀' 0 2 3)) demoChan pZero 1 4 5 ρ₁'
    (fun τ _ => by rw [row1Old]; exact NameLaws.refl _) solved
  have childEq : NameLaws
      (psubst σ (psubst ρ₁' (childLoc rootLoc channelUnknown reflP)))
      (childLoc (psubst σ rootLoc) (psubst σ demoChan) (psubst σ pZero)) := by
    rw [psubst_childLoc, psubst_childLoc, psubst_rootLoc, psubst_rootLoc]
    exact nameLaws_childLoc_iff.mpr ⟨NameLaws.refl _, chan, proc⟩
  have tkRead := phase₁.reads σ (info_known _ solved)
  rw [psubst_pendingTok, psubst_childLoc] at tkRead
  exact ReflLocatedStep.check_fails_pending adm₁₂ ReflLocatedStep.openRoot_checks.1 solved
    childEq phase₁.present tkRead

#print axioms eq_heatChildN
#print axioms eq_coolAt
#print axioms eq_commChildAt
#print axioms commute_disjoint_firings
#print axioms commute_different_children
#print axioms firingSeq_congr_knowledge
#print axioms traceEquiv_sound
#print axioms identical_reflections_serialize_open

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflSystem
