import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamesOnTheStep.CodeOnlyLoading

/-!
# Micromath on the step is sound

Micromath's rule set (`CodeOnlyLoading.micromath`) runs on the first-order step with issuing
(`mm`): its six rules, where `define` issues the defined symbol, whose operands do not mention it,
as in Micromath's own kernel.

**Models.** Every symbol denotes a binary function on a domain (`ι : Expr → D → D → D`), the codes
`X` and `Y` denote the two projections (`Projections`), and `thm o f x y` is true when
`o(A,B) = f(x(A,B), y(A,B))` for all `A B` (`Holds`). A store is sound in a model when every theorem it
holds is true (`Sound`).

* `mm_step_sound`: an admitted firing keeps a store sound, after reinterpreting at most the name it
  issues: a definition interprets its fresh name by its body. Freshness is what makes this possible:
  no stored theorem mentions the issued name yet.
* `mm_run_sound`: **every run keeps every model of its start**, reinterpreting only the names it
  issues.
* `mm_valid`: from the empty store, **every theorem a run stores that mentions no name issued along
  it is true in every model of the codes**.

**Freshness is necessary** (`reissue_unsatisfiable`): without it, `define` issues `0` twice, as `X`
and as `Y`, and no model on a domain with two elements makes both stored theorems true.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamesOnTheStep.MicromathSoundness

open IssuingControls CodeOnlyLoading

/-! ## The step -/

/-- Micromath's six rules as a permission on firings, with the names each issues. A definition's
operands do not mention the symbol it defines. -/
abbrev micromathTheory (f : Fir) (fresh : List ℕ) : Prop :=
  (∃ τ, f.rule = proj1.inst τ ∧ fresh = []) ∨ (∃ τ, f.rule = proj2.inst τ ∧ fresh = []) ∨
    (∃ τ, f.rule = refl.inst τ ∧ fresh = []) ∨ (∃ τ, f.rule = substitute1.inst τ ∧ fresh = []) ∨
    (∃ τ, f.rule = substitute2.inst τ ∧ fresh = []) ∨
    (∃ τ n, f.rule = define.inst τ ∧ fresh = [n] ∧ τ 3 = .name n ∧
      n ∉ (τ 0).support ∧ n ∉ (τ 1).support ∧ n ∉ (τ 2).support)

/-- Micromath on the first-order step with issuing. -/
abbrev mm := withLedger base (issuing micromathTheory)

theorem mm_checksUses : ChecksUses naming (issuing micromathTheory) :=
  fun _ _ _ _ admitted => admitted.1.2.2

/-! ## Models -/

/-- The term of the theorem `thm o f x y`. -/
def thmTerm (o f x y : Expr) : Expr := .app (.app (.app (.app (.sym 100) o) f) x) y

theorem thm_inst (τ : ℕ → Expr) (o f x y : Pat) :
    (thm o f x y).inst τ = thmTerm (o.inst τ) (f.inst τ) (x.inst τ) (y.inst τ) := rfl

theorem thmTerm_inj {o f x y o' f' x' y' : Expr} (same : thmTerm o f x y = thmTerm o' f' x' y') :
    o = o' ∧ f = f' ∧ x = x' ∧ y = y' := by
  simp only [thmTerm, Expr.app.injEq, true_and] at same
  exact ⟨same.1.1.1, same.1.1.2, same.1.2, same.2⟩

variable {D : Type}

/-- The codes `X` and `Y` denote the projections. -/
def Projections (ι : Expr → D → D → D) : Prop :=
  ι projX = (fun a _ => a) ∧ ι projY = (fun _ b => b)

/-- A term is true in a model when, read as a theorem `o(A,B) = f(x(A,B), y(A,B))`, it holds. -/
def Holds (ι : Expr → D → D → D) (e : Expr) : Prop :=
  ∀ o f x y, e = thmTerm o f x y → ∀ a b, ι o a b = ι f (ι x a b) (ι y a b)

/-- Every theorem the store holds is true. -/
def Sound (ι : Expr → D → D → D) (C : Conf) : Prop := ∀ o ∈ C.present, Holds ι o.1

theorem holds_thm {ι : Expr → D → D → D} {o f x y : Expr}
    (truth : ∀ a b, ι o a b = ι f (ι x a b) (ι y a b)) : Holds ι (thmTerm o f x y) := by
  intro o' f' x' y' same
  obtain ⟨rfl, rfl, rfl, rfl⟩ := thmTerm_inj same
  exact truth

theorem truth_of {ι : Expr → D → D → D} {o f x y : Expr} (holds : Holds ι (thmTerm o f x y)) :
    ∀ a b, ι o a b = ι f (ι x a b) (ι y a b) :=
  holds o f x y rfl

/-- Reinterpreting a name: terms that do not mention it keep their denotation. -/
theorem update_away {ι : Expr → D → D → D} {n : ℕ} (body : D → D → D) {t : Expr}
    (outside : n ∉ t.support) : Function.update ι (.name n) body t = ι t := by
  apply Function.update_of_ne
  rintro rfl
  simp at outside

/-- Reinterpreting a name nobody mentions keeps a term's truth. -/
theorem holds_update {ι : Expr → D → D → D} {n : ℕ} (body : D → D → D) {e : Expr}
    (unmentioned : n ∉ e.support) (holds : Holds ι e) :
    Holds (Function.update ι (.name n) body) e := by
  intro o f x y same a b
  subst same
  simp only [thmTerm, Expr.support_app, Expr.support_sym, Finset.empty_union,
    Finset.mem_union, not_or] at unmentioned
  rw [update_away body unmentioned.1.1.1, update_away body unmentioned.1.1.2,
    update_away body unmentioned.1.2, update_away body unmentioned.2]
  exact holds o f x y rfl a b

/-! ## One step -/

/-- The read premises of an admitted firing are true in a sound model. -/
theorem premise_true {σ : Conf × Set ℕ} {f : Fir × List ℕ} (admitted : mm.Admits (s := σ) f)
    {ι : Expr → D → D → D} (sound : Sound ι σ.1) {q : Expr} (premise : q ∈ f.1.rule.read) :
    Holds ι q := by
  have valid := valid_of admitted
  obtain ⟨o, selected, same⟩ := forall₂_left (reads_match valid) q premise
  rw [same]
  exact sound o (read_present valid selected)

/-- Soundness after a firing: the old occurrences keep their truth, and the made ones are true. -/
theorem sound_after {σ : Conf × Set ℕ} {f : Fir × List ℕ} (admitted : mm.Admits (s := σ) f)
    {ι : Expr → D → D → D} (old : ∀ o ∈ σ.1.present, Holds ι o.1)
    (made : ∀ t ∈ f.1.rule.produce, Holds ι t) :
    Sound ι (mm.result (s := σ) f admitted).1 := by
  intro o present
  rcases (present_after admitted).mp present with ⟨inOld, _⟩ | inMade
  · exact old o inOld
  · exact made o.1 (made_label (valid_of admitted) inMade)

/-- **An admitted firing keeps a store sound**, reinterpreting at most the name it issues. -/
theorem mm_step_sound {σ : Conf × Set ℕ} (f : Fir × List ℕ) (admitted : mm.Admits (s := σ) f)
    (invariant : Invariant naming σ) (ι : Expr → D → D → D) (projections : Projections ι)
    (sound : Sound ι σ.1) :
    ∃ ι' : Expr → D → D → D, Projections ι' ∧ Sound ι' (mm.result (s := σ) f admitted).1 ∧
      ∀ e, (∀ n ∈ f.2, e ≠ .name n) → ι' e = ι e := by
  have premise := fun {q : Expr} (member : q ∈ f.1.rule.read) => premise_true admitted sound member
  rcases admitted.2.2 with ⟨τ, hrule, _⟩ | ⟨τ, hrule, _⟩ | ⟨τ, hrule, _⟩ | ⟨τ, hrule, _⟩ |
      ⟨τ, hrule, _⟩ | ⟨τ, n, hrule, hfresh, issuedSlot, free0, free1, free2⟩
  · -- proj1: `x = X(x, y)`
    refine ⟨ι, projections, sound_after admitted sound ?_, fun _ _ => rfl⟩
    rw [hrule]
    intro t member
    simp only [Schema.inst, proj1, List.map_cons, List.map_nil, List.mem_singleton, thm_inst] at member
    subst member
    apply holds_thm
    intro a b
    simp [Pat.inst, projections.1]
  · -- proj2: `y = Y(x, y)`
    refine ⟨ι, projections, sound_after admitted sound ?_, fun _ _ => rfl⟩
    rw [hrule]
    intro t member
    simp only [Schema.inst, proj2, List.map_cons, List.map_nil, List.mem_singleton, thm_inst] at member
    subst member
    apply holds_thm
    intro a b
    simp [Pat.inst, projections.2]
  · -- refl: `a = a(X, Y)`
    refine ⟨ι, projections, sound_after admitted sound ?_, fun _ _ => rfl⟩
    rw [hrule]
    intro t member
    simp only [Schema.inst, CodeOnlyLoading.refl, List.map_cons, List.map_nil, List.mem_singleton,
      thm_inst] at member
    subst member
    apply holds_thm
    intro a b
    simp [Pat.inst, projections.1, projections.2]
  · -- substitute1
    have main := truth_of (premise (q := thmTerm (τ 0) (τ 1) (τ 2) (τ 3))
      (by rw [hrule]; simp [Schema.inst, substitute1, thm_inst, Pat.inst]))
    have su := truth_of (premise (q := thmTerm (τ 6) (τ 2) (τ 4) (τ 5))
      (by rw [hrule]; simp [Schema.inst, substitute1, thm_inst, Pat.inst]))
    have sv := truth_of (premise (q := thmTerm (τ 7) (τ 3) (τ 4) (τ 5))
      (by rw [hrule]; simp [Schema.inst, substitute1, thm_inst, Pat.inst]))
    have sx := truth_of (premise (q := thmTerm (τ 8) (τ 0) (τ 4) (τ 5))
      (by rw [hrule]; simp [Schema.inst, substitute1, thm_inst, Pat.inst]))
    refine ⟨ι, projections, sound_after admitted sound ?_, fun _ _ => rfl⟩
    rw [hrule]
    intro t member
    simp only [Schema.inst, substitute1, List.map_cons, List.map_nil, List.mem_singleton,
      thm_inst] at member
    subst member
    apply holds_thm
    intro a b
    simp only [Pat.inst]
    rw [sx, main, su, sv]
  · -- substitute2
    have main := truth_of (premise (q := thmTerm (τ 0) (τ 1) (τ 2) (τ 3))
      (by rw [hrule]; simp [Schema.inst, substitute2, thm_inst, Pat.inst]))
    have su := truth_of (premise (q := thmTerm (τ 6) (τ 2) (τ 4) (τ 5))
      (by rw [hrule]; simp [Schema.inst, substitute2, thm_inst, Pat.inst]))
    have sv := truth_of (premise (q := thmTerm (τ 7) (τ 3) (τ 4) (τ 5))
      (by rw [hrule]; simp [Schema.inst, substitute2, thm_inst, Pat.inst]))
    have sx := truth_of (premise (q := thmTerm (τ 8) (τ 1) (τ 6) (τ 7))
      (by rw [hrule]; simp [Schema.inst, substitute2, thm_inst, Pat.inst]))
    refine ⟨ι, projections, sound_after admitted sound ?_, fun _ _ => rfl⟩
    rw [hrule]
    intro t member
    simp only [Schema.inst, substitute2, List.map_cons, List.map_nil, List.mem_singleton,
      thm_inst] at member
    subst member
    apply holds_thm
    intro a b
    simp only [Pat.inst]
    rw [sx, su, sv, main]
  · -- define: interpret the fresh name by the body
    have fresh : n ∉ σ.2 := admitted.2.1.2.1 n (by rw [hfresh]; exact List.mem_singleton_self n)
    have unmentioned : ∀ o ∈ σ.1.present, n ∉ o.1.support := by
      intro o present named
      exact fresh (invariant (mem_configurationNames.mpr
        (Or.inr ⟨o, present, by simpa using named⟩)))
    refine ⟨Function.update ι (.name n) (fun a b => ι (τ 0) (ι (τ 1) a b) (ι (τ 2) a b)),
      ⟨?_, ?_⟩, ?_, ?_⟩
    · rw [update_away _ (by simp [projX, quote])]
      exact projections.1
    · rw [update_away _ (by simp [projY, quote])]
      exact projections.2
    · refine sound_after admitted
        (fun o present => holds_update _ (unmentioned o present) (sound o present)) ?_
      rw [hrule]
      intro t member
      simp only [Schema.inst, define, List.map_cons, List.map_nil, List.mem_singleton,
        thm_inst] at member
      subst member
      apply holds_thm
      intro a b
      simp only [Pat.inst, issuedSlot]
      rw [Function.update_self, update_away _ free0, update_away _ free1, update_away _ free2]
    · intro e notIssued
      apply Function.update_of_ne
      exact notIssued n (by rw [hfresh]; exact List.mem_singleton_self n)

/-! ## Runs -/

/-- **Every run keeps every model of its start**, reinterpreting only the names it issues. -/
theorem mm_run_sound : ∀ {σ : Conf × Set ℕ} (r : mm.Run σ), Invariant naming σ →
    ∀ (ι : Expr → D → D → D), Projections ι → Sound ι σ.1 →
      ∃ ι' : Expr → D → D → D, Projections ι' ∧ Sound ι' r.last.1 ∧
        ∀ e, (∀ n ∈ issuedAlong r, e ≠ .name n) → ι' e = ι e
  | _, .nil _, _, ι, projections, sound => ⟨ι, projections, sound, fun _ _ => rfl⟩
  | _, .cons f admitted rest, invariant, ι, projections, sound => by
      obtain ⟨ι₁, projections₁, sound₁, agrees₁⟩ :=
        mm_step_sound f admitted invariant ι projections sound
      obtain ⟨ι₂, projections₂, sound₂, agrees₂⟩ :=
        mm_run_sound rest (invariant_result mm_checksUses f admitted invariant) ι₁ projections₁ sound₁
      refine ⟨ι₂, projections₂, sound₂, fun e notIssued => ?_⟩
      rw [agrees₂ e (fun n member => notIssued n (List.mem_append_right _ member)),
        agrees₁ e (fun n member => notIssued n (List.mem_append_left _ member))]

/-- The empty store with nothing issued. -/
def emptyStart : Conf × Set ℕ := (⟨[], ∅⟩, ∅)

theorem emptyStart_invariant : Invariant naming emptyStart := by
  intro n mentioned
  rcases mem_configurationNames.mp mentioned with ⟨_, member, _⟩ | ⟨_, member, _⟩
  · exact absurd member List.not_mem_nil
  · simp [emptyStart] at member

/-- **Every theorem a run stores that mentions no issued name is true in every model of the
codes.** -/
theorem mm_valid (r : mm.Run emptyStart) (ι : Expr → D → D → D) (projections : Projections ι)
    {o : Occ} (stored : o ∈ r.last.1.present) {p f x y : Expr} (stated : o.1 = thmTerm p f x y)
    (closed : ∀ n ∈ issuedAlong r, n ∉ (thmTerm p f x y).support) :
    ∀ a b, ι p a b = ι f (ι x a b) (ι y a b) := by
  obtain ⟨ι', _, sound, agrees⟩ := mm_run_sound r emptyStart_invariant ι projections
    (fun o member => by simp [emptyStart] at member)
  have truth := truth_of (stated ▸ sound o stored)
  have atom : ∀ t ∈ [p, f, x, y], ι' t = ι t := by
    intro t member
    apply agrees t
    intro n issued same
    apply closed n issued
    subst same
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> simp [thmTerm]
  intro a b
  have := truth a b
  rwa [atom p (by simp), atom f (by simp), atom x (by simp), atom y (by simp)] at this

/-! ## Freshness is necessary -/

/-- `define` without freshness: the issued name need not be new. -/
abbrev mmReissue := withLedger base (usesOnly micromathTheory)

/-- The fillings `0 := X(X, Y)` and `0 := Y(X, Y)`. -/
def asX : ℕ → Expr := fun i => [projX, projX, projY, .name 0].getD i (.sym 0)
def asY : ℕ → Expr := fun i => [projY, projX, projY, .name 0].getD i (.sym 0)

theorem define_writes {τ : ℕ → Expr} (onlyZero : ∀ p ∈ define.patterns, ∀ i ∈ p.holes,
      ∀ m ∈ (τ i).support, m = 0)
    {queries : List (PredicateQueryAdmission.Query Expr Unit Occ)} {sel : Selection Occ} {n : ℕ}
    (written : n ∈ firingNames Expr.names (⟨define.inst τ, queries, sel⟩ : Fir)) : n = 0 := by
  obtain ⟨p, member, i, inHoles, held⟩ :=
    codeOnly_writes (micromath_codeOnly define (by simp [micromath])) τ queries sel written
  exact onlyZero p member i inHoles n held

theorem reissue1 : mmReissue.Admits (s := emptyStart)
    (⟨define.inst asX, [], ⟨[], [], [(thmTerm (.name 0) projX projX projY, 0)]⟩⟩, [0]) := by
  refine admits_of (by decide) (by decide) rfl rfl rfl (by decide) (by decide) rfl (no_checks rfl)
    ⟨?_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨asX, 0, rfl, rfl, rfl, by decide, by decide,
      by decide⟩))))⟩
  intro n written
  rw [define_writes (by decide) written]
  simp

theorem reissue2 : mmReissue.Admits (s := mmReissue.result (s := emptyStart) _ reissue1)
    (⟨define.inst asY, [], ⟨[], [], [(thmTerm (.name 0) projY projX projY, 1)]⟩⟩, [0]) := by
  refine admits_of (by decide) (by decide) rfl rfl rfl (by decide) (by decide) rfl (no_checks rfl)
    ⟨?_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨asY, 0, rfl, rfl, rfl, by decide, by decide,
      by decide⟩))))⟩
  intro n written
  rw [define_writes (by decide) written]
  simp

/-- The store after `0` was issued twice. -/
noncomputable def reissued : Conf × Set ℕ :=
  mmReissue.result (s := mmReissue.result (s := emptyStart) _ reissue1) _ reissue2

/-- **Without freshness, no model on a domain with two elements makes the store true.** -/
theorem reissue_unsatisfiable :
    ¬ ∃ ι : Expr → Bool → Bool → Bool, Projections ι ∧ Sound ι reissued.1 := by
  rintro ⟨ι, ⟨isX, isY⟩, sound⟩
  have first := truth_of (sound (thmTerm (.name 0) projX projX projY, 0) (by decide))
  have second := truth_of (sound (thmTerm (.name 0) projY projX projY, 1) (by decide))
  have same := (first true false).symm.trans (second true false)
  rw [isX, isY] at same
  exact Bool.noConfusion same

#print axioms mm_step_sound
#print axioms mm_run_sound
#print axioms mm_valid
#print axioms reissue_unsatisfiable

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamesOnTheStep.MicromathSoundness
