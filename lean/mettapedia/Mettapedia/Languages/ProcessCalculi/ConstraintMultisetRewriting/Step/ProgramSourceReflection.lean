import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramReflection

/-!
# A reflection query as a source construct

The expression `reflect` asks whether some row is literally a returned quotation, by its raw
syntax. As a source construct it is a firing of the answer schema (take the thread, make its answer)
**carrying the raw query** (`reflectFiring`). The declared restriction is kept:

* **It is a reflection query, never an ordinary one** (`reflect_not_semantic`): its firing is not a
  firing of the ordinary step, since the raw query does not read labels through solutions.
* **Its answer is not a function of the represented rows** (`reflect_collision`): two
  configurations that represent the same rows, the thread and one returned quotation (once as a
  rigid label, once held through the knowledge), are answered differently: the answer `no` is
  admitted at the held configuration and refused at the rigid one. So the construct has no
  reference semantics on rows alone; its semantics is the firing on configurations.
* **Control: the ordinary version answers by the rows** (`ordinary_by_rows`): the same firing with
  the through-solutions query is refused at both configurations, as `Program.semantic_admission_iff`
  predicts from their common rows.
* **Admission** (`reflect_valid_iff`): the reflection firing is admitted exactly when the plain
  answer firing is and the raw query holds at the firing's cut.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramSourceReflection

open ProgramRows ProgramTranslation Program
open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (regionOf)

/-- The expression `reflect`. -/
def reflectE : Sx := t0 122
/-- The answers. -/
def noV : Sx := atom (.sym 124)

/-- The answer schema: take the thread evaluating `reflect`, make the answer under its
continuation. -/
def answerSchema (k : ℕ) : Schema :=
  ⟨[p3 29 (p0 122) (.var 0) (.var 1)], [], [p2 30 (p1 10 (p0 k)) (.var 1)]⟩

/-- **The reflection firing**: the answer schema's firing at scope `n` on the thread occurrence,
carrying the raw query with region `seen`. -/
def reflectFiring (answer : ℕ) (n : ℕ) (o : Occ) (seen : Finset Occ) :
    AnnotatedRuns.Firing Tm (Subst rows) Occ :=
  ⟨(answerSchema answer).rule n, [rawQuoted seen], ⟨[o], [], madeAt n 0 (answerSchema answer).make⟩⟩

/-- The same firing with the ordinary, through-solutions query. -/
def ordinaryFiring (answer : ℕ) (n : ℕ) (o : Occ) (seen : Finset Occ) :
    AnnotatedRuns.Firing Tm (Subst rows) Occ :=
  ⟨(answerSchema answer).rule n, [(semanticQuoted seen).1], ⟨[o], [], madeAt n 0 (answerSchema answer).make⟩⟩

/-- **The reflection firing is not a firing of the ordinary step.** -/
theorem reflect_not_semantic (answer : ℕ) (n : ℕ) (o : Occ) (seen : Finset Occ) :
    ¬ Semantic.IsSemantic A (reflectFiring answer n o seen) := fun reads =>
  rawQuoted_not_semantic seen (reads _ (List.mem_singleton_self _))

/-- **Admission of the reflection firing**: the plain answer firing is admitted and the raw query
holds at the firing's cut. -/
theorem reflect_valid_iff (answer : ℕ) (n : ℕ) (o : Occ) (seen : Finset Occ) (C : Config) :
    (reflectFiring answer n o seen).Valid A Occ.label C ↔
      ((answerSchema answer).firing n [o] []).Valid A Occ.label C ∧
        (rawQuoted seen).Ask A (((answerSchema answer).firing n [o] []).selection.problem Occ.label
          ((answerSchema answer).firing n [o] []).rule C) Occ.label C.present := by
  constructor
  · intro valid
    exact ⟨⟨valid.firing, fun q h => absurd h List.not_mem_nil⟩,
      valid.observations _ (List.mem_singleton_self _)⟩
  · rintro ⟨plain, asked⟩
    exact ⟨plain.firing, fun q h => by rw [List.mem_singleton.mp h]; exact asked⟩

/-! ## The collision -/

/-- The rows of the collision: the thread asking, and one returned quotation. -/
def collisionRows : List Sx := [ev reflectE nil nil, ret quotedValue nil]

/-- The rigid configuration: both rows as labels. -/
noncomputable def rigid : Config := initial collisionRows

/-- The thread occurrence. -/
def threadOcc : Occ := ⟨embed (ev reflectE nil nil), 0, 0⟩
/-- The quotation held through the knowledge. -/
def heldOcc' : Occ := ⟨heldLabel, 0, 1⟩

/-- The held configuration: the thread, and the label `ret X nil` with the knowledge
`X = code a nil`. -/
noncomputable def held : Config := ⟨[(.var (0, 0), embed quotedValue)], ([threadOcc, heldOcc'] : List Occ).toFinset⟩

theorem threadOcc_ne_heldOcc' : threadOcc ≠ heldOcc' := fun h => by
  have := congrArg Occ.index h
  simp [threadOcc, heldOcc'] at this

theorem rigid_represents : Represents rigid (collisionRows : Multiset Sx) 1 := initial_represents _

theorem held_represents' : Represents held (collisionRows : Multiset Sx) 1 := by
  let σ₀ : Subst rows := fun v => if v = (0, 0) then embed quotedValue else .var v
  refine ⟨⟨σ₀, ?_⟩, ?_, ?_, fun o => if o = threadOcc then ev reflectE nil nil else ret quotedValue nil,
    ?_, ?_⟩
  · intro e member
    rw [List.mem_singleton.mp member]
    change σ₀ (0, 0) = σ₀.applyTerm (embed quotedValue)
    rw [apply_embed]
    rfl
  · intro e member
    rw [List.mem_singleton.mp member]
    refine ⟨fun v hv => ?_, embed_bounded 1 _⟩
    rw [Term.mem_freeVars_var (σ := rows)] at hv
    rw [hv]
    exact Nat.zero_lt_one
  · intro o member
    rcases List.mem_cons.mp (List.mem_toFinset.mp member) with rfl | member
    · exact ⟨Nat.zero_lt_one, embed_bounded 1 _⟩
    · rw [List.mem_singleton.mp member]
      refine ⟨Nat.zero_lt_one, fun v hv => ?_⟩
      rcases mem_freeVars_node.mp hv with hv | hv
      · simp [Term.freeVars] at hv
      · rcases mem_freeVars_node.mp hv with hv | hv
        · rw [Term.mem_freeVars_var (σ := rows)] at hv
          rw [hv]
          exact Nat.zero_lt_one
        · simp [Term.freeVars] at hv
  · intro σ solved o member
    rcases List.mem_cons.mp (List.mem_toFinset.mp member) with rfl | member
    · show σ.applyTerm threadOcc.label =
        embed (if threadOcc = threadOcc then ev reflectE nil nil else ret quotedValue nil)
      rw [if_pos rfl]
      exact apply_embed σ _
    · rw [List.mem_singleton.mp member]
      show σ.applyTerm heldOcc'.label =
        embed (if heldOcc' = threadOcc then ev reflectE nil nil else ret quotedValue nil)
      rw [if_neg (Ne.symm threadOcc_ne_heldOcc')]
      exact held_observed σ solved
  · change Multiset.map _ (([threadOcc, heldOcc'] : List Occ).toFinset).val = _
    rw [List.toFinset_val, List.Nodup.dedup (List.nodup_cons.mpr
      ⟨fun h => threadOcc_ne_heldOcc' (List.mem_singleton.mp h), List.nodup_singleton _⟩), Multiset.map_coe]
    simp only [List.map_cons, List.map_nil, if_neg (Ne.symm threadOcc_ne_heldOcc'), ↓reduceIte]
    rfl

/-- The no-firing at the thread occurrence. -/
noncomputable def noAnswer : AnnotatedRuns.Firing Tm (Subst rows) Occ := reflectFiring 124 1 threadOcc ∅

theorem threadOcc_in_rigid : threadOcc ∈ rigid.present :=
  List.mem_toFinset.mpr List.mem_cons_self

theorem threadOcc_in_held : threadOcc ∈ held.present :=
  List.mem_toFinset.mpr List.mem_cons_self

/-- The plain answer firing is admitted at a configuration representing the collision rows, at
the thread occurrence. -/
theorem plain_valid {C : Config} (rep : Represents C (collisionRows : Multiset Sx) 1)
    (present : threadOcc ∈ C.present)
    (reads : ∀ σ, A.Models σ C.equations → σ.applyTerm threadOcc.label = embed (ev reflectE nil nil)) :
    ((answerSchema 124).firing 1 [threadOcc] []).Valid A Occ.label C := by
  obtain ⟨consistent, eqs, pres, value, observed, image⟩ := rep
  have readValue : value threadOcc = ev reflectE nil nil := by
    obtain ⟨σ, solved⟩ := consistent
    exact embed_injective ((observed σ solved threadOcc present).symm.trans (reads σ solved))
  exact (fire_at (r := answerSchema 124) ⟨by decide, by decide⟩ consistent eqs pres observed
    (Program.args [nil, nil]) (List.nodup_singleton _)
    (fun o h => by rw [List.mem_singleton.mp h]; exact present)
    (fun o h => absurd h List.not_mem_nil) (fun o _ h => absurd h List.not_mem_nil)
    (.cons (by rw [readValue]; rfl) .nil) .nil).1

theorem rigid_reads (σ : Subst rows) (_ : A.Models σ rigid.equations) :
    σ.applyTerm threadOcc.label = embed (ev reflectE nil nil) := apply_embed σ _

theorem held_reads (σ : Subst rows) (_ : A.Models σ held.equations) :
    σ.applyTerm threadOcc.label = embed (ev reflectE nil nil) := apply_embed σ _

/-- **The collision**: both configurations represent the same rows; the answer `no` is admitted at
the held configuration and refused at the rigid one. -/
theorem reflect_collision :
    Represents rigid (collisionRows : Multiset Sx) 1 ∧ Represents held (collisionRows : Multiset Sx) 1 ∧
      noAnswer.Valid A Occ.label held ∧ ¬ noAnswer.Valid A Occ.label rigid := by
  refine ⟨rigid_represents, held_represents', ?_, ?_⟩
  · refine (reflect_valid_iff 124 1 threadOcc ∅ held).mpr
      ⟨plain_valid held_represents' threadOcc_in_held held_reads, fun σ _ => ?_⟩
    change regionOf Occ.label held.present (fun t => quotedRow (decode t)) = ∅
    refine Finset.filter_eq_empty_iff.mpr fun o member => ?_
    rcases List.mem_cons.mp (List.mem_toFinset.mp member) with rfl | member
    · show ¬ quotedRow (decode (embed (ev reflectE nil nil))) = true
      rw [decode_embed]; decide
    · rw [List.mem_singleton.mp member]
      show ¬ quotedRow (decode heldLabel) = true
      decide
  · intro valid
    obtain ⟨-, asked⟩ := (reflect_valid_iff 124 1 threadOcc ∅ rigid).mp valid
    obtain ⟨σ, solved⟩ := (plain_valid rigid_represents threadOcc_in_rigid rigid_reads).firing.consistent
    have region := asked σ solved
    change regionOf Occ.label rigid.present (fun t => quotedRow (decode t)) = ∅ at region
    have quotation : (⟨embed (ret quotedValue nil), 0, 1⟩ : Occ) ∈ rigid.present :=
      List.mem_toFinset.mpr (List.mem_cons_of_mem _ List.mem_cons_self)
    have : (⟨embed (ret quotedValue nil), 0, 1⟩ : Occ) ∈
        regionOf Occ.label rigid.present (fun t => quotedRow (decode t)) :=
      Finset.mem_filter.mpr ⟨quotation, by
        show quotedRow (decode (embed (ret quotedValue nil))) = true
        rw [decode_embed]; rfl⟩
    rw [region] at this
    exact Finset.notMem_empty _ this

/-- **Control: the ordinary version answers by the rows**: with the through-solutions query, the
answer `no` is refused at both configurations, since both represent a returned quotation. -/
theorem ordinary_by_rows :
    ¬ (ordinaryFiring 124 1 threadOcc ∅).Valid A Occ.label rigid ∧
      ¬ (ordinaryFiring 124 1 threadOcc ∅).Valid A Occ.label held := by
  constructor
  · intro valid
    obtain ⟨σ, solved⟩ := valid.firing.consistent
    have region := valid.observations _ (List.mem_singleton_self _) σ solved
    change regionOf Occ.label rigid.present (fun t => quotedRow (decode (σ.applyTerm t))) = ∅ at region
    have quotation : (⟨embed (ret quotedValue nil), 0, 1⟩ : Occ) ∈ rigid.present :=
      List.mem_toFinset.mpr (List.mem_cons_of_mem _ List.mem_cons_self)
    have : (⟨embed (ret quotedValue nil), 0, 1⟩ : Occ) ∈
        regionOf Occ.label rigid.present (fun t => quotedRow (decode (σ.applyTerm t))) :=
      Finset.mem_filter.mpr ⟨quotation, by
        change quotedRow (decode (σ.applyTerm (embed (ret quotedValue nil)))) = true
        rw [apply_embed, decode_embed]; rfl⟩
    rw [region] at this
    exact Finset.notMem_empty _ this
  · intro valid
    obtain ⟨σ, solved⟩ := valid.firing.consistent
    have region := valid.observations _ (List.mem_singleton_self _) σ solved
    change regionOf Occ.label held.present (fun t => quotedRow (decode (σ.applyTerm t))) = ∅ at region
    have models : A.Models σ held.equations := fun e member => solved e
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ member)))
    have quotation : heldOcc' ∈ held.present :=
      List.mem_toFinset.mpr (List.mem_cons_of_mem _ List.mem_cons_self)
    have : heldOcc' ∈ regionOf Occ.label held.present (fun t => quotedRow (decode (σ.applyTerm t))) :=
      Finset.mem_filter.mpr ⟨quotation, by
        change quotedRow (decode (σ.applyTerm heldLabel)) = true
        rw [held_observed σ models, decode_embed]; rfl⟩
    rw [region] at this
    exact Finset.notMem_empty _ this

#print axioms reflect_not_semantic
#print axioms reflect_valid_iff
#print axioms held_represents'
#print axioms plain_valid
#print axioms reflect_collision
#print axioms ordinary_by_rows

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramSourceReflection
