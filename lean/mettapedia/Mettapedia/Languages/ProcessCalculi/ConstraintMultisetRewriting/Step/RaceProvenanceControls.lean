import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RaceProvenance
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RaceHistoriesControls

/-!
# Controls for provenance bisimilarity and single assignment

## Provenance is strictly finer than history-preserving identity (`provenance_strictly_finer`)

R71's witness (`HistoryControls`): `C₀ = {g₁}` and `D₀ = {g₂, w₂}`, each a single run of three
firings under the same rules, with causal pasts `∅, {0}, {0, 1}`. They are history-preserving and
record bisimilar. The third firing takes from the first and the second in `C₀` (`e₂` takes `y₁` from
`e₀` and `z₁` from `e₁`), and from the second only in `D₀` (`d₂` takes `w₂`, present from the start,
and `z₂` from `d₁`). The provenance formula `⟨(R₀, ∅)⟩⟨(R₁, {0})⟩⟨(R₂, {0, 1})⟩⊤` holds at `C₀` and
fails at `D₀`, so they are not provenance bisimilar.

Both starts are single-assignment (`singleAssignment_C₀`, `singleAssignment_D₀`), which gives their
reuse-freedom without enumerating runs.

## Each condition of single assignment is needed

* **Something made is present at the start** (`Remade.violates`): R71's reuse control, where `t`
  takes `a` and makes `b`, and `u` takes `b` and makes `a`, from `{a}`. Makers are unique and take
  something; `a` is made and present; the start is not reuse-free.
* **Two makers** (`TwoMakers.violates`): `m₁` takes `t₁` and `m₂` takes `t₂`, both make `o`; `use`
  takes `o`. From `{t₁, t₂}`: nothing made is present and every maker takes something; after
  `m₁, use`, `m₂` makes `o` again.
* **A maker that takes nothing** (`Spring.violates`): `mk` takes nothing and makes `o`; `use` takes
  `o`. From `∅`: nothing made is present and makers are unique; after `mk, use`, `mk` makes `o`
  again.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.ProvenanceControls

open AnnotatedRuns (Firing)
open MeTTaCalculus.OccurrenceCommits (Enabled)
open Mettapedia.GSLT.HennessyMilner (Formula)

universe uT uS

variable {T : Type uT} {S : Type uS} (τ : T) (A : SubstitutionAction T S)

/-! ## Direct provenance on short records -/

section Direct

variable {O : Type*} [DecidableEq O]

theorem provDirect_nil (e : Entry O) : provDirect ([] : ExtRecord O) e = ∅ := by
  ext i
  rw [mem_provDirect]
  simp

theorem provDirect_one (a : Entry O) (p : Finset ℕ) (e : Entry O)
    (overlap : ¬ Disjoint a.made.toFinset e.taken.toFinset) : provDirect [(a, p)] e = {0} := by
  ext i
  rw [mem_provDirect, Finset.mem_singleton]
  constructor
  · rintro ⟨lt, -⟩
    simpa using lt
  · rintro rfl
    exact ⟨by simp, (a, p), rfl, overlap⟩

theorem provDirect_both (a b : Entry O) (p q : Finset ℕ) (e : Entry O)
    (first : ¬ Disjoint a.made.toFinset e.taken.toFinset)
    (second : ¬ Disjoint b.made.toFinset e.taken.toFinset) :
    provDirect [(a, p), (b, q)] e = {0, 1} := by
  ext i
  rw [mem_provDirect, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨lt, -⟩
    simp only [List.length_cons, List.length_nil] at lt
    omega
  · rintro (rfl | rfl)
    · exact ⟨by simp, (a, p), rfl, first⟩
    · exact ⟨by simp, (b, q), rfl, second⟩

theorem provDirect_second (a b : Entry O) (p q : Finset ℕ) (e : Entry O)
    (first : Disjoint a.made.toFinset e.taken.toFinset)
    (second : ¬ Disjoint b.made.toFinset e.taken.toFinset) :
    provDirect [(a, p), (b, q)] e = {1} := by
  ext i
  rw [mem_provDirect, Finset.mem_singleton]
  constructor
  · rintro ⟨lt, x, get, overlap⟩
    simp only [List.length_cons, List.length_nil] at lt
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at get
      subst get
      exact absurd first overlap
    · rfl
  · rintro rfl
    exact ⟨by simp, (b, q), rfl, second⟩

end Direct

/-! ## Provenance is strictly finer than history-preserving identity -/

section Witness

open HistoryControls

/-- `⟨(R₀, ∅)⟩⟨(R₁, {0})⟩⟨(R₂, {0, 1})⟩⊤`: the third firing takes from the first and the second. -/
def provenance : Formula PEmpty.{1} (RuleInstance T × Finset ℕ) :=
  .dia ((e₀ (S := S) τ).rule, ∅) (.dia ((e₁ (S := S) τ).rule, {0}) (.dia ((e₂ (S := S) τ).rule, {0, 1}) .top))

theorem provenance_holds_C₀ :
    (provSystem A (label τ) (offers (S := S) τ)).sat (provenance (S := S) τ) (C₀, []) := by
  refine ⟨_, ⟨e₀ τ, ⟨mem_e₀ τ, rfl⟩, (valid_iff τ A (mem_e₀ τ) reflexive_nil).mpr (of_decide_eq_true rfl),
    (provDirect_nil _).symm, rfl⟩, ?_⟩
  refine ⟨_, ⟨e₁ τ, ⟨mem_e₁ τ, rfl⟩, ?_,
    (provDirect_one _ _ _ (of_decide_eq_false rfl)).symm, rfl⟩, ?_⟩
  · show (e₁ (S := S) τ).Valid A (label τ) ((e₀ (S := S) τ).result (label τ) C₀)
    rw [result_e₀]
    exact (valid_iff τ A (mem_e₁ τ) (reflexive_E τ 1)).mpr (of_decide_eq_true rfl)
  refine ⟨_, ⟨e₂ τ, ⟨mem_e₂ τ, rfl⟩, ?_,
    (provDirect_both _ _ _ _ _ (of_decide_eq_false rfl) (of_decide_eq_false rfl)).symm, rfl⟩, trivial⟩
  show (e₂ (S := S) τ).Valid A (label τ)
    ((e₁ (S := S) τ).result (label τ) ((e₀ (S := S) τ).result (label τ) C₀))
  rw [result_e₀, result_e₁]
  exact (valid_iff τ A (mem_e₂ τ) (reflexive_E τ 2)).mpr (of_decide_eq_true rfl)

theorem provenance_fails_D₀ :
    ¬ (provSystem A (label τ) (offers (S := S) τ)).sat (provenance (S := S) τ) (D₀, []) := by
  rintro ⟨_, ⟨f, ⟨member, -⟩, valid, -, rfl⟩, _, ⟨g, ⟨memberG, -⟩, validG, -, rfl⟩, _,
    ⟨h, ⟨memberH, -⟩, validH, labelled, rfl⟩, -⟩
  obtain rfl := at_D₀ member valid
  have validG' : g.Valid A (label τ) (D₁ τ) := by
    have := validG
    rwa [result_d₀] at this
  obtain rfl := at_D₁ memberG validG'
  have validH' : h.Valid A (label τ) (D₂ τ) := by
    have := validH
    rwa [result_d₀, result_d₁] at this
  obtain rfl := at_D₂ memberH validH'
  have only := labelled.trans (provDirect_second (Entry.ofFiring (d₀ (S := S) τ))
    (Entry.ofFiring (d₁ (S := S) τ)) _ _ (Entry.ofFiring (d₂ (S := S) τ))
    (of_decide_eq_true rfl) (of_decide_eq_false rfl))
  exact absurd only (of_decide_eq_false rfl)

/-- **`C₀` and `D₀` are not provenance bisimilar.** -/
theorem not_provenanceBisimilar : ¬ ProvenanceBisimilar A (label τ) (offers (S := S) τ) C₀ D₀ :=
  fun bisimilar => provenance_fails_D₀ τ A
    (((provSystem A (label τ) (offers (S := S) τ)).logicallyEquivalent_of_bisimilar bisimilar
      (provenance (S := S) τ)).mp (provenance_holds_C₀ τ A))

/-- **Provenance bisimilarity is strictly finer than history-preserving bisimilarity**: on pure
programs from reuse-free starts it implies it, and `C₀`, `D₀` are history-preserving and record
bisimilar without being provenance bisimilar. -/
theorem provenance_strictly_finer :
    (∀ C D : Configuration T Site, ReuseFree A (label τ) (offers (S := S) τ) C →
      ReuseFree A (label τ) (offers (S := S) τ) D →
      ProvenanceBisimilar A (label τ) (offers (S := S) τ) C D →
        HPBisimilar A (label τ) (offers (S := S) τ) C D) ∧
      HPBisimilar A (label τ) (offers (S := S) τ) C₀ D₀ ∧
      RecordBisimilar A (label τ) (offers (S := S) τ) C₀ D₀ ∧
      ¬ ProvenanceBisimilar A (label τ) (offers (S := S) τ) C₀ D₀ :=
  ⟨fun _ _ reuseC reuseD => hpBisimilar_of_provenanceBisimilar (pureProgram τ) reuseC reuseD,
    hpBisimilar τ A, recordBisimilar τ A, not_provenanceBisimilar τ A⟩

theorem unique_alphabet : ∀ ℓ ℓ' (f g : Firing T S Site), offers τ ℓ f → offers τ ℓ' g →
    ∀ o ∈ f.selection.made, o ∈ g.selection.made → f = g := by
  rintro ℓ ℓ' f g ⟨mf, -⟩ ⟨mg, -⟩ o inF inG
  simp only [alphabet, List.mem_cons, List.not_mem_nil, or_false] at mf mg
  rcases mf with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases mg with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | rfl | (exfalso; revert inF inG; revert o; exact of_decide_eq_true rfl)

theorem takes_alphabet : ∀ ℓ (f : Firing T S Site), offers τ ℓ f →
    f.selection.made ≠ [] → f.selection.taken ≠ [] := by
  rintro ℓ f ⟨member, -⟩ -
  simp only [alphabet, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> exact of_decide_eq_true rfl

/-- **`C₀` is a single-assignment start.** -/
theorem singleAssignment_C₀ : SingleAssignment (offers (S := S) τ) C₀ := by
  refine ⟨?_, unique_alphabet τ, takes_alphabet τ⟩
  rintro ℓ f ⟨member, -⟩
  simp only [alphabet, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> exact of_decide_eq_true rfl

/-- **`D₀` is a single-assignment start.** -/
theorem singleAssignment_D₀ : SingleAssignment (offers (S := S) τ) D₀ := by
  refine ⟨?_, unique_alphabet τ, takes_alphabet τ⟩
  rintro ℓ f ⟨member, -⟩
  simp only [alphabet, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> exact of_decide_eq_true rfl

/-- **Reuse-freedom of `C₀` and `D₀` from the static criterion.** -/
theorem reuseFree_of_criterion :
    ReuseFree A (label τ) (offers (S := S) τ) C₀ ∧ ReuseFree A (label τ) (offers (S := S) τ) D₀ :=
  ⟨reuseFree_of_singleAssignment (singleAssignment_C₀ τ),
    reuseFree_of_singleAssignment (singleAssignment_D₀ τ)⟩

end Witness

/-! ## Each condition of single assignment is needed -/

-- Something made is present at the start.
namespace Remade

open HistoryControls.Reuse

/-- **R71's reuse control has unique makers that take something, and makes what is present.** -/
theorem violates :
    (∀ ℓ ℓ' (f g : Firing T S Site), offers τ ℓ f → offers τ ℓ' g →
        ∀ o ∈ f.selection.made, o ∈ g.selection.made → f = g) ∧
      (∀ ℓ (f : Firing T S Site), offers τ ℓ f → f.selection.made ≠ [] → f.selection.taken ≠ []) ∧
      ¬ (∀ ℓ (f : Firing T S Site), offers τ ℓ f → ∀ o ∈ f.selection.made,
        o ∉ (⟨[], {.a}⟩ : Configuration T Site).present) ∧
      ¬ ReuseFree A (label τ) (offers (S := S) τ) ⟨[], {.a}⟩ := by
  refine ⟨?_, ?_, ?_, HistoryControls.Reuse.reuse_control τ A⟩
  · rintro ℓ ℓ' f g ⟨mf, -⟩ ⟨mg, -⟩ o inF inG
    rcases mf with rfl | rfl <;> rcases mg with rfl | rfl <;> first | rfl | simp_all [t, u]
  · rintro ℓ f ⟨mf, -⟩ -
    rcases mf with rfl | rfl <;> exact of_decide_eq_true rfl
  · intro unmade
    exact unmade _ (u τ) ⟨.inr rfl, rfl⟩ .a (by simp [u]) (by simp)

end Remade

-- Two makers of one identity.
namespace TwoMakers

inductive Site
  | t₁ | t₂ | o
  deriving DecidableEq

def label : Site → T := fun _ => τ

def m₁ : Firing T S Site := ⟨⟨[τ], [], [], [], [τ]⟩, [], ⟨[.t₁], [], [.o]⟩⟩
def m₂ : Firing T S Site := ⟨⟨[τ], [], [], [], [τ]⟩, [], ⟨[.t₂], [], [.o]⟩⟩
def use : Firing T S Site := ⟨⟨[τ], [], [], [], []⟩, [], ⟨[.o], [], []⟩⟩

def offers (r : RuleInstance T) (f : Firing T S Site) : Prop :=
  (f = m₁ τ ∨ f = m₂ τ ∨ f = use τ) ∧ f.rule = r

def start : Configuration T Site := ⟨[], {.t₁, .t₂}⟩

theorem ground_m₁ : Ground (label τ) (m₁ (S := S) τ) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, of_decide_eq_true rfl, of_decide_eq_true rfl⟩
theorem ground_m₂ : Ground (label τ) (m₂ (S := S) τ) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, of_decide_eq_true rfl, of_decide_eq_true rfl⟩
theorem ground_use : Ground (label τ) (use (S := S) τ) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, of_decide_eq_true rfl, of_decide_eq_true rfl⟩

/-- **Two makers**: nothing made is present and every maker takes something, and the start is not
reuse-free. -/
theorem violates :
    (∀ ℓ (f : Firing T S Site), offers τ ℓ f → ∀ occ ∈ f.selection.made, occ ∉ (start (T := T)).present) ∧
      (∀ ℓ (f : Firing T S Site), offers τ ℓ f → f.selection.made ≠ [] → f.selection.taken ≠ []) ∧
      ¬ ReuseFree A (label τ) (offers (S := S) τ) start := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ℓ f ⟨mf, -⟩
    rcases mf with rfl | rfl | rfl <;> exact of_decide_eq_true rfl
  · rintro ℓ f ⟨mf, -⟩ -
    rcases mf with rfl | rfl | rfl <;> exact of_decide_eq_true rfl
  · intro reuse
    have v₁ : (m₁ (S := S) τ).Valid A (label τ) start :=
      ((ground_m₁ τ).valid_iff A reflexive_nil).mpr (of_decide_eq_true rfl)
    let x₁ : Configuration T Site × History T S Site :=
      ((m₁ (S := S) τ).result (label τ) start, [] ++ [(m₁ τ, past (label τ) [] (m₁ (S := S) τ))])
    have r₁ : HReach A (label τ) (offers (S := S) τ) start x₁ :=
      Relation.ReflTransGen.single
        ⟨((m₁ (S := S) τ).rule, past (label τ) [] (m₁ (S := S) τ)), m₁ τ, ⟨.inl rfl, rfl⟩, v₁, rfl, rfl⟩
    have refl₁ := (ground_m₁ (S := S) τ).reflexive_result (C := start) reflexive_nil
    have v₂ : (use (S := S) τ).Valid A (label τ) x₁.1 :=
      ((ground_use τ).valid_iff A refl₁).mpr (of_decide_eq_true rfl)
    let x₂ : Configuration T Site × History T S Site :=
      ((use (S := S) τ).result (label τ) x₁.1, x₁.2 ++ [(use τ, past (label τ) x₁.2 (use (S := S) τ))])
    have r₂ : HReach A (label τ) (offers (S := S) τ) start x₂ :=
      r₁.tail ⟨((use (S := S) τ).rule, past (label τ) x₁.2 (use (S := S) τ)), use τ,
        ⟨.inr (.inr rfl), rfl⟩, v₂, rfl, rfl⟩
    have refl₂ := (ground_use (S := S) τ).reflexive_result (C := x₁.1) refl₁
    have v₃ : (m₂ (S := S) τ).Valid A (label τ) x₂.1 :=
      ((ground_m₂ τ).valid_iff A refl₂).mpr (of_decide_eq_true rfl)
    exact reuse x₂ r₂ _ (m₂ τ) ⟨.inr (.inl rfl), rfl⟩ v₃ (use τ, past (label τ) x₁.2 (use (S := S) τ))
      (List.mem_append_right _ (List.mem_singleton_self _)) .o (by simp [m₂]) (by simp [use])

end TwoMakers

-- A maker that takes nothing.
namespace Spring

inductive Site
  | o
  deriving DecidableEq

def label : Site → T := fun _ => τ

def mk : Firing T S Site := ⟨⟨[], [], [], [], [τ]⟩, [], ⟨[], [], [.o]⟩⟩
def use : Firing T S Site := ⟨⟨[τ], [], [], [], []⟩, [], ⟨[.o], [], []⟩⟩

def offers (r : RuleInstance T) (f : Firing T S Site) : Prop := (f = mk τ ∨ f = use τ) ∧ f.rule = r

def start : Configuration T Site := ⟨[], ∅⟩

theorem ground_mk : Ground (label τ) (mk (S := S) τ) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, of_decide_eq_true rfl, of_decide_eq_true rfl⟩
theorem ground_use : Ground (label τ) (use (S := S) τ) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, of_decide_eq_true rfl, of_decide_eq_true rfl⟩

/-- **A maker that takes nothing**: nothing made is present and makers are unique, and the start is
not reuse-free. -/
theorem violates :
    (∀ ℓ (f : Firing T S Site), offers τ ℓ f → ∀ occ ∈ f.selection.made, occ ∉ (start (T := T)).present) ∧
      (∀ ℓ ℓ' (f g : Firing T S Site), offers τ ℓ f → offers τ ℓ' g →
        ∀ occ ∈ f.selection.made, occ ∈ g.selection.made → f = g) ∧
      ¬ ReuseFree A (label τ) (offers (S := S) τ) start := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ℓ f ⟨mf, -⟩
    rcases mf with rfl | rfl <;> exact of_decide_eq_true rfl
  · rintro ℓ ℓ' f g ⟨mf, -⟩ ⟨mg, -⟩ occ inF inG
    rcases mf with rfl | rfl <;> rcases mg with rfl | rfl <;> first | rfl | simp_all [mk, use]
  · intro reuse
    have v₁ : (mk (S := S) τ).Valid A (label τ) start :=
      ((ground_mk τ).valid_iff A reflexive_nil).mpr (of_decide_eq_true rfl)
    let x₁ : Configuration T Site × History T S Site :=
      ((mk (S := S) τ).result (label τ) start, [] ++ [(mk τ, past (label τ) [] (mk (S := S) τ))])
    have r₁ : HReach A (label τ) (offers (S := S) τ) start x₁ :=
      Relation.ReflTransGen.single
        ⟨((mk (S := S) τ).rule, past (label τ) [] (mk (S := S) τ)), mk τ, ⟨.inl rfl, rfl⟩, v₁, rfl, rfl⟩
    have refl₁ := (ground_mk (S := S) τ).reflexive_result (C := start) reflexive_nil
    have v₂ : (use (S := S) τ).Valid A (label τ) x₁.1 :=
      ((ground_use τ).valid_iff A refl₁).mpr (of_decide_eq_true rfl)
    let x₂ : Configuration T Site × History T S Site :=
      ((use (S := S) τ).result (label τ) x₁.1, x₁.2 ++ [(use τ, past (label τ) x₁.2 (use (S := S) τ))])
    have r₂ : HReach A (label τ) (offers (S := S) τ) start x₂ :=
      r₁.tail ⟨((use (S := S) τ).rule, past (label τ) x₁.2 (use (S := S) τ)), use τ,
        ⟨.inr rfl, rfl⟩, v₂, rfl, rfl⟩
    have refl₂ := (ground_use (S := S) τ).reflexive_result (C := x₁.1) refl₁
    have v₃ : (mk (S := S) τ).Valid A (label τ) x₂.1 :=
      ((ground_mk τ).valid_iff A refl₂).mpr (of_decide_eq_true rfl)
    exact reuse x₂ r₂ _ (mk τ) ⟨.inl rfl, rfl⟩ v₃ (use τ, past (label τ) x₁.2 (use (S := S) τ))
      (List.mem_append_right _ (List.mem_singleton_self _)) .o (by simp [mk]) (by simp [use])

end Spring

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.ProvenanceControls

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.ProvenanceControls in
#print axioms provenance_holds_C₀
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.ProvenanceControls in
#print axioms provenance_fails_D₀
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.ProvenanceControls in
#print axioms provenance_strictly_finer
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.ProvenanceControls in
#print axioms reuseFree_of_criterion
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.ProvenanceControls in
#print axioms Remade.violates
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.ProvenanceControls in
#print axioms TwoMakers.violates
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.ProvenanceControls in
#print axioms Spring.violates
