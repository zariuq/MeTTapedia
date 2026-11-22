import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Step
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.SourceControls

/-!
# Small programs for the step

Over the syntactic controls of the source layer (values `Tm Sig`, patterns `Pat ℕ Sig`, no
declared law):

* **A served request** (`serve`): take `(redex $x)`, check that no `lock` is present, produce
  `(out $x)`. It steps `{(redex a), tok}` to `{(out a), tok}` (`serve_steps`) and is blocked at
  `{(redex a), lock}` (`serve_blocked`).
* **Two reads of one value** (`twoReads`): read `tok` twice, produce `out`. At a store with one
  `tok` the compiled transform fires with both reads on the same occurrence (`shared_read_fires`),
  and the step reads the one `tok` twice, counting it once (`shared_read_steps`). Reading consumes
  nothing, so a value read twice is a value read once; Datalog's `path(x, z) :- edge(x, y),
  edge(y, z)` over the loop `edge(a, a)` needs exactly this.
* **A take and a read never share** (`takeRead`): take `tok` and read `tok` makes no step at one
  `tok` (`take_read_no_share`), as the compiled transform refuses it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Examples

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources.Commutative
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources.Controls

/-- In the syntactic layer a constant pattern covers exactly that constant. -/
theorem covers_leaf_iff {σ : Subst ℕ (Tm Sig)} {s : Sig} {t : Tm Sig} :
    Ls.Covers σ (.leaf s) t ↔ t = k s := by
  constructor
  · rintro ⟨τ, step⟩
    obtain ⟨u, hu, e⟩ := step.solves
    have hu' : u = k s := by
      simp only [Ls, termLayer, Pat.inst] at hu
      exact (Option.some.inj hu).symm
    subst hu'
    exact ((syntactic_E_iff (V := ℕ)).mp e).symm
  · rintro rfl
    exact ⟨σ, ⟨Extends.refl σ, fun _ _ => rfl, ⟨k s, rfl, (syntactic_E_iff (V := ℕ)).mpr rfl⟩⟩⟩

/-! ## A served request -/

/-- `(redex $0)`. -/
def pRedex : Pat ℕ Sig := .node .redex (.var 0) (.leaf .nil)

/-- `(out $0)`. -/
def pOut : Pat ℕ Sig := .node .out (.var 0) (.leaf .nil)

/-- Take a request, check that no lock is present, produce the answer. -/
def serve : Rule ℕ (Tm Sig) (Pat ℕ Sig) :=
  ⟨[pRedex], [], [Check.absent (.leaf .lock)], [pOut]⟩

/-- The substitution `$0 ↦ a`. -/
def σa : Subst ℕ (Tm Sig) := Function.update empty 0 (some (k .a))

/-- **Positive: the request is served** when no lock is present. -/
theorem serve_steps :
    Step Ls serve {un .redex (k .a), k .tok} {un .out (k .a), k .tok} := by
  refine ⟨σa, {k .tok}, {un .redex (k .a)}, 0, [un .out (k .a)], ?_, ?_, ⟨[], .nil, by simp, by simp⟩,
    ?_, ?_, ?_, ?_⟩
  · intro v notIn
    by_cases hv : v = 0
    · subst hv
      exact absurd (by simp [pRedex, Ls, termLayer, Pat.vars]) (notIn pRedex (by simp [serve]))
    · simp [σa, Function.update, hv, empty]
  · refine ⟨[un .redex (k .a)], .cons ⟨un .redex (k .a), rfl, ?_⟩ .nil, rfl⟩
    exact (syntactic_E_iff (V := ℕ)).mpr rfl
  · decide
  · intro c mem
    simp only [serve, List.mem_singleton] at mem
    subst mem
    show matchesIn Ls σa (.leaf .lock) {un .redex (k .a), k .tok} = 0
    simp only [matchesIn, Multiset.filter_eq_nil, semRegion_eq_true]
    intro t mem covers
    rw [covers_leaf_iff] at covers
    subst covers
    revert mem
    decide
  · rfl
  · decide

/-- **Negative: the request is not served while a lock is present.** -/
theorem serve_blocked (M' : Multiset (Tm Sig)) :
    ¬ Step Ls serve {un .redex (k .a), k .lock} M' := by
  rintro ⟨σ, S, taken, kept, made, -, -, -, -, holds, -⟩
  have h := holds (Check.absent (.leaf .lock)) (by simp [serve])
  change matchesIn Ls σ (.leaf .lock) {un .redex (k .a), k .lock} = 0 at h
  have mem : k .lock ∈ matchesIn Ls σ (.leaf .lock) {un .redex (k .a), k .lock} :=
    mem_matchesIn.mpr ⟨by simp, covers_leaf_iff.mpr rfl⟩
  rw [h] at mem
  exact Multiset.notMem_zero _ mem

/-! ## Two reads of one value -/

/-- Read `tok` twice, produce `out`. -/
def twoReads : Rule ℕ (Tm Sig) (Pat ℕ Sig) := ⟨[], [.leaf .tok, .leaf .tok], [], [.leaf .out]⟩

/-- **The compiled transform fires at one `tok`**: both reads keep the same occurrence. -/
theorem shared_read_fires :
    ∃ c, Fires Ls ms lbl oneTok (twoReads.transform []) c ∧ c.kept.card = 1 := by
  obtain ⟨x, member, linear, card⟩ : ∃ x ∈ (twoReads.transform []).rows Ls ms lbl oneTok,
      (footprintOf x.2).Linear ∧ (footprintOf x.2).keeps.toFinset.card = 1 := by
    apply exists_of_not_forall
    decide +kernel
  obtain ⟨c, commit⟩ := exists_isCommitOf (S := oneTok) supply (footprintOf x.2)
  exact ⟨c, ⟨x, member, linear, commit⟩, by rw [commit.kept]; exact card⟩

/-- `tok` solves the pattern `tok` under the empty substitution. -/
theorem solves_tok : Ls.Solves empty (.leaf .tok) (k .tok) :=
  ⟨k .tok, rfl, (syntactic_E_iff (V := ℕ)).mpr rfl⟩

/-- **Positive: two reads of one value step.** At one `tok`, both read patterns read it; it is
counted once, and the step makes `out`. This is Datalog's self-join over a loop edge. -/
theorem shared_read_steps : Step Ls twoReads (labels lbl oneTok) {k .tok, k .out} := by
  refine ⟨empty, 0, 0, {k .tok}, [k .out], fun v _ => rfl, ⟨[], .nil, rfl⟩,
    ⟨[k .tok, k .tok], .cons solves_tok (.cons solves_tok .nil), by decide, by simp⟩,
    by decide, fun c mem => by simp [twoReads] at mem, rfl, by decide⟩

/-- Take `tok` and read `tok`, produce `out`. -/
def takeRead : Rule ℕ (Tm Sig) (Pat ℕ Sig) := ⟨[.leaf .tok], [.leaf .tok], [], [.leaf .out]⟩

/-- **Negative: a take and a read never share a value.** At one `tok` the rule that takes `tok`
and reads `tok` makes no step: the read needs a copy apart from the one taken. The compiled
transform refuses it too (`Sources.Controls.readTake_one_refused`). -/
theorem take_read_no_share (M' : Multiset (Tm Sig)) :
    ¬ Step Ls takeRead (labels lbl oneTok) M' := by
  rintro ⟨σ, S, _, kept, made, -, ⟨ts₁, sol₁, rfl⟩, ⟨ts₂, sol₂, -, support⟩, hM, -⟩
  have one : ts₁.length = 1 := by simpa [takeRead] using sol₁.length_eq.symm
  have nonempty : 0 < Multiset.card kept := by
    match ts₂, sol₂, support with
    | u :: _, .cons _ _, support =>
        exact Multiset.card_pos_iff_exists_mem.mpr ⟨u, support u (by simp)⟩
  have card := congrArg Multiset.card hM
  rw [show Multiset.card (labels lbl oneTok) = 1 by decide, Multiset.card_add, Multiset.card_add,
    Multiset.coe_card, one] at card
  omega

end Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Examples
