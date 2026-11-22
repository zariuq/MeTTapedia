import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Equivalence.Gaps

/-!
# Rights on labels, restriction, and the garbage law

Every label lives at a name and carries names (`Naming`): the name it lives at, the names in its
payload, and, for a process, the names it holds. A rule is **owned** by one label of its redex and
**scoped** to that owner's names (`OwnedBy`): what it takes or keeps lives at names the owner
carries, and the region of each of its predicate queries lies there. It **forges** no name
(`NoForge`): what it makes carries only names its redex carries. A process that receives a name in a
message carries it afterwards, because the message is in the redex; so scope extrusion is allowed,
and forging is not. Rules that allocate fresh names are outside this class (see the report's
remaining steps).

## Rights on labels

* **A step borrows and closes only within its owner's rights** (`Rule.Step.within_rights`): the
  borrowed context lives at names the owner carries, and so does every region the label closes.
  A process may only borrow at regions it holds.

## Restriction and region-scoped contexts

* `ν n` is the admissible class of labels that do not mention `n` (`nuAdm`): no environment can
  supply a label at `n` or carrying `n`. Contexts scoped to a set of rights are the class of labels
  that carry only held names (`heldAdm`).
* **Congruence for both** is `Bisimilar.restrict` and `Bisimilar.add_context` of `Bisimulation`:
  bisimilar programs stay bisimilar under `ν n` (`Bisimilar.nu`) and beside every context scoped
  to the rights (`Bisimilar.beside_scoped`). In this representation `ν` is a property of the
  environment, not a term former, so scope extension, `ν n (P | C) = (ν n P) | C` for `C` without
  `n`, is an identity of representations; its content is that composing with a context without `n`
  preserves the restricted equivalence, which `Bisimilar.add_context` proves.

## The garbage law

* **Garbage at a restricted name is invisible** (`garbage`): for scoped, non-forging rules, a
  bag `G` of labels living at `n` that no rule can fire with help that does not mention `n`
  (`Stuck`), and barbs blind to `G`, every bag without `n` is bisimilar under `ν n` to itself
  beside `G`. Every step on either side is the same step on the other: an owner without `n` reaches
  no label at `n`, and nothing it makes carries `n`.
* **A wildcard reader sees through restriction** (`Controls.wildcard_sees_garbage`). A reader that
  closes the region of all messages, whatever their name, is not scoped; with it, one message at a
  restricted name separates `ν n (message)` from `ν n 0`, while the scoped reader of its own name
  cannot tell them apart. So the garbage law, and with it the use of `ν` as hiding, needs scoped
  rules; congruence for `ν` itself holds for every rule set.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Equivalence

universe u v w

variable {R : Type u} [DecidableEq R] {N : Type w}

/-- Names of labels: where a label lives, and the names it carries (the name it lives at among
them). -/
structure Naming (R : Type u) (N : Type w) where
  loc : R → N
  mentions : R → N → Prop
  loc_mentioned : ∀ x, mentions x (loc x)

variable (nm : Naming R N)

/-- **A rule owned by a label of its redex**, scoped to the names the owner carries. -/
structure OwnedBy (ρ : Rule R) (o : R) : Prop where
  mem : o ∈ ρ.redex
  uses : ∀ x ∈ ρ.redex, nm.mentions o (nm.loc x)
  closed : ∀ x, ρ.closed x = true → nm.mentions o (nm.loc x)

/-- A rule forges no name: what it makes carries only names its redex carries. -/
def NoForge (ρ : Rule R) : Prop := ∀ x ∈ ρ.make, ∀ n, nm.mentions x n → ∃ y ∈ ρ.redex, nm.mentions y n

/-- Scoped rules: each has an owner and forges no name. -/
def ScopedRules (Γ : Rule R → Prop) : Prop := ∀ ρ, Γ ρ → (∃ o, OwnedBy nm ρ o) ∧ NoForge nm ρ

/-- A bag that does not mention `n`. -/
def FreshFor (n : N) (M : Multiset R) : Prop := ∀ x ∈ M, ¬ nm.mentions x n

/-- **Restriction**: the admissible labels that do not mention `n`. -/
def nuAdm (n : N) (Adm : R → Prop) : R → Prop := fun x => Adm x ∧ ¬ nm.mentions x n

/-- **Region-scoped contexts**: labels that carry only held names. -/
def heldAdm (held : N → Prop) : R → Prop := fun x => ∀ n, nm.mentions x n → held n

variable {nm}

/-! ## Rights on labels -/

/-- **A step borrows and closes only within its owner's rights.** -/
theorem Rule.Step.within_rights {ρ : Rule R} {o : R} (owned : OwnedBy nm ρ o) {M M' J : Multiset R}
    {F : R → Bool} (step : ρ.Step M ⟨J, F⟩ M') :
    (∀ x ∈ J, nm.mentions o (nm.loc x)) ∧ (∀ x, F x = true → nm.mentions o (nm.loc x)) := by
  obtain ⟨hJ, hF, -, -⟩ := step
  simp only at hJ hF
  subst hJ hF
  exact ⟨fun x member => owned.uses x (Multiset.mem_of_le (Multiset.sub_le_self _ _) member),
    owned.closed⟩

/-! ## Congruence for restriction and scoped contexts -/

section Congruence

variable {Γ : Rule R → Prop} {Adm : R → Prop} {ι : Type v} {obs : ι → R → Prop}

/-- **Congruence for `ν`.** -/
theorem Bisimilar.nu {M M' : Multiset R} (h : Bisimilar Γ Adm obs M M') (n : N) :
    Bisimilar Γ (nuAdm nm n Adm) obs M M' :=
  h.restrict (fun _ h => h.1) id

/-- **Congruence for region-scoped contexts.** Bisimilar under the scoped class, bisimilar beside
every context scoped to the rights. -/
theorem Bisimilar.beside_scoped {held : N → Prop} {M M' : Multiset R}
    (h : Bisimilar Γ (heldAdm nm held) obs M M') {C : Multiset R}
    (inScope : ∀ x ∈ C, ∀ n, nm.mentions x n → held n) :
    Bisimilar Γ (heldAdm nm held) obs (M + C) (M' + C) :=
  h.add_context inScope

/-- **Restriction commutes with composition beside contexts without the name** (the content of
scope extension). -/
theorem Bisimilar.nu_beside {n : N} {M M' : Multiset R} (h : Bisimilar Γ (nuAdm nm n Adm) obs M M')
    {C : Multiset R} (adm : Admissible Adm C) (fresh : FreshFor nm n C) :
    Bisimilar Γ (nuAdm nm n Adm) obs (M + C) (M' + C) :=
  h.add_context fun x member => ⟨adm x member, fresh x member⟩

end Congruence

/-! ## The garbage law -/

section Garbage

variable {Γ : Rule R → Prop} {Adm : R → Prop} {ι : Type v} {obs : ι → R → Prop}

variable (nm) in
/-- `G` is stuck at `n`: a rule that fires with `G` and help not mentioning `n` uses nothing of `G`. -/
def Stuck (Γ : Rule R → Prop) (n : N) (G : Multiset R) : Prop :=
  ∀ ρ, Γ ρ → ∀ Z, FreshFor nm n Z → ρ.redex ≤ G + Z → ∀ x ∈ ρ.redex, x ∉ G

omit [DecidableEq R] in
theorem FreshFor.mono {n : N} {A B : Multiset R} (sub : A ≤ B) (fresh : FreshFor nm n B) :
    FreshFor nm n A := fun x member => fresh x (Multiset.mem_of_le sub member)

omit [DecidableEq R] in
theorem freshFor_add {n : N} {A B : Multiset R} :
    FreshFor nm n (A + B) ↔ FreshFor nm n A ∧ FreshFor nm n B := by
  simp only [FreshFor, Multiset.mem_add]
  exact ⟨fun h => ⟨fun x m => h x (Or.inl m), fun x m => h x (Or.inr m)⟩,
    fun h x m => m.elim (h.1 x) (h.2 x)⟩

/-- What a scoped, non-forging rule makes from a bag without `n` is a bag without `n`. -/
theorem fresh_result {ρ : Rule R} (noForge : NoForge nm ρ) {n : N} {W : Multiset R}
    (sub : ρ.redex ≤ W) (fresh : FreshFor nm n W) : FreshFor nm n (ρ.result W) := by
  intro x member mentions
  rcases Multiset.mem_add.mp member with old | made
  · exact fresh x (Multiset.mem_of_le (Multiset.sub_le_self _ _) old) mentions
  · obtain ⟨y, inRedex, mentionsY⟩ := noForge x made n mentions
    exact fresh y (Multiset.mem_of_le sub inRedex) mentionsY

/-- A bag disjoint from `G` that fits in `G + W` fits in `W`. -/
theorem le_of_le_add_disjoint {l G W : Multiset R} (sub : l ≤ G + W) (apart : ∀ x ∈ l, x ∉ G) :
    l ≤ W := by
  rw [Multiset.le_iff_count] at sub ⊢
  intro x
  by_cases inL : x ∈ l
  · have := sub x
    rw [Multiset.count_add, Multiset.count_eq_zero.mpr (apart x inL), zero_add] at this
    exact this
  · rw [Multiset.count_eq_zero.mpr inL]; exact Nat.zero_le _

/-- The label of a step at a bag beside `G`, when the rule uses nothing of `G`. -/
theorem label_beside {l G Z : Multiset R} (apart : ∀ x ∈ l, x ∉ G) : l - (Z + G) = l - Z := by
  ext x
  by_cases inL : x ∈ l
  · simp only [Multiset.count_sub, Multiset.count_add, Multiset.count_eq_zero.mpr (apart x inL),
      add_zero]
  · simp only [Multiset.count_sub, Multiset.count_add, Multiset.count_eq_zero.mpr inL, zero_tsub]

omit [DecidableEq R] in
/-- A region closed by an owner without `n` holds nothing living at `n`. -/
theorem garbage_avoids_closed {ρ : Rule R} {o : R} (owned : OwnedBy nm ρ o) {n : N}
    (ownerFresh : ¬ nm.mentions o n) {G : Multiset R} (atN : ∀ g ∈ G, nm.loc g = n) :
    Avoids G ρ.closed := by
  intro g member
  cases hc : ρ.closed g
  · rfl
  · exact absurd (atN g member ▸ owned.closed g hc) ownerFresh

/-- **The garbage law.** Under `ν n`, for scoped rules, a stuck bag `G` living at `n` and invisible
to the barbs changes nothing: every bag without `n` is bisimilar to itself beside `G`. -/
theorem garbage (scopedΓ : ScopedRules nm Γ) {n : N} {G : Multiset R}
    (atN : ∀ g ∈ G, nm.loc g = n) (stuck : Stuck nm Γ n G) (blind : ∀ i, ∀ g ∈ G, ¬ obs i g)
    {M : Multiset R} (fresh : FreshFor nm n M) :
    Bisimilar Γ (nuAdm nm n Adm) obs (M + G) M := by
  let B : Multiset R → Multiset R → Prop := fun X Y =>
    (∃ Z, FreshFor nm n Z ∧ X = Z + G ∧ Y = Z) ∨ (∃ Z, FreshFor nm n Z ∧ X = Z ∧ Y = Z + G)
  have barbBeside : ∀ (Z : Multiset R) i, Barb (obs i) (Z + G) → Barb (obs i) Z := by
    intro Z i shows
    rcases barb_add.mp shows with h | ⟨g, member, h⟩
    · exact h
    · exact absurd h (blind i g member)
  refine ⟨B, ⟨?_, ?_, ?_⟩, Or.inl ⟨M, fresh, rfl, rfl⟩⟩
  · rintro X Y (⟨Z, fz, hX, hY⟩ | ⟨Z, fz, hX, hY⟩) <;> subst X Y
    · exact Or.inr ⟨Z, fz, rfl, rfl⟩
    · exact Or.inl ⟨Z, fz, rfl, rfl⟩
  · rintro X Y (⟨Z, fz, hX, hY⟩ | ⟨Z, fz, hX, hY⟩) i shows <;> subst X Y
    · exact barbBeside Z i shows
    · exact barb_add.mpr (Or.inl shows)
  · rintro X Y (⟨Z, fz, hX, hY⟩ | ⟨Z, fz, hX, hY⟩) J F X' adm ⟨ρ, member, step⟩ <;> subst X Y
    · -- a step beside the garbage is the same step without it
      obtain ⟨⟨o, owned⟩, noForge⟩ := scopedΓ ρ member
      have freshJ : FreshFor nm n J := fun x m => (adm x m).2
      obtain ⟨hJ, hF, avoids, hX⟩ := step
      simp only at hJ hF hX
      have sub : ρ.redex ≤ G + (Z + J) := by
        have := le_add_label' (Z + G) ρ.redex
        rw [← hJ] at this
        calc ρ.redex ≤ Z + G + J := this
          _ = G + (Z + J) := by abel
      have apart := stuck ρ member (Z + J) (freshFor_add.mpr ⟨fz, freshJ⟩) sub
      have subZJ : ρ.redex ≤ Z + J := le_of_le_add_disjoint sub apart
      have ownerFresh : ¬ nm.mentions o n :=
        (freshFor_add.mpr ⟨fz, freshJ⟩) o (Multiset.mem_of_le subZJ owned.mem)
      have hJ' : J = ρ.redex - Z := by rw [hJ, label_beside apart]
      have frameZ : Avoids (Z - ρ.redex) ρ.closed := by
        have eq : Z + G - ρ.redex = (Z - ρ.redex) + G := by
          ext x
          by_cases inL : x ∈ ρ.redex
          · simp only [Multiset.count_sub, Multiset.count_add,
              Multiset.count_eq_zero.mpr (apart x inL), add_zero]
          · simp only [Multiset.count_sub, Multiset.count_add, Multiset.count_eq_zero.mpr inL,
              tsub_zero]
        rw [eq] at avoids
        exact (avoids_add.mp avoids).1
      have stepZ : ρ.Step Z ⟨J, F⟩ (ρ.result (Z + J)) := ⟨hJ', hF, frameZ, rfl⟩
      have resultEq : X' = ρ.result (Z + J) + G := by
        rw [hX]
        unfold Rule.result
        have : Z + G + J = Z + J + G := by abel
        rw [this, result_add_frame (ρ.take_le_redex.trans subZJ)]
      have bstepZ : BStep Γ Z ⟨J, F⟩ (ρ.result (Z + J)) := ⟨ρ, member, stepZ⟩
      refine ⟨F, ρ.result (Z + J), Weaker.refl _ _, bstepZ.absorb,
        Or.inl ⟨_, fresh_result noForge subZJ (freshFor_add.mpr ⟨fz, freshJ⟩), resultEq, rfl⟩⟩
    · -- a step without the garbage is the same step beside it
      obtain ⟨⟨o, owned⟩, noForge⟩ := scopedΓ ρ member
      have freshJ : FreshFor nm n J := fun x m => (adm x m).2
      have bstep : BStep Γ Z ⟨J, F⟩ X' := ⟨ρ, member, step⟩
      obtain ⟨hJ, hF, -, hX⟩ := step
      simp only at hJ hF hX
      have subZJ : ρ.redex ≤ Z + J := by rw [hJ]; exact le_add_label' Z ρ.redex
      have ownerFresh : ¬ nm.mentions o n :=
        (freshFor_add.mpr ⟨fz, freshJ⟩) o (Multiset.mem_of_le subZJ owned.mem)
      have avoidsG : Avoids G F := by
        rw [hF]; exact garbage_avoids_closed owned ownerFresh atN
      have lifted := bstep.absorb.lift_zero avoidsG
      have : Z + J + G = Z + G + J := by abel
      rw [this] at lifted
      refine ⟨F, X' + G, Weaker.refl _ _, lifted, Or.inr ⟨X', ?_, rfl, rfl⟩⟩
      rw [hX]
      exact fresh_result noForge subZJ (freshFor_add.mpr ⟨fz, freshJ⟩)

end Garbage

/-! ## Controls -/

namespace Controls

/-- Labels: a scoped reader `S` and a wildcard reader `W` holding name `0`, a message `g` at name
`1`, and an output. -/
inductive NAtom where
  | S
  | W
  | g
  | done
  deriving DecidableEq, Repr

open NAtom

/-- Each label carries exactly the name it lives at. -/
def naming : Naming NAtom ℕ where
  loc
    | g => 1
    | _ => 0
  mentions x n := n = (match x with | g => 1 | _ => 0)
  loc_mentioned x := by cases x <;> rfl

/-- Messages at name `0`. -/
def messagesAtZero : NAtom → Bool := fun _ => false

/-- Messages at any name. -/
def anyMessage : NAtom → Bool
  | g => true
  | _ => false

/-- The scoped reader: fires when no message is at its own name `0`. -/
def scopedRead : Rule NAtom := ⟨{S}, 0, {done}, messagesAtZero⟩

/-- The wildcard reader: fires when no message is anywhere. -/
def wildRead : Rule NAtom := ⟨{W}, 0, {done}, anyMessage⟩

def scopedRules : Rule NAtom → Prop := fun ρ => ρ = scopedRead

def wildRules : Rule NAtom → Prop := fun ρ => ρ = wildRead

/-- The barb: the output. -/
def showsDone : Unit → NAtom → Prop := fun _ y => y = done

theorem scopedRules_scoped : ScopedRules naming scopedRules := by
  rintro ρ rfl
  refine ⟨⟨S, ⟨by decide, ?_, ?_⟩⟩, ?_⟩
  · intro x member
    simp [scopedRead, Rule.redex] at member
    subst member; rfl
  · intro x h; simp [scopedRead, messagesAtZero] at h
  · intro x member n mentions
    simp [scopedRead] at member
    subst member
    exact ⟨S, by decide, mentions⟩

/-- The wildcard reader is not scoped: it closes the region of a message at a name its owner does
not carry. -/
theorem wildRules_not_scoped : ¬ ScopedRules naming wildRules := by
  intro hScoped
  obtain ⟨⟨o, owned⟩, -⟩ := hScoped wildRead rfl
  have mem := owned.mem
  simp [wildRead, Rule.redex] at mem
  subst mem
  have := owned.closed g rfl
  simp [naming] at this

/-- **The garbage law, and a wildcard reader that breaks it.** Under `ν 1`, the message `g` is
invisible to the scoped rules: `{g}` and `0` are bisimilar. With the wildcard reader they are not
even contextually equivalent: beside the reader, `0` lets it fire and `{g}` does not. -/
theorem wildcard_sees_garbage :
    Bisimilar scopedRules (nuAdm naming 1 fun _ => True) showsDone ({g} : Multiset NAtom) 0 ∧
      ¬ Contextual wildRules (nuAdm naming 1 fun _ => True) showsDone ({g} : Multiset NAtom) 0 := by
  refine ⟨?_, ?_⟩
  · have := garbage (Γ := scopedRules) (Adm := fun _ => True) (obs := showsDone) (nm := naming)
      scopedRules_scoped (n := 1) (G := {g})
      (by intro x member; simp at member; subst member; rfl)
      (by
        rintro ρ rfl Z _ _ x member
        simp [scopedRead, Rule.redex] at member
        subst member; decide)
      (by intro i x member; simp at member; subst member; simp [showsDone])
      (M := 0) (by intro x member; simp at member)
    simpa using this
  · rintro ⟨B, ctx, related⟩
    have inContext := ctx.context related (C := {W})
      (by intro x member; simp at member; subst member; exact ⟨trivial, by simp [naming]⟩)
    obtain ⟨X', reduces, -⟩ := ctx.symm inContext |> fun h =>
      ctx.reduce h (M' := {done}) ⟨wildRead, rfl, ⟨by decide, by decide⟩, by decide⟩
    obtain ⟨ρ, rfl, ⟨-, avoids⟩, -⟩ := reduces
    have := avoids g (by decide)
    exact absurd this (by decide)

/-! ### Owned and forging rules, fresh bags -/

/-- **Owned, positive**: the scoped reader is owned by its label `S`: it uses only `S`, at name
`0`, and its absence region is empty. -/
theorem scopedRead_owned : OwnedBy naming scopedRead S := by
  refine ⟨by decide, fun x member => ?_, fun x closed => ?_⟩
  · simp [scopedRead, Rule.redex] at member
    subst member
    rfl
  · simp [scopedRead, messagesAtZero] at closed

/-- **Owned, negative**: the wildcard reader queries the region of the message `g` at name `1`,
which its label `W` does not carry. -/
theorem wildRead_not_owned : ¬ OwnedBy naming wildRead W := fun owned => by
  have := owned.closed g rfl
  simp [naming] at this

/-- **No forging, positive**: the scoped reader makes `done`, at name `0`, which `S` carries. -/
theorem scopedRead_noForge : NoForge naming scopedRead := by
  intro x member n mentions
  simp [scopedRead] at member
  subst member
  exact ⟨S, by decide, mentions⟩

/-- Make the message `g` (name `1`) from `S` (name `0`). -/
def forgeG : Rule NAtom := ⟨{S}, 0, {g}, messagesAtZero⟩

/-- **No forging, negative**: `forgeG` makes a message at name `1`, which nothing it uses carries. -/
theorem forgeG_forges : ¬ NoForge naming forgeG := by
  intro noForge
  obtain ⟨y, member, mentions⟩ := noForge g (by simp [forgeG]) 1 rfl
  simp [forgeG, Rule.redex] at member
  subst member
  simp [naming] at mentions

/-- **Fresh, positive**: `S` and `done` live at name `0`; neither mentions name `1`. -/
theorem fresh_for_one : FreshFor naming 1 ({S, done} : Multiset NAtom) := by
  intro x member
  simp at member
  rcases member with rfl | rfl <;> simp [naming]

/-- **Fresh, negative**: the message `g` mentions name `1`. -/
theorem not_fresh_for_one : ¬ FreshFor naming 1 ({g} : Multiset NAtom) :=
  fun fresh => fresh g (by simp) rfl

/-- **Mentions, positive and negative**: the message `g` mentions name `1` and not name `0`. -/
theorem message_mentions_one : naming.mentions g 1 ∧ ¬ naming.mentions g 0 := by
  simp [naming]

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Equivalence
